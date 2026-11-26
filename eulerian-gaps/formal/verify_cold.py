"""Rebuild and independently replay the exact local Lean source closure."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import fcntl
from hashlib import sha256
import heapq
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import resource
import shutil
import subprocess
from time import monotonic


AUDIT = "EulerianBracketingAudit"
MODULE = r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def verify_manifest(root):
    manifest = root / "SHA256SUMS"
    paths = {}
    for entry in manifest.read_text().splitlines():
        check, name = entry.split("  ", 1)
        path = PurePosixPath(name)
        if (path.is_absolute() or ".." in path.parts or str(path) != name or name in paths
                or not re.fullmatch(r"[a-f0-9]{64}", check)):
            raise ValueError(f"Invalid manifest entry {entry!r}")
        target = root / name
        if target.is_symlink() or digest(target) != check:
            raise ValueError(f"Source hash mismatch: {name}")
        paths[name] = check
    return paths


def lean_sources(root, hashes):
    sources = {name.removesuffix(".lean").replace("/", "."): name
               for name in hashes if name.endswith(".lean")}
    if AUDIT not in sources:
        raise ValueError("Missing audit")
    graph = {}
    for module, name in sources.items():
        if not re.fullmatch(MODULE, module):
            raise ValueError(f"Invalid local module {module}")
        imports = set()
        for group in re.findall(r"^(?:(?:public|private|meta)\s+)*import[ \t]+([^\n]+)",
                                (root / name).read_text(), re.M):
            imports.update(group.split("--", 1)[0].split())
        graph[module] = imports & sources.keys()
    reached = set()
    pending = [AUDIT]
    while pending:
        module = pending.pop()
        if module not in reached:
            reached.add(module)
            pending.extend(graph[module])
    if reached != sources.keys() or len(sources) != 576:
        raise ValueError(f"Expected exactly the 576 reachable source files, found {len(reached)}")
    return sources, graph


def save_json(path, data):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def schedule(tasks, actions, completed, limit, priorities):
    """Run a bounded number of jobs whose prerequisite jobs have finished."""
    pending = {module: deps - completed for module, deps in tasks.items() if module not in completed}
    successors = {module: [] for module in pending}
    ready = []
    for module, deps in pending.items():
        if not deps:
            heapq.heappush(ready, (priorities.get(module, 0), module))
        for dep in deps:
            successors[dep].append(module)
    futures = {}
    with ThreadPoolExecutor(max_workers=limit) as workers:
        while ready or futures:
            while ready and len(futures) < limit:
                _, module = heapq.heappop(ready)
                futures[workers.submit(actions, module)] = module
            finished, _ = wait(futures, return_when=FIRST_COMPLETED)
            for task in finished:
                module = futures.pop(task)
                task.result()
                completed.add(module)
                for following in successors[module]:
                    pending[following].remove(module)
                    if not pending[following]:
                        heapq.heappush(ready, (priorities.get(following, 0), following))
    if completed != tasks.keys():
        raise ValueError("Incomplete build graph")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True, help="Empty or resumable work directory on local storage.")
    parser.add_argument("--packages", type=Path, help="Directory with the nine pinned third-party packages and their build cache.")
    parser.add_argument("--jobs", type=int, default=1, help="Maximum simultaneous Lean processes.")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    root = Path(__file__).resolve().parent
    work = args.work.resolve()
    if work == root or work.is_relative_to(root):
        parser.error("Work directory must be outside the extracted source")
    work.mkdir(exist_ok=True)
    lock = (work / "work.lock").open("w")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    hashes = verify_manifest(root)
    source_set = digest(root / "SHA256SUMS")
    sources, graph = lean_sources(root, hashes)
    project = work / "project"
    checkpoint = work / "checkpoints"
    logs = work / "logs"
    stage_info = work / "source-set"
    if not stage_info.exists():
        if set(work.iterdir()) != {work / "work.lock"}:
            raise ValueError("New verification needs an empty work directory")
        project.mkdir()
        checkpoint.mkdir()
        logs.mkdir()
        for name in sorted(hashes):
            destination = project / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / name, destination)
        shutil.copyfile(root / "SHA256SUMS", project / "SHA256SUMS")
        stage_info.write_text(source_set + "\n")
    if stage_info.read_text().strip() != source_set or verify_manifest(project) != hashes:
        raise ValueError("Staged source set differs from the frozen source set")
    if {p.relative_to(project).as_posix() for p in project.rglob("*.lean")
        if ".lake" not in p.relative_to(project).parts} != set(sources.values()):
        raise ValueError("Untracked local Lean sources in the standalone work directory")
    fd_soft, fd_hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    if fd_soft < 65_536:
        resource.setrlimit(resource.RLIMIT_NOFILE, (min(65_536, fd_hard) if fd_hard >= 0 else 65_536, fd_hard))
    env = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"}}
    env["LEAN_NUM_THREADS"] = "1"

    def run(*argv):
        return subprocess.check_output(argv, cwd=project, env=env, text=True).strip()

    version = run("lean", "--version")
    if LEAN_COMMIT not in version or "version 4.33.1" not in version:
        raise ValueError(f"Unexpected Lean toolchain: {version}")
    compiler = Path(run("lean", "--print-prefix")) / "bin"
    dep_root = project / ".lake/packages"
    if args.packages:
        expected = args.packages.resolve(strict=True)
        if not dep_root.exists():
            dep_root.parent.mkdir(exist_ok=True)
            dep_root.symlink_to(expected, target_is_directory=True)
        if dep_root.resolve() != expected:
            raise ValueError("Package location differs from previous run")
    elif not dep_root.exists():
        subprocess.run(["lake", "exe", "cache", "get"], cwd=project, env=env, check=True)
    manifest = json.loads((project / "lake-manifest.json").read_text())
    versions = {}
    for package in manifest["packages"]:
        checkout = dep_root / package["name"]
        rev = run("git", "-C", checkout, "rev-parse", "HEAD")
        if rev != package["rev"] or run("git", "-C", checkout, "status", "--porcelain", "--untracked-files=no"):
            raise ValueError(f"Locked dependency differs: {package['name']}")
        versions[package["name"]] = rev
    library = project / ".lake/build/lib/lean"
    library.mkdir(parents=True, exist_ok=True)
    inherited = run("lake", "env", "printenv", "LEAN_PATH").split(os.pathsep)
    cache = dep_root.resolve()
    system_library = (compiler.parent / "lib/lean").resolve()
    for path in inherited:
        resolved = Path(path).resolve()
        if resolved not in {library, system_library} and not resolved.is_relative_to(cache):
            raise ValueError(f"Unexpected imported object directory {path}")
    env["LEAN_PATH"] = os.pathsep.join([str(library)] + [
        str(Path(path).resolve()) for path in inherited if Path(path).resolve() != library
    ])
    print(f"START source_set={source_set} project_modules={len(sources)-1} jobs={args.jobs}", flush=True)
    print(platform.machine(), version, flush=True)
    for name, revision in sorted(versions.items()):
        print(f"dependency {name} {revision}", flush=True)

    def object_file(module):
        return library / (sources[module].removesuffix(".lean") + ".olean")

    def checkpoint_file(module, phase):
        return checkpoint / f"{module}.{phase}.json"

    def verify_checkpoint(module, phase):
        entry = checkpoint_file(module, phase)
        if not entry.exists():
            return False
        data = json.loads(entry.read_text())
        if (data["source_sha256"] != hashes[sources[module]]
                or any(digest(library / name) != value for name, value in data["objects"].items())
                or digest(logs / f"{module}.{phase}.log") != data["log_sha256"]):
            raise ValueError(f"Cannot trust resumed result for {phase} {module}")
        return True

    lean = compiler / "lean"
    checker = compiler / "leanchecker"

    def execute(module, phase, arguments):
        transcript = logs / f"{module}.{phase}.log"
        started = monotonic()
        with transcript.open("wb") as output:
            status = subprocess.run(arguments, cwd=project, env=env,
                                    stdout=output, stderr=subprocess.STDOUT).returncode
        elapsed = round(monotonic() - started, 3)
        if status:
            print(transcript.read_text(errors="replace"), flush=True)
            raise RuntimeError(f"{phase} exit={status} {module} seconds={elapsed}")
        out = object_file(module)
        family = {p.relative_to(library).as_posix(): digest(p)
                  for p in sorted(out.parent.glob(out.name + "*")) if p.is_file()}
        if out.relative_to(library).as_posix() not in family:
            raise ValueError(f"Missing main object {module}")
        report = {"exit": status, "elapsed_seconds": elapsed, "source_sha256": hashes[sources[module]],
                  "objects": family, "log_sha256": digest(transcript)}
        save_json(checkpoint_file(module, phase), report)
        print(f"PASS {phase} {module} seconds={elapsed} source={report['source_sha256']} object={digest(out)}",
              flush=True)

    def build(module):
        out = object_file(module)
        out.parent.mkdir(parents=True, exist_ok=True)
        for old in out.parent.glob(out.name + "*"):
            old.unlink()
        execute(module, "strict", [lean, "-j", "1", "-DwarningAsError=true",
                                   "-o", out, sources[module]])

    def replay(module):
        if any(other.startswith(module + ".") for other in sources):
            helper = work / f"ReplayOne_{module.replace('.', '_')}.lean"
            helper.write_text("import LeanChecker\n"
                              "#eval do\n"
                              "  Lean.initSearchPath (← Lean.findSysroot)\n"
                              f"  replayFromImports `{module}\n")
            command = [lean, "-j", "1", "-DwarningAsError=true", str(helper)]
        else:
            command = [checker, "--verbose", module]
        execute(module, "kernel", command)

    completed = {module for module in graph if verify_checkpoint(module, "strict")}
    if any(graph[module] - completed for module in completed):
        raise ValueError("Built checkpoint with missing dependency checkpoint")
    priority = {module: -len(deps) for module, deps in graph.items()}
    print(f"strict_checkpoint_count={len(completed)}", flush=True)
    schedule(graph, build, completed, args.jobs, priority)
    audit_source = (project / sources[AUDIT]).read_text()
    expected = re.findall(r"^#print axioms (\S+)\s*$", audit_source, re.M)
    raw_audit = (logs / f"{AUDIT}.strict.log").read_text()
    print(raw_audit, end="", flush=True)
    entries = re.findall(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$",
                         raw_audit, re.M)
    if len(entries) != len(expected) or sorted(name for name, _ in entries) != sorted(expected):
        raise ValueError("Audit transcript does not match declared results")
    axioms = {name: sorted(axiom.strip() for axiom in report.split(",") if axiom.strip())
              for name, report in entries}
    if any(set(report) - ALLOWED for report in axioms.values()):
        raise ValueError("A declaration uses unapproved transitive axioms")
    local = {module: set() for module in graph if module != AUDIT}
    replayed = {module for module in local if verify_checkpoint(module, "kernel")}
    replay_priority = {module: -(object_file(module).stat().st_size) for module in local}
    print(f"kernel_checkpoint_count={len(replayed)}", flush=True)
    schedule(local, replay, replayed, args.jobs, replay_priority)
    if verify_manifest(project) != hashes or verify_manifest(root) != hashes:
        raise ValueError("Inputs changed during verification")
    report = {"source_set_sha256": source_set, "architecture": platform.machine(), "lean": version,
              "locked_third_party": versions, "audit": axioms, "project_modules": {}}
    for module in sorted(local):
        report["project_modules"][module] = {
            phase: json.loads(checkpoint_file(module, phase).read_text()) for phase in ("strict", "kernel")
        }
    save_json(work / "receipt.json", report)
    print(f"PASS: {len(local)} project modules rebuilt and replayed; {len(axioms)} declarations audited.", flush=True)


if __name__ == "__main__":
    main()
