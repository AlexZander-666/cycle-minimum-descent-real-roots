"""Strictly build and independently kernel-replay the representative Lean audit."""
import argparse
from hashlib import file_digest
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal"
IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import[ \t]+([^\n]+)", re.M)


def copy_closure(audit_dir):
    sources = set()

    def copy_imports(source, relative):
        if relative in sources:
            return
        sources.add(relative)
        destination = audit_dir / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        for line in IMPORT.findall(source.read_text()):
            for module in line.split("--", 1)[0].split():
                imported = Path(*module.split(".")).with_suffix(".lean")
                if (FORMAL / imported).is_file():
                    copy_imports(FORMAL / imported, imported)

    copy_imports(ROOT / "scripts/SmokeAudit.lean", Path("SmokeAudit.lean"))
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(FORMAL / name, audit_dir / name)
        sources.add(Path(name))
    with (audit_dir / "SHA256SUMS").open("w") as manifest:
        for path in sorted(sources):
            with (audit_dir / path).open("rb") as src:
                digest = file_digest(src, "sha256").hexdigest()
            manifest.write(f"{digest}  {path.as_posix()}\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages", type=Path, default=FORMAL / ".lake/packages")
    args = parser.parse_args()
    packages = args.packages.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix="descent-smoke-") as folder:
        work = Path(folder)
        source = work / "source"
        copy_closure(source)
        subprocess.run([sys.executable, "-Bu", FORMAL / "verify_bounded.py", source,
                        "SmokeAudit", work / "build", "--packages", packages, "--jobs", "1"],
                       check=True)


if __name__ == "__main__":
    main()
