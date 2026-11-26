"""Build and replay this edition. Python 3.12 standard library; pdfLaTeX TeX Live 2026."""
import argparse
from hashlib import sha256
import os
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED, ZIP_STORED

ROOT=Path(__file__).resolve().parent
SOURCES=("main.tex","boundary.tex","anc/ordinary-descent-certificate.zip","anc/boundary-certificate.zip")
FIXED_ENV=dict(os.environ,SOURCE_DATE_EPOCH="1795651200",FORCE_SOURCE_DATE="1",TZ="UTC")
def digest(path):
    return sha256(path.read_bytes()).hexdigest()
def archive(path, names):
    with ZipFile(path,"w") as bundle:
        for name in sorted(names):
            info=ZipInfo(name,(2026,11,26,0,0,0))
            info.create_system=3
            info.external_attr=0o100644<<16
            method=ZIP_STORED if name=="ordinary-descents-all-cutoffs-lean.zip" else ZIP_DEFLATED
            bundle.writestr(info,(ROOT/name).read_bytes(),method,compresslevel=9)
def pdf(directory):
    executable=shutil.which("pdflatex")
    if executable is None:
        raise RuntimeError("Add the pinned TeX Live 2026 bin directory to PATH")
    for _ in range(2):
        subprocess.run([executable,"-interaction=nonstopmode","-halt-on-error","-no-shell-escape","main.tex"],
                       cwd=directory,env=FIXED_ENV,check=True,stdout=subprocess.DEVNULL)
    log=(directory/"main.log").read_text()
    problems=[line for line in log.splitlines() if "Warning:" in line or "Overfull " in line or "Missing character:" in line]
    if problems:
        raise RuntimeError("\n".join(problems))
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("action",choices=["build","finite"])
    args=parser.parse_args()
    with TemporaryDirectory() as tmp:
        work=Path(tmp)
        if args.action=="build":
            archive(ROOT/"arxiv-source.zip",SOURCES)
            first=work/"first"
            first.mkdir()
            for name in SOURCES[:2]:
                shutil.copyfile(ROOT/name,first/name)
            pdf(first)
            second=work/"from-zip"
            with ZipFile(ROOT/"arxiv-source.zip") as bundle:bundle.extractall(second)
            pdf(second)
            assert (first/"main.pdf").read_bytes()==(second/"main.pdf").read_bytes()
            shutil.copyfile(first/"main.pdf",ROOT/"main.pdf")
            print("Matching local and clean-source PDF",digest(ROOT/"main.pdf"),flush=True)
            print("arXiv ZIP",digest(ROOT/"arxiv-source.zip"),flush=True)
            return
        for name,commands in [
            (SOURCES[2],[["finite-127/certify.py","--last","127","--direct","9","--verify","finite-127/certificate.json"],
                         ["shared-angle-mesh/verify.py","finite-127"],["check_margins.py"]]),
            (SOURCES[3],[["boundary-mixtures/astra_check.py"],["boundary-mixtures/certificate.py"],["review_margins.py"]])]:
            extracted=work/Path(name).stem
            with ZipFile(ROOT/name) as bundle:bundle.extractall(extracted)
            print("Extracted",name,digest(ROOT/name),flush=True)
            if (extracted/"SHA256SUMS").exists():
                for line in (extracted/"SHA256SUMS").read_text().splitlines():
                    expected,filename=line.split(maxsplit=1)
                    assert digest(extracted/filename)==expected
            for cmd in commands:
                subprocess.run([sys.executable,"-BIu",*cmd],cwd=extracted,check=True)
if __name__=="__main__":
    main()
