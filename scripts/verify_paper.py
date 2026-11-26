"""Build the paper from the checked-out source and the frozen arXiv files."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


root = Path(__file__).resolve().parents[1] / "paper"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--frozen", action="store_true", help="Compare the output with TeX Live 2026 release bytes.")
args = parser.parse_args()
with tempfile.TemporaryDirectory(prefix="descent-paper-") as folder:
    copy = Path(folder) / "paper"
    shutil.copytree(root, copy)
    subprocess.run([sys.executable, "-Bu", "reproduce.py", "build"], cwd=copy, check=True)
    if args.frozen:
        for name in ("main.pdf", "arxiv-source.zip"):
            if (copy / name).read_bytes() != (root / name).read_bytes():
                raise ValueError(f"Release bytes differ for {name}")
        print("PASS pinned TeX build reproduces the archived PDF and arXiv ZIP.")
