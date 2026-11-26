"""Build this internal revision twice from a deterministic archive."""
from hashlib import sha256
import os
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED

root = Path(__file__).resolve().parent
tex = ['main.tex','boundary.tex','eulerian-gaps.tex']
supplement = ['anc/ordinary-descent-certificate.zip','anc/boundary-certificate.zip']
supplement += ['anc/gaps/'+n for n in ('README.md','central-budgets.py','short_signed.py',
    'two_radii.py','certify.py','verify_brackets.py','nodes-127-compact.json')]
env = dict(os.environ, SOURCE_DATE_EPOCH='1795737600', FORCE_SOURCE_DATE='1', TZ='UTC')

def archive(name, members):
    with ZipFile(root/name,'w') as z:
        for member in sorted(members):
            meta = ZipInfo(member,(2026,11,27,0,0,0))
            meta.create_system = 3
            meta.external_attr = 0o100644 << 16
            z.writestr(meta,(root/member).read_bytes(),compress_type=ZIP_DEFLATED,compresslevel=9)

def compile_at(directory):
    for _ in range(2):
        subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                        '-halt-on-error','main.tex'],cwd=directory,env=env,
                       check=True,stdout=subprocess.DEVNULL)
    log = (directory/'main.log').read_text()
    bad = [line for line in log.splitlines() if any(word in line for word in
           ('Warning:', 'Overfull ', 'Missing character:'))]
    if bad:
        raise RuntimeError('\n'.join(bad))
    return (directory/'main.pdf').read_bytes()

archive('revision-tex.zip',tex)
archive('revision-with-certificates.zip',tex+supplement)
with TemporaryDirectory() as a, TemporaryDirectory() as b:
    first, second = Path(a),Path(b)
    with ZipFile(root/'revision-tex.zip') as z:
        z.extractall(first)
    with ZipFile(root/'revision-with-certificates.zip') as z:
        z.extractall(second)
    p,q = compile_at(first),compile_at(second)
    assert p == q
    (root/'main.pdf').write_bytes(p)
    print(next(line for line in (first/'main.log').read_text().splitlines()
               if line.startswith("Output written on")))
for name in ('main.pdf','revision-tex.zip','revision-with-certificates.zip'):
    print(sha256((root/name).read_bytes()).hexdigest(),name)
