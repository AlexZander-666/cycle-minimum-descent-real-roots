"""Verify release checksums, Lean source-level inputs, and the finite certificates."""
from pathlib import Path
from hashlib import file_digest, sha256
from zipfile import ZipFile
import csv
import re

root = Path(__file__).resolve().parents[1]


def digest(file):
    with file.open('rb') as data:
        return file_digest(data, 'sha256').hexdigest()


def check_manifest(directory):
    checked = set()
    for line in (directory / 'SHA256SUMS').read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = directory / name
        if (name in checked or Path(name).is_absolute() or '..' in Path(name).parts
                or path.is_symlink() or not re.fullmatch('[0-9a-f]{64}', expected)):
            raise ValueError(f'Invalid checksum entry {name}')
        if digest(path) != expected:
            raise ValueError(f'Content mismatch: {name}')
        checked.add(name)
    return checked


def main():
    inventory = check_manifest(root)
    modules = check_manifest(root / 'formal')
    with (root / 'verification/verified-modules.tsv').open() as stream:
        rows = list(csv.DictReader(stream, delimiter='\t'))
    names = set()
    for row in rows:
        name = row['module'].replace('.', '/') + '.lean'
        if name in names or digest(root / 'formal' / name) != row['source_sha256']:
            raise ValueError(f'Cold-replay evidence mismatch: {name}')
        names.add(name)
    if len(names) != 499 or names != {p for p in modules if p.endswith('.lean')}:
        raise ValueError('Expected the entire checked 499-module closure')
    papers = {'main.tex', 'boundary.tex', 'anc/ordinary-descent-certificate.zip',
              'anc/boundary-certificate.zip'}
    with ZipFile(root / 'paper/arxiv-source.zip') as archive:
        if sorted(papers) != sorted(archive.namelist()):
            raise ValueError('Unexpected arXiv source members')
        for p in papers:
            if sha256(archive.read(p)).hexdigest() != digest(root / 'paper' / p):
                raise ValueError(f'archived paper source differs: {p}')
    print(f'PASS {len(inventory)} artifact hashes, 499 proof-source receipts and four arXiv members.')


if __name__ == '__main__':
    main()
