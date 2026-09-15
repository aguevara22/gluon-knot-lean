"""Receipt bindings shared by acceptance checks and progress reporting."""
from hashlib import sha256
from pathlib import Path


def project_files(project):
    return sorted(p for p in project.rglob('*') if p.is_file()
                  and not any(part.startswith('.') for part in p.relative_to(project).parts)
                  and (p.suffix == '.lean' or p.name in {'lean-toolchain', 'lakefile.toml',
                       'lakefile.lean', 'lake-manifest.json', 'lean-declarations.json'}))


def hashes(base, paths):
    return {p.relative_to(base).as_posix(): sha256(p.read_bytes()).hexdigest() for p in paths}


def matches(base, expected):
    if not isinstance(expected, dict):
        return False
    for name, wanted in expected.items():
        path = base / name
        if not path.resolve().is_relative_to(base.resolve()) or not path.is_file():
            return False
        if sha256(path.read_bytes()).hexdigest() != wanted:
            return False
    return True


def current(receipt, work, root):
    if not (receipt.get('receipt_schema') == 2 and receipt.get('passed') is True
            and receipt.get('stage_accepted') is True and receipt.get('project_sha256')
            and receipt.get('evidence_sha256') and receipt.get('bundle_sha256')):
        return False
    if set(receipt['project_sha256']) != {p.relative_to(work / 'lean').as_posix()
                                        for p in project_files(work / 'lean')}:
        return False
    return (matches(work / 'lean', receipt['project_sha256'])
            and matches(work, receipt['evidence_sha256'])
            and matches(root, receipt['bundle_sha256']))
