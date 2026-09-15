"""Shared, read-only manifest validation for the handoff (standard library)."""
from hashlib import sha256
from pathlib import Path, PurePosixPath
import re

ROOT = Path(__file__).resolve().parents[1]
FRAMES = {
    'SM15': ('SM', 'FRAMED_MANIFEST_SM15.sha256',
             '8659ffeb9bedcbfa8a9e197b648ef6d09cd27afb3e83e6986a9cb2bf5f02932a', 20),
    'CV': ('R/CV', 'FRAMED_MANIFEST_CV.sha256',
           '8c02692c9a52ffe5a7c549715e00bfbc29f997af62a074b36af1c2f4a4cf3706', 13),
    'RA': ('R/RA', 'FRAMED_MANIFEST_RA.sha256',
           '0ba16c58ea07fdde5b3083b89a59cbd23f2152f6821b9f902100fb2817f678fa', 20),
    'BRIDGE': ('BRIDGE', 'SHA256SUMS',
               'bb49333cef7360c7885dec52cd5ad2f5d63cd9e5c22dd706776e6832b7af9017', 13),
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def safe_file(base, name):
    p = PurePosixPath(name)
    require(name and not p.is_absolute() and str(p) == name
            and '..' not in p.parts and '\\' not in name, 'unsafe path: ' + name)
    current = base
    for part in p.parts:
        current = current / part
        require(not current.is_symlink(), 'symlink: ' + name)
    require(current.is_file(), 'missing file: ' + name)
    return current


def manifest_rows(raw):
    rows = {}
    for line in raw.decode('utf-8').splitlines():
        if not line or line.startswith('#'):
            continue
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match is not None, 'malformed manifest row')
        value, name = match.groups()
        require(name not in rows, 'duplicate manifest member: ' + name)
        rows[name] = value
    require(rows, 'empty manifest')
    return rows


def verify_manifest(base, name, pin=None, count=None, exact=False):
    raw = safe_file(base, name).read_bytes()
    if pin is not None:
        require(digest(raw) == pin, 'manifest pin mismatch: ' + str(base / name))
    rows = manifest_rows(raw)
    require(name not in rows, 'manifest cannot hash itself')
    if count is not None:
        require(len(rows) == count, 'manifest row count: ' + str(base))
    payloads = {}
    for filename, wanted in rows.items():
        data = safe_file(base, filename).read_bytes()
        require(digest(data) == wanted, 'payload hash mismatch: ' + str(base / filename))
        payloads[filename] = data
    if exact:
        actual = set()
        for p in base.rglob('*'):
            require(not p.is_symlink(), 'symlink in frame: ' + str(p))
            if p.is_file() and p.name != '.DS_Store':
                actual.add(p.relative_to(base).as_posix())
        require(actual == set(rows) | {name}, 'frame file inventory mismatch: ' + str(base))
    return payloads


def verify_frames(root=ROOT):
    return {frame: verify_manifest(root / directory, name, pin, count, exact=True)
            for frame, (directory, name, pin, count) in FRAMES.items()}
