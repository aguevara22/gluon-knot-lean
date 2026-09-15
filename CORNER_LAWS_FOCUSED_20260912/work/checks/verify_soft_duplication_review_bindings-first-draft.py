"""Verify full-file technical-review bindings; no stronger fidelity approval."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
REVIEWS = ROOT / 'work/reviews'
GROUPS = json.loads((ROOT / 'work/checks/soft-duplication-candidate-groups-20260912.json').read_text())
FILES = {g['stem']:g['review'] for g in GROUPS}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def ishash(value):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value)

bindings = []
def bind(path, digest):
    assert ishash(digest) and sha(ROOT / path) == digest, path
    bindings.append((path, digest))

def walk(obj):
    if isinstance(obj, list):
        for item in obj: walk(item)
    elif isinstance(obj, dict):
        for key, value in obj.items():
            if key.startswith(('work/', 'reference/')) and ishash(value): bind(key, value)
            walk(value)
        for pathkey, hashkey in [('receipt_path', 'receipt_sha256'),
            ('source_path', 'source_sha256'), ('body_path', 'body_sha256')]:
            if pathkey in obj and hashkey in obj: bind(obj[pathkey], obj[hashkey])

hashes, declarations = {}, []
for group, name in FILES.items():
    path = REVIEWS / name
    d = json.loads(path.read_text())
    assert d['scope']['group'] == group
    assert d['stronger_model_statement_fidelity_approval'] is False
    assert d['source_claim_accepted'] is False and d['source_claim_acceptance_increment'] == 0
    assert d['canonical_integration_approved'] is False
    assert d['reviewer_identity']['authored_reviewed_body'] is False
    assert d['reviewer_identity']['agent'] != d['reviewer_identity']['implementer']
    receipt = json.loads((ROOT / f'work/checks/{group}-prototype-result.json').read_text())
    assert d['scope']['declarations'] == receipt['printed_declarations']
    bodypath = f'work/checks/{group}.body.lean'
    start = len(bindings)
    walk(d)
    assert (bodypath, sha(ROOT / bodypath)) in bindings[start:]
    hashes[str(path.relative_to(ROOT))] = sha(path)
    declarations += d['scope']['declarations']
assert len(declarations) == len(set(declarations)) == 218
ledger = json.loads((ROOT / 'work/checkpoints/goal-turn-092-candidates.json').read_text())
assert declarations == [r['declaration'] for r in ledger]
result = {
    'utc': datetime.now(timezone.utc).isoformat(), 'verification': 'passed',
    'sealed_review_records': len(FILES), 'candidate_groups_reviewed': len(FILES),
    'candidate_declarations_reviewed': len(declarations),
    'implementation_declarations_reviewed': 218, 'prototype_consumers_reviewed': 0,
    'quoted_file_bindings_verified': len(bindings), 'unique_bound_files': len(dict(bindings)),
    'review_files_sha256': hashes, 'stronger_statement_fidelity_approval': False,
    'source_claim_acceptance_increment': 0,
    'binding_method': 'Full frozen bodies including namespace/section binders and complete statements; no parsed header-string hashes',
}
path = ROOT / 'work/checks/checkpoint-092-review-bindings.json'
if path.exists():
    old = json.loads(path.read_text())
    assert {k:v for k,v in old.items() if k != 'utc'} == {k:v for k,v in result.items() if k != 'utc'}
else:
    path.write_text(json.dumps(result, indent=2) + '\n')
print(f'PASS:{len(FILES)} sealed technical reviews;{len(declarations)} declarations;{len(bindings)} file bindings.')
print('Stronger fidelity and source acceptance remain pending.')
