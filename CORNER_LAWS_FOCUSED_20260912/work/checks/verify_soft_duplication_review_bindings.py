"""Verify full-file technical-review bindings; no stronger fidelity approval."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
REVIEWS = ROOT / 'work/reviews'
GROUPS = json.loads((ROOT / 'work/checks/soft-duplication-candidate-groups-20260912.json').read_text())
FILES = {g['stem']:g['review'] for g in GROUPS}
META_PATH = REVIEWS / 'soft-duplication-legacy-review-metadata-20260912.json'
META = json.loads(META_PATH.read_text())
META_RECORDS = {r['group']:r for r in META['records']}
assert set(META_RECORDS) == {'CutSetNearFar', 'CutSetNearFarNeighbors', 'SoftDuplicationAvoiding'}

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
            ('source_path', 'source_sha256'), ('body_path', 'body_sha256'),
            ('base_review_path', 'base_review_sha256')]:
            if pathkey in obj and hashkey in obj: bind(obj[pathkey], obj[hashkey])

hashes, declarations = {}, []
for group, name in FILES.items():
    path = REVIEWS / name
    d = json.loads(path.read_text())
    receipt = json.loads((ROOT / f'work/checks/{group}-prototype-result.json').read_text())
    if group in META_RECORDS:
        # Preserve the legacy substantive record; reviewer attests only its metadata.
        assert d['review_schema'] == 'independent-read-only-helper-technical-review-v1'
        a = META_RECORDS[group]
        assert a['base_review_path'] == str(path.relative_to(ROOT))
        assert a['base_review_sha256'] == sha(path)
        assert a['declarations'] == d['scope']['reviewed_declarations'] == receipt['printed_declarations']
        assert d['scope']['source_acceptance_increment'] == 0
        assert d['scope']['full_A_soft_accepted'] is False
        assert d['scope']['stronger_claims_accepted'] is False
        assert d['read_only'] is True and d['reviewer'] != d['implementer']
        assert d['existing_kernel_evidence']['recorded_kernel_session'] == receipt['kernel_session']
        assert d['existing_kernel_evidence']['recorded_exit_code'] == 0
        assert d['existing_kernel_evidence']['actual_axiom_traces'] == receipt['declaration_axioms']
        walk(a)
        reviewed = a['declarations']
    else:
        a = d
        assert d['scope']['group'] == group
        reviewed = d['scope']['declarations']
    assert a['stronger_model_statement_fidelity_approval'] is False
    assert a['source_claim_accepted'] is False and a['source_claim_acceptance_increment'] == 0
    assert a['canonical_integration_approved'] is False
    if 'reviewer_identity' in a:
        assert a['reviewer_identity']['authored_reviewed_body'] is False
        assert a['reviewer_identity']['agent'] != a['reviewer_identity']['implementer']
    else:
        assert group == 'SoftGeometricDuplication'
        assert a['independence']['authored_reviewed_body'] is False
        assert a['independence']['reviewer_is_ai'] is True
        assert a['independence']['same_model_technical_review_only'] is True
        assert a['read_only'] is True
        assert a['reviewer'] != a['implementer']
    assert reviewed == receipt['printed_declarations']
    bodypath = f'work/checks/{group}.body.lean'
    start = len(bindings)
    walk(d)
    assert (bodypath, sha(ROOT / bodypath)) in bindings[start:]
    hashes[str(path.relative_to(ROOT))] = sha(path)
    declarations += reviewed
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
    'legacy_metadata_addendum_path':str(META_PATH.relative_to(ROOT)),
    'legacy_metadata_addendum_sha256':sha(META_PATH),
    'legacy_metadata_groups':list(META_RECORDS),
    'alternate_explicit_identity_layout':['SoftGeometricDuplication'],
    'metadata_schema_normalization':'Three original substantive reviews retained unchanged; explicit reviewer-authored, hash-bound metadata addendum supplies the common no-approval/identity fields.',
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
