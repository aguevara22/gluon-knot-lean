"""Check full-file technical-review bindings without granting source acceptance."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
ROOT = Path(__file__).resolve().parents[2]
C = ROOT / 'work/checks'
GROUPS = json.loads((C / 'soft-duplication-weighted-candidate-groups-20260912.json').read_text())
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def ishash(value): return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value)
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
        for pk, hk in [('receipt_path','receipt_sha256'), ('source_path','source_sha256'),
                       ('body_path','body_sha256'), ('base_review_path','base_review_sha256')]:
            if pk in obj and hk in obj: bind(obj[pk], obj[hk])
hashes, declarations = {}, []
for g in GROUPS:
    group = g['stem']; path = ROOT / 'work/reviews' / g['review']
    d = json.loads(path.read_text())
    rp = C / f'{group}-prototype-result.json'; r = json.loads(rp.read_text())
    assert d['scope']['group'] == group
    reviewed = d['scope']['declarations']
    assert reviewed == r['printed_declarations']
    assert d['stronger_model_statement_fidelity_approval'] is False
    assert d['source_claim_accepted'] is False and d['source_claim_acceptance_increment'] == 0
    assert d['canonical_integration_approved'] is False
    who = d['reviewer_identity']
    assert who['authored_reviewed_body'] is False and who['reviewer_is_ai'] is True
    assert who['agent'] != who['implementer']
    ev = d['evidence']
    assert ev['receipt_path'] == str(rp.relative_to(ROOT)) and ev['receipt_sha256'] == sha(rp)
    assert ev['declaration_axioms'] == r['declaration_axioms']
    assert ev['receipt_bound_files_sha256'] == r['files_sha256']
    start = len(bindings); walk(d)
    assert set(r['files_sha256'].items()) <= set(bindings[start:])
    hashes[str(path.relative_to(ROOT))] = sha(path)
    declarations += reviewed
assert len(GROUPS) == 10 and len(declarations) == len(set(declarations)) == 103
ledger = json.loads((ROOT / 'work/checkpoints/goal-turn-094-candidates.json').read_text())
assert declarations == [r['declaration'] for r in ledger]
result = {
    'utc':datetime.now(timezone.utc).isoformat(), 'verification':'passed',
    'sealed_review_records':len(GROUPS), 'candidate_groups_reviewed':len(GROUPS),
    'candidate_declarations_reviewed':len(declarations),
    'implementation_declarations_reviewed':103, 'prototype_consumers_reviewed':0,
    'quoted_file_bindings_verified':len(bindings), 'unique_bound_files':len(dict(bindings)),
    'review_files_sha256':hashes, 'stronger_statement_fidelity_approval':False,
    'source_claim_acceptance_increment':0,
    'binding_method':'Full frozen bodies including namespace/section binders and complete statements; every receipt-bound file and exact axiom trace is required. Header comparisons disclose repairs only.',
}
p = C / 'checkpoint-094-review-bindings.json'
if p.exists():
    old = json.loads(p.read_text())
    assert {k:v for k,v in old.items() if k!='utc'} == {k:v for k,v in result.items() if k!='utc'}
else: p.write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS:{len(GROUPS)} sealed technical reviews;{len(declarations)} declarations;{len(bindings)} file bindings.')
print('Stronger fidelity and source acceptance remain pending.')
