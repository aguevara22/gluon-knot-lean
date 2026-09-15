"""Check sealed review bindings, including the explicit header-metadata correction."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
REVIEWS = ROOT / 'work/reviews'
FILES = [
 'formal-near-far-recursion-technical-review-20260911.json',
 'canonical-tree-far-output-technical-review-20260911.json',
 'canonical-freezing-technical-review-20260911.json',
 'visible-generic-sign-persistence-technical-review-20260912.json',
 'canonical-silent-constancy-technical-review-20260911.json',
 'polynomial-continuation-technical-review-20260911.json',
 'formal-recursion-canonical-output-header-addendum-20260911.json']

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def ishash(value): return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value)

bindings, texts = [], []
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
             ('unchanged_sealed_review', 'unchanged_sealed_review_sha256'),
             ('review_path', 'sha256')]:
            if pathkey in obj and hashkey in obj: bind(obj[pathkey], obj[hashkey])
        for textkey, hashkey in [('source_header', 'sha256'), ('complete_header', 'sha256'),
             ('complete_source_header', 'exact_header_bytes_sha256')]:
            if textkey in obj and hashkey in obj:
                assert hashlib.sha256(obj[textkey].encode()).hexdigest() == obj[hashkey]
                texts.append(obj[hashkey])

hashes, groups = {}, []
for name in FILES:
    path = REVIEWS / name
    data = json.loads(path.read_text())
    assert data['stronger_model_statement_fidelity_approval'] is False
    assert data['source_claim_accepted'] is False and data['source_claim_acceptance_increment'] == 0
    if 'scope' in data: groups.append(data['scope']['group'])
    walk(data)
    hashes[str(path.relative_to(ROOT))] = sha(path)
assert set(groups) == {'FormalNearFarRecursion','CanonicalTreeFarOutput','CanonicalFreezing',
 'VisibleGenericSignPersistence','CanonicalSilentConstancy','PolynomialContinuation'}
addendum = json.loads((REVIEWS / FILES[-1]).read_text())
partial = []
for group in addendum['groups']:
    body = (ROOT / group['body_path']).read_text()
    assert body == group['complete_declarations_with_ambient_namespace_section_and_binders']
    for name, header in group['complete_headers'].items():
        assert header['complete_source_header'] in body
        if header['earlier_header_was_partial']: partial.append(name)
assert partial == ['eval_canonicalTreePolynomial_farOnly']
result = {'utc':datetime.now(timezone.utc).isoformat(), 'verification':'passed',
 'sealed_review_records':len(FILES), 'candidate_groups_reviewed':len(groups),
 'quoted_file_bindings_verified':len(bindings), 'unique_bound_files':len(dict(bindings)),
 'quoted_header_hashes_verified':len(texts), 'review_files_sha256':hashes,
 'partial_header_metadata_corrected_by_addendum':partial,
 'stronger_statement_fidelity_approval':False, 'source_claim_acceptance_increment':0}
path = ROOT / 'work/checks/checkpoint-087-review-bindings.json'
if path.exists():
    old = json.loads(path.read_text())
    assert {k:v for k,v in old.items() if k != 'utc'} == {k:v for k,v in result.items() if k != 'utc'}
else:
    path.write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS:{len(FILES)} sealed review records;{len(bindings)} file bindings;{len(texts)} header hashes.')
print('Six candidate groups reviewed; stronger fidelity and source acceptance remain pending.')
