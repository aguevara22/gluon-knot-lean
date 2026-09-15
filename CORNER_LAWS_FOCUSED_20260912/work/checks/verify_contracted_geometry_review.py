"""Bind the independent contracted-word review to its actual frozen evidence."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
checked = {}
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def bind(name, expected):
    path = ROOT / name
    assert path.is_file() and sha(path) == expected, name
    checked[name] = expected
def walk(obj):
    if isinstance(obj, dict):
        for key, value in obj.items():
            if isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value):
                if key.startswith(('work/', 'reference/', 'provenance/', 'lean/')) or key == 'FINAL_REVIEW.md':
                    bind(key, value)
                elif key.endswith('_sha256'):
                    name = obj.get(key[:-7])
                    if isinstance(name, str) and name.startswith(('work/', 'reference/', 'provenance/', 'lean/')):
                        bind(name, value)
            walk(value)
    elif isinstance(obj, list):
        for value in obj:
            walk(value)

path = ROOT / 'work/reviews/contracted-geometric-word-independent.json'
report = json.loads(path.read_text())
assert report['state'].startswith('PASS:')
assert len(report['declarations']) == len(report['reviewed_declarations']) == 10
assert report['acceptance']['source_claim_increment'] == 0
assert not report['acceptance']['full_thm_single_triple_accepted']
assert not report['acceptance']['canonical_port_accepted']
walk(report)
assert len([p for p in checked if p.startswith('work/lean/SM/')]) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327
kernel = report['independent_kernel']
assert kernel['session'] == 65020 and kernel['exit_code'] == 0 and kernel['first_run_passed']
assert kernel['implementation_type_count'] == 10 and kernel['substantive_consumer_count'] == 9
assert not kernel['unexpected_axioms']
log = (ROOT / kernel['trace_log']).read_text()
assert 'error:' not in log
ts = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
assert len(ts) == len({n for n, _ in ts}) == 19
assert all(set(x.strip() for x in a.split(',') if x.strip()) <=
           {'propext', 'Classical.choice', 'Quot.sound'} for _, a in ts)
assert set(n for n, _ in ts) == set(report['axiom_traces'])
body = (ROOT / 'work/checks/ContractedGeometricWord.body.lean').read_text()
for row in report['reviewed_declarations']:
    sig = row['source_signature_text']
    assert sig in body
    assert hashlib.sha256(sig.encode()).hexdigest() == row['source_signature_sha256']
    assert hashlib.sha256(row['reviewed_elaborated_type'].encode()).hexdigest() == row['reviewed_type_sha256']
source = (ROOT / kernel['trace_source']).read_text()
assert source.count(body) == 1
for name in ['BoundaryTripleSupports', 'CriticalContractionPositions', 'CriticalContractionBounds']:
    assert source.count((ROOT / ('work/checks/' + name + '.body.lean')).read_text()) == 1
root_receipt = json.loads((ROOT / 'work/checks/ContractedGeometricWord-prototype-result.json').read_text())
assert root_receipt['kernel_session'] == 99727 and root_receipt['exit_code'] == 0
walk(root_receipt)
print(json.dumps({'passed': True, 'review': str(path.relative_to(ROOT)),
    'review_sha256': sha(path), 'verified_unique_file_bindings': len(checked),
    'canonical_SM_modules_unchanged': 327, 'reviewed_types': 10,
    'consumer_checks': 9, 'standard_or_empty_traces': 19,
    'source_claim_acceptance_increment': 0, 'stage_complete': False}, indent=2))
