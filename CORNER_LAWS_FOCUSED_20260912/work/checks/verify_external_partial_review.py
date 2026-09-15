"""Check file/type/trace bindings of an independently read partial review.

This does not replace the mathematical source review or accept a source claim.
Arguments: review path, expected implementation count, consumer count, session.
"""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
path = ROOT / sys.argv[1]
count, consumers, session = map(int, sys.argv[2:5])
report = json.loads(path.read_text())
checked = {}
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(name, expected):
    p = ROOT / name
    assert p.is_file() and sha(p) == expected, name
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
walk(report)
kernel = report.get('independent_kernel', report.get('evidence', {}))
assert kernel.get('session', kernel.get('passed_session', kernel.get('independent_kernel_session'))) == session
assert kernel.get('exit_code', kernel.get('independent_kernel_exit_code')) == 0
assert kernel.get('implementation_type_count', kernel.get('declaration_count')) == count
assert kernel.get('substantive_consumer_count', kernel.get('additional_example_count')) == consumers
log_path = kernel.get('trace_log', kernel.get('independent_trace_log'))
source_path = kernel.get('trace_source', kernel.get('independent_trace_source'))
log = (ROOT / log_path).read_text()
assert 'error:' not in log
traces = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
assert len(traces) == len({name for name, _ in traces}) == count + consumers
assert all(set(x.strip() for x in aa.split(',') if x.strip()) <=
           {'propext', 'Classical.choice', 'Quot.sound'} for _, aa in traces)
source = (ROOT / source_path).read_text()
for row in report.get('reviewed_declarations', []):
    sig = row['source_signature_text']
    assert sig in source
    assert hashlib.sha256(sig.encode()).hexdigest() == row['source_signature_sha256']
    ty = row['reviewed_elaborated_type']
    assert hashlib.sha256(ty.encode()).hexdigest() == row.get('reviewed_type_sha256', row.get('reviewed_elaborated_type_sha256'))
if 'independent_closure_evidence' in kernel:
    closure = json.loads((ROOT / kernel['independent_closure_evidence']).read_text())
    walk(closure)
if 'reviewed_types' in kernel:
    types = json.loads((ROOT / kernel['reviewed_types']).read_text())
    assert len(types['types']) == count
    for name, ty in types['types'].items():
        assert hashlib.sha256(ty.encode()).hexdigest() == types['type_sha256'][name]
assert len([p for p in checked if p.startswith('work/lean/SM/')]) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327
assert any(report.get(k) for k in ['reviewer', 'independence'])
print(json.dumps({'passed': True, 'review': str(path.relative_to(ROOT)),
    'review_sha256': sha(path), 'verified_unique_file_bindings': len(checked),
    'canonical_SM_modules_unchanged': 327, 'independent_session': session,
    'types': count, 'consumers': consumers, 'standard_or_empty_traces': len(traces),
    'source_claim_acceptance_increment': 0, 'stage_complete': False}, indent=2))
