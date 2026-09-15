"""Verify the two external partial reviews without running another Lean kernel."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
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
def traces(path, count):
    log = (ROOT / path).read_text()
    assert 'error:' not in log
    ts = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    assert len(ts) == len({n for n, _ in ts}) == count
    assert all(set(a.strip() for a in aa.split(',') if a.strip()) <=
               {'propext', 'Classical.choice', 'Quot.sound'} for _, aa in ts)
    return dict(ts)

geo_path = ROOT / 'work/reviews/geometric-gap-response-prototype.json'
geo = json.loads(geo_path.read_text())
assert geo['verdict'] == geo['implemented_scope_verdict'] == 'faithful'
assert geo['reviewer'] != geo['implementer']
assert geo['parameters_reviewed'] and geo['definition_equivalence_reviewed']
assert not geo['source_claim_accepted'] and not geo['in_theorem_library']
assert len(geo['main_declarations']) == 15
assert geo['embedded_body_count'] == 11 and geo['import_closure_file_count'] == 62
ev = geo['evidence']
assert ev['independent_kernel_session'] == 76983 and ev['independent_kernel_exit_code'] == 0
assert ev['declaration_count'] == 42 and ev['additional_example_count'] == 31
assert ev['additional_examples_passed'] and ev['all_27_predecessor_types_unchanged']
walk(geo)
for name, expected in geo['prototype_files_sha256'].items():
    bind('work/checks/' + name + '.prototype.lean', expected)
closure = json.loads((ROOT / ev['independent_closure_evidence']).read_text())
assert closure['SM_closure_count'] == 62
assert len(closure['all_327_canonical_SM_files_sha256']) == 327
walk(closure)
for name in closure['root_receipts_sha256']:
    receipt = json.loads((ROOT / name).read_text())
    assert receipt['exit_code'] == 0
    walk(receipt)
types = json.loads((ROOT / ev['reviewed_types']).read_text())
assert len(types['types']) == len(types['type_sha256']) == 42
assert set(types['types']) == set(ev['checked_declarations'])
for name, ty in types['types'].items():
    assert hashlib.sha256(ty.encode()).hexdigest() == types['type_sha256'][name], name
assert set(geo['main_declarations']) <= traces(ev['independent_trace_log'], 73).keys()
geo_count = len(checked)

child_path = ROOT / 'work/reviews/critical-contraction-child-independent.json'
child = json.loads(child_path.read_text())
assert child['state'].startswith('PASS:')
assert len(child['declarations']) == len(child['reviewed_declarations']) == 22
assert child['acceptance']['source_acceptance_increment'] == 0
assert not child['acceptance']['thm_single_triple_accepted']
assert not child['acceptance']['canonical_port_accepted']
walk(child)
assert child['canonical_frozen_snapshot']['SM_module_count'] == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327
k = child['independent_kernel']
assert k['session'] == 45295 and k['exit_code'] == 0 and k['first_run_passed']
assert k['implementation_type_count'] == 22 and k['substantive_consumer_count'] == 15
assert not k['unexpected_axioms']
ts = traces(k['trace_log'], 37)
assert sum(not a for a in ts.values()) == 2
assert set(ts) == set(child['axiom_traces'])
for row in child['reviewed_declarations']:
    lines = (ROOT / row['path']).read_text().splitlines(keepends=True)
    assert ''.join(lines[row['first_line'] - 1:row['last_line']]) == row['source_declaration_text']
    for field in ['source_declaration', 'source_signature']:
        assert hashlib.sha256(row[field + '_text'].encode()).hexdigest() == row[field + '_sha256']
    assert hashlib.sha256(row['reviewed_elaborated_type'].encode()).hexdigest() == row['reviewed_elaborated_type_sha256']
    assert row['declaration'] in ts
cs = child['independent_consumers']
assert cs['all_passed_first_run'] and len(cs['reviewed_types']) == 15
for name, ty in cs['reviewed_types'].items():
    assert hashlib.sha256(ty.encode()).hexdigest() == cs['type_sha256'][name]
    assert name in ts

print(json.dumps({'passed': True, 'reviews_sha256': {
    str(geo_path.relative_to(ROOT)): sha(geo_path),
    str(child_path.relative_to(ROOT)): sha(child_path)},
    'verified_unique_file_bindings': len(checked), 'geometry_file_bindings': geo_count,
    'canonical_SM_modules_unchanged': 327, 'independently_reviewed_helpers': 64,
    'geometry_types_consumers_traces': [42, 31, 73],
    'contraction_child_types_consumers_traces': [22, 15, 37],
    'source_claim_acceptance_increment': 0, 'stage_complete': False}, indent=2))
