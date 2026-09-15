"""Bind the independent partial geometry review to its actual files and traces."""
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
                if key.startswith(('work/', 'reference/', 'provenance/')):
                    bind(key, value)
                elif key.endswith('_sha256'):
                    name = obj.get(key[:-7])
                    if isinstance(name, str) and name.startswith(('work/', 'reference/', 'provenance/')):
                        bind(name, value)
            walk(value)
    elif isinstance(obj, list):
        for value in obj:
            walk(value)


path = ROOT / 'work/reviews/boundary-gate-stability-prototype.json'
report = json.loads(path.read_text())
assert report['verdict'] == report['implemented_scope_verdict'] == 'faithful'
assert report['parameters_reviewed'] and report['definition_equivalence_reviewed']
assert report['reviewer'] != report['implementer']
assert not report['source_claim_accepted'] and not report['in_theorem_library']
assert len(report['main_declarations']) == 27
assert report['embedded_body_count'] == 5 and report['import_closure_file_count'] == 54
ev = report['evidence']
assert ev['independent_kernel_session'] == 23810 and ev['independent_kernel_exit_code'] == 0
assert ev['declaration_count'] == 27 and ev['additional_example_count'] == 19
assert ev['additional_examples_passed']
walk(report)
for name, expected in report['prototype_files_sha256'].items():
    bind('work/checks/' + name + '.prototype.lean', expected)

closure = json.loads((ROOT / ev['independent_closure_evidence']).read_text())
assert closure['SM_closure_count'] == 54
assert len(closure['all_327_canonical_SM_files_sha256']) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327
walk(closure)
for name in closure['root_receipts_sha256']:
    receipt = json.loads((ROOT / name).read_text())
    assert receipt['exit_code'] == 0
    walk(receipt)

types = json.loads((ROOT / ev['reviewed_types']).read_text())
assert len(types['types']) == len(types['type_sha256']) == 27
assert set(types['types']) == set(report['main_declarations'])
for name, ty in types['types'].items():
    assert hashlib.sha256(ty.encode()).hexdigest() == types['type_sha256'][name], name
log = (ROOT / ev['independent_trace_log']).read_text()
assert 'error:' not in log
traces = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
assert len(traces) == len({name for name, _ in traces}) == 46
assert all(set(a.strip() for a in axioms.split(',') if a.strip()) <=
           {'propext', 'Classical.choice', 'Quot.sound'} for _, axioms in traces)
assert set(report['main_declarations']) <= {name for name, _ in traces}

print(json.dumps({'passed': True, 'review': str(path.relative_to(ROOT)),
                  'review_sha256': sha(path), 'verified_unique_file_bindings': len(checked),
                  'canonical_SM_modules_unchanged': 327,
                  'independent_kernel_session': 23810, 'independent_kernel_exit_code': 0,
                  'reviewed_declarations': 27, 'consumer_checks': 19,
                  'standard_or_empty_traces': 46, 'source_claim_acceptance_increment': 0,
                  'stage_complete': False}, indent=2))
