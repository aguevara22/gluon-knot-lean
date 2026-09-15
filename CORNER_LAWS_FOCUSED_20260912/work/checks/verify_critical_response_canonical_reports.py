"""Verify sealed independent canonical evidence; does not replace source review."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
checked = {}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def binding(name, expected):
    path = ROOT / name
    assert path.is_file(), name
    assert sha(path) == expected, name
    checked[name] = expected


def walk(value):
    if isinstance(value, dict):
        for key, item in value.items():
            if isinstance(item, str) and re.fullmatch(r'[0-9a-f]{64}', item):
                if key.startswith(('work/', 'reference/', 'provenance/')):
                    binding(key, item)
                elif key.endswith('_sha256'):
                    source = value.get(key[:-7])
                    if isinstance(source, str) and source.startswith(('work/', 'reference/', 'provenance/')):
                        binding(source, item)
            walk(item)
    elif isinstance(value, list):
        for item in value:
            walk(item)


reports = {}
for name in ['critical-response-port', 'critical-source-response-canonical-partial']:
    path = ROOT / 'work/reviews' / (name + '.json')
    report = json.loads(path.read_text())
    assert report['verdict'] == 'faithful'
    assert report['reviewer'] != report['implementer']
    assert report['parameters_reviewed'] and report['definition_equivalence_reviewed']
    assert not report['source_claim_accepted']
    assert report['in_theorem_library']
    ev = report['evidence']
    assert ev['independent_kernel_session'] == 98007
    assert ev['independent_kernel_exit_code'] == 0 and ev['first_independent_run_passed']
    assert ev['declaration_count'] == 53 and ev['additional_example_count'] == 41
    assert ev['all_53_prototype_canonical_printed_types_equal']
    assert len(report['reviewed_files_sha256']) == report['import_closure_file_count'] == 40
    walk(report)
    log = (ROOT / ev['independent_trace_log']).read_text()
    assert 'error:' not in log
    traces = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    assert len(traces) == 94
    assert len({name for name, _ in traces}) == 94
    assert all(set(a.strip() for a in axioms.split(',') if a.strip()) <=
               {'propext', 'Classical.choice', 'Quot.sound'} for _, axioms in traces)
    assert set(report['main_declarations']) <= {name for name, _ in traces}
    reports[str(path.relative_to(ROOT))] = sha(path)

print(json.dumps({'passed': True, 'reports_sha256': reports,
                  'verified_unique_file_bindings': len(checked),
                  'independent_kernel_session': 98007,
                  'independent_kernel_exit_code': 0,
                  'reviewed_declarations': 53, 'consumer_checks': 41,
                  'standard_or_empty_traces': 94,
                  'source_claim_acceptance_increment': 0,
                  'stage_complete': False}, indent=2))
