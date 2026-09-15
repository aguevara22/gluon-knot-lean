#!/usr/bin/env python3
"""Check exact evidence for the four reviewed centre/wall components.

This verifies evidence bindings; it does not independently establish theorem
fidelity or accept thm:relgp. The original review reports provide that analysis.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / 'work'
LEAN = WORK / 'lean'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bindings(base, values):
    assert values
    for name, expected in values.items():
        path = (base / name).resolve()
        assert path.is_relative_to(base.resolve()), name
        assert sha(path) == expected, name


def closure(roots):
    seen = set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        path = LEAN / (module.replace('.', '/') + '.lean')
        for dep in re.findall(r'^import (SM\.[\w.]+)\s*$', path.read_text(), re.M):
            visit(dep)

    for root in roots:
        visit(root)
    return {'work/lean/' + m.replace('.', '/') + '.lean':
            sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}


reports = {}
for name in ['single-control-centers-port', 'point-control-geometry-prototype',
             'point-control-walls-prototype', 'concurrence-order-prototype']:
    path = WORK / 'reviews' / (name + '.json')
    review = json.loads(path.read_text())
    assert review['verdict'] == 'partial'
    assert review['implemented_scope_verdict'] == 'faithful'
    assert review['source_claim_accepted'] is False
    assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
    assert review['reviewer'] == 'review_chirotope-independent-20260910'
    assert sha(ROOT / review['source']) == review['source_sha256']
    actual = closure(review['import_closure_roots'])
    assert actual == review['reviewed_files_sha256']
    assert len(actual) == review['import_closure_file_count']
    bindings(ROOT, review['pins']['pin_files_sha256'])
    assert review['pins']['lean_toolchain'] == 'leanprover/lean4:v4.34.0-rc2'
    assert review['pins']['mathlib_revision'] == '85e3a25e006c35636f0e53b0e9296caca2685bc0'
    bindings((LEAN / '.lake/packages/mathlib').resolve(),
             review['pins']['additional_pinned_library_files_read_sha256'])
    bindings(ROOT, review['inherited_review_binding']['reviews_sha256'])
    for inherited in review['inherited_review_binding']['reviews_sha256']:
        bindings(ROOT, json.loads((ROOT / inherited).read_text())['reviewed_files_sha256'])
    if 'additional_source_interpretation_files_sha256' in review:
        bindings(ROOT, review['additional_source_interpretation_files_sha256'])
    for key in ['prototype_file', 'prototype_body']:
        if key in review:
            hash_key = 'prototype_sha256' if key == 'prototype_file' else key + '_sha256'
            assert sha(ROOT / review[key]) == review[hash_key]
    e = review['evidence']
    assert e['independent_kernel_exit_code'] == e['successful_build_exit_code'] == 0
    assert e['additional_examples_passed']
    assert len(e['additional_examples']) == e['additional_example_count']
    assert set(e['checked_declarations']) == set(e['declaration_axioms'])
    assert all(set(a) <= STANDARD for a in e['declaration_axioms'].values())
    for key in ['independent_trace_source', 'independent_trace_log',
                'successful_build_log', 'independent_closure_evidence']:
        assert sha(ROOT / e[key]) == e[key + '_sha256']
    assert sha(ROOT / e['root_result_file']) == e['root_result_sha256']
    root = json.loads((ROOT / e['root_result_file']).read_text())
    if name == 'single-control-centers-port':
        assert root['exit_code'] == 0 and root['session'] == e['successful_build_session']
        assert sha(WORK / root['log']) == root['log_sha256']
        assert sha(WORK / root['candidate']) == root['candidate_sha256']
        port = review['port_binding']
        bindings(LEAN, port['prior_SM_files_sha256'])
        assert sha(ROOT / port['new_module']) == port['new_module_sha256']
        assert sha(ROOT / port['prototype']) == port['prototype_sha256']
        original = (ROOT / port['prototype']).read_text().split('#print axioms', 1)[0]
        body = original[original.index('namespace SM'):].strip() + '\n'
        target = (ROOT / port['new_module']).read_text()
        assert target[target.index('namespace SM'):] == body
        assert hashlib.sha256(body.encode()).hexdigest() == port['body_sha256']
    else:
        assert root['successful_kernel_exit_code'] == 0
        assert root['successful_kernel_session'] == e['successful_build_session']
        bindings(WORK, root['files_sha256'])
    trace = (ROOT / e['independent_trace_log']).read_text()
    assert not re.search(r'error[:(]', trace) and 'sorryAx' not in trace
    parsed = {m.group(1): {s.strip() for s in m.group(2).split(',') if s.strip()}
              for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", trace)}
    for declaration, axioms in e['declaration_axioms'].items():
        assert parsed[declaration] == set(axioms), declaration
    assert not re.search(r'error[:(]', (ROOT / e['successful_build_log']).read_text())
    reports[name] = {'review_sha256': sha(path), 'reviewed_closure': len(actual),
                     'independent_axiom_sets': len(e['declaration_axioms']),
                     'examples': e['additional_example_count'], 'bindings_current': True}

out = {'passed': True, 'source_claim_accepted': False, 'original_proof_increment': 0,
       'components': reports,
       'scope': 'Exact file, review, kernel trace, source, pin and closure bindings only.'}
(WORK / 'checks/relgp-wall-evidence-verification.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
