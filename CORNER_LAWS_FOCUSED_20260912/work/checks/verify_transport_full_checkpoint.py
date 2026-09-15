#!/usr/bin/env python3
"""Verify the complete polynomial-controls candidate/final project and old reviews.

This script never supplies independent source acceptance. It reports the actual
map state and leaves the new full review to its independent reviewer.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.receipts import hashes, matches, project_files
from work.claim_progress import snapshot

WORK = ROOT / 'work'
LEAN = WORK / 'lean'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rp = Path(sys.argv[1]).resolve()
r = json.loads(rp.read_text())
old = json.loads((WORK / 'checks/checkpoint-050-output.json').read_text())
assert r['passed'] is True and r['stage_accepted'] is False
assert r['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert set(r['bundle_sha256']) == set(old['bundle_sha256'])
assert matches(ROOT, r['bundle_sha256'])
assert (WORK / 'checks/stage-development.json').read_bytes() == rp.read_bytes()
old_sm = {k: v for k, v in old['project_sha256'].items() if k.startswith('SM/')}
assert len(old_sm) == 242 and matches(LEAN, old_sm)
added = set(r['project_sha256']) - set(old['project_sha256'])
assert added == {'SM/' + m + '.lean' for m in (
    'PolynomialVertexSupport', 'AreaPolynomialSupport', 'SixEndpointTuples',
    'ConcurrencePolynomialSupport', 'EndpointCollapseWitness', 'ConcurrenceNonassociation',
    'PolynomialControlFamily', 'PolynomialControlRepresentatives', 'TransportPolynomials')}
assert {k for k, v in old['project_sha256'].items() if r['project_sha256'][k] != v} == {
    'Supplemental.lean', 'lean-declarations.json'}
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = LEAN / (module.replace('.', '/') + '.lean')
    for imported in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$', path.read_text(), re.M):
        visit(imported)
visit('SM.TransportPolynomials')
closure = {'work/lean/' + m.replace('.', '/') + '.lean':
           sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}
assert len(closure) == 39
audit_path = WORK / 'checks/declaration-audit.json'
audit = json.loads(audit_path.read_text())
assert audit['audit']['checked'] == r['audited_declarations']
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(d['axioms']) <= standard for d in audit['audit']['declarations'])
main = next(d for d in audit['audit']['declarations'] if d['declaration'] == 'SM.transport_polynomials')
assert main['kind'] == 'theorem' and main['module'] == 'SM.TransportPolynomials'
semantic = hashlib.sha256(json.dumps(main['semantic_dependencies'], sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()
assert audit['statement_hashes']['lem:transport-polynomials'] == semantic
mapping = json.loads((LEAN / 'lean-declarations.json').read_text())['declarations']
row = next(x for x in mapping if x['id'] == 'lem:transport-polynomials')
review_record = None
if row['status'] == 'accepted':
    review_path = WORK / row['review_file']
    review = json.loads(review_path.read_text())
    assert review['reviewed_files_sha256'] == closure
    assert row['statement_sha256'] == review['statement_sha256'] == semantic
    assert review['id'] == row['id'] and review['verdict'] == 'faithful'
    assert row['reviewer'] == review['reviewer'] != row['author']
    assert row['parameters_reviewed'] and row['definition_equivalence_reviewed']
    assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
    assert sha(ROOT / review['source']) == review['source_sha256']
    assert matches(ROOT, review['pins']['pin_files_sha256'])
    library_root = (LEAN / '.lake/packages/mathlib').resolve()
    for name, digest in review['pins']['inherited_reviewed_library_files_sha256'].items():
        library_path = (ROOT / name).resolve()
        assert library_path.is_relative_to(library_root) and sha(library_path) == digest
    binding = review['receipt_binding']
    assert sha(ROOT / binding['receipt']) == binding['receipt_sha256']
    assert binding['main_semantic_sha256'] == semantic
    evidence = review['independent_check_evidence']
    assert evidence['successful_kernel_exit_code'] == 0
    assert evidence['checked_axiom_sets'] == len(evidence['declaration_axioms']) == 28
    assert all(set(v) <= standard for v in evidence['declaration_axioms'].values())
    assert evidence['NeZero_from_source_size_checked']
    for name in ('type_definition_axiom_trace_source', 'type_definition_axiom_trace_log',
                 'successful_implementation_build_log'):
        assert sha(ROOT / evidence[name]) == evidence[name + '_sha256']
    assert matches(ROOT, review['inherited_review_binding']['prior_partial_reports_sha256'])
    candidate = json.loads((ROOT / binding['receipt']).read_text())
    assert {k for k, v in candidate['project_sha256'].items()
            if r['project_sha256'][k] != v} == {'lean-declarations.json'}
    review_record = {'path': str(review_path.relative_to(ROOT)), 'sha256': sha(review_path)}
else:
    assert row['status'] == 'review'
progress = snapshot()
assert not progress['evidence_issues']
assert progress['proved_original_claims'] == (14 if review_record else 13)
assert progress['accepted_original_checklist'] == (29 if review_record else 28)
if not review_record:
    assert progress['compiled_proofs_awaiting_review'] == ['lem:transport-polynomials']
out = {'passed': True, 'stage_accepted': False, 'receipt_sha256': sha(rp),
       'audit_sha256': sha(audit_path), 'previous_SM_modules_unchanged': 242,
       'SM_modules': 251, 'audited_declarations': r['audited_declarations'],
       'project_files': len(r['project_sha256']), 'frozen_files': len(r['bundle_sha256']),
       'main': {'declaration': main['declaration'], 'semantic_entries': len(main['semantic_dependencies']),
                'semantic_sha256': semantic, 'axioms': main['axioms'], 'support_files': len(closure),
                'status': row['status'], 'review': review_record},
       'all_existing_accepted_review_bindings_current': True, 'progress': progress}
target = rp.with_name(rp.name.replace('-output.json', '-full-transport-verification.json'))
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
