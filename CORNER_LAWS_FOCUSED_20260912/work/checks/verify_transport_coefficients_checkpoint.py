#!/usr/bin/env python3
"""Verify audit050 and the independent coefficient/specialization partial review."""
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
rp = WORK / 'checks/checkpoint-050-output.json'
r = json.loads(rp.read_text())
old = json.loads((WORK / 'checks/checkpoint-049-output.json').read_text())
assert r['passed'] is True and r['stage_accepted'] is False
assert r['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert set(r['bundle_sha256']) == set(old['bundle_sha256'])
assert matches(ROOT, r['bundle_sha256'])
assert (WORK / 'checks/stage-development.json').read_bytes() == rp.read_bytes()
old_sm = {k: v for k, v in old['project_sha256'].items() if k.startswith('SM/')}
assert len(old_sm) == 237 and matches(LEAN, old_sm)
added = set(r['project_sha256']) - set(old['project_sha256'])
assert added == {'SM/CoordinateIsolation.lean', 'SM/AffineResultant.lean',
    'SM/RealAffineRoots.lean', 'SM/CoefficientSpecialization.lean',
    'SM/GeometricCoordinateSpecialization.lean'}
assert {k for k, v in old['project_sha256'].items() if r['project_sha256'][k] != v} == {'Supplemental.lean'}

def closure(module):
    seen = set()
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        path = LEAN / (m.replace('.', '/') + '.lean')
        for imported in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$', path.read_text(), re.M):
            visit(imported)
    visit(module)
    return {'work/lean/' + m.replace('.', '/') + '.lean':
            sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}

audit_path = WORK / 'checks/declaration-audit.json'
audit = json.loads(audit_path.read_text())
assert audit['audit']['checked'] == r['audited_declarations']
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(d['axioms']) <= standard for d in audit['audit']['declarations'])
records = []
for name, module, trace_count in (
    ('transport-coefficients-partial', 'SM.GeometricCoordinateSpecialization', 22),):
    path = WORK / 'reviews' / (name + '.json')
    review = json.loads(path.read_text())
    files = closure(module)
    assert len(files) == 28 and review['reviewed_files_sha256'] == files
    assert review['source_id'] == 'lem:transport-polynomials'
    assert review['reviewer'] == 'review_chirotope-independent-20260910'
    assert review['verdict'] == 'partial' and review['implemented_scope_verdict'] == 'faithful'
    assert review['source_claim_accepted'] is False
    assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
    assert sha(ROOT / review['source']) == review['source_sha256']
    assert matches(ROOT, review['pins']['pin_files_sha256'])
    library_root = (LEAN / '.lake/packages/mathlib').resolve()
    for key, value in review['pins']['pinned_library_files_sha256'].items():
        library_path = (ROOT / key).resolve()
        assert library_path.is_relative_to(library_root) and sha(library_path) == value
    binding = review['receipt_binding']
    assert sha(rp) == binding['receipt_sha256']
    assert sha(audit_path) == binding['declaration_audit_sha256']
    evidence = review['evidence']
    for key in ('independent_trace_source', 'independent_trace_log'):
        assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']
    assert evidence['independent_kernel_exit_code'] == 0
    assert len(evidence['successful_build_logs_sha256']) == 3
    for log, digest in evidence['successful_build_logs_sha256'].items():
        assert sha(ROOT / log) == digest
    assert evidence['successful_build_exit_codes'] == [0, 0, 0]
    assert len(evidence['declaration_axioms']) == trace_count
    assert all(set(a) <= standard for a in evidence['declaration_axioms'].values())
    records.append({'review': name, 'sha256': sha(path), 'closure_files': len(files),
                    'traced_declarations': trace_count})
progress = snapshot()
assert not progress['evidence_issues']
assert progress['proved_original_claims'] == 13
assert progress['accepted_original_checklist'] == 28
out = {'passed': True, 'stage_accepted': False, 'receipt_sha256': sha(rp),
       'audit_sha256': sha(audit_path), 'previous_SM_modules_unchanged': 237,
       'SM_modules': 242, 'audited_declarations': r['audited_declarations'],
       'project_files': len(r['project_sha256']), 'frozen_files': len(r['bundle_sha256']),
       'partial_reviews': records, 'all_accepted_review_bindings_current': True,
       'progress': progress}
(WORK / 'checks/checkpoint-050-partial-reviews-verification.json').write_text(
    json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
