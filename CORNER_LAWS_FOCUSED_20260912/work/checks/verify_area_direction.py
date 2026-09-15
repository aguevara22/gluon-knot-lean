#!/usr/bin/env python3
"""Recheck audit048, all existing acceptances, and the partial Δ/H review."""
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
receipt_path = WORK / 'checks/checkpoint-048-output.json'
receipt = json.loads(receipt_path.read_text())
prior = json.loads((WORK / 'checks/checkpoint-047-output.json').read_text())
review_path = WORK / 'reviews/transport-area-direction-partial.json'
review = json.loads(review_path.read_text())
assert receipt['passed'] is True and receipt['stage_accepted'] is False
assert receipt['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert set(receipt['bundle_sha256']) == set(prior['bundle_sha256'])
assert matches(ROOT, receipt['bundle_sha256'])
assert (WORK / 'checks/stage-development.json').read_bytes() == receipt_path.read_bytes()
old_sm = {k: v for k, v in prior['project_sha256'].items() if k.startswith('SM/')}
assert len(old_sm) == 226 and matches(LEAN, old_sm)
added = set(receipt['project_sha256']) - set(prior['project_sha256'])
assert added == {'SM/DeterminantPolynomial.lean', 'SM/PolynomialShear.lean',
                 'SM/CoordinatePolynomials.lean', 'SM/DirectionPolynomials.lean'}
changed = {k for k, v in prior['project_sha256'].items() if receipt['project_sha256'][k] != v}
assert changed == {'Supplemental.lean'}
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = LEAN / (module.replace('.', '/') + '.lean')
    for imported in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$', path.read_text(), re.M):
        visit(imported)
visit('SM.DirectionPolynomials')
closure = {'work/lean/' + m.replace('.', '/') + '.lean':
           sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}
assert len(closure) == 8 and review['reviewed_files_sha256'] == closure
assert review['reviewer'] == 'review_chirotope-independent-20260910'
assert review['verdict'] == 'partial' and review['implemented_scope_verdict'] == 'faithful'
assert review['source_claim_accepted'] is False
assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
assert sha(ROOT / review['source']) == review['source_sha256']
assert matches(ROOT, review['pins']['pin_files_sha256'])
# Library files resolve through the disclosed pinned shared dependency cache;
# project/frozen files above still require the stricter local-path check.
library_root = (LEAN / '.lake/packages/mathlib').resolve()
for name, expected in review['pins']['pinned_library_files_sha256'].items():
    path = (ROOT / name).resolve()
    assert path.is_relative_to(library_root) and sha(path) == expected
binding = review['receipt_binding']
assert sha(receipt_path) == binding['receipt_sha256']
assert sha(ROOT / binding['declaration_audit']) == binding['declaration_audit_sha256']
evidence = review['evidence']
for key in ('independent_trace_source', 'independent_trace_log'):
    assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']
assert evidence['independent_kernel_exit_code'] == 0
assert matches(ROOT, evidence['build_logs_sha256'])
assert len(evidence['declaration_axioms']) == 13
assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for a in evidence['declaration_axioms'].values())
progress = snapshot()
assert not progress['evidence_issues']
assert progress['proved_original_claims'] == 13
assert progress['accepted_original_checklist'] == 28
out = {'passed': True, 'stage_accepted': False, 'receipt_sha256': sha(receipt_path),
       'review_sha256': sha(review_path), 'previous_SM_modules_unchanged': 226,
       'SM_modules': 230, 'audited_declarations': receipt['audited_declarations'],
       'project_files': len(receipt['project_sha256']), 'partial_closure_files': len(closure),
       'all_accepted_review_bindings_current': True, 'progress': progress}
(WORK / 'checks/checkpoint-048-partial-review-verification.json').write_text(
    json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
