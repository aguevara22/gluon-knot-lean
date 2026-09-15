#!/usr/bin/env python3
"""Verify current joint-choice integration without accepting thm:relgp.

Whole-project kernel evidence, exact file inventories, frozen sources, prior
accepted semantic bindings and bounded new independent reviews are all checked.
No helper result changes the original proof count.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / 'work'
LEAN = WORK / 'lean'
sys.path.insert(0, str(ROOT))
from tools.receipts import hashes, matches, project_files
from work.claim_progress import snapshot

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rp = Path(sys.argv[1]).resolve()
receipt = json.loads(rp.read_text())
old = json.loads((WORK / 'checks/checkpoint-052-output.json').read_text())
assert receipt['passed'] is True and receipt['stage_accepted'] is False
assert receipt['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert receipt['bundle_sha256'] == old['bundle_sha256']
assert matches(ROOT, receipt['bundle_sha256'])
assert (WORK / 'checks/stage-development.json').read_bytes() == rp.read_bytes()
old_sm = {k: v for k, v in old['project_sha256'].items() if k.startswith('SM/')}
assert len(old_sm) == 251 and matches(LEAN, old_sm)
new_modules = ['MultivariateAvoidance', 'WaypointPullback', 'CoordinateWaypointLeg',
               'JointWaypointConstraints', 'WaypointOpenDomain',
               'ScalarCoordinateTopology', 'CentralLegCollision']
assert set(receipt['project_sha256']) - set(old['project_sha256']) == {
    'SM/' + m + '.lean' for m in new_modules}
assert {k for k, v in old['project_sha256'].items()
        if receipt['project_sha256'][k] != v} == {'Supplemental.lean'}

audit_path = WORK / 'checks/declaration-audit.json'
audit = json.loads(audit_path.read_text())
assert audit['audit']['checked'] == receipt['audited_declarations']
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(d['axioms']) <= standard for d in audit['audit']['declarations'])
rows = json.loads((LEAN / 'lean-declarations.json').read_text())['declarations']
accepted = [r for r in rows if r['status'] == 'accepted']
assert len(accepted) == 30
for row in accepted:
    review = json.loads((WORK / row['review_file']).read_text())
    assert row['statement_sha256'] == review['statement_sha256'] == audit['statement_hashes'][row['id']]
    assert row['reviewer'] == review['reviewer'] != row['author']
    assert review['verdict'] == 'faithful'
    assert matches(ROOT, review['reviewed_files_sha256'])
    # Older accepted chapter-1 reviews record its hash without a path field.
    source = review.get('source', 'reference/SM/sm-1-polygons.tex')
    assert sha(ROOT / source) == review['source_sha256']

def closure(module):
    seen = set()
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        p = LEAN / (m.replace('.', '/') + '.lean')
        for dep in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$', p.read_text(), re.M):
            visit(dep)
    visit(module)
    return {'work/lean/' + m.replace('.', '/') + '.lean':
            sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}

review_bindings = []
for filename, module in [('joint-waypoint-choice.json', 'SM.WaypointOpenDomain'),
                         ('central-leg-collision.json', 'SM.CentralLegCollision')]:
    p = WORK / 'reviews' / filename
    r = json.loads(p.read_text())
    assert r['verdict'] == 'partial' and r['implemented_scope_verdict'] == 'faithful'
    assert r['source_claim_accepted'] is False
    assert r['reviewer'] == 'review_chirotope-independent-20260910'
    assert r['reviewed_files_sha256'] == closure(module)
    assert sha(ROOT / r['source']) == r['source_sha256']
    assert r['parameters_reviewed'] and r['definition_equivalence_reviewed']
    assert matches(ROOT, r['pins']['pin_files_sha256'])
    assert r['pins']['lean_toolchain'] == 'leanprover/lean4:v4.34.0-rc2'
    assert r['pins']['mathlib_revision'] == '85e3a25e006c35636f0e53b0e9296caca2685bc0'
    evidence = r['evidence']
    assert evidence['independent_kernel_exit_code'] == 0
    assert evidence['successful_build_exit_code'] == 0
    assert evidence['checked_declarations'] == len(evidence['declaration_axioms'])
    assert all(set(a) <= standard for a in evidence['declaration_axioms'].values())
    for key in ('independent_trace_source', 'independent_trace_log', 'successful_build_log'):
        assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']
    trace = (ROOT / evidence['independent_trace_log']).read_text()
    assert 'error:' not in trace and 'sorryAx' not in trace
    review_bindings.append({'file': str(p.relative_to(ROOT)), 'sha256': sha(p),
                            'SM_import_closure': len(closure(module)),
                            'independent_axiom_sets': evidence['checked_declarations']})

prototype = (WORK / 'checks/MultivariateAvoidance.prototype.lean').read_text()
port = (LEAN / 'SM/MultivariateAvoidance.lean').read_text()
assert prototype[prototype.index('namespace SM'):prototype.index('\n#print axioms')].strip() == \
       port[port.index('namespace SM'):].strip()
progress = snapshot()
assert not progress['evidence_issues']
assert progress['proved_original_claims'] == 14
assert progress['accepted_original_checklist'] == 29
assert progress['compiled_proofs_awaiting_review'] == []
out = {'passed': True, 'stage_accepted': False, 'receipt_sha256': sha(rp),
       'audit_sha256': sha(audit_path), 'previous_SM_modules_unchanged': 251,
       'SM_modules': 258, 'new_modules': new_modules,
       'audited_declarations': receipt['audited_declarations'],
       'project_files': len(receipt['project_sha256']),
       'frozen_files': len(receipt['bundle_sha256']),
       'accepted_review_bindings_current': len(accepted),
       'review_bindings': review_bindings, 'prototype_math_port_exact': True,
       'original_thm_relgp_accepted': False, 'progress': progress}
target = rp.with_name(rp.name.replace('-output.json', '-joint-waypoint-verification.json'))
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
