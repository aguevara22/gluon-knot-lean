#!/usr/bin/env python3
"""Verify the current named-wall candidate/final receipt and review bindings."""
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
receipt_path = Path(sys.argv[1]).resolve()
receipt = json.loads(receipt_path.read_text())
audit_path = WORK / 'checks/declaration-audit.json'
audit = json.loads(audit_path.read_text())
prior = json.loads((WORK / 'checks/checkpoint-045-output.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert receipt['passed'] is True
assert receipt['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert set(receipt['bundle_sha256']) == set(prior['bundle_sha256'])
assert matches(ROOT, receipt['bundle_sha256'])
assert (WORK / 'checks/stage-development.json').read_bytes() == receipt_path.read_bytes()
old_sm = {k: v for k, v in prior['project_sha256'].items() if k.startswith('SM/')}
assert len(old_sm) == 213
assert matches(LEAN, old_sm)
assert audit['audit']['checked'] == receipt['audited_declarations']
assert len(audit['audit']['declarations']) == receipt['mapped_declarations']
for row in audit['audit']['declarations']:
    assert set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
main = next(row for row in audit['audit']['declarations']
            if row['declaration'] == 'SM.named_walls_definition')
semantic = hashlib.sha256(json.dumps(main['semantic_dependencies'], sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()
assert semantic == audit['statement_hashes']['def:walls']
assert main['kind'] == 'theorem'
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    for imported in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$',
                               (LEAN / (module.replace('.', '/') + '.lean')).read_text(), re.M):
        visit(imported)
visit('SM.NamedWallsDefinition')
closure = {'work/lean/' + m.replace('.', '/') + '.lean':
           sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}
assert len(closure) == 92
progress = snapshot()
assert not progress['evidence_issues']
mapping = json.loads((LEAN / 'lean-declarations.json').read_text())['declarations']
mapped = next(row for row in mapping if row['id'] == 'def:walls')
review_record = None
if mapped['status'] == 'accepted':
    rp = WORK / mapped['review_file']
    review = json.loads(rp.read_text())
    assert review['reviewed_files_sha256'] == closure
    assert mapped['statement_sha256'] == review['statement_sha256'] == semantic
    review_record = {'path': str(rp.relative_to(ROOT)), 'sha256': sha(rp)}
trace_path = WORK / 'checks/named-walls-types.log'
assert trace_path.is_file() and 'error:' not in trace_path.read_text()
out = {
    'passed': True, 'stage_accepted': receipt['stage_accepted'],
    'receipt_sha256': sha(receipt_path), 'audit_sha256': sha(audit_path),
    'SM_modules': sum(k.startswith('SM/') for k in receipt['project_sha256']),
    'audited_declarations': receipt['audited_declarations'],
    'mapped_claims': receipt['mapped_declarations'], 'project_files': len(receipt['project_sha256']),
    'frozen_files': len(receipt['bundle_sha256']), 'previous_SM_modules_unchanged': len(old_sm),
    'accepted_reviews': sum(row['status'] == 'accepted' for row in mapping),
    'trace_sha256': sha(trace_path),
    'main': {'declaration': main['declaration'], 'semantic_entries': len(main['semantic_dependencies']),
             'semantic_sha256': semantic, 'axioms': main['axioms'], 'support_files': len(closure),
             'review': review_record}, 'progress': progress,
}
target = receipt_path.with_name(receipt_path.name.replace('-output.json', '-verification.json'))
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
