#!/usr/bin/env python3
"""Write work/reviews/<slug>.json from the summarized workflow output and set the map row to
accepted.  Usage:
  write_review_and_accept.py <row-id> <slug> <declaration> <module> <source-file> <source-locator>
      <excerpt-file (relative to work/)> <statement-file (relative to work/)> <primary-index>
      <lens-names comma-separated> <kernel-check text> <hypothesis/notes text>
Requires work/reviews/<slug>-review-workflow-raw.json (from summarize_review.py) and the current
work/checks/declaration-audit.json (row at implemented, checker passed)."""
import json, hashlib, datetime, sys
from pathlib import Path
(rid, slug, decl, module, source_file, locator, excerpt, statement_file, primary, lenses, kernel, notes) = sys.argv[1:13]
primary = int(primary); lenses = lenses.split(',')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
obj = json.load(open(f'work/reviews/{slug}-review-workflow-raw.json'))
reviews, refuters = obj['reviews'], obj['refuters']
assert all(r['verdict'] == 'faithful' for r in reviews)
allow_notes = len(sys.argv) > 13 and sys.argv[13] == 'allow-doc-notes'
assert allow_notes or all(not r['discrepancies'] for r in reviews), 'discrepancies present; pass allow-doc-notes only for documentation-only notes'
assert all(not r['refuted'] for r in refuters)
audit = json.load(open('work/checks/declaration-audit.json'))
h = audit['statement_hashes'][rid]
files = set()
for r in reviews: files.update(f.strip() for f in r['reviewer_files_read'])
for r in refuters: files.update(f.strip() for f in r.get('files_read', []))
def _is_file(f):
    try:
        return len(f) < 240 and Path(f).is_file()
    except OSError:
        return False
norm = {str(Path(f)): sha(f) for f in files if _is_file(f)}
modfile = 'work/lean/' + module.replace('.', '/') + '.lean'
norm[modfile] = sha(modfile)
defs = set()
for r in reviews: defs.update(r['supporting_definitions_inspected'])
WORDS = {1: 'One', 2: 'Two', 3: 'Three', 4: 'Four', 5: 'Five', 6: 'Six', 7: 'Seven', 8: 'Eight'}
n_rev, n_ref = len(reviews), len(refuters)
reviewer_id = ("reviewer-pod-claude-fable-5-1-20260913 (independent Claude Code workflow subagents, model claude-fable-5-1; "
  "AI reviewers; each given only the printed SM15 source, the Lean type with every proof replaced by sorry (" + statement_file + ") "
  "and the Lean definition modules; no authorship of the statement; proof withheld. Primary reviewer: lens '" + lenses[primary] +
  "'; countersigned by the lenses " + ", ".join("'" + l + "'" for i, l in enumerate(lenses) if i != primary) +
  "; " + WORDS[n_ref].lower() + " adversarial refuters found no discrepancy)")
rec = {
 'id': rid, 'reviewer': reviewer_id, 'statement_sha256': h, 'verdict': 'faithful',
 'reason': reviews[primary]['reason'], 'source_sha256': sha(source_file),
 'parameters_reviewed': True, 'definition_equivalence_reviewed': True,
 'source_frame': 'SM15', 'source_locator': locator, 'source_excerpt_file': excerpt,
 'declaration': decl, 'module': module,
 'ai_review_disclosure': ("AI review. " + WORDS[n_rev + n_ref] + " separate Claude Code subagents (model claude-fable-5-1) were spawned by the executor on " +
   datetime.date.today().isoformat() + " in one workflow: " + WORDS[n_rev].lower() + " reviewers with distinct lenses and " + WORDS[n_ref].lower() + " adversarial refuters instructed to find any discrepancy. "
   "Each received only the printed SM15 source files, the row's Lean text with every proof replaced by sorry (" + statement_file +
   "), and the Lean definition modules; none saw the proof module " + modfile + " or the executor's reasoning. The executor (author) is "
   "executor-pod-claude-fable-5-1-20260913, a different session of the same model. No human has read these reviews."),
 'primary_lens': lenses[primary],
 'discrepancies': reviews[primary]['discrepancies'],
 'stronger_than_source': reviews[primary]['stronger_than_source'],
 'weaker_than_source': reviews[primary]['weaker_than_source'],
 'countersignatures': [{'lens': lenses[i], 'verdict': reviews[i]['verdict'], 'reason': reviews[i]['reason'],
                        'discrepancies': reviews[i]['discrepancies'], 'stronger_than_source': reviews[i]['stronger_than_source'],
                        'weaker_than_source': reviews[i]['weaker_than_source']} for i in range(len(reviews)) if i != primary],
 'adversarial_refutations': [{'refuter': f'refute:{i+1}', 'refuted': r['refuted'], 'argument': r['argument'], 'evidence': r.get('evidence', '')}
                             for i, r in enumerate(refuters)],
 'executor_notes': notes,
 'supporting_definitions_inspected': sorted(defs), 'reviewer_files_read': sorted(files),
 'reviewed_files_sha256': dict(sorted(norm.items())), 'kernel_check': kernel,
 'review_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
}
Path(f'work/reviews/{slug}.json').write_text(json.dumps(rec, indent=2, ensure_ascii=False) + '\n')
MAP = Path('work/lean/lean-declarations.json'); data = json.loads(MAP.read_text())
row = [r for r in data['declarations'] if r['id'] == rid][0]
assert row['declaration'] == decl and row['module'] == module and row['status'] == 'implemented'
row.update({'status': 'accepted', 'author': 'executor-pod-claude-fable-5-1-20260913', 'reviewer': reviewer_id,
            'statement_sha256': h, 'review_file': f'reviews/{slug}.json',
            'parameters_reviewed': True, 'definition_equivalence_reviewed': True})
MAP.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
print(f'{rid}: review written (files bound {len(norm)}, defs {len(defs)}), row accepted, hash {h[:16]}…')
