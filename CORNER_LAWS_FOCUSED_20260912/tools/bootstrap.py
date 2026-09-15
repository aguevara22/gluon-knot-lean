#!/usr/bin/env python3
"""Initialize writable work without network access or overwriting existing files."""
import sys
sys.dont_write_bytecode = True
import argparse
import csv
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.scope import SPEC, source_path
EXTRA = SPEC['extra']


def create(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open('x', encoding='utf-8') as f:
            f.write(text)
    except FileExistsError:
        pass


def initialize(work):
    work.mkdir(parents=True, exist_ok=True)
    for path in (ROOT / 'lean').rglob('*'):
        if path.is_file() and not any(p in {'.lake', '__pycache__'} for p in path.parts):
            create(work / 'lean' / path.relative_to(ROOT / 'lean'), path.read_text())
    rows = list(csv.DictReader((ROOT / 'blueprint/NODES.tsv').open(), delimiter='\t'))
    policy = json.loads((ROOT / 'lean/axiom-policy.json').read_text())
    fixed = policy['literature'] | policy['targets'] | {'hyp:R': 'SM.hyp_R'}
    records = []
    for row in rows:
        if row['action'] in {'SKIP', 'CERTIFICATE'}:
            continue
        records.append({'id': row['id'], 'labels': row['labels'].split(),
                        'source': source_path(row), 'line': int(row['line']),
                        'stage1': row['stage1'] == 'Y', 'declaration': fixed.get(row['id'], ''),
                        'module': '', 'status': 'pending', 'author': '',
                        'reviewer': '', 'statement_sha256': '', 'review_file': '',
                        'parameters_reviewed': False, 'definition_equivalence_reviewed': False})
    for name in EXTRA:
        records.append({'id': name, 'declaration': fixed.get(name, ''), 'module': '',
                        'status': 'pending', 'author': '', 'reviewer': '',
                        'statement_sha256': '', 'review_file': '',
                        'parameters_reviewed': False, 'definition_equivalence_reviewed': False})
    create(work / 'lean/lean-declarations.json', json.dumps({'schema': 1, 'declarations': records}, indent=2) + '\n')
    create(work / 'STATUS.md', '''# Execution checkpoint

Infrastructure initialized. No SM, CV, R, or Bridge statement is yet formalized.
Next: read AUTONOMOUS_EXECUTION.md and OPEN_WORK.md in the bundle, install the
pinned toolchain, then run lake update, lake exe cache get, and lake build in
work/lean. Start source-faithful foundational definitions and independent review.
The declaration map contains pending rows, not accepted claims.
Run python3 tools/progress.py --once after each checkpoint. During execution,
report claims verified/total claims every fifteen minutes; see PROGRESS.md
in the bundle for the automatic command wrapper.

Keep this file current after each work unit with results, blockers, and the next
executable step. The author is unavailable; record notes without waiting.
''')
    tasks = [{'id': name, 'state': 'ready', 'worker': 'execution-lead', 'dependencies': [],
              'next_action': action, 'evidence': []} for name, action in SPEC['tasks']]
    create(work / 'TASKS.json', json.dumps(tasks, indent=2) + '\n')
    create(work / 'AUTHOR_NOTES.md', '# Nonblocking author notes\n\nNo author response is required to begin or continue. Record decisions and reasons here.\n')
    for dirname in ['reports', 'reviews', 'repairs', 'certificates', 'delivery', 'decisions']:
        (work / dirname).mkdir(exist_ok=True)
    create(work / 'certificates/index.json', json.dumps({'certificates': [
        {'id': name, 'status': 'pending', 'receipt': '', 'receipt_sha256': '',
         'author': '', 'reviewer': ''} for name in SPEC['certificates']]}, indent=2) + '\n')
    print('Ready to execute; existing files preserved:', work)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, default=ROOT / 'work')
    args = parser.parse_args()
    initialize(args.work_dir.resolve())
