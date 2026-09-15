#!/usr/bin/env python3
"""Edit one row of work/lean/lean-declarations.json during the accept cycle.
  map_row.py implement <id> <declaration> <module>
  map_row.py hash <id>                       # print the row's statement hash from the last audit
  map_row.py accept <id> <author> <reviewer> <review_file>   # sets status accepted + hash from audit
  map_row.py show <id>
"""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
MAP = ROOT / 'work/lean/lean-declarations.json'
AUDIT = ROOT / 'work/checks/declaration-audit.json'
data = json.loads(MAP.read_text())
rows = {r['id']: r for r in data['declarations']}
cmd, rid = sys.argv[1], sys.argv[2]
row = rows[rid]
def save():
    MAP.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
if cmd == 'implement':
    row['declaration'], row['module'], row['status'] = sys.argv[3], sys.argv[4], 'implemented'
    save(); print('row', rid, '-> implemented', row['declaration'], row['module'])
elif cmd == 'hash':
    print(json.loads(AUDIT.read_text())['statement_hashes'][rid])
elif cmd == 'accept':
    h = json.loads(AUDIT.read_text())['statement_hashes'][rid]
    row.update({'status': 'accepted', 'author': sys.argv[3], 'reviewer': sys.argv[4],
                'statement_sha256': h, 'review_file': sys.argv[5],
                'parameters_reviewed': True, 'definition_equivalence_reviewed': True})
    save(); print('row', rid, '-> accepted, hash', h)
elif cmd == 'show':
    print(json.dumps(row, indent=1, ensure_ascii=False))
