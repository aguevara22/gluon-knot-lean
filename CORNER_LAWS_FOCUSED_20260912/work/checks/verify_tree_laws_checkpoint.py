#!/usr/bin/env python3
"""Check exact source-review bindings and the current tree-law checkpoint.
This verifies evidence consistency; independent source review supplies fidelity.
It never counts helpers or declares the full focused stage complete.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
W = ROOT / 'work'
C = W / 'checks'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
REVIEW_HASHES = {'def-treesum.json': '699286e490aa7af29a65d75be3bf339eba379c2659f4e8578a451b8332d7d269',
 'lem-treesum-trees.json': 'b74aa65b358694a551b4f85524cfae49a3618d49003516fe949faf8a6bcf1fa9',
 'prop-A-chamber.json': 'd5b51eeddbe36755cb1ea0ff1c6eea28001069c43dc2b82b5141aa542c61f147',
 'tree-laws-port.json': '331638bacca329bf4ad0982b876dc9e17a2a9ca0516466a15fba6e159181b5e4'}
CLAIMS = {'def:treesum': ('SM.treesumData', 'SM.TreeCoefficient', 'def-treesum.json'),
 'lem:treesum-trees': ('SM.treesum_trees',
                       'SM.PlaneTreeFormal',
                       'lem-treesum-trees.json'),
 'prop:A-chamber': ('SM.A_chamber', 'SM.TreeChamber', 'prop-A-chamber.json')}

def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def checkhash(p, expected):
 assert p.is_file() and sha(p) == expected, str(p)
def pairs(d):
 for k, v in d.items():
  if k.endswith('_sha256') and isinstance(v, str):
   base = k[:-7]
   if base in d and isinstance(d[base], str): checkhash(ROOT / d[base], v)

receipt_path = Path(sys.argv[1])
if not receipt_path.is_absolute(): receipt_path = ROOT / receipt_path
receipt = read(receipt_path)
assert receipt['passed'] and not receipt['stage_accepted']
assert receipt['mapped_declarations'] == 37 and receipt['audited_declarations'] == 3719
for f, x in receipt['project_sha256'].items(): checkhash(W / 'lean' / f, x)
for f, x in receipt['bundle_sha256'].items(): checkhash(ROOT / f, x)
audit = read(C / 'declaration-audit.json')
old = read(C / 'checkpoint-061-declaration-audit.json')
for key, x in old['statement_hashes'].items(): assert audit['statement_hashes'][key] == x, key
actual = {d['declaration']: d for d in audit['audit']['declarations']}
assert all(set(d['axioms']) <= STANDARD for d in actual.values())
prep = read(C / 'tree-laws-port-preparation-with-chamber.json')
assert len(prep['prior_SM_files_sha256']) == 288
assert len(list((W / 'lean/SM').glob('*.lean'))) == 294
for f, x in prep['prior_SM_files_sha256'].items(): checkhash(W / 'lean' / f, x)
for f, d in prep['new_modules'].items():
 checkhash(ROOT / f, d['candidate_sha256'])
 assert (ROOT / f).read_bytes() == (ROOT / d['candidate']).read_bytes()
 for frag in d['source_fragments']: checkhash(ROOT / frag['source'], frag['source_sha256'])

for name, expected in REVIEW_HASHES.items():
 p = W / 'reviews' / name; checkhash(p, expected); r = read(p)
 assert r['verdict'] == 'faithful' and r['reason']
 assert r['reviewer'] != r['implementer']
 assert r['parameters_reviewed'] and r['definition_equivalence_reviewed']
 for f, x in r['reviewed_files_sha256'].items(): checkhash(ROOT / f, x)
 pairs(r)
 e = r['evidence']; pairs(e)
 checkhash(ROOT / e['root_result_file'], e['root_result_sha256'])
 assert e['independent_kernel_session'] == 3756 and e['independent_kernel_exit_code'] == 0
 assert e['successful_build_session'] == 14456 and e['successful_build_exit_code'] == 0
 assert e['all_58_prototype_canonical_printed_types_equal'] and e['additional_examples_passed']
 assert len(e['checked_declarations']) == 58 and len(e['additional_examples']) == 20
 log = (ROOT / e['independent_trace_log']).read_text()
 assert not re.search(r'error:|sorryAx', log)
 traces = {}
 for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", log):
  traces[m[1]] = {x.strip() for x in (m[2] or '').split(',') if x.strip()}
 assert len(traces) == 78 and all(s <= STANDARD for s in traces.values())
 for field in ['declaration_axioms', 'additional_example_axioms']:
  for decl, axioms in e[field].items(): assert traces[decl] == set(axioms), decl
 assert set(e['checked_declarations']) | set(e['additional_examples']) == set(traces)

mapping = {r['id']: r for r in read(W / 'lean/lean-declarations.json')['declarations']}
for key, (decl, module, filename) in CLAIMS.items():
 row = mapping[key]; review = read(W / 'reviews' / filename); a = actual[decl]
 assert row['declaration'] == decl and row['module'] == module
 assert review['id'] == key and review['declaration'] == decl and review['module'] == module
 assert review['statement_sha256'] == audit['statement_hashes'][key]
 semantic = hashlib.sha256(json.dumps(a['semantic_dependencies'], sort_keys=True, separators=(',', ':')).encode()).hexdigest()
 assert semantic == review['statement_sha256'] and a['module'] == module
 assert row['source'] == review['source']; checkhash(ROOT / row['source'], review['source_sha256'])
 if row['status'] == 'accepted':
  assert row['statement_sha256'] == semantic and row['reviewer'] == review['reviewer']
  assert row['author'] != row['reviewer'] and row['parameters_reviewed'] and row['definition_equivalence_reviewed']
  assert row['review_file'] == 'reviews/' + filename
 else: assert row['status'] == 'review'
print(json.dumps({'passed': True, 'receipt': str(receipt_path.relative_to(ROOT)),
 'canonical_SM_modules': 294, 'prior288_unchanged': True, 'prior34_semantics_unchanged': True,
 'reviewed_source_rows': list(CLAIMS), 'accepted_new_rows': sum(mapping[x]['status']=='accepted' for x in CLAIMS),
 'independent_implementation_checks':58,'independent_consumers':20,'stage_complete':False}, indent=2))
