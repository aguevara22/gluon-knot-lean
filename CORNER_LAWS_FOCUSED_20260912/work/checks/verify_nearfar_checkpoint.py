#!/usr/bin/env python3
"""Bind current near-far acceptance to immutable independent source/type review.
This checks evidence consistency; it never accepts full farout or the stage.
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
REVIEW_HASHES = {
 'def-nearfar.json': '933022e776a0440ac35e0f9fbfa193c9e3fc32d6e8c0f67e3560c61361dd314a',
 'nearfar-port.json': '79826e24ca37666ba9af32f59fedfbae069eec6eb93d44d8b1dd792852696bff',
 'triangular-polynomial-inverse-canonical-partial.json': 'bf3e5d8fbcea2b3b9bc1d2a2257dbf20eba813efb9f7d47f140905fecfeb8a4e',
}

def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def checkhash(p, h): assert p.is_file() and sha(p) == h, str(p)
def bindings(d):
 if isinstance(d, dict):
  for k, v in d.items():
   if k.endswith('_sha256') and isinstance(v, str) and isinstance(d.get(k[:-7]), str):
    checkhash(ROOT / d[k[:-7]], v)
   if k.endswith('_sha256') and isinstance(v, dict):
    for f, h in v.items():
     if isinstance(h, str) and len(h) == 64: checkhash(ROOT / f, h)
   bindings(v)
 elif isinstance(d, list):
  for x in d: bindings(x)

p = Path(sys.argv[1])
if not p.is_absolute(): p = ROOT / p
r = read(p)
assert r['passed'] and not r['stage_accepted']
assert r['mapped_declarations'] == 38 and r['audited_declarations'] == 3804
for f, h in r['project_sha256'].items(): checkhash(W / 'lean' / f, h)
for f, h in r['bundle_sha256'].items(): checkhash(ROOT / f, h)
audit = read(C / 'declaration-audit.json')
old = read(C / 'checkpoint-063-declaration-audit.json')
assert len(old['statement_hashes']) == 37
for k, h in old['statement_hashes'].items(): assert audit['statement_hashes'][k] == h, k
actual = {d['declaration']: d for d in audit['audit']['declarations']}
assert all(set(d['axioms']) <= STANDARD for d in actual.values())
prep = read(C / 'nearfar-port-preparation.json')
assert len(prep['prior_SM_files_sha256']) == 294
assert len(list((W / 'lean/SM').glob('*.lean'))) == 299
for f, h in prep['prior_SM_files_sha256'].items(): checkhash(W / 'lean' / f, h)
assert len(prep['new_modules']) == 5
for f, d in prep['new_modules'].items():
 checkhash(ROOT / f, d['candidate_sha256'])
 assert (ROOT / f).read_bytes() == (ROOT / d['candidate']).read_bytes()
 for x in d['source_fragments']: checkhash(ROOT / x['source'], x['source_sha256'])

for name, h in REVIEW_HASHES.items():
 path = W / 'reviews' / name; checkhash(path, h); review = read(path)
 assert review['verdict'] == 'faithful' and review['reason']
 assert review['reviewer'] != review['implementer']
 assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
 bindings(review)
 e = review['evidence']
 assert e['independent_kernel_session'] == 21424 and e['independent_kernel_exit_code'] == 0
 assert e['successful_build_session'] == 90989 and e['successful_build_exit_code'] == 0
 assert e['all_37_prototype_canonical_printed_types_equal'] and e['additional_examples_passed']
 assert len(e['checked_declarations']) == 37 and len(e['additional_examples']) == 11
 log = (ROOT / e['independent_trace_log']).read_text()
 assert not re.search(r'error:|sorryAx', log)
 traces = {}
 for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", log):
  traces[m[1]] = {x.strip() for x in (m[2] or '').split(',') if x.strip()}
 assert len(traces) == 48 and all(a <= STANDARD for a in traces.values())
 assert set(e['checked_declarations']) | set(e['additional_examples']) == set(traces)
 for field in ['declaration_axioms', 'additional_example_axioms']:
  for decl, axioms in e[field].items(): assert traces[decl] == set(axioms), decl

mapping = {x['id']: x for x in read(W / 'lean/lean-declarations.json')['declarations']}
before = {x['id']: x for x in read(C / 'lean-declarations-before-nearfar.json')['declarations']}
assert mapping.keys() == before.keys()
for k, x in before.items():
 if k != 'def:nearfar': assert mapping[k] == x, k
row = mapping['def:nearfar']; review = read(W / 'reviews/def-nearfar.json')
assert row['declaration'] == review['declaration'] == 'SM.nearfarData'
assert row['module'] == review['module'] == 'SM.NearFar'
assert row['source'] == review['source'] and row['line'] == review['source_line'] == 132
assert row['labels'] == review['labels'] == ['def:nearfar']
a = actual['SM.nearfarData']
h = hashlib.sha256(json.dumps(a['semantic_dependencies'], sort_keys=True, separators=(',', ':')).encode()).hexdigest()
assert h == audit['statement_hashes']['def:nearfar'] == review['statement_sha256']
assert len(a['semantic_dependencies']) == review['semantic_dependency_count'] == 41
checkhash(ROOT / row['source'], review['source_sha256'])
if row['status'] == 'accepted':
 assert row['statement_sha256'] == h and row['reviewer'] == review['reviewer']
 assert row['author'] != row['reviewer'] and row['parameters_reviewed'] and row['definition_equivalence_reviewed']
 assert row['review_file'] == 'reviews/def-nearfar.json'
else: assert row['status'] == 'review'
assert mapping['lem:farout']['status'] == 'pending' and not mapping['lem:farout']['declaration']
print(json.dumps({'passed': True, 'receipt': str(p.relative_to(ROOT)),
 'canonical_SM_modules': 299, 'prior294_unchanged': True, 'prior37_semantics_unchanged': True,
 'accepted_new_definitions': int(row['status'] == 'accepted'), 'accepted_new_proofs': 0,
 'independent_declaration_checks': 37, 'independent_consumers': 11,
 'full_farout_accepted': False, 'stage_complete': False}, indent=2))
