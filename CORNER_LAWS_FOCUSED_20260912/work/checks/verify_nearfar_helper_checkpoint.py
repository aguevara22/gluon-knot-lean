#!/usr/bin/env python3
"""Check the exact helper port and independent partial-source review bindings.
No original source proof or full farout/stage acceptance is added here.
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
 'nearfar-helper-port.json': '827cd20235e2e5c6c5b0faa8cc48fd20d21d9289d90ae25020ac4615e442f1e3',
 'composition-cut-set-canonical-partial.json': '37bd41b7708dce3be1dfaf5fd3a0cf4b84b382f7495627eef7acdb6352021121',
 'geometric-nearfar-canonical-partial.json': '1edcd67a154123178a58fea086cbe1870249a9d8ec851f51c1de6be2320e07e5',
 'nearfar-refinement-canonical-partial.json': '93537539849574269dd1609dcb76e125a9e56002498a04d29db1bd96edd2549f',
}

def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def checkhash(p, h): assert p.is_file() and sha(p) == h, str(p)
def bindings(d):
 if isinstance(d, dict):
  for k, v in d.items():
   if k.endswith('_sha256') and isinstance(v, str) and isinstance(d.get(k[:-7]), str):
    checkhash(ROOT / d[k[:-7]], v)
   if (k.endswith('_sha256') or k.endswith('_binding')) and isinstance(v, dict):
    for f, h in v.items():
     if isinstance(h, str) and len(h) == 64:
      p = C / (f + '.prototype.lean') if k == 'prototype_files_sha256' and '/' not in f else ROOT / f
      checkhash(p, h)
   bindings(v)
 elif isinstance(d, list):
  for v in d: bindings(v)

p = Path(sys.argv[1])
if not p.is_absolute(): p = ROOT / p
r = read(p)
assert r['passed'] and not r['stage_accepted']
assert r['mapped_declarations'] == 38 and r['audited_declarations'] == 3965
for f, h in r['project_sha256'].items(): checkhash(W / 'lean' / f, h)
for f, h in r['bundle_sha256'].items(): checkhash(ROOT / f, h)
audit = read(C / 'declaration-audit.json')
old = read(C / 'checkpoint-065-declaration-audit.json')
assert len(old['statement_hashes']) == 38 and audit['statement_hashes'] == old['statement_hashes']
assert all(set(d['axioms']) <= STANDARD for d in audit['audit']['declarations'])
prep = read(C / 'nearfar-helper-port-preparation.json')
assert len(prep['prior_SM_files_sha256']) == 299
assert len(list((W / 'lean/SM').glob('*.lean'))) == 307
for f, h in prep['prior_SM_files_sha256'].items(): checkhash(W / 'lean' / f, h)
checkhash(W / 'lean/lean-declarations.json', prep['prior_map_sha256'])
assert len(prep['new_modules']) == 8
for f, d in prep['new_modules'].items():
 checkhash(ROOT / f, d['candidate_sha256'])
 assert (ROOT / f).read_bytes() == (ROOT / d['candidate']).read_bytes()
 for frag in d['source_fragments']: checkhash(ROOT / frag['source'], frag['source_sha256'])

for name, h in REVIEW_HASHES.items():
 q = W / 'reviews' / name; checkhash(q, h); review = read(q)
 assert review['verdict'] == 'faithful' and review['reason']
 assert review['reviewer'] != review['implementer']
 assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
 assert review['source_claim_accepted'] is False
 bindings(review)
 e = review['evidence']
 assert e['independent_kernel_session'] == 5667 and e['independent_kernel_exit_code'] == 0
 assert e['successful_build_session'] == 85206 and e['successful_build_exit_code'] == 0
 assert e['all_62_prototype_canonical_printed_types_equal'] and e['additional_examples_passed']
 assert len(e['checked_declarations']) == 62 and len(e['additional_examples']) == 22
 log = (ROOT / e['independent_trace_log']).read_text()
 assert not re.search(r'error:|sorryAx', log)
 traces = {}
 for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", log):
  traces[m[1]] = {x.strip() for x in (m[2] or '').split(',') if x.strip()}
 assert len(traces) == 84 and all(a <= STANDARD for a in traces.values())
 assert set(e['checked_declarations']) | set(e['additional_examples']) == set(traces)
 for field in ['declaration_axioms', 'additional_example_axioms']:
  for decl, axioms in e[field].items(): assert traces[decl] == set(axioms), decl

mapping = {x['id']: x for x in read(W / 'lean/lean-declarations.json')['declarations']}
assert mapping['def:nearfar']['status'] == 'accepted'
assert mapping['lem:farout']['status'] == 'pending' and not mapping['lem:farout']['declaration']
print(json.dumps({'passed': True, 'receipt': str(p.relative_to(ROOT)),
 'canonical_SM_modules': 307, 'prior299_unchanged': True, 'all38_semantics_unchanged': True,
 'map_unchanged': True, 'independent_declarations': 62, 'independent_consumers': 22,
 'new_original_acceptance': 0, 'full_farout_accepted': False, 'stage_complete': False}, indent=2))
