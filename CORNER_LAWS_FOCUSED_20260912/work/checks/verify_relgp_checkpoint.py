#!/usr/bin/env python3
"""Verify source-review and integration evidence for full thm:relgp.

The independent reviewer supplies semantic judgment. This check establishes
that the current canonical code, exact ports, kernel and review are those files.
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


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace_check(review):
    e = review['evidence']
    assert e['independent_kernel_exit_code'] == 0
    for key in ['independent_trace_source', 'independent_trace_log',
                'independent_closure_evidence']:
        assert sha(ROOT / e[key]) == e[key + '_sha256'], key
    if 'independent_examples_source' in e:
        assert sha(ROOT / e['independent_examples_source']) == e['independent_examples_source_sha256']
    else:
        # The canonical check embeds the seven examples in its bound trace source.
        assert e['same_seven_examples_as_full_prototype'] is True
        assert e['additional_example_axioms'] == proto['evidence']['additional_example_axioms']
    trace = (ROOT / e['independent_trace_log']).read_text()
    assert not re.search(r'error[:(]', trace) and 'sorryAx' not in trace
    parsed = {m.group(1): {s.strip() for s in m.group(2).split(',') if s.strip()}
              for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", trace)}
    parsed.update({name: set() for name in
                   re.findall(r"'([^']+)' does not depend on any axioms", trace)})
    assert set(e['checked_declarations']) == set(e['declaration_axioms'])
    for name, axioms in (e['declaration_axioms'] | e['additional_example_axioms']).items():
        assert parsed[name] == set(axioms), name
        assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, name
    assert e['additional_examples_passed']
    assert len(e['additional_examples']) == e['additional_example_count'] == 7


proto_path = WORK / 'reviews/relative-general-position-prototype.json'
proto = json.loads(proto_path.read_text())
assert proto['verdict'] == 'faithful' and proto['source_claim_accepted'] is False
assert proto['reviewer'] != proto['implementer']
assert proto['parameters_reviewed'] and proto['definition_equivalence_reviewed']
assert sha(ROOT / proto['source']) == proto['source_sha256']
for key in ['reviewed_files_sha256', 'external_inputs_sha256', 'inherited_review_binding']:
    assert matches(ROOT, proto[key]), key
assert matches(ROOT, proto['pins']['pin_files_sha256'])
for key in ['prototype_file', 'prototype_body', 'kinds_body']:
    hash_key = 'prototype_sha256' if key == 'prototype_file' else key + '_sha256'
    assert sha(ROOT / proto[key]) == proto[hash_key]
trace_check(proto)
assert len(proto['evidence']['checked_declarations']) == 14

rp = Path(sys.argv[1]).resolve()
r = json.loads(rp.read_text())
assert r['passed'] and r['stage_accepted'] is False
assert r['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert matches(ROOT, r['bundle_sha256'])
assert (WORK / 'checks/stage-development.json').read_bytes() == rp.read_bytes()
old = json.loads((WORK / 'checks/checkpoint-057-output.json').read_text())
assert r['bundle_sha256'] == old['bundle_sha256']
prior = {p: h for p, h in old['project_sha256'].items() if p.startswith('SM/')}
assert len(prior) == 279 and matches(LEAN, prior)
candidate = json.loads((WORK / 'checks/relgp-port-candidate-files.json').read_text())
assert len(candidate['prior_SM_files_sha256']) == 280
assert matches(LEAN, candidate['prior_SM_files_sha256'])
assert len(candidate['new_modules']) == 5
for path, b in candidate['new_modules'].items():
    assert sha(ROOT / path) == b['sha256'] == b['candidate_sha256']
    assert sha(ROOT / b['source']) == b['source_sha256']
    assert sha(ROOT / b['candidate']) == b['candidate_sha256']
    source = (ROOT / b['source']).read_text().split('#print axioms', 1)[0]
    body = source[source.index('namespace SM'):].strip() + '\n'
    port = (ROOT / path).read_text()
    assert body == port[port.index('namespace SM'):]
    assert hashlib.sha256(body.encode()).hexdigest() == b['body_sha256']
assert sha(LEAN / 'Supplemental.lean') == candidate['new_Supplemental_sha256']
expected = set(candidate['prior_SM_files_sha256']) | {
    str(Path(p).relative_to('work/lean')) for p in candidate['new_modules']}
assert {p for p in r['project_sha256'] if p.startswith('SM/')} == expected

ap = WORK / 'checks/declaration-audit.json'
a = json.loads(ap.read_text())
assert a['audit']['checked'] == r['audited_declarations']
assert len(a['audit']['declarations']) == r['mapped_declarations'] == 31
assert all(set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for row in a['audit']['declarations'])
main = next(row for row in a['audit']['declarations']
            if row['declaration'] == 'SM.relative_general_position')
assert main['kind'] == 'theorem' and main['module'] == 'SM.RelativeGeneralPosition'
semantic = hashlib.sha256(json.dumps(main['semantic_dependencies'], sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()
assert semantic == a['statement_hashes']['thm:relgp']
assert semantic == 'ea9976b281dfda84381a7c7e0fbf0a258dd7e7b5a8d8d03cb86db9639e8100ec'
rows = json.loads((LEAN / 'lean-declarations.json').read_text())['declarations']
row = next(row for row in rows if row['id'] == 'thm:relgp')
review_hash = None
if row['status'] == 'accepted':
    p = WORK / row['review_file']
    review = json.loads(p.read_text())
    assert review['id'] == 'thm:relgp' and review['verdict'] == 'faithful'
    assert review['statement_sha256'] == row['statement_sha256'] == semantic
    assert review['reviewer'] == row['reviewer'] != row['author']
    assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
    assert matches(ROOT, review['reviewed_files_sha256'])
    assert len(review['reviewed_files_sha256']) == 129
    trace_check(review)
    review_hash = sha(p)
else:
    assert row['status'] == 'review'
progress = snapshot()
assert not progress['evidence_issues']
assert progress['proved_original_claims'] == (15 if row['status'] == 'accepted' else 14)
out = {'passed': True, 'stage_accepted': False, 'receipt_sha256': sha(rp),
       'audit_sha256': sha(ap), 'source_claim_accepted': row['status'] == 'accepted',
       'canonical_SM_modules': len(expected), 'previous_SM_modules_unchanged': 280,
       'exact_five_port_bodies': True, 'audited_declarations': r['audited_declarations'],
       'full_prototype_review_sha256': sha(proto_path), 'canonical_review_sha256': review_hash,
       'statement_sha256': semantic, 'progress': progress}
rp.with_name(rp.name.replace('-output.json', '-relgp-verification.json')).write_text(
    json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
