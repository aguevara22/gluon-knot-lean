from pathlib import Path
from hashlib import sha256
import json, re, datetime

base = Path(__file__).resolve().parents[2]
def load(p): return json.loads((base / p).read_text())
def sha(p): return sha256((base / p).read_bytes()).hexdigest()
def write(p, d): (base / p).write_text(json.dumps(d, indent=2) + '\n')
def digest(d): return sha256(json.dumps(d, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

prep = load('work/checks/root-gates-canonical-review-preparation.json')
manifest = load('work/checks/root-gates-port-preparation.json')
result = load('work/checks/root-gates-port-audit-result.json')
receipt = load('work/checks/checkpoint-060-output.json')
audit = load('work/checks/checkpoint-060-declaration-audit.json')
assert result['session'] == 88785 and result['exit_code'] == 0
assert receipt['passed'] and not receipt['stage_accepted']
for k in ['receipt', 'audit', 'log']:
    assert sha(result[k]) == result[k + '_sha256']
assert all(sha('work/lean/' + p) == h for p, h in receipt['project_sha256'].items())
assert all(sha(p) == h for p, h in receipt['bundle_sha256'].items())
assert all(sha('work/lean/' + p) == h for p, h in manifest['prior_SM_files_sha256'].items())
ports = {}
for dest, d in manifest['new_modules'].items():
    assert (base / dest).read_bytes() == (base / d['candidate']).read_bytes()
    assert sha(dest) == d['candidate_sha256']
    bodies = []
    for f in d['source_fragments']:
        assert sha(f['source']) == f['source_sha256']
        s = (base / f['source']).read_text()
        b = s[s.index('namespace SM'):]
        if '#print axioms' in b: b = b.split('#print axioms')[0].rstrip() + '\n'
        assert sha256(b.encode()).hexdigest() == f['body_sha256']
        bodies.append(b)
    s = (base / dest).read_text()
    assert s[s.index('namespace SM'):] == '\n'.join(bodies)
    ports[dest] = dict(prep['ports'][dest], installed_module_sha256=sha(dest), installed_equals_candidate=True)
current = {str(p.relative_to(base)): sha(str(p.relative_to(base))) for p in sorted((base / 'work/lean/SM').glob('*.lean'))}
assert len(current) == 288
assert set(current) == {'work/lean/' + p for p in manifest['prior_SM_files_sha256']} | set(ports)
sup = (base / 'work/lean/Supplemental.lean').read_bytes()
delta = b'\nimport SM.Gates\nimport SM.FiniteCompositions\n'
assert sup.endswith(delta)
assert sha256(sup[:-len(delta)]).hexdigest() == manifest['prior_Supplemental_sha256']

def closure(roots):
    seen = {}
    def visit(m):
        if m in seen: return
        p = 'work/lean/' + m.replace('.', '/') + '.lean'
        seen[m] = p
        for q in re.findall(r'^import (\S+)', (base / p).read_text(), re.M):
            if q.startswith('SM.'): visit(q)
    for m in roots: visit(m)
    return {seen[m]: sha(seen[m]) for m in sorted(seen)}

union = closure(['SM.Gates', 'SM.FiniteCompositions'])
assert set(union) == {'work/lean/SM/' + n + '.lean' for n in ['Generic', 'Polygon', 'Chirotope', 'RootBoundary', 'FiniteCompositions', 'Gates']}
logfile = 'work/checks/root-gates-canonical-review-types.log'
tracefile = 'work/checks/root-gates-canonical-review-types.lean'
assert sha(tracefile) == prep['canonical_trace_sha256']
log = (base / logfile).read_text()
assert not re.search(r'error[:(]', log)
names, examples = prep['checked_declarations'], prep['examples']
assert len(names) == 46 and len(examples) == 22
axioms, types = {}, {}
for n in names + examples:
    m = re.search("'" + re.escape(n) + r"' depends on axioms:\s*\[([^]]*)\]", log)
    if m: axioms[n] = [s.strip() for s in m[1].split(',') if s.strip()]
    else:
        assert "'" + n + "' does not depend on any axioms" in log, n
        axioms[n] = []
    assert set(axioms[n]) <= {'propext', 'Classical.choice', 'Quot.sound'}
for n in names:
    i = log.index(n + ' '); j = log.index("'" + n + "'", i)
    types[n] = log[i:j].strip()
oldnames = set()
for f in ['root-boundary-reviewed-types.json', 'gates-complete-reviewed-types.json']:
    for n, t in load('work/checks/' + f)['types'].items():
        assert types[n] == t, n
        oldnames.add(n)
assert oldnames == set(names)

rows = [
    ('def:root', 'SM.rootData', 'SM.RootBoundary', 'root-boundary-prototype', 'def-root', 10, '10-27'),
    ('def:gates', 'SM.gatesData', 'SM.Gates', 'gates-prototype', 'def-gates', 29, '29-44'),
    ('lem:gates-nonzero', 'SM.gates_nonzero', 'SM.Gates', 'gates-prototype', 'lem-gates-nonzero', 46, '46-62'),
]
required = {
 'def:root': ['SM.rootData', 'SM.LabelledTuple', 'SM.Plane', 'SM.edge', 'SM.boundaryWord', 'SM.boundaryIndex', 'SM.BoundaryInterval', 'SM.BoundaryInterval.mk', 'SM.BoundaryInterval.leaves', 'SM.IntervalComposition', 'SM.IntervalComposition.mk', 'SM.IntervalComposition.cut', 'SM.IntervalComposition.parts', 'SM.IntervalComposition.part'],
 'def:gates': ['SM.gatesData', 'SM.G1', 'SM.chi', 'SM.det', 'SM.signTheta', 'SM.ordinaryGate', 'SM.rootGate', 'SM.boundaryIndex', 'SM.BoundaryInterval', 'SM.BoundaryInterval.mk', 'SM.IntervalComposition', 'SM.IntervalComposition.mk', 'SM.IntervalComposition.nearSign', 'SM.IntervalComposition.farSign', 'SM.IntervalComposition.ordinaryWeight', 'SM.IntervalComposition.rootWeight'],
 'lem:gates-nonzero': ['SM.gates_nonzero', 'SM.G1', 'SM.chi', 'SM.det', 'SM.signTheta', 'SM.ordinaryGate', 'SM.rootGate', 'SM.boundaryIndex', 'SM.BoundaryInterval', 'SM.BoundaryInterval.mk', 'SM.IntervalComposition', 'SM.IntervalComposition.mk', 'SM.IntervalComposition.nearSign', 'SM.IntervalComposition.farSign', 'SM.IntervalComposition.ordinaryWeight'],
}
semantics = {}
for ident, decl, module, prototype, filename, line, lines in rows:
    target = next(d for d in audit['audit']['declarations'] if d['declaration'] == decl)
    assert target['module'] == module
    assert target['kind'] == ('theorem' if ident.startswith('lem:') else 'definition')
    sh = digest(target['semantic_dependencies'])
    assert sh == audit['statement_hashes'][ident] == result['new_statement_hashes'][ident]
    semnames = {d['declaration'] for d in target['semantic_dependencies']}
    assert set(required[ident]) <= semnames
    semantics[ident] = {'declaration': decl, 'module': module, 'statement_sha256': sh,
        'semantic_dependency_count': len(semnames), 'semantic_declarations': sorted(semnames),
        'required_transparent_definitions_and_constructors': required[ident],
        'semantic_dependency_record_sha256': {d['declaration']: digest(d) for d in target['semantic_dependencies']}}
    p = load('work/reviews/' + prototype + '.json')
    assert sha(p['source']) == p['source_sha256']
    assert all(sha(f) == h for f, h in p['additional_source_sha256'].items())

closefile = 'work/checks/root-gates-canonical-review-closure.json'
write(closefile, {'port_preparation': 'work/checks/root-gates-port-preparation.json', 'port_preparation_sha256': sha('work/checks/root-gates-port-preparation.json'),
    'port_installation': 'work/checks/root-gates-port-installed.json', 'port_installation_sha256': sha('work/checks/root-gates-port-installed.json'),
    'ports': ports, 'prior_SM_count': 285, 'all_285_prior_SM_unchanged': True,
    'canonical_SM_count': 288, 'canonical_SM_files_sha256': current,
    'SM_import_roots': ['SM.Gates', 'SM.FiniteCompositions'], 'SM_closure_count': len(union), 'SM_closure_files_sha256': union,
    'sole_Supplemental_append': delta.decode(), 'Supplemental_sha256': sha('work/lean/Supplemental.lean'),
    'checked_declarations': names, 'consumer_examples': examples, 'canonical_trace_sha256': sha(tracefile)})
semfile = 'work/checks/root-gates-canonical-semantic-review.json'
write(semfile, {'targets': semantics, 'canonical_printed_types': types,
    'canonical_printed_type_sha256': {n: sha256(t.encode()).hexdigest() for n, t in types.items()},
    'all_46_prototype_canonical_printed_types_equal': True,
    'axioms': axioms, 'canonical_semantic_hashes_independently_recomputed': True})
evidence = {'independent_trace_source': tracefile, 'independent_trace_source_sha256': sha(tracefile),
    'independent_trace_log': logfile, 'independent_trace_log_sha256': sha(logfile),
    'independent_kernel_command': 'lake env lean ../checks/root-gates-canonical-review-types.lean',
    'independent_kernel_session': 89726, 'independent_kernel_exit_code': 0, 'first_independent_run_passed': True,
    'checked_declarations': names, 'declaration_axioms': {n: axioms[n] for n in names},
    'additional_examples': examples, 'additional_example_count': 22, 'additional_examples_passed': True,
    'additional_example_axioms': {n: axioms[n] for n in examples},
    'all_46_prototype_canonical_printed_types_equal': True,
    'transparent_predicates_printed': prep['transparent_predicates_printed'],
    'independent_closure_evidence': closefile, 'independent_closure_evidence_sha256': sha(closefile),
    'canonical_semantic_evidence': semfile, 'canonical_semantic_evidence_sha256': sha(semfile),
    'root_result_file': 'work/checks/root-gates-port-audit-result.json', 'root_result_sha256': sha('work/checks/root-gates-port-audit-result.json'),
    'successful_build_session': 88785, 'successful_build_exit_code': 0,
    'successful_build_log': result['log'], 'successful_build_log_sha256': sha(result['log']),
    'audit_receipt': result['receipt'], 'audit_receipt_sha256': sha(result['receipt']),
    'declaration_audit': result['audit'], 'declaration_audit_sha256': sha(result['audit']),
    'scope_note': 'The independently rerun consumer checks include raw-composition coverage, complete enumeration, actual child-size well-foundedness, all labels and physical root endpoints, G1-only signs, real half and product identities, empty/binary cases and exact representative descent.'}
binding = {f: sha(f) for f in [
    'work/reviews/root-boundary-prototype.json', 'work/reviews/finite-compositions-prototype.json', 'work/reviews/gates-prototype.json',
    'work/checks/root-boundary-review-examples.lean', 'work/checks/finite-and-gates-review-examples.lean', 'work/checks/gates-equivariance-review-examples.lean',
    'work/checks/root-boundary-reviewed-types.json', 'work/checks/gates-complete-reviewed-types.json']}
portfile = 'work/reviews/root-gates-port.json'
write(portfile, {'review_schema': 'independent-full-source-port-review-v1', 'id': 'root-gates-port',
    'source_ids': [r[0] for r in rows], 'reviewer': 'review_relgp_full-independent-20260911', 'implementer': 'root-implementation-20260910',
    'verdict': 'faithful', 'parameters_reviewed': True, 'definition_equivalence_reviewed': True, 'in_theorem_library': True,
    'source_claim_accepted': False, 'statement_hashes': {k: d['statement_sha256'] for k, d in semantics.items()},
    'reason': 'The installed RootBoundary body is exactly its frozen prototype namespace body; FiniteCompositions is exactly its frozen body; Gates is exactly the concatenation of its frozen Gates and GatesEquivariance bodies with one intervening newline. Import headers alone replace embedded predecessor bodies. All 285 previous SM modules remain byte-for-byte unchanged and Supplemental adds only the two expected imports. The canonical-only trace independently checks 46 declarations and reruns 22 substantive representation and mathematical consumer theorems. Every printed implementation type equals its separately reviewed prototype type, and all 68 axiom traces are standard only. The source was reread against the installed bodies, including every raw composition, actual orientation and root transport, and the immutable audit060 semantic closures were independently hashed and checked for the real transparent definitions and constructors. This report certifies the exact ports; the three separate source reviews contain their full-source acceptance verdicts.',
    'ports': ports, 'main_declarations': names, 'reviewed_files_sha256': union, 'import_closure_roots': ['SM.Gates', 'SM.FiniteCompositions'],
    'import_closure_file_count': 6, 'prior285_unchanged': True, 'current_SM_count': 288,
    'prototype_review_binding': binding, 'evidence': evidence,
    'not_certified': ['No source row is changed by this report.', 'The finite composition helper is not a separate accepted original claim.', 'No tree-sum equivalence, wall law, soft theorem, R theorem or overall stage completion is certified.']})

reasons = {
 'def:root': 'Faithful complete representative-based implementation of source def:root. The actual cyclic edge occurrence and physical endpoints, exact boundary word and all nonroot leaves, ordered interval domain, arbitrary-natural-part-count strictly increasing compositions and their exact constituent parts match the source. The explicitly permitted representative reading has the required simultaneous root/tuple shift laws. Raw natural cut-sequence admission and full-domain finite enumeration were independently rechecked; no arity bound is assumed and the one-part composition remains present. G2 is absent. The complete installed definition and its constructor fields are bound by the canonical semantic closure.',
 'def:gates': 'Faithful complete implementation of source def:gates. At every actual interior cut, near and far signs have the exact source boundary indices and orientation. Both products use the actual nonzero SignType restriction of the step function and the correct ordinary/root sign, and all one-part products equal one. G1 alone proves every required nonzero argument. Independent real-step and real-product checks establish the exact source scalar interpretation. The canonical gatesData_shift and independent representative-descent consumers prove that the whole data function descends under the exact simultaneous shift, including arbitrary G1 proof witnesses.',
 'lem:gates-nonzero': 'Faithful complete implementation of source lem:gates-nonzero. The canonical theorem quantifies over every actual interval composition under G1 and proves both signs and both step arguments are plus or minus one at every interior cut, both scalar half identities for every nonzero sign pair, and the actual ordinary weight zero for every two-part composition. Strict actual cuts and boundary-index injectivity supply distinct occurrence labels; no G2 premise is used. Independent real-field checks of both scalar identities and arbitrary finite weight products rule out an integer-division rounding reinterpretation. The binary proof uses exact first/last cuts to identify the one near and far sign.',
}
for ident, decl, module, prototype, filename, line, lines in rows:
    protofile = 'work/reviews/' + prototype + '.json'; p = load(protofile)
    c = closure([module]); expected_count = 4 if ident == 'def:root' else 5
    assert len(c) == expected_count
    math = p['mathematical_justification'][:-1]
    if ident == 'def:root':
        math = [dict(x) for x in math]
        math[-1]['assessment'] = math[-1]['assessment'].replace('These finite-domain/coverage theorems are independent representation checks outside the canonical library; no Fintype enumeration implementation or tree-sum theorem is claimed.', 'The independent representation checks remain outside the theorem library. The separately authored, independently reviewed and now canonical FiniteCompositions module additionally implements finiteCode injection and actual Finite/Fintype instances for this unchanged raw type. The canonical consumer trace checks every raw composition belongs to its univ, strict child-size decrease for at least two parts, the induced well-founded child relation, and the necessary equality for the one-part case. No tree-sum theorem is claimed.')
    math += [{'clause': 'Canonical aggregate and complete transparent closure', 'assessment': reasons[ident]},
        {'clause': 'Exact port and independent kernel verification', 'assessment': 'The current installed modules were read against the authoritative source and compared byte-for-byte to the separately reviewed frozen implementation bodies. All 46 canonical printed implementation types exactly match their previous independent prototype traces. Kernel89726 independently rechecks the 46 declarations and 22 substantive consumer theorems from canonical imports only, without embedding any implementation body. It passes on its first run with only propext, Classical.choice and Quot.sound where needed. The successful immutable whole-project audit060 provides the current canonical definition/proposition and transparent constructor/type/body dependency records; their semantic hash is independently recomputed. Ambient n>=3 supplies NeZero, or an existing interval endpoint supplies it in the independent domain tests; no additional mathematical premise or axiom is introduced.'}]
    review = {k: p[k] for k in ['reviewer', 'implementer', 'source', 'source_sha256', 'additional_source_sha256', 'parameters_reviewed', 'definition_equivalence_reviewed', 'pins']}
    review.update({'review_schema': 'independent-full-source-review-v1', 'id': ident, 'source_id': ident, 'labels': [ident],
        'source_line': line, 'source_lines': lines + '; section G1-only domain lines 3-6; representative permission sm-1-polygons.tex lines 55-60',
        'declaration': decl, 'module': module, 'verdict': 'faithful', 'source_claim_accepted': True,
        'statement_sha256': semantics[ident]['statement_sha256'], 'in_theorem_library': True,
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'reason': reasons[ident] + ' Canonical kernel89726 passes all 46 declaration checks and 22 substantive consumers, all canonical printed types match their reviewed prototypes, and immutable whole-project audit060 passes. This exact source row is therefore eligible for map acceptance.',
        'mathematical_justification': math,
        'independence': p['independence'] + ' For this canonical review the reviewer only wrote new review/check evidence. No implementation, source, map or previous evidence was edited. The canonical source bodies were reread and the independent consumer checks were rerun using canonical imports. Finite encoding strategy overlap with a prior reviewer representation test is disclosed in the separate finite-compositions-prototype report; implementation authorship remained with root.',
        'reviewed_files_sha256': c, 'import_closure_roots': [module], 'import_closure_file_count': len(c),
        'semantic_dependency_count': semantics[ident]['semantic_dependency_count'], 'required_semantic_definitions_checked': required[ident],
        'prototype_review': protofile, 'prototype_review_sha256': sha(protofile),
        'prototype_review_binding': binding, 'port_review': portfile, 'port_review_sha256': sha(portfile), 'evidence': evidence,
        'audit_context': {'receipt': result['receipt'], 'receipt_sha256': sha(result['receipt']), 'root_audit_session': 88785,
            'root_audit_exit_code': 0, 'passed': True, 'stage_accepted': False, 'audited_local_declarations': 3578,
            'mapped_claims': 34, 'audited_SM_modules': 288, 'all_receipt_project_and_bundle_hashes_checked_at_review': True,
            'scope': 'Immutable audit060 is the actual post-port development audit. The earlier unchanged-project pre-port audit56858 is not used as evidence for these installed modules. This review does not claim the later accepted-map audit has already passed.'},
        'acceptance_scope': {'original_claim': ident, 'original_rows_added_if_mapped_accepted': 1,
            'proofs_added_if_mapped_accepted': 1 if ident.startswith('lem:') else 0,
            'definitions_added_if_mapped_accepted': 0 if ident.startswith('lem:') else 1,
            'current_map_was_not_edited_by_reviewer': True, 'helper_original_claim_count': 0, 'stage_complete': False},
        'not_certified': ['No tree coefficient or plane-tree-sum equivalence is accepted by this source row.', 'No state-sum wall law, soft theorem, unconditional R theorem or overall handoff completion is certified.']})
    write('work/reviews/' + filename + '.json', review)
    print(ident, 'faithful;', 'semantic', semantics[ident]['statement_sha256'], 'review', sha('work/reviews/' + filename + '.json'))
print('port review', sha(portfile), '; 46 exact types, 22 consumers, 3 complete source rows; no map edits')
