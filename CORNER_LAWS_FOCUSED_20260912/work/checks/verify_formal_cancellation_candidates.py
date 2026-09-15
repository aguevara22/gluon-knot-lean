"""Verify recorded formal-cancellation candidate evidence; not source-fidelity acceptance."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / 'work/checks'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
GROUPS = {'InternalGapSigns': (7424, 'first', ['SM.det_line_base_translation', 'SM.affine_line_far_determinant', 'SM.affine_internal_gap_determinant', 'SM.affine_internal_gap_sign', 'SM.affine_internal_gap_zero_iff', 'SM.affine_internal_gap_sign_cast']), 'SelectedGapFarArray': (3596, 'second', ['SM.selectedOuterCutTriple', 'SM.selectedGapCutTriple', 'SM.selected_gap_epsilon_nonzero', 'SM.weak_selected_gap_far_sign', 'SM.weak_selected_gap_far_array', 'SM.weak_selected_gap_far_array_of_collinear']), 'SelectedCutRefinement': (32831, 'first', ['SM.IntervalComposition.refiningCompositionEquiv', 'SM.IntervalComposition.nestedRefiningCompositionEquiv', 'SM.IntervalComposition.nestedRefiningCompositionEquiv_val', 'SM.IntervalComposition.selectedComposition_interior', 'SM.IntervalComposition.selectedComposition_refines_iff', 'SM.IntervalComposition.prod_interior_positions', 'SM.IntervalComposition.prod_inner_positions', 'SM.IntervalComposition.positionCutSummand', 'SM.IntervalComposition.prod_refinement_gap_summands', 'SM.IntervalComposition.prod_nested_gap_summands', 'SM.IntervalComposition.sum_refining_cut_products', 'SM.IntervalComposition.sum_refining_selected_cut_products', 'SM.IntervalComposition.sum_refining_constant_selected_factor']), 'NearFarRingMaps': (39998, 'second', ['SM.ringHom_map_half', 'SM.map_nearFarWeight', 'SM.map_boundaryUnitArray', 'SM.map_nearFarTransform', 'SM.map_farTransform', 'SM.map_nearFarInverse', 'SM.map_farOnlyCoordinates', 'SM.map_farOnlyOutput']), 'SilentFarPolynomial': (59081, 'third', ['SM.SilentFarEntry', 'SM.silentFarArray', 'SM.silentFarVariable', 'SM.silentFarArray_eq_constant_add_variable', 'SM.silentFarArray_at_zero_entry', 'SM.silentFarArray_at_nonzero_entry', 'SM.silentFarZeroHom', 'SM.silentFarZeroHom_array', 'SM.constantFarCoordinates', 'SM.constantFarCoordinates_equation', 'SM.constantFarCoordinates_inverse', 'SM.silentFarCoordinates_zero_specialization', 'SM.silentFarOutput_zero_specialization', 'SM.silentPolynomialTwoInvertible']), 'PositionalCutDecomposition': (64127, 'second', ['SM.positional_cut_half_add', 'SM.IntervalComposition.nearFarWeight_position_add', 'SM.IntervalComposition.nearFarWeight_position_near', 'SM.IntervalComposition.nearFarWeight_position_far', 'SM.nearFarTransform_position_add', 'SM.nearTransform_position', 'SM.farTransform_position', 'SM.positionCutSum_add_decomposition']), 'SilentCompositionLine': (68161, 'second', ['SM.rational_geometric_far_zero_iff', 'SM.silent_composition_cuts_collinear', 'SM.silent_composition_positive_gap', 'SM.silent_composition_full_negative_gap']), 'TopFarDecomposition': (9281, 'first', ['SM.intervalFarValue', 'SM.intervalFarValue_interior', 'SM.intervalFarValue_map', 'SM.intervalFarCutWeight', 'SM.intervalFarCutWeight_add', 'SM.positionCutSummand_intervalFar', 'SM.farTransform_positionCutSum', 'SM.farTransform_add_decomposition']), 'TopFarCancellation': (49406, 'second', ['SM.topFar_single_summand', 'SM.farTransform_add_eq_of_nonunary_zero']), 'SilentGapTransform': (5830, 'first', ['SM.intervalFarValue_left_mul', 'SM.silent_gap_intervalFarValue', 'SM.silent_gap_intervalFarCutWeight', 'SM.silent_gap_positionCutSummand', 'SM.silent_gap_positionCutSum']), 'SilentSupportedPerturbation': (11561, 'first', ['SM.silent_scaled_top_eq', 'SM.silent_supported_forward_top', 'SM.silent_supported_reversed_full_top', 'SM.silent_supported_coordinates', 'SM.silent_supported_output']), 'FormalSilentCancellation': (10250, 'first', ['SM.map_geometricBoundaryArray', 'SM.silentFarArray_geometric_split', 'SM.silentFarVariable_geometric_support', 'SM.formal_silent_cancellation'])}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
baseline_path = CHECKS / 'formal-cancellation-baseline-20260911.json'
baseline = json.loads(baseline_path.read_text())['frozen_files_sha256']
assert len(baseline) == 876
for name, digest in baseline.items():
    assert sha(ROOT / name) == digest, f'Changed baseline: {name}'
canonical = [x for x in baseline if x.startswith('work/lean/SM/') and x.endswith('.lean')]
assert len(canonical) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327
receipts, evidence, declarations = {}, {}, {}
pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for stem, (session, attempt, expected) in GROUPS.items():
    rp = CHECKS / f'{stem}-prototype-result.json'
    r = json.loads(rp.read_text())
    assert r['kernel_session'] == session and r['exit_code'] == 0
    assert r['source_claim_acceptance_increment'] == 0
    assert r['printed_declarations'] == expected
    prototype = (CHECKS / f'{stem}.prototype.lean').read_text()
    log = (CHECKS / f'{stem}-{attempt}-kernel.log').read_text()
    assert not re.search(r'\berror(?:\(|:)', log), stem
    traces = re.findall(pattern, log)
    assert [name for name, _ in traces] == expected, stem
    parsed = {name: [x.strip() for x in axs.split(',') if x.strip()] for name, axs in traces}
    assert parsed == r['declaration_axioms'], stem
    assert all(set(axs) <= ALLOWED for axs in parsed.values()), stem
    for name, digest in r['files_sha256'].items():
        path = ROOT / name
        assert sha(path) == digest, f'Changed evidence: {name}'
        if name.endswith('.body.lean'):
            assert prototype.count(path.read_text()) == 1, f'Embedding: {name}'
            assert not re.search(r'(?m)^\s*(axiom|sorry|admit)\b|\bnative_decide\b', path.read_text()), name
        assert name not in evidence or evidence[name] == digest
        evidence[name] = digest
    receipts[str(rp.relative_to(ROOT))] = sha(rp)
    declarations.update(parsed)
assert len(declarations) == 83
manifest_path = CHECKS / 'formal-cancellation-preserved-failures-20260912.json'
failures = json.loads(manifest_path.read_text())['failures']
assert len(failures) == 7
expected_failed = {'SelectedGapFarArray:first':77146, 'NearFarRingMaps:first':50920,
 'SilentFarPolynomial:first':80793, 'SilentFarPolynomial:second':76834,
 'PositionalCutDecomposition:first':43011, 'SilentCompositionLine:first':15115,
 'TopFarCancellation:first':40707}
headers = lambda t: re.findall(r'(?ms)^theorem .*? :=', t)
for key, failure in failures.items():
    assert failure['kernel_session'] == expected_failed[key] and failure['exit_code'] == 1
    for name, digest in failure['files_sha256'].items():
        assert sha(ROOT / name) == digest, f'Changed failed snapshot: {name}'
        evidence[name] = digest
    stem, attempt = key.split(':')
    assert headers((CHECKS / f'{stem}.body.lean').read_text()) == headers(
        (CHECKS / f'{stem}-{attempt}-failed.body.lean').read_text()), f'Theorem type repair: {stem}'
for stem in ['SelectedCutRefinement', 'PositionalCutDecomposition', 'SilentGapTransform']:
    for kind in ['body','prototype']:
        path = CHECKS / f'{stem}-first-draft.{kind}.lean'
        other = CHECKS / (f'{stem}-first-failed.{kind}.lean' if stem == 'PositionalCutDecomposition'
                         else f'{stem}.{kind}.lean')
        assert path.read_bytes() == other.read_bytes(), f'Original draft: {path}'
        evidence[str(path.relative_to(ROOT))] = sha(path)
source = ROOT / 'reference/SM/sm-2-amplitude.tex'
assert sha(source) == '014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf'
assert sha(ROOT / 'work/lean/lean-declarations.json') == 'f90f11ebdf5ce92b303fa879479bde4d04ba1b4f1e4c864fcc5688850eafc49c'
ledger_path = ROOT / 'work/checkpoints/goal-turn-086-candidates.json'
ledger = json.loads(ledger_path.read_text())
assert [x['declaration'] for x in ledger] == list(declarations)
assert all(x['source_acceptance_increment'] == 0 for x in ledger)
result = {'utc':datetime.now(timezone.utc).isoformat(), 'verification':'passed',
 'new_kernel_checked_candidate_declarations':83, 'frozen_baseline_files_unchanged':876,
 'canonical_modules_unchanged':327, 'unique_candidate_evidence_files_checked':len(evidence),
 'baseline_sha256':sha(baseline_path), 'receipts_sha256':receipts,
 'candidate_ledger_sha256':sha(ledger_path), 'source_sha256':sha(source),
 'declaration_axioms':declarations, 'repair_statement_text_preserved':True,
 'preserved_failure_manifest_sha256':sha(manifest_path),
 'source_claim_acceptance_increment':0, 'whole_library_audit_rerun':False,
 'source_fidelity_approval':'pending; not granted by this verifier'}
q = CHECKS / 'checkpoint-086-verification.json'
if q.exists():
    old = json.loads(q.read_text())
    assert {k:v for k,v in old.items() if k != 'utc'} == {k:v for k,v in result.items() if k != 'utc'}
else: q.write_text(json.dumps(result,indent=2)+'\n')
print(f"PASS:83 candidate declarations;{len(evidence)} evidence files;876 frozen files;327 canonical modules unchanged.")
print('Full formal-cancellation source candidate; stronger fidelity and canonical acceptance remain pending.')
