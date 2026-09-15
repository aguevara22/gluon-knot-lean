"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {'CompositionTripleSupports': (72033, 'first', ['SM.IntervalComposition.cutTripleSet', 'SM.IntervalComposition.mem_cutTripleSet', 'SM.IntervalComposition.nearTriple_injective', 'SM.IntervalComposition.nearTriple_eq_farTriple_iff', 'SM.IntervalComposition.cutTripleSet_disjoint', 'SM.IntervalComposition.cutTripleSet_bounds', 'SM.IntervalComposition.cutTripleSet_middle_mem', 'SM.IntervalComposition.cutTripleSet_not_contained_in_part', 'SM.IntervalComposition.triple_containing_part_unique']), 'CanonicalTripleSigns': (60299, 'second', ['SM.canonicalPosition', 'SM.canonical_label', 'SM.canonical_label_range', 'SM.boundaryIndex_canonicalPosition', 'SM.canonicalPosition_boundaryIndex', 'SM.canonicalPosition_injective', 'SM.sortTriplePositions', 'SM.sortTriplePositions_sign', 'SM.sortTriplePositions_positionSet', 'SM.canonicalTripleValue', 'SM.sortTriplePositions_evaluation']), 'FormalOrderedChi': (82948, 'second', ['SM.orderedTripleData', 'SM.orderedTripleData_sign', 'SM.orderedTripleData_vertexSet', 'SM.orderedTripleData_evaluation', 'SM.formalOrderedChi', 'SM.formalOrderedChi_distinct', 'SM.formalOrderedChi_repeated', 'SM.eval_formalOrderedChi', 'SM.boundaryTripleData', 'SM.boundaryTripleData_vertexSet', 'SM.boundaryTripleData_injective', 'SM.formalBoundaryChi', 'SM.formalBoundaryChi_eq', 'SM.eval_formalBoundaryChi']), 'FormalTriplePolynomial': (95654, 'first', ['SM.gate_pair_rational', 'SM.IntervalComposition.tripleOrdinaryFactor', 'SM.IntervalComposition.tripleRootFactor', 'SM.IntervalComposition.tripleOrdinaryWeight', 'SM.IntervalComposition.tripleRootWeight', 'SM.IntervalComposition.tripleFactors_binary', 'SM.IntervalComposition.tripleWeights_unary', 'SM.IntervalComposition.tripleOrdinaryWeight_binary', 'SM.IntervalComposition.tripleRootWeight_binary', 'SM.IntervalComposition.eval_tripleOrdinaryFactor', 'SM.IntervalComposition.eval_tripleRootFactor', 'SM.IntervalComposition.eval_tripleOrdinaryWeight', 'SM.IntervalComposition.eval_tripleRootWeight', 'SM.canonicalTreePolynomial', 'SM.canonicalTreePolynomial_eq_signed_tree_sum', 'SM.eval_canonicalTreePolynomial']), 'PlaneTreeTripleSupports': (46937, 'second', ['SM.OpenPlaneTree.CutOccurrence', 'SM.OpenPlaneTree.cutTripleSupport', 'SM.OpenPlaneTree.cutOccurrence_finite', 'SM.OpenPlaneTree.cutOccurrence_fintype', 'SM.OpenPlaneTree.cutTripleSupport_bounds', 'SM.OpenPlaneTree.tripleSupport', 'SM.OpenPlaneTree.mem_tripleSupport', 'SM.OpenPlaneTree.tripleSupport_bounds', 'SM.IntervalComposition.cutTripleSet_disjoint_child_support', 'SM.IntervalComposition.children_tripleSupport_disjoint', 'SM.OpenPlaneTree.cutTripleSupport_pairwise', 'SM.OpenPlaneTree.cutTripleSupport_nonrepetition', 'SM.RootedPlaneTree.CutOccurrence', 'SM.RootedPlaneTree.cutTripleSupport', 'SM.RootedPlaneTree.cutOccurrence_finite', 'SM.RootedPlaneTree.cutOccurrence_fintype', 'SM.RootedPlaneTree.cutTripleSupport_bounds', 'SM.RootedPlaneTree.cutTripleSupport_pairwise', 'SM.RootedPlaneTree.cutTripleSupport_nonrepetition', 'SM.RootedPlaneTree.tripleSupport', 'SM.RootedPlaneTree.mem_tripleSupport', 'SM.RootedPlaneTree.tripleSupport_bounds', 'SM.RootedPlaneTree.cutOccurrence_of_unary']), 'SupportedMultiaffine': (75825, 'second', ['SM.SupportedMultiaffine', 'SM.SupportedMultiaffine.degree_le_one', 'SM.SupportedMultiaffine.constant', 'SM.SupportedMultiaffine.zero', 'SM.SupportedMultiaffine.one', 'SM.SupportedMultiaffine.X_singleton', 'SM.SupportedMultiaffine.mono', 'SM.SupportedMultiaffine.neg', 'SM.SupportedMultiaffine.add', 'SM.SupportedMultiaffine.sub', 'SM.SupportedMultiaffine.constant_mul', 'SM.SupportedMultiaffine.mul_disjoint', 'SM.SupportedMultiaffine.prod', 'SM.SupportedMultiaffine.sum']), 'PlaneTreeInternalIntervals': (17495, 'first', ['SM.OpenPlaneTree.InternalOccurrence', 'SM.OpenPlaneTree.internalInterval', 'SM.OpenPlaneTree.IsTopInternal', 'SM.OpenPlaneTree.internalInterval_bounds', 'SM.OpenPlaneTree.internalInterval_leaves_le', 'SM.IntervalComposition.child_internalInterval_leaves_lt', 'SM.IntervalComposition.part_eq_parent_of_unary', 'SM.OpenPlaneTree.internalInterval_leaves_lt_of_not_top', 'SM.OpenPlaneTree.internalInterval_eq_parent_iff_top', 'SM.OpenPlaneTree.internalInterval_injective', 'SM.RootedPlaneTree.InternalOccurrence', 'SM.RootedPlaneTree.internalInterval', 'SM.RootedPlaneTree.rootOccurrence', 'SM.RootedPlaneTree.IsImmediateChild', 'SM.RootedPlaneTree.internalInterval_bounds', 'SM.RootedPlaneTree.childInternalInterval_injective', 'SM.RootedPlaneTree.child_internalInterval_eq_root_iff', 'SM.RootedPlaneTree.internalInterval_eq_of_distinct', 'SM.RootedPlaneTree.unary_cut_product']), 'CanonicalTripleDegree': (88201, 'first', ['SM.canonicalSupport', 'SM.canonicalSupport_mono', 'SM.canonicalSupport_disjoint', 'SM.canonicalSupport_union', 'SM.canonicalSupport_biUnion', 'SM.formalBoundaryChi_supported', 'SM.IntervalComposition.tripleSupport', 'SM.IntervalComposition.mem_tripleSupport', 'SM.IntervalComposition.tripleFactors_supported', 'SM.IntervalComposition.tripleWeights_supported', 'SM.IntervalComposition.tripleSupport_disjoint_child_support', 'SM.IntervalComposition.tripleSupport_disjoint_children_support', 'SM.RootedPlaneTree.canonical_cut_nonrepetition']), 'TreeTripleDegree': (61050, 'first', ['SM.OpenPlaneTree.tripleSupport_node', 'SM.RootedPlaneTree.tripleSupport_eq', 'SM.IntervalComposition.combine_supported', 'SM.OpenPlaneTree.tripleWeight_supported', 'SM.RootedPlaneTree.tripleWeight_supported', 'SM.canonicalTreePolynomial_multiaffine']), 'MultiaffineForm': (20791, 'first', ['SM.multiaffine_form'])}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "tree-multiaffine-baseline-20260911.json"
baseline = json.loads(baseline_path.read_text())
for name, digest in baseline["frozen_files_sha256"].items():
    assert sha(ROOT / name) == digest, f"Changed baseline file: {name}"
assert len(baseline["frozen_files_sha256"]) == 765
canonical = [name for name in baseline["frozen_files_sha256"]
             if name.startswith("work/lean/SM/") and name.endswith(".lean")]
assert len(canonical) == 327
receipts, evidence, declarations = {}, {}, {}
pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for stem, (session, attempt, expected) in GROUPS.items():
    receipt_path = CHECKS / f"{stem}-prototype-result.json"
    receipt = json.loads(receipt_path.read_text())
    assert receipt["kernel_session"] == session and receipt["exit_code"] == 0
    assert receipt["source_claim_acceptance_increment"] == 0
    assert receipt["printed_declarations"] == expected
    prototype = (CHECKS / f"{stem}.prototype.lean").read_text()
    log = (CHECKS / f"{stem}-{attempt}-kernel.log").read_text()
    assert not re.search(r"\berror(?:\(|:)", log), stem
    traces = re.findall(pattern, log)
    assert [name for name, _ in traces] == expected, stem
    parsed = {name: [a.strip() for a in axioms.split(",") if a.strip()]
              for name, axioms in traces}
    assert parsed == receipt["declaration_axioms"], stem
    assert all(set(axioms) <= ALLOWED for axioms in parsed.values()), stem
    for name, digest in receipt["files_sha256"].items():
        path = ROOT / name
        assert sha(path) == digest, f"Changed evidence: {name}"
        if name.endswith(".body.lean"):
            assert prototype.count(path.read_text()) == 1, f"Body embedding: {name}"
        assert name not in evidence or evidence[name] == digest
        evidence[name] = digest
    receipts[str(receipt_path.relative_to(ROOT))] = sha(receipt_path)
    declarations.update(parsed)
assert len(declarations) == 126
headers = lambda body: re.findall(r"(?ms)^(?:@\[simp\] )?theorem .*? :=", body)
for stem, suffix in [('CanonicalTripleSigns', 'first-failed'), ('FormalOrderedChi', 'first-failed'), ('PlaneTreeTripleSupports', 'first'), ('SupportedMultiaffine', 'first-failed')]:
    assert headers((CHECKS / f"{stem}.body.lean").read_text()) == headers(
        (CHECKS / f"{stem}-{suffix}.body.lean").read_text()), "Changed repaired theorem type"
manifest_path = CHECKS / "tree-multiaffine-preserved-failures-20260911.json"
assert sha(manifest_path) == "d7eb064da9098ad9ddd4588ce4dcc8cc4861a80052dd16bff73b09397148541e"
failures = json.loads(manifest_path.read_text())
for stem, session in [('CanonicalTripleSigns', 11385), ('FormalOrderedChi', 20845), ('PlaneTreeTripleSupports', 65349), ('SupportedMultiaffine', 29366)]:
    assert failures[stem]["kernel_session"] == session
for failed in failures.values():
    assert failed["exit_code"] == 1
    for name, digest in failed["files_sha256"].items():
        assert sha(ROOT / name) == digest, f"Changed preserved failure: {name}"
        evidence[name] = digest
assert len(list((ROOT / "work/lean/SM").glob("*.lean"))) == 327
source = ROOT / "reference/SM/sm-2-amplitude.tex"
assert sha(source) == "014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf"
result = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "verification": "passed", "new_kernel_checked_candidate_declarations": 126,
    "frozen_baseline_files_unchanged": len(baseline["frozen_files_sha256"]),
    "canonical_modules_unchanged": len(canonical),
    "unique_candidate_evidence_files_checked": len(evidence),
    "baseline_sha256": sha(baseline_path), "receipts_sha256": receipts,
    "source_sha256": sha(source), "declaration_axioms": declarations,
    "repair_statement_text_preserved": True,
    "preserved_failure_manifest_sha256": sha(manifest_path),
    "source_fidelity_approval": "pending; not provided by this verifier",
    "source_claim_acceptance_increment": 0,
    "whole_library_audit_rerun": False,
}
report_path = CHECKS / "checkpoint-084-verification.json"
if report_path.exists():
    recorded = json.loads(report_path.read_text())
    assert {k: v for k, v in recorded.items() if k != "utc"} == {
        k: v for k, v in result.items() if k != "utc"
    }, "Recorded verification differs; write a new checkpoint instead of overwriting it"
else:
    report_path.write_text(json.dumps(result, indent=2) + "\n")
print(f"PASS: {len(declarations)} candidate declarations; {len(evidence)} evidence files; "
      f"{len(baseline['frozen_files_sha256'])} frozen files; 327 canonical modules unchanged.")
print("Source-fidelity acceptance remains pending; original accepted count is unchanged.")
