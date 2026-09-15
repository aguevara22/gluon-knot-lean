"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {'WeakLineGeometry': (98317, 'first', ['SM.weak_vertices_injective', 'SM.weak_boundaryWord_injective', 'SM.line_coordinate_interpolation', 'SM.line_coordinate_between_parameter', 'SM.weak_line_edge_no_between', 'SM.weak_not_three_consecutive_on_line', 'SM.boundaryIndex_successive', 'SM.weak_boundary_leaf_no_between']), 'FiniteLineGaps': (15599, 'first', ['SM.FiniteLineOrder.second_max_bound', 'SM.FiniteLineOrder.exists_increasing_nonleaf_gap', 'SM.FiniteLineOrder.exists_decreasing_nonleaf_gap']), 'WeakLineSelections': (98027, 'second', ['SM.boundaryIndex_first_of_val', 'SM.boundaryIndex_last_of_val', 'SM.weak_not_successive_labels_on_line', 'SM.weak_line_coordinate_injective', 'SM.weak_line_selection_clear', 'SM.weak_line_selection_no_successive_leaves', 'SM.weak_line_selection_root_clear', 'SM.weak_line_selection_first_not_leaf', 'SM.weak_line_selection_last_not_leaf']), 'LineCoordinateNormalization': (63737, 'first', ['SM.lineGapEpsilon', 'SM.normalizedLineCoordinate', 'SM.selected_endpoint_difference_nonzero', 'SM.normalizedLineCoordinate_first', 'SM.normalizedLineCoordinate_last', 'SM.normalizedLineCoordinate_injective', 'SM.normalizedLineCoordinate_representation', 'SM.normalizedLineCoordinate_gap', 'SM.lineGapEpsilon_positive', 'SM.lineGapEpsilon_negative']), 'WeakSelectedLineCoordinates': (74872, 'first', ['SM.selectedLineCoordinate', 'SM.weak_selected_line_coordinates']), 'SilentLineGap': (23877, 'second', ['SM.silent_line_gap', 'SM.silent_line_gap_of_collinear'])}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "silent-line-gap-baseline-20260911.json"
baseline = json.loads(baseline_path.read_text())
for name, digest in baseline["frozen_files_sha256"].items():
    assert sha(ROOT / name) == digest, f"Changed baseline file: {name}"
assert len(baseline["frozen_files_sha256"]) == 832
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
assert len(declarations) == 34
headers = lambda body: re.findall(r"(?ms)^(?:@\[simp\] )?theorem .*? :=", body)
for stem, suffix in [('WeakLineSelections', 'first-failed'), ('SilentLineGap', 'first-failed')]:
    assert headers((CHECKS / f"{stem}.body.lean").read_text()) == headers(
        (CHECKS / f"{stem}-{suffix}.body.lean").read_text()), "Changed repaired theorem type"
manifest_path = CHECKS / "silent-line-gap-preserved-failures-20260911.json"
assert sha(manifest_path) == "5ea80f8301cfabd9478d083a782946b2ade889410e408d09d5d95838bef4882e"
failures = json.loads(manifest_path.read_text())
for stem, session in [('WeakLineSelections', 70739), ('SilentLineGap', 10149)]:
    assert failures[stem]["kernel_session"] == session
for failed in failures.values():
    assert failed["exit_code"] == 1
    for name, digest in failed["files_sha256"].items():
        assert sha(ROOT / name) == digest, f"Changed preserved failure: {name}"
        evidence[name] = digest
for kind in ["body", "prototype"]:
    draft = CHECKS / f"FiniteLineGaps-first-draft.{kind}.lean"
    assert draft.read_bytes() == (CHECKS / f"FiniteLineGaps.{kind}.lean").read_bytes()
    evidence[str(draft.relative_to(ROOT))] = sha(draft)
assert len(list((ROOT / "work/lean/SM").glob("*.lean"))) == 327
source = ROOT / "reference/SM/sm-2-amplitude.tex"
assert sha(source) == "014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf"
result = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "verification": "passed", "new_kernel_checked_candidate_declarations": 34,
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
report_path = CHECKS / "checkpoint-085-verification.json"
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
