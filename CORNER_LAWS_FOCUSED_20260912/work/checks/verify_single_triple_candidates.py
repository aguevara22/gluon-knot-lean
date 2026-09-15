"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {
    "ContractionOutput": (16114, "first", [
        "SM.IntervalComposition.expandComposition_injective",
        "SM.IntervalComposition.mem_range_expandComposition",
        "SM.IntervalComposition.sum_composition_expansion",
        "SM.farOnlyCoordinates_response_containing",
        "SM.farTransform_contraction_response",
        "SM.farOnlyOutput_contraction_response",
        "SM.farOnlyOutput_full_contraction",
    ]),
    "ProperSpanGermResponse": (50436, "first", [
        "SM.geometric_proper_output_response",
        "SM.WallGerm.proper_span_tree_response",
    ]),
    "CriticalAffineData": (2001, "first", [
        "SM.distinct_collinear_affine_data", "SM.critical_boundary_affine_data",
    ]),
    "SignedCriticalJump": (61164, "second", [
        "SM.sign_half_difference", "SM.WallGerm.side_chi_signChanges_opposite",
        "SM.WallGerm.chi_signChanges_parameters", "SM.WallGerm.boundary_half_jump_signed",
    ]),
    "SingleTripleTreeResponse": (84196, "second", [
        "SM.WallGerm.single_triple_tree_response_of_affine",
        "SM.WallGerm.single_triple_tree_response",
    ]),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "contraction-output-baseline-20260911.json"
baseline = json.loads(baseline_path.read_text())
for name, digest in baseline["frozen_files_sha256"].items():
    assert sha(ROOT / name) == digest, f"Changed baseline file: {name}"
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
assert len(declarations) == 17
signed = (CHECKS / "SignedCriticalJump.body.lean").read_text()
signed_first = (CHECKS / "SignedCriticalJump-first.body.lean").read_text()
assert signed.replace("    subst s\n    cases t <;> decide",
                      "    cases s <;> cases t <;> norm_num at *") == signed_first
aggregate = (CHECKS / "SingleTripleTreeResponse.body.lean").read_text()
assert aggregate.replace("\nattribute [local instance] Classical.propDecidable", "") == (
    CHECKS / "SingleTripleTreeResponse-first.body.lean").read_text()
source = ROOT / "reference/SM/sm-2-amplitude.tex"
assert sha(source) == "014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf"
result = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "verification": "passed", "new_kernel_checked_candidate_declarations": 17,
    "frozen_baseline_files_unchanged": len(baseline["frozen_files_sha256"]),
    "canonical_modules_unchanged": len(canonical),
    "unique_candidate_evidence_files_checked": len(evidence),
    "baseline_sha256": sha(baseline_path), "receipts_sha256": receipts,
    "source_sha256": sha(source), "declaration_axioms": declarations,
    "repair_statement_text_preserved": True,
    "source_fidelity_approval": "pending; not provided by this verifier",
    "source_claim_acceptance_increment": 0,
    "whole_library_audit_rerun": False,
}
report_path = CHECKS / "checkpoint-075-verification.json"
if report_path.exists():
    recorded = json.loads(report_path.read_text())
    assert {k: v for k, v in recorded.items() if k != "utc"} == {
        k: v for k, v in result.items() if k != "utc"
    }, "Recorded verification differs; write a new checkpoint instead of overwriting it"
else:
    report_path.write_text(json.dumps(result, indent=2) + "\n")
print("PASS: 17 candidate declarations; 37 evidence files; 436 frozen files; 327 canonical modules unchanged.")
print("Source-fidelity acceptance remains pending; original accepted count is unchanged.")
