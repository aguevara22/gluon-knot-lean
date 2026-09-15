"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {'CuspIntegerFactors': (35543, 'second', ['SM.integer_wall_factor_left_leaf_pos_pos', 'SM.integer_wall_factor_left_leaf_pos_neg', 'SM.integer_wall_factor_right_leaf_neg_pos', 'SM.integer_wall_factor_right_leaf_pos_pos']), 'CuspAffineSigns': (39700, 'first', ['SM.cusp_epsilons_incoming_gt_one', 'SM.cusp_epsilons_incoming_lt_zero', 'SM.cusp_epsilons_outgoing_gt_one', 'SM.cusp_epsilons_outgoing_lt_zero', 'SM.WallGerm.cusp_exterior_affine']), 'CuspSignedResponse': (30121, 'first', ['SM.WallGerm.cusp_nonincident_signed_response', 'SM.WallGerm.cusp_incoming_signed_response', 'SM.WallGerm.cusp_outgoing_signed_response', 'SM.WallGerm.cusp_incident_signed_response_all_sizes', 'SM.WallGerm.cusp_signed_response_all_roots']), 'CuspOrientedResponse': (95209, 'first', ['SM.WallGerm.cusp_negative_minus_positive_near', 'SM.WallGerm.cusp_negative_minus_positive']), 'CuspSourceResponse': (68098, 'second', ['SM.WallGerm.cusp_loop_tree_response', 'SM.WallGerm.cusp_tree_law'])}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "cusp-source-baseline-20260911.json"
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
assert len(declarations) == 18
headers = lambda body: re.findall(r"(?ms)^theorem .*? := by", body)
for stem in ["CuspIntegerFactors", "CuspSourceResponse"]:
    current = (CHECKS / f"{stem}.body.lean").read_text()
    earlier = (CHECKS / f"{stem}-first.body.lean").read_text()
    assert headers(current) == headers(earlier), f"Changed statement: {stem}"
source = ROOT / "reference/SM/sm-2-amplitude.tex"
assert sha(source) == "014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf"
result = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "verification": "passed", "new_kernel_checked_candidate_declarations": 18,
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
report_path = CHECKS / "checkpoint-079-verification.json"
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
