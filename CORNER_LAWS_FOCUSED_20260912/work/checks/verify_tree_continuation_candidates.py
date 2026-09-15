"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {'DenseLocalPairs': (79413, 'first', ['SM.dense_local_pairs_extend', 'SM.dense_local_pairs_constant']), 'WeakCenterSilent': (15307, 'first', ['SM.WallGerm.weak_center_not_flat', 'SM.WallGerm.weak_center_not_cusp', 'SM.WallGerm.weak_center_not_vertex', 'SM.WallGerm.weak_center_not_triple', 'SM.WallGerm.silent_of_simple_weak_center']), 'GermPathGeometry': (54231, 'second', ['SM.WallGerm.shifted_curve_eq_path', 'SM.generic_path_dense_of_germs']), 'WeakPathTolerance': (1291, 'first', ['SM.euclidean_path_open_tolerance', 'SM.weak_relative_general_position']), 'TreePathLocal': (1045, 'second', ['SM.g1_all_chi_persists', 'SM.tree_path_pair_near_generic', 'SM.WallGerm.tree_coefficient_same_side', 'SM.WallGerm.tree_parameter_eq_positive_of_sides_equal']), 'TreePathGluing': (5804, 'second', ['SM.WallGerm.silent_tree_parameter_value', 'SM.tree_path_pair_near_silent_event', 'SM.tree_path_constant_of_silent_germs', 'SM.tree_coefficient_eq_along_weak_path']), 'VisibleTreeContinuation': (90683, 'first', ['SM.polygonalJoin_joinedIn', 'SM.weak_visible_path', 'SM.tree_coefficient_visible_chamber', 'SM.visible_chamber_has_generic', 'SM.A_continuation'])}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "tree-continuation-baseline-20260911.json"
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
assert len(declarations) == 24
headers = lambda body: re.findall(r"(?ms)^theorem .*? :=", body)
for stem in ["GermPathGeometry", "TreePathLocal", "TreePathGluing"]:
    assert headers((CHECKS / f"{stem}.body.lean").read_text()) == headers(
        (CHECKS / f"{stem}-first.body.lean").read_text()), "Changed repaired theorem type"
stem = "GermPathGeometry"
assert (CHECKS / f"{stem}.body.lean").read_text() == (
    CHECKS / f"{stem}-first.body.lean").read_text().replace(
        "linarith [min_le_left w.radius ε]", "linarith [min_le_left w.radius ε, w.radius_pos]")
stem = "TreePathGluing"
assert (CHECKS / f"{stem}.body.lean").read_bytes() == (CHECKS / f"{stem}-first.body.lean").read_bytes()
assert (CHECKS / f"{stem}.prototype.lean").read_text() == "import SM.SilentCenter\n" + (
    CHECKS / f"{stem}-first.prototype.lean").read_text()
manifest_path = CHECKS / "tree-continuation-preserved-failures-20260911.json"
assert sha(manifest_path) == "0e2680fc9bd8c3eabdc247cc775a4de6f66182d12175680d931f5dbff4aaaf23"
failures = json.loads(manifest_path.read_text())
for stem, session in [("GermPathGeometry",32126),("TreePathLocal",26364),("TreePathGluing",91465)]:
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
    "verification": "passed", "new_kernel_checked_candidate_declarations": 24,
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
report_path = CHECKS / "checkpoint-083-verification.json"
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
