"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {'TripleTreeData': (97775, 'first', ['SM.WallGerm.g1_center_side_chi', 'SM.WallGerm.triple_wall_tree_data']), 'SilentIntegerFactors': (44434, 'first', ['SM.integer_U_product_zero_of_left_nonleaf_pos', 'SM.integer_U_product_zero_of_right_nonleaf_pos', 'SM.integer_U_product_zero_of_nonleaves_one_positive', 'SM.integer_UV_products_zero_of_nonleaves_opposite']), 'GermTreeEquality': (29206, 'second', ['SM.WallGerm.tree_sides_equal_of_local_zero']), 'PureCutBoundaryBounds': (38666, 'first', ['SM.pureCut_left_gap_nonleaf', 'SM.pureCut_right_gap_nonleaf', 'SM.pureCut_wrap_gap_nonleaf', 'SM.pureCut_span_proper']), 'ExtensionAffineSigns': (22631, 'first', ['SM.extension_epsilons_base', 'SM.extension_right_epsilon_first_arc', 'SM.extension_left_epsilon_second_arc', 'SM.WallGerm.extension_exterior_affine']), 'PureCutTreeResponse': (73319, 'second', ['SM.WallGerm.pure_cut_tree_silent_near', 'SM.WallGerm.pure_cut_tree_silent']), 'ExtensionTreeResponse': (63236, 'first', ['SM.WallGerm.extension_base_tree_silent_near', 'SM.WallGerm.extension_first_arc_tree_silent_near', 'SM.WallGerm.extension_second_arc_tree_silent_near', 'SM.WallGerm.extension_tree_silent_near', 'SM.WallGerm.extension_tree_silent']), 'TripleSilentTreeLaws': (2126, 'first', ['SM.tree_triple_and_silent_laws'])}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "silent-tree-baseline-20260911.json"
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
assert len(declarations) == 23
for stem in ["GermTreeEquality", "PureCutTreeResponse"]:
    assert (CHECKS / f"{stem}.body.lean").read_bytes() == (
        CHECKS / f"{stem}-first.body.lean").read_bytes(), "Changed repaired body"
    before = (CHECKS / f"{stem}-first.prototype.lean").read_text()
    after = (CHECKS / f"{stem}.prototype.lean").read_text()
    if stem == "GermTreeEquality":
        assert after == before.replace("import SM.WallGerm\n", "import SM.GermSides\n")
    else:
        assert after == "import SM.UnorderedWallTriples\n" + before
manifest_path = CHECKS / "silent-tree-preserved-failures-20260911.json"
assert sha(manifest_path) == "36981e5caf8d566fd8460995782d4815ba4f5685e72a10ddcc60602d4f9a54c1"
failures = json.loads(manifest_path.read_text())
assert failures["GermTreeEquality"]["kernel_session"] == 44970
assert failures["PureCutTreeResponse"]["kernel_session"] == 55482
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
    "verification": "passed", "new_kernel_checked_candidate_declarations": 23,
    "frozen_baseline_files_unchanged": len(baseline["frozen_files_sha256"]),
    "canonical_modules_unchanged": len(canonical),
    "unique_candidate_evidence_files_checked": len(evidence),
    "baseline_sha256": sha(baseline_path), "receipts_sha256": receipts,
    "source_sha256": sha(source), "declaration_axioms": declarations,
    "repair_statement_text_preserved": True,
    "repair_bodies_byte_identical": True,
    "repairs_import_only": True,
    "preserved_failure_manifest_sha256": sha(manifest_path),
    "source_fidelity_approval": "pending; not provided by this verifier",
    "source_claim_acceptance_increment": 0,
    "whole_library_audit_rerun": False,
}
report_path = CHECKS / "checkpoint-082-verification.json"
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
