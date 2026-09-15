"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {'ContactRootPartition': (71853, 'second', ['SM.contact_relative_offset_val', 'SM.firstHalf_inherited_root_iff', 'SM.secondHalfEdgeIndex_range_iff', 'SM.secondHalf_inherited_root_iff', 'SM.contact_root_cases', 'SM.contact_root_cases_disjoint']), 'ContactAffineSigns': (89634, 'first', ['SM.contact_epsilons_base', 'SM.contact_epsilons_first_arc', 'SM.contact_epsilons_second_arc', 'SM.WallGerm.contact_interior_affine', 'SM.CyclicContactBoundaryOrder', 'SM.contact_boundary_chi_eq_neg', 'SM.contact_boundary_geometric_sign', 'SM.WallGerm.contact_boundary_chi_signChanges']), 'ContactHalfRoots': (90785, 'first', ['SM.contactHalfRoots', 'SM.contactHalfRoots_base', 'SM.contactHalfRoots_first', 'SM.contactHalfRoots_second', 'SM.contactHalfRoots_spec', 'SM.contactHalfRoots_vertices']), 'ContactBoundaryPositions': (54811, 'second', ['SM.contactBaseTriple', 'SM.contactFirstArcTriple', 'SM.contactSecondArcTriple', 'SM.contactBaseTriple_labels', 'SM.contactFirstArcTriple_labels', 'SM.contactSecondArcTriple_labels', 'SM.contactBaseTriple_gaps', 'SM.contactFirstArcTriple_gaps', 'SM.contactSecondArcTriple_gaps', 'SM.contactBaseTriple_full', 'SM.contactFirstArcTriple_proper', 'SM.contactSecondArcTriple_proper', 'SM.contactFirstArcTriple_contractedSize', 'SM.contactSecondArcTriple_contractedSize']), 'ContactGapTuples': (74248, 'first', ['SM.restrictedWord_reindex_start', 'SM.restrictedWord_eq_secondHalf', 'SM.restrictedWord_eq_shift_firstHalf', 'SM.restrictedWord_secondHalf_coefficient', 'SM.restrictedWord_firstHalf_coefficient']), 'ContactGapWords': (49933, 'first', ['SM.contactBaseTriple_left_word', 'SM.contactBaseTriple_right_word', 'SM.contactFirstArcTriple_right_word', 'SM.contactSecondArcTriple_left_word'])}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "contact-root-baseline-20260911.json"
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
assert len(declarations) == 43
headers = lambda body: re.findall(r"(?ms)^theorem .*? :=", body)
for stem in ["ContactRootPartition", "ContactBoundaryPositions"]:
    current = (CHECKS / f"{stem}.body.lean").read_text()
    earlier = (CHECKS / f"{stem}-first.body.lean").read_text()
    assert headers(current) == headers(earlier), f"Changed statement: {stem}"
    if stem == "ContactBoundaryPositions":
        assert current.split("theorem ", 1)[0] == earlier.split("theorem ", 1)[0]
manifest_path = CHECKS / "contact-root-preserved-failures-20260911.json"
assert sha(manifest_path) == 'ff1bfe089c61748d447e3993bf973443d03994db1b791bca01da0d2e02a71099'
failures = json.loads(manifest_path.read_text())
assert {k: v["kernel_session"] for k, v in failures.items()} == {
    "ContactRootPartition": 15257, "ContactBoundaryPositions": 2538}
for failed in failures.values():
    assert failed["exit_code"] == 1
    for name, digest in failed["files_sha256"].items():
        assert sha(ROOT / name) == digest, f"Changed preserved failure: {name}"
        evidence[name] = digest
source = ROOT / "reference/SM/sm-2-amplitude.tex"
assert sha(source) == "014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf"
result = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "verification": "passed", "new_kernel_checked_candidate_declarations": 43,
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
report_path = CHECKS / "checkpoint-080-verification.json"
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
