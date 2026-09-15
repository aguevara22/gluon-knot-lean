"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {'FlatContractionArithmetic': (93700, 'first', ['SM.consecutive_erased_one', 'SM.consecutive_contracted_size', 'SM.nonincident_fusionIndex_eq', 'SM.nonincident_fusionIndex_cut_relation', 'SM.zmod_cut_shift_val']), 'TupleArityTransport': (29466, 'second', ['SM.g1_reindex_size', 'SM.treeCoefficient_reindex_size', 'SM.treeCoefficient_of_reindexed_tuple_eq']), 'TurnResponseOrientation': (81061, 'first', ['SM.WallGerm.turn_right_left_opposite_time_sides', 'SM.WallGerm.turn_response_right_minus_left']), 'NonincidentFlatContraction': (86583, 'second', ['SM.nonincident_flat_contracted_labels', 'SM.nonincident_flat_contracted_tuple', 'SM.nonincident_flat_contracted_support', 'SM.nonincident_flat_contracted_coefficient']), 'FlatNonincidentResponse': (31841, 'first', ['SM.WallGerm.flat_nonincident_signed_response']), 'FlatAllRootResponse': (58448, 'first', ['SM.WallGerm.flat_signed_response_all_roots', 'SM.WallGerm.flat_right_minus_left_near']), 'FlatSourceResponse': (25627, 'first', ['SM.WallGerm.nearby_same_chirotope', 'SM.WallGerm.flat_right_minus_left'])}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "flat-nonincident-baseline-20260911.json"
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
assert len(declarations) == 19
headers = lambda body: re.findall(r"(?ms)^theorem .*? := by", body)
for stem in ["TupleArityTransport", "NonincidentFlatContraction"]:
    current = (CHECKS / f"{stem}.body.lean").read_text()
    earlier = (CHECKS / f"{stem}-first.body.lean").read_text()
    assert headers(current) == headers(earlier), f"Changed statement: {stem}"
source = ROOT / "reference/SM/sm-2-amplitude.tex"
assert sha(source) == "014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf"
result = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "verification": "passed", "new_kernel_checked_candidate_declarations": 19,
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
report_path = CHECKS / "checkpoint-078-verification.json"
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
