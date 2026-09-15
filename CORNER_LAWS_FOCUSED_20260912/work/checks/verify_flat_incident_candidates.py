"""Verify recorded candidate evidence; never grant source-fidelity acceptance."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / "work/checks"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {'FlatBoundaryPositions': (50897,
                           'second',
                           ['SM.boundaryIndex_first',
                            'SM.boundaryIndex_last',
                            'SM.boundaryIndex_nonincident_interior',
                            'SM.consecutiveBoundaryTriple',
                            'SM.consecutiveBoundaryTriple_labels',
                            'SM.consecutiveBoundaryTriple_gaps',
                            'SM.consecutiveBoundaryTriple_proper',
                            'SM.flat_nonincident_boundary_data',
                            'SM.incomingFlatTriple',
                            'SM.outgoingFlatTriple',
                            'SM.incomingFlatTriple_labels',
                            'SM.outgoingFlatTriple_labels',
                            'SM.incomingFlatTriple_intervals',
                            'SM.outgoingFlatTriple_intervals',
                            'SM.incomingFlatTriple_support',
                            'SM.outgoingFlatTriple_support']),
 'FlatAffineSigns': (53680,
                     'first',
                     ['SM.flat_epsilons_nonincident',
                      'SM.flat_epsilons_incoming',
                      'SM.flat_epsilons_outgoing',
                      'SM.strictBetween_flat_affine',
                      'SM.CyclicTurnBoundaryOrder',
                      'SM.turn_far_cyclic_signs',
                      'SM.flat_boundary_chi_eq_neg_turn',
                      'SM.flat_boundary_geometric_sign',
                      'SM.WallGerm.flat_boundary_chi_signChanges']),
 'IncidentFlatGapTuples': (40179,
                           'fourth',
                           ['SM.incoming_flat_gap_labels',
                            'SM.outgoing_flat_gap_labels',
                            'SM.incoming_flat_gap_tuple',
                            'SM.outgoing_flat_gap_tuple',
                            'SM.incoming_flat_integer_gap',
                            'SM.outgoing_flat_integer_gap',
                            'SM.treeCoefficient_congr_tuple']),
 'FlatIntegerFactors': (65014,
                        'first',
                        ['SM.boundaryUnitArray_nonleaf_zero',
                         'SM.integer_wall_factor_two_leaves',
                         'SM.integer_wall_factor_left_leaf',
                         'SM.integer_wall_factor_right_leaf']),
 'FlatIncidentResponse': (5174,
                          'second',
                          ['SM.WallGerm.flat_incoming_signed_response',
                           'SM.WallGerm.flat_outgoing_signed_response',
                           'SM.WallGerm.flat_incident_signed_response']),
 'FlatIncidentAllSizes': (86495, 'first', ['SM.WallGerm.flat_incident_signed_response_all_sizes'])}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline_path = CHECKS / "flat-boundary-baseline-20260911.json"
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
assert len(declarations) == 40
headers = lambda body: re.findall(r"(?ms)^theorem .*? := by", body)
for stem, attempts in {
    "FlatBoundaryPositions": ["first"],
    "IncidentFlatGapTuples": ["first", "second", "third"],
    "FlatIncidentResponse": ["first"],
}.items():
    current = (CHECKS / f"{stem}.body.lean").read_text()
    for attempt in attempts:
        earlier = (CHECKS / f"{stem}-{attempt}.body.lean").read_text()
        assert all(h in headers(current) for h in headers(earlier)), f"Changed statement: {stem} {attempt}"
first_boundary = (CHECKS / "FlatBoundaryPositions-first.body.lean").read_text()
current_boundary = (CHECKS / "FlatBoundaryPositions.body.lean").read_text()
definitions = lambda body: re.findall(r"(?ms)^def .*?(?=^theorem|^def|\Z)", body)
assert definitions(first_boundary) == definitions(current_boundary)
incident = (CHECKS / "IncidentFlatGapTuples.body.lean").read_text()
third_incident = (CHECKS / "IncidentFlatGapTuples-third.body.lean").read_text()
assert incident.replace("treeCoefficient_congr_tuple (k := m + 3) _ _ _ _",
                        "treeCoefficient_congr_tuple _ _ _ _") == third_incident
source = ROOT / "reference/SM/sm-2-amplitude.tex"
assert sha(source) == "014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf"
result = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "verification": "passed", "new_kernel_checked_candidate_declarations": 40,
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
report_path = CHECKS / "checkpoint-077-verification.json"
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
