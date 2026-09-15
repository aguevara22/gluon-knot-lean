# Geometric duplication first-run repair

Root first34975 failed only in the proof of softRootFarData_neighbors: simplification had changed its two reflexive equalities to True, so the final equality constructors were not of the required type. The proof now uses the two True constructors. All11 public declarations and every other proof are unchanged. Exact failed body/prototype/log and first drafts are preserved. This is a proof elaboration repair, with no premise or mathematical conclusion change.
