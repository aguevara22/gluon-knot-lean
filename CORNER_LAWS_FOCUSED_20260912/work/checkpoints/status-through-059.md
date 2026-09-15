# Verified checkpoint059 — full relative general position accepted

Original proofs **15/132 (11.36%)**; original checklist30/191; expanded31/192.
Main targets0/8. The full corner state-sum wall laws, soft theorem and unconditional
R remain active and incomplete. The original proof denominator remains132.

Full source thm:relgp is accepted as SM.relative_general_position in
lean/SM/RelativeGeneralPosition.lean. The source theorem has its original n>=3,
continuous Regular path, Generic endpoints and delta>0 domain. The constructed
path has exact labelled endpoints, a finite affine partition, actual uniform
Euclidean approximation, collision freedom, finite isolated nongeneric events,
actual shifted simple wall germs, exactly one of six noncusp types, and no cusps.
The stronger theorem retains the same event's derivative and smooth graph data.
No literature/custom axioms or R assumptions were used.

Evidence: whole audit059 session54212 exit0;285 canonical SM modules,3455 local
declarations,31 mapped claims. Full independent source review reviews/thm-relgp.json;
canonical independent kernel92115 exit0 checked36 declarations and seven semantic
consumer theorems. All five new namespace bodies equal their reviewed prototypes.
All280 older SM modules remain unchanged. All285 canonical SM modules are frozen.
checks/verify_relgp_checkpoint.py and verify_named_walls.py passed on audit059;
verify_relgp_wall_evidence.py passed for the four earlier component reviews.

Next source chain: root/boundary words, gates, tree coefficient and its laws.
checks/RootBoundary.prototype.lean passed root82017 exit0 and is frozen. It keeps
raw arbitrary-natural composition lengths and proves their finite bound. Independent
review is active with review_relgp_full-independent-20260911; its current kernel
reservation must be released before another kernel starts. Do not port/count this
definition until its independent review and canonical audit finish.
checks/Gates.body.lean and Gates.prototype.lean are authored and UNCHECKED. The
source step function is only called on nonzero sign arguments; G1 is explicit,
G2 is absent. Next: finish root definition review, kernel-check/fix the gates
candidate and assemble the complete lem:gates-nonzero before claiming that lemma.

The unrestricted original shift reversal claim remains separately obstructed by
its reviewed zero-turn counterexample. Generic consumers use the explicit proved
nonzero-turn repair. This does not stop unrelated proof work.

The sole hourly progress watcher PID92953 was confirmed live during this turn;
no duplicate was started. Last scheduled report03:00:09UTC was relayed; next04:00UTC.
Checkpoint updates at03:39UTC report15/132 (11.36%). Original sources, templates,
provenance and ZIPs are unchanged. Sources addendum is available as a sibling.
