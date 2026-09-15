# Specialize the checked formal duplication identity

Checkpoint096 proves the full formal duplication calculation as separate
kernel-checked candidates. Preserve those files and their receipts. The strongest
new formal result is SoftDuplication.farOnlyOutput_duplication in
checks/SoftDuplicationOrdinaryIdentification.body.lean. It covers every duplicate
position for n >= 3, uses the actual ordinary inverse on both sides, and removes
both auxiliary near arrays using the existing complete-output factorization.
It does not assert near independence of individual open sums. Source acceptance
and stronger statement/definition fidelity are still pending.

## Geometric root coefficients

Use the frozen soft_geometric_duplication_data from
checks/SoftGeometricDuplication.body.lean. It gives one positive radius, parent
G1 and the exact parent far-array equality for every core root g. Apply the
formal identity with s = softRootPosition j g, H0 = geometricBoundaryArray P g,
and t = softRootFarData P j g q. The same supplied geometric result proves all
far sign squares and every required off-s square of t; do not add these as new
geometric hypotheses or require a sign at s.

Use softRootFarData_cyclic_attachments from SoftDuplicationNeighbors to rewrite
the actual cyclic predecessor/successor values as the rational casts of
softAttachmentMinus and softAttachmentPlus. Rewrite parent and core rooted
coefficients with the canonical treeCoefficient_farOnly, using the actual G1
proofs for their open sums. This connects the formal output identity to the
tree coefficients without identifying individual auxiliary open sums.

First prove the equation for softParentEdge j g for every core g. Then cover
every parent root other than the soft edge with soft_parent_edges_exhaust and
softParentEdge_injective. Preserve the return edge: softParentEdge j j is the
new occurrence whose collapsed physical edge is the core edge j. Do not treat
the soft root as another admissible case.

## Printed radius and sector statements

Read reference/SM/sm-2-amplitude.tex, thm:A-soft at lines1152 onward and its
specialization at lines1405 onward. Given the positive source epsilon0 from
lem:soft-generic, choose epsilon1 = min epsilon0 delta. Prove positivity, the
upper bound by epsilon0 and the coefficient equation on the entire positive
interval below epsilon1. Generic P supplies its actual G1 component; retain
all printed domains and do not introduce residual-G1 assumptions.

Keep integer tree coefficients and their rational casts explicit. Derive the
same-sign, mixed and loop multipliers from the actual attachment equalities:
both equal -turn P j, opposite attachments, or both equal turn P j. No sector
is omitted. When translating to an integer formula, justify the cast and the
half-sum identity from sign values rather than using division in the integers.

These steps are the next proof work, not already established by checkpoint096.
After actual A-soft assembly, continue the direct all-sector corner soft law,
wall laws, full-cusp/comparison and R/bridge chain. A-soft alone is not the
user's main theorem. Retain the source-fidelity/integration separation and
obtain qualified review without waiting for the author.

## Execution

Root alone runs one Lean kernel/build/audit at a time. Reuse the exact frozen
candidate closure; cyclicPred and cyclicSucc require SoftDuplicationNeighbors.
Preserve failed body, prototype, log and dependency-list bytes before a repair.
Historical bindings refer to their original bytes, not a subsequently repaired
live path. Use the recorded resolution companions for096 dependency repairs.
Keep reference/, accepted map, 327 canonical SM modules and passing candidates
unchanged. Report percentages and checkpoint every work unit; restart exactly
one progress watcher and retain the hourly app automation.
