# R assembly and translation work

These are assigned proof obligations, not author questions. The source package
contains printed arguments, not Lean proofs, and the final aggregate R assembly
was not located in the original RA frame. Historical “PROVED” tags do not close it.
R_ASSEMBLY_SPEC.md gives the exact fibre-sum definitions and assembly obligations.

Use reference/R/RA/R_ATTACHMENT_WARRANTS.md to prove R-LOC-2, R-PAR-v6 and
R-EXTERIOR-1, including all localization and parity clauses. Then:

1. Partition supports by outside independent support Q and available local set.
   Prove exhaustion, disjointness and availability sizes 0, 1 or 3 on both sides.
2. Prove the fibre identities for availability 0 and 1. The supplied core proofs
   assume full availability and do not by themselves cover these cases.
3. At availability 3, prove both complement graph orbits. Generic orbit:
   R_GENERIC_ORBIT_ACTUAL_TABLE.md, R_GENERIC_NONSELECTED_SELECTOR_PROOF.md,
   R_GENERIC_COMMON_TRANSPORT_PROOF.md, R_GENERIC_SELECTED_COUPLE_PROOF.md.
   Extreme orbit: R_EXTREME_PAIR_ZERO_PROOF.md,
   R_EXTREME_SINGLETON_TRANSPORT_PROOF.md,
   R_EXTREME_SELECTED_COUPLE_PROOF.md. Check every support row, including zeros.
4. Prove the common exterior factor without division; handle absent supports,
   empty products, dead selectors, orientations, both directions and arbitrary
   exterior geometry. Sum all fibre identities to prove CV ax:R on its entire
   printed simple/transversal forced-bundle domain.
5. Prove/review B1–B4 in reference/BRIDGE/BRIDGE.md against the supplied SM15;
   derive SM R and discharge the parameter in the final theorem.

All four selected CV literature entries are **theorems to derive**, not permitted
new axioms. The front and HOMFLY bounds can use the selected SM developments;
check the precise domains and normalizations. CV ax:gausscode asserts link
equivalence; polynomial equality alone is not a proof of that stronger statement.
Prove the necessary record/topological equivalence locally, or port its consumers
to the already proved SM polynomial equivalence with a reviewed source-faithful
translation of every consumed conclusion. Record a legitimate interface
replacement explicitly in work/ and retain evidence; never silently accept the
unproved link-equivalence statement. The baseline checker requires the shipped
CV row, so a replacement requires a reviewed scope/checker change, not an alias.

Keep R's actual theorem dependency graph free of R assumptions, CV thm:main,
lawful-quantity/owner-list axioms and SM R-dependent comparison/inherited laws.
The DAG is a guide; add further necessary intermediates locally. Any scope
change is documented and independently reviewed, never an author approval gate.
