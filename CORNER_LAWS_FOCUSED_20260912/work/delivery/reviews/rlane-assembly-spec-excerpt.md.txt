# Concrete specification for the missing R assembly

This specifies the finite-sum assembly task in OPEN_WORK.md. It introduces proof
obligations, not new axioms or a claim that the R proof is already complete. Source
labels are CV `def:X1`, CV `ax:R`, and the warrants in
`R_ATTACHMENT_WARRANTS.md`. The full package keeps them under R/; the focused
package keeps them under reference/R/.

Fix the two nearby generic sides of a source simple RIII event. First prove
R-LOC-2 and use its carrying-edge labels to identify the crossing sets with one
finite set V. Let T be its three local crossings and W the complement. R-LOC-2
says only the three internal pairs of T toggle. Consequently both graphs induce
the same graph on W and have the same adjacencies between W and T.

For each independent outside support Q in W, define its availability set by

\[
\mathcal A(Q)=\{t\in T:\text{no element of }Q\text{ is adjacent to }t\}.
\]
(1)

It is the same on both sides because the W-to-T adjacencies are unchanged.
Every independent support S on either side decomposes uniquely into Q = S ∩ W
and J = S ∩ T. Q is independent in the outside graph. J is independent in the
local graph and belongs to the availability set because independence forbids
every Q-to-J edge. Conversely, these three conditions imply that Q ∪ J is
independent: its possible edges are outside, inside T, or between the two parts,
and the respective conditions exclude all three kinds. This proves a bijection
of supports, not merely an injection or a list of examples.

Let F±(S) denote the **complete** summand of CV `def:X1` at S on that side,
including the selector and every carrier coefficient with the printed empty
conventions. Define each fibre sum by

\[
\Phi_\pm(Q)=\sum_{J\in\operatorname{Ind}(G_\pm[\mathcal A(Q)])}
F_\pm(Q\cup J).
\]
(2)

The finite bijection just established partitions the exact state sum, so

\[
X_1(P_\pm)=\sum_{Q\in\operatorname{Ind}(G[W])}\Phi_\pm(Q).
\]
(3)

Prove R-PAR-v6(P1) before using availability sizes. It says each outside crossing
is adjacent to either zero or two members of T. The excluded set T minus A(Q)
is a union of these zero- or two-element sets. Such a union has size zero, two
or three: if nonempty it contains one entire two-element set and it is contained
in the three-element T. Thus availability has size three, one or zero.

The local proof task, for each such Q, is

\[
\Phi_+(Q)=\Phi_-(Q).
\]
(4)

At availability zero or one the local supports themselves correspond, but that
does **not** prove their summands agree. Prove the required carrier/record,
selector, rotation and coefficient transport. These cases cannot be omitted
because the four core proofs assume full availability.

At availability three, assemble the supplied generic and extreme orbit tables,
nonselected/zero-row results, common transports and selected-couple identities
listed in OPEN_WORK.md. Check that every row of (2) occurs with the correct sign
and multiplicity on each side. Keep the exterior factor throughout; no division
by a possibly zero selector, row, or exterior coefficient is allowed.

Finally sum the proved identities (4) over the same finite outside-support set
in (3). Equality is preserved by finite summation, giving exactly CV ax:R. Review
that all source event-domain clauses survived the localization and assembly.
Apply the independently proved bridge afterwards. A missing local identity stays
a proof obligation; historical status tags or the fibre partition do not prove it.
