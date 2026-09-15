# Starting-row gate products: next bounded implementation

Read-only design by `/root/review_mark_transport`, 2026-09-12. Source:
`reference/SM/sm-2-amplitude.tex` lines 1280–1302, with the array prescriptions
at 1224–1266. No Lean was written or executed for this plan. Proposed names
below are **not proved APIs**. StartingChildren35 passed root second35266;
StartingChildFactors7 is still being checked as root first51575.

Fix `I.left = A s`, `B s < I.right`, and any complete core cut set
`C : BoundaryCutSet (collapseInterval s I hI)`. Write `J` for that core interval,
`Y0 = J.right`, `X = (startingFirstChild s I hI C).right`, and `S0`, `S1` for
`startingCutSet ... 0`, `startingCutSet ... 1`. Row order is fixed:
row0 has local cuts `{A}`; row1 has `{A,B}`. `X` is the first boundary after
the core left endpoint, including the right endpoint when C is unary.
Do not require X to be an interior cut.

1. **Enumerate the actual interior cuts.** Prove
   `S0.interior.val = C.interior.val.image (old s)` and
   `S1.interior.val = insert (B s) (C.interior.val.image (old s))`. (1)
   Use `startingCutSet_zero_cuts`, `startingCutSet_one_insert_B`, and the
   canonical definition `BoundaryCutSet.interior` (erase both endpoints).
   The endpoint facts are `old s J.left = A s`, `old s Y0 = I.right`, and
   `old_ne_B`. Every core interior k satisfies `s < k < Y0`; hence
   `old s k = startingTailEmbedding s k` and `B s < old s k`.
   Build `startingInteriorZeroEquiv : CInterior ≃ S0Interior` with k ↦ old k,
   and `startingInteriorOneEquiv : Unit ⊕ CInterior ≃ S1Interior`, sending
   the Unit branch to B and the other branch to old k. Derive bijectivity
   from (1), using collapse as the inverse off B. No supplied correspondence.

2. **Identify actual triples before evaluating arrays.** For a core interior
   cut x, prove these four identities using `OrderedBoundaryTransport.triple`:
   row0 near/far are the old images of `C.nearAtCut x`/`C.farAtCut x`;
   row1 near is the tail image of `C.nearAtCut x`, while row1 far is the
   **old image** of `C.farAtCut x`. (2)
   For near endpoints, map `C.nearLeftInterval x` and `C.nearRightInterval x`
   using `consecutive_ordered_image_iff` (row0) or
   `starting_one_mapped_consecutive` (row1). Apply the frozen
   `nearAtCut_lower_eq_of_consecutive` and `nearAtCut_upper_eq_of_consecutive`;
   obtain the middle from `nearAtCut_middle`. For far endpoints, use
   `farAtCut_lower/middle/upper` directly. In particular, S1's full interval
   remains I with left endpoint A: mapping its far triple wholly by the
   tail section would incorrectly replace this endpoint by B.

3. **Evaluate inherited gates for arbitrary lifted arrays.** Use arbitrary
   `D0 H0 : TripleArray n ℚ` and `tD tH : Fin n → ℚ`, then parent arrays
   `tripleLift s D0 tD`, `tripleLift s H0 tH`. Add small helpers
   `tailTriple_plain` and `collapseTriple_tailTriple`: the tail image omits A
   because it is `(A s).succAbove`, and `collapse_startingTail` recovers each
   position. `tripleLift_plain` therefore evaluates every inherited row1
   near triple to D0 at its exact core triple. Old images use
   `tripleLift_oldTriple` (identify `OrderedBoundaryTransport.triple
   (startingOldEmbedding s)` with `oldTriple` by `triple_ext`). Both rows'
   inherited far values equal H0 at the core far triple. This proves all
   inherited gate equalities, including the near gate whose lower neighbor
   changes from A to B; no auxiliary near-array invariance is assumed.

4. **Identify the new gate at B.** Its actual near triple has positions
   `(A, B, old s X)`; its actual far triple has `(A, B, I.right)`. (3)
   The preceding child is `starting_one_duplicate_consecutive`; the following
   child is the tail image of `startingFirstChild`, by
   `starting_one_mapped_consecutive` and `starting_first_one_endpoints`.
   Use the same neighbor lemmas, then `tripleLift_lower` and `collapse_old`.
   The resulting gate is `(tD X - tH Y0) / 2`. (4)
   This also covers a unary core: X=Y0, with no inherited gates.

5. **Reindex the complete products.** Let G(S;D,H) denote precisely the first
   finite product in `BoundaryCutSet.nearFarSummand`, over actual interior
   cuts. Proposed final APIs `starting_zero_gate_product` and
   `starting_one_gate_product` should state
   `G(S0;lift D0 tD,lift H0 tH) = G(C;D0,H0)` and
   `G(S1;lift D0 tD,lift H0 tH) = ((tD X-tH Y0)/2)*G(C;D0,H0)`. (5)
   Prove with `Fintype.prod_equiv`, `Fintype.prod_sum_type`, a proof-local
   Unit binder, and pointwise identities above. No division by a gate or
   child value, and no nonempty-interior premise. Existing
   `OrderedBoundaryTransport.cutSet_toComposition` and
   `composition_nearTriple/farTriple` are an alternative row0 route, but
   the actual-cut route avoids transporting dependent sorted indices.

Specialize D0 to `coreNear s t` and tD=t only when assembling the complete
summand with the separately proved child products. Ordinary far data uses
tH=t; root data uses `(-H0,-t)` and the frozen `tripleLift_neg`, giving the
new root gate `(t X+t Y0)/2`. (6) Combine the two rows using
`sum_startingRows`; only then apply the source scalar cancellation.

Scope limit: this plan proves no gate theorem, weighted transform, inverse
identification, geometric correspondence, or A-soft theorem. The source's
one-leaf endpoint-neighbor condition and the other endpoint/spanning cases
remain separate. Source acceptance increment 0; stronger fidelity approval
false; canonical integration false. Parent source acceptance remains
19/132 (14.39%); original 38/191; expanded 39/192; final 0/8.
