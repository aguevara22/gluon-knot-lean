import SM.PolynomialBlock
import SM.ZeroLink
import SM.Stack
import CV.Axioms
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Skeleton B — marked products block (mp:join, mp:lowest, mp:blocks, lem:homflyrows)

Architect B (reuse-first), 2026-09-14.  Plan of record: work/drafts/markedproducts/PLAN_B.md.
Fixed statements: work/drafts/MarkedProducts_statement.lean (sections A–E and the four bundles are
copied below BYTE-IDENTICALLY; only the four row theorems carry proofs from the chain).

Route in one paragraph.
* mp:join is `P_addFree` (SM/PolynomialBlock.lean §5) done twice: a record-level `(N, b)` induction
  (`skein_induction_based`) on ONE factor with the partner diagram and the join quantified inside the
  predicate.  Inner induction `join_core_right_underFirst` (partner UNDER-first at a marked-first based
  order), outer `join_core` (the other factor in the `inl` slot — `joinRecord_comm` puts it there, so
  only the `inl` versions of the switch/smoothing commutations are needed).  Initialisation: a
  marked-first based order of each factor joins to an UNDER-first based order of the join record
  (`RBasing.join`, `rUnderFirst_join`); step: `joinRecord_switch_inl`, `joinRecord_smooth_inl`
  (the record-level "recombination at disjoint ends", built from `firstReturn_mul_swap` (SM/Stack.lean)
  generalised to an unretained swap point, `lastKeep`), then `solvedR_of_skein`/`solvedR_mul_left`.
* mp:lowest is a corollary of `SM.stack` (singleton blocks), `SM.zero_link.over_constant`,
  `P_support`, `P_knot_support` and `CV.zRow_zero_mul_of_inSupportM_one`: the weight
  `a^{2Λ} [z^{1−c}] P_D` is invariant under a mixed switch (`lowest_switch_step`), an induction on the
  finset of "wrong" mixed crossings (`wrongCrossings`) reaches `BlockOrdered D id`, where
  `stack_formula` + `zRow_delta_pow_mul` give the value and `over_constant` gives `Λ = 0`.
* lem:homflyrows: `connected_sum` = `join_value` + `P_eq_homfly` + `homfly_descent`; `split_union` =
  `SM.stack.split_union` + `restrict_congr` + `presentations`; `two_component_row` =
  `SM.lowest.two_component_row` + `CV.zRow_zero_mul_of_inSupportM_one`.
* mp:blocks: `writhe_additive` and `sign_preserved` are pure record bookkeeping (blocks partition the
  crossings; `JoinForest` induction with crossing equivalences); `product` = `realizes` + `JoinForest`
  induction with `join_value` + `presentations`.  `realizes` (D9's tracked sub-obligation) is
  ANALYSED only: its chain is stated and left `sorry` — and the analysis shows that NO clean-join
  construction is needed: the root node is the supplied actual diagram (`BlockSupply.actual`), every
  internal node is realized by smoothing away the other blocks inside an actual realization
  (`isRealizable_restrictCrossings_of_gapContiguous`, accepted geometry only), the leaves are the
  supplied `C H`; the only new geometry is `exists_markedInterval_of_mark` (a clean disc around a
  point of a gap).  Combinatorics: `restrictCrossings_join_decomp`; assembly:
  `exists_joinForest_of_realizable`.

Status: compiles with `lake env lean`; every `sorry` is a chain lemma listed in PLAN_B.md with its unit. -/

namespace SM

open SM.Link Classical

namespace Link

/-! ## A. `ℤ[a^{±1}]` monomials for the `[z^k]` rows -/

/-- `a^n ∈ ℤ[a^{±1}]`: Mathlib's Laurent monomial `LaurentPolynomial.T n` in the row ring of `zRow`
(mp:lowest 1588-1591 "[z^{1−c}] P_D = a^{−2Λ}(a − a⁻¹)^{c−1} ∏ [z^0] P_{D_i}": both sides are
Laurent polynomials in `a`). -/
noncomputable abbrev aPow (n : ℤ) : LaurentPolynomial ℤ := LaurentPolynomial.T n

/-! ## B. Marked diagrams and the clean marked join (sm-3:1362-1385, 1427-1437) -/

/-- The occurrence `v` names the gap of the arc `I` (sm-3:1375 "at their marked gaps"): `v` is the
crossing occurrence of the component of `I` met last before the entering end `I.start` — no
occurrence of that component lies cyclically strictly between `v` and `I.start`.  When `I` carries no
occurrence, `I` lies in the cyclic gap from `v` to its forward successor `D.nextVisit v`. -/
def Diagram.IsGapOf (D : Diagram) (I : D.Γ.Arc) (v : D.Γ.Visit) : Prop :=
  D.compOf v = I.i ∧
    ∀ w : D.Γ.Visit, D.compOf w = I.i →
      ¬ cycBetween (D.visitCoord v) (D.visitCoord w) (traversalKey I.start)

/-- "A marked diagram is a nonempty actual diagram with a specified closed nonsingular oriented
interval `I` on one component; `I` contains no crossing and is contained in a clean disc"
(sm-3:1363-1365): the diagram `D`, the interval `I` (an `Arc` of `D`, `IsMarkedInterval D I` = the
accepted rendering of "closed nonsingular oriented interval on one component, containing no crossing,
contained in a clean disc", SM/LinkMoves.lean:1107), and the mark of its record that `I` determines
(design decision D9): the marked component `μ.comp = I.i` and the marked gap `μ.gap` — the occurrence
just before `I` (`Diagram.IsGapOf`), or `none` when the marked component is crossing-free ("an
arbitrary crossing-free marked component", 1431-1432).  The rows below read only the record mark
`μ` ("Its finite data are precise", 1374-1377; realizations "are compared only by Lemma
lc:presentations", 1420-1421); the interval is carried so that the rows quantify over exactly the
printed marked diagrams. -/
structure MarkedDiagram where
  /-- the nonempty actual diagram -/
  D : Diagram
  /-- the specified closed nonsingular oriented interval on one component -/
  I : D.Γ.Arc
  /-- "`I` contains no crossing and is contained in a clean disc" -/
  marked : IsMarkedInterval D I
  /-- the record mark determined by `I`: its component and its gap -/
  μ : D.record.Mark
  /-- the mark's component is the component of `I` -/
  comp_eq : I.i = μ.comp
  /-- the mark's gap is the occurrence just before `I` (none exactly when the component is crossing-free) -/
  gap_iff : ∀ v, μ.gap = some v ↔ D.IsGapOf I v

/-- "any actual clean marked join `J(A,B)` just specified" (sm-3:1428-1429): an actual diagram whose
named record is exactly the printed finite data of the marked join — "concatenate the marked
component cycles at their marked gaps, retain every other component, and keep exactly all old crossing
pairings, bits and signs" (1375-1377), i.e. the accepted record-level join `Record.joinRecord A.μ B.μ`
(SM/LinkRecord.lean:1513).  "The old `A` presentation, the new one and any other actual clean
realization are compared only by Lemma lc:presentations" (1420-1421). -/
def IsCleanMarkedJoin (A B : MarkedDiagram) (J : Diagram) : Prop :=
  Nonempty (RecordIso J.record (Record.joinRecord A.μ B.μ))

/-- Sanity ("The component number is `c(A)+c(B)−1`", sm-3:1377-1378): a clean marked join has
`c(A)+c(B)−1` components. -/
theorem IsCleanMarkedJoin.componentCount {A B : MarkedDiagram} {J : Diagram}
    (h : IsCleanMarkedJoin A B J) :
    J.componentCount = A.D.componentCount + B.D.componentCount - 1 := by
  obtain ⟨ι⟩ := h
  have h1 := ι.componentCount_eq
  rw [Diagram.record_componentCount, Record.componentCount_joinRecord,
    Diagram.record_componentCount, Diagram.record_componentCount] at h1
  exact h1

/-- Sanity ("keep exactly all old crossing pairings, bits and signs", sm-3:1376-1377): the writhe of
a clean marked join is the sum of the writhes. -/
theorem IsCleanMarkedJoin.writhe {A B : MarkedDiagram} {J : Diagram}
    (h : IsCleanMarkedJoin A B J) : J.writhe = A.D.writhe + B.D.writhe := by
  obtain ⟨ι⟩ := h
  have h1 := ι.writhe_eq
  rw [Diagram.record_writhe, Record.writhe_joinRecord, Diagram.record_writhe,
    Diagram.record_writhe] at h1
  exact h1

/-! ## C. Knot restrictions and the mixed linking sums (mp:lowest, sm-3:1582-1591) -/

namespace Diagram

/-- "their actual knot restrictions `D_i`" (sm-3:1584): the restriction of `D` to the single
component `i` (all its self crossings, no mixed crossing), `D.restrict {i}` of SM/LinkDiagram.lean
(mp:stack's block restriction with a singleton block). -/
noncomputable def knotRestrict (D : Diagram) (i : Fin D.Γ.c) : Diagram :=
  D.restrict {i} (Finset.singleton_nonempty i)

/-- Sanity: a knot restriction has one component ("the two tagged restrictions are intrinsic knot
diagrams", sm-3:1594-1595). -/
theorem knotRestrict_componentCount (D : Diagram) (i : Fin D.Γ.c) :
    (D.knotRestrict i).componentCount = 1 := by
  unfold knotRestrict
  rw [restrict_componentCount]
  simp

end Diagram

/-- `2 ℓ_ij`: "ℓ_ij = ½ Σ σ(x) using ALL mixed crossings between the original components `i, j`"
(sm-3:1585-1586), doubled — the accepted `mixedSignSum D i j` of mp:zero-link (SM/ZeroLink.lean:31),
the sum of the decorated signs over every mixed crossing between `i` and `j` in the original common
diagram ("`ℓ_12` is computed in their original common diagram", 1595-1596).  Its half is an integer
by mp:zero-link; the rows only use `2ℓ_ij`. -/
noncomputable def twoLinking (D : Diagram) (i j : Fin D.Γ.c) : ℤ := mixedSignSum D i j

/-- `2 Λ`: "put `Λ = Σ_{i<j} ℓ_ij`" (sm-3:1586), doubled: the total mixed sign sum over the unordered
pairs of components. -/
noncomputable def twoLambda (D : Diagram) : ℤ :=
  ∑ i : Fin D.Γ.c, ∑ j : Fin D.Γ.c, if i < j then twoLinking D i j else 0

/-! ## D. Interlacement of a record, its blocks, and the restricted named cyclic record
(mp:blocks, sm-3:1624-1636) -/

namespace Record

variable (ρ : Record)

/-- The number of forward `succ`-steps from the occurrence `v` to the occurrence `w` (the least
`n` with `s^n v = w`; `0` when `w` is not on the circle of `v`).  On a one-circle record every `w` is
reached. -/
noncomputable def steps (v w : ρ.M) : ℕ :=
  if h : ∃ n : ℕ, (ρ.succ ^ n) v = w then Nat.find h else 0

/-- Sanity: no step from an occurrence to itself. -/
theorem steps_self (v : ρ.M) : ρ.steps v v = 0 := by
  unfold steps
  split_ifs with h
  · exact Nat.le_zero.mp (Nat.find_min' h (by simp))
  · rfl

/-- `w` lies strictly inside the open forward arc from `v` to `u` on the circle of `v`. -/
def ArcBetween (v w u : ρ.M) : Prop := 0 < ρ.steps v w ∧ ρ.steps v w < ρ.steps v u

/-- Two chords (crossings) of a one-circle record interlace: their endpoints alternate around the
circle, i.e. exactly one of the two occurrences `w, τw` of `y` lies on the open arc from an occurrence
`v` of `x` to its partner `τv` (mp:blocks proof, sm-3:1638-1645: "Cutting the circle at the endpoints
of `b` gives two open intervals ... Such chords cannot alternate").  Stated for every choice of the
occurrences `v ∈ x`, `w ∈ y`; on a one-circle record the four choices agree (the other occurrence
lies on the complementary arc), and on a different circle nothing interlaces. -/
def Interlaces (x y : ρ.Crossing) : Prop :=
  x ≠ y ∧ ∀ v ∈ x.1, ∀ w ∈ y.1,
    Xor (ρ.ArcBetween v w (ρ.pair v)) (ρ.ArcBetween v (ρ.pair w) (ρ.pair v))

/-- "its interlacement graph" (sm-3:1626): the simple graph on the crossings of the record whose
edges are the interlacing pairs (`SimpleGraph.fromRel` symmetrises and removes loops; interlacement
is symmetric and irreflexive on a one-circle record, so nothing is added). -/
def interlacementGraph : SimpleGraph ρ.Crossing := SimpleGraph.fromRel ρ.Interlaces

/-- The blocks are finitely many (finitely many crossings). -/
noncomputable instance instFintypeInterlacementBlocks :
    Fintype ρ.interlacementGraph.ConnectedComponent := Fintype.ofFinite _

/-- Retained occurrences of a crossing subset `S`: both occurrences of a crossing of `S`. -/
def CrossKeep (S : Set ρ.Crossing) (v : ρ.M) : Prop := ρ.crossingOf v ∈ S

theorem crossKeep_pair_iff (S : Set ρ.Crossing) (v : ρ.M) :
    ρ.CrossKeep S (ρ.pair v) ↔ ρ.CrossKeep S v := by
  unfold CrossKeep
  rw [ρ.crossingOf_pair]

/-- Membership in the crossing subset is decided classically. -/
noncomputable instance instDecidablePredCrossKeep (S : Set ρ.Crossing) :
    DecidablePred (ρ.CrossKeep S) := Classical.decPred _

/-- "that restricted named cyclic record" (sm-3:1628): the record of a crossing subset `S` of `ρ` —
the same parametrizing circle(s), the occurrences of the crossings in `S`, the first-return successor
("the restricted named cyclic record" of the block: its occurrences in their inherited cyclic order),
and the old pairing, bits and signs.  This is the accepted `Record.restrict` pattern
(SM/LinkRecord.lean:1144) with the retained set chosen by crossings instead of by components. -/
noncomputable def restrictCrossings (S : Set ρ.Crossing) : Record where
  comps := ρ.comps
  M := {v : ρ.M // ρ.CrossKeep S v}
  comp v := ρ.comp v.1
  succ := firstReturn ρ.succ (ρ.CrossKeep S)
  pair := ρ.pair.subtypePerm (ρ.crossKeep_pair_iff S)
  isOver v := ρ.isOver v.1
  sgn v := ρ.sgn v.1
  succ_comp v := by
    show ρ.comp (firstReturn ρ.succ (ρ.CrossKeep S) v).1 = ρ.comp v.1
    rw [firstReturn_apply, ρ.comp_pow]
  succ_cycle v w h := firstReturn_sameCycle_of_sameCycle _ _ (ρ.succ_cycle _ _ h)
  pair_ne v h := ρ.pair_ne v.1 (congrArg Subtype.val h)
  pair_invol v := Subtype.ext (ρ.pair_invol v.1)
  bit_pair v := ρ.bit_pair v.1
  sgn_pair v := ρ.sgn_pair v.1
  sgn_ne v := ρ.sgn_ne v.1

@[simp] theorem restrictCrossings_comps (S : Set ρ.Crossing) :
    (ρ.restrictCrossings S).comps = ρ.comps := rfl
@[simp] theorem restrictCrossings_M (S : Set ρ.Crossing) :
    (ρ.restrictCrossings S).M = {v : ρ.M // ρ.CrossKeep S v} := rfl
@[simp] theorem restrictCrossings_sgn (S : Set ρ.Crossing) (v : (ρ.restrictCrossings S).M) :
    (ρ.restrictCrossings S).sgn v = ρ.sgn v.1 := rfl

/-- Sanity: the restricted record keeps the circle count ("one-circle"). -/
theorem componentCount_restrictCrossings (S : Set ρ.Crossing) :
    (ρ.restrictCrossings S).componentCount = ρ.componentCount := rfl

end Record

/-- The hypotheses of mp:blocks (sm-3:1625-1628): "Let an actual oriented one-circle decorated record
have a nonempty crossing set, partitioned into the connected components of its interlacement graph.
Suppose that for every component `H` an actual retained diagram `C_H` with exactly that restricted
named cyclic record is supplied." -/
structure BlockSupply (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram) : Prop where
  /-- "an actual ... record": the record of some actual diagram (`IsRealizable`,
  SM/LinkDiagramRecord.lean:718).  Redundant once the conclusion `realizes` holds, but printed. -/
  actual : IsRealizable ρ
  /-- "oriented one-circle decorated record" -/
  one_circle : ρ.componentCount = 1
  /-- "have a nonempty crossing set" -/
  nonempty : Nonempty ρ.M
  /-- "for every component `H` an actual retained diagram `C_H` with exactly that restricted named
  cyclic record is supplied" -/
  supplied : ∀ H, Nonempty (RecordIso (C H).record (ρ.restrictCrossings H.supp))

/-- "a finite succession of clean marked joins of these actual diagrams" (sm-3:1629-1630): the
diagrams obtainable from the supplied family `C` by clean marked joins, each supplied diagram used
exactly once — `JoinForest C S J` says `J` is built from the leaves `C i`, `i ∈ S`.  A leaf is a
supplied diagram itself ("Every leaf was an already supplied actual diagram", 1676); a node is a clean
marked join (`IsCleanMarkedJoin`) of two forests on disjoint index sets, with any marked intervals. -/
inductive JoinForest {ι : Type} (C : ι → Diagram) : Set ι → Diagram → Prop
  | leaf (i : ι) : JoinForest C {i} (C i)
  | join {S₁ S₂ : Set ι} (A B : MarkedDiagram) {J : Diagram}
      (hA : JoinForest C S₁ A.D) (hB : JoinForest C S₂ B.D) (hdisj : Disjoint S₁ S₂)
      (hJ : IsCleanMarkedJoin A B J) : JoinForest C (S₁ ∪ S₂) J

/-! ## E. Split unions (lem:homflyrows, sm-4:232-233, proof 245-247) -/

/-- "K ⊔ J", the split union of two diagrams (lem:homflyrows proof, sm-4:245-247: "choose
representatives with disjoint page images. Theorem mp:stack, with two one-component blocks and no
mixed crossings"): `D` is partitioned into two nonempty component blocks `B`, `Bᶜ` with no crossing
between the blocks (mp:stack 1502-1503 "A crossing-free disjoint union is the special case with no
crossings between blocks"; for a generic polygonal shadow this is "disjoint page images"), and the two
block restrictions have the named records of `K` and `J`. -/
def IsSplitUnion (K J D : Diagram) : Prop :=
  ∃ (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) (hB' : Bᶜ.Nonempty),
    (∀ (x : D.Γ.Crossing), ∀ s ∈ x.val, ∀ t ∈ x.val, (s.1 ∈ B ↔ t.1 ∈ B)) ∧
    Nonempty (RecordIso (D.restrict B hB).record K.record) ∧
    Nonempty (RecordIso (D.restrict Bᶜ hB').record J.record)

end Link

/-! ## F. The four bundles -/

/-- mp:join (sm-3:1427-1437) as printed: "For two nonempty actual marked diagrams and any actual clean
marked join `J(A,B)` just specified, `P_{J(A,B)} = P_A P_B` (mp:join-value). This includes
smoothing-created multi-component factors and an arbitrary crossing-free marked component." -/
structure JoinData : Prop where
  /-- eq. mp:join-value: "For two nonempty actual marked diagrams and any actual clean marked join
  `J(A,B)` just specified, `P_{J(A,B)} = P_A P_B`." -/
  join_value : ∀ (A B : MarkedDiagram) (J : Diagram), IsCleanMarkedJoin A B J →
    P J = P A.D * P B.D
  /-- "This includes smoothing-created multi-component factors": the identity with a factor of more
  than one component (no hypothesis on the component counts is made in `join_value`; this field
  records the printed inclusion). -/
  multi_component_factors : ∀ (A B : MarkedDiagram) (J : Diagram),
    (1 < A.D.componentCount ∨ 1 < B.D.componentCount) → IsCleanMarkedJoin A B J →
    P J = P A.D * P B.D
  /-- "and an arbitrary crossing-free marked component": the identity when a mark sits on a
  crossing-free component (`gap = none`). -/
  crossing_free_marked_component : ∀ (A B : MarkedDiagram) (J : Diagram),
    (A.μ.gap = none ∨ B.μ.gap = none) → IsCleanMarkedJoin A B J →
    P J = P A.D * P B.D

/-- mp:lowest (sm-3:1582-1596) as printed: "Let `D` be an actual diagram with `c ≥ 1` tagged oriented
components, and let `D_i` be their actual knot restrictions. Define `ℓ_ij = ½ Σ σ(x)` using ALL mixed
crossings between the original components `i, j`, and put `Λ = Σ_{i<j} ℓ_ij`. Then
`[z^{1−c}] P_D = a^{−2Λ} (a − a⁻¹)^{c−1} ∏_{i=1}^c [z^0] P_{D_i}` (mp:lowest-value). For `c = 2` this
is the two-component mixed row; the two tagged restrictions are intrinsic knot diagrams while `ℓ_12`
is computed in their original common diagram." -/
structure LowestData : Prop where
  /-- eq. mp:lowest-value: `[z^{1−c}] P_D = a^{−2Λ}(a − a⁻¹)^{c−1} ∏_{i=1}^c [z^0] P_{D_i}`, an identity in
  `ℤ[a^{±1}]` (`zRow`), with `a^{−2Λ} = aPow (−twoLambda D)`. -/
  lowest_value : ∀ D : Diagram,
    zRow (1 - (D.componentCount : ℤ)) (P D) =
      aPow (-(twoLambda D)) * (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) *
        ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i))
  /-- "For `c = 2` this is the two-component mixed row; the two tagged restrictions are intrinsic knot
  diagrams while `ℓ_12` is computed in their original common diagram":
  `[z^{−1}] P_D = a^{−2ℓ_12}(a − a⁻¹) [z^0] P_{D_1} [z^0] P_{D_2}` for the two components `i ≠ j`. -/
  two_component_row : ∀ (D : Diagram) (i j : Fin D.Γ.c), D.componentCount = 2 → i ≠ j →
    zRow (-1) (P D) =
      aPow (-(twoLinking D i j)) * (aPow 1 - aPow (-1)) *
        (zRow 0 (P (D.knotRestrict i)) * zRow 0 (P (D.knotRestrict j)))

/-- mp:blocks (sm-3:1624-1636) as printed: "Let an actual oriented one-circle decorated record have a
nonempty crossing set, partitioned into the connected components of its interlacement graph. Suppose
that for every component `H` an actual retained diagram `C_H` with exactly that restricted named cyclic
record is supplied. Then a finite succession of clean marked joins of these actual diagrams realizes
the full record, and every actual diagram with that full record has polynomial `∏_H P_{C_H}`. The
joins preserve the sign of every crossing and the writhe is the sum of the writhes of `C_H`."  The
hypotheses are `BlockSupply ρ C`. -/
structure BlocksData : Prop where
  /-- "Then a finite succession of clean marked joins of these actual diagrams realizes the full
  record": some `J` built by `JoinForest` from every supplied `C_H` (each used once) has the named
  record `ρ`. -/
  realizes : ∀ (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram),
    BlockSupply ρ C → ∃ J : Diagram, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record ρ)
  /-- "and every actual diagram with that full record has polynomial `∏_H P_{C_H}`." -/
  product : ∀ (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram),
    BlockSupply ρ C → ∀ D : Diagram, Nonempty (RecordIso D.record ρ) → P D = ∏ H, P (C H)
  /-- "The joins preserve the sign of every crossing": in every succession of clean marked joins of
  the supplied diagrams, each crossing of the result is one crossing of one supplied `C_H`, with its
  sign (proof 1681-1682: "Every old crossing is present once, with its old sign"). -/
  sign_preserved : ∀ (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram),
    BlockSupply ρ C → ∀ J : Diagram, JoinForest C Set.univ J →
      ∃ φ : (Σ H : ρ.interlacementGraph.ConnectedComponent, (C H).Γ.Crossing) ≃ J.Γ.Crossing,
        ∀ q, J.sign (φ q) = (C q.1).sign q.2
  /-- "and the writhe is the sum of the writhes of `C_H`" (for every actual diagram with the full
  record). -/
  writhe_additive : ∀ (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram),
    BlockSupply ρ C → ∀ D : Diagram, Nonempty (RecordIso D.record ρ) →
      D.writhe = ∑ H, (C H).writhe

/-- lem:homflyrows (sm-4:230-238) as printed: "For oriented knots `K, J`, `H_{K#J} = H_K H_J` and
`H_{K⊔J} = (a − a⁻¹)/z · H_K H_J`. For a two-component oriented link diagram `D = D_1 ∪ D_2` with
linking number `lk`, `[z^{−1}] H_D = (a − a⁻¹) a^{−2 lk} [z^0](H_{D_1} H_{D_2})`."  `H` is the
lit:homfly polynomial `homfly`; knots are `LinkEquiv` classes of one-component diagrams, `K # J` any
clean marked join of marked representatives, `K ⊔ J` any split union of representatives,
`2·lk = twoLinking D i j`.  The well-definedness of `K # J` as a class is not claimed (design D9). -/
structure HomflyRowsData : Prop where
  /-- "For oriented knots `K, J`, `H_{K#J} = H_K H_J`": the knots are the `LinkEquiv` classes of the
  one-component diagrams `K, J` ("the oriented link presented by D", lit:homfly), `H_K = homfly K`,
  and `K # J` is any clean marked join `D` of marked representatives `K' ~ K`, `J' ~ J` ("Choose actual
  knot diagrams for `K, J` with clean marked intervals. The clean joining construction ... gives a
  diagram of their ordinary oriented connected sum", proof 240-242). -/
  connected_sum : ∀ (K J : Diagram), K.componentCount = 1 → J.componentCount = 1 →
    ∀ (K' J' : MarkedDiagram) (D : Diagram), LinkEquiv K K'.D → LinkEquiv J J'.D →
      IsCleanMarkedJoin K' J' D → homfly D = homfly K * homfly J
  /-- "and `H_{K⊔J} = (a − a⁻¹)/z · H_K H_J`": `K ⊔ J` is any split union `D` of representatives
  `K' ~ K`, `J' ~ J` ("choose representatives with disjoint page images", proof 245-246);
  `(a − a⁻¹)/z = δ = R.delta`. -/
  split_union : ∀ (K J : Diagram), K.componentCount = 1 → J.componentCount = 1 →
    ∀ (K' J' D : Diagram), LinkEquiv K K' → LinkEquiv J J' → IsSplitUnion K' J' D →
      homfly D = R.delta * (homfly K * homfly J)
  /-- "For a two-component oriented link diagram `D = D_1 ∪ D_2` with linking number `lk`,
  `[z^{−1}] H_D = (a − a⁻¹) a^{−2 lk} [z^0](H_{D_1} H_{D_2})`", `D_1, D_2` the two knot restrictions
  and `2 lk` the mixed sign sum of the original diagram; the `[z^0]` is of the PRODUCT, as printed. -/
  two_component_row : ∀ (D : Diagram) (i j : Fin D.Γ.c), D.componentCount = 2 → i ≠ j →
    zRow (-1) (homfly D) =
      (aPow 1 - aPow (-1)) * aPow (-(twoLinking D i j)) *
        zRow 0 (homfly (D.knotRestrict i) * homfly (D.knotRestrict j))


/-! ## G. Architect B chain — record level (marks under switch and smoothing, the join basing) -/

namespace Link

namespace Record

variable {ρ : Record}

/-! ### G.1 Marks survive a switch (same circles, occurrences and `comp`; sm-3:1455-1457 "Switching it
gives `A^sw` with the same component number, same marked interval") -/

/-- The same mark on the switched record (definitional: `switch` changes only bits and signs). -/
def Mark.switch (μ : ρ.Mark) (x : ρ.M) : (ρ.switch x).Mark :=
  ⟨μ.comp, μ.gap, μ.gap_comp, μ.gap_none⟩

@[simp] theorem Mark.switch_comp (μ : ρ.Mark) (x : ρ.M) : (μ.switch x).comp = μ.comp := rfl
@[simp] theorem Mark.switch_gap (μ : ρ.Mark) (x : ρ.M) : (μ.switch x).gap = μ.gap := rfl

/-- Transport along the identity isomorphism is the identity on marks. -/
theorem Mark.map_refl (μ : ρ.Mark) : μ.map (RecordIso.refl ρ) = μ := by
  obtain ⟨c, g, hc, hn⟩ := μ
  cases g <;> rfl

/-- "In `J(A,B)` it is precisely the corresponding crossing switch" (sm-3:1457-1458): switching the
join at an `A`-occurrence is the join of the switched `A` (identity on circles and occurrences; the
bits and signs agree by `Sum` case analysis on `switch_isOver`/`switch_sgn`). -/
theorem joinRecord_switch_inl {ρ₁ ρ₂ : Record} (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (a : ρ₁.M) :
    Nonempty (RecordIso ((joinRecord μ₁ μ₂).switch (Sum.inl a)) (joinRecord (μ₁.switch a) μ₂)) :=
  ⟨{ e := Equiv.refl _
     Φ := Equiv.refl _
     comp_eq := fun _ => rfl
     succ_eq := fun _ => rfl
     pair_eq := fun _ => rfl
     bit_eq := fun v => by
       rcases v with b | b
       · show (ρ₁.switch a).isOver b =
           (if Sum.inl b ∈ ({Sum.inl a, Sum.inl (ρ₁.pair a)} : Finset (ρ₁.M ⊕ ρ₂.M))
             then !ρ₁.isOver b else ρ₁.isOver b)
         rw [switch_isOver]
         simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]
       · show ρ₂.isOver b =
           (if Sum.inr b ∈ ({Sum.inl a, Sum.inl (ρ₁.pair a)} : Finset (ρ₁.M ⊕ ρ₂.M))
             then !ρ₂.isOver b else ρ₂.isOver b)
         simp
     sgn_eq := fun v => by
       rcases v with b | b
       · show (ρ₁.switch a).sgn b =
           (if Sum.inl b ∈ ({Sum.inl a, Sum.inl (ρ₁.pair a)} : Finset (ρ₁.M ⊕ ρ₂.M))
             then -ρ₁.sgn b else ρ₁.sgn b)
         rw [switch_sgn]
         simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]
       · show ρ₂.sgn b =
           (if Sum.inr b ∈ ({Sum.inl a, Sum.inl (ρ₁.pair a)} : Finset (ρ₁.M ⊕ ρ₂.M))
             then -ρ₂.sgn b else ρ₂.sgn b)
         simp }⟩

/-! ### G.2 The last retained occurrence before a point, and the mark of a smoothing
(sm-3:1378-1380 "a smoothing selects the unique resulting component containing the relevant interval";
the four cases 1462-1472 are the two branches `gap = none` / `gap = some g` together with whether the
`s₁`-cycle of the interval keeps an occurrence) -/

/-- The last `p`-point at or before `u` along `f` — `(f⁻¹)^n u` for the least such `n`; `none` when
the `f`-cycle of `u` has no `p`-point.  (`lastKeep f p u = some ⟨u, _⟩` when `p u`.) -/
noncomputable def lastKeep {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop)
    [DecidablePred p] (u : α) : Option {v // p v} :=
  if h : ∃ n : ℕ, p ((f⁻¹ ^ n) u) then some ⟨(f⁻¹ ^ Nat.find h) u, Nat.find_spec h⟩ else none

theorem lastKeep_of_mem {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    {u : α} (hu : p u) : lastKeep f p u = some ⟨u, hu⟩ := by
  have h : ∃ n : ℕ, p ((f⁻¹ ^ n) u) := ⟨0, by simpa using hu⟩
  have h0 : Nat.find h = 0 := (Nat.find_eq_zero h).mpr (by simpa using hu)
  unfold lastKeep
  rw [dite_eq_left h]
  congr 1
  apply Subtype.ext
  show (f⁻¹ ^ Nat.find h) u = u
  rw [h0, pow_zero, Equiv.Perm.one_apply]

/-- The value of `lastKeep` lies on the `f`-cycle of `u`. -/
theorem lastKeep_sameCycle {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    {u : α} {v : {v // p v}} (h : lastKeep f p u = some v) : f.SameCycle v.1 u := by
  unfold lastKeep at h
  by_cases hex : ∃ n : ℕ, p ((f⁻¹ ^ n) u)
  · rw [dite_eq_left hex] at h
    have hv : v.1 = (f⁻¹ ^ Nat.find hex) u := by
      have := congrArg Subtype.val (Option.some.inj h)
      exact this.symm
    rw [hv]
    refine ⟨(Nat.find hex : ℕ), ?_⟩
    rw [zpow_natCast, ← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply]
  · rw [dite_eq_right hex] at h
    exact absurd h (by simp)

/-- `lastKeep f p u = none` iff the `f`-cycle of `u` carries no `p`-point. -/
theorem lastKeep_eq_none_iff {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop)
    [DecidablePred p] (u : α) : lastKeep f p u = none ↔ ∀ v, p v → ¬ f.SameCycle u v := by
  unfold lastKeep
  split_ifs with hex
  · simp only [false_iff, not_forall, not_not]
    obtain ⟨n, hn⟩ := hex
    exact ⟨_, hn, ⟨-(n : ℤ), by rw [zpow_neg, zpow_natCast, inv_pow]⟩⟩
  · simp only [true_iff]
    intro v hv hc
    apply hex
    obtain ⟨n, hn⟩ := (Equiv.Perm.sameCycle_inv.mpr hc).exists_nat_pow_eq
    exact ⟨n, by rw [hn]; exact hv⟩

/-- "a smoothing selects the unique resulting component containing the relevant interval"
(sm-3:1379-1380): the mark of `ρ.smooth x` induced by a mark `μ` of `ρ`.  With `σ = swap x (τx)`
and `s₁ = ρ.reconnect x = s ∘ σ`, the interval after the gap `g` lies after `σ g` on the `s₁`-cycles
(`s₁ (σ g) = s g`); its component is the `s₁`-cycle of `σ g`, its gap the last retained occurrence
before `σ g` along `s₁` (`lastKeep`; `= σ g = g` when `g ∉ {x, τx}`), `none` when that cycle is
emptied.  A crossing-free marked circle stays crossing-free (`Sum.inr`). -/
noncomputable def Mark.smoothMark (μ : ρ.Mark) (x : ρ.M) : (ρ.smooth x).Mark :=
  match hg : μ.gap with
  | none =>
    { comp := Sum.inr ⟨μ.comp, μ.gap_none hg⟩
      gap := none
      gap_comp := fun _ h => absurd h (by simp)
      gap_none := fun _ v h => by
        rw [smooth_comp] at h
        exact absurd h (by simp) }
  | some g =>
    { comp := Sum.inl (Quotient.mk _ (Equiv.swap x (ρ.pair x) g))
      gap := lastKeep (ρ.reconnect x) (ρ.SmoothKeep x) (Equiv.swap x (ρ.pair x) g)
      gap_comp := fun v h => by
        rw [smooth_comp]
        exact congrArg Sum.inl (Quotient.sound (lastKeep_sameCycle _ _ h))
      gap_none := fun h v hv => by
        rw [smooth_comp] at hv
        have hc : (ρ.reconnect x).SameCycle v.1 (Equiv.swap x (ρ.pair x) g) :=
          Quotient.exact (Sum.inl.inj hv)
        exact (lastKeep_eq_none_iff _ _ _).mp h v.1 v.2 hc.symm }

theorem Mark.smoothMark_of_gap_none (μ : ρ.Mark) (x : ρ.M) (hg : μ.gap = none) :
    (μ.smoothMark x).comp = Sum.inr ⟨μ.comp, μ.gap_none hg⟩ ∧ (μ.smoothMark x).gap = none := by
  unfold Mark.smoothMark
  split
  · exact ⟨rfl, rfl⟩
  · exact absurd (by assumption : μ.gap = some _) (by rw [hg]; simp)

theorem Mark.smoothMark_of_gap_some (μ : ρ.Mark) (x : ρ.M) {g : ρ.M} (hg : μ.gap = some g) :
    (μ.smoothMark x).comp = Sum.inl (Quotient.mk _ (Equiv.swap x (ρ.pair x) g)) ∧
      (μ.smoothMark x).gap = lastKeep (ρ.reconnect x) (ρ.SmoothKeep x) (Equiv.swap x (ρ.pair x) g) := by
  unfold Mark.smoothMark
  split
  · exact absurd (by assumption : μ.gap = none) (by rw [hg]; simp)
  · rename_i g' hg'
    have : g' = g := Option.some.inj (hg'.symm.trans hg)
    subst this
    exact ⟨rfl, rfl⟩

/-! ### G.3 The permutation-level heart of the smoothing commutation: first return of `f * swap a b`
when the swap point `a` need not be retained (generalises `firstReturn_mul_swap`, SM/Stack.lean:345). -/

/-- If the `f`-cycle of `a` has a retained point, with `a'` the last retained point at or before `a`:
`firstReturn (f * swap a b) p = firstReturn f p * swap a' b` (from `a'` the reconnected walk passes
`a`, jumps to `f b` and returns as `f` from `b`; from `b` it jumps to `f a` and returns as `f` from
`a'`; every other retained point never meets `a` before its return, `mul_swap_pow_apply_of_forall_ne`). -/
theorem firstReturn_mul_swap_of_lastKeep_some {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p] (a b : α) (hb : p b)
    {a' : {v // p v}} (ha' : lastKeep f p a = some a') :
    firstReturn (f * Equiv.swap a b) p = firstReturn f p * Equiv.swap a' ⟨b, hb⟩ := by
  sorry

/-- If the `f`-cycle of `a` has no retained point, the swap is invisible to the first return. -/
theorem firstReturn_mul_swap_of_lastKeep_none {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p] (a b : α) (hb : p b)
    (ha : lastKeep f p a = none) :
    firstReturn (f * Equiv.swap a b) p = firstReturn f p := by
  sorry

/-- The retained points of a sum: a predicate on the left summand, everything on the right. -/
def SumKeep {α β : Type*} (p : α → Prop) : α ⊕ β → Prop := fun z => ∀ v, z = Sum.inl v → p v

theorem sumKeep_inl {α β : Type*} (p : α → Prop) (v : α) : SumKeep (β := β) p (Sum.inl v) ↔ p v := by
  simp [SumKeep]

theorem sumKeep_inr {α β : Type*} (p : α → Prop) (b : β) : SumKeep (β := β) p (Sum.inr b) := by
  simp [SumKeep]

/-- First return of `f ⊕ g` to `SumKeep p`, on the left summand: the first return of `f`. -/
theorem firstReturn_sumCongr_inl {α β : Type*} [Fintype α] [Fintype β] (f : Equiv.Perm α)
    (g : Equiv.Perm β) (p : α → Prop) [DecidablePred p] (v : α) (hv : p v) :
    (firstReturn (Equiv.Perm.sumCongr f g) (SumKeep p) ⟨Sum.inl v, (sumKeep_inl p v).mpr hv⟩).1 =
      Sum.inl (firstReturn f p ⟨v, hv⟩).1 := by
  sorry

/-- First return of `f ⊕ g` to `SumKeep p`, on the right summand: one `g`-step. -/
theorem firstReturn_sumCongr_inr {α β : Type*} [Fintype α] [Fintype β] (f : Equiv.Perm α)
    (g : Equiv.Perm β) (p : α → Prop) [DecidablePred p] (b : β) :
    (firstReturn (Equiv.Perm.sumCongr f g) (SumKeep p) ⟨Sum.inr b, sumKeep_inr p b⟩).1 =
      Sum.inr (g b) := by
  sorry

/-- `lastKeep` of `f ⊕ g` at a left point is the left `lastKeep`. -/
theorem lastKeep_sumCongr_inl {α β : Type*} [Fintype α] [Fintype β] (f : Equiv.Perm α)
    (g : Equiv.Perm β) (p : α → Prop) [DecidablePred p] (u : α) :
    lastKeep (Equiv.Perm.sumCongr f g) (SumKeep p) (Sum.inl u) =
      (lastKeep f p u).map (fun v => ⟨Sum.inl v.1, (sumKeep_inl p v.1).mpr v.2⟩) := by
  sorry

/-- The cycles of `(f ⊕ g) * swap (inl a) (inr b)`: two left points lie on one cycle iff they do for
`f`, two right points iff they do for `g`, and a left and a right point iff the left one is on the
`f`-cycle of `a` and the right one on the `g`-cycle of `b` (the two cycles are merged,
`mul_swap_sameCycle_*`, SM/LinkRecord.lean:213-252 and SM/LinkRecordExtras.lean:41-76). -/
theorem sumCongr_mul_swap_sameCycle_inl_inl {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (f : Equiv.Perm α) (g : Equiv.Perm β) (a : α) (b : β) (v w : α) :
    (Equiv.Perm.sumCongr f g * Equiv.swap (Sum.inl a) (Sum.inr b)).SameCycle (Sum.inl v) (Sum.inl w) ↔
      f.SameCycle v w := by
  sorry

theorem sumCongr_mul_swap_sameCycle_inr_inr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (f : Equiv.Perm α) (g : Equiv.Perm β) (a : α) (b : β) (v w : β) :
    (Equiv.Perm.sumCongr f g * Equiv.swap (Sum.inl a) (Sum.inr b)).SameCycle (Sum.inr v) (Sum.inr w) ↔
      g.SameCycle v w := by
  sorry

theorem sumCongr_mul_swap_sameCycle_inl_inr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (f : Equiv.Perm α) (g : Equiv.Perm β) (a : α) (b : β) (v : α) (w : β) :
    (Equiv.Perm.sumCongr f g * Equiv.swap (Sum.inl a) (Sum.inr b)).SameCycle (Sum.inl v) (Sum.inr w) ↔
      f.SameCycle v a ∧ g.SameCycle b w := by
  sorry

/-- The reconnected successor of the join at an `A`-occurrence, rewritten as the join (at the
transported gap `σ g₁`, `σ = swap a (τa)`) of the reconnected successor of `A` with the successor of
`B`: `joinSucc μ₁ μ₂ * swap (inl a) (inl τa) = sumCongr (reconnect a) s₂ * gapSwap (μ₁.gap.map σ) μ₂.gap`
(conjugation `Equiv.swap_apply_apply`; the gap swaps commute past `swap (inl a) (inl τa)`). -/
theorem joinRecord_reconnect_inl {ρ₁ ρ₂ : Record} (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (a : ρ₁.M) :
    (joinRecord μ₁ μ₂).reconnect (Sum.inl a) =
      Equiv.Perm.sumCongr (ρ₁.reconnect a) ρ₂.succ *
        gapSwap (μ₁.gap.map (Equiv.swap a (ρ₁.pair a))) μ₂.gap := by
  sorry

/-- "In the joint diagram, smoothing has exactly the record of `J(A⁰, B)`: both operations are
recombinations at disjoint incoming/outgoing ends. All other successor relations and all other
crossings are unchanged" (sm-3:1459-1462), at the record level.  Occurrences: the subtype of the sum
is the sum of the subtype and `ρ₂.M`; successor: `joinRecord_reconnect_inl`, then
`firstReturn_mul_swap_of_lastKeep_some/none` (the swap point `inl (σ g₁)` is retained iff `g₁ ∉ {a, τa}`)
and `firstReturn_sumCongr_inl/inr`, `lastKeep_sumCongr_inl`; circles: `Equiv.ofBijective` of the
forward map (cycles of left points ↦ `s₁`-cycles, the merged cycle ↦ the marked circle of the
smoothing, right cycles ↦ unmarked circles of `B`, free circles ↦ free circles), well defined by
`sumCongr_mul_swap_sameCycle_*`. -/
theorem joinRecord_smooth_inl {ρ₁ ρ₂ : Record} (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (a : ρ₁.M) :
    Nonempty (RecordIso ((joinRecord μ₁ μ₂).smooth (Sum.inl a))
      (joinRecord (μ₁.smoothMark a) μ₂)) := by
  sorry

/-- The join is symmetric up to named isomorphism: `Φ = Sum.swap` on occurrences; on circles the
marked circle of `A` (which carries `B`'s marked circle) goes to the marked circle of `B`, the other
circles of `A` become unmarked circles of `B`'s side and conversely (`Equiv.sumCompl (· = μ.comp)`). -/
theorem joinRecord_comm {ρ₁ ρ₂ : Record} (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) :
    Nonempty (RecordIso (joinRecord μ₁ μ₂) (joinRecord μ₂ μ₁)) := by
  sorry

/-! ### G.4 Marked-first based orders and the based order of a join (sm-3:1440-1451: "In EACH factor
put the marked component first and base it at its marked gap ... traverse the joined component
starting just before the `A` portion, then its `B` portion ... Thus the entire joined diagram is
UNDER-first") -/

/-- A based order puts the mark first: the marked circle has the least rank and, when the marked
circle carries occurrences, its base occurrence is the one just after the gap. -/
def RBasing.MarkedFirst (B : RBasing ρ) (μ : ρ.Mark) : Prop :=
  (∀ c, c ≠ μ.comp → B.rank μ.comp < B.rank c) ∧ ∀ g, μ.gap = some g → B.base g = ρ.succ g

/-- Every mark admits a marked-first based order (rank `0` on the marked circle, `equivFin + 1`
elsewhere; base `succ g` on the marked circle, `RBasing.default` elsewhere). -/
theorem exists_markedFirst_rbasing (μ : ρ.Mark) : ∃ B : RBasing ρ, B.MarkedFirst μ := by
  sorry

/-- Marked-first survives a record switch (same rank and base). -/
theorem RBasing.markedFirst_switch {B : RBasing ρ} {μ : ρ.Mark} (h : B.MarkedFirst μ) (x : ρ.M) :
    (B.switch x).MarkedFirst (μ.switch x) := h

/-- The based order of the join: the joined marked circle first (rank `0`), then `A`'s other circles
(even ranks `2r+2`), then `B`'s unmarked circles (odd ranks `2r+1`); base occurrences: those of `A`
on `A`'s circles, `A`'s base on the joined circle (or `B`'s when `A`'s marked circle is crossing-free),
`B`'s on its unmarked circles. -/
noncomputable def RBasing.join {ρ₁ ρ₂ : Record} (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂)
    (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) : RBasing (joinRecord μ₁ μ₂) where
  rank := Sum.elim (fun c => if c = μ₁.comp then 0 else 2 * B₁.rank c + 2)
    (fun c => 2 * B₂.rank c.1 + 1)
  rank_inj := by
    rintro (c | c) (c' | c') h
    · simp only [Sum.elim_inl] at h
      by_cases h1 : c = μ₁.comp <;> by_cases h2 : c' = μ₁.comp
      · rw [h1, h2]
      · rw [ite_eq_left h1, ite_eq_right h2] at h; omega
      · rw [ite_eq_right h1, ite_eq_left h2] at h; omega
      · rw [ite_eq_right h1, ite_eq_right h2] at h
        exact congrArg Sum.inl (B₁.rank_inj (by omega))
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      split_ifs at h
      all_goals omega
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      split_ifs at h
      all_goals omega
    · simp only [Sum.elim_inr] at h
      exact congrArg Sum.inr (Subtype.ext (B₂.rank_inj (by omega)))
  base := Sum.elim (fun v => Sum.inl (B₁.base v))
    (fun b => if ρ₂.comp b = μ₂.comp then
        μ₁.gap.elim (Sum.inr (B₂.base b)) (fun g₁ => Sum.inl (B₁.base g₁))
      else Sum.inr (B₂.base b))
  base_comp := by
    sorry
  base_const := by
    sorry

/-- "Thus the entire joined diagram is UNDER-first" (sm-3:1445-1451): the joined based order of two
marked-first UNDER-first based orders is UNDER-first.  Keys of `A`-occurrences compare as in `A`
(same ranks up to the monotone recoding; positions on the joined circle: the `A` portion comes
first — `joinSucc^n (inl (s₁ g₁)) = inl (s₁^n (s₁ g₁))` for `n` below the length of `A`'s marked
cycle), keys of `B`-occurrences compare as in `B` (positions shifted by that length); no crossing
has occurrences in both factors (`pair (inl v) = inl (pair v)`). -/
theorem RBasing.rUnderFirst_join {ρ₁ ρ₂ : Record} {B₁ : RBasing ρ₁} {B₂ : RBasing ρ₂}
    {μ₁ : ρ₁.Mark} {μ₂ : ρ₂.Mark} (h₁ : B₁.MarkedFirst μ₁) (h₂ : B₂.MarkedFirst μ₂)
    (u₁ : B₁.RUnderFirst) (u₂ : B₂.RUnderFirst) : (B₁.join B₂ μ₁ μ₂).RUnderFirst := by
  sorry

/-! ### G.5 Crossings of a join and of an isomorphic record (mp:blocks `sign_preserved`) -/

/-- A named isomorphism induces a bijection of crossings (`{v, τv} ↦ {Φ v, τ' (Φ v)}`,
`RecordIso.crossingOf_eq`). -/
noncomputable def _root_.SM.Link.RecordIso.crossingEquiv {ρ ρ' : Record} (i : RecordIso ρ ρ') :
    ρ.Crossing ≃ ρ'.Crossing where
  toFun c := ρ'.crossingOf (i.Φ c.rep)
  invFun c := ρ.crossingOf (i.Φ.symm c.rep)
  left_inv := by sorry
  right_inv := by sorry

theorem _root_.SM.Link.RecordIso.crossingEquiv_crossingOf {ρ ρ' : Record} (i : RecordIso ρ ρ') (v : ρ.M) :
    i.crossingEquiv (ρ.crossingOf v) = ρ'.crossingOf (i.Φ v) := by
  sorry

/-- The crossings of the join are the crossings of the factors (`pair = sumCongr`). -/
noncomputable def joinCrossingEquiv {ρ₁ ρ₂ : Record} (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) :
    (joinRecord μ₁ μ₂).Crossing ≃ ρ₁.Crossing ⊕ ρ₂.Crossing where
  toFun c := Sum.elim (fun v => Sum.inl (ρ₁.crossingOf v)) (fun w => Sum.inr (ρ₂.crossingOf w)) c.rep
  invFun := Sum.elim (fun c => (joinRecord μ₁ μ₂).crossingOf (Sum.inl c.rep))
    (fun c => (joinRecord μ₁ μ₂).crossingOf (Sum.inr c.rep))
  left_inv := by sorry
  right_inv := by sorry

theorem joinCrossingEquiv_sgn {ρ₁ ρ₂ : Record} (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)
    (c : (joinRecord μ₁ μ₂).Crossing) :
    (joinRecord μ₁ μ₂).sgn c.rep =
      Sum.elim (fun c₁ : ρ₁.Crossing => ρ₁.sgn c₁.rep) (fun c₂ : ρ₂.Crossing => ρ₂.sgn c₂.rep)
        (joinCrossingEquiv μ₁ μ₂ c) := by
  sorry

/-! ### G.6 The blocks of the interlacement graph partition the occurrences (mp:blocks
`writhe_additive`; no geometry) -/

/-- Summing a function of the occurrences block by block (through the retained subtypes of
`restrictCrossings H.supp`) is summing it once: each occurrence lies in exactly the block of its
crossing (`ConnectedComponent.mem_supp_iff`, `Finset.sum_fiberwise`). -/
theorem sum_restrictCrossings_blocks (ρ : Record) (g : ρ.M → ℤ) :
    ∑ H : ρ.interlacementGraph.ConnectedComponent,
      ∑ v : (ρ.restrictCrossings H.supp).M, g v.1 = ∑ v, g v := by
  sorry

/-- "both endpoints of `b` lie in one cyclic gap between successive endpoints of `A`" (sm-3:1645-1646),
for sets of crossings `S₁ ⊆ S`: every occurrence of `S` outside `S₁` lies strictly between one
`S₁`-occurrence `u` and its `S₁`-first return (measured by `steps` along `succ`). -/
def GapContiguous (ρ : Record) (S₁ S : Set ρ.Crossing) : Prop :=
  ∃ u : ρ.M, ∃ hu : ρ.CrossKeep S₁ u, ∀ v, ρ.CrossKeep S v → ¬ ρ.CrossKeep S₁ v →
    ρ.ArcBetween u v ((ρ.restrictCrossings S₁).succ ⟨u, hu⟩).1

/-- Restricting to every crossing changes nothing (cf. `restrictUnivIso`). -/
theorem restrictCrossings_univ_iso (ρ : Record) :
    Nonempty (RecordIso (ρ.restrictCrossings Set.univ) ρ) := by
  sorry

/-- The writhe of a record is the sum of the writhes of its interlacement blocks. -/
theorem writhe_eq_sum_blocks (ρ : Record) :
    ρ.writhe = ∑ H : ρ.interlacementGraph.ConnectedComponent, (ρ.restrictCrossings H.supp).writhe := by
  have h1 := ρ.two_mul_writhe
  have h2 : ∀ H : ρ.interlacementGraph.ConnectedComponent,
      2 * (ρ.restrictCrossings H.supp).writhe = ∑ v : (ρ.restrictCrossings H.supp).M, (ρ.sgn v.1 : ℤ) :=
    fun H => (ρ.restrictCrossings H.supp).two_mul_writhe
  have h3 := sum_restrictCrossings_blocks ρ (fun v => (ρ.sgn v : ℤ))
  have h4 : 2 * ∑ H : ρ.interlacementGraph.ConnectedComponent, (ρ.restrictCrossings H.supp).writhe =
      ∑ v, (ρ.sgn v : ℤ) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun H _ => h2 H), h3]
  omega

end Record

/-! ### G.7 Diagram-level bookkeeping for mp:lowest (wrong mixed crossings, the switch of `Λ`) -/

namespace Diagram

variable (D : Diagram)

/-- Restrictions along equal component sets are equal (the proof of nonemptiness is irrelevant). -/
theorem restrict_congr {S S' : Finset (Fin D.Γ.c)} (h : S = S') (hS : S.Nonempty) (hS' : S'.Nonempty) :
    D.restrict S hS = D.restrict S' hS' := by
  subst h; rfl

/-- `blockRestrict` with singleton blocks (`blk = id`) is the knot restriction. -/
theorem blockRestrict_id (i : Fin D.Γ.c) :
    blockRestrict D id Function.surjective_id i = D.knotRestrict i := by
  unfold blockRestrict knotRestrict
  apply restrict_congr
  ext c
  simp

/-- The mixed crossings at which the smaller-index component is over ("Switch exactly the mixed
crossings necessary to put each smaller-index component UNDER every larger-index component",
sm-3:1608-1610). -/
noncomputable def wrongCrossings : Finset D.Γ.Crossing :=
  Finset.univ.filter (fun x => (D.overStrand x).1 < (D.underStrand x).1)

theorem mem_wrongCrossings (x : D.Γ.Crossing) :
    x ∈ D.wrongCrossings ↔ (D.overStrand x).1 < (D.underStrand x).1 := by
  simp [wrongCrossings]

/-- A wrong crossing is mixed. -/
theorem mixed_of_mem_wrongCrossings {x : D.Γ.Crossing} (hx : x ∈ D.wrongCrossings) :
    (D.overStrand x).1 ≠ (D.underStrand x).1 :=
  ne_of_lt ((D.mem_wrongCrossings x).mp hx)

/-- No wrong crossing: the identity block function is block-ordered (each component its own block). -/
theorem blockOrdered_id_of_wrongCrossings_eq_empty (h : D.wrongCrossings = ∅) :
    BlockOrdered D (id : Fin D.Γ.c → Fin D.Γ.c) := by
  sorry

/-- Switching a wrong crossing removes exactly it from the wrong set. -/
theorem wrongCrossings_switch {x : D.Γ.Crossing} (hx : x ∈ D.wrongCrossings) :
    (D.switch x).wrongCrossings = D.wrongCrossings.erase x := by
  sorry

/-- "no self-crossing or intrinsic component restriction changes" (sm-3:1611-1612): a mixed switch
leaves every knot restriction literally unchanged (`switch_restrict_of_external`). -/
theorem knotRestrict_switch_of_mixed {x : D.Γ.Crossing} (hx : (D.overStrand x).1 ≠ (D.underStrand x).1)
    (i : Fin D.Γ.c) : (D.switch x).knotRestrict i = D.knotRestrict i := by
  unfold knotRestrict
  apply D.switch_restrict_of_external
  intro h
  have h1 := h _ (D.over_mem x)
  have h2 := h _ (D.under_mem x)
  exact hx ((Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm)

/-- A smoothing of a mixed crossing has one component fewer (through the record bridge of
`exists_smoothing_counts`: the over occurrence is not a self crossing). -/
theorem exists_smoothing_of_mixed {x : D.Γ.Crossing} (hx : (D.overStrand x).1 ≠ (D.underStrand x).1) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧ D₀.componentCount = D.componentCount - 1 := by
  obtain ⟨D₀, h₀, -, hc, -, -⟩ := exists_smoothing_counts D x
  refine ⟨D₀, h₀, ?_⟩
  have hns : ¬ D.record.IsSelfCrossing (D.overVisit x) := by
    rw [D.record_isSelfCrossing_iff]
    exact hx
  rw [hc, ite_eq_right hns]

end Diagram

/-- `ℓ_ij = ℓ_ji`: each mixed crossing is one ordered strand pair in either order (`Finset.pair_comm`). -/
theorem mixedSignSum_comm (D : Diagram) (i j : Fin D.Γ.c) : mixedSignSum D i j = mixedSignSum D j i := by
  sorry

/-- The mixed sign sum of a pair not met by `x` is unchanged by switching `x`. -/
theorem mixedSignSum_switch_of_not_mem (D : Diagram) (x : D.Γ.Crossing) (i j : Fin D.Γ.c)
    (h : ¬ ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∧
      ¬ ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)) :
    mixedSignSum (D.switch x) i j = mixedSignSum D i j := by
  sorry

/-- "The switch from positive to negative changes one mixed sign from `+1` to `−1`" (sm-3:1605-1606):
the mixed sign sum of the pair met by `x` drops by `2σ(x)`. -/
theorem mixedSignSum_switch_of_mem (D : Diagram) (x : D.Γ.Crossing) (i j : Fin D.Γ.c) (hij : i ≠ j)
    (h : ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
      ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)) :
    mixedSignSum (D.switch x) i j = mixedSignSum D i j - 2 * (D.sign x : ℤ) := by
  sorry

/-- "and hence changes `Λ` by `−1`" (doubled): `2Λ(D^sw) = 2Λ(D) − 2σ(x)` at a mixed crossing. -/
theorem twoLambda_switch (D : Diagram) {x : D.Γ.Crossing}
    (hx : (D.overStrand x).1 ≠ (D.underStrand x).1) :
    twoLambda (D.switch x) = twoLambda D - 2 * (D.sign x : ℤ) := by
  sorry

/-- "By Lemma mp:zero-link every pair of final components has linking number zero, hence final
`Λ = 0`" (sm-3:1612-1614): `SM.zero_link.over_constant` (second disjunct) for every pair `i < j`. -/
theorem twoLambda_eq_zero_of_blockOrdered (D : Diagram) (h : BlockOrdered D (id : Fin D.Γ.c → Fin D.Γ.c)) :
    twoLambda D = 0 := by
  sorry

/-- With two components, `2Λ = 2ℓ_ij` for the two components `i ≠ j` (`mixedSignSum_comm`). -/
theorem twoLambda_two (D : Diagram) (i j : Fin D.Γ.c) (h2 : D.componentCount = 2) (hij : i ≠ j) :
    twoLambda D = twoLinking D i j := by
  sorry

end Link

/-! ## H. Architect B chain — polynomial level -/

/-! ### H.1 Rows of `a`-monomial multiples and of `δ^n` multiples (mp:lowest, lem:homflyrows) -/

namespace Link

/-- `[a^d z^k](a f) = [a^{d−1} z^k] f` (`AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff`). -/
theorem coeffAt_a_mul (d k : ℤ) (f : R) : coeffAt d k (R.a * f) = coeffAt (d - 1) k f := by
  unfold coeffAt R.a
  rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := (d - 1, k))]
  · simp
  · intro m' _
    constructor
    · intro h; have := Prod.mk.inj h; ext <;> simp <;> omega
    · rintro rfl; ext <;> simp

theorem coeffAt_aInv_mul (d k : ℤ) (f : R) : coeffAt d k (R.aInv * f) = coeffAt (d + 1) k f := by
  unfold coeffAt R.aInv
  rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := (d + 1, k))]
  · simp
  · intro m' _
    constructor
    · intro h; have := Prod.mk.inj h; ext <;> simp <;> omega
    · rintro rfl; ext <;> simp

theorem coeffAt_z_mul (d k : ℤ) (f : R) : coeffAt d k (R.z * f) = coeffAt d (k - 1) f := by
  unfold coeffAt R.z
  rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := (d, k - 1))]
  · simp
  · intro m' _
    constructor
    · intro h; have := Prod.mk.inj h; ext <;> simp <;> omega
    · rintro rfl; ext <;> simp

theorem coeffAt_zInv_mul (d k : ℤ) (f : R) : coeffAt d k (R.zInv * f) = coeffAt d (k + 1) f := by
  unfold coeffAt R.zInv
  rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := (d, k + 1))]
  · simp
  · intro m' _
    constructor
    · intro h; have := Prod.mk.inj h; ext <;> simp <;> omega
    · rintro rfl; ext <;> simp

/-- `(a^n p)_d = p_{d−n}` in `ℤ[a^{±1}]`. -/
theorem coeff_T_mul' (n : ℤ) (p : LaurentPolynomial ℤ) (d : ℤ) :
    (LaurentPolynomial.T n * p).coeff d = p.coeff (d - n) := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := d - n)]
  · simp
  · intro m' _; omega

/-- `[z^k](a f) = a · [z^k] f` in `ℤ[a^{±1}]`. -/
theorem zRow_a_mul (k : ℤ) (f : R) : zRow k (R.a * f) = aPow 1 * zRow k f := by
  ext d
  rw [coeff_zRow, coeffAt_a_mul, coeff_T_mul', coeff_zRow]

/-- `[z^k](a⁻¹ f) = a⁻¹ · [z^k] f`. -/
theorem zRow_aInv_mul (k : ℤ) (f : R) : zRow k (R.aInv * f) = aPow (-1) * zRow k f := by
  ext d
  rw [coeff_zRow, coeffAt_aInv_mul, coeff_T_mul', coeff_zRow, sub_neg_eq_add]

/-- `[z^k](z⁻¹ f) = [z^{k+1}] f`. -/
theorem zRow_zInv_mul (k : ℤ) (f : R) : zRow k (R.zInv * f) = zRow (k + 1) f := by
  ext d
  rw [coeff_zRow, coeffAt_zInv_mul, coeff_zRow]

/-- `[z^k](z f) = [z^{k−1}] f`. -/
theorem zRow_z_mul (k : ℤ) (f : R) : zRow k (R.z * f) = zRow (k - 1) f := by
  ext d
  rw [coeff_zRow, coeffAt_z_mul, coeff_zRow]

/-- `[z^k](δ^n f) = (a − a⁻¹)^n [z^{k+n}] f`, `δ = (a − a⁻¹) z⁻¹` ("the `1−c` coefficient of this
expression is exactly `(a − a⁻¹)^{c−1} ∏ [z^0] P_{D_i}`", sm-3:1616-1618). -/
theorem zRow_delta_pow_mul (n : ℕ) (k : ℤ) (f : R) :
    zRow k (R.delta ^ n * f) = (aPow 1 - aPow (-1)) ^ n * zRow (k + n) f := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    have e : R.delta ^ (n + 1) * f =
        R.a * (R.zInv * (R.delta ^ n * f)) - R.aInv * (R.zInv * (R.delta ^ n * f)) := by
      rw [pow_succ, R.delta]; ring
    rw [e, zRow_sub, zRow_a_mul, zRow_aInv_mul, zRow_zInv_mul, ih, pow_succ]
    push_cast
    rw [show k + 1 + (n : ℤ) = k + (n + 1 : ℤ) by ring]
    ring

/-- "Its multiplication by `z` therefore has support at least `z^{3−c}`, so contributes nothing to
the `1−c` row" (sm-3:1600-1603): for `f ∈ M_{c−1}` (`c ≥ 1`), `[z^{1−c}](z f) = 0`. -/
theorem zRow_z_mul_eq_zero_of_inSupportM {c : ℕ} (hc : 1 ≤ c) {f : R} (hf : InSupportM (c - 1) f) :
    zRow (1 - (c : ℤ)) (R.z * f) = 0 := by
  rw [zRow_z_mul, zRow_eq_zero_iff]
  intro d
  rw [inSupportM_iff] at hf
  apply hf
  rintro ⟨j, hj⟩
  have : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
  rw [this] at hj
  omega

/-- `a^{-n} a^{n} = 1` in `ℤ[a^{±1}]`. -/
theorem aPow_neg_mul_aPow (n : ℤ) : aPow (-n) * aPow n = 1 := by
  rw [aPow, aPow, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

/-- `M_1 = ℤ[a^{±1}, z²]` is closed under products (`InSupportM.mul_left`). -/
theorem InSupportM.one_mul_one {f g : R} (hf : InSupportM 1 f) (hg : InSupportM 1 g) :
    InSupportM 1 (f * g) := by
  refine hg.mul_left fun e he => ?_
  obtain ⟨j, hj⟩ := hf e he
  exact ⟨j, by simpa using hj⟩

/-- `M_1` is closed under finite products. -/
theorem InSupportM.one_prod {ι : Type*} (s : Finset ι) (F : ι → R) (h : ∀ i ∈ s, InSupportM 1 (F i)) :
    InSupportM 1 (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InSupportM.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).one_mul_one
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `[z^0]` of a finite product of elements of `M_1` is the product of the `[z^0]` rows
(`CV.zRow_zero_mul_of_inSupportM_one` iterated; "Knot support is nonnegative and even in `z`",
sm-3:1615-1616). -/
theorem zRow_zero_prod_of_inSupportM_one {ι : Type*} (s : Finset ι) (F : ι → R)
    (h : ∀ i ∈ s, InSupportM 1 (F i)) : zRow 0 (∏ i ∈ s, F i) = ∏ i ∈ s, zRow 0 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    have : zRow 0 (1 : R) = 1 := by
      have h1 := zRow_single 0 0 0 (1 : ℤ)
      rw [ite_eq_left rfl] at h1
      have h2 : (AddMonoidAlgebra.single ((0 : ℤ), (0 : ℤ)) (1 : ℤ) : R) = 1 := by
        rw [AddMonoidAlgebra.one_def, Prod.mk_zero_zero]
      rw [h2] at h1
      rw [h1]
      rfl
    exact this
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      CV.zRow_zero_mul_of_inSupportM_one (h a (Finset.mem_insert_self a s))
        (InSupportM.one_prod s F fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end Link

/-- The polynomial of a knot restriction lies in `M_1` (`P_support`, `knotRestrict_componentCount`). -/
theorem P_knotRestrict_inSupportM_one (D : Diagram) (i : Fin D.Γ.c) :
    InSupportM 1 (P (D.knotRestrict i)) := by
  have h := P_support (D.knotRestrict i)
  rwa [Diagram.knotRestrict_componentCount] at h

/-! ### H.2 mp:join: the step and the two inductions (template: `P_addFree`, SM/PolynomialBlock.lean) -/

namespace Link.Diagram

/-- The mark of the switched diagram induced by a mark of the diagram (through `switchRecordIso`). -/
noncomputable def markSwitch (A : Diagram) (μ : A.record.Mark) (v : A.Γ.Visit) :
    (A.switch v.1).record.Mark :=
  (μ.switch v).map (A.switchRecordIso v.1 v rfl).symm

/-- The mark of a diagram with record `A.record.smooth v` (a smoothing) induced by a mark of `A`. -/
noncomputable def markSmooth (A : Diagram) (μ : A.record.Mark) (v : A.Γ.Visit) {A₀ : Diagram}
    (ι₀ : RecordIso A₀.record (A.record.smooth v)) : A₀.record.Mark :=
  (μ.smoothMark v).map ι₀.symm

/-- Marked-first survives the diagram switch (`rbasingSwitch` keeps rank and base;
`switchRecordIso` is the identity on circles and occurrences). -/
theorem markedFirst_rbasingSwitch (A : Diagram) {B : Record.RBasing A.record}
    {μ : A.record.Mark} (h : B.MarkedFirst μ) (v : A.Γ.Visit) :
    (A.rbasingSwitch v.1 B).MarkedFirst (A.markSwitch μ v) := by
  refine ⟨fun c hc => h.1 c hc, fun g hg => ?_⟩
  obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.mp hg
  exact h.2 g' hg'

end Link.Diagram

/-- The record of `J^sw` at the occurrence corresponding to `inl v` is the join of the switched `A`
with `B` (`switchRecordIso`, `RecordIso.switch`, `joinRecord_switch_inl`, `RecordIso.joinRecord`). -/
theorem join_switch_record (A : Diagram) (v : A.Γ.Visit) {ρ₂ : Record} (μ₂ : ρ₂.Mark)
    (μ : A.record.Mark) (J : Diagram) (ι : RecordIso J.record (Record.joinRecord μ μ₂)) :
    Nonempty (RecordIso (J.switch (ι.Φ.symm (Sum.inl v)).1).record
      (Record.joinRecord (A.markSwitch μ v) μ₂)) := by
  obtain ⟨κ⟩ := Record.joinRecord_switch_inl μ μ₂ v
  set u := ι.Φ.symm (Sum.inl v) with hu_def
  have hu : ι.Φ u = Sum.inl v := Equiv.apply_symm_apply _ _
  refine ⟨(J.switchRecordIso u.1 u rfl).trans ((ι.switch u).trans ?_)⟩
  rw [hu]
  refine κ.trans ?_
  have e := RecordIso.joinRecord (A.switchRecordIso v.1 v rfl).symm (RecordIso.refl ρ₂)
    (μ.switch v) μ₂
  rw [Record.Mark.map_refl] at e
  exact e

/-- The record of the smoothing of `J` at the occurrence corresponding to `inl v` is the join of the
smoothing of `A` with `B` (`exists_smoothing_record_visit`, `RecordIso.smooth`, `joinRecord_smooth_inl`,
`RecordIso.joinRecord`). -/
theorem join_smooth_record (A : Diagram) (v : A.Γ.Visit) {ρ₂ : Record} (μ₂ : ρ₂.Mark)
    (μ : A.record.Mark) (J : Diagram) (ι : RecordIso J.record (Record.joinRecord μ μ₂))
    {A₀ : Diagram} (ι₀ : RecordIso A₀.record (A.record.smooth v)) :
    ∃ J₀ : Diagram, IsOrientedSmoothing J (ι.Φ.symm (Sum.inl v)).1 J₀ ∧
      Nonempty (RecordIso J₀.record (Record.joinRecord (A.markSmooth μ v ι₀) μ₂)) := by
  set u := ι.Φ.symm (Sum.inl v) with hu_def
  have hu : ι.Φ u = Sum.inl v := Equiv.apply_symm_apply _ _
  obtain ⟨J₀, hJ₀, ⟨κ₀⟩⟩ := exists_smoothing_record_visit J u.1 u rfl
  obtain ⟨κ⟩ := Record.joinRecord_smooth_inl μ μ₂ v
  refine ⟨J₀, hJ₀, ⟨κ₀.trans ((ι.smooth u).trans ?_)⟩⟩
  rw [hu]
  refine κ.trans ?_
  have e := RecordIso.joinRecord ι₀.symm (RecordIso.refl ρ₂) (μ.smoothMark v) μ₂
  rw [Record.Mark.map_refl] at e
  exact e

/-- The sign of the join at an `A`-occurrence is the sign in `A` (`ι.sgn_eq`, `joinRecord_sgn_inl`). -/
theorem join_isPositive_iff (A : Diagram) (v : A.Γ.Visit) {ρ₂ : Record} (μ₂ : ρ₂.Mark)
    (μ : A.record.Mark) (J : Diagram) (ι : RecordIso J.record (Record.joinRecord μ μ₂)) :
    J.IsPositive (ι.Φ.symm (Sum.inl v)).1 ↔ A.IsPositive v.1 := by
  have h := ι.sgn_eq (ι.Φ.symm (Sum.inl v))
  have hu : ι.Φ (ι.Φ.symm (Sum.inl v)) = Sum.inl v := Equiv.apply_symm_apply _ _
  rw [hu, Record.joinRecord_sgn_inl] at h
  rw [J.isPositive_iff_sign_eq_one, A.isPositive_iff_sign_eq_one]
  change J.record.sgn (ι.Φ.symm (Sum.inl v)) = 1 ↔ A.record.sgn v = 1
  rw [← h]

/-- The step of mp:join at an occurrence `v` of the first factor (sm-3:1453-1490), for an abstract
second factor with value `q`: from the two smaller identities (switch, smoothing) the solved skein
on `J` and on `A` with `solvedR_mul_left` gives the identity on `J`. -/
theorem join_step (A : Diagram) (v : A.Γ.Visit) {ρ₂ : Record} (μ₂ : ρ₂.Mark) (q : R)
    (μ : A.record.Mark)
    (ihsw : ∀ J' : Diagram, Nonempty (RecordIso J'.record (Record.joinRecord (A.markSwitch μ v) μ₂)) →
      P J' = P (A.switch v.1) * q)
    (ihsm : ∀ (A₀ : Diagram) (ι₀ : RecordIso A₀.record (A.record.smooth v)),
      IsOrientedSmoothing A v.1 A₀ →
      ∀ J₀ : Diagram, Nonempty (RecordIso J₀.record (Record.joinRecord (A.markSmooth μ v ι₀) μ₂)) →
        P J₀ = P A₀ * q)
    (J : Diagram) (ι : RecordIso J.record (Record.joinRecord μ μ₂)) : P J = P A * q := by
  set x : J.Γ.Crossing := (ι.Φ.symm (Sum.inl v)).1
  obtain ⟨A₀, h₀, ⟨ι₀⟩⟩ := exists_smoothing_record_visit A v.1 v rfl
  obtain ⟨J₀, hJ₀, hJ₀r⟩ := join_smooth_record A v μ₂ μ J ι ι₀
  have hsw : P (J.switch x) = P (A.switch v.1) * q := ihsw _ (join_switch_record A v μ₂ μ J ι)
  have hsm : P J₀ = P A₀ * q := ihsm A₀ ι₀ h₀ J₀ hJ₀r
  have hJ : P J = solvedR (J.IsPositive x) (P (J.switch x)) (P J₀) :=
    solvedR_of_skein (fun _ _ _ ht => P_skein ht) hJ₀
  have hA : P A = solvedR (A.IsPositive v.1) (P (A.switch v.1)) (P A₀) :=
    solvedR_of_skein (fun _ _ _ ht => P_skein ht) h₀
  have hpos : J.IsPositive x ↔ A.IsPositive v.1 := join_isPositive_iff A v μ₂ μ J ι
  rw [hJ, hsw, hsm, mul_comm _ q, mul_comm _ q, solvedR_mul_left, hA, mul_comm, propext hpos]

/-- Inner induction of mp:join (sm-3:1438-1451, 1453-1490 with the bad crossing in `A`): for every
`A` with a marked-first based order and every UNDER-first marked `B`, every clean join has
`P = P_A P_B`.  `skein_induction_based` on `A`; init `rUnderFirst_join` through `RBasing.map` and
`exists_underFirst_of_rUnderFirst`, `P_underFirst_init` three times, `componentCount_joinRecord`;
step `join_step`. -/
theorem join_core_right_underFirst (A : Diagram) (BA : Record.RBasing A.record) :
    ∀ (μA : A.record.Mark), BA.MarkedFirst μA →
    ∀ (B : Diagram) (μB : B.record.Mark) (BB : Record.RBasing B.record),
      BB.MarkedFirst μB → BB.RUnderFirst →
    ∀ J : Diagram, Nonempty (RecordIso J.record (Record.joinRecord μA μB)) → P J = P A * P B := by
  refine Diagram.skein_induction_based
    (fun A BA => ∀ (μA : A.record.Mark), BA.MarkedFirst μA →
      ∀ (B : Diagram) (μB : B.record.Mark) (BB : Record.RBasing B.record),
        BB.MarkedFirst μB → BB.RUnderFirst →
      ∀ J : Diagram, Nonempty (RecordIso J.record (Record.joinRecord μA μB)) → P J = P A * P B)
    ?_ ?_ A BA
  · -- init: both factors UNDER-first at marked-first based orders
    rintro A BA hA μA hμA B μB BB hμB hB J ⟨ι⟩
    obtain ⟨B₁, hB₁⟩ := A.exists_underFirst_of_rUnderFirst BA hA
    obtain ⟨B₂, hB₂⟩ := B.exists_underFirst_of_rUnderFirst BB hB
    have hJ : ((BA.join BB μA μB).map ι.symm).RUnderFirst :=
      ((BA.join BB μA μB).rUnderFirst_map ι.symm).mpr
        (Record.RBasing.rUnderFirst_join hμA hμB hA hB)
    obtain ⟨B₃, hB₃⟩ := J.exists_underFirst_of_rUnderFirst _ hJ
    rw [P_underFirst_init A B₁ hB₁, P_underFirst_init B B₂ hB₂, P_underFirst_init J B₃ hB₃, ← pow_add]
    congr 1
    have hc : J.componentCount = A.componentCount + B.componentCount - 1 := by
      rw [← J.record_componentCount, ι.componentCount_eq, Record.componentCount_joinRecord,
        A.record_componentCount, B.record_componentCount]
    have := A.componentCount_pos
    have := B.componentCount_pos
    omega
  · -- step at a bad occurrence `v` of `A`
    rintro A BA v _ ihsw ihsm μA hμA B μB BB hμB hB J ⟨ι⟩
    refine join_step A v μB (P B) μA ?_ ?_ J ι
    · intro J' hJ'
      exact ihsw (A.markSwitch μA v) (A.markedFirst_rbasingSwitch hμA v) B μB BB hμB hB J' hJ'
    · intro A₀ ι₀ h₀ J₀ hJ₀
      obtain ⟨B₀, hB₀⟩ := Record.exists_markedFirst_rbasing (A.markSmooth μA v ι₀)
      exact ihsm A₀ B₀ h₀ (A.markSmooth μA v ι₀) hB₀ B μB BB hμB hB J₀ hJ₀

/-- Outer induction of mp:join (the bad crossing in the other factor, sm-3:1487-1490 "the identical
argument with the two factor names interchanged"): the inducted factor sits in the `inl` slot of the
join record, so the same `join_step` applies; init by `join_core_right_underFirst` after
`joinRecord_comm`. -/
theorem join_core (B : Diagram) (BB : Record.RBasing B.record) :
    ∀ (μB : B.record.Mark), BB.MarkedFirst μB →
    ∀ (A : Diagram) (μA : A.record.Mark) (J : Diagram),
      Nonempty (RecordIso J.record (Record.joinRecord μB μA)) → P J = P B * P A := by
  refine Diagram.skein_induction_based
    (fun B BB => ∀ (μB : B.record.Mark), BB.MarkedFirst μB →
      ∀ (A : Diagram) (μA : A.record.Mark) (J : Diagram),
        Nonempty (RecordIso J.record (Record.joinRecord μB μA)) → P J = P B * P A)
    ?_ ?_ B BB
  · rintro B BB hB μB hμB A μA J ⟨ι⟩
    obtain ⟨comm⟩ := Record.joinRecord_comm μB μA
    obtain ⟨BA, hBA⟩ := Record.exists_markedFirst_rbasing μA
    rw [join_core_right_underFirst A BA μA hBA B μB BB hμB hB J ⟨ι.trans comm⟩, mul_comm]
  · rintro B BB w _ ihsw ihsm μB hμB A μA J ⟨ι⟩
    refine join_step B w μA (P A) μB ?_ ?_ J ι
    · intro J' hJ'
      exact ihsw (B.markSwitch μB w) (B.markedFirst_rbasingSwitch hμB w) A μA J' hJ'
    · intro B₀ ι₀ h₀ J₀ hJ₀
      obtain ⟨B₀', hB₀'⟩ := Record.exists_markedFirst_rbasing (B.markSmooth μB w ι₀)
      exact ihsm B₀ B₀' h₀ (B.markSmooth μB w ι₀) hB₀' A μA J₀ hJ₀

/-- eq. mp:join-value from the chain. -/
theorem join_value_of_cleanMarkedJoin (A B : MarkedDiagram) (J : Diagram)
    (h : IsCleanMarkedJoin A B J) : P J = P A.D * P B.D := by
  obtain ⟨ι⟩ := h
  obtain ⟨comm⟩ := Record.joinRecord_comm A.μ B.μ
  obtain ⟨BB, hBB⟩ := Record.exists_markedFirst_rbasing B.μ
  rw [join_core B.D BB B.μ hBB A.D A.μ J ⟨ι.trans comm⟩, mul_comm]

/-! ### H.3 mp:lowest: the weight `a^{2Λ}[z^{1−c}]P_D` is switch-invariant at mixed crossings;
reduction to `BlockOrdered D id`; the value there from `SM.stack` -/

/-- "It follows that `a^{2Λ} h` is unchanged by that switch" (sm-3:1606-1607): at a mixed crossing `x`
with smoothing `D₀` of `c − 1` components, `P_recursion_pos/neg`, `zRow_z_mul_eq_zero_of_inSupportM`
(`P_support D₀`), `zRow_a_mul`/`zRow_aInv_mul`, `twoLambda_switch`. -/
theorem lowest_switch_step (D : Diagram) {x : D.Γ.Crossing}
    (hx : (D.overStrand x).1 ≠ (D.underStrand x).1) :
    aPow (twoLambda D) * zRow (1 - (D.componentCount : ℤ)) (P D) =
      aPow (twoLambda (D.switch x)) * zRow (1 - (D.componentCount : ℤ)) (P (D.switch x)) := by
  obtain ⟨D₀, h₀, hc₀⟩ := D.exists_smoothing_of_mixed hx
  have hc1 : 1 ≤ D.componentCount := D.componentCount_pos
  have hsupp : InSupportM (D.componentCount - 1) (P D₀) := by rw [← hc₀]; exact P_support D₀
  have hz : zRow (1 - (D.componentCount : ℤ)) (R.z * P D₀) = 0 :=
    zRow_z_mul_eq_zero_of_inSupportM hc1 hsupp
  rw [twoLambda_switch D hx]
  by_cases hp : D.IsPositive x
  · have hs : (D.sign x : ℤ) = 1 := by rw [(D.isPositive_iff_sign_eq_one x).mp hp]; rfl
    rw [P_recursion_pos h₀ hp, zRow_add, mul_assoc, mul_assoc, zRow_aInv_mul, zRow_aInv_mul,
      zRow_aInv_mul, hz, mul_zero, add_zero, hs,
      show twoLambda D - 2 * 1 = twoLambda D + -1 + -1 by ring]
    simp only [aPow, LaurentPolynomial.T_add]
    ring
  · have hs : (D.sign x : ℤ) = -1 := by rw [(D.sign_eq_neg_one_iff x).mpr hp]; rfl
    rw [P_recursion_neg h₀ hp, zRow_sub, mul_assoc, mul_assoc, zRow_a_mul, zRow_a_mul, zRow_a_mul,
      hz, mul_zero, sub_zero, hs,
      show twoLambda D - 2 * (-1) = twoLambda D + 1 + 1 by ring]
    simp only [aPow, LaurentPolynomial.T_add]
    ring

/-- The value on a block-ordered diagram with singleton blocks (sm-3:1614-1618): `stack_formula`
with `blk = id`, `blockRestrict_id`, `zRow_delta_pow_mul`, `zRow_zero_prod_of_inSupportM_one`. -/
theorem lowest_blockOrdered (D : Diagram) (h : BlockOrdered D (id : Fin D.Γ.c → Fin D.Γ.c)) :
    zRow (1 - (D.componentCount : ℤ)) (P D) =
      (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) * ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i)) := by
  have hP := stack_formula D D.Γ.c id Function.surjective_id h
  simp only [Diagram.blockRestrict_id] at hP
  rw [hP, zRow_delta_pow_mul]
  have hc : (1 - (D.componentCount : ℤ)) + ((D.Γ.c - 1 : ℕ) : ℤ) = 0 := by
    have := D.componentCount_pos
    unfold Diagram.componentCount at *
    omega
  rw [hc, zRow_zero_prod_of_inSupportM_one _ _ (fun i _ => P_knotRestrict_inSupportM_one D i)]
  rfl

/-- The reduction (sm-3:1608-1614): induction on the number of wrong mixed crossings, each removed by
one switch (`wrongCrossings_switch`, `lowest_switch_step`, `knotRestrict_switch_of_mixed`); at the
end `BlockOrdered D id`, `lowest_blockOrdered` and `twoLambda_eq_zero_of_blockOrdered`. -/
theorem lowest_reduce (D : Diagram) :
    aPow (twoLambda D) * zRow (1 - (D.componentCount : ℤ)) (P D) =
      (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) * ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i)) := by
  suffices h : ∀ (n : ℕ) (D : Diagram), D.wrongCrossings.card = n →
      aPow (twoLambda D) * zRow (1 - (D.componentCount : ℤ)) (P D) =
        (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) *
          ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i)) from h _ D rfl
  intro n
  induction n with
  | zero =>
    intro D hD
    have hempty : D.wrongCrossings = ∅ := Finset.card_eq_zero.mp hD
    have hbo := D.blockOrdered_id_of_wrongCrossings_eq_empty hempty
    rw [twoLambda_eq_zero_of_blockOrdered D hbo, lowest_blockOrdered D hbo]
    simp [aPow]
  | succ n ih =>
    intro D hD
    obtain ⟨x, hx⟩ : D.wrongCrossings.Nonempty := Finset.card_pos.mp (by omega)
    have hmixed := D.mixed_of_mem_wrongCrossings hx
    have hcard : (D.switch x).wrongCrossings.card = n := by
      have h1 : (D.wrongCrossings.erase x).card = n := by
        rw [Finset.card_erase_of_mem hx, hD]
        rfl
      rw [D.wrongCrossings_switch hx]
      exact h1
    have h1 := ih (D.switch x) hcard
    have hcc : (D.switch x).componentCount = D.componentCount := rfl
    rw [lowest_switch_step D hmixed]
    rw [hcc] at h1
    rw [h1]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [D.knotRestrict_switch_of_mixed hmixed i]

/-- eq. mp:lowest-value from `lowest_reduce` (multiply by `a^{−2Λ}`). -/
theorem lowest_value_of_reduce (D : Diagram) :
    zRow (1 - (D.componentCount : ℤ)) (P D) =
      aPow (-(twoLambda D)) * (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) *
        ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i)) := by
  have h := lowest_reduce D
  rw [mul_assoc, ← h, ← mul_assoc, aPow_neg_mul_aPow, one_mul]

/-- The two-component row from `lowest_value` (`twoLambda_two`, `Fin.prod_univ_two`, `mixedSignSum_comm`). -/
theorem two_component_row_of_lowest (D : Diagram) (i j : Fin D.Γ.c) (h2 : D.componentCount = 2)
    (hij : i ≠ j) :
    zRow (-1) (P D) =
      aPow (-(twoLinking D i j)) * (aPow 1 - aPow (-1)) *
        (zRow 0 (P (D.knotRestrict i)) * zRow 0 (P (D.knotRestrict j))) := by
  have h := lowest_value_of_reduce D
  have huniv : ({i, j} : Finset (Fin D.Γ.c)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    exact h2.le
  rw [h2, twoLambda_two D i j h2 hij, ← huniv, Finset.prod_pair hij] at h
  have e1 : (1 - ((2 : ℕ) : ℤ)) = -1 := by norm_num
  rw [e1, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  exact h

/-! ### H.4 mp:blocks: forest inductions (no geometry) and the realization chain (analysed, `sorry`) -/

/-- "Repeated use of Theorem mp:join gives the product value for the constructed diagram"
(sm-3:1675-1676): `JoinForest` induction with `join_value_of_cleanMarkedJoin`; leaves by
`Finset.prod_singleton`, nodes by `Finset.prod_union` on the disjoint index sets. -/
theorem product_of_joinForest {ι : Type} (C : ι → Diagram) :
    ∀ (S : Set ι) (J : Diagram), JoinForest C S J → ∀ T : Finset ι, (↑T : Set ι) = S →
      P J = ∏ i ∈ T, P (C i) := by
  sorry

/-- "Every old crossing is present once, with its old sign" (sm-3:1681-1682): `JoinForest` induction;
at a node the named isomorphism to the join record gives `J.Γ.Crossing ≃ A.Γ.Crossing ⊕ B.Γ.Crossing`
(`recordCrossingEquiv`, `RecordIso.crossingEquiv`, `joinCrossingEquiv`) with signs
(`sign_eq_of_recordIso`, `joinCrossingEquiv_sgn`); the index sets combine by `Equiv.Set.union`. -/
theorem sign_preserved_of_joinForest {ι : Type} (C : ι → Diagram) :
    ∀ (S : Set ι) (J : Diagram), JoinForest C S J → ∀ T : Finset ι, (↑T : Set ι) = S →
      ∃ φ : (Σ i : T, (C i).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2 := by
  sorry

/-- Realization chain, geometric part 1 (D9 sub-obligation; ANALYSED ONLY, see PLAN_B.md §5): every
record mark of an actual diagram is realized by a printed marked interval — a short clean arc just
after the gap occurrence (or anywhere on a crossing-free marked circle). -/
theorem exists_markedInterval_of_mark (D : Diagram) (μ : D.record.Mark) :
    ∃ I : D.Γ.Arc, IsMarkedInterval D I ∧ I.i = μ.comp ∧ ∀ v, μ.gap = some v ↔ D.IsGapOf I v := by
  sorry

/-- Realization chain, record part 1 (ANALYSED ONLY, PLAN_B.md §5): smoothing away the crossings of
`S \\ S₁` when they lie in one gap of `S₁` (`GapContiguous`) leaves the `S₁`-first-return successor
unchanged and never splits the `S₁`-circle; restricting the resulting actual diagram to that circle
realizes `restrictCrossings S₁`.  Uses only accepted geometry (`exists_smoothing_record_visit`,
`Diagram.restrict`, `restrictRecordIso`) and the `firstReturn` lemmas of §G.3. -/
theorem isRealizable_restrictCrossings_of_gapContiguous (ρ : Record) (h1 : ρ.componentCount = 1)
    {S₁ S : Set ρ.Crossing} (hsub : S₁ ⊆ S) (hS : IsRealizable (ρ.restrictCrossings S))
    (hgap : ρ.GapContiguous S₁ S) : IsRealizable (ρ.restrictCrossings S₁) := by
  sorry

/-- Realization chain, combinatorial part (record level; ANALYSED ONLY): a union of blocks `S` with
at least two blocks splits as `S₁ ⊔ S₂` (both unions of blocks) with each inside one gap of the other
(sm-3:1638-1663), and then the restricted record is the join of the two restricted records at the
gap marks (sm-3:1664-1669). -/
theorem restrictCrossings_join_decomp (ρ : Record) (h1 : ρ.componentCount = 1)
    (S : Set ρ.Crossing)
    (hS : ∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S ∨ Disjoint H.supp S)
    (h2 : ∃ H H' : ρ.interlacementGraph.ConnectedComponent, H ≠ H' ∧ H.supp ⊆ S ∧ H'.supp ⊆ S) :
    ∃ (S₁ S₂ : Set ρ.Crossing), S₁ ∪ S₂ = S ∧ Disjoint S₁ S₂ ∧ S₁.Nonempty ∧ S₂.Nonempty ∧
      (∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S₁ ∨ Disjoint H.supp S₁) ∧
      (∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S₂ ∨ Disjoint H.supp S₂) ∧
      ρ.GapContiguous S₁ S ∧ ρ.GapContiguous S₂ S ∧
      ∃ (μ₁ : (ρ.restrictCrossings S₁).Mark) (μ₂ : (ρ.restrictCrossings S₂).Mark),
        Nonempty (RecordIso (ρ.restrictCrossings S) (Record.joinRecord μ₁ μ₂)) := by
  sorry

/-- Realization chain, assembly (ANALYSED ONLY): induction on the number of blocks in `S`.  One block:
the supplied leaf.  Several: `restrictCrossings_join_decomp`, the two sub-realizations by
`isRealizable_restrictCrossings_of_gapContiguous`, the induction hypothesis for them, marks
transported along the isomorphisms (`Mark.map`, `RecordIso.joinRecord`), intervals by
`exists_markedInterval_of_mark`; the given realization of `restrictCrossings S` is itself the join
node (`IsCleanMarkedJoin` is record-level).  No clean-join construction is needed. -/
theorem exists_joinForest_of_realizable (ρ : Record)
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (h : BlockSupply ρ C) :
    ∀ S : Set ρ.Crossing,
      (∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S ∨ Disjoint H.supp S) →
      S.Nonempty → IsRealizable (ρ.restrictCrossings S) →
      ∃ J : Diagram, JoinForest C {H | H.supp ⊆ S} J ∧
        Nonempty (RecordIso J.record (ρ.restrictCrossings S)) := by
  sorry

/-- "a finite succession of clean marked joins of these actual diagrams realizes the full record"
(sm-3:1629-1630): the assembly at `S = univ`, realizable by `BlockSupply.actual` through
`restrictCrossings_univ_iso`. -/
theorem realizes_of_blockSupply (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram)
    (h : BlockSupply ρ C) : ∃ J : Diagram, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record ρ) := by
  obtain ⟨ιu⟩ := Record.restrictCrossings_univ_iso ρ
  have hreal : IsRealizable (ρ.restrictCrossings Set.univ) := h.actual.of_iso ιu.symm
  have hne : (Set.univ : Set ρ.Crossing).Nonempty := by
    obtain ⟨v⟩ := h.nonempty
    exact ⟨ρ.crossingOf v, Set.mem_univ _⟩
  obtain ⟨J, hJ, ⟨ιJ⟩⟩ := exists_joinForest_of_realizable ρ C h Set.univ
    (fun H => Or.inl (Set.subset_univ _)) hne hreal
  refine ⟨J, ?_, ⟨ιJ.trans ιu⟩⟩
  have hset : {H : ρ.interlacementGraph.ConnectedComponent | H.supp ⊆ Set.univ} = Set.univ := by
    ext H; simp
  rw [hset] at hJ
  exact hJ

/-- `product` from the realization and the forest product (`presentations` transfers to any actual
diagram with the full record). -/
theorem product_of_blockSupply (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram)
    (h : BlockSupply ρ C) (D : Diagram) (hD : Nonempty (RecordIso D.record ρ)) :
    P D = ∏ H, P (C H) := by
  obtain ⟨J, hJ, ⟨ιJ⟩⟩ := realizes_of_blockSupply ρ C h
  obtain ⟨ι⟩ := hD
  rw [presentations D J ⟨ι.trans ιJ.symm⟩]
  exact product_of_joinForest C Set.univ J hJ Finset.univ (by simp)

/-- `writhe_additive` from `writhe_eq_sum_blocks` and the supplied isomorphisms. -/
theorem writhe_additive_of_blockSupply (ρ : Record)
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (h : BlockSupply ρ C) (D : Diagram)
    (hD : Nonempty (RecordIso D.record ρ)) : D.writhe = ∑ H, (C H).writhe := by
  obtain ⟨ι⟩ := hD
  rw [← D.record_writhe, ι.writhe_eq, Record.writhe_eq_sum_blocks]
  refine Finset.sum_congr rfl fun H _ => ?_
  obtain ⟨ιH⟩ := h.supplied H
  rw [← (C H).record_writhe, ιH.writhe_eq]

/-- `sign_preserved` from the forest lemma at `T = univ`. -/
theorem sign_preserved_of_blockSupply (ρ : Record)
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (_h : BlockSupply ρ C) (J : Diagram)
    (hJ : JoinForest C Set.univ J) :
    ∃ φ : (Σ H : ρ.interlacementGraph.ConnectedComponent, (C H).Γ.Crossing) ≃ J.Γ.Crossing,
      ∀ q, J.sign (φ q) = (C q.1).sign q.2 := by
  obtain ⟨φ, hφ⟩ := sign_preserved_of_joinForest C Set.univ J hJ Finset.univ (by simp)
  let e : (Σ H : ρ.interlacementGraph.ConnectedComponent, (C H).Γ.Crossing) ≃
      (Σ i : (Finset.univ : Finset ρ.interlacementGraph.ConnectedComponent), (C i).Γ.Crossing) :=
    (Equiv.sigmaCongrLeft (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x))).symm
  refine ⟨e.trans φ, fun q => ?_⟩
  rw [Equiv.trans_apply, hφ]
  rfl

/-! ### H.5 lem:homflyrows pieces -/

/-- `H_{K⊔J} = δ H_K H_J` on representatives: `SM.stack.split_union` with the block function
`c ↦ if c ∈ B then 0 else 1`, `restrict_congr`, `presentations`, `P_eq_homfly`. -/
theorem P_splitUnion (K' J' D : Diagram) (h : IsSplitUnion K' J' D) : P D = R.delta * (P K' * P J') := by
  obtain ⟨B, hB, hB', hno, ⟨ιK⟩, ⟨ιJ⟩⟩ := h
  let blk : Fin D.Γ.c → Fin 2 := fun c => if c ∈ B then 0 else 1
  have hsurj : Function.Surjective blk := by
    intro k
    fin_cases k
    · obtain ⟨c, hc⟩ := hB
      exact ⟨c, by simp [blk, hc]⟩
    · obtain ⟨c, hc⟩ := hB'
      exact ⟨c, by simp [blk, Finset.mem_compl.mp hc]⟩
  have hblocks : ∀ (x : D.Γ.Crossing) (s t : D.Γ.Strand), s ∈ x.val → t ∈ x.val →
      blk s.1 = blk t.1 := by
    intro x s t hs ht
    simp only [blk]
    have hiff := hno x s hs t ht
    by_cases hsB : s.1 ∈ B
    · rw [ite_eq_left hsB, ite_eq_left (hiff.mp hsB)]
    · rw [ite_eq_right hsB, ite_eq_right (fun h => hsB (hiff.mpr h))]
  have hP := SM.stack.split_union D blk hsurj hblocks
  have e0 : blockRestrict D blk hsurj 0 = D.restrict B hB := by
    unfold blockRestrict
    apply D.restrict_congr
    ext c
    by_cases hc : c ∈ B <;> simp [blk, hc]
  have e1 : blockRestrict D blk hsurj 1 = D.restrict Bᶜ hB' := by
    unfold blockRestrict
    apply D.restrict_congr
    ext c
    by_cases hc : c ∈ B <;> simp [blk, hc]
  rw [hP, e0, e1, presentations _ _ ⟨ιK⟩, presentations _ _ ⟨ιJ⟩, mul_assoc]

/-! ## I. The four row theorems from the chain -/

/-- mp:join. -/
theorem join : JoinData where
  join_value := join_value_of_cleanMarkedJoin
  multi_component_factors := fun A B J _ h => join_value_of_cleanMarkedJoin A B J h
  crossing_free_marked_component := fun A B J _ h => join_value_of_cleanMarkedJoin A B J h

/-- mp:lowest. -/
theorem lowest : LowestData where
  lowest_value := lowest_value_of_reduce
  two_component_row := two_component_row_of_lowest

/-- mp:blocks (`realizes` through the analysed chain `realizes_of_blockSupply`, left `sorry`). -/
theorem blocks : BlocksData where
  realizes := realizes_of_blockSupply
  product := product_of_blockSupply
  sign_preserved := sign_preserved_of_blockSupply
  writhe_additive := writhe_additive_of_blockSupply

/-- lem:homflyrows. -/
theorem homflyrows : HomflyRowsData where
  connected_sum := fun K J _ _ K' J' D hK hJ h => by
    rw [← P_eq_homfly, join_value_of_cleanMarkedJoin K' J' D h, P_eq_homfly, P_eq_homfly,
      homfly_descent hK, homfly_descent hJ]
  split_union := fun K J _ _ K' J' D hK hJ h => by
    rw [← P_eq_homfly, P_splitUnion K' J' D h, P_eq_homfly, P_eq_homfly, homfly_descent hK,
      homfly_descent hJ]
  two_component_row := fun D i j h2 hij => by
    have h := two_component_row_of_lowest D i j h2 hij
    rw [← P_eq_homfly, ← P_eq_homfly, ← P_eq_homfly, h,
      CV.zRow_zero_mul_of_inSupportM_one (P_knotRestrict_inSupportM_one D i)
        (P_knotRestrict_inSupportM_one D j)]
    ring

end SM
