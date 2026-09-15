import SM.PolynomialBlock
import SM.ZeroLink
import SM.Stack
import CV.Axioms
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Skeleton FINAL — marked products (mp:join, mp:lowest, mp:blocks, lem:homflyrows)

Judge's synthesis (2026-09-14) of Skeleton_A.lean (Architect A, record-first) and Skeleton_B.lean
(Architect B, reuse-first).  Plan of record: work/drafts/markedproducts/PLAN_FINAL.md.
Fixed statements: work/drafts/MarkedProducts_statement.lean — sections A-E (lines 106-348) and the four
bundles `JoinData` (352-370), `LowestData` (376-395), `BlocksData` (401-428), `HomflyRowsData` (434-461)
are copied below BYTE-IDENTICALLY (assembled by script from the statement file); only the four row
theorems `SM.join`, `SM.lowest`, `SM.blocks`, `SM.homflyrows` carry proofs here.

Winner: **B** (base), with grafts from A.
* mp:join — A's induction lane (`P_join_init`, `P_join_step_left/right`, the two
  `skein_induction_based` inductions, `RBasing.MarkCompatible`) on B's proved record lemmas
  (`Mark.switch`, `joinRecord_switch_inl`, `lastKeep`, `Mark.smoothMark`).  The two hard record lemmas
  are stated EXISTENTIALLY (A's form, strictly weaker than B's fixed-witness forms and sufficient for the
  inductions): `exists_rUnderFirst_joinRecord` (J3) and `exists_joinRecord_smooth_inl` (J4); B's
  `Mark.smoothMark` is the intended witness of J4 and B's `RBasing.join` (Skeleton_B.lean:668) of J3.
  `joinRecord_comm` in B's weak form (`Nonempty`), which is all the consumers use.
* mp:lowest — B's lane wholesale (row algebra PROVED, `wrongCrossings`, `lowest_switch_step`,
  `lowest_reduce`, `lowest_value_of_reduce`, `two_component_row_of_lowest` PROVED); the judge closed
  `blockOrdered_id_of_wrongCrossings_eq_empty`, `wrongCrossings_switch`, `mixedSignSum_comm`,
  `twoLambda_eq_zero_of_blockOrdered`, `twoLambda_two`.
* lem:homflyrows — B (fully proved from the other rows; `P_splitUnion` PROVED).
* mp:blocks — `writhe_additive` from B (`writhe_eq_sum_blocks` PROVED; the judge closed
  `sum_restrictCrossings_blocks`); `product` from A's PROVED `joinForest_P`; `sign_preserved` from A's
  statements `IsCleanMarkedJoin.crossingEquiv` + `joinForest_sign`; `realizes` through B's chain
  (root node = the supplied actual diagram, sub-records realized by smoothing away the other block
  inside an actual realization — NO clean-join construction; the only geometry is
  `exists_markedInterval_of_mark`); the judge closed `restrictCrossings_univ_iso`.

Every `sorry` below is a chain lemma listed in PLAN_FINAL.md §3 with its unit. -/

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

/-! ## F. The four bundles (byte-identical to work/drafts/MarkedProducts_statement.lean §F, lines
352-370, 376-395, 401-428, 434-461; the row theorems are proved in §I from the chain of §G-§H) -/

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

/-! ## G. Chain — record level (marks under switch and smoothing, the join basing, blocks) -/

namespace Link

namespace Record

variable {ρ : Record}

/-! ### G.1 Marks survive a switch (B, PROVED; sm-3:1455-1457 "Switching it gives `A^sw` with the same
component number, same marked interval") -/

/-- The same mark on the switched record (definitional: `switch` changes only bits and signs). -/
def Mark.switch (μ : ρ.Mark) (x : ρ.M) : (ρ.switch x).Mark :=
  ⟨μ.comp, μ.gap, μ.gap_comp, μ.gap_none⟩

@[simp] theorem Mark.switch_comp (μ : ρ.Mark) (x : ρ.M) : (μ.switch x).comp = μ.comp := rfl
@[simp] theorem Mark.switch_gap (μ : ρ.Mark) (x : ρ.M) : (μ.switch x).gap = μ.gap := rfl

/-- Transport along the identity isomorphism is the identity on marks. -/
theorem Mark.map_refl (μ : ρ.Mark) : μ.map (RecordIso.refl ρ) = μ := by
  obtain ⟨c, g, hc, hn⟩ := μ
  cases g <;> rfl

/-- Unit J2b (PROVED, B): "In `J(A,B)` it is precisely the corresponding crossing switch"
(sm-3:1457-1458): switching the join at an `A`-occurrence is the join of the switched `A` (identity on
circles and occurrences; bits and signs by `Sum` case analysis on `switch_isOver`/`switch_sgn`). -/
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

/-! ### G.2 The last retained occurrence before a point, the mark of a smoothing (B, PROVED), and the
permutation-level heart of the smoothing commutation (B, units J5/J6).
sm-3:1378-1380 "a smoothing selects the unique resulting component containing the relevant interval";
the four printed cases 1462-1472 are the two branches `gap = none` / `gap = some g` together with whether
the `s₁`-cycle of the interval keeps an occurrence.  `Mark.smoothMark` is the intended WITNESS of the
existential chain lemma `exists_joinRecord_smooth_inl` (G.3); provers may use another. -/

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
emptied.  A crossing-free marked circle stays crossing-free (`Sum.inr`).  Use the spec lemmas
`smoothMark_of_gap_none/some`, never unfold the `match`. -/
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

/-- Unit J5 (sub-chain of J4, shared toolbox): if the `f`-cycle of `a` has a retained point, with `a'`
the last retained point at or before `a`: `firstReturn (f * swap a b) p = firstReturn f p * swap a' b`
(from `a'` the reconnected walk passes `a`, jumps to `f b` and returns as `f` from `b`; from `b` it
jumps to `f a` and returns as `f` from `a'`; every other retained point never meets `a` before its
return, `mul_swap_pow_apply_of_forall_ne`).  Generalises `firstReturn_mul_swap` (SM/Stack.lean:345) to
an unretained swap point. -/
theorem firstReturn_mul_swap_of_lastKeep_some {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p] (a b : α) (hb : p b)
    {a' : {v // p v}} (ha' : lastKeep f p a = some a') :
    firstReturn (f * Equiv.swap a b) p = firstReturn f p * Equiv.swap a' ⟨b, hb⟩ := by
  sorry

/-- Unit J6 (sub-chain of J4): if the `f`-cycle of `a` has no retained point, the swap is invisible to
the first return (the whole emptied cycle is inserted after `b`). -/
theorem firstReturn_mul_swap_of_lastKeep_none {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p] (a b : α) (hb : p b)
    (ha : lastKeep f p a = none) :
    firstReturn (f * Equiv.swap a b) p = firstReturn f p := by
  sorry

/-! ### G.3 Mark-compatible based orders, the join of based orders, symmetry and smoothing of a join
(units J1-J4; A's existential statements) -/

/-- "In EACH factor put the marked component first and base it at its marked gap" (sm-3:1440-1441):
a based order compatible with a mark. -/
structure RBasing.MarkCompatible (B : RBasing ρ) (μ : ρ.Mark) : Prop where
  /-- the marked circle has the least rank -/
  rank_lt : ∀ c, c ≠ μ.comp → B.rank μ.comp < B.rank c
  /-- the base occurrence of the marked circle is the one just after the gap -/
  base_gap : ∀ g, μ.gap = some g → B.base g = ρ.succ g

/-- Unit J1 (PROVED by the judge): every mark admits a compatible based order ("New orders and
basepoints can be chosen", sm-3:1099; rank `μ.comp ↦ 0`, others `equivFin + 1`; base `succ g` on the
marked circle, `RBasing.default` elsewhere). -/
theorem exists_markCompatible_rbasing (μ : ρ.Mark) : ∃ B : RBasing ρ, B.MarkCompatible μ := by
  classical
  let B₀ := RBasing.default ρ
  refine ⟨{ rank := fun c => if c = μ.comp then 0 else (Fintype.equivFin ρ.comps c).val + 1
            rank_inj := ?_
            base := fun v => if ρ.comp v = μ.comp then μ.gap.elim v (fun g => ρ.succ g) else B₀.base v
            base_comp := ?_
            base_const := ?_ }, ?_, ?_⟩
  · intro c c' h
    simp only at h
    by_cases h1 : c = μ.comp <;> by_cases h2 : c' = μ.comp
    · rw [h1, h2]
    · rw [ite_eq_left h1, ite_eq_right h2] at h; omega
    · rw [ite_eq_right h1, ite_eq_left h2] at h; omega
    · rw [ite_eq_right h1, ite_eq_right h2] at h
      exact (Fintype.equivFin ρ.comps).injective (Fin.val_injective (by omega))
  · intro v
    show ρ.comp (if ρ.comp v = μ.comp then μ.gap.elim v (fun g => ρ.succ g) else B₀.base v) = ρ.comp v
    by_cases hv : ρ.comp v = μ.comp
    · rw [ite_eq_left hv]
      rcases hg : μ.gap with _ | g
      · rfl
      · show ρ.comp (ρ.succ g) = ρ.comp v
        rw [ρ.succ_comp, μ.gap_comp g hg, hv]
    · rw [ite_eq_right hv]
      exact B₀.base_comp v
  · intro v w hvw
    show (if ρ.comp v = μ.comp then μ.gap.elim v (fun g => ρ.succ g) else B₀.base v) =
      (if ρ.comp w = μ.comp then μ.gap.elim w (fun g => ρ.succ g) else B₀.base w)
    by_cases hv : ρ.comp v = μ.comp
    · have hw : ρ.comp w = μ.comp := hvw.symm.trans hv
      rw [ite_eq_left hv, ite_eq_left hw]
      rcases hg : μ.gap with _ | g
      · exact absurd hv (μ.gap_none hg v)
      · rfl
    · have hw : ¬ ρ.comp w = μ.comp := fun h => hv (hvw.trans h)
      rw [ite_eq_right hv, ite_eq_right hw]
      exact B₀.base_const v w hvw
  · intro c hc
    show (if μ.comp = μ.comp then 0 else (Fintype.equivFin ρ.comps μ.comp).val + 1) <
      (if c = μ.comp then 0 else (Fintype.equivFin ρ.comps c).val + 1)
    rw [ite_eq_left rfl, ite_eq_right hc]
    omega
  · intro g hg
    show (if ρ.comp g = μ.comp then μ.gap.elim g (fun g => ρ.succ g) else B₀.base g) = ρ.succ g
    rw [ite_eq_left (μ.gap_comp g hg), hg]
    rfl

variable {ρ₁ ρ₂ : Record}

/-- Unit J2a (PROVED by the judge): the marked join is symmetric up to named isomorphism ("If the
selected bad crossing is in `B`, the identical argument with the two factor names interchanged
applies", sm-3:1487-1489): `Φ = Sum.swap` on occurrences; on circles the joined circle of `A` goes to
the marked circle of `B`, the other circles of `A` become unmarked circles on `B`'s side and the
unmarked circles of `B` become circles of `B` (`joinComp_inr_of_eq/of_ne`, `joinSucc_*`, `gapSwap_*`). -/
theorem joinRecord_comm (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) :
    Nonempty (RecordIso (joinRecord μ₁ μ₂) (joinRecord μ₂ μ₁)) := by
  have hswap : ∀ v, Sum.swap (joinSucc μ₁ μ₂ v) = joinSucc μ₂ μ₁ (Sum.swap v) := by
    intro v
    unfold joinSucc
    have hs : ∀ w : ρ₁.M ⊕ ρ₂.M, Sum.swap (sumSucc ρ₁ ρ₂ w) = sumSucc ρ₂ ρ₁ (Sum.swap w) := by
      rintro (x | y) <;> rfl
    rcases hg₁ : μ₁.gap with _ | g₁ <;> rcases hg₂ : μ₂.gap with _ | g₂
    · rw [gapSwap_none_left, gapSwap_none_left, mul_one, mul_one, hs]
    · rw [gapSwap_none_left, gapSwap_none_right, mul_one, mul_one, hs]
    · rw [gapSwap_none_right, gapSwap_none_left, mul_one, mul_one, hs]
    · rw [gapSwap_some_some, gapSwap_some_some, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hs]
      congr 1
      rcases v with x | y
      · by_cases hx : x = g₁
        · subst hx
          rw [Equiv.swap_apply_left]
          show Sum.inl g₂ = Equiv.swap (Sum.inl g₂) (Sum.inr x) (Sum.inr x)
          rw [Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne (fun h => hx (Sum.inl.inj h)) Sum.inl_ne_inr]
          show Sum.inr x = Equiv.swap (Sum.inl g₂) (Sum.inr g₁) (Sum.inr x)
          rw [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => hx (Sum.inr.inj h))]
      · by_cases hy : y = g₂
        · subst hy
          rw [Equiv.swap_apply_right]
          show Sum.inr g₁ = Equiv.swap (Sum.inl y) (Sum.inr g₁) (Sum.inl y)
          rw [Equiv.swap_apply_left]
        · rw [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => hy (Sum.inr.inj h))]
          show Sum.inl y = Equiv.swap (Sum.inl g₂) (Sum.inr g₁) (Sum.inl y)
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => hy (Sum.inl.inj h)) Sum.inl_ne_inr]
  -- the circle bijection, abstracted behind its three defining equations
  obtain ⟨e, he1, he2, he3⟩ : ∃ e : ρ₁.comps ⊕ μ₂.Unmarked ≃ ρ₂.comps ⊕ μ₁.Unmarked,
      e (Sum.inl μ₁.comp) = Sum.inl μ₂.comp ∧
      (∀ c (h : c ≠ μ₁.comp), e (Sum.inl c) = Sum.inr ⟨c, h⟩) ∧
      (∀ c : μ₂.Unmarked, e (Sum.inr c) = Sum.inl c.1) := by
    refine ⟨{ toFun := Sum.elim
                (fun c => if h : c = μ₁.comp then Sum.inl μ₂.comp else Sum.inr ⟨c, h⟩)
                (fun c => Sum.inl c.1)
              invFun := Sum.elim
                (fun c => if h : c = μ₂.comp then Sum.inl μ₁.comp else Sum.inr ⟨c, h⟩)
                (fun c => Sum.inl c.1)
              left_inv := ?_
              right_inv := ?_ }, ?_, ?_, ?_⟩
    · rintro (c | ⟨c, hc⟩)
      · by_cases h : c = μ₁.comp
        · subst h
          rw [Sum.elim_inl, dite_eq_left rfl, Sum.elim_inl, dite_eq_left rfl]
        · rw [Sum.elim_inl, dite_eq_right h]
          rfl
      · show (if h : c = μ₂.comp then Sum.inl μ₁.comp
            else (Sum.inr ⟨c, h⟩ : ρ₁.comps ⊕ μ₂.Unmarked)) = Sum.inr ⟨c, hc⟩
        rw [dite_eq_right hc]
    · rintro (c | ⟨c, hc⟩)
      · by_cases h : c = μ₂.comp
        · subst h
          rw [Sum.elim_inl, dite_eq_left rfl, Sum.elim_inl, dite_eq_left rfl]
        · rw [Sum.elim_inl, dite_eq_right h]
          rfl
      · show (if h : c = μ₁.comp then Sum.inl μ₂.comp
            else (Sum.inr ⟨c, h⟩ : ρ₂.comps ⊕ μ₁.Unmarked)) = Sum.inr ⟨c, hc⟩
        rw [dite_eq_right hc]
    · show (if h : μ₁.comp = μ₁.comp then Sum.inl μ₂.comp
          else (Sum.inr ⟨μ₁.comp, h⟩ : ρ₂.comps ⊕ μ₁.Unmarked)) = Sum.inl μ₂.comp
      rw [dite_eq_left rfl]
    · intro c h
      show (if h : c = μ₁.comp then Sum.inl μ₂.comp
          else (Sum.inr ⟨c, h⟩ : ρ₂.comps ⊕ μ₁.Unmarked)) = Sum.inr ⟨c, h⟩
      rw [dite_eq_right h]
    · intro c
      rfl
  refine ⟨{ e := e, Φ := Equiv.sumComm _ _, comp_eq := ?_, succ_eq := fun v => hswap v,
            pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }⟩
  · rintro (a | b)
    · show joinComp μ₂ μ₁ (Sum.inr a) = e (Sum.inl (ρ₁.comp a))
      by_cases h : ρ₁.comp a = μ₁.comp
      · rw [joinComp_inr_of_eq μ₂ μ₁ a h, h, he1]
      · rw [joinComp_inr_of_ne μ₂ μ₁ a h, he2 _ h]
    · show Sum.inl (ρ₂.comp b) = e (joinComp μ₁ μ₂ (Sum.inr b))
      by_cases h : ρ₂.comp b = μ₂.comp
      · rw [joinComp_inr_of_eq μ₁ μ₂ b h, he1, h]
      · rw [joinComp_inr_of_ne μ₁ μ₂ b h]
        exact (he3 ⟨ρ₂.comp b, h⟩).symm
  · rintro (a | b) <;> rfl
  · rintro (a | b) <;> rfl
  · rintro (a | b) <;> rfl

/-- Unit J3: the base case (sm-3:1443-1451): "traverse the joined component starting just before the
`A` portion, then its `B` portion. Traverse the remaining `A` components in their chosen order, then
the remaining `B` components … the relative order of all visits is the same as in its factor
traversal … There are no crossings with one visit in each factor. Thus the entire joined diagram is
UNDER-first."  Witness (B's `RBasing.join`, Skeleton_B.lean:668): rank `inl c ↦ if c = μ₁.comp then 0
else 2·B₁.rank c + 2`, `inr c ↦ 2·B₂.rank c + 1`; base `inl (B₁.base a)` on `A`'s circles and on the
joined circle (`inr (B₂.base b)` when `A`'s marked circle is crossing-free), `inr (B₂.base b)` on `B`'s
unmarked circles; positions `pos (inl a) = B₁.pos a`, `pos (inr b) = |marked circle of A| + B₂.pos b`
on the joined circle.  Only existence is needed, so any UNDER-first based order of the join works. -/
theorem exists_rUnderFirst_joinRecord (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)
    (h₁ : B₁.RUnderFirst) (h₂ : B₂.RUnderFirst) (hμ₁ : B₁.MarkCompatible μ₁)
    (hμ₂ : B₂.MarkCompatible μ₂) :
    ∃ B : RBasing (joinRecord μ₁ μ₂), B.RUnderFirst := by
  sorry

/-- Unit J4 (the critical path of mp:join): "In the joint diagram, smoothing has exactly the record of
`J(A⁰,B)`: both operations are recombinations at disjoint incoming/outgoing ends. All other successor
relations and all other crossings are unchanged" (sm-3:1458-1462), with the four cases self/mixed ×
marked/unmarked (1462-1472) absorbed in the choice of the new mark `μ₀` on `ρ₁.smooth a` (intended
witness `μ₁.smoothMark a`, G.2).  Occurrences: `{v : M₁ ⊕ M₂ // v ∉ {inl a, inl τa}} ≃
{w : M₁ // w ∉ {a, τa}} ⊕ M₂`; successor: `joinSucc μ₁ μ₂ * swap (inl a) (inl τa) =
sumCongr (reconnect a) s₂ * gapSwap (μ₁.gap.map σ) μ₂.gap` (conjugation), then J5/J6 with the retained
swap point `inr g₂`; circles: cycles of left points ↦ `s₁`-cycles, the merged cycle ↦ the marked
circle of the smoothing, right cycles ↦ unmarked circles of `B`, free circles ↦ free circles
(`Equiv.ofBijective` / `Quotient.lift`, or a `RecordIso.ofOcc` helper, PLAN_FINAL §4). -/
theorem exists_joinRecord_smooth_inl (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (a : ρ₁.M) :
    ∃ μ₀ : (ρ₁.smooth a).Mark,
      Nonempty (RecordIso ((joinRecord μ₁ μ₂).smooth (Sum.inl a)) (joinRecord μ₀ μ₂)) := by
  sorry

/-! ### G.4 The blocks of the interlacement graph partition the occurrences; restriction to every
crossing (mp:blocks `writhe_additive`, `realizes`; no geometry) -/

/-- Unit K3 (PROVED by the judge): summing a function of the occurrences block by block (through the
retained subtypes of `restrictCrossings H.supp`) is summing it once: each occurrence lies in exactly
the block of its crossing (`ConnectedComponent.mem_supp_iff`, `Finset.sum_fiberwise`). -/
theorem sum_restrictCrossings_blocks (ρ : Record) (g : ρ.M → ℤ) :
    ∑ H : ρ.interlacementGraph.ConnectedComponent,
      ∑ v : (ρ.restrictCrossings H.supp).M, g v.1 = ∑ v, g v := by
  classical
  have h1 : ∀ H : ρ.interlacementGraph.ConnectedComponent,
      ∑ v : (ρ.restrictCrossings H.supp).M, g v.1 =
        ∑ v ∈ Finset.univ.filter
          (fun v => ρ.interlacementGraph.connectedComponentMk (ρ.crossingOf v) = H), g v := by
    intro H
    show ∑ v : {v : ρ.M // ρ.CrossKeep H.supp v}, g v.1 = _
    symm
    refine Finset.sum_subtype _ (fun v => ?_) g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, CrossKeep,
      SimpleGraph.ConnectedComponent.mem_supp_iff]
  rw [Finset.sum_congr rfl (fun H _ => h1 H)]
  exact Finset.sum_fiberwise Finset.univ
    (fun v => ρ.interlacementGraph.connectedComponentMk (ρ.crossingOf v)) g

/-- The writhe of a record is the sum of the writhes of its interlacement blocks (B, PROVED). -/
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

/-- "both endpoints of `b` lie in one cyclic gap between successive endpoints of `A`" (sm-3:1645-1646),
for sets of crossings `S₁ ⊆ S`: every occurrence of `S` outside `S₁` lies strictly between one
`S₁`-occurrence `u` and its `S₁`-first return (measured by `steps` along `succ`). -/
def GapContiguous (ρ : Record) (S₁ S : Set ρ.Crossing) : Prop :=
  ∃ u : ρ.M, ∃ hu : ρ.CrossKeep S₁ u, ∀ v, ρ.CrossKeep S v → ¬ ρ.CrossKeep S₁ v →
    ρ.ArcBetween u v ((ρ.restrictCrossings S₁).succ ⟨u, hu⟩).1

/-- Unit B4 (PROVED by the judge): restricting to every crossing changes nothing (cf. `restrictUnivIso`,
SM/LinkRecord.lean:1190). -/
theorem restrictCrossings_univ_iso (ρ : Record) :
    Nonempty (RecordIso (ρ.restrictCrossings Set.univ) ρ) :=
  ⟨{ e := Equiv.refl _
     Φ := Equiv.subtypeUnivEquiv (fun _ => Set.mem_univ _)
     comp_eq := fun _ => rfl
     succ_eq := fun v =>
       firstReturn_apply_of_mem ρ.succ (ρ.CrossKeep Set.univ) v (Set.mem_univ _)
     pair_eq := fun _ => rfl
     bit_eq := fun _ => rfl
     sgn_eq := fun _ => rfl }⟩

end Record

/-! ### G.5 Diagram-level bookkeeping for mp:lowest (B; the judge closed L3, L4, L5, L9, L10) -/

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

/-- Unit L3 (PROVED by the judge): no wrong crossing ⇒ the identity block function is block-ordered
(each component its own block). -/
theorem blockOrdered_id_of_wrongCrossings_eq_empty (h : D.wrongCrossings = ∅) :
    BlockOrdered D (id : Fin D.Γ.c → Fin D.Γ.c) := by
  intro x s t hs ht hlt
  have hx : ¬ (D.overStrand x).1 < (D.underStrand x).1 := by
    rw [← D.mem_wrongCrossings, h]
    exact Finset.notMem_empty x
  rcases (D.mem_iff x s).mp hs with rfl | rfl
  · rcases (D.mem_iff x t).mp ht with rfl | rfl
    · exact absurd hlt (lt_irrefl _)
    · exact absurd hlt hx
  · rfl

/-- Unit L4 (PROVED by the judge): switching a wrong crossing removes exactly it from the wrong set. -/
theorem wrongCrossings_switch {x : D.Γ.Crossing} (hx : x ∈ D.wrongCrossings) :
    (D.switch x).wrongCrossings = D.wrongCrossings.erase x := by
  have hx' := (D.mem_wrongCrossings x).mp hx
  refine Finset.ext_iff.mpr fun (y : D.Γ.Crossing) => ?_
  refine ((D.switch x).mem_wrongCrossings y).trans ?_
  refine Iff.trans ?_ (Finset.mem_erase (s := D.wrongCrossings) (a := y) (b := x)).symm
  rw [D.mem_wrongCrossings y]
  by_cases hyx : y = x
  · subst hyx
    rw [switch_overStrand_self, switch_underStrand_self]
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_lt]
    exact hx'.le
  · rw [switch_overStrand_of_ne D hyx, switch_underStrand_of_ne D hyx]
    exact ⟨fun h => ⟨hyx, h⟩, fun h => h.2⟩

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

/-- Unit L5 (PROVED by the judge): `ℓ_ij = ℓ_ji` — each mixed crossing is one ordered strand pair in
either order (`Finset.pair_comm`). -/
theorem mixedSignSum_comm (D : Diagram) (i j : Fin D.Γ.c) : mixedSignSum D i j = mixedSignSum D j i := by
  unfold mixedSignSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : D.Γ.MixedPair i j b a
  · have h' : D.Γ.MixedPair j i a b := ⟨h.2.1, h.1, by rw [Finset.pair_comm]; exact h.2.2⟩
    rw [dite_eq_left h, dite_eq_left h']
    have e : (⟨{b, a}, h.2.2⟩ : D.Γ.Crossing) = ⟨{a, b}, h'.2.2⟩ := Subtype.ext (Finset.pair_comm _ _)
    rw [e]
  · have h' : ¬ D.Γ.MixedPair j i a b := fun h' =>
      h ⟨h'.2.1, h'.1, by rw [Finset.pair_comm]; exact h'.2.2⟩
    rw [dite_eq_right h, dite_eq_right h']

/-- Unit L6: the mixed sign sum of a pair not met by `x` is unchanged by switching `x`
(`switch_sign_of_ne`: the crossing `⟨{s, t}, _⟩ ≠ x` because a strand of `x` has component `∉ {i, j}`
or the pair is the wrong way round). -/
theorem mixedSignSum_switch_of_not_mem (D : Diagram) (x : D.Γ.Crossing) (i j : Fin D.Γ.c)
    (h : ¬ ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∧
      ¬ ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)) :
    mixedSignSum (D.switch x) i j = mixedSignSum D i j := by
  sorry

/-- Unit L7: "The switch from positive to negative changes one mixed sign from `+1` to `−1`"
(sm-3:1605-1606): the mixed sign sum of the pair met by `x` drops by `2σ(x)` (`switch_sign_self` at
the unique ordered pair `(s, t)` with `{s, t} = x.val`, `s.1 = i`, `t.1 = j`; `switch_sign_of_ne`
elsewhere; `Finset.sum_erase`/`Fintype.sum_eq_single` twice, `crossing_pair_spec`). -/
theorem mixedSignSum_switch_of_mem (D : Diagram) (x : D.Γ.Crossing) (i j : Fin D.Γ.c) (hij : i ≠ j)
    (h : ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
      ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)) :
    mixedSignSum (D.switch x) i j = mixedSignSum D i j - 2 * (D.sign x : ℤ) := by
  sorry

/-- Unit L8: "and hence changes `Λ` by `−1`" (doubled): `2Λ(D^sw) = 2Λ(D) − 2σ(x)` at a mixed crossing
(L6, L7 on the double sum `∑ i ∑ j, if i < j`; only the pair `(min, max)` of the two strand components
of `x` changes). -/
theorem twoLambda_switch (D : Diagram) {x : D.Γ.Crossing}
    (hx : (D.overStrand x).1 ≠ (D.underStrand x).1) :
    twoLambda (D.switch x) = twoLambda D - 2 * (D.sign x : ℤ) := by
  sorry

/-- Unit L9 (PROVED by the judge): "By Lemma mp:zero-link every pair of final components has linking
number zero, hence final `Λ = 0`" (sm-3:1612-1614): `SM.zero_link.over_constant` (second disjunct) for
every pair `i < j`. -/
theorem twoLambda_eq_zero_of_blockOrdered (D : Diagram) (h : BlockOrdered D (id : Fin D.Γ.c → Fin D.Γ.c)) :
    twoLambda D = 0 := by
  unfold twoLambda
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hij
  · unfold twoLinking
    apply SM.zero_link.over_constant D i j (ne_of_lt hij)
    right
    intro s t hm
    have hs : s ∈ (⟨{s, t}, hm.2.2⟩ : D.Γ.Crossing).val := Finset.mem_insert_self s {t}
    have ht : t ∈ (⟨{s, t}, hm.2.2⟩ : D.Γ.Crossing).val :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
    have hu : D.underStrand ⟨{s, t}, hm.2.2⟩ = s :=
      h ⟨{s, t}, hm.2.2⟩ s t hs ht (by simp only [id]; rw [hm.1, hm.2.1]; exact hij)
    symm
    apply D.eq_over_of_mem_of_ne ⟨{s, t}, hm.2.2⟩ ht
    rw [hu]
    intro hts
    exact ne_of_lt hij (by rw [← hm.1, ← hm.2.1, hts])
  · rfl

/-- Unit L10 (PROVED by the judge): with two components, `2Λ = 2ℓ_ij` for the two components `i ≠ j`
(`mixedSignSum_comm`). -/
theorem twoLambda_two (D : Diagram) (i j : Fin D.Γ.c) (h2 : D.componentCount = 2) (hij : i ≠ j) :
    twoLambda D = twoLinking D i j := by
  classical
  have huniv : ({i, j} : Finset (Fin D.Γ.c)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    exact h2.le
  unfold twoLambda
  rw [← huniv, Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij,
    ite_eq_right (lt_irrefl i), ite_eq_right (lt_irrefl j)]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h.le)]
    ring
  · rw [ite_eq_right (not_lt.mpr h.le), ite_eq_left h]
    unfold twoLinking
    rw [mixedSignSum_comm D j i]
    ring

end Link

/-! ## H. Chain — polynomial level -/

/-! ### H.1 Rows of `a`-monomial multiples and of `δ^n` multiples (B, all PROVED; mp:lowest,
lem:homflyrows) -/

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

/-! ### H.2 mp:join — the base case, the two steps, the two inductions (A, all PROVED from G.1-G.3) -/

namespace Link

theorem optionMap_eq_self {α : Type} (f : α → α) (hf : ∀ x, f x = x) (o : Option α) : o.map f = o := by
  cases o <;> simp [hf]

/-- eq. mp:join-base (sm-3:1451-1453): both factors UNDER-first ⇒ the join is UNDER-first ⇒
`P_J = δ^{c(A)+c(B)−2} = δ^{c(A)−1} δ^{c(B)−1} = P_A P_B`. -/
theorem P_join_init (A Bd : Diagram) (BA : Record.RBasing A.record) (BB : Record.RBasing Bd.record)
    (μA : A.record.Mark) (μB : Bd.record.Mark) (hA : BA.RUnderFirst) (hB : BB.RUnderFirst)
    (hμA : BA.MarkCompatible μA) (hμB : BB.MarkCompatible μB) (J : Diagram)
    (ι : RecordIso J.record (Record.joinRecord μA μB)) : P J = P A * P Bd := by
  obtain ⟨BJ, hBJ⟩ := Record.exists_rUnderFirst_joinRecord BA BB μA μB hA hB hμA hμB
  obtain ⟨B₁, hB₁⟩ := J.exists_underFirst_of_rUnderFirst (BJ.map ι.symm)
    ((BJ.rUnderFirst_map ι.symm).mpr hBJ)
  obtain ⟨B₂, hB₂⟩ := A.exists_underFirst_of_rUnderFirst BA hA
  obtain ⟨B₃, hB₃⟩ := Bd.exists_underFirst_of_rUnderFirst BB hB
  rw [P_underFirst_init J B₁ hB₁, P_underFirst_init A B₂ hB₂, P_underFirst_init Bd B₃ hB₃, ← pow_add]
  congr 1
  have hc : J.componentCount = A.componentCount + Bd.componentCount - 1 := by
    have h1 := ι.componentCount_eq
    rw [Diagram.record_componentCount, Record.componentCount_joinRecord,
      Diagram.record_componentCount, Diagram.record_componentCount] at h1
    exact h1
  have := A.componentCount_pos
  have := Bd.componentCount_pos
  omega

/-- The step at a bad occurrence `a` of the LEFT factor (sm-3:1454-1487): switch and smoothing of `J`
at the occurrence `ι⁻¹(inl a)` are the join of the switch / smoothing of `A`; the solved skein on `J`
and on `A` with the two inductive values and `solvedR_mul_left`. -/
theorem P_join_step_left (A Bd : Diagram) (μA : A.record.Mark) (μB : Bd.record.Mark) (a : A.Γ.Visit)
    (J : Diagram) (ι : RecordIso J.record (Record.joinRecord μA μB))
    (ihsw : ∀ μ' : (A.switch a.1).record.Mark, μ'.comp = μA.comp → μ'.gap = μA.gap →
      ∀ J' : Diagram, Nonempty (RecordIso J'.record (Record.joinRecord μ' μB)) →
        P J' = P (A.switch a.1) * P Bd)
    (ihsm : ∀ A₀ : Diagram, IsOrientedSmoothing A a.1 A₀ → ∀ (μ₀ : A₀.record.Mark) (J' : Diagram),
      Nonempty (RecordIso J'.record (Record.joinRecord μ₀ μB)) → P J' = P A₀ * P Bd) :
    P J = P A * P Bd := by
  -- the occurrence of `J` corresponding to `a`
  set v : J.Γ.Visit := ι.Φ.symm (Sum.inl a) with hv
  have hΦv : ι.Φ v = Sum.inl a := ι.Φ.apply_symm_apply _
  -- (1) the switch: `record (J^sw) ≅ (joinRecord μA μB).switch (inl a) ≅ joinRecord μA' μB`
  have hsw : P (J.switch v.1) = P (A.switch a.1) * P Bd := by
    obtain ⟨κ⟩ := Record.joinRecord_switch_inl μA μB a
    let ιA : RecordIso (A.switch a.1).record (A.record.switch a) := A.switchRecordIso a.1 a rfl
    refine ihsw ((μA.switch a).map ιA.symm) rfl ?_ (J.switch v.1) ⟨?_⟩
    · exact optionMap_eq_self _ (fun _ => rfl) _
    · refine (J.switchRecordIso v.1 v rfl).trans ?_
      refine (ι.switch v).trans ?_
      rw [hΦv]
      refine κ.trans ?_
      have := RecordIso.joinRecord ιA.symm (RecordIso.refl Bd.record) (μA.switch a) μB
      rw [Record.Mark.map_refl] at this
      exact this
  -- (2) the smoothing: `record J₀ ≅ (joinRecord μA μB).smooth (inl a) ≅ joinRecord μ₀ μB`
  obtain ⟨J₀, h₀J, ⟨ι₀J⟩⟩ := exists_smoothing_record_visit J v.1 v rfl
  obtain ⟨A₀, h₀A, ⟨ι₀A⟩⟩ := exists_smoothing_record_visit A a.1 a rfl
  obtain ⟨μ₀, ⟨κ₀⟩⟩ := Record.exists_joinRecord_smooth_inl μA μB a
  have hsm : P J₀ = P A₀ * P Bd := by
    refine ihsm A₀ h₀A (μ₀.map ι₀A.symm) J₀ ⟨?_⟩
    refine ι₀J.trans ?_
    refine (ι.smooth v).trans ?_
    rw [hΦv]
    refine κ₀.trans ?_
    have := RecordIso.joinRecord ι₀A.symm (RecordIso.refl Bd.record) μ₀ μB
    rw [Record.Mark.map_refl] at this
    exact this
  -- (3) the sign of the crossing is the sign in `A`
  have hsign : J.sign v.1 = A.sign a.1 := by
    have h1 := ι.sgn_eq v
    rw [hΦv] at h1
    exact h1.symm
  have hpos : J.IsPositive v.1 ↔ A.IsPositive a.1 := by
    rw [J.isPositive_iff_sign_eq_one, A.isPositive_iff_sign_eq_one, hsign]
  -- (4) the solved skein on `J` and on `A`
  have eJ := solvedR_of_skein (fun _ _ _ h => P_skein h) h₀J
  have eA := solvedR_of_skein (fun _ _ _ h => P_skein h) h₀A
  rw [eJ, hsw, hsm, hpos, mul_comm (P (A.switch a.1)), mul_comm (P A₀), solvedR_mul_left, ← eA,
    mul_comm]

/-- The step at a bad occurrence of the RIGHT factor: the left step after `joinRecord_comm`
(sm-3:1487-1489 "the identical argument with the two factor names interchanged"). -/
theorem P_join_step_right (A Bd : Diagram) (μA : A.record.Mark) (μB : Bd.record.Mark) (b : Bd.Γ.Visit)
    (J : Diagram) (ι : RecordIso J.record (Record.joinRecord μA μB))
    (ihsw : ∀ μ' : (Bd.switch b.1).record.Mark, μ'.comp = μB.comp → μ'.gap = μB.gap →
      ∀ J' : Diagram, Nonempty (RecordIso J'.record (Record.joinRecord μA μ')) →
        P J' = P A * P (Bd.switch b.1))
    (ihsm : ∀ B₀ : Diagram, IsOrientedSmoothing Bd b.1 B₀ → ∀ (μ₀ : B₀.record.Mark) (J' : Diagram),
      Nonempty (RecordIso J'.record (Record.joinRecord μA μ₀)) → P J' = P A * P B₀) :
    P J = P A * P Bd := by
  obtain ⟨κ⟩ := Record.joinRecord_comm μA μB
  rw [mul_comm]
  refine P_join_step_left Bd A μB μA b J (ι.trans κ) ?_ ?_
  · intro μ' hc hg J' ⟨ι'⟩
    obtain ⟨κ'⟩ := Record.joinRecord_comm μ' μA
    rw [mul_comm]
    exact ihsw μ' hc hg J' ⟨ι'.trans κ'⟩
  · intro B₀ h₀ μ₀ J' ⟨ι'⟩
    obtain ⟨κ'⟩ := Record.joinRecord_comm μ₀ μA
    rw [mul_comm]
    exact ihsm B₀ h₀ μ₀ J' ⟨ι'.trans κ'⟩

/-- The inner `(N, b)` induction on the right factor with the left factor UNDER-first. -/
theorem P_join_of_underFirst (A : Diagram) (BA : Record.RBasing A.record) (hA : BA.RUnderFirst)
    (μA : A.record.Mark) (hμA : BA.MarkCompatible μA) :
    ∀ (Bd : Diagram) (BB : Record.RBasing Bd.record) (μB : Bd.record.Mark), BB.MarkCompatible μB →
      ∀ J : Diagram, Nonempty (RecordIso J.record (Record.joinRecord μA μB)) → P J = P A * P Bd := by
  intro Bd BB
  refine Diagram.skein_induction_based
    (fun Bd BB => ∀ μB : Bd.record.Mark, BB.MarkCompatible μB →
      ∀ J : Diagram, Nonempty (RecordIso J.record (Record.joinRecord μA μB)) → P J = P A * P Bd)
    ?_ ?_ Bd BB
  · intro Bd BB hB μB hμB J ⟨ι⟩
    exact P_join_init A Bd BA BB μA μB hA hB hμA hμB J ι
  · intro Bd BB b _ ihsw ihsm μB hμB J ⟨ι⟩
    refine P_join_step_right A Bd μA μB b J ι ?_ ?_
    · intro μ' hcomp hgap J' hJ'
      refine ihsw μ' ⟨?_, ?_⟩ J' hJ'
      · intro c hc
        rw [hcomp] at hc ⊢
        exact hμB.rank_lt c hc
      · intro g hg
        rw [hgap] at hg
        exact hμB.base_gap g hg
    · intro B₀ h₀ μ₀ J' hJ'
      obtain ⟨B₀', hB₀'⟩ := Record.exists_markCompatible_rbasing μ₀
      exact ihsm B₀ B₀' h₀ μ₀ hB₀' J' hJ'

/-- The outer `(N, b)` induction on the left factor (sm-3:1438-1442). -/
theorem P_join_aux (A : Diagram) (BA : Record.RBasing A.record) :
    ∀ μA : A.record.Mark, BA.MarkCompatible μA →
      ∀ (Bd : Diagram) (μB : Bd.record.Mark) (J : Diagram),
        Nonempty (RecordIso J.record (Record.joinRecord μA μB)) → P J = P A * P Bd := by
  refine Diagram.skein_induction_based
    (fun A BA => ∀ μA : A.record.Mark, BA.MarkCompatible μA →
      ∀ (Bd : Diagram) (μB : Bd.record.Mark) (J : Diagram),
        Nonempty (RecordIso J.record (Record.joinRecord μA μB)) → P J = P A * P Bd)
    ?_ ?_ A BA
  · intro A BA hA μA hμA Bd μB J hJ
    obtain ⟨BB, hBB⟩ := Record.exists_markCompatible_rbasing μB
    exact P_join_of_underFirst A BA hA μA hμA Bd BB μB hBB J hJ
  · intro A BA a _ ihsw ihsm μA hμA Bd μB J ⟨ι⟩
    refine P_join_step_left A Bd μA μB a J ι ?_ ?_
    · intro μ' hcomp hgap J' hJ'
      refine ihsw μ' ⟨?_, ?_⟩ Bd μB J' hJ'
      · intro c hc
        rw [hcomp] at hc ⊢
        exact hμA.rank_lt c hc
      · intro g hg
        rw [hgap] at hg
        exact hμA.base_gap g hg
    · intro A₀ h₀ μ₀ J' hJ'
      obtain ⟨B₀, hB₀⟩ := Record.exists_markCompatible_rbasing μ₀
      exact ihsm A₀ B₀ h₀ μ₀ hB₀ Bd μB J' hJ'

/-- eq. mp:join-value. -/
theorem join_value_of_iso (A B : MarkedDiagram) (J : Diagram) (h : IsCleanMarkedJoin A B J) :
    P J = P A.D * P B.D := by
  obtain ⟨BA, hBA⟩ := Record.exists_markCompatible_rbasing A.μ
  exact P_join_aux A.D BA A.μ hBA B.D B.μ J h

end Link

/-! ### H.3 mp:lowest — the weight `a^{2Λ}[z^{1−c}]P_D` is switch-invariant at mixed crossings;
reduction to `BlockOrdered D id`; the value there from `SM.stack` (B, all PROVED from G.5) -/

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

/-- The two-component row from `lowest_value` (`twoLambda_two`, `Finset.prod_pair`). -/
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

/-! ### H.4 mp:blocks — forest inductions (no geometry) and the realization chain (B's route,
analysed; the chain lemmas are `sorry`) -/

namespace Link

/-- "Repeated use of Theorem mp:join gives the product value for the constructed diagram"
(sm-3:1675-1676): `JoinForest` induction with `join_value_of_iso` (A, PROVED). -/
theorem joinForest_P {ι : Type} [Fintype ι] (C : ι → Diagram) :
    ∀ (S : Set ι) (J : Diagram), JoinForest C S J → P J = ∏ i ∈ S.toFinset, P (C i) := by
  intro S J h
  induction h with
  | leaf i => simp
  | @join S₁ S₂ A B J hA hB hdisj hJ ihA ihB =>
    rw [join_value_of_iso A B J hJ, ihA, ihB, Set.toFinset_union, Finset.prod_union]
    exact Set.disjoint_toFinset.mpr hdisj

def sigmaUnivEquiv {X : Type} (β : X → Type) : (Σ i : (Set.univ : Set X), β i) ≃ Σ i, β i where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨⟨q.1, trivial⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Unit B2: the crossings of a clean marked join are those of the two factors, with their signs
(`D.Γ.Crossing ≃ D.record.Crossing` via `crossingOf (overVisit x)` / `Crossing.rep`;
`RecordIso.crossingOf_eq`; `(joinRecord μ₁ μ₂).Crossing ≃ ρ₁.Crossing ⊕ ρ₂.Crossing` from
`joinRecord_pair_inl/inr`; signs by `record_sgn`, `sgn_eq`, `joinRecord_sgn_inl/inr` — B's
sub-lemmas `RecordIso.crossingEquiv`, `joinCrossingEquiv`, `joinCrossingEquiv_sgn`,
Skeleton_B.lean:713-738). -/
theorem IsCleanMarkedJoin.crossingEquiv {A B : MarkedDiagram} {J : Diagram} (h : IsCleanMarkedJoin A B J) :
    ∃ φ : A.D.Γ.Crossing ⊕ B.D.Γ.Crossing ≃ J.Γ.Crossing,
      (∀ x, J.sign (φ (Sum.inl x)) = A.D.sign x) ∧ (∀ y, J.sign (φ (Sum.inr y)) = B.D.sign y) := by
  sorry

/-- Unit B3: "Every old crossing is present once, with its old sign" (sm-3:1681-1682), along a forest
(`JoinForest` induction; leaf: `Set.uniqueSingleton`/`Equiv.sigmaUnique`; node: `Equiv.Set.union` on
the disjoint index sets, `Equiv.sigmaSumDistrib`, `IsCleanMarkedJoin.crossingEquiv`). -/
theorem joinForest_sign {ι : Type} (C : ι → Diagram) :
    ∀ (S : Set ι) (J : Diagram), JoinForest C S J →
      ∃ φ : (Σ i : S, (C i).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2 := by
  sorry

/-! ### R1 geometry: a clean disc around a nonsingular interior point of an edge -/

namespace EdgeDisc

theorem cycBetween_rotate {a b c : ℝ} : cycBetween a b c ↔ cycBetween b c a := by
  unfold cycBetween; tauto

/-- Strands agree when their components agree and their labels have the same `val`. -/
theorem strand_ext_val {Γ : Shadow} {e s : Γ.Strand} (h1 : e.1 = s.1) (h2 : e.2.val = s.2.val) :
    e = s := by
  obtain ⟨i, a⟩ := e
  obtain ⟨j, b⟩ := s
  dsimp only at h1 h2
  subst h1
  rw [ZMod.val_injective _ h2]

variable (D : Diagram) (s : D.Γ.Strand) (θ₀ : ℝ)

/-- The centre: the point of the strand `s` at parameter `θ₀`. -/
noncomputable def pt : Plane := D.Γ.edgePt s θ₀

/-- The strands other than `s`. -/
noncomputable def others : Finset D.Γ.Strand := Finset.univ.filter (fun e => e ≠ s)

theorem mem_others (e : D.Γ.Strand) : e ∈ others D s ↔ e ≠ s := by
  simp [others]

theorem others_nonempty : (others D s).Nonempty :=
  ⟨⟨s.1, s.2 - 1⟩, (mem_others D s _).mpr (D.Γ.mk_sub_one_ne s)⟩

/-- An adjacent strand distinct from `s` is `s + 1` or `s - 1`. -/
theorem eq_add_one_or_sub_one_of_adjacent {e : D.Γ.Strand} (h : D.Γ.Adjacent s e) (hne : e ≠ s) :
    e = ⟨s.1, s.2 + 1⟩ ∨ e = ⟨s.1, s.2 - 1⟩ := by
  obtain ⟨i, a, b, rfl, rfl, hab⟩ := h
  rcases hab with h | h | h
  · right
    have hb : b = a - 1 := by rw [sub_eq_iff_eq_add] at h; rw [h]; ring
    rw [hb]
  · exact absurd (by rw [sub_eq_zero] at h; rw [h]) hne
  · left
    have hb : b = a + 1 := by rw [sub_eq_iff_eq_add] at h; rw [h]; ring
    rw [hb]

theorem pt_mem_seg (h0 : 0 ≤ θ₀) (h1 : θ₀ ≤ 1) : pt D s θ₀ ∈ D.Γ.seg s := ⟨θ₀, h0, h1, rfl⟩

/-- **Key clearance lemma**: a nonsingular interior point of `s` lies on no other strand. -/
theorem pt_not_mem_seg_other (h0 : 0 < θ₀) (h1 : θ₀ < 1)
    (hp : ∀ y : D.Γ.Crossing, pt D s θ₀ ≠ D.Γ.crossingPoint y) (e : D.Γ.Strand) (he : e ≠ s) :
    pt D s θ₀ ∉ D.Γ.seg e := by
  intro hmem
  by_cases hadj : D.Γ.Adjacent s e
  · rcases eq_add_one_or_sub_one_of_adjacent D s hadj he with rfl | rfl
    · have h2 : pt D s θ₀ ∈ D.Γ.seg s ∩ D.Γ.seg ⟨s.1, s.2 + 1⟩ :=
        ⟨pt_mem_seg D s θ₀ h0.le h1.le, hmem⟩
      rw [D.generic.seg_inter_succ s, Set.mem_singleton_iff] at h2
      have h3 : D.Γ.edgePt s θ₀ = D.Γ.edgePt s 1 := by rw [D.Γ.edgePt_one]; exact h2
      exact h1.ne (D.generic.edgePt_injective s h3)
    · have h2 : pt D s θ₀ ∈ D.Γ.seg ⟨s.1, s.2 - 1⟩ ∩
          D.Γ.seg ⟨(⟨s.1, s.2 - 1⟩ : D.Γ.Strand).1, (⟨s.1, s.2 - 1⟩ : D.Γ.Strand).2 + 1⟩ := by
        refine ⟨hmem, ?_⟩
        exact (D.Γ.mk_sub_one_add_one s).symm ▸ pt_mem_seg D s θ₀ h0.le h1.le
      rw [D.generic.seg_inter_succ, Set.mem_singleton_iff] at h2
      have h3 : D.Γ.edgePt s θ₀ = D.Γ.edgePt s 0 := by
        rw [D.Γ.edgePt_zero]
        change pt D s θ₀ = D.Γ.tail s
        rw [h2, D.Γ.head_eq_tail_mk_add_one]
        exact congrArg D.Γ.tail (D.Γ.mk_sub_one_add_one s)
      exact h0.ne' (D.generic.edgePt_injective s h3)
  · have hmeet : (D.Γ.seg s ∩ D.Γ.seg e).Nonempty := ⟨_, pt_mem_seg D s θ₀ h0.le h1.le, hmem⟩
    let x : D.Γ.Crossing := ⟨{s, e}, D.Γ.isCrossing_pair hadj hmeet⟩
    apply hp x
    apply D.generic.common_point_unique x
    intro u hu
    change u ∈ ({s, e} : Finset D.Γ.Strand) at hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with hu | hu
    · rw [hu]; exact pt_mem_seg D s θ₀ h0.le h1.le
    · rw [hu]; exact hmem

/-- The clearance radius: the least distance from the centre to a strand other than `s`. -/
noncomputable def r₁ : ℝ :=
  (others D s).inf' (others_nonempty D s) (fun e => Metric.infDist (pt D s θ₀) (D.Γ.seg e))

theorem r₁_nonneg : 0 ≤ r₁ D s θ₀ := by
  unfold r₁
  exact Finset.le_inf' _ _ (fun e _ => Metric.infDist_nonneg)

theorem r₁_pos (h0 : 0 < θ₀) (h1 : θ₀ < 1)
    (hp : ∀ y : D.Γ.Crossing, pt D s θ₀ ≠ D.Γ.crossingPoint y) : 0 < r₁ D s θ₀ := by
  unfold r₁
  rw [Finset.lt_inf'_iff]
  intro e he
  rw [mem_others] at he
  exact ((D.Γ.isClosed_seg e).notMem_iff_infDist_pos ⟨_, D.Γ.tail_mem_seg e⟩).mp
    (pt_not_mem_seg_other D s θ₀ h0 h1 hp e he)

theorem r₁_le_dist {e : D.Γ.Strand} (he : e ≠ s) {q : Plane} (hq : q ∈ D.Γ.seg e) :
    r₁ D s θ₀ ≤ dist (pt D s θ₀) q :=
  (Finset.inf'_le _ ((mem_others D s e).mpr he)).trans (Metric.infDist_le_dist_of_mem hq)

/-- Every vertex is at distance `≥ r₁` from the centre. -/
theorem r₁_le_dist_tail (e : D.Γ.Strand) : r₁ D s θ₀ ≤ dist (pt D s θ₀) (D.Γ.tail e) := by
  by_cases he : (⟨e.1, e.2 - 1⟩ : D.Γ.Strand) = s
  · rw [D.Γ.mk_sub_one_eq_iff] at he
    subst he
    exact r₁_le_dist D s θ₀ (D.Γ.mk_add_one_ne s) (D.Γ.tail_mem_seg _)
  · exact r₁_le_dist D s θ₀ he (D.Γ.tail_mem_seg_pred e)

/-- Every crossing point is at distance `≥ r₁` from the centre (one of its strands is not `s`). -/
theorem r₁_le_dist_crossingPoint (y : D.Γ.Crossing) :
    r₁ D s θ₀ ≤ dist (pt D s θ₀) (D.Γ.crossingPoint y) := by
  by_cases hs : y.fst = s
  · have hne : y.snd ≠ s := by rw [← hs]; exact D.Γ.other_ne y y.fst_mem
    exact r₁_le_dist D s θ₀ hne (D.Γ.crossingPoint_mem y y.snd_mem)
  · exact r₁_le_dist D s θ₀ hs (D.Γ.crossingPoint_mem y y.fst_mem)

/-- The disc radius: half the clearance. -/
noncomputable def rad : ℝ := r₁ D s θ₀ / 2

/-- The disc (a closed ball of the sup metric). -/
noncomputable def disc : Set Plane := Metric.closedBall (pt D s θ₀) (rad D s θ₀)

theorem rad_nonneg : 0 ≤ rad D s θ₀ := by
  unfold rad; linarith [r₁_nonneg D s θ₀]

theorem norm_dir_pos : 0 < ‖D.Γ.dir s‖ := norm_pos_iff.mpr (D.Γ.edge_ne_zero D.generic s)

theorem dist_edgePt_pt (θ : ℝ) :
    dist (D.Γ.edgePt s θ) (pt D s θ₀) = |θ - θ₀| * ‖D.Γ.dir s‖ := D.Γ.dist_edgePt s θ θ₀

/-- The half-width of the arc in edge parameter. -/
noncomputable def ρ : ℝ := rad D s θ₀ / ‖D.Γ.dir s‖

/-- The entering and exiting parameters of the arc. -/
noncomputable def θlo : ℝ := θ₀ - ρ D s θ₀
noncomputable def θhi : ℝ := θ₀ + ρ D s θ₀

theorem ρ_nonneg : 0 ≤ ρ D s θ₀ := div_nonneg (rad_nonneg D s θ₀) (norm_dir_pos D s).le

theorem ρ_mul : ρ D s θ₀ * ‖D.Γ.dir s‖ = rad D s θ₀ :=
  div_mul_cancel₀ _ (norm_dir_pos D s).ne'

theorem edgePt_mem_disc_iff (θ : ℝ) :
    D.Γ.edgePt s θ ∈ disc D s θ₀ ↔ θlo D s θ₀ ≤ θ ∧ θ ≤ θhi D s θ₀ := by
  have he := norm_dir_pos D s
  unfold disc θlo θhi ρ
  rw [Metric.mem_closedBall, dist_edgePt_pt, ← le_div_iff₀ he, abs_sub_le_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem edgePt_mem_ball_iff (θ : ℝ) :
    D.Γ.edgePt s θ ∈ Metric.ball (pt D s θ₀) (rad D s θ₀) ↔ θlo D s θ₀ < θ ∧ θ < θhi D s θ₀ := by
  have he := norm_dir_pos D s
  unfold θlo θhi ρ
  rw [Metric.mem_ball, dist_edgePt_pt, ← lt_div_iff₀ he, abs_sub_lt_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem edgePt_θlo_mem_sphere :
    D.Γ.edgePt s (θlo D s θ₀) ∈ Metric.sphere (pt D s θ₀) (rad D s θ₀) := by
  rw [Metric.mem_sphere, dist_edgePt_pt, θlo, sub_sub_cancel_left, abs_neg,
    abs_of_nonneg (ρ_nonneg D s θ₀), ρ_mul]

theorem edgePt_θhi_mem_sphere :
    D.Γ.edgePt s (θhi D s θ₀) ∈ Metric.sphere (pt D s θ₀) (rad D s θ₀) := by
  rw [Metric.mem_sphere, dist_edgePt_pt, θhi, add_sub_cancel_left,
    abs_of_nonneg (ρ_nonneg D s θ₀), ρ_mul]

section Disc

variable (h0 : 0 < θ₀) (h1 : θ₀ < 1) (hp : ∀ y : D.Γ.Crossing, pt D s θ₀ ≠ D.Γ.crossingPoint y)
include h0 h1 hp

theorem rad_lt_r₁ : rad D s θ₀ < r₁ D s θ₀ := by
  unfold rad; linarith [r₁_pos D s θ₀ h0 h1 hp]

theorem rad_pos : 0 < rad D s θ₀ := by
  unfold rad; linarith [r₁_pos D s θ₀ h0 h1 hp]

theorem isDisc_disc : IsDisc (disc D s θ₀) := isDisc_closedBall _ (rad_pos D s θ₀ h0 h1 hp)

theorem interior_disc : interior (disc D s θ₀) = Metric.ball (pt D s θ₀) (rad D s θ₀) :=
  interior_closedBall _ (rad_pos D s θ₀ h0 h1 hp).ne'

theorem frontier_disc : frontier (disc D s θ₀) = Metric.sphere (pt D s θ₀) (rad D s θ₀) :=
  frontier_closedBall _ (rad_pos D s θ₀ h0 h1 hp).ne'

/-- The trace of `D` inside the closed disc lies on `s`. -/
theorem eq_of_mem_seg_of_mem_disc {e : D.Γ.Strand} {q : Plane} (hq : q ∈ D.Γ.seg e)
    (hU : q ∈ disc D s θ₀) : e = s := by
  by_contra h
  have h1' := r₁_le_dist D s θ₀ h hq
  have h2 : dist (pt D s θ₀) q ≤ rad D s θ₀ := by
    rw [dist_comm]; exact Metric.mem_closedBall.mp hU
  have h3 := rad_lt_r₁ D s θ₀ h0 h1 hp
  linarith

/-- No crossing point lies in the closed disc. -/
theorem crossingPoint_not_mem_disc (y : D.Γ.Crossing) : D.Γ.crossingPoint y ∉ disc D s θ₀ := by
  intro hU
  have h1' := r₁_le_dist_crossingPoint D s θ₀ y
  have h2 : dist (pt D s θ₀) (D.Γ.crossingPoint y) ≤ rad D s θ₀ := by
    rw [dist_comm]; exact Metric.mem_closedBall.mp hU
  have h3 := rad_lt_r₁ D s θ₀ h0 h1 hp
  linarith

/-- No vertex lies in the closed disc. -/
theorem tail_not_mem_disc (e : D.Γ.Strand) : D.Γ.tail e ∉ disc D s θ₀ := by
  intro hU
  have h1' := r₁_le_dist_tail D s θ₀ e
  have h2 : dist (pt D s θ₀) (D.Γ.tail e) ≤ rad D s θ₀ := by
    rw [dist_comm]; exact Metric.mem_closedBall.mp hU
  have h3 := rad_lt_r₁ D s θ₀ h0 h1 hp
  linarith

theorem ρ_pos : 0 < ρ D s θ₀ := div_pos (rad_pos D s θ₀ h0 h1 hp) (norm_dir_pos D s)

theorem θlo_lt_θhi : θlo D s θ₀ < θhi D s θ₀ := by
  unfold θlo θhi; linarith [ρ_pos D s θ₀ h0 h1 hp]

/-- The entering parameter is positive: the tail vertex of `s` is outside the disc. -/
theorem θlo_pos : 0 < θlo D s θ₀ := by
  have h := tail_not_mem_disc D s θ₀ h0 h1 hp s
  rw [← D.Γ.edgePt_zero, edgePt_mem_disc_iff, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact h
  · exfalso
    unfold θhi at h
    linarith [ρ_nonneg D s θ₀]

/-- The exiting parameter is below one: the head vertex of `s` is outside the disc. -/
theorem θhi_lt_one : θhi D s θ₀ < 1 := by
  have h := tail_not_mem_disc D s θ₀ h0 h1 hp ⟨s.1, s.2 + 1⟩
  rw [← D.Γ.head_eq_tail_mk_add_one, ← D.Γ.edgePt_one, edgePt_mem_disc_iff, not_and_or, not_le,
    not_le] at h
  rcases h with h | h
  · exfalso
    unfold θlo at h
    linarith [ρ_nonneg D s θ₀]
  · exact h

theorem θlo_lt_one : θlo D s θ₀ < 1 :=
  (θlo_lt_θhi D s θ₀ h0 h1 hp).trans (θhi_lt_one D s θ₀ h0 h1 hp)

theorem θhi_pos : 0 < θhi D s θ₀ :=
  (θlo_pos D s θ₀ h0 h1 hp).trans (θlo_lt_θhi D s θ₀ h0 h1 hp)

/-- The arc of `D` inside the disc: on `s`, from parameter `θlo` to `θhi`. -/
noncomputable def arc : D.Γ.Arc :=
  ⟨s.1, (s.2, ⟨θlo D s θ₀, (θlo_pos D s θ₀ h0 h1 hp).le, θlo_lt_one D s θ₀ h0 h1 hp⟩),
    (s.2, ⟨θhi D s θ₀, (θhi_pos D s θ₀ h0 h1 hp).le, θhi_lt_one D s θ₀ h0 h1 hp⟩)⟩

theorem arc_i : (arc D s θ₀ h0 h1 hp).i = s.1 := rfl

theorem traversalKey_arc_start :
    traversalKey (arc D s θ₀ h0 h1 hp).start = (s.2.val : ℝ) + θlo D s θ₀ := rfl

theorem mem_arc_iff (q : D.Γ.Pt) :
    (arc D s θ₀ h0 h1 hp).Mem q ↔
      (⟨q.1, q.2.1⟩ : D.Γ.Strand) = s ∧ θlo D s θ₀ ≤ q.2.2.val ∧ q.2.2.val ≤ θhi D s θ₀ :=
  Smoothing.arc_mem_iff_of_same_edge (arc D s θ₀ h0 h1 hp) s.2 _ _ rfl rfl
    (θlo_lt_θhi D s θ₀ h0 h1 hp) q

theorem inner_arc_iff (q : D.Γ.Pt) :
    (arc D s θ₀ h0 h1 hp).Inner q ↔
      (⟨q.1, q.2.1⟩ : D.Γ.Strand) = s ∧ θlo D s θ₀ < q.2.2.val ∧ q.2.2.val < θhi D s θ₀ :=
  Smoothing.arc_inner_iff_of_same_edge (arc D s θ₀ h0 h1 hp) s.2 _ _ rfl rfl
    (θlo_lt_θhi D s θ₀ h0 h1 hp) q

theorem isArc_arc : D.Γ.IsArc (disc D s θ₀) (arc D s θ₀ h0 h1 hp) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun r : TraversalPoint (D.Γ.comp (arc D s θ₀ h0 h1 hp).i).k => r.2.val) h
    exact (θlo_lt_θhi D s θ₀ h0 h1 hp).ne this
  · rw [frontier_disc D s θ₀ h0 h1 hp]
    exact edgePt_θlo_mem_sphere D s θ₀
  · rw [frontier_disc D s θ₀ h0 h1 hp]
    exact edgePt_θhi_mem_sphere D s θ₀
  · intro q hq
    rw [inner_arc_iff D s θ₀ h0 h1 hp] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    rw [interior_disc D s θ₀ h0 h1 hp, Smoothing.eval_eq_edgePt, hq1]
    exact (edgePt_mem_ball_iff D s θ₀ _).mpr ⟨hq2, hq3⟩

theorem clean_disc : Clean (disc D s θ₀) D := by
  refine ⟨?_, ?_⟩
  · intro q hq q' hq' heq
    have hq1 : D.Γ.eval q ∈ Metric.sphere (pt D s θ₀) (rad D s θ₀) := by
      rw [← frontier_disc D s θ₀ h0 h1 hp]; exact hq
    have hq1' : D.Γ.eval q' ∈ Metric.sphere (pt D s θ₀) (rad D s θ₀) := by
      rw [← frontier_disc D s θ₀ h0 h1 hp]; exact hq'
    have hU : D.Γ.eval q ∈ disc D s θ₀ := Metric.sphere_subset_closedBall hq1
    have hU' : D.Γ.eval q' ∈ disc D s θ₀ := Metric.sphere_subset_closedBall hq1'
    have hs := eq_of_mem_seg_of_mem_disc D s θ₀ h0 h1 hp (Smoothing.eval_mem_seg q) hU
    have hs' := eq_of_mem_seg_of_mem_disc D s θ₀ h0 h1 hp (Smoothing.eval_mem_seg q') hU'
    refine Smoothing.Pt_ext (hs.trans hs'.symm) ?_
    rw [Smoothing.eval_eq_edgePt, Smoothing.eval_eq_edgePt, hs, hs'] at heq
    exact D.generic.edgePt_injective s heq
  · intro i
    refine ⟨(0, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
    have h0' : D.Γ.eval ⟨i, (0, ⟨0, le_rfl, zero_lt_one⟩)⟩ = D.Γ.tail ⟨i, 0⟩ :=
      D.Γ.edgePt_zero ⟨i, 0⟩
    rw [h0']
    exact tail_not_mem_disc D s θ₀ h0 h1 hp _

theorem arcCover_arc : D.Γ.ArcCover (disc D s θ₀) {arc D s θ₀ h0 h1 hp} := by
  have hclosed : IsClosed (disc D s θ₀) := Metric.isClosed_closedBall
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact isArc_arc D s θ₀ h0 h1 hp
  · intro q
    constructor
    · intro hq
      have hs := eq_of_mem_seg_of_mem_disc D s θ₀ h0 h1 hp (Smoothing.eval_mem_seg q) hq
      refine ⟨arc D s θ₀ h0 h1 hp, Set.mem_singleton _, ?_⟩
      rw [mem_arc_iff D s θ₀ h0 h1 hp]
      refine ⟨hs, ?_⟩
      rw [Smoothing.eval_eq_edgePt, hs] at hq
      exact (edgePt_mem_disc_iff D s θ₀ _).mp hq
    · rintro ⟨a, ha, hq⟩
      rw [Set.mem_singleton_iff] at ha
      rw [ha] at hq
      exact Smoothing.isArc_eval_mem_of_mem (isArc_arc D s θ₀ h0 h1 hp) hclosed hq
  · intro a ha b hb hab q hqa hqb
    rw [Set.mem_singleton_iff] at ha hb
    exact hab (ha.trans hb.symm)

/-- No crossing occurrence lies on the arc. -/
theorem not_mem_arc_visitPt (v : D.Γ.Visit) : ¬ (arc D s θ₀ h0 h1 hp).Mem (D.visitPt v) := by
  intro h
  have hU := Smoothing.isArc_eval_mem_of_mem (isArc_arc D s θ₀ h0 h1 hp)
    Metric.isClosed_closedBall h
  rw [D.eval_visitPt] at hU
  exact crossingPoint_not_mem_disc D s θ₀ h0 h1 hp v.1 hU

theorem isMarkedInterval_arc : IsMarkedInterval D (arc D s θ₀ h0 h1 hp) :=
  ⟨not_mem_arc_visitPt D s θ₀ h0 h1 hp, disc D s θ₀, isDisc_disc D s θ₀ h0 h1 hp,
    clean_disc D s θ₀ h0 h1 hp, arcCover_arc D s θ₀ h0 h1 hp⟩

/-- Clearance in edge parameter: every occurrence on the strand `s` has its parameter farther than
`ρ` from `θ₀`. -/
theorem ρ_lt_abs_sub (u : D.Γ.Visit) (hu1 : (D.visitPt u).1 = s.1)
    (hu2 : ((D.visitPt u).2.1).val = s.2.val) : ρ D s θ₀ < |(D.visitPt u).2.2.val - θ₀| := by
  have he : (⟨(D.visitPt u).1, (D.visitPt u).2.1⟩ : D.Γ.Strand) = s := strand_ext_val hu1 hu2
  have h1' := r₁_le_dist_crossingPoint D s θ₀ u.1
  rw [← D.eval_visitPt, Smoothing.eval_eq_edgePt, he, dist_comm, dist_edgePt_pt] at h1'
  have h3 := rad_lt_r₁ D s θ₀ h0 h1 hp
  have hn := norm_dir_pos D s
  unfold ρ
  rw [div_lt_iff₀ hn]
  linarith

end Disc

/-- **The packaged geometric lemma**: around a nonsingular interior point `edgePt s θ₀` of a strand
there is a marked interval on `s` (a closed sub-arc of `s` inside a clean disc), entering at the
parameter `θ₀ - ρ`, whose half-width `ρ` is below the parameter distance from `θ₀` to every
occurrence on `s`. -/
theorem exists_markedInterval_edgePt (h0 : 0 < θ₀) (h1 : θ₀ < 1)
    (hp : ∀ y : D.Γ.Crossing, D.Γ.edgePt s θ₀ ≠ D.Γ.crossingPoint y) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : D.Γ.Visit, (D.visitPt u).1 = s.1 → ((D.visitPt u).2.1).val = s.2.val →
        ρ < |(D.visitPt u).2.2.val - θ₀|) ∧
      ∃ I : D.Γ.Arc, IsMarkedInterval D I ∧ I.i = s.1 ∧
        traversalKey I.start = (s.2.val : ℝ) + (θ₀ - ρ) :=
  ⟨ρ D s θ₀, ρ_pos D s θ₀ h0 h1 hp, ρ_lt_abs_sub D s θ₀ h0 h1 hp, arc D s θ₀ h0 h1 hp,
    isMarkedInterval_arc D s θ₀ h0 h1 hp, rfl, rfl⟩

end EdgeDisc

/-- Realization chain, geometric part (D9 sub-obligation; PLAN_FINAL §5; PROVED, unit U-R1): every record
mark of an actual diagram is realized by a printed marked interval — a short clean arc just after the
gap occurrence (or anywhere on a crossing-free marked circle), inside a small clean disc. -/
theorem exists_markedInterval_of_mark (D : Diagram) (μ : D.record.Mark) :
    ∃ I : D.Γ.Arc, IsMarkedInterval D I ∧ I.i = μ.comp ∧ ∀ v, μ.gap = some v ↔ D.IsGapOf I v := by
  rcases hgap : μ.gap with _ | g
  · -- crossing-free marked circle: any interior edge point of its first edge
    have hnone : ∀ v : D.Γ.Visit, D.compOf v ≠ μ.comp := μ.gap_none hgap
    let s : D.Γ.Strand := ⟨μ.comp, 0⟩
    have hp : ∀ y : D.Γ.Crossing, D.Γ.edgePt s (1 / 2) ≠ D.Γ.crossingPoint y := by
      intro y hy
      by_cases hs : s ∈ y.val
      · exact hnone ⟨y, ⟨s, hs⟩⟩ rfl
      · refine D.generic.crossingPoint_not_mem_seg y hs ?_
        rw [← hy]
        exact ⟨1 / 2, by norm_num, by norm_num, rfl⟩
    obtain ⟨ρ, -, -, I, hI, hIi, -⟩ :=
      EdgeDisc.exists_markedInterval_edgePt D s (1 / 2) (by norm_num) (by norm_num) hp
    refine ⟨I, hI, hIi, fun v => ⟨fun h => (Option.some_ne_none v h.symm).elim, fun h => ?_⟩⟩
    exact absurd (h.1.trans hIi) (hnone v)
  · -- marked gap after the occurrence `g`: a point of the edge of `g` just after it
    have hgc : D.compOf g = μ.comp := μ.gap_comp g hgap
    obtain ⟨x, s, hs⟩ := g
    change s.1 = μ.comp at hgc
    -- the parameter of `g` on its strand
    set τ : ℝ := D.crossingParam x hs with hτdef
    have hτ0 : 0 < τ := D.crossingParam_pos x hs
    have hτ1 : τ < 1 := D.crossingParam_lt_one x hs
    -- occurrences on the strand `s`, and their parameters
    let onS : D.Γ.Visit → Prop := fun u => (D.visitPt u).1 = s.1 ∧ ((D.visitPt u).2.1).val = s.2.val
    let par : D.Γ.Visit → ℝ := fun u => (D.visitPt u).2.2.val
    -- the least parameter above `τ` on `s` (or `1`)
    obtain ⟨m, hm1, hτm, hmin⟩ : ∃ m : ℝ, m ≤ 1 ∧ τ < m ∧
        ∀ u, onS u → τ < par u → m ≤ par u := by
      let T : Finset ℝ := insert (1 : ℝ) ((Finset.univ.filter (fun u => onS u ∧ τ < par u)).image par)
      have hTne : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
      refine ⟨T.min' hTne, Finset.min'_le _ _ (Finset.mem_insert_self _ _), ?_, ?_⟩
      · rw [Finset.lt_min'_iff]
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hτ1
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
          exact (Finset.mem_filter.mp hu).2.2
      · intro u h1 h2
        exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem par (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)))
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, θ₀ = (τ + m) / 2 := ⟨_, rfl⟩
    have hθτ : τ < θ₀ := by rw [hθ₀]; linarith
    have hθm : θ₀ < m := by rw [hθ₀]; linarith
    have h0 : 0 < θ₀ := by linarith
    have h1 : θ₀ < 1 := by linarith
    -- the centre is not a crossing point
    have hp : ∀ y : D.Γ.Crossing, D.Γ.edgePt s θ₀ ≠ D.Γ.crossingPoint y := by
      intro y hy
      by_cases hsy : s ∈ y.val
      · have hpar : D.Γ.edgePt s θ₀ = D.Γ.edgePt s (D.crossingParam y hsy) :=
          hy.trans (D.crossingParam_spec y hsy).2.2
        have heq : θ₀ = D.crossingParam y hsy := D.generic.edgePt_injective s hpar
        have hon : onS ⟨y, ⟨s, hsy⟩⟩ := ⟨rfl, rfl⟩
        have hpu : par ⟨y, ⟨s, hsy⟩⟩ = θ₀ := heq.symm
        have := hmin _ hon (by rw [hpu]; exact hθτ)
        rw [hpu] at this
        linarith
      · refine D.generic.crossingPoint_not_mem_seg y hsy ?_
        rw [← hy]
        exact ⟨θ₀, h0.le, h1.le, rfl⟩
    obtain ⟨ρ, hρ, hclear, I, hI, hIi, hIstart⟩ :=
      EdgeDisc.exists_markedInterval_edgePt D s θ₀ h0 h1 hp
    -- the entering parameter lies strictly after `τ`
    have hτs : τ < θ₀ - ρ := by
      have h := hclear ⟨x, ⟨s, hs⟩⟩ rfl rfl
      have hpar : (D.visitPt ⟨x, ⟨s, hs⟩⟩).2.2.val = τ := rfl
      rw [hpar, abs_sub_comm, abs_of_pos (by linarith)] at h
      linarith
    -- no occurrence of the component has coordinate in `(coord g, key I.start]`
    have hC : ∀ w : D.Γ.Visit, D.compOf w = I.i →
        (s.2.val : ℝ) + τ < D.visitCoord w → D.visitCoord w ≤ (s.2.val : ℝ) + (θ₀ - ρ) → False := by
      intro w hw hlt1 hlt2
      have hwc : D.visitCoord w = (((D.visitPt w).2.1).val : ℝ) + par w := rfl
      rw [hwc] at hlt1 hlt2
      have hpw0 : 0 ≤ par w := (D.visitPt w).2.2.2.1
      have hpw1 : par w < 1 := (D.visitPt w).2.2.2.2
      have hb1 : ((D.visitPt w).2.1).val < s.2.val + 1 := by
        have : (((D.visitPt w).2.1).val : ℝ) < (s.2.val : ℝ) + 1 := by linarith
        exact_mod_cast this
      have hb2 : s.2.val < ((D.visitPt w).2.1).val + 1 := by
        have : (s.2.val : ℝ) < (((D.visitPt w).2.1).val : ℝ) + 1 := by linarith
        exact_mod_cast this
      have hb : ((D.visitPt w).2.1).val = s.2.val := by omega
      have hon : onS w := ⟨hw.trans hIi, hb⟩
      have hbR : (((D.visitPt w).2.1).val : ℝ) = (s.2.val : ℝ) := by exact_mod_cast hb
      rw [hbR] at hlt1 hlt2
      have hτw : τ < par w := by linarith
      have := hmin w hon hτw
      linarith
    have hgcoord : D.visitCoord ⟨x, ⟨s, hs⟩⟩ = (s.2.val : ℝ) + τ := rfl
    -- (A): the gap condition for `g`
    have hA : ∀ w : D.Γ.Visit, D.compOf w = I.i →
        ¬ cycBetween (D.visitCoord ⟨x, ⟨s, hs⟩⟩) (D.visitCoord w) (traversalKey I.start) := by
      intro w hw hcyc
      rw [hIstart, hgcoord] at hcyc
      unfold cycBetween at hcyc
      rcases hcyc with ⟨hlt1, hlt2⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact hC w hw hlt1 hlt2.le
      · linarith
      · linarith
    have hsI : s.1 = I.i := hIi.symm
    refine ⟨I, hI, hIi.trans hgc, fun v => ⟨?_, ?_⟩⟩
    · intro hv
      obtain rfl := Option.some.inj hv
      exact ⟨hsI, hA⟩
    · rintro ⟨hvc, hv⟩
      refine congrArg some ?_
      by_contra hne
      have hvg : D.compOf v = s.1 := hvc.trans hIi
      have hne1 : D.visitCoord v ≠ D.visitCoord ⟨x, ⟨s, hs⟩⟩ :=
        fun h => hne (D.visitCoord_injOn hvg h).symm
      have hne2 : D.visitCoord ⟨x, ⟨s, hs⟩⟩ ≠ traversalKey I.start := by
        rw [hgcoord, hIstart]; intro h; linarith
      have hne3 : D.visitCoord v ≠ traversalKey I.start := by
        intro h
        refine hC v hvc ?_ ?_
        · rw [h, hIstart]; linarith
        · rw [h, hIstart]
      rcases cycBetween_or_of_ne hne1 hne2 hne3 with h | h
      · exact hv ⟨x, ⟨s, hs⟩⟩ hsI h
      · exact hA v hvc (EdgeDisc.cycBetween_rotate.mp (EdgeDisc.cycBetween_rotate.mp h))

/-- Realization chain, record part 1 (ANALYSED ONLY, PLAN_FINAL §5): smoothing away the crossings of
`S \ S₁` when they lie in one gap of `S₁` (`GapContiguous`) leaves the `S₁`-first-return successor
unchanged and never splits the `S₁`-circle; restricting the resulting actual diagram to that circle
realizes `restrictCrossings S₁`.  Uses only accepted geometry (`exists_smoothing_record_visit`,
`Diagram.restrict`, `restrictRecordIso`) and `firstReturn` lemmas of the J5/J6 type. -/
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
`restrictCrossings_univ_iso` (B, PROVED from the chain). -/
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
diagram with the full record; sm-3:1675-1677). -/
theorem product_of_blockSupply (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram)
    (h : BlockSupply ρ C) (D : Diagram) (hD : Nonempty (RecordIso D.record ρ)) :
    P D = ∏ H, P (C H) := by
  obtain ⟨J, hJ, ⟨ιJ⟩⟩ := realizes_of_blockSupply ρ C h
  obtain ⟨ι⟩ := hD
  rw [presentations D J ⟨ι.trans ιJ.symm⟩, joinForest_P C Set.univ J hJ]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext H
  simp

/-- `writhe_additive` from `writhe_eq_sum_blocks` and the supplied isomorphisms (B, PROVED). -/
theorem writhe_additive_of_blockSupply (ρ : Record)
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (h : BlockSupply ρ C) (D : Diagram)
    (hD : Nonempty (RecordIso D.record ρ)) : D.writhe = ∑ H, (C H).writhe := by
  obtain ⟨ι⟩ := hD
  rw [← D.record_writhe, ι.writhe_eq, Record.writhe_eq_sum_blocks]
  refine Finset.sum_congr rfl fun H _ => ?_
  obtain ⟨ιH⟩ := h.supplied H
  rw [← (C H).record_writhe, ιH.writhe_eq]

/-- `sign_preserved` from the forest lemma at `S = univ`. -/
theorem sign_preserved_of_blockSupply (ρ : Record)
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (_h : BlockSupply ρ C) (J : Diagram)
    (hJ : JoinForest C Set.univ J) :
    ∃ φ : (Σ H : ρ.interlacementGraph.ConnectedComponent, (C H).Γ.Crossing) ≃ J.Γ.Crossing,
      ∀ q, J.sign (φ q) = (C q.1).sign q.2 := by
  obtain ⟨φ, hφ⟩ := joinForest_sign C Set.univ J hJ
  exact ⟨(sigmaUnivEquiv fun H => (C H).Γ.Crossing).symm.trans φ, fun q => hφ _⟩

/-! ### H.5 lem:homflyrows — the split union (B, PROVED) -/

/-- "Theorem mp:stack, with two one-component blocks and no mixed crossings, gives `P_{K⊔J} = δ P_K P_J`"
(sm-4:245-247): `SM.stack.split_union` with the block function `c ↦ if c ∈ B then 0 else 1`,
`restrict_congr`, `presentations`. -/
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

end Link

/-! ## I. The four row theorems from the chain -/

/-- mp:join. -/
theorem join : JoinData where
  join_value := Link.join_value_of_iso
  multi_component_factors := fun A B J _ h => Link.join_value_of_iso A B J h
  crossing_free_marked_component := fun A B J _ h => Link.join_value_of_iso A B J h

/-- mp:lowest. -/
theorem lowest : LowestData where
  lowest_value := lowest_value_of_reduce
  two_component_row := two_component_row_of_lowest

/-- mp:blocks (`realizes` and hence `product` through the analysed chain of §H.4, left `sorry`;
`sign_preserved` through units B2/B3; `writhe_additive` proved). -/
theorem blocks : BlocksData where
  realizes := Link.realizes_of_blockSupply
  product := Link.product_of_blockSupply
  sign_preserved := Link.sign_preserved_of_blockSupply
  writhe_additive := Link.writhe_additive_of_blockSupply

/-- lem:homflyrows. -/
theorem homflyrows : HomflyRowsData where
  connected_sum := fun K J _ _ K' J' D hK hJ h => by
    rw [← P_eq_homfly, Link.join_value_of_iso K' J' D h, P_eq_homfly, P_eq_homfly,
      homfly_descent hK, homfly_descent hJ]
  split_union := fun K J _ _ K' J' D hK hJ h => by
    rw [← P_eq_homfly, Link.P_splitUnion K' J' D h, P_eq_homfly, P_eq_homfly, homfly_descent hK,
      homfly_descent hJ]
  two_component_row := fun D i j h2 hij => by
    have h := two_component_row_of_lowest D i j h2 hij
    rw [← P_eq_homfly, ← P_eq_homfly, ← P_eq_homfly, h,
      CV.zRow_zero_mul_of_inSupportM_one (P_knotRestrict_inSupportM_one D i)
        (P_knotRestrict_inSupportM_one D j)]
    ring

end SM
