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

/-- Realization chain, geometric part (D9 sub-obligation; ANALYSED ONLY, PLAN_FINAL §5): every record
mark of an actual diagram is realized by a printed marked interval — a short clean arc just after the
gap occurrence (or anywhere on a crossing-free marked circle), inside a small clean disc. -/
theorem exists_markedInterval_of_mark (D : Diagram) (μ : D.record.Mark) :
    ∃ I : D.Γ.Arc, IsMarkedInterval D I ∧ I.i = μ.comp ∧ ∀ v, μ.gap = some v ↔ D.IsGapOf I v := by
  sorry

/-- Realization chain, record part 1 (ANALYSED ONLY, PLAN_FINAL §5): smoothing away the crossings of
`S \ S₁` when they lie in one gap of `S₁` (`GapContiguous`) leaves the `S₁`-first-return successor
unchanged and never splits the `S₁`-circle; restricting the resulting actual diagram to that circle
realizes `restrictCrossings S₁`.  Uses only accepted geometry (`exists_smoothing_record_visit`,
`Diagram.restrict`, `restrictRecordIso`) and `firstReturn` lemmas of the J5/J6 type. -/
theorem isRealizable_restrictCrossings_of_gapContiguous (ρ : Record) (h1 : ρ.componentCount = 1)
    {S₁ S : Set ρ.Crossing} (hsub : S₁ ⊆ S) (hS : IsRealizable (ρ.restrictCrossings S))
    (hgap : ρ.GapContiguous S₁ S) : IsRealizable (ρ.restrictCrossings S₁) := by
  sorry

/-! ### Unit U-R3a — R3 parts (a)-(c): the `steps`/`ArcBetween` toolbox on a one-circle record and
the one-gap lemma of the printed mp:blocks proof (sm-3:1637-1663).  PROVED (2026-09-14); consumed by
unit U-R3b (parts (d)-(e) of `restrictCrossings_join_decomp`).  Nothing below changes a fixed
statement or definition; every lemma is sorry-free. -/

namespace Record

/-! ### R3(a): the `steps` / `ArcBetween` toolbox on a one-circle record (unit U-R3a)

On a one-circle record (`componentCount = 1`) every occurrence is reached from every other by
forward `succ`-steps; `steps v w` is then the genuine cyclic distance, `Fintype.card ρ.M` is the
common period, and positions measured from any base point `b` turn `ArcBetween` into the strict
cyclic order `PosBetween` on natural numbers (so that `omega` decides the cyclic-order facts). -/

variable (ρ : Record)

/-- One circle: all occurrences lie on the same parametrizing circle. -/
theorem comp_eq_of_one_circle (h1 : ρ.componentCount = 1) (v w : ρ.M) : ρ.comp v = ρ.comp w :=
  Fintype.card_le_one_iff.mp (le_of_eq h1) _ _

/-- One circle: all occurrences lie on one `succ`-cycle. -/
theorem sameCycle_of_one_circle (h1 : ρ.componentCount = 1) (v w : ρ.M) :
    ρ.succ.SameCycle v w :=
  ρ.succ_cycle v w (ρ.comp_eq_of_one_circle h1 v w)

/-- One circle: every occurrence is a forward power of every other. -/
theorem exists_pow_eq_of_one_circle (h1 : ρ.componentCount = 1) (v w : ρ.M) :
    ∃ n : ℕ, (ρ.succ ^ n) v = w :=
  (ρ.sameCycle_of_one_circle h1 v w).exists_nat_pow_eq

/-- `steps` is a lower bound for every forward power reaching `w` (no circle hypothesis). -/
theorem steps_le_of_pow {v w : ρ.M} {n : ℕ} (h : (ρ.succ ^ n) v = w) : ρ.steps v w ≤ n := by
  unfold steps
  split_ifs with h'
  · exact Nat.find_min' h' h
  · exact absurd ⟨n, h⟩ h'

/-- On one circle `succ ^ steps v w` carries `v` to `w`. -/
theorem pow_steps (h1 : ρ.componentCount = 1) (v w : ρ.M) : (ρ.succ ^ ρ.steps v w) v = w := by
  unfold steps
  split_ifs with h'
  · exact Nat.find_spec h'
  · exact absurd (ρ.exists_pow_eq_of_one_circle h1 v w) h'

/-- Every occurrence is a periodic point of `succ` (the order of `succ` is a period). -/
theorem mem_periodicPts_succ (v : ρ.M) : v ∈ Function.periodicPts ρ.succ :=
  Function.mk_mem_periodicPts (orderOf_pos ρ.succ) (by
    show (ρ.succ ^ orderOf ρ.succ) v = v
    rw [pow_orderOf_eq_one]; rfl)

theorem minimalPeriod_succ_pos (v : ρ.M) : 0 < Function.minimalPeriod ρ.succ v :=
  Function.minimalPeriod_pos_of_mem_periodicPts (ρ.mem_periodicPts_succ v)

/-- On one circle the minimal period of every occurrence is the number of occurrences. -/
theorem minimalPeriod_succ_eq_card (h1 : ρ.componentCount = 1) (v : ρ.M) :
    Function.minimalPeriod ρ.succ v = Fintype.card ρ.M := by
  have hinj : Function.Injective
      (fun i : Fin (Function.minimalPeriod ρ.succ v) => (ρ.succ ^ (i : ℕ)) v) := by
    intro i j hij
    exact Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.2 j.2).mp hij)
  have hsurj : Function.Surjective
      (fun i : Fin (Function.minimalPeriod ρ.succ v) => (ρ.succ ^ (i : ℕ)) v) := by
    intro w
    obtain ⟨n, hn⟩ := ρ.exists_pow_eq_of_one_circle h1 v w
    refine ⟨⟨n % Function.minimalPeriod ρ.succ v, Nat.mod_lt _ (ρ.minimalPeriod_succ_pos v)⟩, ?_⟩
    show (ρ.succ ^ (n % Function.minimalPeriod ρ.succ v)) v = w
    rw [← hn]
    exact Function.iterate_mod_minimalPeriod_eq
  have := Fintype.card_of_bijective ⟨hinj, hsurj⟩
  simpa using this

/-- `succ ^ |M|` is the identity on a one-circle record. -/
theorem pow_card_apply (h1 : ρ.componentCount = 1) (v : ρ.M) :
    (ρ.succ ^ Fintype.card ρ.M) v = v := by
  rw [← ρ.minimalPeriod_succ_eq_card h1 v]
  exact Function.iterate_minimalPeriod

/-- Powers of `succ` may be reduced modulo `|M|` on a one-circle record. -/
theorem pow_mod_card_apply (h1 : ρ.componentCount = 1) (v : ρ.M) (n : ℕ) :
    (ρ.succ ^ (n % Fintype.card ρ.M)) v = (ρ.succ ^ n) v := by
  rw [← ρ.minimalPeriod_succ_eq_card h1 v]
  exact Function.iterate_mod_minimalPeriod_eq

/-- Two powers below `|M|` agree at `v` only when equal (one circle). -/
theorem pow_apply_eq_pow_apply_iff (h1 : ρ.componentCount = 1) (v : ρ.M) {i j : ℕ}
    (hi : i < Fintype.card ρ.M) (hj : j < Fintype.card ρ.M) :
    (ρ.succ ^ i) v = (ρ.succ ^ j) v ↔ i = j := by
  rw [← ρ.minimalPeriod_succ_eq_card h1 v] at hi hj
  exact Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj

theorem card_M_pos (v : ρ.M) : 0 < Fintype.card ρ.M := Fintype.card_pos_iff.mpr ⟨v⟩

/-- The cyclic distance is below the circle length. -/
theorem steps_lt_card (h1 : ρ.componentCount = 1) (v w : ρ.M) :
    ρ.steps v w < Fintype.card ρ.M := by
  obtain ⟨n, hn⟩ := ρ.exists_pow_eq_of_one_circle h1 v w
  have h : (ρ.succ ^ (n % Fintype.card ρ.M)) v = w := by rw [ρ.pow_mod_card_apply h1, hn]
  exact lt_of_le_of_lt (ρ.steps_le_of_pow h) (Nat.mod_lt _ (ρ.card_M_pos v))

/-- Characterisation of `steps` on one circle: the unique power below `|M|` carrying `v` to `w`. -/
theorem steps_eq_iff (h1 : ρ.componentCount = 1) (v w : ρ.M) (n : ℕ) :
    ρ.steps v w = n ↔ n < Fintype.card ρ.M ∧ (ρ.succ ^ n) v = w := by
  constructor
  · rintro rfl
    exact ⟨ρ.steps_lt_card h1 v w, ρ.pow_steps h1 v w⟩
  · rintro ⟨hn, hw⟩
    exact (ρ.pow_apply_eq_pow_apply_iff h1 v (ρ.steps_lt_card h1 v w) hn).mp
      (by rw [ρ.pow_steps h1 v w, hw])

/-- `steps v w` is the residue of any power carrying `v` to `w`. -/
theorem steps_eq_mod (h1 : ρ.componentCount = 1) {v w : ρ.M} {n : ℕ} (h : (ρ.succ ^ n) v = w) :
    ρ.steps v w = n % Fintype.card ρ.M :=
  (ρ.steps_eq_iff h1 v w _).mpr ⟨Nat.mod_lt _ (ρ.card_M_pos v), by rw [ρ.pow_mod_card_apply h1, h]⟩

/-- Positions from a base point are injective. -/
theorem steps_inj (h1 : ρ.componentCount = 1) {b v w : ρ.M} (h : ρ.steps b v = ρ.steps b w) :
    v = w := by
  rw [← ρ.pow_steps h1 b v, ← ρ.pow_steps h1 b w, h]

theorem steps_ne_of_ne (h1 : ρ.componentCount = 1) (b : ρ.M) {v w : ρ.M} (h : v ≠ w) :
    ρ.steps b v ≠ ρ.steps b w := fun h' => h (ρ.steps_inj h1 h')

theorem steps_eq_zero_iff (h1 : ρ.componentCount = 1) (v w : ρ.M) : ρ.steps v w = 0 ↔ v = w := by
  rw [ρ.steps_eq_iff h1]
  constructor
  · rintro ⟨-, h⟩; simpa using h
  · rintro rfl; exact ⟨ρ.card_M_pos v, by simp⟩

theorem steps_pos_iff (h1 : ρ.componentCount = 1) (v w : ρ.M) : 0 < ρ.steps v w ↔ v ≠ w := by
  rw [Nat.pos_iff_ne_zero, not_iff_not]
  exact ρ.steps_eq_zero_iff h1 v w

/-- The transfer formula: the cyclic distance from `u` to `w` in terms of positions from a base
point `b`. -/
theorem steps_eq_of_base (h1 : ρ.componentCount = 1) (b u w : ρ.M) :
    ρ.steps u w = if ρ.steps b u ≤ ρ.steps b w then ρ.steps b w - ρ.steps b u
      else ρ.steps b w + Fintype.card ρ.M - ρ.steps b u := by
  have hu := ρ.pow_steps h1 b u
  have hw := ρ.pow_steps h1 b w
  have hu' := ρ.steps_lt_card h1 b u
  have hw' := ρ.steps_lt_card h1 b w
  have key : (ρ.succ ^ (ρ.steps b w + Fintype.card ρ.M - ρ.steps b u)) u = w := by
    calc (ρ.succ ^ (ρ.steps b w + Fintype.card ρ.M - ρ.steps b u)) u
        = (ρ.succ ^ (ρ.steps b w + Fintype.card ρ.M - ρ.steps b u)) ((ρ.succ ^ ρ.steps b u) b) := by
          rw [hu]
      _ = (ρ.succ ^ (ρ.steps b w + Fintype.card ρ.M - ρ.steps b u + ρ.steps b u)) b := by
          rw [pow_add, Equiv.Perm.mul_apply]
      _ = (ρ.succ ^ (ρ.steps b w + Fintype.card ρ.M)) b := by
          rw [Nat.sub_add_cancel (by omega)]
      _ = w := by rw [pow_add, Equiv.Perm.mul_apply, ρ.pow_card_apply h1, hw]
  rw [ρ.steps_eq_mod h1 key]
  split_ifs with h
  · rw [show ρ.steps b w + Fintype.card ρ.M - ρ.steps b u
        = (ρ.steps b w - ρ.steps b u) + Fintype.card ρ.M by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Strict cyclic betweenness of three positions: `x` lies on the open forward arc from `a` to
`c` (false whenever two of the three coincide). -/
def PosBetween (a x c : ℕ) : Prop := (a < x ∧ x < c) ∨ (x < c ∧ c < a) ∨ (c < a ∧ a < x)

/-- `ArcBetween` measured from any base point `b` is the strict cyclic order of positions. -/
theorem arcBetween_iff_posBetween (h1 : ρ.componentCount = 1) (b v w u : ρ.M) :
    ρ.ArcBetween v w u ↔ PosBetween (ρ.steps b v) (ρ.steps b w) (ρ.steps b u) := by
  unfold ArcBetween PosBetween
  have hv := ρ.steps_lt_card h1 b v
  have hw := ρ.steps_lt_card h1 b w
  have hu := ρ.steps_lt_card h1 b u
  rw [ρ.steps_eq_of_base h1 b v w, ρ.steps_eq_of_base h1 b v u]
  split_ifs <;> omega

/-- `steps_succ_pow`: the distance to a forward power is its residue. -/
theorem steps_pow (h1 : ρ.componentCount = 1) (v : ρ.M) (n : ℕ) :
    ρ.steps v ((ρ.succ ^ n) v) = n % Fintype.card ρ.M :=
  ρ.steps_eq_mod h1 rfl

/-- Trichotomy: of three distinct occurrences on one circle, `w` lies on the arc from `v` to `u`
or `u` lies on the arc from `v` to `w`. -/
theorem arcBetween_or_arcBetween (h1 : ρ.componentCount = 1) {v w u : ρ.M} (hvw : v ≠ w)
    (hvu : v ≠ u) (hwu : w ≠ u) : ρ.ArcBetween v w u ∨ ρ.ArcBetween v u w := by
  rw [ρ.arcBetween_iff_posBetween h1 v, ρ.arcBetween_iff_posBetween h1 v]
  unfold PosBetween
  have := ρ.steps_ne_of_ne h1 v hvw
  have := ρ.steps_ne_of_ne h1 v hvu
  have := ρ.steps_ne_of_ne h1 v hwu
  rw [ρ.steps_self] at *
  omega

/-- Cyclic rotation: `w` between `v` and `u` iff `u` between `w` and `v`. -/
theorem arcBetween_rotate (h1 : ρ.componentCount = 1) (v w u : ρ.M) :
    ρ.ArcBetween v w u ↔ ρ.ArcBetween w u v := by
  rw [ρ.arcBetween_iff_posBetween h1 v, ρ.arcBetween_iff_posBetween h1 v]
  unfold PosBetween
  rw [ρ.steps_self]
  omega

/-- Symmetry of the two open arcs: `w` strictly inside the arc from `v` to `u` iff not inside the
arc from `u` to `v` (for `w` distinct from `v` and `u`, and `v ≠ u`). -/
theorem arcBetween_iff_not_arcBetween (h1 : ρ.componentCount = 1) {v w u : ρ.M} (hvw : v ≠ w)
    (hvu : v ≠ u) (hwu : w ≠ u) : ρ.ArcBetween v w u ↔ ¬ ρ.ArcBetween u w v := by
  rw [ρ.arcBetween_iff_posBetween h1 v, ρ.arcBetween_iff_posBetween h1 v]
  unfold PosBetween
  have := ρ.steps_ne_of_ne h1 v hvw
  have := ρ.steps_ne_of_ne h1 v hvu
  have := ρ.steps_ne_of_ne h1 v hwu
  rw [ρ.steps_self] at *
  omega

end Record

namespace Record

variable (ρ : Record)

/-! ### R3(a), continued: first returns measured by `steps`, and the gaps of a crossing set -/

section FirstReturnSteps

variable (p : ρ.M → Prop) [DecidablePred p]

/-- The return time from `u` is at most the distance to any other `p`-point. -/
theorem returnTime_le_steps (h1 : ρ.componentCount = 1) (u : {m // p m}) {k : ρ.M} (hk : p k)
    (hku : k ≠ u.1) : returnTime ρ.succ p u.1 u.2 ≤ ρ.steps u.1 k := by
  refine not_lt.mp fun hlt => ?_
  have hs : 0 < ρ.steps u.1 k := (ρ.steps_pos_iff h1 _ _).mpr (Ne.symm hku)
  exact returnTime_min ρ.succ p u.1 u.2 hs hlt (by rw [ρ.pow_steps h1]; exact hk)

/-- With another `p`-point present, the distance to the first return is the return time. -/
theorem steps_firstReturn (h1 : ρ.componentCount = 1) (u : {m // p m}) {k : ρ.M} (hk : p k)
    (hku : k ≠ u.1) :
    ρ.steps u.1 (firstReturn ρ.succ p u).1 = returnTime ρ.succ p u.1 u.2 := by
  rw [firstReturn_apply]
  exact (ρ.steps_eq_iff h1 _ _ _).mpr
    ⟨lt_of_le_of_lt (ρ.returnTime_le_steps p h1 u hk hku) (ρ.steps_lt_card h1 _ _), rfl⟩

/-- With another `p`-point present, the first return is not the start. -/
theorem firstReturn_val_ne (h1 : ρ.componentCount = 1) (u : {m // p m}) {k : ρ.M} (hk : p k)
    (hku : k ≠ u.1) : (firstReturn ρ.succ p u).1 ≠ u.1 := by
  intro h
  have h' := ρ.steps_firstReturn p h1 u hk hku
  rw [h, ρ.steps_self] at h'
  exact absurd h'.symm (Nat.pos_iff_ne_zero.mp (returnTime_pos ρ.succ p u.1 u.2))

/-- The first return is the nearest other `p`-point. -/
theorem steps_firstReturn_le (h1 : ρ.componentCount = 1) (u : {m // p m}) {k : ρ.M} (hk : p k)
    (hku : k ≠ u.1) : ρ.steps u.1 (firstReturn ρ.succ p u).1 ≤ ρ.steps u.1 k := by
  rw [ρ.steps_firstReturn p h1 u hk hku]
  exact ρ.returnTime_le_steps p h1 u hk hku

/-- Characterisation of the first return on one circle: the `p`-point other than `u` nearest to
`u` in the forward direction. -/
theorem firstReturn_val_eq_iff (h1 : ρ.componentCount = 1) (u : {m // p m})
    (hex : ∃ k, p k ∧ k ≠ u.1) (w : ρ.M) :
    (firstReturn ρ.succ p u).1 = w ↔
      p w ∧ w ≠ u.1 ∧ ∀ k, p k → k ≠ u.1 → ρ.steps u.1 w ≤ ρ.steps u.1 k := by
  obtain ⟨k₀, hk₀, hk₀u⟩ := hex
  constructor
  · rintro rfl
    exact ⟨(firstReturn ρ.succ p u).2, ρ.firstReturn_val_ne p h1 u hk₀ hk₀u,
      fun k hk hku => ρ.steps_firstReturn_le p h1 u hk hku⟩
  · rintro ⟨hw, hwu, hmin⟩
    have h₁ := ρ.steps_firstReturn_le p h1 u hw hwu
    have h₂ := hmin _ (firstReturn ρ.succ p u).2 (ρ.firstReturn_val_ne p h1 u hk₀ hk₀u)
    exact ρ.steps_inj h1 (le_antisymm h₁ h₂)

/-- The open gap after `u`: `x` lies strictly between `u` and its first return iff `x ≠ u` and
`x` is strictly nearer to `u` than every other `p`-point. -/
theorem arcBetween_firstReturn_iff (h1 : ρ.componentCount = 1) (u : {m // p m})
    (hex : ∃ k, p k ∧ k ≠ u.1) (x : ρ.M) :
    ρ.ArcBetween u.1 x (firstReturn ρ.succ p u).1 ↔
      x ≠ u.1 ∧ ∀ k, p k → k ≠ u.1 → ρ.steps u.1 x < ρ.steps u.1 k := by
  obtain ⟨k₀, hk₀, hk₀u⟩ := hex
  unfold ArcBetween
  rw [ρ.steps_pos_iff h1]
  constructor
  · rintro ⟨hx, hlt⟩
    exact ⟨Ne.symm hx, fun k hk hku => lt_of_lt_of_le hlt (ρ.steps_firstReturn_le p h1 u hk hku)⟩
  · rintro ⟨hx, hmin⟩
    exact ⟨Ne.symm hx, hmin _ (firstReturn ρ.succ p u).2 (ρ.firstReturn_val_ne p h1 u hk₀ hk₀u)⟩

/-- No `p`-point lies strictly inside a gap. -/
theorem not_arcBetween_firstReturn (h1 : ρ.componentCount = 1) (u : {m // p m}) {k : ρ.M}
    (hk : p k) : ¬ ρ.ArcBetween u.1 k (firstReturn ρ.succ p u).1 := by
  rintro ⟨h0, hlt⟩
  have hku : k ≠ u.1 := fun h => by rw [h, ρ.steps_self] at h0; exact lt_irrefl _ h0
  exact absurd (ρ.steps_firstReturn_le p h1 u hk hku) (not_le.mpr hlt)

end FirstReturnSteps

/-- The other occurrence of a retained crossing is retained: every retained set has a second point. -/
theorem crossKeep_exists_ne (S : Set ρ.Crossing) {u : ρ.M} (hu : ρ.CrossKeep S u) :
    ∃ k, ρ.CrossKeep S k ∧ k ≠ u :=
  ⟨ρ.pair u, (ρ.crossKeep_pair_iff S u).mpr hu, ρ.pair_ne u⟩

/-- The successor of the restricted record is the first return to the retained occurrences. -/
theorem restrictCrossings_succ_val (S : Set ρ.Crossing) (u : (ρ.restrictCrossings S).M) :
    ((ρ.restrictCrossings S).succ u).1 = (firstReturn ρ.succ (ρ.CrossKeep S) u).1 := rfl

/-- The gap of `S` after `u`, characterised by distances: `x ≠ u` and `x` is nearer to `u` than
every other retained occurrence. -/
theorem arcBetween_restrictCrossings_succ_iff (h1 : ρ.componentCount = 1) (S : Set ρ.Crossing)
    {u : ρ.M} (hu : ρ.CrossKeep S u) (x : ρ.M) :
    ρ.ArcBetween u x ((ρ.restrictCrossings S).succ ⟨u, hu⟩).1 ↔
      x ≠ u ∧ ∀ k, ρ.CrossKeep S k → k ≠ u → ρ.steps u x < ρ.steps u k :=
  ρ.arcBetween_firstReturn_iff _ h1 ⟨u, hu⟩ (ρ.crossKeep_exists_ne S hu) x

/-- An occurrence lies in at most one gap of `S`. -/
theorem gap_unique (h1 : ρ.componentCount = 1) (S : Set ρ.Crossing) {u u' x : ρ.M}
    (hu : ρ.CrossKeep S u) (hu' : ρ.CrossKeep S u')
    (hx : ρ.ArcBetween u x ((ρ.restrictCrossings S).succ ⟨u, hu⟩).1)
    (hx' : ρ.ArcBetween u' x ((ρ.restrictCrossings S).succ ⟨u', hu'⟩).1) : u = u' := by
  by_contra hne
  rw [ρ.arcBetween_restrictCrossings_succ_iff h1 S hu] at hx
  rw [ρ.arcBetween_restrictCrossings_succ_iff h1 S hu'] at hx'
  have h₁ := hx.2 u' hu' (Ne.symm hne)
  have h₂ := hx'.2 u hu hne
  have e₁ := ρ.steps_eq_of_base h1 x u x
  have e₂ := ρ.steps_eq_of_base h1 x u u'
  have e₃ := ρ.steps_eq_of_base h1 x u' x
  have e₄ := ρ.steps_eq_of_base h1 x u' u
  rw [ρ.steps_self] at e₁ e₃
  have := ρ.steps_lt_card h1 x u
  have := ρ.steps_lt_card h1 x u'
  have := ρ.steps_ne_of_ne h1 x hne
  have := ρ.steps_ne_of_ne h1 x hx.1
  have := ρ.steps_ne_of_ne h1 x hx'.1
  rw [ρ.steps_self] at *
  split_ifs at e₁ e₂ e₃ e₄ <;> omega

/-- Every unretained occurrence lies in some gap of a nonempty retained set. -/
theorem exists_gap (h1 : ρ.componentCount = 1) (S : Set ρ.Crossing) {u₀ : ρ.M}
    (hu₀ : ρ.CrossKeep S u₀) {x : ρ.M} (hx : ¬ ρ.CrossKeep S x) :
    ∃ u, ∃ hu : ρ.CrossKeep S u, ρ.ArcBetween u x ((ρ.restrictCrossings S).succ ⟨u, hu⟩).1 := by
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (ρ.CrossKeep S)) (ρ.steps x)
    ⟨u₀, by simpa using hu₀⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hmax
  refine ⟨u, hu, ?_⟩
  rw [ρ.arcBetween_restrictCrossings_succ_iff h1 S hu]
  have hxu : x ≠ u := fun h => hx (h ▸ hu)
  refine ⟨hxu, fun k hk hku => ?_⟩
  have hxk : x ≠ k := fun h => hx (h ▸ hk)
  have e₁ := ρ.steps_eq_of_base h1 x u x
  have e₂ := ρ.steps_eq_of_base h1 x u k
  have := hmax k hk
  have := ρ.steps_ne_of_ne h1 x hku
  have := ρ.steps_ne_of_ne h1 x hxu
  have := ρ.steps_ne_of_ne h1 x hxk
  have := ρ.steps_lt_card h1 x u
  have := ρ.steps_lt_card h1 x k
  rw [ρ.steps_self] at *
  split_ifs at e₁ e₂ <;> omega

/-! ### R3(b): interlacement through positions; independence of the representatives -/

/-- The crossing of a member occurrence. -/
theorem crossingOf_eq_of_mem {x : ρ.Crossing} {v : ρ.M} (hv : v ∈ x.1) : ρ.crossingOf v = x :=
  (ρ.crossingOf_eq_iff v x).mpr hv

/-- Membership in a crossing, given one member: the two occurrences `v, τv`. -/
theorem mem_val_iff {x : ρ.Crossing} {v : ρ.M} (hv : v ∈ x.1) (w : ρ.M) :
    w ∈ x.1 ↔ w = v ∨ w = ρ.pair v := by
  rw [← ρ.crossingOf_eq_of_mem hv]
  show w ∈ ({v, ρ.pair v} : Finset ρ.M) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem pair_mem_val {x : ρ.Crossing} {v : ρ.M} (hv : v ∈ x.1) : ρ.pair v ∈ x.1 :=
  (ρ.mem_val_iff hv _).mpr (Or.inr rfl)

/-- Occurrences of distinct crossings are pairwise distinct (all four combinations). -/
theorem ne_of_crossingOf_ne {v w : ρ.M} (h : ρ.crossingOf v ≠ ρ.crossingOf w) :
    v ≠ w ∧ v ≠ ρ.pair w ∧ ρ.pair v ≠ w ∧ ρ.pair v ≠ ρ.pair w := by
  refine ⟨fun e => h (by rw [e]), fun e => h (by rw [e, ρ.crossingOf_pair]),
    fun e => h (by rw [← e, ρ.crossingOf_pair]), fun e => h ?_⟩
  rw [← ρ.crossingOf_pair v, e, ρ.crossingOf_pair]

theorem crossingOf_ne_of_mem {x y : ρ.Crossing} (hxy : x ≠ y) {v w : ρ.M} (hv : v ∈ x.1)
    (hw : w ∈ y.1) : ρ.crossingOf v ≠ ρ.crossingOf w := by
  rw [ρ.crossingOf_eq_of_mem hv, ρ.crossingOf_eq_of_mem hw]; exact hxy

/-- The chords of `v` and `w` alternate: exactly one of `w, τw` lies on the open arc from `v` to
`τv` (the body of `Interlaces`, at one choice of representatives). -/
def Alternates (v w : ρ.M) : Prop :=
  Xor (ρ.ArcBetween v w (ρ.pair v)) (ρ.ArcBetween v (ρ.pair w) (ρ.pair v))

theorem alternates_pair_right (v w : ρ.M) : ρ.Alternates v (ρ.pair w) ↔ ρ.Alternates v w := by
  unfold Alternates
  rw [ρ.pair_invol, xor_comm]

theorem alternates_pair_left (h1 : ρ.componentCount = 1) {v w : ρ.M}
    (h : ρ.crossingOf v ≠ ρ.crossingOf w) : ρ.Alternates (ρ.pair v) w ↔ ρ.Alternates v w := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := ρ.ne_of_crossingOf_ne h
  unfold Alternates Xor
  rw [ρ.pair_invol]
  simp only [ρ.arcBetween_iff_posBetween h1 v]
  unfold PosBetween
  have := ρ.steps_lt_card h1 v w
  have := ρ.steps_lt_card h1 v (ρ.pair w)
  have := ρ.steps_lt_card h1 v (ρ.pair v)
  have := ρ.steps_ne_of_ne h1 v h₁
  have := ρ.steps_ne_of_ne h1 v h₂
  have := ρ.steps_ne_of_ne h1 v h₃
  have := ρ.steps_ne_of_ne h1 v h₄
  have := ρ.steps_ne_of_ne h1 v (ρ.ne_pair v)
  have := ρ.steps_ne_of_ne h1 v (ρ.ne_pair w)
  rw [ρ.steps_self] at *
  omega

theorem alternates_comm (h1 : ρ.componentCount = 1) {v w : ρ.M}
    (h : ρ.crossingOf v ≠ ρ.crossingOf w) : ρ.Alternates w v ↔ ρ.Alternates v w := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := ρ.ne_of_crossingOf_ne h
  unfold Alternates Xor
  simp only [ρ.arcBetween_iff_posBetween h1 v]
  unfold PosBetween
  have := ρ.steps_lt_card h1 v w
  have := ρ.steps_lt_card h1 v (ρ.pair w)
  have := ρ.steps_lt_card h1 v (ρ.pair v)
  have := ρ.steps_ne_of_ne h1 v h₁
  have := ρ.steps_ne_of_ne h1 v h₂
  have := ρ.steps_ne_of_ne h1 v h₃
  have := ρ.steps_ne_of_ne h1 v h₄
  have := ρ.steps_ne_of_ne h1 v (ρ.ne_pair v)
  have := ρ.steps_ne_of_ne h1 v (ρ.ne_pair w)
  rw [ρ.steps_self] at *
  omega

/-- On a one-circle record `Interlaces` is decided by any one choice of representatives. -/
theorem interlaces_iff_alternates (h1 : ρ.componentCount = 1) {x y : ρ.Crossing} (hxy : x ≠ y)
    {v w : ρ.M} (hv : v ∈ x.1) (hw : w ∈ y.1) : ρ.Interlaces x y ↔ ρ.Alternates v w := by
  constructor
  · intro h; exact h.2 v hv w hw
  · intro h
    refine ⟨hxy, fun v' hv' w' hw' => ?_⟩
    have hne := ρ.crossingOf_ne_of_mem hxy hv hw
    rw [ρ.mem_val_iff hv] at hv'
    rw [ρ.mem_val_iff hw] at hw'
    rcases hv' with rfl | rfl <;> rcases hw' with rfl | rfl
    · exact h
    · exact (ρ.alternates_pair_right _ _).mpr h
    · exact (ρ.alternates_pair_left h1 hne).mpr h
    · exact (ρ.alternates_pair_right _ _).mpr ((ρ.alternates_pair_left h1 hne).mpr h)

/-- Adjacency in the interlacement graph, at any one choice of representatives. -/
theorem adj_iff_alternates (h1 : ρ.componentCount = 1) {x y : ρ.Crossing} (hxy : x ≠ y)
    {v w : ρ.M} (hv : v ∈ x.1) (hw : w ∈ y.1) :
    ρ.interlacementGraph.Adj x y ↔ ρ.Alternates v w := by
  unfold interlacementGraph
  rw [SimpleGraph.fromRel_adj, ρ.interlaces_iff_alternates h1 hxy hv hw,
    ρ.interlaces_iff_alternates h1 hxy.symm hw hv,
    ρ.alternates_comm h1 (ρ.crossingOf_ne_of_mem hxy hv hw)]
  exact ⟨fun h => h.2.elim id id, fun h => ⟨hxy, Or.inl h⟩⟩

end Record

namespace Record

variable (ρ : Record)

/-! ### R3(c): the one-gap lemma (mp:blocks proof, sm-3:1637-1663)

"Fix a connected component `A` of the interlacement graph and a chord `b` outside it … both
endpoints of `b` lie in one cyclic gap between successive endpoints of `A`; if `b, b'` are
interlacing chords outside `A`, they occupy the same gap of `A`; hence every other connected
component `B` has all its endpoints in one gap of `A`", proved by induction along interlacement
paths (`SimpleGraph.Walk` induction inside a `ConnectedComponent`). -/

/-- Walk induction: a property propagated along edges holds along every walk. -/
theorem walk_induction {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    (hstep : ∀ x y, G.Adj x y → P x → P y) : ∀ {x y : V}, G.Walk x y → P x → P y := by
  intro x y p
  induction p with
  | nil => exact id
  | cons hxy _ ih => exact fun hx => ih (hstep _ _ hxy hx)

/-- Block induction: a property of crossings holding at one crossing of a block and propagated
along interlacement edges from inside the block holds on the whole block. -/
theorem block_induction {P : ρ.Crossing → Prop} (A : ρ.interlacementGraph.ConnectedComponent)
    {a₀ : ρ.Crossing} (ha₀ : a₀ ∈ A.supp) (h0 : P a₀)
    (hstep : ∀ a a', a ∈ A.supp → ρ.interlacementGraph.Adj a a' → P a → P a') :
    ∀ a ∈ A.supp, P a := by
  intro a ha
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact
    (((A.mem_supp_iff a₀).mp ha₀).trans ((A.mem_supp_iff a).mp ha).symm)
  exact (walk_induction (G := ρ.interlacementGraph) (P := fun a => a ∈ A.supp ∧ P a)
    (fun x y hxy hx => ⟨(A.mem_supp_congr_adj hxy).mp hx.1, hstep x y hx.1 hxy hx.2⟩) p
    ⟨ha₀, h0⟩).2

/-- A chord `{v, τv}` not alternating with `{w, τw}` has both occurrences on the same side of
the latter: measured from `w`, both before `τw` or both after. -/
theorem side_eq_of_not_alternates (h1 : ρ.componentCount = 1) {v w : ρ.M}
    (hne : ρ.crossingOf v ≠ ρ.crossingOf w) (h : ¬ ρ.Alternates v w) :
    (ρ.steps w v < ρ.steps w (ρ.pair w) ↔ ρ.steps w (ρ.pair v) < ρ.steps w (ρ.pair w)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := ρ.ne_of_crossingOf_ne hne
  unfold Alternates Xor at h
  simp only [ρ.arcBetween_iff_posBetween h1 w] at h
  unfold PosBetween at h
  have := ρ.steps_lt_card h1 w v
  have := ρ.steps_lt_card h1 w (ρ.pair v)
  have := ρ.steps_lt_card h1 w (ρ.pair w)
  have := ρ.steps_ne_of_ne h1 w h₁
  have := ρ.steps_ne_of_ne h1 w h₂
  have := ρ.steps_ne_of_ne h1 w h₃
  have := ρ.steps_ne_of_ne h1 w h₄
  have := ρ.steps_ne_of_ne h1 w (ρ.ne_pair v)
  have := ρ.steps_ne_of_ne h1 w (ρ.ne_pair w)
  rw [ρ.steps_self] at *
  omega

/-- If `{v, τv}` alternates with `{v', τv'}`, and each of the two chords has both occurrences on
one side of `{w, τw}`, then `v'` is on the side of `v`. -/
theorem side_eq_of_alternates (h1 : ρ.componentCount = 1) {v v' w : ρ.M}
    (hvv' : ρ.crossingOf v ≠ ρ.crossingOf v') (hvw : ρ.crossingOf v ≠ ρ.crossingOf w)
    (hv'w : ρ.crossingOf v' ≠ ρ.crossingOf w) (halt : ρ.Alternates v v')
    (hv : ρ.steps w v < ρ.steps w (ρ.pair w) ↔ ρ.steps w (ρ.pair v) < ρ.steps w (ρ.pair w))
    (hv' : ρ.steps w v' < ρ.steps w (ρ.pair w) ↔ ρ.steps w (ρ.pair v') < ρ.steps w (ρ.pair w)) :
    (ρ.steps w v' < ρ.steps w (ρ.pair w) ↔ ρ.steps w v < ρ.steps w (ρ.pair w)) := by
  obtain ⟨a₁, a₂, a₃, a₄⟩ := ρ.ne_of_crossingOf_ne hvv'
  obtain ⟨b₁, b₂, b₃, b₄⟩ := ρ.ne_of_crossingOf_ne hvw
  obtain ⟨c₁, c₂, c₃, c₄⟩ := ρ.ne_of_crossingOf_ne hv'w
  unfold Alternates Xor at halt
  simp only [ρ.arcBetween_iff_posBetween h1 w] at halt
  unfold PosBetween at halt
  have := ρ.steps_lt_card h1 w v
  have := ρ.steps_lt_card h1 w (ρ.pair v)
  have := ρ.steps_lt_card h1 w v'
  have := ρ.steps_lt_card h1 w (ρ.pair v')
  have := ρ.steps_lt_card h1 w (ρ.pair w)
  have := ρ.steps_ne_of_ne h1 w a₁
  have := ρ.steps_ne_of_ne h1 w a₂
  have := ρ.steps_ne_of_ne h1 w a₃
  have := ρ.steps_ne_of_ne h1 w a₄
  have := ρ.steps_ne_of_ne h1 w b₁
  have := ρ.steps_ne_of_ne h1 w b₂
  have := ρ.steps_ne_of_ne h1 w b₃
  have := ρ.steps_ne_of_ne h1 w b₄
  have := ρ.steps_ne_of_ne h1 w c₁
  have := ρ.steps_ne_of_ne h1 w c₂
  have := ρ.steps_ne_of_ne h1 w c₃
  have := ρ.steps_ne_of_ne h1 w c₄
  have := ρ.steps_ne_of_ne h1 w (ρ.ne_pair v)
  have := ρ.steps_ne_of_ne h1 w (ρ.ne_pair v')
  have := ρ.steps_ne_of_ne h1 w (ρ.ne_pair w)
  rw [ρ.steps_self] at *
  omega

/-- An occurrence of a crossing outside `A` differs from every retained occurrence of `A`. -/
theorem ne_of_crossKeep_of_not_mem {S : Set ρ.Crossing} {u : ρ.M} (hu : ρ.CrossKeep S u)
    {b : ρ.Crossing} (hb : b ∉ S) {x : ρ.M} (hx : x ∈ b.1) : u ≠ x := by
  rintro rfl
  exact hb (ρ.crossingOf_eq_of_mem hx ▸ hu)

/-- (c1) "both endpoints of `b` lie in one cyclic gap between successive endpoints of `A`"
(sm-3:1645-1646): a chord outside the block `A` has both occurrences strictly inside one gap of
`A`, i.e. between some retained occurrence `u` of `A` and its `A`-first return. -/
theorem exists_gap_of_not_mem_block (h1 : ρ.componentCount = 1)
    (A : ρ.interlacementGraph.ConnectedComponent) {b : ρ.Crossing} (hb : b ∉ A.supp) :
    ∃ u, ∃ hu : ρ.CrossKeep A.supp u,
      ∀ w ∈ b.1, ρ.ArcBetween u w ((ρ.restrictCrossings A.supp).succ ⟨u, hu⟩).1 := by
  obtain ⟨a₀, ha₀⟩ := A.nonempty_supp
  obtain ⟨v₀, rfl⟩ := ρ.crossingOf_surjective a₀
  obtain ⟨w₀, rfl⟩ := ρ.crossingOf_surjective b
  -- every chord of `A` does not interlace `b`, hence lies on one side of `b`
  have hnadj : ∀ a ∈ A.supp, ∀ v ∈ a.1,
      ρ.crossingOf v ≠ ρ.crossingOf w₀ ∧ ¬ ρ.Alternates v w₀ := by
    intro a ha v hv
    have hne : a ≠ ρ.crossingOf w₀ := fun h => hb (h ▸ ha)
    refine ⟨ρ.crossingOf_ne_of_mem hne hv (ρ.mem_crossingOf w₀), fun halt => hb ?_⟩
    have hadj := (ρ.adj_iff_alternates h1 hne hv (ρ.mem_crossingOf w₀)).mpr halt
    exact (A.mem_supp_congr_adj hadj).mp ha
  -- by induction along the block, every occurrence of `A` is on the side of `v₀`
  have hside : ∀ a ∈ A.supp, ∀ v ∈ a.1,
      (ρ.steps w₀ v < ρ.steps w₀ (ρ.pair w₀) ↔ ρ.steps w₀ v₀ < ρ.steps w₀ (ρ.pair w₀)) := by
    refine ρ.block_induction A ha₀ ?_ ?_
    · intro v hv
      obtain ⟨hne₀, hna₀⟩ := hnadj _ ha₀ v₀ (ρ.mem_crossingOf v₀)
      rw [ρ.mem_val_iff (ρ.mem_crossingOf v₀)] at hv
      rcases hv with rfl | rfl
      · exact Iff.rfl
      · exact (ρ.side_eq_of_not_alternates h1 hne₀ hna₀).symm
    · intro a a' ha hadj ih
      obtain ⟨v, rfl⟩ := ρ.crossingOf_surjective a
      obtain ⟨v', rfl⟩ := ρ.crossingOf_surjective a'
      have ha' : ρ.crossingOf v' ∈ A.supp := (A.mem_supp_congr_adj hadj).mp ha
      have hvv' : ρ.crossingOf v ≠ ρ.crossingOf v' := hadj.ne
      have halt :=
        (ρ.adj_iff_alternates h1 hvv' (ρ.mem_crossingOf v) (ρ.mem_crossingOf v')).mp hadj
      obtain ⟨hvw, hnv⟩ := hnadj _ ha v (ρ.mem_crossingOf v)
      obtain ⟨hv'w, hnv'⟩ := hnadj _ ha' v' (ρ.mem_crossingOf v')
      have hv := ih v (ρ.mem_crossingOf v)
      have hs' := ρ.side_eq_of_not_alternates h1 hv'w hnv'
      have key := ρ.side_eq_of_alternates h1 hvv' hvw hv'w halt
        (ρ.side_eq_of_not_alternates h1 hvw hnv) hs'
      intro x hx
      rw [ρ.mem_val_iff (ρ.mem_crossingOf v')] at hx
      rcases hx with rfl | rfl
      · exact key.trans hv
      · exact hs'.symm.trans (key.trans hv)
  -- the gap: from the last occurrence of `A` before returning to `w₀`
  have hv₀ : ρ.CrossKeep A.supp v₀ := ha₀
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (ρ.CrossKeep A.supp))
    (ρ.steps w₀) ⟨v₀, by simpa using hv₀⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hmax
  refine ⟨u, hu, fun x hx => ?_⟩
  rw [ρ.arcBetween_restrictCrossings_succ_iff h1 _ hu]
  refine ⟨(ρ.ne_of_crossKeep_of_not_mem hu hb hx).symm, fun k hk hku => ?_⟩
  have hsu := hside _ hu u (ρ.mem_crossingOf u)
  have hsk := hside _ hk k (ρ.mem_crossingOf k)
  have hu1 := ρ.ne_of_crossKeep_of_not_mem hu hb (ρ.mem_crossingOf w₀)
  have hu2 := ρ.ne_of_crossKeep_of_not_mem hu hb (ρ.pair_mem_val (ρ.mem_crossingOf w₀))
  have hk1 := ρ.ne_of_crossKeep_of_not_mem hk hb (ρ.mem_crossingOf w₀)
  have hk2 := ρ.ne_of_crossKeep_of_not_mem hk hb (ρ.pair_mem_val (ρ.mem_crossingOf w₀))
  have e₂ := ρ.steps_eq_of_base h1 w₀ u k
  have := hmax k hk
  have := ρ.steps_ne_of_ne h1 w₀ hku
  have := ρ.steps_ne_of_ne h1 w₀ hu1
  have := ρ.steps_ne_of_ne h1 w₀ hu2
  have := ρ.steps_ne_of_ne h1 w₀ hk1
  have := ρ.steps_ne_of_ne h1 w₀ hk2
  have := ρ.steps_ne_of_ne h1 w₀ (ρ.ne_pair w₀)
  have := ρ.steps_lt_card h1 w₀ u
  have := ρ.steps_lt_card h1 w₀ k
  have := ρ.steps_lt_card h1 w₀ (ρ.pair w₀)
  rw [ρ.mem_val_iff (ρ.mem_crossingOf w₀)] at hx
  rcases hx with rfl | rfl
  · have e₁ := ρ.steps_eq_of_base h1 x u x
    rw [ρ.steps_self] at *
    split_ifs at e₁ e₂ <;> omega
  · have e₁ := ρ.steps_eq_of_base h1 w₀ u (ρ.pair w₀)
    rw [ρ.steps_self] at *
    split_ifs at e₁ e₂ <;> omega

/-- (c2) "if `b, b'` are interlacing chords outside `A`, they occupy the same gap of `A`"
(sm-3:1647-1648): the gaps of two adjacent chords outside `A` coincide. -/
theorem gap_eq_of_adj (h1 : ρ.componentCount = 1) (A : ρ.interlacementGraph.ConnectedComponent)
    {b b' : ρ.Crossing} (hb : b ∉ A.supp) (hb' : b' ∉ A.supp)
    (hadj : ρ.interlacementGraph.Adj b b') {u u' : ρ.M} (hu : ρ.CrossKeep A.supp u)
    (hu' : ρ.CrossKeep A.supp u')
    (hgap : ∀ w ∈ b.1, ρ.ArcBetween u w ((ρ.restrictCrossings A.supp).succ ⟨u, hu⟩).1)
    (hgap' : ∀ w ∈ b'.1, ρ.ArcBetween u' w ((ρ.restrictCrossings A.supp).succ ⟨u', hu'⟩).1) :
    u = u' := by
  by_contra hne
  obtain ⟨w₀, rfl⟩ := ρ.crossingOf_surjective b
  obtain ⟨w₀', rfl⟩ := ρ.crossingOf_surjective b'
  have halt := (ρ.adj_iff_alternates h1 hadj.ne (ρ.mem_crossingOf w₀) (ρ.mem_crossingOf w₀')).mp hadj
  have g₁ := hgap w₀ (ρ.mem_crossingOf w₀)
  have g₂ := hgap (ρ.pair w₀) (ρ.pair_mem_val (ρ.mem_crossingOf w₀))
  have g₃ := hgap' w₀' (ρ.mem_crossingOf w₀')
  have g₄ := hgap' (ρ.pair w₀') (ρ.pair_mem_val (ρ.mem_crossingOf w₀'))
  rw [ρ.arcBetween_restrictCrossings_succ_iff h1 _ hu] at g₁ g₂
  rw [ρ.arcBetween_restrictCrossings_succ_iff h1 _ hu'] at g₃ g₄
  have i₁ := g₁.2 u' hu' (Ne.symm hne)
  have i₂ := g₂.2 u' hu' (Ne.symm hne)
  have i₃ := g₃.2 u hu hne
  have i₄ := g₄.2 u hu hne
  obtain ⟨a₁, a₂, a₃, a₄⟩ := ρ.ne_of_crossingOf_ne hadj.ne
  have hu1 := ρ.ne_of_crossKeep_of_not_mem hu hb (ρ.mem_crossingOf w₀)
  have hu2 := ρ.ne_of_crossKeep_of_not_mem hu hb (ρ.pair_mem_val (ρ.mem_crossingOf w₀))
  have hu3 := ρ.ne_of_crossKeep_of_not_mem hu hb' (ρ.mem_crossingOf w₀')
  have hu4 := ρ.ne_of_crossKeep_of_not_mem hu hb' (ρ.pair_mem_val (ρ.mem_crossingOf w₀'))
  have hu'1 := ρ.ne_of_crossKeep_of_not_mem hu' hb (ρ.mem_crossingOf w₀)
  have hu'2 := ρ.ne_of_crossKeep_of_not_mem hu' hb (ρ.pair_mem_val (ρ.mem_crossingOf w₀))
  have hu'3 := ρ.ne_of_crossKeep_of_not_mem hu' hb' (ρ.mem_crossingOf w₀')
  have hu'4 := ρ.ne_of_crossKeep_of_not_mem hu' hb' (ρ.pair_mem_val (ρ.mem_crossingOf w₀'))
  unfold Alternates Xor at halt
  simp only [ρ.arcBetween_iff_posBetween h1 w₀] at halt
  unfold PosBetween at halt
  have e₁ := ρ.steps_eq_of_base h1 w₀ u w₀
  have e₂ := ρ.steps_eq_of_base h1 w₀ u (ρ.pair w₀)
  have e₃ := ρ.steps_eq_of_base h1 w₀ u' w₀'
  have e₄ := ρ.steps_eq_of_base h1 w₀ u' (ρ.pair w₀')
  have e₅ := ρ.steps_eq_of_base h1 w₀ u u'
  have e₆ := ρ.steps_eq_of_base h1 w₀ u' u
  have := ρ.steps_lt_card h1 w₀ u
  have := ρ.steps_lt_card h1 w₀ u'
  have := ρ.steps_lt_card h1 w₀ w₀'
  have := ρ.steps_lt_card h1 w₀ (ρ.pair w₀)
  have := ρ.steps_lt_card h1 w₀ (ρ.pair w₀')
  have := ρ.steps_ne_of_ne h1 w₀ hne
  have := ρ.steps_ne_of_ne h1 w₀ a₁
  have := ρ.steps_ne_of_ne h1 w₀ a₂
  have := ρ.steps_ne_of_ne h1 w₀ a₃
  have := ρ.steps_ne_of_ne h1 w₀ a₄
  have := ρ.steps_ne_of_ne h1 w₀ hu1
  have := ρ.steps_ne_of_ne h1 w₀ hu2
  have := ρ.steps_ne_of_ne h1 w₀ hu3
  have := ρ.steps_ne_of_ne h1 w₀ hu4
  have := ρ.steps_ne_of_ne h1 w₀ hu'1
  have := ρ.steps_ne_of_ne h1 w₀ hu'2
  have := ρ.steps_ne_of_ne h1 w₀ hu'3
  have := ρ.steps_ne_of_ne h1 w₀ hu'4
  have := ρ.steps_ne_of_ne h1 w₀ (ρ.ne_pair w₀)
  have := ρ.steps_ne_of_ne h1 w₀ (ρ.ne_pair w₀')
  rw [ρ.steps_self] at *
  split_ifs at e₁ e₂ e₃ e₄ e₅ e₆ <;> omega

/-- (c3) "every other connected component `B` has all its endpoints in one gap of `A`"
(sm-3:1648-1649): the occurrences of a block `B ≠ A` all lie strictly inside one gap of `A`. -/
theorem exists_gap_of_ne_block (h1 : ρ.componentCount = 1)
    (A B : ρ.interlacementGraph.ConnectedComponent) (hAB : A ≠ B) :
    ∃ u, ∃ hu : ρ.CrossKeep A.supp u, ∀ w, ρ.CrossKeep B.supp w →
      ρ.ArcBetween u w ((ρ.restrictCrossings A.supp).succ ⟨u, hu⟩).1 := by
  obtain ⟨b₀, hb₀⟩ := B.nonempty_supp
  have hnot : ∀ b ∈ B.supp, b ∉ A.supp := fun b hb hb' =>
    hAB (((A.mem_supp_iff b).mp hb').symm.trans ((B.mem_supp_iff b).mp hb))
  obtain ⟨u, hu, hgap⟩ := ρ.exists_gap_of_not_mem_block h1 A (hnot b₀ hb₀)
  refine ⟨u, hu, ?_⟩
  have hall : ∀ b ∈ B.supp,
      ∀ w ∈ b.1, ρ.ArcBetween u w ((ρ.restrictCrossings A.supp).succ ⟨u, hu⟩).1 := by
    refine ρ.block_induction B hb₀ hgap ?_
    intro b b' hb hadj ih
    have hb' : b' ∈ B.supp := (B.mem_supp_congr_adj hadj).mp hb
    obtain ⟨u', hu', hgap'⟩ := ρ.exists_gap_of_not_mem_block h1 A (hnot b' hb')
    obtain rfl := ρ.gap_eq_of_adj h1 A (hnot b hb) (hnot b' hb') hadj hu hu' ih hgap'
    exact hgap'
  intro w hw
  exact hall _ hw w (ρ.mem_crossingOf w)

/-- (c3) in the `GapContiguous` vocabulary of the fixed statements: the block `A` is gap-contiguous
in `A ∪ B` for every other block `B`. -/
theorem gapContiguous_of_ne_block (h1 : ρ.componentCount = 1)
    (A B : ρ.interlacementGraph.ConnectedComponent) (hAB : A ≠ B) :
    ρ.GapContiguous A.supp (A.supp ∪ B.supp) := by
  obtain ⟨u, hu, h⟩ := ρ.exists_gap_of_ne_block h1 A B hAB
  refine ⟨u, hu, fun v hv hvA => h v ?_⟩
  exact (Set.mem_union _ _ _).mp hv |>.resolve_left hvA

end Record

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
