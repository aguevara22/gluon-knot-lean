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

Every chain lemma listed in PLAN_FINAL.md §3 is proved below by its unit (assembled 2026-09-14). -/

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

/-! ### G.0 Unit U-J4a (PROVED): a named record isomorphism from an occurrence bijection.
"A named record isomorphism is a bijection Φ : M → M' preserving successor, pairing, over/under bits
and these signs" (sm-3:361-365) together with "a bijection of their components" that "must also include
all components with no crossing occurrences" (rp:record-polynomial, sm-3:1220-1224).  `RecordIso.ofOcc`
builds the circle bijection from `Φ` on the occupied circles (successor cycles go to successor cycles,
`sameCycle_map_iff` + `sameCycle_iff_comp_eq`) and from a given bijection of the crossing-free circles;
`RecordIso.ofOccOfCard` replaces that bijection by a count of circles
(`card_comps_eq_cycleCount_add_card_freeComp`).  Consumers: J4 (`exists_joinRecord_smooth_inl`) and
R3(e) (`restrictCrossings_join_decomp`), whose circle bookkeeping this removes. -/

namespace RecordIso

variable {ρ ρ' : Record}

/-- An occurrence bijection commuting with the successors also commutes with them backwards. -/
theorem symm_succ_of_succ {Φ : ρ.M ≃ ρ'.M} (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v)) (w : ρ'.M) :
    Φ.symm (ρ'.succ w) = ρ.succ (Φ.symm w) := by
  apply Φ.injective
  rw [Equiv.apply_symm_apply, hs, Equiv.apply_symm_apply]

/-- The circle map induced by an occurrence bijection `Φ` and a bijection `ef` of the crossing-free
circles: an occupied circle `comp v` goes to `comp' (Φ v)`, a crossing-free circle goes through `ef`. -/
noncomputable def ofOccComps (Φ : ρ.M ≃ ρ'.M) (ef : ρ.FreeComp ≃ ρ'.FreeComp) (c : ρ.comps) :
    ρ'.comps :=
  if h : ∃ v, ρ.comp v = c then ρ'.comp (Φ (Classical.choose h))
  else (ef ⟨c, fun v hv => h ⟨v, hv⟩⟩).1

/-- On an occupied circle the induced map is `comp v ↦ comp' (Φ v)` (well defined because `Φ`
carries successor cycles to successor cycles). -/
theorem ofOccComps_comp (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (ef : ρ.FreeComp ≃ ρ'.FreeComp) (v : ρ.M) :
    ofOccComps Φ ef (ρ.comp v) = ρ'.comp (Φ v) := by
  have h : ∃ w, ρ.comp w = ρ.comp v := ⟨v, rfl⟩
  unfold ofOccComps
  rw [dite_eq_left h]
  apply (ρ'.sameCycle_iff_comp_eq _ _).mp
  rw [sameCycle_map_iff Φ ρ.succ ρ'.succ hs, ρ.sameCycle_iff_comp_eq]
  exact Classical.choose_spec h

/-- On a crossing-free circle the induced map is the given bijection `ef`. -/
theorem ofOccComps_free (Φ : ρ.M ≃ ρ'.M) (ef : ρ.FreeComp ≃ ρ'.FreeComp) (f : ρ.FreeComp) :
    ofOccComps Φ ef f.1 = (ef f).1 := by
  have h : ¬ ∃ v, ρ.comp v = f.1 := fun ⟨v, hv⟩ => f.2 v hv
  unfold ofOccComps
  rw [dite_eq_right h]
  rfl

/-- The induced circle maps of inverse data are inverse. -/
theorem ofOccComps_ofOccComps (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (ef : ρ.FreeComp ≃ ρ'.FreeComp) (Ψ : ρ'.M ≃ ρ.M) (hs' : ∀ w, Ψ (ρ'.succ w) = ρ.succ (Ψ w))
    (ef' : ρ'.FreeComp ≃ ρ.FreeComp) (hΨ : ∀ v, Ψ (Φ v) = v) (hef : ∀ f, ef' (ef f) = f)
    (c : ρ.comps) : ofOccComps Ψ ef' (ofOccComps Φ ef c) = c := by
  by_cases h : ∃ v, ρ.comp v = c
  · obtain ⟨v, rfl⟩ := h
    rw [ofOccComps_comp Φ hs ef v, ofOccComps_comp Ψ hs' ef' (Φ v), hΨ]
  · have hf : ∀ v, ρ.comp v ≠ c := fun v hv => h ⟨v, hv⟩
    calc ofOccComps Ψ ef' (ofOccComps Φ ef c)
        = ofOccComps Ψ ef' (ef (⟨c, hf⟩ : ρ.FreeComp)).1 :=
          congrArg (ofOccComps Ψ ef') (ofOccComps_free Φ ef ⟨c, hf⟩)
      _ = (ef' (ef (⟨c, hf⟩ : ρ.FreeComp))).1 := ofOccComps_free Ψ ef' _
      _ = c := congrArg Subtype.val (hef ⟨c, hf⟩)

/-- The circle bijection induced by an occurrence bijection commuting with the successors together
with a bijection of the crossing-free circles. -/
noncomputable def ofOccCompsEquiv (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (ef : ρ.FreeComp ≃ ρ'.FreeComp) : ρ.comps ≃ ρ'.comps where
  toFun := ofOccComps Φ ef
  invFun := ofOccComps Φ.symm ef.symm
  left_inv c := ofOccComps_ofOccComps Φ hs ef Φ.symm (symm_succ_of_succ hs) ef.symm
    (fun v => Φ.symm_apply_apply v) (fun f => ef.symm_apply_apply f) c
  right_inv c := ofOccComps_ofOccComps Φ.symm (symm_succ_of_succ hs) ef.symm Φ hs ef
    (fun w => Φ.apply_symm_apply w) (fun f => ef.apply_symm_apply f) c

/-- Unit U-J4a: a named record isomorphism from an occurrence bijection `Φ` commuting with
successor, pairing, over/under bits and signs together with a bijection `ef` of the crossing-free
circles ("The component bijection must also include all components with no crossing occurrences",
sm-3:1223-1224).  The circle bijection is induced by `Φ` on the occupied circles (`ofOcc_e_comp`:
successor cycles go to successor cycles) and is `ef` on the crossing-free ones (`ofOcc_e_free`). -/
noncomputable def ofOcc (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hp : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hb : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hσ : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (ef : ρ.FreeComp ≃ ρ'.FreeComp) : RecordIso ρ ρ' where
  e := ofOccCompsEquiv Φ hs ef
  Φ := Φ
  comp_eq v := (ofOccComps_comp Φ hs ef v).symm
  succ_eq := hs
  pair_eq := hp
  bit_eq := hb
  sgn_eq := hσ

@[simp] theorem ofOcc_Φ (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hp : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hb : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hσ : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (ef : ρ.FreeComp ≃ ρ'.FreeComp) :
    (ofOcc Φ hs hp hb hσ ef).Φ = Φ := rfl

theorem ofOcc_e_comp (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hp : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hb : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hσ : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (ef : ρ.FreeComp ≃ ρ'.FreeComp) (v : ρ.M) :
    (ofOcc Φ hs hp hb hσ ef).e (ρ.comp v) = ρ'.comp (Φ v) :=
  ofOccComps_comp Φ hs ef v

theorem ofOcc_e_free (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hp : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hb : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hσ : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (ef : ρ.FreeComp ≃ ρ'.FreeComp) (f : ρ.FreeComp) :
    (ofOcc Φ hs hp hb hσ ef).e f.1 = (ef f).1 :=
  ofOccComps_free Φ ef f

/-- The crossing-free circles of two records with the same number of circles and successor-compatible
occurrence bijection are equinumerous: the circles are the successor cycles plus the crossing-free
ones (`card_comps_eq_cycleCount_add_card_freeComp`) and `Φ` matches the cycles. -/
theorem card_freeComp_eq_of_card_comps_eq (Φ : ρ.M ≃ ρ'.M)
    (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hc : Fintype.card ρ.comps = Fintype.card ρ'.comps) :
    Fintype.card ρ.FreeComp = Fintype.card ρ'.FreeComp := by
  have h1 := ρ.card_comps_eq_cycleCount_add_card_freeComp
  have h2 := ρ'.card_comps_eq_cycleCount_add_card_freeComp
  have h3 : cycleCount ρ.succ = cycleCount ρ'.succ := by
    unfold cycleCount
    exact Fintype.card_congr
      (Quotient.congr Φ (fun v w => (sameCycle_map_iff Φ ρ.succ ρ'.succ hs v w).symm))
  omega

/-- `ofOcc` with the crossing-free circles matched by counting: an occurrence bijection commuting
with successor, pairing, bits and signs between two records with the same number of circles is a
named record isomorphism (the circle bijection is induced on the occupied circles and arbitrary on
the crossing-free ones). -/
noncomputable def ofOccOfCard (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hp : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hb : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hσ : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (hc : Fintype.card ρ.comps = Fintype.card ρ'.comps) :
    RecordIso ρ ρ' :=
  ofOcc Φ hs hp hb hσ (Fintype.equivOfCardEq (card_freeComp_eq_of_card_comps_eq Φ hs hc))

@[simp] theorem ofOccOfCard_Φ (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hp : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hb : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hσ : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (hc : Fintype.card ρ.comps = Fintype.card ρ'.comps) :
    (ofOccOfCard Φ hs hp hb hσ hc).Φ = Φ := rfl

theorem ofOccOfCard_e_comp (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hp : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hb : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hσ : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (hc : Fintype.card ρ.comps = Fintype.card ρ'.comps)
    (v : ρ.M) : (ofOccOfCard Φ hs hp hb hσ hc).e (ρ.comp v) = ρ'.comp (Φ v) :=
  ofOccComps_comp Φ hs _ v

/-- The `Nonempty` form used by the existential chain lemmas (J4, R3). -/
theorem nonempty_of_occ (Φ : ρ.M ≃ ρ'.M) (hs : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hp : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hb : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hσ : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (hc : Fintype.card ρ.comps = Fintype.card ρ'.comps) :
    Nonempty (RecordIso ρ ρ') :=
  ⟨ofOccOfCard Φ hs hp hb hσ hc⟩

end RecordIso

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

/-- U-J5 helper: the data behind `lastKeep f p a = some a'`: `a = f^n a'` for some `n`, and no
point `f^i a'` with `0 < i ≤ n` is retained (`a'` is the LAST retained point before `a`). -/
theorem lastKeep_some_spec {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop)
    [DecidablePred p] {a : α} {a' : {v // p v}} (ha' : lastKeep f p a = some a') :
    ∃ n : ℕ, (f ^ n) a'.1 = a ∧ ∀ i, 0 < i → i ≤ n → ¬ p ((f ^ i) a'.1) := by
  unfold lastKeep at ha'
  by_cases hex : ∃ n : ℕ, p ((f⁻¹ ^ n) a)
  · rw [dite_eq_left hex] at ha'
    have hv : a'.1 = (f⁻¹ ^ Nat.find hex) a :=
      (congrArg Subtype.val (Option.some.inj ha')).symm
    refine ⟨Nat.find hex, ?_, ?_⟩
    · rw [hv, ← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply]
    · intro i hi0 hiN hp
      have hk : (f ^ i) ((f⁻¹ ^ (i + (Nat.find hex - i))) a) = (f⁻¹ ^ (Nat.find hex - i)) a := by
        rw [pow_add, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply (f ^ i), inv_pow,
          mul_inv_cancel, Equiv.Perm.one_apply]
      rw [Nat.add_sub_cancel' hiN, ← hv] at hk
      rw [hk] at hp
      have := Nat.find_min' hex hp
      omega
  · rw [dite_eq_right hex] at ha'
    exact absurd ha' (by simp)

/-- U-J5 helper: a retained point whose `f`-orbit avoids `a` and `b` up to its first return has the
same first return along `f * swap a b` (the `u ∉ {a, b}` case of `firstReturn_mul_swap`). -/
theorem firstReturn_mul_swap_apply_of_avoid {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p] (a b : α) (u : {v // p v})
    (av : ∀ j, j < returnTime f p u.1 u.2 → (f ^ j) u.1 ≠ a ∧ (f ^ j) u.1 ≠ b) :
    (firstReturn (f * Equiv.swap a b) p u).1 = (firstReturn f p u).1 := by
  rw [firstReturn_apply f p u, ← mul_swap_pow_apply_of_forall_ne f a b u.1 _ av]
  apply firstReturn_val_eq_of_pow (f * Equiv.swap a b) p u (returnTime_pos f p u.1 u.2)
  · rw [mul_swap_pow_apply_of_forall_ne f a b u.1 _ av]
    exact returnTime_spec f p u.1 u.2
  · intro j hj0 hj
    rw [mul_swap_pow_apply_of_forall_ne f a b u.1 j (fun i hi => av i (by omega))]
    exact returnTime_min f p u.1 u.2 hj0 hj

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
  obtain ⟨n, hna, hnot⟩ := lastKeep_some_spec f p ha'
  -- a retained point that reaches `a` in `j` steps passed `a'` exactly `n` steps earlier
  have hreach : ∀ (u : α) (j : ℕ), p u → (f ^ j) u = a → n ≤ j ∧ (f ^ (j - n)) u = a'.1 := by
    intro u j hu hj
    have hjn : n ≤ j := by
      by_contra hlt
      have : u = (f ^ (n - j)) a'.1 := by
        apply (f ^ j).injective
        rw [hj, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' (by omega), hna]
      exact hnot (n - j) (by omega) (by omega) (by rw [← this]; exact hu)
    refine ⟨hjn, ?_⟩
    apply (f ^ n).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hjn, hj, hna]
  refine Equiv.ext fun u => Subtype.ext ?_
  by_cases hub : u = ⟨b, hb⟩
  · -- from `b`: jump to `f a = f^(n+1) a'`, then follow `f` to the return of `a'`
    rw [hub, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have hRn : n < returnTime f p a'.1 a'.2 := by
      by_contra hle
      exact hnot _ (returnTime_pos f p a'.1 a'.2) (by omega) (returnTime_spec f p a'.1 a'.2)
    have hiter : ∀ i, n + 1 + i ≤ returnTime f p a'.1 a'.2 →
        ((f * Equiv.swap a b) ^ (i + 1)) b = (f ^ (n + 1 + i)) a'.1 := by
      intro i hi
      have hfa : f a = (f ^ (n + 1)) a'.1 := by rw [pow_succ', Equiv.Perm.mul_apply, hna]
      have av : ∀ j, j < i → (f ^ j) ((f ^ (n + 1)) a'.1) ≠ a ∧ (f ^ j) ((f ^ (n + 1)) a'.1) ≠ b := by
        intro j hj
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        constructor
        · intro h
          obtain ⟨_, hj'⟩ := hreach a'.1 (j + (n + 1)) a'.2 h
          have hsub : j + (n + 1) - n = j + 1 := by omega
          rw [hsub] at hj'
          exact returnTime_min f p a'.1 a'.2 (Nat.succ_pos j) (by omega) (by rw [hj']; exact a'.2)
        · intro h
          exact returnTime_min f p a'.1 a'.2 (j := j + (n + 1)) (by omega) (by omega)
            (by rw [h]; exact hb)
      rw [pow_succ, Equiv.Perm.mul_apply, mul_swap_apply_right, hfa,
        mul_swap_pow_apply_of_forall_ne f a b _ i av, ← Equiv.Perm.mul_apply, ← pow_add,
        add_comm i (n + 1)]
    obtain ⟨m, hm⟩ : ∃ m, returnTime f p a'.1 a'.2 = n + 1 + m :=
      ⟨returnTime f p a'.1 a'.2 - n - 1, by omega⟩
    have hRHS : (firstReturn f p a').1 = (f ^ (n + 1 + m)) a'.1 := by
      rw [firstReturn_apply, hm]
    rw [hRHS, ← hiter m (by omega)]
    apply firstReturn_val_eq_of_pow (f * Equiv.swap a b) p ⟨b, hb⟩ (Nat.succ_pos m)
    · show p (((f * Equiv.swap a b) ^ (m + 1)) b)
      rw [hiter m (by omega), ← hm]
      exact returnTime_spec f p a'.1 a'.2
    · intro j hj0 hj
      show ¬ p (((f * Equiv.swap a b) ^ j) b)
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [hiter i (by omega)]
      exact returnTime_min f p a'.1 a'.2 (by omega) (by omega)
  by_cases hua : u = a'
  · -- from `a'`: follow `f` to `a` (`n` unretained steps), jump to `f b`, follow `f` to the return of `b`
    rw [hua, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have hab : a'.1 ≠ b := fun h => hub (hua.trans (Subtype.ext h))
    have hseg1 : ∀ j, j ≤ n → ((f * Equiv.swap a b) ^ j) a'.1 = (f ^ j) a'.1 := by
      intro j hj
      apply mul_swap_pow_apply_of_forall_ne
      intro i hi
      constructor
      · intro h
        obtain ⟨hni, _⟩ := hreach a'.1 i a'.2 h
        omega
      · intro h
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · rw [pow_zero, Equiv.Perm.one_apply] at h
          exact hab h
        · exact hnot i hpos (by omega) (by rw [h]; exact hb)
    have h1 : ((f * Equiv.swap a b) ^ (n + 1)) a'.1 = f b := by
      rw [pow_succ', Equiv.Perm.mul_apply, hseg1 n le_rfl, hna, mul_swap_apply_left]
    have hseg2 : ∀ i, i + 1 ≤ returnTime f p b hb →
        ((f * Equiv.swap a b) ^ (n + 1 + i)) a'.1 = (f ^ (i + 1)) b := by
      intro i hi
      have av : ∀ j, j < i → (f ^ j) (f b) ≠ a ∧ (f ^ j) (f b) ≠ b := by
        intro j hj
        rw [← Equiv.Perm.mul_apply, ← pow_succ]
        constructor
        · intro h
          obtain ⟨hnj, hj'⟩ := hreach b (j + 1) hb h
          rcases Nat.eq_zero_or_pos (j + 1 - n) with h0 | hpos
          · rw [h0, pow_zero, Equiv.Perm.one_apply] at hj'
            exact hab hj'.symm
          · exact returnTime_min f p b hb hpos (by omega) (by rw [hj']; exact a'.2)
        · intro h
          exact returnTime_min f p b hb (Nat.succ_pos j) (by omega) (by rw [h]; exact hb)
      rw [add_comm (n + 1) i, pow_add, Equiv.Perm.mul_apply, h1,
        mul_swap_pow_apply_of_forall_ne f a b (f b) i av, pow_succ f i, Equiv.Perm.mul_apply]
    obtain ⟨k, hk⟩ : ∃ k, returnTime f p b hb = k + 1 :=
      ⟨returnTime f p b hb - 1, by have := returnTime_pos f p b hb; omega⟩
    have hRHS : (firstReturn f p ⟨b, hb⟩).1 = (f ^ (k + 1)) b := by
      show (f ^ returnTime f p b hb) b = _
      rw [hk]
    rw [hRHS, ← hseg2 k (by omega)]
    apply firstReturn_val_eq_of_pow (f * Equiv.swap a b) p a' (by omega : 0 < n + 1 + k)
    · show p (((f * Equiv.swap a b) ^ (n + 1 + k)) a'.1)
      rw [hseg2 k (by omega), ← hk]
      exact returnTime_spec f p b hb
    · intro j hj0 hj
      show ¬ p (((f * Equiv.swap a b) ^ j) a'.1)
      rcases Nat.lt_or_ge j (n + 1) with hlt | hge
      · rw [hseg1 j (by omega)]
        exact hnot j hj0 (by omega)
      · obtain ⟨i, rfl⟩ : ∃ i, j = n + 1 + i := ⟨j - (n + 1), by omega⟩
        rw [hseg2 i (by omega)]
        exact returnTime_min f p b hb (Nat.succ_pos i) (by omega)
  · -- `u ∉ {a', b}`: the `f`-orbit of `u` meets neither `a` nor `b` before its return
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hua hub]
    apply firstReturn_mul_swap_apply_of_avoid
    intro j hj
    constructor
    · intro h
      obtain ⟨hnj, hj'⟩ := hreach u.1 j u.2 h
      rcases Nat.eq_zero_or_pos (j - n) with h0 | hpos
      · apply hua
        apply Subtype.ext
        rw [← hj', h0, pow_zero, Equiv.Perm.one_apply]
      · exact returnTime_min f p u.1 u.2 hpos (by omega) (by rw [hj']; exact a'.2)
    · intro h
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · apply hub
        apply Subtype.ext
        rw [pow_zero, Equiv.Perm.one_apply] at h
        exact h
      · exact returnTime_min f p u.1 u.2 hpos hj (by rw [h]; exact hb)

/-- Unit J6 (sub-chain of J4): if the `f`-cycle of `a` has no retained point, the swap is invisible to
the first return (the whole emptied cycle is inserted after `b`). -/
theorem firstReturn_mul_swap_of_lastKeep_none {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p] (a b : α) (hb : p b)
    (ha : lastKeep f p a = none) :
    firstReturn (f * Equiv.swap a b) p = firstReturn f p := by
  have hnone : ∀ v, p v → ¬ f.SameCycle a v := (lastKeep_eq_none_iff f p a).mp ha
  -- no retained point ever reaches `a`, and no iterate of `a` is retained
  have hne_a : ∀ (u : α) (j : ℕ), p u → (f ^ j) u ≠ a := fun u j hu h =>
    hnone u hu (Equiv.Perm.SameCycle.symm ⟨j, by rw [zpow_natCast]; exact h⟩)
  have hnot_a : ∀ j : ℕ, ¬ p ((f ^ j) a) := fun j hp => hnone _ hp ⟨j, by rw [zpow_natCast]⟩
  refine Equiv.ext fun u => Subtype.ext ?_
  by_cases hub : u = ⟨b, hb⟩
  · -- from `b`: jump to `f a`, run once around the emptied cycle of `a` back to `a`, jump to `f b`,
    -- then follow `f` to the return of `b`
    rw [hub]
    obtain ⟨L, hLpos, hLa, hLmin⟩ : ∃ L : ℕ, 0 < L ∧ (f ^ L) a = a ∧
        ∀ j, 0 < j → j < L → (f ^ j) a ≠ a :=
      ⟨returnTime f (fun x => x = a) a rfl, returnTime_pos f (fun x => x = a) a rfl,
        returnTime_spec f (fun x => x = a) a rfl,
        fun j hj0 hj => returnTime_min f (fun x => x = a) a rfl hj0 hj⟩
    have hseg1 : ∀ i, i + 1 ≤ L → ((f * Equiv.swap a b) ^ (i + 1)) b = (f ^ (i + 1)) a := by
      intro i hi
      have av : ∀ j, j < i → (f ^ j) (f a) ≠ a ∧ (f ^ j) (f a) ≠ b := by
        intro j hj
        rw [← Equiv.Perm.mul_apply, ← pow_succ]
        exact ⟨hLmin (j + 1) (Nat.succ_pos j) (by omega),
          fun h => hnot_a (j + 1) (by rw [h]; exact hb)⟩
      rw [pow_succ, Equiv.Perm.mul_apply, mul_swap_apply_right,
        mul_swap_pow_apply_of_forall_ne f a b (f a) i av, pow_succ f i, Equiv.Perm.mul_apply]
    have hLb : ((f * Equiv.swap a b) ^ (L + 1)) b = f b := by
      obtain ⟨i, hi⟩ : ∃ i, L = i + 1 := ⟨L - 1, by omega⟩
      rw [pow_succ', Equiv.Perm.mul_apply, hi, hseg1 i (by omega), ← hi, hLa, mul_swap_apply_left]
    have hseg2 : ∀ i, i + 1 ≤ returnTime f p b hb →
        ((f * Equiv.swap a b) ^ (L + 1 + i)) b = (f ^ (i + 1)) b := by
      intro i hi
      have av : ∀ j, j < i → (f ^ j) (f b) ≠ a ∧ (f ^ j) (f b) ≠ b := by
        intro j hj
        rw [← Equiv.Perm.mul_apply, ← pow_succ]
        exact ⟨hne_a b (j + 1) hb,
          fun h => returnTime_min f p b hb (Nat.succ_pos j) (by omega) (by rw [h]; exact hb)⟩
      rw [add_comm (L + 1) i, pow_add, Equiv.Perm.mul_apply, hLb,
        mul_swap_pow_apply_of_forall_ne f a b (f b) i av, pow_succ f i, Equiv.Perm.mul_apply]
    obtain ⟨k, hk⟩ : ∃ k, returnTime f p b hb = k + 1 :=
      ⟨returnTime f p b hb - 1, by have := returnTime_pos f p b hb; omega⟩
    have hRHS : (firstReturn f p ⟨b, hb⟩).1 = (f ^ (k + 1)) b := by
      show (f ^ returnTime f p b hb) b = _
      rw [hk]
    rw [hRHS, ← hseg2 k (by omega)]
    apply firstReturn_val_eq_of_pow (f * Equiv.swap a b) p ⟨b, hb⟩ (by omega : 0 < L + 1 + k)
    · show p (((f * Equiv.swap a b) ^ (L + 1 + k)) b)
      rw [hseg2 k (by omega), ← hk]
      exact returnTime_spec f p b hb
    · intro j hj0 hj
      show ¬ p (((f * Equiv.swap a b) ^ j) b)
      rcases Nat.lt_or_ge j (L + 1) with hlt | hge
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [hseg1 i (by omega)]
        exact hnot_a (i + 1)
      · obtain ⟨i, rfl⟩ : ∃ i, j = L + 1 + i := ⟨j - (L + 1), by omega⟩
        rw [hseg2 i (by omega)]
        exact returnTime_min f p b hb (Nat.succ_pos i) (by omega)
  · -- `u ≠ b`: the `f`-orbit of `u` never meets `a` (other cycle) nor `b` before its return
    apply firstReturn_mul_swap_apply_of_avoid
    intro j hj
    refine ⟨hne_a u.1 j u.2, ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, Equiv.Perm.one_apply]
      exact fun h => hub (Subtype.ext h)
    · exact fun h => returnTime_min f p u.1 u.2 hj0 hj (by rw [h]; exact hb)

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

/-! #### U-J3: the based order of a join (witness of `exists_rUnderFirst_joinRecord`) -/

/-- Iterating a permutation along an embedded orbit: if for the first `n` steps `g` acts on the
image of the `f`-orbit of `a` as `ι ∘ f`, then so does `g ^ n`. -/
theorem pow_apply_of_map_step {α β : Type*} (f : Equiv.Perm α) (g : Equiv.Perm β) (ι : α → β)
    (a : α) (n : ℕ) (h : ∀ k < n, g (ι ((f ^ k) a)) = ι (f ((f ^ k) a))) :
    (g ^ n) (ι a) = ι ((f ^ n) a) := by
  induction n with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply]
  | succ n ih =>
    rw [pow_succ' g n, Equiv.Perm.mul_apply, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
      h n (Nat.lt_succ_self n), pow_succ' f n, Equiv.Perm.mul_apply]

/-- When the base occurrence of `v`'s circle is `succ g`, the occurrence `g` is met last on that
circle: no `succ`-iterate of the base strictly before the position of `v` is `g`. -/
theorem RBasing.pow_base_ne_of_lt_pos (B : RBasing ρ) {v g : ρ.M} (hg : B.base v = ρ.succ g)
    {k : ℕ} (hk : k < B.pos v) : (ρ.succ ^ k) (B.base v) ≠ g := by
  intro h
  have h1 : (ρ.succ ^ (k + 1)) (B.base v) = B.base v := by
    rw [pow_succ', Equiv.Perm.mul_apply, h, hg]
  have h2 : (ρ.succ ^ (B.pos v - (k + 1))) (B.base v) = v := by
    have e : B.pos v - (k + 1) + (k + 1) = B.pos v := by omega
    have h3 := B.pow_pos_base v
    rw [← e, pow_add, Equiv.Perm.mul_apply, h1] at h3
    exact h3
  have := B.pos_le h2
  omega

/-- The based order of the join (Architect B, Skeleton_B.lean:668): the joined marked circle first
(rank `0`), then `A`'s other circles (even ranks `2r+2`), then `B`'s unmarked circles (odd ranks
`2r+1`); base occurrences: those of `A` on `A`'s circles and on the joined circle (`B`'s when `A`'s
marked circle is crossing-free), `B`'s on its unmarked circles. -/
noncomputable def RBasing.join (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) :
    RBasing (joinRecord μ₁ μ₂) where
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
    rintro (a | b)
    · show joinComp μ₁ μ₂ (Sum.inl (B₁.base a)) = joinComp μ₁ μ₂ (Sum.inl a)
      rw [joinComp_inl, joinComp_inl, B₁.base_comp]
    · show joinComp μ₁ μ₂ (if ρ₂.comp b = μ₂.comp then
          μ₁.gap.elim (Sum.inr (B₂.base b)) (fun g₁ => Sum.inl (B₁.base g₁))
        else Sum.inr (B₂.base b)) = joinComp μ₁ μ₂ (Sum.inr b)
      by_cases hb : ρ₂.comp b = μ₂.comp
      · rw [ite_eq_left hb, joinComp_inr_of_eq μ₁ μ₂ b hb]
        rcases hg₁ : μ₁.gap with _ | g₁
        · rw [Option.elim_none, joinComp_inr_of_eq μ₁ μ₂ (B₂.base b) (by rw [B₂.base_comp]; exact hb)]
        · rw [Option.elim_some, joinComp_inl, B₁.base_comp, μ₁.gap_comp g₁ hg₁]
      · rw [ite_eq_right hb, joinComp_inr_of_ne μ₁ μ₂ (B₂.base b) (by rw [B₂.base_comp]; exact hb),
          joinComp_inr_of_ne μ₁ μ₂ b hb]
        exact congrArg Sum.inr (Subtype.ext (B₂.base_comp b))
  base_const := by
    rintro (a | b) (a' | b') h
    · have h' : Sum.inl (ρ₁.comp a) = Sum.inl (ρ₁.comp a') := h
      exact congrArg Sum.inl (B₁.base_const a a' (Sum.inl.inj h'))
    · have h' : joinComp μ₁ μ₂ (Sum.inr b') = Sum.inl (ρ₁.comp a) := h.symm
      by_cases hb : ρ₂.comp b' = μ₂.comp
      · rw [joinComp_inr_of_eq μ₁ μ₂ b' hb] at h'
        have hc : ρ₁.comp a = μ₁.comp := (Sum.inl.inj h').symm
        show Sum.inl (B₁.base a) = (if ρ₂.comp b' = μ₂.comp then
            μ₁.gap.elim (Sum.inr (B₂.base b')) (fun g₁ => Sum.inl (B₁.base g₁))
          else Sum.inr (B₂.base b'))
        rw [ite_eq_left hb]
        rcases hg₁ : μ₁.gap with _ | g₁
        · exact absurd hc (μ₁.gap_none hg₁ a)
        · rw [Option.elim_some]
          exact congrArg Sum.inl (B₁.base_const a g₁ (hc.trans (μ₁.gap_comp g₁ hg₁).symm))
      · rw [joinComp_inr_of_ne μ₁ μ₂ b' hb] at h'
        exact absurd h' Sum.inr_ne_inl
    · have h' : joinComp μ₁ μ₂ (Sum.inr b) = Sum.inl (ρ₁.comp a') := h
      by_cases hb : ρ₂.comp b = μ₂.comp
      · rw [joinComp_inr_of_eq μ₁ μ₂ b hb] at h'
        have hc : ρ₁.comp a' = μ₁.comp := (Sum.inl.inj h').symm
        show (if ρ₂.comp b = μ₂.comp then
            μ₁.gap.elim (Sum.inr (B₂.base b)) (fun g₁ => Sum.inl (B₁.base g₁))
          else Sum.inr (B₂.base b)) = Sum.inl (B₁.base a')
        rw [ite_eq_left hb]
        rcases hg₁ : μ₁.gap with _ | g₁
        · exact absurd hc (μ₁.gap_none hg₁ a')
        · rw [Option.elim_some]
          exact congrArg Sum.inl (B₁.base_const g₁ a' ((μ₁.gap_comp g₁ hg₁).trans hc.symm))
      · rw [joinComp_inr_of_ne μ₁ μ₂ b hb] at h'
        exact absurd h' Sum.inr_ne_inl
    · have h' : joinComp μ₁ μ₂ (Sum.inr b) = joinComp μ₁ μ₂ (Sum.inr b') := h
      show (if ρ₂.comp b = μ₂.comp then
          μ₁.gap.elim (Sum.inr (B₂.base b)) (fun g₁ => Sum.inl (B₁.base g₁))
        else Sum.inr (B₂.base b)) = (if ρ₂.comp b' = μ₂.comp then
          μ₁.gap.elim (Sum.inr (B₂.base b')) (fun g₁ => Sum.inl (B₁.base g₁))
        else Sum.inr (B₂.base b'))
      by_cases hb : ρ₂.comp b = μ₂.comp <;> by_cases hb' : ρ₂.comp b' = μ₂.comp
      · rw [ite_eq_left hb, ite_eq_left hb', B₂.base_const b b' (hb.trans hb'.symm)]
      · rw [joinComp_inr_of_eq μ₁ μ₂ b hb, joinComp_inr_of_ne μ₁ μ₂ b' hb'] at h'
        exact absurd h' Sum.inl_ne_inr
      · rw [joinComp_inr_of_ne μ₁ μ₂ b hb, joinComp_inr_of_eq μ₁ μ₂ b' hb'] at h'
        exact absurd h' Sum.inr_ne_inl
      · rw [joinComp_inr_of_ne μ₁ μ₂ b hb, joinComp_inr_of_ne μ₁ μ₂ b' hb'] at h'
        rw [ite_eq_right hb, ite_eq_right hb', B₂.base_const b b' (congrArg Subtype.val (Sum.inr.inj h'))]

/-- Ranks of `A`'s circles in the joined based order. -/
theorem RBasing.join_rank_comp_inl (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)
    (a : ρ₁.M) : (B₁.join B₂ μ₁ μ₂).rank ((joinRecord μ₁ μ₂).comp (Sum.inl a)) =
      if ρ₁.comp a = μ₁.comp then 0 else 2 * B₁.rank (ρ₁.comp a) + 2 := rfl

/-- Ranks of `B`'s circles in the joined based order (the marked one is the joined circle, rank `0`). -/
theorem RBasing.join_rank_comp_inr (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)
    (b : ρ₂.M) : (B₁.join B₂ μ₁ μ₂).rank ((joinRecord μ₁ μ₂).comp (Sum.inr b)) =
      if ρ₂.comp b = μ₂.comp then 0 else 2 * B₂.rank (ρ₂.comp b) + 1 := by
  by_cases hb : ρ₂.comp b = μ₂.comp
  · rw [joinRecord_comp, joinComp_inr_of_eq μ₁ μ₂ b hb, ite_eq_left hb]
    show (if μ₁.comp = μ₁.comp then 0 else 2 * B₁.rank μ₁.comp + 2) = 0
    rw [ite_eq_left rfl]
  · rw [joinRecord_comp, joinComp_inr_of_ne μ₁ μ₂ b hb, ite_eq_right hb]
    rfl

/-- Positions of `A`'s occurrences in the joined based order are their positions in `A`: the `A`
portion of the joined circle is traversed first ("starting just before the `A` portion"), and the
gap occurrence `g₁` is met last on it because `A` is based at `succ g₁`. -/
theorem RBasing.join_pos_inl (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)
    (hμ₁ : B₁.MarkCompatible μ₁) (a : ρ₁.M) : (B₁.join B₂ μ₁ μ₂).pos (Sum.inl a) = B₁.pos a := by
  have hbase : (B₁.join B₂ μ₁ μ₂).base (Sum.inl a) = Sum.inl (B₁.base a) := rfl
  have hne : ∀ k < B₁.pos a, μ₁.gap ≠ some ((ρ₁.succ ^ k) (B₁.base a)) := by
    intro k hk hgap
    have hb : B₁.base a = ρ₁.succ ((ρ₁.succ ^ k) (B₁.base a)) := by
      rw [← hμ₁.base_gap _ hgap]
      exact B₁.base_const _ _ (by rw [ρ₁.comp_pow, B₁.base_comp])
    exact B₁.pow_base_ne_of_lt_pos hb hk rfl
  have hpow : ∀ n ≤ B₁.pos a,
      ((joinRecord μ₁ μ₂).succ ^ n) (Sum.inl (B₁.base a)) = Sum.inl ((ρ₁.succ ^ n) (B₁.base a)) := by
    intro n hn
    exact pow_apply_of_map_step ρ₁.succ (joinRecord μ₁ μ₂).succ Sum.inl (B₁.base a) n
      (fun k hk => joinSucc_inl_of_ne μ₁ μ₂ _ (hne k (lt_of_lt_of_le hk hn)))
  have h1 : (B₁.join B₂ μ₁ μ₂).pos (Sum.inl a) ≤ B₁.pos a := by
    apply (B₁.join B₂ μ₁ μ₂).pos_le
    rw [hbase, hpow _ le_rfl, B₁.pow_pos_base]
  have h2 : B₁.pos a ≤ (B₁.join B₂ μ₁ μ₂).pos (Sum.inl a) := by
    apply B₁.pos_le
    have h := (B₁.join B₂ μ₁ μ₂).pow_pos_base (Sum.inl a)
    rw [hbase, hpow _ h1] at h
    exact Sum.inl.inj h
  exact le_antisymm h1 h2

/-- Positions on `B`'s unmarked circles are unchanged. -/
theorem RBasing.join_pos_inr_of_ne (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark)
    (μ₂ : ρ₂.Mark) (b : ρ₂.M) (hb : ρ₂.comp b ≠ μ₂.comp) :
    (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) = B₂.pos b := by
  have hbase : (B₁.join B₂ μ₁ μ₂).base (Sum.inr b) = Sum.inr (B₂.base b) := by
    show (if ρ₂.comp b = μ₂.comp then
        μ₁.gap.elim (Sum.inr (B₂.base b)) (fun g₁ => Sum.inl (B₁.base g₁))
      else Sum.inr (B₂.base b)) = _
    rw [ite_eq_right hb]
  have hpow : ∀ n,
      ((joinRecord μ₁ μ₂).succ ^ n) (Sum.inr (B₂.base b)) = Sum.inr ((ρ₂.succ ^ n) (B₂.base b)) := by
    intro n
    refine pow_apply_of_map_step ρ₂.succ (joinRecord μ₁ μ₂).succ Sum.inr (B₂.base b) n (fun k _ => ?_)
    apply joinSucc_inr_of_ne μ₁ μ₂
    intro hgap
    exact hb (by rw [← μ₂.gap_comp _ hgap, ρ₂.comp_pow, B₂.base_comp])
  have h1 : (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) ≤ B₂.pos b := by
    apply (B₁.join B₂ μ₁ μ₂).pos_le
    rw [hbase, hpow, B₂.pow_pos_base]
  have h2 : B₂.pos b ≤ (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) := by
    apply B₂.pos_le
    have h := (B₁.join B₂ μ₁ μ₂).pow_pos_base (Sum.inr b)
    rw [hbase, hpow] at h
    exact Sum.inr.inj h
  exact le_antisymm h1 h2

/-- Positions on the `B` portion of the joined circle are shifted by one constant (the length of
the `A` portion, `B₁.pos g₁ + 1`, or `0` when `A`'s marked circle is crossing-free): "then its `B`
portion" (sm-3:1446). -/
theorem RBasing.join_pos_inr_of_eq (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark)
    (μ₂ : ρ₂.Mark) (hμ₁ : B₁.MarkCompatible μ₁) (hμ₂ : B₂.MarkCompatible μ₂) :
    ∃ S : ℕ, ∀ b, ρ₂.comp b = μ₂.comp → (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) = S + B₂.pos b := by
  rcases hg₁ : μ₁.gap with _ | g₁
  · refine ⟨0, fun b hb => ?_⟩
    have hbase : (B₁.join B₂ μ₁ μ₂).base (Sum.inr b) = Sum.inr (B₂.base b) := by
      show (if ρ₂.comp b = μ₂.comp then
          μ₁.gap.elim (Sum.inr (B₂.base b)) (fun g₁ => Sum.inl (B₁.base g₁))
        else Sum.inr (B₂.base b)) = _
      rw [ite_eq_left hb, hg₁, Option.elim_none]
    have hpow : ∀ n,
        ((joinRecord μ₁ μ₂).succ ^ n) (Sum.inr (B₂.base b)) = Sum.inr ((ρ₂.succ ^ n) (B₂.base b)) :=
      fun n => pow_apply_of_map_step ρ₂.succ (joinRecord μ₁ μ₂).succ Sum.inr (B₂.base b) n
        (fun k _ => joinSucc_inr_of_none μ₁ μ₂ _ hg₁)
    rw [zero_add]
    have h1 : (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) ≤ B₂.pos b := by
      apply (B₁.join B₂ μ₁ μ₂).pos_le
      rw [hbase, hpow, B₂.pow_pos_base]
    have h2 : B₂.pos b ≤ (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) := by
      apply B₂.pos_le
      have h := (B₁.join B₂ μ₁ μ₂).pow_pos_base (Sum.inr b)
      rw [hbase, hpow] at h
      exact Sum.inr.inj h
    exact le_antisymm h1 h2
  · refine ⟨B₁.pos g₁ + 1, fun b hb => ?_⟩
    rcases hg₂ : μ₂.gap with _ | g₂
    · exact absurd hb (μ₂.gap_none hg₂ b)
    have hbase : (B₁.join B₂ μ₁ μ₂).base (Sum.inr b) = Sum.inl (B₁.base g₁) := by
      show (if ρ₂.comp b = μ₂.comp then
          μ₁.gap.elim (Sum.inr (B₂.base b)) (fun g₁ => Sum.inl (B₁.base g₁))
        else Sum.inr (B₂.base b)) = _
      rw [ite_eq_left hb, hg₁, Option.elim_some]
    have hb₁ : B₁.base g₁ = ρ₁.succ g₁ := hμ₁.base_gap g₁ hg₁
    have hb₂ : B₂.base b = ρ₂.succ g₂ := by
      rw [← hμ₂.base_gap g₂ hg₂]
      exact B₂.base_const b g₂ (hb.trans (μ₂.gap_comp g₂ hg₂).symm)
    -- the `A` portion: `p₁ + 1` steps from `inl (succ g₁)` to `inl g₁`, all inside `A`
    have hF1 : ∀ n ≤ B₁.pos g₁,
        ((joinRecord μ₁ μ₂).succ ^ n) (Sum.inl (B₁.base g₁)) = Sum.inl ((ρ₁.succ ^ n) (B₁.base g₁)) := by
      intro n hn
      refine pow_apply_of_map_step ρ₁.succ (joinRecord μ₁ μ₂).succ Sum.inl (B₁.base g₁) n
        (fun k hk => ?_)
      apply joinSucc_inl_of_ne μ₁ μ₂
      rw [hg₁]
      intro heq
      exact B₁.pow_base_ne_of_lt_pos hb₁ (lt_of_lt_of_le hk hn) (Option.some.inj heq).symm
    -- then the step across the gaps into `B`
    have hgl : (joinRecord μ₁ μ₂).succ (Sum.inl g₁) = Sum.inr (ρ₂.succ g₂) :=
      joinSucc_gap_left μ₁ μ₂ hg₁ hg₂
    have hF2 : ((joinRecord μ₁ μ₂).succ ^ (B₁.pos g₁ + 1)) (Sum.inl (B₁.base g₁)) =
        Sum.inr (B₂.base b) := by
      rw [pow_succ']
      show (joinRecord μ₁ μ₂).succ (((joinRecord μ₁ μ₂).succ ^ B₁.pos g₁) (Sum.inl (B₁.base g₁))) =
        Sum.inr (B₂.base b)
      rw [hF1 _ le_rfl, B₁.pow_pos_base, hgl, hb₂]
    -- the `B` portion, inside `B` up to the position of `b`
    have hF3 : ∀ n ≤ B₂.pos b,
        ((joinRecord μ₁ μ₂).succ ^ n) (Sum.inr (B₂.base b)) = Sum.inr ((ρ₂.succ ^ n) (B₂.base b)) := by
      intro n hn
      refine pow_apply_of_map_step ρ₂.succ (joinRecord μ₁ μ₂).succ Sum.inr (B₂.base b) n
        (fun k hk => ?_)
      apply joinSucc_inr_of_ne μ₁ μ₂
      rw [hg₂]
      intro heq
      exact B₂.pow_base_ne_of_lt_pos hb₂ (lt_of_lt_of_le hk hn) (Option.some.inj heq).symm
    have hF4 : ∀ n ≤ B₂.pos b, ((joinRecord μ₁ μ₂).succ ^ (n + (B₁.pos g₁ + 1))) (Sum.inl (B₁.base g₁)) =
        Sum.inr ((ρ₂.succ ^ n) (B₂.base b)) := by
      intro n hn
      rw [pow_add]
      show ((joinRecord μ₁ μ₂).succ ^ n)
        (((joinRecord μ₁ μ₂).succ ^ (B₁.pos g₁ + 1)) (Sum.inl (B₁.base g₁))) = _
      rw [hF2, hF3 n hn]
    have hup : (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) ≤ B₂.pos b + (B₁.pos g₁ + 1) := by
      apply (B₁.join B₂ μ₁ μ₂).pos_le
      rw [hbase, hF4 _ le_rfl, B₂.pow_pos_base]
    have hlow : B₂.pos b + (B₁.pos g₁ + 1) ≤ (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) := by
      by_contra hlt
      push Not at hlt
      have h := (B₁.join B₂ μ₁ μ₂).pow_pos_base (Sum.inr b)
      rw [hbase] at h
      rcases Nat.lt_or_ge ((B₁.join B₂ μ₁ μ₂).pos (Sum.inr b)) (B₁.pos g₁ + 1) with hm | hm
      · rw [hF1 _ (Nat.lt_succ_iff.mp hm)] at h
        exact Sum.inl_ne_inr h
      · obtain ⟨n, hn⟩ : ∃ n, (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) = n + (B₁.pos g₁ + 1) :=
          ⟨(B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) - (B₁.pos g₁ + 1), by omega⟩
        rw [hn, hF4 n (by omega)] at h
        have := B₂.pos_le (Sum.inr.inj h)
        omega
    omega

/-- Keys of `A`'s occurrences compare in the join as in `A` ("the relative order of all visits is
the same as in its factor traversal", sm-3:1448-1449). -/
theorem RBasing.join_key_inl_lt (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)
    (hμ₁ : B₁.MarkCompatible μ₁) {v w : ρ₁.M} (h : B₁.key v < B₁.key w) :
    (B₁.join B₂ μ₁ μ₂).key (Sum.inl v) < (B₁.join B₂ μ₁ μ₂).key (Sum.inl w) := by
  unfold RBasing.key at h ⊢
  rw [Prod.Lex.toLex_lt_toLex] at h ⊢
  rw [B₁.join_rank_comp_inl B₂ μ₁ μ₂, B₁.join_rank_comp_inl B₂ μ₁ μ₂,
    B₁.join_pos_inl B₂ μ₁ μ₂ hμ₁, B₁.join_pos_inl B₂ μ₁ μ₂ hμ₁]
  rcases h with h | ⟨h, hp⟩
  · left
    by_cases hv : ρ₁.comp v = μ₁.comp <;> by_cases hw : ρ₁.comp w = μ₁.comp
    · rw [hv, hw] at h
      exact absurd h (lt_irrefl _)
    · rw [ite_eq_left hv, ite_eq_right hw]
      omega
    · have := hμ₁.rank_lt _ hv
      rw [hw] at h
      exfalso
      omega
    · rw [ite_eq_right hv, ite_eq_right hw]
      omega
  · right
    rw [B₁.rank_inj h]
    exact ⟨rfl, hp⟩

/-- Keys of `B`'s occurrences compare in the join as in `B`. -/
theorem RBasing.join_key_inr_lt (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)
    (hμ₁ : B₁.MarkCompatible μ₁) (hμ₂ : B₂.MarkCompatible μ₂) {v w : ρ₂.M}
    (h : B₂.key v < B₂.key w) :
    (B₁.join B₂ μ₁ μ₂).key (Sum.inr v) < (B₁.join B₂ μ₁ μ₂).key (Sum.inr w) := by
  obtain ⟨S, hS⟩ := B₁.join_pos_inr_of_eq B₂ μ₁ μ₂ hμ₁ hμ₂
  have hpos : ∀ b, (B₁.join B₂ μ₁ μ₂).pos (Sum.inr b) =
      (if ρ₂.comp b = μ₂.comp then S else 0) + B₂.pos b := by
    intro b
    by_cases hb : ρ₂.comp b = μ₂.comp
    · rw [ite_eq_left hb]
      exact hS b hb
    · rw [ite_eq_right hb, zero_add]
      exact B₁.join_pos_inr_of_ne B₂ μ₁ μ₂ b hb
  unfold RBasing.key at h ⊢
  rw [Prod.Lex.toLex_lt_toLex] at h ⊢
  rw [B₁.join_rank_comp_inr B₂ μ₁ μ₂, B₁.join_rank_comp_inr B₂ μ₁ μ₂, hpos, hpos]
  rcases h with h | ⟨h, hp⟩
  · left
    by_cases hv : ρ₂.comp v = μ₂.comp <;> by_cases hw : ρ₂.comp w = μ₂.comp
    · rw [hv, hw] at h
      exact absurd h (lt_irrefl _)
    · rw [ite_eq_left hv, ite_eq_right hw]
      omega
    · have := hμ₂.rank_lt _ hv
      rw [hw] at h
      exfalso
      omega
    · rw [ite_eq_right hv, ite_eq_right hw]
      omega
  · right
    rw [B₂.rank_inj h]
    exact ⟨rfl, Nat.add_lt_add_left hp _⟩

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
  refine ⟨B₁.join B₂ μ₁ μ₂, ?_⟩
  rintro (a | b) hv
  · rw [joinRecord_pair_inl]
    exact B₁.join_key_inl_lt B₂ μ₁ μ₂ hμ₁ (h₁ a hv)
  · rw [joinRecord_pair_inr]
    exact B₁.join_key_inr_lt B₂ μ₁ μ₂ hμ₁ hμ₂ (h₂ b hv)

/-! ### G.2b Unit U-J4b: the permutation-level heart of the smoothing commutation.
"In the joint diagram, smoothing has exactly the record of `J(A⁰,B)`: both operations are
recombinations at disjoint incoming/outgoing ends" (sm-3:1458-1462).  Everything is proved for
permutations of a plain sum `α ⊕ β` (B's J7-J9): the first return and `lastKeep` of `f ⊕ g`
(`firstReturn_sumCongr_inl_val/inr_val`, `lastKeep_sumCongr_inl`), the gap transposition pushed past
the smoothing transposition (`gapSwap_mul_swap_inl`, the conjugation of B's J9), the retained
occurrences of the sum (`sumKeepEquiv`), and the commutation itself
(`firstReturn_sumCongr_gapSwap_swap_val`, through J5/J6 with the retained swap point `inr g₂`).
The records enter only by definitional unfolding in `exists_joinRecord_smooth_inl`. -/

section SumFirstReturn

variable {α β : Type*} (f : Equiv.Perm α) (g : Equiv.Perm β)

theorem sumCongr_pow_inl (n : ℕ) (v : α) :
    ((Equiv.Perm.sumCongr f g) ^ n) (Sum.inl v) = Sum.inl ((f ^ n) v) := by
  rw [sumCongr_pow, Equiv.Perm.sumCongr_apply, Sum.map_inl]

theorem sumCongr_inv_pow_inl (n : ℕ) (v : α) :
    ((Equiv.Perm.sumCongr f g)⁻¹ ^ n) (Sum.inl v) = Sum.inl ((f⁻¹ ^ n) v) := by
  rw [Equiv.Perm.sumCongr_inv, sumCongr_pow, Equiv.Perm.sumCongr_apply, Sum.map_inl]

variable (p : α → Prop) (q : α ⊕ β → Prop)

/-- The retained occurrences of a sum, for a predicate that is `p` on the left summand and holds on
the whole right summand: `{z : α ⊕ β // q z} ≃ {w : α // p w} ⊕ β`. -/
def sumKeepEquiv (hql : ∀ v, q (Sum.inl v) ↔ p v) (hqr : ∀ b, q (Sum.inr b)) :
    {z : α ⊕ β // q z} ≃ ({w : α // p w} ⊕ β) where
  toFun z := match z with
    | ⟨Sum.inl w, h⟩ => Sum.inl ⟨w, (hql w).mp h⟩
    | ⟨Sum.inr b, _⟩ => Sum.inr b
  invFun z := match z with
    | Sum.inl ⟨w, h⟩ => ⟨Sum.inl w, (hql w).mpr h⟩
    | Sum.inr b => ⟨Sum.inr b, hqr b⟩
  left_inv := by rintro ⟨w | b, h⟩ <;> rfl
  right_inv := by rintro (⟨w, h⟩ | b) <;> rfl

theorem sumKeepEquiv_val (hql : ∀ v, q (Sum.inl v) ↔ p v) (hqr : ∀ b, q (Sum.inr b))
    (z : {z : α ⊕ β // q z}) :
    Sum.map (Subtype.val : {w : α // p w} → α) (id : β → β) (sumKeepEquiv p q hql hqr z) = z.1 := by
  rcases z with ⟨w | b, h⟩ <;> rfl

variable [Fintype α] [Fintype β] [DecidablePred p] [DecidablePred q]

/-- First return of `f ⊕ g` at a left point: the first return of `f` (B's J7). -/
theorem firstReturn_sumCongr_inl_val (hql : ∀ v, q (Sum.inl v) ↔ p v) (v : α) (hv : q (Sum.inl v)) :
    (firstReturn (Equiv.Perm.sumCongr f g) q ⟨Sum.inl v, hv⟩).1 =
      Sum.inl (firstReturn f p ⟨v, (hql v).mp hv⟩).1 := by
  have hv' : p v := (hql v).mp hv
  refine (firstReturn_val_eq_of_pow (Equiv.Perm.sumCongr f g) q ⟨Sum.inl v, hv⟩
    (n := returnTime f p v hv') (returnTime_pos f p v hv') ?_ ?_).trans ?_
  · show q (((Equiv.Perm.sumCongr f g) ^ returnTime f p v hv') (Sum.inl v))
    rw [sumCongr_pow_inl, hql]
    exact returnTime_spec f p v hv'
  · intro j hj0 hj
    show ¬ q (((Equiv.Perm.sumCongr f g) ^ j) (Sum.inl v))
    rw [sumCongr_pow_inl, hql]
    exact returnTime_min f p v hv' hj0 hj
  · show ((Equiv.Perm.sumCongr f g) ^ returnTime f p v hv') (Sum.inl v) = _
    rw [sumCongr_pow_inl]
    rfl

/-- First return of `f ⊕ g` at a right point (all of which are retained): one `g`-step. -/
theorem firstReturn_sumCongr_inr_val (hqr : ∀ b, q (Sum.inr b)) (b : β) (hb : q (Sum.inr b)) :
    (firstReturn (Equiv.Perm.sumCongr f g) q ⟨Sum.inr b, hb⟩).1 = Sum.inr (g b) := by
  have h : q ((Equiv.Perm.sumCongr f g) (Sum.inr b)) := by
    rw [Equiv.Perm.sumCongr_apply, Sum.map_inr]; exact hqr (g b)
  exact firstReturn_apply_of_mem (Equiv.Perm.sumCongr f g) q ⟨Sum.inr b, hb⟩ h

/-- The first return of `f ⊕ g` at the level of values: `firstReturn f p ⊕ g` through
`sumKeepEquiv`. -/
theorem firstReturn_sumCongr_val (hql : ∀ v, q (Sum.inl v) ↔ p v) (hqr : ∀ b, q (Sum.inr b))
    (u : {z : α ⊕ β // q z}) :
    (firstReturn (Equiv.Perm.sumCongr f g) q u).1 =
      Sum.map (Subtype.val : {w : α // p w} → α) (id : β → β)
        (Equiv.Perm.sumCongr (firstReturn f p) g (sumKeepEquiv p q hql hqr u)) := by
  rcases u with ⟨w | b, h⟩
  · rw [firstReturn_sumCongr_inl_val f g p q hql w h]
    rfl
  · rw [firstReturn_sumCongr_inr_val f g q hqr b h]
    rfl

/-- `lastKeep` of `f ⊕ g` at a left point is the left `lastKeep` (B's J7). -/
theorem lastKeep_sumCongr_inl (hql : ∀ v, q (Sum.inl v) ↔ p v) (u : α) :
    lastKeep (Equiv.Perm.sumCongr f g) q (Sum.inl u) =
      (lastKeep f p u).map (fun v => ⟨Sum.inl v.1, (hql v.1).mpr v.2⟩) := by
  have hiff : ∀ n : ℕ, q (((Equiv.Perm.sumCongr f g)⁻¹ ^ n) (Sum.inl u)) ↔ p ((f⁻¹ ^ n) u) := by
    intro n; rw [sumCongr_inv_pow_inl, hql]
  unfold lastKeep
  by_cases hex : ∃ n : ℕ, p ((f⁻¹ ^ n) u)
  · have hex' : ∃ n : ℕ, q (((Equiv.Perm.sumCongr f g)⁻¹ ^ n) (Sum.inl u)) :=
      hex.imp (fun n hn => (hiff n).mpr hn)
    rw [dite_eq_left hex, dite_eq_left hex', Option.map_some]
    have hfind : Nat.find hex' = Nat.find hex := by
      rw [Nat.find_eq_iff]
      exact ⟨(hiff _).mpr (Nat.find_spec hex),
        fun n hn hqn => Nat.find_min hex hn ((hiff n).mp hqn)⟩
    congr 1
    apply Subtype.ext
    show ((Equiv.Perm.sumCongr f g)⁻¹ ^ Nat.find hex') (Sum.inl u) = Sum.inl ((f⁻¹ ^ Nat.find hex) u)
    rw [hfind, sumCongr_inv_pow_inl]
  · have hex' : ¬ ∃ n : ℕ, q (((Equiv.Perm.sumCongr f g)⁻¹ ^ n) (Sum.inl u)) :=
      fun ⟨n, hn⟩ => hex ⟨n, (hiff n).mp hn⟩
    rw [dite_eq_right hex, dite_eq_right hex', Option.map_none]

end SumFirstReturn

/-- The gap transposition commutes past a transposition of two left points, at the price of
transporting the left gap (the conjugation of B's J9). -/
theorem gapSwap_mul_swap_inl {α β : Type*} [DecidableEq α] [DecidableEq β] (g₁ : Option α)
    (g₂ : Option β) (a a' : α) :
    gapSwap g₁ g₂ * Equiv.swap (Sum.inl a) (Sum.inl a' : α ⊕ β) =
      Equiv.swap (Sum.inl a) (Sum.inl a') * gapSwap (g₁.map (Equiv.swap a a')) g₂ := by
  have hS : ∀ z : α, Equiv.swap (Sum.inl a) (Sum.inl a' : α ⊕ β) (Sum.inl z) =
      Sum.inl (Equiv.swap a a' z) := by
    intro z
    rw [← Equiv.Perm.sumCongr_swap_one (β := β), Equiv.Perm.sumCongr_apply, Sum.map_inl]
  have hS' : ∀ z : β, Equiv.swap (Sum.inl a) (Sum.inl a' : α ⊕ β) (Sum.inr z) = Sum.inr z :=
    fun z => Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl Sum.inr_ne_inl
  rcases g₁ with _ | x <;> rcases g₂ with _ | y
  · rw [gapSwap_none_left, Option.map_none, gapSwap_none_left, one_mul, mul_one]
  · rw [gapSwap_none_left, Option.map_none, gapSwap_none_left, one_mul, mul_one]
  · rw [gapSwap_none_right, gapSwap_none_right, one_mul, mul_one]
  · rw [Option.map_some, gapSwap_some_some, gapSwap_some_some,
      Equiv.mul_swap_eq_swap_mul (Equiv.swap (Sum.inl a) (Sum.inl a')) (Sum.inl (Equiv.swap a a' x))
        (Sum.inr y), hS, hS', Equiv.swap_apply_self]

/-- The smoothing commutation at the permutation level (sm-3:1459-1472).  `f ⊕ g` with the gaps
`g₁, g₂` transposed is the joined successor; reconnecting it at the left crossing `{a, a'}` and
taking the first return to the retained points `q` (`p` on the left, everything on the right) is,
through `sumKeepEquiv`, the join of the smoothed left successor `firstReturn (f * swap a a') p` with
`g` at the re-chosen gap `g₀`: the last retained point before the transported gap `σ g₁`
(`lastKeep`, J5), or no gap when that cycle is emptied (J6) or when `A`'s marked circle was
crossing-free. -/
theorem firstReturn_sumCongr_gapSwap_swap_val {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (f : Equiv.Perm α) (g : Equiv.Perm β) (g₁ : Option α) (g₂ : Option β) (a a' : α)
    (p : α → Prop) [DecidablePred p] (q : α ⊕ β → Prop) [DecidablePred q]
    (hql : ∀ v, q (Sum.inl v) ↔ p v) (hqr : ∀ b, q (Sum.inr b)) (g₀ : Option {w : α // p w})
    (hg₀ : ∀ x, g₁ = some x → g₀ = lastKeep (f * Equiv.swap a a') p (Equiv.swap a a' x))
    (hg₀' : g₁ = none → g₀ = none) (u : {z : α ⊕ β // q z}) :
    (firstReturn (Equiv.Perm.sumCongr f g * gapSwap g₁ g₂ * Equiv.swap (Sum.inl a) (Sum.inl a'))
      q u).1 =
      Sum.map (Subtype.val : {w : α // p w} → α) (id : β → β)
        ((Equiv.Perm.sumCongr (firstReturn (f * Equiv.swap a a') p) g * gapSwap g₀ g₂)
          (sumKeepEquiv p q hql hqr u)) := by
  have hF := firstReturn_sumCongr_val (f * Equiv.swap a a') g p q hql hqr
  rw [mul_assoc, gapSwap_mul_swap_inl, ← mul_assoc, ← Equiv.Perm.sumCongr_swap_one (β := β),
    Equiv.Perm.sumCongr_mul, mul_one]
  rcases g₁ with _ | g₁
  · -- the marked circle of `A` is crossing-free: no gap swap on either side
    rw [hg₀' rfl, Option.map_none, gapSwap_none_left, gapSwap_none_left, mul_one, mul_one]
    exact hF u
  · rw [hg₀ g₁ rfl]
    rcases g₂ with _ | g₂
    · -- the marked circle of `B` is crossing-free
      rw [gapSwap_none_right, gapSwap_none_right, mul_one, mul_one]
      exact hF u
    · rw [Option.map_some, gapSwap_some_some]
      have hb : q (Sum.inr g₂) := hqr g₂
      have hLK := lastKeep_sumCongr_inl (f * Equiv.swap a a') g p q hql (Equiv.swap a a' g₁)
      rcases Option.eq_none_or_eq_some
          (lastKeep (f * Equiv.swap a a') p (Equiv.swap a a' g₁)) with hL | ⟨g₀, hL⟩
      · -- the `s₁`-cycle of the transported gap is emptied: the swap is invisible (J6)
        rw [hL, Option.map_none] at hLK
        rw [firstReturn_mul_swap_of_lastKeep_none _ _ _ _ hb hLK, hL, gapSwap_none_left, mul_one]
        exact hF u
      · -- the gap is re-chosen at the last retained occurrence `g₀` before `σ g₁` (J5)
        rw [hL, Option.map_some] at hLK
        rw [firstReturn_mul_swap_of_lastKeep_some _ _ _ _ hb hLK, hL, gapSwap_some_some,
          Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hF, map_swap_apply (sumKeepEquiv p q hql hqr)]
        rfl

/-- The retained occurrences of the smoothing of the join at an `A`-occurrence, as a predicate on
the plain sum (definitionally `(joinRecord μ₁ μ₂).SmoothKeep (Sum.inl a)`). -/
def SmoothInlKeep (A B : Record) (a : A.M) (z : A.M ⊕ B.M) : Prop :=
  z ∉ ({Sum.inl a, Sum.inl (A.pair a)} : Finset (A.M ⊕ B.M))

instance instDecidablePredSmoothInlKeep (A B : Record) (a : A.M) :
    DecidablePred (SmoothInlKeep A B a) :=
  fun z => inferInstanceAs (Decidable (z ∉ ({Sum.inl a, Sum.inl (A.pair a)} : Finset (A.M ⊕ B.M))))

theorem smoothInlKeep_inl_iff (A B : Record) (a w : A.M) :
    SmoothInlKeep A B a (Sum.inl w) ↔ A.SmoothKeep a w := by
  unfold SmoothInlKeep SmoothKeep
  simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]

theorem smoothInlKeep_inr (A B : Record) (a : A.M) (b : B.M) : SmoothInlKeep A B a (Sum.inr b) := by
  unfold SmoothInlKeep
  simp

/-- A crossing of `A` is a self crossing of the join iff it is one of `A`. -/
theorem joinRecord_isSelfCrossing_inl_iff (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (a : ρ₁.M) :
    (joinRecord μ₁ μ₂).IsSelfCrossing (Sum.inl a) ↔ ρ₁.IsSelfCrossing a := by
  show Sum.inl (ρ₁.comp a) = Sum.inl (ρ₁.comp (ρ₁.pair a)) ↔ ρ₁.comp a = ρ₁.comp (ρ₁.pair a)
  exact ⟨Sum.inl.inj, congrArg Sum.inl⟩

/-- "The component number is c(A)+c(B)-1" (and `c ± 1` under a smoothing, `componentCount_smooth_*`)
on both sides of the smoothing commutation. -/
theorem card_comps_smooth_joinRecord_inl (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (a : ρ₁.M)
    (μ₀ : (ρ₁.smooth a).Mark) :
    Fintype.card ((joinRecord μ₁ μ₂).smooth (Sum.inl a)).comps =
      Fintype.card (joinRecord μ₀ μ₂).comps := by
  show ((joinRecord μ₁ μ₂).smooth (Sum.inl a)).componentCount = (joinRecord μ₀ μ₂).componentCount
  have h₁ : 1 ≤ ρ₁.componentCount := Fintype.card_pos_iff.mpr ⟨ρ₁.comp a⟩
  have h₂ : 1 ≤ ρ₂.componentCount := Fintype.card_pos_iff.mpr ⟨μ₂.comp⟩
  by_cases hself : ρ₁.IsSelfCrossing a
  · rw [(joinRecord μ₁ μ₂).componentCount_smooth_of_self (Sum.inl a)
        ((joinRecord_isSelfCrossing_inl_iff μ₁ μ₂ a).mpr hself),
      componentCount_joinRecord, componentCount_joinRecord, ρ₁.componentCount_smooth_of_self a hself]
    omega
  · have h₁' := ρ₁.two_le_componentCount_of_mixed a hself
    rw [(joinRecord μ₁ μ₂).componentCount_smooth_of_mixed (Sum.inl a)
        (fun h => hself ((joinRecord_isSelfCrossing_inl_iff μ₁ μ₂ a).mp h)),
      componentCount_joinRecord, componentCount_joinRecord, ρ₁.componentCount_smooth_of_mixed a hself]
    omega

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
  refine ⟨μ₁.smoothMark a, ?_⟩
  -- the occurrence bijection `{v : M₁ ⊕ M₂ // v ∉ {inl a, inl τa}} ≃ {w : M₁ // w ∉ {a, τa}} ⊕ M₂`
  refine RecordIso.nonempty_of_occ
    (sumKeepEquiv (ρ₁.SmoothKeep a) (SmoothInlKeep ρ₁ ρ₂ a) (smoothInlKeep_inl_iff ρ₁ ρ₂ a)
      (smoothInlKeep_inr ρ₁ ρ₂ a)) ?_ ?_ ?_ ?_ (card_comps_smooth_joinRecord_inl μ₁ μ₂ a _)
  · -- successor: the smoothed join successor is the first return of
    -- `(s₁ ⊕ s₂) * gapSwap g₁ g₂ * swap (inl a) (inl τa)`; the join of the smoothing at the mark
    -- `μ₁.smoothMark a` is `(firstReturn (s₁ * swap a τa) keep ⊕ s₂) * gapSwap μ₀.gap g₂`
    intro v
    apply (Sum.map_injective.mpr ⟨Subtype.val_injective, Function.injective_id⟩ :
      Function.Injective
        (Sum.map (Subtype.val : {w : ρ₁.M // ρ₁.SmoothKeep a w} → ρ₁.M) (id : ρ₂.M → ρ₂.M)))
    exact (sumKeepEquiv_val (ρ₁.SmoothKeep a) (SmoothInlKeep ρ₁ ρ₂ a) (smoothInlKeep_inl_iff ρ₁ ρ₂ a)
      (smoothInlKeep_inr ρ₁ ρ₂ a) _).trans
      (firstReturn_sumCongr_gapSwap_swap_val ρ₁.succ ρ₂.succ μ₁.gap μ₂.gap a (ρ₁.pair a)
        (ρ₁.SmoothKeep a) (SmoothInlKeep ρ₁ ρ₂ a) (smoothInlKeep_inl_iff ρ₁ ρ₂ a)
        (smoothInlKeep_inr ρ₁ ρ₂ a) (μ₁.smoothMark a).gap
        (fun x hx => (μ₁.smoothMark_of_gap_some a hx).2)
        (fun hx => (μ₁.smoothMark_of_gap_none a hx).2) v)
  · -- pairing: `τ` acts factorwise on both sides
    rintro ⟨w | b, h⟩ <;> rfl
  · -- over/under bits
    rintro ⟨w | b, h⟩ <;> rfl
  · -- signs
    rintro ⟨w | b, h⟩ <;> rfl

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

/-- U-L helper: if the crossing `{s, t}` is `x`, then the ordered pair `(s, t)` is
`(overStrand x, underStrand x)` or `(underStrand x, overStrand x)`. -/
theorem Diagram.eq_over_under_of_crossing_eq (D : Diagram) {x : D.Γ.Crossing} {s t : D.Γ.Strand}
    (hst : D.Γ.IsCrossing {s, t}) (e : (⟨{s, t}, hst⟩ : D.Γ.Crossing) = x) :
    (s = D.overStrand x ∧ t = D.underStrand x) ∨ (s = D.underStrand x ∧ t = D.overStrand x) := by
  have e' : ({s, t} : Finset D.Γ.Strand) = x.val := congrArg Subtype.val e
  have hs : s ∈ x.val := by rw [← e']; exact Finset.mem_insert_self s {t}
  have ho : D.overStrand x ∈ ({s, t} : Finset D.Γ.Strand) := by rw [e']; exact D.over_mem x
  have hu : D.underStrand x ∈ ({s, t} : Finset D.Γ.Strand) := by rw [e']; exact D.under_mem x
  rw [Finset.mem_insert, Finset.mem_singleton] at ho hu
  rcases (D.mem_iff x s).mp hs with hs' | hs'
  · left
    refine ⟨hs', ?_⟩
    rcases hu with h | h
    · exact absurd (h.trans hs') (D.under_ne_over x)
    · exact h.symm
  · right
    refine ⟨hs', ?_⟩
    rcases ho with h | h
    · exact absurd (h.trans hs') (D.over_ne_under x)
    · exact h.symm

/-- Unit L6: the mixed sign sum of a pair not met by `x` is unchanged by switching `x`
(`switch_sign_of_ne`: the crossing `⟨{s, t}, _⟩ ≠ x` because a strand of `x` has component `∉ {i, j}`
or the pair is the wrong way round). -/
theorem mixedSignSum_switch_of_not_mem (D : Diagram) (x : D.Γ.Crossing) (i j : Fin D.Γ.c)
    (h : ¬ ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∧
      ¬ ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)) :
    mixedSignSum (D.switch x) i j = mixedSignSum D i j := by
  -- termwise: every mixed crossing of the pair `(i, j)` is a crossing other than `x`
  have h1 : ∀ s t : D.Γ.Strand,
      (if hm : D.Γ.MixedPair i j s t then
        (((D.switch x).sign (⟨{s, t}, hm.2.2⟩ : D.Γ.Crossing) : SignType) : ℤ) else 0)
        = (if hm : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, hm.2.2⟩ : SignType) : ℤ) else 0) := by
    intro s t
    by_cases hm : D.Γ.MixedPair i j s t
    · have hne : (⟨{s, t}, hm.2.2⟩ : D.Γ.Crossing) ≠ x := by
        intro e
        rcases D.eq_over_under_of_crossing_eq hm.2.2 e with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · exact h.1 ⟨by rw [← hs]; exact hm.1, by rw [← ht]; exact hm.2.1⟩
        · exact h.2 ⟨by rw [← ht]; exact hm.2.1, by rw [← hs]; exact hm.1⟩
      rw [dite_eq_left hm, dite_eq_left hm, D.switch_sign_of_ne hne]
    · rw [dite_eq_right hm, dite_eq_right hm]
  unfold mixedSignSum
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => h1 s t

/-- Unit L7: "The switch from positive to negative changes one mixed sign from `+1` to `−1`"
(sm-3:1605-1606): the mixed sign sum of the pair met by `x` drops by `2σ(x)` (`switch_sign_self` at
the unique ordered pair `(s, t)` with `{s, t} = x.val`, `s.1 = i`, `t.1 = j`; `switch_sign_of_ne`
elsewhere; `Finset.sum_erase`/`Fintype.sum_eq_single` twice, `crossing_pair_spec`). -/
theorem mixedSignSum_switch_of_mem (D : Diagram) (x : D.Γ.Crossing) (i j : Fin D.Γ.c) (hij : i ≠ j)
    (h : ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
      ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)) :
    mixedSignSum (D.switch x) i j = mixedSignSum D i j - 2 * (D.sign x : ℤ) := by
  -- the unique ordered mixed pair `(s₀, t₀)` of `x` with `s₀` on `i` and `t₀` on `j`
  obtain ⟨s₀, t₀, hs₀, ht₀, hval⟩ :
      ∃ s₀ t₀ : D.Γ.Strand, s₀.1 = i ∧ t₀.1 = j ∧ x.val = {s₀, t₀} := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, h1, h2, D.val_eq_pair x⟩
    · exact ⟨_, _, h2, h1, (D.val_eq_pair x).trans (Finset.pair_comm _ _)⟩
  have hm₀ : D.Γ.MixedPair i j s₀ t₀ := ⟨hs₀, ht₀, by rw [← hval]; exact x.2⟩
  have hx₀ : x = ⟨{s₀, t₀}, hm₀.2.2⟩ := Subtype.ext hval
  -- for a mixed pair `(s, t)` its crossing is `x` iff `(s, t) = (s₀, t₀)`
  have key : ∀ (s t : D.Γ.Strand) (hm : D.Γ.MixedPair i j s t),
      (⟨{s, t}, hm.2.2⟩ : D.Γ.Crossing) = x ↔ (s = s₀ ∧ t = t₀) := by
    intro s t hm
    constructor
    · intro e
      have e' : ({s, t} : Finset D.Γ.Strand) = {s₀, t₀} := (congrArg Subtype.val e).trans hval
      have hs : s ∈ ({s₀, t₀} : Finset D.Γ.Strand) := by
        rw [← e']; exact Finset.mem_insert_self s {t}
      have ht : t ∈ ({s₀, t₀} : Finset D.Γ.Strand) := by
        rw [← e']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
      rw [Finset.mem_insert, Finset.mem_singleton] at hs ht
      refine ⟨hs.resolve_right fun e₁ => hij ?_, ht.resolve_left fun e₁ => hij ?_⟩
      · rw [← hm.1, ← ht₀, e₁]
      · rw [← hs₀, ← hm.2.1, e₁]
    · rintro ⟨rfl, rfl⟩
      exact hx₀.symm
  -- the termwise identity: only the term `(s₀, t₀)` changes, by `-2σ(x)`
  have h1 : ∀ s t : D.Γ.Strand,
      (if hm : D.Γ.MixedPair i j s t then
        (((D.switch x).sign (⟨{s, t}, hm.2.2⟩ : D.Γ.Crossing) : SignType) : ℤ) else 0)
        = (if hm : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, hm.2.2⟩ : SignType) : ℤ) else 0)
          + (if t = t₀ then (if s = s₀ then -2 * (D.sign x : ℤ) else 0) else 0) := by
    intro s t
    by_cases hm : D.Γ.MixedPair i j s t
    · rw [dite_eq_left hm, dite_eq_left hm]
      by_cases e : (⟨{s, t}, hm.2.2⟩ : D.Γ.Crossing) = x
      · obtain ⟨rfl, rfl⟩ := (key s t hm).mp e
        rw [ite_eq_left rfl, ite_eq_left rfl, e, D.switch_sign_self x, SignType.coe_neg]
        ring
      · rw [D.switch_sign_of_ne e]
        have hne : ¬ (s = s₀ ∧ t = t₀) := fun h' => e ((key s t hm).mpr h')
        by_cases ht : t = t₀
        · rw [ite_eq_left ht, ite_eq_right (fun hs => hne ⟨hs, ht⟩), add_zero]
        · rw [ite_eq_right ht, add_zero]
    · rw [dite_eq_right hm, dite_eq_right hm]
      have hne : ¬ (s = s₀ ∧ t = t₀) := by
        rintro ⟨rfl, rfl⟩
        exact hm hm₀
      by_cases ht : t = t₀
      · rw [ite_eq_left ht, ite_eq_right (fun hs => hne ⟨hs, ht⟩), add_zero]
      · rw [ite_eq_right ht, add_zero]
  calc mixedSignSum (D.switch x) i j
      = ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
          ((if hm : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, hm.2.2⟩ : SignType) : ℤ) else 0)
            + (if t = t₀ then (if s = s₀ then -2 * (D.sign x : ℤ) else 0) else 0)) := by
        unfold mixedSignSum
        exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => h1 s t
    _ = mixedSignSum D i j - 2 * (D.sign x : ℤ) := by
        unfold mixedSignSum
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring

/-- Unit L8: "and hence changes `Λ` by `−1`" (doubled): `2Λ(D^sw) = 2Λ(D) − 2σ(x)` at a mixed crossing
(L6, L7 on the double sum `∑ i ∑ j, if i < j`; only the pair `(min, max)` of the two strand components
of `x` changes). -/
theorem twoLambda_switch (D : Diagram) {x : D.Γ.Crossing}
    (hx : (D.overStrand x).1 ≠ (D.underStrand x).1) :
    twoLambda (D.switch x) = twoLambda D - 2 * (D.sign x : ℤ) := by
  -- with `p < q` the two strand components of `x` (in either order), only the term `(p, q)` of the
  -- double sum changes, by `-2σ(x)` (L7); every other term is unchanged (L6)
  have main : ∀ p q : Fin D.Γ.c, p < q →
      (((D.overStrand x).1 = p ∧ (D.underStrand x).1 = q) ∨
        ((D.overStrand x).1 = q ∧ (D.underStrand x).1 = p)) →
      twoLambda (D.switch x) = twoLambda D - 2 * (D.sign x : ℤ) := by
    intro p q hpq hmem
    have h1 : ∀ i j : Fin D.Γ.c,
        (if i < j then twoLinking (D.switch x) i j else 0)
          = (if i < j then twoLinking D i j else 0)
            + (if j = q then (if i = p then -2 * (D.sign x : ℤ) else 0) else 0) := by
      intro i j
      by_cases hij : i < j
      · rw [ite_eq_left hij, ite_eq_left hij]
        unfold twoLinking
        by_cases hpair : i = p ∧ j = q
        · obtain ⟨rfl, rfl⟩ := hpair
          rw [ite_eq_left rfl, ite_eq_left rfl, mixedSignSum_switch_of_mem D x _ _ (ne_of_lt hij) hmem]
          ring
        · have hcorr : (if j = q then (if i = p then -2 * (D.sign x : ℤ) else 0) else 0) = 0 := by
            by_cases hj : j = q
            · rw [ite_eq_left hj]
              exact ite_eq_right fun hi => hpair ⟨hi, hj⟩
            · exact ite_eq_right hj
          rw [hcorr, add_zero]
          apply mixedSignSum_switch_of_not_mem D x i j
          constructor
          · rintro ⟨ha, hb⟩
            rcases hmem with ⟨hp, hq⟩ | ⟨hp, hq⟩
            · exact hpair ⟨ha.symm.trans hp, hb.symm.trans hq⟩
            · exact lt_asymm hpq (by rw [← ha.symm.trans hp, ← hb.symm.trans hq]; exact hij)
          · rintro ⟨ha, hb⟩
            rcases hmem with ⟨hp, hq⟩ | ⟨hp, hq⟩
            · exact lt_asymm hpq (by rw [← ha.symm.trans hp, ← hb.symm.trans hq]; exact hij)
            · exact hpair ⟨hb.symm.trans hq, ha.symm.trans hp⟩
      · rw [ite_eq_right hij, ite_eq_right hij, zero_add]
        symm
        by_cases hj : j = q
        · rw [ite_eq_left hj]
          exact ite_eq_right fun hi => hij (by rw [hi, hj]; exact hpq)
        · exact ite_eq_right hj
    calc twoLambda (D.switch x)
        = ∑ i : Fin D.Γ.c, ∑ j : Fin D.Γ.c, ((if i < j then twoLinking D i j else 0)
            + (if j = q then (if i = p then -2 * (D.sign x : ℤ) else 0) else 0)) := by
          unfold twoLambda
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
      _ = twoLambda D - 2 * (D.sign x : ℤ) := by
          unfold twoLambda
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          ring
  rcases lt_or_gt_of_ne hx with h | h
  · exact main _ _ h (Or.inl ⟨rfl, rfl⟩)
  · exact main _ _ h (Or.inr ⟨rfl, rfl⟩)

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
analysed; the chain lemmas are proved by units U-B2, U-R1, U-R2, U-R3a/b, U-R4 below) -/

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

/-! ### H.4a Unit U-B2 helpers — occurrences of a diagram vs. crossings, and `Σ` over index sets

Written by the U-B2 prover (2026-09-14).  Only helper declarations are added here; no fixed statement or
definition of the skeleton is changed. -/

/-- Two occurrences lie at the same crossing iff they are equal or twins (`Diagram.eq_or_eq_twin`). -/
theorem Diagram.visit_fst_eq_iff (D : Diagram) (v w : D.Γ.Visit) :
    v.1 = w.1 ↔ v = w ∨ v = D.twin w := by
  constructor
  · intro h
    exact D.eq_or_eq_twin w v h
  · rintro (rfl | rfl)
    · rfl
    · exact D.twin_fst w

/-- The over occurrence of the crossing of an occurrence `v` is `v` itself or its twin. -/
theorem Diagram.overVisit_fst_eq_or (D : Diagram) (v : D.Γ.Visit) :
    D.overVisit v.1 = v ∨ D.overVisit v.1 = D.twin v := by
  rcases D.visit_eq_over_or_under v with h | h
  · exact Or.inl h.symm
  · right
    conv_rhs => rw [h]
    exact (D.twin_underVisit v.1).symm

/-- `Σ` over a disjoint union of index sets splits as a sum; the underlying `Σ i : ι` element is kept
(`sigmaSetUnionEquiv_elim`). -/
noncomputable def sigmaSetUnionEquiv {ι : Type} (β : ι → Type) {S₁ S₂ : Set ι}
    (hdisj : Disjoint S₁ S₂) :
    (Σ i : (S₁ ∪ S₂ : Set ι), β i) ≃ (Σ i : S₁, β i) ⊕ (Σ i : S₂, β i) where
  toFun q := if h : q.1.1 ∈ S₁ then Sum.inl ⟨⟨q.1.1, h⟩, q.2⟩
    else Sum.inr ⟨⟨q.1.1, ((Set.mem_union _ _ _).mp q.1.2).resolve_left h⟩, q.2⟩
  invFun := Sum.elim (fun r => ⟨⟨r.1.1, Set.mem_union_left S₂ r.1.2⟩, r.2⟩)
    (fun r => ⟨⟨r.1.1, Set.mem_union_right S₁ r.1.2⟩, r.2⟩)
  left_inv q := by
    rcases q with ⟨⟨i, hi⟩, x⟩
    by_cases h : i ∈ S₁ <;> simp [h]
  right_inv r := by
    rcases r with ⟨⟨i, hi⟩, x⟩ | ⟨⟨i, hi⟩, x⟩
    · simp [hi]
    · have h : i ∉ S₁ := fun h => Set.disjoint_left.mp hdisj h hi
      simp [h]

theorem sigmaSetUnionEquiv_elim {ι : Type} (β : ι → Type) {S₁ S₂ : Set ι} (hdisj : Disjoint S₁ S₂)
    (q : Σ i : (S₁ ∪ S₂ : Set ι), β i) :
    Sum.elim (fun r : Σ i : S₁, β i => (⟨r.1.1, r.2⟩ : Σ i, β i))
        (fun r : Σ i : S₂, β i => (⟨r.1.1, r.2⟩ : Σ i, β i)) (sigmaSetUnionEquiv β hdisj q) =
      ⟨q.1.1, q.2⟩ := by
  rcases q with ⟨⟨i, hi⟩, x⟩
  by_cases h : i ∈ S₁ <;> simp [sigmaSetUnionEquiv, h]

/-- `Σ` over a singleton index set is the fibre. -/
def sigmaSetSingletonEquiv {ι : Type} (β : ι → Type) (i₀ : ι) :
    (Σ i : ({i₀} : Set ι), β i) ≃ β i₀ where
  toFun q := cast (congrArg β (Set.mem_singleton_iff.mp q.1.2)) q.2
  invFun x := ⟨⟨i₀, Set.mem_singleton i₀⟩, x⟩
  left_inv q := by
    rcases q with ⟨⟨j, hj⟩, x⟩
    have hj' : j = i₀ := Set.mem_singleton_iff.mp hj
    subst hj'
    rfl
  right_inv x := rfl

/-- Unit B2: the crossings of a clean marked join are those of the two factors, with their signs
(`D.Γ.Crossing ≃ D.record.Crossing` via `crossingOf (overVisit x)` / `Crossing.rep`;
`RecordIso.crossingOf_eq`; `(joinRecord μ₁ μ₂).Crossing ≃ ρ₁.Crossing ⊕ ρ₂.Crossing` from
`joinRecord_pair_inl/inr`; signs by `record_sgn`, `sgn_eq`, `joinRecord_sgn_inl/inr` — B's
sub-lemmas `RecordIso.crossingEquiv`, `joinCrossingEquiv`, `joinCrossingEquiv_sgn`,
Skeleton_B.lean:713-738). -/
theorem IsCleanMarkedJoin.crossingEquiv {A B : MarkedDiagram} {J : Diagram} (h : IsCleanMarkedJoin A B J) :
    ∃ φ : A.D.Γ.Crossing ⊕ B.D.Γ.Crossing ≃ J.Γ.Crossing,
      (∀ x, J.sign (φ (Sum.inl x)) = A.D.sign x) ∧ (∀ y, J.sign (φ (Sum.inr y)) = B.D.sign y) := by
  obtain ⟨ι⟩ := h
  -- occurrences of `J` are the occurrences of the two factors (`ι.Φ.symm`), compatibly with pairing and signs
  let Ψ : (Record.joinRecord A.μ B.μ).M ≃ J.record.M := ι.Φ.symm
  have hΨpair : ∀ v, Ψ ((Record.joinRecord A.μ B.μ).pair v) = J.record.pair (Ψ v) := by
    intro v
    apply ι.Φ.injective
    rw [ι.pair_eq]
    simp only [Ψ, Equiv.apply_symm_apply]
  have hΨsgn : ∀ v, J.record.sgn (Ψ v) = (Record.joinRecord A.μ B.μ).sgn v := by
    intro v
    rw [← ι.sgn_eq]
    simp only [Ψ, Equiv.apply_symm_apply]
  -- two occurrences of the join land at the same crossing of `J` iff they are equal or paired
  have key : ∀ v w, (Ψ v : J.Γ.Visit).1 = (Ψ w : J.Γ.Visit).1 →
      v = w ∨ v = (Record.joinRecord A.μ B.μ).pair w := by
    intro v w hvw
    rcases (J.visit_fst_eq_iff (Ψ v) (Ψ w)).mp hvw with h1 | h1
    · exact Or.inl (Ψ.injective h1)
    · right
      apply Ψ.injective
      rw [hΨpair]
      exact h1
  -- the crossing map: the crossing of `J` carrying the image of the over occurrence
  let g₁ : A.D.Γ.Crossing → J.Γ.Crossing := fun x => (Ψ (Sum.inl (A.D.overVisit x)) : J.Γ.Visit).1
  let g₂ : B.D.Γ.Crossing → J.Γ.Crossing := fun y => (Ψ (Sum.inr (B.D.overVisit y)) : J.Γ.Visit).1
  have hinj : Function.Injective (Sum.elim g₁ g₂) := by
    intro u u' huu'
    rcases u with x | x <;> rcases u' with y | y <;>
      simp only [Sum.elim_inl, Sum.elim_inr, g₁, g₂] at huu' <;>
      rcases key _ _ huu' with h1 | h1
    · exact congrArg Sum.inl (congrArg (fun v : A.D.Γ.Visit => v.1) (Sum.inl.inj h1))
    · change (Sum.inl (A.D.overVisit x) : (Record.joinRecord A.μ B.μ).M) =
        Sum.inl (A.D.underVisit y) at h1
      exact congrArg Sum.inl (congrArg (fun v : A.D.Γ.Visit => v.1) (Sum.inl.inj h1))
    · exact absurd h1 Sum.inl_ne_inr
    · change (Sum.inl (A.D.overVisit x) : (Record.joinRecord A.μ B.μ).M) =
        Sum.inr (B.D.underVisit y) at h1
      exact absurd h1 Sum.inl_ne_inr
    · exact absurd h1 Sum.inr_ne_inl
    · change (Sum.inr (B.D.overVisit x) : (Record.joinRecord A.μ B.μ).M) =
        Sum.inl (A.D.underVisit y) at h1
      exact absurd h1 Sum.inr_ne_inl
    · exact congrArg Sum.inr (congrArg (fun v : B.D.Γ.Visit => v.1) (Sum.inr.inj h1))
    · change (Sum.inr (B.D.overVisit x) : (Record.joinRecord A.μ B.μ).M) =
        Sum.inr (B.D.underVisit y) at h1
      exact congrArg Sum.inr (congrArg (fun v : B.D.Γ.Visit => v.1) (Sum.inr.inj h1))
  have hsurj : Function.Surjective (Sum.elim g₁ g₂) := by
    intro z
    obtain ⟨v, hv⟩ := Ψ.surjective (J.overVisit z)
    change A.D.Γ.Visit ⊕ B.D.Γ.Visit at v
    rcases v with a | b
    · refine ⟨Sum.inl a.1, ?_⟩
      show (Ψ (Sum.inl (A.D.overVisit a.1)) : J.Γ.Visit).1 = z
      rcases A.D.overVisit_fst_eq_or a with ha | ha
      · rw [ha, hv]
        rfl
      · rw [ha]
        change (Ψ ((Record.joinRecord A.μ B.μ).pair (Sum.inl a)) : J.Γ.Visit).1 = z
        rw [hΨpair (Sum.inl a), hv]
        rfl
    · refine ⟨Sum.inr b.1, ?_⟩
      show (Ψ (Sum.inr (B.D.overVisit b.1)) : J.Γ.Visit).1 = z
      rcases B.D.overVisit_fst_eq_or b with hb | hb
      · rw [hb, hv]
        rfl
      · rw [hb]
        change (Ψ ((Record.joinRecord A.μ B.μ).pair (Sum.inr b)) : J.Γ.Visit).1 = z
        rw [hΨpair (Sum.inr b), hv]
        rfl
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun x => ?_, fun y => ?_⟩
  · change J.record.sgn (Ψ (Sum.inl (A.D.overVisit x))) = A.D.sign x
    exact (hΨsgn (Sum.inl (A.D.overVisit x))).trans rfl
  · change J.record.sgn (Ψ (Sum.inr (B.D.overVisit y))) = B.D.sign y
    exact (hΨsgn (Sum.inr (B.D.overVisit y))).trans rfl

/-- Unit B3: "Every old crossing is present once, with its old sign" (sm-3:1681-1682), along a forest
(`JoinForest` induction; leaf: `Set.uniqueSingleton`/`Equiv.sigmaUnique`; node: `Equiv.Set.union` on
the disjoint index sets, `Equiv.sigmaSumDistrib`, `IsCleanMarkedJoin.crossingEquiv`). -/
theorem joinForest_sign {ι : Type} (C : ι → Diagram) :
    ∀ (S : Set ι) (J : Diagram), JoinForest C S J →
      ∃ φ : (Σ i : S, (C i).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2 := by
  intro S J h
  induction h with
  | leaf i =>
    refine ⟨sigmaSetSingletonEquiv (fun i => (C i).Γ.Crossing) i, fun q => ?_⟩
    rcases q with ⟨⟨j, hj⟩, x⟩
    have hj' : j = i := Set.mem_singleton_iff.mp hj
    subst hj'
    rfl
  | @join S₁ S₂ A B J hA hB hdisj hJ ihA ihB =>
    obtain ⟨φA, hφA⟩ := ihA
    obtain ⟨φB, hφB⟩ := ihB
    obtain ⟨ψ, hψ₁, hψ₂⟩ := hJ.crossingEquiv
    refine ⟨(sigmaSetUnionEquiv (fun i => (C i).Γ.Crossing) hdisj).trans ((φA.sumCongr φB).trans ψ),
      fun q => ?_⟩
    have key := sigmaSetUnionEquiv_elim (fun i => (C i).Γ.Crossing) hdisj q
    simp only [Equiv.trans_apply]
    rcases hq : sigmaSetUnionEquiv (fun i => (C i).Γ.Crossing) hdisj q with r | r
    · rw [hq, Sum.elim_inl] at key
      rw [Equiv.sumCongr_apply, Sum.map_inl, hψ₁, hφA]
      exact congrArg (fun p : Σ i, (C i).Γ.Crossing => (C p.1).sign p.2) key
    · rw [hq, Sum.elim_inr] at key
      rw [Equiv.sumCongr_apply, Sum.map_inr, hψ₂, hφB]
      exact congrArg (fun p : Σ i, (C i).Γ.Crossing => (C p.1).sign p.2) key

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

/-! ### U-R2 toolbox -/

/-- Two permutations that agree off one point agree everywhere (bijectivity forces the image
of the remaining point). -/
theorem perm_eq_of_eq_off_point {β : Type*} (σ σ' : Equiv.Perm β) (u : β)
    (h : ∀ w, w ≠ u → σ w = σ' w) : σ = σ' := by
  refine Equiv.ext fun w => ?_
  by_cases hw : w = u
  · subst hw
    by_contra hne
    have h1 : σ (σ.symm (σ' w)) = σ' w := σ.apply_symm_apply _
    by_cases hz : σ.symm (σ' w) = w
    · rw [hz] at h1
      exact hne h1
    · have h2 := h _ hz
      rw [h1] at h2
      exact hz (σ'.injective h2).symm
  · exact h w hw

/-- U-R2 (permutation level): if every retained point other than `u` has a retained successor,
then swapping two UNRETAINED points does not change the first return to the retained set: off `u`
both first returns are the plain successor, and a permutation is determined by its values off one
point. -/
theorem firstReturn_mul_swap_eq_of_succ_mem {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p] (a b : α) (ha : ¬ p a) (hb : ¬ p b)
    (u : {v // p v}) (hI : ∀ w : {v // p v}, w ≠ u → p (f w.1)) :
    firstReturn (f * Equiv.swap a b) p = firstReturn f p := by
  apply perm_eq_of_eq_off_point _ _ u
  intro w hw
  have hwa : w.1 ≠ a := fun h => ha (h ▸ w.2)
  have hwb : w.1 ≠ b := fun h => hb (h ▸ w.2)
  have hsw : (f * Equiv.swap a b) w.1 = f w.1 := mul_swap_apply_of_ne_of_ne f a b hwa hwb
  apply Subtype.ext
  rw [firstReturn_apply_of_mem (f * Equiv.swap a b) p w (by rw [hsw]; exact hI w hw),
    firstReturn_apply_of_mem f p w (hI w hw), hsw]

/-- Smoothing preserves realizability (the accepted gate `exists_smoothing_record_visit`
transported along the realizing isomorphism by `RecordIso.smooth`). -/
theorem IsRealizable.smooth {τ : Record} (h : IsRealizable τ) (x : τ.M) :
    IsRealizable (τ.smooth x) := by
  obtain ⟨D, ⟨ι⟩⟩ := h
  obtain ⟨D₀, -, ⟨κ⟩⟩ := exists_smoothing_record_visit D (ι.Φ.symm x).1 (ι.Φ.symm x) rfl
  have e : RecordIso (D.record.smooth (ι.Φ.symm x)) (τ.smooth (ι.Φ (ι.Φ.symm x))) := ι.smooth _
  rw [Equiv.apply_symm_apply] at e
  exact ⟨D₀, ⟨κ.trans e⟩⟩

namespace Record

variable (τ : Record)

/-- The one-circle record of a pair-closed set of occurrences all lying on one circle: those
occurrences with their first-return successor, old pairing, bits and signs, on a single
parametrizing circle (`Unit`).  Used as the invariant carrier of U-R2; `restrictCrossings S₁`
of a one-circle record is isomorphic to it (`onePred_iso_restrictCrossings`). -/
noncomputable def onePred (p : τ.M → Prop) [DecidablePred p] (hp : ∀ v, p (τ.pair v) ↔ p v)
    (h1 : ∀ v w, p v → p w → τ.comp v = τ.comp w) : Record where
  comps := Unit
  M := {v // p v}
  comp _ := ()
  succ := firstReturn τ.succ p
  pair := τ.pair.subtypePerm hp
  isOver v := τ.isOver v.1
  sgn v := τ.sgn v.1
  succ_comp _ := rfl
  succ_cycle v w _ :=
    firstReturn_sameCycle_of_sameCycle _ _ (τ.succ_cycle _ _ (h1 v.1 w.1 v.2 w.2))
  pair_ne v h := τ.pair_ne v.1 (congrArg Subtype.val h)
  pair_invol v := Subtype.ext (τ.pair_invol v.1)
  bit_pair v := τ.bit_pair v.1
  sgn_pair v := τ.sgn_pair v.1
  sgn_ne v := τ.sgn_ne v.1

/-- U-R2 path lemma: when every retained point other than `u` has a retained successor, the
`succ`-path from a retained point `w` on the circle of `u` to `u` consists of retained points, so
it avoids the two unretained swap points `x, τ x` and the reconnected successor still carries `w`
to `u`. -/
theorem reconnect_sameCycle_of_succ_mem (p : τ.M → Prop) (x u : τ.M) (hx : ¬ p x)
    (hx' : ¬ p (τ.pair x)) (hI : ∀ w, p w → w ≠ u → p (τ.succ w)) (w : τ.M) (hw : p w)
    (hc : τ.comp w = τ.comp u) : (τ.reconnect x).SameCycle w u := by
  obtain ⟨n, hn⟩ := (τ.succ_cycle w u hc).exists_nat_pow_eq
  have hex : ∃ n, (τ.succ ^ n) w = u := ⟨n, hn⟩
  have hmu : (τ.succ ^ Nat.find hex) w = u := Nat.find_spec hex
  have hall : ∀ j, j ≤ Nat.find hex → p ((τ.succ ^ j) w) := by
    intro j
    induction j with
    | zero => intro _; simpa using hw
    | succ j ih =>
      intro hj
      have hpj := ih (by omega)
      have hne : (τ.succ ^ j) w ≠ u := Nat.find_min hex (by omega)
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hI _ hpj hne
  refine ⟨Nat.find hex, ?_⟩
  rw [zpow_natCast]
  show ((τ.succ * Equiv.swap x (τ.pair x)) ^ Nat.find hex) w = u
  rw [mul_swap_pow_apply_of_forall_ne τ.succ x (τ.pair x) w _ (fun j hj => ?_)]
  · exact hmu
  · have hpj := hall j hj.le
    exact ⟨fun h => hx (h ▸ hpj), fun h => hx' (h ▸ hpj)⟩

/-- U-R2: the retained first return of the smoothed record is the old retained first return
(`firstReturn_firstReturn`, then `firstReturn_mul_swap_eq_of_succ_mem`). -/
theorem smooth_firstReturn_val_of_succ_mem (p : τ.M → Prop) [DecidablePred p] (x : τ.M)
    (hx : ¬ p x) (hx' : ¬ p (τ.pair x)) (u : τ.M) (hu : p u)
    (hI : ∀ w, p w → w ≠ u → p (τ.succ w)) (hSK : ∀ v, p v → τ.SmoothKeep x v)
    (w : {m : {m : τ.M // τ.SmoothKeep x m} // p m.1}) :
    ((firstReturn (firstReturn (τ.reconnect x) (τ.SmoothKeep x)) (fun m => p m.1)) w).1.1 =
      (firstReturn τ.succ p ⟨w.1.1, w.2⟩).1 := by
  have hand : ∀ m, (τ.SmoothKeep x m ∧ p m) ↔ p m := fun m =>
    ⟨fun h => h.2, fun h => ⟨hSK m h, h⟩⟩
  rw [firstReturn_firstReturn, firstReturn_congr_pred (τ.reconnect x) _ p hand,
    show τ.reconnect x = τ.succ * Equiv.swap x (τ.pair x) from rfl,
    firstReturn_mul_swap_eq_of_succ_mem τ.succ p x (τ.pair x) hx hx' ⟨u, hu⟩
      (fun w hw => hI w.1 w.2 (fun h => hw (Subtype.ext h)))]

/-- U-R2 core induction (record level, no geometry beyond the smoothing gate): a realizable
record `τ` with a pair-closed retained set `p` such that all retained points lie on the circle of
the retained point `u` and every retained point other than `u` has a retained successor (all
unretained points of that circle lie in the single gap after `u`) has a realizable one-circle
retained record.  Induction on the number of unretained occurrences: smooth any unretained
crossing; the invariant is trivially preserved (`smooth_succ_val_of_not_mem`,
`reconnect_sameCycle_of_succ_mem`), the retained first return is unchanged
(`firstReturn_mul_swap_eq_of_succ_mem`), and at the end (`p = univ`) restrict the realizing
diagram to the circle of `u` (`Diagram.isRealizable_restrict`, `RecordIso.restrict`). -/
theorem isRealizable_onePred_of_succ_mem (n : ℕ) :
    ∀ (τ : Record) (p : τ.M → Prop) [DecidablePred p] (hp : ∀ v, p (τ.pair v) ↔ p v)
      (u : τ.M) (_hu : p u) (hone : ∀ v, p v → τ.comp v = τ.comp u)
      (_hI : ∀ w, p w → w ≠ u → p (τ.succ w)) (_hn : Fintype.card {v // ¬ p v} = n)
      (_hreal : IsRealizable τ),
      IsRealizable (τ.onePred p hp (fun v w hv hw => (hone v hv).trans (hone w hw).symm)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro τ p _ hp u hu hone hI hn hreal
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- base: every occurrence is retained; restrict the realization to the circle of `u`
    have hall : ∀ v, p v := fun v => by
      by_contra hv
      exact (Fintype.card_eq_zero_iff.mp hn).elim ⟨v, hv⟩
    obtain ⟨D, ⟨ι⟩⟩ := hreal
    have hB : ∀ c', ι.e c' ∈ ({τ.comp u} : Finset τ.comps) ↔
        c' ∈ ({ι.e.symm (τ.comp u)} : Finset D.record.comps) := by
      intro c'
      simp only [Finset.mem_singleton]
      exact (Equiv.eq_symm_apply ι.e).symm
    have hreal' : IsRealizable (D.record.restrict {ι.e.symm (τ.comp u)}) :=
      D.isRealizable_restrict {ι.e.symm (τ.comp u)} (Finset.singleton_nonempty _)
    refine (hreal'.of_iso (ι.restrict _ {τ.comp u} hB)).of_iso ?_
    have hkeep : ∀ v, τ.RestrictKeep {τ.comp u} v ↔ p v := fun v =>
      ⟨fun _ => hall v, fun _ => ⟨Finset.mem_singleton.mpr (hone v (hall v)),
        Finset.mem_singleton.mpr (hone _ (hall _))⟩⟩
    exact
      { e := ⟨fun _ => (), fun _ => ⟨τ.comp u, Finset.mem_singleton_self _⟩,
          fun ⟨_, hc'⟩ => Subtype.ext (Finset.mem_singleton.mp hc').symm, fun _ => rfl⟩
        Φ := Equiv.subtypeEquivRight hkeep
        comp_eq := fun _ => rfl
        succ_eq := fun v => Subtype.ext (by
          show (firstReturn τ.succ (τ.RestrictKeep {τ.comp u}) v).1 =
            (firstReturn τ.succ p ⟨v.1, (hkeep v.1).mp v.2⟩).1
          rw [firstReturn_apply_of_mem _ _ v ((hkeep _).mpr (hall _)),
            firstReturn_apply_of_mem _ _ _ (hall _)])
        pair_eq := fun _ => rfl
        bit_eq := fun _ => rfl
        sgn_eq := fun _ => rfl }
  · -- step: smooth an unretained crossing
    obtain ⟨⟨x, hx⟩⟩ : Nonempty {v // ¬ p v} := Fintype.card_pos_iff.mp (by rw [hn]; exact hpos)
    have hx' : ¬ p (τ.pair x) := fun h => hx ((hp x).mp h)
    have hSK : ∀ v, p v → τ.SmoothKeep x v := fun v hv =>
      (τ.smoothKeep_iff x v).mpr ⟨fun h => hx (h ▸ hv), fun h => hx' (h ▸ hv)⟩
    have hp' : ∀ w : (τ.smooth x).M, p ((τ.smooth x).pair w).1 ↔ p w.1 := fun w => hp w.1
    have hone' : ∀ w : (τ.smooth x).M, p w.1 →
        (τ.smooth x).comp w = (τ.smooth x).comp ⟨u, hSK u hu⟩ := fun w hw =>
      (τ.smooth_comp_eq_iff x w ⟨u, hSK u hu⟩).mpr
        (τ.reconnect_sameCycle_of_succ_mem p x u hx hx' hI w.1 hw (hone w.1 hw))
    have hI' : ∀ w : (τ.smooth x).M, p w.1 → w ≠ ⟨u, hSK u hu⟩ → p ((τ.smooth x).succ w).1 := by
      intro w hw hwu
      have h1 : p (τ.succ w.1) := hI w.1 hw (fun h => hwu (Subtype.ext h))
      rw [τ.smooth_succ_val_of_not_mem x w (hSK _ h1)]
      exact h1
    have hlt : Fintype.card {w : (τ.smooth x).M // ¬ p w.1} < n := by
      rw [← hn]
      refine lt_of_le_of_lt (Fintype.card_le_of_injective
        (fun w : {w : (τ.smooth x).M // ¬ p w.1} =>
          (⟨⟨w.1.1, w.2⟩, fun h => τ.not_smoothKeep_self x (by
            have := w.1.2
            rw [h] at this
            exact this)⟩ : {v : {v // ¬ p v} // v.1 ≠ x})) ?_)
        (Fintype.card_subtype_lt (x := ⟨x, hx⟩) (by simp))
      intro w₁ w₂ h
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1.1) h))
    have key := ih _ hlt (τ.smooth x) (fun w => p w.1) hp' ⟨u, hSK u hu⟩ hu hone' hI' rfl
      (hreal.smooth x)
    refine key.of_iso ?_
    exact
      { e := Equiv.refl Unit
        Φ := Equiv.subtypeSubtypeEquivSubtype (fun {v} hv => hSK v hv)
        comp_eq := fun _ => rfl
        succ_eq := fun w => Subtype.ext
          (τ.smooth_firstReturn_val_of_succ_mem p x hx hx' u hu hI hSK ⟨w.1, w.2⟩)
        pair_eq := fun _ => rfl
        bit_eq := fun _ => rfl
        sgn_eq := fun _ => rfl }

/-- U-R2 helper: a positive `steps` value is a genuine step count. -/
theorem steps_pos_spec (v w : τ.M) (h : 0 < τ.steps v w) : (τ.succ ^ τ.steps v w) v = w := by
  unfold steps at h ⊢
  split_ifs at h ⊢ with hex
  · exact Nat.find_spec hex
  · exact absurd h (lt_irrefl 0)

/-- U-R2 helper: `steps` is the least step count. -/
theorem steps_le_of_pow_eq (v w : τ.M) (n : ℕ) (h : (τ.succ ^ n) v = w) : τ.steps v w ≤ n := by
  have hex : ∃ n, (τ.succ ^ n) v = w := ⟨n, h⟩
  unfold steps
  rw [dite_eq_left hex]
  exact Nat.find_min' hex h

/-- U-R2 helper: the `S₁`-first return inside `restrictCrossings S` is the `S₁`-first return of
`τ` (`firstReturn_firstReturn`, `S₁ ⊆ S`). -/
theorem restrictCrossings_firstReturn_val {S₁ S : Set τ.Crossing} (hsub : S₁ ⊆ S)
    (w : {m : {m : τ.M // τ.CrossKeep S m} // τ.CrossKeep S₁ m.1}) :
    ((firstReturn (firstReturn τ.succ (τ.CrossKeep S)) (fun m => τ.CrossKeep S₁ m.1)) w).1.1 =
      (firstReturn τ.succ (τ.CrossKeep S₁) ⟨w.1.1, w.2⟩).1 := by
  rw [firstReturn_firstReturn, firstReturn_congr_pred τ.succ _ (τ.CrossKeep S₁)
    (fun m => ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩)]

end Record

/-- Realization chain, record part 1 (ANALYSED ONLY, PLAN_FINAL §5): smoothing away the crossings of
`S \ S₁` when they lie in one gap of `S₁` (`GapContiguous`) leaves the `S₁`-first-return successor
unchanged and never splits the `S₁`-circle; restricting the resulting actual diagram to that circle
realizes `restrictCrossings S₁`.  Uses only accepted geometry (`exists_smoothing_record_visit`,
`Diagram.restrict`, `restrictRecordIso`) and `firstReturn` lemmas of the J5/J6 type. -/
theorem isRealizable_restrictCrossings_of_gapContiguous (ρ : Record) (h1 : ρ.componentCount = 1)
    {S₁ S : Set ρ.Crossing} (hsub : S₁ ⊆ S) (hS : IsRealizable (ρ.restrictCrossings S))
    (hgap : ρ.GapContiguous S₁ S) : IsRealizable (ρ.restrictCrossings S₁) := by
  obtain ⟨u, hu, hg⟩ := hgap
  have hsub' : ∀ v, ρ.CrossKeep S₁ v → ρ.CrossKeep S v := fun v hv => hsub hv
  have hss : Subsingleton ρ.comps := Fintype.card_le_one_iff_subsingleton.mp h1.le
  -- the retained set `S₁` inside the realizable record `restrictCrossings S`
  have hp : ∀ w : (ρ.restrictCrossings S).M,
      ρ.CrossKeep S₁ ((ρ.restrictCrossings S).pair w).1 ↔ ρ.CrossKeep S₁ w.1 :=
    fun w => ρ.crossKeep_pair_iff S₁ w.1
  have hone : ∀ w : (ρ.restrictCrossings S).M, ρ.CrossKeep S₁ w.1 →
      (ρ.restrictCrossings S).comp w = (ρ.restrictCrossings S).comp ⟨u, hsub' u hu⟩ :=
    fun _ _ => @Subsingleton.elim ρ.comps hss _ _
  -- gap contiguity ⇒ every `S₁`-point other than `u` has an `S₁`-point as `S`-first return
  have hI : ∀ w : (ρ.restrictCrossings S).M, ρ.CrossKeep S₁ w.1 → w ≠ ⟨u, hsub' u hu⟩ →
      ρ.CrossKeep S₁ ((ρ.restrictCrossings S).succ w).1 := by
    intro w hw hwu
    by_contra hv
    -- `v`, the `S`-first return of `w`, is an `S \ S₁` occurrence, hence lies in the gap after `u`
    obtain ⟨hpos, hlt⟩ := hg _ ((ρ.restrictCrossings S).succ w).2 hv
    have hj : (ρ.succ ^ ρ.steps u ((ρ.restrictCrossings S).succ w).1) u =
        ((ρ.restrictCrossings S).succ w).1 := ρ.steps_pos_spec _ _ hpos
    have hr : ρ.steps u ((ρ.restrictCrossings S₁).succ ⟨u, hu⟩).1 ≤
        returnTime ρ.succ (ρ.CrossKeep S₁) u hu :=
      ρ.steps_le_of_pow_eq _ _ _ (firstReturn_apply ρ.succ (ρ.CrossKeep S₁) ⟨u, hu⟩).symm
    have hk : (ρ.succ ^ returnTime ρ.succ (ρ.CrossKeep S) w.1 w.2) w.1 =
        ((ρ.restrictCrossings S).succ w).1 :=
      (firstReturn_apply ρ.succ (ρ.CrossKeep S) w).symm
    have hjr : ρ.steps u ((ρ.restrictCrossings S).succ w).1 <
        returnTime ρ.succ (ρ.CrossKeep S₁) u hu := lt_of_lt_of_le hlt hr
    have hkpos : 0 < returnTime ρ.succ (ρ.CrossKeep S) w.1 w.2 := returnTime_pos _ _ _ _
    rcases Nat.lt_or_ge (ρ.steps u ((ρ.restrictCrossings S).succ w).1)
      (returnTime ρ.succ (ρ.CrossKeep S) w.1 w.2) with hjk | hkj
    · -- `u = succ ^ (k - j) w` would be an `S`-point strictly before the `S`-first return of `w`
      have hu' : u = (ρ.succ ^ (returnTime ρ.succ (ρ.CrossKeep S) w.1 w.2 -
          ρ.steps u ((ρ.restrictCrossings S).succ w).1)) w.1 := by
        apply (ρ.succ ^ ρ.steps u ((ρ.restrictCrossings S).succ w).1).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hjk.le, hk]
        exact hj
      refine returnTime_min ρ.succ (ρ.CrossKeep S) w.1 w.2
        (j := returnTime ρ.succ (ρ.CrossKeep S) w.1 w.2 -
          ρ.steps u ((ρ.restrictCrossings S).succ w).1) (by omega) (by omega) ?_
      rw [← hu']
      exact hsub' u hu
    · -- `w = succ ^ (j - k) u` lies in the gap: it is `u` (excluded) or unretained (excluded)
      have hw' : w.1 = (ρ.succ ^ (ρ.steps u ((ρ.restrictCrossings S).succ w).1 -
          returnTime ρ.succ (ρ.CrossKeep S) w.1 w.2)) u := by
        apply (ρ.succ ^ returnTime ρ.succ (ρ.CrossKeep S) w.1 w.2).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hkj, hj]
        exact hk
      rcases Nat.eq_zero_or_pos (ρ.steps u ((ρ.restrictCrossings S).succ w).1 -
          returnTime ρ.succ (ρ.CrossKeep S) w.1 w.2) with h0 | h0
      · apply hwu
        apply Subtype.ext
        rw [h0, pow_zero, Equiv.Perm.one_apply] at hw'
        exact hw'
      · refine returnTime_min ρ.succ (ρ.CrossKeep S₁) u hu h0 (by omega) ?_
        rw [← hw']
        exact hw
  -- the smoothing-away induction, then the identification with `restrictCrossings S₁`
  have key := Record.isRealizable_onePred_of_succ_mem _ (ρ.restrictCrossings S)
    (fun w => ρ.CrossKeep S₁ w.1) hp ⟨u, hsub' u hu⟩ hu hone hI rfl hS
  refine key.of_iso ?_
  exact
    { e := (Fintype.equivOfCardEq (by rw [Fintype.card_unit]; exact h1.symm) : Unit ≃ ρ.comps)
      Φ := Equiv.subtypeSubtypeEquivSubtype (fun {v} hv => hsub' v hv)
      comp_eq := fun _ => @Subsingleton.elim ρ.comps hss _ _
      succ_eq := fun w => Subtype.ext (ρ.restrictCrossings_firstReturn_val hsub ⟨w.1, w.2⟩)
      pair_eq := fun _ => rfl
      bit_eq := fun _ => rfl
      sgn_eq := fun _ => rfl }

/-! ### Unit U-R3a — R3 parts (a)-(c): the `steps`/`ArcBetween` toolbox on a one-circle record and
the one-gap lemma of the printed mp:blocks proof (sm-3:1637-1663).  PROVED (2026-09-14); consumed by
unit U-R3b (parts (d)-(e) of `restrictCrossings_join_decomp`).  Nothing below changes a fixed
statement or definition; every lemma is fully proved. -/

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

/-! ### Unit U-R3b — R3 parts (d)-(e): the consecutive block and the join identity
(mp:blocks proof, sm-3:1653-1669).  PROVED (2026-09-14); consumes the U-R3a toolbox above and
`RecordIso.nonempty_of_occ` (unit U-J4a, section G.0).  Nothing below changes a fixed statement or
definition; every lemma is fully proved.

(e) is proved for ANY split `S = S₁ ⊔ S₂` of a crossing set of a one-circle record in which each
part lies in one gap of the other (`exists_iso_joinRecord_of_gaps`): with `μ₁.gap := u₁` (the
`S₁`-occurrence just before the `S₂`-gap) and `μ₂.gap := u₂` (the `S₂`-occurrence just before the
`S₁`-gap) the `S`-first return agrees with the `S₁`- and `S₂`-first returns away from the gap
occurrences (`succ_restrictCrossings_eq_of_gap`) and crosses over at them
(`succ_restrictCrossings_gap_eq`), which is exactly `joinSucc`.  (d) chooses the block `T ⊆ S` with
the longest gap over all (block, occurrence) pairs (`exists_block_gap`) and the `S \ T`-occurrence
farthest from that gap's start (`exists_gap_compl`). -/

namespace Record

variable (ρ : Record)

/-! ### R3(e), preliminaries: gap marks and the occurrence bijection of a split `S = S₁ ⊔ S₂` -/

/-- The mark of a restricted record at a retained occurrence `u`: the marked circle is the circle
of `u`, the gap lies just after `u`. -/
def gapMark (S : Set ρ.Crossing) (u : ρ.M) (hu : ρ.CrossKeep S u) :
    (ρ.restrictCrossings S).Mark where
  comp := ρ.comp u
  gap := some ⟨u, hu⟩
  gap_comp v hv := by
    obtain rfl := Option.some.inj hv
    rfl
  gap_none h := absurd h (Option.some_ne_none _)

@[simp] theorem gapMark_gap (S : Set ρ.Crossing) (u : ρ.M) (hu : ρ.CrossKeep S u) :
    (ρ.gapMark S u hu).gap = some ⟨u, hu⟩ := rfl

section Split

variable {S₁ S₂ S : Set ρ.Crossing}

theorem crossKeep_or_of_union (hS : S₁ ∪ S₂ = S) {v : ρ.M} (hv : ρ.CrossKeep S v) :
    ρ.CrossKeep S₁ v ∨ ρ.CrossKeep S₂ v := by
  have h : ρ.crossingOf v ∈ S₁ ∪ S₂ := by rw [hS]; exact hv
  exact h

theorem crossKeep_left_of_union (hS : S₁ ∪ S₂ = S) {v : ρ.M} (hv : ρ.CrossKeep S₁ v) :
    ρ.CrossKeep S v := by
  show ρ.crossingOf v ∈ S
  rw [← hS]; exact Or.inl hv

theorem crossKeep_right_of_union (hS : S₁ ∪ S₂ = S) {v : ρ.M} (hv : ρ.CrossKeep S₂ v) :
    ρ.CrossKeep S v := by
  show ρ.crossingOf v ∈ S
  rw [← hS]; exact Or.inr hv

theorem not_crossKeep_left_of_right (hdisj : Disjoint S₁ S₂) {v : ρ.M} (hv : ρ.CrossKeep S₂ v) :
    ¬ ρ.CrossKeep S₁ v := fun h => Set.disjoint_left.mp hdisj h hv

theorem not_crossKeep_right_of_left (hdisj : Disjoint S₁ S₂) {v : ρ.M} (hv : ρ.CrossKeep S₁ v) :
    ¬ ρ.CrossKeep S₂ v := fun h => Set.disjoint_left.mp hdisj hv h

/-- The occurrence bijection of a split `S = S₁ ⊔ S₂`: the retained occurrences of `S` are those
of `S₁` together with those of `S₂` ("occurrences `M_A ⊕ M_B`"). -/
noncomputable def splitOcc (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂) :
    (ρ.restrictCrossings S).M ≃ (ρ.restrictCrossings S₁).M ⊕ (ρ.restrictCrossings S₂).M where
  toFun v := if h : ρ.CrossKeep S₁ v.1 then Sum.inl ⟨v.1, h⟩
    else Sum.inr ⟨v.1, (ρ.crossKeep_or_of_union hS v.2).resolve_left h⟩
  invFun := Sum.elim (fun a => ⟨a.1, ρ.crossKeep_left_of_union hS a.2⟩)
    (fun b => ⟨b.1, ρ.crossKeep_right_of_union hS b.2⟩)
  left_inv v := by
    dsimp only
    by_cases h : ρ.CrossKeep S₁ v.1
    · rw [dite_eq_left h]; rfl
    · rw [dite_eq_right h]; rfl
  right_inv z := by
    rcases z with a | b
    · show (if h : ρ.CrossKeep S₁ a.1 then _ else _) = Sum.inl a
      rw [dite_eq_left a.2]
      rfl
    · show (if h : ρ.CrossKeep S₁ b.1 then _ else _) = Sum.inr b
      rw [dite_eq_right (ρ.not_crossKeep_left_of_right hdisj b.2)]
      rfl

theorem splitOcc_apply_of_mem (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂)
    {v : (ρ.restrictCrossings S).M} (h : ρ.CrossKeep S₁ v.1) :
    ρ.splitOcc hS hdisj v = Sum.inl ⟨v.1, h⟩ := by
  show (if h : ρ.CrossKeep S₁ v.1 then _ else _) = _
  rw [dite_eq_left h]

theorem splitOcc_apply_of_not_mem (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂)
    {v : (ρ.restrictCrossings S).M} (h : ¬ ρ.CrossKeep S₁ v.1) :
    ρ.splitOcc hS hdisj v = Sum.inr ⟨v.1, (ρ.crossKeep_or_of_union hS v.2).resolve_left h⟩ := by
  show (if h : ρ.CrossKeep S₁ v.1 then _ else _) = _
  rw [dite_eq_right h]

end Split

/-! ### R3(e): the first return of a split record

If every occurrence of `S \ K` lies in the `K`-gap after `g`, the `S`-first return from a retained
occurrence `v ≠ g` of `K` is its `K`-first return (the `K`-gap after `v` contains no `S`-point), and
the `S`-first return from the gap occurrence of one part is the first return of the other part from
its own gap occurrence: this is `joinSucc` at the marks `gapMark`. -/

/-- The first return of a restricted record, characterised by distances (the `restrictCrossings`
form of `firstReturn_val_eq_iff`). -/
theorem restrictCrossings_succ_val_eq_iff (h1 : ρ.componentCount = 1) (S : Set ρ.Crossing)
    {u : ρ.M} (hu : ρ.CrossKeep S u) (w : ρ.M) :
    ((ρ.restrictCrossings S).succ ⟨u, hu⟩).1 = w ↔
      ρ.CrossKeep S w ∧ w ≠ u ∧ ∀ k, ρ.CrossKeep S k → k ≠ u → ρ.steps u w ≤ ρ.steps u k :=
  ρ.firstReturn_val_eq_iff _ h1 ⟨u, hu⟩ (ρ.crossKeep_exists_ne S hu) w

/-- Away from the gap occurrence, restricting to `S` or to `K ⊆ S` gives the same first return. -/
theorem succ_restrictCrossings_eq_of_gap (h1 : ρ.componentCount = 1) {K S : Set ρ.Crossing}
    (hKS : K ⊆ S) {g : ρ.M} (hg : ρ.CrossKeep K g)
    (hgap : ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep K w →
      ρ.ArcBetween g w ((ρ.restrictCrossings K).succ ⟨g, hg⟩).1)
    {v : ρ.M} (hv : ρ.CrossKeep K v) (hvg : v ≠ g) :
    ((ρ.restrictCrossings S).succ ⟨v, hKS hv⟩).1 = ((ρ.restrictCrossings K).succ ⟨v, hv⟩).1 := by
  rw [ρ.restrictCrossings_succ_val_eq_iff h1 S (hKS hv)]
  refine ⟨hKS ((ρ.restrictCrossings K).succ ⟨v, hv⟩).2,
    ρ.firstReturn_val_ne _ h1 ⟨v, hv⟩ ((ρ.crossKeep_pair_iff K v).mpr hv) (ρ.pair_ne v),
    fun k hk hkv => ?_⟩
  by_cases hkK : ρ.CrossKeep K k
  · exact ρ.steps_firstReturn_le _ h1 ⟨v, hv⟩ hkK hkv
  · refine not_lt.mp fun hlt => hvg (ρ.gap_unique h1 K hv hg ?_ (hgap k hk hkK))
    exact And.intro ((ρ.steps_pos_iff h1 v k).mpr (Ne.symm hkv)) hlt

/-- At the gap occurrence `u₂` of `S₂`, the `S`-first return is the `S₁`-first return of the gap
occurrence `u₁` of `S₁` ("after the gap of `B`, continue into `A` just after its gap"). -/
theorem succ_restrictCrossings_gap_eq (h1 : ρ.componentCount = 1) {S₁ S₂ S : Set ρ.Crossing}
    (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂) {u₁ u₂ : ρ.M}
    (hu₁ : ρ.CrossKeep S₁ u₁) (hu₂ : ρ.CrossKeep S₂ u₂)
    (hg₁ : ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep S₁ w →
      ρ.ArcBetween u₁ w ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).1)
    (hg₂ : ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep S₂ w →
      ρ.ArcBetween u₂ w ((ρ.restrictCrossings S₂).succ ⟨u₂, hu₂⟩).1) :
    ((ρ.restrictCrossings S).succ ⟨u₂, ρ.crossKeep_right_of_union hS hu₂⟩).1 =
      ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).1 := by
  have hu₂S : ρ.CrossKeep S u₂ := ρ.crossKeep_right_of_union hS hu₂
  have hm₁ : ρ.CrossKeep S₁ ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).1 :=
    ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).2
  have hA := hg₁ u₂ hu₂S (ρ.not_crossKeep_left_of_right hdisj hu₂)
  have hB := hg₂ _ (ρ.crossKeep_left_of_union hS hm₁) (ρ.not_crossKeep_right_of_left hdisj hm₁)
  rw [ρ.arcBetween_restrictCrossings_succ_iff h1 S₂ hu₂] at hB
  rw [ρ.restrictCrossings_succ_val_eq_iff h1 S hu₂S]
  refine ⟨ρ.crossKeep_left_of_union hS hm₁, hB.1, fun k hk hku => ?_⟩
  by_cases hk₂ : ρ.CrossKeep S₂ k
  · exact (hB.2 k hk₂ hku).le
  · have hk₁ : ρ.CrossKeep S₁ k := (ρ.crossKeep_or_of_union hS hk).resolve_right hk₂
    have hnk : ¬ ρ.ArcBetween u₁ k ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).1 :=
      ρ.not_arcBetween_firstReturn _ h1 ⟨u₁, hu₁⟩ hk₁
    simp only [ρ.arcBetween_iff_posBetween h1 u₂, PosBetween] at hA hnk
    rw [ρ.steps_self] at hA
    omega

/-- The occurrence bijection of a split commutes with the successors: the `S`-first return is the
joined successor of the two restricted records at the gap marks. -/
theorem splitOcc_succ (h1 : ρ.componentCount = 1) {S₁ S₂ S : Set ρ.Crossing}
    (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂) {u₁ u₂ : ρ.M}
    (hu₁ : ρ.CrossKeep S₁ u₁) (hu₂ : ρ.CrossKeep S₂ u₂)
    (hg₁ : ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep S₁ w →
      ρ.ArcBetween u₁ w ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).1)
    (hg₂ : ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep S₂ w →
      ρ.ArcBetween u₂ w ((ρ.restrictCrossings S₂).succ ⟨u₂, hu₂⟩).1)
    (v : (ρ.restrictCrossings S).M) :
    ρ.splitOcc hS hdisj ((ρ.restrictCrossings S).succ v) =
      joinSucc (ρ.gapMark S₁ u₁ hu₁) (ρ.gapMark S₂ u₂ hu₂) (ρ.splitOcc hS hdisj v) := by
  have hS₁ : S₁ ⊆ S := fun _ hx => by rw [← hS]; exact Or.inl hx
  have hS₂ : S₂ ⊆ S := fun _ hx => by rw [← hS]; exact Or.inr hx
  by_cases h : ρ.CrossKeep S₁ v.1
  · rw [ρ.splitOcc_apply_of_mem hS hdisj h]
    by_cases hv : v.1 = u₁
    · -- the gap occurrence of `S₁`: continue into `S₂` just after its gap
      have hg : (⟨v.1, h⟩ : (ρ.restrictCrossings S₁).M) = ⟨u₁, hu₁⟩ := Subtype.ext hv
      rw [hg, joinSucc_gap_left _ _ (ρ.gapMark_gap S₁ u₁ hu₁) (ρ.gapMark_gap S₂ u₂ hu₂)]
      have hval : ((ρ.restrictCrossings S).succ v).1 =
          ((ρ.restrictCrossings S₂).succ ⟨u₂, hu₂⟩).1 := by
        have hv' : v = ⟨u₁, hS₁ hu₁⟩ := Subtype.ext hv
        rw [hv']
        exact ρ.succ_restrictCrossings_gap_eq h1 (by rw [Set.union_comm]; exact hS) hdisj.symm
          hu₂ hu₁ hg₂ hg₁
      have hnot : ¬ ρ.CrossKeep S₁ ((ρ.restrictCrossings S).succ v).1 := by
        rw [hval]
        exact ρ.not_crossKeep_left_of_right hdisj ((ρ.restrictCrossings S₂).succ ⟨u₂, hu₂⟩).2
      rw [ρ.splitOcc_apply_of_not_mem hS hdisj hnot]
      exact congrArg Sum.inr (Subtype.ext hval)
    · -- inside `S₁`: the `S₁`-first return
      have hne : (ρ.gapMark S₁ u₁ hu₁).gap ≠ some ⟨v.1, h⟩ := by
        rw [ρ.gapMark_gap]
        exact fun e => hv (congrArg Subtype.val (Option.some.inj e)).symm
      rw [joinSucc_inl_of_ne (ρ.gapMark S₁ u₁ hu₁) (ρ.gapMark S₂ u₂ hu₂) ⟨v.1, h⟩ hne]
      have hval : ((ρ.restrictCrossings S).succ v).1 =
          ((ρ.restrictCrossings S₁).succ ⟨v.1, h⟩).1 :=
        ρ.succ_restrictCrossings_eq_of_gap h1 hS₁ hu₁ hg₁ h hv
      have hmem : ρ.CrossKeep S₁ ((ρ.restrictCrossings S).succ v).1 := by
        rw [hval]; exact ((ρ.restrictCrossings S₁).succ ⟨v.1, h⟩).2
      rw [ρ.splitOcc_apply_of_mem hS hdisj hmem]
      exact congrArg Sum.inl (Subtype.ext hval)
  · rw [ρ.splitOcc_apply_of_not_mem hS hdisj h]
    have h₂ : ρ.CrossKeep S₂ v.1 := (ρ.crossKeep_or_of_union hS v.2).resolve_left h
    by_cases hv : v.1 = u₂
    · -- the gap occurrence of `S₂`: continue into `S₁` just after its gap
      have hg : (⟨v.1, (ρ.crossKeep_or_of_union hS v.2).resolve_left h⟩ :
          (ρ.restrictCrossings S₂).M) = ⟨u₂, hu₂⟩ := Subtype.ext hv
      rw [hg, joinSucc_gap_right _ _ (ρ.gapMark_gap S₁ u₁ hu₁) (ρ.gapMark_gap S₂ u₂ hu₂)]
      have hval : ((ρ.restrictCrossings S).succ v).1 =
          ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).1 := by
        have hv' : v = ⟨u₂, hS₂ hu₂⟩ := Subtype.ext hv
        rw [hv']
        exact ρ.succ_restrictCrossings_gap_eq h1 hS hdisj hu₁ hu₂ hg₁ hg₂
      have hmem : ρ.CrossKeep S₁ ((ρ.restrictCrossings S).succ v).1 := by
        rw [hval]; exact ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).2
      rw [ρ.splitOcc_apply_of_mem hS hdisj hmem]
      exact congrArg Sum.inl (Subtype.ext hval)
    · -- inside `S₂`: the `S₂`-first return
      have hne : (ρ.gapMark S₂ u₂ hu₂).gap ≠
          some ⟨v.1, (ρ.crossKeep_or_of_union hS v.2).resolve_left h⟩ := by
        rw [ρ.gapMark_gap]
        exact fun e => hv (congrArg Subtype.val (Option.some.inj e)).symm
      rw [joinSucc_inr_of_ne (ρ.gapMark S₁ u₁ hu₁) (ρ.gapMark S₂ u₂ hu₂) _ hne]
      have hval : ((ρ.restrictCrossings S).succ v).1 =
          ((ρ.restrictCrossings S₂).succ ⟨v.1, h₂⟩).1 :=
        ρ.succ_restrictCrossings_eq_of_gap h1 hS₂ hu₂ hg₂ h₂ hv
      have hnot : ¬ ρ.CrossKeep S₁ ((ρ.restrictCrossings S).succ v).1 := by
        rw [hval]
        exact ρ.not_crossKeep_left_of_right hdisj ((ρ.restrictCrossings S₂).succ ⟨v.1, h₂⟩).2
      rw [ρ.splitOcc_apply_of_not_mem hS hdisj hnot]
      exact congrArg Sum.inr (Subtype.ext hval)

/-- The occurrence bijection of a split commutes with the pairings. -/
theorem splitOcc_pair {S₁ S₂ S : Set ρ.Crossing} (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂)
    (v : (ρ.restrictCrossings S).M) :
    ρ.splitOcc hS hdisj ((ρ.restrictCrossings S).pair v) =
      Equiv.Perm.sumCongr (ρ.restrictCrossings S₁).pair (ρ.restrictCrossings S₂).pair
        (ρ.splitOcc hS hdisj v) := by
  by_cases h : ρ.CrossKeep S₁ v.1
  · have h' : ρ.CrossKeep S₁ ((ρ.restrictCrossings S).pair v).1 :=
      (ρ.crossKeep_pair_iff S₁ v.1).mpr h
    rw [ρ.splitOcc_apply_of_mem hS hdisj h, ρ.splitOcc_apply_of_mem hS hdisj h']
    rfl
  · have h' : ¬ ρ.CrossKeep S₁ ((ρ.restrictCrossings S).pair v).1 :=
      fun e => h ((ρ.crossKeep_pair_iff S₁ v.1).mp e)
    rw [ρ.splitOcc_apply_of_not_mem hS hdisj h, ρ.splitOcc_apply_of_not_mem hS hdisj h']
    rfl

/-- The occurrence bijection of a split keeps the over/under bits. -/
theorem splitOcc_isOver {S₁ S₂ S : Set ρ.Crossing} (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂)
    (v : (ρ.restrictCrossings S).M) :
    Sum.elim (ρ.restrictCrossings S₁).isOver (ρ.restrictCrossings S₂).isOver
      (ρ.splitOcc hS hdisj v) = (ρ.restrictCrossings S).isOver v := by
  by_cases h : ρ.CrossKeep S₁ v.1
  · rw [ρ.splitOcc_apply_of_mem hS hdisj h]
    rfl
  · rw [ρ.splitOcc_apply_of_not_mem hS hdisj h]
    rfl

/-- The occurrence bijection of a split keeps the signs. -/
theorem splitOcc_sgn {S₁ S₂ S : Set ρ.Crossing} (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂)
    (v : (ρ.restrictCrossings S).M) :
    Sum.elim (ρ.restrictCrossings S₁).sgn (ρ.restrictCrossings S₂).sgn
      (ρ.splitOcc hS hdisj v) = (ρ.restrictCrossings S).sgn v := by
  by_cases h : ρ.CrossKeep S₁ v.1
  · rw [ρ.splitOcc_apply_of_mem hS hdisj h]
    rfl
  · rw [ρ.splitOcc_apply_of_not_mem hS hdisj h]
    rfl

/-- (e) THE JOIN IDENTITY (sm-3:1664-1669): if `S = S₁ ⊔ S₂` on a one-circle record with each part
inside one gap of the other, the restricted record of `S` is the marked join of the restricted
records of `S₁` and `S₂` at the gap marks. -/
theorem exists_iso_joinRecord_of_gaps (h1 : ρ.componentCount = 1) {S₁ S₂ S : Set ρ.Crossing}
    (hS : S₁ ∪ S₂ = S) (hdisj : Disjoint S₁ S₂) {u₁ u₂ : ρ.M}
    (hu₁ : ρ.CrossKeep S₁ u₁) (hu₂ : ρ.CrossKeep S₂ u₂)
    (hg₁ : ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep S₁ w →
      ρ.ArcBetween u₁ w ((ρ.restrictCrossings S₁).succ ⟨u₁, hu₁⟩).1)
    (hg₂ : ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep S₂ w →
      ρ.ArcBetween u₂ w ((ρ.restrictCrossings S₂).succ ⟨u₂, hu₂⟩).1) :
    ∃ (μ₁ : (ρ.restrictCrossings S₁).Mark) (μ₂ : (ρ.restrictCrossings S₂).Mark),
      Nonempty (RecordIso (ρ.restrictCrossings S) (joinRecord μ₁ μ₂)) := by
  -- circle counts: one circle on each side (`c(A) + c(B) - 1 = 1`)
  have hc : Fintype.card (ρ.restrictCrossings S).comps =
      Fintype.card (joinRecord (ρ.gapMark S₁ u₁ hu₁) (ρ.gapMark S₂ u₂ hu₂)).comps := by
    show ρ.componentCount = (joinRecord (ρ.gapMark S₁ u₁ hu₁) (ρ.gapMark S₂ u₂ hu₂)).componentCount
    rw [componentCount_joinRecord]
    show ρ.componentCount = ρ.componentCount + ρ.componentCount - 1
    omega
  exact ⟨ρ.gapMark S₁ u₁ hu₁, ρ.gapMark S₂ u₂ hu₂,
    RecordIso.nonempty_of_occ (ρ.splitOcc hS hdisj)
      (fun v => ρ.splitOcc_succ h1 hS hdisj hu₁ hu₂ hg₁ hg₂ v)
      (fun v => ρ.splitOcc_pair hS hdisj v)
      (fun v => ρ.splitOcc_isOver hS hdisj v)
      (fun v => ρ.splitOcc_sgn hS hdisj v) hc⟩

/-! ### R3(d): a block of `S` whose complement in `S` lies in one of its gaps -/

theorem block_eq_of_mem_supp {H H' : ρ.interlacementGraph.ConnectedComponent} {x : ρ.Crossing}
    (hx : x ∈ H.supp) (hx' : x ∈ H'.supp) : H = H' :=
  ((H.mem_supp_iff x).mp hx).symm.trans ((H'.mem_supp_iff x).mp hx')

/-- Distinct blocks have disjoint supports. -/
theorem supp_disjoint_of_ne {H H' : ρ.interlacementGraph.ConnectedComponent} (h : H ≠ H') :
    Disjoint H.supp H'.supp :=
  Set.disjoint_left.mpr fun _ hx hx' => h (ρ.block_eq_of_mem_supp hx hx')

theorem crossKeep_ne_of_block_ne {C T : ρ.interlacementGraph.ConnectedComponent} (hCT : C ≠ T)
    {z z' : ρ.M} (hz : ρ.CrossKeep C.supp z) (hz' : ρ.CrossKeep T.supp z') : z ≠ z' := by
  rintro rfl
  exact hCT (ρ.block_eq_of_mem_supp hz hz')

/-- (d1) the "innermost" block: among all pairs (block `T ⊆ S`, occurrence `u` of `T`) take one
whose `T`-gap after `u` is longest; then every occurrence of `S \ T` lies in that gap.  (Were an
occurrence `w` of another block `C ⊆ S` outside it, `C` would lie in a different gap of `T` by the
one-gap lemma, `T` in one gap of `C`, and that gap of `C` strictly contains the closed arc from `u`
to its `T`-first return — a longer gap.) -/
theorem exists_block_gap (h1 : ρ.componentCount = 1) (S : Set ρ.Crossing)
    (hS : ∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S ∨ Disjoint H.supp S)
    {H₀ : ρ.interlacementGraph.ConnectedComponent} (hH₀ : H₀.supp ⊆ S) :
    ∃ T : ρ.interlacementGraph.ConnectedComponent, T.supp ⊆ S ∧ ∃ u, ∃ hu : ρ.CrossKeep T.supp u,
      ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep T.supp w →
        ρ.ArcBetween u w ((ρ.restrictCrossings T.supp).succ ⟨u, hu⟩).1 := by
  obtain ⟨a₀, ha₀⟩ := H₀.nonempty_supp
  obtain ⟨v₀, rfl⟩ := ρ.crossingOf_surjective a₀
  have : Nonempty {p : ρ.interlacementGraph.ConnectedComponent × ρ.M //
      p.1.supp ⊆ S ∧ ρ.CrossKeep p.1.supp p.2} := ⟨⟨(H₀, v₀), hH₀, ha₀⟩⟩
  obtain ⟨q, hq⟩ := Finite.exists_max
    (fun q : {p : ρ.interlacementGraph.ConnectedComponent × ρ.M //
        p.1.supp ⊆ S ∧ ρ.CrossKeep p.1.supp p.2} =>
      ρ.steps q.1.2 ((ρ.restrictCrossings q.1.1.supp).succ ⟨q.1.2, q.2.2⟩).1)
  obtain ⟨⟨T, u⟩, hTS, hu⟩ := q
  refine ⟨T, hTS, u, hu, fun w hw hwT => ?_⟩
  by_contra hnot
  -- the block `C` of `w` lies in `S` and differs from `T`
  obtain ⟨C, hwC⟩ : ∃ C : ρ.interlacementGraph.ConnectedComponent, ρ.CrossKeep C.supp w :=
    ⟨ρ.interlacementGraph.connectedComponentMk (ρ.crossingOf w),
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩
  have hCS : C.supp ⊆ S := (hS C).resolve_right fun hd => Set.disjoint_left.mp hd hwC hw
  have hCT : C ≠ T := fun h => hwT (h ▸ hwC)
  obtain ⟨u', hu', hgap'⟩ := ρ.exists_gap_of_ne_block h1 T C hCT.symm
  obtain ⟨u'', hu'', hgap''⟩ := ρ.exists_gap_of_ne_block h1 C T hCT
  have hmax : ρ.steps u'' ((ρ.restrictCrossings C.supp).succ ⟨u'', hu''⟩).1 ≤
      ρ.steps u ((ρ.restrictCrossings T.supp).succ ⟨u, hu⟩).1 := hq ⟨(C, u''), hCS, hu''⟩
  -- `C` lies in a gap of `T` other than the gap after `u`, hence outside that gap
  have hu'u : u' ≠ u := by
    rintro rfl
    exact hnot (hgap' w hwC)
  have hout : ∀ z, ρ.CrossKeep C.supp z →
      ¬ ρ.ArcBetween u z ((ρ.restrictCrossings T.supp).succ ⟨u, hu⟩).1 :=
    fun z hz hzu => hu'u (ρ.gap_unique h1 T.supp hu' hu (hgap' z hz) hzu)
  -- positions from `u`: the `C`-gap after `u''` contains `u` and both its ends are beyond the
  -- `T`-first return of `u`, so it is longer than the `T`-gap after `u`
  have p₁ := hgap'' u hu
  have n₁ := hout u'' hu''
  have n₂ := hout _ ((ρ.restrictCrossings C.supp).succ ⟨u'', hu''⟩).2
  have d₁ := ρ.steps_ne_of_ne h1 u (ρ.crossKeep_ne_of_block_ne hCT hu'' hu)
  have d₂ := ρ.steps_ne_of_ne h1 u
    (ρ.crossKeep_ne_of_block_ne hCT ((ρ.restrictCrossings C.supp).succ ⟨u'', hu''⟩).2 hu)
  have d₃ := ρ.steps_ne_of_ne h1 u
    (ρ.crossKeep_ne_of_block_ne hCT hu'' ((ρ.restrictCrossings T.supp).succ ⟨u, hu⟩).2)
  have d₄ := ρ.steps_ne_of_ne h1 u (ρ.crossKeep_ne_of_block_ne hCT
    ((ρ.restrictCrossings C.supp).succ ⟨u'', hu''⟩).2 ((ρ.restrictCrossings T.supp).succ ⟨u, hu⟩).2)
  have e := ρ.steps_eq_of_base h1 u u'' ((ρ.restrictCrossings C.supp).succ ⟨u'', hu''⟩).1
  have := ρ.steps_lt_card h1 u u''
  have := ρ.steps_lt_card h1 u ((ρ.restrictCrossings C.supp).succ ⟨u'', hu''⟩).1
  simp only [ρ.arcBetween_iff_posBetween h1 u, PosBetween] at p₁ n₁ n₂
  rw [ρ.steps_self] at *
  split_ifs at e <;> omega

/-- (d2) with all of `S \ T` in the `T`-gap after `u`, the `(S \ T)`-occurrence `u₁` farthest from
`u` has all of `T` in its `(S \ T)`-gap. -/
theorem exists_gap_compl (h1 : ρ.componentCount = 1) {T S : Set ρ.Crossing} {u : ρ.M}
    (hu : ρ.CrossKeep T u)
    (hgap : ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep T w →
      ρ.ArcBetween u w ((ρ.restrictCrossings T).succ ⟨u, hu⟩).1)
    {x₀ : ρ.M} (hx₀ : ρ.CrossKeep (S \ T) x₀) :
    ∃ u₁, ∃ hu₁ : ρ.CrossKeep (S \ T) u₁, ∀ w, ρ.CrossKeep S w → ¬ ρ.CrossKeep (S \ T) w →
      ρ.ArcBetween u₁ w ((ρ.restrictCrossings (S \ T)).succ ⟨u₁, hu₁⟩).1 := by
  obtain ⟨u₁, hu₁, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (ρ.CrossKeep (S \ T)))
    (ρ.steps u) ⟨x₀, by simpa using hx₀⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu₁ hmax
  refine ⟨u₁, hu₁, fun w hw hw' => ?_⟩
  have hwT : ρ.CrossKeep T w := by
    by_contra h
    exact hw' (show ρ.crossingOf w ∈ S \ T from ⟨hw, h⟩)
  have hu₁S : ρ.CrossKeep S u₁ := (show ρ.crossingOf u₁ ∈ S \ T from hu₁).1
  have hu₁T : ¬ ρ.CrossKeep T u₁ := (show ρ.crossingOf u₁ ∈ S \ T from hu₁).2
  rw [ρ.arcBetween_restrictCrossings_succ_iff h1 (S \ T) hu₁]
  refine ⟨fun h => hu₁T (h ▸ hwT), fun k hk hku₁ => ?_⟩
  have hkS : ρ.CrossKeep S k := (show ρ.crossingOf k ∈ S \ T from hk).1
  have hkT : ¬ ρ.CrossKeep T k := (show ρ.crossingOf k ∈ S \ T from hk).2
  have g₁ := hgap u₁ hu₁S hu₁T
  have g₂ := hgap k hkS hkT
  have hkmax := hmax k hk
  have hnw : ¬ ρ.ArcBetween u w ((ρ.restrictCrossings T).succ ⟨u, hu⟩).1 :=
    ρ.not_arcBetween_firstReturn _ h1 ⟨u, hu⟩ hwT
  have e₁ := ρ.steps_eq_of_base h1 u u₁ w
  have e₂ := ρ.steps_eq_of_base h1 u u₁ k
  have := ρ.steps_ne_of_ne h1 u hku₁
  have := ρ.steps_lt_card h1 u w
  have := ρ.steps_lt_card h1 u k
  have := ρ.steps_lt_card h1 u u₁
  simp only [ρ.arcBetween_iff_posBetween h1 u, PosBetween] at g₁ g₂ hnw
  rw [ρ.steps_self] at *
  split_ifs at e₁ e₂ <;> omega

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
  -- (d) the block `T ⊆ S` with the longest gap has all of `S \ T` in that gap
  obtain ⟨H, H', hHH', hH, hH'⟩ := h2
  obtain ⟨T, hTS, u, hu, hgapT⟩ := ρ.exists_block_gap h1 S hS hH
  -- `S \ T` is nonempty: the other block of `h2`
  have hex : ∃ x₀, ρ.CrossKeep (S \ T.supp) x₀ := by
    have key : ∀ H'' : ρ.interlacementGraph.ConnectedComponent, H''.supp ⊆ S → H'' ≠ T →
        ∃ x₀, ρ.CrossKeep (S \ T.supp) x₀ := by
      intro H'' hsub hne
      obtain ⟨a, ha⟩ := H''.nonempty_supp
      obtain ⟨v, rfl⟩ := ρ.crossingOf_surjective a
      exact ⟨v, show ρ.crossingOf v ∈ S \ T.supp from
        ⟨hsub ha, fun h => hne (ρ.block_eq_of_mem_supp ha h)⟩⟩
    by_cases hHT : H = T
    · exact key H' hH' fun h => hHH' (hHT.trans h.symm)
    · exact key H hH hHT
  obtain ⟨x₀, hx₀⟩ := hex
  -- the `(S \ T)`-occurrence just before the gap of `T`
  obtain ⟨u₁, hu₁, hgap₁⟩ := ρ.exists_gap_compl h1 hu hgapT hx₀
  -- (e) assemble: `S₁ := S \ T`, `S₂ := T`, the join identity at the two gap marks
  refine ⟨S \ T.supp, T.supp, Set.sdiff_union_of_subset hTS, Set.disjoint_sdiff_left,
    ⟨ρ.crossingOf x₀, hx₀⟩, T.nonempty_supp, ?_, ?_, ⟨u₁, hu₁, hgap₁⟩, ⟨u, hu, hgapT⟩,
    ρ.exists_iso_joinRecord_of_gaps h1 (Set.sdiff_union_of_subset hTS) Set.disjoint_sdiff_left
      hu₁ hu hgap₁ hgapT⟩
  · -- every block lies in `S \ T` or is disjoint from it
    intro H₁
    by_cases hHT : H₁ = T
    · subst hHT
      exact Or.inr Set.disjoint_sdiff_right
    · rcases hS H₁ with hsub | hdisj
      · exact Or.inl (Set.subset_sdiff.mpr ⟨hsub, ρ.supp_disjoint_of_ne hHT⟩)
      · exact Or.inr (hdisj.mono_right Set.sdiff_subset)
  · -- every block lies in `T` or is disjoint from it
    intro H₁
    by_cases hHT : H₁ = T
    · subst hHT
      exact Or.inl subset_rfl
    · exact Or.inr (ρ.supp_disjoint_of_ne hHT)

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
  -- a crossing of `S` has its block inside `S` (the block is not disjoint from `S`)
  have block_sub : ∀ S : Set ρ.Crossing,
      (∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S ∨ Disjoint H.supp S) →
      ∀ x ∈ S, (ρ.interlacementGraph.connectedComponentMk x).supp ⊆ S := by
    intro S hS x hx
    rcases hS (ρ.interlacementGraph.connectedComponentMk x) with h' | h'
    · exact h'
    · exact absurd hx (Set.disjoint_left.mp h'
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl))
  -- strong induction on the number of blocks inside `S`
  suffices key : ∀ n : ℕ, ∀ S : Set ρ.Crossing,
      (Finset.univ.filter
        (fun H : ρ.interlacementGraph.ConnectedComponent => H.supp ⊆ S)).card = n →
      (∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S ∨ Disjoint H.supp S) →
      S.Nonempty → IsRealizable (ρ.restrictCrossings S) →
      ∃ J : Diagram, JoinForest C {H | H.supp ⊆ S} J ∧
        Nonempty (RecordIso J.record (ρ.restrictCrossings S)) from
    fun S => key _ S rfl
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro S hcard hS hne hreal
  by_cases h2 : ∃ H H' : ρ.interlacementGraph.ConnectedComponent,
      H ≠ H' ∧ H.supp ⊆ S ∧ H'.supp ⊆ S
  · -- several blocks: split `S = S₁ ⊔ S₂` with the join identity (R3)
    obtain ⟨S₁, S₂, hunion, hdisj, hne₁, hne₂, hblk₁, hblk₂, hgap₁, hgap₂, μ₁, μ₂, ⟨κ⟩⟩ :=
      restrictCrossings_join_decomp ρ h.one_circle S hS h2
    have hsub₁ : S₁ ⊆ S := by rw [← hunion]; exact Set.subset_union_left
    have hsub₂ : S₂ ⊆ S := by rw [← hunion]; exact Set.subset_union_right
    -- both restricted records are realizable (R2)
    have hreal₁ : IsRealizable (ρ.restrictCrossings S₁) :=
      isRealizable_restrictCrossings_of_gapContiguous ρ h.one_circle hsub₁ hreal hgap₁
    have hreal₂ : IsRealizable (ρ.restrictCrossings S₂) :=
      isRealizable_restrictCrossings_of_gapContiguous ρ h.one_circle hsub₂ hreal hgap₂
    -- each part has strictly fewer blocks than `S`: the block of a crossing of the other part
    -- is inside `S` but not inside the part
    have hlt : ∀ T T' : Set ρ.Crossing, T ⊆ S → T' ⊆ S → T'.Nonempty → Disjoint T T' →
        (Finset.univ.filter
          (fun H : ρ.interlacementGraph.ConnectedComponent => H.supp ⊆ T)).card < n := by
      intro T T' hT hT' hne' hd
      rw [← hcard]
      apply Finset.card_lt_card
      have hsubT : Finset.univ.filter
            (fun H : ρ.interlacementGraph.ConnectedComponent => H.supp ⊆ T) ⊆
          Finset.univ.filter
            (fun H : ρ.interlacementGraph.ConnectedComponent => H.supp ⊆ S) := by
        intro H hH
        rw [Finset.mem_filter] at hH ⊢
        exact ⟨hH.1, hH.2.trans hT⟩
      rw [Finset.ssubset_iff_of_subset hsubT]
      obtain ⟨y, hy⟩ := hne'
      refine ⟨ρ.interlacementGraph.connectedComponentMk y, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, block_sub S hS y (hT' hy)⟩
      · rw [Finset.mem_filter]
        intro hcon
        exact Set.disjoint_left.mp hd
          (hcon.2 ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl)) hy
    -- the induction hypothesis on the two parts
    obtain ⟨J₁, hJ₁, ⟨ι₁⟩⟩ :=
      ih _ (hlt S₁ S₂ hsub₁ hsub₂ hne₂ hdisj) S₁ rfl hblk₁ hne₁ hreal₁
    obtain ⟨J₂, hJ₂, ⟨ι₂⟩⟩ :=
      ih _ (hlt S₂ S₁ hsub₂ hsub₁ hne₁ hdisj.symm) S₂ rfl hblk₂ hne₂ hreal₂
    -- the marks transported to the two sub-forests, printed as marked intervals (R1)
    obtain ⟨I₁, hI₁, hc₁, hg₁⟩ := exists_markedInterval_of_mark J₁ (μ₁.map ι₁.symm)
    obtain ⟨I₂, hI₂, hc₂, hg₂⟩ := exists_markedInterval_of_mark J₂ (μ₂.map ι₂.symm)
    let A : MarkedDiagram := ⟨J₁, I₁, hI₁, μ₁.map ι₁.symm, hc₁, hg₁⟩
    let B : MarkedDiagram := ⟨J₂, I₂, hI₂, μ₂.map ι₂.symm, hc₂, hg₂⟩
    -- the given realization of `restrictCrossings S` is the join node
    obtain ⟨X, ⟨ιX⟩⟩ := hreal
    have hX : IsCleanMarkedJoin A B X :=
      ⟨ιX.trans (κ.trans (RecordIso.joinRecord ι₁.symm ι₂.symm μ₁ μ₂))⟩
    -- the index sets: disjoint (a block is nonempty) and covering (a block inside `S` meets
    -- `S₁` or `S₂`, hence lies inside it)
    have hdisjI : Disjoint {H : ρ.interlacementGraph.ConnectedComponent | H.supp ⊆ S₁}
        {H : ρ.interlacementGraph.ConnectedComponent | H.supp ⊆ S₂} := by
      rw [Set.disjoint_left]
      intro H hH₁ hH₂
      obtain ⟨v, hv⟩ := H.nonempty_supp
      exact Set.disjoint_left.mp hdisj (hH₁ hv) (hH₂ hv)
    have hsetI : ({H : ρ.interlacementGraph.ConnectedComponent | H.supp ⊆ S₁} ∪
        {H : ρ.interlacementGraph.ConnectedComponent | H.supp ⊆ S₂}) =
        {H : ρ.interlacementGraph.ConnectedComponent | H.supp ⊆ S} := by
      ext H
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (hH | hH)
        · exact hH.trans hsub₁
        · exact hH.trans hsub₂
      · intro hH
        obtain ⟨v, hv⟩ := H.nonempty_supp
        have hvS : v ∈ S₁ ∪ S₂ := by rw [hunion]; exact hH hv
        rcases hvS with hv₁ | hv₂
        · left
          rcases hblk₁ H with h' | h'
          · exact h'
          · exact absurd hv₁ (Set.disjoint_left.mp h' hv)
        · right
          rcases hblk₂ H with h' | h'
          · exact h'
          · exact absurd hv₂ (Set.disjoint_left.mp h' hv)
    refine ⟨X, ?_, ⟨ιX⟩⟩
    rw [← hsetI]
    exact JoinForest.join A B hJ₁ hJ₂ hdisjI hX
  · -- one block: `S` is the support of the block of any of its crossings; the leaf is supplied
    push Not at h2
    obtain ⟨x, hx⟩ := hne
    obtain ⟨H₀, hxH₀⟩ : ∃ H₀ : ρ.interlacementGraph.ConnectedComponent, x ∈ H₀.supp :=
      ⟨_, (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩
    have hH₀S : H₀.supp ⊆ S := by
      rcases hS H₀ with h' | h'
      · exact h'
      · exact absurd hx (Set.disjoint_left.mp h' hxH₀)
    have huniq : ∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S → H = H₀ := by
      intro H hH
      by_contra hne'
      exact h2 H H₀ hne' hH hH₀S
    have hSeq : S = H₀.supp := by
      apply Set.Subset.antisymm
      · intro y hy
        have hy' := huniq _ (block_sub S hS y hy)
        rw [← hy']
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      · exact hH₀S
    have hsetI : {H : ρ.interlacementGraph.ConnectedComponent | H.supp ⊆ S} = {H₀} := by
      ext H
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨huniq H, fun h' => h' ▸ hH₀S⟩
    refine ⟨C H₀, ?_, ?_⟩
    · rw [hsetI]
      exact JoinForest.leaf H₀
    · rw [hSeq]
      exact h.supplied H₀

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

/-- mp:blocks (`realizes` and hence `product` through the chain of §H.4, now proved;
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
