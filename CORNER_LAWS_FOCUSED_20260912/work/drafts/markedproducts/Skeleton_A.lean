import SM.PolynomialBlock
import SM.ZeroLink
import SM.Stack
import CV.Axioms
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Skeleton A — marked products (mp:join, mp:lowest, mp:blocks, lem:homflyrows), RECORD-FIRST

Architect A (2026-09-14).  Plan of record: work/drafts/markedproducts/PLAN_A.md.
Fixed statements: work/drafts/MarkedProducts_statement.lean — sections A-E (definitions) and F (the four
bundles `JoinData`, `LowestData`, `BlocksData`, `HomflyRowsData`) are copied below BYTE-IDENTICALLY; only
the four row theorems `SM.join`, `SM.lowest`, `SM.blocks`, `SM.homflyrows` carry proofs here (from the
chain lemmas of section G, all `sorry`).  Nothing of the statement file is changed.

Route (record-first): every step of the printed proofs is taken on `Record`s — `Record.joinRecord`,
`Record.switch`, `Record.smooth`, `Record.RBasing`, `Record.restrictCrossings` — and diagrams enter only
through the accepted bridges `Diagram.switchRecordIso`, `exists_smoothing_record_visit`,
`Diagram.skein_induction_based`, `Diagram.exists_underFirst_of_rUnderFirst`, `SM.presentations`,
`SM.stack`, `SM.zero_link`.

* mp:join: nested `(N, b)` inductions (`skein_induction_based` on `A` with `B` quantified; on `B` with
  `A` UNDER-first), marks carried by the based orders (`RBasing.MarkCompatible`: marked circle first,
  based at the gap).  Base: `exists_rUnderFirst_joinRecord` (the join of two UNDER-first based orders is
  UNDER-first).  Step: `joinRecord_switch_inl` / `exists_joinRecord_smooth_inl` (switching / smoothing a
  crossing of one factor is the same operation on the join record), the symmetric cases through
  `exists_joinRecord_comm`.
* mp:lowest: the weight `a^{2Λ} [z^{1−c}] P` is invariant under a mixed switch
  (`weight_switch_of_isMixed`), induction on the number of badly ordered mixed crossings
  (`badMixedCount`) down to `BlockOrdered D id`, where `SM.stack` with singleton blocks, `P_support`
  (knot rows) and `SM.zero_link.over_constant` (`Λ = 0`) give the value.
* lem:homflyrows: `join_value`, `SM.stack.split_union`, `two_component_row` + `P_eq_homfly`,
  `homfly_descent`, `CV.zRow_zero_mul_of_inSupportM_one`.
* mp:blocks: `product`/`realizes` through the printed forest (`realizes` = combinatorial peeling
  `exists_peel` + the two GEOMETRIC lemmas `exists_markedInterval`, `exists_cleanMarkedJoin`, analysed
  in PLAN_A.md §5, NOT proved here); `sign_preserved` and `writhe_additive` are record bookkeeping.

Status: `lake env lean` — no errors; the `sorry`s are exactly the chain lemmas of section G. -/

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

/-! ## G. Architect A — the record-first proof chain (every lemma below is a `sorry` unit; the row
theorems of §F are PROVED from them).  Unit numbers refer to PLAN_A.md §4. -/

namespace Link

/-! ### G.1 Laurent-row algebra (units L1, H3) -/

theorem aPow_add (m n : ℤ) : aPow (m + n) = aPow m * aPow n := LaurentPolynomial.T_add m n

theorem aPow_zero : aPow 0 = 1 := LaurentPolynomial.T_zero

theorem aPow_neg_mul_aPow (n : ℤ) : aPow (-n) * aPow n = 1 := by
  rw [← aPow_add, neg_add_cancel, aPow_zero]

/-- `[z^k] (a f) = a · [z^k] f` (the `a`-shift of a row; `R.a = single (1,0) 1`, `aPow 1 = T 1`). -/
theorem zRow_a_mul (k : ℤ) (f : R) : zRow k (R.a * f) = aPow 1 * zRow k f := by
  sorry

/-- `[z^k] (a⁻¹ f) = a⁻¹ · [z^k] f`. -/
theorem zRow_aInv_mul (k : ℤ) (f : R) : zRow k (R.aInv * f) = aPow (-1) * zRow k f := by
  sorry

/-- `[z^k] (z⁻¹ f) = [z^{k+1}] f`. -/
theorem zRow_zInv_mul (k : ℤ) (f : R) : zRow k (R.zInv * f) = zRow (k + 1) f := by
  sorry

/-- mp:lowest proof (sm-3:1598-1601): "At a mixed crossing the smoothed diagram has `c−1 ≥ 1`
components and support at least `z^{2−c}` … Its multiplication by `z` therefore has support at least
`z^{3−c}`, so contributes nothing to the `1−c` row of the skein."  For `f ∈ M_{c−1}` the row
`[z^{1−c}] (z f)` vanishes (`inSupportM_iff`: `−c ≠ 2 − c + 2j`). -/
theorem zRow_z_mul_eq_zero_of_inSupportM {c : ℕ} (hc : 1 ≤ c) {f : R} (hf : InSupportM (c - 1) f) :
    zRow (1 - (c : ℤ)) (R.z * f) = 0 := by
  sorry

/-- `[z^{k−n}] (δ^n f) = (a − a⁻¹)^n [z^k] f`, `δ = (a − a⁻¹) z⁻¹` (induction on `n`; `zRow_a_mul`,
`zRow_aInv_mul`, `zRow_zInv_mul`, `zRow_sub`). -/
theorem zRow_delta_pow_mul (n : ℕ) (k : ℤ) (f : R) :
    zRow (k - n) (R.delta ^ n * f) = (aPow 1 - aPow (-1)) ^ n * zRow k f := by
  sorry

theorem zRow_one : zRow 0 (1 : R) = 1 := by
  rw [AddMonoidAlgebra.one_def, ← Prod.mk_zero_zero, zRow_single, ite_eq_left rfl]
  exact LaurentPolynomial.T_zero

/-- `M_1 = ℤ[a^{±1}, z²]` is closed under products (`InSupportM.mul_left` with `CV.inSupportM_one_iff`). -/
theorem InSupportM.one_mul_one {f g : R} (hf : InSupportM 1 f) (hg : InSupportM 1 g) :
    InSupportM 1 (f * g) := by
  sorry

theorem inSupportM_one_prod {ι : Type} (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, InSupportM 1 (f i)) :
    InSupportM 1 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InSupportM.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact InSupportM.one_mul_one (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- "Knot support is nonnegative and even in `z`, so the `1−c` coefficient of this expression is
exactly `(a−a⁻¹)^{c−1} ∏ [z^0] P_{D_i}`: any positive `z` power in one factor raises that exponent"
(sm-3:1614-1617): `[z^0]` is multiplicative on `M_1` (`CV.zRow_zero_mul_of_inSupportM_one`), hence on
finite products. -/
theorem zRow_zero_prod_of_inSupportM_one {ι : Type} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, InSupportM 1 (f i)) : zRow 0 (∏ i ∈ s, f i) = ∏ i ∈ s, zRow 0 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact zRow_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      CV.zRow_zero_mul_of_inSupportM_one (hf a (Finset.mem_insert_self a s))
        (inSupportM_one_prod s f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-! ### G.2 Mixed crossings of a diagram (unit L2) -/

namespace Diagram

variable (D : Diagram)

/-- A mixed crossing: its two strands lie on different components ("mixed crossings between the
original components `i, j`", sm-3:1585). -/
def IsMixed (x : D.Γ.Crossing) : Prop := (D.overStrand x).1 ≠ (D.underStrand x).1

theorem componentCount_switch (x : D.Γ.Crossing) : (D.switch x).componentCount = D.componentCount := rfl

/-- "no self-crossing or intrinsic component restriction changes" (sm-3:1607-1608): a mixed switch
leaves every knot restriction unchanged (`switch_restrict_of_external` with `B = {i}`). -/
theorem knotRestrict_switch_of_isMixed {x : D.Γ.Crossing} (hx : D.IsMixed x) (i : Fin D.Γ.c) :
    (D.switch x).knotRestrict i = D.knotRestrict i := by
  sorry

/-- "the smoothed diagram has `c−1 ≥ 1` components" (`exists_smoothing_counts`; a mixed crossing is not
a record self crossing, `record_isSelfCrossing_iff`). -/
theorem exists_smoothing_of_isMixed {x : D.Γ.Crossing} (hx : D.IsMixed x) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧ D₀.componentCount + 1 = D.componentCount := by
  sorry

end Diagram

/-- "The switch from positive to negative changes one mixed sign from `+1` to `−1`, and hence changes
`Λ` by `−1`" (sm-3:1603-1604): `2Λ` drops by `2σ(x)` at a mixed switch (exactly one ordered pair
`(i, j)`, `i < j`, and one strand pair `(s, t)` of `mixedSignSum` sees the crossing;
`switch_sign_self`, `switch_sign_of_ne`; `(D.switch x).Γ = D.Γ` definitionally). -/
theorem twoLambda_switch_of_isMixed (D : Diagram) {x : D.Γ.Crossing} (hx : D.IsMixed x) :
    twoLambda (D.switch x) = twoLambda D - 2 * (D.sign x : ℤ) := by
  sorry

/-- "It follows that `a^{2Λ} h` is unchanged by that switch" (sm-3:1604-1606), `h = [z^{1−c}] P`. -/
theorem weight_switch_of_isMixed (D : Diagram) {x : D.Γ.Crossing} (hx : D.IsMixed x) :
    aPow (twoLambda (D.switch x)) * zRow (1 - (D.componentCount : ℤ)) (P (D.switch x)) =
      aPow (twoLambda D) * zRow (1 - (D.componentCount : ℤ)) (P D) := by
  obtain ⟨D₀, h₀, hc₀⟩ := D.exists_smoothing_of_isMixed hx
  have hz : zRow (1 - (D.componentCount : ℤ)) (R.z * P D₀) = 0 := by
    apply zRow_z_mul_eq_zero_of_inSupportM D.componentCount_pos
    have := P_support D₀
    rwa [show D₀.componentCount = D.componentCount - 1 by omega] at this
  rw [twoLambda_switch_of_isMixed D hx]
  by_cases hp : D.IsPositive x
  · have hs : ((D.sign x : SignType) : ℤ) = 1 := by
      rw [(D.isPositive_iff_sign_eq_one x).mp hp]; simp
    have e1 : zRow (1 - (D.componentCount : ℤ)) (P D) =
        aPow (-1) * (aPow (-1) * zRow (1 - (D.componentCount : ℤ)) (P (D.switch x))) := by
      rw [P_recursion_pos h₀ hp, zRow_add, mul_assoc R.aInv R.aInv, zRow_aInv_mul, zRow_aInv_mul,
        mul_assoc R.aInv R.z, zRow_aInv_mul, hz, mul_zero, add_zero]
    have e2 : aPow (twoLambda D - 2 * 1) = aPow (twoLambda D) * (aPow (-1) * aPow (-1)) := by
      rw [show twoLambda D - 2 * 1 = twoLambda D + (-1 + -1) by ring, aPow_add, aPow_add]
    rw [hs, e1, e2]; ring
  · have hs : ((D.sign x : SignType) : ℤ) = -1 := by
      rw [(D.sign_eq_neg_one_iff x).mpr hp]; simp
    have e1 : zRow (1 - (D.componentCount : ℤ)) (P D) =
        aPow 1 * (aPow 1 * zRow (1 - (D.componentCount : ℤ)) (P (D.switch x))) := by
      rw [P_recursion_neg h₀ hp, zRow_sub, mul_assoc R.a R.a, zRow_a_mul, zRow_a_mul,
        mul_assoc R.a R.z, zRow_a_mul, hz, mul_zero, sub_zero]
    have e2 : aPow (twoLambda D - 2 * (-1)) = aPow (twoLambda D) * (aPow 1 * aPow 1) := by
      rw [show twoLambda D - 2 * (-1) = twoLambda D + (1 + 1) by ring, aPow_add, aPow_add]
    rw [hs, e1, e2]; ring

/-! ### G.3 The block-ordered case (unit L3) -/

/-- "By Lemma mp:zero-link every pair of final components has linking number zero, hence final
`Λ = 0`" (sm-3:1609-1611): under `BlockOrdered D id` the larger-index component is over at every
mixed crossing, so `SM.zero_link.over_constant` kills every `twoLinking D i j`, `i < j`. -/
theorem twoLambda_eq_zero_of_blockOrdered (D : Diagram) (h : BlockOrdered D id) : twoLambda D = 0 := by
  sorry

/-- "Apply Theorem mp:stack with each component as one block" (sm-3:1611-1612): the singleton block
restriction is the knot restriction (`Finset.filter_eq'`; `Diagram.restrict` congruence along equal
finsets). -/
theorem blockRestrict_id_eq_knotRestrict (D : Diagram) (i : Fin D.Γ.c) :
    blockRestrict D id Function.surjective_id i = D.knotRestrict i := by
  sorry

/-- The value on a block-ordered diagram (sm-3:1611-1617): `[z^{1−c}] P_D = (a−a⁻¹)^{c−1} ∏ [z^0] P_{D_i}`. -/
theorem lowest_of_blockOrdered (D : Diagram) (h : BlockOrdered D id) :
    zRow (1 - (D.componentCount : ℤ)) (P D) =
      (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) * ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i)) := by
  have hst : P D = R.delta ^ (D.componentCount - 1) * ∏ i : Fin D.Γ.c, P (D.knotRestrict i) := by
    have := SM.stack.stack D D.Γ.c id Function.surjective_id h
    simp only [blockRestrict_id_eq_knotRestrict] at this
    exact this
  have hsupp : ∀ i ∈ (Finset.univ : Finset (Fin D.Γ.c)), InSupportM 1 (P (D.knotRestrict i)) := by
    intro i _
    have := P_support (D.knotRestrict i)
    rwa [Diagram.knotRestrict_componentCount] at this
  have hc : (1 - (D.componentCount : ℤ)) = 0 - ((D.componentCount - 1 : ℕ) : ℤ) := by
    have := D.componentCount_pos; omega
  rw [hst, hc, zRow_delta_pow_mul, zRow_zero_prod_of_inSupportM_one _ _ hsupp]

/-! ### G.4 Reduction to the block-ordered case by mixed switches (unit L4) -/

namespace Diagram

variable (D : Diagram)

/-- The mixed crossings at which the smaller-index component is NOT under: "Switch exactly the mixed
crossings necessary to put each smaller-index component UNDER every larger-index component"
(sm-3:1607-1608). -/
noncomputable def badMixedCount : ℕ :=
  (Finset.univ.filter (fun x : D.Γ.Crossing =>
    ∃ s ∈ x.val, ∃ t ∈ x.val, s.1 < t.1 ∧ D.underStrand x ≠ s)).card

theorem blockOrdered_id_of_badMixedCount_eq_zero (h : D.badMixedCount = 0) : BlockOrdered D id := by
  sorry

/-- A badly ordered mixed crossing exists and switching it lowers the count by one (`switch_underStrand_self`,
`switch_underStrand_of_ne`). -/
theorem exists_badMixed (h : D.badMixedCount ≠ 0) :
    ∃ x : D.Γ.Crossing, D.IsMixed x ∧ (D.switch x).badMixedCount + 1 = D.badMixedCount := by
  sorry

end Diagram

/-- eq. mp:lowest-value by induction on `badMixedCount` (sm-3:1597-1620): the weight `a^{2Λ}[z^{1−c}]P`
is preserved by each mixed switch and the knot restrictions do not change; at `badMixedCount = 0` the
diagram is block ordered. -/
theorem lowest_value_aux : ∀ (n : ℕ) (D : Diagram), D.badMixedCount = n →
    zRow (1 - (D.componentCount : ℤ)) (P D) =
      aPow (-(twoLambda D)) * (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) *
        ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hD
  by_cases h0 : D.badMixedCount = 0
  · have hbo := D.blockOrdered_id_of_badMixedCount_eq_zero h0
    rw [lowest_of_blockOrdered D hbo, twoLambda_eq_zero_of_blockOrdered D hbo, neg_zero, aPow_zero,
      one_mul]
  · obtain ⟨x, hx, hcount⟩ := D.exists_badMixed h0
    have hK : ∀ i, (D.switch x).knotRestrict i = D.knotRestrict i :=
      D.knotRestrict_switch_of_isMixed hx
    have ih' : zRow (1 - (D.componentCount : ℤ)) (P (D.switch x)) =
        aPow (-(twoLambda (D.switch x))) * (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) *
          ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i)) := by
      have := ih (D.switch x).badMixedCount (by omega) (D.switch x) rfl
      simp only [hK] at this
      exact this
    have hw := weight_switch_of_isMixed D hx
    calc zRow (1 - (D.componentCount : ℤ)) (P D)
        = aPow (-(twoLambda D)) * (aPow (twoLambda D) * zRow (1 - (D.componentCount : ℤ)) (P D)) := by
          rw [← mul_assoc, aPow_neg_mul_aPow, one_mul]
      _ = aPow (-(twoLambda D)) *
            (aPow (twoLambda (D.switch x)) * zRow (1 - (D.componentCount : ℤ)) (P (D.switch x))) := by
          rw [hw]
      _ = aPow (-(twoLambda D)) * (aPow 1 - aPow (-1)) ^ (D.componentCount - 1) *
            ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i)) := by
          rw [ih', ← mul_assoc (aPow (twoLambda (D.switch x))),
            ← mul_assoc (aPow (twoLambda (D.switch x))), ← aPow_add, add_neg_cancel, aPow_zero,
            one_mul]
          ring

/-! ### G.5 The two-component row (unit L5) -/

/-- `ℓ_ij = ℓ_ji`: each mixed crossing is one ordered strand pair `(s, t)`, and `{s, t} = {t, s}`. -/
theorem mixedSignSum_comm (D : Diagram) (i j : Fin D.Γ.c) : mixedSignSum D i j = mixedSignSum D j i := by
  sorry

/-- For `c = 2` the total `2Λ` is the single mixed sum `2ℓ_ij` (`Finset.univ = {i, j}`, `mixedSignSum_comm`). -/
theorem twoLambda_eq_twoLinking_of_two (D : Diagram) (i j : Fin D.Γ.c) (hc : D.componentCount = 2)
    (hij : i ≠ j) : twoLambda D = twoLinking D i j := by
  sorry

/-- A product over the two components. -/
theorem prod_univ_eq_of_componentCount_two {M : Type} [CommMonoid M] (D : Diagram) (i j : Fin D.Γ.c)
    (hc : D.componentCount = 2) (hij : i ≠ j) (f : Fin D.Γ.c → M) : ∏ k, f k = f i * f j := by
  sorry

theorem two_component_row_of_lowest (D : Diagram) (i j : Fin D.Γ.c) (hc : D.componentCount = 2)
    (hij : i ≠ j) :
    zRow (-1) (P D) =
      aPow (-(twoLinking D i j)) * (aPow 1 - aPow (-1)) *
        (zRow 0 (P (D.knotRestrict i)) * zRow 0 (P (D.knotRestrict j))) := by
  have h := lowest_value_aux _ D rfl
  rw [twoLambda_eq_twoLinking_of_two D i j hc hij, prod_univ_eq_of_componentCount_two D i j hc hij,
    hc] at h
  rw [show (1 : ℤ) - ((2 : ℕ) : ℤ) = -1 by norm_num, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  exact h

/-! ### G.6 Record level: mark-compatible based orders, the join of based orders, switch and smoothing
of a join (units J1-J4) -/

namespace Record

variable {ρ : Record}

/-- "In EACH factor put the marked component first and base it at its marked gap" (sm-3:1440-1441):
a based order compatible with a mark. -/
structure RBasing.MarkCompatible (B : RBasing ρ) (μ : ρ.Mark) : Prop where
  /-- the marked circle has the least rank -/
  rank_lt : ∀ c, c ≠ μ.comp → B.rank μ.comp < B.rank c
  /-- the base occurrence of the marked circle is the one just after the gap -/
  base_gap : ∀ g, μ.gap = some g → B.base g = ρ.succ g

/-- Unit J1: every mark admits a compatible based order ("New orders and basepoints can be chosen",
sm-3:1099; rank `μ.comp ↦ 0`, others `equivFin + 1`; base `succ g` on the marked circle). -/
theorem exists_markCompatible_rbasing (μ : ρ.Mark) : ∃ B : RBasing ρ, B.MarkCompatible μ := by
  sorry

theorem Mark.map_refl (μ : ρ.Mark) : μ.map (RecordIso.refl ρ) = μ := by
  rcases μ with ⟨c, g, _, _⟩
  cases g <;> rfl

/-- The mark of a switched record: the same circle and gap ("Switching it gives `A^sw` with the same
component number, same marked interval", sm-3:1454-1455). -/
def Mark.switchMark (μ : ρ.Mark) (x : ρ.M) : (ρ.switch x).Mark :=
  ⟨μ.comp, μ.gap, μ.gap_comp, μ.gap_none⟩

@[simp] theorem Mark.switchMark_comp (μ : ρ.Mark) (x : ρ.M) : (μ.switchMark x).comp = μ.comp := rfl
@[simp] theorem Mark.switchMark_gap (μ : ρ.Mark) (x : ρ.M) : (μ.switchMark x).gap = μ.gap := rfl

variable {ρ₁ ρ₂ : Record}

/-- Unit J2a: the marked join is symmetric ("If the selected bad crossing is in `B`, the identical
argument with the two factor names interchanged applies", sm-3:1487-1489): `Sum.swap` on occurrences,
`comps₁ ⊕ Unmarked₂ ≃ comps₂ ⊕ Unmarked₁` sending the joined circle to `μ₂.comp`. -/
theorem exists_joinRecord_comm (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) :
    ∃ ι : RecordIso (joinRecord μ₁ μ₂) (joinRecord μ₂ μ₁), ∀ v, ι.Φ v = Sum.swap v := by
  sorry

/-- Unit J3: the base case (sm-3:1443-1451): "traverse the joined component starting just before the
`A` portion, then its `B` portion. Traverse the remaining `A` components in their chosen order, then
the remaining `B` components … the relative order of all visits is the same as in its factor
traversal … There are no crossings with one visit in each factor. Thus the entire joined diagram is
UNDER-first."  Rank: `inl c ↦ B₁.rank c`, `inr c ↦ B₂.rank c + (sup B₁.rank + 1)`; base: `inl (B₁.base a)`
on `A`'s circles and on the joined circle, `inr (B₂.base b)` on `B`'s unmarked circles; positions
`pos (inl a) = B₁.pos a`, `pos (inr b) = |marked circle of A| + B₂.pos b` on the joined circle. -/
theorem exists_rUnderFirst_joinRecord (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)
    (h₁ : B₁.RUnderFirst) (h₂ : B₂.RUnderFirst) (hμ₁ : B₁.MarkCompatible μ₁)
    (hμ₂ : B₂.MarkCompatible μ₂) :
    ∃ B : RBasing (joinRecord μ₁ μ₂), B.RUnderFirst := by
  sorry

/-- Unit J2b: "In `J(A,B)` it is precisely the corresponding crossing switch" (sm-3:1455-1456): the
identity on occurrences and circles; bits and signs by cases `inl`/`inr`. -/
theorem joinRecord_switch_inl (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (a : ρ₁.M) :
    Nonempty (RecordIso ((joinRecord μ₁ μ₂).switch (Sum.inl a)) (joinRecord (μ₁.switchMark a) μ₂)) := by
  sorry

/-- Unit J4 (the substantial one): "In the joint diagram, smoothing has exactly the record of
`J(A⁰,B)`: both operations are recombinations at disjoint incoming/outgoing ends. All other successor
relations and all other crossings are unchanged" (sm-3:1458-1462), with the four cases self/mixed ×
marked/unmarked (1462-1472) absorbed in the choice of the new mark `μ₀` on `ρ₁.smooth a` (the gap
re-chosen as the retained occurrence now preceding the interval, `none` when the interval lands on an
emptied circle).  Occurrences: `{v : M₁ ⊕ M₂ // v ∉ {inl a, inl τa}} ≃ {w : M₁ // w ∉ {a, τa}} ⊕ M₂`;
circles through `RecordIso.ofOcc` (PLAN_A.md §4, unit J4a). -/
theorem exists_joinRecord_smooth_inl (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (a : ρ₁.M) :
    ∃ μ₀ : (ρ₁.smooth a).Mark,
      Nonempty (RecordIso ((joinRecord μ₁ μ₂).smooth (Sum.inl a)) (joinRecord μ₀ μ₂)) := by
  sorry

end Record

/-! ### G.7 Diagram level: the base case, the two steps, the two inductions of mp:join (units J5-J6) -/

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
    refine ihsw ((μA.switchMark a).map ιA.symm) rfl ?_ (J.switch v.1) ⟨?_⟩
    · exact optionMap_eq_self _ (fun _ => rfl) _
    · refine (J.switchRecordIso v.1 v rfl).trans ?_
      refine (ι.switch v).trans ?_
      rw [hΦv]
      refine κ.trans ?_
      have := RecordIso.joinRecord ιA.symm (RecordIso.refl Bd.record) (μA.switchMark a) μB
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

/-- The step at a bad occurrence of the RIGHT factor: the left step after `exists_joinRecord_comm`. -/
theorem P_join_step_right (A Bd : Diagram) (μA : A.record.Mark) (μB : Bd.record.Mark) (b : Bd.Γ.Visit)
    (J : Diagram) (ι : RecordIso J.record (Record.joinRecord μA μB))
    (ihsw : ∀ μ' : (Bd.switch b.1).record.Mark, μ'.comp = μB.comp → μ'.gap = μB.gap →
      ∀ J' : Diagram, Nonempty (RecordIso J'.record (Record.joinRecord μA μ')) →
        P J' = P A * P (Bd.switch b.1))
    (ihsm : ∀ B₀ : Diagram, IsOrientedSmoothing Bd b.1 B₀ → ∀ (μ₀ : B₀.record.Mark) (J' : Diagram),
      Nonempty (RecordIso J'.record (Record.joinRecord μA μ₀)) → P J' = P A * P B₀) :
    P J = P A * P Bd := by
  obtain ⟨κ, -⟩ := Record.exists_joinRecord_comm μA μB
  rw [mul_comm]
  refine P_join_step_left Bd A μB μA b J (ι.trans κ) ?_ ?_
  · intro μ' hc hg J' ⟨ι'⟩
    obtain ⟨κ', -⟩ := Record.exists_joinRecord_comm μ' μA
    rw [mul_comm]
    exact ihsw μ' hc hg J' ⟨ι'.trans κ'⟩
  · intro B₀ h₀ μ₀ J' ⟨ι'⟩
    obtain ⟨κ', -⟩ := Record.exists_joinRecord_comm μ₀ μA
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

/-! ### G.8 lem:homflyrows, the split union (unit H1) -/

/-- "Theorem mp:stack, with two one-component blocks and no mixed crossings, gives
`P_{K⊔J} = δ P_K P_J`" (sm-4:245-247): `SM.stack.split_union` with `blk c := if c ∈ B then 0 else 1`,
the block restrictions are `D.restrict B`, `D.restrict Bᶜ` (`Finset.filter` congruence), and
`presentations` transports along the two record isomorphisms. -/
theorem P_split_union (K J D : Diagram) (h : IsSplitUnion K J D) : P D = R.delta * (P K * P J) := by
  sorry

/-! ### G.9 mp:blocks: record bookkeeping (units B1-B3) and the realization chain (units B4-B7,
ANALYSED in PLAN_A.md §5 — the geometric lemmas are NOT to be proved in this panel) -/

/-- Unit B1: "the writhe is the sum of the writhes of `C_H`": the occurrences of `ρ` are partitioned
by the block of their crossing (`Finset.sum_fiberwise` along `connectedComponentMk ∘ crossingOf`),
and each block's half-sum is its writhe (`two_mul_writhe`). -/
theorem Record.writhe_eq_sum_restrictCrossings (ρ : Record) :
    ρ.writhe = ∑ H : ρ.interlacementGraph.ConnectedComponent, (ρ.restrictCrossings H.supp).writhe := by
  sorry

/-- Unit B2: the crossings of a clean marked join are those of the two factors, with their signs
(`RecordIso.crossingOf_eq`, `joinRecord_pair_inl/inr`, `joinRecord_sgn_inl/inr`, `record_sgn`). -/
theorem IsCleanMarkedJoin.crossingEquiv {A B : MarkedDiagram} {J : Diagram} (h : IsCleanMarkedJoin A B J) :
    ∃ φ : A.D.Γ.Crossing ⊕ B.D.Γ.Crossing ≃ J.Γ.Crossing,
      (∀ x, J.sign (φ (Sum.inl x)) = A.D.sign x) ∧ (∀ y, J.sign (φ (Sum.inr y)) = B.D.sign y) := by
  sorry

/-- Unit B3: "Every old crossing is present once, with its old sign" (sm-3:1681-1682), along a forest
(`JoinForest` induction; leaf: `Set.uniqueSingleton`; node: `Equiv.Set.union` on the disjoint index
sets, `Equiv.sigmaSumDistrib`, `IsCleanMarkedJoin.crossingEquiv`). -/
theorem joinForest_sign {ι : Type} (C : ι → Diagram) :
    ∀ (S : Set ι) (J : Diagram), JoinForest C S J →
      ∃ φ : (Σ i : S, (C i).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2 := by
  sorry

/-- "Repeated use of Theorem mp:join gives the product value for the constructed diagram"
(sm-3:1675-1676). -/
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

/-- Unit B4 (record, ~40 lines): restricting to every crossing changes nothing (cf. `restrictUnivIso`). -/
theorem restrictCrossings_univ_iso (ρ : Record) :
    Nonempty (RecordIso (ρ.restrictCrossings Set.univ) ρ) := by
  sorry

/-- Unit B5 (GEOMETRIC, analysed only): every record mark of an actual diagram is realised by a printed
marked interval — a short crossing-free sub-arc of the gap after `μ.gap` (or anywhere on a crossing-free
marked circle), inside a small clean disc.  Needed to feed `JoinForest.join` (whose nodes are
`MarkedDiagram`s) with the marks chosen by the combinatorics. -/
theorem exists_markedInterval (D : Diagram) (μ : D.record.Mark) :
    ∃ I : D.Γ.Arc, IsMarkedInterval D I ∧ I.i = μ.comp ∧ ∀ v, μ.gap = some v ↔ D.IsGapOf I v := by
  sorry

/-- Unit B6 (GEOMETRIC, analysed only — design decision D9's tracked sub-obligation, sm-3:1387-1425):
"These actual clean joins exist": for two marked diagrams some actual diagram has the join record. -/
theorem exists_cleanMarkedJoin (A B : MarkedDiagram) : ∃ J : Diagram, IsCleanMarkedJoin A B J := by
  sorry

/-- Unit B7 (COMBINATORIAL, record level, sm-3:1637-1663): among ≥ 2 blocks of a one-circle record one
block `T` is cyclically consecutive within their union (the block of minimal span from a base gap), so
the union restriction is the join of the restriction to the other blocks (mark at the gap holding `T`)
and the restriction to `T` (mark at its last occurrence).  Sub-lemmas in PLAN_A.md §5. -/
theorem Record.exists_peel (ρ : Record) (h1 : ρ.componentCount = 1)
    (S : Finset ρ.interlacementGraph.ConnectedComponent) (hS : 2 ≤ S.card) :
    ∃ T ∈ S, ∃ (μU : (ρ.restrictCrossings (⋃ H ∈ S.erase T, H.supp)).Mark)
      (μT : (ρ.restrictCrossings T.supp).Mark),
      Nonempty (RecordIso (ρ.restrictCrossings (⋃ H ∈ S, H.supp)) (Record.joinRecord μU μT)) := by
  sorry

/-- The printed nested forest (sm-3:1646-1676), by strong induction on the number of blocks used. -/
theorem realizes_aux (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram)
    (hC : BlockSupply ρ C) :
    ∀ (n : ℕ) (S : Finset ρ.interlacementGraph.ConnectedComponent), S.card = n → S.Nonempty →
      ∃ J : Diagram, JoinForest C (↑S : Set _) J ∧
        Nonempty (RecordIso J.record (ρ.restrictCrossings (⋃ H ∈ S, H.supp))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hS
  by_cases h2 : 2 ≤ S.card
  · obtain ⟨T, hT, μU, μT, ⟨κ⟩⟩ := Record.exists_peel ρ hC.one_circle S h2
    have hcard : (S.erase T).card + 1 = S.card := Finset.card_erase_add_one hT
    have hU : (S.erase T).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨JU, hJU, ⟨ιU⟩⟩ := ih (S.erase T).card (by omega) (S.erase T) rfl hU
    obtain ⟨ιT⟩ := hC.supplied T
    obtain ⟨IU, hIU, hIUc, hIUg⟩ := exists_markedInterval JU (μU.map ιU.symm)
    obtain ⟨IT, hIT, hITc, hITg⟩ := exists_markedInterval (C T) (μT.map ιT.symm)
    let A : MarkedDiagram := ⟨JU, IU, hIU, μU.map ιU.symm, hIUc, hIUg⟩
    let B : MarkedDiagram := ⟨C T, IT, hIT, μT.map ιT.symm, hITc, hITg⟩
    obtain ⟨J, ⟨ιJ⟩⟩ := exists_cleanMarkedJoin A B
    refine ⟨J, ?_, ⟨?_⟩⟩
    · have e : (↑S : Set ρ.interlacementGraph.ConnectedComponent) = ↑(S.erase T) ∪ {T} := by
        rw [Finset.coe_erase,
          Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr hT))]
      rw [e]
      refine JoinForest.join A B hJU (JoinForest.leaf T) ?_ ⟨ιJ⟩
      rw [Finset.coe_erase]
      exact Set.disjoint_sdiff_left
    · exact ιJ.trans ((RecordIso.joinRecord ιU.symm ιT.symm μU μT).symm.trans κ.symm)
  · obtain ⟨T, hT⟩ := hS
    have hcard : S.card = 1 := by
      have := Finset.card_pos.mpr ⟨T, hT⟩
      omega
    obtain ⟨T', hST'⟩ := Finset.card_eq_one.mp hcard
    have hTT' : T = T' := by
      rw [hST'] at hT
      exact Finset.mem_singleton.mp hT
    subst hTT'
    refine ⟨C T, ?_, ?_⟩
    · rw [hST', Finset.coe_singleton]
      exact JoinForest.leaf T
    · rw [hST']
      simpa using hC.supplied T

/-- "Thus the final oriented named record is literally the full given record" (sm-3:1671-1673). -/
theorem realizes_of_chain (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram)
    (hC : BlockSupply ρ C) :
    ∃ J : Diagram, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record ρ) := by
  have hne : (Finset.univ : Finset ρ.interlacementGraph.ConnectedComponent).Nonempty := by
    obtain ⟨v⟩ := hC.nonempty
    exact ⟨ρ.interlacementGraph.connectedComponentMk (ρ.crossingOf v), Finset.mem_univ _⟩
  obtain ⟨J, hJ, ⟨ι⟩⟩ := realizes_aux ρ C hC _ Finset.univ rfl hne
  rw [Finset.coe_univ] at hJ
  refine ⟨J, hJ, ⟨ι.trans ?_⟩⟩
  have huniv : (⋃ H ∈ (Finset.univ : Finset ρ.interlacementGraph.ConnectedComponent), H.supp) =
      (Set.univ : Set ρ.Crossing) := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_univ, iff_true, exists_prop, true_and]
    exact ⟨_, (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩
  rw [huniv]
  exact (restrictCrossings_univ_iso ρ).some

end Link

/-! ## F. The four bundles (byte-identical to work/drafts/MarkedProducts_statement.lean §F; the row
theorems are proved from section G) -/

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

/-- mp:join. -/
theorem join : JoinData where
  join_value := fun A B J h => Link.join_value_of_iso A B J h
  multi_component_factors := fun A B J _ h => Link.join_value_of_iso A B J h
  crossing_free_marked_component := fun A B J _ h => Link.join_value_of_iso A B J h

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

/-- mp:lowest. -/
theorem lowest : LowestData where
  lowest_value := fun D => Link.lowest_value_aux _ D rfl
  two_component_row := fun D i j hc hij => Link.two_component_row_of_lowest D i j hc hij

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

/-- mp:blocks.  `realizes` is proved from the chain of §G.9 whose two geometric lemmas
(`exists_markedInterval`, `exists_cleanMarkedJoin`) are analysed, not proved, in this panel
(PLAN_A.md §5); `product` consumes `realizes` as the printed proof does (sm-3:1675-1677). -/
theorem blocks : BlocksData where
  realizes := fun ρ C hC => Link.realizes_of_chain ρ C hC
  product := fun ρ C hC D ⟨ιD⟩ => by
    obtain ⟨J, hJ, ⟨ιJ⟩⟩ := Link.realizes_of_chain ρ C hC
    rw [presentations D J ⟨ιD.trans ιJ.symm⟩, Link.joinForest_P C Set.univ J hJ]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext H
    simp
  sign_preserved := fun ρ C hC J hJ => by
    obtain ⟨φ, hφ⟩ := Link.joinForest_sign C Set.univ J hJ
    exact ⟨(Link.sigmaUnivEquiv fun H => (C H).Γ.Crossing).symm.trans φ, fun q => hφ _⟩
  writhe_additive := fun ρ C hC D ⟨ιD⟩ => by
    rw [← D.record_writhe, ιD.writhe_eq, Record.writhe_eq_sum_restrictCrossings]
    refine Finset.sum_congr rfl fun H _ => ?_
    obtain ⟨ιH⟩ := hC.supplied H
    rw [← (C H).record_writhe, ιH.writhe_eq]

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

/-- lem:homflyrows. -/
theorem homflyrows : HomflyRowsData where
  connected_sum := fun K J _ _ K' J' D hK hJ hD => by
    have h := Link.join_value_of_iso K' J' D hD
    rw [P_eq_homfly, P_eq_homfly, P_eq_homfly, ← homfly_descent hK, ← homfly_descent hJ] at h
    exact h
  split_union := fun K J _ _ K' J' D hK hJ hD => by
    have h := Link.P_split_union K' J' D hD
    rw [P_eq_homfly, P_eq_homfly, P_eq_homfly, ← homfly_descent hK, ← homfly_descent hJ] at h
    exact h
  two_component_row := fun D i j hc hij => by
    have h := Link.two_component_row_of_lowest D i j hc hij
    rw [P_eq_homfly, P_eq_homfly, P_eq_homfly] at h
    rw [h, CV.zRow_zero_mul_of_inSupportM_one
      (CV.ax_homfly.knot_parity _ (Diagram.knotRestrict_componentCount D i))
      (CV.ax_homfly.knot_parity _ (Diagram.knotRestrict_componentCount D j))]
    ring

end SM
