import SM.CBProducts
import SM.CX1
import SM.EmbeddedRotation
import SM.UniformRotation
import SM.Reversal
import SM.SingleCrossing
import SM.Children
import SM.DeletionHalvesDefinition
import SM.NamedWallsDefinition
import SM.NamedWallSides
import SM.SoftGenericLemma
import SM.SoftAmplitudeSectors
import SM.HypR
import SM.LinkPositiveLift
import SM.CChamber
import SM.GermSides
import SM.VertexSides

/-! # Statements_FINAL — the corner chain after thm:floor: rows 103 cb:singleton, 105 lem:corner-values,
110 thm:C-S7, 112 thm:C-soft (judge's decision, 2026-09-15)

Companion of work/drafts/corner/PLAN_FINAL.md (winner: DESIGN_B's skeleton, with DESIGN_A's grafts).
Check: `cd work/lean && lake env lean ../drafts/corner/Statements_FINAL.lean`.

Every `sorry` is either (a) a LEAF of the unit decomposition of PLAN_FINAL.md §4 (frozen statement, to be
proved in a byte-identical skeleton copy), or (b) one of the four ROW THEOREMS of §6, which become
one-liners `… (thm_floor)` once row 100 (`SM.thm_floor : FloorTheoremData`, floor lane) is accepted.
Everything else is PROVED from accepted declarations: the four row-level assemblies
`cb_singleton_of_floor`, `corner_values_of_singleton`, `thm_C_S7_of`, `thm_C_soft_of_cornerValues`,
row 105 clause (i) (`corner_values_i`, UNCONDITIONAL — grafted from Sketch_A), the floor-interface bridge
`carrierUniformOrOneDissent_of_signed`, and the companions.

Sources (frame SM15): reference/SM/sm-3-statesum.tex 4697-4702 (103; proof 4703-4759), 4801-4809 (105;
proof 4810-4820); reference/SM/sm-4-knotlaws.tex 267-274 (110; proof 275-908), 984-991 (112; proof
992-1147).  Dependencies (tools/claims.py): 103 ← thm:floor; 105 ← cb:singleton; 110 ← cb:singleton,
thm:floor; 112 ← lem:corner-values.  Fixed target names (work/lean/axiom-policy.json): `SM.thm_C_S7`,
`SM.thm_C_soft`.  Proposed: `SM.cb_singleton : CbSingletonData`, `SM.corner_values : CornerValuesData`.

§0 is a VERBATIM copy of the floor lane's interface (work/drafts/floor/Statements_FINAL.lean §7:
`AllLeftOrOneRight`, `CarrierUniformOrOneDissent` in the literal reversal form, `FloorTheoremData` with the
ℤ ∧ ℝ display) — NOT the Gap2Statements §8 shape both designs assumed; to be deleted when the floor lane's
module lands (the names then resolve to the accepted ones).  Only `a_floor`'s first conjunct is consumed
(rows 103, 110); `z_parity` is never used (FR-CC-10). -/

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## §0 The row-100 interface (VERBATIM from work/drafts/floor/Statements_FINAL.lean §7) and the bridge
from the signed form the proof routes produce. -/

section Floor

variable {n : ℕ} [NeZero n]

/-- "either all turns are left, or exactly one turn is right" on the corner polygon `Q` (turns =
def:chirotope's `turn ∈ {−1, 0, +1}`, left = `1`; FR-FL-F2: every corner of the corner polygon) -/
def AllLeftOrOneRight {m : ℕ} (Q : LabelledTuple m) : Prop :=
  (∀ j, turn Q j = 1) ∨ (∃ j₀, turn Q j₀ = -1 ∧ ∀ j, j ≠ j₀ → turn Q j = 1)

/-- "after possibly reversing its orientation either all turns are left, or exactly one turn is
right": for the corner polygon of the subpolygon `Q` (accepted `ccpCornerPolygon`) or its reversal
(accepted `reversal`; FR-FL-F1, literal reversal form) -/
def CarrierUniformOrOneDissent (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Prop :=
  AllLeftOrOneRight (ccpCornerPolygon hn hP S q) ∨
  AllLeftOrOneRight (reversal (ccpCornerPolygon hn hP S q))

/-- thm:floor: "Let Q be a subpolygon of a decomposition of a generic polygon, and suppose that
after possibly reversing its orientation either all turns are left, or exactly one turn is right.
Then mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q, H⁺_Q ∈ ℤ[a^{±1}, z²], so mindeg_z H⁺_Q ≥ 0."
`H⁺_Q = cornerHomfly`, `m_Q = carrierCrossingCount`, `r_Q = carrierRotation`, `d_Q = cornerSlot`
(def:C, accepted; `cornerSlot_cast` is the printed equality `d_Q = 1 − m_Q − |r_Q|`);
`ℤ[a^{±1}, z²] = M_1` is the accepted `InSupportM 1` (lp:support). -/
structure FloorTheoremData : Prop where
  /-- "mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q" (in `ℤ` with `d_Q = cornerSlot`, and as printed with the
  real `r_Q`) -/
  a_floor : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniformOrOneDissent hn hP S q →
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) ∧
    1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q| ≤
      (mindegAZ (cornerHomfly hn hP S q hS) : ℝ)
  /-- "H⁺_Q ∈ ℤ[a^{±1}, z²], so mindeg_z H⁺_Q ≥ 0" (no hypothesis on the turns, FR-FL-F3) -/
  z_parity : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    InSupportM 1 (cornerHomfly hn hP S q hS) ∧ 0 ≤ mindegZZ (cornerHomfly hn hP S q hS)

/-! ### The bridge (judge's addition, PROVED).  The proof routes of rows 103 and 110 produce turn
patterns in the SIGNED form "uniform of sign `τ`, or one dissent `−τ` among turns `τ`" (this is how
lem:uniformrot `uniform_rotation` is stated); the floor lane's hypothesis is the literal reversal form.
`turn_reversal` (SM/Reversal.lean:61) converts. -/

/-- "uniform with sign `τ`, or exactly one dissent" — the output shape of the leaves. -/
def SignedUniformOrOneDissent {m : ℕ} (Q : LabelledTuple m) : Prop :=
  ∃ τ : SignType, τ ≠ 0 ∧
    ((∀ j, turn Q j = τ) ∨ (∃ j₀, turn Q j₀ = -τ ∧ ∀ j, j ≠ j₀ → turn Q j = τ))

theorem allLeftOrOneRight_of_signed {m : ℕ} (Q : LabelledTuple m)
    (h : SignedUniformOrOneDissent Q) : AllLeftOrOneRight Q ∨ AllLeftOrOneRight (reversal Q) := by
  obtain ⟨τ, hτ, h⟩ := h
  rcases SignType.trichotomy τ with h1 | h1 | h1
  · -- `τ = −1`: after reversal every turn is left (`turn (reversal Q) i = −turn Q (2 − i)`)
    subst h1
    right
    rcases h with hall | ⟨j₀, hj₀, hoth⟩
    · left
      intro i
      rw [turn_reversal, hall]; decide
    · right
      refine ⟨2 - j₀, ?_, ?_⟩
      · rw [turn_reversal]
        have : (2 : ZMod m) - (2 - j₀) = j₀ := by ring
        rw [this, hj₀]; decide
      · intro i hi
        rw [turn_reversal, hoth]
        · decide
        · intro h2; apply hi; rw [← h2]; ring
  · exact absurd h1 hτ
  · subst h1
    left
    rcases h with hall | ⟨j₀, hj₀, hoth⟩
    · exact Or.inl hall
    · exact Or.inr ⟨j₀, hj₀, hoth⟩

/-- The floor's hypothesis from the signed turn pattern of a carrier. -/
theorem carrierUniformOrOneDissent_of_signed (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    (h : SignedUniformOrOneDissent (ccpCornerPolygon hn hP S q)) :
    CarrierUniformOrOneDissent hn hP S q :=
  allLeftOrOneRight_of_signed _ h

/-- A uniform carrier (def:uniform) has the signed pattern. -/
theorem signedUniformOrOneDissent_of_uniform (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (h : CarrierUniform hn hP S q) :
    SignedUniformOrOneDissent (ccpCornerPolygon hn hP S q) := by
  obtain ⟨τ, hτ, hall⟩ := h
  exact ⟨τ, hτ, Or.inl hall⟩

/-- The one conjunct of `a_floor` this lane consumes, taken at a signed turn pattern. -/
theorem FloorTheoremData.slot_le_of_signed (hF : FloorTheoremData) (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (h : SignedUniformOrOneDissent (ccpCornerPolygon hn hP S q)) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) :=
  (hF.a_floor hn P hP S hS q (carrierUniformOrOneDissent_of_signed hn hP S q h)).1

end Floor

/-! ## §1 Shared algebra (PROVED): the corner polynomial is nonzero; a product whose two factors satisfy
`a`-floors has zero coefficients below the summed floor. -/

section Algebra

variable {n : ℕ} [NeZero n]

/-- `H⁺_Q ≠ 0` (lp:core "P_D ≠ 0", identified with `homfly` by `P_eq_homfly`). -/
theorem cornerHomfly_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) :
    cornerHomfly hn hP S q hS ≠ 0 := by
  unfold cornerHomfly
  rw [← P_eq_homfly]
  exact lp_core.ne_zero _

/-- The degree argument shared by cb:singleton (eq. cb:singleton-gap) and the noninterlacing branch of
thm:C-S7 (eq. s7c:noninterlacing-extraction): if `k₁ ≤ mindeg_a f`, `k₂ ≤ mindeg_a g` with `f, g ≠ 0`,
every coefficient of `f g` at an `a`-degree `< k₁ + k₂` vanishes (`mindegAZ_mul`, LinkLaurentRing.lean:757).
FR-CC-3: this replaces the printed `[z⁰]`-row bookkeeping; no `z`-parity is consumed. -/
theorem coeffAt_mul_eq_zero_of_lt_floor {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) {k₁ k₂ d k : ℤ}
    (h₁ : k₁ ≤ mindegAZ f) (h₂ : k₂ ≤ mindegAZ g) (hd : d < k₁ + k₂) :
    coeffAt d k (f * g) = 0 := by
  by_contra hne
  have hle := (mindegAZ_spec (mul_ne_zero hf hg)).2 d k hne
  rw [mindegAZ_mul hf hg] at hle
  omega

end Algebra

/-! ## §2 Row 103 cb:singleton (sm-3:4697-4702; proof 4703-4759) -/

section Singleton

variable {n : ℕ} [NeZero n]

/-- **cb:singleton as printed**, one field: "Let `A` be a uniform carrier of `S`, and suppose one of its
self-crossing labels `c` interlaces no other self-crossing of `A`. Then `c(A) = 0`."
Binder as def:C / cb:blocks (`hn : 3 ≤ n`, `hP : Generic P`, `hS : IsDecomposition hn hP S`; FR-CC-2);
"self-crossing labels of `A`" = `carrierCrossings hn hP S A` (def:smoothing; lem:carriers (iii));
"interlaces no other self-crossing" = `∀ c' ∈ carrierCrossings … A, c' ≠ c → ¬ Interlaces hn hP c c'`
(def:interlace, in `G_P`; FR-CC-1); "uniform" = `CarrierUniform` (def:uniform);
`c(A) = cornerCoefficient hn hP S A hS` (def:C, the total coefficient). -/
structure CbSingletonData : Prop where
  isolated_zero : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (A : Component hn hP S),
    CarrierUniform hn hP S A →
    ∀ c ∈ carrierCrossings hn hP S A,
      (∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') →
      cornerCoefficient hn hP S A hS = 0

/-! ### Leaves of row 103 (frozen; units U103-A … U103-E of PLAN_FINAL.md §4). Prefix `sg_`. -/

/-- U103-A. An isolated self-crossing of `A` is undominated by `S` and interlaces NO undominated label (an
undominated interlacer would lie on `A` by lem:carriers (iv), hence be a self-crossing of `A`);
consequently `insert c S` is a decomposition (accepted `greedy_independent`, CBProducts.lean:1911) with
`U(insert c S) = U(S) ∖ {c}` (accepted `greedy_step`, :1917). -/
theorem sg_isolated_undominated (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hiso : ∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') :
    c ∈ supportUnselected hn hP S ∧
      (∀ x ∈ supportUnselected hn hP S, Interlaces hn hP x c → x ∈ carrierCrossings hn hP S A) ∧
      supportUnselected hn hP (insert c S) = (supportUnselected hn hP S).erase c := by
  sorry

/-- U103-B/C/D (the daughters and eq. cb:singleton-products).  Smoothing `c` at `S' = insert c S` splits
`A` into two carriers `Λ₁ ≠ Λ₂` (`smoothingSuccessor_insert_child_data`, CarrierInsertOrbits.lean:49;
`component_card_insert`, CarrierComponentCount.lean:58), leaves every other carrier unchanged
(`owner_insert_iff_of_unaffected`, :99), and cb:products before and after (the blocks of `S'` are the
blocks of `S` other than `{c}`, same labels hence same `blockPoly`; `blockPoly {c} = 1` by
lc:single-crossing) gives `P_A = P_{Λ₁} P_{Λ₂}`, `m_A = m_{Λ₁} + m_{Λ₂} + 1`. -/
theorem sg_daughters_products (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hiso : ∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') :
    ∃ (hS' : IsDecomposition hn hP (insert c S)) (Λ₁ Λ₂ : Component hn hP (insert c S)),
      Λ₁ ≠ Λ₂ ∧
      (∀ m : Mark P, owner hn hP S m = A ↔
        owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) ∧
      cornerHomfly hn hP S A hS =
        cornerHomfly hn hP (insert c S) Λ₁ hS' * cornerHomfly hn hP (insert c S) Λ₂ hS' ∧
      carrierCrossingCount hn hP S A =
        carrierCrossingCount hn hP (insert c S) Λ₁ + carrierCrossingCount hn hP (insert c S) Λ₂ + 1 := by
  sorry

/-- U103-E (the turn ledger, eq. cb:singleton-rotations).  The two new smoothing corners have opposite
nonzero turns (lem:carriers (ii)); every old corner of `A` lies on exactly one daughter with its old turn;
so one daughter is uniform with `A`'s sign `τ` and the other has exactly one dissent (both have the
SIGNED pattern the floor needs), and the real rotations add (the two new principal angles cancel).
lem:uniformrot (`uniform_rotation`, UniformRotation.lean:63) puts all three integers on the ray of `τ`,
hence `|r_A| = |r_{Λ₁}| + |r_{Λ₂}|`. -/
theorem sg_daughters_rotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (hA : CarrierUniform hn hP S A) {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hS' : IsDecomposition hn hP (insert c S)) (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hne : Λ₁ ≠ Λ₂)
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    SignedUniformOrOneDissent (ccpCornerPolygon hn hP (insert c S) Λ₁) ∧
      SignedUniformOrOneDissent (ccpCornerPolygon hn hP (insert c S) Λ₂) ∧
      carrierRotation hn hP S A =
        carrierRotation hn hP (insert c S) Λ₁ + carrierRotation hn hP (insert c S) Λ₂ ∧
      |carrierRotationInt hn hP S A| =
        |carrierRotationInt hn hP (insert c S) Λ₁| + |carrierRotationInt hn hP (insert c S) Λ₂| := by
  sorry

/-! ### Assembly of row 103 (PROVED from the leaves; exactly where `a_floor` enters: twice, at the two
daughters).  Route (FR-CC-3): the printed proof works with the `[z⁰]` rows `f_A = g₁ g₂` and a case
`f_A = 0`; here the full polynomials are nonzero (lp:core) and `mindegAZ_mul` gives eq. cb:singleton-gap
directly: `mindeg_a H⁺_A = mindeg_a H⁺_{Λ₁} + mindeg_a H⁺_{Λ₂} ≥ d_{Λ₁} + d_{Λ₂} = d_A + 2`. -/

/-- eq. cb:singleton-gap in slot form: `d_A = d_{Λ₁} + d_{Λ₂} − 2`. -/
theorem sg_slot_identity (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S S' : Finset (Crossing P)) (A : Component hn hP S) (Λ₁ Λ₂ : Component hn hP S')
    (hm : carrierCrossingCount hn hP S A =
      carrierCrossingCount hn hP S' Λ₁ + carrierCrossingCount hn hP S' Λ₂ + 1)
    (hr : |carrierRotationInt hn hP S A| =
      |carrierRotationInt hn hP S' Λ₁| + |carrierRotationInt hn hP S' Λ₂|) :
    cornerSlot hn hP S A = cornerSlot hn hP S' Λ₁ + cornerSlot hn hP S' Λ₂ - 2 := by
  unfold cornerSlot
  rw [hm, hr]
  push_cast
  ring

/-- **Row 103, conditional on the floor** (library material, D-F11/D-F14 pattern; never mapped). -/
theorem cb_singleton_of_floor (hF : FloorTheoremData) : CbSingletonData := by
  refine ⟨?_⟩
  intro n _ hn P hP S hS A hA c hc hiso
  obtain ⟨hS', Λ₁, Λ₂, hne, hown, hH, hm⟩ := sg_daughters_products hn hP hS A hc hiso
  obtain ⟨hu₁, hu₂, -, hr⟩ := sg_daughters_rotation hn hP hS A hA hc hS' Λ₁ Λ₂ hne hown
  -- thm:floor at the two daughters (their turn patterns are the ones it requires)
  have hf₁ := hF.slot_le_of_signed hn P hP (insert c S) hS' Λ₁ hu₁
  have hf₂ := hF.slot_le_of_signed hn P hP (insert c S) hS' Λ₂ hu₂
  have hslot := sg_slot_identity hn hP S (insert c S) A Λ₁ Λ₂ hm hr
  -- the coefficient at `d_A` lies strictly below the summed floor
  rw [cornerCoefficient_eq_coeffAt, hH]
  exact coeffAt_mul_eq_zero_of_lt_floor (cornerHomfly_ne_zero hn hP _ Λ₁ hS')
    (cornerHomfly_ne_zero hn hP _ Λ₂ hS') hf₁ hf₂ (by omega)

end Singleton

/-! ## §3 Row 105 lem:corner-values (sm-3:4801-4809; proof 4810-4820) -/

section CornerValues

variable {n : ℕ} [NeZero n]

/-- **lem:corner-values as printed**, one field per printed clause, `Q` a subpolygon of the decomposition
`S` of the generic `P` (def:C's binder), `m_Q = carrierCrossingCount`, `r_Q = carrierRotation` (def:uniform's
REAL `rot(Q)`, FR-CC-5), `d_Q = cornerSlot`, `c(Q) = cornerCoefficient`.
(i) "If `Q` is uniform and embedded (`m_Q = 0`) then `|r_Q| = 1`, `d_Q = 0` and `c(Q) = 1`": hypothesis
`m_Q = 0` (the printed parenthetical DEFINES embedded, FR-CC-4; embeddedness of the corner polygon in row
104's sense is a THEOREM, `cvl_embedded_of_no_crossings`); the three printed conclusions.
(ii) "If `Q` is uniform and `{y}` is a crossing of `Q` interlacing no other crossing of `Q`, then
`c(Q) = 0`" — the clause of cb:singleton with `(Q, y)` for `(A, c)` (FR-CC-6). -/
structure CornerValuesData : Prop where
  embedded_value : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniform hn hP S q → carrierCrossingCount hn hP S q = 0 →
      |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1
  isolated_zero : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniform hn hP S q →
    ∀ y ∈ carrierCrossings hn hP S q,
      (∀ y' ∈ carrierCrossings hn hP S q, y' ≠ y → ¬ Interlaces hn hP y y') →
      cornerCoefficient hn hP S q hS = 0

/-! ### Row 105 (i) — UNCONDITIONAL, PROVED (grafted from Sketch_A; no floor, no leaf).  Prefix `cvl_`. -/

/-- `m_Q = 0` ⇒ the corner polygon is an embedded polygon in the sense of row 104 (`Embedded`: nonzero
edges, remote edges disjoint, consecutive edges meet in the shared corner): lem:carriers (ii) and the
accepted `nonadjacent_meet_crossing` (LinkPositiveLift.lean:520), `consecutive_meet` (:698). -/
theorem cvl_embedded_of_no_crossings (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (h0 : carrierCrossings hn hP S q = ∅) : Embedded (ccpCornerPolygon hn hP S q) := by
  refine ⟨fun j => ((carriers_lemma hn hP hS).corner_polygons.2.1 q j).1, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨c, hc, -⟩ := nonadjacent_meet_crossing hn hP S q hS hij hxi hxj
    rw [h0] at hc
    exact Finset.notMem_empty _ hc
  · intro i
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      exact consecutive_meet hn hP S q hS i hx hx'
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨1, by norm_num, le_refl 1, (edgePoint_one _ _).symm⟩,
        ⟨0, le_refl 0, by norm_num, (edgePoint_zero _ _).symm⟩⟩

/-- (i) unconditionally: `|r_Q| = 1` by cb:embedded-rotation (EmbeddedRotation.lean:1081) on the embedded
regular corner polygon (`≥ 3` corners by lem:carriers (ii)), `d_Q = 1 − 0 − 1 = 0`, `c(Q) = [a⁰z⁰] 1 = 1`
by lp:core's `P_○ = 1` on the crossing-free positive lift (`positiveLift_isCrossingFreeCircle`,
LinkPositiveLift.lean:833; `P_circle`, `P_eq_homfly`, `coeffAt_one`).  The hypothesis "uniform" is unused
(FR-CC-4, kept literally). -/
theorem corner_values_i (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (_hu : CarrierUniform hn hP S q) (hm : carrierCrossingCount hn hP S q = 0) :
    |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1 := by
  have h0 : carrierCrossings hn hP S q = ∅ := Finset.card_eq_zero.mp hm
  have hreg : Regular (ccpCornerPolygon hn hP S q) := ccpCornerPolygon_regular hn hP hS q
  have h3 : 3 ≤ ccpCornerCount hn hP S q := (carriers_lemma hn hP hS).corner_polygons.2.2.1 q
  have hpm := (cb_embedded_rotation h3 (ccpCornerPolygon hn hP S q) hreg
    (cvl_embedded_of_no_crossings hn hP hS q h0)).pm_one
  have hrot : |carrierRotation hn hP S q| = 1 := by
    unfold carrierRotation; rcases hpm with h | h <;> rw [h] <;> simp
  have hrotZ : |carrierRotationInt hn hP S q| = 1 := by
    have := carrierRotationInt_cast hn hP hS q
    have h' : |((carrierRotationInt hn hP S q : ℤ) : ℝ)| = 1 := by rw [this]; exact hrot
    exact_mod_cast h'
  refine ⟨hrot, ?_, ?_⟩
  · simp only [cornerSlot, hm, hrotZ]; ring
  · have hslot : cornerSlot hn hP S q = 0 := by simp only [cornerSlot, hm, hrotZ]; ring
    rw [cornerCoefficient_eq_coeffAt, hslot]
    show coeffAt 0 0 (homfly _) = 1
    rw [← P_eq_homfly, P_circle (positiveLift_isCrossingFreeCircle hn hP S q hS h0), coeffAt_one]
    simp

/-- Companion: (i)'s rotation clause for def:C's integer `r_Q` (`carrierRotationInt_cast`). -/
theorem CornerValuesData.embedded_rotationInt (hD : CornerValuesData) (hn : 3 ≤ n)
    {P : LabelledTuple n} (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hu : CarrierUniform hn hP S q) (hm : carrierCrossingCount hn hP S q = 0) :
    |carrierRotationInt hn hP S q| = 1 := by
  have hrot := (hD.embedded_value n hn P hP S hS q hu hm).1
  have h' : |((carrierRotationInt hn hP S q : ℤ) : ℝ)| = 1 := by
    rw [carrierRotationInt_cast hn hP hS q]; exact hrot
  exact_mod_cast h'

/-- **Row 105 from row 103** ((ii) is cb:singleton at `(Q, y)`; (i) needs no floor). -/
theorem corner_values_of_singleton (h : CbSingletonData) : CornerValuesData where
  embedded_value := fun _ _ hn _ hP _ hS q hu h0 => corner_values_i hn hP hS q hu h0
  isolated_zero := fun n _ hn P hP S hS q hu y hy hiso => h.isolated_zero n hn P hP S hS q hu y hy hiso

/-- **Row 105, conditional on the floor** (library material). -/
theorem corner_values_of_floor (hF : FloorTheoremData) : CornerValuesData :=
  corner_values_of_singleton (cb_singleton_of_floor hF)

end CornerValues

/-! ## §4 Row 110 thm:C-S7 (sm-4:267-274; proof 275-908) — fixed target name `SM.thm_C_S7` -/

section VertexEdge

variable {n : ℕ} [NeZero n]

/-- **thm:C-S7 as printed**, one field: "At a simple vertex–edge wall at `(M; a)`, of bigon or sliding
type, with halves `λ₁, λ₂` (def:deletion-halves) and contact sign `s = χ_{a,a+1,M}(P₋)`,
`C(P₊) − C(P₋) = s C(λ₁) C(λ₂)`."  Shape of the accepted thm:A-S7 / cor:A-lawful `vertex_edge_law`
(SM/ALawful.lean:102) and of the consumer thm:uniqueness (c) (`UniquenessHypotheses.vertex_edge`,
SM/Uniqueness.lean:57): the wall is `g : WallGerm n` with `h : g.VertexEdgeAt M a` (def:walls (V));
"of bigon or sliding type" is the exhaustive dichotomy `vertexEdge_bigon_or_sliding`
(NamedWallPredicates.lean:46; FR-CC-7, no hypothesis); `s = g.contactSign M a` (`χ_{a,a+1,M}` on the
negative side, constant there: `contactSign_eq_at`, `vertex_contact_signs`, NamedWallSides.lean:58-69;
FR-CC-8); the halves are `firstHalf/secondHalf g.center M a`, generic by lem:children (ii)
(`vertex_halves_children`) — the genericity proofs are quantified (proof-irrelevant; FR-CC-9); `P₊`, `P₋`
are read at every pair of side parameters (the accepted C-row convention of prop:C-silent / hyp:R,
equivalent to def:germ's chamber values by prop:C-chamber). -/
structure CS7Data : Prop where
  vertex_edge_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.VertexEdgeAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)),
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property -
          cornerStateSum hn (g.sideTuple false tm).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂)

/-- Companion (the printed "of bigon type" reading): the law at a wall of bigon type. -/
theorem CS7Data.bigon (hD : CS7Data) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (tp tm : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true tp).property -
        cornerStateSum hn (g.sideTuple false tm).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) :=
  hD.vertex_edge_law n hn g M a h.1 h₁ h₂ tp tm

/-- Companion (the printed "of sliding type" reading): the law at a wall of sliding type. -/
theorem CS7Data.sliding (hD : CS7Data) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (tp tm : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true tp).property -
        cornerStateSum hn (g.sideTuple false tm).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) :=
  hD.vertex_edge_law n hn g M a h.1 h₁ h₂ tp tm

/-- Sanity (FR-CC-8): the contact sign in the bundle IS `χ_{a,a+1,M}` evaluated on `P₋`, at the very
parameter `tm` of the `C(P₋)` term (accepted `contactSign_eq_at`). -/
theorem CS7Data.contactSign_literal (g : WallGerm n) (M a : ZMod n) (tm : g.SideParameter) :
    (g.contactSign M a : ℤ) = ((chi (g.sideTuple false tm).val a (a + 1) M : SignType) : ℤ) := by
  rw [g.contactSign_eq_at M a tm]

/-! ### Leaves of row 110 (units U110-A … U110-K of PLAN_FINAL.md §4). Prefix `s7_`.
The two branch laws are stated at ONE side parameter below a radius; the row theorem moves both side
parameters there by chamber constancy along a side (`cornerStateSum_side_eq`, accepted SM/HypR.lean:119). -/

/-! ### U110-A helpers (prefix `s7a_`): the contact-wall partial mark transport on persistent marks -/

/-- A mark is *persistent* at the contact `(M; a)` when it is an original vertex or a visit of a
crossing other than the two contact pairs `{a, M−1}`, `{a, M}` (`ContactAffected`). -/
def s7a_Persistent (M a : ZMod n) {P : LabelledTuple n} : Mark P → Prop
  | Sum.inl _ => True
  | Sum.inr v => ¬ ContactAffected M a v.1.val

omit [NeZero n] in
@[simp] theorem s7a_persistent_inl (M a : ZMod n) {P : LabelledTuple n} (i : ZMod n) :
    s7a_Persistent M a (Sum.inl i : Mark P) := trivial

omit [NeZero n] in
@[simp] theorem s7a_persistent_inr (M a : ZMod n) {P : LabelledTuple n} (v : Visit P) :
    s7a_Persistent M a (Sum.inr v) ↔ ¬ ContactAffected M a v.1.val := Iff.rfl

section Transport

variable {P Q : LabelledTuple n} {M a : ZMod n}

omit [NeZero n] in
/-- The transported persistent visit: same crossing support, same edge label
(the visit-level content of the accepted `contactVisitTransport`). -/
def s7a_visit (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) : Visit Q :=
  ⟨⟨v.1.val, (hs _ hv).mpr v.1.property⟩, v.2⟩

omit [NeZero n] in
theorem s7a_visit_support (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    (s7a_visit hs v hv).1.val = v.1.val := rfl

omit [NeZero n] in
theorem s7a_visit_edge (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    (s7a_visit hs v hv).2.val = v.2.val := rfl

omit [NeZero n] in
theorem s7a_visit_eq_contactVisitTransport
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    s7a_visit hs v hv = (contactVisitTransport hs ⟨v, hv⟩).val := rfl

omit [NeZero n] in
theorem s7a_visit_not_affected
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    ¬ ContactAffected M a (s7a_visit hs v hv).1.val := hv

omit [NeZero n] in
theorem s7a_visit_injective
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val) (hw : ¬ ContactAffected M a w.1.val)
    (h : s7a_visit hs v hv = s7a_visit hs w hw) : v = w := by
  have h1 : (⟨v, hv⟩ : PersistentContactVisit P M a) = ⟨w, hw⟩ :=
    (contactVisitTransport hs).injective (Subtype.ext h)
  exact congrArg Subtype.val h1

omit [NeZero n] in
theorem s7a_visit_surjective
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (w : Visit Q) (hw : ¬ ContactAffected M a w.1.val) :
    ∃ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val), s7a_visit hs v hv = w := by
  obtain ⟨v, hv⟩ := (contactVisitTransport hs).surjective ⟨w, hw⟩
  exact ⟨v.1, v.2, congrArg Subtype.val hv⟩

omit [NeZero n] in
/-- Two visits with the same crossing and the same edge label are equal. -/
theorem s7a_visit_ext {P : LabelledTuple n} (v w : Visit P) (hc : v.1 = w.1)
    (he : v.2.val = w.2.val) : v = w := by
  rcases v with ⟨c, i⟩
  rcases w with ⟨d, j⟩
  dsimp only at hc he
  subst hc
  exact congrArg (fun k : {k // k ∈ c.val} => (⟨c, k⟩ : Visit P)) (Subtype.ext he)

omit [NeZero n] in
/-- The twin is carried (same crossing, different edge). -/
theorem s7a_visit_twin (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    s7a_visit hs (visitTwin v) hv = visitTwin (s7a_visit hs v hv) := by
  apply visitTwin_unique
  · rfl
  · intro h
    have he : (visitTwin v).2.val = v.2.val := congrArg (fun w : Visit Q => w.2.val) h
    exact visitTwin_ne v (s7a_visit_ext _ _ (visitTwin_crossing v) he)

omit [NeZero n] in
/-- The total mark map: vertices fixed, persistent visits transported, the (never used) contact
visits sent to the vertex `0`. -/
def s7a_markMap (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)) :
    Mark P → Mark Q
  | Sum.inl i => Sum.inl i
  | Sum.inr v => if hv : ContactAffected M a v.1.val then Sum.inl 0 else Sum.inr (s7a_visit hs v hv)

omit [NeZero n] in
@[simp] theorem s7a_markMap_inl (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (i : ZMod n) : s7a_markMap hs (Sum.inl i) = Sum.inl i := rfl

omit [NeZero n] in
theorem s7a_markMap_inr (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    s7a_markMap hs (Sum.inr v) = Sum.inr (s7a_visit hs v hv) := by
  show (if hv' : ContactAffected M a v.1.val then (Sum.inl 0 : Mark Q)
    else Sum.inr (s7a_visit hs v hv')) = _
  rw [dite_eq_right hv]

omit [NeZero n] in
theorem s7a_markMap_persistent
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (m : Mark P) (hm : s7a_Persistent M a m) : s7a_Persistent M a (s7a_markMap hs m) := by
  cases m with
  | inl i => trivial
  | inr v =>
    rw [s7a_markMap_inr hs v hm]
    exact hm

omit [NeZero n] in
theorem s7a_markMap_injOn
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (m m' : Mark P) (hm : s7a_Persistent M a m) (hm' : s7a_Persistent M a m')
    (h : s7a_markMap hs m = s7a_markMap hs m') : m = m' := by
  cases m with
  | inl i =>
    cases m' with
    | inl j => exact congrArg Sum.inl (Sum.inl_injective h)
    | inr w =>
      rw [s7a_markMap_inr hs w hm'] at h
      exact absurd h Sum.inl_ne_inr
  | inr v =>
    cases m' with
    | inl j =>
      rw [s7a_markMap_inr hs v hm] at h
      exact absurd h Sum.inr_ne_inl
    | inr w =>
      rw [s7a_markMap_inr hs v hm, s7a_markMap_inr hs w hm'] at h
      exact congrArg Sum.inr (s7a_visit_injective hs v w hm hm' (Sum.inr_injective h))

omit [NeZero n] in
theorem s7a_markMap_surjOn
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (m' : Mark Q) (hm' : s7a_Persistent M a m') :
    ∃ m : Mark P, s7a_Persistent M a m ∧ s7a_markMap hs m = m' := by
  cases m' with
  | inl i => exact ⟨Sum.inl i, trivial, rfl⟩
  | inr w =>
    obtain ⟨v, hv, hvw⟩ := s7a_visit_surjective hs w hm'
    exact ⟨Sum.inr v, hv, by rw [s7a_markMap_inr hs v hv, hvw]⟩

/-- The mark map commutes with the selected-mark exchange for a persistent support (the twin is
carried, membership in the transported support is membership in the support). -/
theorem s7a_markMap_selectedMarkPerm
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (S : Finset (Crossing P)) (S' : Finset (Crossing Q))
    (hSS' : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      (s7a_visit hs v hv).1 ∈ S' ↔ v.1 ∈ S)
    (m : Mark P) (hm : s7a_Persistent M a m) :
    selectedMarkPerm S' (s7a_markMap hs m) = s7a_markMap hs (selectedMarkPerm S m) := by
  cases m with
  | inl i => rfl
  | inr v =>
    have hv0 : ¬ ContactAffected M a v.1.val := hm
    rw [s7a_markMap_inr hs v hv0, selectedMarkPerm_visit, selectedMarkPerm_visit]
    by_cases hv : v.1 ∈ S
    · have hm' : ¬ ContactAffected M a (visitTwin v).1.val := hv0
      rw [selectedVisitTwin_of_mem _ _ hv, selectedVisitTwin_of_mem _ _ ((hSS' v hv0).mpr hv),
        s7a_markMap_inr hs _ hm']
      exact congrArg Sum.inr (s7a_visit_twin hs v hv0).symm
    · rw [selectedVisitTwin_of_not_mem _ _ hv,
        selectedVisitTwin_of_not_mem _ _ (fun h => hv ((hSS' v hv0).mp h)), s7a_markMap_inr hs v hv0]

/-! #### Key order and the filtered sorted mark list -/

/-- The mark order among persistent marks is carried, given the same-edge parameter order of
persistent visits (vertex/vertex by label, vertex/visit by label and strict interiority,
visit/visit by label or by the parameter hypothesis) — the persistent analogue of
`Carrier.markKey_lt_transport`. -/
theorem s7a_markKey_lt (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hpar : ∀ (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit hs v hv) < visitParameter (s7a_visit hs w hw) ↔
        visitParameter v < visitParameter w))
    (m m' : Mark P) (hm : s7a_Persistent M a m) (hm' : s7a_Persistent M a m') :
    markKey hn hQ.1 (s7a_markMap hs m) < markKey hn hQ.1 (s7a_markMap hs m') ↔
      markKey hn hP.1 m < markKey hn hP.1 m' := by
  cases m with
  | inl i =>
    cases m' with
    | inl j => simp only [s7a_markMap_inl, markKey_vertex]
    | inr w =>
      rw [s7a_markMap_inl, s7a_markMap_inr hs w hm']
      unfold markKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (i.val < w.2.val.val ∨ i = w.2.val ∧ (0 : ℝ) < visitParameter (s7a_visit hs w hm')) ↔
        (i.val < w.2.val.val ∨ i = w.2.val ∧ (0 : ℝ) < visitParameter w)
      exact or_congr Iff.rfl (and_congr_right fun _ => iff_of_true
        (visitPosition_interior hn hQ.1 _).1 (visitPosition_interior hn hP.1 w).1)
  | inr v =>
    cases m' with
    | inl j =>
      rw [s7a_markMap_inl, s7a_markMap_inr hs v hm]
      unfold markKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < j.val ∨ v.2.val = j ∧ visitParameter (s7a_visit hs v hm) < (0 : ℝ)) ↔
        (v.2.val.val < j.val ∨ v.2.val = j ∧ visitParameter v < (0 : ℝ))
      exact or_congr Iff.rfl (and_congr_right fun _ => iff_of_false
        (not_lt.mpr (visitPosition_interior hn hQ.1 _).1.le)
        (not_lt.mpr (visitPosition_interior hn hP.1 v).1.le))
    | inr w =>
      rw [s7a_markMap_inr hs v hm, s7a_markMap_inr hs w hm']
      unfold markKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧
          visitParameter (s7a_visit hs v hm) < visitParameter (s7a_visit hs w hm')) ↔
        (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧ visitParameter v < visitParameter w)
      exact or_congr Iff.rfl (and_congr_right fun he => hpar v w hm hm' he)

/-- The sorted mark list of `Q`, restricted to persistent marks, is literally the transported
restricted sorted mark list of `P` (`List.Perm.eq_of_pairwise`: both are strictly key-sorted lists of
the same members). -/
theorem s7a_markList_filter (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hpar : ∀ (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit hs v hv) < visitParameter (s7a_visit hs w hw) ↔
        visitParameter v < visitParameter w)) :
    (markList hn hQ).filter (fun m => decide (s7a_Persistent M a m)) =
      ((markList hn hP).filter (fun m => decide (s7a_Persistent M a m))).map (s7a_markMap hs) := by
  have hmemP : ∀ m : Mark P, m ∈ (markList hn hP).filter (fun m => decide (s7a_Persistent M a m)) ↔
      s7a_Persistent M a m := by
    intro m
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_markList hn hP m, h⟩⟩
  have hmemQ : ∀ m : Mark Q, m ∈ (markList hn hQ).filter (fun m => decide (s7a_Persistent M a m)) ↔
      s7a_Persistent M a m := by
    intro m
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_markList hn hQ m, h⟩⟩
  have hnodP : ((markList hn hP).filter (fun m => decide (s7a_Persistent M a m))).Nodup :=
    (markList_nodup hn hP).filter _
  have hnodQ : ((markList hn hQ).filter (fun m => decide (s7a_Persistent M a m))).Nodup :=
    (markList_nodup hn hQ).filter _
  have hnodmap : (((markList hn hP).filter (fun m => decide (s7a_Persistent M a m))).map
      (s7a_markMap hs)).Nodup := by
    refine hnodP.map_on ?_
    intro m hm m' hm' h
    exact s7a_markMap_injOn hs m m' ((hmemP m).mp hm) ((hmemP m').mp hm') h
  apply List.Perm.eq_of_pairwise (le := fun a b => markKey hn hQ.1 a ≤ markKey hn hQ.1 b)
  · intro a b _ _ hab hba
    exact markKey_injective hn hQ (le_antisymm hab hba)
  · exact (markList_sorted hn hQ).filter _
  · rw [List.pairwise_map]
    refine ((markList_sorted hn hP).filter _).imp_of_mem ?_
    intro a b ha hb h
    rw [← not_lt] at h ⊢
    intro h'
    exact h ((s7a_markKey_lt hn hP hQ hs hpar b a ((hmemP b).mp hb) ((hmemP a).mp ha)).mp h')
  · apply (List.perm_ext_iff_of_nodup hnodQ hnodmap).mpr
    intro m'
    rw [hmemQ, List.mem_map]
    constructor
    · intro h
      obtain ⟨m, hm, rfl⟩ := s7a_markMap_surjOn hs m' h
      exact ⟨m, (hmemP m).mpr hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact s7a_markMap_persistent hs m ((hmemP m).mp hm)

end Transport

/-! #### Circular order of marks (helpers on `traversalBetween`) -/

section Cyclic

variable {P : LabelledTuple n}

omit [NeZero n] in
theorem s7a_cyc_or (x y z : ℝ) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ((x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y)) ∨
      ((x < z ∧ z < y) ∨ (z < y ∧ y < x) ∨ (y < x ∧ x < z)) := by
  rcases lt_trichotomy x y with h1 | h1 | h1
  · rcases lt_trichotomy y z with h2 | h2 | h2
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · exact absurd h2 hyz
    · rcases lt_trichotomy x z with h3 | h3 | h3
      · exact Or.inr (Or.inl ⟨h3, h2⟩)
      · exact absurd h3 hxz
      · exact Or.inl (Or.inr (Or.inr ⟨h3, h1⟩))
  · exact absurd h1 hxy
  · rcases lt_trichotomy y z with h2 | h2 | h2
    · rcases lt_trichotomy x z with h3 | h3 | h3
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h3⟩))
      · exact absurd h3 hxz
      · exact Or.inl (Or.inr (Or.inl ⟨h2, h3⟩))
    · exact absurd h2 hyz
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))

/-- Three distinct marks are cyclically ordered one way or the other. -/
theorem s7a_between_or (hn : 3 ≤ n) (hP : Generic P) (p q r : Mark P) (hpq : p ≠ q) (hqr : q ≠ r)
    (hpr : p ≠ r) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r) ∨
      traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 r) (markPosition hn hP.1 q) := by
  have hk : ∀ u w : Mark P, u ≠ w →
      traversalKey (markPosition hn hP.1 u) ≠ traversalKey (markPosition hn hP.1 w) :=
    fun u w h he => h (markKey_injective hn hP he)
  exact s7a_cyc_or _ _ _ (hk p q hpq) (hk q r hqr) (hk p r hpr)

theorem s7a_between_trans (hn : 3 ≤ n) (hP : Generic P) {p q r s : Mark P}
    (h1 : traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r))
    (h2 : traversalBetween (markPosition hn hP.1 q) (markPosition hn hP.1 s) (markPosition hn hP.1 r)) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 s) (markPosition hn hP.1 r) := by
  let _inst : CircularOrder (TraversalPoint n) := traversalCircularOrder
  exact (traversalBetween_eq_circular _ _ _).mpr
    (sbtw_trans_left ((traversalBetween_eq_circular _ _ _).mp h1) ((traversalBetween_eq_circular _ _ _).mp h2))

theorem s7a_between_asymm (hn : 3 ≤ n) (hP : Generic P) {p q r : Mark P}
    (h1 : traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r))
    (h2 : traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 r) (markPosition hn hP.1 q)) :
    False := by
  let _inst : CircularOrder (TraversalPoint n) := traversalCircularOrder
  exact sbtw_asymm ((traversalBetween_eq_circular _ _ _).mp h1)
    (sbtw_cyclic_left ((traversalBetween_eq_circular _ _ _).mp h2))

omit [NeZero n] in
theorem s7a_between_ne (hn : 3 ≤ n) (hP : Generic P) {p q r : Mark P}
    (h : traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r)) :
    p ≠ q ∧ q ≠ r ∧ p ≠ r := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

end Cyclic

/-! #### The contracted successor (first return to the persistent marks) -/

section Contract

variable {P : LabelledTuple n} {M a : ZMod n}

/-- The persistent marks of `P`. -/
abbrev s7a_PMark (M a : ZMod n) (P : LabelledTuple n) := {m : Mark P // s7a_Persistent M a m}

variable (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))

theorem s7a_exists_return (m : Mark P) (hm : s7a_Persistent M a m) :
    ∃ j : ℕ, 0 < j ∧ s7a_Persistent M a ((smoothingSuccessor hn hP S ^ j) m) :=
  ⟨orderOf (smoothingSuccessor hn hP S), orderOf_pos _, by
    rw [pow_orderOf_eq_one, Equiv.Perm.one_apply]; exact hm⟩

/-- The first return time of the smoothing successor to the persistent marks. -/
def s7a_returnTime (m : Mark P) (hm : s7a_Persistent M a m) : ℕ :=
  Nat.find (s7a_exists_return hn hP S m hm)

theorem s7a_returnTime_pos (m : Mark P) (hm : s7a_Persistent M a m) :
    0 < s7a_returnTime hn hP S m hm :=
  (Nat.find_spec (s7a_exists_return hn hP S m hm)).1

theorem s7a_returnTime_persistent (m : Mark P) (hm : s7a_Persistent M a m) :
    s7a_Persistent M a ((smoothingSuccessor hn hP S ^ s7a_returnTime hn hP S m hm) m) :=
  (Nat.find_spec (s7a_exists_return hn hP S m hm)).2

theorem s7a_returnTime_min (m : Mark P) (hm : s7a_Persistent M a m) (i : ℕ) (hi : 0 < i)
    (hlt : i < s7a_returnTime hn hP S m hm) :
    ¬ s7a_Persistent M a ((smoothingSuccessor hn hP S ^ i) m) := by
  intro h
  exact absurd (Nat.find_min' (s7a_exists_return hn hP S m hm) ⟨hi, h⟩) (not_le.mpr hlt)

/-- The contracted successor on persistent marks. -/
def s7a_step (x : s7a_PMark M a P) : s7a_PMark M a P :=
  ⟨(smoothingSuccessor hn hP S ^ s7a_returnTime hn hP S x.1 x.2) x.1,
    s7a_returnTime_persistent hn hP S x.1 x.2⟩

theorem s7a_step_val (x : s7a_PMark M a P) :
    (s7a_step hn hP S x).1 = (smoothingSuccessor hn hP S ^ s7a_returnTime hn hP S x.1 x.2) x.1 := rfl

theorem s7a_step_inj_aux (x y : s7a_PMark M a P)
    (hle : s7a_returnTime hn hP S x.1 x.2 ≤ s7a_returnTime hn hP S y.1 y.2)
    (h : s7a_step hn hP S x = s7a_step hn hP S y) : x = y := by
  set f := smoothingSuccessor hn hP S with hf
  set i := s7a_returnTime hn hP S x.1 x.2 with hi
  set j := s7a_returnTime hn hP S y.1 y.2 with hj
  have h1 : (f ^ i) x.1 = (f ^ j) y.1 := congrArg Subtype.val h
  have h2 : (f ^ j) y.1 = (f ^ i) ((f ^ (j - i)) y.1) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
  have h3 : (f ^ (j - i)) y.1 = x.1 := (f ^ i).injective (h2.symm.trans h1.symm)
  by_cases hji : j - i = 0
  · have hij : i = j := by omega
    apply Subtype.ext
    exact (f ^ i).injective (h1.trans (by rw [hij]))
  · exfalso
    have hpos : 0 < j - i := Nat.pos_of_ne_zero hji
    have hlt : j - i < j := Nat.sub_lt_self (s7a_returnTime_pos hn hP S x.1 x.2) hle
    exact s7a_returnTime_min hn hP S y.1 y.2 (j - i) hpos hlt (h3 ▸ x.2)

theorem s7a_step_injective : Function.Injective (s7a_step hn hP S (M := M) (a := a)) := by
  intro x y h
  rcases le_total (s7a_returnTime hn hP S x.1 x.2) (s7a_returnTime hn hP S y.1 y.2) with hle | hle
  · exact s7a_step_inj_aux hn hP S x y hle h
  · exact (s7a_step_inj_aux hn hP S y x hle h.symm).symm

/-- The contracted successor as a permutation of the persistent marks. -/
def s7a_stepPerm : Equiv.Perm (s7a_PMark M a P) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (s7a_step_injective hn hP S))

theorem s7a_stepPerm_apply (x : s7a_PMark M a P) : s7a_stepPerm hn hP S x = s7a_step hn hP S x := rfl

theorem s7a_sameCycle_step (x : s7a_PMark M a P) :
    (smoothingSuccessor hn hP S).SameCycle x.1 (s7a_step hn hP S x).1 :=
  ⟨(s7a_returnTime hn hP S x.1 x.2 : ℤ), by rw [zpow_natCast]; rfl⟩

theorem s7a_sameCycle_of_stepPerm (x y : s7a_PMark M a P)
    (h : (s7a_stepPerm hn hP S).SameCycle x y) : (smoothingSuccessor hn hP S).SameCycle x.1 y.1 := by
  obtain ⟨k, _, hk⟩ := h.exists_pow_eq'
  have hpow : ∀ (m : ℕ) (z : s7a_PMark M a P),
      (smoothingSuccessor hn hP S).SameCycle z.1 (((s7a_stepPerm hn hP S) ^ m) z).1 := by
    intro m
    induction m with
    | zero => intro z; simp only [pow_zero, Equiv.Perm.one_apply]; exact Equiv.Perm.SameCycle.refl _ _
    | succ m ih =>
      intro z
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (ih z).trans (s7a_sameCycle_step hn hP S _)
  rw [← hk]
  exact hpow k x

theorem s7a_stepPerm_of_sameCycle (x y : s7a_PMark M a P)
    (h : (smoothingSuccessor hn hP S).SameCycle x.1 y.1) : (s7a_stepPerm hn hP S).SameCycle x y := by
  obtain ⟨k, _, hk⟩ := h.exists_pow_eq'
  set f := smoothingSuccessor hn hP S with hf
  have key : ∀ k : ℕ, ∀ x y : s7a_PMark M a P, (f ^ k) x.1 = y.1 →
      (s7a_stepPerm hn hP S).SameCycle x y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x y hk
      by_cases hk0 : k = 0
      · subst hk0
        simp only [pow_zero, Equiv.Perm.one_apply] at hk
        rw [Subtype.ext hk]
      · set r := s7a_returnTime hn hP S x.1 x.2 with hr
        have hrpos : 0 < r := s7a_returnTime_pos hn hP S x.1 x.2
        by_cases hrk : r ≤ k
        · have h1 : (f ^ (k - r)) (s7a_step hn hP S x).1 = y.1 := by
            rw [s7a_step_val, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hrk, hk]
          have h2 := ih (k - r) (Nat.sub_lt (Nat.pos_of_ne_zero hk0) hrpos) (s7a_step hn hP S x) y h1
          have h3 : (s7a_stepPerm hn hP S).SameCycle x (s7a_step hn hP S x) :=
            Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
          exact h3.trans h2
        · exfalso
          exact s7a_returnTime_min hn hP S x.1 x.2 k (Nat.pos_of_ne_zero hk0) (not_le.mp hrk) (hk ▸ y.2)
  exact key k x y hk

theorem s7a_sameCycle_stepPerm_iff (x y : s7a_PMark M a P) :
    (smoothingSuccessor hn hP S).SameCycle x.1 y.1 ↔ (s7a_stepPerm hn hP S).SameCycle x y :=
  ⟨s7a_stepPerm_of_sameCycle hn hP S x y, s7a_sameCycle_of_stepPerm hn hP S x y⟩

/-- Every carrier of a persistent support has a persistent mark (a true corner:
`component_has_trueCorner`). -/
theorem s7a_component_has_persistent (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val)
    (q : Component hn hP S) : ∃ m : Mark P, owner hn hP S m = q ∧ s7a_Persistent M a m := by
  obtain ⟨m, hm, hc⟩ := component_has_trueCorner hn hP S q
  refine ⟨m, hm, ?_⟩
  cases m with
  | inl i => trivial
  | inr v => exact hSp v.1 hc

/-- The carriers of a persistent support are the cycles of the contracted successor. -/
def s7a_componentEquivQuot (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) :
    Component hn hP S ≃ Quotient (Equiv.Perm.SameCycle.setoid (s7a_stepPerm hn hP S (M := M) (a := a))) :=
  (Equiv.ofBijective
    (Quotient.lift (fun x : s7a_PMark M a P => owner hn hP S x.1)
      (fun x y h => (owner_eq_iff hn hP S x.1 y.1).mpr ((s7a_sameCycle_stepPerm_iff hn hP S x y).mpr h)))
    (by
      constructor
      · intro u v huv
        induction u using Quotient.inductionOn with
        | h x =>
          induction v using Quotient.inductionOn with
          | h y =>
            apply Quotient.sound
            exact (s7a_sameCycle_stepPerm_iff hn hP S x y).mp
              ((owner_eq_iff hn hP S x.1 y.1).mp huv)
      · intro q
        obtain ⟨m, hm, hmp⟩ := s7a_component_has_persistent hn hP S hSp q
        exact ⟨Quotient.mk _ ⟨m, hmp⟩, hm⟩)).symm

theorem s7a_componentEquivQuot_owner (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val)
    (m : Mark P) (hm : s7a_Persistent M a m) :
    s7a_componentEquivQuot hn hP S hSp (owner hn hP S m) =
      Quotient.mk _ (⟨m, hm⟩ : s7a_PMark M a P) := by
  unfold s7a_componentEquivQuot
  exact Equiv.symm_apply_eq _ |>.mpr rfl

end Contract

/-! #### The order characterization of the contracted step, and its transport -/

section FirstAfter

variable {P : LabelledTuple n} {M a : ZMod n} (hn : 3 ≤ n) (hP : Generic P)

omit [NeZero n] in
/-- A power of a permutation, applied at a point of period `m`, reduces modulo `m`. -/
theorem s7a_pow_apply_mod {α : Type*} (f : Equiv.Perm α) (x : α) (m : ℕ) (hm : (f ^ m) x = x)
    (i : ℕ) : (f ^ i) x = (f ^ (i % m)) x := by
  conv_lhs => rw [← Nat.mod_add_div i m]
  rw [pow_add, pow_mul, Equiv.Perm.mul_apply]
  congr 1
  induction (i / m) with
  | zero => simp
  | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, hm, ih]

omit [NeZero n] in
/-- If two iterates `f^(j+1) c = f^k c` agree with `0 < k ≤ j`, the point has period `j+1-k`. -/
theorem s7a_pow_period {α : Type*} (f : Equiv.Perm α) (c : α) (j k : ℕ) (hk : k ≤ j + 1)
    (h : (f ^ (j + 1)) c = (f ^ k) c) : (f ^ (j + 1 - k)) c = c := by
  have h2 : (f ^ (j + 1)) c = (f ^ k) ((f ^ (j + 1 - k)) c) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hk]
  exact (f ^ k).injective (h2.symm.trans h)

/-- **The sweep lemma.** Iterating `nextMark` from `c` visits the marks in cyclic order: as long as a
mark `u ≠ c` is not among the first `j` iterates, none of these iterates has returned to `c` and the
`j`-th iterate lies cyclically before `u` (seen from `c`).  From the accepted
`markSuccessor_no_mark_between` (no mark strictly between a mark and its successor). -/
theorem s7a_sweep (c : Mark P) (j : ℕ) (hj : 0 < j) :
    ∀ u : Mark P, u ≠ c → (∀ i, 0 < i → i ≤ j → u ≠ (markSuccessor hn hP ^ i) c) →
    (∀ i, 0 < i → i ≤ j → (markSuccessor hn hP ^ i) c ≠ c) ∧
      traversalBetween (markPosition hn hP.1 c) (markPosition hn hP.1 ((markSuccessor hn hP ^ j) c))
        (markPosition hn hP.1 u) := by
  set ms := markSuccessor hn hP with hms
  induction j with
  | zero => exact absurd hj (lt_irrefl 0)
  | succ j ih =>
    intro u hu hchain
    -- the orbit of `ms` through `c` reaches `u`
    obtain ⟨k₀, _, hk₀⟩ := (markSuccessor_sameCycle hn hP c u).exists_pow_eq'
    -- (i') no return at step `j+1`
    have hne : (ms ^ (j + 1)) c ≠ c := by
      intro hret
      have hmod := s7a_pow_apply_mod ms c (j + 1) hret k₀
      rw [hk₀] at hmod
      have hlt : k₀ % (j + 1) < j + 1 := Nat.mod_lt _ (Nat.succ_pos j)
      by_cases h0 : k₀ % (j + 1) = 0
      · rw [h0, pow_zero, Equiv.Perm.one_apply] at hmod
        exact hu hmod
      · exact hchain _ (Nat.pos_of_ne_zero h0) (by omega) hmod
    by_cases hj0 : j = 0
    · subst hj0
      simp only [zero_add, pow_one] at hne hchain ⊢
      refine ⟨fun i hi hi1 => ?_, ?_⟩
      · have : i = 1 := by omega
        subst this
        simpa using hne
      · have hnb := markSuccessor_no_mark_between hn hP c u
        rcases s7a_between_or hn hP c (ms c) u (Ne.symm hne) (Ne.symm (hchain 1 one_pos le_rfl))
          (Ne.symm hu) with h | h
        · exact h
        · exact absurd h hnb
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hchainj : ∀ i, 0 < i → i ≤ j → u ≠ (ms ^ i) c :=
        fun i hi hij => hchain i hi (Nat.le_succ_of_le hij)
      obtain ⟨hA, hB⟩ := ih hjpos u hu hchainj
      -- the new iterate is not among the earlier ones
      have hnew : ∀ i, 0 < i → i ≤ j → (ms ^ (j + 1)) c ≠ (ms ^ i) c := by
        intro i hi hij heq
        have hper := s7a_pow_period ms c j i (by omega) heq
        exact hA (j + 1 - i) (by omega) (by omega) hper
      refine ⟨fun i hi hi1 => ?_, ?_⟩
      · rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · exact hA i hi (Nat.lt_succ_iff.mp hlt)
        · have : i = j + 1 := by omega
          subst this
          exact hne
      · -- the new iterate lies between `c` and `u`
        have hB' := (ih hjpos ((ms ^ (j + 1)) c) hne hnew).2
        have hsucc : (ms ^ (j + 1)) c = ms ((ms ^ j) c) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        have hnb := markSuccessor_no_mark_between hn hP ((ms ^ j) c) u
        rw [← hsucc] at hnb
        rcases s7a_between_or hn hP ((ms ^ j) c) ((ms ^ (j + 1)) c) u (hnew j hjpos le_rfl).symm
          (hchain (j + 1) (Nat.succ_pos j) le_rfl).symm (hchain j hjpos (Nat.le_succ j)).symm with h | h
        · exact s7a_between_trans hn hP hB h
        · exact absurd h hnb

variable (S : Finset (Crossing P))

/-- The `f`-iterates of a persistent mark up to its return time are the `nextMark`-iterates of its
selected-exchange image (the intermediate marks are unselected contact visits, fixed by the exchange). -/
theorem s7a_pow_eq_markSuccessor_pow (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val)
    (x : s7a_PMark M a P) (i : ℕ) (hi : 0 < i) (hle : i ≤ s7a_returnTime hn hP S x.1 x.2) :
    (smoothingSuccessor hn hP S ^ i) x.1 = (markSuccessor hn hP ^ i) (selectedMarkPerm S x.1) := by
  induction i with
  | zero => exact absurd hi (lt_irrefl 0)
  | succ i ih =>
    by_cases hi0 : i = 0
    · subst hi0
      rfl
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hilt : i < s7a_returnTime hn hP S x.1 x.2 := hle
      have hih := ih hipos hilt.le
      have hnp := s7a_returnTime_min hn hP S x.1 x.2 i hipos hilt
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hih]
      -- the intermediate mark is an unselected (contact) visit: the exchange fixes it
      change markSuccessor hn hP (selectedMarkPerm S ((markSuccessor hn hP ^ i) (selectedMarkPerm S x.1))) = _
      congr 1
      rw [← hih]
      cases hm : (smoothingSuccessor hn hP S ^ i) x.1 with
      | inl k => rw [hm] at hnp; exact (hnp trivial).elim
      | inr v =>
        rw [hm] at hnp
        have hvS : v.1 ∉ S := fun h => hnp (hSp v.1 h)
        rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hvS]

omit [NeZero n] in
include hn in
/-- Some vertex differs from two given marks (`n ≥ 3`). -/
theorem s7a_exists_vertex_ne (p y : Mark P) :
    ∃ i : ZMod n, (Sum.inl i : Mark P) ≠ p ∧ (Sum.inl i : Mark P) ≠ y := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have h1 : (0 : ZMod n) - 1 ≠ 0 := prev_ne_self 0
  have h2 : (0 : ZMod n) + 1 ≠ 0 := next_ne_self 0
  have h3 : (0 : ZMod n) - 1 ≠ 0 + 1 := prev_ne_next hn 0
  by_cases hp0 : p = Sum.inl (0 : ZMod n)
  · by_cases hy1 : y = Sum.inl ((0 : ZMod n) + 1)
    · exact ⟨0 - 1, by rw [hp0]; exact fun h => h1 (Sum.inl_injective h),
        by rw [hy1]; exact fun h => h3 (Sum.inl_injective h)⟩
    · exact ⟨0 + 1, by rw [hp0]; exact fun h => h2 (Sum.inl_injective h), fun h => hy1 h.symm⟩
  · by_cases hy0 : y = Sum.inl (0 : ZMod n)
    · by_cases hp1 : p = Sum.inl ((0 : ZMod n) + 1)
      · exact ⟨0 - 1, by rw [hp1]; exact fun h => h3 (Sum.inl_injective h),
          by rw [hy0]; exact fun h => h1 (Sum.inl_injective h)⟩
      · exact ⟨0 + 1, fun h => hp1 h.symm, by rw [hy0]; exact fun h => h2 (Sum.inl_injective h)⟩
    · exact ⟨0, fun h => hp0 h.symm, fun h => hy0 h.symm⟩

/-- **The order characterization of the contracted step**: `step x` is the first persistent mark
strictly after the selected-exchange image `p` of `x` in cyclic order — it differs from `p`, and every
other persistent mark `z ≠ p` lies cyclically after it (seen from `p`). -/
theorem s7a_step_firstAfter (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (x : s7a_PMark M a P) :
    (s7a_step hn hP S x).1 ≠ selectedMarkPerm S x.1 ∧
      ∀ z : Mark P, s7a_Persistent M a z → z ≠ selectedMarkPerm S x.1 →
        z ≠ (s7a_step hn hP S x).1 →
        traversalBetween (markPosition hn hP.1 (selectedMarkPerm S x.1))
          (markPosition hn hP.1 (s7a_step hn hP S x).1) (markPosition hn hP.1 z) := by
  set r := s7a_returnTime hn hP S x.1 x.2 with hr
  have hrpos : 0 < r := s7a_returnTime_pos hn hP S x.1 x.2
  set p := selectedMarkPerm S x.1 with hp
  have hstep : (s7a_step hn hP S x).1 = (markSuccessor hn hP ^ r) p :=
    s7a_pow_eq_markSuccessor_pow hn hP S hSp x r hrpos le_rfl
  -- the intermediate iterates are not persistent
  have hmid : ∀ i, 0 < i → i < r → ¬ s7a_Persistent M a ((markSuccessor hn hP ^ i) p) := by
    intro i hi hir
    rw [← s7a_pow_eq_markSuccessor_pow hn hP S hSp x i hi hir.le]
    exact s7a_returnTime_min hn hP S x.1 x.2 i hi hir
  have hchain : ∀ z : Mark P, s7a_Persistent M a z → z ≠ (s7a_step hn hP S x).1 →
      ∀ i, 0 < i → i ≤ r → z ≠ (markSuccessor hn hP ^ i) p := by
    intro z hz hzy i hi hir
    rcases Nat.lt_or_ge i r with hlt | hge
    · intro he
      exact hmid i hi hlt (he ▸ hz)
    · have : i = r := by omega
      subst this
      rw [← hstep]
      exact hzy
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hip, hiy⟩ := s7a_exists_vertex_ne hn p (s7a_step hn hP S x).1
    have hA := (s7a_sweep hn hP p r hrpos (Sum.inl i) hip (hchain _ trivial hiy)).1
    rw [hstep]
    exact hA r hrpos le_rfl
  · intro z hz hzp hzy
    have hB := (s7a_sweep hn hP p r hrpos z hzp (hchain z hz hzy)).2
    rw [hstep]
    exact hB

/-- Uniqueness of the first persistent mark after `p`. -/
theorem s7a_firstAfter_unique (p y y' : Mark P) (hy : s7a_Persistent M a y)
    (hy' : s7a_Persistent M a y')
    (h : y ≠ p ∧ ∀ z : Mark P, s7a_Persistent M a z → z ≠ p → z ≠ y →
      traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 y) (markPosition hn hP.1 z))
    (h' : y' ≠ p ∧ ∀ z : Mark P, s7a_Persistent M a z → z ≠ p → z ≠ y' →
      traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 y') (markPosition hn hP.1 z)) :
    y = y' := by
  by_contra hne
  exact s7a_between_asymm hn hP (h.2 y' hy' h'.1 (Ne.symm hne)) (h'.2 y hy h.1 hne)

end FirstAfter

/-! #### Conjugation of the contracted steps through the mark map; the carrier equivalence -/

omit [NeZero n] in
/-- `SameCycle` under a conjugating equivalence. -/
theorem s7a_sameCycle_of_equiv_conj {α β : Type*} (f : Equiv.Perm α) (g : Equiv.Perm β) (e : α ≃ β)
    (h : ∀ x, g (e x) = e (f x)) (x y : α) : g.SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  have hinv : ∀ x, g⁻¹ (e x) = e (f⁻¹ x) := by
    intro x
    rw [Equiv.Perm.inv_eq_iff_eq, h, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have hzpow : ∀ (i : ℤ) (x : α), (g ^ i) (e x) = e ((f ^ i) x) := by
    intro i
    induction i using Int.induction_on with
    | zero => intro x; rw [zpow_zero, zpow_zero, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
    | succ i ih =>
      intro x
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, ih]
    | pred i ih =>
      intro x
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, ih]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, e.injective ((hzpow i x).symm.trans hi)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hzpow i x).trans (congrArg e hi)⟩

section Conjugation

variable {P Q : LabelledTuple n} {M a : ZMod n} (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
  (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (hpar : ∀ (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit hs v hv) < visitParameter (s7a_visit hs w hw) ↔
        visitParameter v < visitParameter w))

/-- The mark map on persistent marks, as an equivalence. -/
def s7a_pmarkEquiv : s7a_PMark M a P ≃ s7a_PMark M a Q :=
  Equiv.ofBijective (fun x => ⟨s7a_markMap hs x.1, s7a_markMap_persistent hs x.1 x.2⟩)
    ⟨fun x y h => Subtype.ext (s7a_markMap_injOn hs x.1 y.1 x.2 y.2 (congrArg Subtype.val h)),
      fun y => by
        obtain ⟨m, hm, hmy⟩ := s7a_markMap_surjOn hs y.1 y.2
        exact ⟨⟨m, hm⟩, Subtype.ext hmy⟩⟩

omit [NeZero n] in
theorem s7a_pmarkEquiv_val (x : s7a_PMark M a P) :
    (s7a_pmarkEquiv hs x).1 = s7a_markMap hs x.1 := rfl

include hpar in
/-- Cyclic betweenness of persistent marks is carried by the mark map. -/
theorem s7a_between_map (p q r : Mark P) (hp : s7a_Persistent M a p) (hq : s7a_Persistent M a q)
    (hr : s7a_Persistent M a r) :
    traversalBetween (markPosition hn hQ.1 (s7a_markMap hs p)) (markPosition hn hQ.1 (s7a_markMap hs q))
        (markPosition hn hQ.1 (s7a_markMap hs r)) ↔
      traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r) := by
  show ((markKey hn hQ.1 _ < markKey hn hQ.1 _ ∧ markKey hn hQ.1 _ < markKey hn hQ.1 _) ∨
      (markKey hn hQ.1 _ < markKey hn hQ.1 _ ∧ markKey hn hQ.1 _ < markKey hn hQ.1 _) ∨
      (markKey hn hQ.1 _ < markKey hn hQ.1 _ ∧ markKey hn hQ.1 _ < markKey hn hQ.1 _)) ↔
    ((markKey hn hP.1 _ < markKey hn hP.1 _ ∧ markKey hn hP.1 _ < markKey hn hP.1 _) ∨
      (markKey hn hP.1 _ < markKey hn hP.1 _ ∧ markKey hn hP.1 _ < markKey hn hP.1 _) ∨
      (markKey hn hP.1 _ < markKey hn hP.1 _ ∧ markKey hn hP.1 _ < markKey hn hP.1 _))
  rw [s7a_markKey_lt hn hP hQ hs hpar p q hp hq, s7a_markKey_lt hn hP hQ hs hpar q r hq hr,
    s7a_markKey_lt hn hP hQ hs hpar r p hr hp]

variable (S : Finset (Crossing P)) (S' : Finset (Crossing Q))
  (hSS' : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val), (s7a_visit hs v hv).1 ∈ S' ↔ v.1 ∈ S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)

include hpar hSS' hSp hSp' in
/-- The contracted steps are conjugate under the mark map. -/
theorem s7a_step_map (x : s7a_PMark M a P) :
    (s7a_step hn hQ S' (s7a_pmarkEquiv hs x)).1 = s7a_markMap hs (s7a_step hn hP S x).1 := by
  have hP1 := s7a_step_firstAfter hn hP S hSp x
  have hQ1 := s7a_step_firstAfter hn hQ S' hSp' (s7a_pmarkEquiv hs x)
  have hperm : selectedMarkPerm S' (s7a_pmarkEquiv hs x).1 = s7a_markMap hs (selectedMarkPerm S x.1) := by
    rw [s7a_pmarkEquiv_val]
    exact s7a_markMap_selectedMarkPerm hs S S' hSS' x.1 x.2
  have hpp : s7a_Persistent M a (selectedMarkPerm S x.1) := by
    rcases x with ⟨m, hm⟩
    cases m with
    | inl i => trivial
    | inr v =>
      rw [selectedMarkPerm_visit]
      show ¬ ContactAffected M a (selectedVisitTwin S v).1.val
      rw [selectedVisitTwin_crossing]
      exact hm
  rw [hperm] at hQ1
  refine s7a_firstAfter_unique hn hQ _ _ _ (s7a_step hn hQ S' _).2
    (s7a_markMap_persistent hs _ (s7a_step hn hP S x).2) hQ1 ⟨?_, ?_⟩
  · intro h
    exact hP1.1 (s7a_markMap_injOn hs _ _ (s7a_step hn hP S x).2 hpp h)
  · intro z' hz' hz'p hz'y
    obtain ⟨z, hz, rfl⟩ := s7a_markMap_surjOn hs z' hz'
    rw [s7a_between_map hn hP hQ hs hpar _ _ _ hpp (s7a_step hn hP S x).2 hz]
    exact hP1.2 z hz (fun h => hz'p (congrArg _ h)) (fun h => hz'y (congrArg _ h))

include hpar hSS' hSp hSp' in
theorem s7a_stepPerm_map (x : s7a_PMark M a P) :
    s7a_stepPerm hn hQ S' (s7a_pmarkEquiv hs x) = s7a_pmarkEquiv hs (s7a_stepPerm hn hP S x) := by
  apply Subtype.ext
  rw [s7a_stepPerm_apply, s7a_stepPerm_apply, s7a_pmarkEquiv_val]
  exact s7a_step_map hn hP hQ hs hpar S S' hSS' hSp hSp' x

/-- **The carrier correspondence** of a persistent support across the contact wall. -/
def s7a_componentEquiv : Component hn hP S ≃ Component hn hQ S' :=
  (s7a_componentEquivQuot hn hP S hSp).trans
    ((Quotient.congr (s7a_pmarkEquiv hs) (fun x y =>
      (s7a_sameCycle_of_equiv_conj (s7a_stepPerm hn hP S) (s7a_stepPerm hn hQ S') (s7a_pmarkEquiv hs)
        (s7a_stepPerm_map hn hP hQ hs hpar S S' hSS' hSp hSp') x y).symm)).trans
      (s7a_componentEquivQuot hn hQ S' hSp').symm)

/-- The correspondence sends the carrier of a persistent mark to the carrier of its image. -/
theorem s7a_componentEquiv_owner (m : Mark P) (hm : s7a_Persistent M a m) :
    s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' (owner hn hP S m) =
      owner hn hQ S' (s7a_markMap hs m) := by
  unfold s7a_componentEquiv
  rw [Equiv.trans_apply, Equiv.trans_apply, s7a_componentEquivQuot_owner hn hP S hSp m hm,
    Equiv.symm_apply_eq, s7a_componentEquivQuot_owner hn hQ S' hSp' _ (s7a_markMap_persistent hs m hm)]
  rfl

end Conjugation

/-! #### Consequences on the carriers: self-crossings, corner lists, turns, uniformity, interlacement -/

section Carriers

variable {P Q : LabelledTuple n} {M a : ZMod n} (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
  (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (hpar : ∀ (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit hs v hv) < visitParameter (s7a_visit hs w hw) ↔
        visitParameter v < visitParameter w))

omit [NeZero n] in
/-- True corners of a persistent support are persistent marks. -/
theorem s7a_isTrueCorner_persistent {R : LabelledTuple n} (T : Finset (Crossing R))
    (hTp : ∀ x ∈ T, ¬ ContactAffected M a x.val) (m : Mark R) (h : IsTrueCorner T m) :
    s7a_Persistent M a m := by
  cases m with
  | inl i => trivial
  | inr v => exact hTp v.1 h

variable (S : Finset (Crossing P)) (S' : Finset (Crossing Q))
  (hSS' : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val), (s7a_visit hs v hv).1 ∈ S' ↔ v.1 ∈ S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)

omit [NeZero n] in
/-- The transported persistent crossing (same support). -/
def s7a_cross (x : Crossing P) (hx : ¬ ContactAffected M a x.val) : Crossing Q :=
  ⟨x.val, (hs _ hx).mpr x.property⟩

omit [NeZero n] in
theorem s7a_cross_val (x : Crossing P) (hx : ¬ ContactAffected M a x.val) :
    (s7a_cross hs x hx).val = x.val := rfl

omit [NeZero n] in
theorem s7a_visit_fst (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    (s7a_visit hs v hv).1 = s7a_cross hs v.1 hv := rfl

omit [NeZero n] in
theorem s7a_cross_surj (x' : Crossing Q) (hx' : ¬ ContactAffected M a x'.val) :
    ∃ (x : Crossing P) (hx : ¬ ContactAffected M a x.val), s7a_cross hs x hx = x' :=
  ⟨⟨x'.val, (hs _ hx').mp x'.property⟩, hx', rfl⟩

include hSS' in
omit [NeZero n] in
/-- Membership in the transported support. -/
theorem s7a_cross_mem (x : Crossing P) (hx : ¬ ContactAffected M a x.val) :
    s7a_cross hs x hx ∈ S' ↔ x ∈ S := by
  obtain ⟨i, j, hij, _, _⟩ := x.property
  have hi : i ∈ x.val := by rw [hij]; simp
  exact hSS' ⟨x, ⟨i, hi⟩⟩ hx

include hpar hSS' hSp hSp' in
/-- A persistent crossing is a self-crossing of a carrier iff its transport is a self-crossing of the
corresponding carrier. -/
theorem s7a_mem_carrierCrossings (x : Crossing P) (hx : ¬ ContactAffected M a x.val)
    (q : Component hn hP S) :
    s7a_cross hs x hx ∈ carrierCrossings hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q) ↔
      x ∈ carrierCrossings hn hP S q := by
  rw [mem_carrierCrossings_iff_fiber, mem_carrierCrossings_iff_fiber, s7a_cross_mem hs S S' hSS' x hx]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  have hmark : (Sum.inr (⟨s7a_cross hs x hx, i⟩ : Visit Q) : Mark Q) =
      s7a_markMap hs (Sum.inr (⟨x, i⟩ : Visit P)) := by
    rw [s7a_markMap_inr hs _ hx]
    rfl
  rw [hmark, ← s7a_componentEquiv_owner hn hP hQ hs hpar S S' hSS' hSp hSp' (Sum.inr ⟨x, i⟩) hx]
  exact (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp').injective.eq_iff

include hSS' in
theorem s7a_isTrueCorner_map (m : Mark P) (hm : s7a_Persistent M a m) :
    IsTrueCorner S' (s7a_markMap hs m) ↔ IsTrueCorner S m := by
  cases m with
  | inl i => exact Iff.rfl
  | inr v =>
    rw [s7a_markMap_inr hs v hm, isTrueCorner_visit, isTrueCorner_visit]
    exact hSS' v hm

include hpar hSS' hSp hSp' in
/-- **The corner lists correspond literally** (no rotation): the corner list is the filter of the
sorted mark list by ownership and true-cornerhood, both carried by the mark map on persistent marks,
and the sorted persistent sublists agree (`s7a_markList_filter`). -/
theorem s7a_ccpCornerList_map (q : Component hn hP S) :
    ccpCornerList hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q) =
      (ccpCornerList hn hP S q).map (s7a_markMap hs) := by
  set e := s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' with he
  -- both corner lists as single filters
  have hP1 : ccpCornerList hn hP S q = (markList hn hP).filter
      (fun m => decide (IsTrueCorner S m) && decide (owner hn hP S m = q)) := by
    unfold ccpCornerList componentMarkList
    rw [List.filter_filter]
  have hQ1 : ccpCornerList hn hQ S' (e q) = (markList hn hQ).filter
      (fun m => decide (IsTrueCorner S' m) && decide (owner hn hQ S' m = e q)) := by
    unfold ccpCornerList componentMarkList
    rw [List.filter_filter]
  -- restrict `Q`'s filter to the persistent sublist
  have hQ2 : (markList hn hQ).filter
      (fun m => decide (IsTrueCorner S' m) && decide (owner hn hQ S' m = e q)) =
      ((markList hn hQ).filter (fun m => decide (s7a_Persistent M a m))).filter
        (fun m => decide (IsTrueCorner S' m) && decide (owner hn hQ S' m = e q)) := by
    rw [List.filter_filter]
    refine List.filter_congr (fun m _ => ?_)
    by_cases hc : IsTrueCorner S' m
    · simp only [hc, decide_true, Bool.true_and, s7a_isTrueCorner_persistent S' hSp' m hc,
        Bool.and_true]
    · simp only [hc, decide_false, Bool.false_and]
  have hP2 : (markList hn hP).filter
      (fun m => decide (IsTrueCorner S m) && decide (owner hn hP S m = q)) =
      ((markList hn hP).filter (fun m => decide (s7a_Persistent M a m))).filter
        (fun m => decide (IsTrueCorner S m) && decide (owner hn hP S m = q)) := by
    rw [List.filter_filter]
    refine List.filter_congr (fun m _ => ?_)
    by_cases hc : IsTrueCorner S m
    · simp only [hc, decide_true, Bool.true_and, s7a_isTrueCorner_persistent S hSp m hc,
        Bool.and_true]
    · simp only [hc, decide_false, Bool.false_and]
  rw [hQ1, hP1, hQ2, hP2, s7a_markList_filter hn hP hQ hs hpar, List.filter_map]
  congr 1
  refine List.filter_congr (fun m hm => ?_)
  have hmp : s7a_Persistent M a m := by
    rw [List.mem_filter, decide_eq_true_eq] at hm
    exact hm.2
  simp only [Function.comp]
  have h1 : decide (IsTrueCorner S' (s7a_markMap hs m)) = decide (IsTrueCorner S m) :=
    decide_eq_decide.mpr (s7a_isTrueCorner_map hs S S' hSS' m hmp)
  have h2 : decide (owner hn hQ S' (s7a_markMap hs m) = e q) = decide (owner hn hP S m = q) := by
    apply decide_eq_decide.mpr
    rw [← s7a_componentEquiv_owner hn hP hQ hs hpar S S' hSS' hSp hSp' m hmp]
    exact e.injective.eq_iff
  rw [h1, h2]

include hpar hSS' hSp hSp' in
theorem s7a_ccpCornerCount_eq (q : Component hn hP S) :
    ccpCornerCount hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q) =
      ccpCornerCount hn hP S q := by
  unfold ccpCornerCount
  rw [s7a_ccpCornerList_map hn hP hQ hs hpar S S' hSS' hSp hSp' q, List.length_map]

include hpar hSS' hSp hSp' in
/-- The corner marks correspond index by index (through the cast of the equal corner counts). -/
theorem s7a_ccpCornerMark_map (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ccpCornerMark hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q)
        (Equiv.cast (congrArg ZMod (s7a_ccpCornerCount_eq hn hP hQ hs hpar S S' hSS' hSp hSp' q).symm) j) =
      s7a_markMap hs (ccpCornerMark hn hP S q j) := by
  unfold ccpCornerMark
  exact Carrier.MarkTransport.getElem_eq_map_of_eq (s7a_markMap hs) _ _
    (s7a_ccpCornerList_map hn hP hQ hs hpar S S' hSS' hSp hSp' q) _ _
    (zmod_val_cast (s7a_ccpCornerCount_eq hn hP hQ hs hpar S S' hSS' hSp hSp' q).symm j) _ _

omit [NeZero n] in
/-- The turn of a persistent mark is carried when vertex turns and the crossing signs of persistent
crossings are. -/
theorem s7a_markTurn_map (hturn : ∀ i, turn Q i = turn P i)
    (hsgn : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      crossingSign Q (s7a_visit hs v hv).2.val (visitTwin (s7a_visit hs v hv)).2.val =
        crossingSign P v.2.val (visitTwin v).2.val)
    (m : Mark P) (hm : s7a_Persistent M a m) :
    markTurn Q (s7a_markMap hs m) = markTurn P m := by
  cases m with
  | inl i => exact hturn i
  | inr v =>
    rw [s7a_markMap_inr hs v hm, markTurn_inr, markTurn_inr]
    exact hsgn v hm

include hpar hSS' hSp hSp' in
/-- The turns of the corner polygons correspond index by index. -/
theorem s7a_turn_ccpCornerPolygon (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hQ S')
    (hturn : ∀ i, turn Q i = turn P i)
    (hsgn : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      crossingSign Q (s7a_visit hs v hv).2.val (visitTwin (s7a_visit hs v hv)).2.val =
        crossingSign P v.2.val (visitTwin v).2.val)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    turn (ccpCornerPolygon hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q))
        (Equiv.cast (congrArg ZMod (s7a_ccpCornerCount_eq hn hP hQ hs hpar S S' hSS' hSp hSp' q).symm) j) =
      turn (ccpCornerPolygon hn hP S q) j := by
  rw [turn_ccpCornerPolygon_eq_markTurn hn hQ hS', turn_ccpCornerPolygon_eq_markTurn hn hP hS,
    s7a_ccpCornerMark_map hn hP hQ hs hpar S S' hSS' hSp hSp' q j]
  exact s7a_markTurn_map hs hturn hsgn _
    (s7a_isTrueCorner_persistent S hSp _ (ccpCornerMark_mem hn hP S q j).2)

include hpar hSS' hSp hSp' in
/-- **Uniformity is carried** across the contact wall for corresponding carriers. -/
theorem s7a_carrierUniform_iff (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hQ S')
    (hturn : ∀ i, turn Q i = turn P i)
    (hsgn : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      crossingSign Q (s7a_visit hs v hv).2.val (visitTwin (s7a_visit hs v hv)).2.val =
        crossingSign P v.2.val (visitTwin v).2.val)
    (q : Component hn hP S) :
    CarrierUniform hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q) ↔
      CarrierUniform hn hP S q := by
  unfold CarrierUniform
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h j
    rw [← s7a_turn_ccpCornerPolygon hn hP hQ hs hpar S S' hSS' hSp hSp' hS hS' hturn hsgn q j]
    exact h _
  · intro h j'
    obtain ⟨j, rfl⟩ := (Equiv.cast (congrArg ZMod
      (s7a_ccpCornerCount_eq hn hP hQ hs hpar S S' hSS' hSp hSp' q).symm)).surjective j'
    rw [s7a_turn_ccpCornerPolygon hn hP hQ hs hpar S S' hSS' hSp hSp' hS hS' hturn hsgn q j]
    exact h j

include hpar in
/-- Interlacement of persistent crossings is carried (all four visits are persistent; cyclic order of
persistent marks is carried, `s7a_between_map`). -/
theorem s7a_interlaces_iff (x y : Crossing P) (hx : ¬ ContactAffected M a x.val)
    (hy : ¬ ContactAffected M a y.val) :
    Interlaces hn hQ (s7a_cross hs x hx) (s7a_cross hs y hy) ↔ Interlaces hn hP x y := by
  have hne : s7a_cross hs x hx ≠ s7a_cross hs y hy ↔ x ≠ y := by
    constructor
    · intro h hxy; exact h (by subst hxy; rfl)
    · intro h h'
      have hv := congrArg Subtype.val h'
      exact h (Subtype.ext hv)
  have hbet : ∀ (x₀ x₁ : {i // i ∈ x.val}) (y₀ : {i // i ∈ y.val}),
      crossingVisitBetween hn hQ.1 (s7a_cross hs x hx) x₀ x₁ (s7a_cross hs y hy) y₀ ↔
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ := by
    intro x₀ x₁ y₀
    have h1 : (Sum.inr (⟨s7a_cross hs x hx, x₀⟩ : Visit Q) : Mark Q) =
        s7a_markMap hs (Sum.inr (⟨x, x₀⟩ : Visit P)) := by rw [s7a_markMap_inr hs _ hx]; rfl
    have h2 : (Sum.inr (⟨s7a_cross hs x hx, x₁⟩ : Visit Q) : Mark Q) =
        s7a_markMap hs (Sum.inr (⟨x, x₁⟩ : Visit P)) := by rw [s7a_markMap_inr hs _ hx]; rfl
    have h3 : (Sum.inr (⟨s7a_cross hs y hy, y₀⟩ : Visit Q) : Mark Q) =
        s7a_markMap hs (Sum.inr (⟨y, y₀⟩ : Visit P)) := by rw [s7a_markMap_inr hs _ hy]; rfl
    change traversalBetween (markPosition hn hQ.1 (Sum.inr ⟨s7a_cross hs x hx, x₀⟩))
      (markPosition hn hQ.1 (Sum.inr ⟨s7a_cross hs y hy, y₀⟩))
      (markPosition hn hQ.1 (Sum.inr ⟨s7a_cross hs x hx, x₁⟩)) ↔
      traversalBetween (markPosition hn hP.1 (Sum.inr ⟨x, x₀⟩)) (markPosition hn hP.1 (Sum.inr ⟨y, y₀⟩))
        (markPosition hn hP.1 (Sum.inr ⟨x, x₁⟩))
    rw [h1, h2, h3]
    exact s7a_between_map hn hP hQ hs hpar _ _ _ hx hy hx
  unfold Interlaces
  rw [hne]
  refine and_congr Iff.rfl ?_
  refine exists_congr fun x₀ => exists_congr fun x₁ => exists_congr fun y₀ => exists_congr fun y₁ => ?_
  rw [hbet x₀ x₁ y₀, hbet x₁ x₀ y₁]
  exact Iff.rfl

include hpar hSS' hSp hSp' in
/-- **Decompositions correspond**: a persistent support is independent iff its transport is. -/
theorem s7a_isDecomposition_iff : IsDecomposition hn hQ S' ↔ IsDecomposition hn hP S := by
  unfold IsDecomposition
  rw [mem_independentSupports_iff, mem_independentSupports_iff]
  constructor
  · intro h x hx y hy hxy hI
    exact h _ ((s7a_cross_mem hs S S' hSS' x (hSp x hx)).mpr hx) _
      ((s7a_cross_mem hs S S' hSS' y (hSp y hy)).mpr hy)
      (fun he => hxy (by have hv := congrArg Subtype.val he; exact Subtype.ext hv))
      ((s7a_interlaces_iff hn hP hQ hs hpar x y (hSp x hx) (hSp y hy)).mpr hI)
  · intro h x' hx' y' hy' hxy hI
    obtain ⟨x, hx, rfl⟩ := s7a_cross_surj hs x' (hSp' x' hx')
    obtain ⟨y, hy, rfl⟩ := s7a_cross_surj hs y' (hSp' y' hy')
    exact h x ((s7a_cross_mem hs S S' hSS' x hx).mp hx') y ((s7a_cross_mem hs S S' hSS' y hy).mp hy')
      (fun he => hxy (by subst he; rfl)) ((s7a_interlaces_iff hn hP hQ hs hpar x y hx hy).mp hI)

end Carriers

/-! #### Instantiation at a simple vertex–edge wall: the two sides at one parameter -/

section Germ

variable (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)

/-- The accepted local data of lem:wall-sides (V) (`VertexLocalData`, SM/VertexSides.lean) at BOTH
sides of the side parameter `t`, relative to the centre. -/
def s7a_SideLocal (r η : ℝ) (t : g.SideParameter) : Prop :=
  ∀ b : Bool, VertexLocalData hn g.center (g.curve (g.sideTime b t)) M a r η

/-- lem:wall-sides (V) (`vertex_sides`) supplies the contact parameter `r`, the window half-width `η`
and a radius `δ` below which both sides carry the local data. -/
theorem s7a_exists_sideLocal (h : g.VertexEdgeAt M a) :
    ∃ r η : ℝ, 0 < r ∧ r < 1 ∧ g.center M = edgePoint g.center a r ∧
      0 < η ∧ 4 * η < r ∧ 4 * η < 1 - r ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
        s7a_SideLocal hn g M a r η t := by
  obtain ⟨-, -, -, -, r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, hδr, hloc⟩ := vertex_sides hn g h
  refine ⟨r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, hδr, fun t ht b => ?_⟩
  exact hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)

variable {M a} {r η : ℝ} {t : g.SideParameter}

omit [NeZero n] in
/-- Genericity of a side point, written on `g.curve (g.sideTime b t)`. -/
theorem s7a_sideGeneric (b : Bool) : Generic (g.curve (g.sideTime b t)) :=
  g.generic_punctured _ (g.sideTime_ne_zero b t)

/-- (1) Persistent crossings agree between any two sides (both agree with the centre's):
the crossing hypothesis of the transport from side `b` to side `b'`. -/
theorem s7a_side_hs (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool) :
    ∀ s, ¬ ContactAffected M a s →
      (IsCrossing (g.curve (g.sideTime b' t)) s ↔ IsCrossing (g.curve (g.sideTime b t)) s) :=
  fun s hs => ((hL b').windows.1 s hs).trans ((hL b).windows.1 s hs).symm

/-- (2) The same-edge parameter order of persistent visits agrees between the two sides
(`VertexLocalData.visit_order` on both sides, composed through the centre): the parameter hypothesis
`hpar` of the transport from side `b` to side `b'`. -/
theorem s7a_side_hpar (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool) :
    ∀ (v w : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit (s7a_side_hs hn g hL b b') v hv) <
          visitParameter (s7a_visit (s7a_side_hs hn g hL b b') w hw) ↔
        visitParameter v < visitParameter w) := by
  intro v w hv hw he
  set hb := (hL b).windows.1
  set hb' := (hL b').windows.1
  let v₀ : PersistentContactVisit g.center M a := (contactVisitTransport hb).symm ⟨v, hv⟩
  let w₀ : PersistentContactVisit g.center M a := (contactVisitTransport hb).symm ⟨w, hw⟩
  have hv₀ : contactVisitTransport hb v₀ = ⟨v, hv⟩ := Equiv.apply_symm_apply _ _
  have hw₀ : contactVisitTransport hb w₀ = ⟨w, hw⟩ := Equiv.apply_symm_apply _ _
  have hedge : v₀.val.2.val = w₀.val.2.val := he
  have h1 := (hL b').visit_order (s7a_sideGeneric g b').1 v₀ w₀ hedge
  have h2 := (hL b).visit_order (s7a_sideGeneric g b).1 v₀ w₀ hedge
  rw [hv₀, hw₀] at h2
  have hv' : s7a_visit (s7a_side_hs hn g hL b b') v hv = (contactVisitTransport hb' v₀).val := rfl
  have hw' : s7a_visit (s7a_side_hs hn g hL b b') w hw = (contactVisitTransport hb' w₀).val := rfl
  rw [hv', hw', h1]
  exact h2.symm

/-- (3) Vertex turns agree between the two sides: the turn triple `{i−1, i, i+1}` is never the
contact support (`contactSupport_ne_turnSupport`), so `ChirotopesOutsideZerosAgree` applies. -/
theorem s7a_side_turn (h : g.VertexEdgeAt M a) (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool)
    (i : ZMod n) : turn (g.curve (g.sideTime b' t)) i = turn (g.curve (g.sideTime b t)) i := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have h1 : i - 1 ≠ i := prev_ne_self i
  have h2 : i ≠ i + 1 := (next_ne_self i).symm
  have h3 : i - 1 ≠ i + 1 := prev_ne_next hn i
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.2.1
  have hnot : ({i - 1, i, i + 1} : Finset (ZMod n)) ∉ pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    exact fun he => contactSupport_ne_turnSupport hn h.1 i he.symm
  have hb := ((hL b).chirotopes (i - 1) i (i + 1) h1 h2 h3 hnot).1
  have hb' := ((hL b').chirotopes (i - 1) i (i + 1) h1 h2 h3 hnot).1
  unfold turn
  rw [hb, hb']

omit [NeZero n] in
include hn in
/-- The crossing sign of a crossing `{i, j}` of a `G1` polygon is the chirotope `χ_{i,i+1,j+1}`
(the two endpoints of `E_j` lie on opposite sides of the line of `E_i`, `crossing_test`). -/
theorem s7a_crossingSign_eq_chi {P : LabelledTuple n} (hP : G1 P) {i j : ZMod n}
    (hc : IsCrossing P {i, j}) : crossingSign P i j = chi P i (i + 1) (j + 1) := by
  have hr := crossing_pair_remote hc
  have ht := ((crossing_test hn P hP).1 i j hr).mp hc
  have hprod : det (edge P i) (P j - P i) * det (edge P i) (P (j + 1) - P i) < 0 := by
    have := ht.1
    rw [chi_edge, chi_edge, sign_product_neg_iff] at this
    exact this
  have hdet : det (edge P i) (edge P j) =
      det (edge P i) (P (j + 1) - P i) - det (edge P i) (P j - P i) := by
    simp [edge, det]; ring
  unfold crossingSign
  rw [chi_edge, hdet]
  rcases mul_neg_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sign_neg h2, sign_neg (by linarith)]
  · rw [sign_pos h2, sign_pos (by linarith)]

/-- (4) Crossing signs of persistent crossings agree between the two sides: the sign is the
chirotope `χ_{e,e+1,f+1}`, whose triple is not the contact support for an unaffected pair, so
`ChirotopesOutsideZerosAgree` applies — the over-bit hypothesis `hsgn` of the transport. -/
theorem s7a_side_sgn (h : g.VertexEdgeAt M a) (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool) :
    ∀ (v : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val),
      crossingSign (g.curve (g.sideTime b' t)) (s7a_visit (s7a_side_hs hn g hL b b') v hv).2.val
          (visitTwin (s7a_visit (s7a_side_hs hn g hL b b') v hv)).2.val =
        crossingSign (g.curve (g.sideTime b t)) v.2.val (visitTwin v).2.val := by
  intro v hv
  have hpair : v.1.val = {v.2.val, (visitTwin v).2.val} := visit_crossing_val_eq_pair v
  have hcb : IsCrossing (g.curve (g.sideTime b t)) {v.2.val, (visitTwin v).2.val} :=
    hpair ▸ v.1.property
  have hnot : ¬ ContactAffected M a {v.2.val, (visitTwin v).2.val} := hpair ▸ hv
  have hcb' : IsCrossing (g.curve (g.sideTime b' t)) {v.2.val, (visitTwin v).2.val} :=
    (s7a_side_hs hn g hL b b' _ hnot).mpr hcb
  have hedge2 : (visitTwin (s7a_visit (s7a_side_hs hn g hL b b') v hv)).2.val = (visitTwin v).2.val := by
    rw [← s7a_visit_twin]
    rfl
  rw [hedge2]
  show crossingSign (g.curve (g.sideTime b' t)) v.2.val (visitTwin v).2.val = _
  rw [s7a_crossingSign_eq_chi hn (s7a_sideGeneric g b').1 hcb',
    s7a_crossingSign_eq_chi hn (s7a_sideGeneric g b).1 hcb]
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints _ _ (crossing_pair_remote hcb)
  have h1 : v.2.val ≠ v.2.val + 1 := (next_ne_self _).symm
  have h2 : v.2.val + 1 ≠ (visitTwin v).2.val + 1 := hf1e1.symm
  have h3 : v.2.val ≠ (visitTwin v).2.val + 1 := hf1e.symm
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.2.1
  have hnotz : ({v.2.val, v.2.val + 1, (visitTwin v).2.val + 1} : Finset (ZMod n)) ∉
      pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    intro heq
    have hea : v.2.val = a := contactSupport_successive hn h.1 (by rw [← heq]; simp) (by rw [← heq]; simp)
    have hf1 : (visitTwin v).2.val + 1 ∈ contactSupport M a := by rw [← heq]; simp
    simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hf1
    rcases hf1 with hf1 | hf1 | hf1
    · exact h3 (by rw [hea, hf1])
    · exact hfe (by rw [add_right_cancel hf1, hea])
    · apply hnot
      left
      rw [hea, eq_sub_of_add_eq hf1]
  have hcb1 := ((hL b).chirotopes _ _ _ h1 h2 h3 hnotz).1
  have hcb1' := ((hL b').chirotopes _ _ _ h1 h2 h3 hnotz).1
  rw [hcb1, hcb1']

omit [NeZero n] in
/-- In `SignType`, `s * t = -1` forces `s = -t`. -/
theorem s7a_signType_mul_eq_neg_one {s t : SignType} (h : s * t = -1) : s = -t := by
  cases s <;> cases t <;> first | rfl | exact absurd h (by decide)

/-- (5) **The sliding relocation sign.** When side `b` carries the contact crossing `{a, M−1}` and
side `b'` carries `{a, M}` (the sliding pattern), the crossing signs of the two contact crossings
agree: `sgn det(E_a, E_M)` on side `b'` equals `sgn det(E_a, E_{M−1})` on side `b`.  Inputs: the contact
test of side `b` (`WallGerm.vertexEdge_contact_tests`, at the side time of `t`), the sliding
alternation `χ_{a,a+1,M−1}(C) ≠ χ_{a,a+1,M+1}(C)`, and chirotope persistence at `{a, a+1, M+1}`.
This is the over-bit input for the relocated visit `x₋ ↦ x₊` (U110-D note 1). -/
theorem s7a_sliding_relocation_sign (h : g.SlidingAt M a) (hL : s7a_SideLocal hn g M a r η t)
    (b b' : Bool) (hb : IsCrossing (g.curve (g.sideTime b t)) {a, M - 1})
    (hb' : IsCrossing (g.curve (g.sideTime b' t)) {a, M})
    (htest : ∀ forward : Bool, IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg forward M} ↔
      chi (g.curve (g.sideTime b t)) a (a + 1) M *
        chi g.center a (a + 1) (contactNeighbour forward M) = -1) :
    crossingSign (g.curve (g.sideTime b' t)) a M = crossingSign (g.curve (g.sideTime b t)) a (M - 1) := by
  have hsep : ContactSeparated M a := h.1.1
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  -- side `b`: `sgn det(E_a, E_{M−1}) = χ_{a,a+1,M}(P_b) = −χ_{a,a+1,M−1}(C)`
  have h1 : crossingSign (g.curve (g.sideTime b t)) a (M - 1) =
      chi (g.curve (g.sideTime b t)) a (a + 1) M := by
    rw [s7a_crossingSign_eq_chi hn (s7a_sideGeneric g b).1 hb, sub_add_cancel]
  have htb := (htest false).mp (by simpa [contactLeg] using hb)
  simp only [contactNeighbour, Bool.false_eq_true, ↓reduceIte] at htb
  have h2 : chi (g.curve (g.sideTime b t)) a (a + 1) M = -chi g.center a (a + 1) (M - 1) :=
    s7a_signType_mul_eq_neg_one htb
  -- side `b'`: `sgn det(E_a, E_M) = χ_{a,a+1,M+1}(P_{b'}) = χ_{a,a+1,M+1}(C)`
  have h3 : crossingSign (g.curve (g.sideTime b' t)) a M =
      chi (g.curve (g.sideTime b' t)) a (a + 1) (M + 1) :=
    s7a_crossingSign_eq_chi hn (s7a_sideGeneric g b').1 hb'
  have hd1 : a ≠ a + 1 := (next_ne_self a).symm
  have hd2 : a + 1 ≠ M + 1 := fun he => hsep.2.1 (add_right_cancel he).symm
  have hd3 : a ≠ M + 1 := fun he => hsep.1 (by rw [he]; ring)
  have hnotz : ({a, a + 1, M + 1} : Finset (ZMod n)) ∉ pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    intro heq
    have hm : M + 1 ∈ contactSupport M a := by rw [← heq]; simp
    simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact hd3 hm.symm
    · exact hd2 hm.symm
    · exact (next_ne_self M) hm
  have h4 := ((hL b').chirotopes a (a + 1) (M + 1) hd1 hd2 hd3 hnotz).1
  -- the sliding alternation: `χ_{M+1}(C) = −χ_{M−1}(C)`
  have hne0 : chi g.center a (a + 1) (M - 1) ≠ 0 := by
    have := contactNeighbour_chi_nonzero hn hsep hz false
    simpa [contactNeighbour] using this
  have hne1 : chi g.center a (a + 1) (M + 1) ≠ 0 := by
    have := contactNeighbour_chi_nonzero hn hsep hz true
    simpa [contactNeighbour] using this
  have hneg0 : -chi g.center a (a + 1) (M - 1) ≠ 0 := by
    rcases signType_nonzero_cases hne0 with hh | hh <;> rw [hh] <;> decide
  have h5 : chi g.center a (a + 1) (M + 1) = -chi g.center a (a + 1) (M - 1) := by
    rw [signType_eq_iff_ne_neg hne1 hneg0, neg_neg]
    exact fun he => h.2 he.symm
  rw [h3, h4, h5, h1, h2]

/-! #### Convenience instantiations at the wall (how the consumers plug the pieces together) -/

variable (h : g.VertexEdgeAt M a) (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool)
  (S : Finset (Crossing (g.curve (g.sideTime b t)))) (S' : Finset (Crossing (g.curve (g.sideTime b' t))))
  (hSS' : ∀ (v : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val),
    (s7a_visit (s7a_side_hs hn g hL b b') v hv).1 ∈ S' ↔ v.1 ∈ S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)

include hL hSS' hSp hSp' in
/-- The carrier correspondence between the two sides for a persistent support. -/
def s7a_sideComponentEquiv :
    Component hn (s7a_sideGeneric g b) S ≃ Component hn (s7a_sideGeneric g b') S' :=
  s7a_componentEquiv hn (s7a_sideGeneric g b) (s7a_sideGeneric g b') (s7a_side_hs hn g hL b b')
    (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp'

theorem s7a_sideComponentEquiv_owner (m : Mark (g.curve (g.sideTime b t)))
    (hm : s7a_Persistent M a m) :
    s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' (owner hn (s7a_sideGeneric g b) S m) =
      owner hn (s7a_sideGeneric g b') S' (s7a_markMap (s7a_side_hs hn g hL b b') m) :=
  s7a_componentEquiv_owner hn _ _ _ _ S S' hSS' hSp hSp' m hm

include hL hSS' hSp hSp' in
/-- Decompositions correspond between the two sides. -/
theorem s7a_side_isDecomposition_iff :
    IsDecomposition hn (s7a_sideGeneric g b') S' ↔ IsDecomposition hn (s7a_sideGeneric g b) S :=
  s7a_isDecomposition_iff hn _ _ (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp'

include h in
/-- Uniformity corresponds between the two sides. -/
theorem s7a_side_carrierUniform_iff (hS : IsDecomposition hn (s7a_sideGeneric g b) S)
    (hS' : IsDecomposition hn (s7a_sideGeneric g b') S') (q : Component hn (s7a_sideGeneric g b) S) :
    CarrierUniform hn (s7a_sideGeneric g b') S' (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q) ↔
      CarrierUniform hn (s7a_sideGeneric g b) S q :=
  s7a_carrierUniform_iff hn _ _ (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp'
    hS hS' (s7a_side_turn hn g h hL b b') (s7a_side_sgn hn g h hL b b') q

/-- Self-crossings correspond for persistent crossings. -/
theorem s7a_side_mem_carrierCrossings (x : Crossing (g.curve (g.sideTime b t)))
    (hx : ¬ ContactAffected M a x.val) (q : Component hn (s7a_sideGeneric g b) S) :
    s7a_cross (s7a_side_hs hn g hL b b') x hx ∈
        carrierCrossings hn (s7a_sideGeneric g b') S' (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q) ↔
      x ∈ carrierCrossings hn (s7a_sideGeneric g b) S q :=
  s7a_mem_carrierCrossings hn _ _ (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' x hx q

end Germ

/-- The sliding branch (sm-4:300-406): relocation bijection `φ(x₋) = x₊`, the support bijection
eq. s7c:sliding-bijection with the halves, equal coefficient products eq. s7c:sliding-coefficients, and
the exact selector difference eq. s7c:sliding-selector-difference.  NO floor, NO singleton. -/
theorem s7_sliding_law_at (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry

/-- The bigon branch (sm-4:407-874): two-newborn sector `B = (1−ε)J` (contact triangle: a crossing-free
uniform carrier, `corner_values_i`), universal skein extraction eq. s7c:universal-extraction (lp:core
skein, R-II deletion, oriented smoothing), lem:homflyrows two-component row, the rotation ledger, and the
two floor-dependent branches (interlacing: `Ω_H − Ω_L = −ω₁ω₂`; noninterlacing: every returned row zero,
the one-newborn rows by cb:singleton).  `a_floor` enters at the two half contact carriers (uniform for
`ε = 1`, one-dissent for `ε = 0`), read as carriers of the decompositions `T_i` of the generic halves
`λ_i` (sm-4:800-835); cb:singleton enters at the one-newborn rows (sm-4:777-783) — both printed
dependencies are explicit parameters. -/
theorem s7_bigon_law_at (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (g : WallGerm n) (M a : ZMod n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry

/-! Two pure-algebra leaves of the bigon branch, stated now on the accepted ring (units U110-G / U110-J). -/

/-- eq. s7c:universal-extraction: from `F_H = a⁻² F_L + a⁻¹ z F_A` (the skein relation at the positive
contact crossing, `lp_core.skein`), `[a^{k−2} z⁰] F_H = [a^k z⁰] F_L + [a^{k−1} z⁻¹] F_A`. -/
theorem s7_universal_extraction (FH FL FA : R) (k : ℤ)
    (hsk : FH = R.aInv * R.aInv * FL + R.aInv * R.z * FA) :
    coeffAt (k - 2) 0 FH = coeffAt k 0 FL + coeffAt (k - 1) (-1) FA := by
  sorry

/-- eq. s7c:interlacing-coefficient-result, the algebra: if `f, g ≠ 0` have `a`-floors `k₁, k₂` and no
negative `z`-exponents (`a_floor` and lp:core's `knot_support` at the two half contact carriers), then
`[a^{k₁+k₂−2} z⁰](fg) = 0` and `[a^{k₁+k₂} z⁰](fg) = [a^{k₁} z⁰]f · [a^{k₂} z⁰]g`. -/
theorem s7_corner_product {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) {k₁ k₂ : ℤ}
    (h₁ : k₁ ≤ mindegAZ f) (h₂ : k₂ ≤ mindegAZ g)
    (hz₁ : ∀ d k, coeffAt d k f ≠ 0 → 0 ≤ k) (hz₂ : ∀ d k, coeffAt d k g ≠ 0 → 0 ≤ k) :
    coeffAt (k₁ + k₂ - 2) 0 (f * g) = 0 ∧
      coeffAt (k₁ + k₂) 0 (f * g) = coeffAt k₁ 0 f * coeffAt k₂ 0 g := by
  refine ⟨coeffAt_mul_eq_zero_of_lt_floor hf hg h₁ h₂ (by omega), ?_⟩
  sorry

/-- **Row 110, conditional on thm:floor AND cb:singleton** (the printed dependency list of
tools/claims.py; library material).  PROVED from the two branch leaves: the wall is of bigon or sliding
type (`vertexEdge_bigon_or_sliding`); both side parameters are moved below the branch radius by chamber
constancy along each side (`cornerStateSum_side_eq`). -/
theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data := by
  refine ⟨?_⟩
  intro n _ hn g M a h h₁ h₂ tp tm
  obtain ⟨δ, hδ, hlaw⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂) := by
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact s7_bigon_law_at hF hsing hn g M a hb h₁ h₂
    · exact s7_sliding_law_at hn g M a hs h₁ h₂
  have hr := g.radius_pos
  let t : g.SideParameter := ⟨min δ g.radius / 2, by
    constructor
    · have := lt_min hδ hr; linarith
    · have := min_le_right δ g.radius; linarith⟩
  have ht : t.val < δ := by
    show min δ g.radius / 2 < δ
    have := min_le_left δ g.radius; linarith
  rw [cornerStateSum_side_eq hn g true tp t, cornerStateSum_side_eq hn g false tm t]
  exact hlaw t ht

/-- **Row 110, conditional on the floor alone** (the row theorem `SM.thm_C_S7 := thm_C_S7_of_floor
SM.thm_floor` once row 100 lands). -/
theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=
  thm_C_S7_of hF (cb_singleton_of_floor hF)

end VertexEdge

/-! ## §5 Row 112 thm:C-soft (sm-4:984-991; proof 992-1147) — fixed target name `SM.thm_C_soft` -/

section Soft

open SoftDuplication

variable {n : ℕ} [NeZero n]

/-- **thm:C-soft as printed**, one field: "Let `P` be generic, `j` a vertex, `q` admissible, and `P_ε` the
soft insertion of def:soft, with attachment signs `χ_±`. Then for all sufficiently small `ε > 0`,
`C(P_ε) = ((χ₋ + χ₊)/2) C(P)`."  Shape of the consumer thm:uniqueness (e) (`UniquenessHypotheses.soft`,
SM/Uniqueness.lean:72): `SoftAdmissible P j q` (def:soft), `softInsertion P j q ε = P_ε`, the multiplier
`softAmplitudeMultiplier P j q = (χ₋ + χ₊)/2 ∈ ℚ` (SoftAmplitudeSectors.lean:96, def:soft's
`softAttachmentMinus/Plus`; FR-CC-11), the ℤ-valued `C` cast to `ℚ`; "for all sufficiently small `ε > 0`"
= `∃ ε₁ > 0, ∀ ε ∈ (0, ε₁)`; `C(P_ε)` presupposes `P_ε` generic (lem:soft-generic (i)), quantified as
`∀ hQ` (FR-CC-12; the `∃ hQ` form of the accepted thm:A-soft is the companion `exists_generic`). -/
structure CSoftData : Prop where
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
        softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)

/-- Companion (the accepted thm:A-soft's shape, `A_lawful.soft_theorem`): genericity of `P_ε` as part of
the conclusion, from lem:soft-generic (i) (`soft_family_generic`, SoftGenericLemma.lean:36). -/
theorem CSoftData.exists_generic (hD : CSoftData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
  obtain ⟨ε₁, hε₁, hall⟩ := hD.soft_theorem n hn P hP j q hq
  obtain ⟨δ, hδ, B, hgen⟩ := (soft_family_generic hn hP j q hq).2.2.2.2.2
  refine ⟨min ε₁ δ, lt_min hε₁ hδ, fun ε hε hlt => ?_⟩
  obtain ⟨hQ, -⟩ := hgen ε hε (lt_of_lt_of_le hlt (min_le_right _ _))
  exact ⟨hQ, hall ε hε (lt_of_lt_of_le hlt (min_le_left _ _)) hQ⟩

/-- Companion (the printed proof's three sector multipliers, sm-4:1123-1127): in `ℤ`,
`2 C(P_ε) = (χ₋ + χ₊) C(P)`. -/
theorem CSoftData.doubled (hD : CSoftData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      2 * cornerStateSum (by omega : 3 ≤ n + 1) hQ =
        ((softAttachmentMinus P j q : ℤ) + (softAttachmentPlus P j q : ℤ)) * cornerStateSum hn hP := by
  obtain ⟨ε₁, hε₁, hall⟩ := hD.soft_theorem n hn P hP j q hq
  refine ⟨ε₁, hε₁, fun ε hε hε' hQ => ?_⟩
  have heq := hall ε hε hε' hQ
  have h2 : (2 : ℚ) * (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
      (((softAttachmentMinus P j q : ℤ) : ℚ) + ((softAttachmentPlus P j q : ℤ) : ℚ)) *
        (cornerStateSum hn hP : ℚ) := by
    rw [heq, softAmplitudeMultiplier]; ring
  exact_mod_cast h2

/-! ### Leaves of row 112 (the three printed sectors; units U112-A … U112-D). Prefix `sft_`. -/

omit [NeZero n] in
/-- The turn at a vertex of a generic polygon is nonzero (def:generic (G1) at the triple `(j−1, j, j+1)`,
distinct for `n ≥ 3`); needed to name the sectors. -/
theorem sft_turn_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) :
    turn P j ≠ 0 := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    intro h
    have hd : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd one_pos hd
    omega
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos hd
    omega
  apply hP.1 (j - 1) j (j + 1)
  · intro h; apply h1; linear_combination -h
  · intro h; apply h1; linear_combination -h
  · intro h; apply h2; linear_combination -h

/-- Same-sign sector `χ₋ = χ₊ = −τ` (sm-4:1024-1057): same Gauss word (lem:soft-generic (iv)), carriers
correspond by contracting the inserted vertex, the carrier through `M` gains one corner of the same sign,
rotations equal (angle addition + integrality), coefficients equal (record / planar isotopy of the positive
lifts), `ℓ(P_ε) = ℓ(P) + [τ = 1]`: `C(P_ε) = −τ C(P)`.  NO floor. -/
theorem sft_same_sign (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q)
    (hs : softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      cornerStateSum (by omega : 3 ≤ n + 1) hQ = -((turn P j : ℤ) * cornerStateSum hn hP) := by
  sorry

/-- Mixed sector `χ₋ ≠ χ₊` (sm-4:1059-1065): the soft edge carries no crossing (lem:soft-generic (i)), so
`M, M_ε` are consecutive corners of one carrier with opposite turns — no uniform decomposition (the
thm:C-S5 argument, `Carrier.markSuccessor_vertex_of_no_crossing`, CS5.lean:30): `C(P_ε) = 0`.  NO floor. -/
theorem sft_mixed (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q) (hmix : softAttachmentMinus P j q ≠ softAttachmentPlus P j q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      cornerStateSum (by omega : 3 ≤ n + 1) hQ = 0 := by
  sorry

/-- Loop sector `χ₋ = χ₊ = τ` (sm-4:1067-1143): the newborn `y` is isolated; supports omitting `y`
contribute `0` by lem:corner-values (ii) (HERE row 105 (ii), hence the floor, enters); for `S ∪ {y}` the
triangle `(b, M, M_ε)` has coefficient `1` by lem:corner-values (i) and the residual carriers correspond to
those of `S` with `M` replaced by the smoothing corner `y` of the same sign; sign bookkeeping gives
`C(P_ε) = τ C(P)`. -/
theorem sft_loop (hCV : CornerValuesData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (hl : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      cornerStateSum (by omega : 3 ≤ n + 1) hQ = (turn P j : ℤ) * cornerStateSum hn hP := by
  sorry

/-! ### Assembly of row 112 (PROVED from the three sector leaves): the attachment signs are `±1`
(admissibility), `τ = ±1` (genericity), and the three sectors exhaust the sign patterns with the
multipliers `−τ`, `0`, `τ` — "The three sector multipliers are exactly `(χ₋ + χ₊)/2`". -/

theorem sft_signType_neg_ne_zero {σ : SignType} (h : σ ≠ 0) : -σ ≠ 0 := by
  revert h; cases σ <;> decide

omit [NeZero n] in
theorem sft_attachment_ne_zero {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) :
    softAttachmentMinus P j q ≠ 0 ∧ softAttachmentPlus P j q ≠ 0 := by
  unfold softAttachmentMinus softAttachmentPlus
  exact ⟨sft_signType_neg_ne_zero (sign_ne_zero.mpr hq.1),
    sft_signType_neg_ne_zero (sign_ne_zero.mpr hq.2.1)⟩

theorem sft_signType_cases {σ : SignType} (h : σ ≠ 0) : σ = 1 ∨ σ = -1 := by
  rcases SignType.trichotomy σ with h1 | h1 | h1
  · exact Or.inr h1
  · exact absurd h1 h
  · exact Or.inl h1

/-- **Row 112 from row 105** (the printed dependency: thm:C-soft ← lem:corner-values). -/
theorem thm_C_soft_of_cornerValues (hCV : CornerValuesData) : CSoftData := by
  refine ⟨?_⟩
  intro n _ hn P hP j q hq
  have hτ := sft_signType_cases (sft_turn_ne_zero hn hP j)
  have hχm := sft_signType_cases (sft_attachment_ne_zero hq).1
  have hχp := sft_signType_cases (sft_attachment_ne_zero hq).2
  -- the same-sign, mixed and loop sectors, with their multipliers
  have hsame : softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
    intro hs
    obtain ⟨ε₁, hε₁, hval⟩ := sft_same_sign hn hP j q hq hs
    refine ⟨ε₁, hε₁, fun ε hε0 hε1 hQ => ?_⟩
    rw [hval ε hε0 hε1 hQ]
    unfold softAmplitudeMultiplier
    rw [hs.1, hs.2]
    push_cast
    ring
  have hmixed : softAttachmentMinus P j q ≠ softAttachmentPlus P j q →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
    intro hne
    obtain ⟨ε₁, hε₁, hval⟩ := sft_mixed hn hP j q hq hne
    refine ⟨ε₁, hε₁, fun ε hε0 hε1 hQ => ?_⟩
    rw [hval ε hε0 hε1 hQ]
    unfold softAmplitudeMultiplier
    rcases hχm with hm | hm <;> rcases hχp with hp | hp
    · exact absurd (hm.trans hp.symm) hne
    · rw [hm, hp]; norm_num
    · rw [hm, hp]; norm_num
    · exact absurd (hm.trans hp.symm) hne
  have hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
    intro hl
    obtain ⟨ε₁, hε₁, hval⟩ := sft_loop hCV hn hP j q hq hl
    refine ⟨ε₁, hε₁, fun ε hε0 hε1 hQ => ?_⟩
    rw [hval ε hε0 hε1 hQ]
    unfold softAmplitudeMultiplier
    rw [hl.1, hl.2]
    push_cast
    ring
  -- the sectors exhaust the sign patterns
  by_cases hne : softAttachmentMinus P j q = softAttachmentPlus P j q
  · rcases hτ with ht | ht <;> rcases hχm with hm | hm
    · exact hloop ⟨hm.trans ht.symm, (hne.symm.trans hm).trans ht.symm⟩
    · exact hsame ⟨by rw [hm, ht]; try decide, by rw [← hne, hm, ht]; try decide⟩
    · exact hsame ⟨by rw [hm, ht]; try decide, by rw [← hne, hm, ht]; try decide⟩
    · exact hloop ⟨hm.trans ht.symm, (hne.symm.trans hm).trans ht.symm⟩
  · exact hmixed hne

/-- **Row 112, conditional on the floor** (library material; the row theorem `SM.thm_C_soft :=
thm_C_soft_of_floor SM.thm_floor` once row 100 lands). -/
theorem thm_C_soft_of_floor (hF : FloorTheoremData) : CSoftData :=
  thm_C_soft_of_cornerValues (corner_values_of_floor hF)

end Soft

/-! ## §6 The row theorems (UNCONDITIONAL statements; `sorry` until row 100 lands).  Once the floor lane's
`SM.thm_floor : FloorTheoremData` is accepted, each body is the one-liner named in its docstring; until
then the rows stay UNMAPPED (D-F11/D-F14) and these four declarations are not ported. -/

/-- Row 103 cb:singleton (proposed name).  Body once row 100 lands: `cb_singleton_of_floor thm_floor`. -/
theorem cb_singleton : CbSingletonData := by
  sorry

/-- Row 105 lem:corner-values (proposed name).  Body once row 100 lands:
`corner_values_of_floor thm_floor`.  Clause (i) is unconditional NOW (`corner_values_i`). -/
theorem corner_values : CornerValuesData := by
  sorry

/-- Row 110 thm:C-S7 (FIXED target name, axiom-policy.json).  Body once row 100 lands:
`thm_C_S7_of_floor thm_floor`. -/
theorem thm_C_S7 : CS7Data := by
  sorry

/-- Row 112 thm:C-soft (FIXED target name, axiom-policy.json).  Body once row 100 lands:
`thm_C_soft_of_floor thm_floor`. -/
theorem thm_C_soft : CSoftData := by
  sorry

/-! ## §7 Consumer shape check (thm:comparison, thm:uniqueness (c), (e)).
`UniquenessHypotheses.vertex_edge` / `.soft` (SM/Uniqueness.lean:57-76) have literally the shapes of
`CS7Data.vertex_edge_law` / `CSoftData.soft_theorem` with `F n Q := C` read on the polygon quotient
`GenericPolygon n`; the descent of `cornerStateSum` to the quotient is the accepted
`cornerStateSum_genericShift` (SM/CChamber.lean) — thm:comparison's business (FR-CC-13). -/
example (hF : FloorTheoremData) : CS7Data ∧ CSoftData ∧ CbSingletonData ∧ CornerValuesData :=
  ⟨thm_C_S7_of_floor hF, thm_C_soft_of_floor hF, cb_singleton_of_floor hF, corner_values_of_floor hF⟩

end

end SM
