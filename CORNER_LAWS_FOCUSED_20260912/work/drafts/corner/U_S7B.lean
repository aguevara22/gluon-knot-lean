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

/-! ### Unit U110-B (helper unit, prefix `s7b_`; PLAN_FINAL §3.3 sliding (2), bigon (1)/(5) discharge, §4
row U110-B): halves ↔ intervals.  Part I — the first-return transport of permutations (the mark-level
engine generalising cor:flat-carriers' one-point skip); part II — labels, remoteness, crossings, visits
and parameters of the halves `λᵢ` against the wall centre; part IV — the support bijections
eq. s7c:sliding-bijection / s7c:eligible-bijection as `Equiv`s on `IsDecomposition`, given the
interlacement-transfer data (`s7b_PivotSplit` / `s7b_SupportSplit`); part III — the half crossings and
visits on a SIDE polygon, the sliding mark map `Mark λ₁ ⊕ Mark λ₂ → Mark Q`, and the transport
structure `s7b_SlidingTransport` whose one field `ret` (the first-return law of the smoothing
successors) yields the carrier correspondence `Component Q S ≃ Component λ₁ S₁ ⊕ Component λ₂ S₂`,
the owners and the carrier crossings / `m_Q`.  Requires `import SM.VertexSides` (lem:wall-sides (V):
`ContactAffected`, `VertexCrossingData`, `vertex_sides` are not reachable from the other imports). -/

section S7BReturn

/-! ### U110-B, part I: the first-return transport of permutations (pure combinatorics).
`ι : β → α` is an injection; `g` is the FIRST-RETURN map of `f` on the image of `ι`: from `ι b`
the iterates of `f` leave the image and come back to it first at `ι (g b)`.  Then the cycles of
`f` through the image are exactly the `ι`-images of the cycles of `g`.  This generalises the
one-point `skipJ` device of cor:flat-carriers (SM/FlatCarriers.lean, `sameCycle_skipJ_iff`) to an
arbitrary skipped set — the marks of a side polygon that have no counterpart on the halves. -/

variable {α β : Type*}

/-- `g` is the first-return map of `f` on the image of `ι`, and every point of `α` reaches the
image. -/
structure s7b_ReturnTransport (f : Equiv.Perm α) (g : Equiv.Perm β) (ι : β → α) : Prop where
  inj : Function.Injective ι
  step : ∀ b : β, ∃ k : ℕ, 0 < k ∧ (f ^ k) (ι b) = ι (g b) ∧
    ∀ j : ℕ, 0 < j → j < k → (f ^ j) (ι b) ∉ Set.range ι
  hit : ∀ a : α, ∃ j : ℕ, (f ^ j) a ∈ Set.range ι

namespace s7b_ReturnTransport

variable {f : Equiv.Perm α} {g : Equiv.Perm β} {ι : β → α}

/-- One `g`-step is realised by a positive power of `f` on the image. -/
theorem sameCycle_step (h : s7b_ReturnTransport f g ι) (b : β) :
    f.SameCycle (ι b) (ι (g b)) := by
  obtain ⟨k, -, hk, -⟩ := h.step b
  rw [← hk]
  exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)

theorem sameCycle_pow_of (h : s7b_ReturnTransport f g ι) (b : β) (m : ℕ) :
    f.SameCycle (ι b) (ι ((g ^ m) b)) := by
  induction m with
  | zero => simp only [pow_zero, Equiv.Perm.coe_one, id_eq]; exact Equiv.Perm.SameCycle.refl _ _
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (h.sameCycle_step _)

/-- Cycles of `g` are carried into cycles of `f`. -/
theorem sameCycle_of [Finite β] (h : s7b_ReturnTransport f g ι) {b b' : β}
    (hb : g.SameCycle b b') : f.SameCycle (ι b) (ι b') := by
  obtain ⟨m, -, hm⟩ := hb.exists_pow_eq'
  rw [← hm]
  exact h.sameCycle_pow_of b m

/-- The converse, by strong induction on the number of `f`-steps: an `f`-iterate of `ι b` that
lands in the image is a `g`-iterate of `b`. -/
theorem sameCycle_of_pow_eq (h : s7b_ReturnTransport f g ι) :
    ∀ (m : ℕ) (b b' : β), (f ^ m) (ι b) = ι b' → g.SameCycle b b' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro b b' hm
    obtain ⟨k, hk0, hk, hgap⟩ := h.step b
    rcases Nat.lt_or_ge m k with hmk | hmk
    · rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hm
        rw [h.inj hm]
      · exact absurd ⟨b', hm.symm⟩ (hgap m hm0 hmk)
    · have h1 : (f ^ (m - k)) (ι (g b)) = ι b' := by
        rw [← hk, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hmk]
        exact hm
      have h2 := ih (m - k) (by omega) (g b) b' h1
      exact Equiv.Perm.sameCycle_apply_left.mp h2

/-- Two image points lie on one `f`-cycle iff their preimages lie on one `g`-cycle. -/
theorem sameCycle_iff [Finite α] [Finite β] (h : s7b_ReturnTransport f g ι) (b b' : β) :
    f.SameCycle (ι b) (ι b') ↔ g.SameCycle b b' := by
  constructor
  · intro hb
    obtain ⟨m, -, hm⟩ := hb.exists_pow_eq'
    exact h.sameCycle_of_pow_eq m b b' hm
  · exact h.sameCycle_of

/-- The induced map on cycle spaces (`Quotient` of `SameCycle`), `⟦b⟧ ↦ ⟦ι b⟧`. -/
def cycleMap [Finite β] (h : s7b_ReturnTransport f g ι) :
    Quotient (Equiv.Perm.SameCycle.setoid g) → Quotient (Equiv.Perm.SameCycle.setoid f) :=
  Quotient.lift (fun b => (Quotient.mk (Equiv.Perm.SameCycle.setoid f) (ι b)))
    (fun _ _ hb => Quotient.sound (h.sameCycle_of hb))

theorem cycleMap_mk [Finite β] (h : s7b_ReturnTransport f g ι) (b : β) :
    h.cycleMap (Quotient.mk (Equiv.Perm.SameCycle.setoid g) b) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid f) (ι b) := rfl

theorem cycleMap_bijective [Finite α] [Finite β] (h : s7b_ReturnTransport f g ι) :
    Function.Bijective h.cycleMap := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h b =>
      induction y using Quotient.inductionOn with
      | h b' =>
        intro he
        rw [cycleMap_mk, cycleMap_mk] at he
        exact Quotient.sound ((h.sameCycle_iff b b').mp (Quotient.exact he))
  · intro x
    induction x using Quotient.inductionOn with
    | h a =>
      obtain ⟨j, b, hb⟩ := h.hit a
      refine ⟨Quotient.mk _ b, ?_⟩
      rw [cycleMap_mk, hb]
      exact Quotient.sound (Equiv.Perm.sameCycle_pow_left.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- **The cycle spaces correspond**: `Quotient (SameCycle g) ≃ Quotient (SameCycle f)`, sending
`⟦b⟧` to `⟦ι b⟧`. -/
def cycleEquiv [Finite α] [Finite β] (h : s7b_ReturnTransport f g ι) :
    Quotient (Equiv.Perm.SameCycle.setoid g) ≃ Quotient (Equiv.Perm.SameCycle.setoid f) :=
  Equiv.ofBijective h.cycleMap h.cycleMap_bijective

theorem cycleEquiv_mk [Finite α] [Finite β] (h : s7b_ReturnTransport f g ι) (b : β) :
    h.cycleEquiv (Quotient.mk (Equiv.Perm.SameCycle.setoid g) b) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid f) (ι b) := rfl

/-- The class of an arbitrary point of `α` is the class of the first image point it reaches. -/
theorem mk_eq_of_pow_eq (_h : s7b_ReturnTransport f g ι) (a : α) (j : ℕ) (b : β)
    (hb : (f ^ j) a = ι b) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid f) a =
      Quotient.mk (Equiv.Perm.SameCycle.setoid f) (ι b) := by
  rw [← hb]
  exact Quotient.sound (Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _))

end s7b_ReturnTransport

/-! Sum types: the cycles of `sumCongr g₁ g₂` are the cycles of `g₁` and of `g₂`. -/

variable {β₁ β₂ : Type*}

theorem s7b_sumCongr_pow_inl (g₁ : Equiv.Perm β₁) (g₂ : Equiv.Perm β₂) (k : ℕ) (x : β₁) :
    ((Equiv.Perm.sumCongr g₁ g₂) ^ k) (Sum.inl x) = Sum.inl ((g₁ ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]; rfl

theorem s7b_sumCongr_pow_inr (g₁ : Equiv.Perm β₁) (g₂ : Equiv.Perm β₂) (k : ℕ) (y : β₂) :
    ((Equiv.Perm.sumCongr g₁ g₂) ^ k) (Sum.inr y) = Sum.inr ((g₂ ^ k) y) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]; rfl

theorem s7b_sumCongr_sameCycle_inl [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (x y : β₁) :
    (Equiv.Perm.sumCongr g₁ g₂).SameCycle (Sum.inl x) (Sum.inl y) ↔ g₁.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
    rw [s7b_sumCongr_pow_inl] at hm
    exact ⟨m, by simpa using Sum.inl.inj hm⟩
  · intro h
    obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
    exact ⟨m, by rw [zpow_natCast, s7b_sumCongr_pow_inl, hm]⟩

theorem s7b_sumCongr_sameCycle_inr [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (x y : β₂) :
    (Equiv.Perm.sumCongr g₁ g₂).SameCycle (Sum.inr x) (Sum.inr y) ↔ g₂.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
    rw [s7b_sumCongr_pow_inr] at hm
    exact ⟨m, by simpa using Sum.inr.inj hm⟩
  · intro h
    obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
    exact ⟨m, by rw [zpow_natCast, s7b_sumCongr_pow_inr, hm]⟩

theorem s7b_sumCongr_not_sameCycle [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (x : β₁) (y : β₂) :
    ¬ (Equiv.Perm.sumCongr g₁ g₂).SameCycle (Sum.inl x) (Sum.inr y) := by
  intro h
  obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
  rw [s7b_sumCongr_pow_inl] at hm
  exact Sum.inl_ne_inr hm

/-- The cycle space of a disjoint union of permutations is the disjoint union of the cycle
spaces. -/
def s7b_sumCongr_cycleEquiv [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁) (g₂ : Equiv.Perm β₂) :
    Quotient (Equiv.Perm.SameCycle.setoid (Equiv.Perm.sumCongr g₁ g₂)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid g₁) ⊕ Quotient (Equiv.Perm.SameCycle.setoid g₂) where
  toFun := Quotient.lift
    (fun z => match z with
      | Sum.inl x => Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid g₁) x)
      | Sum.inr y => Sum.inr (Quotient.mk (Equiv.Perm.SameCycle.setoid g₂) y))
    (by
      intro z z' hz
      cases z with
      | inl x =>
        cases z' with
        | inl x' =>
          exact congrArg Sum.inl (Quotient.sound ((s7b_sumCongr_sameCycle_inl g₁ g₂ x x').mp hz))
        | inr y' => exact absurd hz (s7b_sumCongr_not_sameCycle g₁ g₂ x y')
      | inr y =>
        cases z' with
        | inl x' => exact absurd hz.symm (s7b_sumCongr_not_sameCycle g₁ g₂ x' y)
        | inr y' =>
          exact congrArg Sum.inr (Quotient.sound ((s7b_sumCongr_sameCycle_inr g₁ g₂ y y').mp hz)))
  invFun := fun w => match w with
    | Sum.inl c => Quotient.lift (fun x => Quotient.mk _ (Sum.inl x))
        (fun x x' hx => Quotient.sound ((s7b_sumCongr_sameCycle_inl g₁ g₂ x x').mpr hx)) c
    | Sum.inr c => Quotient.lift (fun y => Quotient.mk _ (Sum.inr y))
        (fun y y' hy => Quotient.sound ((s7b_sumCongr_sameCycle_inr g₁ g₂ y y').mpr hy)) c
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h z => cases z <;> rfl
  right_inv := by
    intro w
    cases w with
    | inl c => induction c using Quotient.inductionOn with | h x => rfl
    | inr c => induction c using Quotient.inductionOn with | h y => rfl

theorem s7b_sumCongr_cycleEquiv_inl [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (x : β₁) :
    s7b_sumCongr_cycleEquiv g₁ g₂ (Quotient.mk _ (Sum.inl x)) =
      Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid g₁) x) := rfl

theorem s7b_sumCongr_cycleEquiv_inr [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (y : β₂) :
    s7b_sumCongr_cycleEquiv g₁ g₂ (Quotient.mk _ (Sum.inr y)) =
      Sum.inr (Quotient.mk (Equiv.Perm.SameCycle.setoid g₂) y) := rfl

end S7BReturn

section S7BHalves

/-! ### U110-B, part II: labels, remoteness, crossings and visits of the halves vs the centre.
The halves `λ₁ = firstHalf P M a`, `λ₂ = secondHalf P M a` (def:deletion-halves) live on the wall
centre `P`; their edge labels are the cyclic ranges `firstHalfIndex M a = cyclicRangeIndex M`
(edges `M, …, a`, the last one `-1 ↦ a` being the cut `[μ_a, μ_M] ⊂ E_a`) and
`secondHalfEdgeIndex M a = cyclicRangeIndex a` (edges `a, a+1, …, M-1`, the first one `0 ↦ a`
being the cut `[μ_M, μ_{a+1}] ⊂ E_a`).  A crossing of a half is a crossing of the centre with both
labels in the range and (on a cut edge) the meeting point in the cut; the only adjacent pair of a
half that maps to a REMOTE pair of the centre is its wrap-around pair, whose image is the
contact-affected pair `{a, M}` (first half) / `{a, M-1}` (second half). -/

omit [NeZero n] in
theorem s7b_adjacent_iff {k : ℕ} (i j : ZMod k) :
    adjacent i j ↔ j = i ∨ j = i + 1 ∨ i = j + 1 := by
  unfold adjacent
  constructor
  · rintro (h | h | h)
    · right; right; linear_combination -h
    · left; linear_combination h
    · right; left; linear_combination h
  · rintro (h | h | h)
    · right; left; rw [h]; ring
    · right; right; rw [h]; ring
    · left; rw [h]; ring

omit [NeZero n] in
theorem s7b_adjacent_zero_neg_one {k : ℕ} : adjacent (0 : ZMod k) (-1) := Or.inl (by ring)

omit [NeZero n] in
theorem s7b_adjacent_neg_one_zero {k : ℕ} : adjacent (-1 : ZMod k) 0 := Or.inr (Or.inr (by ring))

theorem s7b_cyclicRange_succ_iff {k : ℕ} [NeZero k] (hk : k < n) (s : ZMod n) (i j : ZMod k) :
    cyclicRangeIndex s j = cyclicRangeIndex s i + 1 ↔ i ≠ -1 ∧ j = i + 1 := by
  have hi := i.val_lt
  have hj := j.val_lt
  constructor
  · intro h
    have h1 : ((j.val : ℕ) : ZMod n) = ((i.val + 1 : ℕ) : ZMod n) := by
      simp only [cyclicRangeIndex] at h
      push_cast
      linear_combination h
    have h2 : j.val = i.val + 1 := by
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    have hi1 : i ≠ -1 := by
      intro he
      have hl := last_index_val_succ (n := k)
      rw [← he] at hl
      omega
    refine ⟨hi1, ZMod.val_injective k ?_⟩
    rw [zmod_val_next_of_ne_last hi1, h2]
  · rintro ⟨hi1, rfl⟩
    exact cyclicRangeIndex_next s hi1

theorem s7b_adjacent_cyclicRange_iff {k : ℕ} [NeZero k] (hk : k < n) (s : ZMod n)
    (i j : ZMod k) :
    adjacent (cyclicRangeIndex s i) (cyclicRangeIndex s j) ↔
      j = i ∨ (i ≠ -1 ∧ j = i + 1) ∨ (j ≠ -1 ∧ i = j + 1) := by
  rw [s7b_adjacent_iff, s7b_cyclicRange_succ_iff hk, s7b_cyclicRange_succ_iff hk,
    (cyclicRangeIndex_injective hk.le s).eq_iff]

omit [NeZero n] in
theorem s7b_zero_ne_neg_one {k : ℕ} [NeZero k] (hk : 2 ≤ k) : (0 : ZMod k) ≠ -1 := by
  intro he
  have hl := last_index_val_succ (n := k)
  rw [← he, ZMod.val_zero] at hl
  omega

omit [NeZero n] in
theorem s7b_one_ne_neg_one {k : ℕ} [NeZero k] (hk : 3 ≤ k) : (1 : ZMod k) ≠ -1 := by
  intro he
  have hl := last_index_val_succ (n := k)
  have : Fact (1 < k) := ⟨by omega⟩
  rw [← he, ZMod.val_one] at hl
  omega

/-- Remoteness along a cyclic range of size `k` (`3 ≤ k < n`): the images of two labels are remote
iff the labels are remote or form the wrap-around pair `{-1, 0}`. -/
theorem s7b_remote_cyclicRange_iff {k : ℕ} [NeZero k] (hk : k < n) (hk3 : 3 ≤ k) (s : ZMod n)
    (i j : ZMod k) :
    remote (cyclicRangeIndex s i) (cyclicRangeIndex s j) ↔
      remote i j ∨ (i = -1 ∧ j = 0) ∨ (j = -1 ∧ i = 0) := by
  unfold remote
  rw [s7b_adjacent_cyclicRange_iff hk, s7b_adjacent_iff]
  constructor
  · intro h
    by_cases h1 : i = -1 ∧ j = 0
    · exact Or.inr (Or.inl h1)
    by_cases h2 : j = -1 ∧ i = 0
    · exact Or.inr (Or.inr h2)
    left
    rintro (hji | hji | hji)
    · exact h (Or.inl hji)
    · apply h; right; left
      refine ⟨?_, hji⟩
      intro hi
      exact h1 ⟨hi, by rw [hji, hi]; ring⟩
    · apply h; right; right
      refine ⟨?_, hji⟩
      intro hj
      exact h2 ⟨hj, by rw [hji, hj]; ring⟩
  · rintro (h | ⟨hi, hj⟩ | ⟨hj, hi⟩) hadj
    · apply h
      rcases hadj with h' | ⟨_, h'⟩ | ⟨_, h'⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rcases hadj with h' | ⟨hi1, _⟩ | ⟨_, h'⟩
      · rw [hi, hj] at h'
        exact s7b_zero_ne_neg_one (by omega) h'
      · exact hi1 hi
      · rw [hi, hj, zero_add] at h'
        exact s7b_one_ne_neg_one hk3 h'.symm
    · rcases hadj with h' | ⟨_, h'⟩ | ⟨hj1, _⟩
      · rw [hi, hj] at h'
        exact s7b_zero_ne_neg_one (by omega) h'.symm
      · rw [hi, hj, zero_add] at h'
        exact s7b_one_ne_neg_one hk3 h'.symm
      · exact hj1 hj

/-! #### The first half `λ₁` -/

theorem s7b_firstHalfSize_lt (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) :
    firstHalfSize M a < n ∧ 3 ≤ firstHalfSize M a := by
  have hb := contactHalfSizes_bounds hn hsep
  omega

theorem s7b_secondHalfSize_lt (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) :
    secondHalfSize M a < n ∧ 3 ≤ secondHalfSize M a := by
  have hb := contactHalfSizes_bounds hn hsep
  omega

theorem s7b_remote_firstHalfIndex_iff (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    (i j : ZMod (firstHalfSize M a)) :
    remote (firstHalfIndex M a i) (firstHalfIndex M a j) ↔
      remote i j ∨ (i = -1 ∧ j = 0) ∨ (j = -1 ∧ i = 0) :=
  s7b_remote_cyclicRange_iff (s7b_firstHalfSize_lt hn hsep).1 (s7b_firstHalfSize_lt hn hsep).2 M i j

theorem s7b_remote_secondHalfEdgeIndex_iff (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) (i j : ZMod (secondHalfSize M a)) :
    remote (secondHalfEdgeIndex M a i) (secondHalfEdgeIndex M a j) ↔
      remote i j ∨ (i = -1 ∧ j = 0) ∨ (j = -1 ∧ i = 0) :=
  s7b_remote_cyclicRange_iff (s7b_secondHalfSize_lt hn hsep).1 (s7b_secondHalfSize_lt hn hsep).2
    a i j

/-- `M - 1` is not an edge label of the first half. -/
theorem s7b_firstHalfIndex_ne_pred (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    (i : ZMod (firstHalfSize M a)) : firstHalfIndex M a i ≠ M - 1 := by
  intro he
  have hr := (firstHalfIndex_range M a (M - 1)).mp ⟨i, he⟩
  have hb := contactHalfSizes_bounds hn hsep
  have hl := last_index_val_succ (n := n)
  have he' : M - 1 - M = (-1 : ZMod n) := by ring
  rw [he'] at hr
  omega

/-- `M` is not an edge label of the second half (its edge labels are `a, …, M-1`). -/
theorem s7b_secondHalfEdgeIndex_ne (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    (i : ZMod (secondHalfSize M a)) : secondHalfEdgeIndex M a i ≠ M := by
  intro he
  have hr := (cyclicRangeIndex_range (secondHalfSize_le M a) a M).mp ⟨i, he⟩
  have hb := contactHalfSizes_bounds hn hsep
  have hc : M - a = (secondHalfSize M a : ZMod n) := (secondHalfSize_cast M a).symm
  rw [hc, ZMod.val_natCast_of_lt (by omega)] at hr
  exact lt_irrefl _ hr

/-- The image of a crossing of `λ₁` is a crossing of the centre. -/
theorem s7b_isCrossing_firstHalf_image (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) {s : Finset (ZMod (firstHalfSize M a))}
    (hs : IsCrossing (firstHalf P M a) s) : IsCrossing P (s.image (firstHalfIndex M a)) := by
  obtain ⟨i, j, rfl, hr, x, hxi, hxj⟩ := hs
  refine ⟨firstHalfIndex M a i, firstHalfIndex M a j, ?_, ?_, x,
    firstHalf_segment_subset hm i hxi, firstHalf_segment_subset hm j hxj⟩
  · rw [Finset.image_insert, Finset.image_singleton]
  · exact (s7b_remote_firstHalfIndex_iff hn hsep i j).mpr (Or.inl hr)

/-- The image of a crossing of `λ₂` is a crossing of the centre. -/
theorem s7b_isCrossing_secondHalf_image (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) {s : Finset (ZMod (secondHalfSize M a))}
    (hs : IsCrossing (secondHalf P M a) s) : IsCrossing P (s.image (secondHalfEdgeIndex M a)) := by
  obtain ⟨i, j, rfl, hr, x, hxi, hxj⟩ := hs
  refine ⟨secondHalfEdgeIndex M a i, secondHalfEdgeIndex M a j, ?_, ?_, x,
    secondHalf_segment_subset hn hsep hm i hxi, secondHalf_segment_subset hn hsep hm j hxj⟩
  · rw [Finset.image_insert, Finset.image_singleton]
  · exact (s7b_remote_secondHalfEdgeIndex_iff hn hsep i j).mpr (Or.inl hr)

/-- The image of a crossing of `λ₁` is never a contact-affected pair. -/
theorem s7b_firstHalf_image_not_affected (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} {s : Finset (ZMod (firstHalfSize M a))}
    (hs : IsCrossing (firstHalf P M a) s) :
    ¬ ContactAffected M a (s.image (firstHalfIndex M a)) := by
  obtain ⟨i, j, rfl, hr, -⟩ := hs
  rw [Finset.image_insert, Finset.image_singleton]
  have hij : i ≠ j := (remote_endpoints i j hr).1.symm
  rintro (h | h)
  · have hmem : M - 1 ∈ ({firstHalfIndex M a i, firstHalfIndex M a j} : Finset (ZMod n)) := by
      rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · exact s7b_firstHalfIndex_ne_pred hn hsep i h'.symm
    · exact s7b_firstHalfIndex_ne_pred hn hsep j h'.symm
  · have hinj := firstHalfIndex_injective M a
    have hi : i = -1 ∨ i = 0 := by
      have hmem : firstHalfIndex M a i ∈ ({a, M} : Finset (ZMod n)) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (hinj (h'.trans (firstHalfIndex_last M a).symm))
      · exact Or.inr (hinj (h'.trans (firstHalfIndex_zero M a).symm))
    have hj : j = -1 ∨ j = 0 := by
      have hmem : firstHalfIndex M a j ∈ ({a, M} : Finset (ZMod n)) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (hinj (h'.trans (firstHalfIndex_last M a).symm))
      · exact Or.inr (hinj (h'.trans (firstHalfIndex_zero M a).symm))
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact hij rfl
    · exact hr s7b_adjacent_neg_one_zero
    · exact hr s7b_adjacent_zero_neg_one
    · exact hij rfl

/-- The image of a crossing of `λ₂` is never a contact-affected pair. -/
theorem s7b_secondHalf_image_not_affected (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n} {s : Finset (ZMod (secondHalfSize M a))}
    (hs : IsCrossing (secondHalf P M a) s) :
    ¬ ContactAffected M a (s.image (secondHalfEdgeIndex M a)) := by
  obtain ⟨i, j, rfl, hr, -⟩ := hs
  rw [Finset.image_insert, Finset.image_singleton]
  have hij : i ≠ j := (remote_endpoints i j hr).1.symm
  rintro (h | h)
  · have hinj := secondHalfEdgeIndex_injective M a
    have hi : i = 0 ∨ i = -1 := by
      have hmem : secondHalfEdgeIndex M a i ∈ ({a, M - 1} : Finset (ZMod n)) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (hinj (h'.trans (secondHalfEdgeIndex_zero M a).symm))
      · exact Or.inr (hinj (h'.trans (secondHalfEdgeIndex_last M a).symm))
    have hj : j = 0 ∨ j = -1 := by
      have hmem : secondHalfEdgeIndex M a j ∈ ({a, M - 1} : Finset (ZMod n)) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (hinj (h'.trans (secondHalfEdgeIndex_zero M a).symm))
      · exact Or.inr (hinj (h'.trans (secondHalfEdgeIndex_last M a).symm))
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact hij rfl
    · exact hr s7b_adjacent_zero_neg_one
    · exact hr s7b_adjacent_neg_one_zero
    · exact hij rfl
  · have hmem : M ∈ ({secondHalfEdgeIndex M a i, secondHalfEdgeIndex M a j} : Finset (ZMod n)) := by
      rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · exact s7b_secondHalfEdgeIndex_ne hn hsep i h'.symm
    · exact s7b_secondHalfEdgeIndex_ne hn hsep j h'.symm

/-! #### Segments of the halves as subsegments of the centre's edges -/

theorem s7b_edgeSegment_firstHalf (P : LabelledTuple n) (M a : ZMod n)
    {i : ZMod (firstHalfSize M a)} (hi : i ≠ -1) :
    edgeSegment (firstHalf P M a) i = edgeSegment P (firstHalfIndex M a i) := by
  ext x
  simp only [edgeSegment, Set.mem_ofPred_eq, edgePoint_firstHalf P M a hi]

theorem s7b_edgeSegment_secondHalf (P : LabelledTuple n) (M a : ZMod n)
    {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    edgeSegment (secondHalf P M a) i = edgeSegment P (secondHalfEdgeIndex M a i) := by
  ext x
  simp only [edgeSegment, Set.mem_ofPred_eq, edgePoint_secondHalf P M a hi]

/-- The cut of `λ₁` is the initial part `[0, r]` of the contact edge `E_a`. -/
theorem s7b_mem_edgeSegment_firstHalf_cut {P : LabelledTuple n} {M a : ZMod n} {r : ℝ}
    (hr : P M = edgePoint P a r) (hr0 : 0 < r) (x : Plane) :
    x ∈ edgeSegment (firstHalf P M a) (-1) ↔ ∃ u : ℝ, 0 ≤ u ∧ u ≤ r ∧ x = edgePoint P a u := by
  simp only [edgeSegment, Set.mem_ofPred_eq, edgePoint_firstHalf_cut hr]
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨r * t, mul_nonneg hr0.le ht0, by nlinarith, rfl⟩
  · rintro ⟨u, hu0, hu1, rfl⟩
    refine ⟨u / r, div_nonneg hu0 hr0.le, (div_le_one hr0).mpr hu1, ?_⟩
    rw [mul_div_cancel₀ u hr0.ne']

/-- The cut of `λ₂` is the final part `[r, 1]` of the contact edge `E_a`. -/
theorem s7b_mem_edgeSegment_secondHalf_cut (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} {r : ℝ} (hr : P M = edgePoint P a r) (hr1 : r < 1) (x : Plane) :
    x ∈ edgeSegment (secondHalf P M a) 0 ↔ ∃ u : ℝ, r ≤ u ∧ u ≤ 1 ∧ x = edgePoint P a u := by
  simp only [edgeSegment, Set.mem_ofPred_eq, edgePoint_secondHalf_cut hn hsep hr]
  have h1r : 0 < 1 - r := by linarith
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨r + (1 - r) * t, by nlinarith, by nlinarith, rfl⟩
  · rintro ⟨u, hu0, hu1, rfl⟩
    refine ⟨(u - r) / (1 - r), div_nonneg (by linarith) h1r.le,
      (div_le_one h1r).mpr (by linarith), ?_⟩
    rw [mul_div_cancel₀ _ h1r.ne']
    ring_nf

/-! #### Crossing and visit maps `λ_i → centre` -/

/-- The crossing of the centre carried by a crossing of `λ₁`. -/
def s7b_firstHalfCrossing (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (c : Crossing (firstHalf P M a)) :
    Crossing P :=
  ⟨c.val.image (firstHalfIndex M a), s7b_isCrossing_firstHalf_image hn hsep hm c.property⟩

/-- The crossing of the centre carried by a crossing of `λ₂`. -/
def s7b_secondHalfCrossing (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (c : Crossing (secondHalf P M a)) :
    Crossing P :=
  ⟨c.val.image (secondHalfEdgeIndex M a), s7b_isCrossing_secondHalf_image hn hsep hm c.property⟩

theorem s7b_firstHalfCrossing_val (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (c : Crossing (firstHalf P M a)) :
    (s7b_firstHalfCrossing hn hsep hm c).val = c.val.image (firstHalfIndex M a) := rfl

theorem s7b_secondHalfCrossing_val (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (c : Crossing (secondHalf P M a)) :
    (s7b_secondHalfCrossing hn hsep hm c).val = c.val.image (secondHalfEdgeIndex M a) := rfl

theorem s7b_firstHalfCrossing_injective (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) :
    Function.Injective (s7b_firstHalfCrossing hn hsep hm) := by
  intro c d h
  exact Subtype.ext (Finset.image_injective (firstHalfIndex_injective M a) (congrArg Subtype.val h))

theorem s7b_secondHalfCrossing_injective (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) :
    Function.Injective (s7b_secondHalfCrossing hn hsep hm) := by
  intro c d h
  exact Subtype.ext
    (Finset.image_injective (secondHalfEdgeIndex_injective M a) (congrArg Subtype.val h))

theorem s7b_firstHalfCrossing_not_affected (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (c : Crossing (firstHalf P M a)) :
    ¬ ContactAffected M a (s7b_firstHalfCrossing hn hsep hm c).val :=
  s7b_firstHalf_image_not_affected hn hsep c.property

theorem s7b_secondHalfCrossing_not_affected (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (c : Crossing (secondHalf P M a)) :
    ¬ ContactAffected M a (s7b_secondHalfCrossing hn hsep hm c).val :=
  s7b_secondHalf_image_not_affected hn hsep c.property

/-- The visit of the centre carried by a visit of `λ₁` (same crossing image, image edge label). -/
def s7b_firstHalfVisit (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (firstHalf P M a)) : Visit P :=
  ⟨s7b_firstHalfCrossing hn hsep hm v.1,
    ⟨firstHalfIndex M a v.2.val, Finset.mem_image_of_mem _ v.2.property⟩⟩

/-- The visit of the centre carried by a visit of `λ₂`. -/
def s7b_secondHalfVisit (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (secondHalf P M a)) : Visit P :=
  ⟨s7b_secondHalfCrossing hn hsep hm v.1,
    ⟨secondHalfEdgeIndex M a v.2.val, Finset.mem_image_of_mem _ v.2.property⟩⟩

theorem s7b_firstHalfVisit_fst (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (firstHalf P M a)) :
    (s7b_firstHalfVisit hn hsep hm v).1 = s7b_firstHalfCrossing hn hsep hm v.1 := rfl

theorem s7b_firstHalfVisit_edge (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (firstHalf P M a)) :
    (s7b_firstHalfVisit hn hsep hm v).2.val = firstHalfIndex M a v.2.val := rfl

theorem s7b_secondHalfVisit_fst (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (secondHalf P M a)) :
    (s7b_secondHalfVisit hn hsep hm v).1 = s7b_secondHalfCrossing hn hsep hm v.1 := rfl

theorem s7b_secondHalfVisit_edge (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (secondHalf P M a)) :
    (s7b_secondHalfVisit hn hsep hm v).2.val = secondHalfEdgeIndex M a v.2.val := rfl

theorem s7b_firstHalfVisit_injective (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) :
    Function.Injective (s7b_firstHalfVisit hn hsep hm) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hc : c = d := s7b_firstHalfCrossing_injective hn hsep hm (congrArg Sigma.fst h)
  subst hc
  have hi : firstHalfIndex M a i.val = firstHalfIndex M a j.val := by
    have := congrArg (fun w : Visit P => w.2.val) h
    exact this
  rw [Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (Subtype.ext (firstHalfIndex_injective M a hi))⟩

theorem s7b_secondHalfVisit_injective (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) :
    Function.Injective (s7b_secondHalfVisit hn hsep hm) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hc : c = d := s7b_secondHalfCrossing_injective hn hsep hm (congrArg Sigma.fst h)
  subst hc
  have hi : secondHalfEdgeIndex M a i.val = secondHalfEdgeIndex M a j.val := by
    have := congrArg (fun w : Visit P => w.2.val) h
    exact this
  rw [Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (Subtype.ext (secondHalfEdgeIndex_injective M a hi))⟩

/-- The visit maps commute with the crossing pairing `visitTwin`. -/
theorem s7b_firstHalfVisit_visitTwin (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (firstHalf P M a)) :
    s7b_firstHalfVisit hn hsep hm (visitTwin v) = visitTwin (s7b_firstHalfVisit hn hsep hm v) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne v (s7b_firstHalfVisit_injective hn hsep hm h)

theorem s7b_secondHalfVisit_visitTwin (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (secondHalf P M a)) :
    s7b_secondHalfVisit hn hsep hm (visitTwin v) =
      visitTwin (s7b_secondHalfVisit hn hsep hm v) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne v (s7b_secondHalfVisit_injective hn hsep hm h)

/-! #### Meeting points and parameters -/

/-- At the centre, two remote unaffected edges meet in at most one point (transversality,
`contact_unaffected_pair_geometry`). -/
theorem s7b_centre_meet_unique (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hz : pointZeroTriples P = {contactSupport M a}) {i j : ZMod n}
    (hr : remote i j) (hnot : ¬ ContactAffected M a {i, j}) {x y : Plane}
    (hxi : x ∈ edgeSegment P i) (hxj : x ∈ edgeSegment P j)
    (hyi : y ∈ edgeSegment P i) (hyj : y ∈ edgeSegment P j) : x = y := by
  have hd := (contact_unaffected_pair_geometry hn hsep hz hr hnot hxi hxj).2.2
  obtain ⟨s, -, -, hs⟩ := hxi
  obtain ⟨t, -, -, ht⟩ := hxj
  obtain ⟨s', -, -, hs'⟩ := hyi
  obtain ⟨t', -, -, ht'⟩ := hyj
  have h1 : P i + s • edge P i = P j + t • edge P j := hs.symm.trans ht
  have h2 : P i + s' • edge P i = P j + t' • edge P j := hs'.symm.trans ht'
  have := (intersection_parameters_unique hd h1 h2).1
  rw [hs, hs', this]

/-- The crossing point of a crossing of `λ₁` is the crossing point of its image. -/
theorem s7b_crossingPoint_firstHalfCrossing (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (c : Crossing (firstHalf P M a)) :
    crossingPoint (s7b_firstHalfCrossing hn hsep hm c) = crossingPoint c := by
  obtain ⟨i, j, hs, hr, -⟩ := c.property
  have hr' : remote (firstHalfIndex M a i) (firstHalfIndex M a j) :=
    (s7b_remote_firstHalfIndex_iff hn hsep i j).mpr (Or.inl hr)
  have hval : (s7b_firstHalfCrossing hn hsep hm c).val =
      {firstHalfIndex M a i, firstHalfIndex M a j} := by
    rw [s7b_firstHalfCrossing_val, hs, Finset.image_insert, Finset.image_singleton]
  have hnot : ¬ ContactAffected M a {firstHalfIndex M a i, firstHalfIndex M a j} := by
    rw [← hval]; exact s7b_firstHalfCrossing_not_affected hn hsep hm c
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  have hi' : firstHalfIndex M a i ∈ (s7b_firstHalfCrossing hn hsep hm c).val := by rw [hval]; simp
  have hj' : firstHalfIndex M a j ∈ (s7b_firstHalfCrossing hn hsep hm c).val := by rw [hval]; simp
  exact s7b_centre_meet_unique hn hsep hz hr' hnot (crossingPoint_mem _ _ hi') (crossingPoint_mem _ _ hj')
    (firstHalf_segment_subset hm i (crossingPoint_mem c i hi))
    (firstHalf_segment_subset hm j (crossingPoint_mem c j hj))

theorem s7b_crossingPoint_secondHalfCrossing (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (c : Crossing (secondHalf P M a)) :
    crossingPoint (s7b_secondHalfCrossing hn hsep hm c) = crossingPoint c := by
  obtain ⟨i, j, hs, hr, -⟩ := c.property
  have hr' : remote (secondHalfEdgeIndex M a i) (secondHalfEdgeIndex M a j) :=
    (s7b_remote_secondHalfEdgeIndex_iff hn hsep i j).mpr (Or.inl hr)
  have hval : (s7b_secondHalfCrossing hn hsep hm c).val =
      {secondHalfEdgeIndex M a i, secondHalfEdgeIndex M a j} := by
    rw [s7b_secondHalfCrossing_val, hs, Finset.image_insert, Finset.image_singleton]
  have hnot : ¬ ContactAffected M a {secondHalfEdgeIndex M a i, secondHalfEdgeIndex M a j} := by
    rw [← hval]; exact s7b_secondHalfCrossing_not_affected hn hsep hm c
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  have hi' : secondHalfEdgeIndex M a i ∈ (s7b_secondHalfCrossing hn hsep hm c).val := by
    rw [hval]; simp
  have hj' : secondHalfEdgeIndex M a j ∈ (s7b_secondHalfCrossing hn hsep hm c).val := by
    rw [hval]; simp
  exact s7b_centre_meet_unique hn hsep hz hr' hnot (crossingPoint_mem _ _ hi')
    (crossingPoint_mem _ _ hj')
    (secondHalf_segment_subset hn hsep hm i (crossingPoint_mem c i hi))
    (secondHalf_segment_subset hn hsep hm j (crossingPoint_mem c j hj))

/-- Off the cut, a visit of `λ₁` and its image have the same parameter. -/
theorem s7b_visitParameter_firstHalfVisit (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (v : Visit (firstHalf P M a)) (hv : v.2.val ≠ -1) :
    visitParameter (s7b_firstHalfVisit hn hsep hm v) = visitParameter v := by
  have hn5 := contactSeparated_size hn hsep
  have h1 : crossingPoint (s7b_firstHalfCrossing hn hsep hm v.1) =
      edgePoint P (firstHalfIndex M a v.2.val) (visitParameter (s7b_firstHalfVisit hn hsep hm v)) :=
    (crossingParameter_spec (s7b_firstHalfVisit hn hsep hm v).1
      (s7b_firstHalfVisit hn hsep hm v).2.val (s7b_firstHalfVisit hn hsep hm v).2.property).2.2
  have h2 : crossingPoint v.1 = edgePoint (firstHalf P M a) v.2.val (visitParameter v) :=
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2
  rw [s7b_crossingPoint_firstHalfCrossing hn hsep hz hm] at h1
  rw [edgePoint_firstHalf P M a hv] at h2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz _) (h1.symm.trans h2)

/-- On the cut of `λ₁`, the image parameter on `E_a` is `r · t` (`t` the parameter on the cut). -/
theorem s7b_visitParameter_firstHalfVisit_cut (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a) {r : ℝ}
    (hr : P M = edgePoint P a r) (v : Visit (firstHalf P M a)) (hv : v.2.val = -1) :
    visitParameter (s7b_firstHalfVisit hn hsep hm v) = r * visitParameter v := by
  have hn5 := contactSeparated_size hn hsep
  have h1 : crossingPoint (s7b_firstHalfCrossing hn hsep hm v.1) =
      edgePoint P (firstHalfIndex M a v.2.val) (visitParameter (s7b_firstHalfVisit hn hsep hm v)) :=
    (crossingParameter_spec (s7b_firstHalfVisit hn hsep hm v).1
      (s7b_firstHalfVisit hn hsep hm v).2.val (s7b_firstHalfVisit hn hsep hm v).2.property).2.2
  have h2 : crossingPoint v.1 = edgePoint (firstHalf P M a) v.2.val (visitParameter v) :=
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2
  rw [s7b_crossingPoint_firstHalfCrossing hn hsep hz hm, hv, firstHalfIndex_last] at h1
  rw [hv, edgePoint_firstHalf_cut hr] at h2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz _) (h1.symm.trans h2)

/-- Off the cut, a visit of `λ₂` and its image have the same parameter. -/
theorem s7b_visitParameter_secondHalfVisit (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (v : Visit (secondHalf P M a)) (hv : v.2.val ≠ 0) :
    visitParameter (s7b_secondHalfVisit hn hsep hm v) = visitParameter v := by
  have hn5 := contactSeparated_size hn hsep
  have h1 : crossingPoint (s7b_secondHalfCrossing hn hsep hm v.1) =
      edgePoint P (secondHalfEdgeIndex M a v.2.val)
        (visitParameter (s7b_secondHalfVisit hn hsep hm v)) :=
    (crossingParameter_spec (s7b_secondHalfVisit hn hsep hm v).1
      (s7b_secondHalfVisit hn hsep hm v).2.val (s7b_secondHalfVisit hn hsep hm v).2.property).2.2
  have h2 : crossingPoint v.1 = edgePoint (secondHalf P M a) v.2.val (visitParameter v) :=
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2
  rw [s7b_crossingPoint_secondHalfCrossing hn hsep hz hm] at h1
  rw [edgePoint_secondHalf P M a hv] at h2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz _) (h1.symm.trans h2)

/-- On the cut of `λ₂`, the image parameter on `E_a` is `r + (1 − r) t`. -/
theorem s7b_visitParameter_secondHalfVisit_cut (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a) {r : ℝ}
    (hr : P M = edgePoint P a r) (v : Visit (secondHalf P M a)) (hv : v.2.val = 0) :
    visitParameter (s7b_secondHalfVisit hn hsep hm v) = r + (1 - r) * visitParameter v := by
  have hn5 := contactSeparated_size hn hsep
  have h1 : crossingPoint (s7b_secondHalfCrossing hn hsep hm v.1) =
      edgePoint P (secondHalfEdgeIndex M a v.2.val)
        (visitParameter (s7b_secondHalfVisit hn hsep hm v)) :=
    (crossingParameter_spec (s7b_secondHalfVisit hn hsep hm v).1
      (s7b_secondHalfVisit hn hsep hm v).2.val (s7b_secondHalfVisit hn hsep hm v).2.property).2.2
  have h2 : crossingPoint v.1 = edgePoint (secondHalf P M a) v.2.val (visitParameter v) :=
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2
  rw [s7b_crossingPoint_secondHalfCrossing hn hsep hz hm, hv, secondHalfEdgeIndex_zero] at h1
  rw [hv, edgePoint_secondHalf_cut hn hsep hr] at h2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz _) (h1.symm.trans h2)

end S7BHalves

section S7BSupports

/-! ### U110-B, part IV: the support bijections (eq. s7c:sliding-bijection, s7c:eligible-bijection)
as a purely combinatorial splitting of independent sets.  `R` is the interlacement relation of the
side polygon, `R₁, R₂` those of the halves, `ι₁, ι₂` the half crossing maps: independent sets of `R`
contained in the two (disjoint) images — or containing the pivot `x₋` and otherwise contained in the
images — correspond to pairs of independent sets of `R₁`, `R₂`.  The geometric inputs (interlacement
is preserved by `ιᵢ`, no cross-interlacement, the interval dichotomy for the non-neighbours of `x₋`)
are the fields of `s7b_SupportSplit` / `s7b_PivotSplit`. -/

variable {γ γ₁ γ₂ : Type*}

/-- Independence of a finite set for a relation (`IsDecomposition` unfolds to this shape for
`R = Interlaces`, `mem_independentSupports_iff`). -/
def s7b_Indep (R : γ → γ → Prop) (S : Finset γ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y

theorem s7b_isDecomposition_iff_indep {n : ℕ} (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : IsDecomposition hn hP S ↔ s7b_Indep (Interlaces hn hP) S :=
  mem_independentSupports_iff hn hP S

/-- The data of two disjoint injective images on which `R` restricts to `R₁`, `R₂`, with no
interlacement across. -/
structure s7b_SupportSplit (R : γ → γ → Prop) (R₁ : γ₁ → γ₁ → Prop) (R₂ : γ₂ → γ₂ → Prop)
    (ι₁ : γ₁ → γ) (ι₂ : γ₂ → γ) : Prop where
  inj₁ : Function.Injective ι₁
  inj₂ : Function.Injective ι₂
  disjoint : ∀ c₁ c₂, ι₁ c₁ ≠ ι₂ c₂
  rel₁ : ∀ c c', R (ι₁ c) (ι₁ c') ↔ R₁ c c'
  rel₂ : ∀ c c', R (ι₂ c) (ι₂ c') ↔ R₂ c c'
  cross : ∀ c₁ c₂, ¬ R (ι₁ c₁) (ι₂ c₂)
  cross' : ∀ c₁ c₂, ¬ R (ι₂ c₂) (ι₁ c₁)

/-- The preimage of a support under an injection, as a finite set. -/
def s7b_pre [Fintype γ₁] (ι : γ₁ → γ) (S : Finset γ) : Finset γ₁ := Finset.univ.filter fun c => ι c ∈ S

theorem s7b_mem_pre [Fintype γ₁] (ι : γ₁ → γ) (S : Finset γ) (c : γ₁) : c ∈ s7b_pre ι S ↔ ι c ∈ S := by
  simp only [s7b_pre, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The image of a support under an injection. -/
def s7b_img {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ₁) : Finset γ := S.map ⟨ι, hι⟩

theorem s7b_mem_img {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ₁) (y : γ) :
    y ∈ s7b_img hι S ↔ ∃ c ∈ S, ι c = y := by
  simp only [s7b_img, Finset.mem_map, Function.Embedding.coeFn_mk]

theorem s7b_apply_mem_img {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ₁) (c : γ₁) :
    ι c ∈ s7b_img hι S ↔ c ∈ S := by
  rw [s7b_mem_img]
  constructor
  · rintro ⟨c', hc', he⟩
    rw [hι he] at hc'
    exact hc'
  · intro hc
    exact ⟨c, hc, rfl⟩

theorem s7b_pre_img [Fintype γ₁] {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ₁) :
    s7b_pre ι (s7b_img hι S) = S := by
  ext c
  rw [s7b_mem_pre, s7b_apply_mem_img]

theorem s7b_img_pre_subset [Fintype γ₁] {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ) :
    s7b_img hι (s7b_pre ι S) ⊆ S := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := (s7b_mem_img hι _ y).mp hy
  exact (s7b_mem_pre ι S c).mp hc

namespace s7b_SupportSplit

variable {R : γ → γ → Prop} {R₁ : γ₁ → γ₁ → Prop} {R₂ : γ₂ → γ₂ → Prop} {ι₁ : γ₁ → γ} {ι₂ : γ₂ → γ}

theorem indep_pre₁ [Fintype γ₁] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) {S : Finset γ} (hS : s7b_Indep R S) :
    s7b_Indep R₁ (s7b_pre ι₁ S) := by
  intro c hc c' hc' hne hR
  rw [s7b_mem_pre] at hc hc'
  exact hS _ hc _ hc' (fun he => hne (h.inj₁ he)) ((h.rel₁ c c').mpr hR)

theorem indep_pre₂ [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) {S : Finset γ} (hS : s7b_Indep R S) :
    s7b_Indep R₂ (s7b_pre ι₂ S) := by
  intro c hc c' hc' hne hR
  rw [s7b_mem_pre] at hc hc'
  exact hS _ hc _ hc' (fun he => hne (h.inj₂ he)) ((h.rel₂ c c').mpr hR)

/-- The union of the two images of independent half supports. -/
def joinSupport (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) (S₁ : Finset γ₁) (S₂ : Finset γ₂) :
    Finset γ :=
  s7b_img h.inj₁ S₁ ∪ s7b_img h.inj₂ S₂

theorem mem_joinSupport (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) (S₁ : Finset γ₁) (S₂ : Finset γ₂)
    (y : γ) : y ∈ h.joinSupport S₁ S₂ ↔ (∃ c ∈ S₁, ι₁ c = y) ∨ ∃ c ∈ S₂, ι₂ c = y := by
  simp only [joinSupport, Finset.mem_union, s7b_mem_img]

theorem indep_joinSupport (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) {S₁ : Finset γ₁} {S₂ : Finset γ₂}
    (h₁ : s7b_Indep R₁ S₁) (h₂ : s7b_Indep R₂ S₂) : s7b_Indep R (h.joinSupport S₁ S₂) := by
  intro y hy y' hy' hne hR
  rw [mem_joinSupport] at hy hy'
  rcases hy with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;> rcases hy' with ⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩
  · exact h₁ c hc c' hc' (fun he => hne (congrArg ι₁ he)) ((h.rel₁ c c').mp hR)
  · exact h.cross c c' hR
  · exact h.cross' c' c hR
  · exact h₂ c hc c' hc' (fun he => hne (congrArg ι₂ he)) ((h.rel₂ c c').mp hR)

theorem pre₁_joinSupport [Fintype γ₁] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) (S₁ : Finset γ₁) (S₂ : Finset γ₂) :
    s7b_pre ι₁ (h.joinSupport S₁ S₂) = S₁ := by
  ext c
  rw [s7b_mem_pre, mem_joinSupport]
  constructor
  · rintro (⟨c', hc', he⟩ | ⟨c', -, he⟩)
    · rw [h.inj₁ he] at hc'; exact hc'
    · exact absurd he.symm (h.disjoint c c')
  · intro hc
    exact Or.inl ⟨c, hc, rfl⟩

theorem pre₂_joinSupport [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) (S₁ : Finset γ₁) (S₂ : Finset γ₂) :
    s7b_pre ι₂ (h.joinSupport S₁ S₂) = S₂ := by
  ext c
  rw [s7b_mem_pre, mem_joinSupport]
  constructor
  · rintro (⟨c', -, he⟩ | ⟨c', hc', he⟩)
    · exact absurd he (h.disjoint c' c)
    · rw [h.inj₂ he] at hc'; exact hc'
  · intro hc
    exact Or.inr ⟨c, hc, rfl⟩

theorem joinSupport_pre [Fintype γ₁] [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) {S : Finset γ}
    (hS : ∀ y ∈ S, y ∈ Set.range ι₁ ∪ Set.range ι₂) :
    h.joinSupport (s7b_pre ι₁ S) (s7b_pre ι₂ S) = S := by
  ext y
  rw [mem_joinSupport]
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact (s7b_mem_pre ι₁ S c).mp hc
    · exact (s7b_mem_pre ι₂ S c).mp hc
  · intro hy
    rcases hS y hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨c, (s7b_mem_pre ι₁ S c).mpr hy, rfl⟩
    · exact Or.inr ⟨c, (s7b_mem_pre ι₂ S c).mpr hy, rfl⟩

/-- **eq. s7c:eligible-bijection**, abstractly: independent sets of `R` inside the two images
correspond to pairs of independent sets of `R₁`, `R₂`. -/
def eligibleEquiv [Fintype γ₁] [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) :
    {S : Finset γ // s7b_Indep R S ∧ ∀ y ∈ S, y ∈ Set.range ι₁ ∪ Set.range ι₂} ≃
      {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂} where
  toFun S := (⟨s7b_pre ι₁ S.1, h.indep_pre₁ S.2.1⟩, ⟨s7b_pre ι₂ S.1, h.indep_pre₂ S.2.1⟩)
  invFun p := ⟨h.joinSupport p.1.1 p.2.1, h.indep_joinSupport p.1.2 p.2.2, by
    intro y hy
    rcases (h.mem_joinSupport _ _ y).mp hy with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩⟩
  left_inv S := Subtype.ext (h.joinSupport_pre S.2.2)
  right_inv p := by
    ext1
    · exact Subtype.ext (h.pre₁_joinSupport _ _)
    · exact Subtype.ext (h.pre₂_joinSupport _ _)

theorem eligibleEquiv_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂)
    (S : {S : Finset γ // s7b_Indep R S ∧ ∀ y ∈ S, y ∈ Set.range ι₁ ∪ Set.range ι₂}) :
    ((h.eligibleEquiv S).1.1 = s7b_pre ι₁ S.1) ∧ ((h.eligibleEquiv S).2.1 = s7b_pre ι₂ S.1) :=
  ⟨rfl, rfl⟩

theorem eligibleEquiv_symm_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    (h.eligibleEquiv.symm p).1 = h.joinSupport p.1.1 p.2.1 := rfl

end s7b_SupportSplit

/-- The sliding data: a split plus a pivot `x` (the contact crossing `x₋`) outside both images,
interlacing nothing in them, such that every other non-neighbour of `x` lies in an image
(the two visits of `x` cut the traversal into the two half intervals). -/
structure s7b_PivotSplit (R : γ → γ → Prop) (R₁ : γ₁ → γ₁ → Prop) (R₂ : γ₂ → γ₂ → Prop)
    (ι₁ : γ₁ → γ) (ι₂ : γ₂ → γ) (x : γ) : Prop where
  split : s7b_SupportSplit R R₁ R₂ ι₁ ι₂
  x_not₁ : ∀ c, ι₁ c ≠ x
  x_not₂ : ∀ c, ι₂ c ≠ x
  x_free₁ : ∀ c, ¬ R x (ι₁ c) ∧ ¬ R (ι₁ c) x
  x_free₂ : ∀ c, ¬ R x (ι₂ c) ∧ ¬ R (ι₂ c) x
  x_split : ∀ y, y ≠ x → ¬ R x y → ¬ R y x → y ∈ Set.range ι₁ ∪ Set.range ι₂

namespace s7b_PivotSplit

variable {R : γ → γ → Prop} {R₁ : γ₁ → γ₁ → Prop} {R₂ : γ₂ → γ₂ → Prop} {ι₁ : γ₁ → γ} {ι₂ : γ₂ → γ}
  {x : γ}

theorem indep_insert (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) {S₁ : Finset γ₁} {S₂ : Finset γ₂}
    (h₁ : s7b_Indep R₁ S₁) (h₂ : s7b_Indep R₂ S₂) :
    s7b_Indep R (insert x (h.split.joinSupport S₁ S₂)) := by
  intro y hy y' hy' hne hR
  rw [Finset.mem_insert] at hy hy'
  rcases hy with rfl | hy
  · rcases hy' with rfl | hy'
    · exact hne rfl
    · rcases (h.split.mem_joinSupport _ _ y').mp hy' with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.x_free₁ c).1 hR
      · exact (h.x_free₂ c).1 hR
  · rcases hy' with rfl | hy'
    · rcases (h.split.mem_joinSupport _ _ y).mp hy with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.x_free₁ c).2 hR
      · exact (h.x_free₂ c).2 hR
    · exact h.split.indep_joinSupport h₁ h₂ y hy y' hy' hne hR

theorem pre₁_insert [Fintype γ₁] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) (S : Finset γ) :
    s7b_pre ι₁ (insert x S) = s7b_pre ι₁ S := by
  ext c
  rw [s7b_mem_pre, s7b_mem_pre, Finset.mem_insert]
  exact ⟨fun hc => hc.resolve_left (h.x_not₁ c), Or.inr⟩

theorem pre₂_insert [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) (S : Finset γ) :
    s7b_pre ι₂ (insert x S) = s7b_pre ι₂ S := by
  ext c
  rw [s7b_mem_pre, s7b_mem_pre, Finset.mem_insert]
  exact ⟨fun hc => hc.resolve_left (h.x_not₂ c), Or.inr⟩

theorem insert_join_pre [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) {S : Finset γ} (hS : s7b_Indep R S)
    (hx : x ∈ S) :
    insert x (h.split.joinSupport (s7b_pre ι₁ S) (s7b_pre ι₂ S)) = S := by
  ext y
  rw [Finset.mem_insert, h.split.mem_joinSupport]
  constructor
  · rintro (rfl | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact hx
    · exact (s7b_mem_pre ι₁ S c).mp hc
    · exact (s7b_mem_pre ι₂ S c).mp hc
  · intro hy
    by_cases hyx : y = x
    · exact Or.inl hyx
    · right
      rcases h.x_split y hyx (hS x hx y hy (Ne.symm hyx)) (hS y hy x hx hyx) with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact Or.inl ⟨c, (s7b_mem_pre ι₁ S c).mpr hy, rfl⟩
      · exact Or.inr ⟨c, (s7b_mem_pre ι₂ S c).mpr hy, rfl⟩

/-- **eq. s7c:sliding-bijection**, abstractly: independent sets of `R` containing the pivot `x`
correspond to pairs of independent sets of `R₁`, `R₂`; `S ↦ (S₁, S₂)` are the preimages, the
inverse is `(S₁, S₂) ↦ {x} ∪ ι₁ S₁ ∪ ι₂ S₂`. -/
def slidingEquiv [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) :
    {S : Finset γ // s7b_Indep R S ∧ x ∈ S} ≃
      {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂} where
  toFun S := (⟨s7b_pre ι₁ S.1, h.split.indep_pre₁ S.2.1⟩,
    ⟨s7b_pre ι₂ S.1, h.split.indep_pre₂ S.2.1⟩)
  invFun p := ⟨insert x (h.split.joinSupport p.1.1 p.2.1), h.indep_insert p.1.2 p.2.2,
    Finset.mem_insert_self _ _⟩
  left_inv S := Subtype.ext (h.insert_join_pre S.2.1 S.2.2)
  right_inv p := by
    ext1
    · exact Subtype.ext ((h.pre₁_insert _).trans (h.split.pre₁_joinSupport _ _))
    · exact Subtype.ext ((h.pre₂_insert _).trans (h.split.pre₂_joinSupport _ _))

theorem slidingEquiv_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x)
    (S : {S : Finset γ // s7b_Indep R S ∧ x ∈ S}) :
    ((h.slidingEquiv S).1.1 = s7b_pre ι₁ S.1) ∧ ((h.slidingEquiv S).2.1 = s7b_pre ι₂ S.1) :=
  ⟨rfl, rfl⟩

theorem slidingEquiv_symm_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    (h.slidingEquiv.symm p).1 = insert x (h.split.joinSupport p.1.1 p.2.1) := rfl

/-- The support of a sliding row is the pivot together with the two half supports; its cardinality
is `|S₁| + |S₂| + 1` (the sign `(−1)^{|S|}` of the state sum). -/
theorem card_symm_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    (h.slidingEquiv.symm p).1.card = p.1.1.card + p.2.1.card + 1 := by
  rw [slidingEquiv_symm_apply]
  have hx : x ∉ h.split.joinSupport p.1.1 p.2.1 := by
    intro hx
    rcases (h.split.mem_joinSupport _ _ x).mp hx with ⟨c, -, he⟩ | ⟨c, -, he⟩
    · exact h.x_not₁ c he
    · exact h.x_not₂ c he
  rw [Finset.card_insert_of_notMem hx, s7b_SupportSplit.joinSupport, Finset.card_union_of_disjoint,
    s7b_img, s7b_img, Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro y hy₁ hy₂
  obtain ⟨c₁, -, rfl⟩ := (s7b_mem_img _ _ y).mp hy₁
  obtain ⟨c₂, -, he⟩ := (s7b_mem_img _ _ _).mp hy₂
  exact h.split.disjoint c₁ c₂ he.symm

end s7b_PivotSplit

/-- The eligible support's cardinality is `|T₁| + |T₂|`. -/
theorem s7b_SupportSplit.card_symm_apply {R : γ → γ → Prop} {R₁ : γ₁ → γ₁ → Prop}
    {R₂ : γ₂ → γ₂ → Prop} {ι₁ : γ₁ → γ} {ι₂ : γ₂ → γ} [Fintype γ₁] [Fintype γ₂]
    (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    (h.eligibleEquiv.symm p).1.card = p.1.1.card + p.2.1.card := by
  rw [eligibleEquiv_symm_apply, joinSupport, Finset.card_union_of_disjoint, s7b_img, s7b_img,
    Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro y hy₁ hy₂
  obtain ⟨c₁, -, rfl⟩ := (s7b_mem_img _ _ y).mp hy₁
  obtain ⟨c₂, -, he⟩ := (s7b_mem_img _ _ _).mp hy₂
  exact h.disjoint c₁ c₂ he.symm

end S7BSupports


section S7BSide

/-! ### U110-B, part III: the halves on a SIDE polygon and the mark transport of a sliding row.
`P` is the wall centre, `Q` a generic side polygon; lem:wall-sides (V) (`vertex_sides`,
`VertexCrossingData`) gives `hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)`,
so the crossings and visits of the halves (part II) are crossings and visits of `Q`.  For a sliding
row `S ∋ x₋` the marks of `Q` are, apart from the second visit of `x₋` and the visits of the
crossings interlacing `x₋`, exactly the marks of `λ₁ ⊔ λ₂` (`s7b_slidingMark`); the smoothing
successor of `S` is the FIRST-RETURN map of the two halves' successors on that image
(`s7b_SlidingTransport.ret`, the geometric input of this row), whence owners, carriers and carrier
crossings correspond (part I). -/

/-- A crossing of the centre that is not contact-affected, read on a side polygon. -/
def s7b_sideCrossing {P Q : LabelledTuple n} {M a : ZMod n}
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (c : Crossing P) (hc : ¬ ContactAffected M a c.val) : Crossing Q :=
  ⟨c.val, (hQC _ hc).mpr c.property⟩

/-- The crossing of the side polygon carried by a crossing of `λ₁`. -/
def s7b_firstCrossingQ (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (c : Crossing (firstHalf P M a)) : Crossing Q :=
  s7b_sideCrossing hQC (s7b_firstHalfCrossing hn hsep hm c)
    (s7b_firstHalfCrossing_not_affected hn hsep hm c)

/-- The crossing of the side polygon carried by a crossing of `λ₂`. -/
def s7b_secondCrossingQ (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (c : Crossing (secondHalf P M a)) : Crossing Q :=
  s7b_sideCrossing hQC (s7b_secondHalfCrossing hn hsep hm c)
    (s7b_secondHalfCrossing_not_affected hn hsep hm c)

/-- A label in both half ranges is the contact edge `a`, reached only by the wrap labels. -/
theorem s7b_firstHalfIndex_eq_secondHalfEdgeIndex (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {i : ZMod (firstHalfSize M a)}
    {j : ZMod (secondHalfSize M a)} (h : firstHalfIndex M a i = secondHalfEdgeIndex M a j) :
    i = -1 ∧ j = 0 := by
  have hb := contactHalfSizes_bounds hn hsep
  have hi := i.val_lt
  have hj := j.val_lt
  have hd : firstHalfSize M a = contactDistance M a + 1 := rfl
  have hd' : secondHalfSize M a = n - contactDistance M a := rfl
  have hdn : contactDistance M a < n := ZMod.val_lt _
  have h1 : ((i.val : ℕ) : ZMod n) = ((contactDistance M a + j.val : ℕ) : ZMod n) := by
    have hc := contactDistance_cast M a
    simp only [firstHalfIndex, secondHalfEdgeIndex, cyclicRangeIndex] at h
    push_cast
    linear_combination h - hc
  have h2 : i.val = contactDistance M a + j.val := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hj0 : j.val = 0 := by omega
  have hi1 : i.val = contactDistance M a := by omega
  refine ⟨?_, (ZMod.val_eq_zero j).mp hj0⟩
  apply ZMod.val_injective
  have hl := last_index_val_succ (n := firstHalfSize M a)
  omega

theorem s7b_firstHalfIndex_ne_secondHalfIndex (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) (i : ZMod (firstHalfSize M a))
    {j : ZMod (secondHalfSize M a)} (hj : j ≠ 0) :
    firstHalfIndex M a i ≠ secondHalfIndex M a j := by
  intro h
  rw [secondHalfIndex_nonzero M a hj] at h
  exact hj (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep h).2

section Maps

variable (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) {P Q : LabelledTuple n}
  (hm : P M ∈ edgeInterior P a)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))

theorem s7b_firstCrossingQ_val (c : Crossing (firstHalf P M a)) :
    (s7b_firstCrossingQ hn hsep hm hQC c).val = c.val.image (firstHalfIndex M a) := rfl

theorem s7b_secondCrossingQ_val (c : Crossing (secondHalf P M a)) :
    (s7b_secondCrossingQ hn hsep hm hQC c).val = c.val.image (secondHalfEdgeIndex M a) := rfl

theorem s7b_firstCrossingQ_not_affected (c : Crossing (firstHalf P M a)) :
    ¬ ContactAffected M a (s7b_firstCrossingQ hn hsep hm hQC c).val :=
  s7b_firstHalfCrossing_not_affected hn hsep hm c

theorem s7b_secondCrossingQ_not_affected (c : Crossing (secondHalf P M a)) :
    ¬ ContactAffected M a (s7b_secondCrossingQ hn hsep hm hQC c).val :=
  s7b_secondHalfCrossing_not_affected hn hsep hm c

theorem s7b_firstCrossingQ_injective : Function.Injective (s7b_firstCrossingQ hn hsep hm hQC) := by
  intro c d h
  exact Subtype.ext (Finset.image_injective (firstHalfIndex_injective M a) (congrArg Subtype.val h))

theorem s7b_secondCrossingQ_injective :
    Function.Injective (s7b_secondCrossingQ hn hsep hm hQC) := by
  intro c d h
  exact Subtype.ext
    (Finset.image_injective (secondHalfEdgeIndex_injective M a) (congrArg Subtype.val h))

/-- A crossing of `λ₁` and a crossing of `λ₂` never carry the same crossing of `Q`. -/
theorem s7b_firstCrossingQ_ne_secondCrossingQ (c : Crossing (firstHalf P M a))
    (c' : Crossing (secondHalf P M a)) :
    s7b_firstCrossingQ hn hsep hm hQC c ≠ s7b_secondCrossingQ hn hsep hm hQC c' := by
  intro h
  have hv := congrArg Subtype.val h
  rw [s7b_firstCrossingQ_val, s7b_secondCrossingQ_val] at hv
  obtain ⟨i, j, hs, hr, -⟩ := c.property
  have hij : i ≠ j := (remote_endpoints i j hr).1.symm
  have hmem : ∀ k ∈ c.val, firstHalfIndex M a k = a := by
    intro k hk
    have : firstHalfIndex M a k ∈ c'.val.image (secondHalfEdgeIndex M a) := by
      rw [← hv]; exact Finset.mem_image_of_mem _ hk
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp this
    have := (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep hl.symm).1
    rw [this, firstHalfIndex_last]
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  exact hij (firstHalfIndex_injective M a ((hmem i hi).trans (hmem j hj).symm))

/-- The visit of `Q` carried by a visit of `λ₁`. -/
def s7b_firstVisitQ (v : Visit (firstHalf P M a)) : Visit Q :=
  ⟨s7b_firstCrossingQ hn hsep hm hQC v.1,
    ⟨firstHalfIndex M a v.2.val, Finset.mem_image_of_mem _ v.2.property⟩⟩

/-- The visit of `Q` carried by a visit of `λ₂`. -/
def s7b_secondVisitQ (v : Visit (secondHalf P M a)) : Visit Q :=
  ⟨s7b_secondCrossingQ hn hsep hm hQC v.1,
    ⟨secondHalfEdgeIndex M a v.2.val, Finset.mem_image_of_mem _ v.2.property⟩⟩

theorem s7b_firstVisitQ_fst (v : Visit (firstHalf P M a)) :
    (s7b_firstVisitQ hn hsep hm hQC v).1 = s7b_firstCrossingQ hn hsep hm hQC v.1 := rfl

theorem s7b_firstVisitQ_edge (v : Visit (firstHalf P M a)) :
    (s7b_firstVisitQ hn hsep hm hQC v).2.val = firstHalfIndex M a v.2.val := rfl

theorem s7b_secondVisitQ_fst (v : Visit (secondHalf P M a)) :
    (s7b_secondVisitQ hn hsep hm hQC v).1 = s7b_secondCrossingQ hn hsep hm hQC v.1 := rfl

theorem s7b_secondVisitQ_edge (v : Visit (secondHalf P M a)) :
    (s7b_secondVisitQ hn hsep hm hQC v).2.val = secondHalfEdgeIndex M a v.2.val := rfl

theorem s7b_firstVisitQ_injective : Function.Injective (s7b_firstVisitQ hn hsep hm hQC) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hc : c = d := s7b_firstCrossingQ_injective hn hsep hm hQC (congrArg Sigma.fst h)
  subst hc
  have hi : firstHalfIndex M a i.val = firstHalfIndex M a j.val :=
    congrArg (fun w : Visit Q => w.2.val) h
  rw [Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (Subtype.ext (firstHalfIndex_injective M a hi))⟩

theorem s7b_secondVisitQ_injective : Function.Injective (s7b_secondVisitQ hn hsep hm hQC) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hc : c = d := s7b_secondCrossingQ_injective hn hsep hm hQC (congrArg Sigma.fst h)
  subst hc
  have hi : secondHalfEdgeIndex M a i.val = secondHalfEdgeIndex M a j.val :=
    congrArg (fun w : Visit Q => w.2.val) h
  rw [Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (Subtype.ext (secondHalfEdgeIndex_injective M a hi))⟩

theorem s7b_firstVisitQ_visitTwin (v : Visit (firstHalf P M a)) :
    s7b_firstVisitQ hn hsep hm hQC (visitTwin v) = visitTwin (s7b_firstVisitQ hn hsep hm hQC v) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne v (s7b_firstVisitQ_injective hn hsep hm hQC h)

theorem s7b_secondVisitQ_visitTwin (v : Visit (secondHalf P M a)) :
    s7b_secondVisitQ hn hsep hm hQC (visitTwin v) =
      visitTwin (s7b_secondVisitQ hn hsep hm hQC v) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne v (s7b_secondVisitQ_injective hn hsep hm hQC h)

/-- Every visit of the image of a crossing of `λ₁` is the image of a visit of that crossing. -/
theorem s7b_visit_of_firstCrossingQ (v : Visit Q) (c : Crossing (firstHalf P M a))
    (hv : v.1 = s7b_firstCrossingQ hn hsep hm hQC c) :
    ∃ w : Visit (firstHalf P M a), w.1 = c ∧ s7b_firstVisitQ hn hsep hm hQC w = v := by
  obtain ⟨c', i⟩ := v
  change c' = _ at hv
  subst hv
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp i.property
  refine ⟨⟨c, ⟨j, hj⟩⟩, rfl, ?_⟩
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hji))

theorem s7b_visit_of_secondCrossingQ (v : Visit Q) (c : Crossing (secondHalf P M a))
    (hv : v.1 = s7b_secondCrossingQ hn hsep hm hQC c) :
    ∃ w : Visit (secondHalf P M a), w.1 = c ∧ s7b_secondVisitQ hn hsep hm hQC w = v := by
  obtain ⟨c', i⟩ := v
  change c' = _ at hv
  subst hv
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp i.property
  refine ⟨⟨c, ⟨j, hj⟩⟩, rfl, ?_⟩
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hji))

/-! #### The mark map of a sliding row -/

/-- The marks of `λ₁ ⊔ λ₂` inside the marks of `Q`, for a sliding row through the contact visit
`vm` (the visit of `x₋` on the leg edge `M−1` / `M`; its twin on `E_a` has no counterpart): the
vertices `M, …, a` of `λ₁` and `a+1, …, M−1` of `λ₂` are the vertices of `Q`, the vertex `0 = μ_M` of
`λ₂` is the smoothing corner `vm`, the visits are carried by `s7b_firstVisitQ`/`s7b_secondVisitQ`. -/
def s7b_slidingMark (vm : Visit Q) :
    Mark (firstHalf P M a) ⊕ Mark (secondHalf P M a) → Mark Q
  | Sum.inl (Sum.inl i) => Sum.inl (firstHalfIndex M a i)
  | Sum.inl (Sum.inr v) => Sum.inr (s7b_firstVisitQ hn hsep hm hQC v)
  | Sum.inr (Sum.inl i) => if i = 0 then Sum.inr vm else Sum.inl (secondHalfIndex M a i)
  | Sum.inr (Sum.inr v) => Sum.inr (s7b_secondVisitQ hn hsep hm hQC v)

theorem s7b_slidingMark_inl_inl (vm : Visit Q) (i : ZMod (firstHalfSize M a)) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inl (Sum.inl i)) = Sum.inl (firstHalfIndex M a i) := rfl

theorem s7b_slidingMark_inl_inr (vm : Visit Q) (v : Visit (firstHalf P M a)) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inl (Sum.inr v)) =
      Sum.inr (s7b_firstVisitQ hn hsep hm hQC v) := rfl

theorem s7b_slidingMark_inr_inl_zero (vm : Visit Q) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inr (Sum.inl 0)) = Sum.inr vm := by
  simp [s7b_slidingMark]

theorem s7b_slidingMark_inr_inl (vm : Visit Q) {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inr (Sum.inl i)) = Sum.inl (secondHalfIndex M a i) := by
  simp [s7b_slidingMark, hi]

theorem s7b_slidingMark_inr_inr (vm : Visit Q) (v : Visit (secondHalf P M a)) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inr (Sum.inr v)) =
      Sum.inr (s7b_secondVisitQ hn hsep hm hQC v) := rfl

theorem s7b_slidingMark_injective (vm : Visit Q) (hvm : ContactAffected M a vm.1.val) :
    Function.Injective (s7b_slidingMark hn hsep hm hQC vm) := by
  have hvm₁ : ∀ v : Visit (firstHalf P M a), s7b_firstVisitQ hn hsep hm hQC v ≠ vm := by
    intro v h
    exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1 (by
      rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, h]; exact hvm)
  have hvm₂ : ∀ v : Visit (secondHalf P M a), s7b_secondVisitQ hn hsep hm hQC v ≠ vm := by
    intro v h
    exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1 (by
      rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, h]; exact hvm)
  have h12 : ∀ (v : Visit (firstHalf P M a)) (w : Visit (secondHalf P M a)),
      s7b_firstVisitQ hn hsep hm hQC v ≠ s7b_secondVisitQ hn hsep hm hQC w := by
    intro v w h
    exact s7b_firstCrossingQ_ne_secondCrossingQ hn hsep hm hQC v.1 w.1 (congrArg Sigma.fst h)
  rintro (m | m) (m' | m') h
  · rcases m with i | v <;> rcases m' with i' | v'
    · exact congrArg (Sum.inl ∘ Sum.inl) (firstHalfIndex_injective M a (Sum.inl.inj h))
    · exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inr_ne_inl
    · exact congrArg (Sum.inl ∘ Sum.inr) (s7b_firstVisitQ_injective hn hsep hm hQC (Sum.inr.inj h))
  · rcases m with i | v <;> rcases m' with i' | v'
    · by_cases hi' : i' = 0
      · subst hi'
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd h Sum.inl_ne_inr
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
        exact absurd (Sum.inl.inj h) (s7b_firstHalfIndex_ne_secondHalfIndex hn hsep i hi')
    · exact absurd h Sum.inl_ne_inr
    · by_cases hi' : i' = 0
      · subst hi'
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd (Sum.inr.inj h) (hvm₁ v)
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
        exact absurd h Sum.inr_ne_inl
    · exact absurd (Sum.inr.inj h) (h12 v v')
  · rcases m with i | v <;> rcases m' with i' | v'
    · by_cases hi : i = 0
      · subst hi
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd h Sum.inr_ne_inl
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at h
        exact absurd (Sum.inl.inj h).symm (s7b_firstHalfIndex_ne_secondHalfIndex hn hsep i' hi)
    · by_cases hi : i = 0
      · subst hi
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd (Sum.inr.inj h).symm (hvm₁ v')
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at h
        exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inr_ne_inl
    · exact absurd (Sum.inr.inj h).symm (h12 v' v)
  · rcases m with i | v <;> rcases m' with i' | v'
    · by_cases hi : i = 0
      · subst hi
        by_cases hi' : i' = 0
        · subst hi'; rfl
        · rw [s7b_slidingMark_inr_inl_zero, s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
          exact absurd h Sum.inr_ne_inl
      · by_cases hi' : i' = 0
        · subst hi'
          rw [s7b_slidingMark_inr_inl_zero, s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at h
          exact absurd h Sum.inl_ne_inr
        · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi,
            s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
          exact congrArg (Sum.inr ∘ Sum.inl) (secondHalfIndex_injective M a (Sum.inl.inj h))
    · by_cases hi : i = 0
      · subst hi
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd (Sum.inr.inj h).symm (hvm₂ v')
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at h
        exact absurd h Sum.inl_ne_inr
    · by_cases hi' : i' = 0
      · subst hi'
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd (Sum.inr.inj h) (hvm₂ v)
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
        exact absurd h Sum.inr_ne_inl
    · exact congrArg (Sum.inr ∘ Sum.inr) (s7b_secondVisitQ_injective hn hsep hm hQC (Sum.inr.inj h))

end Maps

end S7BSide

section S7BSlidingTransport

/-! ### U110-B, part III (continued): the sliding-row transport structure and its consequences.
The field `ret` (the smoothing successor of `S` is the first-return map of the halves' successors
on the image of `s7b_slidingMark`) is the ONLY geometric input; everything below is derived from
it with part I: owners, the carrier correspondence `Component hn hQ S ≃ Component λ₁ S₁ ⊕
Component λ₂ S₂`, and (with the pivot split of part IV) the carrier crossings and `m_Q`. -/

/-- A sliding row `S ∋ x₋ = vm.1` of the side polygon `Q` with its two half supports `S₁, S₂`
(the preimages of `S`), and the first-return law for the smoothing successors. -/
structure s7b_SlidingTransport (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
    (S : Finset (Crossing Q)) (S₁ : Finset (Crossing (firstHalf P M a)))
    (S₂ : Finset (Crossing (secondHalf P M a))) (vm : Visit Q) : Prop where
  affected : ContactAffected M a vm.1.val
  pivot_mem : vm.1 ∈ S
  first_pre : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S
  second_pre : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S
  ret : s7b_ReturnTransport (smoothingSuccessor hn hQ S)
    (Equiv.Perm.sumCongr (smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
      (smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂))
    (s7b_slidingMark hn hsep hm hQC vm)

namespace s7b_SlidingTransport

variable {hn : 3 ≤ n} {M a : ZMod n} {hsep : ContactSeparated M a} {P Q : LabelledTuple n}
  {hm : P M ∈ edgeInterior P a}
  {hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)}
  {hQ : Generic Q} {h₁ : Generic (firstHalf P M a)} {h₂ : Generic (secondHalf P M a)}
  {S : Finset (Crossing Q)} {S₁ : Finset (Crossing (firstHalf P M a))}
  {S₂ : Finset (Crossing (secondHalf P M a))} {vm : Visit Q}

/-- Two marks of `λ₁` have one owner iff their images have one owner on `Q`. -/
theorem owner_inl_iff (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m m' : Mark (firstHalf P M a)) :
    owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m)) =
        owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m')) ↔
      owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m =
        owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m' := by
  rw [owner_eq_iff, owner_eq_iff, h.ret.sameCycle_iff, s7b_sumCongr_sameCycle_inl]

theorem owner_inr_iff (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m m' : Mark (secondHalf P M a)) :
    owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m)) =
        owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m')) ↔
      owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m =
        owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m' := by
  rw [owner_eq_iff, owner_eq_iff, h.ret.sameCycle_iff, s7b_sumCongr_sameCycle_inr]

/-- Marks of the two different halves never share an owner on `Q`. -/
theorem owner_inl_ne_inr (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m : Mark (firstHalf P M a)) (m' : Mark (secondHalf P M a)) :
    owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m)) ≠
      owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m')) := by
  rw [Ne, owner_eq_iff, h.ret.sameCycle_iff]
  exact s7b_sumCongr_not_sameCycle _ _ m m'

/-- **The carrier correspondence of a sliding row**: the carriers of `S` on `Q` are the carriers of
`S₁` on `λ₁` together with those of `S₂` on `λ₂` (eq. s7c:sliding-residual). -/
def componentEquiv (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) :
    Component hn hQ S ≃
      Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ ⊕
        Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ :=
  h.ret.cycleEquiv.symm.trans (s7b_sumCongr_cycleEquiv _ _)

theorem componentEquiv_owner_inl (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m : Mark (firstHalf P M a)) :
    h.componentEquiv (owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m))) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m) := by
  have he : owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m)) =
      h.ret.cycleEquiv (Quotient.mk _ (Sum.inl m)) := rfl
  show s7b_sumCongr_cycleEquiv _ _
    (h.ret.cycleEquiv.symm (owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m)))) = _
  rw [he, Equiv.symm_apply_apply]
  rfl

theorem componentEquiv_owner_inr (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m : Mark (secondHalf P M a)) :
    h.componentEquiv (owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m))) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m) := by
  have he : owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m)) =
      h.ret.cycleEquiv (Quotient.mk _ (Sum.inr m)) := rfl
  show s7b_sumCongr_cycleEquiv _ _
    (h.ret.cycleEquiv.symm (owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m)))) = _
  rw [he, Equiv.symm_apply_apply]
  rfl

/-- The owner on `Q` of a visit carried from `λ₁`, in terms of the half owner. -/
theorem componentEquiv_owner_firstVisit
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (w : Visit (firstHalf P M a)) :
    h.componentEquiv (owner hn hQ S (Sum.inr (s7b_firstVisitQ hn hsep hm hQC w))) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ (Sum.inr w)) :=
  h.componentEquiv_owner_inl (Sum.inr w)

theorem componentEquiv_owner_secondVisit
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (w : Visit (secondHalf P M a)) :
    h.componentEquiv (owner hn hQ S (Sum.inr (s7b_secondVisitQ hn hsep hm hQC w))) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ (Sum.inr w)) :=
  h.componentEquiv_owner_inr (Sum.inr w)

/-- The carrier through the contact vertex `μ_M` on `Q` corresponds to `λ₁`'s carrier through its
vertex `0 = μ_M`. -/
theorem componentEquiv_owner_vertexM (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) :
    h.componentEquiv (owner hn hQ S (Sum.inl M)) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ (Sum.inl 0)) := by
  have he : (Sum.inl M : Mark Q) = s7b_slidingMark hn hsep hm hQC vm (Sum.inl (Sum.inl 0)) := by
    rw [s7b_slidingMark_inl_inl, firstHalfIndex_zero]
  rw [he, h.componentEquiv_owner_inl]

/-- The carrier through the contact visit `vm` on `Q` corresponds to `λ₂`'s carrier through its
vertex `0 = μ_M`. -/
theorem componentEquiv_owner_pivot (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) :
    h.componentEquiv (owner hn hQ S (Sum.inr vm)) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ (Sum.inl 0)) := by
  have he : (Sum.inr vm : Mark Q) = s7b_slidingMark hn hsep hm hQC vm (Sum.inr (Sum.inl 0)) :=
    (s7b_slidingMark_inr_inl_zero hn hsep hm hQC vm).symm
  rw [he, h.componentEquiv_owner_inr]

/-- A carried crossing of `λ₁` is a crossing of the carrier `q` of `S` iff it is a crossing of the
corresponding half carrier. -/
theorem firstCrossingQ_mem_carrierCrossings_iff
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (c : Crossing (firstHalf P M a))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : h.componentEquiv q = Sum.inl q₁) :
    s7b_firstCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ S q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_firstCrossingQ hn hsep hm hQC c ∈ S ↔ c ∈ S₁ := by
    rw [h.first_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_firstVisitQ hn hsep hm hQC w) (by
      rw [s7b_firstVisitQ_fst, hw])
    have := h.componentEquiv_owner_firstVisit w
    rw [hv, hq] at this
    exact (Sum.inl.inj this).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC v c hv
    apply h.componentEquiv.injective
    rw [h.componentEquiv_owner_firstVisit, hall w hw, hq]

theorem secondCrossingQ_mem_carrierCrossings_iff
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (c : Crossing (secondHalf P M a))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : h.componentEquiv q = Sum.inr q₂) :
    s7b_secondCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ S q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_secondCrossingQ hn hsep hm hQC c ∈ S ↔ c ∈ S₂ := by
    rw [h.second_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_secondVisitQ hn hsep hm hQC w) (by
      rw [s7b_secondVisitQ_fst, hw])
    have := h.componentEquiv_owner_secondVisit w
    rw [hv, hq] at this
    exact (Sum.inr.inj this).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC v c hv
    apply h.componentEquiv.injective
    rw [h.componentEquiv_owner_secondVisit, hall w hw, hq]

/-- A carried crossing of `λ₂` is never a crossing of a carrier corresponding to a carrier of `λ₁`
(and symmetrically). -/
theorem secondCrossingQ_notMem_carrierCrossings
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (c : Crossing (secondHalf P M a))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : h.componentEquiv q = Sum.inl q₁) :
    s7b_secondCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ S q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_secondVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := h.componentEquiv_owner_secondVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inl_ne_inr this

theorem firstCrossingQ_notMem_carrierCrossings
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (c : Crossing (firstHalf P M a))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : h.componentEquiv q = Sum.inr q₂) :
    s7b_firstCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ S q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_firstVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := h.componentEquiv_owner_firstVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inr_ne_inl this

/-- Under the pivot split (part IV: the crossings of `Q` off the two images are `x₋` and the
crossings interlacing it), every carrier crossing of `S` is carried from a half: a crossing
interlacing `x₋ ∈ S` has its visits on two different carriers (lem:carriers (iii)). -/
theorem carrierCrossings_mem_range
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S) {y : Crossing Q}
    (hy : y ∈ carrierCrossings hn hQ S q) :
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪
      Set.range (s7b_secondCrossingQ hn hsep hm hQC) := by
  rw [mem_carrierCrossings] at hy
  have hyx : y ≠ vm.1 := fun he => hy.1 (he ▸ h.pivot_mem)
  have hnot : ∀ z : Crossing Q, Interlaces hn hQ y z → z ∈ S → False := by
    intro z hz hzS
    have hN : y ∈ supportNeighbors hn hQ S := (mem_supportNeighbors hn hQ S y).mpr ⟨z, hzS, hz⟩
    obtain ⟨i, j, hs, -, -⟩ := y.property
    have hi : i ∈ y.val := by rw [hs]; simp
    have hsep' := (carriers_lemma hn hQ hS).neighbor_visits_separated y hN ⟨y, ⟨i, hi⟩⟩ rfl
    exact hsep' ((hy.2 ⟨y, ⟨i, hi⟩⟩ rfl).trans (hy.2 (visitTwin ⟨y, ⟨i, hi⟩⟩) rfl).symm)
  exact hsplit.x_split y hyx (fun hI => hnot _ (interlaces_symm hn hQ hI) h.pivot_mem)
    (fun hI => hnot _ hI h.pivot_mem)

/-- **`m_Q` of a carrier corresponding to a carrier of `λ₁`**: its crossings are exactly the carried
crossings of the half carrier, so the counts agree (eq. s7c:sliding-residual for the self-crossings;
the input to the coefficient transport of U110-D and to the slot `d_Q`). -/
theorem carrierCrossings_eq_img_first
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) (hq : h.componentEquiv q = Sum.inl q₁) :
    carrierCrossings hn hQ S q =
      s7b_img (s7b_firstCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases h.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨c, (h.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mp hy, rfl⟩
    · exact absurd hy (h.secondCrossingQ_notMem_carrierCrossings c q q₁ hq)
  · rintro ⟨c, hc, rfl⟩
    exact (h.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mpr hc

theorem carrierCrossings_eq_img_second
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hq : h.componentEquiv q = Sum.inr q₂) :
    carrierCrossings hn hQ S q =
      s7b_img (s7b_secondCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases h.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact absurd hy (h.firstCrossingQ_notMem_carrierCrossings c q q₂ hq)
    · exact ⟨c, (h.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mp hy, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact (h.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mpr hc

theorem carrierCrossingCount_eq_first
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) (hq : h.componentEquiv q = Sum.inl q₁) :
    carrierCrossingCount hn hQ S q =
      carrierCrossingCount (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := by
  unfold carrierCrossingCount
  rw [h.carrierCrossings_eq_img_first hsplit hS q q₁ hq, s7b_img, Finset.card_map]

theorem carrierCrossingCount_eq_second
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hq : h.componentEquiv q = Sum.inr q₂) :
    carrierCrossingCount hn hQ S q =
      carrierCrossingCount (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := by
  unfold carrierCrossingCount
  rw [h.carrierCrossings_eq_img_second hsplit hS q q₂ hq, s7b_img, Finset.card_map]

end s7b_SlidingTransport

/-- **eq. s7c:sliding-bijection on the actual decompositions**: given the pivot split for the
interlacement relations (the geometric input of U110-A/B), the sliding rows `{S ∈ Ind(G_Q) : x₋ ∈ S}`
correspond to `Ind(G_{λ₁}) × Ind(G_{λ₂})`. -/
def s7b_slidingDecompositionEquiv (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a)) (x : Crossing Q)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x) :
    {S : Finset (Crossing Q) // IsDecomposition hn hQ S ∧ x ∈ S} ≃
      {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂} :=
  (Equiv.subtypeEquivRight fun S => by
      rw [s7b_isDecomposition_iff_indep]).trans
    (hsplit.slidingEquiv.trans
      (Equiv.prodCongr (Equiv.subtypeEquivRight fun S₁ => by rw [s7b_isDecomposition_iff_indep])
        (Equiv.subtypeEquivRight fun S₂ => by rw [s7b_isDecomposition_iff_indep])))

/-- **eq. s7c:eligible-bijection on the actual decompositions**: the eligible supports of the
newborn-free side `P₀` (no crossing off the two half images) correspond to `Ind(G_{λ₁}) × Ind(G_{λ₂})`. -/
def s7b_eligibleDecompositionEquiv (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
    (hsplit : s7b_SupportSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC)) :
    {T : Finset (Crossing Q) // IsDecomposition hn hQ T ∧
        ∀ y ∈ T, y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪
          Set.range (s7b_secondCrossingQ hn hsep hm hQC)} ≃
      {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂} :=
  (Equiv.subtypeEquivRight fun T => by
      rw [s7b_isDecomposition_iff_indep]).trans
    (hsplit.eligibleEquiv.trans
      (Equiv.prodCongr (Equiv.subtypeEquivRight fun S₁ => by rw [s7b_isDecomposition_iff_indep])
        (Equiv.subtypeEquivRight fun S₂ => by rw [s7b_isDecomposition_iff_indep])))

end S7BSlidingTransport

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
