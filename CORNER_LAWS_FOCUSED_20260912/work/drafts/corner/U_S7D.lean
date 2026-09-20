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

/-! ### U110-D helpers (prefix `s7d_`): coefficient transport for spectators / relocated carriers -/

/-- `List.next` commutes with an injective-on-the-list map. -/
theorem s7d_next_map {α β : Type*} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hnd : (l.map f).Nodup) (x : α) (hx : x ∈ l) :
    (l.map f).next (f x) (List.mem_map_of_mem hx) = f (l.next x hx) := by
  have hl : l.Nodup := hnd.of_map f
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi' : i < (l.map f).length := by rw [List.length_map]; exact hi
  have h := List.next_getElem (l.map f) hnd i hi'
  simp only [List.getElem_map, List.length_map] at h
  rw [List.next_getElem l hl i hi]
  exact h

/-- The record-level bridge: a visit map carrying the restricted Gauss list of `X` to a rotation of the
restricted Gauss list of `Y`, commuting with the twin on `X`-visits and preserving the positive over bit,
induces a record isomorphism of the abstract restricted Gauss records (`gaussRecord`, KL0). -/
def s7d_gaussRecordIso {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}
    (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q) (X : Finset (Crossing P))
    (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q)
    (hrot : (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ))
    (htwin : ∀ v : Visit P, v.1 ∈ X → φ (visitTwin v) = visitTwin (φ v))
    (hbit : ∀ v : Visit P, v.1 ∈ X → CB.positiveOverBit (φ v) = CB.positiveOverBit v) :
    RecordIso (CB.gaussRecord hcP X) (CB.gaussRecord hcQ Y) :=
  have hndm : ((CB.gaussList hcP X).map φ).Nodup := hrot.nodup_iff.mp (CB.kl0_gaussList_nodup hcQ Y)
  have hmemφ : ∀ v : Visit P, v.1 ∈ X → (φ v).1 ∈ Y := fun v hv => by
    rw [← CB.kl0_mem_gaussList hcQ Y, hrot.mem_iff]
    exact List.mem_map_of_mem ((CB.kl0_mem_gaussList hcP X v).mpr hv)
  let f : {v : Visit P // v.1 ∈ X} → {w : Visit Q // w.1 ∈ Y} := fun v => ⟨φ v.1, hmemφ v.1 v.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      have h' : φ v.1 = φ w.1 := congrArg Subtype.val h
      exact Subtype.ext (List.inj_on_of_nodup_map hndm ((CB.kl0_mem_gaussList hcP X v.1).mpr v.2)
        ((CB.kl0_mem_gaussList hcP X w.1).mpr w.2) h')
    · intro w
      have hw : w.1 ∈ (CB.gaussList hcP X).map φ := by
        rw [← hrot.mem_iff]
        exact (CB.kl0_mem_gaussList hcQ Y w.1).mpr w.2
      obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hw
      exact ⟨⟨v, (CB.kl0_mem_gaussList hcP X v).mp hv⟩, Subtype.ext hvw⟩
  { e := Equiv.refl Unit
    Φ := Equiv.ofBijective f hf
    comp_eq := fun _ => Subsingleton.elim (α := Unit) _ _
    succ_eq := fun v => by
      apply Subtype.ext
      have hv : v.1 ∈ CB.gaussList hcP X := (CB.kl0_mem_gaussList hcP X v.1).mpr v.2
      have hfv : (f v).1 ∈ CB.gaussList hcQ Y := (CB.kl0_mem_gaussList hcQ Y _).mpr (f v).2
      show φ (CB.gaussSucc hcP X v).1 = (CB.gaussSucc hcQ Y (f v)).1
      rw [CB.gaussSucc_val hcP X v hv, CB.gaussSucc_val hcQ Y (f v) hfv,
        List.isRotated_next_eq hrot (CB.kl0_gaussList_nodup hcQ Y) hfv]
      exact (s7d_next_map (CB.gaussList hcP X) φ hndm v.1 hv).symm
    pair_eq := fun v => by
      apply Subtype.ext
      show φ (visitTwin v.1) = visitTwin (φ v.1)
      exact htwin v.1 v.2
    bit_eq := fun v => hbit v.1 v.2
    sgn_eq := fun _ => rfl }

/-- Two restricted Gauss lists with the same members (via `φ`) and `φ` strictly increasing in the traversal
key on `X`-visits are literally equal after mapping (both are the strictly key-sorted lists of their members). -/
theorem s7d_gaussList_eq_of_strictMono {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}
    (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q) (X : Finset (Crossing P))
    (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w)) :
    CB.gaussList hcQ Y = (CB.gaussList hcP X).map φ := by
  have hsortP : (CB.gaussList hcP X).Pairwise
      (fun v w => geometricVisitKey hcP v < geometricVisitKey hcP w) :=
    CB.kl2_gaussList_pairwise_lt hcP X
  have hsortQ : (CB.gaussList hcQ Y).Pairwise
      (fun v w => geometricVisitKey hcQ v < geometricVisitKey hcQ w) :=
    CB.kl2_gaussList_pairwise_lt hcQ Y
  have hsortM : ((CB.gaussList hcP X).map φ).Pairwise
      (fun v w => geometricVisitKey hcQ v < geometricVisitKey hcQ w) := by
    rw [List.pairwise_map]
    refine (List.Pairwise.and_mem.mp hsortP).imp ?_
    rintro v w ⟨hv, hw, hlt⟩
    exact hmono v w ((CB.kl0_mem_gaussList hcP X v).mp hv) ((CB.kl0_mem_gaussList hcP X w).mp hw) hlt
  -- the mapped list has no duplicates (strict monotonicity forces injectivity on `X`-visits)
  have hnd : ((CB.gaussList hcP X).map φ).Nodup := by
    rw [List.nodup_iff_pairwise_ne] at *
    exact hsortM.imp fun h => ne_of_lt h |> fun h' => fun e => h' (by rw [e])
  have hperm : (CB.gaussList hcQ Y).Perm ((CB.gaussList hcP X).map φ) := by
    rw [List.perm_ext_iff_of_nodup (CB.kl0_gaussList_nodup hcQ Y) hnd]
    intro w
    rw [CB.kl0_mem_gaussList, hmem, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (CB.kl0_mem_gaussList hcP X v).mpr hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (CB.kl0_mem_gaussList hcP X v).mp hv, rfl⟩
  exact List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _))
    hsortQ hsortM hperm

omit [NeZero n] in
/-- The positive over bit is `det(d_v, d_{τ v}) > 0`: equivalent determinant signs give equal bits. -/
theorem s7d_positiveOverBit_eq_of_det_pos_iff {m : ℕ} [NeZero m] {P : LabelledTuple n}
    {Q : LabelledTuple m} (v : Visit P) (w : Visit Q)
    (h : 0 < det (edge Q w.2.val) (edge Q (visitTwin w).2.val) ↔
      0 < det (edge P v.2.val) (edge P (visitTwin v).2.val)) :
    CB.positiveOverBit w = CB.positiveOverBit v := by
  unfold CB.positiveOverBit
  exact decide_eq_decide.mpr h

omit [NeZero n] in
/-- Determinants scale by the product of positive factors. -/
theorem s7d_det_smul_smul (c d : ℝ) (u w : Plane) : det (c • u) (d • w) = (c * d) * det u w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

omit [NeZero n] in
/-- Relocated carriers whose edge directions at the visit and at its twin are POSITIVE multiples of the
originals (the cut edges of a half, or the corner edges `corner_polygons.2.1`) keep the over bit. -/
theorem s7d_positiveOverBit_eq_of_smul {m : ℕ} [NeZero m] {P : LabelledTuple n}
    {Q : LabelledTuple m} (v : Visit P) (w : Visit Q) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (h1 : edge Q w.2.val = c • edge P v.2.val)
    (h2 : edge Q (visitTwin w).2.val = d • edge P (visitTwin v).2.val) :
    CB.positiveOverBit w = CB.positiveOverBit v := by
  apply s7d_positiveOverBit_eq_of_det_pos_iff
  rw [h1, h2, s7d_det_smul_smul]
  constructor
  · intro h
    exact pos_of_mul_pos_right h (mul_pos hc hd).le
  · intro h
    exact mul_pos (mul_pos hc hd) h

omit [NeZero n] in
/-- The positive over bit is read off the sign of `det(d_v, d_{τ v})`: equal crossing signs at a visit and
its image give equal bits. -/
theorem s7d_positiveOverBit_eq_of_crossingSign {m : ℕ} [NeZero m] {P : LabelledTuple n}
    {Q : LabelledTuple m} (v : Visit P) (w : Visit Q)
    (h : crossingSign Q w.2.val (visitTwin w).2.val = crossingSign P v.2.val (visitTwin v).2.val) :
    CB.positiveOverBit w = CB.positiveOverBit v := by
  unfold CB.positiveOverBit
  unfold crossingSign at h
  by_cases hp : 0 < det (edge P v.2.val) (edge P (visitTwin v).2.val)
  · have hq : 0 < det (edge Q w.2.val) (edge Q (visitTwin w).2.val) := by
      rw [← sign_eq_one_iff, h, sign_eq_one_iff]; exact hp
    simp [hp, hq]
  · have hq : ¬ 0 < det (edge Q w.2.val) (edge Q (visitTwin w).2.val) := by
      rw [← sign_eq_one_iff, h, sign_eq_one_iff]; exact hp
    simp [hp, hq]

/-! #### The coefficient transport proper: `H⁺`, `m`, `d` and `c` of two carriers with isomorphic
restricted Gauss records and equal rotations agree (across polygons of different sizes). -/

/-- `H⁺_q = H⁺_{q'}` when the abstract restricted Gauss records of the two carriers are isomorphic
(the CB record bridge `positiveLiftRecordIso` on both sides and lc:presentations, via `P_eq_homfly`). -/
theorem s7d_cornerHomfly_eq_of_recordIso {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (h : Nonempty (RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q))
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q')))) :
    cornerHomfly hn hP S q hS = cornerHomfly hm hQ T q' hT := by
  unfold cornerHomfly
  rw [← P_eq_homfly, ← P_eq_homfly]
  exact presentations _ _ ⟨(CB.positiveLiftRecordIso hn hP hS q).trans
    (h.some.trans (CB.positiveLiftRecordIso hm hQ hT q').symm)⟩

/-- `m_q = m_{q'}`: a record isomorphism preserves the number of occurrences, which is twice the number of
crossings of the carrier (`kl1_card_retained`). -/
theorem s7d_carrierCrossingCount_eq_of_recordIso {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (q : Component hn hP S)
    {T : Finset (Crossing Q)} (q' : Component hm hQ T)
    (h : Nonempty (RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q))
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q')))) :
    carrierCrossingCount hn hP S q = carrierCrossingCount hm hQ T q' := by
  have h1 := h.some.card_M_eq
  have e1 : Fintype.card (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q)).M =
      Fintype.card {u : Visit P // u.1 ∈ carrierCrossings hn hP S q} :=
    Fintype.card_congr (Equiv.refl _)
  have e2 : Fintype.card (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q')).M =
      Fintype.card {u : Visit Q // u.1 ∈ carrierCrossings hm hQ T q'} :=
    Fintype.card_congr (Equiv.refl _)
  rw [e1, e2, CB.kl1_card_retained hn hP q, CB.kl1_card_retained hm hQ q'] at h1
  rw [carrierCrossingCount_eq_card, carrierCrossingCount_eq_card]
  omega

/-- `d_q = d_{q'}` from the record isomorphism and equal (real) rotations. -/
theorem s7d_cornerSlot_eq_of_recordIso {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (q : Component hn hP S)
    {T : Finset (Crossing Q)} (q' : Component hm hQ T)
    (h : Nonempty (RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q))
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q'))))
    (hrot : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerSlot hn hP S q = cornerSlot hm hQ T q' := by
  unfold cornerSlot carrierRotationInt
  rw [s7d_carrierCrossingCount_eq_of_recordIso hn hm hP hQ q q' h, hrot]

/-- **Coefficient transport.** `c(q) = c(q')` for two carriers (of decompositions of possibly different
generic polygons) with isomorphic restricted Gauss records and equal rotations. -/
theorem s7d_cornerCoefficient_eq_of_recordIso {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (h : Nonempty (RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q))
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q'))))
    (hrot : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt,
    s7d_cornerSlot_eq_of_recordIso hn hm hP hQ q q' h hrot,
    s7d_cornerHomfly_eq_of_recordIso hn hm hP hQ hS q hT q' h]

/-- Coefficient transport in the list form: a visit map `φ` carrying the carrier's restricted Gauss list to a
rotation of the other carrier's, commuting with the twin and preserving the over bits on the carrier's
crossings, plus equal rotations. -/
theorem s7d_cornerCoefficient_eq_of_gaussList_rotated {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (φ : Visit P → Visit Q)
    (hrot : (CB.gaussList (CB.cg hm hQ) (carrierCrossings hm hQ T q')).IsRotated
      ((CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S q)).map φ))
    (htwin : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q → φ (visitTwin v) = visitTwin (φ v))
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (φ v) = CB.positiveOverBit v)
    (hr : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT :=
  s7d_cornerCoefficient_eq_of_recordIso hn hm hP hQ hS q hT q'
    ⟨s7d_gaussRecordIso _ _ _ _ φ hrot htwin hbit⟩ hr

/-- Coefficient transport in the key-monotone form (the form the persistent-visit-order clause
`VertexLocalData.visit_order` of lem:wall-sides (V) delivers): `φ` maps the carrier's crossings' visits onto
the other carrier's crossings' visits, strictly increasing in the traversal key, twin-compatible, bit-preserving;
rotations equal. -/
theorem s7d_cornerCoefficient_eq_of_strictMono {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (φ : Visit P → Visit Q)
    (hmem : ∀ w : Visit Q, w.1 ∈ carrierCrossings hm hQ T q' ↔
      ∃ v : Visit P, v.1 ∈ carrierCrossings hn hP S q ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ carrierCrossings hn hP S q → w.1 ∈ carrierCrossings hn hP S q →
      geometricVisitKey (CB.cg hn hP) v < geometricVisitKey (CB.cg hn hP) w →
        geometricVisitKey (CB.cg hm hQ) (φ v) < geometricVisitKey (CB.cg hm hQ) (φ w))
    (htwin : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q → φ (visitTwin v) = visitTwin (φ v))
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (φ v) = CB.positiveOverBit v)
    (hr : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT :=
  s7d_cornerCoefficient_eq_of_gaussList_rotated hn hm hP hQ hS q hT q' φ
    (by rw [s7d_gaussList_eq_of_strictMono _ _ _ _ φ hmem hmono]) htwin hbit hr

/-- The corner product is carried by a bijection of carriers with equal coefficients. -/
theorem s7d_cornerProduct_eq_of_equiv {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T)
    (e : Component hn hP S ≃ Component hm hQ T)
    (hcoef : ∀ q, cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T (e q) hT) :
    cornerProduct hn hP S hS = cornerProduct hm hQ T hT := by
  unfold cornerProduct
  exact Fintype.prod_equiv e _ _ hcoef

/-! #### The cut form: a visit map monotone in the traversal key up to ONE cyclic cut (the labelling of a
half starts at the contact vertex; the traversal order of the parent's retained visits is a rotation of the
half's).  The mapped list is then a rotation of the sorted list. -/

/-- A strictly key-sorted list splits at a threshold: the members below `c` form a prefix. -/
theorem s7d_sorted_eq_filter_append {α : Type*} (key : α → ℝ) (c : ℝ) (l : List α)
    (hl : l.Pairwise (fun v w => key v < key w)) :
    l = l.filter (fun v => decide (key v < c)) ++ l.filter (fun v => !decide (key v < c)) := by
  have hperm : (l.filter (fun v => decide (key v < c)) ++ l.filter (fun v => !decide (key v < c))).Perm l :=
    List.filter_append_perm _ l
  symm
  refine List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _))
    ?_ hl hperm
  rw [List.pairwise_append]
  refine ⟨hl.filter _, hl.filter _, ?_⟩
  intro a ha b hb
  simp only [List.mem_filter, decide_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at ha hb
  exact lt_of_lt_of_le ha.2 hb.2

/-- The cut form of the restricted Gauss list transport: `φ` maps the `X`-visits onto the `Y`-visits, is
strictly key-increasing within each of the two blocks `key < c` / `key ≥ c`, and puts the block `key ≥ c` before
the block `key < c` in `Q`; then the `Y`-list is a rotation of the mapped `X`-list. -/
theorem s7d_gaussList_isRotated_of_cut {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}
    (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q) (X : Finset (Crossing P))
    (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q) (c : ℝ)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
      (geometricVisitKey hcP w < c ∨ c ≤ geometricVisitKey hcP v) →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w))
    (hcut : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < c → c ≤ geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ w) < geometricVisitKey hcQ (φ v)) :
    (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ) := by
  set L := CB.gaussList hcP X with hL
  set A := L.filter (fun v => decide (geometricVisitKey hcP v < c)) with hA
  set B := L.filter (fun v => !decide (geometricVisitKey hcP v < c)) with hB
  have hsortP : L.Pairwise (fun v w => geometricVisitKey hcP v < geometricVisitKey hcP w) :=
    CB.kl2_gaussList_pairwise_lt hcP X
  have hsplit : L = A ++ B := s7d_sorted_eq_filter_append (geometricVisitKey hcP) c L hsortP
  have hmemA : ∀ v ∈ A, v.1 ∈ X ∧ geometricVisitKey hcP v < c := fun v hv => by
    rw [hA, List.mem_filter, decide_eq_true_iff] at hv
    exact ⟨(CB.kl0_mem_gaussList hcP X v).mp hv.1, hv.2⟩
  have hmemB : ∀ v ∈ B, v.1 ∈ X ∧ c ≤ geometricVisitKey hcP v := fun v hv => by
    rw [hB] at hv
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hv
    exact ⟨(CB.kl0_mem_gaussList hcP X v).mp hv.1, hv.2⟩
  -- the rotated candidate `B ++ A`, mapped, is strictly key-sorted in `Q`
  have hsortBA : ((B ++ A).map φ).Pairwise
      (fun v w => geometricVisitKey hcQ v < geometricVisitKey hcQ w) := by
    rw [List.pairwise_map, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · refine (List.Pairwise.and_mem.mp (hsortP.filter _)).imp ?_
      rintro v w ⟨hv, hw, hlt⟩
      exact hmono v w (hmemB v hv).1 (hmemB w hw).1 hlt (Or.inr (hmemB v hv).2)
    · refine (List.Pairwise.and_mem.mp (hsortP.filter _)).imp ?_
      rintro v w ⟨hv, hw, hlt⟩
      exact hmono v w (hmemA v hv).1 (hmemA w hw).1 hlt (Or.inl (hmemA w hw).2)
    · intro b hb a ha
      exact hcut a b (hmemA a ha).1 (hmemB b hb).1 (hmemA a ha).2 (hmemB b hb).2
  have hnd : ((B ++ A).map φ).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hsortBA.imp fun h e => absurd (by rw [e] at h; exact h) (lt_irrefl _)
  have hsortQ : (CB.gaussList hcQ Y).Pairwise
      (fun v w => geometricVisitKey hcQ v < geometricVisitKey hcQ w) :=
    CB.kl2_gaussList_pairwise_lt hcQ Y
  have hperm : (CB.gaussList hcQ Y).Perm ((B ++ A).map φ) := by
    rw [List.perm_ext_iff_of_nodup (CB.kl0_gaussList_nodup hcQ Y) hnd]
    intro w
    have hBA : ∀ v, v ∈ B ++ A ↔ v ∈ L := fun v => by
      rw [hsplit, List.mem_append, List.mem_append]; exact or_comm
    rw [CB.kl0_mem_gaussList, hmem, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (hBA v).mpr ((CB.kl0_mem_gaussList hcP X v).mpr hv), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (CB.kl0_mem_gaussList hcP X v).mp ((hBA v).mp hv), rfl⟩
  have heq : CB.gaussList hcQ Y = (B ++ A).map φ :=
    List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _))
      hsortQ hsortBA hperm
  rw [heq, hsplit, List.map_append, List.map_append]
  exact List.isRotated_append

/-- Coefficient transport in the cut form (relocation to a half whose labelling starts at the contact). -/
theorem s7d_cornerCoefficient_eq_of_cut {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (φ : Visit P → Visit Q) (c : ℝ)
    (hmem : ∀ w : Visit Q, w.1 ∈ carrierCrossings hm hQ T q' ↔
      ∃ v : Visit P, v.1 ∈ carrierCrossings hn hP S q ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ carrierCrossings hn hP S q → w.1 ∈ carrierCrossings hn hP S q →
      geometricVisitKey (CB.cg hn hP) v < geometricVisitKey (CB.cg hn hP) w →
      (geometricVisitKey (CB.cg hn hP) w < c ∨ c ≤ geometricVisitKey (CB.cg hn hP) v) →
        geometricVisitKey (CB.cg hm hQ) (φ v) < geometricVisitKey (CB.cg hm hQ) (φ w))
    (hcut : ∀ v w : Visit P, v.1 ∈ carrierCrossings hn hP S q → w.1 ∈ carrierCrossings hn hP S q →
      geometricVisitKey (CB.cg hn hP) v < c → c ≤ geometricVisitKey (CB.cg hn hP) w →
        geometricVisitKey (CB.cg hm hQ) (φ w) < geometricVisitKey (CB.cg hm hQ) (φ v))
    (htwin : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q → φ (visitTwin v) = visitTwin (φ v))
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (φ v) = CB.positiveOverBit v)
    (hr : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT :=
  s7d_cornerCoefficient_eq_of_gaussList_rotated hn hm hP hQ hS q hT q' φ
    (s7d_gaussList_isRotated_of_cut _ _ _ _ φ c hmem hmono hcut) htwin hbit hr

omit [NeZero n] in
/-- Membership bookkeeping for a global visit bijection: `φ` carries `X`-visits onto `Y`-visits. -/
theorem s7d_mem_iff_of_equiv {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}
    (X : Finset (Crossing P)) (Y : Finset (Crossing Q)) (φ : Visit P ≃ Visit Q)
    (hXY : ∀ v : Visit P, (φ v).1 ∈ Y ↔ v.1 ∈ X) (w : Visit Q) :
    w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w := by
  constructor
  · intro hw
    refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
    rw [← hXY, φ.apply_symm_apply]; exact hw
  · rintro ⟨v, hv, rfl⟩
    exact (hXY v).mpr hv

/-! #### Decoding the traversal key: edge label first, then the edge parameter (the form in which
lem:wall-sides (V) `VertexLocalData.visit_order` states the persistent visit order). -/

/-- `key v < key w` iff `v` is on an earlier edge, or on the same edge at a smaller parameter. -/
theorem s7d_geometricVisitKey_lt_iff {P : LabelledTuple n} (hc : CrossingGeometry P) (v w : Visit P) :
    geometricVisitKey hc v < geometricVisitKey hc w ↔
      (v.2.val.val < w.2.val.val ∨ (v.2.val = w.2.val ∧ visitParameter v < visitParameter w)) := by
  have hv : geometricVisitKey hc v = (v.2.val.val : ℝ) + visitParameter v := rfl
  have hw : geometricVisitKey hc w = (w.2.val.val : ℝ) + visitParameter w := rfl
  have hv1 := (crossingParameter_interior_of_geometry hc v.1 v.2.val v.2.property)
  have hw1 := (crossingParameter_interior_of_geometry hc w.1 w.2.val w.2.property)
  change 0 < visitParameter v ∧ visitParameter v < 1 at hv1
  change 0 < visitParameter w ∧ visitParameter w < 1 at hw1
  constructor
  · intro h
    rcases lt_trichotomy v.2.val.val w.2.val.val with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr ⟨ZMod.val_injective n heq, ?_⟩
      rw [hv, hw, heq] at h
      linarith
    · exfalso
      have h1 : (w.2.val.val : ℝ) + 1 ≤ v.2.val.val := by exact_mod_cast hgt
      rw [hv, hw] at h
      linarith
  · rintro (hlt | ⟨he, hp⟩)
    · have h1 : (v.2.val.val : ℝ) + 1 ≤ w.2.val.val := by exact_mod_cast hlt
      rw [hv, hw]
      linarith
    · rw [hv, hw, he]
      linarith

/-- Strict key-monotonicity of a visit map between polygons with the same labels, from edge preservation and
edgewise preservation of the parameter order (on the visits of `X`). -/
theorem s7d_strictMono_of_edgewise {P Q : LabelledTuple n} (hcP : CrossingGeometry P)
    (hcQ : CrossingGeometry Q) (X : Finset (Crossing P)) (φ : Visit P → Visit Q)
    (hedge : ∀ v : Visit P, v.1 ∈ X → (φ v).2.val = v.2.val)
    (hpar : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X → v.2.val = w.2.val →
      visitParameter v < visitParameter w → visitParameter (φ v) < visitParameter (φ w)) :
    ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w) := by
  intro v w hv hw h
  rw [s7d_geometricVisitKey_lt_iff] at h ⊢
  rw [hedge v hv, hedge w hw]
  rcases h with h | ⟨he, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨he, hpar v w hv hw he hp⟩

/-! #### A full mark transport (SM/CChamber.lean `MarkTransport`) carries the restricted Gauss lists: a
`Deform`-free proof of the homfly hypothesis of `MarkTransport.cornerCoefficient_transport`, given the
crossing signs (over bits) are preserved. -/

/-- Rotations pass through `filterMap`. -/
theorem s7d_isRotated_filterMap {α β : Type*} (f : α → Option β) {l l' : List α}
    (h : l.IsRotated l') : (l.filterMap f).IsRotated (l'.filterMap f) := by
  obtain ⟨k, hk, rfl⟩ := List.isRotated_iff_mod.mp h
  have h1 := List.isRotated_append (l := (l.take k).filterMap f) (l' := (l.drop k).filterMap f)
  rw [← List.filterMap_append, List.take_append_drop] at h1
  rw [List.rotate_eq_drop_append_take hk, List.filterMap_append]
  exact h1

/-- Rotations pass through `filter`. -/
theorem s7d_isRotated_filter {α : Type*} (p : α → Bool) {l l' : List α}
    (h : l.IsRotated l') : (l.filter p).IsRotated (l'.filter p) := by
  obtain ⟨k, hk, rfl⟩ := List.isRotated_iff_mod.mp h
  have h1 := List.isRotated_append (l := (l.take k).filter p) (l' := (l.drop k).filter p)
  rw [← List.filter_append, List.take_append_drop] at h1
  rw [List.rotate_eq_drop_append_take hk, List.filter_append]
  exact h1

/-- The visits of the key-sorted mark list, in order, form the key-sorted Gauss list. -/
theorem s7d_markList_filterMap (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (markList hn hP).filterMap Sum.getRight? = geometricGaussList (CB.cg hn hP) := by
  have hsortM : ((markList hn hP).filterMap Sum.getRight?).Pairwise
      (fun v w : Visit P => geometricVisitKey (CB.cg hn hP) v < geometricVisitKey (CB.cg hn hP) w) := by
    refine List.Pairwise.filterMap _ ?_
      (CB.kl1_pairwise_lt (markList_sorted hn hP) (markList_nodup hn hP) (markKey_injective hn hP))
    intro a a' hlt b hb b' hb'
    cases a with
    | inl i => simp at hb
    | inr v =>
      cases a' with
      | inl i => simp at hb'
      | inr w =>
        simp only [Sum.getRight?_inr, Option.some.injEq] at hb hb'
        subst hb; subst hb'
        exact hlt
  have hsortG : (geometricGaussList (CB.cg hn hP)).Pairwise
      (fun v w : Visit P => geometricVisitKey (CB.cg hn hP) v < geometricVisitKey (CB.cg hn hP) w) :=
    CB.kl1_pairwise_lt (geometricGaussList_sorted _) (geometricGaussList_nodup _)
      (geometricVisitKey_injective _)
  have hnd : ((markList hn hP).filterMap Sum.getRight?).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hsortM.imp fun h e => absurd (by rw [e] at h; exact h) (lt_irrefl _)
  have hperm : ((markList hn hP).filterMap Sum.getRight?).Perm (geometricGaussList (CB.cg hn hP)) := by
    rw [List.perm_ext_iff_of_nodup hnd (geometricGaussList_nodup _)]
    intro v
    refine iff_of_true ?_ (mem_geometricGaussList _ v)
    rw [List.mem_filterMap]
    exact ⟨Sum.inr v, mem_markList hn hP _, rfl⟩
  exact List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _))
    hsortM hsortG hperm

/-- A mark transport carries the restricted Gauss list of `X` to a rotation of the restricted Gauss list of
the transported support (from `markList_rotated`, through `filterMap`/`filter`). -/
theorem s7d_gaussList_transport {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
    (τ : MarkTransport hn hP hQ) (X : Finset (Crossing P)) :
    (CB.gaussList (CB.cg hn hQ) (τ.support X)).IsRotated
      ((CB.gaussList (CB.cg hn hP) X).map τ.visit) := by
  unfold CB.gaussList
  rw [← s7d_markList_filterMap hn hQ, ← s7d_markList_filterMap hn hP]
  have h1 := s7d_isRotated_filter (fun v : Visit Q => decide (v.1 ∈ τ.support X))
    (s7d_isRotated_filterMap Sum.getRight? τ.markList_rotated)
  refine h1.trans ?_
  have h2 : ((markList hn hP).map (Sum.map τ.vert τ.visit)).filterMap Sum.getRight? =
      ((markList hn hP).filterMap Sum.getRight?).map τ.visit := by
    rw [List.filterMap_map, List.map_filterMap]
    congr 1
    funext m
    cases m <;> rfl
  rw [h2, List.filter_map]
  have h3 : ∀ v ∈ (markList hn hP).filterMap Sum.getRight?,
      ((fun w : Visit Q => decide (w.1 ∈ τ.support X)) ∘ τ.visit) v = decide (v.1 ∈ X) := by
    intro v _
    simp only [Function.comp_apply, τ.visit_fst, τ.mem_support]
  rw [List.filter_congr h3]

/-- **Deform-free homfly transport along a mark transport** preserving the positive over bits on the
carrier's crossings: the restricted Gauss records are isomorphic (`s7d_gaussRecordIso`), hence the positive
lifts have equal `homfly` (lc:presentations). -/
theorem s7d_homfly_transport {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
    (τ : MarkTransport hn hP hQ) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (τ.visit v) = CB.positiveOverBit v) :
    homfly (positiveLift hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS)) =
      homfly (positiveLift hn hP S q hS) := by
  have hrot : (CB.gaussList (CB.cg hn hQ) (carrierCrossings hn hQ (τ.support S) (τ.component S q))).IsRotated
      ((CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S q)).map τ.visit) := by
    rw [τ.carrierCrossings_transport S q]
    exact s7d_gaussList_transport τ _
  exact (s7d_cornerHomfly_eq_of_recordIso hn hn hP hQ hS q ((τ.isDecomposition_transport S).mpr hS)
    (τ.component S q) ⟨s7d_gaussRecordIso _ _ _ _ τ.visit hrot (fun v _ => τ.twin_eq v) hbit⟩).symm

/-- The over bits are preserved by a mark transport that preserves the crossing signs
`crossingSign P e (twin e)` at the visits of `X` (as CSilent's `sides_markTurn_eq` establishes for a silent
wall). -/
theorem s7d_positiveOverBit_transport {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P}
    {hQ : Generic Q} (τ : MarkTransport hn hP hQ) (X : Finset (Crossing P))
    (hsgn : ∀ v : Visit P, v.1 ∈ X →
      crossingSign Q (τ.visit v).2.val (τ.visit (visitTwin v)).2.val =
        crossingSign P v.2.val (visitTwin v).2.val) :
    ∀ v : Visit P, v.1 ∈ X → CB.positiveOverBit (τ.visit v) = CB.positiveOverBit v := by
  intro v hv
  apply s7d_positiveOverBit_eq_of_crossingSign
  rw [← τ.twin_eq]
  exact hsgn v hv

/-- `cornerCoefficient_transport` with the homfly hypothesis discharged by the record route: only the rotation
and the over bits remain. -/
theorem s7d_cornerCoefficient_transport {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P}
    {hQ : Generic Q} (τ : MarkTransport hn hP hQ) {S : Finset (Crossing P)}
    (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (τ.visit v) = CB.positiveOverBit v)
    (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q) :
    cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS :=
  τ.cornerCoefficient_transport hS q hrot (s7d_homfly_transport τ hS q hbit)

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
