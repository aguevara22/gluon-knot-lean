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

/-! ### Helper unit U110-I (prefix `s7i_`): the contact rotation ledger — eq. s7c:full-rotation
(sm-4:483-503), the contact turns (540-551), eq. s7c:rotation-ledger (587-598), the `R`-identities
eq. s7c:interlacing-absolute (655-663) / eq. s7c:noninterlacing-rotation (748-757) and the slot
identities eqs. s7c:interlacing-slot, s7c:noninterlacing-slot, s7c:different-low/high-slot.

Design.  Everything is stated on REGULAR LABELLED POLYGONS (the corner polygons of the three contact
carriers — full `L*`, halves `L₁`, `L₂` — are `LabelledTuple`s of three different sizes) with the
corner correspondence of U110-C (`e : {i // i ≠ j₁} ⊕ {i // i ≠ j₂} ≃ {i // i ≠ j}`, "All noncontact
turns partition between the halves", sm-4:551), here required to preserve the PRINCIPAL turn (the real
angle, `principalTurn`), which implies U110-C's sign-preservation (`s7i_turn_elim_of_principalTurn_elim`).
The ledger then needs NO explicit angles: the three rotation numbers are integers (lem:rot,
`rotationNumber_integer`), so the three contact turns sum to a multiple of `2π`; each is in `(−π, π)`
(`principalAngle_bounds`) with the sign of its `turn` (`principalTurn_sign`); the two half contact
turns have the sign `s₀` and the full contact turn has the sign `s₀` (interlacing) or `−s₀`
(noninterlacing) — the multiple is then forced to `0`, resp. `s₀` (`s7i_ledger_of_int`).  The printed
explicit values `β`, `π − α`, `β − α ∓ π` are recovered at the vector level (`s7i_contact_*`), with
eq. s7c:angle-orders in the form "interlacing ⟺ the full contact turn has the sign of the half contact
turns ⟺ `sgn det(w₁, w₂) = −s₀`".  The `R`-identities use lem:uniformrot (`uniform_rotation`) to put
the three rotations on the ray of the uniform sign.  eq. s7c:full-rotation is lem:rot (ii)
(`rotationNumber_family_constant`) on a family through the wall, packaged for the germ's parameter.
Nothing here depends on the floor, the singleton, or any other unit. -/

section S7IRotationLedger

/-! #### eq. s7c:full-rotation — lem:rot (ii) through the wall -/

/-- lem:rot (ii) on a closed real interval: a family of `k`-gons continuous on `[a, b]` and regular at
EVERY parameter of `[a, b]` (including the wall parameter) has one rotation number on `[a, b]`. -/
theorem s7i_rotationNumber_constant_Icc {k : ℕ} [NeZero k] {f : ℝ → LabelledTuple k} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hr : ∀ t ∈ Set.Icc a b, Regular (f t)) {s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    rotationNumber (f s) = rotationNumber (f t) := by
  have : PreconnectedSpace (Set.Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hF : Continuous (fun u : Set.Icc a b => f u.1) :=
    hf.comp_continuous continuous_subtype_val (fun u => u.2)
  exact rotationNumber_family_constant hF (fun u => hr u.1 u.2) ⟨s, hs⟩ ⟨t, ht⟩

/-- The inclusion of the closed symmetric interval `[−t, t]` into the germ's parameter interval. -/
def s7i_germIcc (g : WallGerm n) (t : g.SideParameter) (u : Set.Icc (-t.val) t.val) : g.Parameter :=
  ⟨u.1, by
    obtain ⟨h1, h2⟩ := u.2
    have := t.property.2
    constructor <;> linarith⟩

omit [NeZero n] in
theorem s7i_continuous_germIcc (g : WallGerm n) (t : g.SideParameter) :
    Continuous (s7i_germIcc g t) :=
  continuous_subtype_val.subtype_mk _

omit [NeZero n] in
theorem s7i_germIcc_left (g : WallGerm n) (t : g.SideParameter) :
    s7i_germIcc g t ⟨-t.val, by constructor <;> linarith [t.property.1]⟩ = g.sideTime false t := by
  apply Subtype.ext
  simp [s7i_germIcc, WallGerm.sideTime]

omit [NeZero n] in
theorem s7i_germIcc_right (g : WallGerm n) (t : g.SideParameter) :
    s7i_germIcc g t ⟨t.val, by constructor <;> linarith [t.property.1]⟩ = g.sideTime true t := by
  apply Subtype.ext
  simp [s7i_germIcc, WallGerm.sideTime]

omit [NeZero n] in
/-- **eq. s7c:full-rotation** in the germ's parameter (sm-4:493-503): a family of `k`-gons over the germ's
parameter interval, continuous on `|u| ≤ t` and regular there — "the edge pieces have positive lengths at
the centre, and all its corner turns have nonzero determinants there … a continuous regular family,
including at the wall" — has the same rotation number at the two side parameters `−t` and `t`
(lem:rot (ii)).  `rot(L_L) = rot(L_H)`; `rot(L*)` is the value at the centre `u = 0`. -/
theorem s7i_full_rotation_germ {k : ℕ} [NeZero k] (g : WallGerm n) (t : g.SideParameter)
    {f : g.Parameter → LabelledTuple k} (hf : ContinuousOn f {u : g.Parameter | |u.val| ≤ t.val})
    (hr : ∀ u : g.Parameter, |u.val| ≤ t.val → Regular (f u)) :
    rotationNumber (f (g.sideTime false t)) = rotationNumber (f (g.sideTime true t)) := by
  have : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hmem : ∀ u : Set.Icc (-t.val) t.val, s7i_germIcc g t u ∈ {u : g.Parameter | |u.val| ≤ t.val} := by
    intro u
    show |u.1| ≤ t.val
    exact abs_le.mpr u.2
  have hF : Continuous (fun u : Set.Icc (-t.val) t.val => f (s7i_germIcc g t u)) :=
    hf.comp_continuous (s7i_continuous_germIcc g t) hmem
  have hc := rotationNumber_family_constant hF (fun u => hr _ (hmem u))
    ⟨-t.val, by constructor <;> linarith [t.property.1]⟩ ⟨t.val, by constructor <;> linarith [t.property.1]⟩
  simpa only [s7i_germIcc_left, s7i_germIcc_right] using hc

omit [NeZero n] in
/-- The centre value is the common side value (`rot(L*) = rot(L_L) = rot(L_H)`). -/
theorem s7i_full_rotation_germ_centre {k : ℕ} [NeZero k] (g : WallGerm n) (t : g.SideParameter)
    {f : g.Parameter → LabelledTuple k} (hf : ContinuousOn f {u : g.Parameter | |u.val| ≤ t.val})
    (hr : ∀ u : g.Parameter, |u.val| ≤ t.val → Regular (f u)) (b : Bool) :
    rotationNumber (f (g.sideTime b t)) = rotationNumber (f g.zeroParameter) := by
  have : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hmem : ∀ u : Set.Icc (-t.val) t.val, s7i_germIcc g t u ∈ {u : g.Parameter | |u.val| ≤ t.val} := by
    intro u
    show |u.1| ≤ t.val
    exact abs_le.mpr u.2
  have hF : Continuous (fun u : Set.Icc (-t.val) t.val => f (s7i_germIcc g t u)) :=
    hf.comp_continuous (s7i_continuous_germIcc g t) hmem
  have h0 : s7i_germIcc g t ⟨0, by constructor <;> linarith [t.property.1]⟩ = g.zeroParameter := by
    apply Subtype.ext
    simp [s7i_germIcc, WallGerm.zeroParameter]
  cases b
  · have hc := rotationNumber_family_constant hF (fun u => hr _ (hmem u))
      ⟨-t.val, by constructor <;> linarith [t.property.1]⟩ ⟨0, by constructor <;> linarith [t.property.1]⟩
    simpa only [s7i_germIcc_left, h0] using hc
  · have hc := rotationNumber_family_constant hF (fun u => hr _ (hmem u))
      ⟨t.val, by constructor <;> linarith [t.property.1]⟩ ⟨0, by constructor <;> linarith [t.property.1]⟩
    simpa only [s7i_germIcc_right, h0] using hc

/-- eq. s7c:full-rotation read on the two side carriers: if the corner polygons of the full contact
carriers `q₋` (on `P₋ = sideTuple false t`) and `q₊` (on `P₊ = sideTuple true t`) are, up to the size
recast, the two side values of one regular family through the wall, then `rot(L_L) = rot(L_H)`. -/
theorem s7i_carrierRotation_sides_of_family (hn : 3 ≤ n) (g : WallGerm n) (t : g.SideParameter)
    {k : ℕ} [NeZero k] {f : g.Parameter → LabelledTuple k}
    (hf : ContinuousOn f {u : g.Parameter | |u.val| ≤ t.val})
    (hr : ∀ u : g.Parameter, |u.val| ≤ t.val → Regular (f u))
    (Sm : Finset (Crossing (g.sideTuple false t).val)) (qm : Component hn (g.sideTuple false t).property Sm)
    (Sp : Finset (Crossing (g.sideTuple true t).val)) (qp : Component hn (g.sideTuple true t).property Sp)
    (hkm : k = ccpCornerCount hn (g.sideTuple false t).property Sm qm)
    (hkp : k = ccpCornerCount hn (g.sideTuple true t).property Sp qp)
    (hm : recastTuple hkm (ccpCornerPolygon hn (g.sideTuple false t).property Sm qm) = f (g.sideTime false t))
    (hp : recastTuple hkp (ccpCornerPolygon hn (g.sideTuple true t).property Sp qp) = f (g.sideTime true t)) :
    carrierRotation hn (g.sideTuple false t).property Sm qm =
      carrierRotation hn (g.sideTuple true t).property Sp qp := by
  unfold carrierRotation
  rw [← rotationNumber_recastTuple hkm, ← rotationNumber_recastTuple hkp, hm, hp]
  exact s7i_full_rotation_germ g t hf hr

/-! #### The contact turns at the vector level (sm-4:540-551): `r` the remote direction (edge `E_a`),
`w₁ = μ_{M−1} − μ_M`, `w₂ = μ_{M+1} − μ_M` the neighbour vectors.  Half 1 (`λ₁` closes with
`[μ_a, μ_M] ⊂ E_a`, def:deletion-halves) turns from `r` onto `w₂`; half 2 (`λ₂` closes with `E_{M−1}`
and opens with `[μ_M, μ_b] ⊂ E_a`) turns from `−w₁` onto `r`; the full contact carrier turns from `−w₁`
onto `w₂` (the polygon's own corner at `M`).  In the printed normalisation (`r = (1,0)`, both
neighbours above, arguments `α, β ∈ (0, π)`) these are `β`, `π − α`, `β − α ∓ π`. -/

theorem s7i_det_neg_left (u v : Plane) : det (-u) v = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]
  ring

theorem s7i_det_neg_right (u v : Plane) : det u (-v) = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]
  ring

theorem s7i_det_zero_left (v : Plane) : det 0 v = 0 := by
  simp [det]

theorem s7i_det_zero_right (u : Plane) : det u 0 = 0 := by
  simp [det]

/-- Two vectors with nonzero determinant form a regular pair (not collinear at all). -/
theorem s7i_regularPair_of_det_ne_zero {u v : Plane} (h : det u v ≠ 0) : RegularPair u v := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact h (s7i_det_zero_left v)
  · rintro rfl
    exact h (s7i_det_zero_right u)
  · rintro ⟨r, _, rfl⟩
    exact h (det_smul_self u r)

/-- The three contact turns sum to zero modulo `2π` (the telescoping identity of lem:rot on the triangle
of directions `−w₁ → r → w₂`). -/
theorem s7i_contact_angle_sum {r w₁ w₂ : Plane} (hr : r ≠ 0) (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) :
    ((principalAngle r w₂ + principalAngle (-w₁) r - principalAngle (-w₁) w₂ : ℝ) : Real.Angle) = 0 := by
  have h₁' : -w₁ ≠ 0 := neg_ne_zero.mpr h₁
  rw [Real.Angle.coe_sub, Real.Angle.coe_add, principalAngle_coe_angle hr h₂,
    principalAngle_coe_angle h₁' hr, principalAngle_coe_angle h₁' h₂]
  abel

/-- … hence they sum to an integer multiple of `2π`. -/
theorem s7i_contact_angle_sum_int {r w₁ w₂ : Plane} (hr : r ≠ 0) (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) :
    ∃ m : ℤ, principalAngle r w₂ + principalAngle (-w₁) r - principalAngle (-w₁) w₂ = m * (2 * Real.pi) := by
  obtain ⟨m, hm⟩ := Real.Angle.coe_eq_zero_iff.mp (s7i_contact_angle_sum hr h₁ h₂)
  exact ⟨m, by rw [← hm, zsmul_eq_mul]⟩

/-! #### The ledger as pure real arithmetic -/

/-- A nonzero sign is `1` or `−1`. -/
theorem s7i_signType_cases {σ : SignType} (h : σ ≠ 0) : σ = 1 ∨ σ = -1 := by
  cases σ
  · exact absurd rfl h
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The negative of a nonzero sign is nonzero. -/
theorem s7i_neg_signType_ne_zero {σ : SignType} (h : σ ≠ 0) : -σ ≠ 0 := by
  rcases s7i_signType_cases h with rfl | rfl <;> decide

/-- **The ledger from integrality, bounds and signs** (sm-4:587-598, "Dividing by `2π` gives the signed
identity … The second line contains a full-turn correction; unsigned angles would not give this
formula"): three angles in `(−π, π)` whose signed combination `θ₁ + θ₂ − θ` is a multiple of `2π`, the
first two of sign `s₀`: if `θ` has the sign `s₀` the combination is `0`; if `θ` has the sign `−s₀` it is
the full turn `2π s₀`. -/
theorem s7i_ledger_of_int {θ₁ θ₂ θ : ℝ} {m : ℤ} (hm : θ₁ + θ₂ - θ = m * (2 * Real.pi))
    (hb₁ : -Real.pi < θ₁ ∧ θ₁ < Real.pi) (hb₂ : -Real.pi < θ₂ ∧ θ₂ < Real.pi)
    (hb : -Real.pi < θ ∧ θ < Real.pi) {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (h₁ : SignType.sign θ₁ = s₀) (h₂ : SignType.sign θ₂ = s₀) :
    (SignType.sign θ = s₀ → θ₁ + θ₂ - θ = 0) ∧
      (SignType.sign θ = -s₀ → θ₁ + θ₂ - θ = 2 * Real.pi * (s₀ : ℝ)) := by
  have hpi := Real.pi_pos
  rcases s7i_signType_cases hs₀ with rfl | rfl
  · have hp₁ : 0 < θ₁ := sign_eq_one_iff.mp h₁
    have hp₂ : 0 < θ₂ := sign_eq_one_iff.mp h₂
    constructor
    · intro h
      have hp : 0 < θ := sign_eq_one_iff.mp h
      have hlt : (m : ℝ) < 1 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hgt : (-1 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have hm0 : m = 0 := by
        have h1 : m < 1 := by exact_mod_cast hlt
        have h2 : -1 < m := by exact_mod_cast hgt
        omega
      rw [hm, hm0]
      simp
    · intro h
      have hp : θ < 0 := sign_eq_neg_one_iff.mp (by simpa using h)
      have hlt : (m : ℝ) < 2 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hgt : (0 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have hm1 : m = 1 := by
        have h1 : m < 2 := by exact_mod_cast hlt
        have h2 : 0 < m := by exact_mod_cast hgt
        omega
      rw [hm, hm1]
      simp
  · have hp₁ : θ₁ < 0 := sign_eq_neg_one_iff.mp h₁
    have hp₂ : θ₂ < 0 := sign_eq_neg_one_iff.mp h₂
    constructor
    · intro h
      have hp : θ < 0 := sign_eq_neg_one_iff.mp h
      have hlt : (m : ℝ) < 1 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hgt : (-1 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have hm0 : m = 0 := by
        have h1 : m < 1 := by exact_mod_cast hlt
        have h2 : -1 < m := by exact_mod_cast hgt
        omega
      rw [hm, hm0]
      simp
    · intro h
      have hp : 0 < θ := sign_eq_one_iff.mp (by simpa using h)
      have hlt : (m : ℝ) < 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hgt : (-2 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have hm1 : m = -1 := by
        have h1 : m < 0 := by exact_mod_cast hlt
        have h2 : -2 < m := by exact_mod_cast hgt
        omega
      rw [hm, hm1]
      simp

/-! #### The contact turns: signs, eq. s7c:angle-orders, and the vector-level ledger -/

/-- The half contact turn of `λ₁` (`r → w₂`) has the sign of `det(r, w₂)` (`= s₀`: `β ∈ (0, π)` in the
normalisation). -/
theorem s7i_contact_sign_half₁ {r w₂ : Plane} (h : det r w₂ ≠ 0) :
    SignType.sign (principalAngle r w₂) = SignType.sign (det r w₂) :=
  principalAngle_sign (s7i_regularPair_of_det_ne_zero h)

/-- The half contact turn of `λ₂` (`−w₁ → r`) has the sign of `det(r, w₁)` (`= s₀`: `π − α ∈ (0, π)`). -/
theorem s7i_contact_sign_half₂ {r w₁ : Plane} (h : det r w₁ ≠ 0) :
    SignType.sign (principalAngle (-w₁) r) = SignType.sign (det r w₁) := by
  have h' : det (-w₁) r ≠ 0 := by
    rw [s7i_det_neg_left, det_swap, neg_neg]
    exact h
  rw [principalAngle_sign (s7i_regularPair_of_det_ne_zero h'), s7i_det_neg_left, det_swap, neg_neg]

/-- The full contact turn (`−w₁ → w₂`, the polygon's corner at `M`) has the sign of `−det(w₁, w₂)`
(`β − α ∓ π`). -/
theorem s7i_contact_sign_full {w₁ w₂ : Plane} (h : det w₁ w₂ ≠ 0) :
    SignType.sign (principalAngle (-w₁) w₂) = -SignType.sign (det w₁ w₂) := by
  have h' : det (-w₁) w₂ ≠ 0 := by
    rw [s7i_det_neg_left]
    exact neg_ne_zero.mpr h
  rw [principalAngle_sign (s7i_regularPair_of_det_ne_zero h'), s7i_det_neg_left, Left.sign_neg]

/-- **The contact configuration** (sm-4:540-551, eq. s7c:angle-orders): both neighbours strictly on the
same side `s₀` of the remote line (`sgn det(r, w₁) = sgn det(r, w₂) = s₀ ≠ 0`) and a nondegenerate corner
at `M` (`det(w₁, w₂) ≠ 0`, i.e. (G1)).  Interlacing (`ε = 1`, `β < α`) is `sgn det(w₁, w₂) = −s₀`: then the
full contact turn has the sign `s₀` of the half contact turns and the three contact turns satisfy
`θ₁ + θ₂ − θ* = 0` (`β + (π − α) − (β − α + π)`).  Noninterlacing (`ε = 0`, `α < β`) is `sgn det(w₁, w₂) = s₀`:
the full contact turn has the sign `−s₀` and `θ₁ + θ₂ − θ* = 2π s₀` (`β + (π − α) − (β − α − π)`; the
full-turn correction).  Stated for both orientations at once ("Reflection reverses all signs together"). -/
theorem s7i_contact_ledger {r w₁ w₂ : Plane} {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (h₁ : SignType.sign (det r w₁) = s₀) (h₂ : SignType.sign (det r w₂) = s₀) (h₁₂ : det w₁ w₂ ≠ 0) :
    (SignType.sign (det w₁ w₂) = -s₀ →
        SignType.sign (principalAngle (-w₁) w₂) = s₀ ∧
        principalAngle r w₂ + principalAngle (-w₁) r - principalAngle (-w₁) w₂ = 0) ∧
      (SignType.sign (det w₁ w₂) = s₀ →
        SignType.sign (principalAngle (-w₁) w₂) = -s₀ ∧
        principalAngle r w₂ + principalAngle (-w₁) r - principalAngle (-w₁) w₂ = 2 * Real.pi * (s₀ : ℝ)) := by
  have hd₁ : det r w₁ ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at h₁
    exact hs₀ h₁.symm
  have hd₂ : det r w₂ ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at h₂
    exact hs₀ h₂.symm
  have hr : r ≠ 0 := by
    rintro rfl
    exact hd₁ (s7i_det_zero_left w₁)
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl
    exact hd₁ (s7i_det_zero_right r)
  have hw₂ : w₂ ≠ 0 := by
    rintro rfl
    exact hd₂ (s7i_det_zero_right r)
  obtain ⟨m, hm⟩ := s7i_contact_angle_sum_int hr hw₁ hw₂
  have hb₁ := principalAngle_bounds (s7i_regularPair_of_det_ne_zero hd₂)
  have hb₂ := principalAngle_bounds (s7i_regularPair_of_det_ne_zero (u := -w₁) (v := r)
    (by rw [s7i_det_neg_left, det_swap, neg_neg]; exact hd₁))
  have hb := principalAngle_bounds (s7i_regularPair_of_det_ne_zero (u := -w₁) (v := w₂)
    (by rw [s7i_det_neg_left]; exact neg_ne_zero.mpr h₁₂))
  have hsg₁ : SignType.sign (principalAngle r w₂) = s₀ := (s7i_contact_sign_half₁ hd₂).trans h₂
  have hsg₂ : SignType.sign (principalAngle (-w₁) r) = s₀ := (s7i_contact_sign_half₂ hd₁).trans h₁
  have hled := s7i_ledger_of_int hm hb₁ hb₂ hb hs₀ hsg₁ hsg₂
  have hfull := s7i_contact_sign_full h₁₂
  constructor
  · intro h
    have hs : SignType.sign (principalAngle (-w₁) w₂) = s₀ := by rw [hfull, h, neg_neg]
    exact ⟨hs, hled.1 hs⟩
  · intro h
    have hs : SignType.sign (principalAngle (-w₁) w₂) = -s₀ := by rw [hfull, h]
    exact ⟨hs, hled.2 hs⟩

/-- The dichotomy behind eq. s7c:angle-orders: a nonzero sign is `s₀` or `−s₀`. -/
theorem s7i_sign_cases_of_ne_zero {σ s₀ : SignType} (hσ : σ ≠ 0) (hs₀ : s₀ ≠ 0) : σ = s₀ ∨ σ = -s₀ := by
  rcases s7i_signType_cases hσ with rfl | rfl <;> rcases s7i_signType_cases hs₀ with rfl | rfl <;> decide

/-- With `det(w₁, w₂) ≠ 0` exactly one line of `s7i_contact_ledger` applies: `sgn det(w₁, w₂) = −s₀`
(interlacing, `ε = 1`) or `= s₀` (noninterlacing, `ε = 0`). -/
theorem s7i_contact_dichotomy {w₁ w₂ : Plane} {s₀ : SignType} (hs₀ : s₀ ≠ 0) (h₁₂ : det w₁ w₂ ≠ 0) :
    SignType.sign (det w₁ w₂) = -s₀ ∨ SignType.sign (det w₁ w₂) = s₀ := by
  have hne : SignType.sign (det w₁ w₂) ≠ 0 := sign_ne_zero.mpr h₁₂
  rcases s7i_sign_cases_of_ne_zero hne hs₀ with h | h
  · exact Or.inr h
  · exact Or.inl h

/-! #### From edge directions to principal turns.  Positive rescaling of both edges at a corner leaves
the principal turn unchanged (`principalAngle_smul`): this is how the contact turns of the corner
polygons are identified with the vector-level turns above (the corner polygon's edges at the contact
corner are positive multiples of `r`, `−w₁`, `w₂`: `[μ_a, μ_M] = λ r`, `[μ_M, μ_b] = (1−λ) r`), and how the
inherited noncontact corners keep their principal turns across the half ↔ full correspondence ("corner
edges are positive multiples of the original edges", lem:carriers (ii), `corner_polygons.2.1`). -/

/-- A corner whose two edges are positive multiples of `u`, `v` has principal turn `principalAngle u v`. -/
theorem s7i_principalTurn_eq_of_pos_smul {k : ℕ} (Q : LabelledTuple k) (i : ZMod k) {u v : Plane}
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (hu : edge Q (i - 1) = c • u) (hv : edge Q i = d • v) :
    principalTurn Q i = principalAngle u v := by
  unfold principalTurn
  rw [hu, hv]
  exact principalAngle_smul hc hd u v

/-- … and its turn is `sgn det(u, v)`. -/
theorem s7i_turn_eq_of_pos_smul {k : ℕ} (Q : LabelledTuple k) (i : ZMod k) {u v : Plane}
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (hu : edge Q (i - 1) = c • u) (hv : edge Q i = d • v) :
    turn Q i = SignType.sign (det u v) := by
  rw [turn_det, hu, hv]
  have hdet : det (c • u) (d • v) = (c * d) * det u v := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hdet, sign_mul, sign_pos (mul_pos hc hd), one_mul]

/-- Two corners (of two polygons) whose edges agree up to positive rescaling have the same principal
turn — the hypothesis `he` of the ledger, corner by corner. -/
theorem s7i_principalTurn_eq_of_edges_pos_smul {k₁ k : ℕ} (Q₁ : LabelledTuple k₁) (Q : LabelledTuple k)
    (i₁ : ZMod k₁) (i : ZMod k) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hu : edge Q (i - 1) = c • edge Q₁ (i₁ - 1)) (hv : edge Q i = d • edge Q₁ i₁) :
    principalTurn Q i = principalTurn Q₁ i₁ :=
  s7i_principalTurn_eq_of_pos_smul Q i hc hd hu hv

/-- Equal edges give equal principal turns (the `c = d = 1` case). -/
theorem s7i_principalTurn_eq_of_edges_eq {k₁ k : ℕ} (Q₁ : LabelledTuple k₁) (Q : LabelledTuple k)
    (i₁ : ZMod k₁) (i : ZMod k) (hu : edge Q (i - 1) = edge Q₁ (i₁ - 1)) (hv : edge Q i = edge Q₁ i₁) :
    principalTurn Q i = principalTurn Q₁ i₁ := by
  unfold principalTurn
  rw [hu, hv]

/-! #### eq. s7c:rotation-ledger on regular polygons, through the corner correspondence of U110-C -/

/-- Bounds of a principal turn of a regular polygon: `ϑ_i ∈ (−π, π)` (lem:rot). -/
theorem s7i_principalTurn_bounds {k : ℕ} {Q : LabelledTuple k} (h : Regular Q) (i : ZMod k) :
    -Real.pi < principalTurn Q i ∧ principalTurn Q i < Real.pi :=
  principalAngle_bounds (h i)

/-- Splitting one corner off the turn sum: `Σ_i ϑ_i = Σ_{i ≠ j} ϑ_i + ϑ_j`. -/
theorem s7i_sum_principalTurn_split {k : ℕ} [NeZero k] (Q : LabelledTuple k) (j : ZMod k) :
    ∑ i, principalTurn Q i =
      ∑ x : {i : ZMod k // i ≠ j}, principalTurn Q x.1 + principalTurn Q j := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)]
  congr 1
  exact Finset.sum_subtype (Finset.univ.erase j) (fun i => by simp) (principalTurn Q)

/-- The turn sums of the three contact carriers, given the principal-turn-preserving noncontact corner
correspondence `e`: `Σϑ(Q₁) + Σϑ(Q₂) − Σϑ(Q) = ϑ_{j₁}(Q₁) + ϑ_{j₂}(Q₂) − ϑ_j(Q)` ("Subtract the explicit
full contact turn from the sum of the two half turns, and add the unchanged noncontact turns"). -/
theorem s7i_ledger_sum {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    (Q₁ : LabelledTuple k₁) (Q₂ : LabelledTuple k₂) (Q : LabelledTuple k)
    (j₁ : ZMod k₁) (j₂ : ZMod k₂) (j : ZMod k)
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x) :
    (∑ i, principalTurn Q₁ i) + (∑ i, principalTurn Q₂ i) - ∑ i, principalTurn Q i =
      principalTurn Q₁ j₁ + principalTurn Q₂ j₂ - principalTurn Q j := by
  rw [s7i_sum_principalTurn_split Q₁ j₁, s7i_sum_principalTurn_split Q₂ j₂,
    s7i_sum_principalTurn_split Q j]
  have hsplit : ∑ x : {i : ZMod k // i ≠ j}, principalTurn Q x.1 =
      ∑ x : {i : ZMod k₁ // i ≠ j₁}, principalTurn Q₁ x.1 +
        ∑ x : {i : ZMod k₂ // i ≠ j₂}, principalTurn Q₂ x.1 := by
    have h1 : ∑ x : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂},
        Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
          (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x =
        ∑ x : {i : ZMod k // i ≠ j}, principalTurn Q x.1 :=
      Fintype.sum_equiv e _ _ (fun x => (he x).symm)
    rw [← h1, Fintype.sum_sum_type]
    rfl
  rw [hsplit]
  ring

/-- The rotation numbers combine as the contact turns do:
`rot(Q₁) + rot(Q₂) − rot(Q) = (ϑ_{j₁} + ϑ_{j₂} − ϑ_j) / 2π`. -/
theorem s7i_rotation_ledger_sum {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    (Q₁ : LabelledTuple k₁) (Q₂ : LabelledTuple k₂) (Q : LabelledTuple k)
    (j₁ : ZMod k₁) (j₂ : ZMod k₂) (j : ZMod k)
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x) :
    rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q =
      (principalTurn Q₁ j₁ + principalTurn Q₂ j₂ - principalTurn Q j) / (2 * Real.pi) := by
  unfold rotationNumber
  rw [← s7i_ledger_sum Q₁ Q₂ Q j₁ j₂ j e he]
  ring

/-- Three regular polygons: the combination of contact turns is an integer multiple of `2π`
(lem:rot `rotationNumber_integer` three times). -/
theorem s7i_ledger_int {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    (j₁ : ZMod k₁) (j₂ : ZMod k₂) (j : ZMod k)
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x) :
    ∃ m : ℤ, rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q = m ∧
      principalTurn Q₁ j₁ + principalTurn Q₂ j₂ - principalTurn Q j = m * (2 * Real.pi) := by
  obtain ⟨m₁, hm₁⟩ := rotationNumber_integer h₁
  obtain ⟨m₂, hm₂⟩ := rotationNumber_integer h₂
  obtain ⟨m, hm⟩ := rotationNumber_integer h
  refine ⟨m₁ + m₂ - m, ?_, ?_⟩
  · rw [hm₁, hm₂, hm]
    push_cast
    ring
  · have hs := s7i_rotation_ledger_sum Q₁ Q₂ Q j₁ j₂ j e he
    rw [hm₁, hm₂, hm] at hs
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    rw [eq_div_iff hpi] at hs
    rw [← hs]
    push_cast
    ring

/-- A principal-turn-preserving corner correspondence preserves the turns (the form U110-C's selector
laws take), by `principalTurn_sign`. -/
theorem s7i_turn_elim_of_principalTurn_elim {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x) :
    ∀ x, turn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => turn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => turn Q₂ y.1) x := by
  intro x
  rw [← principalTurn_sign h, he x]
  rcases x with y | y
  · simp only [Sum.elim_inl]
    exact principalTurn_sign h₁ y.1
  · simp only [Sum.elim_inr]
    exact principalTurn_sign h₂ y.1

/-- **eq. s7c:rotation-ledger, interlacing line** (`ε = 1`): contact turns of sign `s₀` on all three
carriers ⇒ `rot(L₁) + rot(L₂) − rot(L*) = 0`. -/
theorem s7i_rotation_ledger_interlacing {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn Q₁ j₁ = s₀) (hj₂ : turn Q₂ j₂ = s₀) (hj : turn Q j = s₀) :
    rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q = 0 := by
  obtain ⟨m, hrot, hm⟩ := s7i_ledger_int h₁ h₂ h j₁ j₂ j e he
  have hled := s7i_ledger_of_int hm (s7i_principalTurn_bounds h₁ j₁) (s7i_principalTurn_bounds h₂ j₂)
    (s7i_principalTurn_bounds h j) hs₀ ((principalTurn_sign h₁ j₁).trans hj₁)
    ((principalTurn_sign h₂ j₂).trans hj₂)
  have h0 := hled.1 ((principalTurn_sign h j).trans hj)
  rw [h0] at hm
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hm0 : (m : ℝ) = 0 := by
    rcases mul_eq_zero.mp hm.symm with hm' | hm'
    · exact hm'
    · exact absurd hm' hpi
  rw [hrot, hm0]

/-- **eq. s7c:rotation-ledger, noninterlacing line** (`ε = 0`): half contact turns of sign `s₀`, full
contact turn of sign `−s₀` ⇒ `rot(L₁) + rot(L₂) − rot(L*) = s₀` (the full-turn correction). -/
theorem s7i_rotation_ledger_noninterlacing {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn Q₁ j₁ = s₀) (hj₂ : turn Q₂ j₂ = s₀) (hj : turn Q j = -s₀) :
    rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q = (s₀ : ℝ) := by
  obtain ⟨m, hrot, hm⟩ := s7i_ledger_int h₁ h₂ h j₁ j₂ j e he
  have hled := s7i_ledger_of_int hm (s7i_principalTurn_bounds h₁ j₁) (s7i_principalTurn_bounds h₂ j₂)
    (s7i_principalTurn_bounds h j) hs₀ ((principalTurn_sign h₁ j₁).trans hj₁)
    ((principalTurn_sign h₂ j₂).trans hj₂)
  have h0 := hled.2 ((principalTurn_sign h j).trans hj)
  rw [h0] at hm
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hm0 : (m : ℝ) = (s₀ : ℝ) := by
    have : (2 * Real.pi) * (s₀ : ℝ) = (2 * Real.pi) * (m : ℝ) := by rw [hm]; ring
    exact (mul_left_cancel₀ hpi this).symm
  rw [hrot, hm0]

/-! #### The `R`-identities: same-sign uniformity puts the three rotations on one ray (lem:uniformrot) -/

/-- lem:uniformrot on a uniform polygon of sign `τ`: `τ · rot ≥ 1`, hence `|rot| = τ · rot`. -/
theorem s7i_rotation_on_ray_of_uniform {k : ℕ} [NeZero k] (hk : 3 ≤ k) {Q : LabelledTuple k}
    (h : Regular Q) {τ : SignType} (hτ : τ ≠ 0) (hall : ∀ i, turn Q i = τ) :
    1 ≤ (τ : ℝ) * rotationNumber Q ∧ |rotationNumber Q| = (τ : ℝ) * rotationNumber Q := by
  have hne : ∀ i, turn Q i ≠ 0 := fun i => by rw [hall i]; exact hτ
  have hu := uniform_rotation hk Q h hne
  rcases s7i_signType_cases hτ with rfl | rfl
  · have h1 := hu.1 hall
    simp only [SignType.coe_one, one_mul]
    exact ⟨h1, abs_of_pos (by linarith)⟩
  · have h1 := hu.2.1 hall
    simp only [SignType.coe_neg_one, neg_mul, one_mul]
    exact ⟨by linarith, abs_of_neg (by linarith)⟩

/-- lem:uniformrot on a one-dissent polygon (one turn `−τ` at `j₀`, all others `τ`): `τ · rot ≥ 1`,
hence `|rot| = τ · rot`. -/
theorem s7i_rotation_on_ray_of_dissent {k : ℕ} [NeZero k] (hk : 3 ≤ k) {Q : LabelledTuple k}
    (h : Regular Q) {τ : SignType} (hτ : τ ≠ 0) (j₀ : ZMod k) (h0 : turn Q j₀ = -τ)
    (hrest : ∀ i, i ≠ j₀ → turn Q i = τ) :
    1 ≤ (τ : ℝ) * rotationNumber Q ∧ |rotationNumber Q| = (τ : ℝ) * rotationNumber Q := by
  have hne : ∀ i, turn Q i ≠ 0 := by
    intro i
    by_cases hi : i = j₀
    · rw [hi, h0]
      exact s7i_neg_signType_ne_zero hτ
    · rw [hrest i hi]
      exact hτ
  have hu := uniform_rotation hk Q h hne
  rcases s7i_signType_cases hτ with rfl | rfl
  · have h1 := hu.2.2.1 ⟨j₀, h0, hrest⟩
    simp only [SignType.coe_one, one_mul]
    exact ⟨h1, abs_of_pos (by linarith)⟩
  · have h1 := hu.2.2.2 ⟨j₀, by rw [h0, neg_neg], hrest⟩
    simp only [SignType.coe_neg_one, neg_mul, one_mul]
    exact ⟨by linarith, abs_of_neg (by linarith)⟩

/-- **eq. s7c:interlacing-absolute** (sm-4:655-663): in a live interlacing row all three contact carriers
are uniform of the contact sign `s₀` (U110-C `s7c_uniform_halves_of_interlacing`); the ledger and
lem:uniformrot give `R_L = R₁ + R₂` (`R = |rot|`). -/
theorem s7i_interlacing_absolute {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    (hk₁ : 3 ≤ k₁) (hk₂ : 3 ≤ k₂) (hk : 3 ≤ k)
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hall₁ : ∀ i, turn Q₁ i = s₀) (hall₂ : ∀ i, turn Q₂ i = s₀) (hall : ∀ i, turn Q i = s₀) :
    |rotationNumber Q| = |rotationNumber Q₁| + |rotationNumber Q₂| := by
  have hled := s7i_rotation_ledger_interlacing h₁ h₂ h e he hs₀ (hall₁ j₁) (hall₂ j₂) (hall j)
  obtain ⟨_, ha₁⟩ := s7i_rotation_on_ray_of_uniform hk₁ h₁ hs₀ hall₁
  obtain ⟨_, ha₂⟩ := s7i_rotation_on_ray_of_uniform hk₂ h₂ hs₀ hall₂
  obtain ⟨_, ha⟩ := s7i_rotation_on_ray_of_uniform hk h hs₀ hall
  rw [ha₁, ha₂, ha, ← mul_add]
  congr 1
  linarith

/-- **eq. s7c:noninterlacing-rotation** (sm-4:748-757): in a live noninterlacing row the full carrier is
uniform of sign `τ = −s₀` and each half has exactly one dissent, its contact corner of sign `s₀`
(U110-C `s7c_dissent_halves_of_noninterlacing`); lem:uniformrot puts all three rotations on the `τ` ray
and the ledger, multiplied by `τ`, gives `R₁ + R₂ − R_L = τ s₀ = −1`. -/
theorem s7i_noninterlacing_absolute {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    (hk₁ : 3 ≤ k₁) (hk₂ : 3 ≤ k₂) (hk : 3 ≤ k)
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn Q₁ j₁ = s₀) (hrest₁ : ∀ i, i ≠ j₁ → turn Q₁ i = -s₀)
    (hj₂ : turn Q₂ j₂ = s₀) (hrest₂ : ∀ i, i ≠ j₂ → turn Q₂ i = -s₀)
    (hall : ∀ i, turn Q i = -s₀) :
    |rotationNumber Q₁| + |rotationNumber Q₂| - |rotationNumber Q| = -1 := by
  have hled := s7i_rotation_ledger_noninterlacing h₁ h₂ h e he hs₀ hj₁ hj₂ (hall j)
  have hτ : -s₀ ≠ 0 := s7i_neg_signType_ne_zero hs₀
  obtain ⟨_, ha₁⟩ := s7i_rotation_on_ray_of_dissent hk₁ h₁ hτ j₁ (by rw [hj₁, neg_neg]) hrest₁
  obtain ⟨_, ha₂⟩ := s7i_rotation_on_ray_of_dissent hk₂ h₂ hτ j₂ (by rw [hj₂, neg_neg]) hrest₂
  obtain ⟨_, ha⟩ := s7i_rotation_on_ray_of_uniform hk h hτ hall
  rw [ha₁, ha₂, ha]
  have hsq : (s₀ : ℝ) * (s₀ : ℝ) = 1 := by
    rcases s7i_signType_cases hs₀ with rfl | rfl <;> simp
  have hc : ((-s₀ : SignType) : ℝ) = -(s₀ : ℝ) := by
    rcases s7i_signType_cases hs₀ with rfl | rfl <;> simp
  rw [hc]
  have : -(s₀ : ℝ) * (rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q) = -(s₀ : ℝ) * (s₀ : ℝ) := by
    rw [hled]
  linear_combination this - hsq

/-! #### The ledger on carriers (`carrierRotation`, `carrierRotationInt`; def:uniform, def:C) -/

/-- The turn-preserving (SignType) correspondence of U110-C from the principal-turn-preserving one, on
corner polygons of carriers of decompositions. -/
theorem s7i_carrier_turn_elim (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x) :
    ∀ x, turn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x :=
  s7i_turn_elim_of_principalTurn_elim (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁)
    (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂) (ccpCornerPolygon_regular hn hP hS q) e he

/-- eq. s7c:rotation-ledger on carriers, interlacing line: `r_{L₁} + r_{L₂} − r_{L*} = 0`. -/
theorem s7i_carrierRotation_ledger_interlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (hj : turn (ccpCornerPolygon hn hP S q) j = s₀) :
    carrierRotation hn₁ hP₁ S₁ q₁ + carrierRotation hn₂ hP₂ S₂ q₂ - carrierRotation hn hP S q = 0 :=
  s7i_rotation_ledger_interlacing (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁)
    (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂) (ccpCornerPolygon_regular hn hP hS q) e he hs₀ hj₁ hj₂ hj

/-- eq. s7c:rotation-ledger on carriers, noninterlacing line: `r_{L₁} + r_{L₂} − r_{L*} = s₀`. -/
theorem s7i_carrierRotation_ledger_noninterlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (hj : turn (ccpCornerPolygon hn hP S q) j = -s₀) :
    carrierRotation hn₁ hP₁ S₁ q₁ + carrierRotation hn₂ hP₂ S₂ q₂ - carrierRotation hn hP S q = (s₀ : ℝ) :=
  s7i_rotation_ledger_noninterlacing (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁)
    (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂) (ccpCornerPolygon_regular hn hP hS q) e he hs₀ hj₁ hj₂ hj

/-- **eq. s7c:interlacing-absolute on carriers, in ℤ** (`R = |r_Q|` as def:C's `carrierRotationInt`):
three uniform carriers of the contact sign `s₀` ⇒ `R_{L*} = R_{L₁} + R_{L₂}`. -/
theorem s7i_carrierRotationInt_interlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hall₁ : ∀ i, turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = s₀)
    (hall₂ : ∀ i, turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = s₀)
    (hall : ∀ i, turn (ccpCornerPolygon hn hP S q) i = s₀) :
    |carrierRotationInt hn hP S q| = |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| := by
  have hR := s7i_interlacing_absolute (ccpCornerCount_ge_three hn₁ hP₁ hS₁ q₁)
    (ccpCornerCount_ge_three hn₂ hP₂ hS₂ q₂) (ccpCornerCount_ge_three hn hP hS q)
    (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁) (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂)
    (ccpCornerPolygon_regular hn hP hS q) e he hs₀ hall₁ hall₂ hall
  have hc : ((|carrierRotationInt hn hP S q| : ℤ) : ℝ) =
      ((|carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| : ℤ) : ℝ) := by
    push_cast
    rw [carrierRotationInt_cast hn hP hS q, carrierRotationInt_cast hn₁ hP₁ hS₁ q₁,
      carrierRotationInt_cast hn₂ hP₂ hS₂ q₂]
    exact hR
  exact_mod_cast hc

/-- **eq. s7c:noninterlacing-rotation on carriers, in ℤ**: full carrier uniform of sign `−s₀`, halves
one-dissent at their contact corners (sign `s₀`) ⇒ `R_{L₁} + R_{L₂} − R_{L*} = −1`. -/
theorem s7i_carrierRotationInt_noninterlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hrest₁ : ∀ i, i ≠ j₁ → turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = -s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (hrest₂ : ∀ i, i ≠ j₂ → turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = -s₀)
    (hall : ∀ i, turn (ccpCornerPolygon hn hP S q) i = -s₀) :
    |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| - |carrierRotationInt hn hP S q| = -1 := by
  have hR := s7i_noninterlacing_absolute (ccpCornerCount_ge_three hn₁ hP₁ hS₁ q₁)
    (ccpCornerCount_ge_three hn₂ hP₂ hS₂ q₂) (ccpCornerCount_ge_three hn hP hS q)
    (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁) (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂)
    (ccpCornerPolygon_regular hn hP hS q) e he hs₀ hj₁ hrest₁ hj₂ hrest₂ hall
  have hc : ((|carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hP S q| : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by
    push_cast
    rw [carrierRotationInt_cast hn hP hS q, carrierRotationInt_cast hn₁ hP₁ hS₁ q₁,
      carrierRotationInt_cast hn₂ hP₂ hS₂ q₂]
    exact hR
  exact_mod_cast hc

/-! #### The slot identities (pure ℤ; def:C `d_Q = 1 − m_Q − |r_Q|` with the writhe `w = m` of the
positive lift, `positiveLift_writhe_eq_carrierCrossingCount`) -/

/-- `k_H = k_L − 2` (sm-4:629-632): `w_H = w_L + 2`, `R_H = R_L` (eq. s7c:full-rotation). -/
theorem s7i_high_slot {kL kH wL wH RL RH : ℤ} (hkL : kL = 1 - wL - RL) (hkH : kH = 1 - wH - RH)
    (hw : wH = wL + 2) (hR : RH = RL) : kH = kL - 2 := by
  omega

/-- **eq. s7c:interlacing-slot** (sm-4:665-670): `w_L = w₁ + w₂ + 2ℓ − 1` and `R_L = R₁ + R₂` ⇒
`k_L = K − 2ℓ` with `K = k₁ + k₂`. -/
theorem s7i_interlacing_slot {kL k₁ k₂ wL w₁ w₂ RL R₁ R₂ ℓ : ℤ}
    (hkL : kL = 1 - wL - RL) (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂)
    (hw : wL = w₁ + w₂ + 2 * ℓ - 1) (hR : RL = R₁ + R₂) :
    kL = k₁ + k₂ - 2 * ℓ := by
  omega

/-- **eq. s7c:noninterlacing-slot** (sm-4:758-762): `w_L = w₁ + w₂ + 2ℓ` and `R₁ + R₂ − R_L = −1` ⇒
`K − k_L = 2ℓ + 2`. -/
theorem s7i_noninterlacing_slot {kL k₁ k₂ wL w₁ w₂ RL R₁ R₂ ℓ : ℤ}
    (hkL : kL = 1 - wL - RL) (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂)
    (hw : wL = w₁ + w₂ + 2 * ℓ) (hR : R₁ + R₂ - RL = -1) :
    k₁ + k₂ - kL = 2 * ℓ + 2 := by
  omega

/-- **eqs. s7c:different-low-slot / s7c:different-high-slot** (sm-4:827-832): `w_L = w₁ + w₂`,
`w_H = w₁ + w₂ + 2`, `R₁ + R₂ − R_L = −1`, `R_H = R_L` ⇒ `k_L = K − 2`, `k_H = K − 4`. -/
theorem s7i_different_slot {kL kH k₁ k₂ wL wH w₁ w₂ RL RH R₁ R₂ : ℤ}
    (hkL : kL = 1 - wL - RL) (hkH : kH = 1 - wH - RH) (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂)
    (hwL : wL = w₁ + w₂) (hwH : wH = w₁ + w₂ + 2) (hR : R₁ + R₂ - RL = -1) (hRH : RH = RL) :
    kL = k₁ + k₂ - 2 ∧ kH = k₁ + k₂ - 4 := by
  omega

end S7IRotationLedger

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
