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

/-! ### U112-A helpers (prefix `sfta_`): the soft mark transport and the carrier correspondence for
common supports (PLAN_FINAL.md §3.4, §4 U112-A).

An abstract *insertion mark transport* `sfta_InsertMarkTransport hn hP hQ` from the generic `n`-gon `P`
to the generic `(n+1)`-gon `Q` (the `MarkTransport` of SM/CChamber.lean for mark sets differing by
exactly one vertex `new`, inserted right after the attachment vertex `att`) carries the whole Carrier
lane: the cyclic and smoothing successors (`markSuccessor_of_ne/_att/_new`,
`smoothingSuccessor_of_ne/_att/_new`), the cycles (`sameCycle_iff`, `sameCycle_new`), the carriers
(`component : Component ≃ Component`, `component_owner`, `owner_new`), their crossings and `m_Q`,
decompositions, true corners, the mark and corner lists (insertion shape for the carrier through the
attachment, rotation for the others), corner counts, uniformity (`carrierUniform_iff_insertion`,
`carrierUniform_iff_of_ne`, `carrierUniform_iff`), the index set, the corner coefficients, the signed
sum (`sum_transport`), the left-turn count (`leftTurns_transport`) and the state sum up to the sign
`(−1)^{ℓ(Q)+ℓ(P)}` (`cornerStateSum_transport`).  The soft instance `sfta_softTransport` (non-loop
sectors; vertices `softOldIndex j`, new vertex `softNewIndex j`, crossings/visits the accepted
`softInheritedCrossing/Visit`) has its mark-list clause proved by sortedness
(`sfta_soft_markList_insertion`; literal when `j ≠ 0`, one rotation when `j = 0`, where `M_ε` becomes
the label `0`) and its interlacement clause by the visit-order clause of lem:soft-generic
(`sfta_interlaces_transport`); `sfta_soft_data` extracts from `soft_family_generic` on one interval
exactly the hypotheses of `sfta_softTransport` and `sfta_softTransport_markTurn` (vertex turns,
`−χ₋` at `μ_j`, `−χ₊` at `M_ε`, inherited crossing signs). -/

section ListLayer
variable {α β : Type*}

/-- `R` is a rotation of `L` mapped by `f` with `y` inserted immediately after `f a₀`. -/
def sfta_IsInsertion (f : α → β) (a₀ : α) (y : β) (L : List α) (R : List β) : Prop :=
  ∃ L₁ L₂ : List α, L = L₁ ++ a₀ :: L₂ ∧ R.IsRotated (L₁.map f ++ f a₀ :: y :: L₂.map f)

theorem sfta_insert_length (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) :
    (L₁.map f ++ f a :: y :: L₂.map f).length = (L₁ ++ a :: L₂).length + 1 := by
  simp only [List.length_append, List.length_map, List.length_cons]; omega

theorem sfta_insert_perm (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) :
    (L₁.map f ++ f a :: y :: L₂.map f).Perm (y :: (L₁ ++ a :: L₂).map f) := by
  have h := List.perm_middle (l₁ := L₁.map f ++ [f a]) (a := y) (l₂ := L₂.map f)
  simpa only [List.append_assoc, List.singleton_append, List.map_append, List.map_cons] using h

theorem sfta_insert_nodup (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) (hf : Function.Injective f)
    (hL : (L₁ ++ a :: L₂).Nodup) (hy : y ∉ (L₁ ++ a :: L₂).map f) :
    (L₁.map f ++ f a :: y :: L₂.map f).Nodup :=
  (sfta_insert_perm L₁ L₂ a f y).nodup_iff.mpr (List.nodup_cons.mpr ⟨hy, hL.map hf⟩)

theorem sfta_insert_mem (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) (m : β) :
    m ∈ L₁.map f ++ f a :: y :: L₂.map f ↔ m = y ∨ ∃ x ∈ L₁ ++ a :: L₂, f x = m := by
  rw [(sfta_insert_perm L₁ L₂ a f y).mem_iff, List.mem_cons, List.mem_map]

theorem sfta_insert_getElem_le (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) {i : ℕ}
    (hi : i ≤ L₁.length) (h₁ : i < (L₁ ++ a :: L₂).length)
    (h₂ : i < (L₁.map f ++ f a :: y :: L₂.map f).length) :
    (L₁.map f ++ f a :: y :: L₂.map f)[i] = f ((L₁ ++ a :: L₂)[i]) := by
  rcases lt_or_eq_of_le hi with hlt | heq
  · rw [List.getElem_append_left (by simpa using hlt), List.getElem_append_left hlt,
      List.getElem_map]
  · subst heq
    rw [List.getElem_append_right (by simp), List.getElem_append_right le_rfl]
    simp

theorem sfta_insert_getElem_gt (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) {i : ℕ}
    (hi : L₁.length < i) (h₁ : i < (L₁ ++ a :: L₂).length)
    (h₂ : i + 1 < (L₁.map f ++ f a :: y :: L₂.map f).length) :
    (L₁.map f ++ f a :: y :: L₂.map f)[i + 1] = f ((L₁ ++ a :: L₂)[i]) := by
  rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, i - L₁.length = k + 1 := ⟨i - L₁.length - 1, by omega⟩
  have h3 : i + 1 - (L₁.map f).length = k + 2 := by simp only [List.length_map]; omega
  simp only [h3, hk, List.getElem_cons_succ, List.getElem_map]

theorem sfta_insert_getElem_new (L₁ L₂ : List α) (a : α) (f : α → β) (y : β)
    (h₂ : L₁.length + 1 < (L₁.map f ++ f a :: y :: L₂.map f).length) :
    (L₁.map f ++ f a :: y :: L₂.map f)[L₁.length + 1] = y := by
  rw [List.getElem_append_right (by simp)]
  simp

theorem sfta_insert_getElem_att (L₁ L₂ : List α) (a : α) (h₁ : L₁.length < (L₁ ++ a :: L₂).length) :
    (L₁ ++ a :: L₂)[L₁.length] = a := by
  rw [List.getElem_append_right le_rfl]; simp

variable [DecidableEq α] [DecidableEq β]

/-- `next` on a nodup list, with the element given by an index up to a propositional equality. -/
theorem sfta_next_eq_of_getElem {l : List α} (hl : l.Nodup) (i : ℕ) (hi : i < l.length)
    (x : α) (hx : x ∈ l) (he : x = l[i]) :
    l.next x hx = l[(i + 1) % l.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  subst he
  exact List.next_getElem l hl i hi

theorem sfta_insert_next_of_ne (L₁ L₂ : List α) (a : α) (f : α → β) (y : β)
    (hf : Function.Injective f) (hL : (L₁ ++ a :: L₂).Nodup) (hy : y ∉ (L₁ ++ a :: L₂).map f)
    (m : α) (hm : m ∈ L₁ ++ a :: L₂) (hne : m ≠ a) (hmR : f m ∈ L₁.map f ++ f a :: y :: L₂.map f) :
    (L₁.map f ++ f a :: y :: L₂.map f).next (f m) hmR = f ((L₁ ++ a :: L₂).next m hm) := by
  have hR := sfta_insert_nodup L₁ L₂ a f y hf hL hy
  have hlen := sfta_insert_length L₁ L₂ a f y
  have hcL : L₁.length < (L₁ ++ a :: L₂).length := by simp
  obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem hm
  have hic : i ≠ L₁.length := by
    intro h
    apply hne
    rw [← hiL]
    subst h
    exact sfta_insert_getElem_att L₁ L₂ a hcL
  rw [sfta_next_eq_of_getElem hL i hi m hm hiL.symm]
  rcases lt_or_gt_of_ne hic with hlt | hgt
  · have h1 : f m = (L₁.map f ++ f a :: y :: L₂.map f)[i]'(by omega) := by
      rw [sfta_insert_getElem_le L₁ L₂ a f y hlt.le hi, hiL]
    rw [sfta_next_eq_of_getElem hR i (by omega) (f m) hmR h1]
    have hmod1 : (i + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = i + 1 :=
      Nat.mod_eq_of_lt (by omega)
    have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = i + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hmod1, hmod2]
    exact sfta_insert_getElem_le L₁ L₂ a f y (by omega) (by omega) (by omega)
  · have h1 : f m = (L₁.map f ++ f a :: y :: L₂.map f)[i + 1]'(by omega) := by
      rw [sfta_insert_getElem_gt L₁ L₂ a f y hgt hi, hiL]
    rw [sfta_next_eq_of_getElem hR (i + 1) (by omega) (f m) hmR h1]
    by_cases hlast : i + 1 < (L₁ ++ a :: L₂).length
    · have hmod1 : (i + 1 + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = i + 2 :=
        Nat.mod_eq_of_lt (by omega)
      have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = i + 1 := Nat.mod_eq_of_lt hlast
      simp only [hmod1, hmod2]
      exact sfta_insert_getElem_gt L₁ L₂ a f y (by omega) hlast (by omega)
    · have hiN : i + 1 = (L₁ ++ a :: L₂).length := by omega
      have hmod1 : (i + 1 + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = 0 := by
        rw [hlen, hiN]; simp
      have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = 0 := by rw [hiN]; simp
      simp only [hmod1, hmod2]
      exact sfta_insert_getElem_le L₁ L₂ a f y (Nat.zero_le _) (by omega) (by omega)

theorem sfta_insert_next_att (L₁ L₂ : List α) (a : α) (f : α → β) (y : β)
    (hf : Function.Injective f) (hL : (L₁ ++ a :: L₂).Nodup) (hy : y ∉ (L₁ ++ a :: L₂).map f)
    (haR : f a ∈ L₁.map f ++ f a :: y :: L₂.map f) :
    (L₁.map f ++ f a :: y :: L₂.map f).next (f a) haR = y := by
  have hR := sfta_insert_nodup L₁ L₂ a f y hf hL hy
  have hlen := sfta_insert_length L₁ L₂ a f y
  have hcL : L₁.length < (L₁ ++ a :: L₂).length := by simp
  have h1 : f a = (L₁.map f ++ f a :: y :: L₂.map f)[L₁.length]'(by omega) := by
    rw [sfta_insert_getElem_le L₁ L₂ a f y le_rfl hcL, sfta_insert_getElem_att L₁ L₂ a hcL]
  rw [sfta_next_eq_of_getElem hR L₁.length (by omega) (f a) haR h1]
  have hmod : (L₁.length + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = L₁.length + 1 :=
    Nat.mod_eq_of_lt (by omega)
  simp only [hmod]
  exact sfta_insert_getElem_new L₁ L₂ a f y (by omega)

theorem sfta_insert_next_new (L₁ L₂ : List α) (a : α) (f : α → β) (y : β)
    (hf : Function.Injective f) (hL : (L₁ ++ a :: L₂).Nodup) (hy : y ∉ (L₁ ++ a :: L₂).map f)
    (hyR : y ∈ L₁.map f ++ f a :: y :: L₂.map f) (ha : a ∈ L₁ ++ a :: L₂) :
    (L₁.map f ++ f a :: y :: L₂.map f).next y hyR = f ((L₁ ++ a :: L₂).next a ha) := by
  have hR := sfta_insert_nodup L₁ L₂ a f y hf hL hy
  have hlen := sfta_insert_length L₁ L₂ a f y
  have hcL : L₁.length < (L₁ ++ a :: L₂).length := by simp
  have h1 : y = (L₁.map f ++ f a :: y :: L₂.map f)[L₁.length + 1]'(by omega) :=
    (sfta_insert_getElem_new L₁ L₂ a f y (by omega)).symm
  rw [sfta_next_eq_of_getElem hR (L₁.length + 1) (by omega) y hyR h1,
    sfta_next_eq_of_getElem hL L₁.length hcL a ha (sfta_insert_getElem_att L₁ L₂ a hcL).symm]
  by_cases hlast : L₁.length + 1 < (L₁ ++ a :: L₂).length
  · have hmod1 : (L₁.length + 1 + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length =
        L₁.length + 2 := Nat.mod_eq_of_lt (by omega)
    have hmod2 : (L₁.length + 1) % (L₁ ++ a :: L₂).length = L₁.length + 1 := Nat.mod_eq_of_lt hlast
    simp only [hmod1, hmod2]
    exact sfta_insert_getElem_gt L₁ L₂ a f y (by omega) hlast (by omega)
  · have hiN : L₁.length + 1 = (L₁ ++ a :: L₂).length := by omega
    have hmod1 : (L₁.length + 1 + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = 0 := by
      rw [hlen, hiN]; simp
    have hmod2 : (L₁.length + 1) % (L₁ ++ a :: L₂).length = 0 := by rw [hiN]; simp
    simp only [hmod1, hmod2]
    exact sfta_insert_getElem_le L₁ L₂ a f y (Nat.zero_le _) (by omega) (by omega)

end ListLayer


section InsertTransport

theorem sfta_next_congr {α : Type*} [DecidableEq α] {l l' : List α} (h : l = l') (x : α) (hx : x ∈ l) :
    l.next x hx = l'.next x (h ▸ hx) := by
  subst h; rfl


/-- An *insertion mark transport* from the generic `n`-gon `P` to the generic `(n+1)`-gon `Q`:
compatible bijections of crossings and visits, a vertex map `vert` with one new vertex `new`
inserted immediately after the attachment vertex `att` in the sorted mark list (up to rotation),
and preserved interlacement.  This is the `MarkTransport` of SM/CChamber.lean for mark sets that
differ by exactly one vertex (the soft insertion `P ↦ P_ε` of def:soft, sm-4:1024-1057). -/
structure sfta_InsertMarkTransport (hn : 3 ≤ n) {P : LabelledTuple n} {Q : LabelledTuple (n + 1)}
    (hP : Generic P) (hQ : Generic Q) where
  vert : ZMod n → ZMod (n + 1)
  new : ZMod (n + 1)
  att : ZMod n
  cross : Crossing P ≃ Crossing Q
  visit : Visit P ≃ Visit Q
  visit_fst : ∀ v, (visit v).1 = cross v.1
  markList_insertion : sfta_IsInsertion (Sum.map vert visit) (Sum.inl att) (Sum.inl new)
    (markList hn hP) (markList (by omega) hQ)
  interlaces_iff : ∀ x y, Interlaces (by omega) hQ (cross x) (cross y) ↔ Interlaces hn hP x y

namespace sfta_InsertMarkTransport

variable {hn : 3 ≤ n} {P : LabelledTuple n} {Q : LabelledTuple (n + 1)} {hP : Generic P}
  {hQ : Generic Q} (τ : sfta_InsertMarkTransport hn hP hQ)

/-- The induced map of marks (injective, missing exactly `Sum.inl new`). -/
def toMark : Mark P → Mark Q := Sum.map τ.vert τ.visit

theorem toMark_inl (i : ZMod n) : τ.toMark (Sum.inl i) = Sum.inl (τ.vert i) := rfl

theorem toMark_inr (v : Visit P) : τ.toMark (Sum.inr v) = Sum.inr (τ.visit v) := rfl

theorem markList_insertion' : sfta_IsInsertion τ.toMark (Sum.inl τ.att) (Sum.inl τ.new)
    (markList hn hP) (markList (by omega) hQ) := τ.markList_insertion

/-- The sorted mark list of `Q` is a permutation of `Sum.inl new :: (markList P).map toMark`. -/
theorem markList_perm :
    (markList (by omega : 3 ≤ n + 1) hQ).Perm (Sum.inl τ.new :: (markList hn hP).map τ.toMark) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  refine hrot.perm.trans ?_
  rw [hL]
  exact sfta_insert_perm L₁ L₂ _ _ _

theorem new_cons_map_nodup : (Sum.inl τ.new :: (markList hn hP).map τ.toMark).Nodup :=
  τ.markList_perm.nodup_iff.mp (markList_nodup _ hQ)

theorem toMark_injective : Function.Injective τ.toMark := by
  have h := (List.nodup_cons.mp τ.new_cons_map_nodup).2
  intro a b hab
  exact List.inj_on_of_nodup_map h (mem_markList hn hP a) (mem_markList hn hP b) hab

theorem new_notMem_map : Sum.inl τ.new ∉ (markList hn hP).map τ.toMark :=
  (List.nodup_cons.mp τ.new_cons_map_nodup).1

theorem toMark_ne_new (m : Mark P) : τ.toMark m ≠ Sum.inl τ.new := fun h =>
  τ.new_notMem_map (List.mem_map.mpr ⟨m, mem_markList hn hP m, h⟩)

theorem vert_ne_new (i : ZMod n) : τ.vert i ≠ τ.new := fun h =>
  τ.toMark_ne_new (Sum.inl i) (by rw [toMark_inl, h])

theorem vert_injective : Function.Injective τ.vert := fun i k h =>
  Sum.inl_injective (τ.toMark_injective (a₁ := Sum.inl i) (a₂ := Sum.inl k) (by rw [toMark_inl, toMark_inl, h]))

/-- Every mark of `Q` is the new vertex or a transported mark. -/
theorem exhaust (m : Mark Q) : m = Sum.inl τ.new ∨ ∃ a : Mark P, τ.toMark a = m := by
  have hm := τ.markList_perm.mem_iff.mp (mem_markList _ hQ m)
  rw [List.mem_cons, List.mem_map] at hm
  rcases hm with h | ⟨a, _, ha⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, ha⟩

theorem vert_exhaust (a : ZMod (n + 1)) : a = τ.new ∨ ∃ i : ZMod n, τ.vert i = a := by
  rcases τ.exhaust (Sum.inl a) with h | ⟨m, hm⟩
  · exact Or.inl (Sum.inl_injective h)
  · cases m with
    | inl i => exact Or.inr ⟨i, Sum.inl_injective hm⟩
    | inr v => exact absurd hm (by rw [toMark_inr]; exact Sum.inr_ne_inl)

/-- The transported support. -/
def support (S : Finset (Crossing P)) : Finset (Crossing Q) :=
  S.map τ.cross.toEmbedding

theorem mem_support (S : Finset (Crossing P)) (x : Crossing P) :
    τ.cross x ∈ τ.support S ↔ x ∈ S := by
  simp only [support, Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem support_card (S : Finset (Crossing P)) : (τ.support S).card = S.card :=
  Finset.card_map _

theorem support_surjective (S' : Finset (Crossing Q)) : ∃ S, τ.support S = S' :=
  ⟨S'.map τ.cross.symm.toEmbedding, by simp [support, Finset.map_map]⟩

theorem support_injective : Function.Injective τ.support := fun S T h =>
  Finset.map_injective τ.cross.toEmbedding h

/-- The visit twin is carried to the visit twin. -/
theorem twin_eq (v : Visit P) : τ.visit (visitTwin v) = visitTwin (τ.visit v) := by
  apply visitTwin_unique (τ.visit v) (τ.visit (visitTwin v))
  · rw [τ.visit_fst, τ.visit_fst, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v (τ.visit.injective h)

/-! ### The cyclic successor: literal for marks other than the attachment, through the new vertex
at the attachment -/

theorem markSuccessor_of_ne (m : Mark P) (hm : m ≠ Sum.inl τ.att) :
    markSuccessor (by omega) hQ (τ.toMark m) = τ.toMark (markSuccessor hn hP m) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  have hy : Sum.inl τ.new ∉ (L₁ ++ Sum.inl τ.att :: L₂).map τ.toMark := by
    rw [← hL]; exact τ.new_notMem_map
  rw [markSuccessor_apply, markSuccessor_apply, nextMark_eq_list_next, nextMark_eq_list_next,
    List.isRotated_next_eq hrot (markList_nodup _ hQ), sfta_next_congr hL]
  exact sfta_insert_next_of_ne L₁ L₂ _ τ.toMark _ τ.toMark_injective hnd hy m
    (hL ▸ mem_markList hn hP m) hm _

theorem markSuccessor_att :
    markSuccessor (by omega) hQ (Sum.inl (τ.vert τ.att)) = Sum.inl τ.new := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  have hy : Sum.inl τ.new ∉ (L₁ ++ Sum.inl τ.att :: L₂).map τ.toMark := by
    rw [← hL]; exact τ.new_notMem_map
  rw [markSuccessor_apply, nextMark_eq_list_next,
    List.isRotated_next_eq hrot (markList_nodup _ hQ)]
  exact sfta_insert_next_att L₁ L₂ _ τ.toMark _ τ.toMark_injective hnd hy _

theorem markSuccessor_new :
    markSuccessor (by omega) hQ (Sum.inl τ.new) = τ.toMark (markSuccessor hn hP (Sum.inl τ.att)) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  have hy : Sum.inl τ.new ∉ (L₁ ++ Sum.inl τ.att :: L₂).map τ.toMark := by
    rw [← hL]; exact τ.new_notMem_map
  rw [markSuccessor_apply, markSuccessor_apply, nextMark_eq_list_next, nextMark_eq_list_next,
    List.isRotated_next_eq hrot (markList_nodup _ hQ), sfta_next_congr hL]
  exact sfta_insert_next_new L₁ L₂ _ τ.toMark _ τ.toMark_injective hnd hy _ _

theorem selectedMarkPerm_transport (S : Finset (Crossing P)) (m : Mark P) :
    selectedMarkPerm (τ.support S) (τ.toMark m) = τ.toMark (selectedMarkPerm S m) := by
  cases m with
  | inl i => rfl
  | inr v =>
    rw [toMark_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, toMark_inr]
    have hv' : (τ.visit v).1 ∈ τ.support S ↔ v.1 ∈ S := by
      rw [τ.visit_fst, τ.mem_support]
    by_cases hv : v.1 ∈ S
    · rw [selectedVisitTwin_of_mem _ _ hv, selectedVisitTwin_of_mem _ _ (hv'.mpr hv), τ.twin_eq]
    · rw [selectedVisitTwin_of_not_mem _ _ hv,
        selectedVisitTwin_of_not_mem _ _ (fun h => hv (hv'.mp h))]

theorem selectedMarkPerm_ne_att (S : Finset (Crossing P)) (m : Mark P) (hm : m ≠ Sum.inl τ.att) :
    selectedMarkPerm S m ≠ Sum.inl τ.att := by
  cases m with
  | inl i => exact hm
  | inr v => rw [selectedMarkPerm_visit]; exact Sum.inr_ne_inl

theorem smoothingSuccessor_of_ne (S : Finset (Crossing P)) (m : Mark P) (hm : m ≠ Sum.inl τ.att) :
    smoothingSuccessor (by omega) hQ (τ.support S) (τ.toMark m) =
      τ.toMark (smoothingSuccessor hn hP S m) := by
  change markSuccessor (by omega) hQ (selectedMarkPerm (τ.support S) (τ.toMark m)) =
    τ.toMark (markSuccessor hn hP (selectedMarkPerm S m))
  rw [τ.selectedMarkPerm_transport, τ.markSuccessor_of_ne _ (τ.selectedMarkPerm_ne_att S m hm)]

theorem smoothingSuccessor_att (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.support S) (Sum.inl (τ.vert τ.att)) = Sum.inl τ.new := by
  rw [smoothingSuccessor_vertex]; exact τ.markSuccessor_att

theorem smoothingSuccessor_new (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.support S) (Sum.inl τ.new) =
      τ.toMark (smoothingSuccessor hn hP S (Sum.inl τ.att)) := by
  rw [smoothingSuccessor_vertex, smoothingSuccessor_vertex]; exact τ.markSuccessor_new

/-! ### Cycles and carriers -/

theorem sameCycle_new (S : Finset (Crossing P)) :
    (smoothingSuccessor (by omega) hQ (τ.support S)).SameCycle (τ.toMark (Sum.inl τ.att))
      (Sum.inl τ.new) := by
  have h := (Equiv.Perm.SameCycle.refl (smoothingSuccessor (by omega) hQ (τ.support S))
    (τ.toMark (Sum.inl τ.att))).apply_right
  rwa [toMark_inl, τ.smoothingSuccessor_att S] at h

theorem sameCycle_of (S : Finset (Crossing P)) {a b : Mark P}
    (h : (smoothingSuccessor hn hP S).SameCycle a b) :
    (smoothingSuccessor (by omega) hQ (τ.support S)).SameCycle (τ.toMark a) (τ.toMark b) := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  clear hk
  induction k with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply]; exact Equiv.Perm.SameCycle.refl _ _
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    by_cases hm : (smoothingSuccessor hn hP S ^ k) a = Sum.inl τ.att
    · rw [hm] at ih ⊢
      have h1 := ih.apply_right.apply_right
      rwa [toMark_inl, τ.smoothingSuccessor_att, τ.smoothingSuccessor_new] at h1
    · have h1 := ih.apply_right
      rwa [τ.smoothingSuccessor_of_ne S _ hm] at h1

theorem sameCycle_iff (S : Finset (Crossing P)) (a b : Mark P) :
    (smoothingSuccessor (by omega) hQ (τ.support S)).SameCycle (τ.toMark a) (τ.toMark b) ↔
      (smoothingSuccessor hn hP S).SameCycle a b := by
  refine ⟨fun h => ?_, τ.sameCycle_of S⟩
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have key : ∀ k : ℕ, ∃ m : Mark P, (smoothingSuccessor hn hP S).SameCycle a m ∧
      ((smoothingSuccessor (by omega) hQ (τ.support S) ^ k) (τ.toMark a) = τ.toMark m ∨
        ((smoothingSuccessor (by omega) hQ (τ.support S) ^ k) (τ.toMark a) = Sum.inl τ.new ∧
          m = Sum.inl τ.att)) := by
    intro k
    induction k with
    | zero => exact ⟨a, Equiv.Perm.SameCycle.refl _ _, Or.inl (by simp)⟩
    | succ k ih =>
      obtain ⟨m, hm, hk⟩ := ih
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases hk with hk | ⟨hk, rfl⟩
      · rw [hk]
        by_cases hma : m = Sum.inl τ.att
        · subst hma
          exact ⟨Sum.inl τ.att, hm, Or.inr ⟨by rw [toMark_inl, τ.smoothingSuccessor_att], rfl⟩⟩
        · exact ⟨smoothingSuccessor hn hP S m, hm.apply_right,
            Or.inl (τ.smoothingSuccessor_of_ne S m hma)⟩
      · rw [hk, τ.smoothingSuccessor_new]
        exact ⟨smoothingSuccessor hn hP S (Sum.inl τ.att), hm.apply_right, Or.inl rfl⟩
  obtain ⟨m, hm, hmk⟩ := key k
  rw [hk] at hmk
  rcases hmk with hmk | ⟨hmk, _⟩
  · rw [← τ.toMark_injective hmk] at hm
    exact hm
  · exact absurd hmk (τ.toMark_ne_new b)

/-- The carriers of `S` correspond to the carriers of the transported support. -/
def component (S : Finset (Crossing P)) :
    Component hn hP S ≃ Component (by omega) hQ (τ.support S) :=
  Equiv.ofBijective
    (Quotient.lift (fun a => owner (by omega) hQ (τ.support S) (τ.toMark a))
      (fun a b hab => (owner_eq_iff _ hQ _ _ _).mpr (τ.sameCycle_of S hab)))
    ⟨by
      intro q r hqr
      obtain ⟨a, rfl⟩ := owner_surjective hn hP S q
      obtain ⟨b, rfl⟩ := owner_surjective hn hP S r
      apply (owner_eq_iff hn hP S a b).mpr
      exact (τ.sameCycle_iff S a b).mp ((owner_eq_iff _ hQ _ _ _).mp hqr),
     by
      intro q'
      obtain ⟨m, rfl⟩ := owner_surjective _ hQ (τ.support S) q'
      rcases τ.exhaust m with rfl | ⟨a, rfl⟩
      · refine ⟨owner hn hP S (Sum.inl τ.att), ?_⟩
        exact (owner_eq_iff _ hQ _ _ _).mpr (τ.sameCycle_new S)
      · exact ⟨owner hn hP S a, rfl⟩⟩

theorem component_owner (S : Finset (Crossing P)) (m : Mark P) :
    τ.component S (owner hn hP S m) = owner (by omega) hQ (τ.support S) (τ.toMark m) := rfl

theorem owner_new (S : Finset (Crossing P)) :
    owner (by omega) hQ (τ.support S) (Sum.inl τ.new) =
      τ.component S (owner hn hP S (Sum.inl τ.att)) := by
  rw [component_owner]
  exact ((owner_eq_iff _ hQ _ _ _).mpr (τ.sameCycle_new S)).symm

theorem carrierCrossings_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossings (by omega) hQ (τ.support S) (τ.component S q) =
      (carrierCrossings hn hP S q).map τ.cross.toEmbedding := by
  ext x'
  obtain ⟨x, rfl⟩ := τ.cross.surjective x'
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  rw [mem_carrierCrossings, mem_carrierCrossings, τ.mem_support]
  apply and_congr Iff.rfl
  constructor
  · intro h v hv
    have h1 : owner (by omega) hQ (τ.support S) (Sum.inr (τ.visit v)) = τ.component S q :=
      h (τ.visit v) (by rw [τ.visit_fst, hv])
    apply (τ.component S).injective
    exact h1
  · intro h w hw
    obtain ⟨v, rfl⟩ := τ.visit.surjective w
    have hv : v.1 = x := τ.cross.injective ((τ.visit_fst v).symm.trans hw)
    show τ.component S (owner hn hP S (Sum.inr v)) = τ.component S q
    exact congrArg _ (h v hv)

theorem carrierCrossingCount_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossingCount (by omega) hQ (τ.support S) (τ.component S q) =
      carrierCrossingCount hn hP S q := by
  rw [carrierCrossingCount_eq_card, carrierCrossingCount_eq_card,
    τ.carrierCrossings_transport, Finset.card_map]

theorem isDecomposition_transport (S : Finset (Crossing P)) :
    IsDecomposition (by omega) hQ (τ.support S) ↔ IsDecomposition hn hP S := by
  unfold IsDecomposition
  rw [mem_independentSupports_iff, mem_independentSupports_iff]
  constructor
  · intro h x hx y hy hxy hI
    exact h _ ((τ.mem_support S x).mpr hx) _ ((τ.mem_support S y).mpr hy)
      (fun he => hxy (τ.cross.injective he)) ((τ.interlaces_iff x y).mpr hI)
  · intro h x hx y hy hxy hI
    obtain ⟨x₀, rfl⟩ := τ.cross.surjective x
    obtain ⟨y₀, rfl⟩ := τ.cross.surjective y
    exact h x₀ ((τ.mem_support S x₀).mp hx) y₀ ((τ.mem_support S y₀).mp hy)
      (fun he => hxy (congrArg τ.cross he)) ((τ.interlaces_iff x₀ y₀).mp hI)

theorem isTrueCorner_transport (S : Finset (Crossing P)) (m : Mark P) :
    IsTrueCorner (τ.support S) (τ.toMark m) ↔ IsTrueCorner S m := by
  cases m with
  | inl i => rw [toMark_inl]; exact Iff.rfl
  | inr v => rw [toMark_inr, isTrueCorner_visit, isTrueCorner_visit, τ.visit_fst, τ.mem_support]

end sfta_InsertMarkTransport

end InsertTransport


section InsertLists

variable {α β : Type*}

theorem sfta_IsInsertion.filter {f : α → β} {a₀ : α} {y : β} {L : List α} {R : List β}
    (h : sfta_IsInsertion f a₀ y L R) (p : β → Bool) (p' : α → Bool) (hpp : ∀ x, p (f x) = p' x)
    (hp₀ : p' a₀ = true) (hpy : p y = true) :
    sfta_IsInsertion f a₀ y (L.filter p') (R.filter p) := by
  obtain ⟨L₁, L₂, rfl, hrot⟩ := h
  refine ⟨L₁.filter p', L₂.filter p', ?_, ?_⟩
  · simp only [List.filter_append, List.filter_cons, hp₀, ite_true]
  · refine (hrot.filter p).trans ?_
    simp only [List.filter_append, List.filter_cons, List.filter_map, Function.comp_def, hpp, hp₀,
      hpy, ite_true]
    exact List.IsRotated.refl _

theorem sfta_IsInsertion.filter_not {f : α → β} {a₀ : α} {y : β} {L : List α} {R : List β}
    (h : sfta_IsInsertion f a₀ y L R) (p : β → Bool) (p' : α → Bool) (hpp : ∀ x, p (f x) = p' x)
    (hp₀ : p' a₀ = false) (hpy : p y = false) :
    (R.filter p).IsRotated ((L.filter p').map f) := by
  obtain ⟨L₁, L₂, rfl, hrot⟩ := h
  refine (hrot.filter p).trans ?_
  simp only [List.filter_append, List.filter_cons, List.filter_map, Function.comp_def, hpp, hp₀,
    hpy, Bool.false_eq_true, ite_false, List.map_append]
  exact List.IsRotated.refl _

end InsertLists

section CornerMarks


/-- Uniformity of a carrier of a decomposition, read on the `markTurn`s of its corner list
(`turn_ccpCornerPolygon_eq_markTurn`, CX1.lean). -/
theorem sfta_carrierUniform_iff_forall_mem (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    CarrierUniform hn hP S q ↔
      ∃ σ : SignType, σ ≠ 0 ∧ ∀ m ∈ ccpCornerList hn hP S q, markTurn P m = σ := by
  unfold CarrierUniform
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h m hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have hi' : i < ccpCornerCount hn hP S q := hi
    have := h (i : ZMod (ccpCornerCount hn hP S q))
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS] at this
    unfold ccpCornerMark at this
    have hval : ((i : ZMod (ccpCornerCount hn hP S q))).val = i := ZMod.val_natCast_of_lt hi'
    simp only [hval] at this
    exact this
  · intro h k
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS]
    exact h _ (List.getElem_mem _)

end CornerMarks

namespace sfta_InsertMarkTransport

variable {hn : 3 ≤ n} {P : LabelledTuple n} {Q : LabelledTuple (n + 1)}
  {hP : Generic P} {hQ : Generic Q} (τ : sfta_InsertMarkTransport hn hP hQ)

theorem owner_toMark_eq_iff (S : Finset (Crossing P)) (q : Component hn hP S) (m : Mark P) :
    owner (by omega) hQ (τ.support S) (τ.toMark m) = τ.component S q ↔ owner hn hP S m = q := by
  rw [← τ.component_owner]
  exact (τ.component S).injective.eq_iff

/-! ### Mark lists and corner lists of the carriers: the carrier through the attachment vertex
gains the new vertex right after it; every other carrier is carried up to rotation -/

theorem componentMarkList_insertion (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) = q) :
    sfta_IsInsertion τ.toMark (Sum.inl τ.att) (Sum.inl τ.new) (componentMarkList hn hP S q)
      (componentMarkList (by omega) hQ (τ.support S) (τ.component S q)) := by
  unfold componentMarkList
  refine τ.markList_insertion'.filter _ _ (fun m => ?_) ?_ ?_
  · exact decide_eq_decide.mpr (τ.owner_toMark_eq_iff S q m)
  · exact decide_eq_true hq
  · apply decide_eq_true
    rw [τ.owner_new, hq]

theorem componentMarkList_rotated_of_ne (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) ≠ q) :
    (componentMarkList (by omega) hQ (τ.support S) (τ.component S q)).IsRotated
      ((componentMarkList hn hP S q).map τ.toMark) := by
  unfold componentMarkList
  refine τ.markList_insertion'.filter_not _ _ (fun m => ?_) ?_ ?_
  · exact decide_eq_decide.mpr (τ.owner_toMark_eq_iff S q m)
  · exact decide_eq_false hq
  · apply decide_eq_false
    rw [τ.owner_new]
    exact fun h => hq ((τ.component S).injective h)

theorem ccpCornerList_insertion (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) = q) :
    sfta_IsInsertion τ.toMark (Sum.inl τ.att) (Sum.inl τ.new) (ccpCornerList hn hP S q)
      (ccpCornerList (by omega) hQ (τ.support S) (τ.component S q)) := by
  unfold ccpCornerList
  exact (τ.componentMarkList_insertion S q hq).filter _ _
    (fun m => decide_eq_decide.mpr (τ.isTrueCorner_transport S m)) (decide_eq_true trivial)
    (decide_eq_true trivial)

theorem ccpCornerList_rotated_of_ne (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) ≠ q) :
    (ccpCornerList (by omega) hQ (τ.support S) (τ.component S q)).IsRotated
      ((ccpCornerList hn hP S q).map τ.toMark) := by
  unfold ccpCornerList
  exact Carrier.MarkTransport.isRotated_filter_map_of_forall τ.toMark (τ.componentMarkList_rotated_of_ne S q hq) _ _
    (fun a => decide_eq_decide.mpr (τ.isTrueCorner_transport S a))

theorem ccpCornerCount_insertion (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) = q) :
    ccpCornerCount (by omega) hQ (τ.support S) (τ.component S q) = ccpCornerCount hn hP S q + 1 := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.ccpCornerList_insertion S q hq
  unfold ccpCornerCount
  rw [hrot.perm.length_eq, sfta_insert_length, hL]

theorem ccpCornerCount_of_ne (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) ≠ q) :
    ccpCornerCount (by omega) hQ (τ.support S) (τ.component S q) = ccpCornerCount hn hP S q := by
  unfold ccpCornerCount
  rw [(τ.ccpCornerList_rotated_of_ne S q hq).perm.length_eq, List.length_map]

theorem mem_ccpCornerList_insertion (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) = q) (m' : Mark Q) :
    m' ∈ ccpCornerList (by omega) hQ (τ.support S) (τ.component S q) ↔
      m' = Sum.inl τ.new ∨ ∃ m ∈ ccpCornerList hn hP S q, τ.toMark m = m' := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.ccpCornerList_insertion S q hq
  rw [hrot.mem_iff, sfta_insert_mem, hL]

theorem mem_ccpCornerList_of_ne (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) ≠ q) (m' : Mark Q) :
    m' ∈ ccpCornerList (by omega) hQ (τ.support S) (τ.component S q) ↔
      ∃ m ∈ ccpCornerList hn hP S q, τ.toMark m = m' := by
  rw [(τ.ccpCornerList_rotated_of_ne S q hq).mem_iff, List.mem_map]

/-! ### Uniformity -/

theorem carrierUniform_iff_insertion (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hq : owner hn hP S (Sum.inl τ.att) = q) :
    CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔
      ∃ σ : SignType, σ ≠ 0 ∧ (∀ m ∈ ccpCornerList hn hP S q, markTurn Q (τ.toMark m) = σ) ∧
        turn Q τ.new = σ := by
  rw [sfta_carrierUniform_iff_forall_mem _ hQ ((τ.isDecomposition_transport S).mpr hS)]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h
    refine ⟨fun m hm => h _ ((τ.mem_ccpCornerList_insertion S q hq _).mpr (Or.inr ⟨m, hm, rfl⟩)), ?_⟩
    have := h _ ((τ.mem_ccpCornerList_insertion S q hq _).mpr (Or.inl rfl))
    rwa [markTurn_inl] at this
  · rintro ⟨h1, h2⟩ m' hm'
    rcases (τ.mem_ccpCornerList_insertion S q hq m').mp hm' with rfl | ⟨m, hm, rfl⟩
    · rw [markTurn_inl]; exact h2
    · exact h1 m hm

theorem carrierUniform_iff_of_ne (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hq : owner hn hP S (Sum.inl τ.att) ≠ q) :
    CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔
      ∃ σ : SignType, σ ≠ 0 ∧ ∀ m ∈ ccpCornerList hn hP S q, markTurn Q (τ.toMark m) = σ := by
  rw [sfta_carrierUniform_iff_forall_mem _ hQ ((τ.isDecomposition_transport S).mpr hS)]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h m hm
    exact h _ ((τ.mem_ccpCornerList_of_ne S q hq _).mpr ⟨m, hm, rfl⟩)
  · rintro h m' hm'
    obtain ⟨m, hm, rfl⟩ := (τ.mem_ccpCornerList_of_ne S q hq m').mp hm'
    exact h m hm

/-- **Uniformity is carried** when every corner mark keeps its turn and the new vertex turns like
the attachment vertex (the same-sign sector of thm:C-soft). -/
theorem carrierUniform_iff (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hturn : ∀ m, markTurn Q (τ.toMark m) = markTurn P m)
    (hnew : turn Q τ.new = turn P τ.att) :
    CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q := by
  rw [sfta_carrierUniform_iff_forall_mem hn hP hS q]
  by_cases hq : owner hn hP S (Sum.inl τ.att) = q
  · rw [τ.carrierUniform_iff_insertion S hS q hq]
    refine exists_congr fun σ => and_congr_right fun _ => ?_
    simp only [hturn]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rw [hnew, ← markTurn_inl]
      exact h _ ((mem_ccpCornerList hn hP S q _).mpr ⟨hq, isTrueCorner_vertex S _⟩)
  · rw [τ.carrierUniform_iff_of_ne S hS q hq]
    simp only [hturn]

theorem uniformDecomposition_transport {S : Finset (Crossing P)}
    (huni : ∀ q : Component hn hP S,
      CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q) :
    UniformDecomposition (by omega) hQ (τ.support S) ↔ UniformDecomposition hn hP S := by
  unfold UniformDecomposition
  rw [(τ.component S).surjective.forall]
  exact forall_congr' huni

theorem mem_uniformDecompositions_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q)
    (S : Finset (Crossing P)) :
    τ.support S ∈ uniformDecompositions (by omega) hQ ↔ S ∈ uniformDecompositions hn hP := by
  rw [mem_uniformDecompositions, mem_uniformDecompositions]
  have hd : τ.support S ∈ independentSupports (by omega) hQ ↔ S ∈ independentSupports hn hP :=
    τ.isDecomposition_transport S
  by_cases hS : IsDecomposition hn hP S
  · exact and_congr hd (τ.uniformDecomposition_transport (huni S hS))
  · constructor
    · rintro ⟨h, _⟩
      exact absurd (hd.mp h) hS
    · rintro ⟨h, _⟩
      exact absurd h hS

/-! ### The left-turn count -/

/-- `ℓ(Q) = ℓ(P) − [τ_att(P) = 1] + [τ_{vert att}(Q) = 1] + [τ_new(Q) = 1]` (additive form) when
every other vertex keeps its turn. -/
theorem leftTurns_transport (hturn : ∀ i, i ≠ τ.att → turn Q (τ.vert i) = turn P i) :
    leftTurns Q + (if turn P τ.att = 1 then 1 else 0) =
      leftTurns P + (if turn Q (τ.vert τ.att) = 1 then 1 else 0) +
        (if turn Q τ.new = 1 then 1 else 0) := by
  unfold leftTurns
  rw [Finset.card_filter, Finset.card_filter]
  have huniv : (Finset.univ : Finset (ZMod (n + 1))) = insert τ.new (Finset.univ.image τ.vert) := by
    ext a
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_image, true_and]
    rcases τ.vert_exhaust a with h | ⟨i, hi⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi⟩
  have hnot : τ.new ∉ Finset.univ.image τ.vert := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun i => τ.vert_ne_new i
  rw [huniv, Finset.sum_insert hnot, Finset.sum_image (fun i _ k _ h => τ.vert_injective h),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ τ.att),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ τ.att)]
  have hrest : ∑ x ∈ Finset.univ.erase τ.att, (if turn Q (τ.vert x) = 1 then 1 else 0) =
      ∑ x ∈ Finset.univ.erase τ.att, (if turn P x = 1 then 1 else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hturn x (Finset.ne_of_mem_erase hx)]
  rw [hrest]
  ring

/-! ### The corner coefficients and the state sum -/

theorem cornerSlot_transport {S : Finset (Crossing P)} (q : Component hn hP S)
    (hrot : carrierRotation (by omega) hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q) :
    cornerSlot (by omega) hQ (τ.support S) (τ.component S q) = cornerSlot hn hP S q := by
  unfold cornerSlot carrierRotationInt
  rw [τ.carrierCrossingCount_transport S q, hrot]

theorem cornerCoefficient_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hrot : carrierRotation (by omega) hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q)
    (hH : homfly (positiveLift (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS)) = homfly (positiveLift hn hP S q hS)) :
    cornerCoefficient (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt]
  unfold cornerHomfly
  rw [τ.cornerSlot_transport q hrot, hH]

theorem cornerProduct_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (hcoef : ∀ q : Component hn hP S,
      cornerCoefficient (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerProduct (by omega) hQ (τ.support S) ((τ.isDecomposition_transport S).mpr hS) =
      cornerProduct hn hP S hS := by
  unfold cornerProduct
  exact (Fintype.prod_equiv (τ.component S) _ _ fun q => (hcoef q).symm).symm

/-- **The signed sum over the uniform decompositions is carried** under a transport preserving
uniformity and the corner coefficients (the prefactor `(−1)^ℓ` is treated by `leftTurns_transport`). -/
theorem sum_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q)
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    (∑ S ∈ (uniformDecompositions (by omega) hQ).attach,
      (-1) ^ S.1.card *
        cornerProduct (by omega) hQ S.1 (isDecomposition_of_mem_uniformDecompositions _ hQ S.2)) =
    ∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2) := by
  set g : Finset (Crossing P) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions hn hP then
      (-1) ^ S.card * cornerProduct hn hP S (isDecomposition_of_mem_uniformDecompositions hn hP h)
    else 0 with hg
  set g' : Finset (Crossing Q) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions (by omega) hQ then
      (-1) ^ S.card * cornerProduct (by omega) hQ S (isDecomposition_of_mem_uniformDecompositions _ hQ h)
    else 0 with hg'
  have h1 : (∑ S ∈ (uniformDecompositions (by omega) hQ).attach,
      (-1) ^ S.1.card *
        cornerProduct (by omega) hQ S.1 (isDecomposition_of_mem_uniformDecompositions _ hQ S.2)) =
      ∑ S ∈ (uniformDecompositions (by omega) hQ).attach, g' S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg']
    rw [dite_eq_left S.2]
  have h2 : (∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2)) =
      ∑ S ∈ (uniformDecompositions hn hP).attach, g S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg]
    rw [dite_eq_left S.2]
  rw [h1, h2, Finset.sum_attach, Finset.sum_attach]
  symm
  refine Finset.sum_nbij τ.support ?_ ?_ ?_ ?_
  · intro S hS
    exact (τ.mem_uniformDecompositions_transport huni S).mpr hS
  · intro S _ T _ h
    exact τ.support_injective h
  · intro S' hS'
    obtain ⟨S, rfl⟩ := τ.support_surjective S'
    exact ⟨S, (τ.mem_uniformDecompositions_transport huni S).mp hS', rfl⟩
  · intro S hS
    have hS' : IsDecomposition hn hP S := isDecomposition_of_mem_uniformDecompositions hn hP hS
    have hSQ : τ.support S ∈ uniformDecompositions (by omega) hQ :=
      (τ.mem_uniformDecompositions_transport huni S).mpr hS
    simp only [hg, hg']
    rw [dite_eq_left hS, dite_eq_left hSQ, τ.support_card]
    congr 1
    exact (τ.cornerProduct_transport hS' (hcoef S hS')).symm

theorem sfta_sign_cancel (ℓ₁ ℓ₂ : ℕ) (x : ℤ) :
    (-1) ^ ℓ₁ * x = (-1) ^ (ℓ₁ + ℓ₂) * ((-1) ^ ℓ₂ * x) := by
  have h : ((-1 : ℤ) ^ ℓ₂) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  rw [pow_add]
  linear_combination (-((-1 : ℤ) ^ ℓ₁ * x)) * h

/-- The corner state sum is carried up to the sign `(−1)^{ℓ(Q) + ℓ(P)}`. -/
theorem cornerStateSum_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q)
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerStateSum (by omega) hQ = (-1) ^ (leftTurns Q + leftTurns P) * cornerStateSum hn hP := by
  unfold cornerStateSum
  rw [τ.sum_transport huni hcoef]
  exact sfta_sign_cancel _ _ _

end sfta_InsertMarkTransport


section SoftIndices


theorem sfta_softOldIndex_val_of_ne_zero (j i : ZMod n) (hj : j ≠ 0) :
    (softOldIndex j i).val = if i.val ≤ j.val then i.val else i.val + 1 := by
  by_cases hi : i = j
  · subst hi
    simp only [le_refl, ite_true]
    rw [softOldIndex_at_attachment, canonicalPosition_val_nonzero i hj]
    have hp := ZMod.val_pos.mpr hj
    have hlt := ZMod.val_lt i
    have h1 : i.val - 1 + 1 = i.val := by omega
    rw [h1]
    exact ZMod.val_natCast_of_lt (by omega)
  · rw [← softParentEdge_of_ne j i hi, softParentEdge_val]
    have hne : i.val ≠ j.val := fun h => hi (ZMod.val_injective n h)
    simp only [hj, false_or]
    split_ifs <;> omega

theorem sfta_softNewIndex_val_of_ne_zero (j : ZMod n) (hj : j ≠ 0) :
    (softNewIndex j).val = j.val + 1 := by
  rw [softNewIndex_physical, canonicalPosition_val_nonzero j hj]
  have hp := ZMod.val_pos.mpr hj
  have hlt := ZMod.val_lt j
  have h1 : j.val - 1 + 2 = j.val + 1 := by omega
  rw [h1]
  exact ZMod.val_natCast_of_lt (by omega)

theorem sfta_softOldIndex_zero_val (i : ZMod n) :
    (softOldIndex (0 : ZMod n) i).val = if i = 0 then n else i.val := by
  by_cases hi : i = 0
  · subst hi
    simp only [ite_true]
    rw [softOldIndex_at_attachment, canonicalPosition_val_zero]
    have := NeZero.pos n
    have h1 : n - 1 + 1 = n := by omega
    rw [h1]
    exact ZMod.val_natCast_of_lt (by omega)
  · rw [if_neg hi, ← softParentEdge_of_ne 0 i hi, softParentEdge_val]
    simp

theorem sfta_softNewIndex_zero : softNewIndex (0 : ZMod n) = 0 := by
  rw [softNewIndex_physical, canonicalPosition_val_zero]
  have := NeZero.pos n
  have h1 : n - 1 + 2 = n + 1 := by omega
  rw [h1, ZMod.natCast_self]

theorem sfta_softParentEdge_val_of_ne_zero (j e : ZMod n) (hj : j ≠ 0) :
    (softParentEdge j e).val = if e.val < j.val then e.val else e.val + 1 := by
  rw [softParentEdge_val]; simp [hj]

theorem sfta_softParentEdge_zero_val (e : ZMod n) : (softParentEdge (0 : ZMod n) e).val = e.val := by
  rw [softParentEdge_val]; simp

end SoftIndices

section SoftKeys

theorem sfta_nat_lt_add_iff (a b : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    (a : ℝ) < b + t ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast (not_le.mp hab)
    linarith
  · intro h
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

theorem sfta_add_lt_nat_iff (a b : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    (b : ℝ) + t < a ↔ b < a := by
  constructor
  · intro h
    by_contra hab
    have : (a : ℝ) ≤ b := by exact_mod_cast (not_lt.mp hab)
    linarith
  · intro h
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    linarith


theorem sfta_markKey_visit_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) (v : Visit P) :
    markKey hn hP (Sum.inr v) = (v.2.val.val : ℝ) + visitParameter v := rfl

theorem sfta_markKey_vertex_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) (i : ZMod n) :
    markKey hn hP (Sum.inl i) = (i.val : ℝ) := markKey_vertex hn hP i

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n} {q : Plane} {ε : ℝ}
  (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)

/-- The soft mark map on the source marks (vertices by `softOldIndex`, visits by
`softInheritedVisit`). -/
abbrev sfta_softMap : Mark P → Mark (softInsertion P j q ε) :=
  Sum.map (softOldIndex j) (softInheritedVisit hp)

include hn hP hQ in
/-- The traversal keys of transported marks compare as the parent keys, except that when `j = 0`
the attachment vertex `inl 0` (which moves to the label `n`) is excluded. -/
theorem sfta_soft_markKey_lt_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
    (a b : Mark P) (ha : a = Sum.inl j → j ≠ 0) (hb : b = Sum.inl j → j ≠ 0) :
    markKey (by omega) hQ.1 (sfta_softMap hp a) < markKey (by omega) hQ.1 (sfta_softMap hp b) ↔
      markKey hn hP.1 a < markKey hn hP.1 b := by
  cases a with
  | inl i =>
    cases b with
    | inl k =>
      simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, Nat.cast_lt]
      by_cases hj : j = 0
      · subst hj
        have hi : i ≠ 0 := fun h => ha (by rw [h]) rfl
        have hk : k ≠ 0 := fun h => hb (by rw [h]) rfl
        rw [sfta_softOldIndex_zero_val, sfta_softOldIndex_zero_val, if_neg hi, if_neg hk]
      · rw [sfta_softOldIndex_val_of_ne_zero j i hj, sfta_softOldIndex_val_of_ne_zero j k hj]
        split_ifs <;> omega
    | inr w =>
      simp only [sfta_softMap, Sum.map_inl, Sum.map_inr, sfta_markKey_vertex_eq,
        sfta_markKey_visit_eq, softInheritedVisit_edge]
      have hw := visitPosition_interior hn hP.1 w
      have hw' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp w)
      rw [sfta_nat_lt_add_iff _ _ hw'.1 hw'.2, sfta_nat_lt_add_iff _ _ hw.1 hw.2]
      by_cases hj : j = 0
      · subst hj
        have hi : i ≠ 0 := fun h => ha (by rw [h]) rfl
        rw [sfta_softOldIndex_zero_val, if_neg hi, sfta_softParentEdge_zero_val]
      · rw [sfta_softOldIndex_val_of_ne_zero j i hj, sfta_softParentEdge_val_of_ne_zero j _ hj]
        split_ifs <;> omega
  | inr v =>
    cases b with
    | inl k =>
      simp only [sfta_softMap, Sum.map_inl, Sum.map_inr, sfta_markKey_vertex_eq,
        sfta_markKey_visit_eq, softInheritedVisit_edge]
      have hv := visitPosition_interior hn hP.1 v
      have hv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
      rw [sfta_add_lt_nat_iff _ _ hv'.1 hv'.2, sfta_add_lt_nat_iff _ _ hv.1 hv.2]
      by_cases hj : j = 0
      · subst hj
        have hk : k ≠ 0 := fun h => hb (by rw [h]) rfl
        rw [sfta_softOldIndex_zero_val, if_neg hk, sfta_softParentEdge_zero_val]
      · rw [sfta_softOldIndex_val_of_ne_zero j k hj, sfta_softParentEdge_val_of_ne_zero j _ hj]
        split_ifs <;> omega
    | inr w =>
      simp only [sfta_softMap, Sum.map_inr, markKey_visit]
      rw [visitKey_lt_iff, visitKey_lt_iff]
      simp only [softInheritedVisit_edge, softParentEdge_val_lt_iff,
        (softParentEdge_injective j).eq_iff]
      exact or_congr Iff.rfl (and_congr_right (fun he => hord v w he))

include hn hP hQ in
theorem sfta_soft_markKey_le_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
    (a b : Mark P) (ha : a = Sum.inl j → j ≠ 0) (hb : b = Sum.inl j → j ≠ 0) :
    markKey (by omega) hQ.1 (sfta_softMap hp a) ≤ markKey (by omega) hQ.1 (sfta_softMap hp b) ↔
      markKey hn hP.1 a ≤ markKey hn hP.1 b := by
  simpa only [not_lt] using not_congr (sfta_soft_markKey_lt_iff hn hP hQ hp hord b a hb ha)

include hn hP hQ in
/-- `j ≠ 0`: the new vertex sits strictly above the attachment vertex and below every transported
mark that follows the attachment vertex. -/
theorem sfta_soft_new_key (hj : j ≠ 0) :
    markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) = (j.val : ℝ) + 1 ∧
    markKey (by omega) hQ.1 (sfta_softMap hp (Sum.inl j)) = (j.val : ℝ) := by
  simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, sfta_softNewIndex_val_of_ne_zero j hj,
    sfta_softOldIndex_val_of_ne_zero j j hj, le_refl, ite_true, Nat.cast_add, Nat.cast_one]
  exact ⟨trivial, trivial⟩

include hn hP hQ in
theorem sfta_soft_new_key_le (hj : j ≠ 0) (w : Mark P) (hw : w ≠ Sum.inl j)
    (hlt : markKey hn hP.1 (Sum.inl j) < markKey hn hP.1 w) :
    markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) ≤ markKey (by omega) hQ.1 (sfta_softMap hp w) := by
  rw [(sfta_soft_new_key hn hP hQ hp hj).1]
  cases w with
  | inl i =>
    simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, Nat.cast_lt] at hlt ⊢
    rw [sfta_softOldIndex_val_of_ne_zero j i hj, if_neg (by omega)]
    push_cast
    have : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hlt
    linarith
  | inr v =>
    simp only [sfta_softMap, Sum.map_inr, sfta_markKey_vertex_eq, sfta_markKey_visit_eq,
      softInheritedVisit_edge] at hlt ⊢
    have hv := visitPosition_interior hn hP.1 v
    have hv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
    have h1 : j.val ≤ v.2.val.val := by
      by_contra hc
      have : (v.2.val.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (not_le.mp hc)
      linarith
    rw [sfta_softParentEdge_val_of_ne_zero j _ hj, if_neg (by omega)]
    push_cast
    have : (j.val : ℝ) ≤ v.2.val.val := by exact_mod_cast h1
    linarith

include hn hP hQ in
/-- `j = 0`: the new vertex is the label `0`, the old vertex `0` is the label `n`, and every other
transported mark lies strictly between. -/
theorem sfta_soft_zero_keys (hj : j = 0) :
    markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) = 0 ∧
    markKey (by omega) hQ.1 (sfta_softMap hp (Sum.inl j)) = (n : ℝ) ∧
    ∀ w : Mark P, w ≠ Sum.inl j → markKey (by omega) hQ.1 (sfta_softMap hp w) ≤ (n : ℝ) := by
  subst hj
  refine ⟨?_, ?_, ?_⟩
  · rw [sfta_softNewIndex_zero, sfta_markKey_vertex_eq, ZMod.val_zero, Nat.cast_zero]
  · simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, sfta_softOldIndex_zero_val, ite_true]
  · intro w hw
    cases w with
    | inl i =>
      have hi : i ≠ 0 := fun h => hw (by rw [h])
      simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, sfta_softOldIndex_zero_val,
        if_neg hi]
      exact_mod_cast (ZMod.val_lt i).le
    | inr v =>
      simp only [sfta_softMap, Sum.map_inr, sfta_markKey_visit_eq, softInheritedVisit_edge,
        sfta_softParentEdge_zero_val]
      have hv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
      have : (v.2.val.val : ℝ) + 1 ≤ n := by exact_mod_cast ZMod.val_lt v.2.val
      linarith

end SoftKeys

section SoftMarkList

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n}
  {q : Plane} {ε : ℝ} (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)

theorem sfta_softMap_injective : Function.Injective (sfta_softMap hp) :=
  Sum.map_injective.mpr ⟨softOldIndex_injective j, softInheritedVisit_injective hp⟩

theorem sfta_softMap_ne_new (m : Mark P) : sfta_softMap hp m ≠ Sum.inl (softNewIndex j) := by
  cases m with
  | inl i => exact fun h => softOldIndex_ne_new j i (Sum.inl_injective h)
  | inr v => exact Sum.inr_ne_inl

theorem sfta_softMap_exhaust (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
    (m : Mark (softInsertion P j q ε)) :
    m = Sum.inl (softNewIndex j) ∨ ∃ a : Mark P, sfta_softMap hp a = m := by
  cases m with
  | inl a =>
    rcases soft_indices_exhaust j a with h | ⟨k, hk⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨Sum.inl k, by rw [hk]; rfl⟩
  | inr w =>
    obtain ⟨v, hv⟩ := softInheritedVisit_surjective_nonloop hp hclass hnot w
    exact Or.inr ⟨Sum.inr v, by rw [← hv]; rfl⟩

include hn hP in
theorem sfta_softMap_new_notMem :
    Sum.inl (softNewIndex j) ∉ (markList hn hP).map (sfta_softMap hp) := by
  intro h
  obtain ⟨m, _, hm⟩ := List.mem_map.mp h
  exact sfta_softMap_ne_new hp m hm

/-- The head of the sorted mark list is the vertex `0` (the cut of def:gauss). -/
theorem sfta_markList_head : markList hn hP = Sum.inl 0 :: (markList hn hP).tail := by
  obtain ⟨m, hm⟩ := markList_nonempty hn hP
  obtain ⟨h, T, hT⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hm)
  rw [hT, List.tail_cons]
  congr 1
  by_contra hh
  have h0 : Sum.inl (0 : ZMod n) ∈ T := by
    have := mem_markList hn hP (Sum.inl 0)
    rw [hT, List.mem_cons] at this
    exact this.resolve_left (fun h' => hh h'.symm)
  have hs := markList_sorted hn hP
  rw [hT, List.pairwise_cons] at hs
  have h1 := hs.1 _ h0
  have h2 : 0 ≤ markKey hn hP.1 h := traversalKey_nonneg _
  have h3 : markKey hn hP.1 h = markKey hn hP.1 (Sum.inl 0) := by
    rw [sfta_markKey_vertex_eq, ZMod.val_zero, Nat.cast_zero] at h1 ⊢
    linarith
  exact hh (markKey_injective hn hP h3)

include hn hP hQ in
/-- **The sorted mark list of the soft insertion** is the parent list mapped by the soft mark map
with the new vertex `M_ε` inserted immediately after the attachment vertex `μ_j`, up to rotation
(literally when `j ≠ 0`; when `j = 0` the new vertex is the label `0`, the cut moves by one). -/
theorem sfta_soft_markList_insertion (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w)) :
    sfta_IsInsertion (sfta_softMap hp) (Sum.inl j) (Sum.inl (softNewIndex j))
      (markList hn hP) (markList (by omega) hQ) := by
  have hinj := sfta_softMap_injective hp
  have hnew := sfta_softMap_new_notMem hn hP hp
  have hndP := markList_nodup hn hP
  have hndQ := markList_nodup (by omega : 3 ≤ n + 1) hQ
  have hsP := markList_sorted hn hP
  have hsQ := markList_sorted (by omega : 3 ≤ n + 1) hQ
  have hkey := sfta_soft_markKey_le_iff hn hP hQ hp hord
  -- a candidate list which is a permutation of `M_ε :: (parent list).map f` is a permutation of the
  -- sorted mark list of the child
  have hperm : ∀ R : List (Mark (softInsertion P j q ε)),
      R.Perm (Sum.inl (softNewIndex j) :: (markList hn hP).map (sfta_softMap hp)) →
        (markList (by omega) hQ).Perm R := by
    intro R hR
    have hRnd : R.Nodup := hR.nodup_iff.mpr (List.nodup_cons.mpr ⟨hnew, hndP.map hinj⟩)
    apply (List.perm_ext_iff_of_nodup hndQ hRnd).mpr
    intro m
    refine ⟨fun _ => ?_, fun _ => mem_markList _ hQ m⟩
    rw [hR.mem_iff, List.mem_cons, List.mem_map]
    rcases sfta_softMap_exhaust hp hclass hnot m with h | ⟨a, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, mem_markList hn hP a, ha⟩
  by_cases hj : j = 0
  · subst hj
    obtain ⟨hk0, hkn, hkle⟩ := sfta_soft_zero_keys hn hP hQ hp rfl
    have hhead := sfta_markList_head hn hP
    set T := (markList hn hP).tail with hTdef
    have hT : Sum.inl (0 : ZMod n) ∉ T := by
      have := hndP
      rw [hhead, List.nodup_cons] at this
      exact this.1
    have hsT : T.Pairwise (fun a b => markKey hn hP.1 a ≤ markKey hn hP.1 b) := by
      have := hsP
      rw [hhead, List.pairwise_cons] at this
      exact this.2
    have heq : markList (by omega) hQ =
        Sum.inl (softNewIndex (0 : ZMod n)) ::
          (T.map (sfta_softMap hp) ++ [sfta_softMap hp (Sum.inl 0)]) := by
      apply List.Perm.eq_of_pairwise (le := fun a b => markKey (by omega) hQ.1 a ≤ markKey (by omega) hQ.1 b)
        (fun a b _ _ hab hba => markKey_injective _ hQ (le_antisymm hab hba)) hsQ
      · rw [List.pairwise_cons]
        refine ⟨fun w _ => ?_, ?_⟩
        · rw [hk0]; exact traversalKey_nonneg _
        · rw [List.pairwise_append]
          refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
          · rw [List.pairwise_map]
            refine hsT.imp_of_mem (fun {a b} ha hb hab => ?_)
            exact (hkey a b (fun h => absurd (h ▸ ha) hT) (fun h => absurd (h ▸ hb) hT)).mpr hab
          · intro u hu w hw
            rw [List.mem_singleton] at hw
            obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.mp hu
            rw [hw, hkn]
            exact hkle u₀ (fun h => hT (h ▸ hu₀))
      · apply hperm
        rw [hhead, List.map_cons]
        exact List.Perm.cons _ (List.perm_append_singleton _ _)
    refine ⟨[], T, by rw [List.nil_append]; exact hhead, ?_⟩
    rw [heq, List.map_nil, List.nil_append, ← List.cons_append]
    exact List.isRotated_concat _ _
  · obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem (mem_markList hn hP (Sum.inl j))
    obtain ⟨hknew, hkatt⟩ := sfta_soft_new_key hn hP hQ hp hj
    have hsP' : (L₁ ++ Sum.inl j :: L₂).Pairwise (fun a b => markKey hn hP.1 a ≤ markKey hn hP.1 b) := by
      rw [← hL]; exact hsP
    have hndP' : (L₁ ++ Sum.inl j :: L₂).Nodup := by rw [← hL]; exact hndP
    obtain ⟨hL₁, hcons, hcross⟩ := List.pairwise_append.mp hsP'
    obtain ⟨hjL₂, hL₂⟩ := List.pairwise_cons.mp hcons
    have hjnot₂ : Sum.inl j ∉ L₂ := by
      have := (List.nodup_append.mp hndP').2.1
      exact (List.nodup_cons.mp this).1
    have hkey' : ∀ a b : Mark P, markKey (by omega) hQ.1 (sfta_softMap hp a) ≤
        markKey (by omega) hQ.1 (sfta_softMap hp b) ↔ markKey hn hP.1 a ≤ markKey hn hP.1 b :=
      fun a b => hkey a b (fun _ => hj) (fun _ => hj)
    have heq : markList (by omega) hQ =
        L₁.map (sfta_softMap hp) ++ sfta_softMap hp (Sum.inl j) ::
          Sum.inl (softNewIndex j) :: L₂.map (sfta_softMap hp) := by
      apply List.Perm.eq_of_pairwise (le := fun a b => markKey (by omega) hQ.1 a ≤ markKey (by omega) hQ.1 b)
        (fun a b _ _ hab hba => markKey_injective _ hQ (le_antisymm hab hba)) hsQ
      · rw [List.pairwise_append]
        refine ⟨?_, ?_, ?_⟩
        · rw [List.pairwise_map]
          exact hL₁.imp (fun {a b} hab => (hkey' a b).mpr hab)
        · rw [List.pairwise_cons, List.pairwise_cons]
          refine ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩
          · rw [List.mem_cons] at hw
            rcases hw with rfl | hw
            · rw [hknew, hkatt]; linarith
            · obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
              exact (hkey' _ _).mpr (hjL₂ w₀ hw₀)
          · obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
            have hne : w₀ ≠ Sum.inl j := fun h => hjnot₂ (h ▸ hw₀)
            exact sfta_soft_new_key_le hn hP hQ hp hj w₀ hne
              (lt_of_le_of_ne (hjL₂ w₀ hw₀) (fun h => hne (markKey_injective hn hP h).symm))
          · rw [List.pairwise_map]
            exact hL₂.imp (fun {a b} hab => (hkey' a b).mpr hab)
        · intro u hu w hw
          obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.mp hu
          rw [List.mem_cons, List.mem_cons] at hw
          rcases hw with rfl | rfl | hw
          · exact (hkey' _ _).mpr (hcross u₀ hu₀ _ (List.mem_cons_self))
          · have h1 := (hkey' _ _).mpr (hcross u₀ hu₀ _ (List.mem_cons_self))
            rw [hkatt] at h1
            rw [hknew]
            linarith
          · obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
            exact (hkey' _ _).mpr (hcross u₀ hu₀ w₀ (List.mem_cons_of_mem _ hw₀))
      · apply hperm
        rw [hL]
        exact sfta_insert_perm L₁ L₂ _ _ _
    exact ⟨L₁, L₂, hL, by rw [heq]⟩

end SoftMarkList


section InterlacesTransport

/-- Interlacement (def:interlace) in terms of visits: alternating visits of `x` and `y`. -/
theorem sfta_interlaces_iff_visits {n : ℕ} (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (x y : Crossing P) :
    Interlaces hn hP x y ↔ x ≠ y ∧ ∃ u₀ u₁ v₀ v₁ : Visit P,
      u₀.1 = x ∧ u₁.1 = x ∧ v₀.1 = y ∧ v₁.1 = y ∧ u₀ ≠ u₁ ∧ v₀ ≠ v₁ ∧
      traversalBetween (visitPosition hn hP.1 u₀) (visitPosition hn hP.1 v₀) (visitPosition hn hP.1 u₁) ∧
      traversalBetween (visitPosition hn hP.1 u₁) (visitPosition hn hP.1 v₁) (visitPosition hn hP.1 u₀) := by
  constructor
  · rintro ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀, h₁⟩
    refine ⟨hxy, ⟨x, x₀⟩, ⟨x, x₁⟩, ⟨y, y₀⟩, ⟨y, y₁⟩, rfl, rfl, rfl, rfl, ?_, ?_, h₀, h₁⟩
    · intro h; exact hx (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    · intro h; exact hy (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · rintro ⟨hxy, ⟨c₀, x₀⟩, ⟨c₁, x₁⟩, ⟨d₀, y₀⟩, ⟨d₁, y₁⟩, h₀, h₁, h₂, h₃, hu, hv, hb₀, hb₁⟩
    dsimp only at h₀ h₁ h₂ h₃
    subst h₀; subst h₁; subst h₂; subst h₃
    refine ⟨hxy, x₀, x₁, y₀, y₁, ?_, ?_, hb₀, hb₁⟩
    · intro h; exact hu (by rw [h])
    · intro h; exact hv (by rw [h])

/-- Interlacement is carried by compatible crossing/visit bijections preserving the cyclic order
of the visit positions. -/
theorem sfta_interlaces_transport {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m) {P : LabelledTuple n}
    {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q) (cross : Crossing P ≃ Crossing Q)
    (visit : Visit P ≃ Visit Q) (hfst : ∀ v, (visit v).1 = cross v.1)
    (hbtw : ∀ u v w : Visit P,
      traversalBetween (visitPosition hm hQ.1 (visit u)) (visitPosition hm hQ.1 (visit v))
        (visitPosition hm hQ.1 (visit w)) ↔
      traversalBetween (visitPosition hn hP.1 u) (visitPosition hn hP.1 v) (visitPosition hn hP.1 w))
    (x y : Crossing P) :
    Interlaces hm hQ (cross x) (cross y) ↔ Interlaces hn hP x y := by
  rw [sfta_interlaces_iff_visits hm hQ, sfta_interlaces_iff_visits hn hP]
  refine and_congr cross.injective.ne_iff ?_
  constructor
  · rintro ⟨u₀, u₁, v₀, v₁, h₀, h₁, h₂, h₃, hu, hv, hb₀, hb₁⟩
    obtain ⟨u₀, rfl⟩ := visit.surjective u₀
    obtain ⟨u₁, rfl⟩ := visit.surjective u₁
    obtain ⟨v₀, rfl⟩ := visit.surjective v₀
    obtain ⟨v₁, rfl⟩ := visit.surjective v₁
    rw [hfst] at h₀ h₁ h₂ h₃
    refine ⟨u₀, u₁, v₀, v₁, cross.injective h₀, cross.injective h₁, cross.injective h₂,
      cross.injective h₃, fun h => hu (by rw [h]), fun h => hv (by rw [h]),
      (hbtw _ _ _).mp hb₀, (hbtw _ _ _).mp hb₁⟩
  · rintro ⟨u₀, u₁, v₀, v₁, h₀, h₁, h₂, h₃, hu, hv, hb₀, hb₁⟩
    refine ⟨visit u₀, visit u₁, visit v₀, visit v₁, ?_, ?_, ?_, ?_, visit.injective.ne hu,
      visit.injective.ne hv, (hbtw _ _ _).mpr hb₀, (hbtw _ _ _).mpr hb₁⟩
    · rw [hfst, h₀]
    · rw [hfst, h₁]
    · rw [hfst, h₂]
    · rw [hfst, h₃]

end InterlacesTransport

section SoftInstance

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n}
  {q : Plane} {ε : ℝ} (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)

include hn hP hQ in
theorem sfta_soft_visitKey_lt_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w)) (v w : Visit P) :
    visitKey (by omega) hQ.1 (softInheritedVisit hp v) < visitKey (by omega) hQ.1 (softInheritedVisit hp w) ↔
      visitKey hn hP.1 v < visitKey hn hP.1 w := by
  rw [visitKey_lt_iff, visitKey_lt_iff]
  simp only [softInheritedVisit_edge, softParentEdge_val_lt_iff, (softParentEdge_injective j).eq_iff]
  exact or_congr Iff.rfl (and_congr_right (hord v w))

include hn hP hQ in
theorem sfta_soft_traversalBetween_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w)) (u v w : Visit P) :
    traversalBetween (visitPosition (by omega) hQ.1 (softInheritedVisit hp u))
      (visitPosition (by omega) hQ.1 (softInheritedVisit hp v))
      (visitPosition (by omega) hQ.1 (softInheritedVisit hp w)) ↔
    traversalBetween (visitPosition hn hP.1 u) (visitPosition hn hP.1 v) (visitPosition hn hP.1 w) := by
  have k := sfta_soft_visitKey_lt_iff hn hP hQ hp hord
  exact or_congr (and_congr (k u v) (k v w))
    (or_congr (and_congr (k v w) (k w u)) (and_congr (k w u) (k u v)))

include hn hP hQ in
theorem sfta_soft_interlaces_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
    (x y : Crossing P) :
    Interlaces (by omega) hQ (softInheritedCrossing hp x) (softInheritedCrossing hp y) ↔
      Interlaces hn hP x y :=
  sfta_interlaces_transport hn (by omega) hP hQ (softCrossingEquivNonloop hp hclass hnot)
    (softVisitEquivNonloop hp hclass hnot) (fun _ => rfl)
    (sfta_soft_traversalBetween_iff hn hP hQ hp hord) x y

/-- **The soft mark transport** `P → P_ε` in the non-loop sectors: vertices by `softOldIndex j`, the
new vertex `softNewIndex j`, attachment `j`, crossings and visits by the accepted inherited maps. -/
def sfta_softTransport (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w)) :
    sfta_InsertMarkTransport hn hP hQ where
  vert := softOldIndex j
  new := softNewIndex j
  att := j
  cross := softCrossingEquivNonloop hp hclass hnot
  visit := softVisitEquivNonloop hp hclass hnot
  visit_fst := fun _ => rfl
  markList_insertion := sfta_soft_markList_insertion hn hP hQ hp hclass hnot hord
  interlaces_iff := fun x y => sfta_soft_interlaces_iff hn hP hQ hp hord hclass hnot x y

variable (hclass : SoftCrossingClassificationAt P j q ε)
  (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
  (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))

@[simp] theorem sfta_softTransport_vert :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).vert = softOldIndex j := rfl

@[simp] theorem sfta_softTransport_new :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).new = softNewIndex j := rfl

@[simp] theorem sfta_softTransport_att :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).att = j := rfl

@[simp] theorem sfta_softTransport_cross (x : Crossing P) :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).cross x = softInheritedCrossing hp x := rfl

@[simp] theorem sfta_softTransport_visit (v : Visit P) :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).visit v = softInheritedVisit hp v := rfl

theorem sfta_softTransport_toMark_inl (i : ZMod n) :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).toMark (Sum.inl i) =
      Sum.inl (softOldIndex j i) := rfl

theorem sfta_softTransport_toMark_inr (v : Visit P) :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).toMark (Sum.inr v) =
      Sum.inr (softInheritedVisit hp v) := rfl

/-- The smoothing corners keep their turns when the crossing signs are inherited
(lem:soft-generic (iii)). -/
theorem sfta_softTransport_markTurn_inr
    (hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge P k) (edge P l))) (v : Visit P) :
    markTurn (softInsertion P j q ε) ((sfta_softTransport hn hP hQ hp hclass hnot hord).toMark (Sum.inr v)) =
      markTurn P (Sum.inr v) := by
  rw [sfta_softTransport_toMark_inr, markTurn_inr, markTurn_inr]
  have ht := (sfta_softTransport hn hP hQ hp hclass hnot hord).twin_eq v
  rw [sfta_softTransport_visit, sfta_softTransport_visit] at ht
  rw [← ht]
  simp only [softInheritedVisit_edge]
  unfold crossingSign
  apply hsign
  rw [← visit_crossing_val_eq_pair v]
  exact v.1.property

/-- All mark turns are carried when the vertex turns are (the same-sign sector supplies
`turn P_ε (softOldIndex j j) = −χ₋ = τ_j(P)`). -/
theorem sfta_softTransport_markTurn
    (hvert : ∀ k : ZMod n, turn (softInsertion P j q ε) (softOldIndex j k) = turn P k)
    (hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge P k) (edge P l))) (m : Mark P) :
    markTurn (softInsertion P j q ε) ((sfta_softTransport hn hP hQ hp hclass hnot hord).toMark m) =
      markTurn P m := by
  cases m with
  | inl i => rw [sfta_softTransport_toMark_inl, markTurn_inl, markTurn_inl]; exact hvert i
  | inr v => exact sfta_softTransport_markTurn_inr hn hP hQ hp hclass hnot hord hsign v

end SoftInstance

section SoftData


/-- **The soft data on one interval** (from lem:soft-generic, `soft_family_generic`): for every
small `ε > 0` and every genericity proof of `P_ε`, the crossing persistence and classification, the
same-edge visit order, the vertex turns (`k ≠ j` kept; `−χ₋` at `μ_j`, `−χ₊` at `M_ε`), and the
inherited crossing signs — exactly the hypotheses of `sfta_softTransport` and
`sfta_softTransport_markTurn`. -/
theorem sfta_soft_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ _hQ : Generic (softInsertion P j q ε),
      ∃ (hp : SoftCrossingPersistence P j q ε) (_hclass : SoftCrossingClassificationAt P j q ε),
        (∀ v w : Visit P, v.2.val = w.2.val →
          (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
            visitParameter v < visitParameter w)) ∧
        (∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k) ∧
        turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
        turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q ∧
        (∀ k l : ZMod n, IsCrossing P {k, l} →
          SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l))) := by
  obtain ⟨δ, hδ, _B, hall⟩ := (soft_family_generic hn hP j q hq).2.2.2.2.2
  refine ⟨δ, hδ, fun ε hε hεδ _hQ => ?_⟩
  obtain ⟨_, hp, hclass, _, hii, hiii, hord, _, _⟩ := hall ε hε hεδ
  exact ⟨hp, hclass, hord, hii.2.2.2.1, hii.2.2.2.2.1, hii.2.2.2.2.2.1,
    fun k l hc => (hiii k l hc).2.2.2.1⟩

end SoftData


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
