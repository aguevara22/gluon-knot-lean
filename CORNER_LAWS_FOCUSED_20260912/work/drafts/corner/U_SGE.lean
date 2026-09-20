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

/-! #### U103-E helpers (prefix `sge_`).  The corner turn of a carrier is a function of its corner
MARK alone (`turn_ccpCornerPolygon_eq_markTurn`, CX1); here the same is done for the REAL principal
turn: `principalTurn (ccpCornerPolygon …) j = sge_markPrincipalTurn S (ccpCornerMark … j)`, because both
corner edges are positive multiples of the original directions `edge P (ccpInEdge m)`,
`edge P (ccpOutSlot S m).1` (lem:carriers (ii), `ccpCornerPolygon_edge/_edge_pred`) and `principalAngle`
is invariant under positive scaling.  Then `2π r_Q` is a sum over the corner-mark finset, inherited
marks keep their value under `S → insert c S` (the out-slot of a true corner of `S` is unchanged), and
the two new smoothing corners cancel (`principalAngle` is antisymmetric on a transverse pair). -/

/-- `cornerRotor` is homogeneous under positive scaling of both arguments. -/
theorem sge_cornerRotor_smul (a b : ℝ) (u v : Plane) :
    cornerRotor (a • u) (b • v) = ((a * b : ℝ) : ℂ) * cornerRotor u v := by
  apply Complex.ext
  · rw [cornerRotor_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, cornerRotor_re,
      cornerRotor_im]
    simp only [planeDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · rw [cornerRotor_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, cornerRotor_re,
      cornerRotor_im]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- The principal angle does not see positive rescaling of either vector. -/
theorem sge_principalAngle_smul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u v : Plane) :
    principalAngle (a • u) (b • v) = principalAngle u v := by
  unfold principalAngle
  rw [sge_cornerRotor_smul, Complex.arg_real_mul _ (mul_pos ha hb)]

/-- Swapping the arguments conjugates the rotor. -/
theorem sge_cornerRotor_swap (u v : Plane) : cornerRotor v u = star (cornerRotor u v) := by
  unfold cornerRotor
  rw [star_mul, star_star]

/-- Antisymmetry of the principal angle on a transverse pair (`det ≠ 0`, so the rotor is off the
negative real axis and `arg (conj z) = − arg z`). -/
theorem sge_principalAngle_swap {u v : Plane} (h : det u v ≠ 0) :
    principalAngle v u = - principalAngle u v := by
  unfold principalAngle
  have hne : (cornerRotor u v).arg ≠ Real.pi := by
    intro hpi
    have him := (Complex.arg_eq_pi_iff.mp hpi).2
    rw [cornerRotor_im] at him
    exact h him
  rw [sge_cornerRotor_swap, Complex.star_def, Complex.arg_conj, ite_eq_right hne]

/-- The real principal turn of a true corner, read off its mark and the support: the principal
angle from the original incoming direction to the original outgoing direction (the real extension
of CX1's `markTurn`). -/
noncomputable def sge_markPrincipalTurn (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (m : Mark P) : ℝ :=
  principalAngle (edge P (ccpInEdge hn hP m)) (edge P (ccpOutSlot hn hP S m).1)

/-- The principal turn of the corner polygon at its `j`-th corner is the mark principal turn of
that corner (lem:carriers (ii): both corner edges are positive multiples of the original
directions). -/
theorem sge_principalTurn_eq_mark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    principalTurn (ccpCornerPolygon hn hP S q) j =
      sge_markPrincipalTurn hn hP S (ccpCornerMark hn hP S q j) := by
  obtain ⟨c₁, hc₁, he₁⟩ := ccpCornerPolygon_edge_pred hn hP hS q j
  obtain ⟨c₂, hc₂, he₂⟩ := ccpCornerPolygon_edge hn hP hS q j
  unfold principalTurn sge_markPrincipalTurn
  rw [he₁, he₂, sge_principalAngle_smul hc₁ hc₂]

/-- The corner marks of the carrier `q` at `S` as a finset: the true corners of `S` owned by `q`. -/
noncomputable def sge_cornerSet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Finset (Mark P) :=
  Finset.univ.filter fun m => owner hn hP S m = q ∧ IsTrueCorner S m

theorem sge_mem_cornerSet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (m : Mark P) :
    m ∈ sge_cornerSet hn hP S q ↔ owner hn hP S m = q ∧ IsTrueCorner S m := by
  simp only [sge_cornerSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `ccpCornerMark` enumerates the corner set exactly once. -/
theorem sge_image_cornerMark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    Finset.univ.image (ccpCornerMark hn hP S q) = sge_cornerSet hn hP S q := by
  ext m
  rw [Finset.mem_image, sge_mem_cornerSet]
  constructor
  · rintro ⟨j, -, rfl⟩
    exact ccpCornerMark_mem hn hP S q j
  · rintro ⟨h1, h2⟩
    obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S q m h1 h2
    exact ⟨j, Finset.mem_univ _, hj⟩

/-- A sum over the corners of `q` is a sum over its corner-mark finset. -/
theorem sge_sum_corners (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (f : Mark P → ℝ) :
    ∑ j, f (ccpCornerMark hn hP S q j) = ∑ m ∈ sge_cornerSet hn hP S q, f m := by
  rw [← sge_image_cornerMark, Finset.sum_image]
  intro i _ j _ hij
  exact ccpCornerMark_injective hn hP S q hij

/-- **Rotation as a mark sum**: `2π r_Q = Σ_{m corner mark of Q} markPrincipalTurn S m`. -/
theorem sge_rotation_eq_sum (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    carrierRotation hn hP S q * (2 * Real.pi) =
      ∑ m ∈ sge_cornerSet hn hP S q, sge_markPrincipalTurn hn hP S m := by
  unfold carrierRotation rotationNumber
  rw [div_mul_cancel₀ _ (by positivity), ← sge_sum_corners]
  exact Finset.sum_congr rfl fun j _ => sge_principalTurn_eq_mark hn hP hS q j

/-- **Inherited corners keep their principal turn** under the refinement `S → insert c S`: the
incoming edge is support-free and the outgoing slot of a true corner of `S` is unchanged. -/
theorem sge_markPrincipalTurn_insert (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (c : Crossing P) (m : Mark P) (hm : IsTrueCorner S m) :
    sge_markPrincipalTurn hn hP (insert c S) m = sge_markPrincipalTurn hn hP S m := by
  unfold sge_markPrincipalTurn
  cases m with
  | inl i => rw [ccpOutSlot_vertex, ccpOutSlot_vertex]
  | inr v =>
    have hv : v.1 ∈ S := hm
    rw [ccpOutSlot_selected hn hP S v hv,
      ccpOutSlot_selected hn hP (insert c S) v (Finset.mem_insert_of_mem hv)]

/-- **The two smoothing corners of a selected crossing cancel** in the real turn ledger: their
principal angles are `∠(d_i, d_j)` and `∠(d_j, d_i)` on a transverse pair. -/
theorem sge_new_turns_cancel (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    sge_markPrincipalTurn hn hP S (Sum.inr v) +
      sge_markPrincipalTurn hn hP S (Sum.inr (visitTwin v)) = 0 := by
  have hdet := ccp_corner_directions_det_ne_zero hn hP S (Sum.inr v) hv
  rw [ccpInEdge_visit, ccpOutSlot_selected hn hP S v hv] at hdet
  have hv' : (visitTwin v).1 ∈ S := by
    rw [visitTwin_crossing]
    exact hv
  unfold sge_markPrincipalTurn
  rw [ccpInEdge_visit, ccpOutSlot_selected hn hP S v hv, ccpInEdge_visit,
    ccpOutSlot_selected hn hP S (visitTwin v) hv', visitTwin_involutive,
    sge_principalAngle_swap hdet]
  ring

/-- The true corners of `insert c S` are those of `S` and the two visits of `c`. -/
theorem sge_isTrueCorner_insert {P : LabelledTuple n} (S : Finset (Crossing P)) (c : Crossing P)
    (v₀ : Visit P) (hv₀ : v₀.1 = c) (m : Mark P) :
    IsTrueCorner (insert c S) m ↔
      IsTrueCorner S m ∨ m = Sum.inr v₀ ∨ m = Sum.inr (visitTwin v₀) := by
  cases m with
  | inl i => exact ⟨fun _ => Or.inl trivial, fun _ => trivial⟩
  | inr w =>
    rw [isTrueCorner_visit, isTrueCorner_visit, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · right
        rcases visit_eq_or_twin v₀ w (h.trans hv₀.symm) with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | h | h)
      · exact Or.inr h
      · left
        rw [Sum.inr.inj h]
        exact hv₀
      · left
        rw [Sum.inr.inj h, visitTwin_crossing]
        exact hv₀

/-- The corner sets of two distinct carriers are disjoint. -/
theorem sge_cornerSet_disjoint (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) {q r : Component hn hP S} (hqr : q ≠ r) :
    Disjoint (sge_cornerSet hn hP S q) (sge_cornerSet hn hP S r) := by
  rw [Finset.disjoint_left]
  intro m hq hr
  rw [sge_mem_cornerSet] at hq hr
  exact hqr (hq.1.symm.trans hr.1)

/-- **The corner ledger of the split**: the corner marks of the two daughters at `insert c S` are
the corner marks of `A` at `S` together with the two visits of `c`. -/
theorem sge_cornerSet_union (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (A : Component hn hP S) {c : Crossing P}
    (hown0 : ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = A)
    (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂)
    (v₀ : Visit P) (hv₀ : v₀.1 = c) :
    sge_cornerSet hn hP (insert c S) Λ₁ ∪ sge_cornerSet hn hP (insert c S) Λ₂ =
      sge_cornerSet hn hP S A ∪ {Sum.inr v₀, Sum.inr (visitTwin v₀)} := by
  ext m
  rw [Finset.mem_union, Finset.mem_union, sge_mem_cornerSet, sge_mem_cornerSet, sge_mem_cornerSet,
    Finset.mem_insert, Finset.mem_singleton, sge_isTrueCorner_insert S c v₀ hv₀ m, ← or_and_right,
    ← hown m]
  have hA₀ : owner hn hP S (Sum.inr v₀) = A := hown0 v₀ hv₀
  have hA₁ : owner hn hP S (Sum.inr (visitTwin v₀)) = A :=
    hown0 (visitTwin v₀) ((visitTwin_crossing v₀).trans hv₀)
  constructor
  · rintro ⟨hm, hT | hm₀ | hm₁⟩
    · exact Or.inl ⟨hm, hT⟩
    · exact Or.inr (Or.inl hm₀)
    · exact Or.inr (Or.inr hm₁)
  · rintro (⟨hm, hT⟩ | rfl | rfl)
    · exact ⟨hm, Or.inl hT⟩
    · exact ⟨hA₀, Or.inr (Or.inl rfl)⟩
    · exact ⟨hA₁, Or.inr (Or.inr rfl)⟩

/-- The two visits of the unselected `c` are not corners of `S`. -/
theorem sge_cornerSet_disjoint_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (A : Component hn hP S) {c : Crossing P} (hcS : c ∉ S)
    (v₀ : Visit P) (hv₀ : v₀.1 = c) :
    Disjoint (sge_cornerSet hn hP S A) {Sum.inr v₀, Sum.inr (visitTwin v₀)} := by
  rw [Finset.disjoint_left]
  intro m hm hm'
  rw [sge_mem_cornerSet] at hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm'
  rcases hm' with rfl | rfl
  · exact hcS (hv₀ ▸ hm.2)
  · exact hcS (((visitTwin_crossing v₀).trans hv₀) ▸ hm.2)

/-- **eq. cb:singleton-rotations, real form**: `r_A = r_{Λ₁} + r_{Λ₂}` (the two new principal angles
cancel, every inherited corner keeps its principal turn). -/
theorem sge_rotation_add (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hS' : IsDecomposition hn hP (insert c S)) (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hne : Λ₁ ≠ Λ₂)
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    carrierRotation hn hP S A =
      carrierRotation hn hP (insert c S) Λ₁ + carrierRotation hn hP (insert c S) Λ₂ := by
  have hcS : c ∉ S := ((mem_carrierCrossings hn hP S A c).mp hc).1
  have hown0 : ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = A :=
    ((mem_carrierCrossings hn hP S A c).mp hc).2
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  let v₀ : Visit P := ⟨c, i⟩
  have hv₀ : v₀.1 = c := rfl
  have hv₀' : v₀.1 ∈ insert c S := by
    rw [hv₀]
    exact Finset.mem_insert_self c S
  have hvne : (Sum.inr v₀ : Mark P) ≠ Sum.inr (visitTwin v₀) := by
    intro h
    exact visitTwin_ne v₀ (Sum.inr.inj h).symm
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  apply mul_right_cancel₀ h2π
  rw [add_mul, sge_rotation_eq_sum hn hP hS A, sge_rotation_eq_sum hn hP hS' Λ₁,
    sge_rotation_eq_sum hn hP hS' Λ₂,
    ← Finset.sum_union (sge_cornerSet_disjoint hn hP (insert c S) hne),
    sge_cornerSet_union hn hP S A hown0 Λ₁ Λ₂ hown v₀ hv₀,
    Finset.sum_union (sge_cornerSet_disjoint_visits hn hP S A hcS v₀ hv₀),
    Finset.sum_pair hvne, sge_new_turns_cancel hn hP (insert c S) v₀ hv₀', add_zero]
  exact Finset.sum_congr rfl fun m hm =>
    (sge_markPrincipalTurn_insert hn hP S c m ((sge_mem_cornerSet hn hP S A m).mp hm).2).symm

/-- Two nonzero signs agree or are opposite. -/
theorem sge_signType_eq_or_neg {σ τ : SignType} (hσ : σ ≠ 0) (hτ : τ ≠ 0) : σ = τ ∨ σ = -τ := by
  revert hσ hτ
  revert σ τ
  decide

/-- Each daughter owns exactly one visit of `c`: there are visits `w₁, w₂` of `c` with
`owner (insert c S) (inr wᵢ) = Λᵢ`. -/
theorem sge_daughter_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (A : Component hn hP S)
    {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hS' : IsDecomposition hn hP (insert c S)) (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    ∃ w₁ w₂ : Visit P, w₁.1 = c ∧ w₂.1 = c ∧
      owner hn hP (insert c S) (Sum.inr w₁) = Λ₁ ∧ owner hn hP (insert c S) (Sum.inr w₂) = Λ₂ := by
  have hown0 : ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = A :=
    ((mem_carrierCrossings hn hP S A c).mp hc).2
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  let v₀ : Visit P := ⟨c, i⟩
  have hv₀ : v₀.1 = c := rfl
  have hv₁ : (visitTwin v₀).1 = c := (visitTwin_crossing v₀).trans hv₀
  have hv₀' : v₀.1 ∈ insert c S := by
    rw [hv₀]
    exact Finset.mem_insert_self c S
  have h0 := (hown (Sum.inr v₀)).mp (hown0 v₀ hv₀)
  have h1 := (hown (Sum.inr (visitTwin v₀))).mp (hown0 (visitTwin v₀) hv₁)
  have hsep := independent_selected_pair_owners_ne hn hP hS' v₀ hv₀'
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hsep
    · exact ⟨v₀, visitTwin v₀, hv₀, hv₁, h0, h1⟩
  · rcases h1 with h1 | h1
    · exact ⟨visitTwin v₀, v₀, hv₁, hv₀, h1, h0⟩
    · exact absurd (h0.trans h1.symm) hsep

/-- **The signed turn pattern of a daughter.** Every corner of the daughter `Λ` other than its visit
`w` of `c` is a corner of `A` (owned by `A`, a true corner of `S`), hence turns by `τ`; the corner at
`w` turns by `markTurn (inr w) ∈ {τ, −τ}`.  So `Λ` is uniform of sign `τ` or has exactly one dissent. -/
theorem sge_daughter_pattern (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {c : Crossing P} (hS' : IsDecomposition hn hP (insert c S))
    (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂)
    (Λ : Component hn hP (insert c S)) (hΛ : Λ = Λ₁ ∨ Λ = Λ₂)
    (w : Visit P) (hw : w.1 = c) (hwΛ : owner hn hP (insert c S) (Sum.inr w) = Λ)
    (τ : SignType) (hτ0 : τ ≠ 0) (hτ : ∀ j, turn (ccpCornerPolygon hn hP S A) j = τ) :
    (∀ j, turn (ccpCornerPolygon hn hP (insert c S) Λ) j = τ) ∨
      (∃ j₀, turn (ccpCornerPolygon hn hP (insert c S) Λ) j₀ = -τ ∧
        ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP (insert c S) Λ) j = τ) := by
  have hwT : IsTrueCorner (insert c S) (Sum.inr w) := by
    show w.1 ∈ insert c S
    rw [hw]
    exact Finset.mem_insert_self c S
  -- every corner of `Λ` other than `inr w` is an inherited corner of `A`, of turn `τ`
  have hother : ∀ j, ccpCornerMark hn hP (insert c S) Λ j ≠ Sum.inr w →
      turn (ccpCornerPolygon hn hP (insert c S) Λ) j = τ := by
    intro j hj
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS' Λ j]
    have hmΛ : owner hn hP (insert c S) (ccpCornerMark hn hP (insert c S) Λ j) = Λ :=
      ccpCornerMark_owner hn hP _ Λ j
    have hmA : owner hn hP S (ccpCornerMark hn hP (insert c S) Λ j) = A := by
      rw [hown]
      rcases hΛ with rfl | rfl
      · exact Or.inl hmΛ
      · exact Or.inr hmΛ
    have hmT' : IsTrueCorner (insert c S) (ccpCornerMark hn hP (insert c S) Λ j) :=
      ccpCornerMark_isTrueCorner hn hP _ Λ j
    rcases (sge_isTrueCorner_insert S c w hw _).mp hmT' with hT | hmw | hmw
    · obtain ⟨j', hj'⟩ := ccpCornerMark_exists hn hP S A _ hmA hT
      rw [← hj', ← turn_ccpCornerPolygon_eq_markTurn hn hP hS A j']
      exact hτ j'
    · exact absurd hmw hj
    · exfalso
      apply independent_selected_pair_owners_ne hn hP hS' w hwT
      rw [hwΛ, ← hmw]
      exact hmΛ.symm
  -- the corner at `w`
  obtain ⟨j₀, hj₀⟩ := ccpCornerMark_exists hn hP (insert c S) Λ (Sum.inr w) hwΛ hwT
  have hj₀turn : turn (ccpCornerPolygon hn hP (insert c S) Λ) j₀ = markTurn P (Sum.inr w) := by
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS' Λ j₀, hj₀]
  have hw0 : markTurn P (Sum.inr w) ≠ 0 := markTurn_ne_zero hn hP hS' w hwT
  rcases sge_signType_eq_or_neg hw0 hτ0 with h | h
  · left
    intro j
    by_cases hj : ccpCornerMark hn hP (insert c S) Λ j = Sum.inr w
    · have hjj : j = j₀ := ccpCornerMark_injective hn hP _ Λ (hj.trans hj₀.symm)
      rw [hjj, hj₀turn, h]
    · exact hother j hj
  · right
    refine ⟨j₀, by rw [hj₀turn, h], fun j hj => hother j ?_⟩
    intro hj'
    exact hj (ccpCornerMark_injective hn hP _ Λ (hj'.trans hj₀.symm))

/-- lem:uniformrot read at a signed pattern: a regular carrier polygon that is uniform of sign `τ` or
has exactly one dissent `−τ` has its rotation on the ray of `τ` (`uniform_rotation` (i)–(iv)). -/
theorem sge_rotation_ray (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (τ : SignType)
    (h : (∀ j, turn (ccpCornerPolygon hn hP S q) j = τ) ∨
      (∃ j₀, turn (ccpCornerPolygon hn hP S q) j₀ = -τ ∧
        ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP S q) j = τ)) :
    (τ = 1 → 1 ≤ carrierRotation hn hP S q) ∧ (τ = -1 → carrierRotation hn hP S q ≤ -1) := by
  have hreg := ccpCornerPolygon_regular hn hP hS q
  have h3 := ccpCornerCount_ge_three hn hP hS q
  have hnz : ∀ j, turn (ccpCornerPolygon hn hP S q) j ≠ 0 :=
    fun j => ccpCornerPolygon_turn_ne_zero hn hP hS q j
  obtain ⟨h1, h2, h3', h4⟩ := uniform_rotation h3 (ccpCornerPolygon hn hP S q) hreg hnz
  constructor
  · rintro rfl
    rcases h with h | ⟨j₀, hj₀, hoth⟩
    · exact h1 h
    · exact h3' ⟨j₀, hj₀, hoth⟩
  · rintro rfl
    rcases h with h | ⟨j₀, hj₀, hoth⟩
    · exact h2 h
    · refine h4 ⟨j₀, ?_, hoth⟩
      rw [hj₀]
      decide

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
  obtain ⟨τ, hτ0, hτ⟩ := hA
  obtain ⟨w₁, w₂, hw₁, hw₂, ho₁, ho₂⟩ := sge_daughter_visits hn hP S A hc hS' Λ₁ Λ₂ hown
  have hp₁ := sge_daughter_pattern hn hP hS A hS' Λ₁ Λ₂ hown Λ₁ (Or.inl rfl) w₁ hw₁ ho₁ τ hτ0 hτ
  have hp₂ := sge_daughter_pattern hn hP hS A hS' Λ₁ Λ₂ hown Λ₂ (Or.inr rfl) w₂ hw₂ ho₂ τ hτ0 hτ
  have hsum := sge_rotation_add hn hP hS A hc hS' Λ₁ Λ₂ hne hown
  refine ⟨⟨τ, hτ0, hp₁⟩, ⟨τ, hτ0, hp₂⟩, hsum, ?_⟩
  -- the integer form: all three rotations lie on the ray of `τ` (lem:uniformrot)
  have hrayA := sge_rotation_ray hn hP hS A τ (Or.inl hτ)
  have hray₁ := sge_rotation_ray hn hP hS' Λ₁ τ hp₁
  have hray₂ := sge_rotation_ray hn hP hS' Λ₂ τ hp₂
  have hcA := carrierRotationInt_cast hn hP hS A
  have hc₁ := carrierRotationInt_cast hn hP hS' Λ₁
  have hc₂ := carrierRotationInt_cast hn hP hS' Λ₂
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [hcA, hc₁, hc₂, hsum]
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · have hA' := hrayA.2 rfl
    have h1' := hray₁.2 rfl
    have h2' := hray₂.2 rfl
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
    ring
  · exact absurd rfl hτ0
  · have hA' := hrayA.1 rfl
    have h1' := hray₁.1 rfl
    have h2' := hray₂.1 rfl
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]

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
