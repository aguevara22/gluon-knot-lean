-- W3_Skeleton.lean — corner wave 3 (row 110 thm:C-S7), 2026-09-15: the four open declarations of Corner_Assembled.lean
-- (s7_sliding_law_at 8656-8668, s7_bigon_law_at 9816-9834, thm_C_S7_of / thm_C_S7_of_floor 10008-10039) VERBATIM on top of the
-- ported library (SM.CornerChainUnits = waves 1-2a, SM.CS7Sliding = wave 2b, SM.BigonDeletion = the moves toolkit,
-- SM.CarrierFloorRows = thm_floor), plus the row theorem. Units APPEND prefixed material and may replace ONLY the two `sorry`
-- bodies; statements, names and docstrings are frozen (audit A-110-1, AUTHOR_NOTES 20:46Z).
import SM.CornerChainUnits
import SM.CS7Sliding
import SM.BigonDeletion
import SM.CarrierFloorRows

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

section VertexEdge

variable {n : ℕ} [NeZero n]

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


/-! ### Unit J (wave 3, prefix `s7j_`; PLAN_FINAL §3.3 bigon (5), sm-4:655-668, 765-769, 777-783, 785-813,
800-835; serves U110-K `s7_bigon_law_at`): **where the floor and cb:singleton ENTER the bigon branch**.
Every theorem takes the EXTRACTED ROWS (the outputs of unit BLOCK: eq. s7c:interlacing-extraction
`Ω_H − Ω_L = [a^{K−2}](f₁f₂) − [a^K](f₁f₂)`, eq. s7c:noninterlacing-extraction with `K−4, K−2`, eq.
s7c:different-polynomials `f_H = f_L = f₁f₂`) as EXPLICIT HYPOTHESES in the vocabulary of the Laurent ring
`R` and of def:C (`cornerHomfly`, `cornerSlot`, `cornerCoefficient`), and returns the printed conclusion.
The floor `hF` enters ONLY through `FloorTheoremData.slot_le_of_signed` (§A); cb:singleton `hsing` ONLY
through `CbSingletonData.isolated_zero` (§E).  §D states the entries at the WALL's own halves
`firstHalf g.center M a`, `secondHalf g.center M a` with the leaf's genericity proofs `h₁ h₂` and sizes
`(contactHalfSizes_bounds hn h.1.1).i.1` — the printed hypothesis discharge (800-835): the half contact
carrier `Lᵢ` is a literal `Component hn'ᵢ hᵢ Tᵢ` of a decomposition `Tᵢ` of the generic half `λᵢ`, the
floor's domain; U110-B supplies `Tᵢ, hTᵢ, Lᵢ`.  The printed case "if either `fᵢ = 0`" is vacuous here:
`cornerHomfly_ne_zero`.  Every `s7j_` declaration is proved; no other wave-3 unit is consumed by name. -/
section S7JFloor

variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]

/-! #### A. The floor at one half contact carrier — `hF` enters -/

/-- lp:core `knot_support` on the one-component positive lift: `H⁺_Q` has no negative `z`-exponent
(the `hz` inputs of `s7_corner_product`). -/
theorem s7j_z_nonneg (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) (d k : ℤ)
    (h : coeffAt d k (cornerHomfly hn hP S q hS) ≠ 0) : 0 ≤ k := by
  unfold cornerHomfly at h
  rw [← P_eq_homfly] at h
  obtain ⟨j, hj⟩ := P_knot_support _ (positiveLift_componentCount hn hP S q hS) d k h
  omega

/-- **thm:floor at a UNIFORM half contact carrier** (the `ε = 1` reads, sm-4:680-684: "both half contact
carriers are uniform, and each is a subpolygon of a decomposition of its generic half … the domain of
Theorem floor, which gives `mindeg_a fᵢ ≥ kᵢ`"). -/
theorem s7j_floor_of_uniform (hF : FloorTheoremData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (hu : CarrierUniform hn hP S q) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) :=
  hF.slot_le_of_signed hn P hP S hS q (signedUniformOrOneDissent_of_uniform hn hP S q hu)

/-- **thm:floor at a ONE-DISSENT half contact carrier** (the `ε = 0` reads, sm-4:745-748: "every half
inherits its old turns and has exactly one new contact turn of sign `s₀`, hence exactly one dissent"):
turns `τ` everywhere except the contact corner `j₀`, where the turn is `−τ`. -/
theorem s7j_floor_of_dissent (hF : FloorTheoremData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {τ : SignType} (hτ : τ ≠ 0) (j₀ : ZMod (ccpCornerCount hn hP S q))
    (h0 : turn (ccpCornerPolygon hn hP S q) j₀ = -τ)
    (h : ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP S q) j = τ) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) :=
  hF.slot_le_of_signed hn P hP S hS q
    (s7c_signedUniformOrOneDissent_of_dissent (ccpCornerPolygon hn hP S q) hτ j₀ h0 h)

/-- The floor at a carrier with the signed pattern (the shape units C/I return). -/
theorem s7j_floor_of_signed (hF : FloorTheoremData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (hu : SignedUniformOrOneDissent (ccpCornerPolygon hn hP S q)) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) :=
  hF.slot_le_of_signed hn P hP S hS q hu

/-! #### B. The entries in the Laurent ring, with the extracted rows as hypotheses -/

/-- eq. s7c:interlacing-slot in pure `ℤ`: `k_L = 1 − w_L − R_L` with `w_L = w₁ + w₂ + 2ℓ − 1` (eq.
s7c:interlacing-writhe-row) and `R_L = R₁ + R₂` (eq. s7c:interlacing-absolute) gives `k_L + 2ℓ = K`. -/
theorem s7j_interlacing_slot_int {kL k₁ k₂ wL w₁ w₂ RL R₁ R₂ ℓ : ℤ} (hkL : kL = 1 - wL - RL)
    (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂) (hw : wL = w₁ + w₂ + 2 * ℓ - 1)
    (hR : RL = R₁ + R₂) : kL + 2 * ℓ = k₁ + k₂ := by omega

/-- eq. s7c:noninterlacing-slot in pure `ℤ`: with `w_L = w₁ + w₂ + 2ℓ` (eq. s7c:noninterlacing-writhe) and
`R₁ + R₂ − R_L = −1` (eq. s7c:noninterlacing-rotation), `K − k_L = 2ℓ + 2`. -/
theorem s7j_noninterlacing_slot_int {kL k₁ k₂ wL w₁ w₂ RL R₁ R₂ ℓ : ℤ} (hkL : kL = 1 - wL - RL)
    (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂) (hw : wL = w₁ + w₂ + 2 * ℓ)
    (hR : R₁ + R₂ - RL = -1) : k₁ + k₂ - kL = 2 * ℓ + 2 := by omega

/-- eqs. s7c:different-low-slot / -high-slot in pure `ℤ`: `w_L = w₁ + w₂`, `w_H = w₁ + w₂ + 2`,
`R₁ + R₂ − R_L = −1`, `R_H = R_L` give `k_L = K − 2` and `k_H = K − 4`. -/
theorem s7j_different_slot_int {kH kL k₁ k₂ wH wL w₁ w₂ RH RL R₁ R₂ : ℤ} (hkH : kH = 1 - wH - RH)
    (hkL : kL = 1 - wL - RL) (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂)
    (hwH : wH = w₁ + w₂ + 2) (hwL : wL = w₁ + w₂) (hR : R₁ + R₂ - RL = -1) (hRH : RH = RL) :
    kL = k₁ + k₂ - 2 ∧ kH = k₁ + k₂ - 4 := by omega

/-- **The interlacing entry** (sm-4:679-690, eq. s7c:interlacing-coefficient-result): from the extracted
row `Ω_H − Ω_L = [a^{K−2}](f₁f₂) − [a^K](f₁f₂)` with `K = k₁ + k₂`, the floors `kᵢ ≤ mindeg_a fᵢ` and no
negative `z`-exponents, `Ω_H − Ω_L = −ω₁ω₂` where `ωᵢ = [a^{kᵢ} z⁰] fᵢ` ("its degree `K − 2` coefficient
is zero; in the degree `K` convolution … the only possible pair is exactly `(k₁, k₂)`"). -/
theorem s7j_interlacing_entry {f₁ f₂ : R} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) {k₁ k₂ K : ℤ}
    (hK : K = k₁ + k₂) (h₁ : k₁ ≤ mindegAZ f₁) (h₂ : k₂ ≤ mindegAZ f₂)
    (hz₁ : ∀ d k, coeffAt d k f₁ ≠ 0 → 0 ≤ k) (hz₂ : ∀ d k, coeffAt d k f₂ ≠ 0 → 0 ≤ k)
    {ΩH ΩL : ℤ} (hrow : ΩH - ΩL = coeffAt (K - 2) 0 (f₁ * f₂) - coeffAt K 0 (f₁ * f₂)) :
    ΩH - ΩL = -(coeffAt k₁ 0 f₁ * coeffAt k₂ 0 f₂) := by
  obtain ⟨h0, hprod⟩ := s7_corner_product hf₁ hf₂ h₁ h₂ hz₁ hz₂
  subst hK
  rw [hrow, h0, hprod, zero_sub]

/-- **One read below the floor** (the device of sm-4:765-769 and 805-811): a row `Ω = [a^d z⁰](f₁f₂)` with
`d < k₁ + k₂` is zero. -/
theorem s7j_below_floor_entry {f₁ f₂ : R} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) {k₁ k₂ d : ℤ}
    (h₁ : k₁ ≤ mindegAZ f₁) (h₂ : k₂ ≤ mindegAZ f₂) (hd : d < k₁ + k₂) {Ω : ℤ}
    (hrow : Ω = coeffAt d 0 (f₁ * f₂)) : Ω = 0 := by
  rw [hrow]
  exact coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ hd

/-- **The noninterlacing entry** (sm-4:762-769, eq. s7c:noninterlacing-extraction): from the extracted row
`Ω_H − Ω_L = [a^{K−4}](f₁f₂) − [a^{K−2}](f₁f₂)` with `K = k₁ + k₂` and the two one-dissent floors,
"both displayed coefficients are below this floor; thus the returned newborn-free row is zero". -/
theorem s7j_noninterlacing_entry {f₁ f₂ : R} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) {k₁ k₂ K : ℤ}
    (hK : K = k₁ + k₂) (h₁ : k₁ ≤ mindegAZ f₁) (h₂ : k₂ ≤ mindegAZ f₂) {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL = coeffAt (K - 4) 0 (f₁ * f₂) - coeffAt (K - 2) 0 (f₁ * f₂)) : ΩH - ΩL = 0 := by
  rw [hrow, coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ (by omega),
    coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ (by omega), sub_zero]

/-- **The different-block entry** (sm-4:785-813): with `f_H = f_L = f₁f₂` (eq. s7c:different-polynomials)
and the slots `k_L = K − 2`, `k_H = K − 4` (eqs. s7c:different-low/high-slot) below the floor `K` of the
product, "both reads vanish separately": `Ω_H = 0` and `Ω_L = 0`. -/
theorem s7j_different_block_entry {fH fL f₁ f₂ : R} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (hfH : fH = f₁ * f₂) (hfL : fL = f₁ * f₂) {kH kL k₁ k₂ : ℤ} (hkH : kH = k₁ + k₂ - 4)
    (hkL : kL = k₁ + k₂ - 2) (h₁ : k₁ ≤ mindegAZ f₁) (h₂ : k₂ ≤ mindegAZ f₂) :
    coeffAt kH 0 fH = 0 ∧ coeffAt kL 0 fL = 0 :=
  ⟨by rw [hfH]; exact coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ (by omega),
   by rw [hfL]; exact coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ (by omega)⟩

/-! #### C. The entries at carriers (def:C's vocabulary at two half contact carriers `L₁, L₂`) -/

/-- The interlacing entry at two UNIFORM half contact carriers: the extracted row at `K = k₁ + k₂`
(`cornerSlot`s) on `H⁺_{L₁} H⁺_{L₂}` returns `Ω_H − Ω_L = −c(L₁) c(L₂)`. -/
theorem s7j_interlacing_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : CarrierUniform hn₁ hP₁ S₁ q₁) (hu₂ : CarrierUniform hn₂ hP₂ S₂ q₂) {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL =
      coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) -
        coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)) :
    ΩH - ΩL = -(cornerCoefficient hn₁ hP₁ S₁ q₁ hS₁ * cornerCoefficient hn₂ hP₂ S₂ q₂ hS₂) :=
  s7j_interlacing_entry (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁) (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂)
    rfl (s7j_floor_of_uniform hF hn₁ hP₁ hS₁ q₁ hu₁) (s7j_floor_of_uniform hF hn₂ hP₂ hS₂ q₂ hu₂)
    (s7j_z_nonneg hn₁ hP₁ hS₁ q₁) (s7j_z_nonneg hn₂ hP₂ hS₂ q₂) hrow

/-- The noninterlacing entry at two half contact carriers with the signed (one-dissent) pattern: the
extracted row at `K − 4, K − 2` returns `Ω_H − Ω_L = 0`. -/
theorem s7j_noninterlacing_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL =
      coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 4) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) -
        coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)) :
    ΩH - ΩL = 0 :=
  s7j_noninterlacing_entry (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁)
    (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂) rfl (s7j_floor_of_signed hF hn₁ hP₁ hS₁ q₁ hu₁)
    (s7j_floor_of_signed hF hn₂ hP₂ hS₂ q₂ hu₂) hrow

/-- Any read of `H⁺_{L₁} H⁺_{L₂}` at an `a`-degree below `k₁ + k₂` is zero at signed patterns. -/
theorem s7j_below_floor_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) {d : ℤ}
    (hd : d < cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂) :
    coeffAt d 0 (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) = 0 :=
  coeffAt_mul_eq_zero_of_lt_floor (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁)
    (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂) (s7j_floor_of_signed hF hn₁ hP₁ hS₁ q₁ hu₁)
    (s7j_floor_of_signed hF hn₂ hP₂ hS₂ q₂ hu₂) hd

/-- The different-block entry at carriers: `H⁺_{L_H} = H⁺_{L_L} = H⁺_{L₁} H⁺_{L₂}` (mp:blocks with the two
singleton newborn blocks, sm-4:785-800) and the slots `k_L = K − 2`, `k_H = K − 4` give
`c(L_H) = 0 ∧ c(L_L) = 0`. -/
theorem s7j_different_block_read (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hfH : cornerHomfly hn hPH SH qH hSH = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)
    (hfL : cornerHomfly hn hPL SL qL hSL = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)
    (hkH : cornerSlot hn hPH SH qH = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 4)
    (hkL : cornerSlot hn hPL SL qL = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) :
    cornerCoefficient hn hPH SH qH hSH = 0 ∧ cornerCoefficient hn hPL SL qL hSL = 0 := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt]
  exact s7j_different_block_entry (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁)
    (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂) hfH hfL hkH hkL (s7j_floor_of_signed hF hn₁ hP₁ hS₁ q₁ hu₁)
    (s7j_floor_of_signed hF hn₂ hP₂ hS₂ q₂ hu₂)

/-- The slots of the different-block alternative from the printed counts (eq. s7c:different-polynomials'
writhes `m_H = m₁ + m₂ + 2`, `m_L = m₁ + m₂`; eq. s7c:noninterlacing-rotation `R₁ + R₂ − R_L = −1`; eq.
s7c:full-rotation `R_H = R_L`) — the inputs of `s7j_different_block_read`. -/
theorem s7j_different_block_slots (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hmH : carrierCrossingCount hn hPH SH qH =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + 2)
    (hmL : carrierCrossingCount hn hPL SL qL =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂)
    (hR : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hPL SL qL| = -1)
    (hRH : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|) :
    cornerSlot hn hPH SH qH = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 4 ∧
      cornerSlot hn hPL SL qL = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2 := by
  unfold cornerSlot
  rw [hmH, hmL, hRH]
  push_cast
  omega

/-- eq. s7c:interlacing-slot at carriers (sm-4:665-670): `k_L + 2ℓ = k₁ + k₂` from the writhe count
`m_L = m₁ + m₂ + 2ℓ − 1` (eq. s7c:interlacing-writhe-row; `tl = 2ℓ = twoLinking D_A`) and
`|R_L| = |R₁| + |R₂|` (eq. s7c:interlacing-absolute). -/
theorem s7j_interlacing_slot (hn : 3 ≤ n) {PL : LabelledTuple n} (hPL : Generic PL)
    {SL : Finset (Crossing PL)} (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (q₁ : Component hn₁ hP₁ S₁)
    (q₂ : Component hn₂ hP₂ S₂) (tl : ℤ)
    (hw : (carrierCrossingCount hn hPL SL qL : ℤ) =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + tl - 1)
    (hR : |carrierRotationInt hn hPL SL qL| =
      |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂|) :
    cornerSlot hn hPL SL qL + tl = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ := by
  unfold cornerSlot
  rw [hR]
  omega

/-- eq. s7c:noninterlacing-slot at carriers (sm-4:758-762): `K − (k_L + 2ℓ) = 2` from
`m_L = m₁ + m₂ + 2ℓ` (eq. s7c:noninterlacing-writhe) and `|R₁| + |R₂| − |R_L| = −1`
(eq. s7c:noninterlacing-rotation). -/
theorem s7j_noninterlacing_slot (hn : 3 ≤ n) {PL : LabelledTuple n} (hPL : Generic PL)
    {SL : Finset (Crossing PL)} (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (q₁ : Component hn₁ hP₁ S₁)
    (q₂ : Component hn₂ hP₂ S₂) (tl : ℤ)
    (hw : (carrierCrossingCount hn hPL SL qL : ℤ) =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + tl)
    (hR : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hPL SL qL| = -1) :
    cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - (cornerSlot hn hPL SL qL + tl) = 2 := by
  unfold cornerSlot
  omega

/-- **The interlacing row in the printed order** (sm-4:655-690): from the universal extraction on the
two-component row, `c(L_H) − c(L_L) = [a^{k_L+2ℓ−2}](H⁺_{L₁}H⁺_{L₂}) − [a^{k_L+2ℓ}](H⁺_{L₁}H⁺_{L₂})`
(the output shape of the skein/two-component units, `tl = 2ℓ`), the writhe count, the rotation identity
and the two UNIFORM half contact carriers: `c(L_H) − c(L_L) = −c(L₁) c(L₂)`. -/
theorem s7j_interlacing_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂) (hu₁ : CarrierUniform hn₁ hP₁ S₁ q₁)
    (hu₂ : CarrierUniform hn₂ hP₂ S₂ q₂) (tl : ℤ)
    (hext : cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      coeffAt (cornerSlot hn hPL SL qL + tl - 2) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) -
        coeffAt (cornerSlot hn hPL SL qL + tl) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂))
    (hw : (carrierCrossingCount hn hPL SL qL : ℤ) =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + tl - 1)
    (hR : |carrierRotationInt hn hPL SL qL| =
      |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂|) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      -(cornerCoefficient hn₁ hP₁ S₁ q₁ hS₁ * cornerCoefficient hn₂ hP₂ S₂ q₂ hS₂) := by
  have hK := s7j_interlacing_slot hn hPL qL hn₁ hn₂ hP₁ hP₂ q₁ q₂ tl hw hR
  rw [hK] at hext
  exact s7j_interlacing_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ hext

/-- **The noninterlacing row in the printed order** (sm-4:736-769): the same extraction shape at
`k_L + 2ℓ`, the writhe count `m_L = m₁ + m₂ + 2ℓ`, the rotation identity `|R₁| + |R₂| − |R_L| = −1` and
the two ONE-DISSENT half contact carriers: `c(L_H) − c(L_L) = 0`. -/
theorem s7j_noninterlacing_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) (tl : ℤ)
    (hext : cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      coeffAt (cornerSlot hn hPL SL qL + tl - 2) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) -
        coeffAt (cornerSlot hn hPL SL qL + tl) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂))
    (hw : (carrierCrossingCount hn hPL SL qL : ℤ) =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + tl)
    (hR : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hPL SL qL| = -1) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL = 0 := by
  have hK := s7j_noninterlacing_slot hn hPL qL hn₁ hn₂ hP₁ hP₂ q₁ q₂ tl hw hR
  rw [hext]
  rw [s7j_below_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ (by omega),
    s7j_below_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ (by omega), sub_zero]

/-! #### D. The entries at the WALL's halves — the floor-domain discharge (sm-4:800-835) literally:
`λ₁ = firstHalf g.center M a`, `λ₂ = secondHalf g.center M a` with the leaf's `h₁ h₂ : Generic` and sizes
`(contactHalfSizes_bounds hn h.1.1).1.1 / .2.1`; `Tᵢ` a decomposition of `λᵢ`, `Lᵢ : Component … Tᵢ`. -/

/-- thm:floor at a carrier of a decomposition of the FIRST generic half of a bigon wall. -/
theorem s7j_half₁_floor (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    {T₁ : Finset (Crossing (firstHalf g.center M a))}
    (hT₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (L₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (hu : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁)) :
    cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ ≤
      mindegAZ (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁) :=
  s7j_floor_of_signed hF _ h₁ hT₁ L₁ hu

/-- thm:floor at a carrier of a decomposition of the SECOND generic half of a bigon wall. -/
theorem s7j_half₂_floor (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.BigonAt M a) (h₂ : Generic (secondHalf g.center M a))
    {T₂ : Finset (Crossing (secondHalf g.center M a))}
    (hT₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (L₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (hu : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂)) :
    cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ ≤
      mindegAZ (cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂) :=
  s7j_floor_of_signed hF _ h₂ hT₂ L₂ hu

/-- **The interlacing entry at the wall's halves** (`ε = 1`): the two UNIFORM half contact carriers
`L₁, L₂`, carriers of decompositions `T₁, T₂` of the generic halves, and the extracted row on
`H⁺_{L₁} H⁺_{L₂}` at `K − 2, K` give `Ω_H − Ω_L = −c(L₁) c(L₂)`. -/
theorem s7j_interlacing_entry_at_halves (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n)
    (M a : ZMod n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) {T₁ : Finset (Crossing (firstHalf g.center M a))}
    {T₂ : Finset (Crossing (secondHalf g.center M a))}
    (hT₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (hT₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (L₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (L₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (hu₁ : CarrierUniform (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁)
    (hu₂ : CarrierUniform (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂) {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL =
      coeffAt (cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
          cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ - 2) 0
          (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
            cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂) -
        coeffAt (cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
          cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂) 0
          (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
            cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂)) :
    ΩH - ΩL = -(cornerCoefficient (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
      cornerCoefficient (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂) :=
  s7j_interlacing_read hF _ _ h₁ h₂ hT₁ hT₂ L₁ L₂ hu₁ hu₂ hrow

/-- **The noninterlacing entry at the wall's halves** (`ε = 0`): the two ONE-DISSENT half contact carriers
and the extracted row at `K − 4, K − 2` give `Ω_H − Ω_L = 0`. -/
theorem s7j_noninterlacing_entry_at_halves (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n)
    (M a : ZMod n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) {T₁ : Finset (Crossing (firstHalf g.center M a))}
    {T₂ : Finset (Crossing (secondHalf g.center M a))}
    (hT₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (hT₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (L₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (L₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂))
    {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL =
      coeffAt (cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
          cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ - 4) 0
          (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
            cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂) -
        coeffAt (cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
          cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ - 2) 0
          (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
            cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂)) :
    ΩH - ΩL = 0 :=
  s7j_noninterlacing_read hF _ _ h₁ h₂ hT₁ hT₂ L₁ L₂ hu₁ hu₂ hrow

/-- **The different-block entry at the wall's halves**: `H⁺_{L_H} = H⁺_{L_L} = H⁺_{L₁} H⁺_{L₂}` with the
printed counts and rotations at the two one-dissent half contact carriers give `c(L_H) = 0 ∧ c(L_L) = 0`. -/
theorem s7j_different_block_entry_at_halves (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n)
    (M a : ZMod n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) {T₁ : Finset (Crossing (firstHalf g.center M a))}
    {T₂ : Finset (Crossing (secondHalf g.center M a))}
    (hT₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (hT₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (L₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (L₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (hfH : cornerHomfly hn hPH SH qH hSH =
      cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
        cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂)
    (hfL : cornerHomfly hn hPL SL qL hSL =
      cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
        cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂)
    (hmH : carrierCrossingCount hn hPH SH qH =
      carrierCrossingCount (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
        carrierCrossingCount (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ + 2)
    (hmL : carrierCrossingCount hn hPL SL qL =
      carrierCrossingCount (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
        carrierCrossingCount (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂)
    (hR : |carrierRotationInt (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁| +
      |carrierRotationInt (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂| -
      |carrierRotationInt hn hPL SL qL| = -1)
    (hRH : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂)) :
    cornerCoefficient hn hPH SH qH hSH = 0 ∧ cornerCoefficient hn hPL SL qL hSL = 0 := by
  obtain ⟨hkH, hkL⟩ := s7j_different_block_slots hn hPH hPL qH qL _ _ h₁ h₂ L₁ L₂ hmH hmL hR hRH
  exact s7j_different_block_read hF hn hPH hPL hSH hSL qH qL _ _ h₁ h₂ hT₁ hT₂ L₁ L₂ hfH hfL hkH hkL
    hu₁ hu₂

/-! #### E. The singleton entry (sm-4:777-783) — `hsing` enters -/

/-- The printed sentence "every old neighbour of `y` is also a neighbour of selected `x`, and hence is
dominated; thus `{y}` is an isolated block" in cb:singleton's vocabulary: if every unselected crossing
`c' ≠ y` interlacing `y` interlaces the SELECTED `x`, then `y` interlaces no other self-crossing of its carrier `q`
— a neighbour of a selected crossing has its two visits on different carriers (lem:carriers (iii),
`neighbor_visit_owners_ne`), whereas a self-crossing of `q` has both on `q`. -/
theorem s7j_isolated_of_neighbours_dominated (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {x y : Crossing P} (hx : x ∈ S)
    (hdom : ∀ c' : Crossing P, c' ∉ S → c' ≠ y → Interlaces hn hP y c' → Interlaces hn hP c' x) :
    ∀ c' ∈ carrierCrossings hn hP S q, c' ≠ y → ¬ Interlaces hn hP y c' := by
  intro c' hc' hne hint
  obtain ⟨hc'S, hc'q⟩ := (mem_carrierCrossings hn hP S q c').mp hc'
  have hN : c' ∈ supportNeighbors hn hP S :=
    (mem_supportNeighbors hn hP S c').mpr ⟨x, hx, hdom c' hc'S hne hint⟩
  obtain ⟨i, _, _⟩ := crossing_visits_exist c'
  exact neighbor_visit_owners_ne hn hP hS hN ⟨c', i⟩ rfl
    ((hc'q ⟨c', i⟩ rfl).trans (hc'q (visitTwin ⟨c', i⟩) rfl).symm)

/-- **cb:singleton at the support `T ∪ {x}` with the isolated block `{y}`** (sm-4:777-783): the owner `q`
of the newborn `y` is uniform, `y` is a self-crossing of `q`, and every unselected neighbour of `y` is a
neighbour of the selected `x`; then `c(q) = 0` ("Lemma cb:singleton makes the required coefficient zero,
including the zero-polynomial case"). -/
theorem s7j_singleton_entry (hsing : CbSingletonData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (hu : CarrierUniform hn hP S q) {x y : Crossing P} (hx : x ∈ S)
    (hy : y ∈ carrierCrossings hn hP S q)
    (hdom : ∀ c' : Crossing P, c' ∉ S → c' ≠ y → Interlaces hn hP y c' → Interlaces hn hP c' x) :
    cornerCoefficient hn hP S q hS = 0 :=
  hsing.isolated_zero n hn P hP S hS q hu y hy (s7j_isolated_of_neighbours_dominated hn hP hS q hx hdom)

/-- **Every one-newborn term is zero** (sm-4:781-783), in the term shape of eq. C-selector-form: "if a
one-newborn selector is zero its term vanishes; otherwise its owner is uniform, and cb:singleton makes the
required coefficient zero". -/
theorem s7j_one_newborn_term_zero (hsing : CbSingletonData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {x y : Crossing P} (hx : x ∈ S) (hy : y ∈ carrierCrossings hn hP S q)
    (hdom : ∀ c' : Crossing P, c' ∉ S → c' ≠ y → Interlaces hn hP y c' → Interlaces hn hP c' x) :
    wind hn hP S * cornerProduct hn hP S hS = 0 := by
  by_cases hu : CarrierUniform hn hP S q
  · unfold cornerProduct
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (s7j_singleton_entry hsing hn hP hS q hu hx hy hdom),
      mul_zero]
  · unfold wind
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (carrierWeight_eq_zero_of_not_uniform hn hP S q hu),
      zero_mul]

/-- The one-newborn term at the support `insert x T` literally (sm-4:777: "`T ∪ {x}` is a support since
`x` is adjacent to neither `T` nor `y`"; the support property `hS` is F's output). -/
theorem s7j_one_newborn_term_zero_insert (hsing : CbSingletonData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (x y : Crossing P)
    (hS : IsDecomposition hn hP (insert x T)) (q : Component hn hP (insert x T))
    (hy : y ∈ carrierCrossings hn hP (insert x T) q)
    (hdom : ∀ c' : Crossing P, c' ∉ insert x T → c' ≠ y → Interlaces hn hP y c' → Interlaces hn hP c' x) :
    wind hn hP (insert x T) * cornerProduct hn hP (insert x T) hS = 0 :=
  s7j_one_newborn_term_zero hsing hn hP hS q (Finset.mem_insert_self x T) hy hdom

end S7JFloor


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


end VertexEdge

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


/-- Row 110 thm:C-S7 (FIXED target name, axiom-policy.json): the assembly on thm:floor (row 100). -/
theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor

end

end SM
