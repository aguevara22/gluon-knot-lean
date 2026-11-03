import ExtendedReturnArcGeometry
import DirectGLSSW.CapCriticalEventGeometry

set_option autoImplicit false
namespace DirectGLSSW.FiniteCriticalRootAvoidance
open ExtendedReturnArcGeometry
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev CubicData := ℝ × ℝ × ℝ × ℝ

def cubicValue (c : CubicData) (ε : ℝ) : ℝ :=
  c.1 + ε*c.2.1 + ε^2*c.2.2.1 + ε^3*c.2.2.2

def NonzeroCoefficients (c : CubicData) : Prop :=
  c.1 ≠ 0 ∨ c.2.1 ≠ 0 ∨ c.2.2.1 ≠ 0 ∨ c.2.2.2 ≠ 0

/-- A cubic with nonzero constant term stays nonzero on an explicit positive interval. -/
def cubicConstantRadius (a b c d : ℝ) : ℝ :=
  min 1 (|a|/(2*(1+|b|+|c|+|d|)))

theorem cubicConstantRadius_pos (a b c d : ℝ) (ha : a ≠ 0) :
    0 < cubicConstantRadius a b c d := by
  apply lt_min (by norm_num)
  exact div_pos (abs_pos.mpr ha) (by positivity)

theorem cubic_constant_ne_zero (a b c d ε : ℝ) (ha : a ≠ 0)
    (hε : 0 ≤ ε) (hbound : ε < cubicConstantRadius a b c d) :
    a+ε*b+ε^2*c+ε^3*d ≠ 0 := by
  have hsmall : ε < 1 := lt_of_lt_of_le hbound (min_le_left _ _)
  have hfrac : ε < |a|/(2*(1+|b|+|c|+|d|)) := lt_of_lt_of_le hbound (min_le_right _ _)
  have hden : 0 < 2*(1+|b|+|c|+|d|) := by positivity
  have hmul := (lt_div_iff₀ hden).mp hfrac
  have hs2 : ε^2 ≤ ε := by nlinarith
  have hs3 : ε^3 ≤ ε := by
    calc
      ε^3 = ε^2*ε := by ring
      _ ≤ ε*ε := mul_le_mul_of_nonneg_right hs2 hε
      _ = ε^2 := by ring
      _ ≤ ε := hs2
  have hb2 := mul_le_mul_of_nonneg_right hs2 (abs_nonneg c)
  have hb3 := mul_le_mul_of_nonneg_right hs3 (abs_nonneg d)
  have hpert : |ε*b+ε^2*c+ε^3*d| < |a| := by
    calc
      |ε*b+ε^2*c+ε^3*d| ≤ |ε*b+ε^2*c|+|ε^3*d| := abs_add _ _
      _ ≤ (|ε*b|+|ε^2*c|)+|ε^3*d| := add_le_add_right (abs_add _ _) _
      _ = ε*|b|+ε^2*|c|+ε^3*|d| := by
        rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hε,abs_of_nonneg (sq_nonneg ε),
          abs_of_nonneg (pow_nonneg hε 3)]
      _ < |a| := by nlinarith [abs_nonneg b,abs_nonneg c,abs_nonneg d,abs_pos.mpr ha]
  intro hz
  have heq : ε*b+ε^2*c+ε^3*d = -a := by linarith
  rw [heq,abs_neg] at hpert
  exact (lt_irrefl _) hpert

/-- Factor out the first nonzero epsilon power; the remaining constant term controls the radius. -/
def cubicAvoidanceRadius (c : CubicData) : ℝ :=
  if c.1 ≠ 0 then cubicConstantRadius c.1 c.2.1 c.2.2.1 c.2.2.2
  else if c.2.1 ≠ 0 then quadraticRadius c.2.1 c.2.2.1 c.2.2.2
  else if c.2.2.1 ≠ 0 then quadraticRadius c.2.2.1 c.2.2.2 0 else 1

theorem cubicAvoidanceRadius_pos (c : CubicData) :
    0 < cubicAvoidanceRadius c := by
  unfold cubicAvoidanceRadius
  split_ifs with h0 h1 h2
  · exact cubicConstantRadius_pos _ _ _ _ h0
  · exact quadraticRadius_pos _ _ _ h1
  · exact quadraticRadius_pos _ _ _ h2
  · norm_num

theorem cubic_ne_zero_of_small (c : CubicData) (hc : NonzeroCoefficients c)
    (ε : ℝ) (hε : 0 < ε) (hbound : ε < cubicAvoidanceRadius c) :
    cubicValue c ε ≠ 0 := by
  unfold cubicAvoidanceRadius at hbound
  split_ifs at hbound with h0 h1 h2
  · exact cubic_constant_ne_zero _ _ _ _ ε h0 hε.le hbound
  · have h0' : c.1 = 0 := not_ne_iff.mp h0
    have hq := quadratic_ne_zero _ _ _ ε h1 hε.le hbound
    have heq : cubicValue c ε = ε*(c.2.1+ε*c.2.2.1+ε^2*c.2.2.2) := by
      dsimp [cubicValue]; rw [h0']; ring
    rw [heq]
    exact mul_ne_zero (ne_of_gt hε) hq
  · have h0' : c.1 = 0 := not_ne_iff.mp h0
    have h1' : c.2.1 = 0 := not_ne_iff.mp h1
    have hq := quadratic_ne_zero _ _ 0 ε h2 hε.le hbound
    have heq : cubicValue c ε = ε^2*(c.2.2.1+ε*c.2.2.2+ε^2*0) := by
      dsimp [cubicValue]; rw [h0',h1']; ring
    rw [heq]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hε)) hq
  · have h3 : c.2.2.2 ≠ 0 := ((hc.resolve_left h0).resolve_left h1).resolve_left h2
    have heq : cubicValue c ε = ε^3*c.2.2.2 := by
      simp [cubicValue,not_ne_iff.mp h0,not_ne_iff.mp h1,not_ne_iff.mp h2]
    rw [heq]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hε)) h3

/-- All sufficiently small positive parameters avoid a finite family of nonzero cubics.
The nonzero-coefficient premise is explicit and is not inferred from G1-G2. -/
theorem finite_cubic_avoidance {ι : Type*} [Fintype ι]
    (C : ι → CubicData) (hC : ∀ i, NonzeroCoefficients (C i)) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧ ∀ i, cubicValue (C i) ε ≠ 0 := by
  let δ := min ρ (finiteRadius (fun i => cubicAvoidanceRadius (C i)))
  have hδ : 0 < δ := lt_min hρ (finiteRadius_pos _ (fun i => cubicAvoidanceRadius_pos (C i)))
  have hδρ : δ ≤ ρ := min_le_left _ _
  refine ⟨δ/2,by linarith,by linarith,?_⟩
  intro i
  apply cubic_ne_zero_of_small _ (hC i) _ (by linarith)
  exact lt_of_lt_of_le (by linarith : δ/2 < δ)
    ((min_le_right _ _).trans (finiteRadius_le _ i))

abbrev QuadraticData := ℝ × ℝ × ℝ
abbrev LinearData := ℝ × ℝ

def quadraticValue (B : QuadraticData) (ε : ℝ) : ℝ := B.1+ε*B.2.1+ε^2*B.2.2

def linearValue (D : LinearData) (ε : ℝ) : ℝ := D.1+ε*D.2

def ZeroSlope (D : LinearData) : Prop := D.1 = 0 ∧ D.2 = 0

/-- Cross multiplication of quadratic base determinants and affine slopes has degree at most three. -/
def collisionData (B B' : QuadraticData) (D D' : LinearData) : CubicData :=
  (B.1*D'.1-B'.1*D.1,
   B.1*D'.2+B.2.1*D'.1-B'.1*D.2-B'.2.1*D.1,
   B.2.1*D'.2+B.2.2*D'.1-B'.2.1*D.2-B'.2.2*D.1,
   B.2.2*D'.2-B'.2.2*D.2)

theorem collisionData_value (B B' : QuadraticData) (D D' : LinearData) (ε : ℝ) :
    cubicValue (collisionData B B' D D') ε =
      quadraticValue B ε*linearValue D' ε-quadraticValue B' ε*linearValue D ε := by
  dsimp [collisionData,cubicValue,quadraticValue,linearValue]
  ring

/-- Required regularity in the original data: a pair is permanently horizontal,
or the cross-multiplied collision polynomial has a genuinely nonzero coefficient. -/
def NoPersistentCoincidence {ι : Type*} (B : ι → QuadraticData) (D : ι → LinearData) : Prop :=
  ∀ p r, p ≠ r → ZeroSlope (D p) ∨ ZeroSlope (D r) ∨
    NonzeroCoefficients (collisionData (B p) (B r) (D p) (D r))

/-- Conditional finite bad-epsilon criterion for actual rational-root formulas.
It isolates rather than proves the needed dense-domain nonidentity condition. -/
theorem exists_injective_rational_roots {ι : Type*} [Fintype ι]
    (B : ι → QuadraticData) (D : ι → LinearData)
    (hreg : NoPersistentCoincidence B D) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧
      Set.InjOn (fun p => -quadraticValue (B p) ε / linearValue (D p) ε)
        {p | linearValue (D p) ε ≠ 0} := by
  let C : ι × ι → CubicData := fun z =>
    if z.1 ≠ z.2 ∧ ¬ ZeroSlope (D z.1) ∧ ¬ ZeroSlope (D z.2) then
      collisionData (B z.1) (B z.2) (D z.1) (D z.2) else (1,0,0,0)
  have hC : ∀ z, NonzeroCoefficients (C z) := by
    intro z
    dsimp [C]
    split_ifs with h
    · exact ((hreg z.1 z.2 h.1).resolve_left h.2.1).resolve_left h.2.2
    · exact Or.inl one_ne_zero
  obtain ⟨ε,hε,hερ,havoid⟩ := finite_cubic_avoidance C hC ρ hρ
  refine ⟨ε,hε,hερ,?_⟩
  intro p hp r hr heq
  by_contra hpr
  have hDp : ¬ ZeroSlope (D p) := by
    rintro ⟨h0,h1⟩
    apply hp
    simp [linearValue,h0,h1]
  have hDr : ¬ ZeroSlope (D r) := by
    rintro ⟨h0,h1⟩
    apply hr
    simp [linearValue,h0,h1]
  have hnon := havoid (p,r)
  have hcond : p ≠ r ∧ ¬ ZeroSlope (D p) ∧ ¬ ZeroSlope (D r) := ⟨hpr,hDp,hDr⟩
  simp only [C,if_pos hcond,collisionData_value] at hnon
  have hcross := (div_eq_div_iff hp hr).mp heq
  apply hnon
  simp only [neg_mul,neg_inj] at hcross
  exact sub_eq_zero.mpr hcross


end
end DirectGLSSW.FiniteCriticalRootAvoidance




















