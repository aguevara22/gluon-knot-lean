import FiniteCriticalRootAvoidance

set_option autoImplicit false
namespace DirectGLSSW.ExtendedArcCriticalData
open ExtendedReturnArcGeometry FiniteCriticalRootAvoidance CapCriticalTimes CapCriticalEventGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- All ordered secant label pairs; transversality is imposed by the actual slope at epsilon. -/
abbrev SecantLabel (n : ℕ) :=
  {p : Fin (n+1) × Fin (n+1) // 0 < p.1.val ∧ p.1.val < p.2.val}

def labelNat (p : SecantLabel n) : ℕ × ℕ := (p.val.1.val,p.val.2.val)

def arcBase (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (k : ℕ) : PlanarPoint ℝ :=
  if hk : 0 < k ∧ k ≤ n then P ⟨k-1,by omega⟩ else P (zeroIndex hn)

def arcVelocity (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (k : ℕ) : PlanarPoint ℝ :=
  if hk : 0 < k ∧ k ≤ n then endpointVelocity hn P ⟨k-1,by omega⟩ else 0

theorem extendedArc_affine (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (ε : ℝ) (k : ℕ) :
    extendedArc hn P ε k = arcBase hn P k + ε • arcVelocity hn P k := by
  unfold extendedArc arcFromWord arcBase arcVelocity
  split_ifs with hk
  · rfl
  · simp

/-- Actual quadratic coefficients of polygonHDet Q 0 k j. -/
def baseData (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (p : SecantLabel n) : QuadraticData :=
  let A := arcBase hn P
  let V := arcVelocity hn P
  let k := (labelNat p).1
  let j := (labelNat p).2
  (planarDet (A k-A j) (A 0-A j),
   planarDet (V k-V j) (A 0-A j) + planarDet (A k-A j) (V 0-V j),
   planarDet (V k-V j) (V 0-V j))

/-- Actual affine coefficients of the horizontal secant slope. -/
def slopeData (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (p : SecantLabel n) : LinearData :=
  (planarDet (arcBase hn P (labelNat p).1-arcBase hn P (labelNat p).2) (1,0),
   planarDet (arcVelocity hn P (labelNat p).1-arcVelocity hn P (labelNat p).2) (1,0))

theorem baseData_eval (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (p : SecantLabel n) (ε : ℝ) :
    quadraticValue (baseData hn P p) ε =
      polygonHDet (extendedArc hn P ε) 0 (labelNat p).1 (labelNat p).2 := by
  dsimp [polygonHDet]
  rw [extendedArc_affine,extendedArc_affine,extendedArc_affine]
  dsimp [quadraticValue,baseData,planarDet]
  ring

theorem slopeData_eval (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (p : SecantLabel n) (ε : ℝ) :
    linearValue (slopeData hn P p) ε =
      planarDet (extendedArc hn P ε (labelNat p).1-extendedArc hn P ε (labelNat p).2) (1,0) := by
  rw [extendedArc_affine,extendedArc_affine]
  dsimp [linearValue,slopeData,planarDet]
  ring

/-- The auxiliary nonidentity hypothesis is fully expressed in original vertex coordinates.
It is NOT a consequence of G1-G2; the forced-secant diagnostic supplies a counterexample. -/
def ExtendedSecantRegular (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) : Prop :=
  NoPersistentCoincidence (baseData hn P) (slopeData hn P)

/-- Exact conditional bridge to the hroots used by the staged cap recurrence.
The radius is the existing geometric radius, and the sole extra premise is the
explicit coefficient nonidentity condition, whose dense-domain proof is separate. -/
theorem exists_extendedArc_injective (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hP : cyclicNoncollinear P) (hreg : ExtendedSecantRegular hn P) :
    ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hn P ∧
      Set.InjOn (criticalRoot (extendedArc hn P ε)) ↑(criticalPairs (extendedArc hn P ε) n) := by
  obtain ⟨ε,hε,hbound,hinj⟩ := exists_injective_rational_roots
    (baseData hn P) (slopeData hn P) hreg (geometricRadius hn P) (geometricRadius_pos hn P hP)
  refine ⟨ε,hε,hbound,?_⟩
  intro a ha b hb heq
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have ha1 := Finset.mem_range.mp (Finset.mem_product.mp ha'.1).1
  have ha2 := Finset.mem_range.mp (Finset.mem_product.mp ha'.1).2
  have hb1 := Finset.mem_range.mp (Finset.mem_product.mp hb'.1).1
  have hb2 := Finset.mem_range.mp (Finset.mem_product.mp hb'.1).2
  let A : SecantLabel n := ⟨(⟨a.1,ha1⟩,⟨a.2,ha2⟩),ha'.2.1,ha'.2.2.1⟩
  let B : SecantLabel n := ⟨(⟨b.1,hb1⟩,⟨b.2,hb2⟩),hb'.2.1,hb'.2.2.1⟩
  have hA : linearValue (slopeData hn P A) ε ≠ 0 := by
    rw [slopeData_eval]
    exact ha'.2.2.2.2
  have hB : linearValue (slopeData hn P B) ε ≠ 0 := by
    rw [slopeData_eval]
    exact hb'.2.2.2.2
  have hab : A = B := hinj hA hB (by
    dsimp only
    rw [baseData_eval,baseData_eval,slopeData_eval,slopeData_eval]
    exact heq)
  exact congrArg labelNat hab

end
end DirectGLSSW.ExtendedArcCriticalData












