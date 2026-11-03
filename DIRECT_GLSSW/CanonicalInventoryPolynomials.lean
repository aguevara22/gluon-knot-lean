import CanonicalAugmentedRealization
import AuxiliaryCoefficient

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart MvPolynomial

abbrev JointCoordinates (n : ℕ) := (Fin n × Fin 2) ⊕ Fin 3

def jointVertices {n : ℕ} (x : JointCoordinates n → ℝ) (i : Fin n) : PlanarPoint ℝ :=
  (x (.inl (i,0)), x (.inl (i,1)))
def jointLine {n : ℕ} (x : JointCoordinates n → ℝ) : CarrierLine :=
  ((x (.inr 0),x (.inr 1)),x (.inr 2))
def jointCarrierPolynomial (n : ℕ) (i : Fin (n+1)) :
    (MvPolynomial (JointCoordinates n) ℝ × MvPolynomial (JointCoordinates n) ℝ) ×
      MvPolynomial (JointCoordinates n) ℝ :=
  if h : i.val < n then
    let j : Fin n := ⟨i.val,h⟩
    let v := (X (.inl (j,0)),X (.inl (j,1)))
    let w := (X (.inl (cyclicSuccessor j,0)),X (.inl (cyclicSuccessor j,1)))
    (w-v,-planarDet (w-v) v)
  else ((X (.inr 0),X (.inr 1)),X (.inr 2))

theorem jointVertices_eq {n : ℕ} (x : JointCoordinates n → ℝ) (i : Fin n) :
    jointVertices x i = (x (.inl (i,0)),x (.inl (i,1))) := rfl
theorem jointLine_eq {n : ℕ} (x : JointCoordinates n → ℝ) :
    jointLine x = ((x (.inr 0),x (.inr 1)),x (.inr 2)) := rfl

theorem jointCarrierPolynomial_eval {n : ℕ} (x : JointCoordinates n → ℝ) (i : Fin (n+1)) :
    ((eval x (jointCarrierPolynomial n i).1.1,eval x (jointCarrierPolynomial n i).1.2),
      eval x (jointCarrierPolynomial n i).2) =
    canonicalAugmentedCarrier (jointVertices x) (jointLine x) i := by
  by_cases hi : i.val < n
  · simp [jointCarrierPolynomial,canonicalAugmentedCarrier,hi,polygonCarrierCoordinates,
      cyclicTangent,jointVertices,planarDet]
  · simp [jointCarrierPolynomial,canonicalAugmentedCarrier,hi,jointLine]

theorem exists_joint_denominator_polynomial {n : ℕ} (a b : Fin (n+1)) :
    ∃ P : MvPolynomial (JointCoordinates n) ℝ, ∀ x,
      eval x P = lineDenominator
        (canonicalAugmentedCarrier (jointVertices x) (jointLine x) a)
        (canonicalAugmentedCarrier (jointVertices x) (jointLine x) b) := by
  refine ⟨slotDen (jointCarrierPolynomial n a) (jointCarrierPolynomial n b),?_⟩
  intro x
  rw [← jointCarrierPolynomial_eval x a,← jointCarrierPolynomial_eval x b]
  simp [slotDen,lineDenominator,planarDet]

theorem exists_joint_triple_polynomial {n : ℕ} (a b c d e f : Fin (n+1)) :
    ∃ P : MvPolynomial (JointCoordinates n) ℝ, ∀ x,
      eval x P = carrierTripleNumerator
        (canonicalAugmentedCarrier (jointVertices x) (jointLine x) a)
        (canonicalAugmentedCarrier (jointVertices x) (jointLine x) b)
        (canonicalAugmentedCarrier (jointVertices x) (jointLine x) c)
        (canonicalAugmentedCarrier (jointVertices x) (jointLine x) d)
        (canonicalAugmentedCarrier (jointVertices x) (jointLine x) e)
        (canonicalAugmentedCarrier (jointVertices x) (jointLine x) f) := by
  let A := jointCarrierPolynomial n a
  let B := jointCarrierPolynomial n b
  let C := jointCarrierPolynomial n c
  let D := jointCarrierPolynomial n d
  let E := jointCarrierPolynomial n e
  let F := jointCarrierPolynomial n f
  refine ⟨(slotNum A B).1 * ((slotNum C D).2 * slotDen E F - slotDen C D * (slotNum E F).2) -
    (slotNum A B).2 * ((slotNum C D).1 * slotDen E F - slotDen C D * (slotNum E F).1) +
    slotDen A B * ((slotNum C D).1 * (slotNum E F).2 - (slotNum C D).2 * (slotNum E F).1),?_⟩
  intro x
  rw [← jointCarrierPolynomial_eval x a,← jointCarrierPolynomial_eval x b,
    ← jointCarrierPolynomial_eval x c,← jointCarrierPolynomial_eval x d,
    ← jointCarrierPolynomial_eval x e,← jointCarrierPolynomial_eval x f]
  simp [A,B,C,D,E,F,slotNum,slotDen,carrierTripleNumerator,lineNumerator,lineDenominator,planarDet]

theorem exists_joint_outer_polynomial {m n : ℕ} (f : Fin m → Fin (n+1)) (l : Fin 4 → Fin m) :
    ∃ P : MvPolynomial (JointCoordinates n) ℝ, ∀ x,
      eval x P = outerCycleNumerator (canonicalAugmentedCarrier (jointVertices x) (jointLine x)) f l := by
  refine ⟨outerCycleNumerator (jointCarrierPolynomial n) f l,?_⟩
  intro x
  have hh := fun i => jointCarrierPolynomial_eval x i
  have he : canonicalAugmentedCarrier (jointVertices x) (jointLine x) = fun i =>
      ((eval x (jointCarrierPolynomial n i).1.1,eval x (jointCarrierPolynomial n i).1.2),
        eval x (jointCarrierPolynomial n i).2) := (funext hh).symm
  rw [he]
  simp [outerCycleNumerator,OriginalOuterProperness.outerNumerator,clearedPoints,slotNum,slotDen,
    planarDet,map_prod]

theorem exists_joint_secant_polynomial {m n : ℕ} (f : Fin m → Fin (n+1)) (l : Fin 6 → Fin m) :
    ∃ P : MvPolynomial (JointCoordinates n) ℝ, ∀ x,
      eval x P = secantCycleNumerator (canonicalAugmentedCarrier (jointVertices x) (jointLine x)) f l := by
  refine ⟨secantCycleNumerator (jointCarrierPolynomial n) f l,?_⟩
  intro x
  have hh := fun i => jointCarrierPolynomial_eval x i
  have he : canonicalAugmentedCarrier (jointVertices x) (jointLine x) = fun i =>
      ((eval x (jointCarrierPolynomial n i).1.1,eval x (jointCarrierPolynomial n i).1.2),
        eval x (jointCarrierPolynomial n i).2) := (funext hh).symm
  rw [he]
  simp [secantCycleNumerator,OriginalSecantProperness.secantNumerator,clearedPoints,slotNum,slotDen,
    planarDet,map_prod]

end DirectGLSSW.CyclicCarrierClearing





