import CanonicalInventoryCoefficient

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart MvPolynomial

theorem jointCarrierPolynomial_eq (n : ℕ) (i : Fin (n+1)) :
    jointCarrierPolynomial n i =
      if h : i.val < n then
        let j : Fin n := ⟨i.val,h⟩
        let v : PlanarPoint (MvPolynomial (JointCoordinates n) ℝ) :=
          (X (.inl (j,0)),X (.inl (j,1)))
        let w : PlanarPoint (MvPolynomial (JointCoordinates n) ℝ) :=
          (X (.inl (cyclicSuccessor j,0)),X (.inl (cyclicSuccessor j,1)))
        (w-v,-planarDet (w-v) v)
      else ((X (.inr 0),X (.inr 1)),X (.inr 2)) := rfl

end DirectGLSSW.CyclicCarrierClearing



