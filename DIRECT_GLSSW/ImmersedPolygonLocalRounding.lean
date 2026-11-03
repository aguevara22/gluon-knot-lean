import ImmersedPolygonTurnInteger
import ImmersedBezierCorner

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.ImmersedPolygonRotation

/-- The unique total-turn integer and the actual local Bezier tangent
interpretation on every corner of a cyclic immersed polygon. This is a local
rounding theorem: no global curve or rotation definition is introduced. -/
theorem existsUnique_integer_with_local_rounding
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃! r : ℤ, originalCornerTotalTurn q = (r:ℝ)*(2*Real.pi) ∧
      ∀ i : Fin n,
        let v := polygonEdgeVector q ((cyclicSuccessorPerm n).symm i)
        let w := polygonEdgeVector q i
        (∀ t : I,
          HasDerivAt (fun x : ℝ => Complex.equivRealProd.symm (q i) +
            δ • ((-((1-x)^2)) • v + x^2 • w))
            ((2*δ) • ((1-t.val) • v + t.val • w)) t.val ∧
          (2*δ) • ((1-t.val) • v + t.val • w) ≠ 0) ∧
        ∃ θ : C(I,ℝ),
          (∀ t : I, (θ t : Real.Angle) =
            (Complex.arg ((2*δ) • ((1-t.val) • v + t.val • w)) : Real.Angle)) ∧
          θ 0 = v.arg ∧ θ 1 - θ 0 = originalCornerTurn q i ∧
          -Real.pi < θ 1 - θ 0 ∧ θ 1 - θ 0 < Real.pi := by
  obtain ⟨r,hr,hunique⟩ := originalCornerTotalTurn_existsUnique_integer_of_edges q hedge
  refine ⟨r,⟨hr,?_⟩,?_⟩
  · intro i
    dsimp only
    constructor
    · intro t
      exact ⟨bezier_corner_hasDerivAt _ _ _ δ t.val,
        bezier_corner_regular _ _ (hedge _) (hshort i) δ t.val hδ t.property⟩
    · exact exists_bezier_tangent_lift _ _ (hedge _) (hshort i) δ hδ
  · intro s hs
    exact hunique s hs.1

end DirectGLSSW.HOMFLY.PolygonDrawingBridge

