import ActualSpatialTrace
import SplitBaseIsolation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY HOMFLY.PrincipalTurning

theorem splitTraversalTime_bounds (m : ℕ) (hm : 0 < m) (t : unitInterval) :
    3/4 ≤ splitTraversalTime m t.val ∧ splitTraversalTime m t.val ≤ (m:ℝ)+1/4 := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : 0 ≤ ((m:ℝ)+1)*t.val := mul_nonneg (by positivity) t.property.1
  have hx1 : ((m:ℝ)+1)*t.val ≤ (m:ℝ)+1 := by nlinarith [t.property.2]
  have hmin0 : 0 ≤ min (max (((m:ℝ)+1)*t.val-1) 0) ((m:ℝ)-1) :=
    le_min (le_max_right _ _) (by linarith)
  have hmin1 := min_le_right (max (((m:ℝ)+1)*t.val-1) 0) ((m:ℝ)-1)
  unfold splitTraversalTime
  constructor <;> linarith

theorem splitBeta_literal_base_parameter (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) :
    splitBeta D e t = Complex.equivRealProd.symm
      (affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e))
        (3/4-t.val/2)) := by
  rw [splitBeta_apply]
  congr 1
  apply Prod.ext <;> simp [splitBaseA, splitBaseB, affinePoint] <;> ring

/-- Actual PL incidence axioms supply avoidance; it is not a source premise. -/
theorem splitMain_avoids_beta (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    splitMainComplex D e t ≠ splitBeta D e t := by
  intro heq
  rw [splitMainComplex_apply, splitBeta_literal_base_parameter] at heq
  have he := Complex.equivRealProd.symm.injective heq
  rw [splitMainPlanar_apply] at he
  let m := componentArcLength D e
  let s := splitTraversalTime m t.val
  let r := (3:ℝ)/4-t.val/2
  have hm : 0 < m := componentArcLength_pos D e
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hb := splitTraversalTime_bounds m hm t
  have hslo : 3/4 ≤ s := hb.1
  have hshi : s ≤ (m:ℝ)+1/4 := hb.2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  change uniformPLCurve D e s = affinePoint _ _ r at he
  by_cases hs : s < (m:ℝ)
  · have he' := uniform_base_interior_preimage D e s r (by linarith) hs hr0 hr1 he
    dsimp [r] at he'
    linarith
  · have hs0 : 0 ≤ s-(m:ℝ) := by linarith
    have hs1 : s-(m:ℝ) < m := by linarith
    have hp : uniformPLCurve D e (s-(m:ℝ)) = uniformPLCurve D e s := by
      have hp := uniformPLCurve_periodic D e (s-(m:ℝ))
      have heq' : s-(m:ℝ)+(m:ℝ)=s := by ring
      rw [heq'] at hp
      exact hp.symm
    have he' := uniform_base_interior_preimage D e (s-m) r hs0 hs1 hr0 hr1 (hp.trans he)
    dsimp [r] at he'
    linarith

end DirectGLSSW.DescendingSpatial



