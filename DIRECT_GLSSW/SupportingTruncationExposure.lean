import SupportingCornerScale
import DirectGLSSW.TruncationPointGeometry
import DirectGLSSW.TruncationCommonRadius
import ExposedEdgeGeometry
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.TruncationDirection
open ShortEdgeCyclicAdapter ShortEdgeCutFibers TruncationCommonRadius ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- Strict support at the original corner yields actual exposure of the new
short side for every sufficiently small positive member of the literal family. -/
theorem exists_small_truncation_leftExposed {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale : ℝ)
    (hsupport : ∀ x : Fin n, x ≠ a →
      0 < planarDet (scale • (q (cyclicSuccessor a)-q a)-(q p-q a)) (q x-q a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      LeftExposed (truncateCyclicCorner q a p scale ε) a.castSucc := by
  let v := scale • (q (cyclicSuccessor a)-q a)-(q p-q a)
  let B := planarDet v (q p-q a)
  let r : Fin n → ℝ := fun x => if x=a then 1 else planarDet v (q x-q a) / (|B|+1)
  have hr : ∀x, 0<r x := by
    intro x
    by_cases hx : x=a
    · simp [r,hx]
    · simp only [r,if_neg hx]
      exact div_pos (hsupport x hx) (by positivity)
  obtain ⟨δ,hδ,hbound⟩ := exists_positive_common_lower_bound r hr
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ i hi his
  have hia : collapseFin a i ≠ a := by
    intro he
    rcases (collapseFin_eq_a_iff a i).mp he with h0|h1
    · exact hi h0
    · exact his (h1.trans (cyclicSuccessor_shortEdge a).symm)
  have heps : ε < planarDet v (q (collapseFin a i)-q a) / (|B|+1) := by
    have hb := lt_of_lt_of_le hεδ (hbound (collapseFin a i))
    simpa only [r,if_neg hia] using hb
  have hden : 0 < |B|+1 := by positivity
  have hmul := (lt_div_iff₀ hden).mp heps
  have hinner : 0 < planarDet v (q (collapseFin a i)-q a)-ε*B := by
    have habs := le_abs_self B
    nlinarith
  have hanchor : truncateCyclicCorner q a p scale ε a.castSucc = q a+ε • (q p-q a) :=
    truncateCyclicCorner_anchor q a p scale ε
  have htangent : cyclicTangent (truncateCyclicCorner q a p scale ε) a.castSucc = ε • v := by
    rw [cyclicTangent,cyclicSuccessor_shortEdge,truncateCyclicCorner_new,hanchor]
    ext <;> simp [v,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  rw [htangent,truncateCyclicCorner_of_collapse_ne q a p scale ε i hia,hanchor]
  have heq : planarDet (ε • v) (q (collapseFin a i)-(q a+ε • (q p-q a))) =
      ε*(planarDet v (q (collapseFin a i)-q a)-ε*B) := by
    simp [B,planarDet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  rw [heq]
  exact mul_pos hε hinner
end DirectGLSSW.TruncationDirection
