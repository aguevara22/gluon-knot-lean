import ActiveArcSuffix
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split

/-- Removing an actual initial physical prefix cannot create a crossing. -/
theorem suffix_crossing_count_le {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) :
    Fintype.card (Crossing (suffix q)) ≤ Fintype.card (Crossing q) := by
  classical
  exact Fintype.card_le_of_injective (suffixCrossingToOriginal q)
    (suffixCrossingToOriginal_injective q)

/-- The literal corner successor (q₁,q₂,…) is Regular, cannot increase actual
crossing count, and has exactly one fewer endpoint-inclusive vertex. This is
only the geometric descent data, not a current or support-transport identity. -/
theorem corner_suffix_descent {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q) :
    Regular (suffix (a:=1) (b:=b) q) ∧
      Fintype.card (Crossing (suffix (a:=1) (b:=b) q)) ≤ Fintype.card (Crossing q) ∧
      Fintype.card (Fin (b+2))+1=Fintype.card (Fin (1+b+2)) := by
  refine ⟨regular_suffix q hR,suffix_crossing_count_le q,?_⟩
  simp only [Fintype.card_fin]
  omega
end DirectGLSSW.ActiveArc.Split
