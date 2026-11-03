import PolygonRebaseEvents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
open HOMFLY HOMFLY.PolygonDrawingBridge HOMFLY.PolygonDrawing
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

def branchFin (c : PolygonCrossing (q ∘ ρ)) : Equiv.Perm (Fin 2) :=
  if ρ c.val.1 < ρ c.val.2 then Equiv.refl _ else Equiv.swap 0 1

theorem eventEquiv_visit (c : PolygonCrossing (q ∘ ρ)) (i : Fin 2) :
    eventEquiv q ρ hρ (visit (q ∘ ρ) c i) =
      visit q (crossingEquiv q ρ hρ c) (branchFin q ρ c i) := by
  have hinr (v : CrossingVisit (q ∘ ρ)) :
      eventEquiv q ρ hρ (Sum.inr v) = Sum.inr (visitEquiv q ρ hρ v) := rfl
  fin_cases i <;> by_cases ho : ρ c.val.1 < ρ c.val.2 <;>
    simp only [visit, Fin.isValue, ↓reduceIte, hinr] <;>
    simp [visitEquiv,branchBool,branchFin,visit,ho]

theorem branchFin_over (hq : CyclicGeneric q) (c : PolygonCrossing (q ∘ ρ)) :
    branchFin q ρ c
      ((positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).overBranch
        (crossingFin (q ∘ ρ) c)) =
      (positivePolygonEventDiagram q hq).overBranch
        (crossingFin q (crossingEquiv q ρ hρ c)) := by
  rw [positivePolygonEventDiagram_overBranch,positivePolygonEventDiagram_overBranch]
  rw [tangent_relabel q ρ hρ,tangent_relabel q ρ hρ]
  by_cases ho : ρ c.val.1 < ρ c.val.2
  · simp [branchFin,crossingEquiv,crossingMap,ho]
  · have hn := crossing_transverse (cyclicGeneric_relabel q ρ hρ hq).size_ge_three
      (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq).g1 c
    rw [tangent_relabel q ρ hρ,tangent_relabel q ρ hρ] at hn
    have hs : planarDet (cyclicTangent q (ρ c.val.2)) (cyclicTangent q (ρ c.val.1)) =
        -planarDet (cyclicTangent q (ρ c.val.1)) (cyclicTangent q (ρ c.val.2)) :=
      planarDet_swap _ _
    by_cases hd : 0 < planarDet (cyclicTangent q (ρ c.val.1)) (cyclicTangent q (ρ c.val.2))
    · have hr : ¬ 0 < -planarDet (cyclicTangent q (ρ c.val.1)) (cyclicTangent q (ρ c.val.2)) :=
        not_lt.mpr (le_of_lt (neg_neg_of_pos hd))
      simp [branchFin,crossingEquiv,crossingMap,ho,hd,hs,hr]
    · have hl : planarDet (cyclicTangent q (ρ c.val.1)) (cyclicTangent q (ρ c.val.2)) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hd) hn
      have hr := neg_pos.mpr hl
      simp [branchFin,crossingEquiv,crossingMap,ho,hd,hs,hr]

end DirectGLSSW.PolygonRebase
