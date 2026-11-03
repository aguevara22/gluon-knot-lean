import PolygonRebaseCrossings

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

def branchBool (c : PolygonCrossing (q ∘ ρ)) : Equiv.Perm Bool :=
  if ρ c.val.1 < ρ c.val.2 then Equiv.refl _ else
    ⟨Bool.not,Bool.not,fun b => Bool.not_not b,fun b => Bool.not_not b⟩

def visitEquiv : CrossingVisit (q ∘ ρ) ≃ CrossingVisit q where
  toFun v := (crossingEquiv q ρ hρ v.1,branchBool q ρ v.1 v.2)
  invFun v := ((crossingEquiv q ρ hρ).symm v.1,
    (branchBool q ρ ((crossingEquiv q ρ hρ).symm v.1)).symm v.2)
  left_inv := by
    rintro ⟨c,b⟩
    dsimp only
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨c,b⟩
    dsimp only
    simp only [Equiv.apply_symm_apply]

theorem visitEquiv_edge (v : CrossingVisit (q ∘ ρ)) :
    crossingVisitEdge q (visitEquiv q ρ hρ v) = ρ (crossingVisitEdge (q ∘ ρ) v) := by
  rcases v with ⟨c,b⟩
  cases b <;> by_cases ho : ρ c.val.1 < ρ c.val.2 <;>
    simp [visitEquiv,crossingEquiv,crossingMap,branchBool,crossingVisitEdge,ho]

theorem visitEquiv_point (hq : CyclicGeneric q) (v : CrossingVisit (q ∘ ρ)) :
    crossingVisitPoint q (visitEquiv q ρ hρ v) = crossingVisitPoint (q ∘ ρ) v := by
  symm
  have hl := (edgeInterior_relabel q ρ hρ _ _).mp (crossingPoint_mem_left (q ∘ ρ) v.1)
  have hr := (edgeInterior_relabel q ρ hρ _ _).mp (crossingPoint_mem_right (q ∘ ρ) v.1)
  apply crossingPoint_eq_of_mem hq.size_ge_three q hq.g1
  · change edgeInterior q (crossingMap q ρ hρ v.1).val.1 _
    rcases crossingMap_carriers q ρ hρ v.1 with hh | hh
    · rw [hh];exact hl
    · rw [hh];exact hr
  · change edgeInterior q (crossingMap q ρ hρ v.1).val.2 _
    rcases crossingMap_carriers q ρ hρ v.1 with hh | hh
    · rw [hh];exact hr
    · rw [hh];exact hl

theorem visitEquiv_parameter (hq : CyclicGeneric q) (v : CrossingVisit (q ∘ ρ)) :
    crossingVisitParameter q (visitEquiv q ρ hρ v) = crossingVisitParameter (q ∘ ρ) v := by
  have hp := crossingVisitParameter_spec q (visitEquiv q ρ hρ v)
  have hqv := crossingVisitParameter_spec (q ∘ ρ) v
  have ha : q (ρ (crossingVisitEdge (q ∘ ρ) v)) ≠
      q (cyclicSuccessor (ρ (crossingVisitEdge (q ∘ ρ) v))) := by
    apply (cyclicNoncollinear_injective hq.size_ge_three q hq.g1).ne
    exact (cyclicSuccessor_ne_self (Nat.le_trans (by decide : 2 ≤ 3) hq.size_ge_three) _).symm
  apply affinePoint_injective _ _ ha
  rw [visitEquiv_edge] at hp
  rw [← hp.2.2,visitEquiv_point q ρ hρ hq v]
  simpa only [Function.comp_apply,hρ] using hqv.2.2

def eventEquiv : PolygonEvent (q ∘ ρ) ≃ PolygonEvent q :=
  Equiv.sumCongr ρ (visitEquiv q ρ hρ)

theorem eventEquiv_edge (x : PolygonEvent (q ∘ ρ)) :
    polygonEventEdge q (eventEquiv q ρ hρ x) = ρ (polygonEventEdge (q ∘ ρ) x) := by
  cases x with
  | inl e => rfl
  | inr v => exact visitEquiv_edge q ρ hρ v

theorem eventEquiv_parameter (hq : CyclicGeneric q) (x : PolygonEvent (q ∘ ρ)) :
    polygonEventParameter q (eventEquiv q ρ hρ x) = polygonEventParameter (q ∘ ρ) x := by
  cases x with
  | inl e => rfl
  | inr v => exact visitEquiv_parameter q ρ hρ hq v

theorem eventEquiv_point (hq : CyclicGeneric q) (x : PolygonEvent (q ∘ ρ)) :
    polygonEventPoint q (eventEquiv q ρ hρ x) = polygonEventPoint (q ∘ ρ) x := by
  cases x with
  | inl e => rfl
  | inr v => exact visitEquiv_point q ρ hρ hq v

end DirectGLSSW.PolygonRebase
