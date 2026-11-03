import PolygonRebaseEvents
import PolygonRebaseLabelOrder

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

theorem event_order_cut (x y : PolygonEvent (q ∘ ρ)) :
    let hQ := cyclicGeneric_relabel q ρ hρ hq
    letI := polygonEventOrder (q ∘ ρ) hQ.g2
    letI := polygonEventOrder q hq.g2
    let a : PolygonEvent (q ∘ ρ) := Sum.inl (ρ.symm ⟨0,by have := hq.size_ge_three;omega⟩)
    eventEquiv q ρ hρ x < eventEquiv q ρ hρ y ↔
      (a ≤ x ∧ y < a) ∨ ((x < a ↔ y < a) ∧ x < y) := by
  let hn : 0 < n := by have := hq.size_ge_three;omega
  let hQ := cyclicGeneric_relabel q ρ hρ hq
  letI := polygonEventOrder (q ∘ ρ) hQ.g2
  letI := polygonEventOrder q hq.g2
  let cut : Fin n := ρ.symm ⟨0,hn⟩
  let a : PolygonEvent (q ∘ ρ) := Sum.inl cut
  have hlt : ∀ z : PolygonEvent (q ∘ ρ), z < a ↔ polygonEventEdge (q ∘ ρ) z < cut := by
    intro z
    rw [polygonEvent_lt_iff (q ∘ ρ) hQ.g2]
    have hp := (polygonEventParameter_bounds (q ∘ ρ) z).1
    change (_ < cut ∨ _ = cut ∧ polygonEventParameter (q ∘ ρ) z < 0) ↔ _
    simp only [not_lt.mpr hp,and_false,or_false]
  have hge : ∀ z : PolygonEvent (q ∘ ρ), a ≤ z ↔ cut ≤ polygonEventEdge (q ∘ ρ) z := by
    intro z
    simpa only [not_lt] using (not_congr (hlt z))
  change eventEquiv q ρ hρ x < eventEquiv q ρ hρ y ↔
      (a ≤ x ∧ y < a) ∨ ((x < a ↔ y < a) ∧ x < y)
  rw [polygonEvent_lt_iff q hq.g2,eventEquiv_edge,eventEquiv_edge,
    eventEquiv_parameter q ρ hρ hq,eventEquiv_parameter q ρ hρ hq,
    label_order_cut ρ hρ hn]
  simp only [hge,hlt,ρ.injective.eq_iff]
  rw [polygonEvent_lt_iff (q ∘ ρ) hQ.g2]
  constructor
  · intro h
    rcases h with h | ⟨he,hp⟩
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1,Or.inl h.2⟩
    · exact Or.inr ⟨by rw [he],Or.inr ⟨he,hp⟩⟩
  · rintro (h | ⟨h,hxy | hxy⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨h,hxy⟩)
    · exact Or.inr hxy

end DirectGLSSW.PolygonRebase
