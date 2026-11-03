import PolygonRebaseEventOrder
import OrderedBlockRotation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

theorem eventEquiv_successor (x : PolygonEvent (q ∘ ρ)) :
    eventEquiv q ρ hρ
        (polygonEventSuccessor (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq).g2 x) =
      polygonEventSuccessor q hq.g2 (eventEquiv q ρ hρ x) := by
  let hQ := cyclicGeneric_relabel q ρ hρ hq
  letI := polygonEventOrder (q ∘ ρ) hQ.g2
  letI := polygonEventOrder q hq.g2
  let a : PolygonEvent (q ∘ ρ) := Sum.inl (ρ.symm ⟨0,by have := hq.size_ge_three;omega⟩)
  exact (orderedCyclicSuccessor_naturality_of_block_rotation (eventEquiv q ρ hρ) a
    (event_order_cut q hq ρ hρ) x).symm

end DirectGLSSW.PolygonRebase
