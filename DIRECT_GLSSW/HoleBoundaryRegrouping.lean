import HoleWitnessReverse
import HoleSideInjectivity
import HoleClockwiseBalance

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem crossingHole_retainedBoundary_regrouping {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v)
    : (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter
        (rectangleTouchesCrossingHole T C c i j), rectangleSideIncrement e) =
      -crossingHoleGridBoundarySum T C c i j := by
  let labels : Finset (Fin 2 × Fin 2 × Fin 4) :=
    (Finset.univ.product (Finset.univ.product Finset.univ)).filter
      (fun z => crossingHoleGridExterior z.1 z.2.1 z.2.2)
  let side : (Fin 2 × Fin 2 × Fin 4) → RetainedRectangleSide T C := fun z =>
    crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv z.1 z.2.1 z.2.2
  have hset : labels.image side = Finset.univ.filter (rectangleTouchesCrossingHole T C c i j) := by
    ext e
    constructor
    · intro he
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      exact crossingHoleOutsideSide_touches T C c i j hij hi hj horder a b u v ha hb hu hv
        z.1 z.2.1 z.2.2 (Finset.mem_filter.mp hz).2
    · intro he
      obtain ⟨h,k,s,hext,heq⟩ := rectangleTouchesCrossingHole_witness T C c i j hij hi hj horder
        a b u v ha hb hu hv e (Finset.mem_filter.mp he).2
      apply Finset.mem_image.mpr
      refine ⟨(h,k,s),?_,heq.symm⟩
      simp [labels,hext]
  have hinj : ∀ z ∈ labels, ∀ z' ∈ labels, side z=side z' → z=z' := by
    intro z hz z' hz' he
    have hh := crossingHoleOutsideSide_injective T C c i j hij hi hj horder a b u v ha hb hu hv
      z.1 z.2.1 z'.1 z'.2.1 z.2.2 z'.2.2 (Finset.mem_filter.mp hz).2 (Finset.mem_filter.mp hz').2 he
    exact Prod.ext hh.1 (Prod.ext hh.2.1 hh.2.2)
  rw [←hset,Finset.sum_image hinj]
  have hsum : (∑ z ∈ labels, rectangleSideIncrement (side z)) =
      crossingHoleClockwiseSideSum T C c i j hij hi hj horder a b u v ha hb hu hv := by
    simp only [labels,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product,side,crossingHoleClockwiseSideSum]
  rw [hsum,crossingHoleClockwiseSideSum_eq_negative]

end
end DirectGLSSW.HOMFLY.PrincipalTurning

