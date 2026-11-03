import DiagonalSideFlatClassification

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The entire literal diagonal staircase contribution is the actual sum
of the source component's principal turns. All other staircase sides are flat. -/
theorem actualComponent_diagonalBoundary_regrouping {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter
      rectangleDiagonalNeighbour, rectangleSideIncrement e) =
    ∑ k : Fin (componentArcLength D (T.baseArc C).val),
      turn D ((D.continuation ^ (k.val : ℤ)) (T.baseArc C).val) := by
  let selected := (Finset.univ : Finset
    (Fin (componentArcLength D (T.baseArc C).val) × Fin 2)).image (actualDiagonalVertexSide T C)
  let diagonal := (Finset.univ : Finset (RetainedRectangleSide T C)).filter rectangleDiagonalNeighbour
  have hsub : selected ⊆ diagonal := by
    intro e he
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,actualDiagonalVertexSide_diagonal T C x⟩
  have hzero : ∀ e ∈ diagonal, e ∉ selected → rectangleSideIncrement e=0 := by
    intro e he hn
    rcases rectangleDiagonalNeighbour_vertex_or_zero T C e (Finset.mem_filter.mp he).2 with hex | hz
    · obtain ⟨x,hx⟩ := hex
      exact False.elim (hn (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx.symm⟩))
    · exact hz
  have hsum : (∑ e ∈ diagonal,rectangleSideIncrement e) = ∑ e ∈ selected,rectangleSideIncrement e :=
    (Finset.sum_subset hsub hzero).symm
  change (∑ e ∈ diagonal,rectangleSideIncrement e)=_
  rw [hsum]
  unfold selected
  rw [Finset.sum_image (fun x _ y _ h => actualDiagonalVertexSide_injective T C h)]
  rw [←Finset.univ_product_univ]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k _
  exact actualDiagonalVertexSide_pair_sum T C k

end
end DirectGLSSW.HOMFLY.PrincipalTurning

