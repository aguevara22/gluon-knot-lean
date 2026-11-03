import RetainedSecantTriangleBalance
import EdgeCancellation

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- SOURCE-PREPARED, UNCOMPILED: actual rectangle boundary consumer. -/
theorem retainedSecantRectangle_angle_zero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v : ℝ)
    (hr : ((a,b),(u,v)) ∈ secantRetainedRectangles T C) :
    Complex.arg (basedUniformSecant T C b u / basedUniformSecant T C a u)+
      Complex.arg (basedUniformSecant T C b v / basedUniformSecant T C b u)+
      Complex.arg (basedUniformSecant T C a v / basedUniformSecant T C b v)+
      Complex.arg (basedUniformSecant T C a u / basedUniformSecant T C a v)=0 := by
  classical
  have hc := Finset.mem_product.mp (Finset.mem_filter.mp hr).1
  have h1 : secantAxisAdjacent T C a b := (Finset.mem_filter.mp hc.1).2
  have h2 : secantAxisAdjacent T C u v := (Finset.mem_filter.mp hc.2).2
  have ha : a ∈ Set.Icc a b := ⟨le_rfl,h1.2.2.1.le⟩
  have hb : b ∈ Set.Icc a b := ⟨h1.2.2.1.le,le_rfl⟩
  have hu : u ∈ Set.Icc u v := ⟨le_rfl,h2.2.2.1.le⟩
  have hv : v ∈ Set.Icc u v := ⟨h2.2.2.1.le,le_rfl⟩
  have hfirst := retainedSecantTriangle_angle_zero T C a b u v a b b u u v hr ha hb hb hu hu hv
  have hsecond := retainedSecantTriangle_angle_zero T C a b u v a b a u v v hr ha hb ha hu hv hv
  have hdiag : (0 : ℂ) ∉ segment ℝ (basedUniformSecant T C a u) (basedUniformSecant T C b v) := by
    intro hz
    exact (retainedSecantTriangle_origin_excluded T C a b u v a b b u v u hr ha hb hb hu hv hu)
      (origin_triangle_of_segment _ _ _ hz)
  have hreverse := segment_arg_reverse _ _ hdiag
  linarith

end DirectGLSSW.HOMFLY.PrincipalTurning

