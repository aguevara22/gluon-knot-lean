import OuterChordIncrements

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

def actualOuterTopCells {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :=
  (secantAxisCells T C).filter (fun ab => (1/4 : ℝ)<ab.2 ∧
    ab.2<(componentArcLength D (T.baseArc C).val : ℝ)-1/4)

def actualOuterLeftCells {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :=
  (secantAxisCells T C).filter (fun ab => (1/4 : ℝ)<ab.1 ∧
    ab.1<(componentArcLength D (T.baseArc C).val : ℝ)-1/4)

def actualOuterTopSide {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (ab : ↥(actualOuterTopCells T C)) : RetainedRectangleSide T C :=
  (⟨(ab.val,((componentArcLength D (T.baseArc C).val : ℝ)-1/4,
      (componentArcLength D (T.baseArc C).val : ℝ))),by
    have hm := Finset.mem_filter.mp ab.property
    apply (secantRetainedRectangles_top_row T C ab.val.1 ab.val.2).mpr
    exact ⟨(Finset.mem_filter.mp hm.1).2,hm.2⟩⟩,2)

def actualOuterLeftSide {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (ab : ↥(actualOuterLeftCells T C)) : RetainedRectangleSide T C :=
  (⟨((0,1/4),ab.val),by
    have hm := Finset.mem_filter.mp ab.property
    apply (secantRetainedRectangles_left_column T C ab.val.1 ab.val.2).mpr
    exact ⟨(Finset.mem_filter.mp hm.1).2,hm.2⟩⟩,3)

theorem actualOuterTop_sum_reindex {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter
      (fun e => e.2=2 ∧ e.1.val.2.2=(componentArcLength D (T.baseArc C).val : ℝ)),
      rectangleSideIncrement e) =
    ∑ ab : ↥(actualOuterTopCells T C), Complex.arg
      (basedUniformSecant T C 0 ab.val.1 / basedUniformSecant T C 0 ab.val.2) := by
  have hset : (Finset.univ : Finset ↥(actualOuterTopCells T C)).image (actualOuterTopSide T C)=
      Finset.univ.filter (fun e : RetainedRectangleSide T C => e.2=2 ∧
        e.1.val.2.2=(componentArcLength D (T.baseArc C).val : ℝ)) := by
    ext e
    constructor
    · intro he
      obtain ⟨ab,_,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩
    · intro he
      obtain ⟨hs,hv⟩ := (Finset.mem_filter.mp he).2
      have hc := (retainedRectangle_axis_cells e.1).2
      rw [hv] at hc
      have hu := secantAxisAdjacent_final_endpoint T C e.1.val.2.1 hc
      have hr := e.1.property
      rw [show e.1.val=(e.1.val.1,((componentArcLength D (T.baseArc C).val : ℝ)-1/4,
        (componentArcLength D (T.baseArc C).val : ℝ))) from Prod.ext rfl (Prod.ext hu hv)] at hr
      have hb := (secantRetainedRectangles_top_row T C _ _).mp hr
      let ab : ↥(actualOuterTopCells T C) := ⟨e.1.val.1,Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb.1.1,hb.1.2.1⟩,hb.1⟩,hb.2⟩⟩
      refine Finset.mem_image.mpr ⟨ab,Finset.mem_univ _,?_⟩
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext rfl (Prod.ext hu.symm hv.symm)
      · exact hs.symm
  have hinj : Function.Injective (actualOuterTopSide T C) := by
    intro ab cd he
    apply Subtype.ext
    exact congrArg (fun e : RetainedRectangleSide T C => e.1.val.1) he
  rw [←hset,Finset.sum_image (fun a _ b _ he => hinj he)]
  apply Finset.sum_congr rfl
  intro ab _
  exact rectangleSideIncrement_top_chord T C _ rfl rfl

theorem actualOuterLeft_sum_reindex {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter
      (fun e => e.2=3 ∧ e.1.val.1.1=0),rectangleSideIncrement e) =
    ∑ ab : ↥(actualOuterLeftCells T C), Complex.arg
      (basedUniformSecant T C 0 ab.val.1 / basedUniformSecant T C 0 ab.val.2) := by
  have hset : (Finset.univ : Finset ↥(actualOuterLeftCells T C)).image (actualOuterLeftSide T C)=
      Finset.univ.filter (fun e : RetainedRectangleSide T C => e.2=3 ∧ e.1.val.1.1=0) := by
    ext e
    constructor
    · intro he
      obtain ⟨ab,_,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩
    · intro he
      obtain ⟨hs,ha⟩ := (Finset.mem_filter.mp he).2
      have hc := (retainedRectangle_axis_cells e.1).1
      rw [ha] at hc
      have hb := secantAxisAdjacent_initial_endpoint T C e.1.val.1.2 hc
      have hr := e.1.property
      rw [show e.1.val=((0,1/4),e.1.val.2) from Prod.ext (Prod.ext ha hb) rfl] at hr
      have hu := (secantRetainedRectangles_left_column T C _ _).mp hr
      let ab : ↥(actualOuterLeftCells T C) := ⟨e.1.val.2,Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu.1.1,hu.1.2.1⟩,hu.1⟩,hu.2⟩⟩
      refine Finset.mem_image.mpr ⟨ab,Finset.mem_univ _,?_⟩
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext (Prod.ext ha.symm hb.symm) rfl
      · exact hs.symm
  have hinj : Function.Injective (actualOuterLeftSide T C) := by
    intro ab cd he
    apply Subtype.ext
    exact congrArg (fun e : RetainedRectangleSide T C => e.1.val.2) he
  rw [←hset,Finset.sum_image (fun a _ b _ he => hinj he)]
  apply Finset.sum_congr rfl
  intro ab _
  exact rectangleSideIncrement_left_chord T C _ rfl rfl

theorem actualOuterBoundary_axis_regrouping {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter rectangleExteriorSide,
      rectangleSideIncrement e) =
    (∑ ab : ↥(actualOuterTopCells T C), Complex.arg
      (basedUniformSecant T C 0 ab.val.1 / basedUniformSecant T C 0 ab.val.2)) +
    (∑ ab : ↥(actualOuterLeftCells T C), Complex.arg
      (basedUniformSecant T C 0 ab.val.1 / basedUniformSecant T C 0 ab.val.2)) := by
  rw [←actualOuterTop_sum_reindex,←actualOuterLeft_sum_reindex]
  simp only [Finset.sum_filter]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rcases e with ⟨r,s⟩
  fin_cases s <;> simp [rectangleExteriorSide]

end
end DirectGLSSW.HOMFLY.PrincipalTurning



