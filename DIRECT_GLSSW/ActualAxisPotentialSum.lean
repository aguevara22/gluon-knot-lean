import OuterCellClassification

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact finite telescoping on the actual adjacent-cut cells between two
actual cuts. No partition or telescoping certificate is an input. -/
theorem actualAxis_interval_potential_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (L R : ℝ) (hL : L ∈ secantAxisCuts T C)
    (hR : R ∈ secantAxisCuts T C) (hLR : L<R) (F : ℝ → ℝ) :
    (∑ ab ∈ (secantAxisCells T C).filter (fun ab => L≤ab.1 ∧ ab.2≤R),
      (F ab.2-F ab.1)) = F R-F L := by
  let E := (secantAxisCells T C).filter (fun ab => L≤ab.1 ∧ ab.2≤R)
  let I := (secantAxisCuts T C).filter (fun x => L≤x ∧ x≤R)
  let V := (secantAxisCuts T C).filter (fun x => L<x ∧ x≤R)
  let W := (secantAxisCuts T C).filter (fun x => L≤x ∧ x<R)
  have hcell : ∀ ab ∈ E, secantAxisAdjacent T C ab.1 ab.2 := by
    intro ab hab
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
  have hsnd : E.image Prod.snd=V := by
    ext x
    constructor
    · intro hx
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
      have hc := hcell ab hab
      have hm := (Finset.mem_filter.mp hab).2
      exact Finset.mem_filter.mpr ⟨hc.2.1,by linarith [hc.2.2.1],hm.2⟩
    · intro hx
      obtain ⟨hx,hLx,hxR⟩ := Finset.mem_filter.mp hx
      have hL0 := (secantAxisCuts_bounds T C L hL).1
      obtain ⟨a,ha⟩ := secantAxis_predecessor_exists T C x hx (by linarith)
      have hLa : L≤a := by
        by_contra hn
        exact ha.2.2.2 L hL (lt_of_not_ge hn) hLx
      apply Finset.mem_image.mpr
      refine ⟨(a,x),Finset.mem_filter.mpr ⟨?_,hLa,hxR⟩,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha.1,ha.2.1⟩,ha⟩
  have hfst : E.image Prod.fst=W := by
    ext x
    constructor
    · intro hx
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
      have hc := hcell ab hab
      have hm := (Finset.mem_filter.mp hab).2
      exact Finset.mem_filter.mpr ⟨hc.1,hm.1,by linarith [hc.2.2.1]⟩
    · intro hx
      obtain ⟨hx,hLx,hxR⟩ := Finset.mem_filter.mp hx
      have hRm := (secantAxisCuts_bounds T C R hR).2
      obtain ⟨b,hb⟩ := secantAxis_successor_exists T C x hx (by linarith)
      have hbR : b≤R := by
        by_contra hn
        exact hb.2.2.2 R hR hxR (lt_of_not_ge hn)
      apply Finset.mem_image.mpr
      refine ⟨(x,b),Finset.mem_filter.mpr ⟨?_,hLx,hbR⟩,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb.1,hb.2.1⟩,hb⟩
  have hsndinj : ∀ a ∈ E, ∀ b ∈ E, a.2=b.2 → a=b := by
    intro a ha b hb he
    apply Prod.ext
    · have hc := hcell b hb
      rw [←he] at hc
      exact secantAxisAdjacent_right_unique T C _ _ _ (hcell a ha) hc
    · exact he
  have hfstinj : ∀ a ∈ E, ∀ b ∈ E, a.1=b.1 → a=b := by
    intro a ha b hb he
    apply Prod.ext
    · exact he
    · have hc := hcell b hb
      rw [←he] at hc
      exact secantAxisAdjacent_left_unique T C _ _ _ (hcell a ha) hc
  have hsumV : (∑ ab ∈ E,F ab.2)=∑ x ∈ V,F x := by
    rw [←hsnd,Finset.sum_image hsndinj]
  have hsumW : (∑ ab ∈ E,F ab.1)=∑ x ∈ W,F x := by
    rw [←hfst,Finset.sum_image hfstinj]
  have hIV : insert L V=I := by
    ext x
    simp only [V,I,Finset.mem_insert,Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨hx,hLx,hxR⟩)
      · exact ⟨hL,le_rfl,hLR.le⟩
      · exact ⟨hx,hLx.le,hxR⟩
    · rintro ⟨hx,hLx,hxR⟩
      rcases eq_or_lt_of_le hLx with he | he
      · exact Or.inl he.symm
      · exact Or.inr ⟨hx,he,hxR⟩
  have hIW : insert R W=I := by
    ext x
    simp only [W,I,Finset.mem_insert,Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨hx,hLx,hxR⟩)
      · exact ⟨hR,hLR.le,le_rfl⟩
      · exact ⟨hx,hLx,hxR.le⟩
    · rintro ⟨hx,hLx,hxR⟩
      rcases eq_or_lt_of_le hxR with he | he
      · exact Or.inl he
      · exact Or.inr ⟨hx,hLx,he⟩
  have hLn : L∉V := by simp [V]
  have hRn : R∉W := by simp [W]
  have hsumIV : (∑ x ∈ I,F x)=F L+∑ x ∈ V,F x := by
    rw [←hIV,Finset.sum_insert hLn]
  have hsumIW : (∑ x ∈ I,F x)=F R+∑ x ∈ W,F x := by
    rw [←hIW,Finset.sum_insert hRn]
  change (∑ ab ∈ E,(F ab.2-F ab.1))=F R-F L
  rw [Finset.sum_sub_distrib,hsumV,hsumW]
  linarith

end
end DirectGLSSW.HOMFLY.PrincipalTurning

