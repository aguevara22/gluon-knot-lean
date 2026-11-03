import ActiveArcClosedChildGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)

def childCrossingToOriginal (d : PolygonCrossing (child q hR c hfirst hcut)) : Crossing q :=
  ⟨(childEdge d.val.1,childEdge d.val.2),d.property.1,by
    obtain ⟨x,hx,hy⟩:=d.property.2
    exact ⟨x,child_edge_subset q hR c hfirst hcut _ x hx,
      child_edge_subset q hR c hfirst hcut _ x hy⟩⟩

theorem childCrossingToOriginal_injective : Function.Injective (childCrossingToOriginal q hR c hfirst hcut) := by
  intro d e h;apply Subtype.ext;apply Prod.ext
  · apply childEdge_injective;exact congrArg (fun z : Crossing q => z.val.1) h
  · apply childEdge_injective;exact congrArg (fun z : Crossing q => z.val.2) h

theorem childCrossingToOriginal_point (d : PolygonCrossing (child q hR c hfirst hcut)) :
    crossingPoint q (childCrossingToOriginal q hR c hfirst hcut d)=
      DirectGLSSW.crossingPoint (child q hR c hfirst hcut) d :=
  crossingPoint_eq_of_mem_regular q hR _ _
    (child_edge_subset q hR c hfirst hcut _ _ (DirectGLSSW.crossingPoint_mem_left _ d))
    (child_edge_subset q hR c hfirst hcut _ _ (DirectGLSSW.crossingPoint_mem_right _ d))

/-- Both physical visits lie in the literal interval child; boundary inequalities
remove exactly the portions omitted from first and closing physical edges. -/
def InChild (d : Crossing q) : Prop :=
  d.val.2.val≤a ∧ (d.val.1=0 → leftParameter q c<leftParameter q d) ∧
    (d.val.2.val=a → rightParameter q d<rightParameter q c)

theorem childCrossingToOriginal_inChild (d : PolygonCrossing (child q hR c hfirst hcut)) :
    InChild q c (childCrossingToOriginal q hR c hfirst hcut d) := by
  constructor
  · change d.val.2.val≤a;have hh:=d.val.2.isLt;omega
  constructor
  · intro hd
    have hd0 : d.val.1=0 := by apply Fin.ext;have hv:=congrArg (fun x : Fin (a+b+1) => x.val) hd;exact hv
    have hx:=DirectGLSSW.crossingPoint_mem_left (child q hR c hfirst hcut) d
    rw [hd0] at hx
    obtain ⟨s,hs0,hs1,hx⟩:=(child_first_edge q hR c hfirst hcut _).mp hx
    have heq : leftParameter q (childCrossingToOriginal q hR c hfirst hcut d)=s := by
      apply edge_parameter_unique q hR 0
      have hp:=(leftParameter_spec q (childCrossingToOriginal q hR c hfirst hcut d)).2.2
      rw [hd,childCrossingToOriginal_point q hR c hfirst hcut] at hp
      exact hp.symm.trans hx
    rw [heq];exact hs0
  · intro hd
    have hx:=DirectGLSSW.crossingPoint_mem_right (child q hR c hfirst hcut) d
    obtain ⟨s,hs0,hs1,hx⟩:=(child_last_edge q hR c hfirst hcut d.val.2 hd _).mp hx
    have he : (childCrossingToOriginal q hR c hfirst hcut d).val.2=c.val.2 := by
      apply Fin.ext;exact hd.trans hcut.symm
    have heq : rightParameter q (childCrossingToOriginal q hR c hfirst hcut d)=s := by
      apply edge_parameter_unique q hR c.val.2
      have hp:=(rightParameter_spec q (childCrossingToOriginal q hR c hfirst hcut d)).2.2
      rw [he,childCrossingToOriginal_point q hR c hfirst hcut] at hp
      exact hp.symm.trans hx
    rw [heq];exact hs1

theorem childCrossing_range (d : Crossing q) :
    (∃ e, childCrossingToOriginal q hR c hfirst hcut e=d) ↔ InChild q c d := by
  constructor
  · rintro ⟨e,rfl⟩;exact childCrossingToOriginal_inChild q hR c hfirst hcut e
  · intro hd
    let e : Fin (a+1) := ⟨d.val.1.val,by have hh:=d.property.1;have hb:=hd.1;omega⟩
    let f : Fin (a+1) := ⟨d.val.2.val,by have hb:=hd.1;omega⟩
    have he : childEdge (b:=b) e=d.val.1 := rfl
    have hf : childEdge (b:=b) f=d.val.2 := rfl
    have hef : e<f := d.property.1
    have hea : e.val<a := by have hh:=d.property.1;have hb:=hd.1;dsimp [e];omega
    have hf0 : f≠0 := by
      intro hh;have hv:=congrArg Fin.val hh;dsimp [f] at hv
      have ho:=d.property.1;have hz : (0 : Fin (a+1)).val=0 := rfl;omega
    have hx : DirectGLSSW.edgeInterior (child q hR c hfirst hcut) e (crossingPoint q d) := by
      by_cases he0 : e=0
      · rw [he0,child_first_edge q hR c hfirst hcut]
        have hd0 : d.val.1=0 := by rw [← he,he0];rfl
        exact ⟨leftParameter q d,hd.2.1 hd0,(leftParameter_spec q d).2.1,by
          simpa only [hd0] using (leftParameter_spec q d).2.2⟩
      · apply (child_middle_edge q hR c hfirst hcut e he0 hea _).mpr
        exact (crossingPoint_mem q d).1
    have hy : DirectGLSSW.edgeInterior (child q hR c hfirst hcut) f (crossingPoint q d) := by
      by_cases hfa : f.val=a
      · apply (child_last_edge q hR c hfirst hcut f hfa _).mpr
        have hdf : d.val.2=c.val.2 := by apply Fin.ext;exact hfa.trans hcut.symm
        exact ⟨rightParameter q d,(rightParameter_spec q d).1,hd.2.2 hfa,by
          simpa only [hdf] using (rightParameter_spec q d).2.2⟩
      · have hfa' : f.val<a := by have hh:=f.isLt;omega
        apply (child_middle_edge q hR c hfirst hcut f hf0 hfa' _).mpr
        exact (crossingPoint_mem q d).2
    let z : PolygonCrossing (child q hR c hfirst hcut) := ⟨(e,f),hef,crossingPoint q d,hx,hy⟩
    exact ⟨z,Subtype.ext (Prod.ext he hf)⟩

/-- Actual closed-child polygon crossings correspond to original labels in its
physical interval. No cyclic G1 or auxiliary amplitude premise is assumed. -/
def childCrossingEquiv : PolygonCrossing (child q hR c hfirst hcut) ≃ {d : Crossing q // InChild q c d} :=
  Equiv.ofBijective (fun e => ⟨childCrossingToOriginal q hR c hfirst hcut e,
    childCrossingToOriginal_inChild q hR c hfirst hcut e⟩) ⟨by
    intro d e h;exact childCrossingToOriginal_injective q hR c hfirst hcut (congrArg Subtype.val h),by
    intro d
    obtain ⟨e,he⟩:=(childCrossing_range q hR c hfirst hcut d.val).mpr d.property
    exact ⟨e,Subtype.ext he⟩⟩

include hfirst in
theorem crossing_not_inChild : ¬ InChild q c c := by
  intro h
  exact (lt_irrefl _) (h.2.1 hfirst)

theorem child_parent_disjoint (d : Crossing q) : ¬ (InChild q c d ∧ InParent q c d) := by
  rintro ⟨hd,hp⟩
  have hlt:=d.property.1
  have h1:=hd.1
  have h2:=hp.1
  change d.val.1.val<d.val.2.val at hlt
  omega

end DirectGLSSW.ActiveArc.Split
