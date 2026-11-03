import ActiveArcParentParameters
import ActiveArcFirstCrossing
import DirectGLSSW.PolygonCrossings

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)

def childVertex (i : Fin (a+1)) : Fin (a+b+2) := ⟨i.val,by omega⟩
def childEdge (e : Fin (a+1)) : Fin (a+b+1) := ⟨e.val,by omega⟩

/-- Literal closed child (c,q₁,...,qₐ). Its cyclic closing edge is the
physical prefix qₐ→c of the crossed original edge, not an artificial seam. -/
def child (_hR : Regular q) (c : Crossing q) (_hfirst : c.val.1=0) (_hcut : c.val.2.val=a) :
    Fin (a+1) → PlanarPoint ℝ :=
  Function.update (fun i => q (childVertex i)) 0 (crossingPoint q c)

@[simp] theorem child_zero (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a) :
    child q hR c hfirst hcut 0=crossingPoint q c := by simp [child]

theorem child_nonzero (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
    (i : Fin (a+1)) (hi : i≠0) : child q hR c hfirst hcut i=q (childVertex i) :=
  Function.update_of_ne hi _ _

theorem childEdge_injective : Function.Injective (childEdge (a:=a) (b:=b)) := by
  intro e f h;apply Fin.ext;have hh:=congrArg (fun x : Fin (a+b+1) => x.val) h;exact hh

theorem cut_positive (c : Crossing q) (hcut : c.val.2.val=a) : 0<a := by
  have hh:=c.property.1;change c.val.1.val<c.val.2.val at hh;omega

theorem child_successor_val (e : Fin (a+1)) (he : e.val<a) :
    (cyclicSuccessor e).val=e.val+1 := by
  simp only [cyclicSuccessor,cyclicVertexIndex_val e (by omega : 0<a+1)]
  split_ifs <;> omega

theorem child_last_successor (e : Fin (a+1)) (he : e.val=a) : cyclicSuccessor e=0 := by
  apply Fin.ext
  simp only [cyclicSuccessor,cyclicVertexIndex_val e (by omega : 0<a+1),Fin.val_zero]
  split_ifs <;> omega

theorem child_middle_edge (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
    (e : Fin (a+1)) (he0 : e≠0) (hea : e.val<a) (x : PlanarPoint ℝ) :
    DirectGLSSW.edgeInterior (child q hR c hfirst hcut) e x ↔
      ActiveArc.edgeInterior q (childEdge e) x := by
  have hs:=child_successor_val e hea
  have hs0 : cyclicSuccessor e≠0 := by intro hh;have hv:=congrArg Fin.val hh;simp only [Fin.val_zero] at hv;omega
  have hstart : childVertex (b:=b) e=(childEdge (b:=b) e).castSucc := rfl
  have hend : childVertex (b:=b) (cyclicSuccessor e)=(childEdge (b:=b) e).succ := by
    apply Fin.ext;exact hs
  simp only [DirectGLSSW.edgeInterior,OnOpenSegment,ActiveArc.edgeInterior,
    child_nonzero q hR c hfirst hcut e he0,child_nonzero q hR c hfirst hcut _ hs0,hstart,hend]

theorem child_first_edge (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
    (x : PlanarPoint ℝ) :
    DirectGLSSW.edgeInterior (child q hR c hfirst hcut) 0 x ↔
      ∃ s : ℝ, leftParameter q c<s ∧ s<1 ∧ x=affinePoint (q 0) (q 1) s := by
  have ha:=cut_positive q c hcut
  have hs:=child_successor_val (0 : Fin (a+1)) (by simpa using ha)
  have hs0 : cyclicSuccessor (0 : Fin (a+1))≠0 := by intro hh;have hv:=congrArg Fin.val hh;simp only [Fin.val_zero] at hv;omega
  have hv : childVertex (b:=b) (cyclicSuccessor (0 : Fin (a+1)))=(1 : Fin (a+b+2)) := by
    apply Fin.ext;exact hs
  have hp : crossingPoint q c=affinePoint (q 0) (q 1) (leftParameter q c) := by
    simpa only [hfirst] using (leftParameter_spec q c).2.2
  change OnOpenSegment (child q hR c hfirst hcut 0) (child q hR c hfirst hcut (cyclicSuccessor 0)) x ↔ _
  rw [child_zero,child_nonzero q hR c hfirst hcut _ hs0,hv,hp]
  have hh:=first_edgeInterior_iff q (leftParameter q c) (leftParameter_spec q c).2.1 x
  simpa only [ActiveArc.edgeInterior,moveStart_zero,moveStart_succ] using hh

theorem affinePoint_prefix (u v : PlanarPoint ℝ) (t s : ℝ) :
    affinePoint u (affinePoint u v t) s=affinePoint u v (t*s) := by
  ext <;> simp only [affinePoint] <;> ring

theorem child_last_edge (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
    (e : Fin (a+1)) (he : e.val=a) (x : PlanarPoint ℝ) :
    DirectGLSSW.edgeInterior (child q hR c hfirst hcut) e x ↔
      ∃ s : ℝ, 0<s ∧ s<rightParameter q c ∧
        x=affinePoint (q c.val.2.castSucc) (q c.val.2.succ) s := by
  have ha:=cut_positive q c hcut
  have he0 : e≠0 := by intro hh;have hv:=congrArg Fin.val hh;simp only [Fin.val_zero] at hv;omega
  have hev : childVertex (b:=b) e=c.val.2.castSucc := by apply Fin.ext;exact he.trans hcut.symm
  change OnOpenSegment (child q hR c hfirst hcut e) (child q hR c hfirst hcut (cyclicSuccessor e)) x ↔ _
  rw [child_last_successor e he,child_zero,child_nonzero q hR c hfirst hcut e he0,hev,
    (rightParameter_spec q c).2.2]
  have ht:= (rightParameter_spec q c).1
  constructor
  · rintro ⟨s,hs0,hs1,hx⟩
    refine ⟨rightParameter q c*s,mul_pos ht hs0,?_,?_⟩
    · nlinarith only [ht,hs1]
    · exact hx.trans (affinePoint_prefix _ _ _ _)
  · rintro ⟨s,hs0,hst,hx⟩
    refine ⟨s/rightParameter q c,div_pos hs0 ht,(div_lt_one ht).mpr hst,?_⟩
    rw [affinePoint_prefix,mul_div_cancel₀ _ (ne_of_gt ht)]
    exact hx

theorem child_edge_subset (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
    (e : Fin (a+1)) (x : PlanarPoint ℝ) :
    DirectGLSSW.edgeInterior (child q hR c hfirst hcut) e x →
      ActiveArc.edgeInterior q (childEdge e) x := by
  by_cases he0 : e=0
  · subst e
    intro hx
    obtain ⟨s,hs0,hs1,hx⟩ := (child_first_edge q hR c hfirst hcut x).mp hx
    exact ⟨s,lt_trans (leftParameter_spec q c).1 hs0,hs1,hx⟩
  · by_cases hea : e.val=a
    · intro hx
      obtain ⟨s,hs0,hs1,hx⟩ := (child_last_edge q hR c hfirst hcut e hea x).mp hx
      have he : childEdge (b:=b) e=c.val.2 := by apply Fin.ext;exact hea.trans hcut.symm
      rw [he]
      exact ⟨s,hs0,lt_trans hs1 (rightParameter_spec q c).2.1,hx⟩
    · have he : e.val<a := by have hh:=e.isLt;omega
      exact (child_middle_edge q hR c hfirst hcut e he0 he x).mp

end DirectGLSSW.ActiveArc.Split
