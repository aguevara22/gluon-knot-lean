import ActiveArcPieceSelections
import DirectGLSSW.PolygonNonalternation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor FiniteCycleOrder
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)

/-- Child G2 is inherited by its actual physical subsegments; this is not G1. -/
theorem child_noTriple : cyclicNoTripleIntersections (child q hR c hfirst hcut) := by
  intro e f g x hef hfg heg h
  exact hR.noTriple (childEdge e) (childEdge f) (childEdge g) x
    (fun hh => hef (childEdge_injective hh)) (fun hh => hfg (childEdge_injective hh))
    (fun hh => heg (childEdge_injective hh.symm))
    ⟨child_edge_subset q hR c hfirst hcut e x h.1,
      child_edge_subset q hR c hfirst hcut f x h.2.1,
      child_edge_subset q hR c hfirst hcut g x h.2.2⟩

def childScale (e : Fin (a+1)) : ℝ :=
  if e=0 then 1-leftParameter q c else if e.val=a then rightParameter q c else 1

def childOffset (e : Fin (a+1)) : ℝ := if e=0 then leftParameter q c else 0

theorem childScale_pos (e : Fin (a+1)) : 0<childScale q c e := by
  unfold childScale
  split_ifs
  · exact sub_pos.mpr (leftParameter_spec q c).2.1
  · exact (rightParameter_spec q c).1
  · exact zero_lt_one

theorem child_affine (e : Fin (a+1)) (u : ℝ) :
    affinePoint (child q hR c hfirst hcut e) (child q hR c hfirst hcut (cyclicSuccessor e)) u=
      affinePoint (q (childEdge e).castSucc) (q (childEdge e).succ)
        (childOffset q c e+childScale q c e*u) := by
  by_cases he0 : e=0
  · subst e
    have ha:=cut_positive q c hcut
    have hs:=child_successor_val (0 : Fin (a+1)) (by simpa using ha)
    have hs0 : cyclicSuccessor (0 : Fin (a+1))≠0 := by
      intro hh;have hv:=congrArg Fin.val hh;simp only [Fin.val_zero] at hv;omega
    have hv : childVertex (b:=b) (cyclicSuccessor (0 : Fin (a+1)))=(1 : Fin (a+b+2)) := by
      apply Fin.ext;exact hs
    have hp : crossingPoint q c=affinePoint (q 0) (q 1) (leftParameter q c) := by
      simpa only [hfirst] using (leftParameter_spec q c).2.2
    rw [child_zero,child_nonzero q hR c hfirst hcut _ hs0,hv,hp,affinePoint_suffix]
    rfl
  · by_cases hea : e.val=a
    · have hv : childVertex (b:=b) e=c.val.2.castSucc := by apply Fin.ext;exact hea.trans hcut.symm
      have he : childEdge (b:=b) e=c.val.2 := by apply Fin.ext;exact hea.trans hcut.symm
      rw [child_last_successor e hea,child_zero,child_nonzero q hR c hfirst hcut e he0,hv,
        (rightParameter_spec q c).2.2,affinePoint_prefix]
      simp only [childOffset,childScale,if_neg he0,if_pos hea,zero_add,he]
    · have hel : e.val<a := by have hh:=e.isLt;omega
      have hs:=child_successor_val e hel
      have hs0 : cyclicSuccessor e≠0 := by
        intro hh;have hv:=congrArg Fin.val hh;simp only [Fin.val_zero] at hv;omega
      have hv : childVertex (b:=b) (cyclicSuccessor e)=(childEdge (b:=b) e).succ := by apply Fin.ext;exact hs
      rw [child_nonzero q hR c hfirst hcut e he0,child_nonzero q hR c hfirst hcut _ hs0,hv]
      simp only [childOffset,childScale,if_neg he0,if_neg hea,one_mul,zero_add]
      rfl

def childVisitMap (v : CrossingVisit (child q hR c hfirst hcut)) : Visit q :=
  (childCrossingToOriginal q hR c hfirst hcut v.1,v.2)

theorem childVisitMap_edge (v : CrossingVisit (child q hR c hfirst hcut)) :
    visitEdge q (childVisitMap q hR c hfirst hcut v)=
      childEdge (crossingVisitEdge (child q hR c hfirst hcut) v) := by
  rcases v with ⟨d,z⟩;cases z <;> rfl

theorem childVisitMap_parameter (v : CrossingVisit (child q hR c hfirst hcut)) :
    visitParameter q (childVisitMap q hR c hfirst hcut v)=
      childOffset q c (crossingVisitEdge (child q hR c hfirst hcut) v)+
      childScale q c (crossingVisitEdge (child q hR c hfirst hcut) v)*
        crossingVisitParameter (child q hR c hfirst hcut) v := by
  apply edge_parameter_unique q hR (childEdge (crossingVisitEdge (child q hR c hfirst hcut) v))
  have ho:=(visitParameter_spec q (childVisitMap q hR c hfirst hcut v)).2.2
  rw [childVisitMap_edge] at ho
  have hn:=(crossingVisitParameter_spec (child q hR c hfirst hcut) v).2.2
  rw [child_affine q hR c hfirst hcut] at hn
  exact ho.symm.trans ((childCrossingToOriginal_point q hR c hfirst hcut v.1).trans hn)

/-- Every actual child crossing-visit comparison has its original strict order. -/
theorem childVisitMap_lt (v w : CrossingVisit (child q hR c hfirst hcut)) :
    (eventOrder q hR.noTriple).lt (Sum.inr (childVisitMap q hR c hfirst hcut v))
      (Sum.inr (childVisitMap q hR c hfirst hcut w)) ↔
    (polygonEventOrder (child q hR c hfirst hcut) (child_noTriple q hR c hfirst hcut)).lt
      (Sum.inr v) (Sum.inr w) := by
  rw [event_lt_iff,polygonEvent_lt_iff]
  change ((visitEdge q (childVisitMap q hR c hfirst hcut v)).val<
      (visitEdge q (childVisitMap q hR c hfirst hcut w)).val ∨
    (visitEdge q (childVisitMap q hR c hfirst hcut v)).val=
      (visitEdge q (childVisitMap q hR c hfirst hcut w)).val ∧
      visitParameter q (childVisitMap q hR c hfirst hcut v)<visitParameter q (childVisitMap q hR c hfirst hcut w)) ↔
    (crossingVisitEdge (child q hR c hfirst hcut) v<crossingVisitEdge (child q hR c hfirst hcut) w ∨
     crossingVisitEdge (child q hR c hfirst hcut) v=crossingVisitEdge (child q hR c hfirst hcut) w ∧
     crossingVisitParameter (child q hR c hfirst hcut) v<crossingVisitParameter (child q hR c hfirst hcut) w)
  rw [childVisitMap_edge,childVisitMap_edge,childVisitMap_parameter,childVisitMap_parameter]
  simp only [childEdge,Fin.mk_lt_mk,Fin.val_inj]
  by_cases he : crossingVisitEdge (child q hR c hfirst hcut) v=crossingVisitEdge (child q hR c hfirst hcut) w
  · rw [he]
    simp only [lt_self_iff_false,true_and,false_or,add_lt_add_iff_left,
      mul_lt_mul_left (childScale_pos q c _)]
  · simp only [he,false_and,or_false]
    rfl

/-- Literal cyclic betweenness on the actual child polygon's event order. -/
def childVisitBetween (u v w : CrossingVisit (child q hR c hfirst hcut)) : Prop :=
  @strictCyclicBetween (PolygonEvent (child q hR c hfirst hcut))
    (polygonEventOrder (child q hR c hfirst hcut) (child_noTriple q hR c hfirst hcut)).toLT
    (Sum.inr u) (Sum.inr v) (Sum.inr w)

theorem childVisitMap_between (u v w : CrossingVisit (child q hR c hfirst hcut)) :
    Nonalternation.between q hR (Sum.inr (childVisitMap q hR c hfirst hcut u))
      (Sum.inr (childVisitMap q hR c hfirst hcut v)) (Sum.inr (childVisitMap q hR c hfirst hcut w)) ↔
    childVisitBetween q hR c hfirst hcut u v w := by
  unfold Nonalternation.between childVisitBetween strictCyclicBetween
  simp only [childVisitMap_lt]


end DirectGLSSW.ActiveArc.Split
