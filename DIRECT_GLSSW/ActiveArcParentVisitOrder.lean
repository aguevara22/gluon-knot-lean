import ActiveArcChildVisitOrder

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor FiniteCycleOrder
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val=a)

def parentVisitMap (v : Visit (parent q c hcut)) : Visit q :=
  (parentCrossingToOriginal q c hcut v.1,v.2)

theorem parentVisitMap_edge (v : Visit (parent q c hcut)) :
    visitEdge q (parentVisitMap q c hcut v)=edge (visitEdge (parent q c hcut) v) := by
  rcases v with ⟨d,z⟩;cases z <;> rfl

def parentOffset (e : Fin (b+1)) : ℝ := if e=0 then rightParameter q c else 0

include hR in
theorem parentVisitMap_parameter (v : Visit (parent q c hcut)) :
    visitParameter q (parentVisitMap q c hcut v)=parentOffset q c (visitEdge (parent q c hcut) v)+
      tangentScale (rightParameter q c) (visitEdge (parent q c hcut) v)*visitParameter (parent q c hcut) v := by
  rcases v with ⟨d,z⟩
  cases z
  · by_cases hd : d.val.1=0
    · simpa only [parentOffset,tangentScale,visitEdge,visitParameter,parentVisitMap,
        Bool.false_eq_true,if_false,hd,if_pos] using parentCrossingToOriginal_firstParameter q hR c hcut d hd
    · simpa only [parentOffset,tangentScale,visitEdge,visitParameter,parentVisitMap,
        Bool.false_eq_true,if_false,hd,if_neg,one_mul,zero_add] using parentCrossingToOriginal_leftParameter q hR c hcut d hd
  · have hd : d.val.2≠0 := by
      intro hh;have hlt:=d.property.1;rw [hh] at hlt;exact (not_lt_of_ge (Fin.zero_le _)) hlt
    simpa only [parentOffset,tangentScale,visitEdge,visitParameter,parentVisitMap,
      if_true,hd,if_neg,if_false,one_mul,zero_add] using parentCrossingToOriginal_rightParameter q hR c hcut d

theorem parentVisitMap_lt (v w : Visit (parent q c hcut)) :
    (eventOrder q hR.noTriple).lt (Sum.inr (parentVisitMap q c hcut v))
      (Sum.inr (parentVisitMap q c hcut w)) ↔
    (eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple).lt (Sum.inr v) (Sum.inr w) := by
  rw [event_lt_iff,event_lt_iff]
  change ((visitEdge q (parentVisitMap q c hcut v)).val<(visitEdge q (parentVisitMap q c hcut w)).val ∨
    (visitEdge q (parentVisitMap q c hcut v)).val=(visitEdge q (parentVisitMap q c hcut w)).val ∧
    visitParameter q (parentVisitMap q c hcut v)<visitParameter q (parentVisitMap q c hcut w)) ↔
    ((visitEdge (parent q c hcut) v).val<(visitEdge (parent q c hcut) w).val ∨
     (visitEdge (parent q c hcut) v).val=(visitEdge (parent q c hcut) w).val ∧
     visitParameter (parent q c hcut) v<visitParameter (parent q c hcut) w)
  rw [parentVisitMap_edge,parentVisitMap_edge,parentVisitMap_parameter q hR,parentVisitMap_parameter q hR]
  simp only [edge,Nat.add_lt_add_iff_left,Nat.add_left_cancel_iff,Fin.val_inj]
  by_cases he : visitEdge (parent q c hcut) v=visitEdge (parent q c hcut) w
  · rw [he]
    simp only [lt_self_iff_false,true_and,false_or,add_lt_add_iff_left,
      mul_lt_mul_left (tangentScale_pos (rightParameter q c) (rightParameter_spec q c).2.1 _)]
  · simp only [he,false_and,or_false]

theorem parentVisitMap_between (u v w : Visit (parent q c hcut)) :
    Nonalternation.between q hR (Sum.inr (parentVisitMap q c hcut u))
      (Sum.inr (parentVisitMap q c hcut v)) (Sum.inr (parentVisitMap q c hcut w)) ↔
    Nonalternation.between (parent q c hcut) (regular_parent q hR c hcut)
      (Sum.inr u) (Sum.inr v) (Sum.inr w) := by
  unfold Nonalternation.between strictCyclicBetween
  simp only [parentVisitMap_lt q hR c hcut]

end DirectGLSSW.ActiveArc.Split
