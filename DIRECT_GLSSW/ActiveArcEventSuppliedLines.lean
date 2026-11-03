import ActiveArcEventPairIntersections
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW Cursor RetainedWords Primitive AuxiliaryCarrierChart
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (U : Support q hR)
variable (L : Fin (n+1) ⊕ Unit → CarrierLine)
variable (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
  lineValue (L (Sum.inl e)) (q e.succ)=0)
variable (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0)

private theorem affine_incidence (K : CarrierLine) (x y : PlanarPoint ℝ) (t : ℝ)
    (hx : lineValue K x=0) (hy : lineValue K y=0) :
    lineValue K (affinePoint x y t)=0 := by
  have hf : lineValue K (affinePoint x y t)=(1-t)*lineValue K x+t*lineValue K y := by
    simp only [lineValue,planarDet,affinePoint];ring
  rw [hf,hx,hy];ring

include hinc hterminal in
/-- Every actual event-word coordinate lies on its two supplied incident
carrier lines. These are actual physical endpoints and a terminal coordinate line. -/
theorem event_pair_supplied_incidence (hc : FirstCrossing q c)
    (i : Fin (openCount q hR U.val)) :
    lineValue (L (eventCarrierPair q hR c U i).1) (eventOpenWord q hR U c i.val)=0 ∧
    lineValue (L (eventCarrierPair q hR c U i).2) (eventOpenWord q hR U c i.val)=0 := by
  by_cases hi0 : i.val=0
  · have he : i=openFirst q hR U.val := Fin.ext hi0
    subst i
    rw [eventCarrierPair_zero]
    change lineValue (L (Sum.inl 0)) (crossingPoint q c)=0 ∧
      lineValue (L (Sum.inl c.val.2)) (crossingPoint q c)=0
    constructor
    · rw [← hc.1,(leftParameter_spec q c).2.2]
      exact affine_incidence _ _ _ _ (hinc c.val.1).1 (hinc c.val.1).2
    · rw [(rightParameter_spec q c).2.2]
      exact affine_incidence _ _ _ _ (hinc c.val.2).1 (hinc c.val.2).2
  · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi0
    rw [eventOpenWord_pos q hR U c i.val hpos i.isLt]
    change lineValue (L (eventCarrierPair q hR c U i).1) (RetainedWords.vertex q hR U.val (start q) i)=0 ∧
      lineValue (L (eventCarrierPair q hR c U i).2) (RetainedWords.vertex q hR U.val (start q) i)=0
    by_cases hi1 : i.val+1<openCount q hR U.val
    · let u : Fin (openCount q hR U.val-1) := ⟨i.val-1,by omega⟩
      let v : Fin (openCount q hR U.val-1) := ⟨i.val,by omega⟩
      have hp : eventCarrierPair q hR c U i=
          (Sum.inl (openSideCarrier q hR U.val u),Sum.inl (openSideCarrier q hR U.val v)) := by
        simp only [eventCarrierPair,if_neg hi0,eventCarrierChain,
          dif_pos (show i.val-1<openCount q hR U.val-1 by omega),
          dif_pos (show i.val<openCount q hR U.val-1 by omega)]
        rfl
      rw [hp]
      obtain ⟨s,t,_,_,_,_,ht⟩ := openSideCarrier_physical q hR U.val u
      obtain ⟨r,w,_,_,_,hr,_⟩ := openSideCarrier_physical q hR U.val v
      have hiu : (⟨u.val+1,by have := u.isLt;omega⟩ : Fin (openCount q hR U.val))=i := by
        apply Fin.ext;change i.val-1+1=i.val;omega
      rw [hiu] at ht
      constructor
      · rw [ht]
        exact affine_incidence _ _ _ _ (hinc _).1 (hinc _).2
      · rw [hr]
        exact affine_incidence _ _ _ _ (hinc _).1 (hinc _).2
    · have he : i=openLast q hR U.val := by
        apply Fin.ext
        change i.val=openCount q hR U.val-1
        have := i.isLt;omega
      subst i
      rw [eventCarrierPair_last]
      change lineValue (L (Sum.inl ⟨n,by omega⟩))
          (RetainedWords.vertex q hR U.val (start q) (openLast q hR U.val))=0 ∧ _
      rw [open_vertex_last]
      exact ⟨(hinc ⟨n,by omega⟩).2,hterminal⟩

include hinc hterminal in
/-- Supplied transverse carrier pairs recover literal event-word coordinates. -/
theorem event_pair_supplied_intersection (hc : FirstCrossing q c)
    (i : Fin (openCount q hR U.val))
    (hd : lineDenominator (L (eventCarrierPair q hR c U i).1)
      (L (eventCarrierPair q hR c U i).2)≠0) :
    lineIntersection (L (eventCarrierPair q hR c U i).1)
      (L (eventCarrierPair q hR c U i).2)=eventOpenWord q hR U c i.val := by
  have hh := event_pair_supplied_incidence q hR c U L hinc hterminal hc i
  exact (lineIntersection_unique _ _ _ hd hh.1 hh.2).symm
end DirectGLSSW.ActiveArc.OpenCarrier
