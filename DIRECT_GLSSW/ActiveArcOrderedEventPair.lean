import ActiveArcEventPairClassification
import ActiveArcParentLineGeometry
import ActiveArcOpenLastSide

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW Cursor RetainedWords Primitive EventCarrierPairClassification AuxiliaryCarrierChart
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (U : Support q hR)

/-- Ordered incident carrier labels of the actual event word: crossing pair
at its root, consecutive retained carrier pair at every positive vertex. -/
def eventCarrierPair (i : Fin (openCount q hR U.val)) :
    (Fin (n+1) ⊕ Unit) × (Fin (n+1) ⊕ Unit) :=
  if i.val=0 then
    (eventCarrierChain q hR U (openFirst q hR U.val),Sum.inl c.val.2)
  else (eventCarrierChain q hR U ⟨i.val-1,by have := i.isLt;omega⟩,
    eventCarrierChain q hR U i)

/-- The ordered physical pair has exactly the unordered pair used in the
sealed actual pair-classification theorem, with the same integer position. -/
theorem eventCarrierPair_finset_eq
    (i : Fin (openCount q hR U.val-2+2)) :
    let h := Nat.sub_add_cancel (open_count_ge_two q hR U.val)
    let f := fun j => eventCarrierChain q hR U (Fin.cast h j)
    let p := eventCarrierPair q hR c U (Fin.cast h i)
    ({p.1,p.2} : Finset (Fin (n+1) ⊕ Unit))=eventPair f (Sum.inl c.val.2) i := by
  intro h f p
  by_cases hi : i.val=0
  · simp only [p,eventCarrierPair,Fin.coe_cast,hi,if_pos rfl,eventPair]
    rfl
  · simp only [p,eventCarrierPair,Fin.coe_cast,if_neg hi,eventPair]
    rfl

/-- At the root the ordered pair is the first and right physical crossing carriers. -/
theorem eventCarrierPair_zero :
    eventCarrierPair q hR c U (openFirst q hR U.val)=(Sum.inl 0,Sum.inl c.val.2) := by
  change (eventCarrierChain q hR U (openFirst q hR U.val),Sum.inl c.val.2)=_
  exact congrArg (fun x : Fin (n+1) ⊕ Unit => (x,Sum.inl c.val.2))
    (eventCarrierChain_zero q hR U)

/-- The terminal vertex uses the original final physical edge and the fresh
terminal coordinate line, never an auxiliary closing edge. -/
theorem eventCarrierPair_last :
    eventCarrierPair q hR c U (openLast q hR U.val)=
      (Sum.inl (⟨n,by omega⟩ : Fin (n+1)),Sum.inr ()) := by
  have hm := open_count_ge_two q hR U.val
  have hp : (openLast q hR U.val).val≠0 := by change openCount q hR U.val-1≠0;omega
  have hl : ¬(openLast q hR U.val).val<openCount q hR U.val-1 := by
    change ¬openCount q hR U.val-1<openCount q hR U.val-1;omega
  have hpred : (openLast q hR U.val).val-1=openCount q hR U.val-2 := by
    change openCount q hR U.val-1-1=openCount q hR U.val-2
    omega
  have hlt : (openLast q hR U.val).val-1<openCount q hR U.val-1 := by rw [hpred];omega
  simp only [eventCarrierPair,if_neg hp,eventCarrierChain,dif_pos hlt,dif_neg hl]
  have he : (⟨(openLast q hR U.val).val-1,hlt⟩ : Fin (openCount q hR U.val-1))=
      ⟨openCount q hR U.val-2,by omega⟩ := Fin.ext hpred
  rw [he,openSideCarrier_last]

end DirectGLSSW.ActiveArc.OpenCarrier
