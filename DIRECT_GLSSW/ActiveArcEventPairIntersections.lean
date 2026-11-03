import ActiveArcOrderedEventPair

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW Cursor RetainedWords Primitive AuxiliaryCarrierChart
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (U : Support q hR)

private theorem physical_intersection (hG1 : cyclicNoncollinear q)
    (e f : Fin (n+1)) (hef : e≠f) (x : PlanarPoint ℝ) (s t : ℝ)
    (hs : x=affinePoint (q e.castSucc) (q e.succ) s)
    (ht : x=affinePoint (q f.castSucc) (q f.succ) t) :
    lineDenominator (physicalLine q e) (physicalLine q f)≠0 ∧
      lineIntersection (physicalLine q e) (physicalLine q f)=x := by
  have hd := physicalLine_denominator_ne q hG1 e f hef s t (hs.symm.trans ht)
  refine ⟨hd,?_⟩
  symm
  apply lineIntersection_unique _ _ x hd
  · rw [hs];exact physicalLine_affine_value q e s
  · rw [ht];exact physicalLine_affine_value q f t

/-- The event root is the actual first/right crossing-line intersection. -/
theorem eventCarrierPair_root_intersection (hc : FirstCrossing q c) (hG1 : cyclicNoncollinear q) :
    let p := eventCarrierPair q hR c U (openFirst q hR U.val)
    let L := parentChartLines (a:=n) (b:=0) q
    lineDenominator (L p.1) (L p.2)≠0 ∧ lineIntersection (L p.1) (L p.2)=crossingPoint q c := by
  dsimp only
  rw [eventCarrierPair_zero]
  change lineDenominator (physicalLine q 0) (physicalLine q c.val.2)≠0 ∧ _
  have hh := physical_intersection q hG1 c.val.1 c.val.2 (ne_of_lt c.property.1)
    (crossingPoint q c) (leftParameter q c) (rightParameter q c)
    (leftParameter_spec q c).2.2 (rightParameter_spec q c).2.2
  rw [hc.1] at hh
  exact hh

/-- Each interior retained vertex is the unique intersection of its two
actual consecutive physical side carriers. Source G1 supplies transversality. -/
theorem eventCarrierPair_middle_intersection (hG1 : cyclicNoncollinear q)
    (i : Fin (openCount q hR U.val)) (hi0 : 0 < i.val)
    (hi1 : i.val+1<openCount q hR U.val) :
    let p := eventCarrierPair q hR c U i
    let L := parentChartLines (a:=n) (b:=0) q
    lineDenominator (L p.1) (L p.2)≠0 ∧ lineIntersection (L p.1) (L p.2)=OpenVertex q hR U i := by
  let u : Fin (openCount q hR U.val-1) := ⟨i.val-1,by omega⟩
  let v : Fin (openCount q hR U.val-1) := ⟨i.val,by omega⟩
  have hp : eventCarrierPair q hR c U i=
      (Sum.inl (openSideCarrier q hR U.val u),Sum.inl (openSideCarrier q hR U.val v)) := by
    simp only [eventCarrierPair,if_neg (Nat.ne_of_gt hi0),eventCarrierChain,
      dif_pos (show i.val-1<openCount q hR U.val-1 by omega),
      dif_pos (show i.val<openCount q hR U.val-1 by omega)]
    rfl
  dsimp only
  rw [hp]
  obtain ⟨s,t,_,_,_,_,ht⟩ := openSideCarrier_physical q hR U.val u
  obtain ⟨r,w,_,_,_,hr,_⟩ := openSideCarrier_physical q hR U.val v
  have hiu : (⟨u.val+1,by have := u.isLt;omega⟩ : Fin (openCount q hR U.val))=i := by
    apply Fin.ext
    change i.val-1+1=i.val
    omega
  rw [hiu] at ht
  have hef : openSideCarrier q hR U.val u≠openSideCarrier q hR U.val v := by
    intro hh
    have huv := openSideCarrier_injective q hR U.val U.property hh
    have hv := congrArg Fin.val huv
    change i.val-1=i.val at hv
    omega
  exact physical_intersection q hG1 _ _ hef _ t r ht hr

/-- The final coordinate-line pair recovers the genuine terminal vertex. -/
theorem eventCarrierPair_last_intersection :
    let p := eventCarrierPair q hR c U (openLast q hR U.val)
    let L := parentChartLines (a:=n) (b:=0) q
    lineDenominator (L p.1) (L p.2)≠0 ∧
      lineIntersection (L p.1) (L p.2)=OpenVertex q hR U (openLast q hR U.val) := by
  dsimp only
  rw [eventCarrierPair_last]
  change lineDenominator (physicalLine q ⟨n,by omega⟩) (terminalLine q)≠0 ∧ _
  have hd := terminalLine_denominator_ne q hR
  refine ⟨hd,?_⟩
  change lineIntersection (physicalLine q ⟨n,by omega⟩) (terminalLine q)=
    RetainedWords.vertex q hR U.val (start q) (openLast q hR U.val)
  rw [open_vertex_last]
  symm
  apply lineIntersection_unique _ _ _ hd
  · simpa only [affinePoint_one] using physicalLine_affine_value q ⟨n,by omega⟩ 1
  · exact terminalLine_value q

/-- Every literal event-word coordinate is the unique intersection of its
canonical ordered carrier pair, with every denominator proved nonzero. -/
theorem eventCarrierPair_intersection (hc : FirstCrossing q c) (hG1 : cyclicNoncollinear q)
    (i : Fin (openCount q hR U.val)) :
    let p := eventCarrierPair q hR c U i
    let L := parentChartLines (a:=n) (b:=0) q
    lineDenominator (L p.1) (L p.2)≠0 ∧
      lineIntersection (L p.1) (L p.2)=eventOpenWord q hR U c i.val := by
  by_cases hi0 : i.val=0
  · have he : i=openFirst q hR U.val := Fin.ext hi0
    subst i
    exact eventCarrierPair_root_intersection q hR c U hc hG1
  · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi0
    have hw := eventOpenWord_pos q hR U c i.val hpos i.isLt
    dsimp only
    rw [hw]
    by_cases hi1 : i.val+1<openCount q hR U.val
    · exact eventCarrierPair_middle_intersection q hR c U hG1 i hpos hi1
    · have he : i=openLast q hR U.val := by
        apply Fin.ext
        change i.val=openCount q hR U.val-1
        have := i.isLt
        omega
      subst i
      exact eventCarrierPair_last_intersection q hR c U

end DirectGLSSW.ActiveArc.OpenCarrier
