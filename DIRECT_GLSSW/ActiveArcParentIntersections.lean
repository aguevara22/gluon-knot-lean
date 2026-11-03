import ActiveArcParentLineGeometry
import ActiveArcOpenLastSide
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split AuxiliaryCarrierChart
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val=a)
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))

/-- Internal original-line intersection characterization, with source vertex G1. -/
private theorem original_intersection (hG1 : cyclicNoncollinear q)
    (e f : Fin (a+b+1)) (hef : e≠f) (x : PlanarPoint ℝ) (s t : ℝ)
    (hs : x=affinePoint (q e.castSucc) (q e.succ) s)
    (ht : x=affinePoint (q f.castSucc) (q f.succ) t) :
    lineDenominator (physicalLine q e) (physicalLine q f)≠0 ∧
      lineIntersection (physicalLine q e) (physicalLine q f)=x := by
  have hd := physicalLine_denominator_ne q hG1 e f hef s t (hs.symm.trans ht)
  refine ⟨hd,?_⟩
  symm
  apply lineIntersection_unique _ _ x hd
  · rw [hs]; exact physicalLine_affine_value q e s
  · rw [ht]; exact physicalLine_affine_value q f t

/-- The first pair is exactly c's two original intersecting physical carriers. -/
theorem parentCarrierChain_one :
    parentCarrierChain q hR c hcut T ⟨1,by have := open_count_ge_two (parent q c hcut) (regular_parent q hR c hcut) T.val; omega⟩ =
      Sum.inl c.val.2 := by
  have h := parentCarrierChain_middle q hR c hcut T
    ⟨0,by have := open_count_ge_two (parent q c hcut) (regular_parent q hR c hcut) T.val; omega⟩
  rw [openSideCarrier_zero] at h
  convert h using 1
  congr 1
  apply Fin.ext
  simpa only [edge,Nat.add_zero] using hcut

/-- Literal first parent retained vertex is recovered from the incoming/outgoing crossing lines. -/
theorem parent_first_intersection (hG1 : cyclicNoncollinear q) :
    let i := openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val
    lineDenominator (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (parentChartLines q (parentCarrierChain q hR c hcut T i.succ))≠0 ∧
    lineIntersection (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (parentChartLines q (parentCarrierChain q hR c hcut T i.succ)) =
      Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i := by
  dsimp only
  have h0 : parentCarrierChain q hR c hcut T
      (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val).castSucc=Sum.inl c.val.1 :=
    parentCarrierChain_zero q hR c hcut T
  have h1 : parentCarrierChain q hR c hcut T
      (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val).succ=Sum.inl c.val.2 :=
    parentCarrierChain_one q hR c hcut T
  rw [h0,h1]
  simp only [parentChartLines,Sum.elim_inl]
  have hp : Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
      (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val)=crossingPoint q c :=
    (open_vertex_first (parent q c hcut) (regular_parent q hR c hcut) T.val).trans (parent_zero q c hcut)
  rw [hp]
  exact original_intersection (a:=a) (b:=b) q hG1 c.val.1 c.val.2 (ne_of_lt c.property.1)
    (crossingPoint q c) (leftParameter q c) (rightParameter q c)
    (leftParameter_spec q c).2.2 (rightParameter_spec q c).2.2

/-- Every interior retained parent vertex is the intersection of its two distinct actual original side lines. -/
theorem parent_middle_intersection (hG1 : cyclicNoncollinear q)
    (i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val))
    (hi0 : 0 < i.val) (hi1 : i.val+1<openCount (parent q c hcut) (regular_parent q hR c hcut) T.val) :
    lineDenominator (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (parentChartLines q (parentCarrierChain q hR c hcut T i.succ))≠0 ∧
    lineIntersection (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (parentChartLines q (parentCarrierChain q hR c hcut T i.succ)) =
      Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i := by
  let u : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val-1) := ⟨i.val-1,by omega⟩
  let v : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val-1) := ⟨i.val,by omega⟩
  have hc0 := parentCarrierChain_middle q hR c hcut T u
  have hc1 := parentCarrierChain_middle q hR c hcut T v
  have hu : (⟨u.val+1,by have := u.isLt; omega⟩ : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val+1))=i.castSucc := by apply Fin.ext; change i.val-1+1=i.val; omega
  have hv : (⟨v.val+1,by have := v.isLt; omega⟩ : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val+1))=i.succ := rfl
  rw [hu] at hc0
  rw [hv] at hc1
  rw [hc0,hc1]
  obtain ⟨s,t,_,ht⟩ := parent_side_original q hR c hcut T u
  obtain ⟨r,w,hr,_⟩ := parent_side_original q hR c hcut T v
  have hiu : (⟨u.val+1,by have := u.isLt; omega⟩ : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val))=i := by apply Fin.ext; change i.val-1+1=i.val; omega
  rw [hiu] at ht
  have hef : edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u) ≠
      edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val v) := by
    intro hh
    have huv := openSideCarrier_injective (parent q c hcut) (regular_parent q hR c hcut) T.val T.property (edge_injective hh)
    have hh := congrArg Fin.val huv
    change i.val-1=i.val at hh
    omega
  exact original_intersection (a:=a) (b:=b) q hG1 _ _ hef _ t r ht hr

/-- The terminal coordinate line recovers the actual terminal retained vertex. -/
theorem parent_last_intersection :
    let i := openLast (parent q c hcut) (regular_parent q hR c hcut) T.val
    lineDenominator (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (parentChartLines q (parentCarrierChain q hR c hcut T i.succ))≠0 ∧
    lineIntersection (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (parentChartLines q (parentCarrierChain q hR c hcut T i.succ)) =
      Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i := by
  let m := openCount (parent q c hcut) (regular_parent q hR c hcut) T.val
  have hm : 2≤m := open_count_ge_two (parent q c hcut) (regular_parent q hR c hcut) T.val
  let u : Fin (m-1) := ⟨m-2,by omega⟩
  have hc0 := parentCarrierChain_middle q hR c hcut T u
  rw [show openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u=⟨b,by omega⟩ from
    openSideCarrier_last (parent q c hcut) (regular_parent q hR c hcut) T.val] at hc0
  have hu : (⟨u.val+1,by have := u.isLt; omega⟩ : Fin (m+1))=
      (openLast (parent q c hcut) (regular_parent q hR c hcut) T.val).castSucc := by
    apply Fin.ext
    change m-2+1=m-1
    omega
  rw [hu] at hc0
  have hc1 := parentCarrierChain_last q hR c hcut T
  have hv : (⟨m,by omega⟩ : Fin (m+1))=
      (openLast (parent q c hcut) (regular_parent q hR c hcut) T.val).succ := by
    apply Fin.ext
    change m=m-1+1
    omega
  rw [hv] at hc1
  dsimp only
  rw [hc0,hc1]
  have he : edge (a:=a) (⟨b,by omega⟩ : Fin (b+1))=⟨a+b,by omega⟩ := rfl
  rw [he]
  change lineDenominator (physicalLine q ⟨a+b,by omega⟩) (terminalLine q)≠0 ∧ _
  have hd := terminalLine_denominator_ne q hR
  refine ⟨hd,?_⟩
  change lineIntersection (physicalLine q ⟨a+b,by omega⟩) (terminalLine q)=
    RetainedWords.vertex (parent q c hcut) (regular_parent q hR c hcut) T.val (start _) (openLast _ _ _)
  rw [open_vertex_last]
  have hp : parent q c hcut ⟨b+1,by omega⟩=q ⟨a+b+1,by omega⟩ := by
    simpa only [Split.vertex,Fin.val_succ,Nat.add_assoc] using parent_succ q c hcut ⟨b,by omega⟩
  rw [hp]
  symm
  apply lineIntersection_unique _ _ _ hd
  · simpa only [affinePoint_one] using physicalLine_affine_value q ⟨a+b,by omega⟩ 1
  · exact terminalLine_value q

/-- Every actual retained parent point is the unique intersection of its adjacent
coordinate carriers. Only source vertex G1 is added; no daughter genericity is assumed. -/
theorem parent_vertex_intersection (hG1 : cyclicNoncollinear q)
    (i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val)) :
    lineDenominator (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (parentChartLines q (parentCarrierChain q hR c hcut T i.succ))≠0 ∧
    lineIntersection (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (parentChartLines q (parentCarrierChain q hR c hcut T i.succ)) =
      Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i := by
  by_cases hi0 : i.val=0
  · have he : i=openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val := Fin.ext hi0
    subst i
    exact parent_first_intersection q hR c hcut T hG1
  · by_cases hi1 : i.val+1<openCount (parent q c hcut) (regular_parent q hR c hcut) T.val
    · exact parent_middle_intersection q hR c hcut T hG1 i (Nat.pos_of_ne_zero hi0) hi1
    · have he : i=openLast (parent q c hcut) (regular_parent q hR c hcut) T.val := by
        apply Fin.ext
        change i.val=openCount (parent q c hcut) (regular_parent q hR c hcut) T.val-1
        have := i.isLt
        omega
      subst i
      exact parent_last_intersection q hR c hcut T

end DirectGLSSW.ActiveArc.OpenCarrier
