import ActiveArcParentIntersections

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

noncomputable section

namespace DirectGLSSW.ActiveArc.OpenCarrier

open DirectGLSSW ActiveArc RetainedWords Split AuxiliaryCarrierChart

variable {a b : ℕ}
variable (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val=a)
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))

private theorem lineValue_affine_incidence (L : CarrierLine)
    (x y : PlanarPoint ℝ) (t : ℝ)
    (hx : lineValue L x=0) (hy : lineValue L y=0) :
    lineValue L (affinePoint x y t)=0 := by
  have hformula : lineValue L (affinePoint x y t) =
      (1-t)*lineValue L x+t*lineValue L y := by
    simp only [lineValue, planarDet, affinePoint]
    ring
  rw [hformula, hx, hy]
  ring

private theorem parent_side_supplied_line_incidence
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine)
    (hinc : ∀ e : Fin (a+b+1),
      lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (u : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val-1)) :
    lineValue (L (Sum.inl (edge (a:=a)
      (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u))))
      (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
        (⟨u.val,by change u.val < openCount (parent q c hcut) (regular_parent q hR c hcut) T.val; have := u.isLt; omega⟩ : Fin _))=0 ∧
    lineValue (L (Sum.inl (edge (a:=a)
      (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u))))
      (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
        (⟨u.val+1,by change u.val+1 < openCount (parent q c hcut) (regular_parent q hR c hcut) T.val; have := u.isLt; omega⟩ : Fin _))=0 := by
  obtain ⟨s,t,hs,ht⟩ := parent_side_original q hR c hcut T u
  let e := edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u)
  constructor
  · rw [hs]
    exact lineValue_affine_incidence (L (Sum.inl e)) (q e.castSucc) (q e.succ) s
      (hinc e).1 (hinc e).2
  · rw [ht]
    exact lineValue_affine_incidence (L (Sum.inl e)) (q e.castSucc) (q e.succ) t
      (hinc e).1 (hinc e).2

/-- Every actual retained parent vertex lies on both neighboring lines from an
arbitrary supplied family satisfying only the physical and terminal endpoint
incidences. -/
theorem parent_vertex_supplied_line_incidence
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine)
    (hinc : ∀ e : Fin (a+b+1),
      lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0)
    (i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val)) :
    lineValue (L (parentCarrierChain q hR c hcut T i.castSucc))
      (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i)=0 ∧
    lineValue (L (parentCarrierChain q hR c hcut T i.succ))
      (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i)=0 := by
  let m := openCount (parent q c hcut) (regular_parent q hR c hcut) T.val
  by_cases hi0 : i.val=0
  · have hei : i=openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val := by
      apply Fin.ext
      simp [openFirst, hi0]
    subst i
    have h0 : parentCarrierChain q hR c hcut T
        (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val).castSucc = Sum.inl c.val.1 :=
      parentCarrierChain_zero q hR c hcut T
    have h1 : parentCarrierChain q hR c hcut T
        (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val).succ = Sum.inl c.val.2 := by
      exact parentCarrierChain_one q hR c hcut T
    have hp : Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
        (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val)=crossingPoint q c :=
      (open_vertex_first (parent q c hcut) (regular_parent q hR c hcut) T.val).trans
        (parent_zero q c hcut)
    constructor
    · rw [h0,hp,(leftParameter_spec q c).2.2]
      exact lineValue_affine_incidence (L (Sum.inl c.val.1))
        (q c.val.1.castSucc) (q c.val.1.succ) (leftParameter q c)
        (hinc c.val.1).1 (hinc c.val.1).2
    · rw [h1,hp,(rightParameter_spec q c).2.2]
      exact lineValue_affine_incidence (L (Sum.inl c.val.2))
        (q c.val.2.castSucc) (q c.val.2.succ) (rightParameter q c)
        (hinc c.val.2).1 (hinc c.val.2).2
  · by_cases hiLast : i.val+1<m
    · let u : Fin (m-1) := ⟨i.val-1,by omega⟩
      let v : Fin (m-1) := ⟨i.val,by omega⟩
      have hu : (⟨u.val+1,by have := u.isLt; omega⟩ : Fin (m+1))=i.castSucc := by
        apply Fin.ext
        change i.val-1+1=i.val
        omega
      have hv : (⟨v.val+1,by have := v.isLt; omega⟩ : Fin (m+1))=i.succ := by
        rfl
      have hcu := parentCarrierChain_middle q hR c hcut T u
      have hcv := parentCarrierChain_middle q hR c hcut T v
      rw [hu] at hcu
      rw [hv] at hcv
      have hiu : (⟨u.val+1,by have := u.isLt; omega⟩ : Fin m)=i := by
        apply Fin.ext
        change i.val-1+1=i.val
        omega
      have hiv : (⟨v.val,by have := v.isLt; omega⟩ : Fin m)=i := by
        apply Fin.ext
        rfl
      have hsideu := parent_side_supplied_line_incidence q hR c hcut T L hinc u
      have hsidev := parent_side_supplied_line_incidence q hR c hcut T L hinc v
      have hsideu' : lineValue (L (Sum.inl (edge (a:=a)
          (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u))))
          (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i)=0 := by
        simpa only [hiu] using hsideu.2
      have hsidev' : lineValue (L (Sum.inl (edge (a:=a)
          (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val v))))
          (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i)=0 := by
        simpa only [hiv] using hsidev.1
      constructor
      · rw [hcu]
        exact hsideu'
      · rw [hcv]
        exact hsidev'
    · let last := openLast (parent q c hcut) (regular_parent q hR c hcut) T.val
      have hilast : i=last := by
        apply Fin.ext
        change i.val=m-1
        have := i.isLt
        omega
      subst i
      have hm : 2≤m := open_count_ge_two (parent q c hcut)
        (regular_parent q hR c hcut) T.val
      let u : Fin (m-1) := ⟨m-2,by omega⟩
      have hside := parent_side_supplied_line_incidence q hR c hcut T L hinc u
      have hiu : (⟨u.val+1,by have := u.isLt; omega⟩ : Fin m)=last := by
        apply Fin.ext
        change m-2+1=m-1
        omega
      have hsideAtLast : lineValue (L (Sum.inl (edge (a:=a)
          (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u))))
          (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T last)=0 := by
        simpa only [hiu] using hside.2
      have hsideLast : lineValue (L (Sum.inl (edge (a:=a) (⟨b,by omega⟩ : Fin (b+1)))))
          (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T last)=0 := by
        have hlastSide : openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u =
            (⟨b,by omega⟩ : Fin (b+1)) := openSideCarrier_last (parent q c hcut)
              (regular_parent q hR c hcut) T.val
        simpa only [hlastSide] using hsideAtLast
      have hc0 := parentCarrierChain_middle q hR c hcut T u
      rw [show openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val u =
        (⟨b,by omega⟩ : Fin (b+1)) from openSideCarrier_last (parent q c hcut)
          (regular_parent q hR c hcut) T.val] at hc0
      have hu : (⟨u.val+1,by have := u.isLt; omega⟩ : Fin (m+1))=last.castSucc := by
        apply Fin.ext
        change m-2+1=m-1
        omega
      rw [hu] at hc0
      have hc1 := parentCarrierChain_last q hR c hcut T
      have hv : (⟨m,by omega⟩ : Fin (m+1))=last.succ := by
        apply Fin.ext
        change m=m-1+1
        omega
      rw [hv] at hc1
      have he : edge (a:=a) (⟨b,by omega⟩ : Fin (b+1)) = ⟨a+b,by omega⟩ := rfl
      have hp : Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T last =
          q ⟨a+b+1,by omega⟩ := by
        change RetainedWords.vertex (parent q c hcut) (regular_parent q hR c hcut) T.val
          (start _) (openLast _ _ _) = _
        rw [open_vertex_last]
        have hpar : parent q c hcut ⟨b+1,by omega⟩=q ⟨a+b+1,by omega⟩ := by
          simpa only [Split.vertex,Fin.val_succ,Nat.add_assoc] using
            parent_succ q c hcut ⟨b,by omega⟩
        exact hpar
      constructor
      · rw [hc0,he]
        exact hsideLast
      · rw [hc1,hp]
        exact hterminal

/-- Under an explicit denominator condition for this adjacent pair, the supplied
lines intersect at the actual retained parent vertex. -/
theorem parent_vertex_supplied_line_intersection
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine)
    (hinc : ∀ e : Fin (a+b+1),
      lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0)
    (i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val))
    (hden : lineDenominator (L (parentCarrierChain q hR c hcut T i.castSucc))
      (L (parentCarrierChain q hR c hcut T i.succ))≠0) :
    lineIntersection (L (parentCarrierChain q hR c hcut T i.castSucc))
      (L (parentCarrierChain q hR c hcut T i.succ)) =
      Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i := by
  have hi := parent_vertex_supplied_line_incidence q hR c hcut T L hinc hterminal i
  symm
  apply lineIntersection_unique _ _ _ hden
  · exact hi.1
  · exact hi.2

/-- The canonical parent chart is a concrete instance of supplied-line incidence. -/
theorem parent_chart_line_incidence
    (i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val)) :
    lineValue (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc))
      (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i)=0 ∧
    lineValue (parentChartLines q (parentCarrierChain q hR c hcut T i.succ))
      (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i)=0 := by
  refine parent_vertex_supplied_line_incidence q hR c hcut T (parentChartLines q) ?_ ?_ i
  · intro e
    constructor
    · simpa only [parentChartLines,Sum.elim_inl,affinePoint_zero] using
        physicalLine_affine_value q e 0
    · simpa only [parentChartLines,Sum.elim_inl,affinePoint_one] using
        physicalLine_affine_value q e 1
  · simpa only [parentChartLines,Sum.elim_inr] using terminalLine_value q

end DirectGLSSW.ActiveArc.OpenCarrier




