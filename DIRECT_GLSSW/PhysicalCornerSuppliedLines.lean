import PhysicalCornerCarrierPairs
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc Cursor RetainedWords Primitive AuxiliaryCarrierChart
attribute [local instance] Classical.propDecidable

lemma cornerCarrierPair_zero {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hQ : Regular q) (U : Support (dropWord q h) (dropWord_regular q h hQ)) :
    cornerCarrierPair q h hQ U (openFirst _ _ U.val)=
      (Sum.inl (dropEdge h 0),precedingLabel h) := by
  change ((eventCarrierChain (dropWord q h) (dropWord_regular q h hQ) U (openFirst _ _ U.val)).map _ _,_)=_
  exact congrArg (fun x => (Sum.map (dropEdge h) id x,precedingLabel h))
    (eventCarrierChain_zero (dropWord q h) (dropWord_regular q h hQ) U)

lemma cornerCarrierPair_middle {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hQ : Regular q) (U : Support (dropWord q h) (dropWord_regular q h hQ))
    (i : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val))
    (hi0 : 0 < i.val) (hi1 : i.val+1<openCount (dropWord q h) (dropWord_regular q h hQ) U.val) :
    cornerCarrierPair q h hQ U i=
      (Sum.inl (dropEdge h (openSideCarrier _ _ U.val ⟨i.val-1,by omega⟩)),
       Sum.inl (dropEdge h (openSideCarrier _ _ U.val ⟨i.val,by omega⟩))) := by
  simp only [cornerCarrierPair,if_neg (Nat.ne_of_gt hi0),cornerCarrierChain,eventCarrierChain,
    dif_pos (show i.val-1<openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1 by omega),
    dif_pos (show i.val<openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1 by omega),Sum.map_inl]

lemma cornerCarrierPair_last {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hQ : Regular q) (U : Support (dropWord q h) (dropWord_regular q h hQ)) :
    cornerCarrierPair q h hQ U (openLast _ _ U.val)=
      (Sum.inl (dropEdge h ⟨M,by omega⟩),Sum.inr ()) := by
  have hm := open_count_ge_two (dropWord q h) (dropWord_regular q h hQ) U.val
  have hp : (openLast (dropWord q h) (dropWord_regular q h hQ) U.val).val≠0 := by
    change openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1≠0;omega
  have hl : ¬(openLast (dropWord q h) (dropWord_regular q h hQ) U.val).val<
      openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1 := lt_irrefl _
  have ht : (openLast (dropWord q h) (dropWord_regular q h hQ) U.val).val-1<
      openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1 := by
    change openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1-1<_
    omega
  simp only [cornerCarrierPair,if_neg hp,cornerCarrierChain,eventCarrierChain,dif_pos ht,dif_neg hl,Sum.map_inl,Sum.map_inr]
  have he : (⟨(openLast (dropWord q h) (dropWord_regular q h hQ) U.val).val-1,ht⟩ :
      Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1))=
      ⟨openCount (dropWord q h) (dropWord_regular q h hQ) U.val-2,by omega⟩ := Fin.ext (by change openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1-1=openCount (dropWord q h) (dropWord_regular q h hQ) U.val-2;omega)
  rw [he,openSideCarrier_last]

private lemma affine_incidence (L : CarrierLine) (x y : PlanarPoint ℝ) (t : ℝ)
    (hx : lineValue L x=0) (hy : lineValue L y=0) : lineValue L (affinePoint x y t)=0 := by
  have he : lineValue L (affinePoint x y t)=(1-t)*lineValue L x+t*lineValue L y := by
    simp only [lineValue,planarDet,affinePoint];ring
  rw [he,hx,hy];ring

/-- Actual supplied lines, including the ORIGINAL preceding edge at the root.
No Crossing is required, so empty crossing carriers are covered. -/
theorem corner_pair_supplied_incidence {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hd : 0<d) (hQ : Regular q)
    (U : Support (dropWord q h) (dropWord_regular q h hQ))
    (L : Fin (N+1) ⊕ Unit → CarrierLine)
    (hinc : ∀ e : Fin (N+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨N+1,by omega⟩)=0)
    (i : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val)) :
    lineValue (L (cornerCarrierPair q h hQ U i).1) (OpenVertex _ _ U i)=0 ∧
      lineValue (L (cornerCarrierPair q h hQ U i).2) (OpenVertex _ _ U i)=0 := by
  let p := dropWord q h
  let hp := dropWord_regular q h hQ
  have hiN : i.val < openCount p hp U.val := i.isLt
  by_cases hi0 : i.val=0
  · have he : i=openFirst p hp U.val := Fin.ext hi0
    subst i
    rw [cornerCarrierPair_zero]
    change lineValue (L (Sum.inl (dropEdge h 0))) (OpenVertex p hp U (openFirst p hp U.val))=0 ∧
      lineValue (L (precedingLabel h)) (OpenVertex p hp U (openFirst p hp U.val))=0
    have hw : OpenVertex p hp U (openFirst p hp U.val)=p 0 := open_vertex_first p hp U.val
    rw [hw]
    have hv : (⟨d-1,by omega⟩ : Fin (N+1)).succ=dropVertex h 0 := Fin.ext (by dsimp [dropVertex];omega)
    exact ⟨(hinc (dropEdge h 0)).1,by simpa only [precedingLabel,p,dropWord,hv] using (hinc ⟨d-1,by omega⟩).2⟩
  · have hi : 0 < i.val := Nat.pos_of_ne_zero hi0
    by_cases hi1 : i.val+1<openCount p hp U.val
    · rw [cornerCarrierPair_middle q h hQ U i hi hi1]
      let u : Fin (openCount p hp U.val-1) := ⟨i.val-1,by omega⟩
      let v : Fin (openCount p hp U.val-1) := ⟨i.val,by omega⟩
      obtain ⟨s,t,_,_,_,_,ht⟩ := openSideCarrier_physical p hp U.val u
      obtain ⟨r,w,_,_,_,hr,_⟩ := openSideCarrier_physical p hp U.val v
      have hiu : (⟨u.val+1,by have := u.isLt;omega⟩ : Fin (openCount p hp U.val))=i := Fin.ext (by dsimp [u];omega)
      rw [hiu] at ht
      constructor
      · change lineValue (L (Sum.inl (dropEdge h (openSideCarrier p hp U.val u)))) (RetainedWords.vertex p hp U.val (start p) i)=0
        rw [ht]
        exact affine_incidence _ _ _ _ (hinc _).1 (hinc _).2
      · change lineValue (L (Sum.inl (dropEdge h (openSideCarrier p hp U.val v)))) (RetainedWords.vertex p hp U.val (start p) i)=0
        rw [hr]
        exact affine_incidence _ _ _ _ (hinc _).1 (hinc _).2
    · have he : i=openLast p hp U.val := Fin.ext (by change i.val=openCount p hp U.val-1;have := i.isLt;omega)
      subst i
      rw [cornerCarrierPair_last]
      change lineValue (L (Sum.inl (dropEdge h ⟨M,by omega⟩))) (OpenVertex p hp U (openLast p hp U.val))=0 ∧
        lineValue (L (Sum.inr ())) (OpenVertex p hp U (openLast p hp U.val))=0
      have hw : OpenVertex p hp U (openLast p hp U.val)=p ⟨M+1,by omega⟩ := open_vertex_last p hp U.val
      rw [hw]
      have hv : dropVertex h ⟨M+1,by omega⟩=(⟨N+1,by omega⟩:Fin (N+2)) := Fin.ext (by dsimp [dropVertex];omega)
      exact ⟨(hinc (dropEdge h ⟨M,by omega⟩)).2,by simpa only [p,dropWord,hv] using hterminal⟩

theorem corner_pair_supplied_intersection {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hd : 0<d) (hQ : Regular q)
    (U : Support (dropWord q h) (dropWord_regular q h hQ))
    (L : Fin (N+1) ⊕ Unit → CarrierLine)
    (hinc : ∀ e : Fin (N+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨N+1,by omega⟩)=0)
    (i : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val))
    (hden : lineDenominator (L (cornerCarrierPair q h hQ U i).1) (L (cornerCarrierPair q h hQ U i).2)≠0) :
    lineIntersection (L (cornerCarrierPair q h hQ U i).1)
      (L (cornerCarrierPair q h hQ U i).2)=OpenVertex _ _ U i := by
  have hh := corner_pair_supplied_incidence q h hd hQ U L hinc hterminal i
  exact (lineIntersection_unique _ _ _ hden hh.1 hh.2).symm
end DirectGLSSW.ActiveArc.OpenCarrier
