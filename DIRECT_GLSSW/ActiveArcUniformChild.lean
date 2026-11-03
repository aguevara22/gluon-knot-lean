import ActiveArcChildTangentScaling

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open DirectGLSSW Cursor

private theorem det_smul_smul (s t : ℝ) (u v : PlanarPoint ℝ) :
    planarDet (s • u) (t • v) = (s*t)*planarDet u v := by
  simp [planarDet]
  ring

private theorem canonical_under_det_neg
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (c : Crossing q) (hc : FirstCrossing q c) (hG1 : cyclicNoncollinear q)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1) :
    planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc)<0 := by
  have hs := ((polygonCrossingOfArc_first_sign q c hc hG1).2.2.2.2.2).mpr hu
  by_contra hn
  simp only [scalarSignValue,hn,if_false] at hs
  split_ifs at hs <;> norm_num at hs

/-- The actual child closing corner is left at a canonical first-under encounter.
The incoming and outgoing sides are positive shortenings of right and first. -/
theorem child_closing_turn_pos
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1) :
    0<planarDet (cyclicTangent (child q hR c hc.1 hcut) ⟨a,by omega⟩)
      (cyclicTangent (child q hR c hc.1 hcut) 0) := by
  obtain ⟨s,hs,he⟩ := child_tangent_positive_scaling q hR c hc.1 hcut ⟨a,by omega⟩
  obtain ⟨t,ht,hf⟩ := child_tangent_positive_scaling q hR c hc.1 hcut 0
  rw [he,hf,det_smul_smul]
  apply mul_pos (mul_pos hs ht)
  have hright : childEdge (b:=b) (⟨a,by omega⟩ : Fin (a+1))=c.val.2 := Fin.ext hcut.symm
  rw [hright]
  change 0<planarDet (q c.val.2.succ-q c.val.2.castSucc) (q 1-q 0)
  have hh := canonical_under_det_neg q c hc hG1 hu
  have hswap : planarDet (q c.val.2.succ-q c.val.2.castSucc) (q 1-q 0)=
      -planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc) := by
    simp [planarDet]
    ring
  rw [hswap]
  exact neg_pos.mpr hh

/-- Actual source prefix corners q1 through qa are left, so every child corner
is left after the canonical first-under cut. This includes both shortened ends. -/
theorem child_all_turns_pos
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0<planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) :
    ∀ e : Fin (a+1), 0<planarDet (cyclicTangent (child q hR c hc.1 hcut) e)
      (cyclicTangent (child q hR c hc.1 hcut) (cyclicSuccessor e)) := by
  intro e
  by_cases hea : e.val=a
  · have he : e=(⟨a,by omega⟩ : Fin (a+1)) := Fin.ext hea
    rw [child_last_successor e hea,he]
    exact child_closing_turn_pos q hR c hc hcut hG1 hu
  · have hel : e.val<a := by have := e.isLt;omega
    obtain ⟨s,hs,he⟩ := child_tangent_positive_scaling q hR c hc.1 hcut e
    obtain ⟨t,ht,hf⟩ := child_tangent_positive_scaling q hR c hc.1 hcut (cyclicSuccessor e)
    rw [he,hf,det_smul_smul]
    apply mul_pos (mul_pos hs ht)
    let i : Fin (a+b) := ⟨e.val,by omega⟩
    have h1 : childEdge (b:=b) e=i.castSucc := rfl
    have h2 : childEdge (b:=b) (cyclicSuccessor e)=i.succ :=
      Fin.ext (child_successor_val e hel)
    rw [h1,h2]
    exact hleft i hel

/-- Literal active child and parent vertex counts. No smoothing-orbit count
is substituted for the source arc/polygon counts. -/
theorem child_parent_vertex_count
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    (List.ofFn (child q hR c hc.1 hcut)).length +
      (List.ofFn (parent q c hcut)).length = (List.ofFn q).length+1 := by
  simp only [List.length_ofFn]
  omega

/-- Whole source uniform-child/count conclusion for the actual first-under cut. -/
theorem first_under_uniform_child_and_count
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0<planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) :
    (0<planarDet (cyclicTangent (child q hR c hc.1 hcut) ⟨a,by omega⟩)
      (cyclicTangent (child q hR c hc.1 hcut) 0)) ∧
    (∀ e : Fin (a+1), 0<planarDet (cyclicTangent (child q hR c hc.1 hcut) e)
      (cyclicTangent (child q hR c hc.1 hcut) (cyclicSuccessor e))) ∧
    (List.ofFn (child q hR c hc.1 hcut)).length +
      (List.ofFn (parent q c hcut)).length = (List.ofFn q).length+1 :=
  ⟨child_closing_turn_pos q hR c hc hcut hG1 hu,
    child_all_turns_pos q hR c hc hcut hG1 hu hleft,
    child_parent_vertex_count q hR c hc hcut⟩





end DirectGLSSW.ActiveArc.Split
