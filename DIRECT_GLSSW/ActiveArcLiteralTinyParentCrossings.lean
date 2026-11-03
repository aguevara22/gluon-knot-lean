import ActiveArcLiteralTinyParentRegular
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry

private theorem before_crossing_avoids_parent
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a)
    (u:ℝ) (hu:0<u) (huc:u<leftParameter q c) :
    ∀e:Fin (b+1),¬edgeInterior (parent q c hcut) e (affinePoint (q 0) (q 1) u) := by
  intro e he
  have ha:0<a := cut_positive q c hcut
  have hfirst:edgeInterior q 0 (affinePoint (q 0) (q 1) u) :=
    ⟨u,hu,lt_trans huc (leftParameter_spec q c).2.1,rfl⟩
  have heOrig:edgeInterior q (edge e) (affinePoint (q 0) (q 1) u) := by
    apply (suffix_edgeInterior q e _).mp
    exact edgeInterior_subset (suffix q) (rightParameter q c)
      (le_of_lt (rightParameter_spec q c).1) (rightParameter_spec q c).2.1 e _ he
  have hepos:(0:Fin (a+b+1))<edge e := by change 0<a+e.val;omega
  let d:Crossing q := ⟨(0,edge e),hepos,⟨_,hfirst,heOrig⟩⟩
  have hd:leftParameter q d=u := by
    apply edge_parameter_unique q hR 0
    have hp:=crossingPoint_eq_of_mem_regular q hR d _ hfirst heOrig
    exact (leftParameter_spec q d).2.2.symm.trans hp
  have hmin:=hc.2 d rfl
  rw [hd] at hmin
  exact not_lt_of_ge hmin huc

theorem tinyParent_edgeInterior_succ
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ)
    (c:Crossing q) (hcut:c.val.2.val=a) (η:ℝ)
    (e:Fin (b+1)) (y:PlanarPoint ℝ) :
    edgeInterior (tinyParent q c hcut η) e.succ y ↔ edgeInterior (parent q c hcut) e y := by
  change (∃t:ℝ,0<t ∧ t<1 ∧ y=affinePoint
    (tinyParent q c hcut η e.castSucc.succ)
    (tinyParent q c hcut η e.succ.succ) t) ↔ _
  simp only [tinyParent_succ,edgeInterior]

/-- The new first segment is strictly before the first original crossing. -/
theorem tinyParent_no_first_crossing
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a)
    (η:ℝ) (hη:0<η) (hη1:η<1)
    (d:Crossing (tinyParent q c hcut η)) : d.val.1≠0 := by
  intro hd
  obtain⟨y,hy0,hy1⟩:=d.property.2
  rw [hd] at hy0
  have he:d.val.2≠0 := by
    have hh:=d.property.1
    rw [hd] at hh
    exact ne_of_gt hh
  obtain⟨e,he⟩:=Fin.exists_succ_eq_of_ne_zero he
  rw [←he] at hy1
  have hp:edgeInterior (parent q c hcut) e y :=
    (tinyParent_edgeInterior_succ q c hcut η e y).mp hy1
  obtain⟨s,hs,hs1,hys⟩:=hy0
  have hpoint:crossingPoint q c=affinePoint (q 0) (q 1) (leftParameter q c) := by
    simpa only [hc.1] using (leftParameter_spec q c).2.2
  change y=affinePoint (tinyParent q c hcut η 0) (tinyParent q c hcut η 1) s at hys
  rw [tinyParent_zero,tinyParent_one,hpoint] at hys
  have hy:y=affinePoint (q 0) (q 1) (leftParameter q c*((1-η)*(1-s)+s)) := by
    rw [hys]
    ext <;> simp [affinePoint] <;> ring
  rw [hy] at hp
  apply before_crossing_avoids_parent q hR c hc hcut _ ?_ ?_ e hp
  · apply mul_pos (leftParameter_spec q c).1
    have hm:0<(1-η)*(1-s):=mul_pos (by linarith) (by linarith)
    linarith
  · have hm:0<leftParameter q c*(η*(1-s)):=
      mul_pos (leftParameter_spec q c).1 (mul_pos hη (by linarith))
    nlinarith

/-- Actual tail crossings with both edge labels shifted by one. -/
def crossingFromParent
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ)
    (c:Crossing q) (hcut:c.val.2.val=a) (η:ℝ)
    (d:Crossing (parent q c hcut)) : Crossing (tinyParent q c hcut η) :=
  ⟨(d.val.1.succ,d.val.2.succ),by
    constructor
    · have hh:=d.property.1
      change d.val.1.val+1<d.val.2.val+1
      exact Nat.succ_lt_succ hh
    · obtain⟨y,hy0,hy1⟩:=d.property.2
      exact⟨y,(tinyParent_edgeInterior_succ q c hcut η _ _).mpr hy0,
        (tinyParent_edgeInterior_succ q c hcut η _ _).mpr hy1⟩⟩

theorem crossingFromParent_injective
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ)
    (c:Crossing q) (hcut:c.val.2.val=a) (η:ℝ) :
    Function.Injective (crossingFromParent q c hcut η) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.succ_inj.mp
    exact congrArg (fun x=>x.val.1) h
  · apply Fin.succ_inj.mp
    exact congrArg (fun x=>x.val.2) h

theorem crossingFromParent_surjective
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a)
    (η:ℝ) (hη:0<η) (hη1:η<1) :
    Function.Surjective (crossingFromParent q c hcut η) := by
  intro d
  have h0:=tinyParent_no_first_crossing q hR c hc hcut η hη hη1 d
  have h1:d.val.2≠0 := by
    have hh:=d.property.1
    exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hh)
  obtain⟨e,he⟩:=Fin.exists_succ_eq_of_ne_zero h0
  obtain⟨f,hf⟩:=Fin.exists_succ_eq_of_ne_zero h1
  have hef:e<f := by
    have hh:=d.property.1
    rw [←he,←hf] at hh
    exact Nat.lt_of_succ_lt_succ hh
  have hex:∃y,edgeInterior (parent q c hcut) e y ∧ edgeInterior (parent q c hcut) f y := by
    obtain⟨y,hy0,hy1⟩:=d.property.2
    rw [←he] at hy0
    rw [←hf] at hy1
    exact⟨y,(tinyParent_edgeInterior_succ q c hcut η e y).mp hy0,
      (tinyParent_edgeInterior_succ q c hcut η f y).mp hy1⟩
  refine⟨⟨(e,f),hef,hex⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext he hf

/-- Every actual crossing of the literal tiny parent is uniquely a parent crossing. -/
def tinyParentCrossingEquiv
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a)
    (η:ℝ) (hη:0<η) (hη1:η<1) :
    Crossing (tinyParent q c hcut η) ≃ Crossing (parent q c hcut) :=
  (Equiv.ofBijective (crossingFromParent q c hcut η)
    ⟨crossingFromParent_injective q c hcut η,
      crossingFromParent_surjective q hR c hc hcut η hη hη1⟩).symm

theorem crossingFromParent_point
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a)
    (η:ℝ) (hη:0<η) (hη1:η<1) (d:Crossing (parent q c hcut)) :
    crossingPoint (tinyParent q c hcut η) (crossingFromParent q c hcut η d)=
      crossingPoint (parent q c hcut) d := by
  apply crossingPoint_eq_of_mem_regular _ (regular_tinyParent q hR c hc hcut η hη hη1)
  · apply (tinyParent_edgeInterior_succ q c hcut η _ _).mpr
    exact⟨leftParameter _ d,(leftParameter_spec _ d).1,(leftParameter_spec _ d).2.1,
      (leftParameter_spec _ d).2.2⟩
  · apply (tinyParent_edgeInterior_succ q c hcut η _ _).mpr
    exact⟨rightParameter _ d,(rightParameter_spec _ d).1,(rightParameter_spec _ d).2.1,
      (rightParameter_spec _ d).2.2⟩

theorem crossingFromParent_leftParameter
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a)
    (η:ℝ) (hη:0<η) (hη1:η<1) (d:Crossing (parent q c hcut)) :
    leftParameter (tinyParent q c hcut η) (crossingFromParent q c hcut η d)=
      leftParameter (parent q c hcut) d := by
  apply edge_parameter_unique _ (regular_parent q hR c hcut) d.val.1
  have ht:=(leftParameter_spec _ (crossingFromParent q c hcut η d)).2.2
  have hp:=(leftParameter_spec _ d).2.2
  rw [crossingFromParent_point q hR c hc hcut η hη hη1 d] at ht
  change crossingPoint (parent q c hcut) d=affinePoint
    (tinyParent q c hcut η d.val.1.castSucc.succ)
    (tinyParent q c hcut η d.val.1.succ.succ) _ at ht
  simp only [tinyParent_succ] at ht
  exact ht.symm.trans hp

theorem crossingFromParent_rightParameter
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a)
    (η:ℝ) (hη:0<η) (hη1:η<1) (d:Crossing (parent q c hcut)) :
    rightParameter (tinyParent q c hcut η) (crossingFromParent q c hcut η d)=
      rightParameter (parent q c hcut) d := by
  apply edge_parameter_unique _ (regular_parent q hR c hcut) d.val.2
  have ht:=(rightParameter_spec _ (crossingFromParent q c hcut η d)).2.2
  have hp:=(rightParameter_spec _ d).2.2
  rw [crossingFromParent_point q hR c hc hcut η hη hη1 d] at ht
  change crossingPoint (parent q c hcut) d=affinePoint
    (tinyParent q c hcut η d.val.2.castSucc.succ)
    (tinyParent q c hcut η d.val.2.succ.succ) _ at ht
  simp only [tinyParent_succ] at ht
  exact ht.symm.trans hp

end DirectGLSSW.ActiveArc.LiteralTinyParent
