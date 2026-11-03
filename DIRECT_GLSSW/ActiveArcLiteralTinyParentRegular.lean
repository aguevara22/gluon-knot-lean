import ActiveArcLiteralTinyParent

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry

private theorem cons_edgeInterior_succ {n : ℕ} (p : Fin (n+2) → PlanarPoint ℝ)
    (x y : PlanarPoint ℝ) (e : Fin (n+1)) :
    edgeInterior (Fin.cons x p) e.succ y ↔ edgeInterior p e y := by
  change (∃t:ℝ,0<t ∧ t<1 ∧ y=affinePoint ((Fin.cons x p : Fin (n+3) → PlanarPoint ℝ) e.castSucc.succ)
    ((Fin.cons x p : Fin (n+3) → PlanarPoint ℝ) e.succ.succ) t) ↔ _
  simp only [Fin.cons_succ,edgeInterior]

private theorem cons_edgeInterior_zero {n : ℕ} (p : Fin (n+2) → PlanarPoint ℝ)
    (x y : PlanarPoint ℝ) :
    edgeInterior (Fin.cons x p) 0 y ↔ OnOpenSegment x (p 0) y := by
  change (∃t:ℝ,0<t ∧ t<1 ∧ y=affinePoint x (p 0) t) ↔ _
  rfl

private theorem regular_cons {n : ℕ} (p : Fin (n+2) → PlanarPoint ℝ)
    (hp : Regular p) (x : PlanarPoint ℝ) (hn : p 0-x≠0)
    (hfree : ∀e:Fin (n+1),∀y,OnOpenSegment x (p 0) y → ¬edgeInterior p e y)
    (hanchors : ∀i:Fin (n+2),i≠0 → ¬OnOpenSegment x (p 0) (p i))
    (hx : ∀e:Fin (n+1),¬edgeInterior p e x) : Regular (Fin.cons x p) := by
  constructor
  · intro e
    refine Fin.cases ?_ (fun e => ?_) e
    · simpa only [Fin.cons_zero,Fin.cons_succ] using hn
    · change p e.succ-p e.castSucc≠0
      exact hp.edge_nonzero e
  · intro e f hef y he hf
    induction e using Fin.cases with
    | zero =>
      induction f using Fin.cases with
      | zero =>
        exact False.elim (hef rfl)
      | succ f =>
        exact False.elim (hfree f y ((cons_edgeInterior_zero p x y).mp he)
          ((cons_edgeInterior_succ p x y f).mp hf))
    | succ e =>
      induction f using Fin.cases with
      | zero =>
        exact False.elim (hfree e y ((cons_edgeInterior_zero p x y).mp hf)
          ((cons_edgeInterior_succ p x y e).mp he))
      | succ f =>
        change planarDet (p e.succ-p e.castSucc) (p f.succ-p f.castSucc)≠0
        exact hp.transverse e f (fun h => hef (congrArg Fin.succ h)) y
          ((cons_edgeInterior_succ p x y e).mp he) ((cons_edgeInterior_succ p x y f).mp hf)
  · intro e f g y hef hfg hge h
    induction e using Fin.cases with
    | zero =>
      induction f using Fin.cases with
      | zero =>
        exact hef rfl
      | succ f =>
        exact hfree f y ((cons_edgeInterior_zero p x y).mp h.1)
          ((cons_edgeInterior_succ p x y f).mp h.2.1)
    | succ e =>
      induction f using Fin.cases with
      | zero =>
        exact hfree e y ((cons_edgeInterior_zero p x y).mp h.2.1)
          ((cons_edgeInterior_succ p x y e).mp h.1)
      | succ f =>
        induction g using Fin.cases with
        | zero =>
          exact hfree e y ((cons_edgeInterior_zero p x y).mp h.2.2)
            ((cons_edgeInterior_succ p x y e).mp h.1)
        | succ g =>
          exact hp.noTriple e f g y
            (fun he => hef (congrArg Fin.succ he)) (fun he => hfg (congrArg Fin.succ he))
            (fun he => hge (congrArg Fin.succ he))
            ⟨(cons_edgeInterior_succ p x y e).mp h.1,
              (cons_edgeInterior_succ p x y f).mp h.2.1,
              (cons_edgeInterior_succ p x y g).mp h.2.2⟩
  · intro e i hi0 hi1 hi
    induction e using Fin.cases with
    | zero =>
      induction i using Fin.cases with
      | zero =>
        exact hi0 rfl
      | succ i =>
        have hne:i≠0 := fun h => hi1 (congrArg Fin.succ h)
        exact hanchors i hne (by simpa only [Fin.cons_succ] using (cons_edgeInterior_zero p x _).mp hi)
    | succ e =>
      induction i using Fin.cases with
      | zero =>
        exact hx e ((cons_edgeInterior_succ p x _ e).mp hi)
      | succ i =>
        exact hp.anchor_avoid e i
          (fun h => hi0 (congrArg Fin.succ h)) (fun h => hi1 (congrArg Fin.succ h))
          (by simpa only [Fin.cons_succ] using (cons_edgeInterior_succ p x _ e).mp hi)

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

/-- Actual physical regularity of the literal tiny parent for the entire
punctured interval 0<eta<1. No support or genericity premise is assumed. -/
theorem regular_tinyParent
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a)
    (η:ℝ) (hη:0<η) (hη1:η<1) : Regular (tinyParent q c hcut η) := by
  let tc:=leftParameter q c
  let x:=affinePoint (crossingPoint q c) (q 0) η
  have htc:0<tc:=(leftParameter_spec q c).1
  have hpoint:crossingPoint q c=affinePoint (q 0) (q 1) tc := by
    simpa only [hc.1] using (leftParameter_spec q c).2.2
  have hxpoint:x=affinePoint (q 0) (q 1) (tc*(1-η)) := by
    dsimp [x]
    rw [hpoint]
    ext <;> simp [affinePoint] <;> ring
  have hqne:q 0≠q 1 := by
    intro h
    have hz:=hR.edge_nonzero 0
    apply hz
    change q 1-q 0=0
    rw [h,sub_self]
  have hn:parent q c hcut 0-x≠0 := by
    apply sub_ne_zero.mpr
    rw [parent_zero q c hcut]
    intro he
    rw [hpoint,hxpoint] at he
    have hh:=affinePoint_injective (q 0) (q 1) hqne he
    nlinarith [mul_pos htc hη]
  have hx:∀e:Fin (b+1),¬edgeInterior (parent q c hcut) e x := by
    rw [hxpoint]
    exact before_crossing_avoids_parent q hR c hc hcut _ (mul_pos htc (by linarith))
      (by nlinarith [mul_pos htc hη])
  have hsegment:∀y,OnOpenSegment x (parent q c hcut 0) y →
      ∃u:ℝ,0<u ∧ u<tc ∧ y=affinePoint (q 0) (q 1) u := by
    intro y hy
    obtain⟨s,hs,hs1,hys⟩:=hy
    rw [parent_zero q c hcut,hpoint,hxpoint] at hys
    refine⟨tc*((1-η)*(1-s)+s),?_,?_,?_⟩
    · apply mul_pos htc
      have hm:0<(1-η)*(1-s):=mul_pos (by linarith) (by linarith)
      linarith
    · have hm:0<tc*(η*(1-s)):=mul_pos htc (mul_pos hη (by linarith))
      nlinarith
    · rw [hys]
      ext <;> simp [affinePoint] <;> ring
  have hfree:∀e:Fin (b+1),∀y,OnOpenSegment x (parent q c hcut 0) y →
      ¬edgeInterior (parent q c hcut) e y := by
    intro e y hy
    obtain⟨u,hu,huc,rfl⟩:=hsegment y hy
    exact before_crossing_avoids_parent q hR c hc hcut u hu huc e
  have hanchors:∀i:Fin (b+2),i≠0 → ¬OnOpenSegment x (parent q c hcut 0) (parent q c hcut i) := by
    intro i hi hy
    obtain⟨u,hu,huc,hpointi⟩:=hsegment _ hy
    obtain⟨j,rfl⟩:=Fin.exists_succ_eq_of_ne_zero hi
    rw [parent_succ] at hpointi
    have ha:0<a:=cut_positive q c hcut
    have hidx0:vertex j.succ≠(0:Fin (a+b+2)):=by
      intro he;have hh:=congrArg Fin.val he;change a+(j.val+1)=0 at hh;omega
    have hidx1:vertex j.succ≠(1:Fin (a+b+2)):=by
      intro he;have hh:=congrArg Fin.val he;change a+(j.val+1)=1 at hh;omega
    exact hR.anchor_avoid 0 (vertex j.succ) hidx0 hidx1
      ⟨u,hu,lt_trans huc (leftParameter_spec q c).2.1,hpointi⟩
  exact regular_cons (parent q c hcut) (regular_parent q hR c hcut) x hn hfree hanchors hx

/-- Uniform actual radius; no condition on a chosen moved arc is supplied. -/
theorem exists_regular_tinyParent_radius
    {a b:ℕ} (q:Fin (a+b+2)→PlanarPoint ℝ) (hR:Regular q)
    (c:Crossing q) (hc:FirstCrossing q c) (hcut:c.val.2.val=a) :
    ∃ρ:ℝ,0<ρ ∧ ∀η:ℝ,0<η → η<ρ → Regular (tinyParent q c hcut η) :=
  ⟨1,by norm_num,fun η hη hη1=>regular_tinyParent q hR c hc hcut η hη hη1⟩

end DirectGLSSW.ActiveArc.LiteralTinyParent
