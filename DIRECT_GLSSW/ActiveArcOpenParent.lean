import ActiveArcSuffix

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)

/-- The actual parent, obtained by cutting the physical edge a at c. -/
def parent (c : Crossing q) (_hc : c.val.2.val=a) : Fin (b+2) → PlanarPoint ℝ :=
  moveStart (suffix q) (rightParameter q c)

@[simp] theorem parent_succ (c : Crossing q) (hc : c.val.2.val=a) (i : Fin (b+1)) :
    parent q c hc i.succ=q (vertex i.succ) := moveStart_succ _ _ _

theorem parent_zero (c : Crossing q) (hc : c.val.2.val=a) :
    parent q c hc 0=crossingPoint q c := by
  have he : edge (a:=a) (b:=b) 0=c.val.2 := by apply Fin.ext;simpa only [edge,Nat.add_zero] using hc.symm
  change moveStart (suffix q) (rightParameter q c) 0=_
  rw [moveStart_zero]
  have hv0 : vertex (a:=a) (b:=b) 0=c.val.2.castSucc := congrArg Fin.castSucc he
  have hv1 : vertex (a:=a) (b:=b) 1=c.val.2.succ := (vertex_succ (a:=a) (0 : Fin (b+1))).trans (congrArg Fin.succ he)
  simpa only [suffix,hv0,hv1] using (rightParameter_spec q c).2.2.symm

/-- Although the full arc at c is singular, the actual open parent is regular:
a new parent crossing at c would be a forbidden third original physical edge. -/
theorem parent_parameter_not_critical (hR : Regular q) (c : Crossing q)
    (hc : c.val.2.val=a) : rightParameter q c∉criticalParameters (suffix q) := by
  intro ht
  obtain ⟨d,hd,hp⟩:=(mem_criticalParameters (suffix q) _).mp ht
  have hx : crossingPoint (suffix q) d=crossingPoint q c := by
    have hz := (leftParameter_spec (suffix q) d).2.2
    rw [hd,hp] at hz
    exact hz.trans (parent_zero q c hc)
  have heq : suffixCrossingToOriginal q d=c :=
    crossingPoint_injective q hR.noTriple ((suffixCrossingToOriginal_point q hR d).trans hx)
  have he := congrArg (fun z : Crossing q => z.val.1.val) heq
  change a+d.val.1.val=c.val.1.val at he
  have hdv : d.val.1.val=0 := congrArg Fin.val hd
  have hlt := c.property.1
  change c.val.1.val<c.val.2.val at hlt
  omega

theorem regular_parent (hR : Regular q) (c : Crossing q) (hc : c.val.2.val=a) :
    Regular (parent q c hc) :=
  regular_moveStart (suffix q) (regular_suffix q hR) (rightParameter q c)
    (le_of_lt (rightParameter_spec q c).1) (rightParameter_spec q c).2.1
    (parent_parameter_not_critical q hR c hc)

theorem suffixCrossingToOriginal_leftParameter (hR : Regular q) (d : Crossing (suffix q)) :
    leftParameter q (suffixCrossingToOriginal q d)=leftParameter (suffix q) d := by
  apply edge_parameter_unique q hR (edge d.val.1)
  have hn := (leftParameter_spec (suffix q) d).2.2
  simp only [suffix,vertex_castSucc,vertex_succ] at hn
  exact (leftParameter_spec q (suffixCrossingToOriginal q d)).2.2.symm.trans
    ((suffixCrossingToOriginal_point q hR d).trans hn)

def parentCrossingToOriginal (c : Crossing q) (hc : c.val.2.val=a) (d : Crossing (parent q c hc)) : Crossing q :=
  suffixCrossingToOriginal q
    (crossingToOriginal (suffix q) (rightParameter q c)
      (le_of_lt (rightParameter_spec q c).1) (rightParameter_spec q c).2.1 d)

@[simp] theorem parentCrossingToOriginal_edges (c : Crossing q) (hc : c.val.2.val=a) (d : Crossing (parent q c hc)) :
    (parentCrossingToOriginal q c hc d).val=(edge d.val.1,edge d.val.2) := rfl

theorem parentCrossingToOriginal_injective (c : Crossing q) (hc : c.val.2.val=a) :
    Function.Injective (parentCrossingToOriginal q c hc) := by
  intro d e h;apply Subtype.ext;apply Prod.ext
  · apply edge_injective;exact congrArg (fun z : Crossing q => z.val.1) h
  · apply edge_injective;exact congrArg (fun z : Crossing q => z.val.2) h

theorem parentCrossingToOriginal_point (hR : Regular q) (c : Crossing q) (hc : c.val.2.val=a)
    (d : Crossing (parent q c hc)) :
    crossingPoint q (parentCrossingToOriginal q c hc d)=crossingPoint (parent q c hc) d := by
  unfold parentCrossingToOriginal
  rw [suffixCrossingToOriginal_point q hR]
  exact crossingToOriginal_point (suffix q) (regular_suffix q hR) (rightParameter q c)
    (le_of_lt (rightParameter_spec q c).1) (rightParameter_spec q c).2.1 d

/-- The original crossing has both visits after the cut on physical edge a. -/
def InParent (c d : Crossing q) : Prop :=
  a≤d.val.1.val ∧ (d.val.1.val=a → rightParameter q c<leftParameter q d)

theorem parentCrossingToOriginal_inParent (hR : Regular q) (c : Crossing q) (hc : c.val.2.val=a)
    (d : Crossing (parent q c hc)) : InParent q c (parentCrossingToOriginal q c hc d) := by
  constructor
  · change a≤a+d.val.1.val;omega
  · intro he
    have hd : d.val.1=0 := by apply Fin.ext;change a+d.val.1.val=a at he;change d.val.1.val=0;omega
    have hh:=crossingToOriginal_survives (suffix q) (regular_suffix q hR) (rightParameter q c)
      (le_of_lt (rightParameter_spec q c).1) (rightParameter_spec q c).2.1 d hd
    unfold parentCrossingToOriginal
    rw [suffixCrossingToOriginal_leftParameter q hR]
    exact hh

theorem parentCrossing_range (hR : Regular q) (c : Crossing q) (hc : c.val.2.val=a) (d : Crossing q) :
    (∃ e, parentCrossingToOriginal q c hc e=d) ↔ InParent q c d := by
  constructor
  · rintro ⟨e,rfl⟩;exact parentCrossingToOriginal_inParent q hR c hc e
  · intro hd
    obtain ⟨e,he⟩:=(suffixCrossing_range q d).mpr hd.1
    have hs : Survives (suffix q) (rightParameter q c) e := by
      intro he0
      have heval : d.val.1.val=a := by
        have hh:=congrArg (fun z : Crossing q => z.val.1.val) he
        change a+e.val.1.val=d.val.1.val at hh
        rw [he0] at hh;simpa only [Fin.val_zero,Nat.add_zero] using hh.symm
      have hh:=hd.2 heval
      rw [← he,suffixCrossingToOriginal_leftParameter q hR] at hh
      exact hh
    let z := crossingFromOriginal (suffix q) (rightParameter q c)
      (rightParameter_spec q c).2.1 e hs
    refine ⟨z,?_⟩
    exact he

/-- Exact physical parent carrier, with no artificial closure crossing sites. -/
def parentCrossingEquiv (hR : Regular q) (c : Crossing q) (hc : c.val.2.val=a) :
    Crossing (parent q c hc) ≃ {d : Crossing q // InParent q c d} :=
  Equiv.ofBijective (fun e => ⟨parentCrossingToOriginal q c hc e,
    parentCrossingToOriginal_inParent q hR c hc e⟩) ⟨by
    intro d e h;exact parentCrossingToOriginal_injective q c hc (congrArg Subtype.val h),by
    intro d
    obtain ⟨e,he⟩:=(parentCrossing_range q hR c hc d.val).mpr d.property
    exact ⟨e,Subtype.ext he⟩⟩

theorem crossing_not_inParent (c : Crossing q) (hc : c.val.2.val=a) : ¬ InParent q c c := by
  intro h;have hh:=c.property.1;change c.val.1.val<c.val.2.val at hh;have hh':=h.1;omega

end DirectGLSSW.ActiveArc.Split
