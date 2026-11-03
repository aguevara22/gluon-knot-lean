import ActiveArcOpenParent

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)

theorem suffixCrossingToOriginal_rightParameter (hR : Regular q) (d : Crossing (suffix q)) :
    rightParameter q (suffixCrossingToOriginal q d)=rightParameter (suffix q) d := by
  apply edge_parameter_unique q hR (edge d.val.2)
  have hn := (rightParameter_spec (suffix q) d).2.2
  simp only [suffix,vertex_castSucc,vertex_succ] at hn
  exact (rightParameter_spec q (suffixCrossingToOriginal q d)).2.2.symm.trans
    ((suffixCrossingToOriginal_point q hR d).trans hn)

theorem parentCrossingToOriginal_rightParameter (hR : Regular q) (c : Crossing q)
    (hc : c.val.2.val=a) (d : Crossing (parent q c hc)) :
    rightParameter q (parentCrossingToOriginal q c hc d)=rightParameter (parent q c hc) d := by
  unfold parentCrossingToOriginal
  rw [suffixCrossingToOriginal_rightParameter q hR]
  exact crossingEquiv_rightParameter (suffix q) (regular_suffix q hR) (rightParameter q c)
    (le_of_lt (rightParameter_spec q c).1) (rightParameter_spec q c).2.1 d

theorem parentCrossingToOriginal_leftParameter (hR : Regular q) (c : Crossing q)
    (hc : c.val.2.val=a) (d : Crossing (parent q c hc)) (hd : d.val.1≠0) :
    leftParameter q (parentCrossingToOriginal q c hc d)=leftParameter (parent q c hc) d := by
  unfold parentCrossingToOriginal
  rw [suffixCrossingToOriginal_leftParameter q hR]
  exact crossingEquiv_leftParameter (suffix q) (regular_suffix q hR) (rightParameter q c)
    (le_of_lt (rightParameter_spec q c).1) (rightParameter_spec q c).2.1 d hd

theorem parentCrossingToOriginal_firstParameter (hR : Regular q) (c : Crossing q)
    (hc : c.val.2.val=a) (d : Crossing (parent q c hc)) (hd : d.val.1=0) :
    leftParameter q (parentCrossingToOriginal q c hc d)=rightParameter q c+
      (1-rightParameter q c)*leftParameter (parent q c hc) d := by
  unfold parentCrossingToOriginal
  rw [suffixCrossingToOriginal_leftParameter q hR]
  exact crossingEquiv_firstParameter (suffix q) (regular_suffix q hR) (rightParameter q c)
    (le_of_lt (rightParameter_spec q c).1) (rightParameter_spec q c).2.1 d hd

/-- The carrier embedding also preserves the number of selected physical labels.
Nonalternation and joint child-parent refinement are separate obligations. -/
def parentSupport (c : Crossing q) (hc : c.val.2.val=a)
    (S : Finset (Crossing (parent q c hc))) : Finset (Crossing q) :=
  S.map ⟨parentCrossingToOriginal q c hc,parentCrossingToOriginal_injective q c hc⟩

theorem parentSupport_card (c : Crossing q) (hc : c.val.2.val=a)
    (S : Finset (Crossing (parent q c hc))) : (parentSupport q c hc S).card=S.card :=
  Finset.card_map _

theorem parentSupport_mem (hR : Regular q) (c : Crossing q) (hc : c.val.2.val=a)
    (S : Finset (Crossing (parent q c hc))) (d : Crossing q) (hd : d∈parentSupport q c hc S) :
    InParent q c d := by
  obtain ⟨e,_,he⟩:=Finset.mem_map.mp hd
  rw [← he]
  exact parentCrossingToOriginal_inParent q hR c hc e

theorem parentSupport_excludes_cut (hR : Regular q) (c : Crossing q) (hc : c.val.2.val=a)
    (S : Finset (Crossing (parent q c hc))) : c∉parentSupport q c hc S := by
  intro hm
  exact crossing_not_inParent q c hc (parentSupport_mem q hR c hc S c hm)

end DirectGLSSW.ActiveArc.Split
