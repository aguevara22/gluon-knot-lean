import OriginalCarrierTransitivity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.ExposedChart

/-- Physical incidence alone is preserved; no auxiliary terminal line is an input. -/
theorem physical_moveStart_incidence {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (L : Fin (n+1) → CarrierLine)
    (hi : ∀ e, lineValue (L e) (q e.castSucc)=0 ∧ lineValue (L e) (q e.succ)=0)
    (t : ℝ) : ∀ e, lineValue (L e) (moveStart q t e.castSucc)=0 ∧
      lineValue (L e) (moveStart q t e.succ)=0 := by
  exact (supplied_moveStart_incidence q (Sum.elim L (fun _ => 0)) hi
    (by simp [lineValue,planarDet]) t).1

theorem physical_suffix_incidence {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (L : Fin (a+b+1) → CarrierLine)
    (hi : ∀ e, lineValue (L e) (q e.castSucc)=0 ∧ lineValue (L e) (q e.succ)=0) :
    ∀ e : Fin (b+1), lineValue (L (edge (a:=a) e)) (suffix q e.castSucc)=0 ∧
      lineValue (L (edge (a:=a) e)) (suffix q e.succ)=0 := by
  exact (supplied_suffix_incidence q (Sum.elim L (fun _ => 0)) hi
    (by simp [lineValue,planarDet])).1

theorem physical_parent_incidence {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (c : Crossing q) (hcut : c.val.2.val=a)
    (L : Fin (a+b+1) → CarrierLine)
    (hi : ∀ e, lineValue (L e) (q e.castSucc)=0 ∧ lineValue (L e) (q e.succ)=0) :
    ∀ e : Fin (b+1), lineValue (L (edge (a:=a) e)) (parent q c hcut e.castSucc)=0 ∧
      lineValue (L (edge (a:=a) e)) (parent q c hcut e.succ)=0 := by
  exact physical_moveStart_incidence (suffix q) (fun e => L (edge (a:=a) e))
    (physical_suffix_incidence q L hi) (rightParameter q c)

theorem physical_cut_incidence {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (e : Fin (n+2)) (L : Fin (n+2) → CarrierLine)
    (hi : ∀ i, lineValue (L i) (q i)=0 ∧ lineValue (L i) (q (cyclicSuccessor i))=0) :
    ∀ i : Fin (n+1), lineValue (L (edgeLabel e i)) (cutArc q e i.castSucc)=0 ∧
      lineValue (L (edgeLabel e i)) (cutArc q e i.succ)=0 := by
  intro i
  change lineValue (L (edgeLabel e i)) (q (cyclicVertexEquiv e i.castSucc))=0 ∧
    lineValue (L (edgeLabel e i)) (q (cyclicVertexEquiv e i.succ))=0
  rw [edgeLabel_successor]
  exact hi (edgeLabel e i)

end DirectGLSSW.CyclicCarrierClearing




