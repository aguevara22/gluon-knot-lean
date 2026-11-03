import DirectGLSSW.HOMFLY.HOMFLYSignedDiagramIso
import DirectGLSSW.HOMFLY.HOMFLYSmoothEquivSwitchFacts

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY

theorem smoothArcLabelEquiv_refl (D : PLLinkDiagram) :
    smoothArcLabelEquiv (SignedDiagramIso.refl D) = Equiv.refl _ := by
  ext e
  simp [smoothArcLabelEquiv, SignedDiagramIso.refl, Equiv.sumCongr_apply]

theorem smoothCrossingLabelEquiv_refl (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    smoothCrossingLabelEquiv (SignedDiagramIso.refl D) c = Equiv.refl _ := by
  ext e
  simp [smoothCrossingLabelEquiv, retainedCrossingEquiv,
    SignedDiagramIso.refl, Equiv.trans_apply]


/-- Switching at a crossing distinct from the smoothing site commutes with
the smoothed signed combinatorial data. The child crossing is tracked through
the actual deleted-label equivalence. -/
noncomputable def switchSmoothSignedDiagramIso (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    SignedDiagramIso
      (smoothCrossing (switchCrossing D d) c)
      (switchCrossing (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, fun h => hcd h.symm⟩)) where
  arcEquiv := Equiv.refl _
  crossingEquiv := Equiv.refl _
  incoming_map := by
    intro x i
    change smoothIncoming (switchCrossing D d) c x i =
      smoothIncoming D c x i
    exact congrFun (congrFun (smoothIncoming_switch D d c) x) i
  outgoing_map := by
    intro x i
    change smoothOutgoing (switchCrossing D d) c x i =
      smoothOutgoing D c x i
    exact congrFun (congrFun (smoothOutgoing_switch D d c) x) i
  continuation_map := by
    intro e
    change smoothContinuation (switchCrossing D d) c e =
      smoothContinuation D c e
    exact congrArg (fun f : Equiv.Perm (Fin (D.nArc + 2)) => f e)
      (smoothContinuation_switch D d c)
  through_map := by
    intro x
    change smoothThrough (switchCrossing D d) c x =
      smoothThrough D c x
    exact congrFun (smoothThrough_switch D d c) x
  overBranch_map := by
    intro x
    simp only [smoothOverBranch]
    rw [smoothCrossingEquiv_switch]
    simp only [switchCrossing, Equiv.refl_apply]
    let E0 := smoothCrossingEquiv D c
    let k := E0 ⟨d, fun h => hcd h.symm⟩
    let old := E0.symm x
    have hx : old.val = d ↔ x = k := by
      constructor
      · intro hv
        have hold : old = ⟨d, fun h => hcd h.symm⟩ := Subtype.ext hv
        calc
          x = E0 old := (E0.apply_symm_apply x).symm
          _ = E0 ⟨d, fun h => hcd h.symm⟩ := congrArg E0 hold
          _ = k := rfl
      · intro hv
        have h' := congrArg E0.symm hv
        simpa [old, k] using congrArg Subtype.val h'
    change Function.update D.overBranch d (otherBranch (D.overBranch d)) old.val =
      Function.update (fun y => D.overBranch (E0.symm y).val) k
        (otherBranch (D.overBranch (E0.symm k).val)) x
    by_cases hk : x = k
    · have hd : old.val = d := hx.mpr hk
      simp [switchCrossing, Function.update_apply, hk, hd, old, k, E0]
    · have hd : old.val ≠ d := fun h => hk (hx.mp h)
      simp [switchCrossing, Function.update_apply, hk, hd, old, k, E0]
  crossingSign_map := by
    intro x
    let E0 := smoothCrossingEquiv D c
    let k := E0 ⟨d, fun h => hcd h.symm⟩
    let old := E0.symm x
    have hlabel : old.val = d ↔ x = k := by
      constructor
      · intro hv
        have hold : old = ⟨d, fun h => hcd h.symm⟩ := Subtype.ext hv
        calc
          x = E0 old := (E0.apply_symm_apply x).symm
          _ = E0 ⟨d, fun h => hcd h.symm⟩ := congrArg E0 hold
          _ = k := rfl
      · intro hv
        have h' := congrArg E0.symm hv
        simpa [old, k] using congrArg Subtype.val h'
    have hlabelD :
        smoothCrossingEquiv D c ⟨old.val, old.property⟩ = x := by
      exact E0.apply_symm_apply x
    have hlabelS :
        smoothCrossingEquiv (switchCrossing D d) c
          ⟨old.val, old.property⟩ = x := by
      rw [smoothCrossingEquiv_switch]
      exact hlabelD
    have hsource0 := crossingSign_smoothRetained
      (switchCrossing D d) c old.val old.property
    have htarget0 := crossingSign_smoothRetained D c old.val old.property
    have hsource :
        crossingSign (smoothCrossing (switchCrossing D d) c) x =
          crossingSign (switchCrossing D d) old.val := by
      rw [← hlabelS]
      exact hsource0
    have htarget :
        crossingSign (smoothCrossing D c) x =
          crossingSign D old.val := by
      rw [← hlabelD]
      exact htarget0
    have hparent :
        crossingSign (switchCrossing D d) old.val =
          if old.val = d then (crossingSign D old.val).reverse
            else crossingSign D old.val := by
      by_cases hd : old.val = d
      · rw [if_pos hd, hd, crossingSign_switchCrossing]
      · rw [if_neg hd, crossingSign_switchCrossing_of_ne D d old.val (hd)]
    have hchild :
        crossingSign (switchCrossing (smoothCrossing D c) k) x =
          if x = k then (crossingSign (smoothCrossing D c) x).reverse
            else crossingSign (smoothCrossing D c) x := by
      by_cases hk : x = k
      · rw [hk]
        rw [if_pos rfl, crossingSign_switchCrossing]
      · rw [if_neg hk, crossingSign_switchCrossing_of_ne
          (smoothCrossing D c) k x (hk)]
    calc
      crossingSign (smoothCrossing (switchCrossing D d) c) x =
          crossingSign (switchCrossing D d) old.val := hsource
      _ = if old.val = d then (crossingSign D old.val).reverse
            else crossingSign D old.val := hparent
      _ = if x = k then (crossingSign D old.val).reverse
            else crossingSign D old.val := by
          by_cases hk : x = k
          · have hd : old.val = d := hlabel.mpr hk
            simp [hk, hd]
          · have hd : old.val ≠ d := fun h => hk (hlabel.mp h)
            simp [hk, hd]
      _ = if x = k then (crossingSign (smoothCrossing D c) x).reverse
            else crossingSign (smoothCrossing D c) x := by rw [htarget]
      _ = crossingSign (switchCrossing (smoothCrossing D c) k) x := hchild.symm

end DirectGLSSW.HOMFLY



