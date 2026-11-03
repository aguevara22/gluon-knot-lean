import DirectGLSSW.HOMFLY.HOMFLYDoubleSmoothingLabels

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY


noncomputable def twiceSmoothFlatC (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    TwiceSmoothArcCode D ≃ SmoothArcCode (smoothCrossing D c) :=
  Equiv.sumCongr (smoothArcEquiv D) (Equiv.refl (Fin 2))

noncomputable def twiceSmoothFlatD (D : PLLinkDiagram) (d : Fin D.nCrossing) :
    TwiceSmoothArcCode D ≃ SmoothArcCode (smoothCrossing D d) :=
  Equiv.sumCongr (smoothArcEquiv D) (Equiv.refl (Fin 2))

noncomputable def twiceSmoothContinuationCodeC (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hdc : d ≠ c) : Equiv.Perm (TwiceSmoothArcCode D) :=
  (twiceSmoothFlatC D c).trans <|
    (smoothContinuationGeometryCode (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hdc⟩)).trans (twiceSmoothFlatC D c).symm

noncomputable def twiceSmoothContinuationCodeD (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) : Equiv.Perm (TwiceSmoothArcCode D) :=
  (twiceSmoothFlatD D d).trans <|
    (smoothContinuationGeometryCode (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩)).trans (twiceSmoothFlatD D d).symm


private theorem smoothChild_continuation_code (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x : SmoothArcCode D) :
    (smoothCrossing D c).continuation (smoothArcEquiv D x) =
      smoothArcEquiv D (smoothContinuationGeometryCode D c x) := by
  change smoothContinuation D c (smoothArcEquiv D x) = _
  simp [smoothContinuation, Equiv.trans_apply]

private theorem flatC_apply_old (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) :
    twiceSmoothFlatC D c (Sum.inl (Sum.inl e)) =
      Sum.inl (smoothArcEquiv D (Sum.inl e)) := rfl

private theorem flatC_apply_c_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    twiceSmoothFlatC D c (Sum.inl (Sum.inr i)) =
      Sum.inl (smoothArcEquiv D (Sum.inr i)) := rfl

private theorem flatC_apply_d_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    twiceSmoothFlatC D c (Sum.inr i) = Sum.inr i := rfl

private theorem flatD_apply_old (D : PLLinkDiagram) (d : Fin D.nCrossing)
    (e : Fin D.nArc) :
    twiceSmoothFlatD D d (Sum.inl (Sum.inl e)) =
      Sum.inl (smoothArcEquiv D (Sum.inl e)) := rfl

private theorem flatD_apply_c_connector (D : PLLinkDiagram) (d : Fin D.nCrossing)
    (i : Fin 2) :
    twiceSmoothFlatD D d (Sum.inl (Sum.inr i)) =
      Sum.inl (smoothArcEquiv D (Sum.inr i)) := rfl

private theorem flatD_apply_d_connector (D : PLLinkDiagram) (d : Fin D.nCrossing)
    (i : Fin 2) :
    twiceSmoothFlatD D d (Sum.inr i) = Sum.inr i := rfl

private theorem incoming_ports_ne {D : PLLinkDiagram} {c d : Fin D.nCrossing}
    (hcd : c ≠ d) (i j : Fin 2) : D.incoming c i ≠ D.incoming d j := by
  intro h
  apply hcd
  apply D.crossingVertex_injective
  calc
    D.crossingVertex c = D.arcTarget (D.incoming c i) := (D.incoming_target c i).symm
    _ = D.arcTarget (D.incoming d j) := congrArg D.arcTarget h
    _ = D.crossingVertex d := D.incoming_target d j

private theorem smoothIncoming_reindexed (D : PLLinkDiagram) (c d : Fin D.nCrossing)
    (hdc : d ≠ c) (i : Fin 2) :
    (smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d, hdc⟩) i =
      smoothArcEquiv D (Sum.inl (D.incoming d i)) := by
  change smoothArcEquiv D (Sum.inl (D.incoming
    ((smoothCrossingEquiv D c).symm (smoothCrossingEquiv D c ⟨d, hdc⟩)).val i)) = _
  simp

private theorem smoothIncoming_reindexed_D (D : PLLinkDiagram) (c d : Fin D.nCrossing)
    (hcd : c ≠ d) (i : Fin 2) :
    (smoothCrossing D d).incoming (smoothCrossingEquiv D d ⟨c, hcd⟩) i =
      smoothArcEquiv D (Sum.inl (D.incoming c i)) := by
  exact smoothIncoming_reindexed D d c hcd i

theorem twiceSmoothContinuationCodeC_old_other (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) (e : Fin D.nArc)
    (hc : ∀ i, e ≠ D.incoming c i) (hd : ∀ i, e ≠ D.incoming d i) :
    twiceSmoothContinuationCodeC D c d hcd.symm (Sum.inl (Sum.inl e)) =
      Sum.inl (Sum.inl (D.continuation e)) := by
  apply (twiceSmoothFlatC D c).injective
  simp only [twiceSmoothContinuationCodeC, Equiv.trans_apply, Equiv.apply_symm_apply]
  change smoothContinuationGeometryCode (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)
      (Sum.inl (smoothArcEquiv D (Sum.inl e))) =
    Sum.inl (smoothArcEquiv D (Sum.inl (D.continuation e)))
  rw [smoothContinuationGeometryCode_other_arc]
  · rw [smoothChild_continuation_code, smoothContinuationGeometryCode_other_arc]
    exact hc
  · intro i
    intro hh
    have hval := (smoothArcEquiv D).injective hh
    have h' : e = D.incoming d i := by
      simpa using Sum.inl.inj hval
    exact hd i h'

theorem twiceSmoothContinuationCodeC_old_c (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) (i : Fin 2) :
    twiceSmoothContinuationCodeC D c d hcd.symm
      (Sum.inl (Sum.inl (D.incoming c i))) = Sum.inl (Sum.inr i) := by
  apply (twiceSmoothFlatC D c).injective
  simp only [twiceSmoothContinuationCodeC, Equiv.trans_apply, Equiv.apply_symm_apply]
  change smoothContinuationGeometryCode (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)
      (Sum.inl (smoothArcEquiv D (Sum.inl (D.incoming c i)))) =
    Sum.inl (smoothArcEquiv D (Sum.inr i))
  rw [smoothContinuationGeometryCode_other_arc]
  · rw [smoothChild_continuation_code]
    fin_cases i <;> simp [smoothContinuationGeometryCode_incoming_zero,
      smoothContinuationGeometryCode_incoming_one]
  · intro j hh
    have hval := (smoothArcEquiv D).injective hh
    have h := Sum.inl.inj hval
    have h := by simpa using h
    exact (incoming_ports_ne hcd i j) h

theorem twiceSmoothContinuationCodeC_old_d (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) (i : Fin 2) :
    twiceSmoothContinuationCodeC D c d hcd.symm
      (Sum.inl (Sum.inl (D.incoming d i))) = Sum.inr i := by
  apply (twiceSmoothFlatC D c).injective
  simp only [twiceSmoothContinuationCodeC, Equiv.trans_apply, Equiv.apply_symm_apply]
  change smoothContinuationGeometryCode (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)
      (Sum.inl (smoothArcEquiv D (Sum.inl (D.incoming d i)))) = Sum.inr i
  rw [← smoothIncoming_reindexed D c d hcd.symm i]
  fin_cases i <;> simp [smoothContinuationGeometryCode_incoming_zero,
    smoothContinuationGeometryCode_incoming_one]

theorem twiceSmoothContinuationCodeC_connector_c (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) (i : Fin 2) :
    twiceSmoothContinuationCodeC D c d hcd.symm (Sum.inl (Sum.inr i)) =
      Sum.inl (Sum.inl (D.outgoing c (D.through c (otherBranch i)))) := by
  apply (twiceSmoothFlatC D c).injective
  simp only [twiceSmoothContinuationCodeC, Equiv.trans_apply, Equiv.apply_symm_apply]
  change smoothContinuationGeometryCode (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)
      (Sum.inl (smoothArcEquiv D (Sum.inr i))) =
    Sum.inl (smoothArcEquiv D (Sum.inl (D.outgoing c (D.through c (otherBranch i)))))
  rw [smoothContinuationGeometryCode_other_arc]
  · rw [smoothChild_continuation_code, smoothContinuationGeometryCode_connector]
  · intro j hh
    have hval := (smoothArcEquiv D).injective hh
    cases hval

theorem twiceSmoothContinuationCodeC_connector_d (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) (i : Fin 2) :
    twiceSmoothContinuationCodeC D c d hcd.symm (Sum.inr i) =
      Sum.inl (Sum.inl (D.outgoing d (D.through d (otherBranch i)))) := by
  apply (twiceSmoothFlatC D c).injective
  simp only [twiceSmoothContinuationCodeC, Equiv.trans_apply, Equiv.apply_symm_apply]
  change smoothContinuationGeometryCode (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩) (Sum.inr i) =
    Sum.inl (smoothArcEquiv D (Sum.inl (D.outgoing d (D.through d (otherBranch i)))))
  rw [smoothContinuationGeometryCode_connector]
  simp [PLLinkDiagram.outgoing, smoothCrossing, smoothOutgoing, smoothThrough]


theorem twiceSmoothContinuationCodeC_commute (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) (x : TwiceSmoothArcCode D) :
    twiceSmoothArcCodeSwap D (twiceSmoothContinuationCodeC D c d hcd.symm x) =
      twiceSmoothContinuationCodeC D d c hcd
        (twiceSmoothArcCodeSwap D x) := by
  cases x with
  | inl y =>
    cases y with
    | inl e =>
      by_cases hc0 : e = D.incoming c 0
      · subst e
        rw [twiceSmoothContinuationCodeC_old_c D c d hcd 0]
        change Sum.inr 0 = twiceSmoothContinuationCodeC D d c hcd
          (Sum.inl (Sum.inl (D.incoming c 0)))
        rw [twiceSmoothContinuationCodeC_old_d D d c hcd.symm 0]
      · by_cases hc1 : e = D.incoming c 1
        · subst e
          rw [twiceSmoothContinuationCodeC_old_c D c d hcd 1]
          change Sum.inr 1 = twiceSmoothContinuationCodeC D d c hcd
            (Sum.inl (Sum.inl (D.incoming c 1)))
          rw [twiceSmoothContinuationCodeC_old_d D d c hcd.symm 1]
        · by_cases hd0 : e = D.incoming d 0
          · subst e
            rw [twiceSmoothContinuationCodeC_old_d D c d hcd 0]
            change Sum.inl (Sum.inr 0) = twiceSmoothContinuationCodeC D d c hcd
              (Sum.inl (Sum.inl (D.incoming d 0)))
            rw [twiceSmoothContinuationCodeC_old_c D d c hcd.symm 0]
          · by_cases hd1 : e = D.incoming d 1
            · subst e
              rw [twiceSmoothContinuationCodeC_old_d D c d hcd 1]
              change Sum.inl (Sum.inr 1) = twiceSmoothContinuationCodeC D d c hcd
                (Sum.inl (Sum.inl (D.incoming d 1)))
              rw [twiceSmoothContinuationCodeC_old_c D d c hcd.symm 1]
            · have hc : ∀ i, e ≠ D.incoming c i := by
                intro i; fin_cases i <;> assumption
              have hd : ∀ i, e ≠ D.incoming d i := by
                intro i; fin_cases i <;> assumption
              rw [twiceSmoothContinuationCodeC_old_other D c d hcd e hc hd]
              change Sum.inl (Sum.inl (D.continuation e)) =
                twiceSmoothContinuationCodeC D d c hcd
                  (Sum.inl (Sum.inl e))
              rw [twiceSmoothContinuationCodeC_old_other D d c hcd.symm e hd hc]
    | inr i =>
      rw [twiceSmoothContinuationCodeC_connector_c D c d hcd i]
      change Sum.inl (Sum.inl (D.outgoing c (D.through c (otherBranch i)))) =
        twiceSmoothContinuationCodeC D d c hcd (Sum.inr i)
      rw [twiceSmoothContinuationCodeC_connector_d D d c hcd.symm i]
  | inr i =>
    rw [twiceSmoothContinuationCodeC_connector_d D c d hcd i]
    change Sum.inl (Sum.inl (D.outgoing d (D.through d (otherBranch i)))) =
      twiceSmoothContinuationCodeC D d c hcd (Sum.inl (Sum.inr i))
    rw [twiceSmoothContinuationCodeC_connector_c D d c hcd.symm i]


private theorem twiceSmoothedContinuation_c (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (e : Fin (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nArc) :
    (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).continuation e =
    (smoothArcEquiv (smoothCrossing D c))
      (smoothContinuationGeometryCode (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)
        ((smoothArcEquiv (smoothCrossing D c)).symm e)) := by
  let ec := smoothArcEquiv (smoothCrossing D c)
  have he : ec (ec.symm e) = e := ec.apply_symm_apply e
  calc
    _ = (smoothCrossing (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).continuation (ec (ec.symm e)) :=
          congrArg _ he.symm
    _ = ec (smoothContinuationGeometryCode (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩) (ec.symm e)) :=
          smoothChild_continuation_code (smoothCrossing D c)
            (smoothCrossingEquiv D c ⟨d, hcd.symm⟩) (ec.symm e)

private theorem twiceSmoothedContinuation_d (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (e : Fin (smoothCrossing (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩)).nArc) :
    (smoothCrossing (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩)).continuation e =
    (smoothArcEquiv (smoothCrossing D d))
      (smoothContinuationGeometryCode (smoothCrossing D d)
        (smoothCrossingEquiv D d ⟨c, hcd⟩)
        ((smoothArcEquiv (smoothCrossing D d)).symm e)) := by
  let ed := smoothArcEquiv (smoothCrossing D d)
  have he : ed (ed.symm e) = e := ed.apply_symm_apply e
  calc
    _ = (smoothCrossing (smoothCrossing D d)
        (smoothCrossingEquiv D d ⟨c, hcd⟩)).continuation (ed (ed.symm e)) :=
          congrArg _ he.symm
    _ = ed (smoothContinuationGeometryCode (smoothCrossing D d)
        (smoothCrossingEquiv D d ⟨c, hcd⟩) (ed.symm e)) :=
          smoothChild_continuation_code (smoothCrossing D d)
            (smoothCrossingEquiv D d ⟨c, hcd⟩) (ed.symm e)

theorem smoothTwiceContinuation_map (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    ∀ e : Fin (smoothCrossing (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nArc,
      smoothTwiceArcLabelEquiv D c d hcd
        ((smoothCrossing (smoothCrossing D c)
          (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).continuation e) =
      (smoothCrossing (smoothCrossing D d)
        (smoothCrossingEquiv D d ⟨c, hcd⟩)).continuation
        (smoothTwiceArcLabelEquiv D c d hcd e) := by
  intro e
  rw [twiceSmoothedContinuation_c D c d hcd e]
  rw [twiceSmoothedContinuation_d D c d hcd (smoothTwiceArcLabelEquiv D c d hcd e)]
  let ec := smoothArcEquiv (smoothCrossing D c)
  let ed := smoothArcEquiv (smoothCrossing D d)
  let fc := twiceSmoothFlatC D c
  let fd := twiceSmoothFlatD D d
  let x : TwiceSmoothArcCode D := fc.symm (ec.symm e)
  have hC (z : SmoothArcCode (smoothCrossing D c)) : ec.symm (ec z) = z :=
    Equiv.symm_apply_apply ec z
  have hD (z : SmoothArcCode (smoothCrossing D d)) : ed.symm (ed z) = z :=
    Equiv.symm_apply_apply ed z
  simp only [smoothTwiceArcLabelEquiv, Equiv.trans_apply]
  change ed (fd (twiceSmoothArcCodeSwap D
      (fc.symm (ec.symm (ec (smoothContinuationGeometryCode
        (smoothCrossing D c) (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)
        (ec.symm e))))))) =
    ed (smoothContinuationGeometryCode (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩)
      (ed.symm (ed (fd (twiceSmoothArcCodeSwap D (fc.symm (ec.symm e)))))))
  simp only [hC, hD]
  congr 1
  have hcx : twiceSmoothContinuationCodeC D c d hcd.symm x =
      fc.symm (smoothContinuationGeometryCode (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩) (ec.symm e)) := by
    change fc.symm (smoothContinuationGeometryCode (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)
        (fc (fc.symm (ec.symm e)))) = _
    rw [fc.apply_symm_apply]
  calc
    fd (twiceSmoothArcCodeSwap D
        (fc.symm (smoothContinuationGeometryCode (smoothCrossing D c)
          (smoothCrossingEquiv D c ⟨d, hcd.symm⟩) (ec.symm e)))) =
      fd (twiceSmoothArcCodeSwap D
        (twiceSmoothContinuationCodeC D c d hcd.symm x)) := by rw [← hcx]
    _ = fd (twiceSmoothContinuationCodeC D d c hcd (twiceSmoothArcCodeSwap D x)) :=
        congrArg fd (twiceSmoothContinuationCodeC_commute D c d hcd x)
    _ = smoothContinuationGeometryCode (smoothCrossing D d)
        (smoothCrossingEquiv D d ⟨c, hcd⟩)
        (fd (twiceSmoothArcCodeSwap D x)) := by
      change fd (fd.symm (smoothContinuationGeometryCode (smoothCrossing D d)
        (smoothCrossingEquiv D d ⟨c, hcd⟩)
        (fd (twiceSmoothArcCodeSwap D x)))) = _
      rw [fd.apply_symm_apply]


theorem smoothTwiceCrossing_parent_label (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (x : Fin (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nCrossing) :
    (smoothTwiceCrossingToDeleted_dFirst D c d hcd
      (smoothTwiceCrossingLabelEquiv D c d hcd x)).val =
    (smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm x).val := by
  simp [smoothTwiceCrossingLabelEquiv, smoothTwiceCrossingToDeleted_cFirst,
    smoothTwiceCrossingToDeleted_dFirst, twiceDeletedCrossingSwap]


theorem smoothTwiceArcLabelEquiv_old_arc (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) (e : Fin D.nArc) :
    smoothTwiceArcLabelEquiv D c d hcd
      ((smoothArcEquiv (smoothCrossing D c))
        (Sum.inl ((smoothArcEquiv D) (Sum.inl e)))) =
      (smoothArcEquiv (smoothCrossing D d))
        (Sum.inl ((smoothArcEquiv D) (Sum.inl e))) := by
  let e0 := smoothArcEquiv D
  let ec := smoothArcEquiv (smoothCrossing D c)
  let ed := smoothArcEquiv (smoothCrossing D d)
  let fc := twiceSmoothFlatC D c
  let fd := twiceSmoothFlatD D d
  have hc : ec.symm (ec (Sum.inl (e0 (Sum.inl e)))) =
      Sum.inl (e0 (Sum.inl e)) := ec.symm_apply_apply _
  have h0 : e0.symm (e0 (Sum.inl e)) = Sum.inl e := e0.symm_apply_apply _
  simp only [smoothTwiceArcLabelEquiv, Equiv.trans_apply]
  change ed (fd (twiceSmoothArcCodeSwap D
      (fc.symm (ec.symm (ec (Sum.inl (e0 (Sum.inl e)))))))) =
    ed (Sum.inl (e0 (Sum.inl e)))
  rw [hc]
  have hfc : fc.symm (Sum.inl (e0 (Sum.inl e))) = Sum.inl (Sum.inl e) := by
    have hf : fc (Sum.inl (Sum.inl e)) = Sum.inl (e0 (Sum.inl e)) := rfl
    calc
      fc.symm (Sum.inl (e0 (Sum.inl e))) =
          fc.symm (fc (Sum.inl (Sum.inl e))) := congrArg fc.symm hf.symm
      _ = Sum.inl (Sum.inl e) := fc.symm_apply_apply _
  rw [hfc]
  simp [fd, twiceSmoothFlatD, twiceSmoothArcCodeSwap, Equiv.sumCongr_apply]
  rfl


private theorem twiceSmoothIncomingCode_c (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (x : Fin (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nCrossing) (i : Fin 2) :
    (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).incoming x i =
    (smoothArcEquiv (smoothCrossing D c))
      (Sum.inl ((smoothArcEquiv D)
        (Sum.inl (D.incoming
          ((smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm x).val) i)))) := by
  simp [smoothCrossing, smoothIncoming, smoothTwiceCrossingToDeleted_cFirst]

private theorem twiceSmoothIncomingCode_d (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (x : Fin (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nCrossing) (i : Fin 2) :
    (smoothCrossing (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩)).incoming
        (smoothTwiceCrossingLabelEquiv D c d hcd x) i =
    (smoothArcEquiv (smoothCrossing D d))
      (Sum.inl ((smoothArcEquiv D)
        (Sum.inl (D.incoming
          ((smoothTwiceCrossingToDeleted_dFirst D c d hcd
            (smoothTwiceCrossingLabelEquiv D c d hcd x)).val) i)))) := by
  simp [smoothCrossing, smoothIncoming, smoothTwiceCrossingLabelEquiv,
    smoothTwiceCrossingToDeleted_cFirst, smoothTwiceCrossingToDeleted_dFirst,
    twiceDeletedCrossingSwap]

private theorem twiceSmoothOutgoingCode_c (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (x : Fin (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nCrossing) (i : Fin 2) :
    (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).outgoing x i =
    (smoothArcEquiv (smoothCrossing D c))
      (Sum.inl ((smoothArcEquiv D)
        (Sum.inl (D.outgoing
          ((smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm x).val) i)))) := by
  simp [smoothCrossing, smoothOutgoing, smoothTwiceCrossingToDeleted_cFirst]

private theorem twiceSmoothOutgoingCode_d (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (x : Fin (smoothCrossing (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nCrossing) (i : Fin 2) :
    (smoothCrossing (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩)).outgoing
        (smoothTwiceCrossingLabelEquiv D c d hcd x) i =
    (smoothArcEquiv (smoothCrossing D d))
      (Sum.inl ((smoothArcEquiv D)
        (Sum.inl (D.outgoing
          ((smoothTwiceCrossingToDeleted_dFirst D c d hcd
            (smoothTwiceCrossingLabelEquiv D c d hcd x)).val) i)))) := by
  simp [smoothCrossing, smoothOutgoing, smoothTwiceCrossingLabelEquiv,
    smoothTwiceCrossingToDeleted_cFirst, smoothTwiceCrossingToDeleted_dFirst,
    twiceDeletedCrossingSwap]

noncomputable def smoothTwiceSignedDiagramIso (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    SignedDiagramIso
      (smoothCrossing (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩))
      (smoothCrossing (smoothCrossing D d)
        (smoothCrossingEquiv D d ⟨c, hcd⟩)) where
  arcEquiv := smoothTwiceArcLabelEquiv D c d hcd
  crossingEquiv := smoothTwiceCrossingLabelEquiv D c d hcd
  incoming_map := by
    intro x i
    rw [twiceSmoothIncomingCode_c D c d hcd x i,
      twiceSmoothIncomingCode_d D c d hcd x i]
    rw [smoothTwiceCrossing_parent_label D c d hcd x]
    exact smoothTwiceArcLabelEquiv_old_arc D c d hcd
      (D.incoming ((smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm x).val) i)
  outgoing_map := by
    intro x i
    rw [twiceSmoothOutgoingCode_c D c d hcd x i,
      twiceSmoothOutgoingCode_d D c d hcd x i]
    rw [smoothTwiceCrossing_parent_label D c d hcd x]
    exact smoothTwiceArcLabelEquiv_old_arc D c d hcd
      (D.outgoing ((smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm x).val) i)
  continuation_map := smoothTwiceContinuation_map D c d hcd
  through_map := by
    intro x
    have hp := smoothTwiceCrossing_parent_label D c d hcd x
    simpa [smoothCrossing, smoothThrough, smoothTwiceCrossingLabelEquiv,
      smoothTwiceCrossingToDeleted_cFirst, smoothTwiceCrossingToDeleted_dFirst,
      twiceDeletedCrossingSwap] using congrArg D.through hp
  overBranch_map := by
    intro x
    have hp := smoothTwiceCrossing_parent_label D c d hcd x
    simpa [smoothCrossing, smoothTwiceCrossingLabelEquiv,
      smoothTwiceCrossingToDeleted_cFirst, smoothTwiceCrossingToDeleted_dFirst,
      twiceDeletedCrossingSwap] using congrArg D.overBranch hp
  crossingSign_map := by
    intro x
    have hp := smoothTwiceCrossing_parent_label D c d hcd x
    let c1 := smoothCrossingEquiv D c ⟨d, hcd.symm⟩
    let x1 := (smoothCrossingEquiv (smoothCrossing D c) c1).symm x
    let d1 := smoothCrossingEquiv D d ⟨c, hcd⟩
    let x2 := (smoothCrossingEquiv (smoothCrossing D d) d1).symm
      (smoothTwiceCrossingLabelEquiv D c d hcd x)
    let pC := smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm x
    let pD := smoothTwiceCrossingToDeleted_dFirst D c d hcd
      (smoothTwiceCrossingLabelEquiv D c d hcd x)
    have hleft2 := crossingSign_smoothRetained
      (smoothCrossing D c) c1 x1.val x1.property
    have hleft1 := crossingSign_smoothRetained D c
      (smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm x).val
      (smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm x).property.1
    have hright2 := crossingSign_smoothRetained
      (smoothCrossing D d) d1 x2.val x2.property
    have hright1 := crossingSign_smoothRetained D d
      (smoothTwiceCrossingToDeleted_dFirst D c d hcd
        (smoothTwiceCrossingLabelEquiv D c d hcd x)).val
      (smoothTwiceCrossingToDeleted_dFirst D c d hcd
        (smoothTwiceCrossingLabelEquiv D c d hcd x)).property.1
    have hleftcode : smoothCrossingEquiv (smoothCrossing D c) c1 x1 = x := by
      exact Equiv.apply_symm_apply _ x
    have hleftparent :
        x1.val = smoothCrossingEquiv D c ⟨pC.val, pC.property.1⟩ := by
      simp [c1, x1, pC, smoothTwiceCrossingToDeleted_cFirst]
    have hrightcode : smoothCrossingEquiv (smoothCrossing D d) d1 x2 =
        smoothTwiceCrossingLabelEquiv D c d hcd x :=
      Equiv.apply_symm_apply _ _
    have hrightparent :
        x2.val = smoothCrossingEquiv D d ⟨pD.val, pD.property.1⟩ := by
      simp [d1, x2, pD, smoothTwiceCrossingLabelEquiv,
        smoothTwiceCrossingToDeleted_dFirst]
    calc
      crossingSign (smoothCrossing (smoothCrossing D c) c1) x =
          crossingSign (smoothCrossing (smoothCrossing D c) c1)
            (smoothCrossingEquiv (smoothCrossing D c) c1 x1) := by rw [hleftcode]
      _ = crossingSign (smoothCrossing D c) x1.val := hleft2
      _ = crossingSign (smoothCrossing D c)
          (smoothCrossingEquiv D c
            ⟨pC.val, pC.property.1⟩) := by
              rw [← hleftparent]
      _ = crossingSign D
          pC.val := by
            simpa [c1, pC, smoothTwiceCrossingToDeleted_cFirst] using hleft1
      _ = crossingSign D
          pD.val := by exact congrArg (crossingSign D) hp.symm
      _ = crossingSign (smoothCrossing D d)
          (smoothCrossingEquiv D d ⟨pD.val, pD.property.1⟩) := by
            exact hright1.symm
      _ = crossingSign (smoothCrossing D d) x2.val := by
            rw [← hrightparent]
      _ = crossingSign (smoothCrossing (smoothCrossing D d) d1)
          (smoothCrossingEquiv (smoothCrossing D d) d1 x2) := hright2.symm
      _ = crossingSign (smoothCrossing (smoothCrossing D d) d1)
          (smoothTwiceCrossingLabelEquiv D c d hcd x) := by
            rw [hrightcode]


end DirectGLSSW.HOMFLY






