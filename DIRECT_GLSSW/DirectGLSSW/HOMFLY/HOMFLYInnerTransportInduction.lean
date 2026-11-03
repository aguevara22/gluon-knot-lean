import DirectGLSSW.HOMFLY.HOMFLYSkeinPivotAlgebra

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- Bounded evaluator transport for the traversal actually carried by a
signed diagram isomorphism. Unlike arbitrary traversal independence, this is
the inner statement that switching can lower. -/
def InnerBadCardTransportIH (n k : ℕ) : Prop :=
  ∀ {D E : PLLinkDiagram} (I : SignedDiagramIso D E)
    (_hD : D.nCrossing = n) (T : BasedTraversal D),
    (badCrossings T).card < k →
      descendingLaurentEvaluator D T =
      descendingLaurentEvaluator E (I.transportTraversal T)

theorem basedTraversal_ext {D : PLLinkDiagram} {T U : BasedTraversal D}
    (hindex : T.componentIndex = U.componentIndex)
    (hbase : ∀ C, (T.baseArc C).val = (U.baseArc C).val) : T = U := by
  cases T with
  | mk ti tb =>
    cases U with
    | mk ui ub =>
      dsimp at hindex hbase
      have hidx : ti = ui := hindex
      subst ui
      have hb : tb = ub := by
        funext C
        apply Subtype.ext
        exact hbase C
      subst ub
      rfl

theorem switchSwitch_transportTraversal_eq (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) (T : BasedTraversal D) :
    (switchSwitchSignedDiagramIso_commute D c d hcd).transportTraversal
      (switchTraversal (switchTraversal T c) d) =
    switchTraversal (switchTraversal T d) c := by
  have hcomp : ∀ C : diagramComponent D,
      (switchSwitchSignedDiagramIso_commute D c d hcd).componentEquiv C = C := by
    intro C
    refine Quotient.inductionOn C ?_
    intro e
    rfl
  have hcompSymm : ∀ C : diagramComponent D,
      (switchSwitchSignedDiagramIso_commute D c d hcd).componentEquiv.symm C = C := by
    intro C
    have hh := hcomp
      ((switchSwitchSignedDiagramIso_commute D c d hcd).componentEquiv.symm C)
    rw [(switchSwitchSignedDiagramIso_commute D c d hcd).componentEquiv.apply_symm_apply] at hh
    exact hh.symm
  apply basedTraversal_ext
  · apply Equiv.ext
    intro C
    rw [SignedDiagramIso.transportTraversal_componentIndex]
    rw [hcompSymm]
    have hp : (switchSwitchSignedDiagramIso_commute D c d hcd).componentCount_eq = rfl :=
      Subsingleton.elim _ _
    rw [hp]
    rfl
  · intro C
    rw [SignedDiagramIso.transportTraversal_baseArc_val, hcompSymm]
    rfl

theorem switchTraversal_transportTraversal_eq {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing) (T : BasedTraversal D) :
    (switchSignedDiagramIso I c).transportTraversal (switchTraversal T c) =
      switchTraversal (I.transportTraversal T) (I.crossingEquiv c) := by
  have hcomponent : (switchSignedDiagramIso I c).componentEquiv = I.componentEquiv := rfl
  have hcount : (switchSignedDiagramIso I c).componentCount_eq = I.componentCount_eq :=
    Subsingleton.elim _ _
  apply basedTraversal_ext
  · apply Equiv.ext
    intro C
    simp only [SignedDiagramIso.transportTraversal_componentIndex,
      switchTraversal, hcomponent, hcount]
    rfl
  · intro C
    simp only [SignedDiagramIso.transportTraversal_baseArc_val,
      switchTraversal, hcomponent]
    rfl

theorem innerIH_doubleSwitch_transport_eval_eq {n k : ℕ}
    (ih : InnerBadCardTransportIH n k)
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (hD : D.nCrossing = n) (T : BasedTraversal D)
    (hc : badAt T c) (hd : badAt T d)
    (hk : (badCrossings T).card = k) :
    descendingLaurentEvaluator (switchCrossing (switchCrossing D c) d)
        (switchTraversal (switchTraversal T c) d) =
      descendingLaurentEvaluator (switchCrossing (switchCrossing D d) c)
        (switchTraversal (switchTraversal T d) c) := by
  have hcMem : c ∈ badCrossings T := by simp [badCrossings, hc]
  have hdMem : d ∈ badCrossings T := by simp [badCrossings, hd]
  have hcdChild : d ∈ badCrossings (switchTraversal T c) := by
    simpa [badCrossings] using (badAt_switch_same T c d hcd.symm).2 hd
  have hdcChild : c ∈ badCrossings (switchTraversal T d) := by
    simpa [badCrossings] using (badAt_switch_same T d c hcd).2 hc
  have hcard :
      (badCrossings (switchTraversal (switchTraversal T c) d)).card < k := by
    have h1 := badCrossings_switch_card T c hcMem
    have h2 := badCrossings_switch_card (switchTraversal T c) d hcdChild
    omega
  have htransport := ih (switchSwitchSignedDiagramIso_commute D c d hcd)
    (by simpa [switch_crossing_count] using hD)
    (switchTraversal (switchTraversal T c) d) hcard
  simpa [switchSwitch_transportTraversal_eq D c d hcd T] using htransport

theorem innerIH_twoBadPivot_branches_transport_eq {n k : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (inner : InnerBadCardPivotIH n k)
    (innerTransport : InnerBadCardTransportIH n k)
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (hD : D.nCrossing = n) (T : BasedTraversal D)
    (hc : badAt T c) (hd : badAt T d)
    (hk : (badCrossings T).card = k) :
    descendingEvaluatorPivotBranch D T c =
      descendingEvaluatorPivotBranch D T d := by
  let sc := smoothChildBasedTraversal D c
  let sd := smoothChildBasedTraversal D d
  let dc := smoothCrossingEquiv D c ⟨d, hcd.symm⟩
  let cd := smoothCrossingEquiv D d ⟨c, hcd⟩
  have hsc : descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) =
      descendingEvaluatorPivotBranch (switchCrossing D c) (switchTraversal T c) d :=
    innerIH_switch_child_other_pivot inner D c d hcd hD T hc hd hk
  have hsd : descendingLaurentEvaluator (switchCrossing D d) (switchTraversal T d) =
      descendingEvaluatorPivotBranch (switchCrossing D d) (switchTraversal T d) c :=
    innerIH_switch_child_other_pivot_swap inner D c d hcd hD T hc hd hk
  have hltc : (smoothCrossing D c).nCrossing < n := by
    have hdrop := smoothCrossing_crossing_count_drop D c
    rw [hD] at hdrop
    omega
  have hltd : (smoothCrossing D d).nCrossing < n := by
    have hdrop := smoothCrossing_crossing_count_drop D d
    rw [hD] at hdrop
    omega
  have hmc := outer.2 hltc sc dc
  have hmd := outer.2 hltd sd cd
  have hss := innerIH_doubleSwitch_transport_eval_eq (n := n) innerTransport
    D c d hcd hD T hc hd hk
  have hys := lowerIH_switchSmooth_child_eval_eq outer.1 D d c hcd.symm hD
    (smoothChildBasedTraversal (switchCrossing D c) d)
    (switchTraversal sd (smoothCrossingEquiv D d ⟨c, hcd⟩))
  have hzs := lowerIH_switchSmooth_child_eval_eq outer.1 D c d hcd hD
    (smoothChildBasedTraversal (switchCrossing D d) c)
    (switchTraversal sc (smoothCrossingEquiv D c ⟨d, hcd.symm⟩))
  have hmm := lowerIH_doubleSmooth_child_eval_eq outer.1 D c d hcd hD
    (smoothChildBasedTraversal (smoothCrossing D c) dc)
    (smoothChildBasedTraversal (smoothCrossing D d) cd)
  change pivotSwitchFactor D c *
      descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) +
    pivotSmoothFactor D c * descendingLaurentEvaluator (smoothCrossing D c) sc =
    pivotSwitchFactor D d *
      descendingLaurentEvaluator (switchCrossing D d) (switchTraversal T d) +
    pivotSmoothFactor D d * descendingLaurentEvaluator (smoothCrossing D d) sd
  rw [hsc, hsd, hmc, hmd]
  simp only [descendingEvaluatorPivotBranch]
  rw [pivotSwitchFactor_switch_ne D d c hcd.symm,
    pivotSmoothFactor_switch_ne D d c hcd.symm,
    pivotSwitchFactor_smooth_ne D c d hcd,
    pivotSmoothFactor_smooth_ne D c d hcd,
    pivotSwitchFactor_switch_ne D c d hcd,
    pivotSmoothFactor_switch_ne D c d hcd,
    pivotSwitchFactor_smooth_ne D d c hcd.symm,
    pivotSmoothFactor_smooth_ne D d c hcd.symm]
  rw [← hss, ← hys, ← hzs, ← hmm]
  exact actualTwoPivotExpansion_algebra D c d
    (descendingLaurentEvaluator
      (switchCrossing (switchCrossing D c) d)
      (switchTraversal (switchTraversal T c) d))
    (descendingLaurentEvaluator (smoothCrossing (switchCrossing D c) d)
      (smoothChildBasedTraversal (switchCrossing D c) d))
    (descendingLaurentEvaluator (smoothCrossing (switchCrossing D d) c)
      (smoothChildBasedTraversal (switchCrossing D d) c))
    (descendingLaurentEvaluator (smoothCrossing (smoothCrossing D c) dc)
      (smoothChildBasedTraversal (smoothCrossing D c) dc))

theorem switchSmooth_pivotBranch_transport_eq {n k : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (inner : InnerBadCardTransportIH n k)
    {D E : PLLinkDiagram} (I : SignedDiagramIso D E)
    (hD : D.nCrossing = n) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (hc : badAt T c)
    (hk : (badCrossings T).card = k) :
    descendingEvaluatorPivotBranch D T c =
      descendingEvaluatorPivotBranch E (I.transportTraversal T)
        (I.crossingEquiv c) := by
  let cE := I.crossingEquiv c
  let ISwitch := switchSignedDiagramIso I c
  have hcard :
      (badCrossings (switchTraversal T c)).card < k := by
    have hcMem : c ∈ badCrossings T := by simp [badCrossings, hc]
    have hdrop := badCrossings_switch_card T c hcMem
    omega
  have hSwitch := inner ISwitch (by simpa [switch_crossing_count] using hD)
    (switchTraversal T c) hcard
  have hChildTraversal :
      ISwitch.transportTraversal (switchTraversal T c) =
        switchTraversal (I.transportTraversal T) cE :=
    switchTraversal_transportTraversal_eq I c T
  rw [hChildTraversal] at hSwitch
  have hSmoothCount : (smoothCrossing D c).nCrossing < n := by
    have hdrop := smoothCrossing_crossing_count_drop D c
    rw [hD] at hdrop
    omega
  have hSmooth := outer.1 (smoothSignedDiagramIso I c) hSmoothCount
    (smoothChildBasedTraversal D c)
    (smoothChildBasedTraversal E cE)
  have hA : pivotSwitchFactor D c = pivotSwitchFactor E cE := by
    change pivotSwitchFactor D c = pivotSwitchFactor E (I.crossingEquiv c)
    simp [pivotSwitchFactor, I.crossingSign_map c]
  have hB : pivotSmoothFactor D c = pivotSmoothFactor E cE := by
    change pivotSmoothFactor D c = pivotSmoothFactor E (I.crossingEquiv c)
    simp [pivotSmoothFactor, I.crossingSign_map c]
  rw [descendingEvaluatorPivotBranch, descendingEvaluatorPivotBranch,
    hA, hB, hSwitch, hSmooth]

theorem innerIH_pivot_transport_successor {n k : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (ihPivot : InnerBadCardPivotIH n k)
    (ihTransport : InnerBadCardTransportIH n k) :
    InnerBadCardPivotIH n (k + 1) := by
  intro D hD T c hcard hc
  by_cases hlt : (badCrossings T).card < k
  · exact ihPivot hD T c hlt hc
  · have hk : (badCrossings T).card = k := by omega
    have hnonempty : (badCrossings T).Nonempty := by
      refine ⟨c, ?_⟩
      simpa [badCrossings] using hc
    let c0 := Classical.choose hnonempty
    have hmem : c0 ∈ badCrossings T := Classical.choose_spec hnonempty
    have hc0 : badAt T c0 := by simpa [badCrossings] using hmem
    have heval := descendingEvaluator_eq_pivotBranch_of_choice D T hnonempty c0 rfl
    have hbranch : descendingEvaluatorPivotBranch D T c0 =
        descendingEvaluatorPivotBranch D T c := by
      by_cases heq : c0 = c
      · simpa [heq]
      · exact innerIH_twoBadPivot_branches_transport_eq outer ihPivot ihTransport
          D c0 c heq hD T hc0 hc hk
    exact heval.trans hbranch

theorem innerIH_transport_successor {n k : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (ihPivot : InnerBadCardPivotIH n (k + 1))
    (ihTransport : InnerBadCardTransportIH n k) :
    InnerBadCardTransportIH n (k + 1) := by
  intro D E I hD T hcard
  by_cases hlt : (badCrossings T).card < k
  · exact ihTransport I hD T hlt
  · have hk : (badCrossings T).card = k := by omega
    have hDE : D.nCrossing = E.nCrossing := by
      simpa using Fintype.card_congr I.crossingEquiv
    have hE : E.nCrossing = n := hDE.symm.trans hD
    have hcardE : (badCrossings (I.transportTraversal T)).card = k := by
      rw [I.badCrossings_card_eq]
      exact hk
    by_cases hk0 : k = 0
    · have hempty : badCrossings T = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      exact (I.descendingEvaluator_terminal_eq T hempty).symm
    · have hnonempty : (badCrossings T).Nonempty :=
        Finset.card_pos.mp (by omega)
      let c := Classical.choose hnonempty
      have hcMem : c ∈ badCrossings T := Classical.choose_spec hnonempty
      have hc : badAt T c := by simpa [badCrossings] using hcMem
      let cE := I.crossingEquiv c
      have hcE : badAt (I.transportTraversal T) cE := by
        simpa [cE] using (I.badAt_transport T c).2 hc
      have hEvalD : descendingLaurentEvaluator D T =
          descendingEvaluatorPivotBranch D T c :=
        ihPivot hD T c (by omega) hc
      have hEvalE :
          descendingLaurentEvaluator E (I.transportTraversal T) =
            descendingEvaluatorPivotBranch E (I.transportTraversal T) cE :=
        ihPivot hE (I.transportTraversal T) cE (by rw [hcardE]; omega) hcE
      have hBranch := switchSmooth_pivotBranch_transport_eq outer ihTransport
        I hD T c hc hk
      exact hEvalD.trans (hBranch.trans hEvalE.symm)

theorem innerBadCard_simultaneous_induction {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n) (k : ℕ) :
    InnerBadCardPivotIH n k ∧ InnerBadCardTransportIH n k := by
  induction k with
  | zero =>
      constructor
      · intro D hD T c hcard hc
        omega
      · intro D E I hD T hcard
        omega
  | succ k ih =>
      have hp : InnerBadCardPivotIH n (k + 1) :=
        innerIH_pivot_transport_successor (n := n) (k := k) outer ih.1 ih.2
      have hq : InnerBadCardTransportIH n (k + 1) :=
        innerIH_transport_successor (n := n) (k := k) outer hp ih.2
      exact ⟨hp, hq⟩

end DirectGLSSW.HOMFLY











