import DirectGLSSW.HOMFLY.HOMFYSmoothingDiagram
import DirectGLSSW.HOMFLY.HOMFLYSmoothingRetainedSign
import DirectGLSSW.HOMFLY.HOMFLYSwitchChoiceFacts
import DirectGLSSW.HOMFLY.BasedTraversal
import SmoothingComponentCount

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- The signed combinatorial data read by the descending evaluator. Geometry
is deliberately omitted: this is an isomorphism of actual finite labelled
PL diagrams after forgetting vertex coordinates, but it retains the induced
crossing signs. -/
structure SignedDiagramIso (D E : PLLinkDiagram) where
  arcEquiv : Fin D.nArc ≃ Fin E.nArc
  crossingEquiv : Fin D.nCrossing ≃ Fin E.nCrossing
  incoming_map : ∀ c i, arcEquiv (D.incoming c i) = E.incoming (crossingEquiv c) i
  outgoing_map : ∀ c i, arcEquiv (D.outgoing c i) = E.outgoing (crossingEquiv c) i
  continuation_map : ∀ e, arcEquiv (D.continuation e) = E.continuation (arcEquiv e)
  through_map : ∀ c, D.through c = E.through (crossingEquiv c)
  overBranch_map : ∀ c, D.overBranch c = E.overBranch (crossingEquiv c)
  crossingSign_map : ∀ c, crossingSign D c = crossingSign E (crossingEquiv c)

namespace SignedDiagramIso

variable {D E F : PLLinkDiagram}

/-- Identity signed isomorphism. -/
def refl (D : PLLinkDiagram) : SignedDiagramIso D D where
  arcEquiv := Equiv.refl _
  crossingEquiv := Equiv.refl _
  incoming_map := by intros; rfl
  outgoing_map := by intros; rfl
  continuation_map := by intro; rfl
  through_map := by intro; rfl
  overBranch_map := by intro; rfl
  crossingSign_map := by intro; rfl

/-- Composition preserves every observed signed combinatorial field. -/
def trans (I : SignedDiagramIso D E) (J : SignedDiagramIso E F) :
    SignedDiagramIso D F where
  arcEquiv := I.arcEquiv.trans J.arcEquiv
  crossingEquiv := I.crossingEquiv.trans J.crossingEquiv
  incoming_map := by intro c i; simp only [Equiv.trans_apply]; rw [I.incoming_map, J.incoming_map]
  outgoing_map := by intro c i; simp only [Equiv.trans_apply]; rw [I.outgoing_map, J.outgoing_map]
  continuation_map := by
    intro e
    change J.arcEquiv (I.arcEquiv (D.continuation e)) =
      F.continuation (J.arcEquiv (I.arcEquiv e))
    rw [I.continuation_map, J.continuation_map]
  through_map := by intro c; simp only [Equiv.trans_apply]; rw [I.through_map, J.through_map]
  overBranch_map := by intro c; simp only [Equiv.trans_apply]; rw [I.overBranch_map, J.overBranch_map]
  crossingSign_map := by
    intro c
    calc
      crossingSign D c = crossingSign E (I.crossingEquiv c) := I.crossingSign_map c
      _ = crossingSign F (J.crossingEquiv (I.crossingEquiv c)) :=
        J.crossingSign_map (I.crossingEquiv c)

end SignedDiagramIso

/-- Switching corresponding sites preserves signed combinatorial isomorphism. -/
def switchSignedDiagramIso {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing) :
    SignedDiagramIso (switchCrossing D c)
      (switchCrossing E (I.crossingEquiv c)) where
  arcEquiv := I.arcEquiv
  crossingEquiv := I.crossingEquiv
  incoming_map := I.incoming_map
  outgoing_map := I.outgoing_map
  continuation_map := I.continuation_map
  through_map := I.through_map
  overBranch_map := by
    intro d
    by_cases hd : d = c
    · subst d
      simp only [switchCrossing, Function.update_self]
      exact congrArg otherBranch (I.overBranch_map c)
    · simp only [switchCrossing, Function.update_of_ne hd,
        Function.update_of_ne (fun he => hd (I.crossingEquiv.injective he))]
      exact I.overBranch_map d
  crossingSign_map := by
    intro d
    by_cases hd : d = c
    · subst d
      calc
        crossingSign (switchCrossing D c) c =
            (crossingSign D c).reverse := crossingSign_switchCrossing D c
        _ = (crossingSign E (I.crossingEquiv c)).reverse :=
          congrArg Sign.reverse (I.crossingSign_map c)
        _ = crossingSign (switchCrossing E (I.crossingEquiv c)) (I.crossingEquiv c) :=
          (crossingSign_switchCrossing E (I.crossingEquiv c)).symm
    · rw [crossingSign_switchCrossing_of_ne D c d hd,
        I.crossingSign_map d]
      have hdE : I.crossingEquiv d ≠ I.crossingEquiv c := by
        intro h
        exact hd (I.crossingEquiv.injective h)
      exact (crossingSign_switchCrossing_of_ne E (I.crossingEquiv c)
        (I.crossingEquiv d) hdE).symm

/-- Deleted-label reindexing transports the retained crossing labels. -/
noncomputable def retainedCrossingEquiv {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing) :
    {d : Fin D.nCrossing // d ≠ c} ≃
      {e : Fin E.nCrossing // e ≠ I.crossingEquiv c} where
  toFun d := ⟨I.crossingEquiv d.val, fun h => d.property (I.crossingEquiv.injective h)⟩
  invFun e := ⟨I.crossingEquiv.symm e.val, fun h => e.property (by
    have hh := congrArg I.crossingEquiv h
    simpa using hh)⟩
  left_inv := by intro d; apply Subtype.ext; simp
  right_inv := by intro e; apply Subtype.ext; simp

/-- Reindexing the actual `Fin` child crossing labels through deleted-label
subtypes. -/
noncomputable def smoothCrossingLabelEquiv {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing) :
    Fin (D.nCrossing - 1) ≃ Fin (E.nCrossing - 1) :=
  (smoothCrossingEquiv D c).symm.trans
    ((retainedCrossingEquiv I c).trans (smoothCrossingEquiv E (I.crossingEquiv c)))

/-- Reindex the old arcs and leave the two local connector labels fixed. -/
noncomputable def smoothArcLabelEquiv {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) : Fin (D.nArc + 2) ≃ Fin (E.nArc + 2) :=
  (smoothArcEquiv D).symm.trans
    ((Equiv.sumCongr I.arcEquiv (Equiv.refl (Fin 2))).trans (smoothArcEquiv E))

/-- The deletion/reindex maps commute with retained crossing ports and through
pairings. Coordinates are intentionally absent from this theorem. -/
def smoothRetainedPorts {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing) :
    let cE := I.crossingEquiv c
    ∀ d i,
      smoothArcLabelEquiv I
        ((smoothCrossing D c).incoming d i) =
          (smoothCrossing E cE).incoming (smoothCrossingLabelEquiv I c d) i ∧
      smoothArcLabelEquiv I
        ((smoothCrossing D c).outgoing d i) =
          (smoothCrossing E cE).outgoing (smoothCrossingLabelEquiv I c d) i ∧
      (smoothCrossing D c).through d =
          (smoothCrossing E cE).through (smoothCrossingLabelEquiv I c d) := by
  intro cE d i
  let oldD := (smoothCrossingEquiv D c).symm d
  let oldE := (retainedCrossingEquiv I c) oldD
  constructor
  · simpa [smoothCrossingLabelEquiv, smoothArcLabelEquiv, smoothCrossing,
      smoothIncoming, smoothArcEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.sumCongr_apply, retainedCrossingEquiv, oldD, oldE, cE] using
        I.incoming_map oldD.val i
  constructor
  · simpa [smoothCrossingLabelEquiv, smoothArcLabelEquiv, smoothCrossing,
      smoothOutgoing, smoothArcEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.sumCongr_apply, retainedCrossingEquiv, oldD, oldE, cE] using
        I.outgoing_map oldD.val i
  · simpa [smoothCrossingLabelEquiv, smoothCrossing, smoothThrough,
      Equiv.trans_apply, Equiv.symm_apply_apply, retainedCrossingEquiv,
      oldD, oldE, cE] using I.through_map oldD.val

/-- The retained crossing's over-branch is transported by the deleted-label
reindexing. -/
theorem smoothRetained_overBranch {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing)
    (d : Fin (smoothCrossing D c).nCrossing) :
    (smoothCrossing D c).overBranch d =
      (smoothCrossing E (I.crossingEquiv c)).overBranch
        (smoothCrossingLabelEquiv I c d) := by
  let oldD := (smoothCrossingEquiv D c).symm d
  simpa [smoothCrossingLabelEquiv, smoothCrossing, retainedCrossingEquiv, oldD]
    using I.overBranch_map oldD.val

/-- A signed combinatorial isomorphism transports the concrete smoothing's
retained crossing signs. The local geometric proof is delegated to the
positive tangent-rescaling theorem for the actual constructor. -/
theorem smoothRetained_crossingSign {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing)
    (d : Fin (smoothCrossing D c).nCrossing) :
    crossingSign (smoothCrossing D c) d =
      crossingSign (smoothCrossing E (I.crossingEquiv c))
        (smoothCrossingLabelEquiv I c d) := by
  let oldD := (smoothCrossingEquiv D c).symm d
  let oldE := retainedCrossingEquiv I c oldD
  have hD := crossingSign_smoothRetained D c oldD.val oldD.property
  have hE := crossingSign_smoothRetained E (I.crossingEquiv c)
    oldE.val oldE.property
  have hlabel :
      smoothCrossingEquiv E (I.crossingEquiv c) oldE =
        smoothCrossingLabelEquiv I c d := rfl
  calc
    crossingSign (smoothCrossing D c) d = crossingSign D oldD.val := by
      simpa [oldD] using hD
    _ = crossingSign E (I.crossingEquiv oldD.val) := I.crossingSign_map oldD.val
    _ = crossingSign E oldE.val := by rfl
    _ = crossingSign (smoothCrossing E (I.crossingEquiv c))
        (smoothCrossingLabelEquiv I c d) := by
      rw [← hlabel]
      exact hE.symm

/-- The geometry-code continuation commutes with a signed diagram
isomorphism. The old-arc case uses the proven nonincident fixed-point fact;
the two selected incoming arcs and the connectors use their actual
smoothing equations. -/
theorem smoothContinuationGeometryCode_natural {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing) :
    let cE := I.crossingEquiv c
    let A := Equiv.sumCongr I.arcEquiv (Equiv.refl (Fin 2))
    ∀ x : SmoothArcCode D,
      A (smoothContinuationGeometryCode D c x) =
        smoothContinuationGeometryCode E cE (A x) := by
  intro cE A x
  cases x with
  | inl e =>
      by_cases h0 : e = D.incoming c 0
      · subst e
        rw [smoothContinuationGeometryCode_incoming_zero]
        have hE : I.arcEquiv (D.incoming c 0) = E.incoming cE 0 := I.incoming_map c 0
        simpa [A, cE, Equiv.sumCongr_apply, hE] using
          (smoothContinuationGeometryCode_incoming_zero E cE).symm
      · by_cases h1 : e = D.incoming c 1
        · subst e
          rw [smoothContinuationGeometryCode_incoming_one]
          have hE : I.arcEquiv (D.incoming c 1) = E.incoming cE 1 := I.incoming_map c 1
          simpa [A, cE, Equiv.sumCongr_apply, hE] using
            (smoothContinuationGeometryCode_incoming_one E cE).symm
        · have heD : ∀ i, e ≠ D.incoming c i := by
            intro i
            fin_cases i
            · exact h0
            · exact h1
          have heE : ∀ i, I.arcEquiv e ≠ E.incoming cE i := by
            intro i hi
            apply heD i
            apply I.arcEquiv.injective
            rw [I.incoming_map]
            exact hi
          rw [smoothContinuationGeometryCode_other_arc D c e heD]
          simp only [A, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
          rw [smoothContinuationGeometryCode_other_arc E cE (I.arcEquiv e) heE]
          simp [I.continuation_map]
  | inr i =>
      have hA : A (Sum.inr i) = Sum.inr i := rfl
      rw [smoothContinuationGeometryCode_connector D c i, hA,
        smoothContinuationGeometryCode_connector E cE i]
      simp only [A, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
      rw [I.outgoing_map, I.through_map]

/-- The actual smoothed child continuation is transported by the arc
reindexing. -/
theorem smoothContinuation_map {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing) (e : Fin (D.nArc + 2)) :
    smoothArcLabelEquiv I ((smoothCrossing D c).continuation e) =
      (smoothCrossing E (I.crossingEquiv c)).continuation
        (smoothArcLabelEquiv I e) := by
  let A := Equiv.sumCongr I.arcEquiv (Equiv.refl (Fin 2))
  let x := (smoothArcEquiv D).symm e
  have h := smoothContinuationGeometryCode_natural I c x
  simp only [smoothArcLabelEquiv, smoothCrossing, smoothContinuation,
    Equiv.trans_apply, Equiv.symm_apply_apply]
  exact congrArg (smoothArcEquiv E) h

/-- Smoothing transports the complete signed combinatorial structure to the
correspondingly reindexed child diagram. -/
noncomputable def smoothSignedDiagramIso {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (c : Fin D.nCrossing) :
    SignedDiagramIso (smoothCrossing D c)
      (smoothCrossing E (I.crossingEquiv c)) where
  arcEquiv := smoothArcLabelEquiv I
  crossingEquiv := smoothCrossingLabelEquiv I c
  incoming_map := by
    intro d i
    exact (smoothRetainedPorts I c d i).1
  outgoing_map := by
    intro d i
    exact (smoothRetainedPorts I c d i).2.1
  continuation_map := smoothContinuation_map I c
  through_map := by
    intro d
    exact (smoothRetainedPorts I c d 0).2.2
  overBranch_map := smoothRetained_overBranch I c
  crossingSign_map := smoothRetained_crossingSign I c

end DirectGLSSW.HOMFLY














