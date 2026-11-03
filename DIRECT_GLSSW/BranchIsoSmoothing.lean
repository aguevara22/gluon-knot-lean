import BranchSignedDiagramIso
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.BranchSignedDiagramIso
open Equiv
variable {D E : PLLinkDiagram}
def retainedEquiv (I : BranchSignedDiagramIso D E) (c : Fin D.nCrossing) :
    {d:Fin D.nCrossing//d≠c} ≃ {d:Fin E.nCrossing//d≠I.crossingEquiv c} where
  toFun d:=⟨I.crossingEquiv d.val,fun h=>d.property (I.crossingEquiv.injective h)⟩
  invFun d:=⟨I.crossingEquiv.symm d.val,fun h=>d.property (by simpa using congrArg I.crossingEquiv h)⟩
  left_inv:=by intro d;apply Subtype.ext;simp
  right_inv:=by intro d;apply Subtype.ext;simp
def smoothCrossingEquiv (I : BranchSignedDiagramIso D E) (c : Fin D.nCrossing) :
    Fin (D.nCrossing-1) ≃ Fin (E.nCrossing-1) :=
  (_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm.trans
    ((I.retainedEquiv c).trans (_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv E (I.crossingEquiv c)))
def smoothArcEquiv (I : BranchSignedDiagramIso D E) (c : Fin D.nCrossing) : Fin (D.nArc+2) ≃ Fin (E.nArc+2):=
  (_root_.DirectGLSSW.HOMFLY.smoothArcEquiv D).symm.trans
    ((Equiv.sumCongr I.arcEquiv (I.branchEquiv c)).trans (_root_.DirectGLSSW.HOMFLY.smoothArcEquiv E))

theorem incoming_code (D : PLLinkDiagram) (c : Fin D.nCrossing) (i:Fin 2):
    smoothContinuationGeometryCode D c (Sum.inl (D.incoming c i))=Sum.inr i := by
  fin_cases i
  · exact smoothContinuationGeometryCode_incoming_zero D c
  · exact smoothContinuationGeometryCode_incoming_one D c

theorem smooth_code (I:BranchSignedDiagramIso D E) (c:Fin D.nCrossing)
    (x:SmoothArcCode D):
    (Equiv.sumCongr I.arcEquiv (I.branchEquiv c)) (smoothContinuationGeometryCode D c x)=
      smoothContinuationGeometryCode E (I.crossingEquiv c) ((Equiv.sumCongr I.arcEquiv (I.branchEquiv c)) x) := by
  cases x with
  | inl e =>
    by_cases he:∃i,e=D.incoming c i
    · obtain ⟨i,rfl⟩:=he
      rw [incoming_code]
      simp only [Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,I.incoming_map]
      rw [incoming_code]
    · have hd:∀i,e≠D.incoming c i:=by simpa only [not_exists] using he
      have he':∀i,I.arcEquiv e≠E.incoming (I.crossingEquiv c) i:=by
        intro i hh
        apply hd ((I.branchEquiv c).symm i)
        apply I.arcEquiv.injective
        rw [I.incoming_map,Equiv.apply_symm_apply]
        exact hh
      rw [smoothContinuationGeometryCode_other_arc D c e hd]
      simp only [Equiv.sumCongr_apply,Sum.map_inl]
      rw [smoothContinuationGeometryCode_other_arc E (I.crossingEquiv c) _ he',I.continuation_map]
  | inr i =>
    simp only [Equiv.sumCongr_apply,Sum.map_inr]
    rw [smoothContinuationGeometryCode_connector,smoothContinuationGeometryCode_connector]
    simp only [Sum.map_inl]
    rw [I.outgoing_map,I.through_map,branch_other]

theorem smooth_continuation (I:BranchSignedDiagramIso D E) (c:Fin D.nCrossing) (e:Fin (D.nArc+2)):
    I.smoothArcEquiv c ((smoothCrossing D c).continuation e)=
      (smoothCrossing E (I.crossingEquiv c)).continuation (I.smoothArcEquiv c e) := by
  have h:=I.smooth_code c ((_root_.DirectGLSSW.HOMFLY.smoothArcEquiv D).symm e)
  simp only [smoothArcEquiv,smoothCrossing,smoothContinuation,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact congrArg (_root_.DirectGLSSW.HOMFLY.smoothArcEquiv E) h

def smooth (I:BranchSignedDiagramIso D E) (c:Fin D.nCrossing):
    BranchSignedDiagramIso (smoothCrossing D c) (smoothCrossing E (I.crossingEquiv c)) where
  arcEquiv:=I.smoothArcEquiv c
  crossingEquiv:=I.smoothCrossingEquiv c
  branchEquiv:=fun d=>I.branchEquiv ((_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d).val
  incoming_map:=by
    intro d i
    let old:=((_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d).val
    simpa [smoothArcEquiv,smoothCrossingEquiv,smoothCrossing,smoothIncoming,retainedEquiv,old] using
      congrArg (fun e=>_root_.DirectGLSSW.HOMFLY.smoothArcEquiv E (Sum.inl e)) (I.incoming_map old i)
  outgoing_map:=by
    intro d i
    let old:=((_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d).val
    simpa [smoothArcEquiv,smoothCrossingEquiv,smoothCrossing,smoothOutgoing,retainedEquiv,old] using
      congrArg (fun e=>_root_.DirectGLSSW.HOMFLY.smoothArcEquiv E (Sum.inl e)) (I.outgoing_map old i)
  continuation_map:=I.smooth_continuation c
  through_map:=by
    intro d i
    simpa [smoothCrossingEquiv,smoothCrossing,smoothThrough,retainedEquiv] using
      I.through_map ((_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d).val i
  overBranch_map:=by
    intro d
    simpa [smoothCrossingEquiv,smoothCrossing,retainedEquiv] using
      I.overBranch_map ((_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d).val
  crossingSign_map:=by
    intro d
    let od:=(_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d
    let oe:=I.retainedEquiv c od
    have hd:=crossingSign_smoothRetained D c od.val od.property
    have he:=crossingSign_smoothRetained E (I.crossingEquiv c) oe.val oe.property
    calc
      crossingSign (smoothCrossing D c) d=crossingSign D od.val:=by simpa [od] using hd
      _=crossingSign E (I.crossingEquiv od.val):=I.crossingSign_map od.val
      _=crossingSign E oe.val:=rfl
      _=crossingSign (smoothCrossing E (I.crossingEquiv c)) (I.smoothCrossingEquiv c d):=he.symm
end DirectGLSSW.HOMFLY.BranchSignedDiagramIso
