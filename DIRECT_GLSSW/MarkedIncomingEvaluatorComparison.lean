import PLMarkedRefinementTargets
import MarkedCycleEqualGaps
import HOMFLYSignedIsoNormalized
import SignedDiagramIsoFromIncoming
import ChildMarkedCycleComparison
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv Coefficients ArcSubdivision MarkedCycleGaps
attribute [local instance] Classical.propDecidable

/-- Common crossing labels give injective actual incoming marks. -/
theorem labelledIncoming_injective {κ : Type*} (D : PLLinkDiagram)
    (u : κ ≃ Fin D.nCrossing) :
    Function.Injective (fun m : κ × Fin 2=>D.incoming (u m.1) m.2) := by
  intro x y h
  have he:=@incomingMark_injective D (u x.1,x.2) (u y.1,y.2) h
  exact Prod.ext (u.injective (congrArg Prod.fst he))
    (congrArg (fun z : Fin D.nCrossing × Fin 2=>z.2) he)

/-- Physical finite common refinements turn matching cyclic incoming-port
labels and crossing data into equality of every normalized evaluator. -/
theorem normalizedEvaluator_eq_of_matching_incoming
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (H : (D : PLLinkDiagram) → 0<D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D E : PLLinkDiagram) (hD : 0<D.nArc) (hE : 0<E.nArc)
    (u : κ ≃ Fin D.nCrossing) (v : κ ≃ Fin E.nCrossing)
    (hp : D.continuation.IsCycleOn Set.univ) (hq : E.continuation.IsCycleOn Set.univ)
    (hnext : next D.continuation (fun m:κ×Fin 2=>D.incoming (u m.1) m.2) (labelledIncoming_injective D u) =
      next E.continuation (fun m:κ×Fin 2=>E.incoming (v m.1) m.2) (labelledIncoming_injective E v))
    (ht : ∀j,D.through (u j)=E.through (v j))
    (ho : ∀j,D.overBranch (u j)=E.overBranch (v j))
    (hs : ∀j,crossingSign D (u j)=crossingSign E (v j)) : H D hD=H E hE := by
  let md : κ×Fin 2→Fin D.nArc:=fun m=>D.incoming (u m.1) m.2
  let me : κ×Fin 2→Fin E.nArc:=fun m=>E.incoming (v m.1) m.2
  have hid : Function.Injective md:=labelledIncoming_injective D u
  have hie : Function.Injective me:=labelledIncoming_injective E v
  obtain ⟨ld,le,hlen⟩:=exists_common_markedRefinements D md hid E me hie
  let sd:=markedRefinementState D md ld
  let se:=markedRefinementState E me le
  have hpd : sd.1.continuation.IsCycleOn Set.univ:=markedRefinement_isCycleOn D md hp ld
  have hpe : se.1.continuation.IsCycleOn Set.univ:=markedRefinement_isCycleOn E me hq le
  have hijd : Function.Injective sd.2:=markedRefinement_injective D md hid ld
  have hije : Function.Injective se.2:=markedRefinement_injective E me hie le
  have hg : ∀m,gapLength sd.1.continuation sd.2 m=gapLength se.1.continuation se.2 m:=
    fun m=>(hlen m).1.trans (hlen m).2.symm
  have hn : next sd.1.continuation sd.2 hijd=next se.1.continuation se.2 hije:=
    (markedRefinement_next D md hid ld).trans (hnext.trans (markedRefinement_next E me hie le).symm)
  let f:=equalGapArcEquiv sd.1.continuation se.1.continuation sd.2 se.2 hpd hpe hijd hije hg
  let cd:=markedRefinementCrossingEquiv D md ld
  let ce:=markedRefinementCrossingEquiv E me le
  let g:=cd.symm.trans ((u.symm.trans v).trans ce)
  have hcont : ∀x,f (sd.1.continuation x)=se.1.continuation (f x):=
    equalGapArcEquiv_continuation _ _ _ _ _ _ _ _ _ hn
  have hmark : ∀m,f (sd.2 m)=se.2 m:=equalGapArcEquiv_mark _ _ _ _ _ _ _ _ _ hn
  have hin : ∀k i,f (sd.1.incoming k i)=se.1.incoming (g k) i := by
    intro k i
    obtain ⟨j,rfl⟩:=(u.trans cd).surjective k
    have hd : sd.1.incoming (cd (u j)) i=sd.2 (j,i) := by
      rw [markedRefinement_incoming,markedRefinement_mark]
    have he : se.1.incoming (ce (v j)) i=se.2 (j,i) := by
      rw [markedRefinement_incoming,markedRefinement_mark]
    change f (sd.1.incoming (cd (u j)) i)=se.1.incoming (g (cd (u j))) i
    have hgc : g (cd (u j))=ce (v j) := by simp only [g,Equiv.trans_apply,Equiv.symm_apply_apply]
    rw [hgc,hd,he,hmark]
  have hthrough : ∀k,sd.1.through k=se.1.through (g k) := by
    intro k
    obtain ⟨j,rfl⟩:=(u.trans cd).surjective k
    change sd.1.through (cd (u j))=se.1.through (g (cd (u j)))
    have hgc : g (cd (u j))=ce (v j) := by simp only [g,Equiv.trans_apply,Equiv.symm_apply_apply]
    rw [hgc,markedRefinement_through,markedRefinement_through,ht]
  have hover : ∀k,sd.1.overBranch k=se.1.overBranch (g k) := by
    intro k
    obtain ⟨j,rfl⟩:=(u.trans cd).surjective k
    change sd.1.overBranch (cd (u j))=se.1.overBranch (g (cd (u j)))
    have hgc : g (cd (u j))=ce (v j) := by simp only [g,Equiv.trans_apply,Equiv.symm_apply_apply]
    rw [hgc,markedRefinement_overBranch,markedRefinement_overBranch,ho]
  have hsign : ∀k,crossingSign sd.1 k=crossingSign se.1 (g k) := by
    intro k
    obtain ⟨j,rfl⟩:=(u.trans cd).surjective k
    change crossingSign sd.1 (cd (u j))=crossingSign se.1 (g (cd (u j)))
    have hgc : g (cd (u j))=ce (v j) := by simp only [g,Equiv.trans_apply,Equiv.symm_apply_apply]
    rw [hgc,markedRefinement_crossingSign,markedRefinement_crossingSign,hs]
  let I : SignedDiagramIso sd.1 se.1:=SignedDiagramIso.ofIncoming f g hin hcont hthrough hover hsign
  have hsd : 0<sd.1.nArc := by change 0<(markedRefinementState D md ld).1.nArc;rw [markedRefinement_nArc];omega
  have hse : 0<se.1.nArc := by change 0<(markedRefinementState E me le).1.nArc;rw [markedRefinement_nArc];omega
  exact (markedRefinement_normalizedEvaluator_eq D md H hH ld hD).symm.trans
    ((SignedDiagramIso.normalizedEvaluator_eq H hH I hsd hse).trans
      (markedRefinement_normalizedEvaluator_eq E me H hH le hE))
end DirectGLSSW.HOMFLY
