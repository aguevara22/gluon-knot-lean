import DetachedOriginalPositions
import ProcessedChildOriginalCutWord
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

theorem orbitEnumeration_position_of_word
    {α : Type*} [Fintype α] (p : Equiv.Perm α) (root : α)
    {N : ℕ} (f : Fin N → α) (hw : orbitWord p root = List.ofFn f)
    (i : Fin N) (hi : componentOf p (f i) = componentOf p root) :
    ((orbitEnumeration p root).symm ⟨f i,hi⟩).val = i.val := by
  have hlen : Fintype.card (Fibre p (componentOf p root)) = N := by
    simpa only [orbitWord_length, List.length_ofFn] using congrArg List.length hw
  have hib : i.val < Fintype.card (Fibre p (componentOf p root)) := by
    rw [hlen]
    exact i.isLt
  let j : Fin (Fintype.card (Fibre p (componentOf p root))) := ⟨i.val,hib⟩
  have he : (orbitEnumeration p root j).val = f i := by
    have hh := congrArg (fun xs : List α => xs[i.val]?) hw
    simpa [orbitWord, List.getElem?_ofFn, hib, i.isLt, j] using hh
  have hsub : orbitEnumeration p root j = ⟨f i,hi⟩ := Subtype.ext he
  have hs := congrArg (fun x => ((orbitEnumeration p root).symm x).val) hsub
  simpa only [Equiv.symm_apply_apply] using hs.symm

variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

theorem detachedOldOrbitArc_position (j : Fin (detachedOrbitSize t c R-1)) :
    ((detachedOrbitEquiv t c R).symm (detachedOldOrbitArc c R j)).val = j.val+1 := by
  simp only [detachedOldOrbitArc, Equiv.symm_apply_apply, detachedOldOrbitIndex]

theorem MarkedParentTrace.detachedIncoming_position
    (d : Fin R.diagram.nCrossing) (i : Fin 2) :
    ∃ j : Fin (detachedOrbitSize t c R-1),
      ((detachedOrbitEquiv t c R).symm (R.diagram.incoming d i)).val = j.val+1 ∧
      visitPosition s.2.1 (s.1.incoming (h.detachedCrossingOrigin c R d) i) =
        visitPosition s.2.1 (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)+j.val := by
  obtain ⟨j,hj,ho⟩ := h.detachedCrossingOrigin_incoming_position c hc R d i
  refine ⟨j, ?_, ?_⟩
  · rw [←hj]
    exact detachedOldOrbitArc_position c R j
  · rw [←ho]
    exact h.detachedOriginalArc_visitPosition c hc R j

include hc in
theorem MarkedParentTrace.detachedIncoming_order
    (d e : Fin R.diagram.nCrossing) (i j : Fin 2) :
    ((detachedOrbitEquiv t c R).symm (R.diagram.incoming d i)).val <
        ((detachedOrbitEquiv t c R).symm (R.diagram.incoming e j)).val ↔
      visitPosition s.2.1 (s.1.incoming (h.detachedCrossingOrigin c R d) i) <
        visitPosition s.2.1 (s.1.incoming (h.detachedCrossingOrigin c R e) j) := by
  obtain ⟨k,hk,hko⟩ := h.detachedIncoming_position c hc R d i
  obtain ⟨l,hl,hlo⟩ := h.detachedIncoming_position c hc R e j
  rw [hk,hl,hko,hlo]
  omega

theorem MarkedParentTrace.detachedOriginalArc_cut_component
    (i : Fin (detachedOrbitSize t c R-1)) :
    componentOf (cutContinuation s.1 (h.crossingOrigin c)) (h.detachedOriginalArc c hc R i) =
      componentOf (cutContinuation s.1 (h.crossingOrigin c))
        (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) := by
  apply (componentOf_eq_iff _ _ _).mpr
  apply Equiv.Perm.SameCycle.symm
  apply (mem_orbitWord_iff _ _ _).mp
  rw [h.detachedOriginalCut_orbitWord c hc R]
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem MarkedParentTrace.detachedOriginalArc_cut_position
    (i : Fin (detachedOrbitSize t c R-1)) :
    ((orbitEnumeration (cutContinuation s.1 (h.crossingOrigin c))
      (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).symm
      ⟨h.detachedOriginalArc c hc R i,h.detachedOriginalArc_cut_component c hc R i⟩).val = i.val :=
  orbitEnumeration_position_of_word _ _ _ (h.detachedOriginalCut_orbitWord c hc R) _ _

theorem MarkedParentTrace.detachedIncoming_cut_component
    (d : Fin R.diagram.nCrossing) (i : Fin 2) :
    componentOf (cutContinuation s.1 (h.crossingOrigin c))
      (s.1.incoming (h.detachedCrossingOrigin c R d) i) =
      componentOf (cutContinuation s.1 (h.crossingOrigin c))
        (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) := by
  obtain ⟨j,_,hj⟩ := h.detachedCrossingOrigin_incoming_position c hc R d i
  rw [←hj]
  exact h.detachedOriginalArc_cut_component c hc R j

theorem MarkedParentTrace.detachedIncoming_cut_position
    (d : Fin R.diagram.nCrossing) (i : Fin 2) :
    ((detachedOrbitEquiv t c R).symm (R.diagram.incoming d i)).val =
      ((orbitEnumeration (cutContinuation s.1 (h.crossingOrigin c))
        (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).symm
        ⟨s.1.incoming (h.detachedCrossingOrigin c R d) i,
          h.detachedIncoming_cut_component c hc R d i⟩).val + 1 := by
  obtain ⟨j,hj,ho⟩ := h.detachedCrossingOrigin_incoming_position c hc R d i
  rw [←hj,detachedOldOrbitArc_position]
  have hp := h.detachedOriginalArc_cut_position c hc R j
  have hs : (⟨s.1.incoming (h.detachedCrossingOrigin c R d) i,
      h.detachedIncoming_cut_component c hc R d i⟩ :
      Fibre (cutContinuation s.1 (h.crossingOrigin c))
        (componentOf (cutContinuation s.1 (h.crossingOrigin c))
          (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))) =
      ⟨h.detachedOriginalArc c hc R j,h.detachedOriginalArc_cut_component c hc R j⟩ :=
    Subtype.ext ho.symm
  rw [hs,hp]

theorem MarkedParentTrace.detachedIncoming_cut_order
    (d e : Fin R.diagram.nCrossing) (i j : Fin 2) :
    ((detachedOrbitEquiv t c R).symm (R.diagram.incoming d i)).val <
        ((detachedOrbitEquiv t c R).symm (R.diagram.incoming e j)).val ↔
      ((orbitEnumeration (cutContinuation s.1 (h.crossingOrigin c))
        (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).symm
        ⟨s.1.incoming (h.detachedCrossingOrigin c R d) i,
          h.detachedIncoming_cut_component c hc R d i⟩).val <
      ((orbitEnumeration (cutContinuation s.1 (h.crossingOrigin c))
        (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).symm
        ⟨s.1.incoming (h.detachedCrossingOrigin c R e) j,
          h.detachedIncoming_cut_component c hc R e j⟩).val := by
  rw [h.detachedIncoming_cut_position c hc R d i,
    h.detachedIncoming_cut_position c hc R e j]
  omega










end DirectGLSSW.HOMFLY
