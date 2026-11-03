import DirectGLSSW.HOMFLY.HOMFLYSignedDiagramIso
import DirectGLSSW.HOMFLY.HOMFLYSkeinEvaluator
import DirectGLSSW.OrbitNormalization

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- A signed diagram isomorphism transports the orbit components of its
continuation permutations. -/
noncomputable def SignedDiagramIso.componentEquiv {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) : diagramComponent D ≃ diagramComponent E :=
  DirectGLSSW.PermutationOrbits.componentEquivOfIntertwining
    I.arcEquiv D.continuation E.continuation I.continuation_map

@[simp] theorem SignedDiagramIso.componentEquiv_componentOf
    {D E : PLLinkDiagram} (I : SignedDiagramIso D E) (e : Fin D.nArc) :
    I.componentEquiv (PermutationOrbits.componentOf D.continuation e) =
      PermutationOrbits.componentOf E.continuation (I.arcEquiv e) := by
  exact DirectGLSSW.PermutationOrbits.componentEquivOfIntertwining_componentOf
    I.arcEquiv D.continuation E.continuation I.continuation_map e

/-- Iteration commutes with the arc map, so traversal order can be transported
from the same chosen base arc. -/
theorem SignedDiagramIso.continuation_pow_map {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (n : ℕ) (e : Fin D.nArc) :
    I.arcEquiv ((D.continuation ^ n) e) =
      (E.continuation ^ n) (I.arcEquiv e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, I.continuation_map,
        ih, pow_succ', Equiv.Perm.mul_apply]

theorem SignedDiagramIso.componentCount_eq {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) : diagramComponentCount D = diagramComponentCount E :=
  DirectGLSSW.PermutationOrbits.componentCount_eq_of_intertwining
    I.arcEquiv D.continuation E.continuation I.continuation_map

noncomputable def SignedDiagramIso.fibreEquiv {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (C : diagramComponent D) :
    PermutationOrbits.Fibre D.continuation C ≃
      PermutationOrbits.Fibre E.continuation (I.componentEquiv C) where
  toFun x := ⟨I.arcEquiv x.val, by
    exact (I.componentEquiv_componentOf x.val).trans
      (congrArg I.componentEquiv x.property)⟩
  invFun y := ⟨I.arcEquiv.symm y.val, by
    apply I.componentEquiv.injective
    rw [I.componentEquiv_componentOf]
    simpa using y.property⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro y; apply Subtype.ext; simp

noncomputable def SignedDiagramIso.fibreEquivAt {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (e : Fin D.nArc) :
    PermutationOrbits.Fibre D.continuation
        (PermutationOrbits.componentOf D.continuation e) ≃
      PermutationOrbits.Fibre E.continuation
        (PermutationOrbits.componentOf E.continuation (I.arcEquiv e)) where
  toFun x := ⟨I.arcEquiv x.val, by
    exact (I.componentEquiv_componentOf x.val).trans
      (congrArg I.componentEquiv x.property)⟩
  invFun y := ⟨I.arcEquiv.symm y.val, by
    apply I.componentEquiv.injective
    rw [I.componentEquiv_componentOf, I.componentEquiv_componentOf]
    simpa only [Equiv.apply_symm_apply] using y.property⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro y; apply Subtype.ext; simp

theorem SignedDiagramIso.orbitEnumeration_map {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (e : Fin D.nArc)
    (i : Fin (Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation e)))) :
    I.fibreEquiv (PermutationOrbits.componentOf D.continuation e)
      (PermutationOrbits.orbitEnumeration D.continuation e i) =
    PermutationOrbits.orbitEnumeration E.continuation (I.arcEquiv e)
      (Fin.cast (Fintype.card_congr (I.fibreEquivAt e)) i) := by
  apply Subtype.ext
  change I.arcEquiv ((PermutationOrbits.orbitEnumeration
    D.continuation e i).val) =
    (PermutationOrbits.orbitEnumeration E.continuation (I.arcEquiv e)
      (Fin.cast (Fintype.card_congr (I.fibreEquivAt e)) i)).val
  rw [PermutationOrbits.orbitEnumeration_apply_val,
    PermutationOrbits.orbitEnumeration_apply_val]
  rw [I.continuation_pow_map]
  simp

/-- Transport a complete based traversal across a signed combinatorial
isomorphism, carrying its component order and its selected base arcs. -/
noncomputable def SignedDiagramIso.transportTraversal {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D) : BasedTraversal E where
  componentIndex := I.componentEquiv.symm.trans
    (T.componentIndex.trans
      (Equiv.cast (congrArg Fin I.componentCount_eq)))
  baseArc := fun C => by
    let C0 := I.componentEquiv.symm C
    let a := T.baseArc C0
    refine ⟨I.arcEquiv a.val, ?_⟩
    calc
      PermutationOrbits.componentOf E.continuation (I.arcEquiv a.val) =
          I.componentEquiv (PermutationOrbits.componentOf D.continuation a.val) :=
            (I.componentEquiv_componentOf a.val).symm
      _ = I.componentEquiv C0 := congrArg I.componentEquiv a.property
      _ = C := I.componentEquiv.apply_symm_apply C

@[simp] theorem SignedDiagramIso.transportTraversal_componentIndex
    {D E : PLLinkDiagram} (I : SignedDiagramIso D E) (T : BasedTraversal D)
    (C : diagramComponent E) :
    (I.transportTraversal T).componentIndex C =
      Equiv.cast (congrArg Fin I.componentCount_eq)
        (T.componentIndex (I.componentEquiv.symm C)) := rfl

@[simp] theorem SignedDiagramIso.transportTraversal_baseArc_val
    {D E : PLLinkDiagram} (I : SignedDiagramIso D E) (T : BasedTraversal D)
    (C : diagramComponent E) :
    ((I.transportTraversal T).baseArc C).val =
      I.arcEquiv (T.baseArc (I.componentEquiv.symm C)).val := rfl

theorem visitPosition_lt_orbitCard {D : PLLinkDiagram} (T : BasedTraversal D)
    (e : Fin D.nArc) :
    visitPosition T e < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation
        (T.baseArc (PermutationOrbits.componentOf D.continuation e)).val)) := by
  simp [visitPosition]

theorem SignedDiagramIso.visitPosition_transport {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D) (e : Fin D.nArc) :
    visitPosition (I.transportTraversal T) (I.arcEquiv e) = visitPosition T e := by
  let C := PermutationOrbits.componentOf D.continuation e
  let b := T.baseArc C
  let C' := PermutationOrbits.componentOf E.continuation (I.arcEquiv e)
  let b' := (I.transportTraversal T).baseArc C'
  have hC : I.componentEquiv.symm C' = C := by
    apply I.componentEquiv.injective
    simp [C, C']
  have hbase : b'.val = I.arcEquiv b.val := by
    change ((I.transportTraversal T).baseArc C').val = I.arcEquiv b.val
    rw [SignedDiagramIso.transportTraversal_baseArc_val, hC]
  let nS := Fintype.card (PermutationOrbits.Fibre D.continuation
    (PermutationOrbits.componentOf D.continuation b.val))
  let nT := Fintype.card (PermutationOrbits.Fibre E.continuation
    (PermutationOrbits.componentOf E.continuation b'.val))
  have hcard : nS = nT := by
    dsimp [nS, nT]
    calc
      Fintype.card (PermutationOrbits.Fibre D.continuation
          (PermutationOrbits.componentOf D.continuation b.val)) =
        Fintype.card (PermutationOrbits.Fibre E.continuation
          (PermutationOrbits.componentOf E.continuation (I.arcEquiv b.val))) :=
        Fintype.card_congr (I.fibreEquivAt b.val)
      _ = Fintype.card (PermutationOrbits.Fibre E.continuation
          (PermutationOrbits.componentOf E.continuation b'.val)) := by rw [← hbase]
  let s : Fin nS := ⟨visitPosition T e, visitPosition_lt_orbitCard T e⟩
  let t : Fin nT := ⟨visitPosition (I.transportTraversal T) (I.arcEquiv e),
    visitPosition_lt_orbitCard (I.transportTraversal T) (I.arcEquiv e)⟩
  let q := PermutationOrbits.orbitEnumeration E.continuation b'.val
  have hqt : q (Fin.cast hcard s) = q t := by
    apply Subtype.ext
    change (PermutationOrbits.orbitEnumeration E.continuation b'.val
      (Fin.cast hcard s)).val =
        (PermutationOrbits.orbitEnumeration E.continuation b'.val t).val
    have hcast : (Fin.cast hcard s).val = s.val := by
      rfl
    simp only [PermutationOrbits.orbitEnumeration_apply_val, hcast]
    calc
      (E.continuation ^ (s : ℕ)) b'.val =
          (E.continuation ^ (s : ℕ)) (I.arcEquiv b.val) := by rw [hbase]
      _ = I.arcEquiv ((D.continuation ^ (s : ℕ)) b.val) :=
          (I.continuation_pow_map (s : ℕ) b.val).symm
      _ = I.arcEquiv e := by
          exact congrArg I.arcEquiv (visitPosition_reconstruct T e)
      _ = (E.continuation ^ (t : ℕ)) b'.val := by
          simpa [b', SignedDiagramIso.transportTraversal_baseArc_val] using
            (visitPosition_reconstruct (I.transportTraversal T) (I.arcEquiv e)).symm
  have hindex : Fin.cast hcard s = t := q.injective hqt
  have hs : s.val = visitPosition T e := rfl
  have ht : t.val = visitPosition (I.transportTraversal T) (I.arcEquiv e) := rfl
  calc
    visitPosition (I.transportTraversal T) (I.arcEquiv e) = t.val := ht.symm
    _ = (Fin.cast hcard s).val := (congrArg Fin.val hindex).symm
    _ = s.val := by simp
    _ = visitPosition T e := hs

theorem rankBefore_cast_iff {n m : ℕ} (h : n = m) (x y : Fin n × ℕ) :
    rankBefore (Equiv.cast (congrArg Fin h) x.1, x.2)
      (Equiv.cast (congrArg Fin h) y.1, y.2) ↔ rankBefore x y := by
  cases h
  rfl

theorem SignedDiagramIso.visitRank_transport {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D) (e : Fin D.nArc) :
    visitRank (I.transportTraversal T) (I.arcEquiv e) =
      (Equiv.cast (congrArg Fin I.componentCount_eq)
          (T.componentIndex (PermutationOrbits.componentOf D.continuation e)),
        visitPosition T e) := by
  apply Prod.ext
  · change (I.transportTraversal T).componentIndex
      (PermutationOrbits.componentOf E.continuation (I.arcEquiv e)) = _
    rw [I.transportTraversal_componentIndex]
    congr 1
    apply congrArg T.componentIndex
    apply I.componentEquiv.injective
    simp [SignedDiagramIso.componentEquiv_componentOf]
  · exact I.visitPosition_transport T e

theorem SignedDiagramIso.rankBefore_transport {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D) (e f : Fin D.nArc) :
    rankBefore (visitRank (I.transportTraversal T) (I.arcEquiv e))
      (visitRank (I.transportTraversal T) (I.arcEquiv f)) ↔
    rankBefore (visitRank T e) (visitRank T f) := by
  rw [I.visitRank_transport T e, I.visitRank_transport T f]
  change rankBefore
      (Equiv.cast (congrArg Fin I.componentCount_eq)
        (T.componentIndex (PermutationOrbits.componentOf D.continuation e)),
        visitPosition T e)
      (Equiv.cast (congrArg Fin I.componentCount_eq)
        (T.componentIndex (PermutationOrbits.componentOf D.continuation f)),
        visitPosition T f) ↔
    rankBefore
      (T.componentIndex (PermutationOrbits.componentOf D.continuation e), visitPosition T e)
      (T.componentIndex (PermutationOrbits.componentOf D.continuation f), visitPosition T f)
  exact rankBefore_cast_iff (n := diagramComponentCount D)
    (m := diagramComponentCount E) I.componentCount_eq
    (T.componentIndex (PermutationOrbits.componentOf D.continuation e), visitPosition T e)
    (T.componentIndex (PermutationOrbits.componentOf D.continuation f), visitPosition T f)

theorem SignedDiagramIso.firstVisitedBranch_transport {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D) (c : Fin D.nCrossing) :
    firstVisitedBranch (I.transportTraversal T) (I.crossingEquiv c) =
      firstVisitedBranch T c := by
  classical
  unfold firstVisitedBranch
  rw [← I.incoming_map c 0, ← I.incoming_map c 1]
  rw [I.rankBefore_transport T (D.incoming c 0) (D.incoming c 1)]

theorem SignedDiagramIso.badAt_transport {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D) (c : Fin D.nCrossing) :
    badAt (I.transportTraversal T) (I.crossingEquiv c) ↔ badAt T c := by
  simp [badAt, I.firstVisitedBranch_transport, I.overBranch_map]

theorem SignedDiagramIso.badCrossings_map {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D) :
    badCrossings (I.transportTraversal T) =
      (badCrossings T).map I.crossingEquiv.toEmbedding := by
  classical
  ext d
  let c := I.crossingEquiv.symm d
  have hd : I.crossingEquiv c = d := I.crossingEquiv.apply_symm_apply d
  rw [← hd]
  simp [badCrossings, I.badAt_transport]

theorem SignedDiagramIso.badCrossings_card_eq {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D) :
    (badCrossings (I.transportTraversal T)).card = (badCrossings T).card := by
  rw [I.badCrossings_map]
  simp

theorem SignedDiagramIso.unlinkValue_eq {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) : descendingUnlinkValue D = descendingUnlinkValue E := by
  have harc : D.nArc = E.nArc := by
    have h := Fintype.card_congr I.arcEquiv
    simpa using h
  simp [descendingUnlinkValue, harc, I.componentCount_eq]

/-- The evaluator is transport invariant in the terminal case: both traversals
have no bad crossings, and their source unlink values agree by component
reindexing. This handles the base case without asserting traversal
independence for recursive diagrams. -/
theorem SignedDiagramIso.descendingEvaluator_terminal_eq {D E : PLLinkDiagram}
    (I : SignedDiagramIso D E) (T : BasedTraversal D)
    (h : badCrossings T = ∅) :
    descendingLaurentEvaluator E (I.transportTraversal T) =
      descendingLaurentEvaluator D T := by
  have hE : (badCrossings (I.transportTraversal T)).Nonempty = False := by
    rw [I.badCrossings_map, h]
    simp
  have hD : (badCrossings T).Nonempty = False := by simp [h]
  rw [descendingLaurentEvaluator_terminal E (I.transportTraversal T) hE,
    descendingLaurentEvaluator_terminal D T hD]
  exact I.unlinkValue_eq.symm

end DirectGLSSW.HOMFLY





















