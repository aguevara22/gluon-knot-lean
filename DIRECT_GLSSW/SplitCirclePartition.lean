import SplitCircleActual
import GeminiLowest.LayeredSublinkFactorization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW DirectGLSSW.PermutationOrbits GeminiLowest

variable (D : PLLinkDiagram) (R : ℝ)

def codeSide : ArcCode D R → Fin 2
  | .inl _ => 0
  | .inr _ => 1

theorem codeSide_next (e : ArcCode D R) :
    codeSide D R (continuationCode D R e) = codeSide D R e := by
  cases e <;> rfl

theorem codeSide_pow (e : ArcCode D R) (n : ℕ) :
    codeSide D R ((continuationCode D R ^ n) e) = codeSide D R e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, codeSide_next, ih]

theorem codeSide_sameCycle (e f : ArcCode D R)
    (h : (continuationCode D R).SameCycle e f) :
    codeSide D R e = codeSide D R f := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn, codeSide_pow]

def codeComponentSide : Component (continuationCode D R) → Fin 2 :=
  Quotient.lift (codeSide D R) (fun e f h => codeSide_sameCycle D R e f h)

@[simp] theorem codeComponentSide_componentOf (e : ArcCode D R) :
    codeComponentSide D R (componentOf (continuationCode D R) e) = codeSide D R e := rfl

variable (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
  (hright : ∀ v : Fin (rightTriangle R).nVertex,
    R < ((rightTriangle R).vertexPoint v).1)

def J : PLLinkDiagram := joinedDiagram D R hleft hright

def A : ArcCode D R ≃ Fin (J D R hleft hright).nArc := arcEquiv D R

def joinedSideOfArc (e : Fin (J D R hleft hright).nArc) : Fin 2 :=
  codeSide D R ((A D R hleft hright).symm e)

theorem joinedSide_next (e : Fin (J D R hleft hright).nArc) :
    joinedSideOfArc D R hleft hright ((J D R hleft hright).continuation e) =
      joinedSideOfArc D R hleft hright e := by
  change codeSide D R
      ((A D R hleft hright).symm
        ((A D R hleft hright)
          (continuationCode D R ((A D R hleft hright).symm e)))) = _
  simp only [Equiv.symm_apply_apply, codeSide_next]
  rfl

theorem joinedSide_pow (e : Fin (J D R hleft hright).nArc) (n : ℕ) :
    joinedSideOfArc D R hleft hright (((J D R hleft hright).continuation ^ n) e) =
      joinedSideOfArc D R hleft hright e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, joinedSide_next, ih]

theorem joinedSide_sameCycle (e f : Fin (J D R hleft hright).nArc)
    (h : (J D R hleft hright).continuation.SameCycle e f) :
    joinedSideOfArc D R hleft hright e = joinedSideOfArc D R hleft hright f := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn, joinedSide_pow]

def joinedSideOfComponent : diagramComponent (J D R hleft hright) → Fin 2 :=
  Quotient.lift (joinedSideOfArc D R hleft hright)
    (fun e f h => joinedSide_sameCycle D R hleft hright e f h)

theorem joinedSide_componentOf (e : Fin (J D R hleft hright).nArc) :
    joinedSideOfComponent D R hleft hright
      (componentOf (J D R hleft hright).continuation e) =
      joinedSideOfArc D R hleft hright e := rfl

theorem joinedSide_old (e : Fin D.nArc) :
    joinedSideOfArc D R hleft hright ((A D R hleft hright) (.inl e)) = 0 := by
  simp [joinedSideOfArc, A, codeSide]

theorem joinedSide_circle (e : Fin (rightTriangle R).nArc) :
    joinedSideOfArc D R hleft hright ((A D R hleft hright) (.inr e)) = 1 := by
  simp [joinedSideOfArc, A, codeSide]

def joinedPartition (hD : 0 < D.nArc) :
    SublinkPartition (J D R hleft hright) (Fin 2) where
  block j := {
    components := {C | joinedSideOfComponent D R hleft hright C = j}
    nonempty := by
      fin_cases j
      · refine ⟨componentOf (J D R hleft hright).continuation
          ((A D R hleft hright) (.inl ⟨0, hD⟩)), ?_⟩
        simp only [Set.mem_setOf_eq, joinedSide_componentOf, joinedSide_old]
        rfl
      · refine ⟨componentOf (J D R hleft hright).continuation
          ((A D R hleft hright) (.inr (⟨0, by change 0 < 3; omega⟩ :
            Fin (rightTriangle R).nArc))), ?_⟩
        simp only [Set.mem_setOf_eq, joinedSide_componentOf, joinedSide_circle]
        rfl }
  unique C := by
    refine ⟨joinedSideOfComponent D R hleft hright C, ?_, ?_⟩
    · rfl
    · intro j hj
      exact hj.symm

theorem joinedPartition_blockIndex (hD : 0 < D.nArc)
    (C : diagramComponent (J D R hleft hright)) :
    blockIndex (joinedPartition D R hleft hright hD) C =
      joinedSideOfComponent D R hleft hright C := by
  apply blockIndex_eq_of_mem
  rfl

theorem joinedPartition_layered (hD : 0 < D.nArc) :
    IsLayeredPartition (joinedPartition D R hleft hright hD) := by
  intro c
  rw [joinedPartition_blockIndex, joinedPartition_blockIndex]
  have h0 (i : Fin 2) :
      joinedSideOfComponent D R hleft hright
        (componentOf (J D R hleft hright).continuation
          ((J D R hleft hright).incoming c i)) = 0 := by
    change joinedSideOfComponent D R hleft hright
      (componentOf (J D R hleft hright).continuation
        ((A D R hleft hright) (.inl (D.incoming c i)))) = 0
    rw [joinedSide_componentOf, joinedSide_old]
  rw [h0, h0]

theorem joinedPartition_right_crossing_count (hD : 0 < D.nArc) :
    (restrictSublink (J D R hleft hright)
      ((joinedPartition D R hleft hright hD).block 1)).nCrossing = 0 := by
  let P := joinedPartition D R hleft hright hD
  change Fintype.card (SublinkCrossing (J D R hleft hright) (P.block 1)) = 0
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun x => ?_⟩
  have hx := x.property (D.overBranch x.val)
  change joinedSideOfComponent D R hleft hright
    (componentOf (J D R hleft hright).continuation
      ((J D R hleft hright).outgoing x.val (D.overBranch x.val))) = 1 at hx
  have hzero : joinedSideOfComponent D R hleft hright
      (componentOf (J D R hleft hright).continuation
        ((J D R hleft hright).outgoing x.val (D.overBranch x.val))) = 0 := by
    change joinedSideOfComponent D R hleft hright
      (componentOf (J D R hleft hright).continuation
        ((A D R hleft hright) (.inl (D.outgoing x.val (D.overBranch x.val))))) = 0
    rw [joinedSide_componentOf, joinedSide_old]
  exact (Fin.zero_ne_one : (0 : Fin 2) ≠ 1) (hzero.symm.trans hx)

end DirectGLSSW.HOMFLY.SplitCircleConstructor

