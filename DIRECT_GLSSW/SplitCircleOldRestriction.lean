import SplitCircleComponent
import DirectGLSSW.HOMFLY.HOMFLYSignedDiagramIso

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW DirectGLSSW.PermutationOrbits GeminiLowest

variable (D : PLLinkDiagram) (R : ℝ)
  (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
  (hright : ∀ v : Fin (rightTriangle R).nVertex,
    R < ((rightTriangle R).vertexPoint v).1)
  (hD : 0 < D.nArc)

def B : Sublink (J D R hleft hright) :=
  (joinedPartition D R hleft hright hD).block 0

private theorem selectedArc_side (a : SublinkArc (J D R hleft hright)
    (B D R hleft hright hD)) :
    joinedSideOfArc D R hleft hright a.val = 0 := by
  exact a.property

private theorem existsLeftArcOfSelected
    (a : SublinkArc (J D R hleft hright) (B D R hleft hright hD)) :
    ∃ e : Fin D.nArc, (A D R hleft hright) (.inl e) = a.val := by
  rcases ha : (A D R hleft hright).symm a.val with e | e
  · exact ⟨e, by rw [← (A D R hleft hright).apply_symm_apply a.val, ha]⟩
  · have hside := selectedArc_side D R hleft hright hD a
    have h1 : joinedSideOfArc D R hleft hright a.val = 1 := by
      simp [joinedSideOfArc, ha, codeSide]
    exact False.elim ((Fin.zero_ne_one : (0 : Fin 2) ≠ 1) (hside.symm.trans h1))

private def leftArcOfSelected
    (a : SublinkArc (J D R hleft hright) (B D R hleft hright hD)) :
    Fin D.nArc := Classical.choose (existsLeftArcOfSelected D R hleft hright hD a)

private def selectedOfLeftArc (e : Fin D.nArc) :
    SublinkArc (J D R hleft hright) (B D R hleft hright hD) :=
  ⟨(A D R hleft hright) (.inl e), by
    change joinedSideOfComponent D R hleft hright
      (componentOf (J D R hleft hright).continuation
        ((A D R hleft hright) (.inl e))) = 0
    rw [joinedSide_componentOf, joinedSide_old]⟩

private theorem leftArcOfSelected_val
    (a : SublinkArc (J D R hleft hright) (B D R hleft hright hD)) :
    (A D R hleft hright) (.inl (leftArcOfSelected D R hleft hright hD a)) = a.val := by
  exact Classical.choose_spec (existsLeftArcOfSelected D R hleft hright hD a)

private theorem leftArcOfSelected_left (e : Fin D.nArc) :
    leftArcOfSelected D R hleft hright hD
      (selectedOfLeftArc D R hleft hright hD e) = e := by
  apply Sum.inl_injective
  apply (A D R hleft hright).injective
  exact leftArcOfSelected_val D R hleft hright hD _

def leftArcEquiv :
    SublinkArc (J D R hleft hright) (B D R hleft hright hD) ≃ Fin D.nArc where
  toFun := leftArcOfSelected D R hleft hright hD
  invFun := selectedOfLeftArc D R hleft hright hD
  left_inv := by
    intro a
    apply Subtype.ext
    exact leftArcOfSelected_val D R hleft hright hD a
  right_inv := leftArcOfSelected_left D R hleft hright hD

def leftRestrictedArcEquiv :
    Fin (restrictSublink (J D R hleft hright)
      (B D R hleft hright hD)).nArc ≃ Fin D.nArc :=
  (sublinkArcEquiv (J D R hleft hright) (B D R hleft hright hD)).trans
    (leftArcEquiv D R hleft hright hD)

@[simp] theorem leftRestrictedArcEquiv_val
    (e : Fin (restrictSublink (J D R hleft hright)
      (B D R hleft hright hD)).nArc) :
    (A D R hleft hright) (.inl (leftRestrictedArcEquiv D R hleft hright hD e)) =
      sublinkOldArc (J D R hleft hright) (B D R hleft hright hD) e :=
  leftArcOfSelected_val D R hleft hright hD _

def leftCrossingEquiv :
    Fin (restrictSublink (J D R hleft hright)
      (B D R hleft hright hD)).nCrossing ≃ Fin D.nCrossing :=
  (sublinkCrossingEquiv (J D R hleft hright) (B D R hleft hright hD)).trans
    (Equiv.ofBijective Subtype.val (by
      constructor
      · exact Subtype.val_injective
      · intro c
        refine ⟨⟨c, ?_⟩, rfl⟩
        intro i
        change joinedSideOfComponent D R hleft hright
          (componentOf (J D R hleft hright).continuation
            ((A D R hleft hright) (.inl (D.outgoing c i)))) = 0
        rw [joinedSide_componentOf, joinedSide_old]))

@[simp] theorem leftCrossingEquiv_val
    (c : Fin (restrictSublink (J D R hleft hright)
      (B D R hleft hright hD)).nCrossing) :
    leftCrossingEquiv D R hleft hright hD c =
      sublinkOldCrossing (J D R hleft hright) (B D R hleft hright hD) c := rfl

end DirectGLSSW.HOMFLY.SplitCircleConstructor


