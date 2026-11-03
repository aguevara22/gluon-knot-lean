import SplitCirclePartition

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW DirectGLSSW.PermutationOrbits GeminiLowest

variable (D : PLLinkDiagram) (R : ℝ)
  (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
  (hright : ∀ v : Fin (rightTriangle R).nVertex,
    R < ((rightTriangle R).vertexPoint v).1)

private def E (e : Fin (rightTriangle R).nArc) :
    Fin (J D R hleft hright).nArc :=
  A D R hleft hright (.inr e)

theorem right_next (e : Fin (rightTriangle R).nArc) :
    (J D R hleft hright).continuation (E D R hleft hright e) =
      E D R hleft hright ((rightTriangle R).continuation e) := by
  change (A D R hleft hright)
    (continuationCode D R ((A D R hleft hright).symm
      ((A D R hleft hright) (.inr e)))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem right_components_eq (e f : Fin (rightTriangle R).nArc) :
    componentOf (J D R hleft hright).continuation (E D R hleft hright e) =
      componentOf (J D R hleft hright).continuation (E D R hleft hright f) := by
  let C := componentOf (J D R hleft hright).continuation
  have hnext (x : Fin (rightTriangle R).nArc) :
      C (E D R hleft hright x) =
        C (E D R hleft hright ((rightTriangle R).continuation x)) := by
    rw [← right_next]
    exact (componentOf_apply _ _).symm
  let e0 : Fin (rightTriangle R).nArc := ⟨0, by change 0 < 3; omega⟩
  let e1 : Fin (rightTriangle R).nArc := ⟨1, by change 1 < 3; omega⟩
  let e2 : Fin (rightTriangle R).nArc := ⟨2, by change 2 < 3; omega⟩
  have h01 : C (E D R hleft hright e0) = C (E D R hleft hright e1) := by
    simpa [e0, e1, rightTriangle, triangleUnknot] using hnext e0
  have h12 : C (E D R hleft hright e1) = C (E D R hleft hright e2) := by
    simpa [e1, e2, rightTriangle, triangleUnknot] using hnext e1
  fin_cases e <;> fin_cases f <;>
    first
    | rfl
    | exact h01
    | exact h01.symm
    | exact h12
    | exact h12.symm
    | exact h01.trans h12
    | exact h12.symm.trans h01.symm

theorem right_component_unique (hD : 0 < D.nArc)
    (C : diagramComponent (J D R hleft hright))
    (hC : C ∈ ((joinedPartition D R hleft hright hD).block 1).components) :
    C = componentOf (J D R hleft hright).continuation
      (E D R hleft hright (⟨0, by change 0 < 3; omega⟩ :
        Fin (rightTriangle R).nArc)) := by
  induction C using Quotient.inductionOn with
  | h e =>
      have hs : joinedSideOfArc D R hleft hright e = 1 := hC
      rcases he : (A D R hleft hright).symm e with a | a
      · have hz : joinedSideOfArc D R hleft hright e = 0 := by
          simp [joinedSideOfArc, he, codeSide]
        exact False.elim ((Fin.zero_ne_one : (0 : Fin 2) ≠ 1) (hz.symm.trans hs))
      · have heq : e = E D R hleft hright a := by
          change e = (A D R hleft hright) (.inr a)
          calc
            e = (A D R hleft hright) ((A D R hleft hright).symm e) :=
              ((A D R hleft hright).apply_symm_apply e).symm
            _ = _ := congrArg (A D R hleft hright) he
        rw [heq]
        exact right_components_eq D R hleft hright a _

theorem joinedPartition_right_component_count (hD : 0 < D.nArc) :
    diagramComponentCount (restrictSublink (J D R hleft hright)
      ((joinedPartition D R hleft hright hD).block 1)) = 1 := by
  let B := (joinedPartition D R hleft hright hD).block 1
  rw [sublink_component_count]
  letI : Subsingleton (SublinkSelectedComponent (J D R hleft hright) B) :=
    ⟨by
      intro C F
      apply Subtype.ext
      exact (right_component_unique D R hleft hright hD C.val C.property).trans
        (right_component_unique D R hleft hright hD F.val F.property).symm⟩
  letI : Nonempty (SublinkSelectedComponent (J D R hleft hright) B) :=
    inferInstance
  letI : Unique (SublinkSelectedComponent (J D R hleft hright) B) :=
    Classical.choice (nonempty_unique _)
  exact Fintype.card_unique

end DirectGLSSW.HOMFLY.SplitCircleConstructor

