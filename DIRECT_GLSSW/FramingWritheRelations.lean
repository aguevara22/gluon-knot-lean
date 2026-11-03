import ActualTerminalFramedValue
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open LowestRowContract PrincipalTurning
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem writheSign_switch_self (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    writheSign (switchCrossing D c) c = -writheSign D c := by
  unfold writheSign
  rw [crossingSign_switchCrossing]
  cases crossingSign D c <;> rfl

theorem writheSign_switch_other (D : PLLinkDiagram) (c d : Fin D.nCrossing)
    (hd : d ≠ c) : writheSign (switchCrossing D c) d = writheSign D d := by
  unfold writheSign
  rw [crossingSign_switchCrossing_of_ne D c d hd]

theorem diagramWrithe_switch (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    diagramWrithe (switchCrossing D c) = diagramWrithe D - 2 * writheSign D c := by
  unfold diagramWrithe
  have hsum : (∑ d : Fin D.nCrossing, writheSign (switchCrossing D c) d) =
      ∑ d : Fin D.nCrossing, (writheSign D d - if d = c then 2 * writheSign D c else 0) := by
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d = c
    · subst d
      rw [writheSign_switch_self,if_pos rfl]
      ring
    · rw [writheSign_switch_other D c d hd,if_neg hd,sub_zero]
  calc
    _ = ∑ d : Fin D.nCrossing,
        (writheSign D d - if d = c then 2 * writheSign D c else 0) := hsum
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

theorem diagramWrithe_switch_positive (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hc : crossingSign D c = Sign.pos) :
    diagramWrithe (switchCrossing D c) = diagramWrithe D - 2 := by
  rw [diagramWrithe_switch]
  simp [writheSign,hc]

theorem diagramWrithe_smooth_add (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    diagramWrithe (smoothCrossing D c) + writheSign D c = diagramWrithe D := by
  have he : (∑ d : SmoothCrossingCode D c, writheSign D d.val) =
      ∑ e : Fin (D.nCrossing - 1), writheSign (smoothCrossing D c) e := by
    apply Fintype.sum_equiv (smoothCrossingEquiv D c)
    intro d
    unfold writheSign
    rw [crossingSign_smoothRetained D c d.val d.property]
  have hs : (∑ d ∈ (Finset.univ.erase c), writheSign D d) =
      ∑ d : SmoothCrossingCode D c, writheSign D d.val := by
    apply Finset.sum_subtype
    intro d
    simp
  have hsum := Finset.sum_erase_add Finset.univ (writheSign D) (Finset.mem_univ c)
  calc
    diagramWrithe (smoothCrossing D c) + writheSign D c =
        (∑ d : SmoothCrossingCode D c, writheSign D d.val) + writheSign D c :=
      congrArg (fun x : ℤ => x + writheSign D c) he.symm
    _ = (∑ d ∈ (Finset.univ.erase c), writheSign D d) + writheSign D c :=
      congrArg (fun x : ℤ => x + writheSign D c) hs.symm
    _ = diagramWrithe D := hsum

theorem diagramWrithe_smooth_positive (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hc : crossingSign D c = Sign.pos) :
    diagramWrithe (smoothCrossing D c) = diagramWrithe D - 1 := by
  have h := diagramWrithe_smooth_add D c
  simp only [writheSign,hc] at h
  omega







end DirectGLSSW.HOMFLY
