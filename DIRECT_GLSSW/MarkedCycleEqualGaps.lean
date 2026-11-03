import MarkedCycleConjugacy
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.MarkedCycleGaps
open Equiv

/-- The literal index-preserving identification of equal-length gap coordinates. -/
def gapCoordinateEquiv {ι : Type*} {len left : ι → ℕ}
    (h : ∀ m, len m = left m) : (Σ m, Fin (len m)) ≃ (Σ m, Fin (left m)) :=
  Equiv.sigmaCongrRight (fun m => finCongr (h m))

theorem gapCoordinateEquiv_successor {ι : Type*} {len left : ι → ℕ}
    (h : ∀ m, len m = left m) (hp : ∀ m, 0 < len m) (hq : ∀ m, 0 < left m)
    (next : Perm ι) (x : Σ m, Fin (len m)) :
    gapCoordinateEquiv h (gapSuccessor len hp next x) =
      gapSuccessor left hq next (gapCoordinateEquiv h x) := by
  have he : len = left := funext h
  subst left
  rfl

theorem gapCoordinateEquiv_last {ι : Type*} {len left : ι → ℕ}
    (h : ∀ m, len m = left m) (hp : ∀ m, 0 < len m) (hq : ∀ m, 0 < left m)
    (m : ι) :
    gapCoordinateEquiv h ⟨m,⟨len m - 1, by have := hp m; omega⟩⟩ =
      ⟨m,⟨left m - 1, by have := hq m; omega⟩⟩ := by
  have he : len = left := funext h
  subst left
  rfl

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [Nonempty ι]
    (p : Perm α) (q : Perm β) (mark : ι → α) (mark' : ι → β)
    (hp : p.IsCycleOn Set.univ) (hq : q.IsCycleOn Set.univ)
    (hinj : Function.Injective mark) (hinj' : Function.Injective mark')
    (hlen : ∀ m, gapLength p mark m = gapLength q mark' m)

/-- Equal actual gaps identify all arcs by their derived coordinates. -/
def equalGapArcEquiv : α ≃ β :=
  (gapEquiv p mark hp hinj).symm.trans
    ((gapCoordinateEquiv hlen).trans (gapEquiv q mark' hq hinj'))

theorem equalGapArcEquiv_continuation
    (hnext : next p mark hinj = next q mark' hinj') (x : α) :
    equalGapArcEquiv p q mark mark' hp hq hinj hinj' hlen (p x) =
      q (equalGapArcEquiv p q mark mark' hp hq hinj hinj' hlen x) := by
  obtain ⟨y, rfl⟩ := (gapEquiv p mark hp hinj).surjective x
  rw [← gapEquiv_successor p mark hp hinj y]
  simp only [equalGapArcEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [gapCoordinateEquiv_successor hlen (gapLength_pos p mark) (gapLength_pos q mark')]
  rw [hnext, gapEquiv_successor]

theorem equalGapArcEquiv_mark
    (hnext : next p mark hinj = next q mark' hinj') (m : ι) :
    equalGapArcEquiv p q mark mark' hp hq hinj hinj' hlen (mark m) = mark' m := by
  let j := (next p mark hinj).symm m
  have hm : mark m = gapEquiv p mark hp hinj
      ⟨j,⟨gapLength p mark j - 1,by have := gapLength_pos p mark j; omega⟩⟩ := by
    rw [gapEquiv_last]
    exact congrArg mark ((next p mark hinj).apply_symm_apply m).symm
  rw [hm]
  simp only [equalGapArcEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [gapCoordinateEquiv_last hlen (gapLength_pos p mark) (gapLength_pos q mark'),
    gapEquiv_last, ← hnext]
  exact congrArg mark' ((next p mark hinj).apply_symm_apply m)

end DirectGLSSW.MarkedCycleGaps
