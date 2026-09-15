import SM.NearFar
import SM.UnaryComposition
import SM.TriangularInverse

namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem nearFarWeight_one (D H : TripleArray n R) (hparts : π.parts = 1) :
    π.nearFarWeight D H = 1 := by
  letI : IsEmpty (Fin (π.parts - 1)) := ⟨fun k => by have := k.isLt; omega⟩
  simp [nearFarWeight]

end IntervalComposition

/-- Separate the unique unary composition from the complete source sum, with
the same cuts and the same coefficients on every nonunary term. -/
theorem nearFarTransform_eq_triangular (D H : TripleArray n R) :
    nearFarTransform D H = triangularTransform (fun _ π => π.nearFarWeight D H) := by
  classical
  funext X I
  unfold nearFarTransform triangularTransform
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (IntervalComposition.single I)]
  rw [(IntervalComposition.single I).nearFarWeight_one D H rfl,
    IntervalComposition.single_product X I, one_mul]
  congr 1
  exact Fintype.sum_equiv (IntervalComposition.nonSingleEquiv I) _ _ (fun _ => rfl)

def nearFarInverse (D H : TripleArray n R) : IntervalArray n R → IntervalArray n R :=
  triangularInverse (fun _ π => π.nearFarWeight D H)

theorem nearFarTransform_inverse (D H : TripleArray n R) (Y : IntervalArray n R) :
    nearFarTransform D H (nearFarInverse D H Y) = Y := by
  rw [nearFarTransform_eq_triangular]
  exact triangularTransform_inverse _ Y

theorem nearFarInverse_transform (D H : TripleArray n R) (X : IntervalArray n R) :
    nearFarInverse D H (nearFarTransform D H X) = X := by
  rw [nearFarTransform_eq_triangular]
  exact triangularInverse_transform _ X

theorem nearFar_solution_unique (D H : TripleArray n R) (X Y : IntervalArray n R)
    (hX : nearFarTransform D H X = Y) : X = nearFarInverse D H Y := by
  rw [nearFarTransform_eq_triangular] at hX
  exact triangular_solution_unique _ X Y hX

end

end SM
