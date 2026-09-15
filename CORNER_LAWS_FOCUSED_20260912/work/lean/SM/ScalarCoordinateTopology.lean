import SM.CoordinatePolynomials
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Homeomorph.Defs

/-! The scalar coordinate presentation is a homeomorphism of the actual labelled
tuple space with its product topology. This does not identify the product max
metric with the source's Euclidean metric; metric bounds need their own proof. -/

namespace SM

noncomputable section

variable {n : ℕ}

theorem continuous_scalarCoordinates : Continuous (scalarCoordinates (n := n)) := by
  apply continuous_pi
  intro c
  by_cases h : c.2 = 0
  · simpa only [scalarCoordinates, h, if_true] using (continuous_apply c.1).fst
  · simpa only [scalarCoordinates, h, if_false] using (continuous_apply c.1).snd

theorem continuous_tupleOfScalarCoordinates :
    Continuous (tupleOfScalarCoordinates (n := n)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (i, 0)).prodMk (continuous_apply (i, 1))

def scalarCoordinateHomeomorph (n : ℕ) : LabelledTuple n ≃ₜ (ScalarCoordinate n → ℝ) where
  toEquiv := scalarCoordinateEquiv n
  continuous_toFun := continuous_scalarCoordinates
  continuous_invFun := continuous_tupleOfScalarCoordinates

end

end SM
