import SM.FiniteChiStability
import SM.GermNeighborhood

/-! Every actual nonzero central chirotope persists on one common interval.
This works for all named wall types, including a contact centre. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

def ChirotopesOutsideZerosAgree (P Q : LabelledTuple n) : Prop :=
  ∀ i j k : ZMod n, i ≠ j → j ≠ k → i ≠ k →
    ({i, j, k} : Finset _) ∉ pointZeroTriples P →
    chi Q i j k = chi P i j k ∧ chi Q i j k ≠ 0

theorem outsideZeros_chi_persists (P : LabelledTuple n) :
    ∀ᶠ Q in 𝓝 P, ChirotopesOutsideZerosAgree P Q := by
  filter_upwards [finite_nonzero_chi_persists (P := P)] with Q hQ
  intro i j k hij hjk hik hnot
  have hn : chi P i j k ≠ 0 := by
    intro hz
    exact hnot ((mem_pointZeroTriples P {i, j, k}).mpr
      ((pointZeroTriple_iff hij hjk hik).mpr hz))
  have he := hQ i j k hn
  exact ⟨he, he ▸ hn⟩

theorem germ_outsideZeros_chi_persists (g : WallGerm n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
      ChirotopesOutsideZerosAgree g.center (g.curve t) := by
  exact (g.eventually_center_iff_radius _).mp
    (g.continuous_curve.continuousAt.eventually (outsideZeros_chi_persists g.center))

end SM
