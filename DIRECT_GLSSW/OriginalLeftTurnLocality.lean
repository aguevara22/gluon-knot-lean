import DirectGLSSW.PolygonGeometry
import DirectGLSSW.OrderedEventSuccessor
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

namespace DirectGLSSW.OriginalLeftTurnLocality

open DirectGLSSW
open scoped Topology

private noncomputable def turnDet {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) : ℝ :=
  planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
    (cyclicTangent q i)

private theorem turnDet_continuous {n : ℕ} (i : Fin n) :
    Continuous (fun q : Fin n → PlanarPoint ℝ => turnDet q i) := by
  have hleft : Continuous
      (fun q : Fin n → PlanarPoint ℝ => cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i)) := by
    simp only [cyclicTangent]
    exact (continuous_apply _).sub (continuous_apply _)
  have hright : Continuous
      (fun q : Fin n → PlanarPoint ℝ => cyclicTangent q i) := by
    simp only [cyclicTangent]
    exact (continuous_apply _).sub (continuous_apply _)
  dsimp [turnDet, planarDet]
  exact (hleft.fst.mul hright.snd).sub (hleft.snd.mul hright.fst)

private theorem turnDet_ne_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (i : Fin n) : turnDet q i ≠ 0 := by
  let e := (cyclicSuccessorPerm n)⁻¹ i
  have he : cyclicSuccessor e = i := by
    dsimp [e]
    have h := Equiv.apply_symm_apply (cyclicSuccessorPerm n) i
    simpa only [cyclicSuccessorPerm_apply] using h
  have hturn := cyclic_turn_det_ne_zero hq.size_ge_three q hq.g1 e
  rw [he] at hturn
  exact hturn

private theorem eventually_turnDet_positive_iff {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (i : Fin n) :
    ∀ᶠ r : Fin n → PlanarPoint ℝ in 𝓝 q,
      (0 < turnDet r i ↔ 0 < turnDet q i) := by
  have hcont := turnDet_continuous i
  have hne := turnDet_ne_zero q hq i
  by_cases hpos : 0 < turnDet q i
  · have hopen : IsOpen {r : Fin n → PlanarPoint ℝ | 0 < turnDet r i} :=
      isOpen_Ioi.preimage hcont
    filter_upwards [hopen.mem_nhds hpos] with r hr
    exact ⟨fun _ => hpos, fun _ => hr⟩
  · have hneg : turnDet q i < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hne
    have hopen : IsOpen {r : Fin n → PlanarPoint ℝ | turnDet r i < 0} :=
      isOpen_Iio.preimage hcont
    filter_upwards [hopen.mem_nhds hneg] with r hr
    exact Iff.intro
      (fun h => False.elim ((not_lt_of_ge (le_of_lt hr)) h))
      (fun h => False.elim (hpos h))

/-- The number of positive consecutive-tangent determinants is locally constant
at every actual G1/G2 polygon. -/
theorem eventually_literal_leftTurnCount_eq {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' : Fin n → PlanarPoint ℝ in 𝓝 q,
      (Finset.univ.filter (fun i : Fin n =>
        0 < planarDet (cyclicTangent q' ((cyclicSuccessorPerm n)⁻¹ i))
          (cyclicTangent q' i))).card =
      (Finset.univ.filter (fun i : Fin n =>
        0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
          (cyclicTangent q i))).card := by
  classical
  have hpoint (i : Fin n) : ∀ᶠ r : Fin n → PlanarPoint ℝ in 𝓝 q,
      (0 < turnDet r i ↔ 0 < turnDet q i) :=
    eventually_turnDet_positive_iff q hq i
  have hall (s : Finset (Fin n)) : ∀ᶠ r : Fin n → PlanarPoint ℝ in 𝓝 q,
      ∀ i ∈ s, (0 < turnDet r i ↔ 0 < turnDet q i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      filter_upwards [ih, hpoint a] with r hrs hra
      intro i hi
      rcases Finset.mem_insert.mp hi with h | h
      · subst i
        exact hra
      · exact hrs i h
  filter_upwards [hall Finset.univ] with r hr
  have hfilter :
      Finset.univ.filter (fun i : Fin n => 0 < turnDet r i) =
      Finset.univ.filter (fun i : Fin n => 0 < turnDet q i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hr i (Finset.mem_univ i)
  simpa only [turnDet] using congrArg Finset.card hfilter

/-- Exactly the `ell` expression in the frozen final theorem. -/
noncomputable def leftTurnCount {n : ℕ} (q : Fin n → PlanarPoint ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin n =>
    0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
      (cyclicTangent q i))).card

/-- The literal final-theorem left-turn count is locally constant. -/
theorem eventually_leftTurnCount_eq {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' : Fin n → PlanarPoint ℝ in 𝓝 q,
      leftTurnCount q' = leftTurnCount q := by
  exact eventually_literal_leftTurnCount_eq q hq




end DirectGLSSW.OriginalLeftTurnLocality
