import SM.GenericDensity
import SM.RotationContinuity

/-! The full regular locus is open, including zero principal turns from
positive collinearity. Actual rotation is locally constant there by continuity
and its proved integer values. Full Generic density then preserves rotation. -/

namespace SM

open Filter Set Topology

variable {n : ℕ} [NeZero n]

theorem continuous_cornerRotor_edges (i : ZMod n) : Continuous
    (fun P : LabelledTuple n => cornerRotor (edge P (i - 1)) (edge P i)) :=
  ((continuous_planeComplex.comp (continuous_edge (i - 1))).star).mul
    (continuous_planeComplex.comp (continuous_edge i))

theorem regular_persists {P : LabelledTuple n} (hP : Regular P) :
    ∀ᶠ Q in 𝓝 P, Regular Q := by
  apply eventually_all.mpr
  intro i
  have hu : ∀ᶠ Q in 𝓝 P, edge Q (i - 1) ≠ 0 :=
    (continuous_edge (i - 1)).continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds (hP i).1)
  have hv : ∀ᶠ Q in 𝓝 P, edge Q i ≠ 0 :=
    (continuous_edge i).continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds (hP i).2.1)
  have hs : ∀ᶠ Q in 𝓝 P, cornerRotor (edge Q (i - 1)) (edge Q i) ∈ Complex.slitPlane :=
    (continuous_cornerRotor_edges i).continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds (regularPair_slitPlane (hP i)))
  filter_upwards [hu, hv, hs] with Q hQu hQv hQs
  exact (regularPair_iff_slitPlane _ _).mpr ⟨hQu, hQv, hQs⟩

theorem isOpen_Regular : IsOpen {P : LabelledTuple n | Regular P} :=
  isOpen_iff_mem_nhds.mpr fun _ hP => regular_persists hP

theorem continuousAt_rotationNumber {P : LabelledTuple n} (hP : Regular P) :
    ContinuousAt (rotationNumber (n := n)) P := by
  change ContinuousAt (fun Q : LabelledTuple n =>
    (∑ i : ZMod n, principalTurn Q i) / (2 * Real.pi)) P
  apply ContinuousAt.div_const
  exact tendsto_finsetSum _ (fun i _ => continuousAt_principalAngle
    (continuous_edge (i - 1)).continuousAt (continuous_edge i).continuousAt (hP i))

theorem rotationNumber_locally_constant {P : LabelledTuple n} (hP : Regular P) :
    ∀ᶠ Q in 𝓝 P, rotationNumber Q = rotationNumber P := by
  have hd : ∀ᶠ Q in 𝓝 P,
      -1 < rotationNumber Q - rotationNumber P ∧ rotationNumber Q - rotationNumber P < 1 :=
    ((continuousAt_rotationNumber hP).sub continuousAt_const).eventually
      (isOpen_Ioo.mem_nhds (by simp : rotationNumber P - rotationNumber P ∈ Ioo (-1 : ℝ) 1))
  obtain ⟨k, hk⟩ := rotationNumber_integer hP
  filter_upwards [regular_persists hP, hd] with Q hQ hdiff
  obtain ⟨l, hl⟩ := rotationNumber_integer hQ
  rw [hl, hk] at hdiff ⊢
  have hlo : (-1 : ℤ) < l - k := by exact_mod_cast hdiff.1
  have hhi : l - k < (1 : ℤ) := by exact_mod_cast hdiff.2
  have he : l = k := by omega
  rw [he]

/-- Every actual regular n-tuple can be replaced by an actual full-Generic
n-tuple with the same normalized rotation. The neighbourhood is constructed
from openness and proved local constancy; the generic witness is not supplied. -/
theorem exists_generic_same_rotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Regular P) :
    ∃ Q : LabelledTuple n, Generic Q ∧ rotationNumber Q = rotationNumber P := by
  have hs : {Q : LabelledTuple n | Regular Q ∧ rotationNumber Q = rotationNumber P} ∈ 𝓝 P :=
    (regular_persists hP).and (rotationNumber_locally_constant hP)
  obtain ⟨U, hsub, hU, hPU⟩ := mem_nhds_iff.mp hs
  obtain ⟨Q, hQU, hQ⟩ := generic_in_nonempty_open hn U hU ⟨P, hPU⟩
  exact ⟨Q, hQ, (hsub hQU).2⟩

end SM
