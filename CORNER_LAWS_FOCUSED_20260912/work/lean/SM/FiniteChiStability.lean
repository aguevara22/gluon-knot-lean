import SM.ChamberPaths
import SM.SinglePointTriple

/-! Simultaneous stability of every nonzero chirotope at an arbitrary tuple.
This does not assume G1 and retains all unordered source triple exclusions. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem chi_locally_constant_of_ne_zero {i j k : ZMod n} (hz : chi P i j k ≠ 0) :
    ∀ᶠ Q in 𝓝 P, chi Q i j k = chi P i j k := by
  have hc : ContinuousAt (fun Q : LabelledTuple n => chi Q i j k) P :=
    (continuousAt_sign_of_ne_zero (sign_ne_zero.mp hz)).comp
      (f := fun Q : LabelledTuple n => det (Q j - Q i) (Q k - Q i))
      (continuous_area i j k).continuousAt
  exact hc.eventually (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton (chi P i j k)))

theorem finite_nonzero_chi_persists :
    ∀ᶠ Q in 𝓝 P, ∀ i j k : ZMod n, chi P i j k ≠ 0 → chi Q i j k = chi P i j k := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  apply eventually_all.mpr
  intro k
  by_cases hz : chi P i j k = 0
  · exact Eventually.of_forall (fun _ hne => (hne hz).elim)
  · exact (chi_locally_constant_of_ne_zero hz).mono (fun _ h _ => h)

theorem singlePointTriple_chi_persists {s : Finset (ZMod n)}
    (h : pointZeroTriples P = {s}) :
    ∀ᶠ Q in 𝓝 P, ∀ i j k : ZMod n, i ≠ j → j ≠ k → i ≠ k →
      ({i, j, k} : Finset _) ≠ s →
        chi Q i j k = chi P i j k ∧ chi Q i j k ≠ 0 := by
  filter_upwards [finite_nonzero_chi_persists (P := P)] with Q hQ
  intro i j k hij hjk hik hne
  have hz := chi_nonzero_outside_singleton h hij hjk hik hne
  have he := hQ i j k hz
  exact ⟨he, he ▸ hz⟩

end SM
