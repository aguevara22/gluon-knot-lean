import SM.TransportAngleInterval

/-! Source lem:transport-angle-interval (reference/SM/sm-5-transport.tex:132, frame SM15): lifting
a semicircle to one real interval. Main declaration: `SM.transport_angle_interval_law`. Notation:
the finite real sequence `θ_0, …, θ_N` is `θ : Fin (N + 1) → ℝ`; its unit directions are
`unitDir (θ i) = (cos (θ i), sin (θ i))`; "lie in a closed semicircle" is `InClosedSemicircle θ`
(some unit vector has nonnegative inner product with every direction), equivalently
`∃ α, ∀ i, 0 ≤ cos (θ i - α)`; "lie in one interval of length π" is `∃ c, ∀ i, c ≤ θ i ≤ c + π`.
Proof: SM.TransportAngleInterval (prover subagent, ported verbatim). -/

namespace SM

open Real

/-- lem:transport-angle-interval as printed on SM15, both directions. The step hypothesis
`|θ_{i+1} - θ_i| < π` is a hypothesis of the forward direction only; the converse holds for every
finite real sequence. -/
theorem transport_angle_interval_law {N : ℕ} (θ : Fin (N + 1) → ℝ) :
    (∀ i, unitDir (θ i) = (Real.cos (θ i), Real.sin (θ i))) ∧
    (InClosedSemicircle θ ↔ ∃ α : ℝ, ∀ i, 0 ≤ Real.cos (θ i - α)) ∧
    ((∀ i : Fin N, |θ i.succ - θ i.castSucc| < π) → InClosedSemicircle θ →
      ∃ c : ℝ, ∀ i, c ≤ θ i ∧ θ i ≤ c + π) ∧
    ((∃ c : ℝ, ∀ i, c ≤ θ i ∧ θ i ≤ c + π) → InClosedSemicircle θ) :=
  ⟨fun _ => rfl, inClosedSemicircle_iff θ,
    fun hstep => (transport_angle_interval_iff θ hstep).mp, transport_angle_interval_converse θ⟩

end SM
