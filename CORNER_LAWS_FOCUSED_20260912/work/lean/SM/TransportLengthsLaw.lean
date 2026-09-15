import SM.TransportLengths

/-! Source lem:transport-lengths (reference/SM/sm-5-transport.tex:74, frame SM15): positive
closing lengths along a direction path. Main declaration: `SM.transport_lengths_law`. Notation:
the directions are `u i : ℝ → Plane`, continuous on the compact interval `Set.Icc a b` and of
Euclidean length `1` there; "lying in no closed semicircle at any parameter" is: no unit vector
`v` has nonnegative inner product with every `u i t`; the lengths are `l i : ℝ → ℝ`, continuous
and strictly positive on the interval, with `∑ i, l i t • u i t = 0`; "at either endpoint any
prescribed positive closing lengths `m` can be joined to the selected lengths while keeping the
directions fixed" is: every point of the straight segment from `m` to `l a` (resp. `l b`) is a
positive closing length vector. Proof: SM.TransportLengths (prover subagent, ported verbatim). -/

namespace SM

open Set

/-- lem:transport-lengths as printed on SM15, for any finite index set of directions. -/
theorem transport_lengths_law {ι : Type*} [Fintype ι] {a b : ℝ} (hab : a ≤ b) (u : ι → ℝ → Plane)
    (hu : ∀ i, ContinuousOn (u i) (Icc a b))
    (hunit : ∀ i, ∀ t ∈ Icc a b, euclideanLength (u i t) = 1)
    (hsemi : ∀ t ∈ Icc a b,
      ¬ ∃ v : Plane, euclideanLength v = 1 ∧ ∀ i, 0 ≤ planeDot v (u i t)) :
    ∃ l : ι → ℝ → ℝ,
      (∀ i, ContinuousOn (l i) (Icc a b)) ∧
      (∀ i, ∀ t ∈ Icc a b, 0 < l i t) ∧
      (∀ t ∈ Icc a b, ∑ i, l i t • u i t = 0) ∧
      (∀ m : ι → ℝ, (∀ i, 0 < m i) → ∑ i, m i • u i a = 0 →
        ∀ s ∈ Icc (0 : ℝ) 1,
          (∀ i, 0 < (1 - s) * m i + s * l i a) ∧
          ∑ i, ((1 - s) * m i + s * l i a) • u i a = 0) ∧
      (∀ m : ι → ℝ, (∀ i, 0 < m i) → ∑ i, m i • u i b = 0 →
        ∀ s ∈ Icc (0 : ℝ) 1,
          (∀ i, 0 < (1 - s) * m i + s * l i b) ∧
          ∑ i, ((1 - s) * m i + s * l i b) • u i b = 0) :=
  transport_lengths hab u hu hunit hsemi

end SM
