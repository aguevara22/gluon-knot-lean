import SM.LineConcurrence

/-! Explicit nonzero witnesses and simultaneous avoidance of every triple of
pairwise remote supporting lines. Witness coordinates need not be generic. -/

namespace SM

open Set

variable {n : ℕ}

def concurrenceWitness (i j k : ZMod n) : LabelledTuple n := fun a =>
  if a = i + 1 then (1, 0) else if a = k + 1 then (1, 1)
  else if a = j + 1 ∨ a = k then (0, 1) else (0, 0)

theorem concurrenceWitness_vertices [Nontrivial (ZMod n)] (i j k : ZMod n)
    (hij : remote i j) (hjk : remote j k) (hik : remote i k) :
    concurrenceWitness i j k i = (0, 0) ∧
    concurrenceWitness i j k (i + 1) = (1, 0) ∧
    concurrenceWitness i j k j = (0, 0) ∧
    concurrenceWitness i j k (j + 1) = (0, 1) ∧
    concurrenceWitness i j k k = (0, 1) ∧
    concurrenceWitness i j k (k + 1) = (1, 1) := by
  obtain ⟨hji, hjip, hjpi, hjpip⟩ := remote_endpoints i j hij
  obtain ⟨hki, hkip, hkpi, hkpip⟩ := remote_endpoints i k hik
  obtain ⟨hkj, hkjp, hkpj, hkpjp⟩ := remote_endpoints j k hjk
  have hselfi : i + 1 ≠ i := next_ne_self i
  have hselfj : j + 1 ≠ j := next_ne_self j
  have hselfk : k + 1 ≠ k := next_ne_self k
  simp_all [concurrenceWitness, eq_comm]

theorem concurrenceWitness_value [Nontrivial (ZMod n)] (i j k : ZMod n)
    (hij : remote i j) (hjk : remote j k) (hik : remote i k) :
    concurrenceDet (concurrenceWitness i j k) i j k = -1 := by
  obtain ⟨hi, hip, hj, hjp, hk, hkp⟩ := concurrenceWitness_vertices i j k hij hjk hik
  norm_num [concurrenceDet_formula, edgeLineA, edgeLineB, edgeLineC,
    hi, hip, hj, hjp, hk, hkp]

theorem concurrence_nonzero_witness [Nontrivial (ZMod n)] (i j k : ZMod n)
    (hij : remote i j) (hjk : remote j k) (hik : remote i k) :
    ∃ P : LabelledTuple n, concurrenceDet P i j k ≠ 0 := by
  refine ⟨concurrenceWitness i j k, ?_⟩
  rw [concurrenceWitness_value i j k hij hjk hik]
  norm_num

abbrev RemoteEdgeTriple (n : ℕ) :=
  {v : ZMod n × ZMod n × ZMod n //
    remote v.1 v.2.1 ∧ remote v.2.1 v.2.2 ∧ remote v.1 v.2.2}

def RemoteNonconcurrent (P : LabelledTuple n) : Prop :=
  ∀ i j k, remote i j → remote j k → remote i k → concurrenceDet P i j k ≠ 0

theorem remoteNonconcurrent_iff_indexed (P : LabelledTuple n) :
    RemoteNonconcurrent P ↔ ∀ v : RemoteEdgeTriple n,
      concurrenceDet P v.val.1 v.val.2.1 v.val.2.2 ≠ 0 := by
  constructor
  · intro h v
    exact h v.val.1 v.val.2.1 v.val.2.2 v.property.1 v.property.2.1 v.property.2.2
  · intro h i j k hij hjk hik
    exact h ⟨(i, j, k), hij, hjk, hik⟩

theorem dense_remoteNonconcurrent [NeZero n] [Nontrivial (ZMod n)] :
    Dense {P : LabelledTuple n | RemoteNonconcurrent P} := by
  let f : RemoteEdgeTriple n → LabelledTuple n → ℝ := fun v P =>
    concurrenceDet P v.val.1 v.val.2.1 v.val.2.2
  have hd : Dense {P | ∀ v, f v P ≠ 0} := dense_finite_nonzero_family f
    (fun v => continuous_concurrenceDet v.val.1 v.val.2.1 v.val.2.2)
    (fun v => concurrence_polynomial_on_lines v.val.1 v.val.2.1 v.val.2.2)
    (fun v => concurrence_nonzero_witness v.val.1 v.val.2.1 v.val.2.2
      v.property.1 v.property.2.1 v.property.2.2)
  exact hd.mono (fun P hP => (remoteNonconcurrent_iff_indexed P).mpr hP)

theorem isOpen_remoteNonconcurrent [NeZero n] :
    IsOpen {P : LabelledTuple n | RemoteNonconcurrent P} := by
  let A : RemoteEdgeTriple n → Set (LabelledTuple n) := fun v =>
    {P | concurrenceDet P v.val.1 v.val.2.1 v.val.2.2 ≠ 0}
  have hs : IsOpen (⋂₀ Set.range A) := (Set.finite_range A).isOpen_sInter (by
    rintro _ ⟨v, rfl⟩
    exact isOpen_ne.preimage (continuous_concurrenceDet v.val.1 v.val.2.1 v.val.2.2))
  have he : (⋂₀ Set.range A) = {P : LabelledTuple n | RemoteNonconcurrent P} := by
    ext P
    constructor
    · intro h
      apply (remoteNonconcurrent_iff_indexed P).mpr
      intro v
      exact Set.mem_sInter.mp h (A v) (Set.mem_range_self v)
    · intro h
      apply Set.mem_sInter.mpr
      rintro _ ⟨v, rfl⟩
      exact (remoteNonconcurrent_iff_indexed P).mp h v
  rwa [he] at hs

end SM
