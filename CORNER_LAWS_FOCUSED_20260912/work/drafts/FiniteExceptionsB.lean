import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Data.Finset.Max

/-! A function on a closed real interval that is locally constant away from a finite set of
exceptional points, and whose one-sided values agree at every interior exceptional point, takes
the same value at both endpoints. Main declaration: `SM.constant_of_finite_exceptions` (for
`f : ℝ → ℤ`), derived from the version `SM.constant_of_finite_exceptions_general` for an
arbitrary codomain. Helper names carry the prefix `feB_`. -/

namespace SM

open Set Filter Topology

/-- A function that is locally constant (in the metric sense) on `S` is continuous on `S`,
for any topology on the codomain. -/
theorem feB_continuousOn_of_locally_const {α : Type*} [TopologicalSpace α] {f : ℝ → α}
    {S : Set ℝ} (hloc : ∀ t ∈ S, ∃ ε > 0, ∀ u ∈ S, |u - t| < ε → f u = f t) :
    ContinuousOn f S := by
  intro t ht
  obtain ⟨ε, hε, h⟩ := hloc t ht
  have hev : ∀ᶠ u in 𝓝[S] t, f t = f u := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    exact ⟨ε, hε, fun u hu huS => (h u huS (by rwa [Real.dist_eq] at hu)).symm⟩
  exact tendsto_const_nhds.congr' hev

/-- Base case: a function locally constant on `[a, b]` takes the same value at `a` and `b`. -/
theorem feB_constant_of_locally_const {α : Type*} {f : ℝ → α} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ t ∈ Icc a b, ∃ ε > 0, ∀ u ∈ Icc a b, |u - t| < ε → f u = f t) :
    f a = f b := by
  let _ : TopologicalSpace α := ⊥
  have : DiscreteTopology α := discreteTopology_bot α
  exact isPreconnected_Icc.constant (feB_continuousOn_of_locally_const hloc)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)

/-- A point outside a finite set of reals is at positive distance from it. -/
theorem feB_exists_pos_le_dist (E : Finset ℝ) {t : ℝ} (ht : t ∉ E) :
    ∃ r > 0, ∀ e ∈ E, r ≤ |e - t| := by
  rcases E.eq_empty_or_nonempty with hE | hE
  · exact ⟨1, one_pos, fun e he => by simp [hE] at he⟩
  · obtain ⟨e₀, he₀, hmin⟩ := E.exists_min_image (fun e => |e - t|) hE
    exact ⟨|e₀ - t|, abs_pos.mpr (sub_ne_zero.mpr fun h => ht (h ▸ he₀)), hmin⟩

/-- General form of `constant_of_finite_exceptions`, for an arbitrary codomain `α`. -/
theorem constant_of_finite_exceptions_general {α : Type*} {f : ℝ → α} {a b : ℝ} (hab : a ≤ b)
    (E : Finset ℝ) (ha : a ∉ E) (hb : b ∉ E)
    (hloc : ∀ t ∈ Set.Icc a b, t ∉ E → ∃ ε > 0, ∀ u ∈ Set.Icc a b, |u - t| < ε → f u = f t)
    (hjump : ∀ t ∈ E, t ∈ Set.Ioo a b →
      ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f (t - s) = f (t + s)) :
    f a = f b := by
  classical
  induction E using Finset.induction_on generalizing a b with
  | empty =>
    exact feB_constant_of_locally_const hab fun t ht => hloc t ht (Finset.notMem_empty t)
  | insert t E' htE' ih =>
    have hat : a ≠ t := fun h => ha (h ▸ Finset.mem_insert_self t E')
    have hbt : b ≠ t := fun h => hb (h ▸ Finset.mem_insert_self t E')
    have ha' : a ∉ E' := fun h => ha (Finset.mem_insert_of_mem h)
    have hb' : b ∉ E' := fun h => hb (Finset.mem_insert_of_mem h)
    by_cases htab : t ∈ Ioo a b
    · -- interior exceptional point: split `[a, b]` at `t` into `[a, t - s]` and `[t + s, b]`
      obtain ⟨δ, hδ, hjt⟩ := hjump t (Finset.mem_insert_self t E') htab
      obtain ⟨r, hr, hrE⟩ := feB_exists_pos_le_dist E' htE'
      obtain ⟨s, hspos, hsδ, hsa, hsb, hsr⟩ :
          ∃ s : ℝ, 0 < s ∧ s < δ ∧ s < t - a ∧ s < b - t ∧ s < r := by
        have hMpos : 0 < min (min δ (t - a)) (min (b - t) r) :=
          lt_min (lt_min hδ (sub_pos.mpr htab.1)) (lt_min (sub_pos.mpr htab.2) hr)
        have hsM := half_lt_self hMpos
        exact ⟨_, half_pos hMpos,
          hsM.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
          hsM.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
          hsM.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
          hsM.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
      have hsE : ∀ e ∈ E', s < |e - t| := fun e he => hsr.trans_le (hrE e he)
      have h1 : a ≤ t - s := by linarith
      have h2 : t + s ≤ b := by linarith
      have hts_notin : t - s ∉ E' := fun h => by
        have := hsE _ h
        rw [show t - s - t = -s by ring, abs_neg, abs_of_pos hspos] at this
        exact lt_irrefl _ this
      have hts_notin' : t + s ∉ E' := fun h => by
        have := hsE _ h
        rw [show t + s - t = s by ring, abs_of_pos hspos] at this
        exact lt_irrefl _ this
      have hL : f a = f (t - s) := by
        refine ih h1 ha' hts_notin ?_ ?_
        · intro u hu huE'
          have hut : u ≠ t := by
            intro h; rw [h] at hu; linarith [hu.2]
          have huE : u ∉ insert t E' := by
            rw [Finset.mem_insert]; rintro (h | h)
            · exact hut h
            · exact huE' h
          have hu' : u ∈ Icc a b := ⟨hu.1, by linarith [hu.2]⟩
          obtain ⟨ε, hε, hεu⟩ := hloc u hu' huE
          exact ⟨ε, hε, fun v hv hvu => hεu v ⟨hv.1, by linarith [hv.2]⟩ hvu⟩
        · intro e he heab
          exact hjump e (Finset.mem_insert_of_mem he) ⟨heab.1, by linarith [heab.2]⟩
      have hR : f (t + s) = f b := by
        refine ih h2 hts_notin' hb' ?_ ?_
        · intro u hu huE'
          have hut : u ≠ t := by
            intro h; rw [h] at hu; linarith [hu.1]
          have huE : u ∉ insert t E' := by
            rw [Finset.mem_insert]; rintro (h | h)
            · exact hut h
            · exact huE' h
          have hu' : u ∈ Icc a b := ⟨by linarith [hu.1], hu.2⟩
          obtain ⟨ε, hε, hεu⟩ := hloc u hu' huE
          exact ⟨ε, hε, fun v hv hvu => hεu v ⟨by linarith [hv.1], hv.2⟩ hvu⟩
        · intro e he heab
          exact hjump e (Finset.mem_insert_of_mem he) ⟨by linarith [heab.1], heab.2⟩
      rw [hL, hjt s hspos hsδ, hR]
    · -- `t` is not in `[a, b]` at all, so it is not an exception that matters
      have htI : t ∉ Icc a b := fun h =>
        htab ⟨lt_of_le_of_ne h.1 hat, lt_of_le_of_ne h.2 hbt.symm⟩
      refine ih hab ha' hb' ?_ ?_
      · intro u hu huE'
        have huE : u ∉ insert t E' := by
          rw [Finset.mem_insert]; rintro (h | h)
          · exact htI (h ▸ hu)
          · exact huE' h
        exact hloc u hu huE
      · intro e he heab
        exact hjump e (Finset.mem_insert_of_mem he) heab

/-- A function `f : ℝ → ℤ` that is locally constant on `[a, b]` away from a finite exceptional
set `E` (not containing `a` or `b`), and whose values just to the left and just to the right of
each exceptional point strictly inside `(a, b)` agree, satisfies `f a = f b`. -/
theorem constant_of_finite_exceptions {f : ℝ → ℤ} {a b : ℝ} (hab : a ≤ b) (E : Finset ℝ)
    (ha : a ∉ E) (hb : b ∉ E)
    (hloc : ∀ t ∈ Set.Icc a b, t ∉ E → ∃ ε > 0, ∀ u ∈ Set.Icc a b, |u - t| < ε → f u = f t)
    (hjump : ∀ t ∈ E, t ∈ Set.Ioo a b → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f (t - s) = f (t + s)) :
    f a = f b :=
  constant_of_finite_exceptions_general hab E ha hb hloc hjump

end SM

#print axioms SM.constant_of_finite_exceptions
