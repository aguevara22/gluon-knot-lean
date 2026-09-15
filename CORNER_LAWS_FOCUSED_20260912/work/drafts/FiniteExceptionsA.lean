import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

/-! A function `f : ℝ → ℤ` that is locally constant on `[a, b]` away from a finite set `E` of
exceptional points, and whose one-sided values agree at each exceptional point strictly inside
`[a, b]`, takes the same value at `a` and at `b`. Main declaration:
`SM.constant_of_finite_exceptions`; the version for an arbitrary codomain is
`SM.constant_of_finite_exceptions_gen`. Helper names carry the prefix `feA_`. -/

namespace SM

/-- Base case: a function locally constant on the closed interval `[a, b]` (in the metric
sense, relative to the interval) takes the same value at both endpoints. Direct `sSup`
argument on `{t ∈ [a, b] | f t = f a}`; no topology on the codomain is needed. -/
theorem feA_base {α : Type*} {f : ℝ → α} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ ε > 0, ∀ u ∈ Set.Icc a b, |u - t| < ε → f u = f t) :
    f a = f b := by
  set S : Set ℝ := {t | t ∈ Set.Icc a b ∧ f t = f a} with hS
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, rfl⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hSbdd : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
  set c := sSup S with hc
  have hac : a ≤ c := le_csSup hSbdd haS
  have hcb : c ≤ b := csSup_le hSne (fun t ht => ht.1.2)
  have hcI : c ∈ Set.Icc a b := ⟨hac, hcb⟩
  obtain ⟨ε, hε, hεf⟩ := hloc c hcI
  have hfc : f c = f a := by
    obtain ⟨t, htS, hlt⟩ := exists_lt_of_lt_csSup hSne (show c - ε < c by linarith)
    have htc : t ≤ c := le_csSup hSbdd htS
    have habs : |t - c| < ε := by
      rw [abs_sub_lt_iff]; constructor <;> linarith
    rw [← hεf t htS.1 habs]
    exact htS.2
  have hcb' : c = b := by
    by_contra hne
    have hlt : c < b := lt_of_le_of_ne hcb hne
    set u := min (c + ε / 2) b with hu
    have hcu : c < u := lt_min (by linarith) hlt
    have hub : u ≤ b := min_le_right _ _
    have huc : u ≤ c + ε / 2 := min_le_left _ _
    have huI : u ∈ Set.Icc a b := ⟨le_trans hac hcu.le, hub⟩
    have habs : |u - c| < ε := by
      rw [abs_sub_lt_iff]; constructor <;> linarith
    have huS : u ∈ S := ⟨huI, (hεf u huI habs).trans hfc⟩
    exact absurd (le_csSup hSbdd huS) (not_le.mpr hcu)
  rw [← hcb']
  exact hfc.symm

/-- Restricting the two hypotheses from `[a, b]` with exceptional set `insert t E` to a
subinterval `[a', b']` not containing `t`, with exceptional set `E`. -/
theorem feA_restrict {α : Type*} {f : ℝ → α} {a b a' b' : ℝ} (E : Finset ℝ) (t : ℝ)
    (haa' : a ≤ a') (hb'b : b' ≤ b) (ht : t ∉ Set.Icc a' b')
    (hloc : ∀ u ∈ Set.Icc a b, u ∉ insert t E →
      ∃ ε > 0, ∀ v ∈ Set.Icc a b, |v - u| < ε → f v = f u)
    (hjump : ∀ e ∈ insert t E, e ∈ Set.Ioo a b →
      ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f (e - s) = f (e + s)) :
    (∀ u ∈ Set.Icc a' b', u ∉ E →
      ∃ ε > 0, ∀ v ∈ Set.Icc a' b', |v - u| < ε → f v = f u) ∧
    (∀ e ∈ E, e ∈ Set.Ioo a' b' →
      ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f (e - s) = f (e + s)) := by
  have hsub : Set.Icc a' b' ⊆ Set.Icc a b := Set.Icc_subset_Icc haa' hb'b
  refine ⟨fun u hu huE => ?_, fun e he heI => ?_⟩
  · have huE' : u ∉ insert t E := by
      intro h
      rcases Finset.mem_insert.mp h with rfl | h
      · exact ht hu
      · exact huE h
    obtain ⟨ε, hε, hεf⟩ := hloc u (hsub hu) huE'
    exact ⟨ε, hε, fun v hv hvu => hεf v (hsub hv) hvu⟩
  · exact hjump e (Finset.mem_insert_of_mem he) (Set.Ioo_subset_Ioo haa' hb'b heI)

/-- Existence of a radius `s > 0` below `δ`, keeping `[t - s, t + s]` strictly inside `(a, b)`
and away from every point of the finite set `E` (which does not contain `t`). -/
theorem feA_exists_radius {a b t δ : ℝ} (E : Finset ℝ) (htE : t ∉ E) (hδ : 0 < δ)
    (ht : t ∈ Set.Ioo a b) :
    ∃ s : ℝ, 0 < s ∧ s < δ ∧ a < t - s ∧ t + s < b ∧ ∀ e ∈ E, s < |e - t| := by
  set D : Finset ℝ := insert δ (insert (t - a) (insert (b - t) (E.image fun e => |e - t|)))
    with hD
  have hDne : D.Nonempty := ⟨δ, Finset.mem_insert_self _ _⟩
  have hmpos : 0 < D.min' hDne := by
    rw [Finset.lt_min'_iff]
    intro y hy
    simp only [hD, Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | rfl | rfl | ⟨e, he, rfl⟩
    · exact hδ
    · exact sub_pos.mpr ht.1
    · exact sub_pos.mpr ht.2
    · exact abs_pos.mpr (sub_ne_zero.mpr (fun h => htE (h ▸ he)))
  have hmle : ∀ y ∈ D, D.min' hDne ≤ y := fun y hy => Finset.min'_le D y hy
  refine ⟨D.min' hDne / 2, half_pos hmpos, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (half_lt_self hmpos) (hmle δ (Finset.mem_insert_self _ _))
  · have := hmle (t - a) (by simp [hD])
    linarith [half_lt_self hmpos]
  · have := hmle (b - t) (by simp [hD])
    linarith [half_lt_self hmpos]
  · intro e he
    refine lt_of_lt_of_le (half_lt_self hmpos) (hmle _ ?_)
    simp only [hD, Finset.mem_insert, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inr ⟨e, he, rfl⟩))

/-- The main statement, for an arbitrary codomain, in the form suited to induction on `E`. -/
theorem feA_gen {α : Type*} (E : Finset ℝ) :
    ∀ (f : ℝ → α) (a b : ℝ), a ≤ b → a ∉ E → b ∉ E →
      (∀ t ∈ Set.Icc a b, t ∉ E → ∃ ε > 0, ∀ u ∈ Set.Icc a b, |u - t| < ε → f u = f t) →
      (∀ t ∈ E, t ∈ Set.Ioo a b → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f (t - s) = f (t + s)) →
      f a = f b := by
  refine Finset.induction_on E ?_ ?_
  · intro f a b hab _ _ hloc _
    exact feA_base hab (fun t ht => hloc t ht (Finset.notMem_empty t))
  · intro t E' htE' ih f a b hab ha hb hloc hjump
    have ha' : a ∉ E' := fun h => ha (Finset.mem_insert_of_mem h)
    have hb' : b ∉ E' := fun h => hb (Finset.mem_insert_of_mem h)
    by_cases ht : t ∈ Set.Ioo a b
    · obtain ⟨δ, hδ, hδf⟩ := hjump t (Finset.mem_insert_self t E') ht
      obtain ⟨s, hs0, hsδ, hsa, hsb, hsE⟩ := feA_exists_radius E' htE' hδ ht
      have hts_left : t - s ∉ E' := by
        intro h
        have := hsE (t - s) h
        rw [show t - s - t = -s by ring, abs_neg, abs_of_pos hs0] at this
        exact lt_irrefl s this
      have hts_right : t + s ∉ E' := by
        intro h
        have := hsE (t + s) h
        rw [show t + s - t = s by ring, abs_of_pos hs0] at this
        exact lt_irrefl s this
      have hL := feA_restrict (a' := a) (b' := t - s) E' t le_rfl (by linarith [ht.2])
        (fun h => (lt_irrefl t) (lt_of_le_of_lt h.2 (by linarith))) hloc hjump
      have hR := feA_restrict (a' := t + s) (b' := b) E' t (by linarith [ht.1]) le_rfl
        (fun h => (lt_irrefl t) (lt_of_lt_of_le (by linarith) h.1)) hloc hjump
      have h1 : f a = f (t - s) := ih f a (t - s) hsa.le ha' hts_left hL.1 hL.2
      have h2 : f (t - s) = f (t + s) := hδf s hs0 hsδ
      have h3 : f (t + s) = f b := ih f (t + s) b hsb.le hts_right hb' hR.1 hR.2
      exact h1.trans (h2.trans h3)
    · have htI : t ∉ Set.Icc a b := by
        intro h
        apply ht
        refine ⟨lt_of_le_of_ne h.1 ?_, lt_of_le_of_ne h.2 ?_⟩
        · rintro rfl
          exact ha (Finset.mem_insert_self _ _)
        · rintro rfl
          exact hb (Finset.mem_insert_self _ _)
      have hres := feA_restrict (a' := a) (b' := b) E' t le_rfl le_rfl htI hloc hjump
      exact ih f a b hab ha' hb' hres.1 hres.2

/-- Generalisation of `constant_of_finite_exceptions` to an arbitrary codomain `α`. -/
theorem constant_of_finite_exceptions_gen {α : Type*} {f : ℝ → α} {a b : ℝ} (hab : a ≤ b)
    (E : Finset ℝ) (ha : a ∉ E) (hb : b ∉ E)
    (hloc : ∀ t ∈ Set.Icc a b, t ∉ E → ∃ ε > 0, ∀ u ∈ Set.Icc a b, |u - t| < ε → f u = f t)
    (hjump : ∀ t ∈ E, t ∈ Set.Ioo a b → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f (t - s) = f (t + s)) :
    f a = f b :=
  feA_gen E f a b hab ha hb hloc hjump

/-- `f : ℝ → ℤ` locally constant on `[a, b]` away from the finite set `E`, with agreeing
one-sided values at each point of `E` strictly inside `(a, b)`, satisfies `f a = f b`. -/
theorem constant_of_finite_exceptions {f : ℝ → ℤ} {a b : ℝ} (hab : a ≤ b) (E : Finset ℝ)
    (ha : a ∉ E) (hb : b ∉ E)
    (hloc : ∀ t ∈ Set.Icc a b, t ∉ E → ∃ ε > 0, ∀ u ∈ Set.Icc a b, |u - t| < ε → f u = f t)
    (hjump : ∀ t ∈ E, t ∈ Set.Ioo a b → ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f (t - s) = f (t + s)) :
    f a = f b :=
  constant_of_finite_exceptions_gen hab E ha hb hloc hjump

end SM

#print axioms SM.constant_of_finite_exceptions
#print axioms SM.constant_of_finite_exceptions_gen
