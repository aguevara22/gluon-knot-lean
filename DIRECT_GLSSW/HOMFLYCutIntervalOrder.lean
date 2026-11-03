import DirectGLSSW.FiniteCycleSplit
import DirectGLSSW.HOMFLY.BasedTraversal

set_option autoImplicit false

namespace DirectGLSSW.FiniteCycleSplit
open Equiv PermutationOrbits
variable {m : ℕ} [NeZero m]

/-- The middle cut interval in its actual successor order, starting at the
cut port k. That port ceases to be a crossing visit after smoothing. -/
noncomputable def cutMarkEnumeration (k : Fin m) (hk : k ≠ 0) :
    Fin k.val ≃ Fibre (cutPerm k) (componentOf (cutPerm k) k) := by
  let f : Fin k.val → Fibre (cutPerm k) (componentOf (cutPerm k) k) :=
    fun t => ⟨(cutPerm k ^ t.val) k,
      ((componentOf_eq_iff _ _ _).2
        (show (cutPerm k).SameCycle k ((cutPerm k ^ t.val) k) from
          ⟨(t.val : ℤ), by simp only [zpow_natCast]⟩)).symm⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro s t h
    have hv := congrArg (fun x => x.val.val) h
    change ((cutPerm k ^ s.val) k).val = ((cutPerm k ^ t.val) k).val at hv
    apply Fin.ext
    by_cases hs : s.val = 0
    · by_cases ht : t.val = 0
      · omega
      · rw [hs, pow_zero, Perm.one_apply,
          cutPerm_pow_mark_val k hk _ (by omega) t.isLt] at hv
        omega
    · by_cases ht : t.val = 0
      · rw [ht, pow_zero, Perm.one_apply,
          cutPerm_pow_mark_val k hk _ (by omega) s.isLt] at hv
        omega
      · rw [cutPerm_pow_mark_val k hk _ (by omega) s.isLt,
          cutPerm_pow_mark_val k hk _ (by omega) t.isLt] at hv
        exact hv
  · intro x
    have hx : (cutPerm k).SameCycle k x.val :=
      (componentOf_eq_iff _ _ _).1 x.property.symm
    have hside := (cut_sameCycle_mark_iff k hk x.val).1 hx
    obtain ⟨t, ht, he⟩ := cut_mark_exists_pow k hk x.val hside
    exact ⟨⟨t, ht⟩, Subtype.ext he⟩

/-- The complementary cut interval in actual successor order, starting at 0. -/
noncomputable def cutZeroEnumeration (k : Fin m) :
    Fin (m - k.val) ≃ Fibre (cutPerm k) (componentOf (cutPerm k) 0) := by
  let f : Fin (m - k.val) → Fibre (cutPerm k) (componentOf (cutPerm k) 0) :=
    fun t => ⟨(cutPerm k ^ t.val) 0,
      ((componentOf_eq_iff _ _ _).2
        (show (cutPerm k).SameCycle 0 ((cutPerm k ^ t.val) 0) from
          ⟨(t.val : ℤ), by simp only [zpow_natCast]⟩)).symm⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro s t h
    have hv := congrArg (fun x => x.val.val) h
    change ((cutPerm k ^ s.val) 0).val = ((cutPerm k ^ t.val) 0).val at hv
    apply Fin.ext
    by_cases hs : s.val = 0
    · by_cases ht : t.val = 0
      · omega
      · rw [hs, pow_zero, Perm.one_apply,
          cutPerm_pow_zero_val k _ (by omega) t.isLt] at hv
        simp only [Fin.val_zero] at hv
        omega
    · by_cases ht : t.val = 0
      · rw [ht, pow_zero, Perm.one_apply,
          cutPerm_pow_zero_val k _ (by omega) s.isLt] at hv
        simp only [Fin.val_zero] at hv
        omega
      · rw [cutPerm_pow_zero_val k _ (by omega) s.isLt,
          cutPerm_pow_zero_val k _ (by omega) t.isLt] at hv
        omega
  · intro x
    have hx : (cutPerm k).SameCycle 0 x.val :=
      (componentOf_eq_iff _ _ _).1 x.property.symm
    have hside := (cut_sameCycle_zero_iff k x.val).1 hx
    obtain ⟨t, ht, he⟩ := cut_zero_exists_pow k x.val hside
    exact ⟨⟨t, ht⟩, Subtype.ext he⟩

theorem cutMark_card (k : Fin m) (hk : k ≠ 0) :
    Fintype.card (Fibre (cutPerm k) (componentOf (cutPerm k) k)) = k.val := by
  simpa using (Fintype.card_congr (cutMarkEnumeration k hk)).symm

theorem cutZero_card (k : Fin m) :
    Fintype.card (Fibre (cutPerm k) (componentOf (cutPerm k) 0)) = m - k.val := by
  simpa using (Fintype.card_congr (cutZeroEnumeration k)).symm

/-- Actual orbit-enumeration position of a non-cut port in the middle interval. -/
theorem cutMark_orbitPosition (k : Fin m) (hk : k ≠ 0) (i : Fin m)
    (hi : cutSide k i = true) (hik : i ≠ k) :
    ((orbitEnumeration (cutPerm k) k).symm
      ⟨i, ((componentOf_eq_iff _ _ _).2
        ((cut_sameCycle_mark_iff k hk i).2 hi)).symm⟩).val = i.val := by
  have hip : 0 < i.val ∧ i.val ≤ k.val := by
    simpa only [cutSide, decide_eq_true_eq] using hi
  have hit : i.val < k.val := by
    have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
    omega
  let t : Fin (Fintype.card (Fibre (cutPerm k) (componentOf (cutPerm k) k))) :=
    ⟨i.val, by rw [cutMark_card k hk]; exact hit⟩
  have he : orbitEnumeration (cutPerm k) k t =
      ⟨i, ((componentOf_eq_iff _ _ _).2
        ((cut_sameCycle_mark_iff k hk i).2 hi)).symm⟩ := by
    apply Subtype.ext
    apply Fin.ext
    rw [orbitEnumeration_apply_val]
    exact cutPerm_pow_mark_val k hk i.val hip.1 hit
  rw [← he, Equiv.symm_apply_apply]

/-- Actual orbit-enumeration position of a non-cut port in the tail interval. -/
theorem cutZero_orbitPosition (k i : Fin m) (hi : cutSide k i = false)
    (hi0 : i ≠ 0) :
    ((orbitEnumeration (cutPerm k) 0).symm
      ⟨i, ((componentOf_eq_iff _ _ _).2
        ((cut_sameCycle_zero_iff k i).2 hi)).symm⟩).val = i.val - k.val := by
  have hip : 0 < i.val := by
    have hne : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    omega
  have hki : k.val < i.val := by
    simp only [cutSide, decide_eq_false_iff_not] at hi
    omega
  let t : Fin (Fintype.card (Fibre (cutPerm k) (componentOf (cutPerm k) 0))) :=
    ⟨i.val - k.val, by rw [cutZero_card k]; have := i.isLt; omega⟩
  have he : orbitEnumeration (cutPerm k) 0 t =
      ⟨i, ((componentOf_eq_iff _ _ _).2
        ((cut_sameCycle_zero_iff k i).2 hi)).symm⟩ := by
    apply Subtype.ext
    apply Fin.ext
    rw [orbitEnumeration_apply_val]
    change ((cutPerm k ^ (i.val - k.val)) 0).val = i.val
    rw [cutPerm_pow_zero_val k _ (by omega) (by have := i.isLt; omega)]
    omega
  rw [← he, Equiv.symm_apply_apply]

/-- Actual two-component cut traversal rank. The middle interval is first;
its base is k, and the tail interval has base 0. Both exceptional base ports
are deleted crossing visits, so their placement cannot affect retained ones. -/
noncomputable def cutIntervalRank (k : Fin m) (hk : k ≠ 0) (i : Fin m) :
    Fin 2 × ℕ := by
  classical
  exact if h : cutSide k i = true then
    (0, ((orbitEnumeration (cutPerm k) k).symm
      ⟨i, ((componentOf_eq_iff _ _ _).2
        ((cut_sameCycle_mark_iff k hk i).2 h)).symm⟩).val)
  else
    (1, ((orbitEnumeration (cutPerm k) 0).symm
      ⟨i, ((componentOf_eq_iff _ _ _).2
        ((cut_sameCycle_zero_iff k i).2 (by cases hs : cutSide k i <;> simp_all))).symm⟩).val)

/-- The two genuine cut cycles retain the old linear visit order away from
the two cut ports. This includes crossings whose two visits land in different
cut components; that case is why the middle component must be traversed first. -/
theorem cutIntervalRank_before_iff (k : Fin m) (hk : k ≠ 0)
    (i j : Fin m) (hi0 : i ≠ 0) (hik : i ≠ k) (hj0 : j ≠ 0) (hjk : j ≠ k) :
    HOMFLY.rankBefore (cutIntervalRank k hk i) (cutIntervalRank k hk j) ↔
      i.val < j.val := by
  classical
  cases hsi : cutSide k i with
  | false =>
    have hki : k.val < i.val := by
      have hpos : 0 < i.val := by
        have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
        omega
      simp only [cutSide, decide_eq_false_iff_not] at hsi
      omega
    cases hsj : cutSide k j with
    | false =>
      have hkj : k.val < j.val := by
        have hpos : 0 < j.val := by
          have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
          omega
        simp only [cutSide, decide_eq_false_iff_not] at hsj
        omega
      simp only [cutIntervalRank, hsi, hsj, Bool.false_eq_true, ↓reduceDIte,
        cutZero_orbitPosition k i hsi hi0, cutZero_orbitPosition k j hsj hj0,
        HOMFLY.rankBefore]
      simp only [lt_self_iff_false, true_and, false_or]
      omega
    | true =>
      have hjk' : j.val ≤ k.val := by
        have h := (show 0 < j.val ∧ j.val ≤ k.val from by
          simpa only [cutSide, decide_eq_true_eq] using hsj)
        exact h.2
      simp only [cutIntervalRank, hsi, hsj, Bool.false_eq_true, ↓reduceDIte,
        cutZero_orbitPosition k i hsi hi0, cutMark_orbitPosition k hk j hsj hjk,
        HOMFLY.rankBefore]
      norm_num
      omega
  | true =>
    have hik' : i.val ≤ k.val := by
      have h := (show 0 < i.val ∧ i.val ≤ k.val from by
        simpa only [cutSide, decide_eq_true_eq] using hsi)
      exact h.2
    cases hsj : cutSide k j with
    | false =>
      have hkj : k.val < j.val := by
        have hpos : 0 < j.val := by
          have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
          omega
        simp only [cutSide, decide_eq_false_iff_not] at hsj
        omega
      simp only [cutIntervalRank, hsi, hsj, Bool.false_eq_true, ↓reduceDIte,
        cutMark_orbitPosition k hk i hsi hik, cutZero_orbitPosition k j hsj hj0,
        HOMFLY.rankBefore]
      norm_num
      omega
    | true =>
      simp only [cutIntervalRank, hsi, hsj, ↓reduceDIte,
        cutMark_orbitPosition k hk i hsi hik, cutMark_orbitPosition k hk j hsj hjk,
        HOMFLY.rankBefore]
      simp

end DirectGLSSW.FiniteCycleSplit










