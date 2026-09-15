import SM.GaussWord

/-! Changing a cut in a finite sorted sequence is a rotation. This lemma
compares independently sorted lists, including the empty list; it does not
merely assert that a list is equivalent to a rotation chosen by definition. -/

namespace SM

theorem sorted_map_cut_rotation {α β : Type*} (l : List α) (m : List β)
    (f : α → β) (k : α → ℝ) (t : β → ℝ) (N a : ℝ)
    (hki : Function.Injective k) (hti : Function.Injective t)
    (hl : l.Pairwise (fun x y => k x ≤ k y))
    (hm : m.Pairwise (fun x y => t x ≤ t y))
    (hp : (l.map f).Perm m)
    (hb : ∀ x ∈ l, 0 ≤ k x ∧ k x < N)
    (hk : ∀ x ∈ l, t (f x) = if k x < a then k x - a + N else k x - a) :
    (l.map f).IsRotated m := by
  classical
  let p : α → Bool := fun x => decide (k x < a)
  let lo := l.filter p
  let hi := l.filter (fun x => !p x)
  have hlo (x : α) : x ∈ lo ↔ x ∈ l ∧ k x < a := by simp [lo, p]
  have hhi (x : α) : x ∈ hi ↔ x ∈ l ∧ ¬ k x < a := by simp [hi, p]
  have hls : lo.Pairwise (fun x y => k x ≤ k y) := hl.filter p
  have hhs : hi.Pairwise (fun x y => k x ≤ k y) := hl.filter (fun x => !p x)
  have hsplitperm : (lo ++ hi).Perm l := List.filter_append_perm p l
  have hsplit : lo ++ hi = l := by
    apply List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => hki (le_antisymm hxy hyx))
      _ hl hsplitperm
    apply List.pairwise_append.mpr
    refine ⟨hls, hhs, ?_⟩
    intro x hx y hy
    exact ((hlo x).mp hx).2.le.trans (le_of_not_gt ((hhi y).mp hy).2)
  have hlos : (lo.map f).Pairwise (fun x y => t x ≤ t y) := by
    apply List.pairwise_map.mpr
    apply hls.imp_of_mem
    intro x y hx hy hxy
    obtain ⟨hxl, hxa⟩ := (hlo x).mp hx
    obtain ⟨hyl, hya⟩ := (hlo y).mp hy
    rw [hk x hxl, hk y hyl, if_pos hxa, if_pos hya]
    linarith
  have hhis : (hi.map f).Pairwise (fun x y => t x ≤ t y) := by
    apply List.pairwise_map.mpr
    apply hhs.imp_of_mem
    intro x y hx hy hxy
    obtain ⟨hxl, hxa⟩ := (hhi x).mp hx
    obtain ⟨hyl, hya⟩ := (hhi y).mp hy
    rw [hk x hxl, hk y hyl, if_neg hxa, if_neg hya]
    linarith
  have hnew : ((hi ++ lo).map f).Pairwise (fun x y => t x ≤ t y) := by
    rw [List.map_append]
    apply List.pairwise_append.mpr
    refine ⟨hhis, hlos, ?_⟩
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hul, hua⟩ := (hhi u).mp hu
    obtain ⟨hvl, hva⟩ := (hlo v).mp hv
    have hub := hb u hul
    have hvb := hb v hvl
    rw [hk u hul, hk v hvl, if_neg hua, if_pos hva]
    linarith
  have hp' : ((hi ++ lo).map f).Perm m :=
    ((List.perm_append_comm.trans hsplitperm).map f).trans hp
  have heq : (hi ++ lo).map f = m :=
    List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => hti (le_antisymm hxy hyx)) hnew hm hp'
  have hr : (lo ++ hi).IsRotated (hi ++ lo) := List.isRotated_append
  rw [hsplit] at hr
  have hr' := hr.map f
  rw [heq] at hr'
  exact hr'

end SM
