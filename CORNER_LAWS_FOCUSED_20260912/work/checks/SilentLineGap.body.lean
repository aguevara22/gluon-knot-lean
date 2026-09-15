namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Both assertions of source pf:line-gap for every actual selected collinear
list in a weak polygon, using its exact endpoint-normalized sign ratios.
The negative assertion requires both endpoints of the physical root word. -/
theorem silent_line_gap (hn : 3 ≤ n) {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) (k : ℕ) (hk : 2 ≤ k) (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω) :
    (∃ j : Fin k, lineGapEpsilon t j = 1 ∧
      2 ≤ (r j.succ).val - (r j.castSucc).val) ∧
    ((r 0).val = 0 → (r (Fin.last k)).val = n - 1 →
      ∃ j : Fin k, lineGapEpsilon t j = -1 ∧
        2 ≤ (r j.succ).val - (r j.castSucc).val) := by
  have hinj := weak_line_coordinate_injective hP g r hr p ω t hline
  have hd := selected_endpoint_difference_nonzero (by omega : 0 < k) t hinj
  let u := normalizedLineCoordinate t
  let p' := p + t 0 • ω
  let ω' := (t (Fin.last k) - t 0) • ω
  have hu : ∀ l, boundaryWord P g (r l) = p' + u l • ω' := by
    intro l
    exact (hline l).trans (normalizedLineCoordinate_representation p ω t hd l)
  have hui : Function.Injective u := normalizedLineCoordinate_injective t hinj hd
  have hend : u 0 < u (Fin.last k) := by
    change normalizedLineCoordinate t 0 < normalizedLineCoordinate t (Fin.last k)
    rw [normalizedLineCoordinate_first, normalizedLineCoordinate_last t hd]
    norm_num
  let leaf : Fin k → Prop := fun j => (r j.succ).val = (r j.castSucc).val + 1
  have hclear : ∀ j : Fin k, leaf j → ∀ l : Fin (k + 1),
      ¬ (u j.castSucc < u l ∧ u l < u j.succ) ∧
      ¬ (u j.succ < u l ∧ u l < u j.castSucc) :=
    fun j hj l => weak_line_selection_clear hP g r hr p' ω' u hu j hj l
  have hnext : ∀ j l : Fin k, j.val + 1 = l.val → ¬ (leaf j ∧ leaf l) :=
    fun j l hjl => weak_line_selection_no_successive_leaves hP g r p' ω' u hu j l hjl
  have hlength (j : Fin k) (hj : ¬ leaf j) :
      2 ≤ (r j.succ).val - (r j.castSucc).val := by
    have hpos : r j.castSucc < r j.succ := hr Fin.castSucc_lt_succ
    change (r j.castSucc).val < (r j.succ).val at hpos
    change ¬ ((r j.succ).val = (r j.castSucc).val + 1) at hj
    omega
  constructor
  · obtain ⟨j, hj, hl⟩ := FiniteLineOrder.exists_increasing_nonleaf_gap
      k hk u hui leaf hend hclear hnext
    exact ⟨j, (lineGapEpsilon_positive t j).mpr hj, hlength j hl⟩
  · intro hfirst hlast
    have hclose : ∀ l, ¬ (u 0 < u l ∧ u l < u (Fin.last k)) :=
      weak_line_selection_root_clear hP g r hr p' ω' u hu hfirst hlast
    have hf : ¬ leaf ⟨0, by omega⟩ :=
      weak_line_selection_first_not_leaf hP g (by omega) r p' ω' u hu hfirst hlast
    have hh : ¬ leaf ⟨k - 1, by omega⟩ :=
      weak_line_selection_last_not_leaf hP g (by omega) r p' ω' u hu hfirst hlast
    obtain ⟨j, hj, hl⟩ := FiniteLineOrder.exists_decreasing_nonleaf_gap
      k hk u hui leaf hend hclear hnext hclose hf hh
    exact ⟨j, (lineGapEpsilon_negative t j).mpr hj, hlength j hl⟩

/-- The source lemma applied directly to vanishing actual determinants.
The printed distinct line coordinates are constructed from the selected
points themselves; no affine-data oracle is required of the caller. -/
theorem silent_line_gap_of_collinear (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (k : ℕ) (hk : 2 ≤ k)
    (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (hcol : ∀ l, det (boundaryWord P g (r l) - boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0) :
    Function.Injective (selectedLineCoordinate P g r) ∧
    selectedLineCoordinate P g r 0 = 0 ∧
    selectedLineCoordinate P g r (Fin.last k) = 1 ∧
    (∃ j : Fin k, lineGapEpsilon (selectedLineCoordinate P g r) j = 1 ∧
      2 ≤ (r j.succ).val - (r j.castSucc).val) ∧
    ((r 0).val = 0 → (r (Fin.last k)).val = n - 1 →
      ∃ j : Fin k, lineGapEpsilon (selectedLineCoordinate P g r) j = -1 ∧
        2 ≤ (r j.succ).val - (r j.castSucc).val) := by
  have hdata := weak_selected_line_coordinates hP g (by omega : 0 < k) r hr hcol
  exact ⟨hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2,
    silent_line_gap hn hP g k hk r hr (boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0))
      (selectedLineCoordinate P g r) hdata.2.1⟩

end
end SM
