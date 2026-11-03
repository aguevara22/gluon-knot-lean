import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

namespace DirectGLSSW

/-- A finite collection of jumps accounts for the entire change of a function
that is constant on event-free closed intervals. -/
theorem finiteJumpTelescope
    {A : Type} [AddCommGroup A]
    (J D : ℝ → A) (T : Finset ℝ)
    (hconst : ∀ a b : ℝ, a ≤ b → (∀ t ∈ T, t < a ∨ b < t) → J a = J b)
    (hjump : ∀ t ∈ T, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ε < ρ → J (t + ε) - J (t - ε) = D t)
    {x y : ℝ} (hxy : x < y) (hx : x ∉ T) (hy : y ∉ T) :
    J y - J x = ∑ t ∈ T.filter (fun t => x < t ∧ t < y), D t := by
  classical
  let S := T.filter (fun t => x < t ∧ t < y)
  have hS : S = T.filter (fun t => x < t ∧ t < y) := rfl
  suffices hmain : ∀ n : ℕ, ∀ (S : Finset ℝ) (T : Finset ℝ) (x y : ℝ),
      S.card = n → S = T.filter (fun t => x < t ∧ t < y) →
      (∀ a b : ℝ, a ≤ b → (∀ t ∈ T, t < a ∨ b < t) → J a = J b) →
      (∀ t ∈ T, ∃ ρ : ℝ, 0 < ρ ∧
        ∀ ε : ℝ, 0 < ε → ε < ρ → J (t + ε) - J (t - ε) = D t) →
      x < y → x ∉ T → y ∉ T →
      J y - J x = ∑ t ∈ S, D t by
    simpa [S, hS] using hmain S.card S T x y rfl rfl hconst hjump hxy hx hy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S T x y hcard hS hconst hjump hxy hx hy
    by_cases hne : S.Nonempty
    · let t : ℝ := S.min' hne
      have htS : t ∈ S := by simpa [t] using S.min'_mem hne
      have hmin : ∀ u ∈ S, t ≤ u := by
        intro u hu
        exact S.min'_le u hu
      have htT : t ∈ T := (Finset.mem_filter.mp (hS ▸ htS)).1
      have hxt : x < t := (Finset.mem_filter.mp (hS ▸ htS)).2.1
      have hty : t < y := (Finset.mem_filter.mp (hS ▸ htS)).2.2
      obtain ⟨ρ, hρ, hj⟩ := hjump t htT
      let gaps := (S.filter (fun u : ℝ => t < u)).image (fun u => u - t)
      let bounds := insert ρ (insert (t - x) (insert (y - t) gaps))
      have hboundsne : bounds.Nonempty := ⟨ρ, by simp [bounds]⟩
      let δ := bounds.min' hboundsne
      have hδmem : δ ∈ bounds := by simpa [δ] using bounds.min'_mem hboundsne
      have hδpos : 0 < δ := by
        rcases Finset.mem_insert.mp hδmem with hz | hz
        · rw [hz]; exact hρ
        · rcases Finset.mem_insert.mp hz with hz | hz
          · rw [hz]; linarith
          · rcases Finset.mem_insert.mp hz with hz | hz
            · rw [hz]; linarith
            · obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hz
              rw [← heq]
              exact sub_pos.mpr (Finset.mem_filter.mp hu).2
      have hδle_rho : δ ≤ ρ := bounds.min'_le ρ (by simp [bounds])
      have hδle_tx : δ ≤ t - x := bounds.min'_le (t - x) (by simp [bounds])
      have hδle_yt : δ ≤ y - t := bounds.min'_le (y - t) (by simp [bounds])
      have hδle_gap : ∀ u ∈ S, t < u → δ ≤ u - t := by
        intro u hu htu
        have hgap : u - t ∈ gaps := by
          apply Finset.mem_image.mpr
          exact ⟨u, Finset.mem_filter.mpr ⟨hu, htu⟩, rfl⟩
        have hbound : u - t ∈ bounds := by simp [bounds, hgap]
        have : δ ≤ u - t := bounds.min'_le (u - t) hbound
        exact this
      let ε := δ / 2
      have hεpos : 0 < ε := by dsimp [ε]; linarith
      have hεrho : ε < ρ := by dsimp [ε]; linarith
      have hεtx : ε < t - x := by dsimp [ε]; linarith
      have hεyt : ε < y - t := by dsimp [ε]; linarith
      have hεgap : ∀ u ∈ S, t < u → ε < u - t := by
        intro u hu htu
        have := hδle_gap u hu htu
        dsimp [ε]
        linarith
      have hxleft : J x = J (t - ε) := by
        apply hconst x (t - ε)
        · linarith
        intro v hv
        rcases lt_or_ge v x with hvx | hxv
        · exact Or.inl hvx
        by_cases hvb : t - ε < v
        · exact Or.inr hvb
        have hvle : v ≤ t - ε := le_of_not_gt hvb
        have hvt : v < t := by linarith
        right
        have hxvstrict : x < v := by
          rcases lt_or_eq_of_le hxv with hlt | heq
          · exact hlt
          · subst v
            exact (hx hv).elim
        have hvS : v ∈ S := by
          rw [hS]
          simp only [Finset.mem_filter]
          exact ⟨hv, ⟨hxvstrict, lt_trans hvt hty⟩⟩
        have : t ≤ v := hmin v hvS
        linarith
      have hz : t + ε < y := by linarith
      have hznot : t + ε ∉ T := by
        intro hmem
        have hmemS : t + ε ∈ S := by
          rw [hS]
          simp only [Finset.mem_filter]
          exact ⟨hmem, ⟨lt_trans hxt (by linarith), hz⟩⟩
        have hgap := hεgap (t + ε) hmemS (by linarith)
        linarith
      let S' := T.filter (fun u => t + ε < u ∧ u < y)
      have hS' : S' = S.erase t := by
        apply Finset.ext
        intro u
        constructor
        · intro hu
          have huT := (Finset.mem_filter.mp hu).1
          have htu := (Finset.mem_filter.mp hu).2.1
          have huy := (Finset.mem_filter.mp hu).2.2
          have huS : u ∈ S := by
            rw [hS]
            simp only [Finset.mem_filter]
            exact ⟨huT, ⟨lt_trans hxt (lt_trans (by linarith) htu), huy⟩⟩
          have hut : u ≠ t := by intro heq; subst u; linarith
          exact Finset.mem_erase.mpr ⟨hut, huS⟩
        · intro hu
          have huS := (Finset.mem_erase.mp hu).2
          have huT := (Finset.mem_filter.mp (hS ▸ huS)).1
          have huy := (Finset.mem_filter.mp (hS ▸ huS)).2.2
          have htu : t < u := by
            have hle := hmin u huS
            have hut := (Finset.mem_erase.mp hu).1
            rcases lt_or_eq_of_le hle with hlt | heq
            · exact hlt
            · subst u
              exact (hut rfl).elim
          have hgap := hεgap u huS htu
          change u ∈ T.filter (fun v => t + ε < v ∧ v < y)
          simp only [Finset.mem_filter]
          exact ⟨huT, ⟨by linarith, huy⟩⟩
      have hS'lt : S'.card < S.card := by
        rw [hS']
        exact Finset.card_erase_lt_of_mem htS
      have hS'n : S'.card < n := by rw [← hcard]; exact hS'lt
      have hrec := ih S'.card hS'n S' T (t + ε) y rfl rfl hconst hjump hz hznot hy
      have hsum : (∑ u ∈ S, D u) = D t + ∑ u ∈ S', D u := by
        calc
          (∑ u ∈ S, D u) = (∑ u ∈ S.erase t, D u) + D t :=
            (Finset.sum_erase_add S (fun u => D u) htS).symm
          _ = D t + ∑ u ∈ S.erase t, D u := by abel
          _ = D t + ∑ u ∈ S', D u := by rw [hS']
      have hjumpEq := hj ε hεpos hεrho
      have hlocal : J (t + ε) - J x = D t := by
        rw [← hxleft] at hjumpEq
        exact hjumpEq
      calc
        J y - J x = (J y - J (t + ε)) + (J (t + ε) - J x) := by abel
        _ = (∑ u ∈ S', D u) + D t := by rw [hrec, hlocal]
        _ = D t + ∑ u ∈ S', D u := by abel
        _ = ∑ u ∈ S, D u := hsum.symm

    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      have hJ : J x = J y := by
        apply hconst x y (le_of_lt hxy)
        intro v hv
        rcases lt_or_ge v x with hvx | hxv
        · exact Or.inl hvx
        by_cases hvy : y < v
        · exact Or.inr hvy
        have hvle : v ≤ y := le_of_not_gt hvy
        have hvne : v ≠ y := by intro heq; subst v; exact hy hv
        have hvlt : v < y := lt_of_le_of_ne hvle hvne
        have hxvstrict : x < v := by
          rcases lt_or_eq_of_le hxv with hlt | heq
          · exact hlt
          · subst v
            exact (hx hv).elim
        have hvS : v ∈ T.filter (fun u => x < u ∧ u < y) := by
          simp only [Finset.mem_filter]
          exact ⟨hv, hxvstrict, hvlt⟩
        rw [hSempty] at hvS
        simp at hvS
      simp [hJ, hSempty, Finset.sum_empty]



end DirectGLSSW
