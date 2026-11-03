import ShiftFirstPair
import CompactSegmentStability
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport

/-- One positive translation radius preserves separation from every actual
later closed side over the entire compact cursor interval. -/
theorem exists_shiftFirstPair_side_radius
    (W : ℕ → PlanarPoint ℝ) (v w : PlanarPoint ℝ) (N : ℕ) (a b : ℝ)
    (hno : ∀ t : ℝ, a≤t → t≤b → ∀ r : ℕ, 0<r → r<N →
      ∀ u : ℝ, 0≤u → u≤1 → W 0+t • v≠affinePoint (W r) (W (r+1)) u) :
    ∃ δ : ℝ, 0<δ ∧ ∀ η : ℝ, 0<η → η<δ →
      ∀ t : ℝ, a≤t → t≤b → ∀ r : ℕ, 0<r → r<N →
      ∀ u : ℝ, 0≤u → u≤1 →
      shiftFirstPair W w η 0+t • v≠affinePoint (shiftFirstPair W w η r) (shiftFirstPair W w η (r+1)) u := by
  let P : ℕ → ℝ → Prop := fun r η => 0<r → r<N →
    ∀ t : ℝ, a≤t → t≤b → ∀ u : ℝ, 0≤u → u≤1 →
      shiftFirstPair W w η 0+t • v≠affinePoint (shiftFirstPair W w η r) (shiftFirstPair W w η (r+1)) u
  have hf : ∀ r∈Finset.range N, ∃ δ : ℝ, 0<δ ∧ ∀ η : ℝ, 0<η → η<δ → P r η := by
    intro r hr
    by_cases hr0 : 0<r
    · have hrN : r<N := Finset.mem_range.mp hr
      obtain ⟨δ,hδ,hh⟩ := CursorSegmentStability.exists_translated_segments_separation_radius
        (W 0) (W 0+v) (W r) (W (r+1)) w (if r=1 then w else 0) 0 a b (by
          intro t ht u hu
          have he : affinePoint (W 0) (W 0+v) t=W 0+t • v := by ext <;> dsimp [affinePoint] <;> ring
          rw [he]
          exact hno t ht.1 ht.2 r hr0 hrN u hu.1 hu.2)
      refine ⟨δ,hδ,?_⟩
      intro η hη hηδ _ _ t ht0 ht1 u hu0 hu1
      have he := hh η (by simpa only [abs_of_pos hη] using hηδ) t ⟨ht0,ht1⟩ u ⟨hu0,hu1⟩
      have hp : affinePoint (W 0+η • w) (W 0+v+η • w) t=shiftFirstPair W w η 0+t • v := by
        dsimp [shiftFirstPair,affinePoint]
        ext <;> dsimp <;> ring
      rw [hp] at he
      have hr1 : shiftFirstPair W w η r = W r+η • (if r=1 then w else 0) := by
        by_cases hr1 : r=1
        · simp only [shiftFirstPair,if_pos (Or.inr hr1),if_pos hr1]
        · simp only [shiftFirstPair,if_neg (by omega : ¬(r=0 ∨ r=1)),if_neg hr1,smul_zero,add_zero]
      have hr2 : shiftFirstPair W w η (r+1) = W (r+1)+η • (0 : PlanarPoint ℝ) := by
        simp only [shiftFirstPair,if_neg (by omega : ¬(r+1=0 ∨ r+1=1)),smul_zero,add_zero]
      rwa [hr1,hr2]
    · exact ⟨1,by norm_num,fun _ _ _ h _ => (hr0 h).elim⟩
  obtain ⟨δ,hδ,hh⟩ := ShortEdgeSignStability.exists_finset_common_radius (Finset.range N) P hf
  refine ⟨δ,hδ,?_⟩
  intro η hη hηδ t ht0 ht1 r hr0 hrN u hu0 hu1
  exact hh η hη hηδ r (Finset.mem_range.mpr hrN) hr0 hrN t ht0 ht1 u hu0 hu1

end DirectGLSSW.CursorWallTransport
