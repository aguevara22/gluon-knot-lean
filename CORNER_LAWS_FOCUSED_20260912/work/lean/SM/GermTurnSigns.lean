import SM.GermDefinition
import SM.ChamberPaths

/-! Actual turn signs are constant on each connected generic germ side.
The source SignChanges condition therefore compares independent side points. -/

namespace SM

theorem signType_cast_product_neg_iff (s t : SignType) :
    (s : ℝ) * (t : ℝ) < 0 ↔ s = -t ∧ s ≠ 0 := by
  cases s <;> cases t <;> norm_num

theorem signType_ne_neg_self {s : SignType} (hs : s ≠ 0) : s ≠ -s := by
  cases s <;> norm_num at *

theorem signType_nonzero_cases {s : SignType} (hs : s ≠ 0) : s = -1 ∨ s = 1 := by
  cases s <;> norm_num at *

theorem signType_eq_iff_ne_neg {s t : SignType} (hs : s ≠ 0) (ht : t ≠ 0) :
    s = t ↔ s ≠ -t := by
  cases s <;> cases t <;> norm_num at *

namespace WallGerm

variable {n : ℕ} (g : WallGerm n)

theorem side_turn_constant (b : Bool) (s t : g.SideParameter) (i : ZMod n) :
    turn (g.sideTuple b s).val i = turn (g.sideTuple b t).val i :=
  generic_family_chi_constant (g.continuous_sideTuple b) s t (i - 1) i (i + 1)

theorem turn_signChanges_opposite {j : ZMod n}
    (h : g.SignChanges (fun P => (turn P j : ℝ))) (s t : g.SideParameter) :
    turn (g.sideTuple true s).val j = -turn (g.sideTuple false t).val j ∧
      turn (g.sideTuple true s).val j ≠ 0 := by
  obtain ⟨δ, hδ, hδr, hchange⟩ := h
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have hc := (signType_cast_product_neg_iff _ _).mp (hchange t₀ ht₀)
  rw [g.side_turn_constant true s t₀ j, g.side_turn_constant false t t₀ j]
  exact hc

end WallGerm
end SM
