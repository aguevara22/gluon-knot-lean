import SM.FusionGeometry

/-! Actual directed determinant signs and positive over/under readings are
unchanged by fusion, since both edge factors are proved strictly positive. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem det_fusion (P : LabelledTuple (n + 1)) {j : ZMod (n + 1)} {r : ℝ}
    (hm : P j = P (j - 1) + r • (P (j + 1) - P (j - 1))) (a b : ZMod (n + 1)) :
    det (edge P a) (edge P b) = (fusionScale r j a * fusionScale r j b) *
      det (edge (deleteVertex P j) (fusionIndex j a))
        (edge (deleteVertex P j) (fusionIndex j b)) := by
  rw [edge_fusion P hm a, edge_fusion P hm b]
  dsimp [det]
  ring

theorem crossingSign_fusion {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) (a b : ZMod (n + 1)) :
    crossingSign (deleteVertex P j) (fusionIndex j a) (fusionIndex j b) =
      crossingSign P a b := by
  obtain ⟨_, r, hr0, hr1, hm⟩ := hb
  have hs : SignType.sign (fusionScale r j a * fusionScale r j b) = 1 :=
    sign_eq_one_iff.mpr (mul_pos (fusionScale_pos hr0 hr1 j a) (fusionScale_pos hr0 hr1 j b))
  simp only [crossingSign, det_fusion P hm a b, sign_mul, hs, one_mul]

theorem positive_over_fusion {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) (a b : ZMod (n + 1)) :
    0 < det (edge P a) (edge P b) ↔
      0 < det (edge (deleteVertex P j) (fusionIndex j a))
        (edge (deleteVertex P j) (fusionIndex j b)) := by
  have hs := crossingSign_fusion hb a b
  change SignType.sign _ = SignType.sign _ at hs
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, hs]

end SM
