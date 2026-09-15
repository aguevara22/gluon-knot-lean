namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The flat law for the actual rooted tree coefficient at every source
root and every pair of punctured right/left representatives in the germ.
Connected-side chirotope constancy removes the local radius restriction. -/
theorem flat_right_minus_left (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) (sRight sLeft : w.Parameter)
    (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hRight : turn (w.curve sRight) j = -1) (hLeft : turn (w.curve sLeft) j = 1) :
    treeCoefficient (w.curve sRight) (w.generic_punctured sRight hRight0).1 g
        (by have := hf.1; omega) -
      treeCoefficient (w.curve sLeft) (w.generic_punctured sLeft hLeft0).1 g
        (by have := hf.1; omega) =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j g) (by have := hf.1; omega) := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.flat_right_minus_left_near j g hf
  obtain ⟨r, hr0, hrNear, hrChi⟩ := w.nearby_same_chirotope δ hδ hδr sRight hRight0
  obtain ⟨l, hl0, hlNear, hlChi⟩ := w.nearby_same_chirotope δ hδ hδr sLeft hLeft0
  have hrTurn : turn (w.curve r) j = -1 := (hrChi (j - 1) j (j + 1)).trans hRight
  have hlTurn : turn (w.curve l) j = 1 := (hlChi (j - 1) j (j + 1)).trans hLeft
  have he := hresponse r l hr0 hl0 hrTurn hlTurn hrNear hlNear
  have hrCoeff := treeCoefficient_eq_of_chi (w.generic_punctured r hr0).1
    (w.generic_punctured sRight hRight0).1 hrChi g (by have := hf.1; omega)
  have hlCoeff := treeCoefficient_eq_of_chi (w.generic_punctured l hl0).1
    (w.generic_punctured sLeft hLeft0).1 hlChi g (by have := hf.1; omega)
  rw [hrCoeff, hlCoeff] at he
  exact he

end
end SM.WallGerm
