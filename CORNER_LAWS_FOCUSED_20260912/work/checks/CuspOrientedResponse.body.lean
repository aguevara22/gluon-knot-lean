namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The source consecutive signed deletion identity uses chirotope
negative minus positive, independently of real time orientation. All roots
are retained and deletion is at the actual center. -/
theorem cusp_negative_minus_positive_near (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sNegative sPositive : w.Parameter, ∀ hNegative0 : sNegative.val ≠ 0, ∀ hPositive0 : sPositive.val ≠ 0,
        turn (w.curve sNegative) j = -1 → turn (w.curve sPositive) j = 1 →
        |sNegative.val| < δ → |sPositive.val| < δ →
        treeCoefficient (w.curve sNegative) (w.generic_punctured sNegative hNegative0).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sPositive) (w.generic_punctured sPositive hPositive0).1 g
            (by have := hf.1; omega) =
          treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega) := by
  classical
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ := w.cusp_signed_response_all_roots j g hf
  let F : w.Parameter → ℤ := fun s =>
    if hs : s.val ≠ 0 then
      treeCoefficient (w.curve s) (w.generic_punctured s hs).1 g (by have := hf.1; omega)
    else 0
  have hFresponse :
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
          (F sPlus - F sMinus = d *
            treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
              (fusionIndex j g) (by have := hf.1; omega)) := by
    intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    simpa only [F, dif_pos (ne_of_gt hPlus), dif_pos (ne_of_lt hMinus)] using
      hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  refine ⟨δ, hδ, hrad, ?_⟩
  intro sNegative sPositive hNegative0 hPositive0 hNegative hPositive hNegativeNear hPositiveNear
  have h := w.turn_response_right_minus_left j F
    (treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
      (fusionIndex j g) (by have := hf.1; omega)) d δ hd hδ hrad hFresponse
    sNegative sPositive hNegative0 hPositive0 hNegative hPositive hNegativeNear hPositiveNear
  simpa only [F, dif_pos hNegative0, dif_pos hPositive0] using h


/-- The source consecutive signed deletion identity uses chirotope
negative minus positive, independently of real time orientation. All roots
are retained and deletion is at the actual center. -/
theorem cusp_negative_minus_positive (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) (sNegative sPositive : w.Parameter)
    (hNegative0 : sNegative.val ≠ 0) (hPositive0 : sPositive.val ≠ 0)
    (hNegative : turn (w.curve sNegative) j = -1) (hPositive : turn (w.curve sPositive) j = 1) :
    treeCoefficient (w.curve sNegative) (w.generic_punctured sNegative hNegative0).1 g
        (by have := hf.1; omega) -
      treeCoefficient (w.curve sPositive) (w.generic_punctured sPositive hPositive0).1 g
        (by have := hf.1; omega) =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j g) (by have := hf.1; omega) := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.cusp_negative_minus_positive_near j g hf
  obtain ⟨r, hr0, hrNear, hrChi⟩ := w.nearby_same_chirotope δ hδ hδr sNegative hNegative0
  obtain ⟨l, hl0, hlNear, hlChi⟩ := w.nearby_same_chirotope δ hδ hδr sPositive hPositive0
  have hrTurn : turn (w.curve r) j = -1 := (hrChi (j - 1) j (j + 1)).trans hNegative
  have hlTurn : turn (w.curve l) j = 1 := (hlChi (j - 1) j (j + 1)).trans hPositive
  have he := hresponse r l hr0 hl0 hrTurn hlTurn hrNear hlNear
  have hrCoeff := treeCoefficient_eq_of_chi (w.generic_punctured r hr0).1
    (w.generic_punctured sNegative hNegative0).1 hrChi g (by have := hf.1; omega)
  have hlCoeff := treeCoefficient_eq_of_chi (w.generic_punctured l hl0).1
    (w.generic_punctured sPositive hPositive0).1 hlChi g (by have := hf.1; omega)
  rw [hrCoeff, hlCoeff] at he
  exact he


end
end SM.WallGerm
