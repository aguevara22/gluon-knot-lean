namespace SM

noncomputable section
variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The half-difference of opposite sign values equals the positive-side
sign after the exact integer-to-ring cast. No nontrivial-ring premise is needed. -/
theorem sign_half_difference (s t : SignType) (h : s = -t) :
    (((s : ℤ) : R) - ((t : ℤ) : R)) * ⅟ (2 : R) = ((s : ℤ) : R) := by
  have hi : (s : ℤ) - (t : ℤ) = 2 * (s : ℤ) := by
    cases s <;> cases t <;> norm_num at *
  have hr : ((s : ℤ) : R) - ((t : ℤ) : R) = 2 * ((s : ℤ) : R) := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using
      congrArg (fun z : ℤ => (z : R)) hi
  rw [hr, mul_right_comm, mul_invOf_self, one_mul]

end

namespace WallGerm

noncomputable section
variable {n : ℕ}

/-- Source sign change, together with connected generic sides, gives opposite
nonzero chirotopes at independent side parameters, not merely paired times. -/
theorem side_chi_signChanges_opposite (w : WallGerm n) (i j k : ZMod n)
    (h : w.SignChanges (fun P => (chi P i j k : ℝ))) (s t : w.SideParameter) :
    chi (w.sideTuple true s).val i j k = -chi (w.sideTuple false t).val i j k ∧
      chi (w.sideTuple true s).val i j k ≠ 0 := by
  obtain ⟨δ, hδ, hδr, hchange⟩ := h
  let t₀ : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have hc := (signType_cast_product_neg_iff _ _).mp (hchange t₀ ht₀)
  rw [generic_family_chi_constant (w.continuous_sideTuple true) s t₀ i j k,
    generic_family_chi_constant (w.continuous_sideTuple false) t t₀ i j k]
  exact hc

/-- The constant signed value is fixed at the positive-side base point; every
actual negative parameter has its opposite. All evaluations stay inside w. -/
theorem chi_signChanges_parameters (w : WallGerm n) (i j k : ZMod n)
    (h : w.SignChanges (fun P => (chi P i j k : ℝ)))
    (sMinus sPlus : w.Parameter) (hMinus : sMinus.val < 0) (hPlus : 0 < sPlus.val) :
    chi (w.curve sPlus) i j k = chi (w.sideTuple true w.sideBase).val i j k ∧
      chi (w.curve sMinus) i j k = -chi (w.sideTuple true w.sideBase).val i j k ∧
      chi (w.sideTuple true w.sideBase).val i j k ≠ 0 := by
  let s : w.SideParameter := ⟨sPlus.val, hPlus, sPlus.property.2⟩
  let t : w.SideParameter := ⟨-sMinus.val, neg_pos.mpr hMinus, by linarith [sMinus.property.1]⟩
  have hp : (w.sideTuple true s).val = w.curve sPlus := by
    apply congrArg w.curve
    apply Subtype.ext
    rfl
  have hm : (w.sideTuple false t).val = w.curve sMinus := by
    apply congrArg w.curve
    apply Subtype.ext
    change -(-sMinus.val) = sMinus.val
    exact neg_neg _
  have hb := generic_family_chi_constant (w.continuous_sideTuple true) s w.sideBase i j k
  have hc := w.side_chi_signChanges_opposite i j k h s t
  rw [hp] at hb
  rw [hp, hm, hb] at hc
  refine ⟨hb, ?_, hc.2⟩
  calc
    chi (w.curve sMinus) i j k = -(-chi (w.curve sMinus) i j k) := (neg_neg _).symm
    _ = -chi (w.sideTuple true w.sideBase).val i j k := congrArg Neg.neg hc.1.symm

variable [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual critical half-jump is one fixed integer sign on all independent
punctured side points. This proves the source normalization instead of assuming it. -/
theorem boundary_half_jump_signed (w : WallGerm n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n)
    (h : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ))) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧
      ∀ sMinus sPlus : w.Parameter, sMinus.val < 0 → 0 < sPlus.val →
        (geometricBoundaryArray (R := R) (w.curve sPlus) g t -
          geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R) = (d : R) := by
  let σ := chi (w.sideTuple true w.sideBase).val (boundaryIndex g t.upper)
    (boundaryIndex g t.middle) (boundaryIndex g t.lower)
  have hσ : σ ≠ 0 := (w.side_chi_signChanges_opposite _ _ _ h w.sideBase w.sideBase).2
  refine ⟨(σ : ℤ), ?_, ?_⟩
  · rcases signType_nonzero_cases hσ with hn | hp
    · left
      rw [hn]
      rfl
    · right
      rw [hp]
      rfl
  · intro sMinus sPlus hMinus hPlus
    have hs := w.chi_signChanges_parameters _ _ _ h sMinus sPlus hMinus hPlus
    have hop : chi (w.curve sPlus) (boundaryIndex g t.upper) (boundaryIndex g t.middle)
        (boundaryIndex g t.lower) =
        -chi (w.curve sMinus) (boundaryIndex g t.upper) (boundaryIndex g t.middle)
          (boundaryIndex g t.lower) := by rw [hs.1, hs.2.1, neg_neg]
    change (((chi (w.curve sPlus) (boundaryIndex g t.upper) (boundaryIndex g t.middle)
        (boundaryIndex g t.lower) : ℤ) : R) -
      ((chi (w.curve sMinus) (boundaryIndex g t.upper) (boundaryIndex g t.middle)
        (boundaryIndex g t.lower) : ℤ) : R)) * ⅟ (2 : R) = _
    rw [sign_half_difference _ _ hop, hs.1]

end
end WallGerm
end SM
