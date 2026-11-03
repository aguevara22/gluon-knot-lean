import DirectGLSSW.FiniteFirstReturn

namespace DirectGLSSW.OrderedPointInsertion

/-- Removing one point from a finite cyclic order advances by one step unless
that step was the removed point, in which case it advances two steps. -/
theorem orderedCyclicSuccessor_complement_firstReturn
    {β : Type*} [LinearOrder β] [Fintype β]
    (b : β) (y : {z : β // z ≠ b}) :
    (orderedCyclicSuccessor {z : β // z ≠ b} y).val =
      if orderedCyclicSuccessor β y.val = b then orderedCyclicSuccessor β b
      else orderedCyclicSuccessor β y.val := by
  let C := {z : β // z ≠ b}
  let x : C := y
  let s := orderedCyclicSuccessor β
  have hY := orderedCyclicSuccessor_order_spec β y.val
  have hB := orderedCyclicSuccessor_order_spec β b
  have hsB_ne : s b ≠ b := by
    intro hsB
    rcases hB with ⟨hBlt, _⟩ | ⟨hBmax, hBmin⟩
    · rw [hsB] at hBlt
      exact (lt_irrefl b) hBlt
    · have hby : b ≤ y.val := by simpa [s, hsB] using hBmin y.val
      exact y.property (le_antisymm hby (hBmax y.val)).symm
  let cval := if s y.val = b then s b else s y.val
  have hcval : cval ≠ b := by
    dsimp [cval]
    split_ifs with h
    · exact hsB_ne
    · exact h
  let z : C := ⟨cval, hcval⟩
  have hspec :
      (x < z ∧ ∀ w : C, x < w → z ≤ w) ∨
      ((∀ w : C, w ≤ x) ∧ ∀ w : C, z ≤ w) := by
    by_cases hyb : s y.val = b
    · rcases hY with ⟨hYlt, hYmin⟩ | ⟨hYmax, hYmin⟩
      · rcases hB with ⟨hBlt, hBmin⟩ | ⟨hBmax, hBmin⟩
        · left
          constructor
          · have hlt : y.val < s b := by
              calc
                y.val < s y.val := hYlt
                _ = b := hyb
                _ < s b := hBlt
            simpa only [x, z, cval, if_pos hyb] using hlt
          · intro w hw
            have hw' : y.val < w.val := by exact hw
            have hbw : b ≤ w.val := by simpa only [s, hyb] using hYmin w.val hw'
            have hbwl : b < w.val := lt_of_le_of_ne hbw (by
              intro heq
              exact w.property heq.symm)
            have hle : s b ≤ w.val := hBmin w.val hbwl
            simpa only [x, z, cval, if_pos hyb] using hle
        · right
          constructor
          · intro w
            by_cases hyw : y.val < w.val
            · have hbw : b ≤ w.val := by simpa only [s, hyb] using hYmin w.val hyw
              have hwb : w.val ≤ b := hBmax w.val
              exact False.elim (w.property (le_antisymm hwb hbw))
            · simpa only [x] using (le_of_not_gt hyw)
          · intro w
            have hle : s b ≤ w.val := hBmin w.val
            simpa only [x, z, cval, if_pos hyb] using hle
      · rcases hB with ⟨hBlt, hBmin⟩ | ⟨hBmax, hBmin⟩
        · right
          constructor
          · intro w
            simpa only [x] using hYmax w.val
          · intro w
            have hbw : b ≤ w.val := by simpa only [s, hyb] using hYmin w.val
            have hbwl : b < w.val := lt_of_le_of_ne hbw (by
              intro heq
              exact w.property heq.symm)
            have hle : s b ≤ w.val := hBmin w.val hbwl
            simpa only [x, z, cval, if_pos hyb] using hle
        · have hby : b ≤ y.val := by simpa only [s, hyb] using hYmin y.val
          exact False.elim (y.property (le_antisymm hby (hBmax y.val)).symm)
    · rcases hY with ⟨hYlt, hYmin⟩ | ⟨hYmax, hYmin⟩
      · left
        constructor
        · have hlt : y.val < s y.val := hYlt
          simpa only [x, z, cval, if_neg hyb] using hlt
        · intro w hw
          have hw' : y.val < w.val := by exact hw
          have hle : s y.val ≤ w.val := hYmin w.val hw'
          simpa only [x, z, cval, if_neg hyb] using hle
      · right
        constructor
        · intro w
          simpa only [x] using hYmax w.val
        · intro w
          have hle : s y.val ≤ w.val := hYmin w.val
          simpa only [x, z, cval, if_neg hyb] using hle
  have hsucc : orderedCyclicSuccessor C x = z :=
    orderedCyclicSuccessor_eq_of_order_spec C x z hspec
  exact congrArg Subtype.val hsucc

/-- The first-return law transports an ordered successor through the
insertion isomorphism that restores the omitted point. -/
theorem orderedCyclicSuccessor_orderIso_complement
    {α β : Type*} [LinearOrder α] [Fintype α]
    [LinearOrder β] [Fintype β]
    (a : α) (b : β)
    (E : α ≃o {z : β // z ≠ b})
    (hb : orderedCyclicSuccessor β b = (E a).val) :
    ∀ x : α,
      orderedCyclicSuccessor β (E x).val =
        if orderedCyclicSuccessor α x = a then b
        else (E (orderedCyclicSuccessor α x)).val := by
  intro x
  let C := {z : β // z ≠ b}
  have hNat : orderedCyclicSuccessor C (E x) = E (orderedCyclicSuccessor α x) :=
    orderedCyclicSuccessor_naturality α E x
  have hEq := orderedCyclicSuccessor_complement_firstReturn b (E x)
  rw [hNat] at hEq
  have hiff : orderedCyclicSuccessor β (E x).val = b ↔
      orderedCyclicSuccessor α x = a := by
    constructor
    · intro hc
      rw [if_pos hc, hb] at hEq
      exact E.injective (Subtype.ext hEq)
    · intro hxa
      by_contra hc
      rw [if_neg hc, hxa, ← hb] at hEq
      have hs : orderedCyclicSuccessor β b =
          orderedCyclicSuccessor β (E x).val := by
        simpa only using hEq
      have heq := (orderedCyclicSuccessor β).injective hs
      exact (E x).property heq.symm
  by_cases hxa : orderedCyclicSuccessor α x = a
  · have hc := hiff.mpr hxa
    simp only [if_pos hxa]
    exact hc
  · have hc : orderedCyclicSuccessor β (E x).val ≠ b := fun hc => hxa (hiff.mp hc)
    have hEq' := hEq
    rw [if_neg hc] at hEq'
    simp only [if_neg hxa]
    exact hEq'.symm

end DirectGLSSW.OrderedPointInsertion
