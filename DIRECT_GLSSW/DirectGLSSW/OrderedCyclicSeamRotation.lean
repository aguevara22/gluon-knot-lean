import DirectGLSSW.OrderedEventSuccessor

namespace DirectGLSSW

/-- Cyclic successor is natural under an order equivalence whose cut minimum
is sent to the target maximum. The strict-order hypothesis is needed only
away from the cut point. -/
theorem orderedCyclicSuccessor_naturality_of_cut
    {A B : Type*} [LinearOrder A] [Fintype A] [LinearOrder B] [Fintype B]
    (E : A ≃ B) (a : A) (b : B)
    (hmin : ∀ x, a ≤ x) (hmax : ∀ y, y ≤ b) (hEa : E a = b)
    (hord : ∀ x y, x ≠ a → y ≠ a → (E x < E y ↔ x < y))
    (x : A) :
    E (orderedCyclicSuccessor A x) = orderedCyclicSuccessor B (E x) := by
  let y := orderedCyclicSuccessor A x
  have hmono : ∀ u v, u ≠ a → v ≠ a → u ≤ v → E u ≤ E v := by
    intro u v hu hv huv
    rcases lt_or_eq_of_le huv with hlt | heq
    · exact le_of_lt ((hord u v hu hv).2 hlt)
    · subst v
      exact le_rfl
  have hinv_cut : E.symm b = a := by
    apply E.injective
    simpa only [Equiv.apply_symm_apply] using hEa.symm
  have hback_not_cut : ∀ z : B, z ≠ b → E.symm z ≠ a := by
    intro z hz hza
    apply hz
    calc
      z = E (E.symm z) := (E.apply_symm_apply z).symm
      _ = E a := congrArg E hza
      _ = b := hEa
  have hcut_not_back : ∀ u : A, u ≠ a → E u ≠ b := by
    intro u hua heq
    apply hua
    calc
      u = E.symm (E u) := (E.symm_apply_apply u).symm
      _ = E.symm b := congrArg E.symm heq
      _ = a := hinv_cut
  have hspecA := orderedCyclicSuccessor_order_spec A x
  have htarget :
      (E x < E y ∧ ∀ z : B, E x < z → E y ≤ z) ∨
      ((∀ z : B, z ≤ E x) ∧ ∀ z : B, E y ≤ z) := by
    by_cases hxa : x = a
    · subst x
      rcases hspecA with ⟨hxy, hminy⟩ | ⟨hmaxa, hleasty⟩
      · right
        change a < y at hxy
        constructor
        · intro z
          simpa only [hEa] using hmax z
        · intro z
          by_cases hzb : z = b
          · simpa [hzb] using hmax (E y)
          · have hza : E.symm z ≠ a := hback_not_cut z hzb
            have haz : a < E.symm z := lt_of_le_of_ne (hmin (E.symm z)) (Ne.symm hza)
            have hle : y ≤ E.symm z := hminy (E.symm z) haz
            simpa only [Equiv.apply_symm_apply] using
              hmono y (E.symm z) (ne_of_gt hxy) hza hle
      · have hy_a : y = a := by
          apply le_antisymm
          · exact hleasty a
          · exact hmin y
        have hallA : ∀ u : A, u = a := by
          intro u
          apply le_antisymm
          · exact hmaxa u
          · exact hmin u
        have hallB : ∀ z : B, z = b := by
          intro z
          have hz : E.symm z = a := hallA (E.symm z)
          calc
            z = E (E.symm z) := (E.apply_symm_apply z).symm
            _ = E a := congrArg E hz
            _ = b := hEa
        right
        constructor
        · intro z
          simpa [hallB z, hEa] using (le_rfl : b ≤ b)
        · intro z
          simpa [hallB z, hy_a, hEa] using (le_rfl : b ≤ b)
    · have hax : a < x := lt_of_le_of_ne (hmin x) (Ne.symm hxa)
      rcases hspecA with ⟨hxy, hminy⟩ | ⟨hmaxx, hleasty⟩
      · left
        change x < y at hxy
        have hya : y ≠ a := by
          intro hya
          rw [hya] at hxy
          exact (not_lt_of_ge (le_of_lt hax)) hxy
        constructor
        · exact (hord x y hxa hya).2 hxy
        · intro z hxz
          by_cases hzb : z = b
          · simpa [hzb] using hmax (E y)
          · have hza : E.symm z ≠ a := hback_not_cut z hzb
            have hxz' : x < E.symm z := (hord x (E.symm z) hxa hza).1 (by
              simpa only [Equiv.apply_symm_apply] using hxz)
            simpa only [Equiv.apply_symm_apply] using
              hmono y (E.symm z) hya hza (hminy (E.symm z) hxz')
      · have hy_a : y = a := by
          apply le_antisymm
          · exact hleasty a
          · exact hmin y
        have hEx_b : E x < b := lt_of_le_of_ne (hmax (E x)) (hcut_not_back x hxa)
        left
        constructor
        · simpa [hy_a, hEa] using hEx_b
        · intro z hxz
          by_cases hzb : z = b
          · simpa [hzb, hy_a, hEa] using (le_rfl : b ≤ b)
          · have hza : E.symm z ≠ a := hback_not_cut z hzb
            have hxz' : x < E.symm z := (hord x (E.symm z) hxa hza).1 (by
              simpa only [Equiv.apply_symm_apply] using hxz)
            have : E.symm z ≤ x := hmaxx (E.symm z)
            exact False.elim ((not_lt_of_ge this) hxz')
  have hsuccessor := orderedCyclicSuccessor_eq_of_order_spec B (E x) (E y) htarget
  exact hsuccessor.symm

end DirectGLSSW
