import DirectGLSSW.ShortEdgeGenericity
import DirectGLSSW.ShortEdgeCyclicGeometry
import DirectGLSSW.ShortEdgeSeparated

namespace DirectGLSSW.ShortEdgeGenericity

open DirectGLSSW.ShortEdgeCyclicAdapter

theorem collapseFin_ne_of_separated_pair {n : ℕ}
    (a : Fin n) (e f : Fin (n + 1))
    (hef : e ≠ f) (hsucc_ef : cyclicSuccessor e ≠ f)
    (hsucc_fe : cyclicSuccessor f ≠ e) :
    collapseFin a e ≠ collapseFin a f := by
  intro hcollapse
  have hsucc : cyclicSuccessor (a.castSucc : Fin (n + 1)) =
      ⟨a.val + 1, by omega⟩ := by
    apply Fin.ext
    change (a.val + 1 + 0) % (n + 1) = a.val + 1
    exact Nat.mod_eq_of_lt (by have := a.isLt; omega)
  by_cases he : e = a.castSucc
  · subst e
    have hea : collapseFin a (a.castSucc : Fin (n + 1)) = a := by
      exact (collapseFin_eq_a_iff a (a.castSucc : Fin (n + 1))).mpr (Or.inl rfl)
    have hfa : collapseFin a f = a := by rw [← hcollapse, hea]
    have hf := (collapseFin_eq_a_iff a f).mp hfa
    rcases hf with hf | hf
    · exact hef hf.symm
    · exact hsucc_ef (by rw [hsucc]; exact hf.symm)
  · by_cases hf : f = a.castSucc
    · subst f
      have he' : collapseFin a e = a := by
        rw [hcollapse]
        exact (collapseFin_eq_a_iff a (a.castSucc : Fin (n + 1))).mpr (Or.inl rfl)
      rcases (collapseFin_eq_a_iff a e).mp he' with he' | he'
      · exact hef (by simpa using he')
      · exact hsucc_fe (by rw [hsucc]; exact he'.symm)
    · exact hef (collapseFin_injective_off_shortEdge a e f he hf hcollapse)

theorem insert_zero_no_three_separated {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a : Fin n) (v : PlanarPoint ℝ) (e f g : Fin (n + 1))
    (hsep : SeparatedTriple e f g) :
    ¬ ∃ x : PlanarPoint ℝ,
      edgeClosed (insertCyclicAfter q a 0 v) e x ∧
      edgeClosed (insertCyclicAfter q a 0 v) f x ∧
      edgeClosed (insertCyclicAfter q a 0 v) g x := by
  let ce := collapseFin a e
  let cf := collapseFin a f
  let cg := collapseFin a g
  have hcecf : ce ≠ cf := collapseFin_ne_of_separated_pair a e f hsep.1 hsep.2.2.2.1 hsep.2.2.2.2.1
  have hcfeg : cf ≠ cg := collapseFin_ne_of_separated_pair a f g hsep.2.1 hsep.2.2.2.2.2.1 hsep.2.2.2.2.2.2.1
  have hcecg : ce ≠ cg := collapseFin_ne_of_separated_pair a e g hsep.2.2.1 hsep.2.2.2.2.2.2.2.1 hsep.2.2.2.2.2.2.2.2
  have hclosed (i : Fin (n + 1)) (x : PlanarPoint ℝ)
      (hi : edgeClosed (insertCyclicAfter q a 0 v) i x) :
      edgeClosed q (collapseFin a i) x := by
    obtain ⟨t, ht0, ht1, hx⟩ := hi
    by_cases his : i = a.castSucc
    · subst i
      have hsucc : cyclicSuccessor (a.castSucc : Fin (n + 1)) = ⟨a.val + 1, by omega⟩ := by
        apply Fin.ext
        change (a.val + 1 + 0) % (n + 1) = a.val + 1
        exact Nat.mod_eq_of_lt (by have := a.isLt; omega)
      have hleft : insertCyclicAfter q a 0 v (a.castSucc : Fin (n + 1)) = q a := by
        rw [insertCyclicAfter_zero]
        exact congrArg q ((collapseFin_eq_a_iff a (a.castSucc : Fin (n + 1))).mpr (Or.inl rfl))
      have hright : insertCyclicAfter q a 0 v (cyclicSuccessor (a.castSucc : Fin (n + 1))) = q a := by
        rw [insertCyclicAfter_zero, hsucc]
        exact congrArg q ((collapseFin_eq_a_iff a (⟨a.val + 1, by omega⟩ : Fin (n + 1))).mpr (Or.inr rfl))
      rw [hleft, hright] at hx
      have hx' : x = q a := hx.trans (by simp [affinePoint])
      rw [(collapseFin_eq_a_iff a (a.castSucc : Fin (n + 1))).mpr (Or.inl rfl)]
      refine ⟨0, le_rfl, zero_le_one, ?_⟩
      simpa [affinePoint_zero] using hx'
    · have hleft := insertCyclicAfter_zero q a v i
      have hright := insertCyclicAfter_zero q a v (cyclicSuccessor i)
      rw [hleft, hright, collapseFin_cyclicSuccessor a i his] at hx
      exact ⟨t, ht0, ht1, hx⟩
  rintro ⟨x, he, hf, hg⟩
  exact cyclic_no_three_closed_edges q hq ce cf cg x hcecf hcfeg hcecg
    ⟨hclosed e x he, hclosed f x hf, hclosed g x hg⟩

end DirectGLSSW.ShortEdgeGenericity
