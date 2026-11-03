import DirectGLSSW.DaughterCarrier
import DirectGLSSW.DaughterTurns

set_option autoImplicit false
namespace DirectGLSSW.AuxiliaryCarrierPairs
open DirectGLSSW

/-- The unordered endpoints of the cyclic edge ending at `i` and starting at `i`. -/
noncomputable def cyclicCarrierPair {α : Type*} [DecidableEq α] {m : ℕ}
    (f : Fin m → α) (i : Fin m) : Finset α :=
  {f ((cyclicSuccessorPerm m)⁻¹ i), f i}

theorem cyclicSuccessorPerm_symm_ne_self {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    (cyclicSuccessorPerm m)⁻¹ i ≠ i := by
  intro h
  have hsi : cyclicSuccessorPerm m i = i := by
    calc
      cyclicSuccessorPerm m i = cyclicSuccessorPerm m ((cyclicSuccessorPerm m)⁻¹ i) :=
        congrArg (cyclicSuccessorPerm m) h.symm
      _ = i := Equiv.apply_symm_apply (cyclicSuccessorPerm m) i
  exact cyclicSuccessor_ne_self (by omega) i
    (by simpa only [cyclicSuccessorPerm_apply] using hsi)

theorem cyclicCarrierPair_card {α : Type*} [DecidableEq α] {m : ℕ}
    (hm : 3 ≤ m) (f : Fin m → α) (hf : Function.Injective f) (i : Fin m) :
    (cyclicCarrierPair f i).card=2 := by
  have hne : f ((cyclicSuccessorPerm m)⁻¹ i) ≠ f i := by
    intro h
    have hi := hf h
    exact cyclicSuccessorPerm_symm_ne_self hm i hi
  exact Finset.card_pair hne

theorem cyclicCarrierPair_injective {α : Type*} [DecidableEq α] {m : ℕ}
    (hm : 3 ≤ m) (f : Fin m → α) (hf : Function.Injective f) :
    Function.Injective (cyclicCarrierPair f) := by
  intro i j hij
  let σ := cyclicSuccessorPerm m
  have hmem : f i ∈ cyclicCarrierPair f j := by
    rw [← hij]
    simp [cyclicCarrierPair]
  have hchoices : f i=f (σ⁻¹ j) ∨ f i=f j := by
    simpa [cyclicCarrierPair, σ] using hmem
  rcases hchoices with hprev | hnow
  · have hsij : σ i=j := by
      calc
        σ i = σ (σ⁻¹ j) := congrArg σ (hf hprev)
        _ = j := Equiv.apply_symm_apply σ j
    have hmem' : f (σ⁻¹ i) ∈ cyclicCarrierPair f j := by
      rw [← hij]
      simp [cyclicCarrierPair, σ]
    have hchoices' : f (σ⁻¹ i)=f (σ⁻¹ j) ∨ f (σ⁻¹ i)=f j := by
      simpa [cyclicCarrierPair, σ] using hmem'
    rcases hchoices' with hprev | hnext
    · have heq := hf hprev
      have hij' : i=j := by
        calc
          i = σ (σ⁻¹ i) := (Equiv.apply_symm_apply σ i).symm
          _ = σ (σ⁻¹ j) := congrArg σ heq
          _ = j := Equiv.apply_symm_apply σ j
      exact hij'
    · have hprev_i : σ⁻¹ i=j := hf hnext
      have hsj : σ j=i := by
        calc
          σ j = σ (σ⁻¹ i) := (congrArg σ hprev_i).symm
          _ = i := Equiv.apply_symm_apply σ i
      have hcycle : σ (σ i)=i := by rw [hsij, hsj]
      have htwo := cyclicSuccessor_twice_ne_self hm i
      have hcycle' : cyclicSuccessor (cyclicSuccessor i)=i := by
        simpa only [σ, cyclicSuccessorPerm_apply] using hcycle
      exact (htwo hcycle').elim
  · exact hf hnow

private theorem index_or_successor_of_mem_pair {α : Type*} [DecidableEq α] {m : ℕ}
    (f : Fin m → α) (e : Fin m) (a : α) (ha : a ∈ cyclicCarrierPair f e) :
    ∃ x : Fin m, a=f x ∧ (e=x ∨ cyclicSuccessorPerm m x=e) := by
  have hchoices : a=f ((cyclicSuccessorPerm m)⁻¹ e) ∨ a=f e := by
    simpa [cyclicCarrierPair] using ha
  rcases hchoices with hprev | hnext
  · refine ⟨(cyclicSuccessorPerm m)⁻¹ e,hprev,Or.inr ?_⟩
    exact Equiv.apply_symm_apply (cyclicSuccessorPerm m) e
  · exact ⟨e,hnext,Or.inl rfl⟩

theorem cyclicCarrierPair_no_three_common {α : Type*} [DecidableEq α] {m : ℕ}
    (hm : 3 ≤ m) (f : Fin m → α) (hf : Function.Injective f)
    (i j k : Fin m) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ¬ ∃ a : α, a∈cyclicCarrierPair f i ∧ a∈cyclicCarrierPair f j ∧
      a∈cyclicCarrierPair f k := by
  rintro ⟨a,hai,haj,hak⟩
  obtain ⟨x,hx,hi⟩ := index_or_successor_of_mem_pair f i a hai
  obtain ⟨y,hy,hj⟩ := index_or_successor_of_mem_pair f j a haj
  obtain ⟨z,hz,hk⟩ := index_or_successor_of_mem_pair f k a hak
  have hxy : x=y := hf (hx.symm.trans hy)
  have hxz : x=z := hf (hx.symm.trans hz)
  subst y
  subst z
  by_cases hix : i=x
  · have hjs : cyclicSuccessorPerm m x=j := by
      rcases hj with h | h
      · exact False.elim (hij (hix.trans h.symm))
      · exact h
    have hks : cyclicSuccessorPerm m x=k := by
      rcases hk with h | h
      · exact False.elim (hik (hix.trans h.symm))
      · exact h
    exact hjk (hjs.symm.trans hks)
  · have his : cyclicSuccessorPerm m x=i := by
      rcases hi with h | h
      · exact False.elim (hix h)
      · exact h
    have hjs : j=x := by
      rcases hj with h | h
      · exact h
      · exact False.elim (hij (his.symm.trans h))
    have hks : k=x := by
      rcases hk with h | h
      · exact h
      · exact False.elim (hik (his.symm.trans h))
    exact hjk (hjs.trans hks.symm)

/-! Actual daughter specialization. It uses the established parent G1/G2 and
nonalternation hypotheses; it does not assume a generic daughter polygon. -/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ} (q : Fin n → PlanarPoint K)
variable (hG2 : cyclicNoTripleIntersections q)
variable (S : Finset (PolygonCrossing q))

noncomputable def daughterCarrierPair (root : PolygonEvent q)
    (i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root))) : Finset (Fin n) :=
  cyclicCarrierPair (DaughterFirstReturn.daughterCarrier q hG2 S root) i

theorem daughterCarrierPair_card
    (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : DaughterFirstReturn.retainedCorner q S root)
    (i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root))) :
    (daughterCarrierPair q hG2 S root i).card=2 := by
  let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
  have hm : 3≤m := DaughterTurns.daughterVertexCount_ge_three q hG2 S hn hG1 root hroot
  have hf := DaughterFirstReturn.daughterCarrier_injective q hG2 S hn hNA root
  exact cyclicCarrierPair_card hm (DaughterFirstReturn.daughterCarrier q hG2 S root) hf i

theorem daughterCarrierPair_injective
    (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : DaughterFirstReturn.retainedCorner q S root) :
    Function.Injective (daughterCarrierPair q hG2 S root) := by
  let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
  have hm : 3≤m := DaughterTurns.daughterVertexCount_ge_three q hG2 S hn hG1 root hroot
  have hf := DaughterFirstReturn.daughterCarrier_injective q hG2 S hn hNA root
  exact cyclicCarrierPair_injective hm (DaughterFirstReturn.daughterCarrier q hG2 S root) hf

theorem daughterCarrierPair_no_three_common
    (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : DaughterFirstReturn.retainedCorner q S root)
    (i j k : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)))
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ¬ ∃ a : Fin n, a∈daughterCarrierPair q hG2 S root i ∧
      a∈daughterCarrierPair q hG2 S root j ∧ a∈daughterCarrierPair q hG2 S root k := by
  let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
  have hm : 3≤m := DaughterTurns.daughterVertexCount_ge_three q hG2 S hn hG1 root hroot
  have hf := DaughterFirstReturn.daughterCarrier_injective q hG2 S hn hNA root
  exact cyclicCarrierPair_no_three_common hm
    (DaughterFirstReturn.daughterCarrier q hG2 S root) hf i j k hij hjk hik

end DirectGLSSW.AuxiliaryCarrierPairs







