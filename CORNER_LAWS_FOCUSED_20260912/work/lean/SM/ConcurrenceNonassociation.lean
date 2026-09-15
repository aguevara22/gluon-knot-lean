import SM.ConcurrencePolynomialSupport
import SM.ConcurrencePolynomialIrreducible
import SM.EndpointCollapseWitness
import SM.AreaPolynomialSupport

/-! Nonassociation of the actual named controls. Distinct edge triples are
separated by a collapsed-edge specialization, including the six-cycle case. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

theorem concurrencePolynomial_cyclic (e f g : ZMod n) :
    concurrencePolynomial e f g = concurrencePolynomial f g e := by
  simp only [concurrencePolynomial_formula]
  ring

theorem cycle_no_reversed_edge (hn : 3 ≤ n) (e a : ZMod n)
    (he : e = a + 1) (he1 : e + 1 = a) : False := by
  have htwo : (2 : ZMod n) = 0 := by linear_combination -he + he1
  have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by simpa using htwo)
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

theorem cycle_tail_mem_of_same_slots (hn : 3 ≤ n) (e a b c : ZMod n)
    (i j : Fin 6) (he : e = sixEndpointMap a b c i)
    (he1 : e + 1 = sixEndpointMap a b c j) (hgroup : i.val / 2 = j.val / 2) :
    e ∈ ({a, b, c} : Finset (ZMod n)) := by
  classical
  letI : Fact (1 < n) := ⟨by omega⟩
  have hij : i ≠ j := by
    intro h
    subst j
    exact next_ne_self e (he1.trans he.symm)
  fin_cases i <;> fin_cases j <;> norm_num at *
  all_goals simp only [sixEndpointMap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.vecHead, Matrix.vecTail] at he he1
  all_goals first
    | solve | simp [he]
    | exact (cycle_no_reversed_edge hn e _ he he1).elim

theorem concurrence_associated_first_mem (hn : 3 ≤ n) (e f g a b c : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g)
    (hab : remote a b) (hac : remote a c) (hbc : remote b c)
    (hassoc : Associated (concurrencePolynomial e f g) (concurrencePolynomial a b c)) :
    e ∈ ({a, b, c} : Finset (ZMod n)) := by
  classical
  letI : Fact (1 < n) := ⟨by omega⟩
  have hs := polynomialVertexSupport_eq_of_associated
    (concurrencePolynomial_ne_zero hn e f g hef heg hfg)
    (concurrencePolynomial_ne_zero hn a b c hab hac hbc) hassoc
  rw [concurrencePolynomial_vertexSupport e f g hef heg hfg,
    concurrencePolynomial_vertexSupport a b c hab hac hbc] at hs
  have he : e ∈ ({a, a + 1, b, b + 1, c, c + 1} : Finset (ZMod n)) := by
    rw [← hs]
    simp
  have he1 : e + 1 ∈ ({a, a + 1, b, b + 1, c, c + 1} : Finset (ZMod n)) := by
    rw [← hs]
    simp
  obtain ⟨i, hi⟩ := (mem_sixEndpointMap_range a b c e).mpr he
  obtain ⟨j, hj⟩ := (mem_sixEndpointMap_range a b c (e + 1)).mpr he1
  by_contra hmem
  have hgroup : i.val / 2 ≠ j.val / 2 := by
    intro h
    exact hmem (cycle_tail_mem_of_same_slots hn e a b c i j hi.symm hj.symm h)
  exact concurrence_not_associated_of_crossed_slots e f g a b c hab hac hbc
    i j hi.symm hj.symm hgroup hassoc

theorem concurrence_associated_tail_subset (hn : 3 ≤ n) (e f g a b c : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g)
    (hab : remote a b) (hac : remote a c) (hbc : remote b c)
    (hassoc : Associated (concurrencePolynomial e f g) (concurrencePolynomial a b c)) :
    ({e, f, g} : Finset (ZMod n)) ⊆ {a, b, c} := by
  classical
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv | hv <;> subst v
  · exact concurrence_associated_first_mem hn e f g a b c hef heg hfg hab hac hbc hassoc
  · apply concurrence_associated_first_mem hn f g e a b c hfg (remote_symm hef)
      (remote_symm heg) hab hac hbc
    rwa [← concurrencePolynomial_cyclic e f g]
  · apply concurrence_associated_first_mem hn g e f a b c (remote_symm heg)
      (remote_symm hfg) hef hab hac hbc
    rwa [concurrencePolynomial_cyclic g e f]

theorem concurrence_not_associated_of_tail_sets_ne (hn : 3 ≤ n)
    (e f g a b c : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g)
    (hab : remote a b) (hac : remote a c) (hbc : remote b c)
    (hne : ({e, f, g} : Finset (ZMod n)) ≠ {a, b, c}) :
    ¬ Associated (concurrencePolynomial e f g) (concurrencePolynomial a b c) := by
  intro h
  exact hne (Finset.Subset.antisymm
    (concurrence_associated_tail_subset hn e f g a b c hef heg hfg hab hac hbc h)
    (concurrence_associated_tail_subset hn a b c e f g hab hac hbc hef heg hfg h.symm))

theorem areaPolynomial_vertexSupport_card (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (polynomialVertexSupport (areaPolynomial i j k)).card = 3 := by
  classical
  rw [areaPolynomial_vertexSupport i j k hij hik hjk]
  simp [hij, hik, hjk]

theorem concurrencePolynomial_vertexSupport_card [Nontrivial (ZMod n)]
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    (polynomialVertexSupport (concurrencePolynomial e f g)).card = 6 := by
  classical
  rw [concurrencePolynomial_vertexSupport e f g hef heg hfg]
  have hs : Finset.univ.image (sixEndpointMap e f g) =
      ({e, e + 1, f, f + 1, g, g + 1} : Finset (ZMod n)) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact mem_sixEndpointMap_range e f g v
  rw [← hs, Finset.card_image_of_injective _ (sixEndpointMap_injective e f g hef heg hfg)]
  norm_num

theorem area_concurrence_not_associated (hn : 3 ≤ n) (i j k e f g : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    ¬ Associated (areaPolynomial i j k) (concurrencePolynomial e f g) := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro h
  have hs := congrArg Finset.card (polynomialVertexSupport_eq_of_associated
    (areaPolynomial_ne_zero i j k hij hik hjk)
    (concurrencePolynomial_ne_zero hn e f g hef heg hfg) h)
  rw [areaPolynomial_vertexSupport_card i j k hij hik hjk,
    concurrencePolynomial_vertexSupport_card e f g hef heg hfg] at hs
  norm_num at hs

end

end SM
