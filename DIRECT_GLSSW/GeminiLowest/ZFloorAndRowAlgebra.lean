import LowestRowContract.Contract

set_option autoImplicit false
noncomputable section

namespace GeminiLowest

open DirectGLSSW
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.HOMFLY.Gemini
open DirectGLSSW.HOMFLY.LowestRowContract
open scoped BigOperators

/-! ### Part 1: Monomial Power Rules for `aPower` -/

@[simp] theorem aPower_zero : aPower 0 = 1 :=
  AddMonoidAlgebra.one_def.symm

@[simp] theorem aPower_one : aPower 1 = aMonomial := rfl

@[simp] theorem aPower_neg_one : aPower (-1) = aInvMonomial := rfl

theorem single_mul_single_homfly (a b i j c v : ℤ) :
    AddMonoidAlgebra.single (a, b) c * AddMonoidAlgebra.single (i, j) v =
      (AddMonoidAlgebra.single (a + i, b + j) (c * v) : HOMFLYCoeff) := by
  rw [AddMonoidAlgebra.single_mul_single]
  have hp : ((a, b) : ℤ × ℤ) + (i, j) = (a + i, b + j) := by
    ext <;> simp
  rw [hp]

theorem aPower_add (m n : ℤ) : aPower (m + n) = aPower m * aPower n := by
  change AddMonoidAlgebra.single (m + n, 0) 1 =
    AddMonoidAlgebra.single (m, 0) 1 * AddMonoidAlgebra.single (n, 0) 1
  rw [single_mul_single_homfly, add_zero, one_mul]

theorem aPower_two : aPower 2 = aMonomial * aMonomial := by
  have h := aPower_add 1 1
  norm_num at h
  exact h

theorem aPower_neg_two : aPower (-2) = aInvMonomial * aInvMonomial := by
  have h := aPower_add (-1) (-1)
  norm_num at h
  exact h

@[simp] theorem aPower_mul_neg (n : ℤ) : aPower n * aPower (-n) = 1 := by
  rw [← aPower_add, add_neg_cancel, aPower_zero]

@[simp] theorem aPower_neg_mul (n : ℤ) : aPower (-n) * aPower n = 1 := by
  rw [← aPower_add, neg_add_cancel, aPower_zero]

/-! ### Part 2: Linearity and Singleton Rules for `zRow` -/

@[simp] theorem zRow_zero (n : ℤ) : zRow 0 n = 0 := by
  simp [zRow]

theorem zRow_single (ij : ℤ × ℤ) (v : ℤ) (n : ℤ) :
    zRow (AddMonoidAlgebra.single ij v) n =
      if ij.2 = n then AddMonoidAlgebra.single (ij.1, 0) v else 0 := by
  unfold zRow
  exact Finsupp.sum_single_index (by simp)

theorem zRow_add (P Q : HOMFLYCoeff) (n : ℤ) :
    zRow (P + Q) n = zRow P n + zRow Q n := by
  unfold zRow
  exact Finsupp.sum_add_index'
    (fun _ => by simp)
    (fun _ _ _ => by split_ifs <;> simp [Finsupp.single_add])

theorem zRow_neg (P : HOMFLYCoeff) (n : ℤ) :
    zRow (-P) n = -zRow P n := by
  apply eq_neg_of_add_eq_zero_left
  rw [← zRow_add, neg_add_cancel, zRow_zero]

theorem zRow_sub (P Q : HOMFLYCoeff) (n : ℤ) :
    zRow (P - Q) n = zRow P n - zRow Q n := by
  rw [sub_eq_add_neg, zRow_add, zRow_neg, ← sub_eq_add_neg]

@[simp] theorem zRow_one_zero : zRow 1 0 = 1 := by
  rw [← aPower_zero]
  change zRow (AddMonoidAlgebra.single (0, 0) 1) 0 = AddMonoidAlgebra.single (0, 0) 1
  rw [zRow_single]
  simp

theorem zRow_finset_sum {α : Type*} (S : Finset α) (f : α → HOMFLYCoeff) (n : ℤ) :
    zRow (∑ x ∈ S, f x) n = ∑ x ∈ S, zRow (f x) n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, zRow_add, ih, Finset.sum_insert ha]

theorem zRow_single_mul (a b c : ℤ) (P : HOMFLYCoeff) (n : ℤ) :
    zRow (AddMonoidAlgebra.single (a, b) c * P) n =
      AddMonoidAlgebra.single (a, 0) c * zRow P (n - b) := by
  induction P using Finsupp.induction_linear with
  | zero =>
      simp
  | add f g hf hg =>
      rw [mul_add, zRow_add, hf, hg, zRow_add, mul_add]
  | single ij v =>
      rcases ij with ⟨i, j⟩
      change zRow (AddMonoidAlgebra.single (a, b) c * AddMonoidAlgebra.single (i, j) v) n =
        AddMonoidAlgebra.single (a, 0) c * zRow (AddMonoidAlgebra.single (i, j) v) (n - b)
      rw [single_mul_single_homfly, zRow_single, zRow_single]
      have hcond : (b + j = n) ↔ (j = n - b) := by omega
      simp only [hcond]
      by_cases hj : j = n - b
      · rw [if_pos hj, if_pos hj, single_mul_single_homfly, add_zero]
      · rw [if_neg hj, if_neg hj, mul_zero]

@[simp] theorem zRow_aPower_mul (m : ℤ) (P : HOMFLYCoeff) (n : ℤ) :
    zRow (aPower m * P) n = aPower m * zRow P n := by
  simpa [aPower] using zRow_single_mul m 0 1 P n

@[simp] theorem zRow_aMonomial_mul (P : HOMFLYCoeff) (n : ℤ) :
    zRow (aMonomial * P) n = aMonomial * zRow P n := by
  simpa [aMonomial] using zRow_single_mul 1 0 1 P n

@[simp] theorem zRow_aInvMonomial_mul (P : HOMFLYCoeff) (n : ℤ) :
    zRow (aInvMonomial * P) n = aInvMonomial * zRow P n := by
  simpa [aInvMonomial] using zRow_single_mul (-1) 0 1 P n

@[simp] theorem zRow_zMonomial_mul (P : HOMFLYCoeff) (n : ℤ) :
    zRow (zMonomial * P) n = zRow P (n - 1) := by
  change zRow (AddMonoidAlgebra.single (0, 1) 1 * P) n = zRow P (n - 1)
  rw [zRow_single_mul]
  change aPower 0 * zRow P (n - 1) = zRow P (n - 1)
  rw [aPower_zero, one_mul]

@[simp] theorem zRow_zInvMonomial_mul (P : HOMFLYCoeff) (n : ℤ) :
    zRow (zInvMonomial * P) n = zRow P (n + 1) := by
  change zRow (AddMonoidAlgebra.single (0, -1) 1 * P) n = zRow P (n + 1)
  rw [zRow_single_mul]
  change aPower 0 * zRow P (n - -1) = zRow P (n + 1)
  rw [aPower_zero, one_mul, sub_neg_eq_add]

@[simp] theorem zRow_unlinkFactor_mul (P : HOMFLYCoeff) (n : ℤ) :
    zRow (unlinkFactor * P) n = (aMonomial - aInvMonomial) * zRow P (n + 1) := by
  calc
    zRow (unlinkFactor * P) n =
        zRow (aMonomial * (zInvMonomial * P) - aInvMonomial * (zInvMonomial * P)) n := by
      unfold unlinkFactor
      congr 1
      ring
    _ = aMonomial * zRow P (n + 1) - aInvMonomial * zRow P (n + 1) := by
      rw [zRow_sub, zRow_aMonomial_mul, zRow_aInvMonomial_mul, zRow_zInvMonomial_mul]
    _ = (aMonomial - aInvMonomial) * zRow P (n + 1) := by ring

/-! ### Part 3: Support Characterization of `zFloor` and Multiplicativity of `zRow` -/

theorem zFloor_zero (n : ℤ) : zFloor 0 n := by
  intro i j _
  rfl

theorem zFloor_mono {P : HOMFLYCoeff} {m n : ℤ}
    (hP : zFloor P m) (hnm : n ≤ m) : zFloor P n := by
  intro i j hj
  exact hP i j (lt_of_lt_of_le hj hnm)

theorem zFloor_neg {P : HOMFLYCoeff} {n : ℤ}
    (hP : zFloor P n) : zFloor (-P) n := by
  intro i j hj
  rw [coeff, Finsupp.neg_apply, show P (i, j) = coeff P i j from rfl, hP i j hj, neg_zero]

theorem zFloor_sub {P Q : HOMFLYCoeff} {n : ℤ}
    (hP : zFloor P n) (hQ : zFloor Q n) : zFloor (P - Q) n := by
  rw [sub_eq_add_neg]
  exact zFloor_add P (-Q) n hP (zFloor_neg hQ)

theorem zFloor_aMonomial_mul {P : HOMFLYCoeff} {n : ℤ}
    (hP : zFloor P n) : zFloor (aMonomial * P) n := by
  intro i j hj
  rw [coeff_aMonomial_mul]
  exact hP (i - 1) j hj

theorem zFloor_aInvMonomial_mul {P : HOMFLYCoeff} {n : ℤ}
    (hP : zFloor P n) : zFloor (aInvMonomial * P) n := by
  intro i j hj
  rw [coeff_aInvMonomial_mul]
  exact hP (i + 1) j hj

theorem zFloor_iff_support (P : HOMFLYCoeff) (m : ℤ) :
    zFloor P m ↔ ∀ ij ∈ P.support, m ≤ ij.2 := by
  constructor
  · intro hP ij hij
    rw [Finsupp.mem_support_iff] at hij
    by_contra hlt
    exact hij (hP ij.1 ij.2 (not_le.mp hlt))
  · intro hsup i j hj
    by_contra hne
    have hij : (i, j) ∈ P.support := Finsupp.mem_support_iff.mpr hne
    have hle := hsup (i, j) hij
    dsimp at hle
    omega

theorem zRow_eq_zero_of_lt_zFloor {P : HOMFLYCoeff} {m n : ℤ}
    (hP : zFloor P m) (hnm : n < m) : zRow P n = 0 := by
  unfold zRow Finsupp.sum
  apply Finset.sum_eq_zero
  intro ij hij
  have hle := (zFloor_iff_support P m).mp hP ij hij
  have hne : ij.2 ≠ n := by omega
  dsimp only
  rw [if_neg hne]

theorem zFloor_single_of_le (ij : ℤ × ℤ) (v : ℤ) (m : ℤ) (hm : m ≤ ij.2) :
    zFloor (AddMonoidAlgebra.single ij v) m := by
  rw [zFloor_iff_support]
  intro x hx
  have hEq : x = ij := Finset.mem_singleton.mp (Finsupp.support_single_subset hx)
  subst hEq
  exact hm

theorem zFloor_one : zFloor 1 0 := by
  rw [← aPower_zero]
  exact zFloor_single_of_le (0, 0) 1 0 (le_refl 0)

theorem zFloor_unlinkFactor : zFloor unlinkFactor (-1) := by
  intro i j hj
  rw [unlinkFactor_coeff]
  have h1 : (i, j) ≠ (1, -1) := by
    intro h
    have := congrArg Prod.snd h
    dsimp at this
    omega
  have h2 : (i, j) ≠ (-1, -1) := by
    intro h
    have := congrArg Prod.snd h
    dsimp at this
    omega
  simp [h1, h2]

theorem zFloor_unlinkFactor_pow :
    ∀ k : ℕ, zFloor (unlinkFactor ^ k) (-(k : ℤ))
  | 0 => by
      simpa using zFloor_one
  | k + 1 => by
      rw [pow_succ']
      have h := zFloor_mul unlinkFactor (unlinkFactor ^ k) (-1) (-(k : ℤ))
        zFloor_unlinkFactor (zFloor_unlinkFactor_pow k)
      have hk : (-1 : ℤ) + -(k : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
      rwa [hk] at h

theorem zFloor_positive_skein {Hplus Hminus Hzero : HOMFLYCoeff} {m : ℤ}
    (hminus : zFloor Hminus m)
    (hzero : zFloor Hzero (m - 1))
    (hskein : aMonomial * Hplus - aInvMonomial * Hminus = zMonomial * Hzero) :
    zFloor Hplus m := by
  have hplus_eq : Hplus =
      aInvMonomial * (aInvMonomial * Hminus + zMonomial * Hzero) := by
    have hmul : aMonomial * Hplus = aInvMonomial * Hminus + zMonomial * Hzero :=
      sub_eq_iff_eq_add'.mp hskein
    calc
      Hplus = (aInvMonomial * aMonomial) * Hplus := by
        rw [mul_comm aInvMonomial aMonomial, aMonomial_mul_aInvMonomial, one_mul]
      _ = aInvMonomial * (aMonomial * Hplus) := by ring
      _ = aInvMonomial * (aInvMonomial * Hminus + zMonomial * Hzero) := by rw [hmul]
  rw [hplus_eq]
  apply zFloor_aInvMonomial_mul
  apply zFloor_add
  · exact zFloor_aInvMonomial_mul hminus
  · have hz := zFloor_zmul Hzero (m - 1) hzero
    have hm : m - 1 + 1 = m := by omega
    rwa [hm] at hz

theorem zFloor_negative_skein {Hplus Hminus Hzero : HOMFLYCoeff} {m : ℤ}
    (hplus : zFloor Hplus m)
    (hzero : zFloor Hzero (m - 1))
    (hskein : aMonomial * Hplus - aInvMonomial * Hminus = zMonomial * Hzero) :
    zFloor Hminus m := by
  have hminus_eq : Hminus =
      aMonomial * (aMonomial * Hplus - zMonomial * Hzero) := by
    have hmul : aInvMonomial * Hminus = aMonomial * Hplus - zMonomial * Hzero := by
      calc
        aInvMonomial * Hminus = aMonomial * Hplus - (aMonomial * Hplus - aInvMonomial * Hminus) := by ring
        _ = aMonomial * Hplus - zMonomial * Hzero := by rw [hskein]
    calc
      Hminus = (aMonomial * aInvMonomial) * Hminus := by
        rw [aMonomial_mul_aInvMonomial, one_mul]
      _ = aMonomial * (aInvMonomial * Hminus) := by ring
      _ = aMonomial * (aMonomial * Hplus - zMonomial * Hzero) := by rw [hmul]
  rw [hminus_eq]
  apply zFloor_aMonomial_mul
  apply zFloor_sub
  · exact zFloor_aMonomial_mul hplus
  · have hz := zFloor_zmul Hzero (m - 1) hzero
    have hm : m - 1 + 1 = m := by omega
    rwa [hm] at hz

theorem zRow_mul_of_zFloor {P Q : HOMFLYCoeff} {m n : ℤ}
    (hP : zFloor P m) (hQ : zFloor Q n) :
    zRow (P * Q) (m + n) = zRow P m * zRow Q n := by
  have hP_sum : P = ∑ ij ∈ P.support, AddMonoidAlgebra.single ij (P ij) := by
    exact (Finsupp.sum_single P).symm
  calc
    zRow (P * Q) (m + n) =
        zRow (∑ ij ∈ P.support, (AddMonoidAlgebra.single ij (P ij) * Q)) (m + n) := by
      conv_lhs => rw [hP_sum, Finset.sum_mul]
    _ = ∑ ij ∈ P.support, zRow (AddMonoidAlgebra.single ij (P ij) * Q) (m + n) := by
      rw [zRow_finset_sum]
    _ = ∑ ij ∈ P.support,
        (if ij.2 = m then AddMonoidAlgebra.single (ij.1, 0) (P ij) else 0) * zRow Q n := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hle : m ≤ ij.2 := (zFloor_iff_support P m).mp hP ij hij
      rcases ij with ⟨i, j⟩
      rw [zRow_single_mul]
      dsimp at hle ⊢
      by_cases hjm : j = m
      · subst hjm
        have hsub : j + n - j = n := by omega
        rw [if_pos rfl, hsub]
      · rw [if_neg hjm, zero_mul]
        have hlt : m + n - j < n := by omega
        rw [zRow_eq_zero_of_lt_zFloor hQ hlt, mul_zero]
    _ = (∑ ij ∈ P.support,
        if ij.2 = m then AddMonoidAlgebra.single (ij.1, 0) (P ij) else 0) * zRow Q n := by
      rw [Finset.sum_mul]
    _ = zRow P m * zRow Q n := rfl

theorem zFloor_prod_zero {α : Type*} (S : Finset α) (f : α → HOMFLYCoeff)
    (hf : ∀ x ∈ S, zFloor (f x) 0) :
    zFloor (∏ x ∈ S, f x) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      exact zFloor_one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h := zFloor_mul (f a) (∏ x ∈ s, f x) 0 0
        (hf a (Finset.mem_insert_self a s))
        (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))
      simpa using h

theorem zRow_prod_zero {α : Type*} (S : Finset α) (f : α → HOMFLYCoeff)
    (hf : ∀ x ∈ S, zFloor (f x) 0) :
    zRow (∏ x ∈ S, f x) 0 = ∏ x ∈ S, zRow (f x) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty, zRow_one_zero]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have h_s : zFloor (∏ x ∈ s, f x) 0 :=
        zFloor_prod_zero s f (fun x hx => hf x (Finset.mem_insert_of_mem hx))
      have hmul := zRow_mul_of_zFloor (hf a (Finset.mem_insert_self a s)) h_s
      simpa [ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))] using hmul

theorem zRow_unlinkFactor_pow :
    ∀ k : ℕ, zRow (unlinkFactor ^ k) (-(k : ℤ)) = (aMonomial - aInvMonomial) ^ k
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ', pow_succ', zRow_unlinkFactor_mul]
      have hk : (-((k + 1 : ℕ) : ℤ)) + 1 = -(k : ℤ) := by omega
      rw [hk, zRow_unlinkFactor_pow k]

/-! ### Part 4: Unconditional Proof of `lowest_z_floor` -/

theorem diagramComponentCount_pos_of_nArc_pos (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    0 < diagramComponentCount D := by
  letI : Fintype (diagramComponent D) := componentFintype D.continuation
  unfold diagramComponentCount componentCount
  exact Fintype.card_pos_iff.mpr ⟨componentOf D.continuation ⟨0, hD⟩⟩

private theorem lowest_z_floor_aux (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (T : BasedTraversal D) :
    zFloor (candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) := by
  classical
  have hNorm := candidateEvaluator_isNormalized all_lowerCrossingEvaluatorSkeinIH
  by_cases hdesc : badCrossings T = ∅
  · rw [hNorm.1 D hD T hdesc]
    have hcomp_pos : 0 < diagramComponentCount D := diagramComponentCount_pos_of_nArc_pos D hD
    have hexp : (1 - (diagramComponentCount D : ℤ)) =
        -((diagramComponentCount D - 1 : ℕ) : ℤ) := by omega
    rw [hexp]
    exact zFloor_unlinkFactor_pow (diagramComponentCount D - 1)
  · obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hdesc
    have hsw : zFloor (candidateEvaluator (switchCrossing D c) hD)
        (1 - (diagramComponentCount D : ℤ)) := by
      simpa only [switch_componentCount D c] using
        lowest_z_floor_aux (switchCrossing D c) hD (switchTraversal T c)
    have hsm_raw := lowest_z_floor_aux (smoothCrossing D c)
      (by change 0 < D.nArc + 2; omega) (smoothChildBasedTraversal D c)
    have hsm : zFloor (candidateEvaluator (smoothCrossing D c)
        (by change 0 < D.nArc + 2; omega))
        (1 - (diagramComponentCount D : ℤ) - 1) := by
      by_cases hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)
      · have hcnt := smooth_componentCount_self D c hself
        exact zFloor_mono hsm_raw (by omega)
      · have hcnt := smooth_componentCount_join D c hself
        exact zFloor_mono hsm_raw (by omega)
    have hskein := hNorm.2 D hD c
    cases hs : crossingSign D c with
    | pos =>
        simp only [hs] at hskein
        exact zFloor_positive_skein hsw hsm hskein
    | neg =>
        simp only [hs] at hskein
        exact zFloor_negative_skein hsw hsm hskein
termination_by (D.nCrossing, (badCrossings T).card)
decreasing_by
  · exact Prod.Lex.right _ (by have hdrop := badCrossings_switch_card T c hc; omega)
  · exact Prod.Lex.left _ _ (by have hdrop := smoothCrossing_crossing_count_drop D c; omega)

theorem lowest_z_floor :
    ∀ (D : PLLinkDiagram) (hD : 0 < D.nArc),
      zFloor (candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) := by
  intro D hD
  exact lowest_z_floor_aux D hD (chooseBasedTraversal D)

end GeminiLowest
