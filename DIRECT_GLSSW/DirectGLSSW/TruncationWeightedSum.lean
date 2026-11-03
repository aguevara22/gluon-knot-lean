import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

namespace DirectGLSSW.TruncationWeightedSum

private theorem prod_single_flip
    {C : Type*} [Fintype C] [DecidableEq C]
    (c0 : C) (f g : C → ℚ)
    (h : ∀ c : C, f c = if c = c0 then -g c else g c) :
    (∏ c : C, f c) = -(∏ c : C, g c) := by
  have herase :
      (∏ c ∈ Finset.univ.erase c0, f c) =
        ∏ c ∈ Finset.univ.erase c0, g c := by
    apply Finset.prod_congr rfl
    intro c hc
    rw [h c]
    have hne : c ≠ c0 := Finset.ne_of_mem_erase hc
    simp [hne]
  calc
    (∏ c : C, f c) =
        (∏ c ∈ Finset.univ.erase c0, f c) * f c0 := by
          exact (Finset.prod_erase_mul Finset.univ (fun c : C => f c)
            (Finset.mem_univ c0)).symm
    _ = (∏ c ∈ Finset.univ.erase c0, g c) * (-g c0) := by
          rw [herase, h c0]
          simp
    _ = -((∏ c ∈ Finset.univ.erase c0, g c) * g c0) := by ring
    _ = -(∏ c : C, g c) := by
          rw [← Finset.prod_erase_mul Finset.univ (fun c : C => g c)
            (Finset.mem_univ c0)]

theorem prod_equiv_single_sign_flip
    {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
    (E : C ≃ D) (c0 : C) (w : C → ℚ) (w' : D → ℚ)
    (hweights : ∀ c : C, w' (E c) = if c = c0 then -w c else w c) :
    (∏ d : D, w' d) = -(∏ c : C, w c) := by
  calc
    (∏ d : D, w' d) = ∏ c : C, w' (E c) :=
      (Fintype.prod_equiv E (fun c => w' (E c)) w' (by intro c; rfl)).symm
    _ = -(∏ c : C, w c) := prod_single_flip c0 (fun c => w' (E c)) w hweights

theorem weighted_sum_equiv_single_sign_flip
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (F : A ≃ B)
    (C : A → Type*) (D : B → Type*)
    [∀ a, Fintype (C a)] [∀ b, Fintype (D b)]
    [∀ a, DecidableEq (C a)] [∀ b, DecidableEq (D b)]
    (G : ∀ a : A, C a ≃ D (F a))
    (c0 : ∀ a : A, C a)
    (s : A → ℚ) (t : B → ℚ)
    (w : ∀ a : A, C a → ℚ) (w' : ∀ b : B, D b → ℚ)
    (hsigns : ∀ a : A, t (F a) = s a)
    (hweights : ∀ a : A, ∀ c : C a,
      w' (F a) (G a c) = if c = c0 a then -w a c else w a c) :
    (∑ b : B, t b * (∏ d : D b, w' b d)) =
      -(∑ a : A, s a * (∏ c : C a, w a c)) := by
  have hcomponent (a : A) :
      (∏ d : D (F a), w' (F a) d) = -(∏ c : C a, w a c) := by
    calc
      (∏ d : D (F a), w' (F a) d) =
          ∏ c : C a, w' (F a) (G a c) :=
        (Fintype.prod_equiv (G a)
          (fun c => w' (F a) (G a c)) (w' (F a)) (by intro c; rfl)).symm
      _ = -(∏ c : C a, w a c) :=
        prod_single_flip (c0 a) (fun c => w' (F a) (G a c)) (w a) (hweights a)
  calc
    (∑ b : B, t b * (∏ d : D b, w' b d)) =
        ∑ a : A, t (F a) * (∏ d : D (F a), w' (F a) d) :=
      (Fintype.sum_equiv F
        (fun a => t (F a) * (∏ d : D (F a), w' (F a) d))
        (fun b => t b * (∏ d : D b, w' b d)) (by intro a; rfl)).symm
    _ = ∑ a : A, -(s a * (∏ c : C a, w a c)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsigns a, hcomponent a]
      ring
    _ = -(∑ a : A, s a * (∏ c : C a, w a c)) := by
      rw [Finset.sum_neg_distrib]

end DirectGLSSW.TruncationWeightedSum
