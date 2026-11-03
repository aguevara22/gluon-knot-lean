import Mathlib.Data.List.Rotate

import DirectGLSSW.DaughterFirstReturn
import DirectGLSSW.DaughterPointListFilter

set_option autoImplicit false

namespace DirectGLSSW.DaughterRootRotation

open DirectGLSSW
open DirectGLSSW.DaughterFirstReturn
open DirectGLSSW.PermutationOrbits

theorem filter_rotate_one {α : Type*} (l : List α) (p : α → Bool) :
    (l.rotate 1).filter p ~r l.filter p := by
  cases l with
  | nil => exact List.IsRotated.refl _
  | cons a l =>
      by_cases h : p a
      · simp [List.rotate_cons_succ, List.rotate_zero, List.filter_append, h]
        exact List.isRotated_concat a (l.filter p)
      · simp [List.rotate_cons_succ, List.rotate_zero, List.filter_append, h]
        exact List.IsRotated.refl _

theorem filter_rotate {α : Type*} (l : List α) (p : α → Bool) (n : ℕ) :
    (l.rotate n).filter p ~r l.filter p := by
  induction n with
  | zero => simpa using (List.IsRotated.refl (l.filter p))
  | succ n ih =>
      have heq : l.rotate (n + 1) = (l.rotate n).rotate 1 := by
        rw [List.rotate_rotate]
      rw [heq]
      exact List.IsRotated.trans (filter_rotate_one (l.rotate n) p) ih

theorem listIsRotated_filter {α : Type*} {l l' : List α} (h : l ~r l')
    (p : α → Bool) : l.filter p ~r l'.filter p := by
  obtain ⟨n, rfl⟩ := h
  exact (filter_rotate l p n).symm

theorem orbitWord_isRotated_of_sameCycle {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x y : α) (hxy : p.SameCycle x y) :
    orbitWord p x ~r orbitWord p y := by
  classical
  let c := componentOf p x
  have hcomp : componentOf p x = componentOf p y :=
    (componentOf_eq_iff p x y).2 hxy
  let x₀ : Fibre p c := ⟨x, rfl⟩
  let y₀ : Fibre p c := ⟨y, hcomp.symm⟩
  let q := fibrePerm p c
  have hq : q.IsCycleOn (Finset.univ : Finset (Fibre p c)) := by
    simpa [q] using fibrePerm_isCycleOn p c
  obtain ⟨k, hk, hroot⟩ := hq.exists_pow_eq (Finset.mem_univ x₀)
    (Finset.mem_univ y₀)
  have hrootval : ((q ^ k) x₀).val = y := congrArg Subtype.val hroot
  have hlen : (orbitWord p x).length = (orbitWord p y).length := by
    simp [orbitWord_length, hcomp]
  refine ⟨k, ?_⟩
  apply List.ext_getElem
  · simp [List.length_rotate, hlen]
  · intro i hi₁ hi₂
    have hN : (orbitWord p x).length = Fintype.card (Fibre p c) := by
      simp [orbitWord_length, c]
    have hmpos : 0 < Fintype.card (Fibre p c) :=
      Fintype.card_pos_iff.mpr ⟨x₀⟩
    have hindex : (i + k) % Fintype.card (Fibre p c) < (orbitWord p x).length := by
      rw [hN]
      exact Nat.mod_lt _ hmpos
    have hrot := List.getElem_rotate (orbitWord p x) k i hi₁
    have hrot' : ((orbitWord p x).rotate k)[i] =
        (orbitWord p x)[(i + k) % Fintype.card (Fibre p c)] := by
      simpa only [hN] using hrot
    have hleft : (orbitWord p x)[(i + k) % Fintype.card (Fibre p c)] =
        ((q ^ ((i + k) % Fintype.card (Fibre p c))) x₀).val := by
      simp [orbitWord, q, c, x₀, hindex, orbitEnumeration_apply_val,
        fibrePerm_pow_apply_val]
    have hright : (orbitWord p y)[i] = ((q ^ i) y₀).val := by
      simp [orbitWord, q, c, y₀, hcomp, orbitEnumeration_apply_val,
        fibrePerm_pow_apply_val]
    rw [hrot', hleft, hright]
    have hperiod := hq.pow_apply_eq_pow_apply (Finset.mem_univ x₀)
      (m := (i + k) % Fintype.card (Fibre p c)) (n := i + k)
    have hmod : (i + k) % Fintype.card (Fibre p c) ≡ i + k
        [MOD Fintype.card (Fibre p c)] := by
      exact Nat.mod_modEq _ _
    have hpow := hperiod.mpr hmod
    have hshift : (q ^ i) y₀ = (q ^ (i + k)) x₀ := by
      calc
        (q ^ i) y₀ = (q ^ i) ((q ^ k) x₀) := congrArg (q ^ i) hroot.symm
        _ = ((q ^ i) * (q ^ k)) x₀ := rfl
        _ = (q ^ (i + k)) x₀ := by rw [← pow_add]
    rw [hshift, hpow]

theorem daughterPointList_isRotated_of_sameCycle
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (q : Fin n → PlanarPoint K)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x y : PolygonEvent q)
    (hxy : (smoothingDartPermutation q hG2 S).SameCycle x y) :
    daughterPointList q hG2 S x ~r daughterPointList q hG2 S y := by
  classical
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map]
  have horbit := orbitWord_isRotated_of_sameCycle (smoothingDartPermutation q hG2 S)
    x y hxy
  exact (listIsRotated_filter horbit (fun z => decide (retainedCorner q S z))).map
    (polygonEventPoint q)







end DirectGLSSW.DaughterRootRotation
