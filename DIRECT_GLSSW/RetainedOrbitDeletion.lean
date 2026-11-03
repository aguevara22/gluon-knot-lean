import DirectGLSSW.OrbitWordPrerequisite
import DirectGLSSW.FiniteFirstReturn

set_option autoImplicit false

namespace DirectGLSSW.RetainedOrbitDeletion

open Equiv
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.FiniteFirstReturn
open scoped Classical

private theorem orderedSuccessor_subtype_firstReturn
    {A : Type*} [LinearOrder A] [Fintype A]
    (R : A → Prop) [DecidablePred R]
    (y : {x : A // R x}) :
    ∃ d : ℕ, 0 < d ∧
      (orderedCyclicSuccessor A ^ d) y.val =
        (orderedCyclicSuccessor {x : A // R x} y).val ∧
      ∀ k : ℕ, 0 < k → k < d →
        ¬ R ((orderedCyclicSuccessor A ^ k) y.val) := by
  classical
  let eA := increasingEnumeration A
  let P : Fin (Fintype.card A) → Prop := fun i => R (eA i)
  let I := {i : Fin (Fintype.card A) // P i}
  let e : {x : A // R x} ≃o I := {
    toFun := fun x => ⟨eA.symm x.val, by simpa [P] using x.property⟩
    invFun := fun i => ⟨eA i.val, i.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact eA.apply_symm_apply x.val
    right_inv := by
      intro i
      apply Subtype.ext
      exact eA.symm_apply_apply i.val
    map_rel_iff' := by
      intro x y
      exact eA.symm.map_rel_iff
  }
  let c : I := e y
  let next := orderedCyclicSuccessor I c
  let d := forwardGap c.val next.val
  have hfr := orderedSubtype_firstReturn P c
  have hfr' : 0 < d ∧ d ≤ Fintype.card A ∧
      (cyclicSuccessorPerm (Fintype.card A) ^ d) c.val = next.val ∧
      ∀ k : ℕ, 0 < k → k < d →
        ¬ P ((cyclicSuccessorPerm (Fintype.card A) ^ k) c.val) := by
    simpa [d, next] using hfr
  refine ⟨d, hfr'.1, ?_, ?_⟩
  · have hpow : (orderedCyclicSuccessor A ^ d) y.val =
        eA ((cyclicSuccessorPerm (Fintype.card A) ^ d) c.val) := by
      simpa [c, e, eA] using orderedCyclicSuccessor_pow_apply A y.val d
    calc
      (orderedCyclicSuccessor A ^ d) y.val =
          eA ((cyclicSuccessorPerm (Fintype.card A) ^ d) c.val) := hpow
      _ = eA next.val := congrArg eA hfr'.2.2.1
      _ = (orderedCyclicSuccessor {x : A // R x} y).val := by
        have hn := orderedCyclicSuccessor_naturality {x : A // R x} e y
        simpa [c, e, eA] using congrArg (fun z : I => eA z.val) hn
  · intro k hk hkd hr
    have hpow : (orderedCyclicSuccessor A ^ k) y.val =
        eA ((cyclicSuccessorPerm (Fintype.card A) ^ k) c.val) := by
      simpa [c, e, eA] using orderedCyclicSuccessor_pow_apply A y.val k
    have hp : P ((cyclicSuccessorPerm (Fintype.card A) ^ k) c.val) := by
      dsimp [P]
      rw [← hpow]
      exact hr
    exact hfr'.2.2.2 k hk hkd hp

private theorem map_filter_comp {α β : Type*} (f : α → β) (p : β → Bool)
    (l : List α) :
    (l.filter (fun a => p (f a))).map f = (l.map f).filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : p (f a) = true <;> simp [List.filter, h, ih]

/-- Deleting the fixed non-retained points from an ambient successor orbit
commutes with the actual restricted pairing and the induced retained-order
successor. The restriction hypothesis records only the pointwise action; the
first-return successor relation is proved here. -/
theorem orbitWord_filter_restrict
    (A : Type*) [LinearOrder A] [Fintype A]
    (R : A → Prop) [DecidablePred R]
    (t : Equiv.Perm A) (u : Equiv.Perm {x : A // R x})
    (hfix : ∀ x : A, ¬ R x → t x = x)
    (hrestriction : ∀ x : {x : A // R x}, (u x).val = t x.val)
    (x : {x : A // R x}) :
    (orbitWord (orderedCyclicSuccessor A * t) x.val).filter
        (fun y => decide (R y)) =
      (orbitWord (orderedCyclicSuccessor {x : A // R x} * u) x).map Subtype.val := by
  classical
  let S := {x : A // R x}
  let p : Equiv.Perm A := orderedCyclicSuccessor A * t
  let q : Equiv.Perm S := orderedCyclicSuccessor S * u
  let M := Fintype.card (Fibre p (componentOf p x.val))
  let f : Fin M → A := fun i => (orbitEnumeration p x.val i).val
  let P : Fin M → Prop := fun i => R (f i)
  let I := {i : Fin M // P i}
  let eI := increasingEnumeration I
  let g : Fin (Fintype.card I) → S := fun i => ⟨f (eI i).val, (eI i).property⟩
  have hM : 0 < M := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨x.val, rfl⟩⟩
  have hfstep (i : Fin M) : f (cyclicSuccessorPerm M i) = p (f i) := by
    simpa [f, p, PermutationOrbits.fibrePerm_apply_val] using
      congrArg Subtype.val (PermutationOrbits.orbitEnumeration_successor p x.val i)
  have hfiter (k : ℕ) (i : Fin M) :
      f ((cyclicSuccessorPerm M ^ k) i) = (p ^ k) (f i) := by
    induction k with
    | zero => rfl
    | succ k ih =>
        calc
          f ((cyclicSuccessorPerm M ^ (k + 1)) i) =
              f (cyclicSuccessorPerm M ((cyclicSuccessorPerm M ^ k) i)) := by
                rw [pow_succ', Equiv.Perm.mul_apply]
          _ = p (f ((cyclicSuccessorPerm M ^ k) i)) := hfstep _
          _ = p ((p ^ k) (f i)) := by rw [ih]
          _ = (p ^ (k + 1)) (f i) := by
                rw [pow_succ', Equiv.Perm.mul_apply]
                rfl
  have hperiod (i : Fin M) : (p ^ M) (f i) = f i := by
    rw [← hfiter M i, cyclicSuccessorPerm_pow_card]
  have hrootP : P (⟨0, hM⟩ : Fin M) := by
    dsimp [P, f]
    simpa using x.property
  let rootFin : Fin M := ⟨0, hM⟩
  let rootI : I := ⟨rootFin, hrootP⟩
  have hIpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨rootI⟩
  have hrootEnum : (eI ⟨0, hIpos⟩ : I) = rootI := by
    have hzero : (⟨0, hIpos⟩ : Fin (Fintype.card I)) ≤ eI.symm rootI := by
      apply Fin.le_iff_val_le_val.mpr
      exact Nat.zero_le _
    have hmin := eI.monotone hzero
    have hmin' : eI ⟨0, hIpos⟩ ≤ rootI := by
      simpa only [OrderIso.apply_symm_apply] using hmin
    apply Subtype.ext
    apply Fin.ext
    have hv : (eI ⟨0, hIpos⟩).val.val ≤ rootFin.val := by
      simpa [rootI] using hmin'
    have hz : (eI ⟨0, hIpos⟩).val.val = 0 := by
      have hv' : (eI ⟨0, hIpos⟩).val.val ≤ 0 := by simpa [rootFin] using hv
      omega
    simpa [rootI, rootFin] using hz
  have hfirst (i : I) :
      ∃ d : ℕ, 0 < d ∧ d ≤ M ∧
        (p ^ d) (f i.val) = q ⟨f i.val, i.property⟩ ∧
        ∀ k : ℕ, 0 < k → k < d → ¬ R ((p ^ k) (f i.val)) := by
    let y : S := ⟨f i.val, i.property⟩
    let z : S := u y
    obtain ⟨d, hd, hreach, hno⟩ := orderedSuccessor_subtype_firstReturn R z
    have htraj : ∀ k : ℕ, 0 < k → k ≤ d →
        (p ^ k) y.val = (orderedCyclicSuccessor A ^ k) z.val := by
      intro k
      induction k with
      | zero => intro hk _; omega
      | succ k ih =>
          intro hk hkle
          by_cases hk0 : k = 0
          · subst k
            change orderedCyclicSuccessor A (t y.val) =
              orderedCyclicSuccessor A z.val
            rw [hrestriction y]
          · have hkpos : 0 < k := by omega
            have hkle : k ≤ d := by omega
            have hprev := ih hkpos hkle
            have hklt : k < d := by omega
            have hfixed : t ((orderedCyclicSuccessor A ^ k) z.val) =
                (orderedCyclicSuccessor A ^ k) z.val := hfix _ (hno k hkpos hklt)
            calc
              (p ^ (k + 1)) y.val = p ((p ^ k) y.val) := by
                rw [pow_succ', Equiv.Perm.mul_apply]
              _ = p ((orderedCyclicSuccessor A ^ k) z.val) := by rw [hprev]
              _ = orderedCyclicSuccessor A ((orderedCyclicSuccessor A ^ k) z.val) := by
                simp [p, Equiv.Perm.mul_apply, hfixed]
              _ = (orderedCyclicSuccessor A ^ (k + 1)) z.val := by
                rw [pow_succ', Equiv.Perm.mul_apply]
    have hreachP : (p ^ d) y.val = q y := by
      calc
        (p ^ d) y.val = (orderedCyclicSuccessor A ^ d) z.val := htraj d hd (by omega)
        _ = (orderedCyclicSuccessor S z).val := hreach
        _ = q y := by rfl
    have hnoP : ∀ k : ℕ, 0 < k → k < d → ¬ R ((p ^ k) y.val) := by
      intro k hk hkd hr
      have htrajk := htraj k hk (by omega)
      exact hno k hk hkd (htrajk ▸ hr)
    have hdM : d ≤ M := by
      by_cases hle : d ≤ M
      · exact hle
      · have hMN : M < d := by omega
        have hbad := hnoP M hM hMN
        rw [hperiod i.val] at hbad
        exact False.elim (hbad i.property)
    exact ⟨d, hd, hdM, hreachP, hnoP⟩
  have hqstep (i : I) :
      q ⟨f i.val, i.property⟩ =
        ⟨f (orderedCyclicSuccessor I i).val,
          (orderedCyclicSuccessor I i).property⟩ := by
    let next := orderedCyclicSuccessor I i
    let d := forwardGap i.val next.val
    have hfr := orderedSubtype_firstReturn P i
    have hfr' : 0 < d ∧ d ≤ M ∧
        (cyclicSuccessorPerm M ^ d) i.val = next.val ∧
        ∀ k : ℕ, 0 < k → k < d →
          ¬ P ((cyclicSuccessorPerm M ^ k) i.val) := by
      simpa [d, next] using hfr
    have hnext : (p ^ d) (f i.val) = f next.val := by
      calc
        (p ^ d) (f i.val) = f ((cyclicSuccessorPerm M ^ d) i.val) := (hfiter d i.val).symm
        _ = f next.val := congrArg f hfr'.2.2.1
    obtain ⟨d', hd'pos, hd'M, hq, hqno⟩ := hfirst i
    have heq : d' = d := by
      by_cases hlt : d' < d
      · have hbad := hfr'.2.2.2 d' hd'pos hlt
        change ¬ R (f ((cyclicSuccessorPerm M ^ d') i.val)) at hbad
        have hret : R ((p ^ d') (f i.val)) := by
          rw [hq]
          exact (q ⟨f i.val, i.property⟩).property
        rw [← hfiter d' i.val] at hret
        exact False.elim (hbad hret)
      · by_cases heq : d' = d
        · exact heq
        · have hgt : d < d' := by omega
          have hbad := hqno d hfr'.1 hgt
          have hret : R ((p ^ d) (f i.val)) := by rw [hnext]; exact next.property
          exact False.elim (hbad hret)
    apply Subtype.ext
    calc
      (q ⟨f i.val, i.property⟩).val = (p ^ d') (f i.val) := hq.symm
      _ = (p ^ d) (f i.val) := by rw [heq]
      _ = f next.val := hnext
  have hsorted1 :
      (List.ofFn (fun i : Fin (Fintype.card I) => (eI i).val)).Sorted (· < ·) := by
    apply List.sorted_lt_ofFn_iff.mpr
    intro i j hij
    exact eI.strictMono hij
  have hsorted2 :
      ((List.ofFn (fun i : Fin M => i)).filter (fun i => decide (P i))).Sorted (· < ·) := by
    exact (List.sorted_lt_ofFn_iff.mpr strictMono_id).filter _
  have hindexList : List.ofFn (fun i : Fin (Fintype.card I) => (eI i).val) =
      (List.ofFn (fun i : Fin M => i)).filter (fun i => decide (P i)) := by
    apply List.Sorted.eq_of_mem_iff hsorted1 hsorted2
    intro i
    constructor
    · intro hi
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      apply List.mem_filter.mpr
      refine ⟨List.mem_ofFn.mpr ⟨(eI j).val, rfl⟩, ?_⟩
      simpa using (eI j).property
    · intro hi
      obtain ⟨_, hPi⟩ := List.mem_filter.mp hi
      have hPi' : P i := by simpa using hPi
      let z : I := ⟨i, hPi'⟩
      apply List.mem_ofFn.mpr
      refine ⟨eI.symm z, ?_⟩
      exact congrArg Subtype.val (eI.apply_symm_apply z)
  have hfiltered :
      (List.ofFn f).filter (fun y => decide (R y)) =
        List.ofFn (fun i : Fin (Fintype.card I) => f (eI i).val) := by
    have hfinMap : List.ofFn f = (List.ofFn (fun i : Fin M => i)).map f := by
      simp [Function.comp_def]
    calc
      (List.ofFn f).filter (fun y => decide (R y)) =
          ((List.ofFn (fun i : Fin M => i)).filter (fun i => decide (P i))).map f := by
            rw [hfinMap]
            exact (map_filter_comp f (fun y => decide (R y))
              (List.ofFn (fun i : Fin M => i))).symm
      _ = (List.ofFn (fun i : Fin (Fintype.card I) => (eI i).val)).map f := by
            rw [← hindexList]
      _ = List.ofFn (fun i : Fin (Fintype.card I) => f (eI i).val) := by
            simp [List.map_ofFn, Function.comp_def]
  have hgroot : g ⟨0, hIpos⟩ = x := by
    apply Subtype.ext
    change (PermutationOrbits.orbitEnumeration p x.val
      (eI ⟨0, hIpos⟩).val).val = x.val
    rw [hrootEnum]
    dsimp [rootI]
    simp [rootFin, PermutationOrbits.orbitEnumeration_zero]
  have hgstep : ∀ i, q (g i) = g (cyclicSuccessor i) := by
    intro i
    have hnat := orderedCyclicSuccessor_naturality (Fin (Fintype.card I)) eI i
    have hnat' := by simpa only [orderedCyclicSuccessor_fin] using hnat
    have hq := hqstep (eI i)
    calc
      q (g i) = ⟨f (orderedCyclicSuccessor I (eI i)).val,
          (orderedCyclicSuccessor I (eI i)).property⟩ := hq
      _ = g (cyclicSuccessor i) := by
        apply Subtype.ext
        exact congrArg (fun z : I => f z.val) hnat'
  have hginj : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg (fun z : S => z.val) hij
    have hfinj : Function.Injective f := by
      intro a b hab
      exact (PermutationOrbits.orbitEnumeration p x.val).injective (Subtype.ext hab)
    have hval' : (eI i).val = (eI j).val := hfinj hval
    have hIeq : eI i = eI j := Subtype.ext hval'
    exact congrArg Fin.val (eI.injective hIeq)
  have hOrbit := orbitWord_eq_of_injective_cyclicSuccessor q hIpos g hginj hgstep
  have hOrbitRoot := congrArg (List.map Subtype.val) hOrbit
  rw [hgroot] at hOrbitRoot
  change (orbitWord p x.val).filter (fun y => decide (R y)) = _
  rw [show orbitWord p x.val = List.ofFn f by rfl, hfiltered]
  simpa [g] using hOrbitRoot.symm

end DirectGLSSW.RetainedOrbitDeletion

