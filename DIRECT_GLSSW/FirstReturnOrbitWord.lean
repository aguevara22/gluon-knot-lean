import DirectGLSSW.OrbitWordPrerequisite
import DirectGLSSW.FiniteFirstReturn
import DirectGLSSW.DaughterPointListFilter

set_option autoImplicit false
namespace DirectGLSSW.FirstReturnOrbitWord
open PermutationOrbits FiniteFirstReturn
noncomputable section
attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [Fintype β]

theorem firstReturn_time_unique (p : Equiv.Perm α) (R : α → Prop) (a : α)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hRd : R ((p ^ d) a)) (hRe : R ((p ^ e) a))
    (hnd : ∀ k : ℕ, 0 < k → k < d → ¬ R ((p ^ k) a))
    (hne : ∀ k : ℕ, 0 < k → k < e → ¬ R ((p ^ k) a)) : d = e := by
  apply le_antisymm
  · exact le_of_not_gt (fun h => hnd e he h hRe)
  · exact le_of_not_gt (fun h => hne d hd h hRd)

theorem orbitEnumeration_iterate (p : Equiv.Perm α) (a : α)
    (i : Fin (Fintype.card (Fibre p (componentOf p a)))) (k : ℕ) :
    (orbitEnumeration p a ((cyclicSuccessorPerm _ ^ k) i)).val =
      (p ^ k) (orbitEnumeration p a i).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,orbitEnumeration_successor]
    simp only [fibrePerm_apply_val,ih,pow_succ',Equiv.Perm.mul_apply]

/-- A genuine first-return injection identifies the actual rooted orbit word
with the filtered parent orbit word, without a component-surjectivity premise. -/
theorem orbitWord_map_eq_filter (p : Equiv.Perm α) (q : Equiv.Perm β)
    (f : β → α) (hf : Function.Injective f)
    (hreturn : ∀ x : β, ∃ d : ℕ, 0 < d ∧ (p ^ d) (f x) = f (q x) ∧
      ∀ k : ℕ, 0 < k → k < d → ¬ Set.range f ((p ^ k) (f x))) (x : β) :
    (orbitWord q x).map f = (orbitWord p (f x)).filter (fun y => decide (y ∈ Set.range f)) := by
  classical
  let C := Fin (Fintype.card (Fibre p (componentOf p (f x))))
  let eventAt : C → α := fun i => (orbitEnumeration p (f x) i).val
  let R : C → Prop := fun i => eventAt i ∈ Set.range f
  let K := {i : C // R i}
  have hC : 0 < Fintype.card (Fibre p (componentOf p (f x))) := Fintype.card_pos
  let c0 : C := ⟨0,hC⟩
  have hat0 : eventAt c0 = f x := by simp [eventAt,c0]
  have hR0 : R c0 := by change eventAt c0 ∈ Set.range f; rw [hat0]; exact ⟨x,rfl⟩
  let z : K := ⟨c0,hR0⟩
  have hK : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨z⟩
  let E : Fin (Fintype.card K) ≃o K := increasingEnumeration K
  let g : Fin (Fintype.card K) → β := fun i => Classical.choose (E i).property
  have hfg (i : Fin (Fintype.card K)) : f (g i) = eventAt (E i).val := Classical.choose_spec (E i).property
  have hat : Function.Injective eventAt := Subtype.val_injective.comp (orbitEnumeration p (f x)).injective
  have hg : Function.Injective g := by
    intro i j hij
    apply E.injective
    apply Subtype.ext
    apply hat
    rw [← hfg i,← hfg j,hij]
  have hE0 : E (⟨0,hK⟩ : Fin (Fintype.card K)) = z := by
    apply Subtype.ext
    apply Fin.ext
    have hle := E.monotone (show (⟨0,hK⟩ : Fin (Fintype.card K)) ≤ E.symm z from Nat.zero_le _)
    rw [E.apply_symm_apply] at hle
    change (E ⟨0,hK⟩).val.val ≤ 0 at hle
    exact Nat.eq_zero_of_le_zero hle
  have hg0 : g ⟨0,hK⟩ = x := by
    apply hf
    rw [hfg,hE0]
    exact hat0
  have hstep (i : Fin (Fintype.card K)) : q (g i) = g (cyclicSuccessor i) := by
    let j := cyclicSuccessor i
    have hnext : orderedCyclicSuccessor K (E i) = E j := by
      rw [orderedCyclicSuccessor_apply]
      simp only [E,OrderIso.symm_apply_apply,j]
    have hcanonical := orderedSubtype_firstReturn R (E i)
    dsimp only at hcanonical
    rw [hnext] at hcanonical
    rcases hcanonical with ⟨hd,_,hreach,hno⟩
    let d := forwardGap (E i).val (E j).val
    have hdreach : (p ^ d) (f (g i)) = f (g j) := by
      rw [hfg i,hfg j]
      exact (orbitEnumeration_iterate p (f x) (E i).val d).symm.trans (congrArg eventAt hreach)
    have hdno : ∀ k : ℕ, 0 < k → k < d → ¬ Set.range f ((p ^ k) (f (g i))) := by
      intro k hk0 hkd hkR
      apply hno k hk0 hkd
      change eventAt ((cyclicSuccessorPerm _ ^ k) (E i).val) ∈ Set.range f
      rw [show eventAt ((cyclicSuccessorPerm _ ^ k) (E i).val) = (p ^ k) (eventAt (E i).val) from
        orbitEnumeration_iterate p (f x) (E i).val k]
      rw [← hfg i]
      exact hkR
    obtain ⟨e,he,hereach,heno⟩ := hreturn (g i)
    have hde : d=e := firstReturn_time_unique p (Set.range f) (f (g i)) hd he
      (by rw [hdreach]; exact ⟨g j,rfl⟩) (by rw [hereach]; exact ⟨q (g i),rfl⟩) hdno heno
    apply hf
    rw [← hereach,← hde,hdreach]
  have hword := orbitWord_eq_of_injective_cyclicSuccessor q hK g hg hstep
  rw [hg0] at hword
  have hcoords : List.ofFn (fun i : Fin (Fintype.card K) => (E i).val) =
      (List.ofFn (fun i : C => i)).filter (fun i => decide (R i)) := by
    have hs1 : (List.ofFn (fun i : Fin (Fintype.card K) => (E i).val)).Sorted (· < ·) :=
      List.sorted_lt_ofFn_iff.mpr E.strictMono
    have hs2 : ((List.ofFn (fun i : C => i)).filter (fun i => decide (R i))).Sorted (· < ·) :=
      (List.sorted_lt_ofFn_iff.mpr strictMono_id).filter _
    apply List.Sorted.eq_of_mem_iff hs1 hs2
    intro i
    constructor
    · intro hi
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
      have hRi : R i := hj ▸ (E j).property
      exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,by simpa using hRi⟩
    · intro hi
      obtain ⟨_,hi⟩ := List.mem_filter.mp hi
      have hRi : R i := by simpa using hi
      exact List.mem_ofFn.mpr ⟨E.symm ⟨i,hRi⟩,by simp⟩
  calc
    (orbitWord q x).map f = List.ofFn (fun i => eventAt (E i).val) := by
      rw [hword,List.map_ofFn]
      congr 1
      funext i
      exact hfg i
    _ = ((List.ofFn (fun i : C => i)).filter (fun i => decide (R i))).map eventAt := by
      rw [← hcoords,List.map_ofFn]
      rfl
    _ = (orbitWord p (f x)).filter (fun y => decide (y ∈ Set.range f)) := by
      exact (DaughterPointListFilter.map_filter_comp eventAt (fun y => decide (y ∈ Set.range f))
        (List.ofFn (fun i : C => i))).trans (by simp only [List.map_ofFn]; rfl)

theorem sameCycle_iff (p : Equiv.Perm α) (q : Equiv.Perm β)
    (f : β → α) (hf : Function.Injective f)
    (hreturn : ∀ x : β, ∃ d : ℕ, 0 < d ∧ (p ^ d) (f x) = f (q x) ∧
      ∀ k : ℕ, 0 < k → k < d → ¬ Set.range f ((p ^ k) (f x))) (x y : β) :
    q.SameCycle x y ↔ p.SameCycle (f x) (f y) := by
  have hw := orbitWord_map_eq_filter p q f hf hreturn x
  constructor
  · intro h
    have hm : f y ∈ (orbitWord q x).map f :=
      List.mem_map.mpr ⟨y,(mem_orbitWord_iff q x y).mpr h,rfl⟩
    rw [hw] at hm
    exact (mem_orbitWord_iff p (f x) (f y)).mp (List.mem_filter.mp hm).1
  · intro h
    have hm : f y ∈ (orbitWord p (f x)).filter (fun a => decide (a ∈ Set.range f)) :=
      List.mem_filter.mpr ⟨(mem_orbitWord_iff p (f x) (f y)).mpr h,by simp⟩
    rw [← hw] at hm
    obtain ⟨z,hz,hzy⟩ := List.mem_map.mp hm
    have hz' : z=y := hf hzy
    subst z
    exact (mem_orbitWord_iff q x y).mp hz





end
end DirectGLSSW.FirstReturnOrbitWord
