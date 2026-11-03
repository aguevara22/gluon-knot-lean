import DirectGLSSW.FiniteFirstReturn
import DirectGLSSW.OrbitNormalization
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.OrderCoordinateFirstReturn
open PermutationOrbits FiniteFirstReturn
attribute [local instance] Classical.propDecidable

/-- A strictly ordered subset of one actual orbit carries its genuine first-return permutation. -/
theorem firstReturn_of_coordinate_order
    {α β : Type*} [Fintype α] [Fintype β] [LinearOrder β]
    (p : Equiv.Perm α) (a : α) (f : β → α)
    (hmem : ∀x, componentOf p (f x)=componentOf p a)
    (horder : ∀x y,
      (orbitEnumeration p a).symm ⟨f x,hmem x⟩ <
      (orbitEnumeration p a).symm ⟨f y,hmem y⟩ ↔ x<y) :
    ∀x : β, ∃d : ℕ, 0<d ∧
      (p^d) (f x)= f (orderedCyclicSuccessor β x) ∧
      ∀k : ℕ, 0<k → k<d → (p^k) (f x) ∉ Set.range f := by
  classical
  let N := Fintype.card (Fibre p (componentOf p a))
  let E := orbitEnumeration p a
  let j : β → Fin N := fun x => E.symm ⟨f x,hmem x⟩
  have hj : Function.Injective j := (show StrictMono j from fun x y h => (horder x y).mpr h).injective
  let e : β ≃o {i : Fin N // i ∈ Set.range j} :=
    { toEquiv := Equiv.ofInjective j hj
      map_rel_iff' := by
        intro x y
        change j x ≤ j y ↔ x ≤ y
        exact not_lt.symm.trans ((horder y x).not.trans not_lt) }
  have heval (x : β) : (e x).val=j x := rfl
  have hEf (x : β) : (E (j x)).val=f x := congrArg Subtype.val (E.apply_symm_apply _)
  have hiter (i : Fin N) (k : ℕ) :
      (E ((cyclicSuccessorPerm N^k) i)).val=(p^k) (E i).val := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,orbitEnumeration_successor]
      simp only [fibrePerm_apply_val,pow_succ',Equiv.Perm.mul_apply]
      exact congrArg p ih
  intro x
  let y := orderedCyclicSuccessor β x
  have hn := orderedCyclicSuccessor_naturality β e x
  have hh := orderedSubtype_firstReturn (fun i : Fin N => i ∈ Set.range j) (e x)
  dsimp only at hh
  simp only [orderedCyclicSuccessor_naturality] at hh
  obtain ⟨hd,_,hr,hno⟩ := hh
  let d := forwardGap (e x).val (e y).val
  refine ⟨d,hd,?_,?_⟩
  · have hi := hiter (j x) d
    rw [hEf] at hi
    rw [←hi]
    change (E ((cyclicSuccessorPerm N^d) (e x).val)).val=f y
    rw [hr]
    exact hEf y
  · intro k hk hkd hbad
    obtain ⟨z,hz⟩ := hbad
    apply hno k hk hkd
    refine ⟨z,?_⟩
    apply E.injective
    apply Subtype.ext
    rw [hEf,hiter]
    change f z=(p^k) (E (j x)).val
    rw [hEf]
    exact hz
end DirectGLSSW.OrderCoordinateFirstReturn
