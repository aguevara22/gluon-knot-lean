import DirectGLSSW.OrbitNormalization

set_option autoImplicit false

universe u

namespace DirectGLSSW

/-- An injective cyclic successor word is exactly the rooted actual orbit word.
This identifies one component fibre only; the ambient permutation may have
other components. -/
theorem orbitWord_eq_of_injective_cyclicSuccessor
    {α : Type u} [Fintype α] (p : Equiv.Perm α) {N : ℕ}
    (hN : 0 < N) (f : Fin N → α)
    (hf : Function.Injective f)
    (hstep : ∀ i, p (f i) = f (DirectGLSSW.cyclicSuccessor i)) :
    DirectGLSSW.PermutationOrbits.orbitWord p
        (f (⟨0, hN⟩ : Fin N)) = List.ofFn f := by
  let root : Fin N := ⟨0, hN⟩
  let cyc : Equiv.Perm (Fin N) := DirectGLSSW.cyclicSuccessorPerm N
  have hiterate : ∀ k : ℕ,
      (p ^ k) (f root) = f ((cyc ^ k) root) := by
    intro k
    induction k with
    | zero => simp [cyc]
    | succ k ih =>
        calc
          (p ^ (k + 1)) (f root) = p ((p ^ k) (f root)) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = p (f ((cyc ^ k) root)) := by rw [ih]
          _ = f (DirectGLSSW.cyclicSuccessor ((cyc ^ k) root)) := hstep _
          _ = f (cyc ((cyc ^ k) root)) := rfl
          _ = f ((cyc ^ (k + 1)) root) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
  have hcoordinate (i : Fin N) :
      (p ^ (i : ℕ)) (f root) = f i := by
    by_cases hi : i.val = 0
    · have hir : i = root := by
        apply Fin.ext
        simpa [root] using hi
      subst i
      simp [root]
    · have hpos : 0 < i.val := by omega
      have hsplit : i.val - 1 + 1 = i.val := by omega
      calc
        (p ^ (i : ℕ)) (f root) = f ((cyc ^ (i : ℕ)) root) := hiterate _
        _ = f (DirectGLSSW.cyclicVertexIndex root (i.val - 1)) := by
          congr 1
          have hcyc : (cyc ^ i.val) root =
              DirectGLSSW.cyclicVertexIndex root (i.val - 1) := by
            conv_lhs => rw [← hsplit]
            exact DirectGLSSW.cyclicSuccessorPerm_pow_succ root (i.val - 1)
          exact hcyc
        _ = f i := by
          congr 1
          apply Fin.ext
          change (root.val + 1 + (i.val - 1)) % N = i.val
          have hroot : root.val = 0 := rfl
          rw [hroot]
          have hval : 0 + 1 + (i.val - 1) = i.val := by omega
          rw [hval, Nat.mod_eq_of_lt i.isLt]
  let F := DirectGLSSW.PermutationOrbits.Fibre p
    (DirectGLSSW.PermutationOrbits.componentOf p (f root))
  let toFibre : Fin N → F := fun i => ⟨f i, by
    rw [← hcoordinate i]
    simp⟩
  have htoFibre : Function.Bijective toFibre := by
    constructor
    · intro i j hij
      apply hf
      exact congrArg Subtype.val hij
    · intro y
      have hcycle : p.SameCycle (f root) y.val :=
        (DirectGLSSW.PermutationOrbits.componentOf_eq_iff p (f root) y.val).mp
          y.property.symm
      obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
      refine ⟨(cyc ^ k) root, ?_⟩
      apply Subtype.ext
      change f ((cyc ^ k) root) = y.val
      calc
        f ((cyc ^ k) root) = (p ^ k) (f root) := (hiterate k).symm
        _ = y.val := hk
  let e : Fin N ≃ F := Equiv.ofBijective toFibre htoFibre
  have hcard : Fintype.card F = N := by
    simpa [F] using (Fintype.card_congr e).symm
  apply List.ext_getElem
  · simpa [F, root, DirectGLSSW.PermutationOrbits.orbitWord_length] using hcard
  · intro i hi hj
    have hiN : i < N := by simpa using hj
    let j : Fin N := ⟨i, hiN⟩
    simpa [DirectGLSSW.PermutationOrbits.orbitWord,
      DirectGLSSW.PermutationOrbits.orbitEnumeration_apply_val] using hcoordinate j

#check orbitWord_eq_of_injective_cyclicSuccessor


end DirectGLSSW











