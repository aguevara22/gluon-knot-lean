import MarkedCycleNext

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.MarkedCycleGaps
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {α β ι : Type*} [Fintype α] [Fintype β]

private theorem intertwining_pow (p : Perm α) (q : Perm β) (e : α ≃ β)
    (he : ∀ x,e (p x)=q (e x)) (n : ℕ) (x : α) :
    e ((p^n) x)=(q^n) (e x) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',Perm.mul_apply,he,ih]

theorem gapLength_conjugacy (p : Perm α) (q : Perm β) (e : α ≃ β)
    (he : ∀ x,e (p x)=q (e x)) (mark : ι → α) (m : ι) :
    gapLength p mark m=gapLength q (e ∘ mark) m := by
  apply (gapLength_characterization q (e ∘ mark) m _).2
  refine ⟨gapLength_pos p mark m,?_,?_⟩
  · obtain ⟨j,hj⟩:=gapLength_return p mark m
    exact ⟨j,(intertwining_pow p q e he _ _).symm.trans (congrArg e hj)⟩
  · intro k hk hkl ⟨j,hj⟩
    apply gapLength_minimal p mark m k hk hkl
    exact ⟨j,e.injective ((intertwining_pow p q e he k _).trans hj)⟩

theorem next_conjugacy [Fintype ι] (p : Perm α) (q : Perm β) (e : α ≃ β)
    (he : ∀ x,e (p x)=q (e x)) (mark : ι → α) (hinj : Function.Injective mark) :
    next p mark hinj=next q (e ∘ mark) (e.injective.comp hinj) := by
  ext m
  apply (e.injective.comp hinj)
  change e (mark (nextLabel p mark hinj m))=e (mark (nextLabel q (e ∘ mark) (e.injective.comp hinj) m))
  rw [← nextLabel_spec p mark hinj m,intertwining_pow p q e he,
    gapLength_conjugacy p q e he mark m]
  exact nextLabel_spec q (e ∘ mark) (e.injective.comp hinj) m

/-- A mark's least positive return in finite cyclic coordinates is precisely
its successor in the increasing ordered subtype of marked coordinates. -/
theorem next_cyclic_range [Fintype ι] {N : ℕ} (mark : ι → Fin N)
    (hinj : Function.Injective mark) (m : ι) :
    (Equiv.ofInjective mark hinj) (next (cyclicSuccessorPerm N) mark hinj m)=
      orderedCyclicSuccessor {i : Fin N // Set.range mark i} ((Equiv.ofInjective mark hinj) m) := by
  let e:=Equiv.ofInjective mark hinj
  let z:=orderedCyclicSuccessor {i : Fin N // Set.range mark i} (e m)
  let d:=FiniteFirstReturn.forwardGap (e m).val z.val
  have h:=FiniteFirstReturn.orderedSubtype_firstReturn (Set.range mark) (e m)
  have hd : d=gapLength (cyclicSuccessorPerm N) mark m := by
    apply (gapLength_characterization _ _ _ _).2
    refine ⟨h.1,?_,?_⟩
    · refine ⟨e.symm z,?_⟩
      exact h.2.2.1.trans (congrArg Subtype.val (e.apply_symm_apply z)).symm
    · intro k hk hkl ⟨j,hj⟩
      exact h.2.2.2 k hk hkl ⟨j,hj.symm⟩
  apply Subtype.ext
  change mark (nextLabel (cyclicSuccessorPerm N) mark hinj m)=z.val
  rw [← nextLabel_spec (cyclicSuccessorPerm N) mark hinj m,← hd]
  exact h.2.2.1

/-- Rooted coordinate order, without equality of unmarked gap lengths,
determines the complete next-mark permutation. -/
theorem next_cyclic_eq_of_order [Fintype ι] {M N : ℕ}
    (f : ι → Fin M) (g : ι → Fin N) (hf : Function.Injective f) (hg : Function.Injective g)
    (horder : ∀ i j, f i < f j ↔ g i < g j) :
    next (cyclicSuccessorPerm M) f hf=next (cyclicSuccessorPerm N) g hg := by
  let ef : ι ≃ {i : Fin M // Set.range f i}:=Equiv.ofInjective f hf
  let eg : ι ≃ {i : Fin N // Set.range g i}:=Equiv.ofInjective g hg
  let e : {i : Fin M // Set.range f i} ≃o {i : Fin N // Set.range g i} :=
    OrderIso.ofRelIsoLT
      { toEquiv:=ef.symm.trans eg
        map_rel_iff':=by
          intro x y
          change g (ef.symm x)<g (ef.symm y) ↔ x.val<y.val
          rw [← horder]
          have hx : f (ef.symm x)=x.val := congrArg Subtype.val (ef.apply_symm_apply x)
          have hy : f (ef.symm y)=y.val := congrArg Subtype.val (ef.apply_symm_apply y)
          simpa only [Equiv.ofInjective_apply] using (show f (ef.symm x)<f (ef.symm y) ↔ x.val<y.val by rw [hx,hy]) }
  ext m
  apply eg.injective
  have hnat:=orderedCyclicSuccessor_naturality _ e (ef m)
  have hnf:=next_cyclic_range f hf m
  have hng:=next_cyclic_range g hg m
  change (Equiv.ofInjective g hg) (next (cyclicSuccessorPerm M) f hf m)=
    (Equiv.ofInjective g hg) (next (cyclicSuccessorPerm N) g hg m)
  calc
    (Equiv.ofInjective g hg) (next (cyclicSuccessorPerm M) f hf m) =
        e ((Equiv.ofInjective f hf) (next (cyclicSuccessorPerm M) f hf m)) := by
          change eg _ = eg (ef.symm (ef _))
          rw [ef.symm_apply_apply]
    _ = e (orderedCyclicSuccessor {i : Fin M // Set.range f i} ((Equiv.ofInjective f hf) m)) := congrArg e hnf
    _ = orderedCyclicSuccessor {i : Fin N // Set.range g i} (e (ef m)) := hnat.symm
    _ = orderedCyclicSuccessor {i : Fin N // Set.range g i} ((Equiv.ofInjective g hg) m) := by
          apply congrArg (orderedCyclicSuccessor {i : Fin N // Set.range g i})
          change eg (ef.symm (ef m)) = eg m
          rw [ef.symm_apply_apply]
    _ = (Equiv.ofInjective g hg) (next (cyclicSuccessorPerm N) g hg m) := hng.symm


end DirectGLSSW.MarkedCycleGaps

namespace DirectGLSSW.MarkedCycleGaps
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Fintype β]

/-- The full fibre really exhausts a proved single cycle. -/
def fullFibreEquiv (p : Perm α) (hp : p.IsCycleOn Set.univ) (root : α) :
    Fibre p (componentOf p root) ≃ α where
  toFun:=Subtype.val
  invFun x:=⟨x,(componentOf_eq_iff _ _ _).2 (hp.2 (Set.mem_univ x) (Set.mem_univ root))⟩
  left_inv _:=rfl
  right_inv _:=rfl

/-- Actual full-orbit coordinates, starting at the specified root. -/
def fullOrbitRank (p : Perm α) (hp : p.IsCycleOn Set.univ) (root : α) :
    α ≃ Fin (Fintype.card (Fibre p (componentOf p root))) :=
  (fullFibreEquiv p hp root).symm.trans (orbitEnumeration p root).symm

theorem fullOrbitRank_step (p : Perm α) (hp : p.IsCycleOn Set.univ) (root x : α) :
    fullOrbitRank p hp root (p x)=
      cyclicSuccessorPerm _ (fullOrbitRank p hp root x) := by
  apply (orbitEnumeration p root).injective
  rw [orbitEnumeration_successor]
  simp only [fullOrbitRank,Equiv.trans_apply,Equiv.apply_symm_apply]
  change (fullFibreEquiv p hp root).symm (p x)=
    fibrePerm p (componentOf p root) ((fullFibreEquiv p hp root).symm x)
  rfl

theorem next_eq_of_coordinate_order [Fintype ι]
    (p : Perm α) (q : Perm β) {M N : ℕ} (e : α ≃ Fin M) (f : β ≃ Fin N)
    (he : ∀ x,e (p x)=cyclicSuccessorPerm M (e x))
    (hf : ∀ x,f (q x)=cyclicSuccessorPerm N (f x))
    (a : ι → α) (b : ι → β) (ha : Function.Injective a) (hb : Function.Injective b)
    (horder : ∀ i j,e (a i)<e (a j) ↔ f (b i)<f (b j)) :
    next p a ha=next q b hb := by
  rw [next_conjugacy p _ e he a ha,next_conjugacy q _ f hf b hb]
  exact next_cyclic_eq_of_order (e ∘ a) (f ∘ b) (e.injective.comp ha) (f.injective.comp hb) horder
end DirectGLSSW.MarkedCycleGaps
