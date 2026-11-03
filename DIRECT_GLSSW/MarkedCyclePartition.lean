import MarkedCycleFirstReturn
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.MarkedCycleGaps
open Equiv
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] (p : Perm α) (mark : ι → α)

/-- Literal arcs after one mark, including the next marked incoming arc. -/
def gapMap (x : Σ m : ι, Fin (gapLength p mark m)) : α :=
  (p ^ (x.2.val + 1)) (mark x.1)

private theorem pow_cancel_distance (x y : α) (n r : ℕ) (hnr : n ≤ r)
    (h : (p ^ n) x = (p ^ r) y) : (p ^ (r - n)) y = x := by
  apply (p ^ n).injective
  rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hnr]
  exact h.symm

theorem gapMap_injective (hinj : Function.Injective mark) :
    Function.Injective (gapMap p mark) := by
  rintro ⟨m,k⟩ ⟨j,l⟩ h
  change (p ^ (k.val + 1)) (mark m) = (p ^ (l.val + 1)) (mark j) at h
  have hn : k.val + 1 = l.val + 1 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have he := pow_cancel_distance p (mark m) (mark j) _ _ (Nat.le_of_lt hlt) h
      exact gapLength_minimal p mark j (l.val + 1 - (k.val + 1))
        (by omega) (by omega) ⟨m,he⟩
    · have he := pow_cancel_distance p (mark j) (mark m) _ _ (Nat.le_of_lt hgt) h.symm
      exact gapLength_minimal p mark m (k.val + 1 - (l.val + 1))
        (by omega) (by omega) ⟨j,he⟩
  have hm : m = j := hinj ((p ^ (k.val + 1)).injective (by simpa only [← hn] using h))
  subst j
  have hk : k = l := Fin.ext (by omega)
  subst l
  rfl

/-- Every actual arc is reached at a least positive distance from some mark. -/
theorem exists_positive_mark_distance [Nonempty ι] (hp : p.IsCycleOn Set.univ) (x : α) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ι, (p ^ n) (mark m) = x := by
  let m : ι := Classical.choice inferInstance
  have hcycle := hp.2 (Set.mem_univ (mark m)) (Set.mem_univ x)
  obtain ⟨n,hn,_,he⟩ := hcycle.exists_pow_eq''
  exact ⟨n,hn,m,he⟩

theorem gapMap_surjective [Nonempty ι] (hp : p.IsCycleOn Set.univ) :
    Function.Surjective (gapMap p mark) := by
  intro x
  let h := exists_positive_mark_distance p mark hp x
  let n := Nat.find h
  have hn : 0 < n := (Nat.find_spec h).1
  obtain ⟨m,hm⟩ := (Nat.find_spec h).2
  have hnlen : n ≤ gapLength p mark m := by
    by_contra hle
    have hlt : gapLength p mark m < n := Nat.lt_of_not_ge hle
    obtain ⟨j,hj⟩ := gapLength_return p mark m
    have he : (p ^ (n - gapLength p mark m)) (mark j) = x := by
      rw [← hj, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      exact hm
    exact Nat.find_min h (by change n - gapLength p mark m < n; exact Nat.sub_lt hn (gapLength_pos p mark m))
      ⟨by omega,j,he⟩
  refine ⟨⟨m,⟨n-1,by omega⟩⟩,?_⟩
  change (p ^ (n-1+1)) (mark m) = x
  simpa only [Nat.sub_add_cancel hn] using hm

/-- The actual gap partition is a bijection, rather than a supplied partition law. -/
def gapEquiv [Nonempty ι] (hp : p.IsCycleOn Set.univ) (hinj : Function.Injective mark) :
    (Σ m : ι, Fin (gapLength p mark m)) ≃ α :=
  Equiv.ofBijective (gapMap p mark) ⟨gapMap_injective p mark hinj,gapMap_surjective p mark hp⟩

theorem gapEquiv_apply [Nonempty ι] (hp : p.IsCycleOn Set.univ)
    (hinj : Function.Injective mark) (m : ι) (k : Fin (gapLength p mark m)) :
    gapEquiv p mark hp hinj ⟨m,k⟩ = (p ^ (k.val+1)) (mark m) := rfl

end DirectGLSSW.MarkedCycleGaps
