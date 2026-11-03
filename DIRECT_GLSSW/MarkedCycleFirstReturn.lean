import DirectGLSSW.PermutationOrbits
import DirectGLSSW.OrbitNormalization
import DirectGLSSW.FiniteFirstReturn

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.MarkedCycleGaps
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] (p : Perm α) (mark : ι → α)

/-- Every marked point returns to a mark after a positive number of actual steps. -/
theorem exists_positive_mark_return (m : ι) :
    ∃ n : ℕ, 0<n ∧ ∃ j : ι, (p^n) (mark m)=mark j := by
  obtain ⟨n,hn,_,he⟩:=(Perm.SameCycle.refl p (mark m)).exists_pow_eq''
  exact ⟨n,hn,m,he⟩

/-- Existence and uniqueness of the source's least positive marked return time. -/
theorem exists_unique_positive_firstReturn (m : ι) :
    ∃! n : ℕ, 0<n ∧ (∃ j : ι, (p^n) (mark m)=mark j) ∧
      ∀ k : ℕ, 0<k → k<n → ¬∃ j : ι, (p^k) (mark m)=mark j := by
  let h:=exists_positive_mark_return p mark m
  refine ⟨Nat.find h,?_,?_⟩
  · exact ⟨(Nat.find_spec h).1,(Nat.find_spec h).2,fun k hk hkn hj=>Nat.find_min h hkn ⟨hk,hj⟩⟩
  · intro n hn
    apply Nat.le_antisymm
    · by_contra hle
      exact hn.2.2 (Nat.find h) (Nat.find_spec h).1 (Nat.lt_of_not_ge hle) (Nat.find_spec h).2
    · exact Nat.find_min' h ⟨hn.1,hn.2.1⟩

/-- Literal least positive number of continuation steps reaching any marked point. -/
def gapLength (m : ι) : ℕ := Nat.find (exists_positive_mark_return p mark m)

theorem gapLength_pos (m : ι) : 0<gapLength p mark m :=
  (Nat.find_spec (exists_positive_mark_return p mark m)).1

theorem gapLength_return (m : ι) : ∃ j : ι, (p^gapLength p mark m) (mark m)=mark j :=
  (Nat.find_spec (exists_positive_mark_return p mark m)).2

theorem gapLength_minimal (m : ι) (k : ℕ) (hk : 0<k) (hkl : k<gapLength p mark m) :
    ¬∃ j : ι, (p^k) (mark m)=mark j :=
  fun hj=>Nat.find_min (exists_positive_mark_return p mark m) hkl ⟨hk,hj⟩

theorem gapLength_le_of_return (m : ι) (k : ℕ) (hk : 0<k)
    (hreturn : ∃ j : ι, (p^k) (mark m)=mark j) : gapLength p mark m≤k :=
  Nat.find_min' (exists_positive_mark_return p mark m) ⟨hk,hreturn⟩

theorem gapLength_characterization (m : ι) (n : ℕ) :
    n=gapLength p mark m ↔ 0<n ∧ (∃j : ι,(p^n) (mark m)=mark j) ∧
      ∀k : ℕ,0<k→k<n→¬∃j : ι,(p^k) (mark m)=mark j := by
  constructor
  · rintro rfl;exact ⟨gapLength_pos p mark m,gapLength_return p mark m,gapLength_minimal p mark m⟩
  · intro hn
    apply Nat.le_antisymm
    · by_contra hle
      exact hn.2.2 _ (gapLength_pos p mark m) (Nat.lt_of_not_ge hle) (gapLength_return p mark m)
    · exact gapLength_le_of_return p mark m n hn.1 hn.2.1

theorem gapLength_le_card (hp : p.IsCycleOn Set.univ) (m : ι) :
    gapLength p mark m≤Fintype.card α := by
  have hp' : p.IsCycleOn (Finset.univ : Finset α) := by simpa using hp
  apply gapLength_le_of_return p mark m _ (Fintype.card_pos_iff.mpr ⟨mark m⟩)
  exact ⟨m,by simpa only [Finset.card_univ] using hp'.pow_card_apply (Finset.mem_univ (mark m))⟩

/-- The first-return target has a unique actual marked label when marks are injective. -/
theorem exists_unique_nextLabel (hinj : Function.Injective mark) (m : ι) :
    ∃! j : ι, (p^gapLength p mark m) (mark m)=mark j := by
  obtain ⟨j,hj⟩:=gapLength_return p mark m
  exact ⟨j,hj,fun k hk=>hinj (hk.symm.trans hj)⟩

def nextLabel (hinj : Function.Injective mark) (m : ι) : ι :=
  Classical.choose (exists_unique_nextLabel p mark hinj m)

theorem nextLabel_spec (hinj : Function.Injective mark) (m : ι) :
    (p^gapLength p mark m) (mark m)=mark (nextLabel p mark hinj m) :=
  (Classical.choose_spec (exists_unique_nextLabel p mark hinj m)).1
end DirectGLSSW.MarkedCycleGaps
