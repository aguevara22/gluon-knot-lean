import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

/-- A function with one literal two-element fiber and every other literal
fiber of cardinality one has exactly one more domain element than codomain
elements. The cardinality calculation uses the full finite fiber sum and
removes only the distinguished codomain element. -/
theorem fintype_card_eq_add_one_of_fiber_cards {α β : Type*}
    [Fintype α] [Fintype β] (f : α → β) (q0 : β)
    (h0 : (Finset.univ.filter (fun x => f x = q0)).card = 2)
    (hother : ∀ q, q ≠ q0 → (Finset.univ.filter (fun x => f x = q)).card = 1) :
    Fintype.card α = Fintype.card β + 1 := by
  have hsum : Fintype.card α =
      ∑ q : β, (Finset.univ.filter (fun x : α => f x = q)).card :=
    Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
      (fun x _ => Finset.mem_univ (f x))
  have hrest :
      (∑ q ∈ (Finset.univ : Finset β).erase q0,
        (Finset.univ.filter (fun x : α => f x = q)).card) =
      ((Finset.univ : Finset β).erase q0).card := by
    calc
      _ = ∑ q ∈ (Finset.univ : Finset β).erase q0, (1 : ℕ) :=
        Finset.sum_congr rfl (fun q hq => hother q (Finset.mem_erase.mp hq).1)
      _ = _ := by simp
  have herase : ((Finset.univ : Finset β).erase q0).card + 1 = Fintype.card β :=
    Finset.card_erase_add_one (Finset.mem_univ q0)
  calc
    Fintype.card α =
        ∑ q : β, (Finset.univ.filter (fun x : α => f x = q)).card := hsum
    _ = (Finset.univ.filter (fun x : α => f x = q0)).card +
        ∑ q ∈ (Finset.univ : Finset β).erase q0,
          (Finset.univ.filter (fun x : α => f x = q)).card :=
      (Finset.add_sum_erase (Finset.univ : Finset β)
        (fun q => (Finset.univ.filter (fun x : α => f x = q)).card)
        (Finset.mem_univ q0)).symm
    _ = 2 + ((Finset.univ : Finset β).erase q0).card := by rw [h0, hrest]
    _ = (((Finset.univ : Finset β).erase q0).card + 1) + 1 :=
      (Nat.add_comm 2 _).trans (Nat.add_assoc _ 1 1).symm
    _ = Fintype.card β + 1 := congrArg (fun k : ℕ => k + 1) herase

end
end SM.Carrier


#print axioms SM.Carrier.fintype_card_eq_add_one_of_fiber_cards
