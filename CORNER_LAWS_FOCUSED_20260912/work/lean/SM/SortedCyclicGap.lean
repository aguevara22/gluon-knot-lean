import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Cycle
import Lean.Elab.Tactic.Omega

/-! Consecutive entries of a complete finite sorted cycle have no element
strictly between them in its oriented circular order, including the last/first cut. -/

namespace SM

theorem sorted_next_no_cyclic_between {α : Type*} [LinearOrder α]
    (s : Finset α) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hnext : s.sort.next a ((Finset.mem_sort _).mpr ha) = b)
    (x : α) (hx : x ∈ s) :
    ¬ ((a < x ∧ x < b) ∨ (x < b ∧ b < a) ∨ (b < a ∧ a < x)) := by
  let e := s.orderIsoOfFin rfl
  let ia := e.symm ⟨a, ha⟩
  let ib := e.symm ⟨b, hb⟩
  let ix := e.symm ⟨x, hx⟩
  have hsize : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  let nextIndex : Fin s.card := ⟨(ia.val + 1) % s.card, Nat.mod_lt _ hsize⟩
  have hvalue : b = (e nextIndex).val := by
    rw [← hnext, List.next_eq_getElem]
    simp only [e, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply, Finset.length_sort]
    rfl
  have he : e ib = e nextIndex := by
    apply Subtype.ext
    simpa only [ib, e.apply_symm_apply] using hvalue
  have hindex : ib.val = (ia.val + 1) % s.card := congrArg Fin.val (e.injective he)
  have hlo : a < x → ia.val < ix.val := fun h => e.symm.strictMono h
  have hhi : x < b → ix.val < ib.val := fun h => e.symm.strictMono h
  have hba : b < a → ib.val < ia.val := fun h => e.symm.strictMono h
  have haN := ia.isLt
  have hxN := ix.isLt
  by_cases hcut : ia.val + 1 < s.card
  · rw [Nat.mod_eq_of_lt hcut] at hindex
    rintro (⟨hax, hxb⟩ | ⟨hxb, hba'⟩ | ⟨hba', hax⟩)
    · have h1 := hlo hax; have h2 := hhi hxb; omega
    · have h1 := hhi hxb; have h2 := hba hba'; omega
    · have h1 := hba hba'; have h2 := hlo hax; omega
  · have hlast : ia.val + 1 = s.card := by omega
    rw [hlast, Nat.mod_self] at hindex
    rintro (⟨hax, hxb⟩ | ⟨hxb, hba'⟩ | ⟨hba', hax⟩)
    · have h1 := hlo hax; have h2 := hhi hxb; omega
    · have h1 := hhi hxb; omega
    · have h1 := hlo hax; omega

end SM
