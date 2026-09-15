import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega

/-! Absence of an intervening element gives consecutive positions in the
actual sorted finite list. The proof uses its order isomorphism with Fin. -/

namespace SM

theorem sorted_indices_adjacent {α : Type*} [LinearOrder α] (s : Finset α)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hgap : ∀ x ∈ s, ¬ (a < x ∧ x < b)) :
    s.sort.idxOf b = s.sort.idxOf a + 1 := by
  let e := s.orderIsoOfFin rfl
  let ia := e.symm ⟨a, ha⟩
  let ib := e.symm ⟨b, hb⟩
  have horder : ia < ib := e.symm.strictMono hab
  have hstep : ib.val = ia.val + 1 := by
    by_contra hne
    have hlt : ia.val + 1 < ib.val := by
      change ia.val < ib.val at horder
      omega
    let mid : Fin s.card := ⟨ia.val + 1, lt_trans hlt ib.isLt⟩
    have hl : ia < mid := by change ia.val < ia.val + 1; omega
    have hr : mid < ib := hlt
    have hal : a < (e mid).val := by
      have h := e.strictMono hl
      change (e ia).val < (e mid).val at h
      simpa only [ia, e.apply_symm_apply] using h
    have hbr : (e mid).val < b := by
      have h := e.strictMono hr
      change (e mid).val < (e ib).val at h
      simpa only [ib, e.apply_symm_apply] using h
    exact hgap (e mid).val (e mid).property ⟨hal, hbr⟩
  simpa only [ia, ib, e, Finset.orderIsoOfFin_symm_apply] using hstep

end SM
