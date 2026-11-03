import ActiveArcOpenParent
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val=a)

include hR in
/-- The physical parent crossing embedding omits its cut crossing. -/
theorem parentCrossingToOriginal_ne_cut (d : Crossing (parent q c hcut)) :
    parentCrossingToOriginal q c hcut d≠c := by
  intro he
  have hd := parentCrossingToOriginal_inParent q hR c hcut d
  rw [he] at hd
  exact crossing_not_inParent q c hcut hd

include hR in
/-- Every genuine shortened parent has strictly fewer actual self-crossings.
No FirstCrossing, G1, turn or amplitude premise is needed for this decrease. -/
theorem parent_crossing_count_lt :
    Fintype.card (Crossing (parent q c hcut)) < Fintype.card (Crossing q) := by
  classical
  refine Fintype.card_lt_of_injective_of_not_mem (parentCrossingToOriginal q c hcut)
    (parentCrossingToOriginal_injective q c hcut) (b:=c) ?_
  rintro ⟨d,hd⟩
  exact parentCrossingToOriginal_ne_cut q hR c hcut d hd
end DirectGLSSW.ActiveArc.Split
