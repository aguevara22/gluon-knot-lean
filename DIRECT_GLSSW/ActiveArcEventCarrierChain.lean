import ActiveArcRightCarrierSecant

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW Cursor RetainedWords Primitive
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (U : Support q hR)

/-- Canonical actual side-carrier chain with a final fresh coordinate-line
label. The final label is not a physical edge or a smoothing site. -/
def eventCarrierChain (i : Fin (openCount q hR U.val)) : Fin (n+1) ⊕ Unit :=
  if h : i.val<openCount q hR U.val-1 then
    Sum.inl (openSideCarrier q hR U.val ⟨i.val,h⟩) else Sum.inr ()

/-- Actual nonalternating side uniqueness extends to the terminal coordinate label. -/
theorem eventCarrierChain_injective : Function.Injective (eventCarrierChain q hR U) := by
  intro i j he
  by_cases hi : i.val<openCount q hR U.val-1
  · by_cases hj : j.val<openCount q hR U.val-1
    · simp only [eventCarrierChain,dif_pos hi,dif_pos hj,Sum.inl.injEq] at he
      have hh := openSideCarrier_injective q hR U.val U.property he
      exact Fin.ext (congrArg (fun z : Fin (openCount q hR U.val-1) => z.val) hh)
    · simp only [eventCarrierChain,dif_pos hi,dif_neg hj,Sum.inl_ne_inr] at he
  · by_cases hj : j.val<openCount q hR U.val-1
    · simp only [eventCarrierChain,dif_neg hi,dif_pos hj,Sum.inr_ne_inl] at he
    · apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega

theorem eventCarrierChain_zero :
    eventCarrierChain q hR U ⟨0,lt_of_lt_of_le (by decide : 0<2) (open_count_ge_two q hR U.val)⟩=
      Sum.inl 0 := by
  have hh : 0<openCount q hR U.val-1 := by have := open_count_ge_two q hR U.val;omega
  simp only [eventCarrierChain,dif_pos hh]
  exact congrArg Sum.inl (openSideCarrier_zero q hR U.val)

/-- The actual crossing uses a right carrier distinct from the first physical side. -/
theorem eventCarrierChain_right_ne_zero (c : Crossing q) (hc : FirstCrossing q c) :
    (Sum.inl c.val.2 : Fin (n+1) ⊕ Unit)≠
      eventCarrierChain q hR U ⟨0,lt_of_lt_of_le (by decide : 0<2) (open_count_ge_two q hR U.val)⟩ := by
  rw [eventCarrierChain_zero]
  intro hh
  have hv := congrArg Fin.val (Sum.inl.inj hh)
  have hlt := c.property.1
  rw [hc.1] at hlt
  change 0<c.val.2.val at hlt
  change c.val.2.val=0 at hv
  omega

/-- Exclusion of c from the actual support rules out repetition of the root
intersection pair at the first retained vertex. If carrier1 were the right
carrier, that vertex would create a forbidden transverse first-side secant. -/
theorem eventCarrierChain_right_ne_one (c : Crossing q) (hc : FirstCrossing q c)
    (hu : c∉U.val) :
    (Sum.inl c.val.2 : Fin (n+1) ⊕ Unit)≠
      eventCarrierChain q hR U ⟨1,lt_of_lt_of_le (by decide : 1<2) (open_count_ge_two q hR U.val)⟩ := by
  intro hh
  by_cases hside : 1<openCount q hR U.val-1
  · simp only [eventCarrierChain,dif_pos hside,Sum.inl.injEq] at hh
    obtain ⟨hk,τ,hcol,htrans,_⟩ := event_right_carrier_secant q hR c hc U hu ⟨1,hside⟩ hh.symm
    have hne := eventOpenWord_transverse_index_ne_one q hR c hc U hu 1 2 (by decide)
      (lt_of_lt_of_le (by decide : 1<2) (open_count_ge_two q hR U.val)) τ hcol htrans
    exact hne rfl
  · simp only [eventCarrierChain,dif_neg hside,Sum.inl_ne_inr] at hh






end DirectGLSSW.ActiveArc.OpenCarrier
