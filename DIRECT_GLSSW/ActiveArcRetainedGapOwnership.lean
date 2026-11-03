import ActiveArcRetainedInterval

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalSegments
open RetainedWords PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

theorem retained_pairing (x : Event q) (hr : retained q S x) :
    retained q S (pairing q S x) := by
  classical
  cases x with
  | inl i => trivial
  | inr v =>
    change retained q S (if v.1∈S then Sum.inr (v.1,!v.2) else Sum.inr v)
    change v.1∈S at hr
    rw [if_pos hr]
    exact hr

theorem retained_interval_not_retained (root : Event q) (c : Corner q hR S root)
    (hx : eventAt q hR S root c.val≠terminal q) (v : Event q)
    (hv : (eventOrder q hR.noTriple).lt (pairing q S (eventAt q hR S root c.val)) v)
    (hvend : (eventOrder q hR.noTriple).lt v
      (eventAt q hR S root (nextCorner q hR S root c).val)) : ¬retained q S v := by
  letI := eventOrder q hR.noTriple
  have hf := corner_firstReturn q hR S root c
  obtain ⟨k,hk,hkd,hkv⟩ := firstReturn_interval_exists q hR S _ hx
    (cornerGap q hR S root c) hf.1 hf.2.2 v hv (by rw [hf.2.1];exact le_of_lt hvend)
  have hklt : k<cornerGap q hR S root c := by
    apply lt_of_le_of_ne hkd
    intro he
    rw [he,hf.2.1] at hkv
    exact (ne_of_lt hvend) hkv.symm
  rw [← hkv]
  exact hf.2.2 k hk hklt

/-- Two retained physical gaps containing the same actual visit have the same
starting incoming event, even before any geometric edge-label comparison. -/
theorem retained_gap_owner_unique (r s : Event q)
    (c : Corner q hR S r) (d : Corner q hR S s)
    (hc : eventAt q hR S r c.val≠terminal q)
    (hd : eventAt q hR S s d.val≠terminal q) (v : Event q)
    (hc0 : (eventOrder q hR.noTriple).lt (pairing q S (eventAt q hR S r c.val)) v)
    (hc1 : (eventOrder q hR.noTriple).lt v (eventAt q hR S r (nextCorner q hR S r c).val))
    (hd0 : (eventOrder q hR.noTriple).lt (pairing q S (eventAt q hR S s d.val)) v)
    (hd1 : (eventOrder q hR.noTriple).lt v (eventAt q hR S s (nextCorner q hR S s d).val)) :
    eventAt q hR S r c.val=eventAt q hR S s d.val := by
  letI := eventOrder q hR.noTriple
  apply (pairing q S).injective
  rcases lt_trichotomy (pairing q S (eventAt q hR S r c.val))
      (pairing q S (eventAt q hR S s d.val)) with h|h|h
  · exact False.elim (retained_interval_not_retained q hR S r c hc _ h (lt_trans hd0 hc1)
      (retained_pairing q S _ d.property))
  · exact h
  · exact False.elim (retained_interval_not_retained q hR S s d hd _ h (lt_trans hc0 hd1)
      (retained_pairing q S _ c.property))

end DirectGLSSW.ActiveArc.PhysicalSegments
