import ActiveArcRetainedVisitInterior

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalSegments
open RetainedWords PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- The original edge of a retained gap is determined by any actual visit
strictly inside its event interval. -/
theorem retained_visit_interval_outgoingEdge (root : Event q) (z : Corner q hR S root)
    (hz : eventAt q hR S root z.val ≠ terminal q) (v : Visit q)
    (hv0 : (eventOrder q hR.noTriple).lt
      (pairing q S (eventAt q hR S root z.val)) (Sum.inr v))
    (hv1 : (eventOrder q hR.noTriple).lt (Sum.inr v)
      (eventAt q hR S root (nextCorner q hR S root z).val)) :
    outgoingEdge q S (eventAt q hR S root z.val) hz = visitEdge q v := by
  letI := eventOrder q hR.noTriple
  letI : LinearOrder (Fin (n+2) ⊕ Visit q) := eventOrder q hR.noTriple
  let x := eventAt q hR S root z.val
  let y := pairing q S x
  have hy : y≠terminal q := pairing_ne_terminal q S x hz
  have hf := corner_firstReturn q hR S root z
  have hb := firstReturn_prefix_bounded q hR S x hz (cornerGap q hR S root z)
    hf.2.2 (cornerGap q hR S root z) hf.1 le_rfl
  rw [hf.2.1] at hb
  have hvbound : (Sum.inr v : Event q) < Sum.inl (physicalEdge q y hy).succ :=
    lt_of_lt_of_le hv1 hb.2
  have hlo : edgeTag q y≤edgeTag q (Sum.inr v) := by
    rcases (event_lt_iff q hR.noTriple _ _).mp hv0 with h|h
    · exact le_of_lt h
    · exact le_of_eq h.1
  have hhi : edgeTag q (Sum.inr v)<edgeTag q y+1 := by
    by_contra h
    have ha := anchor_le_of_tag_le q hR (physicalEdge q y hy).succ (Sum.inr v)
      (by change edgeTag q y+1≤edgeTag q (Sum.inr v);omega)
    exact (not_le_of_gt hvbound) ha
  apply Fin.ext
  change edgeTag q y = edgeTag q (Sum.inr v)
  omega

/-- A visit interval produces actual ordered endpoints on that visit's
original physical edge; these feed the Regular transversality wrapper. -/
theorem retained_visit_interval_subsegment (root : Event q) (z : Corner q hR S root)
    (hz : eventAt q hR S root z.val ≠ terminal q) (v : Visit q)
    (hv0 : (eventOrder q hR.noTriple).lt
      (pairing q S (eventAt q hR S root z.val)) (Sum.inr v))
    (hv1 : (eventOrder q hR.noTriple).lt (Sum.inr v)
      (eventAt q hR S root (nextCorner q hR S root z).val)) :
    ∃ a b : ℝ, 0≤a ∧ a<b ∧ b≤1 ∧
      eventPoint q (eventAt q hR S root z.val)=affinePoint (q (visitEdge q v).castSucc) (q (visitEdge q v).succ) a ∧
      eventPoint q (eventAt q hR S root (nextCorner q hR S root z).val)=
        affinePoint (q (visitEdge q v).castSucc) (q (visitEdge q v).succ) b := by
  obtain ⟨a,b,ha,hab,hb,hx,hy,_⟩ := retained_side_physical q hR S root z hz
  have he := retained_visit_interval_outgoingEdge q hR S root z hz v hv0 hv1
  rw [he] at hx hy
  exact ⟨a,b,ha,hab,hb,hx,hy⟩

end DirectGLSSW.ActiveArc.PhysicalSegments
