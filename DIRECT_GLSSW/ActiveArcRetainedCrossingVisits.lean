import ActiveArcRetainedSideVisit

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalSegments
open RetainedWords PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- An actual original crossing lying in a retained side supplies one of its
actual two visits in that side's strict physical event interval. -/
theorem retained_side_crossing_visit (root : Event q) (z : Corner q hR S root)
    (hz : eventAt q hR S root z.val≠terminal q) (c : Crossing q)
    (t : ℝ) (ht0 : 0<t) (ht1 : t<1)
    (hp : crossingPoint q c=affinePoint
      (eventPoint q (eventAt q hR S root z.val))
      (eventPoint q (eventAt q hR S root (nextCorner q hR S root z).val)) t) :
    ∃ b : Bool,
      (eventOrder q hR.noTriple).lt (pairing q S (eventAt q hR S root z.val)) (Sum.inr (c,b)) ∧
      (eventOrder q hR.noTriple).lt (Sum.inr (c,b))
        (eventAt q hR S root (nextCorner q hR S root z).val) := by
  let e := outgoingEdge q S (eventAt q hR S root z.val) hz
  obtain ⟨a,b,ha,hab,hb,hx,hy,_⟩ := retained_side_physical q hR S root z hz
  have hp' : crossingPoint q c=affinePoint (q e.castSucc) (q e.succ) (a+(b-a)*t) := by
    rw [hx,hy,affinePoint_subsegment] at hp
    exact hp
  have hem : edgeInterior q e (crossingPoint q c) := by
    refine ⟨a+(b-a)*t,?_,?_,hp'⟩
    · have := mul_pos (sub_pos.mpr hab) ht0;nlinarith
    · have := mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht1);nlinarith
  have he : e=c.val.1 ∨ e=c.val.2 := by
    by_contra hh
    push_neg at hh
    exact hR.noTriple c.val.1 c.val.2 e (crossingPoint q c)
      (ne_of_lt c.property.1) (Ne.symm hh.2) hh.1
      ⟨(crossingPoint_mem q c).1,(crossingPoint_mem q c).2,hem⟩
  rcases he with he|he
  · refine ⟨false,?_⟩
    exact retained_side_visit_between q hR S root z hz (c,false) he.symm t ht0 ht1 hp
  · refine ⟨true,?_⟩
    exact retained_side_visit_between q hR S root z hz (c,true) he.symm t ht0 ht1 hp

end DirectGLSSW.ActiveArc.PhysicalSegments
