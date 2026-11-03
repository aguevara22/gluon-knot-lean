import ActiveArcRetainedInterval
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalSegments
open RetainedWords PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

theorem affinePoint_subsegment (a b : PlanarPoint ℝ) (s t u : ℝ) :
    affinePoint (affinePoint a b s) (affinePoint a b t) u=
      affinePoint a b (s+(t-s)*u) := by
  ext <;> simp only [affinePoint] <;> ring

/-- A literal visit in the interior of a retained physical side belongs to its
incoming component. The side's physical edge is the proved outgoing branch. -/
theorem retained_side_visit_between (root : Event q) (c : Corner q hR S root)
    (hx : eventAt q hR S root c.val≠terminal q) (v : Visit q)
    (he : visitEdge q v=outgoingEdge q S (eventAt q hR S root c.val) hx)
    (t : ℝ) (ht0 : 0<t) (ht1 : t<1)
    (hp : eventPoint q (Sum.inr v)=affinePoint
      (eventPoint q (eventAt q hR S root c.val))
      (eventPoint q (eventAt q hR S root (nextCorner q hR S root c).val)) t) :
    (eventOrder q hR.noTriple).lt (pairing q S (eventAt q hR S root c.val)) (Sum.inr v) ∧
    (eventOrder q hR.noTriple).lt (Sum.inr v)
      (eventAt q hR S root (nextCorner q hR S root c).val) := by
  letI := eventOrder q hR.noTriple
  let x := eventAt q hR S root c.val
  let y := pairing q S x
  let z := eventAt q hR S root (nextCorner q hR S root c).val
  have hy : y≠terminal q := pairing_ne_terminal q S x hx
  have hf := corner_firstReturn q hR S root c
  have hb := firstReturn_prefix_bounded q hR S x hx (cornerGap q hR S root c)
    hf.2.2 (cornerGap q hR S root c) hf.1 le_rfl
  rw [hf.2.1] at hb
  obtain ⟨b,hab,hb1,hbz,hunique⟩ := bounded_event_physical_spec q hR y z hy hb.1 hb.2
  have hxpoint : eventPoint q x=affinePoint (q (physicalEdge q y hy).castSucc)
      (q (physicalEdge q y hy).succ) (parameter q y) := by
    rw [← pairing_point q S x]
    exact eventPoint_affine q y hy
  have he' : visitEdge q v=physicalEdge q y hy := he
  have hparam : visitParameter q v=parameter q y+(b-parameter q y)*t := by
    apply edge_parameter_unique q hR (physicalEdge q y hy)
    have hvpoint := (visitParameter_spec q v).2.2
    rw [he'] at hvpoint
    have hpoint := hp
    change eventPoint q (Sum.inr v)=affinePoint (eventPoint q x) (eventPoint q z) t at hpoint
    rw [hxpoint,hbz,affinePoint_subsegment] at hpoint
    exact hvpoint.symm.trans hpoint
  have hlow : parameter q y<visitParameter q v := by
    rw [hparam];have := mul_pos (sub_pos.mpr hab) ht0;linarith
  have hupp : visitParameter q v<b := by
    rw [hparam];have := mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht1);nlinarith
  have hetag : edgeTag q (Sum.inr v)=edgeTag q y := congrArg Fin.val he'
  have hv : (eventOrder q hR.noTriple).lt y (Sum.inr v) :=
    (event_lt_iff q hR.noTriple _ _).mpr (Or.inr ⟨hetag.symm,hlow⟩)
  have hvz : (eventOrder q hR.noTriple).lt (Sum.inr v) z := by
    by_cases hzy : edgeTag q z=edgeTag q y
    · have hzn : z≠terminal q := by
        intro hh
        have hyn := edgeTag_lt q y hy
        rw [hh] at hzy
        change n+1=edgeTag q y at hzy
        omega
      have hez : physicalEdge q z hzn=physicalEdge q y hy := Fin.ext hzy
      have hzpoint := eventPoint_affine q z hzn
      rw [hez] at hzpoint
      have hpb := hunique (parameter q z) hzpoint
      apply (event_lt_iff q hR.noTriple _ _).mpr
      exact Or.inr ⟨hetag.trans hzy.symm,by change visitParameter q v<parameter q z;rw [hpb];exact hupp⟩
    · have htag : edgeTag q y<edgeTag q z := by
        rcases (event_lt_iff q hR.noTriple y z).mp hb.1 with hh|hh
        · exact hh
        · exact False.elim (hzy hh.1.symm)
      exact (event_lt_iff q hR.noTriple _ _).mpr (Or.inl (hetag ▸ htag))
  exact ⟨hv,hvz⟩

end DirectGLSSW.ActiveArc.PhysicalSegments
