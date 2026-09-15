import SM.ContactVisitOrder
import SM.ContactCrossingSides
import SM.GermChiStability
import SM.ContactInteriorCrossings

/-! Full V geometric clause of the named-wall sides lemma. Every local
conclusion holds on one interval. The source's actual persistent central
visits exclude the two closed-segment endpoint contacts. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

structure VertexLocalData (hn : 3 ≤ n) (P Q : LabelledTuple n)
    (M a : ZMod n) (r η : ℝ) : Prop where
  chirotopes : ChirotopesOutsideZerosAgree P Q
  parameter_order : ContactOrderAgrees P Q M a
  windows : ContactParameterWindows P Q M a r η
  visit_windows : G1 Q → ∀ v : Visit Q,
    InContactVisitWindow M a r η v ↔ ContactAffected M a v.1.val
  visit_order : G1 Q → ∀ v w : PersistentContactVisit P M a,
    v.val.2.val = w.val.2.val →
    (visitParameter (contactVisitTransport windows.1 v).val <
        visitParameter (contactVisitTransport windows.1 w).val ↔
      visitParameter v.val < visitParameter w.val)

def VertexSidesData (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) : Prop :=
  Regular g.center ∧
  (∀ c, IsInteriorCrossing g.center c ↔ IsCrossing g.center c ∧ ¬ ContactAffected M a c) ∧
  ({a, M - 1} : Finset (ZMod n)) ≠ {a, M} ∧
  (∀ s t : g.SideParameter,
    VertexCrossingData g.center (g.sideTuple true s).val (g.sideTuple false t).val M a) ∧
  ∃ r η : ℝ, 0 < r ∧ r < 1 ∧ g.center M = edgePoint g.center a r ∧
    0 < η ∧ 4 * η < r ∧ 4 * η < 1 - r ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
      VertexLocalData hn g.center (g.curve t) M a r η

theorem vertex_sides (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n}
    (h : g.VertexEdgeAt M a) : VertexSidesData hn g M a := by
  obtain ⟨hreg, hpairs, hpatterns⟩ := g.vertex_crossing_sides hn h
  obtain ⟨r, hr0, hr1, hr⟩ := h.2.2.2.1
  obtain ⟨η, hη, hηr, hηr1, hw⟩ := contact_parameter_windows hn h.1 h.2.1
    h.2.2.2.1 r hr0 hr1 hr
  refine ⟨hreg, contact_interior_crossing_iff hn h.1 h.2.1 h.2.2.2.1,
    hpairs, hpatterns, r, η, hr0, hr1, hr, hη, hηr, hηr1, ?_⟩
  apply (g.eventually_center_iff_radius _).mp
  have hchi := g.continuous_curve.continuousAt.eventually (outsideZeros_chi_persists g.center)
  have horder := g.continuous_curve.continuousAt.eventually (contact_order_persists hn h.1 h.2.1 h.2.2.1)
  have hwin := g.continuous_curve.continuousAt.eventually hw
  filter_upwards [hchi, horder, hwin] with t hct hot hwt
  exact ⟨hct, hot, hwt, fun hg v => contact_visit_window_iff hn hg hη hwt v,
    fun hg v w he => contact_persistent_visit_order hn h.1 h.2.1 hg hot hwt.1 v w he⟩

end SM
