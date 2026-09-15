import SM.ContactLegs
import SM.FiniteChiStability
import SM.NamedWallPredicates
import SM.GermNeighborhood

/-! Exact finite-segment crossing tests for both vertex-contact legs.
The second separation test is proved at the centre and persists; both
segment interiors are therefore controlled by the full crossing criterion. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

theorem continuousAt_baseLegSideProduct (P : LabelledTuple n) (a l : ZMod n) :
    ContinuousAt (fun Q : LabelledTuple n => baseLegSideProduct Q a l) P :=
  (continuousAt_det (continuous_edge l).continuousAt
    ((continuous_vertex a).continuousAt.sub (continuous_vertex l).continuousAt)).mul
    (continuousAt_det (continuous_edge l).continuousAt
      ((continuous_vertex (a + 1)).continuousAt.sub (continuous_vertex l).continuousAt))

theorem contact_crossing_iff_height (hn : 3 ≤ n) (Q : LabelledTuple n) (hQ : G1 Q)
    {M a : ZMod n} (hsep : ContactSeparated M a) (forward : Bool)
    (hbase : baseLegSideProduct Q a (contactLeg forward M) < 0) :
    IsCrossing Q {a, contactLeg forward M} ↔
      contactHeight (Q a) (Q (a + 1)) (Q M) *
        contactHeight (Q a) (Q (a + 1)) (Q (contactNeighbour forward M)) < 0 := by
  have hr := contactLeg_remote hsep forward
  have hc := (isCrossing_pair Q a (contactLeg forward M) hr).trans
    (crossing_test_iff hn Q hQ a (contactLeg forward M) hr)
  simp only [chi_edge, sign_product_neg_iff] at hc
  rw [hc]
  have hs : det (edge Q (contactLeg forward M)) (Q a - Q (contactLeg forward M)) *
      det (edge Q (contactLeg forward M)) (Q (a + 1) - Q (contactLeg forward M)) < 0 := hbase
  rw [and_iff_left hs]
  cases forward <;> simp [contactLeg, contactNeighbour, contactHeight, edge, mul_comm]

theorem contact_crossing_tests_persist (hn : 3 ≤ n) (P : LabelledTuple n)
    {M a : ZMod n} (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a) :
    ∀ᶠ Q in 𝓝 P, ∀ forward : Bool, G1 Q →
      (IsCrossing Q {a, contactLeg forward M} ↔
        chi Q a (a + 1) M * chi P a (a + 1) (contactNeighbour forward M) = -1) := by
  apply eventually_all.mpr
  intro forward
  have hp := (continuousAt_baseLegSideProduct P a (contactLeg forward M)).eventually
    (isOpen_Iio.mem_nhds (contact_baseLegSideProduct_neg hn hsep hz hm forward))
  have hc := chi_locally_constant_of_ne_zero (contactNeighbour_chi_nonzero hn hsep hz forward)
  filter_upwards [hp, hc] with Q hprod hchi
  intro hQ
  have he : IsCrossing Q {a, contactLeg forward M} ↔
      chi Q a (a + 1) M * chi Q a (a + 1) (contactNeighbour forward M) = -1 :=
    (contact_crossing_iff_height hn Q hQ hsep forward hprod).trans
      (sign_product_neg_iff _ _).symm
  rwa [hchi] at he

namespace WallGerm

theorem vertexEdge_contact_tests (hn : 3 ≤ n) (g : WallGerm n)
    {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ → t.val ≠ 0 →
      ∀ forward : Bool, IsCrossing (g.curve t) {a, contactLeg forward M} ↔
        chi (g.curve t) a (a + 1) M *
          chi g.center a (a + 1) (contactNeighbour forward M) = -1 := by
  have he := g.continuous_curve.continuousAt.eventually
    (contact_crossing_tests_persist hn g.center h.1 h.2.1 h.2.2.2.1)
  apply (g.eventually_center_iff_radius _).mp
  filter_upwards [he] with t ht
  intro htnz forward
  exact ht forward (g.generic_punctured t htnz).1

end WallGerm
end SM
