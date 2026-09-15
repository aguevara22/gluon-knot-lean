import SM.SingleControlCenters
import SM.WallCenterKinds
import SM.CuspCenter
import SM.RegularTriangle

/-! Development: exhaustive cyclic supports and actual regular point-root
geometry. These are derived centre conditions, not assumed simple walls. -/

namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

theorem triple_support_of_adjacent_pair (hn : 3 ≤ n) {s : Finset (ZMod n)}
    (hs : s.card = 3) (a : ZMod n) (ha : a ∈ s) (hb : a + 1 ∈ s) :
    ∃ M : ZMod n, M ≠ a ∧ M ≠ a + 1 ∧ s = contactSupport M a := by
  classical
  letI : Fact (1 < n) := ⟨by omega⟩
  have hcard : ({a, a + 1} : Finset (ZMod n)).card < s.card := by
    rw [hs]
    have hp : ({a, a + 1} : Finset (ZMod n)).card ≤ 2 := by
      calc
        _ ≤ ({a + 1} : Finset (ZMod n)).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    omega
  obtain ⟨M, hM, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hMa : M ≠ a := fun he => hnot (by simp [he])
  have hMb : M ≠ a + 1 := fun he => hnot (by simp [he])
  have hsub : contactSupport M a ⊆ s := by
    intro i hi
    simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> assumption
  have hc : (contactSupport M a).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨(next_ne_self a).symm, hMa.symm, hMb.symm⟩
  exact ⟨M, hMa, hMb, (Finset.eq_of_subset_of_card_le hsub (by rw [hs, hc])).symm⟩

theorem triple_support_cases (hn : 3 ≤ n) {s : Finset (ZMod n)} (hs : s.card = 3) :
    NoConsecutive s ∨ (∃ j, s = turnSupport j) ∨
      ∃ M a, ContactSeparated M a ∧ s = contactSupport M a := by
  classical
  by_cases hno : NoConsecutive s
  · exact Or.inl hno
  · right
    change ¬ (∀ i ∈ s, i + 1 ∉ s) at hno
    push_neg at hno
    obtain ⟨a, ha, hb⟩ := hno
    obtain ⟨M, hMa, hMb, he⟩ := triple_support_of_adjacent_pair hn hs a ha hb
    by_cases hprev : M = a - 1
    · left
      refine ⟨a, he.trans ?_⟩
      subst M
      ext i
      simp only [contactSupport, turnSupport, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · by_cases hnext : M = a + 2
      · left
        refine ⟨a + 1, he.trans ?_⟩
        subst M
        have heq : a + 1 + 1 = a + 2 := by ring
        ext i
        simp only [contactSupport, turnSupport, add_sub_cancel_right, heq,
          Finset.mem_insert, Finset.mem_singleton]
      · exact Or.inr ⟨M, a, ⟨hprev, hMa, hMb, hnext⟩, he⟩

theorem regular_pointZeroTriple_size (hn : 3 ≤ n) {P : LabelledTuple n}
    (hreg : Regular P) {s : Finset (ZMod n)} (hz : PointZeroTriple P s) : 4 ≤ n := by
  by_contra hsmall
  have he : n = 3 := by omega
  subst n
  have hs : s = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ s)
    (by rw [Finset.card_univ, ZMod.card, hz.1])
  have hc := hz.2 0 (by rw [hs]; simp) 1 (by rw [hs]; simp) 2 (by rw [hs]; simp)
  have hd : det (P 1 - P 0) (P 2 - P 0) = 0 := sign_eq_zero_iff.mp hc
  apply regular_triangle_det_ne_zero hreg
  change det (P 1 - P 0) (P 2 - P 1) = 0
  dsimp [det] at hd ⊢
  linear_combination hd

theorem regular_consecutive_strictBetween (hn : 4 ≤ n) {P : LabelledTuple n}
    (hreg : Regular P) {j : ZMod n} (hz : pointZeroTriples P = {turnSupport j}) :
    StrictBetween (P (j - 1)) (P j) (P (j + 1)) := by
  letI : Fact (1 < n) := ⟨by omega⟩
  have hinj := singlePointTriple_vertices_injective hn hz
  have hAB : P (j - 1) ≠ P (j + 1) :=
    fun he => prev_ne_next (by omega) j (hinj he)
  have hc : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) = 0 :=
    sign_eq_zero_iff.mp (singlePointTriple_turn_zero hz)
  have hc' : det (P (j + 1) - P (j - 1)) (P j - P (j - 1)) = 0 := by
    rw [det_swap, hc, neg_zero]
  have hclosed : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      P j = P (j - 1) + t • (P (j + 1) - P (j - 1)) := by
    by_contra hout
    rcases (collinear_exterior_cases hAB hc' hout).1 with hA | hB
    · exact cusp_not_regular (show CuspCase P j true from hA) hreg
    · exact cusp_not_regular (show CuspCase P j false from hB) hreg
  obtain ⟨t, ht0, ht1, ht⟩ := hclosed
  have hzero : t ≠ 0 := by
    intro he
    have hp : P j = P (j - 1) := by simpa [he] using ht
    exact prev_ne_self j (hinj hp).symm
  have hone : t ≠ 1 := by
    intro he
    have hp : P j = P (j + 1) := by simpa [he] using ht
    exact next_ne_self j (hinj hp).symm
  exact ⟨hAB, t, lt_of_le_of_ne ht0 hzero.symm, lt_of_le_of_ne ht1 hone, ht⟩

theorem separated_contact_on_line (hn : 3 ≤ n) {P : LabelledTuple n} {M a : ZMod n}
    (hsep : ContactSeparated M a) (hz : pointZeroTriples P = {contactSupport M a}) :
    ∃ t : ℝ, P M = edgePoint P a t := by
  have hn5 := contactSeparated_size hn hsep
  have hp := singlePointTriple_data hz
  have hc : chi P a (a + 1) M = 0 := hp.2 _ (by simp [contactSupport])
    _ (by simp [contactSupport]) _ (by simp [contactSupport])
  have hd : det (edge P a) (P M - P a) = 0 := sign_eq_zero_iff.mp hc
  let t := planeDot (edge P a) (P M - P a) / planeDot (edge P a) (edge P a)
  have he : P M - P a = t • edge P a :=
    scalar_of_det_zero (singlePointTriple_edge_ne_zero (by omega) hz a) hd
  exact ⟨t, by rw [edgePoint, ← he]; abel⟩

theorem separated_contact_interior_or_exterior (hn : 3 ≤ n) {P : LabelledTuple n}
    {M a : ZMod n} (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    P M ∈ edgeInterior P a ∨ P M ∉ edgeSegment P a := by
  have hn5 := contactSeparated_size hn hsep
  have hinj := singlePointTriple_vertices_injective (by omega) hz
  by_cases hseg : P M ∈ edgeSegment P a
  · left
    obtain ⟨t, ht0, ht1, ht⟩ := hseg
    have hzero : t ≠ 0 := by
      intro he
      have hp : P M = P a := by simpa only [he, edgePoint_zero] using ht
      exact hsep.2.1 (hinj hp)
    have hone : t ≠ 1 := by
      intro he
      have hp : P M = P (a + 1) := by simpa only [he, edgePoint_one] using ht
      exact hsep.2.2.1 (hinj hp)
    exact ⟨t, lt_of_le_of_ne ht0 hzero.symm, lt_of_le_of_ne ht1 hone, ht⟩
  · exact Or.inr hseg

theorem regular_single_point_center_cases (hn : 3 ≤ n) {P : LabelledTuple n}
    (hreg : Regular P) {s : Finset (ZMod n)} (hz : pointZeroTriples P = {s})
    (hc : concurrenceTriples P = ∅) :
    (∃ j, FlatCenterAt P j) ∨ (∃ M a, VertexCenterAt P M a) ∨
      (∃ M a, ExtensionCenterAt P M a) ∨ (∃ i j k, CutCenterAt P i j k) := by
  have hp := singlePointTriple_data hz
  have hn4 := regular_pointZeroTriple_size hn hreg hp
  rcases triple_support_cases hn hp.1 with hcut | hturn | hcontact
  · obtain ⟨i, j, k, hij, hik, hjk, hs⟩ := Finset.card_eq_three.mp hp.1
    right; right; right
    refine ⟨i, j, k, ?_, ?_, hc⟩
    · rwa [← hs]
    · rwa [← hs]
  · obtain ⟨j, hs⟩ := hturn
    have hz' : pointZeroTriples P = {turnSupport j} := by rwa [← hs]
    exact Or.inl ⟨j, hn4, hz', hc, regular_consecutive_strictBetween hn4 hreg hz'⟩
  · obtain ⟨M, a, hsep, hs⟩ := hcontact
    have hz' : pointZeroTriples P = {contactSupport M a} := by rwa [← hs]
    rcases separated_contact_interior_or_exterior hn hsep hz' with hin | hout
    · exact Or.inr (Or.inl ⟨M, a, hsep, hz', hc, hin⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨M, a, hsep, hz', hc, separated_contact_on_line hn hsep hz', hout⟩))

theorem WallGerm.not_cuspAt_of_regular (g : WallGerm n) (hreg : Regular g.center)
    (j : ZMod n) : ¬ g.CuspAt j := by
  intro h
  rcases (g.cusp_cases h).1 with hA | hB
  · exact cusp_not_regular hA hreg
  · exact cusp_not_regular hB hreg

end

end SM

set_option pp.fullNames true
set_option pp.universes false

#check SM.vertex_control_zero_iff
#print axioms SM.vertex_control_zero_iff

#check SM.edge_control_zero_of_concurrence
#print axioms SM.edge_control_zero_of_concurrence

#check SM.pointZeroTriples_eq_singleton_of_unique_vertex_control
#print axioms SM.pointZeroTriples_eq_singleton_of_unique_vertex_control

#check SM.pointZeroTriples_empty_of_vertex_controls_nonzero
#print axioms SM.pointZeroTriples_empty_of_vertex_controls_nonzero

#check SM.concurrenceTriples_empty_of_edge_controls_nonzero
#print axioms SM.concurrenceTriples_empty_of_edge_controls_nonzero

#check SM.concurrenceTriples_nonempty_of_g1_nongeneric
#print axioms SM.concurrenceTriples_nonempty_of_g1_nongeneric

#check SM.concurrenceTriples_eq_singleton_of_unique_active_control
#print axioms SM.concurrenceTriples_eq_singleton_of_unique_active_control

#check SM.ControlCenterSets
#print axioms SM.ControlCenterSets

#check SM.unique_named_control_center_sets
#print axioms SM.unique_named_control_center_sets

#check SM.CurveCubeSubdivision.TimedEventCertificate.center_sets
#print axioms SM.CurveCubeSubdivision.TimedEventCertificate.center_sets

#print SM.ControlCenterSets

open Set MvPolynomial

-- Raw source hypotheses give ONE actual A; every actual nongeneric time has
-- a certificate whose named control determines these exact geometric sets.
example {n : ℕ} (hn : 3 ≤ n)
    (gamma : unitInterval → SM.LabelledTuple n) (hgamma : Continuous gamma)
    (hregular : ∀ t, SM.Regular (gamma t))
    (hfirst : SM.Generic (gamma 0)) (hlast : SM.Generic (gamma 1))
    (delta : ℝ) (hdelta : 0 < delta) :
    letI : NeZero n := ⟨by omega⟩
    ∃ d : SM.CurveCubeSubdivision gamma delta,
      ∃ W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ,
      ∃ A : d.CubeCoordinateApproximation W,
        ∀ t, ¬ SM.Generic (A.path t) →
          ∃ E : SM.CurveCubeSubdivision.TimedEventCertificate A hn t,
            SM.ControlCenterSets E.germ.center E.control := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨d⟩ := SM.nonempty_curveCubeSubdivision hn gamma hgamma hregular hfirst hlast delta hdelta
  obtain ⟨W, A, hJ, _, _⟩ := d.exists_joint_cubeCoordinateApproximation hn
  refine ⟨d, W, A, ?_⟩
  intro t hng
  obtain ⟨E⟩ := A.nonempty_timedEventCertificate hn hJ t hng
  exact ⟨E, E.center_sets hng⟩

-- Existing certificate fields suffice; no extra nongenericness premise is
-- necessary because its actual WallGerm already has a nongeneric centre.
example {n : ℕ} [NeZero n] {gamma : unitInterval → SM.LabelledTuple n} {delta : ℝ}
    {d : SM.CurveCubeSubdivision gamma delta}
    {W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}
    (E : SM.CurveCubeSubdivision.TimedEventCertificate A hn t) :
    SM.ControlCenterSets E.germ.center E.control := by
  apply E.center_sets
  rw [← E.germ_center]
  exact E.germ.center_not_generic

-- This conditional check preserves inactive roots: even if a named edge
-- control vanishes at a Generic tuple, its actual concurrence set is empty.
-- It does not assert existence of such a tuple or treat the zero as an event.
example {n : ℕ} [NeZero n] (P : SM.LabelledTuple n) (hP : SM.Generic P)
    (e : SM.EdgeControlName n)
    (_hz : eval (SM.scalarCoordinates P) (SM.namedControlPolynomial (.inr e)) = 0) :
    SM.concurrenceTriples P = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hp := (SM.mem_concurrenceTriples P s).mp hs
  obtain ⟨i, j, k, hij, hik, hjk, heq⟩ := Finset.card_eq_three.mp hp.1
  obtain ⟨x, hx⟩ := hp.2.2
  apply hP.2
  refine ⟨i, j, k, x, hij, hjk, hik, ?_, ?_, ?_⟩
  all_goals
    apply hx
    rw [heq]
    simp


#check SM.triple_support_of_adjacent_pair
#print axioms SM.triple_support_of_adjacent_pair

#check SM.triple_support_cases
#print axioms SM.triple_support_cases

#check SM.regular_pointZeroTriple_size
#print axioms SM.regular_pointZeroTriple_size

#check SM.regular_consecutive_strictBetween
#print axioms SM.regular_consecutive_strictBetween

#check SM.separated_contact_on_line
#print axioms SM.separated_contact_on_line

#check SM.separated_contact_interior_or_exterior
#print axioms SM.separated_contact_interior_or_exterior

#check SM.regular_single_point_center_cases
#print axioms SM.regular_single_point_center_cases

#check SM.WallGerm.not_cuspAt_of_regular
#print axioms SM.WallGerm.not_cuspAt_of_regular

#print SM.FlatCenterAt
#print SM.VertexCenterAt
#print SM.ExtensionCenterAt
#print SM.CutCenterAt

-- A certificate alone derives nongenericness and Regular at its actual centre.
-- Selecting the vertex-control branch is the only classification case input.
example {n : ℕ} [NeZero n] {gamma : unitInterval → SM.LabelledTuple n} {delta : ℝ}
    {d : SM.CurveCubeSubdivision gamma delta}
    {W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}
    (E : SM.CurveCubeSubdivision.TimedEventCertificate A hn t)
    (v : SM.VertexControlName n) (hv : E.control = .inl v) :
    ((∃ j, SM.FlatCenterAt E.germ.center j) ∨
      (∃ M a, SM.VertexCenterAt E.germ.center M a) ∨
      (∃ M a, SM.ExtensionCenterAt E.germ.center M a) ∨
      (∃ i j k, SM.CutCenterAt E.germ.center i j k)) ∧
      ∀ j, ¬ E.germ.CuspAt j := by
  have hng : ¬ SM.Generic (A.path t) := by
    rw [← E.germ_center]
    exact E.germ.center_not_generic
  have hsets := E.center_sets hng
  rw [hv] at hsets
  change SM.pointZeroTriples E.germ.center = {v.val} ∧
    SM.concurrenceTriples E.germ.center = ∅ at hsets
  have hr : SM.Regular E.germ.center := by rw [E.germ_center]; exact A.regular t
  exact ⟨SM.regular_single_point_center_cases hn hr hsets.1 hsets.2,
    E.germ.not_cuspAt_of_regular hr⟩

-- Full raw-source construction uses ONE A, then classifies each actual
-- point-root event without supplying Simple, a wall type, or transversality.
example {n : ℕ} (hn : 3 ≤ n)
    (gamma : unitInterval → SM.LabelledTuple n) (hgamma : Continuous gamma)
    (hregular : ∀ t, SM.Regular (gamma t))
    (hfirst : SM.Generic (gamma 0)) (hlast : SM.Generic (gamma 1))
    (delta : ℝ) (hdelta : 0 < delta) :
    letI : NeZero n := ⟨by omega⟩
    ∃ d : SM.CurveCubeSubdivision gamma delta,
      ∃ W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ,
      ∃ A : d.CubeCoordinateApproximation W,
        ∀ t, ¬ SM.Generic (A.path t) →
          ∃ E : SM.CurveCubeSubdivision.TimedEventCertificate A hn t,
            (∀ j, ¬ E.germ.CuspAt j) ∧
            ∀ v : SM.VertexControlName n, E.control = .inl v →
              (∃ j, SM.FlatCenterAt E.germ.center j) ∨
              (∃ M a, SM.VertexCenterAt E.germ.center M a) ∨
              (∃ M a, SM.ExtensionCenterAt E.germ.center M a) ∨
              (∃ i j k, SM.CutCenterAt E.germ.center i j k) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨d⟩ := SM.nonempty_curveCubeSubdivision hn gamma hgamma hregular hfirst hlast delta hdelta
  obtain ⟨W, A, hJ, _, _⟩ := d.exists_joint_cubeCoordinateApproximation hn
  refine ⟨d, W, A, ?_⟩
  intro t hng
  obtain ⟨E⟩ := A.nonempty_timedEventCertificate hn hJ t hng
  have hr : SM.Regular E.germ.center := by rw [E.germ_center]; exact A.regular t
  refine ⟨E, E.germ.not_cuspAt_of_regular hr, ?_⟩
  intro v hv
  have hsets := E.center_sets hng
  rw [hv] at hsets
  change SM.pointZeroTriples E.germ.center = {v.val} ∧
    SM.concurrenceTriples E.germ.center = ∅ at hsets
  exact SM.regular_single_point_center_cases hn hr hsets.1 hsets.2

-- No separate single-root or Simple assumption is needed for no-cusp.
example {n : ℕ} [NeZero n] (g : SM.WallGerm n) (hr : SM.Regular g.center) :
    ∀ j, ¬ g.CuspAt j := g.not_cuspAt_of_regular hr

-- The boundary n=3 case is genuinely excluded by Regular, without collision assumptions.
example (P : SM.LabelledTuple 3) (hr : SM.Regular P) :
    ∀ s, ¬ SM.PointZeroTriple P s := by
  intro s hs
  have := SM.regular_pointZeroTriple_size (by omega) hr hs
  omega

-- The cyclic support crossing the numeric cut is an actual consecutive triple.
example : ({(3 : ZMod 4), 0, 1} : Finset (ZMod 4)) = SM.turnSupport 0 := by
  change ({(3 : ZMod 4), 0, 1} : Finset (ZMod 4)) = {0 - 1, 0, 0 + 1}
  decide
