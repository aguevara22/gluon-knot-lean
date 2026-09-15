import SM.UnorderedWallTriples
import SM.ContactLegs
import Mathlib.Data.Sign.Basic
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


namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ} [NeZero n]

theorem real_sign_product_neg {a b : ℝ} (h : a * b < 0) :
    (SignType.sign a : ℝ) * (SignType.sign b : ℝ) < 0 := by
  rw [← SignType.coe_mul, ← sign_mul, sign_eq_neg_one_iff.mpr h]
  norm_num

namespace WallGerm

variable (g : WallGerm n)

theorem signChanges_real_sign {φ : LabelledTuple n → ℝ} (h : g.SignChanges φ) :
    g.SignChanges (fun P => (SignType.sign (φ P) : ℝ)) := by
  obtain ⟨δ, hδ, hδr, hδφ⟩ := h
  exact ⟨δ, hδ, hδr, fun t ht => real_sign_product_neg (hδφ t ht)⟩

theorem vertex_control_signChanges_chi (v : VertexControlName n)
    (h : g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inl v))))
    (i j k : ZMod n) (hs : ({i, j, k} : Finset (ZMod n)) = v.val) :
    g.SignChanges (fun P => (chi P i j k : ℝ)) := by
  have hcard : ({i, j, k} : Finset (ZMod n)).card = 3 := by rw [hs]; exact v.property
  obtain ⟨hij, hik, hjk⟩ := Finset.card_triple_eq_three_iff.mp hcard
  let r := vertexRepresentative v
  have harea : g.SignChanges (fun P => det (P j - P i) (P k - P i)) := by
    rcases triple_value_eq_or_neg areaPolynomial areaPolynomial_cyclic areaPolynomial_swap_last
      r.first r.second r.third i j k hij hik hjk (hs.trans r.support_eq) with hF | hF
    · have he : (fun P : LabelledTuple n => det (P j - P i) (P k - P i)) =
          (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inl v))) := by
        funext P
        rw [← eval_areaPolynomial, hF]
        rfl
      rw [he]
      exact h
    · have he : (fun P : LabelledTuple n => det (P j - P i) (P k - P i)) =
          (fun P => -eval (scalarCoordinates P) (namedControlPolynomial (.inl v))) := by
        funext P
        rw [← eval_areaPolynomial, hF, map_neg]
        rfl
      rw [he]
      exact (g.signChanges_neg _).mpr h
  exact g.signChanges_real_sign harea

/-- The five point-control branches in the source wall dictionary. -/
def PointWallCases : Prop :=
  (∃ j, g.FlatAt j) ∨ (∃ M a, g.BigonAt M a) ∨ (∃ M a, g.SlidingAt M a) ∨
    (∃ M a, g.ExtensionAt M a) ∨ (∃ i j k, g.PureCutAt i j k)

theorem point_control_wall_cases (hn : 3 ≤ n) (hreg : Regular g.center)
    (v : VertexControlName n) (hz : g.pointZeros = {v.val}) (hc : g.concurrences = ∅)
    (h : g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inl v)))) :
    g.PointWallCases := by
  rcases regular_single_point_center_cases hn hreg hz hc with hF | hV | hE | hC
  · obtain ⟨j, hf⟩ := hF
    have hs : ({j - 1, j, j + 1} : Finset (ZMod n)) = v.val :=
      Finset.singleton_inj.mp (hf.2.1.symm.trans hz)
    have hχ := g.vertex_control_signChanges_chi v h (j - 1) j (j + 1) hs
    exact Or.inl ⟨j, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, hχ⟩
  · obtain ⟨M, a, hv⟩ := hV
    have hs : ({a, a + 1, M} : Finset (ZMod n)) = v.val :=
      Finset.singleton_inj.mp (hv.2.1.symm.trans hz)
    have hχ := g.vertex_control_signChanges_chi v h a (a + 1) M hs
    have hV' : g.VertexEdgeAt M a := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hχ⟩
    rcases g.vertexEdge_bigon_or_sliding hV' with hB | hS
    · exact Or.inr (Or.inl ⟨M, a, hB⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨M, a, hS⟩))
  · obtain ⟨M, a, he⟩ := hE
    have hs : ({a, a + 1, M} : Finset (ZMod n)) = v.val :=
      Finset.singleton_inj.mp (he.2.1.symm.trans hz)
    have hχ := g.vertex_control_signChanges_chi v h a (a + 1) M hs
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨M, a, he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2, hχ⟩)))
  · obtain ⟨i, j, k, hc'⟩ := hC
    have hs : ({i, j, k} : Finset (ZMod n)) = v.val :=
      Finset.singleton_inj.mp (hc'.2.1.symm.trans hz)
    have hχ := g.vertex_control_signChanges_chi v h i j k hs
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, k, hc'.1, hc'.2.1, hc'.2.2, hχ⟩)))

theorem pointWallCases_simple (h : g.PointWallCases) : g.Simple := by
  rcases h with ⟨j, hf⟩ | ⟨M, a, hb⟩ | ⟨M, a, hs⟩ | ⟨M, a, he⟩ | ⟨i, j, k, hc⟩
  · exact ⟨.flat, j, hf⟩
  · exact ⟨.vertex, M, a, hb.1⟩
  · exact ⟨.vertex, M, a, hs.1⟩
  · exact ⟨.extension, M, a, he⟩
  · exact ⟨.cut, i, j, k, hc⟩

theorem vertexEdgeAt_heights_nonzero (hn : 3 ≤ n) {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    chi g.center a (a + 1) (M - 1) ≠ 0 ∧ chi g.center a (a + 1) (M + 1) ≠ 0 := by
  exact ⟨contactNeighbour_chi_nonzero hn h.1 h.2.1 false,
    contactNeighbour_chi_nonzero hn h.1 h.2.1 true⟩

end WallGerm

namespace CurveCubeSubdivision.TimedEventCertificate

variable {γ : unitInterval → LabelledTuple n} {δ : ℝ}
    {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}

theorem point_wall_cases (E : TimedEventCertificate A hn t)
    (v : VertexControlName n) (he : E.control = .inl v) :
    E.germ.PointWallCases ∧ E.germ.Simple ∧ ∀ j, ¬ E.germ.CuspAt j := by
  have hng : ¬ Generic (A.path t) := by
    rw [← E.germ_center]
    exact E.germ.center_not_generic
  have hsets := E.center_sets hng
  simp only [he] at hsets
  have hreg : Regular E.germ.center := by rw [E.germ_center]; exact A.regular t
  have hs : E.germ.SignChanges
      (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inl v))) := by
    simpa only [he] using E.signChanges
  have hw := E.germ.point_control_wall_cases hn hreg v hsets.1 hsets.2 hs
  exact ⟨hw, E.germ.pointWallCases_simple hw, E.germ.not_cuspAt_of_regular hreg⟩

end CurveCubeSubdivision.TimedEventCertificate

end

end SM


set_option pp.fullNames true
set_option pp.universes false
#check SM.real_sign_product_neg
#print axioms SM.real_sign_product_neg
#check SM.WallGerm.signChanges_real_sign
#print axioms SM.WallGerm.signChanges_real_sign
#check SM.WallGerm.vertex_control_signChanges_chi
#print axioms SM.WallGerm.vertex_control_signChanges_chi
#check SM.WallGerm.PointWallCases
#print axioms SM.WallGerm.PointWallCases
#check SM.WallGerm.point_control_wall_cases
#print axioms SM.WallGerm.point_control_wall_cases
#check SM.WallGerm.pointWallCases_simple
#print axioms SM.WallGerm.pointWallCases_simple
#check SM.WallGerm.vertexEdgeAt_heights_nonzero
#print axioms SM.WallGerm.vertexEdgeAt_heights_nonzero
#check SM.CurveCubeSubdivision.TimedEventCertificate.point_wall_cases
#print axioms SM.CurveCubeSubdivision.TimedEventCertificate.point_wall_cases
#print SM.WallGerm.PointWallCases
#print SM.WallGerm.BigonAt
#print SM.WallGerm.SlidingAt

open Set MvPolynomial
-- A point event certificate alone supplies all five actual wall branches,
-- simplicity and no cusp at the same actual globally timed germ.
example {n : ℕ} [NeZero n] {gamma : unitInterval → SM.LabelledTuple n} {delta : ℝ}
    {d : SM.CurveCubeSubdivision gamma delta}
    {W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}
    (E : SM.CurveCubeSubdivision.TimedEventCertificate A hn t)
    (v : SM.VertexControlName n) (hv : E.control = .inl v) :
    E.germ.PointWallCases ∧ E.germ.Simple ∧ ∀ j, ¬ E.germ.CuspAt j :=
  E.point_wall_cases v hv

-- Raw source inputs produce ONE approximation and all of its actual point walls.
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
            ∀ v : SM.VertexControlName n, E.control = .inl v →
              E.germ.PointWallCases ∧ E.germ.Simple ∧ ∀ j, ¬ E.germ.CuspAt j := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨d⟩ := SM.nonempty_curveCubeSubdivision hn gamma hgamma hregular hfirst hlast delta hdelta
  obtain ⟨W, A, hJ, _, _⟩ := d.exists_joint_cubeCoordinateApproximation hn
  refine ⟨d, W, A, ?_⟩
  intro t hng
  obtain ⟨E⟩ := A.nonempty_timedEventCertificate hn hJ t hng
  exact ⟨E, E.point_wall_cases⟩

-- Actual sliding heights are opposite, not merely unequal with zero allowed.
example {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : SM.WallGerm n)
    {M a : ZMod n} (hs : g.SlidingAt M a) :
    SM.chi g.center a (a + 1) (M - 1) = -SM.chi g.center a (a + 1) (M + 1) := by
  have hz := g.vertexEdgeAt_heights_nonzero hn hs.1
  have hne := hs.2
  generalize hL : SM.chi g.center a (a + 1) (M - 1) = l at *
  generalize hR : SM.chi g.center a (a + 1) (M + 1) = r at *
  cases l <;> cases r <;> simp_all

-- All six ordered representations of the actual same support use the
-- same sign-change condition, including a reversed orientation.
example {n : ℕ} [NeZero n] (g : SM.WallGerm n) (v : SM.VertexControlName n)
    (h : g.SignChanges (fun P => eval (SM.scalarCoordinates P)
      (SM.namedControlPolynomial (.inl v))))
    (i j k : ZMod n) (hs : ({i,j,k} : Finset (ZMod n)) = v.val) :
    g.SignChanges (fun P => (SM.chi P i k j : ℝ)) := by
  apply g.vertex_control_signChanges_chi v h i k j
  rw [← hs]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
