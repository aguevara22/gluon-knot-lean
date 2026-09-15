import SM.WallCenterClassification
import SM.TripleCenter
import SM.GermNeighborhood
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


namespace SM

open MvPolynomial Filter Topology

noncomputable section

variable {n : ℕ} [NeZero n]

theorem concurrenceDet_order_identity (P : LabelledTuple n) (e f k : ZMod n)
    (hef : det (edge P e) (edge P f) ≠ 0) (hek : det (edge P e) (edge P k) ≠ 0) :
    concurrenceDet P e f k = -(edgeParameter P e f - edgeParameter P e k) *
      det (edge P e) (edge P f) * det (edge P e) (edge P k) := by
  have heq : -(edgeParameter P e f - edgeParameter P e k) *
        det (edge P e) (edge P f) * det (edge P e) (edge P k) =
      -det (P f - P e) (edge P f) * det (edge P e) (edge P k) +
        det (P k - P e) (edge P k) * det (edge P e) (edge P f) := by
    dsimp [edgeParameter, cramerFirst]
    field_simp [hef, hek] <;> ring
  rw [heq, concurrenceDet_formula]
  dsimp [edgeLineA, edgeLineB, edgeLineC, edge, det]
  ring

namespace WallGerm

variable (g : WallGerm n)

theorem signChanges_of_nonzero_factor {F ψ χ : LabelledTuple n → ℝ}
    (hF : g.SignChanges F) (hχ : ContinuousAt χ g.center) (hc : χ g.center ≠ 0)
    (hid : ∀ P, χ P ≠ 0 → F P = ψ P * χ P) : g.SignChanges ψ := by
  have hcont : ContinuousAt (fun t : g.Parameter => χ (g.curve t) * χ g.center)
      g.zeroParameter := (hχ.comp (f := g.curve) (x := g.zeroParameter) g.continuous_curve.continuousAt).mul continuousAt_const
  have hcc : 0 < χ g.center * χ g.center := mul_self_pos.mpr hc
  have hev : ∀ᶠ t in 𝓝 g.zeroParameter, 0 < χ (g.curve t) * χ g.center :=
    hcont.eventually (isOpen_Ioi.mem_nhds hcc)
  obtain ⟨η, hη, hηr, hηχ⟩ := (g.eventually_center_iff_radius _).mp hev
  obtain ⟨δ, hδ, hδr, hδF⟩ := hF
  refine ⟨min δ η, lt_min hδ hη, (min_le_left _ _).trans hδr, ?_⟩
  intro t ht
  have htδ := lt_of_lt_of_le ht (min_le_left δ η)
  have htη := lt_of_lt_of_le ht (min_le_right δ η)
  have hp := hηχ (g.sideTime true t) (by simpa [sideTime, abs_of_pos t.property.1] using htη)
  have hm := hηχ (g.sideTime false t) (by simpa [sideTime, abs_of_pos t.property.1] using htη)
  change 0 < χ (g.sideTuple true t).val * χ g.center at hp
  change 0 < χ (g.sideTuple false t).val * χ g.center at hm
  have hpne : χ (g.sideTuple true t).val ≠ 0 := (mul_ne_zero_iff.mp hp.ne').1
  have hmne : χ (g.sideTuple false t).val ≠ 0 := (mul_ne_zero_iff.mp hm.ne').1
  have hprod : 0 < χ (g.sideTuple true t).val * χ (g.sideTuple false t).val := by
    have hh := mul_pos hp hm
    have he : (χ (g.sideTuple true t).val * χ g.center) *
        (χ (g.sideTuple false t).val * χ g.center) =
        (χ (g.sideTuple true t).val * χ (g.sideTuple false t).val) *
          (χ g.center * χ g.center) := by ring
    rw [he] at hh
    exact (mul_pos_iff_of_pos_right hcc).mp hh
  have hh := hδF t htδ
  rw [hid _ hpne, hid _ hmne] at hh
  have he : (ψ (g.sideTuple true t).val * χ (g.sideTuple true t).val) *
      (ψ (g.sideTuple false t).val * χ (g.sideTuple false t).val) =
      (ψ (g.sideTuple true t).val * ψ (g.sideTuple false t).val) *
        (χ (g.sideTuple true t).val * χ (g.sideTuple false t).val) := by ring
  rw [he] at hh
  rcases mul_neg_iff.mp hh with hbad | hgood
  · exact (not_lt_of_gt hprod hbad.2).elim
  · exact hgood.1

theorem edge_control_signChanges_concurrence (v : EdgeControlName n)
    (h : g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inr v))))
    (e f k : ZMod n) (hs : ({e, f, k} : Finset (ZMod n)) = v.val) :
    g.SignChanges (fun P => concurrenceDet P e f k) := by
  have hcard : ({e, f, k} : Finset (ZMod n)).card = 3 := by rw [hs]; exact v.property.1
  obtain ⟨hef, hek, hfk⟩ := Finset.card_triple_eq_three_iff.mp hcard
  let r := edgeRepresentative v
  rcases triple_value_eq_or_neg concurrencePolynomial concurrencePolynomial_cyclic
    concurrencePolynomial_swap_last r.first r.second r.third e f k hef hek hfk
    (hs.trans r.support_eq) with hF | hF
  · have he : (fun P : LabelledTuple n => concurrenceDet P e f k) =
        (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inr v))) := by
      funext P
      rw [← eval_concurrencePolynomial, hF]
      rfl
    rw [he]
    exact h
  · have he : (fun P : LabelledTuple n => concurrenceDet P e f k) =
        (fun P => -eval (scalarCoordinates P) (namedControlPolynomial (.inr v))) := by
      funext P
      rw [← eval_concurrencePolynomial, hF, map_neg]
      rfl
    rw [he]
    exact (g.signChanges_neg _).mpr h

theorem concurrence_signChanges_parameter_order (e f k : ZMod n)
    (hef : det (edge g.center e) (edge g.center f) ≠ 0)
    (hek : det (edge g.center e) (edge g.center k) ≠ 0)
    (h : g.SignChanges (fun P => concurrenceDet P e f k)) :
    g.SignChanges (fun P => edgeParameter P e f - edgeParameter P e k) := by
  let χ : LabelledTuple n → ℝ := fun P =>
    -det (edge P e) (edge P f) * det (edge P e) (edge P k)
  have hχ : ContinuousAt χ g.center :=
    (continuousAt_det (continuous_edge e).continuousAt (continuous_edge f).continuousAt).neg.mul
      (continuousAt_det (continuous_edge e).continuousAt (continuous_edge k).continuousAt)
  have hc : χ g.center ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hef) hek
  apply g.signChanges_of_nonzero_factor h hχ hc
  intro P hP
  have hp : -det (edge P e) (edge P f) ≠ 0 ∧ det (edge P e) (edge P k) ≠ 0 :=
    mul_ne_zero_iff.mp hP
  rw [concurrenceDet_order_identity P e f k (neg_ne_zero.mp hp.1) hp.2]
  dsimp [χ]
  ring

theorem active_edge_control_tripleAt (hn : 3 ≤ n) (v : EdgeControlName n)
    (hz : g.pointZeros = ∅) (hc : g.concurrences = {v.val})
    (h : g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inr v)))) :
    ∃ e f k, ({e, f, k} : Finset (ZMod n)) = v.val ∧ g.TripleAt e f k := by
  let r := edgeRepresentative v
  let e := r.first
  let f := r.second
  let k := r.third
  have hs : ({e, f, k} : Finset (ZMod n)) = v.val := r.support_eq.symm
  have hc' : concurrenceTriples g.center = {{e, f, k}} := by rwa [hs]
  have h1 : G1 g.center := (g.pointZeros_empty_iff).mp hz
  obtain ⟨hremEF, hremFK, hremEK, q, hqE, hqF, hqK⟩ := uniqueTriple_data hc'
  have hef := crossing_edgeParameter_det_ne_zero hn h1
    (isCrossing_of_common_interiors hremEF hqE hqF)
  have hek := crossing_edgeParameter_det_ne_zero hn h1
    (isCrossing_of_common_interiors hremEK hqE hqK)
  have hfk := crossing_edgeParameter_det_ne_zero hn h1
    (isCrossing_of_common_interiors hremFK hqF hqK)
  have hfe : det (edge g.center f) (edge g.center e) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hef
  have hke : det (edge g.center k) (edge g.center e) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hek
  have hkf : det (edge g.center k) (edge g.center f) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hfk
  have hsf : ({f, e, k} : Finset (ZMod n)) = v.val := by
    rw [← hs]
    ext i
    simp [or_comm, or_left_comm]
  have hsk : ({k, e, f} : Finset (ZMod n)) = v.val := by
    rw [← hs]
    ext i
    simp [or_comm, or_left_comm]
  refine ⟨e, f, k, hs, hz, hc', ?_, ?_, ?_⟩
  · exact g.concurrence_signChanges_parameter_order e f k hef hek
      (g.edge_control_signChanges_concurrence v h e f k hs)
  · exact g.concurrence_signChanges_parameter_order f e k hfe hfk
      (g.edge_control_signChanges_concurrence v h f e k hsf)
  · exact g.concurrence_signChanges_parameter_order k e f hke hkf
      (g.edge_control_signChanges_concurrence v h k e f hsk)

end WallGerm

namespace CurveCubeSubdivision.TimedEventCertificate

variable {γ : unitInterval → LabelledTuple n} {δ : ℝ}
    {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}

theorem triple_wall (E : TimedEventCertificate A hn t)
    (v : EdgeControlName n) (he : E.control = .inr v) :
    ∃ e f k, ({e, f, k} : Finset (ZMod n)) = v.val ∧ E.germ.TripleAt e f k := by
  have hng : ¬ Generic (A.path t) := by rw [← E.germ_center]; exact E.germ.center_not_generic
  have hsets := E.center_sets hng
  simp only [he] at hsets
  have hs : E.germ.SignChanges
      (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inr v))) := by
    simpa only [he] using E.signChanges
  exact E.germ.active_edge_control_tripleAt hn v hsets.1 hsets.2 hs

end CurveCubeSubdivision.TimedEventCertificate

end

end SM


namespace SM

/- The two vertex branches remain separate in the six source alternatives. -/
inductive RegularWallKind where
  | flat | bigon | sliding | triple | extension | cut
  deriving DecidableEq

def RegularWallKind.toWallKind : RegularWallKind → WallKind
  | .flat => .flat
  | .bigon => .vertex
  | .sliding => .vertex
  | .triple => .triple
  | .extension => .extension
  | .cut => .cut

namespace WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

def HasRegularWallKind : RegularWallKind → Prop
  | .flat => ∃ j, g.FlatAt j
  | .bigon => ∃ M a, g.BigonAt M a
  | .sliding => ∃ M a, g.SlidingAt M a
  | .triple => ∃ e f k, g.TripleAt e f k
  | .extension => ∃ M a, g.ExtensionAt M a
  | .cut => ∃ i j k, g.PureCutAt i j k

theorem hasRegularWallKind_underlying {kind : RegularWallKind} (h : g.HasRegularWallKind kind) :
    g.HasWallKind kind.toWallKind := by
  cases kind with
  | flat => exact h
  | bigon => obtain ⟨M, a, h⟩ := h; exact ⟨M, a, h.1⟩
  | sliding => obtain ⟨M, a, h⟩ := h; exact ⟨M, a, h.1⟩
  | triple => exact h
  | extension => exact h
  | cut => exact h

theorem bigon_sliding_marks_incompatible (hn : 3 ≤ n)
    (hb : g.HasRegularWallKind .bigon) (hs : g.HasRegularWallKind .sliding) : False := by
  obtain ⟨M, a, hb⟩ := hb
  obtain ⟨N, b, hs⟩ := hs
  have he := contactSupport_marks_unique hn hb.1.1 hs.1.1
    (Finset.singleton_inj.mp (hb.1.2.1.symm.trans hs.1.2.1))
  rcases he with ⟨rfl, rfl⟩
  exact hs.2 hb.2

theorem regularWallKind_unique (hn : 3 ≤ n) {a b : RegularWallKind}
    (ha : g.HasRegularWallKind a) (hb : g.HasRegularWallKind b) : a = b := by
  have he := g.wallKinds_mutually_exclusive hn
    (g.hasRegularWallKind_underlying ha) (g.hasRegularWallKind_underlying hb)
  cases a <;> cases b <;> simp only [RegularWallKind.toWallKind] at he <;>
    try cases he <;> try rfl
  · exact (g.bigon_sliding_marks_incompatible hn ha hb).elim
  · exact (g.bigon_sliding_marks_incompatible hn hb ha).elim

theorem exists_regularWallKind_of_simple (h : g.Simple) (hno : ∀ j, ¬ g.CuspAt j) :
    ∃ kind : RegularWallKind, g.HasRegularWallKind kind := by
  obtain ⟨kind, h⟩ := h
  cases kind with
  | flat => exact ⟨.flat, h⟩
  | cusp => obtain ⟨j, h⟩ := h; exact (hno j h).elim
  | vertex =>
    obtain ⟨M, a, h⟩ := h
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact ⟨.bigon, M, a, hb⟩
    · exact ⟨.sliding, M, a, hs⟩
  | triple => exact ⟨.triple, h⟩
  | extension => exact ⟨.extension, h⟩
  | cut => exact ⟨.cut, h⟩

theorem existsUnique_regularWallKind_of_simple (hn : 3 ≤ n) (h : g.Simple)
    (hno : ∀ j, ¬ g.CuspAt j) : ∃! kind : RegularWallKind, g.HasRegularWallKind kind := by
  obtain ⟨kind, hk⟩ := g.exists_regularWallKind_of_simple h hno
  exact ⟨kind, hk, fun other ho => g.regularWallKind_unique hn ho hk⟩

end WallGerm

namespace CurveCubeSubdivision.TimedEventCertificate

variable {n : ℕ} [NeZero n] {γ : unitInterval → LabelledTuple n} {δ : ℝ}
    {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}

theorem simple (E : TimedEventCertificate A hn t) : E.germ.Simple := by
  cases he : E.control with
  | inl v => exact (E.point_wall_cases v he).2.1
  | inr v =>
    obtain ⟨e, f, k, _, ht⟩ := E.triple_wall v he
    exact ⟨.triple, e, f, k, ht⟩

theorem regular_kind_unique (E : TimedEventCertificate A hn t) :
    (∃! kind : RegularWallKind, E.germ.HasRegularWallKind kind) ∧ ∀ j, ¬ E.germ.CuspAt j := by
  have hreg : Regular E.germ.center := by rw [E.germ_center]; exact A.regular t
  have hno := E.germ.not_cuspAt_of_regular hreg
  exact ⟨E.germ.existsUnique_regularWallKind_of_simple hn E.simple hno, hno⟩

end CurveCubeSubdivision.TimedEventCertificate

end SM


namespace SM

open Set

noncomputable section

variable {n : ℕ} [NeZero n]

theorem WallGerm.isolates_shifted_path (g : WallGerm n)
    (p : unitInterval → LabelledTuple n) (t : unitInterval)
    (hcurve : ∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      g.curve s = p ⟨(t : ℝ) + s.val, hs⟩) :
    ∃ ε > 0, ∀ u : unitInterval, u ≠ t → |(u : ℝ) - (t : ℝ)| < ε → Generic (p u) := by
  refine ⟨g.radius, g.radius_pos, ?_⟩
  intro u hne hu
  let s : g.Parameter := ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hu⟩
  have hsne : s.val ≠ 0 := sub_ne_zero.mpr (fun he => hne (Subtype.ext he))
  have hg := g.generic_punctured s hsne
  obtain ⟨hs, he⟩ := hcurve s
  have htu : (⟨(t : ℝ) + s.val, hs⟩ : unitInterval) = u := by
    apply Subtype.ext
    dsimp [s]
    ring
  rw [he, htu] at hg
  exact hg

/-- The source conclusion as explicit properties of one actual labelled path.
The uniform cells form a genuine finite partition; the affine formulas are in
the actual occurrence scalar coordinates. No cube, waypoint, control or wall
existence hypothesis is hidden in this structure. -/
structure RelativeGeneralPositionPath (γ : unitInterval → LabelledTuple n) (δ : ℝ) where
  path : unitInterval → LabelledTuple n
  continuous : Continuous path
  first : path 0 = γ 0
  last : path 1 = γ 1
  regular : ∀ t, Regular (path t)
  close : ∀ t, dist (tupleCoordinates (path t)) (tupleCoordinates (γ t)) < δ
  collision_free : ∀ t, Function.Injective (path t)
  edges_nonzero : ∀ t i, edge (path t) i ≠ 0
  cellCount : ℕ
  cellCount_pos : 0 < cellCount
  cell_cover : ∀ t, ∃ k : Fin cellCount, t ∈ uniformMeshCell cellCount cellCount_pos k
  affine_on_cells : ∀ k : Fin cellCount, ∃ a b : ScalarCoordinate n → ℝ,
    ∀ t ∈ uniformMeshCell cellCount cellCount_pos k,
      scalarCoordinates (path t) = fun z => a z + (t : ℝ) * b z
  generic_endpoint_collar : ∃ ε > 0, ∀ t : unitInterval,
    ((t : ℝ) < ε ∨ 1 - ε < (t : ℝ)) → Generic (path t)
  finite_nongeneric : {t : unitInterval | ¬ Generic (path t)}.Finite
  event : ∀ t, ¬ Generic (path t) → ∃ g : WallGerm n,
    g.center = path t ∧
    (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      g.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
    g.Simple ∧ ∃! kind : RegularWallKind, g.HasRegularWallKind kind
  isolated : ∀ t, ¬ Generic (path t) → ∃ ε > 0,
    ∀ u : unitInterval, u ≠ t → |(u : ℝ) - (t : ℝ)| < ε → Generic (path u)
  no_cusp : ∀ t (g : WallGerm n), g.center = path t → ∀ j, ¬ g.CuspAt j

/-- Strong construction retaining the same actual fine-cell/control/derivative/
smooth-graph certificate for every classified nongeneric event. -/
theorem relative_general_position_with_certificates (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hregular : ∀ t, Regular (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : CurveCubeSubdivision γ δ,
      ∃ W : d.InternalWaypoint × ScalarCoordinate n → ℝ,
        ∃ A : d.CubeCoordinateApproximation W,
          (∀ t, Function.Injective (A.path t)) ∧
          {t : unitInterval | ¬ Generic (A.path t)}.Finite ∧
          ∀ t, ¬ Generic (A.path t) →
            ∃ E : CurveCubeSubdivision.TimedEventCertificate A hn t,
              (∃! kind : RegularWallKind, E.germ.HasRegularWallKind kind) ∧
              ∀ j, ¬ E.germ.CuspAt j := by
  let d := chooseCurveCubeSubdivision hn γ hγ hregular hfirst hlast δ hδ
  obtain ⟨W, A, hJ, hcollision, hfinite⟩ := d.exists_joint_cubeCoordinateApproximation hn
  refine ⟨d, W, A, hcollision, hfinite, ?_⟩
  intro t hng
  obtain ⟨E⟩ := A.nonempty_timedEventCertificate hn hJ t hng
  exact ⟨E, E.regular_kind_unique⟩

/-- SM thm:relgp: relative general position, all six noncusp wall alternatives,
uniqueness of the kind, and retention of every labelled occurrence. -/
theorem relative_general_position (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hregular : ∀ t, Regular (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1))
    (δ : ℝ) (hδ : 0 < δ) : Nonempty (RelativeGeneralPositionPath γ δ) := by
  obtain ⟨d, W, A, hcollision, hfinite, hE⟩ :=
    relative_general_position_with_certificates hn γ hγ hregular hfirst hlast δ hδ
  have hm : 0 < 2 * n := by omega
  have hN := Nat.mul_pos d.count_pos hm
  refine ⟨{
    path := A.path
    continuous := A.continuous
    first := A.first
    last := A.last
    regular := A.regular
    close := A.close
    collision_free := hcollision
    edges_nonzero := fun t i => (A.regular t i).2.1
    cellCount := d.count * (2 * n)
    cellCount_pos := hN
    cell_cover := fun t => exists_uniformMeshCell _ hN t
    affine_on_cells := A.affine_on_cells
    generic_endpoint_collar := A.generic_endpoint_collar
    finite_nongeneric := hfinite
    event := ?_
    isolated := ?_
    no_cusp := ?_ }⟩
  · intro t hng
    obtain ⟨E, hk, _⟩ := hE t hng
    exact ⟨E.germ, E.germ_center, E.curve_on_path, E.simple, hk⟩
  · intro t hng
    obtain ⟨E, _, _⟩ := hE t hng
    exact E.germ.isolates_shifted_path A.path t E.curve_on_path
  · intro t g he j
    apply g.not_cuspAt_of_regular
    rw [he]
    exact A.regular t

end

end SM

#print axioms SM.RelativeGeneralPositionPath
#print axioms SM.relative_general_position_with_certificates
#print axioms SM.relative_general_position
