import CV.Events
import SM.TripleVisitExchanges
import SM.GeometricParameters
import SM.GeometricInterlacement

/-! # CV-DOM unit U8 — the triple lane on CV events (intended home `work/lean/CV/TripleEvents.lean`)

Draft written 2026-09-14 (prover subagent of the pod executor) for DECISION_FINAL.md §5 unit U8.
Checked with `cd work/lean && lake env lean ../drafts/cvdom/U8/CVTripleEvents.lean`.

The accepted SM triple lane (SM/TripleCenter … SM/TripleWallSides) proves, for a simple triple
wall germ `g.TripleAt e f k` on SM-generic sides, the six facts of lem:triple-sides: the crossing
set persists on both sides, the three triangle orders reverse, every other same-edge order persists
(parameter and visit level), and on each bundle edge the two triangle visits are adjacent. This
module restates them on a CV event `E : CV.Event n` with `E.IsSimpleRIII e f g h3 h4e h4f h4g`
(CV/Events.lean; CV ax:R's forced bundle), whose sides `E.curve t`, `t ≠ 0`, are only CV-generic
(`CV.Generic`, hence `SM.CrossingGeometry` — three collinear vertices are allowed). Orders are the
printed parameters `CV.crossParam` (= `SM.edgeParameter`, `CV.crossParam_eq_edgeParameter`); visit
positions are the geometric ones `SM.geometricVisitPosition` of CV:def:interlace; adjacency is the
empty-arc predicate of the R-lane statement file (`RProof.AdjacentVisits`), restated here as
`CV.EmptyArcAdjacent` with the identical body.

What replaces the SM ingredients.
* `SM.Generic` entered the accepted lane only through `generic_edgeParameters_ne`; here the
  accepted `SM.geometric_edgeParameters_ne` (CrossingGeometry) and `CV.Generic.crossParam_ne` do
  the same work.
* `G1` at the centre (`g1_crossings_locally_constant`, `g1_center_side_parameter_order`) is
  replaced by the four unconditional `G2` members being off the zero set (`Event.NoG2Zero`, true
  for the forced RIII bundle) and CV:lem:guardconst: every `Crosses` activation is then constant
  along the WHOLE event interval, centre included (`NoG2Zero.crosses_const`, the event form of the
  accepted `Bridge.crosses_const`).
* the unique concurrence triple (`uniqueTriple_parameter_tie_iff`) is replaced by the zero set
  being exactly the forced bundle: a parameter tie at the centre on an active pair is a vanishing
  member-valued `G4⟨i;j,k⟩`, hence a member of `Z`, hence one of the three printed `G4`s
  (`IsSimpleRIII.tie_center_iff`).
* the three sign changes (`SignChanges` of the parameter differences) are replaced by
  transversality of the three `G4` members (`E.Transversal`, the route of the accepted `Bridge.B3`
  read backwards through `CV.G4_factorization`).

Consequence: no radius `δ` is needed anywhere — every clause holds on the whole punctured
interval `t ≠ 0`, `|t| < E.radius` (the localization unit can take `δ := E.radius`).

Two small intermediate-value facts (`CV.lt_zero_iff_of_ne_zero`, `CV.mul_pos_of_ne_zero_of_preconnected`)
duplicate `Bridge.neg_iff_of_ne_zero` / `Bridge.mul_pos_of_ne_zero_const` so that this CV module
does not import the Bridge lane (Bridge imports CV). -/

namespace CV

open SM Filter Topology

variable {n : ℕ}

/-! ## Intermediate-value facts -/

/-- A continuous real function without zeros on a preconnected space has constant sign
(the intermediate value theorem; mirror of the accepted `Bridge.neg_iff_of_ne_zero`). -/
theorem lt_zero_iff_of_ne_zero {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {φ : X → ℝ} (hφ : Continuous φ) (h0 : ∀ x, φ x ≠ 0) (a b : X) : φ a < 0 ↔ φ b < 0 := by
  have key : ∀ a b : X, φ a < 0 → φ b < 0 := by
    intro a b ha
    by_contra hb
    have hb' : 0 < φ b := lt_of_le_of_ne (not_lt.mp hb) (h0 b).symm
    obtain ⟨x, hx⟩ := intermediate_value_univ a b hφ ⟨ha.le, hb'.le⟩
    exact h0 x hx
  exact ⟨key a b, key b a⟩

/-- Mirror of the accepted `Bridge.mul_pos_of_ne_zero_const`. -/
theorem mul_pos_of_ne_zero_of_preconnected {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {φ : X → ℝ} (hφ : Continuous φ) (h0 : ∀ x, φ x ≠ 0) (a b : X) : 0 < φ a * φ b := by
  rcases lt_or_gt_of_ne (h0 a) with ha | ha
  · exact mul_pos_of_neg_of_neg ha ((lt_zero_iff_of_ne_zero hφ h0 a b).mp ha)
  · rcases lt_or_gt_of_ne (h0 b) with hb | hb
    · exact absurd ((lt_zero_iff_of_ne_zero hφ h0 a b).mpr hb) (not_lt.mpr ha.le)
    · exact mul_pos ha hb

/-! ## Polygon-level facts -/

/-- `G4_{a;b,c} = (t_b − t_c) · (det(d_b, d_a) det(d_c, d_a))` (`CV.G4_factorization` regrouped,
BRIDGE.md (7) with the printed parameters). -/
theorem G4_eq_crossParam_sub_mul {P : LabelledTuple n} {a b c : ZMod n} (hab : Crosses P a b)
    (hac : Crosses P a c) :
    G4 P a b c = (crossParam P a b - crossParam P a c) *
      (det (edge P b) (edge P a) * det (edge P c) (edge P a)) := by
  rw [G4_factorization P a b c hab.det_ne_zero' hac.det_ne_zero', mul_assoc]

/-- The accepted `SM.TriangleOrderExchanges` written with the printed parameters `CV.crossParam`
(`SM.edgeParameter`): on each of the three bundle edges the order of the two triangle crossings
is reversed between `P` and `Q`, both directions. This is the body of
`LocalizationData.order_reverses`. -/
def TriangleCrossParamExchanges (P Q : LabelledTuple n) (e f g : ZMod n) : Prop :=
  ((crossParam P e f < crossParam P e g ↔ crossParam Q e g < crossParam Q e f) ∧
    (crossParam P e g < crossParam P e f ↔ crossParam Q e f < crossParam Q e g)) ∧
  ((crossParam P f e < crossParam P f g ↔ crossParam Q f g < crossParam Q f e) ∧
    (crossParam P f g < crossParam P f e ↔ crossParam Q f e < crossParam Q f g)) ∧
  ((crossParam P g e < crossParam P g f ↔ crossParam Q g f < crossParam Q g e) ∧
    (crossParam P g f < crossParam P g e ↔ crossParam Q g e < crossParam Q g f))

theorem triangleCrossParamExchanges_iff (P Q : LabelledTuple n) (e f g : ZMod n) :
    TriangleCrossParamExchanges P Q e f g ↔ TriangleOrderExchanges P Q e f g := by
  simp only [TriangleCrossParamExchanges, TriangleOrderExchanges, crossParam_eq_edgeParameter]

theorem TriangleCrossParamExchanges.symm {P Q : LabelledTuple n} {e f g : ZMod n}
    (h : TriangleCrossParamExchanges P Q e f g) : TriangleCrossParamExchanges Q P e f g :=
  ⟨⟨h.1.2.symm, h.1.1.symm⟩, ⟨h.2.1.2.symm, h.2.1.1.symm⟩, ⟨h.2.2.2.symm, h.2.2.1.symm⟩⟩

/-- CrossingGeometry form of the accepted `SM.exactTriangleVisitOrders_of_parameters`: `G1` is
replaced by the geometric identification of visit parameters with edge parameters
(`SM.visitParameter_eq_of_support_pair_of_geometry`). -/
theorem exactTriangleVisitOrders_of_parameters_of_geometry {P Q : LabelledTuple n}
    (hP : CrossingGeometry P) (hQ : CrossingGeometry Q) {e f g : ZMod n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : ExactTriangleParameterOrders P Q e f g) :
    ExactTriangleVisitOrders P Q e f g hs := by
  intro v w he
  obtain ⟨j, _, hv⟩ := crossing_support_partner v.1 v.2.val v.2.property
  obtain ⟨k, _, hw⟩ := crossing_support_partner w.1 w.2.val w.2.property
  have hij : IsCrossing P {v.2.val, j} := by simpa only [hv] using v.1.property
  have hik : IsCrossing P {v.2.val, k} := by simpa only [hw, he] using w.1.property
  have hu : v.1.val ∪ w.1.val = {v.2.val, j, k} := by
    calc
      v.1.val ∪ w.1.val = {v.2.val, j} ∪ {w.2.val, k} :=
        congrArg₂ (fun x y : Finset (ZMod n) => x ∪ y) hv hw
      _ = {v.2.val, j, k} := by
        rw [← he]
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
  rw [visitParameter_eq_of_support_pair_of_geometry hP v j hv,
    visitParameter_eq_of_support_pair_of_geometry hP w k hw,
    visitParameter_eq_of_support_pair_of_geometry hQ (visitTransport hs v) j hv,
    visitParameter_eq_of_support_pair_of_geometry hQ (visitTransport hs w) k hw,
    visitTransport_edge, visitTransport_edge, ← he, hu]
  exact ho _ j k hij hik

/-- If `{h, i, j}` is the bundle (three distinct edges), then the two pairs `{h, i}`, `{h, j}` are
both triangle supports (the contrapositive of the printed "other than a bundle pair"). -/
theorem pairs_mem_of_support_eq {e f g h i j : ZMod n} (hhi : h ≠ i) (hhj : h ≠ j) (hij : i ≠ j)
    (hs : ({h, i, j} : Finset (ZMod n)) = {e, f, g}) :
    ({h, i} : Finset (ZMod n)) ∈ ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n))) ∧
    ({h, j} : Finset (ZMod n)) ∈ ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n))) := by
  rcases triple_support_six_orders hhi hhj hij hs with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  simp [Finset.pair_comm]

/-! ## Empty-arc adjacency on `CrossingGeometry` (the R-lane form) -/

/-- The empty-arc adjacency of the R-lane statement file (`RProof.AdjacentVisits`, identical body):
`v ≠ w` and no crossing visit lies strictly inside one of the two arcs into which `v, w` cut the
traversal circle, positions being the geometric visit positions of CV:def:interlace. -/
def EmptyArcAdjacent {P : LabelledTuple n} (hP : CrossingGeometry P) (v w : Visit P) : Prop :=
  v ≠ w ∧
  ((∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP u)
      (geometricVisitPosition hP w)) ∨
   (∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP w) (geometricVisitPosition hP u)
      (geometricVisitPosition hP v)))

/-- The visit of the crossing carried by `{i, j}` on its edge `h` (the unfolding of the statement
file's `visitOn (xPair hc) h hh`). -/
def visitOfPair {P : LabelledTuple n} {i j : ZMod n} (hc : IsCrossing P {i, j}) (h : ZMod n)
    (hh : h ∈ ({i, j} : Finset (ZMod n))) : Visit P := ⟨⟨{i, j}, hc⟩, h, hh⟩

theorem pair_ne_of_not_mem_left {a b c d : ZMod n} (h : a ∉ ({c, d} : Finset (ZMod n))) :
    ({a, b} : Finset (ZMod n)) ≠ {c, d} := fun hs => h (hs ▸ Finset.mem_insert_self a {b})

theorem pair_ne_of_not_mem_right {a b c d : ZMod n} (h : b ∉ ({c, d} : Finset (ZMod n))) :
    ({a, b} : Finset (ZMod n)) ≠ {c, d} :=
  fun hs => h (hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))

theorem crossingPoints_ne_of_geometry {P : LabelledTuple n} (hP : CrossingGeometry P)
    {c d : Crossing P} (h : c.val ≠ d.val) : crossingPoint c ≠ crossingPoint d :=
  fun he => h (congrArg Subtype.val (crossingPoint_injective_of_geometry hP he))

variable [NeZero n]

/-- The geometric form of the accepted `visitKey_lt_iff`. -/
theorem geometricVisitKey_lt_iff {P : LabelledTuple n} (hP : CrossingGeometry P) (v w : Visit P) :
    geometricVisitKey hP v < geometricVisitKey hP w ↔
      v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧ visitParameter v < visitParameter w :=
  traversalKey_lt_iff (geometricVisitPosition hP v) (geometricVisitPosition hP w)

/-- The geometric form of the accepted `visit_between_same_edge`: a visit strictly between two
visits of one edge is on that edge with parameter strictly between. -/
theorem geometric_visit_between_same_edge {P : LabelledTuple n} (hP : CrossingGeometry P)
    {v w u : Visit P} (he : v.2.val = w.2.val)
    (hl : geometricVisitKey hP v < geometricVisitKey hP u)
    (hr : geometricVisitKey hP u < geometricVisitKey hP w) :
    u.2.val = v.2.val ∧ visitParameter v < visitParameter u ∧
      visitParameter u < visitParameter w := by
  have h₁ := (geometricVisitKey_lt_iff hP v u).mp hl
  have h₂ := (geometricVisitKey_lt_iff hP u w).mp hr
  rcases h₁ with h₁ | ⟨h₁, hp₁⟩
  · rcases h₂ with h₂ | ⟨h₂, _⟩
    · rw [← he] at h₂
      exact (lt_asymm h₁ h₂).elim
    · rw [h₂, ← he] at h₁
      exact (lt_irrefl _ h₁).elim
  · rcases h₂ with h₂ | ⟨_, hp₂⟩
    · rw [← h₁, ← he] at h₂
      exact (lt_irrefl _ h₂).elim
    · exact ⟨h₁.symm, hp₁, hp₂⟩

/-- The geometric outside-parameter condition on the edge `i` (accepted `SM.OtherCrossingsOutside`)
makes the two visits of `{i, j}`, `{i, k}` on `i` adjacent in the empty-arc sense: an intervening
visit would be a crossing `{i, h}` of `i` with parameter strictly between the two — the CrossingGeometry
form of the accepted `pairVisits_adjacent` / `pairVisits_no_between`, with the two supports given
up to presentation order. -/
theorem emptyArcAdjacent_of_outside {P : LabelledTuple n} (hP : CrossingGeometry P)
    {i j k : ZMod n} (hjk : j ≠ k) {v w : Visit P} (hv : v.2.val = i) (hw : w.2.val = i)
    (hvs : v.1.val = {i, j}) (hws : w.1.val = {i, k}) (hout : OtherCrossingsOutside P i j k) :
    EmptyArcAdjacent hP v w := by
  have hcj : IsCrossing P {i, j} := hvs ▸ v.1.property
  have hck : IsCrossing P {i, k} := hws ▸ w.1.property
  have hpv : visitParameter v = edgeParameter P i j := by
    have := visitParameter_eq_of_support_pair_of_geometry hP v j (by rw [hv]; exact hvs)
    rwa [hv] at this
  have hpw : visitParameter w = edgeParameter P i k := by
    have := visitParameter_eq_of_support_pair_of_geometry hP w k (by rw [hw]; exact hws)
    rwa [hw] at this
  have hne : edgeParameter P i j ≠ edgeParameter P i k := geometric_edgeParameters_ne hP hjk hcj hck
  have hvw : v ≠ w := by
    intro h
    apply hne
    rw [← hpv, ← hpw, h]
  -- an intervening visit on the edge `i` is a third crossing `{i, h}` with parameter between
  have between : ∀ {a b : Visit P} {ja ka : ZMod n}, a.2.val = i → b.2.val = i →
      visitParameter a = edgeParameter P i ja → visitParameter b = edgeParameter P i ka →
      OtherCrossingsOutside P i ja ka → ∀ u : Visit P,
      ¬ (geometricVisitKey hP a < geometricVisitKey hP u ∧
        geometricVisitKey hP u < geometricVisitKey hP b) := by
    intro a b ja ka ha hb hpa' hpb' hout' u ⟨hl, hr⟩
    obtain ⟨he, hpa, hpb⟩ := geometric_visit_between_same_edge hP (ha.trans hb.symm) hl hr
    have hui : u.2.val = i := he.trans ha
    obtain ⟨h, hih, hus⟩ := crossing_support_partner u.1 u.2.val u.2.property
    rw [hui] at hus hih
    have hpu : visitParameter u = edgeParameter P i h := by
      have := visitParameter_eq_of_support_pair_of_geometry hP u h (by rw [hui]; exact hus)
      rwa [hui] at this
    have hch : IsCrossing P {i, h} := hus ▸ u.1.property
    rw [hpa', hpu] at hpa
    rw [hpu, hpb'] at hpb
    by_cases hhj : h = ja
    · subst hhj
      exact lt_irrefl _ hpa
    by_cases hhk : h = ka
    · subst hhk
      exact lt_irrefl _ hpb
    exact (outsidePair_not_between (hout' h hih.symm hhj hhk hch)).1 ⟨hpa, hpb⟩
  have hgap1 := between hv hw hpv hpw hout
  have hgap2 := between hw hv hpw hpv (otherCrossingsOutside_swap hout)
  refine ⟨hvw, ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hkvw : geometricVisitKey hP v < geometricVisitKey hP w :=
      (geometricVisitKey_lt_iff hP v w).mpr (Or.inr ⟨hv.trans hw.symm, by rw [hpv, hpw]; exact hlt⟩)
    left
    intro u hb
    rcases hb with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hgap1 u ⟨h1, h2⟩
    · exact lt_asymm hkvw h2
    · exact lt_asymm hkvw h1
  · have hkwv : geometricVisitKey hP w < geometricVisitKey hP v :=
      (geometricVisitKey_lt_iff hP w v).mpr (Or.inr ⟨hw.trans hv.symm, by rw [hpv, hpw]; exact hgt⟩)
    right
    intro u hb
    rcases hb with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hgap2 u ⟨h1, h2⟩
    · exact lt_asymm hkwv h2
    · exact lt_asymm hkwv h1

/-- CV form of the accepted `SM.TripleSides`: the three triangle crossings, their pairwise distinct
points, and empty-arc adjacency of the three bundle-pair visits (same visit terms as the SM
predicate; adjacency in the geometric form). -/
def GeometricTripleSides {P : LabelledTuple n} (hP : CrossingGeometry P) (i j k : ZMod n) : Prop :=
  ∃ hij : IsCrossing P {i, j}, ∃ hik : IsCrossing P {i, k},
    ∃ hjk : IsCrossing P {j, k},
      crossingPoint ⟨{i, j}, hij⟩ ≠ crossingPoint ⟨{i, k}, hik⟩ ∧
      crossingPoint ⟨{i, j}, hij⟩ ≠ crossingPoint ⟨{j, k}, hjk⟩ ∧
      crossingPoint ⟨{i, k}, hik⟩ ≠ crossingPoint ⟨{j, k}, hjk⟩ ∧
      EmptyArcAdjacent hP (pairVisit hij) (pairVisit hik) ∧
      EmptyArcAdjacent hP (pairVisit (isCrossing_pair_reverse hij)) (pairVisit hjk) ∧
      EmptyArcAdjacent hP (pairVisit (isCrossing_pair_reverse hik))
        (pairVisit (isCrossing_pair_reverse hjk))

/-! ### Bridge from the SM lane's linear adjacency (`SM.VisitsAdjacent`, consecutive indices in
`gaussList`) to the empty-arc form. Only this direction holds in general: the first and the last
visit of `gaussList` are cyclically adjacent (empty arc through the cut at label `0`) but not
index-adjacent. -/

/-- Converse of the accepted `sorted_indices_adjacent`: consecutive positions in the sorted list
leave no element of `s` strictly between. -/
theorem sorted_no_between_of_adjacent {α : Type*} [LinearOrder α] (s : Finset α) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hidx : s.sort.idxOf b = s.sort.idxOf a + 1) :
    ∀ x ∈ s, ¬ (a < x ∧ x < b) := by
  rintro x hx ⟨hax, hxb⟩
  let e := s.orderIsoOfFin rfl
  have h1 : (e.symm ⟨a, ha⟩).val < (e.symm ⟨x, hx⟩).val := e.symm.strictMono hax
  have h2 : (e.symm ⟨x, hx⟩).val < (e.symm ⟨b, hb⟩).val := e.symm.strictMono hxb
  simp only [e, Finset.orderIsoOfFin_symm_apply] at h1 h2
  omega

/-- Order from list positions in the sorted list. -/
theorem sorted_lt_of_idxOf_lt {α : Type*} [LinearOrder α] (s : Finset α) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (h : s.sort.idxOf a < s.sort.idxOf b) : a < b := by
  let e := s.orderIsoOfFin rfl
  have h' : e.symm ⟨a, ha⟩ < e.symm ⟨b, hb⟩ := by
    change (e.symm ⟨a, ha⟩).val < (e.symm ⟨b, hb⟩).val
    simpa only [e, Finset.orderIsoOfFin_symm_apply] using h
  exact e.symm.lt_iff_lt.mp h'

/-- The SM lane's `VisitsAdjacent` (consecutive in the linear Gauss list of an SM-generic polygon)
implies the empty-arc adjacency of the R lane, read on any `CrossingGeometry` proof of the same
polygon (`geometricVisitPosition_eq_generic` is `rfl`). -/
theorem visitsAdjacent_emptyArc (hn : 3 ≤ n) {P : LabelledTuple n} (hP : SM.Generic P)
    (hCG : CrossingGeometry P) {v w : Visit P} (h : VisitsAdjacent hn hP v w) :
    EmptyArcAdjacent hCG v w := by
  classical
  let _ := visitLinearOrder hn hP
  let _ : DecidableEq (Visit P) := fun a b => LinearOrder.toDecidableEq a b
  have key : ∀ {a b : Visit P}, (gaussList hn hP).idxOf a + 1 = (gaussList hn hP).idxOf b →
      a ≠ b ∧ geometricVisitKey hCG a < geometricVisitKey hCG b ∧
      ∀ u : Visit P, ¬ (geometricVisitKey hCG a < geometricVisitKey hCG u ∧
        geometricVisitKey hCG u < geometricVisitKey hCG b) := by
    intro a b hab
    have hidx : (gaussList hn hP).idxOf a < (gaussList hn hP).idxOf b := by omega
    have hlt : a < b :=
      sorted_lt_of_idxOf_lt Finset.univ (Finset.mem_univ a) (Finset.mem_univ b) hidx
    have hgap := sorted_no_between_of_adjacent Finset.univ (Finset.mem_univ a) (Finset.mem_univ b)
      hab.symm
    exact ⟨ne_of_lt hlt, hlt, fun u => hgap u (Finset.mem_univ u)⟩
  rcases h with h | h
  · obtain ⟨hne, hlt, hgap⟩ := key h
    refine ⟨hne, Or.inl fun u hb => ?_⟩
    rcases hb with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hgap u ⟨h1, h2⟩
    · exact lt_asymm hlt h2
    · exact lt_asymm hlt h1
  · obtain ⟨hne, hlt, hgap⟩ := key h
    refine ⟨hne.symm, Or.inr fun u hb => ?_⟩
    rcases hb with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hgap u ⟨h1, h2⟩
    · exact lt_asymm hlt h2
    · exact lt_asymm hlt h1

/-- The accepted `SM.TripleSides` (SM lane, on an SM-generic polygon) implies the CV form. -/
theorem geometricTripleSides_of_tripleSides (hn : 3 ≤ n) {P : LabelledTuple n} (hP : SM.Generic P)
    (hCG : CrossingGeometry P) {i j k : ZMod n} (h : SM.TripleSides hn hP i j k) :
    GeometricTripleSides hCG i j k := by
  obtain ⟨hij, hik, hjk, h1, h2, h3, a1, a2, a3⟩ := h
  exact ⟨hij, hik, hjk, h1, h2, h3, visitsAdjacent_emptyArc hn hP hCG a1,
    visitsAdjacent_emptyArc hn hP hCG a2, visitsAdjacent_emptyArc hn hP hCG a3⟩

namespace Event

variable (E : Event n)

instance parameter_connectedSpace : ConnectedSpace E.Parameter :=
  isConnected_iff_connectedSpace.mp (isConnected_Ioo (by linarith [E.radius_pos]))

variable {E}

theorem curve_eq_center_of_val {t : E.Parameter} (ht : t.val = 0) : E.curve t = E.center := by
  have : t = E.zeroParameter := Subtype.ext ht
  rw [this]
  rfl

variable (E)

/-- No unconditional `G2` member belongs to the zero set of `E`. This is the one property of the
forced RIII bundle that makes every activation constant along the whole event interval. -/
def NoG2Zero : Prop := ∀ (a i : ZMod n) (h : i ≠ a ∧ i ≠ a + 1), Member.g2 a i h ∉ E.zeroSet

variable {E}

/-! ## Activations are constant along the whole event -/

theorem NoG2Zero.g2_center_ne_zero (hZ : E.NoG2Zero) {a i : ZMod n} (h0 : i ≠ a)
    (h1 : i ≠ a + 1) : G2 E.center a i ≠ 0 :=
  (guardconst E (Member.g2 a i ⟨h0, h1⟩) ⟨E.sideTime true E.sideBase,
    E.sideTime_ne_zero true E.sideBase, Member.relevant_g2 _ a i ⟨h0, h1⟩⟩ (hZ a i ⟨h0, h1⟩)).1

theorem NoG2Zero.g2_ne_zero (hZ : E.NoG2Zero) (t : E.Parameter) {a i : ZMod n} (h0 : i ≠ a)
    (h1 : i ≠ a + 1) : G2 (E.curve t) a i ≠ 0 := by
  by_cases ht : t.val = 0
  · rw [curve_eq_center_of_val ht]
    exact hZ.g2_center_ne_zero h0 h1
  · exact (E.generic_punctured t ht).g2 h0 h1

theorem NoG2Zero.four_g2 (hZ : E.NoG2Zero) (t : E.Parameter) {a b : ZMod n} (hr : remote a b) :
    G2 (E.curve t) a b ≠ 0 ∧ G2 (E.curve t) a (b + 1) ≠ 0 ∧
      G2 (E.curve t) b a ≠ 0 ∧ G2 (E.curve t) b (a + 1) ≠ 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := remote_endpoints a b hr
  exact ⟨hZ.g2_ne_zero t h0 h1, hZ.g2_ne_zero t h2 h3, hZ.g2_ne_zero t h0.symm h2.symm,
    hZ.g2_ne_zero t h1.symm h3.symm⟩

/-- CV activation of a pair is constant along the whole event interval, centre included (the event
form of the accepted `Bridge.crosses_const`). -/
theorem NoG2Zero.crosses_const (hZ : E.NoG2Zero) (a b : ZMod n) (s t : E.Parameter) :
    Crosses (E.curve s) a b ↔ Crosses (E.curve t) a b := by
  by_cases hr : remote a b
  · obtain ⟨h0, h1, h2, h3⟩ := remote_endpoints a b hr
    have c1 : Continuous fun u : E.Parameter => G2 (E.curve u) a b * G2 (E.curve u) a (b + 1) :=
      ((continuous_G2 a b).comp E.continuous_curve).mul
        ((continuous_G2 a (b + 1)).comp E.continuous_curve)
    have c2 : Continuous fun u : E.Parameter => G2 (E.curve u) b a * G2 (E.curve u) b (a + 1) :=
      ((continuous_G2 b a).comp E.continuous_curve).mul
        ((continuous_G2 b (a + 1)).comp E.continuous_curve)
    have n1 : ∀ u : E.Parameter, G2 (E.curve u) a b * G2 (E.curve u) a (b + 1) ≠ 0 :=
      fun u => mul_ne_zero (hZ.g2_ne_zero u h0 h1) (hZ.g2_ne_zero u h2 h3)
    have n2 : ∀ u : E.Parameter, G2 (E.curve u) b a * G2 (E.curve u) b (a + 1) ≠ 0 :=
      fun u => mul_ne_zero (hZ.g2_ne_zero u h0.symm h2.symm) (hZ.g2_ne_zero u h1.symm h3.symm)
    exact and_congr Iff.rfl
      (and_congr (lt_zero_iff_of_ne_zero c1 n1 s t) (lt_zero_iff_of_ne_zero c2 n2 s t))
  · exact ⟨fun hc => (hr hc.1).elim, fun hc => (hr hc.1).elim⟩

/-- At every time of the event (centre included) activation is the actual crossing relation. -/
theorem NoG2Zero.isCrossing_iff_crosses (hZ : E.NoG2Zero) (t : E.Parameter) (a b : ZMod n) :
    IsCrossing (E.curve t) {a, b} ↔ Crosses (E.curve t) a b :=
  ⟨fun h => crosses_of_meet (crossing_pair_remote h) (hZ.four_g2 t (crossing_pair_remote h))
    ((isCrossing_pair _ a b (crossing_pair_remote h)).mp h), Crosses.isCrossing⟩

/-- The crossing set, indexed by carrying edge pairs, is constant along the whole event interval. -/
theorem NoG2Zero.isCrossing_const (hZ : E.NoG2Zero) (s t : E.Parameter) (c : Finset (ZMod n)) :
    IsCrossing (E.curve s) c ↔ IsCrossing (E.curve t) c := by
  have key : ∀ s t : E.Parameter, IsCrossing (E.curve s) c → IsCrossing (E.curve t) c := by
    intro s t h
    obtain ⟨i, j, rfl, hr, hne⟩ := h
    have hc : IsCrossing (E.curve s) {i, j} := ⟨i, j, rfl, hr, hne⟩
    exact (hZ.isCrossing_iff_crosses t i j).mpr
      ((hZ.crosses_const i j s t).mp ((hZ.isCrossing_iff_crosses s i j).mp hc))
  exact ⟨key s t, key t s⟩

theorem NoG2Zero.active_const (hZ : E.NoG2Zero) (m : Member n) (s t : E.Parameter) :
    m.Active (E.curve s) ↔ m.Active (E.curve t) := by
  cases m with
  | g1 _ => exact Iff.rfl
  | g2 _ _ _ => exact Iff.rfl
  | g5 a b _ => exact hZ.crosses_const a b s t
  | g3 a b c _ =>
    exact and_congr (hZ.crosses_const a b s t)
      (and_congr (hZ.crosses_const b c s t) (hZ.crosses_const a c s t))
  | g4 a b c _ => exact and_congr (hZ.crosses_const a b s t) (hZ.crosses_const a c s t)

theorem NoG2Zero.active_center_of_relevant (hZ : E.NoG2Zero) {m : Member n} (hc : m.Conditional)
    {t : E.Parameter} (hm : m.Relevant (E.curve t)) : m.Active E.center := by
  rcases hm with hu | ha
  · exact (hc hu).elim
  · exact (hZ.active_const m t E.zeroParameter).mp ha

/-- A member vanishing at the centre and active there is in the zero set. -/
theorem NoG2Zero.mem_zeroSet_of_active (hZ : E.NoG2Zero) {m : Member n}
    (h0 : m.eval E.center = 0) (ha : m.Active E.center) : m ∈ E.zeroSet :=
  ⟨h0, E.sideTime true E.sideBase, E.sideTime_ne_zero true E.sideBase,
    Or.inr ((hZ.active_const m E.zeroParameter _).mp ha)⟩

/-! ## Continuity and sign constancy of the crossing parameters along the event -/

/-- `t ↦ t_j(P(t))` along `i` is continuous on the whole event interval once `i, j` cross at the
centre (the denominator `det(d_j, d_i)` is nonzero at every time). -/
theorem NoG2Zero.continuous_crossParam (hZ : E.NoG2Zero) {i j : ZMod n}
    (hc : Crosses E.center i j) :
    Continuous fun t : E.Parameter => crossParam (E.curve t) i j := by
  have hd : ∀ t : E.Parameter, det (edge (E.curve t) j) (edge (E.curve t) i) ≠ 0 :=
    fun t => ((hZ.crosses_const i j E.zeroParameter t).mp hc).det_ne_zero'
  have h1 : Continuous fun t : E.Parameter => det (edge (E.curve t) j) (E.curve t j - E.curve t i) :=
    continuous_det ((continuous_edge j).comp E.continuous_curve)
      (((continuous_vertex j).comp E.continuous_curve).sub
        ((continuous_vertex i).comp E.continuous_curve))
  have h2 : Continuous fun t : E.Parameter => det (edge (E.curve t) j) (edge (E.curve t) i) :=
    continuous_det ((continuous_edge j).comp E.continuous_curve)
      ((continuous_edge i).comp E.continuous_curve)
  exact h1.div h2 hd

theorem NoG2Zero.continuous_crossParam_sub (hZ : E.NoG2Zero) {i j k : ZMod n}
    (hij : Crosses E.center i j) (hik : Crosses E.center i k) :
    Continuous fun t : E.Parameter => crossParam (E.curve t) i j - crossParam (E.curve t) i k :=
  (hZ.continuous_crossParam hij).sub (hZ.continuous_crossParam hik)

/-- On a generic side polygon two crossings on a common edge never tie. -/
theorem NoG2Zero.crossParam_sub_ne_zero (hZ : E.NoG2Zero) {t : E.Parameter} (ht : t.val ≠ 0)
    {i j k : ZMod n} (hjk : j ≠ k) (hij : Crosses E.center i j) (hik : Crosses E.center i k) :
    crossParam (E.curve t) i j - crossParam (E.curve t) i k ≠ 0 :=
  sub_ne_zero.mpr ((E.generic_punctured t ht).crossParam_ne
    ((hZ.crosses_const i j E.zeroParameter t).mp hij)
    ((hZ.crosses_const i k E.zeroParameter t).mp hik) hjk)

/-- Same-side constancy of every same-edge order: each side `P((0, ε))`, `P((−ε, 0))` is connected
and consists of generic polygons, on which the two parameters never tie (the CV form of the
accepted `g1_center_side_parameter_order`; no `j ≠ k` hypothesis, the case `j = k` being trivial). -/
theorem NoG2Zero.crossParam_lt_iff_side (hZ : E.NoG2Zero) {i j k : ZMod n}
    (hij : Crosses E.center i j) (hik : Crosses E.center i k) (b : Bool)
    (s s' : E.SideParameter) :
    (crossParam (E.sideCurve b s) i j < crossParam (E.sideCurve b s) i k ↔
      crossParam (E.sideCurve b s') i j < crossParam (E.sideCurve b s') i k) := by
  by_cases hjk : j = k
  · subst k
    simp
  have hφ : Continuous fun s : E.SideParameter =>
      crossParam (E.sideCurve b s) i j - crossParam (E.sideCurve b s) i k :=
    (hZ.continuous_crossParam_sub hij hik).comp (E.continuous_sideTime b)
  have h0 : ∀ s : E.SideParameter,
      crossParam (E.sideCurve b s) i j - crossParam (E.sideCurve b s) i k ≠ 0 :=
    fun s => hZ.crossParam_sub_ne_zero (E.sideTime_ne_zero b s) hjk hij hik
  have := lt_zero_iff_of_ne_zero hφ h0 s s'
  simpa only [sub_neg] using this

/-- Whole-interval constancy of a same-edge order whose two parameters do not tie at the centre. -/
theorem NoG2Zero.crossParam_lt_iff_of_center_ne (hZ : E.NoG2Zero) {i j k : ZMod n}
    (hij : Crosses E.center i j) (hik : Crosses E.center i k)
    (hne : crossParam E.center i j ≠ crossParam E.center i k) (s t : E.Parameter) :
    (crossParam (E.curve s) i j < crossParam (E.curve s) i k ↔
      crossParam (E.curve t) i j < crossParam (E.curve t) i k) := by
  have hjk : j ≠ k := by
    rintro rfl
    exact hne rfl
  have h0 : ∀ t : E.Parameter, crossParam (E.curve t) i j - crossParam (E.curve t) i k ≠ 0 := by
    intro t
    by_cases ht : t.val = 0
    · rw [curve_eq_center_of_val ht]
      exact sub_ne_zero.mpr hne
    · exact hZ.crossParam_sub_ne_zero ht hjk hij hik
  have := lt_zero_iff_of_ne_zero (hZ.continuous_crossParam_sub hij hik) h0 s t
  simpa only [sub_neg] using this

/-! ## Consequences of the forced RIII bundle -/

variable {e f g : ZMod n}
  {h3 : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g}
  {h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g}
  {h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ rep e < rep g}
  {h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ rep e < rep f}

theorem IsSimpleRIII.noG2Zero (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) : E.NoG2Zero := by
  intro a i h hm
  rw [hE.1] at hm
  simp at hm

theorem IsSimpleRIII.g3_mem (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    Member.g3 e f g h3 ∈ E.zeroSet := by
  rw [hE.1]; simp

theorem IsSimpleRIII.g4e_mem (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    Member.g4 e f g h4e ∈ E.zeroSet := by
  rw [hE.1]; simp

theorem IsSimpleRIII.g4f_mem (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    Member.g4 f e g h4f ∈ E.zeroSet := by
  rw [hE.1]; simp

theorem IsSimpleRIII.g4g_mem (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    Member.g4 g e f h4g ∈ E.zeroSet := by
  rw [hE.1]; simp

theorem IsSimpleRIII.ne (_hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) : e ≠ f ∧ e ≠ g ∧ f ≠ g :=
  ⟨h4g.2.2.1, h4f.2.2.1, h4e.2.2.1⟩

/-- The three bundle pairs are active at the centre ("concurrent at `t = 0`": the `G3` member of
`Z` is relevant at some `t ≠ 0`, hence active there, hence at the centre). -/
theorem IsSimpleRIII.crosses_center (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    Crosses E.center e f ∧ Crosses E.center f g ∧ Crosses E.center e g := by
  obtain ⟨_, t, _, hrel⟩ := hE.g3_mem
  exact hE.noG2Zero.active_center_of_relevant (Member.conditional_g3 e f g h3) hrel

/-- The three bundle pairs are active at every time of the event. -/
theorem IsSimpleRIII.crosses (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) (t : E.Parameter) :
    Crosses (E.curve t) e f ∧ Crosses (E.curve t) f g ∧ Crosses (E.curve t) e g :=
  ⟨(hE.noG2Zero.crosses_const e f E.zeroParameter t).mp hE.crosses_center.1,
   (hE.noG2Zero.crosses_const f g E.zeroParameter t).mp hE.crosses_center.2.1,
   (hE.noG2Zero.crosses_const e g E.zeroParameter t).mp hE.crosses_center.2.2⟩

/-- **Target shape** `LocalizationData.triangle_crossings` (for `t` punctured; true at every `t`):
"Let `T = {x_ef, x_eg, x_fg}`" — the three triangle crossings exist. -/
theorem IsSimpleRIII.isCrossing (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) (t : E.Parameter) :
    IsCrossing (E.curve t) {e, f} ∧ IsCrossing (E.curve t) {e, g} ∧ IsCrossing (E.curve t) {f, g} :=
  ⟨(hE.crosses t).1.isCrossing, (hE.crosses t).2.2.isCrossing, (hE.crosses t).2.1.isCrossing⟩

/-- **Target shape** `LocalizationData.crossing_set_constant` (1): "the crossing set, indexed by
carrying edge pairs, is constant" — on the whole interval, centre included (SM source:
`WallGerm.triple_sides_crossing_equiv`, `g1_center_side_crossings`). -/
theorem IsSimpleRIII.isCrossing_iff (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (t t' : E.Parameter) (s : Finset (ZMod n)) :
    IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s :=
  hE.noG2Zero.isCrossing_const t t' s

/-- At the centre the two crossings of each bundle edge tie (the three `G4` members vanish). -/
theorem IsSimpleRIII.tie_center (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    crossParam E.center e f = crossParam E.center e g ∧
    crossParam E.center f e = crossParam E.center f g ∧
    crossParam E.center g e = crossParam E.center g f := by
  obtain ⟨cef, cfg, ceg⟩ := hE.crosses_center
  have cfe := (crosses_comm _ _ _).mp cef
  have cge := (crosses_comm _ _ _).mp ceg
  have cgf := (crosses_comm _ _ _).mp cfg
  exact ⟨(G4_eq_zero_iff _ cef ceg).mp hE.g4e_mem.1, (G4_eq_zero_iff _ cfe cfg).mp hE.g4f_mem.1,
    (G4_eq_zero_iff _ cge cgf).mp hE.g4g_mem.1⟩

/-- A `G4` member of the zero set is one of the three printed ones. -/
theorem IsSimpleRIII.g4_mem_iff (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) {i j k : ZMod n}
    (h : remote i j ∧ remote i k ∧ j ≠ k ∧ rep j < rep k) :
    Member.g4 i j k h ∈ E.zeroSet ↔
      (i = e ∧ j = f ∧ k = g) ∨ (i = f ∧ j = e ∧ k = g) ∨ (i = g ∧ j = e ∧ k = f) := by
  rw [hE.1]
  simp

/-- A parameter tie at the centre between two active crossings on a common edge is a vanishing,
active, hence relevant `G4⟨i;j,k⟩`, hence a member of `Z`, hence one of the three printed `G4`s:
the support is the bundle (CV form of the accepted `uniqueTriple_parameter_tie_iff`, `→`). -/
theorem IsSimpleRIII.support_eq_of_tie (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {i j k : ZMod n} (hjk : j ≠ k) (hij : Crosses E.center i j) (hik : Crosses E.center i k)
    (htie : crossParam E.center i j = crossParam E.center i k) :
    ({i, j, k} : Finset (ZMod n)) = {e, f, g} := by
  have h4 : G4 E.center i j k = 0 := (G4_eq_zero_iff _ hij hik).mpr htie
  have hZ := hE.noG2Zero
  rcases rep_lt_or_lt hjk with hlt | hlt
  · have hm : Member.g4 i j k ⟨hij.remote, hik.remote, hjk, hlt⟩ ∈ E.zeroSet :=
      hZ.mem_zeroSet_of_active h4 ⟨hij, hik⟩
    rcases (hE.g4_mem_iff _).mp hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rfl
    · ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · have h4' : G4 E.center i k j = 0 := by rw [G4_swap, h4, neg_zero]
    have hm : Member.g4 i k j ⟨hik.remote, hij.remote, hjk.symm, hlt⟩ ∈ E.zeroSet :=
      hZ.mem_zeroSet_of_active h4' ⟨hik, hij⟩
    rcases (hE.g4_mem_iff _).mp hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- Conversely, every bundle order ties at the centre (CV form of `uniqueTriple_parameters_eq`). -/
theorem IsSimpleRIII.tie_of_support_eq (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {i j k : ZMod n} (hjk : j ≠ k) (hij : Crosses E.center i j) (hik : Crosses E.center i k)
    (hs : ({i, j, k} : Finset (ZMod n)) = {e, f, g}) :
    crossParam E.center i j = crossParam E.center i k := by
  obtain ⟨tef, tfe, tge⟩ := hE.tie_center
  rcases triple_support_six_orders hij.ne hik.ne hjk hs with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact tef
  · exact tef.symm
  · exact tfe
  · exact tfe.symm
  · exact tge
  · exact tge.symm

/-- CV form of the accepted `uniqueTriple_parameter_tie_iff`: at the centre exactly the three
bundle comparisons tie. -/
theorem IsSimpleRIII.tie_center_iff (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {i j k : ZMod n} (hjk : j ≠ k) (hij : Crosses E.center i j) (hik : Crosses E.center i k) :
    crossParam E.center i j = crossParam E.center i k ↔
      ({i, j, k} : Finset (ZMod n)) = {e, f, g} :=
  ⟨hE.support_eq_of_tie hjk hij hik, hE.tie_of_support_eq hjk hij hik⟩

theorem IsSimpleRIII.crossParam_ne_center (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {i j k : ZMod n} (hjk : j ≠ k) (hij : Crosses E.center i j) (hik : Crosses E.center i k)
    (hne : ({i, j, k} : Finset (ZMod n)) ≠ {e, f, g}) :
    crossParam E.center i j ≠ crossParam E.center i k :=
  fun h => hne (hE.support_eq_of_tie hjk hij hik h)

/-- Every same-edge order other than the three bundle orders is constant along the WHOLE event
interval, centre included (no tie at the centre, none on the generic sides). -/
theorem IsSimpleRIII.crossParam_lt_iff_of_ne (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {i j k : ZMod n} (hij : Crosses E.center i j) (hik : Crosses E.center i k)
    (hne : ({i, j, k} : Finset (ZMod n)) ≠ {e, f, g}) (s t : E.Parameter) :
    (crossParam (E.curve s) i j < crossParam (E.curve s) i k ↔
      crossParam (E.curve t) i j < crossParam (E.curve t) i k) := by
  by_cases hjk : j = k
  · subst k
    simp
  exact hE.noG2Zero.crossParam_lt_iff_of_center_ne hij hik
    (hE.crossParam_ne_center hjk hij hik hne) s t

/-- The accepted predicate `SM.TripleUnchangedOrders` (centre against any time `t`; SM source
`WallGerm.triple_other_orders_sides`, which had it only on the sides). -/
theorem IsSimpleRIII.tripleUnchangedOrders (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (t : E.Parameter) : TripleUnchangedOrders E.center (E.curve t) e f g := by
  intro i j k hij hik hne
  have hZ := hE.noG2Zero
  have hij' : Crosses E.center i j := (hZ.isCrossing_iff_crosses E.zeroParameter i j).mp hij
  have hik' : Crosses E.center i k := (hZ.isCrossing_iff_crosses E.zeroParameter i k).mp hik
  simp only [← crossParam_eq_edgeParameter]
  exact hE.crossParam_lt_iff_of_ne hij' hik' hne t E.zeroParameter

/-! ## The wall: the three bundle orders reverse (SM sources `WallGerm.triple_order_exchanges`,
`g1_parameter_signChange_sides`; the `G4` route of the accepted `Bridge.B3` read backwards) -/

/-- `K(t) = det(d_b, d_a) det(d_c, d_a)` along the event (BRIDGE.md B3). -/
def dirProd (E : Event n) (a b c : ZMod n) (t : E.Parameter) : ℝ :=
  det (edge (E.curve t) b) (edge (E.curve t) a) * det (edge (E.curve t) c) (edge (E.curve t) a)

theorem continuous_dirProd (E : Event n) (a b c : ZMod n) : Continuous (E.dirProd a b c) :=
  (continuous_det ((continuous_edge b).comp E.continuous_curve)
      ((continuous_edge a).comp E.continuous_curve)).mul
    (continuous_det ((continuous_edge c).comp E.continuous_curve)
      ((continuous_edge a).comp E.continuous_curve))

theorem NoG2Zero.dirProd_ne_zero (hZ : E.NoG2Zero) {a b c : ZMod n} (hab : Crosses E.center a b)
    (hac : Crosses E.center a c) (t : E.Parameter) : E.dirProd a b c t ≠ 0 :=
  mul_ne_zero ((hZ.crosses_const a b E.zeroParameter t).mp hab).det_ne_zero'
    ((hZ.crosses_const a c E.zeroParameter t).mp hac).det_ne_zero'

theorem NoG2Zero.dirProd_mul_pos (hZ : E.NoG2Zero) {a b c : ZMod n} (hab : Crosses E.center a b)
    (hac : Crosses E.center a c) (s t : E.Parameter) : 0 < E.dirProd a b c s * E.dirProd a b c t :=
  mul_pos_of_ne_zero_of_preconnected (E.continuous_dirProd a b c) (hZ.dirProd_ne_zero hab hac) s t

/-- A sign change of the member `G4_{a;b,c}` is a sign change of the parameter difference
`t_b − t_c` along `a` (BRIDGE.md (8) read backwards: `K(t) K(−t) > 0`). -/
theorem NoG2Zero.paramDiff_signChanges (hZ : E.NoG2Zero) {a b c : ZMod n}
    (hab : Crosses E.center a b) (hac : Crosses E.center a c)
    (hs : E.SignChanges (fun P => G4 P a b c)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ∀ s : E.SideParameter, s.val < δ →
      (crossParam (E.sideCurve true s) a b - crossParam (E.sideCurve true s) a c) *
        (crossParam (E.sideCurve false s) a b - crossParam (E.sideCurve false s) a c) < 0 := by
  obtain ⟨δ, hδ, hδr, h⟩ := hs
  refine ⟨δ, hδ, hδr, fun s hs => ?_⟩
  have hG : ∀ β : Bool, G4 (E.sideCurve β s) a b c =
      (crossParam (E.sideCurve β s) a b - crossParam (E.sideCurve β s) a c) *
        E.dirProd a b c (E.sideTime β s) :=
    fun β => G4_eq_crossParam_sub_mul ((hZ.crosses_const a b E.zeroParameter _).mp hab)
      ((hZ.crosses_const a c E.zeroParameter _).mp hac)
  have hprod : G4 (E.sideCurve true s) a b c * G4 (E.sideCurve false s) a b c < 0 := h s hs
  rw [hG true, hG false, mul_mul_mul_comm] at hprod
  exact neg_of_mul_neg_left hprod (hZ.dirProd_mul_pos hab hac _ _).le

/-- Between ANY positive time and ANY negative time the order of `b, c` along `a` is reversed
(both directions), once `G4_{a;b,c}` changes sign: the sign change at one small time and
same-side constancy on each connected side (CV form of the accepted
`WallGerm.g1_parameter_signChange_sides`). -/
theorem NoG2Zero.orders_reverse_of_signChanges (hZ : E.NoG2Zero) {a b c : ZMod n}
    (hab : Crosses E.center a b) (hac : Crosses E.center a c)
    (hs : E.SignChanges (fun P => G4 P a b c)) (s t : E.SideParameter) :
    (crossParam (E.sideCurve true s) a b < crossParam (E.sideCurve true s) a c ↔
      crossParam (E.sideCurve false t) a c < crossParam (E.sideCurve false t) a b) ∧
    (crossParam (E.sideCurve true s) a c < crossParam (E.sideCurve true s) a b ↔
      crossParam (E.sideCurve false t) a b < crossParam (E.sideCurve false t) a c) := by
  obtain ⟨δ, hδ, _, hlocal⟩ := hZ.paramDiff_signChanges hab hac hs
  let t₀ : E.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by
    show δ / 2 < δ
    linarith
  have hswap := opposite_difference_orders (hlocal t₀ ht₀)
  exact ⟨(hZ.crossParam_lt_iff_side hab hac true s t₀).trans
      (hswap.1.trans (hZ.crossParam_lt_iff_side hac hab false t₀ t)),
    (hZ.crossParam_lt_iff_side hac hab true s t₀).trans
      (hswap.2.trans (hZ.crossParam_lt_iff_side hab hac false t₀ t))⟩

/-- Two times of opposite signs: one is `+s`, the other `−s'`. -/
theorem opposite_sides_cases {t t' : E.Parameter} (h : t.val * t'.val < 0) :
    (∃ s s' : E.SideParameter, E.sideTime true s = t ∧ E.sideTime false s' = t') ∨
    (∃ s s' : E.SideParameter, E.sideTime false s = t ∧ E.sideTime true s' = t') := by
  rcases mul_neg_iff.mp h with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · left
    refine ⟨⟨t.val, hpos, t.property.2⟩, ⟨-t'.val, by constructor <;> linarith [t'.property.1]⟩,
      rfl, ?_⟩
    apply Subtype.ext
    simp [sideTime]
  · right
    refine ⟨⟨-t.val, by constructor <;> linarith [t.property.1]⟩, ⟨t'.val, hpos, t'.property.2⟩,
      ?_, rfl⟩
    apply Subtype.ext
    simp [sideTime]

/-- Two times of the same sign lie on one side. -/
theorem same_side_cases {t t' : E.Parameter} (h : 0 < t.val * t'.val) :
    ∃ (b : Bool) (s s' : E.SideParameter), E.sideTime b s = t ∧ E.sideTime b s' = t' := by
  rcases mul_pos_iff.mp h with ⟨hpos, hpos'⟩ | ⟨hneg, hneg'⟩
  · exact ⟨true, ⟨t.val, hpos, t.property.2⟩, ⟨t'.val, hpos', t'.property.2⟩, rfl, rfl⟩
  · refine ⟨false, ⟨-t.val, by constructor <;> linarith [t.property.1]⟩,
      ⟨-t'.val, by constructor <;> linarith [t'.property.1]⟩, ?_, ?_⟩ <;>
    · apply Subtype.ext
      simp [sideTime]

/-- The three printed `G4` members change sign (transversality of the forced bundle). -/
theorem IsSimpleRIII.signChanges_G4 (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    E.SignChanges (fun P => G4 P e f g) ∧ E.SignChanges (fun P => G4 P f e g) ∧
      E.SignChanges (fun P => G4 P g e f) :=
  ⟨hE.2.2 _ hE.g4e_mem, hE.2.2 _ hE.g4f_mem, hE.2.2 _ hE.g4g_mem⟩

/-- SM source `WallGerm.triple_order_exchanges`: between any positive and any negative time the
three bundle orders reverse. -/
theorem IsSimpleRIII.triangleCrossParamExchanges_sides (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (s t : E.SideParameter) :
    TriangleCrossParamExchanges (E.sideCurve true s) (E.sideCurve false t) e f g := by
  obtain ⟨cef, cfg, ceg⟩ := hE.crosses_center
  have cfe := (crosses_comm _ _ _).mp cef
  have cge := (crosses_comm _ _ _).mp ceg
  have cgf := (crosses_comm _ _ _).mp cfg
  obtain ⟨se, sf, sg⟩ := hE.signChanges_G4
  have hZ := hE.noG2Zero
  exact ⟨hZ.orders_reverse_of_signChanges cef ceg se s t,
    hZ.orders_reverse_of_signChanges cfe cfg sf s t,
    hZ.orders_reverse_of_signChanges cge cgf sg s t⟩

/-- **Target shape** `LocalizationData.order_reverses` (2): "their order along that edge is opposite
on the two sides" (`OppositeSides E t t'` is `t.val * t'.val < 0`; the conclusion unfolds to the
printed twelve-term conjunction). -/
theorem IsSimpleRIII.order_reverses (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (t t' : E.Parameter) (h : t.val * t'.val < 0) :
    TriangleCrossParamExchanges (E.curve t) (E.curve t') e f g := by
  rcases opposite_sides_cases h with ⟨s, s', rfl, rfl⟩ | ⟨s, s', rfl, rfl⟩
  · exact hE.triangleCrossParamExchanges_sides s s'
  · exact (hE.triangleCrossParamExchanges_sides s' s).symm

/-- **Target shape** `LocalizationData.order_same_side`: on one side (`SameSide E t t'` is
`0 < t.val * t'.val`) every same-edge order is constant. Only `NoG2Zero` is used. -/
theorem IsSimpleRIII.order_same_side (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (t t' : E.Parameter) (h : 0 < t.val * t'.val) (i j k : ZMod n)
    (hij : IsCrossing (E.curve t) {i, j}) (hik : IsCrossing (E.curve t) {i, k}) :
    (crossParam (E.curve t) i j < crossParam (E.curve t) i k ↔
      crossParam (E.curve t') i j < crossParam (E.curve t') i k) := by
  have hZ := hE.noG2Zero
  have hij' : Crosses E.center i j :=
    (hZ.crosses_const i j t E.zeroParameter).mp ((hZ.isCrossing_iff_crosses t i j).mp hij)
  have hik' : Crosses E.center i k :=
    (hZ.crosses_const i k t E.zeroParameter).mp ((hZ.isCrossing_iff_crosses t i k).mp hik)
  obtain ⟨b, s, s', rfl, rfl⟩ := same_side_cases h
  exact hZ.crossParam_lt_iff_side hij' hik' b s s'

/-- **Target shape** `LocalizationData.other_orders_persist` (3): "every other pair of crossings
keeps its order along every edge" — for ANY two times (the field asks it for opposite sides), the
pair being "other than a bundle pair" in the printed form `¬ ({h, i} ∈ T ∧ {h, j} ∈ T)` with
`T = triangleSupports e f g = {{e, f}, {e, g}, {f, g}}`. SM source
`WallGerm.triple_other_orders_sides` / `uniqueTriple_other_orders_persist`. -/
theorem IsSimpleRIII.other_orders_persist (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (t t' : E.Parameter) (h i j : ZMod n)
    (hhi : IsCrossing (E.curve t) {h, i}) (hhj : IsCrossing (E.curve t) {h, j})
    (hnot : ¬ (({h, i} : Finset (ZMod n)) ∈ ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n))) ∧
      ({h, j} : Finset (ZMod n)) ∈ ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n))))) :
    (crossParam (E.curve t) h i < crossParam (E.curve t) h j ↔
      crossParam (E.curve t') h i < crossParam (E.curve t') h j) := by
  have hZ := hE.noG2Zero
  have hhi' : Crosses E.center h i :=
    (hZ.crosses_const h i t E.zeroParameter).mp ((hZ.isCrossing_iff_crosses t h i).mp hhi)
  have hhj' : Crosses E.center h j :=
    (hZ.crosses_const h j t E.zeroParameter).mp ((hZ.isCrossing_iff_crosses t h j).mp hhj)
  by_cases hij : i = j
  · subst j
    simp
  apply hE.crossParam_lt_iff_of_ne hhi' hhj'
  intro hs
  exact hnot (pairs_mem_of_support_eq hhi'.ne hhj'.ne hij hs)

/-- The accepted `SM.ExactTriangleParameterOrders` between opposite sides (SM source
`WallGerm.triple_exact_parameter_orders`). -/
theorem IsSimpleRIII.exactTriangleParameterOrders (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {t t' : E.Parameter} (h : t.val * t'.val < 0) :
    ExactTriangleParameterOrders (E.curve t) (E.curve t') e f g := by
  have hZ := hE.noG2Zero
  obtain ⟨hef, heg, hfg⟩ := hE.ne
  have hcard : ({e, f, g} : Finset (ZMod n)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hef, heg, hfg⟩
  intro i j k hij hik
  have hij' : Crosses E.center i j :=
    (hZ.crosses_const i j t E.zeroParameter).mp ((hZ.isCrossing_iff_crosses t i j).mp hij)
  have hik' : Crosses E.center i k :=
    (hZ.crosses_const i k t E.zeroParameter).mp ((hZ.isCrossing_iff_crosses t i k).mp hik)
  constructor
  · intro hs
    have hd : i ≠ j ∧ i ≠ k ∧ j ≠ k :=
      Finset.card_triple_eq_three_iff.mp (by rw [hs]; exact hcard)
    exact triangleOrderExchanges_all
      ((triangleCrossParamExchanges_iff _ _ _ _ _).mp (hE.order_reverses t t' h)) hd.1 hd.2.1 hd.2.2 hs
  · intro hne
    simpa only [crossParam_eq_edgeParameter] using hE.crossParam_lt_iff_of_ne hij' hik' hne t t'

/-- **Target shape** `LocalizationData.gauss_words`: "the two Gauss words differ by exactly the three
transpositions" — the accepted `SM.ExactTriangleVisitOrders` between opposite sides, transported
along the crossing equivalence `hs` (SM source `WallGerm.triple_exact_visit_orders`). -/
theorem IsSimpleRIII.exactTriangleVisitOrders (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {t t' : E.Parameter} (h : t.val * t'.val < 0)
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s) :
    ExactTriangleVisitOrders (E.curve t) (E.curve t') e f g hs :=
  exactTriangleVisitOrders_of_parameters_of_geometry
    (E.generic_punctured t (left_ne_zero_of_mul h.ne)).crossingGeometry
    (E.generic_punctured t' (right_ne_zero_of_mul h.ne)).crossingGeometry hs
    (hE.exactTriangleParameterOrders h)

/-! ## Adjacency of the bundle-pair visits (SM sources `uniqueTriple_outside_persists`,
`pairVisits_adjacent`, `tripleSides_of_outside`, `triple_sides`) -/

/-- For every third edge `h` crossing the bundle edge `i` (at any time), its parameter along `i`
stays on one side of the tied pair `t_j = t_k` along the WHOLE event: the two differences
`t_h − t_j`, `t_h − t_k` never vanish (not at the centre, `{i, h, j} ≠ {e, f, g}`; not on the generic
sides) and agree at the centre. -/
theorem IsSimpleRIII.otherCrossingsOutside_edge (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {i j k : ZMod n} (hs : ({i, j, k} : Finset (ZMod n)) = {e, f, g})
    (hij : Crosses E.center i j) (hik : Crosses E.center i k) (hjk : j ≠ k) (t : E.Parameter) :
    OtherCrossingsOutside (E.curve t) i j k := by
  intro h _ hhj hhk hc
  have hZ := hE.noG2Zero
  have hih : Crosses E.center i h :=
    (hZ.crosses_const i h t E.zeroParameter).mp ((hZ.isCrossing_iff_crosses t i h).mp hc)
  have hne_j : ({i, h, j} : Finset (ZMod n)) ≠ {e, f, g} := by
    intro hs'
    have hk : k ∈ ({i, h, j} : Finset (ZMod n)) := by rw [hs', ← hs]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk | hk | hk
    · exact hik.ne hk.symm
    · exact hhk hk.symm
    · exact hjk hk.symm
  have hne_k : ({i, h, k} : Finset (ZMod n)) ≠ {e, f, g} := by
    intro hs'
    have hj : j ∈ ({i, h, k} : Finset (ZMod n)) := by rw [hs', ← hs]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj | hj
    · exact hij.ne hj.symm
    · exact hhj hj.symm
    · exact hjk hj
  have hdj := hE.crossParam_ne_center hhj hih hij hne_j
  have hdk := hE.crossParam_ne_center hhk hih hik hne_k
  have htie : crossParam E.center i j = crossParam E.center i k := hE.tie_of_support_eq hjk hij hik hs
  have h1 := hZ.crossParam_lt_iff_of_center_ne hih hij hdj t E.zeroParameter
  have h2 := hZ.crossParam_lt_iff_of_center_ne hij hih hdj.symm t E.zeroParameter
  have h3 := hZ.crossParam_lt_iff_of_center_ne hih hik hdk t E.zeroParameter
  have h4 := hZ.crossParam_lt_iff_of_center_ne hik hih hdk.symm t E.zeroParameter
  unfold OutsidePair
  simp only [← crossParam_eq_edgeParameter]
  rcases lt_or_gt_of_ne hdj with hlt | hgt
  · exact Or.inl ⟨h1.mpr hlt, h3.mpr (lt_of_lt_of_eq hlt htie)⟩
  · exact Or.inr ⟨h2.mpr hgt, h4.mpr (lt_of_eq_of_lt htie.symm hgt)⟩

/-- The outside condition on the three bundle edges, at every time of the event (SM source
`uniqueTriple_outside_persists`, which had it only eventually near the centre). -/
theorem IsSimpleRIII.otherCrossingsOutside (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (t : E.Parameter) :
    OtherCrossingsOutside (E.curve t) e f g ∧ OtherCrossingsOutside (E.curve t) f e g ∧
      OtherCrossingsOutside (E.curve t) g e f := by
  obtain ⟨cef, cfg, ceg⟩ := hE.crosses_center
  obtain ⟨hef, heg, hfg⟩ := hE.ne
  refine ⟨hE.otherCrossingsOutside_edge rfl cef ceg hfg t,
    hE.otherCrossingsOutside_edge ?_ ((crosses_comm _ _ _).mp cef) cfg heg t,
    hE.otherCrossingsOutside_edge ?_ ((crosses_comm _ _ _).mp ceg) ((crosses_comm _ _ _).mp cfg)
      hef t⟩
  · exact Finset.insert_comm _ _ _
  · ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- **Target shape** `LocalizationData.adjacent` (2b) at a punctured time `t` (any `t ≠ 0`, no
radius): "on each of `e, f, g` the two crossings of `T` carried by that edge occupy adjacent
crossing-visits of the traversal circle" — on `e` the visits of `x_ef, x_eg`; on `f` those of
`x_ef, x_fg`; on `g` those of `x_eg, x_fg`; `visitOfPair hc h _` is `visitOn (xPair hc) h _` and
`EmptyArcAdjacent` is `AdjacentVisits` (identical bodies), so the field is discharged by `exact`
(proof irrelevance identifies `geomAt E t _` with `(E.generic_punctured t _).crossingGeometry`). -/
theorem IsSimpleRIII.adjacent (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) {t : E.Parameter}
    (ht : t.val ≠ 0) (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) :
    EmptyArcAdjacent (E.generic_punctured t ht).crossingGeometry
      (visitOfPair hef e (by simp)) (visitOfPair heg e (by simp)) ∧
    EmptyArcAdjacent (E.generic_punctured t ht).crossingGeometry
      (visitOfPair hef f (by simp)) (visitOfPair hfg f (by simp)) ∧
    EmptyArcAdjacent (E.generic_punctured t ht).crossingGeometry
      (visitOfPair heg g (by simp)) (visitOfPair hfg g (by simp)) := by
  obtain ⟨oe, of, og⟩ := hE.otherCrossingsOutside t
  obtain ⟨hef', heg', hfg'⟩ := hE.ne
  exact ⟨emptyArcAdjacent_of_outside _ hfg' rfl rfl rfl rfl oe,
    emptyArcAdjacent_of_outside _ heg' rfl rfl (Finset.pair_comm e f) rfl of,
    emptyArcAdjacent_of_outside _ hef' rfl rfl (Finset.pair_comm e g) (Finset.pair_comm f g) og⟩

/-- SM source `triple_sides` (lem:triple-sides): the CV form `GeometricTripleSides` at every
punctured time. -/
theorem IsSimpleRIII.geometricTripleSides (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {t : E.Parameter} (ht : t.val ≠ 0) :
    GeometricTripleSides (E.generic_punctured t ht).crossingGeometry e f g := by
  obtain ⟨hef, heg, hfg⟩ := hE.isCrossing t
  obtain ⟨oe, of, og⟩ := hE.otherCrossingsOutside t
  obtain ⟨nef, neg, nfg⟩ := hE.ne
  have hP := (E.generic_punctured t ht).crossingGeometry
  refine ⟨hef, heg, hfg, crossingPoints_ne_of_geometry hP ?_, crossingPoints_ne_of_geometry hP ?_,
    crossingPoints_ne_of_geometry hP ?_, emptyArcAdjacent_of_outside hP nfg rfl rfl rfl rfl oe,
    emptyArcAdjacent_of_outside hP neg rfl rfl rfl rfl of,
    emptyArcAdjacent_of_outside hP nef rfl rfl rfl rfl og⟩
  · exact pair_ne_of_not_mem_right (by simp [Ne.symm nef, nfg])
  · exact pair_ne_of_not_mem_left (by simp [nef, neg])
  · exact pair_ne_of_not_mem_left (by simp [nef, neg])

/-! ## Same-side transport of the interlacement graph (bonus for `interlace_same_side`) -/

/-- The accepted `SM.CrossingParameterOrderAgrees` between two times of one side. -/
theorem IsSimpleRIII.crossingParameterOrderAgrees_same_side
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) {t t' : E.Parameter} (h : 0 < t.val * t'.val) :
    CrossingParameterOrderAgrees (E.curve t) (E.curve t') := by
  intro i j k hij hik
  simp only [← crossParam_eq_edgeParameter]
  exact (hE.order_same_side t t' h i j k hij hik).symm

/-- **Target shape** `LocalizationData.interlace_same_side`: the interlacement graph is the same at
any two times of one side (the accepted `geometric_interlaces_transport`). -/
theorem IsSimpleRIII.interlace_same_side (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {t t' : E.Parameter} (ht : t.val ≠ 0) (ht' : t'.val ≠ 0) (h : 0 < t.val * t'.val)
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s) (x y : Crossing (E.curve t)) :
    (GeometricInterlaces (E.generic_punctured t' ht').crossingGeometry (crossingTransport hs x)
        (crossingTransport hs y) ↔
      GeometricInterlaces (E.generic_punctured t ht).crossingGeometry x y) :=
  (geometric_interlaces_transport _ _ hs (hE.crossingParameterOrderAgrees_same_side h) x y).symm

/-! ## The bundle -/

/-- The clauses of `RProof.LocalizationData` proved by this unit, each in the field's exact body
shape, with `t.val ≠ 0` in place of `Punctured E δ t` (every clause holds on the whole punctured
interval, so the localization unit may take `δ := E.radius`), `t.val * t'.val < 0` for
`OppositeSides E t t'` and `0 < t.val * t'.val` for `SameSide E t t'`. Not included (unit L3):
`interlace_toggle` and its corollary `complement_on_triangle`. -/
structure TripleEventData (E : Event n) (e f g : ZMod n) : Prop where
  triangle_crossings : ∀ t : E.Parameter,
    IsCrossing (E.curve t) {e, f} ∧ IsCrossing (E.curve t) {e, g} ∧ IsCrossing (E.curve t) {f, g}
  crossing_set_constant : ∀ t t' : E.Parameter,
    ∀ s : Finset (ZMod n), IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s
  adjacent : ∀ t : E.Parameter, ∀ ht : t.val ≠ 0,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyArcAdjacent (E.generic_punctured t ht).crossingGeometry
      (visitOfPair hef e (by simp)) (visitOfPair heg e (by simp)) ∧
    EmptyArcAdjacent (E.generic_punctured t ht).crossingGeometry
      (visitOfPair hef f (by simp)) (visitOfPair hfg f (by simp)) ∧
    EmptyArcAdjacent (E.generic_punctured t ht).crossingGeometry
      (visitOfPair heg g (by simp)) (visitOfPair hfg g (by simp))
  order_reverses : ∀ t t' : E.Parameter, t.val * t'.val < 0 →
    TriangleCrossParamExchanges (E.curve t) (E.curve t') e f g
  order_same_side : ∀ t t' : E.Parameter, 0 < t.val * t'.val →
    ∀ h i j : ZMod n, IsCrossing (E.curve t) {h, i} → IsCrossing (E.curve t) {h, j} →
      (crossParam (E.curve t) h i < crossParam (E.curve t) h j ↔
        crossParam (E.curve t') h i < crossParam (E.curve t') h j)
  other_orders_persist : ∀ t t' : E.Parameter,
    ∀ h i j : ZMod n, IsCrossing (E.curve t) {h, i} → IsCrossing (E.curve t) {h, j} →
      ¬ (({h, i} : Finset (ZMod n)) ∈ ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n))) ∧
          ({h, j} : Finset (ZMod n)) ∈ ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n)))) →
      (crossParam (E.curve t) h i < crossParam (E.curve t) h j ↔
        crossParam (E.curve t') h i < crossParam (E.curve t') h j)
  gauss_words : ∀ t t' : E.Parameter, t.val * t'.val < 0 →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
      ExactTriangleVisitOrders (E.curve t) (E.curve t') e f g hs
  interlace_same_side : ∀ t t' : E.Parameter, ∀ ht : t.val ≠ 0, ∀ ht' : t'.val ≠ 0,
    0 < t.val * t'.val →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t),
      (GeometricInterlaces (E.generic_punctured t' ht').crossingGeometry (crossingTransport hs x)
          (crossingTransport hs y) ↔
        GeometricInterlaces (E.generic_punctured t ht).crossingGeometry x y)

/-- **Unit U8**: every simple transversal RIII event of CV ax:R satisfies the bundle. -/
theorem IsSimpleRIII.tripleEventData (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    TripleEventData E e f g where
  triangle_crossings := hE.isCrossing
  crossing_set_constant := hE.isCrossing_iff
  adjacent := fun _ ht hef heg hfg => hE.adjacent ht hef heg hfg
  order_reverses := hE.order_reverses
  order_same_side := hE.order_same_side
  other_orders_persist := hE.other_orders_persist
  gauss_words := fun _ _ h hs => hE.exactTriangleVisitOrders h hs
  interlace_same_side := fun _ _ ht ht' h hs x y => hE.interlace_same_side ht ht' h hs x y

end Event

end CV
