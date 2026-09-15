import CV.Events
import SM.NamedWallPredicates
import SM.TripleOrder
import SM.UnorderedWallTriples

/-! Bridge lane, rows 179 (Bridge:B1) and 180 (Bridge:B2).
Source: reference/BRIDGE/BRIDGE.md §2, B1 at lines 159–446 and B2 at 448–491; coordinates as in
BRIDGE.md §0 (SM_MAP): `p_i = μ_i`, `d_i = edge P i`, CV's `e_i` is SM's `E_i`, one-based tails on
both sides, so a CV polygon and an SM labelled tuple are the same `LabelledTuple n`.

**Lemma B1** (BRIDGE.md:161–169). "With the labelled coordinate identification of §0,
`𝓤_n^SM ⊆ 𝓤_n^CV`. (1) Every SM11 wall germ satisfying the central conditions of type `T` is a CV
event. This assertion is restricted to that central type; it does not assert that every type of
SM wall is a CV event."

**Lemma B2** (BRIDGE.md:450–453). "For the germ in B1, its CV zero set is
`Z = {G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}`. (3) These are four *indexed members*."

Library facts consumed (all accepted): clause (1) is `CV.generic_of_sm` (row 132, CV/Setup.lean);
the SM germ and its type-`T` centre are `SM.WallGerm`, `WallGerm.TripleAt` (pointZeros = ∅,
concurrences = {{e,f,k}}, three parameter-difference sign changes; SM/NamedWallPredicates.lean),
`WallGerm.pointZeros_empty_iff`, `WallGerm.mem_concurrences`; the CV event is `CV.Event`
(row 148, CV/Events.lean); the concurrency/determinant link is `CV.G3_eq_zero_of_common_point`; the
parameter-tie link for B2 is `CV.G4_eq_zero_iff`, `CV.crossParam_eq_edgeParameter` and SM's
`uniqueTriple_parameter_tie_iff` (SM/TripleOrder.lean).

Shape decisions.
* `eventOfTriple hn g h : CV.Event n` has `radius := g.radius` and `curve := g.curve`
  definitionally, so `(eventOfTriple hn g h).curve = g.curve` and
  `(eventOfTriple hn g h).center = g.center` are `rfl`. In the existential statement of `B1` the
  curve identity is stated pointwise on the real parameter with both membership proofs, because
  the two parameter subtypes `Set.Ioo (-E.radius) E.radius` and `Set.Ioo (-g.radius) g.radius` are
  only propositionally equal for a bound `E`.
* `hn : 3 ≤ n` is a binder of `eventOfTriple` (needed for `generic_of_sm` and for the centre to
  have nonzero edges); `[NeZero n]` is required by `WallGerm.pointZeros` and by `CV.Member`.
* B2 is stated for the increasing representatives `rep e < rep f < rep k` of the central triple,
  which is BRIDGE.md §0's convention "when naming the central triple, choose `e<f<g` in those
  representatives"; `TripleAt` is invariant under permuting the triple
  (`WallGerm.tripleAt_support_iff`), and `exists_sorted_tripleAt` below produces such a naming. -/

namespace Bridge

open SM

variable {n : ℕ} [NeZero n]

/-! ### The centre of a type-`T` germ -/

/-- `Z_pt = ∅` is SM (G1) at the centre (BRIDGE.md B1: "At the centre, `Z_pt = ∅` says that the SM
point-triple condition still holds"). -/
theorem tripleAt_g1_center {g : WallGerm n} {e f k : ZMod n} (h : g.TripleAt e f k) :
    G1 g.center :=
  (g.pointZeros_empty_iff).mp h.1

/-- `Z_c = {{e,f,g}}` "specifies pairwise remote edges and a point `q` interior to all three"
(BRIDGE.md B1). -/
theorem tripleAt_remote_and_common_point {g : WallGerm n} {e f k : ZMod n}
    (h : g.TripleAt e f k) :
    remote e f ∧ remote f k ∧ remote e k ∧
      ∃ q : Plane, q ∈ edgeInterior g.center e ∧ q ∈ edgeInterior g.center f ∧
        q ∈ edgeInterior g.center k :=
  uniqueTriple_data h.2.1

theorem tripleAt_remote_ef {g : WallGerm n} {e f k : ZMod n} (h : g.TripleAt e f k) :
    remote e f := (tripleAt_remote_and_common_point h).1

theorem tripleAt_remote_fk {g : WallGerm n} {e f k : ZMod n} (h : g.TripleAt e f k) :
    remote f k := (tripleAt_remote_and_common_point h).2.1

theorem tripleAt_remote_ek {g : WallGerm n} {e f k : ZMod n} (h : g.TripleAt e f k) :
    remote e k := (tripleAt_remote_and_common_point h).2.2.1

omit [NeZero n] in
/-- Under SM (G1), two remote edges with a common interior point satisfy CV's strict four-sign
activation test (BRIDGE.md B1: "The three pairs satisfy CV's strict crossing activation at the
centre"; the test is `CV.crosses_iff`, "exactly a transverse interior crossing"). -/
theorem crosses_of_common_interior [Nontrivial (ZMod n)] {P : LabelledTuple n} (hP : G1 P)
    {e f : ZMod n} (hr : remote e f) {q : Plane}
    (he : q ∈ edgeInterior P e) (hf : q ∈ edgeInterior P f) : CV.Crosses P e f := by
  obtain ⟨s, hs0, hs1, hs⟩ := he
  obtain ⟨t, ht0, ht1, ht⟩ := hf
  have heq : edgePoint P e s = edgePoint P f t := hs.symm.trans ht
  exact (CV.crosses_iff P e f).mpr
    ⟨hr, s, t, hs0, hs1, ht0, ht1, heq, g1_remote_intersection_det hP hr heq⟩

/-- The centre "has nonzero edges and is also a CV polygon" (BRIDGE.md B1). -/
theorem tripleAt_center_isPolygon (hn : 3 ≤ n) {g : WallGerm n} {e f k : ZMod n}
    (h : g.TripleAt e f k) : CV.IsPolygon g.center := by
  have : Fact (1 < n) := ⟨by omega⟩
  exact g1_edge_ne_zero hn (tripleAt_g1_center h)

/-- The three central activations of the concurrent triple. -/
theorem tripleAt_crosses_center (hn : 3 ≤ n) {g : WallGerm n} {e f k : ZMod n}
    (h : g.TripleAt e f k) :
    CV.Crosses g.center e f ∧ CV.Crosses g.center f k ∧ CV.Crosses g.center e k := by
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨hef, hfk, hek, q, hqe, hqf, hqk⟩ := (tripleAt_remote_and_common_point h)
  exact ⟨crosses_of_common_interior (tripleAt_g1_center h) hef hqe hqf,
    crosses_of_common_interior (tripleAt_g1_center h) hfk hqf hqk,
    crosses_of_common_interior (tripleAt_g1_center h) hek hqe hqk⟩

/-- "Their coefficient matrix annihilates `(q_1,q_2,1)^T`, so its determinant `G3` is zero"
(BRIDGE.md B1). -/
theorem tripleAt_G3_center {g : WallGerm n} {e f k : ZMod n} (h : g.TripleAt e f k) :
    CV.G3 g.center e f k = 0 := by
  obtain ⟨_, _, _, q, hqe, hqf, hqk⟩ := (tripleAt_remote_and_common_point h)
  exact CV.G3_eq_zero_of_common_point _ e f k
    (CV.lineForm_eq_zero_of_mem _ _ (edgeInterior_subset_edgeSegment _ _ hqe))
    (CV.lineForm_eq_zero_of_mem _ _ (edgeInterior_subset_edgeSegment _ _ hqf))
    (CV.lineForm_eq_zero_of_mem _ _ (edgeInterior_subset_edgeSegment _ _ hqk))

/-- "This is an active, hence relevant, zero guard; the centre is not CV-generic" (BRIDGE.md B1). -/
theorem tripleAt_center_not_cv_generic (hn : 3 ≤ n) {g : WallGerm n} {e f k : ZMod n}
    (h : g.TripleAt e f k) : ¬ CV.Generic g.center := by
  intro hP
  obtain ⟨cef, cfk, cek⟩ := tripleAt_crosses_center hn h
  exact hP.g3 cef cfk cek (tripleAt_G3_center h)

/-! ### The CV event of a type-`T` germ -/

/-- The CV event carried by an SM wall germ of type `T` (BRIDGE.md B1, second assertion): the same
radius, the same curve, punctured values CV-generic by clause (1) (`CV.generic_of_sm`), the centre
a CV polygon with the active `G3` of the concurrent triple vanishing. -/
def eventOfTriple (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n} (h : g.TripleAt e f k) :
    CV.Event n where
  radius := g.radius
  radius_pos := g.radius_pos
  curve := g.curve
  continuous_curve := g.continuous_curve
  center_polygon := tripleAt_center_isPolygon hn h
  generic_punctured := fun t ht => CV.generic_of_sm hn (g.generic_punctured t ht)
  nongeneric_center := tripleAt_center_not_cv_generic hn h

theorem eventOfTriple_radius (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) : (eventOfTriple hn g h).radius = g.radius := rfl

theorem eventOfTriple_curve (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) : (eventOfTriple hn g h).curve = g.curve := rfl

theorem eventOfTriple_center (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) : (eventOfTriple hn g h).center = g.center := rfl

theorem eventOfTriple_sideCurve (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (b : Bool) (t : g.SideParameter) :
    (eventOfTriple hn g h).sideCurve b t = (g.sideTuple b t).val := rfl

/-- **Bridge B1** (BRIDGE.md:161–169). "With the labelled coordinate identification of §0,
`𝓤_n^SM ⊆ 𝓤_n^CV`. (1) Every SM11 wall germ satisfying the central conditions of type `T` is a CV
event. This assertion is restricted to that central type; it does not assert that every type of
SM wall is a CV event."

Clause (1) is the inclusion of labelled generic loci; clause (2) produces, for every SM wall germ
`g` with `g.TripleAt e f k`, a CV event with the same radius and the same curve (stated pointwise
on the real parameter), whose centre `g.center` is not CV-generic. -/
theorem B1 (hn : 3 ≤ n) :
    (∀ P : LabelledTuple n, SM.Generic P → CV.Generic P) ∧
    (∀ (g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k →
      ∃ E : CV.Event n, E.radius = g.radius ∧
        (∀ (t : ℝ) (hE : t ∈ Set.Ioo (-E.radius) E.radius)
            (hg : t ∈ Set.Ioo (-g.radius) g.radius), E.curve ⟨t, hE⟩ = g.curve ⟨t, hg⟩) ∧
        ¬ CV.Generic g.center) :=
  ⟨fun _ hP => CV.generic_of_sm hn hP,
   fun g _ _ _ h => ⟨eventOfTriple hn g h, rfl, fun _ _ _ => rfl, tripleAt_center_not_cv_generic hn h⟩⟩


/-! ### B2: the relevance quantifier

BRIDGE.md B2, "Proof: the relevance quantifier": on every punctured value SM (G1) holds, and at
zero it holds because `Z_pt = ∅`; so every unconditional CV member is nonzero at **every** time of
the germ interval, each is continuous, and "a nonzero continuous real function on an interval has
constant sign: if two values had opposite signs, the intermediate value theorem would give a zero
between them". CV's strict crossing tests are products of `G2` values, so every activation
predicate is constant on the whole interval; "for a conditional member, being relevant at *some*
nonzero time is consequently equivalent to being active at the centre". -/

/-- SM (G1) at every time of a germ with `Z_pt = ∅`. -/
theorem g1_all {g : WallGerm n} (hz : g.pointZeros = ∅) (t : g.Parameter) : G1 (g.curve t) := by
  by_cases ht : t.val = 0
  · have : t = g.zeroParameter := Subtype.ext ht
    rw [this]
    exact (g.pointZeros_empty_iff).mp hz
  · exact (g.generic_punctured t ht).1

omit [NeZero n] in
/-- CV's `G2_{e,i}` (`i ∉ {e, e+1}`) is the determinant of the three distinct vertices `e, e+1, i`,
nonzero under SM (G1) (BRIDGE.md B1: "CV's `G2_{a,i}` is directly the determinant of the distinct
vertices `(a,a+1,i)`, so it too is nonzero"). -/
theorem cvG2_ne_zero_of_g1 [Nontrivial (ZMod n)] {P : LabelledTuple n} (hP : G1 P) {e i : ZMod n}
    (h0 : i ≠ e) (h1 : i ≠ e + 1) : CV.G2 P e i ≠ 0 :=
  g1_area_ne_zero hP (next_ne_self e).symm h1.symm h0.symm

/-- Every unconditional `G2` member is nonzero at every time of the germ interval. -/
theorem cvG2_ne_zero_all (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) (t : g.Parameter)
    {e i : ZMod n} (h0 : i ≠ e) (h1 : i ≠ e + 1) : CV.G2 (g.curve t) e i ≠ 0 := by
  have : Fact (1 < n) := ⟨by omega⟩
  exact cvG2_ne_zero_of_g1 (g1_all hz t) h0 h1

omit [NeZero n] in
/-- The intermediate value theorem in the form used by BRIDGE.md B2: a continuous real function
without zeros on a preconnected space has constant sign. -/
theorem neg_iff_of_ne_zero {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {φ : X → ℝ} (hφ : Continuous φ) (h0 : ∀ x, φ x ≠ 0) (a b : X) : φ a < 0 ↔ φ b < 0 := by
  have key : ∀ a b : X, φ a < 0 → φ b < 0 := by
    intro a b ha
    by_contra hb
    have hb' : 0 < φ b := lt_of_le_of_ne (not_lt.mp hb) (h0 b).symm
    obtain ⟨x, hx⟩ := intermediate_value_univ a b hφ ⟨ha.le, hb'.le⟩
    exact h0 x hx
  exact ⟨key a b, key b a⟩

instance parameter_connectedSpace (g : WallGerm n) : ConnectedSpace g.Parameter :=
  isConnected_iff_connectedSpace.mp (isConnected_Ioo (by linarith [g.radius_pos]))

/-- CV activation of a pair is constant along the whole germ interval, centre included
(BRIDGE.md B2, "every crossing activation predicate … is constant throughout the interval"). -/
theorem crosses_const (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) (e f : ZMod n)
    (s t : g.Parameter) : CV.Crosses (g.curve s) e f ↔ CV.Crosses (g.curve t) e f := by
  by_cases hr : remote e f
  · obtain ⟨h0, h1, h2, h3⟩ := remote_endpoints e f hr
    have c1 : Continuous fun u : g.Parameter =>
        CV.G2 (g.curve u) e f * CV.G2 (g.curve u) e (f + 1) :=
      ((CV.continuous_G2 e f).comp g.continuous_curve).mul
        ((CV.continuous_G2 e (f + 1)).comp g.continuous_curve)
    have c2 : Continuous fun u : g.Parameter =>
        CV.G2 (g.curve u) f e * CV.G2 (g.curve u) f (e + 1) :=
      ((CV.continuous_G2 f e).comp g.continuous_curve).mul
        ((CV.continuous_G2 f (e + 1)).comp g.continuous_curve)
    have n1 : ∀ u : g.Parameter, CV.G2 (g.curve u) e f * CV.G2 (g.curve u) e (f + 1) ≠ 0 :=
      fun u => mul_ne_zero (cvG2_ne_zero_all hn hz u h0 h1) (cvG2_ne_zero_all hn hz u h2 h3)
    have n2 : ∀ u : g.Parameter, CV.G2 (g.curve u) f e * CV.G2 (g.curve u) f (e + 1) ≠ 0 :=
      fun u => mul_ne_zero (cvG2_ne_zero_all hn hz u h0.symm h2.symm)
        (cvG2_ne_zero_all hn hz u h1.symm h3.symm)
    exact and_congr Iff.rfl
      (and_congr (neg_iff_of_ne_zero c1 n1 s t) (neg_iff_of_ne_zero c2 n2 s t))
  · exact ⟨fun hc => (hr hc.1).elim, fun hc => (hr hc.1).elim⟩

/-- Activation of every member is constant along the whole germ interval. -/
theorem active_const (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) (m : CV.Member n)
    (s t : g.Parameter) : m.Active (g.curve s) ↔ m.Active (g.curve t) := by
  cases m with
  | g1 _ => exact Iff.rfl
  | g2 _ _ _ => exact Iff.rfl
  | g5 e f _ => exact crosses_const hn hz e f s t
  | g3 e f k _ =>
    exact and_congr (crosses_const hn hz e f s t)
      (and_congr (crosses_const hn hz f k s t) (crosses_const hn hz e k s t))
  | g4 e f k _ => exact and_congr (crosses_const hn hz e f s t) (crosses_const hn hz e k s t)

/-- "For a conditional member, being relevant at *some* nonzero time is consequently equivalent to
being active at the centre" (BRIDGE.md B2); here the direction used for `Z ⊆` bundle. -/
theorem active_center_of_relevant (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅)
    {m : CV.Member n} (hc : m.Conditional) {t : g.Parameter} (hm : m.Relevant (g.curve t)) :
    m.Active g.center := by
  rcases hm with hu | ha
  · exact (hc hu).elim
  · exact (active_const hn hz m t g.zeroParameter).mp ha

/-- The zero set of `eventOfTriple`, read on the germ's own data. -/
theorem mem_zeroSet_eventOfTriple (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (m : CV.Member n) :
    m ∈ (eventOfTriple hn g h).zeroSet ↔
      m.eval g.center = 0 ∧ ∃ t : g.Parameter, t.val ≠ 0 ∧ m.Relevant (g.curve t) :=
  Iff.rfl

/-! ### B2: sorting the index triple -/

/-- Membership data of a triple equality, read through the representatives. -/
theorem rep_mem_of_triple_eq {a b c e f k : ZMod n}
    (h : ({a, b, c} : Finset (ZMod n)) = {e, f, k}) :
    (CV.rep a = CV.rep e ∨ CV.rep a = CV.rep f ∨ CV.rep a = CV.rep k) ∧
    (CV.rep b = CV.rep e ∨ CV.rep b = CV.rep f ∨ CV.rep b = CV.rep k) ∧
    (CV.rep c = CV.rep e ∨ CV.rep c = CV.rep f ∨ CV.rep c = CV.rep k) ∧
    (CV.rep e = CV.rep a ∨ CV.rep e = CV.rep b ∨ CV.rep e = CV.rep c) ∧
    (CV.rep f = CV.rep a ∨ CV.rep f = CV.rep b ∨ CV.rep f = CV.rep c) ∧
    (CV.rep k = CV.rep a ∨ CV.rep k = CV.rep b ∨ CV.rep k = CV.rep c) := by
  have ha : a ∈ ({e, f, k} : Finset (ZMod n)) := h ▸ (by simp)
  have hb : b ∈ ({e, f, k} : Finset (ZMod n)) := h ▸ (by simp)
  have hc : c ∈ ({e, f, k} : Finset (ZMod n)) := h ▸ (by simp)
  have he : e ∈ ({a, b, c} : Finset (ZMod n)) := h ▸ (by simp)
  have hf : f ∈ ({a, b, c} : Finset (ZMod n)) := h ▸ (by simp)
  have hk : k ∈ ({a, b, c} : Finset (ZMod n)) := h ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc he hf hk
  exact ⟨ha.imp (congrArg CV.rep) (Or.imp (congrArg CV.rep) (congrArg CV.rep)),
    hb.imp (congrArg CV.rep) (Or.imp (congrArg CV.rep) (congrArg CV.rep)),
    hc.imp (congrArg CV.rep) (Or.imp (congrArg CV.rep) (congrArg CV.rep)),
    he.imp (congrArg CV.rep) (Or.imp (congrArg CV.rep) (congrArg CV.rep)),
    hf.imp (congrArg CV.rep) (Or.imp (congrArg CV.rep) (congrArg CV.rep)),
    hk.imp (congrArg CV.rep) (Or.imp (congrArg CV.rep) (congrArg CV.rep))⟩

/-- Two increasing namings of the same triple coincide ("The unique increasing representative is
the displayed G3 member", BRIDGE.md B2). -/
theorem sorted_triple_eq {a b c e f k : ZMod n}
    (h : ({a, b, c} : Finset (ZMod n)) = {e, f, k})
    (hab : CV.rep a < CV.rep b) (hbc : CV.rep b < CV.rep c)
    (hef : CV.rep e < CV.rep f) (hfk : CV.rep f < CV.rep k) : a = e ∧ b = f ∧ c = k := by
  obtain ⟨ha, hb, hc, he, hf, hk⟩ := rep_mem_of_triple_eq h
  refine ⟨CV.rep_injective ?_, CV.rep_injective ?_, CV.rep_injective ?_⟩ <;> omega

/-- A `G4` index triple `a; b, c` (`b̄ < c̄`) with support `{e, f, k}` (`ē < f̄ < k̄`) is one of the
three displayed `G4` members ("The possible base edge `a` is one of these three, and the remaining
two indices are put in increasing representative order", BRIDGE.md B2). -/
theorem g4_index_of_triple_eq {a b c e f k : ZMod n}
    (h : ({a, b, c} : Finset (ZMod n)) = {e, f, k}) (hbc : CV.rep b < CV.rep c)
    (hef : CV.rep e < CV.rep f) (hfk : CV.rep f < CV.rep k) :
    (a = e ∧ b = f ∧ c = k) ∨ (a = f ∧ b = e ∧ c = k) ∨ (a = k ∧ b = e ∧ c = f) := by
  obtain ⟨ha, hb, hc, he, hf, hk⟩ := rep_mem_of_triple_eq h
  rcases ha with ha | ha | ha
  · exact Or.inl ⟨CV.rep_injective ha, CV.rep_injective (by omega), CV.rep_injective (by omega)⟩
  · exact Or.inr (Or.inl
      ⟨CV.rep_injective ha, CV.rep_injective (by omega), CV.rep_injective (by omega)⟩)
  · exact Or.inr (Or.inr
      ⟨CV.rep_injective ha, CV.rep_injective (by omega), CV.rep_injective (by omega)⟩)

/-! ### B2: the parameter tie at the centre -/

/-- At the centre of a type-`T` germ, a vanishing `G4_{a;b,c}` whose two pairs are active is a
parameter tie on `a`, hence a point interior to `a, b, c`, hence `{a,b,c} = {e,f,k}` (BRIDGE.md B2,
clauses 3 and 4 of "`Z` contained in the forced bundle"; SM's
`uniqueTriple_parameter_tie_iff`). -/
theorem triple_eq_of_G4_center (hn : 3 ≤ n) {g : WallGerm n} {e f k : ZMod n}
    (h : g.TripleAt e f k) {a b c : ZMod n} (hbc : b ≠ c)
    (hab : CV.Crosses g.center a b) (hac : CV.Crosses g.center a c)
    (h4 : CV.G4 g.center a b c = 0) : ({a, b, c} : Finset (ZMod n)) = {e, f, k} := by
  have htie := (CV.G4_eq_zero_iff _ hab hac).mp h4
  rw [CV.crossParam_eq_edgeParameter, CV.crossParam_eq_edgeParameter] at htie
  exact (uniqueTriple_parameter_tie_iff hn (tripleAt_g1_center h) h.2.1 hbc
    hab.isCrossing hac.isCrossing).mp htie

/-! ### B2 -/

/-- **Bridge B2** (BRIDGE.md:450–453). "For the germ in B1, its CV zero set is
`Z = {G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}`. (3) These are four *indexed members*."

Stated for the increasing representatives `ē < f̄ < k̄` of the central triple (BRIDGE.md §0:
"when naming the central triple, choose `e<f<g` in those representatives"); the side conditions of
the four members are the pairwise remoteness supplied by `Z_c = {{e,f,k}}`. -/
theorem B2 (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n} (h : g.TripleAt e f k)
    (hef : CV.rep e < CV.rep f) (hfk : CV.rep f < CV.rep k) :
    (eventOfTriple hn g h).zeroSet =
      {CV.Member.g3 e f k ⟨tripleAt_remote_ef h, tripleAt_remote_fk h, tripleAt_remote_ek h, hef, hfk⟩,
       CV.Member.g4 e f k ⟨tripleAt_remote_ef h, tripleAt_remote_ek h, ne_of_apply_ne CV.rep hfk.ne, hfk⟩,
       CV.Member.g4 f e k ⟨remote_symm (tripleAt_remote_ef h), tripleAt_remote_fk h,
         ne_of_apply_ne CV.rep (hef.trans hfk).ne, hef.trans hfk⟩,
       CV.Member.g4 k e f ⟨remote_symm (tripleAt_remote_ek h), remote_symm (tripleAt_remote_fk h),
         ne_of_apply_ne CV.rep hef.ne, hef⟩} := by
  have hz : g.pointZeros = ∅ := h.1
  have hG1 := tripleAt_g1_center h
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨cef, cfk, cek⟩ := tripleAt_crosses_center hn h
  have h3 := tripleAt_G3_center h
  -- a nonzero time of the germ
  let t₀ : g.Parameter := g.sideTime true g.sideBase
  have ht₀ : t₀.val ≠ 0 := g.sideTime_ne_zero true g.sideBase
  ext m
  rw [mem_zeroSet_eventOfTriple]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Z ⊆ forced bundle: exhaust the five families
    rintro ⟨h0, t, -, hm⟩
    cases m with
    | g1 i =>
      exact absurd h0 (g1_turn_nonzero hn hG1 i)
    | g2 a i hi =>
      exact absurd h0 (cvG2_ne_zero_of_g1 hG1 hi.1 hi.2)
    | g5 a b hab =>
      have hact := active_center_of_relevant hn hz (CV.Member.conditional_g5 a b hab) hm
      exact absurd h0 (CV.Crosses.det_ne_zero hact)
    | g3 a b c habc =>
      obtain ⟨hab, hbc, hac⟩ :=
        active_center_of_relevant hn hz (CV.Member.conditional_g3 a b c habc) hm
      have h4 : CV.G4 g.center a b c = 0 := by
        rw [CV.G4_eq_neg_G3, CV.Member.eval_g3] at *
        rw [h0, neg_zero]
      have hset := triple_eq_of_G4_center hn h (ne_of_apply_ne CV.rep habc.2.2.2.2.ne) hab hac h4
      obtain ⟨rfl, rfl, rfl⟩ := sorted_triple_eq hset habc.2.2.2.1 habc.2.2.2.2 hef hfk
      exact Or.inl rfl
    | g4 a b c habc =>
      obtain ⟨hab, hac⟩ :=
        active_center_of_relevant hn hz (CV.Member.conditional_g4 a b c habc) hm
      have hset := triple_eq_of_G4_center hn h habc.2.2.1 hab hac h0
      rcases g4_index_of_triple_eq hset habc.2.2.2 hef hfk with ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  · -- forced bundle ⊆ Z: each member vanishes at the centre and is active there, hence at `t₀`
    rintro (rfl | rfl | rfl | rfl)
    · refine ⟨h3, t₀, ht₀, Or.inr ?_⟩
      exact (active_const hn hz _ g.zeroParameter t₀).mp ⟨cef, cfk, cek⟩
    · refine ⟨?_, t₀, ht₀, Or.inr ?_⟩
      · rw [CV.Member.eval_g4, CV.G4_eq_neg_G3, h3, neg_zero]
      · exact (active_const hn hz _ g.zeroParameter t₀).mp ⟨cef, cek⟩
    · refine ⟨?_, t₀, ht₀, Or.inr ?_⟩
      · rw [CV.Member.eval_g4, CV.G4_swap_first_eq_G3, h3]
      · exact (active_const hn hz _ g.zeroParameter t₀).mp ⟨(CV.crosses_comm _ _ _).mp cef, cfk⟩
    · refine ⟨?_, t₀, ht₀, Or.inr ?_⟩
      · rw [CV.Member.eval_g4, CV.G4_last_eq_neg_G3, h3, neg_zero]
      · exact (active_const hn hz _ g.zeroParameter t₀).mp
          ⟨(CV.crosses_comm _ _ _).mp cek, (CV.crosses_comm _ _ _).mp cfk⟩

/-- Every type-`T` germ can be named by its increasing representatives (BRIDGE.md §0), so `B2`
applies to every `TripleAt` after renaming the triple (`WallGerm.tripleAt_support_iff`). -/
theorem exists_sorted_tripleAt (g : WallGerm n) {e f k : ZMod n} (h : g.TripleAt e f k) :
    ∃ e' f' k' : ZMod n, ({e', f', k'} : Finset (ZMod n)) = {e, f, k} ∧
      CV.rep e' < CV.rep f' ∧ CV.rep f' < CV.rep k' ∧ g.TripleAt e' f' k' := by
  have hef : e ≠ f := (remote_endpoints e f (tripleAt_remote_ef h)).1.symm
  have hfk : f ≠ k := (remote_endpoints f k (tripleAt_remote_fk h)).1.symm
  have hek : e ≠ k := (remote_endpoints e k (tripleAt_remote_ek h)).1.symm
  have key : ∀ a b c : ZMod n, ({a, b, c} : Finset (ZMod n)) = {e, f, k} →
      CV.rep a < CV.rep b → CV.rep b < CV.rep c → ∃ e' f' k' : ZMod n,
        ({e', f', k'} : Finset (ZMod n)) = {e, f, k} ∧
        CV.rep e' < CV.rep f' ∧ CV.rep f' < CV.rep k' ∧ g.TripleAt e' f' k' :=
    fun a b c hs hab hbc => ⟨a, b, c, hs, hab, hbc, g.tripleAt_of_support_eq hs h⟩
  have perm : ∀ a b c : ZMod n, ({a, b, c} : Finset (ZMod n)) = {e, f, k} →
      ({b, a, c} : Finset (ZMod n)) = {e, f, k} ∧ ({a, c, b} : Finset (ZMod n)) = {e, f, k} := by
    intro a b c hs
    refine ⟨?_, ?_⟩
    · rw [← hs, Finset.insert_comm]
    · rw [← hs]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  rcases CV.rep_lt_or_lt hef with h1 | h1 <;> rcases CV.rep_lt_or_lt hfk with h2 | h2 <;>
    rcases CV.rep_lt_or_lt hek with h3 | h3
  · exact key e f k rfl h1 h2
  · omega
  · exact key e k f (perm e f k rfl).2 h3 h2
  · exact key k e f (perm e k f (perm e f k rfl).2).1 h3 h1
  · exact key f e k (perm e f k rfl).1 h1 h3
  · exact key f k e (perm f e k (perm e f k rfl).1).2 h2 h3
  · omega
  · exact key k f e (perm f k e (perm f e k (perm e f k rfl).1).2).1 h2 h1

end Bridge

#print axioms Bridge.B1
#print axioms Bridge.eventOfTriple
#print axioms Bridge.B2
#print axioms Bridge.exists_sorted_tripleAt
