import SM.GeoMarkTransport
import SM.LinkMoves
import SM.LinkInterfaces
import SM.RotationContinuity
import SM.WeakGeometry
import Mathlib.Topology.LocallyConstant.Basic

/-! # SM/GeoPathTransport.lean — transport along a continuous family on the geometric record domain
(CV-DOM unit U5a, part 2)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1–R5, §5 row **U5a**). Draft; intended home
`work/lean/SM/GeoPathTransport.lean` (library module, namespace `SM.GeoCarrier`, `open Carrier Link`,
CV-free). Nothing under work/lean was written.

## What this module is

The re-binding of the *analytic* half of the accepted prop:C-chamber module (SM/CChamber.lean §2,
`pathTransport` along a `Path` of `SM.Generic` polygons) to a continuous family `γ : unitInterval →
LabelledTuple n` every member of which lies on the accepted geometric record domain (`CrossingGeometry`,
tier 0); the corner-polygon geometry is read at tier 1 (`CarrierGeometry`, ruling R4) and the vertex turn
data at tier 2 (`WeakGeneric`, or just `turn ≠ 0` along the family).

* §0 copies (row modules are not imported) the link-layer family lemmas of SM/CChamber.lean §2c and
  SM/CS3.lean: a generic deformation from a continuous family of generic re-vertexings
  (`geo_deform_of_family`), persistence of positivity (`geo_isPositive_deform_of_family`), the record domain
  of a generic one-component shadow (`geo_crossingGeometry_of_single_generic`), and the conclusion
  **lit:homfly's planar clause along a family** (`geo_homfly_positiveDiagram_single_of_family`).
* §1 `geoMarkPoint R a`: the plane point of a mark of `P` read on any polygon `R` with the same crossing
  supports (vertices by label, visits by Cramer), continuous in `R` on the record domain.
* §2 along a continuous family of `CrossingGeometry` polygons the crossing supports, the same-edge parameter
  order and the crossing signs are constant (`geoFamily_crossing_iff`, `geoFamily_orderAgrees`,
  `geoFamily_crossingSign_eq`: locally constant by the accepted persistence lemmas, constant on the
  connected `unitInterval`), so every two members are related by a `GeoMarkTransport`
  (`geoFamily_transport`); with nonzero turns along the family the vertex turns are constant too
  (`geoFamily_turn_eq`).
* §3 the corner polygon of a carrier of `γ 0`, read along the family (`geoCornerFamily`), is continuous,
  is the corner polygon of the transported carrier up to a recast at every time, and — at tier 1 — is
  regular at every time, so its rotation number is constant (lem:rot (ii), the accepted
  `rotationNumber_family_constant`) and its positive lifts at the two ends have the same HOMFLY polynomial
  (`geo_homfly_positiveDiagram_single_of_family`): `geoCarrierRotation_eq_of_family`,
  `homfly_geoPositiveLift_eq_of_family`.
* §4 the endpoint packages `GeoPathData` (tier 1: transport, rotation, HOMFLY) and `GeoWeakPathData`
  (tier 2: + vertex turns, hence `geoCarrierSelector`, `geoCarrierUniform`, `geoWind`), from a family
  (`of_family`) and from a `Path P Q` (`of_path`, endpoints transferred by generalisation), and the
  culminating `geoWind_eq_of_path`, `homfly_geoPositiveLift_eq_of_path`, `geoCarrierRotation_eq_of_path`.

## Names (ruling R3)

Namespace `SM.GeoCarrier`, prefix `geo`/`geoFamily`/`geoCornerFamily`; the copies of row-module lemmas
carry the prefix `geo_` (`geo_positiveDiagram_congr`, `geo_single_isCrossing_iff_of_forall`,
`geo_crossingGeometry_of_single_generic`, `geo_deform_of_family`, `geo_isPositive_deform_of_family`,
`geo_deform_positiveDiagram_single_of_family`, `geo_homfly_positiveDiagram_single_of_family`). No
accepted or ported name is re-declared. -/

namespace SM.GeoCarrier

open Carrier Link Filter Topology

/-! ## 0. Link-layer family lemmas (copies of SM/CChamber.lean §2c and SM/CS3.lean) -/

section LinkFamily

/-- Proof-irrelevant congruence of positive diagrams along an equality of shadows. -/
theorem geo_positiveDiagram_congr {Γ Γ' : Shadow} (h : Γ = Γ') (hΓ : Γ.Generic) (hΓ' : Γ'.Generic) :
    Γ.positiveDiagram hΓ = Γ'.positiveDiagram hΓ' := by
  subst h
  rfl

/-- Crossing pairs of one-component shadows on two polygons with the same crossing supports. -/
theorem geo_single_isCrossing_iff_of_forall {k : ℕ} (hk : 3 ≤ k) {X Y : LabelledTuple k}
    (h : ∀ s, IsCrossing X s ↔ IsCrossing Y s) (x : Finset (Shadow.single ⟨k, hk, X⟩).Strand) :
    (Shadow.single ⟨k, hk, X⟩).IsCrossing x ↔ (Shadow.single ⟨k, hk, Y⟩).IsCrossing x := by
  rw [Shadow.single_isCrossing_iff, Shadow.single_isCrossing_iff]
  exact h _

/-- A polygon whose one-component shadow is generic lies on the geometric record domain: nonzero edges
(`regular`), meetings of remote edges interior and transverse (`tail_off`, `transverse`), no triple point
(`no_triple`). -/
theorem geo_crossingGeometry_of_single_generic {k : ℕ} (hk : 3 ≤ k) {T : LabelledTuple k}
    (h : (Shadow.single ⟨k, hk, T⟩).Generic) : CrossingGeometry T := by
  have hvertex : ∀ a b : ZMod k, ¬ incident a b → T a ∉ edgeSegment T b := fun a b hinc =>
    h.tail_off ⟨0, a⟩ ⟨0, b⟩ (fun h' => hinc ((Shadow.single_incidentTail_iff _ _ _).mp h'))
  refine ⟨fun i => ((regular_iff_edges T).mp (h.regular 0) i).1, ?_, ?_⟩
  · intro i j hr x hi hj
    refine ⟨remote_closed_point_interior hvertex hr hi hj,
      remote_closed_point_interior hvertex (remote_symm hr) hj hi, ?_⟩
    exact h.transverse ⟨0, i⟩ ⟨0, j⟩
      (fun h' => hr ((Shadow.single_adjacent_iff _ _ _).mp h')) ⟨x, hi, hj⟩
  · rintro ⟨i, j, l, x, hij, hjl, hil, hi, hj, hl⟩
    exact h.no_triple ⟨⟨0, i⟩, ⟨0, j⟩, ⟨0, l⟩,
      fun e => hij (congrArg (Shadow.singleStrandEquiv _) e),
      fun e => hjl (congrArg (Shadow.singleStrandEquiv _) e),
      fun e => hil (congrArg (Shadow.singleStrandEquiv _) e), x, ⟨hi, hj⟩, hl⟩

/-- A generic deformation from a family on the unit interval (`DeformData` with
`γ t := V (Set.projIcc 0 1 zero_le_one t)`). -/
theorem geo_deform_of_family (D : Diagram) {V : unitInterval → D.Γ.Vertices}
    (hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun t => V t i j)
    (hgen : ∀ t, (D.Γ.withVertices (V t)).Generic)
    (hcross : ∀ t (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V t)).IsCrossing x ↔ D.Γ.IsCrossing x)
    (h0 : V 0 = D.Γ.vertices) :
    Deform D (D.deform (V 1) (hgen 1) (hcross 1)) := by
  have h0' : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := Set.projIcc_left _
  have h1' : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) := Set.projIcc_right _
  exact ⟨{ γ := fun t => V (Set.projIcc 0 1 zero_le_one t)
           continuous := fun i j => ((hV i j).comp continuous_projIcc).continuousOn
           start := by
             show V (Set.projIcc 0 1 zero_le_one 0) = D.Γ.vertices
             rw [h0']
             exact h0
           generic := fun t _ => hgen _
           crossings := fun t _ x => hcross _ x
           stop := by
             show D.deform (V 1) (hgen 1) (hcross 1) =
               D.deform (V (Set.projIcc 0 1 zero_le_one 1)) (hgen _) (hcross _)
             rw [h1'] }⟩

/-- Positivity of every crossing persists along a generic deformation: the determinant of the over and
under directions is continuous and nonzero at every time. -/
theorem geo_isPositive_deform_of_family (D : Diagram) {V : unitInterval → D.Γ.Vertices}
    (hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun t => V t i j)
    (hgen : ∀ t, (D.Γ.withVertices (V t)).Generic)
    (hcross : ∀ t (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V t)).IsCrossing x ↔ D.Γ.IsCrossing x)
    (h0 : V 0 = D.Γ.vertices) (hpos : ∀ x, D.IsPositive x)
    (x : (D.deform (V 1) (hgen 1) (hcross 1)).Γ.Crossing) :
    (D.deform (V 1) (hgen 1) (hcross 1)).IsPositive x := by
  let x₀ : D.Γ.Crossing := ⟨x.val, (hcross 1 x.val).mp x.2⟩
  let xt (t : unitInterval) : (D.Γ.withVertices (V t)).Crossing :=
    ⟨x.val, (hcross t x.val).mpr x₀.2⟩
  let o : D.Γ.Strand := D.overStrand x₀
  let u : D.Γ.Strand := D.underStrand x₀
  let f (t : unitInterval) : ℝ := det (edge (V t o.1) o.2) (edge (V t u.1) u.2)
  have he : ∀ s : D.Γ.Strand, Continuous fun t => edge (V t s.1) s.2 := fun s =>
    (hV s.1 (s.2 + 1)).sub (hV s.1 s.2)
  have hf : Continuous f := ((he o).fst.mul (he u).snd).sub ((he o).snd.mul (he u).fst)
  have hne : ∀ t, f t ≠ 0 := fun t =>
    (hgen t).transverse o u (D.not_adjacent_over_under x₀)
      ((D.Γ.withVertices (V t)).crossing_pair_spec (xt t) (D.over_mem x₀) (D.under_mem x₀)
        (D.over_ne_under x₀)).2
  have hsign : Continuous fun t => SignType.sign (f t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_sign_of_ne_zero (hne t)).comp hf.continuousAt
  have hconst : SignType.sign (f 1) = SignType.sign (f 0) :=
    PreconnectedSpace.constant inferInstance hsign
  have hf0 : 0 < f 0 := by
    show 0 < det (edge (V 0 o.1) o.2) (edge (V 0 u.1) u.2)
    rw [h0]
    exact hpos x₀
  have hunder : (D.deform (V 1) (hgen 1) (hcross 1)).underStrand x = u :=
    ((D.Γ.withVertices (V 1)).eq_other_of_mem_of_ne x (D.over_mem x₀) (D.under_mem x₀)
      (D.under_ne_over x₀)).symm
  show 0 < det _ _
  rw [hunder]
  exact sign_eq_one_iff.mp (hconst.trans (sign_eq_one_iff.mpr hf0))

/-- **Deform along a continuous family of generic one-component shadows**: the crossing pairs are
constant (`crossing_support_persists_of_geometry` + `geo_crossingGeometry_of_single_generic`, locally
constant on the connected `unitInterval`), `geo_deform_of_family`, positivity persists
(`geo_isPositive_deform_of_family`), and the deformed diagram is the positive diagram
(`eq_positiveDiagram_of_isPositive`). -/
theorem geo_deform_positiveDiagram_single_of_family {k : ℕ} (hk : 3 ≤ k)
    (Φ : unitInterval → LabelledTuple k) (hΦ : Continuous Φ)
    (hgen : ∀ u, (Shadow.single ⟨k, hk, Φ u⟩).Generic) :
    Deform ((Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0))
      ((Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1)) := by
  have : NeZero k := ⟨by omega⟩
  let D : Diagram := (Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0)
  let V : unitInterval → D.Γ.Vertices := fun u _ => Φ u
  have hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun u => V u i j :=
    fun _ j => (continuous_apply j).comp hΦ
  have hgen' : ∀ u, (D.Γ.withVertices (V u)).Generic := fun u => hgen u
  have hcross : ∀ u (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V u)).IsCrossing x ↔ D.Γ.IsCrossing x := by
    intro u x
    have hg : IsLocallyConstant fun u : unitInterval => {s : Finset (ZMod k) | IsCrossing (Φ u) s} := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro u₀
      have hev := crossing_support_persists_of_geometry
        (geo_crossingGeometry_of_single_generic hk (hgen u₀))
      filter_upwards [hΦ.continuousAt.eventually hev] with u' hu'
      exact Set.ext hu'
    have hconst := Set.ext_iff.mp (IsLocallyConstant.apply_eq_of_preconnectedSpace hg u 0)
    exact geo_single_isCrossing_iff_of_forall hk (fun s => hconst s) x
  have h0 : V 0 = D.Γ.vertices := rfl
  have hd : Deform D (D.deform (V 1) (hgen' 1) (hcross 1)) :=
    geo_deform_of_family D hV hgen' hcross h0
  have heq : D.deform (V 1) (hgen' 1) (hcross 1) =
      (Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1) :=
    Shadow.eq_positiveDiagram_of_isPositive _ (hgen 1) _ rfl
      (geo_isPositive_deform_of_family D hV hgen' hcross h0
        (fun x => Shadow.positiveDiagram_isPositive _ _ x))
  rw [← heq]
  exact hd

/-- **lit:homfly's planar clause along a family** of generic one-component shadows: the positive diagrams
at the two ends have the same HOMFLY polynomial (`homfly_planar`, `PlanarIsotopic.of_deform`). -/
theorem geo_homfly_positiveDiagram_single_of_family {k : ℕ} (hk : 3 ≤ k)
    (Φ : unitInterval → LabelledTuple k) (hΦ : Continuous Φ)
    (hgen : ∀ u, (Shadow.single ⟨k, hk, Φ u⟩).Generic) :
    homfly ((Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0)) =
      homfly ((Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1)) :=
  homfly_planar (PlanarIsotopic.of_deform (geo_deform_positiveDiagram_single_of_family hk Φ hΦ hgen))

end LinkFamily

variable {n : ℕ} [NeZero n] {P Q R : LabelledTuple n}

/-! ## 1. Mark points as functions of the polygon -/

omit [NeZero n] in
/-- The plane point of a mark of `P` read on a polygon `R` with the same crossing supports: a vertex by its
label, a visit as the Cramer crossing point of its two edge labels (the accepted row modules'
`markPointOn` / `silentMarkPoint`, for two arbitrary polygons). No hypothesis on `R` is needed to write it
down; `geoMarkPoint_eq` identifies it with the point of the transported mark on the record domain. -/
noncomputable def geoMarkPoint (R : LabelledTuple n) : Mark P → Plane
  | Sum.inl i => R i
  | Sum.inr v => edgePoint R v.2.val (edgeParameter R v.2.val (visitTwin v).2.val)

omit [NeZero n] in
theorem geoMarkPoint_vertex (R : LabelledTuple n) (i : ZMod n) :
    geoMarkPoint (P := P) R (Sum.inl i) = R i := rfl

omit [NeZero n] in
theorem geoMarkPoint_visit (R : LabelledTuple n) (v : Visit P) :
    geoMarkPoint R (Sum.inr v) = edgePoint R v.2.val (edgeParameter R v.2.val (visitTwin v).2.val) := rfl

omit [NeZero n] in
/-- On the record domain with the same crossing supports, the mark point is the point of the transported
mark. -/
theorem geoMarkPoint_eq (hR : CrossingGeometry R) (hs : ∀ s, IsCrossing P s ↔ IsCrossing R s)
    (a : Mark P) :
    geoMarkPoint R a = traversalEvaluation R (geoMarkPosition hR (markTransport hs a)) := by
  cases a with
  | inl i =>
    show R i = traversalEvaluation R (geoMarkPosition hR (Sum.inl i))
    rw [geoMarkPosition_evaluation_vertex]
  | inr v =>
    have hpair := visitParameter_eq_of_support_pair_of_geometry hR (visitTransport hs v)
      (visitTwin v).2.val (visit_crossing_val_eq_pair v)
    show edgePoint R v.2.val (edgeParameter R v.2.val (visitTwin v).2.val) =
      traversalEvaluation R (geoMarkPosition hR (Sum.inr (visitTransport hs v)))
    rw [geoMarkPosition_evaluation_visit,
      (crossingParameter_spec _ _ (visitTransport hs v).2.property).2.2]
    exact congrArg (edgePoint R v.2.val) hpair.symm

omit [NeZero n] in
/-- The canonical identification of the marks of `P` with themselves is the identity. -/
theorem markTransport_self (hs : ∀ s, IsCrossing P s ↔ IsCrossing P s) (a : Mark P) :
    markTransport hs a = a := by
  cases a with
  | inl i => rfl
  | inr v => rfl

omit [NeZero n] in
/-- On `P` itself the mark point is the mark's point. -/
theorem geoMarkPoint_self (hP : CrossingGeometry P) (a : Mark P) :
    geoMarkPoint P a = traversalEvaluation P (geoMarkPosition hP a) := by
  rw [geoMarkPoint_eq hP (fun _ => Iff.rfl) a, markTransport_self]

omit [NeZero n] in
/-- Continuity of the mark points at every polygon of the record domain with the crossing supports of
`P`: vertices by projection, visits by Cramer's rule (`continuousAt_edgeParameter_of_geometry`). -/
theorem continuousAt_geoMarkPoint (hR : CrossingGeometry R)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing R s) (a : Mark P) :
    ContinuousAt (fun R' : LabelledTuple n => geoMarkPoint R' a) R := by
  cases a with
  | inl i => exact (continuous_vertex i).continuousAt
  | inr v =>
    have hcross0 : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    have hcross := (hs _).mp hcross0
    exact (continuous_vertex v.2.val).continuousAt.add
      ((continuousAt_edgeParameter_of_geometry hR hcross).smul (continuous_edge v.2.val).continuousAt)

/-! ## 2. Families on the geometric record domain: constancy of the records -/

section Family

variable (γ : unitInterval → LabelledTuple n) (hγc : Continuous γ)
  (hγ : ∀ t, CrossingGeometry (γ t))

include hγc hγ in
/-- **The crossing supports are constant along the family**: locally constant by the accepted
`crossing_support_persists_of_geometry` at every time, constant on the connected `unitInterval`. -/
theorem geoFamily_crossing_iff (s t : unitInterval) (c : Finset (ZMod n)) :
    IsCrossing (γ s) c ↔ IsCrossing (γ t) c := by
  have hg : IsLocallyConstant fun u : unitInterval => {c : Finset (ZMod n) | IsCrossing (γ u) c} := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u₀
    filter_upwards [hγc.continuousAt.eventually (crossing_support_persists_of_geometry (hγ u₀))]
      with u hu
    exact Set.ext hu
  exact Set.ext_iff.mp (IsLocallyConstant.apply_eq_of_preconnectedSpace hg s t) c

include hγc hγ in
/-- **The same-edge parameter order is constant along the family** (accepted
`geometric_parameter_order_persists`, locally; connectedness). -/
theorem geoFamily_orderAgrees (s t : unitInterval) : CrossingParameterOrderAgrees (γ s) (γ t) := by
  intro i j k hij hik
  have hg : IsLocallyConstant fun u : unitInterval =>
      {x : ZMod n × ZMod n × ZMod n | IsCrossing (γ s) {x.1, x.2.1} ∧ IsCrossing (γ s) {x.1, x.2.2} ∧
        edgeParameter (γ u) x.1 x.2.1 < edgeParameter (γ u) x.1 x.2.2} := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u₀
    filter_upwards [hγc.continuousAt.eventually (geometric_parameter_order_persists (hγ u₀))]
      with u hu
    ext ⟨a, b, c⟩
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (hu a b c ((geoFamily_crossing_iff γ hγc hγ s u₀ _).mp h1)
        ((geoFamily_crossing_iff γ hγc hγ s u₀ _).mp h2)).mp h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (hu a b c ((geoFamily_crossing_iff γ hγc hγ s u₀ _).mp h1)
        ((geoFamily_crossing_iff γ hγc hγ s u₀ _).mp h2)).mpr h3⟩
  have h := Set.ext_iff.mp (IsLocallyConstant.apply_eq_of_preconnectedSpace hg t s) (i, j, k)
  simp only [Set.mem_ofPred_eq] at h
  constructor
  · intro hlt
    exact (h.mp ⟨hij, hik, hlt⟩).2.2
  · intro hlt
    exact (h.mpr ⟨hij, hik, hlt⟩).2.2

include hγc hγ in
/-- **Crossing signs are constant along the family** (accepted `crossingSign_locally_constant_of_geometry`,
locally; connectedness). -/
theorem geoFamily_crossingSign_eq (s t : unitInterval) (i j : ZMod n)
    (h : IsCrossing (γ s) {i, j}) : crossingSign (γ t) i j = crossingSign (γ s) i j := by
  have hg : IsLocallyConstant fun u : unitInterval => crossingSign (γ u) i j := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u₀
    filter_upwards [hγc.continuousAt.eventually (crossingSign_locally_constant_of_geometry (hγ u₀)
      ((geoFamily_crossing_iff γ hγc hγ s u₀ _).mp h))] with u hu
    exact hu
  exact IsLocallyConstant.apply_eq_of_preconnectedSpace hg t s

/-- **Every two members of the family are related by a mark transport** (the canonical identification,
`GeoMarkTransport.ofOrderAgrees`). -/
theorem geoFamily_transport (s t : unitInterval) :
    GeoMarkTransport (hγ s) (hγ t) (geoFamily_crossing_iff γ hγc hγ s t) :=
  GeoMarkTransport.ofOrderAgrees (hγ s) (hγ t) _ (geoFamily_orderAgrees γ hγc hγ s t)
    (fun i j h => geoFamily_crossingSign_eq γ hγc hγ s t i j h)

omit [NeZero n] in
include hγc in
/-- **Vertex turns are constant along a family with nonzero turns** (tier 2 datum): `turn = sign ∘ det`
of consecutive edges is continuous into the discrete `SignType` where nonzero, hence locally constant. -/
theorem geoFamily_turn_eq (hne : ∀ (t : unitInterval) (i : ZMod n), turn (γ t) i ≠ 0)
    (s t : unitInterval) (i : ZMod n) : turn (γ t) i = turn (γ s) i := by
  have hc : Continuous fun u : unitInterval => det (edge (γ u) (i - 1)) (edge (γ u) i) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact continuousAt_det ((continuous_edge (i - 1)).comp hγc).continuousAt
      ((continuous_edge i).comp hγc).continuousAt
  have hg : IsLocallyConstant fun u : unitInterval => turn (γ u) i := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u₀
    have h1 : ContinuousAt (fun u : unitInterval => turn (γ u) i) u₀ := by
      have : (fun u : unitInterval => turn (γ u) i) =
          fun u => SignType.sign (det (edge (γ u) (i - 1)) (edge (γ u) i)) := by
        funext u
        exact turn_det (γ u) i
      rw [this]
      refine (continuousAt_sign_of_ne_zero ?_).comp hc.continuousAt
      have h := hne u₀ i
      rw [turn_det] at h
      exact sign_ne_zero.mp h
    exact h1.eventually ((isOpen_discrete _).mem_nhds (Set.mem_singleton _))
  exact IsLocallyConstant.apply_eq_of_preconnectedSpace hg t s

omit [NeZero n] in
include hγc in
/-- Weak genericity along the family supplies the nonzero turns. -/
theorem geoFamily_turn_eq_of_weak (hW : ∀ t, WeakGeneric (γ t)) (s t : unitInterval) (i : ZMod n) :
    turn (γ t) i = turn (γ s) i :=
  geoFamily_turn_eq γ hγc (fun t i => (hW t).2.1 i) s t i

end Family

/-! ## 3. The corner polygon of a carrier read along a family -/

section CornerFamily

variable (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
  (γ : unitInterval → LabelledTuple n)

/-- The corner polygon of the carrier `q` of `P` read on the polygon `γ t`: its `k`-th vertex is the mark
point of the `k`-th corner mark of `q` on `γ t` (the accepted row modules' `cornerFamily` /
`silentCornerFamily`, for an arbitrary family). -/
noncomputable def geoCornerFamily (t : unitInterval) : LabelledTuple (geoCornerCount hP S q) :=
  fun k => geoMarkPoint (γ t) (geoCornerMark hP S q k)

theorem geoCornerFamily_apply (t : unitInterval) (k : ZMod (geoCornerCount hP S q)) :
    geoCornerFamily hP S q γ t k = geoMarkPoint (γ t) (geoCornerMark hP S q k) := rfl

/-- Where the family passes through `P`, the corner family is the corner polygon. -/
theorem geoCornerFamily_eq_self (t : unitInterval) (ht : γ t = P) :
    geoCornerFamily hP S q γ t = geoCornerPolygon hP S q := by
  funext k
  rw [geoCornerFamily_apply, ht, geoMarkPoint_self hP]
  rfl

/-- At a time `t` on the record domain with the crossing supports of `P`, the corner family is the
transported corner polygon of any mark transport from `P` to `γ t`. -/
theorem geoCornerFamily_eq_transported (t : unitInterval) (hR : CrossingGeometry (γ t))
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing (γ t) s} (τ : GeoMarkTransport hP hR hs) :
    geoCornerFamily hP S q γ t = τ.transportedCornerPolygon S q := by
  funext k
  rw [geoCornerFamily_apply, geoMarkPoint_eq hR hs]
  rfl

/-- The corner family at `t` is the corner polygon of the transported carrier on `γ t`, recast. -/
theorem geoCornerFamily_eq_recast (t : unitInterval) (hR : CrossingGeometry (γ t))
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing (γ t) s} (τ : GeoMarkTransport hP hR hs) :
    geoCornerFamily hP S q γ t =
      geoRecast (τ.geoCornerCount_eq S q).symm
        (geoCornerPolygon hR (transportSupport hs S) (τ.component S q)) := by
  rw [geoCornerFamily_eq_transported hP S q γ t hR τ, τ.transportedCornerPolygon_eq S q]

/-- **Continuity of the corner family** along a continuous family on the record domain with the crossing
supports of `P`. -/
theorem continuous_geoCornerFamily (hγc : Continuous γ) (hγ : ∀ t, CrossingGeometry (γ t))
    (hs : ∀ t s, IsCrossing P s ↔ IsCrossing (γ t) s) :
    Continuous fun t => geoCornerFamily hP S q γ t := by
  apply continuous_pi
  intro k
  rw [continuous_iff_continuousAt]
  intro t
  exact (continuousAt_geoMarkPoint (hγ t) (hs t) (geoCornerMark hP S q k)).comp hγc.continuousAt

end CornerFamily

/-! ## 3b. Along a family: regularity, rotation, HOMFLY (tier 1) -/

section FamilyTier1

variable (hn : 3 ≤ n) (γ : unitInterval → LabelledTuple n) (hγc : Continuous γ)
  (hG : ∀ t, CarrierGeometry (γ t))

/-- The mark transport from time `0` to time `t` of a family on the record domain. -/
theorem geoFamily_transport_zero (t : unitInterval) :
    GeoMarkTransport (hG 0).cg (hG t).cg (geoFamily_crossing_iff γ hγc (fun u => (hG u).cg) 0 t) :=
  geoFamily_transport γ hγc (fun u => (hG u).cg) 0 t

include hγc in
/-- The corner family of a carrier of `γ 0` is continuous. -/
theorem continuous_geoCornerFamily_zero (S : Finset (Crossing (γ 0))) (q : GeoComponent (hG 0).cg S) :
    Continuous fun t => geoCornerFamily (hG 0).cg S q γ t :=
  continuous_geoCornerFamily (hG 0).cg S q γ hγc (fun t => (hG t).cg)
    (fun t => geoFamily_crossing_iff γ hγc (fun u => (hG u).cg) 0 t)

theorem geoCornerFamily_zero (S : Finset (Crossing (γ 0))) (q : GeoComponent (hG 0).cg S) :
    geoCornerFamily (hG 0).cg S q γ 0 = geoCornerPolygon (hG 0).cg S q :=
  geoCornerFamily_eq_self (hG 0).cg S q γ 0 rfl

include hn hγc in
/-- At tier 1 the corner family is regular at every time (`geoCornerPolygon_regular` of the transported
carrier, `regular_geoRecast`). -/
theorem regular_geoCornerFamily {S : Finset (Crossing (γ 0))} (hS : GeoIndependent (hG 0).cg S)
    (q : GeoComponent (hG 0).cg S) (t : unitInterval) :
    Regular (geoCornerFamily (hG 0).cg S q γ t) := by
  rw [geoCornerFamily_eq_recast (hG 0).cg S q γ t (hG t).cg (geoFamily_transport_zero γ hγc hG t),
    regular_geoRecast]
  exact geoCornerPolygon_regular hn (hG t)
    (((geoFamily_transport_zero γ hγc hG t).geoIndependent_iff S).mpr hS) _

include hn hγc in
/-- **lem:rot (ii) along the family**: the rotation number of the corner family is constant. -/
theorem rotationNumber_geoCornerFamily_const {S : Finset (Crossing (γ 0))}
    (hS : GeoIndependent (hG 0).cg S) (q : GeoComponent (hG 0).cg S) (s t : unitInterval) :
    rotationNumber (geoCornerFamily (hG 0).cg S q γ s) =
      rotationNumber (geoCornerFamily (hG 0).cg S q γ t) :=
  rotationNumber_family_constant (continuous_geoCornerFamily_zero γ hγc hG S q)
    (regular_geoCornerFamily hn γ hγc hG hS q) s t

include hn in
/-- **The rotation of a carrier is constant along the family** (`geoCarrierRotation`, def:uniform's `r_Q`). -/
theorem geoCarrierRotation_eq_of_family {S : Finset (Crossing (γ 0))}
    (hS : GeoIndependent (hG 0).cg S) (q : GeoComponent (hG 0).cg S) (t : unitInterval) :
    geoCarrierRotation (hG t).cg (transportSupport (geoFamily_crossing_iff γ hγc (fun u => (hG u).cg) 0 t) S)
        ((geoFamily_transport_zero γ hγc hG t).component S q) =
      geoCarrierRotation (hG 0).cg S q := by
  rw [← (geoFamily_transport_zero γ hγc hG t).rotationNumber_transportedCornerPolygon S q,
    ← geoCornerFamily_eq_transported (hG 0).cg S q γ t (hG t).cg (geoFamily_transport_zero γ hγc hG t),
    rotationNumber_geoCornerFamily_const hn γ hγc hG hS q t 0, geoCornerFamily_zero γ hG S q]
  rfl

include hγc in
/-- The corner family is a generic one-component shadow at every time (tier 1 at `γ t`, through the
transport). -/
theorem single_generic_geoCornerFamily {S : Finset (Crossing (γ 0))}
    (hS : GeoIndependent (hG 0).cg S) (q : GeoComponent (hG 0).cg S) (t : unitInterval) :
    (Shadow.single ⟨geoCornerCount (hG 0).cg S q, three_le_geoCornerCount hn (hG 0) hS q,
      geoCornerFamily (hG 0).cg S q γ t⟩).Generic := by
  rw [geoCornerFamily_eq_transported (hG 0).cg S q γ t (hG t).cg (geoFamily_transport_zero γ hγc hG t)]
  exact (geoFamily_transport_zero γ hγc hG t).single_generic_transportedCornerPolygon (hG 0) (hG t) hn hS q

/-- **lit:homfly's planar clause along the family**: the positive diagrams of the corner family at the two
ends have the same HOMFLY polynomial. -/
theorem homfly_geoCornerFamily {S : Finset (Crossing (γ 0))} (hS : GeoIndependent (hG 0).cg S)
    (q : GeoComponent (hG 0).cg S) :
    homfly ((Shadow.single ⟨geoCornerCount (hG 0).cg S q, three_le_geoCornerCount hn (hG 0) hS q,
        geoCornerFamily (hG 0).cg S q γ 0⟩).positiveDiagram
        (single_generic_geoCornerFamily hn γ hγc hG hS q 0)) =
      homfly ((Shadow.single ⟨geoCornerCount (hG 0).cg S q, three_le_geoCornerCount hn (hG 0) hS q,
        geoCornerFamily (hG 0).cg S q γ 1⟩).positiveDiagram
        (single_generic_geoCornerFamily hn γ hγc hG hS q 1)) :=
  geo_homfly_positiveDiagram_single_of_family (three_le_geoCornerCount hn (hG 0) hS q)
    (fun t => geoCornerFamily (hG 0).cg S q γ t) (continuous_geoCornerFamily_zero γ hγc hG S q)
    (single_generic_geoCornerFamily hn γ hγc hG hS q)

/-- The positive lift of the transported carrier at time `t` is the positive diagram of the corner family
at `t`. -/
theorem geoPositiveLift_eq_geoCornerFamily {S : Finset (Crossing (γ 0))}
    (hS : GeoIndependent (hG 0).cg S) (q : GeoComponent (hG 0).cg S) (t : unitInterval) :
    geoPositiveLift hn (hG t) (((geoFamily_transport_zero γ hγc hG t).geoIndependent_iff S).mpr hS)
        ((geoFamily_transport_zero γ hγc hG t).component S q) =
      (Shadow.single ⟨geoCornerCount (hG 0).cg S q, three_le_geoCornerCount hn (hG 0) hS q,
        geoCornerFamily (hG 0).cg S q γ t⟩).positiveDiagram
        (single_generic_geoCornerFamily hn γ hγc hG hS q t) := by
  unfold geoPositiveLift
  apply geo_positiveDiagram_congr
  rw [(geoFamily_transport_zero γ hγc hG t).geoCarrierShadow_eq (hG 0) (hG t) hn hS q,
    geoCornerFamily_eq_transported (hG 0).cg S q γ t (hG t).cg (geoFamily_transport_zero γ hγc hG t)]

/-- The positive lift of a carrier of `γ 0` is the positive diagram of the corner family at `0`. -/
theorem geoPositiveLift_zero_eq_geoCornerFamily {S : Finset (Crossing (γ 0))}
    (hS : GeoIndependent (hG 0).cg S) (q : GeoComponent (hG 0).cg S) :
    geoPositiveLift hn (hG 0) hS q =
      (Shadow.single ⟨geoCornerCount (hG 0).cg S q, three_le_geoCornerCount hn (hG 0) hS q,
        geoCornerFamily (hG 0).cg S q γ 0⟩).positiveDiagram
        (single_generic_geoCornerFamily hn γ hγc hG hS q 0) := by
  unfold geoPositiveLift
  apply geo_positiveDiagram_congr
  rw [geoCornerFamily_zero γ hG S q]

/-- **The HOMFLY polynomial of the positive lift of a carrier is constant along the family.** -/
theorem homfly_geoPositiveLift_eq_of_family {S : Finset (Crossing (γ 0))}
    (hS : GeoIndependent (hG 0).cg S) (q : GeoComponent (hG 0).cg S) :
    homfly (geoPositiveLift hn (hG 1) (((geoFamily_transport_zero γ hγc hG 1).geoIndependent_iff S).mpr hS)
        ((geoFamily_transport_zero γ hγc hG 1).component S q)) =
      homfly (geoPositiveLift hn (hG 0) hS q) := by
  rw [geoPositiveLift_eq_geoCornerFamily hn γ hγc hG hS q 1,
    geoPositiveLift_zero_eq_geoCornerFamily hn γ hγc hG hS q]
  exact (homfly_geoCornerFamily hn γ hγc hG hS q).symm

end FamilyTier1

/-! ## 4. Endpoint packages and the path theorems

Two layers, so that the combinatorial and rotation facts do not inherit `lit:homfly`'s axiom
(`SM.lit_homfly`) through the packaging: the *core* (`GeoPathCore`, `GeoWeakPathCore`: transport, parameter
order, rotations, vertex turns — standard axioms) and the *data* (`GeoPathData`, `GeoWeakPathData`: core +
the HOMFLY clause, which needs `homfly_planar`). -/

/-- **Tier-1 path core** between two `CarrierGeometry` polygons with the same crossing supports: a mark
transport, the same-edge parameter order, and constant carrier rotations, carrier by carrier (every carrier
is the owner of some mark). Axioms: standard. -/
structure GeoPathCore (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) : Prop where
  /-- the mark transport (marks, interlacement, signs) -/
  transport : GeoMarkTransport hGP.cg hGQ.cg hs
  /-- the same-edge crossing-parameter order agrees (the local datum of `geometric_records_persist`) -/
  order_agrees : CrossingParameterOrderAgrees P Q
  /-- lem:rot (ii): the rotation of every carrier of an independent set is carried -/
  rotation_eq : ∀ (S : Finset (Crossing P)), GeoIndependent hGP.cg S → ∀ a : Mark P,
    geoCarrierRotation hGQ.cg (transportSupport hs S)
        (geoOwner hGQ.cg (transportSupport hs S) (markTransport hs a)) =
      geoCarrierRotation hGP.cg S (geoOwner hGP.cg S a)

/-- **Tier-2 path core**: the tier-1 core plus constant vertex turns. Axioms: standard. -/
structure GeoWeakPathCore (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) : Prop extends GeoPathCore hGP hGQ hs where
  /-- the vertex turn signs agree -/
  turn_eq : ∀ i, turn Q i = turn P i

/-- **Tier-1 path data**: the core plus constant HOMFLY polynomials of the positive lifts, carrier by
carrier (lit:homfly's planar clause; axiom `SM.lit_homfly`). -/
structure GeoPathData (hn : 3 ≤ n) (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) : Prop extends GeoPathCore hGP hGQ hs where
  /-- lit:homfly (planar): the HOMFLY polynomial of the positive lift of every carrier is carried -/
  homfly_eq : ∀ (S : Finset (Crossing P)) (hS : GeoIndependent hGP.cg S)
    (hS' : GeoIndependent hGQ.cg (transportSupport hs S)) (a : Mark P),
    homfly (geoPositiveLift hn hGQ hS' (geoOwner hGQ.cg (transportSupport hs S) (markTransport hs a))) =
      homfly (geoPositiveLift hn hGP hS (geoOwner hGP.cg S a))

/-- **Tier-2 path data**: the tier-2 core plus the HOMFLY clause. -/
structure GeoWeakPathData (hn : 3 ≤ n) (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) : Prop extends GeoWeakPathCore hGP hGQ hs where
  /-- lit:homfly (planar): the HOMFLY polynomial of the positive lift of every carrier is carried -/
  homfly_eq : ∀ (S : Finset (Crossing P)) (hS : GeoIndependent hGP.cg S)
    (hS' : GeoIndependent hGQ.cg (transportSupport hs S)) (a : Mark P),
    homfly (geoPositiveLift hn hGQ hS' (geoOwner hGQ.cg (transportSupport hs S) (markTransport hs a))) =
      homfly (geoPositiveLift hn hGP hS (geoOwner hGP.cg S a))

namespace GeoPathCore

variable {hGP : CarrierGeometry P} {hGQ : CarrierGeometry Q}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s}

/-- The identification is determined by the supports: a core along one is a core along any. -/
theorem congr_hs (d : GeoPathCore hGP hGQ hs) {hs' : ∀ s, IsCrossing P s ↔ IsCrossing Q s} :
    GeoPathCore hGP hGQ hs' := by
  have : hs = hs' := Subsingleton.elim _ _
  subst this
  exact d

/-- The rotation clause on an arbitrary carrier, through the transport's carrier bijection. -/
theorem rotation_eq' (d : GeoPathCore hGP hGQ hs) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S) :
    geoCarrierRotation hGQ.cg (transportSupport hs S) (d.transport.component S q) =
      geoCarrierRotation hGP.cg S q := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective hGP.cg S q
  exact d.rotation_eq S hS a

/-- The integer rotation `r_Q` (def:uniform, `geoCarrierRotationInt`) is carried. -/
theorem rotationInt_eq (d : GeoPathCore hGP hGQ hs) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S) :
    geoCarrierRotationInt hGQ.cg (transportSupport hs S) (d.transport.component S q) =
      geoCarrierRotationInt hGP.cg S q := by
  unfold geoCarrierRotationInt
  rw [d.rotation_eq' hS q]

/-- The Gauss lists are carried (the accepted `geometricGaussList_transport`). -/
theorem gaussList_eq (d : GeoPathCore hGP hGQ hs) :
    (geometricGaussList hGP.cg).map (visitTransport hs) = geometricGaussList hGQ.cg :=
  geometricGaussList_transport hGP.cg hGQ.cg hs d.order_agrees

/-- The Gauss words are carried (the accepted `geometricGaussWord_transport`). -/
theorem gaussWord_eq (d : GeoPathCore hGP hGQ hs) :
    (geometricGaussWord hGP.cg).map (crossingTransport hs) = geometricGaussWord hGQ.cg :=
  geometricGaussWord_transport hGP.cg hGQ.cg hs d.order_agrees

/-- **The complete geometric records agree** (`GeometricRecordsAgree`, SM/GeometricRecords.lean) between
the two ends. -/
theorem recordsAgree (d : GeoPathCore hGP hGQ hs) : GeometricRecordsAgree hGP.cg hGQ.cg :=
  ⟨hs, d.gaussList_eq, d.gaussWord_eq, d.transport.interlaces_iff, d.transport.sign_eq⟩

/-- The number of retained crossings of a carrier is carried. -/
theorem card_geoCarrierCrossings_eq (d : GeoPathCore hGP hGQ hs) (S : Finset (Crossing P))
    (q : GeoComponent hGP.cg S) :
    (geoCarrierCrossings hGQ.cg (transportSupport hs S) (d.transport.component S q)).card =
      (geoCarrierCrossings hGP.cg S q).card :=
  d.transport.card_geoCarrierCrossings_eq S q

/-- **Path core from a continuous family of `CarrierGeometry` polygons**, between its two ends. -/
theorem of_family (hn : 3 ≤ n) (γ : unitInterval → LabelledTuple n) (hγc : Continuous γ)
    (hG : ∀ t, CarrierGeometry (γ t)) :
    GeoPathCore (hG 0) (hG 1) (geoFamily_crossing_iff γ hγc (fun u => (hG u).cg) 0 1) where
  transport := geoFamily_transport_zero γ hγc hG 1
  order_agrees := geoFamily_orderAgrees γ hγc (fun u => (hG u).cg) 0 1
  rotation_eq := fun S hS a =>
    geoCarrierRotation_eq_of_family hn γ hγc hG hS (geoOwner (hG 0).cg S a) 1

/-- **Path core from a `Path P Q` of `CarrierGeometry` polygons** (endpoints transferred by
generalisation along `γ.source`, `γ.target`). -/
theorem of_path (hn : 3 ≤ n) (γ : Path P Q) (hG : ∀ t, CarrierGeometry (γ t))
    (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s, GeoPathCore hGP hGQ hs := by
  have key : ∀ (P' Q' : LabelledTuple n) (hGP' : CarrierGeometry P') (hGQ' : CarrierGeometry Q'),
      γ 0 = P' → γ 1 = Q' → ∃ hs : ∀ s, IsCrossing P' s ↔ IsCrossing Q' s, GeoPathCore hGP' hGQ' hs := by
    intro P' Q' hGP' hGQ' h0 h1
    subst h0 h1
    exact ⟨_, of_family hn γ γ.continuous hG⟩
  exact key P Q hGP hGQ γ.source γ.target

end GeoPathCore

namespace GeoWeakPathCore

variable {hGP : CarrierGeometry P} {hGQ : CarrierGeometry Q}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s}

theorem congr_hs (d : GeoWeakPathCore hGP hGQ hs) {hs' : ∀ s, IsCrossing P s ↔ IsCrossing Q s} :
    GeoWeakPathCore hGP hGQ hs' := by
  have : hs = hs' := Subsingleton.elim _ _
  subst this
  exact d

/-- Uniformity of a carrier is carried. -/
theorem geoCarrierUniform_iff (hn : 3 ≤ n) (d : GeoWeakPathCore hGP hGQ hs) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S) :
    geoCarrierUniform hGQ.cg (transportSupport hs S) (d.transport.component S q) ↔
      geoCarrierUniform hGP.cg S q :=
  d.transport.geoCarrierUniform_iff hn d.turn_eq hS q

/-- The selector / def:wind weight of a carrier is carried. -/
theorem geoCarrierSelector_eq (hn : 3 ≤ n) (d : GeoWeakPathCore hGP hGQ hs) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S) :
    geoCarrierSelector hGQ.cg (transportSupport hs S) (d.transport.component S q) =
      geoCarrierSelector hGP.cg S q :=
  d.transport.geoCarrierSelector_eq hn d.turn_eq hS q

/-- **`geoWind` is carried.** -/
theorem geoWind_eq (hn : 3 ≤ n) (d : GeoWeakPathCore hGP hGQ hs) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) :
    geoWind hGQ.cg (transportSupport hs S) = geoWind hGP.cg S :=
  d.transport.geoWind_eq hn d.turn_eq hS

/-- The corner turns of a carrier are carried (at the cast index). -/
theorem turn_geoCornerPolygon_eq (hn : 3 ≤ n) (d : GeoWeakPathCore hGP hGQ hs) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S)
    (j : ZMod (geoCornerCount hGQ.cg (transportSupport hs S) (d.transport.component S q))) :
    turn (geoCornerPolygon hGQ.cg (transportSupport hs S) (d.transport.component S q)) j =
      turn (geoCornerPolygon hGP.cg S q)
        (Equiv.cast (congrArg ZMod (d.transport.geoCornerCount_eq S q)) j) :=
  d.transport.turn_geoCornerPolygon_eq hn d.turn_eq hS q j

/-- **Tier-2 path core from a continuous family of weakly generic polygons.** -/
theorem of_family (hn : 3 ≤ n) (γ : unitInterval → LabelledTuple n) (hγc : Continuous γ)
    (hW : ∀ t, WeakGeneric (γ t)) :
    GeoWeakPathCore (hW 0).carrierGeometry (hW 1).carrierGeometry
      (geoFamily_crossing_iff γ hγc (fun u => (hW u).carrierGeometry.cg) 0 1) where
  toGeoPathCore := GeoPathCore.of_family hn γ hγc (fun t => (hW t).carrierGeometry)
  turn_eq := fun i => geoFamily_turn_eq_of_weak γ hγc hW 0 1 i

/-- **Tier-2 path core from a `Path P Q` of weakly generic polygons.** -/
theorem of_path (hn : 3 ≤ n) (γ : Path P Q) (hW : ∀ t, WeakGeneric (γ t))
    (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s, GeoWeakPathCore hGP hGQ hs := by
  have key : ∀ (P' Q' : LabelledTuple n) (hGP' : CarrierGeometry P') (hGQ' : CarrierGeometry Q'),
      γ 0 = P' → γ 1 = Q' →
        ∃ hs : ∀ s, IsCrossing P' s ↔ IsCrossing Q' s, GeoWeakPathCore hGP' hGQ' hs := by
    intro P' Q' hGP' hGQ' h0 h1
    subst h0 h1
    exact ⟨_, of_family hn γ γ.continuous hW⟩
  exact key P Q hGP hGQ γ.source γ.target

end GeoWeakPathCore

namespace GeoPathData

variable {hn : 3 ≤ n} {hGP : CarrierGeometry P} {hGQ : CarrierGeometry Q}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s}

theorem congr_hs (d : GeoPathData hn hGP hGQ hs) {hs' : ∀ s, IsCrossing P s ↔ IsCrossing Q s} :
    GeoPathData hn hGP hGQ hs' := by
  have : hs = hs' := Subsingleton.elim _ _
  subst this
  exact d

/-- The HOMFLY clause on an arbitrary carrier, through the transport's carrier bijection. -/
theorem homfly_eq' (d : GeoPathData hn hGP hGQ hs) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S) :
    homfly (geoPositiveLift hn hGQ ((d.transport.geoIndependent_iff S).mpr hS)
        (d.transport.component S q)) =
      homfly (geoPositiveLift hn hGP hS q) := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective hGP.cg S q
  exact d.homfly_eq S hS _ a

/-- **Path data from a continuous family of `CarrierGeometry` polygons**, between its two ends. -/
theorem of_family (hn : 3 ≤ n) (γ : unitInterval → LabelledTuple n) (hγc : Continuous γ)
    (hG : ∀ t, CarrierGeometry (γ t)) :
    GeoPathData hn (hG 0) (hG 1) (geoFamily_crossing_iff γ hγc (fun u => (hG u).cg) 0 1) where
  toGeoPathCore := GeoPathCore.of_family hn γ hγc hG
  homfly_eq := fun S hS _ a =>
    homfly_geoPositiveLift_eq_of_family hn γ hγc hG hS (geoOwner (hG 0).cg S a)

/-- **Path data from a `Path P Q` of `CarrierGeometry` polygons.** -/
theorem of_path (hn : 3 ≤ n) (γ : Path P Q) (hG : ∀ t, CarrierGeometry (γ t))
    (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s, GeoPathData hn hGP hGQ hs := by
  have key : ∀ (P' Q' : LabelledTuple n) (hGP' : CarrierGeometry P') (hGQ' : CarrierGeometry Q'),
      γ 0 = P' → γ 1 = Q' → ∃ hs : ∀ s, IsCrossing P' s ↔ IsCrossing Q' s, GeoPathData hn hGP' hGQ' hs := by
    intro P' Q' hGP' hGQ' h0 h1
    subst h0 h1
    exact ⟨_, of_family hn γ γ.continuous hG⟩
  exact key P Q hGP hGQ γ.source γ.target

end GeoPathData

namespace GeoWeakPathData

variable {hn : 3 ≤ n} {hGP : CarrierGeometry P} {hGQ : CarrierGeometry Q}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s}

theorem congr_hs (d : GeoWeakPathData hn hGP hGQ hs) {hs' : ∀ s, IsCrossing P s ↔ IsCrossing Q s} :
    GeoWeakPathData hn hGP hGQ hs' := by
  have : hs = hs' := Subsingleton.elim _ _
  subst this
  exact d

/-- The tier-1 data of tier-2 data. -/
theorem toGeoPathData (d : GeoWeakPathData hn hGP hGQ hs) : GeoPathData hn hGP hGQ hs :=
  ⟨d.toGeoPathCore, d.homfly_eq⟩

/-- The HOMFLY clause on an arbitrary carrier. -/
theorem homfly_eq' (d : GeoWeakPathData hn hGP hGQ hs) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S) :
    homfly (geoPositiveLift hn hGQ ((d.transport.geoIndependent_iff S).mpr hS)
        (d.transport.component S q)) =
      homfly (geoPositiveLift hn hGP hS q) :=
  d.toGeoPathData.homfly_eq' hS q

/-- **Tier-2 path data from a continuous family of weakly generic polygons.** -/
theorem of_family (hn : 3 ≤ n) (γ : unitInterval → LabelledTuple n) (hγc : Continuous γ)
    (hW : ∀ t, WeakGeneric (γ t)) :
    GeoWeakPathData hn (hW 0).carrierGeometry (hW 1).carrierGeometry
      (geoFamily_crossing_iff γ hγc (fun u => (hW u).carrierGeometry.cg) 0 1) where
  toGeoWeakPathCore := GeoWeakPathCore.of_family hn γ hγc hW
  homfly_eq := fun S hS _ a =>
    homfly_geoPositiveLift_eq_of_family hn γ hγc (fun t => (hW t).carrierGeometry) hS
      (geoOwner (hW 0).carrierGeometry.cg S a)

/-- **Tier-2 path data from a `Path P Q` of weakly generic polygons.** -/
theorem of_path (hn : 3 ≤ n) (γ : Path P Q) (hW : ∀ t, WeakGeneric (γ t))
    (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s, GeoWeakPathData hn hGP hGQ hs := by
  have key : ∀ (P' Q' : LabelledTuple n) (hGP' : CarrierGeometry P') (hGQ' : CarrierGeometry Q'),
      γ 0 = P' → γ 1 = Q' →
        ∃ hs : ∀ s, IsCrossing P' s ↔ IsCrossing Q' s, GeoWeakPathData hn hGP' hGQ' hs := by
    intro P' Q' hGP' hGQ' h0 h1
    subst h0 h1
    exact ⟨_, of_family hn γ γ.continuous hW⟩
  exact key P Q hGP hGQ γ.source γ.target

end GeoWeakPathData

/-! ### 4b. The culminating path theorems -/

/-- **`geoWind` is constant along a path of weakly generic polygons** (def:wind on the geo lane; the
CV-chamber instance is CV/ChamberInvII). Standard axioms. -/
theorem geoWind_eq_of_path (hn : 3 ≤ n) (γ : Path P Q) (hW : ∀ t, WeakGeneric (γ t))
    (hP : CrossingGeometry P) (hQ : CrossingGeometry Q) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s,
      GeoMarkTransport hP hQ hs ∧ (∀ i, turn Q i = turn P i) ∧
      ∀ S : Finset (Crossing P), GeoIndependent hP S →
        geoWind hQ (transportSupport hs S) = geoWind hP S := by
  obtain ⟨hs, d⟩ := GeoWeakPathCore.of_path hn γ hW (CarrierGeometry.ofWeak (γ.source ▸ hW 0))
    (CarrierGeometry.ofWeak (γ.target ▸ hW 1))
  exact ⟨hs, d.transport, d.turn_eq, fun S hS => d.geoWind_eq hn hS⟩

/-- **The HOMFLY polynomials of the positive lifts are constant along a path of `CarrierGeometry`
polygons** (lit:homfly's planar clause, carrier by carrier). Axioms: standard + `SM.lit_homfly`. -/
theorem homfly_geoPositiveLift_eq_of_path (hn : 3 ≤ n) (γ : Path P Q)
    (hG : ∀ t, CarrierGeometry (γ t)) (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s,
      GeoMarkTransport hGP.cg hGQ.cg hs ∧
      ∀ (S : Finset (Crossing P)) (hS : GeoIndependent hGP.cg S)
        (hS' : GeoIndependent hGQ.cg (transportSupport hs S)) (a : Mark P),
        homfly (geoPositiveLift hn hGQ hS'
            (geoOwner hGQ.cg (transportSupport hs S) (markTransport hs a))) =
          homfly (geoPositiveLift hn hGP hS (geoOwner hGP.cg S a)) := by
  obtain ⟨hs, d⟩ := GeoPathData.of_path hn γ hG hGP hGQ
  exact ⟨hs, d.transport, d.homfly_eq⟩

/-- **The carrier rotations are constant along a path of `CarrierGeometry` polygons** (lem:rot (ii)).
Standard axioms. -/
theorem geoCarrierRotation_eq_of_path (hn : 3 ≤ n) (γ : Path P Q)
    (hG : ∀ t, CarrierGeometry (γ t)) (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s,
      GeoMarkTransport hGP.cg hGQ.cg hs ∧
      ∀ (S : Finset (Crossing P)), GeoIndependent hGP.cg S → ∀ a : Mark P,
        geoCarrierRotation hGQ.cg (transportSupport hs S)
            (geoOwner hGQ.cg (transportSupport hs S) (markTransport hs a)) =
          geoCarrierRotation hGP.cg S (geoOwner hGP.cg S a) := by
  obtain ⟨hs, d⟩ := GeoPathCore.of_path hn γ hG hGP hGQ
  exact ⟨hs, d.transport, d.rotation_eq⟩

end SM.GeoCarrier
