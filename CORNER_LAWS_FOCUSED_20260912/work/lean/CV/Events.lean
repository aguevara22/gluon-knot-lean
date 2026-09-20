import CV.Setup
import SM.GeometricInterlacement
import SM.InterlaceCount
import SM.GenericTopology

/-! CV lane, module CV.Events: CV:def:interlace (reference/R/CV/d1_setup.tex 346-353, on the accepted geometric interlacement graph),
CV:def:event (1072-1097: the structure `CV.Event` — a continuous path of polygons generic off the centre — with zero set, side chambers,
sign changes and transversality), CV:lem:guardconst (1107-1121) and CV:def:silent (1265-1271: `Event.Silent`; the forced RIII bundle `Event.IsSimpleRIII` of CV ax:R, d10_axioms.tex:18-24, is defined here for the later ax:R rows and is NOT part of that definition),
each with a row bundle and its theorem (`CV.interlace_definition`, `CV.event_definition`, `CV.guardconst`, `CV.silent_definition`).
Follows the CV-lane plan (work/reports/cv-lane-plan-20260913.md) and decision F2 (no domain narrowing). Written 2026-09-13 by Claude
Code implementer subagents of the pod executor (workflow implement-cv-definitions, then unified with CV.Setup by a second subagent),
checked with `lake env lean` (placeholder-free, standard axioms) and ported verbatim from work/drafts/CV_Events_unified.lean (only this header
added and #print lines removed). Revised 2026-09-13 (work/drafts/CV_Events_rev.lean, after an independent review of rows 134 and 148):
row 134's bundle lost the `U(S)` clause and the cross-lane `generic_agree` clause (now the standalone theorem
`CV.interlace_generic_agree`) and gained the printed vertex set — the crossing point map is a bijection from `SM.Crossing P` onto the
double points `CV.selfIntersections P` of a diagrammatic polygon (`vertices`, `vertex_ncard`); row 148's bundle gained the printed
tangency example `CV.tangencyExample : Event 4` with its claims (`EventExampleData`, field `tangency_example`). -/

/-! CV lane, rows 134 (CV:def:interlace, d1_setup.tex:346–353), 148 (CV:def:event,
d1_setup.tex:1072–1097), 149 (CV:lem:guardconst, d1_setup.tex:1107–1121) and 150
(CV:def:silent, d1_setup.tex:1265–1271; `Event.IsSimpleRIII` renders the forced RIII bundle of d10_axioms.tex:18–24 for the later ax:R rows and is outside the def:silent bundle).
Source: reference/R/CV/d1_setup.tex, d10_axioms.tex (frozen).

Row declarations: `CV.interlace_definition : CV.InterlaceData hP` (134),
`CV.event_definition : CV.EventData E` (148), `CV.guardconst` (149),
`CV.silent_definition : CV.SilentData E` (150).

Domain (decision F2, work/AUTHOR_NOTES.md): no narrowing. def:interlace is stated on the class
where CV's Gauss word exists, carried here by the accepted `SM.CrossingGeometry P` (fidelity fact
F3 of the lane plan: CV's diagrammatic class is `CrossingGeometry ∧ no vertex on a non-incident
segment`; only `CrossingGeometry` is used by the geometric Gauss/interlacement API). The event
rows are stated on CV's own guarded genericity.

Deviations from the lane plan's Appendix A skeleton (to be recorded at porting): (i) `Event`
carries the extra field `center_polygon` — the printed "path of polygons" makes `P(0)` a CV
polygon (nonzero edges), which does not follow from the other fields; (ii) row 134 takes the
binder `hP : CrossingGeometry P` rather than `Diagrammatic P` (row 133's
`Diagrammatic → CrossingGeometry` specialises it); (iii) the chamber of a point is
`CV.chamber Q` without a genericity proof argument.

Unification (2026-09-13). This file supersedes work/drafts/CV_Events.lean, which predated the
module `CV.Setup` and carried `Ev`-prefixed copies of the guarded-list skeleton. Every such copy
is gone: the guarded list of CV:def:guarded (d1_setup.tex:42–218) and CV:def:generic (220–238)
are taken from `CV.Setup` — `CV.IsPolygon`, `CV.rep`, `CV.lineForm`, `CV.G1`, `CV.G2`, `CV.G5`,
`CV.G3`, `CV.G4`, `CV.Crosses`, the indexed family `CV.Member` (with `eval`, `Unconditional`,
`Active`, `Relevant`, `continuous_eval`), `CV.Generic`, `CV.genericLocus` and `CV.chamber`. The
only guarded-list fact used here that `CV.Setup` does not state, the vanishing criterion
`CV.G2_eq_zero_iff`, is proved below. Inside `namespace CV` the bare name `Generic` is CV's;
SM's genericity is always written `SM.Generic` (the cross-lane theorem `interlace_generic_agree`). -/

namespace CV

open SM Filter Topology

variable {n : ℕ}

/-! ## Row 134 — CV:def:interlace (d1_setup.tex:346–353)

Printed text: "The interlacement graph $G_P$ has vertex set $[m]=\{1,\dots,m\}$, with $c\sim c'$
if and only if exactly one of the two occurrences of $c'$ lies between the two occurrences of $c$
in the Gauss word. (The relation is symmetric.) We write $\Ind(G_P)$ for the set of independent
sets of $G_P$, including $\varnothing$, and $N_{G_P}(S)$ for the set of vertices adjacent to some
element of $S$."

The graph is the accepted `SM.geometricInterlacementGraph hP` on the actual crossing type
`SM.Crossing P` — the vertex set `[m]`: for a diagrammatic polygon (d1_setup.tex:303–313, the class
fixed for the whole subsection) the crossing point map is a bijection of `SM.Crossing P` onto the
printed double points `CV.selfIntersections P` (`crossingPoint_bijOn`), so `m` is their number — whose adjacency
`SM.GeometricInterlaces` is the alternating-visit form; the printed "exactly one occurrence
between" clause is proved equivalent below (`geometricInterlaces_iff_unique`) for the whole
`CrossingGeometry` class, where the two occurrences of a crossing `c` in the Gauss word are its two
visits `⟨c, c₀⟩`, `⟨c, c₁⟩` at their geometric traversal positions `SM.geometricVisitPosition`. -/

section Interlace

variable {P : LabelledTuple n}

theorem geometricVisitPosition_ne_of_ne (hP : CrossingGeometry P) {x y : Crossing P}
    (hxy : x ≠ y) (i : {k // k ∈ x.val}) (j : {k // k ∈ y.val}) :
    geometricVisitPosition hP ⟨x, i⟩ ≠ geometricVisitPosition hP ⟨y, j⟩ := by
  intro he
  exact hxy (congrArg Sigma.fst (geometricVisitPosition_injective hP he))

theorem geometricVisitPosition_ne_of_visit_ne (hP : CrossingGeometry P) (x : Crossing P)
    {i j : {k // k ∈ x.val}} (hij : i ≠ j) :
    geometricVisitPosition hP ⟨x, i⟩ ≠ geometricVisitPosition hP ⟨x, j⟩ := by
  intro he
  have h := geometricVisitPosition_injective hP he
  exact hij (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem geometricInterlaces_comm (hP : CrossingGeometry P) (x y : Crossing P) :
    GeometricInterlaces hP x y ↔ GeometricInterlaces hP y x :=
  ⟨geometricInterlaces_symm hP, geometricInterlaces_symm hP⟩

variable [NeZero n]

/-- On the geometric domain the two open arcs cut by the two visits of `x` are complementary
for the visits of another crossing `y`. -/
theorem geometricCrossingVisitBetween_complement (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j : {i // i ∈ y.val}) :
    geometricCrossingVisitBetween hP x x₀ x₁ y j ↔
      ¬ geometricCrossingVisitBetween hP x x₁ x₀ y j := by
  apply traversalBetween_complement
  · exact geometricVisitPosition_ne_of_ne hP hxy x₀ j
  · exact geometricVisitPosition_ne_of_ne hP hxy.symm j x₁
  · exact geometricVisitPosition_ne_of_visit_ne hP x hx.symm

theorem geometric_alternating_visits_iff_unique (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    (∃ y₀ y₁ : {i // i ∈ y.val}, y₀ ≠ y₁ ∧
      geometricCrossingVisitBetween hP x x₀ x₁ y y₀ ∧
      geometricCrossingVisitBetween hP x x₁ x₀ y y₁) ↔
      ∃! j, geometricCrossingVisitBetween hP x x₀ x₁ y j := by
  rw [crossing_unique_visit_iff]
  constructor
  · rintro ⟨y₀, y₁, hy, h₀, h₁⟩
    exact ⟨y₀, y₁, hy, h₀,
      (geometricCrossingVisitBetween_complement hP hxy x₁ x₀ hx.symm y₁).mp h₁⟩
  · rintro ⟨y₀, y₁, hy, h₀, h₁⟩
    exact ⟨y₀, y₁, hy, h₀,
      (geometricCrossingVisitBetween_complement hP hxy x₁ x₀ hx.symm y₁).mpr h₁⟩

theorem geometric_unique_between_swap (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    (∃! j, geometricCrossingVisitBetween hP x x₀ x₁ y j) ↔
      ∃! j, geometricCrossingVisitBetween hP x x₁ x₀ y j := by
  rw [← geometric_alternating_visits_iff_unique hP hxy x₀ x₁ hx,
    ← geometric_alternating_visits_iff_unique hP hxy x₁ x₀ hx.symm]
  constructor <;> rintro ⟨a, b, hab, ha, hb⟩
  · exact ⟨b, a, hab.symm, hb, ha⟩
  · exact ⟨b, a, hab.symm, hb, ha⟩

/-- The printed clause of def:interlace: `c ∼ c'` iff exactly one of the two occurrences of `c'`
lies between the two occurrences of `c` — for either order of the two occurrences of `c`. -/
theorem geometricInterlaces_iff_unique (hP : CrossingGeometry P)
    (x y : Crossing P) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    GeometricInterlaces hP x y ↔ x ≠ y ∧
      ∃! j, geometricCrossingVisitBetween hP x x₀ x₁ y j := by
  constructor
  · rintro ⟨hxy, a, b, c, d, hab, hcd, h₀, h₁⟩
    refine ⟨hxy, ?_⟩
    have hu := (geometric_alternating_visits_iff_unique hP hxy a b hab).mp ⟨c, d, hcd, h₀, h₁⟩
    rcases crossing_visits_exhaust x x₀ x₁ hx a with he | he
    · subst a
      have hb : b = x₁ := by
        rcases crossing_visits_exhaust x x₀ x₁ hx b with hb | hb
        · exact (hab hb.symm).elim
        · exact hb
      simpa only [hb] using hu
    · subst a
      have hb : b = x₀ := by
        rcases crossing_visits_exhaust x x₀ x₁ hx b with hb | hb
        · exact hb
        · exact (hab hb.symm).elim
      rw [hb] at hu
      exact (geometric_unique_between_swap hP hxy x₀ x₁ hx).mpr hu
  · rintro ⟨hxy, hu⟩
    obtain ⟨a, b, hab, ha, hb⟩ :=
      (geometric_alternating_visits_iff_unique hP hxy x₀ x₁ hx).mpr hu
    exact ⟨hxy, x₀, x₁, a, b, hx, hab, ha, hb⟩

/-- `Ind(G_P)`: "the set of independent sets of $G_P$, including $\varnothing$"
(d1_setup.tex:350–351), on the actual finite crossing type. -/
noncomputable def Ind (hP : CrossingGeometry P) : Finset (Finset (Crossing P)) := by
  classical
  exact Finset.univ.powerset.filter fun S => (geometricInterlacementGraph hP).IsIndepSet ↑S

/-- `N_{G_P}(S)`: "the set of vertices adjacent to some element of $S$" (d1_setup.tex:351–352),
defined for every support `S`. -/
noncomputable def N (hP : CrossingGeometry P) (S : Finset (Crossing P)) : Finset (Crossing P) := by
  classical
  exact Finset.univ.filter fun y => ∃ x ∈ S, GeometricInterlaces hP y x

/-- `U(S)`: the vertices neither in `S` nor adjacent to it (the SM complement `U(S)` of
def:interlace, kept here because the CV carrier rows read it). -/
noncomputable def U (hP : CrossingGeometry P) (S : Finset (Crossing P)) : Finset (Crossing P) := by
  classical
  exact Finset.univ \ (S ∪ N hP S)

theorem mem_Ind (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    S ∈ Ind hP ↔ (geometricInterlacementGraph hP).IsIndepSet ↑S := by
  classical
  simp only [Ind, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]

theorem mem_Ind_iff (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    S ∈ Ind hP ↔ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ GeometricInterlaces hP x y :=
  mem_Ind hP S

theorem empty_mem_Ind (hP : CrossingGeometry P) : ∅ ∈ Ind hP := by
  rw [mem_Ind_iff]
  simp

theorem mem_N (hP : CrossingGeometry P) (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ N hP S ↔ ∃ x ∈ S, GeometricInterlaces hP y x := by
  classical
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_U (hP : CrossingGeometry P) (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ U hP S ↔ y ∉ S ∧ y ∉ N hP S := by
  classical
  simp only [U, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, not_or, true_and]

theorem Ind_eq_generic (hn : 3 ≤ n) (hG : SM.Generic P) (hP : CrossingGeometry P) :
    Ind hP = independentSupports hn hG := by
  ext S
  rw [mem_Ind, mem_independentSupports, geometricInterlacementGraph_eq_generic hn hG hP]

theorem N_eq_generic (hn : 3 ≤ n) (hG : SM.Generic P) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) : N hP S = supportNeighbors hn hG S := by
  ext y
  rw [mem_N, mem_supportNeighbors]
  simp only [geometricInterlaces_iff_generic hn hG hP]

theorem U_eq_generic (hn : 3 ≤ n) (hG : SM.Generic P) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) : U hP S = supportUnselected hn hG S := by
  ext y
  rw [mem_U, mem_supportUnselected, N_eq_generic hn hG hP]

/-! ### The vertex set `[m]`: crossings are the double points of a diagrammatic polygon -/

omit [NeZero n] in
/-- Every crossing point of a diagrammatic polygon is a printed double point: it has the two
distinct preimages `(i, s)`, `(j, t)` on its two (remote, hence distinct) edges. -/
theorem crossingPoint_mem_selfIntersections (hD : Diagrammatic P) (c : Crossing P) :
    crossingPoint c ∈ selfIntersections P := by
  have hCG := hD.crossingGeometry
  obtain ⟨i, j, hs, hr, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  obtain ⟨s, hs0, hs1, hxs⟩ := crossingPoint_interior_of_geometry hCG c i hi
  obtain ⟨t, ht0, ht1, hxt⟩ := crossingPoint_interior_of_geometry hCG c j hj
  refine ⟨(i, s), ⟨⟨hs0.le, hs1⟩, hxs.symm⟩, (j, t), ⟨⟨ht0.le, ht1⟩, hxt.symm⟩, fun h => ?_⟩
  exact (remote_endpoints i j hr).1 (congrArg Prod.fst h).symm

omit [NeZero n] in
/-- Every double point of a diagrammatic polygon (`n ≥ 3`) is the point of an actual crossing. -/
theorem exists_crossing_of_selfIntersection (hn : 3 ≤ n) (hD : Diagrammatic P) {x : Plane}
    (hx : x ∈ selfIntersections P) : ∃ c : Crossing P, crossingPoint c = x := by
  have hCG := hD.crossingGeometry
  obtain ⟨⟨i, s⟩, hp, ⟨j, t⟩, hq, hne⟩ := hx
  obtain ⟨_, hr, hxi, hxj, _⟩ := selfIntersection_geometry hn hCG hD.2.2.2.2 hp hq hne
  have hxi' := edgeInterior_subset_edgeSegment P i hxi
  have hxj' := edgeInterior_subset_edgeSegment P j hxj
  refine ⟨⟨{i, j}, i, j, rfl, hr, x, hxi', hxj'⟩, ?_⟩
  symm
  apply crossingPoint_unique_of_geometry hCG
  intro k hk
  have hk' : k ∈ ({i, j} : Finset (ZMod n)) := hk
  rw [Finset.mem_insert, Finset.mem_singleton] at hk'
  rcases hk' with rfl | rfl
  · exact hxi'
  · exact hxj'

omit [NeZero n] in
/-- The printed vertex set `[m] = {1, …, m}` of `G_P` (d1_setup.tex:303–313, 346): on a diagrammatic
polygon (`n ≥ 3`) the crossing point map is a bijection from the actual crossings `SM.Crossing P`
onto the printed double points `selfIntersections P`. -/
theorem crossingPoint_bijOn (hn : 3 ≤ n) (hD : Diagrammatic P) :
    Set.BijOn (fun c : Crossing P => crossingPoint c) Set.univ (selfIntersections P) := by
  refine ⟨fun c _ => crossingPoint_mem_selfIntersections hD c,
    (crossingPoint_injective_of_geometry hD.crossingGeometry).injOn, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := exists_crossing_of_selfIntersection hn hD hx
  exact ⟨c, Set.mem_univ c, hc⟩

/-- `m`, the number of double points, is the number of crossings. -/
theorem ncard_selfIntersections (hn : 3 ≤ n) (hD : Diagrammatic P) :
    (selfIntersections P).ncard = Fintype.card (Crossing P) := by
  have hb := crossingPoint_bijOn hn hD
  rw [← hb.image_eq, hb.injOn.ncard_image, Set.ncard_univ, Nat.card_eq_fintype_card]

/-- CV:def:interlace (d1_setup.tex:346–353), clause by clause, on the geometric domain
`hP : CrossingGeometry P`. -/
structure InterlaceData (hP : CrossingGeometry P) : Prop where
  /-- "vertex set $[m]$": the vertices of `G_P` are the actual crossings, `m` of them. -/
  vertex_count : Fintype.card (Crossing P) = (crossingSet P).card
  /-- "vertex set $[m]=\{1,\dots,m\}$", the `m` double points of the diagrammatic polygon fixed for
  the subsection (d1_setup.tex:303–313): for a diagrammatic `P` (`n ≥ 3`) the crossing point map is
  a bijection from the vertices `Crossing P` of `G_P` onto the printed double points
  `selfIntersections P`. -/
  vertices : ∀ (_hD : Diagrammatic P) (_hn : 3 ≤ n),
    Set.BijOn (fun c : Crossing P => crossingPoint c) Set.univ (selfIntersections P)
  /-- Hence `m = Fintype.card (Crossing P)` is the number of double points. -/
  vertex_ncard : ∀ (_hD : Diagrammatic P) (_hn : 3 ≤ n),
    (selfIntersections P).ncard = Fintype.card (Crossing P)
  /-- "the two occurrences of $c$ in the Gauss word": every visit `⟨c, c₀⟩` occurs in the geometric
  Gauss list, which has length `2m`; its position on the traversal circle is
  `geometricVisitPosition hP ⟨c, c₀⟩`, evaluating to the crossing point. -/
  occurrences : (∀ c : Crossing P, Fintype.card {i // i ∈ c.val} = 2) ∧
    (∀ v : Visit P, v ∈ geometricGaussList hP) ∧
    (geometricGaussList hP).length = 2 * Nat.card (Crossing P) ∧
    ∀ v : Visit P, traversalEvaluation P (geometricVisitPosition hP v) = crossingPoint v.1
  /-- `G_P`'s adjacency is the alternating-visit relation. -/
  adj : ∀ x y : Crossing P, (geometricInterlacementGraph hP).Adj x y ↔ GeometricInterlaces hP x y
  /-- "$c\sim c'$ if and only if exactly one of the two occurrences of $c'$ lies between the two
  occurrences of $c$": for either order `x₀, x₁` of the two visits of `x = c`, exactly one visit
  `j` of `y = c'` lies strictly between them on the traversal circle. -/
  exactly_one_between : ∀ (x y : Crossing P) (x₀ x₁ : {i // i ∈ x.val}), x₀ ≠ x₁ →
    (GeometricInterlaces hP x y ↔ x ≠ y ∧
      ∃! j : {i // i ∈ y.val}, traversalBetween (geometricVisitPosition hP ⟨x, x₀⟩)
        (geometricVisitPosition hP ⟨y, j⟩) (geometricVisitPosition hP ⟨x, x₁⟩))
  /-- "(The relation is symmetric.)" -/
  symm : ∀ x y : Crossing P, GeometricInterlaces hP x y ↔ GeometricInterlaces hP y x
  /-- No crossing is adjacent to itself (simple graph). -/
  irrefl : ∀ x : Crossing P, ¬ GeometricInterlaces hP x x
  /-- "$\Ind(G_P)$ for the set of independent sets of $G_P$". -/
  mem_Ind : ∀ S : Finset (Crossing P), S ∈ Ind hP ↔ (geometricInterlacementGraph hP).IsIndepSet ↑S
  /-- Independence spelled out: no two distinct elements of `S` interlace. -/
  mem_Ind_iff : ∀ S : Finset (Crossing P),
    S ∈ Ind hP ↔ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ GeometricInterlaces hP x y
  /-- "including $\varnothing$". -/
  empty_mem_Ind : ∅ ∈ Ind hP
  /-- "$N_{G_P}(S)$ for the set of vertices adjacent to some element of $S$". -/
  mem_N : ∀ (S : Finset (Crossing P)) (y : Crossing P),
    y ∈ N hP S ↔ ∃ x ∈ S, GeometricInterlaces hP y x

/-- Row 134, CV:def:interlace. -/
theorem interlace_definition (hP : CrossingGeometry P) : InterlaceData hP where
  vertex_count := card_crossing P
  vertices := fun hD hn => crossingPoint_bijOn hn hD
  vertex_ncard := fun hD hn => ncard_selfIntersections hn hD
  occurrences := ⟨visits_per_crossing P, mem_geometricGaussList hP, geometricGaussList_length hP,
    geometricVisitPosition_evaluation hP⟩
  adj := fun _ _ => Iff.rfl
  exactly_one_between := fun x y x₀ x₁ hx => geometricInterlaces_iff_unique hP x y x₀ x₁ hx
  symm := geometricInterlaces_comm hP
  irrefl := geometricInterlaces_irrefl hP
  mem_Ind := mem_Ind hP
  mem_Ind_iff := mem_Ind_iff hP
  empty_mem_Ind := empty_mem_Ind hP
  mem_N := mem_N hP

/-- Cross-lane fact (not a clause of the printed row): on an SM-generic polygon (`n ≥ 3`) the CV
objects of def:interlace are the accepted SM def:interlace objects — the graph, the relation,
`Ind` and `N`. (`U_eq_generic` does the same for the SM complement `U(S)`.) -/
theorem interlace_generic_agree (hP : CrossingGeometry P) (hn : 3 ≤ n) (hG : SM.Generic P) :
    geometricInterlacementGraph hP = interlacementGraph hn hG ∧
    (∀ x y : Crossing P, GeometricInterlaces hP x y ↔ Interlaces hn hG x y) ∧
    Ind hP = independentSupports hn hG ∧
    (∀ S, N hP S = supportNeighbors hn hG S) :=
  ⟨geometricInterlacementGraph_eq_generic hn hG hP, geometricInterlaces_iff_generic hn hG hP,
    Ind_eq_generic hn hG hP, N_eq_generic hn hG hP⟩

end Interlace

/-! ## Supplement to `CV.Setup`: the vanishing of a (G2) member

The guarded list, activation, relevance, CV genericity and CV chambers are those of `CV.Setup`
(rows 131–132: `CV.G1`, …, `CV.Member`, `CV.Generic`, `CV.chamber`). def:silent additionally reads
the vanishing of `G2_{e,i}` at a polygon as "`p_i` on the line of `e`" (d1_setup.tex:1266–1267);
`CV.Setup` gives one direction (`CV.lineForm_edgePoint`), the equivalence is proved here. -/

section G2Vanishing

/-- The vanishing of `G2_{e,i}` at a polygon places `p_i` on the line of `e` (used by def:silent). -/
theorem G2_eq_zero_iff (P : LabelledTuple n) (e i : ZMod n) (he : edge P e ≠ 0) :
    G2 P e i = 0 ↔ ∃ t : ℝ, P i = edgePoint P e t := by
  constructor
  · intro h
    unfold G2 lineForm det at h
    simp only [Prod.fst_sub, Prod.snd_sub] at h
    rcases eq_or_ne (edge P e).1 0 with h1 | h1
    · have h2 : (edge P e).2 ≠ 0 := fun h2 => he (Prod.ext h1 h2)
      refine ⟨((P i).2 - (P e).2) / (edge P e).2, ?_⟩
      have hc1 : (P i).1 - (P e).1 = ((P i).2 - (P e).2) / (edge P e).2 * (edge P e).1 := by
        rw [div_mul_eq_mul_div, eq_div_iff h2]
        linear_combination -h
      ext
      · simp only [edgePoint, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linarith [hc1]
      · simp only [edgePoint, Prod.snd_add, Prod.smul_snd, smul_eq_mul, div_mul_cancel₀ _ h2]
        ring
    · refine ⟨((P i).1 - (P e).1) / (edge P e).1, ?_⟩
      have hc2 : (P i).2 - (P e).2 = ((P i).1 - (P e).1) / (edge P e).1 * (edge P e).2 := by
        rw [div_mul_eq_mul_div, eq_div_iff h1]
        linear_combination h
      ext
      · simp only [edgePoint, Prod.fst_add, Prod.smul_fst, smul_eq_mul, div_mul_cancel₀ _ h1]
        ring
      · simp only [edgePoint, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linarith [hc2]
  · rintro ⟨t, ht⟩
    unfold G2
    rw [ht]
    exact lineForm_edgePoint P e t

end G2Vanishing

/-! ## Row 148 — CV:def:event (d1_setup.tex:1072–1097)

Printed text: "An event is a continuous path $t\mapsto P(t)$ of polygons on $n$ vertices,
$t\in(-\varepsilon,\varepsilon)$, such that $P(t)$ is generic for every $t\neq0$ and $P(0)$ is
not. Its zero set is $Z=\{g\in\mathcal G:\ g(P(0))=0$ and $g$ is relevant at $P(t)$ for some
$t\neq0\}$. The two chambers of the event are the chambers containing $P((-\varepsilon,0))$ and
$P((0,\varepsilon))$; each of those two sets is connected and consists of generic polygons, so
each does lie in one chamber. […] The event is transversal if every member of $Z$ changes sign
at $t=0$."

The structure mirrors `SM.WallGerm` field for field (radius, curve, continuity, punctured
genericity, nongeneric centre) with CV's guarded genericity `CV.Generic` in place of `SM.Generic`,
plus the printed "path of polygons" clause at the centre (`center_polygon`; off the centre it
follows from genericity). Chambers are CV chambers (`CV.chamber`): connected components of the
*labelled* CV-generic locus `CV.genericLocus n` (d1_setup.tex:232–238), no cyclic quotient. -/

section Event

variable [NeZero n]

/-- CV def:event (d1_setup.tex:1072–1076): a continuous path of polygons on `(−ε, ε)`,
CV-generic for every `t ≠ 0` and not at `t = 0`. -/
structure Event (n : ℕ) [NeZero n] where
  radius : ℝ
  radius_pos : 0 < radius
  curve : Set.Ioo (-radius) radius → LabelledTuple n
  continuous_curve : Continuous curve
  center_polygon : IsPolygon (curve ⟨0, by constructor <;> linarith [radius_pos]⟩)
  generic_punctured : ∀ t, t.val ≠ 0 → Generic (curve t)
  nongeneric_center : ¬ Generic (curve ⟨0, by constructor <;> linarith [radius_pos]⟩)

namespace Event

variable (E : Event n)

abbrev Parameter := Set.Ioo (-E.radius) E.radius
abbrev SideParameter := Set.Ioo 0 E.radius

def zeroParameter : E.Parameter := ⟨0, by constructor <;> linarith [E.radius_pos]⟩

/-- `P(0)`. -/
def center : LabelledTuple n := E.curve E.zeroParameter

theorem center_not_generic : ¬ Generic E.center := E.nongeneric_center

theorem center_isPolygon : IsPolygon E.center := E.center_polygon

/-- Every `P(t)` is a polygon (CV def:polygon): at `t ≠ 0` by genericity, at `0` by
`center_polygon`. -/
theorem polygon (t : E.Parameter) : IsPolygon (E.curve t) := by
  by_cases ht : t.val = 0
  · have : t = E.zeroParameter := Subtype.ext ht
    rw [this]
    exact E.center_polygon
  · exact (E.generic_punctured t ht).isPolygon

/-- The parameter `±t` on the positive (`true`) or negative (`false`) side. -/
def sideTime (positive : Bool) (t : E.SideParameter) : E.Parameter :=
  if positive then ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2, E.radius_pos]⟩
  else ⟨-t.val, by constructor <;> linarith [t.property.1, t.property.2, E.radius_pos]⟩

theorem sideTime_ne_zero (positive : Bool) (t : E.SideParameter) :
    (E.sideTime positive t).val ≠ 0 := by
  cases positive <;> simp only [sideTime, Bool.false_eq_true, ↓reduceIte]
  · exact neg_ne_zero.mpr t.property.1.ne'
  · exact t.property.1.ne'

theorem continuous_sideTime (positive : Bool) : Continuous (E.sideTime positive) := by
  cases positive
  · exact continuous_subtype_val.neg.subtype_mk _
  · exact continuous_subtype_val.subtype_mk _

/-- `P(t)` for `t ∈ (0, ε)` (`true`) and `P(−t)` for `t ∈ (0, ε)` (`false`). -/
def sideCurve (positive : Bool) (t : E.SideParameter) : LabelledTuple n :=
  E.curve (E.sideTime positive t)

theorem continuous_sideCurve (positive : Bool) : Continuous (E.sideCurve positive) :=
  E.continuous_curve.comp (E.continuous_sideTime positive)

theorem sideCurve_generic (positive : Bool) (t : E.SideParameter) :
    Generic (E.sideCurve positive t) :=
  E.generic_punctured _ (E.sideTime_ne_zero positive t)

/-- Every nonzero parameter is on exactly the side of its sign. -/
theorem sideTime_surjective_punctured (t : E.Parameter) (ht : t.val ≠ 0) :
    ∃ positive : Bool, ∃ s : E.SideParameter, E.sideTime positive s = t := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine ⟨false, ⟨-t.val, by constructor <;> linarith [t.property.1]⟩, ?_⟩
    apply Subtype.ext
    simp [sideTime]
  · exact ⟨true, ⟨t.val, hpos, t.property.2⟩, rfl⟩

/-- `P((0, ε))` is the image of the positive side. -/
theorem range_sideCurve_true :
    Set.range (E.sideCurve true) = E.curve '' {t : E.Parameter | 0 < t.val} := by
  ext Q
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨E.sideTime true s, s.property.1, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t.val, ht, t.property.2⟩, rfl⟩

/-- `P((−ε, 0))` is the image of the negative side. -/
theorem range_sideCurve_false :
    Set.range (E.sideCurve false) = E.curve '' {t : E.Parameter | t.val < 0} := by
  ext Q
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨E.sideTime false s, ?_, rfl⟩
    show (E.sideTime false s).val < 0
    simp only [sideTime, Bool.false_eq_true, ↓reduceIte]
    linarith [s.property.1]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨-t.val, by constructor <;> linarith [t.property.1, (show t.val < 0 from ht)]⟩, ?_⟩
    simp only [sideCurve]
    congr 1
    apply Subtype.ext
    simp [sideTime]

instance sideParameter_connectedSpace : ConnectedSpace E.SideParameter :=
  isConnected_iff_connectedSpace.mp (isConnected_Ioo E.radius_pos)

/-- "each of those two sets is connected". -/
theorem sideRange_connected (positive : Bool) : IsConnected (Set.range (E.sideCurve positive)) :=
  isConnected_range (E.continuous_sideCurve positive)

/-- "and consists of generic polygons". -/
theorem sideRange_subset_generic (positive : Bool) :
    Set.range (E.sideCurve positive) ⊆ {Q | Generic Q} := by
  rintro Q ⟨t, rfl⟩
  exact E.sideCurve_generic positive t

noncomputable def sideBase : E.SideParameter :=
  ⟨E.radius / 2, by constructor <;> linarith [E.radius_pos]⟩

/-- "The two chambers of the event are the chambers containing $P((-\varepsilon,0))$ and
$P((0,\varepsilon))$": the CV chamber of the positive (`true`) / negative (`false`) side. -/
def sideChamber (positive : Bool) : Set (LabelledTuple n) :=
  chamber (E.sideCurve positive E.sideBase)

/-- "so each does lie in one chamber". -/
theorem sideCurve_mem_sideChamber (positive : Bool) (t : E.SideParameter) :
    E.sideCurve positive t ∈ E.sideChamber positive :=
  subset_chamber (E.sideRange_connected positive).isPreconnected
    (E.sideRange_subset_generic positive) (Set.mem_range_self E.sideBase)
    (Set.mem_range_self t)

theorem sideChamber_eq_at (positive : Bool) (t : E.SideParameter) :
    E.sideChamber positive = chamber (E.sideCurve positive t) :=
  (chamber_eq_of_mem (E.sideCurve_mem_sideChamber positive t)).symm

theorem sideChamber_subset_generic (positive : Bool) :
    E.sideChamber positive ⊆ {Q | Generic Q} :=
  chamber_subset _

theorem sideRange_subset_sideChamber (positive : Bool) :
    Set.range (E.sideCurve positive) ⊆ E.sideChamber positive := by
  rintro Q ⟨t, rfl⟩
  exact E.sideCurve_mem_sideChamber positive t

/-- `P((0, ε))` lies in the positive chamber of the event. -/
theorem curve_mem_sideChamber_pos (t : E.Parameter) (ht : 0 < t.val) :
    E.curve t ∈ E.sideChamber true :=
  E.sideRange_subset_sideChamber true (E.range_sideCurve_true ▸ ⟨t, ht, rfl⟩)

/-- `P((−ε, 0))` lies in the negative chamber of the event. -/
theorem curve_mem_sideChamber_neg (t : E.Parameter) (ht : t.val < 0) :
    E.curve t ∈ E.sideChamber false :=
  E.sideRange_subset_sideChamber false (E.range_sideCurve_false ▸ ⟨t, ht, rfl⟩)

/-- "Its zero set is $Z=\{g\in\mathcal G:\ g(P(0))=0$ and $g$ is relevant at $P(t)$ for some
$t\neq0\}$" (d1_setup.tex:1076–1079). -/
def zeroSet : Set (Member n) :=
  {m | m.eval E.center = 0 ∧ ∃ t : E.Parameter, t.val ≠ 0 ∧ m.Relevant (E.curve t)}

theorem mem_zeroSet (m : Member n) :
    m ∈ E.zeroSet ↔ m.eval E.center = 0 ∧ ∃ t : E.Parameter, t.val ≠ 0 ∧ m.Relevant (E.curve t) :=
  Iff.rfl

/-- "changes sign at $t = 0$": the germ form of `SM.WallGerm.SignChanges` — on some `(0, δ)`
the values at `t` and `−t` have opposite signs. -/
def SignChanges (φ : LabelledTuple n → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ∀ t : E.SideParameter, t.val < δ →
    φ (E.sideCurve true t) * φ (E.sideCurve false t) < 0

theorem signChanges_iff_real (φ : LabelledTuple n → ℝ) :
    E.SignChanges φ ↔ ∃ δ : ℝ, 0 < δ ∧ ∃ hδr : δ ≤ E.radius,
      ∀ t : ℝ, ∀ ht : 0 < t, ∀ htd : t < δ,
      φ (E.curve ⟨t, by constructor <;> linarith [E.radius_pos]⟩) *
        φ (E.curve ⟨-t, by constructor <;> linarith [E.radius_pos]⟩) < 0 := by
  constructor
  · rintro ⟨δ, hδ, hδr, h⟩
    refine ⟨δ, hδ, hδr, ?_⟩
    intro t ht htd
    exact h ⟨t, ht, lt_of_lt_of_le htd hδr⟩ htd
  · rintro ⟨δ, hδ, hδr, h⟩
    exact ⟨δ, hδ, hδr, fun t ht => h t.val t.property.1 ht⟩

/-- "The event is transversal if every member of $Z$ changes sign at $t=0$"
(d1_setup.tex:1086). -/
def Transversal : Prop := ∀ m ∈ E.zeroSet, E.SignChanges m.eval

/-- The mechanism of the printed tangency remark (d1_setup.tex:1092–1098): a path with
`P(t) = P(−t)` changes the sign of no function, so it is transversal only if `Z = ∅`. -/
theorem even_not_signChanges (heven : ∀ t : E.SideParameter, E.sideCurve true t = E.sideCurve false t)
    (φ : LabelledTuple n → ℝ) : ¬ E.SignChanges φ := by
  rintro ⟨δ, hδ, hδr, h⟩
  have ht := h ⟨δ / 2, by constructor <;> linarith⟩ (by simp only; linarith)
  rw [heven] at ht
  exact absurd ht (not_lt.mpr (mul_self_nonneg _))

/-- "its two punctured sides are the same chamber" for an even path. -/
theorem even_sideChamber_eq
    (heven : ∀ t : E.SideParameter, E.sideCurve true t = E.sideCurve false t) :
    E.sideChamber true = E.sideChamber false := by
  simp only [sideChamber, heven]

/-- The exact bridge from a neighbourhood of `0` in the parameter interval to one positive
radius (as `SM.WallGerm.eventually_center_iff_radius`). -/
theorem eventually_center_iff_radius (A : E.Parameter → Prop) :
    (∀ᶠ t in 𝓝 E.zeroParameter, A t) ↔
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ∀ t : E.Parameter, |t.val| < δ → A t := by
  constructor
  · intro h
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp h
    refine ⟨min δ E.radius, lt_min hδ E.radius_pos, min_le_right _ _, ?_⟩
    intro t ht
    apply hball
    change dist t E.zeroParameter < δ
    change dist t.val (0 : ℝ) < δ
    rw [Real.dist_eq, sub_zero]
    exact lt_of_lt_of_le ht (min_le_left _ _)
  · rintro ⟨δ, hδ, _, h⟩
    apply Filter.mem_of_superset (Metric.ball_mem_nhds E.zeroParameter hδ)
    intro t ht
    apply h t
    change dist t.val (0 : ℝ) < δ at ht
    simpa only [Real.dist_eq, sub_zero] using ht

end Event

/-! ## The tangency example of def:event (d1_setup.tex:1088–1096)

Printed text: "Without that requirement the definition admits a tangency: the path
$p_1=(0,0),\ p_2(t)=(2,-t^2),\ p_3=(1,0),\ p_4=(3,2)$ is generic for $t\neq0$ and has exactly the
cusp zero bundle at $t=0$, yet $P(t)=P(-t)$, so its two punctured sides are the same chamber and no
crossing is created."

Indices are read from `0` (as for `CV.collinearExample`): the moving vertex is `p_1(t) = (2, −t²)`.
Edge directions: `d_0 = (2, −t²)`, `d_1 = (−1, t²)`, `d_2 = (2, 2)`, `d_3 = (−3, −2)`. The values of the
guarded members along the path are computed below (`tangencyPath_G1_*`, `tangencyPath_G2_*`,
`tangencyPath_G5_*`): the turns are `3t² + 4, t², −2t² − 2, 2` and the eight (G2) members are
`t², 3t² + 4, −2t² − 2, t², 2, −2t² − 2, 3t² + 4, 2`. No pair of remote edges is ever active
(`tangencyPath_not_crosses`: one of the two four-sign products is `t²(3t² + 4) ≥ 0` or
`2(3t² + 4) > 0`), and for `n = 4` there are no (G3) or (G4) members at all (`no_remote_triple4`,
`no_g4_index4`), so genericity off `t = 0` is the nonvanishing of the four turns and eight (G2)
members, and the zero set is exactly `{G1_1, G2_{0,2}, G2_{1,0}}`: the turn at the moving vertex
`p_1(0) = (2, 0)` (a kink, `p_0, p_1, p_2` collinear with `p_1` outside `[p_0, p_2]`) and the two (G2)
members that put `p_2 = (1, 0)` on the line of `e_0` and `p_0 = (0, 0)` on the line of `e_1` — the
three members vanishing at a cusp; the printed text calls this "the cusp zero bundle", a name this
library does not define. -/

section TangencyExample

/-! Index arithmetic in `ZMod 4`. -/

theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide

theorem zmod4_two_add_one : (2 : ZMod 4) + 1 = 3 := by decide
theorem zmod4_three_add_one : (3 : ZMod 4) + 1 = 0 := by decide
theorem zmod4_zero_sub_one : (0 : ZMod 4) - 1 = 3 := by decide
theorem zmod4_two_sub_one : (2 : ZMod 4) - 1 = 1 := by decide
theorem zmod4_three_sub_one : (3 : ZMod 4) - 1 = 2 := by decide

/-- The remote pairs of edges of a `4`-gon are `{e_0, e_2}` and `{e_1, e_3}`. -/
theorem remote4_iff (e f : ZMod 4) :
    remote e f ↔ (e = 0 ∧ f = 2) ∨ (e = 2 ∧ f = 0) ∨ (e = 1 ∧ f = 3) ∨ (e = 3 ∧ f = 1) := by
  revert e f; unfold remote adjacent; decide

/-- No three edges of a `4`-gon are pairwise remote: there are no (G3) members for `n = 4`. -/
theorem no_remote_triple4 (e f g : ZMod 4) : ¬ (remote e f ∧ remote f g ∧ remote e g) := by
  revert e f g; unfold remote adjacent; decide

/-- No edge of a `4`-gon has two distinct remote edges: there are no (G4) members for `n = 4`. -/
theorem no_g4_index4 (e f g : ZMod 4) : ¬ (remote e f ∧ remote e g ∧ f ≠ g) := by
  revert e f g; unfold remote adjacent; decide

theorem g2_zero_two_index : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ≠ 0 + 1 := by decide
theorem g2_one_zero_index : (0 : ZMod 4) ≠ 1 ∧ (0 : ZMod 4) ≠ 1 + 1 := by decide

/-- The printed path `p₁ = (0,0), p₂(t) = (2,−t²), p₃ = (1,0), p₄ = (3,2)` (d1_setup.tex:1088–1090),
indices read from `0`. -/
def tangencyPath (t : ℝ) : LabelledTuple 4 :=
  (![((0 : ℝ), (0 : ℝ)), (2, -t ^ 2), (1, 0), (3, 2)] : Fin 4 → Plane)

@[simp] theorem tangencyPath_zero (t : ℝ) : tangencyPath t 0 = (0, 0) := rfl
@[simp] theorem tangencyPath_one (t : ℝ) : tangencyPath t 1 = (2, -t ^ 2) := rfl
@[simp] theorem tangencyPath_two (t : ℝ) : tangencyPath t 2 = (1, 0) := rfl
@[simp] theorem tangencyPath_three (t : ℝ) : tangencyPath t 3 = (3, 2) := rfl

/-- "$P(t) = P(-t)$". -/
theorem tangencyPath_even (t : ℝ) : tangencyPath (-t) = tangencyPath t := by
  unfold tangencyPath
  rw [neg_sq]

theorem tangencyPath_continuous : Continuous tangencyPath := by
  refine continuous_pi fun i => ?_
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · simp only [tangencyPath_zero]; exact continuous_const
  · simp only [tangencyPath_one]; fun_prop
  · simp only [tangencyPath_two]; exact continuous_const
  · simp only [tangencyPath_three]; exact continuous_const

/-! The four edge directions. -/

theorem tangencyPath_edge_zero (t : ℝ) : edge (tangencyPath t) 0 = (2, -t ^ 2) := by
  rw [edge, zero_add, tangencyPath_one, tangencyPath_zero]; ext <;> norm_num

theorem tangencyPath_edge_one (t : ℝ) : edge (tangencyPath t) 1 = (-1, t ^ 2) := by
  rw [edge, one_add_one_eq_two, tangencyPath_two, tangencyPath_one]; ext <;> norm_num

theorem tangencyPath_edge_two (t : ℝ) : edge (tangencyPath t) 2 = (2, 2) := by
  rw [edge, zmod4_two_add_one, tangencyPath_three, tangencyPath_two]; ext <;> norm_num

theorem tangencyPath_edge_three (t : ℝ) : edge (tangencyPath t) 3 = (-3, -2) := by
  rw [edge, zmod4_three_add_one, tangencyPath_zero, tangencyPath_three]; ext <;> norm_num

/-- Every `P(t)` is a polygon (nonzero edges). -/
theorem tangencyPath_isPolygon (t : ℝ) : IsPolygon (tangencyPath t) := by
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [tangencyPath_edge_zero]; intro h; have := congrArg Prod.fst h; norm_num at this
  · rw [tangencyPath_edge_one]; intro h; have := congrArg Prod.fst h; norm_num at this
  · rw [tangencyPath_edge_two]; intro h; have := congrArg Prod.fst h; norm_num at this
  · rw [tangencyPath_edge_three]; intro h; have := congrArg Prod.fst h; norm_num at this

/-! The four turns (G1). -/

theorem tangencyPath_G1_zero (t : ℝ) : G1 (tangencyPath t) 0 = 3 * t ^ 2 + 4 := by
  rw [G1, zmod4_zero_sub_one, tangencyPath_edge_three, tangencyPath_edge_zero]
  simp only [det]; ring

theorem tangencyPath_G1_one (t : ℝ) : G1 (tangencyPath t) 1 = t ^ 2 := by
  rw [G1, sub_self, tangencyPath_edge_zero, tangencyPath_edge_one]
  simp only [det]; ring

theorem tangencyPath_G1_two (t : ℝ) : G1 (tangencyPath t) 2 = -2 * t ^ 2 - 2 := by
  rw [G1, zmod4_two_sub_one, tangencyPath_edge_one, tangencyPath_edge_two]
  simp only [det]; ring

theorem tangencyPath_G1_three (t : ℝ) : G1 (tangencyPath t) 3 = 2 := by
  rw [G1, zmod4_three_sub_one, tangencyPath_edge_two, tangencyPath_edge_three]
  simp only [det]; ring

/-! The eight (G2) members `G2_{e,i}`, `i ∉ {e, e+1}`. -/

theorem tangencyPath_G2_zero_two (t : ℝ) : G2 (tangencyPath t) 0 2 = t ^ 2 := by
  rw [G2, lineForm, tangencyPath_edge_zero, tangencyPath_two, tangencyPath_zero]
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem tangencyPath_G2_zero_three (t : ℝ) : G2 (tangencyPath t) 0 3 = 3 * t ^ 2 + 4 := by
  rw [G2, lineForm, tangencyPath_edge_zero, tangencyPath_three, tangencyPath_zero]
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem tangencyPath_G2_one_three (t : ℝ) : G2 (tangencyPath t) 1 3 = -2 * t ^ 2 - 2 := by
  rw [G2, lineForm, tangencyPath_edge_one, tangencyPath_three, tangencyPath_one]
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem tangencyPath_G2_one_zero (t : ℝ) : G2 (tangencyPath t) 1 0 = t ^ 2 := by
  rw [G2, lineForm, tangencyPath_edge_one, tangencyPath_zero, tangencyPath_one]
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem tangencyPath_G2_two_zero (t : ℝ) : G2 (tangencyPath t) 2 0 = 2 := by
  rw [G2, lineForm, tangencyPath_edge_two, tangencyPath_zero, tangencyPath_two]
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem tangencyPath_G2_two_one (t : ℝ) : G2 (tangencyPath t) 2 1 = -2 * t ^ 2 - 2 := by
  rw [G2, lineForm, tangencyPath_edge_two, tangencyPath_one, tangencyPath_two]
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem tangencyPath_G2_three_one (t : ℝ) : G2 (tangencyPath t) 3 1 = 3 * t ^ 2 + 4 := by
  rw [G2, lineForm, tangencyPath_edge_three, tangencyPath_one, tangencyPath_three]
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem tangencyPath_G2_three_two (t : ℝ) : G2 (tangencyPath t) 3 2 = 2 := by
  rw [G2, lineForm, tangencyPath_edge_three, tangencyPath_two, tangencyPath_three]
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-! The two (G5) members (`e_2, e_0` and `e_1, e_3`, in representative order); never active. -/

theorem tangencyPath_G5_two_zero (t : ℝ) : G5 (tangencyPath t) 2 0 = -2 * t ^ 2 - 4 := by
  rw [G5, tangencyPath_edge_two, tangencyPath_edge_zero]
  simp only [det]; ring

theorem tangencyPath_G5_one_three (t : ℝ) : G5 (tangencyPath t) 1 3 = 3 * t ^ 2 + 2 := by
  rw [G5, tangencyPath_edge_one, tangencyPath_edge_three]
  simp only [det]; ring

/-- "no crossing is created": no two remote edges are active at any `t` — for `{e_0, e_2}` the
product `G2_{0,2} G2_{0,3} = t²(3t² + 4)` is never negative, for `{e_1, e_3}` the product
`G2_{3,1} G2_{3,2} = 2(3t² + 4)` is positive. -/
theorem tangencyPath_not_crosses (t : ℝ) (e f : ZMod 4) : ¬ Crosses (tangencyPath t) e f := by
  rintro ⟨hr, h1, h2⟩
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  rcases (remote4_iff e f).mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [zmod4_two_add_one, tangencyPath_G2_zero_two, tangencyPath_G2_zero_three] at h1
    nlinarith
  · rw [zmod4_two_add_one, tangencyPath_G2_zero_two, tangencyPath_G2_zero_three] at h2
    nlinarith
  · rw [one_add_one_eq_two, tangencyPath_G2_three_one, tangencyPath_G2_three_two] at h2
    nlinarith
  · rw [one_add_one_eq_two, tangencyPath_G2_three_one, tangencyPath_G2_three_two] at h1
    nlinarith

theorem tangencyPath_G1_ne_zero {t : ℝ} (ht : t ≠ 0) (i : ZMod 4) : G1 (tangencyPath t) i ≠ 0 := by
  have h2 : 0 < t ^ 2 := by positivity
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [tangencyPath_G1_zero]; positivity
  · rw [tangencyPath_G1_one]; exact h2.ne'
  · rw [tangencyPath_G1_two]; exact ne_of_lt (by linarith)
  · rw [tangencyPath_G1_three]; norm_num

theorem tangencyPath_G2_ne_zero {t : ℝ} (ht : t ≠ 0) (e i : ZMod 4) (h : i ≠ e ∧ i ≠ e + 1) :
    G2 (tangencyPath t) e i ≠ 0 := by
  have h2 : 0 < t ^ 2 := by positivity
  rcases zmod4_cases e with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd (by decide) h.1
    | exact absurd (by decide) h.2
    | (simp only [tangencyPath_G2_zero_two, tangencyPath_G2_zero_three, tangencyPath_G2_one_three,
          tangencyPath_G2_one_zero, tangencyPath_G2_two_zero, tangencyPath_G2_two_one,
          tangencyPath_G2_three_one, tangencyPath_G2_three_two]
       first
       | exact h2.ne'
       | positivity
       | exact ne_of_lt (by linarith))

/-- "is generic for $t \neq 0$" (CV def:generic), for every real `t ≠ 0`. -/
theorem tangencyPath_generic {t : ℝ} (ht : t ≠ 0) : Generic (tangencyPath t) := by
  refine ⟨tangencyPath_isPolygon t, fun m hm => ?_⟩
  cases m with
  | g1 i => exact tangencyPath_G1_ne_zero ht i
  | g2 e i h => exact tangencyPath_G2_ne_zero ht e i h
  | g5 e f h =>
    exact absurd ((Member.relevant_g5_iff _ e f h).mp hm) (tangencyPath_not_crosses t e f)
  | g3 e f g h => exact absurd ⟨h.1, h.2.1, h.2.2.1⟩ (no_remote_triple4 e f g)
  | g4 e f g h => exact absurd ⟨h.1, h.2.1, h.2.2.1⟩ (no_g4_index4 e f g)

/-- `P(0)` is not generic: the turn `G1_1` at the moving vertex vanishes. -/
theorem tangencyPath_zero_not_generic : ¬ Generic (tangencyPath 0) := by
  intro hG
  apply hG.g1 1
  rw [tangencyPath_G1_one, zero_pow two_ne_zero]

/-- Off the centre the actual crossing set (SM def:crossings) is empty. -/
theorem tangencyPath_crossingSet_eq_empty {t : ℝ} (ht : t ≠ 0) :
    crossingSet (tangencyPath t) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨i, j, rfl, hr, hmeet⟩ := (mem_crossingSet _ s).mp hs
  exact tangencyPath_not_crosses t i j
    (((tangencyPath_generic ht).crosses_iff i j).mpr ⟨i, j, rfl, hr, hmeet⟩)

/-- At the centre the closed segments `e_0 = [(0,0),(2,0)]` and `e_2 = [(1,0),(3,2)]` do meet, at the
vertex `p_2 = (1,0) ∈ e_0`: SM's closed-segment `IsCrossing` holds there although CV's activation
`Crosses` does not (`tangencyPath_not_crosses 0`). This is why `crossingSet = ∅` is stated off the
centre. -/
theorem tangencyPath_zero_isCrossing : IsCrossing (tangencyPath 0) {0, 2} :=
  ⟨0, 2, rfl, (remote4_iff 0 2).mpr (Or.inl ⟨rfl, rfl⟩), (1, 0),
    ⟨1 / 2, by norm_num, by norm_num, by
      rw [edgePoint, tangencyPath_edge_zero, tangencyPath_zero]; ext <;> norm_num⟩,
    ⟨0, le_rfl, zero_le_one, by rw [edgePoint_zero, tangencyPath_two]⟩⟩

/-- The printed tangency (d1_setup.tex:1088–1096) as a CV event on `(−1, 1)`. -/
noncomputable def tangencyExample : Event 4 where
  radius := 1
  radius_pos := one_pos
  curve := fun t => tangencyPath t.val
  continuous_curve := tangencyPath_continuous.comp continuous_subtype_val
  center_polygon := tangencyPath_isPolygon 0
  generic_punctured := fun _ ht => tangencyPath_generic ht
  nongeneric_center := tangencyPath_zero_not_generic

theorem tangencyExample_radius : tangencyExample.radius = 1 := rfl

theorem tangencyExample_curve (t : tangencyExample.Parameter) :
    tangencyExample.curve t = tangencyPath t.val := rfl

theorem tangencyExample_center : tangencyExample.center = tangencyPath 0 := rfl

theorem tangencyExample_sideCurve_true (s : tangencyExample.SideParameter) :
    tangencyExample.sideCurve true s = tangencyPath s.val := rfl

theorem tangencyExample_sideCurve_false (s : tangencyExample.SideParameter) :
    tangencyExample.sideCurve false s = tangencyPath (-s.val) := rfl

/-- "$P(t) = P(-t)$" on the two punctured sides. -/
theorem tangencyExample_even (s : tangencyExample.SideParameter) :
    tangencyExample.sideCurve true s = tangencyExample.sideCurve false s := by
  rw [tangencyExample_sideCurve_true, tangencyExample_sideCurve_false, tangencyPath_even]

/-- "so its two punctured sides are the same chamber". -/
theorem tangencyExample_sideChamber_eq :
    tangencyExample.sideChamber true = tangencyExample.sideChamber false :=
  tangencyExample.even_sideChamber_eq tangencyExample_even

/-- No function changes sign at `t = 0` along the tangency. -/
theorem tangencyExample_not_signChanges (φ : LabelledTuple 4 → ℝ) :
    ¬ tangencyExample.SignChanges φ :=
  tangencyExample.even_not_signChanges tangencyExample_even φ

/-- The parameter `t = 1/2` of the tangency event, a point off the centre. -/
noncomputable def tangencyHalf : tangencyExample.Parameter :=
  ⟨1 / 2, by constructor <;> norm_num [tangencyExample_radius]⟩

theorem tangencyHalf_ne_zero : tangencyHalf.val ≠ 0 := by
  show (1 / 2 : ℝ) ≠ 0
  norm_num

/-- "has exactly the cusp zero bundle at $t = 0$": the zero set of the tangency is the three-member
set `{G1_1, G2_{0,2}, G2_{1,0}}` — the turn at the moving vertex and the two (G2) members placing
`p_2` on the line of `e_0` and `p_0` on the line of `e_1`. The (G5) members are never relevant (no
crossing), and there are no (G3)/(G4) members for `n = 4`. -/
theorem tangencyExample_zeroSet :
    tangencyExample.zeroSet =
      {Member.g1 1, Member.g2 0 2 g2_zero_two_index, Member.g2 1 0 g2_one_zero_index} := by
  ext m
  rw [Event.mem_zeroSet, tangencyExample_center]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, t, _, hrel⟩
    cases m with
    | g1 i =>
      rw [Member.eval_g1] at hz
      rcases zmod4_cases i with rfl | rfl | rfl | rfl
      · rw [tangencyPath_G1_zero] at hz; norm_num at hz
      · exact Or.inl rfl
      · rw [tangencyPath_G1_two] at hz; norm_num at hz
      · rw [tangencyPath_G1_three] at hz; norm_num at hz
    | g2 e i h =>
      rw [Member.eval_g2] at hz
      rcases zmod4_cases e with rfl | rfl | rfl | rfl <;>
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        first
        | exact absurd (by decide) h.1
        | exact absurd (by decide) h.2
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr rfl)
        | (simp only [tangencyPath_G2_zero_three, tangencyPath_G2_one_three,
              tangencyPath_G2_two_zero, tangencyPath_G2_two_one, tangencyPath_G2_three_one,
              tangencyPath_G2_three_two] at hz
           norm_num at hz)
    | g5 e f h =>
      exact absurd ((Member.relevant_g5_iff _ e f h).mp hrel) (tangencyPath_not_crosses _ e f)
    | g3 e f g h => exact absurd ⟨h.1, h.2.1, h.2.2.1⟩ (no_remote_triple4 e f g)
    | g4 e f g h => exact absurd ⟨h.1, h.2.1, h.2.2.1⟩ (no_g4_index4 e f g)
  · rintro (rfl | rfl | rfl)
    · refine ⟨?_, tangencyHalf, tangencyHalf_ne_zero, Member.relevant_g1 _ _⟩
      rw [Member.eval_g1, tangencyPath_G1_one]; norm_num
    · refine ⟨?_, tangencyHalf, tangencyHalf_ne_zero, Member.relevant_g2 _ _ _ _⟩
      rw [Member.eval_g2, tangencyPath_G2_zero_two]; norm_num
    · refine ⟨?_, tangencyHalf, tangencyHalf_ne_zero, Member.relevant_g2 _ _ _ _⟩
      rw [Member.eval_g2, tangencyPath_G2_one_zero]; norm_num

theorem g1_one_mem_tangencyZeroSet : Member.g1 1 ∈ tangencyExample.zeroSet := by
  rw [tangencyExample_zeroSet]
  simp

/-- The tangency is not transversal: `G1_1 ∈ Z` changes no sign. -/
theorem tangencyExample_not_transversal : ¬ tangencyExample.Transversal := fun hT =>
  tangencyExample_not_signChanges _ (hT _ g1_one_mem_tangencyZeroSet)

/-- The printed tangency example of def:event (d1_setup.tex:1088–1096), clause by clause, for
`tangencyExample : Event 4`. -/
structure EventExampleData : Prop where
  /-- "the path $p_1=(0,0),\ p_2(t)=(2,-t^2),\ p_3=(1,0),\ p_4=(3,2)$", indices read from `0`: the
  curve of the event on `(−1, 1)` is that tuple. -/
  curve_eq : ∀ t : tangencyExample.Parameter, tangencyExample.curve t = tangencyPath t.val ∧
    tangencyPath t.val = (![((0 : ℝ), (0 : ℝ)), (2, -t.val ^ 2), (1, 0), (3, 2)] : Fin 4 → Plane)
  radius : tangencyExample.radius = 1
  /-- "is generic for $t\neq0$": for every real `t ≠ 0` (this is the event's `generic_punctured`
  field on the punctured interval). -/
  generic_punctured : (∀ t : ℝ, t ≠ 0 → Generic (tangencyPath t)) ∧
    ∀ t : tangencyExample.Parameter, t.val ≠ 0 → Generic (tangencyExample.curve t)
  /-- "and $P(0)$ is not": the turn `G1_1` at the moving vertex vanishes. -/
  nongeneric_center : ¬ Generic tangencyExample.center ∧ G1 tangencyExample.center 1 = 0
  /-- "has exactly the cusp zero bundle at $t=0$": `Z = {G1_1, G2_{0,2}, G2_{1,0}}`. -/
  zeroSet_eq : tangencyExample.zeroSet =
    {Member.g1 1, Member.g2 0 2 g2_zero_two_index, Member.g2 1 0 g2_one_zero_index}
  /-- "$P(t)=P(-t)$", on the path and on the two punctured sides of the event. -/
  even : (∀ t : ℝ, tangencyPath (-t) = tangencyPath t) ∧
    ∀ s : tangencyExample.SideParameter,
      tangencyExample.sideCurve true s = tangencyExample.sideCurve false s
  /-- "so its two punctured sides are the same chamber". -/
  sideChamber_eq : tangencyExample.sideChamber true = tangencyExample.sideChamber false
  /-- No function — in particular no member of `𝓖` — changes sign at `t = 0`. -/
  not_signChanges : (∀ φ : LabelledTuple 4 → ℝ, ¬ tangencyExample.SignChanges φ) ∧
    ∀ m : Member 4, ¬ tangencyExample.SignChanges m.eval
  /-- Hence the tangency is not transversal ("Every named event … is required to be transversal.
  Without that requirement the definition admits a tangency"). -/
  not_transversal : ¬ tangencyExample.Transversal
  /-- "no crossing is created": no two remote edges are ever active (CV's activation `Crosses`),
  and off the centre the actual crossing set (SM def:crossings) is empty. -/
  no_crossing : (∀ (t : ℝ) (e f : ZMod 4), ¬ Crosses (tangencyPath t) e f) ∧
    ∀ t : ℝ, t ≠ 0 → crossingSet (tangencyPath t) = ∅

/-- The printed tangency example, proved. -/
theorem event_example : EventExampleData where
  curve_eq := fun _ => ⟨rfl, rfl⟩
  radius := rfl
  generic_punctured := ⟨fun _ ht => tangencyPath_generic ht, fun _ ht => tangencyPath_generic ht⟩
  nongeneric_center := ⟨tangencyPath_zero_not_generic, by
    rw [tangencyExample_center, tangencyPath_G1_one]; norm_num⟩
  zeroSet_eq := tangencyExample_zeroSet
  even := ⟨tangencyPath_even, tangencyExample_even⟩
  sideChamber_eq := tangencyExample_sideChamber_eq
  not_signChanges := ⟨tangencyExample_not_signChanges,
    fun m => tangencyExample_not_signChanges m.eval⟩
  not_transversal := tangencyExample_not_transversal
  no_crossing := ⟨tangencyPath_not_crosses, fun _ ht => tangencyPath_crossingSet_eq_empty ht⟩

end TangencyExample

/-- CV:def:event (d1_setup.tex:1072–1097), clause by clause. -/
structure EventData (E : Event n) : Prop where
  /-- "$t\in(-\varepsilon,\varepsilon)$" with `ε > 0`, and "a continuous path". -/
  radius_pos : 0 < E.radius
  continuous : Continuous E.curve
  /-- "of polygons on $n$ vertices" (CV def:polygon: nonzero edges), for every `t`. -/
  polygon : ∀ t : E.Parameter, IsPolygon (E.curve t)
  /-- `P(0)` is the value at the parameter `0`. -/
  center_eq : E.center = E.curve E.zeroParameter ∧ E.zeroParameter.val = 0
  /-- "$P(t)$ is generic for every $t\neq0$". -/
  generic_punctured : ∀ t : E.Parameter, t.val ≠ 0 → Generic (E.curve t)
  /-- "and $P(0)$ is not". -/
  nongeneric_center : ¬ Generic E.center
  /-- "$Z=\{g\in\mathcal G:\ g(P(0))=0$ and $g$ is relevant at $P(t)$ for some $t\neq0\}$". -/
  mem_zeroSet : ∀ m : Member n,
    m ∈ E.zeroSet ↔ m.eval E.center = 0 ∧ ∃ t : E.Parameter, t.val ≠ 0 ∧ m.Relevant (E.curve t)
  /-- The two punctured sides are `P((0, ε))` and `P((−ε, 0))`. -/
  positive_side : Set.range (E.sideCurve true) = E.curve '' {t : E.Parameter | 0 < t.val}
  negative_side : Set.range (E.sideCurve false) = E.curve '' {t : E.Parameter | t.val < 0}
  /-- "each of those two sets is connected and consists of generic polygons". -/
  side_connected : ∀ b : Bool, IsConnected (Set.range (E.sideCurve b))
  side_generic : ∀ b : Bool, Set.range (E.sideCurve b) ⊆ {Q | Generic Q}
  /-- "so each does lie in one chamber": the chamber of the side is a CV chamber (a connected
  component of the labelled CV-generic locus) containing the whole side, independent of the
  representative point. -/
  side_chamber : ∀ b : Bool, (∀ t, E.sideCurve b t ∈ E.sideChamber b) ∧
    (∀ t, E.sideChamber b = connectedComponentIn {Q | Generic Q} (E.sideCurve b t)) ∧
    E.sideChamber b ⊆ {Q | Generic Q}
  /-- "the chambers containing $P((-\varepsilon,0))$ and $P((0,\varepsilon))$". -/
  curve_mem_sideChamber : ∀ t : E.Parameter,
    (0 < t.val → E.curve t ∈ E.sideChamber true) ∧ (t.val < 0 → E.curve t ∈ E.sideChamber false)
  /-- "changes sign at $t=0$": on some `(0, δ)`, `g(P(t))·g(P(−t)) < 0`. -/
  signChanges_iff : ∀ φ : LabelledTuple n → ℝ, E.SignChanges φ ↔
    ∃ δ : ℝ, 0 < δ ∧ ∃ hδr : δ ≤ E.radius, ∀ t : ℝ, ∀ ht : 0 < t, ∀ htd : t < δ,
      φ (E.curve ⟨t, by constructor <;> linarith [E.radius_pos]⟩) *
        φ (E.curve ⟨-t, by constructor <;> linarith [E.radius_pos]⟩) < 0
  /-- "The event is transversal if every member of $Z$ changes sign at $t=0$". -/
  transversal_iff : E.Transversal ↔ ∀ m ∈ E.zeroSet, E.SignChanges m.eval
  /-- The printed tangency example (d1_setup.tex:1088–1096), `tangencyExample : Event 4`, clause by
  clause (`EventExampleData`). -/
  tangency_example : EventExampleData

/-- Row 148, CV:def:event. -/
theorem event_definition (E : Event n) : EventData E where
  radius_pos := E.radius_pos
  continuous := E.continuous_curve
  polygon := E.polygon
  center_eq := ⟨rfl, rfl⟩
  generic_punctured := E.generic_punctured
  nongeneric_center := E.nongeneric_center
  mem_zeroSet := E.mem_zeroSet
  positive_side := E.range_sideCurve_true
  negative_side := E.range_sideCurve_false
  side_connected := E.sideRange_connected
  side_generic := E.sideRange_subset_generic
  side_chamber := fun b => ⟨E.sideCurve_mem_sideChamber b, E.sideChamber_eq_at b,
    E.sideChamber_subset_generic b⟩
  curve_mem_sideChamber := fun t => ⟨E.curve_mem_sideChamber_pos t, E.curve_mem_sideChamber_neg t⟩
  signChanges_iff := E.signChanges_iff_real
  transversal_iff := Iff.rfl
  tangency_example := event_example

/-! ## Row 149 — CV:lem:guardconst (d1_setup.tex:1107–1121)

Printed text: "Let $t\mapsto P(t)$, $t\in(-\varepsilon,\varepsilon)$, be an event with zero set
$Z$, and let $g\in\mathcal G$ be relevant at $P(t)$ for some $t\neq0$ and not a member of $Z$.
Then $g(P(0))\neq0$, and there is $\varepsilon'\in(0,\varepsilon]$ such that $g$ is nonzero and
of constant sign on the whole of $(-\varepsilon',\varepsilon')$." -/

/-- Row 149, CV:lem:guardconst. The constant sign is the (nonzero) sign at the centre. -/
theorem guardconst (E : Event n) (m : Member n)
    (hrel : ∃ t : E.Parameter, t.val ≠ 0 ∧ m.Relevant (E.curve t)) (hZ : m ∉ E.zeroSet) :
    m.eval E.center ≠ 0 ∧
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ E.radius ∧ ∀ t : E.Parameter, |t.val| < ε' →
      m.eval (E.curve t) ≠ 0 ∧
      SignType.sign (m.eval (E.curve t)) = SignType.sign (m.eval E.center) := by
  have h0 : m.eval E.center ≠ 0 := fun h => hZ ⟨h, hrel⟩
  refine ⟨h0, ?_⟩
  have hc : Continuous fun t : E.Parameter => m.eval (E.curve t) :=
    m.continuous_eval.comp E.continuous_curve
  have hev : ∀ᶠ t in 𝓝 E.zeroParameter, m.eval (E.curve t) ≠ 0 ∧
      SignType.sign (m.eval (E.curve t)) = SignType.sign (m.eval E.center) := by
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hn : ∀ᶠ t in 𝓝 E.zeroParameter, m.eval (E.curve t) < 0 :=
        hc.continuousAt.eventually (isOpen_Iio.mem_nhds hneg)
      filter_upwards [hn] with t ht
      exact ⟨ht.ne, by rw [sign_neg ht, sign_neg hneg]⟩
    · have hp : ∀ᶠ t in 𝓝 E.zeroParameter, 0 < m.eval (E.curve t) :=
        hc.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
      filter_upwards [hp] with t ht
      exact ⟨ht.ne', by rw [sign_pos ht, sign_pos hpos]⟩
  exact (E.eventually_center_iff_radius _).mp hev

/-! ## Row 150 — CV:def:silent (d1_setup.tex:1265–1271)

Printed text: "An event is silent if every member of its zero set $Z$ is a predicate
$\mathrm{G2}_{e,i}$ whose vanishing at $t=0$ places $p_i$ on the line of $e$ but not on the
segment $e$. In particular no member of $Z$ is a turn (G1), a crossing-order predicate (G4), a
concurrency (G3) or a direction determinant (G5)."

Not part of this row (defined here for the later CV:ax:R rows only): the forced Reidemeister III
bundle of CV ax:R (d10_axioms.tex:18–24), "every event whose zero
set is the forced bundle $Z=\{\mathrm{G3}_{e,f,g},\mathrm{G4}_{e;f,g},\mathrm{G4}_{f;e,g},
\mathrm{G4}_{g;e,f}\}$ for three pairwise remote edges with $1\leq e<f<g\leq n$, concurrent at
$t=0$ at a point interior to all three, the event being transversal". -/

namespace Event

variable (E : Event n)

/-- CV def:silent (d1_setup.tex:1265–1271), the defining clause. -/
def Silent : Prop := ∀ m ∈ E.zeroSet, ∃ e i h, m = Member.g2 e i h ∧
  (∃ t : ℝ, E.center i = edgePoint E.center e t) ∧ E.center i ∉ edgeSegment E.center e

/-- The forced RIII bundle of CV ax:R (d10_axioms.tex:18–24): zero set exactly
`{G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}` with `e < f < g` pairwise remote, concurrent
at `t = 0` at a point interior to all three edges, and transversal. -/
def IsSimpleRIII (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ rep e < rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ rep e < rep f) : Prop :=
  E.zeroSet = {Member.g3 e f g h3, Member.g4 e f g h4e, Member.g4 f e g h4f,
    Member.g4 g e f h4g} ∧
  (∃ x : Plane, x ∈ edgeInterior E.center e ∧ x ∈ edgeInterior E.center f ∧
    x ∈ edgeInterior E.center g) ∧
  E.Transversal

/-- For a member of `Z` of the form `G2_{e,i}`, its vanishing at `P(0)` is automatic and is the
same as `p_i` lying on the line of `e` (the centre is a polygon, so `d_e ≠ 0`). -/
theorem g2_mem_zeroSet_line (e i : ZMod n) (h : i ≠ e ∧ i ≠ e + 1)
    (hm : Member.g2 e i h ∈ E.zeroSet) : ∃ t : ℝ, E.center i = edgePoint E.center e t :=
  (G2_eq_zero_iff E.center e i (E.center_isPolygon e)).mp hm.1

theorem silent_iff_segment : E.Silent ↔ ∀ m ∈ E.zeroSet, ∃ e i h, m = Member.g2 e i h ∧
    E.center i ∉ edgeSegment E.center e := by
  constructor
  · intro hs m hm
    obtain ⟨e, i, h, rfl, _, hseg⟩ := hs m hm
    exact ⟨e, i, h, rfl, hseg⟩
  · intro hs m hm
    obtain ⟨e, i, h, rfl, hseg⟩ := hs m hm
    exact ⟨e, i, h, rfl, E.g2_mem_zeroSet_line e i h hm, hseg⟩

variable {E} in
theorem Silent.no_g1 (hs : E.Silent) : ∀ m ∈ E.zeroSet, ∀ i, m ≠ Member.g1 i := by
  intro m hm i he
  obtain ⟨_, _, _, rfl, _⟩ := hs m hm
  cases he

variable {E} in
theorem Silent.no_g5 (hs : E.Silent) : ∀ m ∈ E.zeroSet, ∀ e f h, m ≠ Member.g5 e f h := by
  intro m hm e f h he
  obtain ⟨_, _, _, rfl, _⟩ := hs m hm
  cases he

variable {E} in
theorem Silent.no_g3 (hs : E.Silent) : ∀ m ∈ E.zeroSet, ∀ e f g h, m ≠ Member.g3 e f g h := by
  intro m hm e f g h he
  obtain ⟨_, _, _, rfl, _⟩ := hs m hm
  cases he

variable {E} in
theorem Silent.no_g4 (hs : E.Silent) : ∀ m ∈ E.zeroSet, ∀ e f g h, m ≠ Member.g4 e f g h := by
  intro m hm e f g h he
  obtain ⟨_, _, _, rfl, _⟩ := hs m hm
  cases he

variable {E} in
/-- A silent event is never a simple RIII event (its zero set holds no G3). -/
theorem Silent.not_isSimpleRIII (hs : E.Silent) (e f g : ZMod n) (h3 h4e h4f h4g) :
    ¬ E.IsSimpleRIII e f g h3 h4e h4f h4g := by
  rintro ⟨hZ, _, _⟩
  have hmem : Member.g3 e f g h3 ∈ E.zeroSet := by
    rw [hZ]
    simp
  exact hs.no_g3 _ hmem e f g h3 rfl

end Event

/-- CV:def:silent (d1_setup.tex:1265–1271), clause by clause. The forced RIII bundle of
d10_axioms.tex:18–24 (`Event.IsSimpleRIII`) is defined in this module for the CV:ax:R rows but is not
part of this definition. -/
structure SilentData (E : Event n) : Prop where
  /-- "every member of its zero set $Z$ is a predicate $\mathrm{G2}_{e,i}$ whose vanishing at
  $t=0$ places $p_i$ on the line of $e$ but not on the segment $e$". -/
  silent_iff : E.Silent ↔ ∀ m ∈ E.zeroSet, ∃ e i h, m = Member.g2 e i h ∧
    (∃ t : ℝ, E.center i = edgePoint E.center e t) ∧ E.center i ∉ edgeSegment E.center e
  /-- The vanishing of `G2_{e,i}` at a polygon is exactly "`p_i` on the line of `e`". -/
  g2_vanishing_iff_line : ∀ (P : LabelledTuple n) (e i : ZMod n), edge P e ≠ 0 →
    (G2 P e i = 0 ↔ ∃ t : ℝ, P i = edgePoint P e t)
  /-- Hence, the centre being a polygon, silence is: every member of `Z` is a `G2_{e,i}` with
  `p_i(0)` off the closed segment `e`. -/
  silent_iff_segment : E.Silent ↔ ∀ m ∈ E.zeroSet, ∃ e i h, m = Member.g2 e i h ∧
    E.center i ∉ edgeSegment E.center e
  /-- "In particular no member of $Z$ is a turn (G1)". -/
  no_turn : E.Silent → ∀ m ∈ E.zeroSet, ∀ i, m ≠ Member.g1 i
  /-- "a crossing-order predicate (G4)". -/
  no_crossing_order : E.Silent → ∀ m ∈ E.zeroSet, ∀ e f g h, m ≠ Member.g4 e f g h
  /-- "a concurrency (G3)". -/
  no_concurrency : E.Silent → ∀ m ∈ E.zeroSet, ∀ e f g h, m ≠ Member.g3 e f g h
  /-- "or a direction determinant (G5)". -/
  no_direction : E.Silent → ∀ m ∈ E.zeroSet, ∀ e f h, m ≠ Member.g5 e f h

/-- Row 150, CV:def:silent. -/
theorem silent_definition (E : Event n) : SilentData E where
  silent_iff := Iff.rfl
  g2_vanishing_iff_line := G2_eq_zero_iff
  silent_iff_segment := E.silent_iff_segment
  no_turn := fun hs => hs.no_g1
  no_crossing_order := fun hs => hs.no_g4
  no_concurrency := fun hs => hs.no_g3
  no_direction := fun hs => hs.no_g5

end Event

end CV

