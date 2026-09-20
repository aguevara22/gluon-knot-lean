import SM.CarrierVisitTwin
import SM.GenericReversal
import SM.RotationReversal
import SM.GenericTopology

/-! Chapter-3 representation layer, module LinkDiagram: polygonal oriented link diagrams (Shadow, Strand, multi-component crossings and visits, Shadow.Generic, Diagram with over-strand data, signs and writhe, switch / restrict / reverse / mirror, based orders and UnderFirst). Implements the design adopted 2026-09-13
(work/reports/design-decision-diagram-record-20260913.md, Proposal #1 with the judges' grafts). Written 2026-09-13 by a Claude Code
implementer subagent of the pod executor (workflow implement-diagram-layer-phase1), checked with `lake env lean` (placeholder-free,
standard axioms) and ported verbatim from work/drafts/LinkDiagram.lean (only this header added and #print lines removed). All
declarations live in `SM.Link`; no row points here yet — the definition rows (def:positive-lift, def:gauss-record, def:adeg, ...)
are stated on top of this layer and reviewed against the source. -/

/-! # Polygonal oriented link diagrams (Chapter 3 representation layer, Proposal #1)

Source: reference/SM/sm-3-statesum.tex, frame SM15.  This file renders the first sentence of
def:positive-lift (325-335), read in the polygonal class fixed by the named-record bridge
paragraph (337-351; 340-341: "A diagram here is a finite polygonal immersion"), together with the
based-order vocabulary of lp:lm (935-960; the UNDER-first sentence is 947-949).  Design: work/reports/design-decision-diagram-record-
20260913.md, section diagram_type, and the judges' grafts.

Printed words rendered here (sm-3:325-335):
"An oriented link diagram in the plane is a finite collection of closed oriented curves with
finitely many transverse double points, no triple points, and at each double point a choice of
the over strand. A double point with over-strand direction u_o and under-strand direction u_u is
positive if det(u_o,u_u)>0 and negative otherwise. ... Its writhe (the sum of crossing signs) is
m_Q."

and (sm-3:935-960, lp:lm): "For every such diagram D ... independently of the auxiliary component
order, nonsingular basepoints, and order of required crossing switches ... has the initialization
F_D = μ^{c-1} for every based ordered c-component UNDER-first diagram. UNDER-first means that,
traversing components in their order, from their basepoints and in their orientations, the first
encounter with each crossing is the underpass. ... Here c ≥ 1."  (sm-3:932-933: "Diagrams are
actual nonempty finite oriented diagrams, including all crossing-free components. Algebraic empty
products are not empty links.")

Reuse of the accepted library (work/lean/SM, read-only): `LabelledTuple`, `Plane`, `det`, `edge`,
`edgePoint`, `edgeSegment`, `edgeInterior`, `adjacent`, `incident`, `remote`, `Regular`,
`reversal`, `TraversalPoint`, `traversalKey`, `traversalEvaluation`, `SM.IsCrossing`,
`SM.Crossing`, `SM.Visit`, `SM.crossingPoint`.

Main declarations (all in `SM.Link`): `PolyComp`, `Shadow` (with `Strand`, `seg`, `interior`,
`dir`, `tail`, `Adjacent`, `IncidentTail`, `IsCrossing`, `Crossing`, `Visit`, `crossingPoint`,
`Generic`, `Pt`, `eval`), `Diagram` (with `underStrand`, `IsPositive`, `sign`, `writhe`,
`switch`, `componentCount`, `IsCrossingFreeCircle`, `restrict`, `reverse`, `mirror`, `Basing`,
`visitPt`, `basedRank`, `UnderFirst`), and the sanity lemmas listed at the end. -/

namespace SM.Link

open SM

noncomputable section

/-! ## One closed oriented polygon (a component) -/

/-- One component of a polygonal link diagram: a closed oriented polygon in the accepted sense
of def:polygon, i.e. a labelled tuple `P : ZMod k → Plane` with `k ≥ 3` vertices, traversed in the
direction of increasing label.  This is the polygonal reading of "closed oriented curves"
(sm-3:326-327) fixed by the bridge paragraph "A diagram here is a finite polygonal immersion"
(sm-3:340-341).  A carrier's corner polygon (`Carrier.ccpCornerPolygon`) is a `PolyComp` with no
coercion. -/
structure PolyComp where
  /-- number of vertices (= number of directed edges) -/
  k : ℕ
  /-- the source's `n ≥ 3` restriction on polygons (def:polygon) -/
  hk : 3 ≤ k
  /-- the vertex tuple; `edge P i = P (i+1) - P i` is the directed edge `E_i` -/
  P : LabelledTuple k

instance PolyComp.instNeZeroK (C : PolyComp) : NeZero C.k := ⟨by have := C.hk; omega⟩

theorem PolyComp.one_lt_k (C : PolyComp) : 1 < C.k := by have := C.hk; omega

instance PolyComp.instNontrivialZMod (C : PolyComp) : Nontrivial (ZMod C.k) :=
  ZMod.nontrivial_iff.mpr (by have := C.hk; omega)

/-! ## Shadows: finite families of closed oriented polygons -/

/-- The *shadow* (underlying finite collection of closed oriented curves, sm-3:326-327) of a
polygonal link diagram: `c ≥ 1` components `comp 0, …, comp (c-1)`, each a `PolyComp`.  The bound
`c ≥ 1` is built into the type following lp:lm "Here c ≥ 1" (sm-3:951) and "Diagrams are actual
nonempty finite oriented diagrams, including all crossing-free components. Algebraic empty
products are not empty links." (sm-3:932-933). -/
structure Shadow where
  /-- number of components -/
  c : ℕ
  /-- "Here c ≥ 1" (sm-3:951) -/
  hc : 0 < c
  /-- the components -/
  comp : Fin c → PolyComp

namespace Shadow

variable (Γ : Shadow)

/-- A *strand* is a directed edge `E_j` of a component `i`: the pair `⟨i, j⟩`. -/
abbrev Strand : Type := Σ i : Fin Γ.c, ZMod (Γ.comp i).k

/-- The closed edge segment of a strand (accepted `edgeSegment`). -/
def seg (s : Γ.Strand) : Set Plane := edgeSegment (Γ.comp s.1).P s.2

/-- The open edge segment of a strand (accepted `edgeInterior`). -/
def interior (s : Γ.Strand) : Set Plane := edgeInterior (Γ.comp s.1).P s.2

/-- The direction vector `u` of a strand: the accepted `edge`, i.e. `P (j+1) - P j`; this is the
"strand direction" of def:positive-lift (sm-3:329) for a polygonal strand. -/
def dir (s : Γ.Strand) : Plane := edge (Γ.comp s.1).P s.2

/-- The tail vertex `P j` of the strand `⟨i, j⟩`. -/
def tail (s : Γ.Strand) : Plane := (Γ.comp s.1).P s.2

/-- The head vertex `P (j+1)` of the strand `⟨i, j⟩`. -/
def head (s : Γ.Strand) : Plane := (Γ.comp s.1).P (s.2 + 1)

theorem seg_mk (i : Fin Γ.c) (a : ZMod (Γ.comp i).k) :
    Γ.seg ⟨i, a⟩ = edgeSegment (Γ.comp i).P a := rfl

theorem interior_mk (i : Fin Γ.c) (a : ZMod (Γ.comp i).k) :
    Γ.interior ⟨i, a⟩ = edgeInterior (Γ.comp i).P a := rfl

theorem dir_mk (i : Fin Γ.c) (a : ZMod (Γ.comp i).k) :
    Γ.dir ⟨i, a⟩ = edge (Γ.comp i).P a := rfl

theorem tail_mk (i : Fin Γ.c) (a : ZMod (Γ.comp i).k) :
    Γ.tail ⟨i, a⟩ = (Γ.comp i).P a := rfl

theorem interior_subset_seg (s : Γ.Strand) : Γ.interior s ⊆ Γ.seg s :=
  edgeInterior_subset_edgeSegment _ _

theorem tail_mem_seg (s : Γ.Strand) : Γ.tail s ∈ Γ.seg s :=
  ⟨0, le_rfl, zero_le_one, by rw [edgePoint_zero]; rfl⟩

theorem head_mem_seg (s : Γ.Strand) : Γ.head s ∈ Γ.seg s :=
  ⟨1, zero_le_one, le_rfl, by rw [edgePoint_one]; rfl⟩

/-- The head of `⟨i, j⟩` is the tail of the next strand `⟨i, j+1⟩`. -/
theorem head_eq_tail_succ (i : Fin Γ.c) (a : ZMod (Γ.comp i).k) :
    Γ.head ⟨i, a⟩ = Γ.tail ⟨i, a + 1⟩ := rfl

/-- Two strands are *adjacent* when they lie on the same component and their edge labels are
adjacent in the accepted sense (`adjacent a b`: `b - a ∈ {-1, 0, 1}`, def:polygon).  Adjacent
strands share a vertex (or coincide) and their meeting there is not a double point. -/
def Adjacent (s t : Γ.Strand) : Prop :=
  ∃ (i : Fin Γ.c) (a b : ZMod (Γ.comp i).k), s = ⟨i, a⟩ ∧ t = ⟨i, b⟩ ∧ adjacent a b

/-- The tail vertex of `s` is an endpoint of the edge `t`: same component and the accepted
`incident` relation between the vertex label of `s` and the edge label of `t`. -/
def IncidentTail (s t : Γ.Strand) : Prop :=
  ∃ (i : Fin Γ.c) (a b : ZMod (Γ.comp i).k), s = ⟨i, a⟩ ∧ t = ⟨i, b⟩ ∧ incident a b

theorem adjacent_mk_iff (i : Fin Γ.c) (a b : ZMod (Γ.comp i).k) :
    Γ.Adjacent ⟨i, a⟩ ⟨i, b⟩ ↔ adjacent a b := by
  constructor
  · rintro ⟨j, a', b', hs, ht, h⟩
    rw [Sigma.mk.inj_iff] at hs ht
    obtain ⟨rfl, ha⟩ := hs
    obtain ⟨-, hb⟩ := ht
    rw [eq_of_heq ha, eq_of_heq hb]
    exact h
  · intro h
    exact ⟨i, a, b, rfl, rfl, h⟩

theorem incidentTail_mk_iff (i : Fin Γ.c) (a b : ZMod (Γ.comp i).k) :
    Γ.IncidentTail ⟨i, a⟩ ⟨i, b⟩ ↔ incident a b := by
  constructor
  · rintro ⟨j, a', b', hs, ht, h⟩
    rw [Sigma.mk.inj_iff] at hs ht
    obtain ⟨rfl, ha⟩ := hs
    obtain ⟨-, hb⟩ := ht
    rw [eq_of_heq ha, eq_of_heq hb]
    exact h
  · intro h
    exact ⟨i, a, b, rfl, rfl, h⟩

theorem Adjacent.fst_eq {s t : Γ.Strand} (h : Γ.Adjacent s t) : s.1 = t.1 := by
  obtain ⟨i, a, b, rfl, rfl, -⟩ := h
  rfl

theorem IncidentTail.fst_eq {s t : Γ.Strand} (h : Γ.IncidentTail s t) : s.1 = t.1 := by
  obtain ⟨i, a, b, rfl, rfl, -⟩ := h
  rfl

theorem adjacent_iff {s t : Γ.Strand} :
    Γ.Adjacent s t ↔ ∃ h : s.1 = t.1, adjacent (h ▸ s.2) t.2 := by
  obtain ⟨i, a⟩ := s
  obtain ⟨j, b⟩ := t
  constructor
  · intro h
    obtain rfl := h.fst_eq
    exact ⟨rfl, (Γ.adjacent_mk_iff i a b).mp h⟩
  · rintro ⟨h, hab⟩
    dsimp only at h
    subst h
    exact (Γ.adjacent_mk_iff i a b).mpr hab

theorem adjacent_of_eq_of_adjacent {i j : Fin Γ.c} (h : i = j) {a : ZMod (Γ.comp i).k}
    {b : ZMod (Γ.comp j).k} (hab : adjacent (h ▸ a) b) : Γ.Adjacent ⟨i, a⟩ ⟨j, b⟩ := by
  subst h
  exact (Γ.adjacent_mk_iff i a b).mpr hab

theorem Adjacent.refl (s : Γ.Strand) : Γ.Adjacent s s :=
  ⟨s.1, s.2, s.2, rfl, rfl, Or.inr (Or.inl (sub_self _))⟩

/-- `adjacent` is symmetric (from the accepted `remote_symm`). -/
theorem _root_.SM.Link.adjacent_symm' {n : ℕ} {a b : ZMod n} (h : adjacent a b) : adjacent b a := by
  by_contra hn
  exact remote_symm hn h

theorem Adjacent.symm {s t : Γ.Strand} (h : Γ.Adjacent s t) : Γ.Adjacent t s := by
  obtain ⟨i, a, b, rfl, rfl, hab⟩ := h
  exact ⟨i, b, a, rfl, rfl, adjacent_symm' hab⟩

theorem adjacent_comm {s t : Γ.Strand} : Γ.Adjacent s t ↔ Γ.Adjacent t s :=
  ⟨Adjacent.symm Γ, Adjacent.symm Γ⟩

theorem ne_of_not_adjacent {s t : Γ.Strand} (h : ¬ Γ.Adjacent s t) : s ≠ t := by
  rintro rfl
  exact h (Adjacent.refl Γ s)

/-- The tail of `s` incident to the edge `t` forces `s` and `t` adjacent. -/
theorem IncidentTail.adjacent {s t : Γ.Strand} (h : Γ.IncidentTail s t) : Γ.Adjacent s t := by
  obtain ⟨i, a, b, rfl, rfl, hab⟩ := h
  refine ⟨i, a, b, rfl, rfl, ?_⟩
  rcases hab with rfl | rfl
  · exact Or.inl (by ring)
  · exact Or.inr (Or.inl (sub_self _))

/-- The head vertex of `⟨i, a⟩` incident to the edge `t` forces `⟨i, a⟩` and `t` adjacent. -/
theorem adjacent_of_incidentTail_succ {i : Fin Γ.c} {a : ZMod (Γ.comp i).k} {t : Γ.Strand}
    (h : Γ.IncidentTail ⟨i, a + 1⟩ t) : Γ.Adjacent ⟨i, a⟩ t := by
  obtain ⟨j, a', b, hs, rfl, hab⟩ := h
  rw [Sigma.mk.inj_iff] at hs
  obtain ⟨rfl, ha⟩ := hs
  have ha' := eq_of_heq ha
  subst ha'
  refine ⟨i, a, b, rfl, rfl, ?_⟩
  rcases hab with rfl | rfl
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inr (Or.inr (by ring))

/-! ### Crossings and visits -/

/-- A *crossing* (double point, sm-3:327) of the shadow: an unordered pair `{s, t}` of
non-adjacent strands (possibly on different components) whose closed edge segments meet.  This is
the multi-component copy of the accepted `SM.IsCrossing`, so self-crossings and crossings between
different components are one notion. -/
def IsCrossing (x : Finset Γ.Strand) : Prop :=
  ∃ s t, x = {s, t} ∧ ¬ Γ.Adjacent s t ∧ (Γ.seg s ∩ Γ.seg t).Nonempty

/-- The crossings of a shadow (the "finitely many transverse double points", sm-3:327).  A `def`
(as the accepted `SM.Crossing`) so that instances are found by unifying the shadow. -/
def Crossing : Type := {x : Finset Γ.Strand // Γ.IsCrossing x}

/-- The crossing *occurrences* `M` (def:gauss-record, sm-3:355-357): a crossing together with one of
its two strands, i.e. one passage of a component through the double point.  Multi-component copy
of the accepted `SM.Visit`. -/
def Visit : Type := Σ x : Γ.Crossing, {s // s ∈ x.val}

instance instDecidableEqCrossing : DecidableEq Γ.Crossing := by
  classical
  exact (inferInstance : DecidableEq {x : Finset Γ.Strand // Γ.IsCrossing x})

instance instFintypeCrossing : Fintype Γ.Crossing := by
  classical
  exact (inferInstance : Fintype {x : Finset Γ.Strand // Γ.IsCrossing x})

instance instDecidableEqVisit : DecidableEq Γ.Visit := by
  classical
  exact (inferInstance : DecidableEq (Σ x : Γ.Crossing, {s // s ∈ x.val}))

instance instFintypeVisit : Fintype Γ.Visit := by
  classical
  exact (inferInstance : Fintype (Σ x : Γ.Crossing, {s // s ∈ x.val}))

theorem isCrossing_pair {s t : Γ.Strand} (hna : ¬ Γ.Adjacent s t)
    (hmeet : (Γ.seg s ∩ Γ.seg t).Nonempty) : Γ.IsCrossing {s, t} :=
  ⟨s, t, rfl, hna, hmeet⟩

theorem IsCrossing.comm {s t : Γ.Strand} (h : Γ.IsCrossing {s, t}) : Γ.IsCrossing {t, s} := by
  classical
  rwa [Finset.pair_comm]

/-- Every crossing is a two-element set (its two strands are distinct because they are not
adjacent). -/
theorem crossing_card_two (x : Γ.Crossing) : x.val.card = 2 := by
  classical
  obtain ⟨s, t, hx, hna, -⟩ := x.2
  rw [hx]
  exact Finset.card_pair (Γ.ne_of_not_adjacent hna)

/-- Any two distinct strands of a crossing are non-adjacent and meet. -/
theorem crossing_pair_spec (x : Γ.Crossing) {s t : Γ.Strand} (hs : s ∈ x.val) (ht : t ∈ x.val)
    (hne : s ≠ t) : ¬ Γ.Adjacent s t ∧ (Γ.seg s ∩ Γ.seg t).Nonempty := by
  classical
  obtain ⟨s₀, t₀, hx, hna, hmeet⟩ := x.2
  rw [hx] at hs ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨hna, hmeet⟩
  · exact ⟨fun h => hna h.symm, by rwa [Set.inter_comm]⟩
  · exact absurd rfl hne

theorem exists_other (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) :
    ∃ t ∈ x.val, t ≠ s := by
  classical
  obtain ⟨s₀, t₀, hx, hna, -⟩ := x.2
  have hne := Γ.ne_of_not_adjacent hna
  rw [hx] at hs ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact ⟨t₀, by simp, hne.symm⟩
  · exact ⟨s₀, by simp, hne⟩

/-- The *other* strand of a crossing `x` at a strand `s ∈ x`. -/
def other (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) : Γ.Strand :=
  Classical.choose (Γ.exists_other x hs)

theorem other_mem (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) : Γ.other x hs ∈ x.val :=
  (Classical.choose_spec (Γ.exists_other x hs)).1

theorem other_ne (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) : Γ.other x hs ≠ s :=
  (Classical.choose_spec (Γ.exists_other x hs)).2

/-- A crossing is exactly the pair of a strand and its other strand. -/
theorem eq_pair_other (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) :
    x.val = {s, Γ.other x hs} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hs, Γ.other_mem x hs⟩
  · rw [Γ.crossing_card_two x, Finset.card_pair (Γ.other_ne x hs).symm]

theorem mem_iff_eq_or_other (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) (t : Γ.Strand) :
    t ∈ x.val ↔ t = s ∨ t = Γ.other x hs := by
  classical
  rw [Γ.eq_pair_other x hs]
  simp

theorem eq_other_of_mem_of_ne (x : Γ.Crossing) {s t : Γ.Strand} (hs : s ∈ x.val)
    (ht : t ∈ x.val) (hne : t ≠ s) : t = Γ.other x hs :=
  ((Γ.mem_iff_eq_or_other x hs t).mp ht).resolve_left hne

theorem other_other (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) :
    Γ.other x (Γ.other_mem x hs) = s := by
  have h := Γ.other_mem x (Γ.other_mem x hs)
  rcases (Γ.mem_iff_eq_or_other x hs _).mp h with h' | h'
  · exact h'
  · exact absurd h' (Γ.other_ne x (Γ.other_mem x hs))

theorem not_adjacent_other (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) :
    ¬ Γ.Adjacent s (Γ.other x hs) :=
  (Γ.crossing_pair_spec x hs (Γ.other_mem x hs) (Γ.other_ne x hs).symm).1

theorem seg_inter_other_nonempty (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) :
    (Γ.seg s ∩ Γ.seg (Γ.other x hs)).Nonempty :=
  (Γ.crossing_pair_spec x hs (Γ.other_mem x hs) (Γ.other_ne x hs).symm).2

theorem crossing_common_point_exists (x : Γ.Crossing) :
    ∃ p : Plane, ∀ s ∈ x.val, p ∈ Γ.seg s := by
  classical
  obtain ⟨s, t, hx, -, p, hps, hpt⟩ := x.2
  refine ⟨p, fun u hu => ?_⟩
  rw [hx] at hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact hps
  · exact hpt

/-- The double point of a crossing: a chosen common point of its two edge segments (unique for a
generic shadow, `crossingPoint_unique`). -/
def crossingPoint (x : Γ.Crossing) : Plane :=
  Classical.choose (Γ.crossing_common_point_exists x)

theorem crossingPoint_mem (x : Γ.Crossing) {s : Γ.Strand} (hs : s ∈ x.val) :
    Γ.crossingPoint x ∈ Γ.seg s :=
  Classical.choose_spec (Γ.crossing_common_point_exists x) s hs

/-! ### Genericity -/

/-- The genericity clause of def:positive-lift for a polygonal shadow: "finitely many transverse
double points, no triple points" (sm-3:327), with the polygonal immersion condition of the
bridge paragraph (sm-3:340-341).  Fields:
* `regular`: every component is a regular polygon in the accepted sense (`Regular`: nonzero edges,
  no antiparallel consecutive edges; zero turns are allowed so that subdivision vertices stay in the
  class);
* `tail_off`: no vertex lies on an edge segment other than its two incident edges (across
  components as well), so all meetings of edges are at interior points of both edges and all
  vertices are distinct — the polygonal form of "immersion";
* `transverse`: two non-adjacent edges that meet have independent directions ("transverse double
  points"); finiteness of double points follows (finitely many edge pairs, each meeting at most
  once);
* `no_triple`: no point lies in the interior of three distinct edges ("no triple points"). -/
structure Generic : Prop where
  regular : ∀ i, Regular (Γ.comp i).P
  tail_off : ∀ s t, ¬ Γ.IncidentTail s t → Γ.tail s ∉ Γ.seg t
  transverse : ∀ s t, ¬ Γ.Adjacent s t → (Γ.seg s ∩ Γ.seg t).Nonempty →
    det (Γ.dir s) (Γ.dir t) ≠ 0
  no_triple : ¬ ∃ s t u : Γ.Strand, s ≠ t ∧ t ≠ u ∧ s ≠ u ∧
    (Γ.interior s ∩ Γ.interior t ∩ Γ.interior u).Nonempty

/-- The parameter circles of the components: a component index and an accepted `TraversalPoint`
(edge label plus a parameter in `[0,1)`). -/
abbrev Pt : Type := Σ i : Fin Γ.c, TraversalPoint (Γ.comp i).k

/-- The point of the plane traced at a traversal point (accepted `traversalEvaluation`). -/
def eval (p : Γ.Pt) : Plane := traversalEvaluation (Γ.comp p.1).P p.2

theorem eval_mk (i : Fin Γ.c) (p : TraversalPoint (Γ.comp i).k) :
    Γ.eval ⟨i, p⟩ = edgePoint (Γ.comp i).P p.1 p.2.val := rfl

/-- A point common to the two strands of a crossing is the crossing point, for a generic shadow
(transverse segments meet at most once). -/
theorem Generic.common_point_unique {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {p : Plane}
    (hp : ∀ s ∈ x.val, p ∈ Γ.seg s) : p = Γ.crossingPoint x := by
  obtain ⟨s, t, hx, hna, hmeet⟩ := x.2
  have hs : s ∈ x.val := by rw [hx]; simp
  have ht : t ∈ x.val := by rw [hx]; simp
  have hd := hΓ.transverse s t hna hmeet
  obtain ⟨a, -, -, ha⟩ := hp s hs
  obtain ⟨b, -, -, hb⟩ := hp t ht
  obtain ⟨a', -, -, ha'⟩ := Γ.crossingPoint_mem x hs
  obtain ⟨b', -, -, hb'⟩ := Γ.crossingPoint_mem x ht
  have h1 : (Γ.comp s.1).P s.2 + a • Γ.dir s = (Γ.comp t.1).P t.2 + b • Γ.dir t :=
    ha.symm.trans hb
  have h2 : (Γ.comp s.1).P s.2 + a' • Γ.dir s = (Γ.comp t.1).P t.2 + b' • Γ.dir t :=
    ha'.symm.trans hb'
  obtain ⟨rfl, -⟩ := intersection_parameters_unique hd h1 h2
  exact ha.trans ha'.symm

/-- For a generic shadow the crossing point lies in the interior of each of its two strands, at a
parameter strictly between `0` and `1` (the polygonal "transverse double point away from the
corners", from `tail_off`). -/
theorem Generic.crossingPoint_param {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s : Γ.Strand}
    (hs : s ∈ x.val) {τ : ℝ} (hτ : Γ.crossingPoint x = edgePoint (Γ.comp s.1).P s.2 τ)
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1) : 0 < τ ∧ τ < 1 := by
  have hna := Γ.not_adjacent_other x hs
  have hother := Γ.crossingPoint_mem x (Γ.other_mem x hs)
  obtain ⟨i, a⟩ := s
  constructor
  · rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      rw [edgePoint_zero] at hτ
      exact hΓ.tail_off ⟨i, a⟩ _ (fun hinc => hna hinc.adjacent)
        (by rw [show Γ.tail ⟨i, a⟩ = Γ.crossingPoint x from hτ.symm]; exact hother)
  · rcases h1.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      rw [edgePoint_one] at hτ
      exact hΓ.tail_off ⟨i, a + 1⟩ _ (fun hinc => hna (Γ.adjacent_of_incidentTail_succ hinc))
        (by rw [show Γ.tail ⟨i, a + 1⟩ = Γ.crossingPoint x from hτ.symm]; exact hother)

theorem Generic.crossingPoint_mem_interior {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)
    {s : Γ.Strand} (hs : s ∈ x.val) : Γ.crossingPoint x ∈ Γ.interior s := by
  obtain ⟨τ, h0, h1, hτ⟩ := Γ.crossingPoint_mem x hs
  obtain ⟨h0', h1'⟩ := hΓ.crossingPoint_param x hs hτ h0 h1
  exact ⟨τ, h0', h1', hτ⟩

/-- Two crossings with the same crossing point coincide (generic shadow, `no_triple`). -/
theorem Generic.crossingPoint_injective {Γ : Shadow} (hΓ : Γ.Generic) :
    Function.Injective Γ.crossingPoint := by
  classical
  intro x y hxy
  have key : ∀ x y : Γ.Crossing, Γ.crossingPoint x = Γ.crossingPoint y → x.val ⊆ y.val := by
    intro x y hxy u hu
    by_contra hnot
    obtain ⟨s, t, hy, hna, -⟩ := y.2
    have hs : s ∈ y.val := by rw [hy]; simp
    have ht : t ∈ y.val := by rw [hy]; simp
    have hus : u ≠ s := fun h => hnot (h ▸ hs)
    have hut : u ≠ t := fun h => hnot (h ▸ ht)
    apply hΓ.no_triple
    refine ⟨s, t, u, Γ.ne_of_not_adjacent hna, hut.symm, hus.symm, Γ.crossingPoint y, ?_⟩
    exact ⟨⟨hΓ.crossingPoint_mem_interior y hs, hΓ.crossingPoint_mem_interior y ht⟩,
      hxy ▸ hΓ.crossingPoint_mem_interior x hu⟩
  exact Subtype.ext (Finset.Subset.antisymm (key x y hxy) (key y x hxy.symm))

end Shadow

/-! ## Oriented link diagrams -/

/-- def:positive-lift, first sentence (sm-3:326-328): "An oriented link diagram in the plane is a
finite collection of closed oriented curves with finitely many transverse double points, no triple
points, and at each double point a choice of the over strand."  Polygonal reading (sm-3:337-341):
the curves are the components of a generic `Shadow`, and the over-strand choice is the field
`overStrand`, valued in the two strands of each crossing. -/
structure Diagram where
  /-- the finite collection of closed oriented (polygonal) curves -/
  Γ : Shadow
  /-- "finitely many transverse double points, no triple points" -/
  generic : Γ.Generic
  /-- "at each double point a choice of the over strand" -/
  overStrand : Γ.Crossing → Γ.Strand
  /-- the chosen over strand is one of the two strands of the crossing -/
  over_mem : ∀ x, overStrand x ∈ x.val

namespace Diagram

variable (D : Diagram)

/-- The under strand of a crossing: the other strand of the crossing. -/
def underStrand (x : D.Γ.Crossing) : D.Γ.Strand := D.Γ.other x (D.over_mem x)

theorem under_mem (x : D.Γ.Crossing) : D.underStrand x ∈ x.val := D.Γ.other_mem x (D.over_mem x)

theorem under_ne_over (x : D.Γ.Crossing) : D.underStrand x ≠ D.overStrand x :=
  D.Γ.other_ne x (D.over_mem x)

theorem over_ne_under (x : D.Γ.Crossing) : D.overStrand x ≠ D.underStrand x :=
  (D.under_ne_over x).symm

/-- Sanity: the over and under strands are exactly the two strands of the crossing. -/
theorem val_eq_pair (x : D.Γ.Crossing) : x.val = {D.overStrand x, D.underStrand x} :=
  D.Γ.eq_pair_other x (D.over_mem x)

theorem mem_iff (x : D.Γ.Crossing) (s : D.Γ.Strand) :
    s ∈ x.val ↔ s = D.overStrand x ∨ s = D.underStrand x :=
  D.Γ.mem_iff_eq_or_other x (D.over_mem x) s

theorem eq_under_of_mem_of_ne (x : D.Γ.Crossing) {s : D.Γ.Strand} (hs : s ∈ x.val)
    (hne : s ≠ D.overStrand x) : s = D.underStrand x :=
  D.Γ.eq_other_of_mem_of_ne x (D.over_mem x) hs hne

theorem eq_over_of_mem_of_ne (x : D.Γ.Crossing) {s : D.Γ.Strand} (hs : s ∈ x.val)
    (hne : s ≠ D.underStrand x) : s = D.overStrand x :=
  ((D.mem_iff x s).mp hs).resolve_right hne

theorem not_adjacent_over_under (x : D.Γ.Crossing) :
    ¬ D.Γ.Adjacent (D.overStrand x) (D.underStrand x) :=
  D.Γ.not_adjacent_other x (D.over_mem x)

theorem seg_over_inter_under_nonempty (x : D.Γ.Crossing) :
    (D.Γ.seg (D.overStrand x) ∩ D.Γ.seg (D.underStrand x)).Nonempty :=
  D.Γ.seg_inter_other_nonempty x (D.over_mem x)

/-- Transversality at every crossing: `det(u_o, u_u) ≠ 0`. -/
theorem det_over_under_ne_zero (x : D.Γ.Crossing) :
    det (D.Γ.dir (D.overStrand x)) (D.Γ.dir (D.underStrand x)) ≠ 0 :=
  D.generic.transverse _ _ (D.not_adjacent_over_under x) (D.seg_over_inter_under_nonempty x)

/-- def:positive-lift (sm-3:328-331): "A double point with over-strand direction u_o and
under-strand direction u_u is positive if det(u_o,u_u)>0 and negative otherwise."  Directions are
the accepted edge vectors of the over and under strands. -/
def IsPositive (x : D.Γ.Crossing) : Prop :=
  0 < det (D.Γ.dir (D.overStrand x)) (D.Γ.dir (D.underStrand x))

/-- The crossing sign `σ = sgn det(u_o, u_u)` (eq:gauss-cross-sign, sm-3:358-359, with the
convention of def:positive-lift sm-3:328-331). -/
def sign (x : D.Γ.Crossing) : SignType :=
  SignType.sign (det (D.Γ.dir (D.overStrand x)) (D.Γ.dir (D.underStrand x)))

/-- Sanity: signs are never zero for a generic diagram (transversality). -/
theorem sign_ne_zero (x : D.Γ.Crossing) : D.sign x ≠ 0 :=
  _root_.sign_ne_zero.mpr (D.det_over_under_ne_zero x)

theorem isPositive_iff_sign_eq_one (x : D.Γ.Crossing) : D.IsPositive x ↔ D.sign x = 1 :=
  sign_eq_one_iff.symm

theorem sign_eq_neg_one_iff (x : D.Γ.Crossing) : D.sign x = -1 ↔ ¬ D.IsPositive x := by
  unfold IsPositive sign
  rw [_root_.sign_eq_neg_one_iff, not_lt]
  constructor
  · exact le_of_lt
  · intro h
    exact lt_of_le_of_ne h (D.det_over_under_ne_zero x)

theorem sign_eq_one_or_neg_one (x : D.Γ.Crossing) : D.sign x = 1 ∨ D.sign x = -1 := by
  rcases h : D.sign x with _ | _ | _
  · exact absurd h (D.sign_ne_zero x)
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- def:positive-lift (sm-3:334): "Its writhe (the sum of crossing signs)". -/
def writhe : ℤ := ∑ x : D.Γ.Crossing, (D.sign x : ℤ)

/-- The component count `c` of lp:lm (sm-3:946-947, "c-component"; sm-3:951 "Here c ≥ 1"). -/
def componentCount : ℕ := D.Γ.c

theorem componentCount_pos : 0 < D.componentCount := D.Γ.hc

/-- "the crossing-free circle" (lit:homfly sm-3:919, lp:lm-uniqueness "the unknot" sm-3:967): a
one-component diagram with no crossing.  Every such diagram is meant (design decision D10; no
Jordan/Schoenflies theorem is needed). -/
def IsCrossingFreeCircle : Prop := D.Γ.c = 1 ∧ IsEmpty D.Γ.Crossing

theorem writhe_eq_zero_of_isEmpty (h : IsEmpty D.Γ.Crossing) : D.writhe = 0 := by
  unfold writhe
  rw [Finset.univ_eq_empty, Finset.sum_empty]

theorem IsCrossingFreeCircle.writhe_eq_zero (h : D.IsCrossingFreeCircle) : D.writhe = 0 :=
  D.writhe_eq_zero_of_isEmpty h.2

/-- The over occurrence of a crossing. -/
def overVisit (x : D.Γ.Crossing) : D.Γ.Visit := ⟨x, ⟨D.overStrand x, D.over_mem x⟩⟩

/-- The under occurrence of a crossing. -/
def underVisit (x : D.Γ.Crossing) : D.Γ.Visit := ⟨x, ⟨D.underStrand x, D.under_mem x⟩⟩

@[simp] theorem overVisit_fst (x : D.Γ.Crossing) : (D.overVisit x).1 = x := rfl
@[simp] theorem underVisit_fst (x : D.Γ.Crossing) : (D.underVisit x).1 = x := rfl
@[simp] theorem overVisit_strand (x : D.Γ.Crossing) : (D.overVisit x).2.val = D.overStrand x := rfl
@[simp] theorem underVisit_strand (x : D.Γ.Crossing) :
    (D.underVisit x).2.val = D.underStrand x := rfl

theorem overVisit_ne_underVisit (x : D.Γ.Crossing) : D.overVisit x ≠ D.underVisit x := by
  intro h
  exact D.over_ne_under x (congrArg (fun v : D.Γ.Visit => v.2.val) h)

/-- Sanity: every occurrence is the over or the under occurrence of its crossing. -/
theorem visit_eq_over_or_under (v : D.Γ.Visit) : v = D.overVisit v.1 ∨ v = D.underVisit v.1 := by
  obtain ⟨x, s, hs⟩ := v
  rcases (D.mem_iff x s).mp hs with h | h
  · left
    simp only [overVisit]
    congr 1
    exact Subtype.ext h
  · right
    simp only [underVisit]
    congr 1
    exact Subtype.ext h

/-- The occurrence bit "over" of def:gauss-record (sm-3:356-357, "an over/under bit at each
occurrence"). -/
def isOver (v : D.Γ.Visit) : Prop := v.2.val = D.overStrand v.1

theorem isOver_overVisit (x : D.Γ.Crossing) : D.isOver (D.overVisit x) := rfl

theorem not_isOver_underVisit (x : D.Γ.Crossing) : ¬ D.isOver (D.underVisit x) :=
  D.under_ne_over x

/-! ### Replacing the over data on the same shadow; switching one crossing -/

/-- The diagram on the same generic shadow with a new over-strand choice. -/
def withOver (ov : D.Γ.Crossing → D.Γ.Strand) (h : ∀ x, ov x ∈ x.val) : Diagram :=
  ⟨D.Γ, D.generic, ov, h⟩

theorem withOver_congr {f g : D.Γ.Crossing → D.Γ.Strand} (h : f = g) (hf : ∀ x, f x ∈ x.val)
    (hg : ∀ x, g x ∈ x.val) : D.withOver f hf = D.withOver g hg := by
  subst h
  rfl

theorem withOver_overStrand_over_mem : D.withOver D.overStrand D.over_mem = D := rfl

/-- `D^{sw}`: the diagram with the over and under strands exchanged at the one crossing `x₀` and
unchanged elsewhere (the "crossing switches" of lp:lm sm-3:939-940 and the `D_+ / D_-` pair of the
skein relation, lp:source-skein sm-3:942-945).  Same shadow, same genericity proof. -/
def switch (x₀ : D.Γ.Crossing) : Diagram where
  Γ := D.Γ
  generic := D.generic
  overStrand := Function.update D.overStrand x₀ (D.underStrand x₀)
  over_mem := by
    intro x
    by_cases h : x = x₀
    · subst h
      rw [Function.update_self]
      exact D.under_mem x
    · rw [Function.update_of_ne h]
      exact D.over_mem x

@[simp] theorem switch_Γ (x₀ : D.Γ.Crossing) : (D.switch x₀).Γ = D.Γ := rfl

theorem switch_overStrand_self (x₀ : D.Γ.Crossing) :
    (D.switch x₀).overStrand x₀ = D.underStrand x₀ :=
  Function.update_self x₀ _ _

theorem switch_overStrand_of_ne {x x₀ : D.Γ.Crossing} (h : x ≠ x₀) :
    (D.switch x₀).overStrand x = D.overStrand x :=
  Function.update_of_ne h _ _

theorem switch_underStrand_self (x₀ : D.Γ.Crossing) :
    (D.switch x₀).underStrand x₀ = D.overStrand x₀ := by
  symm
  apply D.Γ.eq_other_of_mem_of_ne x₀ ((D.switch x₀).over_mem x₀) (D.over_mem x₀)
  rw [switch_overStrand_self]
  exact D.over_ne_under x₀

theorem switch_underStrand_of_ne {x x₀ : D.Γ.Crossing} (h : x ≠ x₀) :
    (D.switch x₀).underStrand x = D.underStrand x := by
  symm
  apply D.Γ.eq_other_of_mem_of_ne x ((D.switch x₀).over_mem x) (D.under_mem x)
  rw [switch_overStrand_of_ne D h]
  exact D.under_ne_over x

/-- Sanity: switching negates the sign at the switched crossing. -/
theorem switch_sign_self (x₀ : D.Γ.Crossing) : (D.switch x₀).sign x₀ = -D.sign x₀ := by
  unfold sign
  rw [switch_overStrand_self, switch_underStrand_self, det_swap, Left.sign_neg]
  rfl

/-- Sanity: switching leaves every other sign unchanged. -/
theorem switch_sign_of_ne {x x₀ : D.Γ.Crossing} (h : x ≠ x₀) : (D.switch x₀).sign x = D.sign x := by
  unfold sign
  rw [switch_overStrand_of_ne D h, switch_underStrand_of_ne D h]
  rfl

theorem switch_isPositive_self (x₀ : D.Γ.Crossing) :
    (D.switch x₀).IsPositive x₀ ↔ ¬ D.IsPositive x₀ := by
  rw [(D.switch x₀).isPositive_iff_sign_eq_one x₀, switch_sign_self, neg_eq_iff_eq_neg,
    D.sign_eq_neg_one_iff x₀]

theorem switch_isPositive_of_ne {x x₀ : D.Γ.Crossing} (h : x ≠ x₀) :
    (D.switch x₀).IsPositive x ↔ D.IsPositive x := by
  rw [(D.switch x₀).isPositive_iff_sign_eq_one x, D.isPositive_iff_sign_eq_one x,
    switch_sign_of_ne D h]

/-- Switching twice at the same crossing restores the diagram. -/
theorem switch_switch (x₀ : D.Γ.Crossing) : (D.switch x₀).switch x₀ = D := by
  have h : ((D.switch x₀).switch x₀).overStrand = D.overStrand := by
    funext x
    by_cases hx : x = x₀
    · rw [hx]
      exact (switch_overStrand_self (D.switch x₀) x₀).trans (switch_underStrand_self D x₀)
    · exact (switch_overStrand_of_ne (D.switch x₀) hx).trans (switch_overStrand_of_ne D hx)
  calc (D.switch x₀).switch x₀
      = D.withOver ((D.switch x₀).switch x₀).overStrand ((D.switch x₀).switch x₀).over_mem := rfl
    _ = D.withOver D.overStrand D.over_mem := D.withOver_congr h _ _
    _ = D := rfl

/-- Sanity: the writhe drops by twice the switched sign. -/
theorem switch_writhe (x₀ : D.Γ.Crossing) :
    (D.switch x₀).writhe = D.writhe - 2 * (D.sign x₀ : ℤ) := by
  have h1 : (D.switch x₀).writhe = ((D.switch x₀).sign x₀ : ℤ) +
      ∑ x ∈ ({x₀}ᶜ : Finset D.Γ.Crossing), ((D.switch x₀).sign x : ℤ) :=
    Fintype.sum_eq_add_sum_compl x₀ _
  have h2 : D.writhe = (D.sign x₀ : ℤ) + ∑ x ∈ ({x₀}ᶜ : Finset D.Γ.Crossing), (D.sign x : ℤ) :=
    Fintype.sum_eq_add_sum_compl x₀ _
  have h3 : ∑ x ∈ ({x₀}ᶜ : Finset D.Γ.Crossing), ((D.switch x₀).sign x : ℤ) =
      ∑ x ∈ ({x₀}ᶜ : Finset D.Γ.Crossing), (D.sign x : ℤ) :=
    Finset.sum_congr rfl fun x hx => by rw [switch_sign_of_ne D (by simpa using hx)]
  rw [h1, h2, h3, switch_sign_self, SignType.coe_neg]
  ring

end Diagram

/-! ## Transport of shadows along strand relabellings

`restrict`, `reverse` and `mirror` are all instances of one construction: a relabelling of the
strands of a new shadow `Γ'` into the strands of the given shadow `Γ`, compatible with an injective
map of the plane, along which genericity pulls back and the over data of a diagram is pulled back.
-/

/-- A relabelling of the strands of `Γ'` into the strands of `Γ`, compatible with an injective map
`f` of the plane: edge segments and open edges correspond under `f`; the tail vertex of `s` is
carried by `f` to the tail vertex of a strand `vert s` of `Γ`; adjacency and vertex-edge incidence
are preserved and reflected; and all determinants of pairs of directions are multiplied by one fixed
nonzero sign `sgn`.  Instances below: component restriction (`f = id`, `sgn = 1`), reversal of
every component (`f = id`, `⟨i, j⟩ ↦ ⟨i, 1 - j⟩`, `sgn = 1`), mirror reflection
(`f (x, y) = (x, -y)`, `sgn = -1`). -/
structure StrandMap (Γ' Γ : Shadow) where
  toFun : Γ'.Strand → Γ.Strand
  inj : Function.Injective toFun
  f : Plane → Plane
  f_inj : Function.Injective f
  seg_eq : ∀ s, Γ.seg (toFun s) = f '' Γ'.seg s
  interior_eq : ∀ s, Γ.interior (toFun s) = f '' Γ'.interior s
  vert : Γ'.Strand → Γ.Strand
  tail_eq : ∀ s, Γ.tail (vert s) = f (Γ'.tail s)
  adjacent_iff : ∀ s t, Γ.Adjacent (toFun s) (toFun t) ↔ Γ'.Adjacent s t
  incidentTail_iff : ∀ s t, Γ.IncidentTail (vert s) (toFun t) ↔ Γ'.IncidentTail s t
  sgn : SignType
  sgn_ne : sgn ≠ 0
  det_eq : ∀ s t, det (Γ.dir (toFun s)) (Γ.dir (toFun t)) = (sgn : ℝ) * det (Γ'.dir s) (Γ'.dir t)

namespace StrandMap

variable {Γ' Γ : Shadow} (m : StrandMap Γ' Γ)

/-- The strand relabelling as an embedding. -/
def emb : Γ'.Strand ↪ Γ.Strand := ⟨m.toFun, m.inj⟩

@[simp] theorem emb_apply (s : Γ'.Strand) : m.emb s = m.toFun s := rfl

theorem sgn_eq_one_or_neg_one : m.sgn = 1 ∨ m.sgn = -1 := by
  rcases h : m.sgn with _ | _ | _
  · exact absurd h m.sgn_ne
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem coe_sgn_ne_zero : (m.sgn : ℝ) ≠ 0 := by
  rcases m.sgn_eq_one_or_neg_one with h | h <;> rw [h] <;> simp

theorem det_ne_zero_iff (s t : Γ'.Strand) :
    det (Γ.dir (m.toFun s)) (Γ.dir (m.toFun t)) ≠ 0 ↔ det (Γ'.dir s) (Γ'.dir t) ≠ 0 := by
  rw [m.det_eq, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨m.coe_sgn_ne_zero, h⟩⟩

theorem seg_inter_nonempty_iff (s t : Γ'.Strand) :
    (Γ.seg (m.toFun s) ∩ Γ.seg (m.toFun t)).Nonempty ↔ (Γ'.seg s ∩ Γ'.seg t).Nonempty := by
  rw [m.seg_eq, m.seg_eq, ← Set.image_inter m.f_inj]
  exact Set.image_nonempty

/-- Crossings correspond under the relabelling of their strand pairs. -/
theorem isCrossing_map_iff (x : Finset Γ'.Strand) :
    Γ.IsCrossing (x.map m.emb) ↔ Γ'.IsCrossing x := by
  constructor
  · rintro ⟨s, t, hx, hna, hmeet⟩
    have hs : s ∈ x.map m.emb := by rw [hx]; simp
    have ht : t ∈ x.map m.emb := by rw [hx]; simp
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    refine ⟨s', t', ?_, fun h => hna ((m.adjacent_iff s' t').mpr h),
      (m.seg_inter_nonempty_iff s' t').mp hmeet⟩
    apply Finset.map_injective m.emb
    rw [hx, Finset.map_insert, Finset.map_singleton]
  · rintro ⟨s, t, rfl, hna, hmeet⟩
    refine ⟨m.toFun s, m.toFun t, ?_, fun h => hna ((m.adjacent_iff s t).mp h),
      (m.seg_inter_nonempty_iff s t).mpr hmeet⟩
    rw [Finset.map_insert, Finset.map_singleton]
    rfl

/-- The crossing of `Γ` corresponding to a crossing of `Γ'`. -/
def mapCrossing (x : Γ'.Crossing) : Γ.Crossing :=
  ⟨x.val.map m.emb, (m.isCrossing_map_iff x.val).mpr x.2⟩

@[simp] theorem mapCrossing_val (x : Γ'.Crossing) : (m.mapCrossing x).val = x.val.map m.emb := rfl

theorem mapCrossing_injective : Function.Injective m.mapCrossing := by
  intro x y h
  exact Subtype.ext (Finset.map_injective m.emb (congrArg Subtype.val h))

theorem toFun_mem_mapCrossing_iff (x : Γ'.Crossing) (s : Γ'.Strand) :
    m.toFun s ∈ (m.mapCrossing x).val ↔ s ∈ x.val :=
  Finset.mem_map' m.emb

theorem toFun_mem_of_mem {x : Γ'.Crossing} {s : Γ'.Strand} (hs : s ∈ x.val) :
    m.toFun s ∈ (m.mapCrossing x).val :=
  (m.toFun_mem_mapCrossing_iff x s).mpr hs

theorem exists_preimage_of_mem {x : Γ'.Crossing} {u : Γ.Strand} (hu : u ∈ (m.mapCrossing x).val) :
    ∃ s ∈ x.val, m.toFun s = u :=
  Finset.mem_map.mp hu

/-- The other strand of a crossing transports. -/
theorem other_mapCrossing {x : Γ'.Crossing} {s : Γ'.Strand} (hs : s ∈ x.val) :
    Γ.other (m.mapCrossing x) (m.toFun_mem_of_mem hs) = m.toFun (Γ'.other x hs) := by
  symm
  apply Γ.eq_other_of_mem_of_ne
  · exact m.toFun_mem_of_mem (Γ'.other_mem x hs)
  · intro h
    exact Γ'.other_ne x hs (m.inj h)

/-- The crossing point transports by `f` when the target shadow is generic. -/
theorem crossingPoint_mapCrossing (hΓ : Γ.Generic) (x : Γ'.Crossing) :
    Γ.crossingPoint (m.mapCrossing x) = m.f (Γ'.crossingPoint x) := by
  symm
  apply hΓ.common_point_unique
  intro u hu
  obtain ⟨s, hs, rfl⟩ := m.exists_preimage_of_mem hu
  rw [m.seg_eq]
  exact ⟨_, Γ'.crossingPoint_mem x hs, rfl⟩

/-- Genericity pulls back along a strand relabelling (given regular components of `Γ'`). -/
theorem generic_pullback (m : StrandMap Γ' Γ) (hΓ : Γ.Generic) (hreg : ∀ i, Regular (Γ'.comp i).P) :
    Γ'.Generic where
  regular := hreg
  tail_off := by
    intro s t hinc hmem
    apply hΓ.tail_off (m.vert s) (m.toFun t) (fun h => hinc ((m.incidentTail_iff s t).mp h))
    rw [m.tail_eq, m.seg_eq]
    exact ⟨_, hmem, rfl⟩
  transverse := by
    intro s t hna hmeet
    rw [← m.det_ne_zero_iff]
    exact hΓ.transverse _ _ (fun h => hna ((m.adjacent_iff s t).mp h))
      ((m.seg_inter_nonempty_iff s t).mpr hmeet)
  no_triple := by
    rintro ⟨s, t, u, hst, htu, hsu, p, ⟨hps, hpt⟩, hpu⟩
    apply hΓ.no_triple
    refine ⟨m.toFun s, m.toFun t, m.toFun u, fun h => hst (m.inj h), fun h => htu (m.inj h),
      fun h => hsu (m.inj h), m.f p, ⟨?_, ?_⟩, ?_⟩
    · rw [m.interior_eq]; exact ⟨p, hps, rfl⟩
    · rw [m.interior_eq]; exact ⟨p, hpt, rfl⟩
    · rw [m.interior_eq]; exact ⟨p, hpu, rfl⟩

/-- For a surjective relabelling every crossing of `Γ` comes from a crossing of `Γ'`. -/
theorem mapCrossing_surjective (hsurj : Function.Surjective m.toFun) :
    Function.Surjective m.mapCrossing := by
  intro x
  obtain ⟨s, t, hx, hna, hmeet⟩ := x.2
  obtain ⟨s', rfl⟩ := hsurj s
  obtain ⟨t', rfl⟩ := hsurj t
  have hx' : Γ'.IsCrossing {s', t'} := by
    rw [← m.isCrossing_map_iff, Finset.map_insert, Finset.map_singleton, emb_apply, emb_apply,
      ← hx]
    exact x.2
  refine ⟨(⟨{s', t'}, hx'⟩ : Γ'.Crossing), Subtype.ext ?_⟩
  show Finset.map m.emb {s', t'} = x.val
  rw [Finset.map_insert, Finset.map_singleton, hx]
  rfl

/-- The crossing bijection induced by a surjective relabelling. -/
def crossingEquiv (hsurj : Function.Surjective m.toFun) : Γ'.Crossing ≃ Γ.Crossing :=
  Equiv.ofBijective m.mapCrossing ⟨m.mapCrossing_injective, m.mapCrossing_surjective hsurj⟩

@[simp] theorem crossingEquiv_apply (hsurj : Function.Surjective m.toFun) (x : Γ'.Crossing) :
    m.crossingEquiv hsurj x = m.mapCrossing x := rfl

end StrandMap

namespace Diagram

variable (D : Diagram)

/-- The diagram on `Γ'` obtained by pulling back the over data of `D` along a strand
relabelling `m : StrandMap Γ' D.Γ` (the over strand at `x'` is the strand of `x'` that `m` sends to
the over strand of `D` at the corresponding crossing).  Used for `restrict`, `reverse`, `mirror`. -/
def pullback {Γ' : Shadow} (m : StrandMap Γ' D.Γ) (hreg : ∀ i, Regular (Γ'.comp i).P) : Diagram where
  Γ := Γ'
  generic := m.generic_pullback D.generic hreg
  overStrand := fun x => Classical.choose (m.exists_preimage_of_mem (D.over_mem (m.mapCrossing x)))
  over_mem := fun x =>
    (Classical.choose_spec (m.exists_preimage_of_mem (D.over_mem (m.mapCrossing x)))).1

variable {Γ' : Shadow} (m : StrandMap Γ' D.Γ) (hreg : ∀ i, Regular (Γ'.comp i).P)

@[simp] theorem pullback_Γ : (D.pullback m hreg).Γ = Γ' := rfl

/-- The pulled-back over strand is sent to the original over strand ("over data kept"). -/
theorem toFun_pullback_overStrand (x : Γ'.Crossing) :
    m.toFun ((D.pullback m hreg).overStrand x) = D.overStrand (m.mapCrossing x) :=
  (Classical.choose_spec (m.exists_preimage_of_mem (D.over_mem (m.mapCrossing x)))).2

theorem toFun_pullback_underStrand (x : Γ'.Crossing) :
    m.toFun ((D.pullback m hreg).underStrand x) = D.underStrand (m.mapCrossing x) := by
  apply D.eq_under_of_mem_of_ne
  · exact m.toFun_mem_of_mem ((D.pullback m hreg).under_mem x)
  · rw [← toFun_pullback_overStrand D m hreg]
    intro h
    exact (D.pullback m hreg).under_ne_over x (m.inj h)

/-- Signs transport up to the fixed sign of the relabelling. -/
theorem pullback_sign (x : Γ'.Crossing) :
    (D.pullback m hreg).sign x = m.sgn * D.sign (m.mapCrossing x) := by
  have ho := toFun_pullback_overStrand D m hreg x
  have hu := toFun_pullback_underStrand D m hreg x
  have hdet := m.det_eq ((D.pullback m hreg).overStrand x) ((D.pullback m hreg).underStrand x)
  rw [ho, hu] at hdet
  change SignType.sign (det (Γ'.dir ((D.pullback m hreg).overStrand x))
    (Γ'.dir ((D.pullback m hreg).underStrand x))) =
    m.sgn * SignType.sign (det (D.Γ.dir (D.overStrand (m.mapCrossing x)))
      (D.Γ.dir (D.underStrand (m.mapCrossing x))))
  rw [hdet, sign_mul]
  rcases m.sgn_eq_one_or_neg_one with h | h <;> rw [h] <;> simp

theorem pullback_isPositive_iff (x : Γ'.Crossing) :
    (D.pullback m hreg).IsPositive x ↔ (m.sgn = 1 ∧ D.IsPositive (m.mapCrossing x)) ∨
      (m.sgn = -1 ∧ ¬ D.IsPositive (m.mapCrossing x)) := by
  rw [(D.pullback m hreg).isPositive_iff_sign_eq_one x, pullback_sign,
    D.isPositive_iff_sign_eq_one]
  rcases m.sgn_eq_one_or_neg_one with h | h <;> rw [h] <;>
    rcases D.sign_eq_one_or_neg_one (m.mapCrossing x) with h' | h' <;> rw [h'] <;> decide

/-- The writhe transports up to the fixed sign, for a surjective relabelling. -/
theorem pullback_writhe (hsurj : Function.Surjective m.toFun) :
    (D.pullback m hreg).writhe = m.sgn * D.writhe := by
  unfold writhe
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (m.crossingEquiv hsurj) _ _ fun x => ?_
  rw [pullback_sign, SignType.coe_mul, StrandMap.crossingEquiv_apply]

/-! ## Restriction to a block of components (mp:stack / mp:lowest) -/

end Diagram

namespace Shadow

variable (Γ : Shadow)

/-- The shadow consisting of the components in the nonempty block `B`, reindexed in increasing
order by `B.orderEmbOfFin`. -/
abbrev restrictShadow (B : Finset (Fin Γ.c)) (hB : B.Nonempty) : Shadow where
  c := B.card
  hc := Finset.card_pos.mpr hB
  comp := fun j => Γ.comp (B.orderEmbOfFin rfl j)

/-- The strand relabelling of a block restriction: `⟨j, a⟩ ↦ ⟨B.orderEmbOfFin rfl j, a⟩`. -/
def restrictMap (B : Finset (Fin Γ.c)) (hB : B.Nonempty) : StrandMap (Γ.restrictShadow B hB) Γ where
  toFun := fun s => ⟨B.orderEmbOfFin rfl s.1, s.2⟩
  inj := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    dsimp only at h
    rw [Sigma.mk.inj_iff] at h
    obtain ⟨hij, hab⟩ := h
    have hij' := (B.orderEmbOfFin rfl).injective hij
    subst hij'
    rw [eq_of_heq hab]
  f := id
  f_inj := fun _ _ h => h
  seg_eq := fun s => by rw [Set.image_id]; rfl
  interior_eq := fun s => by rw [Set.image_id]; rfl
  vert := fun s => ⟨B.orderEmbOfFin rfl s.1, s.2⟩
  tail_eq := fun s => rfl
  adjacent_iff := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    constructor
    · intro h
      have hij := (B.orderEmbOfFin rfl).injective h.fst_eq
      subst hij
      exact ((Γ.restrictShadow B hB).adjacent_mk_iff i a b).mpr ((Γ.adjacent_mk_iff _ a b).mp h)
    · intro h
      obtain rfl := h.fst_eq
      exact (Γ.adjacent_mk_iff _ a b).mpr (((Γ.restrictShadow B hB).adjacent_mk_iff i a b).mp h)
  incidentTail_iff := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    constructor
    · intro h
      have hij := (B.orderEmbOfFin rfl).injective h.fst_eq
      subst hij
      exact ((Γ.restrictShadow B hB).incidentTail_mk_iff i a b).mpr
        ((Γ.incidentTail_mk_iff _ a b).mp h)
    · intro h
      obtain rfl := h.fst_eq
      exact (Γ.incidentTail_mk_iff _ a b).mpr
        (((Γ.restrictShadow B hB).incidentTail_mk_iff i a b).mp h)
  sgn := 1
  sgn_ne := by decide
  det_eq := fun s t => by rw [SignType.coe_one, one_mul]; rfl

theorem restrictMap_toFun (B : Finset (Fin Γ.c)) (hB : B.Nonempty)
    (s : (Γ.restrictShadow B hB).Strand) :
    (Γ.restrictMap B hB).toFun s = ⟨B.orderEmbOfFin rfl s.1, s.2⟩ := rfl

@[simp] theorem restrictMap_sgn (B : Finset (Fin Γ.c)) (hB : B.Nonempty) :
    (Γ.restrictMap B hB).sgn = 1 := rfl

/-- A strand in the image of the restriction lies on a component of the block. -/
theorem restrictMap_fst_mem (B : Finset (Fin Γ.c)) (hB : B.Nonempty)
    (s : (Γ.restrictShadow B hB).Strand) : ((Γ.restrictMap B hB).toFun s).1 ∈ B :=
  Finset.orderEmbOfFin_mem B rfl s.1

/-- Sanity (mp:stack / mp:lowest): the crossings of the restricted shadow are exactly the
*internal* crossings of the block — those crossings of `Γ` both of whose strands lie on components
of `B`. -/
theorem restrict_mapCrossing_range_iff (B : Finset (Fin Γ.c)) (hB : B.Nonempty) (x : Γ.Crossing) :
    (∃ y, (Γ.restrictMap B hB).mapCrossing y = x) ↔ ∀ s ∈ x.val, s.1 ∈ B := by
  constructor
  · rintro ⟨y, rfl⟩ s hs
    obtain ⟨s', -, rfl⟩ := (Γ.restrictMap B hB).exists_preimage_of_mem hs
    exact Γ.restrictMap_fst_mem B hB s'
  · intro hB'
    obtain ⟨⟨i, a⟩, ⟨j, b⟩, hx, hna, hmeet⟩ := x.2
    have hi : i ∈ B := hB' ⟨i, a⟩ (by rw [hx]; simp)
    have hj : j ∈ B := hB' ⟨j, b⟩ (by rw [hx]; simp)
    have hi' : i ∈ Set.range (B.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hi
    have hj' : j ∈ Set.range (B.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hj
    obtain ⟨i', rfl⟩ := hi'
    obtain ⟨j', rfl⟩ := hj'
    have hy : (Γ.restrictShadow B hB).IsCrossing {⟨i', a⟩, ⟨j', b⟩} := by
      rw [← (Γ.restrictMap B hB).isCrossing_map_iff, Finset.map_insert, Finset.map_singleton]
      rw [StrandMap.emb_apply, StrandMap.emb_apply, restrictMap_toFun, restrictMap_toFun, ← hx]
      exact x.2
    refine ⟨(⟨_, hy⟩ : (Γ.restrictShadow B hB).Crossing), Subtype.ext ?_⟩
    show Finset.map (Γ.restrictMap B hB).emb {⟨i', a⟩, ⟨j', b⟩} = x.val
    rw [Finset.map_insert, Finset.map_singleton, hx]
    rfl

/-- The crossings of the restriction, as a bijection with the internal crossings of the block. -/
def restrictCrossingEquiv (B : Finset (Fin Γ.c)) (hB : B.Nonempty) :
    (Γ.restrictShadow B hB).Crossing ≃ {x : Γ.Crossing // ∀ s ∈ x.val, s.1 ∈ B} :=
  Equiv.ofBijective
    (fun y => ⟨(Γ.restrictMap B hB).mapCrossing y,
      (Γ.restrict_mapCrossing_range_iff B hB _).mp ⟨y, rfl⟩⟩)
    ⟨fun y z h => (Γ.restrictMap B hB).mapCrossing_injective (congrArg Subtype.val h),
     fun x => by
      obtain ⟨y, hy⟩ := (Γ.restrict_mapCrossing_range_iff B hB x.val).mpr x.2
      exact ⟨y, Subtype.ext hy⟩⟩

end Shadow

namespace Diagram

variable (D : Diagram)

/-- The block restriction `D|_B` (mp:stack, mp:lowest): the diagram formed by the components in the
nonempty block `B`, reindexed in increasing order, with the over data of `D` at every internal
crossing; genericity is inherited. -/
def restrict (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) : Diagram :=
  D.pullback (D.Γ.restrictMap B hB) fun j => D.generic.regular (B.orderEmbOfFin rfl j)

theorem restrict_componentCount (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) :
    (D.restrict B hB).componentCount = B.card := rfl

theorem restrict_sign (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (x : (D.Γ.restrictShadow B hB).Crossing) :
    (D.restrict B hB).sign x = D.sign ((D.Γ.restrictMap B hB).mapCrossing x) := by
  have h := pullback_sign D (D.Γ.restrictMap B hB)
    (fun j => D.generic.regular (B.orderEmbOfFin rfl j)) x
  rw [Shadow.restrictMap_sgn, one_mul] at h
  exact h

/-- Sanity: restricting to all components changes nothing about the crossing set. -/
theorem restrict_univ_crossing_range (x : D.Γ.Crossing) :
    ∃ y, (D.Γ.restrictMap Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, D.Γ.hc⟩⟩)).mapCrossing y = x :=
  (D.Γ.restrict_mapCrossing_range_iff _ _ x).mpr fun s _ => Finset.mem_univ s.1

end Diagram

/-! ## Reversal of every component (cf:thm-carrierfloor (R)) -/

/-- The component with reversed orientation (accepted `reversal`: `i ↦ P (2 - i)`). -/
abbrev PolyComp.reverse (C : PolyComp) : PolyComp := ⟨C.k, C.hk, reversal C.P⟩

namespace Shadow

variable (Γ : Shadow)

/-- The shadow with every component reversed. -/
abbrev reverseShadow : Shadow := ⟨Γ.c, Γ.hc, fun i => (Γ.comp i).reverse⟩

theorem adjacent_one_sub_iff {n : ℕ} (a b : ZMod n) : adjacent (1 - a) (1 - b) ↔ adjacent a b := by
  have h : adjacent (1 - a) (1 - b) ↔ adjacent b a := by
    unfold adjacent
    rw [show (1 - b) - (1 - a) = a - b by ring]
  rw [h]
  exact ⟨adjacent_symm', adjacent_symm'⟩

theorem incident_reverse_iff {n : ℕ} (a b : ZMod n) : incident (2 - a) (1 - b) ↔ incident a b := by
  unfold incident
  constructor
  · rintro (h | h)
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination -h)
  · rintro (h | h)
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination -h)

/-- The strand relabelling of reversal: the strand `⟨i, a⟩` of the reversed component is the strand
`⟨i, 1 - a⟩` of the original traversed backwards (accepted `edge_reversal`,
`edgeSegment_reversal`); its tail `P (2 - a)` is the tail of the original strand `⟨i, 2 - a⟩`. -/
def reverseMap : StrandMap Γ.reverseShadow Γ where
  toFun := fun s => ⟨s.1, 1 - (s.2 : ZMod (Γ.comp s.1).k)⟩
  inj := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    dsimp only at h
    rw [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, hab⟩ := h
    rw [sub_right_inj.mp (eq_of_heq hab)]
  f := id
  f_inj := fun _ _ h => h
  seg_eq := fun s => by
    rw [Set.image_id]
    exact (edgeSegment_reversal (Γ.comp s.1).P s.2).symm
  interior_eq := fun s => by
    rw [Set.image_id]
    exact (edgeInterior_reversal (Γ.comp s.1).P s.2).symm
  vert := fun s => ⟨s.1, 2 - (s.2 : ZMod (Γ.comp s.1).k)⟩
  tail_eq := fun s => rfl
  adjacent_iff := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    constructor
    · intro h
      obtain rfl := h.fst_eq
      exact (Γ.reverseShadow.adjacent_mk_iff i a b).mpr
        ((adjacent_one_sub_iff a b).mp ((Γ.adjacent_mk_iff i _ _).mp h))
    · intro h
      obtain rfl := h.fst_eq
      exact (Γ.adjacent_mk_iff i _ _).mpr
        ((adjacent_one_sub_iff a b).mpr ((Γ.reverseShadow.adjacent_mk_iff i a b).mp h))
  incidentTail_iff := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    constructor
    · intro h
      obtain rfl := h.fst_eq
      exact (Γ.reverseShadow.incidentTail_mk_iff i a b).mpr
        ((incident_reverse_iff a b).mp ((Γ.incidentTail_mk_iff i _ _).mp h))
    · intro h
      obtain rfl := h.fst_eq
      exact (Γ.incidentTail_mk_iff i _ _).mpr
        ((incident_reverse_iff a b).mpr ((Γ.reverseShadow.incidentTail_mk_iff i a b).mp h))
  sgn := 1
  sgn_ne := by decide
  det_eq := fun s t => by
    rw [SignType.coe_one, one_mul]
    change det (edge (Γ.comp s.1).P (1 - s.2)) (edge (Γ.comp t.1).P (1 - t.2)) =
      det (edge (reversal (Γ.comp s.1).P) s.2) (edge (reversal (Γ.comp t.1).P) t.2)
    rw [edge_reversal, edge_reversal]
    unfold det
    simp only [Prod.fst_neg, Prod.snd_neg]
    ring

theorem reverseMap_toFun (s : Γ.reverseShadow.Strand) :
    (Γ.reverseMap).toFun s = ⟨s.1, 1 - (s.2 : ZMod (Γ.comp s.1).k)⟩ := rfl

@[simp] theorem reverseMap_sgn : (Γ.reverseMap).sgn = 1 := rfl

theorem reverseMap_surjective : Function.Surjective (Γ.reverseMap).toFun := by
  rintro ⟨i, a⟩
  refine ⟨⟨i, ((1 - a : ZMod (Γ.comp i).k) : ZMod (Γ.reverseShadow.comp i).k)⟩, ?_⟩
  rw [reverseMap_toFun]
  change (⟨i, 1 - (1 - a)⟩ : Γ.Strand) = ⟨i, a⟩
  rw [sub_sub_cancel]

/-- Crossings of the reversed shadow correspond bijectively to crossings of the shadow. -/
def reverseCrossingEquiv : Γ.reverseShadow.Crossing ≃ Γ.Crossing :=
  Γ.reverseMap.crossingEquiv Γ.reverseMap_surjective

@[simp] theorem reverseCrossingEquiv_apply (x : Γ.reverseShadow.Crossing) :
    Γ.reverseCrossingEquiv x = Γ.reverseMap.mapCrossing x := rfl

end Shadow

namespace Diagram

variable (D : Diagram)

/-- The diagram with every component reversed (cf:thm-carrierfloor (R): "reversing the orientation
of every component"), keeping the over data at every crossing. -/
def reverse : Diagram :=
  D.pullback D.Γ.reverseMap fun i => regular_reversal_forward (D.generic.regular i)

theorem reverse_componentCount : D.reverse.componentCount = D.componentCount := rfl

/-- Sanity: reversing all components preserves every crossing sign (both directions flip). -/
theorem reverse_sign (x : D.Γ.reverseShadow.Crossing) :
    D.reverse.sign x = D.sign (D.Γ.reverseCrossingEquiv x) := by
  have h := pullback_sign D D.Γ.reverseMap
    (fun i => regular_reversal_forward (D.generic.regular i)) x
  rw [Shadow.reverseMap_sgn, one_mul] at h
  rw [Shadow.reverseCrossingEquiv_apply]
  exact h

theorem reverse_writhe : D.reverse.writhe = D.writhe := by
  have h := pullback_writhe D D.Γ.reverseMap
    (fun i => regular_reversal_forward (D.generic.regular i)) D.Γ.reverseMap_surjective
  rw [Shadow.reverseMap_sgn, SignType.coe_one, one_mul] at h
  exact h

end Diagram

/-! ## Mirror image (the mirror paragraph of cf:thm-carrierfloor) -/

/-- Reflection of the plane in the first axis, `(x, y) ↦ (x, -y)`. -/
def reflect (p : Plane) : Plane := (p.1, -p.2)

@[simp] theorem reflect_reflect (p : Plane) : reflect (reflect p) = p := by
  simp [reflect]

theorem reflect_involutive : Function.Involutive reflect := reflect_reflect

theorem reflect_injective : Function.Injective reflect := reflect_involutive.injective

theorem reflect_sub (u v : Plane) : reflect (u - v) = reflect u - reflect v := by
  simp [reflect, Prod.ext_iff]; ring

theorem reflect_add (u v : Plane) : reflect (u + v) = reflect u + reflect v := by
  simp [reflect, Prod.ext_iff]; ring

theorem reflect_smul (t : ℝ) (u : Plane) : reflect (t • u) = t • reflect u := by
  simp [reflect]

theorem reflect_eq_zero_iff (u : Plane) : reflect u = 0 ↔ u = 0 := by
  simp [reflect, Prod.ext_iff]

theorem det_reflect (u v : Plane) : det (reflect u) (reflect v) = -det u v := by
  simp [reflect, det]; ring

theorem reflect_image_reflect (S : Set Plane) : reflect '' (reflect '' S) = S := by
  rw [Set.image_image]
  simp

theorem edge_reflect {n : ℕ} (P : LabelledTuple n) (i : ZMod n) :
    edge (reflect ∘ P) i = reflect (edge P i) := by
  simp [edge, reflect_sub]

theorem edgePoint_reflect {n : ℕ} (P : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    edgePoint (reflect ∘ P) i t = reflect (edgePoint P i t) := by
  simp [edgePoint, edge_reflect, reflect_add, reflect_smul]

theorem edgeSegment_reflect {n : ℕ} (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment (reflect ∘ P) i = reflect '' edgeSegment P i := by
  ext p
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨edgePoint P i t, ⟨t, ht0, ht1, rfl⟩, (edgePoint_reflect P i t).symm⟩
  · rintro ⟨q, ⟨t, ht0, ht1, rfl⟩, rfl⟩
    exact ⟨t, ht0, ht1, (edgePoint_reflect P i t).symm⟩

theorem edgeInterior_reflect {n : ℕ} (P : LabelledTuple n) (i : ZMod n) :
    edgeInterior (reflect ∘ P) i = reflect '' edgeInterior P i := by
  ext p
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨edgePoint P i t, ⟨t, ht0, ht1, rfl⟩, (edgePoint_reflect P i t).symm⟩
  · rintro ⟨q, ⟨t, ht0, ht1, rfl⟩, rfl⟩
    exact ⟨t, ht0, ht1, (edgePoint_reflect P i t).symm⟩

theorem regularPair_reflect {u v : Plane} (h : RegularPair u v) :
    RegularPair (reflect u) (reflect v) := by
  obtain ⟨hu, hv, hneg⟩ := h
  refine ⟨fun h => hu ((reflect_eq_zero_iff u).mp h), fun h => hv ((reflect_eq_zero_iff v).mp h), ?_⟩
  rintro ⟨r, hr, hrv⟩
  apply hneg
  refine ⟨r, hr, ?_⟩
  rw [← reflect_reflect v, hrv, ← reflect_smul, reflect_reflect]

theorem regular_reflect {n : ℕ} {P : LabelledTuple n} (h : Regular P) : Regular (reflect ∘ P) := by
  intro i
  rw [edge_reflect, edge_reflect]
  exact regularPair_reflect (h i)

/-- The mirror image of a component: every vertex reflected. -/
abbrev PolyComp.mirror (C : PolyComp) : PolyComp := ⟨C.k, C.hk, reflect ∘ C.P⟩

namespace Shadow

variable (Γ : Shadow)

/-- The shadow with every component reflected. -/
abbrev mirrorShadow : Shadow := ⟨Γ.c, Γ.hc, fun i => (Γ.comp i).mirror⟩

/-- The strand relabelling of the mirror image: strands keep their labels, the plane map is the
reflection, and every determinant changes sign. -/
def mirrorMap : StrandMap Γ.mirrorShadow Γ where
  toFun := fun s => ⟨s.1, s.2⟩
  inj := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    dsimp only at h
    exact h
  f := reflect
  f_inj := reflect_injective
  seg_eq := fun s => by
    change edgeSegment (Γ.comp s.1).P s.2 = reflect '' edgeSegment (reflect ∘ (Γ.comp s.1).P) s.2
    rw [edgeSegment_reflect, reflect_image_reflect]
  interior_eq := fun s => by
    change edgeInterior (Γ.comp s.1).P s.2 = reflect '' edgeInterior (reflect ∘ (Γ.comp s.1).P) s.2
    rw [edgeInterior_reflect, reflect_image_reflect]
  vert := fun s => ⟨s.1, s.2⟩
  tail_eq := fun s => by
    change (Γ.comp s.1).P s.2 = reflect (reflect ((Γ.comp s.1).P s.2))
    rw [reflect_reflect]
  adjacent_iff := fun s t => Iff.rfl
  incidentTail_iff := fun s t => Iff.rfl
  sgn := -1
  sgn_ne := by decide
  det_eq := fun s t => by
    change det (edge (Γ.comp s.1).P s.2) (edge (Γ.comp t.1).P t.2) =
      ((-1 : SignType) : ℝ) * det (edge (reflect ∘ (Γ.comp s.1).P) s.2)
        (edge (reflect ∘ (Γ.comp t.1).P) t.2)
    rw [edge_reflect, edge_reflect, det_reflect, SignType.coe_neg_one]
    ring

@[simp] theorem mirrorMap_sgn : (Γ.mirrorMap).sgn = -1 := rfl

theorem mirrorMap_surjective : Function.Surjective (Γ.mirrorMap).toFun := by
  rintro ⟨i, a⟩
  exact ⟨⟨i, a⟩, rfl⟩

/-- Crossings of the mirror shadow are the crossings of the shadow (same strand pairs). -/
def mirrorCrossingEquiv : Γ.mirrorShadow.Crossing ≃ Γ.Crossing :=
  Γ.mirrorMap.crossingEquiv Γ.mirrorMap_surjective

@[simp] theorem mirrorCrossingEquiv_apply (x : Γ.mirrorShadow.Crossing) :
    Γ.mirrorCrossingEquiv x = Γ.mirrorMap.mapCrossing x := rfl

theorem mirrorCrossingEquiv_val (x : Γ.mirrorShadow.Crossing) :
    (Γ.mirrorCrossingEquiv x).val = x.val := by
  ext s
  change s ∈ x.val.map Γ.mirrorMap.emb ↔ s ∈ x.val
  rw [Finset.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hs
    exact ⟨s, hs, rfl⟩

end Shadow

namespace Diagram

variable (D : Diagram)

/-- The mirror image of a diagram (the mirror paragraph of cf:thm-carrierfloor): every component
reflected in the first axis, over data kept at every crossing. -/
def mirror : Diagram :=
  D.pullback D.Γ.mirrorMap fun i => regular_reflect (D.generic.regular i)

theorem mirror_componentCount : D.mirror.componentCount = D.componentCount := rfl

/-- Sanity: the mirror image negates every crossing sign. -/
theorem mirror_sign (x : D.Γ.mirrorShadow.Crossing) :
    D.mirror.sign x = -D.sign (D.Γ.mirrorCrossingEquiv x) := by
  have h := pullback_sign D D.Γ.mirrorMap (fun i => regular_reflect (D.generic.regular i)) x
  rw [Shadow.mirrorMap_sgn, neg_one_mul] at h
  rw [Shadow.mirrorCrossingEquiv_apply]
  exact h

theorem mirror_isPositive_iff (x : D.Γ.mirrorShadow.Crossing) :
    D.mirror.IsPositive x ↔ ¬ D.IsPositive (D.Γ.mirrorCrossingEquiv x) := by
  rw [D.mirror.isPositive_iff_sign_eq_one x, mirror_sign, neg_eq_iff_eq_neg, D.sign_eq_neg_one_iff]

/-- Sanity: the mirror image negates the writhe. -/
theorem mirror_writhe : D.mirror.writhe = -D.writhe := by
  have h := pullback_writhe D D.Γ.mirrorMap (fun i => regular_reflect (D.generic.regular i))
    D.Γ.mirrorMap_surjective
  rw [Shadow.mirrorMap_sgn, SignType.coe_neg_one, neg_one_mul] at h
  exact h

end Diagram

/-! ## Occurrences as traversal points; based orders and UNDER-first (lp:lm) -/

namespace Diagram

variable (D : Diagram)

/-- The edge parameter at which the strand `s` of the crossing `x` passes through the crossing
point. -/
def crossingParam (x : D.Γ.Crossing) {s : D.Γ.Strand} (hs : s ∈ x.val) : ℝ :=
  Classical.choose (D.Γ.crossingPoint_mem x hs)

theorem crossingParam_spec (x : D.Γ.Crossing) {s : D.Γ.Strand} (hs : s ∈ x.val) :
    0 ≤ D.crossingParam x hs ∧ D.crossingParam x hs ≤ 1 ∧
      D.Γ.crossingPoint x = edgePoint (D.Γ.comp s.1).P s.2 (D.crossingParam x hs) :=
  Classical.choose_spec (D.Γ.crossingPoint_mem x hs)

theorem crossingParam_pos (x : D.Γ.Crossing) {s : D.Γ.Strand} (hs : s ∈ x.val) :
    0 < D.crossingParam x hs :=
  (D.generic.crossingPoint_param x hs (D.crossingParam_spec x hs).2.2 (D.crossingParam_spec x hs).1
    (D.crossingParam_spec x hs).2.1).1

theorem crossingParam_lt_one (x : D.Γ.Crossing) {s : D.Γ.Strand} (hs : s ∈ x.val) :
    D.crossingParam x hs < 1 :=
  (D.generic.crossingPoint_param x hs (D.crossingParam_spec x hs).2.2 (D.crossingParam_spec x hs).1
    (D.crossingParam_spec x hs).2.1).2

/-- The traversal point of an occurrence: the component of its strand, the edge label of its strand
and the crossing parameter on that edge (strictly inside `(0,1)` by genericity, so a valid accepted
`TraversalPoint`).  This is the position at which the traversal of the component "encounters" the
crossing (lp:lm, sm-3:947-949). -/
def visitPt (v : D.Γ.Visit) : D.Γ.Pt :=
  ⟨v.2.val.1, (v.2.val.2, ⟨D.crossingParam v.1 v.2.2, (D.crossingParam_pos v.1 v.2.2).le,
    D.crossingParam_lt_one v.1 v.2.2⟩)⟩

@[simp] theorem visitPt_fst (v : D.Γ.Visit) : (D.visitPt v).1 = v.2.val.1 := rfl

@[simp] theorem visitPt_edge (v : D.Γ.Visit) : (D.visitPt v).2.1 = v.2.val.2 := rfl

theorem visitPt_param (v : D.Γ.Visit) : (D.visitPt v).2.2.val = D.crossingParam v.1 v.2.2 := rfl

theorem visitPt_param_pos (v : D.Γ.Visit) : 0 < (D.visitPt v).2.2.val :=
  D.crossingParam_pos v.1 v.2.2

/-- The traversal point of an occurrence evaluates to the crossing point. -/
theorem eval_visitPt (v : D.Γ.Visit) : D.Γ.eval (D.visitPt v) = D.Γ.crossingPoint v.1 :=
  (D.crossingParam_spec v.1 v.2.2).2.2.symm

/-- Distinct occurrences have distinct traversal points (generic diagram). -/
theorem visitPt_injective : Function.Injective D.visitPt := by
  intro v w h
  have hpt : D.Γ.crossingPoint v.1 = D.Γ.crossingPoint w.1 := by
    rw [← D.eval_visitPt v, ← D.eval_visitPt w, h]
  have hx : v.1 = w.1 := D.generic.crossingPoint_injective hpt
  obtain ⟨x, s, hs⟩ := v
  obtain ⟨y, t, ht⟩ := w
  dsimp only at hx
  subst hx
  have hst : s = t := by
    obtain ⟨i, a⟩ := s
    obtain ⟨j, b⟩ := t
    have h1 : (⟨i, (a, _)⟩ : D.Γ.Pt) = ⟨j, (b, _)⟩ := h
    rw [Sigma.mk.inj_iff] at h1
    obtain ⟨rfl, h2⟩ := h1
    have h3 : a = b := congrArg Prod.fst (eq_of_heq h2)
    rw [h3]
  subst hst
  rfl

/-- lp:lm (sm-3:939-940, 946-949): the auxiliary data of a *based ordered* diagram — a component
order ("traversing components in their order": a rank bijection of the components) and
"nonsingular basepoints" (a traversal point on each component whose plane point is no crossing
point). -/
structure Basing where
  /-- the auxiliary component order: `rank i` is the position of component `i` -/
  rank : Fin D.Γ.c ≃ Fin D.Γ.c
  /-- the basepoint of each component, as a traversal point -/
  base : ∀ i : Fin D.Γ.c, TraversalPoint (D.Γ.comp i).k
  /-- "nonsingular": no basepoint is a crossing point -/
  nonsingular : ∀ i (x : D.Γ.Crossing), D.Γ.eval ⟨i, base i⟩ ≠ D.Γ.crossingPoint x

/-- The forward traversal distance from `a` to `b` on a circle of circumference `k` whose points are
parametrized by `[0, k)`: `b - a` if `a ≤ b`, else `b - a + k`. -/
def cyclicOffset (k : ℕ) (a b : ℝ) : ℝ := if a ≤ b then b - a else b - a + k

theorem cyclicOffset_self (k : ℕ) (a : ℝ) : cyclicOffset k a a = 0 := by
  simp [cyclicOffset]

theorem cyclicOffset_of_le (k : ℕ) {a b : ℝ} (h : a ≤ b) : cyclicOffset k a b = b - a := by
  simp [cyclicOffset, h]

theorem cyclicOffset_of_lt (k : ℕ) {a b : ℝ} (h : b < a) : cyclicOffset k a b = b - a + k := by
  simp [cyclicOffset, not_le.mpr h]

theorem cyclicOffset_nonneg {k : ℕ} {a b : ℝ} (ha : a < k) (hb : 0 ≤ b) :
    0 ≤ cyclicOffset k a b := by
  unfold cyclicOffset
  split_ifs with h
  · linarith
  · linarith

theorem cyclicOffset_lt {k : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : b < k) : cyclicOffset k a b < k := by
  unfold cyclicOffset
  split_ifs with h
  · linarith
  · have := not_le.mp h
    linarith

theorem traversalKey_nonneg {n : ℕ} (p : TraversalPoint n) : 0 ≤ traversalKey p :=
  add_nonneg (Nat.cast_nonneg _) p.2.2.1

theorem traversalKey_lt_card {n : ℕ} [NeZero n] (p : TraversalPoint n) : traversalKey p < n := by
  unfold traversalKey
  have h1 := p.2.2.2
  have h2 : (p.1.val : ℝ) + 1 ≤ n := by exact_mod_cast ZMod.val_lt p.1
  linarith

/-- lp:lm's based rank of an occurrence: the rank of its component in the auxiliary order, then the
traversal offset from that component's basepoint to the occurrence along the orientation (modulo
the length `k` of the parameter circle).  Lexicographic comparison of these pairs is the traversal
order "components in their order, from their basepoints and in their orientations"
(sm-3:947-949). -/
def basedRank (B : D.Basing) (v : D.Γ.Visit) : ℕ × ℝ :=
  (B.rank (D.visitPt v).1,
    cyclicOffset (D.Γ.comp (D.visitPt v).1).k (traversalKey (B.base (D.visitPt v).1))
      (traversalKey (D.visitPt v).2))

theorem basedRank_fst (B : D.Basing) (v : D.Γ.Visit) :
    (D.basedRank B v).1 = B.rank (D.visitPt v).1 := rfl

theorem basedRank_snd_nonneg (B : D.Basing) (v : D.Γ.Visit) : 0 ≤ (D.basedRank B v).2 :=
  cyclicOffset_nonneg (traversalKey_lt_card _) (traversalKey_nonneg _)

theorem basedRank_snd_lt (B : D.Basing) (v : D.Γ.Visit) :
    (D.basedRank B v).2 < (D.Γ.comp (D.visitPt v).1).k :=
  cyclicOffset_lt (traversalKey_nonneg _) (traversalKey_lt_card _)

/-- lp:lm (sm-3:947-949): "UNDER-first means that, traversing components in their order, from their
basepoints and in their orientations, the first encounter with each crossing is the underpass": for
every crossing the under occurrence strictly precedes the over occurrence in the lexicographic
based order (component rank first, then offset from the basepoint). -/
def UnderFirst (B : D.Basing) : Prop :=
  ∀ x, Prod.Lex (· < ·) (· < ·) (D.basedRank B (D.underVisit x)) (D.basedRank B (D.overVisit x))

/-- lp:lm (sm-3:949-951): "every crossing-free c-component diagram has that value, regardless of
nesting or orientations" — a crossing-free diagram is UNDER-first for every basing. -/
theorem underFirst_of_isEmpty (h : IsEmpty D.Γ.Crossing) (B : D.Basing) : D.UnderFirst B :=
  fun x => h.elim x

theorem IsCrossingFreeCircle.underFirst (h : D.IsCrossingFreeCircle) (B : D.Basing) :
    D.UnderFirst B :=
  D.underFirst_of_isEmpty h.2 B

/-- Nonsingular basepoints exist on every component: finitely many crossing points, infinitely many
points on the (nondegenerate) first edge. -/
theorem exists_nonsingular_base (i : Fin D.Γ.c) :
    ∃ p : TraversalPoint (D.Γ.comp i).k, ∀ x, D.Γ.eval ⟨i, p⟩ ≠ D.Γ.crossingPoint x := by
  have hinf : (Set.Ico (0 : ℝ) 1).Infinite := Set.Ico_infinite zero_lt_one
  have hedge : edge (D.Γ.comp i).P 0 ≠ 0 :=
    ((regular_iff_edges _).mp (D.generic.regular i) 0).1
  have hfin : ((fun t : ℝ => edgePoint (D.Γ.comp i).P 0 t) ⁻¹' Set.range D.Γ.crossingPoint).Finite :=
    (Set.finite_range _).preimage (edgePoint_injective hedge).injOn
  obtain ⟨t, ht, hnot⟩ := (hinf.sdiff hfin).nonempty
  refine ⟨(0, ⟨t, ht⟩), fun x hx => hnot ⟨x, hx.symm⟩⟩

/-- Every diagram admits a basing (identity order, chosen nonsingular basepoints). -/
theorem exists_basing : Nonempty D.Basing :=
  ⟨{ rank := Equiv.refl _
     base := fun i => Classical.choose (D.exists_nonsingular_base i)
     nonsingular := fun i => Classical.choose_spec (D.exists_nonsingular_base i) }⟩

/-- An occurrence never sits at a basepoint. -/
theorem visitPt_ne_base (B : D.Basing) (v : D.Γ.Visit) (i : Fin D.Γ.c) :
    D.visitPt v ≠ ⟨i, B.base i⟩ := by
  intro h
  apply B.nonsingular i v.1
  rw [← h, D.eval_visitPt]

end Diagram

/-! ## One-component shadows versus the accepted one-polygon crossings and visits -/

namespace Shadow

/-- The shadow with the single component `C`. -/
abbrev single (C : PolyComp) : Shadow := ⟨1, Nat.one_pos, fun _ => C⟩

variable (C : PolyComp)

/-- Strands of a one-component shadow are the edge labels of its polygon. -/
def singleStrandEquiv : (single C).Strand ≃ ZMod C.k where
  toFun s := s.2
  invFun a := ⟨0, a⟩
  left_inv := by
    rintro ⟨i, a⟩
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rfl
  right_inv := fun _ => rfl

@[simp] theorem singleStrandEquiv_apply (s : (single C).Strand) :
    singleStrandEquiv C s = s.2 := rfl

@[simp] theorem singleStrandEquiv_symm_apply (a : ZMod C.k) :
    (singleStrandEquiv C).symm a = ⟨0, a⟩ := rfl

@[simp] theorem single_strand_eta (s : (single C).Strand) : (⟨0, s.2⟩ : (single C).Strand) = s := by
  obtain ⟨i, a⟩ := s
  obtain rfl : i = 0 := Subsingleton.elim i 0
  rfl

theorem single_adjacent_iff (s t : (single C).Strand) :
    (single C).Adjacent s t ↔ adjacent (singleStrandEquiv C s) (singleStrandEquiv C t) := by
  obtain ⟨i, a⟩ := s
  obtain ⟨j, b⟩ := t
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  exact (single C).adjacent_mk_iff 0 a b

theorem single_incidentTail_iff (s t : (single C).Strand) :
    (single C).IncidentTail s t ↔ incident (singleStrandEquiv C s) (singleStrandEquiv C t) := by
  obtain ⟨i, a⟩ := s
  obtain ⟨j, b⟩ := t
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  exact (single C).incidentTail_mk_iff 0 a b

theorem single_seg (s : (single C).Strand) :
    (single C).seg s = edgeSegment C.P (singleStrandEquiv C s) := rfl

theorem single_interior (s : (single C).Strand) :
    (single C).interior s = edgeInterior C.P (singleStrandEquiv C s) := rfl

theorem single_dir (s : (single C).Strand) :
    (single C).dir s = edge C.P (singleStrandEquiv C s) := rfl

/-- Sanity: the crossings of a one-component shadow are exactly the accepted `SM.IsCrossing` pairs
of its polygon, under the strand/label identification. -/
theorem single_isCrossing_iff (x : Finset (single C).Strand) :
    (single C).IsCrossing x ↔ SM.IsCrossing C.P (x.map (singleStrandEquiv C).toEmbedding) := by
  constructor
  · rintro ⟨s, t, rfl, hna, hmeet⟩
    refine ⟨singleStrandEquiv C s, singleStrandEquiv C t, ?_, ?_, hmeet⟩
    · rw [Finset.map_insert, Finset.map_singleton]
      rfl
    · exact fun h => hna ((single_adjacent_iff C s t).mpr h)
  · rintro ⟨i, j, hx, hr, hmeet⟩
    refine ⟨(singleStrandEquiv C).symm i, (singleStrandEquiv C).symm j, ?_, ?_, ?_⟩
    · apply Finset.map_injective (singleStrandEquiv C).toEmbedding
      rw [hx, Finset.map_insert, Finset.map_singleton]
      simp
    · intro h
      apply hr
      simpa using (single_adjacent_iff C _ _).mp h
    · simpa [single_seg] using hmeet

/-- The crossings of a one-component shadow, identified with the accepted `SM.Crossing` of its
polygon. -/
def singleCrossingEquiv : (single C).Crossing ≃ SM.Crossing C.P where
  toFun x := ⟨x.val.map (singleStrandEquiv C).toEmbedding, (single_isCrossing_iff C x.val).mp x.2⟩
  invFun y := ⟨y.val.map (singleStrandEquiv C).symm.toEmbedding, by
    rw [single_isCrossing_iff]
    convert y.2 using 1
    ext a
    simp [Finset.mem_map_equiv]⟩
  left_inv x := by
    apply Subtype.ext
    ext s
    rw [Finset.mem_map_equiv, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    ext a
    simp [Finset.mem_map_equiv]

@[simp] theorem singleCrossingEquiv_val (x : (single C).Crossing) :
    (singleCrossingEquiv C x).val = x.val.map (singleStrandEquiv C).toEmbedding := rfl

theorem mem_singleCrossingEquiv_iff (x : (single C).Crossing) (s : (single C).Strand) :
    singleStrandEquiv C s ∈ (singleCrossingEquiv C x).val ↔ s ∈ x.val :=
  Finset.mem_map' _

/-- The occurrences of a one-component shadow, identified with the accepted `SM.Visit`. -/
def singleVisitEquiv : (single C).Visit ≃ SM.Visit C.P :=
  Equiv.sigmaCongr (singleCrossingEquiv C) fun x =>
    Equiv.subtypeEquiv (singleStrandEquiv C) fun s => (mem_singleCrossingEquiv_iff C x s).symm

theorem singleVisitEquiv_fst (v : (single C).Visit) :
    (singleVisitEquiv C v).1 = singleCrossingEquiv C v.1 := rfl

theorem singleVisitEquiv_snd (v : (single C).Visit) :
    (singleVisitEquiv C v).2.val = singleStrandEquiv C v.2.val := rfl

theorem card_single_crossing : Fintype.card (single C).Crossing = Fintype.card (SM.Crossing C.P) :=
  Fintype.card_congr (singleCrossingEquiv C)

/-- Two occurrences per crossing (the accepted `card_visit`). -/
theorem card_single_visit : Fintype.card (single C).Visit = 2 * (crossingSet C.P).card := by
  rw [Fintype.card_congr (singleVisitEquiv C), card_visit]

/-- For a generic one-component shadow the crossing point is the accepted `SM.crossingPoint`. -/
theorem single_crossingPoint (hΓ : (single C).Generic) (x : (single C).Crossing) :
    (single C).crossingPoint x = SM.crossingPoint (singleCrossingEquiv C x) := by
  symm
  apply hΓ.common_point_unique
  intro s hs
  rw [single_seg]
  exact SM.crossingPoint_mem (singleCrossingEquiv C x) _
    ((mem_singleCrossingEquiv_iff C x s).mpr hs)

/-- A polygon generic in the accepted sense (def:generic, `G1 ∧ G2`) gives a generic one-component
shadow: regularity from `generic_regular`, `tail_off` from `g1_vertex_not_mem_edge`,
transversality from `g1_remote_meeting`, `no_triple` from `G2`. -/
theorem single_generic_of_generic {C : PolyComp} (hP : SM.Generic C.P) : (single C).Generic where
  regular := fun _ => generic_regular C.hk hP
  tail_off := by
    intro s t hinc hmem
    rw [single_incidentTail_iff] at hinc
    rw [single_seg] at hmem
    obtain ⟨i, a⟩ := s
    obtain ⟨j, b⟩ := t
    simp only [singleStrandEquiv_apply] at hinc hmem
    change C.P a ∈ edgeSegment C.P b at hmem
    have h1 : a ≠ b := fun h => hinc (Or.inr h.symm)
    have h2 : a ≠ b + 1 := fun h => hinc (Or.inl (by rw [h]; ring))
    exact g1_vertex_not_mem_edge hP.1 b a (next_ne_self b).symm h1 h2 hmem
  transverse := by
    intro s t hna hmeet
    rw [single_adjacent_iff] at hna
    obtain ⟨p, hps, hpt⟩ := hmeet
    rw [single_seg] at hps hpt
    rw [single_dir, single_dir]
    exact (g1_remote_meeting hP.1 hna hps hpt).2.2.1
  no_triple := by
    rintro ⟨s, t, u, hst, htu, hsu, p, ⟨hps, hpt⟩, hpu⟩
    apply hP.2
    refine ⟨singleStrandEquiv C s, singleStrandEquiv C t, singleStrandEquiv C u,
      p, ?_, ?_, ?_, hps, hpt, hpu⟩
    · exact fun h => hst ((singleStrandEquiv C).injective h)
    · exact fun h => htu ((singleStrandEquiv C).injective h)
    · exact fun h => hsu ((singleStrandEquiv C).injective h)

end Shadow

/-! ## Axiom audit -/

end

end SM.Link

