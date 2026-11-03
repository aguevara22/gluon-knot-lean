import DirectGLSSW.CyclicWords
import DirectGLSSW.AffineSegments

/-!
# Concrete cyclic G1–G2 polygon geometry

Source: Section 1, lines 61–100 of the frozen note. Edges are actual open
segments between cyclically consecutive vertices, and G2 excludes a common
point of three distinct labelled edge interiors. The generic polygon
predicate has exactly size at least three, G1 and G2 as its fields.

These ordered-field prerequisites do not narrow the final real-plane target.
Transversality and vertex exclusion are proved from G1 rather than assumed.
-/

namespace DirectGLSSW

/-- The next labelled vertex in the polygon's given orientation. -/
def cyclicSuccessor {n : ℕ} (e : Fin n) : Fin n := cyclicVertexIndex e 0

/-- Moving forward once permutes the original vertex labels. -/
theorem cyclicSuccessor_bijective {n : ℕ} :
    Function.Bijective (cyclicSuccessor (n := n)) := by
  apply Finite.injective_iff_bijective.mp
  intro a b h
  have hv := congrArg Fin.val h
  have hn : 0 < n := by have := a.isLt; omega
  simp only [cyclicSuccessor, cyclicVertexIndex_val _ hn] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

/-- A polygon with at least two labels has no successor fixed point. -/
theorem cyclicSuccessor_ne_self {n : ℕ} (hn : 2 ≤ n) (e : Fin n) :
    cyclicSuccessor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  have hn' : 0 < n := by omega
  simp only [cyclicSuccessor, cyclicVertexIndex_val _ hn'] at hv
  split_ifs at hv <;> have := e.isLt <;> omega

/-- Three or more labels prevent a two-step return to the starting label. -/
theorem cyclicSuccessor_twice_ne_self {n : ℕ} (hn : 3 ≤ n) (e : Fin n) :
    cyclicSuccessor (cyclicSuccessor e) ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  have hn' : 0 < n := by omega
  simp only [cyclicSuccessor, cyclicVertexIndex_val _ hn'] at hv
  split_ifs at hv <;> have := e.isLt <;> omega

/-- The actual directed edge vector at the labelled polygon edge. -/
def cyclicTangent {K : Type*} [CommRing K] {n : ℕ}
    (q : Fin n → PlanarPoint K) (e : Fin n) : PlanarPoint K :=
  q (cyclicSuccessor e) - q e

/-- G1 forces every directed polygon edge to have distinct endpoints. -/
theorem cyclicTangent_ne_zero {K : Type*} [CommRing K] {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint K) (hq : cyclicNoncollinear q)
    (e : Fin n) : cyclicTangent q e ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  exact cyclicSuccessor_ne_self (by omega) e (cyclicNoncollinear_injective hn q hq h)

/-- G1 excludes a third vertex from the whole carrier line of an edge. -/
theorem cyclic_vertex_carrier_det_ne_zero {K : Type*} [CommRing K] {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint K) (hq : cyclicNoncollinear q)
    (e v : Fin n) (hve : v ≠ e) (hvs : v ≠ cyclicSuccessor e) :
    planarDet (cyclicTangent q e) (q v - q e) ≠ 0 := by
  exact hq v (cyclicSuccessor e) e hvs (cyclicSuccessor_ne_self (by omega) e) hve

/-- The Cartesian determinant of consecutive polygon tangents is nonzero by G1. -/
theorem cyclic_turn_det_ne_zero {K : Type*} [CommRing K] {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint K) (hq : cyclicNoncollinear q)
    (e : Fin n) : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) ≠ 0 := by
  have h := cyclic_vertex_carrier_det_ne_zero hn q hq e
    (cyclicSuccessor (cyclicSuccessor e))
    (cyclicSuccessor_twice_ne_self hn e) (cyclicSuccessor_ne_self (by omega) _)
  have hid : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) =
      planarDet (cyclicTangent q e) (q (cyclicSuccessor (cyclicSuccessor e)) - q e) := by
    simp only [cyclicTangent, planarDet, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hid]
  exact h

/-- Membership in the actual relative interior of the labelled directed edge. -/
def edgeInterior {K : Type*} [Field K] [LinearOrder K] {n : ℕ}
    (q : Fin n → PlanarPoint K) (e : Fin n) (x : PlanarPoint K) : Prop :=
  OnOpenSegment (q e) (q (cyclicSuccessor e)) x

/-- G2: no point belongs to the interiors of three distinct labelled edges. -/
def cyclicNoTripleIntersections {K : Type*} [Field K] [LinearOrder K] {n : ℕ}
    (q : Fin n → PlanarPoint K) : Prop :=
  ∀ (e f g : Fin n) (x : PlanarPoint K), e ≠ f → f ≠ g → e ≠ g →
    ¬ (edgeInterior q e x ∧ edgeInterior q f x ∧ edgeInterior q g x)

/-- The concrete generic locus: at least three vertices, G1 and G2 only. -/
structure CyclicGeneric {K : Type*} [Field K] [LinearOrder K] {n : ℕ}
    (q : Fin n → PlanarPoint K) : Prop where
  size_ge_three : 3 ≤ n
  g1 : cyclicNoncollinear q
  g2 : cyclicNoTripleIntersections q

section OrderedGeometry

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
/-- No nonincident vertex lies in an edge interior; G1 excludes its carrier. -/
theorem cyclic_vertex_not_in_nonincident_edge {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint K) (hq : cyclicNoncollinear q)
    (e v : Fin n) (hve : v ≠ e) (hvs : v ≠ cyclicSuccessor e) :
    ¬ edgeInterior q e (q v) := by
  intro h
  exact cyclic_vertex_carrier_det_ne_zero hn q hq e v hve hvs
    (onOpenSegment_carrier_det_zero h)

/-- Two edges incident in succession have disjoint relative interiors. -/
theorem cyclic_adjacent_interiors_disjoint {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint K) (hq : cyclicNoncollinear q)
    (e : Fin n) (x : PlanarPoint K) (he : edgeInterior q e x) :
    ¬ edgeInterior q (cyclicSuccessor e) x := by
  have hdet : planarDet (q e - q (cyclicSuccessor e))
      (q (cyclicSuccessor (cyclicSuccessor e)) - q (cyclicSuccessor e)) ≠ 0 := by
    exact hq (cyclicSuccessor (cyclicSuccessor e)) e (cyclicSuccessor e)
      (cyclicSuccessor_twice_ne_self hn e)
      (Ne.symm (cyclicSuccessor_ne_self (by omega) e))
      (cyclicSuccessor_ne_self (by omega) _)
  exact onOpenSegment_common_origin_disjoint hdet (onOpenSegment_symm he)

omit [IsStrictOrderedRing K] in
/-- Any actual intersection of distinct edge interiors is transverse.
The nonparallel determinant is a consequence of G1, not an extra hypothesis. -/
theorem cyclicTangent_det_ne_zero_of_intersection {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint K) (hq : cyclicNoncollinear q)
    (e f : Fin n) (hef : e ≠ f) (x : PlanarPoint K)
    (he : edgeInterior q e x) (hf : edgeInterior q f x) :
    planarDet (cyclicTangent q e) (cyclicTangent q f) ≠ 0 := by
  by_cases hfs : f = cyclicSuccessor e
  · subst f
    exact cyclic_turn_det_ne_zero hn q hq e
  · intro hparallel
    obtain ⟨s, _, _, hs⟩ := he
    obtain ⟨t, _, _, ht⟩ := hf
    have hcol := affinePoint_parallel_collinear (q e) (q (cyclicSuccessor e))
      (q f) (q (cyclicSuccessor f)) s t (hs.symm.trans ht) hparallel
    exact cyclic_vertex_carrier_det_ne_zero hn q hq e f (Ne.symm hef) hfs hcol

/-- G2 is automatic for a G1 triangle because one of any other two edges
is the successor edge, whose interior is disjoint from the first. -/
theorem cyclicNoTripleIntersections_of_three
    (q : Fin 3 → PlanarPoint K) (hq : cyclicNoncollinear q) :
    cyclicNoTripleIntersections q := by
  intro e f g x hef hfg heg ⟨he, hf, hg⟩
  have hse := cyclicSuccessor_ne_self (by omega : 2 ≤ 3) e
  have hs : f = cyclicSuccessor e ∨ g = cyclicSuccessor e := by
    by_contra h
    push_neg at h
    have h1 := Fin.val_ne_iff.mpr hef
    have h2 := Fin.val_ne_iff.mpr hfg
    have h3 := Fin.val_ne_iff.mpr heg
    have h4 := Fin.val_ne_iff.mpr hse
    have h5 := Fin.val_ne_iff.mpr h.1
    have h6 := Fin.val_ne_iff.mpr h.2
    have hbound := (cyclicSuccessor e).isLt
    omega
  rcases hs with hs | hs
  · subst f
    exact cyclic_adjacent_interiors_disjoint (by omega) q hq e x he hf
  · subst g
    exact cyclic_adjacent_interiors_disjoint (by omega) q hq e x he hg

/-- The standard triangle satisfies the literal no-triple-intersection G2. -/
theorem standardTriangle_noTripleIntersections :
    cyclicNoTripleIntersections (standardTriangle (K := K)) :=
  cyclicNoTripleIntersections_of_three _ standardTriangle_noncollinear

/-- The concrete G1–G2 locus has a genuine ordered-field example. -/
theorem standardTriangle_generic : CyclicGeneric (standardTriangle (K := K)) :=
  ⟨by omega, standardTriangle_noncollinear, standardTriangle_noTripleIntersections⟩

end OrderedGeometry

end DirectGLSSW
