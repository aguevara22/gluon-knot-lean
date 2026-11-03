import DirectGLSSW.PolygonGeometry

/-!
# Actual polygon crossings and their positive orientation

Source: Section 1, G1–G2 and `eq:positive-diagram`. A crossing is an
intersecting pair of actual open edges, ordered once by its labels. Its point
and parameters are chosen from actual affine equations, then proved unique
using the transversality already derived from G1. G2 separates distinct
crossing points. No smoothing, diagram invariance or HOMFLY is asserted.
-/

namespace DirectGLSSW

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- An unordered pair of intersecting open polygon edges, represented once
by increasing labels. On G1–G2 this is the finite set of actual crossings. -/
def PolygonCrossing (q : Fin n → PlanarPoint K) :=
  {p : Fin n × Fin n // p.1 < p.2 ∧
    ∃ x : PlanarPoint K, edgeInterior q p.1 x ∧ edgeInterior q p.2 x}

noncomputable instance polygonCrossingFintype (q : Fin n → PlanarPoint K) :
    Fintype (PolygonCrossing q) := by
  classical
  unfold PolygonCrossing
  exact Fintype.ofFinite _

/-- A crossing's two edge labels are distinct. -/
theorem crossing_edges_ne (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) :
    c.val.1 ≠ c.val.2 := ne_of_lt c.property.1

/-- The actual point supplied by the open-segment intersection relation. -/
noncomputable def crossingPoint (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) :
    PlanarPoint K := Classical.choose c.property.2

theorem crossingPoint_mem_left (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) :
    edgeInterior q c.val.1 (crossingPoint q c) := (Classical.choose_spec c.property.2).1

theorem crossingPoint_mem_right (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) :
    edgeInterior q c.val.2 (crossingPoint q c) := (Classical.choose_spec c.property.2).2

/-- The two oriented visit parameters are taken from their affine equations. -/
noncomputable def crossingParameterLeft (q : Fin n → PlanarPoint K)
    (c : PolygonCrossing q) : K := Classical.choose (crossingPoint_mem_left q c)

noncomputable def crossingParameterRight (q : Fin n → PlanarPoint K)
    (c : PolygonCrossing q) : K := Classical.choose (crossingPoint_mem_right q c)

/-- The chosen parameters are strictly interior and give exactly the chosen point. -/
theorem crossingParameterLeft_spec (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) :
    0 < crossingParameterLeft q c ∧ crossingParameterLeft q c < 1 ∧
      crossingPoint q c = affinePoint (q c.val.1) (q (cyclicSuccessor c.val.1))
        (crossingParameterLeft q c) := Classical.choose_spec (crossingPoint_mem_left q c)

theorem crossingParameterRight_spec (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) :
    0 < crossingParameterRight q c ∧ crossingParameterRight q c < 1 ∧
      crossingPoint q c = affinePoint (q c.val.2) (q (cyclicSuccessor c.val.2))
        (crossingParameterRight q c) := Classical.choose_spec (crossingPoint_mem_right q c)

/-- G1 supplies the nonzero crossing determinant for the actual intersecting edges. -/
theorem crossing_transverse (hn : 3 ≤ n) (q : Fin n → PlanarPoint K)
    (hq : cyclicNoncollinear q) (c : PolygonCrossing q) :
    planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) ≠ 0 :=
  cyclicTangent_det_ne_zero_of_intersection hn q hq c.val.1 c.val.2
    (crossing_edges_ne q c) (crossingPoint q c)
    (crossingPoint_mem_left q c) (crossingPoint_mem_right q c)

/-- Any intersection parameters, even on the whole carriers, equal the
chosen interior parameters. No uniqueness is hidden in the crossing definition. -/
theorem crossingParameters_unique (hn : 3 ≤ n) (q : Fin n → PlanarPoint K)
    (hq : cyclicNoncollinear q) (c : PolygonCrossing q) (s t : K)
    (h : affinePoint (q c.val.1) (q (cyclicSuccessor c.val.1)) s =
      affinePoint (q c.val.2) (q (cyclicSuccessor c.val.2)) t) :
    s = crossingParameterLeft q c ∧ t = crossingParameterRight q c := by
  apply affinePoint_intersection_parameters_unique
    (q c.val.1) (q (cyclicSuccessor c.val.1))
    (q c.val.2) (q (cyclicSuccessor c.val.2)) s t
    (crossingParameterLeft q c) (crossingParameterRight q c)
    (crossing_transverse hn q hq c) h
  exact (crossingParameterLeft_spec q c).2.2.symm.trans
    (crossingParameterRight_spec q c).2.2

/-- Any point in both crossing edges is the represented crossing point. -/
theorem crossingPoint_eq_of_mem (hn : 3 ≤ n) (q : Fin n → PlanarPoint K)
    (hq : cyclicNoncollinear q) (c : PolygonCrossing q) (x : PlanarPoint K)
    (hl : edgeInterior q c.val.1 x) (hr : edgeInterior q c.val.2 x) :
    x = crossingPoint q c := by
  obtain ⟨s, _, _, hs⟩ := hl
  obtain ⟨t, _, _, ht⟩ := hr
  have hp := crossingParameters_unique hn q hq c s t (hs.symm.trans ht)
  rw [hp.1] at hs
  exact hs.trans (crossingParameterLeft_spec q c).2.2.symm

/-- G2 makes the finite edge-pair representation inject into actual plane points. -/
theorem crossingPoint_injective (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) : Function.Injective (crossingPoint q) := by
  intro c d hpoint
  have hcl := crossingPoint_mem_left q c
  have hcr := crossingPoint_mem_right q c
  have hdl : edgeInterior q d.val.1 (crossingPoint q c) := by
    rw [hpoint]; exact crossingPoint_mem_left q d
  have hdr : edgeInterior q d.val.2 (crossingPoint q c) := by
    rw [hpoint]; exact crossingPoint_mem_right q d
  have hl : d.val.1 = c.val.1 ∨ d.val.1 = c.val.2 := by
    by_contra h
    push_neg at h
    exact hq c.val.1 c.val.2 d.val.1 (crossingPoint q c)
      (crossing_edges_ne q c) (Ne.symm h.2) (Ne.symm h.1) ⟨hcl, hcr, hdl⟩
  have hr : d.val.2 = c.val.1 ∨ d.val.2 = c.val.2 := by
    by_contra h
    push_neg at h
    exact hq c.val.1 c.val.2 d.val.2 (crossingPoint q c)
      (crossing_edges_ne q c) (Ne.symm h.2) (Ne.symm h.1) ⟨hcl, hcr, hdr⟩
  apply Subtype.ext
  have hc := c.property.1
  have hd := d.property.1
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · exact False.elim (ne_of_lt hd (hl.trans hr.symm))
  · exact Prod.ext hl.symm hr.symm
  · have hcycle : c.val.2 < c.val.1 := by simpa [hl, hr] using hd
    exact False.elim (lt_asymm hc hcycle)
  · exact False.elim (ne_of_lt hd (hl.trans hr.symm))

/-- An actual crossing point is interior to two distinct labelled edges. -/
def IsCrossingPoint (q : Fin n → PlanarPoint K) (x : PlanarPoint K) : Prop :=
  ∃ e f : Fin n, e ≠ f ∧ edgeInterior q e x ∧ edgeInterior q f x

theorem isCrossingPoint_crossingPoint (q : Fin n → PlanarPoint K)
    (c : PolygonCrossing q) : IsCrossingPoint q (crossingPoint q c) :=
  ⟨c.val.1, c.val.2, crossing_edges_ne q c,
    crossingPoint_mem_left q c, crossingPoint_mem_right q c⟩

/-- Every actual crossing point is represented; no geometric crossing is
lost by ordering the finite pair of edge labels. -/
theorem isCrossingPoint_iff_exists (hn : 3 ≤ n) (q : Fin n → PlanarPoint K)
    (hq : cyclicNoncollinear q) (x : PlanarPoint K) :
    IsCrossingPoint q x ↔ ∃ c : PolygonCrossing q, crossingPoint q c = x := by
  constructor
  · rintro ⟨e, f, hef, he, hf⟩
    rcases lt_or_gt_of_ne hef with hlt | hgt
    · let c : PolygonCrossing q := ⟨(e, f), hlt, x, he, hf⟩
      exact ⟨c, (crossingPoint_eq_of_mem hn q hq c x he hf).symm⟩
    · let c : PolygonCrossing q := ⟨(f, e), hgt, x, hf, he⟩
      exact ⟨c, (crossingPoint_eq_of_mem hn q hq c x hf he).symm⟩
  · rintro ⟨c, rfl⟩
    exact isCrossingPoint_crossingPoint q c

/-- On exactly G1–G2, the finite edge-pair representation is equivalent to
the actual set of plane crossing points. -/
noncomputable def crossingPointEquiv (q : Fin n → PlanarPoint K)
    (hq : CyclicGeneric q) : PolygonCrossing q ≃ {x // IsCrossingPoint q x} :=
  Equiv.ofBijective
    (fun c => ⟨crossingPoint q c, isCrossingPoint_crossingPoint q c⟩)
    ⟨fun _ _ h => crossingPoint_injective q hq.g2 (congrArg Subtype.val h), by
      intro x
      obtain ⟨c, hc⟩ := (isCrossingPoint_iff_exists hq.size_ge_three q hq.g1 x.val).mp x.property
      exact ⟨c, Subtype.ext hc⟩⟩

/-- Finiteness of actual crossing points follows from the proved representation. -/
theorem crossingPoint_finite (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q) :
    Finite {x // IsCrossingPoint q x} := by
  letI := Fintype.ofEquiv (PolygonCrossing q) (crossingPointEquiv q hq)
  infer_instance

variable [IsStrictOrderedRing K]

/-- The two represented crossing edges are nonincident in either cyclic direction. -/
theorem crossing_nonincident (hn : 3 ≤ n) (q : Fin n → PlanarPoint K)
    (hq : cyclicNoncollinear q) (c : PolygonCrossing q) :
    c.val.2 ≠ cyclicSuccessor c.val.1 ∧ c.val.1 ≠ cyclicSuccessor c.val.2 := by
  constructor
  · intro h
    have hr := crossingPoint_mem_right q c
    rw [h] at hr
    exact cyclic_adjacent_interiors_disjoint hn q hq c.val.1 (crossingPoint q c)
      (crossingPoint_mem_left q c) hr
  · intro h
    have hl := crossingPoint_mem_left q c
    rw [h] at hl
    exact cyclic_adjacent_interiors_disjoint hn q hq c.val.2 (crossingPoint q c)
      (crossingPoint_mem_right q c) hl

/-- The positive diagram chooses its overstrand by the actual tangent determinant. -/
noncomputable def crossingOver (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) : Fin n :=
  if 0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)
    then c.val.1 else c.val.2

noncomputable def crossingUnder (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) : Fin n :=
  if 0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)
    then c.val.2 else c.val.1

omit [IsStrictOrderedRing K] in
/-- Over and under select the two different represented edges. -/
theorem crossingOver_ne_under (q : Fin n → PlanarPoint K) (c : PolygonCrossing q) :
    crossingOver q c ≠ crossingUnder q c := by
  unfold crossingOver crossingUnder
  split_ifs
  · exact crossing_edges_ne q c
  · exact Ne.symm (crossing_edges_ne q c)

/-- The convention is exactly positive determinant of over tangent then under tangent. -/
theorem crossing_positive (hn : 3 ≤ n) (q : Fin n → PlanarPoint K)
    (hq : cyclicNoncollinear q) (c : PolygonCrossing q) :
    0 < planarDet (cyclicTangent q (crossingOver q c))
      (cyclicTangent q (crossingUnder q c)) := by
  have hnz := crossing_transverse hn q hq c
  unfold crossingOver crossingUnder
  split_ifs with hp
  · exact hp
  · rw [planarDet_swap]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hnz)

end DirectGLSSW
