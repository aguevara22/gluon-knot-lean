import SourcePolygonMinimumSize

set_option autoImplicit false
namespace DirectGLSSW.SourcePolygonData
open DirectGLSSW.HOMFLY.PolygonDrawingBridge

/-- On the admitted immersed domain, the stored cardinality condition is a
derived consequence. Thus the generic locus is exactly G1 and G2. -/
theorem generic_locus_iff_G1_G2 {n : ℕ} (hn : 0 < n)
    (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane) :
    CyclicGeneric q ↔ cyclicNoncollinear q ∧ cyclicNoTripleIntersections q := by
  constructor
  · intro hq
    exact ⟨hq.g1,hq.g2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨immersed_polygon_size_ge_three hn q hedge hshort,h1,h2⟩

/-- G1 is the literal noncollinearity determinant for every three distinct
labels; this equation does not introduce a substitute generic predicate. -/
theorem G1_literal {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    cyclicNoncollinear q ↔ ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
      planarDet (q b-q c) (q a-q c) ≠ 0 := Iff.rfl

/-- G2 is literally absence of a common point in three distinct open edges. -/
theorem G2_literal {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    cyclicNoTripleIntersections q ↔ ∀ (e f g : Fin n) (x : PlanarPoint ℝ),
      e ≠ f → f ≠ g → e ≠ g →
        ¬ (OnOpenSegment (q e) (q (cyclicSuccessor e)) x ∧
           OnOpenSegment (q f) (q (cyclicSuccessor f)) x ∧
           OnOpenSegment (q g) (q (cyclicSuccessor g)) x) := Iff.rfl

theorem generic_vertices_injective {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) : Function.Injective q :=
  cyclicNoncollinear_injective hq.size_ge_three q hq.g1

theorem generic_incoming_turn_det_ne_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (i : Fin n) :
    planarDet (cyclicTangent q ((cyclicSuccessorPerm n).symm i)) (cyclicTangent q i) ≠ 0 := by
  have h := cyclic_turn_det_ne_zero hq.size_ge_three q hq.g1 ((cyclicSuccessorPerm n).symm i)
  have hs : cyclicSuccessor ((cyclicSuccessorPerm n).symm i) = i :=
    Equiv.apply_symm_apply (cyclicSuccessorPerm n) i
  simpa only [hs] using h

/-- At an actual intersection of two distinct labelled edge interiors, the
tangent determinant is nonzero. Transversality is concluded, not assumed. -/
theorem generic_crossing_transverse {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e f : Fin n) (hef : e ≠ f) (x : PlanarPoint ℝ)
    (he : edgeInterior q e x) (hf : edgeInterior q f x) :
    planarDet (cyclicTangent q e) (cyclicTangent q f) ≠ 0 :=
  cyclicTangent_det_ne_zero_of_intersection hq.size_ge_three q hq.g1 e f hef x he hf

/-- Every edge through that crossing is one of the two actual branches. -/
theorem generic_crossing_exactly_two_edges {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e f : Fin n) (hef : e ≠ f) (x : PlanarPoint ℝ)
    (he : edgeInterior q e x) (hf : edgeInterior q f x) :
    ∀ g : Fin n, edgeInterior q g x ↔ g=e ∨ g=f := by
  intro g
  constructor
  · intro hg
    by_cases hge : g=e
    · exact Or.inl hge
    · by_cases hgf : g=f
      · exact Or.inr hgf
      · exact (hq.g2 e f g x hef (Ne.symm hgf) (Ne.symm hge) ⟨he,hf,hg⟩).elim
  · rintro (rfl | rfl)
    · exact he
    · exact hf

/-- A nonincident vertex is excluded even from the whole edge carrier line;
in particular it cannot lie anywhere on the closed nonincident edge. -/
theorem generic_nonincident_vertex_avoids_carrier {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e v : Fin n) (hve : v ≠ e)
    (hvs : v ≠ cyclicSuccessor e) (t : ℝ) :
    q v ≠ affinePoint (q e) (q (cyclicSuccessor e)) t := by
  intro h
  apply cyclic_vertex_carrier_det_ne_zero hq.size_ge_three q hq.g1 e v hve hvs
  rw [h]
  exact affinePoint_carrier_det_zero _ _ _

end DirectGLSSW.SourcePolygonData








