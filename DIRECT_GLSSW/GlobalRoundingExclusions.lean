import SmallRoundingFraction

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- An actual small cutoff simultaneously excludes intersections between
corners at different vertices and between a corner and any nonincident
closed original arc. No neighborhood certificate is a hypothesis. -/
theorem exists_rounding_global_exclusions (D : PLLinkDiagram) (base : Fin D.nArc)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 1) :
    ∃ δ : RoundingFraction, δ.val < τ ∧ δ.val < 1 - τ ∧
      (∀ e f : Fin D.nArc, ∀ s t : ℝ,
        D.arcTarget e ≠ D.arcTarget f → s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
        Complex.equivRealProd (roundedCorner D e δ.val s) ≠
          Complex.equivRealProd (roundedCorner D f δ.val t)) ∧
      (∀ e f : Fin D.nArc, ∀ s t : ℝ,
        D.arcSource f ≠ D.arcTarget e → D.arcTarget f ≠ D.arcTarget e →
        s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
        Complex.equivRealProd (roundedCorner D e δ.val s) ≠
          affinePoint (D.vertexPoint (D.arcSource f)) (D.vertexPoint (D.arcTarget f)) t) := by
  let b := affinePoint (D.vertexPoint (D.arcSource base))
    (D.vertexPoint (D.arcTarget base)) τ
  have hb : ∀ v, D.vertexPoint v ≠ b := interior_basepoint_nonvertex D base τ hτ
  obtain ⟨r,hr,hclear,hdisjoint⟩ := exists_common_vertex_radius D b hb
  obtain ⟨δ,hdleft,hdright,hsmall⟩ := exists_small_rounding_fraction D r τ hr hτ
  refine ⟨δ,hdleft,hdright,?_,?_⟩
  · intro e f s t hef hs ht heq
    have hx : Complex.equivRealProd (roundedCorner D e δ.val s) ∈
        Metric.ball (D.vertexPoint (D.arcTarget e)) r := hsmall e s hs
    have hy : Complex.equivRealProd (roundedCorner D e δ.val s) ∈
        Metric.ball (D.vertexPoint (D.arcTarget f)) r := by
      rw [heq]
      exact hsmall f t ht
    exact Set.disjoint_left.mp (hdisjoint _ _ hef) hx hy
  · intro e f s t hsource htarget hs ht
    have hnear : dist (Complex.equivRealProd (roundedCorner D e δ.val s))
        (D.vertexPoint (D.arcTarget e)) < 3 * r := by
      have h := hsmall e s hs
      linarith
    exact (hclear (D.arcTarget e) _ hnear).2.2 f hsource htarget t ht

end DirectGLSSW.HOMFLY.PrincipalTurning

