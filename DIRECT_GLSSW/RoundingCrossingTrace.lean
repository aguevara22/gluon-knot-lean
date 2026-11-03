import RoundingLocalInjectivity

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- The actual through condition gives positive collinearity of the literal
complex arc vectors, with the prescribed crossing continuation. -/
theorem crossing_arcVector_collinear (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) : ∃ a : ℝ, 0 < a ∧
      arcVector D (D.incoming c i) = a • arcVector D (D.continuation (D.incoming c i)) := by
  obtain ⟨a,ha,h⟩ := D.through_tangents_positive_collinear c i
  refine ⟨a,ha,?_⟩
  rw [D.continuation_crossing]
  apply Complex.ext
  · simpa [arcVector, D.incoming_target, D.outgoing_source, Complex.real_smul]
      using congrArg Prod.fst h
  · simpa [arcVector, D.incoming_target, D.outgoing_source, Complex.real_smul]
      using congrArg Prod.snd h

/-- Exact scalar range of a positively collinear quadratic rounding. -/
theorem crossing_quadratic_scalar_range (a : ℝ) (ha : 0 < a) :
    (fun t : ℝ => -a * (1 - t) ^ 2 + t ^ 2) '' Set.Icc 0 1 = Set.Icc (-a) 1 := by
  let f : ℝ → ℝ := fun t => -a * (1 - t) ^ 2 + t ^ 2
  have hf : Continuous f := by fun_prop
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1,ht.2]
    have h1t : (1 - t) ^ 2 ≤ 1 := by nlinarith [ht.1,ht.2]
    have hmul : 0 ≤ a * (1 - t) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
    have hmul' : a * (1 - t) ^ 2 ≤ a := by nlinarith
    change -a ≤ -a * (1 - t) ^ 2 + t ^ 2 ∧ -a * (1 - t) ^ 2 + t ^ 2 ≤ 1
    constructor <;> nlinarith [sq_nonneg t]
  · have h := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf.continuousOn
    simpa [f] using h

/-- At an actual crossing the rounded branch has exactly the same straight
cut trace between its two actual cut points; it introduces no curved branch. -/
theorem roundedCorner_crossing_trace (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) : ∃ a : ℝ, 0 < a ∧ ∀ δ : ℝ,
      roundedCorner D (D.incoming c i) δ '' Set.Icc 0 1 =
        (fun q : ℝ => cornerCenter D (D.incoming c i) +
          δ • (q • arcVector D (D.continuation (D.incoming c i)))) '' Set.Icc (-a) 1 := by
  obtain ⟨a,ha,hv⟩ := crossing_arcVector_collinear D c i
  refine ⟨a,ha,?_⟩
  intro δ
  have heq : roundedCorner D (D.incoming c i) δ =
      (fun q : ℝ => cornerCenter D (D.incoming c i) +
        δ • (q • arcVector D (D.continuation (D.incoming c i)))) ∘
        (fun t : ℝ => -a * (1 - t) ^ 2 + t ^ 2) := by
    funext t
    simp only [roundedCorner, hv, Function.comp_apply, smul_smul, ← add_smul]
    congr 2
    ring
  rw [heq, Set.image_comp, crossing_quadratic_scalar_range a ha]

end DirectGLSSW.HOMFLY.PrincipalTurning



