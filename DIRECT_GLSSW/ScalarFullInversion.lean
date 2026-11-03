import ScalarEmptyProduct

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open scoped BigOperators
open DirectGLSSW.PermutationOrbits DirectGLSSW.ActualLocalSupports
open DirectGLSSW.ScalarInversionBridge DirectGLSSW.LocalCoordinates
open DirectGLSSW.DaughterFirstReturn
attribute [local instance] Classical.propDecidable

variable {R : Type*} [CommRing R] (X : CyclicScalar R)
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem scalar_subset_refinement_coefficient (U : Finset (PolygonCrossing q)) :
    (∑ S : {S : Finset (PolygonCrossing q) // S ⊆ U},
      (-1 : R) ^ (U.card - S.1.card)) =
      if U = ∅ then 1 else 0 := by
  classical
  let E : {S : Finset (PolygonCrossing q) // S ⊆ U} ≃
      {S : Finset (PolygonCrossing q) // S ∈ U.powerset} :=
    { toFun := fun S => ⟨S.1, Finset.mem_powerset.mpr S.2⟩
      invFun := fun S => ⟨S.1, Finset.mem_powerset.mp S.2⟩
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl }
  have hsum : (∑ S : {S : Finset (PolygonCrossing q) // S ⊆ U},
        (-1 : R) ^ (U.card - S.1.card)) =
      ∑ S ∈ U.powerset, (-1 : R) ^ (U.card - S.card) := by
    calc
      _ = ∑ S : {S : Finset (PolygonCrossing q) // S ∈ U.powerset},
          (-1 : R) ^ (U.card - S.1.card) := by
        apply Fintype.sum_equiv E
        intro S
        rfl
      _ = ∑ S ∈ U.powerset, (-1 : R) ^ (U.card - S.card) := by
        simpa using (Finset.sum_attach U.powerset
          (fun S : Finset (PolygonCrossing q) => (-1 : R) ^ (U.card - S.card)))
  rw [hsum]
  exact DirectGLSSW.refinementCoefficient_eq (R := R) U

set_option maxHeartbeats 20000000 in
/-- Literal full inversion for every cyclic scalar on G2 closed polygons.
The smoothing primitive and all component products use actual daughter words. -/
theorem scalar_full_inversion :
    X.toFun (List.ofFn q) =
    ∑ S : Supports q hq,
      ∏ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
        primitive X (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
          (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
            hq.size_ge_three S.2 (rootEvent q hq S A)) := by
  classical
  let roots : ∀ S : Supports q hq,
      ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1) :=
    fun S => ScalarInversionBridge.roots q hq S
  let weighted (U : Supports q hq) : R := componentProduct X q hq.g2 U.1
  let families := fun S : Supports q hq =>
    {family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 (roots S) family}
  let Source := Σ S : Supports q hq, families S
  let Target := Σ U : Supports q hq,
    {S : Finset (PolygonCrossing q) // S ⊆ U.1}
  let sourceWeight : Source → R := fun x =>
    (-1 : R) ^ ((x.1.1 ∪ unionLocal q
      (smoothingIncomingPermutation q hq.g2 x.1.1) x.1.1 x.2.1).card - x.1.1.card) *
      componentProduct X q hq.g2
        (x.1.1 ∪ unionLocal q
          (smoothingIncomingPermutation q hq.g2 x.1.1) x.1.1 x.2.1)
  letI : ∀ S : Supports q hq, Fintype (families S) :=
    fun S => scalarLocalFamilyFintype q hq S (roots S)
  letI : Fintype Source := inferInstance
  let E := TwoStageRefinement.twoStageSupportEquiv q hq.g2 hq.size_ge_three roots
  have hExpand :
      (∑ S : Supports q hq,
        ∏ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
          primitive X (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
            (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
              hq.size_ge_three S.2 (rootEvent q hq S A))) =
      ∑ x : Source, sourceWeight x := by
    rw [Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro S
    exact scalar_product_daughter_primitives_eq_refinement_sum X q hq S (roots S)
  let targetWeight : Target → R := fun y =>
    (-1 : R) ^ (y.1.1.card - y.2.1.card) * weighted y.1
  have hPoint (x : Source) : sourceWeight x = targetWeight (E x) := by
    rcases x with ⟨S, family⟩
    simp [sourceWeight, targetWeight, weighted, E,
      TwoStageRefinement.twoStageSupportEquiv_apply_support,
      TwoStageRefinement.twoStageSupportEquiv_apply_firstStage]
  have hReindex : (∑ x : Source, sourceWeight x) =
      ∑ y : Target, targetWeight y := by
    apply Fintype.sum_equiv E sourceWeight targetWeight
    intro x
    exact hPoint x
  have hTarget : (∑ y : Target, targetWeight y) =
      weighted ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩ := by
    rw [Fintype.sum_sigma]
    change (∑ U : Supports q hq,
      ∑ S : {S : Finset (PolygonCrossing q) // S ⊆ U.1},
        (-1 : R) ^ (U.1.card - S.1.card) * weighted U) = _
    calc
      _ = ∑ U : Supports q hq,
          (∑ S : {S : Finset (PolygonCrossing q) // S ⊆ U.1},
            (-1 : R) ^ (U.1.card - S.1.card)) * weighted U := by
        apply Fintype.sum_congr
        intro U
        rw [← Finset.sum_mul]
      _ = weighted ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩ := by
        let U0 : Supports q hq :=
          ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩
        rw [Finset.sum_eq_single U0]
        · simp [U0, scalar_subset_refinement_coefficient]
        · intro U hU hU0
          have hne : U.1 ≠ ∅ := by
            intro h
            apply hU0
            apply Subtype.ext
            exact h
          simp [scalar_subset_refinement_coefficient, hne]
        · intro h
          exact (h (Finset.mem_univ U0)).elim
  have hEmpty := scalar_empty_componentProduct_eq_polygon X q hq
  change weighted ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩ =
    X.toFun (List.ofFn q) at hEmpty
  calc
    X.toFun (List.ofFn q) =
        weighted ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩ :=
      hEmpty.symm
    _ = ∑ y : Target, targetWeight y := hTarget.symm
    _ = ∑ x : Source, sourceWeight x := hReindex.symm
    _ = ∑ S : Supports q hq,
        ∏ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
          primitive X (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
            (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
              hq.size_ge_three S.2 (rootEvent q hq S A)) := hExpand.symm

end DirectGLSSW.FullScalarInversion


