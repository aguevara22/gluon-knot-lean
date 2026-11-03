import SmoothingTurnSigns
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SmoothingTurnCount
open DirectGLSSW GeometricSmoothingWeights DaughterFirstReturn PermutationOrbits
open scoped BigOperators

/-- Literal cornerStateSum exponent equals the count of actual strictly left turns. -/
theorem leftTurnCount_eq_literal_filter_card {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    leftTurnCount q = (Finset.univ.filter (fun i : Fin n =>
      0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
        (cyclicTangent q i))).card := by
  classical
  unfold leftTurnCount turnValue
  rw [Finset.card_filter]
  rfl

/-- Exact public name used by the frozen cornerStateSum exponent. -/
theorem leftTurnCount_eq_filter_card {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    leftTurnCount q = (Finset.univ.filter (fun i : Fin n =>
      0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
        (cyclicTangent q i))).card :=
  leftTurnCount_eq_literal_filter_card q

/-- All-support version of the daughter count in the exact final-expression convention. -/
theorem sum_daughter_literal_filter_cards {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q)) :
    (∑ c : Component (smoothingDartPermutation q hq.g2 S),
      (Finset.univ.filter (fun i : Fin (Fintype.card (CornerCoord q hq.g2 S
          (componentRoot q hq S c))) =>
        0 < planarDet (daughterSideVector q hq.g2 S (componentRoot q hq S c)
          ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S
            (componentRoot q hq S c))))⁻¹ i))
          (daughterSideVector q hq.g2 S (componentRoot q hq S c) i))).card) =
      (Finset.univ.filter (fun i : Fin n =>
        0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
          (cyclicTangent q i))).card + S.card := by
  simpa only [leftTurnCount_eq_literal_filter_card] using
    sum_daughter_leftTurnCount q hq S

/-- The actual signed daughter weights extract the exact literal parent and support signs. -/
theorem product_daughter_literal_signed_weights {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q))
    (w : Component (smoothingDartPermutation q hq.g2 S) → ℚ) :
    (∏ c : Component (smoothingDartPermutation q hq.g2 S),
      ((-1 : ℚ) ^ (Finset.univ.filter (fun i : Fin (Fintype.card (CornerCoord q hq.g2 S
          (componentRoot q hq S c))) =>
        0 < planarDet (daughterSideVector q hq.g2 S (componentRoot q hq S c)
          ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S
            (componentRoot q hq S c))))⁻¹ i))
          (daughterSideVector q hq.g2 S (componentRoot q hq S c) i))).card * w c)) =
      (-1 : ℚ) ^ (Finset.univ.filter (fun i : Fin n =>
        0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
          (cyclicTangent q i))).card * (-1 : ℚ) ^ S.card * ∏ c, w c := by
  simpa only [leftTurnCount_eq_literal_filter_card] using
    product_daughter_signed_weights q hq S w

end DirectGLSSW.SmoothingTurnCount




