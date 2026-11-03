import DaughterNoRetainedInterior

set_option autoImplicit false
namespace DirectGLSSW.DaughterOpenParameter
open DaughterFirstReturn DaughterG2Inheritance
noncomputable section

theorem openSubsegment_parameter_iff (u v a b : PlanarPoint ℝ) (s d t : ℝ)
    (huv : u ≠ v) (hd : 0 < d) (ha : a = affinePoint u v s)
    (hab : b-a = d • (v-u)) :
    OnOpenSegment a b (affinePoint u v t) ↔ s < t ∧ t < s+d := by
  constructor
  · rintro ⟨r,hr0,hr1,hpoint⟩
    have heq : t = s+r*d := affinePoint_injective u v huv
      (hpoint.trans (affinePoint_subsegment u v a b s d r ha hab))
    rw [heq]
    constructor <;> nlinarith
  · rintro ⟨hst,htd⟩
    let r := (t-s)/d
    have hr0 : 0 < r := div_pos (sub_pos.mpr hst) hd
    have hr1 : r < 1 := (div_lt_iff₀ hd).mpr (by linarith)
    refine ⟨r,hr0,hr1,?_⟩
    rw [affinePoint_subsegment u v a b s d r ha hab]
    congr 1
    dsimp [r]
    rw [div_mul_cancel₀ _ (ne_of_gt hd)]
    ring

theorem eventPoint_mem_daughter_edge_iff {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (S : Finset (PolygonCrossing P))
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (y : PolygonEvent P) (hye : polygonEventEdge P y = daughterCarrier P hP.g2 S root i) :
    edgeInterior (daughterVertex P hP.g2 S root) i (polygonEventPoint P y) ↔
    polygonEventParameter P (orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val) <
        polygonEventParameter P y ∧
    polygonEventParameter P y <
      polygonEventParameter P (orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val) +
      daughterSideScale P hP.g2 S root (cornerEnumeration P hP.g2 S root i) := by
  let e := daughterCarrier P hP.g2 S root i
  have hne : P e ≠ P (cyclicSuccessor e) := by
    intro h
    exact cyclicTangent_ne_zero hP.size_ge_three P hP.g1 e (sub_eq_zero.mpr h.symm)
  obtain ⟨hd,hab⟩ := daughterSide_positive_multiple P hP.g2 S hP.size_ge_three root hroot i
  have ha := polygonEventPoint_eq_affine P
    (orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val)
  rw [polygonEventPoint_eq_affine P y,hye]
  exact openSubsegment_parameter_iff _ _ _ _ _ _ _ hne hd ha hab



end
end DirectGLSSW.DaughterOpenParameter
