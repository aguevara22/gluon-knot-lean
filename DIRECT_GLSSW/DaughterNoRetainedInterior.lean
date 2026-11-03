import DaughterParentCrossing
import DirectGLSSW.MixedEdgeRetainedWord

set_option autoImplicit false
namespace DirectGLSSW.DaughterNoRetainedInterior
open DaughterFirstReturn DaughterG2Inheritance MixedEdgeRetainedSuccessor MixedEdgeRetainedWord
noncomputable section
attribute [local instance] Classical.propDecidable

theorem originalCornerNext_le_of_retained_after {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) (S : Finset (PolygonCrossing P))
    (x y : PolygonEvent P) (hx : retainedCorner P S x) (hy : retainedCorner P S y)
    (hxy : (polygonEventOrder P hG2).lt x y) :
    (polygonEventOrder P hG2).lt x (originalCornerNext P hG2 S x hx) ∧
      (polygonEventOrder P hG2).le (originalCornerNext P hG2 S x hx) y := by
  letI : LinearOrder (PolygonEvent P) := polygonEventOrder P hG2
  let a : RetainedEvent P S := ⟨x,hx⟩
  let b : RetainedEvent P S := ⟨y,hy⟩
  have hab : a < b := hxy
  rcases orderedCyclicSuccessor_order_spec (RetainedEvent P S) a with h | h
  · have h₁ := h.1
    have h₂ := h.2 b hab
    change x < (retainedOriginalSuccessor P hG2 S ⟨x,hx⟩).val at h₁
    change (retainedOriginalSuccessor P hG2 S ⟨x,hx⟩).val ≤ y at h₂
    rw [← originalCornerNext_eq_retainedOriginalSuccessor] at h₁ h₂
    exact ⟨h₁,h₂⟩
  · exact ((not_le_of_gt hab) (h.1 b)).elim

theorem polygonEventEdge_monotone {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) :
    letI := polygonEventOrder P hG2
    Monotone (polygonEventEdge P) := by
  letI := polygonEventOrder P hG2
  intro x y hxy
  rcases lt_or_eq_of_le hxy with h | rfl
  · rcases (polygonEvent_lt_iff P hG2 x y).mp h with h | h
    · exact h.le
    · exact le_of_eq h.1
  · exact le_rfl

theorem daughter_successor_point_originalCornerNext {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) (S : Finset (PolygonCrossing P))
    (root : PolygonEvent P) (i : Fin (Fintype.card (CornerCoord P hG2 S root))) :
    daughterVertex P hG2 S root (cyclicSuccessor i) =
      polygonEventPoint P (originalCornerNext P hG2 S
        (orbitEventAt P hG2 S root (cornerEnumeration P hG2 S root i).val)
        (cornerEnumeration P hG2 S root i).property) := by
  unfold daughterVertex
  rw [cornerEnumeration_successor,cornerSuccessor_eq_pairing_originalCornerNext]
  exact smoothingPairing_point P S _

/-- A daughter open edge has no retained original event in its interior. -/
theorem no_retained_event_in_daughter_edge {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (S : Finset (PolygonCrossing P))
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (y : PolygonEvent P) (hy : retainedCorner P S y)
    (hye : polygonEventEdge P y = daughterCarrier P hP.g2 S root i) :
    ¬ edgeInterior (daughterVertex P hP.g2 S root) i (polygonEventPoint P y) := by
  letI : LinearOrder (PolygonEvent P) := polygonEventOrder P hP.g2
  let c := cornerEnumeration P hP.g2 S root i
  let x := orbitEventAt P hP.g2 S root c.val
  let e := daughterCarrier P hP.g2 S root i
  let s := polygonEventParameter P x
  let d := daughterSideScale P hP.g2 S root c
  let z := originalCornerNext P hP.g2 S x c.property
  have hxe : polygonEventEdge P x = e := rfl
  have hye' : polygonEventEdge P y = e := hye
  have hne : P e ≠ P (cyclicSuccessor e) := by
    intro h
    exact cyclicTangent_ne_zero hP.size_ge_three P hP.g1 e (sub_eq_zero.mpr h.symm)
  have hstart : daughterVertex P hP.g2 S root i =
      affinePoint (P e) (P (cyclicSuccessor e)) s := polygonEventPoint_eq_affine P x
  obtain ⟨hd,hstep⟩ := daughterSide_positive_multiple P hP.g2 S hP.size_ge_three root hroot i
  change 0 < d at hd
  change daughterVertex P hP.g2 S root (cyclicSuccessor i) - daughterVertex P hP.g2 S root i =
    d • (P (cyclicSuccessor e) - P e) at hstep
  intro hinside
  obtain ⟨t,ht0,ht1,hpoint⟩ := hinside
  have hyparam : polygonEventParameter P y = s+t*d := by
    apply affinePoint_injective (P e) (P (cyclicSuccessor e)) hne
    calc
      affinePoint (P e) (P (cyclicSuccessor e)) (polygonEventParameter P y) =
          polygonEventPoint P y := by simpa only [hye'] using (polygonEventPoint_eq_affine P y).symm
      _ = affinePoint (daughterVertex P hP.g2 S root i)
          (daughterVertex P hP.g2 S root (cyclicSuccessor i)) t := hpoint
      _ = affinePoint (P e) (P (cyclicSuccessor e)) (s+t*d) :=
        affinePoint_subsegment _ _ _ _ s d t hstart hstep
  have hxy : x < y := by
    apply (polygonEvent_sameEdge_lt_iff P hP.g2 x y (hxe.trans hye'.symm)).mpr
    change s < polygonEventParameter P y
    rw [hyparam]
    nlinarith
  obtain ⟨hxz,hzy⟩ := originalCornerNext_le_of_retained_after P hP.g2 S x y c.property hy hxy
  change x < z at hxz
  change z ≤ y at hzy
  have hze : polygonEventEdge P z = e := by
    have h₁ := polygonEventEdge_monotone P hP.g2 hxz.le
    have h₂ := polygonEventEdge_monotone P hP.g2 hzy
    rw [hxe] at h₁
    rw [hye'] at h₂
    exact le_antisymm h₂ h₁
  have hend : daughterVertex P hP.g2 S root (cyclicSuccessor i) = polygonEventPoint P z :=
    daughter_successor_point_originalCornerNext P hP.g2 S root i
  have hzparam : polygonEventParameter P z = s+d := by
    apply affinePoint_injective (P e) (P (cyclicSuccessor e)) hne
    calc
      affinePoint (P e) (P (cyclicSuccessor e)) (polygonEventParameter P z) =
          polygonEventPoint P z := by simpa only [hze] using (polygonEventPoint_eq_affine P z).symm
      _ = daughterVertex P hP.g2 S root (cyclicSuccessor i) := hend.symm
      _ = affinePoint (daughterVertex P hP.g2 S root i)
          (daughterVertex P hP.g2 S root (cyclicSuccessor i)) 1 := (affinePoint_one _ _).symm
      _ = affinePoint (P e) (P (cyclicSuccessor e)) (s+d) := by
        simpa only [one_mul] using affinePoint_subsegment _ _ _ _ s d 1 hstart hstep
  have hparamle : polygonEventParameter P z ≤ polygonEventParameter P y := by
    apply le_of_not_gt
    intro h
    exact (not_lt_of_ge hzy)
      ((polygonEvent_sameEdge_lt_iff P hP.g2 y z (hye'.trans hze.symm)).mpr h)
  rw [hyparam,hzparam] at hparamle
  nlinarith





end
end DirectGLSSW.DaughterNoRetainedInterior
