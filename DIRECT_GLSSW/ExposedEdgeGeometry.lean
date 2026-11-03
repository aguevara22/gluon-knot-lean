import DirectGLSSW.RealPolygons
import DirectGLSSW.PolygonEvents
import DirectGLSSW.PrimitiveEdgeGrouping
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ExposedOpenPrimitive

/-- Actual occupied-left supporting edge; only its two endpoints lie on its line. -/
def LeftExposed {n : ℕ} (q : Fin n → PlanarPoint ℝ) (e : Fin n) : Prop :=
  ∀ i : Fin n, i ≠ e → i ≠ cyclicSuccessor e →
    0 < planarDet (cyclicTangent q e) (q i - q e)

theorem leftExposed_vertex_nonneg {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (e : Fin n) (he : LeftExposed q e) (i : Fin n) :
    0 ≤ planarDet (cyclicTangent q e) (q i-q e) := by
  by_cases hi : i=e
  · subst i; simp [planarDet]
  by_cases hs : i=cyclicSuccessor e
  · subst i; simp [cyclicTangent,planarDet,mul_comm]
  exact le_of_lt (he i hi hs)

theorem affine_halfplane_nonneg (p u x y : PlanarPoint ℝ) (t : ℝ)
    (hx : 0 ≤ planarDet u (x-p)) (hy : 0 ≤ planarDet u (y-p))
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ planarDet u (affinePoint x y t-p) := by
  have hh : planarDet u (affinePoint x y t-p) =
      (1-t)*planarDet u (x-p)+t*planarDet u (y-p) := by
    simp [planarDet,affinePoint]; ring
  rw [hh]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hx) (mul_nonneg ht hy)

theorem leftExposed_event_nonneg {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (e : Fin n) (he : LeftExposed q e) (x : PolygonEvent q) :
    0 ≤ planarDet (cyclicTangent q e) (polygonEventPoint q x-q e) := by
  rw [polygonEventPoint_eq_affine]
  exact affine_halfplane_nonneg _ _ _ _ _ (leftExposed_vertex_nonneg q e he _)
    (leftExposed_vertex_nonneg q e he _) (polygonEventParameter_bounds q x).1
    (le_of_lt (polygonEventParameter_bounds q x).2)

theorem leftExposed_no_incident_crossing {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) (he : LeftExposed q e)
    (c : PolygonCrossing q) : ¬ PrimitiveEdgeGrouping.Incident q e c := by
  have side (f : Fin n) (hfe : f ≠ e) (hfs : f ≠ cyclicSuccessor e)
      (hsfe : cyclicSuccessor f ≠ e) (x : PlanarPoint ℝ) (hx : edgeInterior q f x) :
      0 < planarDet (cyclicTangent q e) (x-q e) := by
    obtain ⟨t,ht,ht1,rfl⟩ := hx
    have hss : cyclicSuccessor f ≠ cyclicSuccessor e :=
      fun h => hfe (cyclicSuccessor_bijective.injective h)
    have hf := he f hfe hfs
    have hs := he (cyclicSuccessor f) hsfe hss
    have hh : planarDet (cyclicTangent q e) (affinePoint (q f) (q (cyclicSuccessor f)) t-q e) =
        (1-t)*planarDet (cyclicTangent q e) (q f-q e)+
          t*planarDet (cyclicTangent q e) (q (cyclicSuccessor f)-q e) := by
      simp [planarDet,affinePoint];ring
    rw [hh]
    exact add_pos (mul_pos (sub_pos.mpr ht1) hf) (mul_pos ht hs)
  intro hi
  obtain ⟨h12,h21⟩ := crossing_nonincident hq.size_ge_three q hq.g1 c
  rcases hi with hl | hr
  · have hp := side c.val.2 (by rw [← hl];exact (crossing_edges_ne q c).symm)
      (by simpa only [hl] using h12) (by simpa only [hl] using Ne.symm h21)
      (crossingPoint q c) (crossingPoint_mem_right q c)
    have hz := onOpenSegment_carrier_det_zero (crossingPoint_mem_left q c)
    rw [hl] at hz
    change planarDet (cyclicTangent q e) _ = 0 at hz
    linarith
  · have hp := side c.val.1 (by rw [← hr];exact crossing_edges_ne q c)
      (by simpa only [hr] using h21) (by simpa only [hr] using Ne.symm h12)
      (crossingPoint q c) (crossingPoint_mem_left q c)
    have hz := onOpenSegment_carrier_det_zero (crossingPoint_mem_right q c)
    rw [hr] at hz
    change planarDet (cyclicTangent q e) _ = 0 at hz
    linarith

/-- The exposed physical closing edge gives all actual root far signs -1. -/
theorem leftExposed_root_far_sign {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) (he : LeftExposed q e)
    (k : ℕ) (hk : k ∈ Finset.Ioo 0 (n-1)) :
    polygonSignArray (rootedPolygonWord q e) 0 k (n-1) = -1 := by
  have hk0 : 0<k := (Finset.mem_Ioo.mp hk).1
  have hkn : k<n-1 := (Finset.mem_Ioo.mp hk).2
  have hn := hq.size_ge_three
  have hke : cyclicVertexIndex e k ≠ e := by
    intro h
    have hh : cyclicVertexIndex e k = cyclicVertexIndex e (n-1) := h.trans (cyclicVertexIndex_last e).symm
    have := cyclicVertexIndex_injective e (by omega) (by omega) hh
    omega
  have hks : cyclicVertexIndex e k ≠ cyclicSuccessor e := by
    intro h
    have := cyclicVertexIndex_injective e (by omega) (by omega) h
    omega
  have hp := he (cyclicVertexIndex e k) hke hks
  have hd : polygonHDet (rootedPolygonWord q e) 0 k (n-1) < 0 := by
    rw [polygonHDet,rootedPolygonWord_last]
    change planarDet (q (cyclicVertexIndex e k)-q e) (q (cyclicSuccessor e)-q e)<0
    unfold cyclicTangent planarDet at hp
    unfold planarDet
    nlinarith
  simp [polygonSignArray,scalarSignValue,hd,ne_of_lt hd]

end DirectGLSSW.ExposedOpenPrimitive
