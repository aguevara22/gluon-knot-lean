import DirectGLSSW.GeometricGates

/-!
# Concrete affine segments in the oriented plane

Source: Section 1, lines 61–100 of the frozen note. These are elementary
prerequisites for its G1–G2 polygon geometry. Segment membership is defined
by actual affine interpolation, independently of determinant tests.

The statements are generic over a field (and an ordered field for open
segments). Specialization to the real plane and the full polygon claims
are separate obligations.
-/

namespace DirectGLSSW

variable {K : Type*}

section AffineAlgebra

variable [CommRing K]

/-- Swapping the ordered planar directions reverses the determinant sign. -/
theorem planarDet_swap (u v : PlanarPoint K) : planarDet v u = -planarDet u v := by
  simp only [planarDet]
  ring

/-- The point with affine parameter `t` on the directed carrier from `a` to `b`. -/
def affinePoint (a b : PlanarPoint K) (t : K) : PlanarPoint K :=
  (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))

theorem affinePoint_zero (a b : PlanarPoint K) : affinePoint a b 0 = a := by
  ext <;> simp [affinePoint]

theorem affinePoint_one (a b : PlanarPoint K) : affinePoint a b 1 = b := by
  ext <;> simp [affinePoint]

/-- Reversing the endpoints replaces the affine parameter by `1 - t`. -/
theorem affinePoint_reverse (a b : PlanarPoint K) (t : K) :
    affinePoint b a (1 - t) = affinePoint a b t := by
  ext <;> simp only [affinePoint] <;> ring

/-- Affine interpolation lies on its carrier, including both endpoints. -/
theorem affinePoint_carrier_det_zero (a b : PlanarPoint K) (t : K) :
    planarDet (b - a) (affinePoint a b t - a) = 0 := by
  simp only [planarDet, affinePoint, Prod.fst_sub, Prod.snd_sub]
  ring

/-- The determinant against an affine carrier splits into its base and tangent parts. -/
theorem affinePoint_det_offset (a b c d : PlanarPoint K) (t : K) :
    planarDet (b - a) (affinePoint c d t - a) =
      planarDet (b - a) (c - a) + t * planarDet (b - a) (d - c) := by
  simp only [planarDet, affinePoint, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Parallel intersecting carriers have collinear base points. Neither carrier
is assumed transverse, and degenerate carriers satisfy this identity too. -/
theorem affinePoint_parallel_collinear (a b c d : PlanarPoint K) (s t : K)
    (h : affinePoint a b s = affinePoint c d t)
    (hpar : planarDet (b - a) (d - c) = 0) :
    planarDet (b - a) (c - a) = 0 := by
  have hd := congrArg (fun x => planarDet (b - a) (x - a)) h
  dsimp only at hd
  rw [affinePoint_carrier_det_zero, affinePoint_det_offset, hpar] at hd
  simpa using hd.symm

end AffineAlgebra

section AffineField

variable [Field K]

/-- A nondegenerate affine parametrization is injective. -/
theorem affinePoint_injective (a b : PlanarPoint K) (hab : a ≠ b) :
    Function.Injective (affinePoint a b) := by
  intro s t h
  by_contra hst
  have hx : (s - t) * (b.1 - a.1) = 0 := by
    calc
      (s - t) * (b.1 - a.1) =
          (a.1 + s * (b.1 - a.1)) - (a.1 + t * (b.1 - a.1)) := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
  have hy : (s - t) * (b.2 - a.2) = 0 := by
    calc
      (s - t) * (b.2 - a.2) =
          (a.2 + s * (b.2 - a.2)) - (a.2 + t * (b.2 - a.2)) := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.snd h)
  have hba : b = a := Prod.ext
    (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hst)))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left (sub_ne_zero.mpr hst)))
  exact hab hba.symm

/-- Two transverse carriers have at most one pair of intersection parameters. -/
theorem affinePoint_intersection_parameters_unique
    (a b c d : PlanarPoint K) (s t s' t' : K)
    (hdet : planarDet (b - a) (d - c) ≠ 0)
    (h : affinePoint a b s = affinePoint c d t)
    (h' : affinePoint a b s' = affinePoint c d t') : s = s' ∧ t = t' := by
  have ht0 : planarDet (b - a) (c - a) + t * planarDet (b - a) (d - c) = 0 := by
    rw [← affinePoint_det_offset, ← h, affinePoint_carrier_det_zero]
  have ht1 : planarDet (b - a) (c - a) + t' * planarDet (b - a) (d - c) = 0 := by
    rw [← affinePoint_det_offset, ← h', affinePoint_carrier_det_zero]
  have htprod : (t - t') * planarDet (b - a) (d - c) = 0 := by
    calc
      (t - t') * planarDet (b - a) (d - c) =
          (planarDet (b - a) (c - a) + t * planarDet (b - a) (d - c)) -
            (planarDet (b - a) (c - a) + t' * planarDet (b - a) (d - c)) := by ring
      _ = 0 := by rw [ht0, ht1, sub_self]
  have ht : t = t' := sub_eq_zero.mp ((mul_eq_zero.mp htprod).resolve_right hdet)
  have hab : a ≠ b := by
    intro heq
    apply hdet
    simp [← heq, planarDet]
  have hs : s = s' := affinePoint_injective a b hab (h.trans (ht ▸ h'.symm))
  exact ⟨hs, ht⟩

end AffineField

section OpenSegments

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Membership in an open segment is witnessed by an actual parameter in `(0,1)`. -/
def OnOpenSegment (a b x : PlanarPoint K) : Prop :=
  ∃ t : K, 0 < t ∧ t < 1 ∧ x = affinePoint a b t

/-- Open segment membership is independent of the orientation of its endpoints. -/
theorem onOpenSegment_symm {a b x : PlanarPoint K} (h : OnOpenSegment a b x) :
    OnOpenSegment b a x := by
  obtain ⟨t, ht0, ht1, hx⟩ := h
  refine ⟨1 - t, sub_pos.mpr ht1, ?_, ?_⟩
  · exact sub_lt_self 1 ht0
  · rw [affinePoint_reverse]
    exact hx

omit [IsStrictOrderedRing K] in
/-- The left endpoint of a nondegenerate segment is excluded from its interior. -/
theorem onOpenSegment_ne_left {a b x : PlanarPoint K} (hab : a ≠ b)
    (h : OnOpenSegment a b x) : x ≠ a := by
  obtain ⟨t, ht0, _, hx⟩ := h
  intro hxa
  have ht : t = 0 := affinePoint_injective a b hab
    (hx.symm.trans (hxa.trans (affinePoint_zero a b).symm))
  exact (ne_of_gt ht0) ht

/-- The right endpoint of a nondegenerate segment is excluded from its interior. -/
theorem onOpenSegment_ne_right {a b x : PlanarPoint K} (hab : a ≠ b)
    (h : OnOpenSegment a b x) : x ≠ b := by
  exact onOpenSegment_ne_left hab.symm (onOpenSegment_symm h)

omit [IsStrictOrderedRing K] in
/-- Every interior point satisfies the carrier's collinearity equation. -/
theorem onOpenSegment_carrier_det_zero {a b x : PlanarPoint K}
    (h : OnOpenSegment a b x) : planarDet (b - a) (x - a) = 0 := by
  obtain ⟨t, _, _, rfl⟩ := h
  exact affinePoint_carrier_det_zero a b t

/-- Two noncollinear rays from a common vertex have disjoint open segments. -/
theorem onOpenSegment_common_origin_disjoint {a b c x : PlanarPoint K}
    (hdet : planarDet (b - a) (c - a) ≠ 0)
    (hab : OnOpenSegment a b x) : ¬ OnOpenSegment a c x := by
  intro hac
  obtain ⟨t, ht0, _, hx⟩ := hac
  have hcarrier := onOpenSegment_carrier_det_zero hab
  rw [hx, affinePoint_det_offset] at hcarrier
  have htprod : t * planarDet (b - a) (c - a) = 0 := by
    simpa [planarDet] using hcarrier
  exact hdet ((mul_eq_zero.mp htprod).resolve_left (ne_of_gt ht0))

end OpenSegments

end DirectGLSSW
