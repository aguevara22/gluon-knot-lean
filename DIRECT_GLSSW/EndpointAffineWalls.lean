import FiniteCursorWallGluing
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport
open EndpointEventGeometry EndpointCurrent

private theorem affine_root_between (A B x y : ℝ) (hxy : x≤y)
    (hx : B+x*A<0) (hy : 0<B+y*A) :
    ∃ z : ℝ, x<z ∧ z<y ∧ B+z*A=0 := by
  have hA : 0<A := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) (le_of_not_gt hh)
    nlinarith
  refine ⟨-B/A, (lt_div_iff₀ hA).mpr (by linarith),
    (div_lt_iff₀ hA).mpr (by linarith),?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hA)]
  ring

/-- Exact sign constancy in an affine chamber, with no value assigned at a root. -/
theorem affine_sign_eq_of_no_root (A B x y : ℝ) (hxy : x≤y)
    (hx : B+x*A≠0) (hy : B+y*A≠0)
    (hn : ∀ z : ℝ, x<z → z<y → B+z*A≠0) :
    scalarSignValue (B+x*A)=scalarSignValue (B+y*A) := by
  have hneg : B+x*A<0 ↔ B+y*A<0 := by
    constructor
    · intro hlt
      by_contra hh
      have hpos : 0<B+y*A := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hy)
      obtain ⟨z,hxz,hzy,hz⟩ := affine_root_between A B x y hxy hlt hpos
      exact hn z hxz hzy hz
    · intro hlt
      by_contra hh
      have hpos : 0<B+x*A := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hx)
      obtain ⟨z,hxz,hzy,hz⟩ := affine_root_between (-A) (-B) x y hxy (by nlinarith) (by nlinarith)
      apply hn z hxz hzy
      nlinarith [hz]
  simp only [scalarSignValue,hx,hy,if_false]
  exact if_congr hneg rfl rfl

/-- Literal finite set of affine moving-endpoint determinant roots. -/
def endpointWallSet (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact ((Finset.univ : Finset (Fin (N+1) × Fin (N+1))).filter fun ij =>
    0 < ij.1.val ∧ ij.1.val < ij.2.val ∧ planarDet (W ij.1-W ij.2) v≠0).image fun ij =>
      -polygonHDet W 0 ij.1 ij.2 / planarDet (W ij.1-W ij.2) v

theorem mem_endpointWallSet (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N : ℕ) (t : ℝ) :
    t∈endpointWallSet W v N ↔ ∃ k j : ℕ, 0<k ∧ k<j ∧ j≤N ∧
      planarDet (W k-W j) v≠0 ∧ polygonHDet (moveEndpoint W v t) 0 k j=0 := by
  classical
  constructor
  · intro ht
    obtain ⟨⟨k,j⟩,hkj,ht⟩ := Finset.mem_image.mp ht
    obtain ⟨hk,hkj,hs⟩ := (Finset.mem_filter.mp hkj).2
    refine ⟨k,j,hk,hkj,by omega,hs,?_⟩
    rw [moveEndpoint_farDet W v hk hkj,←ht,div_mul_cancel₀ _ hs]
    ring
  · rintro ⟨k,j,hk,hkj,hjN,hs,hzero⟩
    apply Finset.mem_image.mpr
    refine ⟨(⟨k,by omega⟩,⟨j,by omega⟩),?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk,hkj,hs⟩
    · apply (div_eq_iff hs).mpr
      rw [moveEndpoint_farDet W v hk hkj] at hzero
      linarith

/-- Once any endpoint is generic, every later failure of core genericity is
one of the displayed affine roots; fixed tail triples are discharged here. -/
theorem core_iff_not_endpointWallSet (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ)
    (N : ℕ) (a : ℝ) (ha : ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v a) N)
    (t : ℝ) :
    ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v t) N ↔ t∉endpointWallSet W v N := by
  constructor
  · intro ht hmem
    obtain ⟨k,j,hk,hkj,hj,hs,hz⟩ := (mem_endpointWallSet W v N t).mp hmem
    exact ht 0 k j hk hkj hj hz
  · intro ht i k j hik hkj hjN hz
    by_cases hi : i=0
    · subst i
      have hs : planarDet (W k-W j) v≠0 := by
        intro hs
        have haa := ha 0 k j hik hkj hjN
        rw [moveEndpoint_farDet W v hik hkj,hs,mul_zero,add_zero] at haa hz
        exact haa hz
      exact ht ((mem_endpointWallSet W v N t).mpr ⟨k,j,hik,hkj,hjN,hs,hz⟩)
    · have hk0 : k≠0 := by omega
      have hj0 : j≠0 := by omega
      have haa := ha i k j hik hkj hjN
      simp only [polygonHDet,moveEndpoint,if_neg hi,if_neg hk0,if_neg hj0] at haa hz
      exact haa hz

/-- The actual open current is constant between consecutive affine walls. -/
theorem endpoint_chamber_openCurrent_eq (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ)
    (N : ℕ) (hN : 0<N) (a : ℝ)
    (ha : ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v a) N)
    (x y : ℝ) (hxy : x≤y) (hx : x∉endpointWallSet W v N) (hy : y∉endpointWallSet W v N)
    (hn : ∀ z∈endpointWallSet W v N, ¬(x<z ∧ z<y)) :
    OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v x)) 0 N =
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v y)) 0 N := by
  have hcx := (core_iff_not_endpointWallSet W v N a ha x).mpr hx
  have hcy := (core_iff_not_endpointWallSet W v N a ha y).mpr hy
  have hsign (i k j : ℕ) (hik : i<k) (hkj : k<j) (hjN : j≤N) :
      polygonSignArray (moveEndpoint W v x) i k j = polygonSignArray (moveEndpoint W v y) i k j := by
    by_cases hi : i=0
    · subst i
      unfold polygonSignArray
      rw [moveEndpoint_farDet W v hik hkj,moveEndpoint_farDet W v hik hkj]
      apply affine_sign_eq_of_no_root _ _ x y hxy
      · simpa only [moveEndpoint_farDet W v hik hkj] using hcx 0 k j hik hkj hjN
      · simpa only [moveEndpoint_farDet W v hik hkj] using hcy 0 k j hik hkj hjN
      · intro z hxz hzy hz
        have hcz := (core_iff_not_endpointWallSet W v N a ha z).mpr (by
          intro hmem; exact hn z hmem ⟨hxz,hzy⟩)
        apply hcz 0 k j hik hkj hjN
        simpa only [moveEndpoint_farDet W v hik hkj] using hz
    · have hk0 : k≠0 := by omega
      have hj0 : j≠0 := by omega
      simp only [polygonSignArray,polygonHDet,moveEndpoint,if_neg hi,if_neg hk0,if_neg hj0]
  unfold OpenMarkedCurrent.entry
  apply weightedCutSum_congr_of_branch_eq _ hN
  intro a b ha hab hbN
  apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hab
  intro i k j hai hik hkj hjb
  exact hsign i k j hik hkj (le_trans hjb hbN)

end DirectGLSSW.CursorWallTransport
