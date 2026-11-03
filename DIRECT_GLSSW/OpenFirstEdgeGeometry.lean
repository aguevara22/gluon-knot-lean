import DirectGLSSW.ShortEdgeSignStability
import DirectGLSSW.EndpointDirectSource

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.OpenFirstEdgeGeometry
open ShortEdgeSignStability

/-- Literal approach of the initial point to q1 along its incoming line. -/
def approach (q : ℕ → PlanarPoint ℝ) (ε : ℝ) (i : ℕ) : PlanarPoint ℝ :=
  if i=0 then affinePoint (q 1) (q 0) ε else q i

theorem approach_zero (q : ℕ → PlanarPoint ℝ) (ε : ℝ) :
    approach q ε 0=affinePoint (q 1) (q 0) ε := by simp [approach]

theorem approach_pos (q : ℕ → PlanarPoint ℝ) (ε : ℝ) {i : ℕ} (hi : 0<i) :
    approach q ε i=q i := by simp [approach,Nat.ne_of_gt hi]

theorem polygonHDet_tail (q : ℕ → PlanarPoint ℝ) (ε : ℝ)
    {i k j : ℕ} (hi : 0<i) (hk : 0<k) (hj : 0<j) :
    polygonHDet (approach q ε) i k j=polygonHDet q i k j := by
  simp only [polygonHDet,approach_pos q ε hi,approach_pos q ε hk,approach_pos q ε hj]

theorem polygonSignArray_tail (q : ℕ → PlanarPoint ℝ) (ε : ℝ)
    {i k j : ℕ} (hi : 0<i) (hk : 0<k) (hj : 0<j) :
    polygonSignArray (approach q ε) i k j=polygonSignArray q i k j := by
  exact congrArg scalarSignValue (polygonHDet_tail q ε hi hk hj)

theorem polygonHDet_first_pair (q : ℕ → PlanarPoint ℝ) (ε : ℝ)
    {j : ℕ} (hj : 0<j) :
    polygonHDet (approach q ε) 0 1 j=ε*polygonHDet q 0 1 j := by
  rw [polygonHDet,approach_zero,approach_pos q ε (by omega : 0<1),approach_pos q ε hj]
  simp [polygonHDet,affinePoint,planarDet] <;> ring

private theorem scalarSignValue_positive_mul (ε x : ℝ) (hε : 0<ε) :
    scalarSignValue (ε*x)=scalarSignValue x := by
  rcases lt_trichotomy x 0 with hx|hx|hx
  · have hm : ε*x<0 := mul_neg_of_pos_of_neg hε hx
    simp [scalarSignValue,ne_of_lt hx,ne_of_lt hm,hx,hm]
  · subst x
    simp [scalarSignValue]
  · have hm : 0<ε*x := mul_pos hε hx
    simp [scalarSignValue,ne_of_gt hx,ne_of_gt hm,not_lt_of_ge hx.le,not_lt_of_ge hm.le]

theorem polygonSignArray_first_pair (q : ℕ → PlanarPoint ℝ) {ε : ℝ}
    (hε : 0<ε) {j : ℕ} (hj : 0<j) :
    polygonSignArray (approach q ε) 0 1 j=polygonSignArray q 0 1 j := by
  unfold polygonSignArray
  rw [polygonHDet_first_pair q ε hj]
  exact scalarSignValue_positive_mul ε _ hε

theorem polygonSignArray_turn (q : ℕ → PlanarPoint ℝ) {ε : ℝ} (hε : 0<ε) :
    polygonSignArray (approach q ε) 0 1 2=polygonSignArray q 0 1 2 :=
  polygonSignArray_first_pair q hε (by omega)

theorem polygonHDet_far_affine (q : ℕ → PlanarPoint ℝ) (ε : ℝ)
    {k j : ℕ} (hk : 0<k) (hj : 0<j) :
    polygonHDet (approach q ε) 0 k j=
      polygonHDet q 1 k j+ε*(polygonHDet q 0 k j-polygonHDet q 1 k j) := by
  rw [polygonHDet,approach_zero,approach_pos q ε hk,approach_pos q ε hj]
  simp [polygonHDet,affinePoint,planarDet] <;> ring

/-- One positive radius controls the finite family of actual far triples. -/
theorem exists_uniform_far_data (q : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hcore : CoreHGeneric q N) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ ∀ ε : ℝ, 0<ε → ε<δ →
      ∀ k j : ℕ, 1<k → k<j → j≤N →
        polygonHDet (approach q ε) 0 k j≠0 ∧
        (polygonHDet (approach q ε) 0 k j<0 ↔ polygonHDet q 1 k j<0) := by
  let s := Finset.range (N+1) ×ˢ Finset.range (N+1)
  let P : (ℕ×ℕ) → ℝ → Prop := fun z ε => 1<z.1 → z.1<z.2 → z.2≤N →
    polygonHDet (approach q ε) 0 z.1 z.2≠0 ∧
      (polygonHDet (approach q ε) 0 z.1 z.2<0 ↔ polygonHDet q 1 z.1 z.2<0)
  have hlocal : ∀ z, z∈s → ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, 0<ε → ε<δ → P z ε := by
    intro z hz
    by_cases hg : 1<z.1 ∧ z.1<z.2 ∧ z.2≤N
    · obtain ⟨δ,hδ,hgood⟩ := exists_affine_sign_radius
        (polygonHDet q 1 z.1 z.2)
        (polygonHDet q 0 z.1 z.2-polygonHDet q 1 z.1 z.2)
        (hcore 1 z.1 z.2 hg.1 hg.2.1 hg.2.2)
      refine ⟨δ,hδ,?_⟩
      intro ε hε hεδ _ _ _
      rw [polygonHDet_far_affine q ε (by omega : 0<z.1) (by omega : 0<z.2)]
      exact hgood ε hε hεδ
    · refine ⟨1,by norm_num,?_⟩
      intro ε _ _ hk hkj hj
      exact False.elim (hg ⟨hk,hkj,hj⟩)
  obtain ⟨δ,hδ,hgood⟩ := exists_finset_common_radius s P hlocal
  refine ⟨min δ 1,lt_min hδ (by norm_num),min_le_right _ _,?_⟩
  intro ε hε hεδ k j hk hkj hj
  have hmem : (k,j)∈s := by simp [s];omega
  exact hgood ε hε (lt_of_lt_of_le hεδ (min_le_left _ _)) (k,j) hmem hk hkj hj

private theorem scalarSignValue_of_neg_iff {x y : ℝ} (hx : x≠0) (hy : y≠0)
    (h : x<0 ↔ y<0) : scalarSignValue x=scalarSignValue y := by
  by_cases hn : y<0
  · simp [scalarSignValue,hx,hy,hn,h.mpr hn]
  · have hn' : ¬x<0 := mt h.mp hn
    simp [scalarSignValue,hx,hy,hn,hn']

/-- Far-row equality on the real approach family, with no assumed shortness certificate. -/
theorem exists_uniform_far_signs (q : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hcore : CoreHGeneric q N) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ ∀ ε : ℝ, 0<ε → ε<δ →
      ∀ k j : ℕ, 1<k → k<j → j≤N →
        polygonSignArray (approach q ε) 0 k j=polygonSignArray (approach q ε) 1 k j ∧
        polygonSignArray (approach q ε) 1 k j=polygonSignArray q 1 k j := by
  obtain ⟨δ,hδ,hδ1,hgood⟩ := exists_uniform_far_data q N hcore
  refine ⟨δ,hδ,hδ1,?_⟩
  intro ε hε hεδ k j hk hkj hj
  have hd := hgood ε hε hεδ k j hk hkj hj
  have ht := polygonSignArray_tail q ε (by omega : 0<1) (by omega : 0<k) (by omega : 0<j)
  refine ⟨?_,ht⟩
  rw [ht]
  exact scalarSignValue_of_neg_iff hd.1 (hcore 1 k j hk hkj hj) hd.2

/-- The full finite open-word noncollinearity remains valid during a short approach. -/
theorem exists_approach_coreHGeneric (q : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hcore : CoreHGeneric q N) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ ∀ ε : ℝ, 0<ε → ε<δ →
      CoreHGeneric (approach q ε) N := by
  obtain ⟨δ,hδ,hδ1,hgood⟩ := exists_uniform_far_data q N hcore
  refine ⟨δ,hδ,hδ1,?_⟩
  intro ε hε hεδ i k j hik hkj hj
  by_cases hi : i=0
  · subst i
    by_cases hk : k=1
    · subst k
      rw [polygonHDet_first_pair q ε (by omega : 0<j)]
      exact mul_ne_zero (ne_of_gt hε) (hcore 0 1 j hik hkj hj)
    · exact (hgood ε hε hεδ k j (by omega) hkj hj).1
  · rw [polygonHDet_tail q ε (by omega : 0<i) (by omega : 0<k) (by omega : 0<j)]
    exact hcore i k j hik hkj hj

/-- Every tail interval is unchanged, for arbitrary fixed near data and all ε. -/
theorem ordinaryCurrent_tail (q : ℕ → PlanarPoint ℝ) (ε : ℝ) (D : TripleArray)
    {i j : ℕ} (hi : 1≤i) (hij : i<j) :
    ordinaryCurrent D (polygonSignArray (approach q ε)) i j=
      ordinaryCurrent D (polygonSignArray q) i j := by
  apply ordinaryCurrent_congr_interval_fixed_near D _ _ hij
  intro a k b hia hak hkb hbj
  exact polygonSignArray_tail q ε (by omega) (by omega) (by omega)

end DirectGLSSW.OpenFirstEdgeGeometry
