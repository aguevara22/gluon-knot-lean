import DirectGLSSW.PolygonSignExtensionality
import DirectGLSSW.HorizontalShortEdge
import DirectGLSSW.PolygonCrossings

set_option autoImplicit false

namespace DirectGLSSW.EdgeAffineNormalization

/-- Source lines 557–563: explicit positive-orientation coordinates with
the two endpoints of the chosen edge on the horizontal axis. -/
def normSq (u v : PlanarPoint ℝ) : ℝ :=
  (v.1 - u.1)^2 + (v.2 - u.2)^2

def normalize (u v p : PlanarPoint ℝ) : PlanarPoint ℝ :=
  ((v.1-u.1)*(p.1-u.1) + (v.2-u.2)*(p.2-u.2),
   (v.1-u.1)*(p.2-u.2) - (v.2-u.2)*(p.1-u.1))

theorem normSq_pos (u v : PlanarPoint ℝ) (huv : u ≠ v) : 0 < normSq u v := by
  unfold normSq
  by_contra h
  have hx : (v.1-u.1)^2 = 0 := by nlinarith [sq_nonneg (v.1-u.1), sq_nonneg (v.2-u.2)]
  have hy : (v.2-u.2)^2 = 0 := by nlinarith [sq_nonneg (v.1-u.1), sq_nonneg (v.2-u.2)]
  have hx' : v.1 = u.1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hy' : v.2 = u.2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hy)
  exact huv (Prod.ext hx' hy').symm

theorem normalize_left (u v : PlanarPoint ℝ) : normalize u v u = (0,0) := by
  simp [normalize]

theorem normalize_right (u v : PlanarPoint ℝ) :
    normalize u v v = (normSq u v,0) := by
  apply Prod.ext <;> dsimp [normalize,normSq] <;> ring

theorem normalize_affinePoint (u v a b : PlanarPoint ℝ) (t : ℝ) :
    normalize u v (affinePoint a b t) =
      affinePoint (normalize u v a) (normalize u v b) t := by
  apply Prod.ext <;> dsimp [normalize,affinePoint] <;> ring

theorem normalize_injective (u v : PlanarPoint ℝ) (huv : u ≠ v) :
    Function.Injective (normalize u v) := by
  intro p q hpq
  have hD : normSq u v ≠ 0 := ne_of_gt (normSq_pos u v huv)
  have hx : (p.1-q.1)*normSq u v = 0 := by
    calc
      (p.1-q.1)*normSq u v =
          (v.1-u.1)*((normalize u v p).1-(normalize u v q).1) -
          (v.2-u.2)*((normalize u v p).2-(normalize u v q).2) := by
            dsimp [normalize,normSq]; ring
      _ = 0 := by rw [hpq]; ring
  have hy : (p.2-q.2)*normSq u v = 0 := by
    calc
      (p.2-q.2)*normSq u v =
          (v.2-u.2)*((normalize u v p).1-(normalize u v q).1) +
          (v.1-u.1)*((normalize u v p).2-(normalize u v q).2) := by
            dsimp [normalize,normSq]; ring
      _ = 0 := by rw [hpq]; ring
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right hD))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right hD))

theorem normalize_det (u v a b c : PlanarPoint ℝ) :
    planarDet (normalize u v b - normalize u v c)
      (normalize u v a - normalize u v c) =
        normSq u v * planarDet (b-c) (a-c) := by
  dsimp [normalize,normSq,planarDet]
  ring

theorem normalize_segment_iff (u v : PlanarPoint ℝ) (huv : u ≠ v)
    (a b x : PlanarPoint ℝ) :
    OnOpenSegment (normalize u v a) (normalize u v b) (normalize u v x) ↔
      OnOpenSegment a b x := by
  constructor
  · rintro ⟨t,ht0,ht1,hx⟩
    refine ⟨t,ht0,ht1,normalize_injective u v huv ?_⟩
    rw [normalize_affinePoint]
    exact hx
  · rintro ⟨t,ht0,ht1,hx⟩
    refine ⟨t,ht0,ht1,?_⟩
    rw [hx,normalize_affinePoint]

theorem normalize_generic {n : ℕ} (u v : PlanarPoint ℝ) (huv : u ≠ v)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    CyclicGeneric (fun i => normalize u v (q i)) := by
  refine ⟨hq.size_ge_three,?_,?_⟩
  · intro a b c hab hbc hac
    rw [normalize_det]
    exact mul_ne_zero (ne_of_gt (normSq_pos u v huv)) (hq.g1 a b c hab hbc hac)
  · intro e f g x hef hfg heg ⟨he,hf,hg⟩
    obtain ⟨t,ht0,ht1,hx⟩ := he
    let y := affinePoint (q e) (q (cyclicSuccessor e)) t
    have hyx : normalize u v y = x := by
      rw [normalize_affinePoint]
      exact hx.symm
    have hye : edgeInterior q e y := ⟨t,ht0,ht1,rfl⟩
    have hyf : edgeInterior q f y := by
      apply (normalize_segment_iff u v huv _ _ _).mp
      rw [hyx]
      exact hf
    have hyg : edgeInterior q g y := by
      apply (normalize_segment_iff u v huv _ _ _).mp
      rw [hyx]
      exact hg
    exact hq.g2 e f g y hef hfg heg ⟨hye,hyf,hyg⟩

theorem normalize_amplitude {n : ℕ} (u v : PlanarPoint ℝ) (huv : u ≠ v)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq = polygonAmplitude (fun i => normalize u v (q i))
      (normalize_generic u v huv q hq) := by
  apply polygonAmplitude_eq_of_oriented_triple_signs
  intro a b c _ _ _
  rw [normalize_det]
  exact (HorizontalShortEdge.scalarSignValue_positive_mul _ _ (normSq_pos u v huv)).symm

theorem chosen_endpoints_ne {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) : q (cyclicSuccessor e) ≠ q e := by
  intro heq
  exact cyclicSuccessor_ne_self (by have := hq.size_ge_three; omega) e
    (cyclicNoncollinear_injective hq.size_ge_three q hq.g1 heq)

def normalizedPolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ) (e : Fin n) :
    Fin n → PlanarPoint ℝ := fun i => normalize (q (cyclicSuccessor e)) (q e) (q i)

theorem normalizedPolygon_generic {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) : CyclicGeneric (normalizedPolygon q e) :=
  normalize_generic _ _ (chosen_endpoints_ne q hq e) q hq

theorem normalizedPolygon_leftward {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) :
    (normalizedPolygon q e e).2 = 0 ∧
    (normalizedPolygon q e (cyclicSuccessor e)).2 = 0 ∧
    (normalizedPolygon q e (cyclicSuccessor e)).1 < (normalizedPolygon q e e).1 := by
  dsimp [normalizedPolygon]
  rw [normalize_left,normalize_right]
  exact ⟨rfl,rfl,normSq_pos _ _ (chosen_endpoints_ne q hq e)⟩

theorem normalizedPolygon_amplitude {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) : polygonAmplitude q hq =
    polygonAmplitude (normalizedPolygon q e) (normalizedPolygon_generic q hq e) :=
  normalize_amplitude _ _ (chosen_endpoints_ne q hq e) q hq

theorem normalize_edgeIntersection_iff {n : ℕ} (u v : PlanarPoint ℝ)
    (huv : u ≠ v) (q : Fin n → PlanarPoint ℝ) (e f : Fin n) :
    (∃ x, edgeInterior (fun i => normalize u v (q i)) e x ∧
      edgeInterior (fun i => normalize u v (q i)) f x) ↔
      ∃ x, edgeInterior q e x ∧ edgeInterior q f x := by
  constructor
  · rintro ⟨x,⟨t,ht0,ht1,hx⟩,hf⟩
    let y := affinePoint (q e) (q (cyclicSuccessor e)) t
    have hyx : normalize u v y = x := by
      rw [normalize_affinePoint]
      exact hx.symm
    refine ⟨y,⟨t,ht0,ht1,rfl⟩,?_⟩
    apply (normalize_segment_iff u v huv _ _ _).mp
    rw [hyx]
    exact hf
  · rintro ⟨x,he,hf⟩
    exact ⟨normalize u v x,(normalize_segment_iff u v huv _ _ _).mpr he,
      (normalize_segment_iff u v huv _ _ _).mpr hf⟩

def crossingEquiv {n : ℕ} (u v : PlanarPoint ℝ) (huv : u ≠ v)
    (q : Fin n → PlanarPoint ℝ) :
    PolygonCrossing q ≃ PolygonCrossing (fun i => normalize u v (q i)) :=
  Equiv.subtypeEquivRight (fun p => and_congr_right fun _ =>
    (normalize_edgeIntersection_iff u v huv q p.1 p.2).symm)

theorem crossingEquiv_labels {n : ℕ} (u v : PlanarPoint ℝ) (huv : u ≠ v)
    (q : Fin n → PlanarPoint ℝ) (c : PolygonCrossing q) :
    (crossingEquiv u v huv q c).val = c.val := rfl

theorem normalize_crossingPoint {n : ℕ} (u v : PlanarPoint ℝ) (huv : u ≠ v)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (c : PolygonCrossing q) :
    crossingPoint (fun i => normalize u v (q i)) (crossingEquiv u v huv q c) =
      normalize u v (crossingPoint q c) := by
  symm
  apply crossingPoint_eq_of_mem hq.size_ge_three _ (normalize_generic u v huv q hq).g1
  · exact (normalize_segment_iff u v huv _ _ _).mpr (crossingPoint_mem_left q c)
  · exact (normalize_segment_iff u v huv _ _ _).mpr (crossingPoint_mem_right q c)

theorem normalize_crossingParameters {n : ℕ} (u v : PlanarPoint ℝ) (huv : u ≠ v)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (c : PolygonCrossing q) :
    crossingParameterLeft (fun i => normalize u v (q i)) (crossingEquiv u v huv q c) =
      crossingParameterLeft q c ∧
    crossingParameterRight (fun i => normalize u v (q i)) (crossingEquiv u v huv q c) =
      crossingParameterRight q c := by
  have h := crossingParameters_unique hq.size_ge_three _
    (normalize_generic u v huv q hq).g1 (crossingEquiv u v huv q c)
    (crossingParameterLeft q c) (crossingParameterRight q c)
  have heq : affinePoint (q c.val.1) (q (cyclicSuccessor c.val.1))
      (crossingParameterLeft q c) =
      affinePoint (q c.val.2) (q (cyclicSuccessor c.val.2))
        (crossingParameterRight q c) :=
    (crossingParameterLeft_spec q c).2.2.symm.trans (crossingParameterRight_spec q c).2.2
  have h' := h (by
    simpa only [crossingEquiv_labels,← normalize_affinePoint] using
      (congrArg (normalize u v) heq))
  exact ⟨h'.1.symm,h'.2.symm⟩

end DirectGLSSW.EdgeAffineNormalization






















