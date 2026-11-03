import FixedEndpointSecantDensity
import DirectGLSSW.ConfigurationNeighborhood

set_option autoImplicit false
namespace DirectGLSSW.GenericSecantDensity
open FixedEndpointSecantDensity ExtendedReturnArcGeometry

theorem continuous_configuration_segment {n : ℕ} (P Q : Fin n → PlanarPoint ℝ) :
    Continuous (fun t : ℝ => fun i => affinePoint (P i) (Q i) t) := by
  apply continuous_pi
  intro i
  change Continuous (fun t : ℝ =>
    ((P i).1+t*((Q i).1-(P i).1),(P i).2+t*((Q i).2-(P i).2)))
  exact (continuous_const.add (continuous_id.mul continuous_const)).prodMk
    (continuous_const.add (continuous_id.mul continuous_const))

/-- An actual straight motion between two configurations stays in their coordinate box. -/
theorem affine_configuration_close {n : ℕ} (P Q : Fin n → PlanarPoint ℝ)
    (δ : ℝ) (hclose : ∀ i, |(Q i).1-(P i).1| < δ ∧ |(Q i).2-(P i).2| < δ)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ i, |(affinePoint (P i) (Q i) t).1-(P i).1| < δ ∧
      |(affinePoint (P i) (Q i) t).2-(P i).2| < δ := by
  intro i
  have hscalar (a b : ℝ) (hab : |b-a| < δ) : |(a+t*(b-a))-a| < δ := by
    have heq : (a+t*(b-a))-a = t*(b-a) := by ring
    rw [heq,abs_mul,abs_of_nonneg ht]
    calc
      t * |b-a| ≤ |b-a| := mul_le_of_le_one_left (abs_nonneg _) ht1
      _ < δ := hab
  exact ⟨hscalar _ _ (hclose i).1,hscalar _ _ (hclose i).2⟩

/-- Fixed-endpoint density within G1–G2, with the exact parent signs/amplitude
and a straight G1–G2 motion. This does not assert daughter genericity. -/
theorem exists_near_generic_regular_extension {n : ℕ} (hn : 3 ≤ n)
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (η : ℝ) (hη : 0 < η) :
    ∃ Q : Fin n → PlanarPoint ℝ, ∃ ε : ℝ, ∃ hQ : CyclicGeneric Q,
      Q (zeroIndex hn)=P (zeroIndex hn) ∧ Q (lastIndex hn)=P (lastIndex hn) ∧
      (∀ i, |(Q i).1-(P i).1| < η ∧ |(Q i).2-(P i).2| < η) ∧
      (∀ i k j, i≠k → k≠j → i≠j →
        scalarSignValue (planarDet (Q k-Q j) (Q i-Q j)) =
          scalarSignValue (planarDet (P k-P j) (P i-P j))) ∧
      polygonAmplitude Q hQ = polygonAmplitude P hP ∧
      0 < ε ∧ ε < geometricRadius hn Q ∧
      Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hn Q ε))
        ↑(CapCriticalTimes.criticalPairs (extendedArc hn Q ε) n) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∃ ht : CyclicGeneric (fun i => affinePoint (P i) (Q i) t),
          polygonAmplitude (fun i => affinePoint (P i) (Q i) t) ht =
            polygonAmplitude P hP) := by
  obtain ⟨δ,hδ,hlocal⟩ := exists_configurationNeighborhood_cyclicGeneric_and_signs_amplitude P hP
  obtain ⟨Q,ε,hQ0,hQn,hnear,hG1,hε,hbound,hroots⟩ :=
    exists_near_with_extendedArc_injective hn P hU hV hleft (min η δ) (lt_min hη hδ)
  have hnearη : ∀ i, |(Q i).1-(P i).1| < η ∧ |(Q i).2-(P i).2| < η := by
    intro i
    exact ⟨lt_of_lt_of_le (hnear i).1 (min_le_left _ _),
      lt_of_lt_of_le (hnear i).2 (min_le_left _ _)⟩
  have hnearδ : ∀ i, |(Q i).1-(P i).1| < δ ∧ |(Q i).2-(P i).2| < δ := by
    intro i
    exact ⟨lt_of_lt_of_le (hnear i).1 (min_le_right _ _),
      lt_of_lt_of_le (hnear i).2 (min_le_right _ _)⟩
  obtain ⟨hQ,hsigns,hamp⟩ := hlocal Q hnearδ
  refine ⟨Q,ε,hQ,hQ0,hQn,hnearη,hsigns,hamp,hε,hbound,hroots,?_⟩
  intro t ht ht1
  obtain ⟨hQt,_,hAt⟩ := hlocal (fun i => affinePoint (P i) (Q i) t)
    (affine_configuration_close P Q δ hnearδ t ht ht1)
  exact ⟨hQt,hAt⟩




end DirectGLSSW.GenericSecantDensity
