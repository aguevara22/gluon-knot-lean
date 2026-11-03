import ConfigurationDaughterTransport
import DirectGLSSW.GeometricSmoothingWeights
import DirectGLSSW.TruncationPointListAdapter

set_option autoImplicit false
namespace DirectGLSSW.DaughterCoordinateStability
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
open ConfigurationEventOrder ConfigurationSmoothingTransport ConfigurationDaughterTransport
open DaughterFirstReturn GeometricSmoothingWeights TruncationPointListAdapter
open Filter Topology
noncomputable section

variable {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)

def baseWordVertex (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
    (i : Fin (retainedLabelWord P hP S root).length) : PlanarPoint ℝ :=
  polygonEventPoint P ((retainedLabelWord P hP S root)[i.val])

theorem ofFn_baseWordVertex (S : Finset (PolygonCrossing P)) (root : PolygonEvent P) :
    List.ofFn (baseWordVertex P hP S root) = daughterPointList P hP.g2 S root := by
  classical
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map]
  exact List.ofFn_getElem_eq_map (retainedLabelWord P hP S root) (polygonEventPoint P)

theorem baseWord_generic (hAux : auxiliaryGenericity P hP)
    (S : Finset (PolygonCrossing P)) (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P) : CyclicGeneric (baseWordVertex P hP S root) :=
  cyclicGeneric_of_pointList_eq (daughterVertex P hP.g2 S root) (baseWordVertex P hP S root)
    (hAux S hS root) (ofFn_baseWordVertex P hP S root).symm

theorem baseWord_amplitude (hAux : auxiliaryGenericity P hP)
    (S : Finset (PolygonCrossing P)) (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P) :
    polygonAmplitude (baseWordVertex P hP S root) (baseWord_generic P hP hAux S hS root) =
      polygonAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root) :=
  polygonAmplitude_eq_of_pointList_eq _ _ _ _ (ofFn_baseWordVertex P hP S root)

theorem coordClose_self (η : ℝ) (hη : 0 < η) : CoordClose η P P := by
  intro i
  simpa only [sub_self,abs_zero] using And.intro hη hη

theorem eventEquiv_self
    (h : ∀ e f, edgeIntersection P e f ↔ edgeIntersection P e f) (x : PolygonEvent P) :
    eventEquiv P P h x = x := by
  cases x with
  | inl a => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    rw [eventEquiv_visit]
    congr 2

theorem mappedDaughterVertex_self (η : ℝ) (hη : 0 < η) (hBox : StableBox P η)
    (S : Finset (PolygonCrossing P)) (root : PolygonEvent P) :
    mappedDaughterVertex P hP η hBox S root ⟨P,coordClose_self P η hη⟩ =
      baseWordVertex P hP S root := by
  funext i
  simp only [mappedDaughterVertex,baseWordVertex,eventEquiv_self]

/-- The familiar coordinate box is a metric neighborhood; this only converts
between the already used CoordClose and the finite-product metric. -/
theorem coordClose_mem_nhds {m : ℕ} (R : Configuration m) (δ : ℝ) (hδ : 0 < δ) :
    {T | CoordClose δ T R} ∈ 𝓝 R := by
  have heq : {T | CoordClose δ T R} = Metric.ball R δ := by
    ext T
    simp only [Set.mem_setOf_eq,Metric.mem_ball,dist_pi_lt_iff hδ,CoordClose,
      Prod.dist_eq,Real.dist_eq,max_lt_iff]
  rw [heq]
  exact Metric.ball_mem_nhds R hδ

/-- One fixed daughter is locally generic with all its oriented triple signs and
rooted amplitude unchanged. Its original genericity is supplied only by hAux. -/
theorem eventually_daughter_stable (hAux : auxiliaryGenericity P hP)
    (η : ℝ) (hη : 0 < η) (hBox : StableBox P η)
    (S : Finset (PolygonCrossing P)) (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P) :
    ∀ᶠ Q in 𝓝 (⟨P,coordClose_self P η hη⟩ : Box P η),
      ∃ hR : CyclicGeneric (mappedDaughterVertex P hP η hBox S root Q),
        (∀ i k j, i ≠ k → k ≠ j → i ≠ j →
          scalarSignValue (planarDet
            (mappedDaughterVertex P hP η hBox S root Q k-mappedDaughterVertex P hP η hBox S root Q j)
            (mappedDaughterVertex P hP η hBox S root Q i-mappedDaughterVertex P hP η hBox S root Q j)) =
          scalarSignValue (planarDet
            (baseWordVertex P hP S root k-baseWordVertex P hP S root j)
            (baseWordVertex P hP S root i-baseWordVertex P hP S root j))) ∧
        polygonAmplitude (mappedDaughterVertex P hP η hBox S root Q) hR =
          polygonAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root) := by
  obtain ⟨δ,hδ,hgood⟩ := exists_configurationNeighborhood_cyclicGeneric_and_signs_amplitude
    (baseWordVertex P hP S root) (baseWord_generic P hP hAux S hS root)
  have hnear : {R | CoordClose δ R (baseWordVertex P hP S root)} ∈
      𝓝 (mappedDaughterVertex P hP η hBox S root ⟨P,coordClose_self P η hη⟩) := by
    rw [mappedDaughterVertex_self P hP η hη hBox S root]
    exact coordClose_mem_nhds _ δ hδ
  have hev := (continuous_mappedDaughterVertex P hP η hBox S root).continuousAt.eventually hnear
  filter_upwards [hev] with Q hQ
  obtain ⟨hR,hs,ha⟩ := hgood (mappedDaughterVertex P hP η hBox S root Q) hQ
  exact ⟨hR,hs,ha.trans (baseWord_amplitude P hP hAux S hS root)⟩

/-- One finite intersection handles every actual separating support and every
root simultaneously; no bound depends on a subsequently chosen support. -/
theorem eventually_all_daughters_stable (hAux : auxiliaryGenericity P hP)
    (η : ℝ) (hη : 0 < η) (hBox : StableBox P η) :
    ∀ᶠ Q in 𝓝 (⟨P,coordClose_self P η hη⟩ : Box P η),
      ∀ (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
        (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S),
      ∃ hR : CyclicGeneric (mappedDaughterVertex P hP η hBox S root Q),
        (∀ i k j, i ≠ k → k ≠ j → i ≠ j →
          scalarSignValue (planarDet
            (mappedDaughterVertex P hP η hBox S root Q k-mappedDaughterVertex P hP η hBox S root Q j)
            (mappedDaughterVertex P hP η hBox S root Q i-mappedDaughterVertex P hP η hBox S root Q j)) =
          scalarSignValue (planarDet
            (baseWordVertex P hP S root k-baseWordVertex P hP S root j)
            (baseWordVertex P hP S root i-baseWordVertex P hP S root j))) ∧
        polygonAmplitude (mappedDaughterVertex P hP η hBox S root Q) hR =
          polygonAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root) := by
  classical
  apply Filter.eventually_all.mpr
  intro S
  apply Filter.eventually_all.mpr
  intro root
  by_cases hS : PolygonNonalternation.polygonNonalternating P hP.g2 S
  · filter_upwards [eventually_daughter_stable P hP hAux η hη hBox S hS root] with Q hQ
    exact fun _ => hQ
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hS h))











end
end DirectGLSSW.DaughterCoordinateStability
