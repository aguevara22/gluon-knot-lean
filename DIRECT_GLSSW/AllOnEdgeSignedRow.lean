import ChosenEdgeNormalization
import DirectGLSSW.MixedEdgeRootWeights
import DirectGLSSW.DaughterRootAmplitude
import DirectGLSSW.MixedEdgeRetainedWord
import EmptyDaughterWord

set_option autoImplicit false
open scoped BigOperators
namespace DirectGLSSW.AllOnEdgeSignedRow
open ChosenEdgeNormalization GeometricSmoothingWeights PolygonNonalternation
open MixedEdgeComponentRoots MixedEdgeRootWeights DaughterFirstReturn DaughterRootAmplitude
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- All nonalternating supports on a selected polygon edge, including empty. -/
def AllOnEdgeSupport (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) :=
  {T : Finset (DirectGLSSW.EdgeChord q e) //
    polygonNonalternating q hq.g2 (T.image Subtype.val)}

instance allOnEdgeSupportFintype (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) : Fintype (AllOnEdgeSupport q hq e) := by
  unfold AllOnEdgeSupport
  infer_instance

/-- The signed all-on-edge row includes the empty support with sign +1. -/
def allOnEdgeSignedRow (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n)
    (hAux : auxiliaryGenericity q hq) : ℚ :=
  ∑ T : AllOnEdgeSupport q hq e,
    (-1 : ℚ)^T.val.card *
      componentAmplitudeProduct q hq (T.val.image Subtype.val) hAux T.property


/-- The empty support's actual component product is the polygon amplitude. -/
theorem empty_componentAmplitudeProduct_eq_polygonAmplitude
    (hRI : GLSSWRootIndependence) (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n)
    (hAux : auxiliaryGenericity q hq) :
    componentAmplitudeProduct q hq ∅ hAux (by simp [polygonNonalternating]) =
      polygonAmplitude q hq := by
  classical
  let T : Finset (EdgeChord q e) := ∅
  have hNA : polygonNonalternating q hq.g2 (T.image Subtype.val) := by simp [T, polygonNonalternating]
  change componentAmplitudeProduct q hq (T.image Subtype.val) hAux hNA = _
  rw [MixedEdgeRootWeights.componentAmplitudeProduct_eq_edgeRootProduct
    hRI q hq e T hAux hNA]
  simp only [T, Finset.image_empty]
  simp [EdgeRoot, rootEvent]
  let root0 : PolygonEvent q := Sum.inl ⟨0, by have := hq.size_ge_three; omega⟩
  have hcycle : (polygonEventSuccessor q hq.g2).SameCycle (Sum.inl e) root0 :=
    (polygonEventSuccessor_isCycleOn q hq.g2).2 (Set.mem_univ _) (Set.mem_univ _)
  have hcycleDart : (smoothingDartPermutation q hq.g2 ∅).SameCycle (Sum.inl e) root0 := by
    simpa [smoothingDartPermutation_empty] using hcycle
  have hrot := DaughterRootRotation.daughterPointList_isRotated_of_sameCycle
    q hq.g2 ∅ (Sum.inl e) root0 hcycleDart
  have hn : 0 < n := by have := hq.size_ge_three; omega
  have hlist : List.ofFn q ~r
      List.ofFn (fun i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 ∅ (Sum.inl e))) =>
        DaughterFirstReturn.daughterVertex q hq.g2 ∅ (Sum.inl e) i) := by
    rw [_root_.DirectGLSSW.EmptyDaughterWord.empty_daughterPointList_zero hn q hq.g2] at hrot
    exact hrot.symm
  have hamp := DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI hq hlist
  exact hamp.symm

/-- Nonempty all-on-edge supports are exactly the existing chosen-edge supports. -/
def NonemptyAllOnEdgeSupport (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) :=
  {T : AllOnEdgeSupport q hq e // T.val.Nonempty}

instance nonemptyAllOnEdgeSupportFintype (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) : Fintype (NonemptyAllOnEdgeSupport q hq e) := by
  unfold NonemptyAllOnEdgeSupport AllOnEdgeSupport
  infer_instance

def nonemptyAllOnEdgeSupportEquiv (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) :
    NonemptyAllOnEdgeSupport q hq e ≃ ChosenEdgeSeparatingSupport q hq e where
  toFun T := ⟨T.val.val, T.property, T.val.property⟩
  invFun T := ⟨⟨T.val, T.property.2⟩, T.property.1⟩
  left_inv T := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl

def allOnEdgeSupportEquivOption (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) :
    AllOnEdgeSupport q hq e ≃ Option (ChosenEdgeSeparatingSupport q hq e) where
  toFun T := if h : T.val.Nonempty then
      some (nonemptyAllOnEdgeSupportEquiv q hq e ⟨T, h⟩) else none
  invFun
    | none => ⟨∅, by simp [AllOnEdgeSupport, polygonNonalternating]⟩
    | some T => (nonemptyAllOnEdgeSupportEquiv q hq e).symm T |>.val
  left_inv T := by
    by_cases h : T.val.Nonempty
    · simp [h, nonemptyAllOnEdgeSupportEquiv]
    · have hT : T.val = ∅ := (Finset.not_nonempty_iff_eq_empty.mp h)
      apply Subtype.ext
      simpa [h, hT, AllOnEdgeSupport, polygonNonalternating]
  right_inv T := by
    cases T with
    | none => simp [AllOnEdgeSupport, polygonNonalternating]
    | some T => simp [T.property.1, nonemptyAllOnEdgeSupportEquiv]

/-- Partitioning the all-on-edge row gives the empty term plus its nonempty terms. -/
theorem allOnEdgeSignedRow_eq_empty_add_chosenEdgeTerms
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hAux : auxiliaryGenericity q hq) :
    allOnEdgeSignedRow q hq e hAux =
      componentAmplitudeProduct q hq ∅ hAux (by simp [polygonNonalternating]) +
        ∑ T : ChosenEdgeSeparatingSupport q hq e,
          (-1 : ℚ)^T.val.card *
            componentAmplitudeProduct q hq (T.val.image Subtype.val) hAux T.property.2 := by
  classical
  unfold allOnEdgeSignedRow
  let E := allOnEdgeSupportEquivOption q hq e
  trans ∑ T : Option (ChosenEdgeSeparatingSupport q hq e),
      (-1 : ℚ)^((E.symm T).val.card) *
        componentAmplitudeProduct q hq ((E.symm T).val.image Subtype.val) hAux (E.symm T).property
  · apply Fintype.sum_equiv E
    intro T
    simp [E]
  · simp [E, allOnEdgeSupportEquivOption, Fintype.sum_option,
      nonemptyAllOnEdgeSupportEquiv, AllOnEdgeSupport, polygonNonalternating]


/-- The exact sign shift on the nonempty supports is minus the existing sum. -/
theorem chosenEdgeTerms_eq_neg_chosenEdgeSmoothingSum
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hAux : auxiliaryGenericity q hq) :
    (∑ T : ChosenEdgeSeparatingSupport q hq e,
      (-1 : ℚ)^T.val.card *
        componentAmplitudeProduct q hq (T.val.image Subtype.val) hAux T.property.2) =
      -chosenEdgeSmoothingSum q hq e hAux := by
  classical
  unfold chosenEdgeSmoothingSum
  calc
    _ = ∑ T : ChosenEdgeSeparatingSupport q hq e,
        -(((-1 : ℚ)^(T.val.card+1)) *
          componentAmplitudeProduct q hq (T.val.image Subtype.val) hAux T.property.2) := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [pow_succ]
          ring
    _ = -∑ T : ChosenEdgeSeparatingSupport q hq e,
        (-1 : ℚ)^(T.val.card+1) *
          componentAmplitudeProduct q hq (T.val.image Subtype.val) hAux T.property.2 :=
          Finset.sum_neg_distrib

/-- The signed all-on-edge row is the empty amplitude minus the source nonempty sum. -/
theorem allOnEdgeSignedRow_eq_emptyTerm_sub_chosenEdgeSmoothingSum
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hAux : auxiliaryGenericity q hq) :
    allOnEdgeSignedRow q hq e hAux =
      componentAmplitudeProduct q hq ∅ hAux (by simp [polygonNonalternating]) -
        chosenEdgeSmoothingSum q hq e hAux := by
  rw [allOnEdgeSignedRow_eq_empty_add_chosenEdgeTerms,
    chosenEdgeTerms_eq_neg_chosenEdgeSmoothingSum]
  ring


/-- The exact generic single-polygon mixed-edge row, with the empty support included. -/
theorem allOnEdgeSignedRow_eq_amplitude_sub_chosenEdgeSmoothingSum
    (hRI : GLSSWRootIndependence) (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n)
    (hAux : auxiliaryGenericity q hq) :
    allOnEdgeSignedRow q hq e hAux =
      polygonAmplitude q hq - chosenEdgeSmoothingSum q hq e hAux := by
  rw [allOnEdgeSignedRow_eq_emptyTerm_sub_chosenEdgeSmoothingSum,
    empty_componentAmplitudeProduct_eq_polygonAmplitude hRI q hq e hAux]














end
end DirectGLSSW.AllOnEdgeSignedRow
