import CellEventOrders
import DirectGLSSW.MixedCellOrbitWord
import DirectGLSSW.CapEventInterpretation
import MixedCellWeights
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
open scoped BigOperators
namespace DirectGLSSW.AllCellCapMatrix
open MixedConsecutiveCapWord SelectedCellClippedWord ExtendedReturnArcGeometry
open OrderedCapEvents CrossingCapPairing DaughterFirstReturn DaughterRootAmplitude
open GeometricSmoothingWeights MixedCellWeights MixedCellOrbitWord CellEventOrders

variable {n : ℕ}

/-- Intermediate word bridge: actual daughter genericity transfers to the clipped cap.
Both list identities are explicit inputs here; the all-cell wrapper below derives them. -/
theorem selected_cap_generic_of_cell_word
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (L : List (DirectGLSSW.EdgeChord q e)) (i : Fin (L.length+1))
    (Q : ℕ → PlanarPoint ℝ) (c d : ℝ) (k l : ℕ)
    (hD : CyclicGeneric (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i)))
    (hDword : daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i) =
      (cellEventWord q hq e L i).map (polygonEventPoint q))
    (hCword : List.ofFn (crossingClippedCapWord Q c d k l) =
      ((cellEventWord q hq e L i).map (polygonEventPoint q)).rotate 1) :
    CyclicGeneric (crossingClippedCapWord Q c d k l) := by
  apply cyclicGeneric_ofFn_isRotated (q := daughterVertex q hq.g2 (supportOfList q e L)
    (cellRootEvent q e L i)) _ hD
  refine ⟨1,?_⟩
  change (daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i)).rotate 1 = _
  rw [hDword]
  exact hCword.symm

/-- Intermediate amplitude bridge, with explicit root independence and derived cap genericity. -/
theorem selected_cap_amplitude_of_cell_word (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (L : List (DirectGLSSW.EdgeChord q e)) (i : Fin (L.length+1))
    (Q : ℕ → PlanarPoint ℝ) (c d : ℝ) (k l : ℕ)
    (hD : CyclicGeneric (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i)))
    (hDword : daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i) =
      (cellEventWord q hq e L i).map (polygonEventPoint q))
    (hCword : List.ofFn (crossingClippedCapWord Q c d k l) =
      ((cellEventWord q hq e L i).map (polygonEventPoint q)).rotate 1) :
    polygonAmplitude (crossingClippedCapWord Q c d k l)
      (selected_cap_generic_of_cell_word q hq e L i Q c d k l hD hDword hCword) =
      polygonAmplitude (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i)) hD := by
  have hrot : List.ofFn (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i)) ~r
      List.ofFn (crossingClippedCapWord Q c d k l) := by
    refine ⟨1,?_⟩
    change (daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i)).rotate 1 = _
    rw [hDword]
    exact hCword.symm
  exact (polygonAmplitude_ofFn_isRotated hRI hD hrot).symm

/-- All-cell actual cap genericity, derived from auxiliary daughter genericity and both proved all-cell words. -/
theorem actual_cell_cap_generic (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ)
    (hAux : auxiliaryGenericity q hq) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∀ (cU cV : EventIndex Q n) (F : DirectGLSSW.EdgeChord q e → EventIndex Q n),
    eventTime Q n cU = 0 →
    eventTime Q n cV = (q e).1-(q (cyclicSuccessor e)).1 →
    eventPair Q n cU = (1,2) → eventPair Q n cV = (n-1,n) →
    (∀ z, eventTime Q n (F z) = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
      eventPair Q n (F z) = (returnRank q e z+1,returnRank q e z+2)) →
    ∀ (L : List (DirectGLSSW.EdgeChord q e)) (_hL : OrderedEdgeSupport q hq e L)
      (i : Fin (L.length+1)),
    let a := leftBoundary cU F L i
    let b := rightBoundary cV F L i
    CyclicGeneric (crossingClippedCapWord Q (eventTime Q n a) (eventTime Q n b)
      (eventPair Q n a).1 (eventPair Q n b).1) := by
  dsimp only
  intro cU cV F htU htV hpU hpV hF L hL i
  have hNA := ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL
  have hD := hAux (supportOfList q e L) hNA (cellRootEvent q e L i)
  have hDword := MixedCellOrbitWord.daughterPointList_eq_cellEventWord q hq e
    (hV.trans hU.symm) hleft L hL i
  have hCword := actual_selected_cell_word q hq e hU hV hleft ε cU cV F
    htU htV hpU hpV hF L hL i
  exact selected_cap_generic_of_cell_word q hq e L i _ _ _ _ _ hD hDword hCword

/-- The actual selected clipped cap has the actual daughter amplitude.
Neither its genericity nor either point-word identity is an input premise. -/
theorem actual_cell_cap_amplitude (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ)
    (hAux : auxiliaryGenericity q hq) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∀ (cU cV : EventIndex Q n) (F : DirectGLSSW.EdgeChord q e → EventIndex Q n)
      (htU : eventTime Q n cU = 0)
      (htV : eventTime Q n cV = (q e).1-(q (cyclicSuccessor e)).1)
      (hpU : eventPair Q n cU = (1,2)) (hpV : eventPair Q n cV = (n-1,n))
      (hF : ∀ z, eventTime Q n (F z) = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
        eventPair Q n (F z) = (returnRank q e z+1,returnRank q e z+2))
      (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
      (i : Fin (L.length+1)),
    let a := leftBoundary cU F L i
    let b := rightBoundary cV F L i
    polygonAmplitude (crossingClippedCapWord Q (eventTime Q n a) (eventTime Q n b)
      (eventPair Q n a).1 (eventPair Q n b).1)
      (actual_cell_cap_generic q hq e hU hV hleft ε hAux cU cV F
        htU htV hpU hpV hF L hL i) =
      polygonAmplitude (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i))
        (hAux (supportOfList q e L)
          (ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL)
          (cellRootEvent q e L i)) := by
  dsimp only
  intro cU cV F htU htV hpU hpV hF L hL i
  have hNA := ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL
  have hD := hAux (supportOfList q e L) hNA (cellRootEvent q e L i)
  have hDword := MixedCellOrbitWord.daughterPointList_eq_cellEventWord q hq e
    (hV.trans hU.symm) hleft L hL i
  have hCword := actual_selected_cell_word q hq e hU hV hleft ε cU cV F
    htU htV hpU hpV hF L hL i
  exact selected_cap_amplitude_of_cell_word hRI q hq e L i _ _ _ _ _ hD hDword hCword


/-- Every actual selected cell's event-matrix entry is its actual daughter amplitude.
All orders, cap genericity and word identities are derived from the stated geometry. -/
theorem actual_cell_eventMatrix_eq_daughter (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ)
    (hAux : auxiliaryGenericity q hq) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∀ (cU cV : EventIndex Q n) (F : DirectGLSSW.EdgeChord q e → EventIndex Q n)
      (_htU : eventTime Q n cU = 0)
      (_htV : eventTime Q n cV = (q e).1-(q (cyclicSuccessor e)).1)
      (_hpU : eventPair Q n cU = (1,2)) (_hpV : eventPair Q n cV = (n-1,n))
      (_hF : ∀ z, eventTime Q n (F z) = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
        eventPair Q n (F z) = (returnRank q e z+1,returnRank q e z+2))
      (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
      (i : Fin (L.length+1)),
    eventMatrix Q n (leftBoundary cU F L i) (rightBoundary cV F L i) =
      polygonAmplitude (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i))
        (hAux (supportOfList q e L)
          (ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL)
          (cellRootEvent q e L i)) := by
  dsimp only
  intro cU cV F htU htV hpU hpV hF L hL i
  let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
  have hzero : (Q 0).2 = 0 := by
    dsimp only [Q]
    rw [extendedArc_zero,InteriorEdgeEvents.opened_zero]
    exact hU
  have hord := actual_cell_orders q hq e hU hV hleft Q n cU cV F htU htV hpU hpV hF L hL i
  have hcap := actual_cell_cap_generic q hq e hU hV hleft ε hAux
    cU cV F htU htV hpU hpV hF L hL i
  exact (CapEventInterpretation.eventMatrix_eq_cap_amplitude hRI Q n hzero _ _
    hord.1 hord.2 hcap).trans (actual_cell_cap_amplitude hRI q hq e hU hV hleft ε hAux
      cU cV F htU htV hpU hpV hF L hL i)

/-- The product of actual event-matrix cell weights is the actual smoothing-component product. -/
theorem actual_cell_eventMatrix_product_eq_componentProduct (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ)
    (hAux : auxiliaryGenericity q hq) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∀ (cU cV : EventIndex Q n) (F : DirectGLSSW.EdgeChord q e → EventIndex Q n),
    eventTime Q n cU = 0 →
    eventTime Q n cV = (q e).1-(q (cyclicSuccessor e)).1 →
    eventPair Q n cU = (1,2) → eventPair Q n cV = (n-1,n) →
    (∀ z, eventTime Q n (F z) = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
      eventPair Q n (F z) = (returnRank q e z+1,returnRank q e z+2)) →
    ∀ (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L),
    (∏ i : Fin (L.length+1),
      eventMatrix Q n (leftBoundary cU F L i) (rightBoundary cV F L i)) =
      componentAmplitudeProduct q hq (supportOfList q e L) hAux
        (ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL) := by
  dsimp only
  intro cU cV F htU htV hpU hpV hF L hL
  rw [componentAmplitudeProduct_eq_cellProduct hRI q hq e (hV.trans hU.symm) hleft L hL hAux]
  apply Finset.prod_congr rfl
  intro i _
  exact actual_cell_eventMatrix_eq_daughter hRI q hq e hU hV hleft ε hAux
    cU cV F htU htV hpU hpV hF L hL i

/-- Positive endpoint extension supplies the actual endpoint events and interior-event
bijection, and every selected-cell matrix weight and their product are identified.
No critical-root injectivity or upper bound on the extension parameter is used. -/
theorem exists_actual_cell_weights (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0 < ε)
    (hAux : auxiliaryGenericity q hq) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    let ℓ := (q e).1-(q (cyclicSuccessor e)).1
    ∃ (cU cV : EventIndex Q n)
      (E : DirectGLSSW.EdgeChord q e ≃
        {c : EventIndex Q n // 0 < eventTime Q n c ∧ eventTime Q n c < ℓ}),
      eventTime Q n cU = 0 ∧ eventTime Q n cV = ℓ ∧
      eventPair Q n cU = (1,2) ∧ eventPair Q n cV = (n-1,n) ∧ cU < cV ∧
      (∀ z, eventTime Q n (E z).val = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
        eventPair Q n (E z).val = (returnRank q e z+1,returnRank q e z+2)) ∧
      (∀ (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L),
        (∀ i : Fin (L.length+1),
          eventMatrix Q n (leftBoundary cU (fun z => (E z).val) L i)
            (rightBoundary cV (fun z => (E z).val) L i) =
          polygonAmplitude (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i))
            (hAux (supportOfList q e L)
              (ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL)
              (cellRootEvent q e L i))) ∧
        (∏ i : Fin (L.length+1),
          eventMatrix Q n (leftBoundary cU (fun z => (E z).val) L i)
            (rightBoundary cV (fun z => (E z).val) L i)) =
        componentAmplitudeProduct q hq (supportOfList q e L) hAux
          (ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL)) := by
  dsimp only
  obtain ⟨cU,cV,E,htU,htV,hpU,hpV,hord,hE,_⟩ :=
    exists_actual_selected_cell_words q hq e hU hV hleft ε hε
  refine ⟨cU,cV,E,htU,htV,hpU,hpV,hord,hE,?_⟩
  intro L hL
  constructor
  · intro i
    exact actual_cell_eventMatrix_eq_daughter hRI q hq e hU hV hleft ε hAux
      cU cV (fun z => (E z).val) htU htV hpU hpV hE L hL i
  · exact actual_cell_eventMatrix_product_eq_componentProduct hRI q hq e hU hV hleft ε hAux
      cU cV (fun z => (E z).val) htU htV hpU hpV hE L hL


end DirectGLSSW.AllCellCapMatrix









