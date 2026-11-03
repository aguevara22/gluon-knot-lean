import SharpDaughterDiagram
import LocalPolygonEventOrder
import LocalSupportConjugacy
import DirectGLSSW.HOMFLY.HOMFLYSignedDiagramIso

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace DirectGLSSW.HOMFLY.SharpDaughterSignedIsoOfOrientation

open DirectGLSSW PermutationOrbits PolygonDrawingBridge
open DirectGLSSW.TruncationDirection
open DirectGLSSW.HOMFLY.SharpDaughter
open DirectGLSSW.LocalCrossingTransport

private abbrev eventMap {n : ℕ} {q q' : Fin n → PlanarPoint ℝ}
    (E : PolygonCrossing q ≃ PolygonCrossing q') :=
  polygonEventMapEquiv E

private abbrev supportMap {n : ℕ} {q q' : Fin n → PlanarPoint ℝ}
    (E : PolygonCrossing q ≃ PolygonCrossing q') (S : Finset (PolygonCrossing q)) :=
  S.map E.toEmbedding

private abbrev componentEquiv {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2;
        eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) :=
  LocalSupportConjugacy.smoothingComponentMapEquiv
    q q' hq hq' E hlabels horder S

private abbrev componentMap {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2;
        eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S)) :=
  componentEquiv q q' hq hq' E hlabels horder S C

private theorem componentOf_map {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    componentEquiv q q' hq hq' E hlabels horder S
      (componentOf (smoothingDartPermutation q hq.g2 S) x) =
    componentOf (smoothingDartPermutation q' hq'.g2 (supportMap E S)) (eventMap E x) :=
  LocalSupportConjugacy.smoothingComponentMapEquiv_componentOf
    q q' hq hq' E hlabels horder S x

private def arcCarrierEquiv {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S)) :
    Arc q hq S C ≃ Arc q' hq' (supportMap E S)
      (componentMap q q' hq hq' E hlabels horder S C) := by
  let C' := componentMap q q' hq hq' E hlabels horder S C
  refine Equiv.subtypeEquiv (eventMap E) ?_
  intro x
  constructor
  · intro hx
    calc
      componentOf (P q' hq' (supportMap E S)) (eventMap E x) =
          componentEquiv q q' hq hq' E hlabels horder S
            (componentOf (P q hq S) x) :=
        (componentOf_map q q' hq hq' E hlabels horder S x).symm
      _ = componentMap q q' hq hq' E hlabels horder S C := congrArg
        (componentEquiv q q' hq hq' E hlabels horder S) hx
  · intro hx
    apply (componentEquiv q q' hq hq' E hlabels horder S).injective
    calc
      componentEquiv q q' hq hq' E hlabels horder S (componentOf (P q hq S) x) =
          componentOf (P q' hq' (supportMap E S)) (eventMap E x) :=
        componentOf_map q q' hq hq' E hlabels horder S x
      _ = componentEquiv q q' hq hq' E hlabels horder S C := hx

private def crossingFinMap {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q') :
    Fin (Parent q hq).nCrossing ≃ Fin (Parent q' hq').nCrossing :=
  (crossingFin q).symm.trans (E.trans (crossingFin q'))

private theorem crossingFinMap_inv_apply {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (c : Fin (Parent q hq).nCrossing) :
    (crossingFin q').symm (crossingFinMap q q' hq hq' E c) =
      E ((crossingFin q).symm c) := by
  change (crossingFin q').symm
      ((crossingFin q') (E ((crossingFin q).symm c))) = _
  exact (crossingFin q').symm_apply_apply _

private theorem outgoing_event_map {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (c : Fin (Parent q hq).nCrossing) (i : Fin 2) :
    eventMap E ((eventFin q).symm ((Parent q hq).outgoing c i)) =
      (eventFin q').symm ((Parent q' hq').outgoing (crossingFinMap q q' hq hq' E c) i) := by
  rw [outgoing_event q hq c i, outgoing_event q' hq'
    (crossingFinMap q q' hq hq' E c) i]
  rw [crossingFinMap_inv_apply q q' hq hq' E c]
  rfl

private def crossingCarrierEquiv {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S)) :
    Crossing q hq S C ≃ Crossing q' hq' (supportMap E S)
      (componentMap q q' hq hq' E hlabels horder S C) := by
  let C' := componentMap q q' hq hq' E hlabels horder S C
  refine Equiv.subtypeEquiv (crossingFinMap q q' hq hq' E) ?_
  intro c
  have hmem :
      (crossingFin q').symm (crossingFinMap q q' hq hq' E c) ∈ supportMap E S ↔
        (crossingFin q).symm c ∈ S := by
    rw [crossingFinMap_inv_apply q q' hq hq' E c]
    constructor
    · intro hm
      rcases Finset.mem_map.mp hm with ⟨d, hd, hde⟩
      have : d = (crossingFin q).symm c := E.injective hde
      simpa [this] using hd
    · intro hm
      exact Finset.mem_map.mpr ⟨(crossingFin q).symm c, hm, rfl⟩
  constructor
  · rintro ⟨hcS, hcC⟩
    refine ⟨?_, ?_⟩
    · intro hcS'
      exact hcS (hmem.mp hcS')
    · intro i
      rw [← outgoing_event_map q q' hq hq' E c i]
      exact (componentOf_map q q' hq hq' E hlabels horder S _).symm.trans
        (congrArg (componentEquiv q q' hq hq' E hlabels horder S) (hcC i))
  · intro hh
    rcases hh with ⟨hcS', hcC'⟩
    refine ⟨?_, ?_⟩
    · intro hcS
      exact hcS' (hmem.mpr hcS)
    · intro i
      apply (componentEquiv q q' hq hq' E hlabels horder S).injective
      exact (componentOf_map q q' hq hq' E hlabels horder S _).trans
        ((congrArg (componentOf (P q' hq' (supportMap E S)))
          (outgoing_event_map q q' hq hq' E c i)).trans (hcC' i))

private theorem arcCarrierEquiv_next {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (a : Arc q hq S C) :
    arcCarrierEquiv q q' hq hq' E hlabels horder S C
        (fibrePerm (P q hq S) C a) =
      fibrePerm (P q' hq' (supportMap E S))
        (componentMap q q' hq hq' E hlabels horder S C)
        (arcCarrierEquiv q q' hq hq' E hlabels horder S C a) := by
  apply Subtype.ext
  exact LocalSupportConjugacy.smoothingDartPermutation_map
    q q' hq hq' E hlabels horder S a.val

private theorem arcCarrierEquiv_out {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (c : Crossing q hq S C) (i : Fin 2) :
    arcCarrierEquiv q q' hq hq' E hlabels horder S C (out q hq S C c i) =
      out q' hq' (supportMap E S)
        (componentMap q q' hq hq' E hlabels horder S C)
        (crossingCarrierEquiv q q' hq hq' E hlabels horder S C c) i := by
  apply Subtype.ext
  exact outgoing_event_map q q' hq hq' E c.val i

private theorem arcCarrierEquiv_inc {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (c : Crossing q hq S C) (i : Fin 2) :
    arcCarrierEquiv q q' hq hq' E hlabels horder S C (inc q hq S C c i) =
      inc q' hq' (supportMap E S)
        (componentMap q q' hq hq' E hlabels horder S C)
        (crossingCarrierEquiv q q' hq hq' E hlabels horder S C c) i := by
  apply (fibrePerm (P q' hq' (supportMap E S))
    (componentMap q q' hq hq' E hlabels horder S C)).injective
  apply Subtype.ext
  change P q' hq' (supportMap E S)
      (eventMap E ((eventFin q).symm ((Parent q hq).incoming c.val i))) =
    P q' hq' (supportMap E S)
      ((eventFin q').symm ((Parent q' hq').incoming
        (crossingCarrierEquiv q q' hq hq' E hlabels horder S C c).val i))
  rw [← LocalSupportConjugacy.smoothingDartPermutation_map
    q q' hq hq' E hlabels horder S]
  rw [p_incoming q hq S c.val c.property.1 i,
      p_incoming q' hq' (supportMap E S)
        (crossingCarrierEquiv q q' hq hq' E hlabels horder S C c).val
        (crossingCarrierEquiv q q' hq hq' E hlabels horder S C c).property.1 i]
  exact outgoing_event_map q q' hq hq' E c.val i

private def arcIndexEquiv {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (hNA' : PolygonNonalternation.polygonNonalternating q' hq'.g2 (supportMap E S)) :
    Fin (sharpDaughterDiagram q hq S C hNA).nArc ≃
      Fin (sharpDaughterDiagram q' hq' (supportMap E S)
        (componentMap q q' hq hq' E hlabels horder S C) hNA').nArc :=
  (arcEquiv q hq S C).trans
    ((arcCarrierEquiv q q' hq hq' E hlabels horder S C).trans
      (arcEquiv q' hq' (supportMap E S)
        (componentMap q q' hq hq' E hlabels horder S C)).symm)

private def crossingIndexEquiv {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (hNA' : PolygonNonalternation.polygonNonalternating q' hq'.g2 (supportMap E S)) :
    Fin (sharpDaughterDiagram q hq S C hNA).nCrossing ≃
      Fin (sharpDaughterDiagram q' hq' (supportMap E S)
        (componentMap q q' hq hq' E hlabels horder S C) hNA').nCrossing :=
  (crossingEquiv q hq S C).trans
    ((crossingCarrierEquiv q q' hq hq' E hlabels horder S C).trans
      (crossingEquiv q' hq' (supportMap E S)
        (componentMap q q' hq hq' E hlabels horder S C)).symm)

private theorem parent_overBranch_map {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (c : Fin (Parent q hq).nCrossing)
    (hpos : ∀ c : PolygonCrossing q,
      (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)) ↔
      (0 < planarDet (cyclicTangent q' (E c).val.1)
        (cyclicTangent q' (E c).val.2))) :
    (Parent q hq).overBranch c =
      (Parent q' hq').overBranch (crossingFinMap q q' hq hq' E c) := by
  let c₀ := (crossingFin q).symm c
  have hleft : crossingFin q c₀ = c := (crossingFin q).apply_symm_apply _
  have hinv := crossingFinMap_inv_apply q q' hq hq' E c
  have hright : crossingFinMap q q' hq hq' E c = crossingFin q' (E c₀) := by
    rfl
  change (positivePolygonEventDiagram q hq).overBranch c =
    (positivePolygonEventDiagram q' hq').overBranch
      (crossingFinMap q q' hq hq' E c)
  rw [hright, ← hleft,
    positivePolygonEventDiagram_overBranch q hq c₀,
    positivePolygonEventDiagram_overBranch q' hq' (E c₀)]
  have hbranch := hpos c₀
  by_cases hdet : 0 < planarDet (cyclicTangent q c₀.val.1)
    (cyclicTangent q c₀.val.2)
  · rw [if_pos hdet, if_pos (hbranch.mp hdet)]
  · have hdet' : ¬ 0 < planarDet (cyclicTangent q' (E c₀).val.1)
        (cyclicTangent q' (E c₀).val.2) := by
      intro h'
      exact hdet (hbranch.mpr h')
    rw [if_neg hdet, if_neg hdet']

private theorem arcIndexEquiv_apply {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (hNA' : PolygonNonalternation.polygonNonalternating q' hq'.g2 (supportMap E S))
    (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    arcEquiv q' hq' (supportMap E S)
        (componentMap q q' hq hq' E hlabels horder S C)
        (arcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a) =
      arcCarrierEquiv q q' hq hq' E hlabels horder S C (arcEquiv q hq S C a) :=
  (arcEquiv q' hq' (supportMap E S)
    (componentMap q q' hq hq' E hlabels horder S C)).apply_symm_apply _

private theorem crossingIndexEquiv_apply {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (hNA' : PolygonNonalternation.polygonNonalternating q' hq'.g2 (supportMap E S))
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) :
    crossingEquiv q' hq' (supportMap E S)
        (componentMap q q' hq hq' E hlabels horder S C)
        (crossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' c) =
      crossingCarrierEquiv q q' hq hq' E hlabels horder S C (crossingEquiv q hq S C c) :=
  (crossingEquiv q' hq' (supportMap E S)
    (componentMap q q' hq hq' E hlabels horder S C)).apply_symm_apply _

private theorem arcEquiv_incoming {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q))
    (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) (i : Fin 2) :
    arcEquiv q hq S C ((sharpDaughterDiagram q hq S C hNA).incoming c i) =
      inc q hq S C (crossingEquiv q hq S C c) i :=
  (arcEquiv q hq S C).apply_symm_apply _

private theorem arcEquiv_outgoing {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q))
    (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) (i : Fin 2) :
    arcEquiv q hq S C ((sharpDaughterDiagram q hq S C hNA).outgoing c i) =
      out q hq S C (crossingEquiv q hq S C c) i :=
  (arcEquiv q hq S C).apply_symm_apply _

/-- The actual finite signed diagrams of corresponding smoothing components
are isomorphic under crossing label/order transport that also preserves each
crossing's oriented tangent-determinant sign. This is a conditional internal
bridge; its determinant-sign input must be produced separately. -/
def sharpDaughter_signedDiagramIso_of_crossing_orientation {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2;
        eventMap E x < eventMap E y))
    (S : Finset (PolygonCrossing q))
    (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (hpos : ∀ c : PolygonCrossing q,
      (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)) ↔
      (0 < planarDet (cyclicTangent q' (E c).val.1)
        (cyclicTangent q' (E c).val.2))) :
    let S' := supportMap E S
    let C' := componentMap q q' hq hq' E hlabels horder S C
    let hNA' := (LocalSupportConjugacy.polygonNonalternating_map_iff
      q q' hq hq' E hlabels horder S).mp hNA
    SignedDiagramIso (sharpDaughterDiagram q hq S C hNA)
      (sharpDaughterDiagram q' hq' S' C' hNA') := by
  let S' := supportMap E S
  let C' := componentMap q q' hq hq' E hlabels horder S C
  let hNA' := (LocalSupportConjugacy.polygonNonalternating_map_iff
    q q' hq hq' E hlabels horder S).mp hNA
  refine {
    arcEquiv := arcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
    crossingEquiv := crossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
    incoming_map := ?_
    outgoing_map := ?_
    continuation_map := ?_
    through_map := ?_
    overBranch_map := ?_
    crossingSign_map := ?_ }
  · intro c i
    apply (arcEquiv q' hq' S' C').injective
    rw [arcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA',
      arcEquiv_incoming q hq S C hNA,
      arcEquiv_incoming q' hq' S' C' hNA',
      crossingIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA']
    exact arcCarrierEquiv_inc q q' hq hq' E hlabels horder S C
      (crossingEquiv q hq S C c) i
  · intro c i
    apply (arcEquiv q' hq' S' C').injective
    rw [arcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA',
      arcEquiv_outgoing q hq S C hNA,
      arcEquiv_outgoing q' hq' S' C' hNA',
      crossingIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA']
    exact arcCarrierEquiv_out q q' hq hq' E hlabels horder S C
      (crossingEquiv q hq S C c) i
  · intro a
    apply (arcEquiv q' hq' S' C').injective
    change arcEquiv q' hq' S' C'
        (arcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
          (next q hq S C a)) =
      arcEquiv q' hq' S' C'
        (next q' hq' S' C'
          (arcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a))
    rw [arcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA',
      arcEquiv_next, arcEquiv_next,
      arcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA']
    exact arcCarrierEquiv_next q q' hq hq' E hlabels horder S C
      (arcEquiv q hq S C a)
  · intro c
    rfl
  · intro c
    have hindex :
        oldCrossing q' hq' S' C'
          (crossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' c) =
        crossingFinMap q q' hq hq' E (oldCrossing q hq S C c) := by
      exact congrArg Subtype.val
        (crossingIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA' c)
    change (Parent q hq).overBranch (oldCrossing q hq S C c) =
      (Parent q' hq').overBranch
        (oldCrossing q' hq' S' C'
          (crossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' c))
    rw [hindex]
    exact parent_overBranch_map q q' hq hq' E (oldCrossing q hq S C c) hpos
  · intro c
    rw [sharpDaughterDiagram_crossingSign q hq S C hNA c,
      sharpDaughterDiagram_crossingSign q' hq' S' C' hNA'
        (crossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' c)]

end DirectGLSSW.HOMFLY.SharpDaughterSignedIsoOfOrientation
