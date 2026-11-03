import DirectGLSSW.EdgeNormalizationSmoothing
import LocalCrossingPointContinuity
import LocalSupportConjugacy

set_option autoImplicit false
namespace DirectGLSSW.LocalDaughterTransport
open DaughterFirstReturn PermutationOrbits
open LocalCrossingTransport
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual retained event sequence of a rooted smoothing daughter. -/
def daughterEventWord {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (root : PolygonEvent q) : List (PolygonEvent q) :=
  List.ofFn (fun i : Fin (Fintype.card (CornerCoord q hG2 S root)) =>
    orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val)

/-- Each old daughter index is evaluated at its fixed original event labels. -/
def daughterVertexFormula {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (root : PolygonEvent q) (q' : Fin n → PlanarPoint ℝ)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) : PlanarPoint ℝ :=
  eventPointFormula q q'
    (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val)

variable {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (hG2' : cyclicNoTripleIntersections q')
    (E : PolygonCrossing q ≃ PolygonCrossing q') (S : Finset (PolygonCrossing q))

/-- Actual visit transport preserves the retained-corner predicate. -/
theorem polygonEventMapEquiv_retained (x : PolygonEvent q) :
    retainedCorner q' (S.map E.toEmbedding) (polygonEventMapEquiv E x) ↔
      retainedCorner q S x := by
  cases x with
  | inl e => rfl
  | inr v =>
    change E v.1 ∈ S.map E.toEmbedding ↔ v.1 ∈ S
    simp

/-- Rooted retained daughter words commute with actual dart conjugacy. -/
theorem daughterEventWord_map
    (hdart : ∀ x, polygonEventMapEquiv E (smoothingDartPermutation q hG2 S x) =
      smoothingDartPermutation q' hG2' (S.map E.toEmbedding) (polygonEventMapEquiv E x))
    (root : PolygonEvent q) :
    daughterEventWord q' hG2' (S.map E.toEmbedding) (polygonEventMapEquiv E root) =
      (daughterEventWord q hG2 S root).map (polygonEventMapEquiv E) := by
  classical
  unfold daughterEventWord
  rw [DaughterPointListFilter.daughterEventList_eq_filtered_orbitWord,
    DaughterPointListFilter.daughterEventList_eq_filtered_orbitWord,
    EdgeAffineNormalization.orbitWord_map_equiv (polygonEventMapEquiv E) _ _ hdart,
    ← DaughterPointListFilter.map_filter_comp]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [polygonEventMapEquiv_retained]

/-- The actual daughter sizes agree, including for arbitrary unretained roots. -/
theorem daughterCard_eq
    (hdart : ∀ x, polygonEventMapEquiv E (smoothingDartPermutation q hG2 S x) =
      smoothingDartPermutation q' hG2' (S.map E.toEmbedding) (polygonEventMapEquiv E x))
    (root : PolygonEvent q) :
    Fintype.card (CornerCoord q hG2 S root) =
      Fintype.card (CornerCoord q' hG2' (S.map E.toEmbedding) (polygonEventMapEquiv E root)) := by
  have h := congrArg List.length (daughterEventWord_map q q' hG2 hG2' E S hdart root)
  simpa [daughterEventWord] using h.symm

/-- Actual daughter geometry equals the fixed old-index event formula list. -/
theorem daughterPointList_eq_formula (hq' : CyclicGeneric q')
    (hlabels : ∀ c, (E c).val = c.val)
    (hdart : ∀ x, polygonEventMapEquiv E (smoothingDartPermutation q hG2 S x) =
      smoothingDartPermutation q' hG2' (S.map E.toEmbedding) (polygonEventMapEquiv E x))
    (root : PolygonEvent q) :
    daughterPointList q' hG2' (S.map E.toEmbedding) (polygonEventMapEquiv E root) =
      List.ofFn (daughterVertexFormula q hG2 S root q') := by
  have h := congrArg (List.map (polygonEventPoint q'))
    (daughterEventWord_map q q' hG2 hG2' E S hdart root)
  simpa only [daughterEventWord, daughterPointList, daughterVertex,
    List.map_ofFn, List.map_map, Function.comp_def,
    polygonEventPoint_map_eq_formula q q' hq' E hlabels, daughterVertexFormula] using h

/-- List equality gives pointwise equality with the explicit cardinality cast. -/
theorem ofFn_eq_cast {α : Type*} {a b : ℕ} (f : Fin a → α) (g : Fin b → α)
    (hab : a = b) (h : List.ofFn g = List.ofFn f) (i : Fin a) :
    g (Fin.cast hab i) = f i := by
  subst b
  have hgf : g = f := List.ofFn_injective h
  exact congrFun hgf i

/-- Actual Fin-indexed daughter vertices align with old fixed event labels. -/
theorem daughterVertex_cast_eq_formula (hq' : CyclicGeneric q')
    (hlabels : ∀ c, (E c).val = c.val)
    (hdart : ∀ x, polygonEventMapEquiv E (smoothingDartPermutation q hG2 S x) =
      smoothingDartPermutation q' hG2' (S.map E.toEmbedding) (polygonEventMapEquiv E x))
    (root : PolygonEvent q) (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    daughterVertex q' hG2' (S.map E.toEmbedding) (polygonEventMapEquiv E root)
        (Fin.cast (daughterCard_eq q q' hG2 hG2' E S hdart root) i) =
      daughterVertexFormula q hG2 S root q' i := by
  apply ofFn_eq_cast
  exact daughterPointList_eq_formula q q' hG2 hG2' E S hq' hlabels hdart root

/-- The fixed-index daughter formula is continuous at the generic base time. -/
theorem daughterVertexFormula_continuousAt
    (Q : ℝ → Fin n → PlanarPoint ℝ) (hQ : ∀ v, Continuous (fun t => Q t v))
    (h0 : CyclicGeneric (Q 0)) (S₀ : Finset (PolygonCrossing (Q 0)))
    (root : PolygonEvent (Q 0))
    (i : Fin (Fintype.card (CornerCoord (Q 0) h0.g2 S₀ root))) :
    ContinuousAt (fun t => daughterVertexFormula (Q 0) h0.g2 S₀ root (Q t) i) 0 := by
  exact eventPointFormula_continuousAt Q hQ h0 _

/-- At the base polygon the fixed-label formula is the actual daughter vertex. -/
theorem daughterVertexFormula_self (hq : CyclicGeneric q)
    (root : PolygonEvent q) (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    daughterVertexFormula q hG2 S root q i = daughterVertex q hG2 S root i := by
  unfold daughterVertexFormula daughterVertex
  have h := polygonEventPoint_map_eq_formula q q hq (Equiv.refl _)
    (fun _ => rfl) (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val)
  have hmap (x : PolygonEvent q) : polygonEventMapEquiv (Equiv.refl _) x = x := by
    cases x with
    | inl e => rfl
    | inr v => rfl
  rw [hmap] at h
  exact h.symm

/-- The concrete event-order hypotheses imply daughter geometry transport. -/
theorem daughterPointList_eq_formula_of_order
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2;
        polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (root : PolygonEvent q) :
    daughterPointList q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) =
      List.ofFn (daughterVertexFormula q hq.g2 S root q') := by
  exact daughterPointList_eq_formula q q' hq.g2 hq'.g2 E S hq' hlabels
    (LocalSupportConjugacy.smoothingDartPermutation_map q q' hq hq' E hlabels horder S) root

/-- One parent event-order neighborhood simultaneously aligns all rooted daughters. -/
theorem exists_local_daughterPointList_formula
    (Q : ℝ → Fin n → PlanarPoint ℝ) (hQ : ∀ v, Continuous (fun t => Q t v))
    (h0 : CyclicGeneric (Q 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, |t| < δ →
      ∃ ht : CyclicGeneric (Q t),
      ∃ E : PolygonCrossing (Q 0) ≃ PolygonCrossing (Q t),
        (∀ c, (E c).val = c.val) ∧
        (∀ x y : PolygonEvent (Q 0),
          ((polygonEventOrder (Q 0) h0.g2).lt x y ↔
            (polygonEventOrder (Q t) ht.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y))) ∧
        ∀ (S₀ : Finset (PolygonCrossing (Q 0))) (root : PolygonEvent (Q 0)),
          daughterPointList (Q t) ht.g2 (S₀.map E.toEmbedding) (polygonEventMapEquiv E root) =
            List.ofFn (daughterVertexFormula (Q 0) h0.g2 S₀ root (Q t)) := by
  obtain ⟨δ, hδ, hg⟩ := exists_local_polygonEvent_order_equiv Q hQ h0
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  obtain ⟨hgt, E, hlabels, horder⟩ := hg t ht
  refine ⟨hgt, E, hlabels, horder, ?_⟩
  intro S₀ root
  exact daughterPointList_eq_formula_of_order (Q 0) (Q t) E S₀ h0 hgt hlabels horder root











end
end DirectGLSSW.LocalDaughterTransport
