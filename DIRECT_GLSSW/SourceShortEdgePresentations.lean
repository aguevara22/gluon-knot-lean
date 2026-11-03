import SourceCyclicShortEdgeCurrentTable
import DirectGLSSW.ShortEdgeCurrentTable
import DirectGLSSW.ShortEdgeFiberSums
import DirectGLSSW.ShortEdgeLeftEndpoint
import DirectGLSSW.ShortEdgeRightEndpoint
import DirectGLSSW.ShortEdgeSpanning
import DirectGLSSW.ShortEdgeSpanningPhi

namespace DirectGLSSW.ShortEdgeCurrentGeometry.SourceCutPresentation

open DirectGLSSW
open DirectGLSSW.ShortEdgeCutFibers
open DirectGLSSW.ShortEdgeWeighted
open scoped BigOperators

/-- The actual left-endpoint fiber consists of precisely its unsplit and
short-leaf finite cut lists. -/
theorem source_left_endpoint_actual_fiber
    (a j : ℕ) (S : Finset ℕ) (hBj : a + 1 < j)
    (hS : S ⊆ Finset.Ioo a (ShortEdgeCutFibers.collapseAfter a j)) :
    ((Finset.Ioo a j).powerset.filter
      fun T => collapsedInteriorCuts a a j T = S) =
      {leftEndpointCandidate a S .unsplit,
       leftEndpointCandidate a S .shortLeaf} :=
  ShortEdgeFiberSums.leftEndpoint_fiber_finset a j S hBj hS

/-- The actual right-endpoint fiber consists of precisely its unsplit and
short-leaf finite cut lists. -/
theorem source_right_endpoint_actual_fiber
    (a i : ℕ) (S : Finset ℕ) (hiA : i < a)
    (hS : S ⊆ Finset.Ioo (ShortEdgeCutFibers.collapseAfter a i) a) :
    ((Finset.Ioo i (a + 1)).powerset.filter
      fun T => collapsedInteriorCuts a i (a + 1) T = S) =
      {rightEndpointCandidate a S .unsplit,
       rightEndpointCandidate a S .shortLeaf} :=
  ShortEdgeFiberSums.rightEndpoint_fiber_finset a i S hiA hS

/-- If a strict spanning core cut set contains the collapsed cut, its actual
fiber consists of the three endpoint, endpoint, and both-endpoint lists. -/
theorem source_strict_spanning_three_actual_fiber
    (a i j : ℕ) (S : Finset ℕ) (hiA : i < a) (hBj : a + 1 < j)
    (haS : a ∈ S) (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j)) :
    ((Finset.Ioo i j).powerset.filter
      fun T => collapsedInteriorCuts a i j T = S) =
      {spanCandidate a S .cutAtA, spanCandidate a S .cutAtB,
       spanCandidate a S .cutAtBoth} :=
  ShortEdgeFiberSums.span_at_cut_fiber_finset a i j S hiA hBj haS hS

/-- If a strict spanning core cut set misses the collapsed cut, the actual
fiber is the unique lifted cut list. -/
theorem source_strict_spanning_single_actual_fiber
    (a i j : ℕ) (S : Finset ℕ) (hiA : i < a) (hBj : a + 1 < j)
    (haS : a ∉ S) (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j)) :
    ((Finset.Ioo i j).powerset.filter
      fun T => collapsedInteriorCuts a i j T = S) = {liftedCuts a S} :=
  ShortEdgeFiberSums.span_no_cut_fiber_finset a i j S hiA hBj haS hS

/-- The two left-endpoint lists have the exact source contribution factor;
this is the ordinary or marked formula according to η. -/
theorem source_left_endpoint_two_lift_weight
    (a j : ℕ) (ha : 0 < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo a (ShortEdgeCutFibers.collapseAfter a j)) :
    cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) a j (leftEndpointCandidate a S .unsplit) +
      cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) a j (leftEndpointCandidate a S .shortLeaf) =
      ((beta a t + η.value * (t (ShortEdgeCutFibers.collapseAfter a j)).value) / 2) *
        cutContribution (D0 a t D)
          (fun x k y => -η.value * H0 H x k y)
          U a (ShortEdgeCutFibers.collapseAfter a j) S :=
  ShortEdgeWeighted.LeftEndpointImpl.leftEndpointContribution_twoLifts
    a j ha hBj t U η D H S hS

/-- The two right-endpoint lists have their exact source contribution factor. -/
theorem source_right_endpoint_two_lift_weight
    (a i : ℕ) (ha : 0 < a) (hiA : i < a)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo (ShortEdgeCutFibers.collapseAfter a i) a) :
    cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i (a + 1) (rightEndpointCandidate a S .unsplit) +
      cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i (a + 1) (rightEndpointCandidate a S .shortLeaf) =
      ((alpha a ha t + η.value * (t (ShortEdgeCutFibers.collapseAfter a i)).value) / 2) *
        cutContribution (D0 a t D)
          (fun x k y => -η.value * H0 H x k y)
          U (ShortEdgeCutFibers.collapseAfter a i) a S :=
  ShortEdgeRightEndpoint.rightEndpointContribution_twoLifts
    a i ha hiA t U η D H S hS

/-- A strict spanning fiber containing the short cut has the exact sum of its
three actual cut-list contributions. -/
theorem source_strict_spanning_three_lift_weight
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    (S : Finset ℕ) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j)) :
    cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i j (spanCandidate a S .cutAtA) +
      cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i j (spanCandidate a S .cutAtB) +
      cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i j (spanCandidate a S .cutAtBoth) =
      kappa a ha t * cutContribution (D0 a t D)
        (fun x k y => -η.value * H0 H x k y) U i (ShortEdgeCutFibers.collapseAfter a j) S :=
  ShortEdgeWeighted.SpanningPhiImpl.spanContribution_threeLifts
    a i j ha hiA hBj t U η D H S haS hS

/-- With no cut at the short edge, the single actual lifted cut list carries
exactly the core contribution times κ. -/
theorem source_strict_spanning_single_lift_weight
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    (S : Finset ℕ) (haS : a ∉ S)
    (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j)) :
    cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i j (liftedCuts a S) =
      kappa a ha t * cutContribution (D0 a t D)
        (fun x k y => -η.value * H0 H x k y)
        U (ShortEdgeCutFibers.collapseAfter a i) (ShortEdgeCutFibers.collapseAfter a j) S :=
  ShortEdgeWeighted.spanNoCoreCutContribution
    a i j ha hiA hBj t U η D H S hS haS

/-- The inserted parent table satisfies the source equation E on every
interval, with the actual one-edge value distinguished from longer intervals. -/
theorem source_parent_table_equation_cases
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} (hij : i < j) :
    phi (D1 a t D) (H1 a t H)
        (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) i j =
      if j = i + 1 then 1 else 0 := by
  rw [ShortEdgeWeighted.CurrentTableImpl.parentTable_phi_ordinary a ha t D H hij]
  by_cases h : j = i + 1
  · simp [source, h]
  · simp [source, h]

/-- The source table is the actual ordinary current of the inserted sign
arrays, so the preceding finite cut-list formulas apply to the source current. -/
theorem source_parent_table_is_actual_current
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} (hij : i < j) :
    parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H)) i j =
      ordinaryCurrent (D1 a t D) (H1 a t H) i j :=
  ShortEdgeWeighted.CurrentTableImpl.parentTable_eq_ordinaryCurrent
    a ha t D H hij

/-- For a literal cyclic polygon and its short-edge insertion, the source
current has the actual parent-table presentation on every bounded interval. -/
theorem source_cyclic_actual_current_has_parent_table_presentation
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (hq : cyclicNoncollinear q) (a : Fin n) (v : PlanarPoint ℝ)
    (havoid : ∀ x : Fin n, x ≠ a → planarDet v (q x - q a) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ i j : ℕ, i < j → j ≤ n →
        ordinaryCurrent
            (D1 1 (ShortEdgeSignRealization.shortSign
              (sourceCoreWordBefore hn q a) 1 v)
              (H0 (ShortEdgeSignRealization.coreHSign
                (sourceCoreWordBefore hn q a))))
            (polygonSignArray (ShortEdgeSignStability.insertAfter
              (sourceCoreWordBefore hn q a) 1 ε v)) i j =
          parentTable 1 (by omega)
            (ShortEdgeSignRealization.shortSign
              (sourceCoreWordBefore hn q a) 1 v)
            (ordinaryCurrent
              (D0 1 (ShortEdgeSignRealization.shortSign
                (sourceCoreWordBefore hn q a) 1 v)
                (H0 (ShortEdgeSignRealization.coreHSign
                  (sourceCoreWordBefore hn q a))))
              (H0 (ShortEdgeSignRealization.coreHSign
                (sourceCoreWordBefore hn q a)))) i j :=
  source_cyclic_exists_shortEdge_actual_current_table hn q hq a v havoid

end DirectGLSSW.ShortEdgeCurrentGeometry.SourceCutPresentation
