import DirectGLSSW.DaughterCarrier
import DirectGLSSW.ShortEdgeGenericity

set_option autoImplicit false
namespace DirectGLSSW.DaughterClosedContainment
noncomputable section
open DaughterFirstReturn EventSegmentGeometry ShortEdgeGenericity
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ)
variable (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))

/-- Both endpoints use the same actual parent edge, with ordered parameters
in its closed unit interval. No daughter genericity is assumed. -/
theorem daughterSide_endpoint_parameters (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
      daughterVertex q hG2 S root i =
        affinePoint (q (daughterCarrier q hG2 S root i))
          (q (cyclicSuccessor (daughterCarrier q hG2 S root i))) s ∧
      daughterVertex q hG2 S root (cyclicSuccessor i) =
        affinePoint (q (daughterCarrier q hG2 S root i))
          (q (cyclicSuccessor (daughterCarrier q hG2 S root i))) t := by
  classical
  let c := cornerEnumeration q hG2 S root i
  let d := cornerGap q hG2 S root c.val (cornerSuccessor q hG2 S root c).val
  let start := orbitEventAt q hG2 S root c.val
  let z := lastDartStart q hG2 S root c
  let terminal := terminalEvent q hG2 z
  let e := polygonEventEdge q start
  let u := polygonEventSuccessorTerminalParameter q hG2 hn z
  have hfr := cornerSuccessor_is_firstReturn q hG2 S hn root hroot c
  rcases hfr with ⟨hdpos, hnext, _, hpoint, _, _⟩
  have hd : 0 < d := hdpos
  have hlast : d - 1 < d := Nat.sub_lt hd (by omega)
  have hpref := orbitPrefix_edge_parameter q hG2 S hn root hroot c (d-1) hlast
  have hzedge : polygonEventEdge q z = e := by
    simpa [z, start, lastDartStart, e] using hpref.1
  have hzparam : polygonEventParameter q start ≤ polygonEventParameter q z := by
    simpa [z, start, lastDartStart] using hpref.2
  have hpositive := polygonEventSuccessor_positive_elementary_step q hG2 hn z
  dsimp at hpositive
  rcases hpositive with ⟨hlt, hu1, _, hterminalPoint, _⟩
  have hterminalAffine : polygonEventPoint q terminal =
      affinePoint (q e) (q (cyclicSuccessor e)) u := by
    simpa [terminal, terminalEvent, z, e, u, hzedge] using hterminalPoint
  have hcornerSucc : cornerEnumeration q hG2 S root (cyclicSuccessor i) =
      cornerSuccessor q hG2 S root c := by
    rw [cornerEnumeration_successor]
  have hvertexNext : daughterVertex q hG2 S root (cyclicSuccessor i) =
      polygonEventPoint q terminal := by
    change polygonEventPoint q
      (orbitEventAt q hG2 S root
        (cornerEnumeration q hG2 S root (cyclicSuccessor i)).val) = _
    rw [hcornerSucc, ← hnext, hpoint]
  refine ⟨polygonEventParameter q start, u, (polygonEventParameter_bounds q start).1,
    lt_of_le_of_lt hzparam hlt, hu1, ?_, ?_⟩
  · exact polygonEventPoint_eq_affine q start
  · exact hvertexNext.trans hterminalAffine

/-- Every closed daughter side lies on its actual parent closed side. -/
theorem daughter_closed_edge_on_parent (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) (x : PlanarPoint ℝ)
    (hx : edgeClosed (daughterVertex q hG2 S root) i x) :
    edgeClosed q (daughterCarrier q hG2 S root i) x := by
  obtain ⟨s,t,hs0,hst,ht1,hs,ht⟩ :=
    daughterSide_endpoint_parameters q hG2 S hn root hroot i
  obtain ⟨r,hr0,hr1,hx⟩ := hx
  have ht0 : 0 ≤ t := le_trans hs0 (le_of_lt hst)
  have hs1 : s ≤ 1 := le_trans (le_of_lt hst) ht1
  refine ⟨(1-r)*s+r*t, ?_, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hr1) hs0) (mul_nonneg hr0 ht0)
  · calc
      (1-r)*s+r*t ≤ (1-r)*1+r*1 := add_le_add
        (mul_le_mul_of_nonneg_left hs1 (sub_nonneg.mpr hr1))
        (mul_le_mul_of_nonneg_left ht1 hr0)
      _ = 1 := by ring
  · rw [hx, hs, ht]
    ext <;> simp [affinePoint] <;> ring

/-- Parent genericity and actual nonalternation imply daughter G2.
This does not assert daughter G1 or full daughter genericity. -/
theorem daughter_no_triple (hq : CyclicGeneric q)
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (root : PolygonEvent q) (hroot : retainedCorner q S root) :
    cyclicNoTripleIntersections (daughterVertex q hq.g2 S root) := by
  intro e f g x hef hfg heg hthree
  have hinj := daughterCarrier_injective q hq.g2 S hq.size_ge_three hNA root
  apply cyclic_no_three_closed_edges q hq
    (daughterCarrier q hq.g2 S root e)
    (daughterCarrier q hq.g2 S root f)
    (daughterCarrier q hq.g2 S root g) x
    (fun h => hef (hinj h)) (fun h => hfg (hinj h)) (fun h => heg (hinj h))
  have lift : ∀ j, edgeInterior (daughterVertex q hq.g2 S root) j x →
      edgeClosed q (daughterCarrier q hq.g2 S root j) x := by
    intro j hj
    obtain ⟨t,ht0,ht1,htx⟩ := hj
    exact daughter_closed_edge_on_parent q hq.g2 S hq.size_ge_three root hroot j x
      ⟨t,le_of_lt ht0,le_of_lt ht1,htx⟩
  exact ⟨lift e hthree.1, lift f hthree.2.1, lift g hthree.2.2⟩

end
end DirectGLSSW.DaughterClosedContainment



