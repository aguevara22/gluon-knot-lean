import InteriorEdgeEvents
import ExtendedReturnEndpointEvents
import DirectGLSSW.ExtendedReturnClippedWord
import DirectGLSSW.EdgeAffineNormalization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceMixedEdgeExtendedArc
open EdgeAffineNormalization ExtendedReturnArcGeometry ExtendedReturnEndpointEvents
open InteriorEdgeEvents ExtendedReturnClippedWord CrossingCapPairing

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)

include hq in
/-- The coordinate change scales every oriented determinant by a positive number. -/
theorem chosen_coordinates_positive :
    0 < normSq (q (cyclicSuccessor e)) (q e) ∧
    ∀ a b c : PlanarPoint ℝ,
      planarDet
        (normalize (q (cyclicSuccessor e)) (q e) b - normalize (q (cyclicSuccessor e)) (q e) c)
        (normalize (q (cyclicSuccessor e)) (q e) a - normalize (q (cyclicSuccessor e)) (q e) c) =
      normSq (q (cyclicSuccessor e)) (q e) * planarDet (b-c) (a-c) :=
  ⟨normSq_pos _ _ (chosen_endpoints_ne q hq e), normalize_det _ _⟩

/-- Exact source extended return arc for any chosen edge. The vertices are the
positive-label word, so the moving label zero is not a retained arc vertex. -/
theorem exists_extended_arc_geometry :
    let P := normalizedPolygon q e ∘ cyclicVertexEquiv e
    let hn := hq.size_ge_three
    (P (zeroIndex hn)).2 = 0 ∧ (P (lastIndex hn)).2 = 0 ∧
    (P (zeroIndex hn)).1 < (P (lastIndex hn)).1 ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      cyclicNoncollinear (extendedWord hn P ε) ∧
      (∀ i : Fin n, (extendedWord hn P ε i).2 ≠ 0) ∧
      extendedArc hn P ε 1 = P (zeroIndex hn) + ε • (P (zeroIndex hn)-P (firstIndex hn)) ∧
      extendedArc hn P ε n = P (lastIndex hn) + ε • (P (lastIndex hn)-P (penultimateIndex hn)) ∧
      (∀ i : Fin n, 0 < i.val → i.val+1 < n → extendedArc hn P ε (i.val+1) = P i) ∧
      planarDet (extendedArc hn P ε 1-extendedArc hn P ε 2) (1,0) ≠ 0 ∧
      planarDet (extendedArc hn P ε (n-1)-extendedArc hn P ε n) (1,0) ≠ 0 ∧
      List.ofFn (crossingClippedCapWord (extendedArc hn P ε) 0
        ((P (lastIndex hn)).1-(P (zeroIndex hn)).1) 1 (n-1)) = List.ofFn P := by
  dsimp only
  let P := normalizedPolygon q e ∘ cyclicVertexEquiv e
  have hP : CyclicGeneric P := opened_generic _ (normalizedPolygon_generic q hq e) e
  obtain ⟨hv,hu,hl⟩ := normalizedPolygon_leftward q hq e
  have hU : (P (zeroIndex hq.size_ge_three)).2 = 0 := by
    simpa only [P,opened_zero] using hu
  have hV : (P (lastIndex hq.size_ge_three)).2 = 0 := by
    simpa only [P,opened_last] using hv
  have hL : (P (zeroIndex hq.size_ge_three)).1 < (P (lastIndex hq.size_ge_three)).1 := by
    simpa only [P,opened_zero,opened_last] using hl
  refine ⟨hU,hV,hL,geometricRadius hq.size_ge_three P,
    geometricRadius_pos hq.size_ge_three P hP.g1,?_⟩
  intro ε hε hb
  have hpair := endpoint_pairs_mem hq.size_ge_three P hP.g1 hU hV ε hε
  have hfirst := (actualPair_bounds _ n (1,2) hpair.1).2.2.2.2
  have hlast := (actualPair_bounds _ n (n-1,n) hpair.2).2.2.2.2
  exact ⟨affineWord_G1 P _ hP.g1 ε (le_of_lt hε) (lt_of_lt_of_le hb (min_le_left _ _)),
    extendedWord_off_line hq.size_ge_three P hP.g1 hU hV ε hε,
    extendedArc_first hq.size_ge_three P ε,extendedArc_last hq.size_ge_three P ε,
    extendedArc_interior hq.size_ge_three P ε,hfirst,hlast,
    whole_cap_list hq.size_ge_three P hU hV ε⟩

end DirectGLSSW.SourceMixedEdgeExtendedArc


