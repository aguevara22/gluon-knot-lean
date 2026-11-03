import GlobalRoundingExclusions
import NormalizedCellPieces
import DistinctCrossingBranches
import IncidentRetainedClassification
import StrictCrossingPhase

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate5: one actual cutoff gives the COMPLETE intersection iff
for all half-open normalized cells. Every geometric exclusion is derived
internally from actual D, never supplied as an intersection certificate. -/
theorem exists_normalized_cell_intersection (D : PLLinkDiagram) (base : Fin D.nArc)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 1) :
    ∃ (δ : RoundingFraction) (θ : Fin D.nCrossing → Fin 2 → ℝ),
      δ.val < τ ∧ δ.val < 1 - τ ∧
      (∀ c i, θ c i ∈ Set.Ioo 0 (2 * δ.val) ∧
        Complex.equivRealProd (normalizedRoundedCell D (D.incoming c i) δ (θ c i)) =
          D.vertexPoint (D.crossingVertex c)) ∧
      (∀ (e f : Fin D.nArc) (s t : ℝ), s ∈ Set.Ico 0 1 → t ∈ Set.Ico 0 1 →
        (Complex.equivRealProd (normalizedRoundedCell D e δ s) =
          Complex.equivRealProd (normalizedRoundedCell D f δ t) ↔
          (e = f ∧ s = t) ∨
          (∃ (c : Fin D.nCrossing) (i j : Fin 2), i ≠ j ∧
            e = D.incoming c i ∧ f = D.incoming c j ∧ s = θ c i ∧ t = θ c j))) := by
  classical
  obtain ⟨δ,hleft,hright,hdifferent,hnonincident⟩ := exists_rounding_global_exclusions D base τ hτ
  have hp : 0 < 2 * δ.val := by linarith [δ.property.1]
  have hcenters : ∀ (c : Fin D.nCrossing) (i : Fin 2), ∃ q : ℝ,
      q ∈ Set.Ioo 0 1 ∧ roundedCorner D (D.incoming c i) δ.val q = cornerCenter D (D.incoming c i) := by
    intro c i
    obtain ⟨q,hq,_⟩ := roundedCorner_crossing_center_existsUnique D c i δ.val δ.property.1
    exact ⟨q,roundedCorner_crossing_center_interior D c i δ.val q δ.property.1 hq.1 hq.2,hq.2⟩
  choose qc hqc using hcenters
  let θ : Fin D.nCrossing → Fin 2 → ℝ := fun c i => 2 * δ.val * qc c i
  have hphases : ∀ c i, θ c i ∈ Set.Ioo 0 (2 * δ.val) ∧
      Complex.equivRealProd (normalizedRoundedCell D (D.incoming c i) δ (θ c i)) =
        D.vertexPoint (D.crossingVertex c) := by
    intro c i
    have hqi : qc c i ∈ Set.Icc 0 1 := ⟨(hqc c i).1.1.le,(hqc c i).1.2.le⟩
    refine ⟨⟨mul_pos hp (hqc c i).1.1,?_⟩,?_⟩
    · dsimp only [θ]
      nlinarith [mul_lt_mul_of_pos_left (hqc c i).1.2 hp]
    · dsimp only [θ]
      rw [normalizedRoundedCell_corner_time D _ δ _ hqi,(hqc c i).2]
      simp [cornerCenter,D.incoming_target]
  have hcorners : ∀ (e f : Fin D.nArc) (q r : ℝ), q ∈ Set.Icc 0 1 → r ∈ Set.Icc 0 1 →
      Complex.equivRealProd (roundedCorner D e δ.val q) =
        Complex.equivRealProd (roundedCorner D f δ.val r) →
      (e = f ∧ q = r) ∨ (∃ (c : Fin D.nCrossing) (i j : Fin 2), i ≠ j ∧
        e = D.incoming c i ∧ f = D.incoming c j ∧ q = qc c i ∧ r = qc c j) := by
    intro e f q r hq hr heq
    by_cases hef : e = f
    · subst f
      exact Or.inl ⟨rfl,roundedCorner_injOn D e δ.val δ.property.1 hq hr
        (Complex.equivRealProd.injective heq)⟩
    · by_cases htargets : D.arcTarget e = D.arcTarget f
      · by_cases hcross : ∃ c : Fin D.nCrossing, D.crossingVertex c = D.arcTarget e
        · obtain ⟨c,hc⟩ := hcross
          obtain ⟨i,hi⟩ := crossing_incoming_arc_label D c e hc.symm
          obtain ⟨j,hj⟩ := crossing_incoming_arc_label D c f (htargets.symm.trans hc.symm)
          subst e
          subst f
          have hij : i ≠ j := by intro h; subst j; exact hef rfl
          have hz := (roundedCorner_crossing_distinct_iff_center D c i j hij δ.val q r).mp
            (Complex.equivRealProd.injective heq)
          have hqi : q = qc c i := roundedCorner_injOn D _ δ.val δ.property.1 hq
            ⟨(hqc c i).1.1.le,(hqc c i).1.2.le⟩ (hz.1.trans (hqc c i).2.symm)
          have hrj : r = qc c j := roundedCorner_injOn D _ δ.val δ.property.1 hr
            ⟨(hqc c j).1.1.le,(hqc c j).1.2.le⟩ (hz.2.trans (hqc c j).2.symm)
          exact Or.inr ⟨c,i,j,hij,rfl,rfl,hqi,hrj⟩
        · have hnoncross : ∀ c, D.crossingVertex c ≠ D.arcTarget e := by simpa only [not_exists] using hcross
          exact False.elim (hef (regular_vertex_incoming_unique D (D.arcTarget e) hnoncross
            e f rfl htargets.symm))
      · exact False.elim (hdifferent e f q r htargets hq hr heq)
  have hmixed : ∀ (e f : Fin D.nArc) (q u : ℝ), q ∈ Set.Icc 0 1 → u ∈ Set.Ioo 0 1 →
      Complex.equivRealProd (roundedCorner D e δ.val q) ≠ retainedArcPoint D f δ u := by
    intro e f q u hq hu heq
    by_cases hinc : D.arcSource f = D.arcTarget e ∨ D.arcTarget f = D.arcTarget e
    · have h := (roundedCorner_incident_retained_iff D e f δ q u hq ⟨hu.1.le,hu.2.le⟩ hinc).mp heq
      rcases h with ⟨_,_,h⟩ | ⟨_,_,h⟩
      · linarith [hu.2]
      · linarith [hu.1]
    · have hsource : D.arcSource f ≠ D.arcTarget e := fun h => hinc (Or.inl h)
      have htarget : D.arcTarget f ≠ D.arcTarget e := fun h => hinc (Or.inr h)
      have ha := retainedArc_parameter_interior δ u ⟨hu.1.le,hu.2.le⟩
      exact hnonincident e f q _ hsource htarget hq ⟨ha.1.le,ha.2.le⟩ heq
  refine ⟨δ,θ,hleft,hright,hphases,?_⟩
  intro e f s t hs ht
  constructor
  · intro heq
    by_cases hsc : s ≤ 2 * δ.val
    · obtain ⟨q,hq,hqs,hcurveS⟩ := normalizedRoundedCell_corner_piece D e δ s ⟨hs.1,hsc⟩
      by_cases htc : t ≤ 2 * δ.val
      · obtain ⟨r,hr,hrt,hcurveT⟩ := normalizedRoundedCell_corner_piece D f δ t ⟨ht.1,htc⟩
        rw [hcurveS,hcurveT] at heq
        rcases hcorners e f q r hq hr heq with ⟨hef,hqr⟩ | ⟨c,i,j,hij,hei,hfj,hqi,hrj⟩
        · exact Or.inl ⟨hef,by rw [← hqs,← hrt,hqr]⟩
        · refine Or.inr ⟨c,i,j,hij,hei,hfj,?_,?_⟩
          · dsimp only [θ]
            rw [← hqs,hqi]
          · dsimp only [θ]
            rw [← hrt,hrj]
      · obtain ⟨u,hu,_,hcurveT⟩ := normalizedRoundedCell_straight_piece D f δ t ⟨lt_of_not_ge htc,ht.2⟩
        rw [hcurveS,hcurveT] at heq
        exact False.elim (hmixed e (D.continuation f) q u hq hu heq)
    · obtain ⟨u,hu,hus,hcurveS⟩ := normalizedRoundedCell_straight_piece D e δ s ⟨lt_of_not_ge hsc,hs.2⟩
      by_cases htc : t ≤ 2 * δ.val
      · obtain ⟨r,hr,_,hcurveT⟩ := normalizedRoundedCell_corner_piece D f δ t ⟨ht.1,htc⟩
        rw [hcurveS,hcurveT] at heq
        exact False.elim (hmixed f (D.continuation e) r u hr hu heq.symm)
      · obtain ⟨v,hv,hvt,hcurveT⟩ := normalizedRoundedCell_straight_piece D f δ t ⟨lt_of_not_ge htc,ht.2⟩
        rw [hcurveS,hcurveT] at heq
        have h := (retainedArcPoint_intersection_iff D _ _ δ u v ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩).mp heq
        exact Or.inl ⟨D.continuation.injective h.1,by rw [← hus,← hvt,h.2]⟩
  · rintro (⟨rfl,rfl⟩ | ⟨c,i,j,_,rfl,rfl,rfl,rfl⟩)
    · rfl
    · exact (hphases c i).2.trans (hphases c j).2.symm

end DirectGLSSW.HOMFLY.PrincipalTurning

