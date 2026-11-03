import DirectGLSSW.HOMFLY.HOMFYSmoothingLocal
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace DirectGLSSW.HOMFLY

/-- An arc not incident to the chosen crossing, among its four named ports. -/
def nonincidentArc (D : PLLinkDiagram) (c : Fin D.nCrossing) (e : Fin D.nArc) : Prop :=
  e ≠ D.incoming c 0 ∧ e ≠ D.incoming c 1 ∧
    e ≠ D.outgoing c 0 ∧ e ≠ D.outgoing c 1

private theorem center_not_in_nonincident_segment (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc) (hne : nonincidentArc D c e) :
    smoothingCenter D c ∉ closedSegmentTrace
      (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) := by
  rintro ⟨t, ht, hpoint⟩
  have hsource : D.arcSource e ≠ D.crossingVertex c := by
    intro h
    have hp := (D.crossing_incidence_complete c e).mp (Or.inl h)
    rcases hp with he | he | he | he
    · exact hne.1 he
    · exact hne.2.1 he
    · exact hne.2.2.1 he
    · exact hne.2.2.2 he
  have htarget : D.arcTarget e ≠ D.crossingVertex c := by
    intro h
    have hp := (D.crossing_incidence_complete c e).mp (Or.inr h)
    rcases hp with he | he | he | he
    · exact hne.1 he
    · exact hne.2.1 he
    · exact hne.2.2.1 he
    · exact hne.2.2.2 he
  rcases ht with ⟨ht0, ht1⟩
  by_cases htzero : t = 0
  ·
    have heq : D.vertexPoint (D.arcSource e) = smoothingCenter D c := by
      simpa [htzero, smoothingCenter, affinePoint_zero] using hpoint
    exact hsource (by simpa [smoothingCenter] using D.vertexPoint_injective heq)
  · by_cases htone : t = 1
    ·
      have heq : D.vertexPoint (D.arcTarget e) = smoothingCenter D c := by
        simpa [htone, smoothingCenter, affinePoint_one] using hpoint
      exact htarget (by simpa [smoothingCenter] using D.vertexPoint_injective heq)
    · have h0 : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
      have h1 : t < 1 := lt_of_le_of_ne ht1 htone
      exact (D.vertices_avoid_arc_interiors (D.crossingVertex c) e t h0 h1) hpoint.symm

theorem exists_nonincidentArc_clearance (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e, nonincidentArc D c e →
      ∀ x ∈ closedSegmentTrace (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)), δ ≤ dist (smoothingCenter D c) x := by
  classical
  let seg : Fin D.nArc → Set (PlanarPoint ℝ) := fun e => closedSegmentTrace
    (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e))
  let U : Set (PlanarPoint ℝ) := ⋂ e : Fin D.nArc,
    if nonincidentArc D c e then (seg e)ᶜ else Set.univ
  have hopen : IsOpen U := isOpen_iInter_of_finite fun e => by
    by_cases he : nonincidentArc D c e
    · simp only [U, he, ↓reduceIte]
      have hc : Continuous (fun t : ℝ => affinePoint
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) t) := by
        simp only [affinePoint]
        fun_prop
      exact (isCompact_Icc.image hc).isClosed.isOpen_compl
    · simp only [U, he, ↓reduceIte]
      exact isOpen_univ
  have hpU : smoothingCenter D c ∈ U := by
    rw [Set.mem_iInter]
    intro e
    by_cases he : nonincidentArc D c e
    · simpa [U, he, seg] using center_not_in_nonincident_segment D c e he
    · simp [U, he]
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hpU)
  refine ⟨δ, hδ, ?_⟩
  intro e he x hx
  by_cases hxlt : dist (smoothingCenter D c) x < δ
  · have hxU : x ∈ U := hball (by simpa [Metric.mem_ball, dist_comm] using hxlt)
    have hxnot : x ∉ seg e := by
      have hmem := Set.mem_iInter.mp hxU e
      simpa [U, he] using hmem
    exact False.elim (hxnot (by simpa [seg] using hx))
  · exact le_of_not_gt hxlt

private theorem real_smul_pair_local (r x y : ℝ) : r • (x, y) = (r * x, r * y) := by
  ext <;> simp

private theorem connectorZero_vector_form (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε s : ℝ) :
    smoothingConnectorZero D c ε s = smoothingCenter D c +
      (ε * (s - 1)) • strandTangent D c 0 + (ε * s) • strandTangent D c 1 := by
  ext <;> simp [smoothingConnectorZero, incomingCutPoint, outgoingCutPoint,
    smoothingCenter, affinePoint, real_smul_pair_local, strandTangent] <;> ring

private theorem connectorOne_vector_form (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε s : ℝ) :
    smoothingConnectorOne D c ε s = smoothingCenter D c +
      (ε * s) • strandTangent D c 0 + (ε * (s - 1)) • strandTangent D c 1 := by
  ext <;> simp [smoothingConnectorOne, incomingCutPoint, outgoingCutPoint,
    smoothingCenter, affinePoint, real_smul_pair_local, strandTangent] <;> ring

private theorem affineCoordinate_bound {ε s a b : ℝ} (hε : 0 ≤ ε)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |ε * (s - 1) * a + ε * s * b| ≤ ε * (|a| + |b|) := by
  have hleft : |s - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hright : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hA0 : ε * |s - 1| ≤ ε := by
    calc ε * |s - 1| ≤ ε * 1 := mul_le_mul_of_nonneg_left hleft hε
      _ = ε := by ring
  have hB0 : ε * |s| ≤ ε := by
    calc ε * |s| ≤ ε * 1 := mul_le_mul_of_nonneg_left hright hε
      _ = ε := by ring
  have hA : ε * |s - 1| * |a| ≤ ε * |a| :=
    mul_le_mul_of_nonneg_right hA0 (abs_nonneg a)
  have hB : ε * |s| * |b| ≤ ε * |b| :=
    mul_le_mul_of_nonneg_right hB0 (abs_nonneg b)
  calc
    |ε * (s - 1) * a + ε * s * b| ≤
        |ε * (s - 1) * a| + |ε * s * b| := abs_add _ _
    _ = ε * |s - 1| * |a| + ε * |s| * |b| := by
      simp [abs_mul, abs_of_nonneg hε, abs_of_nonneg hs0]
    _ ≤ ε * |a| + ε * |b| := add_le_add hA hB
    _ = ε * (|a| + |b|) := by ring

private theorem affineCoordinate_bound_swap {ε s a b : ℝ} (hε : 0 ≤ ε)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |ε * s * a + ε * (s - 1) * b| ≤ ε * (|a| + |b|) := by
  have h := affineCoordinate_bound hε hs0 hs1 (a := b) (b := a)
  simpa [add_comm, add_left_comm, add_assoc] using h

private theorem point_dist_le_of_coord_bounds (p x : PlanarPoint ℝ) (R : ℝ)
    (h1 : |x.1 - p.1| ≤ R) (h2 : |x.2 - p.2| ≤ R) : dist p x ≤ R := by
  rw [Prod.dist_eq, Real.dist_eq]
  exact max_le (by simpa [abs_sub_comm] using h1) (by simpa [abs_sub_comm] using h2)

private theorem connectorZero_dist_le (D : PLLinkDiagram) (c : Fin D.nCrossing)
    {ε s : ℝ} (hε : 0 ≤ ε) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    dist (smoothingCenter D c) (smoothingConnectorZero D c ε s) ≤
      ε * (1 + |(strandTangent D c 0).1| + |(strandTangent D c 1).1| +
        |(strandTangent D c 0).2| + |(strandTangent D c 1).2|) := by
  let p := smoothingCenter D c
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hform := connectorZero_vector_form D c ε s
  have hcoords1 : (smoothingConnectorZero D c ε s).1 - p.1 =
      ε * (s - 1) * u.1 + ε * s * v.1 := by
    have h := congrArg (fun z : PlanarPoint ℝ => z.1 - p.1) hform
    dsimp [p, u, v, real_smul_pair_local] at h ⊢
    linarith
  have hcoords2 : (smoothingConnectorZero D c ε s).2 - p.2 =
      ε * (s - 1) * u.2 + ε * s * v.2 := by
    have h := congrArg (fun z : PlanarPoint ℝ => z.2 - p.2) hform
    dsimp [p, u, v, real_smul_pair_local] at h ⊢
    linarith
  have h1 := affineCoordinate_bound hε hs.1 hs.2 (a := u.1) (b := v.1)
  have h2 := affineCoordinate_bound hε hs.1 hs.2 (a := u.2) (b := v.2)
  apply point_dist_le_of_coord_bounds p _ _
  · calc
      |(smoothingConnectorZero D c ε s).1 - p.1| =
          |ε * (s - 1) * u.1 + ε * s * v.1| := by rw [hcoords1]
      _ ≤ ε * (|u.1| + |v.1|) := h1
      _ ≤ ε * (1 + |u.1| + |v.1| + |u.2| + |v.2|) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [abs_nonneg (u.1), abs_nonneg (v.1), abs_nonneg (u.2), abs_nonneg (v.2)]
        · exact hε
  · calc
      |(smoothingConnectorZero D c ε s).2 - p.2| =
          |ε * (s - 1) * u.2 + ε * s * v.2| := by rw [hcoords2]
      _ ≤ ε * (|u.2| + |v.2|) := h2
      _ ≤ ε * (1 + |u.1| + |v.1| + |u.2| + |v.2|) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [abs_nonneg (u.1), abs_nonneg (v.1), abs_nonneg (u.2), abs_nonneg (v.2)]
        · exact hε

private theorem connectorOne_dist_le (D : PLLinkDiagram) (c : Fin D.nCrossing)
    {ε s : ℝ} (hε : 0 ≤ ε) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    dist (smoothingCenter D c) (smoothingConnectorOne D c ε s) ≤
      ε * (1 + |(strandTangent D c 0).1| + |(strandTangent D c 1).1| +
        |(strandTangent D c 0).2| + |(strandTangent D c 1).2|) := by
  let p := smoothingCenter D c
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hform := connectorOne_vector_form D c ε s
  have hcoords1 : (smoothingConnectorOne D c ε s).1 - p.1 =
      ε * s * u.1 + ε * (s - 1) * v.1 := by
    have h := congrArg (fun z : PlanarPoint ℝ => z.1 - p.1) hform
    dsimp [p, u, v, real_smul_pair_local] at h ⊢
    linarith
  have hcoords2 : (smoothingConnectorOne D c ε s).2 - p.2 =
      ε * s * u.2 + ε * (s - 1) * v.2 := by
    have h := congrArg (fun z : PlanarPoint ℝ => z.2 - p.2) hform
    dsimp [p, u, v, real_smul_pair_local] at h ⊢
    linarith
  have h1 := affineCoordinate_bound_swap hε hs.1 hs.2 (a := u.1) (b := v.1)
  have h2 := affineCoordinate_bound_swap hε hs.1 hs.2 (a := u.2) (b := v.2)
  apply point_dist_le_of_coord_bounds p _ _
  · calc
      |(smoothingConnectorOne D c ε s).1 - p.1| =
          |ε * s * u.1 + ε * (s - 1) * v.1| := by rw [hcoords1]
      _ ≤ ε * (|u.1| + |v.1|) := h1
      _ ≤ ε * (1 + |u.1| + |v.1| + |u.2| + |v.2|) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [abs_nonneg (u.1), abs_nonneg (v.1), abs_nonneg (u.2), abs_nonneg (v.2)]
        · exact hε
  · calc
      |(smoothingConnectorOne D c ε s).2 - p.2| =
          |ε * s * u.2 + ε * (s - 1) * v.2| := by rw [hcoords2]
      _ ≤ ε * (|u.2| + |v.2|) := h2
      _ ≤ ε * (1 + |u.1| + |v.1| + |u.2| + |v.2|) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [abs_nonneg (u.1), abs_nonneg (v.1), abs_nonneg (u.2), abs_nonneg (v.2)]
        · exact hε

theorem exists_connector_nonincident_clearance (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ crossingCutoffRadius D c ∧
      ∀ ε, 0 < ε → ε < ρ → ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ∀ e, nonincidentArc D c e →
          smoothingConnectorZero D c ε s ∉ closedSegmentTrace
            (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) ∧
          smoothingConnectorOne D c ε s ∉ closedSegmentTrace
            (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) := by
  obtain ⟨δ, hδ, hclear⟩ := exists_nonincidentArc_clearance D c
  let C := 1 + |(strandTangent D c 0).1| + |(strandTangent D c 1).1| +
    |(strandTangent D c 0).2| + |(strandTangent D c 1).2|
  have hC : 0 < C := by dsimp [C]; positivity
  let ρ := min (crossingCutoffRadius D c) (δ / C)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (crossingCutoffRadius_pos D c) (div_pos hδ hC)
  refine ⟨ρ, hρ, min_le_left _ _, ?_⟩
  intro ε hε hερ s hs e he
  have hεC : ε * C < δ := by
    apply (lt_div_iff₀ hC).mp
    exact lt_of_lt_of_le hερ (min_le_right _ _)
  have hzero : dist (smoothingCenter D c) (smoothingConnectorZero D c ε s) < δ := by
    calc
      _ ≤ ε * C := by simpa [C] using connectorZero_dist_le D c (le_of_lt hε) hs
      _ < δ := hεC
  have hone : dist (smoothingCenter D c) (smoothingConnectorOne D c ε s) < δ := by
    calc
      _ ≤ ε * C := by simpa [C] using connectorOne_dist_le D c (le_of_lt hε) hs
      _ < δ := hεC
  constructor
  · intro hz
    obtain ⟨t, ht, hqx⟩ := hz
    have hlower := hclear e he (affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) t) ⟨t, ht, rfl⟩
    have hdist : dist (smoothingCenter D c)
        (affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) t) =
        dist (smoothingCenter D c) (smoothingConnectorZero D c ε s) := by rw [← hqx]
    rw [hdist] at hlower
    exact (not_lt_of_ge hlower) hzero
  · intro hz
    obtain ⟨t, ht, hqx⟩ := hz
    have hlower := hclear e he (affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) t) ⟨t, ht, rfl⟩
    have hdist : dist (smoothingCenter D c)
        (affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) t) =
        dist (smoothingCenter D c) (smoothingConnectorOne D c ε s) := by rw [← hqx]
    rw [hdist] at hlower
    exact (not_lt_of_ge hlower) hone
end DirectGLSSW.HOMFLY



