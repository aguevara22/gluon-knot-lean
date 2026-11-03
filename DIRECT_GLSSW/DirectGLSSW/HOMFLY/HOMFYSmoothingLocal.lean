import DirectGLSSW.HOMFLY.PLDiagrams
import DirectGLSSW.AffineSegments
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace DirectGLSSW.HOMFLY

def smoothingCenter (D : PLLinkDiagram) (c : Fin D.nCrossing) : PlanarPoint ℝ :=
  D.vertexPoint (D.crossingVertex c)

noncomputable def outgoingTangentScale (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) : ℝ := Classical.choose (D.through_tangents_positive_collinear c i)

theorem outgoingTangentScale_pos (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    0 < outgoingTangentScale D c i :=
  (Classical.choose_spec (D.through_tangents_positive_collinear c i)).1

theorem outgoingTangentScale_spec (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    strandTangent D c i = outgoingTangentScale D c i •
      (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i))) - smoothingCenter D c) :=
  (Classical.choose_spec (D.through_tangents_positive_collinear c i)).2

noncomputable def crossingCutoffRadius (D : PLLinkDiagram) (c : Fin D.nCrossing) : ℝ :=
  min 1 (min (1 / outgoingTangentScale D c 0) (1 / outgoingTangentScale D c 1))

theorem crossingCutoffRadius_pos (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    0 < crossingCutoffRadius D c := by
  unfold crossingCutoffRadius
  apply lt_min
  · norm_num
  · apply lt_min
    · exact one_div_pos.mpr (outgoingTangentScale_pos D c 0)
    · exact one_div_pos.mpr (outgoingTangentScale_pos D c 1)

def incomingCutPoint (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) (i : Fin 2) :
    PlanarPoint ℝ := smoothingCenter D c - ε • strandTangent D c i

def outgoingCutPoint (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) (i : Fin 2) :
    PlanarPoint ℝ := smoothingCenter D c + ε • strandTangent D c i

def closedSegmentTrace (a b : PlanarPoint ℝ) : Set (PlanarPoint ℝ) :=
  (affinePoint a b) '' Set.Icc (0 : ℝ) 1

private theorem real_smul_pair (r x y : ℝ) : r • (x, y) = (r * x, r * y) := by
  ext <;> simp

def smoothingConnectorZero (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε s : ℝ) :
    PlanarPoint ℝ :=
  affinePoint (incomingCutPoint D c ε 0) (outgoingCutPoint D c ε 1) s

def smoothingConnectorOne (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε s : ℝ) :
    PlanarPoint ℝ :=
  affinePoint (incomingCutPoint D c ε 1) (outgoingCutPoint D c ε 0) s

theorem crossingCutoff_parameters (D : PLLinkDiagram) (c : Fin D.nCrossing)
    {ε : ℝ} (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) (i : Fin 2) :
    0 < 1 - ε ∧ 1 - ε < 1 ∧
      affinePoint (D.vertexPoint (D.arcSource (D.incoming c i))) (smoothingCenter D c) (1 - ε) =
        incomingCutPoint D c ε i ∧
      0 < ε * outgoingTangentScale D c i ∧ ε * outgoingTangentScale D c i < 1 ∧
      affinePoint (smoothingCenter D c)
        (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i))))
        (ε * outgoingTangentScale D c i) = outgoingCutPoint D c ε i := by
  have hs := outgoingTangentScale_pos D c
  have hrel := outgoingTangentScale_spec D c
  have hεone : ε < 1 := by
    have := lt_of_lt_of_le hεr (min_le_left _ _)
    exact this
  have hradius : ε < 1 / outgoingTangentScale D c i := by
    fin_cases i
    · exact lt_of_lt_of_le hεr (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact lt_of_lt_of_le hεr (le_trans (min_le_right _ _) (min_le_right _ _))
  have hprod : ε * outgoingTangentScale D c i < 1 :=
    (lt_div_iff₀ (hs i)).mp hradius
  have hprodpos : 0 < ε * outgoingTangentScale D c i := mul_pos hε (hs i)
  have hin : D.vertexPoint (D.arcSource (D.incoming c i)) =
      smoothingCenter D c - strandTangent D c i := by
    dsimp [strandTangent, smoothingCenter]
    abel
  refine ⟨by linarith, by linarith, ?_, hprodpos, hprod, ?_⟩
  · rw [hin]
    dsimp [incomingCutPoint]
    ext <;> simp [affinePoint] <;> ring
  · change affinePoint (smoothingCenter D c)
        (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i))))
        (ε * outgoingTangentScale D c i) =
      smoothingCenter D c + ε • strandTangent D c i
    rw [hrel i]
    ext <;> simp [affinePoint, smoothingCenter, smul_eq_mul] <;> ring

private def basisVector (u v : PlanarPoint ℝ) (a b : ℝ) : PlanarPoint ℝ :=
  a • u + b • v

private theorem planarDet_add_left (x y z : PlanarPoint ℝ) :
    planarDet (x + y) z = planarDet x z + planarDet y z := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp [planarDet]
  ring

private theorem planarDet_add_right (x y z : PlanarPoint ℝ) :
    planarDet x (y + z) = planarDet x y + planarDet x z := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp [planarDet]
  ring

private theorem planarDet_smul_left (r : ℝ) (x y : PlanarPoint ℝ) :
    planarDet (r • x) y = r * planarDet x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [planarDet, real_smul_pair]
  ring

private theorem planarDet_smul_right (r : ℝ) (x y : PlanarPoint ℝ) :
    planarDet x (r • y) = r * planarDet x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [planarDet, real_smul_pair]
  ring

private theorem planarDet_self (x : PlanarPoint ℝ) : planarDet x x = 0 := by
  rcases x with ⟨x₁, x₂⟩
  simp only [planarDet]
  ring

private theorem basisVector_injective {u v : PlanarPoint ℝ}
    (hdet : planarDet u v ≠ 0) :
    Function.Injective (fun z : ℝ × ℝ => basisVector u v z.1 z.2) := by
  intro x y hxy
  have h0 := congrArg (fun z : PlanarPoint ℝ => planarDet z v) hxy
  have h1 := congrArg (fun z : PlanarPoint ℝ => planarDet u z) hxy
  have h0' : x.1 * planarDet u v = y.1 * planarDet u v := by
    simpa only [basisVector, planarDet_add_left, planarDet_smul_left, planarDet_smul_right,
      planarDet_self, zero_mul, mul_zero, add_zero, zero_add] using h0
  have h1' : x.2 * planarDet u v = y.2 * planarDet u v := by
    simpa only [basisVector, planarDet_add_right, planarDet_smul_left, planarDet_smul_right,
      planarDet_self, zero_mul, mul_zero, add_zero, zero_add] using h1
  apply Prod.ext
  · exact mul_right_cancel₀ hdet h0'
  · exact mul_right_cancel₀ hdet h1'

private theorem affinePoint_basis (p u v : PlanarPoint ℝ)
    (a b c d t : ℝ) :
    affinePoint (p + basisVector u v a b) (p + basisVector u v c d) t =
      p + basisVector u v (a + t * (c - a)) (b + t * (d - b)) := by
  ext <;> simp [affinePoint, basisVector, real_smul_pair] <;> ring

private theorem basisPoint_eq_of_coeffs {p u v : PlanarPoint ℝ}
    {a b c d : ℝ} (hdet : planarDet u v ≠ 0)
    (h : p + basisVector u v a b = p + basisVector u v c d) :
    a = c ∧ b = d := by
  have hv := add_left_cancel h
  have hp : (a, b) = (c, d) := by
    apply basisVector_injective hdet
    simpa using hv
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

private theorem finTwo_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

private theorem source_basis_form (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    D.vertexPoint (D.arcSource (D.incoming c i)) =
      smoothingCenter D c - strandTangent D c i := by
  dsimp [smoothingCenter, strandTangent]
  abel

private theorem incomingRay_basis (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε t : ℝ) (i : Fin 2) :
    affinePoint (D.vertexPoint (D.arcSource (D.incoming c i)))
        (incomingCutPoint D c ε i) t =
      if i = 0 then
        smoothingCenter D c + basisVector (strandTangent D c 0) (strandTangent D c 1)
          (-1 + t * (1 - ε)) 0
      else
        smoothingCenter D c + basisVector (strandTangent D c 0) (strandTangent D c 1)
          0 (-1 + t * (1 - ε)) := by
  rcases finTwo_eq_zero_or_one i with hi | hi
  · subst i
    simp only [if_pos rfl]
    have hsrc : smoothingCenter D c - strandTangent D c 0 = smoothingCenter D c +
        basisVector (strandTangent D c 0) (strandTangent D c 1) (-1) 0 := by
      ext <;> simp [basisVector, real_smul_pair] <;> ring
    rw [source_basis_form, hsrc]
    have hcut : incomingCutPoint D c ε 0 = smoothingCenter D c +
        basisVector (strandTangent D c 0) (strandTangent D c 1) (-ε) 0 := by
      ext <;> simp [incomingCutPoint, basisVector, real_smul_pair] <;> ring
    rw [hcut]
    rw [affinePoint_basis]
    congr 1 <;> ring
  · subst i
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    have hsrc : smoothingCenter D c - strandTangent D c 1 = smoothingCenter D c +
        basisVector (strandTangent D c 0) (strandTangent D c 1) 0 (-1) := by
      ext <;> simp [basisVector, real_smul_pair] <;> ring
    rw [source_basis_form, hsrc]
    have hcut : incomingCutPoint D c ε 1 = smoothingCenter D c +
        basisVector (strandTangent D c 0) (strandTangent D c 1) 0 (-ε) := by
      ext <;> simp [incomingCutPoint, basisVector, real_smul_pair] <;> ring
    rw [hcut]
    rw [affinePoint_basis]
    congr 1 <;> ring

private theorem outgoingTarget_basis (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i))) =
      smoothingCenter D c + (1 / outgoingTangentScale D c i) • strandTangent D c i := by
  let σ := outgoingTangentScale D c i
  have hσ : 0 < σ := outgoingTangentScale_pos D c i
  have hrel := outgoingTangentScale_spec D c i
  have hmain : smoothingCenter D c + (1 / σ) • (σ •
      (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i))) - smoothingCenter D c)) =
      D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i))) := by
    rw [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hσ), one_smul]
    abel
  calc
    _ = smoothingCenter D c + (1 / σ) • (σ •
        (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i))) - smoothingCenter D c)) :=
          hmain.symm
    _ = _ := by rw [← hrel]

private theorem outgoingRay_basis (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε t : ℝ) (i : Fin 2) :
    affinePoint (outgoingCutPoint D c ε i)
        (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i)))) t =
      if i = 0 then
        smoothingCenter D c + basisVector (strandTangent D c 0) (strandTangent D c 1)
          (ε + t * (1 / outgoingTangentScale D c 0 - ε)) 0
      else
        smoothingCenter D c + basisVector (strandTangent D c 0) (strandTangent D c 1)
          0 (ε + t * (1 / outgoingTangentScale D c 1 - ε)) := by
  rcases finTwo_eq_zero_or_one i with hi | hi
  · subst i
    simp only [if_pos rfl]
    have hcut : outgoingCutPoint D c ε 0 = smoothingCenter D c +
        basisVector (strandTangent D c 0) (strandTangent D c 1) ε 0 := by
      ext <;> simp [outgoingCutPoint, basisVector, real_smul_pair] <;> ring
    rw [hcut, outgoingTarget_basis]
    have ht : smoothingCenter D c + (1 / outgoingTangentScale D c 0) •
        strandTangent D c 0 = smoothingCenter D c + basisVector
          (strandTangent D c 0) (strandTangent D c 1)
          (1 / outgoingTangentScale D c 0) 0 := by simp [basisVector]
    rw [ht]
    rw [affinePoint_basis]
    congr 1 <;> ring
  · subst i
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    have hcut : outgoingCutPoint D c ε 1 = smoothingCenter D c +
        basisVector (strandTangent D c 0) (strandTangent D c 1) 0 ε := by
      ext <;> simp [outgoingCutPoint, basisVector, real_smul_pair] <;> ring
    rw [hcut, outgoingTarget_basis]
    have ht : smoothingCenter D c + (1 / outgoingTangentScale D c 1) •
        strandTangent D c 1 = smoothingCenter D c + basisVector
          (strandTangent D c 0) (strandTangent D c 1) 0
          (1 / outgoingTangentScale D c 1) := by simp [basisVector]
    rw [ht]
    rw [affinePoint_basis]
    congr 1 <;> ring

private theorem connectorZero_basis (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε s : ℝ) :
    smoothingConnectorZero D c ε s = smoothingCenter D c +
      basisVector (strandTangent D c 0) (strandTangent D c 1)
        (ε * (s - 1)) (ε * s) := by
  have hL : incomingCutPoint D c ε 0 = smoothingCenter D c +
      basisVector (strandTangent D c 0) (strandTangent D c 1) (-ε) 0 := by
    ext <;> simp [incomingCutPoint, basisVector, real_smul_pair] <;> ring
  have hR : outgoingCutPoint D c ε 1 = smoothingCenter D c +
      basisVector (strandTangent D c 0) (strandTangent D c 1) 0 ε := by
    ext <;> simp [outgoingCutPoint, basisVector, real_smul_pair] <;> ring
  rw [smoothingConnectorZero, hL, hR]
  rw [affinePoint_basis]
  congr 1 <;> ring

private theorem connectorOne_basis (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε s : ℝ) :
    smoothingConnectorOne D c ε s = smoothingCenter D c +
      basisVector (strandTangent D c 0) (strandTangent D c 1)
        (ε * s) (ε * (s - 1)) := by
  have hL : incomingCutPoint D c ε 1 = smoothingCenter D c +
      basisVector (strandTangent D c 0) (strandTangent D c 1) 0 (-ε) := by
    ext <;> simp [incomingCutPoint, basisVector, real_smul_pair] <;> ring
  have hR : outgoingCutPoint D c ε 0 = smoothingCenter D c +
      basisVector (strandTangent D c 0) (strandTangent D c 1) ε 0 := by
    ext <;> simp [outgoingCutPoint, basisVector, real_smul_pair] <;> ring
  rw [smoothingConnectorOne, hL, hR]
  rw [affinePoint_basis]
  congr 1 <;> ring

theorem crossing_cut_connector_disjoint (D : PLLinkDiagram) (c : Fin D.nCrossing)
    {ε s t : ℝ} (hε : 0 < ε) :
    smoothingConnectorZero D c ε s ≠ smoothingConnectorOne D c ε t := by
  let p := smoothingCenter D c
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  let L0 := incomingCutPoint D c ε 0
  let L1 := incomingCutPoint D c ε 1
  let R0 := outgoingCutPoint D c ε 0
  let R1 := outgoingCutPoint D c ε 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  have hpar : planarDet (R1 - L0) (R0 - L1) = 0 := by
    simp [R1, R0, L0, L1, incomingCutPoint, outgoingCutPoint, u, v, p,
      smoothingCenter, strandTangent, planarDet, real_smul_pair] <;> ring
  have hbase : planarDet (R1 - L0) (L1 - L0) ≠ 0 := by
    have hformula : planarDet (R1 - L0) (L1 - L0) = -2 * ε ^ 2 * planarDet u v := by
      simp [R1, L1, L0, incomingCutPoint, outgoingCutPoint, u, v, p,
        smoothingCenter, strandTangent, planarDet, real_smul_pair] <;> ring
    rw [hformula]
    exact mul_ne_zero (mul_ne_zero (by positivity) (pow_ne_zero _ (ne_of_gt hε))) hdet
  intro heq
  have hcol := affinePoint_parallel_collinear L0 R1 L1 R0 s t heq hpar
  exact hbase hcol

theorem connectorZero_meets_incomingZero_only_endpoint
    (D : PLLinkDiagram) (c : Fin D.nCrossing) {ε s t : ℝ}
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heq : smoothingConnectorZero D c ε s =
      affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
        (incomingCutPoint D c ε 0) t) : s = 0 ∧ t = 1 := by
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  have hcoords : ε * (s - 1) = -1 + t * (1 - ε) ∧ ε * s = 0 := by
    have heq' : smoothingCenter D c + basisVector u v (ε * (s - 1)) (ε * s) =
        smoothingCenter D c + basisVector u v (-1 + t * (1 - ε)) 0 := by
      simpa [u, v, connectorZero_basis, incomingRay_basis] using heq
    exact basisPoint_eq_of_coeffs hdet heq'
  have hεone : ε < 1 := lt_of_lt_of_le hεr (min_le_left _ _)
  rcases hcoords with ⟨hx, hy⟩
  constructor
  · nlinarith [hs.1, hs.2, hε]
  · have hprod := mul_nonneg (sub_nonneg.mpr (le_of_lt hεone)) (sub_nonneg.mpr ht.2)
    nlinarith [hs.1, hs.2, ht.1, ht.2, hε, hεone, hprod]

theorem connectorZero_meets_outgoingOne_only_endpoint
    (D : PLLinkDiagram) (c : Fin D.nCrossing) {ε s t : ℝ}
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heq : smoothingConnectorZero D c ε s =
      affinePoint (outgoingCutPoint D c ε 1)
        (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 1)))) t) : s = 1 ∧ t = 0 := by
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  have hcoords : ε * (s - 1) = 0 ∧ ε * s = ε + t * (1 / outgoingTangentScale D c 1 - ε) := by
    have heq' : smoothingCenter D c + basisVector u v (ε * (s - 1)) (ε * s) =
        smoothingCenter D c + basisVector u v 0
          (ε + t * (1 / outgoingTangentScale D c 1 - ε)) := by
      simpa [u, v, connectorZero_basis, outgoingRay_basis] using heq
    exact basisPoint_eq_of_coeffs hdet heq'
  have hσpos := outgoingTangentScale_pos D c 1
  have hσbound : ε * outgoingTangentScale D c 1 < 1 := by
    exact (crossingCutoff_parameters D c hε hεr 1).2.2.2.2.1
  rcases hcoords with ⟨hx, hy⟩
  constructor
  · nlinarith [hs.1, hs.2, hε]
  · have hgap : 0 < 1 / outgoingTangentScale D c 1 - ε := by
      rw [sub_pos]
      exact (lt_div_iff₀ hσpos).2 hσbound
    have hprod := mul_nonneg (le_of_lt hgap) ht.1
    nlinarith [hs.1, hs.2, ht.1, ht.2, hε, hσpos, hgap, hprod]

theorem connectorZero_avoids_incomingOne
    (D : PLLinkDiagram) (c : Fin D.nCrossing) {ε s t : ℝ}
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    smoothingConnectorZero D c ε s ≠
      affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
        (incomingCutPoint D c ε 1) t := by
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  intro heq
  have hcoords : ε * (s - 1) = 0 ∧ ε * s = -1 + t * (1 - ε) := by
    have heq' : smoothingCenter D c + basisVector u v (ε * (s - 1)) (ε * s) =
        smoothingCenter D c + basisVector u v 0 (-1 + t * (1 - ε)) := by
      simpa [u, v, connectorZero_basis, incomingRay_basis] using heq
    exact basisPoint_eq_of_coeffs hdet heq'
  have hεone : ε < 1 := lt_of_lt_of_le hεr (min_le_left _ _)
  rcases hcoords with ⟨hx, hy⟩
  have hprod := mul_nonneg (sub_nonneg.mpr (le_of_lt hεone)) (sub_nonneg.mpr ht.2)
  nlinarith [hs.1, hs.2, ht.1, ht.2, hε, hεone, hprod]

theorem connectorZero_avoids_outgoingZero
    (D : PLLinkDiagram) (c : Fin D.nCrossing) {ε s t : ℝ}
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    smoothingConnectorZero D c ε s ≠
      affinePoint (outgoingCutPoint D c ε 0)
        (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 0)))) t := by
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  intro heq
  have hcoords : ε * (s - 1) = ε + t * (1 / outgoingTangentScale D c 0 - ε) ∧ ε * s = 0 := by
    have heq' : smoothingCenter D c + basisVector u v (ε * (s - 1)) (ε * s) =
        smoothingCenter D c + basisVector u v
          (ε + t * (1 / outgoingTangentScale D c 0 - ε)) 0 := by
      simpa [u, v, connectorZero_basis, outgoingRay_basis] using heq
    exact basisPoint_eq_of_coeffs hdet heq'
  have hσpos := outgoingTangentScale_pos D c 0
  have hσbound : ε * outgoingTangentScale D c 0 < 1 :=
    (crossingCutoff_parameters D c hε hεr 0).2.2.2.2.1
  have hgap : 0 < 1 / outgoingTangentScale D c 0 - ε := by
    rw [sub_pos]
    exact (lt_div_iff₀ hσpos).2 hσbound
  rcases hcoords with ⟨hx, hy⟩
  have hprod := mul_nonneg (le_of_lt hgap) ht.1
  nlinarith [hs.1, hs.2, ht.1, ht.2, hε, hσpos, hgap, hprod]

theorem connectorOne_meets_incomingOne_only_endpoint
    (D : PLLinkDiagram) (c : Fin D.nCrossing) {ε s t : ℝ}
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heq : smoothingConnectorOne D c ε s =
      affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
        (incomingCutPoint D c ε 1) t) : s = 0 ∧ t = 1 := by
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  have hcoords : ε * s = 0 ∧ ε * (s - 1) = -1 + t * (1 - ε) := by
    have heq' : smoothingCenter D c + basisVector u v (ε * s) (ε * (s - 1)) =
        smoothingCenter D c + basisVector u v 0 (-1 + t * (1 - ε)) := by
      simpa [u, v, connectorOne_basis, incomingRay_basis] using heq
    exact basisPoint_eq_of_coeffs hdet heq'
  have hεone : ε < 1 := lt_of_lt_of_le hεr (min_le_left _ _)
  rcases hcoords with ⟨hx, hy⟩
  constructor
  · nlinarith [hs.1, hs.2, hε]
  · have hprod := mul_nonneg (sub_nonneg.mpr (le_of_lt hεone)) (sub_nonneg.mpr ht.2)
    nlinarith [hs.1, hs.2, ht.1, ht.2, hε, hεone, hprod]

theorem connectorOne_meets_outgoingZero_only_endpoint
    (D : PLLinkDiagram) (c : Fin D.nCrossing) {ε s t : ℝ}
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heq : smoothingConnectorOne D c ε s =
      affinePoint (outgoingCutPoint D c ε 0)
        (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 0)))) t) : s = 1 ∧ t = 0 := by
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  have hcoords : ε * s = ε + t * (1 / outgoingTangentScale D c 0 - ε) ∧ ε * (s - 1) = 0 := by
    have heq' : smoothingCenter D c + basisVector u v (ε * s) (ε * (s - 1)) =
        smoothingCenter D c + basisVector u v
          (ε + t * (1 / outgoingTangentScale D c 0 - ε)) 0 := by
      simpa [u, v, connectorOne_basis, outgoingRay_basis] using heq
    exact basisPoint_eq_of_coeffs hdet heq'
  have hσpos := outgoingTangentScale_pos D c 0
  have hσbound : ε * outgoingTangentScale D c 0 < 1 :=
    (crossingCutoff_parameters D c hε hεr 0).2.2.2.2.1
  have hgap : 0 < 1 / outgoingTangentScale D c 0 - ε := by
    rw [sub_pos]
    exact (lt_div_iff₀ hσpos).2 hσbound
  rcases hcoords with ⟨hx, hy⟩
  constructor
  · have hprod := mul_nonneg (le_of_lt hgap) ht.1
    nlinarith [hs.1, hs.2, ht.1, ht.2, hε, hgap, hprod]
  · nlinarith [hs.1, hs.2, hε]

theorem connectorOne_avoids_incomingZero
    (D : PLLinkDiagram) (c : Fin D.nCrossing) {ε s t : ℝ}
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    smoothingConnectorOne D c ε s ≠
      affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
        (incomingCutPoint D c ε 0) t := by
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  intro heq
  have hcoords : ε * s = -1 + t * (1 - ε) ∧ ε * (s - 1) = 0 := by
    have heq' : smoothingCenter D c + basisVector u v (ε * s) (ε * (s - 1)) =
        smoothingCenter D c + basisVector u v (-1 + t * (1 - ε)) 0 := by
      simpa [u, v, connectorOne_basis, incomingRay_basis] using heq
    exact basisPoint_eq_of_coeffs hdet heq'
  have hεone : ε < 1 := lt_of_lt_of_le hεr (min_le_left _ _)
  rcases hcoords with ⟨hx, hy⟩
  have hprod := mul_nonneg (sub_nonneg.mpr (le_of_lt hεone)) (sub_nonneg.mpr ht.2)
  nlinarith [hs.1, hs.2, ht.1, ht.2, hε, hεone, hprod]

theorem connectorOne_avoids_outgoingOne
    (D : PLLinkDiagram) (c : Fin D.nCrossing) {ε s t : ℝ}
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    smoothingConnectorOne D c ε s ≠
      affinePoint (outgoingCutPoint D c ε 1)
        (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 1)))) t := by
  let u := strandTangent D c 0
  let v := strandTangent D c 1
  have hdet : planarDet u v ≠ 0 := by
    simpa [u, v, strandTangent, smoothingCenter] using D.crossing_transverse c
  intro heq
  have hcoords : ε * s = 0 ∧ ε * (s - 1) = ε + t * (1 / outgoingTangentScale D c 1 - ε) := by
    have heq' : smoothingCenter D c + basisVector u v (ε * s) (ε * (s - 1)) =
        smoothingCenter D c + basisVector u v 0
          (ε + t * (1 / outgoingTangentScale D c 1 - ε)) := by
      simpa [u, v, connectorOne_basis, outgoingRay_basis] using heq
    exact basisPoint_eq_of_coeffs hdet heq'
  have hσpos := outgoingTangentScale_pos D c 1
  have hσbound : ε * outgoingTangentScale D c 1 < 1 :=
    (crossingCutoff_parameters D c hε hεr 1).2.2.2.2.1
  have hgap : 0 < 1 / outgoingTangentScale D c 1 - ε := by
    rw [sub_pos]
    exact (lt_div_iff₀ hσpos).2 hσbound
  rcases hcoords with ⟨hx, hy⟩
  have hprod := mul_nonneg (le_of_lt hgap) ht.1
  nlinarith [hs.1, hs.2, ht.1, ht.2, hε, hσpos, hgap, hprod]

end DirectGLSSW.HOMFLY











