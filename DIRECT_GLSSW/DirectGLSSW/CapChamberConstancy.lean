import DirectGLSSW.CapCrossingEvent
import DirectGLSSW.EndpointActualPropagation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.CapChamberConstancy

open DirectGLSSW
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.EndpointEventGeometry
open DirectGLSSW.GlobalCapAlgebra
open DirectGLSSW.GlobalCapIntertwining
open DirectGLSSW.EndpointCurrent
open DirectGLSSW.EndpointPropagation

private theorem horizontalMove_height (q : ℕ → PlanarPoint ℝ) (t : ℝ) (a : ℕ) :
    (horizontalMove q t a).2 = (q a).2 := by
  by_cases ha : a = 0
  · subst a
    simp [horizontalMove, EndpointEventGeometry.moveEndpoint,
      Prod.snd_add]
  · simp [horizontalMove, EndpointEventGeometry.moveEndpoint, ha]

private theorem scalarSignValue_same_sign {u v : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hneg : (u < 0) ↔ (v < 0)) :
    scalarSignValue u = scalarSignValue v := by
  by_cases h : u < 0
  · have hvneg : v < 0 := hneg.mp h
    simp [scalarSignValue, hu, hv, h, hvneg]
  · have hvnonneg : ¬ v < 0 := fun hv' => h (hneg.mpr hv')
    have huPos : 0 < u := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hu)
    have hvPos : 0 < v := lt_of_le_of_ne (le_of_not_gt hvnonneg) (Ne.symm hv)
    simp [scalarSignValue, hu, hv, not_lt_of_gt huPos, not_lt_of_gt hvPos]

private theorem polygonSign_eq_on_horizontal_chamber
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) {x y : ℝ} (hxy : x < y)
    (hchamber : ∀ t, t ∈ Set.Icc x y → ∀ a b c,
      a < b → b < c → c ≤ n →
      polygonHDet (horizontalMove q t) a b c ≠ 0)
    {a b c : ℕ} (hab : a < b) (hbc : b < c) (hc : c ≤ n) :
    polygonSignArray (horizontalMove q x) a b c =
      polygonSignArray (horizontalMove q y) a b c := by
  let f : ℝ → ℝ := fun t => polygonHDet (horizontalMove q t) a b c
  have hxmem : x ∈ Set.Icc x y := ⟨le_rfl, le_of_lt hxy⟩
  have hymem : y ∈ Set.Icc x y := ⟨le_of_lt hxy, le_rfl⟩
  have hfx : f x ≠ 0 := by
    exact hchamber x hxmem a b c hab hbc hc
  have hfy : f y ≠ 0 := by
    exact hchamber y hymem a b c hab hbc hc
  have hcontinuous : ContinuousOn f (Set.Icc x y) := by
    by_cases ha : a = 0
    · subst a
      have heq : f = fun t =>
          polygonHDet q 0 b c + t * planarDet (q b - q c) (1, 0) := by
        funext t
        calc
          f t = polygonHDet (EndpointEventGeometry.moveEndpoint q (1, 0) t) 0 b c := rfl
          _ = polygonHDet q 0 b c + t * planarDet (q b - q c) (1, 0) :=
            EndpointEventGeometry.moveEndpoint_farDet q (1, 0) (by omega) hbc t
      rw [heq]
      exact continuousOn_const.add (continuousOn_id.mul continuousOn_const)
    · have heq : f = fun _ : ℝ => polygonHDet q a b c := by
        funext t
        have hb : b ≠ 0 := by omega
        have hc : c ≠ 0 := by omega
        have hpa : horizontalMove q t a = q a := by
          simp [horizontalMove, EndpointEventGeometry.moveEndpoint, ha]
        have hpb : horizontalMove q t b = q b := by
          simp [horizontalMove, EndpointEventGeometry.moveEndpoint, hb]
        have hpc : horizontalMove q t c = q c := by
          simp [horizontalMove, EndpointEventGeometry.moveEndpoint, hc]
        simp only [f, polygonHDet, hpa, hpb, hpc]
      rw [heq]
      exact continuousOn_const
  have hsign : scalarSignValue (f x) = scalarSignValue (f y) := by
    by_cases hxneg : f x < 0
    · by_cases hyneg : f y < 0
      · exact scalarSignValue_same_sign hfx hfy ⟨fun _ => hyneg, fun _ => hxneg⟩
      · have hypos : 0 < f y := lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm hfy)
        have hzero : (0 : ℝ) ∈ Set.Icc (f x) (f y) :=
          ⟨le_of_lt hxneg, le_of_lt hypos⟩
        obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (le_of_lt hxy) hcontinuous hzero
        have htne := hchamber t ht a b c hab hbc hc
        change f t ≠ 0 at htne
        rw [hft] at htne
        exact False.elim (htne rfl)
    · have hxpos : 0 < f x := lt_of_le_of_ne (le_of_not_gt hxneg) (Ne.symm hfx)
      by_cases hyneg : f y < 0
      · have hzero : (0 : ℝ) ∈ Set.Icc (f y) (f x) :=
          ⟨le_of_lt hyneg, le_of_lt hxpos⟩
        obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (le_of_lt hxy) hcontinuous hzero
        have htne := hchamber t ht a b c hab hbc hc
        change f t ≠ 0 at htne
        rw [hft] at htne
        exact False.elim (htne rfl)
      · have hypos : 0 < f y := lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm hfy)
        have hneg : (f x < 0) ↔ (f y < 0) :=
          Iff.intro
            (fun h => False.elim ((not_lt_of_gt hxpos) h))
            (fun h => False.elim ((not_lt_of_gt hypos) h))
        exact scalarSignValue_same_sign hfx hfy hneg
  simpa [polygonSignArray, f] using hsign

private theorem endpointCoefficient_congr_of_ordered_signs
    (d : ℕ → ℚ) (H₀ H₁ : TripleArray) (n : ℕ)
    (hH : ∀ a b c, a < b → b < c → c ≤ n → H₁ a b c = H₀ a b c)
    {l J : ℕ} (hl : 0 < l) (hlJ : l < J) (hJn : J ≤ n) :
    endpointCoefficient d H₁ l J = endpointCoefficient d H₀ l J := by
  classical
  unfold endpointCoefficient
  have hroot : ∀ b, 0 < b → b < J → H₁ 0 b J = H₀ 0 b J := by
    intro b hb hbJ
    exact hH 0 b J (by omega) hbJ hJn
  have hcore : ∀ a b c, 0 < a → a < b → b < c → c ≤ J → H₁ a b c = H₀ a b c := by
    intro a b c ha hab hbc hcJ
    exact hH a b c hab hbc (le_trans hcJ hJn)
  rw [hroot l hl hlJ]
  congr 1
  let w₀ := fun b => (d b - H₀ 0 b J) / 2
  let w₁ := fun b => (d b - H₁ 0 b J) / 2
  let b₀ := ordinaryCurrent (fun _ b _ => d b) H₀
  let b₁ := ordinaryCurrent (fun _ b _ => d b) H₁
  change weightedCutSum w₁ b₁ l J = weightedCutSum w₀ b₀ l J
  calc
    weightedCutSum w₁ b₁ l J = weightedCutSum w₀ b₁ l J := by
      unfold weightedCutSum
      apply Finset.sum_congr rfl
      intro S hS
      apply congrArg (fun z : ℚ => z * branchProduct b₁ (cutVertices l J S))
      apply Finset.prod_congr rfl
      intro b hb
      have hbI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hS hb)
      dsimp [w₀, w₁]
      rw [hroot b (by omega) hbI.2]
    _ = weightedCutSum w₀ b₀ l J := by
      apply weightedCutSum_congr_of_branch_eq w₀ hlJ
      intro a b hla hab hbJ
      apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hab
      intro x y z hax hxy hyz hzb
      exact hcore x y z (by omega) hxy hyz (by omega)

/-- `F`, `C`, and `J` are constant between two positions whenever every
ordered triple determinant of the moved word stays nonzero on the interval. -/
theorem lineCapFCJ_constant_on_horizontal_chamber
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) {x y : ℝ} (hxy : x < y)
    (hchamber : ∀ t, t ∈ Set.Icc x y → ∀ a b c,
      a < b → b < c → c ≤ n →
      polygonHDet (horizontalMove q t) a b c ≠ 0) :
    lineCapF (horizontalMove q x) n = lineCapF (horizontalMove q y) n ∧
    lineCapC (horizontalMove q x) n = lineCapC (horizontalMove q y) n ∧
    lineCapJ (horizontalMove q x) n = lineCapJ (horizontalMove q y) n := by
  let Hₓ := polygonSignArray (horizontalMove q x)
  let Hᵧ := polygonSignArray (horizontalMove q y)
  have hsign : ∀ a b c, a < b → b < c → c ≤ n → Hₓ a b c = Hᵧ a b c := by
    intro a b c hab hbc hc
    exact polygonSign_eq_on_horizontal_chamber q n hxy hchamber hab hbc hc
  have hnearX : lineCapNear (horizontalMove q x) n = lineCapNear q n := by
    funext k
    exact congrArg scalarSignValue (horizontalMove_height q x k)
  have hnearY : lineCapNear (horizontalMove q y) n = lineCapNear q n := by
    funext k
    exact congrArg scalarSignValue (horizontalMove_height q y k)
  have hnear : lineCapNear (horizontalMove q x) n = lineCapNear (horizontalMove q y) n :=
    hnearX.trans hnearY.symm
  have hC : lineCapC (horizontalMove q x) n = lineCapC (horizontalMove q y) n := by
    change EndpointPropagation.finiteKernel
        (endpointCoefficient (lineCapNear (horizontalMove q x) n)
          (polygonSignArray (horizontalMove q x))) n =
      EndpointPropagation.finiteKernel
        (endpointCoefficient (lineCapNear (horizontalMove q y) n)
          (polygonSignArray (horizontalMove q y))) n
    rw [hnearX, hnearY]
    ext i j
    by_cases hij : i.val < j.val
    · simp only [EndpointPropagation.finiteKernel, if_pos hij]
      exact endpointCoefficient_congr_of_ordered_signs
        (lineCapNear q n) Hᵧ Hₓ n hsign
        (by omega) (by omega) (by have := j.isLt; omega)
    · simp [EndpointPropagation.finiteKernel, hij]
  have hF : lineCapF (horizontalMove q x) n = lineCapF (horizontalMove q y) n := by
    calc
      lineCapF (horizontalMove q x) n = finiteInverse (lineCapC (horizontalMove q x) n) n :=
        lineCapF_eq_finiteInverse (horizontalMove q x) n
      _ = finiteInverse (lineCapC (horizontalMove q y) n) n := by rw [hC]
      _ = lineCapF (horizontalMove q y) n :=
        (lineCapF_eq_finiteInverse (horizontalMove q y) n).symm
  have hS : lineCapS (horizontalMove q x) n = lineCapS (horizontalMove q y) n := by
    have hh : GlobalCapAlgebra.lineCapHeights (horizontalMove q x) n =
        GlobalCapAlgebra.lineCapHeights (horizontalMove q y) n := by
      funext r
      exact congrArg scalarSignValue (horizontalMove_height q x (r.val + 1)) |>.trans
        (congrArg scalarSignValue (horizontalMove_height q y (r.val + 1))).symm
    exact congrArg Matrix.diagonal hh
  have hJ : lineCapJ (horizontalMove q x) n = lineCapJ (horizontalMove q y) n := by
    simp [lineCapJ, hC, hF, hS]
  exact ⟨hF, hC, hJ⟩







end DirectGLSSW.CapChamberConstancy
