import PolygonRotationSum
import TwoBendContraction
import DirectGLSSW.TruncationEdgeOrientation

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge

open DirectGLSSW DirectGLSSW.TruncationDirection
open DirectGLSSW.TruncationEdgeLift
open DirectGLSSW.HOMFLY.PrincipalTurning
open scoped BigOperators

private theorem cyclicSuccessor_val_local {m : ℕ} (i : Fin m) :
    (cyclicSuccessor i).val = if i.val + 1 < m then i.val + 1 else 0 := by
  change (cyclicVertexIndex i 0).val = _
  rw [cyclicVertexIndex_val i (k := 0) (by have := i.isLt; omega)]
  split_ifs <;> omega

private theorem edgeLift_successor_of_ne_prev {n : ℕ}
    (a p e : Fin n) (hpa : cyclicSuccessor p = a) (he : e ≠ p) :
    cyclicSuccessor (edgeLift a e) = edgeLift a (cyclicSuccessor e) := by
  have hpval := congrArg Fin.val hpa
  rw [cyclicSuccessor_val_local] at hpval
  have hsucc_ne : cyclicSuccessor e ≠ a := by
    intro h
    have hh : cyclicSuccessor e = cyclicSuccessor p := h.trans hpa.symm
    have hp := (cyclicSuccessorPerm n).injective hh
    exact he hp
  have hsuccV : (cyclicSuccessor e).val ≠ a.val := by
    intro h
    exact hsucc_ne (Fin.ext h)
  apply Fin.ext
  by_cases hwrap : e.val + 1 < n
  · have hnext : (cyclicSuccessor e).val = e.val + 1 := by
      simp [cyclicSuccessor_val_local, hwrap]
    have hnot : e.val + 1 ≠ a.val := by
      intro h
      apply hsuccV
      rw [hnext]
      exact h
    by_cases hlt : e.val < a.val
    · have hlt' : e.val + 1 < a.val := by omega
      simp [cyclicSuccessor_val_local, hwrap, edgeLift, hlt, hlt']
    · have hgt : a.val < e.val + 1 := by omega
      simp [cyclicSuccessor_val_local, hwrap, edgeLift, hlt,
        not_lt.mpr (Nat.le_of_lt hgt)]
  · have elast : e.val + 1 = n := by omega
    have ha0 : a.val ≠ 0 := by
      intro hz
      have hpwrap : p.val + 1 = n := by
        by_cases hpw : p.val + 1 < n
        · have hbad : p.val + 1 = a.val := by simpa [hpw] using hpval
          omega
        · omega
      exact he (Fin.ext (by omega))
    have hnotlt : ¬ e.val < a.val := by omega
    have hapos : 0 < a.val := Nat.pos_of_ne_zero ha0
    simp [cyclicSuccessor_val_local, hwrap, edgeLift, elast, hnotlt, hapos]

private noncomputable def edgeLiftPlusShort {n : ℕ} (a : Fin n) :
    (Fin n ⊕ Unit) ≃ Fin (n + 1) :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl e => edgeLift a e
      | Sum.inr _ => a.castSucc)
    (by
      constructor
      · intro x y hxy
        cases x with
        | inl e =>
          cases y with
          | inl f => exact congrArg Sum.inl (edgeLift_injective a hxy)
          | inr u => exact False.elim (edgeLift_ne_short a e hxy)
        | inr u =>
          cases y with
          | inl f => exact False.elim (edgeLift_ne_short a f hxy.symm)
          | inr v => rfl
      · intro i
        by_cases hi : i = a.castSucc
        · exact ⟨Sum.inr (), hi.symm⟩
        · exact ⟨Sum.inl (ShortEdgeCyclicAdapter.collapseFin a i), edgeLift_collapseFin a i hi⟩)

private theorem truncate_originalCornerTotalTurn_eq {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (a p : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hturn : 0 < planarDet (q a - q p)
      (q (cyclicSuccessor a) - q a)) :
    originalCornerTotalTurn (truncateCyclicCorner q a p scale ε) =
      originalCornerTotalTurn q := by
  classical
  let q' : Fin (n + 1) → PlanarPoint ℝ := truncateCyclicCorner q a p scale ε
  let short : Fin (n + 1) := a.castSucc
  have hn : 2 ≤ n := by have h := hq.size_ge_three; omega
  have hscale_pos : 0 < scale := by
    by_contra hnscale
    have hle : scale ≤ 0 := le_of_not_gt hnscale
    exact (not_le_of_gt hscale) (mul_nonpos_of_nonneg_of_nonpos hε.le hle)
  have hpa_ne : p ≠ a := by
    intro h
    have hs : cyclicSuccessor p = p := hpa.trans h.symm
    exact cyclicSuccessor_ne_self hn p hs
  have hfactor_pos (e : Fin n) :
      0 < (if e = p then 1 - ε else if e = a then 1 - ε * scale else (1 : ℝ)) := by
    by_cases hep : e = p
    · simp [hep]; linarith
    · by_cases hea : e = a
      · simp [hep, hea, hpa_ne.symm]; linarith
      · simp [hep, hea]
  have hfactor_vec (e : Fin n) :
      polygonEdgeVector q' (edgeLift a e) =
        (((if e = p then 1 - ε else if e = a then 1 - ε * scale else (1 : ℝ)) : ℝ) : ℂ) *
          polygonEdgeVector q e := by
    have ht := truncateCyclicCorner_edge_tangent_scale hn q a p hpa scale ε
      hε hε1 hscale hscale1 e
    have ht1 := congrArg Prod.fst ht
    have ht2 := congrArg Prod.snd ht
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at ht1 ht2
    apply Complex.ext
    · simpa [q', polygonEdgeVector, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul] using ht1
    · simpa [q', polygonEdgeVector, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul] using ht2
  have hsucc (e : Fin n) (he : e ≠ p) :
      cyclicSuccessor (edgeLift a e) = edgeLift a (cyclicSuccessor e) :=
    edgeLift_successor_of_ne_prev a p e hpa he
  have hpredLift (i : Fin n) (hi : i ≠ a) :
      (cyclicSuccessorPerm (n + 1)).symm (edgeLift a i) =
        edgeLift a ((cyclicSuccessorPerm n).symm i) := by
    apply (cyclicSuccessorPerm (n + 1)).injective
    rw [Equiv.apply_symm_apply]
    have hpre_ne : (cyclicSuccessorPerm n).symm i ≠ p := by
      intro he
      have hii : i = a := by simpa [hpa] using congrArg (cyclicSuccessorPerm n) he
      exact hi hii
    have hid : cyclicSuccessor ((cyclicSuccessorPerm n).symm i) = i :=
      (cyclicSuccessorPerm n).apply_symm_apply i
    simpa [hid] using (hsucc ((cyclicSuccessorPerm n).symm i) hpre_ne).symm
  have hturn_old (i : Fin n) (hi : i ≠ a) :
      originalCornerTurn q' (edgeLift a i) = originalCornerTurn q i := by
    unfold originalCornerTurn
    rw [hpredLift i hi, hfactor_vec i,
      hfactor_vec ((cyclicSuccessorPerm n).symm i)]
    exact turn_positive_rescale
      (polygonEdgeVector q ((cyclicSuccessorPerm n).symm i))
      (polygonEdgeVector q i)
      (if i = p then 1 - ε else if i = a then 1 - ε * scale else 1)
      (if (cyclicSuccessorPerm n).symm i = p then 1 - ε
        else if (cyclicSuccessorPerm n).symm i = a then 1 - ε * scale else 1)
      (hfactor_pos i) (hfactor_pos ((cyclicSuccessorPerm n).symm i))
  have hshort_succ : cyclicSuccessor short = edgeLift a a := by
    apply Fin.ext
    have ha : a.val + 1 < n + 1 := by omega
    simp [short, edgeLift, cyclicSuccessor_val_local, ha]
  have hincoming_succ : cyclicSuccessor (edgeLift a p) = short := by
    apply Fin.ext
    have hpaV := congrArg Fin.val hpa
    rw [cyclicSuccessor_val_local] at hpaV
    by_cases hpwrap : p.val + 1 < n
    · simp [hpwrap] at hpaV
      have hple : p.val < a.val := by omega
      simpa [short, edgeLift, cyclicSuccessor_val_local, hpwrap, hple] using hpaV
    · have hplast : p.val + 1 = n := by omega
      have ha0 : a.val = 0 := by
        have hpaV0 := hpaV
        simp only [if_neg hpwrap] at hpaV0
        exact hpaV0.symm
      simpa [short, edgeLift, cyclicSuccessor_val_local, hpwrap, hplast, ha0] using hpaV
  have hpred_short : (cyclicSuccessorPerm (n + 1)).symm short = edgeLift a p := by
    apply (cyclicSuccessorPerm (n + 1)).injective
    rw [Equiv.apply_symm_apply]
    exact hincoming_succ.symm
  have hpred_lift_a :
      (cyclicSuccessorPerm (n + 1)).symm (edgeLift a a) = short := by
    apply (cyclicSuccessorPerm (n + 1)).injective
    rw [Equiv.apply_symm_apply]
    exact hshort_succ.symm
  have hshort_vec : polygonEdgeVector q' short =
      (ε : ℂ) * (polygonEdgeVector q p + (scale : ℂ) * polygonEdgeVector q a) := by
    have hnewidx : edgeLift a a = ⟨a.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [edgeLift]
    have hcoords : cyclicTangent q' short =
        ε • (cyclicTangent q p + scale • cyclicTangent q a) := by
      change truncateCyclicCorner q a p scale ε (cyclicSuccessor short) -
        truncateCyclicCorner q a p scale ε short = _
      rw [hshort_succ, hnewidx]
      change truncateCyclicCorner q a p scale ε ⟨a.val + 1, by omega⟩ -
        truncateCyclicCorner q a p scale ε ⟨a.val, by omega⟩ = _
      rw [truncateCyclicCorner_new, truncateCyclicCorner_anchor]
      have hpTan : cyclicTangent q p = q a - q p := by
        simp [cyclicTangent, hpa]
      rw [hpTan]
      ext <;> simp [cyclicTangent, smul_eq_mul] <;> ring
    apply Complex.ext <;>
      simp [polygonEdgeVector, hcoords, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul] <;> ring
  have hdet :
      (polygonEdgeVector q p).re * (polygonEdgeVector q a).im -
        (polygonEdgeVector q p).im * (polygonEdgeVector q a).re ≠ 0 := by
    have hpos : 0 <
        (polygonEdgeVector q p).re * (polygonEdgeVector q a).im -
          (polygonEdgeVector q p).im * (polygonEdgeVector q a).re := by
      simpa [polygonEdgeVector, cyclicTangent, hpa, planarDet] using hturn
    exact ne_of_gt hpos
  have hshort_turn :
      originalCornerTurn q' short =
        Complex.arg ((polygonEdgeVector q p + (scale : ℂ) * polygonEdgeVector q a) /
          polygonEdgeVector q p) := by
    unfold originalCornerTurn
    rw [hpred_short, hshort_vec, hfactor_vec p]
    have hfac : (if p = p then 1 - ε else if p = a then 1 - ε * scale else (1 : ℝ)) =
        1 - ε := by simp [hpa_ne]
    rw [hfac]
    exact (turn_positive_rescale (polygonEdgeVector q p)
      (polygonEdgeVector q p + (scale : ℂ) * polygonEdgeVector q a)
      ε (1 - ε) hε (sub_pos.mpr hε1))
  have hcorner_turn :
      originalCornerTurn q' (edgeLift a a) =
        Complex.arg (polygonEdgeVector q a /
          (polygonEdgeVector q p + (scale : ℂ) * polygonEdgeVector q a)) := by
    unfold originalCornerTurn
    rw [hpred_lift_a, hfactor_vec a, hshort_vec]
    have hfac : (if a = p then 1 - ε else if a = a then 1 - ε * scale else (1 : ℝ)) =
        1 - ε * scale := by simp [hpa_ne.symm]
    rw [hfac]
    exact (turn_positive_rescale
      (polygonEdgeVector q p + (scale : ℂ) * polygonEdgeVector q a)
      (polygonEdgeVector q a) (1 - ε * scale) ε
      (sub_pos.mpr hscale1) hε)
  have hreplace : originalCornerTurn q' (edgeLift a a) +
      originalCornerTurn q' short = originalCornerTurn q a := by
    rw [hcorner_turn, hshort_turn]
    have h := positive_combination_two_bend_contraction
      (polygonEdgeVector q p) (polygonEdgeVector q a) 1 scale (by norm_num)
      hscale_pos hdet
    have hold : originalCornerTurn q a =
        Complex.arg (polygonEdgeVector q a / polygonEdgeVector q p) := by
      unfold originalCornerTurn
      have hp : (cyclicSuccessorPerm n).symm a = p := by
        apply (cyclicSuccessorPerm n).injective
        rw [Equiv.apply_symm_apply]
        exact hpa.symm
      rw [hp]
    rw [hold]
    simpa [one_mul, add_comm] using h
  have hsum_split :
      originalCornerTotalTurn q' =
        (∑ e : Fin n, originalCornerTurn q' (edgeLift a e)) +
          originalCornerTurn q' short := by
    unfold originalCornerTotalTurn
    let E := edgeLiftPlusShort a
    calc
      (∑ i : Fin (n + 1), originalCornerTurn q' i) =
          ∑ x : Fin n ⊕ PUnit, originalCornerTurn q' (E x) :=
        (Fintype.sum_equiv E _ _ (fun _ => rfl)).symm
      _ = (∑ e : Fin n, originalCornerTurn q' (edgeLift a e)) +
          originalCornerTurn q' short := by
        simp [E, edgeLiftPlusShort, Fintype.sum_sum_type, short]
  have hsum_replace :
      (∑ e : Fin n, originalCornerTurn q' (edgeLift a e)) +
          originalCornerTurn q' short = originalCornerTotalTurn q := by
    unfold originalCornerTotalTurn
    let f : Fin n → ℝ := fun e => originalCornerTurn q' (edgeLift a e)
    let g : Fin n → ℝ := fun e => originalCornerTurn q e
    have hdiff : (∑ e : Fin n, (f e - g e)) = f a - g a := by
      apply Finset.sum_eq_single a
      · intro e he hne
        have he' : e ≠ a := hne
        simp [f, g, hturn_old e he']
      · simp
    have hsum : (∑ e : Fin n, f e) = (∑ e : Fin n, g e) + (f a - g a) := by
      have hs : (∑ e : Fin n, (f e - g e)) =
          (∑ e : Fin n, f e) - (∑ e : Fin n, g e) := by
        rw [Finset.sum_sub_distrib]
      rw [hdiff] at hs
      linarith
    change (∑ e : Fin n, f e) + originalCornerTurn q' short =
      (∑ e : Fin n, g e)
    rw [hsum]
    have hrep : f a + originalCornerTurn q' short = g a := by
      exact hreplace
    dsimp [f, g] at hrep ⊢
    linarith
  exact hsum_split.trans hsum_replace

/-- Corner truncation preserves the total principal turn of the actual positive
polygon-event diagram. The changed corner is replaced by its two exact bends. -/
theorem truncate_positive_totalTurn_eq {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (a p : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (hturn : 0 < planarDet (q a - q p)
      (q (cyclicSuccessor a) - q a)) :
    PrincipalTurning.totalTurn
      (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ) =
    PrincipalTurning.totalTurn (positivePolygonEventDiagram q hq) := by
  rw [positivePolygonEventDiagram_totalTurn, positivePolygonEventDiagram_totalTurn]
  exact truncate_originalCornerTotalTurn_eq q hq a p hpa scale ε
    hε hε1 hscale hscale1 hturn

theorem truncate_positive_turnInteger_eq {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (a p : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (hturn : 0 < planarDet (q a - q p)
      (q (cyclicSuccessor a) - q a)) :
    PrincipalTurning.turnInteger
      (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ) =
    PrincipalTurning.turnInteger (positivePolygonEventDiagram q hq) := by
  apply PrincipalTurning.turnInteger_unique _ _
  rw [truncate_positive_totalTurn_eq q hq a p hpa scale ε hε hε1 hscale hscale1 hQ hturn]
  exact PrincipalTurning.totalTurn_eq_turnInteger _

#check @truncate_positive_totalTurn_eq

#check @truncate_positive_turnInteger_eq


end DirectGLSSW.HOMFLY.PolygonDrawingBridge
