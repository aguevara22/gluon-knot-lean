import DirectGLSSW.TruncationEdgeOrientation
import DirectGLSSW.OrderedEventSuccessor

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge

open DirectGLSSW
open DirectGLSSW.TruncationDirection
open DirectGLSSW.TruncationEdgeLift
open DirectGLSSW.ShortEdgeCyclicAdapter

private theorem cyclicSuccessor_val_uniform {m : ℕ} (i : Fin m) :
    (cyclicSuccessor i).val = if i.val + 1 < m then i.val + 1 else 0 := by
  change (cyclicVertexIndex i 0).val = _
  rw [cyclicVertexIndex_val i (k := 0) (by have := i.isLt; omega)]
  split_ifs <;> omega

private theorem edgeLift_successor_uniform {n : ℕ}
    (a p e : Fin n) (hpa : cyclicSuccessor p = a) (he : e ≠ p) :
    cyclicSuccessor (edgeLift a e) = edgeLift a (cyclicSuccessor e) := by
  have hpval := congrArg Fin.val hpa
  rw [cyclicSuccessor_val_uniform] at hpval
  have hsucc_ne : cyclicSuccessor e ≠ a := by
    intro h
    have hh : cyclicSuccessor e = cyclicSuccessor p := h.trans hpa.symm
    exact he ((cyclicSuccessorPerm n).injective hh)
  have hsuccV : (cyclicSuccessor e).val ≠ a.val := by
    intro h
    exact hsucc_ne (Fin.ext h)
  apply Fin.ext
  by_cases hwrap : e.val + 1 < n
  · have hnext : (cyclicSuccessor e).val = e.val + 1 := by
      simp [cyclicSuccessor_val_uniform, hwrap]
    have hnot : e.val + 1 ≠ a.val := by
      intro h
      apply hsuccV
      rw [hnext]
      exact h
    by_cases hlt : e.val < a.val
    · have hlt' : e.val + 1 < a.val := by omega
      simp [cyclicSuccessor_val_uniform, hwrap, edgeLift, hlt, hlt']
    · have hgt : a.val < e.val + 1 := by omega
      simp [cyclicSuccessor_val_uniform, hwrap, edgeLift, hlt,
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
    simp [cyclicSuccessor_val_uniform, hwrap, edgeLift, elast, hnotlt, hapos]

private noncomputable def edgeLiftPlusShort_uniform {n : ℕ} (a : Fin n) :
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
        · exact ⟨Sum.inl (ShortEdgeCyclicAdapter.collapseFin a i),
            edgeLift_collapseFin a i hi⟩)

private theorem incoming_successor_uniform {n : ℕ}
    (a p : Fin n) (hpa : cyclicSuccessor p = a) :
    cyclicSuccessor (edgeLift a p) = a.castSucc := by
  apply Fin.ext
  have hpaV := congrArg Fin.val hpa
  rw [cyclicSuccessor_val_uniform] at hpaV
  by_cases hpwrap : p.val + 1 < n
  · simp [hpwrap] at hpaV
    have hple : p.val < a.val := by omega
    simpa [edgeLift, cyclicSuccessor_val_uniform, hpwrap, hple] using hpaV
  · have hplast : p.val + 1 = n := by omega
    have ha0 : a.val = 0 := by
      have h := hpaV
      simp only [if_neg hpwrap] at h
      exact h.symm
    simpa [edgeLift, cyclicSuccessor_val_uniform, hpwrap, hplast, ha0] using hpaV

private theorem short_successor_uniform {n : ℕ}
    (a : Fin n) :
    cyclicSuccessor (a.castSucc : Fin (n + 1)) = edgeLift a a := by
  apply Fin.ext
  have ha : a.val + 1 < n + 1 := by omega
  simp [cyclicSuccessor_val_uniform, edgeLift, ha]

private theorem tangent_short_uniform {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε : ℝ) :
    cyclicTangent (truncateCyclicCorner q a p scale ε) (a.castSucc : Fin (n + 1)) =
      ε • (cyclicTangent q p + scale • cyclicTangent q a) := by
  have hnewidx : edgeLift a a = ⟨a.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [edgeLift]
  change truncateCyclicCorner q a p scale ε
      (cyclicSuccessor (a.castSucc : Fin (n + 1))) -
      truncateCyclicCorner q a p scale ε (a.castSucc : Fin (n + 1)) = _
  rw [short_successor_uniform, hnewidx]
  change truncateCyclicCorner q a p scale ε ⟨a.val + 1, by omega⟩ -
      truncateCyclicCorner q a p scale ε ⟨a.val, by omega⟩ = _
  rw [truncateCyclicCorner_new, truncateCyclicCorner_anchor]
  have hpTan : cyclicTangent q p = q a - q p := by
    simp [cyclicTangent, hpa]
  rw [hpTan]
  ext <;> simp [cyclicTangent, smul_eq_mul] <;> ring

/-- Strict left turns are preserved by the actual corner truncation.  The old
turn at the cut is split into the two turns adjoining the new short edge. -/
theorem truncate_uniform_left {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ e : Fin n,
      0 < planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)))
    (a p : Fin n) (hpa : cyclicSuccessor p = a)
    (scale ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hscale : 0 < ε * scale) (hscale1 : ε * scale < 1) :
    ∀ i : Fin (n + 1),
      0 < planarDet
        (cyclicTangent (truncateCyclicCorner q a p scale ε) i)
        (cyclicTangent (truncateCyclicCorner q a p scale ε) (cyclicSuccessor i)) := by
  classical
  let q' := truncateCyclicCorner q a p scale ε
  let short : Fin (n + 1) := a.castSucc
  have hn : 2 ≤ n := by have hs := hq.size_ge_three; omega
  have hpne : p ≠ a := by
    intro h
    have hf : cyclicSuccessor p = p := hpa.trans h.symm
    exact cyclicSuccessor_ne_self hn p hf
  have hscale_pos : 0 < scale := by
    by_contra hh
    have hle : scale ≤ 0 := le_of_not_gt hh
    exact (not_le_of_gt hscale) (mul_nonpos_of_nonneg_of_nonpos hε.le hle)
  have hfactor (e : Fin n) :
      0 < if e = p then 1 - ε else if e = a then 1 - ε * scale else (1 : ℝ) := by
    by_cases hep : e = p
    · simp [hep]; linarith
    · by_cases hea : e = a
      · simp [hep, hea, hpne.symm]; linarith
      · simp [hep, hea]
  have hsucc (e : Fin n) (he : e ≠ p) :
      cyclicSuccessor (edgeLift a e) = edgeLift a (cyclicSuccessor e) :=
    edgeLift_successor_uniform a p e hpa he
  have hu : 0 < planarDet (cyclicTangent q p) (cyclicTangent q a) := by
    simpa [hpa] using hleft p
  have hshortSucc := short_successor_uniform (n := n) a
  have hincoming := incoming_successor_uniform (n := n) a p hpa
  have hshortVec := tangent_short_uniform q a p hpa scale ε
  have hsplit_left :
      0 < planarDet
        (cyclicTangent q' (edgeLift a p))
        (cyclicTangent q' short) := by
    have hpTan := truncateCyclicCorner_edge_tangent_scale hn q a p hpa scale ε
      hε hε1 hscale hscale1 p
    rw [hpTan, hshortVec]
    have hfac : (if p = p then 1 - ε else if p = a then 1 - ε * scale else (1 : ℝ)) =
        1 - ε := by simp [hpne.symm]
    rw [hfac]
    have hd : planarDet ((1 - ε) • cyclicTangent q p)
        (ε • (cyclicTangent q p + scale • cyclicTangent q a)) =
        ((1 - ε) * ε * scale) * planarDet (cyclicTangent q p) (cyclicTangent q a) := by
      simp [planarDet, smul_eq_mul]
      <;> ring
    rw [hd]
    exact mul_pos (mul_pos (mul_pos (sub_pos.mpr hε1) hε) hscale_pos) hu
  have hsplit_right :
      0 < planarDet
        (cyclicTangent q' short)
        (cyclicTangent q' (edgeLift a a)) := by
    have haTan := truncateCyclicCorner_edge_tangent_scale hn q a p hpa scale ε
      hε hε1 hscale hscale1 a
    rw [hshortVec, haTan]
    have hfac : (if a = p then 1 - ε else if a = a then 1 - ε * scale else (1 : ℝ)) =
        1 - ε * scale := by simp [hpne.symm]
    rw [hfac]
    have hd : planarDet
        (ε • (cyclicTangent q p + scale • cyclicTangent q a))
        ((1 - ε * scale) • cyclicTangent q a) =
        (ε * (1 - ε * scale)) * planarDet (cyclicTangent q p) (cyclicTangent q a) := by
      simp [planarDet, smul_eq_mul]
      <;> ring
    rw [hd]
    exact mul_pos (mul_pos hε (sub_pos.mpr hscale1)) hu
  let E := edgeLiftPlusShort_uniform a
  intro i
  obtain ⟨x, rfl⟩ := E.surjective i
  cases x with
  | inr u =>
      simpa [E, edgeLiftPlusShort_uniform, q', short, hshortSucc] using hsplit_right
  | inl e =>
      by_cases he : e = p
      · subst e
        simpa [E, edgeLiftPlusShort_uniform, q', short, hincoming] using hsplit_left
      · change 0 < planarDet (cyclicTangent q' (edgeLift a e))
          (cyclicTangent q' (cyclicSuccessor (edgeLift a e)))
        rw [hsucc e he]
        have hsign := truncateCyclicCorner_edge_determinant_sign_iff hn q a p hpa
          scale ε hε hε1 hscale hscale1 e (cyclicSuccessor e)
        exact (hsign.mpr (hleft e))

#check @truncate_uniform_left


end DirectGLSSW.HOMFLY.PolygonDrawingBridge
