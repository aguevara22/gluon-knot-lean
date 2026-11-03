import DirectGLSSW.FirstCut
import DirectGLSSW.TriangularInverse
import DirectGLSSW.OrderedCapEvents
import DirectGLSSW.CapEventInterpretation

set_option autoImplicit false

namespace DirectGLSSW
open OrderedCapEvents
open CapEventInterpretation
open scoped BigOperators

/-- Natural-indexed interval view of a matrix on `Fin n`; out-of-range
entries are zero. -/
def finiteMatrixIntervalArray {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) : IntervalArray :=
  fun i j =>
    if hi : i < n then
      if hj : j < n then X ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else 0

/-- The candidate inverse assembled from the existing weighted cut sum. -/
def intervalCutResolventCandidate {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun p q =>
    if p.val < q.val then
      -weightedCutSum (fun _ : ℕ => -1) (finiteMatrixIntervalArray X) p.val q.val
    else if p.val = q.val then 1 else 0

noncomputable def eventIntervalArray (q : ℕ → PlanarPoint ℝ) (n : ℕ) : IntervalArray :=
  finiteMatrixIntervalArray (eventMatrix q n)

def eventIndexValues {q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (E : List (EventIndex q n)) : List ℕ := E.map Fin.val

private theorem sum_fin_Ioc {n : ℕ} (p q : Fin n) (f : Fin n → ℚ) :
    (∑ k : Fin n, if p.val < k.val ∧ k.val ≤ q.val then f k else 0) =
      ∑ k : ↥(Finset.Ioc p.val q.val),
        f ⟨k.val, (Finset.mem_Ioc.mp k.property).2.trans_lt q.isLt⟩ := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun k => p.val < k.val ∧ k.val ≤ q.val)
  have hfilter :
      (∑ k : Fin n, if p.val < k.val ∧ k.val ≤ q.val then f k else 0) =
        ∑ k ∈ s, f k := by
    simp [s, Finset.sum_filter]
  let e : ↥s ≃ ↥(Finset.Ioc p.val q.val) := {
    toFun := fun k => ⟨k.1.val, Finset.mem_Ioc.mpr (Finset.mem_filter.mp k.2).2⟩
    invFun := fun k => ⟨⟨k.1, by
        exact (Finset.mem_Ioc.mp k.2).2.trans_lt q.isLt⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_Ioc.mp k.2⟩⟩
    left_inv := by
      intro k
      apply Subtype.ext
      apply Fin.ext
      rfl
    right_inv := by
      intro k
      apply Subtype.ext
      rfl
  }
  calc
    _ = ∑ k ∈ s, f k := hfilter
    _ = ∑ k : ↥s, f k.1 := (Finset.sum_coe_sort _ _).symm
    _ = ∑ k : ↥(Finset.Ioc p.val q.val),
          f ⟨k.val, (Finset.mem_Ioc.mp k.2).2.trans_lt q.isLt⟩ := by
      simpa [e] using
        (e.sum_comp (fun k => f ⟨k.val, (Finset.mem_Ioc.mp k.2).2.trans_lt q.isLt⟩))

theorem intervalCutResolventCandidate_mul_eq_one {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (hX : StrictUpper X) :
    (1 + X) * intervalCutResolventCandidate X = 1 := by
  classical
  let b : IntervalArray := finiteMatrixIntervalArray X
  let G : ℕ → ℕ → ℚ := weightedCutSum (fun _ : ℕ => -1) b
  let W : Matrix (Fin n) (Fin n) ℚ := intervalCutResolventCandidate X
  have hXentry (p q : Fin n) :
      X p q = if p.val < q.val then b p.val q.val else 0 := by
    by_cases hpq : p.val < q.val
    · simp [b, finiteMatrixIntervalArray, hpq, p.isLt, q.isLt]
    · have hz := hX p q (by omega)
      simp [b, finiteMatrixIntervalArray, hpq, hz, p.isLt, q.isLt]
  have hWabove (p q : Fin n) (hpq : p.val < q.val) : W p q = -G p.val q.val := by
    simp [W, intervalCutResolventCandidate, G, b, hpq]
  have hWdiag (p : Fin n) : W p p = 1 := by
    simp [W, intervalCutResolventCandidate]
  have hWbelow (p q : Fin n) (hpq : q.val < p.val) : W p q = 0 := by
    have hnot : ¬p.val < q.val := by omega
    have hne : p.val ≠ q.val := by omega
    simp [W, intervalCutResolventCandidate, hnot, hne]
  have hmul : (1 + X) * W = W + X * W := by
    rw [Matrix.add_mul, Matrix.one_mul]
  apply Matrix.ext
  intro p q
  rw [hmul]
  change W p q + (∑ k : Fin n, X p k * W k q) = (1 : Matrix (Fin n) (Fin n) ℚ) p q
  by_cases hpq : p.val < q.val
  · have hsum_support :
        (∑ k : Fin n, X p k * W k q) =
          ∑ k : Fin n,
            if p.val < k.val ∧ k.val ≤ q.val then X p k * W k q else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hpk : p.val < k.val
      · by_cases hkq : k.val ≤ q.val
        · simp [hpk, hkq]
        · have hqk : q.val < k.val := by omega
          rw [hWbelow k q hqk]
          simp [hpk, hkq]
      · have hzero := hX p k (by omega)
        simp [hzero, hpk]
    rw [hsum_support, sum_fin_Ioc]
    have hcut_sum :
        (∑ k : ↥(Finset.Ioc p.val q.val),
          X p ⟨k.val, (Finset.mem_Ioc.mp k.property).2.trans_lt q.isLt⟩ *
            W ⟨k.val, (Finset.mem_Ioc.mp k.property).2.trans_lt q.isLt⟩ q) =
          X p q - ∑ k ∈ Finset.Ioo p.val q.val,
            b p.val k * G k q.val := by
      let I : Finset ℕ := Finset.Ioo p.val q.val
      let C : Finset ℕ := Finset.Ioc p.val q.val
      let toOpt : ↥C → Option (↥I) := fun k =>
        if hk : k.val = q.val then none else
          some ⟨k.val, Finset.mem_Ioo.mpr ⟨
            (by simpa [C] using (Finset.mem_Ioc.mp k.property).1), by
              have hle := (by simpa [C] using (Finset.mem_Ioc.mp k.property).2)
              omega⟩⟩
      let fromOpt : Option (↥I) → ↥C := fun z =>
        match z with
        | none => ⟨q.val, Finset.mem_Ioc.mpr ⟨hpq, le_rfl⟩⟩
        | some k => ⟨k.val, Finset.mem_Ioc.mpr ⟨
            (Finset.mem_Ioo.mp k.property).1,
            le_of_lt (Finset.mem_Ioo.mp k.property).2⟩⟩
      have hleft : Function.LeftInverse fromOpt toOpt := by
        intro k
        apply Subtype.ext
        by_cases hk : k.val = q.val
        · simp [toOpt, fromOpt, hk]
        · simp [toOpt, fromOpt, hk]
      have hright : Function.RightInverse fromOpt toOpt := by
        intro z
        cases z with
        | none =>
          simp [toOpt, fromOpt]
        | some k =>
          have hkq : k.val ≠ q.val := ne_of_lt (Finset.mem_Ioo.mp k.property).2
          simp [toOpt, fromOpt, hkq]
      let e : ↥C ≃ Option (↥I) := ⟨toOpt, fromOpt, hleft, hright⟩
      let f : Fin n → ℚ := fun k => X p k * W k q
      let g : Option (↥I) → ℚ := fun z =>
        match z with
        | none => X p q
        | some k => f ⟨k.val, lt_trans (Finset.mem_Ioo.mp k.property).2 q.isLt⟩
      have htransport :
          (∑ k : ↥C,
            f ⟨k.val, (Finset.mem_Ioc.mp k.property).2.trans_lt q.isLt⟩) =
            ∑ z : Option (↥I), g z := by
        calc
          _ = ∑ k : ↥C, g (e k) := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : k.val = q.val
            · simp [g, e, toOpt, hk, f, hWdiag]
            · simp [g, e, toOpt, hk, f]
          _ = ∑ z : Option (↥I), g z := e.sum_comp g
      have hopt :
          (∑ z : Option (↥I), g z) =
            X p q + ∑ k : ↥I,
              X p ⟨k.val, lt_trans (Finset.mem_Ioo.mp k.property).2 q.isLt⟩ *
                W ⟨k.val, lt_trans (Finset.mem_Ioo.mp k.property).2 q.isLt⟩ q := by
        simp [g, f, hWdiag]
      have hinterm (k : ↥I) :
          X p ⟨k.val, lt_trans (Finset.mem_Ioo.mp k.property).2 q.isLt⟩ *
              W ⟨k.val, lt_trans (Finset.mem_Ioo.mp k.property).2 q.isLt⟩ q =
            -(b p.val k.val * G k.val q.val) := by
        have hpk : p.val < k.val := (Finset.mem_Ioo.mp k.property).1
        have hkq : k.val < q.val := (Finset.mem_Ioo.mp k.property).2
        have hx : X p ⟨k.val, lt_trans (Finset.mem_Ioo.mp k.property).2 q.isLt⟩ =
            b p.val k.val := by
          simp [b, finiteMatrixIntervalArray, hpk, p.isLt,
            lt_trans (Finset.mem_Ioo.mp k.property).2 q.isLt]
        have hw : W ⟨k.val, lt_trans (Finset.mem_Ioo.mp k.property).2 q.isLt⟩ q =
            -G k.val q.val := hWabove _ _ hkq
        rw [hx, hw]
        ring
      rw [htransport, hopt]
      have hnegative :
          (∑ k : ↥I, -(b p.val k.val * G k.val q.val)) =
            -(∑ k : ↥I, b p.val k.val * G k.val q.val) := by
        rw [Finset.sum_neg_distrib]
      have hcoe :
          (∑ k : ↥I, b p.val k.val * G k.val q.val) =
            ∑ k ∈ I, b p.val k * G k q.val :=
        Finset.sum_coe_sort I (fun k => b p.val k * G k q.val)
      simp_rw [hinterm]
      rw [hnegative, hcoe]
      ring
    rw [hWabove p q hpq, hcut_sum]
    have hrec := weightedCutSum_eq_firstCut (fun _ : ℕ => -1) b hpq
    have hbpq : b p.val q.val = X p q := by
      simp [b, finiteMatrixIntervalArray, p.isLt, q.isLt]
    have hrec' : G p.val q.val = X p q -
        ∑ k ∈ Finset.Ioo p.val q.val, b p.val k * G k q.val := by
      change G p.val q.val = b p.val q.val +
        ∑ k ∈ Finset.Ioo p.val q.val, b p.val k * (-1) * G k q.val at hrec
      rw [hbpq] at hrec
      simpa [sub_eq_add_neg, mul_assoc] using hrec
    rw [← hrec']
    have hpqNe : p ≠ q := by
      intro he
      have hval : p.val = q.val := congrArg Fin.val he
      omega
    simp [Matrix.one_apply, hpqNe]
  · by_cases hdiag : p.val = q.val
    · have hpqEq : p = q := Fin.ext hdiag
      subst q
      have hsum_zero : (∑ k : Fin n, X p k * W k p) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        by_cases hpk : p.val < k.val
        · have hqk : p.val < k.val := hpk
          rw [hWbelow k p hqk]
          simp
        · have hzero := hX p k (by omega)
          simp [hzero]
      rw [hsum_zero, hWdiag p]
      simp [Matrix.one_apply]
    · have hqp : q.val < p.val := by omega
      have hpqNe : p ≠ q := by
        intro he
        exact hdiag (congrArg Fin.val he)
      have hsum_zero : (∑ k : Fin n, X p k * W k q) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        by_cases hpk : p.val < k.val
        · have hqk : q.val < k.val := by omega
          rw [hWbelow k q hqk]
          simp
        · have hzero := hX p k (by omega)
          simp [hzero]
      rw [hWbelow p q hqp, hsum_zero]
      simp [Matrix.one_apply, hpqNe]

theorem intervalCutResolventCandidate_eq_finiteInverse {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (hX : StrictUpper X) :
    intervalCutResolventCandidate X = finiteInverse X n := by
  have hF := strictUpper_finiteInverse X hX
  calc
    intervalCutResolventCandidate X = 1 * intervalCutResolventCandidate X := by
      rw [Matrix.one_mul]
    _ = (finiteInverse X n * (1 + X)) * intervalCutResolventCandidate X := by
      rw [hF.1]
    _ = finiteInverse X n * ((1 + X) * intervalCutResolventCandidate X) := by
      rw [Matrix.mul_assoc]
    _ = finiteInverse X n * 1 := by
      rw [intervalCutResolventCandidate_mul_eq_one X hX]
    _ = finiteInverse X n := by rw [Matrix.mul_one]

theorem finiteInverse_entry_eq_negative_weightedCutSum {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (hX : StrictUpper X)
    (u v : Fin n) (huv : u < v) :
    finiteInverse X n u v =
      -weightedCutSum (fun _ : ℕ => -1) (finiteMatrixIntervalArray X) u.val v.val := by
  have hEq := intervalCutResolventCandidate_eq_finiteInverse X hX
  have hEntry := congrFun (congrFun hEq u) v
  rw [← hEntry]
  simp [intervalCutResolventCandidate, Fin.lt_iff_val_lt_val, huv]

theorem event_branchProduct_zero_of_arc_order_failure
    {q : ℕ → PlanarPoint ℝ} {n : ℕ} (E : List (EventIndex q n))
    (hidx : List.Pairwise (· < ·) E)
    (harc : ¬ List.Pairwise
      (fun c d => (eventPair q n c).1 < (eventPair q n d).1) E) :
    branchProduct (eventIntervalArray q n) (eventIndexValues E) = 0 := by
  classical
  let arcRel : EventIndex q n → EventIndex q n → Prop :=
    fun c d => (eventPair q n c).1 < (eventPair q n d).1
  letI : IsTrans (EventIndex q n) arcRel := ⟨by
    intro a b c hab hbc
    exact Nat.lt_trans hab hbc⟩
  have hbadChain : ¬ List.Chain' arcRel E := by
    intro hc
    apply harc
    exact (List.chain'_iff_pairwise).1 (by simpa [arcRel] using hc)
  have hfilter : ∀ (L : List (EventIndex q n)),
      List.Chain' (· < ·) L → ¬ List.Chain' arcRel L →
      branchProduct (eventIntervalArray q n) (eventIndexValues L) = 0 := by
    intro L
    induction L with
    | nil =>
      intro _ hfail
      have : List.Chain' arcRel [] := by simp
      exact (hfail this).elim
    | cons c rest ih =>
      cases rest with
      | nil =>
        intro _ hfail
        have : List.Chain' arcRel [c] := by simp
        exact (hfail this).elim
      | cons d tail =>
        intro hsorted hfail
        have hsorted' := List.chain'_cons.mp hsorted
        have hcd : c < d := hsorted'.1
        have htailSorted : List.Chain' (· < ·) (d :: tail) := hsorted'.2
        have hrec (hcdArc : arcRel c d) : ¬ List.Chain' arcRel (d :: tail) := by
          intro ht
          exact hfail (List.chain'_cons.mpr ⟨hcdArc, ht⟩)
        have hfactor :
            branchProduct (eventIntervalArray q n) (eventIndexValues (c :: d :: tail)) =
              eventPairing q n c d *
                branchProduct (eventIntervalArray q n) (eventIndexValues (d :: tail)) := by
          simp [branchProduct, eventIndexValues, List.zip_cons_cons,
            eventIntervalArray, finiteMatrixIntervalArray, eventMatrix, hcd]
        by_cases hArc : arcRel c d
        · rw [hfactor, ih htailSorted (hrec hArc)]
          ring
        · have horder : (eventPair q n d).1 ≤ (eventPair q n c).1 := by
            dsimp [arcRel] at hArc
            omega
          have hzero := eventPairing_reverse_arc_zero q n c d horder
          rw [hfactor, hzero]
          ring
  have hChain := List.Pairwise.chain' hidx
  exact hfilter E hChain hbadChain

end DirectGLSSW









