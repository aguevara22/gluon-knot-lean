import ActualSideIndex

set_option autoImplicit false
noncomputable section
open DirectGLSSW Filter Topology
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

theorem normalIndexOrZero_eq_literal {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (ε : ℝ) :
    normalIndexOrZero q i ε =
      if h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε) then
        windingIndex q (normalAtEdgeMidpoint q i ε) h else 0 := rfl

private theorem half_minus_im_ne_zero (ε : ℝ) (hε : ε ≠ 0) :
    (((1 / 2 : ℂ) - (ε : ℂ) * Complex.I) /
      (-(1 / 2 : ℂ) - (ε : ℂ) * Complex.I)).im ≠ 0 := by
  have hden : (1 / 4 : ℝ) + ε ^ 2 ≠ 0 := by positivity
  rw [Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_add,
    sub_zero, zero_sub]
  simp only [Complex.normSq_apply]
  norm_num at *
  have hden' : 1 + ε * ε * 4 ≠ 0 := by
    nlinarith [sq_nonneg ε]
  intro hz
  field_simp [hden'] at hz

private theorem base_ratio_normal_eq {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (ε : ℝ)
    (hdir : q (cyclicSuccessorPerm n i) - q i ≠ 0) :
    (q (cyclicSuccessorPerm n i) - normalAtEdgeMidpoint q i ε) /
        (q i - normalAtEdgeMidpoint q i ε) =
      ((1 / 2 : ℂ) - (ε : ℂ) * Complex.I) /
        (-(1 / 2 : ℂ) - (ε : ℂ) * Complex.I) := by
  let v := q (cyclicSuccessorPerm n i) - q i
  have hn : q (cyclicSuccessorPerm n i) - normalAtEdgeMidpoint q i ε =
      ((1 / 2 : ℂ) - (ε : ℂ) * Complex.I) * v := by
    dsimp [normalAtEdgeMidpoint, v]
    push_cast
    ring
  have hd : q i - normalAtEdgeMidpoint q i ε =
      (-(1 / 2 : ℂ) - (ε : ℂ) * Complex.I) * v := by
    dsimp [normalAtEdgeMidpoint, v]
    push_cast
    ring
  rw [hn, hd]
  exact mul_div_mul_right _ _ hdir

private theorem half_minus_ratio_conj (ε : ℝ) :
    ((1 / 2 : ℂ) - ((-ε : ℝ) : ℂ) * Complex.I) /
        (-(1 / 2 : ℂ) - ((-ε : ℝ) : ℂ) * Complex.I) =
      conj (((1 / 2 : ℂ) - (ε : ℂ) * Complex.I) /
        (-(1 / 2 : ℂ) - (ε : ℂ) * Complex.I)) := by
  simp [div_eq_mul_inv, Complex.conj_inv, Complex.conj_ofNat]

/-- The base edge contributes opposite principal arguments from its two
normal sides. No branch-cut assignment is made at the midpoint itself. -/
theorem base_edge_paired_arg_zero {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (ε : ℝ)
    (hdir : q (cyclicSuccessorPerm n i) - q i ≠ 0)
    (hε : ε ≠ 0) :
    Complex.arg ((q (cyclicSuccessorPerm n i) - normalAtEdgeMidpoint q i ε) /
        (q i - normalAtEdgeMidpoint q i ε)) +
      Complex.arg ((q (cyclicSuccessorPerm n i) - normalAtEdgeMidpoint q i (-ε)) /
        (q i - normalAtEdgeMidpoint q i (-ε))) = 0 := by
  rw [base_ratio_normal_eq q i ε hdir,
    base_ratio_normal_eq q i (-ε) hdir,
    half_minus_ratio_conj]
  have harg : Complex.arg
      (((1 / 2 : ℂ) - (ε : ℂ) * Complex.I) /
        (-(1 / 2 : ℂ) - (ε : ℂ) * Complex.I)) ≠ Real.pi := by
    intro heq
    exact half_minus_im_ne_zero ε hε (Complex.arg_eq_pi_iff.mp heq).2
  rw [Complex.arg_conj, if_neg harg]
  ring

/-- The literal principal-angle sum over all actual edges except the
selected base edge. This is evaluated at the base midpoint only after
proving that midpoint misses every other actual edge. -/
def nonBaseArgSum {n : ℕ} (q : Fin n → ℂ) (i : Fin n) (z : ℂ) : ℝ :=
  ∑ j ∈ (Finset.univ.erase i),
    Complex.arg ((q (cyclicSuccessorPerm n j) - z) / (q j - z))

theorem nonBaseArgSum_eq_literal {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (z : ℂ) :
    nonBaseArgSum q i z =
      ∑ j ∈ (Finset.univ.erase i),
        Complex.arg ((q (cyclicSuccessorPerm n j) - z) / (q j - z)) := rfl

theorem edgeArgSum_eq_base_add_nonBase {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (z : ℂ) :
    edgeArgSum q z =
      Complex.arg ((q (cyclicSuccessorPerm n i) - z) / (q i - z)) +
        nonBaseArgSum q i z := by
  unfold edgeArgSum nonBaseArgSum
  exact (Finset.add_sum_erase Finset.univ
    (fun j : Fin n => Complex.arg
      ((q (cyclicSuccessorPerm n j) - z) / (q j - z)))
    (Finset.mem_univ i)).symm

/-- Pairing normal test points cancels the base-edge argument exactly;
only the arguments of actual non-base edges remain. -/
theorem paired_edgeArgSum_eq_nonBase {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (ε : ℝ)
    (hdir : q (cyclicSuccessorPerm n i) - q i ≠ 0)
    (hε : ε ≠ 0) :
    edgeArgSum q (normalAtEdgeMidpoint q i ε) +
      edgeArgSum q (normalAtEdgeMidpoint q i (-ε)) =
    nonBaseArgSum q i (normalAtEdgeMidpoint q i ε) +
      nonBaseArgSum q i (normalAtEdgeMidpoint q i (-ε)) := by
  rw [edgeArgSum_eq_base_add_nonBase q i (normalAtEdgeMidpoint q i ε),
    edgeArgSum_eq_base_add_nonBase q i (normalAtEdgeMidpoint q i (-ε))]
  have hbase := base_edge_paired_arg_zero q i ε hdir hε
  linear_combination hbase

private theorem offset_ne_zero_of_not_on_edge {n : ℕ}
    (q : Fin n → ℂ) (z : ℂ) (j : Fin n)
    (hnot : z ∉ edgeTrace q j) : q j - z ≠ 0 := by
  have hz : z ≠ q j := by
    intro heq
    apply hnot
    exact (edgeTrace_iff_literal q j z).mpr
      ⟨0, by norm_num, by norm_num, by simpa using heq⟩
  exact sub_ne_zero.mpr hz.symm

private theorem edge_ratio_slit_of_not_on_edge {n : ℕ}
    (q : Fin n → ℂ) (z : ℂ) (j : Fin n)
    (hnot : z ∉ edgeTrace q j) :
    (q (cyclicSuccessorPerm n j) - z) / (q j - z) ∈ Complex.slitPlane := by
  let v : ℂ := q (cyclicSuccessorPerm n j)
  let a : ℂ := q j - z
  let b : ℂ := v - z
  let w : ℂ := b / a
  have ha : a ≠ 0 := offset_ne_zero_of_not_on_edge q z j hnot
  have hslit : 0 < w.re ∨ w.im ≠ 0 := by
    by_contra hbad
    push_neg at hbad
    let r : ℝ := w.re
    have hr : r ≤ 0 := hbad.1
    have hw : w = (r : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa [r] using hbad.2
    have hb : b = (r : ℂ) * a := by
      calc
        b = (b / a) * a := (div_mul_cancel₀ b ha).symm
        _ = (r : ℂ) * a := by change w * a = _; rw [hw]
    have hden : 0 < 1 - r := by linarith
    have hdenC : ((1 - r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hden)
    let t : ℝ := 1 / (1 - r)
    have ht0 : 0 ≤ t := le_of_lt (div_pos (by norm_num) hden)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact (div_le_iff₀ hden).2 (by linarith)
    have hz : z = q j + (t : ℂ) * (v - q j) := by
      apply mul_left_cancel₀ hdenC
      calc
        ((1 - r : ℝ) : ℂ) * z = v - (r : ℂ) * q j := by
          dsimp [a,b] at hb
          push_cast
          linear_combination -hb
        _ = ((1 - r : ℝ) : ℂ) *
              (q j + (t : ℂ) * (v - q j)) := by
          have htC : (t : ℂ) = 1 / ((1 - r : ℝ) : ℂ) := by
            simp only [t, Complex.ofReal_div, Complex.ofReal_one]
          have hdenC' : (1 : ℂ) - (r : ℂ) ≠ 0 := by
            simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hdenC
          rw [htC]
          field_simp [hdenC']
          ring
    exact hnot ((edgeTrace_iff_literal q j z).mpr ⟨t, ht0, ht1, hz⟩)
  exact Complex.mem_slitPlane_iff.mpr hslit

/-- All non-base argument terms remain continuous at a point that misses
their literal closed edges, even when that point lies on the base edge. -/
theorem nonBaseArgSum_continuousAt {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (z : ℂ)
    (hnot : ∀ j : Fin n, j ≠ i → z ∉ edgeTrace q j) :
    ContinuousAt (nonBaseArgSum q i) z := by
  have hterm (j : Fin n) (hji : j ≠ i) : ContinuousAt
      (fun ζ : ℂ => Complex.arg
        ((q (cyclicSuccessorPerm n j) - ζ) / (q j - ζ))) z := by
    have hr : ContinuousAt
        (fun ζ : ℂ => (q (cyclicSuccessorPerm n j) - ζ) / (q j - ζ)) z :=
      (continuousAt_const.sub continuousAt_id).div
        (continuousAt_const.sub continuousAt_id)
        (offset_ne_zero_of_not_on_edge q z j (hnot j hji))
    exact ContinuousAt.comp
      (f := fun ζ : ℂ => (q (cyclicSuccessorPerm n j) - ζ) / (q j - ζ))
      (x := z)
      (Complex.continuousAt_arg
        (edge_ratio_slit_of_not_on_edge q z j (hnot j hji))) hr
  have hs (s : Finset (Fin n)) (hsi : i ∉ s) : ContinuousAt
      (fun ζ : ℂ => ∑ j ∈ s,
        Complex.arg ((q (cyclicSuccessorPerm n j) - ζ) / (q j - ζ))) z := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) z)
    | @insert j s hjs ih =>
        have hji : j ≠ i := by
          intro h
          apply hsi
          simp [h]
        have hsi' : i ∉ s := by
          intro h
          apply hsi
          simp [h]
        simpa only [Finset.sum_insert hjs] using (hterm j hji).add (ih hsi')
  exact hs (Finset.univ.erase i) (Finset.not_mem_erase i Finset.univ)

/-- The actual selected base arc has a nonzero geometric direction. -/
theorem actualComponentWord_base_dir_ne_zero {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    q (cyclicSuccessorPerm m i₀) - q i₀ ≠ 0 := by
  intro e m q i₀
  have hsource : q i₀ = Complex.equivRealProd.symm
      (D.vertexPoint (D.arcSource e)) := by
    simpa only [q, i₀] using actualComponentWord_zero T C
  have htarget : q (cyclicSuccessorPerm m i₀) =
      Complex.equivRealProd.symm (D.vertexPoint (D.arcTarget e)) := by
    simpa only [q, m, e] using actualComponentWord_successor T C i₀
  rw [htarget, hsource]
  apply sub_ne_zero.mpr
  intro h
  exact D.arc_endpoints_distinct e
    (D.vertexPoint_injective (Complex.equivRealProd.symm.injective h.symm))

/-- The sum of the two actual off-trace region indices equals the
non-base principal-angle sum at the base midpoint. The base edge is
handled by exact pairing before taking the limit; its undefined
midpoint argument is never evaluated. -/
theorem actual_side_index_sum_eq_nonBase_midpoint {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    let pair := actualBaseSideIndexPair T C
    (((pair.1 + pair.2 : ℤ) : ℝ) * (2 * Real.pi)) =
      2 * nonBaseArgSum q i₀ (normalAtEdgeMidpoint q i₀ 0) := by
  intro e m q i₀ pair
  obtain ⟨δ, hδ, hspec⟩ := (actualBaseSideIndexPair_characterization T C).1
  have hdir : q (cyclicSuccessorPerm m i₀) - q i₀ ≠ 0 :=
    actualComponentWord_base_dir_ne_zero T C
  have hnot : ∀ j : Fin m, j ≠ i₀ →
      normalAtEdgeMidpoint q i₀ 0 ∉ edgeTrace q j :=
    actualComponentWord_base_midpoint_regular T C
  let f : ℝ → ℝ := fun ε => nonBaseArgSum q i₀ (normalAtEdgeMidpoint q i₀ ε)
  have hnormal : ContinuousAt (normalAtEdgeMidpoint q i₀) (0 : ℝ) := by
    unfold normalAtEdgeMidpoint
    fun_prop
  have hf : ContinuousAt f (0 : ℝ) :=
    (nonBaseArgSum_continuousAt q i₀ _ hnot).comp hnormal
  have hneg : ContinuousAt (fun ε : ℝ => -ε) 0 := by fun_prop
  have hfneg : ContinuousAt (fun ε : ℝ => f (-ε)) 0 := by
    exact ContinuousAt.comp' (f := fun ε : ℝ => -ε) (g := f)
      (by simpa only [neg_zero] using hf) hneg
  have hpair : ContinuousAt (fun ε : ℝ => f ε + f (-ε)) 0 := hf.add hfneg
  have hpoint (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) δ) :
      f ε + f (-ε) =
        (((pair.1 + pair.2 : ℤ) : ℝ) * (2 * Real.pi)) := by
    obtain ⟨hp, hkp⟩ := hspec.1 ε hε
    have hεneg : -ε ∈ Set.Ioo (-δ) (0 : ℝ) := by
      constructor <;> linarith [hε.1, hε.2]
    obtain ⟨hn, hkn⟩ := hspec.2 (-ε) hεneg
    have hsum := paired_edgeArgSum_eq_nonBase q i₀ ε hdir (ne_of_gt hε.1)
    rw [edgeArgSum_eq_windingIndex q (normalAtEdgeMidpoint q i₀ ε) hp,
      edgeArgSum_eq_windingIndex q (normalAtEdgeMidpoint q i₀ (-ε)) hn,
      hkp, hkn] at hsum
    dsimp [f]
    rw [Int.cast_add]
    linear_combination -hsum
  have hevent : (fun ε : ℝ => f ε + f (-ε)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => (((pair.1 + pair.2 : ℤ) : ℝ) * (2 * Real.pi))) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact hpoint ε hε
  have hlim : Filter.Tendsto (fun ε : ℝ => f ε + f (-ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (f 0 + f 0)) :=
    by
      simpa only [neg_zero] using hpair.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hconst : Filter.Tendsto
      (fun _ : ℝ => (((pair.1 + pair.2 : ℤ) : ℝ) * (2 * Real.pi)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((pair.1 + pair.2 : ℤ) : ℝ) * (2 * Real.pi))) :=
    tendsto_const_nhds
  have hval := tendsto_nhds_unique_of_eventuallyEq hlim hconst hevent
  dsimp [f] at hval
  simpa only [neg_zero, two_mul] using hval.symm

end DirectGLSSW.HOMFLY.PLWinding
