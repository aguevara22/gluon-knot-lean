import SM.LocalPolynomial

/-! Ported verbatim 2026-09-13 from work/drafts/SingleCrossingB.lean (prover subagent B of the pod executor; checked with `lake env lean`, no placeholder, axioms propext/Classical.choice/Quot.sound/SM.lp_lm); only this header added and the `#print axioms` line removed. Cross-check draft: work/drafts/SingleCrossingA.lean (independent, in progress at port time). -/

/-! Source lc:single-crossing (reference/SM/sm-3-statesum.tex:1345-1352, frame SM15): a single self crossing
has scalar value one. Main declaration: `SM.single_crossing`.

Notation (namespace `SM.Link`): "an actual oriented one-circle diagram" is a `Diagram` with `D.Γ.c = 1`
(one component circle); "just one self crossing" is `∀ y : D.Γ.Crossing, y = x` for a crossing `x` (the
crossing type is a subsingleton with the inhabitant `x`; on one circle every crossing is a self
crossing); "for either crossing sign" is the absence of any hypothesis on `D.IsPositive x`; "local LM
evaluation `P_D`" is `SM.P` (SM/LocalPolynomial.lean: the element of `R` read off as the coefficientwise
real part of the Gaussian evaluation `φ(F_D)` of the source value of lp:lm; that the imaginary part
vanishes is lp:core's integral descent, recorded in lp:core's bundle, so `P D = 1` is the printed `P_D = 1`); "a crossing-free one-circle diagram" is `D.IsCrossingFreeCircle`. -/

namespace SM

open SM.Link

/-! ## Helpers (draft B): a basing whose basepoint lies immediately before a given occurrence

Printed proof (sm-3:1353-1361): "choose the nonsingular basepoint in the cyclic interval immediately
before the under occurrence of the unique crossing". The general fact is `Diagram.exists_basing_first`:
for every occurrence `v` there is a basing whose basepoint on `v`'s component lies just before `v`, so
that every other occurrence on that component has a strictly larger offset from the basepoint. -/

namespace Link.Diagram

variable (D : Diagram)

/-- On any edge, the parameters whose plane point is a crossing point form a finite set (the edge map is
injective by `regular`, and there are finitely many crossings). -/
theorem finite_crossing_params (i : Fin D.Γ.c) (e : ZMod (D.Γ.comp i).k) :
    {t : ℝ | ∃ x, edgePoint (D.Γ.comp i).P e t = D.Γ.crossingPoint x}.Finite := by
  have hedge : edge (D.Γ.comp i).P e ≠ 0 :=
    ((regular_iff_edges _).mp (D.generic.regular i) e).1
  refine ((Set.finite_range D.Γ.crossingPoint).preimage (edgePoint_injective hedge).injOn).subset ?_
  rintro t ⟨x, hx⟩
  exact ⟨x, hx.symm⟩

/-- On an edge, immediately before a parameter `t₀ > 0`: a parameter `t ∈ [0, t₀)` that lies strictly
above every crossing parameter of the edge below `t₀` (in particular `t` itself is no crossing
parameter). -/
theorem exists_param_before (i : Fin D.Γ.c) (e : ZMod (D.Γ.comp i).k) {t₀ : ℝ} (h₀ : 0 < t₀) :
    ∃ t : ℝ, 0 ≤ t ∧ t < t₀ ∧
      ∀ s, 0 ≤ s → s < t₀ → (∃ x, edgePoint (D.Γ.comp i).P e s = D.Γ.crossingPoint x) → s < t := by
  set A : Set ℝ :=
    insert 0 {s | 0 ≤ s ∧ s < t₀ ∧ ∃ x, edgePoint (D.Γ.comp i).P e s = D.Γ.crossingPoint x} with hA
  have hfin : A.Finite :=
    Set.Finite.insert 0 ((D.finite_crossing_params i e).subset (fun s hs => hs.2.2))
  have hne : A.Nonempty := ⟨0, Set.mem_insert 0 _⟩
  obtain ⟨m, hmA, hm⟩ := Set.exists_max_image A id hfin hne
  have hm0 : (0 : ℝ) ≤ m := hm 0 (Set.mem_insert 0 _)
  have hmt : m < t₀ := by
    rcases hmA with h | ⟨-, h, -⟩
    · rw [h]; exact h₀
    · exact h
  refine ⟨(m + t₀) / 2, by linarith, by linarith, fun s hs0 hs1 hsx => ?_⟩
  have hs : s ≤ m := hm s (Set.mem_insert_of_mem 0 ⟨hs0, hs1, hsx⟩)
  linarith

/-- The basing with the identity component order, the given nonsingular basepoint `b` on component
`i`, and chosen nonsingular basepoints on the other components. -/
noncomputable def basingAt (i : Fin D.Γ.c) (b : TraversalPoint (D.Γ.comp i).k)
    (hb : ∀ x, D.Γ.eval ⟨i, b⟩ ≠ D.Γ.crossingPoint x) : D.Basing where
  rank := Equiv.refl _
  base := Function.update (fun j => Classical.choose (D.exists_nonsingular_base j)) i b
  nonsingular := by
    intro j x
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact hb x
    · rw [Function.update_of_ne hj]
      exact Classical.choose_spec (D.exists_nonsingular_base j) x

theorem basingAt_base (i : Fin D.Γ.c) (b : TraversalPoint (D.Γ.comp i).k)
    (hb : ∀ x, D.Γ.eval ⟨i, b⟩ ≠ D.Γ.crossingPoint x) : (D.basingAt i b hb).base i = b := by
  simp only [basingAt, Function.update_self]

/-- Reusable: for every occurrence `v` there is a basing whose basepoint on `v`'s component lies
immediately before `v` — every other occurrence `w` on that component has a strictly larger offset
from the basepoint than `v` (so `v` is the first occurrence met on its component). -/
theorem exists_basing_first (v : D.Γ.Visit) :
    ∃ B : D.Basing, ∀ w : D.Γ.Visit, (D.visitPt w).1 = (D.visitPt v).1 → w ≠ v →
      (D.basedRank B v).2 < (D.basedRank B w).2 := by
  have hpos := D.visitPt_param_pos v
  rcases hpv : D.visitPt v with ⟨i, pv⟩
  rw [hpv] at hpos
  dsimp only at hpos
  -- the basepoint parameter `tb`: just before `pv` on its edge, above every crossing parameter below
  obtain ⟨tb, htb0, htb1, htb⟩ := D.exists_param_before i pv.1 hpos
  have htb1' : tb < 1 := htb1.trans pv.2.2.2
  obtain ⟨b, hb⟩ : ∃ b : TraversalPoint (D.Γ.comp i).k, b = (pv.1, ⟨tb, htb0, htb1'⟩) := ⟨_, rfl⟩
  have hevb : D.Γ.eval ⟨i, b⟩ = edgePoint (D.Γ.comp i).P pv.1 tb := by rw [hb]; rfl
  have hbns : ∀ x, D.Γ.eval ⟨i, b⟩ ≠ D.Γ.crossingPoint x := by
    intro x hx
    rw [hevb] at hx
    exact lt_irrefl tb (htb tb htb0 htb1 ⟨x, hx⟩)
  refine ⟨D.basingAt i b hbns, fun w hw hwv => ?_⟩
  have hevw := D.eval_visitPt w
  rcases hpw : D.visitPt w with ⟨j, pw⟩
  rw [hpw] at hw hevw
  dsimp only at hw
  subst hw
  simp only [Diagram.basedRank]
  rw [hpv, hpw]
  simp only [basingAt_base]
  -- keys
  have hb1 : b.1 = pv.1 := by rw [hb]
  have hb2 : b.2.val = tb := by rw [hb]
  have hkb : traversalKey b = (pv.1.val : ℝ) + tb := by rw [hb]; rfl
  have hkv : traversalKey pv = (pv.1.val : ℝ) + pv.2.val := rfl
  have hkw : traversalKey pw = (pw.1.val : ℝ) + pw.2.val := rfl
  have hbv : traversalKey b < traversalKey pv := by
    rw [hkb, hkv]; linarith
  rw [cyclicOffset_of_le _ hbv.le]
  rcases lt_or_ge (traversalKey pw) (traversalKey b) with h | h
  · -- `w` lies before the basepoint: its offset wraps around the whole circle
    rw [cyclicOffset_of_lt _ h]
    have h1 := traversalKey_lt_card pv
    have h2 := traversalKey_nonneg pw
    linarith
  · -- `w` lies after the basepoint: it cannot lie in `[b, v)`, so it lies after `v`
    rw [cyclicOffset_of_le _ h]
    have hne : traversalKey pw ≠ traversalKey pv := by
      intro heq
      have heq' := traversalKey_injective heq
      apply hwv
      apply D.visitPt_injective
      rw [hpw, hpv, heq']
    have hlt : traversalKey pv < traversalKey pw := by
      rcases lt_or_lt_iff_ne.mpr hne with hlt | hlt
      · exfalso
        have h' := not_lt.mpr h
        rw [traversalKey_lt_iff] at hlt h'
        push Not at h'
        rw [hb1, hb2] at h'
        rcases hlt with h1 | ⟨h1, h2⟩
        · exact absurd h1 (not_lt.mpr h'.1)
        · have h3 : tb ≤ pw.2.val := h'.2 h1
          have hevw' : edgePoint (D.Γ.comp _).P pv.1 pw.2.val = D.Γ.crossingPoint w.1 := by
            rw [← h1]; exact hevw
          have h4 : pw.2.val < tb := htb pw.2.val pw.2.2.1 h2 ⟨w.1, hevw'⟩
          linarith
      · exact hlt
    linarith

end Link.Diagram

/-- lc:single-crossing as printed. -/
structure SingleCrossingData : Prop where
  /-- "An actual oriented one-circle diagram with just one self crossing has local LM evaluation
  `P_D = 1`, for either crossing sign." -/
  one_crossing : ∀ (D : Diagram) (x : D.Γ.Crossing), D.Γ.c = 1 → (∀ y : D.Γ.Crossing, y = x) → P D = 1
  /-- "A crossing-free one-circle diagram also has value one." -/
  crossing_free : ∀ D : Diagram, D.IsCrossingFreeCircle → P D = 1

theorem single_crossing : SingleCrossingData := by
  refine ⟨?_, ?_⟩
  · intro D x hc hx
    -- basepoint immediately before the under occurrence of the unique crossing
    obtain ⟨B, hB⟩ := D.exists_basing_first (D.underVisit x)
    -- with one component every component index is the same
    have hfin : ∀ i j : Fin D.Γ.c, i = j := by
      intro i j
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    have hUF : D.UnderFirst B := by
      intro y
      rw [hx y, Prod.lex_def]
      right
      refine ⟨?_, ?_⟩
      · simp only [Diagram.basedRank_fst]
        rw [hfin (D.visitPt (D.underVisit x)).1 (D.visitPt (D.overVisit x)).1]
      · exact hB (D.overVisit x) (hfin _ _) (D.overVisit_ne_underVisit x)
    apply P_eq_one_of_lmF_eq_one
    rw [lmF_underFirst_init B hUF]
    have hc' : D.componentCount - 1 = 0 := by
      show D.Γ.c - 1 = 0
      omega
    rw [hc', pow_zero]
  · intro D h
    exact P_eq_one_of_lmF_eq_one (lmF_unknot h)

end SM
