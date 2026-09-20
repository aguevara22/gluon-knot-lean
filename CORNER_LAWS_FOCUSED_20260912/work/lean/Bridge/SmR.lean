-- Ported 15:19Z 2026-09-14 from work/drafts/hypr/HypR.lean Part 3 (hyp:R architect unit) by the pod executor; body verbatim. LIBRARY: `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` is proved from accepted rows; the fixed-name row Bridge:theorem (`Bridge.sm_R : SM.hyp_R`) is NOT declared — it needs RProof.cv_R (R:cv_theorem), blocked by GAP-2.
-- Header note 2026-09-19 (comment only; no declaration changed; D-AUTH-20260919 G-05, OPEN_ITEMS_20260916.md §E-11): GAP-2 was CLOSED on 2026-09-15 by the author's decision D-GAP2 (axiom SM.lit_homfly_descent, SM/LitHomflyDescent.lean); `Bridge.sm_R` now waits only on `RProof.cv_R` (row 178 R:cv_theorem, a staged one-liner in work/drafts/cvtail/port/R178_183/), which waits on row 177 R:extreme_selected (OPEN_ITEMS_20260916.md §A-15, §A-19, §A-20).
import SM.HypR
import RProof.X1Rows
import Bridge.B4

/-! # Bridge lane: SM Hypothesis R from CV Hypothesis R (consumer check for hyp:R)

The theorem `SM.sm_R_of_cv_R` shows that the accepted `CV.hyp_R` (row CV:ax:R, form R6) together with the accepted bridge B4 yields `SM.hyp_R` (row hyp:R, SM/HypR.lean); `smR_shape_conclusion_is_diagonal` records that RProof/X1Rows.lean's `smR_shape_of_hyp_R` concludes the diagonal form `SM.HypRDiagonal`. Once `RProof.cv_R` is proved, `Bridge.sm_R := SM.sm_R_of_cv_R RProof.cv_R`. -/

namespace SM
/-! ## Part 3 — consumer check against the Bridge lane (intended home: work/lean/Bridge/SmR.lean, the module
of row Bridge:theorem; needs RProof.X1Rows and Bridge.B4) -/

/-- The conclusion of the accepted-lane consistency theorem `RProof.smR_shape_of_hyp_R` IS `HypRDiagonal`
(by `rfl` on the types): hence `CV.hyp_R → B4.pointwise → HypRDiagonal`. -/
theorem smR_shape_conclusion_is_diagonal (hcv : CV.hyp_R)
    (hB4 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P),
      CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP) :
    HypRDiagonal :=
  RProof.smR_shape_of_hyp_R hcv hB4

/-- **`CV.hyp_R → SM.hyp_R` given Bridge:B4 (17)** — the shape of row Bridge:theorem (BRIDGE.md §3
(19)-(21)) with `SM.hyp_R` as its literal conclusion. Same proof as `RProof.smR_shape_of_hyp_R`: name the
germ's triple by increasing representatives (`Bridge.exists_sorted_tripleAt`, B1), its CV event
`Bridge.eventOfTriple` is a simple transversal RIII event (`RProof.isSimpleRIII_eventOfTriple`, B1-B3),
apply `CV.hyp_R` at the two INDEPENDENT side times `g.sideTime true tp > 0`, `g.sideTime false tm < 0`
(BRIDGE.md (20)), and translate `X₁ = C` on both sides by (17) (BRIDGE.md (21)). -/
theorem hyp_R_of_cv_hyp_R (hcv : CV.hyp_R)
    (hB4 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P),
      CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP) :
    hyp_R := by
  intro n _ hn g e f k h tp tm
  obtain ⟨e', f', k', -, hef, hfk, h'⟩ := Bridge.exists_sorted_tripleAt g h
  have hE := RProof.isSimpleRIII_eventOfTriple hn g h' hef hfk
  have hp : 0 < (g.sideTime true tp).val := by
    show 0 < (if (true : Bool) = true then _ else _ : g.Parameter).val
    simp only [ite_true]
    exact tp.2.1
  have hm : (g.sideTime false tm).val < 0 := by
    show (if (false : Bool) = true then _ else _ : g.Parameter).val < 0
    simp only [Bool.false_eq_true, ite_false]
    exact neg_neg_iff_pos.mpr tm.2.1
  have key := hcv n hn (Bridge.eventOfTriple hn g h') e' f' k' _ _ _ _ hE
    (g.sideTime true tp) (g.sideTime false tm) hp hm
  exact (hB4 n hn _ (g.sideTuple true tp).2).symm.trans
    (key.trans (hB4 n hn _ (g.sideTuple false tm).2))

/-- **`CV.hyp_R → SM.hyp_R`**, with Bridge:B4 discharged by the accepted row `Bridge.B4`: the row
Bridge:theorem (`Bridge.sm_R : SM.hyp_R`) is `sm_R_of_cv_R RProof.cv_R` once the R lane's `RProof.cv_R :
CV.hyp_R` (row R:cv_theorem, GAP-2-blocked) exists. -/
theorem sm_R_of_cv_R (hcv : CV.hyp_R) : hyp_R :=
  hyp_R_of_cv_hyp_R hcv Bridge.B4.pointwise

end SM
