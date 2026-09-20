-- Ported 08:06Z 2026-09-19 from work/drafts/moves/W3D_Assembled.lean lines 7837-21748 (row 177 (6) and the
-- realisers: units E/G/H (`w3g_`, `w3h_`, `w3bg_`, `w3bh_`), REAL (`w3bi_`: `w3bi_switch_riii`, the site data β1′, the wall
-- data β2, `w3bi_hrec_general`), SPLITA (`w3ca_`), SPLITC (`w3cc_`), BIGON (`w3cz_`), SITE (`w3cs_`), SPLITB (`w3cb_`),
-- NONKINK (`w3dk_`: the flat subdivision and the value form of the site data), KNOT (`w3ck_`: the record-clause chain),
-- RESPAR (`w3dp_`: the parity clause), RESID (`w3di_`: the identification clause), the assembler's `w3cx_` (the sign table,
-- the OUTER residue) and the terminal `w3ck_extreme_selected : RowShape @ExtremeSelectedData`) by the pod executor (files
-- prepared by the pod executor (files prepared by the row-177 wave-3d assembler), W3D_ASSEMBLY_REPORT.md).  Body verbatim except this header, the import block
-- and the opening `namespace SM.Link / open SM / noncomputable section` (the assembled file's lines 1-7836 are
-- RProof/GenericTransportSw.lean).  No placeholder; no unproved declaration; no interface Prop asserted.
-- Axioms of `w3ck_extreme_selected`: propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent,
-- SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact (W3D_AXIOMS.log; the registered nine, no placeholder axiom).
import RProof.GenericTransportSw
import RProof.ExtremeTransportUnits
import SM.CBProducts
import CV.SingletonDi
import SM.ZeroRotationSeed

/-! # Row 177 (R:extreme_selected): the units and the row in the fixed shape

Everything below is the row-177 material of `work/drafts/moves/W3D_Assembled.lean` from its `## 5` header on, verbatim
(prefixes by unit: `w3g_`/`w3h_`/`w3bg_`/`w3bh_` the `j = 2` bigon sites and the reduced-smoothed-record lemma, `w3bi_` the
realisers and the site/wall data, `w3ca_` SPLITA, `w3cc_` SPLITC, `w3cz_` BIGON, `w3cs_` SITE, `w3cb_` SPLITB, `w3dk_`
NONKINK, `w3ck_` KNOT, `w3dp_` RESPAR, `w3di_` RESID, `w3cx_` the assembler).  The terminal theorem is
`w3ck_extreme_selected : RowShape @ExtremeSelectedData`, instantiated as `RProof.extreme_selected` in
RProof/ExtremeSelected.lean.  The switched G11 core it consumes is RProof/GenericTransportSw.lean. -/

namespace SM.Link

open SM

noncomputable section

/-! ## 5. Row 177 (6): the two `j = 2` bigon sites on smoothing outputs and the reduced-smoothed-record
lemma (statements with proof sketches; PLAN_FINAL §4.4 (6), §5 Wave 3 "I-177b") -/

section Row177_6

open Smoothing

/-! ### Unit G (`w3bg_`): the corrected `j = 2` bigon sites on smoothing outputs.  The frozen statements
`w3g_bigonData_smooth_arcST/TS` are FALSE as stated (rule 3): `BigonData.hk : j + 3 ≤ k` needs `5 ≤ k` on the
component carrying the cut-start strand, and in the self model that component has only `4` strands when the
smoothed crossing is a kink (`t = s ∓ 2` on one component, one old strand between the two cut points).  The corrected
forms `w3bg_bigonData_smooth_arcST_of_five` / `_arcTS_of_five` add exactly that hypothesis and are PROVED; the
frozen sub-leaves are reduced to it (their remaining obligation is the hypothesis `hk5` alone).  Tools: the affine
determinant `det v (· − p)`, the half-plane / segment-union convexity lemmas and the line lemma
`w3bg_line_convexHull` (a line through two generators of a convex hull whose other generators lie strictly on one
side meets the hull only in the segment between them). -/

/-- (G) `det v (· − p)` is affine along a segment. -/
theorem w3bg_det_affine (v p q₁ q₂ : Plane) {a b : ℝ} (hab : a + b = 1) :
    det v (a • q₁ + b • q₂ - p) = a * det v (q₁ - p) + b * det v (q₂ - p) := by
  have hp : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
  conv_lhs => rw [hp]
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul]
  ring

/-- (G) a closed half-plane `{q | 0 ≤ det v (q − p) * c}` is convex. -/
theorem w3bg_convex_halfPlane (v p : Plane) (c : ℝ) : Convex ℝ {q : Plane | 0 ≤ det v (q - p) * c} := by
  intro q₁ h₁ q₂ h₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at h₁ h₂ ⊢
  rw [w3bg_det_affine v p q₁ q₂ hab, add_mul, mul_assoc, mul_assoc]
  exact add_nonneg (mul_nonneg ha h₁) (mul_nonneg hb h₂)

/-- (G) the convex hull of four points lies in a closed half-plane containing them. -/
theorem w3bg_convexHull_subset_halfPlane (v p : Plane) (c : ℝ) (a b c' d : Plane)
    (ha : 0 ≤ det v (a - p) * c) (hb : 0 ≤ det v (b - p) * c) (hc : 0 ≤ det v (c' - p) * c)
    (hd : 0 ≤ det v (d - p) * c) :
    convexHull ℝ {a, b, c', d} ⊆ {q : Plane | 0 ≤ det v (q - p) * c} := by
  apply convexHull_min _ (w3bg_convex_halfPlane v p c)
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> assumption

/-- (G) a segment on the line `det v (· − p) = 0` together with an open half-plane of that line is convex. -/
theorem w3bg_convex_segment_union_open (v p a b : Plane) (c : ℝ) (ha : det v (a - p) = 0)
    (hb : det v (b - p) = 0) :
    Convex ℝ (segment ℝ a b ∪ {q : Plane | 0 < det v (q - p) * c}) := by
  have key : ∀ q ∈ segment ℝ a b, det v (q - p) = 0 := by
    rintro q ⟨γ, δ, hγ, hδ, hγδ, rfl⟩
    rw [w3bg_det_affine v p a b hγδ, ha, hb]; ring
  intro q₁ h₁ q₂ h₂ α β hα hβ hαβ
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (convex_segment a b h₁ h₂ hα hβ hαβ)
  · rcases hβ.lt_or_eq with hβ' | hβ'
    · right
      show 0 < det v (α • q₁ + β • q₂ - p) * c
      rw [w3bg_det_affine v p _ _ hαβ, key _ h₁, mul_zero, zero_add, mul_assoc]
      exact mul_pos hβ' h₂
    · left
      rw [← hβ', add_zero] at hαβ
      rw [← hβ', zero_smul, add_zero, hαβ, one_smul]
      exact h₁
  · rcases hα.lt_or_eq with hα' | hα'
    · right
      show 0 < det v (α • q₁ + β • q₂ - p) * c
      rw [w3bg_det_affine v p _ _ hαβ, key _ h₂, mul_zero, add_zero, mul_assoc]
      exact mul_pos hα' h₁
    · left
      rw [← hα', zero_add] at hαβ
      rw [← hα', zero_smul, zero_add, hαβ, one_smul]
      exact h₂
  · right
    show 0 < det v (α • q₁ + β • q₂ - p) * c
    rw [w3bg_det_affine v p _ _ hαβ, add_mul, mul_assoc, mul_assoc]
    rcases hα.lt_or_eq with hα' | hα'
    · exact add_pos_of_pos_of_nonneg (mul_pos hα' h₁) (mul_nonneg hβ h₂.le)
    · rw [← hα', zero_add] at hαβ
      rw [← hα', zero_mul, zero_add, hαβ, one_mul]
      exact h₂

/-- (G) **the line lemma**: if `a, b` lie on the line `det v (· − p) = 0` and `c, d` lie strictly on one
side of it (`0 < det v (· − p) * k`), the line meets `conv{a, b, c, d}` only in the segment `[a, b]`. -/
theorem w3bg_line_convexHull_four {v p a b c d q : Plane} {k : ℝ} (ha : det v (a - p) = 0)
    (hb : det v (b - p) = 0) (hc : 0 < det v (c - p) * k) (hd : 0 < det v (d - p) * k)
    (hq : det v (q - p) = 0) (hK : q ∈ convexHull ℝ {a, b, c, d}) : q ∈ segment ℝ a b := by
  have hsub : convexHull ℝ {a, b, c, d} ⊆ segment ℝ a b ∪ {q : Plane | 0 < det v (q - p) * k} := by
    apply convexHull_min _ (w3bg_convex_segment_union_open v p a b k ha hb)
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inr hc
    · exact Or.inr hd
  rcases hsub hK with h | h
  · exact h
  · exfalso
    have h' : 0 < det v (q - p) * k := h
    rw [hq, zero_mul] at h'
    exact lt_irrefl _ h'

/-- (G) the strand of `Γ₀` following the strand of an occurring kind carries the successor kind. -/
theorem w3bg_strandOf_succ {D : Diagram} {x : D.Γ.Crossing} {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (κ : StrandKind D x) (hκ : κ.Occurs) (hκ' : κ.succ.Occurs) :
    (⟨(M.strandOf κ hκ).1, (M.strandOf κ hκ).2 + 1⟩ : Γ₀.Strand) = M.strandOf κ.succ hκ' := by
  apply M.kind_injective
  rw [M.kind_succ, M.kind_strandOf, M.kind_strandOf]

/-- (G) `det` is linear in its second argument (scalars). -/
theorem w3bg_det_smul_right (u v : Plane) (c : ℝ) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
theorem w3bg_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring
theorem w3bg_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring
theorem w3bg_det_neg_right (u v : Plane) : det u (-v) = - det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
theorem w3bg_det_comm (u v : Plane) : det u v = - det v u := by simp only [det]; ring

/-- (G) the convex hull of a set in a closed half-plane lies in that half-plane. -/
theorem w3bg_convexHull_subset_halfPlane' (v p : Plane) (c : ℝ) (S : Set Plane)
    (hS : ∀ z ∈ S, 0 ≤ det v (z - p) * c) : convexHull ℝ S ⊆ {q : Plane | 0 ≤ det v (q - p) * c} :=
  convexHull_min hS (w3bg_convex_halfPlane v p c)

/-- (G) **the line lemma, general form**: if every generator of `S` lies on the segment `[a, b]` of the line
`det v (· − p) = 0` or strictly on one side of it, the line meets `conv S` only in `[a, b]`. -/
theorem w3bg_line_convexHull {v p a b q : Plane} {k : ℝ} (ha : det v (a - p) = 0) (hb : det v (b - p) = 0)
    (S : Set Plane) (hS : ∀ z ∈ S, z ∈ segment ℝ a b ∨ 0 < det v (z - p) * k)
    (hq : det v (q - p) = 0) (hK : q ∈ convexHull ℝ S) : q ∈ segment ℝ a b := by
  have hsub : convexHull ℝ S ⊆ segment ℝ a b ∪ {q : Plane | 0 < det v (q - p) * k} :=
    convexHull_min hS (w3bg_convex_segment_union_open v p a b k ha hb)
  rcases hsub hK with h | h
  · exact h
  · exfalso
    have h' : 0 < det v (q - p) * k := h
    rw [hq, zero_mul] at h'
    exact lt_irrefl _ h'

/-- (G) `liftStrand` on `s` before the cut is the `cutStartS` strand. -/
theorem w3bg_liftStrand_s (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (hs : sS D x ∈ y.val) (h : D.crossingParam y hs < τs D x) :
    liftStrand D x M y (sS D x) hs = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS := by
  unfold liftStrand
  rw [dif_pos rfl, if_pos h]

/-- (G) `liftStrand` on `s` after the cut is the `cutEndS` strand. -/
theorem w3bg_liftStrand_s' (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (hs : sS D x ∈ y.val) (h : τs D x ≤ D.crossingParam y hs) :
    liftStrand D x M y (sS D x) hs = M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS := by
  unfold liftStrand
  rw [dif_pos rfl, if_neg (not_lt.mpr h)]

/-- (G) `liftStrand` on `t` before the cut is the `cutStartT` strand. -/
theorem w3bg_liftStrand_t (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (ht : tS D x ∈ y.val) (h : D.crossingParam y ht < τt D x) :
    liftStrand D x M y (tS D x) ht = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT := by
  unfold liftStrand
  rw [dif_neg (sS_ne_tS D x).symm, dif_pos rfl, if_pos h]

/-- (G) `liftStrand` on `t` after the cut is the `cutEndT` strand. -/
theorem w3bg_liftStrand_t' (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (ht : tS D x ∈ y.val) (h : τt D x ≤ D.crossingParam y ht) :
    liftStrand D x M y (tS D x) ht = M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT := by
  unfold liftStrand
  rw [dif_neg (sS_ne_tS D x).symm, dif_pos rfl, if_neg (not_lt.mpr h)]

/-- (G) `liftStrand` on a third strand is the old strand. -/
theorem w3bg_liftStrand_old (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (g : D.Γ.Strand) (hg : g ∈ y.val) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x) :
    liftStrand D x M y g hg = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) := by
  unfold liftStrand
  rw [dif_neg hgs, dif_neg hgt]

/-- (G) the strands of the lift of a crossing `y = {e, f}` are the lifts of `e` and `f`. -/
theorem w3bg_val_liftCrossing (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε) (y : D.Γ.Crossing) (hyx : y ≠ x)
    (e f : D.Γ.Strand) (hef : e ≠ f) (hy : y.val = {e, f}) (he : e ∈ y.val) (hf : f ∈ y.val) :
    (liftCrossing D x M hε y hyx).val = {liftStrand D x M y e he, liftStrand D x M y f hf} := by
  have key : ∀ (e' : D.Γ.Strand) (he' : e' ∈ y.val) (e'' : D.Γ.Strand) (he'' : e'' ∈ y.val), e' = e'' →
      liftStrand D x M y e' he' = liftStrand D x M y e'' he'' := by
    rintro e' he' e'' he'' rfl; rfl
  show ({liftStrand D x M y y.fst y.fst_mem, liftStrand D x M y y.snd y.snd_mem} : Finset Γ₀.Strand) = _
  have h1 := y.fst_mem
  have h2 := y.snd_mem
  rw [hy] at h1 h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  have hne : y.snd ≠ y.fst := D.Γ.other_ne y y.fst_mem
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h2.trans h1.symm) hne
  · rw [key _ _ e he h1, key _ _ f hf h2]
  · rw [key _ _ f hf h1, key _ _ e he h2, Finset.pair_comm]
  · exact absurd (h2.trans h1.symm) hne

/-- **(G) the corrected `arcST` site (rule 3): `w3g_bigonData_smooth_arcST` with the missing hypothesis
`hk5 : 5 ≤ k` on the component of `cutStartS`.**  Without it the statement is FALSE: in the self model with
`t = s − 2` on one component (a kink at `x`; `dd = kI − 2`) the component `B` carrying `cutStartS`, `arcST`,
`cutEndT` has `kI − dd + 2 = 4` strands, and `BigonData.hk : j + 3 ≤ k` needs `5` for `j = 2`; every other
hypothesis of the frozen statement is satisfiable there.  Everything else is proved: labels by `kind_succ`,
`hy/hz` by `liftCrossing`, `run_free` by `kind_ne_arc_of_mem`, `no_io` by `origCrossing_ne`, `same_over` by
`orig_overStrand₀`/`toDiagram_underStrand_orig` and the switch at `y₀`, `in_iff/out_iff/s_iff` by the line
lemma `w3bg_line_convexHull` (the strict sides come from the orientation `hys, hzt` and, for `s_iff`, from
the clearance `r₁`), `clear` by the half-planes `det es/et (· − p) · det es et ≥ 0` and `K ⊆ Δ`. -/
theorem w3bg_bigonData_smooth_arcST_of_five (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hk5 : 5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- the four strands
  obtain ⟨uIn, huIn⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS :=
    ⟨_, rfl⟩
  obtain ⟨uArc, huArc⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.arcST StrandKind.occurs_arcST := ⟨_, rfl⟩
  obtain ⟨uOut, huOut⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT :=
    ⟨_, rfl⟩
  obtain ⟨uG, huG⟩ : ∃ u : Γ₀.Strand, u = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) :=
    ⟨_, rfl⟩
  rw [← huIn] at hk5
  have hkIn : M.kind uIn = StrandKind.cutStartS := by rw [huIn, M.kind_strandOf]
  have hkArc : M.kind uArc = StrandKind.arcST := by rw [huArc, M.kind_strandOf]
  have hkOut : M.kind uOut = StrandKind.cutEndT := by rw [huOut, M.kind_strandOf]
  have hkG : M.kind uG = StrandKind.old g := by rw [huG, M.kind_strandOf]
  -- labels
  have hArc : (⟨uIn.1, uIn.2 + 1⟩ : Γ₀.Strand) = uArc := by
    apply M.kind_injective
    rw [M.kind_succ, hkIn, hkArc]
    rfl
  have hOut : (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) = uOut := by
    apply M.kind_injective
    have h2 : uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = (uIn.2 + 1) + 1 := by push_cast; ring
    rw [h2]
    have h3 : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1⟩).succ := M.kind_succ ⟨uIn.1, uIn.2 + 1⟩
    rw [h3, hArc, hkArc, hkOut]
    rfl
  -- the crossings and their lifts
  have hyx : y ≠ x := by rw [← hy₀]; exact origCrossing_ne D x M hε y₀
  have hzx : z ≠ x := by rw [← hz₀]; exact origCrossing_ne D x M hε z₀
  have hgy : g ∈ y.val := by rw [hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hgz : g ∈ z.val := by rw [hz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hlift_y : liftCrossing D x M hε y hyx = y₀ := by
    have key : ∀ (y'' : D.Γ.Crossing) (h : y'' ≠ x), y'' = y →
        liftCrossing D x M hε y'' h = liftCrossing D x M hε y hyx := by
      rintro y'' h rfl; rfl
    exact (key _ _ hy₀).symm.trans (liftCrossing_origCrossing D x M hε y₀)
  have hlift_z : liftCrossing D x M hε z hzx = z₀ := by
    have key : ∀ (z'' : D.Γ.Crossing) (h : z'' ≠ x), z'' = z →
        liftCrossing D x M hε z'' h = liftCrossing D x M hε z hzx := by
      rintro z'' h rfl; rfl
    exact (key _ _ hz₀).symm.trans (liftCrossing_origCrossing D x M hε z₀)
  have hyv : y₀.val = {uIn, uG} := by
    rw [← hlift_y, w3bg_val_liftCrossing D x M hε y hyx (sS D x) g hgs.symm hy hsy hgy,
      w3bg_liftStrand_s D x M y hsy hys, w3bg_liftStrand_old D x M y g hgy hgs hgt, huIn, huG]
  have hzv : z₀.val = {uOut, uG} := by
    rw [← hlift_z, w3bg_val_liftCrossing D x M hε z hzx (tS D x) g hgt.symm hz htz hgz,
      w3bg_liftStrand_t' D x M z htz hzt.le, w3bg_liftStrand_old D x M z g hgz hgs hgt, huOut, huG]
  have huIn_y : uIn ∈ y₀.val := by rw [hyv]; exact Finset.mem_insert_self _ _
  have huG_y : uG ∈ y₀.val := by rw [hyv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have huOut_z : uOut ∈ z₀.val := by rw [hzv]; exact Finset.mem_insert_self _ _
  have huG_z : uG ∈ z₀.val := by rw [hzv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hyz₀ : z₀ ≠ y₀ := by
    intro h
    have h1 : z = y := by rw [← hz₀, ← hy₀, h]
    have h2 : sS D x ∈ z.val := by rw [h1]; exact hsy
    rw [hz] at h2
    rcases Finset.mem_insert.mp h2 with h3 | h3
    · exact sS_ne_tS D x h3
    · exact hgs (Finset.mem_singleton.mp h3).symm
  -- points and parameters in `D`
  have hpy : Γ₀.crossingPoint y₀ = D.Γ.crossingPoint y := by
    rw [crossingPoint_origCrossing D x M hε y₀, hy₀]
  have hpz : Γ₀.crossingPoint z₀ = D.Γ.crossingPoint z := by
    rw [crossingPoint_origCrossing D x M hε z₀, hz₀]
  have hYs : D.Γ.crossingPoint y = D.Γ.edgePt (sS D x) (D.crossingParam y hsy) :=
    (D.crossingParam_spec y hsy).2.2
  have hZt : D.Γ.crossingPoint z = D.Γ.edgePt (tS D x) (D.crossingParam z htz) :=
    (D.crossingParam_spec z htz).2.2
  have hYg : D.Γ.crossingPoint y = D.Γ.edgePt g (D.crossingParam y hgy) := (D.crossingParam_spec y hgy).2.2
  have hZg : D.Γ.crossingPoint z = D.Γ.edgePt g (D.crossingParam z hgz) := (D.crossingParam_spec z hgz).2.2
  have hpt_s : pt D x = D.Γ.edgePt (sS D x) (τs D x) := pt_eq_s D x
  have hpt_t : pt D x = D.Γ.edgePt (tS D x) (τt D x) := pt_eq_t D x
  have hYsub : D.Γ.crossingPoint y - pt D x = (D.crossingParam y hsy - τs D x) • es D x := by
    rw [hYs, hpt_s, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul]
  have hZsub : D.Γ.crossingPoint z - pt D x = (D.crossingParam z htz - τt D x) • et D x := by
    rw [hZt, hpt_t, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul]
  have hsm : sMinus D x ε - pt D x = -(ε • es D x) := by rw [sMinus, sub_sub_cancel_left]
  have htp : tPlus D x ε - pt D x = ε • et D x := by rw [tPlus, add_sub_cancel_left]
  have hsm' : sMinus D x ε = D.Γ.edgePt (sS D x) (τs D x - ε) := sMinus_eq_edgePoint D x ε
  have htp' : tPlus D x ε = D.Γ.edgePt (tS D x) (τt D x + ε) := tPlus_eq_edgePoint D x ε
  have hd : det (es D x) (et D x) ≠ 0 := det_es_et_ne_zero D x
  have hdd : 0 < det (es D x) (et D x) * det (es D x) (et D x) := mul_self_pos.mpr hd
  -- clearance: `y`, `z` are farther from `p` than the cut points
  have hεy : ε < τs D x - D.crossingParam y hsy := by
    have h1 := r₁_le_dist_crossingPoint D x hyx
    rw [hYs, hpt_s, D.Γ.dist_edgePt, abs_of_pos (sub_pos.mpr hys)] at h1
    have hes : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
    exact lt_of_mul_lt_mul_right (hε.mul_es_lt.trans_le h1) hes.le
  have hεz : ε < D.crossingParam z htz - τt D x := by
    have h1 := r₁_le_dist_crossingPoint D x hzx
    rw [hZt, hpt_t, D.Γ.dist_edgePt, abs_sub_comm, abs_of_pos (sub_pos.mpr hzt)] at h1
    have het : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
    exact lt_of_mul_lt_mul_right (hε.mul_et_lt.trans_le h1) het.le
  -- transversality of `g` with `s` at `y` and with `t` at `z`
  have hgs_det : det (D.Γ.dir g) (es D x) ≠ 0 := by
    have hspec := D.Γ.crossing_pair_spec y hgy hsy hgs
    exact D.generic.transverse _ _ hspec.1 hspec.2
  have hgt_det : det (D.Γ.dir g) (et D x) ≠ 0 := by
    have hspec := D.Γ.crossing_pair_spec z hgz htz hgt
    exact D.generic.transverse _ _ hspec.1 hspec.2
  -- edge points of the three local strands of `Γ₀`
  have heIn : ∀ θ : ℝ, Γ₀.edgePt uIn θ = pt D x + (θ * (τs D x - ε) - τs D x) • es D x + (0:ℝ) • et D x := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkIn]; exact u3_cutStartS_pt D x θ
  have heOut : ∀ θ : ℝ, Γ₀.edgePt uOut θ = pt D x + (0:ℝ) • es D x + (ε + θ * (1 - τt D x - ε)) • et D x := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkOut]; exact u3_cutEndT_pt D x θ
  have heG : ∀ θ : ℝ, Γ₀.edgePt uG θ = D.Γ.edgePt g θ := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkG]; rfl
  have hIn1 : Γ₀.edgePt uIn 1 = sMinus D x ε := by rw [heIn, sMinus]; module
  have hOut0 : Γ₀.edgePt uOut 0 = tPlus D x ε := by rw [heOut, tPlus]; module
  have hsw : ∀ (w : Γ₀.Crossing) (u : Γ₀.Strand) (hu : u ∈ w.val),
      Γ₀.edgePt u (((toDiagram D x M hε).switch y₀).crossingParam w hu) = Γ₀.crossingPoint w :=
    fun w u hu => (((toDiagram D x M hε).switch y₀).crossingParam_spec w hu).2.2.symm
  have hEty : Γ₀.edgePt uIn (((toDiagram D x M hε).switch y₀).crossingParam y₀ huIn_y) = D.Γ.crossingPoint y := by
    rw [hsw, hpy]
  have hEtz : Γ₀.edgePt uOut (((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z) = D.Γ.crossingPoint z := by
    rw [hsw, hpz]
  have hEtsy : Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_y) = D.Γ.crossingPoint y := by
    rw [hsw, hpy]
  have hEtsz : Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_z) = D.Γ.crossingPoint z := by
    rw [hsw, hpz]
  have hty1 : ((toDiagram D x M hε).switch y₀).crossingParam y₀ huIn_y ≤ 1 :=
    (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huIn_y).2.1
  have htz0 : 0 ≤ ((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z :=
    (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huOut_z).1
  -- the half-plane data of the line `s`
  have hs_y : det (es D x) (D.Γ.crossingPoint y - pt D x) = 0 := by
    rw [hYsub, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hs_sm : det (es D x) (sMinus D x ε - pt D x) = 0 := by
    rw [hsm, w3bg_det_neg_right, w3bg_det_smul_right, w3bg_det_self, mul_zero, neg_zero]
  have hs_tp : 0 < det (es D x) (tPlus D x ε - pt D x) * det (es D x) (et D x) := by
    rw [htp, w3bg_det_smul_right, mul_assoc]; exact mul_pos hε.pos hdd
  have hs_z : 0 < det (es D x) (D.Γ.crossingPoint z - pt D x) * det (es D x) (et D x) := by
    rw [hZsub, w3bg_det_smul_right, mul_assoc]; exact mul_pos (sub_pos.mpr hzt) hdd
  -- the half-plane data of the line `t`
  have ht_y : 0 < det (et D x) (D.Γ.crossingPoint y - pt D x) * det (es D x) (et D x) := by
    rw [hYsub, w3bg_det_smul_right, w3bg_det_comm (et D x) (es D x)]
    have e : (D.crossingParam y hsy - τs D x) * -det (es D x) (et D x) * det (es D x) (et D x) =
        (τs D x - D.crossingParam y hsy) * (det (es D x) (et D x) * det (es D x) (et D x)) := by ring
    rw [e]; exact mul_pos (sub_pos.mpr hys) hdd
  have ht_sm : 0 < det (et D x) (sMinus D x ε - pt D x) * det (es D x) (et D x) := by
    rw [hsm, w3bg_det_neg_right, w3bg_det_smul_right, w3bg_det_comm (et D x) (es D x)]
    have e : -(ε * -det (es D x) (et D x)) * det (es D x) (et D x) =
        ε * (det (es D x) (et D x) * det (es D x) (et D x)) := by ring
    rw [e]; exact mul_pos hε.pos hdd
  have ht_tp : det (et D x) (tPlus D x ε - pt D x) = 0 := by
    rw [htp, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have ht_z : det (et D x) (D.Γ.crossingPoint z - pt D x) = 0 := by
    rw [hZsub, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  -- the half-plane data of the line `g` (through `y`), sign constant `kg = det eg (p − y)`
  have hg_y : det (D.Γ.dir g) (D.Γ.crossingPoint y - D.Γ.crossingPoint y) = 0 := by
    rw [sub_self]; simp only [det, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero]
  have hg_z : det (D.Γ.dir g) (D.Γ.crossingPoint z - D.Γ.crossingPoint y) = 0 := by
    rw [hZg, hYg, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
      w3bg_det_self, mul_zero]
  have hkg : det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) =
      (τs D x - D.crossingParam y hsy) * det (D.Γ.dir g) (es D x) := by
    rw [← neg_sub, hYsub, w3bg_det_neg_right, w3bg_det_smul_right]; ring
  have hg_sm : 0 < det (D.Γ.dir g) (sMinus D x ε - D.Γ.crossingPoint y) *
      det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) := by
    have e1 : sMinus D x ε - D.Γ.crossingPoint y = (τs D x - D.crossingParam y hsy - ε) • es D x := by
      rw [sMinus, pt_eq_s, hYs, D.Γ.edgePt_eq]; module
    rw [e1, hkg, w3bg_det_smul_right]
    have e2 : (τs D x - D.crossingParam y hsy - ε) * det (D.Γ.dir g) (es D x) *
        ((τs D x - D.crossingParam y hsy) * det (D.Γ.dir g) (es D x)) =
        ((τs D x - D.crossingParam y hsy - ε) * (τs D x - D.crossingParam y hsy)) *
          (det (D.Γ.dir g) (es D x) * det (D.Γ.dir g) (es D x)) := by ring
    rw [e2]
    exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hys)) (mul_self_pos.mpr hgs_det)
  have hg_tp : 0 < det (D.Γ.dir g) (tPlus D x ε - D.Γ.crossingPoint y) *
      det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) := by
    have e3 : tPlus D x ε - D.Γ.crossingPoint y = ε • et D x + (pt D x - D.Γ.crossingPoint y) := by
      rw [tPlus]; abel
    have e4 : D.Γ.crossingPoint z - D.Γ.crossingPoint y =
        (D.crossingParam z htz - τt D x) • et D x + (pt D x - D.Γ.crossingPoint y) := by
      rw [← hZsub]; abel
    have h0 : (D.crossingParam z htz - τt D x) * det (D.Γ.dir g) (et D x) +
        det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) = 0 := by
      rw [← w3bg_det_smul_right, ← w3bg_det_add_right, ← e4]; exact hg_z
    rw [e3, w3bg_det_add_right, w3bg_det_smul_right]
    have hkg' : det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) =
        -((D.crossingParam z htz - τt D x) * det (D.Γ.dir g) (et D x)) := by linarith
    rw [hkg']
    have e5 : (ε * det (D.Γ.dir g) (et D x) + -((D.crossingParam z htz - τt D x) * det (D.Γ.dir g) (et D x))) *
        -((D.crossingParam z htz - τt D x) * det (D.Γ.dir g) (et D x)) =
        ((D.crossingParam z htz - τt D x - ε) * (D.crossingParam z htz - τt D x)) *
          (det (D.Γ.dir g) (et D x) * det (D.Γ.dir g) (et D x)) := by ring
    rw [e5]
    exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hzt)) (mul_self_pos.mpr hgt_det)
  -- the generators
  have hgen : ∀ q ∈ ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane),
      q = D.Γ.crossingPoint y ∨ q = sMinus D x ε ∨ q = tPlus D x ε ∨ q = D.Γ.crossingPoint z := by
    intro q hq
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq
  have hmem_y : D.Γ.crossingPoint y ∈
      ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane) := by simp
  have hmem_sm : sMinus D x ε ∈
      ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane) := by simp
  have hmem_tp : tPlus D x ε ∈
      ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane) := by simp
  have hmem_z : D.Γ.crossingPoint z ∈
      ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane) := by simp
  -- `K` inside the two closed half-planes at `p` and inside the triangle `Δ = conv{p, y, z}`
  have hKs : convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} ⊆
      {q : Plane | 0 ≤ det (es D x) (q - pt D x) * det (es D x) (et D x)} := by
    apply w3bg_convexHull_subset_halfPlane'
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · rw [hs_y, zero_mul]
    · rw [hs_sm, zero_mul]
    · exact hs_tp.le
    · exact hs_z.le
  have hKt : convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} ⊆
      {q : Plane | 0 ≤ det (et D x) (q - pt D x) * det (es D x) (et D x)} := by
    apply w3bg_convexHull_subset_halfPlane'
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact ht_y.le
    · exact ht_sm.le
    · rw [ht_tp, zero_mul]
    · rw [ht_z, zero_mul]
  have hKΔ : convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} ⊆
      convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z} := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (by simp)
    · refine segment_subset_convexHull (𝕜 := ℝ) (x := D.Γ.crossingPoint y) (y := D.Γ.crossingPoint x)
        (by simp) (by simp) ?_
      rw [hsm', hYs, show D.Γ.crossingPoint x = D.Γ.edgePt (sS D x) (τs D x) from hpt_s,
        um7_edgePt_mem_segment_iff D.generic, min_eq_left hys.le, max_eq_right hys.le]
      constructor <;> linarith [hε.pos]
    · refine segment_subset_convexHull (𝕜 := ℝ) (x := D.Γ.crossingPoint x) (y := D.Γ.crossingPoint z)
        (by simp) (by simp) ?_
      rw [htp', hZt, show D.Γ.crossingPoint x = D.Γ.edgePt (tS D x) (τt D x) from hpt_t,
        um7_edgePt_mem_segment_iff D.generic, min_eq_left hzt.le, max_eq_right hzt.le]
      constructor <;> linarith [hε.pos]
    · exact subset_convexHull ℝ _ (by simp)
  -- the three lines through `K`
  have hline_s : ∀ θ : ℝ, det (es D x) (Γ₀.edgePt uIn θ - pt D x) = 0 := by
    intro θ
    rw [heIn, zero_smul, add_zero, add_sub_cancel_left, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hline_t : ∀ θ : ℝ, det (et D x) (Γ₀.edgePt uOut θ - pt D x) = 0 := by
    intro θ
    rw [heOut, zero_smul, add_zero, add_sub_cancel_left, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hline_g : ∀ θ : ℝ, det (D.Γ.dir g) (Γ₀.edgePt uG θ - D.Γ.crossingPoint y) = 0 := by
    intro θ
    rw [heG, hYg, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
      w3bg_det_self, mul_zero]
  have hS_s : ∀ q ∈ ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane),
      q ∈ segment ℝ (D.Γ.crossingPoint y) (sMinus D x ε) ∨
        0 < det (es D x) (q - pt D x) * det (es D x) (et D x) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inr hs_tp
    · exact Or.inr hs_z
  have hS_t : ∀ q ∈ ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane),
      q ∈ segment ℝ (tPlus D x ε) (D.Γ.crossingPoint z) ∨
        0 < det (et D x) (q - pt D x) * det (es D x) (et D x) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inr ht_y
    · exact Or.inr ht_sm
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
  have hS_g : ∀ q ∈ ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane),
      q ∈ segment ℝ (D.Γ.crossingPoint y) (D.Γ.crossingPoint z) ∨
        0 < det (D.Γ.dir g) (q - D.Γ.crossingPoint y) * det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr hg_sm
    · exact Or.inr hg_tp
    · exact Or.inl (right_mem_segment ℝ _ _)
  have hΓ₀ : Γ₀.Generic := generic D x M hε
  refine ⟨{
    i := uIn.1
    a := uIn.2
    j := 2
    hj := by norm_num
    hk := hk5
    s := uG
    y := y₀
    z := z₀
    hy := hyv
    hz := by
      show z₀.val = {(⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand), uG}
      rw [hOut]; exact hzv
    run_free := ?_
    no_io := ?_
    same_over := ?_
    ty := ((toDiagram D x M hε).switch y₀).crossingParam y₀ huIn_y
    tz := ((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z
    tsy := ((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_y
    tsz := ((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_z
    hty := (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huIn_y).2.2.symm
    htz := by
      show Γ₀.edgePt (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) _ = Γ₀.crossingPoint z₀
      rw [hOut]; exact hsw z₀ uOut huOut_z
    htsy := (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huG_y).2.2.symm
    htsz := (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huG_z).2.2.symm
    K := convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z}
    K_convex := convex_convexHull ℝ _
    K_compact := (Set.toFinite _).isCompact_convexHull ℝ
    run_mem := ?_
    in_iff := ?_
    out_iff := ?_
    s_iff := ?_
    clear := ?_ }, rfl, rfl, rfl, huG, huIn, rfl⟩
  · -- run_free: the only run edge is the arc `arcST`, which carries no crossing
    intro m h1 h2 x' hmem
    have hm : m = 1 := by omega
    subst hm
    have hmem' : (⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) ∈ x'.val := hmem
    rw [Nat.cast_one, hArc] at hmem'
    exact (kind_ne_arc_of_mem D x M hε x' hmem').1 hkArc
  · -- no_io: a crossing of `cutStartS` with `cutEndT` would be a lift of `x`
    intro x' hx'
    have hx'' : uIn ∈ x'.val ∧ (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) ∈ x'.val := hx'
    rw [hOut] at hx''
    obtain ⟨h1, h2⟩ := hx''
    have horIn : M.orig uIn = sS D x := by unfold SpliceModel.orig; rw [hkIn]; rfl
    have horOut : M.orig uOut = tS D x := by unfold SpliceModel.orig; rw [hkOut]; rfl
    have hs' : sS D x ∈ (origCrossing D x M hε x').val := by
      have := orig_mem_origCrossing D x M hε h1; rwa [horIn] at this
    have ht' : tS D x ∈ (origCrossing D x M hε x').val := by
      have := orig_mem_origCrossing D x M hε h2; rwa [horOut] at this
    apply origCrossing_ne D x M hε x'
    apply Subtype.ext
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rw [D.mem_iff] at he
      rcases he with rfl | rfl
      · exact hs'
      · exact ht'
    · rw [D.Γ.crossing_card_two, D.Γ.crossing_card_two]
  · -- same_over: the switch at `y₀` and `hover`
    have hov_y : ((toDiagram D x M hε).switch y₀).overStrand y₀ = (toDiagram D x M hε).underStrand y₀ :=
      (toDiagram D x M hε).switch_overStrand_self y₀
    have hov_z : ((toDiagram D x M hε).switch y₀).overStrand z₀ = (toDiagram D x M hε).overStrand z₀ :=
      (toDiagram D x M hε).switch_overStrand_of_ne hyz₀
    have hor_uy : M.orig ((toDiagram D x M hε).underStrand y₀) = D.underStrand y := by
      have h := toDiagram_underStrand_orig D x M hε y₀; rwa [hy₀] at h
    have hor_oz : M.orig ((toDiagram D x M hε).overStrand z₀) = D.overStrand z := by
      have h := orig_overStrand₀ D x M hε z₀; rwa [hz₀] at h
    have horG : M.orig uG = g := by unfold SpliceModel.orig; rw [hkG]; rfl
    have hA : (toDiagram D x M hε).underStrand y₀ = uG ↔ D.underStrand y = g := by
      constructor
      · intro h; rw [← hor_uy, h, horG]
      · intro h
        exact orig_injOn_crossing D x M hε y₀ ((toDiagram D x M hε).under_mem y₀) huG_y
          (by rw [hor_uy, horG, h])
    have hB : (toDiagram D x M hε).overStrand z₀ = uG ↔ D.overStrand z = g := by
      constructor
      · intro h; rw [← hor_oz, h, horG]
      · intro h
        exact orig_injOn_crossing D x M hε z₀ ((toDiagram D x M hε).over_mem z₀) huG_z
          (by rw [hor_oz, horG, h])
    have hC : D.underStrand y = g ↔ D.overStrand y ≠ g := by
      constructor
      · intro h h'; exact D.under_ne_over y (h.trans h'.symm)
      · intro h
        have hg' := hgy
        rw [D.mem_iff] at hg'
        rcases hg' with hg' | hg'
        · exact absurd hg'.symm h
        · exact hg'.symm
    rw [hov_y, hov_z]
    by_cases hz' : D.overStrand z = g
    · left
      exact ⟨hA.mpr (hC.mpr (fun h => hover.mp h hz')), hB.mpr hz'⟩
    · right
      exact ⟨fun h => (hC.mp (hA.mp h)) (hover.mpr hz'), fun h => hz' (hB.mp h)⟩
  · -- run_mem: the run vertices are `s⁻` and `t⁺`
    intro m h1 h2
    have hm : m = 1 ∨ m = 2 := by omega
    rcases hm with rfl | rfl
    · show Γ₀.tail ⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ ∈ _
      rw [Nat.cast_one, hArc, M.tail_eq, hkArc]
      exact subset_convexHull ℝ _ hmem_sm
    · show Γ₀.tail ⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ ∈ _
      rw [hOut, M.tail_eq, hkOut]
      exact subset_convexHull ℝ _ hmem_tp
  · -- in_iff: `cutStartS ∩ K = [y, s⁻]`
    intro t h0 h1
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull hs_y hs_sm _ hS_s (hline_s t) hmem
      rw [← hEty, ← hIn1, um7_edgePt_mem_segment_iff hΓ₀, min_eq_left hty1] at hseg
      exact hseg.1
    · intro hle
      have hseg : Γ₀.edgePt uIn t ∈ segment ℝ
          (Γ₀.edgePt uIn (((toDiagram D x M hε).switch y₀).crossingParam y₀ huIn_y)) (Γ₀.edgePt uIn 1) := by
        rw [um7_edgePt_mem_segment_iff hΓ₀, min_eq_left hty1, max_eq_right hty1]
        exact ⟨hle, h1⟩
      rw [hEty, hIn1] at hseg
      exact segment_subset_convexHull hmem_y hmem_sm hseg
  · -- out_iff: `cutEndT ∩ K = [t⁺, z]`
    intro t h0 h1
    show Γ₀.edgePt (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) t ∈
      convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} ↔
      t ≤ ((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z
    rw [hOut]
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull ht_tp ht_z _ hS_t (hline_t t) hmem
      rw [← hEtz, ← hOut0, um7_edgePt_mem_segment_iff hΓ₀, max_eq_right htz0] at hseg
      exact hseg.2
    · intro hle
      have hseg : Γ₀.edgePt uOut t ∈ segment ℝ (Γ₀.edgePt uOut 0)
          (Γ₀.edgePt uOut (((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z)) := by
        rw [um7_edgePt_mem_segment_iff hΓ₀, min_eq_left htz0, max_eq_right htz0]
        exact ⟨h0, hle⟩
      rw [hEtz, hOut0] at hseg
      exact segment_subset_convexHull hmem_tp hmem_z hseg
  · -- s_iff: `g ∩ K = [y, z]`
    intro t h0 h1
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull hg_y hg_z _ hS_g (hline_g t) hmem
      rwa [← hEtsy, ← hEtsz, um7_edgePt_mem_segment_iff hΓ₀] at hseg
    · intro hbetween
      have hseg : Γ₀.edgePt uG t ∈ segment ℝ
          (Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_y))
          (Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_z)) := by
        rwa [um7_edgePt_mem_segment_iff hΓ₀]
      rw [hEtsy, hEtsz] at hseg
      exact segment_subset_convexHull hmem_y hmem_z hseg
  · -- clear: every other strand of `Γ₀` misses `K`
    intro u hu1 hu2 hu3 hrun
    have hu2' : u ≠ (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) := hu2
    rw [hOut] at hu2'
    have hu4 : u ≠ uArc := by
      have h := hrun 1 le_rfl one_lt_two
      have h' : u ≠ (⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) := h
      rwa [Nat.cast_one, hArc] at h'
    rw [Set.disjoint_left]
    intro q hqu hqK
    have hqu' : q ∈ (M.kind u).seg ε := (M.seg_eq u).subset hqu
    obtain ⟨κ, hκ⟩ : ∃ κ, M.kind u = κ := ⟨_, rfl⟩
    have hocc : κ.Occurs := hκ ▸ M.kind_occurs u
    have hu_eq : u = M.strandOf κ hocc := by subst hκ; exact (M.strandOf_kind u).symm
    rw [hκ] at hqu'
    cases κ with
    | old e =>
      have hocc' := (u3_occurs_old_iff D x).mp hocc
      have heg : e ≠ g := by
        rintro rfl
        exact hu3 (hu_eq.trans huG.symm)
      have hsub : StrandKind.seg ε (StrandKind.old e) ⊆ D.Γ.seg e :=
        StrandKind.seg_subset_seg_orig ε hε _ (fun h => by cases h) (fun h => by cases h)
      exact Set.disjoint_left.mp (clear e hocc'.1 hocc'.2 heg) (hsub hqu') (hKΔ hqK)
    | cutStartS => exact hu1 (hu_eq.trans huIn.symm)
    | cutEndS =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq_eq : StrandKind.tail ε (StrandKind.cutEndS : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.cutEndS : StrandKind D x) =
          D.Γ.edgePt (sS D x) (τs D x + (ε + θ * (1 - τs D x - ε))) := by
        rw [u3_cutEndS_pt D x θ, D.Γ.edgePt_eq, pt_eq_s]; module
      have hline : det (es D x) (D.Γ.edgePt (sS D x) (τs D x + (ε + θ * (1 - τs D x - ε))) - pt D x) = 0 := by
        rw [hpt_s, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
          w3bg_det_self, mul_zero]
      rw [hq_eq] at hqK
      have hseg := w3bg_line_convexHull hs_y hs_sm _ hS_s hline hqK
      rw [hYs, hsm', um7_edgePt_mem_segment_iff D.generic, max_eq_right (by linarith)] at hseg
      have hc : 0 ≤ θ * (1 - τs D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τs])
      linarith [hseg.2, hε.pos]
    | cutStartT =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq_eq : StrandKind.tail ε (StrandKind.cutStartT : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.cutStartT : StrandKind D x) =
          D.Γ.edgePt (tS D x) (τt D x + (θ * (τt D x - ε) - τt D x)) := by
        rw [u3_cutStartT_pt D x θ, D.Γ.edgePt_eq, pt_eq_t]; module
      have hline : det (et D x) (D.Γ.edgePt (tS D x) (τt D x + (θ * (τt D x - ε) - τt D x)) - pt D x) = 0 := by
        rw [hpt_t, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
          w3bg_det_self, mul_zero]
      rw [hq_eq] at hqK
      have hseg := w3bg_line_convexHull ht_tp ht_z _ hS_t hline hqK
      rw [htp', hZt, um7_edgePt_mem_segment_iff D.generic] at hseg
      have hc : θ * (τt D x - ε) ≤ τt D x - ε := mul_le_of_le_one_left (by linarith [hε.lt_τt]) h1
      rcases min_le_iff.mp hseg.1 with h | h <;> linarith [hε.pos]
    | cutEndT => exact hu2' (hu_eq.trans huOut.symm)
    | arcST => exact hu4 (hu_eq.trans huArc.symm)
    | arcTS =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq1 : StrandKind.tail ε (StrandKind.arcTS : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.arcTS : StrandKind D x) - pt D x =
          (θ * ε) • es D x + ((θ - 1) * ε) • et D x := by
        rw [u3_arcTS_pt D x θ]; abel
      have hA := hKs hqK
      have hB := hKt hqK
      simp only [Set.mem_setOf_eq] at hA hB
      rw [hq1, w3bg_det_add_right, w3bg_det_smul_right, w3bg_det_smul_right, w3bg_det_self] at hA hB
      rw [w3bg_det_comm (et D x) (es D x)] at hB
      have hP : 0 < ε * (det (es D x) (et D x) * det (es D x) (et D x)) := mul_pos hε.pos hdd
      have eA : (θ * ε * 0 + (θ - 1) * ε * det (es D x) (et D x)) * det (es D x) (et D x) =
          (θ - 1) * (ε * (det (es D x) (et D x) * det (es D x) (et D x))) := by ring
      have eB : (θ * ε * -det (es D x) (et D x) + (θ - 1) * ε * 0) * det (es D x) (et D x) =
          -θ * (ε * (det (es D x) (et D x) * det (es D x) (et D x))) := by ring
      rw [eA] at hA
      rw [eB] at hB
      nlinarith [hA, hB, hP]

/-- **(G) the corrected `arcTS` site (rule 3): `w3g_bigonData_smooth_arcTS` with the missing hypothesis
`hk5 : 5 ≤ k` on the component of `cutStartT`** (the same kink counterexample as for `arcST`, with `s ↔ t`:
component `A` has `dd + 2 = 4` strands when `dd = 2`).  The proof is `w3bg_bigonData_smooth_arcST_of_five` with the
roles `s ↔ t`, `y ↔ z` (entering crossing `z` on `cutStartT`, exiting crossing `y` on `cutEndS`, `B.y = z₀`,
`B.z = y₀`); the switch stays at `y₀ = B.z`. -/
theorem w3bg_bigonData_smooth_arcTS_of_five (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hk5 : 5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- the four strands
  obtain ⟨uIn, huIn⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT :=
    ⟨_, rfl⟩
  obtain ⟨uArc, huArc⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.arcTS StrandKind.occurs_arcTS := ⟨_, rfl⟩
  obtain ⟨uOut, huOut⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS :=
    ⟨_, rfl⟩
  obtain ⟨uG, huG⟩ : ∃ u : Γ₀.Strand, u = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) :=
    ⟨_, rfl⟩
  rw [← huIn] at hk5
  have hkIn : M.kind uIn = StrandKind.cutStartT := by rw [huIn, M.kind_strandOf]
  have hkArc : M.kind uArc = StrandKind.arcTS := by rw [huArc, M.kind_strandOf]
  have hkOut : M.kind uOut = StrandKind.cutEndS := by rw [huOut, M.kind_strandOf]
  have hkG : M.kind uG = StrandKind.old g := by rw [huG, M.kind_strandOf]
  -- labels
  have hArc : (⟨uIn.1, uIn.2 + 1⟩ : Γ₀.Strand) = uArc := by
    apply M.kind_injective
    rw [M.kind_succ, hkIn, hkArc]
    rfl
  have hOut : (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) = uOut := by
    apply M.kind_injective
    have h2 : uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = (uIn.2 + 1) + 1 := by push_cast; ring
    rw [h2]
    have h3 : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1⟩).succ := M.kind_succ ⟨uIn.1, uIn.2 + 1⟩
    rw [h3, hArc, hkArc, hkOut]
    rfl
  -- the crossings and their lifts
  have hzx : z ≠ x := by rw [← hz₀]; exact origCrossing_ne D x M hε z₀
  have hyx : y ≠ x := by rw [← hy₀]; exact origCrossing_ne D x M hε y₀
  have hgz : g ∈ z.val := by rw [hz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hgy : g ∈ y.val := by rw [hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hlift_z : liftCrossing D x M hε z hzx = z₀ := by
    have key : ∀ (y'' : D.Γ.Crossing) (h : y'' ≠ x), y'' = z →
        liftCrossing D x M hε y'' h = liftCrossing D x M hε z hzx := by
      rintro y'' h rfl; rfl
    exact (key _ _ hz₀).symm.trans (liftCrossing_origCrossing D x M hε z₀)
  have hlift_y : liftCrossing D x M hε y hyx = y₀ := by
    have key : ∀ (z'' : D.Γ.Crossing) (h : z'' ≠ x), z'' = y →
        liftCrossing D x M hε z'' h = liftCrossing D x M hε y hyx := by
      rintro z'' h rfl; rfl
    exact (key _ _ hy₀).symm.trans (liftCrossing_origCrossing D x M hε y₀)
  have hzv : z₀.val = {uIn, uG} := by
    rw [← hlift_z, w3bg_val_liftCrossing D x M hε z hzx (tS D x) g hgt.symm hz htz hgz,
      w3bg_liftStrand_t D x M z htz hzt, w3bg_liftStrand_old D x M z g hgz hgs hgt, huIn, huG]
  have hyv : y₀.val = {uOut, uG} := by
    rw [← hlift_y, w3bg_val_liftCrossing D x M hε y hyx (sS D x) g hgs.symm hy hsy hgy,
      w3bg_liftStrand_s' D x M y hsy hys.le, w3bg_liftStrand_old D x M y g hgy hgs hgt, huOut, huG]
  have huIn_y : uIn ∈ z₀.val := by rw [hzv]; exact Finset.mem_insert_self _ _
  have huG_y : uG ∈ z₀.val := by rw [hzv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have huOut_z : uOut ∈ y₀.val := by rw [hyv]; exact Finset.mem_insert_self _ _
  have huG_z : uG ∈ y₀.val := by rw [hyv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hyz₀ : y₀ ≠ z₀ := by
    intro h
    have h1 : y = z := by rw [← hy₀, ← hz₀, h]
    have h2 : tS D x ∈ y.val := by rw [h1]; exact htz
    rw [hy] at h2
    rcases Finset.mem_insert.mp h2 with h3 | h3
    · exact sS_ne_tS D x h3.symm
    · exact hgt (Finset.mem_singleton.mp h3).symm
  -- points and parameters in `D`
  have hpz : Γ₀.crossingPoint z₀ = D.Γ.crossingPoint z := by
    rw [crossingPoint_origCrossing D x M hε z₀, hz₀]
  have hpy : Γ₀.crossingPoint y₀ = D.Γ.crossingPoint y := by
    rw [crossingPoint_origCrossing D x M hε y₀, hy₀]
  have hZt : D.Γ.crossingPoint z = D.Γ.edgePt (tS D x) (D.crossingParam z htz) :=
    (D.crossingParam_spec z htz).2.2
  have hYs : D.Γ.crossingPoint y = D.Γ.edgePt (sS D x) (D.crossingParam y hsy) :=
    (D.crossingParam_spec y hsy).2.2
  have hZg : D.Γ.crossingPoint z = D.Γ.edgePt g (D.crossingParam z hgz) := (D.crossingParam_spec z hgz).2.2
  have hYg : D.Γ.crossingPoint y = D.Γ.edgePt g (D.crossingParam y hgy) := (D.crossingParam_spec y hgy).2.2
  have hpt_t : pt D x = D.Γ.edgePt (tS D x) (τt D x) := pt_eq_t D x
  have hpt_s : pt D x = D.Γ.edgePt (sS D x) (τs D x) := pt_eq_s D x
  have hZsub : D.Γ.crossingPoint z - pt D x = (D.crossingParam z htz - τt D x) • et D x := by
    rw [hZt, hpt_t, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul]
  have hYsub : D.Γ.crossingPoint y - pt D x = (D.crossingParam y hsy - τs D x) • es D x := by
    rw [hYs, hpt_s, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul]
  have htp : tMinus D x ε - pt D x = -(ε • et D x) := by rw [tMinus, sub_sub_cancel_left]
  have hsm : sPlus D x ε - pt D x = ε • es D x := by rw [sPlus, add_sub_cancel_left]
  have htp' : tMinus D x ε = D.Γ.edgePt (tS D x) (τt D x - ε) := tMinus_eq_edgePoint D x ε
  have hsm' : sPlus D x ε = D.Γ.edgePt (sS D x) (τs D x + ε) := sPlus_eq_edgePoint D x ε
  have hd : det (et D x) (es D x) ≠ 0 := by rw [w3bg_det_comm]; exact neg_ne_zero.mpr (det_es_et_ne_zero D x)
  have hdd : 0 < det (et D x) (es D x) * det (et D x) (es D x) := mul_self_pos.mpr hd
  -- clearance: `z`, `y` are farther from `p` than the cut points
  have hεz : ε < τt D x - D.crossingParam z htz := by
    have h1 := r₁_le_dist_crossingPoint D x hzx
    rw [hZt, hpt_t, D.Γ.dist_edgePt, abs_of_pos (sub_pos.mpr hzt)] at h1
    have hes : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
    exact lt_of_mul_lt_mul_right (hε.mul_et_lt.trans_le h1) hes.le
  have hεy : ε < D.crossingParam y hsy - τs D x := by
    have h1 := r₁_le_dist_crossingPoint D x hyx
    rw [hYs, hpt_s, D.Γ.dist_edgePt, abs_sub_comm, abs_of_pos (sub_pos.mpr hys)] at h1
    have het : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
    exact lt_of_mul_lt_mul_right (hε.mul_es_lt.trans_le h1) het.le
  -- transversality of `g` with `s` at `z` and with `t` at `y`
  have hgt_det : det (D.Γ.dir g) (et D x) ≠ 0 := by
    have hspec := D.Γ.crossing_pair_spec z hgz htz hgt
    exact D.generic.transverse _ _ hspec.1 hspec.2
  have hgs_det : det (D.Γ.dir g) (es D x) ≠ 0 := by
    have hspec := D.Γ.crossing_pair_spec y hgy hsy hgs
    exact D.generic.transverse _ _ hspec.1 hspec.2
  -- edge points of the three local strands of `Γ₀`
  have heOut : ∀ θ : ℝ, Γ₀.edgePt uIn θ = pt D x + (0:ℝ) • es D x + (θ * (τt D x - ε) - τt D x) • et D x := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkIn]; exact u3_cutStartT_pt D x θ
  have heIn : ∀ θ : ℝ, Γ₀.edgePt uOut θ = pt D x + (ε + θ * (1 - τs D x - ε)) • es D x + (0:ℝ) • et D x := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkOut]; exact u3_cutEndS_pt D x θ
  have heG : ∀ θ : ℝ, Γ₀.edgePt uG θ = D.Γ.edgePt g θ := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkG]; rfl
  have hOut0 : Γ₀.edgePt uIn 1 = tMinus D x ε := by rw [heOut, tMinus]; module
  have hIn1 : Γ₀.edgePt uOut 0 = sPlus D x ε := by rw [heIn, sPlus]; module
  have hsw : ∀ (w : Γ₀.Crossing) (u : Γ₀.Strand) (hu : u ∈ w.val),
      Γ₀.edgePt u (((toDiagram D x M hε).switch y₀).crossingParam w hu) = Γ₀.crossingPoint w :=
    fun w u hu => (((toDiagram D x M hε).switch y₀).crossingParam_spec w hu).2.2.symm
  have hEtz : Γ₀.edgePt uIn (((toDiagram D x M hε).switch y₀).crossingParam z₀ huIn_y) = D.Γ.crossingPoint z := by
    rw [hsw, hpz]
  have hEty : Γ₀.edgePt uOut (((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z) = D.Γ.crossingPoint y := by
    rw [hsw, hpy]
  have hEtsz : Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_y) = D.Γ.crossingPoint z := by
    rw [hsw, hpz]
  have hEtsy : Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_z) = D.Γ.crossingPoint y := by
    rw [hsw, hpy]
  have htz0 : ((toDiagram D x M hε).switch y₀).crossingParam z₀ huIn_y ≤ 1 :=
    (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huIn_y).2.1
  have hty1 : 0 ≤ ((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z :=
    (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huOut_z).1
  -- the half-plane data of the line `s`
  have ht_tp : det (et D x) (D.Γ.crossingPoint z - pt D x) = 0 := by
    rw [hZsub, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have ht_z : det (et D x) (tMinus D x ε - pt D x) = 0 := by
    rw [htp, w3bg_det_neg_right, w3bg_det_smul_right, w3bg_det_self, mul_zero, neg_zero]
  have ht_y : 0 < det (et D x) (sPlus D x ε - pt D x) * det (et D x) (es D x) := by
    rw [hsm, w3bg_det_smul_right, mul_assoc]; exact mul_pos hε.pos hdd
  have ht_sm : 0 < det (et D x) (D.Γ.crossingPoint y - pt D x) * det (et D x) (es D x) := by
    rw [hYsub, w3bg_det_smul_right, mul_assoc]; exact mul_pos (sub_pos.mpr hys) hdd
  -- the half-plane data of the line `t`
  have hs_tp : 0 < det (es D x) (D.Γ.crossingPoint z - pt D x) * det (et D x) (es D x) := by
    rw [hZsub, w3bg_det_smul_right, w3bg_det_comm (es D x) (et D x)]
    have e : (D.crossingParam z htz - τt D x) * -det (et D x) (es D x) * det (et D x) (es D x) =
        (τt D x - D.crossingParam z htz) * (det (et D x) (es D x) * det (et D x) (es D x)) := by ring
    rw [e]; exact mul_pos (sub_pos.mpr hzt) hdd
  have hs_z : 0 < det (es D x) (tMinus D x ε - pt D x) * det (et D x) (es D x) := by
    rw [htp, w3bg_det_neg_right, w3bg_det_smul_right, w3bg_det_comm (es D x) (et D x)]
    have e : -(ε * -det (et D x) (es D x)) * det (et D x) (es D x) =
        ε * (det (et D x) (es D x) * det (et D x) (es D x)) := by ring
    rw [e]; exact mul_pos hε.pos hdd
  have hs_y : det (es D x) (sPlus D x ε - pt D x) = 0 := by
    rw [hsm, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hs_sm : det (es D x) (D.Γ.crossingPoint y - pt D x) = 0 := by
    rw [hYsub, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  -- the half-plane data of the line `g` (through `z`), sign constant `kg = det eg (p − z)`
  have hg_y : det (D.Γ.dir g) (D.Γ.crossingPoint z - D.Γ.crossingPoint z) = 0 := by
    rw [sub_self]; simp only [det, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero]
  have hg_z : det (D.Γ.dir g) (D.Γ.crossingPoint y - D.Γ.crossingPoint z) = 0 := by
    rw [hYg, hZg, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
      w3bg_det_self, mul_zero]
  have hkg : det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) =
      (τt D x - D.crossingParam z htz) * det (D.Γ.dir g) (et D x) := by
    rw [← neg_sub, hZsub, w3bg_det_neg_right, w3bg_det_smul_right]; ring
  have hg_sm : 0 < det (D.Γ.dir g) (tMinus D x ε - D.Γ.crossingPoint z) *
      det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) := by
    have e1 : tMinus D x ε - D.Γ.crossingPoint z = (τt D x - D.crossingParam z htz - ε) • et D x := by
      rw [tMinus, pt_eq_t, hZt, D.Γ.edgePt_eq]; module
    rw [e1, hkg, w3bg_det_smul_right]
    have e2 : (τt D x - D.crossingParam z htz - ε) * det (D.Γ.dir g) (et D x) *
        ((τt D x - D.crossingParam z htz) * det (D.Γ.dir g) (et D x)) =
        ((τt D x - D.crossingParam z htz - ε) * (τt D x - D.crossingParam z htz)) *
          (det (D.Γ.dir g) (et D x) * det (D.Γ.dir g) (et D x)) := by ring
    rw [e2]
    exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hzt)) (mul_self_pos.mpr hgt_det)
  have hg_tp : 0 < det (D.Γ.dir g) (sPlus D x ε - D.Γ.crossingPoint z) *
      det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) := by
    have e3 : sPlus D x ε - D.Γ.crossingPoint z = ε • es D x + (pt D x - D.Γ.crossingPoint z) := by
      rw [sPlus]; abel
    have e4 : D.Γ.crossingPoint y - D.Γ.crossingPoint z =
        (D.crossingParam y hsy - τs D x) • es D x + (pt D x - D.Γ.crossingPoint z) := by
      rw [← hYsub]; abel
    have h0 : (D.crossingParam y hsy - τs D x) * det (D.Γ.dir g) (es D x) +
        det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) = 0 := by
      rw [← w3bg_det_smul_right, ← w3bg_det_add_right, ← e4]; exact hg_z
    rw [e3, w3bg_det_add_right, w3bg_det_smul_right]
    have hkg' : det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) =
        -((D.crossingParam y hsy - τs D x) * det (D.Γ.dir g) (es D x)) := by linarith
    rw [hkg']
    have e5 : (ε * det (D.Γ.dir g) (es D x) + -((D.crossingParam y hsy - τs D x) * det (D.Γ.dir g) (es D x))) *
        -((D.crossingParam y hsy - τs D x) * det (D.Γ.dir g) (es D x)) =
        ((D.crossingParam y hsy - τs D x - ε) * (D.crossingParam y hsy - τs D x)) *
          (det (D.Γ.dir g) (es D x) * det (D.Γ.dir g) (es D x)) := by ring
    rw [e5]
    exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hys)) (mul_self_pos.mpr hgs_det)
  -- the generators
  have hgen : ∀ q ∈ ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane),
      q = D.Γ.crossingPoint z ∨ q = tMinus D x ε ∨ q = sPlus D x ε ∨ q = D.Γ.crossingPoint y := by
    intro q hq
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq
  have hmem_z : D.Γ.crossingPoint z ∈
      ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane) := by simp
  have hmem_tp : tMinus D x ε ∈
      ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane) := by simp
  have hmem_sm : sPlus D x ε ∈
      ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane) := by simp
  have hmem_y : D.Γ.crossingPoint y ∈
      ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane) := by simp
  -- `K` inside the two closed half-planes at `p` and inside the triangle `Δ = conv{p, z, y}`
  have hKt : convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} ⊆
      {q : Plane | 0 ≤ det (et D x) (q - pt D x) * det (et D x) (es D x)} := by
    apply w3bg_convexHull_subset_halfPlane'
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · rw [ht_tp, zero_mul]
    · rw [ht_z, zero_mul]
    · exact ht_y.le
    · exact ht_sm.le
  have hKs : convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} ⊆
      {q : Plane | 0 ≤ det (es D x) (q - pt D x) * det (et D x) (es D x)} := by
    apply w3bg_convexHull_subset_halfPlane'
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact hs_tp.le
    · exact hs_z.le
    · rw [hs_y, zero_mul]
    · rw [hs_sm, zero_mul]
  have hKΔ : convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} ⊆
      convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z} := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (by simp)
    · refine segment_subset_convexHull (𝕜 := ℝ) (x := D.Γ.crossingPoint z) (y := D.Γ.crossingPoint x)
        (by simp) (by simp) ?_
      rw [htp', hZt, show D.Γ.crossingPoint x = D.Γ.edgePt (tS D x) (τt D x) from hpt_t,
        um7_edgePt_mem_segment_iff D.generic, min_eq_left hzt.le, max_eq_right hzt.le]
      constructor <;> linarith [hε.pos]
    · refine segment_subset_convexHull (𝕜 := ℝ) (x := D.Γ.crossingPoint x) (y := D.Γ.crossingPoint y)
        (by simp) (by simp) ?_
      rw [hsm', hYs, show D.Γ.crossingPoint x = D.Γ.edgePt (sS D x) (τs D x) from hpt_s,
        um7_edgePt_mem_segment_iff D.generic, min_eq_left hys.le, max_eq_right hys.le]
      constructor <;> linarith [hε.pos]
    · exact subset_convexHull ℝ _ (by simp)
  -- the three lines through `K`
  have hline_t : ∀ θ : ℝ, det (et D x) (Γ₀.edgePt uIn θ - pt D x) = 0 := by
    intro θ
    rw [heOut, zero_smul, add_zero, add_sub_cancel_left, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hline_s : ∀ θ : ℝ, det (es D x) (Γ₀.edgePt uOut θ - pt D x) = 0 := by
    intro θ
    rw [heIn, zero_smul, add_zero, add_sub_cancel_left, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hline_g : ∀ θ : ℝ, det (D.Γ.dir g) (Γ₀.edgePt uG θ - D.Γ.crossingPoint z) = 0 := by
    intro θ
    rw [heG, hZg, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
      w3bg_det_self, mul_zero]
  have hS_t : ∀ q ∈ ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane),
      q ∈ segment ℝ (D.Γ.crossingPoint z) (tMinus D x ε) ∨
        0 < det (et D x) (q - pt D x) * det (et D x) (es D x) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inr ht_y
    · exact Or.inr ht_sm
  have hS_s : ∀ q ∈ ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane),
      q ∈ segment ℝ (sPlus D x ε) (D.Γ.crossingPoint y) ∨
        0 < det (es D x) (q - pt D x) * det (et D x) (es D x) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inr hs_tp
    · exact Or.inr hs_z
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
  have hS_g : ∀ q ∈ ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane),
      q ∈ segment ℝ (D.Γ.crossingPoint z) (D.Γ.crossingPoint y) ∨
        0 < det (D.Γ.dir g) (q - D.Γ.crossingPoint z) * det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr hg_sm
    · exact Or.inr hg_tp
    · exact Or.inl (right_mem_segment ℝ _ _)
  have hΓ₀ : Γ₀.Generic := generic D x M hε
  refine ⟨{
    i := uIn.1
    a := uIn.2
    j := 2
    hj := by norm_num
    hk := hk5
    s := uG
    y := z₀
    z := y₀
    hy := hzv
    hz := by
      show y₀.val = {(⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand), uG}
      rw [hOut]; exact hyv
    run_free := ?_
    no_io := ?_
    same_over := ?_
    ty := ((toDiagram D x M hε).switch y₀).crossingParam z₀ huIn_y
    tz := ((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z
    tsy := ((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_y
    tsz := ((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_z
    hty := (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huIn_y).2.2.symm
    htz := by
      show Γ₀.edgePt (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) _ = Γ₀.crossingPoint y₀
      rw [hOut]; exact hsw y₀ uOut huOut_z
    htsy := (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huG_y).2.2.symm
    htsz := (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huG_z).2.2.symm
    K := convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y}
    K_convex := convex_convexHull ℝ _
    K_compact := (Set.toFinite _).isCompact_convexHull ℝ
    run_mem := ?_
    in_iff := ?_
    out_iff := ?_
    s_iff := ?_
    clear := ?_ }, rfl, rfl, rfl, huG, huIn, rfl⟩
  · -- run_free: the only run edge is the arc `arcTS`, which carries no crossing
    intro m h1 h2 x' hmem
    have hm : m = 1 := by omega
    subst hm
    have hmem' : (⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) ∈ x'.val := hmem
    rw [Nat.cast_one, hArc] at hmem'
    exact (kind_ne_arc_of_mem D x M hε x' hmem').2 hkArc
  · -- no_io: a crossing of `cutStartT` with `cutEndS` would be a lift of `x`
    intro x' hx'
    have hx'' : uIn ∈ x'.val ∧ (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) ∈ x'.val := hx'
    rw [hOut] at hx''
    obtain ⟨h1, h2⟩ := hx''
    have horIn : M.orig uIn = tS D x := by unfold SpliceModel.orig; rw [hkIn]; rfl
    have horOut : M.orig uOut = sS D x := by unfold SpliceModel.orig; rw [hkOut]; rfl
    have hs' : tS D x ∈ (origCrossing D x M hε x').val := by
      have := orig_mem_origCrossing D x M hε h1; rwa [horIn] at this
    have ht' : sS D x ∈ (origCrossing D x M hε x').val := by
      have := orig_mem_origCrossing D x M hε h2; rwa [horOut] at this
    apply origCrossing_ne D x M hε x'
    apply Subtype.ext
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rw [D.mem_iff] at he
      rcases he with rfl | rfl
      · exact ht'
      · exact hs'
    · rw [D.Γ.crossing_card_two, D.Γ.crossing_card_two]
  · -- same_over: the switch at `y₀` (= `B.z`) and `hover`
    have hov_y : ((toDiagram D x M hε).switch y₀).overStrand y₀ = (toDiagram D x M hε).underStrand y₀ :=
      (toDiagram D x M hε).switch_overStrand_self y₀
    have hov_z : ((toDiagram D x M hε).switch y₀).overStrand z₀ = (toDiagram D x M hε).overStrand z₀ :=
      (toDiagram D x M hε).switch_overStrand_of_ne hyz₀.symm
    have hor_uy : M.orig ((toDiagram D x M hε).underStrand y₀) = D.underStrand y := by
      have h := toDiagram_underStrand_orig D x M hε y₀; rwa [hy₀] at h
    have hor_oz : M.orig ((toDiagram D x M hε).overStrand z₀) = D.overStrand z := by
      have h := orig_overStrand₀ D x M hε z₀; rwa [hz₀] at h
    have horG : M.orig uG = g := by unfold SpliceModel.orig; rw [hkG]; rfl
    have hA : (toDiagram D x M hε).underStrand y₀ = uG ↔ D.underStrand y = g := by
      constructor
      · intro h; rw [← hor_uy, h, horG]
      · intro h
        exact orig_injOn_crossing D x M hε y₀ ((toDiagram D x M hε).under_mem y₀) huG_z
          (by rw [hor_uy, horG, h])
    have hB : (toDiagram D x M hε).overStrand z₀ = uG ↔ D.overStrand z = g := by
      constructor
      · intro h; rw [← hor_oz, h, horG]
      · intro h
        exact orig_injOn_crossing D x M hε z₀ ((toDiagram D x M hε).over_mem z₀) huG_y
          (by rw [hor_oz, horG, h])
    have hC : D.underStrand y = g ↔ D.overStrand y ≠ g := by
      constructor
      · intro h h'; exact D.under_ne_over y (h.trans h'.symm)
      · intro h
        have hg' := hgy
        rw [D.mem_iff] at hg'
        rcases hg' with hg' | hg'
        · exact absurd hg'.symm h
        · exact hg'.symm
    rw [hov_y, hov_z]
    by_cases hz' : D.overStrand z = g
    · left
      exact ⟨hB.mpr hz', hA.mpr (hC.mpr (fun h => hover.mp h hz'))⟩
    · right
      exact ⟨fun h => hz' (hB.mp h), fun h => (hC.mp (hA.mp h)) (hover.mpr hz')⟩
  · -- run_mem: the run vertices are `s⁻` and `t⁺`
    intro m h1 h2
    have hm : m = 1 ∨ m = 2 := by omega
    rcases hm with rfl | rfl
    · show Γ₀.tail ⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ ∈ _
      rw [Nat.cast_one, hArc, M.tail_eq, hkArc]
      exact subset_convexHull ℝ _ hmem_tp
    · show Γ₀.tail ⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ ∈ _
      rw [hOut, M.tail_eq, hkOut]
      exact subset_convexHull ℝ _ hmem_sm
  · -- in_iff: `cutStartT ∩ K = [z, s⁻]`
    intro t h0 h1
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull ht_tp ht_z _ hS_t (hline_t t) hmem
      rw [← hEtz, ← hOut0, um7_edgePt_mem_segment_iff hΓ₀, min_eq_left htz0] at hseg
      exact hseg.1
    · intro hle
      have hseg : Γ₀.edgePt uIn t ∈ segment ℝ
          (Γ₀.edgePt uIn (((toDiagram D x M hε).switch y₀).crossingParam z₀ huIn_y)) (Γ₀.edgePt uIn 1) := by
        rw [um7_edgePt_mem_segment_iff hΓ₀, min_eq_left htz0, max_eq_right htz0]
        exact ⟨hle, h1⟩
      rw [hEtz, hOut0] at hseg
      exact segment_subset_convexHull hmem_z hmem_tp hseg
  · -- out_iff: `cutEndS ∩ K = [t⁺, y]`
    intro t h0 h1
    show Γ₀.edgePt (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) t ∈
      convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} ↔
      t ≤ ((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z
    rw [hOut]
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull hs_y hs_sm _ hS_s (hline_s t) hmem
      rw [← hEty, ← hIn1, um7_edgePt_mem_segment_iff hΓ₀, max_eq_right hty1] at hseg
      exact hseg.2
    · intro hle
      have hseg : Γ₀.edgePt uOut t ∈ segment ℝ (Γ₀.edgePt uOut 0)
          (Γ₀.edgePt uOut (((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z)) := by
        rw [um7_edgePt_mem_segment_iff hΓ₀, min_eq_left hty1, max_eq_right hty1]
        exact ⟨h0, hle⟩
      rw [hEty, hIn1] at hseg
      exact segment_subset_convexHull hmem_sm hmem_y hseg
  · -- s_iff: `g ∩ K = [z, y]`
    intro t h0 h1
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull hg_y hg_z _ hS_g (hline_g t) hmem
      rwa [← hEtsz, ← hEtsy, um7_edgePt_mem_segment_iff hΓ₀] at hseg
    · intro hbetween
      have hseg : Γ₀.edgePt uG t ∈ segment ℝ
          (Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_y))
          (Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_z)) := by
        rwa [um7_edgePt_mem_segment_iff hΓ₀]
      rw [hEtsz, hEtsy] at hseg
      exact segment_subset_convexHull hmem_z hmem_y hseg
  · -- clear: every other strand of `Γ₀` misses `K`
    intro u hu1 hu2 hu3 hrun
    have hu2' : u ≠ (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) := hu2
    rw [hOut] at hu2'
    have hu4 : u ≠ uArc := by
      have h := hrun 1 le_rfl one_lt_two
      have h' : u ≠ (⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) := h
      rwa [Nat.cast_one, hArc] at h'
    rw [Set.disjoint_left]
    intro q hqu hqK
    have hqu' : q ∈ (M.kind u).seg ε := (M.seg_eq u).subset hqu
    obtain ⟨κ, hκ⟩ : ∃ κ, M.kind u = κ := ⟨_, rfl⟩
    have hocc : κ.Occurs := hκ ▸ M.kind_occurs u
    have hu_eq : u = M.strandOf κ hocc := by subst hκ; exact (M.strandOf_kind u).symm
    rw [hκ] at hqu'
    cases κ with
    | old e =>
      have hocc' := (u3_occurs_old_iff D x).mp hocc
      have heg : e ≠ g := by
        rintro rfl
        exact hu3 (hu_eq.trans huG.symm)
      have hsub : StrandKind.seg ε (StrandKind.old e) ⊆ D.Γ.seg e :=
        StrandKind.seg_subset_seg_orig ε hε _ (fun h => by cases h) (fun h => by cases h)
      exact Set.disjoint_left.mp (clear e hocc'.1 hocc'.2 heg) (hsub hqu') (hKΔ hqK)
    | cutStartT => exact hu1 (hu_eq.trans huIn.symm)
    | cutEndT =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq_eq : StrandKind.tail ε (StrandKind.cutEndT : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.cutEndT : StrandKind D x) =
          D.Γ.edgePt (tS D x) (τt D x + (ε + θ * (1 - τt D x - ε))) := by
        rw [u3_cutEndT_pt D x θ, D.Γ.edgePt_eq, pt_eq_t]; module
      have hline : det (et D x) (D.Γ.edgePt (tS D x) (τt D x + (ε + θ * (1 - τt D x - ε))) - pt D x) = 0 := by
        rw [hpt_t, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
          w3bg_det_self, mul_zero]
      rw [hq_eq] at hqK
      have hseg := w3bg_line_convexHull ht_tp ht_z _ hS_t hline hqK
      rw [hZt, htp', um7_edgePt_mem_segment_iff D.generic, max_eq_right (by linarith)] at hseg
      have hc : 0 ≤ θ * (1 - τt D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τt])
      linarith [hseg.2, hε.pos]
    | cutStartS =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq_eq : StrandKind.tail ε (StrandKind.cutStartS : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.cutStartS : StrandKind D x) =
          D.Γ.edgePt (sS D x) (τs D x + (θ * (τs D x - ε) - τs D x)) := by
        rw [u3_cutStartS_pt D x θ, D.Γ.edgePt_eq, pt_eq_s]; module
      have hline : det (es D x) (D.Γ.edgePt (sS D x) (τs D x + (θ * (τs D x - ε) - τs D x)) - pt D x) = 0 := by
        rw [hpt_s, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
          w3bg_det_self, mul_zero]
      rw [hq_eq] at hqK
      have hseg := w3bg_line_convexHull hs_y hs_sm _ hS_s hline hqK
      rw [hsm', hYs, um7_edgePt_mem_segment_iff D.generic] at hseg
      have hc : θ * (τs D x - ε) ≤ τs D x - ε := mul_le_of_le_one_left (by linarith [hε.lt_τs]) h1
      rcases min_le_iff.mp hseg.1 with h | h <;> linarith [hε.pos]
    | cutEndS => exact hu2' (hu_eq.trans huOut.symm)
    | arcTS => exact hu4 (hu_eq.trans huArc.symm)
    | arcST =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq1 : StrandKind.tail ε (StrandKind.arcST : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.arcST : StrandKind D x) - pt D x =
          (θ * ε) • et D x + ((θ - 1) * ε) • es D x := by
        rw [u3_arcST_pt D x θ]; abel
      have hA := hKt hqK
      have hB := hKs hqK
      simp only [Set.mem_setOf_eq] at hA hB
      rw [hq1, w3bg_det_add_right, w3bg_det_smul_right, w3bg_det_smul_right, w3bg_det_self] at hA hB
      rw [w3bg_det_comm (es D x) (et D x)] at hB
      have hP : 0 < ε * (det (et D x) (es D x) * det (et D x) (es D x)) := mul_pos hε.pos hdd
      have eA : (θ * ε * 0 + (θ - 1) * ε * det (et D x) (es D x)) * det (et D x) (es D x) =
          (θ - 1) * (ε * (det (et D x) (es D x) * det (et D x) (es D x))) := by ring
      have eB : (θ * ε * -det (et D x) (es D x) + (θ - 1) * ε * 0) * det (et D x) (es D x) =
          -θ * (ε * (det (et D x) (es D x) * det (et D x) (es D x))) := by ring
      rw [eA] at hA
      rw [eB] at hB
      nlinarith [hA, hB, hP]


/-- (G) **the missing `hk5` in `D`'s own terms (`arcST`)**: unless the strand before `s` IS the strand after `t`
(the kink at `x`: `⟨s.1, s.2 − 1⟩ = ⟨t.1, t.2 + 1⟩`), the component of `cutStartS` in ANY splice model has at least
five strands.  Proof from the model laws alone: the labels `a − 1, a, a + 1, a + 2, a + 3` of the component carry the
kinds `old ⟨s.1, s.2 − 1⟩, cutStartS, arcST, cutEndT, old ⟨t.1, t.2 + 1⟩` (`kind_pred`, `kind_succ`); `k = 3` would
identify the first with `cutEndT`, `k = 4` the first with the last. -/
theorem w3bg_hk5_arcST_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k := by
  obtain ⟨uIn, huIn⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS :=
    ⟨_, rfl⟩
  rw [← huIn]
  have hkIn : M.kind uIn = StrandKind.cutStartS := by rw [huIn, M.kind_strandOf]
  have hPrev : M.kind ⟨uIn.1, uIn.2 - 1⟩ = StrandKind.old ⟨(sS D x).1, (sS D x).2 - 1⟩ := by
    rw [M.kind_pred, hkIn]; rfl
  have h1 : M.kind ⟨uIn.1, uIn.2 + 1⟩ = StrandKind.arcST := by rw [M.kind_succ, hkIn]; rfl
  have h2 : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = StrandKind.cutEndT := by
    have h : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1⟩).succ := M.kind_succ ⟨uIn.1, uIn.2 + 1⟩
    rw [h, h1]; rfl
  have h3 : M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ = StrandKind.old ⟨(tS D x).1, (tS D x).2 + 1⟩ := by
    have h : M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩).succ :=
      M.kind_succ ⟨uIn.1, uIn.2 + 1 + 1⟩
    rw [h, h2]; rfl
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ (Γ₀.comp uIn.1).k := (Γ₀.comp uIn.1).hk
  rcases (show (Γ₀.comp uIn.1).k = 3 ∨ (Γ₀.comp uIn.1).k = 4 by omega) with hk | hk
  · have hz : ((3 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod (Γ₀.comp uIn.1).k) hk.symm).trans (ZMod.natCast_self _)
    have hdiff : uIn.2 + 1 + 1 - (uIn.2 - 1) = ((3 : ℕ) : ZMod (Γ₀.comp uIn.1).k) := by push_cast; ring
    have e : uIn.2 - 1 = uIn.2 + 1 + 1 := (sub_eq_zero.mp (hdiff.trans hz)).symm
    have : M.kind ⟨uIn.1, uIn.2 - 1⟩ = M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ := by rw [e]
    rw [hPrev, h2] at this
    simp at this
  · have hz : ((4 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod (Γ₀.comp uIn.1).k) hk.symm).trans (ZMod.natCast_self _)
    have hdiff : uIn.2 + 1 + 1 + 1 - (uIn.2 - 1) = ((4 : ℕ) : ZMod (Γ₀.comp uIn.1).k) := by push_cast; ring
    have e : uIn.2 - 1 = uIn.2 + 1 + 1 + 1 := (sub_eq_zero.mp (hdiff.trans hz)).symm
    have : M.kind ⟨uIn.1, uIn.2 - 1⟩ = M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ := by rw [e]
    rw [hPrev, h3] at this
    exact hkink (StrandKind.old.inj this)

/-- (G) the `arcTS` analogue: unless the strand before `t` is the strand after `s`, the component of `cutStartT`
has at least five strands. -/
theorem w3bg_hk5_arcTS_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k := by
  obtain ⟨uIn, huIn⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT :=
    ⟨_, rfl⟩
  rw [← huIn]
  have hkIn : M.kind uIn = StrandKind.cutStartT := by rw [huIn, M.kind_strandOf]
  have hPrev : M.kind ⟨uIn.1, uIn.2 - 1⟩ = StrandKind.old ⟨(tS D x).1, (tS D x).2 - 1⟩ := by
    rw [M.kind_pred, hkIn]; rfl
  have h1 : M.kind ⟨uIn.1, uIn.2 + 1⟩ = StrandKind.arcTS := by rw [M.kind_succ, hkIn]; rfl
  have h2 : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = StrandKind.cutEndS := by
    have h : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1⟩).succ := M.kind_succ ⟨uIn.1, uIn.2 + 1⟩
    rw [h, h1]; rfl
  have h3 : M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ = StrandKind.old ⟨(sS D x).1, (sS D x).2 + 1⟩ := by
    have h : M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩).succ :=
      M.kind_succ ⟨uIn.1, uIn.2 + 1 + 1⟩
    rw [h, h2]; rfl
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ (Γ₀.comp uIn.1).k := (Γ₀.comp uIn.1).hk
  rcases (show (Γ₀.comp uIn.1).k = 3 ∨ (Γ₀.comp uIn.1).k = 4 by omega) with hk | hk
  · have hz : ((3 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod (Γ₀.comp uIn.1).k) hk.symm).trans (ZMod.natCast_self _)
    have hdiff : uIn.2 + 1 + 1 - (uIn.2 - 1) = ((3 : ℕ) : ZMod (Γ₀.comp uIn.1).k) := by push_cast; ring
    have e : uIn.2 - 1 = uIn.2 + 1 + 1 := (sub_eq_zero.mp (hdiff.trans hz)).symm
    have : M.kind ⟨uIn.1, uIn.2 - 1⟩ = M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ := by rw [e]
    rw [hPrev, h2] at this
    simp at this
  · have hz : ((4 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod (Γ₀.comp uIn.1).k) hk.symm).trans (ZMod.natCast_self _)
    have hdiff : uIn.2 + 1 + 1 + 1 - (uIn.2 - 1) = ((4 : ℕ) : ZMod (Γ₀.comp uIn.1).k) := by push_cast; ring
    have e : uIn.2 - 1 = uIn.2 + 1 + 1 + 1 := (sub_eq_zero.mp (hdiff.trans hz)).symm
    have : M.kind ⟨uIn.1, uIn.2 - 1⟩ = M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ := by rw [e]
    rw [hPrev, h3] at this
    exact hkink (StrandKind.old.inj this)

/-- (G) **the corrected `arcST` site in `D`'s terms**: the frozen `w3g_bigonData_smooth_arcST` plus the non-kink
hypothesis `⟨s.1, s.2 − 1⟩ ≠ ⟨t.1, t.2 + 1⟩` (which is exactly what the frozen statement lacks). -/
theorem w3bg_bigonData_smooth_arcST_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} :=
  w3bg_bigonData_smooth_arcST_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (w3bg_hk5_arcST_of_not_kink D x M hkink)

/-- (G) **the corrected `arcTS` site in `D`'s terms**: the frozen `w3g_bigonData_smooth_arcTS` plus the non-kink
hypothesis `⟨t.1, t.2 − 1⟩ ≠ ⟨s.1, s.2 + 1⟩`. -/
theorem w3bg_bigonData_smooth_arcTS_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} :=
  w3bg_bigonData_smooth_arcTS_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (w3bg_hk5_arcTS_of_not_kink D x M hkink)

/-- (G) in the mixed case (`s`, `t` on different components) both non-kink conditions hold trivially, so the
corrected sites need no extra hypothesis there; only the self case (one component split into two) can be a kink. -/
theorem w3bg_not_kink_of_ne_comp (D : Diagram) (x : D.Γ.Crossing) (h : (sS D x).1 ≠ (tS D x).1) :
    (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ ∧
    (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩ :=
  ⟨fun h' => h (Sigma.mk.inj h').1, fun h' => h.symm (Sigma.mk.inj h').1⟩

/-- **(g) sub-leaf — the `j = 2` bigon site on a smoothing output, case `arcST`** (the corner-cut arc on
the bigon side runs `s⁻ → t⁺`: `y` PRECEDES `x` on the over strand `s` and `z` FOLLOWS `x` on the under
strand `t`).  On the switched smoothing `(D^x)^{y−}` the run is the two arc ends `s⁻ = tail arcST`,
`t⁺ = tail cutEndT` (`StrandKind.tail`), the entering edge is `cutStartS` (carrying `y`), the exiting edge
`cutEndT` (carrying `z`), the remote strand is the old strand `g`, and `K = conv{y, s⁻, t⁺, z} ⊆ Δ`.
Sketch: labels of the three consecutive kinds from `SpliceModel.kind_succ` (`cutStartS → arcST → cutEndT`,
no wrap by `cut_val`), `hk` from `5 ≤ k` (the run + three); `run_free`: no crossing on `arcST`
(`eval_arc_mem_ball` + the clearance `r₁`); `no_io`: a crossing of `cutStartS` with `cutEndT` would be a
crossing of `s` with `t` other than `x` inside the triangle corner — excluded by `clear` (closed form);
`same_over` from `hover` through `orig_overStrand₀` (the smoothing pulls the over data back along
`orig`) and the switch at `y₀`; parameters `ty tz tsy tsz` rescaled through `origParam`; `in_iff`,
`out_iff`, `s_iff` from the quadrilateral's sides (`K ⊆ Δ`, `Δ` on one side of `line(s)`, `line(t)`,
`line(g)`; the affine-basis toolkit `gu2_mem_segment_*` of BigonDeletion §2a); `clear`: old kinds from
`clear` (their segments are sub-segments of the old edges), the three other new kinds `cutStartT`,
`arcTS`, `cutEndS` lie in the opposite cone at `x` (`sPlus`, `tMinus` on the far half-edges) and miss
`K ⊆ Δ ∩ {corner (−e_s, +e_t)}` — the cone geometry with `SmallEps.mul_es_lt / mul_et_lt`.  ≈ 1.2k lines. -/
theorem w3g_bigonData_smooth_arcST (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- (W3C assembler) STATEMENT RESTATED (W3C_ASSEMBLY_REPORT.md §2): the Wave-3 skeleton form (with `clear_vertex`,
  -- without `hkink`) is false on a kink (`BigonData.hk : 5 ≤ k`, W3B_G_REPORT.md §2); this is unit G's proved
  -- corrected form `w3bg_bigonData_smooth_arcST_of_not_kink`, which does not consume `clear_vertex`.
  exact w3bg_bigonData_smooth_arcST_of_not_kink D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀
    hy₀ hz₀ hkink

/-- **(g) sub-leaf — the `j = 2` bigon site, case `arcTS`** (the other orientation: `y` FOLLOWS `x` on
`s`, `z` PRECEDES `x` on `t`; the bigon path runs `z → t⁻ → s⁺ → y`, so the ENTERING edge is `cutStartT`
(carrying `z`, which is `B.y`), the run is `t⁻, s⁺`, the exiting edge `cutEndS` (carrying `y`, which is
`B.z`), `K = conv{z, t⁻, s⁺, y}`).  The consumer case-splits on the orientation (PLAN §4.4 (6)); in the two
remaining orientation combinations the oriented smoothing does not cut the triangle's corner at `x` and
NO bigon exists — the realiser must derive `(hys ∧ hzt) ∨ (hys' ∧ hzt')` from the 177 configuration (the
sign table (1c) / the coherent orientation of the triangle's corner at `x`), see the report.  Same
sketch as `w3g_bigonData_smooth_arcST` with `s ↔ t`. -/
theorem w3g_bigonData_smooth_arcTS (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- (W3C assembler) STATEMENT RESTATED as for `arcST` (W3C_ASSEMBLY_REPORT.md §2): unit G's proved corrected form
  -- `w3bg_bigonData_smooth_arcTS_of_not_kink` (non-kink hypothesis on the component of `cutStartT`).
  exact w3bg_bigonData_smooth_arcTS_of_not_kink D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀
    hy₀ hz₀ hkink

/-- `w3bh_` helper: membership of `crossingOf v` in an occurrence-defined crossing set. -/
theorem w3bh_crossingOf_mem_setOf (ρ : Record) (P : ρ.M → Prop) (v : ρ.M) :
    ρ.crossingOf v ∈ {c : ρ.Crossing | ∀ w ∈ c.1, P w} ↔ P v ∧ P (ρ.pair v) := by
  show (∀ w ∈ ({v, ρ.pair v} : Finset ρ.M), P w) ↔ P v ∧ P (ρ.pair v)
  simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]

/-- `w3bh_` helper: two occurrences of a diagram name the same record crossing iff they lie over the
same crossing. -/
theorem w3bh_record_crossingOf_eq_iff (D : Diagram) (v w : D.Γ.Visit) :
    D.record.crossingOf v = D.record.crossingOf w ↔ v.1 = w.1 := by
  rw [Record.crossingOf_eq_iff]
  exact D.mem_pair_twin_iff w v

/-- `w3bh_` helper: a product of two commuting involutions is an involution. -/
theorem w3bh_invol_mul {G : Type*} [Group G] {f g : G} (hf : f * f = 1) (hg : g * g = 1)
    (hc : Commute f g) : (f * g) * (f * g) = 1 := by
  calc (f * g) * (f * g) = f * (g * f) * g := by simp only [mul_assoc]
    _ = f * (f * g) * g := by rw [hc.eq]
    _ = (f * f) * (g * g) := by simp only [mul_assoc]
    _ = 1 := by rw [hf, hg, one_mul]

/-- `w3bh_` helper: two swaps on disjoint pairs are disjoint permutations. -/
theorem w3bh_swap_disjoint {α : Type*} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).Disjoint (Equiv.swap c d) := by
  intro x
  by_cases hxa : x = a
  · right; subst hxa; exact Equiv.swap_apply_of_ne_of_ne hac had
  by_cases hxb : x = b
  · right; subst hxb; exact Equiv.swap_apply_of_ne_of_ne hbc hbd
  · left; exact Equiv.swap_apply_of_ne_of_ne hxa hxb

/-- `w3bh_` helper: the twist `σ = (a₁ a₂)(b₁ b₂)(c₁ c₂)` on six distinct points is an involution. -/
theorem w3bh_swap3_sq {α : Type*} [DecidableEq α] (a₁ a₂ b₁ b₂ c₁ c₂ : α)
    (h13 : a₁ ≠ b₁) (h14 : a₁ ≠ b₂) (h23 : a₂ ≠ b₁) (h24 : a₂ ≠ b₂)
    (h15 : a₁ ≠ c₁) (h16 : a₁ ≠ c₂) (h25 : a₂ ≠ c₁) (h26 : a₂ ≠ c₂)
    (h35 : b₁ ≠ c₁) (h36 : b₁ ≠ c₂) (h45 : b₂ ≠ c₁) (h46 : b₂ ≠ c₂) :
    (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) *
      (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) = 1 := by
  have hBC : (Equiv.swap b₁ b₂).Disjoint (Equiv.swap c₁ c₂) := w3bh_swap_disjoint h35 h36 h45 h46
  have hAB : (Equiv.swap a₁ a₂).Disjoint (Equiv.swap b₁ b₂) := w3bh_swap_disjoint h13 h14 h23 h24
  have hAC : (Equiv.swap a₁ a₂).Disjoint (Equiv.swap c₁ c₂) := w3bh_swap_disjoint h15 h16 h25 h26
  apply w3bh_invol_mul (Equiv.swap_mul_self _ _)
  · exact w3bh_invol_mul (Equiv.swap_mul_self _ _) (Equiv.swap_mul_self _ _) hBC.commute
  · exact (hAB.mul_right hAC).commute

theorem w3bh_swap3_apply_apply {α : Type*} [DecidableEq α] (a₁ a₂ b₁ b₂ c₁ c₂ : α)
    (h13 : a₁ ≠ b₁) (h14 : a₁ ≠ b₂) (h23 : a₂ ≠ b₁) (h24 : a₂ ≠ b₂)
    (h15 : a₁ ≠ c₁) (h16 : a₁ ≠ c₂) (h25 : a₂ ≠ c₁) (h26 : a₂ ≠ c₂)
    (h35 : b₁ ≠ c₁) (h36 : b₁ ≠ c₂) (h45 : b₂ ≠ c₁) (h46 : b₂ ≠ c₂) (v : α) :
    (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) = v := by
  have h := w3bh_swap3_sq a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  have := congrArg (fun σ : Equiv.Perm α => σ v) h
  simpa [Equiv.Perm.mul_apply] using this

/-- `w3bh_` helper: on a one-component diagram every two occurrences share the component. -/
theorem w3bh_compOf_eq_of_one (D : Diagram) (h1 : D.componentCount = 1) (v w : D.Γ.Visit) :
    D.compOf v = D.compOf w := by
  have hc : D.Γ.c = 1 := h1
  apply Fin.ext
  have := (D.compOf v).isLt
  have := (D.compOf w).isLt
  omega


/-- `w3bh_` helper: an occurrence differs from both occurrences of `a` iff it lies over another crossing. -/
theorem w3bh_ne_ne_twin_iff (D : Diagram) (a w : D.Γ.Visit) :
    (w ≠ a ∧ w ≠ D.twin a) ↔ w.1 ≠ a.1 := by
  constructor
  · rintro ⟨h1, h2⟩ h
    rcases D.eq_or_eq_twin a w h with h' | h'
    · exact h1 h'
    · exact h2 h'
  · intro h
    exact ⟨fun h' => h (congrArg (fun w : D.Γ.Visit => w.1) h'),
      fun h' => h ((congrArg (fun w : D.Γ.Visit => w.1) h').trans (D.twin_fst a))⟩

/-- `w3bh_` helper: a twin-compatible bijection preserves "same crossing". -/
theorem w3bh_fst_eq_iff_of_twin {D D' : Diagram} (Ψ : D.Γ.Visit ≃ D'.Γ.Visit)
    (htw : ∀ v, Ψ (D.twin v) = D'.twin (Ψ v)) (u v : D.Γ.Visit) :
    (Ψ u).1 = (Ψ v).1 ↔ u.1 = v.1 := by
  constructor
  · intro h
    rcases D'.eq_or_eq_twin (Ψ v) (Ψ u) h with h' | h'
    · rw [Ψ.injective h']
    · rw [← htw, Ψ.apply_eq_iff_eq] at h'
      exact (congrArg (fun w : D.Γ.Visit => w.1) h').trans (D.twin_fst v)
  · intro h
    rcases D.eq_or_eq_twin v u h with h' | h'
    · rw [h']
    · rw [h', htw]
      exact D'.twin_fst (Ψ v)

/-- `w3bh_` helper: `ρ.pair u ≠ a ↔ u ≠ b` when `ρ.pair a = b` (and symmetrically). -/
theorem w3bh_pair_ne_iff (ρ : Record) {a b : ρ.M} (h : ρ.pair a = b) (u : ρ.M) :
    (ρ.pair u = a ↔ u = b) ∧ (ρ.pair u = b ↔ u = a) := by
  constructor
  · rw [ρ.pair_eq_iff, h]
  · rw [ρ.pair_eq_iff, ← h, ρ.pair_invol]

/-- `w3bh_` helper: the retained predicate of the `{y, z}`-deletion on `ρ.smooth a₁`, read on the
underlying occurrence (the four deleted occurrences form a pair-closed set). -/
theorem w3bh_crossKeep_iff (ρ : Record) (a₁ a₂ b₂ c₁ c₂ : ρ.M) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (w : (ρ.smooth a₁).M) :
    (ρ.smooth a₁).CrossKeep {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂} w ↔
      (w.1 ≠ a₂ ∧ w.1 ≠ c₁ ∧ w.1 ≠ b₂ ∧ w.1 ≠ c₂) := by
  show (ρ.smooth a₁).crossingOf w ∈ {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂} ↔ _
  rw [w3bh_crossingOf_mem_setOf]
  show (w.1 ≠ a₂ ∧ w.1 ≠ c₁ ∧ w.1 ≠ b₂ ∧ w.1 ≠ c₂) ∧
    (ρ.pair w.1 ≠ a₂ ∧ ρ.pair w.1 ≠ c₁ ∧ ρ.pair w.1 ≠ b₂ ∧ ρ.pair w.1 ≠ c₂) ↔ _
  have e := w3bh_pair_ne_iff ρ hy w.1
  have f := w3bh_pair_ne_iff ρ hz w.1
  simp only [Ne, e.1, e.2, f.1, f.2]
  tauto


/-- `w3bh_` helper: a bijection carries a transposition to the transposition of the images. -/
theorem w3bh_map_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (Φ : α ≃ β) (a b u : α) :
    Φ (Equiv.swap a b u) = Equiv.swap (Φ a) (Φ b) (Φ u) := by
  by_cases h1 : u = a
  · subst h1; rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  by_cases h2 : u = b
  · subst h2; rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
      Equiv.swap_apply_of_ne_of_ne (Φ.injective.ne h1) (Φ.injective.ne h2)]

/-- `w3bh_` helper: a `k`-step chain (intermediate points outside `p`, end point in `p`) determines the first return. -/
theorem w3bh_fr_chain {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (m : {m // p m}) (k : ℕ) (hk : 0 < k) (hmid : ∀ j, 0 < j → j < k → ¬ p ((f ^ j) m.1))
    (hend : p ((f ^ k) m.1)) : (firstReturn f p m).1 = (f ^ k) m.1 := by
  have h : returnTime f p m.1 m.2 = k :=
    (returnTime_eq_iff f p m.1 m.2).mpr ⟨⟨hk, hend⟩, fun j hj hj' => hmid j hj'.1 hj hj'.2⟩
  rw [firstReturn_apply, h]

theorem w3bh_pow2 {α : Type*} (f : Equiv.Perm α) (u : α) : (f ^ 2) u = f (f u) := by
  rw [pow_two, Equiv.Perm.mul_apply]
theorem w3bh_pow3 {α : Type*} (f : Equiv.Perm α) (u : α) : (f ^ 3) u = f (f (f u)) := by
  rw [pow_succ, Equiv.Perm.mul_apply, w3bh_pow2]
theorem w3bh_pow4 {α : Type*} (f : Equiv.Perm α) (u : α) : (f ^ 4) u = f (f (f (f u))) := by
  rw [pow_succ, Equiv.Perm.mul_apply, w3bh_pow3]

/-- `w3bh_` helper: on a one-circle record, a two-cycle `x ↦ y ↦ x` of the successor leaves no room for a third occurrence. -/
theorem w3bh_no_two_cycle (ρ : Record) (hρ : ρ.componentCount = 1) (x y v : ρ.M)
    (hxy : ρ.succ x = y) (hyx : ρ.succ y = x) (hv : v ≠ x) (hv' : v ≠ y) : False := by
  obtain ⟨n, hn⟩ := (ρ.sameCycle_of_one_circle hρ x v).exists_nat_pow_eq
  have key : ∀ n : ℕ, (ρ.succ ^ n) x = x ∨ (ρ.succ ^ n) x = y := by
    intro n
    induction n with
    | zero => left; rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h
      · right; rw [h, hxy]
      · left; rw [h, hyx]
  rcases key n with h | h
  · exact hv (hn.symm.trans h)
  · exact hv' (hn.symm.trans h)

/-- `w3bh_` helper: on a one-circle record the successor has no fixed point next to another occurrence. -/
theorem w3bh_no_fixed (ρ : Record) (hρ : ρ.componentCount = 1) (x v : ρ.M)
    (hx : ρ.succ x = x) (hv : v ≠ x) : False := by
  obtain ⟨n, hn⟩ := (ρ.sameCycle_of_one_circle hρ x v).exists_nat_pow_eq
  have key : ∀ n : ℕ, (ρ.succ ^ n) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hx]
  exact hv (hn.symm.trans (key n))

/-- `w3bh_` helper: `s u ≠ t` when `s w = t` and `u ≠ w`. -/
theorem w3bh_succ_ne (ρ : Record) {u w t : ρ.M} (hw : ρ.succ w = t) (hne : u ≠ w) : ρ.succ u ≠ t :=
  fun h => hne (ρ.succ.injective (h.trans hw.symm))

/-- **`w3bh_` the pure core on the four `x, y, z`-strand occurrences** (`c₁, c₂` peeled off): for a one-circle
record and four distinct occurrences with `a₁ ~ a₂`, `b₁ ~ b₂` adjacent, the first returns of `s ∘ (a₁ b₁)` and
`s ∘ (a₂ b₂)` to the complement of `{a₁, b₁, a₂, b₂}` agree.  PROVED (Unit H, 2026-09-15) by the chase: if `s v` is
retained both return `s v`; otherwise `s v` is an entry of the block and the two chains (`w3bh_fr_chain`, 2–4 steps)
end at the same exit, which is retained by predecessor uniqueness (`w3bh_succ_ne`) and one circle (`w3bh_no_two_cycle`,
`w3bh_no_fixed`): pattern `s a₁ = a₂, s b₁ = b₂`: entry `a₁`: `a₁ ↦ b₂ ↦ s b₂` vs `a₁ ↦ a₂ ↦ s b₂`, entry `b₁`:
`b₁ ↦ a₂ ↦ s a₂` vs `b₁ ↦ b₂ ↦ s a₂`; pattern `s a₁ = a₂, s b₂ = b₁`: entry `a₁`: `a₁ ↦ s b₁` vs `a₁ ↦ a₂ ↦ b₁ ↦ s b₁`,
entry `b₂`: `b₂ ↦ b₁ ↦ a₂ ↦ s a₂` vs `b₂ ↦ s a₂`; the two mirror patterns likewise.  Brute-force checked for all
one-circle records with `≤ 10` occurrences (`W3B_H_brute.py`).  `w3bh_core_pure` is derived from it. -/
theorem w3bh_core_pure₀ (ρ : Record) (hρ : ρ.componentCount = 1) (a₁ a₂ b₁ b₂ : ρ.M)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ b₁) (h14 : a₁ ≠ b₂) (h23 : a₂ ≠ b₁) (h24 : a₂ ≠ b₂) (h34 : b₁ ≠ b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (v : ρ.M) (hv : v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ b₂) :
    (firstReturn (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ⟨v, hv⟩).1 =
      (firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ⟨v, hv⟩).1 := by
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  -- evaluations of the two reconnections
  have e1 : ∀ u, u ≠ a₁ → u ≠ b₁ → (ρ.succ * Equiv.swap a₁ b₁) u = ρ.succ u := fun u h1 h2 => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e1a : (ρ.succ * Equiv.swap a₁ b₁) a₁ = ρ.succ b₁ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have e1b : (ρ.succ * Equiv.swap a₁ b₁) b₁ = ρ.succ a₁ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have e2 : ∀ u, u ≠ a₂ → u ≠ b₂ → (ρ.succ * Equiv.swap a₂ b₂) u = ρ.succ u := fun u h1 h2 => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e2a : (ρ.succ * Equiv.swap a₂ b₂) a₂ = ρ.succ b₂ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have e2b : (ρ.succ * Equiv.swap a₂ b₂) b₂ = ρ.succ a₂ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have hf1v : (ρ.succ * Equiv.swap a₁ b₁) v = ρ.succ v := e1 v hv1 hv2
  have hf2v : (ρ.succ * Equiv.swap a₂ b₂) v = ρ.succ v := e2 v hv3 hv4
  -- the four local points are not retained
  have nA₁ : ¬ (a₁ ≠ a₁ ∧ a₁ ≠ b₁ ∧ a₁ ≠ a₂ ∧ a₁ ≠ b₂) := fun h => h.1 rfl
  have nB₁ : ¬ (b₁ ≠ a₁ ∧ b₁ ≠ b₁ ∧ b₁ ≠ a₂ ∧ b₁ ≠ b₂) := fun h => h.2.1 rfl
  have nA₂ : ¬ (a₂ ≠ a₁ ∧ a₂ ≠ b₁ ∧ a₂ ≠ a₂ ∧ a₂ ≠ b₂) := fun h => h.2.2.1 rfl
  have nB₂ : ¬ (b₂ ≠ a₁ ∧ b₂ ≠ b₁ ∧ b₂ ≠ a₂ ∧ b₂ ≠ b₂) := fun h => h.2.2.2 rfl
  by_cases hw : ρ.succ v ≠ a₁ ∧ ρ.succ v ≠ b₁ ∧ ρ.succ v ≠ a₂ ∧ ρ.succ v ≠ b₂
  · -- the successor of `v` is retained: both first returns are `s v`
    rw [firstReturn_apply_of_mem _ _ ⟨v, ⟨hv1, hv2, hv3, hv4⟩⟩ (by rw [hf1v]; exact hw),
      firstReturn_apply_of_mem _ _ ⟨v, ⟨hv1, hv2, hv3, hv4⟩⟩ (by rw [hf2v]; exact hw)]
    exact hf1v.trans hf2v.symm
  · -- `s v` is one of the four local points: chase through the block
    have hw' : ρ.succ v = a₁ ∨ ρ.succ v = b₁ ∨ ρ.succ v = a₂ ∨ ρ.succ v = b₂ := by
      by_contra hc
      push Not at hc
      exact hw ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
    rcases hadj_e with hE | hE <;> rcases hadj_f with hF | hF <;>
      rcases hw' with hw | hw | hw | hw
    -- pattern E1 F1 (s a₁ = a₂, s b₁ = b₂)
    · -- entry a₁: f₁ : v a₁ b₂ (s b₂); f₂ : v a₁ a₂ (s b₂)
      have ex : ρ.succ b₂ ≠ a₁ ∧ ρ.succ b₂ ≠ b₁ ∧ ρ.succ b₂ ≠ a₂ ∧ ρ.succ b₂ ≠ b₂ :=
        ⟨w3bh_succ_ne ρ hw (Ne.symm hv4), fun h => w3bh_no_two_cycle ρ hρ b₁ b₂ v hF h hv2 hv4,
         w3bh_succ_ne ρ hE (Ne.symm h14), fun h => w3bh_no_fixed ρ hρ b₂ v h hv4⟩
      rw [w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nA₁
          · rw [w3bh_pow2, hf1v, hw, e1a, hF]; exact nB₂)
        (by rw [w3bh_pow3, hf1v, hw, e1a, hF, e1 b₂ (Ne.symm h14) (Ne.symm h34)]; exact ex),
        w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nA₁
          · rw [w3bh_pow2, hf2v, hw, e2 a₁ h12 h14, hE]; exact nA₂)
        (by rw [w3bh_pow3, hf2v, hw, e2 a₁ h12 h14, hE, e2a]; exact ex)]
      rw [w3bh_pow3, w3bh_pow3, hf1v, hf2v, hw, e1a, hF, e1 b₂ (Ne.symm h14) (Ne.symm h34),
        e2 a₁ h12 h14, hE, e2a]
    · -- entry b₁: f₁ : v b₁ a₂ (s a₂); f₂ : v b₁ b₂ (s a₂)
      have ex : ρ.succ a₂ ≠ a₁ ∧ ρ.succ a₂ ≠ b₁ ∧ ρ.succ a₂ ≠ a₂ ∧ ρ.succ a₂ ≠ b₂ :=
        ⟨fun h => w3bh_no_two_cycle ρ hρ a₁ a₂ v hE h hv1 hv3, w3bh_succ_ne ρ hw (Ne.symm hv3),
         fun h => w3bh_no_fixed ρ hρ a₂ v h hv3, w3bh_succ_ne ρ hF h23⟩
      rw [w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nB₁
          · rw [w3bh_pow2, hf1v, hw, e1b, hE]; exact nA₂)
        (by rw [w3bh_pow3, hf1v, hw, e1b, hE, e1 a₂ (Ne.symm h12) h23]; exact ex),
        w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nB₁
          · rw [w3bh_pow2, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF]; exact nB₂)
        (by rw [w3bh_pow3, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF, e2b]; exact ex)]
      rw [w3bh_pow3, w3bh_pow3, hf1v, hf2v, hw, e1b, hE, e1 a₂ (Ne.symm h12) h23,
        e2 b₁ (Ne.symm h23) h34, hF, e2b]
    · exact absurd (ρ.succ.injective (hw.trans hE.symm)) hv1
    · exact absurd (ρ.succ.injective (hw.trans hF.symm)) hv2
    -- pattern E1 F2 (s a₁ = a₂, s b₂ = b₁)
    · -- entry a₁: f₁ : v a₁ (s b₁); f₂ : v a₁ a₂ b₁ (s b₁)
      have ex : ρ.succ b₁ ≠ a₁ ∧ ρ.succ b₁ ≠ b₁ ∧ ρ.succ b₁ ≠ a₂ ∧ ρ.succ b₁ ≠ b₂ :=
        ⟨w3bh_succ_ne ρ hw (Ne.symm hv2), fun h => w3bh_no_fixed ρ hρ b₁ v h hv2,
         w3bh_succ_ne ρ hE (Ne.symm h13), fun h => w3bh_no_two_cycle ρ hρ b₂ b₁ v hF h hv4 hv2⟩
      rw [w3bh_fr_chain _ _ _ 2 (by norm_num) (by
          intro j hj hjk; interval_cases j
          rw [pow_one, hf1v, hw]; exact nA₁)
        (by rw [w3bh_pow2, hf1v, hw, e1a]; exact ex),
        w3bh_fr_chain _ _ _ 4 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nA₁
          · rw [w3bh_pow2, hf2v, hw, e2 a₁ h12 h14, hE]; exact nA₂
          · rw [w3bh_pow3, hf2v, hw, e2 a₁ h12 h14, hE, e2a, hF]; exact nB₁)
        (by rw [w3bh_pow4, hf2v, hw, e2 a₁ h12 h14, hE, e2a, hF, e2 b₁ (Ne.symm h23) h34]; exact ex)]
      rw [w3bh_pow2, w3bh_pow4, hf1v, hf2v, hw, e1a, e2 a₁ h12 h14, hE, e2a, hF, e2 b₁ (Ne.symm h23) h34]
    · exact absurd (ρ.succ.injective (hw.trans hF.symm)) hv4
    · exact absurd (ρ.succ.injective (hw.trans hE.symm)) hv1
    · -- entry b₂: f₁ : v b₂ b₁ a₂ (s a₂); f₂ : v b₂ (s a₂)
      have ex : ρ.succ a₂ ≠ a₁ ∧ ρ.succ a₂ ≠ b₁ ∧ ρ.succ a₂ ≠ a₂ ∧ ρ.succ a₂ ≠ b₂ :=
        ⟨fun h => w3bh_no_two_cycle ρ hρ a₁ a₂ v hE h hv1 hv3, w3bh_succ_ne ρ hF h24,
         fun h => w3bh_no_fixed ρ hρ a₂ v h hv3, w3bh_succ_ne ρ hw (Ne.symm hv3)⟩
      rw [w3bh_fr_chain _ _ _ 4 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nB₂
          · rw [w3bh_pow2, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF]; exact nB₁
          · rw [w3bh_pow3, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b, hE]; exact nA₂)
        (by rw [w3bh_pow4, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b, hE,
              e1 a₂ (Ne.symm h12) h23]; exact ex),
        w3bh_fr_chain _ _ _ 2 (by norm_num) (by
          intro j hj hjk; interval_cases j
          rw [pow_one, hf2v, hw]; exact nB₂)
        (by rw [w3bh_pow2, hf2v, hw, e2b]; exact ex)]
      rw [w3bh_pow4, w3bh_pow2, hf1v, hf2v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b, hE,
        e1 a₂ (Ne.symm h12) h23, e2b]
    -- pattern E2 F1 (s a₂ = a₁, s b₁ = b₂)
    · exact absurd (ρ.succ.injective (hw.trans hE.symm)) hv3
    · -- entry b₁: f₁ : v b₁ (s a₁); f₂ : v b₁ b₂ a₁ (s a₁)
      have ex : ρ.succ a₁ ≠ a₁ ∧ ρ.succ a₁ ≠ b₁ ∧ ρ.succ a₁ ≠ a₂ ∧ ρ.succ a₁ ≠ b₂ :=
        ⟨fun h => w3bh_no_fixed ρ hρ a₁ v h hv1, w3bh_succ_ne ρ hw (Ne.symm hv1),
         fun h => w3bh_no_two_cycle ρ hρ a₂ a₁ v hE h hv3 hv1, w3bh_succ_ne ρ hF h13⟩
      rw [w3bh_fr_chain _ _ _ 2 (by norm_num) (by
          intro j hj hjk; interval_cases j
          rw [pow_one, hf1v, hw]; exact nB₁)
        (by rw [w3bh_pow2, hf1v, hw, e1b]; exact ex),
        w3bh_fr_chain _ _ _ 4 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nB₁
          · rw [w3bh_pow2, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF]; exact nB₂
          · rw [w3bh_pow3, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF, e2b, hE]; exact nA₁)
        (by rw [w3bh_pow4, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF, e2b, hE, e2 a₁ h12 h14]; exact ex)]
      rw [w3bh_pow2, w3bh_pow4, hf1v, hf2v, hw, e1b, e2 b₁ (Ne.symm h23) h34, hF, e2b, hE, e2 a₁ h12 h14]
    · -- entry a₂: f₁ : v a₂ a₁ b₂ (s b₂); f₂ : v a₂ (s b₂)
      have ex : ρ.succ b₂ ≠ a₁ ∧ ρ.succ b₂ ≠ b₁ ∧ ρ.succ b₂ ≠ a₂ ∧ ρ.succ b₂ ≠ b₂ :=
        ⟨w3bh_succ_ne ρ hE (Ne.symm h24), fun h => w3bh_no_two_cycle ρ hρ b₁ b₂ v hF h hv2 hv4,
         w3bh_succ_ne ρ hw (Ne.symm hv4), fun h => w3bh_no_fixed ρ hρ b₂ v h hv4⟩
      rw [w3bh_fr_chain _ _ _ 4 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nA₂
          · rw [w3bh_pow2, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE]; exact nA₁
          · rw [w3bh_pow3, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a, hF]; exact nB₂)
        (by rw [w3bh_pow4, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a, hF,
              e1 b₂ (Ne.symm h14) (Ne.symm h34)]; exact ex),
        w3bh_fr_chain _ _ _ 2 (by norm_num) (by
          intro j hj hjk; interval_cases j
          rw [pow_one, hf2v, hw]; exact nA₂)
        (by rw [w3bh_pow2, hf2v, hw, e2a]; exact ex)]
      rw [w3bh_pow4, w3bh_pow2, hf1v, hf2v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a, hF,
        e1 b₂ (Ne.symm h14) (Ne.symm h34), e2a]
    · exact absurd (ρ.succ.injective (hw.trans hF.symm)) hv2
    -- pattern E2 F2 (s a₂ = a₁, s b₂ = b₁)
    · exact absurd (ρ.succ.injective (hw.trans hE.symm)) hv3
    · exact absurd (ρ.succ.injective (hw.trans hF.symm)) hv4
    · -- entry a₂: f₁ : v a₂ a₁ (s b₁); f₂ : v a₂ b₁ (s b₁)
      have ex : ρ.succ b₁ ≠ a₁ ∧ ρ.succ b₁ ≠ b₁ ∧ ρ.succ b₁ ≠ a₂ ∧ ρ.succ b₁ ≠ b₂ :=
        ⟨w3bh_succ_ne ρ hE (Ne.symm h23), fun h => w3bh_no_fixed ρ hρ b₁ v h hv2,
         w3bh_succ_ne ρ hw (Ne.symm hv2), fun h => w3bh_no_two_cycle ρ hρ b₂ b₁ v hF h hv4 hv2⟩
      rw [w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nA₂
          · rw [w3bh_pow2, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE]; exact nA₁)
        (by rw [w3bh_pow3, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a]; exact ex),
        w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nA₂
          · rw [w3bh_pow2, hf2v, hw, e2a, hF]; exact nB₁)
        (by rw [w3bh_pow3, hf2v, hw, e2a, hF, e2 b₁ (Ne.symm h23) h34]; exact ex)]
      rw [w3bh_pow3, w3bh_pow3, hf1v, hf2v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a, e2a, hF,
        e2 b₁ (Ne.symm h23) h34]
    · -- entry b₂: f₁ : v b₂ b₁ (s a₁); f₂ : v b₂ a₁ (s a₁)
      have ex : ρ.succ a₁ ≠ a₁ ∧ ρ.succ a₁ ≠ b₁ ∧ ρ.succ a₁ ≠ a₂ ∧ ρ.succ a₁ ≠ b₂ :=
        ⟨fun h => w3bh_no_fixed ρ hρ a₁ v h hv1, w3bh_succ_ne ρ hF h14,
         fun h => w3bh_no_two_cycle ρ hρ a₂ a₁ v hE h hv3 hv1, w3bh_succ_ne ρ hw (Ne.symm hv1)⟩
      rw [w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nB₂
          · rw [w3bh_pow2, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF]; exact nB₁)
        (by rw [w3bh_pow3, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b]; exact ex),
        w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nB₂
          · rw [w3bh_pow2, hf2v, hw, e2b, hE]; exact nA₁)
        (by rw [w3bh_pow3, hf2v, hw, e2b, hE, e2 a₁ h12 h14]; exact ex)]
      rw [w3bh_pow3, w3bh_pow3, hf1v, hf2v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b, e2b, hE,
        e2 a₁ h12 h14]


/-- **`w3bh_` THE pure core (Φ-free)**: on a one-circle record with the six local occurrences
`a₁,b₁` (of `x`), `a₂,c₁` (of `y`), `b₂,c₂` (of `z`), adjacent in pairs on the three strands, the first
return to the non-local occurrences of the smoothing reconnection `s ∘ (a₁ b₁)` equals that of the
reconnection `s ∘ (a₂ b₂)`.  Cyclic-word check (`(a₁ A b₁ B) ↦ (a₁ B)(b₁ A)` and `(a₂ B')(b₂ A')`): with
`s a₁ = a₂, s b₁ = b₂`: `A = a₂ A''`, `A' = A'' b₁`, `B = b₂ B''`, `B' = B'' a₁`, so the cycles are
`(a₁ b₂ B'')(b₁ a₂ A'')` versus `(a₂ B'' a₁)(b₂ A'' b₁)` — the same cyclic order on `M ∖ L`; the other
three `e/f` patterns likewise (`s a₂ = a₁, s b₁ = b₂`: `(a₁ b₂ B' a₂)(b₁ A)` vs `(a₂ B')(b₂ a₁ A b₁)`;
`s a₁ = a₂, s b₂ = b₁`: `(a₁ B)(b₁ a₂ A' b₂)` vs `(a₂ b₁ B a₁)(b₂ A')`; `s a₂ = a₁, s b₂ = b₁`:
`(a₁ B'' a₂)(b₁ A'' b₂)` vs `(a₂ b₁ B'')(b₂ a₁ A'')`).  The `g`-strand orientation and any adjacency
between the blocks are irrelevant.  OPEN (Unit H, 2026-09-15): stated, not proved; the two consumers are
`w3bh_core_firstReturn` (proved from it) and, in the same cyclic-word terms, `w3bh_core_comp`. -/
theorem w3bh_core_pure (ρ : Record) (hρ : ρ.componentCount = 1) (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁)
    (v : ρ.M) (hv : v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) :
    (firstReturn (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 =
      (firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 := by
  -- the six local occurrences are distinct
  have hne : ∀ u w : ρ.M, ρ.crossingOf u ≠ ρ.crossingOf w → u ≠ w := fun u w h h' => h (h' ▸ rfl)
  have hcb₁ : ρ.crossingOf b₁ = ρ.crossingOf a₁ := by rw [← hx, ρ.crossingOf_pair]
  have h13 : a₁ ≠ b₁ := by rw [← hx]; exact ρ.ne_pair a₁
  have h12 : a₁ ≠ a₂ := hne _ _ hxy
  have h14 : a₁ ≠ b₂ := hne _ _ hxz
  have h24 : a₂ ≠ b₂ := hne _ _ hyz
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [hcb₁]; exact hxy.symm)
  have h34 : b₁ ≠ b₂ := hne _ _ (by rw [hcb₁]; exact hxz)
  -- peel off `c₁, c₂`: the first return to `N` is the first return of the first return to `P`
  have hNsplit : ∀ u : ρ.M, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u ↔ (fun u => (u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ∧ (u ≠ c₁ ∧ u ≠ c₂)) u := by
    intro u; simp only; tauto
  have hv₀ : (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) v := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.2.1⟩
  have key : firstReturn (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) = firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) := by
    ext m
    exact w3bh_core_pure₀ ρ hρ a₁ a₂ b₁ b₂ h12 h13 h14 h23 h24 h34 hadj_e hadj_f m.1 m.2
  have step : ∀ f : Equiv.Perm ρ.M, (firstReturn f (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 =
      ((firstReturn (firstReturn f (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂)) (fun m => (fun u => u ≠ c₁ ∧ u ≠ c₂) m.1)) ⟨⟨v, hv₀⟩, hv.2.2.2.1, hv.2.2.2.2.2⟩).1.1 := by
    intro f
    rw [firstReturn_congr_pred f (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) (fun u => (u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ∧ (u ≠ c₁ ∧ u ≠ c₂)) hNsplit ⟨v, hv⟩,
      firstReturn_firstReturn f (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) (fun u => u ≠ c₁ ∧ u ≠ c₂) ⟨⟨v, hv₀⟩, hv.2.2.2.1, hv.2.2.2.2.2⟩]
  rw [step, step, key]


/-- **`w3bh_` core sub-lemma (a), the twisted first return** — THE content of `w3h_record_core`: on the
retained (non-local) occurrences the first return of the reconnected successor `s ∘ (a₁ b₁)` to the
non-local set is carried by `Φ` to the first return of `s' ∘ (Φ a₁, Φ b₁)`.  Since
`s' (Φ v) = Φ (σ (s (σ v)))` this is the pure statement on `ρ`
`firstReturn (s ∘ (a₁ b₁)) N v = firstReturn (s ∘ (a₂ b₂)) N v` (conjugate by `σ`, which fixes the
non-local set pointwise): the smoothing at `x` and the "smoothing" `a₂ ↔ b₂` induce the same
first return on `M ∖ {six local occurrences}`, in each of the four `e/f` orientation patterns (cyclic-word
check: `(a₁ A b₁ B) ↦ (a₁ B)(b₁ A)` versus `(a₂ B')(b₂ A')`, where `A = a₂ A''`, `A' = A'' b₁` when `x`
precedes on both strands, etc.).  The `g`-strand orientation is irrelevant (its two occurrences are
deleted points inside `A` or `B`).  OPEN (Unit H, 2026-09-15): stated, not proved. -/
theorem w3bh_core_firstReturn (ρ ρ' : Record) (hρ : ρ.componentCount = 1) (Φ : ρ.M ≃ ρ'.M)
    (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁)
    (hpair : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v))
    (hsucc : ∀ v, Φ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (ρ.succ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) = ρ'.succ (Φ v))
    (v : ρ.M) (hv : v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂)
    (hv' : Φ v ≠ Φ a₁ ∧ Φ v ≠ Φ b₁ ∧ Φ v ≠ Φ a₂ ∧ Φ v ≠ Φ c₁ ∧ Φ v ≠ Φ b₂ ∧ Φ v ≠ Φ c₂) :
    Φ (firstReturn (ρ.reconnect a₁)
        (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 =
      (firstReturn (ρ'.reconnect (Φ a₁))
        (fun u => u ≠ Φ a₁ ∧ u ≠ Φ b₁ ∧ u ≠ Φ a₂ ∧ u ≠ Φ c₁ ∧ u ≠ Φ b₂ ∧ u ≠ Φ c₂) ⟨Φ v, hv'⟩).1 := by
  -- the six local occurrences are distinct
  have hne : ∀ u w : ρ.M, ρ.crossingOf u ≠ ρ.crossingOf w → u ≠ w := fun u w h h' => h (h' ▸ rfl)
  have hcb₁ : ρ.crossingOf b₁ = ρ.crossingOf a₁ := by rw [← hx, ρ.crossingOf_pair]
  have hcc₁ : ρ.crossingOf c₁ = ρ.crossingOf a₂ := by rw [← hy, ρ.crossingOf_pair]
  have hcc₂ : ρ.crossingOf c₂ = ρ.crossingOf b₂ := by rw [← hz, ρ.crossingOf_pair]
  have h13 : a₁ ≠ b₁ := by rw [← hx]; exact ρ.ne_pair a₁
  have h25 : a₂ ≠ c₁ := by rw [← hy]; exact ρ.ne_pair a₂
  have h46 : b₂ ≠ c₂ := by rw [← hz]; exact ρ.ne_pair b₂
  have h14 : a₁ ≠ b₂ := hne _ _ hxz
  have h24 : a₂ ≠ b₂ := hne _ _ hyz
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [hcc₁]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [hcc₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [hcb₁]; exact hxy.symm)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [hcc₂]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hcb₁, hcc₁]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hcb₁, hcc₂]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hcc₁]; exact hyz.symm)
  set σ : Equiv.Perm ρ.M := Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂) with hσ
  have hσσ : ∀ u, σ (σ u) = u :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  have hσa₁ : σ a₁ = a₂ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h15 h16,
      Equiv.swap_apply_of_ne_of_ne h13 h14, Equiv.swap_apply_left]
  have hσb₁ : σ b₁ = b₂ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h35 h36,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h14.symm h24.symm]
  -- `σ` fixes the non-local occurrences, and the non-local set is `σ`-invariant
  have hσfix : ∀ u, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u → σ u = u := by
    intro u hu
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h4 h6,
      Equiv.swap_apply_of_ne_of_ne h2 h5, Equiv.swap_apply_of_ne_of_ne h1 h3]
  have hNσ : ∀ u, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) (σ u) ↔ (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u := by
    intro u
    constructor
    · intro h
      have h' := hσfix _ h
      rw [hσσ] at h'
      rw [h']; exact h
    · intro h; rw [hσfix u h]; exact h
  -- the reconnections
  have hrec : ρ.reconnect a₁ = ρ.succ * Equiv.swap a₁ b₁ := by unfold Record.reconnect; rw [hx]
  have hrec' : ρ'.reconnect (Φ a₁) = ρ'.succ * Equiv.swap (Φ a₁) (Φ b₁) := by
    unfold Record.reconnect; rw [← hpair, hx]
  -- `Φ` intertwines the `σ`-conjugate `r̃ = σ (s ∘ (a₂ b₂)) σ` with `s' ∘ (Φ a₁, Φ b₁)`
  have hΦr : ∀ u, Φ ((σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) u) = ρ'.reconnect (Φ a₁) (Φ u) := by
    intro u
    rw [hrec']
    show Φ (σ ((ρ.succ * Equiv.swap a₂ b₂) (σ u))) = ρ'.succ (Equiv.swap (Φ a₁) (Φ b₁) (Φ u))
    rw [← w3bh_map_swap Φ a₁ b₁ u, ← hsucc]
    show Φ (σ (ρ.succ (Equiv.swap a₂ b₂ (σ u)))) = Φ (σ (ρ.succ (σ (Equiv.swap a₁ b₁ u))))
    have h := congrArg (fun π : Equiv.Perm ρ.M => π u) (Equiv.mul_swap_eq_swap_mul σ a₁ b₁)
    simp only [Equiv.Perm.mul_apply, hσa₁, hσb₁] at h
    rw [h]
  have hp : ∀ u, (fun u => u ≠ Φ a₁ ∧ u ≠ Φ b₁ ∧ u ≠ Φ a₂ ∧ u ≠ Φ c₁ ∧ u ≠ Φ b₂ ∧ u ≠ Φ c₂) (Φ u) ↔ (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u := by
    intro u; simp only [Ne, Φ.apply_eq_iff_eq]
  have step1 : (firstReturn (ρ'.reconnect (Φ a₁)) (fun u => u ≠ Φ a₁ ∧ u ≠ Φ b₁ ∧ u ≠ Φ a₂ ∧ u ≠ Φ c₁ ∧ u ≠ Φ b₂ ∧ u ≠ Φ c₂) ⟨Φ v, hv'⟩).1 =
      Φ (firstReturn (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 :=
    firstReturn_map_val Φ (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) (ρ'.reconnect (Φ a₁)) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) (fun u => u ≠ Φ a₁ ∧ u ≠ Φ b₁ ∧ u ≠ Φ a₂ ∧ u ≠ Φ c₁ ∧ u ≠ Φ b₂ ∧ u ≠ Φ c₂) hΦr hp ⟨v, hv⟩
  -- conjugation by `σ` does not change the first return on the (pointwise fixed) non-local set
  have step2 : (firstReturn (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 =
      (firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 := by
    have hg : ∀ u, σ ((ρ.succ * Equiv.swap a₂ b₂) u) = (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) (σ u) := by
      intro u
      show σ ((ρ.succ * Equiv.swap a₂ b₂) u) = σ ((ρ.succ * Equiv.swap a₂ b₂) (σ (σ u)))
      rw [hσσ]
    have h := firstReturn_map_val σ (ρ.succ * Equiv.swap a₂ b₂) (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ)
      (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) hg hNσ ⟨v, hv⟩
    have hσv : (⟨σ v, (hNσ v).mpr hv⟩ : {u // (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u}) = ⟨v, hv⟩ := Subtype.ext (hσfix v hv)
    rw [hσv] at h
    rw [h]
    exact hσfix _ (firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).2
  rw [step1, step2, hrec]
  exact congrArg Φ (w3bh_core_pure ρ hρ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz hxy hxz hyz hadj_e hadj_f hadj_g v hv)

/-- `w3bh_` helper: a set closed under `f` contains the whole `f`-cycle of each of its points. -/
theorem w3bh_sameCycle_closed {α : Type*} [Finite α] (f : Equiv.Perm α) (S : α → Prop)
    (hS : ∀ x, S x → S (f x)) {x v : α} (hx : S x) (h : f.SameCycle x v) : S v := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have key : ∀ n : ℕ, S ((f ^ n) x) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hS _ ih
  rw [← hn]; exact key n

/-- **`w3bh_` the pure component core (Φ-free)**, companion of `w3bh_core_pure`: the cycles of the smoothing
reconnection `s ∘ (a₁ b₁)` and of the reconnection `s ∘ (a₂ b₂)` induce the same partition of the non-local
occurrences — a bijection of the two-element cycle sets (`mul_swap_sameCycle_or`,
`not_mul_swap_sameCycle_of_sameCycle`) fixing the class of every non-local `v`.  PROVED (Unit H, 2026-09-15):
the induced permutations on the retained set agree (`w3bh_core_pure₀`), so cycle classes of retained points
transfer (`firstReturn_sameCycle_iff`); the class of `a₁` (resp. `a₂`) is followed to its exit `s b₂` (`s b₁` when
`s b₂ = b₁`) by `sameCycle_apply_right`; a non-retained exit closes a local cycle containing no retained point
(`w3bh_sameCycle_closed`) or contradicts predecessor uniqueness / one circle.  `w3bh_core_comp` is derived from it. -/
theorem w3bh_core_comp_pure (ρ : Record) (hρ : ρ.componentCount = 1) (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁) :
    ∃ e₀ : Quotient (Equiv.Perm.SameCycle.setoid (ρ.reconnect a₁)) ≃
        Quotient (Equiv.Perm.SameCycle.setoid (ρ.succ * Equiv.swap a₂ b₂)),
      ∀ v : ρ.M, (v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) →
        e₀ (Quotient.mk _ v) = Quotient.mk _ v := by
  have hne : ∀ u w : ρ.M, ρ.crossingOf u ≠ ρ.crossingOf w → u ≠ w := fun u w h h' => h (h' ▸ rfl)
  have hcb₁ : ρ.crossingOf b₁ = ρ.crossingOf a₁ := by rw [← hx, ρ.crossingOf_pair]
  have h13 : a₁ ≠ b₁ := by rw [← hx]; exact ρ.ne_pair a₁
  have h12 : a₁ ≠ a₂ := hne _ _ hxy
  have h14 : a₁ ≠ b₂ := hne _ _ hxz
  have h24 : a₂ ≠ b₂ := hne _ _ hyz
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [hcb₁]; exact hxy.symm)
  have h34 : b₁ ≠ b₂ := hne _ _ (by rw [hcb₁]; exact hxz)
  have hrec : ρ.reconnect a₁ = ρ.succ * Equiv.swap a₁ b₁ := by unfold Record.reconnect; rw [hx]
  rw [hrec]
  -- evaluations of the two reconnections
  have e1 : ∀ u, u ≠ a₁ → u ≠ b₁ → (ρ.succ * Equiv.swap a₁ b₁) u = ρ.succ u := fun u h1 h2 => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e1a : (ρ.succ * Equiv.swap a₁ b₁) a₁ = ρ.succ b₁ := by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have e2 : ∀ u, u ≠ a₂ → u ≠ b₂ → (ρ.succ * Equiv.swap a₂ b₂) u = ρ.succ u := fun u h1 h2 => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e2a : (ρ.succ * Equiv.swap a₂ b₂) a₂ = ρ.succ b₂ := by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  -- the induced permutations on the retained set agree (`w3bh_core_pure₀`), so cycle classes transfer
  have hF : firstReturn (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) = firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) := by
    ext m
    exact w3bh_core_pure₀ ρ hρ a₁ a₂ b₁ b₂ h12 h13 h14 h23 h24 h34 hadj_e hadj_f m.1 m.2
  have transfer : ∀ u w, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) u → (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) w → ((ρ.succ * Equiv.swap a₁ b₁).SameCycle u w ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle u w) := by
    intro u w hu hw
    have h1 := firstReturn_sameCycle_iff (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ⟨u, hu⟩ ⟨w, hw⟩
    have h2 := firstReturn_sameCycle_iff (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ⟨u, hu⟩ ⟨w, hw⟩
    rw [hF] at h1
    exact h1.symm.trans h2
  -- the class of `a₁` under `f₁` and of `a₂` under `f₂` agree on the retained occurrences
  have key : ∀ v, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) v → ((ρ.succ * Equiv.swap a₁ b₁).SameCycle v a₁ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v a₂) := by
    intro v hv
    obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
    rcases hadj_f with hF1 | hF2
    · -- `s b₁ = b₂`: both classes continue at `s b₂`
      have t1 : (ρ.succ * Equiv.swap a₁ b₁).SameCycle v a₁ ↔ (ρ.succ * Equiv.swap a₁ b₁).SameCycle v ((ρ.succ * Equiv.swap a₁ b₁) a₁) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e1a, hF1] at t1
      have t2 : (ρ.succ * Equiv.swap a₁ b₁).SameCycle v b₂ ↔ (ρ.succ * Equiv.swap a₁ b₁).SameCycle v ((ρ.succ * Equiv.swap a₁ b₁) b₂) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e1 b₂ (Ne.symm h14) (Ne.symm h34)] at t2
      have u1 : (ρ.succ * Equiv.swap a₂ b₂).SameCycle v a₂ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v ((ρ.succ * Equiv.swap a₂ b₂) a₂) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e2a] at u1
      rw [t1, t2, u1]
      by_cases hβ : (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) (ρ.succ b₂)
      · exact transfer v _ ⟨hv1, hv2, hv3, hv4⟩ hβ
      · have hβ' : ρ.succ b₂ = a₁ ∨ ρ.succ b₂ = b₁ ∨ ρ.succ b₂ = a₂ ∨ ρ.succ b₂ = b₂ := by
          by_contra hc
          push Not at hc
          exact hβ ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
        rcases hβ' with hβ | hβ | hβ | hβ
        · rcases hadj_e with hE1 | hE2
          · rw [hβ]
            apply iff_of_false
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₁ b₁) (fun u => u = a₁ ∨ u = b₂) (by
                  rintro u (hu | hu)
                  · rw [hu]; right; rw [e1a, hF1]
                  · rw [hu]; left; rw [e1 b₂ (Ne.symm h14) (Ne.symm h34), hβ]) (Or.inl rfl) h.symm
              rcases this with h' | h'
              · exact hv1 h'
              · exact hv4 h'
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₂ b₂) (fun u => u = a₂ ∨ u = a₁) (by
                  rintro u (hu | hu)
                  · rw [hu]; right; rw [e2a, hβ]
                  · rw [hu]; left; rw [e2 a₁ h12 h14, hE1]) (Or.inr rfl) h.symm
              rcases this with h' | h'
              · exact hv3 h'
              · exact hv1 h'
          · exact absurd (ρ.succ.injective (hβ.trans hE2.symm)) (Ne.symm h24)
        · exact (w3bh_no_two_cycle ρ hρ b₁ b₂ v hF1 hβ hv2 hv4).elim
        · rcases hadj_e with hE1 | hE2
          · exact absurd (ρ.succ.injective (hβ.trans hE1.symm)) (Ne.symm h14)
          · rw [hβ]
            apply iff_of_false
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₁ b₁) (fun u => u = a₁ ∨ u = b₂ ∨ u = a₂) (by
                  rintro u (hu | hu | hu)
                  · rw [hu]; right; left; rw [e1a, hF1]
                  · rw [hu]; right; right; rw [e1 b₂ (Ne.symm h14) (Ne.symm h34), hβ]
                  · rw [hu]; left; rw [e1 a₂ (Ne.symm h12) h23, hE2]) (Or.inr (Or.inr rfl)) h.symm
              rcases this with h' | h' | h'
              · exact hv1 h'
              · exact hv4 h'
              · exact hv3 h'
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₂ b₂) (fun u => u = a₂) (by
                  rintro u hu; rw [hu, e2a, hβ]) rfl h.symm
              exact hv3 this
        · exact (w3bh_no_fixed ρ hρ b₂ v hβ hv4).elim
    · -- `s b₂ = b₁`: both classes continue at `s b₁`
      have t1 : (ρ.succ * Equiv.swap a₁ b₁).SameCycle v a₁ ↔ (ρ.succ * Equiv.swap a₁ b₁).SameCycle v ((ρ.succ * Equiv.swap a₁ b₁) a₁) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e1a] at t1
      have u1 : (ρ.succ * Equiv.swap a₂ b₂).SameCycle v a₂ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v ((ρ.succ * Equiv.swap a₂ b₂) a₂) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e2a, hF2] at u1
      have u2 : (ρ.succ * Equiv.swap a₂ b₂).SameCycle v b₁ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v ((ρ.succ * Equiv.swap a₂ b₂) b₁) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e2 b₁ (Ne.symm h23) h34] at u2
      rw [t1, u1, u2]
      by_cases hγ : (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) (ρ.succ b₁)
      · exact transfer v _ ⟨hv1, hv2, hv3, hv4⟩ hγ
      · have hγ' : ρ.succ b₁ = a₁ ∨ ρ.succ b₁ = b₁ ∨ ρ.succ b₁ = a₂ ∨ ρ.succ b₁ = b₂ := by
          by_contra hc
          push Not at hc
          exact hγ ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
        rcases hγ' with hγ | hγ | hγ | hγ
        · rcases hadj_e with hE1 | hE2
          · rw [hγ]
            apply iff_of_false
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₁ b₁) (fun u => u = a₁) (by
                  rintro u hu; rw [hu, e1a, hγ]) rfl h.symm
              exact hv1 this
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₂ b₂) (fun u => u = a₂ ∨ u = b₁ ∨ u = a₁) (by
                  rintro u (hu | hu | hu)
                  · rw [hu]; right; left; rw [e2a, hF2]
                  · rw [hu]; right; right; rw [e2 b₁ (Ne.symm h23) h34, hγ]
                  · rw [hu]; left; rw [e2 a₁ h12 h14, hE1]) (Or.inr (Or.inr rfl)) h.symm
              rcases this with h' | h' | h'
              · exact hv3 h'
              · exact hv2 h'
              · exact hv1 h'
          · exact absurd (ρ.succ.injective (hγ.trans hE2.symm)) (Ne.symm h23)
        · exact (w3bh_no_fixed ρ hρ b₁ v hγ hv2).elim
        · rcases hadj_e with hE1 | hE2
          · exact absurd (ρ.succ.injective (hγ.trans hE1.symm)) (Ne.symm h13)
          · rw [hγ]
            apply iff_of_false
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₁ b₁) (fun u => u = a₁ ∨ u = a₂) (by
                  rintro u (hu | hu)
                  · rw [hu]; right; rw [e1a, hγ]
                  · rw [hu]; left; rw [e1 a₂ (Ne.symm h12) h23, hE2]) (Or.inr rfl) h.symm
              rcases this with h' | h'
              · exact hv1 h'
              · exact hv3 h'
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₂ b₂) (fun u => u = a₂ ∨ u = b₁) (by
                  rintro u (hu | hu)
                  · rw [hu]; right; rw [e2a, hF2]
                  · rw [hu]; left; rw [e2 b₁ (Ne.symm h23) h34, hγ]) (Or.inl rfl) h.symm
              rcases this with h' | h'
              · exact hv3 h'
              · exact hv2 h'
        · exact (w3bh_no_two_cycle ρ hρ b₁ b₂ v hγ hF2 hv2 hv4).elim
  -- the two-class structure of both reconnections
  have two1 : ∀ u, (ρ.succ * Equiv.swap a₁ b₁).SameCycle u a₁ ∨ (ρ.succ * Equiv.swap a₁ b₁).SameCycle u b₁ := fun u =>
    mul_swap_sameCycle_or ρ.succ a₁ b₁ (ρ.sameCycle_of_one_circle hρ u a₁)
  have two2 : ∀ u, (ρ.succ * Equiv.swap a₂ b₂).SameCycle u a₂ ∨ (ρ.succ * Equiv.swap a₂ b₂).SameCycle u b₂ := fun u =>
    mul_swap_sameCycle_or ρ.succ a₂ b₂ (ρ.sameCycle_of_one_circle hρ u a₂)
  have nab2 : ¬ (ρ.succ * Equiv.swap a₂ b₂).SameCycle a₂ b₂ :=
    not_mul_swap_sameCycle_of_sameCycle ρ.succ a₂ b₂ h24 (ρ.sameCycle_of_one_circle hρ a₂ b₂)
  have nab1 : ¬ (ρ.succ * Equiv.swap a₁ b₁).SameCycle a₁ b₁ :=
    not_mul_swap_sameCycle_of_sameCycle ρ.succ a₁ b₁ h13 (ρ.sameCycle_of_one_circle hρ a₁ b₁)
  classical
  refine ⟨{ toFun := Quotient.lift
              (fun u => if (ρ.succ * Equiv.swap a₁ b₁).SameCycle u a₁ then Quotient.mk _ a₂ else Quotient.mk _ b₂) ?_
            invFun := Quotient.lift
              (fun u => if (ρ.succ * Equiv.swap a₂ b₂).SameCycle u a₂ then Quotient.mk _ a₁ else Quotient.mk _ b₁) ?_
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro u w huw
    have h : (ρ.succ * Equiv.swap a₁ b₁).SameCycle u a₁ ↔ (ρ.succ * Equiv.swap a₁ b₁).SameCycle w a₁ :=
      ⟨fun h => (huw : (ρ.succ * Equiv.swap a₁ b₁).SameCycle u w).symm.trans h, fun h => (huw : (ρ.succ * Equiv.swap a₁ b₁).SameCycle u w).trans h⟩
    simp only [h]
  · intro u w huw
    have h : (ρ.succ * Equiv.swap a₂ b₂).SameCycle u a₂ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle w a₂ :=
      ⟨fun h => (huw : (ρ.succ * Equiv.swap a₂ b₂).SameCycle u w).symm.trans h, fun h => (huw : (ρ.succ * Equiv.swap a₂ b₂).SameCycle u w).trans h⟩
    simp only [h]
  · intro q
    induction q using Quotient.inductionOn with
    | h u =>
      by_cases h : (ρ.succ * Equiv.swap a₁ b₁).SameCycle u a₁
      · rw [Quotient.lift_mk, if_pos h, Quotient.lift_mk, if_pos (Equiv.Perm.SameCycle.refl _ _)]
        exact Quotient.sound h.symm
      · rw [Quotient.lift_mk, if_neg h, Quotient.lift_mk, if_neg (fun h' => nab2 h'.symm)]
        exact Quotient.sound ((two1 u).resolve_left h).symm
  · intro q
    induction q using Quotient.inductionOn with
    | h u =>
      by_cases h : (ρ.succ * Equiv.swap a₂ b₂).SameCycle u a₂
      · rw [Quotient.lift_mk, if_pos h, Quotient.lift_mk, if_pos (Equiv.Perm.SameCycle.refl _ _)]
        exact Quotient.sound h.symm
      · rw [Quotient.lift_mk, if_neg h, Quotient.lift_mk, if_neg (fun h' => nab1 h'.symm)]
        exact Quotient.sound ((two2 u).resolve_left h).symm
  · intro v hv
    have hP : (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) v := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.2.1⟩
    rw [Equiv.coe_fn_mk]
    by_cases h : (ρ.succ * Equiv.swap a₁ b₁).SameCycle v a₁
    · rw [Quotient.lift_mk, if_pos h]
      exact Quotient.sound ((key v hP).mp h).symm
    · rw [Quotient.lift_mk, if_neg h]
      have h2 : ¬ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v a₂ := fun h' => h ((key v hP).mpr h')
      exact Quotient.sound ((two2 v).resolve_left h2).symm


/-- **`w3bh_` core sub-lemma (b), the component bijection**: the two cycles of `s ∘ (a₁ b₁)` (the
smoothing of a self-crossing of the single circle, `componentCount_smooth_of_self`) are the classes of
`a₁` and of `b₁` (`reconnect_sameCycle_or`, `not_reconnect_sameCycle_pair_of_self`), likewise on `ρ'`;
`e := [a₁] ↦ [Φ a₁], [b₁] ↦ [Φ b₁]` (crossing-free circles: none, one component with occurrences), and a
retained `v` lies on the cycle of `a₁` iff `Φ v` lies on the cycle of `Φ a₁` (the same cyclic-word check as
in (a): `v ∈ B''` on both sides).  OPEN (Unit H, 2026-09-15): stated, not proved. -/
theorem w3bh_core_comp (ρ ρ' : Record) (hρ : ρ.componentCount = 1) (hρ' : ρ'.componentCount = 1)
    (Φ : ρ.M ≃ ρ'.M) (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁)
    (hpair : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v))
    (hsucc : ∀ v, Φ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (ρ.succ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) = ρ'.succ (Φ v)) :
    ∃ e : (ρ.smooth a₁).comps ≃ (ρ'.smooth (Φ a₁)).comps,
      ∀ (v : ρ.M) (hv : ρ.SmoothKeep a₁ v) (hv' : ρ'.SmoothKeep (Φ a₁) (Φ v)),
        (v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) →
        (ρ'.smooth (Φ a₁)).comp ⟨Φ v, hv'⟩ = e ((ρ.smooth a₁).comp ⟨v, hv⟩) := by
  -- the six local occurrences are distinct (as in `w3bh_core_firstReturn`)
  have hne : ∀ u w : ρ.M, ρ.crossingOf u ≠ ρ.crossingOf w → u ≠ w := fun u w h h' => h (h' ▸ rfl)
  have hcb₁ : ρ.crossingOf b₁ = ρ.crossingOf a₁ := by rw [← hx, ρ.crossingOf_pair]
  have hcc₁ : ρ.crossingOf c₁ = ρ.crossingOf a₂ := by rw [← hy, ρ.crossingOf_pair]
  have hcc₂ : ρ.crossingOf c₂ = ρ.crossingOf b₂ := by rw [← hz, ρ.crossingOf_pair]
  have h13 : a₁ ≠ b₁ := by rw [← hx]; exact ρ.ne_pair a₁
  have h25 : a₂ ≠ c₁ := by rw [← hy]; exact ρ.ne_pair a₂
  have h46 : b₂ ≠ c₂ := by rw [← hz]; exact ρ.ne_pair b₂
  have h14 : a₁ ≠ b₂ := hne _ _ hxz
  have h24 : a₂ ≠ b₂ := hne _ _ hyz
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [hcc₁]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [hcc₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [hcb₁]; exact hxy.symm)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [hcc₂]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hcb₁, hcc₁]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hcb₁, hcc₂]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hcc₁]; exact hyz.symm)
  set σ : Equiv.Perm ρ.M := Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂) with hσ
  have hσsq : σ * σ = 1 :=
    w3bh_swap3_sq a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  have hσσ : ∀ u, σ (σ u) = u :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσsq
  have hσa₁ : σ a₁ = a₂ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h15 h16,
      Equiv.swap_apply_of_ne_of_ne h13 h14, Equiv.swap_apply_left]
  have hσb₁ : σ b₁ = b₂ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h35 h36,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h14.symm h24.symm]
  have hσfix : ∀ u, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u → σ u = u := by
    intro u hu
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h4 h6,
      Equiv.swap_apply_of_ne_of_ne h2 h5, Equiv.swap_apply_of_ne_of_ne h1 h3]
  have hrec' : ρ'.reconnect (Φ a₁) = ρ'.succ * Equiv.swap (Φ a₁) (Φ b₁) := by
    unfold Record.reconnect; rw [← hpair, hx]
  have hΦr : ∀ u, Φ ((σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) u) = ρ'.reconnect (Φ a₁) (Φ u) := by
    intro u
    rw [hrec']
    show Φ (σ ((ρ.succ * Equiv.swap a₂ b₂) (σ u))) = ρ'.succ (Equiv.swap (Φ a₁) (Φ b₁) (Φ u))
    rw [← w3bh_map_swap Φ a₁ b₁ u, ← hsucc]
    show Φ (σ (ρ.succ (Equiv.swap a₂ b₂ (σ u)))) = Φ (σ (ρ.succ (σ (Equiv.swap a₁ b₁ u))))
    have h := congrArg (fun π : Equiv.Perm ρ.M => π u) (Equiv.mul_swap_eq_swap_mul σ a₁ b₁)
    simp only [Equiv.Perm.mul_apply, hσa₁, hσb₁] at h
    rw [h]
  -- the non-local predicate
  have hN : ∀ v : ρ.M, ρ.SmoothKeep a₁ v → (v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) → (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) v := by
    intro v hv hQ
    rw [Record.smoothKeep_iff, hx] at hv
    exact ⟨hv.1, hv.2, hQ⟩
  -- crossing-free circles: none on a one-circle record with an occurrence
  have hfree : ∀ (τ : Record) (hτ : τ.componentCount = 1) (u : τ.M), IsEmpty τ.FreeComp := by
    intro τ hτ u
    refine ⟨fun c => c.2 u ?_⟩
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hτ
    rw [hx (τ.comp u), hx c.1]
  have := hfree ρ hρ a₁
  have := hfree ρ' hρ' (Φ a₁)
  -- the pure core and the two transports of the cycle quotients
  obtain ⟨e₀, he₀⟩ := w3bh_core_comp_pure ρ hρ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz hxy hxz hyz hadj_e hadj_f hadj_g
  have hconj : ∀ u w, (ρ.succ * Equiv.swap a₂ b₂).SameCycle u w ↔
      (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ).SameCycle (σ u) (σ w) := by
    intro u w
    have h := Equiv.Perm.sameCycle_conj (g := σ) (f := ρ.succ * Equiv.swap a₂ b₂) (x := σ u) (y := σ w)
    rw [hσinv, hσσ, hσσ] at h
    exact h.symm
  let qσ : Quotient (Equiv.Perm.SameCycle.setoid (ρ.succ * Equiv.swap a₂ b₂)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ)) := Quotient.congr σ hconj
  let qΦ : Quotient (Equiv.Perm.SameCycle.setoid (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (ρ'.reconnect (Φ a₁))) :=
    Quotient.congr Φ (fun u w => (sameCycle_map_iff Φ _ _ hΦr u w).symm)
  refine ⟨Equiv.sumCongr (e₀.trans (qσ.trans qΦ)) (Equiv.equivOfIsEmpty _ _), ?_⟩
  intro v hv hv' hQ
  have hNv := hN v hv hQ
  show Sum.inl (Quotient.mk _ (Φ v)) =
    Equiv.sumCongr (e₀.trans (qσ.trans qΦ)) (Equiv.equivOfIsEmpty _ _) (Sum.inl (Quotient.mk _ v))
  rw [Equiv.sumCongr_apply, Sum.map_inl, Equiv.trans_apply, he₀ v hNv, Equiv.trans_apply]
  show Sum.inl (Quotient.mk _ (Φ v)) = Sum.inl (Quotient.mk _ (Φ (σ v)))
  rw [hσfix v hNv]


/-- **(h) sub-leaf — the record core**: two one-circle records `ρ, ρ'` whose occurrences correspond by `Φ`
preserving pairing, bits and signs and the successor TWISTED by the three transpositions
`σ = (a₁ a₂)(b₁ b₂)(c₁ c₂)` on the six local occurrences (`Φ (σ (s (σ v))) = s' (Φ v)`, the successor form
of `G11_core_statement`'s cyclic clause) — `a₁,b₁` the occurrences of `x` on `e, f`; `a₂,c₁` of `y` on `e, g`;
`b₂,c₂` of `z` on `f, g`; on each strand the two local occurrences adjacent (R-LOC (2),
`LocalizationData.adjacent`).  After smoothing at `x` (`Record.smooth a₁`) and deleting the crossings of
`y, z` (`restrictCrossings`), the two records are isomorphic.  Sketch: the retained occurrences are the
non-local ones, on which `Φ` is a bijection; for a retained `u` the first return of the reconnected
successor `s₁ = s ∘ swap a₁ b₁` to the retained set passes through at most one local strand-pair and
reconnects `pred(a₁) ↦ succ(b₂)`, `pred(b₁) ↦ succ(a₂)` when `x` precedes on both strands, etc. — the
eight orientation patterns (`hadj_*`) each give the SAME first-return on both sides (verified case by
case in the report); components: the cycles of `s₁` correspond under `Φ` (two cycles: the smoothing of a
self-crossing of one circle, `Record.componentCount_smooth`), `RecordIso.ofOcc`-style assembly with
`firstReturn_no_between`/`cycNext_unique_on`.  ≈ 1.2k lines. -/
theorem w3h_record_core (ρ ρ' : Record) (hρ : ρ.componentCount = 1) (hρ' : ρ'.componentCount = 1)
    (Φ : ρ.M ≃ ρ'.M) (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁)
    (hpair : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hbit : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hsgn : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v)
    (hsucc : ∀ v, Φ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (ρ.succ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) = ρ'.succ (Φ v)) :
    Nonempty (RecordIso
      ((ρ.smooth a₁).restrictCrossings {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})
      ((ρ'.smooth (Φ a₁)).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ Φ a₂ ∧ v.1 ≠ Φ c₁ ∧ v.1 ≠ Φ b₂ ∧ v.1 ≠ Φ c₂})) := by
  -- the pairing on `ρ'`
  have hx' : ρ'.pair (Φ a₁) = Φ b₁ := by rw [← hpair, hx]
  have hy' : ρ'.pair (Φ a₂) = Φ c₁ := by rw [← hpair, hy]
  have hz' : ρ'.pair (Φ b₂) = Φ c₂ := by rw [← hpair, hz]
  -- the smoothing-retained occurrences correspond
  have hSK : ∀ v, ρ.SmoothKeep a₁ v ↔ ρ'.SmoothKeep (Φ a₁) (Φ v) := by
    intro v
    rw [Record.smoothKeep_iff, Record.smoothKeep_iff, ← hpair, Ne, Ne, Ne, Ne,
      Φ.apply_eq_iff_eq, Φ.apply_eq_iff_eq]
  let Φ₁ : (ρ.smooth a₁).M ≃ (ρ'.smooth (Φ a₁)).M := Equiv.subtypeEquiv Φ hSK
  -- the deletion-retained occurrences correspond
  have hQ := w3bh_crossKeep_iff ρ a₁ a₂ b₂ c₁ c₂ hy hz
  have hQ' := w3bh_crossKeep_iff ρ' (Φ a₁) (Φ a₂) (Φ b₂) (Φ c₁) (Φ c₂) hy' hz'
  have hRK : ∀ w : (ρ.smooth a₁).M,
      (ρ.smooth a₁).CrossKeep {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂} w ↔
      (ρ'.smooth (Φ a₁)).CrossKeep {c | ∀ v ∈ c.1, v.1 ≠ Φ a₂ ∧ v.1 ≠ Φ c₁ ∧ v.1 ≠ Φ b₂ ∧ v.1 ≠ Φ c₂}
        (Φ₁ w) := by
    intro w
    rw [hQ, hQ']
    show _ ↔ (Φ w.1 ≠ Φ a₂ ∧ Φ w.1 ≠ Φ c₁ ∧ Φ w.1 ≠ Φ b₂ ∧ Φ w.1 ≠ Φ c₂)
    simp only [Ne, Φ.apply_eq_iff_eq]
  let Φ₂ := Equiv.subtypeEquiv Φ₁ hRK
  -- the component bijection
  obtain ⟨e, he⟩ := w3bh_core_comp ρ ρ' hρ hρ' Φ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz hxy hxz hyz hadj_e hadj_f
    hadj_g hpair hsucc
  -- the non-local predicate
  have hN : ∀ v : ρ.M, (ρ.SmoothKeep a₁ v ∧ (v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂)) ↔
      (v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) := by
    intro v; rw [Record.smoothKeep_iff, hx, and_assoc]
  have hN' : ∀ v : ρ'.M, (ρ'.SmoothKeep (Φ a₁) v ∧ (v ≠ Φ a₂ ∧ v ≠ Φ c₁ ∧ v ≠ Φ b₂ ∧ v ≠ Φ c₂)) ↔
      (v ≠ Φ a₁ ∧ v ≠ Φ b₁ ∧ v ≠ Φ a₂ ∧ v ≠ Φ c₁ ∧ v ≠ Φ b₂ ∧ v ≠ Φ c₂) := by
    intro v; rw [Record.smoothKeep_iff, hx', and_assoc]
  -- the successor of a doubly restricted record is the first return to the non-local set
  have hred : ∀ (τ : Record) (a₁ a₂ b₁ b₂ c₁ c₂ : τ.M) (hx : τ.pair a₁ = b₁) (hy : τ.pair a₂ = c₁)
      (hz : τ.pair b₂ = c₂)
      (w : ((τ.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂}).M)
      (hw : w.1.1 ≠ a₁ ∧ w.1.1 ≠ b₁ ∧ w.1.1 ≠ a₂ ∧ w.1.1 ≠ c₁ ∧ w.1.1 ≠ b₂ ∧ w.1.1 ≠ c₂),
      (((τ.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂}).succ w).1.1 =
      (firstReturn (τ.reconnect a₁)
        (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨w.1.1, hw⟩).1 := by
    intro τ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz w hw
    have hQτ := w3bh_crossKeep_iff τ a₁ a₂ b₂ c₁ c₂ hy hz
    have hNτ : ∀ v : τ.M, (τ.SmoothKeep a₁ v ∧ (v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂)) ↔
        (v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) := by
      intro v; rw [Record.smoothKeep_iff, hx, and_assoc]
    have h1 := firstReturn_congr_pred (τ.smooth a₁).succ
      ((τ.smooth a₁).CrossKeep {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})
      (fun m => m.1 ≠ a₂ ∧ m.1 ≠ c₁ ∧ m.1 ≠ b₂ ∧ m.1 ≠ c₂) hQτ w
    have h2 := firstReturn_firstReturn (τ.reconnect a₁) (τ.SmoothKeep a₁)
      (fun m => m ≠ a₂ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂) ⟨w.1, (hQτ w.1).mp w.2⟩
    have h3 := firstReturn_congr_pred (τ.reconnect a₁)
      (fun m => τ.SmoothKeep a₁ m ∧ (m ≠ a₂ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂))
      (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) hNτ
      ⟨w.1.1, w.1.2, (hQτ w.1).mp w.2⟩
    exact (congrArg Subtype.val h1).trans (h2.trans h3)
  refine ⟨{ e := e, Φ := Φ₂, comp_eq := ?_, succ_eq := ?_, pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }⟩
  · intro w
    exact he w.1.1 w.1.2 ((hSK w.1.1).mp w.1.2) ((hQ w.1).mp w.2)
  · intro w
    apply Subtype.ext; apply Subtype.ext
    have hw : w.1.1 ≠ a₁ ∧ w.1.1 ≠ b₁ ∧ w.1.1 ≠ a₂ ∧ w.1.1 ≠ c₁ ∧ w.1.1 ≠ b₂ ∧ w.1.1 ≠ c₂ :=
      (hN w.1.1).mp ⟨w.1.2, (hQ w.1).mp w.2⟩
    have hw' : Φ w.1.1 ≠ Φ a₁ ∧ Φ w.1.1 ≠ Φ b₁ ∧ Φ w.1.1 ≠ Φ a₂ ∧ Φ w.1.1 ≠ Φ c₁ ∧ Φ w.1.1 ≠ Φ b₂ ∧
        Φ w.1.1 ≠ Φ c₂ := by
      simp only [Ne, Φ.apply_eq_iff_eq]; exact hw
    show Φ (((ρ.smooth a₁).restrictCrossings _).succ w).1.1 =
      (((ρ'.smooth (Φ a₁)).restrictCrossings _).succ (Φ₂ w)).1.1
    rw [hred ρ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz w hw,
      hred ρ' (Φ a₁) (Φ a₂) (Φ b₁) (Φ b₂) (Φ c₁) (Φ c₂) hx' hy' hz' (Φ₂ w) hw']
    exact w3bh_core_firstReturn ρ ρ' hρ Φ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz hxy hxz hyz hadj_e hadj_f hadj_g
      hpair hsucc w.1.1 hw hw'
  · intro w
    apply Subtype.ext; apply Subtype.ext
    exact hpair w.1.1
  · intro w; exact hbit w.1.1
  · intro w; exact hsgn w.1.1


/-- **(h) sub-leaf — the record bridge with the occurrence correspondence exposed**: the accepted
`smoothDiagram_record` gives SOME record isomorphism `(D^x).record ≅ D.record.smooth (overVisit x)`; the
consumer needs to know that it carries the crossing of `D^x` at a double point to the crossing of `D` at the
same double point (so that `y₀, z₀` go to `y, z`).  Sketch: unfold `smoothDiagram`, `split_ifs`, and read
`selfRecordIso`/`mixedRecordIso`'s `Φ` (built from `crossingEquiv`/`origCrossing`, Smoothing §8): the image
of an occurrence lies over `origCrossing` of its crossing, whose double point is the same
(`crossingPoint_origCrossing`-type lemma of §6).  ≈ 200 lines. -/
theorem w3h_smooth_record_occ (D : Diagram) (x : D.Γ.Crossing) (ε : ℝ) (hε : SmallEps D x ε) :
    ∃ ι : RecordIso (smoothDiagram D x ε hε).record (D.record.smooth (D.overVisit x)),
      ∀ v : (smoothDiagram D x ε hε).Γ.Visit,
        D.Γ.crossingPoint (ι.Φ v).1.1 = (smoothDiagram D x ε hε).Γ.crossingPoint v.1 := by
  unfold smoothDiagram
  by_cases h : (sS D x).1 = (tS D x).1
  · rw [dite_eq_left h]
    refine ⟨selfRecordIso D x hε h, fun v => ?_⟩
    exact (crossingPoint_origCrossing D x (selfModel D x ε h) hε v.1).symm
  · rw [dite_eq_right h]
    refine ⟨mixedRecordIso D x hε h, fun v => ?_⟩
    exact (crossingPoint_origCrossing D x (mixedModel D x ε h) hε v.1).symm


/-- **(h) sub-leaf — switching a DELETED crossing is invisible after the restriction** (companion of
`Record.restrictCrossings_switch`): `Record.switch v` changes only the bits and signs of the two occurrences
of `crossingOf v`, which are not retained; the identity on the retained occurrences is a `RecordIso`
(`firstReturn` of the same successor, same pairing).  ≈ 60 lines. -/
theorem w3h_restrict_switch_deleted (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ρ.crossingOf v ∉ S) :
    Nonempty (RecordIso ((ρ.switch v).restrictCrossings S) (ρ.restrictCrossings S)) := by
  have hne : ∀ w : ρ.M, ρ.crossingOf w ∈ S → w ≠ v ∧ w ≠ ρ.pair v := by
    intro w hw
    constructor
    · intro h; exact hv (h ▸ hw)
    · intro h; rw [h, ρ.crossingOf_pair] at hw; exact hv hw
  exact ⟨RecordIso.mk (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun w => by
      show ρ.isOver w.1 = (ρ.switch v).isOver w.1
      exact (ρ.switch_isOver_of_ne v (hne w.1 w.2).1 (hne w.1 w.2).2).symm)
    (fun w => by
      show ρ.sgn w.1 = (ρ.switch v).sgn w.1
      exact (ρ.switch_sgn_of_ne v (hne w.1 w.2).1 (hne w.1 w.2).2).symm)⟩


/-- `w3bh_` bridge (one side of `w3h_hrec`, D6 glue): the reduced record of a bigon `B` on the switched
smoothing output `(D^x)^{y₀−}` with `B.y = y₀`, `B.z = z₀` at the double points of `y, z`, transported
to the occurrence-defined restriction of `D.record.smooth a₁` (`a₁` either occurrence of `x`):
`switchRecordIso` → `restrictCrossings_iso_of_recordIso` → `w3h_restrict_switch_deleted` →
`w3h_smooth_record_occ` → (`smoothPairIso`). -/
theorem w3bh_reduced_to_smooth (D : Diagram) (x y z : D.Γ.Crossing)
    (a₁ a₂ b₂ c₁ c₂ : D.Γ.Visit) (ha₁ : a₁.1 = x) (ha₂ : a₂.1 = y) (hc₁ : c₁ = D.twin a₂)
    (hb₂ : b₂.1 = z) (hc₂ : c₂ = D.twin b₂)
    {ε : ℝ} (hε : SmallEps D x ε)
    (y₀ z₀ : (smoothDiagram D x ε hε).Γ.Crossing)
    (hy₀ : (smoothDiagram D x ε hε).Γ.crossingPoint y₀ = D.Γ.crossingPoint y)
    (hz₀ : (smoothDiagram D x ε hε).Γ.crossingPoint z₀ = D.Γ.crossingPoint z)
    (B : BigonData ((smoothDiagram D x ε hε).switch y₀)) (hBy : B.y = y₀) (hBz : B.z = z₀) :
    Nonempty (RecordIso B.reducedRecord
      ((D.record.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})) := by
  subst hc₁ hc₂
  -- the occurrence-defined retained set on `E = smoothDiagram D x ε hε`
  let X₁ : Set (smoothDiagram D x ε hε).record.Crossing := {c | ∀ w ∈ c.1, w.1 ≠ y₀ ∧ w.1 ≠ z₀}
  have hX₁ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit,
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔ (u.1 ≠ y₀ ∧ u.1 ≠ z₀) := by
    intro u
    rw [w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ∧
      (((smoothDiagram D x ε hε).twin u).1 ≠ y₀ ∧ ((smoothDiagram D x ε hε).twin u).1 ≠ z₀) ↔ _
    rw [Diagram.twin_fst, and_self]
  -- Step A/B: `B.reducedRecord ≅ (E.record.switch v₀).restrictCrossings X₁`
  obtain ⟨ι₂⟩ := CB.restrictCrossings_iso_of_recordIso
    ((smoothDiagram D x ε hε).switchRecordIso y₀ ((smoothDiagram D x ε hε).overVisit y₀) rfl) B.keep X₁ (by
    intro u
    show (((smoothDiagram D x ε hε).switch y₀).record.crossingOf u ≠
        ((smoothDiagram D x ε hε).switch y₀).record.crossingOf
          (((smoothDiagram D x ε hε).switch y₀).overVisit B.y) ∧
      ((smoothDiagram D x ε hε).switch y₀).record.crossingOf u ≠
        ((smoothDiagram D x ε hε).switch y₀).record.crossingOf
          (((smoothDiagram D x ε hε).switch y₀).overVisit B.z)) ↔
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁
    rw [Ne, Ne, w3bh_record_crossingOf_eq_iff, w3bh_record_crossingOf_eq_iff, Diagram.overVisit_fst,
      Diagram.overVisit_fst, hBy, hBz]
    exact (hX₁ u).symm)
  -- Step C: the switch at the deleted `y₀` is invisible
  obtain ⟨ι₃⟩ := w3h_restrict_switch_deleted (smoothDiagram D x ε hε).record X₁
    ((smoothDiagram D x ε hε).overVisit y₀) (fun h => ((hX₁ _).mp h).1 rfl)
  -- Step D: the smoothing bridge
  obtain ⟨ι₄, hι₄⟩ := w3h_smooth_record_occ D x ε hε
  have hpt : ∀ (u : (smoothDiagram D x ε hε).Γ.Visit) (w : D.Γ.Crossing)
      (w₀ : (smoothDiagram D x ε hε).Γ.Crossing)
      (hw₀ : (smoothDiagram D x ε hε).Γ.crossingPoint w₀ = D.Γ.crossingPoint w),
      (ι₄.Φ u).1.1 = w ↔ u.1 = w₀ := by
    intro u w w₀ hw₀
    constructor
    · intro h
      apply (smoothDiagram D x ε hε).generic.crossingPoint_injective
      rw [← hι₄ u, h, hw₀]
    · intro h
      apply D.generic.crossingPoint_injective
      rw [hι₄ u, h, hw₀]
  let X₂ : Set (D.record.smooth (D.overVisit x)).Crossing :=
    {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂}
  have hP : ∀ w : D.Γ.Visit, (w ≠ a₂ ∧ w ≠ D.twin a₂ ∧ w ≠ b₂ ∧ w ≠ D.twin b₂) ↔
      (w.1 ≠ y ∧ w.1 ≠ z) := by
    intro w
    rw [← and_assoc, w3bh_ne_ne_twin_iff, w3bh_ne_ne_twin_iff, ha₂, hb₂]
  have hX₂ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit, (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔
      (D.record.smooth (D.overVisit x)).crossingOf (ι₄.Φ u) ∈ X₂ := by
    intro u
    rw [hX₁, w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ↔
      ((ι₄.Φ u).1 ≠ a₂ ∧ (ι₄.Φ u).1 ≠ D.twin a₂ ∧ (ι₄.Φ u).1 ≠ b₂ ∧ (ι₄.Φ u).1 ≠ D.twin b₂) ∧
      (D.twin (ι₄.Φ u).1 ≠ a₂ ∧ D.twin (ι₄.Φ u).1 ≠ D.twin a₂ ∧ D.twin (ι₄.Φ u).1 ≠ b₂ ∧
        D.twin (ι₄.Φ u).1 ≠ D.twin b₂)
    rw [hP, hP, Diagram.twin_fst, and_self]
    exact Iff.and (not_congr (hpt u y y₀ hy₀).symm) (not_congr (hpt u z z₀ hz₀).symm)
  obtain ⟨ι₅⟩ := CB.restrictCrossings_iso_of_recordIso ι₄ X₁ X₂ hX₂
  -- Step E: land on `a₁`
  rcases D.eq_or_eq_twin (D.overVisit x) a₁ ha₁ with h | h
  · subst h
    exact ⟨ι₂.trans (ι₃.trans ι₅)⟩
  · subst h
    obtain ⟨ι₆⟩ := CB.restrictCrossings_iso_of_recordIso (D.record.smoothPairIso (D.overVisit x)).symm X₂
      {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂} (by
        intro u
        rw [w3bh_crossingOf_mem_setOf, w3bh_crossingOf_mem_setOf]
        exact Iff.rfl)
    exact ⟨ι₂.trans (ι₃.trans (ι₅.trans ι₆))⟩

/-- **(h) THE reduced-smoothed-record lemma, in the consumer's terms** (`esc_rii_after_smoothing_of_bigons`'s
`hrec`): two one-component diagrams `D_H, D_L` with a wall bijection `Ψ` (twins, bits, signs, the cyclic
order twisted by the three transpositions on the six local occurrences — the shape of
`G11_core_statement`, produced by G11 Unit F's `G11_twisted_key_lt` machinery on the two lifts), the
triangle `x, y, z` with adjacent local occurrences on each strand, the two `smoothDiagram` outputs at `x`,
the crossings `y₀, z₀` at the double points of `y, z`, and two `BigonData` on the switched outputs with
`B.y = y₀`, `B.z = z₀`: the two reduced records are isomorphic.  Sketch: `B.reducedRecord =
((D^x).switch y₀).record.restrictCrossings keep` `≅ ((D^x).record.switch _).restrictCrossings keep`
(`switchRecordIso`, `restrictCrossings_iso_of_recordIso` CBProducts:1358) `≅ (D^x).record.restrictCrossings
keep` (`w3h_restrict_switch_deleted`: `y₀` is deleted) `≅ (D.record.smooth (overVisit x)).restrictCrossings
{y,z}ᶜ` (`w3h_smooth_record_occ` + `restrictCrossings_iso_of_recordIso`; `smoothPairIso` to land on `a₁`), on
both sides; then `w3h_record_core` with `Φ := Ψ` (`hsucc` from `hcyc` by `nextVisit_comm_of_visitBetween_iff`
on the one-component `D_H`, `record_succ_apply`).  ≈ 400 lines of glue. -/
theorem w3h_hrec (D_H D_L : Diagram) (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1)
    (x_H y_H z_H : D_H.Γ.Crossing) (x_L y_L z_L : D_L.Γ.Crossing)
    (Ψ : D_H.Γ.Visit ≃ D_L.Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : D_H.Γ.Visit)
    (ha₁ : a₁.1 = x_H) (hb₁ : b₁ = D_H.twin a₁) (ha₂ : a₂.1 = y_H) (hc₁ : c₁ = D_H.twin a₂)
    (hb₂ : b₂.1 = z_H) (hc₂ : c₂ = D_H.twin b₂)
    (hxy : x_H ≠ y_H) (hxz : x_H ≠ z_H) (hyz : y_H ≠ z_H)
    (hadj_e : D_H.nextVisit a₁ = a₂ ∨ D_H.nextVisit a₂ = a₁)
    (hadj_f : D_H.nextVisit b₁ = b₂ ∨ D_H.nextVisit b₂ = b₁)
    (hadj_g : D_H.nextVisit c₁ = c₂ ∨ D_H.nextVisit c₂ = c₁)
    (htw : ∀ v, Ψ (D_H.twin v) = D_L.twin (Ψ v)) (hbit : ∀ v, D_L.overBit (Ψ v) = D_H.overBit v)
    (hsgn : ∀ v, D_L.sign (Ψ v).1 = D_H.sign v.1)
    (hcyc : ∀ u v w, D_L.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      D_H.VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w))
    (hxL : (Ψ a₁).1 = x_L) (hyL : (Ψ a₂).1 = y_L) (hzL : (Ψ b₂).1 = z_L)
    {εH εL : ℝ} (hεH : SmallEps D_H x_H εH) (hεL : SmallEps D_L x_L εL)
    (yH0 zH0 : (smoothDiagram D_H x_H εH hεH).Γ.Crossing)
    (hyH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint yH0 = D_H.Γ.crossingPoint y_H)
    (hzH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint zH0 = D_H.Γ.crossingPoint z_H)
    (yL0 zL0 : (smoothDiagram D_L x_L εL hεL).Γ.Crossing)
    (hyL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint yL0 = D_L.Γ.crossingPoint y_L)
    (hzL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint zL0 = D_L.Γ.crossingPoint z_L)
    (B_H : BigonData ((smoothDiagram D_H x_H εH hεH).switch yH0)) (hBHy : B_H.y = yH0) (hBHz : B_H.z = zH0)
    (B_L : BigonData ((smoothDiagram D_L x_L εL hεL).switch yL0)) (hBLy : B_L.y = yL0) (hBLz : B_L.z = zL0) :
    Nonempty (RecordIso B_H.reducedRecord B_L.reducedRecord) := by
  -- the six local occurrences and their crossings
  have hb₁x : b₁.1 = x_H := by rw [hb₁]; exact ha₁
  have hc₁y : c₁.1 = y_H := by rw [hc₁]; exact ha₂
  have hc₂z : c₂.1 = z_H := by rw [hc₂]; exact hb₂
  have hne : ∀ (u v : D_H.Γ.Visit), u.1 ≠ v.1 → u ≠ v :=
    fun u v h h' => h (congrArg (fun w : D_H.Γ.Visit => w.1) h')
  have h13 : a₁ ≠ b₁ := by rw [hb₁]; exact (D_H.twin_ne a₁).symm
  have h25 : a₂ ≠ c₁ := by rw [hc₁]; exact (D_H.twin_ne a₂).symm
  have h46 : b₂ ≠ c₂ := by rw [hc₂]; exact (D_H.twin_ne b₂).symm
  have h14 : a₁ ≠ b₂ := hne _ _ (by rw [ha₁, hb₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [ha₂, hb₁x]; exact hxy.symm)
  have h24 : a₂ ≠ b₂ := hne _ _ (by rw [ha₂, hb₂]; exact hyz)
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [ha₁, hc₁y]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [ha₁, hc₂z]; exact hxz)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [ha₂, hc₂z]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hb₁x, hc₁y]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hb₁x, hc₂z]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hb₂, hc₁y]; exact hyz.symm)
  have hσσ : ∀ v, (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) = v :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  -- the twisted successor clause from the twisted cyclic order (one component on both sides)
  have hsucc : ∀ v, Ψ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (D_H.nextVisit ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) =
      D_L.nextVisit (Ψ v) := by
    let Φ' : D_H.Γ.Visit ≃ D_L.Γ.Visit :=
      (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)).trans Ψ
    have hcomp : ∀ v w, D_L.compOf (Φ' v) = D_L.compOf (Φ' w) ↔ D_H.compOf v = D_H.compOf w :=
      fun v w => ⟨fun _ => w3bh_compOf_eq_of_one D_H hH v w, fun _ => w3bh_compOf_eq_of_one D_L hL _ _⟩
    have hbetw : ∀ v w u, D_H.compOf w = D_H.compOf v → D_H.compOf u = D_H.compOf v →
        (D_L.VisitBetween (Φ' v) (Φ' w) (Φ' u) ↔ D_H.VisitBetween v w u) := by
      intro v w u _ _
      have := hcyc ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
      rw [hσσ, hσσ, hσσ] at this
      exact this
    intro v
    have key := D_H.nextVisit_comm_of_visitBetween_iff Φ' hcomp hbetw
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
    simp only [Φ', Equiv.trans_apply, hσσ] at key
    exact key
  -- the crossings of `D_L`
  have hΨfst := w3bh_fst_eq_iff_of_twin Ψ htw
  have hxyL : x_L ≠ y_L := by
    rw [← hxL, ← hyL, Ne, hΨfst, ha₁, ha₂]; exact hxy
  have hxzL : x_L ≠ z_L := by
    rw [← hxL, ← hzL, Ne, hΨfst, ha₁, hb₂]; exact hxz
  have hyzL : y_L ≠ z_L := by
    rw [← hyL, ← hzL, Ne, hΨfst, ha₂, hb₂]; exact hyz
  -- the two bridges
  obtain ⟨ιH⟩ := w3bh_reduced_to_smooth D_H x_H y_H z_H a₁ a₂ b₂ c₁ c₂ ha₁ ha₂ hc₁ hb₂ hc₂ hεH
    yH0 zH0 hyH0 hzH0 B_H hBHy hBHz
  obtain ⟨ιL⟩ := w3bh_reduced_to_smooth D_L x_L y_L z_L (Ψ a₁) (Ψ a₂) (Ψ b₂) (Ψ c₁) (Ψ c₂) hxL hyL
    (by rw [hc₁, htw]) hzL (by rw [hc₂, htw]) hεL yL0 zL0 hyL0 hzL0 B_L hBLy hBLz
  -- the core
  have hcr : ∀ u v : D_H.Γ.Visit, u.1 ≠ v.1 → D_H.record.crossingOf u ≠ D_H.record.crossingOf v :=
    fun u v h h' => h ((w3bh_record_crossingOf_eq_iff D_H u v).mp h')
  obtain ⟨κ⟩ := w3h_record_core D_H.record D_L.record (D_H.record_componentCount.trans hH)
    (D_L.record_componentCount.trans hL) Ψ a₁ a₂ b₁ b₂ c₁ c₂ hb₁.symm hc₁.symm hc₂.symm
    (hcr _ _ (by rw [ha₁, ha₂]; exact hxy)) (hcr _ _ (by rw [ha₁, hb₂]; exact hxz))
    (hcr _ _ (by rw [ha₂, hb₂]; exact hyz)) hadj_e hadj_f hadj_g htw hbit hsgn hsucc
  exact ⟨ιH.trans (κ.trans ιL.symm)⟩


end Row177_6

/-! ## 6. UNIT REAL (Wave 3b): the two realisers and the F-177-2 interface replay (prefix `w3bi_`)

(a) `w3bi_switch_riii` realises `esc_MoveData.switch_riii` from `w3e_strong_case_sw` (PROVED); (b) the site data β1′
`w3bi_site_data` (PROVED by unit SITE, `w3bi_site_data_data`) and the wall data β2 `w3bi_wall_data` (PROVED:
`w3bi_wallEquiv`, `w3bi_wall_data_lift`, `w3bi_adjacent_lift_proof`), glued by `w3bi_hrec_general` (the `ST/ST` case is
`w3h_hrec`) — consumed, in the value form of unit NONKINK (`w3dk_rii_value_sites_data`), by the record-clause chain of
unit KNOT (`w3ck_esc_interface_ext_occ`, `w3ck_esc_outer_occ`, `w3ck_esc_ledger`, `w3ck_extreme_selected`).
(W3D assembler) The Wave-3b interface Props of this unit (`w3bi_esc_interface_ext`, `w3bi_esc_outer`, `w3bi_rii_sites`,
`w3bi_bigon_pair`, the weak move data `w3bi_esc_MoveDataWeak` with `w3bi_knot_after_two` / `w3bi_three_components`), its
replayed ledger and its terminal `w3bi_extreme_selected` were superseded by that chain and removed here
(OPEN_ITEMS §A-18 item 2, W3D_ASSEMBLY_REPORT.md §2).  Report: `W3B_REAL_REPORT.md`. -/
section W3BI_REAL
open RProof SM.GeoCarrier SM.Carrier Smoothing
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- an alternating triple stays alternating under the relabelling `f ↔ g` (`strandSign P g f = -strandSign P f g`) -/
theorem w3bi_alt_swap {P : LabelledTuple n} {e f g : ZMod n}
    (h : IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g)) :
    IsAlternating (strandSign P e g) (strandSign P e f) (strandSign P g f) := by
  rw [show strandSign P g f = -strandSign P f g from crossingSign_swap P f g]
  unfold IsAlternating at h ⊢
  generalize strandSign P e f = sa at *
  generalize strandSign P e g = sb at *
  generalize strandSign P f g = sc at *
  revert h sa sb sc
  decide

/-- **(a) the realiser of `esc_MoveData.switch_riii`** at a configuration of the (extended) interface:
`D_H = carrierDiagram (K3 side) = geoPositiveLift`, `D_L` likewise on the empty side; the contact carrier
`q₀'` is the wall image of `q₀` (`esc_contact_unique`), `hcarr` from `GT_empty_wall`, `htri` from
`esc_contact_owns`, `hX` from `hL.gauss_words`, `hdet` from `hR.sign_eq`, the flipped strand-sign triple
non-alternating from `w3e_alt_of_completeLocal` and the nonzero signs `SEL_strandSigns_ne_zero hGT` (D3);
`sw := 0` in the main case, `sw := 1` after the relabelling `f ↔ g` (as `GT_G11_strong_proof`). -/
theorem w3bi_switch_riii (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀ : GeoComponent (geomAt E t ht.1) Q)
    (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q))
    (hq₀ : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀)
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀')
    (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
    (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing)
    (hxH : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H =
      crossingPoint (xPair hef))
    (hxL : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
      crossingPoint (xPair ((hs _).mp hef))) :
    esc_switch_riii (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
      (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_H x_L := by
  have hef₀ : e ≠ f := P1.ne_of_isCrossing_pair hef
  have heg₀ : e ≠ g := P1.ne_of_isCrossing_pair heg
  have hfg₀ : f ≠ g := P1.ne_of_isCrossing_pair hfg
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  -- the wall and the transported contact carrier
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hcarr := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀'' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hcarr, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have hq₀eq : q₀' = GT_carrierEquiv W q₀ :=
    esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀' hq₀''
  subst hq₀eq
  -- the wall data
  have hX := hL.gauss_words t t' ht ht' hop hs
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  have halt := w3e_alt_of_completeLocal hGT t ht hef heg hfg hK
  obtain ⟨ha, hb, -⟩ := SEL_strandSigns_ne_zero hGT t ht
  unfold esc_switch_riii
  unfold CV.carrierDiagram at x_H x_L hxH hxL ⊢
  rcases lt_or_gt_of_ne (G11_param_ne (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
      hfg₀ hef heg) with hord | hord
  · -- main case: `x = x_ef`, `sw = 0`
    exact (w3e_strong_case_sw hn _ _ hs _ _ q₀ _ hef₀ heg₀ hfg₀ hef heg hfg hX hdet hcarr hTq₀ hord 0
      (w3e_trans_sw_of_alt _ _ _ ha halt 0) x_H x_L hxH hxL).symm
  · -- relabelled case `f ↔ g`: `x = x_ef` is the SECOND crossing along `e`, `sw = 1`
    exact (w3e_strong_case_sw hn _ _ hs _ _ q₀ _ heg₀ hef₀ (Ne.symm hfg₀) heg hef (G11_isCrossing_comm hfg)
      (G11_exact_swap hs hX) hdet hcarr (by rw [G11_triangleCrossings_swap]; exact hTq₀) hord 1
      (w3e_trans_sw_of_alt _ _ _ hb (w3bi_alt_swap halt) 1) x_H x_L hxH hxL).symm


/-! ### W3C SPLITA — `esc_FullSplitData` fields `touching_iff`, `distinct`, `central_no_piece`, `central_rot` (prefix `w3ca_`)

The carrier split of `Q' ∪ T'` on the empty side (ESC §1, §4–§5), first four fields.  Route: the six
triangle visits `a_e, a_f, b_e, b_g, c_g, c_f` are pairwise adjacent along the three edges
(`GT_adjacent_of_shared`, R-LOC-2 (2b)); the independence of `Q' ∪ T'` alone
(`geoIndependent_remaining_pair_owners`, `geoIndependent_selected_pair_owners_ne`, `geoOwner_eq_of_subset`
along `Q' ⊂ Q' ∪ {a} ⊂ Q' ∪ {a, b} ⊂ Q' ∪ T'`) forces the coherent orientation of the three adjacencies
(`w3ca_pattern`: the word `a b | b c | c a` or its mirror), whence the smoothing successor of `Q' ∪ T'`
has the `3`-cycle `Z` on the three inner visits and the three outer visits lie on three further
carriers `A, B, C`, pairwise distinct (`w3ca_core`).  No traversal-position or piece geometry is
used; `central_no_piece` follows because `Z` owns only selected visits, and `central_rot` because
`Z` has exactly three corners (`w3ca_cornerCount_three`) and a regular `3`-gon has `|rot| = 1`
(`CV.rot_triangle`, lem:uniformrot (i)).  The four carriers are the named definitions `w3ca_A`,
`w3ca_B`, `w3ca_C`, `w3ca_Z` (selected by the orientation of the edge-`e` adjacency);
`w3ca_split_at_outer` / `w3ca_central_rot_at_outer` state the four fields at the binders of
`w3bi_esc_outer` (the black box `w3bi_esc_outer_data` itself stays open: its remaining fields
`writhe`, `mixed`, `outer_alternative`, `uniform` and the two move clauses are other units').
For those units: `w3ca_marks_partition(_config)` — the marks of `A ∪ B ∪ C ∪ Z` are exactly the marks
of the contact carrier `q₀'` of `Q'`. -/

section W3CA_Core
variable {P : LabelledTuple n}

attribute [local instance high] Classical.propDecidable

theorem w3ca_geoIndependent_mono (hP : CrossingGeometry P) {S T : Finset (Crossing P)}
    (hTS : T ⊆ S) (hS : GeoIndependent hP S) : GeoIndependent hP T :=
  fun x hx y hy hxy => hS x (hTS hx) y (hTS hy) hxy

theorem w3ca_owner_of_succ (hP : CrossingGeometry P) (T : Finset (Crossing P)) {m m' : Mark P}
    (h : geoSmoothingSuccessor hP T m = m') : geoOwner hP T m' = geoOwner hP T m := by
  rw [← h]; exact geoOwner_successor hP T m

/-- **The six-visit data of the triangle on the empty side** (abstract form): three crossings
`a = a₁.1 = a₂.1`, `b`, `c` outside the support `Q`, pairwise distinct, with twin visits
`a₁ ↔ a₂`, `b₁ ↔ b₂`, `c₁ ↔ c₂`, and the three edge adjacencies of the traversal circle:
`a₁, b₁` consecutive marks (edge `e`), `b₂, c₁` consecutive (edge `g`), `c₂, a₂` consecutive
(edge `f`). -/
structure w3ca_SixData (hP : CrossingGeometry P) (Q : Finset (Crossing P))
    (a₁ a₂ b₁ b₂ c₁ c₂ : Visit P) : Prop where
  ta : visitTwin a₁ = a₂
  ta' : visitTwin a₂ = a₁
  tb : visitTwin b₁ = b₂
  tb' : visitTwin b₂ = b₁
  tc : visitTwin c₁ = c₂
  tc' : visitTwin c₂ = c₁
  a12 : a₂.1 = a₁.1
  b12 : b₂.1 = b₁.1
  c12 : c₂.1 = c₁.1
  ab : a₁.1 ≠ b₁.1
  ac : a₁.1 ≠ c₁.1
  bc : b₁.1 ≠ c₁.1
  aQ : a₁.1 ∉ Q
  bQ : b₁.1 ∉ Q
  cQ : c₁.1 ∉ Q
  adj_e : geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ ∨ geoMarkSuccessor hP (Sum.inr b₁) = Sum.inr a₁
  adj_g : geoMarkSuccessor hP (Sum.inr b₂) = Sum.inr c₁ ∨ geoMarkSuccessor hP (Sum.inr c₁) = Sum.inr b₂
  adj_f : geoMarkSuccessor hP (Sum.inr c₂) = Sum.inr a₂ ∨ geoMarkSuccessor hP (Sum.inr a₂) = Sum.inr c₂

/-- **The non-interlaced pattern**: on the traversal circle the six visits read `a₁ b₁ | b₂ c₁ | c₂ a₂`
(each edge pair oriented the same way) or its mirror — the three adjacencies are coherently
oriented.  Proved from the independence of `Q ∪ {a, b, c}` alone (the incoherent orientations put
the two visits of one selected crossing on one carrier of `Q ∪ {a}` or of `Q ∪ {a, b}`). -/
theorem w3ca_pattern (hP : CrossingGeometry P) {Q : Finset (Crossing P)} {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P}
    (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂)
    (hS : GeoIndependent hP (insert c₁.1 (insert b₁.1 (insert a₁.1 Q)))) :
    (geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ ∧ geoMarkSuccessor hP (Sum.inr b₂) = Sum.inr c₁ ∧
      geoMarkSuccessor hP (Sum.inr c₂) = Sum.inr a₂) ∨
    (geoMarkSuccessor hP (Sum.inr b₁) = Sum.inr a₁ ∧ geoMarkSuccessor hP (Sum.inr c₁) = Sum.inr b₂ ∧
      geoMarkSuccessor hP (Sum.inr a₂) = Sum.inr c₂) := by
  set Q₁ := insert a₁.1 Q with hQ₁
  set Q₂ := insert b₁.1 Q₁ with hQ₂
  set S := insert c₁.1 Q₂ with hSdef
  have hQ₁S : Q₁ ⊆ S := fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  have hQ₂S : Q₂ ⊆ S := fun x hx => Finset.mem_insert_of_mem hx
  have hS₁ : GeoIndependent hP Q₁ := w3ca_geoIndependent_mono hP hQ₁S hS
  have hS₂ : GeoIndependent hP Q₂ := w3ca_geoIndependent_mono hP hQ₂S hS
  have ha₁Q₁ : a₁.1 ∈ Q₁ := Finset.mem_insert_self _ _
  have ha₂Q₁ : a₂.1 ∈ Q₁ := by rw [D.a12]; exact ha₁Q₁
  have hb₁Q₁ : b₁.1 ∉ Q₁ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.ab h.symm
    · exact D.bQ h
  have hb₂Q₁ : b₂.1 ∉ Q₁ := by rw [D.b12]; exact hb₁Q₁
  have hc₁Q₁ : c₁.1 ∉ Q₁ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.ac h.symm
    · exact D.cQ h
  have hc₂Q₁ : c₂.1 ∉ Q₁ := by rw [D.c12]; exact hc₁Q₁
  have hb₁Q₂ : b₁.1 ∈ Q₂ := Finset.mem_insert_self _ _
  have hb₂Q₂ : b₂.1 ∈ Q₂ := by rw [D.b12]; exact hb₁Q₂
  have ha₁Q₂ : a₁.1 ∈ Q₂ := Finset.mem_insert_of_mem ha₁Q₁
  have ha₂Q₂ : a₂.1 ∈ Q₂ := by rw [D.a12]; exact ha₁Q₂
  have hc₁Q₂ : c₁.1 ∉ Q₂ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.bc h.symm
    · exact hc₁Q₁ h
  have hc₂Q₂ : c₂.1 ∉ Q₂ := by rw [D.c12]; exact hc₁Q₂
  have hc₁S : c₁.1 ∈ S := Finset.mem_insert_self _ _
  have hb₁S : b₁.1 ∈ S := hQ₂S hb₁Q₂
  -- successors on the two intermediate supports
  have s1a₁ : geoSmoothingSuccessor hP Q₁ (Sum.inr a₁) = geoMarkSuccessor hP (Sum.inr a₂) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₁ a₁ ha₁Q₁, D.ta]
  have s1a₂ : geoSmoothingSuccessor hP Q₁ (Sum.inr a₂) = geoMarkSuccessor hP (Sum.inr a₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₁ a₂ ha₂Q₁, D.ta']
  have s1b₁ : geoSmoothingSuccessor hP Q₁ (Sum.inr b₁) = geoMarkSuccessor hP (Sum.inr b₁) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₁ b₁ hb₁Q₁
  have s1b₂ : geoSmoothingSuccessor hP Q₁ (Sum.inr b₂) = geoMarkSuccessor hP (Sum.inr b₂) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₁ b₂ hb₂Q₁
  have s1c₁ : geoSmoothingSuccessor hP Q₁ (Sum.inr c₁) = geoMarkSuccessor hP (Sum.inr c₁) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₁ c₁ hc₁Q₁
  have s1c₂ : geoSmoothingSuccessor hP Q₁ (Sum.inr c₂) = geoMarkSuccessor hP (Sum.inr c₂) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₁ c₂ hc₂Q₁
  have s2a₁ : geoSmoothingSuccessor hP Q₂ (Sum.inr a₁) = geoMarkSuccessor hP (Sum.inr a₂) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₂ a₁ ha₁Q₂, D.ta]
  have s2a₂ : geoSmoothingSuccessor hP Q₂ (Sum.inr a₂) = geoMarkSuccessor hP (Sum.inr a₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₂ a₂ ha₂Q₂, D.ta']
  have s2b₁ : geoSmoothingSuccessor hP Q₂ (Sum.inr b₁) = geoMarkSuccessor hP (Sum.inr b₂) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₂ b₁ hb₁Q₂, D.tb]
  have s2b₂ : geoSmoothingSuccessor hP Q₂ (Sum.inr b₂) = geoMarkSuccessor hP (Sum.inr b₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₂ b₂ hb₂Q₂, D.tb']
  have s2c₁ : geoSmoothingSuccessor hP Q₂ (Sum.inr c₁) = geoMarkSuccessor hP (Sum.inr c₁) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₂ c₁ hc₁Q₂
  have s2c₂ : geoSmoothingSuccessor hP Q₂ (Sum.inr c₂) = geoMarkSuccessor hP (Sum.inr c₂) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₂ c₂ hc₂Q₂
  -- owner facts
  have hne₁ : geoOwner hP Q₁ (Sum.inr a₁) ≠ geoOwner hP Q₁ (Sum.inr a₂) := by
    have := geoIndependent_selected_pair_owners_ne hP hS₁ a₁ ha₁Q₁
    rwa [D.ta] at this
  have hne₂ : geoOwner hP Q₂ (Sum.inr b₁) ≠ geoOwner hP Q₂ (Sum.inr b₂) := by
    have := geoIndependent_selected_pair_owners_ne hP hS₂ b₁ hb₁Q₂
    rwa [D.tb] at this
  have hb₁₂ : geoOwner hP Q₁ (Sum.inr b₁) = geoOwner hP Q₁ (Sum.inr b₂) := by
    have := geoIndependent_remaining_pair_owners hP hS Q₁ hQ₁S b₁ hb₁S hb₁Q₁
    rwa [D.tb] at this
  have hc₁₂ : geoOwner hP Q₁ (Sum.inr c₁) = geoOwner hP Q₁ (Sum.inr c₂) := by
    have := geoIndependent_remaining_pair_owners hP hS Q₁ hQ₁S c₁ hc₁S hc₁Q₁
    rwa [D.tc] at this
  have hc₁₂' : geoOwner hP Q₂ (Sum.inr c₁) = geoOwner hP Q₂ (Sum.inr c₂) := by
    have := geoIndependent_remaining_pair_owners hP hS Q₂ hQ₂S c₁ hc₁S hc₁Q₂
    rwa [D.tc] at this
  rcases D.adj_e with h1 | h1
  · left
    have ob₁ : geoOwner hP Q₁ (Sum.inr b₁) = geoOwner hP Q₁ (Sum.inr a₂) :=
      w3ca_owner_of_succ hP Q₁ (s1a₂.trans h1)
    have h3 : geoMarkSuccessor hP (Sum.inr c₂) = Sum.inr a₂ := by
      rcases D.adj_f with h3 | h3
      · exact h3
      · exfalso
        have oc₂ : geoOwner hP Q₁ (Sum.inr c₂) = geoOwner hP Q₁ (Sum.inr a₁) :=
          w3ca_owner_of_succ hP Q₁ (s1a₁.trans h3)
        rcases D.adj_g with h2 | h2
        · have h' : geoOwner hP Q₁ (Sum.inr c₁) = geoOwner hP Q₁ (Sum.inr b₂) :=
            w3ca_owner_of_succ hP Q₁ (s1b₂.trans h2)
          exact hne₁ (oc₂.symm.trans (hc₁₂.symm.trans (h'.trans (hb₁₂.symm.trans ob₁))))
        · have h' : geoOwner hP Q₁ (Sum.inr b₂) = geoOwner hP Q₁ (Sum.inr c₁) :=
            w3ca_owner_of_succ hP Q₁ (s1c₁.trans h2)
          exact hne₁ (oc₂.symm.trans (hc₁₂.symm.trans (h'.symm.trans (hb₁₂.symm.trans ob₁))))
    have h2 : geoMarkSuccessor hP (Sum.inr b₂) = Sum.inr c₁ := by
      rcases D.adj_g with h2 | h2
      · exact h2
      · exfalso
        have o1 : geoOwner hP Q₂ (Sum.inr b₁) = geoOwner hP Q₂ (Sum.inr a₂) :=
          w3ca_owner_of_succ hP Q₂ (s2a₂.trans h1)
        have o2 : geoOwner hP Q₂ (Sum.inr a₂) = geoOwner hP Q₂ (Sum.inr c₂) :=
          w3ca_owner_of_succ hP Q₂ (s2c₂.trans h3)
        have o3 : geoOwner hP Q₂ (Sum.inr b₂) = geoOwner hP Q₂ (Sum.inr c₁) :=
          w3ca_owner_of_succ hP Q₂ (s2c₁.trans h2)
        exact hne₂ (o1.trans (o2.trans (hc₁₂'.symm.trans o3.symm)))
    exact ⟨h1, h2, h3⟩
  · right
    have oa₁ : geoOwner hP Q₁ (Sum.inr a₁) = geoOwner hP Q₁ (Sum.inr b₁) :=
      w3ca_owner_of_succ hP Q₁ (s1b₁.trans h1)
    have h3 : geoMarkSuccessor hP (Sum.inr a₂) = Sum.inr c₂ := by
      rcases D.adj_f with h3 | h3
      · exfalso
        have oa₂ : geoOwner hP Q₁ (Sum.inr a₂) = geoOwner hP Q₁ (Sum.inr c₂) :=
          w3ca_owner_of_succ hP Q₁ (s1c₂.trans h3)
        rcases D.adj_g with h2 | h2
        · have h' : geoOwner hP Q₁ (Sum.inr c₁) = geoOwner hP Q₁ (Sum.inr b₂) :=
            w3ca_owner_of_succ hP Q₁ (s1b₂.trans h2)
          exact hne₁ (oa₁.trans (hb₁₂.trans (h'.symm.trans (hc₁₂.trans oa₂.symm))))
        · have h' : geoOwner hP Q₁ (Sum.inr b₂) = geoOwner hP Q₁ (Sum.inr c₁) :=
            w3ca_owner_of_succ hP Q₁ (s1c₁.trans h2)
          exact hne₁ (oa₁.trans (hb₁₂.trans (h'.trans (hc₁₂.trans oa₂.symm))))
      · exact h3
    have h2 : geoMarkSuccessor hP (Sum.inr c₁) = Sum.inr b₂ := by
      rcases D.adj_g with h2 | h2
      · exfalso
        have o1 : geoOwner hP Q₂ (Sum.inr a₁) = geoOwner hP Q₂ (Sum.inr b₂) :=
          w3ca_owner_of_succ hP Q₂ (s2b₂.trans h1)
        have o2 : geoOwner hP Q₂ (Sum.inr c₂) = geoOwner hP Q₂ (Sum.inr a₁) :=
          w3ca_owner_of_succ hP Q₂ (s2a₁.trans h3)
        have o3 : geoOwner hP Q₂ (Sum.inr c₁) = geoOwner hP Q₂ (Sum.inr b₁) :=
          w3ca_owner_of_succ hP Q₂ (s2b₁.trans h2)
        exact hne₂ (o3.symm.trans (hc₁₂'.trans (o2.trans o1)))
      · exact h2
    exact ⟨h1, h2, h3⟩

/-- The marks of a carrier that is a `3`-cycle `x → y → z → x` of the smoothing successor. -/
theorem w3ca_three_cycle_marks (hP : CrossingGeometry P) (S : Finset (Crossing P)) (x y z : Mark P)
    (hx : geoSmoothingSuccessor hP S x = y) (hy : geoSmoothingSuccessor hP S y = z)
    (hz : geoSmoothingSuccessor hP S z = x) (m : Mark P) :
    geoOwner hP S m = geoOwner hP S x ↔ (m = x ∨ m = y ∨ m = z) := by
  constructor
  · intro h
    have hsc := (geoOwner_eq_iff hP S x m).mp h.symm
    obtain ⟨i, -, hi⟩ := hsc.exists_pow_eq'
    have key : ∀ k : ℕ, (geoSmoothingSuccessor hP S ^ k) x = x ∨
        (geoSmoothingSuccessor hP S ^ k) x = y ∨ (geoSmoothingSuccessor hP S ^ k) x = z := by
      intro k
      induction k with
      | zero => left; rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h | h <;> rw [h]
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hy)
        · exact Or.inl hz
    rw [← hi]
    exact key i
  · rintro (rfl | rfl | rfl)
    · rfl
    · rw [← hx]; exact geoOwner_successor hP S x
    · rw [← hy, ← hx]; exact (geoOwner_successor hP S _).trans (geoOwner_successor hP S x)

/-- **The output of the split** (abstract form): the carriers `A, B, C, Z` of `S = Q ∪ {a, b, c}`
own the six visits (`six`, each of the four owns one: `hit*`), are pairwise distinct, and `Z` is the
central triangle: its marks are exactly three visits, one of each of `a, b, c`. -/
structure w3ca_CoreData (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a₁ a₂ b₁ b₂ c₁ c₂ : Visit P) (A B C Z : GeoComponent hP S) : Prop where
  six : ∀ v : Visit P, (v = a₁ ∨ v = a₂ ∨ v = b₁ ∨ v = b₂ ∨ v = c₁ ∨ v = c₂) →
    geoOwner hP S (Sum.inr v) = A ∨ geoOwner hP S (Sum.inr v) = B ∨
      geoOwner hP S (Sum.inr v) = C ∨ geoOwner hP S (Sum.inr v) = Z
  hitA : ∃ v : Visit P, (v = a₁ ∨ v = a₂ ∨ v = b₁ ∨ v = b₂ ∨ v = c₁ ∨ v = c₂) ∧
    geoOwner hP S (Sum.inr v) = A
  hitB : ∃ v : Visit P, (v = a₁ ∨ v = a₂ ∨ v = b₁ ∨ v = b₂ ∨ v = c₁ ∨ v = c₂) ∧
    geoOwner hP S (Sum.inr v) = B
  hitC : ∃ v : Visit P, (v = a₁ ∨ v = a₂ ∨ v = b₁ ∨ v = b₂ ∨ v = c₁ ∨ v = c₂) ∧
    geoOwner hP S (Sum.inr v) = C
  hitZ : ∃ v : Visit P, (v = a₁ ∨ v = a₂ ∨ v = b₁ ∨ v = b₂ ∨ v = c₁ ∨ v = c₂) ∧
    geoOwner hP S (Sum.inr v) = Z
  distinct : A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z
  /-- the central triangle: exactly one visit of each of `a, b, c`, nothing else -/
  central : ∃ zA zB zC : Visit P, zA.1 = a₁.1 ∧ zB.1 = b₁.1 ∧ zC.1 = c₁.1 ∧
    ∀ m : Mark P, geoOwner hP S m = Z ↔ (m = Sum.inr zA ∨ m = Sum.inr zB ∨ m = Sum.inr zC)


/-- **The central triangle `Z`** (abstract form): the carrier of the second `a`-visit when the edge
`e` reads `a₁ b₁`, of the first when it reads `b₁ a₁` (the mirror pattern of `w3ca_pattern`). -/
noncomputable def w3ca_Zc (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a₁ a₂ b₁ : Visit P) :
    GeoComponent hP S :=
  if geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ then geoOwner hP S (Sum.inr a₂)
  else geoOwner hP S (Sum.inr a₁)

/-- **The outer carrier `A`** (abstract form): the carrier of the other `a`-visit. -/
noncomputable def w3ca_Ac (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a₁ a₂ b₁ : Visit P) :
    GeoComponent hP S :=
  if geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ then geoOwner hP S (Sum.inr a₁)
  else geoOwner hP S (Sum.inr a₂)

/-- **The outer carrier `B`** (abstract form): the carrier of the outer `b`-visit. -/
noncomputable def w3ca_Bc (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a₁ b₁ b₂ : Visit P) :
    GeoComponent hP S :=
  if geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ then geoOwner hP S (Sum.inr b₂)
  else geoOwner hP S (Sum.inr b₁)

/-- **The outer carrier `C`** (abstract form): the carrier of the outer `c`-visit. -/
noncomputable def w3ca_Cc (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a₁ b₁ c₁ c₂ : Visit P) :
    GeoComponent hP S :=
  if geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ then geoOwner hP S (Sum.inr c₂)
  else geoOwner hP S (Sum.inr c₁)

/-- **The carrier split of `Q ∪ {a, b, c}`** (abstract form of `esc_FullSplitData`'s `touching_iff`,
`distinct`, `central_no_piece`): from the six-visit data and the independence of the support. -/
theorem w3ca_core (hP : CrossingGeometry P) {Q : Finset (Crossing P)} {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P}
    (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂) (S : Finset (Crossing P))
    (hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = a₁.1 ∨ x = b₁.1 ∨ x = c₁.1) (hS : GeoIndependent hP S) :
    w3ca_CoreData hP S a₁ a₂ b₁ b₂ c₁ c₂ (w3ca_Ac hP S a₁ a₂ b₁) (w3ca_Bc hP S a₁ b₁ b₂)
      (w3ca_Cc hP S a₁ b₁ c₁ c₂) (w3ca_Zc hP S a₁ a₂ b₁) := by
  have hSdef : S = insert c₁.1 (insert b₁.1 (insert a₁.1 Q)) := by
    ext x
    rw [hSeq]
    simp only [Finset.mem_insert]
    tauto
  subst hSdef
  set Q₁ := insert a₁.1 Q with hQ₁
  set Q₂ := insert b₁.1 Q₁ with hQ₂
  set S := insert c₁.1 Q₂ with hSdef
  have hQ₁S : Q₁ ⊆ S := fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  have hQ₂S : Q₂ ⊆ S := fun x hx => Finset.mem_insert_of_mem hx
  have ha₁Q₁ : a₁.1 ∈ Q₁ := Finset.mem_insert_self _ _
  have ha₂Q₁ : a₂.1 ∈ Q₁ := by rw [D.a12]; exact ha₁Q₁
  have hb₁Q₁ : b₁.1 ∉ Q₁ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.ab h.symm
    · exact D.bQ h
  have hb₂Q₁ : b₂.1 ∉ Q₁ := by rw [D.b12]; exact hb₁Q₁
  have hc₁Q₁ : c₁.1 ∉ Q₁ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.ac h.symm
    · exact D.cQ h
  have hc₂Q₁ : c₂.1 ∉ Q₁ := by rw [D.c12]; exact hc₁Q₁
  have hb₁Q₂ : b₁.1 ∈ Q₂ := Finset.mem_insert_self _ _
  have hb₂Q₂ : b₂.1 ∈ Q₂ := by rw [D.b12]; exact hb₁Q₂
  have ha₁Q₂ : a₁.1 ∈ Q₂ := Finset.mem_insert_of_mem ha₁Q₁
  have ha₂Q₂ : a₂.1 ∈ Q₂ := by rw [D.a12]; exact ha₁Q₂
  have hc₁Q₂ : c₁.1 ∉ Q₂ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.bc h.symm
    · exact hc₁Q₁ h
  have hc₂Q₂ : c₂.1 ∉ Q₂ := by rw [D.c12]; exact hc₁Q₂
  have hc₁S : c₁.1 ∈ S := Finset.mem_insert_self _ _
  have hc₂S : c₂.1 ∈ S := by rw [D.c12]; exact hc₁S
  have hb₁S : b₁.1 ∈ S := hQ₂S hb₁Q₂
  have hb₂S : b₂.1 ∈ S := by rw [D.b12]; exact hb₁S
  have ha₁S : a₁.1 ∈ S := hQ₁S ha₁Q₁
  have ha₂S : a₂.1 ∈ S := by rw [D.a12]; exact ha₁S
  -- successors
  have s1a₁ : geoSmoothingSuccessor hP Q₁ (Sum.inr a₁) = geoMarkSuccessor hP (Sum.inr a₂) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₁ a₁ ha₁Q₁, D.ta]
  have s1a₂ : geoSmoothingSuccessor hP Q₁ (Sum.inr a₂) = geoMarkSuccessor hP (Sum.inr a₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₁ a₂ ha₂Q₁, D.ta']
  have s1b₁ : geoSmoothingSuccessor hP Q₁ (Sum.inr b₁) = geoMarkSuccessor hP (Sum.inr b₁) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₁ b₁ hb₁Q₁
  have s1c₂ : geoSmoothingSuccessor hP Q₁ (Sum.inr c₂) = geoMarkSuccessor hP (Sum.inr c₂) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₁ c₂ hc₂Q₁
  have s2a₁ : geoSmoothingSuccessor hP Q₂ (Sum.inr a₁) = geoMarkSuccessor hP (Sum.inr a₂) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₂ a₁ ha₁Q₂, D.ta]
  have s2a₂ : geoSmoothingSuccessor hP Q₂ (Sum.inr a₂) = geoMarkSuccessor hP (Sum.inr a₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₂ a₂ ha₂Q₂, D.ta']
  have s2b₂ : geoSmoothingSuccessor hP Q₂ (Sum.inr b₂) = geoMarkSuccessor hP (Sum.inr b₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP Q₂ b₂ hb₂Q₂, D.tb']
  have s2c₂ : geoSmoothingSuccessor hP Q₂ (Sum.inr c₂) = geoMarkSuccessor hP (Sum.inr c₂) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q₂ c₂ hc₂Q₂
  have sSa₁ : geoSmoothingSuccessor hP S (Sum.inr a₁) = geoMarkSuccessor hP (Sum.inr a₂) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP S a₁ ha₁S, D.ta]
  have sSa₂ : geoSmoothingSuccessor hP S (Sum.inr a₂) = geoMarkSuccessor hP (Sum.inr a₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP S a₂ ha₂S, D.ta']
  have sSb₁ : geoSmoothingSuccessor hP S (Sum.inr b₁) = geoMarkSuccessor hP (Sum.inr b₂) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP S b₁ hb₁S, D.tb]
  have sSb₂ : geoSmoothingSuccessor hP S (Sum.inr b₂) = geoMarkSuccessor hP (Sum.inr b₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP S b₂ hb₂S, D.tb']
  have sSc₁ : geoSmoothingSuccessor hP S (Sum.inr c₁) = geoMarkSuccessor hP (Sum.inr c₂) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP S c₁ hc₁S, D.tc]
  have sSc₂ : geoSmoothingSuccessor hP S (Sum.inr c₂) = geoMarkSuccessor hP (Sum.inr c₁) := by
    rw [geoSmoothingSuccessor_visit_of_mem hP S c₂ hc₂S, D.tc']
  -- owner facts
  have hS₁ : GeoIndependent hP Q₁ := w3ca_geoIndependent_mono hP hQ₁S hS
  have hS₂ : GeoIndependent hP Q₂ := w3ca_geoIndependent_mono hP hQ₂S hS
  have hne₁ : geoOwner hP Q₁ (Sum.inr a₁) ≠ geoOwner hP Q₁ (Sum.inr a₂) := by
    have := geoIndependent_selected_pair_owners_ne hP hS₁ a₁ ha₁Q₁
    rwa [D.ta] at this
  have hne₂ : geoOwner hP Q₂ (Sum.inr b₁) ≠ geoOwner hP Q₂ (Sum.inr b₂) := by
    have := geoIndependent_selected_pair_owners_ne hP hS₂ b₁ hb₁Q₂
    rwa [D.tb] at this
  have hnA : geoOwner hP S (Sum.inr a₁) ≠ geoOwner hP S (Sum.inr a₂) := by
    have := geoIndependent_selected_pair_owners_ne hP hS a₁ ha₁S
    rwa [D.ta] at this
  have hnB : geoOwner hP S (Sum.inr b₁) ≠ geoOwner hP S (Sum.inr b₂) := by
    have := geoIndependent_selected_pair_owners_ne hP hS b₁ hb₁S
    rwa [D.tb] at this
  have hnC : geoOwner hP S (Sum.inr c₁) ≠ geoOwner hP S (Sum.inr c₂) := by
    have := geoIndependent_selected_pair_owners_ne hP hS c₁ hc₁S
    rwa [D.tc] at this
  have hb₁₂ : geoOwner hP Q₁ (Sum.inr b₁) = geoOwner hP Q₁ (Sum.inr b₂) := by
    have := geoIndependent_remaining_pair_owners hP hS Q₁ hQ₁S b₁ hb₁S hb₁Q₁
    rwa [D.tb] at this
  have hc₁₂ : geoOwner hP Q₁ (Sum.inr c₁) = geoOwner hP Q₁ (Sum.inr c₂) := by
    have := geoIndependent_remaining_pair_owners hP hS Q₁ hQ₁S c₁ hc₁S hc₁Q₁
    rwa [D.tc] at this
  have hc₁₂' : geoOwner hP Q₂ (Sum.inr c₁) = geoOwner hP Q₂ (Sum.inr c₂) := by
    have := geoIndependent_remaining_pair_owners hP hS Q₂ hQ₂S c₁ hc₁S hc₁Q₂
    rwa [D.tc] at this
  have ref₁ : ∀ m m' : Mark P, geoOwner hP S m = geoOwner hP S m' →
      geoOwner hP Q₁ m = geoOwner hP Q₁ m' := fun m m' h => geoOwner_eq_of_subset hP hS hQ₁S m m' h
  have ref₂ : ∀ m m' : Mark P, geoOwner hP S m = geoOwner hP S m' →
      geoOwner hP Q₂ m = geoOwner hP Q₂ m' := fun m m' h => geoOwner_eq_of_subset hP hS hQ₂S m m' h
  rcases w3ca_pattern hP D hS with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- pattern `a₁ b₁ | b₂ c₁ | c₂ a₂`: the central triangle is `a₂ → b₁ → c₁ → a₂`
    have cyc := w3ca_three_cycle_marks hP S (Sum.inr a₂) (Sum.inr b₁) (Sum.inr c₁)
      (sSa₂.trans h1) (sSb₁.trans h2) (sSc₁.trans h3)
    have oZb₁ : geoOwner hP S (Sum.inr b₁) = geoOwner hP S (Sum.inr a₂) :=
      (cyc _).mpr (Or.inr (Or.inl rfl))
    have oZc₁ : geoOwner hP S (Sum.inr c₁) = geoOwner hP S (Sum.inr a₂) :=
      (cyc _).mpr (Or.inr (Or.inr rfl))
    have ob₁ : geoOwner hP Q₁ (Sum.inr b₁) = geoOwner hP Q₁ (Sum.inr a₂) :=
      w3ca_owner_of_succ hP Q₁ (s1a₂.trans h1)
    have oc₂ : geoOwner hP Q₁ (Sum.inr a₂) = geoOwner hP Q₁ (Sum.inr c₂) :=
      w3ca_owner_of_succ hP Q₁ (s1c₂.trans h3)
    have o1 : geoOwner hP Q₂ (Sum.inr b₁) = geoOwner hP Q₂ (Sum.inr a₂) :=
      w3ca_owner_of_succ hP Q₂ (s2a₂.trans h1)
    have o2 : geoOwner hP Q₂ (Sum.inr a₂) = geoOwner hP Q₂ (Sum.inr c₂) :=
      w3ca_owner_of_succ hP Q₂ (s2c₂.trans h3)
    unfold w3ca_Ac w3ca_Bc w3ca_Cc w3ca_Zc
    simp only [h1, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inr oZb₁))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr oZc₁))
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact ⟨a₁, Or.inl rfl, rfl⟩
    · exact ⟨b₂, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
    · exact ⟨c₂, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), rfl⟩
    · exact ⟨a₂, Or.inr (Or.inl rfl), rfl⟩
    · refine ⟨?_, ?_, hnA, ?_, ?_, ?_⟩
      · intro h
        exact hne₁ ((ref₁ _ _ h).trans (hb₁₂.symm.trans ob₁))
      · intro h
        exact hne₁ ((ref₁ _ _ h).trans oc₂.symm)
      · intro h
        exact hne₂ (o1.trans (o2.trans (ref₂ _ _ h).symm))
      · intro h
        exact hnB (oZb₁.trans h.symm)
      · intro h
        exact hnC (oZc₁.trans h.symm)
    · exact ⟨a₂, b₁, c₁, D.a12, rfl, rfl, cyc⟩
  · -- mirror pattern `b₁ a₁ | c₁ b₂ | a₂ c₂`: the central triangle is `a₁ → c₂ → b₂ → a₁`
    have cyc := w3ca_three_cycle_marks hP S (Sum.inr a₁) (Sum.inr c₂) (Sum.inr b₂)
      (sSa₁.trans h3) (sSc₂.trans h2) (sSb₂.trans h1)
    have oZc₂ : geoOwner hP S (Sum.inr c₂) = geoOwner hP S (Sum.inr a₁) :=
      (cyc _).mpr (Or.inr (Or.inl rfl))
    have oZb₂ : geoOwner hP S (Sum.inr b₂) = geoOwner hP S (Sum.inr a₁) :=
      (cyc _).mpr (Or.inr (Or.inr rfl))
    have oa₁ : geoOwner hP Q₁ (Sum.inr a₁) = geoOwner hP Q₁ (Sum.inr b₁) :=
      w3ca_owner_of_succ hP Q₁ (s1b₁.trans h1)
    have oc₂ : geoOwner hP Q₁ (Sum.inr c₂) = geoOwner hP Q₁ (Sum.inr a₁) :=
      w3ca_owner_of_succ hP Q₁ (s1a₁.trans h3)
    have o1 : geoOwner hP Q₂ (Sum.inr a₁) = geoOwner hP Q₂ (Sum.inr b₂) :=
      w3ca_owner_of_succ hP Q₂ (s2b₂.trans h1)
    have o2 : geoOwner hP Q₂ (Sum.inr c₂) = geoOwner hP Q₂ (Sum.inr a₁) :=
      w3ca_owner_of_succ hP Q₂ (s2a₁.trans h3)
    have hn1 : ¬ geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ := by
      intro h1'
      exact hne₁ (oa₁.trans (w3ca_owner_of_succ hP Q₁ (s1a₂.trans h1')))
    unfold w3ca_Ac w3ca_Bc w3ca_Cc w3ca_Zc
    simp only [hn1, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr oZb₂))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr oZc₂))
    · exact ⟨a₂, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨b₁, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨c₁, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
    · exact ⟨a₁, Or.inl rfl, rfl⟩
    · refine ⟨?_, ?_, fun h => hnA h.symm, ?_, ?_, ?_⟩
      · intro h
        exact hne₁ (oa₁.trans (ref₁ _ _ h).symm)
      · intro h
        exact hne₁ (oc₂.symm.trans (hc₁₂.symm.trans (ref₁ _ _ h).symm))
      · intro h
        exact hne₂ ((ref₂ _ _ h).trans (hc₁₂'.trans (o2.trans o1)))
      · intro h
        exact hnB (h.trans oZb₂.symm)
      · intro h
        exact hnC (h.trans oZc₂.symm)
    · exact ⟨a₁, b₂, c₂, rfl, D.b12, D.c12, fun m => (cyc m).trans (or_congr_right or_comm)⟩

/-- All six visits lie on the `Q`-carrier of `a₁` — the contact carrier — from independence
(`geoIndependent_remaining_pair_owners`) and the three edge adjacencies alone. -/
theorem w3ca_six_on_contact (hP : CrossingGeometry P) {Q : Finset (Crossing P)}
    {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P} (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂) (S : Finset (Crossing P))
    (hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = a₁.1 ∨ x = b₁.1 ∨ x = c₁.1) (hS : GeoIndependent hP S) :
    ∀ v : Visit P, (v = a₁ ∨ v = a₂ ∨ v = b₁ ∨ v = b₂ ∨ v = c₁ ∨ v = c₂) →
      geoOwner hP Q (Sum.inr v) = geoOwner hP Q (Sum.inr a₁) := by
  have hQS : Q ⊆ S := fun x hx => (hSeq x).mpr (Or.inl hx)
  have ha₁S : a₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inl rfl))
  have hb₁S : b₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hc₁S : c₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hb₂Q : b₂.1 ∉ Q := by rw [D.b12]; exact D.bQ
  have hc₂Q : c₂.1 ∉ Q := by rw [D.c12]; exact D.cQ
  have oa : geoOwner hP Q (Sum.inr a₂) = geoOwner hP Q (Sum.inr a₁) := by
    have := geoIndependent_remaining_pair_owners hP hS Q hQS a₁ ha₁S D.aQ
    rw [D.ta] at this
    exact this.symm
  have ob : geoOwner hP Q (Sum.inr b₂) = geoOwner hP Q (Sum.inr b₁) := by
    have := geoIndependent_remaining_pair_owners hP hS Q hQS b₁ hb₁S D.bQ
    rw [D.tb] at this
    exact this.symm
  have oc : geoOwner hP Q (Sum.inr c₂) = geoOwner hP Q (Sum.inr c₁) := by
    have := geoIndependent_remaining_pair_owners hP hS Q hQS c₁ hc₁S D.cQ
    rw [D.tc] at this
    exact this.symm
  have sa₁ : geoSmoothingSuccessor hP Q (Sum.inr a₁) = geoMarkSuccessor hP (Sum.inr a₁) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q a₁ D.aQ
  have sb₁ : geoSmoothingSuccessor hP Q (Sum.inr b₁) = geoMarkSuccessor hP (Sum.inr b₁) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q b₁ D.bQ
  have sb₂ : geoSmoothingSuccessor hP Q (Sum.inr b₂) = geoMarkSuccessor hP (Sum.inr b₂) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q b₂ hb₂Q
  have sc₁ : geoSmoothingSuccessor hP Q (Sum.inr c₁) = geoMarkSuccessor hP (Sum.inr c₁) :=
    geoSmoothingSuccessor_visit_of_not_mem hP Q c₁ D.cQ
  have hb : geoOwner hP Q (Sum.inr b₁) = geoOwner hP Q (Sum.inr a₁) := by
    rcases D.adj_e with h | h
    · exact w3ca_owner_of_succ hP Q (sa₁.trans h)
    · exact (w3ca_owner_of_succ hP Q (sb₁.trans h)).symm
  have hc : geoOwner hP Q (Sum.inr c₁) = geoOwner hP Q (Sum.inr a₁) := by
    rcases D.adj_g with h | h
    · exact (w3ca_owner_of_succ hP Q (sb₂.trans h)).trans (ob.trans hb)
    · exact (w3ca_owner_of_succ hP Q (sc₁.trans h)).symm.trans (ob.trans hb)
  rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
  · rfl
  · exact oa
  · exact hb
  · exact ob.trans hb
  · exact hc
  · exact oc.trans hc

/-- **The marks of the four carriers are exactly the marks of the contact carrier**: for every mark
`m`, `m` lies on `A`, `B`, `C` or `Z` in `S = Q ∪ {a, b, c}` iff it lies on the `Q`-carrier of `a₁`
(the three insertions, `geoComponentForgetSwitch_fiber_affected` on the affected block and
`geoOwner_insert_iff_of_unaffected` on the others). -/
theorem w3ca_marks_partition (hP : CrossingGeometry P) {Q : Finset (Crossing P)}
    {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P} (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂) (S : Finset (Crossing P))
    (hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = a₁.1 ∨ x = b₁.1 ∨ x = c₁.1) (hS : GeoIndependent hP S)
    (m : Mark P) :
    (geoOwner hP S m = w3ca_Ac hP S a₁ a₂ b₁ ∨ geoOwner hP S m = w3ca_Bc hP S a₁ b₁ b₂ ∨
      geoOwner hP S m = w3ca_Cc hP S a₁ b₁ c₁ c₂ ∨ geoOwner hP S m = w3ca_Zc hP S a₁ a₂ b₁) ↔
    geoOwner hP Q m = geoOwner hP Q (Sum.inr a₁) := by
  have hcore := w3ca_core hP D S hSeq hS
  have hsix := w3ca_six_on_contact hP D S hSeq hS
  have hSdef : S = insert c₁.1 (insert b₁.1 (insert a₁.1 Q)) := by
    ext x
    rw [hSeq]
    simp only [Finset.mem_insert]
    tauto
  subst hSdef
  set Q₁ := insert a₁.1 Q with hQ₁
  set Q₂ := insert b₁.1 Q₁ with hQ₂
  set S := insert c₁.1 Q₂ with hSdef
  have hQQ₁ : Q ⊆ Q₁ := fun x hx => Finset.mem_insert_of_mem hx
  have hQ₁S : Q₁ ⊆ S := fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  have hQ₂S : Q₂ ⊆ S := fun x hx => Finset.mem_insert_of_mem hx
  have hQS : Q ⊆ S := fun x hx => hQ₁S (hQQ₁ hx)
  have ha₁S : a₁.1 ∈ S := hQ₁S (Finset.mem_insert_self _ _)
  have hb₁Q₁ : b₁.1 ∉ Q₁ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.ab h.symm
    · exact D.bQ h
  have hb₁S : b₁.1 ∈ S := hQ₂S (Finset.mem_insert_self _ _)
  have hc₁Q₂ : c₁.1 ∉ Q₂ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.bc h.symm
    · rcases Finset.mem_insert.mp h with h | h
      · exact D.ac h.symm
      · exact D.cQ h
  have hc₁S : c₁.1 ∈ S := Finset.mem_insert_self _ _
  constructor
  · intro h
    have hex : ∃ v : Visit P, (v = a₁ ∨ v = a₂ ∨ v = b₁ ∨ v = b₂ ∨ v = c₁ ∨ v = c₂) ∧
        geoOwner hP S (Sum.inr v) = geoOwner hP S m := by
      rcases h with h | h | h | h
      · obtain ⟨v, hv6, hv⟩ := hcore.hitA
        exact ⟨v, hv6, hv.trans h.symm⟩
      · obtain ⟨v, hv6, hv⟩ := hcore.hitB
        exact ⟨v, hv6, hv.trans h.symm⟩
      · obtain ⟨v, hv6, hv⟩ := hcore.hitC
        exact ⟨v, hv6, hv.trans h.symm⟩
      · obtain ⟨v, hv6, hv⟩ := hcore.hitZ
        exact ⟨v, hv6, hv.trans h.symm⟩
    obtain ⟨v, hv6, hv⟩ := hex
    exact (geoOwner_eq_of_subset hP hS hQS _ _ hv).symm.trans (hsix v hv6)
  · intro hm
    -- step 1: `Q → Q₁`, the affected block of `a`
    have hI₀ : GeoInheritsMarkOrder hP Q := (geoIndependent_partial_invariants hP hS Q hQS).1
    have hcA : geoOwner hP Q (Sum.inr a₁) = geoOwner hP Q (Sum.inr (visitTwin a₁)) :=
      geoIndependent_remaining_pair_owners hP hS Q hQS a₁ ha₁S D.aQ
    have step1 : geoOwner hP Q₁ m = geoOwner hP Q₁ (Sum.inr a₁) ∨
        geoOwner hP Q₁ m = geoOwner hP Q₁ (Sum.inr a₂) := by
      have hf := (geoComponentForgetSwitch_fiber_affected hP Q hI₀ a₁ D.aQ hcA).2
      have hmem := (Finset.ext_iff.mp hf (geoOwner hP Q₁ m)).mp
        (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hm⟩)
      rw [Finset.mem_insert, Finset.mem_singleton, D.ta] at hmem
      exact hmem
    -- step 2: `Q₁ → Q₂`
    have hI₁ : GeoInheritsMarkOrder hP Q₁ := (geoIndependent_partial_invariants hP hS Q₁ hQ₁S).1
    have hcB : geoOwner hP Q₁ (Sum.inr b₁) = geoOwner hP Q₁ (Sum.inr (visitTwin b₁)) :=
      geoIndependent_remaining_pair_owners hP hS Q₁ hQ₁S b₁ hb₁S hb₁Q₁
    have step2 : geoOwner hP Q₂ m = geoOwner hP Q₂ (Sum.inr a₁) ∨
        geoOwner hP Q₂ m = geoOwner hP Q₂ (Sum.inr a₂) ∨
        geoOwner hP Q₂ m = geoOwner hP Q₂ (Sum.inr b₁) ∨
        geoOwner hP Q₂ m = geoOwner hP Q₂ (Sum.inr b₂) := by
      by_cases hmb : geoOwner hP Q₁ m = geoOwner hP Q₁ (Sum.inr b₁)
      · have hf := (geoComponentForgetSwitch_fiber_affected hP Q₁ hI₁ b₁ hb₁Q₁ hcB).2
        have hmem := (Finset.ext_iff.mp hf (geoOwner hP Q₂ m)).mp
          (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hmb⟩)
        rw [Finset.mem_insert, Finset.mem_singleton, D.tb] at hmem
        rcases hmem with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · have hun := geoOwner_insert_iff_of_unaffected hP Q₁ b₁ hb₁Q₁ hcB (geoOwner hP Q₁ m) hmb m rfl
        rcases step1 with h | h
        · exact Or.inl ((hun _).mpr h.symm).symm
        · exact Or.inr (Or.inl ((hun _).mpr h.symm).symm)
    -- step 3: `Q₂ → S`
    have hI₂ : GeoInheritsMarkOrder hP Q₂ := (geoIndependent_partial_invariants hP hS Q₂ hQ₂S).1
    have hcC : geoOwner hP Q₂ (Sum.inr c₁) = geoOwner hP Q₂ (Sum.inr (visitTwin c₁)) :=
      geoIndependent_remaining_pair_owners hP hS Q₂ hQ₂S c₁ hc₁S hc₁Q₂
    have step3 : ∃ v : Visit P, (v = a₁ ∨ v = a₂ ∨ v = b₁ ∨ v = b₂ ∨ v = c₁ ∨ v = c₂) ∧
        geoOwner hP S m = geoOwner hP S (Sum.inr v) := by
      by_cases hmc : geoOwner hP Q₂ m = geoOwner hP Q₂ (Sum.inr c₁)
      · have hf := (geoComponentForgetSwitch_fiber_affected hP Q₂ hI₂ c₁ hc₁Q₂ hcC).2
        have hmem := (Finset.ext_iff.mp hf (geoOwner hP S m)).mp
          (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hmc⟩)
        rw [Finset.mem_insert, Finset.mem_singleton, D.tc] at hmem
        rcases hmem with h | h
        · exact ⟨c₁, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h⟩
        · exact ⟨c₂, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), h⟩
      · have hun := geoOwner_insert_iff_of_unaffected hP Q₂ c₁ hc₁Q₂ hcC (geoOwner hP Q₂ m) hmc m rfl
        rcases step2 with h | h | h | h
        · exact ⟨a₁, Or.inl rfl, ((hun _).mpr h.symm).symm⟩
        · exact ⟨a₂, Or.inr (Or.inl rfl), ((hun _).mpr h.symm).symm⟩
        · exact ⟨b₁, Or.inr (Or.inr (Or.inl rfl)), ((hun _).mpr h.symm).symm⟩
        · exact ⟨b₂, Or.inr (Or.inr (Or.inr (Or.inl rfl))), ((hun _).mpr h.symm).symm⟩
    obtain ⟨v, hv6, hv⟩ := step3
    rw [hv]
    exact hcore.six v hv6

end W3CA_Core

section W3CA_Config

/-- A visit of a triangle crossing is one of the six named visits `a_e, a_f, b_e, b_g, c_g, c_f`. -/
theorem w3ca_visit_six {P : LabelledTuple n} {e f g : ZMod n} (hef : IsCrossing P {e, f})
    (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) (v : Visit P)
    (hv : v.1.val ∈ triangleSupports e f g) :
    v = visitOn (xPair hef) e (mem_pair_left e f) ∨ v = visitOn (xPair hef) f (mem_pair_right e f) ∨
    v = visitOn (xPair heg) e (mem_pair_left e g) ∨ v = visitOn (xPair heg) g (mem_pair_right e g) ∨
    v = visitOn (xPair hfg) g (mem_pair_right f g) ∨ v = visitOn (xPair hfg) f (mem_pair_left f g) := by
  obtain ⟨x, i, hi⟩ := v
  have hv' : x.val ∈ triangleSupports e f g := hv
  rcases (P1.mem_triangleSupports _).mp hv' with h | h | h
  · have hx : x = xPair hef := Subtype.ext h
    subst hx
    have hi' : i ∈ ({e, f} : Finset (ZMod n)) := hi
    rcases Finset.mem_insert.mp hi' with h' | h'
    · subst h'; exact Or.inl rfl
    · rw [Finset.mem_singleton] at h'; subst h'; exact Or.inr (Or.inl rfl)
  · have hx : x = xPair heg := Subtype.ext h
    subst hx
    have hi' : i ∈ ({e, g} : Finset (ZMod n)) := hi
    rcases Finset.mem_insert.mp hi' with h' | h'
    · subst h'; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [Finset.mem_singleton] at h'; subst h'; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · have hx : x = xPair hfg := Subtype.ext h
    subst hx
    have hi' : i ∈ ({f, g} : Finset (ZMod n)) := hi
    rcases Finset.mem_insert.mp hi' with h' | h'
    · subst h'; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · rw [Finset.mem_singleton] at h'; subst h'; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- Each of the six named visits is a triangle visit. -/
theorem w3ca_six_tri {P : LabelledTuple n} {e f g : ZMod n} (hef : IsCrossing P {e, f})
    (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) (v : Visit P)
    (hv : v = visitOn (xPair hef) e (mem_pair_left e f) ∨ v = visitOn (xPair hef) f (mem_pair_right e f) ∨
      v = visitOn (xPair heg) e (mem_pair_left e g) ∨ v = visitOn (xPair heg) g (mem_pair_right e g) ∨
      v = visitOn (xPair hfg) g (mem_pair_right f g) ∨ v = visitOn (xPair hfg) f (mem_pair_left f g)) :
    v.1.val ∈ triangleSupports e f g := by
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  · exact (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  · exact (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  · exact (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  · exact (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  · exact (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))

/-- **The six-visit data at a punctured parameter** (either side; used on the empty side `t'`): the
twins by `SEL_visitTwin_visitOn`, the three crossings outside `Q` by `GT_empty_tri_mem_U`, the three
edge adjacencies by `GT_adjacent_of_shared` + `GT_succ_of_adjacent` (R-LOC-2 (2b)). -/
theorem w3ca_sixData_config {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) {t : E.Parameter} (ht : Punctured E δ t)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    w3ca_SixData (geomAt E t ht.1) Q
      (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)) := by
  have hef₀ : e ≠ f := P1.ne_of_isCrossing_pair hef
  have heg₀ : e ≠ g := P1.ne_of_isCrossing_pair heg
  have hfg₀ : f ≠ g := P1.ne_of_isCrossing_pair hfg
  have hab : xPair hef ≠ xPair heg := P1.xPair_ef_ne_eg hef heg hfg
  have hac : xPair hef ≠ xPair hfg := P1.xPair_ef_ne_fg hef heg hfg
  have hbc : xPair heg ≠ xPair hfg := P1.xPair_eg_ne_fg hef heg hfg
  have hta : (xPair hef).val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have htb : (xPair heg).val ∈ triangleSupports e f g :=
    (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have htc : (xPair hfg).val ∈ triangleSupports e f g :=
    (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have notQ : ∀ {y : Crossing (E.curve t)}, y.val ∈ triangleSupports e f g → y ∉ Q := fun hy =>
    ((CV.mem_U_iff _ Q _).mp (GT_empty_tri_mem_U ht hQ hfull hy)).1
  exact {
    ta := SEL_visitTwin_visitOn (mem_pair_right e f) (mem_pair_left e f) hef₀.symm
    ta' := SEL_visitTwin_visitOn (mem_pair_left e f) (mem_pair_right e f) hef₀
    tb := SEL_visitTwin_visitOn (mem_pair_right e g) (mem_pair_left e g) heg₀.symm
    tb' := SEL_visitTwin_visitOn (mem_pair_left e g) (mem_pair_right e g) heg₀
    tc := SEL_visitTwin_visitOn (mem_pair_left f g) (mem_pair_right f g) hfg₀
    tc' := SEL_visitTwin_visitOn (mem_pair_right f g) (mem_pair_left f g) hfg₀.symm
    a12 := rfl
    b12 := rfl
    c12 := rfl
    ab := hab
    ac := hac
    bc := hbc
    aQ := notQ hta
    bQ := notQ htb
    cQ := notQ htc
    adj_e := GT_succ_of_adjacent _ (GT_adjacent_of_shared hL hef₀ heg₀ hfg₀ t ht hta htb hab
      (mem_pair_left e f) (mem_pair_left e g)) rfl
    adj_g := GT_succ_of_adjacent _ (GT_adjacent_of_shared hL hef₀ heg₀ hfg₀ t ht htb htc hbc
      (mem_pair_right e g) (mem_pair_right f g)) rfl
    adj_f := GT_succ_of_adjacent _ (GT_adjacent_of_shared hL hef₀ heg₀ hfg₀ t ht htc hta hac.symm
      (mem_pair_left f g) (mem_pair_right e f)) rfl }


/-- **`Z`, the central triangle** of `Q ∪ T` at a polygon with the triangle `x_ef, x_eg, x_fg`: the
carrier through the three inner triangle visits (no piece, `carrierR Z = 1`). -/
noncomputable def w3ca_Z {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (_hfg : IsCrossing P {f, g}) : GeoComponent hP S :=
  w3ca_Zc hP S (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
    (visitOn (xPair heg) e (mem_pair_left e g))

/-- **`A`, the outer carrier through the outer visit of `x_ef`**. -/
noncomputable def w3ca_A {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (_hfg : IsCrossing P {f, g}) : GeoComponent hP S :=
  w3ca_Ac hP S (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
    (visitOn (xPair heg) e (mem_pair_left e g))

/-- **`B`, the outer carrier through the outer visit of `x_eg`**. -/
noncomputable def w3ca_B {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (_hfg : IsCrossing P {f, g}) : GeoComponent hP S :=
  w3ca_Bc hP S (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair heg) e (mem_pair_left e g))
    (visitOn (xPair heg) g (mem_pair_right e g))

/-- **`C`, the outer carrier through the outer visit of `x_fg`**. -/
noncomputable def w3ca_C {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) : GeoComponent hP S :=
  w3ca_Cc hP S (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair heg) e (mem_pair_left e g))
    (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g))

/-- **SPLITA at a configuration** (stated at any punctured parameter `t` carrying an outside support
`Q` at full availability with `Q ∪ T` independent; applied on the empty side `t'` to the transported
support): the four triangle-touching carriers `A, B, C, Z` of `Q ∪ T` exist with the abstract split
data on the six named visits, and the three `esc_FullSplitData` fields `touching_iff`, `distinct`,
`central_no_piece` hold for them. -/
theorem w3ca_split_config {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) {t : E.Parameter} (ht : Punctured E δ t)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hS : Q ∪ triangleCrossings (E.curve t) e f g ∈ CV.Ind (geomAt E t ht.1)) :
    w3ca_CoreData (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g)
        (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
        (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
        (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g))
        (w3ca_A (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg) (w3ca_B (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg)
        (w3ca_C (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg) (w3ca_Z (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg) ∧
      (∀ q, ¬ TriangleDisjoint (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) e f g q ↔
        (q = w3ca_A (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∨ q = w3ca_B (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∨
          q = w3ca_C (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∨ q = w3ca_Z (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg)) ∧
      (w3ca_A (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ≠ w3ca_B (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∧
        w3ca_A (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ≠ w3ca_C (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∧
        w3ca_A (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ≠ w3ca_Z (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∧
        w3ca_B (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ≠ w3ca_C (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∧
        w3ca_B (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ≠ w3ca_Z (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∧
        w3ca_C (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ≠ w3ca_Z (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg) ∧
      CV.piecesOn (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g)
        (w3ca_Z (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg) = ∅ := by
  have D := w3ca_sixData_config hL ht hef heg hfg hQ hfull
  have hSeq : ∀ x, x ∈ Q ∪ triangleCrossings (E.curve t) e f g ↔
      x ∈ Q ∨ x = xPair hef ∨ x = xPair heg ∨ x = xPair hfg := by
    intro x
    rw [Finset.mem_union, P1.mem_triangleCrossings_iff hef heg hfg]
  have hSi : GeoIndependent (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) :=
    CV.geoIndependent_of_mem_Ind _ hS
  have hcore := w3ca_core _ D _ hSeq hSi
  refine ⟨hcore, ?_, hcore.distinct, ?_⟩
  · intro q
    rw [esc_not_triangleDisjoint_iff]
    constructor
    · rintro ⟨v, hv, hvq⟩
      subst hvq
      exact hcore.six v (w3ca_visit_six hef heg hfg v hv)
    · rintro (rfl | rfl | rfl | rfl)
      · obtain ⟨v, hv6, hvA⟩ := hcore.hitA
        exact ⟨v, w3ca_six_tri hef heg hfg v hv6, hvA⟩
      · obtain ⟨v, hv6, hvB⟩ := hcore.hitB
        exact ⟨v, w3ca_six_tri hef heg hfg v hv6, hvB⟩
      · obtain ⟨v, hv6, hvC⟩ := hcore.hitC
        exact ⟨v, w3ca_six_tri hef heg hfg v hv6, hvC⟩
      · obtain ⟨v, hv6, hvZ⟩ := hcore.hitZ
        exact ⟨v, w3ca_six_tri hef heg hfg v hv6, hvZ⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro H hH
    rw [CV.mem_piecesOn] at hH
    obtain ⟨c₀, hc₀⟩ := CV.pieceLabels_nonempty _ _ H
    have hc₀U := CV.pieceLabels_subset _ _ H hc₀
    have hc₀S : c₀ ∉ Q ∪ triangleCrossings (E.curve t) e f g := ((CV.mem_U_iff _ _ c₀).mp hc₀U).1
    obtain ⟨i, -, -⟩ := crossing_visits_exist c₀
    have hown := hH c₀ hc₀ ⟨c₀, i⟩ rfl
    obtain ⟨zA, zB, zC, hzA, hzB, hzC, hZ⟩ := hcore.central
    apply hc₀S
    rw [hSeq]
    rcases (hZ _).mp hown with h | h | h
    · have h' : (⟨c₀, i⟩ : Visit (E.curve t)).1 = zA.1 := congrArg Sigma.fst (Sum.inr.inj h)
      exact Or.inr (Or.inl (h'.trans hzA))
    · have h' : (⟨c₀, i⟩ : Visit (E.curve t)).1 = zB.1 := congrArg Sigma.fst (Sum.inr.inj h)
      exact Or.inr (Or.inr (Or.inl (h'.trans hzB)))
    · have h' : (⟨c₀, i⟩ : Visit (E.curve t)).1 = zC.1 := congrArg Sigma.fst (Sum.inr.inj h)
      exact Or.inr (Or.inr (Or.inr (h'.trans hzC)))

/-- **SPLITA at the configuration of `w3bi_esc_outer`** (same binders up to the contact carriers,
which the four fields do not see): on the empty side `t'`, for the transported outside support
`Q' = transportSupport hs Q` and `T'` the three triangle crossings of `E.curve t'`, the four carriers
`w3ca_A, w3ca_B, w3ca_C, w3ca_Z` of `Q' ∪ T'` satisfy `esc_FullSplitData`'s `touching_iff`,
`distinct` and `central_no_piece`. -/
theorem w3ca_split_at_outer (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1)) :
    (∀ q, ¬ TriangleDisjoint (geomAt E t' ht'.1)
        (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) e f g q ↔
      (q = w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∨
        q = w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∨
        q = w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∨
        q = w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg))) ∧
    (w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ≠
        w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∧
      w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ≠
        w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∧
      w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ≠
        w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∧
      w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ≠
        w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∧
      w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ≠
        w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∧
      w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ≠
        w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) ∧
    CV.piecesOn (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
      (w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) = ∅ := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨-, h1, h2, h3⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  exact ⟨h1, h2, h3⟩

/-- lem:uniformrot (i) at three corners, in `rotAbs` form: a regular `3`-gon has `|rot| = 1`
(`CV.rot_triangle`, from `SM.rotation_number`). -/
theorem w3ca_rotAbs_three {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : CV.Regular L) (h3 : c = 3) :
    CV.rotAbs L hL = 1 := by
  subst h3
  unfold CV.rotAbs
  rcases (CV.rot_triangle L hL).2 with h | h <;> rw [h] <;> rfl

/-- A carrier whose marks are exactly three selected visits of three distinct crossings has exactly
three corners. -/
theorem w3ca_cornerCount_three {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (Z : GeoComponent hP S) (zA zB zC : Visit P)
    (hA : zA.1 ∈ S) (hB : zB.1 ∈ S) (hC : zC.1 ∈ S)
    (hAB : zA.1 ≠ zB.1) (hAC : zA.1 ≠ zC.1) (hBC : zB.1 ≠ zC.1)
    (hZ : ∀ m : Mark P, geoOwner hP S m = Z ↔ (m = Sum.inr zA ∨ m = Sum.inr zB ∨ m = Sum.inr zC)) :
    geoCornerCount hP S Z = 3 := by
  unfold geoCornerCount
  have hmem : ∀ m, m ∈ geoComponentCornerList hP S Z ↔
      m ∈ ([Sum.inr zA, Sum.inr zB, Sum.inr zC] : List (Mark P)) := by
    intro m
    rw [mem_geoComponentCornerList, hZ]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · rintro (rfl | rfl | rfl)
      · exact ⟨Or.inl rfl, hA⟩
      · exact ⟨Or.inr (Or.inl rfl), hB⟩
      · exact ⟨Or.inr (Or.inr rfl), hC⟩
  have hne1 : (Sum.inr zA : Mark P) ≠ Sum.inr zB := fun h => hAB (congrArg Sigma.fst (Sum.inr.inj h))
  have hne2 : (Sum.inr zA : Mark P) ≠ Sum.inr zC := fun h => hAC (congrArg Sigma.fst (Sum.inr.inj h))
  have hne3 : (Sum.inr zB : Mark P) ≠ Sum.inr zC := fun h => hBC (congrArg Sigma.fst (Sum.inr.inj h))
  have hnd : ([Sum.inr zA, Sum.inr zB, Sum.inr zC] : List (Mark P)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true]
    exact ⟨⟨hne1, hne2⟩, hne3, not_false⟩
  exact ((List.perm_ext_iff_of_nodup (geoComponentCornerList_nodup hP S Z) hnd).mpr hmem).length_eq

/-- `carrierR` of a carrier with exactly three corners is `1` (lem:uniformrot (i)). -/
theorem w3ca_carrierR_of_three (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry)
    (Z : GeoComponent hG.crossingGeometry S) (h3 : geoCornerCount hG.crossingGeometry S Z = 3) :
    CV.carrierR hn hG hS Z = 1 := by
  unfold CV.carrierR
  exact w3ca_rotAbs_three _ _ h3

/-- **`central_rot` at a configuration**: the central triangle `w3ca_Z` has exactly the three inner
visits as corners, so `carrierR Z = 1` ("`lem:uniformrot(i)` gives it absolute rotation one", ESC §4). -/
theorem w3ca_central_rot_config (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) {t : E.Parameter} (ht : Punctured E δ t)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hS : Q ∪ triangleCrossings (E.curve t) e f g ∈ CV.Ind (geomAt E t ht.1)) :
    CV.carrierR hn (genericAt E t ht.1) hS
      (w3ca_Z (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg) = 1 := by
  obtain ⟨hcore, -, -, -⟩ := w3ca_split_config hL ht hef heg hfg hQ hfull hS
  obtain ⟨zA, zB, zC, hzA, hzB, hzC, hZ⟩ := hcore.central
  apply w3ca_carrierR_of_three
  refine w3ca_cornerCount_three _ _ _ zA zB zC ?_ ?_ ?_ ?_ ?_ ?_ hZ
  · rw [hzA]
    exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
  · rw [hzB]
    exact Finset.mem_union_right _
      ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl)))
  · rw [hzC]
    exact Finset.mem_union_right _
      ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl)))
  · rw [hzA, hzB]
    exact P1.xPair_ef_ne_eg hef heg hfg
  · rw [hzA, hzC]
    exact P1.xPair_ef_ne_fg hef heg hfg
  · rw [hzB, hzC]
    exact P1.xPair_eg_ne_fg hef heg hfg

/-- **`central_rot` at the configuration of `w3bi_esc_outer`** (empty side `t'`). -/
theorem w3ca_central_rot_at_outer (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1)) :
    CV.carrierR hn (genericAt E t' ht'.1) hS'
      (w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
        ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) = 1 :=
  w3ca_central_rot_config hn hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)
    (GT_outsideSupports_transport hL ht ht' hop hs hQ)
    (GT_fullAvail_transport hL ht ht' hop hs hQ hfull) hS'

/-- **The marks partition at a configuration**: a mark lies on one of `w3ca_A, w3ca_B, w3ca_C, w3ca_Z`
(carriers of `Q ∪ T`) iff it lies on the triangle-touching carrier `q₀` of `Q` (unique by
`esc_contact_unique`; here any triangle-touching `q₀`). -/
theorem w3ca_marks_partition_config {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) {t : E.Parameter} (ht : Punctured E δ t)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hS : Q ∪ triangleCrossings (E.curve t) e f g ∈ CV.Ind (geomAt E t ht.1))
    (q₀ : GeoComponent (geomAt E t ht.1) Q) (hq₀ : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀)
    (m : Mark (E.curve t)) :
    (geoOwner (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) m =
        w3ca_A (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∨
      geoOwner (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) m =
        w3ca_B (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∨
      geoOwner (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) m =
        w3ca_C (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg ∨
      geoOwner (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) m =
        w3ca_Z (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) hef heg hfg) ↔
    geoOwner (geomAt E t ht.1) Q m = q₀ := by
  have D := w3ca_sixData_config hL ht hef heg hfg hQ hfull
  have hSeq : ∀ x, x ∈ Q ∪ triangleCrossings (E.curve t) e f g ↔
      x ∈ Q ∨ x = xPair hef ∨ x = xPair heg ∨ x = xPair hfg := by
    intro x
    rw [Finset.mem_union, P1.mem_triangleCrossings_iff hef heg hfg]
  have hSi : GeoIndependent (geomAt E t ht.1) (Q ∪ triangleCrossings (E.curve t) e f g) :=
    CV.geoIndependent_of_mem_Ind _ hS
  obtain ⟨v, hv, hvq⟩ := (esc_not_triangleDisjoint_iff _ _ _ _ _ _).1 hq₀
  have hsix := w3ca_six_on_contact _ D _ hSeq hSi v (w3ca_visit_six hef heg hfg v hv)
  rw [← hvq, hsix]
  exact w3ca_marks_partition _ D _ hSeq hSi m

end W3CA_Config

/-! ### W3CC — unit SPLITC: `esc_FullSplitData.outer_alternative` and `.uniform` from the corner ledger

The two sign/rotation fields of `esc_FullSplitData` (ESC §4, (14)/(16)) at the split `q₀ → A, B, C, Z`
of the contact carrier by the three triangle smoothings, from ONE combinatorial interface — the corner
ledger `w3cc_SplitCorners` (unit SPLITA's carriers as a black box): every corner of `q₀` is a corner
of exactly one outer carrier and keeps its turn, the central triangle `Z` owns exactly the three inner
smoothing-site visits `zA, zB, zC` (hence turns one way: a regular triangle is uniform,
`w3cc_uniform_of_three`), and each outer carrier owns
exactly one outer smoothing-site visit (the twin), whose turn is the negative of the inner one.
Then lem:turnlift (ii) (`CV.two_pi_mul_rot`) gives `rot q₀ = rot A + rot B + rot C + rot Z` (the six new
turns cancel in pairs), lem:uniformrot (i) gives `rot Z = ζ`, and the two branches are `ζ = −τ` (live:
the outer carriers are uniform of `q₀`'s sign `τ`) and `ζ = τ` (dead: each outer carrier has exactly the
one dissent `−τ` at its smoothing corner).  Template: U-SPLIT's `cvt165s_` rotation lane
(`CV/SingletonDi.lean`, NOT in this file's import closure — the needed helpers are copied under
`w3cc_`) and R176's `r176l_` ledgers.  Prefix `w3cc_`; nothing above is modified. -/

section W3CC_SplitC

/-! #### C0. Signs, patterns and rays on labelled tuples -/

theorem w3cc_signType_eq_or_neg {σ τ : SignType} (hσ : σ ≠ 0) (hτ : τ ≠ 0) : σ = τ ∨ σ = -τ := by
  revert hσ hτ
  revert σ τ
  decide

theorem w3cc_signType_eq_zero_of_eq_neg {τ : SignType} (h : τ = -τ) : τ = 0 := by
  revert h
  revert τ
  decide

theorem w3cc_sign_principalTurn {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : CV.Regular L)
    (k : ZMod c) : SignType.sign (CV.principalTurn L k) = turn L k := by
  rw [CV.principalTurn_eq_sm]
  exact principalTurn_sign ((CV.regular_iff_sm L).mp hL) k

theorem w3cc_principalTurn_reversal {c : ℕ} (L : LabelledTuple c) (hL : CV.Regular L) (k : ZMod c) :
    CV.principalTurn (reversal L) k = -CV.principalTurn L (2 - k) := by
  rw [CV.principalTurn_eq_sm, CV.principalTurn_eq_sm]
  exact principalTurn_reversal ((CV.regular_iff_sm L).mp hL) k

/-- The signed corner pattern of ESC §4: uniform of sign `τ`, or exactly one dissent `−τ`. -/
def w3cc_Pattern {c : ℕ} (L : LabelledTuple c) (τ : SignType) : Prop :=
  (∀ k, turn L k = τ) ∨ (∃ k₀, turn L k₀ = -τ ∧ ∀ k, k ≠ k₀ → turn L k = τ)

/-- `τ · rot(L) ≥ 1` at a signed pattern of sign `τ ≠ 0`. -/
theorem w3cc_one_le_sign_mul_rot {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : CV.Regular L)
    {τ : SignType} (hτ0 : τ ≠ 0) (h : w3cc_Pattern L τ) : 1 ≤ (τ : ℤ) * CV.rot L hL := by
  have hr := CV.cvt165s_rot_ray L hL τ h
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · have := hr.2 rfl
    simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul]
    omega
  · exact absurd rfl hτ0
  · have := hr.1 rfl
    simp only [SignType.coe_one, one_mul]
    omega

/-- lem:uniformrot (i) with three corners: a uniform triangle has rotation its common sign. -/
theorem w3cc_rot_uniform_three {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : CV.Regular L) (h3 : c = 3)
    {σ : SignType} (hσ : σ ≠ 0) (h : ∀ k, turn L k = σ) : CV.rot L hL = (σ : ℤ) := by
  have hsign := w3cc_sign_principalTurn L hL
  rcases SignType.trichotomy σ with rfl | rfl | rfl
  · have := CV.rot_eq_neg_one_of_neg_three hL
      (fun i => sign_eq_neg_one_iff.mp ((hsign i).trans (h i))) h3
    simpa using this
  · exact absurd rfl hσ
  · have := CV.rot_eq_one_of_pos_three hL (fun i => sign_eq_one_iff.mp ((hsign i).trans (h i))) h3
    simpa using this

/-- **The `|·|`-arithmetic of (16), live branch**: four signed rotations on one ray `σ` with
`r₁ + r₂ + r₃ = r + σ` have `|r₁| + |r₂| + |r₃| = |r| + 1`. -/
theorem w3cc_abs_ledger_live {r r₁ r₂ r₃ : ℤ} {σ : SignType} (hσ : σ ≠ 0)
    (h : r₁ + r₂ + r₃ = r + (σ : ℤ)) (h₀ : 1 ≤ (σ : ℤ) * r)
    (h₁ : 1 ≤ (σ : ℤ) * r₁) (h₂ : 1 ≤ (σ : ℤ) * r₂) (h₃ : 1 ≤ (σ : ℤ) * r₃) :
    |r₁| + |r₂| + |r₃| = |r| + 1 := by
  rcases SignType.trichotomy σ with rfl | rfl | rfl
  · simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul] at h h₀ h₁ h₂ h₃
    rw [abs_of_neg (by omega), abs_of_neg (by omega), abs_of_neg (by omega), abs_of_neg (by omega)]
    omega
  · exact absurd rfl hσ
  · simp only [SignType.coe_one, one_mul] at h h₀ h₁ h₂ h₃
    rw [abs_of_pos (by omega), abs_of_pos (by omega), abs_of_pos (by omega), abs_of_pos (by omega)]
    omega

/-- **The `|·|`-arithmetic of (16), dead branch**: `r₁ + r₂ + r₃ + σ = r` gives `|r₁| + |r₂| + |r₃| + 1 = |r|`. -/
theorem w3cc_abs_ledger_dead {r r₁ r₂ r₃ : ℤ} {σ : SignType} (hσ : σ ≠ 0)
    (h : r₁ + r₂ + r₃ + (σ : ℤ) = r) (h₀ : 1 ≤ (σ : ℤ) * r)
    (h₁ : 1 ≤ (σ : ℤ) * r₁) (h₂ : 1 ≤ (σ : ℤ) * r₂) (h₃ : 1 ≤ (σ : ℤ) * r₃) :
    |r₁| + |r₂| + |r₃| + 1 = |r| := by
  rcases SignType.trichotomy σ with rfl | rfl | rfl
  · simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul] at h h₀ h₁ h₂ h₃
    rw [abs_of_neg (by omega), abs_of_neg (by omega), abs_of_neg (by omega), abs_of_neg (by omega)]
    omega
  · exact absurd rfl hσ
  · simp only [SignType.coe_one, one_mul] at h h₀ h₁ h₂ h₃
    rw [abs_of_pos (by omega), abs_of_pos (by omega), abs_of_pos (by omega), abs_of_pos (by omega)]
    omega

/-- **A regular triangle has no corner of turn `≤ 0` with the other two `≥ 0`**: lem:uniformrot (ii) would
give `rot ≥ 1`, but two principal turns below `π` (`principalAngle_bounds`) sum to less than `2π`. -/
theorem w3cc_no_dissent_three {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : CV.Regular L) (h3 : c = 3)
    (a : ZMod c) (ha : CV.principalTurn L a ≤ 0) (hother : ∀ i, i ≠ a → 0 ≤ CV.principalTurn L i) :
    False := by
  have hrot := CV.one_le_rot_of_one_dissent hL a hother
  have hsum := CV.two_pi_mul_rot L hL
  have hSM : Regular L := (CV.regular_iff_sm L).mp hL
  have hb : ∀ i, CV.principalTurn L i < Real.pi := fun i =>
    (principalAngle_bounds (hSM i) : -Real.pi < CV.principalTurn L i ∧ CV.principalTurn L i < Real.pi).2
  have hcard : (Finset.univ.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, ZMod.card, h3]
  have hne : (Finset.univ.erase a).Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
  have hlt : ∑ i ∈ Finset.univ.erase a, CV.principalTurn L i < 2 * Real.pi := by
    calc ∑ i ∈ Finset.univ.erase a, CV.principalTurn L i < ∑ i ∈ Finset.univ.erase a, Real.pi :=
          Finset.sum_lt_sum_of_nonempty hne (fun i _ => hb i)
      _ = 2 * Real.pi := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; norm_num
  have hsplit := Finset.add_sum_erase Finset.univ (fun i => CV.principalTurn L i) (Finset.mem_univ a)
  have hrot' : (1 : ℝ) ≤ CV.rot L hL := by exact_mod_cast hrot
  have h2 : 2 * Real.pi * 1 ≤ 2 * Real.pi * (CV.rot L hL : ℝ) :=
    mul_le_mul_of_nonneg_left hrot' (by positivity)
  linarith

/-- The reversal form: no corner of turn `≥ 0` with the other two `≤ 0`. -/
theorem w3cc_no_dissent_three' {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : CV.Regular L) (h3 : c = 3)
    (a : ZMod c) (ha : 0 ≤ CV.principalTurn L a) (hother : ∀ i, i ≠ a → CV.principalTurn L i ≤ 0) :
    False := by
  have hrev := CV.regular_reversal' hL
  refine w3cc_no_dissent_three (reversal L) hrev h3 (2 - a) ?_ ?_
  · rw [w3cc_principalTurn_reversal L hL, sub_sub_cancel]
    linarith
  · intro i hi
    rw [w3cc_principalTurn_reversal L hL]
    have hne : 2 - i ≠ a := fun he => hi (by rw [← he, sub_sub_cancel])
    linarith [hother _ hne]

/-- **A regular polygon with three corners is uniform** (lem:uniformrot (i) "with three corners" read
backwards): its three turns have one common nonzero sign. -/
theorem w3cc_uniform_of_three {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : CV.Regular L) (h3 : c = 3) :
    ∃ σ : SignType, σ ≠ 0 ∧ ∀ k, turn L k = σ := by
  have hsign := w3cc_sign_principalTurn L hL
  suffices h : (∀ i, 0 < CV.principalTurn L i) ∨ (∀ i, CV.principalTurn L i < 0) by
    rcases h with h | h
    · exact ⟨1, by decide, fun k => by rw [← hsign k]; exact sign_eq_one_iff.mpr (h k)⟩
    · exact ⟨-1, by decide, fun k => by rw [← hsign k]; exact sign_eq_neg_one_iff.mpr (h k)⟩
  subst h3
  have N := w3cc_no_dissent_three L hL rfl
  have R := w3cc_no_dissent_three' L hL rfl
  have hall : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  have N0 : ¬ (CV.principalTurn L 0 ≤ 0 ∧ 0 ≤ CV.principalTurn L 1 ∧ 0 ≤ CV.principalTurn L 2) :=
    fun ⟨h0, h1, h2⟩ => N 0 h0 fun i hi => by
      rcases hall i with rfl | rfl | rfl
      · exact absurd rfl hi
      · exact h1
      · exact h2
  have N1 : ¬ (CV.principalTurn L 1 ≤ 0 ∧ 0 ≤ CV.principalTurn L 0 ∧ 0 ≤ CV.principalTurn L 2) :=
    fun ⟨h1, h0, h2⟩ => N 1 h1 fun i hi => by
      rcases hall i with rfl | rfl | rfl
      · exact h0
      · exact absurd rfl hi
      · exact h2
  have N2 : ¬ (CV.principalTurn L 2 ≤ 0 ∧ 0 ≤ CV.principalTurn L 0 ∧ 0 ≤ CV.principalTurn L 1) :=
    fun ⟨h2, h0, h1⟩ => N 2 h2 fun i hi => by
      rcases hall i with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact absurd rfl hi
  have R0 : ¬ (0 ≤ CV.principalTurn L 0 ∧ CV.principalTurn L 1 ≤ 0 ∧ CV.principalTurn L 2 ≤ 0) :=
    fun ⟨h0, h1, h2⟩ => R 0 h0 fun i hi => by
      rcases hall i with rfl | rfl | rfl
      · exact absurd rfl hi
      · exact h1
      · exact h2
  have R1 : ¬ (0 ≤ CV.principalTurn L 1 ∧ CV.principalTurn L 0 ≤ 0 ∧ CV.principalTurn L 2 ≤ 0) :=
    fun ⟨h1, h0, h2⟩ => R 1 h1 fun i hi => by
      rcases hall i with rfl | rfl | rfl
      · exact h0
      · exact absurd rfl hi
      · exact h2
  have R2 : ¬ (0 ≤ CV.principalTurn L 2 ∧ CV.principalTurn L 0 ≤ 0 ∧ CV.principalTurn L 1 ≤ 0) :=
    fun ⟨h2, h0, h1⟩ => R 2 h2 fun i hi => by
      rcases hall i with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact absurd rfl hi
  rcases lt_or_ge 0 (CV.principalTurn L 0) with h0 | h0 <;>
    rcases lt_or_ge 0 (CV.principalTurn L 1) with h1 | h1 <;>
    rcases lt_or_ge 0 (CV.principalTurn L 2) with h2 | h2
  · left
    intro i
    rcases hall i with rfl | rfl | rfl <;> assumption
  · exact absurd ⟨h2, h0.le, h1.le⟩ N2
  · exact absurd ⟨h1, h0.le, h2.le⟩ N1
  · exact absurd ⟨h0.le, h1, h2⟩ R0
  · exact absurd ⟨h0, h1.le, h2.le⟩ N0
  · exact absurd ⟨h1.le, h0, h2⟩ R1
  · exact absurd ⟨h2.le, h0, h1⟩ R2
  · right
    have h0' : CV.principalTurn L 0 < 0 := lt_of_le_of_ne h0 fun e => R0 ⟨e.ge, h1, h2⟩
    have h1' : CV.principalTurn L 1 < 0 := lt_of_le_of_ne h1 fun e => R1 ⟨e.ge, h0, h2⟩
    have h2' : CV.principalTurn L 2 < 0 := lt_of_le_of_ne h2 fun e => R2 ⟨e.ge, h0, h1⟩
    intro i
    rcases hall i with rfl | rfl | rfl <;> assumption

/-! #### C1. Corner marks, mark turns, corner sets (U-SPLIT's `cvt165s_` rotation lane, copied) -/

section W3CC_Marks

variable {P : LabelledTuple n} (hP : CrossingGeometry P)

/-- The real principal turn of a corner mark of a carrier at the support `S`. -/
noncomputable def w3cc_markPT (S : Finset (Crossing P)) (m : Mark P) : ℝ :=
  principalAngle (edge P (geoInEdge hP m)) (edge P (geoOutSlot hP S m).1)

/-- Its sign. -/
noncomputable def w3cc_markTurn (S : Finset (Crossing P)) (m : Mark P) : SignType :=
  SignType.sign (w3cc_markPT hP S m)

theorem w3cc_principalTurn_eq_mark (hn : 3 ≤ n) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    CV.principalTurn (geoCornerPolygon hP S q) k = w3cc_markPT hP S (geoCornerMark hP S q k) := by
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred_smul hn hP hS q k
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge_smul hn hP hS q k
  rw [CV.principalTurn_eq_sm]
  unfold principalTurn w3cc_markPT
  rw [he₁, he₂, principalAngle_smul hc₁ hc₂]

theorem w3cc_turn_eq_mark (hn : 3 ≤ n) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (hreg : CV.Regular (geoCornerPolygon hP S q)) (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k = w3cc_markTurn hP S (geoCornerMark hP S q k) := by
  rw [← w3cc_sign_principalTurn _ hreg k, w3cc_principalTurn_eq_mark hP hn hS q k]
  rfl

open scoped Classical in
/-- The corner marks of `q` at `S`: the true corners of `S` owned by `q`. -/
noncomputable def w3cc_cornerSet (S : Finset (Crossing P)) (q : GeoComponent hP S) : Finset (Mark P) :=
  Finset.univ.filter fun m => geoOwner hP S m = q ∧ IsTrueCorner S m

theorem w3cc_mem_cornerSet (S : Finset (Crossing P)) (q : GeoComponent hP S) (m : Mark P) :
    m ∈ w3cc_cornerSet hP S q ↔ geoOwner hP S m = q ∧ IsTrueCorner S m := by
  simp only [w3cc_cornerSet, Finset.mem_filter, Finset.mem_univ, true_and]

open scoped Classical in
theorem w3cc_image_cornerMark (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    Finset.univ.image (geoCornerMark hP S q) = w3cc_cornerSet hP S q := by
  ext m
  rw [Finset.mem_image, w3cc_mem_cornerSet]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact geoCornerMark_mem hP S q k
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q m h1 h2
    exact ⟨k, Finset.mem_univ _, hk⟩

theorem w3cc_sum_corners (S : Finset (Crossing P)) (q : GeoComponent hP S) (f : Mark P → ℝ) :
    ∑ k, f (geoCornerMark hP S q k) = ∑ m ∈ w3cc_cornerSet hP S q, f m := by
  classical
  rw [← w3cc_image_cornerMark, Finset.sum_image]
  intro i _ j _ hij
  exact geoCornerMark_injective hP S q hij

/-- The corner count is the size of the corner set. -/
theorem w3cc_geoCornerCount_eq_card (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCornerCount hP S q = (w3cc_cornerSet hP S q).card := by
  classical
  rw [← w3cc_image_cornerMark, Finset.card_image_of_injective _ (geoCornerMark_injective hP S q),
    Finset.card_univ, ZMod.card]

omit [NeZero n] in
theorem w3cc_isTrueCorner_mono {S S' : Finset (Crossing P)} (hSS : S ⊆ S') (m : Mark P)
    (hm : IsTrueCorner S m) : IsTrueCorner S' m := by
  cases m with
  | inl i => trivial
  | inr w => exact hSS hm

/-- **Inherited corners keep their principal turn** under `S ⊆ S'`. -/
theorem w3cc_markPT_mono {S S' : Finset (Crossing P)} (hSS : S ⊆ S') (m : Mark P)
    (hm : IsTrueCorner S m) : w3cc_markPT hP S' m = w3cc_markPT hP S m := by
  unfold w3cc_markPT
  cases m with
  | inl i => rw [geoOutSlot_vertex, geoOutSlot_vertex]
  | inr w =>
    have hw : w.1 ∈ S := hm
    rw [geoOutSlot_selected hP S w hw, geoOutSlot_selected hP S' w (hSS hw)]

theorem w3cc_markTurn_mono {S S' : Finset (Crossing P)} (hSS : S ⊆ S') (m : Mark P)
    (hm : IsTrueCorner S m) : w3cc_markTurn hP S' m = w3cc_markTurn hP S m := by
  unfold w3cc_markTurn
  rw [w3cc_markPT_mono hP hSS m hm]

/-- **The two smoothing corners of a selected crossing cancel** in the real turn ledger. -/
theorem w3cc_new_turns_cancel (hn : 3 ≤ n) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    w3cc_markPT hP S (Sum.inr v) + w3cc_markPT hP S (Sum.inr (visitTwin v)) = 0 := by
  have hdet := geo_visit_corner_det_ne_zero hn hP S v hv
  have hv' : (visitTwin v).1 ∈ S := by
    rw [visitTwin_crossing]
    exact hv
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv] at hdet
  unfold w3cc_markPT
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv, geoInEdge_visit hn hP (visitTwin v),
    geoOutSlot_selected hP S (visitTwin v) hv', visitTwin_involutive,
    principalAngle_swap (regularPair_of_det_ne_zero hdet)]
  ring

/-- The turn sign at the twin visit is the negative of the turn sign at the visit. -/
theorem w3cc_markTurn_twin (hn : 3 ≤ n) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    w3cc_markTurn hP S (Sum.inr (visitTwin v)) = -w3cc_markTurn hP S (Sum.inr v) := by
  have h := w3cc_new_turns_cancel hP hn S v hv
  unfold w3cc_markTurn
  rw [show w3cc_markPT hP S (Sum.inr (visitTwin v)) = -w3cc_markPT hP S (Sum.inr v) by linarith,
    Left.sign_neg]

end W3CC_Marks

/-! #### C2. The corner ledger of the split (the black box from unit SPLITA) -/

/-- **BLACK BOX (unit SPLITA's carriers `A, B, C, Z`, in the form this unit consumes): the corner ledger
of the split of the contact carrier `q₀` of `S = Q` into the four triangle-touching carriers of
`S' = Q ∪ T`** ("All nonlocal corners of the empty contact carrier partition among the three outer
carriers", ESC §4; the central triangle `Z` has exactly the three inner smoothing-site corners
`zA, zB, zC`, one per triangle crossing, and each outer carrier has exactly one smoothing-site corner,
the twin of the corresponding inner one).  Purely combinatorial (owners and true corners): the sign data
— the central triangle turns one way (`w3cc_central_uniform_of`), `carrierR Z = 1` (`w3cc_central_rot_of`)
— is DERIVED from it (three corners force a uniform triangle, `w3cc_uniform_of_three`). -/
structure w3cc_SplitCorners {P : LabelledTuple n} (hP : CrossingGeometry P) (S S' : Finset (Crossing P))
    (q₀ : GeoComponent hP S) (A B C Z : GeoComponent hP S') (zA zB zC : Visit P) : Prop where
  subset : S ⊆ S'
  distinct : A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z
  /-- the three inner visits lie on crossings selected in `S'` but not in `S` (the triangle crossings) -/
  memA : zA.1 ∈ S' ∧ zA.1 ∉ S
  memB : zB.1 ∈ S' ∧ zB.1 ∉ S
  memC : zC.1 ∈ S' ∧ zC.1 ∉ S
  /-- the central triangle owns the three inner visits -/
  ownZ : geoOwner hP S' (Sum.inr zA) = Z ∧ geoOwner hP S' (Sum.inr zB) = Z ∧ geoOwner hP S' (Sum.inr zC) = Z
  /-- each outer carrier owns the twin of its inner visit -/
  ownA : geoOwner hP S' (Sum.inr (visitTwin zA)) = A
  ownB : geoOwner hP S' (Sum.inr (visitTwin zB)) = B
  ownC : geoOwner hP S' (Sum.inr (visitTwin zC)) = C
  /-- every corner of `q₀` is a corner of one of the outer carriers -/
  inherited : ∀ m : Mark P, IsTrueCorner S m → geoOwner hP S m = q₀ →
    geoOwner hP S' m = A ∨ geoOwner hP S' m = B ∨ geoOwner hP S' m = C
  /-- every corner of `A, B, C, Z` is a corner of `q₀` or one of the six smoothing-site visits -/
  cover : ∀ m : Mark P, IsTrueCorner S' m →
    (geoOwner hP S' m = A ∨ geoOwner hP S' m = B ∨ geoOwner hP S' m = C ∨ geoOwner hP S' m = Z) →
    (IsTrueCorner S m ∧ geoOwner hP S m = q₀) ∨
      m = Sum.inr zA ∨ m = Sum.inr zB ∨ m = Sum.inr zC ∨
      m = Sum.inr (visitTwin zA) ∨ m = Sum.inr (visitTwin zB) ∨ m = Sum.inr (visitTwin zC)

section W3CC_Ledger

variable {P : LabelledTuple n} (hP : CrossingGeometry P) {S S' : Finset (Crossing P)}
  {q₀ : GeoComponent hP S} {A B C Z : GeoComponent hP S'} {zA zB zC : Visit P}

open scoped Classical in
/-- The inherited corners of `q₀` that go to the outer carrier `X`. -/
noncomputable def w3cc_inh (S' : Finset (Crossing P)) (q₀ : GeoComponent hP S) (X : GeoComponent hP S') :
    Finset (Mark P) :=
  (w3cc_cornerSet hP S q₀).filter fun m => geoOwner hP S' m = X

theorem w3cc_mem_inh (X : GeoComponent hP S') (m : Mark P) :
    m ∈ w3cc_inh hP S' q₀ X ↔ (geoOwner hP S m = q₀ ∧ IsTrueCorner S m) ∧ geoOwner hP S' m = X := by
  simp only [w3cc_inh, Finset.mem_filter, w3cc_mem_cornerSet]

variable (hC : w3cc_SplitCorners hP S S' q₀ A B C Z zA zB zC)
include hC

/-- **The corner set of an outer carrier**: its smoothing corner and its inherited corners.  Stated for
a generic outer carrier `X` with its inner visit `zX`; `hsix` says that among the six smoothing-site
visits only the twin of `zX` is owned by `X`. -/
theorem w3cc_cornerSet_outer (X : GeoComponent hP S') (zX : Visit P) (hzX : zX.1 ∈ S')
    (hownX : geoOwner hP S' (Sum.inr (visitTwin zX)) = X) (hXne : X = A ∨ X = B ∨ X = C)
    (hsix : ∀ m : Mark P,
      (m = Sum.inr zA ∨ m = Sum.inr zB ∨ m = Sum.inr zC ∨
        m = Sum.inr (visitTwin zA) ∨ m = Sum.inr (visitTwin zB) ∨ m = Sum.inr (visitTwin zC)) →
      geoOwner hP S' m = X → m = Sum.inr (visitTwin zX)) :
    w3cc_cornerSet hP S' X = insert (Sum.inr (visitTwin zX)) (w3cc_inh hP S' q₀ X) := by
  ext m
  rw [w3cc_mem_cornerSet, Finset.mem_insert, w3cc_mem_inh]
  constructor
  · rintro ⟨hown, hT⟩
    have hX4 : geoOwner hP S' m = A ∨ geoOwner hP S' m = B ∨ geoOwner hP S' m = C ∨ geoOwner hP S' m = Z := by
      rcases hXne with rfl | rfl | rfl
      · exact Or.inl hown
      · exact Or.inr (Or.inl hown)
      · exact Or.inr (Or.inr (Or.inl hown))
    rcases hC.cover m hT hX4 with ⟨hTS, hq⟩ | h6
    · exact Or.inr ⟨⟨hq, hTS⟩, hown⟩
    · exact Or.inl (hsix m h6 hown)
  · rintro (rfl | ⟨⟨hq, hTS⟩, hown⟩)
    · refine ⟨hownX, ?_⟩
      rw [isTrueCorner_visit, visitTwin_crossing]
      exact hzX
    · exact ⟨hown, w3cc_isTrueCorner_mono hC.subset m hTS⟩

theorem w3cc_cornerSet_A :
    w3cc_cornerSet hP S' A = insert (Sum.inr (visitTwin zA)) (w3cc_inh hP S' q₀ A) := by
  refine w3cc_cornerSet_outer hP hC A zA hC.memA.1 hC.ownA (Or.inl rfl) ?_
  rintro m (rfl | rfl | rfl | rfl | rfl | rfl) h
  · exact absurd (h.symm.trans hC.ownZ.1) hC.distinct.2.2.1
  · exact absurd (h.symm.trans hC.ownZ.2.1) hC.distinct.2.2.1
  · exact absurd (h.symm.trans hC.ownZ.2.2) hC.distinct.2.2.1
  · rfl
  · exact absurd (h.symm.trans hC.ownB) hC.distinct.1
  · exact absurd (h.symm.trans hC.ownC) hC.distinct.2.1

theorem w3cc_cornerSet_B :
    w3cc_cornerSet hP S' B = insert (Sum.inr (visitTwin zB)) (w3cc_inh hP S' q₀ B) := by
  refine w3cc_cornerSet_outer hP hC B zB hC.memB.1 hC.ownB (Or.inr (Or.inl rfl)) ?_
  rintro m (rfl | rfl | rfl | rfl | rfl | rfl) h
  · exact absurd (h.symm.trans hC.ownZ.1) hC.distinct.2.2.2.2.1
  · exact absurd (h.symm.trans hC.ownZ.2.1) hC.distinct.2.2.2.2.1
  · exact absurd (h.symm.trans hC.ownZ.2.2) hC.distinct.2.2.2.2.1
  · exact absurd (h.symm.trans hC.ownA).symm hC.distinct.1
  · rfl
  · exact absurd (h.symm.trans hC.ownC) hC.distinct.2.2.2.1

theorem w3cc_cornerSet_C :
    w3cc_cornerSet hP S' C = insert (Sum.inr (visitTwin zC)) (w3cc_inh hP S' q₀ C) := by
  refine w3cc_cornerSet_outer hP hC C zC hC.memC.1 hC.ownC (Or.inr (Or.inr rfl)) ?_
  rintro m (rfl | rfl | rfl | rfl | rfl | rfl) h
  · exact absurd (h.symm.trans hC.ownZ.1) hC.distinct.2.2.2.2.2
  · exact absurd (h.symm.trans hC.ownZ.2.1) hC.distinct.2.2.2.2.2
  · exact absurd (h.symm.trans hC.ownZ.2.2) hC.distinct.2.2.2.2.2
  · exact absurd (h.symm.trans hC.ownA).symm hC.distinct.2.1
  · exact absurd (h.symm.trans hC.ownB).symm hC.distinct.2.2.2.1
  · rfl

/-- **The corner set of the central triangle**: exactly the three inner visits. -/
theorem w3cc_cornerSet_Z :
    w3cc_cornerSet hP S' Z = {Sum.inr zA, Sum.inr zB, Sum.inr zC} := by
  ext m
  rw [w3cc_mem_cornerSet, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hown, hT⟩
    rcases hC.cover m hT (Or.inr (Or.inr (Or.inr hown))) with ⟨hTS, hq⟩ | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      rcases hC.inherited m hTS hq with h | h | h
      · exact hC.distinct.2.2.1 (h.symm.trans hown)
      · exact hC.distinct.2.2.2.2.1 (h.symm.trans hown)
      · exact hC.distinct.2.2.2.2.2 (h.symm.trans hown)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd (hC.ownA.symm.trans hown) hC.distinct.2.2.1
    · exact absurd (hC.ownB.symm.trans hown) hC.distinct.2.2.2.2.1
    · exact absurd (hC.ownC.symm.trans hown) hC.distinct.2.2.2.2.2
  · rintro (rfl | rfl | rfl)
    · exact ⟨hC.ownZ.1, (isTrueCorner_visit _ _).mpr hC.memA.1⟩
    · exact ⟨hC.ownZ.2.1, (isTrueCorner_visit _ _).mpr hC.memB.1⟩
    · exact ⟨hC.ownZ.2.2, (isTrueCorner_visit _ _).mpr hC.memC.1⟩

/-- The three inner visits are pairwise distinct marks (through the owners of their twins). -/
theorem w3cc_zA_ne_zB : (Sum.inr zA : Mark P) ≠ Sum.inr zB := by
  intro h
  have e : zA = zB := Sum.inr.inj h
  apply hC.distinct.1
  rw [← hC.ownA, ← hC.ownB, e]

theorem w3cc_zA_ne_zC : (Sum.inr zA : Mark P) ≠ Sum.inr zC := by
  intro h
  have e : zA = zC := Sum.inr.inj h
  apply hC.distinct.2.1
  rw [← hC.ownA, ← hC.ownC, e]

theorem w3cc_zB_ne_zC : (Sum.inr zB : Mark P) ≠ Sum.inr zC := by
  intro h
  have e : zB = zC := Sum.inr.inj h
  apply hC.distinct.2.2.2.1
  rw [← hC.ownB, ← hC.ownC, e]

/-- The central triangle has three corners. -/
theorem w3cc_cornerCount_Z : geoCornerCount hP S' Z = 3 := by
  classical
  rw [w3cc_geoCornerCount_eq_card, w3cc_cornerSet_Z hP hC, Finset.card_insert_of_notMem,
    Finset.card_pair (w3cc_zB_ne_zC hP hC)]
  rw [Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · exact w3cc_zA_ne_zB hP hC h
  · exact w3cc_zA_ne_zC hP hC h

/-- The sum over the corners of the central triangle. -/
theorem w3cc_sum_Z (f : Mark P → ℝ) :
    ∑ m ∈ w3cc_cornerSet hP S' Z, f m = f (Sum.inr zA) + f (Sum.inr zB) + f (Sum.inr zC) := by
  classical
  rw [w3cc_cornerSet_Z hP hC, Finset.sum_insert, Finset.sum_pair (w3cc_zB_ne_zC hP hC), add_assoc]
  rw [Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · exact w3cc_zA_ne_zB hP hC h
  · exact w3cc_zA_ne_zC hP hC h

omit hC in
/-- The smoothing corner of an outer carrier is not an inherited corner. -/
theorem w3cc_twin_notMem_inh (X : GeoComponent hP S') (zX : Visit P) (hzX : zX.1 ∉ S) :
    Sum.inr (visitTwin zX) ∉ w3cc_inh hP S' q₀ X := by
  intro h
  rw [w3cc_mem_inh] at h
  have hT : IsTrueCorner S (Sum.inr (visitTwin zX)) := h.1.2
  rw [isTrueCorner_visit, visitTwin_crossing] at hT
  exact hzX hT

omit hC in
/-- The sum over the corners of an outer carrier (generic `M`, for both the real turn ledger and the
corner count). -/
theorem w3cc_sum_outer {M : Type*} [AddCommMonoid M] (f : Mark P → M) (X : GeoComponent hP S')
    (zX : Visit P) (hzX : zX.1 ∉ S)
    (hXeq : w3cc_cornerSet hP S' X = insert (Sum.inr (visitTwin zX)) (w3cc_inh hP S' q₀ X)) :
    ∑ m ∈ w3cc_cornerSet hP S' X, f m = f (Sum.inr (visitTwin zX)) + ∑ m ∈ w3cc_inh hP S' q₀ X, f m := by
  classical
  rw [hXeq, Finset.sum_insert (w3cc_twin_notMem_inh hP X zX hzX)]

omit hC in
open scoped Classical in
theorem w3cc_sum_inh_eq {M : Type*} [AddCommMonoid M] (f : Mark P → M) (X : GeoComponent hP S') :
    ∑ m ∈ w3cc_inh hP S' q₀ X, f m =
      ∑ m ∈ w3cc_cornerSet hP S q₀, (if geoOwner hP S' m = X then f m else 0) := by
  classical
  unfold w3cc_inh
  rw [Finset.sum_filter]

/-- **The inherited corners partition**: the corners of `q₀` are the inherited corners of `A`, `B`, `C`. -/
theorem w3cc_inh_partition {M : Type*} [AddCommMonoid M] (f : Mark P → M) :
    ∑ m ∈ w3cc_cornerSet hP S q₀, f m =
      ∑ m ∈ w3cc_inh hP S' q₀ A, f m + ∑ m ∈ w3cc_inh hP S' q₀ B, f m + ∑ m ∈ w3cc_inh hP S' q₀ C, f m := by
  classical
  rw [w3cc_sum_inh_eq, w3cc_sum_inh_eq, w3cc_sum_inh_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [w3cc_mem_cornerSet] at hm
  have d := hC.distinct
  rcases hC.inherited m hm.2 hm.1 with h | h | h <;> rw [h] <;>
    simp [d.1, d.2.1, d.2.2.2.1, Ne.symm d.1, Ne.symm d.2.1, Ne.symm d.2.2.2.1]

/-- **The corner-count ledger**: `c_A + c_B + c_C = c_{q₀} + 3`. -/
theorem w3cc_cornerCount_ledger :
    geoCornerCount hP S' A + geoCornerCount hP S' B + geoCornerCount hP S' C = geoCornerCount hP S q₀ + 3 := by
  classical
  rw [w3cc_geoCornerCount_eq_card, w3cc_geoCornerCount_eq_card, w3cc_geoCornerCount_eq_card,
    w3cc_geoCornerCount_eq_card, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
    Finset.card_eq_sum_ones,
    w3cc_sum_outer hP (fun _ => (1 : ℕ)) A zA hC.memA.2 (w3cc_cornerSet_A hP hC),
    w3cc_sum_outer hP (fun _ => (1 : ℕ)) B zB hC.memB.2 (w3cc_cornerSet_B hP hC),
    w3cc_sum_outer hP (fun _ => (1 : ℕ)) C zC hC.memC.2 (w3cc_cornerSet_C hP hC),
    w3cc_inh_partition hP hC (fun _ => (1 : ℕ))]
  ring

end W3CC_Ledger

/-! #### C3. The rotation ledger and the signed patterns, on a CV-generic polygon -/

section W3CC_Rot

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P) {S S' : Finset (Crossing P)}
  (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG.crossingGeometry)
  {q₀ : GeoComponent hG.crossingGeometry S} {A B C Z : GeoComponent hG.crossingGeometry S'} {zA zB zC : Visit P}

/-- **`2π rot(L) = Σ` over the corner marks of `L`** (lem:turnlift (ii), `CV.two_pi_mul_rot`). -/
theorem w3cc_two_pi_rot {T : Finset (Crossing P)} (hT : T ∈ CV.Ind hG.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry T) :
    2 * Real.pi * (CV.rot (geoCornerPolygon hG.crossingGeometry T q) (CV.carrierPolygon_cvRegular hn hG hT q) : ℝ) =
      ∑ m ∈ w3cc_cornerSet hG.crossingGeometry T q, w3cc_markPT hG.crossingGeometry T m := by
  rw [CV.two_pi_mul_rot, ← w3cc_sum_corners]
  exact Finset.sum_congr rfl fun k _ =>
    w3cc_principalTurn_eq_mark hG.crossingGeometry hn (CV.geoIndependent_of_mem_Ind _ hT) q k

variable (hC : w3cc_SplitCorners hG.crossingGeometry S S' q₀ A B C Z zA zB zC)
include hC

/-- **The rotation ledger (15)**: `rot q₀ = rot A + rot B + rot C + rot Z` — every inherited corner keeps its
principal turn and the six smoothing corners cancel in pairs. -/
theorem w3cc_rot_ledger :
    CV.rot (geoCornerPolygon hG.crossingGeometry S q₀) (CV.carrierPolygon_cvRegular hn hG hS q₀) =
      CV.rot (geoCornerPolygon hG.crossingGeometry S' A) (CV.carrierPolygon_cvRegular hn hG hS' A) +
      CV.rot (geoCornerPolygon hG.crossingGeometry S' B) (CV.carrierPolygon_cvRegular hn hG hS' B) +
      CV.rot (geoCornerPolygon hG.crossingGeometry S' C) (CV.carrierPolygon_cvRegular hn hG hS' C) +
      CV.rot (geoCornerPolygon hG.crossingGeometry S' Z) (CV.carrierPolygon_cvRegular hn hG hS' Z) := by
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  have hA := w3cc_two_pi_rot hn hG hS' A
  have hB := w3cc_two_pi_rot hn hG hS' B
  have hCC := w3cc_two_pi_rot hn hG hS' C
  have hZ := w3cc_two_pi_rot hn hG hS' Z
  have h0 := w3cc_two_pi_rot hn hG hS q₀
  rw [w3cc_sum_outer _ _ A zA hC.memA.2 (w3cc_cornerSet_A _ hC)] at hA
  rw [w3cc_sum_outer _ _ B zB hC.memB.2 (w3cc_cornerSet_B _ hC)] at hB
  rw [w3cc_sum_outer _ _ C zC hC.memC.2 (w3cc_cornerSet_C _ hC)] at hCC
  rw [w3cc_sum_Z _ hC] at hZ
  have hinh : ∑ m ∈ w3cc_cornerSet hG.crossingGeometry S q₀, w3cc_markPT hG.crossingGeometry S m =
      ∑ m ∈ w3cc_cornerSet hG.crossingGeometry S q₀, w3cc_markPT hG.crossingGeometry S' m :=
    Finset.sum_congr rfl fun m hm =>
      (w3cc_markPT_mono _ hC.subset m ((w3cc_mem_cornerSet _ S q₀ m).mp hm).2).symm
  rw [hinh, w3cc_inh_partition _ hC] at h0
  have cA := w3cc_new_turns_cancel hG.crossingGeometry hn S' zA hC.memA.1
  have cB := w3cc_new_turns_cancel hG.crossingGeometry hn S' zB hC.memB.1
  have cC := w3cc_new_turns_cancel hG.crossingGeometry hn S' zC hC.memC.1
  have hreal : (2 * Real.pi) *
      (CV.rot (geoCornerPolygon hG.crossingGeometry S q₀) (CV.carrierPolygon_cvRegular hn hG hS q₀) : ℝ) =
      (2 * Real.pi) *
      ((CV.rot (geoCornerPolygon hG.crossingGeometry S' A) (CV.carrierPolygon_cvRegular hn hG hS' A) : ℝ) +
        CV.rot (geoCornerPolygon hG.crossingGeometry S' B) (CV.carrierPolygon_cvRegular hn hG hS' B) +
        CV.rot (geoCornerPolygon hG.crossingGeometry S' C) (CV.carrierPolygon_cvRegular hn hG hS' C) +
        CV.rot (geoCornerPolygon hG.crossingGeometry S' Z) (CV.carrierPolygon_cvRegular hn hG hS' Z)) := by
    rw [mul_add, mul_add, mul_add, hA, hB, hCC, hZ, h0]
    linarith
  have := mul_left_cancel₀ h2π hreal
  exact_mod_cast this

omit hC in
include hn hS' in
/-- The mark turn at an inner visit is the common sign of the central triangle. -/
theorem w3cc_markTurn_inner {ζ : SignType} (hζ : ∀ k, turn (geoCornerPolygon hG.crossingGeometry S' Z) k = ζ)
    (zX : Visit P) (hzX : zX.1 ∈ S') (hown : geoOwner hG.crossingGeometry S' (Sum.inr zX) = Z) :
    w3cc_markTurn hG.crossingGeometry S' (Sum.inr zX) = ζ := by
  obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hG.crossingGeometry S' Z (Sum.inr zX) hown
    ((isTrueCorner_visit _ _).mpr hzX)
  rw [← hk, ← w3cc_turn_eq_mark hG.crossingGeometry hn (CV.geoIndependent_of_mem_Ind _ hS') Z
    (CV.carrierPolygon_cvRegular hn hG hS' Z) k]
  exact hζ k

include hn hS hS' in
/-- **The corner-sign shape of an outer carrier** (ESC §4): its smoothing corner turns by `−ζ` (the negative
of the central sign) and every other corner is an inherited corner of `q₀`, turning by `τ`. -/
theorem w3cc_outer_shape (X : GeoComponent hG.crossingGeometry S') (zX : Visit P) (hzX : zX.1 ∈ S')
    (hownX : geoOwner hG.crossingGeometry S' (Sum.inr (visitTwin zX)) = X)
    (hXeq : w3cc_cornerSet hG.crossingGeometry S' X =
      insert (Sum.inr (visitTwin zX)) (w3cc_inh hG.crossingGeometry S' q₀ X))
    {τ : SignType} (hτ : ∀ k, turn (geoCornerPolygon hG.crossingGeometry S q₀) k = τ)
    {ζ : SignType} (hζX : w3cc_markTurn hG.crossingGeometry S' (Sum.inr zX) = ζ) :
    ∃ k₀ : ZMod (geoCornerCount hG.crossingGeometry S' X),
      geoCornerMark hG.crossingGeometry S' X k₀ = Sum.inr (visitTwin zX) ∧
      turn (geoCornerPolygon hG.crossingGeometry S' X) k₀ = -ζ ∧
      ∀ k, k ≠ k₀ → turn (geoCornerPolygon hG.crossingGeometry S' X) k = τ := by
  have hind := CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS
  have hind' := CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS'
  have hreg := CV.carrierPolygon_cvRegular hn hG hS q₀
  have hreg' := CV.carrierPolygon_cvRegular hn hG hS' X
  have hT : IsTrueCorner S' (Sum.inr (visitTwin zX)) := by
    rw [isTrueCorner_visit, visitTwin_crossing]
    exact hzX
  obtain ⟨k₀, hk₀⟩ := geoCornerMark_exists_of_owner hG.crossingGeometry S' X _ hownX hT
  refine ⟨k₀, hk₀, ?_, ?_⟩
  · rw [w3cc_turn_eq_mark hG.crossingGeometry hn hind' X hreg' k₀, hk₀,
      w3cc_markTurn_twin hG.crossingGeometry hn S' zX hzX, hζX]
  · intro k hk
    have hmem : geoCornerMark hG.crossingGeometry S' X k ∈ w3cc_cornerSet hG.crossingGeometry S' X :=
      (w3cc_mem_cornerSet _ _ _ _).mpr (geoCornerMark_mem _ _ _ k)
    rw [hXeq, Finset.mem_insert, w3cc_mem_inh] at hmem
    rcases hmem with h | ⟨⟨hq, hTS⟩, -⟩
    · exact absurd (geoCornerMark_injective _ _ _ (h.trans hk₀.symm)) hk
    · obtain ⟨k', hk'⟩ := geoCornerMark_exists_of_owner hG.crossingGeometry S q₀ _ hq hTS
      rw [w3cc_turn_eq_mark hG.crossingGeometry hn hind' X hreg' k,
        w3cc_markTurn_mono hG.crossingGeometry hC.subset _ hTS, ← hk',
        ← w3cc_turn_eq_mark hG.crossingGeometry hn hind q₀ hreg k']
      exact hτ k'

omit [NeZero n] hC in
/-- A shape with dissent `−ζ`, `ζ ∈ {τ, −τ}`, is a signed pattern of sign `τ`. -/
theorem w3cc_pattern_of_shape {c : ℕ} (L : LabelledTuple c) {τ ζ : SignType} (hζτ : ζ = τ ∨ ζ = -τ)
    (h : ∃ k₀, turn L k₀ = -ζ ∧ ∀ k, k ≠ k₀ → turn L k = τ) : w3cc_Pattern L τ := by
  obtain ⟨k₀, hk₀, hoth⟩ := h
  rcases hζτ with rfl | rfl
  · exact Or.inr ⟨k₀, hk₀, hoth⟩
  · left
    intro k
    by_cases hk : k = k₀
    · rw [hk, hk₀, neg_neg]
    · exact hoth k hk

omit hC in
include hn hS' in
/-- A shape with dissent `−τ` on a polygon with at least two corners is mixed. -/
theorem w3cc_mixed_of_shape (X : GeoComponent hG.crossingGeometry S') {τ : SignType} (hτ0 : τ ≠ 0)
    (h : ∃ k₀, turn (geoCornerPolygon hG.crossingGeometry S' X) k₀ = -τ ∧
      ∀ k, k ≠ k₀ → turn (geoCornerPolygon hG.crossingGeometry S' X) k = τ) :
    CV.CarrierMixed hG.crossingGeometry S' X := by
  obtain ⟨k₀, hk₀, hoth⟩ := h
  rintro ⟨τ', -, hτ'⟩
  have h3 : 3 ≤ geoCornerCount hG.crossingGeometry S' X :=
    three_le_geoCornerCount hn (CarrierGeometry.ofCV hG) (CV.geoIndependent_of_mem_Ind _ hS') X
  obtain ⟨k₁, hk₁⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [ZMod.card]; omega : 1 < Fintype.card (ZMod (geoCornerCount hG.crossingGeometry S' X))) k₀
  have e1 : τ' = -τ := (hτ' k₀).symm.trans hk₀
  have e2 : τ' = τ := (hτ' k₁).symm.trans (hoth k₁ hk₁)
  exact hτ0 (w3cc_signType_eq_zero_of_eq_neg (e2.symm.trans e1))

include hn hS' in
/-- **The central triangle is uniform**: it has exactly three corners (`w3cc_cornerCount_Z`), and a regular
triangle turns one way (`w3cc_uniform_of_three`) — lem:uniformrot (i)'s "three same-sign corners". -/
theorem w3cc_central_uniform_of : CV.CarrierUniform hG.crossingGeometry S' Z :=
  w3cc_uniform_of_three _ (CV.carrierPolygon_cvRegular hn hG hS' Z) (w3cc_cornerCount_Z _ hC)

/-- **`carrierR Z = 1`** (`esc_FullSplitData.central_rot`, for the assembler): the uniform triangle. -/
theorem w3cc_central_rot_of : CV.carrierR hn hG hS' Z = 1 := by
  obtain ⟨ζ, hζ0, hζ⟩ := w3cc_central_uniform_of hn hG hS' hC
  have h := w3cc_rot_uniform_three _ (CV.carrierPolygon_cvRegular hn hG hS' Z) (w3cc_cornerCount_Z _ hC) hζ0 hζ
  have hc : (CV.carrierR hn hG hS' Z : ℤ) = 1 := by
    rw [CV.carrierR_cast, h]
    rcases SignType.trichotomy ζ with rfl | rfl | rfl
    · simp
    · exact absurd rfl hζ0
    · simp
  exact_mod_cast hc

/-! #### C4. The two fields -/

include hn hS hS' in
/-- **`esc_FullSplitData.outer_alternative` from the corner ledger**: "Each outer carrier is uniform in the
live branch and exactly one-dissent in the dead branch … after a possible orientation reversal,
`thm:carrierfloor` applies" (ESC §4). -/
theorem w3cc_outer_alternative_of (hq : CV.CarrierUniform hG.crossingGeometry S q₀) :
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S' A) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S' B) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S' C) := by
  obtain ⟨τ, hτ0, hτ⟩ := hq
  obtain ⟨ζ, hζ0, hζ⟩ := w3cc_central_uniform_of hn hG hS' hC
  have hζτ := w3cc_signType_eq_or_neg hζ0 hτ0
  obtain ⟨kA, -, hkA, hoA⟩ := w3cc_outer_shape hn hG hS hS' hC A zA hC.memA.1 hC.ownA (w3cc_cornerSet_A _ hC) hτ
    (w3cc_markTurn_inner hn hG hS' hζ zA hC.memA.1 hC.ownZ.1)
  obtain ⟨kB, -, hkB, hoB⟩ := w3cc_outer_shape hn hG hS hS' hC B zB hC.memB.1 hC.ownB (w3cc_cornerSet_B _ hC) hτ
    (w3cc_markTurn_inner hn hG hS' hζ zB hC.memB.1 hC.ownZ.2.1)
  obtain ⟨kC, -, hkC, hoC⟩ := w3cc_outer_shape hn hG hS hS' hC C zC hC.memC.1 hC.ownC (w3cc_cornerSet_C _ hC) hτ
    (w3cc_markTurn_inner hn hG hS' hζ zC hC.memC.1 hC.ownZ.2.2)
  exact ⟨CV.cvt165s_uniformOrOneDissent_of_pattern _ (CV.carrierPolygon_cvRegular hn hG hS' A) τ hτ0
      (w3cc_pattern_of_shape _ hζτ ⟨kA, hkA, hoA⟩),
    CV.cvt165s_uniformOrOneDissent_of_pattern _ (CV.carrierPolygon_cvRegular hn hG hS' B) τ hτ0
      (w3cc_pattern_of_shape _ hζτ ⟨kB, hkB, hoB⟩),
    CV.cvt165s_uniformOrOneDissent_of_pattern _ (CV.carrierPolygon_cvRegular hn hG hS' C) τ hτ0
      (w3cc_pattern_of_shape _ hζτ ⟨kC, hkC, hoC⟩)⟩

/-- **`esc_FullSplitData.uniform` from the corner ledger**: the two exhaustive branches of a uniform contact
carrier — live `ζ = −τ` ((16) `R_A + R_B + R_C = R + 1`, (14) `W_full = −W`) and dead `ζ = τ`
((16) `R_A + R_B + R_C + 1 = R`, `W_full = 0`). -/
theorem w3cc_uniform_of (hq : CV.CarrierUniform hG.crossingGeometry S q₀) :
    (CV.carrierR hn hG hS' A + CV.carrierR hn hG hS' B + CV.carrierR hn hG hS' C = CV.carrierR hn hG hS q₀ + 1 ∧
      CV.weight hG.crossingGeometry S' A * CV.weight hG.crossingGeometry S' B *
        CV.weight hG.crossingGeometry S' C * CV.weight hG.crossingGeometry S' Z =
        -CV.weight hG.crossingGeometry S q₀) ∨
    (CV.carrierR hn hG hS' A + CV.carrierR hn hG hS' B + CV.carrierR hn hG hS' C + 1 = CV.carrierR hn hG hS q₀ ∧
      CV.weight hG.crossingGeometry S' A * CV.weight hG.crossingGeometry S' B *
        CV.weight hG.crossingGeometry S' C * CV.weight hG.crossingGeometry S' Z = 0) := by
  obtain ⟨τ, hτ0, hτ⟩ := hq
  obtain ⟨ζ, hζ0, hζ⟩ := w3cc_central_uniform_of hn hG hS' hC
  have hregA := CV.carrierPolygon_cvRegular hn hG hS' A
  have hregB := CV.carrierPolygon_cvRegular hn hG hS' B
  have hregC := CV.carrierPolygon_cvRegular hn hG hS' C
  have hregZ := CV.carrierPolygon_cvRegular hn hG hS' Z
  have hreg0 := CV.carrierPolygon_cvRegular hn hG hS q₀
  obtain ⟨kA, -, hkA, hoA⟩ := w3cc_outer_shape hn hG hS hS' hC A zA hC.memA.1 hC.ownA (w3cc_cornerSet_A _ hC) hτ
    (w3cc_markTurn_inner hn hG hS' hζ zA hC.memA.1 hC.ownZ.1)
  obtain ⟨kB, -, hkB, hoB⟩ := w3cc_outer_shape hn hG hS hS' hC B zB hC.memB.1 hC.ownB (w3cc_cornerSet_B _ hC) hτ
    (w3cc_markTurn_inner hn hG hS' hζ zB hC.memB.1 hC.ownZ.2.1)
  obtain ⟨kC, -, hkC, hoC⟩ := w3cc_outer_shape hn hG hS hS' hC C zC hC.memC.1 hC.ownC (w3cc_cornerSet_C _ hC) hτ
    (w3cc_markTurn_inner hn hG hS' hζ zC hC.memC.1 hC.ownZ.2.2)
  have hledger := w3cc_rot_ledger hn hG hS hS' hC
  have hrotZ := w3cc_rot_uniform_three _ hregZ (w3cc_cornerCount_Z _ hC) hζ0 hζ
  have hray0 := w3cc_one_le_sign_mul_rot _ hreg0 hτ0 (Or.inl hτ)
  have hcount := w3cc_cornerCount_ledger hG.crossingGeometry hC
  rcases w3cc_signType_eq_or_neg hζ0 hτ0 with hζτ | hζτ
  · -- dead branch: `ζ = τ`, each outer carrier has the one dissent `−τ`
    right
    have hpA : w3cc_Pattern (geoCornerPolygon hG.crossingGeometry S' A) τ :=
      Or.inr ⟨kA, by rw [hkA, hζτ], hoA⟩
    have hpB : w3cc_Pattern (geoCornerPolygon hG.crossingGeometry S' B) τ :=
      Or.inr ⟨kB, by rw [hkB, hζτ], hoB⟩
    have hpC : w3cc_Pattern (geoCornerPolygon hG.crossingGeometry S' C) τ :=
      Or.inr ⟨kC, by rw [hkC, hζτ], hoC⟩
    constructor
    · have hZ : (CV.rot (geoCornerPolygon hG.crossingGeometry S' Z) hregZ) = (τ : ℤ) := by rw [hrotZ, hζτ]
      have habs := w3cc_abs_ledger_dead hτ0 (by rw [← hZ]; exact hledger.symm) hray0
        (w3cc_one_le_sign_mul_rot _ hregA hτ0 hpA) (w3cc_one_le_sign_mul_rot _ hregB hτ0 hpB)
        (w3cc_one_le_sign_mul_rot _ hregC hτ0 hpC)
      have hc : (CV.carrierR hn hG hS' A : ℤ) + CV.carrierR hn hG hS' B + CV.carrierR hn hG hS' C + 1 =
          CV.carrierR hn hG hS q₀ := by
        rw [CV.carrierR_cast, CV.carrierR_cast, CV.carrierR_cast, CV.carrierR_cast]
        exact habs
      exact_mod_cast hc
    · have hwA : CV.weight hG.crossingGeometry S' A = 0 :=
        CV.weight_of_mixed _ _ _ (w3cc_mixed_of_shape hn hG hS' A hτ0 ⟨kA, by rw [hkA, hζτ], hoA⟩)
      rw [hwA, zero_mul, zero_mul, zero_mul]
  · -- live branch: `ζ = −τ`, the outer carriers are uniform of sign `τ`
    left
    have huA : ∀ k, turn (geoCornerPolygon hG.crossingGeometry S' A) k = τ := by
      intro k
      by_cases hk : k = kA
      · rw [hk, hkA, hζτ, neg_neg]
      · exact hoA k hk
    have huB : ∀ k, turn (geoCornerPolygon hG.crossingGeometry S' B) k = τ := by
      intro k
      by_cases hk : k = kB
      · rw [hk, hkB, hζτ, neg_neg]
      · exact hoB k hk
    have huC : ∀ k, turn (geoCornerPolygon hG.crossingGeometry S' C) k = τ := by
      intro k
      by_cases hk : k = kC
      · rw [hk, hkC, hζτ, neg_neg]
      · exact hoC k hk
    constructor
    · have hZ : (CV.rot (geoCornerPolygon hG.crossingGeometry S' Z) hregZ) = -(τ : ℤ) := by
        rw [hrotZ, hζτ, SignType.coe_neg]
      have habs := w3cc_abs_ledger_live hτ0 (by rw [hledger, hZ]; ring) hray0
        (w3cc_one_le_sign_mul_rot _ hregA hτ0 (Or.inl huA)) (w3cc_one_le_sign_mul_rot _ hregB hτ0 (Or.inl huB))
        (w3cc_one_le_sign_mul_rot _ hregC hτ0 (Or.inl huC))
      have hc : (CV.carrierR hn hG hS' A : ℤ) + CV.carrierR hn hG hS' B + CV.carrierR hn hG hS' C =
          CV.carrierR hn hG hS q₀ + 1 := by
        rw [CV.carrierR_cast, CV.carrierR_cast, CV.carrierR_cast, CV.carrierR_cast]
        exact habs
      exact_mod_cast hc
    · have hZ3 := w3cc_cornerCount_Z hG.crossingGeometry hC
      rcases SignType.trichotomy τ with rfl | rfl | rfl
      · -- all right turns: the outer weights are `1`, the central triangle turns left, `(−1)^3 = −1`
        have hζ1 : ζ = 1 := by subst hζτ; decide
        rw [CV.weight_of_all_right _ _ _ huA, CV.weight_of_all_right _ _ _ huB, CV.weight_of_all_right _ _ _ huC,
          CV.weight_of_all_right _ _ _ hτ, CV.weight_of_all_left _ _ _ (fun k => (hζ k).trans hζ1), hZ3]
        norm_num
      · exact absurd rfl hτ0
      · -- all left turns: the outer weights are `(−1)^{c}`, the central triangle turns right
        have hζ1 : ζ = -1 := by subst hζτ; decide
        rw [CV.weight_of_all_left _ _ _ huA, CV.weight_of_all_left _ _ _ huB, CV.weight_of_all_left _ _ _ huC,
          CV.weight_of_all_left _ _ _ hτ, CV.weight_of_all_right _ _ _ (fun k => (hζ k).trans hζ1), mul_one,
          ← pow_add, ← pow_add, hcount, pow_add]
        norm_num

end W3CC_Rot

/-! #### C5. Assembly and the SPLITA black box -/

/-- **`esc_FullSplitData` from the corner ledger** (this unit's two fields `outer_alternative`, `uniform`,
plus `distinct` and `central_rot` read off the ledger) **and the five remaining fields** (units SPLITA:
`touching_iff`, `central_no_piece`; SPLITB: `writhe`, `mixed`), for the assembler of `w3bi_esc_outer_data`. -/
theorem w3cc_fullSplitData_of (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P) (e f g : ZMod n)
    {Q : Finset (Crossing P)} (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (q₀ : GeoComponent hG.crossingGeometry Q)
    (A B C Z : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)) (Λ : ℕ) {zA zB zC : Visit P}
    (hC : w3cc_SplitCorners hG.crossingGeometry Q (Q ∪ triangleCrossings P e f g) q₀ A B C Z zA zB zC)
    (touching_iff : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry (Q ∪ triangleCrossings P e f g) e f g q ↔
      (q = A ∨ q = B ∨ q = C ∨ q = Z))
    (central_no_piece : CV.piecesOn hG.crossingGeometry (Q ∪ triangleCrossings P e f g) Z = ∅)
    (writhe : CV.groupedWrithe hG q₀ =
      3 + CV.groupedWrithe hG A + CV.groupedWrithe hG B + CV.groupedWrithe hG C + 2 * (Λ : ℤ))
    (mixed : CV.CarrierMixed hG.crossingGeometry Q q₀ →
      CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
        CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0) :
    esc_FullSplitData hn hG e f g hQ hS q₀ A B C Z Λ where
  touching_iff := touching_iff
  distinct := hC.distinct
  central_no_piece := central_no_piece
  central_rot := w3cc_central_rot_of hn hG hS hC
  writhe := writhe
  mixed := mixed
  outer_alternative := w3cc_outer_alternative_of hn hG hQ hS hC
  uniform := w3cc_uniform_of hn hG hQ hS hC

/-- **BLACK BOX (unit SPLITA, stated by this unit): the corner ledger holds for SPLITA's carriers at every
configuration of the extended interface** — the binders of `w3bi_esc_outer`; conclusion: four carriers
`A, B, C, Z` of `Q' ∪ T'` and three inner visits with `w3cc_SplitCorners` relative to the contact carrier
`q₀'` of `Q'`.  Consumed by `w3cc_fullSplitData_of` (with SPLITA's `touching_iff`, `central_no_piece` and
SPLITB's `writhe`, `mixed`) to produce the `esc_FullSplitData` conjunct of `w3bi_esc_outer`. -/
def w3cc_splitA_corners : Prop :=
  ∀ {n : ℕ} [NeZero n] (_hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (_hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (_hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (zA zB zC : Visit (E.curve t')),
        w3cc_SplitCorners (geomAt E t' ht'.1) (transportSupport hs Q)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀' A B C Z zA zB zC

/-! #### (W3C assembler, `w3cx_`) SPLITC's corner ledger from SPLITA's carriers -/

/-- (W3C assembler) **`w3cc_SplitCorners` from SPLITA's core data** (abstract form): with the six-visit data `D`
(twins, `a, b, c ∉ Q`), `S = Q ∪ {a, b, c}` (instance-free, as `w3ca_core` takes it), the core `w3ca_CoreData` (whose
`central` clause names the three inner visits `zA zB zC` and says `Z` owns exactly them), the definitions of the
outer carriers (`w3ca_Ac/Bc/Cc`: the carrier of the other visit of the same crossing, by the orientation pattern)
and the marks partition (`w3ca_marks_partition`: a mark is on `A ∪ B ∪ C ∪ Z` iff it is on `q₀`).  `ownA/B/C`: in
either orientation pattern the outer carrier `X` is by definition the owner of one visit of its crossing and `Z` of
the other, and `Z ≠ X`, so the inner visit `zX` is the visit `Z` owns and `X` owns its twin.  `inherited`: a
`q₀`-mark on `Z` is one of `zA, zB, zC`, whose crossings are not in `Q`, so it is not a true corner of `Q`.
`cover`: a true corner of `S` on `A ∪ B ∪ C ∪ Z` is on `q₀`; its crossing is in `Q` or is `a`, `b` or `c`, and
the two visits of `a` are `zA` and its twin (`visit_eq_or_twin`). -/
theorem w3cx_splitCorners_of_core {P : LabelledTuple n} (hP : CrossingGeometry P) {Q S : Finset (Crossing P)}
    {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P} (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂)
    (hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = a₁.1 ∨ x = b₁.1 ∨ x = c₁.1)
    {A B C Z : GeoComponent hP S} (core : w3ca_CoreData hP S a₁ a₂ b₁ b₂ c₁ c₂ A B C Z)
    (hA : A = w3ca_Ac hP S a₁ a₂ b₁) (hB : B = w3ca_Bc hP S a₁ b₁ b₂) (hC : C = w3ca_Cc hP S a₁ b₁ c₁ c₂)
    (q₀ : GeoComponent hP Q)
    (hpart : ∀ m : Mark P, (geoOwner hP S m = A ∨ geoOwner hP S m = B ∨ geoOwner hP S m = C ∨
      geoOwner hP S m = Z) ↔ geoOwner hP Q m = q₀) :
    ∃ zA zB zC : Visit P, w3cc_SplitCorners hP Q S q₀ A B C Z zA zB zC := by
  obtain ⟨zA, zB, zC, hzA, hzB, hzC, hiff⟩ := core.central
  have hQS : Q ⊆ S := fun x hx => (hSeq x).mpr (Or.inl hx)
  have haS : a₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inl rfl))
  have hbS : b₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hcS : c₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have ownZA : geoOwner hP S (Sum.inr zA) = Z := (hiff _).mpr (Or.inl rfl)
  have ownZB : geoOwner hP S (Sum.inr zB) = Z := (hiff _).mpr (Or.inr (Or.inl rfl))
  have ownZC : geoOwner hP S (Sum.inr zC) = Z := (hiff _).mpr (Or.inr (Or.inr rfl))
  obtain ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩ := core.distinct
  -- the outer ownerships, by the orientation pattern in the definitions
  have hown : geoOwner hP S (Sum.inr (visitTwin zA)) = A ∧ geoOwner hP S (Sum.inr (visitTwin zB)) = B ∧
      geoOwner hP S (Sum.inr (visitTwin zC)) = C := by
    by_cases h : geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁
    · simp only [w3ca_Ac, w3ca_Bc, w3ca_Cc, h, ↓reduceIte] at hA hB hC
      refine ⟨?_, ?_, ?_⟩
      · rcases visit_eq_or_twin a₁ zA hzA with h1 | h1
        · exact absurd (hA.trans (by rw [← h1, ownZA])) hAZ
        · rw [h1, D.ta, D.ta']; exact hA.symm
      · rcases visit_eq_or_twin b₁ zB hzB with h1 | h1
        · rw [h1, D.tb]; exact hB.symm
        · exact absurd (hB.trans (by rw [← D.tb, ← h1, ownZB])) hBZ
      · rcases visit_eq_or_twin c₁ zC hzC with h1 | h1
        · rw [h1, D.tc]; exact hC.symm
        · exact absurd (hC.trans (by rw [← D.tc, ← h1, ownZC])) hCZ
    · simp only [w3ca_Ac, w3ca_Bc, w3ca_Cc, h, ↓reduceIte] at hA hB hC
      refine ⟨?_, ?_, ?_⟩
      · rcases visit_eq_or_twin a₁ zA hzA with h1 | h1
        · rw [h1, D.ta]; exact hA.symm
        · exact absurd (hA.trans (by rw [← D.ta, ← h1, ownZA])) hAZ
      · rcases visit_eq_or_twin b₁ zB hzB with h1 | h1
        · exact absurd (hB.trans (by rw [← h1, ownZB])) hBZ
        · rw [h1, D.tb, D.tb']; exact hB.symm
      · rcases visit_eq_or_twin c₁ zC hzC with h1 | h1
        · exact absurd (hC.trans (by rw [← h1, ownZC])) hCZ
        · rw [h1, D.tc, D.tc']; exact hC.symm
  refine ⟨zA, zB, zC, ?_⟩
  exact {
    subset := hQS
    distinct := ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩
    memA := ⟨by rw [hzA]; exact haS, by rw [hzA]; exact D.aQ⟩
    memB := ⟨by rw [hzB]; exact hbS, by rw [hzB]; exact D.bQ⟩
    memC := ⟨by rw [hzC]; exact hcS, by rw [hzC]; exact D.cQ⟩
    ownZ := ⟨ownZA, ownZB, ownZC⟩
    ownA := hown.1
    ownB := hown.2.1
    ownC := hown.2.2
    inherited := fun m hm hq => by
      rcases (hpart m).mpr hq with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exfalso
        rcases (hiff m).mp h with rfl | rfl | rfl
        · have hm' : zA.1 ∈ Q := hm
          rw [hzA] at hm'
          exact D.aQ hm'
        · have hm' : zB.1 ∈ Q := hm
          rw [hzB] at hm'
          exact D.bQ hm'
        · have hm' : zC.1 ∈ Q := hm
          rw [hzC] at hm'
          exact D.cQ hm'
    cover := fun m hm hown' => by
      have hq : geoOwner hP Q m = q₀ := (hpart m).mp hown'
      rcases m with i | v
      · exact Or.inl ⟨trivial, hq⟩
      · have hv : v.1 ∈ S := hm
        rcases (hSeq _).mp hv with hvQ | hva | hvb | hvc
        · exact Or.inl ⟨hvQ, hq⟩
        · rcases visit_eq_or_twin zA v (hva.trans hzA.symm) with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases visit_eq_or_twin zB v (hvb.trans hzB.symm) with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · rcases visit_eq_or_twin zC v (hvc.trans hzC.symm) with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) }

/-- (W3C assembler) **`w3cc_splitA_corners` PROVED** at every configuration of the extended interface, from
unit SPLITA's `w3ca_split_config` (the core at `t'`), `w3ca_sixData_config` (the six-visit data), and
`w3ca_marks_partition_config` (the marks partition against the contact carrier `q₀'`), with the supports
transported by `GT_outsideSupports_transport` / `GT_fullAvail_transport` and `S' = Q' ∪ T'` read through
`P1.mem_triangleCrossings_iff`. -/
theorem w3cx_splitA_corners_proof : w3cc_splitA_corners := by
  intro n _ _hn E e f g δ hL _hGT _hR t t' ht ht' hop hs hef heg hfg _hK Q hQ hfull _hQi _hQi' hS' _q₀ q₀' _hq₀ hq₀'
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  have D := w3ca_sixData_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull'
  have hSeq : ∀ x, x ∈ transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ↔
      x ∈ transportSupport hs Q ∨ x = xPair ((hs _).mp hef) ∨ x = xPair ((hs _).mp heg) ∨
        x = xPair ((hs _).mp hfg) := by
    intro x
    rw [Finset.mem_union, P1.mem_triangleCrossings_iff ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)]
  obtain ⟨zA, zB, zC, hC⟩ := w3cx_splitCorners_of_core (geomAt E t' ht'.1) D hSeq core rfl rfl rfl q₀'
    (fun m => w3ca_marks_partition_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
      q₀' hq₀' m)
  exact ⟨_, _, _, _, zA, zB, zC, hC⟩

/-- (W3C assembler) the black box CLOSED: unit SPLITA's content in this unit's form (`w3cx_splitA_corners_proof`). -/
theorem w3cc_splitA_corners_data : w3cc_splitA_corners :=
  w3cx_splitA_corners_proof

end W3CC_SplitC

/-! ### Unit BIGON (`w3cz_`): the switch-at-`z₀` bigon forms.  `(D^x).switch y₀` and `(D^x).switch z₀` share the
shadow `Γ₀`; of `BigonData`'s fields only `same_over` reads the over data, and for a bigon whose two crossings ARE
`y₀, z₀` that field says "in `D^x` the over bit of `s` at `y₀` is opposite to the one at `z₀`" (= `hover` pulled back
along `orig`), which is symmetric in which of the two is switched.  So every bigon of unit G on `(D^x).switch y₀`
transfers verbatim to `(D^x).switch z₀` (`w3cz_bigonData_switch_transfer`: 27 of the 28 fields are copied, the
run, the strands, the crossings and the region are unchanged).  The switch-at-`z₀` forms `w3cz_…_switch_z_of_five`
(with G's `hk5 : 5 ≤ k`) and `w3cz_…_switch_z_of_not_kink` (with G's non-kink hypothesis) are PROVED from
`w3bg_…_of_five` / `w3bg_hk5_*_of_not_kink`.  The frozen `w3bi_…_switch_z` statements are FALSE as stated for
exactly unit G's reason: `BigonData.hk : j + 3 ≤ k` is a condition on the SHADOW `Γ₀` (which does not see the
switch), and G's kink counterexample (`t = s − 2` on one component, `k = 4` on the component of `cutStartS`)
satisfies every hypothesis of the switch_z statements too (`clear_vertex` included).  Their bodies are reduced to
the one hypothesis `hk5` exactly as unit G did with `w3g_*` (rule 3). -/

/-- (BIGON) `same_over` moves from `D₀.switch y₀` to `D₀.switch z₀` when `y₀, z₀` are the bigon's own two
crossings: on either switched diagram the condition says that in `D₀` the over bit of `s` at `y₀` is the
opposite of the over bit at `z₀`. -/
theorem w3cz_same_over_switch_swap (D₀ : Diagram) (y₀ z₀ : D₀.Γ.Crossing) (hne : y₀ ≠ z₀) (s : D₀.Γ.Strand)
    (hsy : s ∈ y₀.val) (hsz : s ∈ z₀.val)
    (h : ((D₀.switch y₀).overStrand y₀ = s ∧ (D₀.switch y₀).overStrand z₀ = s) ∨
      ((D₀.switch y₀).overStrand y₀ ≠ s ∧ (D₀.switch y₀).overStrand z₀ ≠ s)) :
    ((D₀.switch z₀).overStrand y₀ = s ∧ (D₀.switch z₀).overStrand z₀ = s) ∨
      ((D₀.switch z₀).overStrand y₀ ≠ s ∧ (D₀.switch z₀).overStrand z₀ ≠ s) := by
  rw [D₀.switch_overStrand_self, D₀.switch_overStrand_of_ne hne.symm] at h
  rw [D₀.switch_overStrand_of_ne hne, D₀.switch_overStrand_self]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right
    refine ⟨?_, ?_⟩
    · rw [← h1]; exact D₀.over_ne_under y₀
    · rw [← h2]; exact D₀.under_ne_over z₀
  · left
    refine ⟨?_, ?_⟩
    · exact (D₀.eq_over_of_mem_of_ne y₀ hsy (Ne.symm h1)).symm
    · exact (D₀.eq_under_of_mem_of_ne z₀ hsz (Ne.symm h2)).symm

/-- (BIGON) **BigonData transfer across the two switched diagrams.**  `D₀.switch y₀` and `D₀.switch z₀` share
the shadow `D₀.Γ`; of `BigonData`'s fields only `same_over` reads the over data, and when the bigon's two
crossings are exactly `{y₀, z₀}` that field transfers by `w3cz_same_over_switch_swap`.  Every other field is
copied verbatim; the run, the strands, the crossings and the region are unchanged. -/
theorem w3cz_bigonData_switch_transfer (D₀ : Diagram) (y₀ z₀ : D₀.Γ.Crossing) (hne : y₀ ≠ z₀)
    (B : BigonData (D₀.switch y₀)) (h : (B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧ B.z = y₀)) :
    ∃ B' : BigonData (D₀.switch z₀),
      B'.j = B.j ∧ B'.y = B.y ∧ B'.z = B.z ∧ B'.s = B.s ∧
      (⟨B'.i, B'.a⟩ : D₀.Γ.Strand) = ⟨B.i, B.a⟩ ∧ B'.K = B.K := by
  have hmy : B.s ∈ B.y.val := by rw [B.hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmz : B.s ∈ B.z.val := by rw [B.hz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have key : ((D₀.switch z₀).overStrand B.y = B.s ∧ (D₀.switch z₀).overStrand B.z = B.s) ∨
      ((D₀.switch z₀).overStrand B.y ≠ B.s ∧ (D₀.switch z₀).overStrand B.z ≠ B.s) := by
    have h0 := B.same_over
    rcases h with ⟨hBy, hBz⟩ | ⟨hBy, hBz⟩
    · rw [hBy] at hmy; rw [hBz] at hmz; rw [hBy, hBz] at h0 ⊢
      exact w3cz_same_over_switch_swap D₀ y₀ z₀ hne B.s hmy hmz h0
    · rw [hBy] at hmy; rw [hBz] at hmz; rw [hBy, hBz] at h0 ⊢
      exact (w3cz_same_over_switch_swap D₀ y₀ z₀ hne B.s hmz hmy (h0.imp And.symm And.symm)).imp And.symm And.symm
  exact ⟨{ i := B.i, a := B.a, j := B.j, hj := B.hj, hk := B.hk, s := B.s, y := B.y, z := B.z, hy := B.hy,
           hz := B.hz, run_free := B.run_free, no_io := B.no_io, same_over := key, ty := B.ty, tz := B.tz,
           tsy := B.tsy, tsz := B.tsz, hty := B.hty, htz := B.htz, htsy := B.htsy, htsz := B.htsz, K := B.K,
           K_convex := B.K_convex, K_compact := B.K_compact, run_mem := B.run_mem, in_iff := B.in_iff,
           out_iff := B.out_iff, s_iff := B.s_iff, clear := B.clear }, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (BIGON) the two triangle crossings `y = {sS, g}` and `z = {tS, g}` are distinct (`sS ≠ tS`, `g ≠ sS`). -/
theorem w3cz_site_y_ne_z (D : Diagram) (x : D.Γ.Crossing) (g : D.Γ.Strand) (hgs : g ≠ sS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g}) : y ≠ z := by
  intro h
  have hmem : sS D x ∈ z.val := by rw [← h, hy]; exact Finset.mem_insert_self _ _
  rw [hz, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact sS_ne_tS D x h1
  · exact hgs h1.symm

/-- (BIGON) smoothing crossings over distinct crossings of `D` are distinct. -/
theorem w3cz_lift_ne (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (hε : SmallEps D x ε) {y z : D.Γ.Crossing} (hyz : y ≠ z) {y₀ z₀ : Γ₀.Crossing}
    (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) : y₀ ≠ z₀ :=
  fun h => hyz (hy₀.symm.trans ((congrArg (origCrossing D x M hε) h).trans hz₀))

/-- (BIGON) **the `arcST` site with the switch at `z₀`, given `hk5`** — `w3bi_bigonData_smooth_arcST_switch_z`
plus unit G's hypothesis `5 ≤ k` on the component of `cutStartS`; PROVED by transferring the bigon of
`w3bg_bigonData_smooth_arcST_of_five` from `(D^x).switch y₀` to `(D^x).switch z₀`. -/
theorem w3cz_bigonData_smooth_arcST_switch_z_of_five (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hk5 : 5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  obtain ⟨B, hj, hBy, hBz, hs, hia, hK⟩ := w3bg_bigonData_smooth_arcST_of_five D x M hε g hgs hgt y z hy hz hsy htz
    hys hzt clear hover y₀ z₀ hy₀ hz₀ hk5
  obtain ⟨B', hj', hy', hz', hs', hia', hK'⟩ := w3cz_bigonData_switch_transfer (toDiagram D x M hε) y₀ z₀
    (w3cz_lift_ne D x M hε (w3cz_site_y_ne_z D x g hgs y z hy hz) hy₀ hz₀) B (Or.inl ⟨hBy, hBz⟩)
  exact ⟨B', hj'.trans hj, hy'.trans hBy, hz'.trans hBz, hs'.trans hs, hia'.trans hia, hK'.trans hK⟩

/-- (BIGON) **the `arcST` site with the switch at `z₀` in `D`'s terms**: `w3bi_bigonData_smooth_arcST_switch_z`
plus the non-kink hypothesis `⟨s.1, s.2 − 1⟩ ≠ ⟨t.1, t.2 + 1⟩` of unit G (`w3bg_hk5_arcST_of_not_kink`). -/
theorem w3cz_bigonData_smooth_arcST_switch_z_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} :=
  w3cz_bigonData_smooth_arcST_switch_z_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (w3bg_hk5_arcST_of_not_kink D x M hkink)

/-- (BIGON) **the `arcTS` site with the switch at `z₀`, given `hk5`** — `w3bi_bigonData_smooth_arcTS_switch_z`
plus unit G's hypothesis `5 ≤ k` on the component of `cutStartT`; the bigon of
`w3bg_bigonData_smooth_arcTS_of_five` (whose `B.y = z₀`, `B.z = y₀`) transferred to `(D^x).switch z₀`. -/
theorem w3cz_bigonData_smooth_arcTS_switch_z_of_five (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hk5 : 5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  obtain ⟨B, hj, hBy, hBz, hs, hia, hK⟩ := w3bg_bigonData_smooth_arcTS_of_five D x M hε g hgs hgt y z hy hz hsy htz
    hys hzt clear hover y₀ z₀ hy₀ hz₀ hk5
  obtain ⟨B', hj', hy', hz', hs', hia', hK'⟩ := w3cz_bigonData_switch_transfer (toDiagram D x M hε) y₀ z₀
    (w3cz_lift_ne D x M hε (w3cz_site_y_ne_z D x g hgs y z hy hz) hy₀ hz₀) B (Or.inr ⟨hBy, hBz⟩)
  exact ⟨B', hj'.trans hj, hy'.trans hBy, hz'.trans hBz, hs'.trans hs, hia'.trans hia, hK'.trans hK⟩

/-- (BIGON) **the `arcTS` site with the switch at `z₀` in `D`'s terms**: `w3bi_bigonData_smooth_arcTS_switch_z`
plus the non-kink hypothesis `⟨t.1, t.2 − 1⟩ ≠ ⟨s.1, s.2 + 1⟩` of unit G (`w3bg_hk5_arcTS_of_not_kink`). -/
theorem w3cz_bigonData_smooth_arcTS_switch_z_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} :=
  w3cz_bigonData_smooth_arcTS_switch_z_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (w3bg_hk5_arcTS_of_not_kink D x M hkink)

/-- (BIGON) **the reduction is exact**: any bigon meeting the conclusion of a switch_z statement (`j = 2`, entering
edge `u`) has `5 ≤ k` on the component of `u` by `BigonData.hk` — a condition on the shadow `Γ₀` alone. -/
theorem w3cz_hk5_of_conclusion (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε) (c : Γ₀.Crossing) (u : Γ₀.Strand)
    (B : BigonData ((toDiagram D x M hε).switch c)) (hj : B.j = 2) (hia : (⟨B.i, B.a⟩ : Γ₀.Strand) = u) :
    5 ≤ (Γ₀.comp u.1).k := by
  have h : B.j + 3 ≤ (Γ₀.comp B.i).k := B.hk
  rw [hj] at h
  have hi : B.i = u.1 := congrArg Sigma.fst hia
  rw [← hi]; exact h

/-- (BIGON) **`w3bi_bigonData_smooth_arcST_switch_z` is EQUIVALENT to `hk5`** under its own hypotheses (rule 3,
made formal): the frozen conclusion holds iff `5 ≤ k` on the component of `cutStartS`.  Since unit G's kink
counterexample satisfies every hypothesis with `k = 4`, the frozen statement is false as stated; `clear_vertex` is
not needed for either direction. -/
theorem w3cz_switch_z_arcST_iff_hk5 (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    (∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z}) ↔
    5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k := by
  constructor
  · rintro ⟨B, hj, -, -, -, hia, -⟩
    exact w3cz_hk5_of_conclusion D x M hε z₀ _ B hj hia
  · intro hk5
    exact w3cz_bigonData_smooth_arcST_switch_z_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀
      hy₀ hz₀ hk5

/-- (BIGON) the `arcTS` companion: `w3bi_bigonData_smooth_arcTS_switch_z` is equivalent to `hk5` on the component
of `cutStartT`. -/
theorem w3cz_switch_z_arcTS_iff_hk5 (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    (∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y}) ↔
    5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k := by
  constructor
  · rintro ⟨B, hj, -, -, -, hia, -⟩
    exact w3cz_hk5_of_conclusion D x M hε z₀ _ B hj hia
  · intro hk5
    exact w3cz_bigonData_smooth_arcTS_switch_z_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀
      hy₀ hz₀ hk5

/-- **Rule (3) — the corrected forms of `w3g_bigonData_smooth_arcST/TS` needed by the (6) realiser when the
SWITCHED crossing is `z`.**  The frozen `w3g_*` put the bigon on `(D^x).switch y₀` with `y = {sS D x, g}` on
the OVER strand at `x`; the consumer (`esc_MoveData.rii_after_smoothing`, `esc_rii_after_smoothing_weak`) switches
the crossing at the double point of `x_eg`.  On the K3 side both alternating orientations occur
(`ExtremeLocal` is symmetric): if `e` is over `f` at `x_ef` then `sS = e`, `y = x_eg` and `w3g_*` apply; if `f`
is over `e` then `y = x_fg`, `z = x_eg` and the bigon must be read on `(D^x).switch z₀` — the same statement
with the switch moved (`same_over` holds after switching EITHER of `y, z`, by `hover`; no other field sees the
over data).  Stated here (open), consumed by the realisation of `w3bi_bigon_pair`. -/
theorem w3bi_bigonData_smooth_arcST_switch_z (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- (W3C assembler) STATEMENT RESTATED (W3C_ASSEMBLY_REPORT.md §2): the Wave-3b form is false on a kink for unit G's
  -- reason (the shadow does not see the switch; W3C_BIGON_REPORT.md §3); unit BIGON's proved corrected form.
  exact w3cz_bigonData_smooth_arcST_switch_z_of_not_kink D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover
    y₀ z₀ hy₀ hz₀ hkink

/-- the `arcTS` companion with the switch at `z₀` (see `w3bi_bigonData_smooth_arcST_switch_z`). -/
theorem w3bi_bigonData_smooth_arcTS_switch_z (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- (W3C assembler) STATEMENT RESTATED as for `arcST` (W3C_ASSEMBLY_REPORT.md §2): unit BIGON's proved corrected form.
  exact w3cz_bigonData_smooth_arcTS_switch_z_of_not_kink D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover
    y₀ z₀ hy₀ hz₀ hkink


/-- **The site data of one `j = 2` bigon site (the inputs of `w3g_bigonData_smooth_arcST/TS`, D4 + D5)** at a
crossing `x` of `D` with the two other triangle crossings at the double points `py, pz`: the remote strand `g`,
the crossings `y = {sS, g}` (on the over strand at `x`) and `z = {tS, g}`, their parameters relative to `x`
in one of the two coherent orientations (D4: `arcST` or `arcTS`), the clearance of the triangle disc, the
over data `hover` (D5), and which of `y, z` sits at `py` (the switched crossing of the consumer). -/
def w3bi_SiteData (D : Diagram) (x : D.Γ.Crossing) (py pz : Plane) : Prop :=
  ∃ (g : D.Γ.Strand) (_hgs : g ≠ sS D x) (_hgt : g ≠ tS D x) (y z : D.Γ.Crossing) (_hyx : y ≠ x) (_hzx : z ≠ x)
    (_hy : y.val = {sS D x, g}) (_hz : z.val = {tS D x, g}) (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val),
    ((D.crossingParam y hsy < τs D x ∧ τt D x < D.crossingParam z htz) ∨
      (τs D x < D.crossingParam y hsy ∧ D.crossingParam z htz < τt D x)) ∧
    (∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})) ∧
    (∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}) ∧
    (D.overStrand y = g ↔ D.overStrand z ≠ g) ∧
    ((D.Γ.crossingPoint y = py ∧ D.Γ.crossingPoint z = pz) ∨ (D.Γ.crossingPoint y = pz ∧ D.Γ.crossingPoint z = py))

/-- **One bigon from the site data, any `SpliceModel` (PROVED from `w3g_*` and the `switch_z` forms by name)**:
the smoothing crossings `y₀, z₀` over `y, z` (`liftCrossing`, `origCrossing_liftCrossing`), the consumer's `y_H`
at `py` is `y₀` or `z₀` (`crossingPoint_origCrossing` + generic injectivity), then the four cases
(orientation × switched crossing).  (W3C assembler) carries unit G's two non-kink conditions `hkST`, `hkTS`
(`⟨s.1, s.2 − 1⟩ ≠ ⟨t.1, t.2 + 1⟩`, `⟨t.1, t.2 − 1⟩ ≠ ⟨s.1, s.2 + 1⟩`), which the four restated sub-leaves need;
`clear_vertex` of the site data is no longer consumed.  Body = unit BIGON's `w3cz_bigon_of_site_model_of_not_kink`. -/
theorem w3bi_bigon_of_site_model (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε) (py pz : Plane) (hsite : w3bi_SiteData D x py pz)
    (hkST : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩)
    (hkTS : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩)
    (y_H : (toDiagram D x M hε).Γ.Crossing) (hyH : (toDiagram D x M hε).Γ.crossingPoint y_H = py) :
    ∃ z_H : (toDiagram D x M hε).Γ.Crossing, (toDiagram D x M hε).Γ.crossingPoint z_H = pz ∧
      ∃ B : BigonData ((toDiagram D x M hε).switch y_H), (B.y = y_H ∧ B.z = z_H) ∨ (B.y = z_H ∧ B.z = y_H) := by
  obtain ⟨g, hgs, hgt, y, z, hyx, hzx, hy, hz, hsy, htz, hor, clear, -, hover, hpts⟩ := hsite
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, origCrossing D x M hε y₀ = y := ⟨_, origCrossing_liftCrossing D x M hε y hyx⟩
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, origCrossing D x M hε z₀ = z := ⟨_, origCrossing_liftCrossing D x M hε z hzx⟩
  have hpy₀ : (toDiagram D x M hε).Γ.crossingPoint y₀ = D.Γ.crossingPoint y :=
    (crossingPoint_origCrossing D x M hε y₀).trans (by rw [hy₀])
  have hpz₀ : (toDiagram D x M hε).Γ.crossingPoint z₀ = D.Γ.crossingPoint z :=
    (crossingPoint_origCrossing D x M hε z₀).trans (by rw [hz₀])
  rcases hpts with ⟨hpy, hpz⟩ | ⟨hpy, hpz⟩
  · -- `y` at `py`: the switched crossing is `y₀`
    have hyH₀ : y₀ = y_H :=
      (toDiagram D x M hε).generic.crossingPoint_injective (hpy₀.trans (hpy.trans hyH.symm))
    subst hyH₀
    refine ⟨z₀, hpz₀.trans hpz, ?_⟩
    rcases hor with ⟨hys, hzt⟩ | ⟨hys, hzt⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3g_bigonData_smooth_arcST D x M hε g hgs hgt y z hy hz hsy htz hys hzt
        clear hover y₀ z₀ hy₀ hz₀ hkST
      exact ⟨B, Or.inl ⟨hBy, hBz⟩⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3g_bigonData_smooth_arcTS D x M hε g hgs hgt y z hy hz hsy htz hys hzt
        clear hover y₀ z₀ hy₀ hz₀ hkTS
      exact ⟨B, Or.inr ⟨hBy, hBz⟩⟩
  · -- `z` at `py`: the switched crossing is `z₀` (the corrected `switch_z` forms)
    have hyH₀ : z₀ = y_H :=
      (toDiagram D x M hε).generic.crossingPoint_injective (hpz₀.trans (hpz.trans hyH.symm))
    subst hyH₀
    refine ⟨y₀, hpy₀.trans hpy, ?_⟩
    rcases hor with ⟨hys, hzt⟩ | ⟨hys, hzt⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3bi_bigonData_smooth_arcST_switch_z D x M hε g hgs hgt y z hy hz hsy htz
        hys hzt clear hover y₀ z₀ hy₀ hz₀ hkST
      exact ⟨B, Or.inr ⟨hBy, hBz⟩⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3bi_bigonData_smooth_arcTS_switch_z D x M hε g hgs hgt y z hy hz hsy htz
        hys hzt clear hover y₀ z₀ hy₀ hz₀ hkTS
      exact ⟨B, Or.inl ⟨hBy, hBz⟩⟩

/-- the same on the library smoothing `smoothDiagram D x (eps D x) (eps_small D x)` (`unfold; split_ifs`).
(W3C assembler) the non-kink conditions are needed only in the self case `(sS D x).1 = (tS D x).1` (in the mixed case
they hold by `w3bg_not_kink_of_ne_comp`); body = unit BIGON's `w3cz_bigon_of_site_of_not_kink`. -/
theorem w3bi_bigon_of_site (D : Diagram) (x : D.Γ.Crossing) (py pz : Plane) (hsite : w3bi_SiteData D x py pz)
    (hk : (sS D x).1 = (tS D x).1 →
      (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ ∧
      (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩)
    (y_H : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.Crossing)
    (hyH : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.crossingPoint y_H = py) :
    ∃ z_H : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.Crossing,
      (smoothDiagram D x (eps D x) (eps_small D x)).Γ.crossingPoint z_H = pz ∧
      ∃ B : BigonData ((smoothDiagram D x (eps D x) (eps_small D x)).switch y_H),
        (B.y = y_H ∧ B.z = z_H) ∨ (B.y = z_H ∧ B.z = y_H) := by
  revert y_H hyH
  unfold smoothDiagram
  by_cases h : (sS D x).1 = (tS D x).1
  · rw [dif_pos h]
    exact w3bi_bigon_of_site_model D x (selfModel D x (eps D x) h) (eps_small D x) py pz hsite (hk h).1 (hk h).2
  · rw [dif_neg h]
    exact w3bi_bigon_of_site_model D x (mixedModel D x (eps D x) h) (eps_small D x) py pz hsite
      (w3bg_not_kink_of_ne_comp D x h).1 (w3bg_not_kink_of_ne_comp D x h).2

/-! (W3C assembler) unit BIGON's consumer variants `w3cz_bigon_of_site_model_of_not_kink` /
`w3cz_bigon_of_site_of_not_kink` were merged INTO `w3bi_bigon_of_site_model` / `w3bi_bigon_of_site` above
(same statements, same bodies) and are not repeated here. -/
/-- **BLACK BOX β1′ (the site data at the 177 configuration, both sides)** — what remains of β1 after the
reduction: at every configuration, `w3bi_SiteData` for the two lifts at `x_H, x_L` with `py, pz` the double points
of `x_eg, x_fg` (and their transports).  Contents: `g` the third lift strand, `y, z` the lift crossings at the double
points (`esc_lift_crossing`), `hy/hz` from the over data at `x`, `clear`/`clear_vertex` from
`G11_cfg_clear_frontier/vertex`, `hover` from the sign table (D5), the orientation from the strand orders (D4). -/
def w3bi_site_data : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∀ (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
        (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing),
        (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H = crossingPoint (xPair hef) →
        (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
          crossingPoint (xPair ((hs _).mp hef)) →
        w3bi_SiteData (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H (crossingPoint (xPair heg)) (crossingPoint (xPair hfg)) ∧
        w3bi_SiteData (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L
          (crossingPoint (xPair ((hs _).mp heg))) (crossingPoint (xPair ((hs _).mp hfg)))

/-! ### Unit SITE (`w3cs_`, W3C): β1′ `w3bi_site_data` PROVED — D4 as a determinant identity, D5 from the
positive over-strand convention, the lift wiring through `G11_cfg_*` / `gu2_x*_eq` / `G11_carrierSign`.
Report: `W3C_SITE_REPORT.md`. -/

/-! ### SITE (unit `w3cs_`): the site data from an alternating triangle on a positive diagram -/

theorem w3cs_det_lin (α β : ℝ) (u v w : Plane) : det (α • u - β • v) w = α * det u w - β * det v w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

theorem w3cs_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

/-- the crossing parameter depends only on the strand -/
theorem w3cs_crossingParam_congr (D : Diagram) (x : D.Γ.Crossing) {s s' : D.Γ.Strand} (h : s = s')
    (hs : s ∈ x.val) (hs' : s' ∈ x.val) : D.crossingParam x hs = D.crossingParam x hs' := by
  subst h; rfl

/-- two crossings on one strand differ by a multiple of the strand direction -/
theorem w3cs_sub_eq (D : Diagram) (x y : D.Γ.Crossing) {s : D.Γ.Strand} (hsx : s ∈ x.val) (hsy : s ∈ y.val) :
    D.Γ.crossingPoint y - D.Γ.crossingPoint x = (D.crossingParam y hsy - D.crossingParam x hsx) • D.Γ.dir s := by
  rw [(D.crossingParam_spec y hsy).2.2, (D.crossingParam_spec x hsx).2.2]
  unfold edgePoint
  show _ = (D.crossingParam y hsy - D.crossingParam x hsx) • edge (D.Γ.comp s.1).P s.2
  rw [sub_smul]
  abel

/-- the over strand of the positive diagram at a crossing `{s, t}` is `s` iff `det (dir s) (dir t) > 0` -/
theorem w3cs_pos_overStrand_eq_iff (Γ : Shadow) (hΓ : Γ.Generic) (y : Γ.Crossing) (s t : Γ.Strand)
    (hs : s ∈ y.val) (ht : t ∈ y.val) (hst : s ≠ t) :
    (Γ.positiveDiagram hΓ).overStrand y = s ↔ 0 < det (Γ.dir s) (Γ.dir t) := by
  have key : ∀ (o : Γ.Strand) (ho : o ∈ y.val), 0 < det (Γ.dir o) (Γ.dir (Γ.other y ho)) →
      (o = s ↔ 0 < det (Γ.dir s) (Γ.dir t)) := by
    intro o ho hpos
    rcases (Γ.mem_iff_eq_or_other y hs o).mp ho with rfl | h
    · have ht' : Γ.other y ho = t := (Γ.eq_other_of_mem_of_ne y ho ht hst.symm).symm
      rw [ht'] at hpos
      exact iff_of_true rfl hpos
    · have hot : o = t := by
        rw [h]; exact (Γ.eq_other_of_mem_of_ne y hs ht hst.symm).symm
      subst hot
      have hs' : Γ.other y ho = s := (Γ.eq_other_of_mem_of_ne y ho hs hst).symm
      rw [hs', det_swap] at hpos
      exact iff_of_false hst.symm (by linarith)
  exact key _ ((Γ.positiveDiagram hΓ).over_mem y) (Γ.positiveDiagram_det_pos hΓ y)

/-- **D4 core**: `α·det(a,c) = β·det(b,c)` with `det(a,c)`, `det(b,c)` of opposite signs and `α ≠ 0` forces
`α, β` to have opposite signs. -/
theorem w3cs_opposite_signs {α β dac dbc : ℝ} (h : α * dac = β * dbc) (hα : α ≠ 0)
    (hac : dac ≠ 0) (hbc : dbc ≠ 0) (hsign : SignType.sign dac = -SignType.sign dbc) :
    (α < 0 ∧ 0 < β) ∨ (0 < α ∧ β < 0) := by
  rcases lt_or_gt_of_ne hac with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    simp only [sign_pos, sign_neg, h1, h2] at hsign
  · exact absurd hsign (by decide)
  · rcases lt_or_gt_of_ne hα with h3 | h3
    · exact Or.inl ⟨h3, by nlinarith⟩
    · exact Or.inr ⟨h3, by nlinarith⟩
  · rcases lt_or_gt_of_ne hα with h3 | h3
    · exact Or.inl ⟨h3, by nlinarith⟩
    · exact Or.inr ⟨h3, by nlinarith⟩
  · exact absurd hsign (by decide)

theorem w3cs_det_smul_self (γ : ℝ) (u : Plane) : det (γ • u) u = 0 := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **The site data from an alternating triangle on the positive diagram of a generic shadow** (D4 + D5):
`x = {a, b}`, `y = {a, c}`, `z = {b, c}` with `sign det(a,b), det(a,c), det(b,c)` alternating, the closed
triangle clear of the other strands and of all vertices.  D4 is the identity
`(τ_y^a − τ_x^a)·det(a,c) = (τ_z^b − τ_x^b)·det(b,c)` (`y − x ∥ a`, `z − x ∥ b`, `y − z ∥ c`), D5 the
positive over-strand convention read on the two determinants. -/
theorem w3cs_siteData_of_triangle (Γ : Shadow) (hΓ : Γ.Generic) (x y z : Γ.Crossing) (a b c : Γ.Strand)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hx : x.val = {a, b}) (hy : y.val = {a, c}) (hz : z.val = {b, c})
    (halt : IsAlternating (SignType.sign (det (Γ.dir a) (Γ.dir b))) (SignType.sign (det (Γ.dir a) (Γ.dir c)))
      (SignType.sign (det (Γ.dir b) (Γ.dir c))))
    (hclear : ∀ u : Γ.Strand, u ≠ a → u ≠ b → u ≠ c →
      Disjoint (Γ.seg u) (convexHull ℝ {Γ.crossingPoint x, Γ.crossingPoint y, Γ.crossingPoint z}))
    (hvert : ∀ (i : Fin Γ.c) (l : ZMod (Γ.comp i).k),
      (Γ.comp i).P l ∉ convexHull ℝ {Γ.crossingPoint x, Γ.crossingPoint y, Γ.crossingPoint z}) :
    w3bi_SiteData (Γ.positiveDiagram hΓ) x (Γ.crossingPoint y) (Γ.crossingPoint z) := by
  have hxa : a ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have hxb : b ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hya : a ∈ y.val := by rw [hy]; exact Finset.mem_insert_self _ _
  have hyc : c ∈ y.val := by rw [hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hzb : b ∈ z.val := by rw [hz]; exact Finset.mem_insert_self _ _
  have hzc : c ∈ z.val := by rw [hz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hdac : det (Γ.dir a) (Γ.dir c) ≠ 0 := by
    obtain ⟨hna, hmeet⟩ := Γ.crossing_pair_spec y hya hyc hac
    exact hΓ.transverse a c hna hmeet
  have hdbc : det (Γ.dir b) (Γ.dir c) ≠ 0 := by
    obtain ⟨hna, hmeet⟩ := Γ.crossing_pair_spec z hzb hzc hbc
    exact hΓ.transverse b c hna hmeet
  have hsign : SignType.sign (det (Γ.dir a) (Γ.dir c)) = -SignType.sign (det (Γ.dir b) (Γ.dir c)) := by
    rw [halt.2, halt.1]
  have hyx : y ≠ x := by
    intro h
    have hb' : b ∈ ({a, c} : Finset Γ.Strand) := by rw [← hy, h]; exact hxb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with h' | h'
    · exact hab h'.symm
    · exact hbc h'
  have hzx : z ≠ x := by
    intro h
    have ha' : a ∈ ({b, c} : Finset Γ.Strand) := by rw [← hz, h]; exact hxa
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
    rcases ha' with h' | h'
    · exact hab h'
    · exact hac h'
  -- D4
  have hyx_eq : Γ.crossingPoint y - Γ.crossingPoint x =
      ((Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa) • Γ.dir a := w3cs_sub_eq (Γ.positiveDiagram hΓ) x y hxa hya
  have hzx_eq : Γ.crossingPoint z - Γ.crossingPoint x =
      ((Γ.positiveDiagram hΓ).crossingParam z hzb - (Γ.positiveDiagram hΓ).crossingParam x hxb) • Γ.dir b := w3cs_sub_eq (Γ.positiveDiagram hΓ) x z hxb hzb
  have hyz_eq : Γ.crossingPoint y - Γ.crossingPoint z =
      ((Γ.positiveDiagram hΓ).crossingParam y hyc - (Γ.positiveDiagram hΓ).crossingParam z hzc) • Γ.dir c := w3cs_sub_eq (Γ.positiveDiagram hΓ) z y hzc hyc
  have hkey : ((Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa) * det (Γ.dir a) (Γ.dir c) =
      ((Γ.positiveDiagram hΓ).crossingParam z hzb - (Γ.positiveDiagram hΓ).crossingParam x hxb) * det (Γ.dir b) (Γ.dir c) := by
    have h1 : ((Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa) • Γ.dir a -
        ((Γ.positiveDiagram hΓ).crossingParam z hzb - (Γ.positiveDiagram hΓ).crossingParam x hxb) • Γ.dir b =
        ((Γ.positiveDiagram hΓ).crossingParam y hyc - (Γ.positiveDiagram hΓ).crossingParam z hzc) • Γ.dir c := by
      rw [← hyx_eq, ← hzx_eq, ← hyz_eq]; abel
    have h2 : det (((Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa) • Γ.dir a -
        ((Γ.positiveDiagram hΓ).crossingParam z hzb - (Γ.positiveDiagram hΓ).crossingParam x hxb) • Γ.dir b) (Γ.dir c) =
        det (((Γ.positiveDiagram hΓ).crossingParam y hyc - (Γ.positiveDiagram hΓ).crossingParam z hzc) • Γ.dir c) (Γ.dir c) := by
      rw [h1]
    rw [w3cs_det_lin, w3cs_det_smul_self] at h2
    linarith
  have hα0 : (Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa ≠ 0 := by
    intro h0
    apply hyx
    apply hΓ.crossingPoint_injective
    have : Γ.crossingPoint y - Γ.crossingPoint x = 0 := by rw [hyx_eq, h0, zero_smul]
    exact sub_eq_zero.mp this
  have hD4 := w3cs_opposite_signs hkey hα0 hdac hdbc hsign
  -- D5
  have hoy : (Γ.positiveDiagram hΓ).overStrand y = c ↔ 0 < det (Γ.dir c) (Γ.dir a) :=
    w3cs_pos_overStrand_eq_iff Γ hΓ y c a hyc hya hac.symm
  have hoz : (Γ.positiveDiagram hΓ).overStrand z = c ↔ 0 < det (Γ.dir c) (Γ.dir b) :=
    w3cs_pos_overStrand_eq_iff Γ hΓ z c b hzc hzb hbc.symm
  have hover : (Γ.positiveDiagram hΓ).overStrand y = c ↔ (Γ.positiveDiagram hΓ).overStrand z ≠ c := by
    rcases lt_or_gt_of_ne hdac with h1 | h1 <;> rcases lt_or_gt_of_ne hdbc with h2 | h2 <;>
      simp only [sign_pos, sign_neg, h1, h2] at hsign
    · exact absurd hsign (by decide)
    · refine iff_of_true (hoy.mpr (by rw [det_swap]; linarith)) (fun h => ?_)
      have := hoz.mp h
      rw [det_swap] at this
      linarith
    · refine iff_of_false (fun h => ?_) (fun h => h (hoz.mpr (by rw [det_swap]; linarith)))
      have := hoy.mp h
      rw [det_swap] at this
      linarith
    · exact absurd hsign (by decide)
  have hset : ({Γ.crossingPoint x, Γ.crossingPoint z, Γ.crossingPoint y} : Set Plane) =
      {Γ.crossingPoint x, Γ.crossingPoint y, Γ.crossingPoint z} := by
    rw [Set.pair_comm]
  have hover' : (Γ.positiveDiagram hΓ).overStrand z = c ↔ (Γ.positiveDiagram hΓ).overStrand y ≠ c := by
    constructor
    · intro hq hp; exact hover.mp hp hq
    · intro hnp; by_contra hnq; exact hnp (hover.mpr hnq)
  -- the case split on the over strand at `x`
  have hsx : (Γ.positiveDiagram hΓ).overStrand x ∈ ({a, b} : Finset Γ.Strand) := by
    rw [← hx]; exact (Γ.positiveDiagram hΓ).over_mem x
  unfold w3bi_SiteData
  rcases Finset.mem_insert.mp hsx with hsa | hsb'
  · -- `sS = a`, `tS = b`: `y` at `py`
    have htb : (Γ.positiveDiagram hΓ).underStrand x = b :=
      ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x hxb (by rw [hsa]; exact hab.symm)).symm
    have hsy' : sS (Γ.positiveDiagram hΓ) x ∈ y.val := by show (Γ.positiveDiagram hΓ).overStrand x ∈ y.val; rw [hsa]; exact hya
    have htz' : tS (Γ.positiveDiagram hΓ) x ∈ z.val := by show (Γ.positiveDiagram hΓ).underStrand x ∈ z.val; rw [htb]; exact hzb
    refine ⟨c, ?_, ?_, y, z, hyx, hzx, ?_, ?_, hsy', htz', ?_, ?_, hvert, hover, Or.inl ⟨rfl, rfl⟩⟩
    · show c ≠ (Γ.positiveDiagram hΓ).overStrand x; rw [hsa]; exact hac.symm
    · show c ≠ (Γ.positiveDiagram hΓ).underStrand x; rw [htb]; exact hbc.symm
    · show y.val = {(Γ.positiveDiagram hΓ).overStrand x, c}; rw [hsa]; exact hy
    · show z.val = {(Γ.positiveDiagram hΓ).underStrand x, c}; rw [htb]; exact hz
    · have e1 : (Γ.positiveDiagram hΓ).crossingParam y hsy' = (Γ.positiveDiagram hΓ).crossingParam y hya := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) y hsa _ _
      have e2 : τs (Γ.positiveDiagram hΓ) x = (Γ.positiveDiagram hΓ).crossingParam x hxa := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) x hsa _ _
      have e3 : (Γ.positiveDiagram hΓ).crossingParam z htz' = (Γ.positiveDiagram hΓ).crossingParam z hzb := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) z htb _ _
      have e4 : τt (Γ.positiveDiagram hΓ) x = (Γ.positiveDiagram hΓ).crossingParam x hxb := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) x htb _ _
      rw [e1, e2, e3, e4]
      rcases hD4 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    · intro u hu1 hu2 hu3
      apply hclear u _ _ hu3
      · intro h; apply hu1; rw [h]; exact hsa.symm
      · intro h; apply hu2; rw [h]; exact htb.symm
  · -- `sS = b`, `tS = a`: the roles of `y, z` swap, `y` at `pz`
    have hsb : (Γ.positiveDiagram hΓ).overStrand x = b := Finset.mem_singleton.mp hsb'
    have hta : (Γ.positiveDiagram hΓ).underStrand x = a :=
      ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x hxa (by rw [hsb]; exact hab)).symm
    have hsz' : sS (Γ.positiveDiagram hΓ) x ∈ z.val := by show (Γ.positiveDiagram hΓ).overStrand x ∈ z.val; rw [hsb]; exact hzb
    have hty' : tS (Γ.positiveDiagram hΓ) x ∈ y.val := by show (Γ.positiveDiagram hΓ).underStrand x ∈ y.val; rw [hta]; exact hya
    refine ⟨c, ?_, ?_, z, y, hzx, hyx, ?_, ?_, hsz', hty', ?_, ?_, ?_, hover', Or.inr ⟨rfl, rfl⟩⟩
    · show c ≠ (Γ.positiveDiagram hΓ).overStrand x; rw [hsb]; exact hbc.symm
    · show c ≠ (Γ.positiveDiagram hΓ).underStrand x; rw [hta]; exact hac.symm
    · show z.val = {(Γ.positiveDiagram hΓ).overStrand x, c}; rw [hsb]; exact hz
    · show y.val = {(Γ.positiveDiagram hΓ).underStrand x, c}; rw [hta]; exact hy
    · have e1 : (Γ.positiveDiagram hΓ).crossingParam z hsz' = (Γ.positiveDiagram hΓ).crossingParam z hzb := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) z hsb _ _
      have e2 : τs (Γ.positiveDiagram hΓ) x = (Γ.positiveDiagram hΓ).crossingParam x hxb := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) x hsb _ _
      have e3 : (Γ.positiveDiagram hΓ).crossingParam y hty' = (Γ.positiveDiagram hΓ).crossingParam y hya := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) y hta _ _
      have e4 : τt (Γ.positiveDiagram hΓ) x = (Γ.positiveDiagram hΓ).crossingParam x hxa := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) x hta _ _
      rw [e1, e2, e3, e4]
      rcases hD4 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    · intro u hu1 hu2 hu3
      show Disjoint (Γ.seg u) (convexHull ℝ {Γ.crossingPoint x, Γ.crossingPoint z, Γ.crossingPoint y})
      rw [hset]
      apply hclear u _ _ hu3
      · intro h; apply hu2; rw [h]; exact hta.symm
      · intro h; apply hu1; rw [h]; exact hsb.symm
    · show ∀ (i : Fin Γ.c) (l : ZMod (Γ.comp i).k),
        (Γ.comp i).P l ∉ convexHull ℝ {Γ.crossingPoint x, Γ.crossingPoint z, Γ.crossingPoint y}
      rw [hset]
      exact hvert


/-! ### SITE (unit `w3cs_`): the site data at the lift of the distinguished carrier -/

section W3CS_Lift

open SM.GeoCarrier SM.Carrier

/-- `ExactTriangleVisitOrders` is symmetric in the two polygons (copy of `s174_exact_symm`, not imported here). -/
theorem w3cs_exact_symm {P P' : LabelledTuple n} {e f g : ZMod n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ExactTriangleVisitOrders P' P e f g (fun s => (hs s).symm) := by
  intro v w he
  have h1 := hX ((visitTransport hs).symm w) ((visitTransport hs).symm v) he.symm
  have h2 := hX ((visitTransport hs).symm v) ((visitTransport hs).symm w) he
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1 h2
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · have hu' : ((visitTransport hs).symm w).1.val ∪ ((visitTransport hs).symm v).1.val =
        {e, f, g} := by
      rw [Finset.union_comm]; exact hu
    exact (h1.1 hu').symm
  · exact (h2.2 hu).symm

/-- **β1′ at the lift level (PROVED)**: the site data of the positive lift of the distinguished carrier at the
lift crossing over `x_ef`, with `py, pz` the double points of `x_eg, x_fg`.  The three lift crossings are
`(singleCrossingEquiv).symm (xPair hmp / hmq / hpq)` of the configuration crossings `G11_cfg_hmp/hmq/hpq`
(double points `gu2_x*_eq`), the strands `⟨0, m⟩ ⟨0, p⟩ ⟨0, q⟩`, the alternating triple through
`G11_carrierSign`, the closed triangle through `G11_cfg_clear_frontier/vertex`; then
`w3cs_siteData_of_triangle`. -/
theorem w3cs_site_data_lift (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (halt : IsAlternating (crossingSign P e f) (crossingSign P e g) (crossingSign P f g))
    (x_H : (geoPositiveLift hn hG hT q).Γ.Crossing)
    (hxH : (geoPositiveLift hn hG hT q).Γ.crossingPoint x_H = crossingPoint (xPair hcef)) :
    w3bi_SiteData (geoPositiveLift hn hG hT q) x_H (crossingPoint (xPair hceg)) (crossingPoint (xPair hcfg)) := by
  have hmp := G11_cfg_hmp hn hG hT q hcef htri
  have hmq := G11_cfg_hmq hn hG hs hT q hcef hceg htri hX
  have hpq := G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX
  have hgen : (Shadow.single (geoCarrierPolyComp hn hG hT q)).Generic := geoCarrierShadow_generic hn hG hT q
  have cp : ∀ c : Crossing (geoCornerPolygon hG.cg T q),
      (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
        ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm c) = crossingPoint c := by
    intro c
    rw [Shadow.single_crossingPoint _ hgen, Equiv.apply_symm_apply]
  have hxm : (Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp) = x_H := by
    apply hgen.crossingPoint_injective
    rw [cp, gu2_xmp_eq hn hG hT q hcef htri hmp]
    exact hxH.symm
  have hym : (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
      ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq)) =
      crossingPoint (xPair hceg) := by
    rw [cp, gu2_xmq_eq hn hG hT q hcef hceg htri hmq]
  have hzm : (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
      ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq)) =
      crossingPoint (xPair hcfg) := by
    rw [cp, gu2_xpq_eq hn hG hT q hcef hceg hcfg htri hpq]
  have hval : ∀ (i j : ZMod (geoCornerCount hG.cg T q)) (h : IsCrossing (geoCornerPolygon hG.cg T q) {i, j}),
      ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair h)).val =
        {(⟨0, i⟩ : (Shadow.single (geoCarrierPolyComp hn hG hT q)).Strand), ⟨0, j⟩} := by
    intro i j h
    show ({i, j} : Finset (ZMod (geoCornerCount hG.cg T q))).map _ = _
    rw [Finset.map_insert, Finset.map_singleton]
    rfl
  have hne : ∀ (i j : ZMod (geoCornerCount hG.cg T q)), i ≠ j →
      (⟨0, i⟩ : (Shadow.single (geoCarrierPolyComp hn hG hT q)).Strand) ≠ ⟨0, j⟩ := by
    intro i j hij h
    exact hij (congrArg (Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)) h)
  have hsgn : IsAlternating
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_pE hn hG hT q hcef htri))
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri))
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri)) := by
    have h1 : crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_pE hn hG hT q hcef htri) =
        crossingSign P e f :=
      G11_carrierSign hn hG hT q (G11_vef hcef) (G11_vfe hcef) _ _
    have h2 : crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri) =
        crossingSign P e g :=
      G11_carrierSign hn hG hT q (G11_vef hcef) (G11_vge hceg) _ _
    have h3 : crossingSign (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri) =
        crossingSign P f g :=
      G11_carrierSign hn hG hT q (G11_vfe hcef) (G11_vge hceg) _ _
    rw [h1, h2, h3]
    exact halt
  have hclear_closed : ∀ h : ZMod (geoCornerCount hG.cg T q), h ≠ G11_mE hn hG hT q hcef htri →
      h ≠ G11_pE hn hG hT q hcef htri → h ≠ G11_qE hn hG hT q hceg htri →
      ∀ y ∈ edgeSegment (geoCornerPolygon hG.cg T q) h, y ∉ G11_triangle (geoCornerPolygon hG.cg T q) hmp hmq hpq := by
    intro h hm hp hq y hy hyΔ
    obtain ⟨w, hw, hwF⟩ := G11_preconnected_meets_frontier
      (G11_edgeSegment_isPreconnected (geoCornerPolygon hG.cg T q) h) ⟨y, hy, hyΔ⟩
      ⟨geoCornerPolygon hG.cg T q h, ⟨0, le_rfl, zero_le_one, (edgePoint_zero _ h).symm⟩,
        G11_cfg_clear_vertex hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX h⟩
    exact G11_cfg_clear_frontier hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX h hm hp hq w hw hwF
  have htri_eq : convexHull ℝ
      {(Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
          ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp)),
        (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
          ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq)),
        (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
          ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq))} =
      G11_triangle (geoCornerPolygon hG.cg T q) hmp hmq hpq := by
    unfold G11_triangle
    rw [cp, cp, cp]
  have hclear : ∀ u : (Shadow.single (geoCarrierPolyComp hn hG hT q)).Strand,
      u ≠ ⟨0, G11_mE hn hG hT q hcef htri⟩ → u ≠ ⟨0, G11_pE hn hG hT q hcef htri⟩ →
      u ≠ ⟨0, G11_qE hn hG hT q hceg htri⟩ →
      Disjoint ((Shadow.single (geoCarrierPolyComp hn hG hT q)).seg u) (convexHull ℝ
        {(Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp)),
          (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq)),
          (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq))}) := by
    intro u hu1 hu2 hu3
    rw [htri_eq, Set.disjoint_left]
    intro y hy hyΔ
    refine hclear_closed u.2 ?_ ?_ ?_ y hy hyΔ
    · intro h
      exact hu1 ((Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)).injective
        (show Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) u =
          Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) ⟨0, _⟩ from h))
    · intro h
      exact hu2 ((Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)).injective
        (show Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) u =
          Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) ⟨0, _⟩ from h))
    · intro h
      exact hu3 ((Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)).injective
        (show Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) u =
          Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) ⟨0, _⟩ from h))
  have hvert : ∀ (i : Fin (Shadow.single (geoCarrierPolyComp hn hG hT q)).c)
      (l : ZMod ((Shadow.single (geoCarrierPolyComp hn hG hT q)).comp i).k),
      ((Shadow.single (geoCarrierPolyComp hn hG hT q)).comp i).P l ∉ convexHull ℝ
        {(Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp)),
          (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq)),
          (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq))} := by
    intro i l
    rw [htri_eq]
    exact G11_cfg_clear_vertex hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX l
  have main := w3cs_siteData_of_triangle (Shadow.single (geoCarrierPolyComp hn hG hT q)) hgen
    ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp))
    ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq))
    ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq))
    ⟨0, G11_mE hn hG hT q hcef htri⟩ ⟨0, G11_pE hn hG hT q hcef htri⟩ ⟨0, G11_qE hn hG hT q hceg htri⟩
    (hne _ _ (P1.ne_of_isCrossing_pair hmp)) (hne _ _ (P1.ne_of_isCrossing_pair hmq))
    (hne _ _ (P1.ne_of_isCrossing_pair hpq))
    (hval _ _ hmp) (hval _ _ hmq) (hval _ _ hpq) hsgn hclear hvert
  rw [hym, hzm] at main
  subst hxm
  exact main

/-- the transported triangle crossings are carried by the transported carrier (`hcarr`) -/
theorem w3cs_triangle_transport {P P' : LabelledTuple n} (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
    {T : Finset (Crossing P)} {T' : Finset (Crossing P')} (q : GeoComponent hP T) (q' : GeoComponent hP' T')
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (hcarr : geoCarrierCrossings hP' T' q' =
      (geoCarrierCrossings hP T q).map (crossingTransport hs).toEmbedding)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hP T q) :
    triangleCrossings P' e f g ⊆ geoCarrierCrossings hP' T' q' := by
  intro c hc
  rw [hcarr, Finset.mem_map_equiv]
  apply htri
  rw [P1.mem_triangleCrossings_iff hef heg hfg]
  rw [P1.mem_triangleCrossings_iff ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)] at hc
  rcases hc with rfl | rfl | rfl
  · left; rfl
  · right; left; rfl
  · right; right; rfl

end W3CS_Lift

/-- **β1′ PROVED**: the site glue of `w3bi_wall_data_of` (the contact carrier owns the triangle, the transported
carrier is the contact carrier of the other side, `hcarr`), the alternating triple from `CompleteLocal`
(`w3e_alt_of_completeLocal`) transported by `AV_EventRadius.sign_eq`, then `w3cs_site_data_lift` on each side. -/
theorem w3cs__w3bi_site_data_data_proof : w3bi_site_data := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL
  have hef₀ : e ≠ f := P1.ne_of_isCrossing_pair hef
  have heg₀ : e ≠ g := P1.ne_of_isCrossing_pair heg
  have hfg₀ : f ≠ g := P1.ne_of_isCrossing_pair hfg
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hcarr := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀'' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hcarr, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have hq₀eq : q₀' = GT_carrierEquiv W q₀ :=
    esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀' hq₀''
  subst hq₀eq
  have hX := hL.gauss_words t t' ht ht' hop hs
  have halt : IsAlternating (crossingSign (E.curve t) e f) (crossingSign (E.curve t) e g)
      (crossingSign (E.curve t) f g) :=
    w3e_alt_of_completeLocal hGT t ht hef heg hfg hK
  have halt' : IsAlternating (crossingSign (E.curve t') e f) (crossingSign (E.curve t') e g)
      (crossingSign (E.curve t') f g) := by
    rw [hR.sign_eq t t' ht ht' e f hef, hR.sign_eq t t' ht ht' e g heg, hR.sign_eq t t' ht ht' f g hfg]
    exact halt
  have htri' := w3cs_triangle_transport _ _ hs q₀ (GT_carrierEquiv W q₀) hef heg hfg hcarr hTq₀
  unfold CV.carrierDiagram at x_H x_L hxH hxL ⊢
  exact ⟨w3cs_site_data_lift hn _ hs _ q₀ hef₀ heg₀ hfg₀ hef heg hfg hX hTq₀ halt x_H hxH,
    w3cs_site_data_lift hn _ (fun s => (hs s).symm) _ (GT_carrierEquiv W q₀) hef₀ heg₀ hfg₀
      ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) (w3cs_exact_symm hs hX) htri' halt' x_L hxL⟩


/-- the black box asserted (open body) -/
theorem w3bi_site_data_data : w3bi_site_data := by
  exact w3cs__w3bi_site_data_data_proof

/-! ### Unit SITE — the NON-KINK condition of unit G at the 177 site (stated; the site-level black box is OPEN,
W3C_SITE_REPORT.md §4) -/

/-- the two non-kink conditions of `w3bg_bigonData_smooth_arcST_of_not_kink` / `_arcTS_of_not_kink` at `x`: the
strand before `s` is not the strand after `t`, and the strand before `t` is not the strand after `s` (on the
one-component lift: the two strands of `x` are not at cyclic distance `2`, so the oriented smoothing of `x` does not
split off a `4`-gon). -/
def w3cs_NotKink (D : Diagram) (x : D.Γ.Crossing) : Prop :=
  (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ ∧
  (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩

/-- the `hkink` of `w3bg_bigonData_smooth_arcST_of_not_kink` / `w3bg_hk5_arcST_of_not_kink` -/
theorem w3cs_not_kink_arcST (D : Diagram) (x : D.Γ.Crossing) (h : w3cs_NotKink D x) :
    (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ := h.1

/-- the `hkink` of `w3bg_bigonData_smooth_arcTS_of_not_kink` / `w3bg_hk5_arcTS_of_not_kink` -/
theorem w3cs_not_kink_arcTS (D : Diagram) (x : D.Γ.Crossing) (h : w3cs_NotKink D x) :
    (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩ := h.2

section W3BI_Lift
variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
  (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
  (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')

/-- **The wall bijection of the two UNSWITCHED lifts (D6, the reusable core of β2)** — the `Λ` of the
accepted `G11_recordIsoData` (:10852–10920) on its own, `halt`-free: `Λ` lifts `visitTransport` through
`CV.liftVisitEquiv` (`hcarr`), carries twins (`liftVisit_twin`, `visitTransport_visitTwin`), the over
bits (a positive lift's bit is the divide sign, carried by `hdet`), the signs (all `+1`,
`geoPositiveLift_sign`), and the cyclic order TWISTED by any `σ` lifting `G11_σP` (`visitBetween_iff_key`,
`G11_twisted_key_lt`, `GT_cyc_congr_of_lt`).  What β2 (`w3bi_wall_data`) still needs on top: the six local
lift visits `a₁ b₁ | a₂ c₁ | b₂ c₂` over `G11_vef, vfe | veg, vge | vfg, vgf` (`G11_mem_tri_*` + `htri`),
`σ := swap a₁ a₂ * (swap b₁ b₂ * swap c₁ c₂)` lifting `G11_σP` (`Function.Injective.swap_apply` with
`liftVisit_injective`), and the adjacency of the local pairs on each strand (`LocalizationData.adjacent`
lifted to `nextVisit`). -/
theorem w3bi_wallEquiv (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding) :
    ∃ Λ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit,
      (∀ v, CV.liftVisit hn hG' hT' q' (Λ v) = visitTransport hs (CV.liftVisit hn hG hT q v)) ∧
      (∀ v, Λ ((geoPositiveLift hn hG hT q).twin v) = (geoPositiveLift hn hG' hT' q').twin (Λ v)) ∧
      (∀ v, (geoPositiveLift hn hG' hT' q').overBit (Λ v) = (geoPositiveLift hn hG hT q).overBit v) ∧
      (∀ v, (geoPositiveLift hn hG' hT' q').sign (Λ v).1 = (geoPositiveLift hn hG hT q).sign v.1) ∧
      (∀ σ : Equiv.Perm (geoPositiveLift hn hG hT q).Γ.Visit,
        (∀ v, CV.liftVisit hn hG hT q (σ v) = G11_σP hcef hceg hcfg (CV.liftVisit hn hG hT q v)) →
        ∀ u v w, (geoPositiveLift hn hG' hT' q').VisitBetween (Λ u) (Λ v) (Λ w) ↔
          (geoPositiveLift hn hG hT q).VisitBetween (σ u) (σ v) (σ w)) := by
  let ψ : {w : Visit P // w.1 ∈ geoCarrierCrossings hG.cg T q} ≃
      {w : Visit P' // w.1 ∈ geoCarrierCrossings hG'.cg T' q'} :=
    (visitTransport hs).subtypeEquiv fun w => by
      rw [hcarr, visitTransport_crossing, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  let Λ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit :=
    (CV.liftVisitEquiv hn hG hT q).trans (ψ.trans (CV.liftVisitEquiv hn hG' hT' q').symm)
  have hΛ : ∀ v, CV.liftVisit hn hG' hT' q' (Λ v) = visitTransport hs (CV.liftVisit hn hG hT q v) := by
    intro v
    show CV.liftVisit hn hG' hT' q'
      ((CV.liftVisitEquiv hn hG' hT' q').symm (ψ (CV.liftVisitEquiv hn hG hT q v))) = _
    rw [CV.liftVisit_symm]
    rfl
  have hΛtw : ∀ v, Λ ((geoPositiveLift hn hG hT q).twin v) = (geoPositiveLift hn hG' hT' q').twin (Λ v) := by
    intro v
    apply CV.liftVisit_injective hn hG' hT' q'
    rw [hΛ, CV.liftVisit_twin, CV.liftVisit_twin, hΛ, visitTransport_visitTwin]
  refine ⟨Λ, hΛ, hΛtw, ?_, ?_, ?_⟩
  · intro v
    rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΛ,
      visitTransport_edge, ← visitTransport_visitTwin, visitTransport_edge]
    exact (hdet _ _ (by rw [← visit_crossing_val_eq_pair]; exact (CV.liftVisit hn hG hT q _).1.property)).symm
  · intro v
    rw [geoPositiveLift_sign, geoPositiveLift_sign]
  · intro σ hσ u v w
    rw [CV.visitBetween_iff_key, hΛ, hΛ, hΛ, CV.visitBetween_iff_key, hσ, hσ, hσ]
    exact (GT_cyc_congr_of_lt
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)).symm


/-- **β2a (adjacency lifted to the carrier lift; PROVED below, `w3bi_adjacent_lift_proof`)**: two visits of the lift whose parents are
adjacent on the traversal circle of `P` (`AdjacentVisits`, R-LOC (2): no visit of `P` strictly between, in
one of the two directions) are consecutive on the one-component lift (`nextVisit`; the lift's visits are a
subset of `P`'s, ordered by the same key: `visitBetween_iff_key`, `traversalBetween_iff_cycBetween`,
`nextVisit_no_between` + the uniqueness of the cyclic successor). -/
def w3bi_adjacent_lift : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
    (v w : (geoPositiveLift hn hG hT q).Γ.Visit),
    AdjacentVisits hG.cg (CV.liftVisit hn hG hT q v) (CV.liftVisit hn hG hT q w) →
    (geoPositiveLift hn hG hT q).nextVisit v = w ∨ (geoPositiveLift hn hG hT q).nextVisit w = v

/-- three distinct reals are cyclically ordered one way or the other -/
theorem w3bi_cycBetween_or {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cycBetween a b c ∨ cycBetween a c b := by
  unfold cycBetween
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3
  all_goals first
    | (left; first | exact Or.inl ⟨h1, h2⟩ | exact Or.inr (Or.inl ⟨h2, h3⟩) | exact Or.inr (Or.inr ⟨h3, h1⟩))
    | (right; first | exact Or.inl ⟨h3, h2⟩ | exact Or.inr (Or.inl ⟨h2, h1⟩) | exact Or.inr (Or.inr ⟨h1, h3⟩))

/-- **β2a PROVED**: on the one-component lift every two visits share the component
(`compOf_eq_of_single`), `VisitBetween` is the cyclic order of the parents' traversal keys
(`visitBetween_iff_key`), and the cyclic successor is the unique visit with nothing strictly between
(`not_visitBetween_nextVisit`, `nextVisit_ne_self`, `visitCoord_injOn`, the trichotomy above). -/
theorem w3bi_adjacent_lift_proof : w3bi_adjacent_lift := by
  intro n _ hn P hG T hT q v w hadj
  obtain ⟨hne, hcase⟩ := hadj
  have hvw : v ≠ w := fun h => hne (by rw [h])
  have hc1 : ∀ a b : (geoPositiveLift hn hG hT q).Γ.Visit,
      (geoPositiveLift hn hG hT q).compOf a = (geoPositiveLift hn hG hT q).compOf b :=
    CV.compOf_eq_of_single rfl
  have hkey : ∀ a b c : (geoPositiveLift hn hG hT q).Γ.Visit,
      (geoPositiveLift hn hG hT q).VisitBetween a b c ↔
        traversalBetween (geometricVisitPosition hG.cg (CV.liftVisit hn hG hT q a))
          (geometricVisitPosition hG.cg (CV.liftVisit hn hG hT q b))
          (geometricVisitPosition hG.cg (CV.liftVisit hn hG hT q c)) := fun a b c => by
    rw [CV.visitBetween_iff_key]
    exact Iff.rfl
  have tri : ∀ a b c : (geoPositiveLift hn hG hT q).Γ.Visit, a ≠ b → b ≠ c → a ≠ c →
      (geoPositiveLift hn hG hT q).VisitBetween a b c ∨ (geoPositiveLift hn hG hT q).VisitBetween a c b := by
    intro a b c hab hbc hac
    exact w3bi_cycBetween_or (fun h => hab ((geoPositiveLift hn hG hT q).visitCoord_injOn (hc1 a b) h))
      (fun h => hbc ((geoPositiveLift hn hG hT q).visitCoord_injOn (hc1 b c) h))
      (fun h => hac ((geoPositiveLift hn hG hT q).visitCoord_injOn (hc1 a c) h))
  rcases hcase with h | h
  · left
    by_contra hne'
    have hn1 : (geoPositiveLift hn hG hT q).nextVisit v ≠ v :=
      (geoPositiveLift hn hG hT q).nextVisit_ne_self v w (hc1 w v) hvw.symm
    rcases tri v w _ hvw (Ne.symm hne') hn1.symm with hb | hb
    · exact (geoPositiveLift hn hG hT q).not_visitBetween_nextVisit v w (hc1 w v) hb
    · exact h _ ((hkey _ _ _).mp hb)
  · right
    by_contra hne'
    have hn1 : (geoPositiveLift hn hG hT q).nextVisit w ≠ w :=
      (geoPositiveLift hn hG hT q).nextVisit_ne_self w v (hc1 v w) hvw
    rcases tri w v _ hvw.symm (Ne.symm hne') hn1.symm with hb | hb
    · exact (geoPositiveLift hn hG hT q).not_visitBetween_nextVisit w v (hc1 v w) hb
    · exact h _ ((hkey _ _ _).mp hb)

/-- β2a, PROVED (kept under its black-box name for the consumers below) -/
theorem w3bi_adjacent_lift_data : w3bi_adjacent_lift := w3bi_adjacent_lift_proof

/-- **β2 at the lift level (PROVED from `w3bi_wallEquiv` and β2a)**: the six local lift visits
`a₁ b₁ | a₂ c₁ | b₂ c₂` over `G11_vef, vfe | veg, vge | vfg, vgf`, `σ = swap a₁ a₂ * (swap b₁ b₂ * swap c₁ c₂)`
lifting `G11_σP` (`Function.Injective.swap_apply`), twins (`liftVisit_twin`, `gu2_visitTwin_*`), the double
points (`liftVisit_fst`, `crossingPoint_liftCrossing`), the transported crossings (generic injectivity on
the empty-side lift), adjacency through β2a. -/
theorem w3bi_wall_data_lift (hadjl : w3bi_adjacent_lift) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hadjE : AdjacentVisits hG.cg (G11_vef hcef) (G11_veg hceg))
    (hadjF : AdjacentVisits hG.cg (G11_vfe hcef) (G11_vfg hcfg))
    (hadjG : AdjacentVisits hG.cg (G11_vge hceg) (G11_vgf hcfg))
    (x_H : (geoPositiveLift hn hG hT q).Γ.Crossing) (x_L : (geoPositiveLift hn hG' hT' q').Γ.Crossing)
    (hxH : (geoPositiveLift hn hG hT q).Γ.crossingPoint x_H = crossingPoint (xPair hcef))
    (hxL : (geoPositiveLift hn hG' hT' q').Γ.crossingPoint x_L = crossingPoint (crossingTransport hs (xPair hcef))) :
    ∃ (y_H z_H : (geoPositiveLift hn hG hT q).Γ.Crossing) (y_L z_L : (geoPositiveLift hn hG' hT' q').Γ.Crossing)
      (Ψ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : (geoPositiveLift hn hG hT q).Γ.Visit),
      (geoPositiveLift hn hG hT q).Γ.crossingPoint y_H = crossingPoint (xPair hceg) ∧
      (geoPositiveLift hn hG hT q).Γ.crossingPoint z_H = crossingPoint (xPair hcfg) ∧
      (geoPositiveLift hn hG' hT' q').Γ.crossingPoint y_L = crossingPoint (crossingTransport hs (xPair hceg)) ∧
      (geoPositiveLift hn hG' hT' q').Γ.crossingPoint z_L = crossingPoint (crossingTransport hs (xPair hcfg)) ∧
      a₁.1 = x_H ∧ b₁ = (geoPositiveLift hn hG hT q).twin a₁ ∧ a₂.1 = y_H ∧ c₁ = (geoPositiveLift hn hG hT q).twin a₂ ∧ b₂.1 = z_H ∧ c₂ = (geoPositiveLift hn hG hT q).twin b₂ ∧
      ((geoPositiveLift hn hG hT q).nextVisit a₁ = a₂ ∨ (geoPositiveLift hn hG hT q).nextVisit a₂ = a₁) ∧
      ((geoPositiveLift hn hG hT q).nextVisit b₁ = b₂ ∨ (geoPositiveLift hn hG hT q).nextVisit b₂ = b₁) ∧
      ((geoPositiveLift hn hG hT q).nextVisit c₁ = c₂ ∨ (geoPositiveLift hn hG hT q).nextVisit c₂ = c₁) ∧
      (∀ v, Ψ ((geoPositiveLift hn hG hT q).twin v) = (geoPositiveLift hn hG' hT' q').twin (Ψ v)) ∧
      (∀ v, (geoPositiveLift hn hG' hT' q').overBit (Ψ v) = (geoPositiveLift hn hG hT q).overBit v) ∧
      (∀ v, (geoPositiveLift hn hG' hT' q').sign (Ψ v).1 = (geoPositiveLift hn hG hT q).sign v.1) ∧
      (∀ u v w, (geoPositiveLift hn hG' hT' q').VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
        (geoPositiveLift hn hG hT q).VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u) ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)) ∧
      (Ψ a₁).1 = x_L ∧ (Ψ a₂).1 = y_L ∧ (Ψ b₂).1 = z_L := by
  obtain ⟨Λ, hΛ, hΛtw, hΛbit, hΛsgn, hΛcyc⟩ :=
    w3bi_wallEquiv hn hG hG' hs hT hT' q q' hef heg hfg hcef hceg hcfg hX hdet hcarr
  -- the six local lift visits
  let a₁ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vef hcef, G11_mem_tri_ef hG q hcef htri⟩
  let b₁ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vfe hcef, G11_mem_tri_ef hG q hcef htri⟩
  let a₂ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_veg hceg, G11_mem_tri_eg hG q hceg htri⟩
  let c₁ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vge hceg, G11_mem_tri_eg hG q hceg htri⟩
  let b₂ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vfg hcfg, G11_mem_tri_fg hG q hcfg htri⟩
  let c₂ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vgf hcfg, G11_mem_tri_fg hG q hcfg htri⟩
  have la₁ : CV.liftVisit hn hG hT q a₁ = G11_vef hcef := CV.liftVisit_symm hn hG hT q _
  have lb₁ : CV.liftVisit hn hG hT q b₁ = G11_vfe hcef := CV.liftVisit_symm hn hG hT q _
  have la₂ : CV.liftVisit hn hG hT q a₂ = G11_veg hceg := CV.liftVisit_symm hn hG hT q _
  have lc₁ : CV.liftVisit hn hG hT q c₁ = G11_vge hceg := CV.liftVisit_symm hn hG hT q _
  have lb₂ : CV.liftVisit hn hG hT q b₂ = G11_vfg hcfg := CV.liftVisit_symm hn hG hT q _
  have lc₂ : CV.liftVisit hn hG hT q c₂ = G11_vgf hcfg := CV.liftVisit_symm hn hG hT q _
  have hinj := CV.liftVisit_injective hn hG hT q
  -- double points of the lift crossings through the parents
  have hpt : ∀ v : (geoPositiveLift hn hG hT q).Γ.Visit,
      (geoPositiveLift hn hG hT q).Γ.crossingPoint v.1 = crossingPoint (CV.liftVisit hn hG hT q v).1 := fun v => by
    rw [CV.liftVisit_fst, CV.crossingPoint_liftCrossing]
  have hpt' : ∀ v : (geoPositiveLift hn hG' hT' q').Γ.Visit,
      (geoPositiveLift hn hG' hT' q').Γ.crossingPoint v.1 = crossingPoint (CV.liftVisit hn hG' hT' q' v).1 := fun v => by
    rw [CV.liftVisit_fst, CV.crossingPoint_liftCrossing]
  -- the twisting permutation lifts `σ_P`
  have hσ : ∀ v, CV.liftVisit hn hG hT q ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) =
      G11_σP hcef hceg hcfg (CV.liftVisit hn hG hT q v) := by
    intro v
    simp only [G11_σP, Equiv.Perm.mul_apply]
    rw [← la₁, ← la₂, ← lb₁, ← lb₂, ← lc₁, ← lc₂, hinj.swap_apply, hinj.swap_apply, hinj.swap_apply]
  refine ⟨a₂.1, b₂.1, (Λ a₂).1, (Λ b₂).1, Λ, a₁, a₂, b₁, b₂, c₁, c₂, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_,
    ?_, ?_, ?_, hΛtw, hΛbit, hΛsgn, hΛcyc _ hσ, ?_, rfl, rfl⟩
  · rw [hpt, la₂]; rfl
  · rw [hpt, lb₂]; rfl
  · rw [hpt', hΛ, la₂]; rfl
  · rw [hpt', hΛ, lb₂]; rfl
  · exact (geoPositiveLift hn hG hT q).generic.crossingPoint_injective (by rw [hpt, la₁, hxH]; rfl)
  · exact hinj (by rw [CV.liftVisit_twin, la₁, lb₁, gu2_visitTwin_vef])
  · exact hinj (by rw [CV.liftVisit_twin, la₂, lc₁, gu2_visitTwin_veg])
  · exact hinj (by rw [CV.liftVisit_twin, lb₂, lc₂, gu2_visitTwin_vfg])
  · exact hadjl hn hG hT q a₁ a₂ (by rw [la₁, la₂]; exact hadjE)
  · exact hadjl hn hG hT q b₁ b₂ (by rw [lb₁, lb₂]; exact hadjF)
  · exact hadjl hn hG hT q c₁ c₂ (by rw [lc₁, lc₂]; exact hadjG)
  · exact (geoPositiveLift hn hG' hT' q').generic.crossingPoint_injective (by rw [hpt', hΛ, la₁, hxL]; rfl)

end W3BI_Lift

/-- **BLACK BOX β2 (G11 Unit F at the 177 site, D6)**: the wall bijection `Ψ` between the two UNSWITCHED
lifts with twins, bits, signs and the cyclic order twisted by the three transpositions on the six local
visits (the `G11_core_statement` shape, `G11_twisted_key_lt` + `visitTransport`), the local visits
`a₁ b₁ | a₂ c₁ | b₂ c₂` of `x, y, z` (`x = x_ef`, `y = x_eg`, `z = x_fg`) with adjacency on each strand
(R-LOC (2), `LocalizationData.adjacent`), the transported crossings — exactly the inputs of `w3h_hrec`. -/
def w3bi_wall_data : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∀ (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
        (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing),
        (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H = crossingPoint (xPair hef) →
        (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
          crossingPoint (xPair ((hs _).mp hef)) →
        ∃ (y_H z_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
          (y_L z_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing)
          (Ψ : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Visit ≃ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Visit)
          (a₁ a₂ b₁ b₂ c₁ c₂ : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Visit),
          (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint y_H = crossingPoint (xPair heg) ∧
          (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint z_H = crossingPoint (xPair hfg) ∧
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint y_L = crossingPoint (xPair ((hs _).mp heg)) ∧
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint z_L = crossingPoint (xPair ((hs _).mp hfg)) ∧
          a₁.1 = x_H ∧ b₁ = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).twin a₁ ∧
          a₂.1 = y_H ∧ c₁ = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).twin a₂ ∧
          b₂.1 = z_H ∧ c₂ = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).twin b₂ ∧
          ((CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit a₁ = a₂ ∨
            (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit a₂ = a₁) ∧
          ((CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit b₁ = b₂ ∨
            (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit b₂ = b₁) ∧
          ((CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit c₁ = c₂ ∨
            (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit c₂ = c₁) ∧
          (∀ v, Ψ ((CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).twin v) = (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').twin (Ψ v)) ∧
          (∀ v, (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').overBit (Ψ v) = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).overBit v) ∧
          (∀ v, (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').sign (Ψ v).1 = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).sign v.1) ∧
          (∀ u v w, (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
            (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u) ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)) ∧
          (Ψ a₁).1 = x_L ∧ (Ψ a₂).1 = y_L ∧ (Ψ b₂).1 = z_L

/-- **β2 at the site (PROVED from β2a)**: `q₀'` is the wall image of `q₀` (`esc_contact_unique`), `hcarr`
from `GT_empty_wall`, `htri` from `esc_contact_owns`, `hX` from `hL.gauss_words`, `hdet` from `hR.sign_eq`,
the three adjacencies from `hL.adjacent` (R-LOC (2)); then `w3bi_wall_data_lift` after
`unfold CV.carrierDiagram`. -/
theorem w3bi_wall_data_of (hadjl : w3bi_adjacent_lift) : w3bi_wall_data := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL
  have hef₀ : e ≠ f := P1.ne_of_isCrossing_pair hef
  have heg₀ : e ≠ g := P1.ne_of_isCrossing_pair heg
  have hfg₀ : f ≠ g := P1.ne_of_isCrossing_pair hfg
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hcarr := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀'' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hcarr, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have hq₀eq : q₀' = GT_carrierEquiv W q₀ :=
    esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀' hq₀''
  subst hq₀eq
  have hX := hL.gauss_words t t' ht ht' hop hs
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  obtain ⟨hadjE, hadjF, hadjG⟩ := hL.adjacent t ht hef heg hfg
  unfold CV.carrierDiagram at x_H x_L hxH hxL ⊢
  exact w3bi_wall_data_lift hn _ _ hs _ _ q₀ _ hadjl hef₀ heg₀ hfg₀ hef heg hfg hX hdet hcarr hTq₀ hadjE hadjF
    hadjG x_H x_L hxH hxL

/-- β2 with β2a asserted -/
theorem w3bi_wall_data_data : w3bi_wall_data :=
  w3bi_wall_data_of w3bi_adjacent_lift_data

/-! ### Assembler connections (prefix `w3ba_`, W3B_ASSEMBLY_REPORT.md): unit H's bridge and `w3h_hrec` in the
orientation-general form REAL's `w3bi_hrec_general` needs.  `BigonData.keep` is symmetric in `B.y, B.z`, so the
text of `w3bh_reduced_to_smooth` proves the disjunctive form with one `and_comm`; `w3ba_hrec_gen` is the text of
`w3h_hrec` calling it (derived from W3B_H.lean by `assemble_W3B_connect.py`). -/

/-- `w3bh_reduced_to_smooth` with `{B.y, B.z} = {y₀, z₀}` in either order (assembler copy). -/
theorem w3ba_reduced_to_smooth_gen (D : Diagram) (x y z : D.Γ.Crossing)
    (a₁ a₂ b₂ c₁ c₂ : D.Γ.Visit) (ha₁ : a₁.1 = x) (ha₂ : a₂.1 = y) (hc₁ : c₁ = D.twin a₂)
    (hb₂ : b₂.1 = z) (hc₂ : c₂ = D.twin b₂)
    {ε : ℝ} (hε : SmallEps D x ε)
    (y₀ z₀ : (smoothDiagram D x ε hε).Γ.Crossing)
    (hy₀ : (smoothDiagram D x ε hε).Γ.crossingPoint y₀ = D.Γ.crossingPoint y)
    (hz₀ : (smoothDiagram D x ε hε).Γ.crossingPoint z₀ = D.Γ.crossingPoint z)
    (B : BigonData ((smoothDiagram D x ε hε).switch y₀))
    (hB : (B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧ B.z = y₀)) :
    Nonempty (RecordIso B.reducedRecord
      ((D.record.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})) := by
  subst hc₁ hc₂
  -- the occurrence-defined retained set on `E = smoothDiagram D x ε hε`
  let X₁ : Set (smoothDiagram D x ε hε).record.Crossing := {c | ∀ w ∈ c.1, w.1 ≠ y₀ ∧ w.1 ≠ z₀}
  have hX₁ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit,
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔ (u.1 ≠ y₀ ∧ u.1 ≠ z₀) := by
    intro u
    rw [w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ∧
      (((smoothDiagram D x ε hε).twin u).1 ≠ y₀ ∧ ((smoothDiagram D x ε hε).twin u).1 ≠ z₀) ↔ _
    rw [Diagram.twin_fst, and_self]
  -- Step A/B: `B.reducedRecord ≅ (E.record.switch v₀).restrictCrossings X₁`
  obtain ⟨ι₂⟩ := CB.restrictCrossings_iso_of_recordIso
    ((smoothDiagram D x ε hε).switchRecordIso y₀ ((smoothDiagram D x ε hε).overVisit y₀) rfl) B.keep X₁ (by
    intro u
    show (((smoothDiagram D x ε hε).switch y₀).record.crossingOf u ≠
        ((smoothDiagram D x ε hε).switch y₀).record.crossingOf
          (((smoothDiagram D x ε hε).switch y₀).overVisit B.y) ∧
      ((smoothDiagram D x ε hε).switch y₀).record.crossingOf u ≠
        ((smoothDiagram D x ε hε).switch y₀).record.crossingOf
          (((smoothDiagram D x ε hε).switch y₀).overVisit B.z)) ↔
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁
    rw [Ne, Ne, w3bh_record_crossingOf_eq_iff, w3bh_record_crossingOf_eq_iff, Diagram.overVisit_fst,
      Diagram.overVisit_fst]
    rcases hB with ⟨hBy, hBz⟩ | ⟨hBy, hBz⟩
    · rw [hBy, hBz]; exact (hX₁ u).symm
    · rw [hBy, hBz]; exact and_comm.trans (hX₁ u).symm)
  -- Step C: the switch at the deleted `y₀` is invisible
  obtain ⟨ι₃⟩ := w3h_restrict_switch_deleted (smoothDiagram D x ε hε).record X₁
    ((smoothDiagram D x ε hε).overVisit y₀) (fun h => ((hX₁ _).mp h).1 rfl)
  -- Step D: the smoothing bridge
  obtain ⟨ι₄, hι₄⟩ := w3h_smooth_record_occ D x ε hε
  have hpt : ∀ (u : (smoothDiagram D x ε hε).Γ.Visit) (w : D.Γ.Crossing)
      (w₀ : (smoothDiagram D x ε hε).Γ.Crossing)
      (hw₀ : (smoothDiagram D x ε hε).Γ.crossingPoint w₀ = D.Γ.crossingPoint w),
      (ι₄.Φ u).1.1 = w ↔ u.1 = w₀ := by
    intro u w w₀ hw₀
    constructor
    · intro h
      apply (smoothDiagram D x ε hε).generic.crossingPoint_injective
      rw [← hι₄ u, h, hw₀]
    · intro h
      apply D.generic.crossingPoint_injective
      rw [hι₄ u, h, hw₀]
  let X₂ : Set (D.record.smooth (D.overVisit x)).Crossing :=
    {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂}
  have hP : ∀ w : D.Γ.Visit, (w ≠ a₂ ∧ w ≠ D.twin a₂ ∧ w ≠ b₂ ∧ w ≠ D.twin b₂) ↔
      (w.1 ≠ y ∧ w.1 ≠ z) := by
    intro w
    rw [← and_assoc, w3bh_ne_ne_twin_iff, w3bh_ne_ne_twin_iff, ha₂, hb₂]
  have hX₂ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit, (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔
      (D.record.smooth (D.overVisit x)).crossingOf (ι₄.Φ u) ∈ X₂ := by
    intro u
    rw [hX₁, w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ↔
      ((ι₄.Φ u).1 ≠ a₂ ∧ (ι₄.Φ u).1 ≠ D.twin a₂ ∧ (ι₄.Φ u).1 ≠ b₂ ∧ (ι₄.Φ u).1 ≠ D.twin b₂) ∧
      (D.twin (ι₄.Φ u).1 ≠ a₂ ∧ D.twin (ι₄.Φ u).1 ≠ D.twin a₂ ∧ D.twin (ι₄.Φ u).1 ≠ b₂ ∧
        D.twin (ι₄.Φ u).1 ≠ D.twin b₂)
    rw [hP, hP, Diagram.twin_fst, and_self]
    exact Iff.and (not_congr (hpt u y y₀ hy₀).symm) (not_congr (hpt u z z₀ hz₀).symm)
  obtain ⟨ι₅⟩ := CB.restrictCrossings_iso_of_recordIso ι₄ X₁ X₂ hX₂
  -- Step E: land on `a₁`
  rcases D.eq_or_eq_twin (D.overVisit x) a₁ ha₁ with h | h
  · subst h
    exact ⟨ι₂.trans (ι₃.trans ι₅)⟩
  · subst h
    obtain ⟨ι₆⟩ := CB.restrictCrossings_iso_of_recordIso (D.record.smoothPairIso (D.overVisit x)).symm X₂
      {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂} (by
        intro u
        rw [w3bh_crossingOf_mem_setOf, w3bh_crossingOf_mem_setOf]
        exact Iff.rfl)
    exact ⟨ι₂.trans (ι₃.trans (ι₅.trans ι₆))⟩

/-- `w3h_hrec` with either orientation on either side (assembler copy of unit H's proof). -/
theorem w3ba_hrec_gen (D_H D_L : Diagram) (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1)
    (x_H y_H z_H : D_H.Γ.Crossing) (x_L y_L z_L : D_L.Γ.Crossing)
    (Ψ : D_H.Γ.Visit ≃ D_L.Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : D_H.Γ.Visit)
    (ha₁ : a₁.1 = x_H) (hb₁ : b₁ = D_H.twin a₁) (ha₂ : a₂.1 = y_H) (hc₁ : c₁ = D_H.twin a₂)
    (hb₂ : b₂.1 = z_H) (hc₂ : c₂ = D_H.twin b₂)
    (hxy : x_H ≠ y_H) (hxz : x_H ≠ z_H) (hyz : y_H ≠ z_H)
    (hadj_e : D_H.nextVisit a₁ = a₂ ∨ D_H.nextVisit a₂ = a₁)
    (hadj_f : D_H.nextVisit b₁ = b₂ ∨ D_H.nextVisit b₂ = b₁)
    (hadj_g : D_H.nextVisit c₁ = c₂ ∨ D_H.nextVisit c₂ = c₁)
    (htw : ∀ v, Ψ (D_H.twin v) = D_L.twin (Ψ v)) (hbit : ∀ v, D_L.overBit (Ψ v) = D_H.overBit v)
    (hsgn : ∀ v, D_L.sign (Ψ v).1 = D_H.sign v.1)
    (hcyc : ∀ u v w, D_L.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      D_H.VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w))
    (hxL : (Ψ a₁).1 = x_L) (hyL : (Ψ a₂).1 = y_L) (hzL : (Ψ b₂).1 = z_L)
    {εH εL : ℝ} (hεH : SmallEps D_H x_H εH) (hεL : SmallEps D_L x_L εL)
    (yH0 zH0 : (smoothDiagram D_H x_H εH hεH).Γ.Crossing)
    (hyH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint yH0 = D_H.Γ.crossingPoint y_H)
    (hzH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint zH0 = D_H.Γ.crossingPoint z_H)
    (yL0 zL0 : (smoothDiagram D_L x_L εL hεL).Γ.Crossing)
    (hyL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint yL0 = D_L.Γ.crossingPoint y_L)
    (hzL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint zL0 = D_L.Γ.crossingPoint z_L)
    (B_H : BigonData ((smoothDiagram D_H x_H εH hεH).switch yH0))
    (hBH : (B_H.y = yH0 ∧ B_H.z = zH0) ∨ (B_H.y = zH0 ∧ B_H.z = yH0))
    (B_L : BigonData ((smoothDiagram D_L x_L εL hεL).switch yL0))
    (hBL : (B_L.y = yL0 ∧ B_L.z = zL0) ∨ (B_L.y = zL0 ∧ B_L.z = yL0)) :
    Nonempty (RecordIso B_H.reducedRecord B_L.reducedRecord) := by
  -- the six local occurrences and their crossings
  have hb₁x : b₁.1 = x_H := by rw [hb₁]; exact ha₁
  have hc₁y : c₁.1 = y_H := by rw [hc₁]; exact ha₂
  have hc₂z : c₂.1 = z_H := by rw [hc₂]; exact hb₂
  have hne : ∀ (u v : D_H.Γ.Visit), u.1 ≠ v.1 → u ≠ v :=
    fun u v h h' => h (congrArg (fun w : D_H.Γ.Visit => w.1) h')
  have h13 : a₁ ≠ b₁ := by rw [hb₁]; exact (D_H.twin_ne a₁).symm
  have h25 : a₂ ≠ c₁ := by rw [hc₁]; exact (D_H.twin_ne a₂).symm
  have h46 : b₂ ≠ c₂ := by rw [hc₂]; exact (D_H.twin_ne b₂).symm
  have h14 : a₁ ≠ b₂ := hne _ _ (by rw [ha₁, hb₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [ha₂, hb₁x]; exact hxy.symm)
  have h24 : a₂ ≠ b₂ := hne _ _ (by rw [ha₂, hb₂]; exact hyz)
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [ha₁, hc₁y]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [ha₁, hc₂z]; exact hxz)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [ha₂, hc₂z]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hb₁x, hc₁y]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hb₁x, hc₂z]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hb₂, hc₁y]; exact hyz.symm)
  have hσσ : ∀ v, (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) = v :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  -- the twisted successor clause from the twisted cyclic order (one component on both sides)
  have hsucc : ∀ v, Ψ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (D_H.nextVisit ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) =
      D_L.nextVisit (Ψ v) := by
    let Φ' : D_H.Γ.Visit ≃ D_L.Γ.Visit :=
      (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)).trans Ψ
    have hcomp : ∀ v w, D_L.compOf (Φ' v) = D_L.compOf (Φ' w) ↔ D_H.compOf v = D_H.compOf w :=
      fun v w => ⟨fun _ => w3bh_compOf_eq_of_one D_H hH v w, fun _ => w3bh_compOf_eq_of_one D_L hL _ _⟩
    have hbetw : ∀ v w u, D_H.compOf w = D_H.compOf v → D_H.compOf u = D_H.compOf v →
        (D_L.VisitBetween (Φ' v) (Φ' w) (Φ' u) ↔ D_H.VisitBetween v w u) := by
      intro v w u _ _
      have := hcyc ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
      rw [hσσ, hσσ, hσσ] at this
      exact this
    intro v
    have key := D_H.nextVisit_comm_of_visitBetween_iff Φ' hcomp hbetw
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
    simp only [Φ', Equiv.trans_apply, hσσ] at key
    exact key
  -- the crossings of `D_L`
  have hΨfst := w3bh_fst_eq_iff_of_twin Ψ htw
  have hxyL : x_L ≠ y_L := by
    rw [← hxL, ← hyL, Ne, hΨfst, ha₁, ha₂]; exact hxy
  have hxzL : x_L ≠ z_L := by
    rw [← hxL, ← hzL, Ne, hΨfst, ha₁, hb₂]; exact hxz
  have hyzL : y_L ≠ z_L := by
    rw [← hyL, ← hzL, Ne, hΨfst, ha₂, hb₂]; exact hyz
  -- the two bridges
  obtain ⟨ιH⟩ := w3ba_reduced_to_smooth_gen D_H x_H y_H z_H a₁ a₂ b₂ c₁ c₂ ha₁ ha₂ hc₁ hb₂ hc₂ hεH
    yH0 zH0 hyH0 hzH0 B_H hBH
  obtain ⟨ιL⟩ := w3ba_reduced_to_smooth_gen D_L x_L y_L z_L (Ψ a₁) (Ψ a₂) (Ψ b₂) (Ψ c₁) (Ψ c₂) hxL hyL
    (by rw [hc₁, htw]) hzL (by rw [hc₂, htw]) hεL yL0 zL0 hyL0 hzL0 B_L hBL
  -- the core
  have hcr : ∀ u v : D_H.Γ.Visit, u.1 ≠ v.1 → D_H.record.crossingOf u ≠ D_H.record.crossingOf v :=
    fun u v h h' => h ((w3bh_record_crossingOf_eq_iff D_H u v).mp h')
  obtain ⟨κ⟩ := w3h_record_core D_H.record D_L.record (D_H.record_componentCount.trans hH)
    (D_L.record_componentCount.trans hL) Ψ a₁ a₂ b₁ b₂ c₁ c₂ hb₁.symm hc₁.symm hc₂.symm
    (hcr _ _ (by rw [ha₁, ha₂]; exact hxy)) (hcr _ _ (by rw [ha₁, hb₂]; exact hxz))
    (hcr _ _ (by rw [ha₂, hb₂]; exact hyz)) hadj_e hadj_f hadj_g htw hbit hsgn hsucc
  exact ⟨ιH.trans (κ.trans ιL.symm)⟩

/-- **`w3h_hrec` in the form the (6) realiser needs (rule (3), corrected form)**: the frozen `w3h_hrec` fixes
`B.y = y₀` (the switched crossing) and `B.z = z₀` on BOTH sides, i.e. the `arcST` orientation on both sides
of the wall; the reduced record `B.reducedRecord = restrictCrossings keep` is symmetric in `B.y, B.z`, so the
same statement holds for either assignment on either side.  PROVED from `w3h_hrec` in the `ST/ST` case; the
three other orientation pairs are closed by the assembler's `w3ba_hrec_gen` (unit H's proof, `and_comm`). -/
theorem w3bi_hrec_general (D_H D_L : Diagram) (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1)
    (x_H y_H z_H : D_H.Γ.Crossing) (x_L y_L z_L : D_L.Γ.Crossing)
    (Ψ : D_H.Γ.Visit ≃ D_L.Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : D_H.Γ.Visit)
    (ha₁ : a₁.1 = x_H) (hb₁ : b₁ = D_H.twin a₁) (ha₂ : a₂.1 = y_H) (hc₁ : c₁ = D_H.twin a₂)
    (hb₂ : b₂.1 = z_H) (hc₂ : c₂ = D_H.twin b₂)
    (hxy : x_H ≠ y_H) (hxz : x_H ≠ z_H) (hyz : y_H ≠ z_H)
    (hadj_e : D_H.nextVisit a₁ = a₂ ∨ D_H.nextVisit a₂ = a₁)
    (hadj_f : D_H.nextVisit b₁ = b₂ ∨ D_H.nextVisit b₂ = b₁)
    (hadj_g : D_H.nextVisit c₁ = c₂ ∨ D_H.nextVisit c₂ = c₁)
    (htw : ∀ v, Ψ (D_H.twin v) = D_L.twin (Ψ v)) (hbit : ∀ v, D_L.overBit (Ψ v) = D_H.overBit v)
    (hsgn : ∀ v, D_L.sign (Ψ v).1 = D_H.sign v.1)
    (hcyc : ∀ u v w, D_L.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      D_H.VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w))
    (hxL : (Ψ a₁).1 = x_L) (hyL : (Ψ a₂).1 = y_L) (hzL : (Ψ b₂).1 = z_L)
    {εH εL : ℝ} (hεH : SmallEps D_H x_H εH) (hεL : SmallEps D_L x_L εL)
    (yH0 zH0 : (smoothDiagram D_H x_H εH hεH).Γ.Crossing)
    (hyH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint yH0 = D_H.Γ.crossingPoint y_H)
    (hzH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint zH0 = D_H.Γ.crossingPoint z_H)
    (yL0 zL0 : (smoothDiagram D_L x_L εL hεL).Γ.Crossing)
    (hyL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint yL0 = D_L.Γ.crossingPoint y_L)
    (hzL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint zL0 = D_L.Γ.crossingPoint z_L)
    (B_H : BigonData ((smoothDiagram D_H x_H εH hεH).switch yH0))
    (hBH : (B_H.y = yH0 ∧ B_H.z = zH0) ∨ (B_H.y = zH0 ∧ B_H.z = yH0))
    (B_L : BigonData ((smoothDiagram D_L x_L εL hεL).switch yL0))
    (hBL : (B_L.y = yL0 ∧ B_L.z = zL0) ∨ (B_L.y = zL0 ∧ B_L.z = yL0)) :
    Nonempty (RecordIso B_H.reducedRecord B_L.reducedRecord) := by
  rcases hBH with ⟨hBHy, hBHz⟩ | ⟨hBHy, hBHz⟩ <;> rcases hBL with ⟨hBLy, hBLz⟩ | ⟨hBLy, hBLz⟩
  · exact w3h_hrec D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz
      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0 B_H hBHy hBHz
      B_L hBLy hBLz
  · exact w3ba_hrec_gen D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz
      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0
      B_H (Or.inl ⟨hBHy, hBHz⟩) B_L (Or.inr ⟨hBLy, hBLz⟩)
  · exact w3ba_hrec_gen D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz
      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0
      B_H (Or.inr ⟨hBHy, hBHz⟩) B_L (Or.inl ⟨hBLy, hBLz⟩)
  · exact w3ba_hrec_gen D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz
      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0
      B_H (Or.inr ⟨hBHy, hBHz⟩) B_L (Or.inr ⟨hBLy, hBLz⟩)

/-! ### W3C unit SPLITB — `esc_FullSplitData.writhe` (17) and `.mixed` (ESC §4), the SPLITB half of the
carrier split of `Q ∪ T` on the empty side (the black box `w3bi_esc_outer_data`).

Both fields are PROVED (`w3cb_fields_of_splitGeometry`, `w3cb_fields_of_residue`) from a single geometric input
`w3cb_SplitResidue` (the black box towards unit SPLITA: `A, B, C` are the `Q ∪ T`-carriers of three triangle
visits at which the local turn is the common outer sign `s_o` (the sign table (1c)), pairwise distinct; the
carrier of every triangle visit is `A`, `B`, `C` or a carrier owning only triangle visits (the central `Z`); the
parity `2Λ` of the crossings between distinct outer gap strings, `Λ = lk(J)` of the KNOT unit; and the three
triangle crossings retained on the contact carrier — FREE at the event level, `w3cb_triangle_on_contact_at` via
`esc_contact_owns`).  Content:
* the retained-set ledger with three children (the analogue of row 176's `r176l_retained_decomp` /
  `r176l_card_retained`): `geoCarrierCrossings Q q₀ = ⋃ geoCarrierCrossings (Q ∪ T) {A, B, C} ⊔ mixedSet ⊔
  selectedPart`, the five parts pairwise disjoint (`w3cb_retained_decomp`, `w3cb_card_retained`); the selected
  part is exactly `T` (`w3cb_selectedPart_eq`), so with `groupedWrithe_eq_card_geoCarrierCrossings`
  `w = 3 + w_A + w_B + w_C + #mixedSet` (`w3cb_writhe_count`) and (17) once `#mixedSet = 2Λ`
  (`w3cb_writhe_field`);
* the mixed clause: the turn of a carrier's corner polygon at `k` is the sign `w3cb_turnAt` at its corner mark
  (`w3cb_turn_eq_turnAt`, via `geoCornerPolygon_edge_pred_smul` / `_smul`), which is unchanged when the support
  grows without selecting or deselecting the mark's crossing (`w3cb_turnAt_eq_of_iff`); hence every corner of
  the contact carrier is inherited by one of `A, B, C` with the same turn (`w3cb_inherit_turn`,
  `w3cb_inherit_of_markChildren`), and if `A, B, C` were all uniform their common local sign would make the
  parent uniform (`w3cb_uniform_of_cornerData`) — so a mixed contact carrier forces
  `wt(A) wt(B) wt(C) wt(Z) = 0` (`w3cb_mixed_field`);
* the children clauses (`w3cb_Children` / `w3cb_MarkChildren`: the marks of `A, B, C` are marks of `q₀`, and the
  non-triangle marks of `q₀` are marks of `A, B, C`) PROVED from the accepted one-insertion lemmas iterated three
  times (`w3cb_step_affected`, `w3cb_stage`, `w3cb_cover_three`, `w3cb_cover_triangle`: every mark of `q₀` lands on
  the `Q ∪ T`-carrier of one of the six triangle visits; `geoOwner_eq_of_subset` for the refinement), given only
  the residue's `central` clause (`w3cb_markChildren_of`, `w3cb_splitGeometry_of_residue`);
* `w3cb_fullSplitData_of`: `esc_FullSplitData` assembled from `w3cb_SplitGeometry` and SPLITA's six fields as
  hypotheses (in the exact field statements); `w3cb_central_no_piece`: SPLITA's `central_no_piece` follows from
  the residue's `central` clause, so `w3cb_fullSplitData_of_residue` needs only the remaining five fields;
  `w3cb_split_core` the event-level black box — the residue without `triangle_on_contact`, which is free there
  (`w3cb_split_core_data`, left open by this unit and since proved from the residue; `w3cb_split_geometry_data` is then a theorem).
Nothing frozen is touched; the leaf `w3bi_esc_outer_data` keeps its body (it also needs SPLITA's fields and
KNOT's two clauses).  Report: `W3C_SPLITB_REPORT.md`. -/
section W3CB_SPLITB

variable {P : LabelledTuple n} (hP : CrossingGeometry P)

structure w3cb_Children (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S')
    (A B C : GeoComponent hP Sf) : Prop where
  subA : ∀ m : Mark P, geoOwner hP Sf m = A → geoOwner hP S' m = q'
  subB : ∀ m : Mark P, geoOwner hP Sf m = B → geoOwner hP S' m = q'
  subC : ∀ m : Mark P, geoOwner hP Sf m = C → geoOwner hP S' m = q'
  neAB : A ≠ B
  neAC : A ≠ C
  neBC : B ≠ C
  cover : ∀ w : Visit P, w.1 ∉ Sf → geoOwner hP S' (Sum.inr w) = q' →
    geoOwner hP Sf (Sum.inr w) = A ∨ geoOwner hP Sf (Sum.inr w) = B ∨ geoOwner hP Sf (Sum.inr w) = C

open scoped Classical in
noncomputable def w3cb_mixedSet (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S') : Finset (Crossing P) :=
  (geoCarrierCrossings hP S' q').filter fun x => x ∉ Sf ∧
    ∃ v w : Visit P, v.1 = x ∧ w.1 = x ∧ geoOwner hP Sf (Sum.inr v) ≠ geoOwner hP Sf (Sum.inr w)

open scoped Classical in
noncomputable def w3cb_selectedPart (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S') : Finset (Crossing P) :=
  (geoCarrierCrossings hP S' q').filter fun x => x ∈ Sf

variable {S' Sf : Finset (Crossing P)} {q' : GeoComponent hP S'} {A B C : GeoComponent hP Sf}

theorem w3cb_retained_child_subset (hSS : S' ⊆ Sf) {r : GeoComponent hP Sf}
    (hsub : ∀ m : Mark P, geoOwner hP Sf m = r → geoOwner hP S' m = q') {x : Crossing P}
    (hx : x ∈ geoCarrierCrossings hP Sf r) : x ∈ geoCarrierCrossings hP S' q' ∧ x ∉ Sf := by
  rw [mem_geoCarrierCrossings] at hx ⊢
  exact ⟨⟨fun h => hx.1 (hSS h), fun v hv => hsub _ (hx.2 v hv)⟩, hx.1⟩

theorem w3cb_retained_decomp (hSS : S' ⊆ Sf) (hC : w3cb_Children hP S' Sf q' A B C) :
    geoCarrierCrossings hP S' q' =
      geoCarrierCrossings hP Sf A ∪ geoCarrierCrossings hP Sf B ∪ geoCarrierCrossings hP Sf C ∪
        w3cb_mixedSet hP S' Sf q' ∪ w3cb_selectedPart hP S' Sf q' := by
  classical
  ext x
  simp only [Finset.mem_union, w3cb_mixedSet, w3cb_selectedPart, Finset.mem_filter]
  constructor
  · intro hx
    by_cases hxSf : x ∈ Sf
    · exact Or.inr ⟨hx, hxSf⟩
    · have hx' := (mem_geoCarrierCrossings hP S' q' x).mp hx
      obtain ⟨i, -, -⟩ := crossing_visits_exist x
      set v₀ : Visit P := ⟨x, i⟩ with hv₀
      have hall : ∀ w : Visit P, w.1 = x → w = v₀ ∨ w = visitTwin v₀ := fun w hw =>
        visit_eq_or_twin v₀ w hw
      by_cases heq : geoOwner hP Sf (Sum.inr v₀) = geoOwner hP Sf (Sum.inr (visitTwin v₀))
      · have hown : ∀ w : Visit P, w.1 = x →
            geoOwner hP Sf (Sum.inr w) = geoOwner hP Sf (Sum.inr v₀) := by
          intro w hw
          rcases hall w hw with rfl | rfl
          · rfl
          · exact heq.symm
        left
        rcases hC.cover v₀ hxSf (hx'.2 v₀ rfl) with h₀ | h₀ | h₀
        · left; left; left
          rw [mem_geoCarrierCrossings]
          exact ⟨hxSf, fun w hw => (hown w hw).trans h₀⟩
        · left; left; right
          rw [mem_geoCarrierCrossings]
          exact ⟨hxSf, fun w hw => (hown w hw).trans h₀⟩
        · left; right
          rw [mem_geoCarrierCrossings]
          exact ⟨hxSf, fun w hw => (hown w hw).trans h₀⟩
      · left; right
        exact ⟨hx, hxSf, v₀, visitTwin v₀, rfl, rfl, heq⟩
  · rintro ((((h | h) | h) | ⟨h, -⟩) | ⟨h, -⟩)
    · exact (w3cb_retained_child_subset hP hSS hC.subA h).1
    · exact (w3cb_retained_child_subset hP hSS hC.subB h).1
    · exact (w3cb_retained_child_subset hP hSS hC.subC h).1
    · exact h
    · exact h

theorem w3cb_card_retained (hSS : S' ⊆ Sf) (hC : w3cb_Children hP S' Sf q' A B C) :
    (geoCarrierCrossings hP S' q').card =
      (geoCarrierCrossings hP Sf A).card + (geoCarrierCrossings hP Sf B).card +
        (geoCarrierCrossings hP Sf C).card + (w3cb_mixedSet hP S' Sf q').card +
        (w3cb_selectedPart hP S' Sf q').card := by
  classical
  have hdis : ∀ {r r' : GeoComponent hP Sf}, r ≠ r' →
      Disjoint (geoCarrierCrossings hP Sf r) (geoCarrierCrossings hP Sf r') := by
    intro r r' hne
    rw [Finset.disjoint_left]
    intro x h₁ h₂
    obtain ⟨i, -, -⟩ := crossing_visits_exist x
    have e₁ := ((mem_geoCarrierCrossings hP Sf r x).mp h₁).2 ⟨x, i⟩ rfl
    have e₂ := ((mem_geoCarrierCrossings hP Sf r' x).mp h₂).2 ⟨x, i⟩ rfl
    exact hne (e₁.symm.trans e₂)
  have hAB := hdis hC.neAB
  have hABC : Disjoint (geoCarrierCrossings hP Sf A ∪ geoCarrierCrossings hP Sf B)
      (geoCarrierCrossings hP Sf C) :=
    Finset.disjoint_union_left.mpr ⟨hdis hC.neAC, hdis hC.neBC⟩
  have hM : ∀ r : GeoComponent hP Sf,
      Disjoint (geoCarrierCrossings hP Sf r) (w3cb_mixedSet hP S' Sf q') := by
    intro r
    rw [Finset.disjoint_left]
    intro x hx hM
    obtain ⟨-, -, v, w, hv, hw, hne⟩ := Finset.mem_filter.mp hM
    have e₁ := ((mem_geoCarrierCrossings hP Sf r x).mp hx).2 v hv
    have e₂ := ((mem_geoCarrierCrossings hP Sf r x).mp hx).2 w hw
    exact hne (e₁.trans e₂.symm)
  have hMM : Disjoint (geoCarrierCrossings hP Sf A ∪ geoCarrierCrossings hP Sf B ∪
      geoCarrierCrossings hP Sf C) (w3cb_mixedSet hP S' Sf q') :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hM A, hM B⟩, hM C⟩
  have hS : Disjoint (geoCarrierCrossings hP Sf A ∪ geoCarrierCrossings hP Sf B ∪
      geoCarrierCrossings hP Sf C ∪ w3cb_mixedSet hP S' Sf q') (w3cb_selectedPart hP S' Sf q') := by
    rw [Finset.disjoint_left]
    intro x hx hS
    have hxSf : x ∈ Sf := (Finset.mem_filter.mp hS).2
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact ((mem_geoCarrierCrossings hP Sf A x).mp h).1 hxSf
        · exact ((mem_geoCarrierCrossings hP Sf B x).mp h).1 hxSf
      · exact ((mem_geoCarrierCrossings hP Sf C x).mp h).1 hxSf
    · exact (Finset.mem_filter.mp h).2.1 hxSf
  rw [w3cb_retained_decomp hP hSS hC, Finset.card_union_of_disjoint hS,
    Finset.card_union_of_disjoint hMM, Finset.card_union_of_disjoint hABC,
    Finset.card_union_of_disjoint hAB]

theorem w3cb_selectedPart_eq (e f g : ZMod n) {Q : Finset (Crossing P)} (q₀ : GeoComponent hP Q)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hP Q q₀) :
    w3cb_selectedPart hP Q (Q ∪ triangleCrossings P e f g) q₀ = triangleCrossings P e f g := by
  classical
  ext x
  simp only [w3cb_selectedPart, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hx, hxQ | hxT⟩
    · exact absurd hxQ ((mem_geoCarrierCrossings hP Q q₀ x).mp hx).1
    · exact hxT
  · intro hxT
    exact ⟨htri hxT, Or.inr hxT⟩

theorem w3cb_writhe_count (hG : CV.Generic P) (e f g : ZMod n) {Q : Finset (Crossing P)}
    (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (q₀ : GeoComponent hG.crossingGeometry Q)
    {A B C : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)}
    (hC : w3cb_Children hG.crossingGeometry Q (Q ∪ triangleCrossings P e f g) q₀ A B C)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.crossingGeometry Q q₀) :
    CV.groupedWrithe hG q₀ =
      3 + CV.groupedWrithe hG A + CV.groupedWrithe hG B + CV.groupedWrithe hG C +
        ((w3cb_mixedSet hG.crossingGeometry Q (Q ∪ triangleCrossings P e f g) q₀).card : ℤ) := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG hQ,
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS A,
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS B,
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS C,
    w3cb_card_retained hG.crossingGeometry Finset.subset_union_left hC,
    w3cb_selectedPart_eq hG.crossingGeometry e f g q₀ htri, P1.triangleCrossings_card hef heg hfg]
  push_cast
  ring

theorem w3cb_writhe_field (hG : CV.Generic P) (e f g : ZMod n) {Q : Finset (Crossing P)}
    (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (q₀ : GeoComponent hG.crossingGeometry Q)
    {A B C : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)}
    (hC : w3cb_Children hG.crossingGeometry Q (Q ∪ triangleCrossings P e f g) q₀ A B C)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.crossingGeometry Q q₀) (Λ : ℕ)
    (hΛ : (w3cb_mixedSet hG.crossingGeometry Q (Q ∪ triangleCrossings P e f g) q₀).card = 2 * Λ) :
    CV.groupedWrithe hG q₀ =
      3 + CV.groupedWrithe hG A + CV.groupedWrithe hG B + CV.groupedWrithe hG C + 2 * (Λ : ℤ) := by
  rw [w3cb_writhe_count hG e f g hQ hS hef heg hfg q₀ hC htri, hΛ]
  push_cast
  ring

structure w3cb_CornerData {Q Sf : Finset (Crossing P)} (q₀ : GeoComponent hP Q)
    (A B C : GeoComponent hP Sf) (s : SignType) : Prop where
  s_ne : s ≠ 0
  localA : ∃ k, turn (geoCornerPolygon hP Sf A) k = s
  localB : ∃ k, turn (geoCornerPolygon hP Sf B) k = s
  localC : ∃ k, turn (geoCornerPolygon hP Sf C) k = s
  inherit : ∀ k : ZMod (geoCornerCount hP Q q₀),
    (∃ k', turn (geoCornerPolygon hP Sf A) k' = turn (geoCornerPolygon hP Q q₀) k) ∨
    (∃ k', turn (geoCornerPolygon hP Sf B) k' = turn (geoCornerPolygon hP Q q₀) k) ∨
    (∃ k', turn (geoCornerPolygon hP Sf C) k' = turn (geoCornerPolygon hP Q q₀) k)

theorem w3cb_uniform_of_cornerData {Q : Finset (Crossing P)} {q₀ : GeoComponent hP Q} {s : SignType}
    (hcd : w3cb_CornerData hP q₀ A B C s)
    (hA : CV.CarrierUniform hP Sf A) (hB : CV.CarrierUniform hP Sf B) (hC : CV.CarrierUniform hP Sf C) :
    CV.CarrierUniform hP Q q₀ := by
  obtain ⟨τA, -, hτA⟩ := hA
  obtain ⟨τB, -, hτB⟩ := hB
  obtain ⟨τC, -, hτC⟩ := hC
  obtain ⟨kA, hkA⟩ := hcd.localA
  obtain ⟨kB, hkB⟩ := hcd.localB
  obtain ⟨kC, hkC⟩ := hcd.localC
  have eA : τA = s := (hτA kA).symm.trans hkA
  have eB : τB = s := (hτB kB).symm.trans hkB
  have eC : τC = s := (hτC kC).symm.trans hkC
  refine ⟨s, hcd.s_ne, fun k => ?_⟩
  rcases hcd.inherit k with ⟨k', hk'⟩ | ⟨k', hk'⟩ | ⟨k', hk'⟩
  · rw [← hk', hτA k', eA]
  · rw [← hk', hτB k', eB]
  · rw [← hk', hτC k', eC]

theorem w3cb_mixed_field {Q : Finset (Crossing P)} {q₀ : GeoComponent hP Q} (Z : GeoComponent hP Sf)
    {s : SignType} (hcd : w3cb_CornerData hP q₀ A B C s) (hmix : CV.CarrierMixed hP Q q₀) :
    CV.weight hP Sf A * CV.weight hP Sf B * CV.weight hP Sf C * CV.weight hP Sf Z = 0 := by
  by_contra h
  have hA : CV.weight hP Sf A ≠ 0 := fun h0 => h (by simp [h0])
  have hB : CV.weight hP Sf B ≠ 0 := fun h0 => h (by simp [h0])
  have hC : CV.weight hP Sf C ≠ 0 := fun h0 => h (by simp [h0])
  exact hmix (w3cb_uniform_of_cornerData hP hcd ((CV.weight_ne_zero_iff hP Sf A).mp hA)
    ((CV.weight_ne_zero_iff hP Sf B).mp hB) ((CV.weight_ne_zero_iff hP Sf C).mp hC))


/-! #### The turn at a corner mark, and its inheritance from `Q` to `Q ∪ T` -/

/-- the sign of the turn at a mark `m` of a carrier of `S`: the sign of the determinant of the incoming
original edge and the outgoing slot's edge (the corner-polygon turn at the corner `m`, `w3cb_turn_eq_turnAt`) -/
noncomputable def w3cb_turnAt (S : Finset (Crossing P)) (m : Mark P) : SignType :=
  SignType.sign (det (edge P (geoInEdge hP m)) (edge P (geoOutSlot hP S m).1))

/-- the turn of the corner polygon at `k` is the turn at its corner mark (`geoCornerPolygon_edge_pred_smul`,
`geoCornerPolygon_edge_smul`: the two polygon edges are positive multiples of the two mark edges) -/
theorem w3cb_turn_eq_turnAt (hn : 3 ≤ n) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (r : GeoComponent hP S) (k : ZMod (geoCornerCount hP S r)) :
    turn (geoCornerPolygon hP S r) k = w3cb_turnAt hP S (geoCornerMark hP S r k) := by
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred_smul hn hP hS r k
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge_smul hn hP hS r k
  rw [turn_det, he₁, he₂, det_smul_left, det_smul_right, sign_mul, sign_mul, sign_pos hc₁, sign_pos hc₂,
    one_mul, one_mul]
  rfl

/-- the out-slot edge of a mark is unchanged by a change of support that does not select or deselect its
crossing -/
theorem w3cb_outSlot_eq_of_iff {S S' : Finset (Crossing P)} (m : Mark P)
    (h : ∀ w : Visit P, m = Sum.inr w → (w.1 ∈ S' ↔ w.1 ∈ S)) :
    (geoOutSlot hP S' m).1 = (geoOutSlot hP S m).1 := by
  cases m with
  | inl i => rfl
  | inr w =>
    by_cases hw : w.1 ∈ S
    · rw [geoOutSlot_selected hP S w hw, geoOutSlot_selected hP S' w ((h w rfl).mpr hw)]
    · rw [geoOutSlot_unselected hP S w hw, geoOutSlot_unselected hP S' w (fun h' => hw ((h w rfl).mp h'))]

theorem w3cb_turnAt_eq_of_iff {S S' : Finset (Crossing P)} (m : Mark P)
    (h : ∀ w : Visit P, m = Sum.inr w → (w.1 ∈ S' ↔ w.1 ∈ S)) :
    w3cb_turnAt hP S' m = w3cb_turnAt hP S m := by
  unfold w3cb_turnAt
  rw [w3cb_outSlot_eq_of_iff hP m h]

omit [NeZero n] in
/-- true corners persist under enlargement of the support -/
theorem w3cb_isTrueCorner_mono {S S' : Finset (Crossing P)} (hSS : S ⊆ S') {m : Mark P}
    (h : IsTrueCorner S m) : IsTrueCorner S' m := by
  cases m with
  | inl i => trivial
  | inr w => exact hSS h

/-- **The clean outer children at the mark level**: `w3cb_Children` plus "all nonlocal corners of the
empty contact carrier partition among the three outer carriers" (ESC §4) — every corner mark of `q'` is owned
in `Sf` by `A`, `B` or `C`. -/
structure w3cb_MarkChildren (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S')
    (A B C : GeoComponent hP Sf) : Prop extends w3cb_Children hP S' Sf q' A B C where
  coverCorner : ∀ m : Mark P, geoOwner hP S' m = q' → IsTrueCorner S' m →
    geoOwner hP Sf m = A ∨ geoOwner hP Sf m = B ∨ geoOwner hP Sf m = C

/-- **An inherited corner keeps its turn**: a corner mark of `q'` (a carrier of `S'`) owned in `Sf ⊇ S'` by
`r` is a corner of `r` with the same turn (its crossing, if any, is selected in both supports). -/
theorem w3cb_inherit_turn (hn : 3 ≤ n) {S' Sf : Finset (Crossing P)} (hSS : S' ⊆ Sf)
    (hS' : GeoIndependent hP S') (hSf : GeoIndependent hP Sf) {q' : GeoComponent hP S'}
    {r : GeoComponent hP Sf} (k : ZMod (geoCornerCount hP S' q'))
    (hown : geoOwner hP Sf (geoCornerMark hP S' q' k) = r) :
    ∃ k' : ZMod (geoCornerCount hP Sf r),
      turn (geoCornerPolygon hP Sf r) k' = turn (geoCornerPolygon hP S' q') k := by
  have hm := geoCornerMark_mem hP S' q' k
  obtain ⟨k', hk'⟩ := geoCornerMark_exists_of_owner hP Sf r _ hown (w3cb_isTrueCorner_mono hSS hm.2)
  refine ⟨k', ?_⟩
  rw [w3cb_turn_eq_turnAt hP hn hSf r k', w3cb_turn_eq_turnAt hP hn hS' q' k, hk']
  apply w3cb_turnAt_eq_of_iff
  intro w hw
  have h2 := hm.2
  rw [hw] at h2
  exact ⟨fun _ => h2, fun h => hSS h⟩

/-- the `inherit` clause of `w3cb_CornerData` from the mark-level children -/
theorem w3cb_inherit_of_markChildren (hn : 3 ≤ n) (hSS : S' ⊆ Sf)
    (hS' : GeoIndependent hP S') (hSf : GeoIndependent hP Sf)
    (hC : w3cb_MarkChildren hP S' Sf q' A B C) (k : ZMod (geoCornerCount hP S' q')) :
    (∃ k', turn (geoCornerPolygon hP Sf A) k' = turn (geoCornerPolygon hP S' q') k) ∨
    (∃ k', turn (geoCornerPolygon hP Sf B) k' = turn (geoCornerPolygon hP S' q') k) ∨
    (∃ k', turn (geoCornerPolygon hP Sf C) k' = turn (geoCornerPolygon hP S' q') k) := by
  have hm := geoCornerMark_mem hP S' q' k
  rcases hC.coverCorner _ hm.1 hm.2 with h | h | h
  · exact Or.inl (w3cb_inherit_turn hP hn hSS hS' hSf k h)
  · exact Or.inr (Or.inl (w3cb_inherit_turn hP hn hSS hS' hSf k h))
  · exact Or.inr (Or.inr (w3cb_inherit_turn hP hn hSS hS' hSf k h))

/-- a selected visit owned by `r` with turn `s` gives a corner of `r` with turn `s` (the local smoothing corner
of an outer carrier: its triangle-crossing visit) -/
theorem w3cb_local_of_visit (hn : 3 ≤ n) (hSf : GeoIndependent hP Sf) {r : GeoComponent hP Sf} {v : Visit P}
    (hv : v.1 ∈ Sf) (hown : geoOwner hP Sf (Sum.inr v) = r) {s : SignType}
    (hs : w3cb_turnAt hP Sf (Sum.inr v) = s) :
    ∃ k, turn (geoCornerPolygon hP Sf r) k = s := by
  obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP Sf r _ hown hv
  exact ⟨k, by rw [w3cb_turn_eq_turnAt hP hn hSf r k, hk, hs]⟩

/-- `w3cb_CornerData` from the mark-level children and the three local corner signs -/
theorem w3cb_cornerData_of (hn : 3 ≤ n) (hSS : S' ⊆ Sf)
    (hS' : GeoIndependent hP S') (hSf : GeoIndependent hP Sf)
    (hC : w3cb_MarkChildren hP S' Sf q' A B C) {s : SignType} (hs : s ≠ 0)
    (hA : ∃ k, turn (geoCornerPolygon hP Sf A) k = s) (hB : ∃ k, turn (geoCornerPolygon hP Sf B) k = s)
    (hC' : ∃ k, turn (geoCornerPolygon hP Sf C) k = s) : w3cb_CornerData hP q' A B C s :=
  { s_ne := hs, localA := hA, localB := hB, localC := hC',
    inherit := w3cb_inherit_of_markChildren hP hn hSS hS' hSf hC }

/-! #### The bundle towards SPLITA, and the two fields of `esc_FullSplitData` -/

/-- **The geometric input of SPLITB at one configuration** (the black box towards unit SPLITA, ESC §1, §4):
the three outer children of the contact carrier `q₀` of `Q` inside `Q ∪ T` at the mark level, the three
triangle crossings retained on `q₀` ("all six visits lie on one `Q`-carrier"), the common local corner sign
`s = s_o` of the three outer carriers at their triangle-crossing visits (the sign table (1c)), and the
parity of the crossings between distinct outer gap strings (`2Λ`, `Λ = lk(J)` of the KNOT unit). -/
structure w3cb_SplitGeometry (e f g : ZMod n) {Q : Finset (Crossing P)} (q₀ : GeoComponent hP Q)
    (A B C : GeoComponent hP (Q ∪ triangleCrossings P e f g)) (Λ : ℕ) (s : SignType) : Prop where
  children : w3cb_MarkChildren hP Q (Q ∪ triangleCrossings P e f g) q₀ A B C
  triangle_on_contact : triangleCrossings P e f g ⊆ geoCarrierCrossings hP Q q₀
  s_ne : s ≠ 0
  localA : ∃ v : Visit P, v.1 ∈ triangleCrossings P e f g ∧
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = A ∧
    w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s
  localB : ∃ v : Visit P, v.1 ∈ triangleCrossings P e f g ∧
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = B ∧
    w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s
  localC : ∃ v : Visit P, v.1 ∈ triangleCrossings P e f g ∧
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = C ∧
    w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s
  mixed_even : (w3cb_mixedSet hP Q (Q ∪ triangleCrossings P e f g) q₀).card = 2 * Λ

theorem w3cb_cornerData_of_splitGeometry (hn : 3 ≤ n) {e f g : ZMod n} {Q : Finset (Crossing P)}
    (hQ : GeoIndependent hP Q) (hS : GeoIndependent hP (Q ∪ triangleCrossings P e f g))
    {q₀ : GeoComponent hP Q} {A B C : GeoComponent hP (Q ∪ triangleCrossings P e f g)} {Λ : ℕ} {s : SignType}
    (h : w3cb_SplitGeometry hP e f g q₀ A B C Λ s) : w3cb_CornerData hP q₀ A B C s := by
  obtain ⟨vA, hvA, hoA, hsA⟩ := h.localA
  obtain ⟨vB, hvB, hoB, hsB⟩ := h.localB
  obtain ⟨vC, hvC, hoC, hsC⟩ := h.localC
  exact w3cb_cornerData_of hP hn Finset.subset_union_left hQ hS h.children h.s_ne
    (w3cb_local_of_visit hP hn hS (Finset.mem_union_right _ hvA) hoA hsA)
    (w3cb_local_of_visit hP hn hS (Finset.mem_union_right _ hvB) hoB hsB)
    (w3cb_local_of_visit hP hn hS (Finset.mem_union_right _ hvC) hoC hsC)

/-- **The two SPLITB fields of `esc_FullSplitData`** — `writhe` (17) and `mixed` — from the split geometry. -/
theorem w3cb_fields_of_splitGeometry (hn : 3 ≤ n) (hG : CV.Generic P) (e f g : ZMod n)
    {Q : Finset (Crossing P)} (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (q₀ : GeoComponent hG.crossingGeometry Q)
    {A B C : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)}
    (Z : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)) {Λ : ℕ} {s : SignType}
    (h : w3cb_SplitGeometry hG.crossingGeometry e f g q₀ A B C Λ s) :
    (CV.groupedWrithe hG q₀ =
      3 + CV.groupedWrithe hG A + CV.groupedWrithe hG B + CV.groupedWrithe hG C + 2 * (Λ : ℤ)) ∧
    (CV.CarrierMixed hG.crossingGeometry Q q₀ →
      CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
        CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0) :=
  ⟨w3cb_writhe_field hG e f g hQ hS hef heg hfg q₀ h.children.tow3cb_Children h.triangle_on_contact Λ h.mixed_even,
    fun hmix => w3cb_mixed_field hG.crossingGeometry Z
      (w3cb_cornerData_of_splitGeometry hG.crossingGeometry hn
        (CV.geoIndependent_of_mem_Ind _ hQ) (CV.geoIndependent_of_mem_Ind _ hS) h) hmix⟩

/-- **`esc_FullSplitData` assembled**: SPLITB's two fields from `w3cb_SplitGeometry`, the six other fields
(SPLITA's: `touching_iff`, `distinct`, `central_no_piece`, `central_rot`, `outer_alternative`, `uniform`) as
hypotheses in the exact field statements. -/
theorem w3cb_fullSplitData_of (hn : 3 ≤ n) (hG : CV.Generic P) (e f g : ZMod n)
    {Q : Finset (Crossing P)} (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (q₀ : GeoComponent hG.crossingGeometry Q)
    (A B C Z : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)) (Λ : ℕ) {s : SignType}
    (h : w3cb_SplitGeometry hG.crossingGeometry e f g q₀ A B C Λ s)
    (touching_iff : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry (Q ∪ triangleCrossings P e f g) e f g q ↔
      (q = A ∨ q = B ∨ q = C ∨ q = Z))
    (distinct : A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z)
    (central_no_piece : CV.piecesOn hG.crossingGeometry (Q ∪ triangleCrossings P e f g) Z = ∅)
    (central_rot : CV.carrierR hn hG hS Z = 1)
    (outer_alternative : CV.CarrierUniform hG.crossingGeometry Q q₀ →
      CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ A) ∧
      CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ B) ∧
      CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ C))
    (uniform : CV.CarrierUniform hG.crossingGeometry Q q₀ →
      (CV.carrierR hn hG hS A + CV.carrierR hn hG hS B + CV.carrierR hn hG hS C = CV.carrierR hn hG hQ q₀ + 1 ∧
        CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
          CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z =
          -CV.weight hG.crossingGeometry Q q₀) ∨
      (CV.carrierR hn hG hS A + CV.carrierR hn hG hS B + CV.carrierR hn hG hS C + 1 = CV.carrierR hn hG hQ q₀ ∧
        CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
          CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0)) :
    esc_FullSplitData hn hG e f g hQ hS q₀ A B C Z Λ :=
  { touching_iff := touching_iff, distinct := distinct, central_no_piece := central_no_piece,
    central_rot := central_rot,
    writhe := (w3cb_fields_of_splitGeometry hn hG e f g hQ hS hef heg hfg q₀ Z h).1
    mixed := (w3cb_fields_of_splitGeometry hn hG e f g hQ hS hef heg hfg q₀ Z h).2
    outer_alternative := outer_alternative, uniform := uniform }

/-! #### The event level: the black box towards SPLITA, and the clause that is already free -/

/-- **BLACK BOX (unit SPLITA / the outer geometry): the split geometry at every configuration of the extended
interface** — same binders as `w3bi_esc_outer` up to the two contact carriers; the `A, B, C` and `Λ` are to be
the ones of `esc_FullSplitData` (the assembler unifies the existentials with SPLITA's `Z` and KNOT's `Λ`). -/
def w3cb_split_geometry : Prop :=
  ∀ {n : ℕ} [NeZero n] (_hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (_hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (_hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ) (s : SignType),
        w3cb_SplitGeometry (geomAt E t' ht'.1) e f g q₀' A B C Λ s

/-- **`triangle_on_contact` is FREE at the event level**: the triangle-touching carrier of the transported
outside support on the empty side owns every visit of every triangle crossing (`esc_contact_owns` after
`GT_outsideSupports_transport` / `GT_fullAvail_transport`). -/
theorem w3cb_triangle_on_contact_at {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)}
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀') :
    triangleCrossings (E.curve t') e f g ⊆
      geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) q₀' :=
  esc_contact_owns hL (P1.ne_of_isCrossing_pair hef) (P1.ne_of_isCrossing_pair heg)
    (P1.ne_of_isCrossing_pair hfg) ht' (GT_outsideSupports_transport hL ht ht' hop hs hQ)
    (GT_fullAvail_transport hL ht ht' hop hs hQ hfull) hq₀'

/-! #### The children from the six triangle visits: three iterated insertions (the accepted one-insertion
lemmas `geoComponentForgetSwitch_fiber_affected`, `geoOwner_insert_iff_of_unaffected`,
`geoIndependent_remaining_pair_owners`, `geoOwner_eq_of_subset`) -/

omit [NeZero n] in
theorem w3cb_geoIndependent_mono {S S' : Finset (Crossing P)} (hS' : GeoIndependent hP S') (hSS : S ⊆ S') :
    GeoIndependent hP S :=
  fun x hx y hy hne => hS' x (hSS hx) y (hSS hy) hne

section W3CB_Classical
/- the accepted insertion lemmas of `SM/GeoCarrierCount.lean` elaborate `insert` with the classical instance
(`attribute [local instance] Classical.propDecidable` there); this subsection follows them, and
`w3cb_cover_triangle` bridges back to the file's global `RProof.instDecidableEqCrossing` through the
accepted `CV.cvt165s_insert_eq`. -/
attribute [local instance high] Classical.propDecidable

/-- one insertion, the affected carrier: a mark of the carrier owning both visits of the inserted crossing
lands on the daughter of `v` or on the daughter of its twin -/
theorem w3cb_step_affected (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T) (v : Visit P)
    (hv : v.1 ∉ T) (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) (m : Mark P)
    (hm : geoOwner hP T m = geoOwner hP T (Sum.inr v)) :
    geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) (Sum.inr v) ∨
    geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) := by
  obtain ⟨-, hfib⟩ := geoComponentForgetSwitch_fiber_affected hP T hI v hv hc
  rw [Finset.ext_iff] at hfib
  have hmem := (hfib (geoOwner hP (insert v.1 T) m)).mp
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [geoComponentForgetSwitch_owner, hm]⟩)
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

/-- one insertion, both cases: a mark `m` on the carrier of `w` stays with `w`, or lands on one of the two
daughters of the inserted visit -/
theorem w3cb_stage (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T) (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) (m w : Mark P)
    (hm : geoOwner hP T m = geoOwner hP T w) :
    geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) w ∨
    geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) (Sum.inr v) ∨
    geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) := by
  by_cases h : geoOwner hP T w = geoOwner hP T (Sum.inr v)
  · exact Or.inr (w3cb_step_affected hP T hI v hv hc m (hm.trans h))
  · exact Or.inl ((geoOwner_insert_iff_of_unaffected hP T v hv hc _ h w rfl m).mpr hm)

/-- **Three insertions of retained crossings of `q₀`**: every mark of `q₀` lands on the carrier of one of the
six visits of the three inserted crossings. -/
theorem w3cb_cover_three {Q : Finset (Crossing P)} {x₁ x₂ x₃ : Crossing P}
    (hSf : GeoIndependent hP (insert x₃ (insert x₂ (insert x₁ Q)))) {q₀ : GeoComponent hP Q}
    (h₁ : x₁ ∈ geoCarrierCrossings hP Q q₀) (h₂ : x₂ ∈ geoCarrierCrossings hP Q q₀)
    (h₃ : x₃ ∈ geoCarrierCrossings hP Q q₀) (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃)
    (m : Mark P) (hm : geoOwner hP Q m = q₀) :
    ∃ w : Visit P, (w.1 = x₁ ∨ w.1 = x₂ ∨ w.1 = x₃) ∧
      geoOwner hP (insert x₃ (insert x₂ (insert x₁ Q))) m =
        geoOwner hP (insert x₃ (insert x₂ (insert x₁ Q))) (Sum.inr w) := by
  have hQ₁S : insert x₁ Q ⊆ insert x₃ (insert x₂ (insert x₁ Q)) :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have hQ₂S : insert x₂ (insert x₁ Q) ⊆ insert x₃ (insert x₂ (insert x₁ Q)) := Finset.subset_insert _ _
  have hQ : GeoIndependent hP Q :=
    w3cb_geoIndependent_mono hP hSf ((Finset.subset_insert _ _).trans hQ₁S)
  have hQ₁ : GeoIndependent hP (insert x₁ Q) := w3cb_geoIndependent_mono hP hSf hQ₁S
  have hQ₂ : GeoIndependent hP (insert x₂ (insert x₁ Q)) := w3cb_geoIndependent_mono hP hSf hQ₂S
  rw [mem_geoCarrierCrossings] at h₁ h₂ h₃
  obtain ⟨i₁, -, -⟩ := crossing_visits_exist x₁
  obtain ⟨i₂, -, -⟩ := crossing_visits_exist x₂
  obtain ⟨i₃, -, -⟩ := crossing_visits_exist x₃
  -- stage 0: insert `x₁`
  have hc₁ : geoOwner hP Q (Sum.inr ⟨x₁, i₁⟩) = geoOwner hP Q (Sum.inr (visitTwin ⟨x₁, i₁⟩)) :=
    (h₁.2 _ rfl).trans (h₁.2 _ (visitTwin_crossing _)).symm
  have hm₀ : geoOwner hP Q m = geoOwner hP Q (Sum.inr ⟨x₁, i₁⟩) := hm.trans (h₁.2 _ rfl).symm
  have e₁ : ∃ w : Visit P, w.1 = x₁ ∧
      geoOwner hP (insert x₁ Q) m = geoOwner hP (insert x₁ Q) (Sum.inr w) := by
    rcases w3cb_step_affected hP Q (geoInheritsMarkOrder_of_independent hP hQ) ⟨x₁, i₁⟩ h₁.1 hc₁ m hm₀
      with h | h
    · exact ⟨_, rfl, h⟩
    · exact ⟨_, visitTwin_crossing _, h⟩
  -- stage 1: insert `x₂`
  have hx₂ : x₂ ∉ insert x₁ Q := fun h => by
    rcases Finset.mem_insert.mp h with h | h
    · exact h₁₂ h.symm
    · exact h₂.1 h
  have hc₂ : geoOwner hP (insert x₁ Q) (Sum.inr ⟨x₂, i₂⟩) =
      geoOwner hP (insert x₁ Q) (Sum.inr (visitTwin ⟨x₂, i₂⟩)) :=
    geoIndependent_remaining_pair_owners hP hSf _ hQ₁S ⟨x₂, i₂⟩ (hQ₂S (Finset.mem_insert_self _ _)) hx₂
  obtain ⟨w₁, hw₁, hm₁⟩ := e₁
  have e₂ : ∃ w : Visit P, (w.1 = x₁ ∨ w.1 = x₂) ∧
      geoOwner hP (insert x₂ (insert x₁ Q)) m = geoOwner hP (insert x₂ (insert x₁ Q)) (Sum.inr w) := by
    rcases w3cb_stage hP _ (geoInheritsMarkOrder_of_independent hP hQ₁) ⟨x₂, i₂⟩ hx₂ hc₂ m (Sum.inr w₁) hm₁
      with h | h | h
    · exact ⟨w₁, Or.inl hw₁, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
    · exact ⟨_, Or.inr (visitTwin_crossing _), h⟩
  -- stage 2: insert `x₃`
  have hx₃ : x₃ ∉ insert x₂ (insert x₁ Q) := fun h => by
    rcases Finset.mem_insert.mp h with h | h
    · exact h₂₃ h.symm
    · rcases Finset.mem_insert.mp h with h | h
      · exact h₁₃ h.symm
      · exact h₃.1 h
  have hc₃ : geoOwner hP (insert x₂ (insert x₁ Q)) (Sum.inr ⟨x₃, i₃⟩) =
      geoOwner hP (insert x₂ (insert x₁ Q)) (Sum.inr (visitTwin ⟨x₃, i₃⟩)) :=
    geoIndependent_remaining_pair_owners hP hSf _ hQ₂S ⟨x₃, i₃⟩ (Finset.mem_insert_self _ _) hx₃
  obtain ⟨w₂, hw₂, hm₂⟩ := e₂
  rcases w3cb_stage hP _ (geoInheritsMarkOrder_of_independent hP hQ₂) ⟨x₃, i₃⟩ hx₃ hc₃ m (Sum.inr w₂) hm₂
    with h | h | h
  · exact ⟨w₂, hw₂.elim Or.inl (fun h' => Or.inr (Or.inl h')), h⟩
  · exact ⟨_, Or.inr (Or.inr rfl), h⟩
  · exact ⟨_, Or.inr (Or.inr (visitTwin_crossing _)), h⟩

end W3CB_Classical

theorem w3cb_union_triangle_eq {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) (Q : Finset (Crossing P)) :
    Q ∪ triangleCrossings P e f g = insert (xPair hfg) (insert (xPair heg) (insert (xPair hef) Q)) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, P1.mem_triangleCrossings_iff hef heg hfg]
  tauto

/-- **Every mark of the contact carrier lands on the `Q ∪ T`-carrier of one of the six triangle visits.** -/
theorem w3cb_cover_triangle {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) {Q : Finset (Crossing P)}
    (hSf : GeoIndependent hP (Q ∪ triangleCrossings P e f g)) {q₀ : GeoComponent hP Q}
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hP Q q₀) (m : Mark P)
    (hm : geoOwner hP Q m = q₀) :
    ∃ w : Visit P, w.1 ∈ triangleCrossings P e f g ∧
      geoOwner hP (Q ∪ triangleCrossings P e f g) m =
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) := by
  have hT : ∀ x, x ∈ triangleCrossings P e f g ↔ x = xPair hef ∨ x = xPair heg ∨ x = xPair hfg :=
    P1.mem_triangleCrossings_iff hef heg hfg
  rw [w3cb_union_triangle_eq hef heg hfg Q, CV.cvt165s_insert_eq (xPair hef) Q,
    CV.cvt165s_insert_eq (xPair heg), CV.cvt165s_insert_eq (xPair hfg)] at hSf ⊢
  obtain ⟨w, hw, hmw⟩ := w3cb_cover_three hP hSf (htri ((hT _).mpr (Or.inl rfl)))
    (htri ((hT _).mpr (Or.inr (Or.inl rfl)))) (htri ((hT _).mpr (Or.inr (Or.inr rfl))))
    (P1.xPair_ef_ne_eg hef heg hfg) (P1.xPair_ef_ne_fg hef heg hfg) (P1.xPair_eg_ne_fg hef heg hfg) m hm
  exact ⟨w, (hT _).mpr hw, hmw⟩

/-- **`w3cb_MarkChildren` from the six triangle visits**: `A, B, C` are the `Q ∪ T`-carriers of three triangle
visits, pairwise distinct, and the carrier of every triangle visit is `A`, `B`, `C` or a carrier owning only
triangle visits (the central triangle `Z`, ESC §4 "the central triangle owns only the three local corner
marks" — the remaining geometric input). -/
theorem w3cb_markChildren_of {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) {Q : Finset (Crossing P)}
    (hSf : GeoIndependent hP (Q ∪ triangleCrossings P e f g)) {q₀ : GeoComponent hP Q}
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hP Q q₀)
    {A B C : GeoComponent hP (Q ∪ triangleCrossings P e f g)}
    (hA : ∃ w : Visit P, w.1 ∈ triangleCrossings P e f g ∧
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = A)
    (hB : ∃ w : Visit P, w.1 ∈ triangleCrossings P e f g ∧
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = B)
    (hC : ∃ w : Visit P, w.1 ∈ triangleCrossings P e f g ∧
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = C)
    (neAB : A ≠ B) (neAC : A ≠ C) (neBC : B ≠ C)
    (hcov : ∀ w : Visit P, w.1 ∈ triangleCrossings P e f g →
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = A ∨
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = B ∨
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = C ∨
      (∀ m : Mark P, geoOwner hP (Q ∪ triangleCrossings P e f g) m =
          geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) →
        ∃ v : Visit P, m = Sum.inr v ∧ v.1 ∈ triangleCrossings P e f g)) :
    w3cb_MarkChildren hP Q (Q ∪ triangleCrossings P e f g) q₀ A B C := by
  -- a child is the carrier of a triangle visit, which lies on `q₀`: refinement gives `sub`
  have hsub : ∀ {r : GeoComponent hP (Q ∪ triangleCrossings P e f g)},
      (∃ w : Visit P, w.1 ∈ triangleCrossings P e f g ∧
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = r) →
      ∀ m : Mark P, geoOwner hP (Q ∪ triangleCrossings P e f g) m = r → geoOwner hP Q m = q₀ := by
    rintro r ⟨w, hw, hwr⟩ m hm
    have h := geoOwner_eq_of_subset hP hSf Finset.subset_union_left m (Sum.inr w) (hm.trans hwr.symm)
    rw [h]
    exact ((mem_geoCarrierCrossings hP Q q₀ w.1).mp (htri hw)).2 w rfl
  -- a mark of `q₀` that is not a triangle visit lands on `A`, `B` or `C`
  have hcover : ∀ m : Mark P, geoOwner hP Q m = q₀ →
      (∀ v : Visit P, m = Sum.inr v → v.1 ∉ triangleCrossings P e f g) →
      geoOwner hP (Q ∪ triangleCrossings P e f g) m = A ∨
      geoOwner hP (Q ∪ triangleCrossings P e f g) m = B ∨
      geoOwner hP (Q ∪ triangleCrossings P e f g) m = C := by
    intro m hm hnot
    obtain ⟨w, hw, hmw⟩ := w3cb_cover_triangle hP hef heg hfg hSf htri m hm
    rcases hcov w hw with h | h | h | h
    · exact Or.inl (hmw.trans h)
    · exact Or.inr (Or.inl (hmw.trans h))
    · exact Or.inr (Or.inr (hmw.trans h))
    · obtain ⟨v, rfl, hv⟩ := h m hmw
      exact absurd hv (hnot v rfl)
  refine ⟨⟨hsub hA, hsub hB, hsub hC, neAB, neAC, neBC, ?_⟩, ?_⟩
  · intro w hw hq
    exact hcover _ hq fun v hv hvT => hw (by
      rw [show w = v from Sum.inr_injective hv]
      exact Finset.mem_union_right _ hvT)
  · intro m hm hcorner
    refine hcover m hm fun v hv hvT => ?_
    rw [hv] at hcorner
    exact ((mem_geoCarrierCrossings hP Q q₀ v.1).mp (htri hvT)).1 hcorner

/-! #### The residue towards SPLITA -/

/-- **The core of the residue** — the residue without `triangle_on_contact` (which is FREE at the event level,
`w3cb_triangle_on_contact_at`): `A, B, C` are the `Q ∪ T`-carriers of three triangle visits at which the local
turn is the common outer sign `s ≠ 0` (the sign table (1c)), pairwise distinct; the carrier of every triangle
visit is `A`, `B`, `C` or a carrier owning only triangle visits (the central triangle `Z`); the crossings between
distinct outer gap strings number `2Λ` (KNOT's `Λ = lk(J)`).  This is the black box towards SPLITA. -/
structure w3cb_SplitCore (e f g : ZMod n) {Q : Finset (Crossing P)} (q₀ : GeoComponent hP Q)
    (A B C : GeoComponent hP (Q ∪ triangleCrossings P e f g)) (Λ : ℕ) (s : SignType) : Prop where
  s_ne : s ≠ 0
  localA : ∃ v : Visit P, v.1 ∈ triangleCrossings P e f g ∧
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = A ∧
    w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s
  localB : ∃ v : Visit P, v.1 ∈ triangleCrossings P e f g ∧
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = B ∧
    w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s
  localC : ∃ v : Visit P, v.1 ∈ triangleCrossings P e f g ∧
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = C ∧
    w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s
  neAB : A ≠ B
  neAC : A ≠ C
  neBC : B ≠ C
  central : ∀ w : Visit P, w.1 ∈ triangleCrossings P e f g →
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = A ∨
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = B ∨
    geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) = C ∨
    (∀ m : Mark P, geoOwner hP (Q ∪ triangleCrossings P e f g) m =
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr w) →
      ∃ v : Visit P, m = Sum.inr v ∧ v.1 ∈ triangleCrossings P e f g)
  mixed_even : (w3cb_mixedSet hP Q (Q ∪ triangleCrossings P e f g) q₀).card = 2 * Λ

/-- **What remains for SPLITA after this unit's reductions**: the core plus the three triangle crossings retained
on `q₀` (FREE at the event level). -/
structure w3cb_SplitResidue (e f g : ZMod n) {Q : Finset (Crossing P)} (q₀ : GeoComponent hP Q)
    (A B C : GeoComponent hP (Q ∪ triangleCrossings P e f g)) (Λ : ℕ) (s : SignType) : Prop
    extends w3cb_SplitCore hP e f g q₀ A B C Λ s where
  triangle_on_contact : triangleCrossings P e f g ⊆ geoCarrierCrossings hP Q q₀

theorem w3cb_residue_of_core {e f g : ZMod n} {Q : Finset (Crossing P)} {q₀ : GeoComponent hP Q}
    {A B C : GeoComponent hP (Q ∪ triangleCrossings P e f g)} {Λ : ℕ} {s : SignType}
    (h : w3cb_SplitCore hP e f g q₀ A B C Λ s)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hP Q q₀) :
    w3cb_SplitResidue hP e f g q₀ A B C Λ s := ⟨h, htri⟩

/-- `w3cb_SplitGeometry` from the residue (the children clauses by `w3cb_markChildren_of`). -/
theorem w3cb_splitGeometry_of_residue {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) {Q : Finset (Crossing P)}
    (hSf : GeoIndependent hP (Q ∪ triangleCrossings P e f g)) {q₀ : GeoComponent hP Q}
    {A B C : GeoComponent hP (Q ∪ triangleCrossings P e f g)} {Λ : ℕ} {s : SignType}
    (h : w3cb_SplitResidue hP e f g q₀ A B C Λ s) : w3cb_SplitGeometry hP e f g q₀ A B C Λ s :=
  { children := w3cb_markChildren_of hP hef heg hfg hSf h.triangle_on_contact
      (h.localA.imp fun _ hv => ⟨hv.1, hv.2.1⟩) (h.localB.imp fun _ hv => ⟨hv.1, hv.2.1⟩)
      (h.localC.imp fun _ hv => ⟨hv.1, hv.2.1⟩) h.neAB h.neAC h.neBC h.central
    triangle_on_contact := h.triangle_on_contact, s_ne := h.s_ne, localA := h.localA, localB := h.localB,
    localC := h.localC, mixed_even := h.mixed_even }

/-- the two SPLITB fields from the residue -/
theorem w3cb_fields_of_residue (hn : 3 ≤ n) (hG : CV.Generic P) (e f g : ZMod n)
    {Q : Finset (Crossing P)} (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (q₀ : GeoComponent hG.crossingGeometry Q)
    {A B C : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)}
    (Z : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)) {Λ : ℕ} {s : SignType}
    (h : w3cb_SplitResidue hG.crossingGeometry e f g q₀ A B C Λ s) :
    (CV.groupedWrithe hG q₀ =
      3 + CV.groupedWrithe hG A + CV.groupedWrithe hG B + CV.groupedWrithe hG C + 2 * (Λ : ℤ)) ∧
    (CV.CarrierMixed hG.crossingGeometry Q q₀ →
      CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
        CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0) :=
  w3cb_fields_of_splitGeometry hn hG e f g hQ hS hef heg hfg q₀ Z
    (w3cb_splitGeometry_of_residue hG.crossingGeometry hef heg hfg (CV.geoIndependent_of_mem_Ind _ hS) h)

/-! #### Bonus: `central_no_piece` from the central clause -/

/-- **The central carrier carries no piece**: a carrier owning only triangle visits (all selected in `Q ∪ T`)
carries no residual piece (`esc_FullSplitData.central_no_piece`, "the central carrier's empty polynomial",
ESC §5) — every piece has a label, an unselected crossing both of whose visits the carrier would own. -/
theorem w3cb_central_no_piece {e f g : ZMod n} {Q : Finset (Crossing P)}
    {Z : GeoComponent hP (Q ∪ triangleCrossings P e f g)}
    (hZ : ∀ m : Mark P, geoOwner hP (Q ∪ triangleCrossings P e f g) m = Z →
      ∃ v : Visit P, m = Sum.inr v ∧ v.1 ∈ triangleCrossings P e f g) :
    CV.piecesOn hP (Q ∪ triangleCrossings P e f g) Z = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro H hH
  rw [CV.mem_piecesOn] at hH
  obtain ⟨c, hc⟩ := CV.pieceLabels_nonempty hP _ H
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  obtain ⟨v, hv, hvT⟩ := hZ _ (hH c hc ⟨c, i⟩ rfl)
  have hcU := CV.pieceLabels_subset hP _ H hc
  rw [CV.mem_U_iff] at hcU
  apply hcU.1
  rw [show c = v.1 from congrArg Sigma.fst (Sum.inr_injective hv)]
  exact Finset.mem_union_right _ hvT

/-- **`esc_FullSplitData` from the residue**: SPLITB's two fields and `central_no_piece` proved; the remaining
five (`touching_iff`, `distinct`, `central_rot`, `outer_alternative`, `uniform`) as hypotheses. -/
theorem w3cb_fullSplitData_of_residue (hn : 3 ≤ n) (hG : CV.Generic P) (e f g : ZMod n)
    {Q : Finset (Crossing P)} (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (q₀ : GeoComponent hG.crossingGeometry Q)
    (A B C Z : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)) (Λ : ℕ) {s : SignType}
    (h : w3cb_SplitResidue hG.crossingGeometry e f g q₀ A B C Λ s)
    (hZ : ∀ m : Mark P, geoOwner hG.crossingGeometry (Q ∪ triangleCrossings P e f g) m = Z →
      ∃ v : Visit P, m = Sum.inr v ∧ v.1 ∈ triangleCrossings P e f g)
    (touching_iff : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry (Q ∪ triangleCrossings P e f g) e f g q ↔
      (q = A ∨ q = B ∨ q = C ∨ q = Z))
    (distinct : A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z)
    (central_rot : CV.carrierR hn hG hS Z = 1)
    (outer_alternative : CV.CarrierUniform hG.crossingGeometry Q q₀ →
      CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ A) ∧
      CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ B) ∧
      CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ C))
    (uniform : CV.CarrierUniform hG.crossingGeometry Q q₀ →
      (CV.carrierR hn hG hS A + CV.carrierR hn hG hS B + CV.carrierR hn hG hS C = CV.carrierR hn hG hQ q₀ + 1 ∧
        CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
          CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z =
          -CV.weight hG.crossingGeometry Q q₀) ∨
      (CV.carrierR hn hG hS A + CV.carrierR hn hG hS B + CV.carrierR hn hG hS C + 1 = CV.carrierR hn hG hQ q₀ ∧
        CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
          CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0)) :
    esc_FullSplitData hn hG e f g hQ hS q₀ A B C Z Λ :=
  w3cb_fullSplitData_of hn hG e f g hQ hS hef heg hfg q₀ A B C Z Λ
    (w3cb_splitGeometry_of_residue hG.crossingGeometry hef heg hfg (CV.geoIndependent_of_mem_Ind _ hS) h)
    touching_iff distinct (w3cb_central_no_piece hG.crossingGeometry hZ) central_rot outer_alternative uniform

/-! #### The event-level black box, minimal form -/

/-- **BLACK BOX (unit SPLITA): the core at every configuration of the extended interface** — same binders as
`w3bi_esc_outer` up to the two contact carriers. -/
def w3cb_split_core : Prop :=
  ∀ {n : ℕ} [NeZero n] (_hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (_hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (_hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ) (s : SignType),
        w3cb_SplitCore (geomAt E t' ht'.1) e f g q₀' A B C Λ s

/-! (W3C assembler) the event-level declarations `w3cb_split_core_data`, `w3cb_split_geometry_of_core`,
`w3cb_split_geometry_data` are declared after the OUTER residue `w3cx_outer_residue` (in `section W3CK_Outer`,
after KNOT's `w3ck_split_ident`), statements unchanged: the black box `w3cb_split_core_data` is there proved from
SPLITA's carriers and the residue (`w3cx_split_core_of_residue`). -/

end W3CB_SPLITB


/-! ## UNIT NONKINK (W3D, prefix `w3dk_`): the kink case of the 177 site handled by a flat subdivision of the
carrier polygon (W3D_NONKINK_REPORT.md).  Steps 1-5: a reparametrisation of an all-positive diagram induces a
record isomorphism; the oriented smoothing is natural in record isomorphisms; the flat subdivision of one edge of
a one-component positive diagram as an explicit reparametrisation; label bookkeeping on the subdivided diagram;
the site data and the non-kink condition on the subdivided diagram.  Steps 6-7: the reduced-value lemma at one
side (by cases: non-kink through the bigon, kink through the subdivision and the record-isomorphism chain), the
BigonData-free reduced-record identification, and the two-sided site Prop `w3dk_rii_value_sites`. -/


/-! # W3D NONKINK — step 1: a reparametrisation of an all-positive diagram induces a record isomorphism -/

section W3DK_Reparam

variable {D D' : Diagram} (r : ReparamData D D')

/-- every occurrence of `D` is carried by the reparametrisation to an occurrence of `D'` -/
theorem w3dk_reparam_exists_visit (v : D.Γ.Visit) :
    ∃ w : D'.Γ.Visit, D'.visitPt w = r.mapPt (D.visitPt v) := by
  rcases D.visit_eq_over_or_under v with h | h
  · obtain ⟨x', hx'⟩ := r.over_map v.1
    refine ⟨D'.overVisit x', ?_⟩
    rw [h]; exact hx'.symm
  · obtain ⟨x', hx'⟩ := r.over_map v.1
    refine ⟨D'.underVisit x', ?_⟩
    rw [h]; exact (usw_reparam_under r v.1 x' hx').symm

/-- the induced map of occurrences -/
noncomputable def w3dk_reparamVisit (v : D.Γ.Visit) : D'.Γ.Visit :=
  Classical.choose (w3dk_reparam_exists_visit r v)

theorem w3dk_reparamVisit_spec (v : D.Γ.Visit) :
    D'.visitPt (w3dk_reparamVisit r v) = r.mapPt (D.visitPt v) :=
  Classical.choose_spec (w3dk_reparam_exists_visit r v)

theorem w3dk_reparamVisit_injective : Function.Injective (w3dk_reparamVisit r) := by
  intro v w h
  apply D.visitPt_injective
  apply usw_mapPt_injective r
  rw [← w3dk_reparamVisit_spec r v, ← w3dk_reparamVisit_spec r w, h]

theorem w3dk_reparamVisit_over (x : D.Γ.Crossing) :
    ∃ x' : D'.Γ.Crossing, w3dk_reparamVisit r (D.overVisit x) = D'.overVisit x' := by
  obtain ⟨x', hx'⟩ := r.over_map x
  refine ⟨x', D'.visitPt_injective ?_⟩
  rw [w3dk_reparamVisit_spec]; exact hx'

theorem w3dk_reparamVisit_under (x : D.Γ.Crossing) (x' : D'.Γ.Crossing)
    (h : w3dk_reparamVisit r (D.overVisit x) = D'.overVisit x') :
    w3dk_reparamVisit r (D.underVisit x) = D'.underVisit x' := by
  apply D'.visitPt_injective
  rw [w3dk_reparamVisit_spec]
  apply usw_reparam_under r x x'
  rw [← w3dk_reparamVisit_spec, h]

theorem w3dk_reparamVisit_surjective : Function.Surjective (w3dk_reparamVisit r) := by
  intro w
  rcases D'.visit_eq_over_or_under w with h | h
  · obtain ⟨x, hx⟩ := r.over_surj w.1
    refine ⟨D.overVisit x, ?_⟩
    rw [h]; apply D'.visitPt_injective; rw [w3dk_reparamVisit_spec]; exact hx
  · obtain ⟨x, hx⟩ := r.over_surj w.1
    refine ⟨D.underVisit x, ?_⟩
    rw [h]
    apply w3dk_reparamVisit_under r x w.1
    apply D'.visitPt_injective; rw [w3dk_reparamVisit_spec]; exact hx

/-- the induced bijection of occurrences -/
noncomputable def w3dk_reparamVisitEquiv : D.Γ.Visit ≃ D'.Γ.Visit :=
  Equiv.ofBijective _ ⟨w3dk_reparamVisit_injective r, w3dk_reparamVisit_surjective r⟩

@[simp] theorem w3dk_reparamVisitEquiv_apply (v : D.Γ.Visit) :
    w3dk_reparamVisitEquiv r v = w3dk_reparamVisit r v := rfl

/-- the image occurrence sits at the same double point -/
theorem w3dk_reparamVisit_point (v : D.Γ.Visit) :
    D'.Γ.crossingPoint (w3dk_reparamVisit r v).1 = D.Γ.crossingPoint v.1 := by
  rw [← D'.eval_visitPt, w3dk_reparamVisit_spec, r.eval_mapPt, D.eval_visitPt]

theorem w3dk_reparamVisit_compOf (v : D.Γ.Visit) :
    D'.compOf (w3dk_reparamVisit r v) = r.e (D.compOf v) := by
  rw [D'.compOf_eq_visitPt_fst, w3dk_reparamVisit_spec]; rfl

theorem w3dk_reparamVisit_twin (v : D.Γ.Visit) :
    w3dk_reparamVisit r (D.twin v) = D'.twin (w3dk_reparamVisit r v) := by
  have hpt : D'.Γ.crossingPoint (w3dk_reparamVisit r (D.twin v)).1 =
      D'.Γ.crossingPoint (w3dk_reparamVisit r v).1 := by
    rw [w3dk_reparamVisit_point, w3dk_reparamVisit_point]; rfl
  have hc : (w3dk_reparamVisit r (D.twin v)).1 = (w3dk_reparamVisit r v).1 :=
    D'.generic.crossingPoint_injective hpt
  have hne : w3dk_reparamVisit r (D.twin v) ≠ w3dk_reparamVisit r v :=
    fun h => D.twin_ne v (w3dk_reparamVisit_injective r h)
  rcases D'.visit_eq_over_or_under (w3dk_reparamVisit r v) with hw | hw <;>
    rcases D'.visit_eq_over_or_under (w3dk_reparamVisit r (D.twin v)) with hw' | hw'
  · exfalso; apply hne; rw [hw', hw, hc]
  · rw [hw', hc]; conv_rhs => rw [hw]
    rw [D'.twin_overVisit]
  · rw [hw', hc]; conv_rhs => rw [hw]
    rw [D'.twin_underVisit]
  · exfalso; apply hne; rw [hw', hw, hc]

theorem w3dk_reparamVisit_overBit (v : D.Γ.Visit) :
    D'.overBit (w3dk_reparamVisit r v) = D.overBit v := by
  rcases D.visit_eq_over_or_under v with h | h
  · obtain ⟨x', hx'⟩ := w3dk_reparamVisit_over r v.1
    rw [h, hx', D'.overBit_overVisit, D.overBit_overVisit]
  · obtain ⟨x', hx'⟩ := w3dk_reparamVisit_over r v.1
    rw [h, w3dk_reparamVisit_under r v.1 x' hx', D'.overBit_underVisit, D.overBit_underVisit]

theorem w3dk_cycBetween_asymm {a b c : ℝ} (h : cycBetween a b c) : ¬ cycBetween a c b := by
  unfold cycBetween at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rintro (⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩) <;> linarith

theorem w3dk_cycBetween_total {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cycBetween a b c ∨ cycBetween a c b := by
  unfold cycBetween
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · exact absurd h2 hbc
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · exact Or.inr (Or.inl ⟨h3, h2⟩)
      · exact absurd h3 hac
      · exact Or.inl (Or.inr (Or.inr ⟨h3, h1⟩))
  · exact absurd h1 hab
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h3⟩))
      · exact absurd h3 hac
      · exact Or.inl (Or.inr (Or.inl ⟨h2, h3⟩))
    · exact absurd h2 hbc
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))

/-- the circle maps of a reparametrisation preserve (and reflect) the strict cyclic order of keys -/
theorem w3dk_reparam_key_between (i : Fin D.Γ.c) (p q s : TraversalPoint (D.Γ.comp i).k) :
    cycBetween (traversalKey (r.φ i p)) (traversalKey (r.φ i q)) (traversalKey (r.φ i s)) ↔
      cycBetween (traversalKey p) (traversalKey q) (traversalKey s) := by
  constructor
  · intro h
    have hpq : traversalKey p ≠ traversalKey q := fun e => by
      have := traversalKey_injective e; subst this; exact not_cycBetween_self_left _ _ h
    have hqs : traversalKey q ≠ traversalKey s := fun e => by
      have := traversalKey_injective e; subst this; exact not_cycBetween_self_mid _ _ h
    have hps : traversalKey p ≠ traversalKey s := fun e => by
      have := traversalKey_injective e; subst this; exact not_cycBetween_self_right _ _ h
    rcases w3dk_cycBetween_total hpq hqs hps with h' | h'
    · exact h'
    · exfalso
      exact w3dk_cycBetween_asymm h ((traversalBetween_iff_cycBetween _ _ _).mp
        (r.between i p s q ((traversalBetween_iff_cycBetween _ _ _).mpr h')))
  · intro h
    exact (traversalBetween_iff_cycBetween _ _ _).mp
      (r.between i p q s ((traversalBetween_iff_cycBetween _ _ _).mpr h))

theorem w3dk_reparamVisit_between (v w u : D.Γ.Visit) (hw : D.compOf w = D.compOf v)
    (hu : D.compOf u = D.compOf v) :
    D'.VisitBetween (w3dk_reparamVisit r v) (w3dk_reparamVisit r w) (w3dk_reparamVisit r u) ↔
      D.VisitBetween v w u := by
  rw [D'.visitBetween_iff, D.visitBetween_iff, w3dk_reparamVisit_spec, w3dk_reparamVisit_spec,
    w3dk_reparamVisit_spec]
  rw [D.compOf_eq_visitPt_fst, D.compOf_eq_visitPt_fst] at hw hu
  obtain ⟨⟨i, p⟩, hv⟩ : ∃ pv, D.visitPt v = pv := ⟨_, rfl⟩
  obtain ⟨⟨j, q⟩, hwp⟩ : ∃ pw, D.visitPt w = pw := ⟨_, rfl⟩
  obtain ⟨⟨l, s⟩, hup⟩ : ∃ pu, D.visitPt u = pu := ⟨_, rfl⟩
  rw [hv, hwp] at hw
  rw [hv, hup] at hu
  change j = i at hw
  change l = i at hu
  subst j
  subst l
  rw [hv, hwp, hup]
  exact w3dk_reparam_key_between r i p q s

/-- **A reparametrisation of an all-positive diagram induces a named record isomorphism**
(`e` the component relabelling, `Φ` the induced bijection of occurrences). -/
noncomputable def w3dk_recordIso_of_reparam (hpos : ∀ x, D.sign x = 1) (hpos' : ∀ x', D'.sign x' = 1) :
    RecordIso D.record D'.record where
  e := r.e
  Φ := w3dk_reparamVisitEquiv r
  comp_eq v := w3dk_reparamVisit_compOf r v
  succ_eq v := by
    show w3dk_reparamVisit r (D.visitSucc v) = D'.visitSucc (w3dk_reparamVisit r v)
    rw [D.visitSucc_apply, D'.visitSucc_apply]
    refine D.nextVisit_comm_of_visitBetween_iff (w3dk_reparamVisitEquiv r) ?_ ?_ v
    · intro v w
      show D'.compOf (w3dk_reparamVisit r v) = D'.compOf (w3dk_reparamVisit r w) ↔ _
      rw [w3dk_reparamVisit_compOf, w3dk_reparamVisit_compOf]
      exact r.e.injective.eq_iff
    · intro v w u hw hu
      exact w3dk_reparamVisit_between r v w u hw hu
  pair_eq v := w3dk_reparamVisit_twin r v
  bit_eq v := w3dk_reparamVisit_overBit r v
  sgn_eq v := by
    show D'.sign _ = D.sign _
    rw [hpos, hpos']

theorem w3dk_recordIso_of_reparam_Φ (hpos : ∀ x, D.sign x = 1) (hpos' : ∀ x', D'.sign x' = 1)
    (v : D.Γ.Visit) : (w3dk_recordIso_of_reparam r hpos hpos').Φ v = w3dk_reparamVisit r v := rfl

theorem w3dk_recordIso_of_reparam_point (hpos : ∀ x, D.sign x = 1) (hpos' : ∀ x', D'.sign x' = 1)
    (v : D.Γ.Visit) :
    D'.Γ.crossingPoint ((w3dk_recordIso_of_reparam r hpos hpos').Φ v).1 = D.Γ.crossingPoint v.1 :=
  w3dk_reparamVisit_point r v

end W3DK_Reparam




/-! # W3D NONKINK — step 2: a named record isomorphism carries the oriented smoothing at `x` to the
oriented smoothing at `Φ x` -/

section W3DK_SmoothIso

open Equiv

variable {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x : ρ.M)

theorem w3dk_iso_swap (v : ρ.M) :
    ι.Φ (swap x (ρ.pair x) v) = swap (ι.Φ x) (ρ'.pair (ι.Φ x)) (ι.Φ v) := by
  by_cases hx : v = x
  · subst hx; rw [swap_apply_left, swap_apply_left, ι.pair_eq]
  · by_cases hp : v = ρ.pair x
    · subst hp; rw [swap_apply_right, ι.pair_eq, swap_apply_right]
    · rw [swap_apply_of_ne_of_ne hx hp, swap_apply_of_ne_of_ne (ι.Φ.injective.ne hx)
        (by rw [← ι.pair_eq]; exact ι.Φ.injective.ne hp)]

/-- the reconnected successor is natural -/
theorem w3dk_iso_reconnect (v : ρ.M) :
    ι.Φ (ρ.reconnect x v) = ρ'.reconnect (ι.Φ x) (ι.Φ v) := by
  unfold Record.reconnect
  rw [Perm.mul_apply, Perm.mul_apply, ι.succ_eq, w3dk_iso_swap]

theorem w3dk_iso_reconnect_pow (n : ℕ) (v : ρ.M) :
    ι.Φ (((ρ.reconnect x) ^ n) v) = ((ρ'.reconnect (ι.Φ x)) ^ n) (ι.Φ v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, w3dk_iso_reconnect, ih, pow_succ', Perm.mul_apply]

theorem w3dk_iso_reconnect_sameCycle (v w : ρ.M) :
    (ρ'.reconnect (ι.Φ x)).SameCycle (ι.Φ v) (ι.Φ w) ↔ (ρ.reconnect x).SameCycle v w := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast]; exact ι.Φ.injective (by rw [w3dk_iso_reconnect_pow, hn])⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← w3dk_iso_reconnect_pow, hn]⟩

theorem w3dk_iso_smoothKeep (v : ρ.M) :
    ρ'.SmoothKeep (ι.Φ x) (ι.Φ v) ↔ ρ.SmoothKeep x v := by
  rw [Record.smoothKeep_iff, Record.smoothKeep_iff, ← ι.pair_eq, ι.Φ.injective.ne_iff,
    ι.Φ.injective.ne_iff]

theorem w3dk_iso_freeComp (c : ρ.comps) :
    (∀ v', ρ'.comp v' ≠ ι.e c) ↔ (∀ v, ρ.comp v ≠ c) := by
  constructor
  · intro h v hv
    apply h (ι.Φ v)
    rw [ι.comp_eq, hv]
  · intro h v' hv'
    apply h (ι.Φ.symm v')
    apply ι.e.injective
    rw [← ι.comp_eq, Equiv.apply_symm_apply, hv']

/-- **The oriented smoothing is natural in named record isomorphisms.** -/
noncomputable def w3dk_recordIso_smooth : RecordIso (ρ.smooth x) (ρ'.smooth (ι.Φ x)) where
  e := Equiv.sumCongr
    (Quotient.congr ι.Φ (fun a b => by
      show (ρ.reconnect x).SameCycle a b ↔ (ρ'.reconnect (ι.Φ x)).SameCycle (ι.Φ a) (ι.Φ b)
      exact (w3dk_iso_reconnect_sameCycle ι x a b).symm))
    (Equiv.subtypeEquiv ι.e (fun c => (w3dk_iso_freeComp ι c).symm))
  Φ := Equiv.subtypeEquiv ι.Φ (fun v => (w3dk_iso_smoothKeep ι x v).symm)
  comp_eq v := by
    rw [Record.smooth_comp, Record.smooth_comp]
    rfl
  succ_eq v := by
    apply Subtype.ext
    exact (firstReturn_map_val ι.Φ (ρ.reconnect x) (ρ'.reconnect (ι.Φ x)) (ρ.SmoothKeep x)
      (ρ'.SmoothKeep (ι.Φ x)) (w3dk_iso_reconnect ι x) (w3dk_iso_smoothKeep ι x) v).symm
  pair_eq v := Subtype.ext (ι.pair_eq v.1)
  bit_eq v := ι.bit_eq v.1
  sgn_eq v := ι.sgn_eq v.1

@[simp] theorem w3dk_recordIso_smooth_Φ_val (v : (ρ.smooth x).M) :
    ((w3dk_recordIso_smooth ι x).Φ v).1 = ι.Φ v.1 := rfl

/-- the same, landing on a named occurrence `x'` with `ι.Φ x = x'` -/
noncomputable def w3dk_recordIso_smooth' (x' : ρ'.M) (h : ι.Φ x = x') :
    RecordIso (ρ.smooth x) (ρ'.smooth x') :=
  h ▸ w3dk_recordIso_smooth ι x

theorem w3dk_recordIso_smooth'_Φ_val (x' : ρ'.M) (h : ι.Φ x = x') (v : (ρ.smooth x).M) :
    ((w3dk_recordIso_smooth' ι x x' h).Φ v).1 = ι.Φ v.1 := by
  subst h; rfl

end W3DK_SmoothIso




/-! # W3D NONKINK — step 3: the flat subdivision of one edge of a one-component positive diagram,
as an explicit reparametrisation (shift the labels so that the edge becomes the closing edge, then
CS3's `appendVertex`) -/

section W3DK_Subdiv

/-- shifting the labels preserves remoteness -/
theorem w3dk_remote_sub {k : ℕ} (a i j : ZMod k) : remote (i - a) (j - a) ↔ remote i j := by
  unfold remote adjacent
  rw [sub_sub_sub_cancel_right]

/-- **The off-edge parameter exists**: a point of the open edge `b` lying on no other closed edge
(the bad parameters form a finite union of subsingletons). -/
theorem w3dk_exists_off (C : PolyComp) (hX : (Shadow.single C).Generic) (b : ZMod C.k) :
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧ ∀ e : ZMod C.k, e ≠ b → edgePoint C.P b u ∉ edgeSegment C.P e := by
  have hreg : Regular C.P := hX.regular 0
  have hE : ∀ i, edge C.P i ≠ 0 := fun i => ((regular_iff_edges C.P).mp hreg i).1
  let S : ZMod C.k → Set ℝ := fun e => {u | 0 < u ∧ u < 1 ∧ edgePoint C.P b u ∈ edgeSegment C.P e}
  have hS : ∀ e, e ≠ b → (S e).Subsingleton := by
    intro e he u₁ hu₁ u₂ hu₂
    obtain ⟨h10, h11, t₁, ht₁0, ht₁1, ht₁⟩ := hu₁
    obtain ⟨h20, h21, t₂, ht₂0, ht₂1, ht₂⟩ := hu₂
    by_cases hadj : adjacent b e
    · exfalso
      rcases hadj with h | h | h
      · -- e = b - 1: the common point is the vertex `P b = edgePoint P b 0`
        have he' : b = e + 1 := by linear_combination -h
        have hx1 : edgePoint C.P b u₁ ∈ edgeSegment C.P e := ⟨t₁, ht₁0, ht₁1, ht₁⟩
        have hx2 : edgePoint C.P b u₁ ∈ edgeSegment C.P (e + 1) := by
          rw [← he']; exact ⟨u₁, h10.le, h11.le, rfl⟩
        have := regular_adjacent_meet hreg e hx1 hx2
        rw [← he', ← edgePoint_zero C.P b] at this
        have := edgePoint_injective (hE b) this
        linarith
      · exact he (by linear_combination h)
      · -- e = b + 1: the common point is the vertex `P (b+1) = edgePoint P b 1`
        have he' : e = b + 1 := by linear_combination h
        have hx1 : edgePoint C.P b u₁ ∈ edgeSegment C.P b := ⟨u₁, h10.le, h11.le, rfl⟩
        have hx2 : edgePoint C.P b u₁ ∈ edgeSegment C.P (b + 1) := by
          rw [← he']; exact ⟨t₁, ht₁0, ht₁1, ht₁⟩
        have := regular_adjacent_meet hreg b hx1 hx2
        rw [← edgePoint_one C.P b] at this
        have := edgePoint_injective (hE b) this
        linarith
    · -- remote edges: transverse, hence they meet in at most one point
      have hna : ¬ (Shadow.single C).Adjacent ⟨0, b⟩ ⟨0, e⟩ := fun h =>
        hadj ((Shadow.single_adjacent_iff C _ _).mp h)
      have hne : ((Shadow.single C).seg ⟨0, b⟩ ∩ (Shadow.single C).seg ⟨0, e⟩).Nonempty :=
        ⟨edgePoint C.P b u₁, ⟨u₁, h10.le, h11.le, rfl⟩, ⟨t₁, ht₁0, ht₁1, ht₁⟩⟩
      have hd : det (edge C.P b) (edge C.P e) ≠ 0 := hX.transverse _ _ hna hne
      have h1 : C.P b + u₁ • edge C.P b = C.P e + t₁ • edge C.P e := ht₁
      have h2 : C.P b + u₂ • edge C.P b = C.P e + t₂ • edge C.P e := ht₂
      exact (intersection_parameters_unique hd h1 h2).1
  have hB : (⋃ e ∈ {e : ZMod C.k | e ≠ b}, S e).Finite :=
    Set.Finite.biUnion (Set.toFinite _) (fun e he => (hS e he).finite)
  obtain ⟨u, hu, hnot⟩ := (Set.Ioo_infinite (zero_lt_one' ℝ)).exists_notMem_finset hB.toFinset
  refine ⟨u, hu.1, hu.2, fun e he hmem => hnot ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_iUnion₂]
  exact ⟨e, he, hu.1, hu.2, hmem⟩

/-- the subdivided polygon: shift the labels by `b₀ + 1` (so that the edge `b₀` becomes the closing
edge `-1`), then append the vertex at parameter `u` of the closing edge -/
noncomputable def w3dk_subdivPoly (C : PolyComp) (b₀ : ZMod C.k) (u : ℝ) : PolyComp :=
  ⟨C.k + 1, Nat.le_succ_of_le C.hk, appendVertex (shift (b₀ + 1) C.P) u⟩

theorem w3dk_subdivPoly_k (C : PolyComp) (b₀ : ZMod C.k) (u : ℝ) :
    (w3dk_subdivPoly C b₀ u).k = C.k + 1 := rfl

theorem w3dk_subdivPoly_P (C : PolyComp) (b₀ : ZMod C.k) (u : ℝ) :
    (w3dk_subdivPoly C b₀ u).P = appendVertex (shift (b₀ + 1) C.P) u := rfl

theorem w3dk_shift_generic (C : PolyComp) (hX : (Shadow.single C).Generic) (a : ZMod C.k) :
    (Shadow.single ⟨C.k, C.hk, shift a C.P⟩).Generic :=
  single_generic_shift C.hk C.P a hX

/-- **The subdivided polygon is generic** (CS3 `single_generic_appendVertex` after the shift). -/
theorem w3dk_subdivPoly_generic (C : PolyComp) (hX : (Shadow.single C).Generic) (b₀ : ZMod C.k)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hoff : ∀ e : ZMod C.k, e ≠ b₀ → edgePoint C.P b₀ u ∉ edgeSegment C.P e) :
    (Shadow.single (w3dk_subdivPoly C b₀ u)).Generic := by
  show (Shadow.single ⟨C.k + 1, Nat.le_succ_of_le C.hk, appendVertex (shift (b₀ + 1) C.P) u⟩).Generic
  apply single_generic_appendVertex C.hk (shift (b₀ + 1) C.P) hu0 hu1 (w3dk_shift_generic C hX (b₀ + 1))
  intro e he
  rw [edgePoint_shift, edgeSegment_shift]
  have h1 : (-1 : ZMod C.k) + (b₀ + 1) = b₀ := by ring
  rw [h1]
  apply hoff
  intro h
  apply he
  linear_combination h

/-- the circle map of the subdivision: shift, then CS3's `subdivPt` -/
noncomputable def w3dk_subdivMap (C : PolyComp) (b₀ : ZMod C.k) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    TraversalPoint C.k ≃ TraversalPoint (C.k + 1) :=
  (traversalShiftEquiv (b₀ + 1)).trans (Equiv.ofBijective _ (subdivPt_bijective hu0 hu1))

theorem w3dk_subdivMap_apply (C : PolyComp) (b₀ : ZMod C.k) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (p : TraversalPoint C.k) :
    w3dk_subdivMap C b₀ hu0 hu1 p = subdivPt hu0 hu1 (traversalShift (b₀ + 1) p) := rfl

theorem w3dk_subdivMap_eval (C : PolyComp) (b₀ : ZMod C.k) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (p : TraversalPoint C.k) :
    traversalEvaluation (w3dk_subdivPoly C b₀ u).P (w3dk_subdivMap C b₀ hu0 hu1 p) =
      traversalEvaluation C.P p := by
  show traversalEvaluation (appendVertex (shift (b₀ + 1) C.P) u) (subdivPt hu0 hu1 (traversalShift (b₀ + 1) p)) = _
  rw [traversalEvaluation_subdivPt, traversalEvaluation_shift]

theorem w3dk_subdivMap_between (C : PolyComp) (b₀ : ZMod C.k) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (p q r : TraversalPoint C.k) (h : traversalBetween p q r) :
    traversalBetween (w3dk_subdivMap C b₀ hu0 hu1 p) (w3dk_subdivMap C b₀ hu0 hu1 q)
      (w3dk_subdivMap C b₀ hu0 hu1 r) := by
  rw [w3dk_subdivMap_apply, w3dk_subdivMap_apply, w3dk_subdivMap_apply]
  exact traversalBetween_subdivPt hu0 hu1 _ _ _ ((traversalBetween_shift _ p q r).mpr h)

theorem w3dk_subdivMap_remote (C : PolyComp) (b₀ : ZMod C.k) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {p q : TraversalPoint C.k} (h : remote p.1 q.1) :
    remote (w3dk_subdivMap C b₀ hu0 hu1 p).1 (w3dk_subdivMap C b₀ hu0 hu1 q).1 := by
  rw [w3dk_subdivMap_apply, w3dk_subdivMap_apply]
  exact remote_subdivPt_fst hu0 hu1 C.hk ((w3dk_remote_sub (b₀ + 1) p.1 q.1).mpr h)

theorem w3dk_subdivMap_det (C : PolyComp) (b₀ : ZMod C.k) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (p q : TraversalPoint C.k) :
    0 < det (edge (w3dk_subdivPoly C b₀ u).P (w3dk_subdivMap C b₀ hu0 hu1 p).1)
        (edge (w3dk_subdivPoly C b₀ u).P (w3dk_subdivMap C b₀ hu0 hu1 q).1) ↔
      0 < det (edge C.P p.1) (edge C.P q.1) := by
  show 0 < det (edge (appendVertex (shift (b₀ + 1) C.P) u) (subdivPt hu0 hu1 (traversalShift (b₀ + 1) p)).1)
      (edge (appendVertex (shift (b₀ + 1) C.P) u) (subdivPt hu0 hu1 (traversalShift (b₀ + 1) q)).1) ↔ _
  rw [det_edge_subdivPt_pos_iff, edge_shift, edge_shift]
  show 0 < det (edge C.P (p.1 - (b₀ + 1) + (b₀ + 1))) (edge C.P (q.1 - (b₀ + 1) + (b₀ + 1))) ↔ _
  rw [sub_add_cancel, sub_add_cancel]

theorem w3dk_subdivMap_remote_back (C : PolyComp) (hX : (Shadow.single C).Generic) (b₀ : ZMod C.k)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hX₂ : (Shadow.single (w3dk_subdivPoly C b₀ u)).Generic)
    {p q : TraversalPoint C.k} (hz : traversalEvaluation C.P p = traversalEvaluation C.P q)
    (h : remote (w3dk_subdivMap C b₀ hu0 hu1 p).1 (w3dk_subdivMap C b₀ hu0 hu1 q).1) :
    remote p.1 q.1 := by
  rw [w3dk_subdivMap_apply, w3dk_subdivMap_apply] at h
  have hz' : traversalEvaluation (shift (b₀ + 1) C.P) (traversalShift (b₀ + 1) p) =
      traversalEvaluation (shift (b₀ + 1) C.P) (traversalShift (b₀ + 1) q) := by
    rw [traversalEvaluation_shift, traversalEvaluation_shift]; exact hz
  have := remote_of_remote_subdivPt hu0 hu1 C.hk (shift (b₀ + 1) C.P) (w3dk_shift_generic C hX _) hX₂
    hz' h
  exact (w3dk_remote_sub (b₀ + 1) p.1 q.1).mp this

/-- the two occurrences of a crossing of a one-component positive diagram, as traversal points of the
polygon: same plane point, remote labels, positive determinant -/
theorem w3dk_single_crossing_pts (C : PolyComp) (hX : (Shadow.single C).Generic)
    (x : ((Shadow.single C).positiveDiagram hX).Γ.Crossing) :
    ∃ p q : TraversalPoint C.k,
      ((Shadow.single C).positiveDiagram hX).visitPt (((Shadow.single C).positiveDiagram hX).overVisit x) =
        (⟨(0 : Fin 1), p⟩ : (Shadow.single C).Pt) ∧
      ((Shadow.single C).positiveDiagram hX).visitPt (((Shadow.single C).positiveDiagram hX).underVisit x) =
        (⟨(0 : Fin 1), q⟩ : (Shadow.single C).Pt) ∧
      traversalEvaluation C.P p = traversalEvaluation C.P q ∧ remote p.1 q.1 ∧
      0 < det (edge C.P p.1) (edge C.P q.1) := by
  refine ⟨(((Shadow.single C).positiveDiagram hX).visitPt
      (((Shadow.single C).positiveDiagram hX).overVisit x)).2,
    (((Shadow.single C).positiveDiagram hX).visitPt
      (((Shadow.single C).positiveDiagram hX).underVisit x)).2,
    Shadow.single_pt_ext _ rfl, Shadow.single_pt_ext _ rfl, ?_, ?_, ?_⟩
  · have h1 := ((Shadow.single C).positiveDiagram hX).eval_visitPt
      (((Shadow.single C).positiveDiagram hX).overVisit x)
    have h2 := ((Shadow.single C).positiveDiagram hX).eval_visitPt
      (((Shadow.single C).positiveDiagram hX).underVisit x)
    exact h1.trans h2.symm
  · exact fun h => ((Shadow.single C).positiveDiagram hX).not_adjacent_over_under x
      ((Shadow.single_adjacent_iff C _ _).mpr h)
  · exact (Shadow.single C).positiveDiagram_det_pos hX x

/-- **The flat subdivision is a reparametrisation of the positive diagram**, with the explicit circle
map `w3dk_subdivMap` (`e = id`; CS3's `reparam_positiveDiagram_single_appendVertex` after the shift,
with the over occurrences located by `exists_crossing_overVisit_eq` on both sides). -/
noncomputable def w3dk_subdivReparam (C : PolyComp) (hX : (Shadow.single C).Generic) (b₀ : ZMod C.k)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hX₂ : (Shadow.single (w3dk_subdivPoly C b₀ u)).Generic) :
    ReparamData ((Shadow.single C).positiveDiagram hX)
      ((Shadow.single (w3dk_subdivPoly C b₀ u)).positiveDiagram hX₂) where
  e := Equiv.refl _
  φ := fun _ => w3dk_subdivMap C b₀ hu0 hu1
  between := fun _ p q r h => w3dk_subdivMap_between C b₀ hu0 hu1 p q r h
  eval_eq := fun _ p => w3dk_subdivMap_eval C b₀ hu0 hu1 p
  over_map := by
    intro x
    obtain ⟨p, q, hp, hq, hz₀, hr₀, hdet₀⟩ := w3dk_single_crossing_pts C hX x
    have hz : traversalEvaluation (w3dk_subdivPoly C b₀ u).P (w3dk_subdivMap C b₀ hu0 hu1 p) =
        traversalEvaluation (w3dk_subdivPoly C b₀ u).P (w3dk_subdivMap C b₀ hu0 hu1 q) := by
      rw [w3dk_subdivMap_eval, w3dk_subdivMap_eval]; exact hz₀
    obtain ⟨x', hx'⟩ := exists_crossing_overVisit_eq (w3dk_subdivPoly C b₀ u) hX₂ _ _ hz
      (w3dk_subdivMap_remote C b₀ hu0 hu1 hr₀) ((w3dk_subdivMap_det C b₀ hu0 hu1 p q).mpr hdet₀)
    refine ⟨x', ?_⟩
    rw [hp, hx']
    exact Shadow.single_pt_ext _ rfl
  over_surj := by
    intro x'
    obtain ⟨p', q', hp', hq', hz', hr', hdet'⟩ := w3dk_single_crossing_pts (w3dk_subdivPoly C b₀ u) hX₂ x'
    obtain ⟨p, hp⟩ : ∃ p : TraversalPoint C.k, w3dk_subdivMap C b₀ hu0 hu1 p = p' :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    obtain ⟨q, hq⟩ : ∃ q : TraversalPoint C.k, w3dk_subdivMap C b₀ hu0 hu1 q = q' :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    rw [← hp, ← hq] at hz' hr' hdet'
    have hz₀ : traversalEvaluation C.P p = traversalEvaluation C.P q := by
      rw [w3dk_subdivMap_eval, w3dk_subdivMap_eval] at hz'; exact hz'
    have hr₀ : remote p.1 q.1 := w3dk_subdivMap_remote_back C hX b₀ hu0 hu1 hX₂ hz₀ hr'
    have hdet₀ : 0 < det (edge C.P p.1) (edge C.P q.1) := (w3dk_subdivMap_det C b₀ hu0 hu1 p q).mp hdet'
    obtain ⟨x, hx⟩ := exists_crossing_overVisit_eq C hX p q hz₀ hr₀ hdet₀
    refine ⟨x, ?_⟩
    rw [hx, hp']
    exact Shadow.single_pt_ext _ hp

end W3DK_Subdiv



/-! # W3D NONKINK — step 4: label bookkeeping on the subdivided diagram -/

section W3DK_Labels

variable (C : PolyComp) (hX : (Shadow.single C).Generic) (b₀ : ZMod C.k) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
  (hX₂ : (Shadow.single (w3dk_subdivPoly C b₀ u)).Generic)

/-- the one-component positive diagram of `C` -/
noncomputable abbrev w3dk_D₀ : Diagram := (Shadow.single C).positiveDiagram hX

/-- the positive diagram of the subdivided polygon -/
noncomputable abbrev w3dk_D₂ : Diagram := (Shadow.single (w3dk_subdivPoly C b₀ u)).positiveDiagram hX₂

/-- the label map of the subdivision on the labels other than the subdivided edge `b₀` -/
def w3dk_lab (b₀ l : ZMod C.k) : ZMod (C.k + 1) := insertIndex (l - (b₀ + 1))

theorem w3dk_lab_injective : Function.Injective (w3dk_lab C b₀) := by
  intro l l' h
  have := insertIndex_injective h
  exact sub_left_injective this

theorem w3dk_lab_ne_last {l : ZMod C.k} (hl : l ≠ b₀) : w3dk_lab C b₀ l ≠ insertIndex (-1 : ZMod C.k) := by
  intro h
  have := insertIndex_injective h
  apply hl
  linear_combination this

theorem w3dk_lab_ne_inserted (l : ZMod C.k) : w3dk_lab C b₀ l ≠ insertedIndex C.k :=
  insertIndex_ne_inserted _

theorem w3dk_sub_ne_neg_one {l : ZMod C.k} (hl : l ≠ b₀) : l - (b₀ + 1) ≠ -1 := by
  intro h; apply hl; linear_combination h

/-- the segment of an old label is unchanged -/
theorem w3dk_seg_lab {l : ZMod C.k} (hl : l ≠ b₀) :
    edgeSegment (w3dk_subdivPoly C b₀ u).P (w3dk_lab C b₀ l) = edgeSegment C.P l := by
  show edgeSegment (appendVertex (shift (b₀ + 1) C.P) u) (insertIndex (l - (b₀ + 1))) = _
  rw [edgeSegment_appendVertex_old _ _ (w3dk_sub_ne_neg_one C b₀ hl), edgeSegment_shift, sub_add_cancel]

/-- the direction of an old label is unchanged -/
theorem w3dk_edge_lab {l : ZMod C.k} (hl : l ≠ b₀) :
    edge (w3dk_subdivPoly C b₀ u).P (w3dk_lab C b₀ l) = edge C.P l := by
  show edge (appendVertex (shift (b₀ + 1) C.P) u) (insertIndex (l - (b₀ + 1))) = _
  rw [edge_appendVertex_old _ _ (w3dk_sub_ne_neg_one C b₀ hl), edge_shift, sub_add_cancel]

/-- the two halves of the subdivided edge lie in it -/
theorem w3dk_seg_last_subset (hu0 : 0 < u) (hu1 : u < 1) :
    edgeSegment (w3dk_subdivPoly C b₀ u).P (insertIndex (-1 : ZMod C.k)) ⊆ edgeSegment C.P b₀ := by
  show edgeSegment (appendVertex (shift (b₀ + 1) C.P) u) (insertIndex (-1 : ZMod C.k)) ⊆ _
  have h := edgeSegment_appendVertex_last_subset (shift (b₀ + 1) C.P) hu0.le hu1.le
  rw [edgeSegment_shift, show (-1 : ZMod C.k) + (b₀ + 1) = b₀ by ring] at h
  exact h

theorem w3dk_seg_inserted_subset (hu0 : 0 < u) (hu1 : u < 1) :
    edgeSegment (w3dk_subdivPoly C b₀ u).P (insertedIndex C.k) ⊆ edgeSegment C.P b₀ := by
  show edgeSegment (appendVertex (shift (b₀ + 1) C.P) u) (insertedIndex C.k) ⊆ _
  have h := edgeSegment_appendVertex_new_subset (shift (b₀ + 1) C.P) hu0.le hu1.le
  rw [edgeSegment_shift, show (-1 : ZMod C.k) + (b₀ + 1) = b₀ by ring] at h
  exact h

/-- the vertices of the subdivided polygon: the old vertices and the new point on the edge `b₀` -/
theorem w3dk_vertex_old (i : ZMod C.k) :
    (w3dk_subdivPoly C b₀ u).P (insertIndex i) = C.P (i + (b₀ + 1)) := by
  show appendVertex (shift (b₀ + 1) C.P) u (insertIndex i) = _
  rw [appendVertex_old]; rfl

theorem w3dk_vertex_new_mem (hu0 : 0 < u) (hu1 : u < 1) :
    (w3dk_subdivPoly C b₀ u).P (insertedIndex C.k) ∈ edgeSegment C.P b₀ := by
  show appendVertex (shift (b₀ + 1) C.P) u (insertedIndex C.k) ∈ _
  rw [appendVertex_new, edgePoint_shift, show (-1 : ZMod C.k) + (b₀ + 1) = b₀ by ring]
  exact ⟨u, hu0.le, hu1.le, rfl⟩

/-- every label of the subdivided polygon is an old label (`w3dk_lab`), the first half or the second
half of the subdivided edge -/
theorem w3dk_label_cases (m : ZMod (C.k + 1)) :
    (∃ l : ZMod C.k, l ≠ b₀ ∧ m = w3dk_lab C b₀ l) ∨ m = insertIndex (-1 : ZMod C.k) ∨
      m = insertedIndex C.k := by
  rcases insertion_indices_exhaust m with h | ⟨i, hi⟩
  · exact Or.inr (Or.inr h)
  · by_cases hi1 : i = -1
    · exact Or.inr (Or.inl (by rw [hi, hi1]))
    · refine Or.inl ⟨i + (b₀ + 1), ?_, ?_⟩
      · intro h; apply hi1; linear_combination h
      · rw [hi]; unfold w3dk_lab; rw [add_sub_cancel_right]

/-- the visit map of the subdivision reparametrisation -/
noncomputable abbrev w3dk_σ :
    (w3dk_D₀ C hX).Γ.Visit →
      (w3dk_D₂ C b₀ hX₂).Γ.Visit :=
  w3dk_reparamVisit (w3dk_subdivReparam C hX b₀ hu0 hu1 hX₂)

/-- the traversal point of an occurrence of the one-component diagram, as a clean pair -/
theorem w3dk_visitPt_eq (v : (w3dk_D₀ C hX).Γ.Visit) :
    ∃ p : TraversalPoint C.k,
      (w3dk_D₀ C hX).visitPt v = (⟨(0 : Fin 1), p⟩ : (Shadow.single C).Pt) ∧
      p.1 = v.2.val.2 ∧ p.2.val = (w3dk_D₀ C hX).crossingParam v.1 v.2.2 :=
  ⟨((w3dk_D₀ C hX).visitPt v).2, Shadow.single_pt_ext _ rfl, rfl, rfl⟩

/-- the traversal point of the image occurrence -/
theorem w3dk_σ_visitPt (v : (w3dk_D₀ C hX).Γ.Visit) (p : TraversalPoint C.k)
    (hp : (w3dk_D₀ C hX).visitPt v = (⟨(0 : Fin 1), p⟩ : (Shadow.single C).Pt)) :
    (w3dk_D₂ C b₀ hX₂).visitPt (w3dk_σ C hX b₀ hu0 hu1 hX₂ v) =
      (⟨(0 : Fin 1), w3dk_subdivMap C b₀ hu0 hu1 p⟩ : (Shadow.single (w3dk_subdivPoly C b₀ u)).Pt) := by
  rw [w3dk_reparamVisit_spec, hp]
  exact Shadow.single_pt_ext _ rfl

/-- **the strand of the image occurrence**: an old label goes to `w3dk_lab` of itself -/
theorem w3dk_σ_strand (v : (w3dk_D₀ C hX).Γ.Visit) (hv : v.2.val.2 ≠ b₀) :
    (w3dk_σ C hX b₀ hu0 hu1 hX₂ v).2.val = ⟨(0 : Fin 1), w3dk_lab C b₀ v.2.val.2⟩ := by
  obtain ⟨p, hp, hp1, -⟩ := w3dk_visitPt_eq C hX v
  have h := w3dk_σ_visitPt C hX b₀ hu0 hu1 hX₂ v p hp
  have h2 := eq_of_heq (Sigma.ext_iff.mp h).2
  have h3 := congrArg Prod.fst h2
  have hp1' : p.1 - (b₀ + 1) ≠ -1 := by rw [hp1]; exact w3dk_sub_ne_neg_one C b₀ hv
  rw [w3dk_subdivMap_apply, subdivPt_fst_of_ne hu0 hu1 hp1', Diagram.visitPt_edge] at h3
  rw [← Shadow.single_strand_eta _ (w3dk_σ C hX b₀ hu0 hu1 hX₂ v).2.val, h3]
  show (⟨0, insertIndex (p.1 - (b₀ + 1))⟩ : (Shadow.single (w3dk_subdivPoly C b₀ u)).Strand) = _
  rw [hp1]; rfl

/-- **the crossing parameter of the image occurrence is unchanged** (old labels) -/
theorem w3dk_σ_param (v : (w3dk_D₀ C hX).Γ.Visit) (hv : v.2.val.2 ≠ b₀) :
    (w3dk_D₂ C b₀ hX₂).crossingParam
        (w3dk_σ C hX b₀ hu0 hu1 hX₂ v).1 (w3dk_σ C hX b₀ hu0 hu1 hX₂ v).2.2 =
      (w3dk_D₀ C hX).crossingParam v.1 v.2.2 := by
  obtain ⟨p, hp, hp1, hp2⟩ := w3dk_visitPt_eq C hX v
  have h := w3dk_σ_visitPt C hX b₀ hu0 hu1 hX₂ v p hp
  have h2 := eq_of_heq (Sigma.ext_iff.mp h).2
  have h4 := congrArg (fun q : TraversalPoint (C.k + 1) => q.2.val) h2
  have hp1' : p.1 - (b₀ + 1) ≠ -1 := by rw [hp1]; exact w3dk_sub_ne_neg_one C b₀ hv
  simp only at h4
  rw [w3dk_subdivMap_apply, subdivPt_snd_of_ne hu0 hu1 hp1', Diagram.visitPt_param] at h4
  rw [h4]
  exact hp2

/-- the image crossing -/
noncomputable abbrev w3dk_χ (x : (w3dk_D₀ C hX).Γ.Crossing) :
    (w3dk_D₂ C b₀ hX₂).Γ.Crossing :=
  (w3dk_σ C hX b₀ hu0 hu1 hX₂ ((w3dk_D₀ C hX).overVisit x)).1

theorem w3dk_σ_overVisit (x : (w3dk_D₀ C hX).Γ.Crossing) :
    w3dk_σ C hX b₀ hu0 hu1 hX₂ ((w3dk_D₀ C hX).overVisit x) =
      (w3dk_D₂ C b₀ hX₂).overVisit (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) := by
  obtain ⟨x', hx'⟩ := w3dk_reparamVisit_over (w3dk_subdivReparam C hX b₀ hu0 hu1 hX₂) x
  have : w3dk_χ C hX b₀ hu0 hu1 hX₂ x = x' := congrArg Sigma.fst hx'
  exact hx'.trans (congrArg _ this.symm)

theorem w3dk_σ_underVisit (x : (w3dk_D₀ C hX).Γ.Crossing) :
    w3dk_σ C hX b₀ hu0 hu1 hX₂ ((w3dk_D₀ C hX).underVisit x) =
      (w3dk_D₂ C b₀ hX₂).underVisit (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) :=
  w3dk_reparamVisit_under _ x _ (w3dk_σ_overVisit C hX b₀ hu0 hu1 hX₂ x)

theorem w3dk_χ_point (x : (w3dk_D₀ C hX).Γ.Crossing) :
    (w3dk_D₂ C b₀ hX₂).Γ.crossingPoint (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) =
      (w3dk_D₀ C hX).Γ.crossingPoint x :=
  w3dk_reparamVisit_point _ _

theorem w3dk_χ_overStrand (x : (w3dk_D₀ C hX).Γ.Crossing)
    (hx : ((w3dk_D₀ C hX).overStrand x).2 ≠ b₀) :
    (w3dk_D₂ C b₀ hX₂).overStrand (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) =
      ⟨(0 : Fin 1), w3dk_lab C b₀ ((w3dk_D₀ C hX).overStrand x).2⟩ := by
  have h := w3dk_σ_strand C hX b₀ hu0 hu1 hX₂ ((w3dk_D₀ C hX).overVisit x) hx
  rw [w3dk_σ_overVisit] at h
  exact h

theorem w3dk_χ_underStrand (x : (w3dk_D₀ C hX).Γ.Crossing)
    (hx : ((w3dk_D₀ C hX).underStrand x).2 ≠ b₀) :
    (w3dk_D₂ C b₀ hX₂).underStrand (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) =
      ⟨(0 : Fin 1), w3dk_lab C b₀ ((w3dk_D₀ C hX).underStrand x).2⟩ := by
  have h := w3dk_σ_strand C hX b₀ hu0 hu1 hX₂ ((w3dk_D₀ C hX).underVisit x) hx
  rw [w3dk_σ_underVisit] at h
  exact h

/-- the image of a crossing is injective (same double point) -/
theorem w3dk_χ_injective : Function.Injective (w3dk_χ C hX b₀ hu0 hu1 hX₂) := by
  intro x y h
  have h1 := w3dk_χ_point C hX b₀ hu0 hu1 hX₂ x
  have h2 := w3dk_χ_point C hX b₀ hu0 hu1 hX₂ y
  exact hX.crossingPoint_injective (h1.symm.trans ((congrArg _ h).trans h2))

/-- the record isomorphism of the subdivision -/
noncomputable abbrev w3dk_ι :
    RecordIso (w3dk_D₀ C hX).record
      (w3dk_D₂ C b₀ hX₂).record :=
  w3dk_recordIso_of_reparam (w3dk_subdivReparam C hX b₀ hu0 hu1 hX₂)
    (fun x => (Shadow.single C).positiveDiagram_sign hX x)
    (fun x => (Shadow.single _).positiveDiagram_sign hX₂ x)

theorem w3dk_ι_Φ (v : (w3dk_D₀ C hX).Γ.Visit) :
    (w3dk_ι C hX b₀ hu0 hu1 hX₂).Φ v = w3dk_σ C hX b₀ hu0 hu1 hX₂ v := rfl

end W3DK_Labels


/-! # W3D NONKINK — step 5a: the label arithmetic of the kink, `k ≠ 4`, and small helpers -/

section W3DK_Arith

/-- the two half-labels of the kink after the subdivision: `insertIndex 0 = 0` and `insertIndex (-2)`
are no longer at cyclic distance two, in either order (`k ≠ 4`) -/
theorem w3dk_lab_kink_arith {k : ℕ} [NeZero k] (hk : 3 ≤ k) (hk4 : k ≠ 4) :
    ((0 : ZMod (k + 1)) - 1 ≠ insertIndex (-2 : ZMod k) + 1) ∧
      (insertIndex (-2 : ZMod k) - 1 ≠ (0 : ZMod (k + 1)) + 1) := by
  have hval : (-2 : ZMod k).val = k - 2 := by
    have : (-2 : ZMod k) = ((k - 2 : ℕ) : ZMod k) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]; norm_num
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h2 : (insertIndex (-2 : ZMod k)).val = k - 2 := by
    rw [insertIndex_val, hval]
  have : Fact (1 < k + 1) := ⟨by omega⟩
  constructor
  · intro h
    have := congrArg ZMod.val h
    rw [zero_sub, ZMod.val_neg_one, ZMod.val_add, h2, ZMod.val_one, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro h
    have := congrArg ZMod.val h
    rw [zero_add, ZMod.val_one, ZMod.val_sub (by rw [h2, ZMod.val_one]; omega), h2, ZMod.val_one] at this
    omega

/-- **`k ≠ 4` at a kink**: if `t = s ∓ 2` and a third label `g` is remote from both `s` and `t`, the
polygon has more than four edges. -/
theorem w3dk_ne_four {k : ℕ} [NeZero k] (s t g : ZMod k) (hst : t = s - 2 ∨ s = t - 2)
    (hsg : ¬ adjacent s g) (htg : ¬ adjacent t g) : k ≠ 4 := by
  intro hk4
  subst hk4
  have key : ∀ d : ZMod 4, (d ≠ -1 ∧ d ≠ 0 ∧ d ≠ 1) → (d + 2 ≠ -1 ∧ d + 2 ≠ 0 ∧ d + 2 ≠ 1) → False := by
    decide
  unfold adjacent at hsg htg
  push Not at hsg htg
  rcases hst with rfl | rfl
  · exact key (g - s) hsg (by
      refine ⟨?_, ?_, ?_⟩
      · intro h; apply htg.1; linear_combination h
      · intro h; apply htg.2.1; linear_combination h
      · intro h; apply htg.2.2; linear_combination h)
  · exact key (g - t) htg (by
      refine ⟨?_, ?_, ?_⟩
      · intro h; apply hsg.1; linear_combination h
      · intro h; apply hsg.2.1; linear_combination h
      · intro h; apply hsg.2.2; linear_combination h)

/-- adjacency of labels is symmetric -/
theorem w3dk_adjacent_symm {k : ℕ} (i j : ZMod k) (h : adjacent i j) : adjacent j i := by
  unfold adjacent at h ⊢
  rcases h with h | h | h
  · right; right; linear_combination -h
  · right; left; linear_combination -h
  · left; linear_combination -h

/-- two unordered pairs with distinct entries -/
theorem w3dk_pair_cases {α : Type*} [DecidableEq α] {a b s g : α} (hab : a ≠ b)
    (h : ({a, b} : Finset α) = {s, g}) : (a = s ∧ b = g) ∨ (a = g ∧ b = s) := by
  have ha : a ∈ ({s, g} : Finset α) := by rw [← h]; exact Finset.mem_insert_self _ _
  have hb : b ∈ ({s, g} : Finset α) := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hs : s ∈ ({a, b} : Finset α) := by rw [h]; exact Finset.mem_insert_self _ _
  have hg : g ∈ ({a, b} : Finset α) := by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hs hg
  rcases ha with ha | ha
  · left; refine ⟨ha, ?_⟩
    rcases hg with hg | hg
    · exfalso; rcases hb with hb | hb
      · exact hab (ha.trans hb.symm)
      · exact hab (hg.symm.trans hb.symm)
    · exact hg.symm
  · right; refine ⟨ha, ?_⟩
    rcases hs with hs | hs
    · exfalso; rcases hb with hb | hb
      · exact hab (hs.symm.trans hb.symm)
      · exact hab (ha.trans hb.symm)
    · exact hs.symm

/-- the crossing parameter through an occurrence with the given crossing and strand -/
theorem w3dk_crossingParam_congr (D : Diagram) (w : D.Γ.Visit) (c : D.Γ.Crossing) (st : D.Γ.Strand)
    (h1 : w.1 = c) (h2 : w.2.val = st) (hst : st ∈ c.val) :
    D.crossingParam c hst = D.crossingParam w.1 w.2.2 := by
  obtain ⟨c', ⟨st', hst'⟩⟩ := w
  simp only at h1 h2
  subst h1 h2
  rfl

/-- a strand of a one-component shadow is determined by its label -/
theorem w3dk_single_strand_ext {C : PolyComp} {s t : (Shadow.single C).Strand} (h : s.2 = t.2) : s = t := by
  rw [← Shadow.single_strand_eta C s, ← Shadow.single_strand_eta C t, h]

theorem w3dk_single_strand_ne {C : PolyComp} {s t : (Shadow.single C).Strand} (h : s ≠ t) : s.2 ≠ t.2 :=
  fun h' => h (w3dk_single_strand_ext h')

/-- the strand not adjacent to a crossing's two strands: the two strands of a crossing of a
one-component shadow have remote labels -/
theorem w3dk_not_adjacent_of_crossing (D : Diagram)
    (y : D.Γ.Crossing) {a b : D.Γ.Strand} (hy : y.val = {a, b}) : ¬ D.Γ.Adjacent a b := by
  have hpair := D.val_eq_pair y
  rw [hy] at hpair
  have hne := D.over_ne_under y
  rcases w3dk_pair_cases hne hpair.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact D.not_adjacent_over_under y
  · rw [← h1, ← h2]; intro h; exact D.not_adjacent_over_under y (D.Γ.adjacent_comm.mp h)

end W3DK_Arith


/-! # W3D NONKINK — step 5b: the site data and the non-kink condition on the subdivided diagram -/

section W3DK_SiteTransport

open Smoothing

variable (C : PolyComp) (hX : (Shadow.single C).Generic) (b₀ : ZMod C.k) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
  (hX₂ : (Shadow.single (w3dk_subdivPoly C b₀ u)).Generic)


/-- the image of an old strand -/
noncomputable abbrev w3dk_st (s : (w3dk_D₀ C hX).Γ.Strand) :
    (w3dk_D₂ C b₀ hX₂).Γ.Strand :=
  ⟨(0 : Fin 1), w3dk_lab C b₀ s.2⟩

theorem w3dk_st_injective : Function.Injective (w3dk_st C hX b₀ (u := u) hX₂) := by
  intro s t h
  have h2 : w3dk_lab C b₀ s.2 = w3dk_lab C b₀ t.2 := eq_of_heq (Sigma.ext_iff.mp h).2
  exact w3dk_single_strand_ext (w3dk_lab_injective C b₀ h2)

theorem w3dk_st_seg (s : (w3dk_D₀ C hX).Γ.Strand) (hs : s.2 ≠ b₀) :
    (w3dk_D₂ C b₀ hX₂).Γ.seg (w3dk_st C hX b₀ hX₂ s) =
      (w3dk_D₀ C hX).Γ.seg s := by
  show edgeSegment (w3dk_subdivPoly C b₀ u).P (w3dk_lab C b₀ s.2) = edgeSegment C.P s.2
  exact w3dk_seg_lab C b₀ hs

/-- the segment of any strand of the subdivided diagram is contained in the segment of an old strand -/
theorem w3dk_seg_cases (hu0 : 0 < u) (hu1 : u < 1) (u' : (w3dk_D₂ C b₀ hX₂).Γ.Strand) :
    (∃ s : (w3dk_D₀ C hX).Γ.Strand, s.2 ≠ b₀ ∧ u' = w3dk_st C hX b₀ hX₂ s) ∨
      (w3dk_D₂ C b₀ hX₂).Γ.seg u' ⊆
        (w3dk_D₀ C hX).Γ.seg (⟨(0 : Fin 1), b₀⟩ : (Shadow.single C).Strand) := by
  rcases w3dk_label_cases C b₀ u'.2 with ⟨l, hl, hm⟩ | hm | hm
  · left
    refine ⟨⟨(0 : Fin 1), l⟩, hl, ?_⟩
    rw [← Shadow.single_strand_eta _ u', hm]; rfl
  · right
    rw [← Shadow.single_strand_eta _ u', hm]
    exact w3dk_seg_last_subset C b₀ hu0 hu1
  · right
    rw [← Shadow.single_strand_eta _ u', hm]
    exact w3dk_seg_inserted_subset C b₀ hu0 hu1

/-- every vertex of the subdivided polygon is an old vertex or lies on the subdivided edge -/
theorem w3dk_vertex_cases (hu0 : 0 < u) (hu1 : u < 1) (m : ZMod (C.k + 1)) :
    (∃ i : ZMod C.k, (w3dk_subdivPoly C b₀ u).P m = C.P i) ∨
      (w3dk_subdivPoly C b₀ u).P m ∈ edgeSegment C.P b₀ := by
  rcases insertion_indices_exhaust m with h | ⟨i, hi⟩
  · right; rw [h]; exact w3dk_vertex_new_mem C b₀ hu0 hu1
  · left; exact ⟨i + (b₀ + 1), by rw [hi]; exact w3dk_vertex_old C b₀ i⟩

/-- **The site data transports to the subdivided diagram** when the subdivided edge `b₀` is adjacent
to one of the two strands of `x` and different from both (the kink situation): the image crossing
`w3dk_χ x` with the images of `g, y, z`, the same parameters, the same triangle, the same over data. -/
theorem w3dk_siteData_subdiv (x : (w3dk_D₀ C hX).Γ.Crossing) (py pz : Plane)
    (hsite : w3bi_SiteData (w3dk_D₀ C hX) x py pz)
    (hbs : b₀ ≠ (sS (w3dk_D₀ C hX) x).2)
    (hbt : b₀ ≠ (tS (w3dk_D₀ C hX) x).2)
    (hadj : adjacent b₀ (sS (w3dk_D₀ C hX) x).2 ∨
      adjacent b₀ (tS (w3dk_D₀ C hX) x).2) :
    w3bi_SiteData (w3dk_D₂ C b₀ hX₂)
      (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) py pz := by
  obtain ⟨g, hgs, hgt, y, z, hyx, hzx, hy, hz, hsy, htz, hord, clear, clear_vertex, hover, hpts⟩ := hsite
  have hs_ne : ((w3dk_D₀ C hX).overStrand x).2 ≠ b₀ := fun h => hbs h.symm
  have ht_ne : ((w3dk_D₀ C hX).underStrand x).2 ≠ b₀ := fun h => hbt h.symm
  -- `g` is not the subdivided edge: it is remote from `s` and from `t`
  have hg_ne : g.2 ≠ b₀ := by
    intro hg
    have hys : ¬ (w3dk_D₀ C hX).Γ.Adjacent (sS (w3dk_D₀ C hX) x) g := w3dk_not_adjacent_of_crossing (w3dk_D₀ C hX) y hy
    have hzt : ¬ (w3dk_D₀ C hX).Γ.Adjacent (tS (w3dk_D₀ C hX) x) g := w3dk_not_adjacent_of_crossing (w3dk_D₀ C hX) z hz
    rcases hadj with h | h
    · apply hys
      apply (Shadow.single_adjacent_iff C (sS (w3dk_D₀ C hX) x) g).mpr
      show adjacent (sS (w3dk_D₀ C hX) x).2 g.2
      rw [hg]
      exact w3dk_adjacent_symm _ _ h
    · apply hzt
      apply (Shadow.single_adjacent_iff C (tS (w3dk_D₀ C hX) x) g).mpr
      show adjacent (tS (w3dk_D₀ C hX) x).2 g.2
      rw [hg]
      exact w3dk_adjacent_symm _ _ h
  -- the strands of `y` and `z` are among `s, t, g`
  have hy_pair : ((w3dk_D₀ C hX).overStrand y = sS (w3dk_D₀ C hX) x ∧ (w3dk_D₀ C hX).underStrand y = g) ∨
      ((w3dk_D₀ C hX).overStrand y = g ∧ (w3dk_D₀ C hX).underStrand y = sS (w3dk_D₀ C hX) x) :=
    w3dk_pair_cases ((w3dk_D₀ C hX).over_ne_under y) (((w3dk_D₀ C hX).val_eq_pair y).symm.trans hy)
  have hz_pair : ((w3dk_D₀ C hX).overStrand z = tS (w3dk_D₀ C hX) x ∧ (w3dk_D₀ C hX).underStrand z = g) ∨
      ((w3dk_D₀ C hX).overStrand z = g ∧ (w3dk_D₀ C hX).underStrand z = tS (w3dk_D₀ C hX) x) :=
    w3dk_pair_cases ((w3dk_D₀ C hX).over_ne_under z) (((w3dk_D₀ C hX).val_eq_pair z).symm.trans hz)
  have hyo : ((w3dk_D₀ C hX).overStrand y).2 ≠ b₀ := by
    rcases hy_pair with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hs_ne
    · exact hg_ne
  have hyu : ((w3dk_D₀ C hX).underStrand y).2 ≠ b₀ := by
    rcases hy_pair with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact hg_ne
    · exact hs_ne
  have hzo : ((w3dk_D₀ C hX).overStrand z).2 ≠ b₀ := by
    rcases hz_pair with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact ht_ne
    · exact hg_ne
  have hzu : ((w3dk_D₀ C hX).underStrand z).2 ≠ b₀ := by
    rcases hz_pair with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact hg_ne
    · exact ht_ne
  -- the image strands
  have hsS : sS (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) = w3dk_st C hX b₀ hX₂ (sS (w3dk_D₀ C hX) x) :=
    w3dk_χ_overStrand C hX b₀ hu0 hu1 hX₂ x hs_ne
  have htS : tS (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) = w3dk_st C hX b₀ hX₂ (tS (w3dk_D₀ C hX) x) :=
    w3dk_χ_underStrand C hX b₀ hu0 hu1 hX₂ x ht_ne
  have hyo' : (w3dk_D₂ C b₀ hX₂).overStrand (w3dk_χ C hX b₀ hu0 hu1 hX₂ y) = w3dk_st C hX b₀ hX₂ ((w3dk_D₀ C hX).overStrand y) :=
    w3dk_χ_overStrand C hX b₀ hu0 hu1 hX₂ y hyo
  have hyu' : (w3dk_D₂ C b₀ hX₂).underStrand (w3dk_χ C hX b₀ hu0 hu1 hX₂ y) = w3dk_st C hX b₀ hX₂ ((w3dk_D₀ C hX).underStrand y) :=
    w3dk_χ_underStrand C hX b₀ hu0 hu1 hX₂ y hyu
  have hzo' : (w3dk_D₂ C b₀ hX₂).overStrand (w3dk_χ C hX b₀ hu0 hu1 hX₂ z) = w3dk_st C hX b₀ hX₂ ((w3dk_D₀ C hX).overStrand z) :=
    w3dk_χ_overStrand C hX b₀ hu0 hu1 hX₂ z hzo
  have hzu' : (w3dk_D₂ C b₀ hX₂).underStrand (w3dk_χ C hX b₀ hu0 hu1 hX₂ z) = w3dk_st C hX b₀ hX₂ ((w3dk_D₀ C hX).underStrand z) :=
    w3dk_χ_underStrand C hX b₀ hu0 hu1 hX₂ z hzu
  have hy' : (w3dk_χ C hX b₀ hu0 hu1 hX₂ y).val = {sS (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x), w3dk_st C hX b₀ hX₂ g} := by
    rw [(w3dk_D₂ C b₀ hX₂).val_eq_pair, hyo', hyu', hsS]
    rcases hy_pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Finset.pair_comm]
  have hz' : (w3dk_χ C hX b₀ hu0 hu1 hX₂ z).val = {tS (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x), w3dk_st C hX b₀ hX₂ g} := by
    rw [(w3dk_D₂ C b₀ hX₂).val_eq_pair, hzo', hzu', htS]
    rcases hz_pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Finset.pair_comm]
  have hsy' : sS (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) ∈ (w3dk_χ C hX b₀ hu0 hu1 hX₂ y).val := by
    rw [hy']; exact Finset.mem_insert_self _ _
  have htz' : tS (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) ∈ (w3dk_χ C hX b₀ hu0 hu1 hX₂ z).val := by
    rw [hz']; exact Finset.mem_insert_self _ _
  -- the parameters are unchanged
  have hpar : ∀ (c : (w3dk_D₀ C hX).Γ.Crossing) (st : (w3dk_D₀ C hX).Γ.Strand) (hst : st ∈ c.val) (hb : st.2 ≠ b₀)
      (st' : (w3dk_D₂ C b₀ hX₂).Γ.Strand) (hst'eq : st' = w3dk_st C hX b₀ hX₂ st)
      (hst' : st' ∈ (w3dk_χ C hX b₀ hu0 hu1 hX₂ c).val),
      (w3dk_D₂ C b₀ hX₂).crossingParam (w3dk_χ C hX b₀ hu0 hu1 hX₂ c) hst' = (w3dk_D₀ C hX).crossingParam c hst := by
    intro c st hst hb st' hst'eq hst'
    subst hst'eq
    have hv : ∀ v : (w3dk_D₀ C hX).Γ.Visit, v.1 = c →
        (w3dk_σ C hX b₀ hu0 hu1 hX₂ v).1 = w3dk_χ C hX b₀ hu0 hu1 hX₂ c := by
      intro v hv
      rcases (w3dk_D₀ C hX).visit_eq_over_or_under v with h | h
      · rw [h, hv, w3dk_σ_overVisit]; rfl
      · rw [h, hv, w3dk_σ_underVisit]; rfl
    have h1 := w3dk_σ_param C hX b₀ hu0 hu1 hX₂ ⟨c, ⟨st, hst⟩⟩ hb
    have h2 := w3dk_σ_strand C hX b₀ hu0 hu1 hX₂ ⟨c, ⟨st, hst⟩⟩ hb
    rw [w3dk_crossingParam_congr (w3dk_D₂ C b₀ hX₂) (w3dk_σ C hX b₀ hu0 hu1 hX₂ ⟨c, ⟨st, hst⟩⟩) _ _ (hv _ rfl) h2 hst']
    exact h1
  have hτs : τs (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) = τs (w3dk_D₀ C hX) x :=
    hpar x (sS (w3dk_D₀ C hX) x) ((w3dk_D₀ C hX).over_mem x) hs_ne _ hsS ((w3dk_D₂ C b₀ hX₂).over_mem _)
  have hτt : τt (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) = τt (w3dk_D₀ C hX) x :=
    hpar x (tS (w3dk_D₀ C hX) x) ((w3dk_D₀ C hX).under_mem x) ht_ne _ htS ((w3dk_D₂ C b₀ hX₂).under_mem _)
  have hpy : (w3dk_D₂ C b₀ hX₂).crossingParam (w3dk_χ C hX b₀ hu0 hu1 hX₂ y) hsy' = (w3dk_D₀ C hX).crossingParam y hsy :=
    hpar y (sS (w3dk_D₀ C hX) x) hsy hs_ne _ hsS hsy'
  have hpz : (w3dk_D₂ C b₀ hX₂).crossingParam (w3dk_χ C hX b₀ hu0 hu1 hX₂ z) htz' = (w3dk_D₀ C hX).crossingParam z htz :=
    hpar z (tS (w3dk_D₀ C hX) x) htz ht_ne _ htS htz'
  -- the triangle is the same
  have hK : convexHull ℝ {(w3dk_D₂ C b₀ hX₂).Γ.crossingPoint (w3dk_χ C hX b₀ hu0 hu1 hX₂ x),
      (w3dk_D₂ C b₀ hX₂).Γ.crossingPoint (w3dk_χ C hX b₀ hu0 hu1 hX₂ y), (w3dk_D₂ C b₀ hX₂).Γ.crossingPoint (w3dk_χ C hX b₀ hu0 hu1 hX₂ z)} =
      convexHull ℝ {(w3dk_D₀ C hX).Γ.crossingPoint x, (w3dk_D₀ C hX).Γ.crossingPoint y, (w3dk_D₀ C hX).Γ.crossingPoint z} := by
    rw [w3dk_χ_point, w3dk_χ_point, w3dk_χ_point]
  -- `b₀` is none of `s, t, g`: its segment is clear of the triangle
  have hb_clear : Disjoint ((w3dk_D₀ C hX).Γ.seg (⟨(0 : Fin 1), b₀⟩ : (Shadow.single C).Strand))
      (convexHull ℝ {(w3dk_D₀ C hX).Γ.crossingPoint x, (w3dk_D₀ C hX).Γ.crossingPoint y, (w3dk_D₀ C hX).Γ.crossingPoint z}) := by
    apply clear
    · intro h; exact hbs (eq_of_heq (Sigma.ext_iff.mp h).2)
    · intro h; exact hbt (eq_of_heq (Sigma.ext_iff.mp h).2)
    · intro h; exact hg_ne (eq_of_heq (Sigma.ext_iff.mp h).2).symm
  refine ⟨w3dk_st C hX b₀ hX₂ g, ?_, ?_, w3dk_χ C hX b₀ hu0 hu1 hX₂ y, w3dk_χ C hX b₀ hu0 hu1 hX₂ z,
    ?_, ?_, hy', hz', hsy', htz', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsS]; exact fun h => hgs (w3dk_st_injective C hX b₀ hX₂ h)
  · rw [htS]; exact fun h => hgt (w3dk_st_injective C hX b₀ hX₂ h)
  · exact fun h => hyx (w3dk_χ_injective C hX b₀ hu0 hu1 hX₂ h)
  · exact fun h => hzx (w3dk_χ_injective C hX b₀ hu0 hu1 hX₂ h)
  · rw [hpy, hpz, hτs, hτt]; exact hord
  · -- clear
    intro u' hu1' hu2' hu3'
    rw [hK]
    rcases w3dk_seg_cases C hX b₀ hX₂ hu0 hu1 u' with ⟨s, hs, rfl⟩ | hsub
    · rw [w3dk_st_seg C hX b₀ hX₂ s hs]
      apply clear
      · intro h; apply hu1'; rw [hsS, h]
      · intro h; apply hu2'; rw [htS, h]
      · intro h; apply hu3'; rw [h]
    · exact Set.disjoint_of_subset_left hsub hb_clear
  · -- clear_vertex
    intro i m
    rw [hK]
    rcases w3dk_vertex_cases C b₀ hu0 hu1 m with ⟨j, hj⟩ | hmem
    · show (w3dk_subdivPoly C b₀ u).P m ∉ _
      rw [hj]; exact clear_vertex (0 : Fin 1) j
    · show (w3dk_subdivPoly C b₀ u).P m ∉ _
      exact Set.disjoint_left.mp hb_clear hmem
  · -- hover
    rw [hyo', hzo']
    constructor
    · intro h1 h2
      exact (hover.mp (w3dk_st_injective C hX b₀ hX₂ h1)) (w3dk_st_injective C hX b₀ hX₂ h2)
    · intro h1
      have : (w3dk_D₀ C hX).overStrand z ≠ g := fun h => h1 (by rw [h])
      rw [hover.mpr this]
  · rw [w3dk_χ_point, w3dk_χ_point]; exact hpts

/-- **The non-kink condition holds on the subdivided diagram** at the image crossing, when the
subdivided edge is the single edge between the two strands of the kink (`t = s − 2` and `b₀ = s − 1`,
or `s = t − 2` and `b₀ = t − 1`) and `k ≠ 4`. -/
theorem w3dk_notKink_subdiv (hk4 : C.k ≠ 4) (x : (w3dk_D₀ C hX).Γ.Crossing)
    (hkink : ((sS (w3dk_D₀ C hX) x).2 - 1 = b₀ ∧
        (tS (w3dk_D₀ C hX) x).2 + 1 = b₀) ∨
      ((tS (w3dk_D₀ C hX) x).2 - 1 = b₀ ∧
        (sS (w3dk_D₀ C hX) x).2 + 1 = b₀)) :
    w3cs_NotKink (w3dk_D₂ C b₀ hX₂)
      (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) := by
  have hone : (1 : ZMod C.k) ≠ 0 := by
    have : Fact (1 < C.k) := ⟨by have := C.hk; omega⟩
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_one C.k, ZMod.val_zero] at this
    exact one_ne_zero this
  obtain ⟨s, hs⟩ : ∃ s : ZMod C.k, (sS (w3dk_D₀ C hX) x).2 = s := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ZMod C.k, (tS (w3dk_D₀ C hX) x).2 = t := ⟨_, rfl⟩
  rw [hs, ht] at hkink
  -- the same hypothesis with every operation read in `ZMod C.k`
  have hk' : (s - 1 = b₀ ∧ t + 1 = b₀) ∨ (t - 1 = b₀ ∧ s + 1 = b₀) := hkink
  have hs_ne : s ≠ b₀ := by
    rcases hk' with ⟨h, -⟩ | ⟨-, h⟩ <;> intro h' <;> apply hone
    · linear_combination h' - h
    · linear_combination h - h'
  have ht_ne : t ≠ b₀ := by
    rcases hk' with ⟨-, h⟩ | ⟨h, -⟩ <;> intro h' <;> apply hone
    · linear_combination h - h'
    · linear_combination h' - h
  have hsS : sS (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) =
      ⟨(0 : Fin 1), w3dk_lab C b₀ s⟩ := by
    rw [← hs]; exact w3dk_χ_overStrand C hX b₀ hu0 hu1 hX₂ x (by rw [hs]; exact hs_ne)
  have htS : tS (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) =
      ⟨(0 : Fin 1), w3dk_lab C b₀ t⟩ := by
    rw [← ht]; exact w3dk_χ_underStrand C hX b₀ hu0 hu1 hX₂ x (by rw [ht]; exact ht_ne)
  have harith := w3dk_lab_kink_arith C.hk hk4
  have hclean : (⟨(0 : Fin 1), insertIndex (s - (b₀ + 1)) - 1⟩ :
      (Shadow.single (w3dk_subdivPoly C b₀ u)).Strand) ≠ ⟨(0 : Fin 1), insertIndex (t - (b₀ + 1)) + 1⟩ ∧
      (⟨(0 : Fin 1), insertIndex (t - (b₀ + 1)) - 1⟩ :
      (Shadow.single (w3dk_subdivPoly C b₀ u)).Strand) ≠ ⟨(0 : Fin 1), insertIndex (s - (b₀ + 1)) + 1⟩ := by
    rcases hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : s - (b₀ + 1) = 0 := by linear_combination h1
      have e2 : t - (b₀ + 1) = -2 := by linear_combination h2
      rw [e1, e2, insertIndex_zero]
      exact ⟨fun h => harith.1 (eq_of_heq (Sigma.ext_iff.mp h).2),
        fun h => harith.2 (eq_of_heq (Sigma.ext_iff.mp h).2)⟩
    · have e1 : t - (b₀ + 1) = 0 := by linear_combination h1
      have e2 : s - (b₀ + 1) = -2 := by linear_combination h2
      rw [e1, e2, insertIndex_zero]
      exact ⟨fun h => harith.2 (eq_of_heq (Sigma.ext_iff.mp h).2),
        fun h => harith.1 (eq_of_heq (Sigma.ext_iff.mp h).2)⟩
  unfold w3cs_NotKink
  rw [hsS, htS]
  exact hclean

end W3DK_SiteTransport


/-! ### Step 6: the reduced value at one side (non-kink through the bigon, kink through the subdivision) -/

section W3DK_Reduced

open Smoothing

/-- the record crossings retained after deleting `y` and `z` (the BigonData-free form of `BigonData.keep`) -/
def w3dk_keep (D : Diagram) (y z : D.Γ.Crossing) : Set D.record.Crossing :=
  {c | c ≠ D.record.crossingOf (D.overVisit y) ∧ c ≠ D.record.crossingOf (D.overVisit z)}

theorem w3dk_keep_comm (D : Diagram) (y z : D.Γ.Crossing) : w3dk_keep D y z = w3dk_keep D z y := by
  ext c; exact and_comm

theorem w3dk_keep_eq_of_bigon {D : Diagram} (B : BigonData D) (y z : D.Γ.Crossing)
    (hB : (B.y = y ∧ B.z = z) ∨ (B.y = z ∧ B.z = y)) : B.keep = w3dk_keep D y z := by
  rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · show w3dk_keep D B.y B.z = _; rw [h1, h2]
  · show w3dk_keep D B.y B.z = _; rw [h1, h2, w3dk_keep_comm]

theorem w3dk_mem_keep_iff (D : Diagram) (y z : D.Γ.Crossing) (v : D.Γ.Visit) :
    D.record.crossingOf v ∈ w3dk_keep D y z ↔ (v.1 ≠ y ∧ v.1 ≠ z) := by
  show (D.record.crossingOf v ≠ D.record.crossingOf (D.overVisit y) ∧
    D.record.crossingOf v ≠ D.record.crossingOf (D.overVisit z)) ↔ _
  rw [Ne, Ne, w3bh_record_crossingOf_eq_iff, w3bh_record_crossingOf_eq_iff, Diagram.overVisit_fst,
    Diagram.overVisit_fst]

/-- **The reduced value at a smoothing crossing** (the BigonData-free content of one side of (6)): for every
crossing `y` of the library smoothing at the double point `py` there are a crossing `z` at `pz` and a diagram `E`
with the HOMFLY polynomial of the switched smoothing output and the record of that output minus `y, z`. -/
def w3dk_ReducedValue (D : Diagram) (x : D.Γ.Crossing) (py pz : Plane) : Prop :=
  ∀ y : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.Crossing,
    (smoothDiagram D x (eps D x) (eps_small D x)).Γ.crossingPoint y = py →
    ∃ z : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.Crossing,
      (smoothDiagram D x (eps D x) (eps_small D x)).Γ.crossingPoint z = pz ∧
      ∃ E : Diagram, homfly ((smoothDiagram D x (eps D x) (eps_small D x)).switch y) = homfly E ∧
        Nonempty (RecordIso E.record
          (((smoothDiagram D x (eps D x) (eps_small D x)).switch y).record.restrictCrossings
            (w3dk_keep _ y z)))

/-- the non-kink case: the bigon of `w3bi_bigon_of_site` and the library's R-II deletion -/
theorem w3dk_reducedValue_of_notKink (D : Diagram) (x : D.Γ.Crossing) (py pz : Plane)
    (hsite : w3bi_SiteData D x py pz) (hnk : w3cs_NotKink D x) : w3dk_ReducedValue D x py pz := by
  intro y hy
  obtain ⟨z, hz, B, hB⟩ := w3bi_bigon_of_site D x py pz hsite (fun _ => hnk) y hy
  obtain ⟨E, hR, -, ⟨ι⟩⟩ := exists_rii_deletion _ B
  refine ⟨z, hz, E, (homfly_reidemeister_II hR).symm, ?_⟩
  have hk := w3dk_keep_eq_of_bigon B y z hB
  obtain ⟨κ⟩ := SM.CB.restrictCrossings_iso_of_recordIso
    (RecordIso.refl ((smoothDiagram D x (eps D x) (eps_small D x)).switch y).record) B.keep
    (w3dk_keep _ y z) (fun v => by rw [hk]; exact Iff.rfl)
  exact ⟨ι.trans κ⟩

/-- **The point-compatible record isomorphism between the library smoothings at `x` and at its image on the
subdivided diagram** (`w3h_smooth_record_occ` twice around the smoothing congruence of the subdivision's
record isomorphism). -/
theorem w3dk_smooth_iso_subdiv (C : PolyComp) (hX : (Shadow.single C).Generic) (b₀ : ZMod C.k) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hX₂ : (Shadow.single (w3dk_subdivPoly C b₀ u)).Generic)
    (x : (w3dk_D₀ C hX).Γ.Crossing) :
    ∃ Θ : RecordIso (smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).record
        (smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _) (eps_small _ _)).record,
      ∀ v, (smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
          (eps_small _ _)).Γ.crossingPoint (Θ.Φ v).1 =
        (smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).Γ.crossingPoint v.1 := by
  obtain ⟨ι₁, hι₁⟩ := w3h_smooth_record_occ (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)
  obtain ⟨ι₂, hι₂⟩ := w3h_smooth_record_occ (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
    (eps_small _ _)
  have hover : (w3dk_ι C hX b₀ hu0 hu1 hX₂).Φ ((w3dk_D₀ C hX).overVisit x) =
      (w3dk_D₂ C b₀ hX₂).overVisit (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) :=
    w3dk_σ_overVisit C hX b₀ hu0 hu1 hX₂ x
  refine ⟨ι₁.trans ((w3dk_recordIso_smooth' (w3dk_ι C hX b₀ hu0 hu1 hX₂) _ _ hover).trans ι₂.symm), ?_⟩
  intro v
  -- the middle occurrence
  have h2 := hι₂ (ι₂.Φ.symm ((w3dk_recordIso_smooth' (w3dk_ι C hX b₀ hu0 hu1 hX₂) _ _ hover).Φ (ι₁.Φ v)))
  have h3 : ι₂.Φ (ι₂.Φ.symm ((w3dk_recordIso_smooth' (w3dk_ι C hX b₀ hu0 hu1 hX₂) _ _ hover).Φ (ι₁.Φ v))) =
      (w3dk_recordIso_smooth' (w3dk_ι C hX b₀ hu0 hu1 hX₂) _ _ hover).Φ (ι₁.Φ v) :=
    Equiv.apply_symm_apply _ _
  have h4 := congrArg (fun q : ((w3dk_D₂ C b₀ hX₂).record.smooth
    ((w3dk_D₂ C b₀ hX₂).overVisit (w3dk_χ C hX b₀ hu0 hu1 hX₂ x))).M =>
      (w3dk_D₂ C b₀ hX₂).Γ.crossingPoint q.1.1) h3
  have h5 := w3dk_recordIso_smooth'_Φ_val (w3dk_ι C hX b₀ hu0 hu1 hX₂) _ _ hover (ι₁.Φ v)
  have h6 := congrArg (fun w : (w3dk_D₂ C b₀ hX₂).Γ.Visit => (w3dk_D₂ C b₀ hX₂).Γ.crossingPoint w.1) h5
  have h7 := w3dk_reparamVisit_point (w3dk_subdivReparam C hX b₀ hu0 hu1 hX₂) (ι₁.Φ v).1
  have h8 := hι₁ v
  exact h2.symm.trans (h4.trans (h6.trans (h7.trans h8)))

/-- **The kink case**: subdivide the edge between the two strands of `x`, transport the site data, obtain the
bigon on the subdivided side, delete it, and carry the record identification back through the
point-compatible record isomorphism `Θ` of the switched smoothing outputs. -/
theorem w3dk_reducedValue_of_kink (C : PolyComp) (hX : (Shadow.single C).Generic)
    (x : (w3dk_D₀ C hX).Γ.Crossing) (py pz : Plane)
    (hsite : w3bi_SiteData (w3dk_D₀ C hX) x py pz) (hnk : ¬ w3cs_NotKink (w3dk_D₀ C hX) x) :
    w3dk_ReducedValue (w3dk_D₀ C hX) x py pz := by
  obtain ⟨s, hs⟩ : ∃ s : ZMod C.k, (sS (w3dk_D₀ C hX) x).2 = s := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ZMod C.k, (tS (w3dk_D₀ C hX) x).2 = t := ⟨_, rfl⟩
  -- the kink equation
  have hkink : (s - 1 = t + 1) ∨ (t - 1 = s + 1) := by
    unfold w3cs_NotKink at hnk
    rw [not_and_or, not_not, not_not] at hnk
    rcases hnk with h | h
    · left
      have := eq_of_heq (Sigma.ext_iff.mp h).2
      rw [hs, ht] at this; exact this
    · right
      have := eq_of_heq (Sigma.ext_iff.mp h).2
      rw [hs, ht] at this; exact this
  -- the third strand `g` is remote from `s` and `t`: `k ≠ 4`
  have hsite' := hsite
  obtain ⟨g, -, -, y, z, -, -, hy, hz, -, -, -, -, -, -, -⟩ := hsite'
  have hsg : ¬ adjacent s g.2 := by
    have h1 := w3dk_not_adjacent_of_crossing (w3dk_D₀ C hX) y hy
    intro h; apply h1
    apply (Shadow.single_adjacent_iff C (sS (w3dk_D₀ C hX) x) g).mpr
    show adjacent (sS (w3dk_D₀ C hX) x).2 g.2
    rw [hs]; exact h
  have htg : ¬ adjacent t g.2 := by
    have h1 := w3dk_not_adjacent_of_crossing (w3dk_D₀ C hX) z hz
    intro h; apply h1
    apply (Shadow.single_adjacent_iff C (tS (w3dk_D₀ C hX) x) g).mpr
    show adjacent (tS (w3dk_D₀ C hX) x).2 g.2
    rw [ht]; exact h
  have hk4 : C.k ≠ 4 := by
    apply w3dk_ne_four s t g.2 _ hsg htg
    rcases hkink with h | h
    · exact Or.inl (by linear_combination -h)
    · exact Or.inr (by linear_combination -h)
  -- the subdivided edge `b₀`: the single edge between the two strands of the kink
  obtain ⟨b₀, hb⟩ : ∃ b₀ : ZMod C.k, (s - 1 = b₀ ∧ t + 1 = b₀) ∨ (t - 1 = b₀ ∧ s + 1 = b₀) := by
    rcases hkink with h | h
    · exact ⟨s - 1, Or.inl ⟨rfl, h.symm⟩⟩
    · exact ⟨t - 1, Or.inr ⟨rfl, h.symm⟩⟩
  have hone : (1 : ZMod C.k) ≠ 0 := by
    have : Fact (1 < C.k) := ⟨by have := C.hk; omega⟩
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_one C.k, ZMod.val_zero] at this
    exact one_ne_zero this
  have hbs : b₀ ≠ s := by
    rcases hb with ⟨h, -⟩ | ⟨-, h⟩ <;> intro h' <;> apply hone
    · linear_combination -(h + h')
    · linear_combination h + h'
  have hbt : b₀ ≠ t := by
    rcases hb with ⟨-, h⟩ | ⟨h, -⟩ <;> intro h' <;> apply hone
    · linear_combination h + h'
    · linear_combination -(h + h')
  have hadj : adjacent b₀ s ∨ adjacent b₀ t := by
    rcases hb with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl (Or.inr (Or.inr (by linear_combination h)))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h)))
  have hbs' : b₀ ≠ (sS (w3dk_D₀ C hX) x).2 := by rw [hs]; exact hbs
  have hbt' : b₀ ≠ (tS (w3dk_D₀ C hX) x).2 := by rw [ht]; exact hbt
  have hadj' : adjacent b₀ (sS (w3dk_D₀ C hX) x).2 ∨ adjacent b₀ (tS (w3dk_D₀ C hX) x).2 := by
    rw [hs, ht]; exact hadj
  have hkink' : ((sS (w3dk_D₀ C hX) x).2 - 1 = b₀ ∧ (tS (w3dk_D₀ C hX) x).2 + 1 = b₀) ∨
      ((tS (w3dk_D₀ C hX) x).2 - 1 = b₀ ∧ (sS (w3dk_D₀ C hX) x).2 + 1 = b₀) := by
    rw [hs, ht]; exact hb
  -- the subdivision
  obtain ⟨u, hu0, hu1, hoff⟩ := w3dk_exists_off C hX b₀
  have hX₂ := w3dk_subdivPoly_generic C hX b₀ hu0 hu1 hoff
  have hsite₂ := w3dk_siteData_subdiv C hX b₀ hu0 hu1 hX₂ x py pz hsite hbs' hbt' hadj'
  have hnk₂ := w3dk_notKink_subdiv C hX b₀ hu0 hu1 hX₂ hk4 x hkink'
  obtain ⟨Θ₀, hΘ₀⟩ := w3dk_smooth_iso_subdiv C hX b₀ hu0 hu1 hX₂ x
  intro y hy
  -- the image of `y`
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, (Θ₀.Φ ((smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).overVisit y)).1 = y₂ :=
    ⟨_, rfl⟩
  have hy₂pt : (smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
      (eps_small _ _)).Γ.crossingPoint y₂ = py := by
    rw [← hy₂, hΘ₀]; exact hy
  obtain ⟨z₂, hz₂, B₂, hB₂⟩ := w3bi_bigon_of_site (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) py pz
    hsite₂ (fun _ => hnk₂) y₂ hy₂pt
  obtain ⟨E, hR, -, ⟨ι⟩⟩ := exists_rii_deletion _ B₂
  -- the record isomorphism of the two switched outputs
  let Θ : RecordIso ((smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).switch y).record
      ((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _) (eps_small _ _)).switch
        y₂).record :=
    ((smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).switchRecordIso y _ rfl).trans
      ((Θ₀.switch _).trans
        ((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
          (eps_small _ _)).switchRecordIso y₂ _ hy₂).symm)
  have hΘ : ∀ v, Θ.Φ v = Θ₀.Φ v := fun _ => rfl
  have hΘpt : ∀ v, (smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
      (eps_small _ _)).Γ.crossingPoint v.1 =
      (smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).Γ.crossingPoint (Θ.symm.Φ v).1 := by
    intro v
    have h1 := hΘ₀ (Θ₀.Φ.symm v)
    have h2 : Θ₀.Φ (Θ₀.Φ.symm v) = v := Equiv.apply_symm_apply _ _
    have h3 := congrArg (fun w : (smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
      (eps_small _ _)).Γ.Visit => (smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
      (eps_small _ _)).Γ.crossingPoint w.1) h2
    exact h3.symm.trans h1
  -- `z`: the preimage of `z₂`
  obtain ⟨z, hz⟩ : ∃ z, (Θ.symm.Φ ((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
      (eps_small _ _)).overVisit z₂)).1 = z := ⟨_, rfl⟩
  have hzpt : (smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).Γ.crossingPoint z = pz := by
    rw [← hz]
    exact (hΘpt _).symm.trans hz₂
  refine ⟨z, hzpt, E, ?_, ?_⟩
  · have h1 : homfly ((smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).switch y) =
        homfly ((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
          (eps_small _ _)).switch y₂) := by
      rw [← P_eq_homfly, ← P_eq_homfly]
      exact presentations _ _ ⟨Θ⟩
    exact h1.trans (homfly_reidemeister_II hR).symm
  · have hk := w3dk_keep_eq_of_bigon B₂ y₂ z₂ hB₂
    have hcond : ∀ v, ((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
        (eps_small _ _)).switch y₂).record.crossingOf v ∈ w3dk_keep ((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _) (eps_small _ _)).switch y₂) y₂ z₂ ↔
        ((smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).switch y).record.crossingOf (Θ.symm.Φ v) ∈
          w3dk_keep ((smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).switch y) y z := by
      intro v
      have e1 : v.1 = y₂ ↔ (Θ.symm.Φ v).1 = y := by
        constructor
        · intro h
          apply (smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).generic.crossingPoint_injective
          exact (hΘpt v).symm.trans ((congrArg _ h).trans (hy₂pt.trans hy.symm))
        · intro h
          apply (smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
            (eps_small _ _)).generic.crossingPoint_injective
          exact (hΘpt v).trans ((congrArg _ h).trans (hy.trans hy₂pt.symm))
      have e2 : v.1 = z₂ ↔ (Θ.symm.Φ v).1 = z := by
        constructor
        · intro h
          apply (smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).generic.crossingPoint_injective
          exact (hΘpt v).symm.trans ((congrArg _ h).trans (hz₂.trans hzpt.symm))
        · intro h
          apply (smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
            (eps_small _ _)).generic.crossingPoint_injective
          exact (hΘpt v).trans ((congrArg _ h).trans (hzpt.trans hz₂.symm))
      exact (w3dk_mem_keep_iff ((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _) (eps_small _ _)).switch y₂) y₂ z₂ v).trans ((and_congr (not_congr e1) (not_congr e2)).trans
        (w3dk_mem_keep_iff ((smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).switch y) y z (Θ.symm.Φ v)).symm)
    obtain ⟨κ⟩ := SM.CB.restrictCrossings_iso_of_recordIso Θ.symm (w3dk_keep ((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _) (eps_small _ _)).switch y₂) y₂ z₂)
      (w3dk_keep ((smoothDiagram (w3dk_D₀ C hX) x (eps _ x) (eps_small _ x)).switch y) y z) hcond
    refine ⟨ι.trans ?_⟩
    show RecordIso (((smoothDiagram (w3dk_D₂ C b₀ hX₂) (w3dk_χ C hX b₀ hu0 hu1 hX₂ x) (eps _ _)
      (eps_small _ _)).switch y₂).record.restrictCrossings B₂.keep) _
    rw [hk]
    exact κ

/-- **The reduced value at every site of a one-component positive diagram**, by cases on the non-kink
condition. -/
theorem w3dk_reducedValue_of_site (C : PolyComp) (hX : (Shadow.single C).Generic)
    (x : (w3dk_D₀ C hX).Γ.Crossing) (py pz : Plane) (hsite : w3bi_SiteData (w3dk_D₀ C hX) x py pz) :
    w3dk_ReducedValue (w3dk_D₀ C hX) x py pz := by
  by_cases hnk : w3cs_NotKink (w3dk_D₀ C hX) x
  · exact w3dk_reducedValue_of_notKink _ x py pz hsite hnk
  · exact w3dk_reducedValue_of_kink C hX x py pz hsite hnk

end W3DK_Reduced


/-! ### Step 7: the BigonData-free reduced-record identification (patched copies of unit H's bridge and glue)
and the two-sided site Prop `w3dk_rii_value_sites` -/

section W3DK_Sites

open RProof SM.GeoCarrier SM.Carrier Smoothing

theorem w3dk_reduced_to_smooth_free (D : Diagram) (x y z : D.Γ.Crossing)
    (a₁ a₂ b₂ c₁ c₂ : D.Γ.Visit) (ha₁ : a₁.1 = x) (ha₂ : a₂.1 = y) (hc₁ : c₁ = D.twin a₂)
    (hb₂ : b₂.1 = z) (hc₂ : c₂ = D.twin b₂)
    {ε : ℝ} (hε : SmallEps D x ε)
    (y₀ z₀ : (smoothDiagram D x ε hε).Γ.Crossing)
    (hy₀ : (smoothDiagram D x ε hε).Γ.crossingPoint y₀ = D.Γ.crossingPoint y)
    (hz₀ : (smoothDiagram D x ε hε).Γ.crossingPoint z₀ = D.Γ.crossingPoint z) :
    Nonempty (RecordIso (((smoothDiagram D x ε hε).switch y₀).record.restrictCrossings (w3dk_keep _ y₀ z₀))
      ((D.record.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})) := by
  subst hc₁ hc₂
  -- the occurrence-defined retained set on `E = smoothDiagram D x ε hε`
  let X₁ : Set (smoothDiagram D x ε hε).record.Crossing := {c | ∀ w ∈ c.1, w.1 ≠ y₀ ∧ w.1 ≠ z₀}
  have hX₁ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit,
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔ (u.1 ≠ y₀ ∧ u.1 ≠ z₀) := by
    intro u
    rw [w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ∧
      (((smoothDiagram D x ε hε).twin u).1 ≠ y₀ ∧ ((smoothDiagram D x ε hε).twin u).1 ≠ z₀) ↔ _
    rw [Diagram.twin_fst, and_self]
  -- Step A/B: `B.reducedRecord ≅ (E.record.switch v₀).restrictCrossings X₁`
  obtain ⟨ι₂⟩ := CB.restrictCrossings_iso_of_recordIso
    ((smoothDiagram D x ε hε).switchRecordIso y₀ ((smoothDiagram D x ε hε).overVisit y₀) rfl)
    (w3dk_keep _ y₀ z₀) X₁ (by
    intro u
    show _ ↔ (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁
    exact (w3dk_mem_keep_iff ((smoothDiagram D x ε hε).switch y₀) y₀ z₀ u).trans (hX₁ u).symm)
  -- Step C: the switch at the deleted `y₀` is invisible
  obtain ⟨ι₃⟩ := w3h_restrict_switch_deleted (smoothDiagram D x ε hε).record X₁
    ((smoothDiagram D x ε hε).overVisit y₀) (fun h => ((hX₁ _).mp h).1 rfl)
  -- Step D: the smoothing bridge
  obtain ⟨ι₄, hι₄⟩ := w3h_smooth_record_occ D x ε hε
  have hpt : ∀ (u : (smoothDiagram D x ε hε).Γ.Visit) (w : D.Γ.Crossing)
      (w₀ : (smoothDiagram D x ε hε).Γ.Crossing)
      (hw₀ : (smoothDiagram D x ε hε).Γ.crossingPoint w₀ = D.Γ.crossingPoint w),
      (ι₄.Φ u).1.1 = w ↔ u.1 = w₀ := by
    intro u w w₀ hw₀
    constructor
    · intro h
      apply (smoothDiagram D x ε hε).generic.crossingPoint_injective
      rw [← hι₄ u, h, hw₀]
    · intro h
      apply D.generic.crossingPoint_injective
      rw [hι₄ u, h, hw₀]
  let X₂ : Set (D.record.smooth (D.overVisit x)).Crossing :=
    {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂}
  have hP : ∀ w : D.Γ.Visit, (w ≠ a₂ ∧ w ≠ D.twin a₂ ∧ w ≠ b₂ ∧ w ≠ D.twin b₂) ↔
      (w.1 ≠ y ∧ w.1 ≠ z) := by
    intro w
    rw [← and_assoc, w3bh_ne_ne_twin_iff, w3bh_ne_ne_twin_iff, ha₂, hb₂]
  have hX₂ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit, (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔
      (D.record.smooth (D.overVisit x)).crossingOf (ι₄.Φ u) ∈ X₂ := by
    intro u
    rw [hX₁, w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ↔
      ((ι₄.Φ u).1 ≠ a₂ ∧ (ι₄.Φ u).1 ≠ D.twin a₂ ∧ (ι₄.Φ u).1 ≠ b₂ ∧ (ι₄.Φ u).1 ≠ D.twin b₂) ∧
      (D.twin (ι₄.Φ u).1 ≠ a₂ ∧ D.twin (ι₄.Φ u).1 ≠ D.twin a₂ ∧ D.twin (ι₄.Φ u).1 ≠ b₂ ∧
        D.twin (ι₄.Φ u).1 ≠ D.twin b₂)
    rw [hP, hP, Diagram.twin_fst, and_self]
    exact Iff.and (not_congr (hpt u y y₀ hy₀).symm) (not_congr (hpt u z z₀ hz₀).symm)
  obtain ⟨ι₅⟩ := CB.restrictCrossings_iso_of_recordIso ι₄ X₁ X₂ hX₂
  -- Step E: land on `a₁`
  rcases D.eq_or_eq_twin (D.overVisit x) a₁ ha₁ with h | h
  · subst h
    exact ⟨ι₂.trans (ι₃.trans ι₅)⟩
  · subst h
    obtain ⟨ι₆⟩ := CB.restrictCrossings_iso_of_recordIso (D.record.smoothPairIso (D.overVisit x)).symm X₂
      {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂} (by
        intro u
        rw [w3bh_crossingOf_mem_setOf, w3bh_crossingOf_mem_setOf]
        exact Iff.rfl)
    exact ⟨ι₂.trans (ι₃.trans (ι₅.trans ι₆))⟩

/-- (W3D NONKINK) **BigonData-free copy of unit H's `w3h_hrec`**: the two reduced records in the form `w3dk_keep`, through `w3dk_reduced_to_smooth_free` on both sides and `w3h_record_core` (body verbatim otherwise). -/
theorem w3dk_hrec_free (D_H D_L : Diagram) (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1)
    (x_H y_H z_H : D_H.Γ.Crossing) (x_L y_L z_L : D_L.Γ.Crossing)
    (Ψ : D_H.Γ.Visit ≃ D_L.Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : D_H.Γ.Visit)
    (ha₁ : a₁.1 = x_H) (hb₁ : b₁ = D_H.twin a₁) (ha₂ : a₂.1 = y_H) (hc₁ : c₁ = D_H.twin a₂)
    (hb₂ : b₂.1 = z_H) (hc₂ : c₂ = D_H.twin b₂)
    (hxy : x_H ≠ y_H) (hxz : x_H ≠ z_H) (hyz : y_H ≠ z_H)
    (hadj_e : D_H.nextVisit a₁ = a₂ ∨ D_H.nextVisit a₂ = a₁)
    (hadj_f : D_H.nextVisit b₁ = b₂ ∨ D_H.nextVisit b₂ = b₁)
    (hadj_g : D_H.nextVisit c₁ = c₂ ∨ D_H.nextVisit c₂ = c₁)
    (htw : ∀ v, Ψ (D_H.twin v) = D_L.twin (Ψ v)) (hbit : ∀ v, D_L.overBit (Ψ v) = D_H.overBit v)
    (hsgn : ∀ v, D_L.sign (Ψ v).1 = D_H.sign v.1)
    (hcyc : ∀ u v w, D_L.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      D_H.VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w))
    (hxL : (Ψ a₁).1 = x_L) (hyL : (Ψ a₂).1 = y_L) (hzL : (Ψ b₂).1 = z_L)
    {εH εL : ℝ} (hεH : SmallEps D_H x_H εH) (hεL : SmallEps D_L x_L εL)
    (yH0 zH0 : (smoothDiagram D_H x_H εH hεH).Γ.Crossing)
    (hyH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint yH0 = D_H.Γ.crossingPoint y_H)
    (hzH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint zH0 = D_H.Γ.crossingPoint z_H)
    (yL0 zL0 : (smoothDiagram D_L x_L εL hεL).Γ.Crossing)
    (hyL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint yL0 = D_L.Γ.crossingPoint y_L)
    (hzL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint zL0 = D_L.Γ.crossingPoint z_L) :
    Nonempty (RecordIso
      (((smoothDiagram D_H x_H εH hεH).switch yH0).record.restrictCrossings (w3dk_keep _ yH0 zH0))
      (((smoothDiagram D_L x_L εL hεL).switch yL0).record.restrictCrossings (w3dk_keep _ yL0 zL0))) := by
  -- the six local occurrences and their crossings
  have hb₁x : b₁.1 = x_H := by rw [hb₁]; exact ha₁
  have hc₁y : c₁.1 = y_H := by rw [hc₁]; exact ha₂
  have hc₂z : c₂.1 = z_H := by rw [hc₂]; exact hb₂
  have hne : ∀ (u v : D_H.Γ.Visit), u.1 ≠ v.1 → u ≠ v :=
    fun u v h h' => h (congrArg (fun w : D_H.Γ.Visit => w.1) h')
  have h13 : a₁ ≠ b₁ := by rw [hb₁]; exact (D_H.twin_ne a₁).symm
  have h25 : a₂ ≠ c₁ := by rw [hc₁]; exact (D_H.twin_ne a₂).symm
  have h46 : b₂ ≠ c₂ := by rw [hc₂]; exact (D_H.twin_ne b₂).symm
  have h14 : a₁ ≠ b₂ := hne _ _ (by rw [ha₁, hb₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [ha₂, hb₁x]; exact hxy.symm)
  have h24 : a₂ ≠ b₂ := hne _ _ (by rw [ha₂, hb₂]; exact hyz)
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [ha₁, hc₁y]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [ha₁, hc₂z]; exact hxz)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [ha₂, hc₂z]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hb₁x, hc₁y]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hb₁x, hc₂z]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hb₂, hc₁y]; exact hyz.symm)
  have hσσ : ∀ v, (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) = v :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  -- the twisted successor clause from the twisted cyclic order (one component on both sides)
  have hsucc : ∀ v, Ψ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (D_H.nextVisit ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) =
      D_L.nextVisit (Ψ v) := by
    let Φ' : D_H.Γ.Visit ≃ D_L.Γ.Visit :=
      (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)).trans Ψ
    have hcomp : ∀ v w, D_L.compOf (Φ' v) = D_L.compOf (Φ' w) ↔ D_H.compOf v = D_H.compOf w :=
      fun v w => ⟨fun _ => w3bh_compOf_eq_of_one D_H hH v w, fun _ => w3bh_compOf_eq_of_one D_L hL _ _⟩
    have hbetw : ∀ v w u, D_H.compOf w = D_H.compOf v → D_H.compOf u = D_H.compOf v →
        (D_L.VisitBetween (Φ' v) (Φ' w) (Φ' u) ↔ D_H.VisitBetween v w u) := by
      intro v w u _ _
      have := hcyc ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
      rw [hσσ, hσσ, hσσ] at this
      exact this
    intro v
    have key := D_H.nextVisit_comm_of_visitBetween_iff Φ' hcomp hbetw
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
    simp only [Φ', Equiv.trans_apply, hσσ] at key
    exact key
  -- the crossings of `D_L`
  have hΨfst := w3bh_fst_eq_iff_of_twin Ψ htw
  have hxyL : x_L ≠ y_L := by
    rw [← hxL, ← hyL, Ne, hΨfst, ha₁, ha₂]; exact hxy
  have hxzL : x_L ≠ z_L := by
    rw [← hxL, ← hzL, Ne, hΨfst, ha₁, hb₂]; exact hxz
  have hyzL : y_L ≠ z_L := by
    rw [← hyL, ← hzL, Ne, hΨfst, ha₂, hb₂]; exact hyz
  -- the two bridges
  obtain ⟨ιH⟩ := w3dk_reduced_to_smooth_free D_H x_H y_H z_H a₁ a₂ b₂ c₁ c₂ ha₁ ha₂ hc₁ hb₂ hc₂ hεH
    yH0 zH0 hyH0 hzH0
  obtain ⟨ιL⟩ := w3dk_reduced_to_smooth_free D_L x_L y_L z_L (Ψ a₁) (Ψ a₂) (Ψ b₂) (Ψ c₁) (Ψ c₂) hxL hyL
    (by rw [hc₁, htw]) hzL (by rw [hc₂, htw]) hεL yL0 zL0 hyL0 hzL0
  -- the core
  have hcr : ∀ u v : D_H.Γ.Visit, u.1 ≠ v.1 → D_H.record.crossingOf u ≠ D_H.record.crossingOf v :=
    fun u v h h' => h ((w3bh_record_crossingOf_eq_iff D_H u v).mp h')
  obtain ⟨κ⟩ := w3h_record_core D_H.record D_L.record (D_H.record_componentCount.trans hH)
    (D_L.record_componentCount.trans hL) Ψ a₁ a₂ b₁ b₂ c₁ c₂ hb₁.symm hc₁.symm hc₂.symm
    (hcr _ _ (by rw [ha₁, ha₂]; exact hxy)) (hcr _ _ (by rw [ha₁, hb₂]; exact hxz))
    (hcr _ _ (by rw [ha₂, hb₂]; exact hyz)) hadj_e hadj_f hadj_g htw hbit hsgn hsucc
  exact ⟨ιH.trans (κ.trans ιL.symm)⟩


/-- **The value form of the (6) site data**: at every 177 configuration the two switched library smoothings at
`x_H, x_L` have equal HOMFLY polynomials (the statement `w3bi_rii_sites` asks for two `BigonData`, which do not
exist in the kink case; this is what the ledger consumes). -/
def w3dk_rii_value_sites : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∀ (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
        (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing),
        (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H = crossingPoint (xPair hef) →
        (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
          crossingPoint (xPair ((hs _).mp hef)) →
        ∀ (y_H : (smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H
              (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)
              (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).Γ.Crossing)
          (y_L : (smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L
              (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)
              (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).Γ.Crossing),
          (smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H
              (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)
              (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).Γ.crossingPoint y_H =
            crossingPoint (xPair heg) →
          (smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L
              (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)
              (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).Γ.crossingPoint y_L =
            crossingPoint (xPair ((hs _).mp heg)) →
          homfly ((smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H
              (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)
              (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).switch y_H) =
            homfly ((smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L
              (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)
              (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).switch y_L)

/-- **The value form of the site data holds** (site data β1′ + wall data β2 + the reduced values of both sides,
by cases kink / non-kink, glued by the BigonData-free record identification). -/
theorem w3dk_rii_value_sites_data : w3dk_rii_value_sites := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL y_H y_L hyH hyL
  obtain ⟨sH, sL⟩ := w3bi_site_data_data hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi
    hQi' q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL
  obtain ⟨y_H', z_H', y_L', z_L', Ψ, a₁, a₂, b₁, b₂, c₁, c₂, hyH', hzH', hyL', hzL', ha₁, hb₁, ha₂, hc₁, hb₂, hc₂,
    hadj_e, hadj_f, hadj_g, htw, hbit, hsgn, hcyc, hxL', hyL'', hzL''⟩ := w3bi_wall_data_data hn E e f g δ hL hGT
    hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL
  have hxy : x_H ≠ y_H' := by
    intro h
    apply P1.xPair_ef_ne_eg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hxH, ← hyH', h]
  have hxz : x_H ≠ z_H' := by
    intro h
    apply P1.xPair_ef_ne_fg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hxH, ← hzH', h]
  have hyz : y_H' ≠ z_H' := by
    intro h
    apply P1.xPair_eg_ne_fg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hyH', ← hzH', h]
  -- the reduced values on both sides
  obtain ⟨z_H, hzH, E_H, hEH, ⟨ιH⟩⟩ := w3dk_reducedValue_of_site _ _ x_H _ _ sH y_H hyH
  obtain ⟨z_L, hzL, E_L, hEL, ⟨ιL⟩⟩ := w3dk_reducedValue_of_site _ _ x_L _ _ sL y_L hyL
  obtain ⟨κ⟩ := w3dk_hrec_free _ _ rfl rfl x_H y_H' z_H' x_L y_L' z_L' Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂
    hxy hxz hyz hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL' hyL'' hzL'' (eps_small _ x_H) (eps_small _ x_L)
    y_H z_H (hyH.trans hyH'.symm) (hzH.trans hzH'.symm) y_L z_L (hyL.trans hyL'.symm) (hzL.trans hzL'.symm)
  have hP : homfly E_H = homfly E_L := by
    rw [← P_eq_homfly, ← P_eq_homfly]
    exact presentations _ _ ⟨ιH.trans (κ.trans ιL.symm)⟩
  exact hEH.trans (hP.trans hEL.symm)

end W3DK_Sites


end W3BI_REAL


/-! # W3C — unit KNOT (`w3ck_`): `esc_MoveData.knot_after_two` / `three_components` at the configuration

APPENDED 2026-09-16 by the W3C KNOT prover to `W3B_Assembled.lean` (byte-identical above this line; nothing
frozen edited, no leaf body replaced).  Companion report: `W3C_KNOT_REPORT.md`.

Content: K1 the record-level counts of a double smoothing (`componentCount_smooth_of_self/_mixed`); K2 the two
arcs of a self crossing on a one-circle record (port of R176_SMOOTH §R1, `r176s_` → `w3ck_`) and
`w3ck_isSelfCrossing_smooth_iff`; K3 the bridge record arcs ↔ `GeometricInterlaces` on the lift
(`CV.arcBetween_iff_key`, `CV.geometricInterlaces_iff_unique`); K4 self/mixed along a `RecordIso`; K5 the two
counts at a carrier diagram from an occurrence-compatible record clause; K6 the corrected (record-clause) forms
of the two outer clauses, PROVED at every configuration (`w3ck_knot_after_two`, `w3ck_three_components_count`);
K7 the corrected outer data `w3ck_esc_outer_occ`, assembled from the black box `w3ck_split_ident` (SPLITB's
`esc_FullSplitData` + this unit's open identification clause).  Rule-3 finding: the frozen
`w3bi_knot_after_two` / `w3bi_three_components` quantify over every RELATIONAL oriented smoothing; the library
identifies the record only of `smoothDiagram`, so they are stated here with record clauses (the ledger consumes
them at such smoothings only). -/

section W3CK_KNOT

open Equiv RProof

/-! ### K1. Component counts of a double smoothing at the record level -/

/-- on a one-circle record every occurrence is a self crossing -/
theorem w3ck_isSelfCrossing_of_one (ρ : Record) (h1 : ρ.componentCount = 1) (x : ρ.M) :
    ρ.IsSelfCrossing x :=
  Fintype.card_le_one_iff.mp (le_of_eq h1) _ _

/-- the smoothing of a one-circle record at any occurrence has two circles -/
theorem w3ck_smooth_componentCount_two (ρ : Record) (h1 : ρ.componentCount = 1) (x : ρ.M) :
    (ρ.smooth x).componentCount = 2 := by
  rw [ρ.componentCount_smooth_of_self x (w3ck_isSelfCrossing_of_one ρ h1 x), h1]

/-- **the first smoothing of a knot diagram has two components**, from its record clause -/
theorem w3ck_componentCount_first (D D₀ : Diagram) (hD : D.componentCount = 1) (v : D.Γ.Visit)
    (ι₀ : RecordIso D₀.record (D.record.smooth v)) : D₀.componentCount = 2 := by
  rw [← D₀.record_componentCount, ι₀.componentCount_eq,
    w3ck_smooth_componentCount_two D.record (CV.record_componentCount_one D hD) v]

/-- **`D^{xy}` is a knot when `y` is mixed in `D^x`** (ESC §2 "there `y` is mixed, so smoothing `y` joins
them and `D_H^{xy}` is a knot"), at the record level: from the two record clauses. -/
theorem w3ck_componentCount_double_mixed (D D₀ J : Diagram) (hD : D.componentCount = 1) (v : D.Γ.Visit)
    (ι₀ : RecordIso D₀.record (D.record.smooth v)) (w : D₀.Γ.Visit)
    (ι₁ : RecordIso J.record (D₀.record.smooth w)) (hmix : ¬ D₀.record.IsSelfCrossing w) :
    J.componentCount = 1 := by
  rw [← J.record_componentCount, ι₁.componentCount_eq, D₀.record.componentCount_smooth_of_mixed w hmix,
    D₀.record_componentCount, w3ck_componentCount_first D D₀ hD v ι₀]

/-- **`D^{xy}` has three components when `y` is a self crossing of `D^x`** (ESC §2 "`D_L^{xy}` has three
components"), at the record level. -/
theorem w3ck_componentCount_double_self (D D₀ J : Diagram) (hD : D.componentCount = 1) (v : D.Γ.Visit)
    (ι₀ : RecordIso D₀.record (D.record.smooth v)) (w : D₀.Γ.Visit)
    (ι₁ : RecordIso J.record (D₀.record.smooth w)) (hself : D₀.record.IsSelfCrossing w) :
    J.componentCount = 3 := by
  rw [← J.record_componentCount, ι₁.componentCount_eq, D₀.record.componentCount_smooth_of_self w hself,
    D₀.record_componentCount, w3ck_componentCount_first D D₀ hD v ι₀]

/-! ### K2. The two arcs of a self crossing on a one-circle record (port of R176_SMOOTH §R1, `r176s_` →
`w3ck_`; byte-identical proofs) -/


section W3CK_Rec

variable (ρ : Record) (h1 : ρ.componentCount = 1) (x : ρ.M)

/-- the open arc from `x` forward to `τ x` (the word `A` of `(x A y B)`) -/
def w3ck_ArcA (v : ρ.M) : Prop := ρ.ArcBetween x v (ρ.pair x)

theorem w3ck_arcA_iff (v : ρ.M) :
    w3ck_ArcA ρ x v ↔ 0 < ρ.steps x v ∧ ρ.steps x v < ρ.steps x (ρ.pair x) := Iff.rfl

include h1 in
theorem w3ck_steps_pair_pos : 0 < ρ.steps x (ρ.pair x) :=
  (ρ.steps_pos_iff h1 x (ρ.pair x)).mpr (ρ.ne_pair x)

theorem w3ck_arcA_ne_self {v : ρ.M} (hv : w3ck_ArcA ρ x v) : v ≠ x := by
  intro h; subst h
  have h0 := hv.1
  rw [ρ.steps_self] at h0
  exact lt_irrefl 0 h0

theorem w3ck_arcA_ne_pair {v : ρ.M} (hv : w3ck_ArcA ρ x v) : v ≠ ρ.pair x := by
  intro h; subst h; exact lt_irrefl _ hv.2

theorem w3ck_arcA_smoothKeep {v : ρ.M} (hv : w3ck_ArcA ρ x v) : ρ.SmoothKeep x v :=
  (ρ.smoothKeep_iff x v).mpr ⟨w3ck_arcA_ne_self ρ x hv, w3ck_arcA_ne_pair ρ x hv⟩

include h1 in
/-- powers of the successor from `x`, identified by their position -/
theorem w3ck_pow_x_eq_iff (n k : ℕ) (hk : k < Fintype.card ρ.M) :
    (ρ.succ ^ n) x = (ρ.succ ^ k) x ↔ n % Fintype.card ρ.M = k := by
  constructor
  · intro h
    have h2 := ρ.steps_pow h1 x n
    rw [h, ρ.steps_pow h1 x k, Nat.mod_eq_of_lt hk] at h2
    exact h2.symm
  · intro h
    rw [← ρ.pow_mod_card_apply h1 x n, h]

include h1 in
theorem w3ck_pow_x_ne_self (n : ℕ) (h0 : n % Fintype.card ρ.M ≠ 0) : (ρ.succ ^ n) x ≠ x := by
  intro h
  apply h0
  have := (w3ck_pow_x_eq_iff ρ h1 x n 0 (ρ.card_M_pos x)).mp (by simpa using h)
  exact this

include h1 in
theorem w3ck_pow_x_ne_pair (n : ℕ) (hm : n % Fintype.card ρ.M ≠ ρ.steps x (ρ.pair x)) :
    (ρ.succ ^ n) x ≠ ρ.pair x := by
  intro h
  apply hm
  exact (w3ck_pow_x_eq_iff ρ h1 x n _ (ρ.steps_lt_card h1 x _)).mp (by rw [h, ρ.pow_steps h1])

include h1 in
/-- the reconnected walk from `succ x` follows `succ` while it stays on the arc `A` -/
theorem w3ck_reconnect_pow_succ_x (i : ℕ) (hi : i < ρ.steps x (ρ.pair x)) :
    ((ρ.reconnect x) ^ i) (ρ.succ x) = (ρ.succ ^ (i + 1)) x := by
  have hm := ρ.steps_lt_card h1 x (ρ.pair x)
  show ((ρ.succ * swap x (ρ.pair x)) ^ i) (ρ.succ x) = _
  rw [mul_swap_pow_apply_of_forall_ne ρ.succ x (ρ.pair x) (ρ.succ x) i ?_, pow_succ, Perm.mul_apply]
  intro j hj
  have hj' : (j + 1) % Fintype.card ρ.M = j + 1 := Nat.mod_eq_of_lt (by omega)
  have e : (ρ.succ ^ j) (ρ.succ x) = (ρ.succ ^ (j + 1)) x := by rw [pow_succ, Perm.mul_apply]
  rw [e]
  exact ⟨w3ck_pow_x_ne_self ρ h1 x _ (by omega), w3ck_pow_x_ne_pair ρ h1 x _ (by omega)⟩

include h1 in
/-- **the `s₁`-cycle of `τ x` is `(τ x, A)`**: every occurrence of the open arc `A` lies on it -/
theorem w3ck_reconnect_sameCycle_pair {v : ρ.M} (hv : w3ck_ArcA ρ x v) :
    (ρ.reconnect x).SameCycle (ρ.pair x) v := by
  refine ⟨ρ.steps x v, ?_⟩
  rw [zpow_natCast]
  obtain ⟨k, hk⟩ : ∃ k, ρ.steps x v = k + 1 := ⟨ρ.steps x v - 1, by have := hv.1; omega⟩
  rw [hk, pow_succ, Perm.mul_apply, Record.reconnect_apply_pair,
    w3ck_reconnect_pow_succ_x ρ h1 x k (by have := hv.2; omega), ← hk, ρ.pow_steps h1]

theorem w3ck_pair_arcA_iff (v : ρ.M) :
    w3ck_ArcA ρ (ρ.pair x) v ↔ ρ.ArcBetween (ρ.pair x) v x := by
  unfold w3ck_ArcA; rw [ρ.pair_invol]

include h1 in
/-- the `s₁`-cycle of `x` is `(x, B)` -/
theorem w3ck_reconnect_sameCycle_self {v : ρ.M} (hv : ρ.ArcBetween (ρ.pair x) v x) :
    (ρ.reconnect x).SameCycle x v := by
  have h := w3ck_reconnect_sameCycle_pair ρ h1 (ρ.pair x) ((w3ck_pair_arcA_iff ρ x v).mpr hv)
  rw [ρ.reconnect_pair, ρ.pair_invol] at h
  exact h

include h1 in
/-- every retained occurrence lies on `A` or on `B` -/
theorem w3ck_arc_dichotomy {v : ρ.M} (hv : ρ.SmoothKeep x v) :
    w3ck_ArcA ρ x v ∨ ρ.ArcBetween (ρ.pair x) v x := by
  obtain ⟨h1', h2'⟩ := (ρ.smoothKeep_iff x v).mp hv
  rcases ρ.arcBetween_or_arcBetween h1 (Ne.symm h1') (ρ.ne_pair x) h2' with h | h
  · exact Or.inl h
  · exact Or.inr ((ρ.arcBetween_rotate h1 x (ρ.pair x) v).mp h)

include h1 in
theorem w3ck_isSelfCrossing : ρ.IsSelfCrossing x :=
  Fintype.card_le_one_iff.mp (le_of_eq h1) _ _

include h1 in
/-- **the component of a retained occurrence of the smoothing is the class of `τ x` iff it lies on `A`** -/
theorem w3ck_smooth_comp_eq_pair_iff (w : (ρ.smooth x).M) :
    (ρ.smooth x).comp w = Sum.inl (Quotient.mk _ (ρ.pair x)) ↔ w3ck_ArcA ρ x w.1 := by
  rw [Record.smooth_comp]
  constructor
  · intro h
    have hsc : (ρ.reconnect x).SameCycle w.1 (ρ.pair x) := Quotient.exact (Sum.inl.inj h)
    rcases w3ck_arc_dichotomy ρ h1 x w.2 with hA | hB
    · exact hA
    · exfalso
      exact ρ.not_reconnect_sameCycle_pair_of_self x (w3ck_isSelfCrossing ρ h1 x)
        ((w3ck_reconnect_sameCycle_self ρ h1 x hB).trans hsc)
  · intro hA
    exact congrArg Sum.inl (Quotient.sound (w3ck_reconnect_sameCycle_pair ρ h1 x hA).symm)

include h1 in
theorem w3ck_smooth_comp_eq_self_iff (w : (ρ.smooth x).M) :
    (ρ.smooth x).comp w = Sum.inl (Quotient.mk _ x) ↔ ρ.ArcBetween (ρ.pair x) w.1 x := by
  rw [Record.smooth_comp]
  constructor
  · intro h
    have hsc : (ρ.reconnect x).SameCycle w.1 x := Quotient.exact (Sum.inl.inj h)
    rcases w3ck_arc_dichotomy ρ h1 x w.2 with hA | hB
    · exfalso
      exact ρ.not_reconnect_sameCycle_pair_of_self x (w3ck_isSelfCrossing ρ h1 x)
        (hsc.symm.trans (w3ck_reconnect_sameCycle_pair ρ h1 x hA).symm)
    · exact hB
  · intro hB
    exact congrArg Sum.inl (Quotient.sound (w3ck_reconnect_sameCycle_self ρ h1 x hB).symm)

include h1 in
/-- **self / mixed in the smoothed record, read on the parent circle**: a retained occurrence `w` is a self
crossing of `ρ^x` iff its two occurrences lie on the same open arc (`A = (x → τx)` or `B = (τx → x)`) —
i.e. iff `x` and `w` do NOT interlace in the Gauss word `(x A τx B)`. -/
theorem w3ck_isSelfCrossing_smooth_iff (w : (ρ.smooth x).M) :
    (ρ.smooth x).IsSelfCrossing w ↔ (w3ck_ArcA ρ x w.1 ↔ w3ck_ArcA ρ x (ρ.pair w.1)) := by
  unfold Record.IsSelfCrossing
  have hpv : ((ρ.smooth x).pair w).1 = ρ.pair w.1 := rfl
  rcases w3ck_arc_dichotomy ρ h1 x w.2 with hA | hB
  · have h1' : (ρ.smooth x).comp w = Sum.inl (Quotient.mk _ (ρ.pair x)) :=
      (w3ck_smooth_comp_eq_pair_iff ρ h1 x w).mpr hA
    rw [h1']
    rcases w3ck_arc_dichotomy ρ h1 x ((ρ.smooth x).pair w).2 with hA' | hB'
    · rw [hpv] at hA'
      have h2' : (ρ.smooth x).comp ((ρ.smooth x).pair w) = Sum.inl (Quotient.mk _ (ρ.pair x)) :=
        (w3ck_smooth_comp_eq_pair_iff ρ h1 x _).mpr (by rw [hpv]; exact hA')
      rw [h2']
      exact ⟨fun _ => ⟨fun _ => hA', fun _ => hA⟩, fun _ => rfl⟩
    · rw [hpv] at hB'
      have h2' : (ρ.smooth x).comp ((ρ.smooth x).pair w) = Sum.inl (Quotient.mk _ x) :=
        (w3ck_smooth_comp_eq_self_iff ρ h1 x _).mpr (by rw [hpv]; exact hB')
      rw [h2']
      have hne : ¬ w3ck_ArcA ρ x (ρ.pair w.1) := by
        intro hA'
        have := hA'.2
        have := hB'.1
        -- both `ArcA` and `ArcBetween (τx) · x` cannot hold: use `w3ck_smooth_comp_eq_*`
        have e1 : (ρ.smooth x).comp ((ρ.smooth x).pair w) = Sum.inl (Quotient.mk _ (ρ.pair x)) :=
          (w3ck_smooth_comp_eq_pair_iff ρ h1 x _).mpr (by rw [hpv]; exact hA')
        rw [h2'] at e1
        have hsc : (ρ.reconnect x).SameCycle x (ρ.pair x) := Quotient.exact (Sum.inl.inj e1)
        exact ρ.not_reconnect_sameCycle_pair_of_self x (w3ck_isSelfCrossing ρ h1 x) hsc
      constructor
      · intro h
        exfalso
        have hsc : (ρ.reconnect x).SameCycle (ρ.pair x) x := Quotient.exact (Sum.inl.inj h)
        exact ρ.not_reconnect_sameCycle_pair_of_self x (w3ck_isSelfCrossing ρ h1 x) hsc.symm
      · intro h
        exact absurd (h.mp hA) hne
  · have h1' : (ρ.smooth x).comp w = Sum.inl (Quotient.mk _ x) :=
      (w3ck_smooth_comp_eq_self_iff ρ h1 x w).mpr hB
    rw [h1']
    have hnA : ¬ w3ck_ArcA ρ x w.1 := by
      intro hA
      have e1 : (ρ.smooth x).comp w = Sum.inl (Quotient.mk _ (ρ.pair x)) :=
        (w3ck_smooth_comp_eq_pair_iff ρ h1 x w).mpr hA
      rw [h1'] at e1
      exact ρ.not_reconnect_sameCycle_pair_of_self x (w3ck_isSelfCrossing ρ h1 x)
        (Quotient.exact (Sum.inl.inj e1))
    rcases w3ck_arc_dichotomy ρ h1 x ((ρ.smooth x).pair w).2 with hA' | hB'
    · rw [hpv] at hA'
      have h2' : (ρ.smooth x).comp ((ρ.smooth x).pair w) = Sum.inl (Quotient.mk _ (ρ.pair x)) :=
        (w3ck_smooth_comp_eq_pair_iff ρ h1 x _).mpr (by rw [hpv]; exact hA')
      rw [h2']
      constructor
      · intro h
        exfalso
        exact ρ.not_reconnect_sameCycle_pair_of_self x (w3ck_isSelfCrossing ρ h1 x)
          (Quotient.exact (Sum.inl.inj h))
      · intro h
        exact absurd (h.mpr hA') hnA
    · rw [hpv] at hB'
      have h2' : (ρ.smooth x).comp ((ρ.smooth x).pair w) = Sum.inl (Quotient.mk _ x) :=
        (w3ck_smooth_comp_eq_self_iff ρ h1 x _).mpr (by rw [hpv]; exact hB')
      rw [h2']
      have hnA' : ¬ w3ck_ArcA ρ x (ρ.pair w.1) := by
        intro hA'
        have e1 : (ρ.smooth x).comp ((ρ.smooth x).pair w) = Sum.inl (Quotient.mk _ (ρ.pair x)) :=
          (w3ck_smooth_comp_eq_pair_iff ρ h1 x _).mpr (by rw [hpv]; exact hA')
        rw [h2'] at e1
        exact ρ.not_reconnect_sameCycle_pair_of_self x (w3ck_isSelfCrossing ρ h1 x)
          (Quotient.exact (Sum.inl.inj e1))
      exact ⟨fun _ => ⟨fun h => absurd h hnA, fun h => absurd h hnA'⟩, fun _ => rfl⟩

end W3CK_Rec


/-! ### K3. The bridge: the arcs of the lift's record, read as geometric interlacement on the parent
(`CV.arcBetween_iff_key` + `CV.geometricInterlaces_iff_unique`) -/

section W3CK_Bridge

open CV Carrier GeoCarrier

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

/-- `w` lies on the open arc `(v → τv)` of the lift's record iff the parent visit of `w` lies between the two
parent visits of `v` on `Γ` -/
theorem w3ck_arcA_iff_between (v w : (geoPositiveLift hn hG hT q).Γ.Visit) :
    w3ck_ArcA (geoPositiveLift hn hG hT q).record v w ↔
      geometricCrossingVisitBetween hG.cg (liftVisit hn hG hT q v).1 (liftVisit hn hG hT q v).2
        (visitTwin (liftVisit hn hG hT q v)).2 (liftVisit hn hG hT q w).1 (liftVisit hn hG hT q w).2 := by
  unfold w3ck_ArcA
  rw [Diagram.record_pair_apply, arcBetween_iff_key, liftVisit_twin]
  exact Iff.rfl

omit [NeZero n] in
/-- a visit and its twin have distinct positions in the fibre -/
theorem w3ck_visit_snd_ne_twin (u : Visit P) : u.2 ≠ (visitTwin u).2 := by
  intro h
  apply visitTwin_ne u
  exact congrArg (fun j : {k // k ∈ u.1.val} => (⟨u.1, j⟩ : Visit P)) h.symm

/-- **the record interlacement of two occurrences of the lift is the geometric interlacement of their
parent crossings**: exactly one of `w, τw` lies on `(v → τv)` iff the parents interlace on `Γ`. -/
theorem w3ck_interlaces_iff_arcs (v w : (geoPositiveLift hn hG hT q).Γ.Visit)
    (hxy : (liftVisit hn hG hT q v).1 ≠ (liftVisit hn hG hT q w).1) :
    GeometricInterlaces hG.cg (liftVisit hn hG hT q v).1 (liftVisit hn hG hT q w).1 ↔
      ¬ (w3ck_ArcA (geoPositiveLift hn hG hT q).record v w ↔
          w3ck_ArcA (geoPositiveLift hn hG hT q).record v ((geoPositiveLift hn hG hT q).record.pair w)) := by
  set B : {k // k ∈ (liftVisit hn hG hT q w).1.val} → Prop := fun j =>
    geometricCrossingVisitBetween hG.cg (liftVisit hn hG hT q v).1 (liftVisit hn hG hT q v).2
      (visitTwin (liftVisit hn hG hT q v)).2 (liftVisit hn hG hT q w).1 j with hB
  have e0 : w3ck_ArcA (geoPositiveLift hn hG hT q).record v w ↔ B (liftVisit hn hG hT q w).2 :=
    w3ck_arcA_iff_between hn hG hT q v w
  have e1 : w3ck_ArcA (geoPositiveLift hn hG hT q).record v ((geoPositiveLift hn hG hT q).record.pair w) ↔
      B (visitTwin (liftVisit hn hG hT q w)).2 := by
    rw [w3ck_arcA_iff_between, Diagram.record_pair_apply, liftVisit_twin]
    exact Iff.rfl
  have hx := w3ck_visit_snd_ne_twin (liftVisit hn hG hT q v)
  have hy := w3ck_visit_snd_ne_twin (liftVisit hn hG hT q w)
  rw [geometricInterlaces_iff_unique hG.cg _ _ _ _ hx, crossing_unique_visit_iff, e0, e1]
  constructor
  · rintro ⟨-, i, j, hij, hi, hj⟩ hiff
    rcases crossing_visits_exhaust _ _ _ hy i with rfl | rfl
    · rcases crossing_visits_exhaust _ _ _ hy j with rfl | rfl
      · exact hij rfl
      · exact hj (hiff.mp hi)
    · rcases crossing_visits_exhaust _ _ _ hy j with rfl | rfl
      · exact hj (hiff.mpr hi)
      · exact hij rfl
  · intro h
    refine ⟨hxy, ?_⟩
    by_cases h0 : B (liftVisit hn hG hT q w).2
    · exact ⟨_, _, hy, h0, fun h1 => h ⟨fun _ => h1, fun _ => h0⟩⟩
    · have h1 : B (visitTwin (liftVisit hn hG hT q w)).2 := by
        by_contra h1
        exact h ⟨fun h0' => absurd h0' h0, fun h1' => absurd h1' h1⟩
      exact ⟨_, _, hy.symm, h1, h0⟩

/-- the parent crossing of an occurrence of the lift is read off its double point -/
theorem w3ck_liftVisit_fst_of_point (v : (geoPositiveLift hn hG hT q).Γ.Visit) (c : Crossing P)
    (hc : (geoPositiveLift hn hG hT q).Γ.crossingPoint v.1 = crossingPoint c) :
    (liftVisit hn hG hT q v).1 = c := by
  rw [liftVisit_fst]
  apply crossingPoint_injective_of_geometry hG.cg
  rw [crossingPoint_liftCrossing, hc]

end W3CK_Bridge

/-! ### K4. Self / mixed transported along a record isomorphism -/

theorem w3ck_isSelfCrossing_iso {ρ ρ' : Record} (ι : RecordIso ρ ρ') (v : ρ.M) :
    ρ'.IsSelfCrossing (ι.Φ v) ↔ ρ.IsSelfCrossing v := by
  unfold Record.IsSelfCrossing
  rw [← ι.pair_eq, ι.comp_eq, ι.comp_eq]
  exact ι.e.injective.eq_iff

/-! ### K5. The two outer clauses at a carrier diagram, from an occurrence-compatible record clause -/

section W3CK_Site

open CV Carrier GeoCarrier

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P)
  {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)

/-- the carrier diagram is a knot diagram (`geoPositiveLift_componentCount`) -/
theorem w3ck_carrierDiagram_componentCount : (CV.carrierDiagram hn hG hS q).componentCount = 1 := rfl

/-- **the self/mixed status of `y` in `D^x`, decided by the geometric interlacement of the parents `c_x, c_y`**:
for a smoothing `D₀` of the carrier diagram `D` at `x` whose record clause is occurrence-compatible (it
carries the crossing of `D₀` at a double point to the crossing of `D` at the same double point,
`w3h_smooth_record_occ`'s shape) and a crossing `y` of `D₀` at the double point of `c_y`. -/
theorem w3ck_isSelfCrossing_smooth_iff_not_interlaces {cx cy : Crossing P} (hne : cx ≠ cy)
    (x : (CV.carrierDiagram hn hG hS q).Γ.Crossing)
    (hx : (CV.carrierDiagram hn hG hS q).Γ.crossingPoint x = crossingPoint cx)
    (D₀ : Diagram)
    (ι₀ : RecordIso D₀.record ((CV.carrierDiagram hn hG hS q).record.smooth
      ((CV.carrierDiagram hn hG hS q).overVisit x)))
    (hι₀ : ∀ v : D₀.Γ.Visit,
      (CV.carrierDiagram hn hG hS q).Γ.crossingPoint (ι₀.Φ v).1.1 = D₀.Γ.crossingPoint v.1)
    (y : D₀.Γ.Crossing) (hy : D₀.Γ.crossingPoint y = crossingPoint cy) :
    D₀.record.IsSelfCrossing (D₀.overVisit y) ↔ ¬ GeometricInterlaces hG.crossingGeometry cx cy := by
  have h1 : (CV.carrierDiagram hn hG hS q).record.componentCount = 1 :=
    CV.record_componentCount_one _ (w3ck_carrierDiagram_componentCount hn hG hS q)
  rw [← w3ck_isSelfCrossing_iso ι₀,
    w3ck_isSelfCrossing_smooth_iff _ h1 ((CV.carrierDiagram hn hG hS q).overVisit x) (ι₀.Φ (D₀.overVisit y))]
  have hcx : (liftVisit hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
      (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS) q
      ((CV.carrierDiagram hn hG hS q).overVisit x)).1 = cx :=
    w3ck_liftVisit_fst_of_point hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
      (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS) q _ cx hx
  have hcy : (liftVisit hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
      (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS) q (ι₀.Φ (D₀.overVisit y)).1).1 = cy := by
    apply w3ck_liftVisit_fst_of_point hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
      (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS) q _ cy
    rw [hι₀ (D₀.overVisit y)]
    exact hy
  have key := w3ck_interlaces_iff_arcs hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
    (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS) q ((CV.carrierDiagram hn hG hS q).overVisit x)
    (ι₀.Φ (D₀.overVisit y)).1 (by rw [hcx, hcy]; exact hne)
  rw [hcx, hcy] at key
  exact ⟨fun h hg => key.mp hg h, fun hg => not_not.mp (fun h => hg (key.mpr h))⟩

/-- **`knot_after_two` at a carrier diagram** (ESC §2): the parents interlace (the `K3` side's edge
`x_ef ∼ x_eg`), so `y` is mixed in `D^x` and the double smoothing is a knot. -/
theorem w3ck_knot_after_two_of {cx cy : Crossing P} (hxy : GeometricInterlaces hG.crossingGeometry cx cy)
    (x : (CV.carrierDiagram hn hG hS q).Γ.Crossing)
    (hx : (CV.carrierDiagram hn hG hS q).Γ.crossingPoint x = crossingPoint cx)
    (D₀ : Diagram)
    (ι₀ : RecordIso D₀.record ((CV.carrierDiagram hn hG hS q).record.smooth
      ((CV.carrierDiagram hn hG hS q).overVisit x)))
    (hι₀ : ∀ v : D₀.Γ.Visit,
      (CV.carrierDiagram hn hG hS q).Γ.crossingPoint (ι₀.Φ v).1.1 = D₀.Γ.crossingPoint v.1)
    (y : D₀.Γ.Crossing) (hy : D₀.Γ.crossingPoint y = crossingPoint cy)
    (J : Diagram) (ι₁ : RecordIso J.record (D₀.record.smooth (D₀.overVisit y))) :
    J.componentCount = 1 := by
  apply w3ck_componentCount_double_mixed (CV.carrierDiagram hn hG hS q) D₀ J
    (w3ck_carrierDiagram_componentCount hn hG hS q) _ ι₀ _ ι₁
  rw [w3ck_isSelfCrossing_smooth_iff_not_interlaces hn hG hS q hxy.1 x hx D₀ ι₀ hι₀ y hy]
  exact not_not.mpr hxy

/-- **the count of `three_components` at a carrier diagram** (ESC §2 "`D_L^{xy}` has three components"):
the parents do NOT interlace (the empty side), so `y` is a self crossing of `D^x`. -/
theorem w3ck_three_components_count_of {cx cy : Crossing P} (hne : cx ≠ cy)
    (hxy : ¬ GeometricInterlaces hG.crossingGeometry cx cy)
    (x : (CV.carrierDiagram hn hG hS q).Γ.Crossing)
    (hx : (CV.carrierDiagram hn hG hS q).Γ.crossingPoint x = crossingPoint cx)
    (D₀ : Diagram)
    (ι₀ : RecordIso D₀.record ((CV.carrierDiagram hn hG hS q).record.smooth
      ((CV.carrierDiagram hn hG hS q).overVisit x)))
    (hι₀ : ∀ v : D₀.Γ.Visit,
      (CV.carrierDiagram hn hG hS q).Γ.crossingPoint (ι₀.Φ v).1.1 = D₀.Γ.crossingPoint v.1)
    (y : D₀.Γ.Crossing) (hy : D₀.Γ.crossingPoint y = crossingPoint cy)
    (J : Diagram) (ι₁ : RecordIso J.record (D₀.record.smooth (D₀.overVisit y))) :
    J.componentCount = 3 := by
  apply w3ck_componentCount_double_self (CV.carrierDiagram hn hG hS q) D₀ J
    (w3ck_carrierDiagram_componentCount hn hG hS q) _ ι₀ _ ι₁
  rw [w3ck_isSelfCrossing_smooth_iff_not_interlaces hn hG hS q hne x hx D₀ ι₀ hι₀ y hy]
  exact hxy

end W3CK_Site


/-! ### K6. The two outer clauses in the form the ledger can consume (rule 3 finding: the frozen
`w3bi_knot_after_two` / `w3bi_three_components` quantify over EVERY relational oriented smoothing, whose
record is not identified by the library (only `smoothDiagram_record`); the ledger consumes them at the
smoothings of the weak (6) form and of `exists_smoothing_record_visit`, i.e. WITH record clauses.  The
occurrence-compatible clause for the first smoothing is `w3h_smooth_record_occ`'s shape.) -/

section W3CK_Config

open RProof CV Carrier GeoCarrier

/-- the occurrence-compatible record clause of a smoothing at `x` (`w3h_smooth_record_occ`'s shape) -/
def w3ck_SmoothRecordOcc (D : Diagram) (x : D.Γ.Crossing) (D₀ : Diagram) : Prop :=
  ∃ ι : RecordIso D₀.record (D.record.smooth (D.overVisit x)),
    ∀ v : D₀.Γ.Visit, D.Γ.crossingPoint (ι.Φ v).1.1 = D₀.Γ.crossingPoint v.1

/-- **`knot_after_two` with record clauses**: the corrected form of `w3bi_knot_after_two`. -/
def w3ck_knot_after_two_occ (D_H : Diagram) (pxH pyH : Plane) : Prop :=
  ∀ (x_H : D_H.Γ.Crossing), D_H.Γ.crossingPoint x_H = pxH →
    ∀ D_H0 : Diagram, IsOrientedSmoothing D_H x_H D_H0 → w3ck_SmoothRecordOcc D_H x_H D_H0 →
    ∀ (y_H : D_H0.Γ.Crossing), D_H0.Γ.crossingPoint y_H = pyH →
    ∀ J_H : Diagram, IsOrientedSmoothing D_H0 y_H J_H →
      Nonempty (RecordIso J_H.record (D_H0.record.smooth (D_H0.overVisit y_H))) → J_H.componentCount = 1

/-- **the count clause of `three_components` with record clauses** (`componentCount = 3`). -/
def w3ck_three_components_count_occ (D_L : Diagram) (pxL pyL : Plane) : Prop :=
  ∀ (x_L : D_L.Γ.Crossing), D_L.Γ.crossingPoint x_L = pxL →
    ∀ D_L0 : Diagram, IsOrientedSmoothing D_L x_L D_L0 → w3ck_SmoothRecordOcc D_L x_L D_L0 →
    ∀ (y_L : D_L0.Γ.Crossing), D_L0.Γ.crossingPoint y_L = pyL →
    ∀ J_L : Diagram, IsOrientedSmoothing D_L0 y_L J_L →
      Nonempty (RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y_L))) → J_L.componentCount = 3

/-- the identification clauses of `esc_three_components` (everything but the count): `2Λ` the total mixed
sign sum and the three knot restrictions carry the outer grouped polynomials -/
def w3ck_IdentData (J : Diagram) (Λ : ℕ) (fA fB fC : R) : Prop :=
  twoLambda J = 2 * (Λ : ℤ) ∧
    ∃ σ : Fin 3 ≃ Fin J.Γ.c, homfly (J.knotRestrict (σ 0)) = fA ∧ homfly (J.knotRestrict (σ 1)) = fB ∧
      homfly (J.knotRestrict (σ 2)) = fC

/-- `esc_three_components` = the count + the identification -/
theorem w3ck_esc_three_components_of {J : Diagram} {Λ : ℕ} {fA fB fC : R} (h3 : J.componentCount = 3)
    (hid : w3ck_IdentData J Λ fA fB fC) : esc_three_components J Λ fA fB fC :=
  ⟨h3, hid.1, hid.2⟩

/-- **the identification clause of `three_components` with record clauses** (the OPEN part, ESC §3
(9)–(11): the three components of `D_L^{xy}` are the outer carriers `A, B, C`; `Λ = lk(J)`). -/
def w3ck_three_components_ident_occ (D_L : Diagram) (pxL pyL : Plane) (Λ : ℕ) (fA fB fC : R) : Prop :=
  ∀ (x_L : D_L.Γ.Crossing), D_L.Γ.crossingPoint x_L = pxL →
    ∀ D_L0 : Diagram, IsOrientedSmoothing D_L x_L D_L0 → w3ck_SmoothRecordOcc D_L x_L D_L0 →
    ∀ (y_L : D_L0.Γ.Crossing), D_L0.Γ.crossingPoint y_L = pyL →
    ∀ J_L : Diagram, IsOrientedSmoothing D_L0 y_L J_L →
      Nonempty (RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y_L))) →
      w3ck_IdentData J_L Λ fA fB fC

/-- **`three_components` with record clauses**: the corrected form of `w3bi_three_components`. -/
def w3ck_three_components_occ (D_L : Diagram) (pxL pyL : Plane) (Λ : ℕ) (fA fB fC : R) : Prop :=
  ∀ (x_L : D_L.Γ.Crossing), D_L.Γ.crossingPoint x_L = pxL →
    ∀ D_L0 : Diagram, IsOrientedSmoothing D_L x_L D_L0 → w3ck_SmoothRecordOcc D_L x_L D_L0 →
    ∀ (y_L : D_L0.Γ.Crossing), D_L0.Γ.crossingPoint y_L = pyL →
    ∀ J_L : Diagram, IsOrientedSmoothing D_L0 y_L J_L →
      Nonempty (RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y_L))) →
      esc_three_components J_L Λ fA fB fC

theorem w3ck_three_components_occ_of {D_L : Diagram} {pxL pyL : Plane} {Λ : ℕ} {fA fB fC : R}
    (hc : w3ck_three_components_count_occ D_L pxL pyL)
    (hi : w3ck_three_components_ident_occ D_L pxL pyL Λ fA fB fC) :
    w3ck_three_components_occ D_L pxL pyL Λ fA fB fC :=
  fun x_L hx D_L0 hsm hocc y_L hy J_L hsmJ hJ =>
    w3ck_esc_three_components_of (hc x_L hx D_L0 hsm hocc y_L hy J_L hsmJ hJ)
      (hi x_L hx D_L0 hsm hocc y_L hy J_L hsmJ hJ)

/-- **`knot_after_two` at a carrier diagram whose parents interlace** -/
theorem w3ck_knot_after_two_occ_of {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    {cx cy : Crossing P} (hxy : GeometricInterlaces hG.crossingGeometry cx cy) :
    w3ck_knot_after_two_occ (CV.carrierDiagram hn hG hS q) (crossingPoint cx) (crossingPoint cy) := by
  intro x_H hx D_H0 _ hocc y_H hy J_H _ hJ
  obtain ⟨ι₀, hι₀⟩ := hocc
  obtain ⟨ι₁⟩ := hJ
  exact w3ck_knot_after_two_of hn hG hS q hxy x_H hx D_H0 ι₀ hι₀ y_H hy J_H ι₁

/-- **the count of `three_components` at a carrier diagram whose parents do not interlace** -/
theorem w3ck_three_components_count_occ_of {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n)
    (hG : CV.Generic P) {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) {cx cy : Crossing P} (hne : cx ≠ cy)
    (hxy : ¬ GeometricInterlaces hG.crossingGeometry cx cy) :
    w3ck_three_components_count_occ (CV.carrierDiagram hn hG hS q) (crossingPoint cx) (crossingPoint cy) := by
  intro x_L hx D_L0 _ hocc y_L hy J_L _ hJ
  obtain ⟨ι₀, hι₀⟩ := hocc
  obtain ⟨ι₁⟩ := hJ
  exact w3ck_three_components_count_of hn hG hS q hne hxy x_L hx D_L0 ι₀ hι₀ y_L hy J_L ι₁

/-- **`knot_after_two` at every configuration of the extended interface** (the `K3` side: `CompleteLocal`'s
edge `x_ef ∼ x_eg`). -/
theorem w3ck_knot_after_two {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (t : E.Parameter) (ht₀ : (t : ℝ) ≠ 0)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hK : CompleteLocal (geomAt E t ht₀) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQi : Q ∈ CV.Ind (geomAt E t ht₀))
    (q₀ : GeoComponent (geomAt E t ht₀) Q) :
    w3ck_knot_after_two_occ (CV.carrierDiagram hn (genericAt E t ht₀) hQi q₀)
      (crossingPoint (xPair hef)) (crossingPoint (xPair heg)) :=
  w3ck_knot_after_two_occ_of hn (genericAt E t ht₀) hQi q₀ hK.1

/-- **the count of `three_components` at every configuration of the extended interface** (the empty side
`t'`: `PRE_176_graphs_complementary` turns `CompleteLocal` at `t` into `EmptyLocal` at `t'`, whose first
clause is `¬ (x_ef ∼ x_eg)`). -/
theorem w3ck_three_components_count {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (δ : ℝ) (hL : LocalizationData E e f g δ) (t t' : E.Parameter) (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q' : Finset (Crossing (E.curve t'))} (hQi' : Q' ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀' : GeoComponent (geomAt E t' ht'.1) Q') :
    w3ck_three_components_count_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
      (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) := by
  have hE := (PRE_176_graphs_complementary hL t t' ht ht' hop hef heg hfg ((hs _).mp hef) ((hs _).mp heg)
    ((hs _).mp hfg)).mp hK
  exact w3ck_three_components_count_occ_of hn (genericAt E t' ht'.1) hQi' q₀'
    (P1.xPair_ef_ne_eg ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) hE.1

end W3CK_Config


/-! ### K7. The OUTER interface data in the corrected form and its assembly from the split + identification -/

section W3CK_Outer

open RProof CV Carrier GeoCarrier

/-- **the corrected OUTER data** (`w3bi_esc_outer` with the two outer clauses in their record-clause forms
`w3ck_knot_after_two_occ` / `w3ck_three_components_occ`; same binders, `esc_FullSplitData` byte-identical). -/
def w3ck_esc_outer_occ : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        w3ck_knot_after_two_occ (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg)) ∧
        w3ck_three_components_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)

/-- **BLACK BOX — the carrier split (unit SPLITB, `esc_FullSplitData`) together with the identification
clause of `three_components` at its `A, B, C, Λ`** (ESC §3 (9)–(11): `knotRestrict` of the three components
of `D_L^{xy}` ≅ the lifts of `A, B, C` — the `r176s_knotRestrictIso_i/_j` + `r176s_homfly_of_liftBlock`
pattern applied to the two arcs of `x_L` cut again at `y_L`; `twoLambda = 2Λ` from the writhe count (17)).
The count clause is NOT part of it (proved: `w3ck_three_components_count`). -/
def w3ck_split_ident : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        w3ck_three_components_ident_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)

/-! #### (W3C assembler, `w3cx_`) the OUTER data from SPLITA + SPLITB + SPLITC + KNOT, modulo ONE residue -/

/-- (W3C assembler) **SPLITB's core `w3cb_SplitCore` from SPLITA's core data** (abstract form): with the six-visit
data `D`, the core (each outer carrier owns one of the six visits, every one of them is on `A`, `B`, `C` or `Z`, and `Z`
owns exactly the three inner visits), the residue's sign table (every triangle visit on an outer carrier has turn `s`)
and parity (`#mixedSet = 2Λ`).  `localX` = the visit `X` owns (`hitX`) with its turn from the table; `central`: a
triangle visit not on `A, B, C` is on `Z`, whose marks are the inner visits, all on triangle crossings. -/
theorem w3cx_splitCore_of_core {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)
    {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    {Q : Finset (Crossing P)} (q₀ : GeoComponent hP Q)
    {A B C Z : GeoComponent hP (Q ∪ triangleCrossings P e f g)}
    (D : w3ca_SixData hP Q (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)))
    (core : w3ca_CoreData hP (Q ∪ triangleCrossings P e f g)
      (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)) A B C Z)
    {Λ : ℕ} {s : SignType} (hs0 : s ≠ 0)
    (htable : ∀ v : Visit P, v.1 ∈ triangleCrossings P e f g →
      (geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = A ∨
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = B ∨
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = C) →
      w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s)
    (hmixed : (w3cb_mixedSet hP Q (Q ∪ triangleCrossings P e f g) q₀).card = 2 * Λ) :
    w3cb_SplitCore hP e f g q₀ A B C Λ s := by
  have hsix : ∀ v : Visit P, (v = visitOn (xPair hef) e (mem_pair_left e f) ∨
      v = visitOn (xPair hef) f (mem_pair_right e f) ∨ v = visitOn (xPair heg) e (mem_pair_left e g) ∨
      v = visitOn (xPair heg) g (mem_pair_right e g) ∨ v = visitOn (xPair hfg) g (mem_pair_right f g) ∨
      v = visitOn (xPair hfg) f (mem_pair_left f g)) → v.1 ∈ triangleCrossings P e f g := by
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl))
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl))
  have hmem : ∀ w : Visit P, w.1 ∈ triangleCrossings P e f g →
      (w = visitOn (xPair hef) e (mem_pair_left e f) ∨ w = visitOn (xPair hef) f (mem_pair_right e f) ∨
      w = visitOn (xPair heg) e (mem_pair_left e g) ∨ w = visitOn (xPair heg) g (mem_pair_right e g) ∨
      w = visitOn (xPair hfg) g (mem_pair_right f g) ∨ w = visitOn (xPair hfg) f (mem_pair_left f g)) := by
    intro w hw
    rcases (P1.mem_triangleCrossings_iff hef heg hfg _).mp hw with h | h | h
    · rcases visit_eq_or_twin (visitOn (xPair hef) e (mem_pair_left e f)) w h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (h1.trans D.ta))
    · rcases visit_eq_or_twin (visitOn (xPair heg) e (mem_pair_left e g)) w h with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h1.trans D.tb))))
    · rcases visit_eq_or_twin (visitOn (xPair hfg) g (mem_pair_right f g)) w h with h1 | h1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h1.trans D.tc)))))
  obtain ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩ := core.distinct
  obtain ⟨zA, zB, zC, hzA, hzB, hzC, hiff⟩ := core.central
  refine ⟨hs0, ?_, ?_, ?_, hAB, hAC, hBC, ?_, hmixed⟩
  · obtain ⟨v, hv6, hvA⟩ := core.hitA
    exact ⟨v, hsix v hv6, hvA, htable v (hsix v hv6) (Or.inl hvA)⟩
  · obtain ⟨v, hv6, hvB⟩ := core.hitB
    exact ⟨v, hsix v hv6, hvB, htable v (hsix v hv6) (Or.inr (Or.inl hvB))⟩
  · obtain ⟨v, hv6, hvC⟩ := core.hitC
    exact ⟨v, hsix v hv6, hvC, htable v (hsix v hv6) (Or.inr (Or.inr hvC))⟩
  · intro w hw
    rcases core.six w (hmem w hw) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr fun m hm => ?_))
      rw [h] at hm
      rcases (hiff m).mp hm with rfl | rfl | rfl
      · exact ⟨zA, rfl, by rw [hzA]; exact hsix _ (Or.inl rfl)⟩
      · exact ⟨zB, rfl, by rw [hzB]; exact hsix _ (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨zC, rfl, by rw [hzC]; exact hsix _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩

/-- (W3C assembler) the turn `w3cb_turnAt` at a SELECTED visit is the crossing sign of its two edge labels
(`geoInEdge_visit`, `geoOutSlot_selected`: the incoming edge is the visit's own, the outgoing slot is the twin's). -/
theorem w3cx_turnAt_selected {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    w3cb_turnAt hP S (Sum.inr v) = crossingSign P v.2.val (visitTwin v).2.val := by
  unfold w3cb_turnAt crossingSign
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv]

/-- (W3C assembler) **the sign table (ESC (1c)) from SPLITA's core data and the alternating triple**: with `A, B, C, Z`
SPLITA's carriers (`w3ca_Ac/Bc/Cc/Zc`), every triangle visit owned by an outer carrier has the same nonzero turn `s`.
In the orientation pattern `σ a₁ = b₁` the outer visits are `a₁ : e → f`, `b₂ : g → e`, `c₂ : f → g` (turns
`cs(e,f)`, `cs(g,e) = −cs(e,g)`, `cs(f,g)`) and `Z` owns `a₂, b₁, c₁`; in the mirror pattern the outer visits are
`a₂ : f → e`, `b₁ : e → g`, `c₁ : g → f` and `Z` owns `a₁, b₂, c₂`.  The alternating triple `cs(e,f) = cs(f,g) =
−cs(e,g)` makes the three outer turns agree (`s = cs(e,f)` resp. `s = cs(e,g)`), `s ≠ 0` by
`CV.crossingSign_visit_twin_ne_zero`, and a visit owned by `Z` is owned by none of `A, B, C` (`distinct`; which
visits `Z` owns comes from the `central` clause). -/
theorem w3cx_sign_table_of_core {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    {Q : Finset (Crossing P)} {A B C Z : GeoComponent hP (Q ∪ triangleCrossings P e f g)}
    (D : w3ca_SixData hP Q (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)))
    (core : w3ca_CoreData hP (Q ∪ triangleCrossings P e f g)
      (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)) A B C Z)
    (hA : A = w3ca_Ac hP (Q ∪ triangleCrossings P e f g) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair hef) f (mem_pair_right e f)) (visitOn (xPair heg) e (mem_pair_left e g)))
    (hB : B = w3ca_Bc hP (Q ∪ triangleCrossings P e f g) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g)))
    (hC : C = w3ca_Cc hP (Q ∪ triangleCrossings P e f g) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair hfg) g (mem_pair_right f g))
      (visitOn (xPair hfg) f (mem_pair_left f g)))
    (hZ : Z = w3ca_Zc hP (Q ∪ triangleCrossings P e f g) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair hef) f (mem_pair_right e f)) (visitOn (xPair heg) e (mem_pair_left e g)))
    (halt : IsAlternating (crossingSign P e f) (crossingSign P e g) (crossingSign P f g)) :
    ∃ s : SignType, s ≠ 0 ∧ ∀ v : Visit P, v.1 ∈ triangleCrossings P e f g →
      (geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = A ∨
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = B ∨
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = C) →
      w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s := by
  obtain ⟨hfg_eq, heg_eq⟩ := halt
  have hsix : ∀ v : Visit P, (v = visitOn (xPair hef) e (mem_pair_left e f) ∨
      v = visitOn (xPair hef) f (mem_pair_right e f) ∨ v = visitOn (xPair heg) e (mem_pair_left e g) ∨
      v = visitOn (xPair heg) g (mem_pair_right e g) ∨ v = visitOn (xPair hfg) g (mem_pair_right f g) ∨
      v = visitOn (xPair hfg) f (mem_pair_left f g)) → v.1 ∈ Q ∪ triangleCrossings P e f g := by
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl)))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl)))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl)))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl)))
  have hmem : ∀ w : Visit P, w.1 ∈ triangleCrossings P e f g →
      (w = visitOn (xPair hef) e (mem_pair_left e f) ∨ w = visitOn (xPair hef) f (mem_pair_right e f) ∨
      w = visitOn (xPair heg) e (mem_pair_left e g) ∨ w = visitOn (xPair heg) g (mem_pair_right e g) ∨
      w = visitOn (xPair hfg) g (mem_pair_right f g) ∨ w = visitOn (xPair hfg) f (mem_pair_left f g)) := by
    intro w hw
    rcases (P1.mem_triangleCrossings_iff hef heg hfg _).mp hw with h | h | h
    · rcases visit_eq_or_twin (visitOn (xPair hef) e (mem_pair_left e f)) w h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (h1.trans D.ta))
    · rcases visit_eq_or_twin (visitOn (xPair heg) e (mem_pair_left e g)) w h with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h1.trans D.tb))))
    · rcases visit_eq_or_twin (visitOn (xPair hfg) g (mem_pair_right f g)) w h with h1 | h1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h1.trans D.tc)))))
  obtain ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩ := core.distinct
  obtain ⟨zA, zB, zC, hzA, hzB, hzC, hiff⟩ := core.central
  -- the six turns
  have hta₁ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hef) e (mem_pair_left e f))) =
      crossingSign P e f := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inl rfl)); rw [D.ta] at this; exact this
  have hta₂ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hef) f (mem_pair_right e f))) =
      crossingSign P f e := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inl rfl))); rw [D.ta'] at this; exact this
  have htb₁ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair heg) e (mem_pair_left e g))) =
      crossingSign P e g := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inr (Or.inl rfl)))); rw [D.tb] at this; exact this
  have htb₂ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair heg) g (mem_pair_right e g))) =
      crossingSign P g e := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    rw [D.tb'] at this; exact this
  have htc₁ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hfg) g (mem_pair_right f g))) =
      crossingSign P g f := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    rw [D.tc] at this; exact this
  have htc₂ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hfg) f (mem_pair_left f g))) =
      crossingSign P f g := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    rw [D.tc'] at this; exact this
  have hne : crossingSign P e f ≠ 0 := by
    have := CV.crossingSign_visit_twin_ne_zero hP (visitOn (xPair hef) e (mem_pair_left e f))
    rw [D.ta] at this; exact this
  have hnotZ : ∀ v : Visit P, (geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = A ∨
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = B ∨
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = C) →
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) ≠ Z := by
    rintro v (h | h | h) <;> rw [h] <;> assumption
  by_cases h : geoMarkSuccessor hP (Sum.inr (visitOn (xPair hef) e (mem_pair_left e f))) =
      Sum.inr (visitOn (xPair heg) e (mem_pair_left e g))
  · simp only [w3ca_Ac, w3ca_Bc, w3ca_Cc, w3ca_Zc, h, ↓reduceIte] at hA hB hC hZ
    -- `A = owner a₁`, `B = owner b₂`, `C = owner c₂`, `Z = owner a₂`; `Z` also owns `b₁`, `c₁`
    have hZb₁ : geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair heg) e (mem_pair_left e g))) = Z := by
      rcases visit_eq_or_twin (visitOn (xPair heg) e (mem_pair_left e g)) zB hzB with h1 | h1
      · rw [← h1]; exact (hiff _).mpr (Or.inr (Or.inl rfl))
      · exact absurd (hB.trans (by rw [← D.tb, ← h1]; exact (hiff _).mpr (Or.inr (Or.inl rfl)))) hBZ
    have hZc₁ : geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hfg) g (mem_pair_right f g))) = Z := by
      rcases visit_eq_or_twin (visitOn (xPair hfg) g (mem_pair_right f g)) zC hzC with h1 | h1
      · rw [← h1]; exact (hiff _).mpr (Or.inr (Or.inr rfl))
      · exact absurd (hC.trans (by rw [← D.tc, ← h1]; exact (hiff _).mpr (Or.inr (Or.inr rfl)))) hCZ
    refine ⟨crossingSign P e f, hne, fun v hv hown => ?_⟩
    rcases hmem v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hta₁
    · exact absurd hZ.symm (hnotZ _ hown)
    · exact absurd hZb₁ (hnotZ _ hown)
    · rw [htb₂, crossingSign_swap, heg_eq, neg_neg]
    · exact absurd hZc₁ (hnotZ _ hown)
    · rw [htc₂, ← hfg_eq]
  · simp only [w3ca_Ac, w3ca_Bc, w3ca_Cc, w3ca_Zc, h, ↓reduceIte] at hA hB hC hZ
    -- `A = owner a₂`, `B = owner b₁`, `C = owner c₁`, `Z = owner a₁`; `Z` also owns `b₂`, `c₂`
    have hZb₂ : geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair heg) g (mem_pair_right e g))) = Z := by
      rcases visit_eq_or_twin (visitOn (xPair heg) e (mem_pair_left e g)) zB hzB with h1 | h1
      · exact absurd (hB.trans (by rw [← h1]; exact (hiff _).mpr (Or.inr (Or.inl rfl)))) hBZ
      · rw [← D.tb, ← h1]; exact (hiff _).mpr (Or.inr (Or.inl rfl))
    have hZc₂ : geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hfg) f (mem_pair_left f g))) = Z := by
      rcases visit_eq_or_twin (visitOn (xPair hfg) g (mem_pair_right f g)) zC hzC with h1 | h1
      · exact absurd (hC.trans (by rw [← h1]; exact (hiff _).mpr (Or.inr (Or.inr rfl)))) hCZ
      · rw [← D.tc, ← h1]; exact (hiff _).mpr (Or.inr (Or.inr rfl))
    have hne' : crossingSign P e g ≠ 0 := by
      rw [heg_eq]; exact (by decide : ∀ a : SignType, a ≠ 0 → -a ≠ 0) _ hne
    refine ⟨crossingSign P e g, hne', fun v hv hown => ?_⟩
    rcases hmem v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hZ.symm (hnotZ _ hown)
    · rw [hta₂, crossingSign_swap, heg_eq]
    · exact htb₁
    · exact absurd hZb₂ (hnotZ _ hown)
    · rw [htc₁, crossingSign_swap, heg_eq, ← hfg_eq]
    · exact absurd hZc₂ (hnotZ _ hown)

/-- (W3C assembler) **the sign table at a configuration** for SPLITA's carriers: the alternating triple of `CompleteLocal`
at `t` (`w3e_alt_of_completeLocal`, via `GenericTableData.extreme_iff_alternating`) transported to `t'` by
`AV_EventRadius.sign_eq` (as unit SITE does), then `w3cx_sign_table_of_core` on `w3ca_split_config` / `w3ca_sixData_config`. -/
theorem w3cx_sign_table_at {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1)) :
    ∃ s : SignType, s ≠ 0 ∧
      (∀ v : Visit (E.curve t'), v.1 ∈ triangleCrossings (E.curve t') e f g →
          (geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) (Sum.inr v) =
              w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∨
            geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) (Sum.inr v) =
              w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∨
            geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) (Sum.inr v) =
              w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) →
          w3cb_turnAt (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) (Sum.inr v) = s) := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  have D := w3ca_sixData_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull'
  have halt : IsAlternating (crossingSign (E.curve t) e f) (crossingSign (E.curve t) e g)
      (crossingSign (E.curve t) f g) :=
    w3e_alt_of_completeLocal hGT t ht hef heg hfg hK
  have halt' : IsAlternating (crossingSign (E.curve t') e f) (crossingSign (E.curve t') e g)
      (crossingSign (E.curve t') f g) := by
    rw [hR.sign_eq t t' ht ht' e f hef, hR.sign_eq t t' ht ht' e g heg, hR.sign_eq t t' ht ht' f g hfg]
    exact halt
  exact w3cx_sign_table_of_core hn (geomAt E t' ht'.1) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) D core
    rfl rfl rfl rfl halt'

/-- (W3C assembler) **BLACK BOX — the residue of the OUTER data** after SPLITA (the carriers `w3ca_A/B/C/Z`,
`touching_iff`, `distinct`, `central_no_piece`, `central_rot`, and — via `w3cx_splitCorners_of_core` — SPLITC's corner
ledger), SPLITB (`writhe`, `mixed` from the core), SPLITC (`outer_alternative`, `uniform`) and KNOT (the two counts,
`w3ck_knot_after_two` / `w3ck_three_components_count`).  At every configuration of the extended interface there are
`Λ` such that (i) **the parity** (KNOT's bridge count, the analogue of `r176m_bridge_count`): the retained crossings of
`q₀'` whose two visits lie on different carriers of `Q' ∪ T'` (`w3cb_mixedSet`) number `2Λ`; (ii) **KNOT's
identification** for the same `Λ`: `twoLambda J_L = 2Λ` and the three knot restrictions of `J_L = D_L^{xy}` have the
HOMFLY polynomials of `A, B, C` (`w3ck_three_components_ident_occ`, record-clause form).  The sign table (ESC (1c)) is
PROVED above (`w3cx_sign_table_at`); everything else of `w3ck_split_ident` and of `w3cb_split_core` is PROVED from the
residue below. -/
def w3cx_outer_residue : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ Λ : ℕ,
        (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card = 2 * Λ ∧
        w3ck_three_components_ident_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))

/-! ## RESPAR (unit W3D, `w3dp_`): the PARITY clause of `w3cx_outer_residue` and the bridge `2Λ(J_L) = #mixedSet`
(report `W3D_RESPAR_REPORT.md`) -/


/-! ### RESPAR — record level: the two smoothings of non-interlacing chords -/
section W3DP_Rec
open Equiv

variable (ρ : Record) (h1 : ρ.componentCount = 1)

include h1 in
theorem w3dp_steps_succ (b m : ρ.M) :
    ρ.steps b (ρ.succ m) = (ρ.steps b m + 1) % Fintype.card ρ.M := by
  apply ρ.steps_eq_mod h1
  rw [pow_succ', Perm.mul_apply, ρ.pow_steps h1]

include h1 in
theorem w3dp_succ_ne_self (m : ρ.M) : ρ.succ m ≠ m := by
  intro h
  have hp : ∀ k : ℕ, (ρ.succ ^ k) m = m := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Perm.mul_apply, ih, h]
  have := ρ.pow_steps h1 m (ρ.pair m)
  rw [hp] at this
  exact ρ.ne_pair m this

include h1 in
theorem w3dp_two_le_card (m : ρ.M) : 2 ≤ Fintype.card ρ.M := by
  have h := ρ.steps_lt_card h1 m (ρ.pair m)
  have h0 := (ρ.steps_pos_iff h1 m (ρ.pair m)).mpr (ρ.ne_pair m)
  omega

include h1 in
theorem w3dp_steps_succ_self (b : ρ.M) : ρ.steps b (ρ.succ b) = 1 := by
  rw [w3dp_steps_succ ρ h1 b b, ρ.steps_self]
  exact Nat.mod_eq_of_lt (w3dp_two_le_card ρ h1 b)

include h1 in
/-- one forward step from the open arc `(b → τb)` stays on it or lands on `τ b` -/
theorem w3dp_arcA_succ {b m : ρ.M} (hm : w3ck_ArcA ρ b m) :
    ρ.succ m = ρ.pair b ∨ w3ck_ArcA ρ b (ρ.succ m) := by
  unfold w3ck_ArcA Record.ArcBetween at hm ⊢
  have hlt := ρ.steps_lt_card h1 b (ρ.pair b)
  have hs := w3dp_steps_succ ρ h1 b m
  rw [Nat.mod_eq_of_lt (by omega)] at hs
  by_cases he : ρ.steps b m + 1 = ρ.steps b (ρ.pair b)
  · left
    exact ρ.steps_inj h1 (hs.trans he)
  · right
    omega

include h1 in
/-- one forward step from the complementary open arc stays off `(b → τb)` or lands on `b` -/
theorem w3dp_not_arcA_succ {b m : ρ.M} (hm : ¬ w3ck_ArcA ρ b m) (hmb : m ≠ b) (hmp : m ≠ ρ.pair b) :
    ρ.succ m = b ∨ (¬ w3ck_ArcA ρ b (ρ.succ m) ∧ ρ.succ m ≠ ρ.pair b ∧ ρ.succ m ≠ b) := by
  unfold w3ck_ArcA Record.ArcBetween at hm ⊢
  have hlt := ρ.steps_lt_card h1 b m
  have hlt' := ρ.steps_lt_card h1 b (ρ.pair b)
  have h0 := (ρ.steps_pos_iff h1 b m).mpr (Ne.symm hmb)
  have hne := ρ.steps_ne_of_ne h1 b hmp
  have hs := w3dp_steps_succ ρ h1 b m
  by_cases hw : ρ.steps b m + 1 = Fintype.card ρ.M
  · left
    rw [hw, Nat.mod_self] at hs
    exact ρ.steps_inj h1 (hs.trans (ρ.steps_self b).symm)
  · right
    rw [Nat.mod_eq_of_lt (by omega)] at hs
    refine ⟨?_, ?_, ?_⟩
    · omega
    · intro he
      rw [he] at hs
      omega
    · intro he
      rw [he, ρ.steps_self] at hs
      omega

/-- the successor of the smoothing when the next occurrence is `τ x`: the jump to `succ x` -/
theorem w3dp_smooth_succ_val_of_succ_eq_pair (x : ρ.M) (v : (ρ.smooth x).M) (h : ρ.succ v.1 = ρ.pair x)
    (hx : ρ.succ x ≠ x) : ((ρ.smooth x).succ v).1 = ρ.succ x := by
  have hv := (ρ.smoothKeep_iff x v.1).mp v.2
  have h1' : ρ.reconnect x v.1 = ρ.pair x := by rw [ρ.reconnect_apply_of_smoothKeep x v.2, h]
  have h2 : ρ.reconnect x (ρ.reconnect x v.1) = ρ.succ x := by
    rw [h1', Record.reconnect_apply_pair]
  rw [← h2]
  apply firstReturn_apply_of_not_mem
  · rw [h1']; exact ρ.not_smoothKeep_pair x
  · rw [h2, Record.smoothKeep_iff]
    refine ⟨hx, fun hc => hv.1 ?_⟩
    exact ρ.succ.injective (h.trans hc.symm)

/-! #### orbit lemmas for a permutation of a finite type -/

theorem w3dp_pow_mem {α : Type*} (σ : Perm α) (p : α → Prop) (h : ∀ m, p m → p (σ m)) {m : α}
    (hm : p m) (k : ℕ) : p ((σ ^ k) m) := by
  induction k with
  | zero => simpa using hm
  | succ k ih => rw [pow_succ', Perm.mul_apply]; exact h _ ih

theorem w3dp_sameCycle_imp {α : Type*} [Finite α] (σ : Perm α) (p : α → Prop) (h : ∀ m, p m → p (σ m))
    {m m' : α} (hmm : σ.SameCycle m m') (hm : p m) : p m' := by
  obtain ⟨k, rfl⟩ := hmm.exists_nat_pow_eq
  exact w3dp_pow_mem σ p h hm k

/-- a permutation of a finite type mapping `p` into `p` preserves `p` in both directions -/
theorem w3dp_perm_iff {α : Type*} [Finite α] (σ : Perm α) (p : α → Prop) (h : ∀ m, p m → p (σ m)) (m : α) :
    p (σ m) ↔ p m := by
  refine ⟨fun hσ => ?_, h m⟩
  let f : {a // p a} → {a // p a} := fun a => ⟨σ a.1, h a.1 a.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (σ.injective (congrArg Subtype.val hab))
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hf) ⟨σ m, hσ⟩
  have : a.1 = m := σ.injective (congrArg Subtype.val ha)
  rw [← this]; exact a.2

theorem w3dp_sameCycle_iff {α : Type*} [Finite α] (σ : Perm α) (p : α → Prop) (h : ∀ m, p m → p (σ m))
    {m m' : α} (hmm : σ.SameCycle m m') : p m ↔ p m' :=
  ⟨w3dp_sameCycle_imp σ p h hmm, w3dp_sameCycle_imp σ p h hmm.symm⟩

/-! #### the two smoothings -/

section TwoSmooth

variable (x : ρ.M) (w : (ρ.smooth x).M)

/-- the chords of `x` and of `w₀ := w.1` do not interlace: both occurrences of `w₀` on one side of `x`
and both occurrences of `x` on one side of `w₀` -/
structure w3dp_NonInterlace : Prop where
  hw : w3ck_ArcA ρ x w.1 ↔ w3ck_ArcA ρ x (ρ.pair w.1)
  hx : w3ck_ArcA ρ w.1 x ↔ w3ck_ArcA ρ w.1 (ρ.pair x)

theorem w3dp_w_ne_x : w.1 ≠ x := ((ρ.smoothKeep_iff x w.1).mp w.2).1
theorem w3dp_w_ne_pair_x : w.1 ≠ ρ.pair x := ((ρ.smoothKeep_iff x w.1).mp w.2).2
theorem w3dp_pair_w_ne_x : ρ.pair w.1 ≠ x := fun h => w3dp_w_ne_pair_x ρ x w ((ρ.pair_eq_iff _ _).mp h)
theorem w3dp_pair_w_ne_pair_x : ρ.pair w.1 ≠ ρ.pair x := fun h => w3dp_w_ne_x ρ x w (ρ.pair_injective h)

theorem w3dp_smooth_pair_val : ((ρ.smooth x).pair w).1 = ρ.pair w.1 := rfl

include h1 in
/-- **Claim A**: the open arc `(x → τx)` is carried into itself by the second reconnection -/
theorem w3dp_reconnect_arcA_x (N : w3dp_NonInterlace ρ x w) (m : (ρ.smooth x).M)
    (hm : w3ck_ArcA ρ x m.1) : w3ck_ArcA ρ x (((ρ.smooth x).reconnect w) m).1 := by
  unfold Record.reconnect
  rw [Perm.mul_apply]
  have hsw : w3ck_ArcA ρ x (swap w ((ρ.smooth x).pair w) m).1 := by
    by_cases h1' : m = w
    · subst h1'; rw [swap_apply_left, w3dp_smooth_pair_val]; exact N.hw.mp hm
    · by_cases h2 : m = (ρ.smooth x).pair w
      · subst h2; rw [swap_apply_right]; rw [w3dp_smooth_pair_val] at hm; exact N.hw.mpr hm
      · rw [swap_apply_of_ne_of_ne h1' h2]; exact hm
  set m' := swap w ((ρ.smooth x).pair w) m with hm'
  rcases w3dp_arcA_succ ρ h1 hsw with h | h
  · rw [w3dp_smooth_succ_val_of_succ_eq_pair ρ x m' h (w3dp_succ_ne_self ρ h1 x)]
    unfold w3ck_ArcA Record.ArcBetween at hsw ⊢
    rw [w3dp_steps_succ_self ρ h1 x]
    omega
  · have hk : ρ.SmoothKeep x (ρ.succ m'.1) := by
      rw [Record.smoothKeep_iff]
      exact ⟨w3ck_arcA_ne_self ρ x h, w3ck_arcA_ne_pair ρ x h⟩
    rw [Record.smooth_succ_val_of_not_mem ρ x m' hk]
    exact h

include h1 in
/-- **Claim A'**: the complementary arc is carried into itself too -/
theorem w3dp_reconnect_not_arcA_x (N : w3dp_NonInterlace ρ x w) (m : (ρ.smooth x).M)
    (hm : ¬ w3ck_ArcA ρ x m.1) : ¬ w3ck_ArcA ρ x (((ρ.smooth x).reconnect w) m).1 := by
  unfold Record.reconnect
  rw [Perm.mul_apply]
  have hsw : ¬ w3ck_ArcA ρ x (swap w ((ρ.smooth x).pair w) m).1 := by
    by_cases h1' : m = w
    · subst h1'; rw [swap_apply_left, w3dp_smooth_pair_val]; exact fun h => hm (N.hw.mpr h)
    · by_cases h2 : m = (ρ.smooth x).pair w
      · subst h2; rw [swap_apply_right]; rw [w3dp_smooth_pair_val] at hm; exact fun h => hm (N.hw.mp h)
      · rw [swap_apply_of_ne_of_ne h1' h2]; exact hm
  set m' := swap w ((ρ.smooth x).pair w) m with hm'
  have hkeep := (ρ.smoothKeep_iff x m'.1).mp m'.2
  rcases w3dp_not_arcA_succ ρ h1 hsw hkeep.1 hkeep.2 with h | ⟨h, hne, hne'⟩
  · rw [Record.smooth_succ_val_of_succ_eq ρ x m' h (w3dp_succ_ne_self ρ h1 (ρ.pair x))]
    unfold w3ck_ArcA Record.ArcBetween
    rw [w3dp_steps_succ ρ h1 x (ρ.pair x)]
    have hlt := ρ.steps_lt_card h1 x (ρ.pair x)
    by_cases hw' : ρ.steps x (ρ.pair x) + 1 = Fintype.card ρ.M
    · rw [hw', Nat.mod_self]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have hk : ρ.SmoothKeep x (ρ.succ m'.1) := by
      rw [Record.smoothKeep_iff]; exact ⟨hne', hne⟩
    rw [Record.smooth_succ_val_of_not_mem ρ x m' hk]
    exact h

/-- the set `W`: the open arc `(w₀ → τw₀)` of `ρ` together with `τw₀` -/
def w3dp_W (m : (ρ.smooth x).M) : Prop := w3ck_ArcA ρ w.1 m.1 ∨ m.1 = ρ.pair w.1

include h1 in
/-- the smoothed successor of an occurrence of `(w₀ → τw₀)` (or of `w` itself) lies in `W` -/
theorem w3dp_smooth_succ_mem_W (N : w3dp_NonInterlace ρ x w) (u : (ρ.smooth x).M)
    (hu : w3ck_ArcA ρ w.1 u.1 ∨ u = w) : w3dp_W ρ x w ((ρ.smooth x).succ u) := by
  have hstep : ρ.succ u.1 = ρ.pair w.1 ∨ w3ck_ArcA ρ w.1 (ρ.succ u.1) := by
    rcases hu with hu | rfl
    · exact w3dp_arcA_succ ρ h1 hu
    · by_cases he : ρ.succ u.1 = ρ.pair u.1
      · exact Or.inl he
      · right
        have hne := ρ.steps_ne_of_ne h1 u.1 he
        unfold w3ck_ArcA Record.ArcBetween
        rw [w3dp_steps_succ_self ρ h1 u.1] at hne ⊢
        have h0 := (ρ.steps_pos_iff h1 u.1 (ρ.pair u.1)).mpr (ρ.ne_pair u.1)
        omega
  have hxW : w3ck_ArcA ρ w.1 x → w3dp_W ρ x w ((ρ.smooth x).succ u) → True := fun _ _ => trivial
  unfold w3dp_W
  by_cases hkx : ρ.succ u.1 = x
  · rw [Record.smooth_succ_val_of_succ_eq ρ x u hkx (w3dp_succ_ne_self ρ h1 (ρ.pair x))]
    have hax : w3ck_ArcA ρ w.1 x := by
      rcases hstep with h | h
      · exact absurd (hkx.symm.trans h) (w3dp_pair_w_ne_x ρ x w).symm
      · rw [hkx] at h; exact h
    have hap : w3ck_ArcA ρ w.1 (ρ.pair x) := N.hx.mp hax
    rcases w3dp_arcA_succ ρ h1 hap with h | h
    · exact Or.inr h
    · exact Or.inl h
  · by_cases hkp : ρ.succ u.1 = ρ.pair x
    · rw [w3dp_smooth_succ_val_of_succ_eq_pair ρ x u hkp (w3dp_succ_ne_self ρ h1 x)]
      have hap : w3ck_ArcA ρ w.1 (ρ.pair x) := by
        rcases hstep with h | h
        · exact absurd (hkp.symm.trans h) (w3dp_pair_w_ne_pair_x ρ x w).symm
        · rw [hkp] at h; exact h
      have hax : w3ck_ArcA ρ w.1 x := N.hx.mpr hap
      rcases w3dp_arcA_succ ρ h1 hax with h | h
      · exact Or.inr h
      · exact Or.inl h
    · have hk : ρ.SmoothKeep x (ρ.succ u.1) := by
        rw [Record.smoothKeep_iff]; exact ⟨hkx, hkp⟩
      rw [Record.smooth_succ_val_of_not_mem ρ x u hk]
      rcases hstep with h | h
      · exact Or.inr h
      · exact Or.inl h

include h1 in
/-- **Claim B**: `W` is carried into itself by the second reconnection -/
theorem w3dp_reconnect_W (N : w3dp_NonInterlace ρ x w) (m : (ρ.smooth x).M) (hm : w3dp_W ρ x w m) :
    w3dp_W ρ x w (((ρ.smooth x).reconnect w) m) := by
  unfold Record.reconnect
  rw [Perm.mul_apply]
  by_cases h2 : m = (ρ.smooth x).pair w
  · subst h2
    rw [swap_apply_right]
    exact w3dp_smooth_succ_mem_W ρ h1 x w N w (Or.inr rfl)
  · have hm' : w3ck_ArcA ρ w.1 m.1 := by
      rcases hm with h | h
      · exact h
      · exact absurd (Subtype.ext h) h2
    have h1' : m ≠ w := fun he => w3ck_arcA_ne_self ρ w.1 hm' (congrArg Subtype.val he)
    rw [swap_apply_of_ne_of_ne h1' h2]
    exact w3dp_smooth_succ_mem_W ρ h1 x w N m (Or.inl hm')

include h1 in
/-- the components of the first smoothing, compared: same circle iff same side of `x` -/
theorem w3dp_smooth_comp_eq_iff (u u' : (ρ.smooth x).M) :
    (ρ.smooth x).comp u = (ρ.smooth x).comp u' ↔ (w3ck_ArcA ρ x u.1 ↔ w3ck_ArcA ρ x u'.1) := by
  have hne : (Sum.inl (Quotient.mk _ x) : (ρ.smooth x).comps) ≠ Sum.inl (Quotient.mk _ (ρ.pair x)) := by
    intro h
    exact ρ.not_reconnect_sameCycle_pair_of_self x (w3ck_isSelfCrossing ρ h1 x)
      (Quotient.exact (Sum.inl.inj h))
  have hself : ∀ v : (ρ.smooth x).M, ¬ w3ck_ArcA ρ x v.1 →
      (ρ.smooth x).comp v = Sum.inl (Quotient.mk _ x) := by
    intro v hv
    rcases w3ck_arc_dichotomy ρ h1 x v.2 with h' | h'
    · exact absurd h' hv
    · exact (w3ck_smooth_comp_eq_self_iff ρ h1 x v).mpr h'
  by_cases hu : w3ck_ArcA ρ x u.1 <;> by_cases hu' : w3ck_ArcA ρ x u'.1
  · rw [(w3ck_smooth_comp_eq_pair_iff ρ h1 x u).mpr hu, (w3ck_smooth_comp_eq_pair_iff ρ h1 x u').mpr hu']
    exact iff_of_true rfl (iff_of_true hu hu')
  · rw [(w3ck_smooth_comp_eq_pair_iff ρ h1 x u).mpr hu, hself u' hu']
    exact iff_of_false (fun h => hne h.symm) (fun h => hu' (h.mp hu))
  · rw [hself u hu, (w3ck_smooth_comp_eq_pair_iff ρ h1 x u').mpr hu']
    exact iff_of_false hne (fun h => hu (h.mpr hu'))
  · rw [hself u hu, hself u' hu']
    exact iff_of_true rfl (iff_of_false hu hu')

include h1 in
/-- **the components of the double smoothing** `(ρ^x)^w` of two non-interlacing chords: two retained
occurrences lie on one circle iff they lie on the same side of `x` and — when on the side of `x` that
carries `w₀` — on the same side of `w₀`. -/
theorem w3dp_comp_eq_iff (N : w3dp_NonInterlace ρ x w) (m m' : ((ρ.smooth x).smooth w).M) :
    ((ρ.smooth x).smooth w).comp m = ((ρ.smooth x).smooth w).comp m' ↔
      ((w3ck_ArcA ρ x m.1.1 ↔ w3ck_ArcA ρ x m'.1.1) ∧
        ((w3ck_ArcA ρ x m.1.1 ↔ w3ck_ArcA ρ x w.1) → (w3ck_ArcA ρ w.1 m.1.1 ↔ w3ck_ArcA ρ w.1 m'.1.1))) := by
  rw [Record.smooth_comp_eq_iff]
  have hA : ∀ u : (ρ.smooth x).M, w3ck_ArcA ρ x u.1 → w3ck_ArcA ρ x (((ρ.smooth x).reconnect w) u).1 :=
    w3dp_reconnect_arcA_x ρ h1 x w N
  have hW : ∀ u, w3dp_W ρ x w u → w3dp_W ρ x w (((ρ.smooth x).reconnect w) u) :=
    w3dp_reconnect_W ρ h1 x w N
  have hm1 : m.1.1 ≠ ρ.pair w.1 := fun h =>
    (((ρ.smooth x).smoothKeep_iff w m.1).mp m.2).2 (Subtype.ext h)
  have hm1' : m'.1.1 ≠ ρ.pair w.1 := fun h =>
    (((ρ.smooth x).smoothKeep_iff w m'.1).mp m'.2).2 (Subtype.ext h)
  have hWm : w3dp_W ρ x w m.1 ↔ w3ck_ArcA ρ w.1 m.1.1 := ⟨fun h => h.resolve_right hm1, Or.inl⟩
  have hWm' : w3dp_W ρ x w m'.1 ↔ w3ck_ArcA ρ w.1 m'.1.1 := ⟨fun h => h.resolve_right hm1', Or.inl⟩
  constructor
  · intro hsc
    refine ⟨w3dp_sameCycle_iff _ (fun u : (ρ.smooth x).M => w3ck_ArcA ρ x u.1) hA hsc, fun _ => ?_⟩
    rw [← hWm, ← hWm']
    exact w3dp_sameCycle_iff _ (w3dp_W ρ x w) hW hsc
  · rintro ⟨hax, haw⟩
    have hcomp : (ρ.smooth x).comp m.1 = (ρ.smooth x).comp m'.1 :=
      (w3dp_smooth_comp_eq_iff ρ h1 x m.1 m'.1).mpr hax
    by_cases hc : (ρ.smooth x).comp m.1 = (ρ.smooth x).comp w
    · have haw' := haw ((w3dp_smooth_comp_eq_iff ρ h1 x m.1 w).mp hc)
      have hc' : (ρ.smooth x).comp m'.1 = (ρ.smooth x).comp w := hcomp.symm.trans hc
      have hor := (ρ.smooth x).reconnect_sameCycle_self_or_pair w m.1 (Or.inl hc)
      have hor' := (ρ.smooth x).reconnect_sameCycle_self_or_pair w m'.1 (Or.inl hc')
      have hWw : ¬ w3dp_W ρ x w w := by
        rintro (h | h)
        · exact w3ck_arcA_ne_self ρ w.1 h rfl
        · exact ρ.ne_pair w.1 h
      have hWtw : w3dp_W ρ x w ((ρ.smooth x).pair w) := Or.inr rfl
      by_cases hmW : w3ck_ArcA ρ w.1 m.1.1
      · have hmW' := haw'.mp hmW
        have h1s : ((ρ.smooth x).reconnect w).SameCycle m.1 ((ρ.smooth x).pair w) := by
          rcases hor with h | h
          · exact absurd ((w3dp_sameCycle_iff _ (w3dp_W ρ x w) hW h).mp (hWm.mpr hmW)) hWw
          · exact h
        have h2s : ((ρ.smooth x).reconnect w).SameCycle m'.1 ((ρ.smooth x).pair w) := by
          rcases hor' with h | h
          · exact absurd ((w3dp_sameCycle_iff _ (w3dp_W ρ x w) hW h).mp (hWm'.mpr hmW')) hWw
          · exact h
        exact h1s.trans h2s.symm
      · have hmW' : ¬ w3ck_ArcA ρ w.1 m'.1.1 := fun h => hmW (haw'.mpr h)
        have h1s : ((ρ.smooth x).reconnect w).SameCycle m.1 w := by
          rcases hor with h | h
          · exact h
          · exact absurd (hWm.mp ((w3dp_sameCycle_iff _ (w3dp_W ρ x w) hW h).mpr hWtw)) hmW
        have h2s : ((ρ.smooth x).reconnect w).SameCycle m'.1 w := by
          rcases hor' with h | h
          · exact h
          · exact absurd (hWm'.mp ((w3dp_sameCycle_iff _ (w3dp_W ρ x w) hW h).mpr hWtw)) hmW'
        exact h1s.trans h2s.symm
    · have hcp : (ρ.smooth x).comp m.1 ≠ (ρ.smooth x).comp ((ρ.smooth x).pair w) := by
        intro h
        apply hc
        rw [h]
        exact (w3dp_smooth_comp_eq_iff ρ h1 x _ _).mpr (by rw [w3dp_smooth_pair_val]; exact N.hw.symm)
      rw [(ρ.smooth x).reconnect_sameCycle_iff_of_comp_ne w m.1 hc hcp m'.1]
      exact hcomp

end TwoSmooth

end W3DP_Rec


/-! ### RESPAR — geometric side: the `Sf`-owner classes of the retained visits of `q₀` after inserting
three retained crossings, read as cyclic-order cells on the traversal circle -/
section W3DP_Geo
open Equiv SM.Carrier SM.GeoCarrier
attribute [local instance high] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)

/-- `m` lies on the open arc from the visit `a` forward to its twin (traversal order; definitionally
`cycBetween` of the geometric keys, `traversalBetween_iff_cycBetween`) -/
def w3dp_Cell (a m : Visit P) : Prop :=
  traversalBetween (geometricVisitPosition hP a) (geometricVisitPosition hP m)
    (geometricVisitPosition hP (visitTwin a))

theorem w3dp_cell_iff_key (a m : Visit P) :
    w3dp_Cell hP a m ↔ cycBetween (geometricVisitKey hP a) (geometricVisitKey hP m)
      (geometricVisitKey hP (visitTwin a)) := Iff.rfl

theorem w3dp_pos_ne_of_crossing_ne {m m' : Visit P} (h : m.1 ≠ m'.1) :
    geometricVisitPosition hP m ≠ geometricVisitPosition hP m' :=
  fun he => h (congrArg Sigma.fst (geometricVisitPosition_injective hP he))

theorem w3dp_pos_twin_ne (a : Visit P) :
    geometricVisitPosition hP a ≠ geometricVisitPosition hP (visitTwin a) :=
  fun he => visitTwin_ne a (geometricVisitPosition_injective hP he).symm

/-- the complementary cell: `m` off the two visits of `a` lies on `(a → τa)` iff not on `(τa → a)` -/
theorem w3dp_cell_complement {a m : Visit P} (hm : m.1 ≠ a.1) :
    w3dp_Cell hP a m ↔ ¬ w3dp_Cell hP (visitTwin a) m := by
  unfold w3dp_Cell
  rw [visitTwin_involutive]
  exact traversalBetween_complement (w3dp_pos_ne_of_crossing_ne hP (Ne.symm hm))
    (w3dp_pos_ne_of_crossing_ne hP (by rw [visitTwin_crossing]; exact hm)) (w3dp_pos_twin_ne hP a).symm

/-- **one insertion**: for a retained crossing `a.1` of a carrier of `T` (both visits owned by one carrier),
the `insert a.1 T`-owner of a visit `m` of that carrier, off the two visits of `a`, is the daughter of `τa`
iff `m` lies on the open arc `(a → τa)`, and the daughter of `a` iff not -/
theorem w3dp_owner_insert_iff (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T) (a : Visit P)
    (ha : a.1 ∉ T) (hc : geoOwner hP T (Sum.inr a) = geoOwner hP T (Sum.inr (visitTwin a)))
    (m : Visit P) (hm : geoOwner hP T (Sum.inr m) = geoOwner hP T (Sum.inr a)) (hma : m.1 ≠ a.1) :
    (geoOwner hP (insert a.1 T) (Sum.inr m) = geoOwner hP (insert a.1 T) (Sum.inr (visitTwin a)) ↔
        w3dp_Cell hP a m) ∧
    (geoOwner hP (insert a.1 T) (Sum.inr m) = geoOwner hP (insert a.1 T) (Sum.inr a) ↔
        ¬ w3dp_Cell hP a m) := by
  obtain ⟨k, A, B, hrot, -, -, -, hleft, hright, -, -⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI a ha hc
  have hmtw : (Sum.inr m : Mark P) ≠ Sum.inr (visitTwin a) := fun h =>
    hma (by rw [Sum.inr.inj h, visitTwin_crossing])
  have hmA : (Sum.inr m : Mark P) ≠ Sum.inr a := fun h => hma (by rw [Sum.inr.inj h])
  constructor
  · rw [hright (Sum.inr m), List.mem_cons, geoMarkList_filter_left_iff hP T _ k _ _ A B hrot]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact absurd h hmtw
      · exact h
    · intro h; exact Or.inr ⟨h, hm⟩
  · rw [hleft (Sum.inr m), List.mem_cons, geoMarkList_filter_right_iff hP T _ k _ _ A B hrot,
      w3dp_cell_complement hP hma, not_not]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact absurd h hmA
      · unfold w3dp_Cell; rw [visitTwin_involutive]; exact h
    · intro h
      unfold w3dp_Cell at h; rw [visitTwin_involutive] at h
      exact Or.inr ⟨h, hm⟩

/-- **the `Sf`-owner classes of the retained visits of `q₀`** after inserting three retained crossings
`a.1, b.1, c.1` (pairwise distinct, the resulting support `Sf` independent), for visits `m, m'` of `q₀` whose
crossings are not in `Sf`, given that one daughter `Z` of the third insertion owns only visits of the three
crossings: the owners agree iff `m, m'` lie on the same side of `a` and — when on the side of `a`
containing `b` — on the same side of `b`. -/
theorem w3dp_owner_eq_iff_three (Q : Finset (Crossing P)) (q₀ : GeoComponent hP Q) (a b c : Visit P)
    (Sf : Finset (Crossing P)) (hSfdef : Sf = insert c.1 (insert b.1 (insert a.1 Q)))
    (hSf : GeoIndependent hP Sf)
    (ha : a.1 ∈ geoCarrierCrossings hP Q q₀) (hb : b.1 ∈ geoCarrierCrossings hP Q q₀)
    (hc : c.1 ∈ geoCarrierCrossings hP Q q₀)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1)
    (Z : GeoComponent hP Sf)
    (hZ : ∀ m : Mark P, geoOwner hP Sf m = Z →
      ∃ v : Visit P, m = Sum.inr v ∧ (v.1 = a.1 ∨ v.1 = b.1 ∨ v.1 = c.1))
    (hZc : ∃ v : Visit P, v.1 = c.1 ∧ geoOwner hP Sf (Sum.inr v) = Z)
    (m m' : Visit P) (hm : m.1 ∈ geoCarrierCrossings hP Q q₀) (hm' : m'.1 ∈ geoCarrierCrossings hP Q q₀)
    (hmS : m.1 ∉ Sf) (hm'S : m'.1 ∉ Sf) :
    geoOwner hP Sf (Sum.inr m) = geoOwner hP Sf (Sum.inr m') ↔
      ((w3dp_Cell hP a m ↔ w3dp_Cell hP a m') ∧
        ((w3dp_Cell hP a m ↔ w3dp_Cell hP a b) → (w3dp_Cell hP b m ↔ w3dp_Cell hP b m'))) := by
  subst hSfdef
  revert Z hZ hZc hmS hm'S
  set S₁ := insert a.1 Q with hS₁
  set S₂ := insert b.1 S₁ with hS₂
  set Sf := insert c.1 S₂ with hSfdef
  intro Z hZ hZc hmS hm'S
  have hQ₁ : Q ⊆ S₁ := Finset.subset_insert _ _
  have hS₁₂ : S₁ ⊆ S₂ := Finset.subset_insert _ _
  have hS₂f : S₂ ⊆ Sf := Finset.subset_insert _ _
  have hS₁f : S₁ ⊆ Sf := hS₁₂.trans hS₂f
  have mono : ∀ {S S' : Finset (Crossing P)}, GeoIndependent hP S' → S ⊆ S' → GeoIndependent hP S :=
    fun hS' hSS x hx y hy hne => hS' x (hSS hx) y (hSS hy) hne
  have hQI : GeoIndependent hP Q := mono hSf (hQ₁.trans hS₁f)
  have hI₁ : GeoIndependent hP S₁ := mono hSf hS₁f
  have hI₂ : GeoIndependent hP S₂ := mono hSf hS₂f
  have hownQ : ∀ v : Visit P, v.1 ∈ geoCarrierCrossings hP Q q₀ → geoOwner hP Q (Sum.inr v) = q₀ :=
    fun v hv => ((mem_geoCarrierCrossings hP Q q₀ v.1).mp hv).2 v rfl
  have haSf : a.1 ∈ Sf := hS₁f (Finset.mem_insert_self _ _)
  have hbSf : b.1 ∈ Sf := hS₂f (Finset.mem_insert_self _ _)
  have hcSf : c.1 ∈ Sf := Finset.mem_insert_self _ _
  have hma : m.1 ≠ a.1 := fun h => hmS (h ▸ haSf)
  have hm'a : m'.1 ≠ a.1 := fun h => hm'S (h ▸ haSf)
  have hmb : m.1 ≠ b.1 := fun h => hmS (h ▸ hbSf)
  have hm'b : m'.1 ≠ b.1 := fun h => hm'S (h ▸ hbSf)
  -- Step 1: insert `a.1` into `Q`
  have haQ : a.1 ∉ Q := ((mem_geoCarrierCrossings hP Q q₀ a.1).mp ha).1
  have hca : geoOwner hP Q (Sum.inr a) = geoOwner hP Q (Sum.inr (visitTwin a)) := by
    rw [hownQ a ha, hownQ (visitTwin a) (by rw [visitTwin_crossing]; exact ha)]
  have hIQ := geoIndependent_inheritsMarkOrder hP hQI
  have step1 : ∀ v : Visit P, v.1 ∈ geoCarrierCrossings hP Q q₀ → v.1 ≠ a.1 →
      (geoOwner hP S₁ (Sum.inr v) = geoOwner hP S₁ (Sum.inr (visitTwin a)) ↔ w3dp_Cell hP a v) ∧
      (geoOwner hP S₁ (Sum.inr v) = geoOwner hP S₁ (Sum.inr a) ↔ ¬ w3dp_Cell hP a v) :=
    fun v hv hva => w3dp_owner_insert_iff hP Q hIQ a haQ hca v (by rw [hownQ v hv, hownQ a ha]) hva
  have hne1 : geoOwner hP S₁ (Sum.inr a) ≠ geoOwner hP S₁ (Sum.inr (visitTwin a)) :=
    (geoComponentForgetSwitch_fiber_affected hP Q hIQ a haQ hca).1
  have G1 : ∀ v v' : Visit P, v.1 ∈ geoCarrierCrossings hP Q q₀ → v'.1 ∈ geoCarrierCrossings hP Q q₀ →
      v.1 ≠ a.1 → v'.1 ≠ a.1 →
      (geoOwner hP S₁ (Sum.inr v) = geoOwner hP S₁ (Sum.inr v') ↔ (w3dp_Cell hP a v ↔ w3dp_Cell hP a v')) := by
    intro v v' hv hv' hva hv'a
    obtain ⟨h1, h2⟩ := step1 v hv hva
    obtain ⟨h1', h2'⟩ := step1 v' hv' hv'a
    by_cases hcv : w3dp_Cell hP a v <;> by_cases hcv' : w3dp_Cell hP a v'
    · rw [h1.mpr hcv, h1'.mpr hcv']; exact iff_of_true rfl (iff_of_true hcv hcv')
    · rw [h1.mpr hcv, h2'.mpr hcv']; exact iff_of_false (Ne.symm hne1) (fun h => hcv' (h.mp hcv))
    · rw [h2.mpr hcv, h1'.mpr hcv']; exact iff_of_false hne1 (fun h => hcv (h.mpr hcv'))
    · rw [h2.mpr hcv, h2'.mpr hcv']; exact iff_of_true rfl (iff_of_false hcv hcv')
  -- Step 2: insert `b.1` into `S₁`
  have hbS₁ : b.1 ∉ S₁ := by
    rw [hS₁, Finset.mem_insert, not_or]
    exact ⟨Ne.symm hab, ((mem_geoCarrierCrossings hP Q q₀ b.1).mp hb).1⟩
  have hcb : geoOwner hP S₁ (Sum.inr b) = geoOwner hP S₁ (Sum.inr (visitTwin b)) :=
    geoIndependent_remaining_pair_owners hP hSf S₁ hS₁f b hbSf hbS₁
  have hI₁' := geoIndependent_inheritsMarkOrder hP hI₁
  have step2 : ∀ v : Visit P, geoOwner hP S₁ (Sum.inr v) = geoOwner hP S₁ (Sum.inr b) → v.1 ≠ b.1 →
      (geoOwner hP S₂ (Sum.inr v) = geoOwner hP S₂ (Sum.inr (visitTwin b)) ↔ w3dp_Cell hP b v) ∧
      (geoOwner hP S₂ (Sum.inr v) = geoOwner hP S₂ (Sum.inr b) ↔ ¬ w3dp_Cell hP b v) :=
    fun v hv hvb => w3dp_owner_insert_iff hP S₁ hI₁' b hbS₁ hcb v hv hvb
  have hne2 : geoOwner hP S₂ (Sum.inr b) ≠ geoOwner hP S₂ (Sum.inr (visitTwin b)) :=
    (geoComponentForgetSwitch_fiber_affected hP S₁ hI₁' b hbS₁ hcb).1
  have G2 : ∀ v v' : Visit P, v.1 ∈ geoCarrierCrossings hP Q q₀ → v'.1 ∈ geoCarrierCrossings hP Q q₀ →
      v.1 ≠ a.1 → v'.1 ≠ a.1 → v.1 ≠ b.1 → v'.1 ≠ b.1 →
      (geoOwner hP S₂ (Sum.inr v) = geoOwner hP S₂ (Sum.inr v') ↔
        ((w3dp_Cell hP a v ↔ w3dp_Cell hP a v') ∧
          ((w3dp_Cell hP a v ↔ w3dp_Cell hP a b) → (w3dp_Cell hP b v ↔ w3dp_Cell hP b v')))) := by
    intro v v' hv hv' hva hv'a hvb hv'b
    have hG1 := G1 v v' hv hv' hva hv'a
    have hG1b := G1 v b hv hb hva (Ne.symm hab)
    have hG1b' := G1 v' b hv' hb hv'a (Ne.symm hab)
    by_cases hr : geoOwner hP S₁ (Sum.inr v) = geoOwner hP S₁ (Sum.inr b)
    · have hcab : w3dp_Cell hP a v ↔ w3dp_Cell hP a b := hG1b.mp hr
      by_cases hr' : geoOwner hP S₁ (Sum.inr v') = geoOwner hP S₁ (Sum.inr b)
      · have hcab' : w3dp_Cell hP a v' ↔ w3dp_Cell hP a b := hG1b'.mp hr'
        have hcvv' : w3dp_Cell hP a v ↔ w3dp_Cell hP a v' := hcab.trans hcab'.symm
        obtain ⟨h1, h2⟩ := step2 v hr hvb
        obtain ⟨h1', h2'⟩ := step2 v' hr' hv'b
        have key : geoOwner hP S₂ (Sum.inr v) = geoOwner hP S₂ (Sum.inr v') ↔
            (w3dp_Cell hP b v ↔ w3dp_Cell hP b v') := by
          by_cases hcv : w3dp_Cell hP b v <;> by_cases hcv' : w3dp_Cell hP b v'
          · rw [h1.mpr hcv, h1'.mpr hcv']; exact iff_of_true rfl (iff_of_true hcv hcv')
          · rw [h1.mpr hcv, h2'.mpr hcv']; exact iff_of_false (Ne.symm hne2) (fun h => hcv' (h.mp hcv))
          · rw [h2.mpr hcv, h1'.mpr hcv']; exact iff_of_false hne2 (fun h => hcv (h.mpr hcv'))
          · rw [h2.mpr hcv, h2'.mpr hcv']; exact iff_of_true rfl (iff_of_false hcv hcv')
        rw [key]
        exact ⟨fun h => ⟨hcvv', fun _ => h⟩, fun h => h.2 hcab⟩
      · have hS₁ne : geoOwner hP S₁ (Sum.inr v) ≠ geoOwner hP S₁ (Sum.inr v') :=
          fun h => hr' (h.symm.trans hr)
        have hcne : ¬ (w3dp_Cell hP a v ↔ w3dp_Cell hP a v') := fun h => hS₁ne (hG1.mpr h)
        exact iff_of_false (fun h => hS₁ne (geoOwner_eq_of_subset hP hI₂ hS₁₂ _ _ h)) (fun h => hcne h.1)
    · by_cases hr' : geoOwner hP S₁ (Sum.inr v') = geoOwner hP S₁ (Sum.inr b)
      · have hS₁ne : geoOwner hP S₁ (Sum.inr v) ≠ geoOwner hP S₁ (Sum.inr v') :=
          fun h => hr (h.trans hr')
        have hcne : ¬ (w3dp_Cell hP a v ↔ w3dp_Cell hP a v') := fun h => hS₁ne (hG1.mpr h)
        exact iff_of_false (fun h => hS₁ne (geoOwner_eq_of_subset hP hI₂ hS₁₂ _ _ h)) (fun h => hcne h.1)
      · have hun := geoOwner_insert_iff_of_unaffected hP S₁ b hbS₁ hcb (geoOwner hP S₁ (Sum.inr v)) hr
          (Sum.inr v) rfl (Sum.inr v')
        rw [eq_comm, hun, eq_comm, hG1]
        exact ⟨fun h => ⟨h, fun hc' => absurd (hG1b.mpr hc') hr⟩, fun h => h.1⟩
  -- Step 3: insert `c.1` into `S₂`; the daughter `Z` carries no retained visit off the triangle
  have hcS₂ : c.1 ∉ S₂ := by
    rw [hS₂, Finset.mem_insert, not_or, hS₁, Finset.mem_insert, not_or]
    exact ⟨Ne.symm hbc, Ne.symm hac, ((mem_geoCarrierCrossings hP Q q₀ c.1).mp hc).1⟩
  have hcc : geoOwner hP S₂ (Sum.inr c) = geoOwner hP S₂ (Sum.inr (visitTwin c)) :=
    geoIndependent_remaining_pair_owners hP hSf S₂ hS₂f c hcSf hcS₂
  have hI₂' := geoIndependent_inheritsMarkOrder hP hI₂
  have hZne : ∀ u : Visit P, u.1 ∉ Sf → geoOwner hP Sf (Sum.inr u) ≠ Z := by
    intro u hu hZu
    obtain ⟨w, hw, hw1⟩ := hZ _ hZu
    have huw : u = w := Sum.inr.inj hw
    subst huw
    apply hu
    rcases hw1 with h | h | h
    · rw [h]; exact haSf
    · rw [h]; exact hbSf
    · rw [h]; exact hcSf
  have G3 : ∀ v v' : Visit P, v.1 ∉ Sf → v'.1 ∉ Sf →
      (geoOwner hP Sf (Sum.inr v) = geoOwner hP Sf (Sum.inr v') ↔
        geoOwner hP S₂ (Sum.inr v) = geoOwner hP S₂ (Sum.inr v')) := by
    intro v v' hvS hv'S
    constructor
    · exact geoOwner_eq_of_subset hP hSf hS₂f _ _
    · intro h
      by_cases hr : geoOwner hP S₂ (Sum.inr v) = geoOwner hP S₂ (Sum.inr c)
      · obtain ⟨zc, hzc1, hzcZ⟩ := hZc
        have hv2 := w3cb_step_affected hP S₂ hI₂' c hcS₂ hcc (Sum.inr v) hr
        have hv'2 := w3cb_step_affected hP S₂ hI₂' c hcS₂ hcc (Sum.inr v') (h.symm.trans hr)
        have hZv := hZne v hvS
        have hZv' := hZne v' hv'S
        rcases visit_eq_or_twin c zc hzc1 with rfl | rfl
        · rcases hv2 with h1 | h1 <;> rcases hv'2 with h2 | h2
          · exact h1.trans h2.symm
          · exact absurd (h1.trans hzcZ) hZv
          · exact absurd (h2.trans hzcZ) hZv'
          · exact h1.trans h2.symm
        · rcases hv2 with h1 | h1 <;> rcases hv'2 with h2 | h2
          · exact h1.trans h2.symm
          · exact absurd (h2.trans hzcZ) hZv'
          · exact absurd (h1.trans hzcZ) hZv
          · exact h1.trans h2.symm
      · have hun := geoOwner_insert_iff_of_unaffected hP S₂ c hcS₂ hcc (geoOwner hP S₂ (Sum.inr v)) hr
          (Sum.inr v) rfl (Sum.inr v')
        exact (hun.mpr h.symm).symm
  rw [G3 m m' hmS hm'S]
  exact G2 m m' hm hm' hma hm'a hmb hm'b

end W3DP_Geo

/-! ### RESPAR — the count: `2Λ` of a positive diagram is its number of mixed crossings -/
section W3DP_Count
open scoped Classical

/-- a crossing between the two components `i, j` (the accepted `r176l_IsMixed`, restated) -/
def w3dp_IsMixed (D : Diagram) (i j : Fin D.Γ.c) (x : D.Γ.Crossing) : Prop :=
  ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
  ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)

/-- a crossing between two different components -/
def w3dp_Mixed (D : Diagram) (x : D.Γ.Crossing) : Prop := (D.overStrand x).1 ≠ (D.underStrand x).1

/-- `2ℓ_ij` as a sum over the mixed crossings (the accepted `SM.s7h_mixedSignSum_eq` /
`RProof.r176l_mixedSignSum_eq`, neither in this import closure; proof copied) -/
theorem w3dp_mixedSignSum_eq (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    mixedSignSum D i j =
      ∑ x ∈ Finset.univ.filter (w3dp_IsMixed D i j), (D.sign x : ℤ) := by
  unfold mixedSignSum
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun s t : D.Γ.Strand =>
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0)]
  have hmp : ∀ p : D.Γ.Strand × D.Γ.Strand,
      (if h : D.Γ.MixedPair i j p.1 p.2 then ((D.sign ⟨{p.1, p.2}, h.2.2⟩ : SignType) : ℤ) else 0) ≠ 0 →
      D.Γ.MixedPair i j p.1 p.2 := by
    intro p hne
    by_contra hm
    exact hne (dite_eq_right hm)
  refine Finset.sum_bij_ne_zero (fun p _ hne => ⟨{p.1, p.2}, (hmp p hne).2.2⟩) ?_ ?_ ?_ ?_
  · intro p _ hne
    have hm := hmp p hne
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases D.eq_over_under_of_crossing_eq hm.2.2 rfl with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · left; exact ⟨by rw [← hs]; exact hm.1, by rw [← ht]; exact hm.2.1⟩
    · right; exact ⟨by rw [← ht]; exact hm.2.1, by rw [← hs]; exact hm.1⟩
  · intro p₁ _ hne₁ p₂ _ hne₂ e
    have hm₁ := hmp p₁ hne₁
    have hm₂ := hmp p₂ hne₂
    have e' : ({p₁.1, p₁.2} : Finset D.Γ.Strand) = {p₂.1, p₂.2} := congrArg Subtype.val e
    have hs : p₁.1 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_self _ _
    have ht : p₁.2 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hs ht
    refine Prod.ext ?_ ?_
    · exact hs.resolve_right fun h => hij (by rw [← hm₁.1, h, hm₂.2.1])
    · exact ht.resolve_left fun h => hij (by rw [← hm₂.1, ← h, hm₁.2.1])
  · intro x hx _
    have hx' := (Finset.mem_filter.mp hx).2
    have hsgn : ((D.sign x : SignType) : ℤ) ≠ 0 := by
      rcases D.sign_eq_one_or_neg_one x with h | h <;> rw [h] <;> decide
    rcases hx' with ⟨ho, hu⟩ | ⟨ho, hu⟩
    · have hm : D.Γ.MixedPair i j (D.overStrand x) (D.underStrand x) :=
        ⟨ho, hu, by rw [← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.overStrand x, D.underStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.overStrand x, D.underStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext (D.val_eq_pair x).symm
        rw [e]; exact hsgn
      · exact Subtype.ext (D.val_eq_pair x).symm
    · have hm : D.Γ.MixedPair i j (D.underStrand x) (D.overStrand x) :=
        ⟨hu, ho, by rw [Finset.pair_comm, ← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.underStrand x, D.overStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.underStrand x, D.overStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
        rw [e]; exact hsgn
      · exact Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
  · intro p _ hne
    rw [dite_eq_left (hmp p hne)]

theorem w3dp_mixedSignSum_eq_card (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j)
    (hpos : ∀ x : D.Γ.Crossing, D.sign x = 1) :
    mixedSignSum D i j = ((Finset.univ.filter (w3dp_IsMixed D i j)).card : ℤ) := by
  rw [w3dp_mixedSignSum_eq D i j hij, Finset.card_eq_sum_ones, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [hpos x]; rfl

/-- over the ordered pairs `i < j`, a crossing is mixed between `i` and `j` exactly once when it is mixed,
never when it is a self crossing -/
theorem w3dp_pair_count (D : Diagram) (x : D.Γ.Crossing) :
    (∑ i : Fin D.Γ.c, ∑ j : Fin D.Γ.c,
        if i < j then (if w3dp_IsMixed D i j x then (1 : ℤ) else 0) else 0) =
      if w3dp_Mixed D x then 1 else 0 := by
  set p := (D.overStrand x).1 with hp
  set q := (D.underStrand x).1 with hq
  have hM : ∀ i j, w3dp_IsMixed D i j x ↔ ((p = i ∧ q = j) ∨ (p = j ∧ q = i)) := fun i j => Iff.rfl
  unfold w3dp_Mixed
  rw [← hp, ← hq]
  by_cases hpq : p = q
  · rw [ite_eq_right (fun h => h hpq)]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h1 h2
    · exfalso
      rcases (hM i j).mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact (ne_of_lt h1) (h3.symm.trans (hpq.trans h4))
      · exact (ne_of_lt h1) (h4.symm.trans (hpq.symm.trans h3))
    · rfl
    · rfl
  · rw [ite_eq_left hpq]
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · rw [Finset.sum_eq_single p]
      · rw [Finset.sum_eq_single q]
        · rw [ite_eq_left hlt, ite_eq_left ((hM p q).mpr (Or.inl ⟨rfl, rfl⟩))]
        · intro j _ hj
          split_ifs with h1 h2
          · exfalso
            rcases (hM p j).mp h2 with ⟨-, h4⟩ | ⟨h3, h4⟩
            · exact hj h4.symm
            · exact hpq h4.symm
          · rfl
          · rfl
        · intro h; exact absurd (Finset.mem_univ q) h
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro j _
        split_ifs with h1 h2
        · exfalso
          rcases (hM i j).mp h2 with ⟨h3, -⟩ | ⟨h3, h4⟩
          · exact hi h3.symm
          · rw [← h3, ← h4] at h1; exact lt_asymm hlt h1
        · rfl
        · rfl
      · intro h; exact absurd (Finset.mem_univ p) h
    · rw [Finset.sum_eq_single q]
      · rw [Finset.sum_eq_single p]
        · rw [ite_eq_left hlt, ite_eq_left ((hM q p).mpr (Or.inr ⟨rfl, rfl⟩))]
        · intro j _ hj
          split_ifs with h1 h2
          · exfalso
            rcases (hM q j).mp h2 with ⟨h3, -⟩ | ⟨h3, h4⟩
            · exact hpq h3
            · exact hj h3.symm
          · rfl
          · rfl
        · intro h; exact absurd (Finset.mem_univ p) h
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro j _
        split_ifs with h1 h2
        · exfalso
          rcases (hM i j).mp h2 with ⟨h3, h4⟩ | ⟨-, h4⟩
          · rw [← h3, ← h4] at h1; exact lt_asymm hlt h1
          · exact hi h4.symm
        · rfl
        · rfl
      · intro h; exact absurd (Finset.mem_univ q) h

/-- **`2Λ` of a positive diagram is the number of its mixed crossings** -/
theorem w3dp_twoLambda_eq_card_mixed (D : Diagram) (hpos : ∀ x : D.Γ.Crossing, D.sign x = 1) :
    twoLambda D = ((Finset.univ.filter (w3dp_Mixed D)).card : ℤ) := by
  unfold twoLambda twoLinking
  have h1 : ∀ i j : Fin D.Γ.c, (if i < j then mixedSignSum D i j else 0) =
      ∑ x : D.Γ.Crossing, if i < j then (if w3dp_IsMixed D i j x then (1 : ℤ) else 0) else 0 := by
    intro i j
    split_ifs with h
    · rw [w3dp_mixedSignSum_eq_card D i j (ne_of_lt h) hpos, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun x _ => by split_ifs <;> rfl
    · simp
  simp_rw [h1]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x _ => w3dp_pair_count D x), Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => by split_ifs <;> rfl

/-- `2Λ` is even (mp:zero-link, `SM.zero_link.half_sum_integer`) -/
theorem w3dp_twoLambda_even (D : Diagram) : ∃ Λ : ℤ, twoLambda D = 2 * Λ := by
  unfold twoLambda
  have : ∀ i j : Fin D.Γ.c, (2 : ℤ) ∣ (if i < j then twoLinking D i j else 0) := by
    intro i j
    split_ifs with h
    · obtain ⟨k, hk⟩ := zero_link.half_sum_integer D i j (ne_of_lt h)
      exact ⟨k, hk⟩
    · exact dvd_zero 2
  exact Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => this i j

end W3DP_Count


/-! ### RESPAR — the bridge at a carrier diagram: `2Λ(J) = #mixedSet` for the double smoothing `J` -/
section W3DP_Site
open CV Carrier GeoCarrier
attribute [local instance high] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P)
  {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)

/-- the carrier geometry of the lift (the first implicit argument of `CV.carrierDiagram`) -/
abbrev w3dp_cg : CarrierGeometry P := CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn)

/-- the independence of the support read on the lift's geometry (the second implicit argument) -/
abbrev w3dp_hT : GeoIndependent (w3dp_cg hn hG).cg S := CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS

/-- the parent visit of an occurrence of the carrier diagram -/
abbrev w3dp_lv (v : (CV.carrierDiagram hn hG hS q).Γ.Visit) : Visit P :=
  liftVisit hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q v

theorem w3dp_lv_twin (v : (CV.carrierDiagram hn hG hS q).Γ.Visit) :
    w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).record.pair v) = visitTwin (w3dp_lv hn hG hS q v) :=
  liftVisit_twin hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q v

theorem w3dp_lv_mem (v : (CV.carrierDiagram hn hG hS q).Γ.Visit) :
    (w3dp_lv hn hG hS q v).1 ∈ geoCarrierCrossings hG.crossingGeometry S q :=
  liftVisit_mem hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q v

theorem w3dp_lv_injective : Function.Injective (w3dp_lv hn hG hS q) :=
  liftVisit_injective hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q

/-- the record arc of the lift, read as a cell of the parent visits (`w3ck_arcA_iff_between`) -/
theorem w3dp_arcA_iff_cell (v m : (CV.carrierDiagram hn hG hS q).Γ.Visit) :
    w3ck_ArcA (CV.carrierDiagram hn hG hS q).record v m ↔
      w3dp_Cell hG.crossingGeometry (w3dp_lv hn hG hS q v) (w3dp_lv hn hG hS q m) :=
  w3ck_arcA_iff_between hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q v m

theorem w3dp_record_one : (CV.carrierDiagram hn hG hS q).record.componentCount = 1 :=
  CV.record_componentCount_one _ (geoPositiveLift_componentCount hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q)

/-- two occurrences of the lift with the same parent crossing are equal or paired -/
theorem w3dp_eq_or_pair_of_lv_eq {u u' : (CV.carrierDiagram hn hG hS q).Γ.Visit}
    (h : (w3dp_lv hn hG hS q u').1 = (w3dp_lv hn hG hS q u).1) :
    u' = u ∨ u' = (CV.carrierDiagram hn hG hS q).record.pair u := by
  rcases visit_eq_or_twin (w3dp_lv hn hG hS q u) (w3dp_lv hn hG hS q u') h with he | he
  · exact Or.inl (w3dp_lv_injective hn hG hS q he)
  · right
    apply w3dp_lv_injective hn hG hS q
    rw [w3dp_lv_twin]; exact he

variable (x : (CV.carrierDiagram hn hG hS q).Γ.Crossing)
  (w : ((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).M)

/-- the non-interlacing data of the two smoothed occurrences, from their parent crossings -/
theorem w3dp_site_nonInterlace
    (hne : (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)).1 ≠ (w3dp_lv hn hG hS q w.1).1)
    (hI : ¬ GeometricInterlaces hG.crossingGeometry
      (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)).1 (w3dp_lv hn hG hS q w.1).1) :
    w3dp_NonInterlace (CV.carrierDiagram hn hG hS q).record ((CV.carrierDiagram hn hG hS q).overVisit x) w := by
  constructor
  · have key := w3ck_interlaces_iff_arcs hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q
      ((CV.carrierDiagram hn hG hS q).overVisit x) w.1 hne
    exact not_not.mp (fun h => hI (key.mpr h))
  · have key := w3ck_interlaces_iff_arcs hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q w.1
      ((CV.carrierDiagram hn hG hS q).overVisit x) (Ne.symm hne)
    exact not_not.mp (fun h => hI (geometricInterlaces_symm _ (key.mpr h)))

/-- **the components of the double smoothing of the carrier diagram, read on the parent visits** -/
theorem w3dp_site_comp_iff
    (N : w3dp_NonInterlace (CV.carrierDiagram hn hG hS q).record ((CV.carrierDiagram hn hG hS q).overVisit x) w)
    (m m' : (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth w).M) :
    (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth w).comp m =
      (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth w).comp m' ↔
      ((w3dp_Cell hG.crossingGeometry (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)) (w3dp_lv hn hG hS q m.1.1) ↔
          w3dp_Cell hG.crossingGeometry (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)) (w3dp_lv hn hG hS q m'.1.1)) ∧
        ((w3dp_Cell hG.crossingGeometry (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)) (w3dp_lv hn hG hS q m.1.1) ↔
            w3dp_Cell hG.crossingGeometry (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)) (w3dp_lv hn hG hS q w.1)) →
          (w3dp_Cell hG.crossingGeometry (w3dp_lv hn hG hS q w.1) (w3dp_lv hn hG hS q m.1.1) ↔
            w3dp_Cell hG.crossingGeometry (w3dp_lv hn hG hS q w.1) (w3dp_lv hn hG hS q m'.1.1)))) := by
  rw [w3dp_comp_eq_iff _ (w3dp_record_one hn hG hS q) _ w N m m']
  simp only [w3dp_arcA_iff_cell hn hG hS q]

/-- the two sides of a record isomorphism agree on component equality -/
theorem w3dp_iso_comp_iff {ρ ρ' : Record} (ι : RecordIso ρ ρ') (a b : ρ.M) :
    ρ'.comp (ι.Φ a) = ρ'.comp (ι.Φ b) ↔ ρ.comp a = ρ.comp b := by
  rw [ι.comp_eq, ι.comp_eq]
  exact ι.e.injective.eq_iff

theorem w3dp_mixed_iff_comp (J : Diagram) (c : J.Γ.Crossing) :
    w3dp_Mixed J c ↔ J.record.comp (J.overVisit c) ≠ J.record.comp (J.underVisit c) := Iff.rfl

/-- **the bridge count at a carrier diagram**: for three pairwise non-interlacing retained crossings
`ca, cb, cc` of the carrier `q` of `S` with `Sf = S ∪ {ca, cb, cc}` independent and a carrier `Z` of `Sf`
owning only visits of the three (the central triangle), the double smoothing `J` of the carrier diagram at
the occurrences over `ca` and `cb` (with record clauses) has `2Λ(J)` equal to the number of retained
crossings of `q` outside `Sf` whose two visits have different `Sf`-carriers. -/
theorem w3dp_twoLambda_eq_card_mixedSet {ca cb cc : Crossing P}
    (hca : ca ∈ geoCarrierCrossings hG.crossingGeometry S q)
    (hcb : cb ∈ geoCarrierCrossings hG.crossingGeometry S q)
    (hcc : cc ∈ geoCarrierCrossings hG.crossingGeometry S q)
    (hab : ca ≠ cb) (hac : ca ≠ cc) (hbc : cb ≠ cc)
    (hIab : ¬ GeometricInterlaces hG.crossingGeometry ca cb)
    (hIac : ¬ GeometricInterlaces hG.crossingGeometry ca cc)
    (hIbc : ¬ GeometricInterlaces hG.crossingGeometry cb cc)
    {Sf : Finset (Crossing P)} (hSfdef : Sf = insert cc (insert cb (insert ca S)))
    (hSf : GeoIndependent hG.crossingGeometry Sf)
    (Z : GeoComponent hG.crossingGeometry Sf)
    (hZ : ∀ m : Mark P, geoOwner hG.crossingGeometry Sf m = Z →
      ∃ v : Visit P, m = Sum.inr v ∧ (v.1 = ca ∨ v.1 = cb ∨ v.1 = cc))
    (hZc : ∃ v : Visit P, v.1 = cc ∧ geoOwner hG.crossingGeometry Sf (Sum.inr v) = Z)
    (hx : (CV.carrierDiagram hn hG hS q).Γ.crossingPoint x = crossingPoint ca)
    (D₀ : Diagram)
    (ι₀ : RecordIso D₀.record ((CV.carrierDiagram hn hG hS q).record.smooth
      ((CV.carrierDiagram hn hG hS q).overVisit x)))
    (hι₀ : ∀ v : D₀.Γ.Visit,
      (CV.carrierDiagram hn hG hS q).Γ.crossingPoint (ι₀.Φ v).1.1 = D₀.Γ.crossingPoint v.1)
    (y : D₀.Γ.Crossing) (hy : D₀.Γ.crossingPoint y = crossingPoint cb)
    (J : Diagram) (ι₁ : RecordIso J.record (D₀.record.smooth (D₀.overVisit y))) :
    twoLambda J = ((w3cb_mixedSet hG.crossingGeometry S Sf q).card : ℤ) := by
  -- the two smoothed occurrences and their parents
  have ha1 : (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)).1 = ca :=
    w3ck_liftVisit_fst_of_point hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q _ ca hx
  have hb1 : (w3dp_lv hn hG hS q (ι₀.Φ (D₀.overVisit y)).1).1 = cb := by
    apply w3ck_liftVisit_fst_of_point hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q _ cb
    rw [hι₀ (D₀.overVisit y)]; exact hy
  have N := w3dp_site_nonInterlace hn hG hS q x (ι₀.Φ (D₀.overVisit y))
    (by rw [ha1, hb1]; exact hab) (by rw [ha1, hb1]; exact hIab)
  obtain ⟨ι⟩ : Nonempty (RecordIso J.record
      (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth
        (ι₀.Φ (D₀.overVisit y)))) := ⟨ι₁.trans (ι₀.smooth (D₀.overVisit y))⟩
  -- every crossing of `J` is positive
  have hpos : ∀ c : J.Γ.Crossing, J.sign c = 1 := by
    intro c
    have h := ι.sgn_eq (J.overVisit c)
    have h' : (CV.carrierDiagram hn hG hS q).sign (ι.Φ (J.overVisit c)).1.1.1 = J.sign c := h
    rw [← h']
    exact geoPositiveLift_sign hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q _
  rw [w3dp_twoLambda_eq_card_mixed J hpos]
  congr 1
  -- the parent visit of an occurrence of the double smoothing, and of its pair
  have hpair : ∀ z : (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth
      (ι₀.Φ (D₀.overVisit y))).M,
      w3dp_lv hn hG hS q ((((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair z).1.1 =
        visitTwin (w3dp_lv hn hG hS q z.1.1) := fun z => w3dp_lv_twin hn hG hS q z.1.1
  -- the parents of the retained occurrences are neither `ca` nor `cb`
  have hkept : ∀ z : (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth
      (ι₀.Φ (D₀.overVisit y))).M, (w3dp_lv hn hG hS q z.1.1).1 ≠ ca ∧ (w3dp_lv hn hG hS q z.1.1).1 ≠ cb := by
    intro z
    have hk1 := ((CV.carrierDiagram hn hG hS q).record.smoothKeep_iff _ z.1.1).mp z.1.2
    have hk2 := (((CV.carrierDiagram hn hG hS q).record.smooth _).smoothKeep_iff _ z.1).mp z.2
    constructor
    · intro h
      rw [← ha1] at h
      rcases w3dp_eq_or_pair_of_lv_eq hn hG hS q h with he | he
      · exact hk1.1 he
      · exact hk1.2 he
    · intro h
      rw [← hb1] at h
      rcases w3dp_eq_or_pair_of_lv_eq hn hG hS q h with he | he
      · exact hk2.1 (Subtype.ext he)
      · exact hk2.2 (Subtype.ext he)
  -- the third triangle visit and the geometric split data in the form of `w3dp_owner_eq_iff_three`
  obtain ⟨i, -, -⟩ := crossing_visits_exist cc
  have hSfdef' : Sf = insert (⟨cc, i⟩ : Visit P).1 (insert (w3dp_lv hn hG hS q (ι₀.Φ (D₀.overVisit y)).1).1
      (insert (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)).1 S)) := by
    rw [hSfdef, ha1, hb1]
  have hZ' : ∀ m : Mark P, geoOwner hG.crossingGeometry Sf m = Z → ∃ v : Visit P, m = Sum.inr v ∧
      (v.1 = (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)).1 ∨
        v.1 = (w3dp_lv hn hG hS q (ι₀.Φ (D₀.overVisit y)).1).1 ∨ v.1 = (⟨cc, i⟩ : Visit P).1) := by
    intro m hm
    obtain ⟨v, hv, h⟩ := hZ m hm
    exact ⟨v, hv, by rw [ha1, hb1]; exact h⟩
  have hZc' : ∃ v : Visit P, v.1 = (⟨cc, i⟩ : Visit P).1 ∧ geoOwner hG.crossingGeometry Sf (Sum.inr v) = Z := hZc
  have hcellMix : ∀ z : (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth
      (ι₀.Φ (D₀.overVisit y))).M, (w3dp_lv hn hG hS q z.1.1).1 ∉ Sf →
      ((((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).comp z ≠
          (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).comp ((((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair z) ↔
        geoOwner hG.crossingGeometry Sf (Sum.inr (w3dp_lv hn hG hS q z.1.1)) ≠
          geoOwner hG.crossingGeometry Sf (Sum.inr (visitTwin (w3dp_lv hn hG hS q z.1.1)))) := by
    intro z hz
    rw [Ne, Ne, w3dp_site_comp_iff hn hG hS q x _ N z _, hpair z,
      w3dp_owner_eq_iff_three hG.crossingGeometry S q _ _ ⟨cc, i⟩ Sf hSfdef' hSf (by rw [ha1]; exact hca) (by rw [hb1]; exact hcb) hcc
        (by rw [ha1, hb1]; exact hab) (by rw [ha1]; exact hac) (by rw [hb1]; exact hbc) Z hZ' hZc'
        (w3dp_lv hn hG hS q z.1.1) (visitTwin (w3dp_lv hn hG hS q z.1.1)) (w3dp_lv_mem hn hG hS q _)
        (by rw [visitTwin_crossing]; exact w3dp_lv_mem hn hG hS q _) hz (by rw [visitTwin_crossing]; exact hz)]
  -- an occurrence over `cc` is a self crossing of the double smoothing
  have hccNot : ∀ z : (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth
      (ι₀.Φ (D₀.overVisit y))).M, (w3dp_lv hn hG hS q z.1.1).1 = cc →
      (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).comp z =
        (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).comp ((((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair z) := by
    intro z hz
    rw [w3dp_site_comp_iff hn hG hS q x _ N z _, hpair z]
    have k1 := w3ck_interlaces_iff_arcs hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q
      ((CV.carrierDiagram hn hG hS q).overVisit x) z.1.1 (by rw [ha1, hz]; exact hac)
    have k2 := w3ck_interlaces_iff_arcs hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q
      (ι₀.Φ (D₀.overVisit y)).1 z.1.1 (by rw [hb1, hz]; exact hbc)
    have e1 := not_not.mp (fun h => hIac (by rw [← ha1, ← hz]; exact k1.mpr h))
    have e2 := not_not.mp (fun h => hIbc (by rw [← hb1, ← hz]; exact k2.mpr h))
    rw [w3dp_arcA_iff_cell, w3dp_arcA_iff_cell, w3dp_lv_twin] at e1 e2
    exact ⟨e1, fun _ => e2⟩
  -- the bijection: a mixed crossing of `J` ↦ the parent crossing of its over occurrence
  refine Finset.card_bij (fun c _ => (w3dp_lv hn hG hS q (ι.Φ (J.overVisit c)).1.1).1) ?_ ?_ ?_
  · intro c hc
    have hmixJ : w3dp_Mixed J c := (Finset.mem_filter.mp hc).2
    rw [w3dp_mixed_iff_comp] at hmixJ
    have hmix : (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).comp (ι.Φ (J.overVisit c)) ≠
        (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).comp
          ((((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair (ι.Φ (J.overVisit c))) := by
      have e : ι.Φ (J.underVisit c) =
          (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair (ι.Φ (J.overVisit c)) :=
        ι.pair_eq (J.overVisit c)
      rw [← e, ne_eq, w3dp_iso_comp_iff]
      exact hmixJ
    have hnotcc : (w3dp_lv hn hG hS q (ι.Φ (J.overVisit c)).1.1).1 ≠ cc := fun h => hmix (hccNot _ h)
    have hnotSf : (w3dp_lv hn hG hS q (ι.Φ (J.overVisit c)).1.1).1 ∉ Sf := by
      rw [hSfdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, not_or, not_or, not_or]
      exact ⟨hnotcc, (hkept _).2, (hkept _).1,
        ((mem_geoCarrierCrossings _ _ _ _).mp (w3dp_lv_mem hn hG hS q _)).1⟩
    simp only [w3cb_mixedSet, Finset.mem_filter]
    exact ⟨w3dp_lv_mem hn hG hS q _, hnotSf, w3dp_lv hn hG hS q _, visitTwin (w3dp_lv hn hG hS q _), rfl,
      visitTwin_crossing _, (hcellMix _ hnotSf).mp hmix⟩
  · intro c _ c' _ h
    rcases w3dp_eq_or_pair_of_lv_eq hn hG hS q h.symm with he | he
    · have : ι.Φ (J.overVisit c') = ι.Φ (J.overVisit c) := Subtype.ext (Subtype.ext he)
      exact congrArg Sigma.fst (ι.Φ.injective this).symm
    · have e : ι.Φ (J.underVisit c) =
          (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair (ι.Φ (J.overVisit c)) :=
        ι.pair_eq (J.overVisit c)
      have : ι.Φ (J.overVisit c') = ι.Φ (J.underVisit c) := by
        rw [e]
        exact Subtype.ext (Subtype.ext he)
      exact congrArg Sigma.fst (ι.Φ.injective this).symm
  · intro xx hxx
    simp only [w3cb_mixedSet, Finset.mem_filter] at hxx
    obtain ⟨hxg, hxS, v, w', hv, hw', hne⟩ := hxx
    obtain ⟨u, hu⟩ := liftVisit_surjective hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q (w := v) (by rw [hv]; exact hxg)
    have hlv : w3dp_lv hn hG hS q u = v := hu
    have hvSf : v.1 ∉ Sf := by rw [hv]; exact hxS
    have hu1 : (CV.carrierDiagram hn hG hS q).record.SmoothKeep ((CV.carrierDiagram hn hG hS q).overVisit x) u := by
      rw [Record.smoothKeep_iff]
      constructor
      · intro he; apply hvSf; rw [← hlv, he, ha1, hSfdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · intro he; apply hvSf; rw [← hlv, he, w3dp_lv_twin, visitTwin_crossing, ha1, hSfdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hu2 : ((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).SmoothKeep
        (ι₀.Φ (D₀.overVisit y))
        (⟨u, hu1⟩ : ((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).M) := by
      refine (Record.smoothKeep_iff _ _ _).mpr ⟨fun he => ?_, fun he => ?_⟩
      · apply hvSf
        have : u = (ι₀.Φ (D₀.overVisit y)).1 := congrArg Subtype.val he
        rw [← hlv, this, hb1, hSfdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · apply hvSf
        have : u = (CV.carrierDiagram hn hG hS q).record.pair (ι₀.Φ (D₀.overVisit y)).1 := congrArg Subtype.val he
        rw [← hlv, this, w3dp_lv_twin, visitTwin_crossing, hb1, hSfdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    -- the owners of `v` and its twin differ
    have hw'v : w' = visitTwin v := by
      rcases visit_eq_or_twin v w' (hw'.trans hv.symm) with he | he
      · exact absurd (by rw [he]) hne
      · exact he
    rw [hw'v] at hne
    have hzmix := (hcellMix ⟨⟨u, hu1⟩, hu2⟩ (by show (w3dp_lv hn hG hS q u).1 ∉ Sf; rw [hlv]; exact hvSf)).mpr
      (by show geoOwner hG.crossingGeometry Sf (Sum.inr (w3dp_lv hn hG hS q u)) ≠
            geoOwner hG.crossingGeometry Sf (Sum.inr (visitTwin (w3dp_lv hn hG hS q u)))
          rw [hlv]; exact hne)
    set z : (((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).smooth
      (ι₀.Φ (D₀.overVisit y))).M := ⟨⟨u, hu1⟩, hu2⟩ with hzdef
    set c : J.Γ.Crossing := (ι.Φ.symm z).1 with hcdef
    have e : ι.Φ (J.underVisit c) =
        (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair (ι.Φ (J.overVisit c)) :=
      ι.pair_eq (J.overVisit c)
    have hlvz : w3dp_lv hn hG hS q z.1.1 = v := hlv
    refine ⟨c, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [w3dp_mixed_iff_comp, ne_eq, ← w3dp_iso_comp_iff ι, e]
      rcases J.visit_eq_over_or_under (ι.Φ.symm z) with he | he
      · have hz' : ι.Φ (J.overVisit c) = z := by rw [← he]; exact Equiv.apply_symm_apply _ _
        rw [hz']
        exact hzmix
      · have hz' : ι.Φ (J.underVisit c) = z := by rw [← he]; exact Equiv.apply_symm_apply _ _
        have e' : ι.Φ (J.overVisit c) =
            (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair z := by
          rw [← hz', e, Record.pair_invol]
        rw [e', Record.pair_invol]
        exact fun h => hzmix h.symm
    · show (w3dp_lv hn hG hS q (ι.Φ (J.overVisit c)).1.1).1 = xx
      rcases J.visit_eq_over_or_under (ι.Φ.symm z) with he | he
      · have hz' : ι.Φ (J.overVisit c) = z := by rw [← he]; exact Equiv.apply_symm_apply _ _
        rw [hz', hlvz, hv]
      · have hz' : ι.Φ (J.underVisit c) = z := by rw [← he]; exact Equiv.apply_symm_apply _ _
        have e' : ι.Φ (J.overVisit c) =
            (((CV.carrierDiagram hn hG hS q).record.smooth _).smooth _).pair z := by
          rw [← hz', e, Record.pair_invol]
        rw [e', hpair, hlvz, visitTwin_crossing, hv]

end W3DP_Site

/-! ### RESPAR — the configuration level: the bridge in occurrence-clause form, the admissible double
smoothing, the PARITY clause (i) of `w3cx_outer_residue`, and the glue closing the residue from KNOT's
identification clause (ii) -/
section W3DP_Config
open RProof CV Carrier GeoCarrier Smoothing

/-- **the bridge count in occurrence-clause form**: for every admissible double smoothing `J_L` of `D_L` at
the double points `pxL` (first) and `pyL` (second), `2Λ(J_L) = N` (the binders of
`w3ck_three_components_ident_occ`) -/
def w3dp_bridge_occ (D_L : Diagram) (pxL pyL : Plane) (N : ℤ) : Prop :=
  ∀ (x_L : D_L.Γ.Crossing), D_L.Γ.crossingPoint x_L = pxL →
    ∀ D_L0 : Diagram, IsOrientedSmoothing D_L x_L D_L0 → w3ck_SmoothRecordOcc D_L x_L D_L0 →
    ∀ (y_L : D_L0.Γ.Crossing), D_L0.Γ.crossingPoint y_L = pyL →
    ∀ J_L : Diagram, IsOrientedSmoothing D_L0 y_L J_L →
      Nonempty (RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y_L))) →
      twoLambda J_L = N

/-- an admissible double smoothing of `D_L` at `pxL, pyL`: the data quantified by the occurrence clauses -/
def w3dp_Admissible (D_L : Diagram) (pxL pyL : Plane) (J_L : Diagram) : Prop :=
  ∃ (x_L : D_L.Γ.Crossing) (_ : D_L.Γ.crossingPoint x_L = pxL) (D_L0 : Diagram)
    (_ : IsOrientedSmoothing D_L x_L D_L0) (_ : w3ck_SmoothRecordOcc D_L x_L D_L0)
    (y_L : D_L0.Γ.Crossing) (_ : D_L0.Γ.crossingPoint y_L = pyL)
    (_ : IsOrientedSmoothing D_L0 y_L J_L),
    Nonempty (RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y_L)))

theorem w3dp_bridge_occ_spec {D_L : Diagram} {pxL pyL : Plane} {N : ℤ} (h : w3dp_bridge_occ D_L pxL pyL N)
    {J_L : Diagram} (hJ : w3dp_Admissible D_L pxL pyL J_L) : twoLambda J_L = N := by
  obtain ⟨x_L, hx, D_L0, hsm, hocc, y_L, hy, hsmJ, hJ⟩ := hJ
  exact h x_L hx D_L0 hsm hocc y_L hy J_L hsmJ hJ

theorem w3dp_ident_occ_spec {D_L : Diagram} {pxL pyL : Plane} {Λ : ℕ} {fA fB fC : R}
    (h : w3ck_three_components_ident_occ D_L pxL pyL Λ fA fB fC)
    {J_L : Diagram} (hJ : w3dp_Admissible D_L pxL pyL J_L) : w3ck_IdentData J_L Λ fA fB fC := by
  obtain ⟨x_L, hx, D_L0, hsm, hocc, y_L, hy, hsmJ, hJ⟩ := hJ
  exact h x_L hx D_L0 hsm hocc y_L hy J_L hsmJ hJ

section W3DP_ConfigUnion
variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- `Q ∪ T` as three insertions, with the (Classical) decidability the insertion lemmas of
`SM/GeoCarrierCount.lean` carry — the instance form of SPLITB's `CV.cvt165s_insert_eq`, stated once so that the
site theorems (elaborated under `Classical.propDecidable`) apply at the configuration -/
theorem w3dp_union_triangle_eq_classical {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) (Q : Finset (Crossing P)) :
    Q ∪ triangleCrossings P e f g =
      @insert _ _ (@Finset.instInsert _ fun x y => Classical.propDecidable (x = y)) (xPair hfg)
        (@insert _ _ (@Finset.instInsert _ fun x y => Classical.propDecidable (x = y)) (xPair heg)
          (@insert _ _ (@Finset.instInsert _ fun x y => Classical.propDecidable (x = y)) (xPair hef) Q)) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, P1.mem_triangleCrossings_iff hef heg hfg]
  tauto

end W3DP_ConfigUnion

section W3DP_ConfigSite
attribute [local instance high] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P)
  {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)

/-- **the bridge in occurrence-clause form at a carrier diagram** (the site theorem under the clauses) -/
theorem w3dp_bridge_occ_of {ca cb cc : Crossing P}
    (hca : ca ∈ geoCarrierCrossings hG.crossingGeometry S q)
    (hcb : cb ∈ geoCarrierCrossings hG.crossingGeometry S q)
    (hcc : cc ∈ geoCarrierCrossings hG.crossingGeometry S q)
    (hab : ca ≠ cb) (hac : ca ≠ cc) (hbc : cb ≠ cc)
    (hIab : ¬ GeometricInterlaces hG.crossingGeometry ca cb)
    (hIac : ¬ GeometricInterlaces hG.crossingGeometry ca cc)
    (hIbc : ¬ GeometricInterlaces hG.crossingGeometry cb cc)
    {Sf : Finset (Crossing P)} (hSfdef : Sf = insert cc (insert cb (insert ca S)))
    (hSf : GeoIndependent hG.crossingGeometry Sf)
    (Z : GeoComponent hG.crossingGeometry Sf)
    (hZ : ∀ m : Mark P, geoOwner hG.crossingGeometry Sf m = Z →
      ∃ v : Visit P, m = Sum.inr v ∧ (v.1 = ca ∨ v.1 = cb ∨ v.1 = cc))
    (hZc : ∃ v : Visit P, v.1 = cc ∧ geoOwner hG.crossingGeometry Sf (Sum.inr v) = Z) :
    w3dp_bridge_occ (CV.carrierDiagram hn hG hS q) (crossingPoint ca) (crossingPoint cb)
      ((w3cb_mixedSet hG.crossingGeometry S Sf q).card : ℤ) := by
  intro x_L hx D_L0 _ hocc y_L hy J_L _ hJ
  obtain ⟨ι₀, hι₀⟩ := hocc
  obtain ⟨ι₁⟩ := hJ
  exact w3dp_twoLambda_eq_card_mixedSet hn hG hS q x_L hca hcb hcc hab hac hbc hIab hIac hIbc hSfdef hSf Z hZ hZc
    hx D_L0 ι₀ hι₀ y_L hy J_L ι₁

/-- the carrier diagram has a crossing over every retained crossing of the carrier -/
theorem w3dp_exists_crossing_over {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry S q) :
    ∃ x : (CV.carrierDiagram hn hG hS q).Γ.Crossing,
      (CV.carrierDiagram hn hG hS q).Γ.crossingPoint x = crossingPoint c := by
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  obtain ⟨v, hv⟩ := liftVisit_surjective hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q (w := ⟨c, i⟩) hc
  have hlv : w3dp_lv hn hG hS q v = ⟨c, i⟩ := hv
  refine ⟨v.1, ?_⟩
  rw [← crossingPoint_liftCrossing hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q v,
    ← liftVisit_fst hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q v]
  show crossingPoint (w3dp_lv hn hG hS q v).1 = crossingPoint c
  rw [hlv]

/-- **an admissible double smoothing exists** at two distinct retained crossings: the constructed
`smoothDiagram`s, with the record clauses `w3h_smooth_record_occ` and `smoothDiagram_record` -/
theorem w3dp_exists_admissible {ca cb : Crossing P}
    (hca : ca ∈ geoCarrierCrossings hG.crossingGeometry S q)
    (hcb : cb ∈ geoCarrierCrossings hG.crossingGeometry S q) (hab : ca ≠ cb) :
    ∃ J_L : Diagram, w3dp_Admissible (CV.carrierDiagram hn hG hS q) (crossingPoint ca) (crossingPoint cb) J_L := by
  obtain ⟨x, hx⟩ := w3dp_exists_crossing_over hn hG hS q hca
  obtain ⟨ι, hι⟩ := w3h_smooth_record_occ (CV.carrierDiagram hn hG hS q) x
    (eps (CV.carrierDiagram hn hG hS q) x) (eps_small (CV.carrierDiagram hn hG hS q) x)
  obtain ⟨i, -, -⟩ := crossing_visits_exist cb
  obtain ⟨u, hu⟩ := liftVisit_surjective hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q (w := ⟨cb, i⟩) hcb
  have hlv : w3dp_lv hn hG hS q u = ⟨cb, i⟩ := hu
  have hxa : (w3dp_lv hn hG hS q ((CV.carrierDiagram hn hG hS q).overVisit x)).1 = ca :=
    w3ck_liftVisit_fst_of_point hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q _ ca hx
  have hk : (CV.carrierDiagram hn hG hS q).record.SmoothKeep ((CV.carrierDiagram hn hG hS q).overVisit x) u := by
    rw [Record.smoothKeep_iff]
    constructor
    · intro he
      apply hab
      have : (w3dp_lv hn hG hS q u).1 = cb := by rw [hlv]
      rw [← hxa, ← this, he]
    · intro he
      apply hab
      have : (w3dp_lv hn hG hS q u).1 = cb := by rw [hlv]
      rw [← hxa, ← this, he, w3dp_lv_twin, visitTwin_crossing]
  let z : (smoothDiagram (CV.carrierDiagram hn hG hS q) x (eps _ x) (eps_small _ x)).Γ.Visit := ι.Φ.symm ⟨u, hk⟩
  have h3 : (CV.carrierDiagram hn hG hS q).Γ.crossingPoint u.1 = crossingPoint cb := by
    rw [← crossingPoint_liftCrossing hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q u,
      ← liftVisit_fst hn (w3dp_cg hn hG) (w3dp_hT hn hG hS) q u]
    show crossingPoint (w3dp_lv hn hG hS q u).1 = crossingPoint cb
    rw [hlv]
  have h2 : (ι.Φ z).1 = u :=
    congrArg Subtype.val (Equiv.apply_symm_apply ι.Φ
      (⟨u, hk⟩ : ((CV.carrierDiagram hn hG hS q).record.smooth ((CV.carrierDiagram hn hG hS q).overVisit x)).M))
  have hz : (smoothDiagram (CV.carrierDiagram hn hG hS q) x (eps _ x) (eps_small _ x)).Γ.crossingPoint z.1 =
      crossingPoint cb := by
    rw [← hι z, h2]
    exact h3
  exact ⟨smoothDiagram _ z.1 (eps _ z.1) (eps_small _ z.1), x, hx, _,
    isOrientedSmoothing_smoothDiagram _ x _ _, ⟨ι, hι⟩, z.1, hz,
    isOrientedSmoothing_smoothDiagram _ z.1 _ _, smoothDiagram_record _ z.1 _ _⟩

end W3DP_ConfigSite

section W3DP_ConfigEvent
variable {n : ℕ} [NeZero n]

/-- **the bridge at every configuration of the extended interface**: the three triangle crossings are retained
on `q₀'` (`w3cb_triangle_on_contact_at`), pairwise non-interlacing on the empty side
(`PRE_176_graphs_complementary`), `Q' ∪ T'` is independent, and SPLITA's central triangle `w3ca_Z` owns exactly
the three inner visits (`w3ca_split_config`, `central`) -/
theorem w3dp_bridge_at (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q))
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀') :
    w3dp_bridge_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
      (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg)))
      ((w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)
        (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card : ℤ) := by
  have hef' := (hs _).mp hef
  have heg' := (hs _).mp heg
  have hfg' := (hs _).mp hfg
  have htri := w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'
  have hT := P1.mem_triangleCrossings_iff hef' heg' hfg'
  have hE := (PRE_176_graphs_complementary hL t t' ht ht' hop hef heg hfg hef' heg' hfg').mp hK
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ := w3ca_split_config hL ht' hef' heg' hfg' hQ' hfull' hS'
  obtain ⟨zA, zB, zC, hzA, hzB, hzC, hZiff⟩ := core.central
  exact w3dp_bridge_occ_of hn (genericAt E t' ht'.1) hQi' q₀' (htri ((hT _).mpr (Or.inl rfl)))
    (htri ((hT _).mpr (Or.inr (Or.inl rfl)))) (htri ((hT _).mpr (Or.inr (Or.inr rfl))))
    (P1.xPair_ef_ne_eg hef' heg' hfg') (P1.xPair_ef_ne_fg hef' heg' hfg') (P1.xPair_eg_ne_fg hef' heg' hfg')
    hE.1 hE.2.1 hE.2.2 (w3dp_union_triangle_eq_classical hef' heg' hfg' _)
    (CV.geoIndependent_of_mem_Ind _ hS')
    (w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) hef' heg' hfg')
    (fun m hm => by
      rcases (hZiff m).mp hm with rfl | rfl | rfl
      · exact ⟨zA, rfl, Or.inl hzA⟩
      · exact ⟨zB, rfl, Or.inr (Or.inl hzB)⟩
      · exact ⟨zC, rfl, Or.inr (Or.inr hzC)⟩)
    ⟨zC, hzC, (hZiff _).mpr (Or.inr (Or.inr rfl))⟩

/-- **the PARITY clause (i) of `w3cx_outer_residue`, in its exact shape**: at every configuration of the extended
interface the retained crossings of `q₀'` between distinct carriers of `Q' ∪ T'` are even in number. -/
def w3dp_parity_at : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (_hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (_hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ Λ : ℕ,
        (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card = 2 * Λ

/-- **the parity clause PROVED**: `#mixedSet = 2Λ(J_L)` for an admissible double smoothing (the bridge), and
`2Λ` is even (mp:zero-link). -/
theorem w3dp_parity_at_proof : w3dp_parity_at := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  have hb := w3dp_bridge_at hn E e f g δ hL t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi' hS' q₀' hq₀'
  have hef' := (hs _).mp hef
  have heg' := (hs _).mp heg
  have hfg' := (hs _).mp hfg
  have htri := w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'
  have hT := P1.mem_triangleCrossings_iff hef' heg' hfg'
  obtain ⟨J, hJ⟩ := w3dp_exists_admissible hn (genericAt E t' ht'.1) hQi' q₀'
    (htri ((hT _).mpr (Or.inl rfl))) (htri ((hT _).mpr (Or.inr (Or.inl rfl)))) (P1.xPair_ef_ne_eg hef' heg' hfg')
  have h1 := w3dp_bridge_occ_spec hb hJ
  obtain ⟨Λ, hΛ⟩ := w3dp_twoLambda_even J
  have h2 : ((w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)
      (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card : ℤ) = 2 * Λ := h1.symm.trans hΛ
  have hΛ0 : 0 ≤ Λ := by
    have := Nat.cast_nonneg (α := ℤ) (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)
      (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card
    omega
  refine ⟨Λ.toNat, ?_⟩
  zify
  rw [Int.toNat_of_nonneg hΛ0]
  exact h2

/-- **clause (ii) of `w3cx_outer_residue` in isolation** — KNOT's identification (unit RESID's content), with its
own `Λ`: the same binders as the residue. -/
def w3dp_ident_at : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ Λ : ℕ,
        w3ck_three_components_ident_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))

/-- **the residue from the identification clause**: the parity for the identification's `Λ` follows from the
bridge (`2Λ(J_L) = #mixedSet`) and `2Λ(J_L) = 2Λ` at an admissible `J_L`. -/
theorem w3dp_outer_residue_of_ident (h : w3dp_ident_at) : w3cx_outer_residue := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨Λ, hid⟩ := h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  refine ⟨Λ, ?_, hid⟩
  have hb := w3dp_bridge_at hn E e f g δ hL t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi' hS' q₀' hq₀'
  have hef' := (hs _).mp hef
  have heg' := (hs _).mp heg
  have hfg' := (hs _).mp hfg
  have htri := w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'
  have hT := P1.mem_triangleCrossings_iff hef' heg' hfg'
  obtain ⟨J, hJ⟩ := w3dp_exists_admissible hn (genericAt E t' ht'.1) hQi' q₀'
    (htri ((hT _).mpr (Or.inl rfl))) (htri ((hT _).mpr (Or.inr (Or.inl rfl)))) (P1.xPair_ef_ne_eg hef' heg' hfg')
  have h1 := w3dp_bridge_occ_spec hb hJ
  have h2 := (w3dp_ident_occ_spec hid hJ).1
  exact_mod_cast h1.symm.trans h2

/-- the σ/HOMFLY half of `w3ck_IdentData` alone: the three knot restrictions carry `fA, fB, fC` -/
def w3dp_HomflyData (J : Diagram) (fA fB fC : R) : Prop :=
  ∃ σ : Fin 3 ≃ Fin J.Γ.c, homfly (J.knotRestrict (σ 0)) = fA ∧ homfly (J.knotRestrict (σ 1)) = fB ∧
    homfly (J.knotRestrict (σ 2)) = fC

/-- the σ/HOMFLY half in occurrence-clause form (the binders of `w3ck_three_components_ident_occ`) -/
def w3dp_homfly_occ (D_L : Diagram) (pxL pyL : Plane) (fA fB fC : R) : Prop :=
  ∀ (x_L : D_L.Γ.Crossing), D_L.Γ.crossingPoint x_L = pxL →
    ∀ D_L0 : Diagram, IsOrientedSmoothing D_L x_L D_L0 → w3ck_SmoothRecordOcc D_L x_L D_L0 →
    ∀ (y_L : D_L0.Γ.Crossing), D_L0.Γ.crossingPoint y_L = pyL →
    ∀ J_L : Diagram, IsOrientedSmoothing D_L0 y_L J_L →
      Nonempty (RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y_L))) →
      w3dp_HomflyData J_L fA fB fC

/-- **the σ/HOMFLY clause at every configuration** (the identification without `Λ`): what unit RESID needs to
prove if it takes the `Λ`-free route; `w3dp_ident_of_homfly` supplies `Λ` from the parity. -/
def w3dp_homfly_at : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
        w3dp_homfly_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg)))
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))

/-- **the identification clause from the σ/HOMFLY clause**: `Λ := #mixedSet / 2` (the parity), and
`2Λ(J_L) = #mixedSet = 2Λ` at every admissible `J_L` (the bridge). -/
theorem w3dp_ident_of_homfly (h : w3dp_homfly_at) : w3dp_ident_at := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨Λ, hΛ⟩ := w3dp_parity_at_proof hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi
    hQi' hS' q₀ q₀' hq₀ hq₀'
  have hb := w3dp_bridge_at hn E e f g δ hL t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi' hS' q₀' hq₀'
  have hh := h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  refine ⟨Λ, ?_⟩
  intro x_L hx D_L0 hsm hocc y_L hy J_L hsmJ hJ
  refine ⟨?_, hh x_L hx D_L0 hsm hocc y_L hy J_L hsmJ hJ⟩
  rw [hb x_L hx D_L0 hsm hocc y_L hy J_L hsmJ hJ, hΛ]
  push_cast
  ring

/-- **the residue from the σ/HOMFLY clause** -/
theorem w3dp_outer_residue_of_homfly (h : w3dp_homfly_at) : w3cx_outer_residue :=
  w3dp_outer_residue_of_ident (w3dp_ident_of_homfly h)

end W3DP_ConfigEvent

end W3DP_Config


/-! ## W3D unit RESID (`w3di_`): the IDENTIFICATION clause of `w3cx_outer_residue` — the three components of
`J_L = D_L^{xy}` are the lifts of SPLITA's outer carriers `A, B, C` (record-clause form
`w3ck_three_components_ident_occ`), and `twoLambda J_L = 2Λ` with `Λ` the parity clause's `Λ`.
Report: `W3D_RESID_REPORT.md`.  Library imported for it: `RProof.ExtremeTransportUnits` (row 176's
`r176s_smoothRestrictIso`, `r176s_homfly_of_liftBlock`, `r176c_homfly_of_liftBlock_curl`, the `r176o_` orbit helpers).
Sections: R0 the two mp:stack isomorphisms as definitions; R1–R3 restriction-of-restriction and arc inheritance;
R4 the three components of a double smoothing; G the word `(α₁ β₁ | β₂ γ₁ | γ₂ α₂)` on the contact carrier, its
positions, owners and the lift's arcs; A `2Λ` = the mixed crossings; B the assembly; C the abstract clause; D the
configuration.  The parity clause is the black box `w3di_parity_data` (unit RESPAR). -/
section W3DI_RESID
open Equiv

/-! ### R1. Restriction of a restriction by crossing sets: `(ρ|K)|K' ≅ ρ|K''` -/

section W3DI_RR
variable (ρ : Record)

/-- the crossings of `ρ` in `K` whose image chord in `ρ|K` lies in `K'` -/
def w3di_innerKeep (K : Set ρ.Crossing) (K' : Set (ρ.restrictCrossings K).Crossing) : Set ρ.Crossing :=
  {c | ∃ u ∈ c.1, ∃ h : ρ.CrossKeep K u, (ρ.restrictCrossings K).CrossKeep K' ⟨u, h⟩}

theorem w3di_crossKeep_innerKeep_iff (K : Set ρ.Crossing) (K' : Set (ρ.restrictCrossings K).Crossing)
    (u : ρ.M) :
    ρ.CrossKeep (w3di_innerKeep ρ K K') u ↔
      ∃ h : ρ.CrossKeep K u, (ρ.restrictCrossings K).CrossKeep K' ⟨u, h⟩ := by
  constructor
  · rintro ⟨u', hu', h, hK'⟩
    rcases (ρ.mem_val_iff (ρ.mem_crossingOf u) u').mp hu' with rfl | rfl
    · exact ⟨h, hK'⟩
    · have h' : ρ.CrossKeep K u := (ρ.crossKeep_pair_iff K u).mp h
      refine ⟨h', ?_⟩
      have e : (⟨ρ.pair u, h⟩ : (ρ.restrictCrossings K).M) = (ρ.restrictCrossings K).pair ⟨u, h'⟩ := rfl
      rw [e] at hK'
      exact ((ρ.restrictCrossings K).crossKeep_pair_iff K' _).mp hK'
  · rintro ⟨h, hK'⟩
    exact ⟨u, ρ.mem_crossingOf u, h, hK'⟩

theorem w3di_crossKeep_of_innerKeep (K : Set ρ.Crossing) (K' : Set (ρ.restrictCrossings K).Crossing)
    {u : ρ.M} (h : ρ.CrossKeep (w3di_innerKeep ρ K K') u) : ρ.CrossKeep K u :=
  ((w3di_crossKeep_innerKeep_iff ρ K K' u).mp h).fst

theorem w3di_innerKeep_subset (K : Set ρ.Crossing) (K' : Set (ρ.restrictCrossings K).Crossing) :
    w3di_innerKeep ρ K K' ⊆ K := by
  rintro c ⟨u, hu, h, -⟩
  have e : ρ.crossingOf u = c := (ρ.crossingOf_eq_iff u c).mpr hu
  rw [← e]; exact h

theorem w3di_rr_keep_iff (K : Set ρ.Crossing) (K' : Set (ρ.restrictCrossings K).Crossing)
    (m : (ρ.restrictCrossings K).M) :
    (ρ.restrictCrossings K).CrossKeep K' m ↔ ρ.CrossKeep (w3di_innerKeep ρ K K') m.1 := by
  rw [w3di_crossKeep_innerKeep_iff]
  exact ⟨fun h => ⟨m.2, h⟩, fun ⟨_, h⟩ => h⟩

/-- the occurrence bijection of the restriction-of-a-restriction isomorphism -/
def w3di_rrEquiv (K : Set ρ.Crossing) (K' : Set (ρ.restrictCrossings K).Crossing) :
    ((ρ.restrictCrossings K).restrictCrossings K').M ≃
      (ρ.restrictCrossings (w3di_innerKeep ρ K K')).M :=
  (Equiv.subtypeEquivRight (fun m => w3di_rr_keep_iff ρ K K' m)).trans
    (Equiv.subtypeSubtypeEquivSubtype (p := ρ.CrossKeep K) (q := ρ.CrossKeep (w3di_innerKeep ρ K K'))
      (fun {_} hx => w3di_crossKeep_of_innerKeep ρ K K' hx))

theorem w3di_rrEquiv_val (K : Set ρ.Crossing) (K' : Set (ρ.restrictCrossings K).Crossing) (m) :
    (w3di_rrEquiv ρ K K' m).1 = m.1.1 := rfl

/-- **Restriction of a restriction (crossing sets)**: `(ρ|K)|K' ≅ ρ|K''` with `K''` the crossings of
`K` whose chord in `ρ|K` lies in `K'` (the general form of `r176c_restrictRestrictIso`). -/
def w3di_restrictRestrictIso (K : Set ρ.Crossing) (K' : Set (ρ.restrictCrossings K).Crossing) :
    RecordIso ((ρ.restrictCrossings K).restrictCrossings K')
      (ρ.restrictCrossings (w3di_innerKeep ρ K K')) where
  e := Equiv.refl _
  Φ := w3di_rrEquiv ρ K K'
  comp_eq _ := rfl
  succ_eq m := by
    apply Subtype.ext
    have h₁ := firstReturn_congr_pred (ρ.restrictCrossings K).succ
      ((ρ.restrictCrossings K).CrossKeep K') (fun m => ρ.CrossKeep (w3di_innerKeep ρ K K') m.1)
      (w3di_rr_keep_iff ρ K K') m
    have h₂ := ρ.restrictCrossings_firstReturn_val (S₁ := w3di_innerKeep ρ K K') (S := K)
      (w3di_innerKeep_subset ρ K K') ⟨m.1, (w3di_rr_keep_iff ρ K K' m.1).mp m.2⟩
    exact (congrArg Subtype.val h₁).trans h₂
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

end W3DI_RR

/-! ### R2. Restriction of a restriction by blocks: `(ρ|B)|B₁ ≅ ρ|B₂` (`B₂` = `B₁` read in `ρ.comps`) -/

section W3DI_RB
variable (ρ : Record)

theorem w3di_restrictKeep_outer_iff (B : Finset ρ.comps) (B₁ : Finset (ρ.restrict B).comps)
    (B₂ : Finset ρ.comps)
    (hB₂ : ∀ c : ρ.comps, c ∈ B₂ ↔ ∃ h : c ∈ B, (⟨c, h⟩ : (ρ.restrict B).comps) ∈ B₁)
    (m : (ρ.restrict B).M) :
    (ρ.restrict B).RestrictKeep B₁ m ↔ ρ.RestrictKeep B₂ m.1 := by
  unfold Record.RestrictKeep
  rw [hB₂, hB₂]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨m.2.1, h1⟩, ⟨m.2.2, h2⟩⟩
  · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    exact ⟨h1, h2⟩

theorem w3di_restrictKeep_of_outer (B : Finset ρ.comps) (B₁ : Finset (ρ.restrict B).comps)
    (B₂ : Finset ρ.comps)
    (hB₂ : ∀ c : ρ.comps, c ∈ B₂ ↔ ∃ h : c ∈ B, (⟨c, h⟩ : (ρ.restrict B).comps) ∈ B₁) {u : ρ.M}
    (h : ρ.RestrictKeep B₂ u) : ρ.RestrictKeep B u := by
  obtain ⟨h1, h2⟩ := h
  rw [hB₂] at h1 h2
  exact ⟨h1.fst, h2.fst⟩

/-- **Restriction of a restriction (blocks)**: `(ρ|B)|B₁ ≅ ρ|B₂` when `B₂` is `B₁` read in `ρ.comps`. -/
noncomputable def w3di_restrictRestrictBlockIso (B : Finset ρ.comps) (B₁ : Finset (ρ.restrict B).comps)
    (B₂ : Finset ρ.comps)
    (hB₂ : ∀ c : ρ.comps, c ∈ B₂ ↔ ∃ h : c ∈ B, (⟨c, h⟩ : (ρ.restrict B).comps) ∈ B₁) :
    RecordIso ((ρ.restrict B).restrict B₁) (ρ.restrict B₂) where
  e := (Equiv.subtypeSubtypeEquivSubtypeExists (fun c : ρ.comps => c ∈ B) (fun c => c ∈ B₁)).trans
    (Equiv.subtypeEquivRight (fun c => (hB₂ c).symm))
  Φ := (Equiv.subtypeEquivRight (fun m => w3di_restrictKeep_outer_iff ρ B B₁ B₂ hB₂ m)).trans
    (Equiv.subtypeSubtypeEquivSubtype (p := ρ.RestrictKeep B) (q := ρ.RestrictKeep B₂)
      (fun {_} hx => w3di_restrictKeep_of_outer ρ B B₁ B₂ hB₂ hx))
  comp_eq _ := rfl
  succ_eq m := by
    apply Subtype.ext
    have h₁ := firstReturn_congr_pred (ρ.restrict B).succ ((ρ.restrict B).RestrictKeep B₁)
      (fun m => ρ.RestrictKeep B₂ m.1) (w3di_restrictKeep_outer_iff ρ B B₁ B₂ hB₂) m
    have h₂ := firstReturn_firstReturn ρ.succ (ρ.RestrictKeep B) (ρ.RestrictKeep B₂)
      ⟨m.1, (w3di_restrictKeep_outer_iff ρ B B₁ B₂ hB₂ m.1).mp m.2⟩
    have h₃ := firstReturn_congr_pred ρ.succ
      (fun u => ρ.RestrictKeep B u ∧ ρ.RestrictKeep B₂ u) (ρ.RestrictKeep B₂)
      (fun u => ⟨fun h => h.2, fun h => ⟨w3di_restrictKeep_of_outer ρ B B₁ B₂ hB₂ h, h⟩⟩)
      ⟨m.1.1, m.1.2, (w3di_restrictKeep_outer_iff ρ B B₁ B₂ hB₂ m.1).mp m.2⟩
    exact (congrArg Subtype.val h₁).trans (h₂.trans h₃)
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

theorem w3di_restrictRestrictBlockIso_Φ_val (B : Finset ρ.comps) (B₁ : Finset (ρ.restrict B).comps)
    (B₂ : Finset ρ.comps) (hB₂) (m) :
    ((w3di_restrictRestrictBlockIso ρ B B₁ B₂ hB₂).Φ m).1 = m.1.1 := rfl

end W3DI_RB

/-! ### R3. The arc order of a one-circle record is inherited by every `restrictCrossings` -/

section W3DI_Arc
variable (ρ : Record) (h1 : ρ.componentCount = 1) (K : Set ρ.Crossing)

/-- the position in `ρ` of the `k`-th `ρ|K`-successor of `x` -/
noncomputable def w3di_pos (x : (ρ.restrictCrossings K).M) (k : ℕ) : ℕ :=
  ρ.steps x.1 (((ρ.restrictCrossings K).succ ^ k) x).1

theorem w3di_pos_zero (x : (ρ.restrictCrossings K).M) : w3di_pos ρ K x 0 = 0 := by
  unfold w3di_pos
  rw [pow_zero, Perm.one_apply, ρ.steps_self]

include h1 in
/-- the position of the restricted successor of `u ≠ x`, when it is not `x`: the old position plus
the return time (no wrap-around) -/
theorem w3di_steps_rsucc (x u : (ρ.restrictCrossings K).M) (hux : u ≠ x)
    (hsx : (ρ.restrictCrossings K).succ u ≠ x) :
    ρ.steps x.1 ((ρ.restrictCrossings K).succ u).1 =
      ρ.steps x.1 u.1 + returnTime ρ.succ (ρ.CrossKeep K) u.1 u.2 := by
  set rt := returnTime ρ.succ (ρ.CrossKeep K) u.1 u.2 with hrt
  have hsucc : ((ρ.restrictCrossings K).succ u).1 = (ρ.succ ^ rt) u.1 := firstReturn_apply _ _ u
  have hux' : u.1 ≠ x.1 := fun h => hux (Subtype.ext h)
  have hspos : 0 < ρ.steps x.1 u.1 := (ρ.steps_pos_iff h1 _ _).mpr (Ne.symm hux')
  have hle : rt ≤ ρ.steps u.1 x.1 := ρ.returnTime_le_steps _ h1 u x.2 (Ne.symm hux')
  have hne : rt ≠ ρ.steps u.1 x.1 := by
    intro h
    apply hsx
    apply Subtype.ext
    rw [hsucc, h, ρ.pow_steps h1]
  have hlt : rt < ρ.steps u.1 x.1 := lt_of_le_of_ne hle hne
  have ht : ρ.steps u.1 x.1 = Fintype.card ρ.M - ρ.steps x.1 u.1 := by
    have ht0 := ρ.steps_eq_of_base h1 x.1 u.1 x.1
    rw [ρ.steps_self] at ht0
    split_ifs at ht0 with h
    · omega
    · omega
  have hcard : ρ.steps x.1 u.1 + rt < Fintype.card ρ.M := by omega
  rw [ρ.steps_eq_iff h1]
  refine ⟨hcard, ?_⟩
  rw [hsucc, add_comm, pow_add, Perm.mul_apply, ρ.pow_steps h1]

include h1 in
theorem w3di_pos_succ (x : (ρ.restrictCrossings K).M) (k : ℕ)
    (hk : k + 1 < Fintype.card (ρ.restrictCrossings K).M) :
    w3di_pos ρ K x k < w3di_pos ρ K x (k + 1) := by
  have h1K : (ρ.restrictCrossings K).componentCount = 1 := h1
  have hpow : ∀ i j, i < Fintype.card (ρ.restrictCrossings K).M →
      j < Fintype.card (ρ.restrictCrossings K).M →
      ((ρ.restrictCrossings K).succ ^ i) x = ((ρ.restrictCrossings K).succ ^ j) x → i = j :=
    fun i j hi hj h => ((ρ.restrictCrossings K).pow_apply_eq_pow_apply_iff h1K x hi hj).mp h
  have hsu : ((ρ.restrictCrossings K).succ ^ (k + 1)) x =
      (ρ.restrictCrossings K).succ (((ρ.restrictCrossings K).succ ^ k) x) := by
    rw [pow_succ', Perm.mul_apply]
  unfold w3di_pos
  rw [hsu]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero, Perm.one_apply, ρ.steps_self, ρ.steps_pos_iff h1]
    exact (ρ.firstReturn_val_ne _ h1 x ((ρ.crossKeep_pair_iff K x.1).mpr x.2) (ρ.pair_ne x.1)).symm
  · have hux : ((ρ.restrictCrossings K).succ ^ k) x ≠ x := by
      intro h
      have := hpow k 0 (by omega) (by omega) (by rw [h, pow_zero, Perm.one_apply])
      omega
    have hsx : (ρ.restrictCrossings K).succ (((ρ.restrictCrossings K).succ ^ k) x) ≠ x := by
      intro h
      rw [← hsu] at h
      have := hpow (k + 1) 0 hk (by omega) (by rw [h, pow_zero, Perm.one_apply])
      omega
    rw [w3di_steps_rsucc ρ h1 K x _ hux hsx]
    exact Nat.lt_add_of_pos_right (returnTime_pos _ _ _ _)

include h1 in
theorem w3di_pos_lt_of_lt (x : (ρ.restrictCrossings K).M) {i j : ℕ} (hij : i < j)
    (hj : j < Fintype.card (ρ.restrictCrossings K).M) : w3di_pos ρ K x i < w3di_pos ρ K x j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i j with h | h
    · exact lt_trans (ih h (by omega)) (w3di_pos_succ ρ h1 K x j hj)
    · have : i = j := by omega
      subst this
      exact w3di_pos_succ ρ h1 K x i hj

include h1 in
theorem w3di_pos_lt_iff (x : (ρ.restrictCrossings K).M) {i j : ℕ}
    (hi : i < Fintype.card (ρ.restrictCrossings K).M) (hj : j < Fintype.card (ρ.restrictCrossings K).M) :
    w3di_pos ρ K x i < w3di_pos ρ K x j ↔ i < j := by
  constructor
  · intro h
    by_contra hle
    rcases Nat.lt_or_ge j i with h' | h'
    · exact absurd (lt_trans h (w3di_pos_lt_of_lt ρ h1 K x h' hi)) (lt_irrefl _)
    · have : i = j := by omega
      subst this
      exact lt_irrefl _ h
  · intro h
    exact w3di_pos_lt_of_lt ρ h1 K x h hj

include h1 in
/-- **the arc order is inherited by the restriction**: three retained occurrences are in the cyclic
order of `ρ|K` iff they are in the cyclic order of `ρ`. -/
theorem w3di_arcBetween_restrictCrossings_iff (x y z : (ρ.restrictCrossings K).M) :
    (ρ.restrictCrossings K).ArcBetween x y z ↔ ρ.ArcBetween x.1 y.1 z.1 := by
  have h1K : (ρ.restrictCrossings K).componentCount = 1 := h1
  have hy := (ρ.restrictCrossings K).pow_steps h1K x y
  have hz := (ρ.restrictCrossings K).pow_steps h1K x z
  have hky := (ρ.restrictCrossings K).steps_lt_card h1K x y
  have hkz := (ρ.restrictCrossings K).steps_lt_card h1K x z
  have hcard : 0 < Fintype.card (ρ.restrictCrossings K).M := Fintype.card_pos_iff.mpr ⟨x⟩
  have ey : ρ.steps x.1 y.1 = w3di_pos ρ K x ((ρ.restrictCrossings K).steps x y) := by
    unfold w3di_pos; rw [hy]
  have ez : ρ.steps x.1 z.1 = w3di_pos ρ K x ((ρ.restrictCrossings K).steps x z) := by
    unfold w3di_pos; rw [hz]
  have e0 : 0 < w3di_pos ρ K x ((ρ.restrictCrossings K).steps x y) ↔
      0 < (ρ.restrictCrossings K).steps x y := by
    have := w3di_pos_lt_iff ρ h1 K x hcard hky
    rw [w3di_pos_zero] at this
    exact this
  unfold Record.ArcBetween
  rw [ey, ez, e0, w3di_pos_lt_iff ρ h1 K x hky hkz]

end W3DI_Arc



/-! ### R0. The two mp:stack record isomorphisms as explicit definitions (occurrence maps
`rsOccEquiv` / `rdOccEquiv`: the identity on the underlying occurrences).  Bodies = the accepted proofs of
`Record.restrictSmoothIso'` / `Record.restrictSmoothDisjointIso'` (SM/Stack.lean), verbatim. -/

section W3DI_Stack
open Classical

/-- `Record.restrictSmoothIso'` as a definition (explicit occurrence map `rsOccEquiv`). -/
noncomputable def w3di_rsIso (ρ : Record) (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B) :
    RecordIso ((ρ.smooth v'.1).restrict B') ((ρ.restrict B).smooth v') := by
  refine { e := ρ.rsCompsEquiv B v' B' hB' hB''
           Φ := ρ.rsOccEquiv B v' B' hB'
           comp_eq := ?_, succ_eq := ?_, pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }
  · intro w
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff v'.1 B B' hB' w.1).mp w.2
    have hk : ∃ u', (ρ.reconnect v'.1).SameCycle
        (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1)) w.1.1).out u' ∧
          ρ.RestrictKeep B u' :=
      ⟨w.1.1, ρ.reconnect_sameCycle_out v'.1 _, hK⟩
    refine Eq.trans ?_ (ρ.rsFwd_inl_pos B v' B' hB' hB'' _ ((hB' _).mpr hK.1) hk).symm
    apply congrArg Sum.inl
    apply Quotient.sound
    refine (ρ.restrict_reconnect_sameCycle_iff B v' _ _).mpr ?_
    exact (ρ.reconnect_sameCycle_out v'.1 _).symm.trans (Classical.choose_spec hk).1
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff v'.1 B B' hB' w.1).mp w.2
    have hP : (ρ.restrict B).SmoothKeep v' ⟨w.1.1, hK⟩ :=
      (ρ.restrict_smoothKeep_iff B v' _).mpr w.1.2
    show (firstReturn (ρ.smooth v'.1).succ ((ρ.smooth v'.1).RestrictKeep B') w).1.1 =
      (firstReturn ((ρ.restrict B).reconnect v') ((ρ.restrict B).SmoothKeep v')
        ⟨⟨w.1.1, hK⟩, hP⟩).1.1
    calc (firstReturn (ρ.smooth v'.1).succ ((ρ.smooth v'.1).RestrictKeep B') w).1.1
        = (firstReturn (ρ.smooth v'.1).succ (fun m => ρ.RestrictKeep B m.1) ⟨w.1, hK⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (ρ.smooth_restrictKeep_iff v'.1 B B' hB') w (fun _ => rfl))
      _ = (firstReturn (ρ.reconnect v'.1) (fun m => ρ.SmoothKeep v'.1 m ∧ ρ.RestrictKeep B m)
            ⟨w.1.1, w.1.2, hK⟩).1 :=
          firstReturn_firstReturn (ρ.reconnect v'.1) (ρ.SmoothKeep v'.1) (ρ.RestrictKeep B)
            ⟨w.1, hK⟩
      _ = (firstReturn (ρ.reconnect v'.1) (fun m => ρ.RestrictKeep B m ∧ ρ.SmoothKeep v'.1 m)
            ⟨w.1.1, hK, w.1.2⟩).1 :=
          firstReturn_val_congr _ _ _ _ (fun m => and_comm) ⟨w.1.1, w.1.2, hK⟩ (fun _ => rfl)
      _ = (firstReturn (firstReturn (ρ.reconnect v'.1) (ρ.RestrictKeep B))
            (fun m => ρ.SmoothKeep v'.1 m.1) ⟨⟨w.1.1, hK⟩, w.1.2⟩).1.1 :=
          (firstReturn_firstReturn (ρ.reconnect v'.1) (ρ.RestrictKeep B) (ρ.SmoothKeep v'.1)
            ⟨⟨w.1.1, hK⟩, w.1.2⟩).symm
      _ = (firstReturn ((ρ.restrict B).reconnect v') ((ρ.restrict B).SmoothKeep v')
            ⟨⟨w.1.1, hK⟩, hP⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (fun m => (ρ.restrict_smoothKeep_iff B v' m).symm) ⟨⟨w.1.1, hK⟩, w.1.2⟩
            (fun n => by rw [ρ.restrict_reconnect_eq B v']))
  · intro w; rfl
  · intro w; rfl
  · intro w; rfl

theorem w3di_rsIso_Φ_val (ρ : Record) (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps) (hB') (hB'') (w) :
    ((w3di_rsIso ρ B v' B' hB' hB'').Φ w).1.1 = w.1.1 := rfl

/-- `Record.restrictSmoothDisjointIso'` as a definition (explicit occurrence map `rdOccEquiv`). -/
noncomputable def w3di_rdIso (ρ : Record) (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B)
    (hx' : ρ.comp (ρ.pair x) ∉ B) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B) :
    RecordIso ((ρ.smooth x).restrict B') (ρ.restrict B) := by
  refine { e := ρ.rdCompsEquiv x B hx hx' B' hB' hB''
           Φ := ρ.rdOccEquiv x B hx hx' B' hB'
           comp_eq := ?_, succ_eq := ?_, pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }
  · intro w
    apply Subtype.ext
    show ρ.comp w.1.1 = ρ.comp (Quotient.mk _ w.1.1).out
    exact (ρ.comp_out_eq_disjoint x B hx hx'
      ((ρ.smooth_restrictKeep_iff x B B' hB' w.1).mp w.2).1).symm
  · intro w
    apply Subtype.ext
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff x B B' hB' w.1).mp w.2
    have hne := ρ.comp_ne_of_mem_disjoint x B hx hx' hK.1
    show (firstReturn (ρ.smooth x).succ ((ρ.smooth x).RestrictKeep B') w).1.1 =
      (firstReturn ρ.succ (ρ.RestrictKeep B) ⟨w.1.1, hK⟩).1
    calc (firstReturn (ρ.smooth x).succ ((ρ.smooth x).RestrictKeep B') w).1.1
        = (firstReturn (ρ.smooth x).succ (fun m => ρ.RestrictKeep B m.1) ⟨w.1, hK⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (ρ.smooth_restrictKeep_iff x B B' hB') w (fun _ => rfl))
      _ = (firstReturn (ρ.reconnect x) (fun m => ρ.SmoothKeep x m ∧ ρ.RestrictKeep B m)
            ⟨w.1.1, w.1.2, hK⟩).1 :=
          firstReturn_firstReturn (ρ.reconnect x) (ρ.SmoothKeep x) (ρ.RestrictKeep B) ⟨w.1, hK⟩
      _ = (firstReturn ρ.succ (ρ.RestrictKeep B) ⟨w.1.1, hK⟩).1 :=
          firstReturn_val_congr _ _ _ _
            (fun m => ⟨fun h => h.2, fun h => ⟨ρ.smoothKeep_of_comp_mem_disjoint x B hx hx' h.1, h⟩⟩)
            ⟨w.1.1, w.1.2, hK⟩ (ρ.reconnect_pow_eq_succ_pow x w.1.1 hne.1 hne.2)
  · intro w; rfl
  · intro w; rfl
  · intro w; rfl

theorem w3di_rdIso_Φ_val (ρ : Record) (x : ρ.M) (B : Finset ρ.comps) (hx) (hx')
    (B' : Finset (ρ.smooth x).comps) (hB') (hB'') (w) :
    ((w3di_rdIso ρ x B hx hx' B' hB' hB'').Φ w).1 = w.1.1 := rfl

end W3DI_Stack

/-! ### R4. The three components of a double smoothing of a one-circle record -/

section W3DI_Double

/-- restriction to equal blocks -/
noncomputable def w3di_restrictCongr (τ : Record) {B B' : Finset τ.comps} (h : B = B') :
    RecordIso (τ.restrict B) (τ.restrict B') where
  e := Equiv.subtypeEquivRight (fun c => by rw [h])
  Φ := Equiv.subtypeEquivRight (fun m => by rw [h])
  comp_eq _ := rfl
  succ_eq m := Subtype.ext (firstReturn_congr_pred τ.succ (τ.RestrictKeep B) (τ.RestrictKeep B')
    (fun m => by rw [h]) m)
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

theorem w3di_restrictCongr_Φ_val (τ : Record) {B B' : Finset τ.comps} (h : B = B') (m : (τ.restrict B).M) :
    ((w3di_restrictCongr τ h).Φ m).1 = m.1 := rfl

/-- `RestrictKeep B ↔ CrossKeep K` through a block/crossing isomorphism whose occurrence map is the
identity on the underlying occurrences -/
theorem w3di_restrictKeep_iff_of_iso (τ σ : Record) (B : Finset τ.comps) (K : Set σ.Crossing)
    (f : τ.M → σ.M) (hf : Function.Injective f)
    (ι : RecordIso (τ.restrict B) (σ.restrictCrossings K)) (hΦ : ∀ m, (ι.Φ m).1 = f m.1) (u : τ.M) :
    τ.RestrictKeep B u ↔ σ.CrossKeep K (f u) := by
  constructor
  · intro h
    exact Eq.mp (congrArg (σ.CrossKeep K) (hΦ ⟨u, h⟩)) (ι.Φ ⟨u, h⟩).2
  · intro h
    have e := ι.Φ.apply_symm_apply ⟨f u, h⟩
    have e1 := hΦ (ι.Φ.symm ⟨f u, h⟩)
    rw [e] at e1
    have e2 : u = (ι.Φ.symm ⟨f u, h⟩).1 := hf e1
    rw [e2]
    exact (ι.Φ.symm ⟨f u, h⟩).2

/-- the block of the smoothing at a self crossing `w'` lying over a block `B` of `σ` -/
theorem w3di_block_exists (σ : Record) (w' : σ.M) (hself : σ.IsSelfCrossing w') (B : Finset σ.comps) :
    ∃ B' : Finset (σ.smooth w').comps,
      (∀ u : σ.M, (Sum.inl (Quotient.mk _ u) : σ.SmoothComps w') ∈ B' ↔ σ.comp u ∈ B) ∧
      (∀ f : σ.FreeComp, (Sum.inr f : σ.SmoothComps w') ∈ B' ↔ f.1 ∈ B) := by
  classical
  have hβ : (σ.comp w' ∈ B) = (σ.comp (σ.pair w') ∈ B) := by
    have h : σ.comp w' = σ.comp (σ.pair w') := hself
    rw [h]
  have hmem : ∀ κ : (σ.smooth w').comps,
      κ ∈ Finset.univ.filter (fun κ => σ.smoothBlock (fun c => c ∈ B) w' hβ κ) ↔
        σ.smoothBlock (fun c => c ∈ B) w' hβ κ := by
    intro κ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨Finset.univ.filter (fun κ => σ.smoothBlock (fun c => c ∈ B) w' hβ κ), ?_, ?_⟩
  · intro u
    exact (hmem (Sum.inl (Quotient.mk _ u))).trans Iff.rfl
  · intro f
    exact (hmem (Sum.inr f)).trans Iff.rfl

/-- two blocks over disjoint blocks are disjoint -/
theorem w3di_block_disjoint (σ : Record) (w' : σ.M) (B₁ B₂ : Finset σ.comps)
    (hd : ∀ c, c ∈ B₁ → c ∈ B₂ → False) (B₁' B₂' : Finset (σ.smooth w').comps)
    (h₁ : ∀ u : σ.M, (Sum.inl (Quotient.mk _ u) : σ.SmoothComps w') ∈ B₁' ↔ σ.comp u ∈ B₁)
    (h₁' : ∀ f : σ.FreeComp, (Sum.inr f : σ.SmoothComps w') ∈ B₁' ↔ f.1 ∈ B₁)
    (h₂ : ∀ u : σ.M, (Sum.inl (Quotient.mk _ u) : σ.SmoothComps w') ∈ B₂' ↔ σ.comp u ∈ B₂)
    (h₂' : ∀ f : σ.FreeComp, (Sum.inr f : σ.SmoothComps w') ∈ B₂' ↔ f.1 ∈ B₂)
    (κ : (σ.smooth w').comps) (hκ₁ : κ ∈ B₁') (hκ₂ : κ ∈ B₂') : False := by
  rcases κ with κ | f
  · induction κ using Quotient.inductionOn with
    | h u => exact hd _ ((h₁ u).mp hκ₁) ((h₂ u).mp hκ₂)
  · exact hd _ ((h₁' f).mp hκ₁) ((h₂' f).mp hκ₂)

/-- **The three components of the double smoothing `(ρ^v)^{w'}` of a one-circle record**, with `w'`
a retained occurrence whose chord has both ends on the arc `A = (v → τv)`: the component `κB` over the
arc `B` (its record is `ρ` restricted to `K_B`), and the two components `κ₁, κ₂` over the arc `A`
(records `ρ|K₁`, `ρ|K₂`, the chords with both occurrences on `A` and on the same open arc of the chord of
`w'`, read in `ρ`). -/
structure w3di_DoubleData (ρ : Record) (v : ρ.M) (w' : (ρ.smooth v).M) where
  κB : ((ρ.smooth v).smooth w').comps
  κ₁ : ((ρ.smooth v).smooth w').comps
  κ₂ : ((ρ.smooth v).smooth w').comps
  K₁ : Set ρ.Crossing
  K₂ : Set ρ.Crossing
  ne_B1 : κB ≠ κ₁
  ne_B2 : κB ≠ κ₂
  ne_12 : κ₁ ≠ κ₂
  count3 : ((ρ.smooth v).smooth w').componentCount = 3
  keep₁ : ∀ u : ρ.M, ρ.CrossKeep K₁ u ↔
    (r176s_ArcA ρ v u ∧ r176s_ArcA ρ v (ρ.pair u)) ∧
      (ρ.ArcBetween w'.1 u (ρ.pair w'.1) ∧ ρ.ArcBetween w'.1 (ρ.pair u) (ρ.pair w'.1))
  keep₂ : ∀ u : ρ.M, ρ.CrossKeep K₂ u ↔
    (r176s_ArcA ρ v u ∧ r176s_ArcA ρ v (ρ.pair u)) ∧
      (ρ.ArcBetween (ρ.pair w'.1) u w'.1 ∧ ρ.ArcBetween (ρ.pair w'.1) (ρ.pair u) w'.1)
  isoB : Nonempty (RecordIso (((ρ.smooth v).smooth w').restrict {κB})
    (ρ.restrictCrossings (r176s_KB ρ v)))
  iso₁ : Nonempty (RecordIso (((ρ.smooth v).smooth w').restrict {κ₁}) (ρ.restrictCrossings K₁))
  iso₂ : Nonempty (RecordIso (((ρ.smooth v).smooth w').restrict {κ₂}) (ρ.restrictCrossings K₂))
  rkB : ∀ m : ((ρ.smooth v).smooth w').M,
    ((ρ.smooth v).smooth w').RestrictKeep {κB} m ↔ ρ.CrossKeep (r176s_KB ρ v) m.1.1
  rk₁ : ∀ m : ((ρ.smooth v).smooth w').M,
    ((ρ.smooth v).smooth w').RestrictKeep {κ₁} m ↔ ρ.CrossKeep K₁ m.1.1
  rk₂ : ∀ m : ((ρ.smooth v).smooth w').M,
    ((ρ.smooth v).smooth w').RestrictKeep {κ₂} m ↔ ρ.CrossKeep K₂ m.1.1

variable (ρ : Record) (h1 : ρ.componentCount = 1) (v : ρ.M) (w' : (ρ.smooth v).M)

theorem w3di_val_val_injective :
    Function.Injective (fun m : ((ρ.smooth v).smooth w').M => m.1.1) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

include h1 in
theorem w3di_double_exists (hA : r176s_ArcA ρ v w'.1) (hA' : r176s_ArcA ρ v (ρ.pair w'.1)) :
    Nonempty (w3di_DoubleData ρ v w') := by
  classical
  have hcompw : (ρ.smooth v).comp w' = Sum.inl (Quotient.mk _ (ρ.pair v)) :=
    (r176s_smooth_comp_eq_pair_iff ρ h1 v w').mpr hA
  have hcompw' : (ρ.smooth v).comp ((ρ.smooth v).pair w') = Sum.inl (Quotient.mk _ (ρ.pair v)) := by
    rw [r176s_smooth_comp_eq_pair_iff ρ h1 v, Record.smooth_pair_val]
    exact hA'
  have hself : (ρ.smooth v).IsSelfCrossing w' := hcompw.trans hcompw'.symm
  have hvself : ρ.IsSelfCrossing v := r176s_isSelfCrossing ρ h1 v
  have hvA : (ρ.smooth v).RestrictKeep (r176s_smoothB ρ v) w' :=
    (r176s_restrictKeep_iff ρ h1 v w').mpr ⟨hA, hA'⟩
  have hcount3 : ((ρ.smooth v).smooth w').componentCount = 3 := by
    rw [Record.componentCount_smooth_of_self _ _ hself, Record.componentCount_smooth_of_self _ _ hvself, h1]
  -- the A-side chain
  have h1A : (ρ.restrictCrossings (r176s_KA ρ v)).componentCount = 1 := h1
  obtain ⟨B', hB', hB''⟩ := w3di_block_exists (ρ.smooth v) w' hself (r176s_smoothB ρ v)
  let ιS := w3di_rsIso (ρ.smooth v) (r176s_smoothB ρ v) ⟨w', hvA⟩ B' hB' hB''
  let ιAS := ιS.trans ((r176s_smoothRestrictIso ρ h1 v).smooth ⟨w', hvA⟩)
  -- the point of the second smoothing, read in `ρ_A`
  let w₃ : (ρ.restrictCrossings (r176s_KA ρ v)).M := (r176s_smoothRestrictIso ρ h1 v).Φ ⟨w', hvA⟩
  have hw₃ : w₃.1 = w'.1 := rfl
  have hw₃self : (ρ.restrictCrossings (r176s_KA ρ v)).IsSelfCrossing w₃ :=
    r176s_isSelfCrossing _ h1A w₃
  let κ₁' : (((ρ.smooth v).smooth w').restrict B').comps :=
    ιAS.e.symm (Sum.inl (Quotient.mk _ ((ρ.restrictCrossings (r176s_KA ρ v)).pair w₃)))
  let κ₂' : (((ρ.smooth v).smooth w').restrict B').comps := ιAS.e.symm (Sum.inl (Quotient.mk _ w₃))
  have hκ₁₂ : κ₁' ≠ κ₂' := by
    intro h
    apply Record.smooth_comps_ne_of_self _ _ hw₃self
    have e1 := ιAS.e.apply_symm_apply
      (Sum.inl (Quotient.mk _ ((ρ.restrictCrossings (r176s_KA ρ v)).pair w₃)))
    have e2 := ιAS.e.apply_symm_apply (Sum.inl (Quotient.mk _ w₃))
    rw [← e1, ← e2]
    exact (congrArg ιAS.e h).symm
  -- the restriction isomorphisms of the two A-components
  let ι₁ := ιAS.restrict {κ₁'} (r176s_smoothB _ w₃) (by
    intro c
    rw [r176s_mem_smoothB, Finset.mem_singleton]
    exact (Equiv.eq_symm_apply ιAS.e).symm)
  let ι₂ := ιAS.restrict {κ₂'} (r176s_smoothB' _ w₃) (by
    intro c
    rw [r176s_mem_smoothB', Finset.mem_singleton]
    exact (Equiv.eq_symm_apply ιAS.e).symm)
  have hB₂₁ : ∀ c : ((ρ.smooth v).smooth w').comps, c ∈ ({κ₁'.1} : Finset _) ↔
      ∃ h : c ∈ B', (⟨c, h⟩ : (((ρ.smooth v).smooth w').restrict B').comps) ∈ ({κ₁'} : Finset _) := by
    intro c
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨κ₁'.2, Finset.mem_singleton.mpr rfl⟩
    · rintro ⟨h, hc⟩
      exact congrArg Subtype.val (Finset.mem_singleton.mp hc)
  have hB₂₂ : ∀ c : ((ρ.smooth v).smooth w').comps, c ∈ ({κ₂'.1} : Finset _) ↔
      ∃ h : c ∈ B', (⟨c, h⟩ : (((ρ.smooth v).smooth w').restrict B').comps) ∈ ({κ₂'} : Finset _) := by
    intro c
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨κ₂'.2, Finset.mem_singleton.mpr rfl⟩
    · rintro ⟨h, hc⟩
      exact congrArg Subtype.val (Finset.mem_singleton.mp hc)
  let χ₁ := ((w3di_restrictRestrictBlockIso ((ρ.smooth v).smooth w') B' {κ₁'} {κ₁'.1} hB₂₁).symm.trans
    ι₁).trans ((r176s_smoothRestrictIso _ h1A w₃).trans
      (w3di_restrictRestrictIso ρ (r176s_KA ρ v) (r176s_KA _ w₃)))
  let χ₂ := ((w3di_restrictRestrictBlockIso ((ρ.smooth v).smooth w') B' {κ₂'} {κ₂'.1} hB₂₂).symm.trans
    ι₂).trans ((r176s_smoothRestrictIso' _ h1A w₃).trans
      (w3di_restrictRestrictIso ρ (r176s_KA ρ v) (r176s_KB _ w₃)))
  have t1 : ∀ m, ((w3di_restrictRestrictBlockIso ((ρ.smooth v).smooth w') B' {κ₁'} {κ₁'.1} hB₂₁).symm.Φ m).1.1 = m.1 :=
    fun m => rfl
  have t2 : ∀ m, (ι₁.Φ m).1 = ιAS.Φ m.1 := fun m => rfl
  have t3 : ∀ t, (ιAS.Φ t).1.1 = t.1.1.1 := fun t => rfl
  have t4 : ∀ y, ((r176s_smoothRestrictIso _ h1A w₃).Φ y).1 = y.1.1 := fun y => rfl
  have t5 : ∀ x, ((w3di_restrictRestrictIso ρ (r176s_KA ρ v) (r176s_KA _ w₃)).Φ x).1 = x.1.1 := fun x => rfl
  have hχ₁ : ∀ m, (χ₁.Φ m).1 = m.1.1.1 := fun m => rfl
  have hχ₂ : ∀ m, (χ₂.Φ m).1 = m.1.1.1 := fun m => rfl
  -- the B-side
  obtain ⟨B'', hB'₂, hB''₂⟩ := w3di_block_exists (ρ.smooth v) w' hself (r176s_smoothB' ρ v)
  have hv1 : (ρ.smooth v).comp w' ∉ r176s_smoothB' ρ v := by
    rw [r176s_mem_smoothB', hcompw]
    exact (Record.smooth_comps_ne_of_self ρ v hvself).symm
  have hv2 : (ρ.smooth v).comp ((ρ.smooth v).pair w') ∉ r176s_smoothB' ρ v := by
    rw [r176s_mem_smoothB', hcompw']
    exact (Record.smooth_comps_ne_of_self ρ v hvself).symm
  let ιD := w3di_rdIso (ρ.smooth v) w' (r176s_smoothB' ρ v) hv1 hv2 B'' hB'₂ hB''₂
  let ιB0 := ιD.trans (r176s_smoothRestrictIso' ρ h1 v)
  have hcardB : B''.card = 1 := by
    have e := Finset.card_eq_of_equiv (ιD.e : ↥B'' ≃ ↥(r176s_smoothB' ρ v))
    rw [e]
    exact Finset.card_singleton _
  obtain ⟨κB, hκB⟩ := Finset.card_eq_one.mp hcardB
  let χB := (w3di_restrictCongr ((ρ.smooth v).smooth w') hκB.symm).trans ιB0
  have hχB : ∀ m, (χB.Φ m).1 = m.1.1.1 := fun m => rfl
  -- disjointness of the two blocks
  have hdisj : ∀ κ, κ ∈ B' → κ ∈ B'' → False := by
    intro κ hκ hκ'
    refine w3di_block_disjoint (ρ.smooth v) w' (r176s_smoothB ρ v) (r176s_smoothB' ρ v) ?_ B' B'' hB' hB'' hB'₂ hB''₂ κ hκ hκ'
    intro c hc hc'
    rw [r176s_mem_smoothB] at hc
    rw [r176s_mem_smoothB'] at hc'
    exact Record.smooth_comps_ne_of_self ρ v hvself (hc'.symm.trans hc)
  have hκBmem : κB ∈ B'' := by rw [hκB]; exact Finset.mem_singleton_self _
  refine ⟨{ κB := κB, κ₁ := κ₁'.1, κ₂ := κ₂'.1
            K₁ := w3di_innerKeep ρ (r176s_KA ρ v) (r176s_KA _ w₃)
            K₂ := w3di_innerKeep ρ (r176s_KA ρ v) (r176s_KB _ w₃)
            ne_B1 := fun h => hdisj _ (h ▸ κ₁'.2) hκBmem
            ne_B2 := fun h => hdisj _ (h ▸ κ₂'.2) hκBmem
            ne_12 := fun h => hκ₁₂ (Subtype.ext h)
            count3 := hcount3
            keep₁ := ?_, keep₂ := ?_
            isoB := ⟨χB⟩, iso₁ := ⟨χ₁⟩, iso₂ := ⟨χ₂⟩
            rkB := ?_, rk₁ := ?_, rk₂ := ?_ }⟩
  · intro u
    rw [w3di_crossKeep_innerKeep_iff]
    constructor
    · rintro ⟨h, h2⟩
      have h2' := (r176s_crossKeep_KA_iff _ w₃ ⟨u, h⟩).mp h2
      exact ⟨(r176s_crossKeep_KA_iff ρ v u).mp h,
        (w3di_arcBetween_restrictCrossings_iff ρ h1 _ w₃ ⟨u, h⟩ _).mp h2'.1,
        (w3di_arcBetween_restrictCrossings_iff ρ h1 _ w₃ _ _).mp h2'.2⟩
    · rintro ⟨h, h2⟩
      have h' := (r176s_crossKeep_KA_iff ρ v u).mpr h
      exact ⟨h', (r176s_crossKeep_KA_iff _ w₃ ⟨u, h'⟩).mpr
        ⟨(w3di_arcBetween_restrictCrossings_iff ρ h1 _ w₃ ⟨u, h'⟩ _).mpr h2.1,
         (w3di_arcBetween_restrictCrossings_iff ρ h1 _ w₃ _ _).mpr h2.2⟩⟩
  · intro u
    rw [w3di_crossKeep_innerKeep_iff]
    constructor
    · rintro ⟨h, h2⟩
      have h2' := (r176s_crossKeep_KB_iff _ w₃ ⟨u, h⟩).mp h2
      exact ⟨(r176s_crossKeep_KA_iff ρ v u).mp h,
        (w3di_arcBetween_restrictCrossings_iff ρ h1 _ _ ⟨u, h⟩ w₃).mp h2'.1,
        (w3di_arcBetween_restrictCrossings_iff ρ h1 _ _ _ w₃).mp h2'.2⟩
    · rintro ⟨h, h2⟩
      have h' := (r176s_crossKeep_KA_iff ρ v u).mpr h
      exact ⟨h', (r176s_crossKeep_KB_iff _ w₃ ⟨u, h'⟩).mpr
        ⟨(w3di_arcBetween_restrictCrossings_iff ρ h1 _ _ ⟨u, h'⟩ w₃).mpr h2.1,
         (w3di_arcBetween_restrictCrossings_iff ρ h1 _ _ _ w₃).mpr h2.2⟩⟩
  · exact w3di_restrictKeep_iff_of_iso _ _ _ _ _ (w3di_val_val_injective ρ v w') χB hχB
  · exact w3di_restrictKeep_iff_of_iso _ _ _ _ _ (w3di_val_val_injective ρ v w') χ₁ hχ₁
  · exact w3di_restrictKeep_iff_of_iso _ _ _ _ _ (w3di_val_val_injective ρ v w') χ₂ hχ₂

end W3DI_Double


/-! ### G. The word `(α₁ β₁ | X | β₂ γ₁ | Y | γ₂ α₂ | W)` on the contact carrier: positions, owners -/

section W3DI_Geom
variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)

/-- **The word data**: three retained crossings `α, β, γ` of the carrier `q₀` of `Q`, with visits
`α₁ α₂`, `β₁ β₂`, `γ₁ γ₂` (twins), outside `Q`, `S = Q ∪ {α, β, γ}`, the three edge adjacencies of the
traversal circle `σ α₁ = β₁`, `σ β₂ = γ₁`, `σ γ₂ = α₂` (the word `α₁ β₁ | β₂ γ₁ | γ₂ α₂`), `α₁` on `q₀`, and
the three outer `S`-carriers `owner_S α₁`, `owner_S β₂`, `owner_S γ₂` pairwise distinct. -/
structure w3di_WordData (Q S : Finset (Crossing P)) (q₀ : GeoComponent hP Q)
    (α₁ α₂ β₁ β₂ γ₁ γ₂ : Visit P) : Prop where
  tα : visitTwin α₁ = α₂
  tα' : visitTwin α₂ = α₁
  tβ : visitTwin β₁ = β₂
  tβ' : visitTwin β₂ = β₁
  tγ : visitTwin γ₁ = γ₂
  tγ' : visitTwin γ₂ = γ₁
  αβ : α₁.1 ≠ β₁.1
  αγ : α₁.1 ≠ γ₁.1
  βγ : β₁.1 ≠ γ₁.1
  αQ : α₁.1 ∉ Q
  βQ : β₁.1 ∉ Q
  γQ : γ₁.1 ∉ Q
  hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = α₁.1 ∨ x = β₁.1 ∨ x = γ₁.1
  wαβ : geoMarkSuccessor hP (Sum.inr α₁) = Sum.inr β₁
  wβγ : geoMarkSuccessor hP (Sum.inr β₂) = Sum.inr γ₁
  wγα : geoMarkSuccessor hP (Sum.inr γ₂) = Sum.inr α₂
  hq₀ : geoOwner hP Q (Sum.inr α₁) = q₀
  neαβ : geoOwner hP S (Sum.inr α₁) ≠ geoOwner hP S (Sum.inr β₂)
  neαγ : geoOwner hP S (Sum.inr α₁) ≠ geoOwner hP S (Sum.inr γ₂)
  neβγ : geoOwner hP S (Sum.inr β₂) ≠ geoOwner hP S (Sum.inr γ₂)

variable {Q S : Finset (Crossing P)} (hQ : GeoIndependent hP Q) (hS : GeoIndependent hP S)
  {q₀ : GeoComponent hP Q} {α₁ α₂ β₁ β₂ γ₁ γ₂ : Visit P}
  (D : w3di_WordData hP Q S q₀ α₁ α₂ β₁ β₂ γ₁ γ₂)

include D

theorem w3di_α12 : α₂.1 = α₁.1 := by rw [← D.tα]; rfl
theorem w3di_β12 : β₂.1 = β₁.1 := by rw [← D.tβ]; rfl
theorem w3di_γ12 : γ₂.1 = γ₁.1 := by rw [← D.tγ]; rfl
theorem w3di_QS : Q ⊆ S := fun x hx => (D.hSeq x).mpr (Or.inl hx)
theorem w3di_α₁S : α₁.1 ∈ S := (D.hSeq _).mpr (Or.inr (Or.inl rfl))
theorem w3di_β₁S : β₁.1 ∈ S := (D.hSeq _).mpr (Or.inr (Or.inr (Or.inl rfl)))
theorem w3di_γ₁S : γ₁.1 ∈ S := (D.hSeq _).mpr (Or.inr (Or.inr (Or.inr rfl)))
theorem w3di_α₂Q : α₂.1 ∉ Q := by rw [w3di_α12 hP D]; exact D.αQ
theorem w3di_β₂Q : β₂.1 ∉ Q := by rw [w3di_β12 hP D]; exact D.βQ
theorem w3di_γ₂Q : γ₂.1 ∉ Q := by rw [w3di_γ12 hP D]; exact D.γQ

/-- the `Q`-successor of the three "entry" visits -/
theorem w3di_f_α₁ : geoSmoothingSuccessor hP Q (Sum.inr α₁) = Sum.inr β₁ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP Q α₁ D.αQ, D.wαβ]
theorem w3di_f_β₂ : geoSmoothingSuccessor hP Q (Sum.inr β₂) = Sum.inr γ₁ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP Q β₂ (w3di_β₂Q hP D), D.wβγ]
theorem w3di_f_γ₂ : geoSmoothingSuccessor hP Q (Sum.inr γ₂) = Sum.inr α₂ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP Q γ₂ (w3di_γ₂Q hP D), D.wγα]

/-- the `S`-successor at the three "exit" visits jumps to the polygon successor of the twin -/
theorem w3di_g_α₁ : geoSmoothingSuccessor hP S (Sum.inr α₁) = geoSmoothingSuccessor hP Q (Sum.inr α₂) := by
  rw [geoSmoothingSuccessor_visit_of_mem hP S α₁ (w3di_α₁S hP D), D.tα,
    geoSmoothingSuccessor_visit_of_not_mem hP Q α₂ (w3di_α₂Q hP D)]
theorem w3di_g_β₂ : geoSmoothingSuccessor hP S (Sum.inr β₂) = geoSmoothingSuccessor hP Q (Sum.inr β₁) := by
  have : β₂.1 ∈ S := by rw [w3di_β12 hP D]; exact w3di_β₁S hP D
  rw [geoSmoothingSuccessor_visit_of_mem hP S β₂ this, D.tβ',
    geoSmoothingSuccessor_visit_of_not_mem hP Q β₁ D.βQ]
theorem w3di_g_γ₂ : geoSmoothingSuccessor hP S (Sum.inr γ₂) = geoSmoothingSuccessor hP Q (Sum.inr γ₁) := by
  have : γ₂.1 ∈ S := by rw [w3di_γ12 hP D]; exact w3di_γ₁S hP D
  rw [geoSmoothingSuccessor_visit_of_mem hP S γ₂ this, D.tγ',
    geoSmoothingSuccessor_visit_of_not_mem hP Q γ₁ D.γQ]

include hS in
/-- all six visits lie on `q₀` -/
theorem w3di_own_six :
    geoOwner hP Q (Sum.inr α₂) = q₀ ∧ geoOwner hP Q (Sum.inr β₁) = q₀ ∧ geoOwner hP Q (Sum.inr β₂) = q₀ ∧
      geoOwner hP Q (Sum.inr γ₁) = q₀ ∧ geoOwner hP Q (Sum.inr γ₂) = q₀ := by
  have hβ₁ : geoOwner hP Q (Sum.inr β₁) = q₀ := by
    rw [← w3di_f_α₁ hP D, geoOwner_successor, D.hq₀]
  have hβ₂ : geoOwner hP Q (Sum.inr β₂) = q₀ := by
    have := geoIndependent_remaining_pair_owners hP hS Q (w3di_QS hP D) β₁ (w3di_β₁S hP D) D.βQ
    rw [D.tβ] at this
    exact this.symm.trans hβ₁
  have hγ₁ : geoOwner hP Q (Sum.inr γ₁) = q₀ := by
    rw [← w3di_f_β₂ hP D, geoOwner_successor, hβ₂]
  have hγ₂ : geoOwner hP Q (Sum.inr γ₂) = q₀ := by
    have := geoIndependent_remaining_pair_owners hP hS Q (w3di_QS hP D) γ₁ (w3di_γ₁S hP D) D.γQ
    rw [D.tγ] at this
    exact this.symm.trans hγ₁
  have hα₂ : geoOwner hP Q (Sum.inr α₂) = q₀ := by
    rw [← w3di_f_γ₂ hP D, geoOwner_successor, hγ₂]
  exact ⟨hα₂, hβ₁, hβ₂, hγ₁, hγ₂⟩

/-- **The positions of the six visits along the `Q`-orbit of `α₁`**: `α₁ = 0`, `β₁ = 1`, `β₂ = p`,
`γ₁ = p + 1`, `γ₂ = r`, `α₂ = r + 1` with `1 < p`, `p + 1 < r`, `r + 1 < N` (`N` = the length of the
mark list of `q₀`). -/
structure w3di_PosData (hP : CrossingGeometry P) (Q : Finset (Crossing P)) (q₀ : GeoComponent hP Q)
    (α₁ α₂ β₁ β₂ γ₁ γ₂ : Visit P) where
  p : ℕ
  r : ℕ
  hp1 : 1 < p
  hpr : p + 1 < r
  hrN : r + 1 < (geoComponentMarkList hP Q q₀).length
  e1 : (geoSmoothingSuccessor hP Q ^ 1) (Sum.inr α₁) = Sum.inr β₁
  ep : (geoSmoothingSuccessor hP Q ^ p) (Sum.inr α₁) = Sum.inr β₂
  ep1 : (geoSmoothingSuccessor hP Q ^ (p + 1)) (Sum.inr α₁) = Sum.inr γ₁
  er : (geoSmoothingSuccessor hP Q ^ r) (Sum.inr α₁) = Sum.inr γ₂
  er1 : (geoSmoothingSuccessor hP Q ^ (r + 1)) (Sum.inr α₁) = Sum.inr α₂

include hQ in
theorem w3di_pow_inj {i j : ℕ} (hi : i < (geoComponentMarkList hP Q q₀).length)
    (hj : j < (geoComponentMarkList hP Q q₀).length)
    (h : (geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₁) = (geoSmoothingSuccessor hP Q ^ j) (Sum.inr α₁)) :
    i = j :=
  r176o_pow_inj hP hQ q₀ D.hq₀ hi hj h

include hQ in
theorem w3di_pow_N : (geoSmoothingSuccessor hP Q ^ (geoComponentMarkList hP Q q₀).length) (Sum.inr α₁) =
    Sum.inr α₁ :=
  r176o_pow_length_fixes hP hQ q₀ D.hq₀

include hQ in
/-- **the agreement off the six visits**: at a mark of `q₀` other than the six triangle visits, the
`S`-successor is the `Q`-successor -/
theorem w3di_agree (pd : w3di_PosData hP Q q₀ α₁ α₂ β₁ β₂ γ₁ γ₂) {j : ℕ}
    (hjN : j < (geoComponentMarkList hP Q q₀).length)
    (hj : j ≠ 0 ∧ j ≠ 1 ∧ j ≠ pd.p ∧ j ≠ pd.p + 1 ∧ j ≠ pd.r ∧ j ≠ pd.r + 1) :
    geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP Q ^ j) (Sum.inr α₁)) =
      geoSmoothingSuccessor hP Q ((geoSmoothingSuccessor hP Q ^ j) (Sum.inr α₁)) := by
  have hN := CV.markList_length_pos hP q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  obtain ⟨m, hm⟩ : ∃ m, (geoSmoothingSuccessor hP Q ^ j) (Sum.inr α₁) = m := ⟨_, rfl⟩
  rw [hm]
  rcases m with i | z
  · rw [geoSmoothingSuccessor_vertex, geoSmoothingSuccessor_vertex]
  · by_cases hzQ : z.1 ∈ Q
    · rw [geoSmoothingSuccessor_visit_of_mem hP S z (w3di_QS hP D hzQ),
        geoSmoothingSuccessor_visit_of_mem hP Q z hzQ]
    · by_cases hzS : z.1 ∈ S
      · exfalso
        have hidx : ∀ {i : ℕ}, i < (geoComponentMarkList hP Q q₀).length →
            (geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₁) = Sum.inr z → j = i :=
          fun hi h => w3di_pow_inj hP hQ D hjN hi (hm.trans h.symm)
        rcases (D.hSeq z.1).mp hzS with h | h | h | h
        · exact hzQ h
        · rcases visit_eq_or_twin α₁ z h with rfl | rfl
          · exact hj.1 (hidx hN (by rw [pow_zero, Perm.one_apply]))
          · rw [D.tα] at hidx
            exact hj.2.2.2.2.2 (hidx pd.hrN pd.er1)
        · rcases visit_eq_or_twin β₁ z h with rfl | rfl
          · exact hj.2.1 (hidx (by omega) pd.e1)
          · rw [D.tβ] at hidx
            exact hj.2.2.1 (hidx (by omega) pd.ep)
        · rcases visit_eq_or_twin γ₁ z h with rfl | rfl
          · exact hj.2.2.2.1 (hidx (by omega) pd.ep1)
          · rw [D.tγ] at hidx
            exact hj.2.2.2.2.1 (hidx (by omega) pd.er)
      · rw [geoSmoothingSuccessor_visit_of_not_mem hP S z hzS,
          geoSmoothingSuccessor_visit_of_not_mem hP Q z hzQ]

include hQ hS in
/-- **the positions exist** (the order `p < r` from the distinctness of the outer carriers) -/
theorem w3di_posData_exists : Nonempty (w3di_PosData hP Q q₀ α₁ α₂ β₁ β₂ γ₁ γ₂) := by
  have hN := CV.markList_length_pos hP q₀
  obtain ⟨hα₂, hβ₁, hβ₂, hγ₁, hγ₂⟩ := w3di_own_six hP hS D
  obtain ⟨p, hpN, hp⟩ := r176o_exists_pow hP hQ q₀ D.hq₀ hβ₂
  obtain ⟨r, hrN, hr⟩ := r176o_exists_pow hP hQ q₀ D.hq₀ hγ₂
  have e1 : (geoSmoothingSuccessor hP Q ^ 1) (Sum.inr α₁) = Sum.inr β₁ := by
    rw [pow_one]; exact w3di_f_α₁ hP D
  have ep1 : (geoSmoothingSuccessor hP Q ^ (p + 1)) (Sum.inr α₁) = Sum.inr γ₁ := by
    rw [pow_succ', Perm.mul_apply, hp]; exact w3di_f_β₂ hP D
  have er1 : (geoSmoothingSuccessor hP Q ^ (r + 1)) (Sum.inr α₁) = Sum.inr α₂ := by
    rw [pow_succ', Perm.mul_apply, hr]; exact w3di_f_γ₂ hP D
  have hfix := w3di_pow_N hP hQ D
  have inj : ∀ {i j : ℕ}, i < (geoComponentMarkList hP Q q₀).length →
      j < (geoComponentMarkList hP Q q₀).length →
      (geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₁) = (geoSmoothingSuccessor hP Q ^ j) (Sum.inr α₁) →
      i = j := fun hi hj h => w3di_pow_inj hP hQ D hi hj h
  have hp1N : p + 1 < (geoComponentMarkList hP Q q₀).length := by
    by_contra h
    have : p + 1 = (geoComponentMarkList hP Q q₀).length := by omega
    rw [this, hfix] at ep1
    exact D.αγ (by rw [Sum.inr.inj ep1])
  have hr1N : r + 1 < (geoComponentMarkList hP Q q₀).length := by
    by_contra h
    have : r + 1 = (geoComponentMarkList hP Q q₀).length := by omega
    rw [this, hfix] at er1
    exact visitTwin_ne α₁ (by rw [D.tα]; exact (Sum.inr.inj er1).symm)
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, pow_zero, Perm.one_apply] at hp
    exact D.αβ (by rw [Sum.inr.inj hp, w3di_β12 hP D])
  have hp1 : p ≠ 1 := by
    intro h
    rw [h, e1] at hp
    exact visitTwin_ne β₁ (by rw [D.tβ]; exact (Sum.inr.inj hp).symm)
  have hpr1 : p ≠ r + 1 := by
    intro h
    rw [h, er1] at hp
    exact D.αβ (by rw [← w3di_α12 hP D, Sum.inr.inj hp, w3di_β12 hP D])
  have hp1r : p + 1 ≠ r := by
    intro h
    rw [h, hr] at ep1
    exact visitTwin_ne γ₁ (by rw [D.tγ]; exact Sum.inr.inj ep1)
  have hpr : p ≠ r := by
    intro h
    rw [h, hr] at hp
    exact D.βγ (by rw [← w3di_β12 hP D, ← w3di_γ12 hP D, Sum.inr.inj hp])
  -- the order: `r < p` would put `β₂` on the carrier of `α₁`
  have horder : p < r := by
    by_contra hle
    have hrp : r + 1 < p := by omega
    -- the `S`-orbit of `α₁` follows the `Q`-orbit of `α₂` up to `β₂`
    have hagree : ∀ i, 0 < i → i < p - (r + 1) →
        geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₂)) =
          geoSmoothingSuccessor hP Q ((geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₂)) := by
      intro i hi0 hik
      have e : (geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₂) =
          (geoSmoothingSuccessor hP Q ^ (i + (r + 1))) (Sum.inr α₁) := by
        rw [pow_add, Perm.mul_apply, er1]
      rw [e]
      -- a provisional position record for `w3di_agree` is not available (`p < r` is being proved):
      -- argue directly with the six positions
      obtain ⟨m, hm⟩ : ∃ m, (geoSmoothingSuccessor hP Q ^ (i + (r + 1))) (Sum.inr α₁) = m := ⟨_, rfl⟩
      rw [hm]
      have hjN : i + (r + 1) < (geoComponentMarkList hP Q q₀).length := by omega
      rcases m with k | z
      · rw [geoSmoothingSuccessor_vertex, geoSmoothingSuccessor_vertex]
      · by_cases hzQ : z.1 ∈ Q
        · rw [geoSmoothingSuccessor_visit_of_mem hP S z (w3di_QS hP D hzQ),
            geoSmoothingSuccessor_visit_of_mem hP Q z hzQ]
        · by_cases hzS : z.1 ∈ S
          · exfalso
            have hidx : ∀ {l : ℕ}, l < (geoComponentMarkList hP Q q₀).length →
                (geoSmoothingSuccessor hP Q ^ l) (Sum.inr α₁) = Sum.inr z → i + (r + 1) = l :=
              fun hl h => inj hjN hl (hm.trans h.symm)
            rcases (D.hSeq z.1).mp hzS with h | h | h | h
            · exact hzQ h
            · rcases visit_eq_or_twin α₁ z h with rfl | rfl
              · have := hidx hN (by rw [pow_zero, Perm.one_apply]); omega
              · rw [D.tα] at hidx
                have := hidx hr1N er1; omega
            · rcases visit_eq_or_twin β₁ z h with rfl | rfl
              · have := hidx (by omega) e1; omega
              · rw [D.tβ] at hidx
                have := hidx hpN hp; omega
            · rcases visit_eq_or_twin γ₁ z h with rfl | rfl
              · have := hidx hp1N ep1; omega
              · rw [D.tγ] at hidx
                have := hidx hrN hr; omega
          · rw [geoSmoothingSuccessor_visit_of_not_mem hP S z hzS,
              geoSmoothingSuccessor_visit_of_not_mem hP Q z hzQ]
    have htr := r176o_orbit_transfer (geoSmoothingSuccessor hP Q) (geoSmoothingSuccessor hP S)
      (a := Sum.inr α₁) (b := Sum.inr α₂) (k := p - (r + 1)) (w3di_g_α₁ hP D) hagree (p - (r + 1))
      (by omega) le_rfl
    have hβ : (geoSmoothingSuccessor hP S ^ (p - (r + 1))) (Sum.inr α₁) = Sum.inr β₂ := by
      rw [htr, ← hp, ← er1, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega)]
    apply D.neαβ
    rw [← hβ, geo_pow_owner]
  exact ⟨⟨p, r, by omega, by omega, hr1N, e1, hp, ep1, hr, er1⟩⟩


/-! ### G2. The `S`-owners read on the orbit index -/

section W3DI_Owners
variable (pd : w3di_PosData hP Q q₀ α₁ α₂ β₁ β₂ γ₁ γ₂)

include hQ in
/-- **`owner_S m = owner_S α₁ ↔ i = 0 ∨ r + 1 < i`** (the arc `W`) -/
theorem w3di_owner_α_iff {m : Mark P} {i : ℕ} (hi : i < (geoComponentMarkList hP Q q₀).length)
    (hm : (geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₁) = m) :
    geoOwner hP S m = geoOwner hP S (Sum.inr α₁) ↔ i = 0 ∨ pd.r + 1 < i := by
  have hN := CV.markList_length_pos hP q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  have hfix := w3di_pow_N hP hQ D
  rw [eq_comm, geoOwner_eq_iff]
  have hagree : ∀ j, 0 < j → j < (geoComponentMarkList hP Q q₀).length - (pd.r + 1) →
      geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP Q ^ j) (Sum.inr α₂)) =
        geoSmoothingSuccessor hP Q ((geoSmoothingSuccessor hP Q ^ j) (Sum.inr α₂)) := by
    intro j hj0 hjk
    have e : (geoSmoothingSuccessor hP Q ^ j) (Sum.inr α₂) =
        (geoSmoothingSuccessor hP Q ^ (j + (pd.r + 1))) (Sum.inr α₁) := by
      rw [pow_add, Perm.mul_apply, pd.er1]
    rw [e]
    exact w3di_agree hP hQ D pd (by omega) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hka : (geoSmoothingSuccessor hP Q ^ ((geoComponentMarkList hP Q q₀).length - (pd.r + 1)))
      (Sum.inr α₂) = Sum.inr α₁ := by
    rw [← pd.er1, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (le_of_lt hrN), hfix]
  rw [r176o_sameCycle_transfer_iff (geoSmoothingSuccessor hP Q) (geoSmoothingSuccessor hP S)
    (by omega) (w3di_g_α₁ hP D) hagree hka m]
  constructor
  · rintro (rfl | ⟨j, hj0, hjk, hj⟩)
    · left
      exact w3di_pow_inj hP hQ D hi hN (hm.trans (by rw [pow_zero, Perm.one_apply]))
    · right
      have e : (geoSmoothingSuccessor hP Q ^ (j + (pd.r + 1))) (Sum.inr α₁) = m := by
        rw [pow_add, Perm.mul_apply, pd.er1, hj]
      have := w3di_pow_inj hP hQ D hi (by omega) (hm.trans e.symm)
      omega
  · rintro (rfl | h)
    · left
      rw [pow_zero, Perm.one_apply] at hm
      exact hm.symm
    · right
      refine ⟨i - (pd.r + 1), by omega, by omega, ?_⟩
      rw [← hm, ← pd.er1, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (le_of_lt h)]

include hQ in
/-- **`owner_S m = owner_S β₂ ↔ i = p ∨ 1 < i < p`** (the arc `X`) -/
theorem w3di_owner_β_iff {m : Mark P} {i : ℕ} (hi : i < (geoComponentMarkList hP Q q₀).length)
    (hm : (geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₁) = m) :
    geoOwner hP S m = geoOwner hP S (Sum.inr β₂) ↔ i = pd.p ∨ (1 < i ∧ i < pd.p) := by
  have hN := CV.markList_length_pos hP q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  have hf1 := w3di_f_α₁ hP D
  rw [eq_comm, geoOwner_eq_iff]
  have hagree : ∀ j, 0 < j → j < pd.p - 1 →
      geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP Q ^ j) (Sum.inr β₁)) =
        geoSmoothingSuccessor hP Q ((geoSmoothingSuccessor hP Q ^ j) (Sum.inr β₁)) := by
    intro j hj0 hjk
    have e : (geoSmoothingSuccessor hP Q ^ j) (Sum.inr β₁) =
        (geoSmoothingSuccessor hP Q ^ (j + 1)) (Sum.inr α₁) := by
      rw [pow_succ, Perm.mul_apply, hf1]
    rw [e]
    exact w3di_agree hP hQ D pd (by omega) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hka : (geoSmoothingSuccessor hP Q ^ (pd.p - 1)) (Sum.inr β₁) = Sum.inr β₂ := by
    rw [← hf1, ← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega), pd.ep]
  rw [r176o_sameCycle_transfer_iff (geoSmoothingSuccessor hP Q) (geoSmoothingSuccessor hP S)
    (by omega) (w3di_g_β₂ hP D) hagree hka m]
  constructor
  · rintro (rfl | ⟨j, hj0, hjk, hj⟩)
    · left
      exact w3di_pow_inj hP hQ D hi (by omega) (hm.trans pd.ep.symm)
    · right
      have e : (geoSmoothingSuccessor hP Q ^ (j + 1)) (Sum.inr α₁) = m := by
        rw [pow_succ, Perm.mul_apply, hf1, hj]
      have := w3di_pow_inj hP hQ D hi (by omega) (hm.trans e.symm)
      omega
  · rintro (rfl | h)
    · left
      exact hm.symm.trans pd.ep
    · right
      refine ⟨i - 1, by omega, by omega, ?_⟩
      rw [← hm, ← hf1, ← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)]

include hQ in
/-- **`owner_S m = owner_S γ₂ ↔ i = r ∨ p + 1 < i < r`** (the arc `Y`) -/
theorem w3di_owner_γ_iff {m : Mark P} {i : ℕ} (hi : i < (geoComponentMarkList hP Q q₀).length)
    (hm : (geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₁) = m) :
    geoOwner hP S m = geoOwner hP S (Sum.inr γ₂) ↔ i = pd.r ∨ (pd.p + 1 < i ∧ i < pd.r) := by
  have hN := CV.markList_length_pos hP q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  rw [eq_comm, geoOwner_eq_iff]
  have hagree : ∀ j, 0 < j → j < pd.r - (pd.p + 1) →
      geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP Q ^ j) (Sum.inr γ₁)) =
        geoSmoothingSuccessor hP Q ((geoSmoothingSuccessor hP Q ^ j) (Sum.inr γ₁)) := by
    intro j hj0 hjk
    have e : (geoSmoothingSuccessor hP Q ^ j) (Sum.inr γ₁) =
        (geoSmoothingSuccessor hP Q ^ (j + (pd.p + 1))) (Sum.inr α₁) := by
      rw [pow_add, Perm.mul_apply, pd.ep1]
    rw [e]
    exact w3di_agree hP hQ D pd (by omega) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hka : (geoSmoothingSuccessor hP Q ^ (pd.r - (pd.p + 1))) (Sum.inr γ₁) = Sum.inr γ₂ := by
    rw [← pd.ep1, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (le_of_lt hpr), pd.er]
  rw [r176o_sameCycle_transfer_iff (geoSmoothingSuccessor hP Q) (geoSmoothingSuccessor hP S)
    (by omega) (w3di_g_γ₂ hP D) hagree hka m]
  constructor
  · rintro (rfl | ⟨j, hj0, hjk, hj⟩)
    · left
      exact w3di_pow_inj hP hQ D hi (by omega) (hm.trans pd.er.symm)
    · right
      have e : (geoSmoothingSuccessor hP Q ^ (j + (pd.p + 1))) (Sum.inr α₁) = m := by
        rw [pow_add, Perm.mul_apply, pd.ep1, hj]
      have := w3di_pow_inj hP hQ D hi (by omega) (hm.trans e.symm)
      omega
  · rintro (rfl | h)
    · left
      exact hm.symm.trans pd.er
    · right
      refine ⟨i - (pd.p + 1), by omega, by omega, ?_⟩
      rw [← hm, ← pd.ep1, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (le_of_lt h.1)]

include hQ in
/-- a retained visit of `q₀` lies at a crossing of `S` iff its index is one of the six -/
theorem w3di_mem_S_iff {z : Visit P} (hzQ : z.1 ∉ Q) {i : ℕ}
    (hi : i < (geoComponentMarkList hP Q q₀).length)
    (hz : (geoSmoothingSuccessor hP Q ^ i) (Sum.inr α₁) = Sum.inr z) :
    z.1 ∈ S ↔ i = 0 ∨ i = 1 ∨ i = pd.p ∨ i = pd.p + 1 ∨ i = pd.r ∨ i = pd.r + 1 := by
  have hN := CV.markList_length_pos hP q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  have hidx : ∀ {l : ℕ}, l < (geoComponentMarkList hP Q q₀).length →
      (geoSmoothingSuccessor hP Q ^ l) (Sum.inr α₁) = Sum.inr z → i = l :=
    fun hl h => w3di_pow_inj hP hQ D hi hl (hz.trans h.symm)
  constructor
  · intro hzS
    rcases (D.hSeq z.1).mp hzS with h | h | h | h
    · exact absurd h hzQ
    · rcases visit_eq_or_twin α₁ z h with rfl | rfl
      · exact Or.inl (hidx hN (by rw [pow_zero, Perm.one_apply]))
      · rw [D.tα] at hidx
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hidx hrN pd.er1)))))
    · rcases visit_eq_or_twin β₁ z h with rfl | rfl
      · exact Or.inr (Or.inl (hidx (by omega) pd.e1))
      · rw [D.tβ] at hidx
        exact Or.inr (Or.inr (Or.inl (hidx (by omega) pd.ep)))
    · rcases visit_eq_or_twin γ₁ z h with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hidx (by omega) pd.ep1))))
      · rw [D.tγ] at hidx
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hidx (by omega) pd.er)))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · rw [pow_zero, Perm.one_apply] at hz
      rw [← Sum.inr.inj hz]; exact w3di_α₁S hP D
    · rw [pd.e1] at hz
      rw [← Sum.inr.inj hz]; exact w3di_β₁S hP D
    · rw [pd.ep] at hz
      rw [← Sum.inr.inj hz, w3di_β12 hP D]; exact w3di_β₁S hP D
    · rw [pd.ep1] at hz
      rw [← Sum.inr.inj hz]; exact w3di_γ₁S hP D
    · rw [pd.er] at hz
      rw [← Sum.inr.inj hz, w3di_γ12 hP D]; exact w3di_γ₁S hP D
    · rw [pd.er1] at hz
      rw [← Sum.inr.inj hz, w3di_α12 hP D]; exact w3di_α₁S hP D

end W3DI_Owners

/-! ### G3. The lift of the contact carrier: arcs of its record read on the orbit index -/

omit D in
/-- membership in the retained set of a carrier, through the two visits -/
theorem w3di_mem_gCC_iff (S : Finset (Crossing P)) (X : GeoComponent hP S) (x : Visit P) :
    x.1 ∈ geoCarrierCrossings hP S X ↔
      x.1 ∉ S ∧ geoOwner hP S (Sum.inr x) = X ∧ geoOwner hP S (Sum.inr (visitTwin x)) = X := by
  rw [mem_geoCarrierCrossings]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 x rfl, h2 _ (visitTwin_crossing x)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun w hw => ?_⟩
    rcases visit_eq_or_twin x w hw with rfl | rfl
    · exact h2
    · exact h3

end W3DI_Geom

section W3DI_Lift
variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {Q S : Finset (Crossing P)} (hQ : GeoIndependent hG.cg Q) (hS : GeoIndependent hG.cg S)
  {q₀ : GeoComponent hG.cg Q} {α₁ α₂ β₁ β₂ γ₁ γ₂ : Visit P}
  (D : w3di_WordData hG.cg Q S q₀ α₁ α₂ β₁ β₂ γ₁ γ₂)
  (pd : w3di_PosData hG.cg Q q₀ α₁ α₂ β₁ β₂ γ₁ γ₂)

include D in
theorem w3di_lift_idx (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) :
    ∃ i < (geoComponentMarkList hG.cg Q q₀).length,
      (geoSmoothingSuccessor hG.cg Q ^ i) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ u) :=
  r176o_exists_pow hG.cg hQ q₀ D.hq₀ (liftVisit_owner hn hG hQ q₀ u)

theorem w3di_lift_notQ (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) : (liftVisit hn hG hQ q₀ u).1 ∉ Q :=
  ((mem_geoCarrierCrossings _ _ _ _).mp (liftVisit_mem hn hG hQ q₀ u)).1

include D in
/-- **the arc order of the lift's record is the index order on the orbit of `α₁`** -/
theorem w3di_arc_idx (x u y : (geoPositiveLift hn hG hQ q₀).Γ.Visit) {i j l : ℕ}
    (hi : i < (geoComponentMarkList hG.cg Q q₀).length) (hj : j < (geoComponentMarkList hG.cg Q q₀).length)
    (hl : l < (geoComponentMarkList hG.cg Q q₀).length)
    (hx : (geoSmoothingSuccessor hG.cg Q ^ i) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ x))
    (hu : (geoSmoothingSuccessor hG.cg Q ^ j) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ u))
    (hy : (geoSmoothingSuccessor hG.cg Q ^ l) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ y)) :
    (geoPositiveLift hn hG hQ q₀).record.ArcBetween x u y ↔
      ((i < j ∧ j < l) ∨ (j < l ∧ l < i) ∨ (l < i ∧ i < j)) := by
  rw [CV.arcBetween_iff_key]
  change cycBetween (geoMarkKey hG.cg (Sum.inr (liftVisit hn hG hQ q₀ x)))
    (geoMarkKey hG.cg (Sum.inr (liftVisit hn hG hQ q₀ u)))
    (geoMarkKey hG.cg (Sum.inr (liftVisit hn hG hQ q₀ y))) ↔ _
  rw [← hx, ← hu, ← hy]
  exact r176o_cyc_iff hG.cg hQ q₀ D.hq₀ hi hj hl

include D in
/-- two occurrences of the lift agree iff their indices agree -/
theorem w3di_eq_iff_idx (u x : (geoPositiveLift hn hG hQ q₀).Γ.Visit) {i l : ℕ}
    (hi : i < (geoComponentMarkList hG.cg Q q₀).length) (hl : l < (geoComponentMarkList hG.cg Q q₀).length)
    (hu : (geoSmoothingSuccessor hG.cg Q ^ i) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ u))
    (hx : (geoSmoothingSuccessor hG.cg Q ^ l) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ x)) :
    u = x ↔ i = l := by
  constructor
  · rintro rfl
    exact w3di_pow_inj hG.cg hQ D hi hl (hu.trans hx.symm)
  · rintro rfl
    exact liftVisit_injective hn hG hQ q₀ (Sum.inr.inj (hu.symm.trans hx))

/-- the chord of an occurrence: membership of another occurrence -/
theorem w3di_crossingOf_eq_iff (ρ : Record) (u x : ρ.M) :
    ρ.crossingOf u = ρ.crossingOf x ↔ u = x ∨ u = ρ.pair x := by
  rw [ρ.crossingOf_eq_iff]
  exact ρ.mem_val_iff (ρ.mem_crossingOf x) u

include hQ D pd in
/-- **`K_B` at `v ↦ α₁` is the block of the outer carrier `owner_S α₁`** (occurrence form) -/
theorem w3di_KB_iff (v : (geoPositiveLift hn hG hQ q₀).Γ.Visit) (hv : liftVisit hn hG hQ q₀ v = α₁)
    (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) :
    (geoPositiveLift hn hG hQ q₀).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hQ q₀).record v) u ↔
      (liftVisit hn hG hQ q₀ u).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr α₁)) := by
  have hN := CV.markList_length_pos hG.cg q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  obtain ⟨i, hi, hu⟩ := w3di_lift_idx hn hG hQ D u
  obtain ⟨i', hi', hu'⟩ := w3di_lift_idx hn hG hQ D ((geoPositiveLift hn hG hQ q₀).twin u)
  have htw : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin u) = visitTwin (liftVisit hn hG hQ q₀ u) :=
    liftVisit_twin hn hG hQ q₀ u
  have hzQ := w3di_lift_notQ hn hG hQ u
  have hzQ' : (visitTwin (liftVisit hn hG hQ q₀ u)).1 ∉ Q := by rw [visitTwin_crossing]; exact hzQ
  have hvt : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin v) = α₂ := by
    rw [liftVisit_twin, hv, D.tα]
  have h0 : (geoSmoothingSuccessor hG.cg Q ^ 0) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ v) := by
    rw [pow_zero, Perm.one_apply, hv]
  have hr1 : (geoSmoothingSuccessor hG.cg Q ^ (pd.r + 1)) (Sum.inr α₁) =
      Sum.inr (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin v)) := by
    rw [pd.er1, hvt]
  have e1 := w3di_arc_idx hn hG hQ D ((geoPositiveLift hn hG hQ q₀).twin v) u v hrN hi hN hr1 hu h0
  have e2 := w3di_arc_idx hn hG hQ D ((geoPositiveLift hn hG hQ q₀).twin v)
    ((geoPositiveLift hn hG hQ q₀).twin u) v hrN hi' hN hr1 hu' h0
  rw [htw] at hu'
  have hS1 := w3di_mem_S_iff hG.cg hQ D pd hzQ hi hu
  have hS2 := w3di_mem_S_iff hG.cg hQ D pd hzQ' hi' hu'
  have hO1 := w3di_owner_α_iff hG.cg hQ D pd hi hu
  have hO2 := w3di_owner_α_iff hG.cg hQ D pd hi' hu'
  have hSS : (liftVisit hn hG hQ q₀ u).1 ∈ S ↔ (visitTwin (liftVisit hn hG hQ q₀ u)).1 ∈ S := by
    rw [visitTwin_crossing]
  rw [hS1, hS2] at hSS
  rw [r176s_crossKeep_KB_iff, w3di_mem_gCC_iff]
  change ((geoPositiveLift hn hG hQ q₀).record.ArcBetween ((geoPositiveLift hn hG hQ q₀).twin v) u v ∧
    (geoPositiveLift hn hG hQ q₀).record.ArcBetween ((geoPositiveLift hn hG hQ q₀).twin v)
      ((geoPositiveLift hn hG hQ q₀).twin u) v) ↔ _
  rw [e1, e2, hO1, hO2, hS1]
  omega

/-- **the six occurrences of the lift** over the six triangle visits -/
structure w3di_SixLift (hn : 3 ≤ n) (hG : CarrierGeometry P) {Q : Finset (Crossing P)}
    (hQ : GeoIndependent hG.cg Q) (q₀ : GeoComponent hG.cg Q) (α₁ β₁ β₂ γ₁ γ₂ : Visit P) where
  v : (geoPositiveLift hn hG hQ q₀).Γ.Visit
  b₁ : (geoPositiveLift hn hG hQ q₀).Γ.Visit
  b₂ : (geoPositiveLift hn hG hQ q₀).Γ.Visit
  c₁ : (geoPositiveLift hn hG hQ q₀).Γ.Visit
  c₂ : (geoPositiveLift hn hG hQ q₀).Γ.Visit
  hv : liftVisit hn hG hQ q₀ v = α₁
  hb₁ : liftVisit hn hG hQ q₀ b₁ = β₁
  hb₂ : liftVisit hn hG hQ q₀ b₂ = β₂
  hc₁ : liftVisit hn hG hQ q₀ c₁ = γ₁
  hc₂ : liftVisit hn hG hQ q₀ c₂ = γ₂

include hS D in
theorem w3di_sixLift_exists : Nonempty (w3di_SixLift hn hG hQ q₀ α₁ β₁ β₂ γ₁ γ₂) := by
  obtain ⟨hα₂, hβ₁, hβ₂, hγ₁, hγ₂⟩ := w3di_own_six hG.cg hS D
  have mem : ∀ x : Visit P, x.1 ∉ Q → geoOwner hG.cg Q (Sum.inr x) = q₀ →
      geoOwner hG.cg Q (Sum.inr (visitTwin x)) = q₀ → x.1 ∈ geoCarrierCrossings hG.cg Q q₀ := by
    intro x h1 h2 h3
    exact (w3di_mem_gCC_iff hG.cg Q q₀ x).mpr ⟨h1, h2, h3⟩
  obtain ⟨v, hv⟩ := liftVisit_surjective hn hG hQ q₀ (mem α₁ D.αQ D.hq₀ (by rw [D.tα]; exact hα₂))
  obtain ⟨b₁, hb₁⟩ := liftVisit_surjective hn hG hQ q₀ (mem β₁ D.βQ hβ₁ (by rw [D.tβ]; exact hβ₂))
  obtain ⟨b₂, hb₂⟩ := liftVisit_surjective hn hG hQ q₀
    (mem β₂ (w3di_β₂Q hG.cg D) hβ₂ (by rw [D.tβ']; exact hβ₁))
  obtain ⟨c₁, hc₁⟩ := liftVisit_surjective hn hG hQ q₀ (mem γ₁ D.γQ hγ₁ (by rw [D.tγ]; exact hγ₂))
  obtain ⟨c₂, hc₂⟩ := liftVisit_surjective hn hG hQ q₀
    (mem γ₂ (w3di_γ₂Q hG.cg D) hγ₂ (by rw [D.tγ']; exact hγ₁))
  exact ⟨⟨v, b₁, b₂, c₁, c₂, hv, hb₁, hb₂, hc₁, hc₂⟩⟩

variable (sl : w3di_SixLift hn hG hQ q₀ α₁ β₁ β₂ γ₁ γ₂)

include D pd sl in
/-- the index witnesses of the six occurrences and of their twins -/
theorem w3di_six_idx :
    (geoSmoothingSuccessor hG.cg Q ^ 0) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ sl.v) ∧
    (geoSmoothingSuccessor hG.cg Q ^ (pd.r + 1)) (Sum.inr α₁) =
      Sum.inr (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin sl.v)) ∧
    (geoSmoothingSuccessor hG.cg Q ^ 1) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ sl.b₁) ∧
    (geoSmoothingSuccessor hG.cg Q ^ pd.p) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ sl.b₂) ∧
    (geoSmoothingSuccessor hG.cg Q ^ (pd.p + 1)) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ sl.c₁) ∧
    (geoSmoothingSuccessor hG.cg Q ^ pd.r) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ sl.c₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_zero, Perm.one_apply, sl.hv]
  · rw [pd.er1, liftVisit_twin, sl.hv, D.tα]
  · rw [pd.e1, sl.hb₁]
  · rw [pd.ep, sl.hb₂]
  · rw [pd.ep1, sl.hc₁]
  · rw [pd.er, sl.hc₂]

include D pd sl in
/-- the six arcs of the lift's record, read on the index of an occurrence -/
theorem w3di_arcs_idx (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) {i : ℕ}
    (hi : i < (geoComponentMarkList hG.cg Q q₀).length)
    (hu : (geoSmoothingSuccessor hG.cg Q ^ i) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ u)) :
    (r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v u ↔ 0 < i ∧ i < pd.r + 1) ∧
    ((geoPositiveLift hn hG hQ q₀).record.ArcBetween ((geoPositiveLift hn hG hQ q₀).twin sl.v) u sl.v ↔
      pd.r + 1 < i) ∧
    ((geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.b₁ u sl.b₂ ↔ 1 < i ∧ i < pd.p) ∧
    ((geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.b₂ u sl.b₁ ↔ i = 0 ∨ pd.p < i) ∧
    ((geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.c₁ u sl.c₂ ↔ pd.p + 1 < i ∧ i < pd.r) ∧
    ((geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.c₂ u sl.c₁ ↔ i < pd.p + 1 ∨ pd.r < i) := by
  have hN := CV.markList_length_pos hG.cg q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  obtain ⟨h0, hr1, h1, hp, hp1', hr⟩ := w3di_six_idx hn hG hQ D pd sl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.v u ((geoPositiveLift hn hG hQ q₀).twin sl.v) ↔ _
    rw [w3di_arc_idx hn hG hQ D sl.v u _ hN hi hrN h0 hu hr1]
    omega
  · rw [w3di_arc_idx hn hG hQ D _ u sl.v hrN hi hN hr1 hu h0]
    omega
  · rw [w3di_arc_idx hn hG hQ D sl.b₁ u sl.b₂ (by omega) hi (by omega) h1 hu hp]
    omega
  · rw [w3di_arc_idx hn hG hQ D sl.b₂ u sl.b₁ (by omega) hi (by omega) hp hu h1]
    omega
  · rw [w3di_arc_idx hn hG hQ D sl.c₁ u sl.c₂ (by omega) hi (by omega) hp1' hu hr]
    omega
  · rw [w3di_arc_idx hn hG hQ D sl.c₂ u sl.c₁ (by omega) hi (by omega) hr hu hp1']
    omega

include D pd in
/-- the index data of an occurrence and of its twin: indices, membership in `S`, the three owners -/
theorem w3di_occ_idx (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) :
    ∃ i i' : ℕ, i < (geoComponentMarkList hG.cg Q q₀).length ∧ i' < (geoComponentMarkList hG.cg Q q₀).length ∧
      (geoSmoothingSuccessor hG.cg Q ^ i) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ u) ∧
      (geoSmoothingSuccessor hG.cg Q ^ i') (Sum.inr α₁) =
        Sum.inr (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin u)) ∧
      ((liftVisit hn hG hQ q₀ u).1 ∈ S ↔ i = 0 ∨ i = 1 ∨ i = pd.p ∨ i = pd.p + 1 ∨ i = pd.r ∨ i = pd.r + 1) ∧
      ((liftVisit hn hG hQ q₀ u).1 ∈ S ↔ i' = 0 ∨ i' = 1 ∨ i' = pd.p ∨ i' = pd.p + 1 ∨ i' = pd.r ∨ i' = pd.r + 1) ∧
      (geoOwner hG.cg S (Sum.inr (liftVisit hn hG hQ q₀ u)) = geoOwner hG.cg S (Sum.inr α₁) ↔
        i = 0 ∨ pd.r + 1 < i) ∧
      (geoOwner hG.cg S (Sum.inr (visitTwin (liftVisit hn hG hQ q₀ u))) = geoOwner hG.cg S (Sum.inr α₁) ↔
        i' = 0 ∨ pd.r + 1 < i') ∧
      (geoOwner hG.cg S (Sum.inr (liftVisit hn hG hQ q₀ u)) = geoOwner hG.cg S (Sum.inr β₂) ↔
        i = pd.p ∨ (1 < i ∧ i < pd.p)) ∧
      (geoOwner hG.cg S (Sum.inr (visitTwin (liftVisit hn hG hQ q₀ u))) = geoOwner hG.cg S (Sum.inr β₂) ↔
        i' = pd.p ∨ (1 < i' ∧ i' < pd.p)) ∧
      (geoOwner hG.cg S (Sum.inr (liftVisit hn hG hQ q₀ u)) = geoOwner hG.cg S (Sum.inr γ₂) ↔
        i = pd.r ∨ (pd.p + 1 < i ∧ i < pd.r)) ∧
      (geoOwner hG.cg S (Sum.inr (visitTwin (liftVisit hn hG hQ q₀ u))) = geoOwner hG.cg S (Sum.inr γ₂) ↔
        i' = pd.r ∨ (pd.p + 1 < i' ∧ i' < pd.r)) ∧
      ((i = 0 → i' = pd.r + 1) ∧ (i = 1 → i' = pd.p) ∧ (i = pd.p → i' = 1) ∧
        (i = pd.p + 1 → i' = pd.r) ∧ (i = pd.r → i' = pd.p + 1) ∧ (i = pd.r + 1 → i' = 0)) := by
  have hN := CV.markList_length_pos hG.cg q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  obtain ⟨i, hi, hu⟩ := w3di_lift_idx hn hG hQ D u
  obtain ⟨i', hi', hu'⟩ := w3di_lift_idx hn hG hQ D ((geoPositiveLift hn hG hQ q₀).twin u)
  have htw : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin u) = visitTwin (liftVisit hn hG hQ q₀ u) :=
    liftVisit_twin hn hG hQ q₀ u
  have hzQ := w3di_lift_notQ hn hG hQ u
  have hzQ' : (visitTwin (liftVisit hn hG hQ q₀ u)).1 ∉ Q := by rw [visitTwin_crossing]; exact hzQ
  have hu'' := hu'
  rw [htw] at hu''
  have hS2 := w3di_mem_S_iff hG.cg hQ D pd hzQ' hi' hu''
  rw [visitTwin_crossing] at hS2
  -- the twin relations on the six indices
  have tw : ∀ {l l' : ℕ} {x : Visit P}, l < (geoComponentMarkList hG.cg Q q₀).length →
      l' < (geoComponentMarkList hG.cg Q q₀).length →
      (geoSmoothingSuccessor hG.cg Q ^ l) (Sum.inr α₁) = Sum.inr x →
      (geoSmoothingSuccessor hG.cg Q ^ l') (Sum.inr α₁) = Sum.inr (visitTwin x) → i = l → i' = l' := by
    intro l l' x hl hl' hx hx' hil
    subst hil
    have e : liftVisit hn hG hQ q₀ u = x := Sum.inr.inj (hu.symm.trans hx)
    rw [e] at hu''
    exact w3di_pow_inj hG.cg hQ D hi' hl' (hu''.trans hx'.symm)
  refine ⟨i, i', hi, hi', hu, hu', w3di_mem_S_iff hG.cg hQ D pd hzQ hi hu, hS2,
    w3di_owner_α_iff hG.cg hQ D pd hi hu, w3di_owner_α_iff hG.cg hQ D pd hi' hu'',
    w3di_owner_β_iff hG.cg hQ D pd hi hu, w3di_owner_β_iff hG.cg hQ D pd hi' hu'',
    w3di_owner_γ_iff hG.cg hQ D pd hi hu, w3di_owner_γ_iff hG.cg hQ D pd hi' hu'', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tw hN hrN (by rw [pow_zero, Perm.one_apply]) (by rw [D.tα, pd.er1])
  · exact tw (by omega) (by omega) pd.e1 (by rw [D.tβ, pd.ep])
  · exact tw (by omega) (by omega) pd.ep (by rw [D.tβ', pd.e1])
  · exact tw (by omega) (by omega) pd.ep1 (by rw [D.tγ, pd.er])
  · exact tw (by omega) (by omega) pd.er (by rw [D.tγ', pd.ep1])
  · exact tw hrN hN pd.er1 (by rw [D.tα', pow_zero, Perm.one_apply])

theorem w3di_crossKeep_union_iff (ρ : Record) (K : Set ρ.Crossing) (x u : ρ.M) :
    ρ.CrossKeep (K ∪ {ρ.crossingOf x}) u ↔ ρ.CrossKeep K u ∨ (u = x ∨ u = ρ.pair x) := by
  unfold Record.CrossKeep
  rw [Set.mem_union, Set.mem_singleton_iff, w3di_crossingOf_eq_iff]

include D pd sl in
/-- **the four arc conditions of the two `A`-components, as the retained sets of the outer carriers**:
(X) `β₁ → β₂` inside `A` is `owner_S β₂`; (Yγ) `β₂ → β₁` inside `A` is `owner_S γ₂` plus the chord of `γ`;
(Y) `γ₁ → γ₂` inside `A` is `owner_S γ₂`; (Xβ) `γ₂ → γ₁` inside `A` is `owner_S β₂` plus the chord of `β`. -/
theorem w3di_arcs_ident (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) :
    (((r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v u ∧
        r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v ((geoPositiveLift hn hG hQ q₀).record.pair u)) ∧
      ((geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.b₁ u sl.b₂ ∧
        (geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.b₁ ((geoPositiveLift hn hG hQ q₀).record.pair u) sl.b₂)) ↔
      (liftVisit hn hG hQ q₀ u).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) ∧
    (((r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v u ∧
        r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v ((geoPositiveLift hn hG hQ q₀).record.pair u)) ∧
      ((geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.b₂ u sl.b₁ ∧
        (geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.b₂ ((geoPositiveLift hn hG hQ q₀).record.pair u) sl.b₁)) ↔
      (geoPositiveLift hn hG hQ q₀).record.CrossKeep
        (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) ∪
          {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.c₂}) u) ∧
    (((r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v u ∧
        r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v ((geoPositiveLift hn hG hQ q₀).record.pair u)) ∧
      ((geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.c₁ u sl.c₂ ∧
        (geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.c₁ ((geoPositiveLift hn hG hQ q₀).record.pair u) sl.c₂)) ↔
      (liftVisit hn hG hQ q₀ u).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) ∧
    (((r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v u ∧
        r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v ((geoPositiveLift hn hG hQ q₀).record.pair u)) ∧
      ((geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.c₂ u sl.c₁ ∧
        (geoPositiveLift hn hG hQ q₀).record.ArcBetween sl.c₂ ((geoPositiveLift hn hG hQ q₀).record.pair u) sl.c₁)) ↔
      (geoPositiveLift hn hG hQ q₀).record.CrossKeep
        (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) ∪
          {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.b₂}) u) := by
  have hN := CV.markList_length_pos hG.cg q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  obtain ⟨i, i', hi, hi', hu, hu', hS1, hS2, hOα1, hOα2, hOβ1, hOβ2, hOγ1, hOγ2, tw0, tw1, twp, twp1, twr, twr1⟩ :=
    w3di_occ_idx hn hG hQ D pd u
  obtain ⟨hA, -, hβ, hβ', hγ, hγ'⟩ := w3di_arcs_idx hn hG hQ D pd sl u hi hu
  obtain ⟨hA', -, hβt, hβ't, hγt, hγ't⟩ := w3di_arcs_idx hn hG hQ D pd sl _ hi' hu'
  obtain ⟨-, -, -, hp, hp1', hr⟩ := w3di_six_idx hn hG hQ D pd sl
  have hpair : (geoPositiveLift hn hG hQ q₀).record.pair u = (geoPositiveLift hn hG hQ q₀).twin u := rfl
  have hc₂t : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin sl.c₂) = γ₁ := by
    rw [liftVisit_twin, sl.hc₂, D.tγ']
  have hb₂t : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin sl.b₂) = β₁ := by
    rw [liftVisit_twin, sl.hb₂, D.tβ']
  have hp1c : (geoSmoothingSuccessor hG.cg Q ^ (pd.p + 1)) (Sum.inr α₁) =
      Sum.inr (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin sl.c₂)) := by rw [hc₂t, pd.ep1]
  have h1b : (geoSmoothingSuccessor hG.cg Q ^ 1) (Sum.inr α₁) =
      Sum.inr (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin sl.b₂)) := by rw [hb₂t, pd.e1]
  have euc₂ := w3di_eq_iff_idx hn hG hQ D u sl.c₂ hi (by omega) hu hr
  have euc₂' := w3di_eq_iff_idx hn hG hQ D u _ hi (by omega) hu hp1c
  have eub₂ := w3di_eq_iff_idx hn hG hQ D u sl.b₂ hi (by omega) hu hp
  have eub₂' := w3di_eq_iff_idx hn hG hQ D u _ hi (by omega) hu h1b
  have hgγ : (geoPositiveLift hn hG hQ q₀).record.CrossKeep
      (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂)))) u ↔
      (liftVisit hn hG hQ q₀ u).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂)) :=
    crossKeep_liftBlock_iff hn hG hQ q₀ _ u
  have hgβ : (geoPositiveLift hn hG hQ q₀).record.CrossKeep
      (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂)))) u ↔
      (liftVisit hn hG hQ q₀ u).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂)) :=
    crossKeep_liftBlock_iff hn hG hQ q₀ _ u
  have hpc : (geoPositiveLift hn hG hQ q₀).record.pair sl.c₂ = (geoPositiveLift hn hG hQ q₀).twin sl.c₂ := rfl
  have hpb : (geoPositiveLift hn hG hQ q₀).record.pair sl.b₂ = (geoPositiveLift hn hG hQ q₀).twin sl.b₂ := rfl
  rw [hpair, w3di_crossKeep_union_iff, w3di_crossKeep_union_iff, hpc, hpb, hgγ, hgβ, w3di_mem_gCC_iff,
    w3di_mem_gCC_iff, hA, hA', hβ, hβ', hβt, hβ't, hγ, hγ', hγt, hγ't, hOβ1, hOβ2, hOγ1, hOγ2, hS1,
    euc₂, euc₂', eub₂, eub₂']
  have hSS : (i = 0 ∨ i = 1 ∨ i = pd.p ∨ i = pd.p + 1 ∨ i = pd.r ∨ i = pd.r + 1) ↔
      (i' = 0 ∨ i' = 1 ∨ i' = pd.p ∨ i' = pd.p + 1 ∨ i' = pd.r ∨ i' = pd.r + 1) := hS1.symm.trans hS2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

include D pd sl in
/-- the four visits of `β`, `γ` lie on the arc `A = (α₁ → α₂)` -/
theorem w3di_arcA_of_βγ (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit)
    (h : liftVisit hn hG hQ q₀ u = β₁ ∨ liftVisit hn hG hQ q₀ u = β₂ ∨
      liftVisit hn hG hQ q₀ u = γ₁ ∨ liftVisit hn hG hQ q₀ u = γ₂) :
    r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v u := by
  have hN := CV.markList_length_pos hG.cg q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  obtain ⟨i, hi, hu⟩ := w3di_lift_idx hn hG hQ D u
  obtain ⟨hA, -, -, -, -, -⟩ := w3di_arcs_idx hn hG hQ D pd sl u hi hu
  rw [hA]
  have inj := fun {l : ℕ} (hl : l < (geoComponentMarkList hG.cg Q q₀).length)
    (h : (geoSmoothingSuccessor hG.cg Q ^ l) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ u)) =>
    w3di_pow_inj hG.cg hQ D hi hl (hu.trans h.symm)
  rcases h with h | h | h | h
  · have := inj (l := 1) (by omega) (by rw [pd.e1, h]); omega
  · have := inj (l := pd.p) (by omega) (by rw [pd.ep, h]); omega
  · have := inj (l := pd.p + 1) (by omega) (by rw [pd.ep1, h]); omega
  · have := inj (l := pd.r) (by omega) (by rw [pd.er, h]); omega

include D pd sl in
/-- **the kinks**: in `ρ|(block of owner_S γ₂ ∪ {chord γ})` the successor of `c₂` is `c₁`; in
`ρ|(block of owner_S β₂ ∪ {chord β})` the successor of `b₂` is `b₁`. -/
theorem w3di_kinks :
    (∃ hc : (geoPositiveLift hn hG hQ q₀).record.CrossKeep
        (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) ∪
          {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.c₂}) sl.c₂,
      (((geoPositiveLift hn hG hQ q₀).record.restrictCrossings
        (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) ∪
          {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.c₂})).succ ⟨sl.c₂, hc⟩).1 =
        (geoPositiveLift hn hG hQ q₀).record.pair sl.c₂) ∧
    (∃ hb : (geoPositiveLift hn hG hQ q₀).record.CrossKeep
        (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) ∪
          {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.b₂}) sl.b₂,
      (((geoPositiveLift hn hG hQ q₀).record.restrictCrossings
        (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) ∪
          {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.b₂})).succ ⟨sl.b₂, hb⟩).1 =
        (geoPositiveLift hn hG hQ q₀).record.pair sl.b₂) := by
  have hN := CV.markList_length_pos hG.cg q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  have h1 : (geoPositiveLift hn hG hQ q₀).record.componentCount = 1 :=
    CV.record_componentCount_one _ (geoPositiveLift_componentCount hn hG hQ q₀)
  obtain ⟨-, -, h1b, hp, hp1', hr⟩ := w3di_six_idx hn hG hQ D pd sl
  -- a generic kink argument
  have key : ∀ (K : Set (geoPositiveLift hn hG hQ q₀).record.Crossing)
      (x : (geoPositiveLift hn hG hQ q₀).Γ.Visit) {l l' : ℕ}
      (hl : l < (geoComponentMarkList hG.cg Q q₀).length) (hl' : l' < (geoComponentMarkList hG.cg Q q₀).length)
      (hx : (geoSmoothingSuccessor hG.cg Q ^ l) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ x))
      (hx' : (geoSmoothingSuccessor hG.cg Q ^ l') (Sum.inr α₁) =
        Sum.inr (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin x)))
      (hxK : (geoPositiveLift hn hG hQ q₀).record.CrossKeep K x)
      (hbound : ∀ s : (geoPositiveLift hn hG hQ q₀).Γ.Visit, (geoPositiveLift hn hG hQ q₀).record.CrossKeep K s →
        ∀ {j : ℕ}, j < (geoComponentMarkList hG.cg Q q₀).length →
        (geoSmoothingSuccessor hG.cg Q ^ j) (Sum.inr α₁) = Sum.inr (liftVisit hn hG hQ q₀ s) →
        ¬ ((l < j ∧ j < l') ∨ (j < l' ∧ l' < l) ∨ (l' < l ∧ l < j))),
      (((geoPositiveLift hn hG hQ q₀).record.restrictCrossings K).succ ⟨x, hxK⟩).1 =
        (geoPositiveLift hn hG hQ q₀).record.pair x := by
    intro K x l l' hl hl' hx hx' hxK hbound
    have hpK : (geoPositiveLift hn hG hQ q₀).record.CrossKeep K ((geoPositiveLift hn hG hQ q₀).record.pair x) :=
      ((geoPositiveLift hn hG hQ q₀).record.crossKeep_pair_iff K x).mpr hxK
    have hpne : (geoPositiveLift hn hG hQ q₀).record.pair x ≠ x := (geoPositiveLift hn hG hQ q₀).record.pair_ne x
    have hsK := (((geoPositiveLift hn hG hQ q₀).record.restrictCrossings K).succ ⟨x, hxK⟩).2
    have hsne : (((geoPositiveLift hn hG hQ q₀).record.restrictCrossings K).succ ⟨x, hxK⟩).1 ≠ x :=
      (geoPositiveLift hn hG hQ q₀).record.firstReturn_val_ne _ h1 ⟨x, hxK⟩ hpK hpne
    by_contra hne
    rcases (geoPositiveLift hn hG hQ q₀).record.arcBetween_or_arcBetween h1 (Ne.symm hsne) hpne.symm hne
      with harc | harc
    · obtain ⟨j, hj, hs⟩ := w3di_lift_idx hn hG hQ D
        (((geoPositiveLift hn hG hQ q₀).record.restrictCrossings K).succ ⟨x, hxK⟩).1
      have hpx : (geoPositiveLift hn hG hQ q₀).record.pair x = (geoPositiveLift hn hG hQ q₀).twin x := rfl
      rw [hpx, w3di_arc_idx hn hG hQ D x _ ((geoPositiveLift hn hG hQ q₀).twin x) hl hj hl' hx hs hx'] at harc
      exact hbound _ hsK hj hs harc
    · exact (geoPositiveLift hn hG hQ q₀).record.not_arcBetween_firstReturn _ h1 ⟨x, hxK⟩ hpK harc
  have hc₂t : (geoSmoothingSuccessor hG.cg Q ^ (pd.p + 1)) (Sum.inr α₁) =
      Sum.inr (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin sl.c₂)) := by
    rw [liftVisit_twin, sl.hc₂, D.tγ', pd.ep1]
  have hb₂t : (geoSmoothingSuccessor hG.cg Q ^ 1) (Sum.inr α₁) =
      Sum.inr (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin sl.b₂)) := by
    rw [liftVisit_twin, sl.hb₂, D.tβ', pd.e1]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · refine key _ sl.c₂ (by omega) (by omega) hr hc₂t _ ?_
    intro s hsK j hj hs
    have := ((w3di_arcs_ident hn hG hQ D pd sl s).2.1).mpr hsK
    obtain ⟨hA, -, -, hβ', -, -⟩ := w3di_arcs_idx hn hG hQ D pd sl s hj hs
    rw [hA, hβ'] at this
    omega
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · refine key _ sl.b₂ (by omega) (by omega) hp hb₂t _ ?_
    intro s hsK j hj hs
    have := ((w3di_arcs_ident hn hG hQ D pd sl s).2.2.2).mpr hsK
    obtain ⟨hA, -, -, -, -, hγ'⟩ := w3di_arcs_idx hn hG hQ D pd sl s hj hs
    rw [hA, hγ'] at this
    omega

end W3DI_Lift



/-! ### A. `2Λ` of an all-positive diagram is the number of its mixed crossings -/

section W3DI_Lambda

/-- the double sum over an ordered pair `(i < j)` picking the unordered pair `{a, b}` -/
theorem w3di_pair_sum {c : ℕ} (a b : Fin c) :
    (∑ i : Fin c, ∑ j : Fin c,
      if (i < j ∧ ((a = i ∧ b = j) ∨ (a = j ∧ b = i))) then (1 : ℤ) else 0) =
      if a ≠ b then 1 else 0 := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [ite_eq_left (ne_of_lt hab), Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · rw [ite_eq_left ⟨hab, Or.inl ⟨rfl, rfl⟩⟩]
      · intro j _ hj
        rw [ite_eq_right]
        rintro ⟨hij, (⟨-, rfl⟩ | ⟨rfl, -⟩)⟩
        · exact hj rfl
        · exact lt_irrefl _ hij
      · intro h; exact absurd (Finset.mem_univ b) h
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      rw [ite_eq_right]
      rintro ⟨hij, (⟨rfl, -⟩ | ⟨rfl, rfl⟩)⟩
      · exact hi rfl
      · exact absurd hab (not_lt.mpr hij.le)
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [ite_eq_right (fun h => h rfl)]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right]
    rintro ⟨hij, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact lt_irrefl _ hij
    · exact lt_irrefl _ hij
  · rw [ite_eq_left (ne_of_gt hba), Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single a]
      · rw [ite_eq_left ⟨hba, Or.inr ⟨rfl, rfl⟩⟩]
      · intro j _ hj
        rw [ite_eq_right]
        rintro ⟨hij, (⟨hab', -⟩ | ⟨haj, -⟩)⟩
        · exact ne_of_gt hba hab'
        · exact hj haj.symm
      · intro h; exact absurd (Finset.mem_univ a) h
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      rw [ite_eq_right]
      rintro ⟨hij, (⟨hai, hbj⟩ | ⟨-, hbi⟩)⟩
      · rw [← hai, ← hbj] at hij
        exact absurd hba (not_lt.mpr hij.le)
      · exact hi hbi.symm
    · intro h; exact absurd (Finset.mem_univ b) h

/-- **`2Λ` on an all-positive diagram is the number of mixed crossings** (`r176l_mixedSignSum_eq_card`
summed over the unordered pairs of components). -/
theorem w3di_twoLambda_eq_card (D : Diagram) (hpos : ∀ x : D.Γ.Crossing, D.sign x = 1) :
    twoLambda D = ((Finset.univ.filter
      (fun x : D.Γ.Crossing => (D.overStrand x).1 ≠ (D.underStrand x).1)).card : ℤ) := by
  classical
  have h1 : ∀ i j : Fin D.Γ.c, (if i < j then twoLinking D i j else 0) =
      ∑ x : D.Γ.Crossing, if (i < j ∧ r176l_IsMixed D i j x) then (1 : ℤ) else 0 := by
    intro i j
    by_cases hij : i < j
    · rw [ite_eq_left hij]
      unfold twoLinking
      rw [r176l_mixedSignSum_eq_card D i j (ne_of_lt hij) hpos, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h : r176l_IsMixed D i j x
      · rw [ite_eq_left h, ite_eq_left ⟨hij, h⟩]; rfl
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.2)]; rfl
    · rw [ite_eq_right hij]
      symm
      apply Finset.sum_eq_zero
      intro x _
      rw [ite_eq_right (fun h => hij h.1)]
  unfold twoLambda
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1 i j))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have e : ∀ i j : Fin D.Γ.c, (if (i < j ∧ r176l_IsMixed D i j x) then (1 : ℤ) else 0) =
      if (i < j ∧ (((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
        ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i))) then (1 : ℤ) else 0 := by
    intro i j
    unfold r176l_IsMixed
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => e i j)), w3di_pair_sum]
  split_ifs <;> simp



end W3DI_Lambda


/-! ### B. The identification at the record level: from the two record clauses to `w3ck_IdentData` -/

section W3DI_Assembly
variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {Q S : Finset (Crossing P)} (hQ : GeoIndependent hG.cg Q) (hS : GeoIndependent hG.cg S)
  {q₀ : GeoComponent hG.cg Q} {α₁ α₂ β₁ β₂ γ₁ γ₂ : Visit P}
  (D : w3di_WordData hG.cg Q S q₀ α₁ α₂ β₁ β₂ γ₁ γ₂)
  (pd : w3di_PosData hG.cg Q q₀ α₁ α₂ β₁ β₂ γ₁ γ₂)

/-- the parent crossing of an occurrence of the lift is read off its double point -/
theorem w3di_liftVisit_fst_of_point (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) (c : Crossing P)
    (hc : (geoPositiveLift hn hG hQ q₀).Γ.crossingPoint u.1 = crossingPoint c) :
    (liftVisit hn hG hQ q₀ u).1 = c := by
  rw [liftVisit_fst]
  apply crossingPoint_injective_of_geometry hG.cg
  rw [crossingPoint_liftCrossing, hc]

open scoped Classical in
theorem w3di_mem_mixedSet (hP : CrossingGeometry P) (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S')
    (x : Crossing P) :
    x ∈ w3cb_mixedSet hP S' Sf q' ↔ x ∈ geoCarrierCrossings hP S' q' ∧ x ∉ Sf ∧
      ∃ v w : Visit P, v.1 = x ∧ w.1 = x ∧ geoOwner hP Sf (Sum.inr v) ≠ geoOwner hP Sf (Sum.inr w) := by
  unfold w3cb_mixedSet
  rw [Finset.mem_filter]

include D pd in
/-- every retained visit of `q₀` off `S` is owned by one of the three outer carriers -/
theorem w3di_owner_cover (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) (hu : (liftVisit hn hG hQ q₀ u).1 ∉ S) :
    geoOwner hG.cg S (Sum.inr (liftVisit hn hG hQ q₀ u)) = geoOwner hG.cg S (Sum.inr α₁) ∨
    geoOwner hG.cg S (Sum.inr (liftVisit hn hG hQ q₀ u)) = geoOwner hG.cg S (Sum.inr β₂) ∨
    geoOwner hG.cg S (Sum.inr (liftVisit hn hG hQ q₀ u)) = geoOwner hG.cg S (Sum.inr γ₂) := by
  have hN := CV.markList_length_pos hG.cg q₀
  have hp1 := pd.hp1
  have hpr := pd.hpr
  have hrN := pd.hrN
  obtain ⟨i, i', hi, hi', hu', hu'', hS1, hS2, hOα1, hOα2, hOβ1, hOβ2, hOγ1, hOγ2, -⟩ :=
    w3di_occ_idx hn hG hQ D pd u
  rw [hS1] at hu
  rw [hOα1, hOβ1, hOγ1]
  omega

include D pd in
/-- for a retained crossing off `S`: its two visits have the same `S`-owner iff it is a retained
crossing of one of the three outer carriers -/
theorem w3di_owner_eq_iff (u : (geoPositiveLift hn hG hQ q₀).Γ.Visit) (hu : (liftVisit hn hG hQ q₀ u).1 ∉ S) :
    geoOwner hG.cg S (Sum.inr (liftVisit hn hG hQ q₀ u)) =
        geoOwner hG.cg S (Sum.inr (visitTwin (liftVisit hn hG hQ q₀ u))) ↔
      (liftVisit hn hG hQ q₀ u).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr α₁)) ∨
      (liftVisit hn hG hQ q₀ u).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂)) ∨
      (liftVisit hn hG hQ q₀ u).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂)) := by
  rw [w3di_mem_gCC_iff, w3di_mem_gCC_iff, w3di_mem_gCC_iff]
  constructor
  · intro h
    rcases w3di_owner_cover hn hG hQ D pd u hu with h1 | h1 | h1
    · exact Or.inl ⟨hu, h1, h.symm.trans h1⟩
    · exact Or.inr (Or.inl ⟨hu, h1, h.symm.trans h1⟩)
    · exact Or.inr (Or.inr ⟨hu, h1, h.symm.trans h1⟩)
  · rintro (⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩) <;> exact h1.trans h2.symm

/-- the cover of the components of a three-component record by three distinct ones -/
theorem w3di_comps_cover (τ : Record) (h3 : τ.componentCount = 3) (κB κ₁ κ₂ : τ.comps)
    (neB1 : κB ≠ κ₁) (neB2 : κB ≠ κ₂) (ne12 : κ₁ ≠ κ₂) (κ : τ.comps) : κ = κB ∨ κ = κ₁ ∨ κ = κ₂ := by
  classical
  have hcard : ({κB, κ₁, κ₂} : Finset τ.comps).card = Fintype.card τ.comps := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair ne12]
    · exact h3.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨neB1, neB2⟩
  have := Finset.eq_univ_of_card _ hcard
  have hκ : κ ∈ ({κB, κ₁, κ₂} : Finset τ.comps) := by rw [this]; exact Finset.mem_univ _
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hκ

/-- a self crossing of a three-component record is internal to one of the three components -/
theorem w3di_isSelfCrossing_iff_restrictKeep (τ : Record) (h3 : τ.componentCount = 3) (κB κ₁ κ₂ : τ.comps)
    (neB1 : κB ≠ κ₁) (neB2 : κB ≠ κ₂) (ne12 : κ₁ ≠ κ₂) (m : τ.M) :
    τ.IsSelfCrossing m ↔ τ.RestrictKeep {κB} m ∨ τ.RestrictKeep {κ₁} m ∨ τ.RestrictKeep {κ₂} m := by
  unfold Record.IsSelfCrossing Record.RestrictKeep
  simp only [Finset.mem_singleton]
  constructor
  · intro h
    rcases w3di_comps_cover τ h3 κB κ₁ κ₂ neB1 neB2 ne12 (τ.comp m) with e | e | e
    · exact Or.inl ⟨e, h.symm.trans e⟩
    · exact Or.inr (Or.inl ⟨e, h.symm.trans e⟩)
    · exact Or.inr (Or.inr ⟨e, h.symm.trans e⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact h1.trans h2.symm

/-- the three-element bijection with prescribed values -/
theorem w3di_exists_equiv_fin3 {c : ℕ} (hc : c = 3) (i₀ i₁ i₂ : Fin c) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂)
    (h12 : i₁ ≠ i₂) : ∃ σ : Fin 3 ≃ Fin c, σ 0 = i₀ ∧ σ 1 = i₁ ∧ σ 2 = i₂ := by
  subst hc
  let f : Fin 3 → Fin 3 := ![i₀, i₁, i₂]
  have hinj : Function.Injective f := by
    intro a b hab
    match a, b with
    | 0, 0 => rfl
    | 0, 1 => exact absurd hab h01
    | 0, 2 => exact absurd hab h02
    | 1, 0 => exact absurd hab.symm h01
    | 1, 1 => rfl
    | 1, 2 => exact absurd hab h12
    | 2, 0 => exact absurd hab.symm h02
    | 2, 1 => exact absurd hab.symm h12
    | 2, 2 => rfl
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩), rfl, rfl, rfl⟩

/-! #### The generic core: from the components and their identified crossing sets to the count and the
three polynomials -/

include D pd in
/-- **`2Λ(J_L)` is the number of mixed retained crossings of the contact carrier**: the mixed crossings of
`J_L` are the chords of the lift whose two occurrences lie on different components, i.e. the retained
crossings of `q₀` off `S` whose two visits have different `S`-owners. -/
theorem w3di_count (v : (geoPositiveLift hn hG hQ q₀).Γ.Visit) (hv : liftVisit hn hG hQ q₀ v = α₁)
    (D_L0 : Diagram) (ι₀ : RecordIso D_L0.record ((geoPositiveLift hn hG hQ q₀).record.smooth v))
    (y : D_L0.Γ.Crossing) (J_L : Diagram)
    (ι₁ : RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y)))
    (o₂ : (geoPositiveLift hn hG hQ q₀).Γ.Visit)
    (hwo : ((liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 = β₁.1 ∧ (liftVisit hn hG hQ q₀ o₂).1 = γ₁.1) ∨
      ((liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 = γ₁.1 ∧ (liftVisit hn hG hQ q₀ o₂).1 = β₁.1))
    (κB κ₁ κ₂ : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).comps)
    (neB1 : κB ≠ κ₁) (neB2 : κB ≠ κ₂) (ne12 : κ₁ ≠ κ₂)
    (count3 : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).componentCount = 3)
    (K₁ K₂ : Set (geoPositiveLift hn hG hQ q₀).record.Crossing)
    (rkB : ∀ m, (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).RestrictKeep {κB} m ↔
      (geoPositiveLift hn hG hQ q₀).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hQ q₀).record v) m.1.1)
    (rk₁ : ∀ m, (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).RestrictKeep {κ₁} m ↔
      (geoPositiveLift hn hG hQ q₀).record.CrossKeep K₁ m.1.1)
    (rk₂ : ∀ m, (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).RestrictKeep {κ₂} m ↔
      (geoPositiveLift hn hG hQ q₀).record.CrossKeep K₂ m.1.1)
    (X Y : GeoComponent hG.cg S)
    (hXY : (X = geoOwner hG.cg S (Sum.inr β₂) ∧ Y = geoOwner hG.cg S (Sum.inr γ₂)) ∨
      (X = geoOwner hG.cg S (Sum.inr γ₂) ∧ Y = geoOwner hG.cg S (Sum.inr β₂)))
    (hKB : r176s_KB (geoPositiveLift hn hG hQ q₀).record v =
      liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr α₁))))
    (hK₁ : K₁ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S X))
    (hK₂ : K₂ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S Y) ∪
      {(geoPositiveLift hn hG hQ q₀).record.crossingOf o₂}) :
    twoLambda J_L = ((w3cb_mixedSet hG.cg Q S q₀).card : ℤ) := by
  classical
  have hpos : ∀ x : J_L.Γ.Crossing, J_L.sign x = 1 := by
    intro x
    have e := (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).sgn_eq (J_L.overVisit x)
    rw [Diagram.record_sgn, Diagram.overVisit_fst] at e
    have e2 : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).sgn
        ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ (J_L.overVisit x)) =
        (geoPositiveLift hn hG hQ q₀).record.sgn
          ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ (J_L.overVisit x)).1.1 := rfl
    rw [← e, e2, Diagram.record_sgn]
    exact geoPositiveLift_sign hn hG hQ q₀ _
  rw [w3di_twoLambda_eq_card J_L hpos, Nat.cast_inj]
  -- the retained chords of the double smoothing avoid the two smoothed crossings
  have hwS : (liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 ∈ S := by
    rcases hwo with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact w3di_β₁S hG.cg D
    · rw [h]; exact w3di_γ₁S hG.cg D
  have ho₂S : (liftVisit hn hG hQ q₀ o₂).1 ∈ S := by
    rcases hwo with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h]; exact w3di_γ₁S hG.cg D
    · rw [h]; exact w3di_β₁S hG.cg D
  have hvt : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin v) = α₂ := by
    rw [liftVisit_twin, hv, D.tα]
  -- an occurrence of the double smoothing, read in the lift: its label is not `α` and not the second crossing
  have hret : ∀ m : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).M,
      (liftVisit hn hG hQ q₀ m.1.1).1 ≠ α₁.1 ∧
      (liftVisit hn hG hQ q₀ m.1.1).1 ≠ (liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 := by
    intro m
    have h1 := ((geoPositiveLift hn hG hQ q₀).record.smoothKeep_iff v m.1.1).mp m.1.2
    have h2 := (((geoPositiveLift hn hG hQ q₀).record.smooth v).smoothKeep_iff _ m.1).mp m.2
    constructor
    · intro h
      rcases visit_eq_or_twin α₁ _ h with e | e
      · exact h1.1 (liftVisit_injective hn hG hQ q₀ (e.trans hv.symm))
      · rw [D.tα, ← hvt] at e
        exact h1.2 (liftVisit_injective hn hG hQ q₀ e)
    · intro h
      rcases visit_eq_or_twin _ _ h with e | e
      · exact h2.1 (Subtype.ext (liftVisit_injective hn hG hQ q₀ e))
      · rw [← liftVisit_twin] at e
        exact h2.2 (Subtype.ext (liftVisit_injective hn hG hQ q₀ e))
  -- self ↔ owners agree, for an occurrence off `S`; self, for an occurrence at the third crossing
  have hself : ∀ m : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).M,
      (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).IsSelfCrossing m ↔
        ((geoPositiveLift hn hG hQ q₀).record.CrossKeep
          (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr α₁)))) m.1.1 ∨
        (geoPositiveLift hn hG hQ q₀).record.CrossKeep (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S X)) m.1.1 ∨
        ((geoPositiveLift hn hG hQ q₀).record.CrossKeep (liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S Y)) m.1.1 ∨
          (m.1.1 = o₂ ∨ m.1.1 = (geoPositiveLift hn hG hQ q₀).record.pair o₂))) := by
    intro m
    rw [w3di_isSelfCrossing_iff_restrictKeep _ count3 κB κ₁ κ₂ neB1 neB2 ne12 m, rkB, rk₁, rk₂, hKB, hK₁, hK₂,
      w3di_crossKeep_union_iff]
  have hmixed : ∀ m : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).M,
      ¬ (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).IsSelfCrossing m ↔
        ((liftVisit hn hG hQ q₀ m.1.1).1 ∉ S ∧
          geoOwner hG.cg S (Sum.inr (liftVisit hn hG hQ q₀ m.1.1)) ≠
            geoOwner hG.cg S (Sum.inr (visitTwin (liftVisit hn hG hQ q₀ m.1.1)))) := by
    intro m
    rw [hself, crossKeep_liftBlock_iff, crossKeep_liftBlock_iff, crossKeep_liftBlock_iff]
    obtain ⟨hα, hw⟩ := hret m
    by_cases hmS : (liftVisit hn hG hQ q₀ m.1.1).1 ∈ S
    · -- at the third crossing: the chord is the kink, hence self
      have hm3 : (liftVisit hn hG hQ q₀ m.1.1).1 = (liftVisit hn hG hQ q₀ o₂).1 := by
        rcases (D.hSeq _).mp hmS with h | h | h | h
        · exact absurd h (w3di_lift_notQ hn hG hQ m.1.1)
        · exact absurd h hα
        · rcases hwo with ⟨h', -⟩ | ⟨-, h'⟩
          · exact absurd (h.trans h'.symm) hw
          · exact h.trans h'.symm
        · rcases hwo with ⟨-, h'⟩ | ⟨h', -⟩
          · exact h.trans h'.symm
          · exact absurd (h.trans h'.symm) hw
      have huo : m.1.1 = o₂ ∨ m.1.1 = (geoPositiveLift hn hG hQ q₀).record.pair o₂ := by
        rcases visit_eq_or_twin _ _ hm3 with e | e
        · exact Or.inl (liftVisit_injective hn hG hQ q₀ e)
        · rw [← liftVisit_twin] at e
          exact Or.inr (liftVisit_injective hn hG hQ q₀ e)
      constructor
      · intro h; exact absurd (Or.inr (Or.inr (Or.inr huo))) h
      · intro h; exact absurd hmS h.1
    · -- off `S`: the third alternative's kink cases are impossible, the rest is the owner criterion
      have hno : ¬ (m.1.1 = o₂ ∨ m.1.1 = (geoPositiveLift hn hG hQ q₀).record.pair o₂) := by
        rintro (h | h)
        · apply hmS; rw [h]; exact ho₂S
        · apply hmS
          rw [h]
          change (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin o₂)).1 ∈ S
          rw [liftVisit_twin, visitTwin_crossing]; exact ho₂S
      have key := w3di_owner_eq_iff hn hG hQ D pd m.1.1 hmS
      constructor
      · intro h
        refine ⟨hmS, fun heq => h ?_⟩
        rcases key.mp heq with h1 | h1 | h1
        · exact Or.inl h1
        · rcases hXY with ⟨rfl, -⟩ | ⟨-, rfl⟩
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl h1))
        · rcases hXY with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact Or.inr (Or.inr (Or.inl h1))
          · exact Or.inr (Or.inl h1)
      · rintro ⟨-, hne⟩ h
        apply hne
        apply key.mpr
        rcases h with h1 | h1 | h1 | h1
        · exact Or.inl h1
        · rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr h1)
        · rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact Or.inr (Or.inr h1)
          · exact Or.inr (Or.inl h1)
        · exact absurd h1 hno
  -- the mixed crossings of `J_L`, read on the lift
  have hF1 : ∀ x : J_L.Γ.Crossing, ((J_L.overStrand x).1 ≠ (J_L.underStrand x).1 ↔
      ¬ (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).IsSelfCrossing
        ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ (J_L.overVisit x))) := by
    intro x
    rw [(ι₁.trans (ι₀.smooth (D_L0.overVisit y))).isSelfCrossing_iff]
    unfold Record.IsSelfCrossing
    rw [Diagram.record_comp, Diagram.record_comp, Diagram.record_pair_apply, Diagram.twin_overVisit]
    exact Iff.rfl
  refine Finset.card_bij
    (fun x _ => (liftVisit hn hG hQ q₀ ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ (J_L.overVisit x)).1.1).1)
    ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [w3di_mem_mixedSet]
    obtain ⟨hnS, hne⟩ := (hmixed _).mp ((hF1 x).mp hx.2)
    exact ⟨liftVisit_mem hn hG hQ q₀ _, hnS, _, _, rfl, visitTwin_crossing _, hne⟩
  · intro x hx x' hx' heq
    rcases visit_eq_or_twin _ _ heq.symm with e | e
    · have e1 := liftVisit_injective hn hG hQ q₀ e
      have e2 : (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ (J_L.overVisit x') =
          (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ (J_L.overVisit x) := Subtype.ext (Subtype.ext e1)
      have e3 := (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ.injective e2
      exact (congrArg Sigma.fst e3).symm
    · rw [← liftVisit_twin] at e
      have e1 := liftVisit_injective hn hG hQ q₀ e
      have e2 : (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ (J_L.overVisit x') =
          (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).pair
            ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ (J_L.overVisit x)) := Subtype.ext (Subtype.ext e1)
      rw [← (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).pair_eq] at e2
      have e3 := (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ.injective e2
      rw [Diagram.record_pair_apply, Diagram.twin_overVisit] at e3
      exact (congrArg Sigma.fst e3).symm
  · intro c hc
    rw [w3di_mem_mixedSet] at hc
    obtain ⟨hcQ, hcS, v₁, w₁, hv₁, hw₁, hne⟩ := hc
    obtain ⟨u₀, hu₀⟩ := liftVisit_surjective hn hG hQ q₀ (w := v₁) (by rw [hv₁]; exact hcQ)
    have hlab : (liftVisit hn hG hQ q₀ u₀).1 = c := by rw [hu₀, hv₁]
    have hk1 : (geoPositiveLift hn hG hQ q₀).record.SmoothKeep v u₀ := by
      rw [Record.smoothKeep_iff]
      constructor
      · rintro rfl
        apply hcS; rw [← hlab, hv]; exact w3di_α₁S hG.cg D
      · rintro rfl
        apply hcS
        rw [← hlab]
        change (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin v)).1 ∈ S
        rw [hvt, w3di_α12 hG.cg D]; exact w3di_α₁S hG.cg D
    have hk2 : ((geoPositiveLift hn hG hQ q₀).record.smooth v).SmoothKeep (ι₀.Φ (D_L0.overVisit y)) ⟨u₀, hk1⟩ := by
      refine (((geoPositiveLift hn hG hQ q₀).record.smooth v).smoothKeep_iff _ _).mpr ⟨?_, ?_⟩
      · intro h
        have h' : u₀ = (ι₀.Φ (D_L0.overVisit y)).1 := congrArg Subtype.val h
        apply hcS; rw [← hlab, h']; exact hwS
      · intro h
        have h' : u₀ = (geoPositiveLift hn hG hQ q₀).record.pair (ι₀.Φ (D_L0.overVisit y)).1 :=
          congrArg Subtype.val h
        apply hcS
        rw [← hlab, h']
        change (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin _)).1 ∈ S
        rw [liftVisit_twin, visitTwin_crossing]; exact hwS
    let m : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).M := ⟨⟨u₀, hk1⟩, hk2⟩
    refine ⟨((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ.symm m).1, ?_, ?_⟩
    · -- membership in the mixed filter
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (hF1 _).mpr ?_⟩
      have hw₁' : w₁ = visitTwin v₁ := by
        rcases visit_eq_or_twin v₁ w₁ (hw₁.trans hv₁.symm) with e | e
        · exact absurd (by rw [e]) hne
        · exact e
      have hcrit : ∀ m' : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).M,
          (liftVisit hn hG hQ q₀ m'.1.1).1 = c →
          ¬ (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).IsSelfCrossing m' := by
        intro m' hm'
        rw [hmixed]
        refine ⟨by rw [hm']; exact hcS, ?_⟩
        rcases visit_eq_or_twin v₁ _ (hm'.trans hv₁.symm) with e | e
        · rw [e, ← hw₁']; exact hne
        · have htt : visitTwin (visitTwin v₁) = v₁ := by
            rcases visit_eq_or_twin v₁ (visitTwin (visitTwin v₁)) (by rw [visitTwin_crossing, visitTwin_crossing])
              with e' | e'
            · exact e'
            · exact absurd e' (visitTwin_ne _)
          rw [e, htt, ← hw₁']
          exact hne.symm
      apply hcrit
      rcases J_L.eq_or_eq_twin ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ.symm m)
        (J_L.overVisit ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ.symm m).1) rfl with e | e
      · rw [e, Equiv.apply_symm_apply]; exact hlab
      · rw [e, ← Diagram.record_pair_apply, (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).pair_eq,
          Equiv.apply_symm_apply]
        change (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin u₀)).1 = c
        rw [liftVisit_twin, visitTwin_crossing, hlab]
    · -- the label
      rcases J_L.eq_or_eq_twin ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ.symm m)
        (J_L.overVisit ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).Φ.symm m).1) rfl with e | e
      · rw [e, Equiv.apply_symm_apply]; exact hlab
      · rw [e, ← Diagram.record_pair_apply, (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).pair_eq,
          Equiv.apply_symm_apply]
        change (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin u₀)).1 = c
        rw [liftVisit_twin, visitTwin_crossing, hlab]

include D pd in
/-- **The generic core**: the three components of `J_L` with their crossing sets identified give `2Λ(J_L)`
= `#mixedSet` and a numbering of the components with the HOMFLY polynomials of the lifts of the three outer
carriers (`r176s_homfly_of_liftBlock` for the two clean components, `r176c_homfly_of_liftBlock_curl` for
the component carrying the third triangle crossing as a kink). -/
theorem w3di_core (v : (geoPositiveLift hn hG hQ q₀).Γ.Visit) (hv : liftVisit hn hG hQ q₀ v = α₁)
    (D_L0 : Diagram) (ι₀ : RecordIso D_L0.record ((geoPositiveLift hn hG hQ q₀).record.smooth v))
    (y : D_L0.Γ.Crossing) (J_L : Diagram)
    (ι₁ : RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y)))
    (o₂ : (geoPositiveLift hn hG hQ q₀).Γ.Visit)
    (hwo : ((liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 = β₁.1 ∧ (liftVisit hn hG hQ q₀ o₂).1 = γ₁.1) ∨
      ((liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 = γ₁.1 ∧ (liftVisit hn hG hQ q₀ o₂).1 = β₁.1))
    (κB κ₁ κ₂ : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).comps)
    (neB1 : κB ≠ κ₁) (neB2 : κB ≠ κ₂) (ne12 : κ₁ ≠ κ₂)
    (count3 : (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).componentCount = 3)
    (K₁ K₂ : Set (geoPositiveLift hn hG hQ q₀).record.Crossing)
    (isoB : Nonempty (RecordIso ((((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).restrict {κB})
      ((geoPositiveLift hn hG hQ q₀).record.restrictCrossings (r176s_KB (geoPositiveLift hn hG hQ q₀).record v))))
    (iso₁ : Nonempty (RecordIso ((((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).restrict {κ₁})
      ((geoPositiveLift hn hG hQ q₀).record.restrictCrossings K₁)))
    (iso₂ : Nonempty (RecordIso ((((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).restrict {κ₂})
      ((geoPositiveLift hn hG hQ q₀).record.restrictCrossings K₂)))
    (rkB : ∀ m, (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).RestrictKeep {κB} m ↔
      (geoPositiveLift hn hG hQ q₀).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hQ q₀).record v) m.1.1)
    (rk₁ : ∀ m, (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).RestrictKeep {κ₁} m ↔
      (geoPositiveLift hn hG hQ q₀).record.CrossKeep K₁ m.1.1)
    (rk₂ : ∀ m, (((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).RestrictKeep {κ₂} m ↔
      (geoPositiveLift hn hG hQ q₀).record.CrossKeep K₂ m.1.1)
    (X Y : GeoComponent hG.cg S)
    (hXY : (X = geoOwner hG.cg S (Sum.inr β₂) ∧ Y = geoOwner hG.cg S (Sum.inr γ₂)) ∨
      (X = geoOwner hG.cg S (Sum.inr γ₂) ∧ Y = geoOwner hG.cg S (Sum.inr β₂)))
    (hKB : r176s_KB (geoPositiveLift hn hG hQ q₀).record v =
      liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr α₁))))
    (hK₁ : K₁ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S X))
    (hK₂ : K₂ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S Y) ∪
      {(geoPositiveLift hn hG hQ q₀).record.crossingOf o₂})
    (hno : (geoPositiveLift hn hG hQ q₀).record.crossingOf o₂ ∉
      liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S Y))
    (hkink : ∃ hc : (geoPositiveLift hn hG hQ q₀).record.CrossKeep K₂ o₂,
      (((geoPositiveLift hn hG hQ q₀).record.restrictCrossings K₂).succ ⟨o₂, hc⟩).1 =
        (geoPositiveLift hn hG hQ q₀).record.pair o₂) :
    twoLambda J_L = ((w3cb_mixedSet hG.cg Q S q₀).card : ℤ) ∧
    ∃ σ : Fin 3 ≃ Fin J_L.Γ.c,
      homfly (J_L.knotRestrict (σ 0)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr α₁))) ∧
      homfly (J_L.knotRestrict (σ 1)) = homfly (geoPositiveLift hn hG hS X) ∧
      homfly (J_L.knotRestrict (σ 2)) = homfly (geoPositiveLift hn hG hS Y) := by
  classical
  refine ⟨w3di_count hn hG hQ D pd v hv D_L0 ι₀ y J_L ι₁ o₂ hwo κB κ₁ κ₂ neB1 neB2 ne12 count3 K₁ K₂
    rkB rk₁ rk₂ X Y hXY hKB hK₁ hK₂, ?_⟩
  -- subsets
  have hsub : ∀ (Z : GeoComponent hG.cg S) (m₀ : Visit P), geoOwner hG.cg S (Sum.inr m₀) = Z →
      geoOwner hG.cg Q (Sum.inr m₀) = q₀ →
      geoCarrierCrossings hG.cg S Z ⊆ geoCarrierCrossings hG.cg Q q₀ := by
    intro Z m₀ hZ hq x hx
    rw [mem_geoCarrierCrossings] at hx ⊢
    refine ⟨fun h => hx.1 (w3di_QS hG.cg D h), fun w hw => ?_⟩
    have := geoOwner_eq_of_subset hG.cg hS (w3di_QS hG.cg D) (Sum.inr w) (Sum.inr m₀)
      ((hx.2 w hw).trans hZ.symm)
    exact this.trans hq
  obtain ⟨-, -, hβ₂, -, hγ₂⟩ := w3di_own_six hG.cg hS D
  have hsubα := hsub _ α₁ rfl D.hq₀
  have hsubβ := hsub _ β₂ rfl hβ₂
  have hsubγ := hsub _ γ₂ rfl hγ₂
  have hsubX : geoCarrierCrossings hG.cg S X ⊆ geoCarrierCrossings hG.cg Q q₀ := by
    rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hsubβ
    · exact hsubγ
  have hsubY : geoCarrierCrossings hG.cg S Y ⊆ geoCarrierCrossings hG.cg Q q₀ := by
    rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hsubγ
    · exact hsubβ
  -- the components of `J_L`
  have hJL3 : J_L.Γ.c = 3 := by
    have := (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).componentCount_eq
    rw [Diagram.record_componentCount] at this
    exact this.trans count3
  have hres : ∀ κ, Nonempty (RecordIso
      (J_L.knotRestrict ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm κ)).record
      ((((geoPositiveLift hn hG hQ q₀).record.smooth v).smooth (ι₀.Φ (D_L0.overVisit y))).restrict {κ})) := by
    intro κ
    refine ⟨(J_L.restrictRecordIso {(ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm κ}
      (Finset.singleton_nonempty _)).trans
      ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).restrict {(ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm κ} {κ} ?_)⟩
    intro c
    rw [Finset.mem_singleton, Finset.mem_singleton]
    exact (Equiv.eq_symm_apply (ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e).symm
  obtain ⟨χB⟩ := isoB
  obtain ⟨χ₁⟩ := iso₁
  obtain ⟨χ₂⟩ := iso₂
  obtain ⟨rB⟩ := hres κB
  obtain ⟨r₁⟩ := hres κ₁
  obtain ⟨r₂⟩ := hres κ₂
  have hB := r176s_homfly_of_liftBlock hn hG hQ hS q₀ _ hsubα _ _ hKB ⟨rB.trans χB⟩
  have hX := r176s_homfly_of_liftBlock hn hG hQ hS q₀ X hsubX _ K₁ hK₁ ⟨r₁.trans χ₁⟩
  have hY : homfly (J_L.knotRestrict ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm κ₂)) =
      homfly (geoPositiveLift hn hG hS Y) := by
    obtain ⟨hc, hk⟩ := hkink
    exact r176c_homfly_of_liftBlock_curl hn hG hQ hS q₀ Y hsubY _ K₂ _ hK₂ hno ⟨o₂, hc, rfl, hk⟩ ⟨r₂.trans χ₂⟩
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := w3di_exists_equiv_fin3 hJL3
    ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm κB)
    ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm κ₁)
    ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm κ₂)
    (fun h => neB1 ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm.injective h))
    (fun h => neB2 ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm.injective h))
    (fun h => ne12 ((ι₁.trans (ι₀.smooth (D_L0.overVisit y))).e.symm.injective h))
  exact ⟨σ, by rw [hσ0]; exact hB, by rw [hσ1]; exact hX, by rw [hσ2]; exact hY⟩

variable (sl : w3di_SixLift hn hG hQ q₀ α₁ β₁ β₂ γ₁ γ₂)

include D pd sl in
/-- **the case of the second smoothing at `β`**: `x ↦ α`, `y ↦ β`; the third component carries `γ` -/
theorem w3di_ident_β (D_L0 : Diagram)
    (ι₀ : RecordIso D_L0.record ((geoPositiveLift hn hG hQ q₀).record.smooth sl.v))
    (y : D_L0.Γ.Crossing) (J_L : Diagram)
    (ι₁ : RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y)))
    (hw : (liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 = β₁.1) :
    twoLambda J_L = ((w3cb_mixedSet hG.cg Q S q₀).card : ℤ) ∧
    ∃ σ : Fin 3 ≃ Fin J_L.Γ.c,
      homfly (J_L.knotRestrict (σ 0)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr α₁))) ∧
      homfly (J_L.knotRestrict (σ 1)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr β₂))) ∧
      homfly (J_L.knotRestrict (σ 2)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr γ₂))) := by
  have h1 : (geoPositiveLift hn hG hQ q₀).record.componentCount = 1 :=
    CV.record_componentCount_one _ (geoPositiveLift_componentCount hn hG hQ q₀)
  have hpair : ∀ u : (geoPositiveLift hn hG hQ q₀).Γ.Visit,
      (geoPositiveLift hn hG hQ q₀).record.pair u = (geoPositiveLift hn hG hQ q₀).twin u := fun _ => rfl
  have hwt : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin (ι₀.Φ (D_L0.overVisit y)).1) =
      visitTwin (liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1) := liftVisit_twin hn hG hQ q₀ _
  -- the sets of the identification
  have hKB : r176s_KB (geoPositiveLift hn hG hQ q₀).record sl.v =
      liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr α₁))) := by
    apply r176o_crossing_set_ext
    intro u
    rw [w3di_KB_iff hn hG hQ D pd sl.v sl.hv u, crossKeep_liftBlock_iff]
  have hno : (geoPositiveLift hn hG hQ q₀).record.crossingOf sl.c₂ ∉
      liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) := by
    intro h
    have h' : (liftVisit hn hG hQ q₀ sl.c₂).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂)) :=
      (crossKeep_liftBlock_iff hn hG hQ q₀ _ sl.c₂).mp h
    rw [sl.hc₂, mem_geoCarrierCrossings] at h'
    exact h'.1 (by rw [w3di_γ12 hG.cg D]; exact w3di_γ₁S hG.cg D)
  obtain ⟨hkγ, -⟩ := w3di_kinks hn hG hQ D pd sl
  have hwo : (liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 = β₁.1 ∧ (liftVisit hn hG hQ q₀ sl.c₂).1 = γ₁.1 :=
    ⟨hw, by rw [sl.hc₂]; exact w3di_γ12 hG.cg D⟩
  -- both ends of the chord of `y` lie on the arc `A`
  have hA : r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v (ι₀.Φ (D_L0.overVisit y)).1 := by
    apply w3di_arcA_of_βγ hn hG hQ D pd sl
    rcases visit_eq_or_twin β₁ _ hw with e | e
    · exact Or.inl e
    · rw [D.tβ] at e; exact Or.inr (Or.inl e)
  have hA' : r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v
      ((geoPositiveLift hn hG hQ q₀).record.pair (ι₀.Φ (D_L0.overVisit y)).1) := by
    apply w3di_arcA_of_βγ hn hG hQ D pd sl
    rw [hpair, hwt]
    rcases visit_eq_or_twin β₁ _ hw with e | e
    · rw [e, D.tβ]; exact Or.inr (Or.inl rfl)
    · rw [e, D.tβ, D.tβ']; exact Or.inl rfl
  obtain ⟨d⟩ := w3di_double_exists (geoPositiveLift hn hG hQ q₀).record h1 sl.v (ι₀.Φ (D_L0.overVisit y)) hA hA'
  rcases visit_eq_or_twin β₁ _ hw with e | e
  · -- `y ↦ β₁`: `K₁` is the block of `owner β₂`, `K₂` the block of `owner γ₂` with the kink `γ`
    have hwb : (ι₀.Φ (D_L0.overVisit y)).1 = sl.b₁ := liftVisit_injective hn hG hQ q₀ (e.trans sl.hb₁.symm)
    have hwb' : (geoPositiveLift hn hG hQ q₀).record.pair (ι₀.Φ (D_L0.overVisit y)).1 = sl.b₂ := by
      rw [hpair]
      apply liftVisit_injective hn hG hQ q₀
      rw [hwt, e, D.tβ, sl.hb₂]
    have hK₁ : d.K₁ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) := by
      apply r176o_crossing_set_ext
      intro u
      have := d.keep₁ u
      rw [hwb', hwb] at this
      rw [this, crossKeep_liftBlock_iff]
      exact (w3di_arcs_ident hn hG hQ D pd sl u).1
    have hK₂ : d.K₂ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) ∪
        {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.c₂} := by
      apply r176o_crossing_set_ext
      intro u
      have := d.keep₂ u
      rw [hwb', hwb] at this
      rw [this]
      exact (w3di_arcs_ident hn hG hQ D pd sl u).2.1
    rw [← hK₂] at hkγ
    exact w3di_core hn hG hQ hS D pd sl.v sl.hv D_L0 ι₀ y J_L ι₁ sl.c₂ (Or.inl hwo) d.κB d.κ₁ d.κ₂ d.ne_B1 d.ne_B2
      d.ne_12 d.count3 d.K₁ d.K₂ d.isoB d.iso₁ d.iso₂ d.rkB d.rk₁ d.rk₂ _ _ (Or.inl ⟨rfl, rfl⟩) hKB hK₁ hK₂ hno hkγ
  · -- `y ↦ β₂`: the roles of the two `A`-components are exchanged
    rw [D.tβ] at e
    have hwb : (ι₀.Φ (D_L0.overVisit y)).1 = sl.b₂ := liftVisit_injective hn hG hQ q₀ (e.trans sl.hb₂.symm)
    have hwb' : (geoPositiveLift hn hG hQ q₀).record.pair (ι₀.Φ (D_L0.overVisit y)).1 = sl.b₁ := by
      rw [hpair]
      apply liftVisit_injective hn hG hQ q₀
      rw [hwt, e, D.tβ', sl.hb₁]
    have hK₂ : d.K₂ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) := by
      apply r176o_crossing_set_ext
      intro u
      have := d.keep₂ u
      rw [hwb', hwb] at this
      rw [this, crossKeep_liftBlock_iff]
      exact (w3di_arcs_ident hn hG hQ D pd sl u).1
    have hK₁ : d.K₁ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) ∪
        {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.c₂} := by
      apply r176o_crossing_set_ext
      intro u
      have := d.keep₁ u
      rw [hwb', hwb] at this
      rw [this]
      exact (w3di_arcs_ident hn hG hQ D pd sl u).2.1
    rw [← hK₁] at hkγ
    exact w3di_core hn hG hQ hS D pd sl.v sl.hv D_L0 ι₀ y J_L ι₁ sl.c₂ (Or.inl hwo) d.κB d.κ₂ d.κ₁ d.ne_B2 d.ne_B1
      d.ne_12.symm d.count3 d.K₂ d.K₁ d.isoB d.iso₂ d.iso₁ d.rkB d.rk₂ d.rk₁ _ _ (Or.inl ⟨rfl, rfl⟩) hKB hK₂ hK₁
      hno hkγ

include D pd sl in
/-- **the case of the second smoothing at `γ`**: `x ↦ α`, `y ↦ γ`; the third component carries `β` -/
theorem w3di_ident_γ (D_L0 : Diagram)
    (ι₀ : RecordIso D_L0.record ((geoPositiveLift hn hG hQ q₀).record.smooth sl.v))
    (y : D_L0.Γ.Crossing) (J_L : Diagram)
    (ι₁ : RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y)))
    (hw : (liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 = γ₁.1) :
    twoLambda J_L = ((w3cb_mixedSet hG.cg Q S q₀).card : ℤ) ∧
    ∃ σ : Fin 3 ≃ Fin J_L.Γ.c,
      homfly (J_L.knotRestrict (σ 0)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr α₁))) ∧
      homfly (J_L.knotRestrict (σ 1)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr γ₂))) ∧
      homfly (J_L.knotRestrict (σ 2)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr β₂))) := by
  have h1 : (geoPositiveLift hn hG hQ q₀).record.componentCount = 1 :=
    CV.record_componentCount_one _ (geoPositiveLift_componentCount hn hG hQ q₀)
  have hpair : ∀ u : (geoPositiveLift hn hG hQ q₀).Γ.Visit,
      (geoPositiveLift hn hG hQ q₀).record.pair u = (geoPositiveLift hn hG hQ q₀).twin u := fun _ => rfl
  have hwt : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin (ι₀.Φ (D_L0.overVisit y)).1) =
      visitTwin (liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1) := liftVisit_twin hn hG hQ q₀ _
  have hKB : r176s_KB (geoPositiveLift hn hG hQ q₀).record sl.v =
      liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr α₁))) := by
    apply r176o_crossing_set_ext
    intro u
    rw [w3di_KB_iff hn hG hQ D pd sl.v sl.hv u, crossKeep_liftBlock_iff]
  have hno : (geoPositiveLift hn hG hQ q₀).record.crossingOf sl.b₂ ∉
      liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) := by
    intro h
    have h' : (liftVisit hn hG hQ q₀ sl.b₂).1 ∈ geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂)) :=
      (crossKeep_liftBlock_iff hn hG hQ q₀ _ sl.b₂).mp h
    rw [sl.hb₂, mem_geoCarrierCrossings] at h'
    exact h'.1 (by rw [w3di_β12 hG.cg D]; exact w3di_β₁S hG.cg D)
  obtain ⟨-, hkβ⟩ := w3di_kinks hn hG hQ D pd sl
  have hwo : (liftVisit hn hG hQ q₀ (ι₀.Φ (D_L0.overVisit y)).1).1 = γ₁.1 ∧ (liftVisit hn hG hQ q₀ sl.b₂).1 = β₁.1 :=
    ⟨hw, by rw [sl.hb₂]; exact w3di_β12 hG.cg D⟩
  have hA : r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v (ι₀.Φ (D_L0.overVisit y)).1 := by
    apply w3di_arcA_of_βγ hn hG hQ D pd sl
    rcases visit_eq_or_twin γ₁ _ hw with e | e
    · exact Or.inr (Or.inr (Or.inl e))
    · rw [D.tγ] at e; exact Or.inr (Or.inr (Or.inr e))
  have hA' : r176s_ArcA (geoPositiveLift hn hG hQ q₀).record sl.v
      ((geoPositiveLift hn hG hQ q₀).record.pair (ι₀.Φ (D_L0.overVisit y)).1) := by
    apply w3di_arcA_of_βγ hn hG hQ D pd sl
    rw [hpair, hwt]
    rcases visit_eq_or_twin γ₁ _ hw with e | e
    · rw [e, D.tγ]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [e, D.tγ, D.tγ']; exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨d⟩ := w3di_double_exists (geoPositiveLift hn hG hQ q₀).record h1 sl.v (ι₀.Φ (D_L0.overVisit y)) hA hA'
  rcases visit_eq_or_twin γ₁ _ hw with e | e
  · have hwc : (ι₀.Φ (D_L0.overVisit y)).1 = sl.c₁ := liftVisit_injective hn hG hQ q₀ (e.trans sl.hc₁.symm)
    have hwc' : (geoPositiveLift hn hG hQ q₀).record.pair (ι₀.Φ (D_L0.overVisit y)).1 = sl.c₂ := by
      rw [hpair]
      apply liftVisit_injective hn hG hQ q₀
      rw [hwt, e, D.tγ, sl.hc₂]
    have hK₁ : d.K₁ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) := by
      apply r176o_crossing_set_ext
      intro u
      have := d.keep₁ u
      rw [hwc', hwc] at this
      rw [this, crossKeep_liftBlock_iff]
      exact (w3di_arcs_ident hn hG hQ D pd sl u).2.2.1
    have hK₂ : d.K₂ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) ∪
        {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.b₂} := by
      apply r176o_crossing_set_ext
      intro u
      have := d.keep₂ u
      rw [hwc', hwc] at this
      rw [this]
      exact (w3di_arcs_ident hn hG hQ D pd sl u).2.2.2
    rw [← hK₂] at hkβ
    exact w3di_core hn hG hQ hS D pd sl.v sl.hv D_L0 ι₀ y J_L ι₁ sl.b₂ (Or.inr hwo) d.κB d.κ₁ d.κ₂ d.ne_B1 d.ne_B2
      d.ne_12 d.count3 d.K₁ d.K₂ d.isoB d.iso₁ d.iso₂ d.rkB d.rk₁ d.rk₂ _ _ (Or.inr ⟨rfl, rfl⟩) hKB hK₁ hK₂ hno hkβ
  · rw [D.tγ] at e
    have hwc : (ι₀.Φ (D_L0.overVisit y)).1 = sl.c₂ := liftVisit_injective hn hG hQ q₀ (e.trans sl.hc₂.symm)
    have hwc' : (geoPositiveLift hn hG hQ q₀).record.pair (ι₀.Φ (D_L0.overVisit y)).1 = sl.c₁ := by
      rw [hpair]
      apply liftVisit_injective hn hG hQ q₀
      rw [hwt, e, D.tγ', sl.hc₁]
    have hK₂ : d.K₂ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr γ₂))) := by
      apply r176o_crossing_set_ext
      intro u
      have := d.keep₂ u
      rw [hwc', hwc] at this
      rw [this, crossKeep_liftBlock_iff]
      exact (w3di_arcs_ident hn hG hQ D pd sl u).2.2.1
    have hK₁ : d.K₁ = liftBlock hn hG hQ q₀ (geoCarrierCrossings hG.cg S (geoOwner hG.cg S (Sum.inr β₂))) ∪
        {(geoPositiveLift hn hG hQ q₀).record.crossingOf sl.b₂} := by
      apply r176o_crossing_set_ext
      intro u
      have := d.keep₁ u
      rw [hwc', hwc] at this
      rw [this]
      exact (w3di_arcs_ident hn hG hQ D pd sl u).2.2.2
    rw [← hK₁] at hkβ
    exact w3di_core hn hG hQ hS D pd sl.v sl.hv D_L0 ι₀ y J_L ι₁ sl.b₂ (Or.inr hwo) d.κB d.κ₂ d.κ₁ d.ne_B2 d.ne_B1
      d.ne_12.symm d.count3 d.K₂ d.K₁ d.isoB d.iso₂ d.iso₁ d.rkB d.rk₂ d.rk₁ _ _ (Or.inr ⟨rfl, rfl⟩) hKB hK₂ hK₁
      hno hkβ

end W3DI_Assembly

/-! ### C. The identification clause in occurrence form (abstract word data) -/

section W3DI_Top
variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {Q S : Finset (Crossing P)} (hQ : GeoIndependent hG.cg Q) (hS : GeoIndependent hG.cg S)
  {q₀ : GeoComponent hG.cg Q} {α₁ α₂ β₁ β₂ γ₁ γ₂ : Visit P}
  (D : w3di_WordData hG.cg Q S q₀ α₁ α₂ β₁ β₂ γ₁ γ₂)

include hS D in
/-- **The identification clause, abstractly**: for the lift `D_L` of the contact carrier, a crossing `x_L`
over `α` and (after a smoothing with an occurrence-compatible record clause) a crossing `y_L` over `b`
(`b = β` or `b = γ`), every diagram `J_L` record-isomorphic to the second smoothing has `2Λ(J_L)` = the number
of mixed retained crossings of the contact carrier, and its three knot restrictions carry the HOMFLY
polynomials of the lifts of the outer carriers `owner_S α₁`, `owner_S b₂`, `owner_S o₂` (`o` the third
crossing). -/
theorem w3di_ident_abstract (b₁ b₂ o₂ : Visit P)
    (hb : (b₁ = β₁ ∧ b₂ = β₂ ∧ o₂ = γ₂) ∨ (b₁ = γ₁ ∧ b₂ = γ₂ ∧ o₂ = β₂))
    (x_L : (geoPositiveLift hn hG hQ q₀).Γ.Crossing)
    (hx : (geoPositiveLift hn hG hQ q₀).Γ.crossingPoint x_L = crossingPoint α₁.1)
    (D_L0 : Diagram)
    (ι₀ : RecordIso D_L0.record ((geoPositiveLift hn hG hQ q₀).record.smooth
      ((geoPositiveLift hn hG hQ q₀).overVisit x_L)))
    (hι₀ : ∀ u : D_L0.Γ.Visit, (geoPositiveLift hn hG hQ q₀).Γ.crossingPoint (ι₀.Φ u).1.1 = D_L0.Γ.crossingPoint u.1)
    (y_L : D_L0.Γ.Crossing) (hy : D_L0.Γ.crossingPoint y_L = crossingPoint b₁.1)
    (J_L : Diagram) (ι₁ : RecordIso J_L.record (D_L0.record.smooth (D_L0.overVisit y_L))) :
    twoLambda J_L = ((w3cb_mixedSet hG.cg Q S q₀).card : ℤ) ∧
    ∃ σ : Fin 3 ≃ Fin J_L.Γ.c,
      homfly (J_L.knotRestrict (σ 0)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr α₁))) ∧
      homfly (J_L.knotRestrict (σ 1)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr b₂))) ∧
      homfly (J_L.knotRestrict (σ 2)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr o₂))) := by
  obtain ⟨pd⟩ := w3di_posData_exists hG.cg hQ hS D
  obtain ⟨sl₀⟩ := w3di_sixLift_exists hn hG hQ hS D
  -- the occurrence of `x_L` over `α₁`
  have hv₀ : (liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).overVisit x_L)).1 = α₁.1 :=
    w3di_liftVisit_fst_of_point hn hG hQ _ _ hx
  -- the general step at a normalised occurrence `v ↦ α₁` with its record clause
  have key : ∀ (v : (geoPositiveLift hn hG hQ q₀).Γ.Visit) (hv : liftVisit hn hG hQ q₀ v = α₁)
      (ι : RecordIso D_L0.record ((geoPositiveLift hn hG hQ q₀).record.smooth v))
      (hι : ∀ u : D_L0.Γ.Visit, (geoPositiveLift hn hG hQ q₀).Γ.crossingPoint (ι.Φ u).1.1 = D_L0.Γ.crossingPoint u.1),
      twoLambda J_L = ((w3cb_mixedSet hG.cg Q S q₀).card : ℤ) ∧
      ∃ σ : Fin 3 ≃ Fin J_L.Γ.c,
        homfly (J_L.knotRestrict (σ 0)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr α₁))) ∧
        homfly (J_L.knotRestrict (σ 1)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr b₂))) ∧
        homfly (J_L.knotRestrict (σ 2)) = homfly (geoPositiveLift hn hG hS (geoOwner hG.cg S (Sum.inr o₂))) := by
    intro v hv ι hι
    let sl : w3di_SixLift hn hG hQ q₀ α₁ β₁ β₂ γ₁ γ₂ := { sl₀ with v := v, hv := hv }
    have hw : (liftVisit hn hG hQ q₀ (ι.Φ (D_L0.overVisit y_L)).1).1 = b₁.1 := by
      apply w3di_liftVisit_fst_of_point hn hG hQ
      rw [hι (D_L0.overVisit y_L), Diagram.overVisit_fst, hy]
    rcases hb with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact w3di_ident_β hn hG hQ hS D pd sl D_L0 ι y_L J_L ι₁ hw
    · exact w3di_ident_γ hn hG hQ hS D pd sl D_L0 ι y_L J_L ι₁ hw
  rcases visit_eq_or_twin α₁ _ hv₀ with e | e
  · exact key _ e ι₀ hι₀
  · -- the over occurrence lies over `α₂`: pass to the twin through `smoothPairIso`
    rw [D.tα] at e
    have hv : liftVisit hn hG hQ q₀ ((geoPositiveLift hn hG hQ q₀).twin ((geoPositiveLift hn hG hQ q₀).overVisit x_L)) =
        α₁ := by
      rw [liftVisit_twin, e, D.tα']
    refine key _ hv (ι₀.trans ((geoPositiveLift hn hG hQ q₀).record.smoothPairIso _).symm) ?_
    intro u
    exact hι₀ u

end W3DI_Top


/-- the crossings of the twin visits of `w3ca_SixData` (used to read the mirror pattern) -/
theorem w3di_α12_aux {n : ℕ} [NeZero n] {P : LabelledTuple n} {hP : CrossingGeometry P} {Q : Finset (Crossing P)}
    {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P} (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂) : a₂.1 = a₁.1 := D.a12
theorem w3di_β12_aux {n : ℕ} [NeZero n] {P : LabelledTuple n} {hP : CrossingGeometry P} {Q : Finset (Crossing P)}
    {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P} (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂) : b₂.1 = b₁.1 := D.b12
theorem w3di_γ12_aux {n : ℕ} [NeZero n] {P : LabelledTuple n} {hP : CrossingGeometry P} {Q : Finset (Crossing P)}
    {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P} (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂) : c₂.1 = c₁.1 := D.c12

/-! ### D. The configuration: SPLITA's six visits in the two orientation patterns, the black box for the
parity clause (unit RESPAR), and the identification clause of `w3cx_outer_residue` -/

section W3DI_Config
open Equiv

section W3DI_Pattern
variable {n : ℕ} [NeZero n] {P : LabelledTuple n}
attribute [local instance high] Classical.propDecidable

/-- SPLITA's `w3ca_pattern` with the support given by its membership predicate (the classical-`insert`
bridge of `w3ca_core`) -/
theorem w3di_pattern' (hP : CrossingGeometry P) {Q : Finset (Crossing P)} {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P}
    (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂) (S : Finset (Crossing P))
    (hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = a₁.1 ∨ x = b₁.1 ∨ x = c₁.1) (hS : GeoIndependent hP S) :
    (geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ ∧ geoMarkSuccessor hP (Sum.inr b₂) = Sum.inr c₁ ∧
      geoMarkSuccessor hP (Sum.inr c₂) = Sum.inr a₂) ∨
    (geoMarkSuccessor hP (Sum.inr b₁) = Sum.inr a₁ ∧ geoMarkSuccessor hP (Sum.inr c₁) = Sum.inr b₂ ∧
      geoMarkSuccessor hP (Sum.inr a₂) = Sum.inr c₂) := by
  have hSdef : S = insert c₁.1 (insert b₁.1 (insert a₁.1 Q)) := by
    ext x
    rw [hSeq]
    simp only [Finset.mem_insert]
    tauto
  subst hSdef
  exact w3ca_pattern hP D hS

end W3DI_Pattern

/-- in the mirror pattern the edge `e` does NOT read `a₁ b₁` (the traversal circle has more than two marks) -/
theorem w3di_not_succ_of_mirror {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)
    {Q : Finset (Crossing P)} {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P} (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂)
    (h : geoMarkSuccessor hP (Sum.inr b₁) = Sum.inr a₁) :
    ¬ geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁ := by
  intro h'
  have hfix : (geoMarkSuccessor hP ^ 2) (Sum.inr a₁) = Sum.inr a₁ := by
    rw [pow_two, Perm.mul_apply, h', h]
  have hsc := geoMarkSuccessor_sameCycle hP (Sum.inr a₁) (Sum.inr c₁)
  rw [r176o_sameCycle_iff_pow _ (by norm_num) hfix] at hsc
  obtain ⟨i, hi, hic⟩ := hsc
  interval_cases i
  · rw [pow_zero, Perm.one_apply] at hic
    exact D.ac (by rw [Sum.inr.inj hic])
  · rw [pow_one, h'] at hic
    exact D.bc (by rw [Sum.inr.inj hic])

/-- **BLACK BOX (unit RESPAR) — the parity clause of `w3cx_outer_residue`**: the retained crossings of
the contact carrier `q₀'` unselected in `Q' ∪ T'` whose two visits lie on different outer carriers number
`2Λ` (binders = those of `w3cx_outer_residue`). -/
def w3di_parity : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ Λ : ℕ,
        (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card = 2 * Λ

/-- **the parity clause, PROVED** (W3D assembler): unit RESPAR's `w3dp_parity_at_proof` — `w3di_parity` and
`w3dp_parity_at` are the residue's binders with the parity conclusion `#w3cb_mixedSet Q' (Q' ∪ T') q₀' = 2Λ`, identical
up to binder names, so the proof term is accepted as is. -/
theorem w3di_parity_data : w3di_parity := w3dp_parity_at_proof

/-- **The identification clause of `w3cx_outer_residue` at every configuration, given the parity**
(unit RESID): `twoLambda J_L = 2Λ` and the three knot restrictions of `J_L = D_L^{xy}` carry the grouped
polynomials of SPLITA's `w3ca_A, w3ca_B, w3ca_C`, in the record-clause form `w3ck_three_components_ident_occ`.
Route: the six visits and the orientation pattern of SPLITA (`w3ca_sixData_config`, `w3ca_pattern`) give the
word data `w3di_WordData` (pattern P1 with `(α, β, γ) = (a, b, c)`, pattern P2 with `(α, β, γ) = (a, c, b)`),
`w3di_ident_abstract` does the rest, and `r176s_homfly_eq_groupedPoly` reads the lifts of the outer carriers
as `groupedPoly`. -/
theorem w3di_ident_at {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q))
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀')
    (Λ : ℕ)
    (hpar : (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)
      (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card = 2 * Λ) :
    w3ck_three_components_ident_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
      (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
      (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))
      (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)))
      (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg))) := by
  have hef' := (hs _).mp hef
  have heg' := (hs _).mp heg
  have hfg' := (hs _).mp hfg
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have D6 := w3ca_sixData_config hL ht' hef' heg' hfg' hQ' hfull'
  have hSeq : ∀ x, x ∈ transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ↔
      x ∈ transportSupport hs Q ∨ x = xPair hef' ∨ x = xPair heg' ∨ x = xPair hfg' := by
    intro x
    rw [Finset.mem_union, P1.mem_triangleCrossings_iff hef' heg' hfg']
  have hSi : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hQi : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs Q) := CV.geoIndependent_of_mem_Ind _ hQi'
  obtain ⟨core, -, -, -⟩ := w3ca_split_config hL ht' hef' heg' hfg' hQ' hfull' hS'
  have hpat := w3di_pattern' (geomAt E t' ht'.1) D6 _ hSeq hSi
  obtain ⟨v, hv, hvq⟩ := (esc_not_triangleDisjoint_iff _ _ _ _ _ _).1 hq₀'
  have hsix := w3ca_six_on_contact _ D6 _ hSeq hSi v (w3ca_visit_six hef' heg' hfg' v hv)
  have hq₀a₁ : geoOwner (geomAt E t' ht'.1) (transportSupport hs Q)
      (Sum.inr (visitOn (xPair hef') e (mem_pair_left e f))) = q₀' := hsix.symm.trans hvq
  have hq₀a₂ : geoOwner (geomAt E t' ht'.1) (transportSupport hs Q)
      (Sum.inr (visitOn (xPair hef') f (mem_pair_right e f))) = q₀' := by
    have := w3ca_six_on_contact _ D6 _ hSeq hSi (visitOn (xPair hef') f (mem_pair_right e f))
      (Or.inr (Or.inl rfl))
    exact this.trans hq₀a₁
  have hpoly : ∀ X : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g),
      homfly (geoPositiveLift hn (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hSi X) =
        CV.groupedPoly hn (genericAt E t' ht'.1) hS' X :=
    fun X => r176s_homfly_eq_groupedPoly hn (genericAt E t' ht'.1) hS' X _ ⟨RecordIso.refl _⟩
  intro x_L hx D_L0 _ hocc y_L hy J_L _ hJ
  obtain ⟨ι₀, hι₀⟩ := hocc
  obtain ⟨ι₁⟩ := hJ
  rcases hpat with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- pattern P1: the word `a₁ b₁ | b₂ c₁ | c₂ a₂`; `(α, β, γ) = (a, b, c)`
    have hA : w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) hef' heg' hfg' =
        geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          (Sum.inr (visitOn (xPair hef') e (mem_pair_left e f))) := by
      simp only [w3ca_A, w3ca_Ac, h1, ↓reduceIte]
    have hB : w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) hef' heg' hfg' =
        geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          (Sum.inr (visitOn (xPair heg') g (mem_pair_right e g))) := by
      simp only [w3ca_B, w3ca_Bc, h1, ↓reduceIte]
    have hC : w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) hef' heg' hfg' =
        geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          (Sum.inr (visitOn (xPair hfg') f (mem_pair_left f g))) := by
      simp only [w3ca_C, w3ca_Cc, h1, ↓reduceIte]
    have hdist := core.distinct
    rw [hA, hB, hC] at hdist
    have D : w3di_WordData (geomAt E t' ht'.1) (transportSupport hs Q)
        (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀'
        (visitOn (xPair hef') e (mem_pair_left e f)) (visitOn (xPair hef') f (mem_pair_right e f))
        (visitOn (xPair heg') e (mem_pair_left e g)) (visitOn (xPair heg') g (mem_pair_right e g))
        (visitOn (xPair hfg') g (mem_pair_right f g)) (visitOn (xPair hfg') f (mem_pair_left f g)) :=
      { tα := D6.ta, tα' := D6.ta', tβ := D6.tb, tβ' := D6.tb', tγ := D6.tc, tγ' := D6.tc'
        αβ := D6.ab, αγ := D6.ac, βγ := D6.bc, αQ := D6.aQ, βQ := D6.bQ, γQ := D6.cQ
        hSeq := hSeq, wαβ := h1, wβγ := h2, wγα := h3, hq₀ := hq₀a₁
        neαβ := hdist.1, neαγ := hdist.2.1, neβγ := hdist.2.2.2.1 }
    obtain ⟨htl, σ, hσ0, hσ1, hσ2⟩ := w3di_ident_abstract hn
      (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hQi hSi D _ _ _
      (Or.inl ⟨rfl, rfl, rfl⟩) x_L hx D_L0 ι₀ hι₀ y_L hy J_L ι₁
    refine ⟨?_, σ, ?_, ?_, ?_⟩
    · rw [htl, hpar]; push_cast; ring
    · rw [hσ0, hA]; exact hpoly _
    · rw [hσ1, hB]; exact hpoly _
    · rw [hσ2, hC]; exact hpoly _
  · -- pattern P2: the word `b₁ a₁ | c₁ b₂ | a₂ c₂`, read from `a₂` as `a₂ c₂ | c₁ b₂ | b₁ a₁`;
    -- `(α, β, γ) = (a, c, b)`
    have hn1 := w3di_not_succ_of_mirror _ D6 h1
    have hA : w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) hef' heg' hfg' =
        geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          (Sum.inr (visitOn (xPair hef') f (mem_pair_right e f))) := by
      simp only [w3ca_A, w3ca_Ac, hn1, ↓reduceIte]
    have hB : w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) hef' heg' hfg' =
        geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          (Sum.inr (visitOn (xPair heg') e (mem_pair_left e g))) := by
      simp only [w3ca_B, w3ca_Bc, hn1, ↓reduceIte]
    have hC : w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) hef' heg' hfg' =
        geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)
          (Sum.inr (visitOn (xPair hfg') g (mem_pair_right f g))) := by
      simp only [w3ca_C, w3ca_Cc, hn1, ↓reduceIte]
    have hdist := core.distinct
    rw [hA, hB, hC] at hdist
    have hSeq' : ∀ x, x ∈ transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ↔
        x ∈ transportSupport hs Q ∨ x = xPair hef' ∨ x = xPair hfg' ∨ x = xPair heg' := by
      intro x
      rw [hSeq x]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
      · rintro (h | h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
    have D : w3di_WordData (geomAt E t' ht'.1) (transportSupport hs Q)
        (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀'
        (visitOn (xPair hef') f (mem_pair_right e f)) (visitOn (xPair hef') e (mem_pair_left e f))
        (visitOn (xPair hfg') f (mem_pair_left f g)) (visitOn (xPair hfg') g (mem_pair_right f g))
        (visitOn (xPair heg') g (mem_pair_right e g)) (visitOn (xPair heg') e (mem_pair_left e g)) :=
      { tα := D6.ta', tα' := D6.ta, tβ := D6.tc', tβ' := D6.tc, tγ := D6.tb', tγ' := D6.tb
        αβ := fun h => D6.ac (by rw [← w3di_α12_aux D6, ← w3di_γ12_aux D6]; exact h)
        αγ := fun h => D6.ab (by rw [← w3di_α12_aux D6, ← w3di_β12_aux D6]; exact h)
        βγ := fun h => D6.bc (by rw [← w3di_β12_aux D6, ← w3di_γ12_aux D6]; exact h.symm)
        αQ := by rw [w3di_α12_aux D6]; exact D6.aQ
        βQ := by rw [w3di_γ12_aux D6]; exact D6.cQ
        γQ := by rw [w3di_β12_aux D6]; exact D6.bQ
        hSeq := hSeq', wαβ := h3, wβγ := h2, wγα := h1, hq₀ := hq₀a₂
        neαβ := hdist.2.1, neαγ := hdist.1, neβγ := fun h => hdist.2.2.2.1 h.symm }
    obtain ⟨htl, σ, hσ0, hσ1, hσ2⟩ := w3di_ident_abstract hn
      (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hQi hSi D _ _ _
      (Or.inr ⟨rfl, rfl, rfl⟩) x_L hx D_L0 ι₀ hι₀ y_L hy J_L ι₁
    refine ⟨?_, σ, ?_, ?_, ?_⟩
    · rw [htl, hpar]; push_cast; ring
    · rw [hσ0, hA]; exact hpoly _
    · rw [hσ1, hB]; exact hpoly _
    · rw [hσ2, hC]; exact hpoly _

/-- **`w3cx_outer_residue` from the parity black box and the identification** (unit RESID): the parity
clause is RESPAR's `w3di_parity_data`; the identification clause at the same `Λ` is `w3di_ident_at`. -/
theorem w3di_outer_residue_proof : w3cx_outer_residue := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨Λ, hpar⟩ := w3di_parity_data hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi
    hQi' hS' q₀ q₀' hq₀ hq₀'
  exact ⟨Λ, hpar, w3di_ident_at hn E e f g δ hL t t' ht ht' hop hs hef heg hfg Q hQ hfull hQi' hS' q₀' hq₀' Λ hpar⟩

end W3DI_Config

end W3DI_RESID

/-- **the OUTER residue, PROVED** (W3D assembler): unit RESID's `w3di_outer_residue_proof` — the identification clause
`w3di_ident_at` at the parity's `Λ` — with unit RESPAR's parity clause `w3dp_parity_at_proof` wired in through
`w3di_parity_data` (W3D_RESPAR_REPORT.md, W3D_RESID_REPORT.md, W3D_ASSEMBLY_REPORT.md §1). -/
theorem w3cx_outer_residue_data : w3cx_outer_residue := w3di_outer_residue_proof

/-- (W3C assembler) **`esc_FullSplitData` at a configuration for SPLITA's carriers**, given the residue's sign table
and parity: SPLITA's `w3ca_split_at_outer` (`touching_iff`, `central_no_piece`), the corner ledger
`w3cx_splitCorners_of_core` (from `w3ca_split_config`, `w3ca_sixData_config`, `w3ca_marks_partition_config`), SPLITB's
`w3cb_fields_of_residue` (`writhe`, `mixed`) on the core `w3cx_splitCore_of_core` with `w3cb_triangle_on_contact_at`,
assembled by SPLITC's `w3cc_fullSplitData_of` (`distinct`, `central_rot`, `outer_alternative`, `uniform`). -/
theorem w3cx_fullSplitData_at {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q))
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀')
    (Λ : ℕ) (s : SignType) (hs0 : s ≠ 0)
    (htable : (∀ v : Visit (E.curve t'), v.1 ∈ triangleCrossings (E.curve t') e f g →
          (geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) (Sum.inr v) =
              w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∨
            geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) (Sum.inr v) =
              w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) ∨
            geoOwner (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) (Sum.inr v) =
              w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) →
          w3cb_turnAt (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) (Sum.inr v) = s))
    (hmixed : (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card = 2 * Λ) :
    esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀'
      (w3ca_A (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) (w3ca_B (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) (w3ca_C (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) (w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)) Λ := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  have D := w3ca_sixData_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull'
  have hSeq : ∀ x, x ∈ transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ↔
      x ∈ transportSupport hs Q ∨ x = xPair ((hs _).mp hef) ∨ x = xPair ((hs _).mp heg) ∨
        x = xPair ((hs _).mp hfg) := by
    intro x
    rw [Finset.mem_union, P1.mem_triangleCrossings_iff ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)]
  obtain ⟨zA, zB, zC, hC⟩ := w3cx_splitCorners_of_core (geomAt E t' ht'.1) D hSeq core rfl rfl rfl q₀'
    (fun m => w3ca_marks_partition_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
      q₀' hq₀' m)
  obtain ⟨touching_iff, -, central_no_piece⟩ :=
    w3ca_split_at_outer E e f g δ hL t t' ht ht' hop hs hef heg hfg Q hQ hfull hS'
  have hcore := w3cx_splitCore_of_core (geomAt E t' ht'.1) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) q₀'
    D core hs0 htable hmixed
  obtain ⟨writhe, mixed⟩ := w3cb_fields_of_residue hn (genericAt E t' ht'.1) e f g hQi' hS' ((hs _).mp hef)
    ((hs _).mp heg) ((hs _).mp hfg) q₀' (w3ca_Z (geomAt E t' ht'.1) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg))
    (w3cb_residue_of_core _ hcore (w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'))
  exact w3cc_fullSplitData_of hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' _ _ _ _ Λ hC touching_iff
    central_no_piece writhe mixed

/-- (W3C assembler) **KNOT's `w3ck_split_ident` from the residue**: `esc_FullSplitData` by `w3cx_fullSplitData_at`,
the identification clause verbatim from the residue, for the SAME `Λ`. -/
theorem w3cx_split_ident_of_residue (h : w3cx_outer_residue) : w3ck_split_ident := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨Λ, hmixed, hident⟩ :=
    h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨s, hs0, htable⟩ := w3cx_sign_table_at hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hS'
  exact ⟨_, _, _, _, Λ, w3cx_fullSplitData_at hn E e f g δ hL t t' ht ht' hop hs hef heg hfg Q hQ hfull hQi' hS'
    q₀' hq₀' Λ s hs0 htable hmixed, hident⟩

/-- (W3C assembler) **SPLITB's `w3cb_split_core` from the residue**: SPLITA's carriers and core with the residue's
sign table and parity (`w3cx_splitCore_of_core`). -/
theorem w3cx_split_core_of_residue (h : w3cx_outer_residue) : w3cb_split_core := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨Λ, hmixed, -⟩ :=
    h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨s, hs0, htable⟩ := w3cx_sign_table_at hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hS'
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  exact ⟨_, _, _, Λ, s, w3cx_splitCore_of_core (geomAt E t' ht'.1) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)
    q₀' (w3ca_sixData_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull') core hs0 htable
    hmixed⟩

/-- (W3C assembler) SPLITB's black box, PROVED modulo the residue (moved here from `section W3CB_SPLITB`; statement
unchanged). -/
theorem w3cb_split_core_data : w3cb_split_core :=
  w3cx_split_core_of_residue w3cx_outer_residue_data

/-- the split geometry at every configuration from the core (`triangle_on_contact` supplied by
`w3cb_triangle_on_contact_at`) — unit SPLITB's theorem, moved after the residue -/
theorem w3cb_split_geometry_of_core (h : w3cb_split_core) : w3cb_split_geometry := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨A, B, C, Λ, s, hc⟩ :=
    h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  exact ⟨A, B, C, Λ, s, w3cb_splitGeometry_of_residue _ ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)
    (CV.geoIndependent_of_mem_Ind _ hS')
    (w3cb_residue_of_core _ hc (w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'))⟩

/-- the split geometry at every configuration, on the black box (unit SPLITB's theorem, moved after the residue) -/
theorem w3cb_split_geometry_data : w3cb_split_geometry :=
  w3cb_split_geometry_of_core w3cb_split_core_data

/-- (W3C assembler) KNOT's black box, PROVED modulo the residue. -/
theorem w3ck_split_ident_data : w3ck_split_ident :=
  w3cx_split_ident_of_residue w3cx_outer_residue_data

/-- **the corrected OUTER data from the split + identification**: the two counts are this unit's theorems. -/
theorem w3ck_esc_outer_occ_of (h : w3ck_split_ident) : w3ck_esc_outer_occ := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hT hT'
  obtain ⟨A, B, C, Z, Λ, hsplit, hident⟩ :=
    h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hT hT'
  exact ⟨A, B, C, Z, Λ, hsplit, w3ck_knot_after_two hn E e f g t ht.1 hef heg hfg hK hQi q₀,
    w3ck_three_components_occ_of
      (w3ck_three_components_count hn E e f g δ hL t t' ht ht' hop hs hef heg hfg hK hQi' q₀') hident⟩

theorem w3ck_esc_outer_occ_holds : w3ck_esc_outer_occ := w3ck_esc_outer_occ_of w3ck_split_ident_data

end W3CK_Outer

/-! ### K8. The chain made consumable: the weak (6) form with occurrence-compatible record clauses, the move
data / interface in the record-clause form, and the ledger replayed on it (byte-faithful copies of the `w3bi_`
replay; only the two consumption lines of the contact identity pass the record clauses) -/

section W3CK_Chain

open RProof CV SM.GeoCarrier SM.Carrier Smoothing

variable {n : ℕ} [NeZero n]

/-- **(6) in the weak form with occurrence-compatible record clauses** (`esc_rii_after_smoothing_weak` of
SM/BigonDeletion.lean with `w3ck_SmoothRecordOcc` in place of the bare `RecordIso`; realised by
`smoothDiagram` + `w3h_smooth_record_occ`). -/
def w3ck_esc_rii_after_smoothing_weak_occ (D_H D_L : Diagram) (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing)
    (pyH pyL : Plane) : Prop :=
  ∃ (D_H0 D_L0 : Diagram), IsOrientedSmoothing D_H x_H D_H0 ∧ IsOrientedSmoothing D_L x_L D_L0 ∧
    w3ck_SmoothRecordOcc D_H x_H D_H0 ∧ w3ck_SmoothRecordOcc D_L x_L D_L0 ∧
    ∀ (y_H : D_H0.Γ.Crossing) (y_L : D_L0.Γ.Crossing),
      D_H0.Γ.crossingPoint y_H = pyH → D_L0.Γ.crossingPoint y_L = pyL →
      homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L)

/-- **`esc_MoveData` in the record-clause form**: (4) byte-identical, (6) weak with occurrence-compatible
record clauses, the two outer clauses in their record-clause forms. -/
structure w3ck_esc_MoveDataOcc (D_H D_L : Diagram) (pxH pyH pxL pyL : Plane) (Λ : ℕ)
    (fA fB fC : R) : Prop where
  /-- (4), for the crossings at the double points of `x`. -/
  switch_riii : ∀ (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing),
    D_H.Γ.crossingPoint x_H = pxH → D_L.Γ.crossingPoint x_L = pxL → esc_switch_riii D_H D_L x_H x_L
  /-- (6) in the weak form with record clauses, for the crossings at the double points of `x`. -/
  rii_after_smoothing_weak : ∀ (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing),
    D_H.Γ.crossingPoint x_H = pxH → D_L.Γ.crossingPoint x_L = pxL →
    w3ck_esc_rii_after_smoothing_weak_occ D_H D_L x_H x_L pyH pyL
  knot_after_two : w3ck_knot_after_two_occ D_H pxH pyH
  three_components : w3ck_three_components_occ D_L pxL pyL Λ fA fB fC

/-- **The interface of row 177, EXTENDED, with the move data in the record-clause form `w3ck_esc_MoveDataOcc`** (copy of `w3bi_esc_interface_ext`; original docstring:) **The interface of row 177, EXTENDED (F-177-2)**: `esc_interface`'s statement with the two extra
hypotheses `GenericTableData` and `AV_EventRadius` (needed for `trans_sw` and `hdet`, skeleton report
§1.4) and the move data in the weak form `w3ck_esc_MoveDataOcc`.  `RProof/RALedgers.lean` is untouched;
the ledger is replayed below (`w3bi_esc_couple`, `w3bi_esc_ledger`). -/
def w3ck_esc_interface_ext_occ : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        w3ck_esc_MoveDataOcc (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg))
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)

/-! ### (W3D assembler) the operative chain through the VALUE form of the site data (unit NONKINK, step 8).  The site
input of the record-clause interface is `w3dk_rii_value_sites_data` — the HOMFLY equality of the two switched smoothings
at every configuration, kink case included (W3D_NONKINK_REPORT.md) — in place of the Wave-3c site box
`w3bi_rii_sites_data`, whose non-kink leaf was false as stated; that box and the superseded Wave-3b chain were removed
(W3D_ASSEMBLY_REPORT.md §2). -/

/-- (W3D NONKINK) copy of `w3ck_rii_after_smoothing_weak_occ` on the value form of the site data. -/
theorem w3dk_rii_after_smoothing_weak_occ (hsites : w3dk_rii_value_sites) (hn : 3 ≤ n) {E : CV.Event n}
    {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀ : GeoComponent (geomAt E t ht.1) Q)
    (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q))
    (hq₀ : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀)
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀')
    (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
    (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing)
    (hxH : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H =
      crossingPoint (xPair hef))
    (hxL : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
      crossingPoint (xPair ((hs _).mp hef))) :
    w3ck_esc_rii_after_smoothing_weak_occ (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
      (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_H x_L
      (crossingPoint (xPair heg)) (crossingPoint (xPair ((hs _).mp heg))) :=
  ⟨_, _, isOrientedSmoothing_smoothDiagram _ _ _ (eps_small _ x_H),
    isOrientedSmoothing_smoothDiagram _ _ _ (eps_small _ x_L),
    w3h_smooth_record_occ _ x_H _ (eps_small _ x_H), w3h_smooth_record_occ _ x_L _ (eps_small _ x_L),
    fun y_H y_L hyH hyL => hsites hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull
        hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL y_H y_L hyH hyL⟩

/-- (W3D NONKINK) copy of `w3ck_esc_interface_ext_of` on the value form of the site data. -/
theorem w3dk_esc_interface_ext_of (houter : w3ck_esc_outer_occ) (hsites : w3dk_rii_value_sites) :
    w3ck_esc_interface_ext_occ := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨A, B, C, Z, Λ, hsplit, hk2, h3c⟩ := houter hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg
    hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  exact ⟨A, B, C, Z, Λ, hsplit,
    { switch_riii := fun x_H x_L hxH hxL =>
        w3bi_switch_riii hn hL hGT hR ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀'
          x_H x_L hxH hxL
      rii_after_smoothing_weak := fun x_H x_L hxH hxL =>
        w3dk_rii_after_smoothing_weak_occ hsites hn hL hGT hR ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi'
          q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL
      knot_after_two := hk2
      three_components := h3c }⟩

/-- the record-clause interface, both inputs PROVED: the OUTER data `w3ck_esc_outer_occ_holds` (SPLITA / SPLITB / SPLITC /
KNOT, with the residue closed by RESPAR + RESID) and the value form of the site data `w3dk_rii_value_sites_data` (NONKINK) -/
theorem w3ck_esc_interface_ext_occ_holds : w3ck_esc_interface_ext_occ :=
  w3dk_esc_interface_ext_of w3ck_esc_outer_occ_holds w3dk_rii_value_sites_data

/-- **The contact identity, replayed on the record-clause move data `w3ck_esc_MoveDataOcc`** (copy of `w3bi_esc_contact_identity`, the two consumption lines pass the record clauses; original docstring:) **The contact identity, replayed (D-RM-5) on the WEAK move data** (`w3ck_esc_MoveDataOcc`: the two
smoothings at `x` are the ones the weak clause provides instead of `exists_smoothing_record_visit`; body
otherwise the accepted `esc_contact_identity`).  **The contact identity**: the difference of the two touching factors of the empty row is the
touching factor of the full row on the empty side (ESC §1–§5 at one configuration), from the interface
data and `CarrierSlotFloor`. -/
theorem w3ck_esc_contact_identity (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n}
    {δ : ℝ} (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef₀ : e ≠ f) (heg₀ : e ≠ g) (hfg₀ : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (_hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
    (hI : ∀ (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        w3ck_esc_MoveDataOcc (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg))
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)) :
    touchingFactor hn (genericAt E t ht.1) hQi e f g -
        touchingFactor hn (genericAt E t' ht'.1) hQi' e f g =
      touchingFactor hn (genericAt E t' ht'.1) hS' e f g := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  -- the contact carrier on the `K3` side
  obtain ⟨q₀, hq₀⟩ := esc_contact_exists ht hef Q
  have huniq : ∀ q, ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q ↔ q = q₀ :=
    fun q => ⟨fun hq => esc_contact_unique hL hef₀ heg₀ hfg₀ ht hQ hfull hq hq₀, fun h => h ▸ hq₀⟩
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  -- the wall and the transported contact carrier on the empty side
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hX := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hX, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have huniq' : ∀ q, ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q ↔
      q = GT_carrierEquiv W q₀ :=
    fun q => ⟨fun hq => esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq hq₀', fun h => h ▸ hq₀'⟩
  have hT'q₀' := esc_contact_owns hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀'
  -- the interface data
  obtain ⟨A, B, C, Z, Λ, hsplit, hmove⟩ := hI q₀ (GT_carrierEquiv W q₀) hq₀ hq₀'
  -- notation
  set hG := genericAt E t ht.1
  set hG' := genericAt E t' ht'.1
  set q₀' := GT_carrierEquiv W q₀
  set D_H := CV.carrierDiagram hn hG hQi q₀
  set D_L := CV.carrierDiagram hn hG' hQi' q₀'
  set fA := CV.groupedPoly hn hG' hS' A
  set fB := CV.groupedPoly hn hG' hS' B
  set fC := CV.groupedPoly hn hG' hS' C
  -- the transported data of the contact carrier
  have hw : CV.weight hG'.crossingGeometry (transportSupport hs Q) q₀' = CV.weight hG.crossingGeometry Q q₀ :=
    GT_weight_eq hn hG hG' W q₀
  have hRq : CV.carrierR hn hG' hQi' q₀' = CV.carrierR hn hG hQi q₀ := GT_carrierR_eq hn hG hG' W hQi hQi' q₀
  have hwr : CV.groupedWrithe hG' q₀' = CV.groupedWrithe hG q₀ := by
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      hX, Finset.card_map]
  have hslot : CV.slot hn hG' hQi' q₀' = CV.slot hn hG hQi q₀ := by
    unfold CV.slot; rw [hRq, hwr]
  -- the two touching factors of the empty row and the one of the full row
  rw [esc_touchingFactor_eq_of_unique hn hG hQi e f g q₀ huniq,
    esc_touchingFactor_eq_of_unique hn hG' hQi' e f g q₀' huniq',
    esc_touchingFactor_eq_of_four hn hG' hS' e f g A B C Z hsplit.distinct hsplit.touching_iff, ← hw,
    ← mul_sub]
  -- the central carrier: `Ω₁ = 1`
  have hΩZ : CV.Omega1 hn hG' hS' Z = 1 := by
    unfold CV.Omega1 CV.slot
    rw [CV.groupedPoly_of_piecesOn_eq_empty hn hG' hS' Z hsplit.central_no_piece,
      CV.groupedWrithe_of_piecesOn_eq_empty hG' Z hsplit.central_no_piece, hsplit.central_rot]
    simp [coeffAt_one]
  rw [hΩZ]
  -- `Ω_H − Ω_L = [a^d z^0](F_H − F_L)`, `d` the common slot
  have hΩ : CV.Omega1 hn hG hQi q₀ - CV.Omega1 hn hG' hQi' q₀' =
      coeffAt (CV.slot hn hG' hQi' q₀') 0 (homfly D_H - homfly D_L) := by
    unfold CV.Omega1
    rw [hslot, GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly, coeffAt_sub]
  -- the crossings `x`, `y` on the grouped contact diagrams, the smoothings, the moves
  have hxT : xPair hef ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
  have hyT : xPair heg ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hxT' : xPair hef' ∈ triangleCrossings (E.curve t') e f g :=
    (P1.mem_triangleCrossings_iff hef' heg' hfg' _).mpr (Or.inl rfl)
  have hyT' : xPair heg' ∈ triangleCrossings (E.curve t') e f g :=
    (P1.mem_triangleCrossings_iff hef' heg' hfg' _).mpr (Or.inr (Or.inl rfl))
  obtain ⟨x_H, hxH_pt, hxH_pos⟩ := esc_lift_crossing hn hG hQi q₀ (xPair hef) (hTq₀ hxT)
  obtain ⟨y_H, hyH_pt, hyH_pos⟩ := esc_lift_crossing hn hG hQi q₀ (xPair heg) (hTq₀ hyT)
  obtain ⟨x_L, hxL_pt, hxL_pos⟩ := esc_lift_crossing hn hG' hQi' q₀' (xPair hef') (hT'q₀' hxT')
  obtain ⟨y_L, hyL_pt, hyL_pos⟩ := esc_lift_crossing hn hG' hQi' q₀' (xPair heg') (hT'q₀' hyT')
  have hyxH : y_H ≠ x_H := by
    intro h
    apply P1.xPair_ef_ne_eg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hxH_pt, ← hyH_pt, h]
  have hyxL : y_L ≠ x_L := by
    intro h
    apply P1.xPair_ef_ne_eg hef' heg' hfg'
    apply crossingPoint_injective_of_geometry (geomAt E t' ht'.1)
    rw [← hxL_pt, ← hyL_pt, h]
  have m6w := hmove.rii_after_smoothing_weak x_H x_L hxH_pt hxL_pt
  unfold w3ck_esc_rii_after_smoothing_weak_occ at m6w
  obtain ⟨D_H0, D_L0, hsmH, hsmL, hoccH, hoccL, m6f⟩ := m6w
  obtain ⟨y_H0, hyH0_pt, hyH0_pos⟩ := esc_smoothing_outer hsmH y_H hyxH
  obtain ⟨y_L0, hyL0_pt, hyL0_pos⟩ := esc_smoothing_outer hsmL y_L hyxL
  rw [hyH_pt] at hyH0_pt
  rw [hyL_pt] at hyL0_pt
  obtain ⟨J_H, hsmJH, hJH_rec⟩ := exists_smoothing_record_visit D_H0 y_H0 (D_H0.overVisit y_H0) rfl
  obtain ⟨J_L, hsmJL, hJL_rec⟩ := exists_smoothing_record_visit D_L0 y_L0 (D_L0.overVisit y_L0) rfl
  have m4 := hmove.switch_riii x_H x_L hxH_pt hxL_pt
  have m6 : esc_rii_after_smoothing D_H0 D_L0 y_H0 y_L0 := m6f y_H0 y_L0 hyH0_pt hyL0_pt
  have hJH := hmove.knot_after_two x_H hxH_pt D_H0 hsmH hoccH y_H0 hyH0_pt J_H hsmJH hJH_rec
  have h12 := esc_three_component_row (hmove.three_components x_L hxL_pt D_L0 hsmL hoccL y_L0 hyL0_pt J_L hsmJL
    hJL_rec)
  -- (13)
  have h13 := esc_coefficient_identity hxH_pos hxL_pos hsmH hsmL (hyH0_pos.mpr hyH_pos)
    (hyL0_pos.mpr hyL_pos) hsmJH hsmJL m4 m6 hJH h12 (CV.slot hn hG' hQi' q₀')
  rw [hΩ, h13, esc_coeffAt_sq_mul]
  -- the three selector branches on the empty contact carrier
  set d := CV.slot hn hG' hQi' q₀' with hd
  set K := fA * fB * fC with hK
  have hprod : (CV.weight hG'.crossingGeometry _ A * CV.Omega1 hn hG' hS' A) *
      (CV.weight hG'.crossingGeometry _ B * CV.Omega1 hn hG' hS' B) *
      (CV.weight hG'.crossingGeometry _ C * CV.Omega1 hn hG' hS' C) *
      (CV.weight hG'.crossingGeometry _ Z * 1) =
      (CV.weight hG'.crossingGeometry _ A * CV.weight hG'.crossingGeometry _ B *
        CV.weight hG'.crossingGeometry _ C * CV.weight hG'.crossingGeometry _ Z) *
      (CV.Omega1 hn hG' hS' A * CV.Omega1 hn hG' hS' B * CV.Omega1 hn hG' hS' C) := by ring
  rw [hprod]
  by_cases huni : CV.CarrierUniform hG'.crossingGeometry (transportSupport hs Q) q₀'
  · -- the uniform contact carrier: the outer floors
    obtain ⟨haltA, haltB, haltC⟩ := hsplit.outer_alternative huni
    have hqA := esc_quadrant_groupedPoly hF hn hG' hS' A haltA
    have hqB := esc_quadrant_groupedPoly hF hn hG' hS' B haltB
    have hqC := esc_quadrant_groupedPoly hF hn hG' hS' C haltC
    have hqK := esc_quadrant_mul (esc_quadrant_mul hqA hqB) hqC
    -- (19)
    have h19 : coeffAt (CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C) 0 K =
        CV.Omega1 hn hG' hS' A * CV.Omega1 hn hG' hS' B * CV.Omega1 hn hG' hS' C := by
      rw [hK, esc_coeffAt_corner (esc_quadrant_mul hqA hqB) hqC, esc_coeffAt_corner hqA hqB]
      rfl
    have hwrq := hsplit.writhe
    have hdq : d = 1 - CV.groupedWrithe hG' q₀' - (CV.carrierR hn hG' hQi' q₀' : ℤ) := rfl
    rcases hsplit.uniform huni with ⟨hrot, hwf⟩ | ⟨hrot, hwf⟩
    · -- live branch `χ = 1`: (18) `D = d + 4 + 2Λ`; (20) `Ω_H − Ω_L = −ω_A ω_B ω_C`
      have hrot' : (CV.carrierR hn hG' hS' A : ℤ) + CV.carrierR hn hG' hS' B + CV.carrierR hn hG' hS' C =
          CV.carrierR hn hG' hQi' q₀' + 1 := by exact_mod_cast hrot
      have hD : CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C = d + 4 + 2 * (Λ : ℤ) := by
        simp only [CV.slot] at hdq ⊢
        omega
      rw [hD] at h19 hqK
      rw [show d + 2 + 2 * (Λ : ℤ) - 2 = d + 2 * Λ by ring,
        show d + 2 + 2 * (Λ : ℤ) + 2 = d + 4 + 2 * Λ by ring, h19,
        hqK.coeffAt_eq_zero (by omega), hqK.coeffAt_eq_zero (by omega), hwf]
      ring
    · -- dead branch `χ = 0`: (18) `D = d + 6 + 2Λ`; every sample is below the floor
      have hrot' : (CV.carrierR hn hG' hS' A : ℤ) + CV.carrierR hn hG' hS' B + CV.carrierR hn hG' hS' C + 1 =
          CV.carrierR hn hG' hQi' q₀' := by exact_mod_cast hrot
      have hD : CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C = d + 6 + 2 * (Λ : ℤ) := by
        simp only [CV.slot] at hdq ⊢
        omega
      rw [hD] at hqK
      rw [hqK.coeffAt_eq_zero (by omega), hqK.coeffAt_eq_zero (by omega),
        hqK.coeffAt_eq_zero (by omega), hwf]
      ring
  · -- the mixed contact carrier: `W = 0` and `W_full = 0`
    have hW0 : CV.weight hG'.crossingGeometry (transportSupport hs Q) q₀' = 0 :=
      CV.weight_of_mixed _ _ q₀' huni
    rw [hsplit.mixed huni, hW0]
    ring

/-- **The `couple` field of row 177, replayed on the extended interface** (F-177-2 / D-RM-5: `hGT` is an
extra hypothesis, discharged in `w3ck_esc_ledger` by `generic_table`; body otherwise the accepted `esc_couple`). from the interface, `CarrierSlotFloor`, and the accepted data at a
common radius: (2) "`T_H(empty) - T_L(empty) = T_L(xyz)`" — the exterior factor `C_Q` is common to the
three rows (row 168: `EXT_exteriorFactor_wall`, `EXT_exteriorFactor_eq_base`), the rest is the contact
identity.  "No exterior scalar, selector, or coefficient was divided out." -/
theorem w3ck_esc_couple (hI : w3ck_esc_interface_ext_occ) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {E : CV.Event n}
    {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q - rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) =
        rowTerm hn (genericAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) := by
  intro t t' ht ht' hop hs hef heg hfg hK Q hQ hfull
  have hef₀ : e ≠ f := AV_ne_of_remote h3.1
  have hfg₀ : f ≠ g := AV_ne_of_remote h3.2.1
  have heg₀ : e ≠ g := AV_ne_of_remote h3.2.2.1
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hQi : Q ∈ CV.Ind (geomAt E t ht.1) := mem_Ind_of_mem_outsideSupports hQ
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) := mem_Ind_of_mem_outsideSupports hQ'
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hEmpty : EmptyLocal (geomAt E t' ht'.1) hef' heg' hfg' :=
    (PRE_176_graphs_complementary hL t t' ht ht' hop hef heg hfg hef' heg' hfg').mp hK
  have hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1) :=
    PRE_177_full_present_on_empty E e f g δ t' ht' hef' heg' hfg' hEmpty _ hQ' hfull'
  -- the exterior factor `C_Q` of the three rows (row 168)
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := fun x hx hxT =>
    Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  have hQ'T : ∀ x ∈ transportSupport hs Q, x.val ∉ triangleSupports e f g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hQT y hy
  rw [rowTerm_eq_exterior_mul_touching hn (genericAt E t ht.1) hQi e f g,
    rowTerm_eq_exterior_mul_touching hn (genericAt E t' ht'.1) hQi' e f g,
    rowTerm_eq_exterior_mul_touching hn (genericAt E t' ht'.1) hS' e f g,
    EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQi hQT hQi',
    ← EXT_exteriorFactor_eq_base hn (genericAt E t' ht'.1) hQ'T
      (fun x hx => (P1.mem_triangleCrossings x).mp hx) hS' hQi',
    EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQi hQT hQi', ← mul_sub]
  congr 1
  exact w3ck_esc_contact_identity hF hn hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi' hS'
    (fun q₀ q₀' hq₀ hq₀' => hI hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi'
      hS' q₀ q₀' hq₀ hq₀')

/-- **The RA ledger of row 177, replayed on the extended interface** (body the accepted `esc_ledger` with the
fourth radius of `generic_table` and `SEL_genericTableData_mono`, as `generic_transport` does). -/
theorem w3ck_esc_ledger (hI : w3ck_esc_interface_ext_occ) (hF : CV.CarrierSlotFloor) :
    RowShape @ExtremeSelectedData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  obtain ⟨δG, hδG, -, hguard⟩ := EXT_exists_guardRadius hE
  obtain ⟨δT, hδT, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  refine ⟨min δL (min δR (min δG δT)), lt_min hδL (lt_min hδR (lt_min hδG hδT)),
    (min_le_left _ _).trans hδLr, ?_⟩
  have h1 : min δL (min δR (min δG δT)) ≤ δL := min_le_left _ _
  have h2 : min δL (min δR (min δG δT)) ≤ δR := (min_le_right _ _).trans (min_le_left _ _)
  have h3' : min δL (min δR (min δG δT)) ≤ δG :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : min δL (min δR (min δG δT)) ≤ δT :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hL' := F1.localizationData_mono h1 hL
  have hR' := AV_eventRadius_mono h2 hR
  have hGT' := SEL_genericTableData_mono h4 hGT
  have hguard' : ∀ u : E.Parameter, |u.val| < min δL (min δR (min δG δT)) → EXT_GuardAt E u :=
    fun u hu => hguard u (lt_of_lt_of_le hu h3')
  exact { full_present_on_empty := PRE_177_full_present_on_empty E e f g _
          full_absent_on_complete := PRE_177_full_absent_on_complete E e f g _
          couple := w3ck_esc_couple hI hF hn hE hL' hGT' hR' hguard' }

/-- **Row 177 (R:extreme_selected) in the fixed row shape, through the record-clause chain** (W3D assembler): every
input PROVED — the OUTER data with its residue closed by units RESPAR + RESID, the value form of the site data by unit
NONKINK, the replayed ledger and `CV.carrierSlotFloor` (row 155); registered axioms only (W3D_ASSEMBLY_REPORT.md §3). -/
theorem w3ck_extreme_selected : RowShape @ExtremeSelectedData :=
  w3ck_esc_ledger w3ck_esc_interface_ext_occ_holds CV.carrierSlotFloor

end W3CK_Chain


end W3CK_KNOT


end

end SM.Link
