import SM.LocalPolynomial

/-! Source lc:single-crossing (reference/SM/sm-3-statesum.tex:1345-1352, frame SM15): a single self crossing
has scalar value one. Main declaration: `SM.single_crossing`.

Notation (namespace `SM.Link`): "an actual oriented one-circle diagram" is a `Diagram` with `D.Γ.c = 1`
(one component circle); "just one self crossing" is `∀ y : D.Γ.Crossing, y = x` for a crossing `x` (the
crossing type is a subsingleton with the inhabitant `x`; on one circle every crossing is a self
crossing); "for either crossing sign" is the absence of any hypothesis on `D.IsPositive x`; "local LM
evaluation `P_D`" is `SM.P` (SM/LocalPolynomial.lean, the Gaussian evaluation of the source value of
lp:lm); "a crossing-free one-circle diagram" is `D.IsCrossingFreeCircle`. -/

namespace SM

open SM.Link

/-! ## Helpers for the one-crossing case (sm-3:1353-1361)

"In the one-crossing case choose the nonsingular basepoint in the cyclic interval immediately before its
under occurrence. That occurrence is first; there is no other crossing." The basepoint is placed on the
edge of the under occurrence, at a parameter strictly below the under parameter and (cyclically) after the
over occurrence; the arithmetic lemma below is the resulting comparison of forward offsets. -/

/-- Forward-offset comparison on a circle of circumference `k`: from a basepoint `kb ≤ ku`, the offset to
`ku` is smaller than the offset to `ko` when `ko` lies cyclically after `ku` (either `ku < ko`, or `ko`
wrapped around before `kb`). -/
theorem singleCrossing_cyclicOffset_lt (k : ℕ) {kb ku ko : ℝ} (hbu : kb ≤ ku) (hko0 : 0 ≤ ko)
    (huk : ku < k) (h : ko < kb ∨ ku < ko) :
    Diagram.cyclicOffset k kb ku < Diagram.cyclicOffset k kb ko := by
  rw [Diagram.cyclicOffset_of_le k hbu]
  rcases h with h | h
  · rw [Diagram.cyclicOffset_of_lt k h]
    linarith
  · rw [Diagram.cyclicOffset_of_le k (by linarith)]
    linarith

/-- On a one-component diagram (all component indices equal) with a single crossing `x`, any traversal
point `p` of the component that is not the crossing point is the basepoint of some basing (identity
component order; the same label and parameter are used on every component index, of which there is only
one). -/
theorem singleCrossing_exists_basing_with_base (D : Diagram) (x : D.Γ.Crossing) (hx : ∀ y, y = x)
    (hsub : ∀ i j : Fin D.Γ.c, i = j) (i : Fin D.Γ.c) (p : TraversalPoint (D.Γ.comp i).k)
    (hp : D.Γ.eval ⟨i, p⟩ ≠ D.Γ.crossingPoint x) :
    ∃ B : D.Basing, B.base i = p := by
  have hp' : (((p.1.val : ℕ) : ZMod (D.Γ.comp i).k), p.2) = p :=
    Prod.ext (ZMod.natCast_zmod_val p.1) rfl
  refine ⟨⟨Equiv.refl _, fun j => (((p.1.val : ℕ) : ZMod (D.Γ.comp j).k), p.2), ?_⟩, ?_⟩
  · intro j y
    obtain rfl := hsub i j
    rw [hx y]
    show D.Γ.eval ⟨i, (((p.1.val : ℕ) : ZMod (D.Γ.comp i).k), p.2)⟩ ≠ D.Γ.crossingPoint x
    rw [hp']
    exact hp
  · exact hp'

/-- The one-crossing basepoint: on a one-component diagram with the single crossing `x`, given the under
traversal point `pu` (evaluating to the crossing point, with positive parameter) and the distinct over
traversal point `po` on the same component, there is a basing whose forward offset to `pu` is smaller
than its forward offset to `po`. -/
theorem singleCrossing_exists_basing_offset_lt (D : Diagram) (x : D.Γ.Crossing) (hx : ∀ y, y = x)
    (hsub : ∀ i j : Fin D.Γ.c, i = j) (i : Fin D.Γ.c) (pu po : TraversalPoint (D.Γ.comp i).k)
    (hu : D.Γ.eval ⟨i, pu⟩ = D.Γ.crossingPoint x) (hne : pu ≠ po) (hpos : 0 < pu.2.val) :
    ∃ B : D.Basing,
      Diagram.cyclicOffset (D.Γ.comp i).k (traversalKey (B.base i)) (traversalKey pu) <
        Diagram.cyclicOffset (D.Γ.comp i).k (traversalKey (B.base i)) (traversalKey po) := by
  have hku : traversalKey pu ≠ traversalKey po := fun h => hne (traversalKey_injective h)
  obtain ⟨a, tu, htu0, htu1⟩ := pu
  obtain ⟨b, tv, hto0, hto1⟩ := po
  change 0 < tu at hpos
  change (a.val : ℝ) + tu ≠ (b.val : ℝ) + tv at hku
  have hak : (a.val : ℝ) + 1 ≤ ((D.Γ.comp i).k : ℝ) := by exact_mod_cast ZMod.val_lt a
  have hedge : edge (D.Γ.comp i).P a ≠ 0 :=
    ((regular_iff_edges _).mp (D.generic.regular i) a).1
  -- any parameter strictly below the under parameter on the under edge is a nonsingular basepoint
  have step : ∀ (tb : ℝ) (h0 : 0 ≤ tb) (h1 : tb < 1), tb < tu →
      ∃ B : D.Basing, B.base i = (a, ⟨tb, h0, h1⟩) := by
    intro tb h0 h1 hlt
    apply singleCrossing_exists_basing_with_base D x hx hsub i
    intro heq
    rw [← hu] at heq
    have htt : tb = tu := edgePoint_injective hedge heq
    linarith
  have hko0 : (0 : ℝ) ≤ (b.val : ℝ) + tv := add_nonneg (Nat.cast_nonneg _) hto0
  rcases lt_or_gt_of_ne hku with hlt | hgt
  · -- the over occurrence comes later on the cut circle: any basepoint just before `tu` works
    obtain ⟨B, hB⟩ := step (tu / 2) (by linarith) (by linarith) (by linarith)
    refine ⟨B, ?_⟩
    rw [hB]
    change Diagram.cyclicOffset (D.Γ.comp i).k ((a.val : ℝ) + tu / 2) ((a.val : ℝ) + tu) <
      Diagram.cyclicOffset (D.Γ.comp i).k ((a.val : ℝ) + tu / 2) ((b.val : ℝ) + tv)
    exact singleCrossing_cyclicOffset_lt _ (by linarith) hko0 (by linarith) (Or.inr hlt)
  · -- the over occurrence comes earlier on the cut circle: put the basepoint after it, before `tu`
    have hgt' : (b.val : ℝ) + tv < (a.val : ℝ) + tu := hgt
    set m : ℝ := max 0 ((b.val : ℝ) + tv - a.val) with hm
    have hm0 : 0 ≤ m := le_max_left _ _
    have hm1 : (b.val : ℝ) + tv - a.val ≤ m := le_max_right _ _
    have hmtu : m < tu := max_lt hpos (by linarith)
    obtain ⟨B, hB⟩ := step ((m + tu) / 2) (by linarith) (by linarith) (by linarith)
    refine ⟨B, ?_⟩
    rw [hB]
    change Diagram.cyclicOffset (D.Γ.comp i).k ((a.val : ℝ) + (m + tu) / 2) ((a.val : ℝ) + tu) <
      Diagram.cyclicOffset (D.Γ.comp i).k ((a.val : ℝ) + (m + tu) / 2) ((b.val : ℝ) + tv)
    exact singleCrossing_cyclicOffset_lt _ (by linarith) hko0 (by linarith) (Or.inl (by linarith))

/-- A one-circle diagram with a single crossing is UNDER-first for a suitable basing (sm-3:1353-1357). -/
theorem singleCrossing_exists_underFirst (D : Diagram) (x : D.Γ.Crossing) (hc : D.Γ.c = 1)
    (hx : ∀ y, y = x) : ∃ B : D.Basing, D.UnderFirst B := by
  have hsub : ∀ i j : Fin D.Γ.c, i = j := fun i j => Fin.ext (by have := i.2; have := j.2; omega)
  have hmain : ∀ (u o : D.Γ.Pt), D.Γ.eval u = D.Γ.crossingPoint x → u ≠ o → 0 < u.2.2.val →
      ∃ B : D.Basing,
        Diagram.cyclicOffset (D.Γ.comp u.1).k (traversalKey (B.base u.1)) (traversalKey u.2) <
          Diagram.cyclicOffset (D.Γ.comp o.1).k (traversalKey (B.base o.1)) (traversalKey o.2) := by
    rintro ⟨i, pu⟩ ⟨j, po⟩ hu hne hpos
    obtain rfl := hsub i j
    exact singleCrossing_exists_basing_offset_lt D x hx hsub _ pu po hu
      (fun h => hne (by rw [h])) hpos
  obtain ⟨B, hB⟩ := hmain (D.visitPt (D.underVisit x)) (D.visitPt (D.overVisit x))
    (D.eval_visitPt _) (fun h => D.overVisit_ne_underVisit x (D.visitPt_injective h).symm)
    (D.visitPt_param_pos _)
  refine ⟨B, fun y => ?_⟩
  rw [hx y]
  refine Prod.lex_def.mpr (Or.inr ⟨?_, hB⟩)
  rw [Diagram.basedRank_fst, Diagram.basedRank_fst,
    hsub (D.visitPt (D.underVisit x)).1 (D.visitPt (D.overVisit x)).1]

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
    obtain ⟨B, hB⟩ := singleCrossing_exists_underFirst D x hc hx
    apply P_eq_one_of_lmF_eq_one
    rw [lmF_underFirst_init B hB]
    have hcc : D.componentCount = 1 := hc
    rw [hcc, Nat.sub_self, pow_zero]
  · intro D h
    exact P_eq_one_of_lmF_eq_one (lmF_unknot h)

end SM

#print axioms SM.single_crossing
