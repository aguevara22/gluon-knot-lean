import SM.PolynomialBlock
import SM.FrontRealizeCorrespondence

/-! Front block, lane β, unit β2 (2026-09-14): module `SM/FrontRealizeDeform.lean` (intended home).
Adopted design work/reports/front-block-design-FINAL-20260913.md (§5 item 6 "Deform of the realization",
§8 risk 3).

# The grid realization, part 6: changing the placement is a generic deformation

Two realizations of the same closed word with different placements `pl`, `pl'` are joined by the
straight-line homotopy of placements `pl_t = (1 − t) pl + t pl'`: every `pl_t` is a placement, so every
intermediate shadow is generic (`generic`), and the crossing pairs are the `σ` letters throughout
(`crossing_char`), so `DeformData (realizeAt pl …).diagram (realizeAt pl' …).diagram` holds
(`deformData`), hence `PlanarIsotopic` and `P (realizeAt pl …).diagram = P (realizeAt pl' …).diagram`
(`P_realizeAt_eq`, via the accepted `P_planar`).  The move rows realize the two sides of a move with the
factor blocks in one rectangle (non-standard placements) and transport `P` to the standard realization by
this lemma; `sCount`, `downCount`, `writhe` need no transport (they are placement-free by
`SM/FrontRealizeCorrespondence.lean`).

All declarations live in `SM.FrontRealize`.  Checked with `lake env lean` (sorry-free; `P_realizeAt_eq`
reaches `SM.lp_lm` through `P`, as every use of `P` does). -/

namespace SM.FrontRealize

open SM SM.Link SM.FrontWord

noncomputable section

/-! ## 1. The straight-line homotopy of placements -/

namespace Placement

/-- The convex combination of two placements at time `t ∈ [0, 1]`. -/
def lerp (pl pl' : Placement) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Placement where
  x k := (1 - t) * pl.x k + t * pl'.x k
  strictMono := by
    intro a b hab
    have h1 := pl.strictMono hab
    have h2 := pl'.strictMono hab
    obtain ⟨ht0, ht1⟩ := ht
    show (1 - t) * pl.x a + t * pl'.x a < (1 - t) * pl.x b + t * pl'.x b
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · subst h0; simpa using h1
    · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 h1.le), mul_pos h0 (sub_pos.2 h2)]

@[simp] theorem lerp_x (pl pl' : Placement) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (lerp pl pl' t ht).x k = (1 - t) * pl.x k + t * pl'.x k := rfl

theorem lerp_w (pl pl' : Placement) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (lerp pl pl' t ht).w k = (1 - t) * pl.w k + t * pl'.w k := by
  simp only [Placement.w, lerp_x]; ring

theorem lerp_mid (pl pl' : Placement) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (lerp pl pl' t ht).mid k = (1 - t) * pl.mid k + t * pl'.mid k := by
  simp only [Placement.mid, lerp_x, lerp_w]; ring

end Placement

/-- The point of a slot under the interpolated placement is the interpolated point. -/
theorem pt_lerp (pl pl' : Placement) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (W : Word) (s : ℕ × ℕ) :
    pt (Placement.lerp pl pl' t ht) W s = (1 - t) • pt pl W s + t • pt pl' W s := by
  unfold pt
  split_ifs
  · rw [Placement.lerp_mid]
    ext <;> simp <;> ring
  · ext <;> simp <;> ring

/-! ## 2. The vertex path and the intermediate shadows -/

section Deform

variable (pl pl' : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])

/-- The straight-line path of vertex tuples from the `pl`-realization to the `pl'`-realization. -/
def vpath (t : ℝ) : (shadowOf pl hW hne).Vertices :=
  fun i j => (1 - t) • pt pl W (toSlot hW ⟨i, j⟩).1 + t • pt pl' W (toSlot hW ⟨i, j⟩).1

theorem vpath_zero : vpath pl pl' hW hne 0 = (shadowOf pl hW hne).vertices := by
  funext i j; simp [vpath, Shadow.vertices, shadowOf]

theorem continuousOn_vpath (i : Fin (shadowOf pl hW hne).c) (j : ZMod ((shadowOf pl hW hne).comp i).k) :
    ContinuousOn (fun t => vpath pl pl' hW hne t i j) (Set.Icc 0 1) := by
  unfold vpath
  fun_prop

/-- The intermediate shadow at time `t` is the realization with the interpolated placement. -/
theorem withVertices_vpath (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (shadowOf pl hW hne).withVertices (vpath pl pl' hW hne t) = shadowOf (Placement.lerp pl pl' t ht) hW hne := by
  show Shadow.mk _ _ _ = Shadow.mk _ _ _
  congr 1
  funext i
  show PolyComp.mk _ _ _ = PolyComp.mk _ _ _
  congr 1
  funext j
  exact (pt_lerp pl pl' t ht W _).symm

theorem generic_vpath (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((shadowOf pl hW hne).withVertices (vpath pl pl' hW hne t)).Generic := by
  rw [withVertices_vpath pl pl' hW hne t ht]
  exact generic _ hW hne

/-- The crossings of a realization, placement-free: the pairs of the two strands of a `σ` letter. -/
theorem isCrossing_iff_σ (q : Placement) (x : Finset (shadowOf q hW hne).Strand) :
    (shadowOf q hW hne).IsCrossing x ↔
      ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
        x = {strandOfSlot q hW hne (σSlotA hW hk hℓ), strandOfSlot q hW hne (σSlotB hW hk hℓ)} := by
  constructor
  · intro h
    have e := crossingOfIdx_colOfCrossing q hW hne ⟨x, h⟩
    refine ⟨(colOfCrossing q hW hne ⟨x, h⟩).1, Classical.choose (σIdx_letter (colOfCrossing q hW hne ⟨x, h⟩)),
      (colOfCrossing q hW hne ⟨x, h⟩).1.2, Classical.choose_spec (σIdx_letter _), ?_⟩
    exact (congrArg Subtype.val e).symm
  · rintro ⟨k, m, hk, hℓ, rfl⟩
    exact (crossingOf q hW hne hk hℓ).2

/-- The crossing pairs are the same for every placement. -/
theorem isCrossing_placement_free (q q' : Placement) (x : Finset (shadowOf q hW hne).Strand) :
    (shadowOf q hW hne).IsCrossing x ↔ (shadowOf q' hW hne).IsCrossing x := by
  rw [isCrossing_iff_σ hW hne q x, isCrossing_iff_σ hW hne q' x]
  exact Iff.rfl

/-- The edge segments of the intermediate shadow are those of the interpolated realization. -/
theorem seg_withVertices_vpath (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (s : (shadowOf pl hW hne).Strand) :
    ((shadowOf pl hW hne).withVertices (vpath pl pl' hW hne t)).seg s = (shadowOf (Placement.lerp pl pl' t ht) hW hne).seg s := by
  show edgeSegment (vpath pl pl' hW hne t s.1) s.2 = edgeSegment _ s.2
  congr 1
  funext j
  exact (pt_lerp pl pl' t ht W _).symm

/-- The crossing pairs are constant along the path. -/
theorem crossings_vpath (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Finset (shadowOf pl hW hne).Strand) :
    ((shadowOf pl hW hne).withVertices (vpath pl pl' hW hne t)).IsCrossing x ↔ (shadowOf pl hW hne).IsCrossing x := by
  have key : ((shadowOf pl hW hne).withVertices (vpath pl pl' hW hne t)).IsCrossing x ↔
      (shadowOf (Placement.lerp pl pl' t ht) hW hne).IsCrossing x := by
    unfold Shadow.IsCrossing
    constructor
    · rintro ⟨s, s', rfl, hna, hmeet⟩
      refine ⟨s, s', rfl, hna, ?_⟩
      have h1 := seg_withVertices_vpath pl pl' hW hne t ht s
      have h2 := seg_withVertices_vpath pl pl' hW hne t ht s'
      rw [h1, h2] at hmeet; exact hmeet
    · rintro ⟨s, s', rfl, hna, hmeet⟩
      refine ⟨s, s', rfl, hna, ?_⟩
      have h1 := seg_withVertices_vpath pl pl' hW hne t ht s
      have h2 := seg_withVertices_vpath pl pl' hW hne t ht s'
      rw [h1, h2]; exact hmeet
  rw [key]
  exact isCrossing_placement_free hW hne (Placement.lerp pl pl' t ht) pl x

/-! ## 3. The deformation and the invariance of `P` -/

/-- Two diagrams with equal shadows and (heterogeneously) equal over-strand data are equal. -/
theorem _root_.SM.Link.Diagram.ext' {D₁ D₂ : Diagram} (hΓ : D₁.Γ = D₂.Γ) (hov : HEq D₁.overStrand D₂.overStrand) :
    D₁ = D₂ := by
  obtain ⟨Γ₁, g₁, o₁, m₁⟩ := D₁
  obtain ⟨Γ₂, g₂, o₂, m₂⟩ := D₂
  simp only at hΓ hov
  subst hΓ
  have := eq_of_heq hov
  subst this
  rfl

/-- Functions on subtypes of one carrier with equal predicates and equal values are heterogeneously equal. -/
theorem heq_of_subtype_fun {α β : Type*} {p q : α → Prop} (hpq : p = q) {f : Subtype p → β} {g : Subtype q → β}
    (h : ∀ x (hp : p x) (hq : q x), f ⟨x, hp⟩ = g ⟨x, hq⟩) : HEq f g := by
  subst hpq
  exact heq_of_eq (funext fun ⟨x, hx⟩ => h x hx hx)

/-- The over strand of a crossing is the same strand for every placement (the strand of `pass m (m+1)`). -/
theorem overStrand_placement_free (q q' : Placement) (x : Finset (shadowOf q hW hne).Strand)
    (h : (shadowOf q hW hne).IsCrossing x) (h' : (shadowOf q' hW hne).IsCrossing x) :
    (realizeAt q hW hne).overStrand ⟨x, h⟩ = (realizeAt q' hW hne).overStrand ⟨x, h'⟩ := by
  obtain ⟨k, m, hk, hℓ, hx⟩ := (isCrossing_iff_σ hW hne q x).1 h
  have e : (⟨x, h⟩ : (realizeAt q hW hne).Γ.Crossing) = crossingOf q hW hne hk hℓ := Subtype.ext hx
  have e' : (⟨x, h'⟩ : (realizeAt q' hW hne).Γ.Crossing) = crossingOf q' hW hne hk hℓ := Subtype.ext hx
  rw [e, e', overStrand_crossingOf, overStrand_crossingOf]
  rfl

/-- The `pl'`-realization is the deformation of the `pl`-realization along the straight-line path. -/
def deformData : DeformData (realizeAt pl hW hne).diagram (realizeAt pl' hW hne).diagram where
  γ := vpath pl pl' hW hne
  continuous := continuousOn_vpath pl pl' hW hne
  start := vpath_zero pl pl' hW hne
  generic := fun t ht => generic_vpath pl pl' hW hne t ht
  crossings := fun t ht x => crossings_vpath pl pl' hW hne t ht x
  stop := by
    have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hl : Placement.lerp pl pl' 1 ht1 = pl' := by
      cases pl'
      unfold Placement.lerp
      congr 1
      funext k; ring
    have hΓ : (realizeAt pl' hW hne).diagram.Γ =
        ((realizeAt pl hW hne).diagram.deform (vpath pl pl' hW hne 1) (generic_vpath pl pl' hW hne 1 ht1)
          (fun x => crossings_vpath pl pl' hW hne 1 ht1 x)).Γ := by
      show shadowOf pl' hW hne = (shadowOf pl hW hne).withVertices (vpath pl pl' hW hne 1)
      rw [withVertices_vpath pl pl' hW hne 1 ht1, hl]
    apply Diagram.ext' hΓ
    apply heq_of_subtype_fun
    · funext x
      apply propext
      exact (isCrossing_placement_free hW hne pl' pl x).trans (crossings_vpath pl pl' hW hne 1 ht1 x).symm
    · intro x hp hq
      exact overStrand_placement_free hW hne pl' pl x hp _

theorem deform_realizeAt : Deform (realizeAt pl hW hne).diagram (realizeAt pl' hW hne).diagram :=
  ⟨deformData pl pl' hW hne⟩

theorem planarIsotopic_realizeAt : PlanarIsotopic (realizeAt pl hW hne).diagram (realizeAt pl' hW hne).diagram :=
  PlanarIsotopic.of_deform (deform_realizeAt pl pl' hW hne)

/-- `P` does not depend on the placement. -/
theorem P_realizeAt_eq : P (realizeAt pl hW hne).diagram = P (realizeAt pl' hW hne).diagram :=
  P_planar (planarIsotopic_realizeAt pl pl' hW hne)

/-- The defect does not depend on the placement. -/
theorem defect_realizeAt_eq : (realizeAt pl hW hne).defect = (realizeAt pl' hW hne).defect := by
  unfold PLFront.defect
  rw [P_realizeAt_eq pl pl' hW hne, downCount_eq, downCount_eq, writhe_eq, writhe_eq]

end Deform

end

end SM.FrontRealize

namespace SM

open SM.FrontWord SM.FrontRealize

/-- `P` of the realization with any placement is `P` of the standard realization (nonempty words). -/
theorem P_realizeAt_eq_realize (pl : Placement) (W : OWord) (h : W.letters ≠ []) :
    P (realizeAt pl W.closed h).diagram = P (realize W).diagram := by
  rw [realize_eq_realizeAt W h]; exact P_realizeAt_eq pl _ _ _

theorem defect_realizeAt_eq_realize (pl : Placement) (W : OWord) (h : W.letters ≠ []) :
    (realizeAt pl W.closed h).defect = (realize W).defect := by
  rw [realize_eq_realizeAt W h]; exact defect_realizeAt_eq pl _ _ _

end SM
