import SM.FlatCarriers
import SM.CX1
import SM.CChamber
import SM.GermSides

/-! # thm:C-S3 (the flat law) — SKELETON FINAL

Target: `SM.thm_C_S3 : CS3Data` (work/drafts/CS3_statement.lean, copied verbatim at the end).
Source: reference/SM/sm-4-knotlaws.tex:153-229. Plan: work/drafts/cs3/PLAN_FINAL.md (route A with
grafts from route B: `regular_adjacent_meet`, the `hoff` hypothesis on the subdivision `Reparam`, the
off-edge clause bundled into `exists_appendVertex_central`, and the circle map `subdivPt` of the
subdivision stated as its own lemmas).

Every lemma of the chain is STATED (the open ones with `sorry`) and `thm_C_S3` is PROVED from the
chain; the bookkeeping lemmas are proved outright. Route (plan §1): reduce to one side parameter
`t` (chamber constancy along a side, accepted `GermSides` + `prop_C_chamber`); rewrite `C` through
lem:C-X1 as `Σ_S wind(S) ∏ c(Q)`; reindex the three sums over the centre's supports; for each
independent `S`, carriers correspond through `sideCarrierEquiv` / `deletionCarrierEquiv` (fields
`correspond_sides`, `correspond_deletion` of the accepted `FlatCarriersData`); the coefficients
agree because the slots agree (`same_retained_crossings`, `same_rotation`) and the positive lifts
are planar-isotopic to the positive diagram of the centre corner polygon — a `Deform` along the
accepted `cornerFamily` through the flat centre (side) and a `Reparam` (flat subdivision at
`μ_j`) or a cyclic re-indexing (deletion); the selector identity closes the sum
(`selector_identity`, `other_selectors_agree`). -/

namespace SM

open Link Carrier GeoCarrier

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## A. Link-layer lemmas on one-component shadows (new, general) -/

section LinkLayer

/-- `Reindexed` is transitive (compose the two shifts through `ℕ`-casts). -/
theorem Reindexed.trans {m₁ m₂ m₃ : ℕ} [NeZero m₁] [NeZero m₂] [NeZero m₃]
    {Q₁ : LabelledTuple m₁} {Q₂ : LabelledTuple m₂} {Q₃ : LabelledTuple m₃}
    (h₁ : Reindexed Q₁ Q₂) (h₂ : Reindexed Q₂ Q₃) : Reindexed Q₁ Q₃ := by
  obtain ⟨hm, r, hr⟩ := h₁
  obtain ⟨hm', r', hr'⟩ := h₂
  subst hm hm'
  refine ⟨rfl, r' + r, fun k => ?_⟩
  rw [hr' k, hr]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val, add_assoc]

/-- `Reindexed` is symmetric (shift back by `(-r).val`). -/
theorem Reindexed.symm {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂]
    {Q₁ : LabelledTuple m₁} {Q₂ : LabelledTuple m₂} (h : Reindexed Q₁ Q₂) : Reindexed Q₂ Q₁ := by
  obtain ⟨hm, r, hr⟩ := h
  subst hm
  refine ⟨rfl, (-(r : ZMod m₁)).val, fun k => ?_⟩
  rw [hr]
  congr 1
  rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]
  ring

/-- A recast is a re-indexing without shift. -/
theorem reindexed_recastTuple {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k)
    (f : LabelledTuple k) : Reindexed f (recastTuple hk f) := by
  subst hk
  exact reindexed_refl f

theorem edgeSegment_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (e : ZMod k') :
    edgeSegment (recastTuple hk f) e = edgeSegment f (Equiv.cast (congrArg ZMod hk) e) := by
  subst hk; rfl

theorem getElem_congr_lists {α : Type*} (L L' : List α) (h : L = L') (i i' : ℕ)
    (hi : i < L.length) (hi' : i' < L'.length) (hii : i = i') : L[i]'hi = L'[i']'hi' := by
  subst h; subst hii; rfl

/-! ### Polygon facts for the flat subdivision `appendVertex` (unit U1) -/

/-- **(graft from route B, L0.7a)** Consecutive edges of a regular polygon meet only at their common
vertex: independent directions by `intersection_parameters_unique` (as `Link.consecutive_meet`);
collinear same-direction edges (`edge Q (i+1) = s • edge Q i`, `s > 0`) by comparing parameters. -/
theorem regular_adjacent_meet {k : ℕ} [NeZero k] {Q : LabelledTuple k} (hQ : Regular Q)
    (i : ZMod k) {x : Plane} (hx : x ∈ edgeSegment Q i) (hx' : x ∈ edgeSegment Q (i + 1)) :
    x = Q (i + 1) := by
  sorry

/-- An old edge other than the closing one keeps its closed segment under the subdivision. -/
theorem edgeSegment_appendVertex_old {m : ℕ} [NeZero m] (X : LabelledTuple m) (u : ℝ)
    {i : ZMod m} (hi : i ≠ -1) :
    edgeSegment (appendVertex X u) (insertIndex i) = edgeSegment X i := by
  simp only [edgeSegment, edgePoint, appendVertex_old, edge_appendVertex_old X u hi]

/-- The first half-edge `[X (-1), p]` lies in the old closing edge (`edgePoint X (-1) (t·u)`). -/
theorem edgeSegment_appendVertex_last_subset {m : ℕ} [NeZero m] (X : LabelledTuple m) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    edgeSegment (appendVertex X u) (insertIndex (-1 : ZMod m)) ⊆ edgeSegment X (-1) := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  refine ⟨s * u, mul_nonneg hs0 hu0, ?_, ?_⟩
  · calc s * u ≤ 1 * 1 := mul_le_mul hs1 hu1 hu0 zero_le_one
      _ = 1 := one_mul 1
  · rw [edgePoint, edgePoint, edge_appendVertex_last, appendVertex_old, smul_smul]

/-- The second half-edge `[p, X 0]` lies in the old closing edge (`edgePoint X (-1) (u + t·(1-u))`). -/
theorem edgeSegment_appendVertex_new_subset {m : ℕ} [NeZero m] (X : LabelledTuple m) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    edgeSegment (appendVertex X u) (insertedIndex m) ⊆ edgeSegment X (-1) := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  have h1u : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  refine ⟨u + s * (1 - u), by nlinarith [mul_nonneg hs0 h1u], ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hs1 h1u]
  · rw [edgePoint, edgePoint, edge_appendVertex_new, appendVertex_new, edgePoint, smul_smul,
      add_assoc, ← add_smul]

/-- The two half-edges cover the old closing edge. -/
theorem edgeSegment_appendVertex_union {m : ℕ} [NeZero m] (X : LabelledTuple m) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    edgeSegment X (-1) =
      edgeSegment (appendVertex X u) (insertIndex (-1 : ZMod m)) ∪
        edgeSegment (appendVertex X u) (insertedIndex m) := by
  sorry

/-- The two label pairs that become non-adjacent under the subdivision do not meet: the first
half-edge `[X (-1), p]` misses the old edge `E_0` (they lie on the adjacent regular edges `E_{-1}`,
`E_0`, which meet only at `X 0 ≠ p` since `u < 1`, `regular_adjacent_meet`), and the second half-edge
`[p, X 0]` misses `E_{-2}` (meeting only at `X (-1) ≠ p` since `u > 0`). -/
theorem appendVertex_new_pairs_disjoint {m : ℕ} [NeZero m] (hm : 3 ≤ m) {X : LabelledTuple m}
    (hX : Regular X) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ x, x ∈ edgeSegment (appendVertex X u) (insertIndex (-1 : ZMod m)) →
      x ∉ edgeSegment (appendVertex X u) (insertIndex (0 : ZMod m))) ∧
    (∀ x, x ∈ edgeSegment (appendVertex X u) (insertedIndex m) →
      x ∉ edgeSegment (appendVertex X u) (insertIndex (-2 : ZMod m))) := by
  sorry

namespace Link

/-- A cyclic shift of the labels keeps a one-component shadow generic
(`StrandMap.generic_pullback` along the accepted `shiftStrandMap`). -/
theorem single_generic_shift {k : ℕ} (hk : 3 ≤ k) (X : LabelledTuple k) (r : ZMod k)
    (h : (Shadow.single ⟨k, hk, X⟩).Generic) : (Shadow.single ⟨k, hk, shift r X⟩).Generic := by
  have : NeZero k := ⟨by omega⟩
  exact StrandMap.generic_pullback (shiftStrandMap ⟨k, hk, X⟩ r) h
    (fun _ => (regular_shift r X).mpr (h.regular 0))

/-- Genericity of a one-component shadow is invariant under re-indexing. -/
theorem single_generic_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m'] {X : LabelledTuple m}
    {Y : LabelledTuple m'} (h : Reindexed X Y) (hm : 3 ≤ m) (hm' : 3 ≤ m')
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic) : (Shadow.single ⟨m', hm', Y⟩).Generic := by
  obtain ⟨hmm, -⟩ := id h
  subst hmm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  exact single_generic_shift hm X r hX

/-- Re-indexed one-component positive diagrams have the same HOMFLY polynomial
(`reparam_positiveDiagram_single_shift`, `homfly_planar`). -/
theorem homfly_positiveDiagram_single_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m']
    {X : LabelledTuple m} {Y : LabelledTuple m'} (h : Reindexed X Y) (hm : 3 ≤ m) (hm' : 3 ≤ m')
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic) (hY : (Shadow.single ⟨m', hm', Y⟩).Generic) :
    homfly ((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX) =
      homfly ((Shadow.single ⟨m', hm', Y⟩).positiveDiagram hY) := by
  obtain ⟨hmm, -⟩ := id h
  subst hmm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  exact homfly_planar (PlanarIsotopic.of_reparam
    (reparam_positiveDiagram_single_shift ⟨m, hm, X⟩ r hX hY))

/-- **Deform along a continuous family of generic one-component shadows** (the general form of
`deform_positiveLift_path`): the crossing pairs are constant (`crossing_support_persists_of_geometry`
+ `crossingGeometry_of_single_generic`, locally constant on the connected `unitInterval`),
`Deform.of_family`, positivity persists (`isPositive_deform_of_family`), and the deformed diagram
is the positive diagram (`eq_positiveDiagram_of_isPositive`). -/
theorem deform_positiveDiagram_single_of_family {k : ℕ} (hk : 3 ≤ k)
    (Φ : unitInterval → LabelledTuple k) (hΦ : Continuous Φ)
    (hgen : ∀ u, (Shadow.single ⟨k, hk, Φ u⟩).Generic) :
    Deform ((Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0))
      ((Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1)) := by
  have : NeZero k := ⟨by omega⟩
  let D : Diagram := (Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0)
  let V : unitInterval → D.Γ.Vertices := fun u _ => Φ u
  have hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun u => V u i j :=
    fun _ j => (continuous_apply j).comp hΦ
  have hgen' : ∀ u, (D.Γ.withVertices (V u)).Generic := fun u => hgen u
  have hcross : ∀ u (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V u)).IsCrossing x ↔ D.Γ.IsCrossing x := by
    intro u x
    have hg : IsLocallyConstant fun u : unitInterval => {s : Finset (ZMod k) | IsCrossing (Φ u) s} := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro u₀
      have hev := crossing_support_persists_of_geometry
        (crossingGeometry_of_single_generic hk (hgen u₀))
      filter_upwards [hΦ.continuousAt.eventually hev] with u' hu'
      exact Set.ext hu'
    have hconst := Set.ext_iff.mp (IsLocallyConstant.apply_eq_of_preconnectedSpace hg u 0)
    exact single_isCrossing_iff_of_forall hk (fun s => hconst s) x
  have h0 : V 0 = D.Γ.vertices := rfl
  have hd : Deform D (D.deform (V 1) (hgen' 1) (hcross 1)) := Deform.of_family D hV hgen' hcross h0
  have heq : D.deform (V 1) (hgen' 1) (hcross 1) =
      (Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1) :=
    Shadow.eq_positiveDiagram_of_isPositive _ (hgen 1) _ rfl
      (D.isPositive_deform_of_family hV hgen' hcross h0
        (fun x => Shadow.positiveDiagram_isPositive _ _ x))
  rw [← heq]
  exact hd

theorem homfly_positiveDiagram_single_of_family {k : ℕ} (hk : 3 ≤ k)
    (Φ : unitInterval → LabelledTuple k) (hΦ : Continuous Φ)
    (hgen : ∀ u, (Shadow.single ⟨k, hk, Φ u⟩).Generic) :
    homfly ((Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0)) =
      homfly ((Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1)) :=
  homfly_planar (PlanarIsotopic.of_deform (deform_positiveDiagram_single_of_family hk Φ hΦ hgen))

/-- **Flat subdivision keeps genericity** (unit U1). Appending the vertex `p = edgePoint X (-1) u`,
`0 < u < 1`, on the closing edge of a generic one-component shadow keeps it generic provided `p` lies
on no other closed edge. Proof through `Shadow.single_generic_of` in label form, labels by
`insertion_indices_exhaust` (`insertIndex i`, `i ≠ -1`: the old edge, `edgeSegment_appendVertex_old`;
`insertIndex (-1)`: `[X (-1), p]`, direction `u • edge X (-1)`, `edge_appendVertex_last`;
`insertedIndex m`: `[p, X 0]`, direction `(1-u) • edge X (-1)`, `edge_appendVertex_new`).
`regular`: `regular_appendVertex`. `tail_off`: an old vertex on a half-edge is on the old closing
edge (`edgeSegment_appendVertex_last/new_subset`), excluded by `hX.tail_off` unless incident, and
then by parameter comparison (`edgePoint_injective` on the nonzero edge); the new vertex `p` on an old
edge is excluded by `hoff`. `transverse`: two old edges as in `X` (adjacency in `ZMod (m+1)` agrees
with `ZMod m` off `-1`); a half-edge against an old edge `i` reduces to the pair `(-1, i)` of `X`
(directions are positive multiples) unless `i ∈ {0, -2}`, where the pair does not meet
(`appendVertex_new_pairs_disjoint`). `no_triple`: map to `X`; the interiors of the two half-edges are
disjoint. -/
theorem single_generic_appendVertex {m : ℕ} [NeZero m] (hm : 3 ≤ m) (X : LabelledTuple m)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hoff : ∀ e : ZMod m, e ≠ -1 → edgePoint X (-1) u ∉ edgeSegment X e) :
    (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic := by
  sorry

/-! ### The circle map of the flat subdivision (unit U2) -/

/-- The re-parametrization of the traversal circle under the flat subdivision: a traversal point
`(i, s)` of `X` is read on `appendVertex X u` as `(insertIndex i, s)` for `i ≠ -1`; on the closing
edge as `(insertIndex (-1), s / u)` for `s < u` and as `(insertedIndex m, (s - u) / (1 - u))` for
`s ≥ u`. -/
def subdivPt {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (p : TraversalPoint m) :
    TraversalPoint (m + 1) :=
  if p.1 = -1 then
    if h : p.2.val < u then
      (insertIndex (-1 : ZMod m),
        ⟨p.2.val / u, div_nonneg p.2.property.1 hu0.le, (div_lt_one hu0).mpr h⟩)
    else
      (insertedIndex m,
        ⟨(p.2.val - u) / (1 - u), div_nonneg (sub_nonneg.mpr (not_lt.mp h)) (sub_pos.mpr hu1).le,
          (div_lt_one (sub_pos.mpr hu1)).mpr (by linarith [p.2.property.2])⟩)
  else (insertIndex p.1, p.2)

/-! #### Case lemmas for `subdivPt` (unit U2 helpers) -/

theorem subdivPt_trichotomy {u : ℝ} (p : TraversalPoint m) :
    p.1 ≠ -1 ∨ (p.1 = -1 ∧ p.2.val < u) ∨ (p.1 = -1 ∧ u ≤ p.2.val) := by
  by_cases hp : p.1 = -1
  · by_cases hs : p.2.val < u
    · exact Or.inr (Or.inl ⟨hp, hs⟩)
    · exact Or.inr (Or.inr ⟨hp, not_lt.mp hs⟩)
  · exact Or.inl hp

theorem subdivPt_fst_of_ne {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {p : TraversalPoint m} (hp : p.1 ≠ -1) :
    (subdivPt hu0 hu1 p).1 = insertIndex p.1 := by
  simp only [subdivPt, ite_eq_right hp]

theorem subdivPt_snd_of_ne {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {p : TraversalPoint m} (hp : p.1 ≠ -1) :
    (subdivPt hu0 hu1 p).2 = p.2 := by
  simp only [subdivPt, ite_eq_right hp]

theorem subdivPt_fst_of_lt {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {p : TraversalPoint m} (hp : p.1 = -1) (hs : p.2.val < u) :
    (subdivPt hu0 hu1 p).1 = insertIndex (-1 : ZMod m) := by
  simp only [subdivPt, ite_eq_left hp, dite_eq_left hs]

theorem subdivPt_snd_of_lt {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {p : TraversalPoint m} (hp : p.1 = -1) (hs : p.2.val < u) :
    (subdivPt hu0 hu1 p).2.val = p.2.val / u := by
  simp only [subdivPt, ite_eq_left hp, dite_eq_left hs]

theorem subdivPt_fst_of_ge {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {p : TraversalPoint m} (hp : p.1 = -1) (hs : u ≤ p.2.val) :
    (subdivPt hu0 hu1 p).1 = insertedIndex m := by
  simp only [subdivPt, ite_eq_left hp, dite_eq_right (not_lt.mpr hs)]

theorem subdivPt_snd_of_ge {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {p : TraversalPoint m} (hp : p.1 = -1) (hs : u ≤ p.2.val) :
    (subdivPt hu0 hu1 p).2.val = (p.2.val - u) / (1 - u) := by
  simp only [subdivPt, ite_eq_left hp, dite_eq_right (not_lt.mpr hs)]

/-- A label other than `-1` has value at most `m - 2`. -/
theorem val_add_one_lt_of_ne_neg_one {m : ℕ} [NeZero m] {i : ZMod m} (hi : i ≠ -1) :
    i.val + 1 < m := by
  have hlt := i.val_lt
  by_contra h
  apply hi
  apply ZMod.val_injective m
  rw [zmod_val_neg_one]
  omega

/-- `subdivPt` is a bijection of the traversal circles (inverse: `(insertedIndex m, s) ↦
(-1, u + (1-u)·s)`, `(insertIndex (-1), s) ↦ (-1, u·s)`, `(insertIndex i, s) ↦ (i, s)`). -/
theorem subdivPt_bijective {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Function.Bijective (subdivPt (m := m) hu0 hu1) := by
  constructor
  · intro p q h
    rcases subdivPt_trichotomy (u := u) p with hp | ⟨hp, hpu⟩ | ⟨hp, hpu⟩ <;>
    rcases subdivPt_trichotomy (u := u) q with hq | ⟨hq, hqu⟩ | ⟨hq, hqu⟩
    · have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      rw [subdivPt_fst_of_ne hu0 hu1 hp, subdivPt_fst_of_ne hu0 hu1 hq] at h1
      rw [subdivPt_snd_of_ne hu0 hu1 hp, subdivPt_snd_of_ne hu0 hu1 hq] at h2
      exact Prod.ext (insertIndex_injective h1) h2
    · have h1 := congrArg Prod.fst h
      rw [subdivPt_fst_of_ne hu0 hu1 hp, subdivPt_fst_of_lt hu0 hu1 hq hqu] at h1
      exact absurd (insertIndex_injective h1) hp
    · have h1 := congrArg Prod.fst h
      rw [subdivPt_fst_of_ne hu0 hu1 hp, subdivPt_fst_of_ge hu0 hu1 hq hqu] at h1
      exact absurd h1 (insertIndex_ne_inserted _)
    · have h1 := congrArg Prod.fst h
      rw [subdivPt_fst_of_lt hu0 hu1 hp hpu, subdivPt_fst_of_ne hu0 hu1 hq] at h1
      exact absurd (insertIndex_injective h1).symm hq
    · have h2 : (subdivPt hu0 hu1 p).2.val = (subdivPt hu0 hu1 q).2.val :=
        congrArg (fun r : TraversalPoint (m + 1) => r.2.val) h
      rw [subdivPt_snd_of_lt hu0 hu1 hp hpu, subdivPt_snd_of_lt hu0 hu1 hq hqu] at h2
      exact Prod.ext (hp.trans hq.symm) (Subtype.ext ((div_left_inj' hu0.ne').mp h2))
    · have h1 := congrArg Prod.fst h
      rw [subdivPt_fst_of_lt hu0 hu1 hp hpu, subdivPt_fst_of_ge hu0 hu1 hq hqu] at h1
      exact absurd h1 (insertIndex_ne_inserted _)
    · have h1 := congrArg Prod.fst h
      rw [subdivPt_fst_of_ge hu0 hu1 hp hpu, subdivPt_fst_of_ne hu0 hu1 hq] at h1
      exact absurd h1.symm (insertIndex_ne_inserted _)
    · have h1 := congrArg Prod.fst h
      rw [subdivPt_fst_of_ge hu0 hu1 hp hpu, subdivPt_fst_of_lt hu0 hu1 hq hqu] at h1
      exact absurd h1.symm (insertIndex_ne_inserted _)
    · have h2 : (subdivPt hu0 hu1 p).2.val = (subdivPt hu0 hu1 q).2.val :=
        congrArg (fun r : TraversalPoint (m + 1) => r.2.val) h
      rw [subdivPt_snd_of_ge hu0 hu1 hp hpu, subdivPt_snd_of_ge hu0 hu1 hq hqu] at h2
      have h3 := (div_left_inj' (sub_pos.mpr hu1).ne').mp h2
      exact Prod.ext (hp.trans hq.symm) (Subtype.ext (sub_left_inj.mp h3))
  · intro r
    have hr0 := r.2.property.1
    have hr1 := r.2.property.2
    have h1u : 0 < 1 - u := sub_pos.mpr hu1
    rcases insertion_indices_exhaust r.1 with hr | ⟨i, hi⟩
    · refine ⟨(-1, ⟨u + (1 - u) * r.2.val, by nlinarith, by nlinarith⟩), ?_⟩
      have hge : u ≤ u + (1 - u) * r.2.val := by nlinarith
      refine Prod.ext ?_ (Subtype.ext ?_)
      · rw [subdivPt_fst_of_ge hu0 hu1 rfl hge]
        exact hr.symm
      · rw [subdivPt_snd_of_ge hu0 hu1 rfl hge]
        field_simp
        ring
    · by_cases hi1 : i = -1
      · subst hi1
        refine ⟨(-1, ⟨u * r.2.val, by nlinarith, by nlinarith⟩), ?_⟩
        have hlt : u * r.2.val < u := by nlinarith
        refine Prod.ext ?_ (Subtype.ext ?_)
        · rw [subdivPt_fst_of_lt hu0 hu1 rfl hlt]
          exact hi.symm
        · rw [subdivPt_snd_of_lt hu0 hu1 rfl hlt]
          field_simp
      · refine ⟨(i, r.2), ?_⟩
        refine Prod.ext ?_ ?_
        · rw [subdivPt_fst_of_ne hu0 hu1 hi1]
          exact hi.symm
        · rw [subdivPt_snd_of_ne hu0 hu1 hi1]

/-- The piecewise-affine map of traversal keys induced by the flat subdivision: identity below
`m - 1`, the closing-edge key `m - 1 + s` is sent to `m - 1 + s/u` for `s < u` and to
`m + (s - u)/(1 - u)` for `s ≥ u`. -/
def subdivKeyMap (m : ℕ) (u : ℝ) (x : ℝ) : ℝ :=
  if x < (m : ℝ) - 1 then x
  else if x < (m : ℝ) - 1 + u then (m : ℝ) - 1 + (x - ((m : ℝ) - 1)) / u
  else (m : ℝ) + (x - ((m : ℝ) - 1) - u) / (1 - u)

theorem subdivKeyMap_strictMono (m : ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    StrictMono (subdivKeyMap m u) := by
  intro a b hab
  have h1u : 0 < 1 - u := sub_pos.mpr hu1
  unfold subdivKeyMap
  by_cases ha1 : a < (m : ℝ) - 1
  · rw [ite_eq_left ha1]
    by_cases hb1 : b < (m : ℝ) - 1
    · rw [ite_eq_left hb1]
      exact hab
    · rw [ite_eq_right hb1]
      by_cases hb2 : b < (m : ℝ) - 1 + u
      · rw [ite_eq_left hb2]
        have : 0 ≤ (b - ((m : ℝ) - 1)) / u := div_nonneg (by linarith) hu0.le
        linarith
      · rw [ite_eq_right hb2]
        have : 0 ≤ (b - ((m : ℝ) - 1) - u) / (1 - u) := div_nonneg (by linarith) h1u.le
        linarith
  · rw [ite_eq_right ha1]
    have hb1 : ¬ b < (m : ℝ) - 1 := fun h => ha1 (hab.trans h)
    rw [ite_eq_right hb1]
    by_cases ha2 : a < (m : ℝ) - 1 + u
    · rw [ite_eq_left ha2]
      by_cases hb2 : b < (m : ℝ) - 1 + u
      · rw [ite_eq_left hb2]
        have := (div_lt_div_iff_of_pos_right hu0).mpr (sub_lt_sub_right hab ((m : ℝ) - 1))
        linarith
      · rw [ite_eq_right hb2]
        have h3 : (a - ((m : ℝ) - 1)) / u < 1 := (div_lt_one hu0).mpr (by linarith)
        have h4 : 0 ≤ (b - ((m : ℝ) - 1) - u) / (1 - u) := div_nonneg (by linarith) h1u.le
        linarith
    · rw [ite_eq_right ha2]
      have hb2 : ¬ b < (m : ℝ) - 1 + u := fun h => ha2 (hab.trans h)
      rw [ite_eq_right hb2]
      have := (div_lt_div_iff_of_pos_right h1u).mpr
        (sub_lt_sub_right (sub_lt_sub_right hab ((m : ℝ) - 1)) u)
      linarith

/-- The traversal key of `subdivPt p` is the key map applied to the key of `p`. -/
theorem traversalKey_subdivPt {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (p : TraversalPoint m) :
    traversalKey (subdivPt hu0 hu1 p) = subdivKeyMap m u (traversalKey p) := by
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := Nat.cast_pred (NeZero.pos m)
  have hp0 := p.2.property.1
  have hp1 := p.2.property.2
  rcases subdivPt_trichotomy (u := u) p with hp | ⟨hp, hpu⟩ | ⟨hp, hpu⟩
  · have hv : p.1.val + 1 < m := val_add_one_lt_of_ne_neg_one hp
    have hv2 : p.1.val + 2 ≤ m := by omega
    have hv' : (p.1.val : ℝ) + 2 ≤ m := by exact_mod_cast hv2
    have hlt : traversalKey p < (m : ℝ) - 1 := by
      unfold traversalKey
      linarith
    rw [subdivKeyMap, ite_eq_left hlt]
    unfold traversalKey
    rw [subdivPt_fst_of_ne hu0 hu1 hp, subdivPt_snd_of_ne hu0 hu1 hp, insertIndex_val]
  · have hkey : traversalKey p = (m : ℝ) - 1 + p.2.val := by
      unfold traversalKey
      rw [hp, zmod_val_neg_one, hm1]
    have h1 : ¬ traversalKey p < (m : ℝ) - 1 := by rw [hkey]; linarith
    have h2 : traversalKey p < (m : ℝ) - 1 + u := by rw [hkey]; linarith
    rw [subdivKeyMap, ite_eq_right h1, ite_eq_left h2, hkey]
    unfold traversalKey
    rw [subdivPt_fst_of_lt hu0 hu1 hp hpu, subdivPt_snd_of_lt hu0 hu1 hp hpu, insertIndex_val,
      zmod_val_neg_one, hm1]
    ring
  · have hkey : traversalKey p = (m : ℝ) - 1 + p.2.val := by
      unfold traversalKey
      rw [hp, zmod_val_neg_one, hm1]
    have h1 : ¬ traversalKey p < (m : ℝ) - 1 := by rw [hkey]; linarith
    have h2 : ¬ traversalKey p < (m : ℝ) - 1 + u := by rw [hkey]; linarith
    rw [subdivKeyMap, ite_eq_right h1, ite_eq_right h2, hkey]
    unfold traversalKey
    rw [subdivPt_fst_of_ge hu0 hu1 hp hpu, subdivPt_snd_of_ge hu0 hu1 hp hpu, insertedIndex_val]
    ring

/-- `subdivPt` is strictly increasing for the traversal keys (`traversalKey = label.val + s`:
`insertIndex i` has value `i.val`; on the closing edge the key `m - 1 + s`, `s ∈ [0,1)`, becomes
`m - 1 + s/u` on `[0,u)` and `m + (s-u)/(1-u)` on `[u,1)`, both increasing and glued monotonically). -/
theorem traversalKey_subdivPt_lt_iff {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (p q : TraversalPoint m) :
    traversalKey (subdivPt hu0 hu1 p) < traversalKey (subdivPt hu0 hu1 q) ↔
      traversalKey p < traversalKey q := by
  rw [traversalKey_subdivPt hu0 hu1 p, traversalKey_subdivPt hu0 hu1 q]
  exact (subdivKeyMap_strictMono m hu0 hu1).lt_iff_lt

/-- `subdivPt` traces the same plane points (`edge_appendVertex_last/new`, `appendVertex_old/new`:
`X (-1) + (s/u) • (u • E) = X (-1) + s • E`, `p + ((s-u)/(1-u)) • ((1-u) • E) = X (-1) + s • E`). -/
theorem traversalEvaluation_subdivPt {m : ℕ} [NeZero m] (X : LabelledTuple m) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (p : TraversalPoint m) :
    traversalEvaluation (appendVertex X u) (subdivPt hu0 hu1 p) = traversalEvaluation X p := by
  unfold subdivPt traversalEvaluation
  split_ifs with h1 h2
  · dsimp only
    rw [h1, edgePoint, edgePoint, edge_appendVertex_last, appendVertex_old, smul_smul,
      div_mul_cancel₀ _ hu0.ne']
  · dsimp only
    have hsc : u + (p.2.val - u) = p.2.val := by ring
    rw [h1, edgePoint, edgePoint, edge_appendVertex_new, appendVertex_new, edgePoint, smul_smul,
      div_mul_cancel₀ _ (sub_pos.mpr hu1).ne', add_assoc, ← add_smul, hsc]
  · dsimp only
    rw [edgePoint, edgePoint, appendVertex_old, edge_appendVertex_old X u h1]

/-- The strict cyclic order is preserved (all three disjuncts of `traversalBetween` are key
comparisons, `traversalKey_subdivPt_lt_iff`). -/
theorem traversalBetween_subdivPt {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (p q r : TraversalPoint m) (h : traversalBetween p q r) :
    traversalBetween (subdivPt hu0 hu1 p) (subdivPt hu0 hu1 q) (subdivPt hu0 hu1 r) := by
  unfold traversalBetween at h ⊢
  simp only [traversalKey_subdivPt_lt_iff]
  exact h

/-! #### Labels under the subdivision: remoteness both ways (unit U2 helpers) -/

theorem neg_one_ne_zero_of_three_le {m : ℕ} [NeZero m] (hm : 3 ≤ m) : (-1 : ZMod m) ≠ 0 := by
  intro h
  have h' := congrArg ZMod.val h
  rw [zmod_val_neg_one, ZMod.val_zero] at h'
  omega

/-- Off the closing edge, `insertIndex` preserves remoteness. -/
theorem remote_insertIndex_of_remote {m : ℕ} [NeZero m] {i j : ZMod m} (hi : i ≠ -1)
    (_hj : j ≠ -1) (h : remote i j) : remote (insertIndex i) (insertIndex j) := by
  rintro (h1 | h1 | h1) <;> apply h
  · have h2 : insertIndex j = insertIndex i - 1 := by linear_combination h1
    by_cases hi0 : i = 0
    · subst hi0
      rw [insertIndex_zero_prev] at h2
      exact absurd h2 (insertIndex_ne_inserted j)
    · rw [insertIndex_prev hi0] at h2
      left
      rw [insertIndex_injective h2]
      ring
  · right; left
    rw [insertIndex_injective (sub_eq_zero.mp h1), sub_self]
  · have h2 : insertIndex j = insertIndex i + 1 := by linear_combination h1
    rw [← insertIndex_next hi] at h2
    right; right
    rw [insertIndex_injective h2]
    ring

/-- The first half-edge `insertIndex (-1)` is remote from every old edge remote from `-1`. -/
theorem remote_insertIndex_last_of_remote {m : ℕ} [NeZero m] (hm : 3 ≤ m) {j : ZMod m}
    (hj : j ≠ -1) (h : remote (-1) j) : remote (insertIndex (-1 : ZMod m)) (insertIndex j) := by
  rintro (h1 | h1 | h1) <;> apply h
  · have h2 : insertIndex j = insertIndex (-1 : ZMod m) - 1 := by linear_combination h1
    rw [insertIndex_prev (neg_one_ne_zero_of_three_le hm)] at h2
    left
    rw [insertIndex_injective h2]
    ring
  · exact absurd (insertIndex_injective (sub_eq_zero.mp h1)) hj
  · have h2 : insertIndex j = insertIndex (-1 : ZMod m) + 1 := by linear_combination h1
    rw [insertIndex_last_add_one] at h2
    exact absurd h2 (insertIndex_ne_inserted j)

/-- The second half-edge `insertedIndex m` is remote from every old edge remote from `-1`. -/
theorem remote_insertedIndex_of_remote {m : ℕ} [NeZero m] {j : ZMod m} (hj : j ≠ -1)
    (h : remote (-1) j) : remote (insertedIndex m) (insertIndex j) := by
  rintro (h1 | h1 | h1) <;> apply h
  · have h2 : insertIndex j = insertedIndex m - 1 := by linear_combination h1
    rw [insertedIndex_prev] at h2
    exact absurd (insertIndex_injective h2) hj
  · exact absurd (sub_eq_zero.mp h1) (insertIndex_ne_inserted j)
  · have h2 : insertIndex j = insertedIndex m + 1 := by linear_combination h1
    rw [insertedIndex_add_one, ← insertIndex_zero] at h2
    right; right
    rw [insertIndex_injective h2]
    ring

/-- Remote labels stay remote under the subdivision. -/
theorem remote_subdivPt_fst {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hm : 3 ≤ m)
    {p q : TraversalPoint m} (hr : remote p.1 q.1) :
    remote (subdivPt hu0 hu1 p).1 (subdivPt hu0 hu1 q).1 := by
  rcases subdivPt_trichotomy (u := u) p with hp | ⟨hp, hpu⟩ | ⟨hp, hpu⟩ <;>
  rcases subdivPt_trichotomy (u := u) q with hq | ⟨hq, hqu⟩ | ⟨hq, hqu⟩
  · rw [subdivPt_fst_of_ne hu0 hu1 hp, subdivPt_fst_of_ne hu0 hu1 hq]
    exact remote_insertIndex_of_remote hp hq hr
  · rw [subdivPt_fst_of_ne hu0 hu1 hp, subdivPt_fst_of_lt hu0 hu1 hq hqu]
    rw [hq] at hr
    exact remote_symm (remote_insertIndex_last_of_remote hm hp (remote_symm hr))
  · rw [subdivPt_fst_of_ne hu0 hu1 hp, subdivPt_fst_of_ge hu0 hu1 hq hqu]
    rw [hq] at hr
    exact remote_symm (remote_insertedIndex_of_remote hp (remote_symm hr))
  · rw [subdivPt_fst_of_lt hu0 hu1 hp hpu, subdivPt_fst_of_ne hu0 hu1 hq]
    rw [hp] at hr
    exact remote_insertIndex_last_of_remote hm hq hr
  · exact absurd (adjacent_of_eq (hp.trans hq.symm)) hr
  · exact absurd (adjacent_of_eq (hp.trans hq.symm)) hr
  · rw [subdivPt_fst_of_ge hu0 hu1 hp hpu, subdivPt_fst_of_ne hu0 hu1 hq]
    rw [hp] at hr
    exact remote_insertedIndex_of_remote hq hr
  · exact absurd (adjacent_of_eq (hp.trans hq.symm)) hr
  · exact absurd (adjacent_of_eq (hp.trans hq.symm)) hr

/-- Two traversal points on the same old edge land on adjacent (possibly equal) new edges. -/
theorem adjacent_subdivPt_fst_of_eq {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {p q : TraversalPoint m} (h : p.1 = q.1) :
    adjacent (subdivPt hu0 hu1 p).1 (subdivPt hu0 hu1 q).1 := by
  rcases subdivPt_trichotomy (u := u) p with hp | ⟨hp, hpu⟩ | ⟨hp, hpu⟩ <;>
  rcases subdivPt_trichotomy (u := u) q with hq | ⟨hq, hqu⟩ | ⟨hq, hqu⟩
  · rw [subdivPt_fst_of_ne hu0 hu1 hp, subdivPt_fst_of_ne hu0 hu1 hq, h]
    exact adjacent_of_eq rfl
  · exact absurd (h.trans hq) hp
  · exact absurd (h.trans hq) hp
  · exact absurd (h.symm.trans hp) hq
  · rw [subdivPt_fst_of_lt hu0 hu1 hp hpu, subdivPt_fst_of_lt hu0 hu1 hq hqu]
    exact adjacent_of_eq rfl
  · rw [subdivPt_fst_of_lt hu0 hu1 hp hpu, subdivPt_fst_of_ge hu0 hu1 hq hqu]
    exact adjacent_of_add_one_eq insertIndex_last_add_one
  · exact absurd (h.symm.trans hp) hq
  · rw [subdivPt_fst_of_ge hu0 hu1 hp hpu, subdivPt_fst_of_lt hu0 hu1 hq hqu]
    exact adjacent_of_eq_add_one insertIndex_last_add_one.symm
  · rw [subdivPt_fst_of_ge hu0 hu1 hp hpu, subdivPt_fst_of_ge hu0 hu1 hq hqu]
    exact adjacent_of_eq rfl

/-- Two traversal points of `X` tracing an old vertex `X c` are read on adjacent new edges: the
vertex `X c = appendVertex X u (insertIndex c)` lies on both new closed edges, so by `tail_off` of
the subdivided shadow both are incident to it. -/
theorem not_remote_subdivPt_of_vertex {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hm : 3 ≤ m) (X : LabelledTuple m)
    (hX' : (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic)
    {p q : TraversalPoint m} (c : ZMod m) (hzp : traversalEvaluation X p = X c)
    (hzq : traversalEvaluation X q = X c) :
    ¬ remote (subdivPt hu0 hu1 p).1 (subdivPt hu0 hu1 q).1 := by
  intro hr
  have hinc : ∀ r : TraversalPoint m, traversalEvaluation X r = X c →
      incident (insertIndex c) (subdivPt hu0 hu1 r).1 := by
    intro r hr'
    by_contra hn
    refine hX'.tail_off ⟨0, insertIndex c⟩ ⟨0, (subdivPt hu0 hu1 r).1⟩
      (fun h => hn ((Shadow.single_incidentTail_iff _ _ _).mp h)) ?_
    show appendVertex X u (insertIndex c) ∈ edgeSegment (appendVertex X u) (subdivPt hu0 hu1 r).1
    rw [appendVertex_old, ← hr', ← traversalEvaluation_subdivPt X hu0 hu1 r]
    exact ⟨(subdivPt hu0 hu1 r).2.val, (subdivPt hu0 hu1 r).2.property.1,
      (subdivPt hu0 hu1 r).2.property.2.le, rfl⟩
  apply hr
  rcases hinc p hzp with hp | hp <;> rcases hinc q hzq with hq | hq <;> rw [hp, hq]
  · exact adjacent_of_eq rfl
  · exact adjacent_of_add_one_eq (sub_add_cancel _ _)
  · exact adjacent_of_eq_add_one (sub_add_cancel _ _).symm
  · exact adjacent_of_eq rfl

/-- Remoteness descends along the subdivision for two traversal points tracing the same plane
point: adjacent old labels either coincide (then the new labels are adjacent,
`adjacent_subdivPt_fst_of_eq`) or are consecutive, and consecutive regular edges meet only at
their common vertex (`regular_adjacent_meet`), where the new labels are adjacent by `tail_off`
(`not_remote_subdivPt_of_vertex`). -/
theorem remote_of_remote_subdivPt {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hm : 3 ≤ m) (X : LabelledTuple m) (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hX' : (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic)
    {p q : TraversalPoint m} (hz : traversalEvaluation X p = traversalEvaluation X q)
    (hr : remote (subdivPt hu0 hu1 p).1 (subdivPt hu0 hu1 q).1) : remote p.1 q.1 := by
  have hreg : Regular X := hX.regular 0
  have hmp : traversalEvaluation X p ∈ edgeSegment X p.1 :=
    ⟨p.2.val, p.2.property.1, p.2.property.2.le, rfl⟩
  have hmq : traversalEvaluation X p ∈ edgeSegment X q.1 :=
    ⟨q.2.val, q.2.property.1, q.2.property.2.le, hz⟩
  rintro (h | h | h)
  · have hpq : p.1 = q.1 + 1 := by linear_combination -h
    rw [hpq] at hmp
    have hv := regular_adjacent_meet hreg q.1 hmq hmp
    exact not_remote_subdivPt_of_vertex hu0 hu1 hm X hX' (q.1 + 1) hv
      (by rw [← hz]; exact hv) hr
  · exact hr (adjacent_subdivPt_fst_of_eq hu0 hu1 (sub_eq_zero.mp h).symm)
  · have hpq : q.1 = p.1 + 1 := by linear_combination h
    rw [hpq] at hmq
    have hv := regular_adjacent_meet hreg p.1 hmp hmq
    exact not_remote_subdivPt_of_vertex hu0 hu1 hm X hX' (p.1 + 1) hv
      (by rw [← hz]; exact hv) hr

/-! #### Edge directions under the subdivision -/

theorem det_smul_smul_plane (c d : ℝ) (v w : Plane) : det (c • v) (d • w) = (c * d) * det v w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The new edge read at `subdivPt p` is a positive multiple of the old edge at `p`. -/
theorem edge_appendVertex_subdivPt_fst {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (X : LabelledTuple m) (p : TraversalPoint m) :
    ∃ c : ℝ, 0 < c ∧ edge (appendVertex X u) (subdivPt hu0 hu1 p).1 = c • edge X p.1 := by
  rcases subdivPt_trichotomy (u := u) p with hp | ⟨hp, hpu⟩ | ⟨hp, hpu⟩
  · exact ⟨1, one_pos, by rw [subdivPt_fst_of_ne hu0 hu1 hp, edge_appendVertex_old X u hp, one_smul]⟩
  · exact ⟨u, hu0, by rw [subdivPt_fst_of_lt hu0 hu1 hp hpu, edge_appendVertex_last, hp]⟩
  · exact ⟨1 - u, sub_pos.mpr hu1,
      by rw [subdivPt_fst_of_ge hu0 hu1 hp hpu, edge_appendVertex_new, hp]⟩

theorem det_edge_subdivPt_pos_iff {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (X : LabelledTuple m) (p q : TraversalPoint m) :
    0 < det (edge (appendVertex X u) (subdivPt hu0 hu1 p).1)
        (edge (appendVertex X u) (subdivPt hu0 hu1 q).1) ↔
      0 < det (edge X p.1) (edge X q.1) := by
  obtain ⟨c, hc, hce⟩ := edge_appendVertex_subdivPt_fst hu0 hu1 X p
  obtain ⟨d, hd, hde⟩ := edge_appendVertex_subdivPt_fst hu0 hu1 X q
  rw [hce, hde, det_smul_smul_plane]
  exact mul_pos_iff_of_pos_left (mul_pos hc hd)

/-! #### Crossings of a one-component positive diagram from traversal points -/

/-- Two traversal points of a generic one-component shadow that trace the same plane point on
remote edges with positive determinant are the over and under occurrences of a crossing of the
positive diagram, the first one being the over occurrence (`positiveDiagram_det_pos` fixes the over
strand; `common_point_unique` and `edgePoint_injective` fix the crossing parameter). -/
theorem exists_crossing_overVisit_eq (C : PolyComp) (hΓ : (Shadow.single C).Generic)
    (p q : TraversalPoint C.k) (hz : traversalEvaluation C.P p = traversalEvaluation C.P q)
    (hr : remote p.1 q.1) (hdet : 0 < det (edge C.P p.1) (edge C.P q.1)) :
    ∃ x : (Shadow.single C).Crossing,
      ((Shadow.single C).positiveDiagram hΓ).visitPt
        (((Shadow.single C).positiveDiagram hΓ).overVisit x) =
          (⟨0, p⟩ : (Shadow.single C).Pt) := by
  classical
  let s : (Shadow.single C).Strand := ⟨0, p.1⟩
  let t : (Shadow.single C).Strand := ⟨0, q.1⟩
  have hna : ¬ (Shadow.single C).Adjacent s t :=
    fun h => hr ((Shadow.single_adjacent_iff C s t).mp h)
  have hps : traversalEvaluation C.P p ∈ (Shadow.single C).seg s :=
    ⟨p.2.val, p.2.property.1, p.2.property.2.le, rfl⟩
  have hpt : traversalEvaluation C.P p ∈ (Shadow.single C).seg t :=
    ⟨q.2.val, q.2.property.1, q.2.property.2.le, hz⟩
  let x : (Shadow.single C).Crossing :=
    ⟨{s, t}, (Shadow.single C).isCrossing_pair hna ⟨_, hps, hpt⟩⟩
  have hs : s ∈ x.val := Finset.mem_insert_self s {t}
  have hst : s ≠ t := (Shadow.single C).ne_of_not_adjacent hna
  have hover : ((Shadow.single C).positiveDiagram hΓ).overStrand x = s := by
    have hmem : ((Shadow.single C).positiveDiagram hΓ).overStrand x ∈
        ({s, t} : Finset (Shadow.single C).Strand) :=
      ((Shadow.single C).positiveDiagram hΓ).over_mem x
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · have h' : ((Shadow.single C).positiveDiagram hΓ).overStrand x = t :=
        Finset.mem_singleton.mp h
      exfalso
      have hpos := (Shadow.single C).positiveDiagram_det_pos hΓ x
      have hother : (Shadow.single C).other x
          (((Shadow.single C).positiveDiagram hΓ).over_mem x) = s :=
        ((Shadow.single C).eq_other_of_mem_of_ne x
          (((Shadow.single C).positiveDiagram hΓ).over_mem x) hs (by rw [h']; exact hst)).symm
      rw [hother, h'] at hpos
      have hpos' : 0 < det (edge C.P q.1) (edge C.P p.1) := hpos
      rw [det_swap] at hpos'
      linarith
  have hcp : (Shadow.single C).crossingPoint x = traversalEvaluation C.P p := by
    symm
    apply hΓ.common_point_unique x
    intro r hr'
    have hr'' : r ∈ ({s, t} : Finset (Shadow.single C).Strand) := hr'
    rcases Finset.mem_insert.mp hr'' with h | h
    · rw [h]; exact hps
    · rw [Finset.mem_singleton.mp h]; exact hpt
  refine ⟨x, ?_⟩
  apply Shadow.single_pt_ext C
  have hlab : Shadow.singleStrandEquiv C (((Shadow.single C).positiveDiagram hΓ).overStrand x) =
      p.1 :=
    congrArg (Shadow.singleStrandEquiv C) hover
  have hparam : ((Shadow.single C).positiveDiagram hΓ).crossingParam x
      (((Shadow.single C).positiveDiagram hΓ).over_mem x) = p.2.val := by
    have h1 : (Shadow.single C).crossingPoint x = edgePoint C.P
        (Shadow.singleStrandEquiv C (((Shadow.single C).positiveDiagram hΓ).overStrand x))
        (((Shadow.single C).positiveDiagram hΓ).crossingParam x
          (((Shadow.single C).positiveDiagram hΓ).over_mem x)) :=
      (((Shadow.single C).positiveDiagram hΓ).crossingParam_spec x
        (((Shadow.single C).positiveDiagram hΓ).over_mem x)).2.2
    rw [hlab, hcp] at h1
    have h2 : edgePoint C.P p.1 p.2.val = edgePoint C.P p.1
        (((Shadow.single C).positiveDiagram hΓ).crossingParam x
          (((Shadow.single C).positiveDiagram hΓ).over_mem x)) := h1
    exact (edgePoint_injective ((regular_iff_edges C.P).mp (hΓ.regular 0) p.1).1 h2).symm
  exact Prod.ext hlab (Subtype.ext hparam)

-- U2 note: the proof below does not use `hoff` (nor `edgeSegment_appendVertex_union` /
-- `appendVertex_new_pairs_disjoint`): `over_surj` descends remoteness through
-- `regular_adjacent_meet` and `tail_off` of the subdivided shadow. The fixed statement keeps `hoff`.
set_option linter.unusedVariables false in
/-- **The flat subdivision is a reparametrization** (unit U2): `ReparamData` with `e = Equiv.refl`,
`φ := Equiv.ofBijective _ (subdivPt_bijective hu0 hu1)`, `between := traversalBetween_subdivPt`,
`eval_eq := traversalEvaluation_subdivPt`. `over_map`: a crossing `{a, b}` of `X` (a positive
crossing of the positive diagram) is carried to the crossing of `appendVertex X u` in which `-1` is
replaced by the half-edge containing the crossing point (its parameter `≠ u` by `hoff`; membership by
`edgeSegment_appendVertex_union`); non-adjacency of the new labels follows from that of the old (off
`-1`, `insertIndex` preserves adjacency); the over strand is preserved because both diagrams are
positive (`Shadow.positiveDiagram_isPositive`) and the half-edge directions are positive multiples of
`edge X (-1)`; the over-visit parameter is the rescaled one (`crossingParam_spec`, `edgePoint_injective`
on a nonzero edge, template `shiftPullback_overVisit_snd`). `over_surj`: every crossing of the
subdivision maps back to a crossing of `X` (`edgeSegment_appendVertex_old/last_subset/new_subset`),
the two label pairs `(insertIndex (-1), insertIndex 0)`, `(insertedIndex m, insertIndex (-2))` being
excluded by `appendVertex_new_pairs_disjoint`. -/
theorem reparam_positiveDiagram_single_appendVertex {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (X : LabelledTuple m) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hoff : ∀ e : ZMod m, e ≠ -1 → edgePoint X (-1) u ∉ edgeSegment X e)
    (hX' : (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic) :
    Reparam ((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX)
      ((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram hX') := by
  classical
  refine ⟨{ e := Equiv.refl _
            φ := fun _ => Equiv.ofBijective _ (subdivPt_bijective hu0 hu1)
            between := fun _ p q r h => traversalBetween_subdivPt hu0 hu1 p q r h
            eval_eq := fun _ p => traversalEvaluation_subdivPt X hu0 hu1 p
            over_map := ?_
            over_surj := ?_ }⟩
  · intro x
    obtain ⟨p, hp⟩ : ∃ p : TraversalPoint m,
        (((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).visitPt
          (((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).overVisit x)).2 = p := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : TraversalPoint m,
        (((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).visitPt
          (((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).underVisit x)).2 = q := ⟨_, rfl⟩
    have hzp : traversalEvaluation X p = (Shadow.single ⟨m, hm, X⟩).crossingPoint x := by
      subst hp
      exact (((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).crossingParam_spec x
        (((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).over_mem x)).2.2.symm
    have hzq : traversalEvaluation X q = (Shadow.single ⟨m, hm, X⟩).crossingPoint x := by
      subst hq
      exact (((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).crossingParam_spec x
        (((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).under_mem x)).2.2.symm
    have hz : traversalEvaluation X p = traversalEvaluation X q := hzp.trans hzq.symm
    have hr : remote p.1 q.1 := by
      subst hp hq
      exact fun h => ((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX).not_adjacent_over_under x
        ((Shadow.single_adjacent_iff ⟨m, hm, X⟩ _ _).mpr h)
    have hdet : 0 < det (edge X p.1) (edge X q.1) := by
      subst hp hq
      exact Shadow.positiveDiagram_isPositive _ hX x
    have hz' : traversalEvaluation (appendVertex X u) (subdivPt hu0 hu1 p) =
        traversalEvaluation (appendVertex X u) (subdivPt hu0 hu1 q) := by
      rw [traversalEvaluation_subdivPt X hu0 hu1 p, traversalEvaluation_subdivPt X hu0 hu1 q]
      exact hz
    obtain ⟨x', hx'⟩ := exists_crossing_overVisit_eq ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩
      hX' (subdivPt hu0 hu1 p) (subdivPt hu0 hu1 q) hz' (remote_subdivPt_fst hu0 hu1 hm hr)
      ((det_edge_subdivPt_pos_iff hu0 hu1 X p q).mpr hdet)
    refine ⟨x', ?_⟩
    apply Shadow.single_pt_ext ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩
    rw [hx']
    exact congrArg (subdivPt hu0 hu1) hp
  · intro x'
    obtain ⟨p', hp'⟩ : ∃ p' : TraversalPoint (m + 1),
        (((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram hX').visitPt
          (((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram
            hX').overVisit x')).2 = p' := ⟨_, rfl⟩
    obtain ⟨q', hq'⟩ : ∃ q' : TraversalPoint (m + 1),
        (((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram hX').visitPt
          (((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram
            hX').underVisit x')).2 = q' := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ := (subdivPt_bijective (m := m) hu0 hu1).2 p'
    obtain ⟨q, hq⟩ := (subdivPt_bijective (m := m) hu0 hu1).2 q'
    have hzp' : traversalEvaluation (appendVertex X u) p' =
        (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).crossingPoint x' := by
      subst hp'
      exact (((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram
        hX').crossingParam_spec x' (((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm,
          appendVertex X u⟩).positiveDiagram hX').over_mem x')).2.2.symm
    have hzq' : traversalEvaluation (appendVertex X u) q' =
        (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).crossingPoint x' := by
      subst hq'
      exact (((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram
        hX').crossingParam_spec x' (((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm,
          appendVertex X u⟩).positiveDiagram hX').under_mem x')).2.2.symm
    have hz : traversalEvaluation X p = traversalEvaluation X q := by
      rw [← traversalEvaluation_subdivPt X hu0 hu1 p, ← traversalEvaluation_subdivPt X hu0 hu1 q,
        hp, hq, hzp', hzq']
    have hr' : remote p'.1 q'.1 := by
      subst hp' hq'
      exact fun h => ((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram
        hX').not_adjacent_over_under x'
          ((Shadow.single_adjacent_iff ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩ _ _).mpr h)
    have hr : remote p.1 q.1 := by
      refine remote_of_remote_subdivPt hu0 hu1 hm X hX hX' hz ?_
      rw [hp, hq]
      exact hr'
    have hdet' : 0 < det (edge (appendVertex X u) p'.1) (edge (appendVertex X u) q'.1) := by
      subst hp' hq'
      exact Shadow.positiveDiagram_isPositive _ hX' x'
    have hdet : 0 < det (edge X p.1) (edge X q.1) := by
      refine (det_edge_subdivPt_pos_iff hu0 hu1 X p q).mp ?_
      rw [hp, hq]
      exact hdet'
    obtain ⟨x, hx⟩ := exists_crossing_overVisit_eq ⟨m, hm, X⟩ hX p q hz hr hdet
    refine ⟨x, ?_⟩
    apply Shadow.single_pt_ext ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩
    rw [hx, hp']
    exact hp

theorem homfly_positiveDiagram_single_appendVertex {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (X : LabelledTuple m) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hoff : ∀ e : ZMod m, e ≠ -1 → edgePoint X (-1) u ∉ edgeSegment X e)
    (hX' : (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic) :
    homfly ((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX) =
      homfly ((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram hX') :=
  homfly_planar (PlanarIsotopic.of_reparam
    (reparam_positiveDiagram_single_appendVertex hm X hu0 hu1 hX hoff hX'))

end Link

/-- **The list form of the flat-vertex erasure** (unit U3; the structure of the accepted
`rotationNumber_erase_flat`, FlatCarriers.lean:4164-4283, exported and stopped before the rotation
number): the polygon of `L` is, up to re-indexing, the polygon `Q := markPolygon f (L₂ ++ L₁)` (for
`L = L₁ ++ x :: L₂`) with one vertex appended at the parameter `u = 1/(1+s) ∈ (0,1)` of its closing
edge, that vertex being the point `f x`; and `Q` is a re-indexing of the polygon of `L'`. In the
accepted proof: `h1 h2 h3 h4` give the first `Reindexed` (`Reindexed.symm`/`.trans`), `h5 h6` the
second, `hx'` the point identity. The size of `Q` is existential (it equals `L'.length`, recorded by
the first `Reindexed`), so no recast is needed. -/
theorem exists_appendVertex_of_erase_flat {α β : Type*} [BEq α] [LawfulBEq α]
    (f : α → Plane) (L : List α) [NeZero L.length] (hnd : L.Nodup) {x : α} (hx : x ∈ L)
    (hflat : ∀ k : ZMod L.length, L[k.val]'(ZMod.val_lt k) = x →
      ∃ s : ℝ, 0 < s ∧ edge (markPolygon f L) k = s • edge (markPolygon f L) (k - 1))
    (g : α → β) (f' : β → Plane) (hf' : ∀ a ∈ L, a ≠ x → f' (g a) = f a)
    (L' : List β) [NeZero L'.length] (hL' : (L.erase x).map g ~r L') :
    ∃ (m : ℕ) (_ : NeZero m) (Q : LabelledTuple m) (u : ℝ), 0 < u ∧ u < 1 ∧
      Reindexed (markPolygon f' L') Q ∧ Reindexed (appendVertex Q u) (markPolygon f L) ∧
      edgePoint Q (-1) u = f x := by
  sorry

end LinkLayer

/-! ## B. On a generic polygon the geo data are the accepted data (recast) -/

section GenericIdentification

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
  (S : Finset (Crossing P))

theorem geoCornerCount_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCornerCount (generic_crossingGeometry hn hP) S q =
      ccpCornerCount hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoCornerCount ccpCornerCount
  rw [geoComponentCornerList_eq_generic]

/-- The geo corner polygon is the accepted one, recast along the equal corner counts. -/
theorem geoCornerPolygon_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCornerPolygon (generic_crossingGeometry hn hP) S q =
      recastTuple (geoCornerCount_eq_generic hn hP S q)
        (ccpCornerPolygon hn hP S (geoComponentEquivGeneric hn hP S q)) := by
  funext k
  unfold geoCornerPolygon recastTuple
  rw [ccpCornerPolygon_apply, geoMarkPosition_eq_generic hn hP]
  congr 2
  exact getElem_congr_lists _ _ (geoComponentCornerList_eq_generic hn hP S q) _ _ _ _
    (zmod_val_cast (geoCornerCount_eq_generic hn hP S q) k).symm

theorem geoCornerCount_ge_three_generic {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    3 ≤ geoCornerCount (generic_crossingGeometry hn hP) S q := by
  rw [geoCornerCount_eq_generic]
  exact ccpCornerCount_ge_three hn hP hS _

/-- The carrier shadow of the accepted carrier is the one-component shadow of the geo corner
polygon (`polyComp_recastTuple`). -/
theorem carrierShadow_eq_single_geo {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierShadow hn hP S (geoComponentEquivGeneric hn hP S q) hS =
      Shadow.single ⟨geoCornerCount (generic_crossingGeometry hn hP) S q,
        geoCornerCount_ge_three_generic hn hP hS q,
        geoCornerPolygon (generic_crossingGeometry hn hP) S q⟩ := by
  unfold carrierShadow carrierPolyComp
  rw [geoCornerPolygon_eq_generic hn hP]
  exact congrArg Shadow.single (polyComp_recastTuple _ _ _ _).symm

theorem single_geo_generic {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    (Shadow.single ⟨geoCornerCount (generic_crossingGeometry hn hP) S q,
      geoCornerCount_ge_three_generic hn hP hS q,
      geoCornerPolygon (generic_crossingGeometry hn hP) S q⟩).Generic := by
  rw [← carrierShadow_eq_single_geo hn hP hS q]
  exact carrierShadow_generic hn hP S _ hS

/-- The positive lift of the accepted carrier is the positive diagram of the geo corner polygon. -/
theorem positiveLift_eq_geo {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS =
      (Shadow.single ⟨geoCornerCount (generic_crossingGeometry hn hP) S q,
        geoCornerCount_ge_three_generic hn hP hS q,
        geoCornerPolygon (generic_crossingGeometry hn hP) S q⟩).positiveDiagram
        (single_geo_generic hn hP hS q) := by
  unfold positiveLift
  exact positiveDiagram_congr (carrierShadow_eq_single_geo hn hP hS q) _ _

theorem cornerSelector_recastTuple {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k)
    (f : LabelledTuple k) : cornerSelector (recastTuple hk f) = cornerSelector f := by
  subst hk; rfl

/-- The selector weight of lem:C-X1 is the selector of the corner polygon. -/
theorem carrierWeight_eq_cornerSelector (q : Component hn hP S) :
    carrierWeight hn hP S q = cornerSelector (ccpCornerPolygon hn hP S q) := by
  unfold carrierWeight cornerSelector
  split_ifs <;> rfl

/-- The selector weight of lem:C-X1 is the selector of cor:flat-carriers (iii). -/
theorem carrierWeight_eq_geoCarrierSelector (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierWeight hn hP S (geoComponentEquivGeneric hn hP S q) =
      geoCarrierSelector (generic_crossingGeometry hn hP) S q := by
  rw [geoCarrierSelector_eq_cornerSelector, geoCornerPolygon_eq_generic hn hP,
    cornerSelector_recastTuple, carrierWeight_eq_cornerSelector]

theorem wind_eq_prod_geoCarrierSelector :
    wind hn hP S = ∏ q : GeoComponent (generic_crossingGeometry hn hP) S,
      geoCarrierSelector (generic_crossingGeometry hn hP) S q := by
  unfold wind
  exact (Fintype.prod_equiv (geoComponentEquivGeneric hn hP S) _ _
    fun q => (carrierWeight_eq_geoCarrierSelector hn hP S q).symm).symm

theorem carrierCrossings_eq_geo (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierCrossings hn hP S (geoComponentEquivGeneric hn hP S q) =
      geoCarrierCrossings (generic_crossingGeometry hn hP) S q := by
  ext x
  rw [mem_carrierCrossings]
  simp only [geoCarrierCrossings, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr Iff.rfl (forall_congr' fun v => forall_congr' fun _ => ?_)
  rw [← geoComponentEquivGeneric_owner]
  exact (geoComponentEquivGeneric hn hP S).injective.eq_iff

theorem carrierCrossingCount_eq_geo (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierCrossingCount hn hP S (geoComponentEquivGeneric hn hP S q) =
      (geoCarrierCrossings (generic_crossingGeometry hn hP) S q).card := by
  rw [carrierCrossingCount_eq_card, carrierCrossings_eq_geo]

theorem carrierRotation_eq_geo (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierRotation hn hP S (geoComponentEquivGeneric hn hP S q) =
      rotationNumber (geoCornerPolygon (generic_crossingGeometry hn hP) S q) := by
  unfold carrierRotation
  rw [geoCornerPolygon_eq_generic, rotationNumber_recastTuple]

/-- `c(Q)` read on the geo data of the carrier. -/
theorem cornerCoefficient_eq_geo {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    cornerCoefficient hn hP S (geoComponentEquivGeneric hn hP S q) hS =
      coeffAt (1 - ((geoCarrierCrossings (generic_crossingGeometry hn hP) S q).card : ℤ) -
          |round (rotationNumber (geoCornerPolygon (generic_crossingGeometry hn hP) S q))|) 0
        (homfly ((Shadow.single ⟨geoCornerCount (generic_crossingGeometry hn hP) S q,
          geoCornerCount_ge_three_generic hn hP hS q,
          geoCornerPolygon (generic_crossingGeometry hn hP) S q⟩).positiveDiagram
          (single_geo_generic hn hP hS q))) := by
  rw [cornerCoefficient_eq_coeffAt]
  unfold cornerHomfly cornerSlot carrierRotationInt
  rw [carrierCrossingCount_eq_geo, carrierRotation_eq_geo, positiveLift_eq_geo]

end GenericIdentification

/-! ## C. The carrier bijections at one side parameter -/

section Carriers

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
  (S : Finset (Crossing g.center))

/-- Centre carriers ↔ side carriers (field `correspond_sides`): the carrier of `a` goes to the
carrier of `markTransport (hs b) a`. -/
def sideCarrierEquiv (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    GeoComponent (flatCentreCG hn g j hz hb hc) S ≃
      GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S) :=
  Quotient.congr (markTransport (hs b)) fun a a' => by
    have h := (hF.correspond_sides b).2 a a'
    rw [geoOwner_eq_iff, geoOwner_eq_iff] at h
    exact h

theorem sideCarrierEquiv_owner (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (a : Mark g.center) :
    sideCarrierEquiv hn g j hz hb hc t hs S hF b (geoOwner (flatCentreCG hn g j hz hb hc) S a) =
      geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) := rfl

theorem sideCarrierEquiv_central (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    sideCarrierEquiv hn g j hz hb hc t hs S hF b (centralCarrierThroughJ hn g j hz hb hc S) =
      geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) := rfl

/-- The centre copy of a deletion carrier (field `correspond_deletion`): the carrier of `b` goes
to the carrier of `fusionMark b`; a bijection by `correspond_deletion.2`. -/
def deletionCarrierEquiv (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) ≃
      GeoComponent (flatCentreCG hn g j hz hb hc) S :=
  Equiv.ofBijective
    (Quotient.lift (fun b => geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))
      fun b b' hbb' => (hF.correspond_deletion.2.1 b b').mp (Quotient.sound hbb'))
    (by
      constructor
      · intro x y hxy
        induction x using Quotient.inductionOn with
        | h b =>
          induction y using Quotient.inductionOn with
          | h b' => exact (hF.correspond_deletion.2.1 b b').mpr hxy
      · intro q
        obtain ⟨b, hb⟩ := hF.correspond_deletion.2.2 q
        exact ⟨Quotient.mk _ b, hb⟩)

theorem deletionCarrierEquiv_owner (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (b : Mark (deleteVertex g.center j)) :
    deletionCarrierEquiv hn g j hz hb hc t hs S hF
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) := rfl

/-- The deletion copy of the carrier through `μ_j` is `deletionCopyThroughJ`
(`fusionMark_delMark` with `central_vs_deletion_through_mu_j.1`, `geoOwner_successor`). -/
theorem deletionCarrierEquiv_deletionCopy (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    deletionCarrierEquiv hn g j hz hb hc t hs S hF (deletionCopyThroughJ hn g j hz hb hc S) =
      centralCarrierThroughJ hn g j hz hb hc S := by
  show deletionCarrierEquiv hn g j hz hb hc t hs S hF
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delMark hn g j hz hb hc
          (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))) =
    geoOwner (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
  rw [deletionCarrierEquiv_owner,
    fusionMark_delMark hn g j hz hb hc _ hF.central_vs_deletion_through_mu_j.1, geoOwner_successor]

theorem deletionCarrierEquiv_symm_central (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    (deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm (centralCarrierThroughJ hn g j hz hb hc S) =
      deletionCopyThroughJ hn g j hz hb hc S := by
  rw [Equiv.symm_apply_eq]
  exact (deletionCarrierEquiv_deletionCopy hn g j hz hb hc t hs S hF).symm

/-! ### Slots: retained crossings and rotations agree (cor (ii)) -/

theorem card_geoCarrierCrossings_side (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    (geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)).card =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S q).card := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  rw [sideCarrierEquiv_owner]
  have h : geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
      (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a)) =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a)).map (crossingTransport (hs b)).toEmbedding := by
    ext x'
    obtain ⟨x, rfl⟩ := (crossingTransport (hs b)).surjective x'
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact (hF.same_retained_crossings.1 b a x).symm
  rw [h, Finset.card_map]

theorem card_geoCarrierCrossings_deletion (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    (geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)).card =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S q).card := by
  obtain ⟨q', rfl⟩ := (deletionCarrierEquiv hn g j hz hb hc t hs S hF).surjective q
  obtain ⟨b, rfl⟩ := geoOwner_surjective (flatDeletionCG hn g j hz hb hc) _ q'
  rw [Equiv.symm_apply_apply, deletionCarrierEquiv_owner]
  have h : geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).map
          (fusionCrossingEquiv hn hz hb hc).toEmbedding := by
    ext x'
    obtain ⟨x, rfl⟩ := (fusionCrossingEquiv hn hz hb hc).surjective x'
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact (hF.same_retained_crossings.2 b x).symm
  rw [h, Finset.card_map]

theorem rotationNumber_side (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  exact (hF.same_rotation.1 b a).1

theorem rotationNumber_deletion (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  obtain ⟨q', rfl⟩ := (deletionCarrierEquiv hn g j hz hb hc t hs S hF).surjective q
  obtain ⟨b, rfl⟩ := geoOwner_surjective (flatDeletionCG hn g j hz hb hc) _ q'
  rw [Equiv.symm_apply_apply, deletionCarrierEquiv_owner]
  exact (hF.same_rotation.2 b).1

end Carriers

/-! ## D. The centre corner polygons: re-indexed deletion copies, and the flat subdivision -/

section CentreGeometry

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
  (S : Finset (Crossing g.center))

/-- Corner counts agree between a centre carrier and its side copy
(`geoCornerCount_markTransport` with `identify_sides_marks_of`). -/
theorem geoCornerCount_side (hsd : SideRecordData hn g j hz hb hc t)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    geoCornerCount (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q) =
      geoCornerCount (flatCentreCG hn g j hz hb hc) S q := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  exact (geoCornerCount_markTransport _ _ (hs b) (identify_sides_marks_of hn g j hz hb hc t hsd hs b)
    S a).symm

/-- Every centre carrier of an independent support has at least three corners (its side copy is
an accepted carrier). -/
theorem geoCornerCount_ge_three_centre (hsd : SideRecordData hn g j hz hb hc t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    3 ≤ geoCornerCount (flatCentreCG hn g j hz hb hc) S q := by
  rw [← geoCornerCount_side hn g j hz hb hc t hs S hsd hF true q]
  exact geoCornerCount_ge_three_generic (flat_hn1 hn) (g.sideTuple true t).property
    (((independent_supports_of hn g j hz hb hc t hsd hs S).1 true).mp hS) _

/-- "Every other central carrier is unchanged by deletion": its corner polygon is a re-indexing of
its deletion copy's (`others_unchanged.2` through `reindexed_markPolygon_of_isRotated`,
`reindexed_markPolygon_map`, `markPolygon_congr` with `fusion_mark_point` — the three steps of
`rotationNumber_others_unchanged`). -/
theorem reindexed_deletion_other (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hq : q ≠ centralCarrierThroughJ hn g j hz hb hc S) :
    Reindexed (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q))
      (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  obtain ⟨q', rfl⟩ := (deletionCarrierEquiv hn g j hz hb hc t hs S hF).surjective q
  obtain ⟨b, rfl⟩ := geoOwner_surjective (flatDeletionCG hn g j hz hb hc) _ q'
  rw [Equiv.symm_apply_apply, deletionCarrierEquiv_owner]
  rw [deletionCarrierEquiv_owner] at hq
  have hrot := Cycle.coe_eq_coe.mp (hF.others_unchanged b hq).2.1
  have : NeZero ((geoComponentCornerList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        (fusionMark hn g j hz hb hc)).length := ⟨by rw [List.length_map]; exact NeZero.ne _⟩
  have h1 := reindexed_markPolygon_of_isRotated
    (fun m => traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) m)) hrot
  have h2 := reindexed_markPolygon_map
    (fun m => traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) m))
    (fusionMark hn g j hz hb hc)
    (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))
  have h3 := markPolygon_congr
    (f := (fun m => traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) m))
      ∘ fusionMark hn g j hz hb hc)
    (f' := fun m => traversalEvaluation (deleteVertex g.center j)
      (geoMarkPosition (flatDeletionCG hn g j hz hb hc) m))
    (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))
    (fun a _ => fusion_mark_point hn g j hz hb hc a)
  exact (h3 ▸ h2).trans h1

/-- **`μ_j` lies on at most one closed edge of the deletion copy of the carrier through `μ_j`**
(unit U3). Rewrite through `geoCornerPolygon_eq_generic` + `edgeSegment_recastTuple` to the accepted
`ccpCornerPolygon` of the deletion carrier `geoComponentEquivGeneric … (deletionCopyThroughJ …)`. Two
non-adjacent edges meet only at a crossing point of the deletion (`nonadjacent_meet_crossing`),
which is a centre crossing point (`crossingPoint_fusion`) and so not the vertex `μ_j`
(`flat_germ_spatial_data` at the centre); consecutive edges meet only at their common corner
(`consecutive_meet`), a deletion corner point, which is the point of a centre mark other than
`μ_j` (`deletion_mark_point`, `central_vs_deletion_through_mu_j.3`), hence not `μ_j`
(injectivity of the centre vertices, no vertex is a crossing point). -/
theorem mu_j_unique_edge (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S))
    (e e' : ZMod (geoCornerCount (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)))
    (he : g.center j ∈ edgeSegment (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) e)
    (he' : g.center j ∈ edgeSegment (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) e') :
    e = e' := by
  sorry

/-- **The flat subdivision at `μ_j`** (unit U3; cor:flat-carriers (i) "the central copy of that
carrier differs from its deletion copy only by the positive-flat subdivision at `μ_j`"): the centre
corner polygon of the carrier through `μ_j` is, up to re-indexing, a polygon `Q` (itself a
re-indexing of the deletion copy's corner polygon) with the vertex `μ_j` appended on its closing edge
at an interior parameter, and `μ_j` lies on no other closed edge of `Q`.
Proof: `exists_appendVertex_of_erase_flat` applied exactly as in `rotationNumber_deletionCopyThroughJ`
(FlatCarriers.lean:4324): `f` = centre mark point, `L` = centre corner list of `Q_*`
(`geoComponentCornerList_nodup`, `x = Sum.inl j ∈ L` by `mem_geoComponentCornerList` +
`isTrueCorner_vertex`), `hflat` from `flat_of_turn_eq_zero` (regularity by `regular_iff_edges` from
`hF.nonzero_segments.2.1`, `hF.no_antiparallel.1`; zero turn from `hF.turns_nonzero.1`), `g = delMark`,
`f'` = deletion mark point, `hf' = deletion_mark_point`, `L'` = deletion corner list of `Q_*^D`,
`hL' = Cycle.coe_eq_coe.mp hF.central_vs_deletion_through_mu_j.2.2.1`; `f x = g.center j` by
`geoMarkPosition_evaluation_vertex`; the off-edge clause from `mu_j_unique_edge` transported along the
first `Reindexed` (`subst` the size, `reindexed_eq_shift`, `edgeSegment_shift`: `μ_j ∈ edgeSegment Q
(-1)` and `μ_j ∈ edgeSegment Q e` give `-1 + r = e + r`). -/
theorem exists_appendVertex_central (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    ∃ (m : ℕ) (_ : NeZero m) (Q : LabelledTuple m) (u : ℝ), 0 < u ∧ u < 1 ∧
      Reindexed (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S)) Q ∧
      Reindexed (appendVertex Q u)
        (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S (centralCarrierThroughJ hn g j hz hb hc S)) ∧
      edgePoint Q (-1) u = g.center j ∧
      (∀ e : ZMod m, e ≠ -1 → edgePoint Q (-1) u ∉ edgeSegment Q e) := by
  sorry

/-- **The one-component shadow of every centre corner polygon is generic** (unit U4; the answer to
"is the centre corner polygon a generic shadow?" without redoing lem:carriers at the nongeneric
centre). `by_cases q = q_*`. (≠) `single_generic_of_reindexed (reindexed_deletion_other …)` from
`single_geo_generic` on the deletion (`hS_D` from `(independent_supports_of … hsd hs S).2.mp hS`; the
`flatDeletionCG`/`generic_crossingGeometry` proofs coincide by proof irrelevance). (=) `obtain ⟨m, _, Q,
u, hu0, hu1, h1, h2, -, hoff⟩ := exists_appendVertex_central …`; `obtain ⟨hm, -⟩ := h1; subst hm`;
`single Q` generic by `single_generic_of_reindexed h1` (sizes `3 ≤ _` by `geoCornerCount_ge_three_generic`);
`single (appendVertex Q u)` generic by `single_generic_appendVertex … hoff`; then
`single_generic_of_reindexed h2` (with `Nat.le_succ_of_le`). Template: route B's `single_generic_centre`. -/
theorem centre_shadow_generic (hsd : SideRecordData hn g j hz hb hc t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    (Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
      geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF q,
      geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).Generic := by
  have hS_D := (independent_supports_of hn g j hz hb hc t hsd hs S).2.mp hS
  by_cases hq : q = centralCarrierThroughJ hn g j hz hb hc S
  · subst hq
    obtain ⟨m, _, Q, u, hu0, hu1, h1, h2, -, hoff⟩ :=
      exists_appendVertex_central hn g j hz hb hc t hs S hF hS_D
    obtain ⟨hm, -⟩ := id h1
    subst hm
    have hkD : 3 ≤ geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) :=
      geoCornerCount_ge_three_generic hn (generic_deleteVertex hn hz hb hc) hS_D
        (deletionCopyThroughJ hn g j hz hb hc S)
    have hgD := single_geo_generic hn (generic_deleteVertex hn hz hb hc) hS_D
      (deletionCopyThroughJ hn g j hz hb hc S)
    have hgQ := Link.single_generic_of_reindexed h1 hkD hkD hgD
    have hgA := Link.single_generic_appendVertex hkD Q hu0 hu1 hgQ hoff
    exact Link.single_generic_of_reindexed h2 (Nat.le_succ_of_le hkD) _ hgA
  · have hkD : 3 ≤ geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q) :=
      geoCornerCount_ge_three_generic hn (generic_deleteVertex hn hz hb hc) hS_D
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)
    exact Link.single_generic_of_reindexed
      (reindexed_deletion_other hn g j hz hb hc t hs S hF q hq) hkD _
      (single_geo_generic hn (generic_deleteVertex hn hz hb hc) hS_D
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q))

/-- **Deletion lift = centre diagram** (unit U4). The HOMFLY polynomial of the positive lift of the
deletion copy of a centre carrier (read as the positive diagram of its geo corner polygon,
`positiveLift_eq_geo`, exactly as `cornerCoefficient_eq_geo` reads it) is that of the positive diagram
of the centre corner polygon. (≠ q_*) one re-indexing: `homfly_positiveDiagram_single_of_reindexed
(reindexed_deletion_other …)`. (= q_*) `subst` the carrier, `rw [deletionCarrierEquiv_symm_central]`
(or `simp only` on the `symm` application), `exists_appendVertex_central`, `subst` the size, then
`homfly_positiveDiagram_single_of_reindexed h1`, `homfly_positiveDiagram_single_appendVertex … hoff`,
`homfly_positiveDiagram_single_of_reindexed h2` (genericity of the intermediate shadows as in
`centre_shadow_generic`). Template: route B's `planarIsotopic_centre_del`. -/
theorem homfly_deletion_eq_centre (hsd : SideRecordData hn g j hz hb hc t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    homfly ((Shadow.single ⟨geoCornerCount (flatDeletionCG hn g j hz hb hc)
          (deletionSupport hn g j hz hb hc S) ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q),
        geoCornerCount_ge_three_generic hn (generic_deleteVertex hn hz hb hc) hS_D _,
        geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)⟩).positiveDiagram
        (single_geo_generic hn (generic_deleteVertex hn hz hb hc) hS_D _)) =
      homfly ((Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
        geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF q,
        geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).positiveDiagram
        (centre_shadow_generic hn g j hz hb hc t hs S hsd hS hF q)) := by
  by_cases hq : q = centralCarrierThroughJ hn g j hz hb hc S
  · subst hq
    generalize hqD : (deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm
      (centralCarrierThroughJ hn g j hz hb hc S) = qD
    rw [deletionCarrierEquiv_symm_central] at hqD
    subst hqD
    obtain ⟨m, _, Q, u, hu0, hu1, h1, h2, -, hoff⟩ :=
      exists_appendVertex_central hn g j hz hb hc t hs S hF hS_D
    obtain ⟨hm, -⟩ := id h1
    subst hm
    have hkD : 3 ≤ geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) :=
      geoCornerCount_ge_three_generic hn (generic_deleteVertex hn hz hb hc) hS_D
        (deletionCopyThroughJ hn g j hz hb hc S)
    have hgD := single_geo_generic hn (generic_deleteVertex hn hz hb hc) hS_D
      (deletionCopyThroughJ hn g j hz hb hc S)
    have hgQ := Link.single_generic_of_reindexed h1 hkD hkD hgD
    have hgA := Link.single_generic_appendVertex hkD Q hu0 hu1 hgQ hoff
    have e1 := Link.homfly_positiveDiagram_single_of_reindexed h1 hkD hkD hgD hgQ
    have e2 := Link.homfly_positiveDiagram_single_appendVertex hkD Q hu0 hu1 hgQ hoff hgA
    have e3 := Link.homfly_positiveDiagram_single_of_reindexed h2 (Nat.le_succ_of_le hkD)
      (geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF _) hgA
      (centre_shadow_generic hn g j hz hb hc t hs S hsd hS hF _)
    exact e1.trans (e2.trans e3)
  · exact Link.homfly_positiveDiagram_single_of_reindexed
      (reindexed_deletion_other hn g j hz hb hc t hs S hF q hq) _ _ _ _

end CentreGeometry

/-! ## E. The deformation through the flat centre -/

section DeformThroughCentre

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- The radius facts of lem:flat-sides used along the family: below `δ`, every `g.curve s` is on
the geometric record domain with the centre's crossing supports (`FlatSidesData`, last conjunct,
through `GeometricRecordsAgree`), and the side records hold at every side parameter. -/
def FlatFamilyData (δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ g.radius ∧
  (∀ s : g.Parameter, |s.val| < δ →
    CrossingGeometry (g.curve s) ∧
      ∀ c : Finset (ZMod (n + 1)), IsCrossing g.center c ↔ IsCrossing (g.curve s) c) ∧
  ∀ t : g.SideParameter, t.val < δ → SideRecordData hn g j hz hb hc t

theorem exists_flatFamilyData (hsc : g.SignChanges (fun P => (turn P j : ℝ))) :
    ∃ δ : ℝ, FlatFamilyData hn g j hz hb hc δ := by
  obtain ⟨δS, hδS, hδSr, hloc⟩ := flat_side_records hn g j hz hb hc (flat_sides hn g hz hb hc hsc)
  obtain ⟨_, _, _, _, _, _, δF, hδF, -, -, hF⟩ := flat_sides hn g hz hb hc hsc
  refine ⟨min δS δF, lt_min hδS hδF, (min_le_left _ _).trans hδSr, ?_, ?_⟩
  · intro s hs
    have h := hF s (lt_of_lt_of_le hs (min_le_right _ _))
    obtain ⟨hsupp, -⟩ := h.2.2.2.2.2.1
    exact ⟨h.2.1, hsupp⟩
  · intro t ht
    exact (hloc t (lt_of_lt_of_le ht (min_le_left _ _))).2

omit [NeZero n] in
/-- `markPointOn` is continuous at every parameter on the geometric record domain with the
centre's supports (the proof of the accepted `continuousAt_markPointOn`, at `s₀` in place of `0`:
vertices by `g.continuous_curve`, visits by `continuousAt_edgeParameter_of_geometry`). -/
theorem continuousAt_markPointOn_of (s₀ : g.Parameter) (hC : CrossingGeometry (g.curve s₀))
    (hcs : ∀ c : Finset (ZMod (n + 1)), IsCrossing g.center c ↔ IsCrossing (g.curve s₀) c)
    (a : Mark g.center) : ContinuousAt (fun s => markPointOn g s a) s₀ := by
  cases a with
  | inl i => exact ((continuous_apply i).comp g.continuous_curve).continuousAt
  | inr v =>
    have hcross0 : IsCrossing g.center {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    have hcross := (hcs _).mp hcross0
    have hF : ContinuousAt (fun Q : LabelledTuple (n + 1) =>
        edgePoint Q v.2.val (edgeParameter Q v.2.val (visitTwin v).2.val)) (g.curve s₀) :=
      (continuous_vertex v.2.val).continuousAt.add
        ((continuousAt_edgeParameter_of_geometry hC hcross).smul
          (continuous_edge v.2.val).continuousAt)
    exact ContinuousAt.comp (f := g.curve) (x := s₀) hF g.continuous_curve.continuousAt

/-- The affine path `u ↦ u · (±t)` from the centre to the side time `sideTime b t`. -/
def sideParamPath (b : Bool) (t : g.SideParameter) (u : unitInterval) : g.Parameter :=
  ⟨u.val * (g.sideTime b t).val, by
    have h1 := (g.sideTime b t).property
    have h2 := u.property
    simp only [Set.mem_Ioo, Set.mem_Icc] at h1 h2 ⊢
    constructor <;> nlinarith [abs_nonneg (g.sideTime b t).val, g.radius_pos]⟩

omit [NeZero n] in
theorem sideParamPath_zero (b : Bool) (t : g.SideParameter) :
    sideParamPath g b t 0 = g.zeroParameter := by
  apply Subtype.ext
  simp [sideParamPath, WallGerm.zeroParameter]

omit [NeZero n] in
theorem sideParamPath_one (b : Bool) (t : g.SideParameter) :
    sideParamPath g b t 1 = g.sideTime b t := by
  apply Subtype.ext
  simp [sideParamPath]

omit [NeZero n] in
theorem continuous_sideParamPath (b : Bool) (t : g.SideParameter) :
    Continuous (sideParamPath g b t) :=
  (continuous_subtype_val.mul continuous_const).subtype_mk _

omit [NeZero n] in
theorem abs_sideParamPath_lt (b : Bool) (t : g.SideParameter) {δ : ℝ} (ht : t.val < δ)
    (u : unitInterval) : |(sideParamPath g b t u).val| < δ := by
  show |u.val * (g.sideTime b t).val| < δ
  rw [abs_mul, g.sideTime_val_abs, abs_of_nonneg u.property.1]
  exact lt_of_le_of_lt (mul_le_of_le_one_left t.property.1.le u.property.2) ht

omit [NeZero n] in
/-- For `0 < u`, the path parameter is the side time of the side parameter `u · t`. -/
theorem sideParamPath_eq_sideTime (b : Bool) (t : g.SideParameter) (u : unitInterval)
    (hu : 0 < u.val) :
    sideParamPath g b t u =
      g.sideTime b ⟨u.val * t.val, by
        have h1 := t.property; have h2 := u.property
        simp only [Set.mem_Ioo, Set.mem_Icc] at h1 h2 ⊢
        constructor <;> nlinarith⟩ := by
  apply Subtype.ext
  show u.val * (g.sideTime b t).val = (g.sideTime b ⟨u.val * t.val, _⟩).val
  cases b <;> simp only [WallGerm.sideTime, Bool.false_eq_true, ↓reduceIte, mul_neg]

variable (S : Finset (Crossing g.center))

omit [NeZero n] in
/-- The corner polygon of the centre carrier `q` read along the affine path `sideParamPath b t`
from the centre (`u = 0`) to the side time (`u = 1`). -/
def sideCornerPath (b : Bool) (t : g.SideParameter)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (u : unitInterval) :
    LabelledTuple (geoCornerCount (flatCentreCG hn g j hz hb hc) S q) :=
  cornerFamily hn g j hz hb hc S q (sideParamPath g b t u)

omit [NeZero n] in
theorem sideCornerPath_zero (b : Bool) (t : g.SideParameter)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    sideCornerPath hn g j hz hb hc S b t q 0 = geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q := by
  unfold sideCornerPath
  rw [sideParamPath_zero, cornerFamily_zero]

omit [NeZero n] in
theorem sideCornerPath_one (b : Bool) (t : g.SideParameter)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    sideCornerPath hn g j hz hb hc S b t q 1 =
      cornerFamily hn g j hz hb hc S q (g.sideTime b t) := by
  unfold sideCornerPath
  rw [sideParamPath_one]

omit [NeZero n] in
/-- The side copy's corner polygon is the accepted `cornerFamily` at the side time, recast along
the equal corner counts (the corner list is carried literally by `markTransport`:
`geoComponentCornerList_markTransport` with `identify_sides_marks_of`; points by
`markPointOn_side`). -/
theorem geoCornerPolygon_side_eq_cornerFamily (t : g.SideParameter)
    (hsd : SideRecordData hn g j hz hb hc t) (hs : CommonSupports g t) (b : Bool)
    (a : Mark g.center) :
    geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a)) =
      recastTuple (geoCornerCount_markTransport _ _ (hs b)
          (identify_sides_marks_of hn g j hz hb hc t hsd hs b) S a).symm
        (cornerFamily hn g j hz hb hc S (geoOwner (flatCentreCG hn g j hz hb hc) S a)
          (g.sideTime b t)) := by
  have hL := geoComponentCornerList_markTransport (flatCentreCG hn g j hz hb hc) (flatSideCG hn g b t)
    (hs b) (identify_sides_marks_of hn g j hz hb hc t hsd hs b) S a
  funext k
  rw [geoCornerPolygon_eq_markPolygon, cornerFamily_eq_markPolygon]
  unfold recastTuple
  erw [markPolygon_apply, markPolygon_apply]
  rw [markPointOn_side hn g b t hs]
  have h3 : k.val < ((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (geoOwner (flatCentreCG hn g j hz hb hc) S a)).map (markTransport (hs b))).length := by
    rw [hL]; exact ZMod.val_lt k
  have h4 := getElem_congr_lists _ _ hL.symm k.val k.val (ZMod.val_lt k) h3 rfl
  erw [h4, List.getElem_map]
  exact congrArg (fun m => traversalEvaluation (g.sideTuple b t).val
    (geoMarkPosition (flatSideCG hn g b t) (markTransport (hs b) m)))
    (getElem_congr_lists _ _ rfl _ _ _ _
      (zmod_val_cast (geoCornerCount_markTransport _ _ (hs b)
        (identify_sides_marks_of hn g j hz hb hc t hsd hs b) S a).symm k).symm)

/-- At a side time the family's one-component shadow is generic (it is the recast carrier shadow
of the side copy, `single_geo_generic`). -/
theorem cornerFamily_side_generic (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hk : 3 ≤ geoCornerCount (flatCentreCG hn g j hz hb hc) S q) :
    (Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q, hk,
      cornerFamily hn g j hz hb hc S q (g.sideTime b t)⟩).Generic := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  have hs : CommonSupports g t := flat_common_supports hn g j hz hb hc t hsd
  have hS_T := ((independent_supports_of hn g j hz hb hc t hsd hs S).1 b).mp hS
  have h := single_geo_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T
    (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))
  rw [geoCornerPolygon_side_eq_cornerFamily hn g j hz hb hc S t hsd hs b a,
    polyComp_recastTuple _ hk _ _] at h
  exact h

/-- The positive diagram of the side copy's corner polygon (= the positive lift of the accepted
side carrier, `positiveLift_eq_geo`) is the positive diagram of the family at the side time
(`geoCornerPolygon_side_eq_cornerFamily`, `polyComp_recastTuple`, `positiveDiagram_congr`). -/
theorem geoDiagram_side_eq_cornerFamily (t : g.SideParameter)
    (hsd : SideRecordData hn g j hz hb hc t) (hs : CommonSupports g t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hS_T : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    (Shadow.single ⟨geoCornerCount (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q),
        geoCornerCount_ge_three_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T _,
        geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)⟩).positiveDiagram
        (single_geo_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T _) =
      (Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
        geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF q,
        cornerFamily hn g j hz hb hc S q (g.sideTime b t)⟩).positiveDiagram
        (cornerFamily_side_generic hn g j hz hb hc S t hsd hS b q _) := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  apply positiveDiagram_congr
  show Shadow.single ⟨_, _, geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
      (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))⟩ = _
  rw [geoCornerPolygon_side_eq_cornerFamily hn g j hz hb hc S t hsd hs b a]
  exact congrArg Shadow.single (polyComp_recastTuple _ _ _ _)

/-- **The Deform through the flat centre.** Along `u ↦ cornerFamily S q (sideParamPath b t u)` the
corner polygon of the centre carrier moves continuously (`continuousAt_markPointOn_of` on the
family radius) from the centre corner polygon (`cornerFamily_zero`) to the side copy's; every
intermediate shadow is generic (`u = 0`: `centre_shadow_generic`; `u > 0`:
`cornerFamily_side_generic` at the side parameter `u · t`, `sideParamPath_eq_sideTime`); so
`homfly_positiveDiagram_single_of_family` identifies the HOMFLY polynomials (endpoints:
`cornerFamily_zero`, `geoDiagram_side_eq_cornerFamily`). Stated on the geo positive diagram of the
side copy (= the positive lift, `positiveLift_eq_geo`), as `cornerCoefficient_eq_geo` reads it. -/
theorem homfly_side_eq_centre {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hS_T : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    homfly ((Shadow.single ⟨geoCornerCount (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q),
        geoCornerCount_ge_three_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T _,
        geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)⟩).positiveDiagram
        (single_geo_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T _)) =
      homfly ((Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
        geoCornerCount_ge_three_centre hn g j hz hb hc t hs S (hδ.2.2.2 t ht) hS hF q,
        geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).positiveDiagram
        (centre_shadow_generic hn g j hz hb hc t hs S (hδ.2.2.2 t ht) hS hF q)) := by
  have hsd : SideRecordData hn g j hz hb hc t := hδ.2.2.2 t ht
  have hk : 3 ≤ geoCornerCount (flatCentreCG hn g j hz hb hc) S q :=
    geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF q
  -- continuity of the path of corner polygons
  have hΦ : Continuous (sideCornerPath hn g j hz hb hc S b t q) := by
    rw [continuous_iff_continuousAt]
    intro u
    apply continuousAt_pi.mpr
    intro k
    obtain ⟨hC, hcs⟩ := hδ.2.2.1 (sideParamPath g b t u) (abs_sideParamPath_lt g b t ht u)
    exact (continuousAt_markPointOn_of g (sideParamPath g b t u) hC hcs
      (geoCornerMark (flatCentreCG hn g j hz hb hc) S q k)).comp
      (continuous_sideParamPath g b t).continuousAt
  -- genericity at every time
  have hgen : ∀ u, (Shadow.single ⟨_, hk, sideCornerPath hn g j hz hb hc S b t q u⟩).Generic := by
    intro u
    by_cases hu : u.val = 0
    · have hu0 : u = 0 := Subtype.ext hu
      subst hu0
      rw [sideCornerPath_zero]
      exact centre_shadow_generic hn g j hz hb hc t hs S hsd hS hF q
    · have hu0 : 0 < u.val := lt_of_le_of_ne u.property.1 (Ne.symm hu)
      have hlt : u.val * t.val < δ :=
        lt_of_le_of_lt (mul_le_of_le_one_left t.property.1.le u.property.2) ht
      unfold sideCornerPath
      rw [sideParamPath_eq_sideTime g b t u hu0]
      exact cornerFamily_side_generic hn g j hz hb hc S _ (hδ.2.2.2 _ hlt) hS b q hk
  have hfam := Link.homfly_positiveDiagram_single_of_family hk _ hΦ hgen
  have h0 : (Shadow.single ⟨_, hk, sideCornerPath hn g j hz hb hc S b t q 0⟩).positiveDiagram (hgen 0) =
      (Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
        geoCornerCount_ge_three_centre hn g j hz hb hc t hs S (hδ.2.2.2 t ht) hS hF q,
        geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).positiveDiagram
        (centre_shadow_generic hn g j hz hb hc t hs S (hδ.2.2.2 t ht) hS hF q) :=
    positiveDiagram_congr (by rw [sideCornerPath_zero]) _ _
  have h1 : (Shadow.single ⟨_, hk, sideCornerPath hn g j hz hb hc S b t q 1⟩).positiveDiagram (hgen 1) =
      (Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
        geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF q,
        cornerFamily hn g j hz hb hc S q (g.sideTime b t)⟩).positiveDiagram
        (cornerFamily_side_generic hn g j hz hb hc S t hsd hS b q _) :=
    positiveDiagram_congr (by rw [sideCornerPath_one]) _ _
  rw [h0, h1] at hfam
  rw [geoDiagram_side_eq_cornerFamily hn g j hz hb hc S t hsd hs hS hF b q hS_T]
  exact hfam.symm

end DeformThroughCentre

/-! ## F. Corresponding carrier coefficients agree -/

section Coefficients

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))

/-- `c(Q)` of a side copy equals `c(Q)` of the deletion copy: equal slots (`card_geoCarrierCrossings_*`,
`rotationNumber_*`) and equal HOMFLY values (both equal the centre diagram's:
`homfly_side_eq_centre`, `homfly_deletion_eq_centre`), through `cornerCoefficient_eq_geo`. -/
theorem cornerCoefficient_side_eq_deletion {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hS_T : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    cornerCoefficient (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property _
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)) hS_T =
      cornerCoefficient hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) _
          ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)) hS_D := by
  rw [cornerCoefficient_eq_geo, cornerCoefficient_eq_geo]
  rw [card_geoCarrierCrossings_side hn g j hz hb hc t hs S hF b q]
  rw [card_geoCarrierCrossings_deletion hn g j hz hb hc t hs S hF q]
  rw [rotationNumber_side hn g j hz hb hc t hs S hF b q]
  rw [rotationNumber_deletion hn g j hz hb hc t hs S hF q]
  rw [homfly_side_eq_centre hn g j hz hb hc S hδ t ht hs hS hF b q hS_T]
  rw [homfly_deletion_eq_centre hn g j hz hb hc t hs S (hδ.2.2.2 t ht) hS hF q hS_D]

/-- The products of the carrier coefficients agree (`Fintype.prod_equiv` along
`geoEq_T ∘ sideCarrierEquiv ∘ deletionCarrierEquiv ∘ geoEq_D⁻¹`). -/
theorem cornerProduct_side_eq_deletion {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (hS_T : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    cornerProduct (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) hS_T =
      cornerProduct hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) hS_D := by
  unfold cornerProduct
  let e := ((geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) _).symm.trans
    ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).trans
      ((sideCarrierEquiv hn g j hz hb hc t hs S hF b).trans
        (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property _))))
  refine (Fintype.prod_equiv e _ _ fun qD => ?_).symm
  have h := cornerCoefficient_side_eq_deletion hn g j hz hb hc S hδ t ht hs hS hF b
    (deletionCarrierEquiv hn g j hz hb hc t hs S hF
      ((geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) _).symm qD)) hS_T hS_D
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
  exact h.symm

end Coefficients

/-! ## G. The selector algebra: `wind_R − wind_L = wind_D` -/

section SelectorAlgebra

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
  (S : Finset (Crossing g.center))

/-- `wind` of a side, indexed by the centre carriers. -/
theorem wind_side_eq_prod (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    wind (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) =
      ∏ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
        geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q) := by
  rw [wind_eq_prod_geoCarrierSelector]
  exact (Fintype.prod_equiv (sideCarrierEquiv hn g j hz hb hc t hs S hF b) _ _ fun _ => rfl).symm

/-- `wind` of the deletion, indexed by the centre carriers. -/
theorem wind_deletion_eq_prod (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    wind hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) =
      ∏ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
        geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q) := by
  rw [wind_eq_prod_geoCarrierSelector]
  exact (Fintype.prod_equiv (deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm _ _
    fun _ => rfl).symm

/-- "All other corresponding carrier selectors agree" (field `other_selectors_agree`), read on the
centre carriers: away from the carrier through `μ_j`, the side copy's selector is the deletion
copy's. -/
theorem selector_other (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hq : q ≠ centralCarrierThroughJ hn g j hz hb hc S) :
    geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q) =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q) := by
  obtain ⟨q', rfl⟩ := (deletionCarrierEquiv hn g j hz hb hc t hs S hF).surjective q
  obtain ⟨b', rfl⟩ := geoOwner_surjective (flatDeletionCG hn g j hz hb hc) _ q'
  rw [Equiv.symm_apply_apply, deletionCarrierEquiv_owner, sideCarrierEquiv_owner]
  rw [deletionCarrierEquiv_owner] at hq
  exact hF.other_selectors_agree b b' hq

/-- eq. ccf:distinguished-selector, read on the centre carriers (field `selector_identity` with
`sideCarrierEquiv_central`, `deletionCarrierEquiv_symm_central`). -/
theorem selector_central (hF : FlatCarriersData hn g j hz hb hc t hs S) (bR bL : Bool)
    (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    geoCarrierSelector (flatSideCG hn g bR t) (transportSupport (hs bR) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF bR (centralCarrierThroughJ hn g j hz hb hc S)) -
      geoCarrierSelector (flatSideCG hn g bL t) (transportSupport (hs bL) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF bL (centralCarrierThroughJ hn g j hz hb hc S)) =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm
          (centralCarrierThroughJ hn g j hz hb hc S)) := by
  rw [deletionCarrierEquiv_symm_central, sideCarrierEquiv_central, sideCarrierEquiv_central]
  exact hF.selector_identity bR bL hR hL

/-- eq. ccf:term-difference for the selectors: `wind_R − wind_L = wind_D`
(`Fintype.prod_eq_mul_prod_compl` at `q_*`, `selector_other` on the complement, `selector_central`;
`sub_mul`). -/
theorem wind_law (hF : FlatCarriersData hn g j hz hb hc t hs S) (bR bL : Bool)
    (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    wind (flat_hn1 hn) (g.sideTuple bR t).property (transportSupport (hs bR) S) -
        wind (flat_hn1 hn) (g.sideTuple bL t).property (transportSupport (hs bL) S) =
      wind hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) := by
  rw [wind_side_eq_prod hn g j hz hb hc t hs S hF bR, wind_side_eq_prod hn g j hz hb hc t hs S hF bL,
    wind_deletion_eq_prod hn g j hz hb hc t hs S hF,
    Fintype.prod_eq_mul_prod_compl (centralCarrierThroughJ hn g j hz hb hc S),
    Fintype.prod_eq_mul_prod_compl (centralCarrierThroughJ hn g j hz hb hc S),
    Fintype.prod_eq_mul_prod_compl (centralCarrierThroughJ hn g j hz hb hc S)]
  have hU : ∀ b : Bool, ∏ q ∈ ({centralCarrierThroughJ hn g j hz hb hc S} : Finset _)ᶜ,
      geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q) =
      ∏ q ∈ ({centralCarrierThroughJ hn g j hz hb hc S} : Finset _)ᶜ,
        geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q) := by
    intro b
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [Finset.mem_compl, Finset.mem_singleton] at hq
    exact selector_other hn g j hz hb hc t hs S hF b q hq
  rw [hU bR, hU bL, ← sub_mul, selector_central hn g j hz hb hc t hs S hF bR bL hR hL]

end SelectorAlgebra

/-! ## H. The state sums: reindexing over the centre's supports and the flat law at one `t` -/

section StateSum

variable {n : ℕ} [NeZero n]

/-- The summand of lem:C-X1 as a total function of the support (`0` off `Ind(G_P)`). -/
def stateTerm (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P)) : ℤ :=
  if h : IsDecomposition hn hP S then wind hn hP S * cornerProduct hn hP S h else 0

theorem stateTerm_of_not (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (h : ¬ IsDecomposition hn hP S) : stateTerm hn hP S = 0 :=
  dite_eq_right h

theorem stateTerm_of_decomposition (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (h : IsDecomposition hn hP S) :
    stateTerm hn hP S = wind hn hP S * cornerProduct hn hP S h :=
  dite_eq_left h

/-- lem:C-X1 as a sum over all supports (`C_X1.selector_form`, `Finset.sum_attach`,
completion by zeros). -/
theorem cornerStateSum_eq_sum_stateTerm (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    cornerStateSum hn hP = ∑ S : Finset (Crossing P), stateTerm hn hP S := by
  rw [C_X1.selector_form]
  have h1 : (∑ S ∈ (independentSupports hn hP).attach, wind hn hP S.1 * cornerProduct hn hP S.1 S.2) =
      ∑ S ∈ (independentSupports hn hP).attach, stateTerm hn hP S.1 :=
    Finset.sum_congr rfl fun S _ => (stateTerm_of_decomposition hn hP S.2).symm
  rw [h1, Finset.sum_attach]
  exact Finset.sum_subset (Finset.subset_univ _) fun S _ hS => stateTerm_of_not hn hP hS

/-- `Finset.map` along an equivalence, as an equivalence of finsets. -/
def finsetMapEquiv {α β : Type*} (e : α ≃ β) : Finset α ≃ Finset β where
  toFun S := S.map e.toEmbedding
  invFun S := S.map e.symm.toEmbedding
  left_inv S := by simp [Finset.map_map]
  right_inv S := by simp [Finset.map_map]

theorem sum_finsetMapEquiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : Finset β → ℤ) :
    ∑ S' : Finset β, f S' = ∑ S : Finset α, f (S.map e.toEmbedding) :=
  (Fintype.sum_equiv (finsetMapEquiv e) _ _ fun _ => rfl).symm

variable (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- The term-wise flat law: for every centre support `S`, the right term minus the left term is the
deletion term (off `GeoIndependent` all three vanish by `independent_supports_of`; on it,
`stateTerm_of_decomposition`, `cornerProduct_side_eq_deletion` twice, `wind_law`, `sub_mul`). -/
theorem stateTerm_law {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hF : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersData hn g j hz hb hc t hs S)
    (bR bL : Bool) (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t)
    (S : Finset (Crossing g.center)) :
    stateTerm (flat_hn1 hn) (g.sideTuple bR t).property (transportSupport (hs bR) S) -
        stateTerm (flat_hn1 hn) (g.sideTuple bL t).property (transportSupport (hs bL) S) =
      stateTerm hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) := by
  have hind := independent_supports_of hn g j hz hb hc t (hδ.2.2.2 t ht) hs S
  by_cases hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S
  · have hR' := (hind.1 bR).mp hS
    have hL' := (hind.1 bL).mp hS
    have hD' := hind.2.mp hS
    rw [stateTerm_of_decomposition _ _ hR', stateTerm_of_decomposition _ _ hL',
      stateTerm_of_decomposition _ _ hD',
      cornerProduct_side_eq_deletion hn g j hz hb hc S hδ t ht hs hS (hF S hS) bR hR' hD',
      cornerProduct_side_eq_deletion hn g j hz hb hc S hδ t ht hs hS (hF S hS) bL hL' hD',
      ← sub_mul, wind_law hn g j hz hb hc t hs S (hF S hS) bR bL hR hL]
  · rw [stateTerm_of_not _ _ (fun h => hS ((hind.1 bR).mpr h)),
      stateTerm_of_not _ _ (fun h => hS ((hind.1 bL).mpr h)),
      stateTerm_of_not _ _ (fun h => hS (hind.2.mpr h))]
    simp

/-- The flat law at one side parameter `t` below the radii of cor:flat-carriers and of the family
data: `C(P(bR, t)) − C(P(bL, t)) = C(P(0) ∖ j)`. -/
theorem flat_law_at {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hF : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersData hn g j hz hb hc t hs S)
    (bR bL : Bool) (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    cornerStateSum (flat_hn1 hn) (g.sideTuple bR t).property -
        cornerStateSum (flat_hn1 hn) (g.sideTuple bL t).property =
      cornerStateSum hn (generic_deleteVertex hn hz hb hc) := by
  rw [cornerStateSum_eq_sum_stateTerm, cornerStateSum_eq_sum_stateTerm, cornerStateSum_eq_sum_stateTerm,
    sum_finsetMapEquiv (crossingTransport (hs bR)), sum_finsetMapEquiv (crossingTransport (hs bL)),
    sum_finsetMapEquiv (fusionCrossingEquiv hn hz hb hc), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun S _ => stateTerm_law hn g j hz hb hc hδ t ht hs hF bR bL hR hL S

end StateSum

/-! ## I. Reduction to one side parameter, and the theorem -/

section Reduction

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))

omit [NeZero n] in
/-- "Proposition prop:C-chamber supplies the well-defined side values": along one side the state
sum is constant (`GermSides.sideTuple_mem_labelledSide`, `labelledSide_eq_at`,
`cornerStateSum_eq_of_mem_labelledChamber`). -/
theorem cornerStateSum_side_const (b : Bool) (t t' : g.SideParameter) :
    cornerStateSum (flat_hn1 hn) (g.sideTuple b t).property =
      cornerStateSum (flat_hn1 hn) (g.sideTuple b t').property := by
  have h : g.sideTuple b t' ∈ labelledChamber (g.sideTuple b t) := by
    rw [← g.labelledSide_eq_at b t]
    exact g.sideTuple_mem_labelledSide b t'
  exact cornerStateSum_eq_of_mem_labelledChamber (flat_hn1 hn) h

omit [NeZero n] in
/-- The turn at `j` is constant along one side (`generic_family_turn_constant` on the connected
side-parameter interval). -/
theorem side_turn_const (b : Bool) (t t' : g.SideParameter) :
    turn (g.sideTuple b t).val j = turn (g.sideTuple b t').val j :=
  Carrier.generic_family_turn_constant (g.continuous_sideTuple b) t t' j

omit [NeZero n] in
theorem isLeftSide_of_side (b : Bool) (t t' : g.SideParameter) (h : IsLeftSide g j b t) :
    IsLeftSide g j b t' := by
  unfold IsLeftSide at *
  rw [← side_turn_const g j b t t']
  exact h

end Reduction

/-- thm:C-S3 as printed (statement verbatim from work/drafts/CS3_statement.lean). -/
structure CS3Data : Prop where
  /-- eq. ccf:flat-law: `C(P_right) − C(P_left) = C(P(0) ∖ j)` at a simple flat wall, for the polygons of the two
  sides at all sufficiently small side parameters. -/
  flat_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (_hsc : g.SignChanges (fun P => (turn P j : ℝ))),
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧
      ∀ (bR bL : Bool) (tR tL : g.SideParameter), tR.val < δ → tL.val < δ →
        IsRightSide g j bR tR → IsLeftSide g j bL tL →
        cornerStateSum (flat_hn1 hn) (g.sideTuple bR tR).property -
            cornerStateSum (flat_hn1 hn) (g.sideTuple bL tL).property =
          cornerStateSum hn (generic_deleteVertex hn hz hb hc)

/-- **thm:C-S3.** The radius is the minimum of cor:flat-carriers' radius (`flat_carriers`) and the
family radius (`exists_flatFamilyData`); the left side is moved to the right side's parameter
(`cornerStateSum_side_const`, `isLeftSide_of_side`) and `flat_law_at` closes. -/
theorem thm_C_S3 : CS3Data where
  flat_law := by
    intro n _ hn g j hz hb hc hsc
    obtain ⟨δC, hδC, hδCr, hFC⟩ := flat_carriers hn g hz hb hc hsc
    obtain ⟨δF, hδF⟩ := exists_flatFamilyData hn g j hz hb hc hsc
    refine ⟨min δC δF, lt_min hδC hδF.1, (min_le_left _ _).trans hδCr, ?_⟩
    intro bR bL tR tL htR htL hR hL
    have htRC : tR.val < δC := lt_of_lt_of_le htR (min_le_left _ _)
    have htRF : tR.val < δF := lt_of_lt_of_le htR (min_le_right _ _)
    obtain ⟨hs, hF⟩ := hFC tR htRC
    rw [cornerStateSum_side_const hn g bL tL tR]
    exact flat_law_at hn g j hz hb hc hδF tR htRF hs hF bR bL hR
      (isLeftSide_of_side g j bL tL tR hL)

end

end SM
