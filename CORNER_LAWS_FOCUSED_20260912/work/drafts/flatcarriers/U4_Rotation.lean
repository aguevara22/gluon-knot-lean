import SM.FlatCarriersDefs
import SM.AppendRotation
import SM.RegularPerturbation
import SM.GermNeighborhood
import SM.GeometricParameters

/-! # U4 — Rotation (cor:flat-carriers (ii), field `same_rotation`)

Prover unit U4 of work/drafts/flatcarriers/PLAN_FINAL.md §5 for def:flat-carriers /
cor:flat-carriers (reference/SM/sm-3-statesum.tex:788-905; the rotation paragraph of the printed
proof is 866-893). Statement design: SM/FlatCarriersDefs.lean (`SM.FlatCarriersData.same_rotation`).

Contents.
* §A: re-indexing closed polygons (`Reindexed`: equal size + cyclic shift, transported through
  `ℕ`-casts so that polygons on different `ZMod` index types can be compared — plan risk 3);
  `rotationNumber` and `Regular` are invariant.
* §B: closed polygons read off a list of marks (`markPolygon`): rotation of the list, `map`,
  pointwise congruence, appending a last vertex (`appendVertex`), the sub-list embedding.
* §C: the list-level theorem `rotationNumber_erase_flat`: erasing one positively flat vertex from a
  regular closed polygon keeps the rotation number (printed: "removing it merely fuses those
  segments"; accepted `rotationNumber_appendVertex`).
* §D: the deletion half of `same_rotation`: the deletion copy of every centre carrier has the
  centre copy's signed (hence absolute) rotation — through `μ_j` by §C, elsewhere by an equal
  corner cycle.
* §E: the side half (the printed limit argument): the corner polygons of the side copies form a
  family continuous in the germ parameter (vertices by `g.continuous_curve`, crossing points by
  Cramer's rule, `continuousAt_edgeParameter_of_geometry`), regular at the centre, so
  `rotationNumber_locally_constant` gives a common radius `δ_rot` for all supports and carriers.
* §F: `same_rotation`: the field of `FlatCarriersData` from the U2/U3 interface hypotheses.

Interface hypotheses (assumed explicitly as arguments, never `sorry`; each is a projection of a
`FlatCarriersData` field or a U2 lemma — checked by an `example` against the field projections
`correspond_deletion.2.1`, `central_vs_deletion_through_mu_j.1`/`.2.2.1`, `others_unchanged _ _ |>.2.1`,
`nonzero_segments.2.1`/`.2.2.2.1`, `no_antiparallel.1`/`.2.1`, `turns_nonzero.1`, and the conclusion of
`same_rotation` is definitionally the field `same_rotation`):
U2 — `hown` (`correspond_deletion.2`: owner-iff through `fusionMark`), `hsucc`
(`central_vs_deletion_through_mu_j.1`: `ρ_S^C μ_j ≠ μ_j`), `hcycJ` (`.3`: corner cycle of the `μ_j`
carrier with `μ_j` erased = deletion copy's), `hcycO` (`others_unchanged.2`: corner cycles of the
other carriers), and the side corner-list identification `hcorr`
(`(geoComponentCornerList C S (owner a)).map (markTransport (hs b)) = geoComponentCornerList T S_T
(owner (markTransport a))`, U2.2 applied at each `t`).
U3 — at the centre (for every independent `S`): nonzero corner-polygon edges `hneC`, no antiparallel
corner `hnaC` (`nonzero_segments.2`, `no_antiparallel.1`; together `Regular`), and the turn clause
`turn = 0 ↔ corner = μ_j` (`turns_nonzero.1`); on the deletion: nonzero corner-polygon edges, no
antiparallel corner (`nonzero_segments.4`, `no_antiparallel.2`).
Everything else is proved here; axioms `propext, Classical.choice, Quot.sound` only. -/

namespace SM

open GeoCarrier Carrier
open Filter Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## A. Re-indexing closed polygons -/

/-- `Q'` is `Q` re-indexed along an equality of sizes and cyclically shifted by `r` steps:
`Q' k = Q (k + r)`, written through `ℕ`-casts so that the two index types may differ
syntactically. -/
def Reindexed {m m' : ℕ} (Q : LabelledTuple m) (Q' : LabelledTuple m') : Prop :=
  m = m' ∧ ∃ r : ℕ, ∀ k : ZMod m', Q' k = Q ((k.val + r : ℕ) : ZMod m)

theorem reindexed_refl {m : ℕ} [NeZero m] (Q : LabelledTuple m) : Reindexed Q Q :=
  ⟨rfl, 0, fun k => by rw [Nat.add_zero, ZMod.natCast_zmod_val]⟩

/-- Along an equality of sizes a re-indexed polygon is a cyclic shift. -/
theorem reindexed_eq_shift {m : ℕ} [NeZero m] {Q Q' : LabelledTuple m} (h : Reindexed Q Q') :
    ∃ r : ZMod m, Q' = shift r Q := by
  obtain ⟨_, r, hr⟩ := h
  refine ⟨(r : ZMod m), funext fun k => ?_⟩
  rw [hr k, shift, Nat.cast_add, ZMod.natCast_zmod_val]

theorem rotationNumber_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m'] {Q : LabelledTuple m}
    {Q' : LabelledTuple m'} (h : Reindexed Q Q') : rotationNumber Q' = rotationNumber Q := by
  obtain ⟨hm, -⟩ := id h
  subst hm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  exact rotationNumber_shift r Q

theorem regular_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m'] {Q : LabelledTuple m}
    {Q' : LabelledTuple m'} (h : Reindexed Q Q') : Regular Q' ↔ Regular Q := by
  obtain ⟨hm, -⟩ := id h
  subst hm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  exact regular_shift r Q

/-- Re-indexing without a shift: `Q' k = Q k` through the cast. -/
theorem reindexed_of_cast {m m' : ℕ} {Q : LabelledTuple m} {Q' : LabelledTuple m'} (h : m = m')
    (hQ : ∀ k : ZMod m', Q' k = Q ((k.val : ℕ) : ZMod m)) : Reindexed Q Q' :=
  ⟨h, 0, fun k => by rw [hQ k, Nat.add_zero]⟩

/-! ## B. Closed polygons read off a list of marks -/

/-- The closed polygon whose `k`-th vertex is the plane point `f` of the `k`-th entry of `L`. -/
def markPolygon {α : Type*} (f : α → Plane) (L : List α) [NeZero L.length] :
    LabelledTuple L.length :=
  fun k => f (L[k.val]'(ZMod.val_lt k))

theorem markPolygon_apply {α : Type*} (f : α → Plane) (L : List α) [NeZero L.length]
    (k : ZMod L.length) : markPolygon f L k = f (L[k.val]'(ZMod.val_lt k)) := rfl

theorem getElem_idx_congr {α : Type*} (L : List α) {i i' : ℕ} (h : i = i') (hi : i < L.length)
    (hi' : i' < L.length) : L[i]'hi = L[i']'hi' := by
  subst h
  rfl

/-- The corner list of a carrier is nonempty (`geoCornerCount_neZero`, restated on the list's
length so that `markPolygon` finds one canonical instance). -/
instance geoComponentCornerList_length_neZero {n : ℕ} [NeZero n] {P : LabelledTuple n}
    (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    NeZero (geoComponentCornerList hP S q).length :=
  geoCornerCount_neZero hP S q

/-- The corner polygon of a carrier is the polygon read off its corner list. -/
theorem geoCornerPolygon_eq_markPolygon {n : ℕ} [NeZero n] {P : LabelledTuple n}
    (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCornerPolygon hP S q =
      markPolygon (fun m => traversalEvaluation P (geoMarkPosition hP m))
        (geoComponentCornerList hP S q) := rfl

/-- Rotating the list by `r` cyclically shifts the polygon by `r`. -/
theorem markPolygon_rotate_apply {α : Type*} (f : α → Plane) {L L' : List α} {r : ℕ}
    (h : L.rotate r = L') [NeZero L.length] [NeZero L'.length] (k : ZMod L'.length) :
    markPolygon f L' k = markPolygon f L ((k.val + r : ℕ) : ZMod L.length) := by
  subst h
  simp only [markPolygon]
  congr 1
  rw [List.getElem_rotate]
  exact getElem_idx_congr L (ZMod.val_natCast _ _).symm _ _

theorem reindexed_markPolygon_of_rotate {α : Type*} (f : α → Plane) {L L' : List α} {r : ℕ}
    (h : L.rotate r = L') [NeZero L.length] [NeZero L'.length] :
    Reindexed (markPolygon f L) (markPolygon f L') :=
  ⟨by rw [← h, List.length_rotate], r, markPolygon_rotate_apply f h⟩

theorem reindexed_markPolygon_of_isRotated {α : Type*} (f : α → Plane) {L L' : List α}
    (h : L ~r L') [NeZero L.length] [NeZero L'.length] :
    Reindexed (markPolygon f L) (markPolygon f L') := by
  obtain ⟨r, hr⟩ := h
  exact reindexed_markPolygon_of_rotate f hr

/-- Reading a mapped list is reading the list through the composite. -/
theorem reindexed_markPolygon_map {α β : Type*} (f : β → Plane) (g : α → β) (L : List α)
    [NeZero L.length] [NeZero (L.map g).length] :
    Reindexed (markPolygon (f ∘ g) L) (markPolygon f (L.map g)) := by
  have hlen : (L.map g).length = L.length := by simp
  refine reindexed_of_cast hlen.symm fun k => ?_
  have hk : k.val < L.length := hlen ▸ ZMod.val_lt k
  simp only [markPolygon, List.getElem_map, Function.comp]
  congr 2
  exact getElem_idx_congr L (ZMod.val_natCast_of_lt hk).symm _ _

theorem markPolygon_congr {α : Type*} {f f' : α → Plane} (L : List α) [NeZero L.length]
    (h : ∀ a ∈ L, f a = f' a) : markPolygon f L = markPolygon f' L := by
  funext k
  exact h _ (List.getElem_mem _)

/-- The sub-list embedding: the first `M.length` vertices of `M ++ [x]` are those of `M`. -/
theorem markPolygon_append_singleton_cast {α : Type*} (f : α → Plane) (M : List α) (x : α)
    [NeZero M.length] [NeZero (M ++ [x]).length] (k : ZMod M.length) :
    markPolygon f (M ++ [x]) ((k.val : ℕ) : ZMod (M ++ [x]).length) = markPolygon f M k := by
  have hk : k.val < (M ++ [x]).length := by
    rw [List.length_append, List.length_singleton]
    exact (ZMod.val_lt k).trans (Nat.lt_succ_self _)
  simp only [markPolygon]
  congr 1
  rw [getElem_idx_congr (M ++ [x]) (ZMod.val_natCast_of_lt hk) _ hk]
  exact List.getElem_append_left (ZMod.val_lt k)

/-- Appending a vertex: the polygon of `M ++ [x]` is `appendVertex` of the polygon of `M` when
`f x` is the point at parameter `t` of the closing edge of the latter. -/
theorem reindexed_appendVertex_markPolygon {α : Type*} (f : α → Plane) (M : List α) (x : α)
    [NeZero M.length] [NeZero (M ++ [x]).length] {t : ℝ}
    (hx : f x = edgePoint (markPolygon f M) (-1) t) :
    Reindexed (appendVertex (markPolygon f M) t) (markPolygon f (M ++ [x])) := by
  have hlen : (M ++ [x]).length = M.length + 1 := by
    rw [List.length_append, List.length_singleton]
  refine reindexed_of_cast hlen.symm fun k => ?_
  have hk : k.val < M.length + 1 := hlen ▸ ZMod.val_lt k
  rw [appendVertex, ZMod.val_natCast_of_lt hk]
  split_ifs with hlt
  · simp only [markPolygon]
    congr 1
    rw [List.getElem_append_left hlt]
    exact getElem_idx_congr M (ZMod.val_natCast_of_lt hlt).symm _ _
  · have hkm : k.val = M.length := by omega
    rw [← hx, markPolygon]
    exact congrArg f (List.getElem_concat_length hkm _)

/-! ## C. Erasing a positively flat vertex -/

/-- `Mark P = ZMod n ⊕ Visit P` carries `Sum.instBEq`; it is lawful when both summands' `BEq` are
(needed for `List.erase` on mark lists). -/
instance sumLawfulBEq {α β : Type*} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  eq_of_beq {a b} h := by
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (eq_of_beq (a := a) (b := b) h)
      | inr b => exact absurd h Bool.false_ne_true
    | inr a =>
      cases b with
      | inl b => exact absurd h Bool.false_ne_true
      | inr b => exact congrArg Sum.inr (eq_of_beq (a := a) (b := b) h)
  rfl {a} := by
    cases a with
    | inl a => exact beq_self_eq_true a
    | inr a => exact beq_self_eq_true a

theorem zmod_val_neg_one (m : ℕ) [NeZero m] : (-1 : ZMod m).val = m - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  exact ZMod.val_neg_one k

theorem zmod_natCast_pred (m : ℕ) [NeZero m] : ((m - 1 : ℕ) : ZMod m) = -1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  rw [Nat.succ_sub_one]
  apply eq_neg_of_add_eq_zero_left
  rw [← Nat.cast_succ, ZMod.natCast_self]

/-- Erasing one positively flat vertex `x` from the closed polygon read off a duplicate-free list
`L` keeps the rotation number (printed: "removing it merely fuses those segments"): if `L'` is a
rotation of `L` with `x` erased, read through `g` with the same plane points, `f x` is positively
flat between its two neighbours, and the polygon of `L'` is regular, the rotation numbers agree.
Route: rotate `L` to `M ++ [x]`, then `markPolygon f (M ++ [x])` is `appendVertex (markPolygon f M) t`
(`rotationNumber_appendVertex`), and `M` is a rotation of `L'` read back. -/
theorem rotationNumber_erase_flat {α β : Type*} [BEq α] [LawfulBEq α]
    (f : α → Plane) (L : List α) [NeZero L.length] (hnd : L.Nodup) {x : α} (hx : x ∈ L)
    (hflat : ∀ k : ZMod L.length, L[k.val]'(ZMod.val_lt k) = x →
      ∃ s : ℝ, 0 < s ∧ edge (markPolygon f L) k = s • edge (markPolygon f L) (k - 1))
    (g : α → β) (f' : β → Plane) (hf' : ∀ a ∈ L, a ≠ x → f' (g a) = f a)
    (L' : List β) [NeZero L'.length] (hL' : (L.erase x).map g ~r L')
    (hreg : Regular (markPolygon f' L')) :
    rotationNumber (markPolygon f L) = rotationNumber (markPolygon f' L') := by
  obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem hx
  subst hL
  obtain ⟨-, hnd2, hdisj⟩ := List.nodup_append.mp hnd
  have hx1 : x ∉ L₁ := fun h => hdisj x h x (List.mem_cons_self ..) rfl
  have hx2 : x ∉ L₂ := (List.nodup_cons.mp hnd2).1
  have herase : (L₁ ++ x :: L₂).erase x = L₁ ++ L₂ := by
    rw [List.erase_append_right _ hx1, List.erase_cons_head]
  rw [herase] at hL'
  -- lengths and the needed `NeZero` instances
  have hlenL : (L₁ ++ x :: L₂).length = (L₂ ++ L₁).length + 1 := by simp; omega
  have hlenL' : L'.length = (L₂ ++ L₁).length := by
    rw [← hL'.perm.length_eq, List.length_map]; simp; omega
  have hlen12 : (L₁ ++ L₂).length = (L₂ ++ L₁).length := by simp; omega
  have hMne : NeZero (L₂ ++ L₁).length := ⟨hlenL' ▸ NeZero.ne _⟩
  have : NeZero (L₁ ++ L₂).length := ⟨hlen12 ▸ NeZero.ne _⟩
  have : NeZero ((L₁ ++ L₂).map g).length := ⟨by rw [List.length_map]; exact NeZero.ne _⟩
  have : NeZero ((L₂ ++ L₁) ++ [x]).length := ⟨by simp⟩
  -- the deletion polygon is (a re-indexing of) the polygon of `M = L₂ ++ L₁`
  have h1 : Reindexed (markPolygon f' ((L₁ ++ L₂).map g)) (markPolygon f' L') :=
    reindexed_markPolygon_of_isRotated f' hL'
  have h2 : Reindexed (markPolygon (f' ∘ g) (L₁ ++ L₂)) (markPolygon f' ((L₁ ++ L₂).map g)) :=
    reindexed_markPolygon_map f' g (L₁ ++ L₂)
  have h3 : markPolygon (f' ∘ g) (L₁ ++ L₂) = markPolygon f (L₁ ++ L₂) := by
    apply markPolygon_congr
    intro a ha
    have hmem : a ∈ L₁ ++ x :: L₂ := by
      simp only [List.mem_append, List.mem_cons] at ha ⊢
      tauto
    have hne : a ≠ x := by
      rintro rfl
      simp only [List.mem_append] at ha
      exact ha.elim hx1 hx2
    exact hf' a hmem hne
  have h4 : Reindexed (markPolygon f (L₁ ++ L₂)) (markPolygon f (L₂ ++ L₁)) :=
    reindexed_markPolygon_of_isRotated f List.isRotated_append
  have hrotL' : rotationNumber (markPolygon f' L') = rotationNumber (markPolygon f (L₂ ++ L₁)) := by
    rw [rotationNumber_of_reindexed h1, rotationNumber_of_reindexed h2, h3,
      ← rotationNumber_of_reindexed h4]
  have hregM : Regular (markPolygon f (L₂ ++ L₁)) := by
    rw [regular_of_reindexed h4, ← h3, ← regular_of_reindexed h2, ← regular_of_reindexed h1]
    exact hreg
  -- the centre polygon is (a re-indexing of) the polygon of `M ++ [x]`
  have hrotate : (L₁ ++ x :: L₂).rotate (L₁.length + 1) = (L₂ ++ L₁) ++ [x] := by
    have he : L₁ ++ x :: L₂ = (L₁ ++ [x]) ++ L₂ := by simp
    have hl : (L₁ ++ [x]).length = L₁.length + 1 := by simp
    rw [he, ← hl, List.rotate_append_length_eq, List.append_assoc]
  have h5 : Reindexed (markPolygon f (L₁ ++ x :: L₂)) (markPolygon f ((L₂ ++ L₁) ++ [x])) :=
    reindexed_markPolygon_of_rotate f hrotate
  have hQ' := markPolygon_rotate_apply f hrotate (L := L₁ ++ x :: L₂)
  -- the flat vertex `x` sits at the index `k₀ = L₁.length` of `L`
  set c := (L₁ ++ x :: L₂).length with hc
  have hL₁c : L₁.length < c := by rw [hc]; simp
  set k₀ : ZMod c := ((L₁.length : ℕ) : ZMod c) with hk₀
  have hk₀v : k₀.val = L₁.length := ZMod.val_natCast_of_lt hL₁c
  have hk₀x : (L₁ ++ x :: L₂)[k₀.val]'(ZMod.val_lt k₀) = x := by
    rw [getElem_idx_congr _ hk₀v _ hL₁c, List.getElem_append_right (le_refl _)]
    simp
  obtain ⟨s, hs0, hs⟩ := hflat k₀ hk₀x
  -- the three relevant vertices of `M ++ [x]` and `M` read on `L`
  have hQx : markPolygon f (L₁ ++ x :: L₂) k₀ = f x := by
    rw [markPolygon_apply, hk₀x]
  have hP0 : markPolygon f (L₂ ++ L₁) 0 = markPolygon f (L₁ ++ x :: L₂) (k₀ + 1) := by
    rw [← markPolygon_append_singleton_cast f (L₂ ++ L₁) x 0, hQ', ZMod.val_zero, Nat.cast_zero,
      ZMod.val_zero, Nat.zero_add, Nat.cast_add, Nat.cast_one]
  have hPlast : markPolygon f (L₂ ++ L₁) (-1) = markPolygon f (L₁ ++ x :: L₂) (k₀ - 1) := by
    rw [← markPolygon_append_singleton_cast f (L₂ ++ L₁) x (-1), hQ']
    congr 1
    have hlt : (-1 : ZMod (L₂ ++ L₁).length).val < ((L₂ ++ L₁) ++ [x]).length :=
      lt_of_lt_of_le (ZMod.val_lt _) (by simp)
    rw [ZMod.val_natCast_of_lt hlt, zmod_val_neg_one]
    have hM1 : 1 ≤ (L₂ ++ L₁).length := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    have he : (L₂ ++ L₁).length - 1 + (L₁.length + 1) = (c - 1) + L₁.length := by omega
    rw [he, Nat.cast_add, zmod_natCast_pred, hk₀]
    ring
  -- positive flatness at `x`: `f x = edgePoint (markPolygon f M) (-1) t`, `t = 1 / (1 + s)`
  have hs' : markPolygon f (L₁ ++ x :: L₂) (k₀ + 1) - markPolygon f (L₁ ++ x :: L₂) k₀ =
      s • (markPolygon f (L₁ ++ x :: L₂) k₀ - markPolygon f (L₁ ++ x :: L₂) (k₀ - 1)) := by
    have := hs
    simp only [edge, sub_add_cancel] at this
    exact this
  have hu : markPolygon f (L₁ ++ x :: L₂) (k₀ + 1) - markPolygon f (L₁ ++ x :: L₂) (k₀ - 1) =
      (1 + s) • (markPolygon f (L₁ ++ x :: L₂) k₀ - markPolygon f (L₁ ++ x :: L₂) (k₀ - 1)) := by
    rw [add_smul, one_smul, ← hs']
    abel
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hx' : f x = edgePoint (markPolygon f (L₂ ++ L₁)) (-1) (1 / (1 + s)) := by
    rw [edgePoint, edge, neg_add_cancel, hP0, hPlast, ← hQx, hu, smul_smul, one_div,
      inv_mul_cancel₀ h1s.ne', one_smul]
    abel
  have h6 : Reindexed (appendVertex (markPolygon f (L₂ ++ L₁)) (1 / (1 + s)))
      (markPolygon f ((L₂ ++ L₁) ++ [x])) :=
    reindexed_appendVertex_markPolygon f (L₂ ++ L₁) x hx'
  have ht0 : (0 : ℝ) < 1 / (1 + s) := div_pos one_pos h1s
  have ht1 : 1 / (1 + s) < 1 := (div_lt_one h1s).mpr (by linarith)
  calc rotationNumber (markPolygon f (L₁ ++ x :: L₂))
      = rotationNumber (markPolygon f ((L₂ ++ L₁) ++ [x])) :=
        (rotationNumber_of_reindexed h5).symm
    _ = rotationNumber (appendVertex (markPolygon f (L₂ ++ L₁)) (1 / (1 + s))) :=
        rotationNumber_of_reindexed h6
    _ = rotationNumber (markPolygon f (L₂ ++ L₁)) := rotationNumber_appendVertex hregM ht0 ht1
    _ = rotationNumber (markPolygon f' L') := hrotL'.symm

/-! ## D. The deletion half of `same_rotation` -/

section Deletion

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)

/-- The plane point of a centre mark other than `μ_j`, read on the deletion through `delMark`, is
its centre point (a vertex by `deleteVertex_apply`, a visit by `crossingPoint_fusion`). -/
theorem deletion_mark_point (a : Mark g.center) (ha : a ≠ Sum.inl j) :
    traversalEvaluation (deleteVertex g.center j)
      (geoMarkPosition (flatDeletionCG hn g j hz hb hc) (delMark hn g j hz hb hc a)) =
    traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) := by
  cases a with
  | inl k =>
    have hk : k ≠ j := fun h => ha (congrArg Sum.inl h)
    show traversalEvaluation _ (geoMarkPosition _ (Sum.inl (fusionIndex j k))) = _
    rw [geoMarkPosition_evaluation_vertex, geoMarkPosition_evaluation_vertex, deleteVertex_apply]
    obtain ⟨i, rfl⟩ := deletionIndex_exhaust j hk
    rw [fusionIndex_deletionIndex]
  | inr v =>
    show traversalEvaluation _ (geoMarkPosition _ (Sum.inr (fusionVisitEquiv hn hz hb hc v))) = _
    rw [geoMarkPosition_evaluation_visit, geoMarkPosition_evaluation_visit]
    exact crossingPoint_fusion hn hz hb hc v.1

/-- The plane point of a deletion mark read at the centre through `fusionMark` is its deletion
point. -/
theorem fusion_mark_point (b : Mark (deleteVertex g.center j)) :
    traversalEvaluation g.center
      (geoMarkPosition (flatCentreCG hn g j hz hb hc) (fusionMark hn g j hz hb hc b)) =
    traversalEvaluation (deleteVertex g.center j)
      (geoMarkPosition (flatDeletionCG hn g j hz hb hc) b) := by
  rw [← deletion_mark_point hn g j hz hb hc _ (fusionMark_ne_deleted hn g j hz hb hc b),
    delMark_fusionMark]

/-- Positive flatness of a regular corner polygon at a corner with zero turn. -/
theorem flat_of_turn_eq_zero {m : ℕ} {Q : LabelledTuple m} (hreg : Regular Q) {k : ZMod m}
    (h : turn Q k = 0) : ∃ s : ℝ, 0 < s ∧ edge Q k = s • edge Q (k - 1) := by
  have hdet : det (edge Q (k - 1)) (edge Q k) = 0 := by
    rw [turn_det] at h
    exact sign_eq_zero_iff.mp h
  exact (principalAngle_eq_zero_iff (hreg k).1 (hreg k).2.1).mp
    ((principalAngle_zero_iff_det_zero (hreg k)).mpr hdet)

/-- Deletion ↔ centre for the carrier through `μ_j` (printed: "removing it merely fuses those
segments"): the deletion copy's corner polygon is the central one with the positively flat corner
`μ_j` erased, so the rotation numbers agree. Inputs: the corner-cycle identity
(`central_vs_deletion_through_mu_j.3`, U2), and the U3 centre/deletion regularity facts. -/
theorem rotationNumber_deletionCopyThroughJ (S : Finset (Crossing g.center))
    (hcyc : ((((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))))
    (hne : ∀ k : ZMod (geoCornerCount _ S (centralCarrierThroughJ hn g j hz hb hc S)),
      edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)) k ≠ 0)
    (hna : ∀ k : ZMod (geoCornerCount _ S (centralCarrierThroughJ hn g j hz hb hc S)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S)) k =
          r • edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
            (centralCarrierThroughJ hn g j hz hb hc S)) (k - 1))
    (hturn : ∀ k : ZMod (geoCornerCount _ S (centralCarrierThroughJ hn g j hz hb hc S)),
      turn (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)) k = 0 ↔
        geoCornerMark (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S) k = Sum.inl j)
    (hneD : ∀ k : ZMod (geoCornerCount _ _ (deletionCopyThroughJ hn g j hz hb hc S)),
      edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S)) k ≠ 0)
    (hnaD : ∀ k : ZMod (geoCornerCount _ _ (deletionCopyThroughJ hn g j hz hb hc S)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (deletionCopyThroughJ hn g j hz hb hc S)) k =
          r • edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
            (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) (k - 1)) :
    rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)) := by
  have hregC : Regular (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
      (centralCarrierThroughJ hn g j hz hb hc S)) :=
    (regular_iff_edges _).mpr fun k => ⟨hne k, hna k⟩
  have hregD : Regular (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) :=
    (regular_iff_edges _).mpr fun k => ⟨hneD k, hnaD k⟩
  symm
  refine rotationNumber_erase_flat
    (fun m => traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) m))
    (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (centralCarrierThroughJ hn g j hz hb hc S))
    (geoComponentCornerList_nodup _ _ _) (x := Sum.inl j)
    ((mem_geoComponentCornerList _ _ _ _).mpr ⟨rfl, isTrueCorner_vertex S j⟩)
    (fun k hk => flat_of_turn_eq_zero hregC ((hturn k).mpr hk))
    (delMark hn g j hz hb hc)
    (fun m => traversalEvaluation (deleteVertex g.center j)
      (geoMarkPosition (flatDeletionCG hn g j hz hb hc) m))
    (fun a _ ha => deletion_mark_point hn g j hz hb hc a ha)
    (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (deletionCopyThroughJ hn g j hz hb hc S))
    (Cycle.coe_eq_coe.mp hcyc) hregD

/-- Deletion ↔ centre for every other carrier (printed: "every other central carrier is unchanged
by deletion"): equal corner cycles give equal rotation numbers. Input: the corner-cycle identity
of `others_unchanged.2` (U2). -/
theorem rotationNumber_others_unchanged (S : Finset (Crossing g.center))
    (b : Mark (deleteVertex g.center j))
    (hcyc : (((geoComponentCornerList (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
          (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
      (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
          Cycle (Mark g.center))) :
    rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))) := by
  have hrot := Cycle.coe_eq_coe.mp hcyc
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
  exact ((rotationNumber_of_reindexed h1).trans
    ((rotationNumber_of_reindexed h2).trans (congrArg rotationNumber h3))).symm

end Deletion

/-! ## E. The side half of `same_rotation` (the printed limit argument) -/

section Sides

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)

/-- The plane point of a centre mark read on the polygon `g.curve s`: a vertex by its label, a
visit as the Cramer crossing point of its two edge labels (`edgeParameter`). At `s = 0` this is the
mark's point at the centre, at a side parameter it is the point of the transported mark; it is
continuous in `s` at the centre ("corners are vertices and Cramer crossing points"). -/
def markPointOn (s : g.Parameter) : Mark g.center → Plane
  | Sum.inl i => g.curve s i
  | Sum.inr v => edgePoint (g.curve s) v.2.val
      (edgeParameter (g.curve s) v.2.val (visitTwin v).2.val)

omit [NeZero n] in
/-- On any polygon with crossing geometry, the point of a visit is the Cramer crossing point of its
edge and its twin's edge. -/
theorem visit_point_eq_edgePoint {P : LabelledTuple (n + 1)} (hP : CrossingGeometry P)
    (v : Visit P) :
    traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) =
      edgePoint P v.2.val (edgeParameter P v.2.val (visitTwin v).2.val) := by
  rw [geoMarkPosition_evaluation_visit, (crossingParameter_spec v.1 v.2.val v.2.property).2.2]
  congr 1
  exact visitParameter_eq_of_support_pair_of_geometry hP v _ (visit_crossing_val_eq_pair v)

omit [NeZero n] in
theorem markPointOn_zero (a : Mark g.center) :
    markPointOn g g.zeroParameter a =
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) := by
  cases a with
  | inl i => rw [geoMarkPosition_evaluation_vertex]; rfl
  | inr v => rw [visit_point_eq_edgePoint (flatCentreCG hn g j hz hb hc) v]; rfl

omit [NeZero n] in
theorem markPointOn_side (b : Bool) (t : g.SideParameter) (hs : CommonSupports g t)
    (a : Mark g.center) :
    markPointOn g (g.sideTime b t) a =
      traversalEvaluation (g.sideTuple b t).val
        (geoMarkPosition (flatSideCG hn g b t) (markTransport (hs b) a)) := by
  cases a with
  | inl i =>
    show g.curve (g.sideTime b t) i =
      traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) (Sum.inl i))
    rw [geoMarkPosition_evaluation_vertex]
    rfl
  | inr v =>
    have h := visitParameter_eq_of_support_pair_of_geometry (flatSideCG hn g b t)
      (visitTransport (hs b) v) (visitTwin v).2.val (visit_crossing_val_eq_pair v)
    show edgePoint (g.curve (g.sideTime b t)) v.2.val
        (edgeParameter (g.curve (g.sideTime b t)) v.2.val (visitTwin v).2.val) =
      traversalEvaluation (g.sideTuple b t).val
        (geoMarkPosition (flatSideCG hn g b t) (Sum.inr (visitTransport (hs b) v)))
    rw [geoMarkPosition_evaluation_visit,
      (crossingParameter_spec _ _ (visitTransport (hs b) v).2.property).2.2]
    exact congrArg (edgePoint (g.sideTuple b t).val v.2.val) h.symm

omit [NeZero n] in
/-- Continuity of the mark points at the centre: vertices by `g.continuous_curve`, crossing points
by Cramer's rule (`continuousAt_edgeParameter_of_geometry`, the centre's crossing determinants being
nonzero on the geometric record domain). -/
theorem continuousAt_markPointOn (hC : CrossingGeometry g.center) (a : Mark g.center) :
    ContinuousAt (fun s => markPointOn g s a) g.zeroParameter := by
  cases a with
  | inl i => exact ((continuous_apply i).comp g.continuous_curve).continuousAt
  | inr v =>
    have hcross : IsCrossing g.center {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    have hF : ContinuousAt (fun Q : LabelledTuple (n + 1) =>
        edgePoint Q v.2.val (edgeParameter Q v.2.val (visitTwin v).2.val))
        (g.curve g.zeroParameter) :=
      (continuous_vertex v.2.val).continuousAt.add
        ((continuousAt_edgeParameter_of_geometry hC hcross).smul
          (continuous_edge v.2.val).continuousAt)
    exact ContinuousAt.comp (f := g.curve) (x := g.zeroParameter) hF
      g.continuous_curve.continuousAt

/-- The corner polygon of a centre carrier read on `g.curve s`: the family of the printed limit
argument, stated on the centre's own index type (plan risk 3). -/
def cornerFamily (S : Finset (Crossing g.center))
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (s : g.Parameter) :
    LabelledTuple (geoCornerCount (flatCentreCG hn g j hz hb hc) S q) :=
  fun k => markPointOn g s (geoCornerMark (flatCentreCG hn g j hz hb hc) S q k)

omit [NeZero n] in
theorem cornerFamily_zero (S : Finset (Crossing g.center))
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    cornerFamily hn g j hz hb hc S q g.zeroParameter =
      geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q :=
  funext fun k => markPointOn_zero hn g j hz hb hc (geoCornerMark _ S q k)

omit [NeZero n] in
theorem cornerFamily_eq_markPolygon (S : Finset (Crossing g.center))
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (s : g.Parameter) :
    cornerFamily hn g j hz hb hc S q s =
      markPolygon (markPointOn g s) (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S q) :=
  rfl

omit [NeZero n] in
theorem continuousAt_cornerFamily (S : Finset (Crossing g.center))
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    ContinuousAt (cornerFamily hn g j hz hb hc S q) g.zeroParameter :=
  continuousAt_pi.mpr fun _ => continuousAt_markPointOn g (flatCentreCG hn g j hz hb hc) _

omit [NeZero n] in
/-- At a side parameter the family is the corner polygon of the side copy (re-indexed): input the
corner-list identification of U2.2 at `t`. -/
theorem rotationNumber_cornerFamily_side (S : Finset (Crossing g.center)) (b : Bool)
    (t : g.SideParameter) (hs : CommonSupports g t) (a : Mark g.center)
    (hcorr : (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a)).map (markTransport (hs b)) =
      geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) :
    rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) =
      rotationNumber (cornerFamily hn g j hz hb hc S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a) (g.sideTime b t)) := by
  have : NeZero ((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (geoOwner (flatCentreCG hn g j hz hb hc) S a)).map (markTransport (hs b))).length :=
    ⟨by rw [List.length_map]; exact NeZero.ne _⟩
  have h1 := reindexed_markPolygon_of_rotate
    (fun m => traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) m))
    (r := 0) ((List.rotate_zero _).trans hcorr)
  have h2 := reindexed_markPolygon_map
    (fun m => traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) m))
    (markTransport (hs b))
    (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (geoOwner (flatCentreCG hn g j hz hb hc) S a))
  have h3 := markPolygon_congr
    (f := (fun m => traversalEvaluation (g.sideTuple b t).val
      (geoMarkPosition (flatSideCG hn g b t) m)) ∘ markTransport (hs b))
    (f' := markPointOn g (g.sideTime b t))
    (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (geoOwner (flatCentreCG hn g j hz hb hc) S a))
    (fun m _ => (markPointOn_side hn g b t hs m).symm)
  exact (rotationNumber_of_reindexed h1).trans
    ((rotationNumber_of_reindexed h2).trans (congrArg rotationNumber h3))

omit [NeZero n] in
/-- Local constancy along the family for one support: `rotationNumber_locally_constant` at the
regular centre polygon, pulled back through the continuous family. -/
theorem eventually_rotationNumber_cornerFamily (S : Finset (Crossing g.center))
    (hreg : ∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      Regular (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q)) :
    ∀ᶠ s in 𝓝 g.zeroParameter, ∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      rotationNumber (cornerFamily hn g j hz hb hc S q s) =
        rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  rw [Filter.eventually_all]
  intro q
  have hF := continuousAt_cornerFamily hn g j hz hb hc S q
  rw [ContinuousAt, cornerFamily_zero] at hF
  exact hF.eventually (rotationNumber_locally_constant (hreg q))

omit [NeZero n] in
/-- The common radius `δ_rot` (printed: "there are finitely many supports and carriers, so a common
sufficiently small interval works for all of them"): below it, on both sides, the family's rotation
number is the centre's, for every independent support and every carrier. Input: the centre corner
polygons are regular (U3: nonzero edges, no antiparallel corner). -/
theorem exists_rotation_radius
    (hne : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      ∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
        edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k ≠ 0)
    (hna : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      ∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
        ¬ ∃ r : ℝ, r < 0 ∧
          edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k =
            r • edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) (k - 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      ∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (b : Bool),
        rotationNumber (cornerFamily hn g j hz hb hc S q (g.sideTime b t)) =
          rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  have hev : ∀ᶠ s in 𝓝 g.zeroParameter, ∀ S : Finset (Crossing g.center),
      GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      ∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
        rotationNumber (cornerFamily hn g j hz hb hc S q s) =
          rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
    rw [Filter.eventually_all]
    intro S
    by_cases hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S
    · have hreg : ∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
          Regular (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) :=
        fun q => (regular_iff_edges _).mpr fun k => ⟨hne S hS q k, hna S hS q k⟩
      exact (eventually_rotationNumber_cornerFamily hn g j hz hb hc S hreg).mono
        fun s h _ => h
    · exact Filter.Eventually.of_forall fun s h => absurd h hS
  obtain ⟨δ, hδ, hδr, hall⟩ := (g.eventually_center_iff_radius _).mp hev
  refine ⟨δ, hδ, hδr, fun t ht S hS q b => hall _ ?_ S hS q⟩
  have habs : |(g.sideTime b t).val| = t.val := by
    cases b
    · simp only [WallGerm.sideTime, Bool.false_eq_true, ↓reduceIte, abs_neg]
      exact abs_of_pos t.property.1
    · simp only [WallGerm.sideTime, ↓reduceIte]
      exact abs_of_pos t.property.1
  rw [habs]
  exact ht

end Sides

/-! ## F. `same_rotation` -/

section Assembly

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)

/-- The deletion half of `same_rotation` for one support: through `μ_j` by
`rotationNumber_deletionCopyThroughJ`, elsewhere by `rotationNumber_others_unchanged`. Inputs (U2):
the owner-iff through `fusionMark` (`correspond_deletion.2`), `ρ_S^C μ_j ≠ μ_j`
(`central_vs_deletion_through_mu_j.1`), the two corner-cycle identities
(`central_vs_deletion_through_mu_j.3`, `others_unchanged.2`); (U3): the regularity facts. -/
theorem same_rotation_deletion (S : Finset (Crossing g.center))
    (hown : ∀ b b' : Mark (deleteVertex g.center j),
      geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b' ↔
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b'))
    (hsucc : geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j)
    (hcycJ : ((((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))))
    (hcycO : ∀ b : Mark (deleteVertex g.center j),
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
        centralCarrierThroughJ hn g j hz hb hc S →
      (((geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
            (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
        (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
            Cycle (Mark g.center)))
    (hneC : ∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k ≠ 0)
    (hnaC : ∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k =
          r • edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) (k - 1))
    (hturnC : ∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      turn (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k = 0 ↔
        geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j)
    (hneD : ∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k
        ≠ 0)
    (hnaD : ∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k =
          r • edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
            (deletionSupport hn g j hz hb hc S) q) (k - 1)) :
    ∀ b : Mark (deleteVertex g.center j),
      rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))) ∧
      |rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))| =
      |rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)))| := by
  intro b
  suffices h : rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))) from
    ⟨h, congrArg abs h⟩
  by_cases hJ : geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
      centralCarrierThroughJ hn g j hz hb hc S
  · -- the carrier through `μ_j`: its deletion copy is `deletionCopyThroughJ`
    have hD : geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        deletionCopyThroughJ hn g j hz hb hc S := by
      apply (hown b _).mpr
      rw [fusionMark_delMark hn g j hz hb hc _ hsucc, geoOwner_successor]
      exact hJ
    rw [hD, hJ]
    exact rotationNumber_deletionCopyThroughJ hn g j hz hb hc S hcycJ (hneC _) (hnaC _) (hturnC _)
      (hneD _) (hnaD _)
  · exact rotationNumber_others_unchanged hn g j hz hb hc S b (hcycO b hJ)

/-- cor:flat-carriers (ii), field `same_rotation` of `FlatCarriersData`, with its radius `δ_rot`:
"They have the same signed rotation and hence the same absolute rotation" — each side copy and the
deletion copy of every centre carrier have the centre copy's rotation number. Up-front inputs (U3,
for every independent support): the centre corner polygons have nonzero edges and no antiparallel
corner. Per-`t`, per-`S` inputs: the side corner-list identification (U2.2), the deletion interface
(U2: `correspond_deletion.2`, `central_vs_deletion_through_mu_j.1,.3`, `others_unchanged.2`), the
centre turn clause (`turns_nonzero.1`) and the deletion regularity (U3). -/
theorem same_rotation
    (hneC : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      ∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
        edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k ≠ 0)
    (hnaC : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      ∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
        ¬ ∃ r : ℝ, r < 0 ∧
          edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k =
            r • edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) (k - 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ hs : CommonSupports g t,
      ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      (∀ (b : Bool) (a : Mark g.center),
        (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S a)).map (markTransport (hs b)) =
        geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) →
      (∀ b b' : Mark (deleteVertex g.center j),
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
          geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b' ↔
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
          geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) →
      geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j →
      (((((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
            (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
              Cycle (Mark (deleteVertex g.center j))) =
        (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j)))) →
      (∀ b : Mark (deleteVertex g.center j),
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
          centralCarrierThroughJ hn g j hz hb hc S →
        (((geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
            (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
              (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
          (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
            (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
              Cycle (Mark g.center))) →
      (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
        turn (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k = 0 ↔
          geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j) →
      (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
        (k : ZMod (geoCornerCount _ _ q)),
        edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k
          ≠ 0) →
      (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
        (k : ZMod (geoCornerCount _ _ q)),
        ¬ ∃ r : ℝ, r < 0 ∧
          edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k =
            r • edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
              (deletionSupport hn g j hz hb hc S) q) (k - 1)) →
      -- the field `same_rotation` of `FlatCarriersData hn g j hz hb hc t hs S`, verbatim
      ((∀ (b : Bool) (a : Mark g.center),
        rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) =
        rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S a)) ∧
        |rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a)))| =
        |rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S a))|) ∧
      (∀ b : Mark (deleteVertex g.center j),
        rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) =
        rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))) ∧
        |rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))| =
        |rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)))|)) := by
  obtain ⟨δ, hδ, hδr, hrad⟩ := exists_rotation_radius hn g j hz hb hc hneC hnaC
  refine ⟨δ, hδ, hδr, fun t ht hs S hS hcorr hown hsucc hcycJ hcycO hturnC hneD hnaD => ⟨?_, ?_⟩⟩
  · intro b a
    have h : rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) =
        rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S a)) := by
      rw [rotationNumber_cornerFamily_side hn g j hz hb hc S b t hs a (hcorr b a)]
      exact hrad t ht S hS _ b
    exact ⟨h, congrArg abs h⟩
  · exact same_rotation_deletion hn g j hz hb hc S hown hsucc hcycJ hcycO (hneC S hS) (hnaC S hS)
      hturnC hneD hnaD

end Assembly

end
end SM
