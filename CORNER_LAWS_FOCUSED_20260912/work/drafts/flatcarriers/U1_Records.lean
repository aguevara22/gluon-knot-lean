import SM.FlatCarriersDefs

/-! # U1 — Records, mark identifications, generic configurations, assembly

Prover unit U1 of work/drafts/flatcarriers/PLAN_FINAL.md §5 for def:flat-carriers /
cor:flat-carriers (reference/SM/sm-3-statesum.tex:788-835), on the FIXED statement design of
`SM.FlatCarriersDefs` (work/lean/SM/FlatCarriersDefs.lean). Written 2026-09-13 by a Claude Code
prover subagent; checked with `cd work/lean && lake env lean ../drafts/flatcarriers/U1_Records.lean`
(no admitted goals; standard axioms only).

Contents (plan §5 "### U1", items 1–7):
1. `flat_common_supports`, `flat_side_records` — the common supports and the per-`t` side records
   read off `FlatSidesData` (lem:flat-sides).
2. `visitTransport_visitTwin`, `fusionVisitEquiv_visitTwin` (pairing commutes),
   `common_gauss_word_of`, `common_interlacement_of`, `geoIndependent_map_iff`,
   `geoIndependent_iff_isDecomposition`, `independent_supports_of`.
3. `geoMarkKey_lt_transport`, `geoMarkList_transport_perm`, **`geoMarkList_map_transport`**
   (the marked circle is carried mark by mark by `markTransport`), hence `identify_sides_marks_of`.
4. `fusionKey_of_le`, `geoMarkList_erase_mem_iff`, **`geoMarkList_deleteVertex_rotation`**
   (the deletion's marked circle is the centre's with `μ_j` erased, as cycles), hence
   `identify_deletion_marks_of`.
5. `geoMarkSuccessor_no_mark_between` (`successor_gap` on ANY `CrossingGeometry`, the port of
   `nextMark_no_mark_between`), `GeoCarrierSpec.of_core` (every field of `GeoCarrierSpec` except
   `traced_successor` / `inherited_pieces`, on any `CrossingGeometry`), `geoCarrierSpec_of_generic`
   (the full spec on a generic polygon at a decomposition); so `deletion_carriers`, `side_carriers`.
6. `geoCarriers_are_cycles`, `sides_are_smoothing_carriers_of`, `centre_deletion_same_words_of`,
   `named_sides_of_turn_product`, `same_signs_of`, `cornerSelector_spec` (cor (iii) `selector_def`,
   taken over from U5).
7. Assembly: `flat_carriers_definition_data` / `flat_carriers_data` at one `t`, and the row theorems
   `flat_carriers_definition_of` / `flat_carriers_of`, whose remaining inputs are the interfaces of
   U2–U5 (`U2Interface`, `U3Interface`, `U4Interface`, `U5Interface`, fields named as in the plan),
   each supplied "on a small radius" (`OnSmallRadius`). -/

namespace SM

open Carrier GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-! ## 1. Reading lem:flat-sides at one side parameter -/

omit [NeZero n] in
/-- `|±t| = t` for a side parameter. -/
theorem WallGerm.sideTime_val_abs (g : WallGerm n) (b : Bool) (t : g.SideParameter) :
    |(g.sideTime b t).val| = t.val := by
  cases b
  · simp only [WallGerm.sideTime, Bool.false_eq_true, ↓reduceIte, abs_neg]
    exact abs_of_pos t.property.1
  · simp only [WallGerm.sideTime, ↓reduceIte]
    exact abs_of_pos t.property.1

/-- The side records of lem:flat-sides (ii) at one side parameter `t`, for both sides: the
same-edge crossing-parameter order agrees with the centre's, and the geometric records agree
(`GeometricRecordsAgree`: Gauss list and word, interlacement, signs, through some common supports). -/
def SideRecordData (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) : Prop :=
  ∀ b : Bool,
    CrossingParameterOrderAgrees g.center (g.sideTuple b t).val ∧
    GeometricRecordsAgree (flatCentreCG hn g j hz hb hc) (flatSideCG hn g b t)

/-- `FlatSidesData` gives, on its radius, the turn-sign change at `j` and the side records at
every side parameter. -/
theorem flat_side_records (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (hF : FlatSidesData hn g j hz hb hc) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      (turn (g.sideTuple true t).val j : ℝ) * (turn (g.sideTuple false t).val j : ℝ) < 0 ∧
      SideRecordData hn g j hz hb hc t := by
  obtain ⟨δ, hδ, hδr, hturn, hloc⟩ := hF.2.2.2.2.2.2
  refine ⟨δ, hδ, hδr, fun t ht => ⟨hturn t ht, fun b => ?_⟩⟩
  have h := hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

omit [NeZero n] in
/-- Plan U1.1: the common crossing supports of the centre and both sides (the `hs` of
`GeometricRecordsAgree`, both sides at once). -/
theorem flat_common_supports (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t) :
    CommonSupports g t :=
  fun b s => (hsd b).2.choose s

/-! ## 2. Pairing, Gauss words, interlacement, independent supports -/

/-- The canonical visit identification commutes with the pairing of the two visits of a
crossing. -/
theorem visitTransport_visitTwin {m : ℕ} {P Q : LabelledTuple m}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (v : Visit P) :
    visitTransport hs (visitTwin v) = visitTwin (visitTransport hs v) :=
  visitTwin_unique _ _ rfl (fun h => visitTwin_ne v ((visitTransport hs).injective h))

/-- The fused-edge visit identification commutes with the pairing. -/
theorem fusionVisitEquiv_visitTwin (hn : 3 ≤ n) {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (v : Visit P) :
    fusionVisitEquiv hn hz hb hc (visitTwin v) = visitTwin (fusionVisitEquiv hn hz hb hc v) :=
  visitTwin_unique _ _ rfl
    (fun h => visitTwin_ne v ((fusionVisitEquiv hn hz hb hc).injective h))

/-- `markTransport` fixes the vertices and acts by `visitTransport` on the visits. -/
@[simp]
theorem markTransport_inl {m : ℕ} {P Q : LabelledTuple m}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (i : ZMod m) :
    markTransport hs (Sum.inl i) = Sum.inl i := rfl

@[simp]
theorem markTransport_inr {m : ℕ} {P Q : LabelledTuple m}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (v : Visit P) :
    markTransport hs (Sum.inr v) = Sum.inr (visitTransport hs v) := rfl

/-- Independence transports along a crossing bijection that carries the interlacement
relation. -/
theorem geoIndependent_map_iff {m m' : ℕ} [NeZero m] [NeZero m'] {P : LabelledTuple m}
    {Q : LabelledTuple m'}
    (hP : CrossingGeometry P) (hQ : CrossingGeometry Q) (e : Crossing P ≃ Crossing Q)
    (he : ∀ x y, GeometricInterlaces hP x y ↔ GeometricInterlaces hQ (e x) (e y))
    (S : Finset (Crossing P)) :
    GeoIndependent hP S ↔ GeoIndependent hQ (S.map e.toEmbedding) := by
  constructor
  · intro h x hx y hy hxy hI
    rw [Finset.mem_map_equiv] at hx hy
    refine h _ hx _ hy (fun h' => hxy ?_) ?_
    · rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, h']
    · rw [he]
      simpa only [Equiv.apply_symm_apply] using hI
  · intro h x hx y hy hxy hI
    exact h (e x) (Finset.mem_map_of_mem _ hx) (e y) (Finset.mem_map_of_mem _ hy)
      (fun h' => hxy (e.injective h')) ((he x y).mp hI)

/-- On a generic polygon, geometric independence is def:decomposition. -/
theorem geoIndependent_iff_isDecomposition {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    {P : LabelledTuple m} (hP : Generic P) (S : Finset (Crossing P)) :
    GeoIndependent (generic_crossingGeometry hm hP) S ↔ IsDecomposition hm hP S := by
  unfold IsDecomposition
  rw [mem_independentSupports_iff]
  exact Iff.rfl


/-! ## 3. The marked circle under the canonical side identification (plan U1.3) -/

/-- The traversal keys of two marks compare the same way at the centre and on a side (vertices by
index, vertex/visit by the strict interiority of visit parameters, visits by
`geometric_visitKey_lt_transport`). -/
theorem geoMarkKey_lt_transport {m : ℕ} [NeZero m] {P Q : LabelledTuple m}
    (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q)
    (a b : Mark P) :
    geoMarkKey hP a < geoMarkKey hP b ↔
      geoMarkKey hQ (markTransport hs a) < geoMarkKey hQ (markTransport hs b) := by
  cases a with
  | inl i =>
    cases b with
    | inl k => exact Iff.rfl
    | inr v =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hQ (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (i.val < v.2.val.val ∨ i = v.2.val ∧ (0 : ℝ) < visitParameter v) ↔
        (i.val < v.2.val.val ∨ i = v.2.val ∧ (0 : ℝ) < visitParameter (visitTransport hs v))
      exact or_congr Iff.rfl (and_congr Iff.rfl ⟨fun _ => h2, fun _ => h1⟩)
  | inr v =>
    cases b with
    | inl i =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hQ (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter v < (0 : ℝ)) ↔
        (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter (visitTransport hs v) < (0 : ℝ))
      exact or_congr Iff.rfl (and_congr Iff.rfl
        ⟨fun h => (lt_asymm h1 h).elim, fun h => (lt_asymm h2 h).elim⟩)
    | inr w => exact geometric_visitKey_lt_transport hP hQ hs ho v w

theorem geoMarkKey_le_transport {m : ℕ} [NeZero m] {P Q : LabelledTuple m}
    (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q)
    (a b : Mark P) :
    geoMarkKey hP a ≤ geoMarkKey hP b ↔
      geoMarkKey hQ (markTransport hs a) ≤ geoMarkKey hQ (markTransport hs b) := by
  simpa only [not_lt] using not_congr (geoMarkKey_lt_transport hP hQ hs ho b a)

theorem geoMarkList_transport_perm {m : ℕ} [NeZero m] {P Q : LabelledTuple m}
    (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) :
    ((geoMarkList hP).map (markTransport hs)).Perm (geoMarkList hQ) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.map (markTransport hs).injective (geoMarkList_nodup hP))
    (geoMarkList_nodup hQ)).mpr
  intro w
  constructor
  · intro _
    exact mem_geoMarkList hQ w
  · intro _
    obtain ⟨v, rfl⟩ := (markTransport hs).surjective w
    exact List.mem_map.mpr ⟨v, mem_geoMarkList hP v, rfl⟩

/-- **Plan U1.3.** With the same crossing supports and the same same-edge parameter order, the
canonical mark identification carries the sorted marked circle of `P` onto that of `Q`, mark by
mark (the mark-level form of lem:flat-sides (ii)). -/
theorem geoMarkList_map_transport {m : ℕ} [NeZero m] {P Q : LabelledTuple m}
    (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q) :
    (geoMarkList hP).map (markTransport hs) = geoMarkList hQ := by
  apply List.Perm.eq_of_pairwise
    (fun x y _ _ hxy hyx => geoMarkKey_injective hQ (le_antisymm hxy hyx))
    _ (geoMarkList_sorted hQ) (geoMarkList_transport_perm hP hQ hs)
  apply List.pairwise_map.mpr
  apply (geoMarkList_sorted hP).imp
  intro v w h
  exact (geoMarkKey_le_transport hP hQ hs ho v w).mp h

/-! ## 4. The marked circle under deletion (plan U1.4) -/

omit [NeZero n] in
/-- Below the bend the fusion compression is the identity. -/
theorem fusionKey_of_le {c r x : ℝ} (hx : x ≤ c) : fusionKey c r x = x := by
  rcases hx.lt_or_eq with h | h
  · exact fusionKey_low h
  · subst h
    rw [fusionKey_middle le_rfl (by linarith)]
    ring

omit [NeZero n] in
/-- `Sum.instBEq` is lawful when its components are (not provided by the toolchain; needed for
the `List.erase` lemmas on `Mark P = ZMod n ⊕ Visit P`, whose `BEq` instance is `Sum.instBEq`). -/
instance Sum.lawfulBEq {α β : Type*} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  eq_of_beq {a b} h := by
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have h' : (a == b) = true := h
        exact congrArg Sum.inl (eq_of_beq h')
      | inr b =>
        have h' : false = true := h
        exact absurd h' Bool.false_ne_true
    | inr a =>
      cases b with
      | inl b =>
        have h' : false = true := h
        exact absurd h' Bool.false_ne_true
      | inr b =>
        have h' : (a == b) = true := h
        exact congrArg Sum.inr (eq_of_beq h')
  rfl {a} := by
    cases a with
    | inl a => exact (beq_self_eq_true a : (a == a) = true)
    | inr a => exact (beq_self_eq_true a : (a == a) = true)

/-- Membership in the marked circle with one mark erased. -/
theorem geoMarkList_erase_mem_iff {m : ℕ} [NeZero m] {P : LabelledTuple m}
    (hP : CrossingGeometry P) (a x : Mark P) :
    x ∈ (geoMarkList hP).erase a ↔ x ≠ a := by
  rw [(geoMarkList_nodup hP).mem_erase_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_geoMarkList hP x⟩⟩

/-- **Plan U1.4.** The deletion's sorted marked circle is the centre's with the mark `μ_j` erased,
read on the deletion by `delMark`, up to rotation (the deletion list is cut at `μ_{j+1}`); by
`sorted_map_monotone_cut_rotation` with the compression `fusionKey` of the shifted traversal
coordinate (visits: `fusionVisitKey_compression`; vertices: the shifted index is the retained
index, below the bend). -/
theorem geoMarkList_deleteVertex_rotation (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) :
    ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
      (delMark hn g j hz hb hc)) : List (Mark (deleteVertex g.center j))).IsRotated
      (geoMarkList (flatDeletionCG hn g j hz hb hc)) := by
  set C := flatCentreCG hn g j hz hb hc with hC
  set D := flatDeletionCG hn g j hz hb hc with hD
  obtain ⟨r, hr0, hr1, hm⟩ := hb.2
  have hnodup : ((geoMarkList C).erase (Sum.inl j)).Nodup := (geoMarkList_nodup C).erase _
  have hmem := geoMarkList_erase_mem_iff C (Sum.inl j)
  apply sorted_map_monotone_cut_rotation _ _ (delMark hn g j hz hb hc) (geoMarkKey C)
    (geoMarkKey D) ((n : ℝ) + 1) ((j + 1).val) (fusionKey ((n : ℝ) - 1) r)
    (fusionKey_strictMono _ hr0 hr1) (geoMarkKey_injective C) (geoMarkKey_injective D)
    ((geoMarkList_sorted C).sublist List.erase_sublist) (geoMarkList_sorted D)
  · apply (List.perm_ext_iff_of_nodup ?_ (geoMarkList_nodup D)).mpr
    · intro w
      constructor
      · intro _
        exact mem_geoMarkList D w
      · intro _
        exact List.mem_map.mpr ⟨fusionMark hn g j hz hb hc w,
          (hmem _).mpr (fusionMark_ne_deleted hn g j hz hb hc w),
          delMark_fusionMark hn g j hz hb hc w⟩
    · apply List.Nodup.map_on _ hnodup
      intro x hx y hy hxy
      rw [← fusionMark_delMark hn g j hz hb hc x ((hmem x).mp hx), hxy,
        fusionMark_delMark hn g j hz hb hc y ((hmem y).mp hy)]
  · intro x _
    refine ⟨traversalKey_nonneg _, ?_⟩
    have h := traversalKey_lt_size (geoMarkPosition C x)
    unfold geoMarkKey
    exact_mod_cast h
  · intro x hx
    have hx' := (hmem x).mp hx
    have hshift : (if geoMarkKey C x < ((j + 1).val : ℝ)
        then geoMarkKey C x - ((j + 1).val : ℝ) + ((n : ℝ) + 1)
        else geoMarkKey C x - ((j + 1).val : ℝ)) =
        traversalKey (traversalShift (j + 1) (geoMarkPosition C x)) := by
      rw [traversalKey_shift]
      unfold geoMarkKey
      push_cast
      rfl
    rw [hshift]
    cases x with
    | inr v => exact fusionVisitKey_compression hn hz hb hc hm v
    | inl k =>
      have hk : k ≠ j := fun h => hx' (congrArg Sum.inl h)
      change ((fusionIndex j k).val : ℝ) + 0 =
        fusionKey ((n : ℝ) - 1) r (((k - (j + 1)).val : ℝ) + 0)
      rw [retained_shift_index hk, insertIndex_val]
      symm
      apply fusionKey_of_le
      have h1 : (fusionIndex j k).val + 1 ≤ n := (fusionIndex j k).val_lt
      have h2 : ((fusionIndex j k).val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
      linarith

/-! ## 5. The carrier specification on generic configurations (plan U1.5) -/

/-- `successor_gap` on ANY geometric record domain (port of `nextMark_no_mark_between`): no mark
lies strictly in the oriented cyclic gap between a mark and its `ρ`-successor. -/
theorem geoMarkSuccessor_no_mark_between {m : ℕ} [NeZero m] {P : LabelledTuple m}
    (hP : CrossingGeometry P) (a u : Mark P) :
    ¬ traversalBetween (geoMarkPosition hP a) (geoMarkPosition hP u)
      (geoMarkPosition hP (geoMarkSuccessor hP a)) := by
  classical
  let d : DecidableEq (Mark P) := inferInstance
  let _ := geoMarkLinearOrder hP
  have hnext : geoNextMark hP a = geoMarkSuccessor hP a := rfl
  rw [geoNextMark_eq_list_next] at hnext
  have hnext' : @List.next (Mark P) d (Finset.univ : Finset (Mark P)).sort a
      ((Finset.mem_sort _).mpr (Finset.mem_univ a)) = geoMarkSuccessor hP a := hnext
  have hd : d = (fun a b : Mark P => LinearOrder.toDecidableEq a b) :=
    Subsingleton.elim _ _
  rw [hd] at hnext'
  exact sorted_next_no_cyclic_between (Finset.univ : Finset (Mark P))
    (Finset.mem_univ a) (Finset.mem_univ _) hnext' u (Finset.mem_univ u)

omit [NeZero n] in
/-- Transport of the "consecutive entries are successors" statement along an equality of lists. -/
theorem getElem_succ_congr {α : Type*} (ρ : α → α) {L L' : List α} (h : L = L')
    (hL' : ∀ i : Fin L'.length, ρ (L'[i.val]'i.isLt) =
      L'[(i.val + 1) % L'.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))) :
    ∀ i : Fin L.length, ρ (L[i.val]'i.isLt) =
      L[(i.val + 1) % L.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)) := by
  subst h
  exact hL'

/-- Every field of `GeoCarrierSpec` except `traced_successor` and `inherited_pieces` holds on ANY
geometric record domain, by the definitions; the two remaining fields are the inputs. -/
theorem GeoCarrierSpec.of_core {m : ℕ} [NeZero m] {P : LabelledTuple m}
    (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (hts : ∀ (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length),
      geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
        (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)))
    (hip : ∀ (a : Mark P) (u : ℝ), 0 ≤ u → u ≤ 1 →
      geoSmoothingSegment hP S a u ∈ edgeSegment P (geoMarkPosition hP (selectedMarkPerm S a)).1) :
    GeoCarrierSpec hP S where
  mark_vertex i := ⟨geoMarkPosition_evaluation_vertex hP i, rfl, rfl⟩
  mark_visit v := ⟨geoMarkPosition_evaluation_visit hP v, rfl, rfl,
    (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1,
    (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).2⟩
  marks_injective := geoMarkPosition_injective hP
  successor_gap := geoMarkSuccessor_no_mark_between hP
  reconnection _ := rfl
  reconnect_selected v hv := ⟨geoSmoothingSuccessor_visit_of_mem hP S v hv, by
    rw [geoSmoothingSuccessor_visit_of_mem hP S (visitTwin v)
      (by rw [visitTwin_crossing]; exact hv), visitTwin_involutive]⟩
  keep_unselected := geoSmoothingSuccessor_visit_of_not_mem hP S
  keep_vertex _ := rfl
  carriers := geoOwner_eq_iff hP S
  traced_curve _ := rfl
  traced_marks q := ⟨geoComponentMarkList_nodup hP S q, geoComponentMarkList_length_pos hP S q,
    mem_geoComponentMarkList hP S q⟩
  traced_successor := hts
  straight_pieces _ _ := rfl
  inherited_pieces := hip
  corners _ := rfl
  corner_vertex := isTrueCorner_vertex S
  corner_visit := isTrueCorner_visit S

/-- On a generic polygon the inherited subsegment is the accepted one. -/
theorem geoSmoothingSegment_eq_generic {m : ℕ} [NeZero m] (hm : 3 ≤ m) {P : LabelledTuple m}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) (u : ℝ) :
    geoSmoothingSegment (generic_crossingGeometry hm hP) S a u = smoothingSegment hm hP S a u := by
  unfold geoSmoothingSegment smoothingSegment
  rw [geoSmoothingSuccessor_eq_generic, geoMarkPosition_eq_generic hm hP,
    geoMarkPosition_eq_generic hm hP]

/-- **Plan U1.5.** The full carrier specification on a generic polygon at a decomposition: the
sentence-2 fields of def:flat-carriers for the deletion and for the two sides (the accepted
`componentMarkList_getElem_successor` and `smoothingSegment_mem_edgeSegment` through the
generic-agreement layer). -/
theorem geoCarrierSpec_of_generic {m : ℕ} [NeZero m] (hm : 3 ≤ m) {P : LabelledTuple m}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hm hP S) :
    GeoCarrierSpec (generic_crossingGeometry hm hP) S := by
  refine GeoCarrierSpec.of_core _ S ?_ ?_
  · intro q
    refine getElem_succ_congr _ (geoComponentMarkList_eq_generic hm hP S q) ?_
    intro i
    rw [geoSmoothingSuccessor_eq_generic]
    exact componentMarkList_getElem_successor hm hP hS _ i
  · intro a u hu0 hu1
    rw [geoSmoothingSegment_eq_generic, geoMarkPosition_eq_generic hm hP]
    exact smoothingSegment_mem_edgeSegment hm hP S a hu0 hu1


/-! ## 6. The record fields of def:flat-carriers / cor:flat-carriers at one side parameter -/

section Records

variable (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- Sentence 1a/1b of def:flat-carriers (field `common_gauss_word`): the Gauss records of the
four configurations correspond under the canonical identifications, which commute with the
pairing. -/
theorem common_gauss_word_of (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hs : CommonSupports g t) :
    (∀ b : Bool, (geometricGaussList (flatCentreCG hn g j hz hb hc)).map (visitTransport (hs b)) =
      geometricGaussList (flatSideCG hn g b t)) ∧
    (∀ b : Bool, (geometricGaussWord (flatCentreCG hn g j hz hb hc)).map (crossingTransport (hs b)) =
      geometricGaussWord (flatSideCG hn g b t)) ∧
    ((geometricGaussWord (flatCentreCG hn g j hz hb hc)).map (fusionCrossingEquiv hn hz hb hc) =
      geometricGaussWord (flatDeletionCG hn g j hz hb hc)) ∧
    (∀ (b : Bool) (v : Visit g.center),
      visitTransport (hs b) (visitTwin v) = visitTwin (visitTransport (hs b) v)) ∧
    (∀ v : Visit g.center,
      fusionVisitEquiv hn hz hb hc (visitTwin v) = visitTwin (fusionVisitEquiv hn hz hb hc v)) :=
  ⟨fun b => geometricGaussList_transport _ _ (hs b) (hsd b).1,
    fun b => geometricGaussWord_transport _ _ (hs b) (hsd b).1,
    geometricGaussWord_fusion hn hz hb hc,
    fun b v => visitTransport_visitTwin (hs b) v,
    fun v => fusionVisitEquiv_visitTwin hn hz hb hc v⟩

omit [NeZero n] in
/-- Field `identify_sides_marks` (plan U1.3). -/
theorem identify_sides_marks_of (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hs : CommonSupports g t) :
    ∀ b : Bool, (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
      geoMarkList (flatSideCG hn g b t) :=
  fun b => geoMarkList_map_transport _ _ (hs b) (hsd b).1

/-- Field `identify_deletion_marks` (plan U1.4). -/
theorem identify_deletion_marks_of :
    ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
      (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
        Cycle (Mark (deleteVertex g.center j))) =
      (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))) :=
  Cycle.coe_eq_coe.mpr (geoMarkList_deleteVertex_rotation hn g j hz hb hc)

/-- Field `common_interlacement`. -/
theorem common_interlacement_of (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hs : CommonSupports g t) :
    (∀ (b : Bool) (x y : Crossing g.center),
      GeometricInterlaces (flatCentreCG hn g j hz hb hc) x y ↔
        GeometricInterlaces (flatSideCG hn g b t)
          (crossingTransport (hs b) x) (crossingTransport (hs b) y)) ∧
    (∀ x y : Crossing g.center,
      GeometricInterlaces (flatCentreCG hn g j hz hb hc) x y ↔
        GeometricInterlaces (flatDeletionCG hn g j hz hb hc)
          (fusionCrossingEquiv hn hz hb hc x) (fusionCrossingEquiv hn hz hb hc y)) :=
  ⟨fun b x y => geometric_interlaces_transport _ _ (hs b) (hsd b).1 x y,
    fun x y => geometric_interlaces_fusion hn hz hb hc x y⟩

/-- Field `independent_supports`: independence at the centre is def:decomposition on each side
and on the deletion. -/
theorem independent_supports_of (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hs : CommonSupports g t) (S : Finset (Crossing g.center)) :
    (∀ b : Bool, GeoIndependent (flatCentreCG hn g j hz hb hc) S ↔
      IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) ∧
    (GeoIndependent (flatCentreCG hn g j hz hb hc) S ↔
      IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) := by
  refine ⟨fun b => ?_, ?_⟩
  · have h1 : GeoIndependent (flatCentreCG hn g j hz hb hc) S ↔
        GeoIndependent (flatSideCG hn g b t) (transportSupport (hs b) S) :=
      geoIndependent_map_iff (flatCentreCG hn g j hz hb hc) (flatSideCG hn g b t)
        (crossingTransport (hs b))
        (fun x y => geometric_interlaces_transport _ _ (hs b) (hsd b).1 x y) S
    have h2 : GeoIndependent (flatSideCG hn g b t) (transportSupport (hs b) S) ↔
        IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) :=
      geoIndependent_iff_isDecomposition (flat_hn1 hn) (g.sideTuple b t).property _
    exact h1.trans h2
  · have h1 : GeoIndependent (flatCentreCG hn g j hz hb hc) S ↔
        GeoIndependent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) :=
      geoIndependent_map_iff (flatCentreCG hn g j hz hb hc) (flatDeletionCG hn g j hz hb hc)
        (fusionCrossingEquiv hn hz hb hc) (geometric_interlaces_fusion hn hz hb hc) S
    have h2 : GeoIndependent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) ↔
        IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) :=
      geoIndependent_iff_isDecomposition hn (generic_deleteVertex hn hz hb hc) _
    exact h1.trans h2

omit hn g j hz hb hc in
/-- Sentence 3 (field `carriers_are_cycles`) on ANY geometric record domain: every carrier is the
cycle of one of its marks, traced by the plane points of its marks. -/
theorem geoCarriers_are_cycles {m : ℕ} [NeZero m] {P : LabelledTuple m} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) :
    ∀ q : GeoComponent hP S, ∃ a : Mark P, geoOwner hP S a = q ∧
      (∀ m, geoOwner hP S m = q ↔ (geoSmoothingSuccessor hP S).SameCycle a m) ∧
      geoComponentPlaneCycle hP S q =
        ((geoComponentMarkList hP S q).map
          (fun m => traversalEvaluation P (geoMarkPosition hP m)) : Cycle Plane) := by
  intro q
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP S q
  exact ⟨a, rfl, fun m => (geoOwner_eq_iff hP S m a).trans ⟨fun h => h.symm, fun h => h.symm⟩,
    rfl⟩

/-- Sentence 4 (field `sides_are_smoothing_carriers`). -/
theorem sides_are_smoothing_carriers_of (t : g.SideParameter)
    (hsd : SideRecordData hn g j hz hb hc t) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) :
    ∀ b : Bool,
    (∀ a : Mark (g.sideTuple b t).val,
      geoMarkPosition (flatSideCG hn g b t) a =
        markPosition (flat_hn1 hn) (g.sideTuple b t).property.1 a) ∧
    geoMarkList (flatSideCG hn g b t) = markList (flat_hn1 hn) (g.sideTuple b t).property ∧
    geoMarkSuccessor (flatSideCG hn g b t) = markSuccessor (flat_hn1 hn) (g.sideTuple b t).property ∧
    geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S) =
      smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) ∧
    (∀ a : Mark (g.sideTuple b t).val,
      geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) a) =
      owner (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) a) ∧
    (∀ q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S),
      geoComponentMarkList (flatSideCG hn g b t) (transportSupport (hs b) S) q =
        componentMarkList (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
          (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property
            (transportSupport (hs b) S) q) ∧
      geoComponentPlaneCycle (flatSideCG hn g b t) (transportSupport (hs b) S) q =
        componentPlaneCycle (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
          (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property
            (transportSupport (hs b) S) q) ∧
      geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S) q =
        ccpCornerList (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
          (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property
            (transportSupport (hs b) S) q)) ∧
    SmoothingData (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) := by
  intro b
  have hT : Generic (g.sideTuple b t).val := (g.sideTuple b t).property
  have hS' : IsDecomposition (flat_hn1 hn) hT (transportSupport (hs b) S) :=
    ((independent_supports_of hn g j hz hb hc t hsd hs S).1 b).mp hS
  exact ⟨fun a => geoMarkPosition_eq_generic (flat_hn1 hn) hT a,
    geoMarkList_eq_generic (flat_hn1 hn) hT,
    geoMarkSuccessor_eq_generic (flat_hn1 hn) hT,
    geoSmoothingSuccessor_eq_generic (flat_hn1 hn) hT _,
    fun a => geoComponentEquivGeneric_owner (flat_hn1 hn) hT _ a,
    fun q => ⟨geoComponentMarkList_eq_generic (flat_hn1 hn) hT _ q,
      geoComponentPlaneCycle_eq_generic (flat_hn1 hn) hT _ q,
      geoComponentCornerList_eq_generic (flat_hn1 hn) hT _ q⟩,
    smoothing_data (flat_hn1 hn) hT hS'⟩

/-- Sentence 5 (field `centre_deletion_same_words`). -/
theorem centre_deletion_same_words_of (S : Finset (Crossing g.center))
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) :
    ¬ Generic g.center ∧
    (∀ a : Mark g.center, geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a =
      geoMarkSuccessor (flatCentreCG hn g j hz hb hc) (selectedMarkPerm S a)) ∧
    (∀ a b : Mark g.center, geoOwner (flatCentreCG hn g j hz hb hc) S a =
      geoOwner (flatCentreCG hn g j hz hb hc) S b ↔
      (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).SameCycle a b) ∧
    geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) =
      smoothingSuccessor hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) ∧
    geoMarkList (flatDeletionCG hn g j hz hb hc) = markList hn (generic_deleteVertex hn hz hb hc) ∧
    (∀ b : Mark (deleteVertex g.center j),
      geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      owner hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) b) ∧
    SmoothingData hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) := by
  have hD : Generic (deleteVertex g.center j) := generic_deleteVertex hn hz hb hc
  have h1 : GeoIndependent (flatCentreCG hn g j hz hb hc) S ↔
      GeoIndependent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) :=
    geoIndependent_map_iff (flatCentreCG hn g j hz hb hc) (flatDeletionCG hn g j hz hb hc)
      (fusionCrossingEquiv hn hz hb hc) (geometric_interlaces_fusion hn hz hb hc) S
  have h2 : GeoIndependent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) ↔
      IsDecomposition hn hD (deletionSupport hn g j hz hb hc S) :=
    geoIndependent_iff_isDecomposition hn hD _
  have hS' : IsDecomposition hn hD (deletionSupport hn g j hz hb hc S) := (h1.trans h2).mp hS
  exact ⟨g.center_not_generic, fun _ => rfl, geoOwner_eq_iff _ S,
    geoSmoothingSuccessor_eq_generic hn hD _, geoMarkList_eq_generic hn hD,
    fun b => geoComponentEquivGeneric_owner hn hD _ b, smoothing_data hn hD hS'⟩

omit [NeZero n] hn hz hb hc in
/-- Field `named_sides`: the turn-sign change at `j` (lem:flat-sides) names a right side
(`τ_j = -1`) and a left side (`τ_j = +1`). -/
theorem named_sides_of_turn_product (t : g.SideParameter)
    (h : (turn (g.sideTuple true t).val j : ℝ) * (turn (g.sideTuple false t).val j : ℝ) < 0) :
    ∃ br : Bool, IsRightSide g j br t ∧ IsLeftSide g j (!br) t := by
  have key : ∀ a b : SignType, ((a : ℝ)) * (b : ℝ) < 0 →
      (a = -1 ∧ b = 1) ∨ (a = 1 ∧ b = -1) := by
    intro a b h
    cases a <;> cases b <;> simp at h ⊢ <;> norm_num at h
  rcases key _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨true, h1, h2⟩
  · exact ⟨false, h2, h1⟩

/-- Field `same_signs`: crossing signs and positive over/under bits agree at every visit, centre
↔ sides (lem:flat-sides (ii) sign clause) and centre ↔ deletion (`crossingSign_fusion`,
`positive_over_fusion`). -/
theorem same_signs_of (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t) :
    (∀ (b : Bool) (v : Visit g.center),
      crossingSign (g.sideTuple b t).val v.2.val (visitTwin v).2.val =
        crossingSign g.center v.2.val (visitTwin v).2.val ∧
      (0 < det (edge g.center v.2.val) (edge g.center (visitTwin v).2.val) ↔
        0 < det (edge (g.sideTuple b t).val v.2.val) (edge (g.sideTuple b t).val (visitTwin v).2.val))) ∧
    (∀ v : Visit g.center,
      crossingSign (deleteVertex g.center j) (fusionVisitEquiv hn hz hb hc v).2.val
          (visitTwin (fusionVisitEquiv hn hz hb hc v)).2.val =
        crossingSign g.center v.2.val (visitTwin v).2.val ∧
      (0 < det (edge g.center v.2.val) (edge g.center (visitTwin v).2.val) ↔
        0 < det (edge (deleteVertex g.center j) (fusionVisitEquiv hn hz hb hc v).2.val)
          (edge (deleteVertex g.center j) (visitTwin (fusionVisitEquiv hn hz hb hc v)).2.val))) := by
  refine ⟨fun b v => ?_, fun v => ?_⟩
  · obtain ⟨_, _, _, _, hsign⟩ := (hsd b).2
    have hcr : IsCrossing g.center {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rwa [visit_crossing_val_eq_pair v] at h
    have h1 := hsign _ _ hcr
    refine ⟨h1, ?_⟩
    rw [← sign_eq_one_iff, ← sign_eq_one_iff]
    change crossingSign g.center _ _ = 1 ↔ crossingSign (g.sideTuple b t).val _ _ = 1
    rw [h1]
  · rw [← fusionVisitEquiv_visitTwin hn hz hb hc v]
    exact ⟨crossingSign_fusion hb v.2.val (visitTwin v).2.val,
      positive_over_fusion hb v.2.val (visitTwin v).2.val⟩

omit [NeZero n] hn g j hz hb hc in
/-- cor (iii) `selector_def`, first half (taken over from U5): the three defining clauses of
`cornerSelector`. -/
theorem cornerSelector_spec {k : ℕ} [NeZero k] (Q : LabelledTuple k) :
    ((∀ i, turn Q i = -1) → cornerSelector Q = 1) ∧
    ((∀ i, turn Q i = 1) → cornerSelector Q = (-1 : ℤ) ^ k) ∧
    (¬ (∀ i, turn Q i = -1) → ¬ (∀ i, turn Q i = 1) → cornerSelector Q = 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · unfold cornerSelector
    rw [ite_eq_left h]
  · unfold cornerSelector
    have h' : ¬ ∀ i, turn Q i = -1 := by
      intro h'
      have := (h' 0).symm.trans (h 0)
      exact absurd this (by decide)
    rw [ite_eq_right h', ite_eq_left h]
  · unfold cornerSelector
    rw [ite_eq_right h1, ite_eq_right h2]

end Records

/-! ## 7. Interfaces of units U2–U5 and the assembly -/

section Assembly

variable (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- A family of statements holding "after shrinking the interval" (the printed "a common
sufficiently small interval works for all of them"): on some positive radius, for every side
parameter below it, every common-supports proof and every independent `S`. Each unit's top
lemma is supplied in this form; the assembly takes the minimum of the radii. -/
def OnSmallRadius
    (Φ : ∀ t : g.SideParameter, CommonSupports g t → Finset (Crossing g.center) → Prop) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → ∀ hs : CommonSupports g t,
    ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S → Φ t hs S

/-- **Interface of U2** (plan §5): the centre spec by transport, the carrier correspondences and
the cycle identities. Fields are copied verbatim from `FlatCarriersDefinitionData` /
`FlatCarriersData`; `central_vs_deletion_marks` is the first three conjuncts of
`central_vs_deletion_through_mu_j`. -/
structure U2Interface (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) : Prop where
  centre_carriers : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S
  correspond_sides : ∀ b : Bool,
    (∀ a : Mark g.center,
      geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
          (markTransport (hs b) a) =
        markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
    (∀ a a' : Mark g.center,
      geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a'))
  correspond_deletion :
    (∀ b : Mark (deleteVertex g.center j),
      geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        delMark hn g j hz hb hc
          (if geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
              Sum.inl j
            then geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
            else geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S
              (fusionMark hn g j hz hb hc b))) ∧
    (∀ b b' : Mark (deleteVertex g.center j),
      geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b' ↔
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) ∧
    (∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      ∃ b : Mark (deleteVertex g.center j),
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) = q)
  unique_through_mu_j :
    (∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      (∃ a : Mark g.center, geoOwner (flatCentreCG hn g j hz hb hc) S a = q ∧
        traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) =
          g.center j) ↔
      q = centralCarrierThroughJ hn g j hz hb hc S) ∧
    (∀ (b : Bool) (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S)),
      (∃ a : Mark (g.sideTuple b t).val,
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) a = q ∧
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) a) =
          (g.sideTuple b t).val j) ↔
      q = geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j))
  central_vs_deletion_marks :
    geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j ∧
    ((((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) ∧
    ((((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j)))
  others_unchanged : ∀ b : Mark (deleteVertex g.center j),
    geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
      centralCarrierThroughJ hn g j hz hb hc S →
    (((geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
          (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
      (geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
          Cycle (Mark g.center)) ∧
    (((geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
          (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
      (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
          Cycle (Mark g.center)) ∧
    geoComponentPlaneCycle (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      geoComponentPlaneCycle (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))
  same_retained_crossings :
    (∀ (b : Bool) (a : Mark g.center) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a) ↔
      crossingTransport (hs b) x ∈ geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) ∧
    (∀ (b : Mark (deleteVertex g.center j)) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) ↔
      fusionCrossingEquiv hn hz hb hc x ∈
        geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))

/-- **Interface of U3** (plan §5): corner geometry at the centre and turns. Fields copied verbatim
from `FlatCarriersData`; `central_vs_deletion_geometry` is the last two conjuncts of
`central_vs_deletion_through_mu_j`. -/
structure U3Interface (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) : Prop where
  nonzero_segments :
    (∀ a : Mark g.center,
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ≠
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a)) ∧
    (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k ≠ 0) ∧
    (∀ b : Mark (deleteVertex g.center j),
      traversalEvaluation (deleteVertex g.center j) (geoMarkPosition (flatDeletionCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) ≠
      traversalEvaluation (deleteVertex g.center j) (geoMarkPosition (flatDeletionCG hn g j hz hb hc) b)) ∧
    (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k
        ≠ 0) ∧
    (∀ b : Bool,
      (∀ a : Mark (g.sideTuple b t).val,
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t)
          (geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S) a)) ≠
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) a)) ∧
      ∀ (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S))
        (k : ZMod (geoCornerCount _ _ q)),
        edge (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S) q) k ≠ 0)
  no_antiparallel :
    (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k =
          r • edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) (k - 1)) ∧
    (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k =
          r • edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
            (deletionSupport hn g j hz hb hc S) q) (k - 1)) ∧
    (∀ (b : Bool) (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S))
      (k : ZMod (geoCornerCount _ _ q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S) q) k =
          r • edge (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S) q) (k - 1))
  turns_nonzero :
    (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      turn (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k = 0 ↔
        geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j) ∧
    (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      turn (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k
        ≠ 0) ∧
    (∀ (b : Bool) (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S))
      (k : ZMod (geoCornerCount _ _ q)),
      turn (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S) q) k ≠ 0)
  same_turn_signs : ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a → ∀ b : Bool,
    geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
      geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delMark hn g j hz hb hc a)
  centre_turn_signs : ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a →
    geoCornerTurn (flatCentreCG hn g j hz hb hc) S a =
      geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delMark hn g j hz hb hc a)
  extra_corner : ∀ b : Bool,
    geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) =
      turn (g.sideTuple b t).val j ∧
    (IsRightSide g j b t →
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = -1) ∧
    (IsLeftSide g j b t →
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = 1)
  central_vs_deletion_geometry :
    StrictBetween
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))))
      (g.center j)
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))) ∧
    (∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      g.center j - traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))) =
        r • edge (deleteVertex g.center j) (-1) ∧
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j))) - g.center j =
        s • edge (deleteVertex g.center j) (-1))

/-- **Interface of U4** (plan §5): rotation. Field copied verbatim from `FlatCarriersData`. -/
structure U4Interface (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) : Prop where
  same_rotation :
    (∀ (b : Bool) (a : Mark g.center),
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
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)))|)

/-- **Interface of U5** (plan §5): the selector identity and the agreement of the other selectors
(`selector_def` is proved here, `cornerSelector_spec`). Fields copied verbatim. -/
structure U5Interface (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) : Prop where
  selector_identity : ∀ bR bL : Bool, IsRightSide g j bR t → IsLeftSide g j bL t →
    geoCarrierSelector (flatSideCG hn g bR t) (transportSupport (hs bR) S)
        (geoOwner (flatSideCG hn g bR t) (transportSupport (hs bR) S) (Sum.inl j)) -
      geoCarrierSelector (flatSideCG hn g bL t) (transportSupport (hs bL) S)
        (geoOwner (flatSideCG hn g bL t) (transportSupport (hs bL) S) (Sum.inl j)) =
    geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (deletionCopyThroughJ hn g j hz hb hc S)
  other_selectors_agree : ∀ (b : Bool) (b' : Mark (deleteVertex g.center j)),
    geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b') ≠
      centralCarrierThroughJ hn g j hz hb hc S →
    geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
      (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S)
        (markTransport (hs b) (fusionMark hn g j hz hb hc b'))) =
    geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b')

/-- **def:flat-carriers at one side parameter.** All fields are U1's except the centre spec
(U2's `centre_carriers`). -/
theorem flat_carriers_definition_data (t : g.SideParameter)
    (hsd : SideRecordData hn g j hz hb hc t) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hcs : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S) :
    FlatCarriersDefinitionData hn g j hz hb hc t hs S where
  common_gauss_word := common_gauss_word_of hn g j hz hb hc t hsd hs
  identify_sides_marks := identify_sides_marks_of hn g j hz hb hc t hsd hs
  identify_deletion := flat_fusion_data hn hz hb hc
  identify_deletion_marks := identify_deletion_marks_of hn g j hz hb hc
  common_interlacement := common_interlacement_of hn g j hz hb hc t hsd hs
  independent_supports := independent_supports_of hn g j hz hb hc t hsd hs S
  centre_carriers := hcs
  deletion_carriers := geoCarrierSpec_of_generic hn (generic_deleteVertex hn hz hb hc)
    ((independent_supports_of hn g j hz hb hc t hsd hs S).2.mp hS)
  side_carriers := fun b => geoCarrierSpec_of_generic (flat_hn1 hn) (g.sideTuple b t).property
    (((independent_supports_of hn g j hz hb hc t hsd hs S).1 b).mp hS)
  carriers_are_cycles := ⟨geoCarriers_are_cycles _ S, geoCarriers_are_cycles _ _⟩
  sides_are_smoothing_carriers := sides_are_smoothing_carriers_of hn g j hz hb hc t hsd hs S hS
  centre_deletion_same_words := centre_deletion_same_words_of hn g j hz hb hc S hS

/-- **cor:flat-carriers at one side parameter.** U1's fields (`named_sides`, `same_pairing`,
`same_signs`, `selector_def`) are proved; the others are read from the unit interfaces. -/
theorem flat_carriers_data (t : g.SideParameter)
    (hsd : SideRecordData hn g j hz hb hc t)
    (hturn : (turn (g.sideTuple true t).val j : ℝ) * (turn (g.sideTuple false t).val j : ℝ) < 0)
    (hs : CommonSupports g t) (S : Finset (Crossing g.center))
    (h2 : U2Interface hn g j hz hb hc t hs S) (h3 : U3Interface hn g j hz hb hc t hs S)
    (h4 : U4Interface hn g j hz hb hc t hs S) (h5 : U5Interface hn g j hz hb hc t hs S) :
    FlatCarriersData hn g j hz hb hc t hs S where
  named_sides := named_sides_of_turn_product g j t hturn
  correspond_sides := h2.correspond_sides
  correspond_deletion := h2.correspond_deletion
  unique_through_mu_j := h2.unique_through_mu_j
  central_vs_deletion_through_mu_j := ⟨h2.central_vs_deletion_marks.1,
    h2.central_vs_deletion_marks.2.1, h2.central_vs_deletion_marks.2.2,
    h3.central_vs_deletion_geometry.1, h3.central_vs_deletion_geometry.2⟩
  others_unchanged := h2.others_unchanged
  nonzero_segments := h3.nonzero_segments
  no_antiparallel := h3.no_antiparallel
  turns_nonzero := h3.turns_nonzero
  same_retained_crossings := h2.same_retained_crossings
  same_pairing := ⟨(common_gauss_word_of hn g j hz hb hc t hsd hs).2.2.2.1,
    (common_gauss_word_of hn g j hz hb hc t hsd hs).2.2.2.2⟩
  same_signs := same_signs_of hn g j hz hb hc t hsd
  same_rotation := h4.same_rotation
  same_turn_signs := h3.same_turn_signs
  centre_turn_signs := h3.centre_turn_signs
  extra_corner := h3.extra_corner
  selector_def := ⟨by intro m _ Q; exact cornerSelector_spec Q, fun _ _ _ => rfl⟩
  selector_identity := h5.selector_identity
  other_selectors_agree := h5.other_selectors_agree

/-- **def:flat-carriers** (row `flat_carriers_definition`), assembled: under exactly the
hypotheses of lem:flat-sides, given U2's centre spec on a small radius. -/
theorem flat_carriers_definition_of
    (hsc : g.SignChanges (fun P => (turn P j : ℝ)))
    (hU2 : OnSmallRadius hn g j hz hb hc
      (fun _ _ S => GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ hs : CommonSupports g t, ∀ S : Finset (Crossing g.center),
        GeoIndependent (flatCentreCG hn g j hz hb hc) S →
        FlatCarriersDefinitionData hn g j hz hb hc t hs S := by
  obtain ⟨δF, hδF, hδFr, hF⟩ :=
    flat_side_records hn g j hz hb hc (flat_sides hn g hz hb hc hsc)
  obtain ⟨δ2, hδ2, h2⟩ := hU2
  refine ⟨min δF δ2, lt_min hδF hδ2, (min_le_left _ _).trans hδFr, fun t ht => ?_⟩
  have hsd := (hF t (lt_of_lt_of_le ht (min_le_left _ _))).2
  have hs := flat_common_supports hn g j hz hb hc t hsd
  exact ⟨hs, fun S hS => flat_carriers_definition_data hn g j hz hb hc t hsd hs S hS
    (h2 t (lt_of_lt_of_le ht (min_le_right _ _)) hs S hS)⟩

/-- **cor:flat-carriers** (row `flat_carriers`), assembled: under exactly the hypotheses of
lem:flat-sides, given the interfaces of U2–U5, each on a small radius. -/
theorem flat_carriers_of
    (hsc : g.SignChanges (fun P => (turn P j : ℝ)))
    (hU2 : OnSmallRadius hn g j hz hb hc (U2Interface hn g j hz hb hc))
    (hU3 : OnSmallRadius hn g j hz hb hc (U3Interface hn g j hz hb hc))
    (hU4 : OnSmallRadius hn g j hz hb hc (U4Interface hn g j hz hb hc))
    (hU5 : OnSmallRadius hn g j hz hb hc (U5Interface hn g j hz hb hc)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ hs : CommonSupports g t, ∀ S : Finset (Crossing g.center),
        GeoIndependent (flatCentreCG hn g j hz hb hc) S →
        FlatCarriersData hn g j hz hb hc t hs S := by
  obtain ⟨δF, hδF, hδFr, hF⟩ :=
    flat_side_records hn g j hz hb hc (flat_sides hn g hz hb hc hsc)
  obtain ⟨δ2, hδ2, h2⟩ := hU2
  obtain ⟨δ3, hδ3, h3⟩ := hU3
  obtain ⟨δ4, hδ4, h4⟩ := hU4
  obtain ⟨δ5, hδ5, h5⟩ := hU5
  refine ⟨min δF (min δ2 (min δ3 (min δ4 δ5))),
    lt_min hδF (lt_min hδ2 (lt_min hδ3 (lt_min hδ4 hδ5))),
    (min_le_left _ _).trans hδFr, fun t ht => ?_⟩
  have htF : t.val < δF := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : t.val < δ2 := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : t.val < δ3 := lt_of_lt_of_le ht
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht4 : t.val < δ4 := lt_of_lt_of_le ht
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have ht5 : t.val < δ5 := lt_of_lt_of_le ht
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨hturn, hsd⟩ := hF t htF
  have hs := flat_common_supports hn g j hz hb hc t hsd
  exact ⟨hs, fun S hS => flat_carriers_data hn g j hz hb hc t hsd hturn hs S
    (h2 t ht2 hs S hS) (h3 t ht3 hs S hS) (h4 t ht4 hs S hS) (h5 t ht5 hs S hS)⟩

end Assembly

end
end SM
