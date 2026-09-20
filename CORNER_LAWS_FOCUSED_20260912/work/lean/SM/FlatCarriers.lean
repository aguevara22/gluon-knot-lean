import SM.FlatCarriersDefs
import SM.AppendRotation
import SM.RegularPerturbation
import SM.GermNeighborhood
import SM.GeometricParameters

/-! Ported verbatim 2026-09-13 from work/drafts/flatcarriers/FlatCarriers_Assembled.lean (assembler subagent of the pod executor merging the five placeholder-free prover units U1_Records, U2_Correspondence, U3_CentreGeometry, U4_Rotation, U5_Selector; de-duplication and wiring recorded in work/drafts/flatcarriers/ASSEMBLY_REPORT.md; checked with `lake env lean`, no placeholder, standard axioms); only this header added and `#print axioms` lines removed. Rows def:flat-carriers → `SM.flat_carriers_definition`, cor:flat-carriers → `SM.flat_carriers` (bundles and definitions in SM/FlatCarriersDefs.lean; statements byte-identical to work/drafts/flatcarriers/Statement_FINAL.lean; design PLAN_FINAL.md). -/


/-! # def:flat-carriers / cor:flat-carriers — ASSEMBLED

Assembly (2026-09-13) of the five placeholder-free prover units of work/drafts/flatcarriers/
(`U1_Records`, `U2_Correspondence`, `U3_CentreGeometry`, `U4_Rotation`, `U5_Selector`; plan
PLAN_FINAL.md §5) into the two row theorems `SM.flat_carriers_definition` and `SM.flat_carriers`,
whose statements are EXACTLY those of `Statement_FINAL.lean` (lines 950 and 1272), on the FIXED
definitions of the built module `SM.FlatCarriersDefs`.

Layout: the five units follow verbatim, in dependency order, each in its own `namespace SM … end SM`
block (so every unit keeps its own sections, `variable`s and `open`s); duplicated helper
declarations were removed or renamed (see ASSEMBLY_REPORT.md); the final block `Assembly` wires the
units' top lemmas together. Checked with `cd work/lean && lake env lean
../drafts/flatcarriers/FlatCarriers_Assembled.lean`; `#print axioms` at the end. -/

/-! ********************************************************************************
    ## UNIT U1_Records
    ******************************************************************************** -/

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

/-! ********************************************************************************
    ## UNIT U2_Correspondence
    ******************************************************************************** -/

/-! U2 — Centre spec by transport, carrier correspondences, cycle identities
(def:flat-carriers / cor:flat-carriers, work/drafts/flatcarriers/PLAN_FINAL.md §5 "### U2").

Written 2026-09-13 by the U2 prover subagent on top of the built module `SM.FlatCarriersDefs`.
Everything here is placeholder-free. The interface lemmas of U1 are taken as explicit hypotheses,
named as in PLAN_FINAL.md:
* `identify_sides_marks` : `(geoMarkList C).map (markTransport (hs b)) = geoMarkList T`;
* `identify_deletion_marks` : `(((geoMarkList C).erase (inl j)).map delMark : Cycle _) = geoMarkList D`;
* `independent_supports` (one side) : `IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property
  (transportSupport (hs b) S)` — only for the centre's `traced_successor`.
Both pairing facts (`visitTransport`/`fusionVisitEquiv` commute with `visitTwin`) are PROVED here.

Contents.
1. List lemmas: `List.next` commutes with an injective map (`list_next_map`), `List.next` on an
   erased list (`list_next_erase`).
2. `SameCycle` under a conjugating equivalence (`sameCycle_of_equiv_conj`).
3. Intrinsic centre lemmas on any `hP : CrossingGeometry P`: `successor_gap`
   (`geoMarkSuccessor_no_mark_between`), the successor lies on the outgoing edge
   (`geoMarkSuccessor_on_edge`), `inherited_pieces` (`geoSmoothingSegment_mem_edgeSegment`),
   `ρ a ≠ a` (`geoMarkSuccessor_ne_self`), and `geoCarrierSpec_of_traced_successor`.
4. Side ↔ centre: `selectedMarkPerm`, `ρ`, `ρ_S` commute with `markTransport`; owner-iff; mark and
   corner lists transport; `traced_successor` transports (`correspond_sides_of_marks`,
   `centre_carriers_of_marks`).
5. Centre ↔ deletion: the skip-`μ_j` permutation `skipJ`; `ρ_S^D b = delMark (skipJ (fusionMark b))`;
   owner-iff; surjectivity; `ρ_S^C (inl j) ≠ inl j` (`correspond_deletion_of_marks`); the mark-,
   corner- and plane-cycle identities (`central_vs_deletion_cycles_of_marks`,
   `others_unchanged_of_marks`); corner counts (`geoCornerCount_deletion_through_mu_j`,
   `geoCornerCount_deletion_other`; side: `geoCornerCount_markTransport`).
6. `unique_through_mu_j_data`, `same_retained_crossings_of_marks`.
7. The U2 bundle `flat_carriers_U2` (all U2 goals in one statement, exact field bodies).
Also: `sumLawfulBEq`, a `LawfulBEq (α ⊕ β)` instance (the marks' `List.erase` elaborates to
`Sum.instBEq`, which core leaves without a `LawfulBEq` instance). -/

namespace SM

open Carrier GeoCarrier

/-! ## 1. List lemmas -/

section ListLemmas


variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `List.next` commutes with a map that is injective on the list. -/
theorem list_next_map (f : α → β) (l : List α) (hl : l.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (x : α) (hx : x ∈ l) (hfx : f x ∈ l.map f) :
    (l.map f).next (f x) hfx = f (l.next x hx) := by
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  have hmap : (l.map f).Nodup := List.Nodup.map_on hf hl
  have hi' : i < (l.map f).length := by simpa using hi
  have hgen : ∀ (y : β) (hy : y ∈ l.map f), y = (l.map f)[i]'hi' →
      (l.map f).next y hy = (l.map f)[(i + 1) % (l.map f).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi')) := by
    intro y hy hyi
    subst hyi
    exact List.next_getElem (l.map f) hmap i hi'
  have hgen' : ∀ (y : α) (hy : y ∈ l), y = l[i]'hi →
      l.next y hy = l[(i + 1) % l.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
    intro y hy hyi
    subst hyi
    exact List.next_getElem l hl i hi
  rw [hgen (f x) hfx (by rw [List.getElem_map, hxi]), hgen' x hx hxi.symm, List.getElem_map]
  simp only [List.length_map]

/-- `List.next` in a list with a fresh head `y`, at an element of the tail: it is the tail's own
successor, except that the tail's last element goes to `y` (whose successor is the tail's head). -/
theorem list_next_cons_of_mem (M : List α) (hM : M.Nodup) (y : α) (hy : y ∉ M)
    (x : α) (hx : x ∈ M) (hx' : x ∈ y :: M) :
    M.next x hx =
      if (y :: M).next x hx' = y then (y :: M).next y List.mem_cons_self
      else (y :: M).next x hx' := by
  have hN : (y :: M).Nodup := List.nodup_cons.mpr ⟨hy, hM⟩
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  have hi1 : i + 1 < (y :: M).length := by simp; omega
  have hgenM : ∀ (z : α) (hz : z ∈ M), z = M[i]'hi →
      M.next z hz = M[(i + 1) % M.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
    intro z hz hzi
    subst hzi
    exact List.next_getElem M hM i hi
  have hgenN : ∀ (z : α) (hz : z ∈ y :: M), z = (y :: M)[i + 1]'hi1 →
      (y :: M).next z hz = (y :: M)[(i + 1 + 1) % (y :: M).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hi1)) := by
    intro z hz hzi
    subst hzi
    exact List.next_getElem (y :: M) hN (i + 1) hi1
  have hxN : x = (y :: M)[i + 1]'hi1 := by rw [List.getElem_cons_succ]; exact hxi.symm
  rw [hgenM x hx hxi.symm, hgenN x hx' hxN]
  have hlen : (y :: M).length = M.length + 1 := rfl
  by_cases hlast : i + 1 < M.length
  · -- not the last element of `M`
    have h1 : (i + 1) % M.length = i + 1 := Nat.mod_eq_of_lt hlast
    have h2 : (i + 1 + 1) % (y :: M).length = i + 1 + 1 := by
      rw [hlen]; exact Nat.mod_eq_of_lt (by omega)
    have hne : (y :: M)[(i + 1 + 1) % (y :: M).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hi1)) ≠ y := by
      intro he
      apply hy
      have hmem : (y :: M)[(i + 1 + 1) % (y :: M).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hi1)) ∈ M := by
        have hidx : (i + 1 + 1) % (y :: M).length = (i + 1) + 1 := h2
        have hgetc : ∀ (k : ℕ) (hk : k < (y :: M).length), k = i + 1 + 1 →
            (y :: M)[k]'hk ∈ M := by
          intro k hk hk'
          subst hk'
          rw [List.getElem_cons_succ]
          exact List.getElem_mem _
        exact hgetc _ _ hidx
      rw [he] at hmem
      exact hmem
    rw [ite_eq_right hne]
    have hgetc : ∀ (k : ℕ) (hk : k < (y :: M).length), k = i + 1 + 1 →
        (y :: M)[k]'hk = M[i + 1]'hlast := by
      intro k hk hk'
      subst hk'
      exact List.getElem_cons_succ ..
    rw [hgetc _ _ h2]
    have hgetM : ∀ (k : ℕ) (hk : k < M.length), k = i + 1 → M[k]'hk = M[i + 1]'hlast := by
      intro k hk hk'
      subst hk'
      rfl
    exact hgetM _ _ h1
  · -- the last element of `M`
    have hil : i + 1 = M.length := by omega
    have hpos : 0 < M.length := by omega
    have h1 : (i + 1) % M.length = 0 := by rw [hil]; exact Nat.mod_self _
    have h2 : (i + 1 + 1) % (y :: M).length = 0 := by rw [hlen, hil]; exact Nat.mod_self _
    have hgety : ∀ (k : ℕ) (hk : k < (y :: M).length), k = 0 → (y :: M)[k]'hk = y := by
      intro k hk hk'
      subst hk'
      rfl
    rw [hgety _ _ h2, ite_eq_left rfl]
    have hgenY : (y :: M).next y List.mem_cons_self =
        (y :: M)[(0 + 1) % (y :: M).length]'(Nat.mod_lt _ (by simp)) :=
      List.next_getElem (y :: M) hN 0 (by simp)
    rw [hgenY]
    have h3 : (0 + 1) % (y :: M).length = 1 := by rw [hlen]; exact Nat.mod_eq_of_lt (by omega)
    have hget1 : ∀ (k : ℕ) (hk : k < (y :: M).length), k = 1 → (y :: M)[k]'hk = M[0]'hpos := by
      intro k hk hk'
      subst hk'
      exact List.getElem_cons_succ ..
    rw [hget1 _ _ h3]
    have hget0 : ∀ (k : ℕ) (hk : k < M.length), k = 0 → M[k]'hk = M[0]'hpos := by
      intro k hk hk'
      subst hk'
      rfl
    exact hget0 _ _ h1

/-- `List.next` on a nodup list with one element `y` erased: the successor of `x ≠ y` is the old
successor, or the old successor of `y` when the old successor of `x` is `y`. -/
theorem list_next_erase [BEq α] [LawfulBEq α] (l : List α) (hl : l.Nodup) (x y : α)
    (hx : x ∈ l) (hy : y ∈ l) (hx' : x ∈ l.erase y) :
    (l.erase y).next x hx' = if l.next x hx = y then l.next y hy else l.next x hx := by
  obtain ⟨B, A, hBA⟩ := List.append_of_mem hy
  have hl' : (B ++ y :: A).Nodup := hBA ▸ hl
  have hyB : y ∉ B := by
    intro hyB
    have := List.nodup_append.mp hl'
    exact this.2.2 y hyB y List.mem_cons_self rfl
  have herase : l.erase y = B ++ A := by
    rw [hBA, List.erase_append_right _ hyB, List.erase_cons_head]
  -- rotate `y` to the head
  have hrot : l ~r y :: (A ++ B) := by
    rw [hBA]
    have : B ++ y :: A = B ++ (y :: A) := rfl
    rw [this]
    have h2 : (y :: A) ++ B = y :: (A ++ B) := rfl
    rw [← h2]
    exact List.isRotated_append
  have hrotE : l.erase y ~r A ++ B := by
    rw [herase]
    exact List.isRotated_append
  have hM : (A ++ B).Nodup := hrotE.nodup_iff.mp (hl.erase y)
  have hyM : y ∉ A ++ B := by
    intro hyM
    have hN : (y :: (A ++ B)).Nodup := hrot.nodup_iff.mp hl
    exact (List.nodup_cons.mp hN).1 hyM
  have hxM : x ∈ A ++ B := hrotE.mem_iff.mp hx'
  have hxN : x ∈ y :: (A ++ B) := hrot.mem_iff.mp hx
  have hyN : y ∈ y :: (A ++ B) := List.mem_cons_self
  rw [List.isRotated_next_eq hrotE (hl.erase y) hx',
    List.isRotated_next_eq hrot hl hx, List.isRotated_next_eq hrot hl hy]
  exact list_next_cons_of_mem (A ++ B) hM y hyM x hxM hxN

end ListLemmas

/-! ## 2. `SameCycle` under a conjugating equivalence -/

section PermLemmas

/-- If `g ∘ e = e ∘ f` for an equivalence `e`, the cycles of `g` are the images of the cycles of
`f`. -/
theorem sameCycle_of_equiv_conj {α β : Type*} (f : Equiv.Perm α) (g : Equiv.Perm β) (e : α ≃ β)
    (h : ∀ a, g (e a) = e (f a)) (a b : α) : g.SameCycle (e a) (e b) ↔ f.SameCycle a b := by
  have hinv : ∀ a, g⁻¹ (e a) = e (f⁻¹ a) := by
    intro a
    rw [Equiv.Perm.inv_def, Equiv.Perm.inv_def, Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]
  have hz : ∀ (k : ℤ) (a : α), (g ^ k) (e a) = e ((f ^ k) a) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro a; simp
    | succ i ih =>
      intro a
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, ih]
    | pred i ih =>
      intro a
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, ih]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hz] at hk
    exact e.injective hk
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hz, hk]⟩

end PermLemmas

/-! ## 3. Intrinsic centre lemmas (any `hP : CrossingGeometry P`) -/

namespace GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}


theorem geoMarkKey_vertex (hP : CrossingGeometry P) (i : ZMod n) :
    geoMarkKey hP (Sum.inl i) = (i.val : ℝ) := by
  simp [geoMarkKey, geoMarkPosition, traversalKey]

/-- A marked circle with at least two vertices has at least two marks. -/
theorem geoMarkList_two_le_length (hn : 2 ≤ n) (hP : CrossingGeometry P) :
    2 ≤ (geoMarkList hP).length := by
  have h01 : (Sum.inl (0 : ZMod n) : Mark P) ≠ Sum.inl 1 := by
    intro h
    have h' : (0 : ZMod n) = 1 := Sum.inl.inj h
    have hv := congrArg ZMod.val h'
    rw [ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    exact zero_ne_one hv
  have h0 := mem_geoMarkList hP (Sum.inl 0)
  have h1 := mem_geoMarkList hP (Sum.inl 1)
  rcases hL : geoMarkList hP with _ | ⟨z, _ | ⟨w, R⟩⟩
  · rw [hL] at h0
    simp at h0
  · rw [hL] at h0 h1
    simp only [List.mem_singleton] at h0 h1
    exact absurd (h0.trans h1.symm) h01
  · simp

/-- On a marked circle with at least two marks, no mark is its own `ρ`-successor. -/
theorem geoMarkSuccessor_ne_self (hn : 2 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    geoMarkSuccessor hP a ≠ a := by
  intro he
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem (mem_geoMarkList hP a)
  have hlen := geoMarkList_two_le_length hn hP
  have hgen : ∀ (y : Mark P), y = (geoMarkList hP)[i]'hi →
      geoMarkSuccessor hP y = (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
    intro y hy
    subst hy
    exact geoMarkSuccessor_getElem hP i hi
  have h2 := hgen a hia.symm
  rw [he] at h2
  rw [← hia] at h2
  have h3 := ((geoMarkList_nodup hP).getElem_inj_iff).mp h2
  by_cases hc : i + 1 < (geoMarkList hP).length
  · rw [Nat.mod_eq_of_lt hc] at h3
    omega
  · have hc' : i + 1 = (geoMarkList hP).length := by omega
    rw [hc', Nat.mod_self] at h3
    omega

theorem geoSmoothingSuccessor_vertex_ne_self (hn : 2 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    geoSmoothingSuccessor hP S (Sum.inl i) ≠ Sum.inl i :=
  geoMarkSuccessor_ne_self hn hP (Sum.inl i)

theorem zmod_val_add_one_of_lt {i : ZMod n} (h : i.val + 1 < n) : (i + 1).val = i.val + 1 := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < n),
    Nat.mod_eq_of_lt h]

theorem zmod_add_one_eq_zero_of_val {i : ZMod n} (h : i.val + 1 = n) : i + 1 = 0 := by
  have hcast : ((i.val + 1 : ℕ) : ZMod n) = 0 := by
    rw [h]
    exact ZMod.natCast_self n
  rw [← hcast]
  push_cast
  rw [ZMod.natCast_zmod_val]

/-- The `ρ`-successor of a mark lies on the closed edge segment of the mark's edge, at a parameter
not smaller than the mark's own (the same edge further on, or the next vertex). Intrinsic
consequence of `successor_gap`: an intermediate vertex would lie strictly between. -/
theorem geoMarkSuccessor_on_edge (hP : CrossingGeometry P) (a : Mark P) :
    ∃ t : ℝ, (geoMarkPosition hP a).2.val ≤ t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP (geoMarkSuccessor hP a)) =
        edgePoint P (geoMarkPosition hP a).1 t := by
  set p := geoMarkPosition hP a with hp
  set q := geoMarkPosition hP (geoMarkSuccessor hP a) with hq
  have hgap : ∀ u : Mark P, ¬ traversalBetween p (geoMarkPosition hP u) q :=
    geoMarkSuccessor_no_mark_between hP a
  have hkp : traversalKey p = (p.1.val : ℝ) + p.2.val := rfl
  have hkq : traversalKey q = (q.1.val : ℝ) + q.2.val := rfl
  have hkv : ∀ i : ZMod n, traversalKey (geoMarkPosition hP (Sum.inl i)) = (i.val : ℝ) := by
    intro i
    simp [geoMarkPosition, traversalKey]
  have hs0 : 0 ≤ p.2.val := p.2.property.1
  have hs1 : p.2.val < 1 := p.2.property.2
  have hu0 : 0 ≤ q.2.val := q.2.property.1
  have hu1 : q.2.val < 1 := q.2.property.2
  have hpn : p.1.val < n := ZMod.val_lt _
  have hqn : q.1.val < n := ZMod.val_lt _
  have hev : traversalEvaluation P q = edgePoint P q.1 q.2.val := rfl
  have hvert : ∀ i : ZMod n, edgePoint P (i + 1) 0 = edgePoint P i 1 := by
    intro i
    simp [edgePoint, edge]
  rcases lt_trichotomy (traversalKey p) (traversalKey q) with hlt | heq | hgt
  · -- `p` before `q`: no vertex strictly between
    have hno : ∀ i : ZMod n, ¬ (traversalKey p < (i.val : ℝ) ∧ (i.val : ℝ) < traversalKey q) := by
      intro i hi
      apply hgap (Sum.inl i)
      unfold traversalBetween
      rw [hkv]
      exact Or.inl hi
    by_cases hcut : p.1.val + 1 < n
    · have hvn : (p.1 + 1).val = p.1.val + 1 := zmod_val_add_one_of_lt hcut
      have h1 := hno (p.1 + 1)
      rw [hvn] at h1
      push_cast at h1
      have hle : traversalKey q ≤ (p.1.val : ℝ) + 1 :=
        le_of_not_gt (fun hcon => h1 ⟨by rw [hkp]; linarith, hcon⟩)
      have hq1 : q.1.val = p.1.val ∨ q.1.val = p.1.val + 1 := by
        rw [hkq] at hle
        rw [hkp, hkq] at hlt
        have h2 : (q.1.val : ℝ) ≤ (p.1.val : ℝ) + 1 := by linarith
        have h3 : (p.1.val : ℝ) < (q.1.val : ℝ) + 1 := by linarith
        have h2' : q.1.val ≤ p.1.val + 1 := by exact_mod_cast h2
        have h3' : p.1.val < q.1.val + 1 := by exact_mod_cast h3
        omega
      rcases hq1 with h | h
      · have hqp : q.1 = p.1 := ZMod.val_injective n h
        refine ⟨q.2.val, ?_, hu1.le, by rw [hev, hqp]⟩
        rw [hkp, hkq, h] at hlt
        linarith
      · have hqp : q.1 = p.1 + 1 := ZMod.val_injective n (h.trans hvn.symm)
        have hq20 : q.2.val = 0 := by
          rw [hkq, h] at hle
          push_cast at hle
          linarith
        refine ⟨1, hs1.le, le_refl 1, ?_⟩
        rw [hev, hqp, hq20, hvert]
    · have hcut' : p.1.val + 1 = n := by omega
      have hqp : q.1 = p.1 := by
        apply ZMod.val_injective n
        rw [hkp, hkq] at hlt
        have h3 : (p.1.val : ℝ) < (q.1.val : ℝ) + 1 := by linarith
        have h3' : p.1.val < q.1.val + 1 := by exact_mod_cast h3
        omega
      refine ⟨q.2.val, ?_, hu1.le, by rw [hev, hqp]⟩
      rw [hkp, hkq, hqp] at hlt
      linarith
  · -- equal keys: `q = p`
    have hpq : p = q := traversalKey_injective heq
    exact ⟨p.2.val, le_refl _, hs1.le, by rw [hev, ← hpq]⟩
  · -- `q` before `p`: every mark lies between `q` and `p`
    have hno : ∀ i : ZMod n,
        ¬ ((i.val : ℝ) < traversalKey q) ∧ ¬ (traversalKey p < (i.val : ℝ)) := by
      intro i
      constructor
      · intro hi
        apply hgap (Sum.inl i)
        unfold traversalBetween
        rw [hkv]
        exact Or.inr (Or.inl ⟨hi, hgt⟩)
      · intro hi
        apply hgap (Sum.inl i)
        unfold traversalBetween
        rw [hkv]
        exact Or.inr (Or.inr ⟨hgt, hi⟩)
    have h0 : traversalKey q ≤ 0 := by
      have h0' := (hno 0).1
      rw [ZMod.val_zero] at h0'
      push_cast at h0'
      exact not_lt.mp h0'
    have hq10 : q.1.val = 0 := by
      rw [hkq] at h0
      have h0' : (q.1.val : ℝ) ≤ 0 := by linarith
      have h0'' : q.1.val ≤ 0 := by exact_mod_cast h0'
      omega
    have hq20 : q.2.val = 0 := by
      rw [hkq, hq10] at h0
      push_cast at h0
      linarith
    have hcut : p.1.val + 1 = n := by
      by_contra hne
      have hcut' : p.1.val + 1 < n := by omega
      have hvn : (p.1 + 1).val = p.1.val + 1 := zmod_val_add_one_of_lt hcut'
      have h1 := not_lt.mp (hno (p.1 + 1)).2
      rw [hvn, hkp] at h1
      push_cast at h1
      linarith
    have hq1 : q.1 = p.1 + 1 := by
      rw [zmod_add_one_eq_zero_of_val hcut]
      exact (ZMod.val_eq_zero q.1).mp hq10
    refine ⟨1, hs1.le, le_refl 1, ?_⟩
    rw [hev, hq1, hq20, hvert]

/-- The two visits of a crossing evaluate to the same plane point, so the outgoing slot of a mark
(the mark itself, or its twin at a selected visit) has the mark's plane point. -/
theorem geoMarkPosition_evaluation_selectedMarkPerm (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP (selectedMarkPerm S a)) =
      traversalEvaluation P (geoMarkPosition hP a) := by
  cases a with
  | inl i => rfl
  | inr v =>
    rw [selectedMarkPerm_visit, geoMarkPosition_evaluation_visit,
      geoMarkPosition_evaluation_visit, selectedVisitTwin_crossing]

/-- `inherited_pieces`: the straight subsegment from a mark to its `ρ_S`-successor lies in the
closed edge segment of the edge of the outgoing slot. -/
theorem geoSmoothingSegment_mem_edgeSegment (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    geoSmoothingSegment hP S a u ∈ edgeSegment P (geoMarkPosition hP (selectedMarkPerm S a)).1 := by
  obtain ⟨t, hst, ht1, hev⟩ := geoMarkSuccessor_on_edge hP (selectedMarkPerm S a)
  have hs0 : 0 ≤ (geoMarkPosition hP (selectedMarkPerm S a)).2.val :=
    (geoMarkPosition hP (selectedMarkPerm S a)).2.property.1
  have hpa : traversalEvaluation P (geoMarkPosition hP a) =
      edgePoint P (geoMarkPosition hP (selectedMarkPerm S a)).1
        (geoMarkPosition hP (selectedMarkPerm S a)).2.val := by
    rw [← geoMarkPosition_evaluation_selectedMarkPerm hP S a]
    rfl
  have hsucc : geoSmoothingSuccessor hP S a = geoMarkSuccessor hP (selectedMarkPerm S a) := rfl
  refine ⟨(geoMarkPosition hP (selectedMarkPerm S a)).2.val +
    u * (t - (geoMarkPosition hP (selectedMarkPerm S a)).2.val), ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [geoSmoothingSegment, hsucc, hev, hpa]
    simp only [edgePoint]
    module

/-- Every field of `GeoCarrierSpec` except `traced_successor` is intrinsic to the geometric record
domain; `traced_successor` is supplied (at the centre: by transport from a side). -/
theorem geoCarrierSpec_of_traced_successor (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (hts : ∀ (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length),
      geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
        (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))) :
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
  keep_unselected v hv := geoSmoothingSuccessor_visit_of_not_mem hP S v hv
  keep_vertex _ := rfl
  carriers := geoOwner_eq_iff hP S
  traced_curve _ := rfl
  traced_marks q := ⟨geoComponentMarkList_nodup hP S q, geoComponentMarkList_length_pos hP S q,
    mem_geoComponentMarkList hP S q⟩
  traced_successor := hts
  straight_pieces _ _ := rfl
  inherited_pieces a u hu0 hu1 := geoSmoothingSegment_mem_edgeSegment hP S a u hu0 hu1
  corners _ := rfl
  corner_vertex i := isTrueCorner_vertex S i
  corner_visit v := isTrueCorner_visit S v

end
end GeoCarrier

/-! ## 4. Side ↔ centre: transport of the reconnection along `markTransport` -/

section SideTransport

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {m : ℕ} [NeZero m] {P Q : LabelledTuple m}


omit [NeZero m] in
theorem mem_transportSupport_iff (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) (x : Crossing P) :
    crossingTransport hs x ∈ transportSupport hs S ↔ x ∈ S := by
  unfold transportSupport
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]

omit [NeZero m] in
theorem markTransport_vertex (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (i : ZMod m) :
    markTransport hs (Sum.inl i) = Sum.inl i := rfl

omit [NeZero m] in
theorem markTransport_visit (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (v : Visit P) :
    markTransport hs (Sum.inr v) = Sum.inr (visitTransport hs v) := rfl

/-- The selected exchange commutes with the identification of marks. -/
theorem selectedMarkPerm_markTransport (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) (a : Mark P) :
    selectedMarkPerm (transportSupport hs S) (markTransport hs a) =
      markTransport hs (selectedMarkPerm S a) := by
  cases a with
  | inl i => rfl
  | inr v =>
    rw [markTransport_visit, selectedMarkPerm_visit, selectedMarkPerm_visit, markTransport_visit]
    congr 1
    by_cases hv : v.1 ∈ S
    · have hv' : (visitTransport hs v).1 ∈ transportSupport hs S := by
        rw [visitTransport_crossing, mem_transportSupport_iff]
        exact hv
      rw [selectedVisitTwin_of_mem _ _ hv', selectedVisitTwin_of_mem _ _ hv,
        visitTransport_visitTwin]
    · have hv' : (visitTransport hs v).1 ∉ transportSupport hs S := by
        rw [visitTransport_crossing, mem_transportSupport_iff]
        exact hv
      rw [selectedVisitTwin_of_not_mem _ _ hv', selectedVisitTwin_of_not_mem _ _ hv]

/-- `ρ` commutes with the identification once the marked circles correspond (U1's
`identify_sides_marks`): `List.next` commutes with an injective map. -/
theorem geoMarkSuccessor_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ) (a : Mark P) :
    geoMarkSuccessor hQ (markTransport hs a) = markTransport hs (geoMarkSuccessor hP a) := by
  rw [geoMarkSuccessor_apply, geoMarkSuccessor_apply, geoNextMark_eq_list_next,
    geoNextMark_eq_list_next]
  have hmem : markTransport hs a ∈ (geoMarkList hP).map (markTransport hs) :=
    List.mem_map_of_mem (mem_geoMarkList hP a)
  rw [list_next_congr hmarks.symm (markTransport hs a) _ hmem]
  exact list_next_map (markTransport hs) (geoMarkList hP) (geoMarkList_nodup hP)
    (fun x _ y _ h => (markTransport hs).injective h) a (mem_geoMarkList hP a) hmem

/-- `ρ_S` commutes with the identification (`correspond_sides.1`). -/
theorem geoSmoothingSuccessor_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoSmoothingSuccessor hQ (transportSupport hs S) (markTransport hs a) =
      markTransport hs (geoSmoothingSuccessor hP S a) := by
  rw [geoSmoothingSuccessor_apply, geoSmoothingSuccessor_apply, selectedMarkPerm_markTransport,
    geoMarkSuccessor_markTransport hP hQ hs hmarks]

/-- Two marks lie on one carrier iff their images do (`correspond_sides.2`). -/
theorem geoOwner_markTransport_iff (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a a' : Mark P) :
    geoOwner hP S a = geoOwner hP S a' ↔
      geoOwner hQ (transportSupport hs S) (markTransport hs a) =
        geoOwner hQ (transportSupport hs S) (markTransport hs a') := by
  rw [geoOwner_eq_iff, geoOwner_eq_iff]
  exact (sameCycle_of_equiv_conj (geoSmoothingSuccessor hP S)
    (geoSmoothingSuccessor hQ (transportSupport hs S)) (markTransport hs)
    (geoSmoothingSuccessor_markTransport hP hQ hs hmarks S) a a').symm

/-- The marks of a carrier transport, in inherited order, to the marks of its copy. -/
theorem geoComponentMarkList_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a : Mark P) :
    (geoComponentMarkList hP S (geoOwner hP S a)).map (markTransport hs) =
      geoComponentMarkList hQ (transportSupport hs S)
        (geoOwner hQ (transportSupport hs S) (markTransport hs a)) := by
  unfold geoComponentMarkList
  rw [← hmarks, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp]
  exact decide_eq_decide.mpr (geoOwner_markTransport_iff hP hQ hs hmarks S x a)

theorem isTrueCorner_markTransport (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) (a : Mark P) :
    IsTrueCorner (transportSupport hs S) (markTransport hs a) ↔ IsTrueCorner S a := by
  cases a with
  | inl i => exact Iff.rfl
  | inr v =>
    rw [markTransport_visit, isTrueCorner_visit, isTrueCorner_visit, visitTransport_crossing,
      mem_transportSupport_iff]

/-- The corners of a carrier transport, in inherited order, to the corners of its copy. -/
theorem geoComponentCornerList_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a : Mark P) :
    (geoComponentCornerList hP S (geoOwner hP S a)).map (markTransport hs) =
      geoComponentCornerList hQ (transportSupport hs S)
        (geoOwner hQ (transportSupport hs S) (markTransport hs a)) := by
  unfold geoComponentCornerList
  rw [← geoComponentMarkList_markTransport hP hQ hs hmarks S a, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp]
  exact decide_eq_decide.mpr (isTrueCorner_markTransport hs S x).symm

theorem geoCornerCount_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoCornerCount hP S (geoOwner hP S a) =
      geoCornerCount hQ (transportSupport hs S)
        (geoOwner hQ (transportSupport hs S) (markTransport hs a)) := by
  unfold geoCornerCount
  rw [← geoComponentCornerList_markTransport hP hQ hs hmarks S a, List.length_map]

/-- `traced_successor` transports back along the identification: if consecutive marks of every
carrier of `Q` are `ρ_S`-successors, so are those of every carrier of `P`. -/
theorem traced_successor_of_transport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P))
    (hQts : ∀ (q : GeoComponent hQ (transportSupport hs S))
      (i : Fin (geoComponentMarkList hQ (transportSupport hs S) q).length),
      geoSmoothingSuccessor hQ (transportSupport hs S)
          ((geoComponentMarkList hQ (transportSupport hs S) q)[i.val]'i.isLt) =
        (geoComponentMarkList hQ (transportSupport hs S) q)[(i.val + 1) %
          (geoComponentMarkList hQ (transportSupport hs S) q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))) :
    ∀ (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length),
      geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
        (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)) := by
  intro q i
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP S q
  have hL := geoComponentMarkList_markTransport hP hQ hs hmarks S a
  have hgen : ∀ (l : List (Mark Q)),
      l = geoComponentMarkList hQ (transportSupport hs S)
        (geoOwner hQ (transportSupport hs S) (markTransport hs a)) →
      ∀ (k : ℕ) (hk : k < l.length),
        geoSmoothingSuccessor hQ (transportSupport hs S) (l[k]'hk) =
          l[(k + 1) % l.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le k) hk)) := by
    intro l hl k hk
    subst hl
    exact hQts _ ⟨k, hk⟩
  have h := hgen _ hL i.val (by rw [List.length_map]; exact i.isLt)
  simp only [List.getElem_map] at h
  rw [geoSmoothingSuccessor_markTransport hP hQ hs hmarks S] at h
  have h' := (markTransport hs).injective h
  simpa only [List.length_map] using h'

end
end SideTransport

/-! ## 4b. The flat instantiation: `correspond_sides`, the centre `GeoCarrierSpec` -/

section FlatSides

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- cor:flat-carriers (i), sides: `correspond_sides`, from U1's `identify_sides_marks`. -/
theorem correspond_sides_of_marks (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center))
    (identify_sides_marks : ∀ b : Bool,
      (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
        geoMarkList (flatSideCG hn g b t)) :
    ∀ b : Bool,
    (∀ a : Mark g.center,
      geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
          (markTransport (hs b) a) =
        markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
    (∀ a a' : Mark g.center,
      geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a')) :=
  fun b =>
    ⟨geoSmoothingSuccessor_markTransport _ _ (hs b) (identify_sides_marks b) S,
     geoOwner_markTransport_iff _ _ (hs b) (identify_sides_marks b) S⟩

/-- On a generic side, consecutive marks of a carrier are `ρ_S`-successors (the accepted
`componentMarkList_getElem_successor`, for a decomposition). -/
theorem side_traced_successor (hn : 3 ≤ n) (g : WallGerm (n + 1)) (b : Bool)
    (t : g.SideParameter) (S_T : Finset (Crossing (g.sideTuple b t).val))
    (hST : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property S_T) :
    ∀ (q : GeoComponent (flatSideCG hn g b t) S_T)
      (i : Fin (geoComponentMarkList (flatSideCG hn g b t) S_T q).length),
      geoSmoothingSuccessor (flatSideCG hn g b t) S_T
          ((geoComponentMarkList (flatSideCG hn g b t) S_T q)[i.val]'i.isLt) =
        (geoComponentMarkList (flatSideCG hn g b t) S_T q)[(i.val + 1) %
          (geoComponentMarkList (flatSideCG hn g b t) S_T q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)) := by
  intro q i
  have hgen : ∀ (l : List (Mark (g.sideTuple b t).val)),
      l = componentMarkList (flat_hn1 hn) (g.sideTuple b t).property S_T
        (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property S_T q) →
      ∀ (k : ℕ) (hk : k < l.length),
        smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property S_T (l[k]'hk) =
          l[(k + 1) % l.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le k) hk)) := by
    intro l hl k hk
    subst hl
    exact componentMarkList_getElem_successor (flat_hn1 hn) (g.sideTuple b t).property hST _
      ⟨k, hk⟩
  have h := hgen _ (geoComponentMarkList_eq_generic (flat_hn1 hn) (g.sideTuple b t).property S_T q)
    i.val i.isLt
  rw [← geoSmoothingSuccessor_eq_generic (flat_hn1 hn) (g.sideTuple b t).property S_T] at h
  exact h

/-- def:flat-carriers sentence 2 at the centre: `centre_carriers : GeoCarrierSpec C S`, from U1's
`identify_sides_marks` (one side) and `independent_supports` (that side's `S_T` is a
decomposition). -/
theorem centre_carriers_of_marks (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) (b : Bool)
    (identify_sides_marks :
      (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
        geoMarkList (flatSideCG hn g b t))
    (independent_supports :
      IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S :=
  geoCarrierSpec_of_traced_successor _ S
    (traced_successor_of_transport _ _ (hs b) identify_sides_marks S
      (side_traced_successor hn g b t _ independent_supports))

end FlatSides

/-! ## 5. Centre ↔ deletion: the skip-`μ_j` conjugation -/

section Deletion

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- `fusionVisit_crossing`, restated with the germ's `hz` so that `rw` matches syntactically. -/
theorem fusionVisitEquiv_fst (v : Visit g.center) :
    (fusionVisitEquiv hn hz hb hc v).1 = fusionCrossingEquiv hn hz hb hc v.1 := rfl

/-- The fused-edge identification commutes with the pairing of the two visits of a crossing
(`common_gauss_word.5`, `same_pairing.2`). -/
theorem fusionVisitEquiv_visitTwin_germ (v : Visit g.center) :
    fusionVisitEquiv hn hz hb hc (visitTwin v) = visitTwin (fusionVisitEquiv hn hz hb hc v) := by
  apply visitTwin_unique
  · rw [fusionVisitEquiv_fst, fusionVisitEquiv_fst, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v ((fusionVisitEquiv hn hz hb hc).injective h)

theorem mem_deletionSupport_iff (S : Finset (Crossing g.center)) (x : Crossing g.center) :
    fusionCrossingEquiv hn hz hb hc x ∈ deletionSupport hn g j hz hb hc S ↔ x ∈ S := by
  unfold deletionSupport
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem delMark_vertex (k : ZMod (n + 1)) :
    delMark hn g j hz hb hc (Sum.inl k) = Sum.inl (fusionIndex j k) := rfl

theorem delMark_visit (v : Visit g.center) :
    delMark hn g j hz hb hc (Sum.inr v) = Sum.inr (fusionVisitEquiv hn hz hb hc v) := rfl

theorem fusionMark_vertex (i : ZMod n) :
    fusionMark hn g j hz hb hc (Sum.inl i) = Sum.inl (deletionIndex j i) := rfl

theorem fusionMark_visit (w : Visit (deleteVertex g.center j)) :
    fusionMark hn g j hz hb hc (Sum.inr w) = Sum.inr ((fusionVisitEquiv hn hz hb hc).symm w) := rfl

/-- The selected exchange commutes with `delMark`. -/
theorem selectedMarkPerm_delMark (S : Finset (Crossing g.center)) (a : Mark g.center) :
    selectedMarkPerm (deletionSupport hn g j hz hb hc S) (delMark hn g j hz hb hc a) =
      delMark hn g j hz hb hc (selectedMarkPerm S a) := by
  cases a with
  | inl k => rfl
  | inr v =>
    rw [delMark_visit, selectedMarkPerm_visit, selectedMarkPerm_visit, delMark_visit]
    congr 1
    by_cases hv : v.1 ∈ S
    · have hv' : (fusionVisitEquiv hn hz hb hc v).1 ∈ deletionSupport hn g j hz hb hc S := by
        rw [fusionVisitEquiv_fst, mem_deletionSupport_iff]
        exact hv
      rw [selectedVisitTwin_of_mem _ _ hv', selectedVisitTwin_of_mem _ _ hv,
        fusionVisitEquiv_visitTwin_germ]
    · have hv' : (fusionVisitEquiv hn hz hb hc v).1 ∉ deletionSupport hn g j hz hb hc S := by
        rw [fusionVisitEquiv_fst, mem_deletionSupport_iff]
        exact hv
      rw [selectedVisitTwin_of_not_mem _ _ hv', selectedVisitTwin_of_not_mem _ _ hv]

omit [NeZero n] hn hz hb hc in
theorem selectedMarkPerm_ne_deleted (S : Finset (Crossing g.center)) (a : Mark g.center)
    (ha : a ≠ Sum.inl j) : selectedMarkPerm S a ≠ Sum.inl j := by
  cases a with
  | inl k => exact ha
  | inr v => exact Sum.inr_ne_inl

/-- `ρ` on the deletion, read at the centre through `delMark`, from U1's `identify_deletion_marks`:
the centre successor, skipping the erased mark `μ_j`. -/
theorem geoMarkSuccessor_delMark
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (a : Mark g.center) (ha : a ≠ Sum.inl j) :
    geoMarkSuccessor (flatDeletionCG hn g j hz hb hc) (delMark hn g j hz hb hc a) =
      delMark hn g j hz hb hc
        (if geoMarkSuccessor (flatCentreCG hn g j hz hb hc) a = Sum.inl j
          then geoMarkSuccessor (flatCentreCG hn g j hz hb hc) (Sum.inl j)
          else geoMarkSuccessor (flatCentreCG hn g j hz hb hc) a) := by
  have hrot : (((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
      (delMark hn g j hz hb hc)) ~r geoMarkList (flatDeletionCG hn g j hz hb hc) :=
    Cycle.coe_eq_coe.mp identify_deletion_marks
  have hnodC := geoMarkList_nodup (flatCentreCG hn g j hz hb hc)
  have haE : a ∈ (geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j) :=
    (List.mem_erase_of_ne ha).mpr (mem_geoMarkList _ a)
  have hmemM : delMark hn g j hz hb hc a ∈
      ((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) :=
    List.mem_map_of_mem haE
  have hinj : ∀ x ∈ (geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j),
      ∀ y ∈ (geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j),
      delMark hn g j hz hb hc x = delMark hn g j hz hb hc y → x = y := by
    intro x hx y hy hxy
    have hx' : x ≠ Sum.inl j := (hnodC.mem_erase_iff.mp hx).1
    have hy' : y ≠ Sum.inl j := (hnodC.mem_erase_iff.mp hy).1
    rw [← fusionMark_delMark hn g j hz hb hc x hx', ← fusionMark_delMark hn g j hz hb hc y hy',
      hxy]
  have hnodM := List.Nodup.map_on hinj (hnodC.erase (Sum.inl j))
  rw [geoMarkSuccessor_apply, geoNextMark_eq_list_next,
    ← List.isRotated_next_eq hrot hnodM hmemM,
    list_next_map _ _ (hnodC.erase (Sum.inl j)) hinj a haE hmemM,
    list_next_erase _ hnodC a (Sum.inl j) (mem_geoMarkList _ a) (mem_geoMarkList _ _) haE]
  rfl

/-- The reconnected centre successor with the mark `μ_j` skipped:
`ρ_S ∘ swap (μ_j, ρ_S⁻¹ μ_j)`. It fixes `μ_j`, and elsewhere follows `ρ_S`, jumping over `μ_j`. -/
def skipJ (S : Finset (Crossing g.center)) : Equiv.Perm (Mark g.center) :=
  (Equiv.swap (Sum.inl j)
    ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))).trans
    (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S)

omit [NeZero n] in
theorem skipJ_apply (S : Finset (Crossing g.center)) (x : Mark g.center) :
    skipJ hn g j hz hb hc S x =
      geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S
        (Equiv.swap (Sum.inl j)
          ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j)) x) := rfl

omit [NeZero n] in
theorem skipJ_deleted (S : Finset (Crossing g.center)) :
    skipJ hn g j hz hb hc S (Sum.inl j) = Sum.inl j := by
  rw [skipJ_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

omit [NeZero n] in
theorem skipJ_apply_of_ne (S : Finset (Crossing g.center)) (x : Mark g.center)
    (hx : x ≠ Sum.inl j) :
    skipJ hn g j hz hb hc S x =
      if geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S x = Sum.inl j
        then geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
        else geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S x := by
  rw [skipJ_apply]
  by_cases h : geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S x = Sum.inl j
  · rw [ite_eq_left h]
    have hx' : x = (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j) := by
      rw [← h, Equiv.symm_apply_apply]
    rw [hx', Equiv.swap_apply_right]
  · rw [ite_eq_right h]
    have hxp : x ≠ (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j) := by
      intro he
      apply h
      rw [he, Equiv.apply_symm_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hx hxp]

omit [NeZero n] in
theorem skipJ_ne_deleted_iff (S : Finset (Crossing g.center)) (x : Mark g.center) :
    skipJ hn g j hz hb hc S x ≠ Sum.inl j ↔ x ≠ Sum.inl j := by
  constructor
  · intro h hx
    apply h
    rw [hx, skipJ_deleted]
  · intro hx h
    exact hx ((skipJ hn g j hz hb hc S).injective (h.trans (skipJ_deleted hn g j hz hb hc S).symm))

/-- `ρ_S` on the deletion is the skip-`μ_j` centre successor read through `fusionMark`/`delMark`. -/
theorem geoSmoothingSuccessor_deletion (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b : Mark (deleteVertex g.center j)) :
    geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
      delMark hn g j hz hb hc (skipJ hn g j hz hb hc S (fusionMark hn g j hz hb hc b)) := by
  have hb' : fusionMark hn g j hz hb hc b ≠ Sum.inl j := fusionMark_ne_deleted hn g j hz hb hc b
  rw [skipJ_apply_of_ne hn g j hz hb hc S _ hb', geoSmoothingSuccessor_apply]
  have h1 : selectedMarkPerm (deletionSupport hn g j hz hb hc S) b =
      delMark hn g j hz hb hc (selectedMarkPerm S (fusionMark hn g j hz hb hc b)) := by
    rw [← selectedMarkPerm_delMark hn g j hz hb hc S (fusionMark hn g j hz hb hc b),
      delMark_fusionMark]
  rw [h1, geoMarkSuccessor_delMark hn g j hz hb hc identify_deletion_marks _
    (selectedMarkPerm_ne_deleted g j S _ hb')]
  rfl

/-- `correspond_deletion.1`: the deletion's arc from a mark is the centre's arc from the same
mark, skipping `μ_j`. -/
theorem correspond_deletion_successor (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    ∀ b : Mark (deleteVertex g.center j),
      geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        delMark hn g j hz hb hc
          (if geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
              Sum.inl j
            then geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
            else geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S
              (fusionMark hn g j hz hb hc b)) := by
  intro b
  rw [geoSmoothingSuccessor_deletion hn g j hz hb hc S identify_deletion_marks b,
    skipJ_apply_of_ne hn g j hz hb hc S _ (fusionMark_ne_deleted hn g j hz hb hc b)]

omit [NeZero n] in
/-- Away from `μ_j`, the cycles of the skip permutation are the cycles of `ρ_S` (with `μ_j`
removed). -/
theorem sameCycle_skipJ_iff (S : Finset (Crossing g.center)) (x y : Mark g.center)
    (hx : x ≠ Sum.inl j) (hy : y ≠ Sum.inl j) :
    (skipJ hn g j hz hb hc S).SameCycle x y ↔
      (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).SameCycle x y := by
  set ρ := geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S with hρ
  set σ := skipJ hn g j hz hb hc S with hσ
  constructor
  · intro h
    obtain ⟨k, _, hk⟩ := h.exists_pow_eq'
    have hstep : ∀ z, ρ.SameCycle z (σ z) := by
      intro z
      by_cases hzj : z = Sum.inl j
      · rw [hzj, hσ, skipJ_deleted]
      · rw [hσ, skipJ_apply_of_ne hn g j hz hb hc S z hzj]
        split_ifs with h1
        · rw [← h1]
          exact ⟨2, by rw [zpow_two, Equiv.Perm.mul_apply]⟩
        · exact ⟨1, by rw [zpow_one]⟩
    have hpow : ∀ (m : ℕ) (z : Mark g.center), ρ.SameCycle z ((σ ^ m) z) := by
      intro m
      induction m with
      | zero =>
        intro z
        simp only [pow_zero, Equiv.Perm.one_apply]
        exact Equiv.Perm.SameCycle.refl _ _
      | succ m ih =>
        intro z
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact (ih z).trans (hstep _)
    rw [← hk]
    exact hpow k x
  · intro h
    obtain ⟨k, _, hk⟩ := h.exists_pow_eq'
    have hQ : ∀ (m : ℕ),
        ((ρ ^ m) x ≠ Sum.inl j → σ.SameCycle x ((ρ ^ m) x)) ∧
        ((ρ ^ m) x = Sum.inl j → σ.SameCycle x (ρ (Sum.inl j))) := by
      intro m
      induction m with
      | zero =>
        simp only [pow_zero, Equiv.Perm.one_apply]
        exact ⟨fun _ => Equiv.Perm.SameCycle.refl _ _, fun h0 => absurd h0 hx⟩
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        by_cases hzj : (ρ ^ m) x = Sum.inl j
        · have h2 := ih.2 hzj
          rw [hzj]
          exact ⟨fun _ => h2, fun _ => h2⟩
        · have h1 := ih.1 hzj
          constructor
          · intro hne
            have hs : σ ((ρ ^ m) x) = ρ ((ρ ^ m) x) := by
              rw [hσ, skipJ_apply_of_ne hn g j hz hb hc S _ hzj, ite_eq_right hne]
            rw [← hs]
            exact Equiv.Perm.sameCycle_apply_right.mpr h1
          · intro heq
            have hs : σ ((ρ ^ m) x) = ρ (Sum.inl j) := by
              rw [hσ, skipJ_apply_of_ne hn g j hz hb hc S _ hzj, ite_eq_left heq]
            rw [← hs]
            exact Equiv.Perm.sameCycle_apply_right.mpr h1
    have hfin := (hQ k).1 (by rw [hk]; exact hy)
    rw [hk] at hfin
    exact hfin

/-- `correspond_deletion.2`: two deletion marks lie on one carrier iff their centre images do. -/
theorem geoOwner_deletion_iff (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b b' : Mark (deleteVertex g.center j)) :
    geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b' ↔
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b') := by
  rw [geoOwner_eq_iff, geoOwner_eq_iff]
  set σ := skipJ hn g j hz hb hc S with hσ
  have hU : ∀ x, σ x ≠ Sum.inl j ↔ x ≠ Sum.inl j := skipJ_ne_deleted_iff hn g j hz hb hc S
  let e : Mark (deleteVertex g.center j) ≃ {x : Mark g.center // x ≠ Sum.inl j} :=
    { toFun := fun b => ⟨fusionMark hn g j hz hb hc b, fusionMark_ne_deleted hn g j hz hb hc b⟩
      invFun := fun x => delMark hn g j hz hb hc x.1
      left_inv := fun b => delMark_fusionMark hn g j hz hb hc b
      right_inv := fun x => Subtype.ext (fusionMark_delMark hn g j hz hb hc x.1 x.2) }
  have hconj : ∀ b, (σ.subtypePerm hU) (e b) =
      e (geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) b) := by
    intro b
    apply Subtype.ext
    change σ (fusionMark hn g j hz hb hc b) =
      fusionMark hn g j hz hb hc (geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) b)
    rw [geoSmoothingSuccessor_deletion hn g j hz hb hc S identify_deletion_marks b,
      fusionMark_delMark hn g j hz hb hc _ ((hU _).mpr (fusionMark_ne_deleted hn g j hz hb hc b))]
  rw [← sameCycle_of_equiv_conj _ (σ.subtypePerm hU) e hconj b b',
    Equiv.Perm.sameCycle_subtypePerm]
  exact sameCycle_skipJ_iff hn g j hz hb hc S _ _ (fusionMark_ne_deleted hn g j hz hb hc b)
    (fusionMark_ne_deleted hn g j hz hb hc b')

omit [NeZero n] in
/-- `central_vs_deletion_through_mu_j.1`: the mark after `μ_j` is not `μ_j`. -/
theorem geoSmoothingSuccessor_deleted_ne (S : Finset (Crossing g.center)) :
    geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j :=
  geoSmoothingSuccessor_vertex_ne_self (by omega) _ S j

/-- `correspond_deletion.3`: every centre carrier is the centre copy of a deletion carrier. -/
theorem centre_carrier_surjective_deletion (S : Finset (Crossing g.center)) :
    ∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      ∃ b : Mark (deleteVertex g.center j),
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) = q := by
  intro q
  obtain ⟨a, ha⟩ := geoOwner_surjective _ S q
  by_cases haj : a = Sum.inl j
  · refine ⟨delMark hn g j hz hb hc (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a), ?_⟩
    rw [fusionMark_delMark hn g j hz hb hc _
      (by rw [haj]; exact geoSmoothingSuccessor_deleted_ne hn g j hz hb hc S),
      geoOwner_successor, ha]
  · exact ⟨delMark hn g j hz hb hc a, by rw [fusionMark_delMark hn g j hz hb hc a haj, ha]⟩

/-- cor:flat-carriers (i), deletion: `correspond_deletion`, from U1's `identify_deletion_marks`. -/
theorem correspond_deletion_of_marks (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
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
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) = q) :=
  ⟨correspond_deletion_successor hn g j hz hb hc S identify_deletion_marks,
   geoOwner_deletion_iff hn g j hz hb hc S identify_deletion_marks,
   centre_carrier_surjective_deletion hn g j hz hb hc S⟩

/-! ### Cycle identities -/

/-- The marks of a deletion carrier are, up to rotation, the marks of its centre copy with `μ_j`
erased, read on the deletion. -/
theorem geoComponentMarkList_deletion_rotated (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b : Mark (deleteVertex g.center j)) :
    geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) ~r
      ((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).erase
          (Sum.inl j)).map (delMark hn g j hz hb hc) := by
  have hrot : (((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
      (delMark hn g j hz hb hc)) ~r geoMarkList (flatDeletionCG hn g j hz hb hc) :=
    Cycle.coe_eq_coe.mp identify_deletion_marks
  have hnodC := geoMarkList_nodup (flatCentreCG hn g j hz hb hc)
  unfold geoComponentMarkList
  refine (hrot.symm.filter _).trans ?_
  rw [List.filter_map, List.erase_filter]
  have heq : List.filter ((fun m => decide (geoOwner (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) m =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) ∘
        delMark hn g j hz hb hc)
        ((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)) =
      List.filter (fun m => decide (geoOwner (flatCentreCG hn g j hz hb hc) S m =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)))
        ((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)) := by
    apply List.filter_congr
    intro x hx
    have hx' : x ≠ Sum.inl j := (hnodC.mem_erase_iff.mp hx).1
    simp only [Function.comp]
    apply decide_eq_decide.mpr
    rw [geoOwner_deletion_iff hn g j hz hb hc S identify_deletion_marks,
      fusionMark_delMark hn g j hz hb hc x hx']
  rw [heq]

theorem isTrueCorner_delMark (S : Finset (Crossing g.center)) (a : Mark g.center) :
    IsTrueCorner (deletionSupport hn g j hz hb hc S) (delMark hn g j hz hb hc a) ↔
      IsTrueCorner S a := by
  cases a with
  | inl k => exact Iff.rfl
  | inr v =>
    rw [delMark_visit, isTrueCorner_visit, isTrueCorner_visit, fusionVisitEquiv_fst,
      mem_deletionSupport_iff]

/-- The corners of a deletion carrier are, up to rotation, the corners of its centre copy with
`μ_j` erased, read on the deletion. -/
theorem geoComponentCornerList_deletion_rotated (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b : Mark (deleteVertex g.center j)) :
    geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) ~r
      ((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).erase
          (Sum.inl j)).map (delMark hn g j hz hb hc) := by
  unfold geoComponentCornerList
  refine ((geoComponentMarkList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
    b).filter _).trans ?_
  rw [List.filter_map, List.erase_filter]
  have heq : List.filter ((fun a => decide (IsTrueCorner (deletionSupport hn g j hz hb hc S) a)) ∘
        delMark hn g j hz hb hc)
        ((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).erase
            (Sum.inl j)) =
      List.filter (fun a => decide (IsTrueCorner S a))
        ((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).erase
            (Sum.inl j)) := by
    apply List.filter_congr
    intro x _
    simp only [Function.comp]
    exact decide_eq_decide.mpr (isTrueCorner_delMark hn g j hz hb hc S x)
  rw [heq]

/-- A deletion mark and its centre image have the same plane point (`deleteVertex_apply`,
`crossingPoint_fusion`). -/
theorem geoMarkPosition_evaluation_fusionMark (m : Mark (deleteVertex g.center j)) :
    traversalEvaluation (deleteVertex g.center j)
        (geoMarkPosition (flatDeletionCG hn g j hz hb hc) m) =
      traversalEvaluation g.center
        (geoMarkPosition (flatCentreCG hn g j hz hb hc) (fusionMark hn g j hz hb hc m)) := by
  cases m with
  | inl i =>
    rw [fusionMark_vertex, geoMarkPosition_evaluation_vertex, geoMarkPosition_evaluation_vertex,
      deleteVertex_apply]
  | inr w =>
    rw [fusionMark_visit, geoMarkPosition_evaluation_visit, geoMarkPosition_evaluation_visit]
    have h := crossingPoint_fusion hn hz hb hc ((fusionVisitEquiv hn hz hb hc).symm w).1
    have hw : fusionCrossing hn hz hb hc ((fusionVisitEquiv hn hz hb hc).symm w).1 = w.1 := by
      change fusionCrossingEquiv hn hz hb hc _ = _
      rw [← fusionVisitEquiv_fst, Equiv.apply_symm_apply]
    rw [← hw, h]

/-- `central_vs_deletion_through_mu_j.2,.3`: the marks (corners) of the central carrier through
`μ_j`, with `μ_j` erased and read on the deletion, are the marks (corners) of its deletion copy,
as cycles. -/
theorem central_vs_deletion_cycles_of_marks (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
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
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) := by
  have hne := geoSmoothingSuccessor_deleted_ne hn g j hz hb hc S
  refine ⟨hne, ?_, ?_⟩
  · apply Cycle.coe_eq_coe.mpr
    have h := geoComponentMarkList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
      (delMark hn g j hz hb hc (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))
    rw [fusionMark_delMark hn g j hz hb hc _ hne, geoOwner_successor] at h
    exact h.symm
  · apply Cycle.coe_eq_coe.mpr
    have h := geoComponentCornerList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
      (delMark hn g j hz hb hc (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))
    rw [fusionMark_delMark hn g j hz hb hc _ hne, geoOwner_successor] at h
    exact h.symm

/-- cor:flat-carriers (i): `others_unchanged`, from U1's `identify_deletion_marks`. -/
theorem others_unchanged_of_marks (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    ∀ b : Mark (deleteVertex g.center j),
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
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
  intro b hne
  have hnotmem : Sum.inl j ∉ geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
      (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
    rw [mem_geoComponentMarkList]
    exact fun h => hne h.symm
  have hnotmem' : Sum.inl j ∉ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
    rw [mem_geoComponentCornerList]
    exact fun h => hne h.1.symm
  have hmap : ∀ (l : List (Mark g.center)), Sum.inl j ∉ l →
      (l.map (delMark hn g j hz hb hc)).map (fusionMark hn g j hz hb hc) = l := by
    intro l hl
    rw [List.map_map]
    refine (List.map_congr_left ?_).trans (List.map_id _)
    intro x hx
    exact fusionMark_delMark hn g j hz hb hc x (fun he => hl (he ▸ hx))
  have h1 : (geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        (fusionMark hn g j hz hb hc) ~r
      geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
    have h := (geoComponentMarkList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
      b).map (fusionMark hn g j hz hb hc)
    rw [List.erase_eq_self_iff.mpr hnotmem, hmap _ hnotmem] at h
    exact h
  have h2 : (geoComponentCornerList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        (fusionMark hn g j hz hb hc) ~r
      geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
    have h := (geoComponentCornerList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
      b).map (fusionMark hn g j hz hb hc)
    rw [List.erase_eq_self_iff.mpr hnotmem', hmap _ hnotmem'] at h
    exact h
  refine ⟨Cycle.coe_eq_coe.mpr h1, Cycle.coe_eq_coe.mpr h2, ?_⟩
  unfold geoComponentPlaneCycle
  apply Cycle.coe_eq_coe.mpr
  have h3 := h1.map (fun m => traversalEvaluation g.center
    (geoMarkPosition (flatCentreCG hn g j hz hb hc) m))
  rw [List.map_map] at h3
  have heq : (geoComponentMarkList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        (fun m => traversalEvaluation (deleteVertex g.center j)
          (geoMarkPosition (flatDeletionCG hn g j hz hb hc) m)) =
      (geoComponentMarkList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        ((fun m => traversalEvaluation g.center
          (geoMarkPosition (flatCentreCG hn g j hz hb hc) m)) ∘ fusionMark hn g j hz hb hc) :=
    List.map_congr_left (fun m _ => geoMarkPosition_evaluation_fusionMark hn g j hz hb hc m)
  rw [heq]
  exact h3

/-- Corner counts (for U4/U5): the deletion copy of the carrier through `μ_j` has exactly one
corner fewer than the central copy. -/
theorem geoCornerCount_deletion_through_mu_j (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    geoCornerCount (flatCentreCG hn g j hz hb hc) S (centralCarrierThroughJ hn g j hz hb hc S) =
      geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) + 1 := by
  have h := (central_vs_deletion_cycles_of_marks hn g j hz hb hc S identify_deletion_marks).2.2
  have hlen := (Cycle.coe_eq_coe.mp h).perm.length_eq
  have hmem : Sum.inl j ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (centralCarrierThroughJ hn g j hz hb hc S) :=
    (mem_geoComponentCornerList _ _ _ _).mpr ⟨rfl, isTrueCorner_vertex S j⟩
  rw [List.length_map, List.length_erase_of_mem hmem] at hlen
  have hpos := geoComponentCornerList_length_pos (flatCentreCG hn g j hz hb hc) S
    (centralCarrierThroughJ hn g j hz hb hc S)
  unfold geoCornerCount
  omega

/-- Corner counts (for U4/U5): every other carrier has the same number of corners at the centre
and on the deletion. -/
theorem geoCornerCount_deletion_other (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b : Mark (deleteVertex g.center j))
    (hne : geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
      centralCarrierThroughJ hn g j hz hb hc S) :
    geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      geoCornerCount (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
  have h := (others_unchanged_of_marks hn g j hz hb hc S identify_deletion_marks b hne).2.1
  have hlen := (Cycle.coe_eq_coe.mp h).perm.length_eq
  rw [List.length_map] at hlen
  exact hlen

end
end Deletion

/-! ## 6. `unique_through_mu_j`, `same_retained_crossings` -/

section Unique

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

omit [NeZero n] in
/-- cor:flat-carriers (i): `unique_through_mu_j` (centre: `flat_center_geometry` injectivity and
`flat_germ_spatial_data` at the parameter `0`; sides: `g1_vertices_injective` and
`flat_germ_spatial_data` at the side parameter). -/
theorem unique_through_mu_j_data (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) :
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
      q = geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) := by
  constructor
  · have hinj : Function.Injective g.center := (flat_center_geometry (by omega) hz hb).1
    have hcv : ∀ (c : Crossing g.center) (k : ZMod (n + 1)), crossingPoint c ≠ g.center k :=
      (flat_germ_spatial_data (by omega) g hz hb hc g.zeroParameter).2.2
    intro q
    constructor
    · rintro ⟨a, ha, hpt⟩
      cases a with
      | inl i =>
        rw [geoMarkPosition_evaluation_vertex] at hpt
        have hij : i = j := hinj hpt
        rw [← ha, hij]
        rfl
      | inr v =>
        rw [geoMarkPosition_evaluation_visit] at hpt
        exact absurd hpt (hcv v.1 j)
    · rintro rfl
      exact ⟨Sum.inl j, rfl, geoMarkPosition_evaluation_vertex _ j⟩
  · intro b q
    have hinj : Function.Injective (g.sideTuple b t).val :=
      g1_vertices_injective (flat_hn1 hn) (g.sideTuple b t).property.1
    have hcv : ∀ (c : Crossing (g.sideTuple b t).val) (k : ZMod (n + 1)),
        crossingPoint c ≠ (g.sideTuple b t).val k :=
      (flat_germ_spatial_data (by omega) g hz hb hc (g.sideTime b t)).2.2
    constructor
    · rintro ⟨a, ha, hpt⟩
      cases a with
      | inl i =>
        rw [geoMarkPosition_evaluation_vertex] at hpt
        have hij : i = j := hinj hpt
        rw [← ha, hij]
      | inr v =>
        rw [geoMarkPosition_evaluation_visit] at hpt
        exact absurd hpt (hcv v.1 j)
    · rintro rfl
      exact ⟨Sum.inl j, rfl, geoMarkPosition_evaluation_vertex _ j⟩

/-- cor:flat-carriers (ii): `same_retained_crossings`, from U1's `identify_sides_marks` and
`identify_deletion_marks`. -/
theorem same_retained_crossings_of_marks (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center))
    (identify_sides_marks : ∀ b : Bool,
      (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
        geoMarkList (flatSideCG hn g b t))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
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
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) := by
  constructor
  · intro b a x
    unfold geoCarrierCrossings
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [mem_transportSupport_iff]
    apply and_congr Iff.rfl
    constructor
    · intro h w hw
      obtain ⟨v, rfl⟩ := (visitTransport (hs b)).surjective w
      rw [visitTransport_crossing] at hw
      have hv : v.1 = x := (crossingTransport (hs b)).injective hw
      have hvo := h v hv
      rw [geoOwner_markTransport_iff _ _ (hs b) (identify_sides_marks b) S] at hvo
      exact hvo
    · intro h v hv
      have hvo := h (visitTransport (hs b) v) (by rw [visitTransport_crossing, hv])
      rw [geoOwner_markTransport_iff _ _ (hs b) (identify_sides_marks b) S]
      exact hvo
  · intro b x
    unfold geoCarrierCrossings
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [mem_deletionSupport_iff]
    apply and_congr Iff.rfl
    constructor
    · intro h w hw
      obtain ⟨v, rfl⟩ := (fusionVisitEquiv hn hz hb hc).surjective w
      rw [fusionVisitEquiv_fst] at hw
      have hv : v.1 = x := (fusionCrossingEquiv hn hz hb hc).injective hw
      have hvo := h v hv
      rw [← delMark_visit, geoOwner_deletion_iff hn g j hz hb hc S identify_deletion_marks,
        fusionMark_delMark hn g j hz hb hc _ Sum.inr_ne_inl]
      exact hvo
    · intro h v hv
      have hvo := h (fusionVisitEquiv hn hz hb hc v) (by rw [fusionVisitEquiv_fst, hv])
      rw [← delMark_visit, geoOwner_deletion_iff hn g j hz hb hc S identify_deletion_marks,
        fusionMark_delMark hn g j hz hb hc _ Sum.inr_ne_inl] at hvo
      exact hvo

end Unique

/-! ## 7. The U2 bundle -/

section Bundle

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- Everything U2 delivers, from U1's interface lemmas `identify_sides_marks`,
`identify_deletion_marks`, `independent_supports` (sides). Conjuncts, in order, with the exact
field statements of `FlatCarriersDefinitionData` / `FlatCarriersData`: `centre_carriers`,
`correspond_sides`, `correspond_deletion`, `unique_through_mu_j`,
`central_vs_deletion_through_mu_j.1-.3` (the two geometric conjuncts `StrictBetween` / positive
multiples are U3's), `others_unchanged`, `same_retained_crossings`. -/
theorem flat_carriers_U2 (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center))
    (identify_sides_marks : ∀ b : Bool,
      (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
        geoMarkList (flatSideCG hn g b t))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (independent_supports : ∀ b : Bool,
      IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    -- `centre_carriers`
    GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S ∧
    -- `correspond_sides`
    (∀ b : Bool,
      (∀ a : Mark g.center,
        geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
            (markTransport (hs b) a) =
          markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
      (∀ a a' : Mark g.center,
        geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
            geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a'))) ∧
    -- `correspond_deletion`
    ((∀ b : Mark (deleteVertex g.center j),
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
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) = q)) ∧
    -- `unique_through_mu_j`
    ((∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      (∃ a : Mark g.center, geoOwner (flatCentreCG hn g j hz hb hc) S a = q ∧
        traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) =
          g.center j) ↔
      q = centralCarrierThroughJ hn g j hz hb hc S) ∧
    (∀ (b : Bool) (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S)),
      (∃ a : Mark (g.sideTuple b t).val,
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) a = q ∧
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) a) =
          (g.sideTuple b t).val j) ↔
      q = geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j))) ∧
    -- `central_vs_deletion_through_mu_j.1-.3`
    (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j ∧
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
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j)))) ∧
    -- `others_unchanged`
    (∀ b : Mark (deleteVertex g.center j),
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
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))) ∧
    -- `same_retained_crossings`
    ((∀ (b : Bool) (a : Mark g.center) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a) ↔
      crossingTransport (hs b) x ∈ geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) ∧
    (∀ (b : Mark (deleteVertex g.center j)) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) ↔
      fusionCrossingEquiv hn hz hb hc x ∈
        geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))) :=
  ⟨centre_carriers_of_marks hn g j hz hb hc t hs S true (identify_sides_marks true)
      (independent_supports true),
   correspond_sides_of_marks hn g j hz hb hc t hs S identify_sides_marks,
   correspond_deletion_of_marks hn g j hz hb hc S identify_deletion_marks,
   unique_through_mu_j_data hn g j hz hb hc t hs S,
   central_vs_deletion_cycles_of_marks hn g j hz hb hc S identify_deletion_marks,
   others_unchanged_of_marks hn g j hz hb hc S identify_deletion_marks,
   same_retained_crossings_of_marks hn g j hz hb hc t hs S identify_sides_marks
     identify_deletion_marks⟩

end Bundle

end SM

/-! ********************************************************************************
    ## UNIT U3_CentreGeometry
    ******************************************************************************** -/

/-! # U3 — Corner geometry at the centre; turns (def:flat-carriers / cor:flat-carriers)

Prover unit U3 of work/drafts/flatcarriers/PLAN_FINAL.md §5, written 2026-09-13. Source rows:
def:flat-carriers / cor:flat-carriers (reference/SM/sm-3-statesum.tex:788-905), under the
hypotheses of lem:flat-sides (sm-1-polygons.tex:778-826, accepted `SM.flat_sides`). Definitions and
bundles: the library module `SM.FlatCarriersDefs`.

Contents.
1. The successor gap `¬ traversalBetween (pos a) (pos u) (pos (ρ a))` is proved INTRINSICALLY on the
   geometric record domain (`geoNextMark_no_mark_between`), so no field of `GeoCarrierSpec` is needed
   for it.
2. Port of the direction lemmas of `SM/CarrierCrossings.lean:130-300` (and their supports in
   `CarrierMarkedSegments`, `CarrierSegmentGeometry`) from `Generic P` to `CrossingGeometry P`:
   `geoMarkSuccessor_position_cases`, `geoSmoothingSegment_positive_direction`, the incoming /
   outgoing directions at vertices and visits (`geo_vertex_incoming_direction`, …).
3. Block compression at the centre (`geo_block_compression`, without the union-of-segments clause),
   the corner chain from the inherited order (`geo_corner_chain`, from the `traced_successor` field
   of `GeoCarrierSpec` — U2's interface), and `geoCornerPolygon_edge` (each corner-polygon edge is a
   positive multiple of the centre edge direction of the outgoing slot), `geoCornerPolygon_turn_eq_sign`.
4. The flat centre: `nonzero_segments`, `no_antiparallel`, `turns_nonzero` (`turn = 0 ↔ corner mark
   = inl j`), `StrictBetween` and the fused multiples at `μ_j`.
5. Sides and deletion (generic): the same clauses through `geoComponentEquivGeneric` and the accepted
   `carriers_clause_ii` machinery (`CarrierCornerPolygon.lean`), transported along the list equality
   `geoComponentCornerList_eq_generic` by `generic_corner_props`.
6. Turn signs: `same_turn_signs`, `centre_turn_signs`, `extra_corner`.

Assumed interface (explicit hypotheses, never a placeholder): U2's `GeoCarrierSpec (flatCentreCG …) S`
(only `traced_successor` is used), U1's `independent_supports` output in the form
`IsDecomposition … (transportSupport (hs b) S)` / `IsDecomposition … (deletionSupport … S)`, and the
side facts of lem:flat-sides read at the side parameter (chi agreement off `turnSupport j`, crossing
sign agreement), which `flat_sides_side_facts` below extracts from `FlatSidesData`. -/

namespace SM

open Carrier

namespace GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## 1. The successor gap, intrinsically -/

/-- No mark lies strictly in the oriented cyclic gap between a mark and its `ρ`-successor
(port of `nextMark_no_mark_between`; sorted-list argument, no genericity). -/
theorem geoNextMark_no_mark_between (hP : CrossingGeometry P) {a b : Mark P}
    (hnext : geoNextMark hP a = b) (u : Mark P) :
    ¬ traversalBetween (geoMarkPosition hP a) (geoMarkPosition hP u) (geoMarkPosition hP b) := by
  classical
  let d : DecidableEq (Mark P) := inferInstance
  let _ := geoMarkLinearOrder hP
  rw [geoNextMark_eq_list_next] at hnext
  have hnext' : @List.next (Mark P) d (Finset.univ : Finset (Mark P)).sort a
      ((Finset.mem_sort _).mpr (Finset.mem_univ a)) = b := hnext
  have hd : d = (fun a b : Mark P => LinearOrder.toDecidableEq a b) := Subsingleton.elim _ _
  rw [hd] at hnext'
  exact sorted_next_no_cyclic_between (Finset.univ : Finset (Mark P))
    (Finset.mem_univ a) (Finset.mem_univ b) hnext' u (Finset.mem_univ u)


/-- `ρ` has no fixed mark: its single cycle contains the distinct vertices `0` and `1`. -/
theorem geoMarkSuccessor_ne_self_of_three_le (hn : 3 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    geoMarkSuccessor hP a ≠ a := by
  have : Fact (1 < n) := ⟨by omega⟩
  intro ha
  have h0 := (geoMarkSuccessor_sameCycle hP a (Sum.inl (0 : ZMod n))).eq_of_left ha
  have h1 := (geoMarkSuccessor_sameCycle hP a (Sum.inl (1 : ZMod n))).eq_of_left ha
  have h01 : (0 : ZMod n) = 1 := Sum.inl.inj (h0.symm.trans h1)
  have hz : (0 : ℕ) = 1 := by
    simpa only [ZMod.val_zero, ZMod.val_one] using congrArg ZMod.val h01
  omega

/-! ## 2. Position cases and subsegment data (port of `CarrierMarkedSegments`) -/

/-- Consecutive marks lie in increasing parameter order on one edge, or the successor is the next
vertex (port of `markSuccessor_position_cases`). -/
theorem geoMarkSuccessor_position_cases (hn : 3 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    ((geoMarkPosition hP (geoMarkSuccessor hP a)).1 = (geoMarkPosition hP a).1 ∧
      (geoMarkPosition hP a).2.val < (geoMarkPosition hP (geoMarkSuccessor hP a)).2.val) ∨
      geoMarkSuccessor hP a = Sum.inl ((geoMarkPosition hP a).1 + 1) := by
  have : Fact (1 < n) := ⟨by omega⟩
  let p := geoMarkPosition hP a
  let r := geoMarkPosition hP (geoMarkSuccessor hP a)
  let i := p.1
  let r' := traversalShift i r
  let z : Set.Ico (0 : ℝ) 1 := ⟨0, le_rfl, zero_lt_one⟩
  have hp : traversalShift i p = ((0 : ZMod n), p.2) := by
    simp [traversalShift, i]
  have hv : traversalShift i (geoMarkPosition hP (Sum.inl (i + 1))) = ((1 : ZMod n), z) := by
    apply Prod.ext
    · change (i + 1) - i = 1
      abel
    · apply Subtype.ext
      rfl
  have hgap : ¬ traversalBetween ((0 : ZMod n), p.2) ((1 : ZMod n), z) r' := by
    intro h
    have hshift : traversalBetween (traversalShift i p)
        (traversalShift i (geoMarkPosition hP (Sum.inl (i + 1)))) (traversalShift i r) := by
      simpa only [hp, hv] using h
    exact (geoMarkSuccessor_no_mark_between hP a (Sum.inl (i + 1)))
      ((traversalBetween_shift i p (geoMarkPosition hP (Sum.inl (i + 1))) r).mp hshift)
  have hk0 : traversalKey ((0 : ZMod n), p.2) = p.2.val := by
    simp [traversalKey]
  have hk1 : traversalKey ((1 : ZMod n), z) = 1 := by
    simp [traversalKey, z, ZMod.val_one]
  have hne : traversalKey r' ≠ p.2.val := by
    intro he
    have hkey : traversalKey (traversalShift i r) = traversalKey (traversalShift i p) := by
      rw [hp, hk0]
      exact he
    have hrp : r = p := (traversalShiftEquiv i).injective (traversalKey_injective hkey)
    exact (geoMarkSuccessor_ne_self_of_three_le hn hP a) (geoMarkPosition_injective hP hrp)
  have hlt : p.2.val < traversalKey r' := by
    by_contra h
    have hle := le_of_not_gt h
    have hstrict := lt_of_le_of_ne hle hne
    apply hgap
    exact Or.inr (Or.inr ⟨by simpa only [hk0] using hstrict,
      by simpa only [hk0, hk1] using p.2.property.2⟩)
  have hle : traversalKey r' ≤ 1 := by
    by_contra h
    have hstrict : 1 < traversalKey r' := lt_of_not_ge h
    apply hgap
    exact Or.inl ⟨by simpa only [hk0, hk1] using p.2.property.2, by simpa only [hk1] using hstrict⟩
  have hval : r'.1.val ≤ 1 := by
    have hp0 := r'.2.property.1
    have hval' : (r'.1.val : ℝ) ≤ 1 := by
      dsimp only [traversalKey] at hle
      linarith
    exact_mod_cast hval'
  have hcases : r'.1.val = 0 ∨ r'.1.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hr0 : r'.1 = 0 := ZMod.val_injective n (by simpa only [ZMod.val_zero] using hzero)
    have hri : r.1 = p.1 := by
      have he : r.1 - i = 0 := hr0
      exact sub_eq_zero.mp he
    have hk : traversalKey r' = r.2.val := by
      change (r'.1.val : ℝ) + r.2.val = r.2.val
      rw [hr0, ZMod.val_zero, Nat.cast_zero, zero_add]
    exact Or.inl ⟨hri, by simpa only [hk] using hlt⟩
  · have hr1 : r'.1 = 1 := ZMod.val_injective n (hone.trans (ZMod.val_one n).symm)
    have hrt : r.2.val = 0 := by
      have hp0 : 0 ≤ r.2.val := r.2.property.1
      have hk : traversalKey r' = 1 + r.2.val := by
        change (r'.1.val : ℝ) + r.2.val = 1 + r.2.val
        rw [hr1, ZMod.val_one, Nat.cast_one]
      rw [hk] at hle
      linarith
    have hri : r.1 = i + 1 := by
      have he : r.1 - i = 1 := hr1
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp he)
    right
    apply geoMarkPosition_injective hP
    change r = geoMarkPosition hP (Sum.inl (i + 1))
    apply Prod.ext
    · exact hri
    · apply Subtype.ext
      exact hrt

/-- The `ρ`-successor lies a positive parameter distance ahead on the starting edge, up to and
including parameter one (port of `markSuccessor_subsegment_data`). -/
theorem geoMarkSuccessor_subsegment_data (hn : 3 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    ∃ t : ℝ, (geoMarkPosition hP a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP (geoMarkSuccessor hP a)) =
        edgePoint P (geoMarkPosition hP a).1 t := by
  rcases geoMarkSuccessor_position_cases hn hP a with ⟨hi, ht⟩ | hv
  · refine ⟨(geoMarkPosition hP (geoMarkSuccessor hP a)).2.val, ht,
      (geoMarkPosition hP (geoMarkSuccessor hP a)).2.property.2.le, ?_⟩
    unfold traversalEvaluation
    rw [hi]
  · refine ⟨1, (geoMarkPosition hP a).2.property.2, le_rfl, ?_⟩
    rw [hv, geoMarkPosition_evaluation_vertex]
    exact (edgePoint_one P (geoMarkPosition hP a).1).symm

/-- Both visits of a crossing evaluate to the crossing point, so the selected exchange keeps the
plane point (port of `selectedMarkPerm_evaluation`). -/
theorem geoSelectedMarkPerm_evaluation (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP (selectedMarkPerm S a)) =
      traversalEvaluation P (geoMarkPosition hP a) := by
  cases a with
  | inl i => rfl
  | inr v =>
    rw [selectedMarkPerm_visit, geoMarkPosition_evaluation_visit,
      geoMarkPosition_evaluation_visit, selectedVisitTwin_crossing]

/-- The outgoing segment of `a` is a positive piece of the edge of its outgoing slot (port of
`smoothingSegment_subsegment_data`). -/
theorem geoSmoothingSegment_subsegment_data (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    let p := geoMarkPosition hP (selectedMarkPerm S a)
    ∃ t : ℝ, p.2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP a) = edgePoint P p.1 p.2.val ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
        edgePoint P p.1 t ∧
      ∀ u : ℝ, geoSmoothingSegment hP S a u = edgePoint P p.1 (p.2.val + u * (t - p.2.val)) := by
  dsimp only
  obtain ⟨t, hst, ht1, he⟩ := geoMarkSuccessor_subsegment_data hn hP (selectedMarkPerm S a)
  have hstart : traversalEvaluation P (geoMarkPosition hP a) =
      edgePoint P (geoMarkPosition hP (selectedMarkPerm S a)).1
        (geoMarkPosition hP (selectedMarkPerm S a)).2.val :=
    (geoSelectedMarkPerm_evaluation hP S a).symm
  have hend : traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
      edgePoint P (geoMarkPosition hP (selectedMarkPerm S a)).1 t := he
  refine ⟨t, hst, ht1, hstart, hend, ?_⟩
  intro u
  unfold geoSmoothingSegment
  rw [hstart, hend, edgePoint_affine]

/-- The displacement from a mark to its `ρ_S`-successor is a positive multiple of the edge of its
outgoing slot (port of `smoothingSegment_positive_direction`). -/
theorem geoSmoothingSegment_positive_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) -
        traversalEvaluation P (geoMarkPosition hP a) =
        c • edge P (geoMarkPosition hP (selectedMarkPerm S a)).1 := by
  obtain ⟨t, hst, _, hstart, hend, _⟩ := geoSmoothingSegment_subsegment_data hn hP S a
  refine ⟨t - (geoMarkPosition hP (selectedMarkPerm S a)).2.val, sub_pos.mpr hst, ?_⟩
  rw [hstart, hend, edgePoint_sub_edgePoint]

theorem geoSmoothingSegment_displacement_ne_zero (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) -
      traversalEvaluation P (geoMarkPosition hP a) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S a
  rw [he]
  exact smul_ne_zero (ne_of_gt hc) (hP.1 _)

theorem geoSmoothingSuccessor_ne_self (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) : geoSmoothingSuccessor hP S a ≠ a := by
  intro he
  have hne := geoSmoothingSegment_displacement_ne_zero hn hP S a
  rw [he, sub_self] at hne
  exact hne rfl

/-! ## 3. Edges of incoming segments (port of `CarrierCrossings` §2, §4) -/

/-- The mark before a crossing visit lies on the visit's own edge. -/
theorem geoMarkSuccessor_symm_visit_edge (hn : 3 ≤ n) (hP : CrossingGeometry P) (v : Visit P) :
    (geoMarkPosition hP ((geoMarkSuccessor hP).symm (Sum.inr v))).1 = v.2.val := by
  have hb : geoMarkSuccessor hP ((geoMarkSuccessor hP).symm (Sum.inr v)) = Sum.inr v :=
    (geoMarkSuccessor hP).apply_symm_apply (Sum.inr v)
  rcases geoMarkSuccessor_position_cases hn hP ((geoMarkSuccessor hP).symm (Sum.inr v)) with
    ⟨hi, _⟩ | hv
  · rw [hb] at hi
    exact hi.symm
  · rw [hb] at hv
    exact (Sum.inr_ne_inl hv).elim

/-- The mark before the vertex `i` lies on the edge `i - 1`. -/
theorem geoMarkSuccessor_symm_vertex_edge (hn : 3 ≤ n) (hP : CrossingGeometry P) (i : ZMod n) :
    (geoMarkPosition hP ((geoMarkSuccessor hP).symm (Sum.inl i))).1 = i - 1 := by
  have hb : geoMarkSuccessor hP ((geoMarkSuccessor hP).symm (Sum.inl i)) = Sum.inl i :=
    (geoMarkSuccessor hP).apply_symm_apply (Sum.inl i)
  rcases geoMarkSuccessor_position_cases hn hP ((geoMarkSuccessor hP).symm (Sum.inl i)) with
    ⟨_, ht⟩ | hv
  · rw [hb] at ht
    have h0 : (0 : ℝ) ≤ (geoMarkPosition hP ((geoMarkSuccessor hP).symm (Sum.inl i))).2.val :=
      (geoMarkPosition hP ((geoMarkSuccessor hP).symm (Sum.inl i))).2.property.1
    have hz : (geoMarkPosition hP (Sum.inl i)).2.val = 0 := rfl
    rw [hz] at ht
    exact absurd ht (not_lt.mpr h0)
  · rw [hb] at hv
    have he := Sum.inl.inj hv
    exact eq_sub_iff_add_eq.mpr he.symm

/-- The incoming displacement at `a` is a positive multiple of the edge of its `ρ`-predecessor. -/
theorem geoSmoothingSegment_positive_direction_of_succ (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {a b : Mark P} (hba : geoSmoothingSuccessor hP S b = a) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP a) - traversalEvaluation P (geoMarkPosition hP b) =
        c • edge P (geoMarkPosition hP ((geoMarkSuccessor hP).symm a)).1 := by
  have hsel : selectedMarkPerm S b = (geoMarkSuccessor hP).symm a := by
    rw [Equiv.eq_symm_apply]
    exact hba
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S b
  rw [hba, hsel] at he
  exact ⟨c, hc, he⟩

theorem geoSmoothingSegment_incoming_positive_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP a) -
        traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm a)) =
        c • edge P (geoMarkPosition hP ((geoMarkSuccessor hP).symm a)).1 :=
  geoSmoothingSegment_positive_direction_of_succ hn hP S
    ((geoSmoothingSuccessor hP S).apply_symm_apply a)

/-- Incoming direction at a visit: a positive multiple of the visited edge. -/
theorem geo_visit_incoming_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) -
        traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inr v))) =
        c • edge P v.2.val := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_incoming_positive_direction hn hP S (Sum.inr v)
  rw [geoMarkSuccessor_symm_visit_edge hn hP v] at he
  exact ⟨c, hc, he⟩

/-- Outgoing direction at a selected visit: a positive multiple of the twin's edge. -/
theorem geo_selected_visit_outgoing_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inr v))) -
        traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) =
        c • edge P (visitTwin v).2.val := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S (Sum.inr v)
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv] at he
  exact ⟨c, hc, he⟩

/-- Outgoing direction at an unselected visit: along its own edge. -/
theorem geo_unselected_visit_outgoing_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inr v))) -
        traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) =
        c • edge P v.2.val := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S (Sum.inr v)
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv] at he
  exact ⟨c, hc, he⟩

/-- Outgoing direction at the vertex `i`: a positive multiple of `edge P i`. -/
theorem geo_vertex_outgoing_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inl i))) - P i =
        c • edge P i := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S (Sum.inl i)
  rw [selectedMarkPerm_vertex, geoMarkPosition_evaluation_vertex] at he
  exact ⟨c, hc, he⟩

/-- Incoming direction at the vertex `i`: a positive multiple of `edge P (i - 1)`. -/
theorem geo_vertex_incoming_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    ∃ c : ℝ, 0 < c ∧
      P i - traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inl i))) =
        c • edge P (i - 1) := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_incoming_positive_direction hn hP S (Sum.inl i)
  rw [geoMarkSuccessor_symm_vertex_edge hn hP i, geoMarkPosition_evaluation_vertex] at he
  exact ⟨c, hc, he⟩


/-! ## 4. Outgoing slot, incoming edge, block compression (port of `CarrierCornerPolygon` §0-2) -/

/-- The original traversal position of the outgoing slot of `a`: `a` itself if unselected, its twin
if selected. -/
def geoOutSlot (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    TraversalPoint n :=
  geoMarkPosition hP (selectedMarkPerm S a)

/-- The original edge carrying the incoming segment at `b` (the edge of its `ρ`-predecessor). -/
def geoInEdge (hP : CrossingGeometry P) (b : Mark P) : ZMod n :=
  (geoMarkPosition hP ((geoMarkSuccessor hP).symm b)).1

omit [NeZero n] in
theorem geometricVisitPosition_edge (hP : CrossingGeometry P) (v : Visit P) :
    (geometricVisitPosition hP v).1 = v.2.val := rfl

omit [NeZero n] in
theorem geometricVisitPosition_parameter (hP : CrossingGeometry P) (v : Visit P) :
    (geometricVisitPosition hP v).2.val = visitParameter v := rfl

omit [NeZero n] in
theorem geoOutSlot_vertex (hP : CrossingGeometry P) (S : Finset (Crossing P)) (i : ZMod n) :
    (geoOutSlot hP S (Sum.inl i)).1 = i := rfl

theorem geoOutSlot_selected (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P)
    (hv : v.1 ∈ S) : (geoOutSlot hP S (Sum.inr v)).1 = (visitTwin v).2.val := by
  unfold geoOutSlot
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv]
  rfl

theorem geoOutSlot_unselected (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P)
    (hv : v.1 ∉ S) : geoOutSlot hP S (Sum.inr v) = geometricVisitPosition hP v := by
  unfold geoOutSlot
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv]
  rfl

theorem geoInEdge_vertex (hn : 3 ≤ n) (hP : CrossingGeometry P) (i : ZMod n) :
    geoInEdge hP (Sum.inl i) = i - 1 :=
  geoMarkSuccessor_symm_vertex_edge hn hP i

theorem geoInEdge_visit (hn : 3 ≤ n) (hP : CrossingGeometry P) (v : Visit P) :
    geoInEdge hP (Sum.inr v) = v.2.val :=
  geoMarkSuccessor_symm_visit_edge hn hP v

/-- If `ρ_S x = b`, the outgoing edge of `x` is the incoming edge of `b`. -/
theorem geoOutSlot_eq_of_succ (hP : CrossingGeometry P) (S : Finset (Crossing P)) {x b : Mark P}
    (hxb : geoSmoothingSuccessor hP S x = b) : (geoOutSlot hP S x).1 = geoInEdge hP b := by
  unfold geoOutSlot geoInEdge
  have hsel : selectedMarkPerm S x = (geoMarkSuccessor hP).symm b := by
    rw [Equiv.eq_symm_apply]
    exact hxb
  rw [hsel]

theorem geo_evaluation_eq_outSlot (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP a) =
      edgePoint P (geoOutSlot hP S a).1 (geoOutSlot hP S a).2.val :=
  (geoSelectedMarkPerm_evaluation hP S a).symm

theorem geo_subsegment_data (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) :
    ∃ t : ℝ, (geoOutSlot hP S a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
        edgePoint P (geoOutSlot hP S a).1 t := by
  obtain ⟨t, hst, ht1, _, hend, _⟩ := geoSmoothingSegment_subsegment_data hn hP S a
  exact ⟨t, hst, ht1, hend⟩

/-- An incoming segment ending at a crossing visit starts earlier on that visit's own edge. -/
theorem geo_incoming_visit_position (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (x : Mark P) (v : Visit P)
    (hx : geoSmoothingSuccessor hP S x = Sum.inr v) :
    (geoOutSlot hP S x).1 = v.2.val ∧ (geoOutSlot hP S x).2.val < visitParameter v := by
  unfold geoOutSlot
  have he : geoMarkSuccessor hP (selectedMarkPerm S x) = Sum.inr v := hx
  rcases geoMarkSuccessor_position_cases hn hP (selectedMarkPerm S x) with ⟨hi, ht⟩ | hv
  · constructor
    · simpa only [he, geoMarkPosition_visit, geometricVisitPosition_edge] using hi.symm
    · simpa only [he, geoMarkPosition_visit, geometricVisitPosition_parameter] using ht
  · have hbad := he.symm.trans hv
    cases hbad

/-- **Block compression at the centre** (port of `ccp_block_compression`, without the
union-of-segments clause): the marks `ρ_S a, …, ρ_S^{m-1} a` being unselected visits, all outgoing
slots of the block lie on the edge `e` of the outgoing slot of `a`, and `ρ_S^m a` is the point of a
parameter `t > s` on `e`. -/
theorem geo_block_compression (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) (m : ℕ) (hm : 1 ≤ m)
    (hmid : ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a)) :
    (∀ r < m, (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ r) a)).1 = (geoOutSlot hP S a).1) ∧
    ∃ t : ℝ, (geoOutSlot hP S a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S ^ m) a)) =
        edgePoint P (geoOutSlot hP S a).1 t := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      obtain ⟨t, hst, ht1, hend⟩ := geo_subsegment_data hn hP S a
      refine ⟨?_, t, hst, ht1, ?_⟩
      · intro r hr
        have hr0 : r = 0 := by omega
        subst hr0
        rw [pow_zero, Equiv.Perm.one_apply]
      · rw [zero_add, pow_one]
        exact hend
    · have hmid' : ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a) :=
        fun r h1 h2 => hmid r h1 (by omega)
      obtain ⟨hedges, t, hst, ht1, hend⟩ := ih hmpos hmid'
      have hedge : edge P (geoOutSlot hP S a).1 ≠ 0 := hP.1 _
      obtain ⟨v, hxv, hvS⟩ := ccp_not_trueCorner S (hmid m hmpos (Nat.lt_succ_self m))
      have hprev : geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP S ^ (m - 1)) a) =
          (geoSmoothingSuccessor hP S ^ m) a := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ']
        congr 2
        omega
      have hin := geo_incoming_visit_position hn hP S _ v (hprev.trans hxv)
      have hedge_prev : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ (m - 1)) a)).1 =
          (geoOutSlot hP S a).1 :=
        hedges (m - 1) (by omega)
      have hev : v.2.val = (geoOutSlot hP S a).1 := hin.1.symm.trans hedge_prev
      have hslot : geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a) =
          geometricVisitPosition hP v := by
        rw [hxv]
        exact geoOutSlot_unselected hP S v hvS
      have hxeval : traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S ^ m) a)) =
          edgePoint P (geoOutSlot hP S a).1 (visitParameter v) := by
        rw [hxv, geoMarkPosition_visit]
        change edgePoint P v.2.val (visitParameter v) = _
        rw [hev]
      have htv : t = visitParameter v := edgePoint_injective hedge (hend.symm.trans hxeval)
      obtain ⟨t', hst', ht1', hend'⟩ := geo_subsegment_data hn hP S ((geoSmoothingSuccessor hP S ^ m) a)
      have hslot1 : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a)).1 = (geoOutSlot hP S a).1 := by
        rw [hslot]
        exact hev
      have hslot2 : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a)).2.val = t := by
        rw [hslot, htv]
        rfl
      rw [hslot2] at hst'
      rw [hslot1] at hend'
      refine ⟨?_, t', lt_trans hst hst', ht1', ?_⟩
      · intro r hr
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | hr'
        · exact hedges r hr'
        · rw [hr']
          exact hslot1
      · rw [pow_succ', Equiv.Perm.mul_apply]
        exact hend'

/-! ## 5. The corner chain from the inherited order (U2's `traced_successor`) -/

/-- The inherited-order field of `GeoCarrierSpec` at one carrier `q`: consecutive entries of
`geoComponentMarkList hP S q` are `ρ_S`-successors (cyclically). -/
abbrev TracedSuccessor (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    Prop :=
  ∀ i : Fin (geoComponentMarkList hP S q).length,
    geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
      (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))

theorem tracedSuccessor_of_spec (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (hspec : GeoCarrierSpec hP S) (q : GeoComponent hP S) : TracedSuccessor hP S q :=
  hspec.traced_successor q

theorem geoCornerMark_mem (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    geoOwner hP S (geoCornerMark hP S q k) = q ∧ IsTrueCorner S (geoCornerMark hP S q k) :=
  (mem_geoComponentCornerList hP S q _).mp (List.getElem_mem (ZMod.val_lt k))

theorem geoCornerMark_mem_cornerList (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP S q k ∈ geoComponentCornerList hP S q :=
  List.getElem_mem (ZMod.val_lt k)

/-- The corner after `c_k` is the next corner of the corner list, cyclically (port of
`ccpCornerMark_add_one`). -/
theorem geoCornerMark_add_one (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP S q (k + 1) =
      (geoComponentCornerList hP S q).next (geoCornerMark hP S q k)
        (geoCornerMark_mem_cornerList hP S q k) := by
  unfold geoCornerMark
  rw [List.next_getElem _ (geoComponentCornerList_nodup hP S q) k.val (ZMod.val_lt k)]
  have hval : (k + 1).val = (k.val + 1) % (geoComponentCornerList hP S q).length := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rfl
  simp only [hval]

/-- **Corner-to-corner chain at the centre.** From a true corner `a` of `q`, the next corner of the
corner list is reached in `m ≥ 1` steps of `ρ_S`, every intermediate mark not being a true corner.
Derived from the inherited order (`TracedSuccessor`) and the list lemma `firstCornerBlock`. -/
theorem geo_corner_chain (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (htr : TracedSuccessor hP S q) (a : Mark P) (ha : geoOwner hP S a = q) (hac : IsTrueCorner S a) :
    ∃ m : ℕ, 1 ≤ m ∧
      (geoSmoothingSuccessor hP S ^ m) a =
        (geoComponentCornerList hP S q).next a ((mem_geoComponentCornerList hP S q a).mpr ⟨ha, hac⟩) ∧
      ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a) := by
  set L := geoComponentMarkList hP S q with hLdef
  have hNL : L.Nodup := geoComponentMarkList_nodup hP S q
  have haL : a ∈ L := (mem_geoComponentMarkList hP S q a).mpr ha
  obtain ⟨A, R, hAR⟩ := List.mem_iff_append.mp haL
  have hrot : L.rotate A.length = a :: (R ++ A) := by
    rw [hAR, List.rotate_append_length_eq, List.cons_append]
  have hN : (a :: (R ++ A)).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr hNL
  have hk : A.length ≤ L.length := by
    rw [hAR]
    simp
  let p : Mark P → Bool := fun m => decide (IsTrueCorner S m)
  have hpa : p a = true := by simp only [p, hac, decide_true]
  obtain ⟨M, b, B, hsplit, hM, hb, hnext, hprefix, _, _⟩ := firstCornerBlock p a (R ++ A) hN hpa
  have heqOn : Set.EqOn (a :: (R ++ A)).formPerm (geoSmoothingSuccessor hP S)
      {m | m ∈ a :: (R ++ A)} := by
    intro m hm
    have hmL : m ∈ L := by
      have hm' : m ∈ L.rotate A.length := by
        rw [hrot]
        exact hm
      exact List.mem_rotate.mp hm'
    obtain ⟨i, hi, hmi⟩ := List.getElem_of_mem hmL
    change (a :: (R ++ A)).formPerm m = geoSmoothingSuccessor hP S m
    rw [← hrot, List.formPerm_rotate L hNL, ← hmi, List.formPerm_apply_getElem L hNL i hi]
    exact (htr ⟨i, hi⟩).symm
  have hpow : ∀ i (hi : i < M.length + 2),
      (geoSmoothingSuccessor hP S ^ i) a = (a :: (M ++ [b]))[i]'(by simp; omega) := by
    intro i hi
    have hlen := hprefix.length_le
    simp at hlen
    rw [ccp_pow_apply_closed_list _ a (R ++ A) hN heqOn i (by simp only [List.length_append]; omega)]
    exact (hprefix.getElem (by simp; omega)).symm
  have hrotF : (L.filter p) ~r ((a :: (R ++ A)).filter p) := by
    rw [← hrot, List.rotate_eq_drop_append_take hk, List.filter_append]
    conv_lhs => rw [← List.take_append_drop A.length L, List.filter_append]
    exact List.isRotated_append
  have haK : a ∈ geoComponentCornerList hP S q :=
    (mem_geoComponentCornerList hP S q a).mpr ⟨ha, hac⟩
  have hnextK : (geoComponentCornerList hP S q).next a haK = b := by
    rw [← hnext]
    exact List.isRotated_next_eq hrotF (hNL.filter p) haK
  refine ⟨M.length + 1, by omega, ?_, ?_⟩
  · rw [hnextK, hpow (M.length + 1) (by omega)]
    simp
  · intro r hr1 hrm
    rw [hpow r (by omega)]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r' < M.length := by omega
    rw [List.getElem_cons_succ, List.getElem_append_left hr']
    intro hc
    have hMx := hM _ (List.getElem_mem hr')
    simp only [p, hc, decide_true] at hMx
    exact Bool.true_eq_false.mp hMx

/-! ## 6. Edges and turns of the corner polygon at the centre -/

/-- **Compressed block between consecutive corners at the centre**: `c_{k+1}` is reached from `c_k`
in `m ≥ 1` steps through non-corners, the edge `c_{k+1} - c_k` of the corner polygon is a positive
multiple of the direction of the edge `e` of the outgoing slot of `c_k`, and `e` is the incoming
edge at `c_{k+1}`. -/
theorem geoCornerPolygon_edge_data (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (htr : TracedSuccessor hP S q) (k : ZMod (geoCornerCount hP S q)) :
    ∃ m : ℕ, 1 ≤ m ∧
      (geoSmoothingSuccessor hP S ^ m) (geoCornerMark hP S q k) = geoCornerMark hP S q (k + 1) ∧
      (∀ r, 1 ≤ r → r < m →
        ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q k))) ∧
      (∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hP S q) k =
        c • edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1) ∧
      (geoOutSlot hP S (geoCornerMark hP S q k)).1 = geoInEdge hP (geoCornerMark hP S q (k + 1)) := by
  obtain ⟨m, hm, hchain, hmid⟩ := geo_corner_chain hP S q htr _ (geoCornerMark_mem hP S q k).1
    (geoCornerMark_mem hP S q k).2
  rw [← geoCornerMark_add_one hP S q k] at hchain
  obtain ⟨hedges, t, hst, ht1, hend⟩ := geo_block_compression hn hP S _ m hm hmid
  have hstart : geoCornerPolygon hP S q k =
      edgePoint P (geoOutSlot hP S (geoCornerMark hP S q k)).1
        (geoOutSlot hP S (geoCornerMark hP S q k)).2.val :=
    geo_evaluation_eq_outSlot hP S _
  have hend' : geoCornerPolygon hP S q (k + 1) =
      edgePoint P (geoOutSlot hP S (geoCornerMark hP S q k)).1 t := by
    show traversalEvaluation P (geoMarkPosition hP (geoCornerMark hP S q (k + 1))) = _
    rw [← hchain]
    exact hend
  refine ⟨m, hm, hchain, hmid, ⟨t - (geoOutSlot hP S (geoCornerMark hP S q k)).2.val,
    sub_pos.mpr hst, ?_⟩, ?_⟩
  · show geoCornerPolygon hP S q (k + 1) - geoCornerPolygon hP S q k = _
    rw [hstart, hend', edgePoint_sub_edgePoint]
  · have hprev : geoSmoothingSuccessor hP S
        ((geoSmoothingSuccessor hP S ^ (m - 1)) (geoCornerMark hP S q k)) =
        geoCornerMark hP S q (k + 1) := by
      rw [← hchain, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [← geoOutSlot_eq_of_succ hP S hprev]
    exact (hedges (m - 1) (by omega)).symm

/-- **`geoCornerPolygon_edge_centre`**: each edge of the corner polygon is a positive multiple of the
direction of the original edge of the outgoing slot of its starting corner. -/
theorem geoCornerPolygon_edge (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (htr : TracedSuccessor hP S q) (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hP S q) k =
      c • edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  obtain ⟨_, _, _, _, hc, _⟩ := geoCornerPolygon_edge_data hn hP S q htr k
  exact hc

theorem geoCornerPolygon_outEdge_eq_inEdge (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) :
    (geoOutSlot hP S (geoCornerMark hP S q k)).1 = geoInEdge hP (geoCornerMark hP S q (k + 1)) := by
  obtain ⟨_, _, _, _, _, he⟩ := geoCornerPolygon_edge_data hn hP S q htr k
  exact he

/-- The incoming corner-polygon edge at `c_k` is a positive multiple of the original edge carrying
the incoming segment at `c_k`. -/
theorem geoCornerPolygon_edge_pred (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (htr : TracedSuccessor hP S q) (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hP S q) (k - 1) =
      c • edge P (geoInEdge hP (geoCornerMark hP S q k)) := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge hn hP S q htr (k - 1)
  refine ⟨c, hc, ?_⟩
  rw [he, geoCornerPolygon_outEdge_eq_inEdge hn hP S q htr (k - 1), sub_add_cancel]

theorem geoCornerPolygon_turn_det (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (htr : TracedSuccessor hP S q) (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      det (edge (geoCornerPolygon hP S q) (k - 1)) (edge (geoCornerPolygon hP S q) k) =
        c * det (edge P (geoInEdge hP (geoCornerMark hP S q k)))
          (edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1) := by
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred hn hP S q htr k
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge hn hP S q htr k
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, ?_⟩
  rw [he₁, he₂, ccp_det_smul_smul]

/-- **`turn = sign det(in, out)`** at every corner of a centre carrier. -/
theorem geoCornerPolygon_turn_eq_sign (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k =
      SignType.sign (det (edge P (geoInEdge hP (geoCornerMark hP S q k)))
        (edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1)) := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_turn_det hn hP S q htr k
  rw [turn_det, he, sign_mul, sign_pos hc, one_mul]

/-- Every corner-polygon edge of a centre carrier is nonzero. -/
theorem geoCornerPolygon_edge_ne_zero (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) : edge (geoCornerPolygon hP S q) k ≠ 0 := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge hn hP S q htr k
  rw [he]
  exact smul_ne_zero hc.ne' (hP.1 _)

/-- Where the original in/out determinant is nonzero the corner is not antiparallel. -/
theorem geoCornerPolygon_not_antiparallel_of_det (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q))
    (hdet : det (edge P (geoInEdge hP (geoCornerMark hP S q k)))
      (edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1) ≠ 0) :
    ¬ ∃ r : ℝ, r < 0 ∧
      edge (geoCornerPolygon hP S q) k = r • edge (geoCornerPolygon hP S q) (k - 1) := by
  rintro ⟨r, _, hr⟩
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_turn_det hn hP S q htr k
  apply mul_ne_zero hc.ne' hdet
  rw [← he, hr]
  exact det_smul_self _ r


/-! ## 7. Generic configurations: transfer along `geoComponentCornerList_eq_generic` -/

/-- The closed polygon read at the entries of a nonempty list (`geoCornerPolygon` and
`ccpCornerPolygon` are both of this form, definitionally). -/
abbrev polyOfList {α : Type*} (L : List α) [NeZero L.length] (pos : α → Plane) :
    LabelledTuple L.length :=
  fun k => pos (L[k.val]'(ZMod.val_lt k))

/-- The accepted clause (ii) facts (`CarrierCornerPolygon.lean`), stated for any list equal to the
accepted corner list and any position map equal to the accepted one, so that they transport along a
propositional equality of lists (the index types `ZMod L.length` are identified by `subst`). -/
theorem generic_corner_props (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (q' : Component hn hP S) (L : List (Mark P))
    (hL : L = ccpCornerList hn hP S q') [hNZ : NeZero L.length] (pos : Mark P → Plane)
    (hpos : pos = fun a => traversalEvaluation P (markPosition hn hP.1 a)) (k : ZMod L.length) :
    edge (polyOfList L pos) k ≠ 0 ∧
    (¬ ∃ r : ℝ, r < 0 ∧ edge (polyOfList L pos) k = r • edge (polyOfList L pos) (k - 1)) ∧
    turn (polyOfList L pos) k ≠ 0 ∧
    turn (polyOfList L pos) k =
      SignType.sign (det (edge P (ccpInEdge hn hP (L[k.val]'(ZMod.val_lt k))))
        (edge P (ccpOutSlot hn hP S (L[k.val]'(ZMod.val_lt k))).1)) := by
  subst hpos
  subst hL
  exact ⟨ccpCornerPolygon_edge_ne_zero hn hP hS q' k, ccpCornerPolygon_not_antiparallel hn hP hS q' k,
    ccpCornerPolygon_turn_ne_zero hn hP hS q' k, ccpCornerPolygon_turn_eq_sign hn hP hS q' k⟩

/-- **Generic configurations (sides, deletion).** On a generic polygon with `S` independent, every
`geoCornerPolygon` has nonzero edges, no antiparallel corner, nonzero turns, and
`turn = sign det(in, out)` in the accepted in/out-edge bookkeeping. -/
theorem generic_geoCornerPolygon_props (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (q : GeoComponent (generic_crossingGeometry hn hP) S)
    (k : ZMod (geoCornerCount (generic_crossingGeometry hn hP) S q)) :
    edge (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k ≠ 0 ∧
    (¬ ∃ r : ℝ, r < 0 ∧ edge (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k =
      r • edge (geoCornerPolygon (generic_crossingGeometry hn hP) S q) (k - 1)) ∧
    turn (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k ≠ 0 ∧
    turn (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k =
      SignType.sign (det (edge P (ccpInEdge hn hP (geoCornerMark (generic_crossingGeometry hn hP) S q k)))
        (edge P (ccpOutSlot hn hP S (geoCornerMark (generic_crossingGeometry hn hP) S q k)).1)) := by
  have h := @generic_corner_props n _ P hn hP S hS (geoComponentEquivGeneric hn hP S q)
    (geoComponentCornerList (generic_crossingGeometry hn hP) S q)
    (geoComponentCornerList_eq_generic hn hP S q) (geoCornerCount_neZero _ S q)
    (fun a => traversalEvaluation P (geoMarkPosition (generic_crossingGeometry hn hP) a))
    (by funext a; rw [geoMarkPosition_eq_generic hn hP]) k
  exact h

/-- On a generic polygon, `geoCornerTurn` at a true corner `a` is `sign det(in, out)`. -/
theorem generic_geoCornerTurn (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) {a : Mark P} (ha : IsTrueCorner S a) :
    geoCornerTurn (generic_crossingGeometry hn hP) S a =
      SignType.sign (det (edge P (ccpInEdge hn hP a)) (edge P (ccpOutSlot hn hP S a).1)) := by
  unfold geoCornerTurn
  have h := (generic_geoCornerPolygon_props hn hP hS (geoOwner _ S a) (geoCornerIndex _ S a)).2.2.2
  rw [geoCornerMark_geoCornerIndex _ S ha] at h
  exact h

theorem generic_geoCornerTurn_vertex (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (i : ZMod n) :
    geoCornerTurn (generic_crossingGeometry hn hP) S (Sum.inl i) = turn P i := by
  rw [generic_geoCornerTurn hn hP hS (isTrueCorner_vertex S i), ccpInEdge_vertex, ccpOutSlot_vertex,
    turn_det]

theorem generic_geoCornerTurn_visit (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (v : Visit P) (hv : v.1 ∈ S) :
    geoCornerTurn (generic_crossingGeometry hn hP) S (Sum.inr v) =
      crossingSign P v.2.val (visitTwin v).2.val := by
  rw [generic_geoCornerTurn hn hP hS ((isTrueCorner_visit S v).mpr hv), ccpInEdge_visit,
    ccpOutSlot_selected hn hP S v hv]
  rfl

/-! ## 8. Small helpers -/

omit [NeZero n] in
/-- Two positive multiples of one nonzero vector in sequence: the middle point is strictly between. -/
theorem strictBetween_of_positive_multiples {a x b w : Plane} (hw : w ≠ 0) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hxa : x - a = α • w) (hbx : b - x = β • w) : StrictBetween a x b := by
  have hba : b - a = (α + β) • w := by
    rw [add_smul, ← hxa, ← hbx]
    abel
  have hsum : α + β ≠ 0 := by linarith
  refine ⟨?_, α / (α + β), div_pos hα (by linarith), ?_, ?_⟩
  · intro hab
    rw [hab, sub_self] at hba
    exact smul_ne_zero hsum hw hba.symm
  · rw [div_lt_one (by linarith)]
    linarith
  · rw [hba, smul_smul, div_mul_cancel₀ _ hsum, ← hxa]
    abel

omit [NeZero n] in
theorem turn_eq_crossingSign (Q : LabelledTuple n) (i : ZMod n) :
    turn Q i = crossingSign Q (i - 1) i := by
  rw [turn_det]
  rfl

/-- The fused-edge index of `k - 1` is the fused-edge index of `k` minus one, for `k ≠ j`. -/
theorem fusionIndex_sub_one {j k : ZMod (n + 1)} (hk : k ≠ j) :
    fusionIndex j (k - 1) = fusionIndex j k - 1 := by
  obtain ⟨ι, rfl⟩ := deletionIndex_exhaust j hk
  rw [fusionIndex_deletionIndex]
  by_cases hι : ι = 0
  · subst hι
    rw [deletionIndex_zero, add_sub_cancel_right, fusionIndex_deleted]
    ring
  · have hι' : ι - 1 ≠ -1 := by
      intro h
      apply hι
      linear_combination h
    have hnext := deletionIndex_next j hι'
    rw [sub_add_cancel] at hnext
    have h2 : deletionIndex j ι - 1 = deletionIndex j (ι - 1) := by
      rw [hnext]
      ring
    rw [h2, fusionIndex_deletionIndex]





end
end GeoCarrier

/-! ## 9. The flat centre -/

section FlatCentre

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Original in/out determinant at a true corner of the centre: nonzero away from `μ_j` (vertex:
`τ_i ≠ 0` for `i ≠ j`, lem:flat-sides (i); selected visit: transversality of the crossing), zero at
`μ_j` (`τ_j = 0`). -/
theorem flat_centre_corner_det (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) (a : Mark g.center)
    (hac : IsTrueCorner S a) :
    (a ≠ Sum.inl j →
      det (edge g.center (geoInEdge (flatCentreCG hn g j hz hb hc) a))
        (edge g.center (geoOutSlot (flatCentreCG hn g j hz hb hc) S a).1) ≠ 0) ∧
    (a = Sum.inl j →
      det (edge g.center (geoInEdge (flatCentreCG hn g j hz hb hc) a))
        (edge g.center (geoOutSlot (flatCentreCG hn g j hz hb hc) S a).1) = 0) := by
  have hturn : ∀ i, turn g.center i = 0 ↔ i = j :=
    (flat_center_geometry (by omega) hz hb).2.2.2.1
  cases a with
  | inl i =>
    rw [geoInEdge_vertex (flat_hn1 hn), geoOutSlot_vertex]
    constructor
    · intro hij
      have hi : i ≠ j := fun h => hij (congrArg Sum.inl h)
      have hne : turn g.center i ≠ 0 := fun h => hi ((hturn i).mp h)
      rw [turn_det] at hne
      exact sign_ne_zero.mp hne
    · intro hij
      have hi : i = j := Sum.inl.inj hij
      have h0 : turn g.center i = 0 := (hturn i).mpr hi
      rw [turn_det] at h0
      exact sign_eq_zero_iff.mp h0
  | inr v =>
    have hv : v.1 ∈ S := hac
    rw [geoInEdge_visit (flat_hn1 hn), geoOutSlot_selected _ S v hv]
    refine ⟨fun _ => ?_, fun h => (Sum.inr_ne_inl h).elim⟩
    have hcr : IsCrossing g.center {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    exact crossing_det_ne_zero_of_geometry (flatCentreCG hn g j hz hb hc) hcr

omit [NeZero n] in
/-- **cor (i) at the centre, `turns_nonzero`:** a corner turn of a centre carrier vanishes exactly
at the corner `μ_j`. -/
theorem flat_centre_turn_zero_iff (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (k : ZMod (geoCornerCount (flatCentreCG hn g j hz hb hc) S q)) :
    turn (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k = 0 ↔
      geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j := by
  rw [geoCornerPolygon_turn_eq_sign (flat_hn1 hn) _ S q (hspec.traced_successor q) k,
    sign_eq_zero_iff]
  have hd := flat_centre_corner_det hn g j hz hb hc S _ (geoCornerMark_mem _ S q k).2
  constructor
  · intro h0
    by_contra hne
    exact hd.1 hne h0
  · exact hd.2

omit [NeZero n] in
/-- **cor (i) at the centre, `nonzero_segments` (corner edges).** -/
theorem flat_centre_edge_ne_zero (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (k : ZMod (geoCornerCount (flatCentreCG hn g j hz hb hc) S q)) :
    edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k ≠ 0 :=
  geoCornerPolygon_edge_ne_zero (flat_hn1 hn) _ S q (hspec.traced_successor q) k

omit [NeZero n] in
/-- **cor (i) at the centre, `nonzero_segments` (inherited subsegments).** -/
theorem flat_centre_segment_ne (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) (a : Mark g.center) :
    traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ≠
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) :=
  sub_ne_zero.mp (geoSmoothingSegment_displacement_ne_zero (flat_hn1 hn) _ S a)

omit [NeZero n] in
/-- **cor (i) at the centre, `no_antiparallel`:** away from `μ_j` the in/out determinant is nonzero;
at `μ_j` the two consecutive corner edges are positive multiples of `edge C (j-1)` and
`edge C j = r • edge C (j-1)`, `r > 0`, hence positive multiples of each other. -/
theorem flat_centre_not_antiparallel (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (k : ZMod (geoCornerCount (flatCentreCG hn g j hz hb hc) S q)) :
    ¬ ∃ r : ℝ, r < 0 ∧
      edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k =
        r • edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) (k - 1) := by
  have htr := hspec.traced_successor q
  have hd := flat_centre_corner_det hn g j hz hb hc S _ (geoCornerMark_mem _ S q k).2
  by_cases hk : geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j
  · rintro ⟨ρ, hρ, he⟩
    obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred (flat_hn1 hn) _ S q htr k
    obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge (flat_hn1 hn) _ S q htr k
    rw [hk, geoInEdge_vertex (flat_hn1 hn)] at he₁
    rw [hk, geoOutSlot_vertex] at he₂
    obtain ⟨r, hr, hrj⟩ := (flat_center_geometry (by omega) hz hb).2.2.2.2.1
    have hne : edge g.center (j - 1) ≠ 0 := (flat_center_geometry (by omega) hz hb).2.1 _
    rw [he₁, he₂, hrj, smul_smul, smul_smul] at he
    have hcoef : c₂ * r = ρ * c₁ := smul_left_injective ℝ hne he
    have h1 : 0 < c₂ * r := mul_pos hc₂ hr
    have h2 : ρ * c₁ < 0 := mul_neg_of_neg_of_pos hρ hc₁
    linarith
  · exact geoCornerPolygon_not_antiparallel_of_det (flat_hn1 hn) _ S q htr k (hd.1 hk)

/-- **cor (i) at the centre, the geometric conjuncts of `central_vs_deletion_through_mu_j`:** `μ_j`
lies strictly between its carrier neighbours, both incident displacements being positive multiples
of the fused direction `edge D (-1) = μ_{j+1} - μ_{j-1}` (eq. flatpr:fusion). -/
theorem flat_centre_mu_j_between (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) :
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
        s • edge (deleteVertex g.center j) (-1)) := by
  obtain ⟨r, hr0, hr1, hprev, hnext, _⟩ := (flat_fusion_data hn hz hb hc).2.1
  obtain ⟨c, hc0, hin⟩ := geo_vertex_incoming_direction (flat_hn1 hn) (flatCentreCG hn g j hz hb hc) S j
  obtain ⟨c', hc'0, hout⟩ := geo_vertex_outgoing_direction (flat_hn1 hn) (flatCentreCG hn g j hz hb hc) S j
  rw [hprev, smul_smul] at hin
  rw [hnext, smul_smul] at hout
  have hw : edge (deleteVertex g.center j) (-1) ≠ 0 := (flatDeletionCG hn g j hz hb hc).1 _
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  exact ⟨strictBetween_of_positive_multiples hw (mul_pos hc0 hr0) (mul_pos hc'0 h1r) hin hout,
    c * r, c' * (1 - r), mul_pos hc0 hr0, mul_pos hc'0 h1r, hin, hout⟩

end
end FlatCentre

/-! ## 10. Turn signs across the four configurations -/

section FlatTurnSigns

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- The two side facts of lem:flat-sides used by U3, read at one side `b` of the side parameter
`t`: chi agrees with the centre off `turnSupport j` (clause (i)), and crossing signs agree with the
centre at every centre crossing (clause (ii), `GeometricRecordsAgree`). -/
def SideFacts (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (b : Bool) (t : g.SideParameter) : Prop :=
  (∀ a b' c : ZMod (n + 1), a ≠ b' → b' ≠ c → a ≠ c →
    ({a, b', c} : Finset (ZMod (n + 1))) ≠ turnSupport j →
    chi (g.sideTuple b t).val a b' c = chi g.center a b' c) ∧
  (∀ i k : ZMod (n + 1), IsCrossing g.center {i, k} →
    crossingSign (g.sideTuple b t).val i k = crossingSign g.center i k)

/-- `SideFacts` hold on both sides for every side parameter below lem:flat-sides' radius
(extraction from the accepted `FlatSidesData`). -/
theorem flat_sides_side_facts (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (hF : FlatSidesData hn g j hz hb hc) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧
      ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool, SideFacts g j b t := by
  obtain ⟨_, _, _, _, _, _, δ, hδ, hδr, _, hloc⟩ := hF
  refine ⟨δ, hδ, hδr, ?_⟩
  intro t ht b
  have habs : |(g.sideTime b t).val| < δ := by
    cases b <;> simp only [WallGerm.sideTime, Bool.false_eq_true, ↓reduceIte, abs_neg,
      abs_of_pos t.property.1] <;> exact ht
  obtain ⟨hchi, _, _, _, _, hrec, _⟩ := hloc (g.sideTime b t) habs
  obtain ⟨_, _, _, _, hsign⟩ := hrec
  exact ⟨fun a b' c h1 h2 h3 h4 => (hchi a b' c h1 h2 h3 h4).1, hsign⟩

omit [NeZero n] in
/-- Away from `j`, the vertex turn on a side is the centre's (`chi` agreement off `turnSupport j`,
`turnSupport` injective for `n + 1 ≥ 4`). -/
theorem side_turn_eq_centre (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (b : Bool)
    (t : g.SideParameter) (hsf : SideFacts g j b t) (i : ZMod (n + 1)) (hi : i ≠ j) :
    turn (g.sideTuple b t).val i = turn g.center i := by
  have : Fact (1 < n + 1) := ⟨by omega⟩
  have hts : turnSupport i ≠ turnSupport j := fun h => hi (turnSupport_injective (by omega) h)
  exact hsf.1 (i - 1) i (i + 1) (prev_ne_self i) (next_ne_self i).symm (prev_ne_next (by omega) i) hts

/-- Away from `j`, the vertex turn on the deletion at the fused index is the centre's
(`crossingSign_fusion` for all index pairs, and `fusionIndex_sub_one`). -/
theorem deletion_turn_eq_centre (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (i : ZMod (n + 1)) (hi : i ≠ j) :
    turn (deleteVertex g.center j) (fusionIndex j i) = turn g.center i := by
  have hcs := (flat_fusion_data hn hz hb hc).2.2.2.2.2.2.2.2.2.1
  rw [turn_eq_crossingSign, turn_eq_crossingSign, ← fusionIndex_sub_one hi]
  exact hcs _ _

omit [NeZero n] in
/-- The turn of a centre carrier at an original vertex `i` is `τ_i` of the centre. -/
theorem flat_centre_geoCornerTurn_vertex (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S) (i : ZMod (n + 1)) :
    geoCornerTurn (flatCentreCG hn g j hz hb hc) S (Sum.inl i) = turn g.center i := by
  unfold geoCornerTurn
  rw [geoCornerPolygon_turn_eq_sign (flat_hn1 hn) _ S _ (hspec.traced_successor _),
    geoCornerMark_geoCornerIndex _ S (isTrueCorner_vertex S i), geoInEdge_vertex (flat_hn1 hn),
    geoOutSlot_vertex, turn_det]

omit [NeZero n] in
/-- The turn of a centre carrier at a selected visit `v` is `sgn det(d_{v.2}, d_{twin.2})`. -/
theorem flat_centre_geoCornerTurn_visit (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S) (v : Visit g.center) (hv : v.1 ∈ S) :
    geoCornerTurn (flatCentreCG hn g j hz hb hc) S (Sum.inr v) =
      crossingSign g.center v.2.val (visitTwin v).2.val := by
  unfold geoCornerTurn
  rw [geoCornerPolygon_turn_eq_sign (flat_hn1 hn) _ S _ (hspec.traced_successor _),
    geoCornerMark_geoCornerIndex _ S ((isTrueCorner_visit S v).mpr hv), geoInEdge_visit (flat_hn1 hn),
    geoOutSlot_selected _ S v hv]
  rfl

/-- **cor (ii) `same_turn_signs`.** -/
theorem flat_same_turn_signs (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) (hsf : ∀ b : Bool, SideFacts g j b t)
    (hST : ∀ b : Bool, IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))
    (hSD : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a → ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
        geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (delMark hn g j hz hb hc a) := by
  intro a ha hac b
  cases a with
  | inl i =>
    have hi : i ≠ j := fun h => ha (congrArg Sum.inl h)
    change geoCornerTurn _ _ (Sum.inl i) = geoCornerTurn _ _ (Sum.inl (fusionIndex j i))
    rw [generic_geoCornerTurn_vertex (flat_hn1 hn) _ (hST b), generic_geoCornerTurn_vertex hn _ hSD,
      side_turn_eq_centre hn g j b t (hsf b) i hi, deletion_turn_eq_centre hn g j hz hb hc i hi]
  | inr v =>
    have hv : v.1 ∈ S := hac
    have hcs := (flat_fusion_data hn hz hb hc).2.2.2.2.2.2.2.2.2.1
    have hcr : IsCrossing g.center {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    change geoCornerTurn _ _ (Sum.inr (visitTransport (hs b) v)) =
      geoCornerTurn _ _ (Sum.inr (fusionVisitEquiv hn hz hb hc v))
    have hvT : (visitTransport (hs b) v).1 ∈ transportSupport (hs b) S :=
      (mem_transportSupport_iff (hs b) S v.1).mpr hv
    have hvD : (fusionVisitEquiv hn hz hb hc v).1 ∈ deletionSupport hn g j hz hb hc S :=
      (mem_deletionSupport_iff hn g j hz hb hc S v.1).mpr hv
    rw [generic_geoCornerTurn_visit (flat_hn1 hn) _ (hST b) _ hvT,
      generic_geoCornerTurn_visit hn _ hSD _ hvD, ← visitTransport_visitTwin,
      ← fusionVisitEquiv_visitTwin hn hz hb hc v, visitTransport_edge, visitTransport_edge,
      fusionVisit_edge hn hz hb hc v, fusionVisit_edge hn hz hb hc (visitTwin v),
      (hsf b).2 _ _ hcr, hcs]

/-- **cor (ii), flagged broadening `centre_turn_signs`.** -/
theorem flat_centre_turn_signs (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (hSD : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a →
      geoCornerTurn (flatCentreCG hn g j hz hb hc) S a =
        geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (delMark hn g j hz hb hc a) := by
  intro a ha hac
  cases a with
  | inl i =>
    have hi : i ≠ j := fun h => ha (congrArg Sum.inl h)
    change _ = geoCornerTurn _ _ (Sum.inl (fusionIndex j i))
    rw [flat_centre_geoCornerTurn_vertex hn g j hz hb hc S hspec i,
      generic_geoCornerTurn_vertex hn _ hSD, deletion_turn_eq_centre hn g j hz hb hc i hi]
  | inr v =>
    have hv : v.1 ∈ S := hac
    have hcs := (flat_fusion_data hn hz hb hc).2.2.2.2.2.2.2.2.2.1
    change _ = geoCornerTurn _ _ (Sum.inr (fusionVisitEquiv hn hz hb hc v))
    have hvD : (fusionVisitEquiv hn hz hb hc v).1 ∈ deletionSupport hn g j hz hb hc S :=
      (mem_deletionSupport_iff hn g j hz hb hc S v.1).mpr hv
    rw [flat_centre_geoCornerTurn_visit hn g j hz hb hc S hspec v hv,
      generic_geoCornerTurn_visit hn _ hSD _ hvD, ← fusionVisitEquiv_visitTwin hn hz hb hc v,
      fusionVisit_edge hn hz hb hc v, fusionVisit_edge hn hz hb hc (visitTwin v), hcs]

omit [NeZero n] in
/-- **cor (ii) `extra_corner`.** -/
theorem flat_extra_corner (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (t : g.SideParameter) (hs : CommonSupports g t) (S : Finset (Crossing g.center))
    (hST : ∀ b : Bool, IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) =
        turn (g.sideTuple b t).val j ∧
      (IsRightSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = -1) ∧
      (IsLeftSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = 1) := by
  intro b
  have h := generic_geoCornerTurn_vertex (flat_hn1 hn) (g.sideTuple b t).property (hST b) j
  exact ⟨h, fun hr => h.trans hr, fun hl => h.trans hl⟩

end
end FlatTurnSigns

/-! ## 11. The U3 bundle: the six cor fields and the two geometric conjuncts, verbatim -/

section U3Bundle

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- The fields of `FlatCarriersData` owned by U3, with the statements copied verbatim from
`SM/FlatCarriersDefs.lean` (`nonzero_segments`, `no_antiparallel`, `turns_nonzero`,
`same_turn_signs`, `centre_turn_signs`, `extra_corner`), plus the two geometric conjuncts of
`central_vs_deletion_through_mu_j` (`mu_j_between`, `mu_j_fused_multiples`). -/
structure FlatCarriersU3Data (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
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
  mu_j_between :
    StrictBetween
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))))
      (g.center j)
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j))))
  mu_j_fused_multiples :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      g.center j - traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))) =
        r • edge (deleteVertex g.center j) (-1) ∧
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j))) - g.center j =
        s • edge (deleteVertex g.center j) (-1)

/-- **U3, assembled.** Hypotheses beyond lem:flat-sides' domain: U2's `GeoCarrierSpec` at the centre
(only `traced_successor` is used), U1's `independent_supports` output on both sides and on the
deletion, and the side facts of lem:flat-sides at `t` (`flat_sides_side_facts`). -/
theorem flat_carriers_U3 (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (hsf : ∀ b : Bool, SideFacts g j b t)
    (hST : ∀ b : Bool, IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))
    (hSD : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    FlatCarriersU3Data hn g j hz hb hc t hs S where
  nonzero_segments := by
    refine ⟨flat_centre_segment_ne hn g j hz hb hc S,
      flat_centre_edge_ne_zero hn g j hz hb hc S hspec, ?_, ?_, ?_⟩
    · intro b
      exact sub_ne_zero.mp (geoSmoothingSegment_displacement_ne_zero hn _ _ b)
    · intro q k
      exact (generic_geoCornerPolygon_props hn (generic_deleteVertex hn hz hb hc) hSD q k).1
    · intro b
      refine ⟨fun a => sub_ne_zero.mp (geoSmoothingSegment_displacement_ne_zero (flat_hn1 hn) _ _ a),
        fun q k => ?_⟩
      exact (generic_geoCornerPolygon_props (flat_hn1 hn) (g.sideTuple b t).property (hST b) q k).1
  no_antiparallel := by
    refine ⟨flat_centre_not_antiparallel hn g j hz hb hc S hspec, ?_, ?_⟩
    · intro q k
      exact (generic_geoCornerPolygon_props hn (generic_deleteVertex hn hz hb hc) hSD q k).2.1
    · intro b q k
      exact (generic_geoCornerPolygon_props (flat_hn1 hn) (g.sideTuple b t).property (hST b) q k).2.1
  turns_nonzero := by
    refine ⟨flat_centre_turn_zero_iff hn g j hz hb hc S hspec, ?_, ?_⟩
    · intro q k
      exact (generic_geoCornerPolygon_props hn (generic_deleteVertex hn hz hb hc) hSD q k).2.2.1
    · intro b q k
      exact (generic_geoCornerPolygon_props (flat_hn1 hn) (g.sideTuple b t).property (hST b) q k).2.2.1
  same_turn_signs := flat_same_turn_signs hn g j hz hb hc t hs S hsf hST hSD
  centre_turn_signs := flat_centre_turn_signs hn g j hz hb hc S hspec hSD
  extra_corner := flat_extra_corner hn g j t hs S hST
  mu_j_between := (flat_centre_mu_j_between hn g j hz hb hc S).1
  mu_j_fused_multiples := (flat_centre_mu_j_between hn g j hz hb hc S).2

end U3Bundle

end SM

/-! ********************************************************************************
    ## UNIT U4_Rotation
    ******************************************************************************** -/

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

Interface hypotheses (assumed explicitly as arguments, never a placeholder; each is a projection of a
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

/-! ********************************************************************************
    ## UNIT U5_Selector
    ******************************************************************************** -/

/-! # U5 — Selector (cor:flat-carriers (iii))

Prover unit U5 of work/drafts/flatcarriers/PLAN_FINAL.md §5, written 2026-09-13. Proves the three
selector fields of `SM.FlatCarriersData` (SM/FlatCarriersDefs.lean):

* `selector_def` — the printed definition "a carrier's selector is `1` if all its turns are right,
  `(-1)^c` if all its `c` turns are left, and `0` if its turns are mixed" (sm-3:824-826), as the
  three defining clauses of `cornerSelector`, and `geoCarrierSelector = cornerSelector ∘ geoCornerPolygon`;
* `selector_identity` — eq. flatpr:selector-identity `W_right − W_left = W_del` for the carrier
  through `μ_j`, by the exhaustive table flatpr:selector-table (sm-3:893-905):
  surviving turns mixed → `0 − 0 = 0`; all right → `1 − 0 = 1`; all left with `c` surviving corners
  → `0 − (−1)^{c+1} = (−1)^c`;
* `other_selectors_agree` — "All other corresponding carrier selectors agree" (sm-3:831-832): every
  other carrier "retain[s] all [its] corner signs and counts" (sm-3:906-907), so the side copy's
  selector is the deletion copy's.

Interface. The three lemmas take as explicit hypotheses (never a placeholder) the fields of
`FlatCarriersData` proved by the units U2 (carrier correspondences and corner-cycle identities:
`correspond_sides`, `others_unchanged`, `central_vs_deletion_through_mu_j`) and U3 (turn transport:
`same_turn_signs`, `extra_corner`), stated verbatim as the fields so that the assembly (U1) can pass
`hD.correspond_sides` etc. (checked by the `example`s at the end). Not needed: `correspond_deletion`
(the corner-cycle identities already carry the corner correspondence), `turns_nonzero` (the table is
exhaustive over `SignType`, a zero turn counting as "mixed"), `hF`, and any hypothesis on `n, g, j`
beyond those in the fields' statements.

Everything is placeholder-free; `#print axioms` at the end: `propext, Classical.choice, Quot.sound`. -/

namespace SM

open Carrier GeoCarrier

/-! ## 0. `List.erase` on marks

Under the classical decidability instance the `BEq` instance elaborated for `Mark P = ZMod n ⊕ Visit P`
(the `.erase (Sum.inl j)` of the fields `identify_deletion_marks`, `central_vs_deletion_through_mu_j`)
is `Sum.instBEq`, for which the toolchain has no `LawfulBEq` instance; the `List.erase` lemmas
(`List.Nodup.mem_erase_iff`, `List.length_erase_of_mem`, …) need one. -/


noncomputable section

/-! ## 1. `cornerSelector`: the three defining clauses (sm-3:824-826) -/

section SelectorClauses

variable {k : ℕ} [NeZero k]

/-- "1 if all its turns are right" (`turn = -1`). -/
theorem cornerSelector_of_all_right (Q : LabelledTuple k) (h : ∀ i, turn Q i = -1) :
    cornerSelector Q = 1 := by
  unfold cornerSelector
  rw [ite_eq_left h]

/-- "(−1)^c if all its c turns are left" (`turn = +1`, `c = k`). -/
theorem cornerSelector_of_all_left (Q : LabelledTuple k) (h : ∀ i, turn Q i = 1) :
    cornerSelector Q = (-1 : ℤ) ^ k := by
  unfold cornerSelector
  have hnr : ¬ ∀ i, turn Q i = -1 := by
    intro hr
    have h0 := (hr 0).symm.trans (h 0)
    exact absurd h0 (by decide)
  rw [ite_eq_right hnr, ite_eq_left h]

/-- "0 if its turns are mixed". -/
theorem cornerSelector_of_mixed (Q : LabelledTuple k) (h1 : ¬ ∀ i, turn Q i = -1)
    (h2 : ¬ ∀ i, turn Q i = 1) : cornerSelector Q = 0 := by
  unfold cornerSelector
  rw [ite_eq_right h1, ite_eq_right h2]

/-- A carrier's selector is the selector of its corner polygon (by definition). -/
theorem geoCarrierSelector_eq_cornerSelector {n : ℕ} [NeZero n] {P : LabelledTuple n}
    (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCarrierSelector hP S q = cornerSelector (geoCornerPolygon hP S q) := rfl

end SelectorClauses

/-! ## 2. Turn bookkeeping: the turns of a corner polygon are the `geoCornerTurn`s at its corner
marks (certificate `geoCornerMark_geoCornerIndex`) -/

section TurnBookkeeping

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)
  (S : Finset (Crossing P))


theorem geoOwner_geoCornerMark (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoOwner hP S (geoCornerMark hP S q k) = q :=
  ((mem_geoComponentCornerList hP S q _).mp (geoCornerMark_mem_cornerList hP S q k)).1

theorem isTrueCorner_geoCornerMark (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    IsTrueCorner S (geoCornerMark hP S q k) :=
  ((mem_geoComponentCornerList hP S q _).mp (geoCornerMark_mem_cornerList hP S q k)).2

/-- The corner marks of a carrier are distinct (the corner list is duplicate-free). -/
theorem geoCornerMark_injective (q : GeoComponent hP S) :
    Function.Injective (geoCornerMark hP S q) := by
  intro k k' hkk'
  apply ZMod.val_injective
  exact ((geoComponentCornerList_nodup hP S q).getElem_inj_iff).mp hkk'

/-- The turn of a carrier at a corner mark `a` is the turn of its corner polygon at any index whose
corner is `a`. -/
theorem geoCornerTurn_eq_turn {a : Mark P} (ha : IsTrueCorner S a) {q : GeoComponent hP S}
    (hq : geoOwner hP S a = q) (k : ZMod (geoCornerCount hP S q))
    (hk : geoCornerMark hP S q k = a) :
    geoCornerTurn hP S a = turn (geoCornerPolygon hP S q) k := by
  subst hq
  unfold geoCornerTurn
  congr 1
  apply geoCornerMark_injective
  rw [geoCornerMark_geoCornerIndex hP S ha, hk]

/-- Conversely, an owned corner mark is some corner of its carrier, where the polygon's turn is the
carrier's turn at that mark. -/
theorem exists_turn_eq_geoCornerTurn {a : Mark P} (ha : IsTrueCorner S a) {q : GeoComponent hP S}
    (hq : geoOwner hP S a = q) :
    ∃ k : ZMod (geoCornerCount hP S q),
      geoCornerMark hP S q k = a ∧ turn (geoCornerPolygon hP S q) k = geoCornerTurn hP S a := by
  subst hq
  exact ⟨geoCornerIndex hP S a, geoCornerMark_geoCornerIndex hP S ha, rfl⟩

/-- The turn of a corner polygon at the index `k` is the carrier's turn at its `k`-th corner mark. -/
theorem turn_geoCornerPolygon_eq_geoCornerTurn (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k = geoCornerTurn hP S (geoCornerMark hP S q k) :=
  (geoCornerTurn_eq_turn hP S (isTrueCorner_geoCornerMark hP S q k)
    (geoOwner_geoCornerMark hP S q k) k rfl).symm

end TurnBookkeeping

/-! ## 3. Selector congruence: two polygons with the same number of corners and the same set of
turn values have the same selector -/

section SelectorCongr

/-- The selector depends only on the corner count and on the set of turn values. -/
theorem cornerSelector_congr {k k' : ℕ} [NeZero k] [NeZero k'] (Q : LabelledTuple k)
    (Q' : LabelledTuple k') (hk : k = k')
    (h1 : ∀ i, ∃ i', turn Q i = turn Q' i') (h2 : ∀ i', ∃ i, turn Q' i' = turn Q i) :
    cornerSelector Q = cornerSelector Q' := by
  subst hk
  have hall : ∀ s : SignType, (∀ i, turn Q i = s) ↔ (∀ i', turn Q' i' = s) := by
    intro s
    constructor
    · intro h i'
      obtain ⟨i, hi⟩ := h2 i'
      rw [hi, h i]
    · intro h i
      obtain ⟨i', hi'⟩ := h1 i
      rw [hi', h i']
  by_cases hR : ∀ i, turn Q i = -1
  · rw [cornerSelector_of_all_right Q hR, cornerSelector_of_all_right Q' ((hall _).mp hR)]
  · have hR' : ¬ ∀ i', turn Q' i' = -1 := fun h => hR ((hall _).mpr h)
    by_cases hL : ∀ i, turn Q i = 1
    · rw [cornerSelector_of_all_left Q hL, cornerSelector_of_all_left Q' ((hall _).mp hL)]
    · have hL' : ¬ ∀ i', turn Q' i' = 1 := fun h => hL ((hall _).mpr h)
      rw [cornerSelector_of_mixed Q hR hL, cornerSelector_of_mixed Q' hR' hL']

end SelectorCongr

/-! ## 4. The exhaustive table flatpr:selector-table (sm-3:893-905), abstractly

`QD` is the deletion copy (`c` corners, the surviving turns), `QR` / `QL` the right / left side
copies (`c + 1` corners each): one extra corner `kR` / `kL` with turn `-1` (right) / `+1` (left),
and the other corners' turns are exactly the surviving turns (in both directions). -/

section SelectorTable

theorem selector_table {c cR cL : ℕ} [NeZero c] [NeZero cR] [NeZero cL]
    (QD : LabelledTuple c) (QR : LabelledTuple cR) (QL : LabelledTuple cL)
    (hcR : cR = c + 1) (hcL : cL = c + 1) (kR : ZMod cR) (kL : ZMod cL)
    (hR : turn QR kR = -1) (hL : turn QL kL = 1)
    (hRD : ∀ k, k ≠ kR → ∃ k', turn QR k = turn QD k')
    (hDR : ∀ k', ∃ k, k ≠ kR ∧ turn QD k' = turn QR k)
    (hLD : ∀ k, k ≠ kL → ∃ k', turn QL k = turn QD k')
    (hDL : ∀ k', ∃ k, k ≠ kL ∧ turn QD k' = turn QL k) :
    cornerSelector QR - cornerSelector QL = cornerSelector QD := by
  subst hcR
  subst hcL
  -- the two extra corners spoil "all left" on the right side and "all right" on the left side
  have hR_not_left : ¬ ∀ k, turn QR k = 1 := fun h => absurd ((h kR).symm.trans hR) (by decide)
  have hL_not_right : ¬ ∀ k, turn QL k = -1 := fun h => absurd ((h kL).symm.trans hL) (by decide)
  by_cases hAR : ∀ k', turn QD k' = -1
  · -- row "all right": 1 − 0 = 1
    have hQR : ∀ k, turn QR k = -1 := by
      intro k
      by_cases hk : k = kR
      · rw [hk, hR]
      · obtain ⟨k', hk'⟩ := hRD k hk
        rw [hk', hAR k']
    have hQL_not_left : ¬ ∀ k, turn QL k = 1 := by
      intro h
      obtain ⟨k, -, hk⟩ := hDL 0
      have := (hAR 0).symm.trans (hk.trans (h k))
      exact absurd this (by decide)
    rw [cornerSelector_of_all_right QD hAR, cornerSelector_of_all_right QR hQR,
      cornerSelector_of_mixed QL hL_not_right hQL_not_left]
    norm_num
  · by_cases hAL : ∀ k', turn QD k' = 1
    · -- row "all left": 0 − (−1)^{c+1} = (−1)^c
      have hQL : ∀ k, turn QL k = 1 := by
        intro k
        by_cases hk : k = kL
        · rw [hk, hL]
        · obtain ⟨k', hk'⟩ := hLD k hk
          rw [hk', hAL k']
      have hQR_not_right : ¬ ∀ k, turn QR k = -1 := by
        intro h
        obtain ⟨k, -, hk⟩ := hDR 0
        have := (hAL 0).symm.trans (hk.trans (h k))
        exact absurd this (by decide)
      rw [cornerSelector_of_all_left QD hAL, cornerSelector_of_all_left QL hQL,
        cornerSelector_of_mixed QR hQR_not_right hR_not_left]
      rw [pow_succ]
      ring
    · -- row "mixed": 0 − 0 = 0
      push Not at hAR hAL
      obtain ⟨kr, hkr⟩ := hAR
      obtain ⟨kl, hkl⟩ := hAL
      have hQR_not_right : ¬ ∀ k, turn QR k = -1 := by
        intro h
        obtain ⟨k, -, hk⟩ := hDR kr
        exact hkr (hk.trans (h k))
      have hQL_not_left : ¬ ∀ k, turn QL k = 1 := by
        intro h
        obtain ⟨k, -, hk⟩ := hDL kl
        exact hkl (hk.trans (h k))
      have hQD_mixed : cornerSelector QD = 0 :=
        cornerSelector_of_mixed QD (fun h => hkr (h kr)) (fun h => hkl (h kl))
      rw [hQD_mixed, cornerSelector_of_mixed QR hQR_not_right hR_not_left,
        cornerSelector_of_mixed QL hL_not_right hQL_not_left]
      norm_num

end SelectorTable


/-! ## 5. Corner correspondences between two carriers (abstract)

A turn-preserving bijection of the corner marks of two carriers (in configurations of possibly
different sizes) gives equal corner counts and equal selectors; a bijection off one distinguished
corner gives the count `c + 1` and the turn data of the table. -/

section CornerCorrespondence

attribute [local instance] Classical.propDecidable

variable {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {P₁ : LabelledTuple m₁} {P₂ : LabelledTuple m₂}
  (h₁ : CrossingGeometry P₁) (S₁ : Finset (Crossing P₁)) (q₁ : GeoComponent h₁ S₁)
  (h₂ : CrossingGeometry P₂) (S₂ : Finset (Crossing P₂)) (q₂ : GeoComponent h₂ S₂)
  (f : Mark P₁ → Mark P₂) (g : Mark P₂ → Mark P₁)

/-- "All other carriers retain all their … counts": a bijection of corner marks gives equal corner
counts. -/
theorem geoCornerCount_eq_of_corner_bijection
    (hf : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁,
      f a ∈ geoComponentCornerList h₂ S₂ q₂ ∧ g (f a) = a)
    (hg : ∀ b ∈ geoComponentCornerList h₂ S₂ q₂,
      g b ∈ geoComponentCornerList h₁ S₁ q₁ ∧ f (g b) = b) :
    geoCornerCount h₁ S₁ q₁ = geoCornerCount h₂ S₂ q₂ := by
  unfold geoCornerCount
  have hperm : ((geoComponentCornerList h₁ S₁ q₁).map f).Perm (geoComponentCornerList h₂ S₂ q₂) := by
    rw [List.perm_ext_iff_of_nodup ((geoComponentCornerList_nodup h₁ S₁ q₁).map_on ?_)
      (geoComponentCornerList_nodup h₂ S₂ q₂)]
    · intro b
      rw [List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (hf a ha).1
      · intro hb
        exact ⟨g b, (hg b hb).1, (hg b hb).2⟩
    · intro a ha a' ha' hfa
      rw [← (hf a ha).2, ← (hf a' ha').2, hfa]
  rw [← hperm.length_eq, List.length_map]

/-- "All other carriers retain all their corner signs and counts": a turn-preserving bijection of
corner marks gives equal selectors. -/
theorem geoCarrierSelector_eq_of_corner_bijection
    (hf : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁,
      f a ∈ geoComponentCornerList h₂ S₂ q₂ ∧ g (f a) = a)
    (hg : ∀ b ∈ geoComponentCornerList h₂ S₂ q₂,
      g b ∈ geoComponentCornerList h₁ S₁ q₁ ∧ f (g b) = b)
    (hturn : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁,
      geoCornerTurn h₁ S₁ a = geoCornerTurn h₂ S₂ (f a)) :
    geoCarrierSelector h₁ S₁ q₁ = geoCarrierSelector h₂ S₂ q₂ := by
  rw [geoCarrierSelector_eq_cornerSelector, geoCarrierSelector_eq_cornerSelector]
  apply cornerSelector_congr _ _ (geoCornerCount_eq_of_corner_bijection h₁ S₁ q₁ h₂ S₂ q₂ f g hf hg)
  · intro k
    have ha := geoCornerMark_mem_cornerList h₁ S₁ q₁ k
    obtain ⟨hfa, -⟩ := hf _ ha
    obtain ⟨hown, hcor⟩ := (mem_geoComponentCornerList h₂ S₂ q₂ _).mp hfa
    obtain ⟨k', -, hk'⟩ := exists_turn_eq_geoCornerTurn h₂ S₂ hcor hown
    refine ⟨k', ?_⟩
    rw [hk', turn_geoCornerPolygon_eq_geoCornerTurn, hturn _ ha]
  · intro k'
    have hb := geoCornerMark_mem_cornerList h₂ S₂ q₂ k'
    obtain ⟨hgb, hfgb⟩ := hg _ hb
    obtain ⟨hown, hcor⟩ := (mem_geoComponentCornerList h₁ S₁ q₁ _).mp hgb
    obtain ⟨k, -, hk⟩ := exists_turn_eq_geoCornerTurn h₁ S₁ hcor hown
    refine ⟨k, ?_⟩
    rw [hk, turn_geoCornerPolygon_eq_geoCornerTurn, hturn _ hgb, hfgb]

/-- The distinguished carrier: its corners other than one distinguished corner `a₀` correspond
bijectively, with the same turns, to the corners of a second carrier. Then it has `c + 1` corners
(`c` the second carrier's count), `a₀` is its corner `k₀`, and its turns away from `k₀` are exactly
the second carrier's turns (in both directions) — the hypotheses of `selector_table`. -/
theorem corner_data_of_extra_corner (a₀ : Mark P₁) (ha₀ : a₀ ∈ geoComponentCornerList h₁ S₁ q₁)
    (hf : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁, a ≠ a₀ →
      f a ∈ geoComponentCornerList h₂ S₂ q₂ ∧ g (f a) = a)
    (hg : ∀ b ∈ geoComponentCornerList h₂ S₂ q₂,
      g b ∈ geoComponentCornerList h₁ S₁ q₁ ∧ g b ≠ a₀ ∧ f (g b) = b)
    (hturn : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁, a ≠ a₀ →
      geoCornerTurn h₁ S₁ a = geoCornerTurn h₂ S₂ (f a)) :
    geoCornerCount h₁ S₁ q₁ = geoCornerCount h₂ S₂ q₂ + 1 ∧
    ∃ k₀ : ZMod (geoCornerCount h₁ S₁ q₁), geoCornerMark h₁ S₁ q₁ k₀ = a₀ ∧
      (∀ k, k ≠ k₀ → ∃ k',
        turn (geoCornerPolygon h₁ S₁ q₁) k = turn (geoCornerPolygon h₂ S₂ q₂) k') ∧
      (∀ k', ∃ k, k ≠ k₀ ∧
        turn (geoCornerPolygon h₂ S₂ q₂) k' = turn (geoCornerPolygon h₁ S₁ q₁) k) := by
  have hnd₁ := geoComponentCornerList_nodup h₁ S₁ q₁
  refine ⟨?_, ?_⟩
  · unfold geoCornerCount
    have hperm : (((geoComponentCornerList h₁ S₁ q₁).erase a₀).map f).Perm
        (geoComponentCornerList h₂ S₂ q₂) := by
      rw [List.perm_ext_iff_of_nodup ((hnd₁.erase a₀).map_on ?_)
        (geoComponentCornerList_nodup h₂ S₂ q₂)]
      · intro b
        rw [List.mem_map]
        constructor
        · rintro ⟨a, ha, rfl⟩
          rw [hnd₁.mem_erase_iff] at ha
          exact (hf a ha.2 ha.1).1
        · intro hb
          obtain ⟨hgb, hne, hfgb⟩ := hg b hb
          exact ⟨g b, hnd₁.mem_erase_iff.mpr ⟨hne, hgb⟩, hfgb⟩
      · intro a ha a' ha' hfa
        rw [hnd₁.mem_erase_iff] at ha ha'
        rw [← (hf a ha.2 ha.1).2, ← (hf a' ha'.2 ha'.1).2, hfa]
    rw [← hperm.length_eq, List.length_map, List.length_erase_of_mem ha₀]
    have := List.length_pos_of_mem ha₀
    omega
  · obtain ⟨hown, hcor⟩ := (mem_geoComponentCornerList h₁ S₁ q₁ a₀).mp ha₀
    obtain ⟨k₀, hk₀, -⟩ := exists_turn_eq_geoCornerTurn h₁ S₁ hcor hown
    refine ⟨k₀, hk₀, ?_, ?_⟩
    · intro k hk
      have ha := geoCornerMark_mem_cornerList h₁ S₁ q₁ k
      have hne : geoCornerMark h₁ S₁ q₁ k ≠ a₀ := fun h =>
        hk (geoCornerMark_injective h₁ S₁ q₁ (h.trans hk₀.symm))
      obtain ⟨hfa, -⟩ := hf _ ha hne
      obtain ⟨hown', hcor'⟩ := (mem_geoComponentCornerList h₂ S₂ q₂ _).mp hfa
      obtain ⟨k', -, hk'⟩ := exists_turn_eq_geoCornerTurn h₂ S₂ hcor' hown'
      refine ⟨k', ?_⟩
      rw [hk', turn_geoCornerPolygon_eq_geoCornerTurn, hturn _ ha hne]
    · intro k'
      have hb := geoCornerMark_mem_cornerList h₂ S₂ q₂ k'
      obtain ⟨hgb, hne, hfgb⟩ := hg _ hb
      obtain ⟨hown', hcor'⟩ := (mem_geoComponentCornerList h₁ S₁ q₁ _).mp hgb
      obtain ⟨k, hk, hkt⟩ := exists_turn_eq_geoCornerTurn h₁ S₁ hcor' hown'
      refine ⟨k, ?_, ?_⟩
      · intro hkk₀
        apply hne
        rw [← hk, hkk₀, hk₀]
      · rw [hkt, turn_geoCornerPolygon_eq_geoCornerTurn, hturn _ hgb hne, hfgb]

end CornerCorrespondence

/-! ## 6. The flat configurations: `IsTrueCorner` under the side identification -/

section FlatTransport

attribute [local instance] Classical.propDecidable



end FlatTransport

/-! ## 7. The three selector fields of cor:flat-carriers (iii) -/

section FlatSelector

attribute [local instance] Classical.propDecidable

/-- Field `selector_def`: the three defining clauses of `cornerSelector` (sm-3:824-826) and
`geoCarrierSelector = cornerSelector ∘ geoCornerPolygon`. -/
theorem selector_def :
    (∀ {m : ℕ} [NeZero m] (Q : LabelledTuple m),
      ((∀ i, turn Q i = -1) → cornerSelector Q = 1) ∧
      ((∀ i, turn Q i = 1) → cornerSelector Q = (-1 : ℤ) ^ m) ∧
      (¬ (∀ i, turn Q i = -1) → ¬ (∀ i, turn Q i = 1) → cornerSelector Q = 0)) ∧
    (∀ {m : ℕ} [NeZero m] {P : LabelledTuple m} (hP : CrossingGeometry P)
      (S' : Finset (Crossing P)) (q : GeoComponent hP S'),
      geoCarrierSelector hP S' q = cornerSelector (geoCornerPolygon hP S' q)) := by
  refine ⟨?_, ?_⟩
  · intro m _ Q
    exact ⟨cornerSelector_of_all_right Q, cornerSelector_of_all_left Q, cornerSelector_of_mixed Q⟩
  · intro m _ P hP S' q
    rfl

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
  (S : Finset (Crossing g.center))

omit [NeZero n] in
/-- Side copies: a centre mark is a corner of the centre carrier of `a₀` iff its transport is a
corner of the side copy (owner-iff of `correspond_sides` + `isTrueCorner_markTransport`). -/
theorem markTransport_mem_geoComponentCornerList_iff (b : Bool)
    (howner : ∀ a a' : Mark g.center,
      geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a'))
    (a₀ a : Mark g.center) :
    markTransport (hs b) a ∈ geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a₀)) ↔
      a ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a₀) := by
  rw [mem_geoComponentCornerList, mem_geoComponentCornerList, ← howner a a₀,
    isTrueCorner_markTransport]

/-- Field `other_selectors_agree` ("All other corresponding carrier selectors agree"): for a carrier
not through `μ_j`, the side copy's selector is the deletion copy's. Hypotheses: the fields
`correspond_sides` (U2), `others_unchanged` (U2.5: the deletion copy's corner cycle is the centre
carrier's), `same_turn_signs` (U3.4), stated verbatim. Proof: the corner marks of the side copy and
of the deletion copy correspond bijectively through the centre (`delMark ∘ markTransport⁻¹` and
`markTransport ∘ fusionMark`), all away from `μ_j`, with equal turns; then
`geoCarrierSelector_eq_of_corner_bijection` ("retain all their corner signs and counts"). -/
theorem other_selectors_agree
    (correspond_sides : ∀ b : Bool,
      (∀ a : Mark g.center,
        geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
            (markTransport (hs b) a) =
          markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
      (∀ a a' : Mark g.center,
        geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
            geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a')))
    (others_unchanged : ∀ b : Mark (deleteVertex g.center j),
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
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)))
    (same_turn_signs : ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a → ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
        geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (delMark hn g j hz hb hc a)) :
    ∀ (b : Bool) (b' : Mark (deleteVertex g.center j)),
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b') ≠
        centralCarrierThroughJ hn g j hz hb hc S →
      geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S)
          (markTransport (hs b) (fusionMark hn g j hz hb hc b'))) =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b') := by
  intro b b' hne
  -- U2.5: the deletion copy's corner cycle, read at the centre, is the centre carrier's
  have hrot : ((geoComponentCornerList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b')).map
        (fusionMark hn g j hz hb hc)) ~r
      geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) :=
    Cycle.coe_eq_coe.mp (others_unchanged b' hne).2.1
  -- no corner of this centre carrier is `μ_j` (it is not the carrier through `μ_j`)
  have hmemC : ∀ a : Mark g.center,
      a ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) →
      a ≠ Sum.inl j := by
    intro a ha haj
    subst haj
    exact hne ((mem_geoComponentCornerList _ _ _ _).mp ha).1.symm
  -- a side corner mark, read at the centre, is a corner of the centre carrier
  have hside : ∀ m : Mark (g.sideTuple b t).val,
      m ∈ geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S)
          (markTransport (hs b) (fusionMark hn g j hz hb hc b'))) →
      (markTransport (hs b)).symm m ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) := by
    intro m hm
    have h := markTransport_mem_geoComponentCornerList_iff hn g j hz hb hc t hs S b
      (correspond_sides b).2 (fusionMark hn g j hz hb hc b') ((markTransport (hs b)).symm m)
    rw [Equiv.apply_symm_apply] at h
    exact h.mp hm
  apply geoCarrierSelector_eq_of_corner_bijection _ _ _ _ _ _
    (fun m => delMark hn g j hz hb hc ((markTransport (hs b)).symm m))
    (fun b'' => markTransport (hs b) (fusionMark hn g j hz hb hc b''))
  · intro m hm
    have hm' := hside m hm
    have hne' := hmemC _ hm'
    obtain ⟨b'', hb'', hfb''⟩ := List.mem_map.mp (hrot.mem_iff.mpr hm')
    refine ⟨?_, ?_⟩
    · rw [← hfb'', delMark_fusionMark]
      exact hb''
    · rw [fusionMark_delMark hn g j hz hb hc _ hne', Equiv.apply_symm_apply]
  · intro b'' hb''
    have hC : fusionMark hn g j hz hb hc b'' ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) :=
      hrot.mem_iff.mp (List.mem_map.mpr ⟨b'', hb'', rfl⟩)
    refine ⟨?_, ?_⟩
    · exact (markTransport_mem_geoComponentCornerList_iff hn g j hz hb hc t hs S b
        (correspond_sides b).2 _ _).mpr hC
    · rw [Equiv.symm_apply_apply, delMark_fusionMark]
  · intro m hm
    have hm' := hside m hm
    have hne' := hmemC _ hm'
    have hcor : IsTrueCorner S ((markTransport (hs b)).symm m) :=
      ((mem_geoComponentCornerList _ _ _ _).mp hm').2
    have h := same_turn_signs _ hne' hcor b
    rwa [Equiv.apply_symm_apply] at h

/-- Field `selector_identity` (eq. flatpr:selector-identity, `W_right − W_left = W_del` for the
carrier through `μ_j`). Hypotheses: the fields `correspond_sides` (U2),
`central_vs_deletion_through_mu_j` (U2.5: the centre carrier's corner cycle with `μ_j` erased is the
deletion copy's), `same_turn_signs` and `extra_corner` (U3.4), stated verbatim. Proof: on each side
the corners other than `μ_j` correspond bijectively, with equal turns, to the deletion copy's
corners (`corner_data_of_extra_corner`, so each side copy has `c + 1` corners, `c` the deletion
copy's count), the extra corner turning right (`-1`) on the right side and left (`+1`) on the left
side; then the exhaustive table `selector_table` (sm-3:893-905). -/
theorem selector_identity
    (correspond_sides : ∀ b : Bool,
      (∀ a : Mark g.center,
        geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
            (markTransport (hs b) a) =
          markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
      (∀ a a' : Mark g.center,
        geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
            geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a')))
    (central_vs_deletion_through_mu_j :
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
          (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) ∧
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
          s • edge (deleteVertex g.center j) (-1)))
    (same_turn_signs : ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a → ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
        geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (delMark hn g j hz hb hc a))
    (extra_corner : ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) =
        turn (g.sideTuple b t).val j ∧
      (IsRightSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = -1) ∧
      (IsLeftSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = 1)) :
    ∀ bR bL : Bool, IsRightSide g j bR t → IsLeftSide g j bL t →
      geoCarrierSelector (flatSideCG hn g bR t) (transportSupport (hs bR) S)
          (geoOwner (flatSideCG hn g bR t) (transportSupport (hs bR) S) (Sum.inl j)) -
        geoCarrierSelector (flatSideCG hn g bL t) (transportSupport (hs bL) S)
          (geoOwner (flatSideCG hn g bL t) (transportSupport (hs bL) S) (Sum.inl j)) =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) := by
  intro bR bL hR hL
  -- U2.5: the centre carrier's corner cycle with `μ_j` erased is the deletion copy's
  have hrot : (((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc)) ~r
      geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) :=
    Cycle.coe_eq_coe.mp central_vs_deletion_through_mu_j.2.2.1
  have hndC := geoComponentCornerList_nodup (flatCentreCG hn g j hz hb hc) S
    (centralCarrierThroughJ hn g j hz hb hc S)
  -- per side: corner count `c + 1`, and the turns away from the corner `μ_j` are the deletion's
  have side : ∀ b : Bool,
      geoCornerCount (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) =
        geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (deletionCopyThroughJ hn g j hz hb hc S) + 1 ∧
      ∃ k₀, geoCornerMark (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) k₀ = Sum.inl j ∧
        (∀ k, k ≠ k₀ → ∃ k',
          turn (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
            (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j))) k =
          turn (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
            (deletionCopyThroughJ hn g j hz hb hc S)) k') ∧
        (∀ k', ∃ k, k ≠ k₀ ∧
          turn (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
            (deletionCopyThroughJ hn g j hz hb hc S)) k' =
          turn (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
            (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j))) k) := by
    intro b
    -- a side corner mark, read at the centre, is a corner of the central carrier through `μ_j`
    have hside : ∀ m : Mark (g.sideTuple b t).val,
        m ∈ geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) →
        (markTransport (hs b)).symm m ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S) := by
      intro m hm
      have h := markTransport_mem_geoComponentCornerList_iff hn g j hz hb hc t hs S b
        (correspond_sides b).2 (Sum.inl j) ((markTransport (hs b)).symm m)
      rw [Equiv.apply_symm_apply] at h
      exact h.mp hm
    have hsideC : ∀ a : Mark g.center,
        a ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S) →
        markTransport (hs b) a ∈ geoComponentCornerList (flatSideCG hn g b t)
          (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) := by
      intro a ha
      exact (markTransport_mem_geoComponentCornerList_iff hn g j hz hb hc t hs S b
        (correspond_sides b).2 (Sum.inl j) a).mpr ha
    apply corner_data_of_extra_corner _ _ _ _ _ _
      (fun m => delMark hn g j hz hb hc ((markTransport (hs b)).symm m))
      (fun b'' => markTransport (hs b) (fusionMark hn g j hz hb hc b'')) (Sum.inl j)
    · exact (mem_geoComponentCornerList _ _ _ _).mpr ⟨rfl, isTrueCorner_vertex _ j⟩
    · intro m hm hmj
      have hm' := hside m hm
      have hne' : (markTransport (hs b)).symm m ≠ Sum.inl j := by
        intro h
        apply hmj
        rw [← Equiv.apply_symm_apply (markTransport (hs b)) m, h]
        rfl
      have hmem : (markTransport (hs b)).symm m ∈
          (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
            (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j) :=
        hndC.mem_erase_iff.mpr ⟨hne', hm'⟩
      refine ⟨hrot.mem_iff.mp (List.mem_map.mpr ⟨_, hmem, rfl⟩), ?_⟩
      rw [fusionMark_delMark hn g j hz hb hc _ hne', Equiv.apply_symm_apply]
    · intro b'' hb''
      obtain ⟨a, ha, hab⟩ := List.mem_map.mp (hrot.mem_iff.mpr hb'')
      rw [hndC.mem_erase_iff] at ha
      obtain ⟨haj, haC⟩ := ha
      have hfa : fusionMark hn g j hz hb hc b'' = a := by
        rw [← hab, fusionMark_delMark hn g j hz hb hc a haj]
      refine ⟨?_, ?_, ?_⟩
      · rw [hfa]
        exact hsideC a haC
      · rw [hfa]
        intro h
        exact haj ((markTransport (hs b)).injective (a₁ := a) (a₂ := Sum.inl j) h)
      · rw [hfa, Equiv.symm_apply_apply, hab]
    · intro m hm hmj
      have hm' := hside m hm
      have hne' : (markTransport (hs b)).symm m ≠ Sum.inl j := by
        intro h
        apply hmj
        rw [← Equiv.apply_symm_apply (markTransport (hs b)) m, h]
        rfl
      have hcor : IsTrueCorner S ((markTransport (hs b)).symm m) :=
        ((mem_geoComponentCornerList _ _ _ _).mp hm').2
      have h := same_turn_signs _ hne' hcor b
      rwa [Equiv.apply_symm_apply] at h
  obtain ⟨hcR, kR, hkR, hRD, hDR⟩ := side bR
  obtain ⟨hcL, kL, hkL, hLD, hDL⟩ := side bL
  rw [geoCarrierSelector_eq_cornerSelector, geoCarrierSelector_eq_cornerSelector,
    geoCarrierSelector_eq_cornerSelector]
  refine selector_table _ _ _ hcR hcL kR kL ?_ ?_ hRD hDR hLD hDL
  · rw [turn_geoCornerPolygon_eq_geoCornerTurn, hkR]
    exact (extra_corner bR).2.1 hR
  · rw [turn_geoCornerPolygon_eq_geoCornerTurn, hkL]
    exact (extra_corner bL).2.2 hL

/-! ### Interface check: the hypotheses are the fields of `FlatCarriersData`, verbatim -/

example (hD : FlatCarriersData hn g j hz hb hc t hs S) :=
  other_selectors_agree hn g j hz hb hc t hs S hD.correspond_sides hD.others_unchanged
    hD.same_turn_signs

example (hD : FlatCarriersData hn g j hz hb hc t hs S) :=
  selector_identity hn g j hz hb hc t hs S hD.correspond_sides
    hD.central_vs_deletion_through_mu_j hD.same_turn_signs hD.extra_corner

end FlatSelector

end
end SM

/-! ********************************************************************************
    ## ASSEMBLY — the two row theorems
    ******************************************************************************** -/

namespace SM

section Wiring

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- A side parameter below any positive bound (`g.SideParameter = Set.Ioo 0 g.radius`). -/
theorem exists_sideParameter_lt (g : WallGerm (n + 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : g.SideParameter, t.val < δ :=
  ⟨⟨min δ g.radius / 2, Set.mem_Ioo.mpr ⟨half_pos (lt_min hδ g.radius_pos),
      (half_lt_self (lt_min hδ g.radius_pos)).trans_le (min_le_right _ _)⟩⟩,
    (half_lt_self (lt_min hδ g.radius_pos)).trans_le (min_le_left _ _)⟩

variable (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- **U1 → U2.** The interface of U2 at a side parameter with side records (`SideRecordData`),
for any common supports `hs` and any independent `S`: U1's `identify_sides_marks`,
`identify_deletion_marks`, `independent_supports` feed `flat_carriers_U2`. -/
theorem u2Interface_of (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hs : CommonSupports g t) (S : Finset (Crossing g.center))
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) :
    U2Interface hn g j hz hb hc t hs S := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := flat_carriers_U2 hn g j hz hb hc t hs S
    (identify_sides_marks_of hn g j hz hb hc t hsd hs)
    (identify_deletion_marks_of hn g j hz hb hc)
    (fun b => ((independent_supports_of hn g j hz hb hc t hsd hs S).1 b).mp hS)
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- **U1, U2 → U3.** The interface of U3: `flat_carriers_U3` with U2's centre spec, U1's
decompositions on the sides and the deletion, and lem:flat-sides' side facts at `t`. -/
theorem u3Interface_of (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hsf : ∀ b : Bool, SideFacts g j b t)
    (hs : CommonSupports g t) (S : Finset (Crossing g.center))
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) :
    U3Interface hn g j hz hb hc t hs S := by
  have hspec := (u2Interface_of hn g j hz hb hc t hsd hs S hS).centre_carriers
  have hind := independent_supports_of hn g j hz hb hc t hsd hs S
  have h3 := flat_carriers_U3 hn g j hz hb hc t hs S hspec hsf
    (fun b => (hind.1 b).mp hS) (hind.2.mp hS)
  exact ⟨h3.nonzero_segments, h3.no_antiparallel, h3.turns_nonzero, h3.same_turn_signs,
    h3.centre_turn_signs, h3.extra_corner, h3.mu_j_between, h3.mu_j_fused_multiples⟩

/-- **U2, U3 → U5.** The interface of U5: `selector_identity` and `other_selectors_agree` from
U2's correspondences / cycle identities and U3's turn transport. -/
theorem u5Interface_of (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hsf : ∀ b : Bool, SideFacts g j b t)
    (hs : CommonSupports g t) (S : Finset (Crossing g.center))
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) :
    U5Interface hn g j hz hb hc t hs S := by
  have h2 := u2Interface_of hn g j hz hb hc t hsd hs S hS
  have h3 := u3Interface_of hn g j hz hb hc t hsd hsf hs S hS
  exact ⟨selector_identity hn g j hz hb hc t hs S h2.correspond_sides
      ⟨h2.central_vs_deletion_marks.1, h2.central_vs_deletion_marks.2.1,
        h2.central_vs_deletion_marks.2.2, h3.central_vs_deletion_geometry.1,
        h3.central_vs_deletion_geometry.2⟩
      h3.same_turn_signs h3.extra_corner,
    other_selectors_agree hn g j hz hb hc t hs S h2.correspond_sides h2.others_unchanged
      h3.same_turn_signs⟩

end Wiring

section RowTheorems

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- def:flat-carriers under the hypotheses of lem:flat-sides (`hn g hz hb hc hsc`, exactly those of
`flat_sides`): on a common radius `δ`, for every side parameter `t < δ` the common supports `hs`
exist and, for every independent set `S` of the centre's interlacement graph, the four carrier
families are defined as printed. -/
theorem flat_carriers_definition (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)
    (hsc : g.SignChanges (fun P => (turn P j : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ hs : CommonSupports g t, ∀ S : Finset (Crossing g.center),
        GeoIndependent (flatCentreCG hn g j hz hb hc) S →
        FlatCarriersDefinitionData hn g j hz hb hc t hs S := by
  obtain ⟨δF, hδF, -, hrec⟩ :=
    flat_side_records hn g j hz hb hc (flat_sides hn g hz hb hc hsc)
  exact flat_carriers_definition_of hn g j hz hb hc hsc
    ⟨δF, hδF, fun t ht hs S hS =>
      (u2Interface_of hn g j hz hb hc t (hrec t ht).2 hs S hS).centre_carriers⟩

/-- cor:flat-carriers under the hypotheses of lem:flat-sides (`hn g hz hb hc hsc`, exactly those of
`flat_sides`): on a common radius `δ`, for every side parameter `t < δ` the common supports `hs`
exist and, for every independent set `S` of the centre's interlacement graph, the four carrier
families of def:flat-carriers satisfy (i)–(iii) as printed. The closing sentences ("These
assertions concern geometric and combinatorial carrier data. They make no assignment of a
state-sum value at the flat centre.") are non-definitional and have no field. -/
theorem flat_carriers (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)
    (hsc : g.SignChanges (fun P => (turn P j : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ hs : CommonSupports g t, ∀ S : Finset (Crossing g.center),
        GeoIndependent (flatCentreCG hn g j hz hb hc) S →
        FlatCarriersData hn g j hz hb hc t hs S := by
  have hF := flat_sides hn g hz hb hc hsc
  obtain ⟨δF, hδF, -, hrec⟩ := flat_side_records hn g j hz hb hc hF
  obtain ⟨δS, hδS, -, hsf⟩ := flat_sides_side_facts hn g j hz hb hc hF
  -- the centre spec (U2) for every independent support, read off one side parameter `t₀`
  obtain ⟨t₀, ht₀⟩ := exists_sideParameter_lt g hδF
  have hspec : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S := fun S hS =>
    (u2Interface_of hn g j hz hb hc t₀ (hrec t₀ ht₀).2
      (flat_common_supports hn g j hz hb hc t₀ (hrec t₀ ht₀).2) S hS).centre_carriers
  -- U4's rotation radius, from U3's centre regularity for every independent support
  obtain ⟨δR, hδR, -, hR⟩ := same_rotation hn g j hz hb hc
    (fun S hS => flat_centre_edge_ne_zero hn g j hz hb hc S (hspec S hS))
    (fun S hS => flat_centre_not_antiparallel hn g j hz hb hc S (hspec S hS))
  refine flat_carriers_of hn g j hz hb hc hsc ?_ ?_ ?_ ?_
  · -- U2 on the radius of lem:flat-sides
    exact ⟨δF, hδF, fun t ht hs S hS => u2Interface_of hn g j hz hb hc t (hrec t ht).2 hs S hS⟩
  · -- U3 on the radius of the side facts
    refine ⟨min δF δS, lt_min hδF hδS, fun t ht hs S hS => ?_⟩
    exact u3Interface_of hn g j hz hb hc t (hrec t (lt_of_lt_of_le ht (min_le_left _ _))).2
      (hsf t (lt_of_lt_of_le ht (min_le_right _ _))) hs S hS
  · -- U4 on the rotation radius
    refine ⟨min δF (min δS δR), lt_min hδF (lt_min hδS hδR), fun t ht hs S hS => ?_⟩
    have htF : t.val < δF := lt_of_lt_of_le ht (min_le_left _ _)
    have htS : t.val < δS := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
    have htR : t.val < δR := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
    have hsd := (hrec t htF).2
    have h2 := u2Interface_of hn g j hz hb hc t hsd hs S hS
    have h3 := u3Interface_of hn g j hz hb hc t hsd (hsf t htS) hs S hS
    exact ⟨hR t htR hs S hS
      (fun b a => geoComponentCornerList_markTransport (flatCentreCG hn g j hz hb hc)
        (flatSideCG hn g b t) (hs b) (identify_sides_marks_of hn g j hz hb hc t hsd hs b) S a)
      h2.correspond_deletion.2.1 h2.central_vs_deletion_marks.1
      h2.central_vs_deletion_marks.2.2 (fun b hb' => (h2.others_unchanged b hb').2.1)
      h3.turns_nonzero.1 h3.nonzero_segments.2.2.2.1 h3.no_antiparallel.2.1⟩
  · -- U5 on the radius of the side facts
    refine ⟨min δF δS, lt_min hδF hδS, fun t ht hs S hS => ?_⟩
    exact u5Interface_of hn g j hz hb hc t (hrec t (lt_of_lt_of_le ht (min_le_left _ _))).2
      (hsf t (lt_of_lt_of_le ht (min_le_right _ _))) hs S hS

end RowTheorems

end SM
