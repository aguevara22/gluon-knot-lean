import SM.GeoCarrierOrder

/-! Ported 2026-09-14 from work/drafts/cvdom/U2a/GeoCarrierNoncrossing.lean (CV-DOM unit U2a: the noncrossing clause of lem:carriers on the geo carriers; tier 0; REPORT.md in the same directory). Library module, no row. Only this header added. -/

/-! # SM/GeoCarrierNoncrossing.lean — lem:carriers (iv) on the geo lane (CV-DOM unit U2a)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1–R5, §5 unit U2a). Draft home
work/drafts/cvdom/U2a/; intended home work/lean/SM/GeoCarrierNoncrossing.lean.

Port of work/lean/SM/CarrierNoncrossing.lean ("the assignment of all crossing visits is noncrossing",
sm-3-statesum.tex lem:carriers (iv), lines 88–91 and its proof 108–165) onto the accepted geometric carrier
layer `SM.GeoCarrier` (SM/FlatCarriersDefs.lean, def:flat-carriers): the marked traversal circle `Mark P`,
its positions `geoMarkPosition hP` (`geoMarkPosition hP (Sum.inr v) = geometricVisitPosition hP v`
definitionally), `ρ_S = geoSmoothingSuccessor hP S`, the carriers `GeoComponent hP S`, the owner of a mark
`geoOwner hP S` (incoming-visit convention, conv:selected-visits), independence `GeoIndependent hP S`.
The splitting induction is the source's: the invariant `GeoNoncrossingOwners hP T` (noncrossing ownership of
ALL marks) holds for `T = ∅`, is preserved by each insertion of a fresh selected pair (the owner-filtered
rotation supplied by `geoSmoothingSuccessor_insert_child_data`, SM/GeoCarrierCount.lean, and the
complementary-arc alternation lemma `geo_ncx_split_alternation_false`), and the inherited-order /
pending-pair invariants come from `geoIndependent_partial_invariants` (SM/GeoCarrierCount.lean).

Hypothesis-free helpers of the source (`ncx_cyclic_mod_add_iff`, `ncx_sorted_rotate_getElem_cyclic_iff`,
`ncx_mem_cons_of_mem_cons_filter`, `ncx_traversalBetween_ne`, `ncx_cyclic_four_iff`, `SM.Carrier`) are in
the import closure and are used as they are, not re-declared. `carriers_noncrossing_of_isDecomposition` is not
ported (`IsDecomposition` is `SM.Generic`-bound, ruling R2).

Transformer: work/drafts/cvdom/port_lane.py + work/drafts/cvdom/U2a/port_u2a.py; proofs verbatim modulo
`X hn hP → geoX hP`, `markPosition hn hP.1 → geoMarkPosition hP`, `visitPosition hn hP(.1) →
geometricVisitPosition hP`, `S ∈ independentSupports hn hP → GeoIndependent hP S`. Every declaration is tier 0
(`CrossingGeometry P`); no lemma needs `hn : 3 ≤ n` (the source used it only as the argument of
`markPosition` / `visitPosition`); `hn` appears only on the §5 target `geo_noncrossing`, whose shape
DECISION_FINAL.md §5 fixes (ruling R5; unused there).

U2a target (§5) in this file: `geo_noncrossing (hn) (hP) (hS)` — the exact shape of
`CarriersLemmaData.noncrossing` (SM/CarriersLemma.lean:113–124) on `geoOwner` / `geometricVisitPosition`. -/

namespace SM.GeoCarrier
open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-! ## 1. Cyclic order of three entries of the rotated sorted mark list -/

/-- The strict oriented cyclic order of three marks of any rotation of the complete sorted
mark list is the strict cyclic order of their positions in that rotation. -/
theorem geo_ncx_markList_rotate_between_iff {P : LabelledTuple n} (hP : CrossingGeometry P)
    (k i j l : ℕ) (hi : i < ((geoMarkList hP).rotate k).length)
    (hj : j < ((geoMarkList hP).rotate k).length)
    (hl : l < ((geoMarkList hP).rotate k).length) :
    traversalBetween (geoMarkPosition hP (((geoMarkList hP).rotate k)[i]))
        (geoMarkPosition hP (((geoMarkList hP).rotate k)[j]))
        (geoMarkPosition hP (((geoMarkList hP).rotate k)[l])) ↔
      ((i < j ∧ j < l) ∨ (j < l ∧ l < i) ∨ (l < i ∧ i < j)) := by
  let _ := geoMarkLinearOrder hP
  exact ncx_sorted_rotate_getElem_cyclic_iff (Finset.univ : Finset (Mark P)) k i j l hi hj hl

/-! ## 2. Positions of the two children of a split list -/

/-- In the rotation `a :: (A ++ b :: B)` of the marked circle, an entry of the closed-open arc
`a :: B` (the left child `(a, B₁..B_q)` of the split, before owner filtering) is at position
`0` or after position `A.length + 1` of `b`. -/
theorem geo_ncx_rotate_index_left_child {P : LabelledTuple n} (hP : CrossingGeometry P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = a :: (A ++ b :: B))
    (i : ℕ) (hi : i < ((geoMarkList hP).rotate k).length)
    (hx : ((geoMarkList hP).rotate k)[i] ∈ a :: B) : i = 0 ∨ A.length + 1 < i := by
  have hN : ((geoMarkList hP).rotate k).Nodup := List.nodup_rotate.mpr (geoMarkList_nodup hP)
  have h0 : 0 < ((geoMarkList hP).rotate k).length := lt_of_le_of_lt (Nat.zero_le i) hi
  have hb : A.length + 1 < ((geoMarkList hP).rotate k).length := by
    rw [hrot]
    simp only [List.length_cons, List.length_append]
    omega
  have hzero : ((geoMarkList hP).rotate k)[(0 : ℕ)]'h0 = a := by
    simp only [hrot, List.getElem_cons_zero]
  have hbe : ((geoMarkList hP).rotate k)[A.length + 1]'hb = b := by
    simp only [hrot, List.getElem_cons_succ, List.getElem_append_right (Nat.le_refl A.length),
      Nat.sub_self, List.getElem_cons_zero]
  rcases List.mem_cons.mp hx with he | hB
  · left
    exact hN.getElem_inj_iff.mp (he.trans hzero.symm)
  · right
    have hbet := (geoMarkList_rotate_right_iff hP k a b A B hrot _).mp hB
    rw [← hzero, ← hbe] at hbet
    have hcyc := (geo_ncx_markList_rotate_between_iff hP k (A.length + 1) i 0 hb hi h0).mp hbet
    omega

/-- An entry of the complementary closed-open arc `b :: A` (the right child `(b, A₁..A_p)`
before owner filtering) is at a position from `1` to `A.length + 1`. -/
theorem geo_ncx_rotate_index_right_child {P : LabelledTuple n} (hP : CrossingGeometry P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = a :: (A ++ b :: B))
    (i : ℕ) (hi : i < ((geoMarkList hP).rotate k).length)
    (hx : ((geoMarkList hP).rotate k)[i] ∈ b :: A) : 0 < i ∧ i ≤ A.length + 1 := by
  have hN : ((geoMarkList hP).rotate k).Nodup := List.nodup_rotate.mpr (geoMarkList_nodup hP)
  have h0 : 0 < ((geoMarkList hP).rotate k).length := lt_of_le_of_lt (Nat.zero_le i) hi
  have hb : A.length + 1 < ((geoMarkList hP).rotate k).length := by
    rw [hrot]
    simp only [List.length_cons, List.length_append]
    omega
  have hzero : ((geoMarkList hP).rotate k)[(0 : ℕ)]'h0 = a := by
    simp only [hrot, List.getElem_cons_zero]
  have hbe : ((geoMarkList hP).rotate k)[A.length + 1]'hb = b := by
    simp only [hrot, List.getElem_cons_succ, List.getElem_append_right (Nat.le_refl A.length),
      Nat.sub_self, List.getElem_cons_zero]
  rcases List.mem_cons.mp hx with he | hA
  · have hi' := hN.getElem_inj_iff.mp (he.trans hbe.symm)
    omega
  · have hbet := (geoMarkList_rotate_left_iff hP k a b A B hrot _).mp hA
    rw [← hzero, ← hbe] at hbet
    have hcyc := (geo_ncx_markList_rotate_between_iff hP k 0 i (A.length + 1) h0 hi hb).mp hbet
    omega

/-- **Two complementary arcs cannot alternate.** If `m₁, m₃` lie in the arc `a :: B` and
`m₂, m₄` in the complementary arc `b :: A` of a rotation `a :: (A ++ b :: B)` of the marked
circle, then `m₁, m₂, m₃, m₄` are not in that cyclic order. This is the source's "four disjoint
cyclic transitions between these four points would then each contain one of `a, b`". -/
theorem geo_ncx_split_alternation_false {P : LabelledTuple n} (hP : CrossingGeometry P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = a :: (A ++ b :: B))
    (m₁ m₂ m₃ m₄ : Mark P) (h1 : m₁ ∈ a :: B) (h3 : m₃ ∈ a :: B)
    (h2 : m₂ ∈ b :: A) (h4 : m₄ ∈ b :: A)
    (h123 : traversalBetween (geoMarkPosition hP m₁) (geoMarkPosition hP m₂)
      (geoMarkPosition hP m₃))
    (h341 : traversalBetween (geoMarkPosition hP m₃) (geoMarkPosition hP m₄)
      (geoMarkPosition hP m₁)) : False := by
  obtain ⟨i₁, hi₁, rfl⟩ :=
    List.mem_iff_getElem.mp (List.mem_rotate.mpr (mem_geoMarkList hP m₁) : m₁ ∈ (geoMarkList hP).rotate k)
  obtain ⟨i₂, hi₂, rfl⟩ :=
    List.mem_iff_getElem.mp (List.mem_rotate.mpr (mem_geoMarkList hP m₂) : m₂ ∈ (geoMarkList hP).rotate k)
  obtain ⟨i₃, hi₃, rfl⟩ :=
    List.mem_iff_getElem.mp (List.mem_rotate.mpr (mem_geoMarkList hP m₃) : m₃ ∈ (geoMarkList hP).rotate k)
  obtain ⟨i₄, hi₄, rfl⟩ :=
    List.mem_iff_getElem.mp (List.mem_rotate.mpr (mem_geoMarkList hP m₄) : m₄ ∈ (geoMarkList hP).rotate k)
  have c1 := geo_ncx_rotate_index_left_child hP k a b A B hrot i₁ hi₁ h1
  have c3 := geo_ncx_rotate_index_left_child hP k a b A B hrot i₃ hi₃ h3
  have c2 := geo_ncx_rotate_index_right_child hP k a b A B hrot i₂ hi₂ h2
  have c4 := geo_ncx_rotate_index_right_child hP k a b A B hrot i₄ hi₄ h4
  have d123 := (geo_ncx_markList_rotate_between_iff hP k i₁ i₂ i₃ hi₁ hi₂ hi₃).mp h123
  have d341 := (geo_ncx_markList_rotate_between_iff hP k i₃ i₄ i₁ hi₃ hi₄ hi₁).mp h341
  omega

-- [shared] `ncx_mem_cons_of_mem_cons_filter` is hypothesis-free and already in scope (SM.Carrier); not re-declared

/-! ## 3. The noncrossing invariant of the splitting induction -/

/-- The ownership of *all* marks (original vertices, unselected and selected visits) under the
processed support `T` is noncrossing: no four marks in strict cyclic order have
`m₁, m₃` on one component and `m₂, m₄` on a different one. -/
def GeoNoncrossingOwners {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) : Prop :=
  ∀ m₁ m₂ m₃ m₄ : Mark P,
    traversalBetween (geoMarkPosition hP m₁) (geoMarkPosition hP m₂)
      (geoMarkPosition hP m₃) →
    traversalBetween (geoMarkPosition hP m₃) (geoMarkPosition hP m₄)
      (geoMarkPosition hP m₁) →
    geoOwner hP T m₁ = geoOwner hP T m₃ → geoOwner hP T m₂ = geoOwner hP T m₄ →
    geoOwner hP T m₁ = geoOwner hP T m₂

/-- "For no selected pairs there is one carrier, so there is nothing to check." -/
theorem geoNoncrossingOwners_empty {P : LabelledTuple n} (hP : CrossingGeometry P) :
    GeoNoncrossingOwners hP ∅ := by
  intro m₁ m₂ m₃ m₄ _ _ _ _
  exact (geoComponent_empty_subsingleton hP).elim _ _

/-- **The splitting step.** Inserting a fresh selected crossing whose two visits currently share
an owner (inherited order assumed for the current support, as in `inheritsMarkOrder_insert`)
preserves the noncrossing invariant. If at most one of the two alternating blocks came from
splitting the old cycle `L`, the four marks violate the previous invariant with `L` for that
block; if both did, they alternate between the two complementary arcs cut out by the selected
pair, which `geo_ncx_split_alternation_false` excludes. No independence premise is used here. -/
theorem geoNoncrossingOwners_insert {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)))
    (hN : GeoNoncrossingOwners hP T) : GeoNoncrossingOwners hP (insert v.1 T) := by
  intro m₁ m₂ m₃ m₄ h123 h341 h13 h24
  by_contra h12
  have hcS : (geoSmoothingSuccessor hP T).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)) :=
    (geoOwner_eq_iff hP T _ _).mp hc
  -- splitting only refines: the old owners agree
  have h13' : geoOwner hP T m₁ = geoOwner hP T m₃ := geoOwner_insert_eq_imp hP T v hv hcS h13
  have h24' : geoOwner hP T m₂ = geoOwner hP T m₄ := geoOwner_insert_eq_imp hP T v hv hcS h24
  have h12' : geoOwner hP T m₁ = geoOwner hP T m₂ := hN m₁ m₂ m₃ m₄ h123 h341 h13' h24'
  -- the common old owner must be the split block
  have hq1 : geoOwner hP T m₁ = geoOwner hP T (Sum.inr v) := by
    by_contra hne
    exact h12 ((geoOwner_insert_iff_of_unaffected hP T v hv hc (geoOwner hP T m₁) hne m₁ rfl
      m₂).mpr h12'.symm).symm
  have hq2 : geoOwner hP T m₂ = geoOwner hP T (Sum.inr v) := h12'.symm.trans hq1
  have hq3 : geoOwner hP T m₃ = geoOwner hP T (Sum.inr v) := h13'.symm.trans hq1
  have hq4 : geoOwner hP T m₄ = geoOwner hP T (Sum.inr v) := h24'.symm.trans hq2
  obtain ⟨k, A, B, hrot, hNL, hNR, hd, hleft, hright, -, -⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI v hv hc
  -- the two children are different
  have hab : geoOwner hP (insert v.1 T) (Sum.inr v) ≠
      geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) := by
    intro he
    have hbL := (hleft (Sum.inr (visitTwin v))).mp he.symm
    exact hd hbL List.mem_cons_self
  -- every mark of the old block lies in one of the two children
  have hclass : ∀ m : Mark P, geoOwner hP T m = geoOwner hP T (Sum.inr v) →
      geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) (Sum.inr v) ∨
      geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) := by
    intro m hm
    have hmL : m ∈ (geoMarkList hP).rotate k := List.mem_rotate.mpr (mem_geoMarkList hP m)
    rw [hrot] at hmL
    rcases List.mem_cons.mp hmL with he | hmL
    · exact Or.inl ((hleft m).mpr (List.mem_cons.mpr (Or.inl he)))
    · rcases List.mem_append.mp hmL with hA | hB
      · exact Or.inr ((hright m).mpr
          (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hA, decide_eq_true hm⟩)))
      · rcases List.mem_cons.mp hB with he | hB
        · exact Or.inr ((hright m).mpr (List.mem_cons.mpr (Or.inl he)))
        · exact Or.inl ((hleft m).mpr
            (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hB, decide_eq_true hm⟩)))
  -- the rotation starting at the twin
  have hrot' : (geoMarkList hP).rotate (k + (Sum.inr v :: A).length) =
      Sum.inr (visitTwin v) :: (B ++ Sum.inr v :: A) := by
    rw [← List.rotate_rotate, hrot]
    change (((Sum.inr v :: A) ++ (Sum.inr (visitTwin v) :: B)).rotate
      (Sum.inr v :: A).length) = _
    rw [List.rotate_append_length_eq]
    rfl
  have hmemL : ∀ m : Mark P, geoOwner hP (insert v.1 T) m =
      geoOwner hP (insert v.1 T) (Sum.inr v) → m ∈ Sum.inr v :: B :=
    fun m hm => ncx_mem_cons_of_mem_cons_filter _ _ _ ((hleft m).mp hm)
  have hmemR : ∀ m : Mark P, geoOwner hP (insert v.1 T) m =
      geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) → m ∈ Sum.inr (visitTwin v) :: A :=
    fun m hm => ncx_mem_cons_of_mem_cons_filter _ _ _ ((hright m).mp hm)
  rcases hclass m₁ hq1 with h1a | h1b <;> rcases hclass m₂ hq2 with h2a | h2b
  · exact h12 (h1a.trans h2a.symm)
  · -- m₁, m₃ in the child of v; m₂, m₄ in the child of the twin
    have h3a := h13.symm.trans h1a
    have h4b := h24.symm.trans h2b
    exact geo_ncx_split_alternation_false hP k _ _ A B hrot m₁ m₂ m₃ m₄
      (hmemL m₁ h1a) (hmemL m₃ h3a) (hmemR m₂ h2b) (hmemR m₄ h4b) h123 h341
  · -- m₁, m₃ in the child of the twin; m₂, m₄ in the child of v
    have h3b := h13.symm.trans h1b
    have h4a := h24.symm.trans h2a
    exact geo_ncx_split_alternation_false hP _ _ _ B A hrot' m₁ m₂ m₃ m₄
      (hmemR m₁ h1b) (hmemR m₃ h3b) (hmemL m₂ h2a) (hmemL m₄ h4a) h123 h341
  · exact h12 (h1b.trans h2b.symm)

/-- Processing any subset of an independent support keeps the ownership of all marks
noncrossing (induction as in `geoIndependent_partial_invariants`, whose invariants supply the
inherited order and the co-location of each unprocessed selected pair). -/
theorem geoIndependent_noncrossingOwners_partial {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (T : Finset (Crossing P)) (hTS : T ⊆ S) : GeoNoncrossingOwners hP T := by
  revert hTS
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact geoNoncrossingOwners_empty hP
  | @insert c T hc ih =>
    intro hTS
    have hcS : c ∈ S := hTS (Finset.mem_insert_self c T)
    have hTS' : T ⊆ S := fun z hz => hTS (Finset.mem_insert_of_mem hz)
    obtain ⟨hI, hPending⟩ := geoIndependent_partial_invariants hP hS T hTS'
    obtain ⟨i, _, _⟩ := crossing_visits_exist c
    let v : Visit P := ⟨c, i⟩
    have hvS : v.1 ∈ S := hcS
    have hv : v.1 ∉ T := hc
    have hsame := hPending v hvS hv
    exact geoNoncrossingOwners_insert hP T hI v hv hsame (ih hTS')

/-- The ownership of all marks under an independent support is noncrossing. -/
theorem geoIndependent_noncrossingOwners {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    GeoNoncrossingOwners hP S :=
  geoIndependent_noncrossingOwners_partial hP hS S (Finset.Subset.refl S)

/-! ## 4a. Cyclic order of four traversal points -/

-- [shared] `ncx_traversalBetween_ne` is hypothesis-free and already in scope (SM.Carrier); not re-declared

-- [shared] `ncx_cyclic_four_iff` is hypothesis-free and already in scope (SM.Carrier); not re-declared

omit [NeZero n] in
/-- Four visits in strict cyclic order on the traversal circle are pairwise distinct. -/
theorem geo_ncx_cyclic_visits_distinct {P : LabelledTuple n} (hP : CrossingGeometry P)
    (u₁ u₂ u₃ u₄ : Visit P)
    (h123 : traversalBetween (geometricVisitPosition hP u₁) (geometricVisitPosition hP u₂)
      (geometricVisitPosition hP u₃))
    (h341 : traversalBetween (geometricVisitPosition hP u₃) (geometricVisitPosition hP u₄)
      (geometricVisitPosition hP u₁)) :
    u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₃ ≠ u₄ := by
  obtain ⟨h234, _⟩ := traversalAlternating_rotate h123 h341
  obtain ⟨n12, n23, n13⟩ := ncx_traversalBetween_ne h123
  obtain ⟨n34, n41, n31⟩ := ncx_traversalBetween_ne h341
  obtain ⟨_, _, n24⟩ := ncx_traversalBetween_ne h234
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · exact n12 rfl
  · exact n13 rfl
  · exact n41 rfl
  · exact n23 rfl
  · exact n24 rfl
  · exact n34 rfl

/-! ## 4b. lem:carriers (iv) -/

/-- **lem:carriers (iv), for all marks.** For an independent support `S`, no four marks
`m₁, m₂, m₃, m₄` in that cyclic order on the marked traversal circle have `m₁, m₃` on one
carrier and `m₂, m₄` on a different carrier. -/
theorem geo_carriers_noncrossing_marks {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (m₁ m₂ m₃ m₄ : Mark P)
    (h123 : traversalBetween (geoMarkPosition hP m₁) (geoMarkPosition hP m₂)
      (geoMarkPosition hP m₃))
    (h341 : traversalBetween (geoMarkPosition hP m₃) (geoMarkPosition hP m₄)
      (geoMarkPosition hP m₁)) :
    ¬ (geoOwner hP S m₁ = geoOwner hP S m₃ ∧ geoOwner hP S m₂ = geoOwner hP S m₄ ∧
        geoOwner hP S m₁ ≠ geoOwner hP S m₂) := by
  rintro ⟨h13, h24, h12⟩
  exact h12 (geoIndependent_noncrossingOwners hP hS m₁ m₂ m₃ m₄ h123 h341 h13 h24)

/-- **lem:carriers (iv).** Let `S ∈ Ind(G_P)`. The assignment of all crossing visits to
carriers under the incoming-visit convention (`geoOwner hP S (Sum.inr u)`) is noncrossing:
for visits `u₁, u₂, u₃, u₄` in that cyclic order on the traversal circle, it is not the case
that `u₁, u₃` lie on one carrier and `u₂, u₄` on a different carrier. This includes selected
visits. -/
theorem geo_carriers_noncrossing_visits {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (u₁ u₂ u₃ u₄ : Visit P)
    (h123 : traversalBetween (geometricVisitPosition hP u₁) (geometricVisitPosition hP u₂)
      (geometricVisitPosition hP u₃))
    (h341 : traversalBetween (geometricVisitPosition hP u₃) (geometricVisitPosition hP u₄)
      (geometricVisitPosition hP u₁)) :
    ¬ (geoOwner hP S (Sum.inr u₁) = geoOwner hP S (Sum.inr u₃) ∧
        geoOwner hP S (Sum.inr u₂) = geoOwner hP S (Sum.inr u₄) ∧
        geoOwner hP S (Sum.inr u₁) ≠ geoOwner hP S (Sum.inr u₂)) :=
  geo_carriers_noncrossing_marks hP hS (Sum.inr u₁) (Sum.inr u₂) (Sum.inr u₃) (Sum.inr u₄)
    h123 h341

/-- **lem:carriers (iv), as printed.** "There are no four distinct visits `u₁, u₂, u₃, u₄` in
that cyclic order with `u₁, u₃` on one carrier and `u₂, u₄` on a different carrier." -/
theorem geo_carriers_noncrossing {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    ¬ ∃ u₁ u₂ u₃ u₄ : Visit P,
      (u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₃ ≠ u₄) ∧
      traversalBetween (geometricVisitPosition hP u₁) (geometricVisitPosition hP u₂)
        (geometricVisitPosition hP u₃) ∧
      traversalBetween (geometricVisitPosition hP u₃) (geometricVisitPosition hP u₄)
        (geometricVisitPosition hP u₁) ∧
      geoOwner hP S (Sum.inr u₁) = geoOwner hP S (Sum.inr u₃) ∧
      geoOwner hP S (Sum.inr u₂) = geoOwner hP S (Sum.inr u₄) ∧
      geoOwner hP S (Sum.inr u₁) ≠ geoOwner hP S (Sum.inr u₂) := by
  rintro ⟨u₁, u₂, u₃, u₄, -, h123, h341, h13, h24, h12⟩
  exact geo_carriers_noncrossing_visits hP hS u₁ u₂ u₃ u₄ h123 h341 ⟨h13, h24, h12⟩

/-- lem:carriers (iv) in the positive form: if `u₁, u₃` share a carrier and `u₂, u₄` share a
carrier, then all four share it. -/
theorem geo_carriers_noncrossing_owner_eq {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (u₁ u₂ u₃ u₄ : Visit P)
    (h123 : traversalBetween (geometricVisitPosition hP u₁) (geometricVisitPosition hP u₂)
      (geometricVisitPosition hP u₃))
    (h341 : traversalBetween (geometricVisitPosition hP u₃) (geometricVisitPosition hP u₄)
      (geometricVisitPosition hP u₁))
    (h13 : geoOwner hP S (Sum.inr u₁) = geoOwner hP S (Sum.inr u₃))
    (h24 : geoOwner hP S (Sum.inr u₂) = geoOwner hP S (Sum.inr u₄)) :
    geoOwner hP S (Sum.inr u₁) = geoOwner hP S (Sum.inr u₂) :=
  geoIndependent_noncrossingOwners hP hS (Sum.inr u₁) (Sum.inr u₂) (Sum.inr u₃) (Sum.inr u₄)
    h123 h341 h13 h24

/-- lem:carriers (iv) via the sorted mark list rotated to start anywhere (e.g. at `u₁`): for
positions `i₁ < i₂ < i₃ < i₄` in `(geoMarkList hP).rotate k`, if the marks at `i₁, i₃` share a
carrier and those at `i₂, i₄` share a carrier, then all four share it. -/
theorem geo_carriers_noncrossing_rotate {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (k i₁ i₂ i₃ i₄ : ℕ) (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄)
    (hi₄ : i₄ < ((geoMarkList hP).rotate k).length)
    (h13 : geoOwner hP S (((geoMarkList hP).rotate k)[i₁]'(by omega)) =
      geoOwner hP S (((geoMarkList hP).rotate k)[i₃]'(by omega)))
    (h24 : geoOwner hP S (((geoMarkList hP).rotate k)[i₂]'(by omega)) =
      geoOwner hP S (((geoMarkList hP).rotate k)[i₄]'hi₄)) :
    geoOwner hP S (((geoMarkList hP).rotate k)[i₁]'(by omega)) =
      geoOwner hP S (((geoMarkList hP).rotate k)[i₂]'(by omega)) := by
  have hi₁ : i₁ < ((geoMarkList hP).rotate k).length := by omega
  have hi₂ : i₂ < ((geoMarkList hP).rotate k).length := by omega
  have hi₃ : i₃ < ((geoMarkList hP).rotate k).length := by omega
  have h123 := (geo_ncx_markList_rotate_between_iff hP k i₁ i₂ i₃ hi₁ hi₂ hi₃).mpr
    (Or.inl ⟨h12, h23⟩)
  have h341 := (geo_ncx_markList_rotate_between_iff hP k i₃ i₄ i₁ hi₃ hi₄ hi₁).mpr
    (Or.inr (Or.inr ⟨by omega, h34⟩))
  exact geoIndependent_noncrossingOwners hP hS _ _ _ _ h123 h341 h13 h24

-- [not ported] `carriers_noncrossing_of_isDecomposition`: `IsDecomposition` is `SM.Generic`-bound (ruling R2)

/-! ## 5. The U2a target (DECISION_FINAL.md §5) -/

set_option linter.unusedVariables false in
/-- **lem:carriers (iv)** on the geo lane — the exact shape of `CarriersLemmaData.noncrossing`
(SM/CarriersLemma.lean) with `owner hn hP S ↦ geoOwner hP S`, `visitPosition hn hP.1 ↦ geometricVisitPosition hP`:
"there are no four distinct visits `u₁, u₂, u₃, u₄` in that cyclic order with `u₁, u₃` on one carrier and
`u₂, u₄` on a different carrier", selected visits included. `hn` is unused (§5 shape; ruling R5). -/
theorem geo_noncrossing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    ¬ ∃ u₁ u₂ u₃ u₄ : Visit P,
    (u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₃ ≠ u₄) ∧
    traversalBetween (geometricVisitPosition hP u₁) (geometricVisitPosition hP u₂)
    (geometricVisitPosition hP u₃) ∧
    traversalBetween (geometricVisitPosition hP u₃) (geometricVisitPosition hP u₄)
    (geometricVisitPosition hP u₁) ∧
    geoOwner hP S (Sum.inr u₁) = geoOwner hP S (Sum.inr u₃) ∧
    geoOwner hP S (Sum.inr u₂) = geoOwner hP S (Sum.inr u₄) ∧
    geoOwner hP S (Sum.inr u₁) ≠ geoOwner hP S (Sum.inr u₂) :=
  geo_carriers_noncrossing hP hS

end
end SM.GeoCarrier
