import SM.CarrierCrossings
import SM.CarrierNeighborSeparation
import SM.SmoothingDefinition

/-! Towards lem:carriers (iv) (sm-3-statesum.tex:54): the assignment of all crossing visits is noncrossing. Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-carriers-lemma / prove:carriers-iv), checked with `lake env lean` (placeholder-free, standard axioms) and
ported verbatim from work/drafts/CarriersNoncrossing.lean (only this header added and #print lines removed). -/

/-! # lem:carriers (iv): the assignment of all crossing visits is noncrossing

Source: reference/SM/sm-3-statesum.tex, lem:carriers (lines 54-95), clause (iv) (lines 88-91):
"The assignment of *all* crossing visits is noncrossing. There are no four distinct visits
`u₁, u₂, u₃, u₄` in that cyclic order with `u₁, u₃` on one carrier and `u₂, u₄` on a different
carrier. This includes selected visits under the stated convention." Proof: paragraphs
"Splitting and induced order" (lines 108-135), "Noncrossing away from selected endpoints"
(lines 136-153) and "Including every selected visit" (lines 154-165).

Encoding (the finite successor model of the source proof, lines 97-116, i.e. the Carrier lane):
* the traversal circle marked at every original vertex and every crossing visit is `Mark P`;
  the traversal point of a mark is `markPosition hn hP.1 m` (for a visit `v`,
  `markPosition hn hP.1 (Sum.inr v) = visitPosition hn hP.1 v` definitionally);
* "`u₁, u₂, u₃, u₄` in that cyclic order" on the traversal circle is the strict oriented cyclic
  order `traversalBetween p₁ p₂ p₃ ∧ traversalBetween p₃ p₄ p₁` of their positions (the same
  alternation pattern that defines `Interlaces`); `ncx_cyclic_four_iff` shows it is equivalent to
  the four conditions "`u₂` strictly between `u₁,u₃`, `u₃` strictly between `u₂,u₄`, `u₄` strictly
  between `u₃,u₁`, `u₁` strictly between `u₄,u₂`", and `ncx_cyclic_visits_distinct` derives the
  distinctness of the four visits from it; `carriers_noncrossing_rotate` is the equivalent
  formulation by increasing positions in the sorted `markList` rotated to start at any mark;
* `ρ = markSuccessor hn hP`, `ρ_S = smoothingSuccessor hn hP S`, the carriers are its cycles
  `Component hn hP S`, and the carrier a visit `v` is assigned to under the incoming-visit
  convention (conv:selected-visits, `SM.selected_visits_convention`) is `owner hn hP S (Sum.inr v)`;
  "`u₁, u₃` on one carrier and `u₂, u₄` on a different carrier" is
  `owner u₁ = owner u₃ ∧ owner u₂ = owner u₄ ∧ owner u₁ ≠ owner u₂`;
* `S ∈ Ind(G_P)` is `S ∈ independentSupports hn hP` (`= IsDecomposition hn hP S` by definition).

Proof route (as in the source): induction on the selected pairs processed, `T ⊆ S`, with the
invariant `NoncrossingOwners hn hP T` (noncrossing of the ownership of *all* marks, selected
visits included, since in the finite model they are nodes of the split lists). For the empty
support there is one carrier. At a split of the cycle `(a, A₁..A_p, b, B₁..B_q)` (the
owner-filtered rotation `Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)` of the marked circle
supplied by `smoothingSuccessor_insert_child_data`) into `(a, B…)` and `(b, A…)`: if at most one
of the two blocks came from the split, the four marks already violate the previous invariant
(`owner_insert_eq_imp`, `owner_insert_iff_of_unaffected`); if both did, the marks `u₁, u₃` lie in
the arc `a :: B` and `u₂, u₄` in the complementary arc `b :: A`, which is impossible for four
points in cyclic order (`ncx_split_alternation_false`, proved by passing to positions in the
rotated sorted list and `omega`). The general independent `S` follows as in
`independent_partial_invariants`. -/

namespace SM.Carrier

/-! ## Cyclic order of three entries of a rotated sorted list

These two generic lemmas are stated before the classical local instance below, so that the
`DecidableRel` instance of `s.sort` agrees syntactically with Mathlib's `Finset.sortedLT_sort`. -/

/-- Translating three indices around a finite circle preserves their strict cyclic order. -/
theorem ncx_cyclic_mod_add_iff (N k i j l : ℕ) (hi : i < N) (hj : j < N) (hl : l < N) :
    (((i + k) % N < (j + k) % N ∧ (j + k) % N < (l + k) % N) ∨
      ((j + k) % N < (l + k) % N ∧ (l + k) % N < (i + k) % N) ∨
      ((l + k) % N < (i + k) % N ∧ (i + k) % N < (j + k) % N)) ↔
      ((i < j ∧ j < l) ∨ (j < l ∧ l < i) ∨ (l < i ∧ i < j)) := by
  have hp : k % N < N := Nat.mod_lt k (Nat.zero_lt_of_lt hi)
  have hm (z : ℕ) (hz : z < N) : (z + k) % N = (z + k % N) % N := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hz]
  rw [hm i hi, hm j hj, hm l hl, mod_add_one_wrap N (k % N) i hp hi,
    mod_add_one_wrap N (k % N) j hp hj, mod_add_one_wrap N (k % N) l hp hl]
  split_ifs <;> omega

/-- In a rotated finset sort, the strict cyclic order of three entries is the strict cyclic
order of their indices. -/
theorem ncx_sorted_rotate_getElem_cyclic_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (k i j l : ℕ)
    (hi : i < (s.sort.rotate k).length) (hj : j < (s.sort.rotate k).length)
    (hl : l < (s.sort.rotate k).length) :
    (((s.sort.rotate k)[i] < (s.sort.rotate k)[j] ∧
        (s.sort.rotate k)[j] < (s.sort.rotate k)[l]) ∨
      ((s.sort.rotate k)[j] < (s.sort.rotate k)[l] ∧
        (s.sort.rotate k)[l] < (s.sort.rotate k)[i]) ∨
      ((s.sort.rotate k)[l] < (s.sort.rotate k)[i] ∧
        (s.sort.rotate k)[i] < (s.sort.rotate k)[j])) ↔
      ((i < j ∧ j < l) ∨ (j < l ∧ l < i) ∨ (l < i ∧ i < j)) := by
  have hi' : i < s.sort.length := by simpa only [List.length_rotate] using hi
  have hj' : j < s.sort.length := by simpa only [List.length_rotate] using hj
  have hl' : l < s.sort.length := by simpa only [List.length_rotate] using hl
  simp only [List.getElem_rotate, s.sortedLT_sort.getElem_lt_getElem_iff]
  exact ncx_cyclic_mod_add_iff s.sort.length k i j l hi' hj' hl'

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The strict oriented cyclic order of three marks of any rotation of the complete sorted
mark list is the strict cyclic order of their positions in that rotation. -/
theorem ncx_markList_rotate_between_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (k i j l : ℕ) (hi : i < ((markList hn hP).rotate k).length)
    (hj : j < ((markList hn hP).rotate k).length)
    (hl : l < ((markList hn hP).rotate k).length) :
    traversalBetween (markPosition hn hP.1 (((markList hn hP).rotate k)[i]))
        (markPosition hn hP.1 (((markList hn hP).rotate k)[j]))
        (markPosition hn hP.1 (((markList hn hP).rotate k)[l])) ↔
      ((i < j ∧ j < l) ∨ (j < l ∧ l < i) ∨ (l < i ∧ i < j)) := by
  let _ := markLinearOrder hn hP
  exact ncx_sorted_rotate_getElem_cyclic_iff (Finset.univ : Finset (Mark P)) k i j l hi hj hl

/-! ## Positions of the two children of a split list -/

/-- In the rotation `a :: (A ++ b :: B)` of the marked circle, an entry of the closed-open arc
`a :: B` (the left child `(a, B₁..B_q)` of the split, before owner filtering) is at position
`0` or after position `A.length + 1` of `b`. -/
theorem ncx_rotate_index_left_child (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B))
    (i : ℕ) (hi : i < ((markList hn hP).rotate k).length)
    (hx : ((markList hn hP).rotate k)[i] ∈ a :: B) : i = 0 ∨ A.length + 1 < i := by
  have hN : ((markList hn hP).rotate k).Nodup := List.nodup_rotate.mpr (markList_nodup hn hP)
  have h0 : 0 < ((markList hn hP).rotate k).length := lt_of_le_of_lt (Nat.zero_le i) hi
  have hb : A.length + 1 < ((markList hn hP).rotate k).length := by
    rw [hrot]
    simp only [List.length_cons, List.length_append]
    omega
  have hzero : ((markList hn hP).rotate k)[(0 : ℕ)]'h0 = a := by
    simp only [hrot, List.getElem_cons_zero]
  have hbe : ((markList hn hP).rotate k)[A.length + 1]'hb = b := by
    simp only [hrot, List.getElem_cons_succ, List.getElem_append_right (Nat.le_refl A.length),
      Nat.sub_self, List.getElem_cons_zero]
  rcases List.mem_cons.mp hx with he | hB
  · left
    exact hN.getElem_inj_iff.mp (he.trans hzero.symm)
  · right
    have hbet := (markList_rotate_right_iff hn hP k a b A B hrot _).mp hB
    rw [← hzero, ← hbe] at hbet
    have hcyc := (ncx_markList_rotate_between_iff hn hP k (A.length + 1) i 0 hb hi h0).mp hbet
    omega

/-- An entry of the complementary closed-open arc `b :: A` (the right child `(b, A₁..A_p)`
before owner filtering) is at a position from `1` to `A.length + 1`. -/
theorem ncx_rotate_index_right_child (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B))
    (i : ℕ) (hi : i < ((markList hn hP).rotate k).length)
    (hx : ((markList hn hP).rotate k)[i] ∈ b :: A) : 0 < i ∧ i ≤ A.length + 1 := by
  have hN : ((markList hn hP).rotate k).Nodup := List.nodup_rotate.mpr (markList_nodup hn hP)
  have h0 : 0 < ((markList hn hP).rotate k).length := lt_of_le_of_lt (Nat.zero_le i) hi
  have hb : A.length + 1 < ((markList hn hP).rotate k).length := by
    rw [hrot]
    simp only [List.length_cons, List.length_append]
    omega
  have hzero : ((markList hn hP).rotate k)[(0 : ℕ)]'h0 = a := by
    simp only [hrot, List.getElem_cons_zero]
  have hbe : ((markList hn hP).rotate k)[A.length + 1]'hb = b := by
    simp only [hrot, List.getElem_cons_succ, List.getElem_append_right (Nat.le_refl A.length),
      Nat.sub_self, List.getElem_cons_zero]
  rcases List.mem_cons.mp hx with he | hA
  · have hi' := hN.getElem_inj_iff.mp (he.trans hbe.symm)
    omega
  · have hbet := (markList_rotate_left_iff hn hP k a b A B hrot _).mp hA
    rw [← hzero, ← hbe] at hbet
    have hcyc := (ncx_markList_rotate_between_iff hn hP k 0 i (A.length + 1) h0 hi hb).mp hbet
    omega

/-- **Two complementary arcs cannot alternate.** If `m₁, m₃` lie in the arc `a :: B` and
`m₂, m₄` in the complementary arc `b :: A` of a rotation `a :: (A ++ b :: B)` of the marked
circle, then `m₁, m₂, m₃, m₄` are not in that cyclic order. This is the source's "four disjoint
cyclic transitions between these four points would then each contain one of `a, b`". -/
theorem ncx_split_alternation_false (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B))
    (m₁ m₂ m₃ m₄ : Mark P) (h1 : m₁ ∈ a :: B) (h3 : m₃ ∈ a :: B)
    (h2 : m₂ ∈ b :: A) (h4 : m₄ ∈ b :: A)
    (h123 : traversalBetween (markPosition hn hP.1 m₁) (markPosition hn hP.1 m₂)
      (markPosition hn hP.1 m₃))
    (h341 : traversalBetween (markPosition hn hP.1 m₃) (markPosition hn hP.1 m₄)
      (markPosition hn hP.1 m₁)) : False := by
  obtain ⟨i₁, hi₁, rfl⟩ :=
    List.mem_iff_getElem.mp (List.mem_rotate.mpr (mem_markList hn hP m₁) : m₁ ∈ (markList hn hP).rotate k)
  obtain ⟨i₂, hi₂, rfl⟩ :=
    List.mem_iff_getElem.mp (List.mem_rotate.mpr (mem_markList hn hP m₂) : m₂ ∈ (markList hn hP).rotate k)
  obtain ⟨i₃, hi₃, rfl⟩ :=
    List.mem_iff_getElem.mp (List.mem_rotate.mpr (mem_markList hn hP m₃) : m₃ ∈ (markList hn hP).rotate k)
  obtain ⟨i₄, hi₄, rfl⟩ :=
    List.mem_iff_getElem.mp (List.mem_rotate.mpr (mem_markList hn hP m₄) : m₄ ∈ (markList hn hP).rotate k)
  have c1 := ncx_rotate_index_left_child hn hP k a b A B hrot i₁ hi₁ h1
  have c3 := ncx_rotate_index_left_child hn hP k a b A B hrot i₃ hi₃ h3
  have c2 := ncx_rotate_index_right_child hn hP k a b A B hrot i₂ hi₂ h2
  have c4 := ncx_rotate_index_right_child hn hP k a b A B hrot i₄ hi₄ h4
  have d123 := (ncx_markList_rotate_between_iff hn hP k i₁ i₂ i₃ hi₁ hi₂ hi₃).mp h123
  have d341 := (ncx_markList_rotate_between_iff hn hP k i₃ i₄ i₁ hi₃ hi₄ hi₁).mp h341
  omega

/-- Membership in an owner-filtered child list gives membership in the unfiltered arc. -/
theorem ncx_mem_cons_of_mem_cons_filter {α : Type*} (a : α) (L : List α) (p : α → Bool)
    {m : α} (hm : m ∈ a :: L.filter p) : m ∈ a :: L := by
  rcases List.mem_cons.mp hm with rfl | hm
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem a (List.mem_of_mem_filter hm)

/-! ## The noncrossing invariant of the splitting induction -/

/-- The ownership of *all* marks (original vertices, unselected and selected visits) under the
processed support `T` is noncrossing: no four marks in strict cyclic order have
`m₁, m₃` on one component and `m₂, m₄` on a different one. -/
def NoncrossingOwners (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) : Prop :=
  ∀ m₁ m₂ m₃ m₄ : Mark P,
    traversalBetween (markPosition hn hP.1 m₁) (markPosition hn hP.1 m₂)
      (markPosition hn hP.1 m₃) →
    traversalBetween (markPosition hn hP.1 m₃) (markPosition hn hP.1 m₄)
      (markPosition hn hP.1 m₁) →
    owner hn hP T m₁ = owner hn hP T m₃ → owner hn hP T m₂ = owner hn hP T m₄ →
    owner hn hP T m₁ = owner hn hP T m₂

/-- "For no selected pairs there is one carrier, so there is nothing to check." -/
theorem noncrossingOwners_empty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    NoncrossingOwners hn hP ∅ := by
  intro m₁ m₂ m₃ m₄ _ _ _ _
  exact (component_empty_subsingleton hn hP).elim _ _

/-- **The splitting step.** Inserting a fresh selected crossing whose two visits currently share
an owner (inherited order assumed for the current support, as in `inheritsMarkOrder_insert`)
preserves the noncrossing invariant. If at most one of the two alternating blocks came from
splitting the old cycle `L`, the four marks violate the previous invariant with `L` for that
block; if both did, they alternate between the two complementary arcs cut out by the selected
pair, which `ncx_split_alternation_false` excludes. No independence premise is used here. -/
theorem noncrossingOwners_insert (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (hN : NoncrossingOwners hn hP T) : NoncrossingOwners hn hP (insert v.1 T) := by
  intro m₁ m₂ m₃ m₄ h123 h341 h13 h24
  by_contra h12
  have hcS : (smoothingSuccessor hn hP T).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)) :=
    (owner_eq_iff hn hP T _ _).mp hc
  -- splitting only refines: the old owners agree
  have h13' : owner hn hP T m₁ = owner hn hP T m₃ := owner_insert_eq_imp hn hP T v hv hcS h13
  have h24' : owner hn hP T m₂ = owner hn hP T m₄ := owner_insert_eq_imp hn hP T v hv hcS h24
  have h12' : owner hn hP T m₁ = owner hn hP T m₂ := hN m₁ m₂ m₃ m₄ h123 h341 h13' h24'
  -- the common old owner must be the split block
  have hq1 : owner hn hP T m₁ = owner hn hP T (Sum.inr v) := by
    by_contra hne
    exact h12 ((owner_insert_iff_of_unaffected hn hP T v hv hc (owner hn hP T m₁) hne m₁ rfl
      m₂).mpr h12'.symm).symm
  have hq2 : owner hn hP T m₂ = owner hn hP T (Sum.inr v) := h12'.symm.trans hq1
  have hq3 : owner hn hP T m₃ = owner hn hP T (Sum.inr v) := h13'.symm.trans hq1
  have hq4 : owner hn hP T m₄ = owner hn hP T (Sum.inr v) := h24'.symm.trans hq2
  obtain ⟨k, A, B, hrot, hNL, hNR, hd, hleft, hright, -, -⟩ :=
    smoothingSuccessor_insert_child_data hn hP T hI v hv hc
  -- the two children are different
  have hab : owner hn hP (insert v.1 T) (Sum.inr v) ≠
      owner hn hP (insert v.1 T) (Sum.inr (visitTwin v)) := by
    intro he
    have hbL := (hleft (Sum.inr (visitTwin v))).mp he.symm
    exact hd hbL List.mem_cons_self
  -- every mark of the old block lies in one of the two children
  have hclass : ∀ m : Mark P, owner hn hP T m = owner hn hP T (Sum.inr v) →
      owner hn hP (insert v.1 T) m = owner hn hP (insert v.1 T) (Sum.inr v) ∨
      owner hn hP (insert v.1 T) m = owner hn hP (insert v.1 T) (Sum.inr (visitTwin v)) := by
    intro m hm
    have hmL : m ∈ (markList hn hP).rotate k := List.mem_rotate.mpr (mem_markList hn hP m)
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
  have hrot' : (markList hn hP).rotate (k + (Sum.inr v :: A).length) =
      Sum.inr (visitTwin v) :: (B ++ Sum.inr v :: A) := by
    rw [← List.rotate_rotate, hrot]
    change (((Sum.inr v :: A) ++ (Sum.inr (visitTwin v) :: B)).rotate
      (Sum.inr v :: A).length) = _
    rw [List.rotate_append_length_eq]
    rfl
  have hmemL : ∀ m : Mark P, owner hn hP (insert v.1 T) m =
      owner hn hP (insert v.1 T) (Sum.inr v) → m ∈ Sum.inr v :: B :=
    fun m hm => ncx_mem_cons_of_mem_cons_filter _ _ _ ((hleft m).mp hm)
  have hmemR : ∀ m : Mark P, owner hn hP (insert v.1 T) m =
      owner hn hP (insert v.1 T) (Sum.inr (visitTwin v)) → m ∈ Sum.inr (visitTwin v) :: A :=
    fun m hm => ncx_mem_cons_of_mem_cons_filter _ _ _ ((hright m).mp hm)
  rcases hclass m₁ hq1 with h1a | h1b <;> rcases hclass m₂ hq2 with h2a | h2b
  · exact h12 (h1a.trans h2a.symm)
  · -- m₁, m₃ in the child of v; m₂, m₄ in the child of the twin
    have h3a := h13.symm.trans h1a
    have h4b := h24.symm.trans h2b
    exact ncx_split_alternation_false hn hP k _ _ A B hrot m₁ m₂ m₃ m₄
      (hmemL m₁ h1a) (hmemL m₃ h3a) (hmemR m₂ h2b) (hmemR m₄ h4b) h123 h341
  · -- m₁, m₃ in the child of the twin; m₂, m₄ in the child of v
    have h3b := h13.symm.trans h1b
    have h4a := h24.symm.trans h2a
    exact ncx_split_alternation_false hn hP _ _ _ B A hrot' m₁ m₂ m₃ m₄
      (hmemR m₁ h1b) (hmemR m₃ h3b) (hmemL m₂ h2a) (hmemL m₄ h4a) h123 h341
  · exact h12 (h1b.trans h2b.symm)

/-- Processing any subset of an independent support keeps the ownership of all marks
noncrossing (induction as in `independent_partial_invariants`, whose invariants supply the
inherited order and the co-location of each unprocessed selected pair). -/
theorem independent_noncrossingOwners_partial (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (T : Finset (Crossing P)) (hTS : T ⊆ S) : NoncrossingOwners hn hP T := by
  revert hTS
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact noncrossingOwners_empty hn hP
  | @insert c T hc ih =>
    intro hTS
    have hcS : c ∈ S := hTS (Finset.mem_insert_self c T)
    have hTS' : T ⊆ S := fun z hz => hTS (Finset.mem_insert_of_mem hz)
    obtain ⟨hI, hPending⟩ := independent_partial_invariants hn hP hS T hTS'
    obtain ⟨i, _, _⟩ := crossing_visits_exist c
    let v : Visit P := ⟨c, i⟩
    have hvS : v.1 ∈ S := hcS
    have hv : v.1 ∉ T := hc
    have hsame := hPending v hvS hv
    exact noncrossingOwners_insert hn hP T hI v hv hsame (ih hTS')

/-- The ownership of all marks under an independent support is noncrossing. -/
theorem independent_noncrossingOwners (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    NoncrossingOwners hn hP S :=
  independent_noncrossingOwners_partial hn hP hS S (Finset.Subset.refl S)

/-! ## Cyclic order of four traversal points -/

omit [NeZero n] in
/-- Three points in strict oriented cyclic order are pairwise distinct. -/
theorem ncx_traversalBetween_ne {p q r : TraversalPoint n} (h : traversalBetween p q r) :
    p ≠ q ∧ q ≠ r ∧ p ≠ r := by
  unfold traversalBetween at h
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;>
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith

omit [NeZero n] in
/-- "`p₁, p₂, p₃, p₄` in that cyclic order" (`traversalBetween p₁ p₂ p₃ ∧ traversalBetween p₃ p₄ p₁`,
the alternation pattern of `Interlaces`) is equivalent to the four conditions "`p₂` strictly
between `p₁, p₃`; `p₃` strictly between `p₂, p₄`; `p₄` strictly between `p₃, p₁`; `p₁` strictly
between `p₄, p₂`". -/
theorem ncx_cyclic_four_iff (p₁ p₂ p₃ p₄ : TraversalPoint n) :
    (traversalBetween p₁ p₂ p₃ ∧ traversalBetween p₃ p₄ p₁) ↔
      (traversalBetween p₁ p₂ p₃ ∧ traversalBetween p₂ p₃ p₄ ∧
        traversalBetween p₃ p₄ p₁ ∧ traversalBetween p₄ p₁ p₂) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨h₃, h₄⟩ := traversalAlternating_rotate h₁ h₂
    exact ⟨h₁, h₃, h₂, h₄⟩
  · rintro ⟨h₁, -, h₂, -⟩
    exact ⟨h₁, h₂⟩

omit [NeZero n] in
/-- Four visits in strict cyclic order on the traversal circle are pairwise distinct. -/
theorem ncx_cyclic_visits_distinct (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (u₁ u₂ u₃ u₄ : Visit P)
    (h123 : traversalBetween (visitPosition hn hP u₁) (visitPosition hn hP u₂)
      (visitPosition hn hP u₃))
    (h341 : traversalBetween (visitPosition hn hP u₃) (visitPosition hn hP u₄)
      (visitPosition hn hP u₁)) :
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

/-! ## lem:carriers (iv) -/

/-- **lem:carriers (iv), for all marks.** For an independent support `S`, no four marks
`m₁, m₂, m₃, m₄` in that cyclic order on the marked traversal circle have `m₁, m₃` on one
carrier and `m₂, m₄` on a different carrier. -/
theorem carriers_noncrossing_marks (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (m₁ m₂ m₃ m₄ : Mark P)
    (h123 : traversalBetween (markPosition hn hP.1 m₁) (markPosition hn hP.1 m₂)
      (markPosition hn hP.1 m₃))
    (h341 : traversalBetween (markPosition hn hP.1 m₃) (markPosition hn hP.1 m₄)
      (markPosition hn hP.1 m₁)) :
    ¬ (owner hn hP S m₁ = owner hn hP S m₃ ∧ owner hn hP S m₂ = owner hn hP S m₄ ∧
        owner hn hP S m₁ ≠ owner hn hP S m₂) := by
  rintro ⟨h13, h24, h12⟩
  exact h12 (independent_noncrossingOwners hn hP hS m₁ m₂ m₃ m₄ h123 h341 h13 h24)

/-- **lem:carriers (iv).** Let `S ∈ Ind(G_P)`. The assignment of all crossing visits to
carriers under the incoming-visit convention (`owner hn hP S (Sum.inr u)`) is noncrossing:
for visits `u₁, u₂, u₃, u₄` in that cyclic order on the traversal circle, it is not the case
that `u₁, u₃` lie on one carrier and `u₂, u₄` on a different carrier. This includes selected
visits. -/
theorem carriers_noncrossing_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (u₁ u₂ u₃ u₄ : Visit P)
    (h123 : traversalBetween (visitPosition hn hP.1 u₁) (visitPosition hn hP.1 u₂)
      (visitPosition hn hP.1 u₃))
    (h341 : traversalBetween (visitPosition hn hP.1 u₃) (visitPosition hn hP.1 u₄)
      (visitPosition hn hP.1 u₁)) :
    ¬ (owner hn hP S (Sum.inr u₁) = owner hn hP S (Sum.inr u₃) ∧
        owner hn hP S (Sum.inr u₂) = owner hn hP S (Sum.inr u₄) ∧
        owner hn hP S (Sum.inr u₁) ≠ owner hn hP S (Sum.inr u₂)) :=
  carriers_noncrossing_marks hn hP hS (Sum.inr u₁) (Sum.inr u₂) (Sum.inr u₃) (Sum.inr u₄)
    h123 h341

/-- **lem:carriers (iv), as printed.** "There are no four distinct visits `u₁, u₂, u₃, u₄` in
that cyclic order with `u₁, u₃` on one carrier and `u₂, u₄` on a different carrier." -/
theorem carriers_noncrossing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    ¬ ∃ u₁ u₂ u₃ u₄ : Visit P,
      (u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₃ ≠ u₄) ∧
      traversalBetween (visitPosition hn hP.1 u₁) (visitPosition hn hP.1 u₂)
        (visitPosition hn hP.1 u₃) ∧
      traversalBetween (visitPosition hn hP.1 u₃) (visitPosition hn hP.1 u₄)
        (visitPosition hn hP.1 u₁) ∧
      owner hn hP S (Sum.inr u₁) = owner hn hP S (Sum.inr u₃) ∧
      owner hn hP S (Sum.inr u₂) = owner hn hP S (Sum.inr u₄) ∧
      owner hn hP S (Sum.inr u₁) ≠ owner hn hP S (Sum.inr u₂) := by
  rintro ⟨u₁, u₂, u₃, u₄, -, h123, h341, h13, h24, h12⟩
  exact carriers_noncrossing_visits hn hP hS u₁ u₂ u₃ u₄ h123 h341 ⟨h13, h24, h12⟩

/-- lem:carriers (iv) in the positive form: if `u₁, u₃` share a carrier and `u₂, u₄` share a
carrier, then all four share it. -/
theorem carriers_noncrossing_owner_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (u₁ u₂ u₃ u₄ : Visit P)
    (h123 : traversalBetween (visitPosition hn hP.1 u₁) (visitPosition hn hP.1 u₂)
      (visitPosition hn hP.1 u₃))
    (h341 : traversalBetween (visitPosition hn hP.1 u₃) (visitPosition hn hP.1 u₄)
      (visitPosition hn hP.1 u₁))
    (h13 : owner hn hP S (Sum.inr u₁) = owner hn hP S (Sum.inr u₃))
    (h24 : owner hn hP S (Sum.inr u₂) = owner hn hP S (Sum.inr u₄)) :
    owner hn hP S (Sum.inr u₁) = owner hn hP S (Sum.inr u₂) :=
  independent_noncrossingOwners hn hP hS (Sum.inr u₁) (Sum.inr u₂) (Sum.inr u₃) (Sum.inr u₄)
    h123 h341 h13 h24

/-- lem:carriers (iv) via the sorted mark list rotated to start anywhere (e.g. at `u₁`): for
positions `i₁ < i₂ < i₃ < i₄` in `(markList hn hP).rotate k`, if the marks at `i₁, i₃` share a
carrier and those at `i₂, i₄` share a carrier, then all four share it. -/
theorem carriers_noncrossing_rotate (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (k i₁ i₂ i₃ i₄ : ℕ) (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄)
    (hi₄ : i₄ < ((markList hn hP).rotate k).length)
    (h13 : owner hn hP S (((markList hn hP).rotate k)[i₁]'(by omega)) =
      owner hn hP S (((markList hn hP).rotate k)[i₃]'(by omega)))
    (h24 : owner hn hP S (((markList hn hP).rotate k)[i₂]'(by omega)) =
      owner hn hP S (((markList hn hP).rotate k)[i₄]'hi₄)) :
    owner hn hP S (((markList hn hP).rotate k)[i₁]'(by omega)) =
      owner hn hP S (((markList hn hP).rotate k)[i₂]'(by omega)) := by
  have hi₁ : i₁ < ((markList hn hP).rotate k).length := by omega
  have hi₂ : i₂ < ((markList hn hP).rotate k).length := by omega
  have hi₃ : i₃ < ((markList hn hP).rotate k).length := by omega
  have h123 := (ncx_markList_rotate_between_iff hn hP k i₁ i₂ i₃ hi₁ hi₂ hi₃).mpr
    (Or.inl ⟨h12, h23⟩)
  have h341 := (ncx_markList_rotate_between_iff hn hP k i₃ i₄ i₁ hi₃ hi₄ hi₁).mpr
    (Or.inr (Or.inr ⟨by omega, h34⟩))
  exact independent_noncrossingOwners hn hP hS _ _ _ _ h123 h341 h13 h24

/-- lem:carriers (iv) for a decomposition `S` (def:decomposition, `IsDecomposition`). -/
theorem carriers_noncrossing_of_isDecomposition (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) :
    ¬ ∃ u₁ u₂ u₃ u₄ : Visit P,
      (u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₃ ≠ u₄) ∧
      traversalBetween (visitPosition hn hP.1 u₁) (visitPosition hn hP.1 u₂)
        (visitPosition hn hP.1 u₃) ∧
      traversalBetween (visitPosition hn hP.1 u₃) (visitPosition hn hP.1 u₄)
        (visitPosition hn hP.1 u₁) ∧
      owner hn hP S (Sum.inr u₁) = owner hn hP S (Sum.inr u₃) ∧
      owner hn hP S (Sum.inr u₂) = owner hn hP S (Sum.inr u₄) ∧
      owner hn hP S (Sum.inr u₁) ≠ owner hn hP S (Sum.inr u₂) :=
  carriers_noncrossing hn hP hS

end
end SM.Carrier
