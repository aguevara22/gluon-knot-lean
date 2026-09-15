import SM.CarrierActualCornerBlock
import SM.CarrierComponentCount

/-! Towards def:smoothing / lem:carriers (iii) (sm-3-statesum.tex:14, 54): a crossing interlacing a selected crossing has its visits on different carriers. Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-smoothing-support / prove:smoothing-B), checked with `lake env lean` (sorry-free, standard axioms) and
ported verbatim from work/drafts/SmoothingSupportB.lean (only this header added and #print lines removed). -/

/-! # Task B: neighbours of an independent support have separated visits

Source: reference/SM/sm-3-statesum.tex, def:smoothing (lines 14-27), last sentence:
"A crossing in N(S) has its two visits on different subpolygons and is a crossing of
no subpolygon", and lem:carriers (iii) (lines 54-95): "An unselected crossing
interlacing some element of S has its visits on different carriers"; proof lines
169-182 ("process s first ... Its split puts the two visits of x on different cycles.
Later reconnections only split, so they can never be reunited").

Encoding (the finite successor model of the Carrier lane):
* the traversal circle cut and reconnected at the visits of `S` is the permutation
  `smoothingSuccessor hn hP S` of `Mark P`; its cycles are `Component hn hP S`, and the
  carrier a visit is assigned to (incoming-visit convention) is `owner hn hP S (Sum.inr v)`;
* the two visits of the crossing `x` are `v` and `visitTwin v` for any `v : Visit P` with
  `v.1 = x`;
* `N(S)` is `supportNeighbors hn hP S`; "x interlaces s" is `Interlaces hn hP x s`;
  `S ∈ Ind(G_P)` is `S ∈ independentSupports hn hP`;
* "the crossings of Q are the crossings x ∈ X(P) \ S both of whose visits lie on Q" is
  `IsCrossingOf hn hP S q x` below.

The proof follows the source: with `s ∈ S` interlacing `x`, the single switch at `s`
applied to the original circle already separates the two visits of `x` (they lie in
different open arcs of the circle cut at the visits of `s`, because they interlace), and
every later insertion of an element of `S \ {s}` only splits cycles
(`owner_insert_ne_of_ne`), so the visits are never reunited. -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Interlacing puts the two visits of the other crossing in *different* open arcs of the
original marked circle cut at the two visits of `v`: one in the forward arc `A` and one
in the backward arc `B` of any rotated presentation `v :: (A ++ twin v :: B)`. This is the
converse direction of `independent_twin_same_slice`. -/
theorem interlaces_twin_different_slices (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v w : Visit P) (hint : Interlaces hn hP v.1 w.1)
    (k : ℕ) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) :
    (Sum.inr w ∈ A ∧ Sum.inr (visitTwin w) ∈ B) ∨
      (Sum.inr w ∈ B ∧ Sum.inr (visitTwin w) ∈ A) := by
  have hvw : v.1 ≠ w.1 := hint.1
  -- the arc statuses of the two visits of `w` differ
  have hdiff : ¬ (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 (visitTwin v)) ↔
        traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) :=
    fun h => (not_interlaces_iff_twin_same_arc hn hP v w hvw).mpr h hint
  -- every visit of `w` is in one of the two open arcs
  have hmem : ∀ u : Visit P, u.1 = w.1 → (Sum.inr u : Mark P) ∈ A ∨ (Sum.inr u : Mark P) ∈ B := by
    intro u hu
    have h1 : (Sum.inr u : Mark P) ∈ (markList hn hP).rotate k :=
      List.mem_rotate.mpr (mem_markList hn hP _)
    rw [hrot] at h1
    rcases List.mem_cons.mp h1 with he | h1
    · have h2 : u.1 = v.1 := congrArg Sigma.fst (Sum.inr.inj he)
      exact (hvw (h2.symm.trans hu)).elim
    · rcases List.mem_append.mp h1 with hA | hB
      · exact Or.inl hA
      · rcases List.mem_cons.mp hB with he | hB
        · have h2 : u.1 = (visitTwin v).1 := congrArg Sigma.fst (Sum.inr.inj he)
          rw [visitTwin_crossing] at h2
          exact (hvw (h2.symm.trans hu)).elim
        · exact Or.inr hB
  have hAiff : ∀ m : Mark P, m ∈ A ↔
      traversalBetween (markPosition hn hP.1 (Sum.inr v)) (markPosition hn hP.1 m)
        (markPosition hn hP.1 (Sum.inr (visitTwin v))) :=
    markList_rotate_left_iff hn hP k _ _ A B hrot
  by_cases hw : (Sum.inr w : Mark P) ∈ A
  · have hb1 : traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
        (visitPosition hn hP.1 (visitTwin v)) := (hAiff _).mp hw
    have hnt : (Sum.inr (visitTwin w) : Mark P) ∉ A := by
      intro ht
      have hb2 : traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v)) :=
        (hAiff _).mp ht
      exact hdiff ⟨fun _ => hb2, fun _ => hb1⟩
    rcases hmem (visitTwin w) (visitTwin_crossing w) with h | h
    · exact (hnt h).elim
    · exact Or.inl ⟨hw, h⟩
  · have hnb1 : ¬ traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
        (visitPosition hn hP.1 (visitTwin v)) := fun h => hw ((hAiff _).mpr h)
    have ht : (Sum.inr (visitTwin w) : Mark P) ∈ A := by
      by_contra ht
      have hnb2 : ¬ traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v)) :=
        fun h => ht ((hAiff _).mpr h)
      exact hdiff ⟨fun h => (hnb1 h).elim, fun h => (hnb2 h).elim⟩
    rcases hmem w rfl with h | h
    · exact (hw h).elim
    · exact Or.inr ⟨h, ht⟩

/-- **Arc separation at a single switch.** Let the current successor `ρ_T` inherit the
marked order, let `u` be a fresh selected visit whose twin lies on the same current cycle,
and let `w` be a visit of a crossing interlacing `u.1` whose two visits both lie on that
cycle. Then the switch at `u.1` puts the two visits of `w` on different cycles of
`ρ_{insert u.1 T}`. -/
theorem interlacing_pair_owners_ne_insert (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (u : Visit P) (hu : u.1 ∉ T)
    (hc : owner hn hP T (Sum.inr u) = owner hn hP T (Sum.inr (visitTwin u)))
    (w : Visit P) (hint : Interlaces hn hP u.1 w.1)
    (hw : owner hn hP T (Sum.inr w) = owner hn hP T (Sum.inr u))
    (hwt : owner hn hP T (Sum.inr (visitTwin w)) = owner hn hP T (Sum.inr u)) :
    owner hn hP (insert u.1 T) (Sum.inr w) ≠
      owner hn hP (insert u.1 T) (Sum.inr (visitTwin w)) := by
  obtain ⟨k, A, B, hrot, hNL, hNR, hd, hleft, hright, hactL, hactR⟩ :=
    smoothingSuccessor_insert_child_data hn hP T hI u hu hc
  -- the two children are different
  have hne : owner hn hP (insert u.1 T) (Sum.inr u) ≠
      owner hn hP (insert u.1 T) (Sum.inr (visitTwin u)) := by
    intro he
    have hbL := (hleft (Sum.inr (visitTwin u))).mp he.symm
    exact hd hbL List.mem_cons_self
  have hfilA : ∀ m : Mark P, m ∈ A → owner hn hP T m = owner hn hP T (Sum.inr u) →
      m ∈ A.filter (fun m => decide (owner hn hP T m = owner hn hP T (Sum.inr u))) :=
    fun m hm ho => List.mem_filter.mpr ⟨hm, decide_eq_true ho⟩
  have hfilB : ∀ m : Mark P, m ∈ B → owner hn hP T m = owner hn hP T (Sum.inr u) →
      m ∈ B.filter (fun m => decide (owner hn hP T m = owner hn hP T (Sum.inr u))) :=
    fun m hm ho => List.mem_filter.mpr ⟨hm, decide_eq_true ho⟩
  rcases interlaces_twin_different_slices hn hP u w hint k A B hrot with ⟨hwA, htB⟩ | ⟨hwB, htA⟩
  · have h1 : owner hn hP (insert u.1 T) (Sum.inr w) =
        owner hn hP (insert u.1 T) (Sum.inr (visitTwin u)) :=
      (hright (Sum.inr w)).mpr (List.mem_cons_of_mem _ (hfilA _ hwA hw))
    have h2 : owner hn hP (insert u.1 T) (Sum.inr (visitTwin w)) =
        owner hn hP (insert u.1 T) (Sum.inr u) :=
      (hleft (Sum.inr (visitTwin w))).mpr (List.mem_cons_of_mem _ (hfilB _ htB hwt))
    rw [h1, h2]
    exact hne.symm
  · have h1 : owner hn hP (insert u.1 T) (Sum.inr w) =
        owner hn hP (insert u.1 T) (Sum.inr u) :=
      (hleft (Sum.inr w)).mpr (List.mem_cons_of_mem _ (hfilB _ hwB hw))
    have h2 : owner hn hP (insert u.1 T) (Sum.inr (visitTwin w)) =
        owner hn hP (insert u.1 T) (Sum.inr (visitTwin u)) :=
      (hright (Sum.inr (visitTwin w))).mpr (List.mem_cons_of_mem _ (hfilA _ htA hwt))
    rw [h1, h2]
    exact hne

/-- "Process `s` first": for `s ∈ S` interlacing the crossing of `v`, after switching `s`
and then any subset `T ⊆ S \ {s}` of the remaining selected crossings, the two visits of
`v.1` have different owners. Induction on `T`; each later insertion only splits
(`owner_insert_ne_of_ne`, whose same-cycle premise is `independent_remaining_pair_owners`). -/
theorem interlacing_visit_owners_ne_insert_partial (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {s : Crossing P} (hsS : s ∈ S) (v : Visit P) (hint : Interlaces hn hP v.1 s)
    (T : Finset (Crossing P)) (hT : T ⊆ S.erase s) :
    owner hn hP (insert s T) (Sum.inr v) ≠
      owner hn hP (insert s T) (Sum.inr (visitTwin v)) := by
  revert hT
  induction T using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨i, _, _⟩ := crossing_visits_exist s
    let u : Visit P := ⟨s, i⟩
    have hu : u.1 ∉ (∅ : Finset (Crossing P)) := Finset.notMem_empty _
    have hsub := component_empty_subsingleton hn hP
    have hint' : Interlaces hn hP u.1 v.1 := interlaces_symm hn hP hint
    exact interlacing_pair_owners_ne_insert hn hP ∅ (inheritsMarkOrder_empty hn hP) u hu
      (hsub.elim _ _) v hint' (hsub.elim _ _) (hsub.elim _ _)
  | @insert c T hcT ih =>
    intro hT
    have hT' : T ⊆ S.erase s := fun z hz => hT (Finset.mem_insert_of_mem hz)
    have hcE : c ∈ S.erase s := hT (Finset.mem_insert_self c T)
    have hcs : c ≠ s := (Finset.mem_erase.mp hcE).1
    have hcS : c ∈ S := (Finset.mem_erase.mp hcE).2
    have ih' := ih hT'
    have hcU : c ∉ insert s T := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hcs h
      · exact hcT h
    have hUS : insert s T ⊆ S :=
      Finset.insert_subset hsS (hT'.trans (Finset.erase_subset _ _))
    obtain ⟨i, _, _⟩ := crossing_visits_exist c
    let w : Visit P := ⟨c, i⟩
    have hpend : owner hn hP (insert s T) (Sum.inr w) =
        owner hn hP (insert s T) (Sum.inr (visitTwin w)) :=
      independent_remaining_pair_owners hn hP hS (insert s T) hUS w hcS hcU
    have hres : owner hn hP (insert c (insert s T)) (Sum.inr v) ≠
        owner hn hP (insert c (insert s T)) (Sum.inr (visitTwin v)) :=
      owner_insert_ne_of_ne hn hP (insert s T) w hcU
        ((owner_eq_iff hn hP _ _ _).mp hpend) ih'
    rw [Finset.insert_comm c s T] at hres
    exact hres

/-- **lem:carriers (iii), first ownership assertion / def:smoothing, last sentence.**
A crossing `x ∈ N(S)` of an independent support `S` has its two visits `v`, `visitTwin v`
on different carriers of `S`. -/
theorem neighbor_visit_owners_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportNeighbors hn hP S) (v : Visit P) (hv : v.1 = x) :
    owner hn hP S (Sum.inr v) ≠ owner hn hP S (Sum.inr (visitTwin v)) := by
  obtain ⟨s, hsS, hint⟩ := (mem_supportNeighbors hn hP S x).mp hx
  have hint' : Interlaces hn hP v.1 s := by
    rw [hv]
    exact hint
  have h := interlacing_visit_owners_ne_insert_partial hn hP hS hsS v hint'
    (S.erase s) (Finset.Subset.refl _)
  rw [Finset.insert_erase hsS] at h
  exact h

/-- The same statement phrased with the interlacing witness: an unselected crossing
interlacing some element of `S` has its visits on different carriers. -/
theorem interlacing_visit_owners_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {s : Crossing P} (hsS : s ∈ S) (v : Visit P) (hint : Interlaces hn hP v.1 s) :
    owner hn hP S (Sum.inr v) ≠ owner hn hP S (Sum.inr (visitTwin v)) :=
  neighbor_visit_owners_ne hn hP hS
    ((mem_supportNeighbors hn hP S v.1).mpr ⟨s, hsS, hint⟩) v rfl

omit [NeZero n] in
/-- A neighbour of an independent support is unselected (`N(S) ∩ S = ∅`), since the
interlacement graph is loopless and `S` is independent. -/
theorem neighbor_not_mem (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportNeighbors hn hP S) : x ∉ S := by
  intro hxS
  obtain ⟨s, hsS, hint⟩ := (mem_supportNeighbors hn hP S x).mp hx
  exact (mem_independentSupports_iff hn hP S).mp hS x hxS s hsS hint.1 hint

/-- def:smoothing: "The crossings of `Q` are the crossings `x ∈ X(P) \ S` both of whose
visits lie on `Q`." Here `Q` is the carrier `q : Component hn hP S`, and a visit lies on
`Q` when its owner (incoming-visit convention) is `q`. -/
def IsCrossingOf (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (x : Crossing P) : Prop :=
  x ∉ S ∧ ∀ v : Visit P, v.1 = x → owner hn hP S (Sum.inr v) = q

/-- No carrier owns both visits of a crossing in `N(S)`. -/
theorem neighbor_no_common_owner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportNeighbors hn hP S) (v : Visit P) (hv : v.1 = x)
    (q : Component hn hP S) :
    ¬ (owner hn hP S (Sum.inr v) = q ∧ owner hn hP S (Sum.inr (visitTwin v)) = q) :=
  fun h => neighbor_visit_owners_ne hn hP hS hx v hv (h.1.trans h.2.symm)

/-- **def:smoothing, last sentence, second half.** A crossing in `N(S)` is a crossing of
no subpolygon. -/
theorem neighbor_not_isCrossingOf (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportNeighbors hn hP S) (q : Component hn hP S) :
    ¬ IsCrossingOf hn hP S q x := by
  rintro ⟨_, hall⟩
  obtain ⟨i, _, _⟩ := crossing_visits_exist x
  let v : Visit P := ⟨x, i⟩
  exact neighbor_no_common_owner hn hP hS hx v rfl q
    ⟨hall v rfl, hall (visitTwin v) (visitTwin_crossing v)⟩

end
end SM.Carrier
