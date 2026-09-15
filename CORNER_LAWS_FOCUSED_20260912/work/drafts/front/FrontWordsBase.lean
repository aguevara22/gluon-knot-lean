import SM.FrontInterfaces

/-! Front block, lane β, base unit (2026-09-14): module `SM/FrontWordsBase.lean` (intended home); draft
work/drafts/front/FrontWordsBase.lean; report work/drafts/front/HINV_REPORT.md.

# Commutation invariance of the standard-circle base, and the unconditional descent of nonbase words

`SM/FrontInterfaces.lean` (the accepted statement unit of the literature input ng:finite-word) derives the
registry sentence "Thus every nonbase front has a finite principal chain to a front of smaller s"
(AXIOM_REGISTRY.md:105-106) in `Descends.of_principalChain` / `ng_finite_word_nonbase_descends` only under
the hypothesis

  `hinv : ∀ W W' : OWord, IsComm W.letters W'.letters → (W.IsStandardCircleBase ↔ W'.IsStandardCircleBase)`

(a disjoint-gadget commutation is the same front, ng:commutation sm-3:1921-1948), and its review recorded
the OBLIGATION to prove `hinv`.  This module discharges it and projects the unconditional statement.

## The base and why the two runs are not literally equal

`Word.IsStandardCircleBase W := labelRun W 0 [] = some []` (FrontInterfaces §1): the word is run over cuts of
LABELS, the letter at letter index `k` (0-based position in the word) pushing two arms labelled `k` if it
is a left cusp, a right cusp removing two adjacent strands of the SAME label, a crossing untyped.  A
disjoint-gadget commutation `X ++ [a, b] ++ Y ↦ X ++ [b', a'] ++ Y` (`IsCommStep`; `a'`, `b'` the reindexed
letters) moves the letter `a` from letter index `|X|` to `|X| + 1` and `b` the other way, so the fresh
labels the two letters allocate are EXCHANGED: the label cuts after the factor differ by the transposition
`|X| ↔ |X| + 1` of labels (by `decide` below: `l₁ l₃` gives `[0, 0, 1, 1]`, its commutation `l₁ l₁` gives
`[1, 1, 0, 0]`).  The labels present before the factor are `< |X|` (`labelRun_lt`), so the transposition
fixes them; the labels `Y` allocates are `≥ |X| + 2`, so it fixes those too.

## Route

1. Injective relabelling commutes with the label operations, the fresh label mapped along:
   `Letter.labelAct_map`, `Letter.labelStep_map` (any injective `f`), `Word.labelRun_map` (`f` fixing every
   label `≥ k`, the counter).
2. The positional disjoint-window argument of β1's `run_comm_above` / `run_comm_below`, repeated for
   `labelStep` (`labelStep_prefix`, `labelStep_eq_some_iff`, `labelAct_append`, `labelAct_window`):
   `labelRun_comm_above`, `labelRun_comm_below` state that exchanging the two letters and applying any
   injective `f` with `f k = k + 1`, `f (k + 1) = k` to the cuts gives the run of the exchanged pair.
3. `labelRun_lt`: the labels after a run from letter index `k` over labels `< k` are `< k + |W|`.
4. `IsCommStep.isStandardCircleBase` (one direction, with `f := Equiv.swap |X| (|X| + 1)`),
   `IsCommStep.symm` (the reverse exchange is a commutation step), hence
   `IsCommStep.isStandardCircleBase_iff`, `IsComm.isStandardCircleBase_iff`,
   `IsComm.oword_isStandardCircleBase_iff` (= `hinv`, named `isStandardCircleBase_comm_invariant`).
5. `Descends.of_principalChain'` (unconditional, standard axioms only) and
   `SM.ng_finite_word_nonbase_descends'` (consumes `SM.ng_finite_word` exactly as the conditional theorem).

Nothing in `SM/FrontWords.lean` or `SM/FrontInterfaces.lean` is changed or restated.  Checked with `cd
work/lean && lake env lean ../drafts/front/FrontWordsBase.lean` (no placeholders, no new axioms). -/

namespace SM.FrontWord

/-- discharges the index and length side conditions with mapped and appended cuts -/
local macro "labomega" : tactic =>
  `(tactic| ((try simp only [Letter.idx_reindex, List.length_append, List.length_map, List.length_singleton,
      List.length_cons, List.length_nil] at *) <;> omega))

/-! ## 1. The label action: unfolding lemmas, injective relabelling -/

namespace Letter

@[simp] theorem labelAct_l (m : ℕ) (d : Bool) (k : ℕ) (L : List ℕ) :
    (Letter.l m d).labelAct k L = some (k :: k :: L) := rfl

@[simp] theorem labelAct_r_cons (m k a b : ℕ) (L : List ℕ) :
    (Letter.r m).labelAct k (a :: b :: L) = if a = b then some L else none := rfl

/-- reindexing does not change the label action (as `act_reindex`) -/
@[simp] theorem labelAct_reindex (ℓ : Letter) (n : ℕ) : (ℓ.reindex n).labelAct = ℓ.labelAct := by
  cases ℓ <;> funext k L <;> rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩ <;> rfl

theorem labelAct_r_eq_some_iff {m k : ℕ} {L L' : List ℕ} :
    (Letter.r m).labelAct k L = some L' ↔ ∃ a, L = a :: a :: L' := by
  constructor
  · intro h
    match L, h with
    | a :: b :: L₀, h =>
      simp only [labelAct_r_cons] at h
      split_ifs at h with hab
      · subst hab
        obtain rfl := Option.some.inj h
        exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    simp

/-- every label of the output is the fresh label or a label of the input -/
theorem labelAct_mem {ℓ : Letter} {k : ℕ} {L L' : List ℕ} (h : ℓ.labelAct k L = some L') {x : ℕ}
    (hx : x ∈ L') : x = k ∨ x ∈ L := by
  cases ℓ with
  | l m d =>
    simp only [labelAct_l, Option.some.injEq] at h
    subst h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr hx
  | r m =>
    obtain ⟨a, rfl⟩ := labelAct_r_eq_some_iff.1 h
    exact Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  | σ m => simp at h

/-- An injective relabelling commutes with the label action when the fresh label is mapped along: the
right cusp's equality test is invariant, the left cusp pushes the mapped fresh label. -/
theorem labelAct_map {f : ℕ → ℕ} (hf : Function.Injective f) (ℓ : Letter) (k : ℕ) (L : List ℕ) :
    ℓ.labelAct (f k) (L.map f) = (ℓ.labelAct k L).map (List.map f) := by
  cases ℓ with
  | l m d => rfl
  | r m =>
    rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩
    · rfl
    · rfl
    · by_cases hab : a = b <;> simp [hab, hf.eq_iff]
  | σ m => rfl

/-- the same for the positional step -/
theorem labelStep_map {f : ℕ → ℕ} (hf : Function.Injective f) (ℓ : Letter) (k : ℕ) (c : List ℕ) :
    ℓ.labelStep (f k) (c.map f) = (ℓ.labelStep k c).map (List.map f) := by
  unfold labelStep
  rw [List.length_map]
  split_ifs with h
  · rw [← List.map_drop, labelAct_map hf, Option.map_map, Option.map_map]
    congr 1
    funext L
    simp [Function.comp, List.map_append, List.map_take]
  · rfl

/-! ### The positional lemmas of β1 (`step_prefix`, `step_eq_some_iff`, `act_append`, `act_window`) for
the labelled step -/

/-- The letter is typed at `A ++ L` with `|A| = m − 1`: it acts on `L` and keeps `A`. -/
theorem labelStep_prefix {ℓ : Letter} {k : ℕ} {A L : List ℕ} (h1 : 1 ≤ ℓ.idx) (hA : A.length = ℓ.idx - 1) :
    ℓ.labelStep k (A ++ L) = (ℓ.labelAct k L).map (A ++ ·) := by
  unfold labelStep
  rw [ite_eq_left ⟨h1, by simp only [List.length_append]; omega⟩, List.take_left' hA, List.drop_left' hA]

theorem labelStep_of_prefix {ℓ : Letter} {k : ℕ} {A L L' : List ℕ} (h1 : 1 ≤ ℓ.idx)
    (hA : A.length = ℓ.idx - 1) (hL : ℓ.labelAct k L = some L') : ℓ.labelStep k (A ++ L) = some (A ++ L') := by
  rw [labelStep_prefix h1 hA, hL]; rfl

/-- A typed labelled step decomposes the cut at the letter's position. -/
theorem labelStep_eq_some_iff {ℓ : Letter} {k : ℕ} {c c' : List ℕ} :
    ℓ.labelStep k c = some c' ↔
      ∃ A L L' : List ℕ, 1 ≤ ℓ.idx ∧ A.length = ℓ.idx - 1 ∧ c = A ++ L ∧ ℓ.labelAct k L = some L' ∧
        c' = A ++ L' := by
  constructor
  · intro h
    unfold labelStep at h
    split_ifs at h with hc
    · obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.1 h
      refine ⟨c.take (ℓ.idx - 1), c.drop (ℓ.idx - 1), L', hc.1, ?_, (List.take_append_drop _ _).symm, hL', rfl⟩
      simp only [List.length_take]; omega
  · rintro ⟨A, L, L', h1, hA, rfl, hL, rfl⟩
    exact labelStep_of_prefix h1 hA hL

/-- `labelAct` only reads the first `arity` strands: the rest is carried along. -/
theorem labelAct_append {ℓ : Letter} {k : ℕ} {w R : List ℕ} (hw : w.length = ℓ.arity) :
    ℓ.labelAct k (w ++ R) = (ℓ.labelAct k w).map (· ++ R) := by
  cases ℓ with
  | l m d =>
    obtain rfl := List.eq_nil_of_length_eq_zero hw
    simp
  | r m =>
    obtain ⟨a, b, rfl⟩ : ∃ a b, w = [a, b] := by
      match w, hw with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    by_cases hab : a = b <;> simp [hab]
  | σ m => rfl

/-- A typed labelled action splits off its window of `arity` incoming strands, producing `coarity`
outgoing strands and carrying the rest along. -/
theorem labelAct_window {ℓ : Letter} {k : ℕ} {L L' : List ℕ} (h : ℓ.labelAct k L = some L') :
    ∃ w w' R : List ℕ, L = w ++ R ∧ w.length = ℓ.arity ∧ ℓ.labelAct k w = some w' ∧
      w'.length = ℓ.coarity ∧ L' = w' ++ R := by
  cases ℓ with
  | l m d =>
    refine ⟨[], [k, k], L, rfl, rfl, rfl, rfl, ?_⟩
    simpa using h.symm
  | r m =>
    obtain ⟨a, rfl⟩ := labelAct_r_eq_some_iff.1 h
    exact ⟨[a, a], [], L', rfl, rfl, by simp, rfl, rfl⟩
  | σ m => simp at h

end Letter

/-! ## 2. The labelled run: concatenation, relabelling, the label bound -/

namespace Word

theorem labelRun_append (V W : Word) (k : ℕ) (c : List ℕ) :
    labelRun (V ++ W) k c = (labelRun V k c).bind (labelRun W (k + V.length)) := by
  induction V generalizing k c with
  | nil => simp
  | cons a V ih =>
    simp only [List.cons_append, labelRun_cons, Option.bind_assoc, List.length_cons]
    congr 1
    funext c'
    rw [ih]
    have e : k + 1 + V.length = k + (V.length + 1) := by omega
    rw [e]

theorem labelRun_two_iff {a b : Letter} {k : ℕ} {c c' : List ℕ} :
    labelRun [a, b] k c = some c' ↔ ∃ c₁, a.labelStep k c = some c₁ ∧ b.labelStep (k + 1) c₁ = some c' := by
  simp only [labelRun_cons, labelRun_nil, Option.bind_eq_some_iff, Option.some.injEq, exists_eq_right]

/-- An injective relabelling that fixes every label from the counter `k` on (the fresh labels of the run)
commutes with the labelled run. -/
theorem labelRun_map {f : ℕ → ℕ} (hf : Function.Injective f) (W : Word) :
    ∀ (k : ℕ) (c : List ℕ), (∀ j, k ≤ j → f j = j) →
      labelRun W k (c.map f) = (labelRun W k c).map (List.map f) := by
  induction W with
  | nil => intro k c _; rfl
  | cons a W ih =>
    intro k c hfix
    have h1 : a.labelStep k (c.map f) = (a.labelStep k c).map (List.map f) := by
      have := Letter.labelStep_map hf a k c
      rwa [hfix k le_rfl] at this
    rw [labelRun_cons, labelRun_cons, h1, Option.bind_map, Option.map_bind]
    congr 1
    funext c₁
    simp only [Function.comp_apply]
    exact ih (k + 1) c₁ (fun j hj => hfix j (by omega))

/-- The labels after a run from letter index `k` over labels `< k` are `< k + |W|`. -/
theorem labelRun_lt {W : Word} :
    ∀ {k : ℕ} {c c' : List ℕ}, (∀ x ∈ c, x < k) → labelRun W k c = some c' → ∀ x ∈ c', x < k + W.length := by
  induction W with
  | nil =>
    intro k c c' hc h
    rw [labelRun_nil] at h
    obtain rfl := Option.some.inj h
    intro x hx
    exact lt_of_lt_of_le (hc x hx) (Nat.le_add_right _ _)
  | cons a W ih =>
    intro k c c' hc h
    rw [labelRun_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, h1, h2⟩ := h
    have hc₁ : ∀ x ∈ c₁, x < k + 1 := by
      obtain ⟨A, L, L', -, -, rfl, hL, rfl⟩ := Letter.labelStep_eq_some_iff.1 h1
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact Nat.lt_succ_of_lt (hc x (List.mem_append_left _ hx))
      · rcases Letter.labelAct_mem hL hx with rfl | hx
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (hc x (List.mem_append_right _ hx))
    intro x hx
    have := ih hc₁ h2 x hx
    simp only [List.length_cons]
    omega

end Word

/-! ## 3. Exchanging two disjoint gadgets in the labelled run

The positional argument of β1's `run_comm_above` / `run_comm_below`, with the fresh labels of the two
letters exchanged by any injective `f` with `f k = k + 1`, `f (k + 1) = k`. -/

section Comm

open Letter Word

/-- split a labelled cut at a length (β1's `exists_split` is stated for `Cuts = List Bool`) -/
theorem exists_split_labels (c : List ℕ) (n : ℕ) (h : n ≤ c.length) :
    ∃ A B : List ℕ, c = A ++ B ∧ A.length = n :=
  ⟨c.take n, c.drop n, (List.take_append_drop n c).symm, by simp only [List.length_take]; omega⟩

/-- `b` acts above `a`: exchanging them (with `a` reindexed through `b`) and relabelling the cuts by `f`
gives the run of the exchanged pair. -/
theorem labelRun_comm_above {f : ℕ → ℕ} (hf : Function.Injective f) {k : ℕ} (hfk : f k = k + 1)
    (hfk1 : f (k + 1) = k) {a b : Letter} {c c' : List ℕ} (hab : b.idx + b.arity ≤ a.idx)
    (h : labelRun [a, b] k c = some c') :
    labelRun [b, a.reindex (a.idx + b.coarity - b.arity)] k (c.map f) = some (c'.map f) := by
  rw [labelRun_two_iff] at h
  rw [labelRun_two_iff]
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', ha1, hA, rfl, hL, rfl⟩ := labelStep_eq_some_iff.1 h1
  obtain ⟨B, M, M', hb1, hB, hc₁, hM, rfl⟩ := labelStep_eq_some_iff.1 h2
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := labelAct_window hM
  -- `A = B ++ w ++ H`, `R = H ++ L'`
  obtain ⟨A₁, H, rfl, hA₁⟩ := exists_split_labels A (b.idx - 1 + b.arity) (by omega)
  have hlen : A₁.length = (B ++ w).length := by simp only [List.length_append]; omega
  rw [List.append_assoc, ← List.append_assoc B w R] at hc₁
  obtain ⟨rfl, hR⟩ := List.append_inj hc₁ hlen
  -- the two local actions with the fresh labels exchanged
  have hbw : b.labelAct k (w.map f) = some (w'.map f) := by
    have := labelAct_map hf b (k + 1) w
    rw [hfk1, hw'] at this
    exact this
  have haL : a.labelAct (k + 1) (L.map f) = some (L'.map f) := by
    have := labelAct_map hf a k L
    rw [hfk, hL] at this
    exact this
  refine ⟨(B ++ w' ++ H ++ L).map f, ?_, ?_⟩
  · have hs : b.labelStep k (B.map f ++ (w.map f ++ (H ++ L).map f)) =
        some (B.map f ++ (w'.map f ++ (H ++ L).map f)) :=
      labelStep_of_prefix hb1 (by rw [List.length_map]; exact hB)
        (by rw [labelAct_append (by rw [List.length_map]; exact hw), hbw]; rfl)
    rw [show (B ++ w ++ H ++ L).map f = B.map f ++ (w.map f ++ (H ++ L).map f) by
      simp only [List.map_append, List.append_assoc], hs]
    simp only [List.map_append, List.append_assoc]
  · have hs : (a.reindex (a.idx + b.coarity - b.arity)).labelStep (k + 1)
        ((B ++ w' ++ H).map f ++ L.map f) = some ((B ++ w' ++ H).map f ++ L'.map f) :=
      labelStep_of_prefix (by labomega) (by labomega) (by rw [labelAct_reindex]; exact haL)
    rw [← hR, show (B ++ w' ++ H ++ L).map f = (B ++ w' ++ H).map f ++ L.map f by
      simp only [List.map_append, List.append_assoc], hs]
    simp only [List.map_append, List.append_assoc]

/-- `b` acts below `a`: exchanging them (with `b` reindexed through `a`) and relabelling the cuts by `f`
gives the run of the exchanged pair. -/
theorem labelRun_comm_below {f : ℕ → ℕ} (hf : Function.Injective f) {k : ℕ} (hfk : f k = k + 1)
    (hfk1 : f (k + 1) = k) {a b : Letter} {c c' : List ℕ} (hab : a.idx + a.coarity ≤ b.idx)
    (h : labelRun [a, b] k c = some c') :
    labelRun [b.reindex (b.idx + a.arity - a.coarity), a] k (c.map f) = some (c'.map f) := by
  rw [labelRun_two_iff] at h
  rw [labelRun_two_iff]
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', ha1, hA, rfl, hL, rfl⟩ := labelStep_eq_some_iff.1 h1
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := labelAct_window hL
  obtain ⟨B, M, M', hb1, hB, hc₁, hM, rfl⟩ := labelStep_eq_some_iff.1 h2
  -- `B = A ++ w' ++ H`, `R = H ++ M`
  obtain ⟨B₁, H, rfl, hB₁⟩ := exists_split_labels B (a.idx - 1 + a.coarity) (by omega)
  have hlen : (A ++ w').length = B₁.length := by simp only [List.length_append]; omega
  rw [← List.append_assoc, List.append_assoc B₁ H M] at hc₁
  obtain ⟨hB₁eq, hR⟩ := List.append_inj hc₁ hlen
  subst hB₁eq
  have hbM : b.labelAct k (M.map f) = some (M'.map f) := by
    have := labelAct_map hf b (k + 1) M
    rw [hfk1, hM] at this
    exact this
  have haw : a.labelAct (k + 1) (w.map f) = some (w'.map f) := by
    have := labelAct_map hf a k w
    rw [hfk, hw'] at this
    exact this
  refine ⟨(A ++ w ++ H ++ M').map f, ?_, ?_⟩
  · have hs : (b.reindex (b.idx + a.arity - a.coarity)).labelStep k
        ((A ++ w ++ H).map f ++ M.map f) = some ((A ++ w ++ H).map f ++ M'.map f) :=
      labelStep_of_prefix (by labomega) (by labomega) (by rw [labelAct_reindex]; exact hbM)
    rw [hR, show (A ++ (w ++ (H ++ M))).map f = (A ++ w ++ H).map f ++ M.map f by
      simp only [List.map_append, List.append_assoc], hs]
    simp only [List.map_append, List.append_assoc]
  · have hs : a.labelStep (k + 1) (A.map f ++ (w.map f ++ (H ++ M').map f)) =
        some (A.map f ++ (w'.map f ++ (H ++ M').map f)) :=
      labelStep_of_prefix ha1 (by rw [List.length_map]; exact hA)
        (by rw [labelAct_append (by rw [List.length_map]; exact hw), haw]; rfl)
    rw [show (A ++ w ++ H ++ M').map f = A.map f ++ (w.map f ++ (H ++ M').map f) by
      simp only [List.map_append, List.append_assoc], hs]
    simp only [List.map_append, List.append_assoc]

end Comm

/-! ## 4. The base is invariant under disjoint-gadget commutations (`hinv`) -/

section Base

open Letter Word

/-- the transposition of two consecutive labels, packaged as the relabelling the exchange needs -/
theorem exists_swap_fun (k : ℕ) :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ f k = k + 1 ∧ f (k + 1) = k ∧ ∀ j, j ≠ k → j ≠ k + 1 → f j = j :=
  ⟨⇑(Equiv.swap k (k + 1)), (Equiv.swap k (k + 1)).injective, Equiv.swap_apply_left k (k + 1),
    Equiv.swap_apply_right k (k + 1), fun _ h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2⟩

/-- The reverse of a disjoint-gadget commutation step is a disjoint-gadget commutation step (the exchanged
pair is itself disjoint, exchanged back; the two reindexings cancel). -/
theorem IsCommStep.symm {W W' : Word} (h : IsCommStep W W') : IsCommStep W' W := by
  obtain ⟨X, Y, a, b, rfl, hpat⟩ := h
  rcases hpat with ⟨hab, rfl⟩ | ⟨hab, rfl⟩
  · refine ⟨X, Y, b, a.reindex (a.idx + b.coarity - b.arity), rfl, Or.inr ⟨?_, ?_⟩⟩
    · rw [idx_reindex]; omega
    · rw [idx_reindex, reindex_reindex,
        show a.idx + b.coarity - b.arity + b.arity - b.coarity = a.idx by omega, reindex_self]
  · refine ⟨X, Y, b.reindex (b.idx + a.arity - a.coarity), a, rfl, Or.inl ⟨?_, ?_⟩⟩
    · rw [idx_reindex]; omega
    · rw [idx_reindex, reindex_reindex,
        show b.idx + a.arity - a.coarity + a.coarity - a.arity = b.idx by omega, reindex_self]

/-- One direction of `hinv`: a disjoint-gadget commutation step preserves the standard-circle base.  The
labelled cut after the prefix `X` carries labels `< |X|`; exchanging the factor and applying the
transposition `|X| ↔ |X| + 1` (which fixes those labels and the labels `Y` allocates) gives the run of the
exchanged word, which ends at `[]` iff the original does. -/
theorem IsCommStep.isStandardCircleBase {W W' : Word} (h : IsCommStep W W') (hW : W.IsStandardCircleBase) :
    W'.IsStandardCircleBase := by
  obtain ⟨X, Y, a, b, rfl, hpat⟩ := h
  unfold Word.IsStandardCircleBase at hW ⊢
  rw [labelRun_append, labelRun_append, Option.bind_eq_some_iff] at hW
  obtain ⟨c₁, hXab, hY⟩ := hW
  rw [Option.bind_eq_some_iff] at hXab
  obtain ⟨c₀, hX, hab⟩ := hXab
  rw [Nat.zero_add] at hab
  have hlen2 : 0 + (X ++ [a, b]).length = X.length + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rw [hlen2] at hY
  have hc₀ : ∀ x ∈ c₀, x < X.length := by
    have := labelRun_lt (W := X) (by simp) hX
    simpa using this
  obtain ⟨f, hfinj, hfk, hfk1, hfix⟩ := exists_swap_fun X.length
  have hc₀f : c₀.map f = c₀ :=
    (List.map_congr_left fun x hx =>
      hfix x (by have := hc₀ x hx; omega) (by have := hc₀ x hx; omega)).trans (List.map_id c₀)
  have hYf : labelRun Y (X.length + 2) (c₁.map f) = some [] := by
    rw [labelRun_map hfinj Y (X.length + 2) c₁ (fun j hj => hfix j (by omega) (by omega)), hY]
    rfl
  rcases hpat with ⟨hab', rfl⟩ | ⟨hab', rfl⟩
  · have hmid := labelRun_comm_above hfinj hfk hfk1 hab' hab
    rw [hc₀f] at hmid
    rw [labelRun_append, labelRun_append]
    refine Option.bind_eq_some_iff.2 ⟨c₁.map f, Option.bind_eq_some_iff.2 ⟨c₀, hX, ?_⟩, ?_⟩
    · rw [Nat.zero_add]; exact hmid
    · have e : 0 + (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)]).length = X.length + 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [e]; exact hYf
  · have hmid := labelRun_comm_below hfinj hfk hfk1 hab' hab
    rw [hc₀f] at hmid
    rw [labelRun_append, labelRun_append]
    refine Option.bind_eq_some_iff.2 ⟨c₁.map f, Option.bind_eq_some_iff.2 ⟨c₀, hX, ?_⟩, ?_⟩
    · rw [Nat.zero_add]; exact hmid
    · have e : 0 + (X ++ [b.reindex (b.idx + a.arity - a.coarity), a]).length = X.length + 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [e]; exact hYf

/-- A disjoint-gadget commutation step preserves and reflects the standard-circle base. -/
theorem IsCommStep.isStandardCircleBase_iff {W W' : Word} (h : IsCommStep W W') :
    W.IsStandardCircleBase ↔ W'.IsStandardCircleBase :=
  ⟨h.isStandardCircleBase, h.symm.isStandardCircleBase⟩

/-- `hinv` on words: disjoint-gadget commutation in either direction. -/
theorem IsComm.isStandardCircleBase_iff {W W' : Word} (h : IsComm W W') :
    W.IsStandardCircleBase ↔ W'.IsStandardCircleBase := by
  rcases h with h | h
  · exact h.isStandardCircleBase_iff
  · exact h.isStandardCircleBase_iff.symm

/-- `hinv` on closed words: exactly the hypothesis of `Descends.of_principalChain` and
`SM.ng_finite_word_nonbase_descends`. -/
theorem IsComm.oword_isStandardCircleBase_iff {W W' : OWord} (h : IsComm W.letters W'.letters) :
    W.IsStandardCircleBase ↔ W'.IsStandardCircleBase :=
  IsComm.isStandardCircleBase_iff h

/-- The recorded obligation of the statement unit, in the exact shape of `hinv`. -/
theorem isStandardCircleBase_comm_invariant :
    ∀ W W' : OWord, IsComm W.letters W'.letters → (W.IsStandardCircleBase ↔ W'.IsStandardCircleBase) :=
  fun _ _ h => IsComm.oword_isStandardCircleBase_iff h

/-- "Thus every nonbase front has a finite principal chain to a front of smaller s"
(AXIOM_REGISTRY.md:105-106), unconditionally from a principal chain (standard axioms only). -/
theorem Descends.of_principalChain' {W : OWord}
    (hc : PrincipalChain OWord.sCountSyn OWord.IsStandardCircleBase W) (hW : ¬ W.IsStandardCircleBase) :
    Descends OWord.sCountSyn W :=
  Descends.of_principalChain isStandardCircleBase_comm_invariant hc hW

end Base

/-! ### Sanity checks (by `decide`): the two runs of a commuted pair differ by the label transposition,
and the base is preserved -/

/-- `l₁ l₃` and its commutation `l₁ l₁` (`b = l 3 _` acts below `a = l 1 _`: `b` is reindexed by `−2`) -/
example : Word.labelRun [.l 1 true, .l 3 false] 0 [] = some [0, 0, 1, 1] ∧
    Word.labelRun [.l 1 false, .l 1 true] 0 [] = some [1, 1, 0, 0] := by decide
/-- both closings are unions of standard circles -/
example : Word.IsStandardCircleBase [.l 1 true, .l 3 false, .r 3, .r 1] ∧
    Word.IsStandardCircleBase [.l 1 false, .l 1 true, .r 3, .r 1] := by decide
/-- a right cusp commuted past a left cusp above it (`r 3` then `l 1`: `r` is reindexed by `+2`) -/
example : Word.labelRun [.l 1 true, .l 3 false, .r 3, .l 1 true, .r 1, .r 1] 0 [] = some [] ∧
    Word.labelRun [.l 1 true, .l 3 false, .l 1 true, .r 5, .r 1, .r 1] 0 [] = some [] := by decide

end SM.FrontWord

namespace SM

open SM.FrontWord

/-! ## 5. The unconditional projection for consumers -/

/-- The block's conclusion for consumers, unconditional: every nonbase closed oriented word has a finite
principal chain to a word of smaller `s` (`SM.ng_finite_word_nonbase_descends` with `hinv` supplied by
`isStandardCircleBase_comm_invariant`).  Consumes `SM.ng_finite_word`, as the conditional theorem does. -/
theorem ng_finite_word_nonbase_descends' :
    ∀ W : OWord, ¬ W.IsStandardCircleBase → Descends OWord.sCountSyn W :=
  ng_finite_word_nonbase_descends isStandardCircleBase_comm_invariant

end SM
