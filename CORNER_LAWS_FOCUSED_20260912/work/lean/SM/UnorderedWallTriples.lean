import SM.NamedWallRelabel

/-! Reordering an unordered T/C support changes some real observables by
a minus sign. The exact local product condition is unchanged by that sign. -/

namespace SM

theorem three_support_predicate {α : Type*} [DecidableEq α] (R : α → α → α → Prop)
    (hcyc : ∀ a b c, R b c a ↔ R a b c) (hswap : ∀ a b c, R a c b ↔ R a b c)
    {a b c i j k : α} (he : ({i, j, k} : Finset α) = {a, b, c})
    (hc : ({a, b, c} : Finset α).card = 3) (h : R a b c) : R i j k := by
  have hi : i = a ∨ i = b ∨ i = c := by
    have hm : i ∈ ({a, b, c} : Finset α) := he ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hj : j = a ∨ j = b ∨ j = c := by
    have hm : j ∈ ({a, b, c} : Finset α) := he ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hk : k = a ∨ k = b ∨ k = c := by
    have hm : k ∈ ({a, b, c} : Finset α) := he ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hd := Finset.card_triple_eq_three_iff.mp (he.symm ▸ hc)
  have h₁ := (hcyc a b c).mpr h
  have h₂ := (hcyc b c a).mpr h₁
  have h₃ := (hswap a b c).mpr h
  have h₄ := (hcyc a c b).mpr h₃
  have h₅ := (hcyc c b a).mpr h₄
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl <;>
    first | assumption | exact (hd.1 rfl).elim | exact (hd.2.1 rfl).elim | exact (hd.2.2 rfl).elim

namespace WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

theorem signChanges_neg (φ : LabelledTuple n → ℝ) :
    g.SignChanges (fun P => -φ P) ↔ g.SignChanges φ := by
  simp only [SignChanges, neg_mul_neg]

theorem signChanges_sub_swap (φ ψ : LabelledTuple n → ℝ) :
    g.SignChanges (fun P => ψ P - φ P) ↔ g.SignChanges (fun P => φ P - ψ P) := by
  have he : (fun P => ψ P - φ P) = (fun P => -(φ P - ψ P)) := by
    funext P
    ring
  rw [he, g.signChanges_neg]

theorem tripleAt_swap_last (e f k : ZMod n) :
    g.TripleAt e k f ↔ g.TripleAt e f k := by
  have hs : ({e, k, f} : Finset (ZMod n)) = {e, f, k} := by ext i; simp [or_comm, or_left_comm]
  simp only [TripleAt, hs, g.signChanges_sub_swap]
  tauto

theorem tripleAt_cyclic (e f k : ZMod n) :
    g.TripleAt f k e ↔ g.TripleAt e f k := by
  have hs : ({f, k, e} : Finset (ZMod n)) = {e, f, k} := by ext i; simp [or_comm, or_left_comm]
  simp only [TripleAt, hs, g.signChanges_sub_swap]
  tauto

theorem pureCutAt_swap_last (i j k : ZMod n) :
    g.PureCutAt i k j ↔ g.PureCutAt i j k := by
  have hs : ({i, k, j} : Finset (ZMod n)) = {i, j, k} := by ext x; simp [or_comm, or_left_comm]
  have hchi : (fun P : LabelledTuple n => (chi P i k j : ℝ)) =
      (fun P => -(chi P i j k : ℝ)) := by
    funext P
    rw [chi_swap_last, SignType.coe_neg]
  unfold PureCutAt
  rw [hs, hchi, g.signChanges_neg]

theorem pureCutAt_cyclic (i j k : ZMod n) :
    g.PureCutAt j k i ↔ g.PureCutAt i j k := by
  have hs : ({j, k, i} : Finset (ZMod n)) = {i, j, k} := by ext x; simp [or_comm, or_left_comm]
  simp only [PureCutAt, hs, chi_cyclic]

theorem tripleAt_of_support_eq {e f k i j l : ZMod n}
    (he : ({i, j, l} : Finset (ZMod n)) = {e, f, k}) (h : g.TripleAt e f k) :
    g.TripleAt i j l := by
  have hm : ({e, f, k} : Finset (ZMod n)) ∈ g.concurrences := by rw [h.2.1]; simp
  have hc := ((g.mem_concurrences _).mp hm).1
  exact three_support_predicate g.TripleAt g.tripleAt_cyclic g.tripleAt_swap_last he hc h

theorem tripleAt_support_iff {e f k i j l : ZMod n}
    (he : ({i, j, l} : Finset (ZMod n)) = {e, f, k}) :
    g.TripleAt i j l ↔ g.TripleAt e f k :=
  ⟨g.tripleAt_of_support_eq he.symm, g.tripleAt_of_support_eq he⟩

theorem pureCutAt_of_support_eq {e f k i j l : ZMod n}
    (he : ({i, j, l} : Finset (ZMod n)) = {e, f, k}) (h : g.PureCutAt e f k) :
    g.PureCutAt i j l := by
  have hc := (singlePointTriple_data h.2.1).1
  exact three_support_predicate g.PureCutAt g.pureCutAt_cyclic g.pureCutAt_swap_last he hc h

theorem pureCutAt_support_iff {e f k i j l : ZMod n}
    (he : ({i, j, l} : Finset (ZMod n)) = {e, f, k}) :
    g.PureCutAt i j l ↔ g.PureCutAt e f k :=
  ⟨g.pureCutAt_of_support_eq he.symm, g.pureCutAt_of_support_eq he⟩

end WallGerm
end SM
