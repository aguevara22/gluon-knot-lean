import SM.PolynomialBlock

/-! # mp:stack (sm-3:1494-1536): ordered stacked blocks, including split unions

The fifth row of the polynomial block.  `SM/PolynomialBlock.lean` holds §0-§5 of
work/drafts/polyblock/Skeleton_FINAL.lean (the record-level based order, the induction principles,
lp:core, rp:record-polynomial, lc:presentations, lp:split-circle) and four of the five row theorems;
this module is §6 of that skeleton with the proofs of its five units (U1-U5, assembled into
work/drafts/polyblock/Stack_Assembled_full.lean) and the row bundle `StackData` / `stack`
(structure and statement verbatim from work/drafts/Stack_statement.lean).

Design (PLAN_FINAL.md §6).  `skein_induction_based` with the predicate
`Φ D B := ∀ q blk hblk, BlockOrdered D blk → B.BlockCompatible blk → P D = δ^{q−1} ∏ P (D_i)`,
started at a block-compatible based order (`exists_blockCompatible_rbasing`), so that every bad
occurrence is internal to its block (`isBad_internal`; "All between-block crossings are first
encountered under", sm-3:1515).  Init (`stack_init`): the block restrictions of an UNDER-first
diagram are UNDER-first (`restrict_underFirst`).  Step (`stack_step`): the switch is the same switch
in its block restriction and invisible to the other blocks (`blockRestrict_switch_of_internal/external`);
the smoothing carries the blocks (`smoothBlock`, `blocks_of_smoothing`) and its block restrictions are
the smoothing of the old block restriction (`restrictSmoothIso`) resp. unchanged
(`restrictSmoothDisjointIso`), read through `restrictRecordIso`, `RecordIso.restrict` and
lc:presentations; `solvedR_of_skein` on `D` and on the block restriction, `solvedR_mul_left` factors
the common terms.

Sections: 6.1 record-level block order and block-compatible based orders (bad crossings are
internal); 6.2 the blocks of the smoothing; 6.3 restriction versus smoothing at the record level
(the two permutation lemmas `firstReturn_firstReturn` / `firstReturn_mul_swap` and the record isos);
6.4 diagram-level block bookkeeping; 6.5 initialization, step, assembly; then the row bundle.

Main declaration: `SM.stack`. -/

namespace SM

open SM.Link

/-! ## §6. mp:stack (sm-3:1494-1536)

Design (PLAN_FINAL.md §6).  `skein_induction_based` with the predicate
`Φ D B := ∀ q blk hblk, BlockOrdered D blk → B.BlockCompatible blk → P D = δ^{q−1} ∏ P (D_i)`,
started at a block-compatible based order (`exists_blockCompatible_rbasing`), so that every bad
occurrence is internal to its block (`isBad_internal`; "All between-block crossings are first
encountered under", sm-3:1515).  Init (`stack_init`): the block restrictions of an UNDER-first
diagram are UNDER-first (`restrict_underFirst`, diagram level: same basepoints, same traversal
coordinates).  Step (`stack_step`): the switch is the same switch in its block restriction and
invisible to the other blocks (`blockRestrict_switch_of_internal/external`); the smoothing carries
the blocks (`smoothBlock`, `blocks_of_smoothing`) and its block restrictions are the smoothing of the
old block restriction (`restrictSmoothIso`) resp. unchanged (`restrictSmoothDisjointIso`), read
through `restrictRecordIso`, `RecordIso.restrict` and lc:presentations; `solvedR_of_skein` on `D`
and on the block restriction, `solvedR_mul_left` factors the common terms.  The record-level
commutations are stated with the target block `B'` characterised by two hypotheses (graft from
Skeleton A), so that they are provable independently of the block bookkeeping. -/

open SM.Link in
/-- The restriction of `D` to the components of block `i` (the fibre of `blk` over `i`)
(copied verbatim from work/drafts/Stack_statement.lean). -/
noncomputable def blockRestrict (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) : Diagram :=
  D.restrict (Finset.univ.filter (fun c => blk c = i))
    (by obtain ⟨c, hc⟩ := hblk i; exact ⟨c, by simp [hc]⟩)

/-- "at every crossing between different blocks the smaller-index block is under the larger one"
(copied verbatim). -/
def BlockOrdered (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) : Prop :=
  ∀ (x : D.Γ.Crossing) (s t : D.Γ.Strand), s ∈ x.val → t ∈ x.val → blk s.1 < blk t.1 →
    D.underStrand x = s

/-- The component set of block `i`. -/
abbrev blockSet (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (i : Fin q) : Finset (Fin D.Γ.c) :=
  Finset.univ.filter (fun c => blk c = i)

theorem mem_blockSet_iff (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (i : Fin q) (c : Fin D.Γ.c) :
    c ∈ blockSet D blk i ↔ blk c = i := by
  simp [blockSet]

theorem blockSet_nonempty (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) : (blockSet D blk i).Nonempty := by
  obtain ⟨c, hc⟩ := hblk i; exact ⟨c, by simp [blockSet, hc]⟩

theorem blockRestrict_eq (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) :
    blockRestrict D blk hblk i = D.restrict (blockSet D blk i) (blockSet_nonempty D blk hblk i) := rfl

/-! ### 6.1 Record level: block order, block-compatible based orders, bad crossings are internal
("Order components block by block", sm-3:1514) -/

namespace Link.Record

variable (ρ : Record)

/-- Record-level block order: at a crossing between different blocks the occurrence on the smaller
block is the under occurrence. -/
def RBlockOrdered {q : ℕ} (β : ρ.comps → Fin q) : Prop :=
  ∀ v, β (ρ.comp v) < β (ρ.comp (ρ.pair v)) → ρ.isOver v = false

/-- A based order compatible with a block function: earlier blocks come first (exists: rank
`β c * card comps + equivFin c`). -/
def RBasing.BlockCompatible {ρ : Record} {q : ℕ} (B : RBasing ρ) (β : ρ.comps → Fin q) : Prop :=
  ∀ c c', β c < β c' → B.rank c < B.rank c'

theorem exists_blockCompatible_rbasing {q : ℕ} (β : ρ.comps → Fin q) :
    ∃ B : RBasing ρ, B.BlockCompatible β := by
  set N := Fintype.card ρ.comps with hN
  let e := Fintype.equivFin ρ.comps
  have hlt : ∀ c c', β c < β c' → (β c).val * N + (e c).val < (β c').val * N + (e c').val := by
    intro c c' h
    have h1 : (β c).val * N + (e c).val < (β c).val * N + N := Nat.add_lt_add_left (e c).isLt _
    have h2 : (β c).val * N + N ≤ (β c').val * N := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right N h
    exact lt_of_lt_of_le h1 (h2.trans (Nat.le_add_right _ _))
  refine ⟨{ (RBasing.default ρ) with
    rank := fun c => (β c).val * N + (e c).val
    rank_inj := ?_ }, fun c c' h => hlt c c' h⟩
  intro c c' h
  rcases lt_trichotomy (β c) (β c') with hb | hb | hb
  · exact absurd h (ne_of_lt (hlt c c' hb))
  · have h' : (β c).val * N + (e c).val = (β c).val * N + (e c').val := by
      have : (β c').val = (β c).val := by rw [hb]
      simpa [this] using h
    exact e.injective (Fin.ext (Nat.add_left_cancel h'))
  · exact absurd h (ne_of_gt (hlt c' c hb))

/-- "All between-block crossings are first encountered under" (sm-3:1515): a bad occurrence of a
block-compatible based order of a block-ordered record is internal to its block. -/
theorem RBasing.isBad_internal {ρ : Record} {q : ℕ} {β : ρ.comps → Fin q} (hβ : ρ.RBlockOrdered β)
    {B : RBasing ρ} (hB : B.BlockCompatible β) {v : ρ.M} (hv : B.IsBad v) :
    β (ρ.comp v) = β (ρ.comp (ρ.pair v)) := by
  rcases lt_trichotomy (β (ρ.comp v)) (β (ρ.comp (ρ.pair v))) with h | h | h
  · have := hβ v h
    rw [hv.1] at this
    exact absurd this (by decide)
  · exact h
  · have hr : B.rank (ρ.comp (ρ.pair v)) < B.rank (ρ.comp v) := hB _ _ h
    have hk : B.key (ρ.pair v) < B.key v := by
      unfold RBasing.key
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hr
    exact absurd (lt_trans hk hv.2) (lt_irrefl _)

/-! ### 6.2 Record level: the blocks of the smoothing ("Every new component inherits the same block
as the strands smoothed", sm-3:1527) -/

section U2Beta
open Equiv

/-- One step of the reconnected successor keeps any block function that agrees on the two circles
of the smoothed crossing. -/
theorem beta_comp_reconnect_eq {γ : Sort*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) (u : ρ.M) :
    β (ρ.comp (ρ.reconnect v u)) = β (ρ.comp u) := by
  by_cases h1 : u = v
  · subst h1; rw [reconnect_apply_self, ρ.succ_comp, hv]
  by_cases h2 : u = ρ.pair v
  · subst h2; rw [reconnect_apply_pair, ρ.succ_comp, hv]
  · rw [ρ.reconnect_apply_of_ne v h1 h2, ρ.succ_comp]

theorem beta_comp_reconnect_pow_eq {γ : Sort*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) (u : ρ.M) (n : ℕ) :
    β (ρ.comp (((ρ.reconnect v) ^ n) u)) = β (ρ.comp u) := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih => rw [pow_succ', Perm.mul_apply, ρ.beta_comp_reconnect_eq β v hv, ih]

end U2Beta

/-- Any function of the circles that agrees on the two circles of the smoothed crossing is constant
along the cycles of the reconnected successor `s₁ = s ∘ swap v (τ v)`: one step is
`reconnect v u = succ (swap v (pair v) u)` (`u = v ↦ comp (succ (pair v)) = comp (pair v)`,
`u = pair v` symmetric, otherwise `comp (succ u) = comp u`), then `zpow` induction on
`Perm.SameCycle` (as `sameCycle_map_iff`). -/
theorem beta_comp_eq_of_reconnect_sameCycle {γ : Sort*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) {u w : ρ.M}
    (h : (ρ.reconnect v).SameCycle u w) : β (ρ.comp u) = β (ρ.comp w) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn, ρ.beta_comp_reconnect_pow_eq β v hv]

/-- The block function of the smoothing: a cycle of `s₁` inherits the block of any occurrence it
carries (well defined by `beta_comp_eq_of_reconnect_sameCycle`), a crossing-free circle keeps its
block.  Transparent `Quotient.lift`: both computation rules are `rfl`. -/
def smoothBlock {γ : Type*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) : (ρ.smooth v).comps → γ :=
  Sum.elim
    (Quotient.lift (fun u : ρ.M => β (ρ.comp u))
      (fun _ _ h => ρ.beta_comp_eq_of_reconnect_sameCycle β v hv h))
    (fun f => β f.1)

@[simp] theorem smoothBlock_inl {γ : Type*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) (u : ρ.M) :
    ρ.smoothBlock β v hv (Sum.inl (Quotient.mk _ u)) = β (ρ.comp u) := rfl

@[simp] theorem smoothBlock_inr {γ : Type*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) (f : ρ.FreeComp) :
    ρ.smoothBlock β v hv (Sum.inr f) = β f.1 := rfl

end Link.Record

/-! ### 6.3 Record level: restriction versus smoothing (sm-3:1528-1531 "The restriction of the
smoothed diagram in that block is exactly the oriented smoothing of the old block restriction; the
other restrictions do not change") -/

namespace Link

/-- U1 helper: the first return is `f ^ n` once `n > 0` is a `p`-time with no earlier positive
`p`-time (`returnTime_eq_iff` packaged for the subtype value). -/
theorem firstReturn_val_eq_of_pow {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop)
    [DecidablePred p] (m : {m // p m}) {n : ℕ} (hn : 0 < n) (hp : p ((f ^ n) m.1))
    (hmin : ∀ j, 0 < j → j < n → ¬ p ((f ^ j) m.1)) :
    (firstReturn f p m).1 = (f ^ n) m.1 := by
  have : returnTime f p m.1 m.2 = n :=
    (returnTime_eq_iff f p m.1 m.2).mpr ⟨⟨hn, hp⟩, fun j hj hj' => hmin j hj'.1 hj hj'.2⟩
  rw [firstReturn_apply, this]

/-- U1 helper: two equivalent predicates have the same first return (needed by the record isos
to rewrite `RestrictKeep`/`SmoothKeep` under a `firstReturn`). -/
theorem firstReturn_congr_pred {α : Type*} [Fintype α] (f : Equiv.Perm α) (p p' : α → Prop)
    [DecidablePred p] [DecidablePred p'] (h : ∀ m, p m ↔ p' m) (m : {m // p m}) :
    (firstReturn f p m).1 = (firstReturn f p' ⟨m.1, (h _).mp m.2⟩).1 := by
  have hT : returnTime f p m.1 m.2 = returnTime f p' m.1 ((h _).mp m.2) := by
    rw [returnTime_eq_iff]
    refine ⟨⟨returnTime_pos f p' _ _, (h _).mpr (returnTime_spec f p' _ _)⟩, ?_⟩
    rintro j hj ⟨hj0, hpj⟩
    exact returnTime_min f p' _ _ hj0 hj ((h _).mp hpj)
  show (f ^ returnTime f p m.1 m.2) m.1 = (f ^ returnTime f p' m.1 ((h _).mp m.2)) m.1
  rw [hT]

/-- U1 helper: the iterates of `f * swap a b` agree with those of `f` as long as the `f`-orbit
avoids `a` and `b`. -/
theorem mul_swap_pow_apply_of_forall_ne {α : Type*} [DecidableEq α] (f : Equiv.Perm α) (a b u : α)
    (n : ℕ) (h : ∀ j, j < n → (f ^ j) u ≠ a ∧ (f ^ j) u ≠ b) :
    ((f * Equiv.swap a b) ^ n) u = (f ^ n) u := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' := h n (by omega)
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [ih (fun j hj => h j (by omega)), Equiv.swap_apply_of_ne_of_ne h'.1 h'.2]

/-- U1 helper: the `k`-th power of `firstReturn f p` is an `f`-power `f ^ n` of the starting
point (with `n = 0 ↔ k = 0`), and every `p`-point strictly between (along the orbit segment
`0 < j < n`) is an earlier power `firstReturn f p ^ i`, `0 < i < k`. -/
theorem firstReturn_pow_val_spec {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop)
    [DecidablePred p] (x : {m // p m}) (k : ℕ) :
    ∃ n : ℕ, (n = 0 ↔ k = 0) ∧ ((firstReturn f p ^ k) x).1 = (f ^ n) x.1 ∧
      ∀ j, 0 < j → j < n → p ((f ^ j) x.1) →
        ∃ i, 0 < i ∧ i < k ∧ ((firstReturn f p ^ i) x).1 = (f ^ j) x.1 := by
  induction k with
  | zero => exact ⟨0, by simp, by simp, fun j hj0 hj _ => absurd hj (by omega)⟩
  | succ k ih =>
    obtain ⟨n, hn0, hn, hmin⟩ := ih
    set y : {m // p m} := (firstReturn f p ^ k) x with hy
    set r : ℕ := returnTime f p y.1 y.2 with hr
    have hrpos : 0 < r := returnTime_pos f p y.1 y.2
    have h1 : ((firstReturn f p ^ (k + 1)) x).1 = (f ^ r) y.1 := by
      rw [pow_succ', Equiv.Perm.mul_apply]; rfl
    refine ⟨n + r, ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩, ?_, ?_⟩
    · rw [h1, hn, ← Equiv.Perm.mul_apply, ← pow_add, add_comm]
    · intro j hj0 hj hpj
      rcases lt_trichotomy j n with hlt | heq | hgt
      · obtain ⟨i, hi0, hik, hi⟩ := hmin j hj0 hlt hpj
        exact ⟨i, hi0, by omega, hi⟩
      · subst heq
        have hk : 0 < k := by
          rcases Nat.eq_zero_or_pos k with hk | hk
          · exact absurd (hn0.mpr hk) (by omega)
          · exact hk
        exact ⟨k, hk, by omega, hn⟩
      · exfalso
        have hsplit : (f ^ j) x.1 = (f ^ (j - n)) y.1 := by
          rw [hn, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hgt.le]
        exact returnTime_min f p y.1 y.2 (by omega) (by omega) (hsplit ▸ hpj)

/-- U1 helper: the pointwise `u = a` case of `firstReturn_mul_swap`: from `a`, the permutation
`f * swap a b` first steps to `f b` and then follows `f`, so its first return is that of `b`. -/
theorem firstReturn_mul_swap_apply_left {α : Type*} [Fintype α] [DecidableEq α] (f : Equiv.Perm α)
    (p : α → Prop) [DecidablePred p] (a b : α) (ha : p a) (hb : p b) :
    (firstReturn (f * Equiv.swap a b) p ⟨a, ha⟩).1 = (firstReturn f p ⟨b, hb⟩).1 := by
  have hN : 0 < returnTime f p b hb := returnTime_pos f p b hb
  have avoid : ∀ j, 0 < j → j < returnTime f p b hb → (f ^ j) b ≠ a ∧ (f ^ j) b ≠ b :=
    fun j hj0 hj => ⟨fun h => returnTime_min f p b hb hj0 hj (by rw [h]; exact ha),
      fun h => returnTime_min f p b hb hj0 hj (by rw [h]; exact hb)⟩
  have hiter : ∀ i, i + 1 ≤ returnTime f p b hb →
      ((f * Equiv.swap a b) ^ (i + 1)) a = (f ^ (i + 1)) b := by
    intro i hi
    rw [pow_succ (f * Equiv.swap a b) i, Equiv.Perm.mul_apply, mul_swap_apply_left,
      pow_succ f i, Equiv.Perm.mul_apply]
    exact mul_swap_pow_apply_of_forall_ne f a b (f b) i fun j hj => by
      have := avoid (j + 1) (by omega) (by omega)
      rwa [pow_succ, Equiv.Perm.mul_apply] at this
  obtain ⟨k, hk⟩ : ∃ k, returnTime f p b hb = k + 1 := ⟨returnTime f p b hb - 1, by omega⟩
  have hR : (firstReturn f p ⟨b, hb⟩).1 = (f ^ (k + 1)) b := by
    show (f ^ returnTime f p b hb) b = _
    rw [hk]
  have hL : (firstReturn (f * Equiv.swap a b) p ⟨a, ha⟩).1 = ((f * Equiv.swap a b) ^ (k + 1)) a := by
    apply firstReturn_val_eq_of_pow (f * Equiv.swap a b) p ⟨a, ha⟩ (Nat.succ_pos k)
    · show p (((f * Equiv.swap a b) ^ (k + 1)) a)
      rw [hiter k (by omega)]
      have := returnTime_spec f p b hb
      rwa [hk] at this
    · intro j hj0 hj
      show ¬ p (((f * Equiv.swap a b) ^ j) a)
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [hiter i (by omega)]
      exact returnTime_min f p b hb hj0 (by omega)
  rw [hL, hR]
  exact hiter k (by omega)

/-- First return to `p` and then to `q` is first return to `p ∧ q`.  Both sides are `(f ^ n) m` for
the least `n > 0` with `p ∧ q`; the `k`-th power of `firstReturn f p` is `f ^ (sum of return times)`
(`firstReturn_pow_of_pow`, `firstReturn_apply`, `returnTime_spec`, `returnTime_min`); minimality on
both sides via `returnTime_eq_iff`. -/
theorem firstReturn_firstReturn {α : Type*} [Fintype α] (f : Equiv.Perm α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (m : {m : {m // p m} // q m.1}) :
    ((firstReturn (firstReturn f p) (fun m => q m.1)) m).1.1 =
      ((firstReturn f (fun m => p m ∧ q m)) ⟨m.1.1, m.1.2, m.2⟩).1 := by
  set F : Equiv.Perm {m // p m} := firstReturn f p with hF
  set K : ℕ := returnTime F (fun m => q m.1) m.1 m.2 with hK
  have hKpos : 0 < K := returnTime_pos F (fun m => q m.1) m.1 m.2
  obtain ⟨n, hn0, hn, hmin⟩ := firstReturn_pow_val_spec f p m.1 K
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (hn0.mp h) (by omega)
    · exact h
  have hq : q ((F ^ K) m.1).1 := returnTime_spec F (fun m => q m.1) m.1 m.2
  have hRT : returnTime f (fun m => p m ∧ q m) m.1.1 ⟨m.1.2, m.2⟩ = n := by
    rw [returnTime_eq_iff]
    refine ⟨⟨hnpos, ?_⟩, ?_⟩
    · show p ((f ^ n) m.1.1) ∧ q ((f ^ n) m.1.1)
      rw [← hn]
      exact ⟨((F ^ K) m.1).2, hq⟩
    · rintro j hj ⟨hj0, hpj, hqj⟩
      obtain ⟨i, hi0, hiK, hi⟩ := hmin j hj0 hj hpj
      apply returnTime_min F (fun m => q m.1) m.1 m.2 hi0 hiK
      show q ((F ^ i) m.1).1
      rw [hi]
      exact hqj
  show ((F ^ K) m.1).1 = (f ^ returnTime f (fun m => p m ∧ q m) m.1.1 ⟨m.1.2, m.2⟩) m.1.1
  rw [hRT, hn]

/-- First return commutes with a transposition of two `p`-points.  Pointwise: for `u ∉ {a, b}`,
`(f * swap a b)^n u = f^n u` while no intermediate point is a `p`-point (`a, b` are `p`-points), so
the return times agree (`mul_swap_apply_of_ne_of_ne`); for `u = a`: `(f * swap a b) a = f b`, then
as before from `f b`, matching `firstReturn f p ⟨b⟩`; symmetric for `b`. -/
theorem firstReturn_mul_swap {α : Type*} [Fintype α] [DecidableEq α] (f : Equiv.Perm α)
    (p : α → Prop) [DecidablePred p] (a b : α) (ha : p a) (hb : p b) :
    firstReturn (f * Equiv.swap a b) p =
      firstReturn f p * Equiv.swap (⟨a, ha⟩ : {m // p m}) ⟨b, hb⟩ := by
  refine Equiv.ext fun u => Subtype.ext ?_
  by_cases hua : u = ⟨a, ha⟩
  · subst hua
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact firstReturn_mul_swap_apply_left f p a b ha hb
  by_cases hub : u = ⟨b, hb⟩
  · subst hub
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_comm]
    exact firstReturn_mul_swap_apply_left f p b a hb ha
  -- `u ∉ {a, b}`: the two orbits agree up to the first return of `u` along `f`
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hua hub]
  have hu1 : u.1 ≠ a := fun h => hua (Subtype.ext h)
  have hu2 : u.1 ≠ b := fun h => hub (Subtype.ext h)
  have avoid : ∀ j, j < returnTime f p u.1 u.2 → (f ^ j) u.1 ≠ a ∧ (f ^ j) u.1 ≠ b := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, Equiv.Perm.one_apply]
      exact ⟨hu1, hu2⟩
    · exact ⟨fun h => returnTime_min f p u.1 u.2 hj0 hj (by rw [h]; exact ha),
        fun h => returnTime_min f p u.1 u.2 hj0 hj (by rw [h]; exact hb)⟩
  rw [firstReturn_apply f p u, ← mul_swap_pow_apply_of_forall_ne f a b u.1 _ avoid]
  apply firstReturn_val_eq_of_pow (f * Equiv.swap a b) p u (returnTime_pos f p u.1 u.2)
  · rw [mul_swap_pow_apply_of_forall_ne f a b u.1 _ avoid]
    exact returnTime_spec f p u.1 u.2
  · intro j hj0 hj
    rw [mul_swap_pow_apply_of_forall_ne f a b u.1 j (fun i hi => avoid i (by omega))]
    exact returnTime_min f p u.1 u.2 hj0 hj

section U2Perm
open Equiv

/-- The value of a first return depends only on the predicate up to `↔` and on the powers of the
permutation along the orbit of the starting point (decidability instances by unification). -/
theorem firstReturn_val_congr {α : Type*} [Fintype α] (f g : Perm α) (p p' : α → Prop)
    {_ : DecidablePred p} {_ : DecidablePred p'} (hp : ∀ m, p m ↔ p' m) (m : {m // p m})
    (hfg : ∀ n : ℕ, (f ^ n) m.1 = (g ^ n) m.1) :
    (firstReturn f p m).1 = (firstReturn g p' ⟨m.1, (hp _).mp m.2⟩).1 := by
  rw [firstReturn_apply, firstReturn_apply]
  have : returnTime f p m.1 m.2 = returnTime g p' m.1 ((hp _).mp m.2) := by
    rw [returnTime_eq_iff]
    refine ⟨⟨returnTime_pos _ _ _ _, ?_⟩, ?_⟩
    · rw [hfg, hp]; exact returnTime_spec _ _ _ _
    · rintro j hj ⟨hj0, hpj⟩
      rw [hfg, hp] at hpj
      exact returnTime_min _ _ _ _ hj0 hj hpj
  rw [this, hfg]

end U2Perm

namespace Record

variable (ρ : Record)

section U2Record
open Equiv

/-- Away from the two circles of the smoothed crossing the reconnected successor is the old one,
power by power. -/
theorem reconnect_pow_eq_succ_pow (x u : ρ.M) (h1 : ρ.comp u ≠ ρ.comp x)
    (h2 : ρ.comp u ≠ ρ.comp (ρ.pair x)) (n : ℕ) :
    ((ρ.reconnect x) ^ n) u = (ρ.succ ^ n) u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
    apply ρ.reconnect_apply_of_ne
    · intro hc; exact h1 (by rw [← hc, ρ.comp_pow])
    · intro hc; exact h2 (by rw [← hc, ρ.comp_pow])

/-- On the other circles the `s₁`-cycles are the old circles. -/
theorem reconnect_sameCycle_iff_of_comp_ne (x u : ρ.M) (h1 : ρ.comp u ≠ ρ.comp x)
    (h2 : ρ.comp u ≠ ρ.comp (ρ.pair x)) (w : ρ.M) :
    (ρ.reconnect x).SameCycle u w ↔ ρ.comp u = ρ.comp w := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn, ρ.reconnect_pow_eq_succ_pow x u h1 h2, ρ.comp_pow]
  · intro h
    obtain ⟨n, hn⟩ := (ρ.succ_cycle u w h).exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ρ.reconnect_pow_eq_succ_pow x u h1 h2, hn]⟩

/-- An occurrence on one of the two circles of the smoothed crossing lies on the `s₁`-cycle of `x`
or on that of `τ x`. -/
theorem reconnect_sameCycle_self_or_pair (x u : ρ.M)
    (h : ρ.comp u = ρ.comp x ∨ ρ.comp u = ρ.comp (ρ.pair x)) :
    (ρ.reconnect x).SameCycle u x ∨ (ρ.reconnect x).SameCycle u (ρ.pair x) := by
  rcases h with h | h
  · exact ρ.reconnect_sameCycle_or x u h
  · have := ρ.reconnect_sameCycle_or (ρ.pair x) u h
    rw [ρ.reconnect_pair, ρ.pair_invol] at this
    exact this.symm

theorem reconnect_sameCycle_out (x u : ρ.M) :
    (ρ.reconnect x).SameCycle (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect x)) u).out u :=
  Quotient.mk_out (s := Perm.SameCycle.setoid (ρ.reconnect x)) u

/-! #### Shared bookkeeping for the restriction of a smoothing -/

section RestrictSmooth

variable (x : ρ.M) (B : Finset ρ.comps) (B' : Finset (ρ.smooth x).comps)
  (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)

include hB' in
/-- The kept occurrences of the restricted smoothing are the kept occurrences of `ρ`. -/
theorem smooth_restrictKeep_iff (w : (ρ.smooth x).M) :
    (ρ.smooth x).RestrictKeep B' w ↔ ρ.RestrictKeep B w.1 := by
  show (Sum.inl (Quotient.mk _ w.1) ∈ B' ∧ Sum.inl (Quotient.mk _ (ρ.pair w.1)) ∈ B') ↔ _
  rw [hB', hB']
  exact Iff.rfl

include hB' in
theorem mem_of_inl_mem {q : Quotient (Perm.SameCycle.setoid (ρ.reconnect x))}
    (h : (Sum.inl q : (ρ.smooth x).comps) ∈ B') : ρ.comp q.out ∈ B :=
  (hB' _).mp (by rw [Quotient.out_eq]; exact h)

end RestrictSmooth

/-! #### External crossing: restriction of the smoothing = old restriction -/

section Disjoint

variable (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B) (hx' : ρ.comp (ρ.pair x) ∉ B)

include hx hx' in
theorem comp_ne_of_mem_disjoint {u : ρ.M} (hu : ρ.comp u ∈ B) :
    ρ.comp u ≠ ρ.comp x ∧ ρ.comp u ≠ ρ.comp (ρ.pair x) :=
  ⟨fun h => hx (h ▸ hu), fun h => hx' (h ▸ hu)⟩

include hx hx' in
theorem smoothKeep_of_comp_mem_disjoint {u : ρ.M} (hu : ρ.comp u ∈ B) : ρ.SmoothKeep x u := by
  rw [smoothKeep_iff]
  exact ⟨fun h => hx (h ▸ hu), fun h => hx' (h ▸ hu)⟩

include hx hx' in
/-- On a `B`-circle the `s₁`-cycles are the old circles. -/
theorem reconnect_sameCycle_iff_disjoint {u : ρ.M} (hu : ρ.comp u ∈ B) (w : ρ.M) :
    (ρ.reconnect x).SameCycle u w ↔ ρ.comp u = ρ.comp w :=
  ρ.reconnect_sameCycle_iff_of_comp_ne x u (ρ.comp_ne_of_mem_disjoint x B hx hx' hu).1
    (ρ.comp_ne_of_mem_disjoint x B hx hx' hu).2 w

include hx hx' in
theorem comp_out_eq_disjoint {u : ρ.M} (hu : ρ.comp u ∈ B) :
    ρ.comp (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect x)) u).out = ρ.comp u :=
  ((ρ.reconnect_sameCycle_iff_disjoint x B hx hx' hu _).mp
    (ρ.reconnect_sameCycle_out x u).symm).symm

end Disjoint

/-- Circles of the restricted smoothing → circles of the restriction (external crossing). -/
noncomputable def rdFwd (x : ρ.M) (B : Finset ρ.comps) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B)
    (s : ((ρ.smooth x).restrict B').comps) : (ρ.restrict B).comps :=
  match s with
  | ⟨Sum.inl q, h⟩ => ⟨ρ.comp q.out, ρ.mem_of_inl_mem x B B' hB' h⟩
  | ⟨Sum.inr f, h⟩ => ⟨f.1, (hB'' f).mp h⟩

open scoped Classical in
/-- Circles of the restriction → circles of the restricted smoothing (external crossing). -/
noncomputable def rdBwd (x : ρ.M) (B : Finset ρ.comps) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B)
    (c : (ρ.restrict B).comps) : ((ρ.smooth x).restrict B').comps :=
  if h : ∃ u, ρ.comp u = c.1 then
    ⟨Sum.inl (Quotient.mk _ (Classical.choose h)),
      (hB' _).mpr (by rw [Classical.choose_spec h]; exact c.2)⟩
  else ⟨Sum.inr ⟨c.1, fun u hu => h ⟨u, hu⟩⟩, (hB'' _).mpr c.2⟩

section Disjoint

variable (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B) (hx' : ρ.comp (ρ.pair x) ∉ B)
  (B' : Finset (ρ.smooth x).comps)
  (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
  (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B)

theorem rdBwd_pos (c : (ρ.restrict B).comps) (h : ∃ u, ρ.comp u = c.1) :
    ρ.rdBwd x B B' hB' hB'' c =
      ⟨Sum.inl (Quotient.mk _ (Classical.choose h)),
        (hB' _).mpr (by rw [Classical.choose_spec h]; exact c.2)⟩ :=
  dite_eq_left h

theorem rdBwd_neg (c : (ρ.restrict B).comps) (h : ¬ ∃ u, ρ.comp u = c.1) :
    ρ.rdBwd x B B' hB' hB'' c = ⟨Sum.inr ⟨c.1, fun u hu => h ⟨u, hu⟩⟩, (hB'' _).mpr c.2⟩ :=
  dite_eq_right h

include hx hx' in
theorem rdBwd_rdFwd (s : ((ρ.smooth x).restrict B').comps) :
    ρ.rdBwd x B B' hB' hB'' (ρ.rdFwd x B B' hB' hB'' s) = s := by
  rcases s with ⟨q | f, h⟩
  · have hmem : ρ.comp q.out ∈ B := ρ.mem_of_inl_mem x B B' hB' h
    have hex : ∃ u, ρ.comp u = ρ.comp q.out := ⟨q.out, rfl⟩
    refine (ρ.rdBwd_pos x B B' hB' hB'' ⟨ρ.comp q.out, hmem⟩ hex).trans ?_
    apply Subtype.ext
    apply congrArg Sum.inl
    refine (Quotient.sound ?_).trans (Quotient.out_eq q)
    exact ((ρ.reconnect_sameCycle_iff_disjoint x B hx hx' hmem _).mpr
      (Classical.choose_spec hex).symm).symm
  · have hex : ¬ ∃ u, ρ.comp u = f.1 := fun ⟨u, hu⟩ => f.2 u hu
    exact (ρ.rdBwd_neg x B B' hB' hB'' ⟨f.1, (hB'' f).mp h⟩ hex).trans rfl

include hx hx' in
theorem rdFwd_rdBwd (c : (ρ.restrict B).comps) :
    ρ.rdFwd x B B' hB' hB'' (ρ.rdBwd x B B' hB' hB'' c) = c := by
  by_cases hex : ∃ u, ρ.comp u = c.1
  · refine (congrArg (ρ.rdFwd x B B' hB' hB'') (ρ.rdBwd_pos x B B' hB' hB'' c hex)).trans ?_
    apply Subtype.ext
    exact (ρ.comp_out_eq_disjoint x B hx hx'
      (by rw [Classical.choose_spec hex]; exact c.2)).trans (Classical.choose_spec hex)
  · exact (congrArg (ρ.rdFwd x B B' hB' hB'') (ρ.rdBwd_neg x B B' hB' hB'' c hex)).trans rfl

end Disjoint

/-- The circle bijection of `restrictSmoothDisjointIso`. -/
noncomputable def rdCompsEquiv (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B)
    (hx' : ρ.comp (ρ.pair x) ∉ B) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B) :
    ((ρ.smooth x).restrict B').comps ≃ (ρ.restrict B).comps where
  toFun := ρ.rdFwd x B B' hB' hB''
  invFun := ρ.rdBwd x B B' hB' hB''
  left_inv := ρ.rdBwd_rdFwd x B hx hx' B' hB' hB''
  right_inv := ρ.rdFwd_rdBwd x B hx hx' B' hB' hB''

/-- The occurrence bijection of `restrictSmoothDisjointIso`. -/
def rdOccEquiv (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B)
    (hx' : ρ.comp (ρ.pair x) ∉ B) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B) :
    ((ρ.smooth x).restrict B').M ≃ (ρ.restrict B).M where
  toFun w := ⟨w.1.1, (ρ.smooth_restrictKeep_iff x B B' hB' w.1).mp w.2⟩
  invFun u := ⟨⟨u.1, ρ.smoothKeep_of_comp_mem_disjoint x B hx hx' u.2.1⟩,
    (ρ.smooth_restrictKeep_iff x B B' hB' _).mpr u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `restrictSmoothDisjointIso` with the block hypotheses stated on `(ρ.smooth x).comps`. -/
theorem restrictSmoothDisjointIso' (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B)
    (hx' : ρ.comp (ρ.pair x) ∉ B) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth x).restrict B') (ρ.restrict B)) := by
  refine ⟨{ e := ρ.rdCompsEquiv x B hx hx' B' hB' hB''
            Φ := ρ.rdOccEquiv x B hx hx' B' hB'
            comp_eq := ?_, succ_eq := ?_, pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }⟩
  · intro w
    apply Subtype.ext
    show ρ.comp w.1.1 = ρ.comp (Quotient.mk _ w.1.1).out
    exact (ρ.comp_out_eq_disjoint x B hx hx'
      ((ρ.smooth_restrictKeep_iff x B B' hB' w.1).mp w.2).1).symm
  · intro w
    apply Subtype.ext
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff x B B' hB' w.1).mp w.2
    have hne := ρ.comp_ne_of_mem_disjoint x B hx hx' hK.1
    show (firstReturn (ρ.smooth x).succ ((ρ.smooth x).RestrictKeep B') w).1.1 =
      (firstReturn ρ.succ (ρ.RestrictKeep B) ⟨w.1.1, hK⟩).1
    calc (firstReturn (ρ.smooth x).succ ((ρ.smooth x).RestrictKeep B') w).1.1
        = (firstReturn (ρ.smooth x).succ (fun m => ρ.RestrictKeep B m.1) ⟨w.1, hK⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (ρ.smooth_restrictKeep_iff x B B' hB') w (fun _ => rfl))
      _ = (firstReturn (ρ.reconnect x) (fun m => ρ.SmoothKeep x m ∧ ρ.RestrictKeep B m)
            ⟨w.1.1, w.1.2, hK⟩).1 :=
          firstReturn_firstReturn (ρ.reconnect x) (ρ.SmoothKeep x) (ρ.RestrictKeep B) ⟨w.1, hK⟩
      _ = (firstReturn ρ.succ (ρ.RestrictKeep B) ⟨w.1.1, hK⟩).1 :=
          firstReturn_val_congr _ _ _ _
            (fun m => ⟨fun h => h.2, fun h => ⟨ρ.smoothKeep_of_comp_mem_disjoint x B hx hx' h.1, h⟩⟩)
            ⟨w.1.1, w.1.2, hK⟩ (ρ.reconnect_pow_eq_succ_pow x w.1.1 hne.1 hne.2)
  · intro w; rfl
  · intro w; rfl
  · intro w; rfl

/-! #### Internal crossing: restriction of the smoothing = smoothing of the restriction.
The smoothed occurrence is a variable `v' : (ρ.restrict B).M` (so that every statement is
well typed without unfolding `restrict`); `v'.1` is the occurrence of `ρ`. -/

section Internal

variable (B : Finset ρ.comps) (v' : (ρ.restrict B).M)

theorem restrictKeep_pair_of_keep : ρ.RestrictKeep B (ρ.pair v'.1) :=
  (ρ.restrictKeep_pair_iff B v'.1).mpr v'.2

/-- `(restrict B).reconnect v'` is the first return of `reconnect v'.1` to the kept occurrences
(U1: `firstReturn_mul_swap`). -/
theorem restrict_reconnect_eq :
    (ρ.restrict B).reconnect v' = firstReturn (ρ.reconnect v'.1) (ρ.RestrictKeep B) := by
  unfold reconnect
  exact (firstReturn_mul_swap ρ.succ (ρ.RestrictKeep B) v'.1 (ρ.pair v'.1) v'.2
    (ρ.restrictKeep_pair_of_keep B v')).symm

theorem restrict_reconnect_sameCycle_iff (a b : (ρ.restrict B).M) :
    ((ρ.restrict B).reconnect v').SameCycle a b ↔ (ρ.reconnect v'.1).SameCycle a.1 b.1 := by
  rw [ρ.restrict_reconnect_eq B v']
  exact firstReturn_sameCycle_iff _ _ a b

theorem restrict_reconnect_sameCycle_out (a : (ρ.restrict B).M) :
    ((ρ.restrict B).reconnect v').SameCycle
      (Quotient.mk (Perm.SameCycle.setoid ((ρ.restrict B).reconnect v')) a).out a :=
  Quotient.mk_out (s := Perm.SameCycle.setoid ((ρ.restrict B).reconnect v')) a

/-- The retained occurrences of the smoothed restriction are the retained occurrences of `ρ`. -/
theorem restrict_smoothKeep_iff (w : (ρ.restrict B).M) :
    (ρ.restrict B).SmoothKeep v' w ↔ ρ.SmoothKeep v'.1 w.1 :=
  ((ρ.restrict B).smoothKeep_iff v' w).trans
    ((and_congr (not_congr Subtype.ext_iff) (not_congr Subtype.ext_iff)).trans
      (ρ.smoothKeep_iff v'.1 w.1).symm)

/-- An `s₁`-cycle without kept occurrence avoids the two circles of the smoothed crossing (those
carry the kept occurrences `v'`, `τ v'`). -/
theorem comp_ne_of_not_hasKept {u : ρ.M}
    (hk : ¬ ∃ u', (ρ.reconnect v'.1).SameCycle u u' ∧ ρ.RestrictKeep B u') :
    ρ.comp u ≠ ρ.comp v'.1 ∧ ρ.comp u ≠ ρ.comp (ρ.pair v'.1) := by
  have key : ¬ (ρ.comp u = ρ.comp v'.1 ∨ ρ.comp u = ρ.comp (ρ.pair v'.1)) := by
    intro h
    rcases ρ.reconnect_sameCycle_self_or_pair v'.1 u h with hc | hc
    · exact hk ⟨v'.1, hc, v'.2⟩
    · exact hk ⟨ρ.pair v'.1, hc, ρ.restrictKeep_pair_of_keep B v'⟩
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem sameCycle_iff_of_not_hasKept {u : ρ.M}
    (hk : ¬ ∃ u', (ρ.reconnect v'.1).SameCycle u u' ∧ ρ.RestrictKeep B u') (w : ρ.M) :
    (ρ.reconnect v'.1).SameCycle u w ↔ ρ.comp u = ρ.comp w :=
  ρ.reconnect_sameCycle_iff_of_comp_ne v'.1 u (ρ.comp_ne_of_not_hasKept B v' hk).1
    (ρ.comp_ne_of_not_hasKept B v' hk).2 w

/-- A crossing-free circle of the restriction is not one of the two circles of the (internal)
smoothed crossing. -/
theorem comp_ne_of_free (c : (ρ.restrict B).FreeComp) :
    c.1.1 ≠ ρ.comp v'.1 ∧ c.1.1 ≠ ρ.comp (ρ.pair v'.1) :=
  ⟨fun h => c.2 v' (Subtype.ext h.symm),
    fun h => c.2 ⟨ρ.pair v'.1, ρ.restrictKeep_pair_of_keep B v'⟩ (Subtype.ext h.symm)⟩

theorem sameCycle_iff_of_free (c : (ρ.restrict B).FreeComp) {u : ρ.M} (hu : ρ.comp u = c.1.1)
    (w : ρ.M) : (ρ.reconnect v'.1).SameCycle u w ↔ ρ.comp u = ρ.comp w :=
  ρ.reconnect_sameCycle_iff_of_comp_ne v'.1 u (hu ▸ (ρ.comp_ne_of_free B v' c).1)
    (hu ▸ (ρ.comp_ne_of_free B v' c).2) w

theorem not_hasKept_of_free (c : (ρ.restrict B).FreeComp) {u : ρ.M} (hu : ρ.comp u = c.1.1) :
    ¬ ∃ u', (ρ.reconnect v'.1).SameCycle u u' ∧ ρ.RestrictKeep B u' := by
  rintro ⟨u', hc, hk⟩
  have : ρ.comp u' = c.1.1 := ((ρ.sameCycle_iff_of_free B v' c hu u').mp hc).symm.trans hu
  exact c.2 ⟨u', hk⟩ (Subtype.ext this)

theorem comp_out_eq_of_free (c : (ρ.restrict B).FreeComp) {u : ρ.M} (hu : ρ.comp u = c.1.1) :
    ρ.comp (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1)) u).out = c.1.1 :=
  (((ρ.sameCycle_iff_of_free B v' c hu _).mp (ρ.reconnect_sameCycle_out v'.1 u).symm).symm).trans hu

/-- The circle of an `s₁`-cycle without kept occurrence, as a crossing-free circle of the
restriction. -/
noncomputable def rsFreeOfNotKept {u : ρ.M} (hu : ρ.comp u ∈ B)
    (hk : ¬ ∃ u', (ρ.reconnect v'.1).SameCycle u u' ∧ ρ.RestrictKeep B u') :
    (ρ.restrict B).FreeComp :=
  ⟨⟨ρ.comp u, hu⟩, fun w hw => hk ⟨w.1,
    (ρ.sameCycle_iff_of_not_hasKept B v' hk w.1).mpr (congrArg Subtype.val hw).symm, w.2⟩⟩

end Internal

/-- A crossing-free circle of `ρ` in `B` as a crossing-free circle of the restriction. -/
def rsFreeOfFree (B : Finset ρ.comps) (f : ρ.FreeComp) (hf : f.1 ∈ B) : (ρ.restrict B).FreeComp :=
  ⟨⟨f.1, hf⟩, fun w hw => f.2 w.1 (congrArg Subtype.val hw)⟩

open scoped Classical in
/-- Circles of the restricted smoothing → circles of the smoothed restriction (internal crossing):
an `s₁`-cycle carrying a kept occurrence goes to its cycle of the restricted `s₁`; one without
goes to the crossing-free circle it fills. -/
noncomputable def rsFwd (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B)
    (s : ((ρ.smooth v'.1).restrict B').comps) : ((ρ.restrict B).smooth v').comps :=
  match s with
  | ⟨Sum.inl q, h⟩ =>
    if hk : ∃ u', (ρ.reconnect v'.1).SameCycle q.out u' ∧ ρ.RestrictKeep B u' then
      Sum.inl (Quotient.mk _
        (⟨Classical.choose hk, (Classical.choose_spec hk).2⟩ : (ρ.restrict B).M))
    else Sum.inr (ρ.rsFreeOfNotKept B v' (ρ.mem_of_inl_mem v'.1 B B' hB' h) hk)
  | ⟨Sum.inr f, h⟩ => Sum.inr (ρ.rsFreeOfFree B f ((hB'' f).mp h))

open scoped Classical in
/-- Circles of the smoothed restriction → circles of the restricted smoothing. -/
noncomputable def rsBwd (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B)
    (c : ((ρ.restrict B).smooth v').comps) : ((ρ.smooth v'.1).restrict B').comps :=
  match c with
  | Sum.inl q => ⟨Sum.inl (Quotient.mk _ q.out.1), (hB' _).mpr q.out.2.1⟩
  | Sum.inr c =>
    if h : ∃ u, ρ.comp u = c.1.1 then
      ⟨Sum.inl (Quotient.mk _ (Classical.choose h)),
        (hB' _).mpr (by rw [Classical.choose_spec h]; exact c.1.2)⟩
    else ⟨Sum.inr ⟨c.1.1, fun u hu => h ⟨u, hu⟩⟩, (hB'' _).mpr c.1.2⟩

section Internal

variable (B : Finset ρ.comps) (v' : (ρ.restrict B).M) (B' : Finset (ρ.smooth v'.1).comps)
  (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
  (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B)

theorem rsFwd_inl_pos (q : Quotient (Perm.SameCycle.setoid (ρ.reconnect v'.1)))
    (h : (Sum.inl q : (ρ.smooth v'.1).comps) ∈ B')
    (hk : ∃ u', (ρ.reconnect v'.1).SameCycle q.out u' ∧ ρ.RestrictKeep B u') :
    ρ.rsFwd B v' B' hB' hB'' ⟨Sum.inl q, h⟩ =
      Sum.inl (Quotient.mk _
        (⟨Classical.choose hk, (Classical.choose_spec hk).2⟩ : (ρ.restrict B).M)) :=
  dite_eq_left hk

theorem rsFwd_inl_neg (q : Quotient (Perm.SameCycle.setoid (ρ.reconnect v'.1)))
    (h : (Sum.inl q : (ρ.smooth v'.1).comps) ∈ B')
    (hk : ¬ ∃ u', (ρ.reconnect v'.1).SameCycle q.out u' ∧ ρ.RestrictKeep B u') :
    ρ.rsFwd B v' B' hB' hB'' ⟨Sum.inl q, h⟩ =
      Sum.inr (ρ.rsFreeOfNotKept B v' (ρ.mem_of_inl_mem v'.1 B B' hB' h) hk) :=
  dite_eq_right hk

theorem rsBwd_inr_pos (c : (ρ.restrict B).FreeComp) (h : ∃ u, ρ.comp u = c.1.1) :
    ρ.rsBwd B v' B' hB' hB'' (Sum.inr c) =
      ⟨Sum.inl (Quotient.mk _ (Classical.choose h)),
        (hB' _).mpr (by rw [Classical.choose_spec h]; exact c.1.2)⟩ :=
  dite_eq_left h

theorem rsBwd_inr_neg (c : (ρ.restrict B).FreeComp) (h : ¬ ∃ u, ρ.comp u = c.1.1) :
    ρ.rsBwd B v' B' hB' hB'' (Sum.inr c) =
      ⟨Sum.inr ⟨c.1.1, fun u hu => h ⟨u, hu⟩⟩, (hB'' _).mpr c.1.2⟩ :=
  dite_eq_right h

theorem rsBwd_rsFwd (s : ((ρ.smooth v'.1).restrict B').comps) :
    ρ.rsBwd B v' B' hB' hB'' (ρ.rsFwd B v' B' hB' hB'' s) = s := by
  rcases s with ⟨q | f, h⟩
  · have hmem : ρ.comp q.out ∈ B := ρ.mem_of_inl_mem v'.1 B B' hB' h
    by_cases hk : ∃ u', (ρ.reconnect v'.1).SameCycle q.out u' ∧ ρ.RestrictKeep B u'
    · rw [ρ.rsFwd_inl_pos B v' B' hB' hB'' q h hk]
      apply Subtype.ext
      apply congrArg Sum.inl
      refine (Quotient.sound ?_).trans (Quotient.out_eq q)
      have h1 := (ρ.restrict_reconnect_sameCycle_iff B v' _ _).mp
        (ρ.restrict_reconnect_sameCycle_out B v'
          ⟨Classical.choose hk, (Classical.choose_spec hk).2⟩)
      exact h1.trans (Classical.choose_spec hk).1.symm
    · rw [ρ.rsFwd_inl_neg B v' B' hB' hB'' q h hk]
      have hex : ∃ u, ρ.comp u = ρ.comp q.out := ⟨q.out, rfl⟩
      rw [ρ.rsBwd_inr_pos B v' B' hB' hB'' _ hex]
      apply Subtype.ext
      apply congrArg Sum.inl
      refine (Quotient.sound ?_).trans (Quotient.out_eq q)
      exact ((ρ.sameCycle_iff_of_not_hasKept B v' hk _).mpr
        (Classical.choose_spec hex).symm).symm
  · have hex : ¬ ∃ u, ρ.comp u = f.1 := fun ⟨u, hu⟩ => f.2 u hu
    exact (ρ.rsBwd_inr_neg B v' B' hB' hB'' (ρ.rsFreeOfFree B f ((hB'' f).mp h)) hex).trans rfl

theorem rsFwd_rsBwd (c : ((ρ.restrict B).smooth v').comps) :
    ρ.rsFwd B v' B' hB' hB'' (ρ.rsBwd B v' B' hB' hB'' c) = c := by
  rcases c with q | c
  · have hk : ∃ u', (ρ.reconnect v'.1).SameCycle
        (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1)) q.out.1).out u' ∧
          ρ.RestrictKeep B u' :=
      ⟨q.out.1, ρ.reconnect_sameCycle_out v'.1 _, q.out.2⟩
    refine (ρ.rsFwd_inl_pos B v' B' hB' hB'' _ ((hB' _).mpr q.out.2.1) hk).trans ?_
    apply congrArg Sum.inl
    refine (Quotient.sound ?_).trans (Quotient.out_eq q)
    refine (ρ.restrict_reconnect_sameCycle_iff B v' _ _).mpr ?_
    exact (Classical.choose_spec hk).1.symm.trans (ρ.reconnect_sameCycle_out v'.1 _)
  · by_cases hex : ∃ u, ρ.comp u = c.1.1
    · have hout : ρ.comp (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1))
          (Classical.choose hex)).out = c.1.1 :=
        ρ.comp_out_eq_of_free B v' c (Classical.choose_spec hex)
      have hk := ρ.not_hasKept_of_free B v' c hout
      rw [ρ.rsBwd_inr_pos B v' B' hB' hB'' c hex, ρ.rsFwd_inl_neg B v' B' hB' hB'' _ _ hk]
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Subtype.ext hout
    · rw [ρ.rsBwd_inr_neg B v' B' hB' hB'' c hex]
      rfl

end Internal

/-- The circle bijection of `restrictSmoothIso`. -/
noncomputable def rsCompsEquiv (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B) :
    ((ρ.smooth v'.1).restrict B').comps ≃ ((ρ.restrict B).smooth v').comps where
  toFun := ρ.rsFwd B v' B' hB' hB''
  invFun := ρ.rsBwd B v' B' hB' hB''
  left_inv := ρ.rsBwd_rsFwd B v' B' hB' hB''
  right_inv := ρ.rsFwd_rsBwd B v' B' hB' hB''

/-- The occurrence bijection of `restrictSmoothIso`. -/
def rsOccEquiv (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B) :
    ((ρ.smooth v'.1).restrict B').M ≃ ((ρ.restrict B).smooth v').M where
  toFun w := ⟨⟨w.1.1, (ρ.smooth_restrictKeep_iff v'.1 B B' hB' w.1).mp w.2⟩,
    (ρ.restrict_smoothKeep_iff B v' _).mpr w.1.2⟩
  invFun w := ⟨⟨w.1.1, (ρ.restrict_smoothKeep_iff B v' w.1).mp w.2⟩,
    (ρ.smooth_restrictKeep_iff v'.1 B B' hB' _).mpr w.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `restrictSmoothIso` for a kept occurrence `v'` of the restriction, with the block hypotheses
stated on `(ρ.smooth v'.1).comps`. -/
theorem restrictSmoothIso' (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v'.1).restrict B') ((ρ.restrict B).smooth v')) := by
  refine ⟨{ e := ρ.rsCompsEquiv B v' B' hB' hB''
            Φ := ρ.rsOccEquiv B v' B' hB'
            comp_eq := ?_, succ_eq := ?_, pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }⟩
  · intro w
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff v'.1 B B' hB' w.1).mp w.2
    have hk : ∃ u', (ρ.reconnect v'.1).SameCycle
        (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1)) w.1.1).out u' ∧
          ρ.RestrictKeep B u' :=
      ⟨w.1.1, ρ.reconnect_sameCycle_out v'.1 _, hK⟩
    refine Eq.trans ?_ (ρ.rsFwd_inl_pos B v' B' hB' hB'' _ ((hB' _).mpr hK.1) hk).symm
    apply congrArg Sum.inl
    apply Quotient.sound
    refine (ρ.restrict_reconnect_sameCycle_iff B v' _ _).mpr ?_
    exact (ρ.reconnect_sameCycle_out v'.1 _).symm.trans (Classical.choose_spec hk).1
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff v'.1 B B' hB' w.1).mp w.2
    have hP : (ρ.restrict B).SmoothKeep v' ⟨w.1.1, hK⟩ :=
      (ρ.restrict_smoothKeep_iff B v' _).mpr w.1.2
    show (firstReturn (ρ.smooth v'.1).succ ((ρ.smooth v'.1).RestrictKeep B') w).1.1 =
      (firstReturn ((ρ.restrict B).reconnect v') ((ρ.restrict B).SmoothKeep v')
        ⟨⟨w.1.1, hK⟩, hP⟩).1.1
    calc (firstReturn (ρ.smooth v'.1).succ ((ρ.smooth v'.1).RestrictKeep B') w).1.1
        = (firstReturn (ρ.smooth v'.1).succ (fun m => ρ.RestrictKeep B m.1) ⟨w.1, hK⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (ρ.smooth_restrictKeep_iff v'.1 B B' hB') w (fun _ => rfl))
      _ = (firstReturn (ρ.reconnect v'.1) (fun m => ρ.SmoothKeep v'.1 m ∧ ρ.RestrictKeep B m)
            ⟨w.1.1, w.1.2, hK⟩).1 :=
          firstReturn_firstReturn (ρ.reconnect v'.1) (ρ.SmoothKeep v'.1) (ρ.RestrictKeep B)
            ⟨w.1, hK⟩
      _ = (firstReturn (ρ.reconnect v'.1) (fun m => ρ.RestrictKeep B m ∧ ρ.SmoothKeep v'.1 m)
            ⟨w.1.1, hK, w.1.2⟩).1 :=
          firstReturn_val_congr _ _ _ _ (fun m => and_comm) ⟨w.1.1, w.1.2, hK⟩ (fun _ => rfl)
      _ = (firstReturn (firstReturn (ρ.reconnect v'.1) (ρ.RestrictKeep B))
            (fun m => ρ.SmoothKeep v'.1 m.1) ⟨⟨w.1.1, hK⟩, w.1.2⟩).1.1 :=
          (firstReturn_firstReturn (ρ.reconnect v'.1) (ρ.RestrictKeep B) (ρ.SmoothKeep v'.1)
            ⟨⟨w.1.1, hK⟩, w.1.2⟩).symm
      _ = (firstReturn ((ρ.restrict B).reconnect v') ((ρ.restrict B).SmoothKeep v')
            ⟨⟨w.1.1, hK⟩, hP⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (fun m => (ρ.restrict_smoothKeep_iff B v' m).symm) ⟨⟨w.1.1, hK⟩, w.1.2⟩
            (fun n => by rw [ρ.restrict_reconnect_eq B v']))
  · intro w; rfl
  · intro w; rfl
  · intro w; rfl

end U2Record

/-! #### The fixed statements of unit U2 -/

open scoped Classical in
/-- **Restriction of the smoothing = smoothing of the restriction** at an internal crossing.
Occurrences: `SmoothKeep v ∧ RestrictKeep B` on both sides (`smooth_comp`, `smoothKeep_iff`,
`Subtype.ext_iff`); successor: LHS = `firstReturn (firstReturn (reconnect v) SmoothKeep) (RestrictKeep B' ∘ val)`
= `firstReturn (reconnect v) (SmoothKeep ∧ RestrictKeep B)` (`firstReturn_firstReturn`); RHS =
`firstReturn ((restrict B).reconnect ⟨v⟩) SmoothKeep` with `(restrict B).reconnect ⟨v⟩ =
firstReturn succ (RestrictKeep B) * swap ⟨v⟩ ⟨pair v⟩ = firstReturn (reconnect v) (RestrictKeep B)`
(`firstReturn_mul_swap`), so RHS = `firstReturn (reconnect v) (RestrictKeep B ∧ SmoothKeep)`
(`firstReturn_firstReturn`, `and_comm`); circles: `inl ⟦u⟧ ↦ inl ⟦⟨u, _⟩⟧` for `comp u ∈ B`
(`sameCycle_map_iff` along the subtype inclusion), `inr f ↦ inr ⟨⟨f.1, _⟩, free⟩`; `comp_eq` by
`Quotient.ind`. -/
theorem restrictSmoothIso (v : ρ.M) (B : Finset ρ.comps) (hv : ρ.RestrictKeep B v)
    (B' : Finset (ρ.smooth v).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v).restrict B')
      ((ρ.restrict B).smooth (⟨v, hv⟩ : {u : ρ.M // ρ.RestrictKeep B u}))) :=
  ρ.restrictSmoothIso' B ⟨v, hv⟩ B' hB' hB''

open scoped Classical in
/-- **Restriction of the smoothing at an external crossing = the old restriction**: no occurrence of
`B` is erased (`RestrictKeep B u → u ≠ v, pair v`) and `s₁` agrees with `s` along every `B`-circle
(`(reconnect v)^n u = succ^n u` when `comp u ∈ B`, since all iterates keep `comp` (`comp_pow`) and
`comp v, comp (pair v) ∉ B`; hence equal return times, `returnTime_eq_iff`).  Circles:
`inl ⟦u⟧ ↦ ⟨comp u, _⟩` (well defined: on `B`-cycles `reconnect = succ`), `inr f ↦ ⟨f.1, _⟩`;
surjective since a `B`-circle either carries an occurrence or is free. -/
theorem restrictSmoothDisjointIso (v : ρ.M) (B : Finset ρ.comps) (hv : ρ.comp v ∉ B)
    (hv' : ρ.comp (ρ.pair v) ∉ B) (B' : Finset (ρ.smooth v).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v).restrict B') (ρ.restrict B)) :=
  ρ.restrictSmoothDisjointIso' v B hv hv' B' hB' hB''

end Record

end Link

/-! ### 6.4 Diagram level: block bookkeeping -/

namespace Link.Diagram

variable (D : Diagram)

/-- A diagram-level block order is a record-level one: for `v = ⟨x, s⟩`, `record.comp v = s.1`
(`record_comp`), `record.pair v = twin v` carries the other strand `t` (`record_pair_apply`,
`twin`), and `isOver v = false ↔ s ≠ overStrand x ↔ s = underStrand x` (`record_isOver_iff`,
`eq_under_of_mem_of_ne`); `hord x s t` gives `underStrand x = s`. -/
theorem rBlockOrdered_of_blockOrdered {q : ℕ} {blk : Fin D.Γ.c → Fin q} (hord : BlockOrdered D blk) :
    D.record.RBlockOrdered blk := by
  intro v hv
  have h : D.underStrand v.1 = v.2.val :=
    hord v.1 v.2.val (D.twin v).2.val v.2.2 (D.twin v).2.2 hv
  show D.overBit v = false
  apply decide_eq_false
  intro heq
  exact D.under_ne_over v.1 (h.trans heq)

/-- **The restriction of an UNDER-first diagram is UNDER-first** (initialization of mp:stack,
sm-3:1519-1521 "If `b = 0`, the full diagram is ascending … Each factor has scalar `δ^{c_i−1}`").
Rank: the order induced by `B.rank` on the block (`exists_rank_equiv` on
`fun j => (B.rank (S.orderEmbOfFin rfl j)).val`); basepoints: the old ones
(`base' j := B.base (S.orderEmbOfFin rfl j)`, typechecks since `(D.restrict S hS).Γ.comp j =
D.Γ.comp (S.orderEmbOfFin rfl j)` is `rfl`), nonsingular by `crossingPoint_mapCrossing`;
UNDER-first: for a crossing `y` of the restriction with `x := mapCrossing y`, `restrict_visitPt_fst`
/ `restrict_visitPt_snd` give component and traversal coordinate of the mapped visits,
`toFun_restrict_underStrand` / `toFun_restrict_overStrand` identify `mapVisit (underVisit y) =
underVisit x`, and `h x` transfers through the monotone rank (`Prod.lex_def`). -/
theorem restrict_underFirst (B : D.Basing) (h : D.UnderFirst B) (S : Finset (Fin D.Γ.c))
    (hS : S.Nonempty) : ∃ B' : (D.restrict S hS).Basing, (D.restrict S hS).UnderFirst B' := by
  -- the rank: sort the old ranks of the components of `S` into a permutation of `Fin S.card`
  have hinj : Function.Injective (fun j : Fin S.card => (B.rank (S.orderEmbOfFin rfl j)).val) := by
    intro i j hij
    exact (S.orderEmbOfFin rfl).injective (B.rank.injective (Fin.ext hij))
  obtain ⟨r, hr⟩ := exists_rank_equiv _ hinj
  -- the basepoints: the old ones; nonsingular because the crossing points are unchanged
  -- (`crossingPoint_mapCrossing`, `restrictMap.f = id`)
  have hns : ∀ (j : Fin S.card) (y : (D.restrict S hS).Γ.Crossing),
      (D.restrict S hS).Γ.eval ⟨j, B.base (S.orderEmbOfFin rfl j)⟩ ≠
        (D.restrict S hS).Γ.crossingPoint y := by
    intro j y
    have hcp := (D.Γ.restrictMap S hS).crossingPoint_mapCrossing D.generic y
    change D.Γ.crossingPoint ((D.Γ.restrictMap S hS).mapCrossing y) =
      (D.Γ.restrictShadow S hS).crossingPoint y at hcp
    show D.Γ.eval ⟨S.orderEmbOfFin rfl j, B.base (S.orderEmbOfFin rfl j)⟩ ≠
      (D.Γ.restrictShadow S hS).crossingPoint y
    rw [← hcp]
    exact B.nonsingular _ _
  refine ⟨⟨r, fun j => B.base (S.orderEmbOfFin rfl j), hns⟩, fun y => ?_⟩
  -- the two occurrences of `y` map to the two occurrences of `x := mapCrossing y`
  have hu : (D.Γ.restrictMap S hS).mapVisit ((D.restrict S hS).underVisit y) =
      D.underVisit ((D.Γ.restrictMap S hS).mapCrossing y) :=
    Sigma.ext rfl (heq_of_eq (Subtype.ext (D.toFun_restrict_underStrand S hS y)))
  have ho : (D.Γ.restrictMap S hS).mapVisit ((D.restrict S hS).overVisit y) =
      D.overVisit ((D.Γ.restrictMap S hS).mapCrossing y) :=
    Sigma.ext rfl (heq_of_eq (Subtype.ext (D.toFun_restrict_overStrand S hS y)))
  have hx := h ((D.Γ.restrictMap S hS).mapCrossing y)
  rw [← hu, ← ho, Prod.lex_def] at hx
  rw [Prod.lex_def]
  -- the three comparisons transport: rank order by `hr`, rank equality by injectivity, offsets
  -- literally equal (`restrict_visitPt_fst` is `rfl`, `restrict_visitPt_snd`)
  have hlt : ∀ v w : (D.restrict S hS).Γ.Visit,
      (D.basedRank B ((D.Γ.restrictMap S hS).mapVisit v)).1 <
          (D.basedRank B ((D.Γ.restrictMap S hS).mapVisit w)).1 →
        ((D.restrict S hS).basedRank ⟨r, fun j => B.base (S.orderEmbOfFin rfl j), hns⟩ v).1 <
          ((D.restrict S hS).basedRank ⟨r, fun j => B.base (S.orderEmbOfFin rfl j), hns⟩ w).1 := by
    intro v w hvw
    show ((r ((D.restrict S hS).visitPt v).1 : Fin S.card) : ℕ) <
      ((r ((D.restrict S hS).visitPt w).1 : Fin S.card) : ℕ)
    exact Fin.lt_def.mp ((hr _ _).mpr hvw)
  have heq : ∀ v w : (D.restrict S hS).Γ.Visit,
      (D.basedRank B ((D.Γ.restrictMap S hS).mapVisit v)).1 =
          (D.basedRank B ((D.Γ.restrictMap S hS).mapVisit w)).1 →
        ((D.restrict S hS).basedRank ⟨r, fun j => B.base (S.orderEmbOfFin rfl j), hns⟩ v).1 =
          ((D.restrict S hS).basedRank ⟨r, fun j => B.base (S.orderEmbOfFin rfl j), hns⟩ w).1 := by
    intro v w hvw
    show ((r ((D.restrict S hS).visitPt v).1 : Fin S.card) : ℕ) =
      ((r ((D.restrict S hS).visitPt w).1 : Fin S.card) : ℕ)
    have hemb : S.orderEmbOfFin rfl ((D.restrict S hS).visitPt v).1 =
        S.orderEmbOfFin rfl ((D.restrict S hS).visitPt w).1 := B.rank.injective (Fin.ext hvw)
    exact congrArg (fun i => ((r i : Fin S.card) : ℕ)) ((S.orderEmbOfFin rfl).injective hemb)
  have hsnd : ∀ v : (D.restrict S hS).Γ.Visit,
      ((D.restrict S hS).basedRank ⟨r, fun j => B.base (S.orderEmbOfFin rfl j), hns⟩ v).2 =
        (D.basedRank B ((D.Γ.restrictMap S hS).mapVisit v)).2 := by
    intro v
    show cyclicOffset (D.Γ.comp (S.orderEmbOfFin rfl ((D.restrict S hS).visitPt v).1)).k
        (traversalKey (B.base (S.orderEmbOfFin rfl ((D.restrict S hS).visitPt v).1)))
        (traversalKey ((D.restrict S hS).visitPt v).2) =
      cyclicOffset (D.Γ.comp (S.orderEmbOfFin rfl ((D.restrict S hS).visitPt v).1)).k
        (traversalKey (B.base (S.orderEmbOfFin rfl ((D.restrict S hS).visitPt v).1)))
        (traversalKey (D.visitPt ((D.Γ.restrictMap S hS).mapVisit v)).2)
    exact congrArg (fun p => cyclicOffset (D.Γ.comp (S.orderEmbOfFin rfl ((D.restrict S hS).visitPt v).1)).k
        (traversalKey (B.base (S.orderEmbOfFin rfl ((D.restrict S hS).visitPt v).1))) (traversalKey p))
      (D.restrict_visitPt_snd S hS v)
  rcases hx with hx | ⟨hx1, hx2⟩
  · exact Or.inl (hlt _ _ hx)
  · refine Or.inr ⟨heq _ _ hx1, ?_⟩
    rw [hsnd, hsnd]
    exact hx2

end Link.Diagram

/-- Switching an internal crossing "preserves the block assignment and the between-block hypothesis"
(sm-3:1524-1525): `switch_underStrand_self` / `switch_underStrand_of_ne`, `x.val` unchanged; at the
switched crossing both strands have equal `blk`, so the premise `blk s.1 < blk t.1` is false. -/
theorem BlockOrdered.switch_of_internal {D : Diagram} {q : ℕ} {blk : Fin D.Γ.c → Fin q}
    (hord : BlockOrdered D blk) {v : D.Γ.Visit}
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) : BlockOrdered (D.switch v.1) blk := by
  have key : ∀ s : D.Γ.Strand, s ∈ v.1.val → blk s.1 = blk (D.compOf v) := by
    intro s hs
    rcases (D.Γ.mem_iff_eq_or_other v.1 v.2.2 s).mp hs with h | h
    · rw [h]; rfl
    · rw [h]; exact hx.symm
  intro x s t hs ht hlt
  by_cases hxv : x = v.1
  · exfalso
    rw [hxv] at hs ht
    rw [key s hs, key t ht] at hlt
    exact lt_irrefl _ hlt
  · rw [D.switch_underStrand_of_ne hxv]
    exact hord x s t hs ht hlt

/-- "is the same switch in its block restriction" (`switch_restrict_of_internal` after `subst hy`). -/
theorem blockRestrict_switch_of_internal (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (v : D.Γ.Visit) (i : Fin q)
    (y : (blockRestrict D blk hblk i).Γ.Crossing)
    (hy : (D.Γ.restrictMap (blockSet D blk i) (blockSet_nonempty D blk hblk i)).mapCrossing y = v.1) :
    blockRestrict (D.switch v.1) blk hblk i = (blockRestrict D blk hblk i).switch y := by
  have h := D.switch_restrict_of_internal (blockSet D blk i) (blockSet_nonempty D blk hblk i) y
  rw [hy] at h
  exact h

/-- "the other restrictions do not change" (`switch_restrict_of_external`; the strand `v.2.val ∈
v.1.val` has component `compOf v` whose block is not `i`). -/
theorem blockRestrict_switch_of_external (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (v : D.Γ.Visit) (i : Fin q) (hi : i ≠ blk (D.compOf v)) :
    blockRestrict (D.switch v.1) blk hblk i = blockRestrict D blk hblk i := by
  exact D.switch_restrict_of_external (blockSet D blk i) (blockSet_nonempty D blk hblk i)
    (fun h => hi ((mem_blockSet_iff D blk i _).mp (h v.2.val v.2.2)).symm)

/-- The transported blocks `blk₀ := smoothBlock blk v ∘ ι₀.e` of a smoothing `D₀` are surjective
("no block becomes empty": for block `i` pick `k` with `blk k = i`; if some visit `u` has
`compOf u = k` take `ι₀.e.symm (inl ⟦u⟧)`, else `ι₀.e.symm (inr ⟨k, free⟩)`) and block-ordered
("All between-block crossing visits persist on their original strands, so their under/over relation
still has the required block order": for `y` with strands `s, t` and `blk₀ s.1 < blk₀ t.1`, put
`u := ι₀.Φ ⟨y, s⟩`; `ι₀.Φ ⟨y, t⟩ = pair u` (`pair_eq`), `ι₀.comp_eq` gives `inl ⟦u.1⟧ = ι₀.e s.1` so
`blk₀ s.1 = blk (compOf u.1)`; `hord` at `u.1.1` ⇒ `u.1 = underVisit _` ⇒ `isOver u.1 = false` ⇒
`D₀.record.isOver ⟨y, s⟩ = false` (`ι₀.bit_eq`, `smooth_isOver`) ⇒ `s = underStrand y`
(`record_isOver_iff`, `eq_under_of_mem_of_ne`)). -/
theorem blocks_of_smoothing (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (hord : BlockOrdered D blk) (v : D.Γ.Visit)
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) (D₀ : Diagram)
    (ι₀ : RecordIso D₀.record (D.record.smooth v)) :
    Function.Surjective (D.record.smoothBlock blk v hx ∘ ι₀.e) ∧
      BlockOrdered D₀ (D.record.smoothBlock blk v hx ∘ ι₀.e) := by
  constructor
  · -- "no block becomes empty"
    intro i
    obtain ⟨k, hk⟩ := hblk i
    by_cases hex : ∃ u : D.Γ.Visit, D.compOf u = k
    · obtain ⟨u, hu⟩ := hex
      refine ⟨ι₀.e.symm (Sum.inl (Quotient.mk _ u)), ?_⟩
      have h1 : ι₀.e (ι₀.e.symm (Sum.inl (Quotient.mk _ u))) = Sum.inl (Quotient.mk _ u) :=
        ι₀.e.apply_symm_apply _
      calc (D.record.smoothBlock blk v hx ∘ ι₀.e) (ι₀.e.symm (Sum.inl (Quotient.mk _ u)))
          = D.record.smoothBlock blk v hx (Sum.inl (Quotient.mk _ u)) :=
            congrArg (D.record.smoothBlock blk v hx) h1
        _ = blk (D.compOf u) := rfl
        _ = i := by rw [hu]; exact hk
    · have hex' : ∀ u : D.Γ.Visit, D.compOf u ≠ k := fun u hu => hex ⟨u, hu⟩
      refine ⟨ι₀.e.symm (Sum.inr (⟨k, hex'⟩ : D.record.FreeComp)), ?_⟩
      have h1 : ι₀.e (ι₀.e.symm (Sum.inr (⟨k, hex'⟩ : D.record.FreeComp))) =
          Sum.inr (⟨k, hex'⟩ : D.record.FreeComp) :=
        ι₀.e.apply_symm_apply _
      calc (D.record.smoothBlock blk v hx ∘ ι₀.e) (ι₀.e.symm (Sum.inr (⟨k, hex'⟩ : D.record.FreeComp)))
          = D.record.smoothBlock blk v hx (Sum.inr (⟨k, hex'⟩ : D.record.FreeComp)) :=
            congrArg (D.record.smoothBlock blk v hx) h1
        _ = blk k := rfl
        _ = i := hk
  · -- "All between-block crossing visits persist on their original strands"
    intro y s t hs ht hlt
    have hst : s ≠ t := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    let vs : D₀.Γ.Visit := ⟨y, ⟨s, hs⟩⟩
    let vt : D₀.Γ.Visit := ⟨y, ⟨t, ht⟩⟩
    have hvt : vt = D₀.twin vs :=
      D₀.twin_unique vs vt rfl (fun h => hst (congrArg (fun w : D₀.Γ.Visit => w.2.val) h).symm)
    have hp : ι₀.Φ (D₀.twin vs) = (D.record.smooth v).pair (ι₀.Φ vs) := ι₀.pair_eq vs
    have hs' : (D.record.smoothBlock blk v hx ∘ ι₀.e) s.1 = blk (D.compOf (ι₀.Φ vs).1) := by
      show D.record.smoothBlock blk v hx (ι₀.e (D₀.record.comp vs)) = _
      rw [← ι₀.comp_eq vs]
      rfl
    have ht' : (D.record.smoothBlock blk v hx ∘ ι₀.e) t.1 =
        blk (D.compOf (D.twin (ι₀.Φ vs).1)) := by
      show D.record.smoothBlock blk v hx (ι₀.e (D₀.record.comp vt)) = _
      rw [← ι₀.comp_eq vt, hvt, hp]
      rfl
    rw [hs', ht'] at hlt
    have hbit : D.record.isOver (ι₀.Φ vs).1 = false := D.rBlockOrdered_of_blockOrdered hord _ hlt
    have hbit₀ : D₀.overBit vs = false := (ι₀.bit_eq vs).symm.trans hbit
    symm
    apply D₀.eq_under_of_mem_of_ne y hs
    intro heq
    have htrue : D₀.overBit vs = true := (D₀.overBit_eq_true_iff vs).mpr heq
    rw [hbit₀] at htrue
    exact Bool.false_ne_true htrue

/-! ### 6.5 Initialization, step, assembly -/

/-- "If `b = 0`, the full diagram is ascending … their product times `δ^{q−1}` has the same exponent
`q − 1 + Σ(c_i − 1) = Σ c_i − 1`" (sm-3:1519-1523): `P_underFirst_init` on `D` and on every block
restriction (`restrict_underFirst`, value `δ^{c_i−1}` with `c_i = (blockSet i).card`,
`restrict_componentCount`), `Finset.prod_pow_eq_pow_sum`, `∑ c_i = c`
(`Finset.card_eq_sum_card_fiberwise`), `∑ (c_i − 1) = c − q` (each `c_i ≥ 1`), `pow_add`. -/
theorem stack_init (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (B : D.Basing) (h : D.UnderFirst B) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  -- every block restriction is UNDER-first (`restrict_underFirst`), hence `P (D_i) = δ^{c_i − 1}`
  have hi : ∀ i : Fin q,
      P (blockRestrict D blk hblk i) = R.delta ^ ((blockSet D blk i).card - 1) := by
    intro i
    obtain ⟨B', hB'⟩ :=
      D.restrict_underFirst B h (blockSet D blk i) (blockSet_nonempty D blk hblk i)
    rw [blockRestrict_eq]
    exact P_underFirst_init _ B' hB'
  rw [P_underFirst_init D B h, Finset.prod_congr rfl fun i _ => hi i, Finset.prod_pow_eq_pow_sum,
    ← pow_add]
  congr 1
  -- exponents: `∑ c_i = c` (the blocks partition the components), every `c_i ≥ 1`, `q ≥ 1`
  have hsum : ∑ i : Fin q, (blockSet D blk i).card = D.Γ.c := by
    have hfib := Finset.card_eq_sum_card_fiberwise (f := blk) (s := Finset.univ) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at hfib
    exact hfib.symm
  have hpos : ∀ i : Fin q, 1 ≤ (blockSet D blk i).card := fun i =>
    Finset.card_pos.mpr (blockSet_nonempty D blk hblk i)
  have hsub : ∑ i : Fin q, ((blockSet D blk i).card - 1) + q = D.Γ.c := by
    have h1 : ∑ i : Fin q, (blockSet D blk i).card =
        ∑ i : Fin q, (((blockSet D blk i).card - 1) + 1) :=
      Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (hpos i)).symm
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at h1
    omega
  have hq : 0 < q := Fin.pos (blk ⟨0, D.Γ.hc⟩)
  show D.Γ.c - 1 = q - 1 + ∑ i : Fin q, ((blockSet D blk i).card - 1)
  omega

/-- The stack step (sm-3:1524-1533) at an internal occurrence `v` of block `i₀ := blk (compOf v)`.
`P D = solvedR pos (P (D.switch v.1)) (P D₀)` (`solvedR_of_skein`).  `ihsw` is rewritten with
`blockRestrict_switch_of_internal` (factor `i₀`: `F.switch y`, where `F := blockRestrict D blk hblk i₀`,
`v' := (D.exists_restrictVisit _ _ v hv).choose`, `y := v'.1`, `hy` by `restrictVisit_fst`) and
`blockRestrict_switch_of_external` (others).  `blocks_of_smoothing` gives `blk₀`; `ih₀ blk₀`.
Factor `i ≠ i₀`: `(blockRestrict D₀ blk₀ _ i).record ≅ D₀.record.restrict (blockSet₀ i)`
(`restrictRecordIso`) `≅ (D.record.smooth v).restrict B'` with
`B' := univ.filter (smoothBlock blk v hx · = i)` (`ι₀.restrict`, `hB` by `mem_blockSet_iff`)
`≅ D.record.restrict (blockSet i)` (`restrictSmoothDisjointIso`; `hB'`/`hB''` by `smoothBlock_inl/inr`)
`≅ (blockRestrict D blk hblk i).record` ⇒ `P` equal by `presentations`.  Factor `i₀`:
`… ≅ (D.record.restrict (blockSet i₀)).smooth ⟨v, hv⟩` (`restrictSmoothIso`) `≅ F.record.smooth v'`
(`(D.restrictRecordIso _ _).symm.smooth`, `restrictVisitEquiv_apply_val`) `≅ F₀.record` for `F₀` from
`exists_smoothing_record_visit F y v' rfl`; so `P (blockRestrict D₀ blk₀ _ i₀) = P F₀`, and
`P F = solvedR pos' (P (F.switch y)) (P F₀)` with `pos' ↔ pos` (`restrict_isPositive_iff`, `hy`).
Finish: `Finset.mul_prod_erase` on the three products, `solvedR_mul_left`. -/
theorem stack_step (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (hord : BlockOrdered D blk) (v : D.Γ.Visit)
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) (D₀ : Diagram)
    (h₀ : IsOrientedSmoothing D v.1 D₀) (ι₀ : RecordIso D₀.record (D.record.smooth v))
    (ihsw : P (D.switch v.1) =
      R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict (D.switch v.1) blk hblk i))
    (ih₀ : ∀ (blk₀ : Fin D₀.Γ.c → Fin q) (hblk₀ : Function.Surjective blk₀), BlockOrdered D₀ blk₀ →
      P D₀ = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D₀ blk₀ hblk₀ i)) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  -- the block of the crossing, its component set, and the crossing seen in the block restriction
  set i₀ : Fin q := blk (D.compOf v)
  have hS : (blockSet D blk i₀).Nonempty := blockSet_nonempty D blk hblk i₀
  have hv : D.record.RestrictKeep (blockSet D blk i₀) v :=
    ⟨(mem_blockSet_iff D blk i₀ _).mpr rfl, (mem_blockSet_iff D blk i₀ _).mpr hx.symm⟩
  set v' : (blockRestrict D blk hblk i₀).Γ.Visit :=
    (D.restrictVisitEquiv (blockSet D blk i₀) hS).symm ⟨v, hv⟩
  have hv' : D.restrictVisit (blockSet D blk i₀) hS v' = v :=
    congrArg Subtype.val ((D.restrictVisitEquiv (blockSet D blk i₀) hS).apply_symm_apply ⟨v, hv⟩)
  have hy : (D.Γ.restrictMap (blockSet D blk i₀) hS).mapCrossing v'.1 = v.1 :=
    congrArg Sigma.fst hv'
  -- splitting off the factor `i₀` of a product over `Fin q`
  have hsplit : ∀ f : Fin q → R, ∏ i, f i = f i₀ * ∏ i ∈ Finset.univ.erase i₀, f i :=
    fun f => (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)).symm
  -- 1. the skein relation at `v.1` in `D` (lp:positive / lp:negative)
  have hD : P D = solvedR (D.IsPositive v.1) (P (D.switch v.1)) (P D₀) :=
    solvedR_of_skein (Q := P) (fun _ _ _ h => P_skein h) h₀
  -- 2. the switched diagram: the same switch in block `i₀`, invisible to the other blocks
  have hsw : ∏ i, P (blockRestrict (D.switch v.1) blk hblk i) =
      P ((blockRestrict D blk hblk i₀).switch v'.1) *
        ∏ i ∈ Finset.univ.erase i₀, P (blockRestrict D blk hblk i) := by
    rw [hsplit (fun i => P (blockRestrict (D.switch v.1) blk hblk i)),
      blockRestrict_switch_of_internal D blk hblk v i₀ v'.1 hy]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [blockRestrict_switch_of_external D blk hblk v i (Finset.ne_of_mem_erase hi)]
  -- 3. the smoothing: the transported blocks, and its block restrictions up to record isomorphism
  obtain ⟨hblk₀, hord₀⟩ := blocks_of_smoothing D blk hblk hord v hx D₀ ι₀
  have h₀' := ih₀ _ hblk₀ hord₀
  have hB : ∀ (i : Fin q) (c : D₀.record.comps),
      ι₀.e c ∈ Finset.univ.filter (fun s => D.record.smoothBlock blk v hx s = i) ↔
        c ∈ blockSet D₀ (D.record.smoothBlock blk v hx ∘ ι₀.e) i := by
    intro i c
    exact ⟨fun h => (mem_blockSet_iff D₀ _ i _).mpr (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_blockSet_iff D₀ _ i _).mp h⟩⟩
  have hmem : ∀ (i : Fin q) (s : (D.record.smooth v).comps),
      s ∈ Finset.univ.filter (fun s => D.record.smoothBlock blk v hx s = i) ↔
        D.record.smoothBlock blk v hx s = i := by
    intro i s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hB' : ∀ (i : Fin q) (u : D.record.M),
      (Sum.inl (Quotient.mk _ u) : (D.record.smooth v).comps) ∈
          Finset.univ.filter (fun s => D.record.smoothBlock blk v hx s = i) ↔
        D.record.comp u ∈ blockSet D blk i :=
    fun i u => (hmem i _).trans (mem_blockSet_iff D blk i (D.record.comp u)).symm
  have hB'' : ∀ (i : Fin q) (f : D.record.FreeComp),
      (Sum.inr f : (D.record.smooth v).comps) ∈
          Finset.univ.filter (fun s => D.record.smoothBlock blk v hx s = i) ↔
        f.1 ∈ blockSet D blk i :=
    fun i f => (hmem i _).trans (mem_blockSet_iff D blk i f.1).symm
  -- 3a. "the restrictions to the other blocks are unchanged"
  have hPi : ∀ i, i ≠ i₀ →
      P (blockRestrict D₀ (D.record.smoothBlock blk v hx ∘ ι₀.e) hblk₀ i) =
        P (blockRestrict D blk hblk i) := by
    intro i hi
    have hv1 : D.record.comp v ∉ blockSet D blk i := fun h =>
      hi ((mem_blockSet_iff D blk i _).mp h).symm
    have hv2 : D.record.comp (D.record.pair v) ∉ blockSet D blk i := fun h =>
      hi (hx.trans ((mem_blockSet_iff D blk i _).mp h)).symm
    obtain ⟨κ⟩ := D.record.restrictSmoothDisjointIso v (blockSet D blk i) hv1 hv2 _ (hB' i) (hB'' i)
    exact P_congr (lmF_eq_of_recordIso _ _
      ⟨((D₀.restrictRecordIso _ (blockSet_nonempty D₀ _ hblk₀ i)).trans
        (ι₀.restrict _ _ (hB i))).trans
          (κ.trans (D.restrictRecordIso _ (blockSet_nonempty D blk hblk i)).symm)⟩)
  -- 3b. in block `i₀` the restriction of the smoothing is the smoothing of the restriction
  obtain ⟨F₀, hF₀, ⟨ιF⟩⟩ := exists_smoothing_record_visit (blockRestrict D blk hblk i₀) v'.1 v' rfl
  have hPi₀ : P (blockRestrict D₀ (D.record.smoothBlock blk v hx ∘ ι₀.e) hblk₀ i₀) = P F₀ := by
    obtain ⟨κ⟩ := D.record.restrictSmoothIso v (blockSet D blk i₀) hv _ (hB' i₀) (hB'' i₀)
    exact P_congr (lmF_eq_of_recordIso _ _
      ⟨((D₀.restrictRecordIso _ (blockSet_nonempty D₀ _ hblk₀ i₀)).trans
        (ι₀.restrict _ _ (hB i₀))).trans (κ.trans
          (((D.restrictRecordIso (blockSet D blk i₀) hS).symm.smooth
            (⟨v, hv⟩ : {u : D.record.M // D.record.RestrictKeep (blockSet D blk i₀) u})).trans
              ιF.symm))⟩)
  have hsm : ∏ i, P (blockRestrict D₀ (D.record.smoothBlock blk v hx ∘ ι₀.e) hblk₀ i) =
      P F₀ * ∏ i ∈ Finset.univ.erase i₀, P (blockRestrict D blk hblk i) := by
    rw [hsplit (fun i => P (blockRestrict D₀ (D.record.smoothBlock blk v hx ∘ ι₀.e) hblk₀ i)), hPi₀]
    congr 1
    exact Finset.prod_congr rfl fun i hi => hPi i (Finset.ne_of_mem_erase hi)
  -- 4. the skein relation at the same crossing in the block restriction, with the same sign
  have hF : P (blockRestrict D blk hblk i₀) =
      solvedR (D.IsPositive v.1) (P ((blockRestrict D blk hblk i₀).switch v'.1)) (P F₀) := by
    have hpos : (blockRestrict D blk hblk i₀).IsPositive v'.1 ↔ D.IsPositive v.1 := by
      rw [← hy]; exact D.restrict_isPositive_iff (blockSet D blk i₀) hS v'.1
    have h := solvedR_of_skein (Q := P) (fun _ _ _ h => P_skein h) hF₀
    rw [propext hpos] at h
    exact h
  -- 5. the algebra: the common factor is scalar, the recursion in block `i₀` is the same
  calc P D = solvedR (D.IsPositive v.1) (P (D.switch v.1)) (P D₀) := hD
    _ = solvedR (D.IsPositive v.1)
          ((R.delta ^ (q - 1) * ∏ i ∈ Finset.univ.erase i₀, P (blockRestrict D blk hblk i)) *
            P ((blockRestrict D blk hblk i₀).switch v'.1))
          ((R.delta ^ (q - 1) * ∏ i ∈ Finset.univ.erase i₀, P (blockRestrict D blk hblk i)) *
            P F₀) := by
        rw [ihsw, hsw, h₀', hsm]; congr 1 <;> ring
    _ = (R.delta ^ (q - 1) * ∏ i ∈ Finset.univ.erase i₀, P (blockRestrict D blk hblk i)) *
          solvedR (D.IsPositive v.1) (P ((blockRestrict D blk hblk i₀).switch v'.1)) (P F₀) :=
        solvedR_mul_left _ _ _ _
    _ = R.delta ^ (q - 1) * ∏ i, P (blockRestrict D blk hblk i) := by
        rw [← hF, hsplit (fun i => P (blockRestrict D blk hblk i))]; ring

/-- eq. mp:stack-value (sm-3:1513-1535) by `skein_induction_based` at a block-compatible based
order: init `stack_init` (through the bridge), step `stack_step` at the bad — hence internal
(`isBad_internal`) — occurrence, with the smoothing of the gate `exists_smoothing_record_visit`. -/
theorem stack_formula (D : Diagram) (q : ℕ) (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (h : BlockOrdered D blk) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  obtain ⟨B, hB⟩ := D.record.exists_blockCompatible_rbasing blk
  refine Diagram.skein_induction_based
    (fun D B => ∀ (q : ℕ) (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk),
      BlockOrdered D blk → B.BlockCompatible blk →
      P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i)) ?_ ?_ D B q blk hblk h hB
  · intro D B hB q blk hblk _ _
    obtain ⟨B', hB'⟩ := D.exists_underFirst_of_rUnderFirst B hB
    exact stack_init D blk hblk B' hB'
  · intro D B v hv ihsw ihsm q blk hblk hord hBc
    have hx : blk (D.compOf v) = blk (D.compOf (D.twin v)) :=
      Record.RBasing.isBad_internal (D.rBlockOrdered_of_blockOrdered hord) hBc hv
    obtain ⟨D₀, h₀, ⟨ι₀⟩⟩ := exists_smoothing_record_visit D v.1 v rfl
    refine stack_step D blk hblk hord v hx D₀ h₀ ι₀ ?_ ?_
    · exact ihsw q blk hblk (hord.switch_of_internal hx) (fun c c' hc => hBc c c' hc)
    · intro blk₀ hblk₀ hord₀
      obtain ⟨B₀, hB₀⟩ := D₀.record.exists_blockCompatible_rbasing blk₀
      exact ihsm D₀ B₀ h₀ q blk₀ hblk₀ hord₀ hB₀

/-- mp:stack as printed. -/
structure StackData : Prop where
  /-- eq. mp:stack-value: `P_D = δ^{q−1} ∏_{i=1}^q P_{D_i}`. -/
  stack : ∀ (D : Diagram) (q : ℕ) (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk),
    BlockOrdered D blk →
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i)
  /-- "In particular `P_{A ⊔ B} = δ P_A P_B` for two nonempty diagrams presented without mixed
  crossings": a diagram partitioned into two blocks with no crossing between the blocks. -/
  split_union : ∀ (D : Diagram) (blk : Fin D.Γ.c → Fin 2) (hblk : Function.Surjective blk),
    (∀ (x : D.Γ.Crossing) (s t : D.Γ.Strand), s ∈ x.val → t ∈ x.val → blk s.1 = blk t.1) →
    P D = R.delta * P (blockRestrict D blk hblk 0) * P (blockRestrict D blk hblk 1)

theorem stack : StackData where
  stack := stack_formula
  split_union := fun D blk hblk h => by
    have hbo : BlockOrdered D blk := fun x s t hs ht hlt => by
      rw [h x s t hs ht] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [stack_formula D 2 blk hblk hbo, Fin.prod_univ_two, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
      mul_assoc]


end SM
