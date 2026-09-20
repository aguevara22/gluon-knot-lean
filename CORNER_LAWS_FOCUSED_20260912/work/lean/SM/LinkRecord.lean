import SM.CarrierAmbientTransport
import Mathlib.Data.Sign.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Chapter-3 representation layer, module LinkRecord: combinatorial crossing records (Record, RecordIso, record-level switch / smooth / restrict / join). Implements the design adopted 2026-09-13
(work/reports/design-decision-diagram-record-20260913.md, Proposal #1 with the judges' grafts). Written 2026-09-13 by a Claude Code
implementer subagent of the pod executor (workflow implement-diagram-layer-phase1), checked with `lake env lean` (placeholder-free,
standard axioms) and ported verbatim from work/drafts/LinkRecord.lean (only this header added and #print lines removed). All
declarations live in `SM.Link`; no row points here yet — the definition rows (def:positive-lift, def:gauss-record, def:adeg, ...)
are stated on top of this layer and reviewed against the source. -/

/-! # Combinatorial crossing records (`SM.Link.Record`)

Source: `reference/SM/sm-3-statesum.tex`, the named-record bridge (lines 337-351) and
`def:gauss-record` (lines 352-372), read for every finite number of components as
`rp:record-polynomial` (1215-1229), `lc:presentations` (1306-1318) and `mp:join`
(1370-1385, 1427-1437) require.  This module is independent of the diagram type: the bridge
`Diagram.record` belongs to a later module.  Design: work/reports/design-decision-diagram-record-20260913.md,
section `record_type`, with the judges' grafts (Proposal #2's explicit successor formulas for the
smoothing, `Record.Crossing`, `writhe = (Σ σ)/2`).

The printed words rendered here (sm-3:349-351, 352-360):
"The named record defined next (crossing occurrences, successor, pairing, over/under bits and
signs) is what this section and Section knotlaws call the crossing record of a diagram."
"Its finite crossing-occurrence set M has forward successor s, pairing involution τ without fixed
points, an over/under bit at each occurrence, and crossing signs σ(c) = sgn det(u_{c,O}, u_{c,U})."
"A named record isomorphism is a bijection Φ : M → M' preserving successor, pairing, over/under
bits and these signs."

Every declaration lives in `SM.Link`.  Nothing here is an axiom; the file ends with
`#print axioms` for its main theorems. -/

namespace SM.Link

open Equiv

/-! ## A. First-return permutations

The record-level smoothing (sm-3:1084-1103) and the block restriction (mp:stack, sm-3:1495-1500)
both erase some crossing occurrences from a cyclic successor.  The induced successor on the
retained occurrences is the *first return*: follow the old successor until a retained occurrence
is met.  This section builds that permutation for any permutation of a finite type and any
decidable predicate, together with the lemmas the record operations need. -/

section FirstReturn

variable {α : Type*} [Fintype α] (f : Perm α) (p : α → Prop) [DecidablePred p]

omit [DecidablePred p] in
/-- Some positive power of `f` returns a `p`-point to a `p`-point (the order of `f` does). -/
theorem exists_return (m : α) (hm : p m) : ∃ k : ℕ, 0 < k ∧ p ((f ^ k) m) :=
  ⟨orderOf f, orderOf_pos f, by simpa [pow_orderOf_eq_one] using hm⟩

/-- The first-return time of `f` from a `p`-point `m` to the set `p`. -/
noncomputable def returnTime (m : α) (hm : p m) : ℕ := Nat.find (exists_return f p m hm)

theorem returnTime_pos (m : α) (hm : p m) : 0 < returnTime f p m hm :=
  (Nat.find_spec (exists_return f p m hm)).1

theorem returnTime_spec (m : α) (hm : p m) : p ((f ^ returnTime f p m hm) m) :=
  (Nat.find_spec (exists_return f p m hm)).2

theorem returnTime_min (m : α) (hm : p m) {j : ℕ} (hj0 : 0 < j) (hj : j < returnTime f p m hm) :
    ¬ p ((f ^ j) m) := fun h => Nat.find_min (exists_return f p m hm) hj ⟨hj0, h⟩

theorem returnTime_eq_iff (m : α) (hm : p m) {k : ℕ} :
    returnTime f p m hm = k ↔ (0 < k ∧ p ((f ^ k) m)) ∧ ∀ j < k, ¬ (0 < j ∧ p ((f ^ j) m)) :=
  Nat.find_eq_iff _

/-- The first-return map on the subtype of `p`-points. -/
noncomputable def returnMap (m : {m // p m}) : {m // p m} :=
  ⟨(f ^ returnTime f p m.1 m.2) m.1, returnTime_spec f p m.1 m.2⟩

theorem returnMap_injective : Function.Injective (returnMap f p) := by
  intro m m' h
  have h' : (f ^ returnTime f p m.1 m.2) m.1 = (f ^ returnTime f p m'.1 m'.2) m'.1 :=
    congrArg Subtype.val h
  have hk : 0 < returnTime f p m.1 m.2 := returnTime_pos f p m.1 m.2
  have hk' : 0 < returnTime f p m'.1 m'.2 := returnTime_pos f p m'.1 m'.2
  rcases lt_trichotomy (returnTime f p m.1 m.2) (returnTime f p m'.1 m'.2) with hlt | heq | hgt
  · -- `m` would be a `p`-point of the orbit of `m'` strictly before its first return
    exfalso
    have hm : m.1 = (f ^ (returnTime f p m'.1 m'.2 - returnTime f p m.1 m.2)) m'.1 := by
      apply (f ^ returnTime f p m.1 m.2).injective
      rw [h', ← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    exact returnTime_min f p m'.1 m'.2 (Nat.sub_pos_of_lt hlt) (Nat.sub_lt hk' hk) (hm ▸ m.2)
  · rw [heq] at h'
    exact Subtype.ext ((f ^ _).injective h')
  · exfalso
    have hm : m'.1 = (f ^ (returnTime f p m.1 m.2 - returnTime f p m'.1 m'.2)) m.1 := by
      apply (f ^ returnTime f p m'.1 m'.2).injective
      rw [← h', ← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hgt.le]
    exact returnTime_min f p m.1 m.2 (Nat.sub_pos_of_lt hgt) (Nat.sub_lt hk hk') (hm ▸ m'.2)

/-- The first-return permutation of `f` on the `p`-points. -/
noncomputable def firstReturn : Perm {m // p m} :=
  Equiv.ofBijective (returnMap f p) (Finite.injective_iff_bijective.mp (returnMap_injective f p))

theorem firstReturn_apply (m : {m // p m}) :
    (firstReturn f p m).1 = (f ^ returnTime f p m.1 m.2) m.1 := rfl

theorem firstReturn_apply_of_mem (m : {m // p m}) (h : p (f m.1)) :
    (firstReturn f p m).1 = f m.1 := by
  have : returnTime f p m.1 m.2 = 1 :=
    (returnTime_eq_iff f p m.1 m.2).mpr ⟨⟨Nat.one_pos, by simpa using h⟩, fun j hj => by omega⟩
  rw [firstReturn_apply, this, pow_one]

theorem firstReturn_apply_of_not_mem (m : {m // p m}) (h1 : ¬ p (f m.1)) (h2 : p (f (f m.1))) :
    (firstReturn f p m).1 = f (f m.1) := by
  have : returnTime f p m.1 m.2 = 2 :=
    (returnTime_eq_iff f p m.1 m.2).mpr ⟨⟨by norm_num, by simpa [pow_succ, Perm.mul_apply] using h2⟩,
      fun j hj => by
        interval_cases j
        · omega
        · simpa using h1⟩
  rw [firstReturn_apply, this, pow_succ, pow_one, Perm.mul_apply]

theorem firstReturn_apply_of_not_mem₂ (m : {m // p m}) (h1 : ¬ p (f m.1)) (h2 : ¬ p (f (f m.1)))
    (h3 : p (f (f (f m.1)))) : (firstReturn f p m).1 = f (f (f m.1)) := by
  have : returnTime f p m.1 m.2 = 3 :=
    (returnTime_eq_iff f p m.1 m.2).mpr ⟨⟨by norm_num, by simpa [pow_succ, Perm.mul_apply] using h3⟩,
      fun j hj => by
        interval_cases j
        · omega
        · simpa using h1
        · simpa [pow_succ, Perm.mul_apply] using h2⟩
  rw [firstReturn_apply, this, pow_succ, pow_succ, pow_one, Perm.mul_apply, Perm.mul_apply]

/-- When `p` is `f`-invariant the first return is the plain restriction. -/
theorem firstReturn_eq_subtypePerm (h : ∀ m, p (f m) ↔ p m) :
    firstReturn f p = f.subtypePerm h := by
  ext m
  rw [Perm.subtypePerm_apply]
  exact firstReturn_apply_of_mem f p m ((h m.1).mpr m.2)

/-- A point and its first return lie on one `f`-cycle. -/
theorem sameCycle_firstReturn_apply (m : {m // p m}) : f.SameCycle m.1 (firstReturn f p m).1 :=
  ⟨returnTime f p m.1 m.2, by rw [zpow_natCast]; rfl⟩

/-- Iterating the first return stays on the `f`-cycle of the starting point. -/
theorem sameCycle_firstReturn_pow (m : {m // p m}) (n : ℕ) :
    f.SameCycle m.1 ((firstReturn f p ^ n) m).1 := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (sameCycle_firstReturn_apply f p _)

/-- First-return cycles are contained in `f`-cycles. -/
theorem sameCycle_of_firstReturn_sameCycle {m m' : {m // p m}}
    (h : (firstReturn f p).SameCycle m m') : f.SameCycle m.1 m'.1 := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  exact sameCycle_firstReturn_pow f p m n

/-- Every `p`-point of the forward `f`-orbit of a `p`-point is reached by iterating the first
return: the first-return cycles are exactly the `p`-points of the `f`-cycles. -/
theorem firstReturn_pow_of_pow (n : ℕ) : ∀ (m : {m // p m}), p ((f ^ n) m.1) →
    ∃ i : ℕ, ((firstReturn f p ^ i) m).1 = (f ^ n) m.1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨0, by simp⟩
    set k := returnTime f p m.1 m.2 with hk
    rcases lt_trichotomy n k with hlt | heq | hgt
    · exact absurd hn (returnTime_min f p m.1 m.2 hpos hlt)
    · exact ⟨1, by rw [pow_one, firstReturn_apply, ← hk, heq]⟩
    · have hsplit : (f ^ n) m.1 = (f ^ (n - k)) (firstReturn f p m).1 := by
        rw [firstReturn_apply, ← hk, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hgt.le]
      have hpos' : 0 < k := returnTime_pos f p m.1 m.2
      obtain ⟨i, hi⟩ := ih (n - k) (by omega) (firstReturn f p m) (hsplit ▸ hn)
      exact ⟨i + 1, by rw [pow_succ, Perm.mul_apply, hi, hsplit]⟩

theorem firstReturn_sameCycle_of_sameCycle {m m' : {m // p m}} (h : f.SameCycle m.1 m'.1) :
    (firstReturn f p).SameCycle m m' := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  obtain ⟨i, hi⟩ := firstReturn_pow_of_pow f p n m (hn ▸ m'.2)
  exact ⟨i, by rw [zpow_natCast]; exact Subtype.ext (hi.trans hn)⟩

theorem firstReturn_sameCycle_iff (m m' : {m // p m}) :
    (firstReturn f p).SameCycle m m' ↔ f.SameCycle m.1 m'.1 :=
  ⟨sameCycle_of_firstReturn_sameCycle f p, firstReturn_sameCycle_of_sameCycle f p⟩

end FirstReturn

/-! ## B. Reconnecting a permutation by a transposition

`f * swap a b` is the successor "before erasing" of sm-3:1092-1096: a self-crossing cycle
`(x A y B)` becomes the two cycles `(x B), (y A)`; two cycles `(x A), (y B)` of a mixed crossing
become `(x B y A)`.  The merging half is proved here (the splitting half is the accepted
`SM.Carrier.splitList_ambient_*` family); both are consumed by `joinRecord` and `smooth`. -/

section MulSwap

variable {α : Type*} [DecidableEq α] (f : Perm α) (a b : α)

theorem mul_swap_apply_of_ne_of_ne {x : α} (hxa : x ≠ a) (hxb : x ≠ b) :
    (f * swap a b) x = f x := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb]

theorem mul_swap_apply_left : (f * swap a b) a = f b := by
  rw [Perm.mul_apply, swap_apply_left]

theorem mul_swap_apply_right : (f * swap a b) b = f a := by
  rw [Perm.mul_apply, swap_apply_right]

/-- Points on the `f`-cycle of `a` reach `a` along `f * swap a b` when `b` is on another cycle. -/
theorem mul_swap_sameCycle_of_pow_eq (hab : ¬ f.SameCycle a b) :
    ∀ (k : ℕ) (x : α), (f ^ k) x = a → (f * swap a b).SameCycle x a := by
  intro k
  induction k with
  | zero => intro x hx; rw [pow_zero, Perm.one_apply] at hx; rw [hx]
  | succ k ih =>
    intro x hx
    rw [pow_succ, Perm.mul_apply] at hx
    have hx' := ih (f x) hx
    by_cases hxa : x = a
    · rw [hxa]
    by_cases hxb : x = b
    · exfalso
      apply hab
      refine Perm.SameCycle.symm ⟨(k + 1 : ℕ), ?_⟩
      rw [zpow_natCast, pow_succ, Perm.mul_apply, ← hxb, hx]
    have : (f * swap a b).SameCycle x (f x) :=
      ⟨1, by rw [zpow_one, mul_swap_apply_of_ne_of_ne f a b hxa hxb]⟩
    exact this.trans hx'

variable [Finite α]

theorem mul_swap_sameCycle_left (hab : ¬ f.SameCycle a b) {x : α} (hx : f.SameCycle x a) :
    (f * swap a b).SameCycle x a := by
  obtain ⟨k, hk⟩ := hx.exists_nat_pow_eq
  exact mul_swap_sameCycle_of_pow_eq f a b hab k x hk

theorem mul_swap_sameCycle_right (hab : ¬ f.SameCycle a b) {x : α} (hx : f.SameCycle x b) :
    (f * swap a b).SameCycle x b := by
  rw [swap_comm]
  exact mul_swap_sameCycle_left f b a (fun h => hab h.symm) hx

/-- The two reconnected cycles are merged into one. -/
theorem mul_swap_sameCycle_self (hab : ¬ f.SameCycle a b) : (f * swap a b).SameCycle a b := by
  have h1 : (f * swap a b).SameCycle a (f b) :=
    ⟨1, by rw [zpow_one, mul_swap_apply_left]⟩
  have h2 : f.SameCycle (f b) b := Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl f b)
  exact h1.trans (mul_swap_sameCycle_right f a b hab h2)

end MulSwap

section SumCongr

variable {α β : Type*} (f : Perm α) (g : Perm β)

theorem sumCongr_pow (n : ℕ) : (Perm.sumCongr f g) ^ n = Perm.sumCongr (f ^ n) (g ^ n) := by
  have := map_pow (Perm.sumCongrHom α β) (f, g) n
  simpa [Perm.sumCongrHom_apply, Prod.pow_def] using this.symm

theorem sumCongr_zpow (n : ℤ) : (Perm.sumCongr f g) ^ n = Perm.sumCongr (f ^ n) (g ^ n) := by
  have := map_zpow (Perm.sumCongrHom α β) (f, g) n
  simpa [Perm.sumCongrHom_apply, Prod.pow_def] using this.symm

theorem sumCongr_sameCycle_inl_iff (x y : α) :
    (Perm.sumCongr f g).SameCycle (Sum.inl x) (Sum.inl y) ↔ f.SameCycle x y := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl] at hi
    exact Sum.inl.inj hi
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl, hi]⟩

theorem sumCongr_sameCycle_inr_iff (x y : β) :
    (Perm.sumCongr f g).SameCycle (Sum.inr x) (Sum.inr y) ↔ g.SameCycle x y := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inr] at hi
    exact Sum.inr.inj hi
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inr, hi]⟩

theorem not_sumCongr_sameCycle_inl_inr (x : α) (y : β) :
    ¬ (Perm.sumCongr f g).SameCycle (Sum.inl x) (Sum.inr y) := by
  rintro ⟨i, hi⟩
  rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl] at hi
  exact Sum.inl_ne_inr hi

end SumCongr

/-! ## C. The crossing record (def:gauss-record, sm-3:352-360, for every component count)

Printed clauses rendered by the fields (sm-3:353-360): "Its finite crossing-occurrence set M"
(`M`, `mFin`), "forward successor s" (`succ`; one oriented cycle per parametrizing circle,
`succ_comp`, `succ_cycle`), "pairing involution τ without fixed points" (`pair`, `pair_invol`,
`pair_ne`), "an over/under bit at each occurrence" (`isOver`; the two occurrences of a crossing
carry opposite bits, `bit_pair`), "crossing signs σ(c) = sgn det(u_{c,O}, u_{c,U})" (`sgn`, one
nonzero sign per crossing stored on both occurrences, `sgn_pair`, `sgn_ne`).  The component set
`comps` lists every parametrizing circle, crossing-free ones included ("The component bijection
must also include all components with no crossing occurrences", rp:record-polynomial,
sm-3:1223-1224; "All crossing-free circles must be included in the component bijection",
lc:presentations, sm-3:1315), so `comp` need not be surjective. -/

/-- A combinatorial crossing record: the finite data `(M, s, τ, bits, σ)` of def:gauss-record
(sm-3:352-360) together with the parametrizing circles (`comps`) carrying the occurrences. -/
structure Record where
  /-- the parametrizing circles, crossing-free ones included -/
  comps : Type
  [compsFin : Fintype comps]
  /-- "Its finite crossing-occurrence set M" -/
  M : Type
  [mFin : Fintype M]
  [mDec : DecidableEq M]
  /-- the circle carrying an occurrence -/
  comp : M → comps
  /-- "forward successor s" -/
  succ : Perm M
  /-- "pairing involution τ" -/
  pair : Perm M
  /-- "an over/under bit at each occurrence" -/
  isOver : M → Bool
  /-- "crossing signs σ(c) = sgn det(u_{c,O}, u_{c,U})", stored on both occurrences -/
  sgn : M → SignType
  /-- the successor stays on its circle -/
  succ_comp : ∀ v, comp (succ v) = comp v
  /-- one successor cycle per circle -/
  succ_cycle : ∀ v w, comp v = comp w → succ.SameCycle v w
  /-- "without fixed points" -/
  pair_ne : ∀ v, pair v ≠ v
  /-- "pairing involution" -/
  pair_invol : ∀ v, pair (pair v) = v
  /-- the two occurrences of a crossing are one over- and one under-pass -/
  bit_pair : ∀ v, isOver (pair v) = !isOver v
  /-- the sign is a property of the crossing -/
  sgn_pair : ∀ v, sgn (pair v) = sgn v
  /-- signs of transverse double points are nonzero -/
  sgn_ne : ∀ v, sgn v ≠ 0

attribute [instance] Record.compsFin Record.mFin Record.mDec

namespace Record

variable (ρ : Record)

/-- Number of parametrizing circles `c` (lp:lm "Here c ≥ 1" is a property of diagrams, not of
abstract records). -/
def componentCount : ℕ := Fintype.card ρ.comps

theorem pair_injective : Function.Injective ρ.pair := ρ.pair.injective

theorem pair_symm_eq (v : ρ.M) : ρ.pair.symm v = ρ.pair v := by
  rw [Equiv.symm_apply_eq]
  exact (ρ.pair_invol v).symm

theorem pair_eq_iff (v w : ρ.M) : ρ.pair v = w ↔ v = ρ.pair w := by
  constructor
  · rintro rfl; rw [ρ.pair_invol]
  · rintro rfl; rw [ρ.pair_invol]

theorem ne_pair (v : ρ.M) : v ≠ ρ.pair v := fun h => ρ.pair_ne v h.symm

theorem comp_pow (n : ℕ) (v : ρ.M) : ρ.comp ((ρ.succ ^ n) v) = ρ.comp v := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih => rw [pow_succ', Perm.mul_apply, ρ.succ_comp, ih]

theorem comp_zpow (n : ℤ) (v : ρ.M) : ρ.comp ((ρ.succ ^ n) v) = ρ.comp v := by
  obtain ⟨k, hk⟩ := Perm.SameCycle.exists_nat_pow_eq
    (⟨n, rfl⟩ : ρ.succ.SameCycle v ((ρ.succ ^ n) v))
  rw [← hk, ρ.comp_pow]

/-- The cycles of the successor are exactly the components carrying occurrences. -/
theorem sameCycle_iff_comp_eq (v w : ρ.M) : ρ.succ.SameCycle v w ↔ ρ.comp v = ρ.comp w :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, ρ.comp_zpow], ρ.succ_cycle v w⟩

theorem comp_succ_symm (v : ρ.M) : ρ.comp (ρ.succ.symm v) = ρ.comp v := by
  have := ρ.succ_comp (ρ.succ.symm v)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-- The sign is nonzero, so it is `1` or `-1`. -/
theorem sgn_eq_one_or_neg_one (v : ρ.M) : ρ.sgn v = 1 ∨ ρ.sgn v = -1 := by
  rcases h : ρ.sgn v with _ | _ | _
  · exact absurd h (ρ.sgn_ne v)
  · right; rfl
  · left; rfl

/-- Positive crossing occurrence (def:positive-lift: "positive if det(u_o, u_u) > 0"). -/
def IsPositive (v : ρ.M) : Prop := ρ.sgn v = 1

theorem isPositive_pair (v : ρ.M) : ρ.IsPositive (ρ.pair v) ↔ ρ.IsPositive v := by
  unfold IsPositive; rw [ρ.sgn_pair]

/-- The over occurrence of a crossing is unique: exactly one of `v`, `τ v` is over. -/
theorem isOver_xor (v : ρ.M) : ρ.isOver v = true ∨ ρ.isOver (ρ.pair v) = true := by
  rw [ρ.bit_pair]; cases ρ.isOver v <;> simp

/-! ### Even sums and the writhe -/

/-- Any pair-invariant integer weight has even total: the over occurrences and the under
occurrences are exchanged by `τ` (the standard "count each crossing twice"). -/
theorem sum_eq_two_mul_sum_over (g : ρ.M → ℤ) (hg : ∀ v, g (ρ.pair v) = g v) :
    ∑ v, g v = 2 * ∑ v ∈ Finset.univ.filter (fun v => ρ.isOver v = true), g v := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => ρ.isOver v = true) g
  have hswap : ∑ v ∈ Finset.univ.filter (fun v => ¬ ρ.isOver v = true), g v =
      ∑ v ∈ Finset.univ.filter (fun v => ρ.isOver v = true), g v := by
    refine Finset.sum_nbij' ρ.pair ρ.pair ?_ ?_ ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [ρ.bit_pair]; simpa using hv
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [ρ.bit_pair, hv]; simp
    · intro v _; exact ρ.pair_invol v
    · intro v _; exact ρ.pair_invol v
    · intro v _; exact (hg v).symm
  rw [← hsplit, hswap, two_mul]

theorem even_sum_of_pair_invariant (g : ρ.M → ℤ) (hg : ∀ v, g (ρ.pair v) = g v) :
    Even (∑ v, g v) :=
  ⟨_, by rw [ρ.sum_eq_two_mul_sum_over g hg, two_mul]⟩

/-- "crossing occurrences" come in pairs: `|M|` is even. -/
theorem even_card_M : Even (Fintype.card ρ.M) := by
  have h := ρ.even_sum_of_pair_invariant (fun _ => 1) (fun _ => rfl)
  simpa using h

/-- The sum of all stored signs is even (each crossing sign is counted on both occurrences). -/
theorem even_sum_sgn : Even (∑ v, (ρ.sgn v : ℤ)) :=
  ρ.even_sum_of_pair_invariant (fun v => (ρ.sgn v : ℤ)) (fun v => by rw [ρ.sgn_pair])

/-- The writhe: "Its writhe (the sum of crossing signs)" (def:positive-lift, sm-3:334-335);
each crossing sign is stored twice, hence the division by two. -/
def writhe : ℤ := (∑ v, (ρ.sgn v : ℤ)) / 2

theorem two_mul_writhe : 2 * ρ.writhe = ∑ v, (ρ.sgn v : ℤ) := by
  unfold writhe
  exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp ρ.even_sum_sgn)

/-- The writhe is the sum of the signs over the over-occurrences (one per crossing). -/
theorem writhe_eq_sum_over :
    ρ.writhe = ∑ v ∈ Finset.univ.filter (fun v => ρ.isOver v = true), (ρ.sgn v : ℤ) := by
  have h := ρ.sum_eq_two_mul_sum_over (fun v => (ρ.sgn v : ℤ)) (fun v => by rw [ρ.sgn_pair])
  unfold writhe
  rw [h, Int.mul_ediv_cancel_left _ two_ne_zero]

/-- The number of crossings `N` (sm-3:1088 "Its crossing count is N-1"; each crossing has two
occurrences). -/
def crossingCount : ℕ := Fintype.card ρ.M / 2

theorem two_mul_crossingCount : 2 * ρ.crossingCount = Fintype.card ρ.M := by
  unfold crossingCount
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp ρ.even_card_M)

/-! ### Crossings as unordered occurrence pairs -/

/-- A crossing is an unordered pair of paired occurrences `{v, τ v}`. -/
def Crossing : Type := {p : Finset ρ.M // ∃ v, p = {v, ρ.pair v}}

/-- Finitely many crossings (subsets of the finite occurrence set). -/
noncomputable instance : Fintype ρ.Crossing := by unfold Crossing; infer_instance

/-- The crossing of an occurrence. -/
def crossingOf (v : ρ.M) : ρ.Crossing := ⟨{v, ρ.pair v}, v, rfl⟩

theorem crossingOf_pair (v : ρ.M) : ρ.crossingOf (ρ.pair v) = ρ.crossingOf v := by
  apply Subtype.ext
  change ({ρ.pair v, ρ.pair (ρ.pair v)} : Finset ρ.M) = {v, ρ.pair v}
  rw [ρ.pair_invol, Finset.pair_comm]

theorem mem_crossingOf (v : ρ.M) : v ∈ (ρ.crossingOf v).1 := by
  simp [crossingOf]

theorem crossingOf_surjective : Function.Surjective ρ.crossingOf := by
  rintro ⟨p, v, rfl⟩
  exact ⟨v, rfl⟩

theorem Crossing.card_eq_two (x : ρ.Crossing) : x.1.card = 2 := by
  obtain ⟨p, v, rfl⟩ := x
  exact Finset.card_pair (ρ.ne_pair v)

theorem crossingOf_eq_iff (v : ρ.M) (x : ρ.Crossing) : ρ.crossingOf v = x ↔ v ∈ x.1 := by
  obtain ⟨p, w, rfl⟩ := x
  constructor
  · intro h; rw [← h]; exact ρ.mem_crossingOf v
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rfl
    · exact ρ.crossingOf_pair w

/-- `|M| = 2 · #crossings`: the occurrence set is the disjoint union of the crossing pairs. -/
theorem card_M_eq_two_mul_card_crossing : Fintype.card ρ.M = 2 * Fintype.card ρ.Crossing := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := ρ.crossingOf) (s := Finset.univ)
    (t := Finset.univ) (fun v _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_const_nat (m := 2), Finset.card_univ, mul_comm]
  intro x _
  have : (Finset.univ.filter (fun v => ρ.crossingOf v = x)) = x.1 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ρ.crossingOf_eq_iff v x
  rw [this, Crossing.card_eq_two]

theorem card_crossing_eq_crossingCount : Fintype.card ρ.Crossing = ρ.crossingCount := by
  unfold crossingCount
  rw [ρ.card_M_eq_two_mul_card_crossing]
  omega

/-! ### Crossing-free components -/

/-- The parametrizing circles without crossing occurrences ("components with no crossing
occurrences", sm-3:1224). -/
def FreeComp : Type := {c : ρ.comps // ∀ v, ρ.comp v ≠ c}

/-- Finitely many crossing-free circles (classical decidability of "carries no occurrence"). -/
noncomputable instance : Fintype ρ.FreeComp := by
  classical unfold FreeComp; infer_instance

end Record


/-! ## D. Named record isomorphisms (def:gauss-record, sm-3:361-365)

"A named record isomorphism is a bijection Φ : M → M' preserving successor, pairing, over/under
bits and these signs. The parametrizing circles are oriented; the finite bijection must preserve
their cyclic orders. It does not prescribe a map at every unmarked parameter and does not permit
traversal reversal."  Preserving the successor (`succ_eq`, with `Φ ∘ s = s' ∘ Φ`, never
`s'⁻¹`) is the cyclic-order clause without reversal; the component bijection `e` is the
multi-component clause of rp:record-polynomial ("a bijection of their components and crossing
occurrences", sm-3:1220-1224). -/

/-- A named record isomorphism: bijections of circles and of occurrences preserving `comp`,
successor, pairing, bits and signs. -/
structure RecordIso (ρ ρ' : Record) where
  /-- bijection of the parametrizing circles, crossing-free ones included -/
  e : ρ.comps ≃ ρ'.comps
  /-- "a bijection Φ : M → M'" -/
  Φ : ρ.M ≃ ρ'.M
  comp_eq : ∀ v, ρ'.comp (Φ v) = e (ρ.comp v)
  /-- "preserving successor" -/
  succ_eq : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v)
  /-- "pairing" -/
  pair_eq : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)
  /-- "over/under bits" -/
  bit_eq : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v
  /-- "and these signs" -/
  sgn_eq : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v

namespace RecordIso

variable {ρ ρ' ρ'' : Record}

/-- Reflexivity. -/
def refl (ρ : Record) : RecordIso ρ ρ where
  e := Equiv.refl _
  Φ := Equiv.refl _
  comp_eq _ := rfl
  succ_eq _ := rfl
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

/-- Symmetry. -/
def symm (i : RecordIso ρ ρ') : RecordIso ρ' ρ where
  e := i.e.symm
  Φ := i.Φ.symm
  comp_eq v := by
    rw [Equiv.eq_symm_apply, ← i.comp_eq, Equiv.apply_symm_apply]
  succ_eq v := by
    rw [Equiv.symm_apply_eq, i.succ_eq, Equiv.apply_symm_apply]
  pair_eq v := by
    rw [Equiv.symm_apply_eq, i.pair_eq, Equiv.apply_symm_apply]
  bit_eq v := by
    have := i.bit_eq (i.Φ.symm v)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  sgn_eq v := by
    have := i.sgn_eq (i.Φ.symm v)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

/-- Transitivity. -/
def trans (i : RecordIso ρ ρ') (j : RecordIso ρ' ρ'') : RecordIso ρ ρ'' where
  e := i.e.trans j.e
  Φ := i.Φ.trans j.Φ
  comp_eq v := by simp only [Equiv.trans_apply, j.comp_eq, i.comp_eq]
  succ_eq v := by simp only [Equiv.trans_apply, i.succ_eq, j.succ_eq]
  pair_eq v := by simp only [Equiv.trans_apply, i.pair_eq, j.pair_eq]
  bit_eq v := by simp only [Equiv.trans_apply, j.bit_eq, i.bit_eq]
  sgn_eq v := by simp only [Equiv.trans_apply, j.sgn_eq, i.sgn_eq]

theorem Φ_pow (i : RecordIso ρ ρ') (n : ℕ) (v : ρ.M) : i.Φ ((ρ.succ ^ n) v) = (ρ'.succ ^ n) (i.Φ v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, i.succ_eq, ih, pow_succ', Perm.mul_apply]

/-- An isomorphism carries successor cycles to successor cycles. -/
theorem sameCycle_iff (i : RecordIso ρ ρ') (v w : ρ.M) :
    ρ'.succ.SameCycle (i.Φ v) (i.Φ w) ↔ ρ.succ.SameCycle v w := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast]; exact i.Φ.injective (by rw [i.Φ_pow, hn])⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← i.Φ_pow, hn]⟩

theorem componentCount_eq (i : RecordIso ρ ρ') : ρ.componentCount = ρ'.componentCount := Fintype.card_congr i.e

theorem card_M_eq (i : RecordIso ρ ρ') : Fintype.card ρ.M = Fintype.card ρ'.M := Fintype.card_congr i.Φ

theorem crossingCount_eq (i : RecordIso ρ ρ') : ρ.crossingCount = ρ'.crossingCount := by
  unfold Record.crossingCount; rw [i.card_M_eq]

theorem sum_sgn_eq (i : RecordIso ρ ρ') : ∑ v, (ρ.sgn v : ℤ) = ∑ v, (ρ'.sgn v : ℤ) :=
  Fintype.sum_equiv i.Φ _ _ (fun v => by rw [i.sgn_eq])

/-- Isomorphic records have the same writhe. -/
theorem writhe_eq (i : RecordIso ρ ρ') : ρ.writhe = ρ'.writhe := by
  unfold Record.writhe; rw [i.sum_sgn_eq]

/-- The crossing sets correspond. -/
theorem crossingOf_eq (i : RecordIso ρ ρ') (v : ρ.M) :
    ρ'.crossingOf (i.Φ v) = ⟨(ρ.crossingOf v).1.map i.Φ.toEmbedding, i.Φ v, by
      simp [Record.crossingOf, Finset.map_insert, i.pair_eq]⟩ := by
  apply Subtype.ext
  simp [Record.crossingOf, Finset.map_insert, i.pair_eq]

end RecordIso

/-! ## E. Switching one crossing (sm-3:940-944, 1058-1062)

"A switch at the first bad crossing keeps the parameter circles and their traversal order. It
changes that first encounter from OVER to UNDER and leaves every other first-encounter
designation unchanged. ... Its chosen crossing sign is negated, since the two ordered
over/under tangents are exchanged."  At the record level: same `comps`, `M`, `comp`, `succ`,
`pair`; the two bits of the crossing of `x` are flipped and its sign negated. -/

namespace Record

variable (ρ : Record)

theorem pair_mem_pair_iff (x v : ρ.M) :
    ρ.pair v ∈ ({x, ρ.pair x} : Finset ρ.M) ↔ v ∈ ({x, ρ.pair x} : Finset ρ.M) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, ρ.pair_eq_iff, ρ.pair_invol]
  exact or_comm

/-- `D^{sw}` at the crossing of the occurrence `x`: flip both over/under bits and negate both
stored signs of that crossing; everything else is unchanged. -/
def switch (x : ρ.M) : Record where
  comps := ρ.comps
  M := ρ.M
  comp := ρ.comp
  succ := ρ.succ
  pair := ρ.pair
  isOver v := if v ∈ ({x, ρ.pair x} : Finset ρ.M) then !ρ.isOver v else ρ.isOver v
  sgn v := if v ∈ ({x, ρ.pair x} : Finset ρ.M) then -ρ.sgn v else ρ.sgn v
  succ_comp := ρ.succ_comp
  succ_cycle := ρ.succ_cycle
  pair_ne := ρ.pair_ne
  pair_invol := ρ.pair_invol
  bit_pair v := by
    by_cases hv : v ∈ ({x, ρ.pair x} : Finset ρ.M)
    · rw [ite_eq_left ((ρ.pair_mem_pair_iff x v).mpr hv), ite_eq_left hv, ρ.bit_pair, Bool.not_not]
    · rw [ite_eq_right (fun h => hv ((ρ.pair_mem_pair_iff x v).mp h)), ite_eq_right hv, ρ.bit_pair]
  sgn_pair v := by
    by_cases hv : v ∈ ({x, ρ.pair x} : Finset ρ.M)
    · rw [ite_eq_left ((ρ.pair_mem_pair_iff x v).mpr hv), ite_eq_left hv, ρ.sgn_pair]
    · rw [ite_eq_right (fun h => hv ((ρ.pair_mem_pair_iff x v).mp h)), ite_eq_right hv, ρ.sgn_pair]
  sgn_ne v := by
    split_ifs
    · exact fun h => ρ.sgn_ne v (SignType.neg_eq_zero_iff.mp h)
    · exact ρ.sgn_ne v

variable (x : ρ.M)

@[simp] theorem switch_comps : (ρ.switch x).comps = ρ.comps := rfl
@[simp] theorem switch_M : (ρ.switch x).M = ρ.M := rfl
@[simp] theorem switch_comp : (ρ.switch x).comp = ρ.comp := rfl
@[simp] theorem switch_succ : (ρ.switch x).succ = ρ.succ := rfl
@[simp] theorem switch_pair : (ρ.switch x).pair = ρ.pair := rfl

theorem switch_isOver (v : ρ.M) :
    (ρ.switch x).isOver v = if v ∈ ({x, ρ.pair x} : Finset ρ.M) then !ρ.isOver v else ρ.isOver v :=
  rfl

theorem switch_sgn (v : ρ.M) :
    (ρ.switch x).sgn v = if v ∈ ({x, ρ.pair x} : Finset ρ.M) then -ρ.sgn v else ρ.sgn v := rfl

@[simp] theorem switch_isOver_self : (ρ.switch x).isOver x = !ρ.isOver x := by
  rw [switch_isOver, ite_eq_left (by simp)]

@[simp] theorem switch_isOver_pair : (ρ.switch x).isOver (ρ.pair x) = !ρ.isOver (ρ.pair x) := by
  rw [switch_isOver, ite_eq_left (by simp)]

theorem switch_isOver_of_ne {v : ρ.M} (h1 : v ≠ x) (h2 : v ≠ ρ.pair x) :
    (ρ.switch x).isOver v = ρ.isOver v := by
  rw [switch_isOver, ite_eq_right (by simp [h1, h2])]

@[simp] theorem switch_sgn_self : (ρ.switch x).sgn x = -ρ.sgn x := by
  rw [switch_sgn, ite_eq_left (by simp)]

@[simp] theorem switch_sgn_pair : (ρ.switch x).sgn (ρ.pair x) = -ρ.sgn x := by
  rw [switch_sgn, ite_eq_left (by simp), ρ.sgn_pair]

theorem switch_sgn_of_ne {v : ρ.M} (h1 : v ≠ x) (h2 : v ≠ ρ.pair x) :
    (ρ.switch x).sgn v = ρ.sgn v := by
  rw [switch_sgn, ite_eq_right (by simp [h1, h2])]

/-- Switching is an involution. -/
theorem switch_switch : (ρ.switch x).switch x = ρ := by
  cases ρ with
  | mk comps M comp succ pair isOver sgn _ _ _ _ _ _ _ =>
    unfold switch
    simp only
    congr 1
    · funext v
      split_ifs <;> simp_all
    · funext v
      split_ifs <;> simp_all

/-- The switch does not depend on which occurrence of the crossing names it. -/
theorem switch_pair_eq : ρ.switch (ρ.pair x) = ρ.switch x := by
  cases ρ with
  | mk comps M comp succ pair isOver sgn _ _ _ hinv _ _ _ =>
    have hs : ({pair x, pair (pair x)} : Finset M) = {x, pair x} := by
      rw [hinv, Finset.pair_comm]
    unfold switch
    simp only
    congr 1
    · funext v; rw [hs]
    · funext v; rw [hs]

/-- The switched crossing is negated, all other stored signs are kept. -/
theorem sum_sgn_switch :
    ∑ v, ((ρ.switch x).sgn v : ℤ) = ∑ v, (ρ.sgn v : ℤ) + (-2 * (ρ.sgn x : ℤ)) * 2 := by
  have h1 : ∀ v : ρ.M, ((ρ.switch x).sgn v : ℤ) =
      (ρ.sgn v : ℤ) + (if v ∈ ({x, ρ.pair x} : Finset ρ.M) then -2 * (ρ.sgn v : ℤ) else 0) := by
    intro v
    rw [switch_sgn]
    split_ifs
    · rw [SignType.coe_neg]; ring
    · ring
  calc ∑ v, ((ρ.switch x).sgn v : ℤ)
      = ∑ v : ρ.M, ((ρ.sgn v : ℤ) +
          (if v ∈ ({x, ρ.pair x} : Finset ρ.M) then -2 * (ρ.sgn v : ℤ) else 0)) :=
        Finset.sum_congr rfl (fun v _ => h1 v)
    _ = ∑ v, (ρ.sgn v : ℤ) + (-2 * (ρ.sgn x : ℤ)) * 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_pair (ρ.ne_pair x), ρ.sgn_pair]
        ring

/-- "Its chosen crossing sign is negated": the writhe drops by twice the sign of the
switched crossing. -/
theorem writhe_switch : (ρ.switch x).writhe = ρ.writhe - 2 * (ρ.sgn x : ℤ) := by
  unfold writhe
  rw [sum_sgn_switch, Int.add_mul_ediv_right _ _ two_ne_zero]
  ring

theorem crossingCount_switch : (ρ.switch x).crossingCount = ρ.crossingCount := rfl

theorem componentCount_switch : (ρ.switch x).componentCount = ρ.componentCount := rfl

end Record

/-- An isomorphism carries the occurrence pair of the crossing of `x` to that of `Φ x`. -/
theorem RecordIso.mem_pair_iff {ρ ρ' : Record} (i : RecordIso ρ ρ') (x v : ρ.M) :
    i.Φ v ∈ ({i.Φ x, ρ'.pair (i.Φ x)} : Finset ρ'.M) ↔ v ∈ ({x, ρ.pair x} : Finset ρ.M) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, ← i.pair_eq, i.Φ.injective.eq_iff]

/-- A named record isomorphism carries the switch at `x` to the switch at `Φ x` (the record half
of the bridge theorem `record (switch D x) ≅ (record D).switch x`). -/
def RecordIso.switch {ρ ρ' : Record} (i : RecordIso ρ ρ') (x : ρ.M) :
    RecordIso (ρ.switch x) (ρ'.switch (i.Φ x)) where
  e := i.e
  Φ := i.Φ
  comp_eq := i.comp_eq
  succ_eq := i.succ_eq
  pair_eq := i.pair_eq
  bit_eq := by
    show ∀ v : ρ.M, (ρ'.switch (i.Φ x)).isOver (i.Φ v) = (ρ.switch x).isOver v
    intro v
    rw [Record.switch_isOver, Record.switch_isOver]
    by_cases hv : v ∈ ({x, ρ.pair x} : Finset ρ.M)
    · rw [ite_eq_left ((i.mem_pair_iff x v).mpr hv), ite_eq_left hv, i.bit_eq]
    · rw [ite_eq_right (fun h => hv ((i.mem_pair_iff x v).mp h)), ite_eq_right hv, i.bit_eq]
  sgn_eq := by
    show ∀ v : ρ.M, (ρ'.switch (i.Φ x)).sgn (i.Φ v) = (ρ.switch x).sgn v
    intro v
    rw [Record.switch_sgn, Record.switch_sgn]
    by_cases hv : v ∈ ({x, ρ.pair x} : Finset ρ.M)
    · rw [ite_eq_left ((i.mem_pair_iff x v).mpr hv), ite_eq_left hv, i.sgn_eq]
    · rw [ite_eq_right (fun h => hv ((i.mem_pair_iff x v).mp h)), ite_eq_right hv, i.sgn_eq]

/-! ## F. The oriented smoothing (sm-3:1084-1103)

"Oriented smoothing reconnects each incoming strand to the other strand's outgoing end. It
removes just the selected crossing and creates no other crossing in its clean disc. A self
crossing splits one parameter circle into two; a mixed crossing joins two into one. This can be
checked by writing a self-crossing cycle as (x A y B) and replacing it by the two cycles
(x B), (y A) before erasing x, y. For a mixed crossing, the cycles (x A), (y B) become (x B y A)
before erasing the marks. Empty resulting occurrence words are still circles."

Record rendering (Proposal #2's formulas, adopted by the design panel): with `y = τ x`,
`M' = {m // m ∉ {x, τ x}}`, the new successor is the first return of the reconnected successor
`s₁ = s ∘ swap x y` (the cycles `(x B), (y A)` resp. `(x B y A)` before erasing) to `M'`; on the
generic case this is exactly `s'(s⁻¹ x) = s y`, `s'(s⁻¹ y) = s x` and `s' = s` elsewhere
(`smooth_succ_val_*` below; the degenerate cases with `s y = y` or `s x = x` skip one more step).
The components of the smoothing are the cycles of `s₁` (so an emptied circle stays a component)
together with the crossing-free circles of `ρ`. -/

namespace Record

variable (ρ : Record) (x : ρ.M)

/-- `s₁ = s ∘ swap x (τ x)`: the successor "before erasing x, y" (sm-3:1093-1096). -/
def reconnect : Perm ρ.M := ρ.succ * swap x (ρ.pair x)

theorem reconnect_apply_of_ne {v : ρ.M} (h1 : v ≠ x) (h2 : v ≠ ρ.pair x) :
    ρ.reconnect x v = ρ.succ v :=
  mul_swap_apply_of_ne_of_ne _ _ _ h1 h2

theorem reconnect_apply_self : ρ.reconnect x x = ρ.succ (ρ.pair x) :=
  mul_swap_apply_left _ _ _

theorem reconnect_apply_pair : ρ.reconnect x (ρ.pair x) = ρ.succ x :=
  mul_swap_apply_right _ _ _

theorem reconnect_pair : ρ.reconnect (ρ.pair x) = ρ.reconnect x := by
  unfold reconnect
  rw [ρ.pair_invol, swap_comm]

/-- "(x A y B) ↦ (x B), (y A)": when the word `A` after `x` is empty (`s x = y`), the circle
`(y)` is emptied and `y` becomes a fixed point of `s₁`. -/
theorem reconnect_fixed_pair_of_succ_eq (h : ρ.succ x = ρ.pair x) :
    ρ.reconnect x (ρ.pair x) = ρ.pair x := by
  rw [reconnect_apply_pair, h]

theorem reconnect_fixed_self_of_succ_eq (h : ρ.succ (ρ.pair x) = x) :
    ρ.reconnect x x = x := by
  rw [reconnect_apply_self, h]

/-- The retained occurrences `M' = {m // m ∉ {x, τ x}}`. -/
def SmoothKeep (v : ρ.M) : Prop := v ∉ ({x, ρ.pair x} : Finset ρ.M)

/-- Retention is decidable (occurrences carry decidable equality). -/
instance : DecidablePred (ρ.SmoothKeep x) := fun v =>
  inferInstanceAs (Decidable (v ∉ ({x, ρ.pair x} : Finset ρ.M)))

theorem smoothKeep_iff (v : ρ.M) : ρ.SmoothKeep x v ↔ v ≠ x ∧ v ≠ ρ.pair x := by
  unfold SmoothKeep
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]

theorem smoothKeep_pair_iff (v : ρ.M) : ρ.SmoothKeep x (ρ.pair v) ↔ ρ.SmoothKeep x v := by
  unfold SmoothKeep
  rw [ρ.pair_mem_pair_iff]

theorem not_smoothKeep_self : ¬ ρ.SmoothKeep x x := by
  rw [smoothKeep_iff]; simp

theorem not_smoothKeep_pair : ¬ ρ.SmoothKeep x (ρ.pair x) := by
  rw [smoothKeep_iff]; simp

theorem reconnect_apply_of_smoothKeep {v : ρ.M} (hv : ρ.SmoothKeep x v) :
    ρ.reconnect x v = ρ.succ v :=
  ρ.reconnect_apply_of_ne x ((ρ.smoothKeep_iff x v).mp hv).1 ((ρ.smoothKeep_iff x v).mp hv).2

/-- The set of cycles (orbits) of a permutation of a finite type. -/
instance cycleQuotientFintype {α : Type*} [Fintype α] [DecidableEq α] (f : Perm α) :
    Fintype (Quotient (Perm.SameCycle.setoid f)) :=
  @Quotient.fintype _ _ _ (fun a b => inferInstanceAs (Decidable (f.SameCycle a b)))

/-- The components of the smoothing: the cycles of the reconnected successor `s₁` ("Empty
resulting occurrence words are still circles") plus the crossing-free circles of `ρ`. -/
def SmoothComps : Type := Quotient (Perm.SameCycle.setoid (ρ.reconnect x)) ⊕ ρ.FreeComp

/-- Finitely many components of the smoothing. -/
noncomputable instance : Fintype (ρ.SmoothComps x) := by
  unfold SmoothComps; infer_instance

theorem smoothKeep_pair_eq (v : ρ.M) : ρ.SmoothKeep (ρ.pair x) v ↔ ρ.SmoothKeep x v := by
  unfold SmoothKeep
  rw [ρ.pair_invol, Finset.pair_comm]

/-- The smoothed successor: the first return of `s₁` to the retained occurrences. -/
noncomputable def smoothSucc : Perm {v : ρ.M // ρ.SmoothKeep x v} :=
  firstReturn (ρ.reconnect x) (ρ.SmoothKeep x)

/-- The oriented smoothing `D⁰` of `D` at the crossing of the occurrence `x` (sm-3:1084-1103). -/
noncomputable def smooth : Record where
  comps := ρ.SmoothComps x
  M := {v : ρ.M // ρ.SmoothKeep x v}
  comp v := Sum.inl (Quotient.mk _ v.1)
  succ := ρ.smoothSucc x
  pair := ρ.pair.subtypePerm (ρ.smoothKeep_pair_iff x)
  isOver v := ρ.isOver v.1
  sgn v := ρ.sgn v.1
  succ_comp v := by
    apply congrArg Sum.inl
    apply Quotient.sound
    exact (sameCycle_firstReturn_apply (ρ.reconnect x) (ρ.SmoothKeep x) v).symm
  succ_cycle v w h := by
    have h' : (ρ.reconnect x).SameCycle v.1 w.1 := Quotient.exact (Sum.inl.inj h)
    exact firstReturn_sameCycle_of_sameCycle (ρ.reconnect x) (ρ.SmoothKeep x) h'
  pair_ne v h := ρ.pair_ne v.1 (congrArg Subtype.val h)
  pair_invol v := Subtype.ext (ρ.pair_invol v.1)
  bit_pair v := ρ.bit_pair v.1
  sgn_pair v := ρ.sgn_pair v.1
  sgn_ne v := ρ.sgn_ne v.1

@[simp] theorem smooth_comps : (ρ.smooth x).comps = ρ.SmoothComps x := rfl
@[simp] theorem smooth_M : (ρ.smooth x).M = {v : ρ.M // ρ.SmoothKeep x v} := rfl
theorem smooth_comp (v : (ρ.smooth x).M) :
    (ρ.smooth x).comp v = Sum.inl (Quotient.mk _ v.1) := rfl
@[simp] theorem smooth_isOver (v : (ρ.smooth x).M) : (ρ.smooth x).isOver v = ρ.isOver v.1 := rfl
@[simp] theorem smooth_sgn (v : (ρ.smooth x).M) : (ρ.smooth x).sgn v = ρ.sgn v.1 := rfl
@[simp] theorem smooth_pair_val (v : (ρ.smooth x).M) :
    ((ρ.smooth x).pair v).1 = ρ.pair v.1 := rfl

/-- The smoothed successor, unfolded: the first return of `s₁` to the retained occurrences. -/
theorem smooth_succ_val (v : (ρ.smooth x).M) :
    ((ρ.smooth x).succ v).1 =
      ((ρ.reconnect x) ^ returnTime (ρ.reconnect x) (ρ.SmoothKeep x) v.1 v.2) v.1 := rfl

/-- Two retained occurrences lie on one component of the smoothing iff they lie on one cycle of
the reconnected successor `s₁`. -/
theorem smooth_comp_eq_iff (v w : (ρ.smooth x).M) :
    (ρ.smooth x).comp v = (ρ.smooth x).comp w ↔ (ρ.reconnect x).SameCycle v.1 w.1 := by
  rw [smooth_comp, smooth_comp]
  constructor
  · intro h; exact Quotient.exact (Sum.inl.inj h)
  · intro h; exact congrArg Sum.inl (Quotient.sound h)

/-- The smoothed successor agrees with `s` away from the erased crossing ("It removes just the
selected crossing"). -/
theorem smooth_succ_val_of_not_mem (v : (ρ.smooth x).M) (h : ρ.SmoothKeep x (ρ.succ v.1)) :
    ((ρ.smooth x).succ v).1 = ρ.succ v.1 := by
  have h1 : ρ.reconnect x v.1 = ρ.succ v.1 := ρ.reconnect_apply_of_smoothKeep x v.2
  rw [← h1]
  exact firstReturn_apply_of_mem (ρ.reconnect x) (ρ.SmoothKeep x) v (h1 ▸ h)

/-- `s'(s⁻¹ x) = s (τ x)`: the incoming strand at `x` is reconnected to the outgoing end at
`τ x` (generic case: `τ x` is not alone on its circle). -/
theorem smooth_succ_val_of_succ_eq (v : (ρ.smooth x).M) (h : ρ.succ v.1 = x)
    (hy : ρ.succ (ρ.pair x) ≠ ρ.pair x) : ((ρ.smooth x).succ v).1 = ρ.succ (ρ.pair x) := by
  have hv := (ρ.smoothKeep_iff x v.1).mp v.2
  have h1 : ρ.reconnect x v.1 = x := by rw [ρ.reconnect_apply_of_smoothKeep x v.2, h]
  have h2 : ρ.reconnect x (ρ.reconnect x v.1) = ρ.succ (ρ.pair x) := by
    rw [h1, reconnect_apply_self]
  rw [← h2]
  apply firstReturn_apply_of_not_mem
  · rw [h1]; exact ρ.not_smoothKeep_self x
  · rw [h2, smoothKeep_iff]
    refine ⟨fun hc => hv.2 ?_, hy⟩
    exact ρ.succ.injective (h.trans hc.symm)

/-- Degenerate case of `s'(s⁻¹ x)`: when `τ x` is alone on its circle (`s (τ x) = τ x`, the word
`B` is empty) the first return continues to `s x`. -/
theorem smooth_succ_val_of_succ_eq' (v : (ρ.smooth x).M) (h : ρ.succ v.1 = x)
    (hy : ρ.succ (ρ.pair x) = ρ.pair x) : ((ρ.smooth x).succ v).1 = ρ.succ x := by
  have hv := (ρ.smoothKeep_iff x v.1).mp v.2
  have h1 : ρ.reconnect x v.1 = x := by rw [ρ.reconnect_apply_of_smoothKeep x v.2, h]
  have h2 : ρ.reconnect x (ρ.reconnect x v.1) = ρ.pair x := by
    rw [h1, reconnect_apply_self, hy]
  have h3 : ρ.reconnect x (ρ.reconnect x (ρ.reconnect x v.1)) = ρ.succ x := by
    rw [h2, reconnect_apply_pair]
  rw [← h3]
  apply firstReturn_apply_of_not_mem₂
  · rw [h1]; exact ρ.not_smoothKeep_self x
  · rw [h2]; exact ρ.not_smoothKeep_pair x
  · rw [h3, smoothKeep_iff]
    constructor
    · intro hc; exact hv.1 (ρ.succ.injective (h.trans hc.symm))
    · intro hc; exact ρ.ne_pair x (ρ.succ.injective (hc.trans hy.symm))

/-- `s'(s⁻¹ y) = s x` for `y = τ x`: the incoming strand at `τ x` is reconnected to the outgoing
end at `x` (generic case: `x` is not alone on its circle). -/
theorem smooth_succ_val_of_succ_eq_pair (v : (ρ.smooth x).M) (h : ρ.succ v.1 = ρ.pair x)
    (hx : ρ.succ x ≠ x) : ((ρ.smooth x).succ v).1 = ρ.succ x := by
  have hv := (ρ.smoothKeep_iff x v.1).mp v.2
  have h1 : ρ.reconnect x v.1 = ρ.pair x := by rw [ρ.reconnect_apply_of_smoothKeep x v.2, h]
  have h2 : ρ.reconnect x (ρ.reconnect x v.1) = ρ.succ x := by
    rw [h1, reconnect_apply_pair]
  rw [← h2]
  apply firstReturn_apply_of_not_mem
  · rw [h1]; exact ρ.not_smoothKeep_pair x
  · rw [h2, smoothKeep_iff]
    refine ⟨hx, fun hc => hv.1 ?_⟩
    exact ρ.succ.injective (h.trans hc.symm)

/-- Degenerate case of `s'(s⁻¹ y)`: when `x` is alone on its circle (`s x = x`, the word `A` is
empty) the first return continues to `s (τ x)`. -/
theorem smooth_succ_val_of_succ_eq_pair' (v : (ρ.smooth x).M) (h : ρ.succ v.1 = ρ.pair x)
    (hx : ρ.succ x = x) : ((ρ.smooth x).succ v).1 = ρ.succ (ρ.pair x) := by
  have hv := (ρ.smoothKeep_iff x v.1).mp v.2
  have h1 : ρ.reconnect x v.1 = ρ.pair x := by rw [ρ.reconnect_apply_of_smoothKeep x v.2, h]
  have h2 : ρ.reconnect x (ρ.reconnect x v.1) = x := by
    rw [h1, reconnect_apply_pair, hx]
  have h3 : ρ.reconnect x (ρ.reconnect x (ρ.reconnect x v.1)) = ρ.succ (ρ.pair x) := by
    rw [h2, reconnect_apply_self]
  rw [← h3]
  apply firstReturn_apply_of_not_mem₂
  · rw [h1]; exact ρ.not_smoothKeep_pair x
  · rw [h2]; exact ρ.not_smoothKeep_self x
  · rw [h3, smoothKeep_iff]
    constructor
    · intro hc; exact ρ.ne_pair x (ρ.succ.injective (hx.trans hc.symm))
    · intro hc; exact hv.2 (ρ.succ.injective (h.trans hc.symm))

/-- "Its crossing count is N-1": two occurrences are erased. -/
theorem card_M_smooth : Fintype.card (ρ.smooth x).M = Fintype.card ρ.M - 2 := by
  have h := Fintype.card_subtype_compl (fun v : ρ.M => v ∈ ({x, ρ.pair x} : Finset ρ.M))
  rw [Fintype.card_coe, Finset.card_pair (ρ.ne_pair x)] at h
  exact (Fintype.card_congr (Equiv.refl _)).trans h

theorem crossingCount_smooth : (ρ.smooth x).crossingCount = ρ.crossingCount - 1 := by
  unfold crossingCount
  rw [card_M_smooth]
  have := ρ.two_mul_crossingCount
  unfold crossingCount at this
  omega

/-- The emptied circle: if `s x = τ x` (the word `A` is empty) the `s₁`-cycle `{τ x}` is a
component of the smoothing carrying no occurrence ("Empty resulting occurrence words are still
circles"). -/
theorem smooth_emptied_circle (h : ρ.succ x = ρ.pair x) (v : (ρ.smooth x).M) :
    (ρ.smooth x).comp v ≠ Sum.inl (Quotient.mk _ (ρ.pair x)) := by
  intro hc
  have hsc : (ρ.reconnect x).SameCycle v.1 (ρ.pair x) := Quotient.exact (Sum.inl.inj hc)
  have hfix : Function.IsFixedPt (ρ.reconnect x) (ρ.pair x) :=
    ρ.reconnect_fixed_pair_of_succ_eq x h
  exact ρ.not_smoothKeep_pair x (hsc.eq_of_right hfix ▸ v.2)

/-- Smoothing at `τ x` is the smoothing at `x` (the operation depends on the crossing only). -/
noncomputable def smoothPairIso : RecordIso (ρ.smooth (ρ.pair x)) (ρ.smooth x) where
  e := Equiv.sumCongr
    (Quotient.congr (Equiv.refl _) (fun a b => by
      show (ρ.reconnect (ρ.pair x)).SameCycle a b ↔ (ρ.reconnect x).SameCycle a b
      rw [ρ.reconnect_pair]))
    (Equiv.refl _)
  Φ := Equiv.subtypeEquivRight (ρ.smoothKeep_pair_eq x)
  comp_eq v := by
    rw [smooth_comp, smooth_comp]
    rfl
  succ_eq v := by
    apply Subtype.ext
    have h1 := ρ.smooth_succ_val (ρ.pair x) v
    have h2 := ρ.smooth_succ_val x ⟨v.1, (ρ.smoothKeep_pair_eq x v.1).mp v.2⟩
    refine h1.trans (Eq.trans ?_ h2.symm)
    have hr := ρ.reconnect_pair x
    have : returnTime (ρ.reconnect (ρ.pair x)) (ρ.SmoothKeep (ρ.pair x)) v.1 v.2 =
        returnTime (ρ.reconnect x) (ρ.SmoothKeep x) v.1 ((ρ.smoothKeep_pair_eq x v.1).mp v.2) := by
      rw [returnTime_eq_iff]
      simp only [hr, ρ.smoothKeep_pair_eq]
      exact ⟨⟨returnTime_pos _ _ _ _, returnTime_spec _ _ _ _⟩,
        fun j hj hj' => returnTime_min _ _ _ _ hj'.1 hj hj'.2⟩
    rw [this, hr]
  pair_eq v := rfl
  bit_eq v := rfl
  sgn_eq v := rfl

/-- A self crossing: both occurrences lie on one parametrizing circle ("A self crossing splits
one parameter circle into two; a mixed crossing joins two into one", sm-3:1089-1090). -/
def IsSelfCrossing : Prop := ρ.comp x = ρ.comp (ρ.pair x)

theorem isSelfCrossing_pair : ρ.IsSelfCrossing (ρ.pair x) ↔ ρ.IsSelfCrossing x := by
  unfold IsSelfCrossing; rw [ρ.pair_invol]; exact eq_comm

theorem isSelfCrossing_iff_sameCycle :
    ρ.IsSelfCrossing x ↔ ρ.succ.SameCycle x (ρ.pair x) :=
  (ρ.sameCycle_iff_comp_eq x (ρ.pair x)).symm

/-- "a mixed crossing joins two into one": at a mixed crossing the two circles carrying `x` and
`τ x` become one cycle of the reconnected successor `(x B y A)`. -/
theorem reconnect_sameCycle_pair_of_mixed (h : ¬ ρ.IsSelfCrossing x) :
    (ρ.reconnect x).SameCycle x (ρ.pair x) :=
  mul_swap_sameCycle_self ρ.succ x (ρ.pair x)
    (fun hc => h ((ρ.isSelfCrossing_iff_sameCycle x).mpr hc))

/-- At a mixed crossing every occurrence of the two joined circles lies on the merged cycle. -/
theorem reconnect_sameCycle_of_mixed (h : ¬ ρ.IsSelfCrossing x) (v : ρ.M)
    (hv : ρ.comp v = ρ.comp x ∨ ρ.comp v = ρ.comp (ρ.pair x)) :
    (ρ.reconnect x).SameCycle v x := by
  have hne : ¬ ρ.succ.SameCycle x (ρ.pair x) :=
    fun hc => h ((ρ.isSelfCrossing_iff_sameCycle x).mpr hc)
  rcases hv with hv | hv
  · exact mul_swap_sameCycle_left ρ.succ x (ρ.pair x) hne (ρ.succ_cycle v x hv)
  · exact (mul_swap_sameCycle_right ρ.succ x (ρ.pair x) hne (ρ.succ_cycle v _ hv)).trans
      (ρ.reconnect_sameCycle_pair_of_mixed x h).symm

/-- "A self crossing splits one parameter circle into two": at a self crossing the cycles of the
reconnected successor refine the old cycles (no two old circles are joined). -/
theorem reconnect_sameCycle_refines_of_self (h : ρ.IsSelfCrossing x) {v w : ρ.M}
    (hvw : (ρ.reconnect x).SameCycle v w) : ρ.succ.SameCycle v w :=
  SM.Carrier.sameCycle_mul_swap_refines ρ.succ x (ρ.pair x)
    ((ρ.isSelfCrossing_iff_sameCycle x).mp h) hvw

/-- On the circles not carrying the smoothed crossing the smoothed successor is the old one. -/
theorem smooth_succ_val_of_comp_ne (v : (ρ.smooth x).M) (h1 : ρ.comp v.1 ≠ ρ.comp x)
    (h2 : ρ.comp v.1 ≠ ρ.comp (ρ.pair x)) : ((ρ.smooth x).succ v).1 = ρ.succ v.1 := by
  apply ρ.smooth_succ_val_of_not_mem
  rw [smoothKeep_iff]
  constructor
  · intro hc; exact h1 ((ρ.succ_comp v.1).symm.trans (congrArg ρ.comp hc))
  · intro hc; exact h2 ((ρ.succ_comp v.1).symm.trans (congrArg ρ.comp hc))

end Record


/-! ## G. Block restriction (mp:stack, sm-3:1495-1500)

"Let D be an actual nonempty diagram whose components are partitioned into q ≥ 1 nonempty tagged
blocks. ... Let D_i be the actual restriction retaining all components in block i and all
crossings internal to it."  Record rendering: keep the circles of the block `B` (crossing-free
ones and those whose crossings all leave the block included), keep the occurrences whose
crossing is internal to `B` (both occurrences on circles of `B`), and let the successor be the
first return of `s` to the retained occurrences. -/

namespace Record

variable (ρ : Record) (B : Finset ρ.comps)

/-- Retained occurrences: "all crossings internal to it" — both occurrences of the crossing lie
on circles of the block. -/
def RestrictKeep (v : ρ.M) : Prop := ρ.comp v ∈ B ∧ ρ.comp (ρ.pair v) ∈ B

theorem restrictKeep_pair_iff (v : ρ.M) : ρ.RestrictKeep B (ρ.pair v) ↔ ρ.RestrictKeep B v := by
  unfold RestrictKeep
  rw [ρ.pair_invol]
  exact and_comm

/-- Membership of a component in the block is decided classically (the component type carries
no decidable equality). -/
noncomputable instance instDecidablePredRestrictKeep : DecidablePred (ρ.RestrictKeep B) :=
  Classical.decPred _

/-- `D_i`: the restriction of the record to the block `B` (components of `B`, crossings internal
to `B`, first-return successor). -/
noncomputable def restrict : Record where
  comps := {c : ρ.comps // c ∈ B}
  M := {v : ρ.M // ρ.RestrictKeep B v}
  comp v := ⟨ρ.comp v.1, v.2.1⟩
  succ := firstReturn ρ.succ (ρ.RestrictKeep B)
  pair := ρ.pair.subtypePerm (ρ.restrictKeep_pair_iff B)
  isOver v := ρ.isOver v.1
  sgn v := ρ.sgn v.1
  succ_comp v := by
    apply Subtype.ext
    show ρ.comp (firstReturn ρ.succ (ρ.RestrictKeep B) v).1 = ρ.comp v.1
    rw [firstReturn_apply, ρ.comp_pow]
  succ_cycle v w h := by
    have h' : ρ.comp v.1 = ρ.comp w.1 := congrArg Subtype.val h
    exact firstReturn_sameCycle_of_sameCycle _ _ (ρ.succ_cycle _ _ h')
  pair_ne v h := ρ.pair_ne v.1 (congrArg Subtype.val h)
  pair_invol v := Subtype.ext (ρ.pair_invol v.1)
  bit_pair v := ρ.bit_pair v.1
  sgn_pair v := ρ.sgn_pair v.1
  sgn_ne v := ρ.sgn_ne v.1

@[simp] theorem restrict_comps : (ρ.restrict B).comps = {c : ρ.comps // c ∈ B} := rfl
@[simp] theorem restrict_M : (ρ.restrict B).M = {v : ρ.M // ρ.RestrictKeep B v} := rfl
@[simp] theorem restrict_comp_val (v : (ρ.restrict B).M) :
    ((ρ.restrict B).comp v).1 = ρ.comp v.1 := rfl
@[simp] theorem restrict_isOver (v : (ρ.restrict B).M) :
    (ρ.restrict B).isOver v = ρ.isOver v.1 := rfl
@[simp] theorem restrict_sgn (v : (ρ.restrict B).M) : (ρ.restrict B).sgn v = ρ.sgn v.1 := rfl
@[simp] theorem restrict_pair_val (v : (ρ.restrict B).M) :
    ((ρ.restrict B).pair v).1 = ρ.pair v.1 := rfl

/-- Where the next occurrence is retained, the restricted successor is the old one. -/
theorem restrict_succ_val_of_keep (v : (ρ.restrict B).M) (h : ρ.RestrictKeep B (ρ.succ v.1)) :
    ((ρ.restrict B).succ v).1 = ρ.succ v.1 :=
  firstReturn_apply_of_mem ρ.succ (ρ.RestrictKeep B) v h

/-- The restricted successor stays on the old successor cycle (block components are unions of
old components). -/
theorem restrict_succ_sameCycle (v : (ρ.restrict B).M) :
    ρ.succ.SameCycle v.1 ((ρ.restrict B).succ v).1 :=
  sameCycle_firstReturn_apply ρ.succ (ρ.RestrictKeep B) v

theorem componentCount_restrict : (ρ.restrict B).componentCount = B.card :=
  (Fintype.card_congr (Equiv.refl _)).trans (Fintype.card_coe B)

/-- Restricting to every component changes nothing. -/
noncomputable def restrictUnivIso : RecordIso (ρ.restrict Finset.univ) ρ where
  e := Equiv.subtypeUnivEquiv (fun c => Finset.mem_univ c)
  Φ := Equiv.subtypeUnivEquiv (fun _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
  comp_eq _ := rfl
  succ_eq v := ρ.restrict_succ_val_of_keep Finset.univ v ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

end Record

/-! ## H. The marked join (mp:join, sm-3:1370-1385)

"A marked diagram is a nonempty actual diagram with a specified closed nonsingular oriented
interval I on one component; I contains no crossing and is contained in a clean disc. ... A
marked join of (A, I_A) and (B, I_B) cuts a smaller open interval inside each mark and joins
the oriented ends crosswise, preserving the surviving collars. There are no additional crossings
in the joining arcs. Its finite data are precise: concatenate the marked component cycles at
their marked gaps, retain every other component, and keep exactly all old crossing pairings,
bits and signs. The component number is c(A)+c(B)-1."

Record rendering: a mark is a circle together with its gap — the occurrence just before the
interval `I`, or no occurrence when the marked circle is crossing-free ("an arbitrary
crossing-free marked component", mp:join).  The joined occurrence set is `M_A ⊕ M_B`; the
successor is `s_A ⊕ s_B` composed with the transposition of the two gap occurrences (after the
gap of `A` continue into `B` just after its gap, and back), which concatenates the two marked
cycles; pairings, bits and signs are the old ones; the components are those of `A` together
with the unmarked ones of `B`, the marked circle of `B` being merged into the marked circle of
`A`. -/

namespace Record

/-- A marked component with its gap position (mp:join: "a specified closed nonsingular oriented
interval I on one component; I contains no crossing"). `gap = some v` puts the interval just
after the occurrence `v` of the marked circle; `gap = none` is allowed exactly when the marked
circle carries no occurrence. -/
structure Mark (ρ : Record) where
  comp : ρ.comps
  gap : Option ρ.M
  gap_comp : ∀ v, gap = some v → ρ.comp v = comp
  gap_none : gap = none → ∀ v, ρ.comp v ≠ comp

/-- The transposition of the two gap occurrences (the identity when a marked circle is
crossing-free). -/
def gapSwap {α β : Type*} [DecidableEq α] [DecidableEq β] : Option α → Option β → Perm (α ⊕ β)
  | some a, some b => swap (Sum.inl a) (Sum.inr b)
  | _, _ => 1

@[simp] theorem gapSwap_some_some {α β : Type*} [DecidableEq α] [DecidableEq β] (a : α) (b : β) :
    gapSwap (some a) (some b) = swap (Sum.inl a) (Sum.inr b) := rfl

@[simp] theorem gapSwap_none_left {α β : Type*} [DecidableEq α] [DecidableEq β] (b : Option β) :
    gapSwap (none : Option α) b = 1 := by cases b <;> rfl

@[simp] theorem gapSwap_none_right {α β : Type*} [DecidableEq α] [DecidableEq β] (a : Option α) :
    gapSwap a (none : Option β) = 1 := by cases a <;> rfl

section Join

variable {ρ₁ ρ₂ : Record} (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark)

/-- `s_A ⊕ s_B`: the disjoint union of the two successors. -/
def sumSucc (ρ₁ ρ₂ : Record) : Perm (ρ₁.M ⊕ ρ₂.M) := Perm.sumCongr ρ₁.succ ρ₂.succ

theorem sumSucc_sameCycle_inl_iff (a a' : ρ₁.M) :
    (sumSucc ρ₁ ρ₂).SameCycle (Sum.inl a) (Sum.inl a') ↔ ρ₁.comp a = ρ₁.comp a' := by
  rw [sumSucc, sumCongr_sameCycle_inl_iff, ρ₁.sameCycle_iff_comp_eq]

theorem sumSucc_sameCycle_inr_iff (b b' : ρ₂.M) :
    (sumSucc ρ₁ ρ₂).SameCycle (Sum.inr b) (Sum.inr b') ↔ ρ₂.comp b = ρ₂.comp b' := by
  rw [sumSucc, sumCongr_sameCycle_inr_iff, ρ₂.sameCycle_iff_comp_eq]

theorem sumSucc_not_sameCycle_inl_inr (a : ρ₁.M) (b : ρ₂.M) :
    ¬ (sumSucc ρ₁ ρ₂).SameCycle (Sum.inl a) (Sum.inr b) :=
  not_sumCongr_sameCycle_inl_inr _ _ a b

theorem sumSucc_sameCycle_inl_elim (a : ρ₁.M) (z : ρ₁.M ⊕ ρ₂.M)
    (h : (sumSucc ρ₁ ρ₂).SameCycle (Sum.inl a) z) : ∃ c, z = Sum.inl c ∧ ρ₁.comp c = ρ₁.comp a := by
  rcases z with c | c
  · exact ⟨c, rfl, ((sumSucc_sameCycle_inl_iff a c).mp h).symm⟩
  · exact absurd h (sumSucc_not_sameCycle_inl_inr a c)

theorem sumSucc_sameCycle_inr_elim (b : ρ₂.M) (z : ρ₁.M ⊕ ρ₂.M)
    (h : (sumSucc ρ₁ ρ₂).SameCycle (Sum.inr b) z) : ∃ c, z = Sum.inr c ∧ ρ₂.comp c = ρ₂.comp b := by
  rcases z with c | c
  · exact absurd h.symm (sumSucc_not_sameCycle_inl_inr c b)
  · exact ⟨c, rfl, ((sumSucc_sameCycle_inr_iff b c).mp h).symm⟩

/-- The joined successor: `s_A ⊕ s_B` after the transposition of the two gap occurrences. -/
def joinSucc : Perm (ρ₁.M ⊕ ρ₂.M) := sumSucc ρ₁ ρ₂ * gapSwap μ₁.gap μ₂.gap

/-- The unmarked circles of a marked record. -/
def Mark.Unmarked {ρ : Record} (μ : ρ.Mark) : Type := {c : ρ.comps // c ≠ μ.comp}

/-- Finitely many unmarked circles (classical decidability of equality with the marked one). -/
noncomputable instance Mark.instFintypeUnmarked {ρ : Record} (μ : ρ.Mark) : Fintype μ.Unmarked := by
  classical unfold Mark.Unmarked; infer_instance

/-- Equality with the marked circle is decided classically. -/
noncomputable instance Mark.instDecidableEqComp {ρ : Record} (μ : ρ.Mark) (c : ρ.comps) :
    Decidable (c = μ.comp) := Classical.dec _

/-- The joined component map: circles of `A` are kept; the marked circle of `B` is merged into
the marked circle of `A`; the other circles of `B` are kept. -/
noncomputable def joinComp : ρ₁.M ⊕ ρ₂.M → ρ₁.comps ⊕ μ₂.Unmarked :=
  Sum.elim (fun v => Sum.inl (ρ₁.comp v))
    (fun v => if h : ρ₂.comp v = μ₂.comp then Sum.inl μ₁.comp else Sum.inr ⟨ρ₂.comp v, h⟩)

theorem joinComp_inl (a : ρ₁.M) : joinComp μ₁ μ₂ (Sum.inl a) = Sum.inl (ρ₁.comp a) := rfl

theorem joinComp_inr_of_eq (b : ρ₂.M) (h : ρ₂.comp b = μ₂.comp) :
    joinComp μ₁ μ₂ (Sum.inr b) = Sum.inl μ₁.comp := by
  unfold joinComp; rw [Sum.elim_inr, dite_eq_left h]

theorem joinComp_inr_of_ne (b : ρ₂.M) (h : ρ₂.comp b ≠ μ₂.comp) :
    joinComp μ₁ μ₂ (Sum.inr b) = Sum.inr ⟨ρ₂.comp b, h⟩ := by
  unfold joinComp; rw [Sum.elim_inr, dite_eq_right h]

theorem joinComp_inr_succ (b : ρ₂.M) :
    joinComp μ₁ μ₂ (Sum.inr (ρ₂.succ b)) = joinComp μ₁ μ₂ (Sum.inr b) := by
  by_cases hc : ρ₂.comp b = μ₂.comp
  · rw [joinComp_inr_of_eq μ₁ μ₂ _ (by rw [ρ₂.succ_comp]; exact hc), joinComp_inr_of_eq μ₁ μ₂ b hc]
  · rw [joinComp_inr_of_ne μ₁ μ₂ _ (by rw [ρ₂.succ_comp]; exact hc), joinComp_inr_of_ne μ₁ μ₂ b hc]
    exact congrArg Sum.inr (Subtype.ext (ρ₂.succ_comp b))

/-- Points whose whole `f`-cycle is untouched by `g` keep their cycle. -/
theorem sameCycle_of_eqOn_orbit {α : Type*} (f g : Perm α) (v w : α) (hvw : f.SameCycle v w)
    (he : ∀ z, f.SameCycle v z → g z = f z) : g.SameCycle v w := by
  have hU : Set.BijOn f {z | f.SameCycle v z} {z | f.SameCycle v z} := by
    refine ⟨fun z hz => ?_, f.injective.injOn, fun z hz => ⟨f.symm z, ?_, f.apply_symm_apply z⟩⟩
    · exact Perm.sameCycle_apply_right.mpr hz
    · exact Perm.sameCycle_symm_apply_right.mpr hz
  exact (SM.Carrier.sameCycle_congr_of_eqOn_bijOn f g _ hU (fun z hz => (he z hz).symm) v
    (Perm.SameCycle.refl f v) w).mpr hvw

theorem joinSucc_apply_of_ne_gaps (z : ρ₁.M ⊕ ρ₂.M)
    (hz : ∀ g₁ g₂, μ₁.gap = some g₁ → μ₂.gap = some g₂ → z ≠ Sum.inl g₁ ∧ z ≠ Sum.inr g₂) :
    joinSucc μ₁ μ₂ z = sumSucc ρ₁ ρ₂ z := by
  unfold joinSucc
  rcases hg₁ : μ₁.gap with _ | g₁
  · rw [gapSwap_none_left, mul_one]
  rcases hg₂ : μ₂.gap with _ | g₂
  · rw [gapSwap_none_right, mul_one]
  rw [gapSwap_some_some]
  exact mul_swap_apply_of_ne_of_ne _ _ _ (hz g₁ g₂ hg₁ hg₂).1 (hz g₁ g₂ hg₁ hg₂).2

theorem joinSucc_inl_of_ne (a : ρ₁.M) (ha : μ₁.gap ≠ some a) :
    joinSucc μ₁ μ₂ (Sum.inl a) = Sum.inl (ρ₁.succ a) := by
  rw [joinSucc_apply_of_ne_gaps]
  · rfl
  · intro g₁ g₂ hg₁ _
    exact ⟨fun h => ha (by rw [hg₁, Sum.inl.inj h]), Sum.inl_ne_inr⟩

theorem joinSucc_inr_of_ne (b : ρ₂.M) (hb : μ₂.gap ≠ some b) :
    joinSucc μ₁ μ₂ (Sum.inr b) = Sum.inr (ρ₂.succ b) := by
  rw [joinSucc_apply_of_ne_gaps]
  · rfl
  · intro g₁ g₂ _ hg₂
    exact ⟨Sum.inr_ne_inl, fun h => hb (by rw [hg₂, Sum.inr.inj h])⟩

theorem joinSucc_inl_of_none (a : ρ₁.M) (h : μ₂.gap = none) :
    joinSucc μ₁ μ₂ (Sum.inl a) = Sum.inl (ρ₁.succ a) := by
  unfold joinSucc; rw [h, gapSwap_none_right, mul_one]; rfl

theorem joinSucc_inr_of_none (b : ρ₂.M) (h : μ₁.gap = none) :
    joinSucc μ₁ μ₂ (Sum.inr b) = Sum.inr (ρ₂.succ b) := by
  unfold joinSucc; rw [h, gapSwap_none_left, mul_one]; rfl

/-- After the gap of `A`, continue into `B` just after its gap. -/
theorem joinSucc_gap_left {g₁ : ρ₁.M} {g₂ : ρ₂.M} (h₁ : μ₁.gap = some g₁) (h₂ : μ₂.gap = some g₂) :
    joinSucc μ₁ μ₂ (Sum.inl g₁) = Sum.inr (ρ₂.succ g₂) := by
  unfold joinSucc; rw [h₁, h₂, gapSwap_some_some, mul_swap_apply_left]; rfl

/-- After the gap of `B`, continue into `A` just after its gap. -/
theorem joinSucc_gap_right {g₁ : ρ₁.M} {g₂ : ρ₂.M} (h₁ : μ₁.gap = some g₁) (h₂ : μ₂.gap = some g₂) :
    joinSucc μ₁ μ₂ (Sum.inr g₂) = Sum.inl (ρ₁.succ g₁) := by
  unfold joinSucc; rw [h₁, h₂, gapSwap_some_some, mul_swap_apply_right]; rfl

/-- The joined successor stays on the joined components. -/
theorem joinComp_joinSucc (v : ρ₁.M ⊕ ρ₂.M) :
    joinComp μ₁ μ₂ (joinSucc μ₁ μ₂ v) = joinComp μ₁ μ₂ v := by
  rcases hg₁ : μ₁.gap with _ | g₁
  · rcases v with a | b
    · rw [joinSucc_inl_of_ne μ₁ μ₂ a (by rw [hg₁]; exact (Option.some_ne_none a).symm),
        joinComp_inl, joinComp_inl, ρ₁.succ_comp]
    · rw [joinSucc_inr_of_none μ₁ μ₂ b hg₁, joinComp_inr_succ]
  rcases hg₂ : μ₂.gap with _ | g₂
  · rcases v with a | b
    · rw [joinSucc_inl_of_none μ₁ μ₂ a hg₂, joinComp_inl, joinComp_inl, ρ₁.succ_comp]
    · rw [joinSucc_inr_of_ne μ₁ μ₂ b (by rw [hg₂]; exact (Option.some_ne_none b).symm),
        joinComp_inr_succ]
  rcases v with a | b
  · by_cases ha : a = g₁
    · subst ha
      rw [joinSucc_gap_left μ₁ μ₂ hg₁ hg₂, joinComp_inl,
        joinComp_inr_of_eq μ₁ μ₂ _ (by rw [ρ₂.succ_comp]; exact μ₂.gap_comp g₂ hg₂),
        μ₁.gap_comp a hg₁]
    · rw [joinSucc_inl_of_ne μ₁ μ₂ a (by rw [hg₁]; exact fun h => ha (Option.some.inj h).symm),
        joinComp_inl, joinComp_inl, ρ₁.succ_comp]
  · by_cases hb : b = g₂
    · subst hb
      rw [joinSucc_gap_right μ₁ μ₂ hg₁ hg₂, joinComp_inl, ρ₁.succ_comp, μ₁.gap_comp g₁ hg₁,
        joinComp_inr_of_eq μ₁ μ₂ b (μ₂.gap_comp b hg₂)]
    · rw [joinSucc_inr_of_ne μ₁ μ₂ b (by rw [hg₂]; exact fun h => hb (Option.some.inj h).symm),
        joinComp_inr_succ]

/-- Occurrences of `A` on the marked circle of `A` reach the gap of `A` along the joined
successor. -/
theorem joinSucc_sameCycle_gap_left {g₁ : ρ₁.M} {g₂ : ρ₂.M} (h₁ : μ₁.gap = some g₁)
    (h₂ : μ₂.gap = some g₂) (a : ρ₁.M) (ha : ρ₁.comp a = μ₁.comp) :
    (joinSucc μ₁ μ₂).SameCycle (Sum.inl a) (Sum.inl g₁) := by
  have hF : (sumSucc ρ₁ ρ₂).SameCycle (Sum.inl a) (Sum.inl g₁) :=
    (sumSucc_sameCycle_inl_iff a g₁).mpr (ha.trans (μ₁.gap_comp g₁ h₁).symm)
  unfold joinSucc; rw [h₁, h₂, gapSwap_some_some]
  exact mul_swap_sameCycle_left _ _ _ (sumSucc_not_sameCycle_inl_inr g₁ g₂) hF

theorem joinSucc_sameCycle_gap_right {g₁ : ρ₁.M} {g₂ : ρ₂.M} (h₁ : μ₁.gap = some g₁)
    (h₂ : μ₂.gap = some g₂) (b : ρ₂.M) (hb : ρ₂.comp b = μ₂.comp) :
    (joinSucc μ₁ μ₂).SameCycle (Sum.inr b) (Sum.inr g₂) := by
  have hF : (sumSucc ρ₁ ρ₂).SameCycle (Sum.inr b) (Sum.inr g₂) :=
    (sumSucc_sameCycle_inr_iff b g₂).mpr (hb.trans (μ₂.gap_comp g₂ h₂).symm)
  unfold joinSucc; rw [h₁, h₂, gapSwap_some_some]
  exact mul_swap_sameCycle_right _ _ _ (sumSucc_not_sameCycle_inl_inr g₁ g₂) hF

/-- "concatenate the marked component cycles at their marked gaps": the two gaps lie on one
joined cycle. -/
theorem joinSucc_sameCycle_gaps {g₁ : ρ₁.M} {g₂ : ρ₂.M} (h₁ : μ₁.gap = some g₁)
    (h₂ : μ₂.gap = some g₂) : (joinSucc μ₁ μ₂).SameCycle (Sum.inl g₁) (Sum.inr g₂) := by
  unfold joinSucc; rw [h₁, h₂, gapSwap_some_some]
  exact mul_swap_sameCycle_self _ _ _ (sumSucc_not_sameCycle_inl_inr g₁ g₂)

/-- Occurrences on unmarked circles of `A` keep their cycle. -/
theorem joinSucc_sameCycle_inl_of_ne (a a' : ρ₁.M) (ha : ρ₁.comp a ≠ μ₁.comp)
    (h : ρ₁.comp a = ρ₁.comp a') :
    (joinSucc μ₁ μ₂).SameCycle (Sum.inl a) (Sum.inl a') := by
  apply sameCycle_of_eqOn_orbit (sumSucc ρ₁ ρ₂) _ _ _ ((sumSucc_sameCycle_inl_iff a a').mpr h)
  intro z hz
  obtain ⟨c, rfl, hc⟩ := sumSucc_sameCycle_inl_elim a z hz
  apply joinSucc_apply_of_ne_gaps
  intro g₁ g₂ hg₁ _
  refine ⟨fun hcg => ha ?_, Sum.inl_ne_inr⟩
  rw [← hc, Sum.inl.inj hcg]
  exact μ₁.gap_comp g₁ hg₁

/-- Occurrences on unmarked circles of `B` keep their cycle. -/
theorem joinSucc_sameCycle_inr_of_ne (b b' : ρ₂.M) (hb : ρ₂.comp b ≠ μ₂.comp)
    (h : ρ₂.comp b = ρ₂.comp b') :
    (joinSucc μ₁ μ₂).SameCycle (Sum.inr b) (Sum.inr b') := by
  apply sameCycle_of_eqOn_orbit (sumSucc ρ₁ ρ₂) _ _ _ ((sumSucc_sameCycle_inr_iff b b').mpr h)
  intro z hz
  obtain ⟨c, rfl, hc⟩ := sumSucc_sameCycle_inr_elim b z hz
  apply joinSucc_apply_of_ne_gaps
  intro g₁ g₂ _ hg₂
  refine ⟨Sum.inr_ne_inl, fun hcg => hb ?_⟩
  rw [← hc, Sum.inr.inj hcg]
  exact μ₂.gap_comp g₂ hg₂

/-- One joined cycle per joined component. -/
theorem joinSucc_cycle (v w : ρ₁.M ⊕ ρ₂.M) (h : joinComp μ₁ μ₂ v = joinComp μ₁ μ₂ w) :
    (joinSucc μ₁ μ₂).SameCycle v w := by
  -- the marked circles: either both gaps exist, or no occurrence lies on a marked circle
  rcases v with a | b <;> rcases w with a' | b'
  · -- A, A
    rw [joinComp_inl, joinComp_inl] at h
    have h' := Sum.inl.inj h
    by_cases ha : ρ₁.comp a = μ₁.comp
    · rcases hg₁ : μ₁.gap with _ | g₁
      · exact absurd ha (μ₁.gap_none hg₁ a)
      rcases hg₂ : μ₂.gap with _ | g₂
      · exact sameCycle_of_eqOn_orbit _ _ _ _ ((sumSucc_sameCycle_inl_iff a a').mpr h')
          (fun z _ => by unfold joinSucc; rw [hg₂, gapSwap_none_right, mul_one])
      exact (joinSucc_sameCycle_gap_left μ₁ μ₂ hg₁ hg₂ a ha).trans
        (joinSucc_sameCycle_gap_left μ₁ μ₂ hg₁ hg₂ a' (h'.symm.trans ha)).symm
    · exact joinSucc_sameCycle_inl_of_ne μ₁ μ₂ a a' ha h'
  · -- A, B
    rw [joinComp_inl] at h
    by_cases hb : ρ₂.comp b' = μ₂.comp
    · rw [joinComp_inr_of_eq μ₁ μ₂ b' hb] at h
      have ha : ρ₁.comp a = μ₁.comp := Sum.inl.inj h
      rcases hg₁ : μ₁.gap with _ | g₁
      · exact absurd ha (μ₁.gap_none hg₁ a)
      rcases hg₂ : μ₂.gap with _ | g₂
      · exact absurd hb (μ₂.gap_none hg₂ b')
      exact (joinSucc_sameCycle_gap_left μ₁ μ₂ hg₁ hg₂ a ha).trans
        ((joinSucc_sameCycle_gaps μ₁ μ₂ hg₁ hg₂).trans
          (joinSucc_sameCycle_gap_right μ₁ μ₂ hg₁ hg₂ b' hb).symm)
    · rw [joinComp_inr_of_ne μ₁ μ₂ b' hb] at h
      exact absurd h Sum.inl_ne_inr
  · -- B, A
    rw [joinComp_inl] at h
    by_cases hb : ρ₂.comp b = μ₂.comp
    · rw [joinComp_inr_of_eq μ₁ μ₂ b hb] at h
      have ha : ρ₁.comp a' = μ₁.comp := (Sum.inl.inj h).symm
      rcases hg₁ : μ₁.gap with _ | g₁
      · exact absurd ha (μ₁.gap_none hg₁ a')
      rcases hg₂ : μ₂.gap with _ | g₂
      · exact absurd hb (μ₂.gap_none hg₂ b)
      exact (joinSucc_sameCycle_gap_right μ₁ μ₂ hg₁ hg₂ b hb).trans
        ((joinSucc_sameCycle_gaps μ₁ μ₂ hg₁ hg₂).symm.trans
          (joinSucc_sameCycle_gap_left μ₁ μ₂ hg₁ hg₂ a' ha).symm)
    · rw [joinComp_inr_of_ne μ₁ μ₂ b hb] at h
      exact absurd h Sum.inr_ne_inl
  · -- B, B
    by_cases hb : ρ₂.comp b = μ₂.comp <;> by_cases hb' : ρ₂.comp b' = μ₂.comp
    · rcases hg₂ : μ₂.gap with _ | g₂
      · exact absurd hb (μ₂.gap_none hg₂ b)
      rcases hg₁ : μ₁.gap with _ | g₁
      · exact sameCycle_of_eqOn_orbit _ _ _ _
          ((sumSucc_sameCycle_inr_iff b b').mpr (hb.trans hb'.symm))
          (fun z _ => by unfold joinSucc; rw [hg₁, gapSwap_none_left, mul_one])
      exact (joinSucc_sameCycle_gap_right μ₁ μ₂ hg₁ hg₂ b hb).trans
        (joinSucc_sameCycle_gap_right μ₁ μ₂ hg₁ hg₂ b' hb').symm
    · rw [joinComp_inr_of_eq μ₁ μ₂ b hb, joinComp_inr_of_ne μ₁ μ₂ b' hb'] at h
      exact absurd h Sum.inl_ne_inr
    · rw [joinComp_inr_of_ne μ₁ μ₂ b hb, joinComp_inr_of_eq μ₁ μ₂ b' hb'] at h
      exact absurd h Sum.inr_ne_inl
    · rw [joinComp_inr_of_ne μ₁ μ₂ b hb, joinComp_inr_of_ne μ₁ μ₂ b' hb'] at h
      have h' : ρ₂.comp b = ρ₂.comp b' := congrArg Subtype.val (Sum.inr.inj h)
      exact joinSucc_sameCycle_inr_of_ne μ₁ μ₂ b b' hb h'

/-- The marked join `J(A, B)` of two marked records (mp:join, sm-3:1370-1385): occurrences
`M_A ⊕ M_B`, concatenated marked cycles, all other cycles retained, "exactly all old crossing
pairings, bits and signs". -/
noncomputable def joinRecord : Record where
  comps := ρ₁.comps ⊕ μ₂.Unmarked
  M := ρ₁.M ⊕ ρ₂.M
  comp := joinComp μ₁ μ₂
  succ := joinSucc μ₁ μ₂
  pair := Perm.sumCongr ρ₁.pair ρ₂.pair
  isOver := Sum.elim ρ₁.isOver ρ₂.isOver
  sgn := Sum.elim ρ₁.sgn ρ₂.sgn
  succ_comp := joinComp_joinSucc μ₁ μ₂
  succ_cycle := joinSucc_cycle μ₁ μ₂
  pair_ne v := by
    rcases v with a | b
    · exact fun h => ρ₁.pair_ne a (Sum.inl.inj h)
    · exact fun h => ρ₂.pair_ne b (Sum.inr.inj h)
  pair_invol v := by
    rcases v with a | b
    · exact congrArg Sum.inl (ρ₁.pair_invol a)
    · exact congrArg Sum.inr (ρ₂.pair_invol b)
  bit_pair v := by
    rcases v with a | b
    · exact ρ₁.bit_pair a
    · exact ρ₂.bit_pair b
  sgn_pair v := by
    rcases v with a | b
    · exact ρ₁.sgn_pair a
    · exact ρ₂.sgn_pair b
  sgn_ne v := by
    rcases v with a | b
    · exact ρ₁.sgn_ne a
    · exact ρ₂.sgn_ne b

@[simp] theorem joinRecord_M : (joinRecord μ₁ μ₂).M = (ρ₁.M ⊕ ρ₂.M) := rfl
@[simp] theorem joinRecord_comps : (joinRecord μ₁ μ₂).comps = (ρ₁.comps ⊕ μ₂.Unmarked) := rfl
theorem joinRecord_succ : (joinRecord μ₁ μ₂).succ = joinSucc μ₁ μ₂ := rfl
theorem joinRecord_comp : (joinRecord μ₁ μ₂).comp = joinComp μ₁ μ₂ := rfl
@[simp] theorem joinRecord_pair_inl (a : ρ₁.M) :
    (joinRecord μ₁ μ₂).pair (Sum.inl a) = Sum.inl (ρ₁.pair a) := rfl
@[simp] theorem joinRecord_pair_inr (b : ρ₂.M) :
    (joinRecord μ₁ μ₂).pair (Sum.inr b) = Sum.inr (ρ₂.pair b) := rfl
@[simp] theorem joinRecord_isOver_inl (a : ρ₁.M) :
    (joinRecord μ₁ μ₂).isOver (Sum.inl a) = ρ₁.isOver a := rfl
@[simp] theorem joinRecord_isOver_inr (b : ρ₂.M) :
    (joinRecord μ₁ μ₂).isOver (Sum.inr b) = ρ₂.isOver b := rfl
@[simp] theorem joinRecord_sgn_inl (a : ρ₁.M) : (joinRecord μ₁ μ₂).sgn (Sum.inl a) = ρ₁.sgn a := rfl
@[simp] theorem joinRecord_sgn_inr (b : ρ₂.M) : (joinRecord μ₁ μ₂).sgn (Sum.inr b) = ρ₂.sgn b := rfl

/-- "The component number is c(A)+c(B)-1." -/
theorem componentCount_joinRecord :
    (joinRecord μ₁ μ₂).componentCount = ρ₁.componentCount + ρ₂.componentCount - 1 := by
  unfold componentCount
  have h1 : Fintype.card (joinRecord μ₁ μ₂).comps =
      Fintype.card ρ₁.comps + Fintype.card μ₂.Unmarked :=
    (Fintype.card_congr (Equiv.refl _)).trans (Fintype.card_sum)
  have h2 : Fintype.card μ₂.Unmarked = Fintype.card ρ₂.comps - 1 := by
    classical
    have := Fintype.card_subtype_compl (fun c : ρ₂.comps => c = μ₂.comp)
    rw [Fintype.card_subtype_eq] at this
    exact (Fintype.card_congr (Equiv.refl _)).trans this
  have h3 : 1 ≤ Fintype.card ρ₂.comps := Fintype.card_pos_iff.mpr ⟨μ₂.comp⟩
  rw [h1, h2]
  omega

/-- The crossings of the join are those of the two factors. -/
theorem card_M_joinRecord :
    Fintype.card (joinRecord μ₁ μ₂).M = Fintype.card ρ₁.M + Fintype.card ρ₂.M :=
  (Fintype.card_congr (Equiv.refl _)).trans Fintype.card_sum

theorem crossingCount_joinRecord :
    (joinRecord μ₁ μ₂).crossingCount = ρ₁.crossingCount + ρ₂.crossingCount := by
  have h1 := ρ₁.two_mul_crossingCount
  have h2 := ρ₂.two_mul_crossingCount
  have h3 := (joinRecord μ₁ μ₂).two_mul_crossingCount
  rw [card_M_joinRecord] at h3
  omega

/-- The writhe of the join is the sum of the writhes ("keep exactly all old crossing pairings,
bits and signs"). -/
theorem writhe_joinRecord : (joinRecord μ₁ μ₂).writhe = ρ₁.writhe + ρ₂.writhe := by
  have h : ∑ v, ((joinRecord μ₁ μ₂).sgn v : ℤ) = ∑ v, (ρ₁.sgn v : ℤ) + ∑ v, (ρ₂.sgn v : ℤ) :=
    Fintype.sum_sum_type _
  have h1 := ρ₁.two_mul_writhe
  have h2 := ρ₂.two_mul_writhe
  have h3 := (joinRecord μ₁ μ₂).two_mul_writhe
  rw [h] at h3
  omega

end Join

end Record


end SM.Link

/-! ## Axiom audit (must show only `propext`, `Classical.choice`, `Quot.sound`) -/

