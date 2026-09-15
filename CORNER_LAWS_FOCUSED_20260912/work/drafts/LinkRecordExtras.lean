import SM.LinkRecord

/-! # Record extras: component count of the smoothing, isomorphism transport, crossing-indexed
operations, sanity examples (`SM.Link`)

Closes the open items of `SM/LinkRecord.lean`.

* Section A (component count, sm-3:1093-1103): "A self crossing splits one parameter circle
  into two; a mixed crossing joins two into one. ... Empty resulting occurrence words are still
  circles. Thus the resulting component counts are c+1, or c−1 ≥ 1 in the mixed case".  The
  missing fact was that at a self crossing `x` and `τ x` lie on different cycles of the
  reconnected successor `s₁ = s ∘ swap x (τ x)`; it is proved here by a first-return argument
  (`not_mul_swap_sameCycle_of_sameCycle`): the first return of `s₁` to `{a, b}` from `a` is the
  first return of `s` from `b`, which is `a` when `a, b` share an `s`-cycle, so `a` is fixed by
  the first-return permutation of `s₁` on `{a, b}` and cannot reach `b`.  The cycle count of a
  permutation composed with a transposition then goes up by one (same cycle) or down by one
  (different cycles), and the component count of the smoothing follows because the components
  of a record are its successor cycles together with its crossing-free circles.
* Section B: `RecordIso` transport for `smooth`, `restrict` and `joinRecord`.
* Section C: crossing-indexed `smoothAt` / `switchAt` through a chosen occurrence, with the
  independence lemmas.
* Section D: the one-crossing kink (smooths to two empty circles) and a Hopf-type record (two
  circles, two mixed crossings; smoothing one gives one circle). -/

namespace SM.Link

open Equiv

/-! ## A. Cycle count of a permutation composed with a transposition -/

section CycleCount

variable {α : Type*} [DecidableEq α] (f : Perm α) (a b : α)

/-- Without any hypothesis on `a, b`: a point of the `f`-cycle of `a` reaches `a` or `b` along
`f * swap a b` (the path from `x` to `a` is followed until it hits `a` or `b`). -/
theorem mul_swap_sameCycle_or_of_pow_eq :
    ∀ (k : ℕ) (x : α), (f ^ k) x = a →
      (f * swap a b).SameCycle x a ∨ (f * swap a b).SameCycle x b := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, Perm.one_apply] at hx
    exact Or.inl (hx ▸ Perm.SameCycle.refl _ _)
  | succ k ih =>
    intro x hx
    rw [pow_succ, Perm.mul_apply] at hx
    have hx' := ih (f x) hx
    by_cases hxa : x = a
    · exact Or.inl (hxa ▸ Perm.SameCycle.refl _ _)
    by_cases hxb : x = b
    · exact Or.inr (hxb ▸ Perm.SameCycle.refl _ _)
    have hstep : (f * swap a b).SameCycle x (f x) :=
      ⟨1, by rw [zpow_one, mul_swap_apply_of_ne_of_ne f a b hxa hxb]⟩
    exact hx'.imp hstep.trans hstep.trans

variable [Fintype α]

theorem mul_swap_sameCycle_or {x : α} (hx : f.SameCycle x a) :
    (f * swap a b).SameCycle x a ∨ (f * swap a b).SameCycle x b := by
  obtain ⟨k, hk⟩ := hx.exists_nat_pow_eq
  exact mul_swap_sameCycle_or_of_pow_eq f a b k x hk

/-- The missing fact for the self-crossing case (sm-3:1093-1095, "(x A y B) ↦ (x B), (y A)"):
if `a` and `b` lie on one `f`-cycle, they lie on different cycles of `f * swap a b`.  Proof by
first return to `{a, b}`: from `a`, `f * swap a b` first moves to `f b` and then follows `f`,
so its first return to `{a, b}` is the first return of `f` from `b`, which is `a` (the
first-return permutation of `f` on the two points `a, b` exchanges them because they share an
`f`-cycle).  Hence `a` is a fixed point of the first-return permutation of `f * swap a b` on
`{a, b}`, and `b` is not on its cycle. -/
theorem not_mul_swap_sameCycle_of_sameCycle (hab : a ≠ b) (hc : f.SameCycle a b) :
    ¬ (f * swap a b).SameCycle a b := by
  set g := f * swap a b with hg
  set p : α → Prop := fun m => m = a ∨ m = b with hp
  have : DecidablePred p := fun m => inferInstanceAs (Decidable (m = a ∨ m = b))
  have hpa : p a := Or.inl rfl
  have hpb : p b := Or.inr rfl
  set K := returnTime f p b hpb with hK
  have hKpos : 0 < K := returnTime_pos f p b hpb
  -- along the first `K` steps, `g` from `a` follows `f` from `b`
  have horb : ∀ j, 1 ≤ j → j ≤ K → (g ^ j) a = (f ^ j) b := by
    intro j hj1 hjK
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [zero_add, pow_one, pow_one, hg, mul_swap_apply_left]
      · have ih' := ih hj (by omega)
        have hnp : ¬ p ((f ^ j) b) := returnTime_min f p b hpb hj (by omega)
        rw [pow_succ', Perm.mul_apply, ih', pow_succ', Perm.mul_apply]
        exact mul_swap_apply_of_ne_of_ne f a b (fun h => hnp (Or.inl h)) (fun h => hnp (Or.inr h))
  have hret : returnTime g p a hpa = K := by
    rw [returnTime_eq_iff]
    refine ⟨⟨hKpos, ?_⟩, ?_⟩
    · rw [horb K hKpos le_rfl]
      exact returnTime_spec f p b hpb
    · rintro j hj ⟨hj0, hpj⟩
      rw [horb j hj0 hj.le] at hpj
      exact returnTime_min f p b hpb hj0 hj hpj
  have h1 : (firstReturn g p ⟨a, hpa⟩).1 = (firstReturn f p ⟨b, hpb⟩).1 := by
    rw [firstReturn_apply, firstReturn_apply, hret]
    exact horb K hKpos le_rfl
  -- the first return of `f` on `{a, b}` exchanges the two points
  have hsc : (firstReturn f p).SameCycle ⟨a, hpa⟩ ⟨b, hpb⟩ :=
    firstReturn_sameCycle_of_sameCycle f p (m := ⟨a, hpa⟩) (m' := ⟨b, hpb⟩) hc
  have hfb : firstReturn f p ⟨b, hpb⟩ = ⟨a, hpa⟩ := by
    rcases (firstReturn f p ⟨b, hpb⟩).2 with h | h
    · exact Subtype.ext h
    · exfalso
      have hfix : Function.IsFixedPt (firstReturn f p) ⟨b, hpb⟩ := Subtype.ext h
      exact hab (congrArg Subtype.val (hsc.symm.eq_of_left hfix)).symm
  -- so the first return of `g` on `{a, b}` fixes `a`
  have hga : Function.IsFixedPt (firstReturn g p) ⟨a, hpa⟩ :=
    Subtype.ext (h1.trans (congrArg Subtype.val hfb))
  intro hgc
  have := firstReturn_sameCycle_of_sameCycle g p (m := ⟨a, hpa⟩) (m' := ⟨b, hpb⟩) hgc
  exact hab (congrArg Subtype.val (this.eq_of_left hga))

/-- The number of cycles (orbits, fixed points included) of a permutation of a finite type. -/
def cycleCount : ℕ := Fintype.card (Quotient (Perm.SameCycle.setoid f))

theorem cycleCount_pos [Nonempty α] : 0 < cycleCount f :=
  Fintype.card_pos_iff.mpr ⟨Quotient.mk _ (Classical.arbitrary α)⟩

/-- "A self crossing splits one parameter circle into two": composing with a transposition of
two points of one cycle raises the cycle count by one. -/
theorem cycleCount_mul_swap_of_sameCycle (hab : a ≠ b) (hc : f.SameCycle a b) :
    cycleCount (f * swap a b) = cycleCount f + 1 := by
  classical
  set g := f * swap a b with hg
  -- the refinement map from `g`-cycles to `f`-cycles
  let ψ : Quotient (Perm.SameCycle.setoid g) → Quotient (Perm.SameCycle.setoid f) :=
    Quotient.lift (fun u => Quotient.mk _ u)
      (fun u v huv => Quotient.sound (SM.Carrier.sameCycle_mul_swap_refines f a b hc huv))
  have hψ : ∀ u, ψ (Quotient.mk _ u) = Quotient.mk _ u := fun u => rfl
  have hsurj : Function.Surjective ψ := by
    intro q
    induction q using Quotient.ind with
    | _ u => exact ⟨Quotient.mk _ u, rfl⟩
  set qa : Quotient (Perm.SameCycle.setoid f) := Quotient.mk _ a with hqa
  -- the fibre over the cycle of `a` is exactly `{[a], [b]}`
  have hfib : ∀ q, ψ q = qa ↔ q = Quotient.mk _ a ∨ q = Quotient.mk _ b := by
    intro q
    induction q using Quotient.ind with
    | _ u =>
      rw [hψ, hqa]
      constructor
      · intro h
        have hu : f.SameCycle u a := Quotient.exact h
        rcases mul_swap_sameCycle_or f a b hu with h' | h'
        · exact Or.inl (Quotient.sound h')
        · exact Or.inr (Quotient.sound h')
      · rintro (h | h)
        · exact Quotient.sound (SM.Carrier.sameCycle_mul_swap_refines f a b hc (Quotient.exact h))
        · exact Quotient.sound
            ((SM.Carrier.sameCycle_mul_swap_refines f a b hc (Quotient.exact h)).trans hc.symm)
  -- away from the cycle of `a`, `ψ` is injective
  have hinj : ∀ q q', ψ q ≠ qa → ψ q = ψ q' → q = q' := by
    intro q q'
    induction q using Quotient.ind with
    | _ u =>
      induction q' using Quotient.ind with
      | _ v =>
        intro hne h
        rw [hψ, hψ] at h
        rw [hψ, hqa] at hne
        have hua : ¬ f.SameCycle u a := fun hc' => hne (Quotient.sound hc')
        have huv : f.SameCycle u v := Quotient.exact h
        apply Quotient.sound
        refine Record.sameCycle_of_eqOn_orbit f g u v huv (fun z hz => ?_)
        refine mul_swap_apply_of_ne_of_ne f a b (fun hza => hua (hza ▸ hz)) (fun hzb => hua ?_)
        exact (hzb ▸ hz).trans hc.symm
  have hne_ab : (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid g)) ≠ Quotient.mk _ b :=
    fun h => not_mul_swap_sameCycle_of_sameCycle f a b hab hc (Quotient.exact h)
  -- count: `Q_g = fibre over [a] ⊕ rest`
  have hsplit : cycleCount g =
      Fintype.card {q : Quotient (Perm.SameCycle.setoid g) // ψ q = qa} +
        Fintype.card {q : Quotient (Perm.SameCycle.setoid g) // ¬ ψ q = qa} := by
    unfold cycleCount
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun q => ψ q = qa)).symm
  have hfib2 : Fintype.card {q : Quotient (Perm.SameCycle.setoid g) // ψ q = qa} = 2 := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter (fun q : Quotient (Perm.SameCycle.setoid g) => ψ q = qa)) =
        {Quotient.mk _ a, Quotient.mk _ b} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hfib q
    rw [this, Finset.card_pair hne_ab]
  have hrest : Fintype.card {q : Quotient (Perm.SameCycle.setoid g) // ¬ ψ q = qa} =
      Fintype.card {r : Quotient (Perm.SameCycle.setoid f) // ¬ r = qa} := by
    refine Fintype.card_of_bijective (f := fun q => ⟨ψ q.1, q.2⟩) ⟨?_, ?_⟩
    · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      exact Subtype.ext (hinj q q' hq (congrArg Subtype.val h))
    · rintro ⟨r, hr⟩
      obtain ⟨q, rfl⟩ := hsurj r
      exact ⟨⟨q, hr⟩, rfl⟩
  have hcompl : Fintype.card {r : Quotient (Perm.SameCycle.setoid f) // ¬ r = qa} =
      cycleCount f - 1 := by
    have := Fintype.card_subtype_compl (fun r : Quotient (Perm.SameCycle.setoid f) => r = qa)
    rw [Fintype.card_subtype_eq] at this
    exact this
  have hpos : 0 < cycleCount f := Fintype.card_pos_iff.mpr ⟨qa⟩
  rw [hsplit, hfib2, hrest, hcompl]
  omega

/-- "a mixed crossing joins two into one": composing with a transposition of two points on
different cycles lowers the cycle count by one. -/
theorem cycleCount_mul_swap_of_not_sameCycle (hc : ¬ f.SameCycle a b) :
    cycleCount (f * swap a b) + 1 = cycleCount f := by
  have hab : a ≠ b := fun h => hc (h ▸ Perm.SameCycle.refl f a)
  have h := cycleCount_mul_swap_of_sameCycle (f * swap a b) a b hab
    (mul_swap_sameCycle_self f a b hc)
  rw [mul_assoc, swap_mul_self, mul_one] at h
  exact h.symm

end CycleCount

/-! ## A2. The component count of the smoothing (sm-3:1099-1101)

"Thus the resulting component counts are c+1, or c−1 ≥ 1 in the mixed case, and the smoothing
always remains in the nonempty domain."  The components of a record are its successor cycles
together with its crossing-free circles (`card_comps_eq_cycleCount_add_card_freeComp`); the
components of the smoothing are the cycles of the reconnected successor together with the same
crossing-free circles (`card_smooth_comps`); the cycle count moves by one. -/

namespace Record

variable (ρ : Record)

/-- The parametrizing circles are the successor cycles plus the crossing-free circles. -/
theorem card_comps_eq_cycleCount_add_card_freeComp :
    Fintype.card ρ.comps = cycleCount ρ.succ + Fintype.card ρ.FreeComp := by
  classical
  have h1 : Fintype.card ρ.comps =
      Fintype.card {c : ρ.comps // ∃ v, ρ.comp v = c} + Fintype.card ρ.FreeComp := by
    rw [← Fintype.card_sum]
    refine Fintype.card_congr
      ((Equiv.sumCompl (fun c : ρ.comps => ∃ v, ρ.comp v = c)).symm.trans ?_)
    exact Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun c => not_exists))
  have h2 : cycleCount ρ.succ = Fintype.card {c : ρ.comps // ∃ v, ρ.comp v = c} := by
    unfold cycleCount
    refine Fintype.card_congr (Equiv.ofBijective
      (Quotient.lift (fun v => (⟨ρ.comp v, v, rfl⟩ : {c : ρ.comps // ∃ v, ρ.comp v = c}))
        (fun v w h => Subtype.ext ((ρ.sameCycle_iff_comp_eq v w).mp h))) ⟨?_, ?_⟩)
    · intro q q'
      induction q using Quotient.ind with
      | _ v =>
        induction q' using Quotient.ind with
        | _ w =>
          intro h
          exact Quotient.sound (ρ.succ_cycle v w (congrArg Subtype.val h))
    · rintro ⟨c, v, rfl⟩
      exact ⟨Quotient.mk _ v, rfl⟩
  rw [h1, h2]

variable (x : ρ.M)

/-- The components of the smoothing: cycles of `s₁` plus the crossing-free circles of `ρ`. -/
theorem card_smooth_comps :
    Fintype.card (ρ.smooth x).comps = cycleCount (ρ.reconnect x) + Fintype.card ρ.FreeComp := by
  unfold cycleCount
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.refl _)

/-- At a self crossing, `x` and `τ x` lie on different cycles of the reconnected successor
("(x A y B) ↦ (x B), (y A)"). -/
theorem not_reconnect_sameCycle_pair_of_self (h : ρ.IsSelfCrossing x) :
    ¬ (ρ.reconnect x).SameCycle x (ρ.pair x) :=
  not_mul_swap_sameCycle_of_sameCycle ρ.succ x (ρ.pair x) (ρ.ne_pair x)
    ((ρ.isSelfCrossing_iff_sameCycle x).mp h)

/-- Every occurrence of the circle of `x` lies on the `s₁`-cycle of `x` or on that of `τ x`. -/
theorem reconnect_sameCycle_or (v : ρ.M) (hv : ρ.comp v = ρ.comp x) :
    (ρ.reconnect x).SameCycle v x ∨ (ρ.reconnect x).SameCycle v (ρ.pair x) :=
  mul_swap_sameCycle_or ρ.succ x (ρ.pair x) (ρ.succ_cycle v x hv)

/-- The two components created by smoothing a self crossing are distinct. -/
theorem smooth_comps_ne_of_self (h : ρ.IsSelfCrossing x) :
    (Sum.inl (Quotient.mk _ x) : ρ.SmoothComps x) ≠ Sum.inl (Quotient.mk _ (ρ.pair x)) :=
  fun hc => ρ.not_reconnect_sameCycle_pair_of_self x h (Quotient.exact (Sum.inl.inj hc))

/-- "A self crossing splits one parameter circle into two": `c' = c + 1`. -/
theorem card_comps_smooth_of_self (h : ρ.IsSelfCrossing x) :
    Fintype.card (ρ.smooth x).comps = Fintype.card ρ.comps + 1 := by
  rw [card_smooth_comps, card_comps_eq_cycleCount_add_card_freeComp, reconnect,
    cycleCount_mul_swap_of_sameCycle ρ.succ x (ρ.pair x) (ρ.ne_pair x)
      ((ρ.isSelfCrossing_iff_sameCycle x).mp h)]
  omega

/-- "a mixed crossing joins two into one": `c' = c − 1`. -/
theorem card_comps_smooth_of_mixed (h : ¬ ρ.IsSelfCrossing x) :
    Fintype.card (ρ.smooth x).comps = Fintype.card ρ.comps - 1 := by
  have hc := cycleCount_mul_swap_of_not_sameCycle ρ.succ x (ρ.pair x)
    (fun hc => h ((ρ.isSelfCrossing_iff_sameCycle x).mpr hc))
  rw [card_smooth_comps, card_comps_eq_cycleCount_add_card_freeComp, reconnect]
  omega

/-- A mixed crossing needs two circles. -/
theorem two_le_card_comps_of_mixed (h : ¬ ρ.IsSelfCrossing x) : 2 ≤ Fintype.card ρ.comps :=
  Fintype.one_lt_card_iff.mpr ⟨ρ.comp x, ρ.comp (ρ.pair x), h⟩

/-- "c−1 ≥ 1 in the mixed case": the smoothing "always remains in the nonempty domain". -/
theorem one_le_card_comps_smooth_of_mixed (h : ¬ ρ.IsSelfCrossing x) :
    1 ≤ Fintype.card (ρ.smooth x).comps := by
  have := ρ.two_le_card_comps_of_mixed x h
  rw [ρ.card_comps_smooth_of_mixed x h]
  omega

theorem componentCount_smooth_of_self (h : ρ.IsSelfCrossing x) :
    (ρ.smooth x).componentCount = ρ.componentCount + 1 :=
  ρ.card_comps_smooth_of_self x h

theorem componentCount_smooth_of_mixed (h : ¬ ρ.IsSelfCrossing x) :
    (ρ.smooth x).componentCount = ρ.componentCount - 1 :=
  ρ.card_comps_smooth_of_mixed x h

theorem one_le_componentCount_smooth_of_mixed (h : ¬ ρ.IsSelfCrossing x) :
    1 ≤ (ρ.smooth x).componentCount :=
  ρ.one_le_card_comps_smooth_of_mixed x h

theorem two_le_componentCount_of_mixed (h : ¬ ρ.IsSelfCrossing x) : 2 ≤ ρ.componentCount :=
  ρ.two_le_card_comps_of_mixed x h

open scoped Classical in
/-- The component count of the smoothing in one formula. -/
theorem componentCount_smooth :
    (ρ.smooth x).componentCount =
      if ρ.IsSelfCrossing x then ρ.componentCount + 1 else ρ.componentCount - 1 := by
  split_ifs with h
  · exact ρ.componentCount_smooth_of_self x h
  · exact ρ.componentCount_smooth_of_mixed x h

/-- The smoothing of a nonempty record is nonempty (self case: `c + 1 ≥ 1`; mixed: `c − 1 ≥ 1`). -/
theorem one_le_componentCount_smooth : 1 ≤ (ρ.smooth x).componentCount := by
  by_cases h : ρ.IsSelfCrossing x
  · rw [ρ.componentCount_smooth_of_self x h]; omega
  · exact ρ.one_le_componentCount_smooth_of_mixed x h

end Record

/-! ## B. Transport of the record operations along a named record isomorphism

A bijection `Φ` intertwining two permutations carries powers, cycles and first returns; a
`RecordIso` is such a bijection for the successors and the reconnected successors, so it
induces isomorphisms `smooth x ≅ smooth (Φ x)`, `restrict B ≅ restrict (e B)` and
`join ≅ join` of the transported marks. -/

section Transport

variable {α β : Type*} (Φ : α ≃ β) (f : Perm α) (f' : Perm β)

theorem map_pow_apply (hΦ : ∀ v, Φ (f v) = f' (Φ v)) (n : ℕ) (v : α) :
    Φ ((f ^ n) v) = (f' ^ n) (Φ v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, hΦ, ih, pow_succ', Perm.mul_apply]

theorem map_swap_apply [DecidableEq α] [DecidableEq β] (a b v : α) :
    Φ (swap a b v) = swap (Φ a) (Φ b) (Φ v) := by
  rw [← Equiv.symm_trans_swap_trans a b Φ, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply]

theorem sameCycle_map_iff [Finite α] (hΦ : ∀ v, Φ (f v) = f' (Φ v)) (v w : α) :
    f'.SameCycle (Φ v) (Φ w) ↔ f.SameCycle v w := by
  have : Finite β := Finite.of_equiv α Φ
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast]; exact Φ.injective (by rw [map_pow_apply Φ f f' hΦ, hn])⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← map_pow_apply Φ f f' hΦ, hn]⟩

variable [Fintype α] [Fintype β] (p : α → Prop) [DecidablePred p] (p' : β → Prop) [DecidablePred p']

theorem returnTime_map (hΦ : ∀ v, Φ (f v) = f' (Φ v)) (hp : ∀ v, p' (Φ v) ↔ p v) (v : α)
    (hv : p v) : returnTime f' p' (Φ v) ((hp v).mpr hv) = returnTime f p v hv := by
  rw [returnTime_eq_iff]
  refine ⟨⟨returnTime_pos f p v hv, ?_⟩, ?_⟩
  · rw [← map_pow_apply Φ f f' hΦ, hp]
    exact returnTime_spec f p v hv
  · rintro j hj ⟨hj0, hpj⟩
    rw [← map_pow_apply Φ f f' hΦ, hp] at hpj
    exact returnTime_min f p v hv hj0 hj hpj

/-- The first return is natural in the intertwining bijection. -/
theorem firstReturn_map_val (hΦ : ∀ v, Φ (f v) = f' (Φ v)) (hp : ∀ v, p' (Φ v) ↔ p v)
    (v : {v // p v}) :
    (firstReturn f' p' ⟨Φ v.1, (hp v.1).mpr v.2⟩).1 = Φ (firstReturn f p v).1 := by
  rw [firstReturn_apply, firstReturn_apply, returnTime_map Φ f f' p p' hΦ hp,
    map_pow_apply Φ f f' hΦ]

end Transport

namespace RecordIso

variable {ρ ρ' : Record} (i : RecordIso ρ ρ')

theorem reconnect_eq (x v : ρ.M) : i.Φ (ρ.reconnect x v) = ρ'.reconnect (i.Φ x) (i.Φ v) := by
  unfold Record.reconnect
  rw [Perm.mul_apply, Perm.mul_apply, i.succ_eq, map_swap_apply i.Φ, i.pair_eq]

theorem reconnect_sameCycle_iff (x v w : ρ.M) :
    (ρ'.reconnect (i.Φ x)).SameCycle (i.Φ v) (i.Φ w) ↔ (ρ.reconnect x).SameCycle v w :=
  sameCycle_map_iff i.Φ _ _ (i.reconnect_eq x) v w

theorem smoothKeep_iff (x v : ρ.M) : ρ'.SmoothKeep (i.Φ x) (i.Φ v) ↔ ρ.SmoothKeep x v := by
  unfold Record.SmoothKeep
  rw [i.mem_pair_iff]

/-- Crossing-free circles correspond under an isomorphism. -/
def freeCompEquiv : ρ.FreeComp ≃ ρ'.FreeComp :=
  Equiv.subtypeEquiv i.e (fun c => ⟨fun h v' hv' => h (i.Φ.symm v') (by
      apply i.e.injective
      rw [← i.comp_eq, Equiv.apply_symm_apply]
      exact hv'),
    fun h v hv => h (i.Φ v) (by rw [i.comp_eq, hv])⟩)

include i in
theorem card_freeComp_eq : Fintype.card ρ.FreeComp = Fintype.card ρ'.FreeComp :=
  Fintype.card_congr i.freeCompEquiv

/-- A named record isomorphism carries the smoothing at `x` to the smoothing at `Φ x` (the
record half of the bridge `record (smooth D x) ≅ (record D).smooth x`). -/
noncomputable def smooth (x : ρ.M) : RecordIso (ρ.smooth x) (ρ'.smooth (i.Φ x)) where
  e := Equiv.sumCongr
    (Quotient.congr i.Φ (fun v w => (i.reconnect_sameCycle_iff x v w).symm)) i.freeCompEquiv
  Φ := Equiv.subtypeEquiv i.Φ (fun v => (i.smoothKeep_iff x v).symm)
  comp_eq _ := rfl
  succ_eq v :=
    Subtype.ext (firstReturn_map_val i.Φ (ρ.reconnect x) (ρ'.reconnect (i.Φ x))
      (ρ.SmoothKeep x) (ρ'.SmoothKeep (i.Φ x)) (i.reconnect_eq x) (i.smoothKeep_iff x) v).symm
  pair_eq v := Subtype.ext (i.pair_eq v.1)
  bit_eq v := i.bit_eq v.1
  sgn_eq v := i.sgn_eq v.1

theorem isSelfCrossing_iff (x : ρ.M) : ρ'.IsSelfCrossing (i.Φ x) ↔ ρ.IsSelfCrossing x := by
  unfold Record.IsSelfCrossing
  rw [← i.pair_eq, i.comp_eq, i.comp_eq, i.e.injective.eq_iff]

theorem restrictKeep_iff (B : Finset ρ.comps) (B' : Finset ρ'.comps)
    (hB : ∀ c, i.e c ∈ B' ↔ c ∈ B) (v : ρ.M) :
    ρ'.RestrictKeep B' (i.Φ v) ↔ ρ.RestrictKeep B v := by
  unfold Record.RestrictKeep
  rw [i.comp_eq, ← i.pair_eq, i.comp_eq, hB, hB]

/-- A named record isomorphism carries the restriction to a block `B` to the restriction to the
corresponding block `B'`. -/
noncomputable def restrict (B : Finset ρ.comps) (B' : Finset ρ'.comps)
    (hB : ∀ c, i.e c ∈ B' ↔ c ∈ B) : RecordIso (ρ.restrict B) (ρ'.restrict B') where
  e := Equiv.subtypeEquiv i.e (fun c => (hB c).symm)
  Φ := Equiv.subtypeEquiv i.Φ (fun v => (i.restrictKeep_iff B B' hB v).symm)
  comp_eq v := Subtype.ext (i.comp_eq v.1)
  succ_eq v :=
    Subtype.ext (firstReturn_map_val i.Φ ρ.succ ρ'.succ (ρ.RestrictKeep B) (ρ'.RestrictKeep B')
      i.succ_eq (i.restrictKeep_iff B B' hB) v).symm
  pair_eq v := Subtype.ext (i.pair_eq v.1)
  bit_eq v := i.bit_eq v.1
  sgn_eq v := i.sgn_eq v.1

/-- The restriction to `B` and to its image `e(B)`. -/
noncomputable def restrictMap (B : Finset ρ.comps) :
    RecordIso (ρ.restrict B) (ρ'.restrict (B.map i.e.toEmbedding)) :=
  i.restrict B _ (fun _ => Finset.mem_map' _)

end RecordIso

namespace Record

/-- Transport of a mark along a named record isomorphism. -/
def Mark.map {ρ ρ' : Record} (i : RecordIso ρ ρ') (μ : ρ.Mark) : ρ'.Mark where
  comp := i.e μ.comp
  gap := μ.gap.map i.Φ
  gap_comp v' hv' := by
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hv'
    rw [i.comp_eq, μ.gap_comp v hv]
  gap_none h v' hc := by
    have h0 : μ.gap = none := Option.map_eq_none_iff.mp h
    apply μ.gap_none h0 (i.Φ.symm v')
    apply i.e.injective
    rw [← i.comp_eq, Equiv.apply_symm_apply]
    exact hc

@[simp] theorem Mark.map_comp {ρ ρ' : Record} (i : RecordIso ρ ρ') (μ : ρ.Mark) :
    (μ.map i).comp = i.e μ.comp := rfl

@[simp] theorem Mark.map_gap {ρ ρ' : Record} (i : RecordIso ρ ρ') (μ : ρ.Mark) :
    (μ.map i).gap = μ.gap.map i.Φ := rfl

end Record

namespace RecordIso

variable {ρ₁ ρ₁' ρ₂ ρ₂' : Record} (i₁ : RecordIso ρ₁ ρ₁') (i₂ : RecordIso ρ₂ ρ₂')

theorem sumSucc_eq (z : ρ₁.M ⊕ ρ₂.M) :
    Equiv.sumCongr i₁.Φ i₂.Φ (Record.sumSucc ρ₁ ρ₂ z) =
      Record.sumSucc ρ₁' ρ₂' (Equiv.sumCongr i₁.Φ i₂.Φ z) := by
  rcases z with a | b
  · exact congrArg Sum.inl (i₁.succ_eq a)
  · exact congrArg Sum.inr (i₂.succ_eq b)

theorem gapSwap_eq (g₁ : Option ρ₁.M) (g₂ : Option ρ₂.M) (z : ρ₁.M ⊕ ρ₂.M) :
    Equiv.sumCongr i₁.Φ i₂.Φ (Record.gapSwap g₁ g₂ z) =
      Record.gapSwap (g₁.map i₁.Φ) (g₂.map i₂.Φ) (Equiv.sumCongr i₁.Φ i₂.Φ z) := by
  rcases g₁ with _ | a <;> rcases g₂ with _ | b
  · rfl
  · rfl
  · rfl
  · exact map_swap_apply (Equiv.sumCongr i₁.Φ i₂.Φ) (Sum.inl a) (Sum.inr b) z

/-- The unmarked circles correspond under the transport of a mark. -/
def unmarkedEquiv {ρ ρ' : Record} (i : RecordIso ρ ρ') (μ : ρ.Mark) :
    μ.Unmarked ≃ (μ.map i).Unmarked :=
  Equiv.subtypeEquiv (p := fun c => c ≠ μ.comp) (q := fun c => c ≠ i.e μ.comp) i.e
    (fun _ => i.e.injective.ne_iff.symm)

/-- The component bijection of the transported join. -/
def joinCompsEquiv (μ₂ : ρ₂.Mark) : (ρ₁.comps ⊕ μ₂.Unmarked) ≃ (ρ₁'.comps ⊕ (μ₂.map i₂).Unmarked) :=
  Equiv.sumCongr i₁.e (unmarkedEquiv i₂ μ₂)

theorem joinComp_eq (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (z : ρ₁.M ⊕ ρ₂.M) :
    Record.joinComp (μ₁.map i₁) (μ₂.map i₂) (Equiv.sumCongr i₁.Φ i₂.Φ z) =
      joinCompsEquiv i₁ i₂ μ₂ (Record.joinComp μ₁ μ₂ z) := by
  rcases z with a | b
  · exact congrArg Sum.inl (i₁.comp_eq a)
  · show Record.joinComp (μ₁.map i₁) (μ₂.map i₂) (Sum.inr (i₂.Φ b)) =
      joinCompsEquiv i₁ i₂ μ₂ (Record.joinComp μ₁ μ₂ (Sum.inr b))
    by_cases hb : ρ₂.comp b = μ₂.comp
    · rw [Record.joinComp_inr_of_eq _ _ _ (by rw [i₂.comp_eq, hb]; rfl),
        Record.joinComp_inr_of_eq μ₁ μ₂ b hb]
      rfl
    · rw [Record.joinComp_inr_of_ne _ _ _
          (by rw [i₂.comp_eq]; exact fun h => hb (i₂.e.injective h)),
        Record.joinComp_inr_of_ne μ₁ μ₂ b hb]
      exact congrArg Sum.inr (Subtype.ext (i₂.comp_eq b))

theorem joinSucc_eq (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) (z : ρ₁.M ⊕ ρ₂.M) :
    Equiv.sumCongr i₁.Φ i₂.Φ (Record.joinSucc μ₁ μ₂ z) =
      Record.joinSucc (μ₁.map i₁) (μ₂.map i₂) (Equiv.sumCongr i₁.Φ i₂.Φ z) := by
  unfold Record.joinSucc
  rw [Perm.mul_apply, Perm.mul_apply, sumSucc_eq, gapSwap_eq]
  rfl

/-- Named record isomorphisms of the factors induce one of the marked joins. -/
noncomputable def joinRecord (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) :
    RecordIso (Record.joinRecord μ₁ μ₂) (Record.joinRecord (μ₁.map i₁) (μ₂.map i₂)) where
  e := joinCompsEquiv i₁ i₂ μ₂
  Φ := Equiv.sumCongr i₁.Φ i₂.Φ
  comp_eq v := joinComp_eq i₁ i₂ μ₁ μ₂ v
  succ_eq v := joinSucc_eq i₁ i₂ μ₁ μ₂ v
  pair_eq v := by
    rcases v with a | b
    · exact congrArg Sum.inl (i₁.pair_eq a)
    · exact congrArg Sum.inr (i₂.pair_eq b)
  bit_eq v := by
    rcases v with a | b
    · exact i₁.bit_eq a
    · exact i₂.bit_eq b
  sgn_eq v := by
    rcases v with a | b
    · exact i₁.sgn_eq a
    · exact i₂.sgn_eq b

end RecordIso

/-! ## C. Crossing-indexed operations

`switch` and `smooth` are indexed by an occurrence `x : M`; the operations depend only on the
crossing `{x, τ x}` (`switch_pair_eq`, `smoothPairIso`).  Here they are re-indexed by
`ρ.Crossing` through a chosen occurrence `Crossing.rep`, with the independence lemmas. -/

namespace Record

section CrossingRep

variable {ρ : Record}

/-- A chosen occurrence of a crossing. -/
noncomputable def Crossing.rep (c : ρ.Crossing) : ρ.M := Classical.choose c.2

theorem Crossing.eq_pair_rep (c : ρ.Crossing) : c.1 = {c.rep, ρ.pair c.rep} :=
  Classical.choose_spec c.2

theorem Crossing.rep_mem (c : ρ.Crossing) : c.rep ∈ c.1 := by
  rw [Crossing.eq_pair_rep]; simp

/-- Self crossing, indexed by the crossing (independent of the chosen occurrence,
`isSelfCrossing_iff_isSelf`). -/
def Crossing.IsSelf (c : ρ.Crossing) : Prop := ρ.IsSelfCrossing c.rep

end CrossingRep

variable (ρ : Record)

theorem crossingOf_rep (c : ρ.Crossing) : ρ.crossingOf c.rep = c :=
  Subtype.ext c.eq_pair_rep.symm

/-- An occurrence of the crossing `c` is its chosen occurrence or the pair of it. -/
theorem eq_rep_or_eq_pair_rep {v : ρ.M} {c : ρ.Crossing} (h : ρ.crossingOf v = c) :
    v = c.rep ∨ v = ρ.pair c.rep := by
  have hv : v ∈ c.1 := (ρ.crossingOf_eq_iff v c).mp h
  rw [Crossing.eq_pair_rep] at hv
  simpa using hv

theorem crossingOf_pair_rep (c : ρ.Crossing) : ρ.crossingOf (ρ.pair c.rep) = c := by
  rw [crossingOf_pair, crossingOf_rep]

theorem isSelfCrossing_iff_isSelf {v : ρ.M} {c : ρ.Crossing} (h : ρ.crossingOf v = c) :
    ρ.IsSelfCrossing v ↔ c.IsSelf := by
  rcases ρ.eq_rep_or_eq_pair_rep h with hv | hv
  · subst hv; exact Iff.rfl
  · subst hv; exact ρ.isSelfCrossing_pair c.rep

/-- The switch at a crossing. -/
noncomputable def switchAt (c : ρ.Crossing) : Record := ρ.switch c.rep

/-- The oriented smoothing at a crossing. -/
noncomputable def smoothAt (c : ρ.Crossing) : Record := ρ.smooth c.rep

/-- The switch at a crossing is the switch at any of its occurrences. -/
theorem switchAt_eq_of_crossingOf_eq {v : ρ.M} {c : ρ.Crossing} (h : ρ.crossingOf v = c) :
    ρ.switchAt c = ρ.switch v := by
  unfold switchAt
  rcases ρ.eq_rep_or_eq_pair_rep h with hv | hv
  · rw [hv]
  · rw [hv, switch_pair_eq]

theorem switchAt_crossingOf (v : ρ.M) : ρ.switchAt (ρ.crossingOf v) = ρ.switch v :=
  ρ.switchAt_eq_of_crossingOf_eq rfl

/-- The smoothing at a crossing is (isomorphic to) the smoothing at any of its occurrences. -/
noncomputable def smoothAtIso {v : ρ.M} {c : ρ.Crossing} (h : ρ.crossingOf v = c) :
    RecordIso (ρ.smooth v) (ρ.smoothAt c) := by
  unfold smoothAt
  by_cases hv : v = c.rep
  · subst hv; exact RecordIso.refl _
  · have hv' : v = ρ.pair c.rep := (ρ.eq_rep_or_eq_pair_rep h).resolve_left hv
    subst hv'; exact ρ.smoothPairIso c.rep

noncomputable def smoothAtCrossingOfIso (v : ρ.M) :
    RecordIso (ρ.smooth v) (ρ.smoothAt (ρ.crossingOf v)) :=
  ρ.smoothAtIso rfl

variable (c : ρ.Crossing)

theorem componentCount_switchAt : (ρ.switchAt c).componentCount = ρ.componentCount := rfl

theorem crossingCount_switchAt : (ρ.switchAt c).crossingCount = ρ.crossingCount := rfl

/-- The writhe drops by twice the sign of the switched crossing (the sign is that of either
occurrence, `sgn_pair`). -/
theorem writhe_switchAt : (ρ.switchAt c).writhe = ρ.writhe - 2 * (ρ.sgn c.rep : ℤ) :=
  ρ.writhe_switch c.rep

theorem writhe_switchAt_of_crossingOf_eq {v : ρ.M} (h : ρ.crossingOf v = c) :
    (ρ.switchAt c).writhe = ρ.writhe - 2 * (ρ.sgn v : ℤ) := by
  rw [ρ.switchAt_eq_of_crossingOf_eq h, writhe_switch]

theorem crossingCount_smoothAt : (ρ.smoothAt c).crossingCount = ρ.crossingCount - 1 :=
  ρ.crossingCount_smooth c.rep

theorem card_M_smoothAt : Fintype.card (ρ.smoothAt c).M = Fintype.card ρ.M - 2 :=
  ρ.card_M_smooth c.rep

theorem componentCount_smoothAt_of_self (h : c.IsSelf) :
    (ρ.smoothAt c).componentCount = ρ.componentCount + 1 :=
  ρ.componentCount_smooth_of_self c.rep h

theorem componentCount_smoothAt_of_mixed (h : ¬ c.IsSelf) :
    (ρ.smoothAt c).componentCount = ρ.componentCount - 1 :=
  ρ.componentCount_smooth_of_mixed c.rep h

theorem one_le_componentCount_smoothAt : 1 ≤ (ρ.smoothAt c).componentCount :=
  ρ.one_le_componentCount_smooth c.rep

end Record

/-! ## D. Sanity examples

The one-crossing kink: one circle, `M = Fin 2`, `s = τ = swap 0 1`.  Its only crossing is a
self crossing; the smoothing has no occurrence left and two components ("Empty resulting
occurrence words are still circles").  The Hopf-type record: two circles carrying occurrences
`{0, 1}` and `{2, 3}`, crossings `{0, 2}` and `{1, 3}`, both mixed; smoothing one of them
leaves one circle. -/

namespace Examples

/-- The one-crossing kink record (reducible so that numerals and `decide` see `Fin 2`). -/
abbrev kink : Record where
  comps := Unit
  M := Fin 2
  comp _ := ()
  succ := swap 0 1
  pair := swap 0 1
  isOver v := v = 0
  sgn _ := 1
  succ_comp _ := rfl
  succ_cycle v w _ := by
    fin_cases v <;> fin_cases w
    · exact Perm.SameCycle.refl _ _
    · exact ⟨1, by rw [zpow_one]; decide⟩
    · exact ⟨1, by rw [zpow_one]; decide⟩
    · exact Perm.SameCycle.refl _ _
  pair_ne := by decide
  pair_invol := by decide
  bit_pair := by decide
  sgn_pair _ := rfl
  sgn_ne _ := by decide

theorem kink_componentCount : kink.componentCount = 1 := rfl

theorem kink_crossingCount : kink.crossingCount = 1 := rfl

theorem kink_isSelfCrossing : kink.IsSelfCrossing (0 : Fin 2) := rfl

/-- The reconnected successor of the kink is the identity: two one-point cycles. -/
theorem kink_reconnect : kink.reconnect (0 : Fin 2) = 1 := by
  ext v; fin_cases v <;> decide

/-- The smoothed kink has no crossing occurrence left ... -/
theorem kink_smooth_card_M : Fintype.card (kink.smooth (0 : Fin 2)).M = 0 := by
  rw [Record.card_M_smooth]; rfl

theorem kink_smooth_crossingCount : (kink.smooth (0 : Fin 2)).crossingCount = 0 := by
  rw [Record.crossingCount_smooth]; rfl

/-- ... and two components: two empty circles. -/
theorem kink_smooth_componentCount : (kink.smooth (0 : Fin 2)).componentCount = 2 := by
  rw [kink.componentCount_smooth_of_self (0 : Fin 2) kink_isSelfCrossing, kink_componentCount]

/-- A Hopf-type record: two circles, two mixed crossings. -/
abbrev hopf : Record where
  comps := Fin 2
  M := Fin 4
  comp := ![0, 0, 1, 1]
  succ := swap 0 1 * swap 2 3
  pair := swap 0 2 * swap 1 3
  isOver := ![true, false, false, true]
  sgn _ := 1
  succ_comp := by decide
  succ_cycle v w h := by
    fin_cases v <;> fin_cases w <;>
      first
      | exact Perm.SameCycle.refl _ _
      | exact ⟨1, by rw [zpow_one]; decide⟩
      | exact absurd h (by decide)
  pair_ne := by decide
  pair_invol := by decide
  bit_pair := by decide
  sgn_pair _ := rfl
  sgn_ne _ := by decide

theorem hopf_componentCount : hopf.componentCount = 2 := rfl

theorem hopf_crossingCount : hopf.crossingCount = 2 := rfl

theorem hopf_not_isSelfCrossing : ¬ hopf.IsSelfCrossing (0 : Fin 4) := by
  show ¬ (hopf.comp 0 = hopf.comp (hopf.pair 0)); decide

theorem hopf_not_isSelfCrossing' : ¬ hopf.IsSelfCrossing (1 : Fin 4) := by
  show ¬ (hopf.comp 1 = hopf.comp (hopf.pair 1)); decide

/-- Smoothing a mixed crossing of the Hopf-type record leaves one circle. -/
theorem hopf_smooth_componentCount : (hopf.smooth (0 : Fin 4)).componentCount = 1 := by
  rw [hopf.componentCount_smooth_of_mixed (0 : Fin 4) hopf_not_isSelfCrossing, hopf_componentCount]

theorem hopf_smooth_crossingCount : (hopf.smooth (0 : Fin 4)).crossingCount = 1 := by
  rw [Record.crossingCount_smooth]; rfl

/-- The two retained occurrences of the smoothed Hopf record lie on one circle. -/
theorem hopf_reconnect_sameCycle : (hopf.reconnect (0 : Fin 4)).SameCycle (1 : Fin 4) (3 : Fin 4) :=
  (hopf.reconnect_sameCycle_of_mixed (0 : Fin 4) hopf_not_isSelfCrossing 1 (Or.inl rfl)).trans
    (hopf.reconnect_sameCycle_of_mixed (0 : Fin 4) hopf_not_isSelfCrossing 3 (Or.inr rfl)).symm

end Examples

end SM.Link

/-! ## Axiom audit (must show only `propext`, `Classical.choice`, `Quot.sound`) -/
#print axioms SM.Link.not_mul_swap_sameCycle_of_sameCycle
#print axioms SM.Link.cycleCount_mul_swap_of_sameCycle
#print axioms SM.Link.cycleCount_mul_swap_of_not_sameCycle
#print axioms SM.Link.Record.card_comps_smooth_of_self
#print axioms SM.Link.Record.card_comps_smooth_of_mixed
#print axioms SM.Link.Record.one_le_card_comps_smooth_of_mixed
#print axioms SM.Link.Record.componentCount_smooth
#print axioms SM.Link.RecordIso.smooth
#print axioms SM.Link.RecordIso.restrict
#print axioms SM.Link.RecordIso.joinRecord
#print axioms SM.Link.Record.smoothAtIso
#print axioms SM.Link.Record.switchAt_eq_of_crossingOf_eq
#print axioms SM.Link.Examples.kink_smooth_componentCount
#print axioms SM.Link.Examples.hopf_smooth_componentCount
