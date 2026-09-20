-- W3_Skeleton.lean — corner wave 3 (row 110 thm:C-S7), 2026-09-15: the four open declarations of Corner_Assembled.lean
-- (s7_sliding_law_at 8656-8668, s7_bigon_law_at 9816-9834, thm_C_S7_of / thm_C_S7_of_floor 10008-10039) VERBATIM on top of the
-- ported library (SM.CornerChainUnits = waves 1-2a, SM.CS7Sliding = wave 2b, SM.BigonDeletion = the moves toolkit,
-- SM.CarrierFloorRows = thm_floor), plus the row theorem. Units APPEND prefixed material and may replace ONLY the two `sorry`
-- bodies; statements, names and docstrings are frozen (audit A-110-1, AUTHOR_NOTES 20:46Z).
import SM.CornerChainUnits
import SM.CS7Sliding
import SM.BigonDeletion
import SM.CarrierFloorRows

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

section VertexEdge

variable {n : ℕ} [NeZero n]

/-- The sliding branch (sm-4:300-406): relocation bijection `φ(x₋) = x₊`, the support bijection
eq. s7c:sliding-bijection with the halves, equal coefficient products eq. s7c:sliding-coefficients, and
the exact selector difference eq. s7c:sliding-selector-difference.  NO floor, NO singleton. -/
theorem s7_sliding_law_at (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


/-! ### Unit K (wave 3, prefix `s7z_`; PLAN_FINAL §3.3 bigon (6), U110-K, sm-4:874-908): the ASSEMBLY of the
bigon leaf `s7_bigon_law_at`.  Everything geometric is a black box (rule (3)): the outputs of units F (the
eligible bijection eq. s7c:eligible-bijection, the ineligible cancellation, the two-newborn sector
eq. s7c:sector-split `B = (1−ε)J`), SITE + BLOCK + ROT + RET (the newborn-free returned row: the R-II site,
the skein/two-component rows eq. s7c:interlacing-coefficient-result / s7c:noninterlacing-return, the rotation
ledger, the selector laws) and J (the floor entries and cb:singleton at the one-newborn rows) are stated as
the three `s7z_`-Props `s7z_FSector`, `s7z_NewbornFreeRow`, `s7z_OneNewbornRows` (per side parameter, on an
explicit persistent bijection `e₀` and an explicit eligible bijection `e`), bundled in `s7z_RowSector`; their
existence below a radius is the single sorried theorem `s7z_exists_rowSector`.  PROVED here: the state-sum
bookkeeping — the newborn split of the high side's supports into the four classes `T, T∪{x}, T∪{y}, T∪{x,y}`
(`s7z_sum_insert_split`), the row algebra `Σ_H − Σ_L = s₀ Σ_rows` and `B + R_ret = J` (`s7z_law_of_rows`,
eq. s7c:bigon-total), the newborn side and its two newborn crossings from lem:wall-sides
(`s7z_side`, `s7z_pattern`, `s7z_x`, `s7z_y`), the sign `s₀ = χ(P₀)` from `vertex_contact_signs`
(`s7z_s₀_eq_chi`, eq. s7c:bigon-signs), the directed law at one side parameter (`s7z_law_at_of_rowSector`)
and the leaf modulo the sector (`s7z_bigon_law_at_of`). -/

section S7ZBigon

/-! #### A. Pure algebra: the newborn split and the row law (eq. s7c:bigon-total) -/

omit [NeZero n] in
/-- The supports of the high side, split by the two newborns `x ≠ y`: every support is uniquely
`T`, `T ∪ {x}`, `T ∪ {y}` or `T ∪ {x, y}` with `T` newborn-free (sm-4:409-418, the four sectors). -/
theorem s7z_sum_insert_split {κ : Type*} [Fintype κ] [DecidableEq κ] (F : Finset κ → ℤ) (x y : κ)
    (hxy : x ≠ y) :
    ∑ T, F T = ∑ T : {T : Finset κ // x ∉ T ∧ y ∉ T},
      (F T.1 + F (insert x T.1) + F (insert y T.1) + F (insert x (insert y T.1))) := by
  classical
  set s : Finset κ := (Finset.univ.erase x).erase y with hs
  have hy : y ∉ s := Finset.notMem_erase y _
  have hx : x ∉ insert y s := by
    rw [Finset.mem_insert, not_or]
    refine ⟨hxy, ?_⟩
    rw [hs, Finset.mem_erase, Finset.mem_erase]
    tauto
  have huniv : (Finset.univ : Finset κ) = insert x (insert y s) := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_insert, hs, Finset.mem_erase, true_iff]
    by_cases hzx : z = x
    · exact Or.inl hzx
    by_cases hzy : z = y
    · exact Or.inr (Or.inl hzy)
    exact Or.inr (Or.inr ⟨hzy, hzx, trivial⟩)
  have h1 : (Finset.univ : Finset (Finset κ)) = (insert x (insert y s)).powerset := by
    rw [← huniv]
    ext T
    simp only [Finset.mem_univ, Finset.mem_powerset, Finset.subset_univ]
  have hmem : ∀ T : Finset κ, T ∈ s.powerset ↔ (x ∉ T ∧ y ∉ T) := by
    intro T
    rw [Finset.mem_powerset]
    constructor
    · intro hT
      refine ⟨fun hxT => ?_, fun hyT => ?_⟩
      · have := hT hxT
        rw [hs, Finset.mem_erase, Finset.mem_erase] at this
        exact this.2.1 rfl
      · have := hT hyT
        rw [hs, Finset.mem_erase] at this
        exact this.1 rfl
    · intro ⟨hxT, hyT⟩ z hz
      rw [hs, Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun h => hyT (h ▸ hz), fun h => hxT (h ▸ hz), Finset.mem_univ _⟩
  rw [h1, Finset.sum_powerset_insert hx, Finset.sum_powerset_insert hy, Finset.sum_powerset_insert hy,
    ← Finset.sum_subtype s.powerset hmem
      (fun T => F T + F (insert x T) + F (insert y T) + F (insert x (insert y T))),
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

omit [NeZero n] in
/-- **The algebra of the bigon law** (eq. s7c:bigon-total `B + R_ret = J`, sm-4:874-908).  Two state
sums `Σ f` (the low side `P₀`, indexed by all its supports) and `Σ f'` (the high side `P₂`, indexed by
`Finset κ`) are compared through the newborn-free bijection `e₀` (persistent transport) and the ROWS
of the newborn-free supports `T`: `row T = (f' T − f (e₀⁻¹ T)) + f' (T∪{x}) + f' (T∪{y}) + f' (T∪{x,y})`.
Ineligible rows vanish (`hrow0`); the eligible rows are matched with `Ind(λ₁) × Ind(λ₂)` by `e` and
equal `s₀ · g₁ · g₂` termwise (`hrow`); the half terms vanish off the decompositions (`hz₁`, `hz₂`).
Then `Σ f' − Σ f = s₀ (Σ g₁)(Σ g₂)`. -/
theorem s7z_law_of_rows {α κ γ₁ γ₂ : Type*} [Fintype α] [Fintype κ] [DecidableEq κ] [Fintype γ₁]
    [Fintype γ₂] (f : α → ℤ) (f' : Finset κ → ℤ) (g₁ : γ₁ → ℤ) (g₂ : γ₂ → ℤ) (x y : κ) (hxy : x ≠ y)
    (E : Finset κ → Prop) (D₁ : γ₁ → Prop) (D₂ : γ₂ → Prop)
    (hz₁ : ∀ S, ¬ D₁ S → g₁ S = 0) (hz₂ : ∀ S, ¬ D₂ S → g₂ S = 0)
    (e₀ : α ≃ {T : Finset κ // x ∉ T ∧ y ∉ T})
    (e : {T : {T : Finset κ // x ∉ T ∧ y ∉ T} // E T.1} ≃
      {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}) (s : ℤ)
    (hrow : ∀ T : {T : {T : Finset κ // x ∉ T ∧ y ∉ T} // E T.1},
      f' T.1.1 - f (e₀.symm T.1) + f' (insert x T.1.1) + f' (insert y T.1.1) +
        f' (insert x (insert y T.1.1)) = s * (g₁ (e T).1.1 * g₂ (e T).2.1))
    (hrow0 : ∀ T : {T : Finset κ // x ∉ T ∧ y ∉ T}, ¬ E T.1 →
      f' T.1 - f (e₀.symm T) + f' (insert x T.1) + f' (insert y T.1) +
        f' (insert x (insert y T.1)) = 0) :
    ∑ T, f' T - ∑ S, f S = s * ((∑ S₁, g₁ S₁) * (∑ S₂, g₂ S₂)) := by
  classical
  set row : {T : Finset κ // x ∉ T ∧ y ∉ T} → ℤ := fun T =>
    f' T.1 - f (e₀.symm T) + f' (insert x T.1) + f' (insert y T.1) +
      f' (insert x (insert y T.1)) with hrowdef
  rw [s7z_sum_insert_split f' x y hxy]
  have hL : ∑ S, f S = ∑ T : {T : Finset κ // x ∉ T ∧ y ∉ T}, f (e₀.symm T) :=
    Fintype.sum_equiv e₀ _ _ (fun S => by rw [Equiv.symm_apply_apply])
  rw [hL, ← Finset.sum_sub_distrib]
  have hsum : ∑ T : {T : Finset κ // x ∉ T ∧ y ∉ T},
      ((f' T.1 + f' (insert x T.1) + f' (insert y T.1) + f' (insert x (insert y T.1))) -
        f (e₀.symm T)) = ∑ T, row T :=
    Finset.sum_congr rfl fun T _ => by simp only [hrowdef]; ring
  rw [hsum, ← s7e_sum_full_eq_of_zero row (fun T => E T.1) hrow0]
  have he : ∑ T : {T : {T : Finset κ // x ∉ T ∧ y ∉ T} // E T.1}, row T.1 =
      ∑ q : {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}, s * (g₁ q.1.1 * g₂ q.2.1) :=
    Fintype.sum_equiv e _ _ (fun T => hrow T)
  rw [he, ← Finset.mul_sum, Fintype.sum_prod_type, ← s7e_sum_full_eq_of_zero g₁ D₁ hz₁,
    ← s7e_sum_full_eq_of_zero g₂ D₂ hz₂, Finset.sum_mul_sum]

/-! #### B. The bigon wall: the newborn side, the two newborns, the sign `s₀` (sm-4:396-408) -/

variable {g : WallGerm n} {M a : ZMod n}

/-- The NEWBORN side `P₂` of the bigon wall (sm-4:397-399: "the other side, with two newborn
crossings `x, y`"): `true` if `P₊` carries the crossing `{a, M}` (at the base parameter; constant
along the side, `s7z_pattern`).  The side `!s7z_side` is `P₀`. -/
noncomputable def s7z_side (g : WallGerm n) (M a : ZMod n) : Bool :=
  decide (IsCrossing (g.sideTuple true g.sideBase).val {a, M})

/-- The bigon crossing pattern (lem:wall-sides (V), `vertex_sides`, `BigonCrossingPattern`) read with
`s7z_side`: the newborn side carries BOTH contact crossings `{a, M − 1}`, `{a, M}` and the other side
NEITHER, at every side parameter `t`. -/
theorem s7z_pattern (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    IsCrossing (g.curve (g.sideTime (s7z_side g M a) t)) {a, M - 1} ∧
    IsCrossing (g.curve (g.sideTime (s7z_side g M a) t)) {a, M} ∧
    ¬ IsCrossing (g.curve (g.sideTime (!s7z_side g M a) t)) {a, M - 1} ∧
    ¬ IsCrossing (g.curve (g.sideTime (!s7z_side g M a) t)) {a, M} := by
  have hpat : BigonCrossingPattern (g.curve (g.sideTime true t)) (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 t t).2.1 h.2
  have hbase : BigonCrossingPattern (g.curve (g.sideTime true g.sideBase))
      (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 g.sideBase t).2.1 h.2
  unfold s7z_side
  by_cases hM : IsCrossing (g.sideTuple true g.sideBase).val {a, M}
  · rw [decide_eq_true hM]
    simp only [Bool.not_true]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, _, b3, _⟩ | ⟨_, b2, _, _⟩
      · exact b3 h3
      · exact b2 hM
  · rw [decide_eq_false hM]
    simp only [Bool.not_false]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, b2, _, _⟩ | ⟨_, _, _, b4⟩
      · exact hM b2
      · exact h4 b4
    · exact ⟨h3, h4, h1, h2⟩

/-- The newborn `x = x_{M−1,a}` of the newborn side (sm-4:398). -/
noncomputable def s7z_x (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime (s7z_side g M a) t)) :=
  ⟨{a, M - 1}, (s7z_pattern hn h t).1⟩

/-- The newborn `y = x_{a,M}` of the newborn side (sm-4:398). -/
noncomputable def s7z_y (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime (s7z_side g M a) t)) :=
  ⟨{a, M}, (s7z_pattern hn h t).2.1⟩

theorem s7z_x_ne_y (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    s7z_x hn h t ≠ s7z_y hn h t := by
  intro hxy
  exact contact_pairs_distinct hn h.1.1 (congrArg Subtype.val hxy)

/-- The sign `s₀ = sgn det(r, m − a)|_{P₀}` of eq. s7c:bigon-signs, expressed through the frozen
`contactSign` (`= χ(P₋)`, `vertex_contact_signs`): `s₀ = χ(P₀)`, and `P₀ = P₋` iff the newborn side is
`P₊`.  So `s = δ_dir s₀ = contactSign` is automatic (`s7z_s₀_eq_chi`). -/
def s7z_s₀ (g : WallGerm n) (M a : ZMod n) (b : Bool) : ℤ :=
  if b then (g.contactSign M a : ℤ) else -(g.contactSign M a : ℤ)

/-- eq. s7c:bigon-signs: `s7z_s₀ g M a (s7z_side g M a)` IS `χ(P₀) = sgn det(r, m − a)|_{P₀}` on the
newborn-free side `P₀ = !s7z_side`, at every side parameter. -/
theorem s7z_s₀_eq_chi (h : g.BigonAt M a) (t : g.SideParameter) (b : Bool) :
    s7z_s₀ g M a b = (chi (g.sideTuple (!b) t).val a (a + 1) M : ℤ) := by
  obtain ⟨-, hm, hp⟩ := g.vertex_contact_signs h.1 t t
  unfold s7z_s₀
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [hp]; push_cast; ring
  · simp only [↓reduceIte, Bool.not_true]
    rw [hm]

/-- `ε = 1` when the newborn chords interlace, `0` otherwise (sm-4:409). -/
def s7z_eps (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (x y : Crossing P) : ℤ :=
  if Interlaces hn hP x y then 1 else 0

/-- An ELIGIBLE support (sm-4:419-421): a decomposition `T` of the newborn side missing the common
old neighbourhood `N` of `x, y` (no selected crossing interlaces both newborns). -/
def s7z_Eligible (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (x y : Crossing P)
    (T : Finset (Crossing P)) : Prop :=
  IsDecomposition hn hP T ∧ ∀ c ∈ T, ¬ (Interlaces hn hP x c ∧ Interlaces hn hP y c)

/-! #### C. The black boxes, as Props on an explicit newborn side `b`, newborns `x y`, persistent
bijection `e₀` and eligible bijection `e` (rule (3); instantiated at `s7z_side`, `s7z_x`, `s7z_y`) -/

/-- **Unit F's output** (PLAN §3.3 bigon (1), sm-4:396-455): (i) `e₀` is the persistent transport
(labels preserved; `s7a_cross` is `⟨x.val, _⟩`); (ii) `e` restricts an eligible support to the
two intervals (eq. s7c:eligible-bijection: the half crossing `c₁` of `λ₁` lies in `T₁` iff its
image label pair under `firstHalfIndex` lies in `T`; `λ₂` through `secondHalfEdgeIndex`); (iii) the
INELIGIBLE rows vanish: an ineligible or non-independent newborn-free `T` has equal terms on the two
sides and none of its newborn extensions is a support (sm-4:421-425); (iv) the TWO-NEWBORN row is
`(1−ε) s₀ · term(T₁) term(T₂)` (eq. s7c:sector-split with eq. s7c:triangle-data: at `ε = 0` the
contact triangle carries `wt · c = s₀`, the other carriers are those of `T₁, T₂`; at `ε = 1`
`T ∪ {x, y}` is not a support). -/
def s7z_FSector (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) (b : Bool)
    (x y : Crossing (g.curve (g.sideTime b t)))
    (e₀ : Finset (Crossing (g.curve (g.sideTime (!b) t))) ≃
      {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T})
    (e : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}) : Prop :=
  (∀ (S : Finset (Crossing (g.curve (g.sideTime (!b) t)))) (c : Crossing (g.curve (g.sideTime (!b) t))),
      c ∈ S ↔ ∃ c' ∈ (e₀ S).1, c'.val = c.val) ∧
  (∀ (T : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1}) (c₁ : Crossing (firstHalf g.center M a)),
      c₁ ∈ (e T).1.1 ↔ ∃ c ∈ T.1.1, c.val = c₁.val.image (firstHalfIndex M a)) ∧
  (∀ (T : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1}) (c₂ : Crossing (secondHalf g.center M a)),
      c₂ ∈ (e T).2.1 ↔ ∃ c ∈ T.1.1, c.val = c₂.val.image (secondHalfEdgeIndex M a)) ∧
  (∀ T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T},
      ¬ s7z_Eligible hn (s7a_sideGeneric g b) x y T.1 →
      s7e_term hn (s7a_sideGeneric g b) T.1 = s7e_term hn (s7a_sideGeneric g (!b)) (e₀.symm T) ∧
      s7e_term hn (s7a_sideGeneric g b) (insert x T.1) = 0 ∧
      s7e_term hn (s7a_sideGeneric g b) (insert y T.1) = 0 ∧
      s7e_term hn (s7a_sideGeneric g b) (insert x (insert y T.1)) = 0) ∧
  (∀ T : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1},
      s7e_term hn (s7a_sideGeneric g b) (insert x (insert y T.1.1)) =
        (1 - s7z_eps hn (s7a_sideGeneric g b) x y) * s7z_s₀ g M a b *
          (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ (e T).1.1 *
            s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ (e T).2.1))

/-- **The newborn-free returned row** (units SITE + BLOCK + ROT + RET, with the floor entries of J;
PLAN §3.3 bigon (2)-(5), sm-4:456-770, 785-825): for an eligible `T` the difference of the two
newborn-free terms is `ε s₀ · term(T₁) term(T₂)`: interlacing (`ε = 1`) `Ω_H − Ω_L = −ω₁ω₂`
(eq. s7c:interlacing-coefficient-result, `s7k_interlacing_row` + `s7k_interlacing_term`: the R-II
site `P(D_H^{sw}) = P(D_L)`, the skein, the two-component row, the rotation ledger, the floor at the
two uniform half contact carriers); noninterlacing (`ε = 0`) every returned row is zero
(eq. s7c:noninterlacing-return, `s7k_noninterlacing_row` / `s7k_different_block_row` +
`s7k_noninterlacing_term`: the floor at the two one-dissent half contact carriers). -/
def s7z_NewbornFreeRow (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) (b : Bool)
    (x y : Crossing (g.curve (g.sideTime b t)))
    (e₀ : Finset (Crossing (g.curve (g.sideTime (!b) t))) ≃
      {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T})
    (e : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}) : Prop :=
  ∀ T : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
      s7z_Eligible hn (s7a_sideGeneric g b) x y T.1},
    s7e_term hn (s7a_sideGeneric g b) T.1.1 - s7e_term hn (s7a_sideGeneric g (!b)) (e₀.symm T.1) =
      s7z_eps hn (s7a_sideGeneric g b) x y * s7z_s₀ g M a b *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ (e T).1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ (e T).2.1)

/-- **The one-newborn rows** (unit J with unit C; sm-4:693-723 and 777-788): for an eligible `T`
both one-newborn terms vanish — interlacing by their selectors (the daughter carrying the turn at
`m` also carries the opposite smoothing turn eq. s7c:one-newborn-turns, so it is mixed and its
weight is `0`, `carrierWeight_eq_zero_of_not_uniform`); noninterlacing by cb:singleton
(`hsing.isolated_zero` at `T ∪ {x}` with the isolated block `{y}`, `s7k_one_newborn_term_zero`). -/
def s7z_OneNewbornRows (hn : 3 ≤ n) (t : g.SideParameter) (b : Bool)
    (x y : Crossing (g.curve (g.sideTime b t))) : Prop :=
  ∀ T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T},
    s7z_Eligible hn (s7a_sideGeneric g b) x y T.1 →
    s7e_term hn (s7a_sideGeneric g b) (insert x T.1) = 0 ∧
    s7e_term hn (s7a_sideGeneric g b) (insert y T.1) = 0

/-- The ROW SECTOR at the side parameter `t`: the three black boxes on one persistent bijection
`e₀` and one eligible bijection `e` (the shape the algebra `s7z_law_of_rows` consumes). -/
def s7z_RowSector (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) (b : Bool)
    (x y : Crossing (g.curve (g.sideTime b t))) : Prop :=
  ∃ (e₀ : Finset (Crossing (g.curve (g.sideTime (!b) t))) ≃
      {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T})
    (e : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
    s7z_FSector hn h h₁ h₂ t b x y e₀ e ∧ s7z_NewbornFreeRow hn h h₁ h₂ t b x y e₀ e ∧
      s7z_OneNewbornRows hn t b x y

/-! #### D. The composition `B + R_ret = J` and the directed law (sm-4:874-908) -/

/-- The undirected law at one side parameter from its row sector: `Σ_{P₂} − Σ_{P₀} = s₀ C(λ₁) C(λ₂)`
(eq. s7c:bigon-total with `B = (1−ε)J`, `R_ret = εJ`, the one-newborn rows zero). -/
theorem s7z_undirected_of_rowSector (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (t : g.SideParameter) (b : Bool) (x y : Crossing (g.curve (g.sideTime b t))) (hxy : x ≠ y)
    (hsec : s7z_RowSector hn h h₁ h₂ t b x y) :
    cornerStateSum hn (g.sideTuple b t).property -
        cornerStateSum hn (g.sideTuple (!b) t).property =
      s7z_s₀ g M a b *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨e₀, e, ⟨-, -, -, hinel, htwo⟩, hret, hone⟩ := hsec
  rw [s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term,
    s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term]
  refine s7z_law_of_rows (s7e_term hn (s7a_sideGeneric g (!b))) (s7e_term hn (s7a_sideGeneric g b))
    (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂) x y hxy
    (s7z_Eligible hn (s7a_sideGeneric g b) x y)
    (IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
    (fun S hS => s7e_term_of_not _ _ hS) (fun S hS => s7e_term_of_not _ _ hS) e₀ e
    (s7z_s₀ g M a b) (fun T => ?_) (fun T hT => ?_)
  · -- the eligible row: `(f_H − f_L) + 0 + 0 + (1−ε) s₀ G = ε s₀ G + (1−ε) s₀ G = s₀ G`
    have h1 := hret T
    have h2 := hone T.1 T.2
    have h3 := htwo T
    rw [h2.1, h2.2, h3, h1]
    ring
  · -- the ineligible row: the newborn-free terms cancel, the extensions vanish
    obtain ⟨h0, h1, h2, h3⟩ := hinel T hT
    rw [h0, h1, h2, h3]; ring

/-- The DIRECTED law at one side parameter (eq. s7c:bigon-signs `s = δ_dir s₀`, here automatic from
`s7z_s₀`): `C(P₊) − C(P₋) = contactSign · C(λ₁) C(λ₂)` from the row sector at the newborn side. -/
theorem s7z_law_at_of_rowSector (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (t : g.SideParameter)
    (hsec : s7z_RowSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t)) :
    cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  have key := s7z_undirected_of_rowSector hn h h₁ h₂ t _ _ _ (s7z_x_ne_y hn h t) hsec
  cases hb : s7z_side g M a
  · rw [hb] at key
    simp only [Bool.not_false, s7z_s₀, Bool.false_eq_true, ↓reduceIte] at key
    linear_combination -key
  · rw [hb] at key
    simp only [Bool.not_true, s7z_s₀, ↓reduceIte] at key
    linear_combination key

/-- **The leaf modulo the row sector**: `s7_bigon_law_at`'s statement from the row sector available
below a radius (the bigon analogue of `s7e_sliding_law_at_of_contact`). -/
theorem s7z_bigon_law_at_of (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (hsec : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7z_RowSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨δ, hδ, hs⟩ := hsec
  exact ⟨δ, hδ, fun t ht => s7z_law_at_of_rowSector hn h h₁ h₂ t (hs t ht)⟩

/-! #### E. The black boxes (rule (3)): the three per-unit existence statements, `sorry` -/

/-- **BLACK BOX — unit F** (PLAN §3.3 bigon (1); U110-F, est. 1,500-2,200 lines per W3_BLOCK_REPORT §2.1):
below a radius the persistent bijection `e₀` and the eligible bijection `e` exist with the four
properties of `s7z_FSector`. -/
theorem s7z_F_exists (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ (e₀ : Finset (Crossing (g.curve (g.sideTime (!s7z_side g M a) t))) ≃
          {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
            s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T})
        (e : {T : {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
              s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T} //
            s7z_Eligible hn (s7a_sideGeneric g (s7z_side g M a)) (s7z_x hn h t) (s7z_y hn h t) T.1} ≃
          {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        s7z_FSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e := by
  sorry

/-- **BLACK BOX — units SITE + BLOCK + ROT + RET with the floor entries of J** (PLAN §3.3 bigon
(2)-(5)): below a radius, on the persistent and eligible bijections of `s7z_FSector` (which
determine them: labels), every eligible newborn-free row equals `ε s₀ · term(T₁) term(T₂)`.  The
floor `hF` enters at the two half contact carriers (uniform for `ε = 1`, one-dissent for `ε = 0`). -/
theorem s7z_returned_of_FSector (hF : FloorTheoremData) (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ (e₀ : Finset (Crossing (g.curve (g.sideTime (!s7z_side g M a) t))) ≃
          {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
            s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T})
        (e : {T : {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
              s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T} //
            s7z_Eligible hn (s7a_sideGeneric g (s7z_side g M a)) (s7z_x hn h t) (s7z_y hn h t) T.1} ≃
          {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        s7z_FSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e →
        s7z_NewbornFreeRow hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e := by
  sorry

/-- **BLACK BOX — unit J (cb:singleton) with unit C (the one-newborn selectors)** (sm-4:693-723,
777-788): below a radius both one-newborn terms of every eligible support vanish. -/
theorem s7z_oneNewborn_exists (hsing : CbSingletonData) (hn : 3 ≤ n) (h : g.BigonAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7z_OneNewbornRows hn t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) := by
  sorry

/-- The row sector below a radius, from the three black boxes (the radii intersected). -/
theorem s7z_exists_rowSector (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7z_RowSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) := by
  obtain ⟨δ₁, hδ₁, hFs⟩ := s7z_F_exists hn h h₁ h₂
  obtain ⟨δ₂, hδ₂, hR⟩ := s7z_returned_of_FSector hF hn h h₁ h₂
  obtain ⟨δ₃, hδ₃, hO⟩ := s7z_oneNewborn_exists hsing hn h
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun t ht => ?_⟩
  have ht₁ : t.val < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : t.val < δ₂ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
  have ht₃ : t.val < δ₃ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨e₀, e, hFe⟩ := hFs t ht₁
  exact ⟨e₀, e, hFe, hR t ht₂ e₀ e hFe, hO t ht₃⟩

/-! #### F. The F-ALIGNED assembly (W3_F_REPORT §0/§3): K's obligation on unit F's actual output shape.
Unit F delivers (`s7f_exists_law_residual`, at every `t` below a radius, on the supports `T₀` of the
newborn-free side `P₀` with the persistent lift `lift : Finset (Crossing P₀) → Finset (Crossing P₂)`
and the eligible supports `Elig`):
`C(P₊) − C(P₋) = (if ε then 0 else 1) · J + δ_dir · (Σ_{T₀ ∈ Elig} (term₂(lift T₀) − term₀ T₀)
+ Σ_{T₀ ∈ Elig} (term₂(T₀ ∪ {x}) + term₂(T₀ ∪ {y})))`.  The two theorems below take that identity as a
hypothesis with F's data abstracted (`α`, `lift`, `term₀`, `Elig`, `ε : Prop`, `d = δ_dir` with `d² = 1`
and `s₀ = d · s`, `e` the eligible bijection — `s7b_eligibleDecompositionEquiv` on `P₀`), and reduce the
leaf's law at `t` to exactly K's residual obligation "the second summand is `ε J`": the newborn-free
returned row `hrow` (SITE + BLOCK + ROT + RET + J's floor entries) and the one-newborn rows `hone`
(J's cb:singleton entry with C's selectors), both per eligible `T₀`. -/

omit [NeZero n] in
/-- The eligible rows over a finset `Elig`, matched with `Ind(λ₁) × Ind(λ₂)` by `e`, sum to
`c (Σ g₁)(Σ g₂)` (the half terms vanish off the decompositions). -/
theorem s7z_residual_sum {α γ₁ γ₂ : Type*} [Fintype γ₁] [Fintype γ₂]
    (r : α → ℤ) (g₁ : γ₁ → ℤ) (g₂ : γ₂ → ℤ) (D₁ : γ₁ → Prop) (D₂ : γ₂ → Prop)
    (hz₁ : ∀ S, ¬ D₁ S → g₁ S = 0) (hz₂ : ∀ S, ¬ D₂ S → g₂ S = 0)
    (Elig : Finset α) (e : {T₀ : α // T₀ ∈ Elig} ≃ {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}) (c : ℤ)
    (hrow : ∀ T₀ : {T₀ : α // T₀ ∈ Elig}, r T₀.1 = c * (g₁ (e T₀).1.1 * g₂ (e T₀).2.1)) :
    ∑ T₀ ∈ Elig, r T₀ = c * ((∑ S₁, g₁ S₁) * (∑ S₂, g₂ S₂)) := by
  classical
  rw [← Finset.sum_coe_sort Elig r]
  have he : ∑ T₀ : {T₀ : α // T₀ ∈ Elig}, r T₀.1 =
      ∑ q : {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}, c * (g₁ q.1.1 * g₂ q.2.1) :=
    Fintype.sum_equiv e _ _ hrow
  rw [he, ← Finset.mul_sum, Fintype.sum_prod_type, ← s7e_sum_full_eq_of_zero g₁ D₁ hz₁,
    ← s7e_sum_full_eq_of_zero g₂ D₂ hz₂, Finset.sum_mul_sum]

/-- `δ_dir` of eq. s7c:bigon-signs: `+1` iff `P₋ = P₀`, i.e. iff the newborn side is `P₊`. -/
def s7z_dirSign (g : WallGerm n) (M a : ZMod n) : ℤ := if s7z_side g M a then 1 else -1

omit [NeZero n] in
theorem s7z_dirSign_sq (g : WallGerm n) (M a : ZMod n) : s7z_dirSign g M a * s7z_dirSign g M a = 1 := by
  unfold s7z_dirSign; split_ifs <;> norm_num

omit [NeZero n] in
/-- `s₀ = δ_dir · s` (eq. s7c:bigon-signs), at the newborn side. -/
theorem s7z_s₀_eq_dirSign_mul (g : WallGerm n) (M a : ZMod n) :
    s7z_s₀ g M a (s7z_side g M a) = s7z_dirSign g M a * (g.contactSign M a : ℤ) := by
  unfold s7z_s₀ s7z_dirSign; split_ifs <;> ring

/-- **The directed law at `t` from unit F's residual identity** (its shape as a hypothesis `hres`) and K's
two residual obligations `hrow` (returned newborn-free rows `= ε s₀ · term(T₁) term(T₂)`) and `hone`
(one-newborn rows `= 0`): eq. s7c:bigon-total `B + R_ret = (1−ε)J + εJ = J`. -/
theorem s7z_law_at_of_residual (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (t : g.SideParameter) (b : Bool) (x y : Crossing (g.curve (g.sideTime b t)))
    (d : ℤ) (hd : d * d = 1) (hs₀ : s7z_s₀ g M a b = d * (g.contactSign M a : ℤ)) (ε : Prop)
    {α : Type*} (lift : α → Finset (Crossing (g.curve (g.sideTime b t)))) (term₀ : α → ℤ)
    (Elig : Finset α)
    (e : {T₀ : α // T₀ ∈ Elig} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂})
    (hres : cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (if ε then 0 else 1) *
          ((g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
              cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) +
        d * (∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (lift T₀) - term₀ T₀) +
          ∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) +
            s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀)))))
    (hrow : ∀ T₀ : {T₀ : α // T₀ ∈ Elig},
      s7e_term hn (s7a_sideGeneric g b) (lift T₀.1) - term₀ T₀.1 =
        (if ε then 1 else 0) * s7z_s₀ g M a b *
          (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ (e T₀).1.1 *
            s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ (e T₀).2.1))
    (hone : ∀ T₀ ∈ Elig, s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) = 0 ∧
      s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀)) = 0) :
    cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  have hone' : ∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) +
      s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀))) = 0 :=
    Finset.sum_eq_zero fun T₀ hT => by rw [(hone T₀ hT).1, (hone T₀ hT).2, add_zero]
  have hret : ∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (lift T₀) - term₀ T₀) =
      (if ε then 1 else 0) * s7z_s₀ g M a b *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
    rw [s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term]
    exact s7z_residual_sum _ _ _ _ _ (fun S hS => s7e_term_of_not _ _ hS)
      (fun S hS => s7e_term_of_not _ _ hS) Elig e _ hrow
  rw [hres, hret, hone', hs₀]
  by_cases hε : ε
  · simp only [hε, ↓reduceIte]
    linear_combination ((g.contactSign M a : ℤ) *
      (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
        cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) * hd
  · simp only [hε, ↓reduceIte]
    ring

/-- The per-`t` RESIDUAL DATA in unit F's vocabulary: a newborn side `b` with newborns `x y`, `δ_dir = d`,
`ε`, F's residual identity on some low-side index type `α` with lift, low terms and eligible finset, the
eligible bijection `e`, and K's two residual obligations.  (The assembler instantiates `b := s7f_side`,
`x y := s7f_x, s7f_y`, `d := s7f_dirSign`, `ε := s7f_Interlacing`, `α := Finset (Crossing P₀)`,
`lift := s7f_lift`, `term₀ := s7e_term hn hP₀`, `Elig := filter (s7f_Eligible)`, `e` from
`s7b_eligibleDecompositionEquiv` on `P₀`, `hres := s7f_law_residual`.) -/
def s7z_ResidualData (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) : Prop :=
  ∃ (b : Bool) (x y : Crossing (g.curve (g.sideTime b t))) (d : ℤ) (ε : Prop) (α : Type)
    (lift : α → Finset (Crossing (g.curve (g.sideTime b t)))) (term₀ : α → ℤ) (Elig : Finset α)
    (e : {T₀ : α // T₀ ∈ Elig} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
    d * d = 1 ∧ s7z_s₀ g M a b = d * (g.contactSign M a : ℤ) ∧
    (cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (if ε then 0 else 1) *
          ((g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
              cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) +
        d * (∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (lift T₀) - term₀ T₀) +
          ∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) +
            s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀))))) ∧
    (∀ T₀ : {T₀ : α // T₀ ∈ Elig},
      s7e_term hn (s7a_sideGeneric g b) (lift T₀.1) - term₀ T₀.1 =
        (if ε then 1 else 0) * s7z_s₀ g M a b *
          (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ (e T₀).1.1 *
            s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ (e T₀).2.1)) ∧
    (∀ T₀ ∈ Elig, s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) = 0 ∧
      s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀)) = 0)

/-- **The leaf modulo the residual data** (F-aligned form of `s7z_bigon_law_at_of`). -/
theorem s7z_bigon_law_at_of_residual (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (hres : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7z_ResidualData hn h h₁ h₂ t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨δ, hδ, hs⟩ := hres
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨b, x, y, d, ε, α, lift, term₀, Elig, e, hd, hs₀, hid, hrow, hone⟩ := hs t ht
  exact s7z_law_at_of_residual hn h h₁ h₂ t b x y d hd hs₀ ε lift term₀ Elig e hid hrow hone

end S7ZBigon

/-- The bigon branch (sm-4:407-874): two-newborn sector `B = (1−ε)J` (contact triangle: a crossing-free
uniform carrier, `corner_values_i`), universal skein extraction eq. s7c:universal-extraction (lp:core
skein, R-II deletion, oriented smoothing), lem:homflyrows two-component row, the rotation ledger, and the
two floor-dependent branches (interlacing: `Ω_H − Ω_L = −ω₁ω₂`; noninterlacing: every returned row zero,
the one-newborn rows by cb:singleton).  `a_floor` enters at the two half contact carriers (uniform for
`ε = 1`, one-dissent for `ε = 0`), read as carriers of the decompositions `T_i` of the generic halves
`λ_i` (sm-4:800-835); cb:singleton enters at the one-newborn rows (sm-4:777-783) — both printed
dependencies are explicit parameters. -/
theorem s7_bigon_law_at (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (g : WallGerm n) (M a : ZMod n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  exact s7z_bigon_law_at_of hn h h₁ h₂ (s7z_exists_rowSector hF hsing hn h h₁ h₂)


end VertexEdge

/-- **Row 110, conditional on thm:floor AND cb:singleton** (the printed dependency list of
tools/claims.py; library material).  PROVED from the two branch leaves: the wall is of bigon or sliding
type (`vertexEdge_bigon_or_sliding`); both side parameters are moved below the branch radius by chamber
constancy along each side (`cornerStateSum_side_eq`). -/
theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data := by
  refine ⟨?_⟩
  intro n _ hn g M a h h₁ h₂ tp tm
  obtain ⟨δ, hδ, hlaw⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂) := by
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact s7_bigon_law_at hF hsing hn g M a hb h₁ h₂
    · exact s7_sliding_law_at hn g M a hs h₁ h₂
  have hr := g.radius_pos
  let t : g.SideParameter := ⟨min δ g.radius / 2, by
    constructor
    · have := lt_min hδ hr; linarith
    · have := min_le_right δ g.radius; linarith⟩
  have ht : t.val < δ := by
    show min δ g.radius / 2 < δ
    have := min_le_left δ g.radius; linarith
  rw [cornerStateSum_side_eq hn g true tp t, cornerStateSum_side_eq hn g false tm t]
  exact hlaw t ht

/-- **Row 110, conditional on the floor alone** (the row theorem `SM.thm_C_S7 := thm_C_S7_of_floor
SM.thm_floor` once row 100 lands). -/
theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=
  thm_C_S7_of hF (cb_singleton_of_floor hF)


/-- Row 110 thm:C-S7 (FIXED target name, axiom-policy.json): the assembly on thm:floor (row 100). -/
theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor

end

end SM
