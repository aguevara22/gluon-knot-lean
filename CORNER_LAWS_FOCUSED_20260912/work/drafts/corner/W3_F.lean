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


/-! ### Unit U110-F (wave 3, prefix `s7f_`; PLAN_FINAL §3.3 bigon (1), sm-4:396-448: the two-newborn
sector `B = (1−ε)J`, eq. s7c:sector-split, and the row bookkeeping around it).

**The shape U110-K consumes** (stated first, as required).  Notation: `P₂ = g.curve (g.sideTime
(s7f_side g M a) t)` is the side carrying the two newborn crossings `x = {a, M−1}`, `y = {a, M}`
(`s7f_x`, `s7f_y`), `P₀` the other side, `δ_dir = s7f_dirSign g M a` (`+1` iff `P₋ = P₀`,
eq. s7c:bigon-signs), `ε := Interlaces hn hP₂ x y` (`s7f_Interlacing`), `s = g.contactSign M a`,
`J = s · C(λ₁) · C(λ₂)`, `term = s7e_term` (lem:C-X1's summand, `0` off `Ind`), `lift` the reading of a
support of `P₀` on `P₂` (`s7f_lift`; every crossing of `P₀` is persistent), `Eligible T₀` = every
crossing of `T₀` lifts into a half image (`T₀ ∩ N = ∅`, `s7f_Eligible`).

* `s7f_exists_law_residual` / `s7f_law_residual` — **the assembled shape**, below a radius:
  `C(P₊) − C(P₋) = (1−ε)·J + δ_dir·(Σ_{eligible T₀} (term₂(lift T₀) − term₀(T₀)) +
  Σ_{eligible T₀} (term₂(T₀∪{x}) + term₂(T₀∪{y})))`.  U110-K's remaining obligation is exactly sm-4:448
  "`R_ret = ε·J`" for the second summand (skein extraction G, two-component row H, rotation ledger I,
  floor J, cb:singleton).
* `s7f_sector_split` — **eq. s7c:sector-split** `δ_dir · Σ_two(P₂) = (1−ε)·J` below a radius
  (`ε = 1` PROVED outright: `s7f_twoNewbornSum_eq_zero`; `ε = 0` from black boxes 1-2).
* `s7f_law_decomposition` (every `t`, no radius, no black box): `C(P₊) − C(P₋) = δ_dir · ((Σ_pers(P₂) −
  C(P₀)) + Σ_one(P₂) + Σ_two(P₂))`; `s7f_persistentSum_eq_sum_lift`, `s7f_oneNewbornSum_eq_sum_lift`
  rewrite the first two sectors over the supports of `P₀` (PROVED); `s7f_oneNewbornSum_of_split`
  restricts `Σ_one` to the eligible `T₀` (PROVED from the split); `s7f_persistent_difference_of_transport`
  restricts `Σ_pers − C(P₀)` to the eligible rows (from black box 3).
* `s7f_term_eq_zero_of_ineligible` — sm-4:418-420 "if `T` meets `N`, both newborns are dominated": every
  one- or two-newborn support containing an ineligible old crossing has term `0`.  PROVED (pure).
* `s7f_twoNewbornDecompositionEquiv` — eq. s7c:eligible-bijection on the two-newborn rows at `ε = 0`:
  `{T' ∈ Ind(G_{P₂}) : x, y ∈ T'} ≃ Ind(G_{λ₁}) × Ind(G_{λ₂})`, `T' = {x, y} ∪ ι₁T₁ ∪ ι₂T₂`
  (`s7f_BigonSplit.twoNewbornEquiv`, U110-B's `eligibleEquiv` pattern).  PROVED.
* `s7f_bigonSplit_of` — the split from its open geometric fields only (`inj/disjoint/x_not/y_not` are
  U110-B's).  PROVED.
* `s7f_triangle_data` — eq. s7c:triangle-data on a carrier (`wt = s₀`, `|rot| = 1`, `d = 0`, `c = 1` from
  `s7c_carrierWeight_triangle` and row 105 `corner_values_of_floor hF`).  PROVED.

**Black boxes** (`sorry`, geometric; stated exactly as consumed — see W3_F_REPORT.md §2):
1. `s7f_exists_bigonSplit`: the bigon support split of `P₂` — U110-B §2.2's `rel₁ rel₂ cross cross'` in
   their bigon form on `P₂`, the newborns' independence from the half images (`x_free y_free`) and the
   dichotomy "an old crossing interlacing neither newborn lies in a half image" (`x_split y_split`,
   sm-4:414-416).  Reduced to those fields by `s7f_bigonSplit_of`.
2. `s7f_exists_twoNewbornTerm`: the `ε = 0` termwise identity, sm-4:434-447 — `T ∪ {x, y}` smooths to
   the contact triangle (three corners of turn `−s₀`, crossing-free uniform carrier, `wt = s₀`
   (`s7c_carrierWeight_triangle`), coefficient `1` by `corner_values`(i)) plus the successors of
   `T₁, T₂`: `term(T ∪ {x, y}) = s₀ · term(T₁) · term(T₂)` with `s₀ = δ_dir · s` (`s7f_s₀_eq_chi`).
3. `s7f_exists_ineligible_transport`: sm-4:418-421 — for an INELIGIBLE persistent support the terms on
   `P₂` and `P₀` agree (U110-A/A2/D transport with `x, y` MIXED crossings of the carriers).
Not this unit's (U110-K/G/H/I/J): the eligible persistent rows (skein extraction) and the eligible
one-newborn rows (cb:singleton). -/

section S7FBigonSides

variable {g : WallGerm n} {M a : ZMod n}

/-- The bigon side: `true` iff `P₊` carries the two newborn crossings (read at the base parameter;
constant along the side by `s7f_pattern`).  `P₂ := g.curve (g.sideTime (s7f_side g M a) t)`,
`P₀ := g.curve (g.sideTime (!s7f_side g M a) t)` (sm-4:397-399). -/
noncomputable def s7f_side (g : WallGerm n) (M a : ZMod n) : Bool :=
  decide (IsCrossing (g.sideTuple true g.sideBase).val {a, M})

/-- eq. s7c:bigon-signs: `δ_dir = +1` if `P₋ = P₀` (the newborns are on `P₊`), `−1` if `P₋ = P₂`. -/
def s7f_dirSign (g : WallGerm n) (M a : ZMod n) : ℤ := if s7f_side g M a then 1 else -1

omit [NeZero n] in
theorem s7f_dirSign_sq (g : WallGerm n) (M a : ZMod n) : s7f_dirSign g M a * s7f_dirSign g M a = 1 := by
  unfold s7f_dirSign
  split_ifs <;> norm_num

/-- The bigon crossing pattern of lem:wall-sides (V) (`vertex_sides`, `BigonCrossingPattern`) read
with the side `s7f_side`: `P₂(t)` has both contact crossings and `P₀(t)` neither, at EVERY `t`. -/
theorem s7f_pattern (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    IsCrossing (g.curve (g.sideTime (s7f_side g M a) t)) {a, M - 1} ∧
    IsCrossing (g.curve (g.sideTime (s7f_side g M a) t)) {a, M} ∧
    ¬ IsCrossing (g.curve (g.sideTime (!s7f_side g M a) t)) {a, M - 1} ∧
    ¬ IsCrossing (g.curve (g.sideTime (!s7f_side g M a) t)) {a, M} := by
  have hpat : BigonCrossingPattern (g.curve (g.sideTime true t)) (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 t t).2.1 h.2
  have hbase : BigonCrossingPattern (g.curve (g.sideTime true g.sideBase))
      (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 g.sideBase t).2.1 h.2
  unfold s7f_side
  by_cases hM : IsCrossing (g.sideTuple true g.sideBase).val {a, M}
  · rw [decide_eq_true hM]
    simp only [Bool.not_true]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, _, _, b4⟩ | ⟨_, b2, _, _⟩
      · exact b4 h4
      · exact b2 hM
  · rw [decide_eq_false hM]
    simp only [Bool.not_false]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, b2, _, _⟩ | ⟨_, _, _, b4⟩
      · exact hM b2
      · exact h4 b4
    · exact ⟨h3, h4, h1, h2⟩

omit [NeZero n] in
/-- Genericity of the newborn side `P₂(t)`. -/
theorem s7f_hP₂ (g : WallGerm n) (M a : ZMod n) (t : g.SideParameter) :
    Generic (g.curve (g.sideTime (s7f_side g M a) t)) := s7a_sideGeneric g _

omit [NeZero n] in
/-- Genericity of the newborn-free side `P₀(t)`. -/
theorem s7f_hP₀ (g : WallGerm n) (M a : ZMod n) (t : g.SideParameter) :
    Generic (g.curve (g.sideTime (!s7f_side g M a) t)) := s7a_sideGeneric g _

/-- The newborn crossing `x = {a, M − 1}` of `P₂(t)`. -/
noncomputable def s7f_x (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime (s7f_side g M a) t)) :=
  ⟨{a, M - 1}, (s7f_pattern hn h t).1⟩

/-- The newborn crossing `y = {a, M}` of `P₂(t)`. -/
noncomputable def s7f_y (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime (s7f_side g M a) t)) :=
  ⟨{a, M}, (s7f_pattern hn h t).2.1⟩

theorem s7f_x_val (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    (s7f_x hn h t).val = {a, M - 1} := rfl

theorem s7f_y_val (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    (s7f_y hn h t).val = {a, M} := rfl

theorem s7f_x_ne_y (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    s7f_x hn h t ≠ s7f_y hn h t :=
  fun he => contact_pairs_distinct hn h.1.1 (congrArg Subtype.val he)

theorem s7f_x_affected (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    ContactAffected M a (s7f_x hn h t).val := Or.inl rfl

theorem s7f_y_affected (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    ContactAffected M a (s7f_y hn h t).val := Or.inr rfl

/-- `x` and `y` are the ONLY contact-affected crossings of `P₂(t)`. -/
theorem s7f_eq_x_or_y_of_affected (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter)
    (z : Crossing (g.curve (g.sideTime (s7f_side g M a) t))) (hz : ContactAffected M a z.val) :
    z = s7f_x hn h t ∨ z = s7f_y hn h t := by
  rcases hz with hz | hz
  · exact Or.inl (Subtype.ext hz)
  · exact Or.inr (Subtype.ext hz)

/-- Every crossing of `P₀(t)` is persistent. -/
theorem s7f_P₀_not_affected (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter)
    (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) : ¬ ContactAffected M a z.val := by
  rintro (hz | hz)
  · exact (s7f_pattern hn h t).2.2.1 (hz ▸ z.property)
  · exact (s7f_pattern hn h t).2.2.2 (hz ▸ z.property)

/-- The last clause of `VertexCrossingData` (lem:wall-sides (V)) at a vertex–edge wall: persistent
crossings of either side agree with the centre's (U110-B's `hQC` for the side `b`). -/
theorem s7f_hQC (hn : 3 ≤ n) (h : g.VertexEdgeAt M a) (t : g.SideParameter) (b : Bool) :
    ∀ s, ¬ ContactAffected M a s →
      (IsCrossing (g.curve (g.sideTime b t)) s ↔ IsCrossing g.center s) := by
  intro s hs
  have := ((vertex_sides hn g h).2.2.2.1 t t).2.2.2 s hs
  cases b
  · exact this.2
  · exact this.1

/-- `s₀ = δ_dir · s` is the contact sign read on `P₀` (eq. s7c:bigon-signs with
`vertex_contact_signs`: `χ(P₋) = s`, `χ(P₊) = −s`). -/
theorem s7f_s₀_eq_chi (h : g.BigonAt M a) (t : g.SideParameter) :
    s7f_dirSign g M a * (g.contactSign M a : ℤ) =
      (chi (g.curve (g.sideTime (!s7f_side g M a) t)) a (a + 1) M : ℤ) := by
  obtain ⟨-, hm, hp⟩ := g.vertex_contact_signs h.1 t t
  unfold s7f_dirSign
  cases s7f_side g M a
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    have : chi (g.curve (g.sideTime true t)) a (a + 1) M = -g.contactSign M a := hp
    rw [this, SignType.coe_neg]
    ring
  · simp only [Bool.not_true, ↓reduceIte, one_mul]
    have : chi (g.curve (g.sideTime false t)) a (a + 1) M = g.contactSign M a := hm
    rw [this]

end S7FBigonSides

section S7FSectors

variable {g : WallGerm n} {M a : ZMod n}

/-- The interlacing indicator `ε` of the two newborn chords (sm-4:409). -/
def s7f_Interlacing (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) : Prop :=
  Interlaces hn (s7f_hP₂ g M a t) (s7f_x hn h t) (s7f_y hn h t)

/-- The two-newborn sector of `P₂(t)` (undirected: `B = δ_dir · s7f_twoNewbornSum`). -/
noncomputable def s7f_twoNewbornSum (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
      (fun T => s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T), s7e_term hn (s7f_hP₂ g M a t) T

/-- The one-newborn sector of `P₂(t)`. -/
noncomputable def s7f_oneNewbornSum (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
      (fun T => (s7f_x hn h t ∈ T ∧ s7f_y hn h t ∉ T) ∨ (s7f_x hn h t ∉ T ∧ s7f_y hn h t ∈ T)),
    s7e_term hn (s7f_hP₂ g M a t) T

/-- The persistent (newborn-free) sector of `P₂(t)`. -/
noncomputable def s7f_persistentSum (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
      (fun T => s7f_x hn h t ∉ T ∧ s7f_y hn h t ∉ T), s7e_term hn (s7f_hP₂ g M a t) T

omit [NeZero n] in
/-- A finite sum split by two predicates into the three sectors "neither", "exactly one", "both"
(instance-free: the sectors are any finsets with the stated memberships). -/
theorem s7f_sum_split3 {ι : Type*} [Fintype ι] (F : ι → ℤ) (p q : ι → Prop) (s₀ s₁ s₂ : Finset ι)
    (h₀ : ∀ S, S ∈ s₀ ↔ ¬ p S ∧ ¬ q S) (h₁ : ∀ S, S ∈ s₁ ↔ (p S ∧ ¬ q S) ∨ (¬ p S ∧ q S))
    (h₂ : ∀ S, S ∈ s₂ ↔ p S ∧ q S) :
    ∑ S, F S = ∑ S ∈ s₀, F S + ∑ S ∈ s₁, F S + ∑ S ∈ s₂, F S := by
  classical
  have hd₀₁ : Disjoint s₀ s₁ := Finset.disjoint_left.mpr fun S hs0 hs1 => by
    have a0 := (h₀ S).mp hs0
    have a1 := (h₁ S).mp hs1
    tauto
  have hd₀₁₂ : Disjoint (s₀ ∪ s₁) s₂ := Finset.disjoint_left.mpr fun S hs hs2 => by
    rw [Finset.mem_union] at hs
    have a2 := (h₂ S).mp hs2
    rcases hs with hs | hs
    · have a0 := (h₀ S).mp hs
      tauto
    · have a1 := (h₁ S).mp hs
      tauto
  have hu : s₀ ∪ s₁ ∪ s₂ = Finset.univ := by
    ext S
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, h₀, h₁, h₂]
    tauto
  rw [← Finset.sum_union hd₀₁, ← Finset.sum_union hd₀₁₂, hu]

/-- lem:C-X1 on `P₂(t)` split into the three newborn sectors. -/
theorem s7f_cornerStateSum_P₂ (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    cornerStateSum hn (s7f_hP₂ g M a t) =
      s7f_persistentSum hn h t + s7f_oneNewbornSum hn h t + s7f_twoNewbornSum hn h t := by
  rw [s7e_cornerStateSum_eq_sum_term]
  unfold s7f_persistentSum s7f_oneNewbornSum s7f_twoNewbornSum
  exact s7f_sum_split3 (s7e_term hn (s7f_hP₂ g M a t)) (fun T => s7f_x hn h t ∈ T)
    (fun T => s7f_y hn h t ∈ T) _ _ _
    (fun S => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun S => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun S => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])

theorem s7f_directed_difference_aux (hn : 3 ≤ n) (g : WallGerm n) (t : g.SideParameter) (b : Bool) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      (if b then 1 else -1 : ℤ) *
        (cornerStateSum hn (s7a_sideGeneric g (t := t) b) -
          cornerStateSum hn (s7a_sideGeneric g (t := t) (!b))) := by
  have ep : cornerStateSum hn (g.sideTuple true t).property =
      cornerStateSum hn (s7a_sideGeneric g (t := t) true) := rfl
  have em : cornerStateSum hn (g.sideTuple false t).property =
      cornerStateSum hn (s7a_sideGeneric g (t := t) false) := rfl
  rw [ep, em]
  cases b
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    ring
  · simp only [Bool.not_true, ↓reduceIte, one_mul]

/-- The directed difference (sm-4:399-406): `C(P₊) − C(P₋) = δ_dir (C(P₂) − C(P₀))`. -/
theorem s7f_directed_difference (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (t : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      s7f_dirSign g M a * (cornerStateSum hn (s7f_hP₂ g M a t) - cornerStateSum hn (s7f_hP₀ g M a t)) :=
  s7f_directed_difference_aux hn g t (s7f_side g M a)

/-- **The row decomposition for U110-K** (sm-4:396-448): the directed difference is `δ_dir` times the
persistent-sector difference, the one-newborn sector and the two-newborn sector of `P₂`.  The last is
`B` (eq. s7c:sector-split, `s7f_sector_split`); the first two form `R_ret` (sm-4:448, U110-K). -/
theorem s7f_law_decomposition (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      s7f_dirSign g M a *
        ((s7f_persistentSum hn h t - cornerStateSum hn (s7f_hP₀ g M a t)) +
          s7f_oneNewbornSum hn h t + s7f_twoNewbornSum hn h t) := by
  rw [s7f_directed_difference hn g M a t, s7f_cornerStateSum_P₂ hn h t]
  ring

/-- **`ε = 1`: the two-newborn sector is empty** (sm-4:445 "When `ε = 1` it is empty"): a support
containing two interlacing crossings is not a decomposition. -/
theorem s7f_twoNewbornSum_eq_zero (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter)
    (hI : s7f_Interlacing hn h t) : s7f_twoNewbornSum hn h t = 0 := by
  apply Finset.sum_eq_zero
  intro T hT
  have hxy := (Finset.mem_filter.mp hT).2
  apply s7e_term_of_not
  intro hdec
  rw [s7b_isDecomposition_iff_indep] at hdec
  exact hdec _ hxy.1 _ hxy.2 (s7f_x_ne_y hn h t) hI

end S7FSectors

section S7FSplit

/-! #### The bigon support split (abstract; U110-B part IV's pattern).  `R` is the interlacement
relation of `P₂`, `R₁, R₂` those of the halves, `ι₁, ι₂` the half crossing maps into `P₂`, `x, y` the
two newborns.  Beyond `s7b_SupportSplit`: the newborns lie outside both images and interlace nothing in
them (the newborn chords are independent of every internal label of `A` and `B`), and an old label
interlacing neither newborn is internal to one interval (`x_split`, `y_split`; the complement is the
common old neighbourhood `N`, sm-4:414-416). -/

variable {γ γ₁ γ₂ : Type*} [DecidableEq γ]

structure s7f_BigonSplit (R : γ → γ → Prop) (R₁ : γ₁ → γ₁ → Prop) (R₂ : γ₂ → γ₂ → Prop)
    (ι₁ : γ₁ → γ) (ι₂ : γ₂ → γ) (x y : γ) : Prop where
  split : s7b_SupportSplit R R₁ R₂ ι₁ ι₂
  x_not₁ : ∀ c, ι₁ c ≠ x
  x_not₂ : ∀ c, ι₂ c ≠ x
  y_not₁ : ∀ c, ι₁ c ≠ y
  y_not₂ : ∀ c, ι₂ c ≠ y
  x_free₁ : ∀ c, ¬ R x (ι₁ c) ∧ ¬ R (ι₁ c) x
  x_free₂ : ∀ c, ¬ R x (ι₂ c) ∧ ¬ R (ι₂ c) x
  y_free₁ : ∀ c, ¬ R y (ι₁ c) ∧ ¬ R (ι₁ c) y
  y_free₂ : ∀ c, ¬ R y (ι₂ c) ∧ ¬ R (ι₂ c) y
  x_split : ∀ z, z ≠ x → z ≠ y → ¬ R x z → ¬ R z x → z ∈ Set.range ι₁ ∪ Set.range ι₂
  y_split : ∀ z, z ≠ x → z ≠ y → ¬ R y z → ¬ R z y → z ∈ Set.range ι₁ ∪ Set.range ι₂

namespace s7f_BigonSplit

variable {R : γ → γ → Prop} {R₁ : γ₁ → γ₁ → Prop} {R₂ : γ₂ → γ₂ → Prop} {ι₁ : γ₁ → γ} {ι₂ : γ₂ → γ}
  {x y : γ}

omit [DecidableEq γ] in
/-- sm-4:418-420: an old support meeting `N` dominates both newborns — no extension by a newborn is
independent (the `x` case). -/
theorem not_indep_of_mem_x (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) {T : Finset γ}
    (hz : ∃ z ∈ T, z ≠ x ∧ z ≠ y ∧ z ∉ Set.range ι₁ ∪ Set.range ι₂) (hx : x ∈ T) :
    ¬ s7b_Indep R T := by
  intro hT
  obtain ⟨z, hzT, hzx, hzy, hzr⟩ := hz
  exact hzr (h.x_split z hzx hzy (hT x hx z hzT (Ne.symm hzx)) (hT z hzT x hx hzx))

omit [DecidableEq γ] in
/-- The `y` case. -/
theorem not_indep_of_mem_y (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) {T : Finset γ}
    (hz : ∃ z ∈ T, z ≠ x ∧ z ≠ y ∧ z ∉ Set.range ι₁ ∪ Set.range ι₂) (hy : y ∈ T) :
    ¬ s7b_Indep R T := by
  intro hT
  obtain ⟨z, hzT, hzx, hzy, hzr⟩ := hz
  exact hzr (h.y_split z hzx hzy (hT y hy z hzT (Ne.symm hzy)) (hT z hzT y hy hzy))

theorem indep_insert (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) (hxy : ¬ R x y ∧ ¬ R y x)
    {S₁ : Finset γ₁} {S₂ : Finset γ₂} (h₁ : s7b_Indep R₁ S₁) (h₂ : s7b_Indep R₂ S₂) :
    s7b_Indep R (insert x (insert y (h.split.joinSupport S₁ S₂))) := by
  intro u hu u' hu' hne hR
  rw [Finset.mem_insert, Finset.mem_insert] at hu hu'
  rcases hu with rfl | rfl | hu
  · rcases hu' with rfl | rfl | hu'
    · exact hne rfl
    · exact hxy.1 hR
    · rcases (h.split.mem_joinSupport _ _ u').mp hu' with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.x_free₁ c).1 hR
      · exact (h.x_free₂ c).1 hR
  · rcases hu' with rfl | rfl | hu'
    · exact hxy.2 hR
    · exact hne rfl
    · rcases (h.split.mem_joinSupport _ _ u').mp hu' with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.y_free₁ c).1 hR
      · exact (h.y_free₂ c).1 hR
  · rcases hu' with rfl | rfl | hu'
    · rcases (h.split.mem_joinSupport _ _ u).mp hu with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.x_free₁ c).2 hR
      · exact (h.x_free₂ c).2 hR
    · rcases (h.split.mem_joinSupport _ _ u).mp hu with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.y_free₁ c).2 hR
      · exact (h.y_free₂ c).2 hR
    · exact h.split.indep_joinSupport h₁ h₂ u hu u' hu' hne hR

theorem pre₁_insert [Fintype γ₁] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) (S : Finset γ) :
    s7b_pre ι₁ (insert x (insert y S)) = s7b_pre ι₁ S := by
  ext c
  rw [s7b_mem_pre, s7b_mem_pre, Finset.mem_insert, Finset.mem_insert]
  exact ⟨fun hc => (hc.resolve_left (h.x_not₁ c)).resolve_left (h.y_not₁ c),
    fun hc => Or.inr (Or.inr hc)⟩

theorem pre₂_insert [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) (S : Finset γ) :
    s7b_pre ι₂ (insert x (insert y S)) = s7b_pre ι₂ S := by
  ext c
  rw [s7b_mem_pre, s7b_mem_pre, Finset.mem_insert, Finset.mem_insert]
  exact ⟨fun hc => (hc.resolve_left (h.x_not₂ c)).resolve_left (h.y_not₂ c),
    fun hc => Or.inr (Or.inr hc)⟩

theorem insert_join_pre [Fintype γ₁] [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y)
    {S : Finset γ} (hS : s7b_Indep R S) (hx : x ∈ S) (hy : y ∈ S) :
    insert x (insert y (h.split.joinSupport (s7b_pre ι₁ S) (s7b_pre ι₂ S))) = S := by
  ext z
  rw [Finset.mem_insert, Finset.mem_insert, h.split.mem_joinSupport]
  constructor
  · rintro (rfl | rfl | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact hx
    · exact hy
    · exact (s7b_mem_pre ι₁ S c).mp hc
    · exact (s7b_mem_pre ι₂ S c).mp hc
  · intro hz
    by_cases hzx : z = x
    · exact Or.inl hzx
    by_cases hzy : z = y
    · exact Or.inr (Or.inl hzy)
    right; right
    rcases h.x_split z hzx hzy (hS x hx z hz (Ne.symm hzx)) (hS z hz x hx hzx) with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨c, (s7b_mem_pre ι₁ S c).mpr hz, rfl⟩
    · exact Or.inr ⟨c, (s7b_mem_pre ι₂ S c).mpr hz, rfl⟩

/-- **eq. s7c:eligible-bijection on the two-newborn rows** (`ε = 0`, sm-4:434-435 "`T ∪ {x, y}` is a
support … every two-newborn support arises this way"), abstractly: independent sets of `R` containing
both newborns correspond to pairs of independent sets of `R₁`, `R₂`; the inverse is
`(T₁, T₂) ↦ {x, y} ∪ ι₁ T₁ ∪ ι₂ T₂`. -/
def twoNewbornEquiv [Fintype γ₁] [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y)
    (hxy : ¬ R x y ∧ ¬ R y x) :
    {S : Finset γ // s7b_Indep R S ∧ x ∈ S ∧ y ∈ S} ≃
      {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂} where
  toFun S := (⟨s7b_pre ι₁ S.1, h.split.indep_pre₁ S.2.1⟩,
    ⟨s7b_pre ι₂ S.1, h.split.indep_pre₂ S.2.1⟩)
  invFun p := ⟨insert x (insert y (h.split.joinSupport p.1.1 p.2.1)), h.indep_insert hxy p.1.2 p.2.2,
    Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  left_inv S := Subtype.ext (h.insert_join_pre S.2.1 S.2.2.1 S.2.2.2)
  right_inv p := by
    ext1
    · exact Subtype.ext ((h.pre₁_insert _).trans (h.split.pre₁_joinSupport _ _))
    · exact Subtype.ext ((h.pre₂_insert _).trans (h.split.pre₂_joinSupport _ _))

theorem twoNewbornEquiv_symm_apply [Fintype γ₁] [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y)
    (hxy : ¬ R x y ∧ ¬ R y x)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    ((h.twoNewbornEquiv hxy).symm p).1 = insert x (insert y (h.split.joinSupport p.1.1 p.2.1)) := rfl

theorem twoNewbornEquiv_apply [Fintype γ₁] [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y)
    (hxy : ¬ R x y ∧ ¬ R y x) (S : {S : Finset γ // s7b_Indep R S ∧ x ∈ S ∧ y ∈ S}) :
    ((h.twoNewbornEquiv hxy S).1.1 = s7b_pre ι₁ S.1) ∧ ((h.twoNewbornEquiv hxy S).2.1 = s7b_pre ι₂ S.1) :=
  ⟨rfl, rfl⟩

end s7f_BigonSplit

end S7FSplit

section S7FDecompositions

/-- **eq. s7c:eligible-bijection on the actual two-newborn decompositions** (`ε = 0`): given the
bigon split of the interlacement relations, `{T' ∈ Ind(G_{P₂}) : x, y ∈ T'} ≃ Ind(G_{λ₁}) × Ind(G_{λ₂})`
(`s7b_slidingDecompositionEquiv`'s pattern). -/
def s7f_twoNewbornDecompositionEquiv (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
    (x y : Crossing Q)
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x y)
    (hxy : ¬ Interlaces hn hQ x y ∧ ¬ Interlaces hn hQ y x) :
    {S : Finset (Crossing Q) // IsDecomposition hn hQ S ∧ x ∈ S ∧ y ∈ S} ≃
      {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂} where
  toFun S := (⟨s7b_pre _ S.1, (s7b_isDecomposition_iff_indep _ _ _).mpr
      (hsplit.split.indep_pre₁ ((s7b_isDecomposition_iff_indep _ _ _).mp S.2.1))⟩,
    ⟨s7b_pre _ S.1, (s7b_isDecomposition_iff_indep _ _ _).mpr
      (hsplit.split.indep_pre₂ ((s7b_isDecomposition_iff_indep _ _ _).mp S.2.1))⟩)
  invFun p := ⟨insert x (insert y (hsplit.split.joinSupport p.1.1 p.2.1)),
    (s7b_isDecomposition_iff_indep _ _ _).mpr (hsplit.indep_insert hxy
      ((s7b_isDecomposition_iff_indep _ _ _).mp p.1.2) ((s7b_isDecomposition_iff_indep _ _ _).mp p.2.2)),
    Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  left_inv S := Subtype.ext
    (hsplit.insert_join_pre ((s7b_isDecomposition_iff_indep _ _ _).mp S.2.1) S.2.2.1 S.2.2.2)
  right_inv p := by
    ext1
    · exact Subtype.ext ((hsplit.pre₁_insert _).trans (hsplit.split.pre₁_joinSupport _ _))
    · exact Subtype.ext ((hsplit.pre₂_insert _).trans (hsplit.split.pre₂_joinSupport _ _))

theorem s7f_twoNewbornDecompositionEquiv_symm_apply (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
    (x y : Crossing Q)
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x y)
    (hxy : ¬ Interlaces hn hQ x y ∧ ¬ Interlaces hn hQ y x)
    (q : {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂}) :
    ((s7f_twoNewbornDecompositionEquiv hn hsep hm hQC hQ h₁ h₂ x y hsplit hxy).symm q).1 =
      insert x (insert y (hsplit.split.joinSupport q.1.1 q.2.1)) := rfl

end S7FDecompositions

section S7FTriangle

/-- **eq. s7c:triangle-data on a carrier** (sm-4:437-441; the `ε = 0` contact triangle of BLACK BOX 2):
three corners of turn `−s₀` and no carrier crossing give `wt = s₀` (`s7c_carrierWeight_triangle`) and, by
row 105 `corner_values`(i) (`corner_values_of_floor hF`), `|rot| = 1`, `d = 0`, `c = 1`. -/
theorem s7f_triangle_data (hF : FloorTheoremData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S) {s₀ : SignType}
    (hs₀ : s₀ ≠ 0) (h3 : ccpCornerCount hn hP S q = 3)
    (hturn : ∀ j, turn (ccpCornerPolygon hn hP S q) j = -s₀)
    (hfree : carrierCrossingCount hn hP S q = 0) :
    carrierWeight hn hP S q = s₀ ∧ |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧
      cornerCoefficient hn hP S q hS = 1 := by
  have hw := s7c_carrierWeight_triangle hn hP S q hs₀ h3 hturn
  have hne : carrierWeight hn hP S q ≠ 0 := by
    rw [hw]
    rcases SignType.trichotomy s₀ with rfl | rfl | rfl
    · norm_num
    · exact absurd rfl hs₀
    · norm_num
  have hu : CarrierUniform hn hP S q := s7c_carrierUniform_of_weight_ne_zero hn hP S q hne
  exact ⟨hw, (corner_values_of_floor hF).embedded_value n hn P hP S hS q hu hfree⟩

end S7FTriangle

section S7FSectorSplit

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a)
  (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))

/-- **BLACK BOX 1 (geometric; U110-B §2.2 in its bigon form, U_S7B_REPORT §2.2/§2.4).**  Below a radius,
the interlacement relation of `P₂(t)` splits along the two half crossing maps with the newborns as in
`s7f_BigonSplit`: `rel₁ rel₂` (the halves' interlacement is the restriction of `P₂`'s), `cross cross'`
(no interlacement between the two images), the newborns' freedom from both images, and the dichotomy
`x_split`/`y_split` (sm-4:414-416; the converse of `s7b_isCrossing_firstHalf_image`).  The fields
`inj₁ inj₂ disjoint x_not y_not` are already proved in U110-B (`s7b_firstCrossingQ_injective`,
`s7b_firstCrossingQ_ne_secondCrossingQ`, `s7b_firstCrossingQ_not_affected` with `s7f_x_affected`);
`s7f_bigonSplit_of` below assembles them. -/
theorem s7f_exists_bigonSplit :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t) := by
  sorry

/-- **BLACK BOX 2 (geometric; sm-4:434-447, the `ε = 0` two-newborn row).**  Below a radius, for
non-interlacing newborns and eligible `T = ι₁ T₁ ∪ ι₂ T₂`, the selector-form term of `T ∪ {x, y}` on
`P₂` is `s₀ · term(T₁) · term(T₂)`, `s₀ = δ_dir · s` (`s7f_s₀_eq_chi`): smoothing the four newborn
visits makes the contact triangle — three corners of turn `−s₀` (`wt = s₀`, `s7c_carrierWeight_triangle`;
crossing-free uniform carrier of coefficient `1`, `corner_values`(i): `|rot| = 1`, `d = 0`, `c = 1`) —
and otherwise exactly the successors of `T₁, T₂` with equal weights and coefficients (U110-B §2.4's
bigon mark map with the two `μ_M`-vertices identified; U110-D's coefficient transport to the halves). -/
theorem s7f_exists_twoNewbornTerm :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t),
      ¬ s7f_Interlacing hn h t →
      ∀ (S₁ : Finset (Crossing (firstHalf g.center M a))) (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂) := by
  sorry

/-- sm-4:418-420 on `P₂(t)`: a one- or two-newborn support containing an ineligible old crossing
(outside both half images) is not a decomposition — its term is `0`.  PROVED from the split. -/
theorem s7f_term_eq_zero_of_ineligible (t : g.SideParameter)
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (T : Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))
    (hz : ∃ z ∈ T, z ≠ s7f_x hn h t ∧ z ≠ s7f_y hn h t ∧
      z ∉ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) ∪
        Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))))
    (hmem : s7f_x hn h t ∈ T ∨ s7f_y hn h t ∈ T) :
    s7e_term hn (s7f_hP₂ g M a t) T = 0 := by
  apply s7e_term_of_not
  intro hdec
  rw [s7b_isDecomposition_iff_indep] at hdec
  rcases hmem with hx | hy
  · exact hsplit.not_indep_of_mem_x hz hx hdec
  · exact hsplit.not_indep_of_mem_y hz hy hdec

/-- **`ε = 0`: the directed two-newborn sector is `J = s C(λ₁) C(λ₂)`** (sm-4:441-445 "Finite
distributivity and eq. s7c:bigon-signs show that the directed two-newborn sector is `J` when `ε = 0`"),
from the split and the termwise identity along `s7f_twoNewbornDecompositionEquiv`. -/
theorem s7f_twoNewbornSum_of_split (t : g.SideParameter)
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (hxy : ¬ Interlaces hn (s7f_hP₂ g M a t) (s7f_x hn h t) (s7f_y hn h t) ∧
      ¬ Interlaces hn (s7f_hP₂ g M a t) (s7f_y hn h t) (s7f_x hn h t))
    (hterm : ∀ (S₁ : Finset (Crossing (firstHalf g.center M a)))
        (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)) :
    s7f_dirSign g M a * s7f_twoNewbornSum hn h t =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  classical
  let e := s7f_twoNewbornDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))
    (s7f_hP₂ g M a t) h₁ h₂ (s7f_x hn h t) (s7f_y hn h t) hsplit hxy
  have h1 : ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
        (fun T => s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T), s7e_term hn (s7f_hP₂ g M a t) T =
      ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
        (fun T => IsDecomposition hn (s7f_hP₂ g M a t) T ∧ s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T),
        s7e_term hn (s7f_hP₂ g M a t) T := by
    symm
    apply Finset.sum_subset
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact hT.2
    · intro T hT hT'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hT'
      exact s7e_term_of_not _ _ (fun hd => hT' ⟨hd, hT⟩)
  have h1' : ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
        (fun T => IsDecomposition hn (s7f_hP₂ g M a t) T ∧ s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T),
        s7e_term hn (s7f_hP₂ g M a t) T =
      ∑ T : {T : Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))) //
        IsDecomposition hn (s7f_hP₂ g M a t) T ∧ s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T},
        s7e_term hn (s7f_hP₂ g M a t) T.1 :=
    Finset.sum_subtype _ (fun T => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _
  have h2 : ∑ T : {T : Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))) //
        IsDecomposition hn (s7f_hP₂ g M a t) T ∧ s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T},
        s7e_term hn (s7f_hP₂ g M a t) T.1 =
      ∑ q, s7e_term hn (s7f_hP₂ g M a t) (e.symm q).1 :=
    Fintype.sum_equiv e _ _ (fun S => by rw [Equiv.symm_apply_apply])
  have hq : ∀ q, s7e_term hn (s7f_hP₂ g M a t) (e.symm q).1 =
      (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ q.1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ q.2.1) :=
    fun q => hterm _ _ q.1.2 q.2.2
  have h3 : ∑ q, s7e_term hn (s7f_hP₂ g M a t) (e.symm q).1 =
      (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
    simp_rw [hq]
    rw [← Finset.mul_sum, Fintype.sum_prod_type,
      s7e_cornerStateSum_eq_sum_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁,
      s7e_cornerStateSum_eq_sum_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂,
      ← s7e_sum_full_eq_of_zero (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁) (fun S hS => s7e_term_of_not _ _ hS),
      ← s7e_sum_full_eq_of_zero (s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂) (fun S hS => s7e_term_of_not _ _ hS),
      Finset.sum_mul_sum]
  unfold s7f_twoNewbornSum
  rw [h1, h1', h2, h3]
  linear_combination ((g.contactSign M a : ℤ) *
    (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
      cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) * s7f_dirSign_sq g M a

/-- **eq. s7c:sector-split `B = (1 − ε) J` at one side parameter**, from the split and the `ε = 0`
termwise identity. -/
theorem s7f_sector_split_at (t : g.SideParameter)
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (hterm : ¬ s7f_Interlacing hn h t →
      ∀ (S₁ : Finset (Crossing (firstHalf g.center M a)))
        (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)) :
    s7f_dirSign g M a * s7f_twoNewbornSum hn h t =
      (if s7f_Interlacing hn h t then 0 else 1) *
        ((g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) := by
  by_cases hI : s7f_Interlacing hn h t
  · rw [ite_eq_left hI, s7f_twoNewbornSum_eq_zero hn h t hI, mul_zero, zero_mul]
  · rw [ite_eq_right hI, one_mul]
    exact s7f_twoNewbornSum_of_split hn g h h₁ h₂ t hsplit
      ⟨hI, fun hI' => hI (interlaces_symm _ _ hI')⟩ (hterm hI)

/-- **eq. s7c:sector-split `B = (1 − ε) J` below a radius — THE SHAPE FOR U110-K.**  With
`s7f_law_decomposition`, U110-K's remaining obligation is sm-4:448:
`δ_dir · ((Σ_pers(P₂) − C(P₀)) + Σ_one(P₂)) = ε · J` below a radius. -/
theorem s7f_sector_split :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7f_dirSign g M a * s7f_twoNewbornSum hn h t =
        (if s7f_Interlacing hn h t then 0 else 1) *
          ((g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
              cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) := by
  obtain ⟨δ₁, hδ₁, hsplit⟩ := s7f_exists_bigonSplit hn g h h₁ h₂
  obtain ⟨δ₂, hδ₂, hterm⟩ := s7f_exists_twoNewbornTerm hn g h h₁ h₂
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  exact s7f_sector_split_at hn g h h₁ h₂ t (hsplit t (lt_of_lt_of_le ht (min_le_left _ _)))
    (fun hI => hterm t (lt_of_lt_of_le ht (min_le_right _ _))
      (hsplit t (lt_of_lt_of_le ht (min_le_left _ _))) hI)

end S7FSectorSplit

section S7FSplitOf

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a)
  (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter)

/-- **The bigon split from its OPEN geometric fields only.**  `inj₁ inj₂ disjoint` and the newborn
exclusions `x_not y_not` are U110-B's (`s7b_firstCrossingQ_injective`, `s7b_firstCrossingQ_ne_secondCrossingQ`,
`s7b_firstCrossingQ_not_affected` against `s7f_x_affected`/`s7f_y_affected`), so BLACK BOX 1
(`s7f_exists_bigonSplit`) reduces to: `rel₁ rel₂` (U_S7B_REPORT §2.2, the halves' interlacement is the
restriction of `P₂`'s), `cross cross'` (no interlacement across the two half images), `x_free y_free`
(the newborn chords interlace no internal label of `A` or `B`) and `x_split y_split` (sm-4:414-416). -/
theorem s7f_bigonSplit_of
    (hrel₁ : ∀ c c', (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c') ↔ (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁) c c')
    (hrel₂ : ∀ c c', (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c') ↔ (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂) c c')
    (hcross : ∀ c₁ c₂, ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c₁) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c₂))
    (hcross' : ∀ c₁ c₂, ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c₂) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c₁))
    (hxfree₁ : ∀ c, ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_x hn h t) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ∧ ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) (s7f_x hn h t))
    (hxfree₂ : ∀ c, ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_x hn h t) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ∧ ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) (s7f_x hn h t))
    (hyfree₁ : ∀ c, ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_y hn h t) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ∧ ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) (s7f_y hn h t))
    (hyfree₂ : ∀ c, ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_y hn h t) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ∧ ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) (s7f_y hn h t))
    (hxsplit : ∀ z, z ≠ (s7f_x hn h t) → z ≠ (s7f_y hn h t) → ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_x hn h t) z → ¬ (Interlaces hn (s7f_hP₂ g M a t)) z (s7f_x hn h t) →
      z ∈ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) ∪ Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))))
    (hysplit : ∀ z, z ≠ (s7f_x hn h t) → z ≠ (s7f_y hn h t) → ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_y hn h t) z → ¬ (Interlaces hn (s7f_hP₂ g M a t)) z (s7f_y hn h t) →
      z ∈ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) ∪ Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))) :
    s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t)) (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁) (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂) (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) (s7f_x hn h t) (s7f_y hn h t) where
  split :=
    { inj₁ := s7b_firstCrossingQ_injective hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))
      inj₂ := s7b_secondCrossingQ_injective hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))
      disjoint := fun c₁ c₂ =>
        s7b_firstCrossingQ_ne_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)) c₁ c₂
      rel₁ := hrel₁
      rel₂ := hrel₂
      cross := hcross
      cross' := hcross' }
  x_not₁ := fun c he => s7b_firstCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1
    (s7f_hQC hn h.1 t (s7f_side g M a)) c (by rw [he]; exact s7f_x_affected hn h t)
  x_not₂ := fun c he => s7b_secondCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1
    (s7f_hQC hn h.1 t (s7f_side g M a)) c (by rw [he]; exact s7f_x_affected hn h t)
  y_not₁ := fun c he => s7b_firstCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1
    (s7f_hQC hn h.1 t (s7f_side g M a)) c (by rw [he]; exact s7f_y_affected hn h t)
  y_not₂ := fun c he => s7b_secondCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1
    (s7f_hQC hn h.1 t (s7f_side g M a)) c (by rw [he]; exact s7f_y_affected hn h t)
  x_free₁ := hxfree₁
  x_free₂ := hxfree₂
  y_free₁ := hyfree₁
  y_free₂ := hyfree₂
  x_split := hxsplit
  y_split := hysplit

end S7FSplitOf

section S7FPersistent

/-! #### The persistent sector of `P₂` as the supports of `P₀` (sm-4:418-421): every crossing of
`P₀(t)` is persistent and lifts to `P₂(t)`; the lifts are exactly the newborn-free supports.  The
ineligible rows cancel by the U110-A/A2/D transport (BLACK BOX 3), so the persistent-sector difference
`Σ_pers(P₂) − C(P₀)` reduces to the ELIGIBLE rows — the input of the skein branch (U110-K/G/H/I/J). -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a) (t : g.SideParameter)

include hn h in
/-- Persistent crossings agree between the two sides (both agree with the centre). -/
theorem s7f_hs : ∀ s, ¬ ContactAffected M a s →
    (IsCrossing (g.curve (g.sideTime (s7f_side g M a) t)) s ↔
      IsCrossing (g.curve (g.sideTime (!s7f_side g M a) t)) s) :=
  fun s hs => (s7f_hQC hn h.1 t (s7f_side g M a) s hs).trans (s7f_hQC hn h.1 t (!s7f_side g M a) s hs).symm

include hn h in
/-- A crossing of `P₀(t)` read on `P₂(t)`. -/
noncomputable def s7f_liftCross (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    Crossing (g.curve (g.sideTime (s7f_side g M a) t)) :=
  ⟨z.val, (s7f_hs hn g h t z.val (s7f_P₀_not_affected hn h t z)).mpr z.property⟩

theorem s7f_liftCross_val (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    (s7f_liftCross hn g h t z).val = z.val := rfl

theorem s7f_liftCross_injective : Function.Injective (s7f_liftCross hn g h t) :=
  fun z w he => Subtype.ext (show (s7f_liftCross hn g h t z).val = (s7f_liftCross hn g h t w).val from
    congrArg Subtype.val he)

theorem s7f_liftCross_ne_x (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    s7f_liftCross hn g h t z ≠ s7f_x hn h t := fun he =>
  s7f_P₀_not_affected hn h t z (by rw [← s7f_liftCross_val hn g h t z, he]; exact s7f_x_affected hn h t)

theorem s7f_liftCross_ne_y (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    s7f_liftCross hn g h t z ≠ s7f_y hn h t := fun he =>
  s7f_P₀_not_affected hn h t z (by rw [← s7f_liftCross_val hn g h t z, he]; exact s7f_y_affected hn h t)

/-- A crossing of `P₂(t)` other than the newborns is a lift. -/
theorem s7f_exists_liftCross (z : Crossing (g.curve (g.sideTime (s7f_side g M a) t)))
    (hx : z ≠ s7f_x hn h t) (hy : z ≠ s7f_y hn h t) : ∃ w, s7f_liftCross hn g h t w = z := by
  have hz : ¬ ContactAffected M a z.val := fun ha => by
    rcases s7f_eq_x_or_y_of_affected hn h t z ha with h' | h'
    · exact hx h'
    · exact hy h'
  exact ⟨⟨z.val, (s7f_hs hn g h t z.val hz).mp z.property⟩, Subtype.ext rfl⟩

/-- The lift of a support of `P₀(t)` to `P₂(t)` (the same crossing set). -/
noncomputable def s7f_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))) :
    Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))) :=
  T₀.map ⟨s7f_liftCross hn g h t, s7f_liftCross_injective hn g h t⟩

theorem s7f_mem_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))
    (z : Crossing (g.curve (g.sideTime (s7f_side g M a) t))) :
    z ∈ s7f_lift hn g h t T₀ ↔ ∃ w ∈ T₀, s7f_liftCross hn g h t w = z := by
  simp only [s7f_lift, Finset.mem_map, Function.Embedding.coeFn_mk]

theorem s7f_liftCross_mem_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))
    (w : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    s7f_liftCross hn g h t w ∈ s7f_lift hn g h t T₀ ↔ w ∈ T₀ :=
  Finset.mem_map' _

theorem s7f_x_not_mem_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))) :
    s7f_x hn h t ∉ s7f_lift hn g h t T₀ := fun hx => by
  obtain ⟨w, -, hw⟩ := (s7f_mem_lift hn g h t T₀ _).mp hx
  exact s7f_liftCross_ne_x hn g h t w hw

theorem s7f_y_not_mem_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))) :
    s7f_y hn h t ∉ s7f_lift hn g h t T₀ := fun hy => by
  obtain ⟨w, -, hw⟩ := (s7f_mem_lift hn g h t T₀ _).mp hy
  exact s7f_liftCross_ne_y hn g h t w hw

theorem s7f_lift_injective : Function.Injective (s7f_lift hn g h t) :=
  Finset.map_injective _

/-- Every newborn-free support of `P₂(t)` is the lift of a support of `P₀(t)`. -/
theorem s7f_lift_surj (T : Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))
    (hx : s7f_x hn h t ∉ T) (hy : s7f_y hn h t ∉ T) : ∃ T₀, s7f_lift hn g h t T₀ = T := by
  refine ⟨Finset.univ.filter (fun w => s7f_liftCross hn g h t w ∈ T), ?_⟩
  ext z
  rw [s7f_mem_lift]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (Finset.mem_filter.mp hw).2
  · intro hz
    obtain ⟨w, rfl⟩ := s7f_exists_liftCross hn g h t z (fun he => hx (he ▸ hz)) (fun he => hy (he ▸ hz))
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩

/-- The persistent sector of `P₂(t)` is the sum over the supports of `P₀(t)` of the lifted terms. -/
theorem s7f_persistentSum_eq_sum_lift :
    s7f_persistentSum hn h t =
      ∑ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))),
        s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) := by
  unfold s7f_persistentSum
  have himg : (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
      (fun T => s7f_x hn h t ∉ T ∧ s7f_y hn h t ∉ T) = Finset.univ.image (s7f_lift hn g h t) := by
    ext T
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hx, hy⟩
      obtain ⟨T₀, hT₀⟩ := s7f_lift_surj hn g h t T hx hy
      exact ⟨T₀, Finset.mem_univ _, hT₀⟩
    · rintro ⟨T₀, -, rfl⟩
      exact ⟨Finset.mem_univ _, s7f_x_not_mem_lift hn g h t T₀, s7f_y_not_mem_lift hn g h t T₀⟩
  rw [himg, Finset.sum_image (fun T₀ _ T₀' _ he => s7f_lift_injective hn g h t he)]

/-- An old support of `P₀(t)` is ELIGIBLE when every crossing lifts into one of the two half images
(`T ∩ N = ∅`, sm-4:416-417). -/
def s7f_Eligible (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))) : Prop :=
  ∀ z ∈ T₀, s7f_liftCross hn g h t z ∈
    Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) ∪ Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))

/-- **BLACK BOX 3 (geometric; sm-4:418-421 "Deleting their four visits identifies the complete smoothing
successor, owners, corners, rotations, carrier diagrams and coefficient reads. The entire ineligible
returned sector is therefore zero").**  Below a radius, an INELIGIBLE persistent row has equal terms on
the two sides: the support is persistent (U110-A `s7a_sideComponentEquiv`, U110-A2
`s7a2_carrierRotation_eq` for `hr`, U110-D `s7d_cornerCoefficient_eq_of_strictMono` — the exact pattern
of `s7e_term_eq`), and since a smoothed chord of `N` separates the two visits of each newborn, `x, y`
are MIXED crossings of `P₂`'s carriers, never self-crossings — so `hmem` holds with the carrier
crossing sets literally equal (`s7a_side_mem_carrierCrossings` + this separation fact). -/
theorem s7f_exists_ineligible_transport :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))), ¬ s7f_Eligible hn g h t T₀ →
        s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) = s7e_term hn (s7f_hP₀ g M a t) T₀ := by
  sorry

/-- sm-4:420-421: given the ineligible transport at `t`, the persistent-sector difference is the sum of
the ELIGIBLE row differences. -/
theorem s7f_persistent_difference_of_transport
    (htr : ∀ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))), ¬ s7f_Eligible hn g h t T₀ →
      s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) = s7e_term hn (s7f_hP₀ g M a t) T₀) :
    s7f_persistentSum hn h t - cornerStateSum hn (s7f_hP₀ g M a t) =
      ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
          (s7f_Eligible hn g h t),
        (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) := by
  rw [s7f_persistentSum_eq_sum_lift hn g h t, s7e_cornerStateSum_eq_sum_term, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (s7f_Eligible hn g h t)]
  have h0 : ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
      (fun T₀ => ¬ s7f_Eligible hn g h t T₀),
        (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) = 0 :=
    Finset.sum_eq_zero fun T₀ hT₀ => by rw [htr T₀ (Finset.mem_filter.mp hT₀).2, sub_self]
  rw [h0, add_zero]

/-- **The residual for U110-K** (sm-4:448 `R_ret = εJ`; with `s7f_sector_split` for `B`): given the
ineligible transport at `t`,
`C(P₊) − C(P₋) = δ_dir · (Σ_(eligible T₀) (term₂(lift T₀) − term₀(T₀)) + Σ_one(P₂) + Σ_two(P₂))`. -/
theorem s7f_law_decomposition_eligible
    (htr : ∀ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))), ¬ s7f_Eligible hn g h t T₀ →
      s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) = s7e_term hn (s7f_hP₀ g M a t) T₀) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      s7f_dirSign g M a *
        (∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
            (s7f_Eligible hn g h t),
          (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) +
          s7f_oneNewbornSum hn h t + s7f_twoNewbornSum hn h t) := by
  rw [s7f_law_decomposition hn h t, s7f_persistent_difference_of_transport hn g h t htr]

end S7FPersistent

section S7FOneNewborn

/-! #### The one-newborn sector of `P₂` as the supports of `P₀` (sm-4:418-420, 777-783): a one-newborn
support is `T₀ ∪ {x}` or `T₀ ∪ {y}` for a unique support `T₀` of `P₀`, and the ineligible rows vanish
(`s7f_term_eq_zero_of_ineligible`), so `Σ_one(P₂)` is a sum over the ELIGIBLE `T₀` — the input of the
cb:singleton step (U110-K/J). -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a)
  (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter)

theorem s7f_insert_x_lift_injective :
    Function.Injective (fun T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) =>
      insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) := by
  intro T₀ T₀' he
  apply s7f_lift_injective hn g h t
  rw [← Finset.erase_insert (s7f_x_not_mem_lift hn g h t T₀),
    ← Finset.erase_insert (s7f_x_not_mem_lift hn g h t T₀')]
  simp only at he
  rw [he]

theorem s7f_insert_y_lift_injective :
    Function.Injective (fun T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) =>
      insert (s7f_y hn h t) (s7f_lift hn g h t T₀)) := by
  intro T₀ T₀' he
  apply s7f_lift_injective hn g h t
  rw [← Finset.erase_insert (s7f_y_not_mem_lift hn g h t T₀),
    ← Finset.erase_insert (s7f_y_not_mem_lift hn g h t T₀')]
  simp only at he
  rw [he]

/-- The one-newborn supports of `P₂(t)` are the `T₀ ∪ {x}` and the `T₀ ∪ {y}`. -/
theorem s7f_oneNewborn_filter_eq :
    (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
        (fun T => (s7f_x hn h t ∈ T ∧ s7f_y hn h t ∉ T) ∨ (s7f_x hn h t ∉ T ∧ s7f_y hn h t ∈ T)) =
      Finset.univ.image (fun T₀ => insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) ∪
        Finset.univ.image (fun T₀ => insert (s7f_y hn h t) (s7f_lift hn g h t T₀)) := by
  ext T
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨-, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · left
      obtain ⟨T₀, hT₀⟩ := s7f_lift_surj hn g h t (T.erase (s7f_x hn h t)) (Finset.notMem_erase _ _)
        (fun hy' => hy (Finset.mem_of_mem_erase hy'))
      exact ⟨T₀, Finset.mem_univ _, by rw [hT₀, Finset.insert_erase hx]⟩
    · right
      obtain ⟨T₀, hT₀⟩ := s7f_lift_surj hn g h t (T.erase (s7f_y hn h t))
        (fun hx' => hx (Finset.mem_of_mem_erase hx')) (Finset.notMem_erase _ _)
      exact ⟨T₀, Finset.mem_univ _, by rw [hT₀, Finset.insert_erase hy]⟩
  · rintro (⟨T₀, -, rfl⟩ | ⟨T₀, -, rfl⟩)
    · refine ⟨Finset.mem_univ _, Or.inl ⟨Finset.mem_insert_self _ _, fun hy => ?_⟩⟩
      rcases Finset.mem_insert.mp hy with h' | h'
      · exact s7f_x_ne_y hn h t h'.symm
      · exact s7f_y_not_mem_lift hn g h t T₀ h'
    · refine ⟨Finset.mem_univ _, Or.inr ⟨fun hx => ?_, Finset.mem_insert_self _ _⟩⟩
      rcases Finset.mem_insert.mp hx with h' | h'
      · exact s7f_x_ne_y hn h t h'
      · exact s7f_x_not_mem_lift hn g h t T₀ h'

theorem s7f_oneNewborn_images_disjoint :
    Disjoint (Finset.univ.image (fun T₀ => insert (s7f_x hn h t) (s7f_lift hn g h t T₀)))
      (Finset.univ.image (fun T₀ => insert (s7f_y hn h t) (s7f_lift hn g h t T₀))) := by
  rw [Finset.disjoint_left]
  intro T hT₁ hT₂
  obtain ⟨T₀, -, rfl⟩ := Finset.mem_image.mp hT₁
  obtain ⟨T₀', -, he⟩ := Finset.mem_image.mp hT₂
  have hx : s7f_x hn h t ∈ insert (s7f_y hn h t) (s7f_lift hn g h t T₀') := by
    rw [he]; exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hx with h' | h'
  · exact s7f_x_ne_y hn h t h'
  · exact s7f_x_not_mem_lift hn g h t T₀' h'

/-- The one-newborn sector of `P₂(t)` as a sum over the supports of `P₀(t)`. -/
theorem s7f_oneNewbornSum_eq_sum_lift :
    s7f_oneNewbornSum hn h t =
      ∑ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))),
        (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
          s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀))) := by
  unfold s7f_oneNewbornSum
  rw [s7f_oneNewborn_filter_eq hn g h t, Finset.sum_union (s7f_oneNewborn_images_disjoint hn g h t),
    Finset.sum_image (fun T₀ _ T₀' _ he => s7f_insert_x_lift_injective hn g h t he),
    Finset.sum_image (fun T₀ _ T₀' _ he => s7f_insert_y_lift_injective hn g h t he),
    ← Finset.sum_add_distrib]

/-- **The one-newborn sector for U110-K** (sm-4:418-420 + 777-783): given the split at `t`, the
ineligible one-newborn rows vanish and `Σ_one(P₂)` is the sum over the ELIGIBLE `T₀` of
`term(T₀ ∪ {x}) + term(T₀ ∪ {y})`. -/
theorem s7f_oneNewbornSum_of_split
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t)) :
    s7f_oneNewbornSum hn h t =
      ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
          (s7f_Eligible hn g h t),
        (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
          s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀))) := by
  rw [s7f_oneNewbornSum_eq_sum_lift hn g h t,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (s7f_Eligible hn g h t)]
  have h0 : ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
      (fun T₀ => ¬ s7f_Eligible hn g h t T₀),
        (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
          s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀))) = 0 := by
    apply Finset.sum_eq_zero
    intro T₀ hT₀
    have hne := (Finset.mem_filter.mp hT₀).2
    unfold s7f_Eligible at hne
    push Not at hne
    obtain ⟨z, hz, hzr⟩ := hne
    have hzx := s7f_liftCross_ne_x hn g h t z
    have hzy := s7f_liftCross_ne_y hn g h t z
    have hzl : s7f_liftCross hn g h t z ∈ s7f_lift hn g h t T₀ := (s7f_liftCross_mem_lift hn g h t T₀ z).mpr hz
    rw [s7f_term_eq_zero_of_ineligible hn g h h₁ h₂ t hsplit _
        ⟨_, Finset.mem_insert_of_mem hzl, hzx, hzy, hzr⟩ (Or.inl (Finset.mem_insert_self _ _)),
      s7f_term_eq_zero_of_ineligible hn g h h₁ h₂ t hsplit _
        ⟨_, Finset.mem_insert_of_mem hzl, hzx, hzy, hzr⟩ (Or.inr (Finset.mem_insert_self _ _)), add_zero]
  rw [h0, add_zero]

end S7FOneNewborn

section S7FResidual

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a)
  (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))

/-- **THE SHAPE FOR U110-K, at one side parameter** (sm-4:396-448 assembled): given the bigon split, the
`ε = 0` termwise identity and the ineligible transport at `t`,
`C(P₊) − C(P₋) = (1 − ε)·J + δ_dir·(Σ_{eligible T₀} (term₂(T₀) − term₀(T₀)) + Σ_{eligible T₀} (term(T₀∪{x}) + term(T₀∪{y})))`,
`J = s·C(λ₁)·C(λ₂)`.  U110-K's obligation is that the second summand is `ε·J` (sm-4:448 onward:
skein extraction, two-component row, rotation ledger, floor and cb:singleton). -/
theorem s7f_law_residual (t : g.SideParameter)
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (hterm : ¬ s7f_Interlacing hn h t →
      ∀ (S₁ : Finset (Crossing (firstHalf g.center M a)))
        (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂))
    (htr : ∀ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))), ¬ s7f_Eligible hn g h t T₀ →
      s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) = s7e_term hn (s7f_hP₀ g M a t) T₀) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      (if s7f_Interlacing hn h t then 0 else 1) *
        ((g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) +
      s7f_dirSign g M a *
        (∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
            (s7f_Eligible hn g h t),
          (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) +
         ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
            (s7f_Eligible hn g h t),
          (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
            s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀)))) := by
  rw [s7f_law_decomposition_eligible hn g h t htr, s7f_oneNewbornSum_of_split hn g h h₁ h₂ t hsplit,
    ← s7f_sector_split_at hn g h h₁ h₂ t hsplit hterm]
  ring

/-- **THE SHAPE FOR U110-K, below a radius**, from the three black boxes `s7f_exists_bigonSplit`,
`s7f_exists_twoNewbornTerm`, `s7f_exists_ineligible_transport`. -/
theorem s7f_exists_law_residual :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
        (if s7f_Interlacing hn h t then 0 else 1) *
          ((g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
              cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) +
        s7f_dirSign g M a *
          (∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
              (s7f_Eligible hn g h t),
            (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) +
           ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
              (s7f_Eligible hn g h t),
            (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
              s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀)))) := by
  obtain ⟨δ₁, hδ₁, hsplit⟩ := s7f_exists_bigonSplit hn g h h₁ h₂
  obtain ⟨δ₂, hδ₂, hterm⟩ := s7f_exists_twoNewbornTerm hn g h h₁ h₂
  obtain ⟨δ₃, hδ₃, htr⟩ := s7f_exists_ineligible_transport hn g h
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun t ht => ?_⟩
  have ht₁ : t.val < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : t.val < δ₂ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
  have ht₃ : t.val < δ₃ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
  exact s7f_law_residual hn g h h₁ h₂ t (hsplit t ht₁) (fun hI => hterm t ht₂ (hsplit t ht₁) hI) (htr t ht₃)

end S7FResidual

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
  sorry


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
