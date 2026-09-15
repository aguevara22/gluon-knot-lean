import SM.CornerStateSum
import SM.CuspSides

/-! Source thm:C-S5 (reference/SM/sm-4-knotlaws.tex:910-913, frame SM15): empty-cusp zero, "At a simple empty cusp,
`C(P_no) = 0`." Main declaration: `SM.thm_C_S5` (the fixed target name of work/lean/axiom-policy.json).

Notation (accepted rows def:germ, def:walls, lem:cusp-sides, def:C; SM/CuspDefinition.lean, CuspSideCrossings.lean,
CuspSides.lean, CornerStateSum.lean): a simple cusp wall germ at `j` is `g : WallGerm n` with `h : g.CuspAt j`
(def:walls (K): `n ≥ 4`, `Z_pt = {{j−1, j, j+1}}`, `Z_c = ∅`, `μ_j(0)` outside the closed segment
`[μ_{j−1}(0), μ_{j+1}(0)]`, `τ_j` changes sign); its case `b` (`CuspCase g.center j b`: A when `μ_{j+1}(0)` lies between
`μ_{j−1}(0)` and `μ_j(0)`, B when `μ_{j−1}(0)` lies between `μ_j(0)` and `μ_{j+1}(0)`) fixes the newborn pair
`{cuspFirst b j, cuspLast b j}`; the loop side is `g.cuspLoopSide b j` (the side on which the newborn pair is a
crossing, lem:cusp-sides (i)) and the no-loop side `P_no` is the other side, `g.sideTuple (!(g.cuspLoopSide b j)) t`
for every side parameter `t`; "the cusp is empty if on the loop side the two visits of the newborn crossing are
cyclically adjacent in the Gauss word" is `WallGerm.EmptyCusp` (`GaussVisitsAdjacent` of the two visits
`twoStepFirstVisit`/`twoStepLastVisit` of the newborn crossing, at every loop-side parameter); `C` is
`cornerStateSum` (def:C). -/

namespace SM

variable {n : ℕ} [NeZero n]

/-- def:walls (K): "The cusp is *empty* if on the loop side the two visits of the newborn crossing are
cyclically adjacent in the Gauss word." -/
def WallGerm.EmptyCusp (g : WallGerm n) {j : ZMod n} (h : g.CuspAt j) {b : Bool}
    (hc : CuspCase g.center j b) : Prop :=
  ∀ s : g.SideParameter,
    GaussVisitsAdjacent (by have := h.1; omega) (g.sideTuple (g.cuspLoopSide b j) s).property
      (twoStepFirstVisit (g.cusp_loop_crossing h hc s)) (twoStepLastVisit (g.cusp_loop_crossing h hc s))


/-! ### Angle B: the reusable carrier-lane lemma

"A generic polygon with two consecutive corners `i`, `i+1` of opposite turn whose connecting edge
`E_i` carries no crossing has `C = 0`." The proof is the printed argument for an arbitrary
decomposition `S` (sm-4-knotlaws.tex:934-965): the vertex marks `i` and `i+1` are adjacent on the
marked traversal circle because `E_i` carries no visit, so `smoothingSuccessor` (which fixes vertex
marks) sends one to the other and they share their carrier `q`; both are true corners of `q`, with
their original turns on `ccpCornerPolygon q`; hence `q` is not `CarrierUniform`, `S` is not uniform,
`uniformDecompositions = ∅`, and the sum defining `C` is empty. -/

open Carrier in
/-- On the marked traversal circle of a generic polygon the vertex mark `i` is followed by the
vertex mark `i+1` whenever the edge `E_i` carries no crossing visit (the marks strictly between the
two vertex marks are exactly the visits on `E_i`). -/
theorem Carrier.markSuccessor_vertex_of_no_crossing (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i : ZMod n) (hno : ∀ c : Crossing P, i ∉ c.val) :
    markSuccessor hn hP (Sum.inl i) = Sum.inl (i + 1) := by
  classical
  have hnb := markSuccessor_no_mark_between hn hP (Sum.inl i) (Sum.inl (i + 1))
  -- the successor is not the mark itself: a fixed point of the successor would be alone in its
  -- orbit, but every mark lies in the orbit of `inl i`
  have hne : markSuccessor hn hP (Sum.inl i) ≠ Sum.inl i := by
    intro hfix
    have heq : (Sum.inl i : Mark P) = Sum.inl (i + 1) :=
      (markSuccessor_sameCycle hn hP (Sum.inl i) (Sum.inl (i + 1))).eq_of_left hfix
    have h1 : (1 : ZMod n) = 0 := by linear_combination -(Sum.inl.inj heq)
    have := ZMod.one_eq_zero_iff.mp h1
    omega
  have hiv : i.val < n := ZMod.val_lt i
  have hi1 : (i + 1).val = (i.val + 1) % n := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < n by omega)]
  have hkey_i : traversalKey (markPosition hn hP.1 (Sum.inl i)) = (i.val : ℝ) := by
    simp [traversalKey, markPosition]
  have hkey_i1 : traversalKey (markPosition hn hP.1 (Sum.inl (i + 1))) = ((i + 1).val : ℝ) := by
    simp [traversalKey, markPosition]
  generalize hb : markSuccessor hn hP (Sum.inl i) = b at hnb hne
  rcases b with k | v
  · -- a vertex mark `k`: if `k ≠ i + 1` then `i + 1` lies strictly between `i` and `k`
    by_contra hk
    have hk' : k ≠ i + 1 := fun h => hk (by rw [h])
    have hki : k ≠ i := fun h => hne (by rw [h])
    have hkv : k.val < n := ZMod.val_lt k
    have hk1 : k.val ≠ (i + 1).val := fun h => hk' (ZMod.val_injective n h)
    have hk2 : k.val ≠ i.val := fun h => hki (ZMod.val_injective n h)
    have hkey_k : traversalKey (markPosition hn hP.1 (Sum.inl k)) = (k.val : ℝ) := by
      simp [traversalKey, markPosition]
    apply hnb
    unfold traversalBetween
    rw [hkey_i, hkey_i1, hkey_k]
    rcases Nat.lt_or_ge (i.val + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hi1
      rw [hi1] at hk1 ⊢
      rcases Nat.lt_or_gt_of_ne hk2 with hlt' | hgt'
      · right; right
        exact ⟨Nat.cast_lt.mpr hlt', Nat.cast_lt.mpr (by omega)⟩
      · left
        exact ⟨Nat.cast_lt.mpr (by omega), Nat.cast_lt.mpr (by omega)⟩
    · have hn1 : i.val + 1 = n := by omega
      rw [hn1, Nat.mod_self] at hi1
      rw [hi1] at hk1 ⊢
      right; left
      exact ⟨Nat.cast_lt.mpr (by omega), Nat.cast_lt.mpr (by omega)⟩
  · -- a crossing visit `v`: it lies on an edge `e ≠ i`, so `i + 1` lies strictly between
    exfalso
    have hev : v.2.val ≠ i := fun h => hno v.1 (h ▸ v.2.property)
    have hev' : v.2.val.val ≠ i.val := fun h => hev (ZMod.val_injective n h)
    have hvv : v.2.val.val < n := ZMod.val_lt _
    obtain ⟨ht0, ht1⟩ := visitPosition_interior hn hP.1 v
    have hkey_v : traversalKey (markPosition hn hP.1 (Sum.inr v)) =
        (v.2.val.val : ℝ) + visitParameter v := rfl
    apply hnb
    unfold traversalBetween
    rw [hkey_i, hkey_i1, hkey_v]
    rcases Nat.lt_or_ge (i.val + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hi1
      rw [hi1]
      rcases Nat.lt_or_gt_of_ne hev' with hlt' | hgt'
      · right; right
        have hR : (v.2.val.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hlt'
        constructor
        · linarith
        · push_cast; linarith
      · left
        have hR : (i.val : ℝ) + 1 ≤ v.2.val.val := by exact_mod_cast hgt'
        constructor
        · push_cast; linarith
        · push_cast; linarith
    · have hn1 : i.val + 1 = n := by omega
      rw [hn1, Nat.mod_self] at hi1
      rw [hi1]
      right; left
      have hlt' : v.2.val.val < i.val := by omega
      have hR : (v.2.val.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hlt'
      constructor
      · push_cast; linarith
      · linarith

open Carrier in
/-- The printed argument for one decomposition `S`: if the consecutive corners `i`, `i+1` have
opposite turns and `E_i` carries no crossing, then `S` is not uniform — the carrier `q` owning
both vertex marks has a left and a right true corner. -/
theorem not_uniformDecomposition_of_consecutive_opposite (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i : ZMod n) (hno : ∀ c : Crossing P, i ∉ c.val)
    (hopp : turn P (i + 1) = -turn P i) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) : ¬ UniformDecomposition hn hP S := by
  classical
  intro huni
  -- the vertex marks `i` and `i + 1` are smoothing-successor adjacent, hence share their carrier
  have hq1 : owner hn hP S (Sum.inl (i + 1)) = owner hn hP S (Sum.inl i) := by
    rw [← Carrier.markSuccessor_vertex_of_no_crossing hn hP i hno,
      ← smoothingSuccessor_vertex hn hP S i]
    exact owner_successor hn hP S (Sum.inl i)
  -- both are true corners of that carrier, with their original turns
  obtain ⟨j₁, hj₁⟩ := ccpCornerMark_exists hn hP S (owner hn hP S (Sum.inl i)) (Sum.inl i) rfl
    (isTrueCorner_vertex S i)
  obtain ⟨j₂, hj₂⟩ := ccpCornerMark_exists hn hP S (owner hn hP S (Sum.inl i)) (Sum.inl (i + 1))
    hq1 (isTrueCorner_vertex S (i + 1))
  have ht₁ := ccpCornerPolygon_turn_vertex hn hP hS _ j₁ i hj₁
  have ht₂ := ccpCornerPolygon_turn_vertex hn hP hS _ j₂ (i + 1) hj₂
  obtain ⟨τ, hτ, hall⟩ := huni (owner hn hP S (Sum.inl i))
  have h1 : τ = turn P i := by rw [← hall j₁, ht₁]
  have h2 : τ = -turn P i := by rw [← hall j₂, ht₂, hopp]
  have h3 : τ = -τ := by rw [← h1] at h2; exact h2
  apply hτ
  revert h3
  cases τ <;> decide

/-- No decomposition of such a polygon is uniform: the index set of `C` is empty. -/
theorem uniformDecompositions_eq_empty_of_consecutive_opposite (hn : 3 ≤ n)
    {P : LabelledTuple n} (hP : Generic P) (i : ZMod n) (hno : ∀ c : Crossing P, i ∉ c.val)
    (hopp : turn P (i + 1) = -turn P i) : uniformDecompositions hn hP = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro S hS
  obtain ⟨hind, huni⟩ := (mem_uniformDecompositions hn hP S).1 hS
  exact not_uniformDecomposition_of_consecutive_opposite hn hP i hno hopp hind huni

/-- **The reusable lemma.** A generic polygon with two consecutive corners `i`, `i+1` of opposite
turn whose connecting edge `E_i` carries no crossing has `C(P) = 0`
(sm-4-knotlaws.tex:934-965, the argument for an arbitrary decomposition `S`). -/
theorem cornerStateSum_eq_zero_of_consecutive_opposite (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i : ZMod n) (hno : ∀ c : Crossing P, i ∉ c.val)
    (hopp : turn P (i + 1) = -turn P i) : cornerStateSum hn hP = 0 := by
  rw [cornerStateSum_eq_sum_independentSupports, Finset.sum_eq_zero, mul_zero]
  intro S _
  exact ite_eq_right (not_uniformDecomposition_of_consecutive_opposite hn hP i hno hopp S.2)

omit [NeZero n] in
/-- `c₂ = c₁ + 1`: the cusp corners are consecutive, with intervening edge `E_{c₁}`
(CuspDefinition.lean: `cuspCorner₁ = cuspFirst + 1`, `cuspCorner₂ = cuspLast = cuspFirst + 2`). -/
theorem cuspCorner₂_eq_cuspCorner₁_add_one (b : Bool) (j : ZMod n) :
    cuspCorner₂ b j = cuspCorner₁ b j + 1 := by
  unfold cuspCorner₂ cuspCorner₁ cuspLast
  ring

/-- thm:C-S5 as printed. -/
structure CS5Data : Prop where
  /-- "At a simple empty cusp, `C(P_no) = 0`": for every simple cusp wall germ, in its case, if the cusp is
  empty then the corner state sum vanishes at every polygon of the no-loop side. -/
  empty_cusp_zero : ∀ (n : ℕ) [NeZero n] (g : WallGerm n) (j : ZMod n) (h : g.CuspAt j) (b : Bool)
    (hc : CuspCase g.center j b), g.EmptyCusp h hc →
    ∀ t : g.SideParameter,
      cornerStateSum (by have := h.1; omega) (g.sideTuple (!(g.cuspLoopSide b j)) t).property = 0

theorem thm_C_S5 : CS5Data where
  empty_cusp_zero := by
    intro n _ g j h b hc hempty t
    -- the accepted lem:cusp-sides bundle, in the case `b` (unique by `case_unique`)
    obtain ⟨b₀, hc₀, D⟩ := cusp_sides g h
    have hb : b = b₀ := D.case_unique b hc
    subst hb
    have hn3 : 3 ≤ n := by have := h.1; omega
    -- lem:cusp-sides (iii): the empty cusp puts no crossing of any side polygon on `E_{c₁}`
    have hno : ∀ c : Crossing (g.sideTuple (!(g.cuspLoopSide b j)) t).val,
        cuspCorner₁ b j ∉ c.val :=
      D.empty_middle_edge t (hempty t) (!(g.cuspLoopSide b j)) t
    -- lem:cusp-sides (ii): on the no-loop side `τ_{c₁} = -τ_{c₂}`
    have hopp := (D.needle_turns t t).2
    refine cornerStateSum_eq_zero_of_consecutive_opposite hn3
      (g.sideTuple (!(g.cuspLoopSide b j)) t).property (cuspCorner₁ b j) hno ?_
    rw [← cuspCorner₂_eq_cuspCorner₁_add_one, hopp, neg_neg]

end SM

#print axioms SM.thm_C_S5
