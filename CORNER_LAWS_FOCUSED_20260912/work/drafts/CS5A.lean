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

/-- Helper for thm:C-S5 (the "no crossing visit on `E_{c₁}`" step): the traversal successor of the
vertex mark `μ_i` whose outgoing edge `E_i` carries no crossing is the next vertex mark `μ_{i+1}`.
By `markSuccessor_position_cases` the only alternative is a mark on `E_i` at positive parameter,
which is a crossing visit on `E_i`. -/
theorem Carrier.markSuccessor_vertex_of_no_crossing (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i : ZMod n) (hi : ∀ c : Crossing P, i ∉ c.val) :
    Carrier.markSuccessor hn hP (Sum.inl i) = Sum.inl (i + 1) := by
  rcases Carrier.markSuccessor_position_cases hn hP (Sum.inl i) with ⟨hedge, hlt⟩ | h
  · exfalso
    generalize hm : Carrier.markSuccessor hn hP (Sum.inl i) = m at hedge hlt
    cases m with
    | inl k =>
      change (0 : ℝ) < 0 at hlt
      exact lt_irrefl _ hlt
    | inr v =>
      change v.2.val = i at hedge
      exact hi v.1 (by rw [← hedge]; exact v.2.property)
  · exact h

/-- thm:C-S5 as printed. -/
structure CS5Data : Prop where
  /-- "At a simple empty cusp, `C(P_no) = 0`": for every simple cusp wall germ, in its case, if the cusp is
  empty then the corner state sum vanishes at every polygon of the no-loop side. -/
  empty_cusp_zero : ∀ (n : ℕ) [NeZero n] (g : WallGerm n) (j : ZMod n) (h : g.CuspAt j) (b : Bool)
    (hc : CuspCase g.center j b), g.EmptyCusp h hc →
    ∀ t : g.SideParameter,
      cornerStateSum (by have := h.1; omega) (g.sideTuple (!(g.cuspLoopSide b j)) t).property = 0

theorem thm_C_S5 : CS5Data := by
  refine ⟨?_⟩
  intro n _ g j h b hc hempty t
  have hn : 3 ≤ n := by have := h.1; omega
  -- lem:cusp-sides, transported from the derived case to the given case `b` (the case is unique)
  obtain ⟨b', hc', hD₀⟩ := cusp_sides g h
  have hD : CuspSidesData g j h b hc := by
    have hbb : b = b' := hD₀.case_unique b hc
    subst hbb
    exact hD₀
  -- the polygon `P = P_no` on the no-loop side
  set P : LabelledTuple n := (g.sideTuple (!(g.cuspLoopSide b j)) t).val with hPdef
  have hP : Generic P := (g.sideTuple (!(g.cuspLoopSide b j)) t).property
  -- lem:cusp-sides (ii): opposite turns at the consecutive corners `c₁, c₂` on the no-loop side
  have hopp : turn P (cuspCorner₁ b j) = -turn P (cuspCorner₂ b j) := (hD.needle_turns t t).2
  -- lem:cusp-sides (iii): the cusp being empty, the intervening edge `E_{c₁}` carries no crossing
  have hnocross : ∀ c : Crossing P, cuspCorner₁ b j ∉ c.val :=
    hD.empty_middle_edge t (hempty t) (!(g.cuspLoopSide b j)) t
  -- the corners are consecutive: `c₂ = c₁ + 1`
  have hc12 : cuspCorner₁ b j + 1 = cuspCorner₂ b j := by
    show cuspFirst b j + 1 + 1 = cuspFirst b j + 2
    ring
  -- no decomposition `S` of `P` is uniform
  have hno : ∀ S : Finset (Crossing P), S ∉ uniformDecompositions hn hP := by
    intro S hS
    obtain ⟨hSind, hSuni⟩ := (mem_uniformDecompositions hn hP S).mp hS
    -- the arc from the vertex visit `c₁` to the vertex visit `c₂` along `E_{c₁}` has no selected
    -- visit, so smoothing keeps it: the smoothed successor of `μ_{c₁}` is `μ_{c₂}`
    have hsucc : Carrier.smoothingSuccessor hn hP S (Sum.inl (cuspCorner₁ b j)) =
        Sum.inl (cuspCorner₂ b j) := by
      rw [Carrier.smoothingSuccessor_vertex,
        Carrier.markSuccessor_vertex_of_no_crossing hn hP _ hnocross, hc12]
    -- hence both vertices lie on the same carrier `Q`
    have howner : Carrier.owner hn hP S (Sum.inl (cuspCorner₂ b j)) =
        Carrier.owner hn hP S (Sum.inl (cuspCorner₁ b j)) := by
      rw [← hsucc]
      exact Carrier.owner_successor hn hP S _
    -- both remain corners of `Q`, with their original turns
    obtain ⟨k₁, hk₁⟩ := Carrier.ccpCornerMark_exists hn hP S
      (Carrier.owner hn hP S (Sum.inl (cuspCorner₁ b j))) (Sum.inl (cuspCorner₁ b j)) rfl
      (Carrier.isTrueCorner_vertex S _)
    obtain ⟨k₂, hk₂⟩ := Carrier.ccpCornerMark_exists hn hP S
      (Carrier.owner hn hP S (Sum.inl (cuspCorner₁ b j))) (Sum.inl (cuspCorner₂ b j)) howner
      (Carrier.isTrueCorner_vertex S _)
    -- `S` uniform ⇒ `Q` uniform with sign `τ ≠ 0`; but the two turns are `τ` and `-τ`
    obtain ⟨τ, hτ, hall⟩ := hSuni (Carrier.owner hn hP S (Sum.inl (cuspCorner₁ b j)))
    have e₁ := hall k₁
    have e₂ := hall k₂
    rw [Carrier.ccpCornerPolygon_turn_vertex hn hP hSind _ k₁ _ hk₁] at e₁
    rw [Carrier.ccpCornerPolygon_turn_vertex hn hP hSind _ k₂ _ hk₂] at e₂
    rw [e₁, e₂] at hopp
    rcases τ with _ | _ | _
    · exact hτ rfl
    · exact absurd hopp (by decide)
    · exact absurd hopp (by decide)
  -- the index set of def:C is empty, so `C(P) = 0`
  show cornerStateSum hn hP = 0
  unfold cornerStateSum
  rw [Finset.sum_eq_zero, mul_zero]
  intro S _
  exact absurd S.2 (hno S.1)

end SM

#print axioms SM.thm_C_S5
