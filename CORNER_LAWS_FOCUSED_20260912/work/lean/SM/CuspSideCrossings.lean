import SM.CuspLocal
import SM.GermTurnSigns

/-! The source turn-sign change proves which actual connected germ side
has the newborn crossing. Side points may be chosen independently. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

theorem cusp_side_crossing_iff_turn {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (side : Bool) (s : g.SideParameter) :
    IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j} ↔
      turn (g.sideTuple side s).val j = -SignType.sign (cuspDelta g.center b j) := by
  obtain ⟨δ, hδ, hδr, hlocal⟩ := g.cusp_local_control h hc
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have habs : |(g.sideTime side t₀).val| = t₀.val := by
    cases side <;> simp [sideTime, abs_of_pos t₀.property.1]
  have hl := hlocal (g.sideTime side t₀) (by rw [habs]; exact ht₀)
  have ht := (hl.2.2.2 (g.sideTuple side t₀).property.1).1
  rw [generic_family_crossing_constant (by have hn := h.1; omega)
    (g.continuous_sideTuple side) s t₀,
    g.side_turn_constant side s t₀ j]
  exact ht

theorem cusp_side_no_crossing_iff_turn {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (side : Bool) (s : g.SideParameter) :
    (¬ IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j}) ↔
      turn (g.sideTuple side s).val j = SignType.sign (cuspDelta g.center b j) := by
  haveI : Fact (1 < n) := ⟨by have hn := h.1; omega⟩
  have ht : turn (g.sideTuple side s).val j ≠ 0 := by
    rw [turn_det]
    exact sign_ne_zero.mpr (g1_turn_nonzero (by have hn := h.1; omega) (g.sideTuple side s).property.1 j)
  have hd : SignType.sign (cuspDelta g.center b j) ≠ 0 :=
    sign_ne_zero.mpr (cusp_delta_ne_zero h.1 h.2.1 hc)
  rw [g.cusp_side_crossing_iff_turn h hc]
  exact (signType_eq_iff_ne_neg ht hd).symm

theorem cusp_crossing_sides_flip {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s t : g.SideParameter) :
    IsCrossing (g.sideTuple true s).val {cuspFirst b j, cuspLast b j} ↔
      ¬ IsCrossing (g.sideTuple false t).val {cuspFirst b j, cuspLast b j} := by
  have ho := g.turn_signChanges_opposite h.2.2.2.2 s t
  rw [g.cusp_side_crossing_iff_turn h hc, g.cusp_side_no_crossing_iff_turn h hc, ho.1, neg_inj]

/-- The actual crossing on the positive side determines the loop-side Bool.
Its uniqueness is proved below from the source SignChanges condition. -/
noncomputable def cuspLoopSide (b : Bool) (j : ZMod n) : Bool := by
  classical
  exact if IsCrossing (g.sideTuple true g.sideBase).val {cuspFirst b j, cuspLast b j}
    then true else false

theorem cusp_side_crossing_iff_loop {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (side : Bool) (s : g.SideParameter) :
    IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j} ↔ side = g.cuspLoopSide b j := by
  classical
  by_cases hp : IsCrossing (g.sideTuple true g.sideBase).val {cuspFirst b j, cuspLast b j}
  · have hl : g.cuspLoopSide b j = true := by simp only [cuspLoopSide, hp, ↓reduceIte]
    rw [hl]
    cases side
    · simp only [Bool.false_eq_true, iff_false]
      exact (g.cusp_crossing_sides_flip h hc g.sideBase s).mp hp
    · simp only [iff_true]
      exact (generic_family_crossing_constant (by have hn := h.1; omega)
        (g.continuous_sideTuple true) s g.sideBase _).mpr hp
  · have hl : g.cuspLoopSide b j = false := by simp only [cuspLoopSide, hp, ↓reduceIte]
    rw [hl]
    cases side
    · simp only [iff_true]
      by_contra hn
      exact hp ((g.cusp_crossing_sides_flip h hc g.sideBase s).mpr hn)
    · simp only [Bool.true_eq_false, iff_false]
      intro hs
      exact hp ((generic_family_crossing_constant (by have hn := h.1; omega)
        (g.continuous_sideTuple true) s g.sideBase _).mp hs)

theorem cusp_loop_side_unique {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) :
    ∃! side : Bool, ∀ s : g.SideParameter,
      IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j} := by
  refine ⟨g.cuspLoopSide b j, fun s => (g.cusp_side_crossing_iff_loop h hc _ s).mpr rfl, ?_⟩
  intro side hs
  exact (g.cusp_side_crossing_iff_loop h hc side g.sideBase).mp (hs g.sideBase)

theorem cusp_loop_crossing {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s : g.SideParameter) :
    IsCrossing (g.sideTuple (g.cuspLoopSide b j) s).val {cuspFirst b j, cuspLast b j} :=
  (g.cusp_side_crossing_iff_loop h hc _ s).mpr rfl

theorem cusp_no_loop_crossing {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s : g.SideParameter) :
    ¬ IsCrossing (g.sideTuple (!(g.cuspLoopSide b j)) s).val {cuspFirst b j, cuspLast b j} := by
  rw [g.cusp_side_crossing_iff_loop h hc]
  cases g.cuspLoopSide b j <;> decide

theorem cusp_loop_turns {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s t : g.SideParameter) :
    turn (g.sideTuple (g.cuspLoopSide b j) s).val j = -SignType.sign (cuspDelta g.center b j) ∧
    turn (g.sideTuple (!(g.cuspLoopSide b j)) t).val j = SignType.sign (cuspDelta g.center b j) ∧
    turn (g.sideTuple (g.cuspLoopSide b j) s).val j =
      -turn (g.sideTuple (!(g.cuspLoopSide b j)) t).val j ∧
    (turn (g.sideTuple (g.cuspLoopSide b j) s).val j = -1 ∨
      turn (g.sideTuple (g.cuspLoopSide b j) s).val j = 1) := by
  have hl := (g.cusp_side_crossing_iff_turn h hc _ s).mp (g.cusp_loop_crossing h hc s)
  have hn := (g.cusp_side_no_crossing_iff_turn h hc _ t).mp (g.cusp_no_loop_crossing h hc t)
  have hd : SignType.sign (cuspDelta g.center b j) ≠ 0 :=
    sign_ne_zero.mpr (cusp_delta_ne_zero h.1 h.2.1 hc)
  refine ⟨hl, hn, by rw [hl, hn], ?_⟩
  apply signType_nonzero_cases
  rw [hl]
  rcases signType_nonzero_cases hd with he | he <;> rw [he] <;> decide

end SM.WallGerm
