import SM.FlatWallSides
import SM.VertexSides
import SM.TripleWallSides
import SM.SilentSides

/-! All F/V/T/E/C clauses of source lem:wall-sides, under the original
transparent named-wall predicates. Each branch supplies one genuine common
local interval. The separate full def:walls and cusp lemma are not claimed. -/

namespace SM

variable {n : ℕ} [NeZero n]

def WallSidesData (hn : 3 ≤ n) (g : WallGerm n) : Prop :=
  (∀ j, ∀ h : g.FlatAt j, FlatWallSidesData g j h) ∧
  (∀ M a, g.VertexEdgeAt M a → VertexSidesData hn g M a) ∧
  (∀ e f k, g.TripleAt e f k → TripleWallSidesData hn g e f k) ∧
  (∀ M a, ∀ h : g.ExtensionAt M a,
    SilentSidesData hn g (Or.inl ⟨M, a, h⟩)) ∧
  (∀ i j k, ∀ h : g.PureCutAt i j k,
    SilentSidesData hn g (Or.inr ⟨i, j, k, h⟩))

theorem wall_sides (hn : 3 ≤ n) (g : WallGerm n) : WallSidesData hn g := by
  exact ⟨fun _ h => flat_wall_sides g h,
    fun _ _ h => vertex_sides hn g h,
    fun _ _ _ h => triple_wall_sides hn g h,
    fun M a h => silent_sides hn g (Or.inl ⟨M, a, h⟩),
    fun i j k h => silent_sides hn g (Or.inr ⟨i, j, k, h⟩)⟩

end SM
