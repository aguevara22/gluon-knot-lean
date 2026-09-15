import SM.ContactHalfInteriors
import SM.DeletionChamber
import SM.NamedWallPredicates

/-! Both clauses of source lem:children, under the printed simple wall
hypotheses. The flat branch reuses its proved full deletion/chamber theorem. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem vertex_halves_children (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n}
    (h : g.VertexEdgeAt M a) :
    Generic (firstHalf g.center M a) ∧ Generic (secondHalf g.center M a) ∧
      (3 ≤ firstHalfSize M a ∧ firstHalfSize M a ≤ n - 2) ∧
      (3 ≤ secondHalfSize M a ∧ secondHalfSize M a ≤ n - 2) ∧ Regular g.center := by
  have hs := contactHalfSizes_bounds hn h.1
  have hg := contact_halves_generic hn h.1 h.2.1 h.2.2.1 h.2.2.2.1
  exact ⟨hg.1, hg.2, hs.1, hs.2, contact_regular hn h.1 h.2.1⟩

theorem flat_children (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (h : g.FlatAt j) :
    ∃ hg : Generic (deleteVertex g.center j),
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
        ∃ ht : Generic (deleteVertex (g.curve t) j),
          (⟨deleteVertex (g.curve t) j, ht⟩ : GenericTuple n) ∈
            labelledChamber ⟨deleteVertex g.center j, hg⟩ ∧
          polygonProjection ⟨deleteVertex (g.curve t) j, ht⟩ ∈
            chamber (polygonProjection ⟨deleteVertex g.center j, hg⟩) := by
  refine ⟨generic_deleteVertex hn h.2.1 h.2.2.2.1 h.2.2.1, ?_⟩
  exact flat_deletion_chamber hn g h.2.1 h.2.2.2.1 h.2.2.1

def ChildrenData : Prop :=
  (∀ k : ℕ, ∀ _ : NeZero k, ∀ hk : 3 ≤ k, ∀ g : WallGerm (k + 1),
    ∀ j : ZMod (k + 1), g.FlatAt j →
      ∃ hg : Generic (deleteVertex g.center j),
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
          ∃ ht : Generic (deleteVertex (g.curve t) j),
            (⟨deleteVertex (g.curve t) j, ht⟩ : GenericTuple k) ∈
              labelledChamber ⟨deleteVertex g.center j, hg⟩ ∧
            polygonProjection ⟨deleteVertex (g.curve t) j, ht⟩ ∈
              chamber (polygonProjection ⟨deleteVertex g.center j, hg⟩)) ∧
  (∀ k : ℕ, ∀ _ : NeZero k, ∀ hk : 3 ≤ k, ∀ g : WallGerm k,
    ∀ M a : ZMod k, g.VertexEdgeAt M a →
      Generic (firstHalf g.center M a) ∧ Generic (secondHalf g.center M a) ∧
        (3 ≤ firstHalfSize M a ∧ firstHalfSize M a ≤ k - 2) ∧
        (3 ≤ secondHalfSize M a ∧ secondHalfSize M a ≤ k - 2) ∧ Regular g.center)

theorem children : ChildrenData := by
  exact ⟨fun k _ hk g j h => flat_children hk g h,
    fun k _ hk g M a h => vertex_halves_children hk g h⟩

end SM
