import SM.EuclideanTuple

/-! Full lem:weak-open, read on labelled representatives as expressly required
by its source. Components are the actual connected components of the weak
locus. Polygonal connectivity uses finite straight-segment chains, and balls
use the Euclidean norm on all 2n real vertex coordinates. -/

namespace SM

open Set

variable {n : ℕ}

theorem labelledVisibleChamber_image (P : WeakTuple n) :
    Subtype.val '' labelledVisibleChamber P = connectedComponentIn (weakLocus n) P.val :=
  (connectedComponentIn_eq_image (F := weakLocus n) (x := P.val) P.property).symm

theorem weak_visible_components [NeZero n] (P : WeakTuple n) :
    IsOpen (Subtype.val '' labelledVisibleChamber P) ∧
    PolygonallyConnected (Subtype.val '' labelledVisibleChamber P) := by
  rw [labelledVisibleChamber_image]
  exact open_components_polygonallyConnected isOpen_WeakGeneric P.val

theorem weak_visible_euclidean_ball [NeZero n] (P : WeakTuple n) :
    ∃ r > 0, euclideanTupleBall P.val r ⊆ Subtype.val '' labelledVisibleChamber P :=
  exists_euclideanTupleBall_subset (weak_visible_components P).1
    ⟨P, mem_connectedComponent, rfl⟩

/-- All three clauses of the printed lemma, with the inherited n >= 3 domain
and no genericity, distance, intersection or connectivity hypotheses added. -/
theorem weak_open (hn : 3 ≤ n) :
    IsOpen (weakLocus n) ∧
    (∀ P : WeakTuple n,
      IsOpen (Subtype.val '' labelledVisibleChamber P) ∧
      PolygonallyConnected (Subtype.val '' labelledVisibleChamber P)) ∧
    (∀ P : WeakTuple n, ∃ r > 0,
      euclideanTupleBall P.val r ⊆ Subtype.val '' labelledVisibleChamber P) := by
  haveI : NeZero n := ⟨by omega⟩
  exact ⟨isOpen_WeakGeneric, weak_visible_components, weak_visible_euclidean_ball⟩

end SM
