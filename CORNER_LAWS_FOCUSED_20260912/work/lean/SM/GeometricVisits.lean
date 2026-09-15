import SM.CrossingGeometry
import SM.GaussWord

/-! Actual crossing visits and Gauss records on the proved geometric domain.
These agree with the accepted generic definitions, and also apply at flat
centres. No arbitrary word or separate crossing labels are introduced. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

noncomputable def geometricVisitPosition (h : CrossingGeometry P) (v : Visit P) :
    TraversalPoint n :=
  (v.2.val, ⟨visitParameter v,
    (crossingParameter_interior_of_geometry h v.1 v.2.val v.2.property).1.le,
    (crossingParameter_interior_of_geometry h v.1 v.2.val v.2.property).2⟩)

theorem geometricVisitPosition_evaluation (h : CrossingGeometry P) (v : Visit P) :
    traversalEvaluation P (geometricVisitPosition h v) = crossingPoint v.1 :=
  (crossingParameter_spec v.1 v.2.val v.2.property).2.2.symm

theorem geometricVisitPosition_injective (h : CrossingGeometry P) :
    Function.Injective (geometricVisitPosition h) := by
  intro v w he
  have hp : crossingPoint v.1 = crossingPoint w.1 := by
    rw [← geometricVisitPosition_evaluation h v, ← geometricVisitPosition_evaluation h w, he]
  have hc := crossingPoint_injective_of_geometry h hp
  have hi : v.2.val = w.2.val := congrArg Prod.fst he
  cases v with
  | mk c i =>
    cases w with
    | mk d j =>
      dsimp only at hc hi
      cases hc
      have hij : i = j := Subtype.ext hi
      cases hij
      rfl

noncomputable def geometricVisitKey (h : CrossingGeometry P) (v : Visit P) : ℝ :=
  traversalKey (geometricVisitPosition h v)

theorem geometricVisitKey_injective [NeZero n] (h : CrossingGeometry P) :
    Function.Injective (geometricVisitKey h) :=
  traversalKey_injective.comp (geometricVisitPosition_injective h)

@[instance_reducible]
noncomputable def geometricVisitLinearOrder [NeZero n] (h : CrossingGeometry P) :
    LinearOrder (Visit P) :=
  LinearOrder.lift' (geometricVisitKey h) (geometricVisitKey_injective h)

noncomputable def geometricGaussList [NeZero n] (h : CrossingGeometry P) : List (Visit P) := by
  classical
  letI := geometricVisitLinearOrder h
  exact Finset.univ.sort

noncomputable def geometricGaussWord [NeZero n] (h : CrossingGeometry P) :
    Cycle (Crossing P) := (geometricGaussList h : Cycle (Visit P)).map Sigma.fst

theorem geometricVisitPosition_eq_generic (hn : 3 ≤ n) (hP : Generic P)
    (h : CrossingGeometry P) (v : Visit P) :
    geometricVisitPosition h v = visitPosition hn hP.1 v := rfl

theorem geometricVisitKey_eq_generic (hn : 3 ≤ n) (hP : Generic P)
    (h : CrossingGeometry P) (v : Visit P) :
    geometricVisitKey h v = visitKey hn hP.1 v := rfl

theorem geometricGaussList_eq_generic [NeZero n] (hn : 3 ≤ n) (hP : Generic P)
    (h : CrossingGeometry P) : geometricGaussList h = gaussList hn hP := rfl

theorem geometricGaussWord_eq_generic [NeZero n] (hn : 3 ≤ n) (hP : Generic P)
    (h : CrossingGeometry P) : geometricGaussWord h = gaussWord hn hP := rfl

theorem mem_geometricGaussList [NeZero n] (h : CrossingGeometry P) (v : Visit P) :
    v ∈ geometricGaussList h := by
  classical
  letI := geometricVisitLinearOrder h
  exact (Finset.mem_sort _).mpr (Finset.mem_univ v)

theorem geometricGaussList_nodup [NeZero n] (h : CrossingGeometry P) :
    (geometricGaussList h).Nodup := by
  classical
  letI := geometricVisitLinearOrder h
  exact Finset.sort_nodup _ _

theorem geometricGaussList_length [NeZero n] (h : CrossingGeometry P) :
    (geometricGaussList h).length = 2 * Nat.card (Crossing P) := by
  classical
  letI := geometricVisitLinearOrder h
  change (Finset.univ.sort (α := Visit P)).length = _
  rw [Finset.length_sort, Finset.card_univ, card_visit, Nat.card_eq_fintype_card, card_crossing]

end SM
