import DirectGLSSW.PolygonCrossings
import Mathlib.Data.Prod.Lex

/-!
# Actual crossing visits and original vertex anchors

Source: frozen note, Section 1, especially lines 61–77 and 131–139.
This is the visit/anchor representation underlying the proposed smoothing
construction. False selects the smaller-label crossing edge (left); true
selects the larger-label edge (right). The traversal key uses original edge
labels and actual affine parameters, never crossing-pair order.

This candidate does not construct a cyclic successor or smoothing components.
-/

namespace DirectGLSSW

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- Exactly two visits of each actual crossing; false is left, true is right. -/
def CrossingVisit (q : Fin n → PlanarPoint K) := PolygonCrossing q × Bool

noncomputable instance crossingVisitFintype (q : Fin n → PlanarPoint K) :
    Fintype (CrossingVisit q) := by
  unfold CrossingVisit
  infer_instance

/-- The original outgoing edge at a visit, with the stated Boolean convention. -/
def crossingVisitEdge (q : Fin n → PlanarPoint K) (v : CrossingVisit q) : Fin n :=
  if v.2 then v.1.val.2 else v.1.val.1

/-- The actual oriented affine parameter on the selected incident edge. -/
noncomputable def crossingVisitParameter (q : Fin n → PlanarPoint K)
    (v : CrossingVisit q) : K :=
  if v.2 then crossingParameterRight q v.1 else crossingParameterLeft q v.1

/-- Both visits of a crossing have its already constructed actual plane point. -/
noncomputable def crossingVisitPoint (q : Fin n → PlanarPoint K)
    (v : CrossingVisit q) : PlanarPoint K := crossingPoint q v.1

/-- Traversal location consists of the original edge and its actual parameter. -/
noncomputable def crossingVisitKey (q : Fin n → PlanarPoint K)
    (v : CrossingVisit q) : Fin n × K :=
  (crossingVisitEdge q v, crossingVisitParameter q v)

/-- Pair the two visits of one crossing by exchanging their Boolean labels. -/
def crossingVisitFlip (q : Fin n → PlanarPoint K) (v : CrossingVisit q) :
    CrossingVisit q := (v.1, !v.2)

theorem crossingVisitFlip_involutive (q : Fin n → PlanarPoint K) :
    Function.Involutive (crossingVisitFlip q) := by
  rintro ⟨c, b⟩
  cases b <;> rfl

theorem crossingVisitFlip_ne_self (q : Fin n → PlanarPoint K)
    (v : CrossingVisit q) : crossingVisitFlip q v ≠ v := by
  rcases v with ⟨c, b⟩
  intro h
  have hb := congrArg Prod.snd h
  cases b <;> cases hb

theorem crossingVisitPoint_flip (q : Fin n → PlanarPoint K)
    (v : CrossingVisit q) : crossingVisitPoint q (crossingVisitFlip q v) =
      crossingVisitPoint q v := rfl

theorem crossingVisitEdge_flip_ne (q : Fin n → PlanarPoint K)
    (v : CrossingVisit q) : crossingVisitEdge q (crossingVisitFlip q v) ≠
      crossingVisitEdge q v := by
  rcases v with ⟨c, b⟩
  cases b
  · exact Ne.symm (crossing_edges_ne q c)
  · exact crossing_edges_ne q c

/-- Every visit is strictly inside its chosen original edge at the actual point. -/
theorem crossingVisitParameter_spec (q : Fin n → PlanarPoint K)
    (v : CrossingVisit q) :
    0 < crossingVisitParameter q v ∧ crossingVisitParameter q v < 1 ∧
      crossingVisitPoint q v = affinePoint (q (crossingVisitEdge q v))
        (q (cyclicSuccessor (crossingVisitEdge q v))) (crossingVisitParameter q v) := by
  rcases v with ⟨c, b⟩
  cases b
  · exact crossingParameterLeft_spec q c
  · exact crossingParameterRight_spec q c

theorem crossingVisitPoint_mem (q : Fin n → PlanarPoint K)
    (v : CrossingVisit q) : edgeInterior q (crossingVisitEdge q v)
      (crossingVisitPoint q v) :=
  ⟨crossingVisitParameter q v, crossingVisitParameter_spec q v⟩

/-- G2 suffices: equal affine keys give equal crossing points, and the
crossing's distinct edge labels then determine the Boolean visit label. -/
theorem crossingVisitKey_injective (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) : Function.Injective (crossingVisitKey q) := by
  intro v w h
  have he : crossingVisitEdge q v = crossingVisitEdge q w := congrArg Prod.fst h
  have ht : crossingVisitParameter q v = crossingVisitParameter q w := congrArg Prod.snd h
  have hp : crossingVisitPoint q v = crossingVisitPoint q w := by
    rw [(crossingVisitParameter_spec q v).2.2,
      (crossingVisitParameter_spec q w).2.2, he, ht]
  have hc : v.1 = w.1 := crossingPoint_injective q hq hp
  rcases v with ⟨c, b⟩
  rcases w with ⟨d, a⟩
  dsimp at hc
  subst d
  cases b <;> cases a
  · rfl
  · exact False.elim (crossing_edges_ne q c he)
  · exact False.elim (crossing_edges_ne q c he.symm)
  · rfl

/-- Original vertex anchors plus all actual crossing visits. -/
def PolygonEvent (q : Fin n → PlanarPoint K) := Fin n ⊕ CrossingVisit q

noncomputable instance polygonEventFintype (q : Fin n → PlanarPoint K) :
    Fintype (PolygonEvent q) := by
  unfold PolygonEvent
  infer_instance

/-- An anchor is the start of its outgoing original edge. -/
def polygonEventEdge (q : Fin n → PlanarPoint K) : PolygonEvent q → Fin n
  | .inl e => e
  | .inr v => crossingVisitEdge q v

/-- An anchor has parameter zero, and a crossing keeps its interior parameter. -/
noncomputable def polygonEventParameter (q : Fin n → PlanarPoint K) : PolygonEvent q → K
  | .inl _ => 0
  | .inr v => crossingVisitParameter q v

/-- Actual position of an original vertex anchor or a crossing visit. -/
noncomputable def polygonEventPoint (q : Fin n → PlanarPoint K) :
    PolygonEvent q → PlanarPoint K
  | .inl e => q e
  | .inr v => crossingVisitPoint q v

/-- A key is a traversal location on an original directed edge. -/
noncomputable def polygonEventKey (q : Fin n → PlanarPoint K)
    (x : PolygonEvent q) : Fin n × K :=
  (polygonEventEdge q x, polygonEventParameter q x)

theorem polygonEventKey_anchor (q : Fin n → PlanarPoint K) (e : Fin n) :
    polygonEventKey q (.inl e) = (e, 0) := rfl

theorem polygonEventKey_visit (q : Fin n → PlanarPoint K) (v : CrossingVisit q) :
    polygonEventKey q (.inr v) = crossingVisitKey q v := rfl

/-- Every event is placed by actual affine interpolation on its outgoing edge. -/
theorem polygonEventPoint_eq_affine (q : Fin n → PlanarPoint K) (x : PolygonEvent q) :
    polygonEventPoint q x = affinePoint (q (polygonEventEdge q x))
      (q (cyclicSuccessor (polygonEventEdge q x))) (polygonEventParameter q x) := by
  cases x with
  | inl e => exact (affinePoint_zero _ _).symm
  | inr v => exact (crossingVisitParameter_spec q v).2.2

/-- Event parameters lie in the half-open original-edge interval [0,1). -/
theorem polygonEventParameter_bounds [IsStrictOrderedRing K] (q : Fin n → PlanarPoint K)
    (x : PolygonEvent q) :
    0 ≤ polygonEventParameter q x ∧ polygonEventParameter q x < 1 := by
  cases x with
  | inl e =>
      change 0 ≤ (0 : K) ∧ (0 : K) < 1
      exact ⟨le_refl _, zero_lt_one⟩
  | inr v =>
      exact ⟨le_of_lt (crossingVisitParameter_spec q v).1,
        (crossingVisitParameter_spec q v).2.1⟩

/-- Distinct events cannot share their traversal key. Positions alone are not
injective: the two visits to one crossing deliberately share a plane point. -/
theorem polygonEventKey_injective (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) : Function.Injective (polygonEventKey q) := by
  intro x y h
  cases x with
  | inl e =>
      cases y with
      | inl f => exact congrArg Sum.inl (congrArg Prod.fst h)
      | inr v =>
          have ht : (0 : K) = crossingVisitParameter q v := congrArg Prod.snd h
          exact False.elim ((ne_of_gt (crossingVisitParameter_spec q v).1) ht.symm)
  | inr v =>
      cases y with
      | inl e =>
          have ht : crossingVisitParameter q v = (0 : K) := congrArg Prod.snd h
          exact False.elim ((ne_of_gt (crossingVisitParameter_spec q v).1) ht)
      | inr w => exact congrArg Sum.inr (crossingVisitKey_injective q hq h)

/-- All original anchors survive, including the case of no crossings. -/
theorem polygonEvent_card (q : Fin n → PlanarPoint K) :
    Fintype.card (PolygonEvent q) = n + 2 * Fintype.card (PolygonCrossing q) := by
  simp [PolygonEvent, CrossingVisit, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm]

theorem polygonEvent_card_ge_three (q : Fin n → PlanarPoint K) (hn : 3 ≤ n) :
    3 ≤ Fintype.card (PolygonEvent q) := by
  rw [polygonEvent_card]
  omega

theorem polygonEvent_nonempty (q : Fin n → PlanarPoint K) (hn : 3 ≤ n) :
    Nonempty (PolygonEvent q) :=
  ⟨.inl ⟨0, by omega⟩⟩

/-- With no crossings, every event is an original anchor. -/
theorem polygonEvent_eq_anchor_of_no_crossings (q : Fin n → PlanarPoint K)
    [IsEmpty (PolygonCrossing q)] (x : PolygonEvent q) :
    ∃ e : Fin n, x = Sum.inl e := by
  cases x with
  | inl e => exact ⟨e, rfl⟩
  | inr v => exact isEmptyElim v.1

/-- Lexicographic order of actual original-edge/parameter keys, pulled back
along the injective event key. Only G2 is needed for injectivity. -/
noncomputable def polygonEventOrder (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) : LinearOrder (PolygonEvent q) :=
  LinearOrder.lift' (fun x => toLex (polygonEventKey q x))
    (fun _ _ h => polygonEventKey_injective q hq (congrArg ofLex h))

/-- The order is exactly the given polygon traversal: increasing original
edge labels, and increasing actual affine parameters within each edge. -/
theorem polygonEvent_lt_iff (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x y : PolygonEvent q) :
    (letI := polygonEventOrder q hq; x < y) ↔
      polygonEventEdge q x < polygonEventEdge q y ∨
        polygonEventEdge q x = polygonEventEdge q y ∧
          polygonEventParameter q x < polygonEventParameter q y := by
  change toLex (polygonEventKey q x) < toLex (polygonEventKey q y) ↔ _
  exact Prod.Lex.toLex_lt_toLex

/-- On one original edge, traversal comparison is precisely affine-parameter
comparison; crossing-label order has no part in it. -/
theorem polygonEvent_sameEdge_lt_iff (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x y : PolygonEvent q)
    (he : polygonEventEdge q x = polygonEventEdge q y) :
    (letI := polygonEventOrder q hq; x < y) ↔
      polygonEventParameter q x < polygonEventParameter q y := by
  rw [polygonEvent_lt_iff q hq x y, he]
  simp

/-- Traversal of original anchors follows the polygon's original label order. -/
theorem polygonEvent_anchor_lt_iff (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (e f : Fin n) :
    (letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq;
      (Sum.inl e : PolygonEvent q) < Sum.inl f) ↔ e < f := by
  rw [polygonEvent_lt_iff q hq]
  simp [polygonEventEdge, polygonEventParameter]

/-- The start anchor precedes every crossing visit on its original edge. -/
theorem polygonEvent_anchor_lt_visit (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (v : CrossingVisit q) :
    letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
    (Sum.inl (crossingVisitEdge q v) : PolygonEvent q) < Sum.inr v := by
  apply (polygonEvent_lt_iff q hq _ _).2
  exact Or.inr ⟨rfl, (crossingVisitParameter_spec q v).1⟩

/-- With no crossings, the anchor inclusion is an equivalence onto all events. -/
def polygonEventNoCrossingsEquiv (q : Fin n → PlanarPoint K)
    [IsEmpty (PolygonCrossing q)] : Fin n ≃ PolygonEvent q where
  toFun := Sum.inl
  invFun := fun x => match x with
    | .inl e => e
    | .inr v => isEmptyElim v.1
  left_inv := fun _ => rfl
  right_inv := by
    intro x
    cases x with
    | inl e => rfl
    | inr v => exact isEmptyElim v.1

/-- In the crossing-free case the event count is exactly the original size. -/
theorem polygonEvent_card_of_no_crossings (q : Fin n → PlanarPoint K)
    [IsEmpty (PolygonCrossing q)] : Fintype.card (PolygonEvent q) = n := by
  rw [← Fintype.card_congr (polygonEventNoCrossingsEquiv q), Fintype.card_fin]

end DirectGLSSW
