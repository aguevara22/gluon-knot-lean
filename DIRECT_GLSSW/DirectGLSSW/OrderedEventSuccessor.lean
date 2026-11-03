import DirectGLSSW.PolygonEvents
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Ordered successor on the actual event circle

Source: frozen note lines 131–139; implementation design §§2–3.
Only the unsmoothed oriented parameter circle is constructed here.
Enumeration follows the injective actual edge/parameter keys. The two visits
of one crossing remain distinct, despite occupying the same plane point.
-/

namespace DirectGLSSW

/-- The existing modular successor as a permutation, with proved bijectivity. -/
noncomputable def cyclicSuccessorPerm (n : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective cyclicSuccessor cyclicSuccessor_bijective

@[simp] theorem cyclicSuccessorPerm_apply {n : ℕ} (x : Fin n) :
    cyclicSuccessorPerm n x = cyclicSuccessor x := rfl

/-- Positive step k+1 is the already defined cyclic vertex index k. -/
theorem cyclicSuccessorPerm_pow_succ {n : ℕ} (x : Fin n) (k : ℕ) :
    (cyclicSuccessorPerm n ^ (k + 1)) x = cyclicVertexIndex x k := by
  induction k with
  | zero => simp [cyclicSuccessorPerm_apply, cyclicSuccessor]
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      apply Fin.ext
      change (((x.val + 1 + k) % n + 1 + 0) % n) =
        (x.val + 1 + (k + 1)) % n
      rw [Nat.add_zero, Nat.mod_add_mod, Nat.add_assoc]

/-- Exactly one visit to every label in steps 1 through n, including closure. -/
theorem cyclicSuccessorPerm_oneTraversal {n : ℕ} (x : Fin n) :
    Function.Bijective (fun k : Fin n => (cyclicSuccessorPerm n ^ (k.val + 1)) x) := by
  simp only [cyclicSuccessorPerm_pow_succ]
  exact cyclicVertexIndex_bijective x

/-- One complete traversal returns to the starting label. -/
theorem cyclicSuccessorPerm_pow_card {n : ℕ} (x : Fin n) :
    (cyclicSuccessorPerm n ^ n) x = x := by
  have hn : n - 1 + 1 = n := by have := x.isLt; omega
  simpa only [hn, cyclicVertexIndex_last] using cyclicSuccessorPerm_pow_succ x (n - 1)

section FiniteLinearOrder

variable (α : Type*) [LinearOrder α] [Fintype α]

/-- The unique increasing enumeration of a finite linear order. -/
noncomputable def increasingEnumeration : Fin (Fintype.card α) ≃o α :=
  Fintype.orderIsoFinOfCardEq α rfl

/-- Move to the next element in increasing order, wrapping at the last one. -/
noncomputable def orderedCyclicSuccessor : Equiv.Perm α :=
  (increasingEnumeration α).toEquiv.symm.trans
    ((cyclicSuccessorPerm (Fintype.card α)).trans (increasingEnumeration α).toEquiv)

/-- The definition is conjugation of the original finite modular successor. -/
theorem orderedCyclicSuccessor_apply (x : α) :
    orderedCyclicSuccessor α x = increasingEnumeration α
      (cyclicSuccessor ((increasingEnumeration α).symm x)) := rfl

/-- Conjugation identifies every finite iterate, not merely individual steps. -/
theorem orderedCyclicSuccessor_pow_apply (x : α) (k : ℕ) :
    (orderedCyclicSuccessor α ^ k) x = increasingEnumeration α
      ((cyclicSuccessorPerm (Fintype.card α) ^ k) ((increasingEnumeration α).symm x)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, orderedCyclicSuccessor_apply]
      simp only [OrderIso.symm_apply_apply]
      rw [pow_succ', Equiv.Perm.mul_apply, cyclicSuccessorPerm_apply]

/-- Every event is reached exactly once in steps 1 through the cardinality. -/
theorem orderedCyclicSuccessor_oneTraversal (x : α) :
    Function.Bijective (fun k : Fin (Fintype.card α) =>
      (orderedCyclicSuccessor α ^ (k.val + 1)) x) := by
  simp only [orderedCyclicSuccessor_pow_apply]
  exact (increasingEnumeration α).bijective.comp
    (cyclicSuccessorPerm_oneTraversal ((increasingEnumeration α).symm x))

/-- The standard zero-based traversal also visits each element exactly once. -/
theorem orderedCyclicSuccessor_zeroBasedTraversal (x : α) :
    Function.Bijective (fun k : Fin (Fintype.card α) =>
      (orderedCyclicSuccessor α ^ k.val) x) := by
  constructor
  · intro a b hab
    apply (orderedCyclicSuccessor_oneTraversal α x).1
    simp only [pow_succ', Equiv.Perm.mul_apply, hab]
  · intro y
    obtain ⟨k, hk⟩ := (orderedCyclicSuccessor_oneTraversal α x).2
      (orderedCyclicSuccessor α y)
    refine ⟨k, (orderedCyclicSuccessor α).injective ?_⟩
    simpa only [pow_succ', Equiv.Perm.mul_apply] using hk

/-- Every two elements are on the same permutation cycle; this follows from
the proved finite traversal, not from an assumed component-count formula. -/
theorem orderedCyclicSuccessor_isCycleOn :
    (orderedCyclicSuccessor α).IsCycleOn Set.univ := by
  refine ⟨(orderedCyclicSuccessor α).bijective.bijOn_univ, ?_⟩
  intro x _ y _
  obtain ⟨k, hk⟩ := (orderedCyclicSuccessor_zeroBasedTraversal α x).2 y
  exact ⟨(k.val : ℤ), by simpa only [zpow_natCast] using hk⟩

/-- The full traversal closes at its starting element. -/
theorem orderedCyclicSuccessor_pow_card (x : α) :
    (orderedCyclicSuccessor α ^ Fintype.card α) x = x := by
  rw [orderedCyclicSuccessor_pow_apply, cyclicSuccessorPerm_pow_card]
  exact (increasingEnumeration α).apply_symm_apply x

/-- If there are at least two elements, none is its own immediate successor. -/
theorem orderedCyclicSuccessor_ne_self (hα : 2 ≤ Fintype.card α) (x : α) :
    orderedCyclicSuccessor α x ≠ x := by
  intro h
  apply cyclicSuccessor_ne_self hα ((increasingEnumeration α).symm x)
  apply (increasingEnumeration α).injective
  simpa only [orderedCyclicSuccessor_apply, OrderIso.apply_symm_apply] using h

/-- A successor is the least strictly larger element, or wraps from maximum
 to minimum. This also covers a singleton finite order. -/
theorem orderedCyclicSuccessor_order_spec (x : α) :
    (x < orderedCyclicSuccessor α x ∧
      ∀ z : α, x < z → orderedCyclicSuccessor α x ≤ z) ∨
    ((∀ z : α, z ≤ x) ∧ ∀ z : α, orderedCyclicSuccessor α x ≤ z) := by
  let e := increasingEnumeration α
  let i := e.symm x
  have hm : 0 < Fintype.card α := by have := i.isLt; omega
  have hs : (cyclicSuccessor i).val =
      if i.val + 1 < Fintype.card α then i.val + 1 else i.val + 1 - Fintype.card α := by
    simpa only [cyclicSuccessor, Nat.add_zero] using cyclicVertexIndex_val i hm
  by_cases hi : i.val + 1 < Fintype.card α
  · left
    constructor
    · rw [orderedCyclicSuccessor_apply]
      change x < e (cyclicSuccessor i)
      rw [← e.apply_symm_apply x]
      apply e.strictMono
      change i.val < (cyclicSuccessor i).val
      rw [hs, if_pos hi]
      omega
    · intro z hz
      rw [orderedCyclicSuccessor_apply]
      change e (cyclicSuccessor i) ≤ z
      rw [← e.apply_symm_apply z]
      apply e.monotone
      change (cyclicSuccessor i).val ≤ (e.symm z).val
      have hix : i < e.symm z := e.symm.strictMono hz
      rw [hs, if_pos hi]
      exact hix
  · right
    constructor
    · intro z
      have hz := (e.symm z).isLt
      have hij : e.symm z ≤ i := by change (e.symm z).val ≤ i.val; omega
      change e.symm z ≤ e.symm x at hij
      simpa only [OrderIso.apply_symm_apply] using e.monotone hij
    · intro z
      rw [orderedCyclicSuccessor_apply]
      change e (cyclicSuccessor i) ≤ z
      rw [← e.apply_symm_apply z]
      apply e.monotone
      change (cyclicSuccessor i).val ≤ (e.symm z).val
      rw [hs, if_neg hi]
      have := i.isLt
      omega

/-- The least-greater / maximum-to-minimum rule uniquely determines successor. -/
theorem orderedCyclicSuccessor_eq_of_order_spec (x y : α)
    (hy : (x < y ∧ ∀ z : α, x < z → y ≤ z) ∨
      ((∀ z : α, z ≤ x) ∧ ∀ z : α, y ≤ z)) :
    orderedCyclicSuccessor α x = y := by
  rcases orderedCyclicSuccessor_order_spec α x with ⟨hs, hmin⟩ | ⟨hmax, hmin⟩
  · rcases hy with ⟨hy, hymin⟩ | ⟨hymax, _⟩
    · exact le_antisymm (hmin y hy) (hymin _ hs)
    · exact False.elim ((not_lt_of_ge (hymax _)) hs)
  · rcases hy with ⟨hy, _⟩ | ⟨_, hymin⟩
    · exact False.elim ((not_lt_of_ge (hmax y)) hy)
    · exact le_antisymm (hmin y) (hymin _)

/-- Increasing relabellings preserve cyclic successor, including wrap. -/
theorem orderedCyclicSuccessor_naturality
    {β : Type*} [LinearOrder β] [Fintype β] (e : α ≃o β) (x : α) :
    orderedCyclicSuccessor β (e x) = e (orderedCyclicSuccessor α x) := by
  apply orderedCyclicSuccessor_eq_of_order_spec
  rcases orderedCyclicSuccessor_order_spec α x with ⟨hs, hmin⟩ | ⟨hmax, hmin⟩
  · left
    refine ⟨e.strictMono hs, ?_⟩
    intro z hz
    have hxz : x < e.symm z := by
      simpa only [OrderIso.symm_apply_apply] using e.symm.strictMono hz
    simpa only [OrderIso.apply_symm_apply] using e.monotone (hmin (e.symm z) hxz)
  · right
    constructor
    · intro z
      simpa only [OrderIso.apply_symm_apply] using e.monotone (hmax (e.symm z))
    · intro z
      simpa only [OrderIso.apply_symm_apply] using e.monotone (hmin (e.symm z))

end FiniteLinearOrder

/-- On the original finite labels, increasing-order successor is exactly the
existing polygon successor, not merely a conjugate arbitrary n-cycle. -/
theorem orderedCyclicSuccessor_fin {n : ℕ} (x : Fin n) :
    orderedCyclicSuccessor (Fin n) x = cyclicSuccessor x := by
  apply orderedCyclicSuccessor_eq_of_order_spec
  have hn : 0 < n := by have := x.isLt; omega
  have hs : (cyclicSuccessor x).val =
      if x.val + 1 < n then x.val + 1 else x.val + 1 - n := by
    simpa only [cyclicSuccessor, Nat.add_zero] using cyclicVertexIndex_val x hn
  by_cases hx : x.val + 1 < n
  · left
    constructor
    · change x.val < (cyclicSuccessor x).val
      rw [hs, if_pos hx]
      omega
    · intro z hz
      change (cyclicSuccessor x).val ≤ z.val
      rw [hs, if_pos hx]
      exact hz
  · right
    constructor
    · intro z
      change z.val ≤ x.val
      have := z.isLt
      omega
    · intro z
      change (cyclicSuccessor x).val ≤ z.val
      rw [hs, if_neg hx]
      have := x.isLt
      omega

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- Increasing enumeration in actual outgoing-edge / affine-parameter order. -/
noncomputable def polygonEventEnumeration (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) :
    letI := polygonEventOrder q hq
    Fin (Fintype.card (PolygonEvent q)) ≃o PolygonEvent q := by
  letI := polygonEventOrder q hq
  exact increasingEnumeration (PolygonEvent q)

/-- The original unsmoothed event successor in the oriented traversal order. -/
noncomputable def polygonEventSuccessor (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) : Equiv.Perm (PolygonEvent q) := by
  letI := polygonEventOrder q hq
  exact orderedCyclicSuccessor (PolygonEvent q)

/-- Explicit conjugation by the increasing event enumeration. -/
theorem polygonEventSuccessor_apply (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x : PolygonEvent q) :
    letI := polygonEventOrder q hq
    polygonEventSuccessor q hq x = polygonEventEnumeration q hq
      (cyclicSuccessor ((polygonEventEnumeration q hq).symm x)) := by
  letI := polygonEventOrder q hq
  rfl

/-- Every actual event occurs exactly once before the traversal repeats. -/
theorem polygonEventSuccessor_oneTraversal (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x : PolygonEvent q) :
    Function.Bijective (fun k : Fin (Fintype.card (PolygonEvent q)) =>
      (polygonEventSuccessor q hq ^ (k.val + 1)) x) := by
  letI := polygonEventOrder q hq
  exact orderedCyclicSuccessor_oneTraversal (PolygonEvent q) x

/-- In the standard zero-based indexing, the first card(E) steps enumerate E. -/
theorem polygonEventSuccessor_zeroBasedTraversal (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x : PolygonEvent q) :
    Function.Bijective (fun k : Fin (Fintype.card (PolygonEvent q)) =>
      (polygonEventSuccessor q hq ^ k.val) x) := by
  letI := polygonEventOrder q hq
  exact orderedCyclicSuccessor_zeroBasedTraversal (PolygonEvent q) x

/-- The unsmoothed actual event permutation consists of one cycle on all events. -/
theorem polygonEventSuccessor_isCycleOn (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) :
    (polygonEventSuccessor q hq).IsCycleOn Set.univ := by
  letI := polygonEventOrder q hq
  exact orderedCyclicSuccessor_isCycleOn (PolygonEvent q)

/-- One complete original traversal returns to the same event. -/
theorem polygonEventSuccessor_pow_card (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x : PolygonEvent q) :
    (polygonEventSuccessor q hq ^ Fintype.card (PolygonEvent q)) x = x := by
  letI := polygonEventOrder q hq
  exact orderedCyclicSuccessor_pow_card (PolygonEvent q) x

/-- At geometric sizes n ≥ 3, the original event successor has no fixed event. -/
theorem polygonEventSuccessor_ne_self (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n) (x : PolygonEvent q) :
    polygonEventSuccessor q hq x ≠ x := by
  letI := polygonEventOrder q hq
  exact orderedCyclicSuccessor_ne_self (PolygonEvent q)
    (by have := polygonEvent_card_ge_three q hn; omega) x

/-- The successor is next in actual edge/parameter order, with maximum/minimum wrap. -/
theorem polygonEventSuccessor_order_spec (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x : PolygonEvent q) :
    letI := polygonEventOrder q hq
    (x < polygonEventSuccessor q hq x ∧
      ∀ z : PolygonEvent q, x < z → polygonEventSuccessor q hq x ≤ z) ∨
    ((∀ z : PolygonEvent q, z ≤ x) ∧
      ∀ z : PolygonEvent q, polygonEventSuccessor q hq x ≤ z) := by
  letI := polygonEventOrder q hq
  exact orderedCyclicSuccessor_order_spec (PolygonEvent q) x

/-- Explicit key-order reading: the successor is the least larger actual key,
or it wraps from the greatest actual key to the least one. Weak comparison is
written as absence of a reversed strict key comparison. -/
theorem polygonEventSuccessor_key_spec (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x : PolygonEvent q) :
    let next := polygonEventSuccessor q hq x
    let before := fun a b : PolygonEvent q =>
      polygonEventEdge q a < polygonEventEdge q b ∨
        polygonEventEdge q a = polygonEventEdge q b ∧
          polygonEventParameter q a < polygonEventParameter q b
    (before x next ∧ ∀ z, before x z → ¬ before z next) ∨
      ((∀ z, ¬ before x z) ∧ ∀ z, ¬ before z next) := by
  letI := polygonEventOrder q hq
  change (_ ∧ ∀ z, _ → ¬ _) ∨ ((∀ z, ¬ _) ∧ ∀ z, ¬ _)
  simp only [← polygonEvent_lt_iff q hq, not_lt]
  exact polygonEventSuccessor_order_spec q hq x

/-- Without crossings the anchor equivalence preserves the actual traversal order. -/
noncomputable def polygonEventNoCrossingsOrderIso (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) [IsEmpty (PolygonCrossing q)] :
    letI := polygonEventOrder q hq
    Fin n ≃o PolygonEvent q := by
  letI := polygonEventOrder q hq
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  refine { toEquiv := polygonEventNoCrossingsEquiv q, map_rel_iff' := ?_ }
  intro a b
  change (Sum.inl a : PolygonEvent q) ≤ Sum.inl b ↔ a ≤ b
  rw [← not_lt, ← not_lt]
  exact not_congr (polygonEvent_anchor_lt_iff q hq b a)

/-- Crossing-free traversal is exactly the original polygon edge successor. -/
theorem polygonEventSuccessor_anchor_of_no_crossings (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) [IsEmpty (PolygonCrossing q)] (e : Fin n) :
    polygonEventSuccessor q hq (Sum.inl e) = Sum.inl (cyclicSuccessor e) := by
  letI := polygonEventOrder q hq
  have h := orderedCyclicSuccessor_naturality (Fin n)
    (polygonEventNoCrossingsOrderIso q hq) e
  rw [orderedCyclicSuccessor_fin] at h
  exact h

end DirectGLSSW
