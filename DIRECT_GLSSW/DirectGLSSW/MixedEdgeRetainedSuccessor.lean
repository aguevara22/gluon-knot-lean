import DirectGLSSW.MixedEdgeFirstReturn

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeRetainedSuccessor

open Equiv DaughterFirstReturn FiniteFirstReturn MixedEdgeFirstReturn

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

noncomputable def originalCornerNext
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q)
    (hx : retainedCorner q S x) : PolygonEvent q := by
  classical
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
  let E := polygonEventEnumeration q hq
  let P : Fin (Fintype.card (PolygonEvent q)) → Prop :=
    fun i => retainedCorner q S (E i)
  let i : {j : Fin (Fintype.card (PolygonEvent q)) // P j} :=
    ⟨E.symm x, by simpa [P] using hx⟩
  exact E (orderedCyclicSuccessor {j : Fin (Fintype.card (PolygonEvent q)) // P j} i).val

theorem originalCornerNext_firstReturn
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q)
    (hx : retainedCorner q S x) :
    ∃ d : ℕ, 0 < d ∧
      (polygonEventSuccessor q hq ^ d) x = originalCornerNext q hq S x hx ∧
      retainedCorner q S (originalCornerNext q hq S x hx) ∧
      ∀ k : ℕ, 0 < k → k < d →
        ¬ retainedCorner q S ((polygonEventSuccessor q hq ^ k) x) := by
  classical
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
  let E := polygonEventEnumeration q hq
  let P : Fin (Fintype.card (PolygonEvent q)) → Prop :=
    fun i => retainedCorner q S (E i)
  let i : {j : Fin (Fintype.card (PolygonEvent q)) // P j} :=
    ⟨E.symm x, by simpa [P] using hx⟩
  let next := orderedCyclicSuccessor {j : Fin (Fintype.card (PolygonEvent q)) // P j} i
  let d := forwardGap i.val next.val
  have hfr : 0 < d ∧ d ≤ Fintype.card (PolygonEvent q) ∧
      (cyclicSuccessorPerm (Fintype.card (PolygonEvent q)) ^ d) i.val = next.val ∧
      ∀ k : ℕ, 0 < k → k < d →
        ¬ P ((cyclicSuccessorPerm (Fintype.card (PolygonEvent q)) ^ k) i.val) := by
    simpa [next, d] using orderedSubtype_firstReturn P i
  rcases hfr with ⟨hd, _, hreach, hno⟩
  have hp (k : ℕ) : (polygonEventSuccessor q hq ^ k) x =
      E ((cyclicSuccessorPerm (Fintype.card (PolygonEvent q)) ^ k) i.val) := by
    exact orderedCyclicSuccessor_pow_apply (PolygonEvent q) x k
  have hnext : originalCornerNext q hq S x hx = E next.val := rfl
  refine ⟨d, hd, ?_, ?_, ?_⟩
  · rw [hp d, hreach, hnext]
  · rw [hnext]
    exact next.property
  · intro k hk hkd
    rw [hp k]
    exact hno k hk hkd


theorem cornerSuccessor_eq_pairing_originalCornerNext
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (c : CornerCoord q hq S root) :
    orbitEventAt q hq S root (cornerSuccessor q hq S root c).val =
      smoothingPairing q S
        (originalCornerNext q hq S (orbitEventAt q hq S root c.val) c.property) := by
  obtain ⟨d, hd, hreach, hret, hno⟩ := originalCornerNext_firstReturn q hq S
    (orbitEventAt q hq S root c.val) c.property
  have ht : retainedCorner q S
      ((polygonEventSuccessor q hq ^ d) (orbitEventAt q hq S root c.val)) := by
    rw [hreach]
    exact hret
  have h := cornerSuccessor_eq_pairing_of_original_firstReturn q hq S root c d hd ht hno
  rw [hreach] at h
  exact h






end DirectGLSSW.MixedEdgeRetainedSuccessor
