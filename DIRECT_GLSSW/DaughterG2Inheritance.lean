import DaughterOpenEdgeContainment
import DirectGLSSW.ShortEdgeCyclicRelabel
import DirectGLSSW.DaughterRootRotation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DaughterG2Inheritance
open DirectGLSSW DaughterFirstReturn DaughterRootRotation PolygonNonalternation
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/- The following two private shift proofs and the List.ofFn coordinate argument
   are adapted explicitly from canonical DirectGLSSW/DaughterRootAmplitude.lean.
   The result here uses only G2, over an ordered field, not daughter G1. -/
private theorem cyclicShift_val {n k : ℕ} (hk : k < n)
    (i : Fin n) :
    ((cyclicSuccessorPerm n ^ k) i).val = (i.val + k) % n := by
  cases k with
  | zero =>
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ t =>
      have ht : t < n := by omega
      rw [cyclicSuccessorPerm_pow_succ]
      change (i.val + 1 + t) % n = (i.val + (t + 1)) % n
      congr 1
      omega

private theorem cyclicShift_commutes {n k : ℕ} :
    ∀ e : Fin n,
      (cyclicSuccessorPerm n ^ k) (cyclicSuccessor e) =
        cyclicSuccessor ((cyclicSuccessorPerm n ^ k) e) := by
  intro e
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      simp only [Equiv.Perm.mul_apply]
      exact congrArg cyclicSuccessor (ih e)

/-- G2 alone is invariant under actual finite cyclic point-word rotation. -/
theorem cyclicNoTripleIntersections_ofFn_isRotated
    {m n : ℕ} {q : Fin n → PlanarPoint K} {r : Fin m → PlanarPoint K}
    (hnpos : 0 < n) (hrot : List.ofFn q ~r List.ofFn r)
    (hq : cyclicNoTripleIntersections q) :
    cyclicNoTripleIntersections r := by
  classical
  obtain ⟨k, hk⟩ := hrot
  have hlen : n = m := by
    have h := congrArg List.length hk
    simpa using h
  subst m
  let k' := k % n
  have hk' : (List.ofFn q).rotate k' = List.ofFn r := by
    have hmod := (List.rotate_mod (List.ofFn q) k).trans hk
    simpa [k', List.length_ofFn] using hmod
  let σ : Equiv.Perm (Fin n) := cyclicSuccessorPerm n ^ k'
  have hσval (i : Fin n) :
      (σ i).val = (i.val + k') % n := by
    exact cyclicShift_val (Nat.mod_lt _ hnpos) i
  have hrel : r = q ∘ σ := by
    funext i
    let l₁ : {l : List (PlanarPoint K) // l.length = n} :=
      ⟨(List.ofFn q).rotate k', by simp⟩
    let l₂ : {l : List (PlanarPoint K) // l.length = n} :=
      ⟨List.ofFn r, by simp⟩
    have hsub : l₁ = l₂ := Subtype.ext hk'
    have hget := congrArg
      (fun l : {l : List (PlanarPoint K) // l.length = n} =>
        l.val[i.val]'(by rw [l.property]; exact i.isLt)) hsub
    have hrotget := List.getElem_rotate (List.ofFn q) k' i.val (by
      rw [List.length_rotate, List.length_ofFn]
      exact i.isLt)
    change ((List.ofFn q).rotate k')[i.val]'_ = (List.ofFn r)[i.val]'_ at hget
    rw [hrotget] at hget
    have hpoint :
        (⟨(i.val + k') % n, Nat.mod_lt _ hnpos⟩ : Fin n) = σ i := by
      apply Fin.ext
      exact (hσval i).symm
    simpa [List.getElem_ofFn, hpoint] using hget.symm
  exact hrel ▸ cyclicNoTripleIntersections_relabel q σ
    (cyclicShift_commutes) hq


/-- G2 is inherited for every event root, with no daughter G1 premise. -/
theorem daughter_cyclicNoTripleIntersections {n : ℕ}
    (q : Fin n → PlanarPoint K) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (hn : 3 ≤ n)
    (hNA : polygonNonalternating q hG2 S) (root : PolygonEvent q) :
    cyclicNoTripleIntersections (daughterVertex q hG2 S root) := by
  classical
  obtain ⟨r, hcycle, hr⟩ := everyDartOrbit_hasCorner q hG2 S hn root
  have hnonempty : Nonempty (CornerCoord q hG2 S r) := by
    refine ⟨⟨⟨0, orbitCard_pos q hG2 S r⟩, ?_⟩⟩
    simpa [orbitEventAt] using hr
  have hpos : 0 < Fintype.card (CornerCoord q hG2 S r) :=
    Fintype.card_pos_iff.mpr hnonempty
  apply cyclicNoTripleIntersections_ofFn_isRotated hpos
    (daughterPointList_isRotated_of_sameCycle q hG2 S r root hcycle.symm)
  exact daughter_cyclicNoTripleIntersections_retained q hG2 S hn hNA r hr

/-- Original G1–G2 supplies all premises; daughter genericity is not assumed. -/
theorem daughter_g2_of_cyclicGeneric {n : ℕ}
    (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (hNA : polygonNonalternating q hq.g2 S) (root : PolygonEvent q) :
    cyclicNoTripleIntersections (daughterVertex q hq.g2 S root) :=
  daughter_cyclicNoTripleIntersections q hq.g2 S hq.size_ge_three hNA root






end DirectGLSSW.DaughterG2Inheritance
