import DaughterPairingLift

set_option autoImplicit false
namespace DirectGLSSW.DaughterSecondReturn
open DaughterFirstReturn DaughterParentCrossing DaughterLocalCrossing
  DaughterEventLift DaughterKeptEvents DaughterKeptSuccessor DaughterPairingLift
  DaughterG2Inheritance PolygonNonalternation PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

/-- Every newly selected visit is genuinely among the daughter's kept events. -/
theorem liftedSupport_visit_kept
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (v : CrossingVisit P) (hv : v.1 ∈ liftedSupport P hP S hS root hroot T) :
    keptEvent P hP S root (Sum.inr v) := by
  obtain ⟨d,_,hd⟩ := Finset.mem_map.mp hv
  have hd' : parentCrossing P hP S hS root hroot d = v.1 := hd
  have h (b : Bool) : componentOf (smoothingDartPermutation P hP.g2 S) (Sum.inr (v.1,b)) =
      componentOf (smoothingDartPermutation P hP.g2 S) root := by
    rw [← hd']
    exact parentCrossing_visit_component P hP S hS root hroot d b
  exact ⟨h v.2,Or.inr (h (!v.2))⟩

theorem liftedPairing_fixes_omitted
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (y : PolygonEvent P) (hy : ¬ keptEvent P hP S root y) :
    smoothingPairing P (liftedSupport P hP S hS root hroot T) y = y := by
  cases y with
  | inl i => rfl
  | inr v =>
    apply (smoothingPairing_visit_fixed_iff P _ v).mpr
    exact fun hv => hy (liftedSupport_visit_kept P hP S hS root hroot T v hv)

/-- Before the next kept event no newly selected pairing changes the orbit. -/
theorem unionDart_pow_before_return
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent P) (d : ℕ)
    (hno : ∀ k : ℕ, 0 < k → k < d → ¬ keptEvent P hP S root
      ((smoothingDartPermutation P hP.g2 S ^ k) x))
    (k : ℕ) (hk : k < d) :
    (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T) ^ k) x =
      (smoothingDartPermutation P hP.g2 S ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hi := ih (by omega)
    rw [pow_succ',Equiv.Perm.mul_apply,hi]
    rw [smoothingDartPermutation_union P hP.g2 S _ (liftedSupport_disjoint P hP S hS root hroot T),
      Equiv.Perm.mul_apply]
    have he : smoothingDartPermutation P hP.g2 S ((smoothingDartPermutation P hP.g2 S ^ k) x) =
        (smoothingDartPermutation P hP.g2 S ^ (k+1)) x := by simp only [pow_succ',Equiv.Perm.mul_apply]
    rw [he]
    exact liftedPairing_fixes_omitted P hP S hS root hroot T _ (hno (k+1) (by omega) hk)

/-- The actual second-stage daughter successor is the first return of the actual
union-support dart successor to the kept old-component events. -/
theorem secondStage_firstReturn
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    ∃ d : ℕ, 0 < d ∧
      (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T) ^ d)
          (eventLift P hP S hS root hroot x) =
        eventLift P hP S hS root hroot
          (smoothingDartPermutation (daughterVertex P hP.g2 S root)
            (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T x) ∧
      ∀ k : ℕ, 0 < k → k < d → ¬ keptEvent P hP S root
        ((smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T) ^ k)
          (eventLift P hP S hS root hroot x)) := by
  obtain ⟨d,hd,hreach,hno⟩ := eventLift_successor_firstReturn P hP S hS root hroot x
  let p := smoothingDartPermutation P hP.g2 S
  let p' := smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T)
  let a := eventLift P hP S hS root hroot x
  let τ := smoothingPairing P (liftedSupport P hP S hS root hroot T)
  have hprefix := unionDart_pow_before_return P hP S hS root hroot T a d hno
  have hlast : d-1+1=d := Nat.sub_add_cancel hd
  have hfinish : (p' ^ d) a = τ ((p ^ d) a) := by
    calc
      (p' ^ d) a = p' ((p' ^ (d-1)) a) := by
        conv_lhs => rw [← hlast]
        rw [pow_succ',Equiv.Perm.mul_apply]
      _ = τ (p ((p ^ (d-1)) a)) := by
        rw [hprefix (d-1) (by omega)]
        exact congrArg (fun g : Equiv.Perm (PolygonEvent P) => g ((p ^ (d-1)) a))
          (smoothingDartPermutation_union P hP.g2 S _
            (liftedSupport_disjoint P hP S hS root hroot T))
      _ = τ ((p ^ d) a) := by
        conv_rhs => rw [← hlast,pow_succ',Equiv.Perm.mul_apply]
  refine ⟨d,hd,?_,?_⟩
  · change (p' ^ d) a = _
    rw [hfinish]
    change τ ((smoothingDartPermutation P hP.g2 S ^ d) (eventLift P hP S hS root hroot x)) = _
    rw [hreach]
    exact (eventLift_pairing P hP S hS root hroot T _).symm
  · intro k hk0 hkd
    rw [hprefix k hkd]
    exact hno k hk0 hkd





end
end DirectGLSSW.DaughterSecondReturn
