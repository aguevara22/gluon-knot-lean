import SM.Farout

namespace SM

noncomputable section
universe u v
variable {n : ℕ} [NeZero n] {R : Type u} {S : Type v}
  [CommRing R] [CommRing S] [Invertible (2 : R)] [Invertible (2 : S)]

/-- The designated inverses of two are respected by every ring map,
including maps into polynomial rings. No cancellation assumption is needed. -/
theorem ringHom_map_half (f : R →+* S) : f (⅟ (2 : R)) = ⅟ (2 : S) := by
  have hprod : f (⅟ (2 : R)) * (2 : S) = 1 := by
    calc
      _ = f (⅟ (2 : R) * 2) := by rw [map_mul, map_ofNat]
      _ = 1 := by rw [invOf_mul_self, map_one]
  calc
    f (⅟ (2 : R)) = f (⅟ (2 : R)) * ((2 : S) * ⅟ (2 : S)) := by
      rw [mul_invOf_self, mul_one]
    _ = (f (⅟ (2 : R)) * (2 : S)) * ⅟ (2 : S) := by rw [mul_assoc]
    _ = ⅟ (2 : S) := by rw [hprod, one_mul]

theorem map_nearFarWeight (f : R →+* S) (D H : TripleArray n R)
    {I : BoundaryInterval n} (π : IntervalComposition I) :
    f (π.nearFarWeight D H) = π.nearFarWeight (fun t => f (D t)) (fun t => f (H t)) := by
  simp only [IntervalComposition.nearFarWeight, map_prod, map_mul, map_sub,
    ringHom_map_half]

theorem map_boundaryUnitArray (f : R →+* S) (I : BoundaryInterval n) :
    f (boundaryUnitArray (R := R) I) = boundaryUnitArray (R := S) I := by
  simp only [boundaryUnitArray, apply_ite, map_one, map_zero]

/-- Naturality preserves the complete sum, including its unary term and
all actual child intervals. -/
theorem map_nearFarTransform (f : R →+* S) (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    f (nearFarTransform D H X I) = nearFarTransform (fun t => f (D t))
      (fun t => f (H t)) (fun J => f (X J)) I := by
  simp only [nearFarTransform, map_sum, map_mul, map_prod, map_nearFarWeight]

theorem map_farTransform (f : R →+* S) (H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    f (farTransform H X I) = farTransform (fun t => f (H t)) (fun J => f (X J)) I := by
  simpa only [farTransform, Pi.zero_apply, map_zero] using map_nearFarTransform f 0 H X I

/-- The existing well-founded inverse recursion commutes with every ring
map, after mapping its actual near/far weights. -/
theorem map_nearFarInverse (f : R →+* S) (D H : TripleArray n R)
    (Y : IntervalArray n R) (I : BoundaryInterval n) :
    f (nearFarInverse D H Y I) = nearFarInverse (fun t => f (D t))
      (fun t => f (H t)) (fun J => f (Y J)) I := by
  simpa only [nearFarInverse, map_nearFarWeight] using
    map_triangularInverse f (fun _ π => π.nearFarWeight D H) Y I

theorem map_farOnlyCoordinates (f : R →+* S) (H : TripleArray n R)
    (I : BoundaryInterval n) :
    f (farOnlyCoordinates H I) = farOnlyCoordinates (fun t => f (H t)) I := by
  simpa only [farOnlyCoordinates, Pi.zero_apply, map_zero, map_boundaryUnitArray] using
    map_nearFarInverse f 0 H boundaryUnitArray I

theorem map_farOnlyOutput (f : R →+* S) (H : TripleArray n R)
    (I : BoundaryInterval n) :
    f (farOnlyOutput H I) = farOnlyOutput (fun t => f (H t)) I := by
  simpa only [farOnlyOutput, Pi.neg_apply, map_neg, map_farOnlyCoordinates] using
    map_farTransform f (-H) (farOnlyCoordinates H) I

end
end SM

#print axioms SM.ringHom_map_half
#print axioms SM.map_nearFarWeight
#print axioms SM.map_boundaryUnitArray
#print axioms SM.map_nearFarTransform
#print axioms SM.map_farTransform
#print axioms SM.map_nearFarInverse
#print axioms SM.map_farOnlyCoordinates
#print axioms SM.map_farOnlyOutput
