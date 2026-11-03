import CutArcSuppliedCarriers

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart CarrierNumeratorPath DaughterFirstReturn
open scoped BigOperators

theorem slotDen_eq {R : Type*} [CommRing R] (A B : (R × R) × R) :
    slotDen A B = planarDet A.1 B.1 := rfl

theorem slotNum_eq {R : Type*} [CommRing R] (A B : (R × R) × R) :
    slotNum A B = (B.2*A.1.1-A.2*B.1.1, B.2*A.1.2-A.2*B.1.2) := rfl

theorem clearedPoints_eq_formula {R : Type*} [CommRing R] {s : ℕ}
    (A B : Fin s → (R × R) × R) (i : Fin s) :
    clearedPoints A B i =
      ((∏ j ∈ Finset.univ.erase i, slotDen (A j) (B j)) * (slotNum (A i) (B i)).1,
       (∏ j ∈ Finset.univ.erase i, slotDen (A j) (B j)) * (slotNum (A i) (B i)).2) := rfl

theorem outerCycleNumerator_eq_formula {R : Type*} [CommRing R] {m n : ℕ}
    (L : Fin n → (R × R) × R) (f : Fin m → Fin n) (l : Fin 4 → Fin m) :
    outerCycleNumerator L f l = OriginalOuterProperness.outerNumerator (clearedPoints
      (fun i => L (f ((cyclicSuccessorPerm m)⁻¹ (l i)))) (fun i => L (f (l i)))) := rfl

theorem secantCycleNumerator_eq_formula {R : Type*} [CommRing R] {m n : ℕ}
    (L : Fin n → (R × R) × R) (f : Fin m → Fin n) (l : Fin 6 → Fin m) :
    secantCycleNumerator L f l = OriginalSecantProperness.secantNumerator (clearedPoints
      (fun i => L (f ((cyclicSuccessorPerm m)⁻¹ (l i)))) (fun i => L (f (l i)))) := rfl

theorem outerCyclePolynomial_eq {m n : ℕ} (L M : Fin n → CarrierLine)
    (f : Fin m → Fin n) (l : Fin 4 → Fin m) :
    outerCyclePolynomial L M f l =
      outerCycleNumerator (fun i => carrierPolynomial (L i) (M i)) f l := rfl

theorem secantCyclePolynomial_eq {m n : ℕ} (L M : Fin n → CarrierLine)
    (f : Fin m → Fin n) (l : Fin 6 → Fin m) :
    secantCyclePolynomial L M f l =
      secantCycleNumerator (fun i => carrierPolynomial (L i) (M i)) f l := rfl

theorem cycleSecantExclusions_iff_formula {m n : ℕ} (f : Fin m → Fin n)
    (L : Fin n → CarrierLine) : cycleSecantExclusions f L ↔
      (∀ l : Fin 4 → Fin m, Function.Injective l → outerCycleNumerator L f l ≠ 0) ∧
      (∀ l : Fin 6 → Fin m, Function.Injective l → secantCycleNumerator L f l ≠ 0) := Iff.rfl

theorem daughterSecantExclusions_iff {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (L : Fin n → CarrierLine) : daughterSecantExclusions q hq L ↔
      ∀ S : Finset (PolygonCrossing q),
        PolygonNonalternation.polygonNonalternating q hq.g2 S →
        ∀ root : PolygonEvent q,
          cycleSecantExclusions (daughterCarrier q hq.g2 S root) L := Iff.rfl

theorem actualDaughterSecants_iff {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) : actualDaughterSecants q hq ↔
      ∀ S : Finset (PolygonCrossing q),
        PolygonNonalternation.polygonNonalternating q hq.g2 S →
        ∀ root : PolygonEvent q, retainedCorner q S root →
          (∀ l : Fin 4 → Fin (Fintype.card (CornerCoord q hq.g2 S root)),
            Function.Injective l → OriginalOuterProperness.outerNumerator
              (daughterVertex q hq.g2 S root ∘ l) ≠ 0) ∧
          (∀ l : Fin 6 → Fin (Fintype.card (CornerCoord q hq.g2 S root)),
            Function.Injective l → OriginalSecantProperness.secantNumerator
              (daughterVertex q hq.g2 S root ∘ l) ≠ 0) := Iff.rfl

theorem cutCarrierLabel_eq {n : ℕ} (e : Fin (n+2)) (x : Fin (n+1) ⊕ Unit) :
    cutCarrierLabel e x = Sum.elim (ActiveArc.ExposedChart.edgeLabel e) (fun _ => e) x := rfl

end DirectGLSSW.CyclicCarrierClearing












