import DirectGLSSW.DaughterFirstReturn
import DirectGLSSW.PolygonNonalternation
import DirectGLSSW.RealPolygons
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace DirectGLSSW.GeometricSmoothingWeights
open scoped BigOperators
open DirectGLSSW.PermutationOrbits

abbrev SeparatingSupport {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) :=
    {S : Finset (PolygonCrossing q) //
      PolygonNonalternation.polygonNonalternating q hq.g2 S}

private theorem component_has_retained_root {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    ∃ root : PolygonEvent q,
      componentOf (smoothingDartPermutation q hq.g2 S) root = c ∧
        DaughterFirstReturn.retainedCorner q S root := by
  let p := smoothingDartPermutation q hq.g2 S
  let x : PolygonEvent q := Quotient.out c
  have hx : componentOf p x = c := Quotient.out_eq c
  obtain ⟨root, hrx, hret⟩ :=
    DaughterFirstReturn.everyDartOrbit_hasCorner q hq.g2 S
      hq.size_ge_three x
  have hcomp : componentOf p root = componentOf p x :=
    (componentOf_eq_iff p root x).2 hrx.symm
  exact ⟨root, hcomp.trans hx, hret⟩

/-- Select a retained event in each actual outgoing-dart quotient component.
The selection first takes `Quotient.out`, then moves within that orbit to a
retained corner using `everyDartOrbit_hasCorner`. -/
noncomputable def componentRoot {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) :
    Component (smoothingDartPermutation q hq.g2 S) → PolygonEvent q :=
  fun c => Classical.choose (component_has_retained_root q hq S c)

theorem componentRoot_sameComponent {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    componentOf (smoothingDartPermutation q hq.g2 S)
      (componentRoot q hq S c) = c :=
  (Classical.choose_spec (component_has_retained_root q hq S c)).1

theorem componentRoot_retainedCorner {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    DaughterFirstReturn.retainedCorner q S (componentRoot q hq S c) :=
  (Classical.choose_spec (component_has_retained_root q hq S c)).2

/-- The actual oriented polygon associated to one dart component, enumerated
from the chosen retained event. -/
noncomputable def componentPolygon {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S
      (componentRoot q hq S c))) → PlanarPoint ℝ :=
  DaughterFirstReturn.daughterVertex q hq.g2 S (componentRoot q hq S c)

theorem componentPolygon_list {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    List.ofFn (componentPolygon q hq S c) =
      DaughterFirstReturn.daughterPointList q hq.g2 S (componentRoot q hq S c) := rfl

/-- Auxiliary genericity is explicit for every separating support and every
possible component root. It is supplied as data; no inheritance from parent
genericity is asserted. -/
def auxiliaryGenericity {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) : Prop :=
    ∀ S : Finset (PolygonCrossing q),
      PolygonNonalternation.polygonNonalternating q hq.g2 S →
        ∀ root : PolygonEvent q, CyclicGeneric
          (DaughterFirstReturn.daughterVertex q hq.g2 S root)

/-- Amplitude of the actual daughter polygon at the explicitly selected root. -/
noncomputable def componentAmplitude {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (hAux : auxiliaryGenericity q hq)
    (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (c : Component (smoothingDartPermutation q hq.g2 S)) : ℚ :=
  polygonAmplitude (componentPolygon q hq S c)
    (hAux S hS (componentRoot q hq S c))

/-- Product of the component amplitudes for one actual separating smoothing. -/
noncomputable def componentAmplitudeProduct {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (hAux : auxiliaryGenericity q hq)
    (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S) : ℚ :=
  ∏ c : Component (smoothingDartPermutation q hq.g2 S),
    componentAmplitude q hq S hAux hS c

/-- The reference separating primitive: sum over actual pairwise
nonalternating supports with sign `(-1)^|S|`, multiplying the amplitudes of
all outgoing-dart smoothing components. -/
noncomputable def separatingSmoothingSum {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) : ℚ := by
  classical
  exact ∑ S : SeparatingSupport q hq,
    (-1 : ℚ) ^ S.1.card *
      componentAmplitudeProduct q hq S.1 hAux S.2

end DirectGLSSW.GeometricSmoothingWeights
