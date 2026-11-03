import ActiveArcNonalternation

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.ChordNonalternation
open Equiv PermutationOrbits FiniteCycleOrder
universe u
variable {C : Type u} {m : ℕ}

/-- A selected chord alternating with another chord separates its two visits
in every final nonalternating smoothing, not just after the first cut. -/
theorem alternating_visits_separated (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (hS : Nonalternating e S)
    (d c : C) (hd : d ∈ S) (hdc : d ≠ c)
    (halt : ¬ (strictCyclicBetween (e (d,false)) (e (c,false)) (e (d,true)) ↔
      strictCyclicBetween (e (d,false)) (e (c,true)) (e (d,true)))) :
    ¬ (smoothing e he S).SameCycle (e (c,false)) (e (c,true)) := by
  classical
  intro h
  have hs := smoothing_refines_of_subset e he {d} S
    (Finset.singleton_subset_iff.mpr hd) hS h
  have hs' : (cyclicSuccessorPerm m * chordSwap e d).SameCycle
      (e (c,false)) (e (c,true)) := by
    simpa only [smoothing, swapProduct_singleton] using hs
  exact halt ((after_one_sameCycle_iff e he hdc).mp hs')

end DirectGLSSW.ChordNonalternation

namespace DirectGLSSW.ActiveArc.Nonalternation
open FiniteCycleOrder PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

theorem incoming_sameCycle_iff (S : Finset (Crossing q)) (x y : Event q) :
    (ChordNonalternation.smoothing (actualEndpoint q hR)
      (actualEndpoint_injective q hR) S).SameCycle
        ((eventEnumeration q hR).symm x) ((eventEnumeration q hR).symm y) ↔
      (incoming q hR.noTriple S).SameCycle x y := by
  simpa using (sameCycle_iff_of_intertwining (eventEnumeration q hR)
    (ChordNonalternation.smoothing (actualEndpoint q hR)
      (actualEndpoint_injective q hR) S)
    (incoming q hR.noTriple S) (incoming_intertwines q hR S)
    ((eventEnumeration q hR).symm x) ((eventEnumeration q hR).symm y))

/-- Literal physical visits of a crossing alternating with a selected chord
belong to different full smoothing components. No first-crossing assumption
or artificial closing-edge crossing is needed. -/
theorem incoming_alternating_separated (S : Finset (Crossing q))
    (hS : Nonalternating q hR S) (d c : Crossing q) (hd : d ∈ S) (hdc : d ≠ c)
    (halt : ¬ (between q hR (Sum.inr (d,false)) (Sum.inr (c,false)) (Sum.inr (d,true)) ↔
      between q hR (Sum.inr (d,false)) (Sum.inr (c,true)) (Sum.inr (d,true)))) :
    ¬ (incoming q hR.noTriple S).SameCycle (Sum.inr (c,false)) (Sum.inr (c,true)) := by
  intro h
  have hc := (incoming_sameCycle_iff q hR S _ _).mpr h
  have ha : ¬ (strictCyclicBetween (actualEndpoint q hR (d,false))
      (actualEndpoint q hR (c,false)) (actualEndpoint q hR (d,true)) ↔
      strictCyclicBetween (actualEndpoint q hR (d,false))
      (actualEndpoint q hR (c,true)) (actualEndpoint q hR (d,true))) := by
    simpa only [between_iff_coordinates, actualEndpoint] using halt
  exact ChordNonalternation.alternating_visits_separated (actualEndpoint q hR)
    (actualEndpoint_injective q hR) S ((nonalternating_iff_abstract q hR S).mp hS)
    d c hd hdc ha hc

theorem incoming_alternating_components_ne (S : Finset (Crossing q))
    (hS : Nonalternating q hR S) (d c : Crossing q) (hd : d ∈ S) (hdc : d ≠ c)
    (halt : ¬ (between q hR (Sum.inr (d,false)) (Sum.inr (c,false)) (Sum.inr (d,true)) ↔
      between q hR (Sum.inr (d,false)) (Sum.inr (c,true)) (Sum.inr (d,true)))) :
    componentOf (incoming q hR.noTriple S) (Sum.inr (c,false)) ≠
      componentOf (incoming q hR.noTriple S) (Sum.inr (c,true)) := by
  intro h
  exact incoming_alternating_separated q hR S hS d c hd hdc halt
    ((componentOf_eq_iff _ _ _).mp h)

/-- In particular the two visits cannot both belong to the distinguished
open component (the component of the physical initial anchor). -/
theorem not_both_in_open_of_alternating (S : Finset (Crossing q))
    (hS : Nonalternating q hR S) (d c : Crossing q) (hd : d ∈ S) (hdc : d ≠ c)
    (halt : ¬ (between q hR (Sum.inr (d,false)) (Sum.inr (c,false)) (Sum.inr (d,true)) ↔
      between q hR (Sum.inr (d,false)) (Sum.inr (c,true)) (Sum.inr (d,true)))) :
    ¬ (componentOf (incoming q hR.noTriple S) (Sum.inr (c,false)) =
        componentOf (incoming q hR.noTriple S) (start q) ∧
      componentOf (incoming q hR.noTriple S) (Sum.inr (c,true)) =
        componentOf (incoming q hR.noTriple S) (start q)) := by
  rintro ⟨h0,h1⟩
  exact incoming_alternating_components_ne q hR S hS d c hd hdc halt (h0.trans h1.symm)

end DirectGLSSW.ActiveArc.Nonalternation






