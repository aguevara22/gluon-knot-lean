import DirectGLSSW.DaughterCarrier
import DirectGLSSW.EdgeCrossingVisits
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeComponentRoots

open Equiv PermutationOrbits PolygonNonalternation DaughterFirstReturn

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

abbrev EdgeRoot (q : Fin n → PlanarPoint K) (e : Fin n)
    (T : Finset (EdgeChord q e)) := Option {c : EdgeChord q e // c ∈ T}

def rootEvent (q : Fin n → PlanarPoint K) (e : Fin n)
    (T : Finset (EdgeChord q e)) : EdgeRoot q e T → PolygonEvent q
  | none => Sum.inl e
  | some c => Sum.inr (edgeVisit q e c.val)

theorem rootEvent_injective (q : Fin n → PlanarPoint K) (e : Fin n)
    (T : Finset (EdgeChord q e)) : Function.Injective (rootEvent q e T) := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => cases h
  | some a =>
      cases b with
      | none => cases h
      | some b =>
          have hv : edgeVisit q e a.val = edgeVisit q e b.val := Sum.inr.inj h
          have hab : a = b := Subtype.ext (edgeVisit_injective q e hv)
          exact congrArg some hab


theorem rootEvent_retained (q : Fin n → PlanarPoint K) (e : Fin n)
    (T : Finset (EdgeChord q e)) (r : EdgeRoot q e T) :
    retainedCorner q (T.image Subtype.val) (rootEvent q e T r) := by
  classical
  cases r with
  | none => trivial
  | some c =>
      change c.val.val ∈ T.image Subtype.val
      exact Finset.mem_image.mpr ⟨c.val, c.property, rfl⟩


theorem rootEvent_edge (q : Fin n → PlanarPoint K) (e : Fin n)
    (T : Finset (EdgeChord q e)) (r : EdgeRoot q e T) :
    polygonEventEdge q (rootEvent q e T r) = e := by
  cases r with
  | none => rfl
  | some c => exact (edgeVisitSide_spec q e c.val).1


def rootComponent (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (e : Fin n)
    (T : Finset (EdgeChord q e)) : EdgeRoot q e T →
      Component (smoothingDartPermutation q hq (T.image Subtype.val)) :=
  fun r => componentOf (smoothingDartPermutation q hq (T.image Subtype.val))
    (rootEvent q e T r)

theorem rootComponent_injective (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n) (e : Fin n)
    (T : Finset (EdgeChord q e))
    (hNA : polygonNonalternating q hq (T.image Subtype.val)) :
    Function.Injective (rootComponent q hq e T) := by
  intro a b hab
  apply rootEvent_injective q e T
  apply retained_sameEdge_eq_of_sameCycle q hq (T.image Subtype.val) hn hNA
    (rootEvent_retained q e T a) (rootEvent_retained q e T b)
  · rw [rootEvent_edge, rootEvent_edge]
  · exact (componentOf_eq_iff _ _ _).mp hab


theorem rootComponent_bijective (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n) (e : Fin n)
    (T : Finset (EdgeChord q e))
    (hNA : polygonNonalternating q hq (T.image Subtype.val)) :
    Function.Bijective (rootComponent q hq e T) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card (rootComponent q hq e T)).mpr
  refine ⟨rootComponent_injective q hq hn e T hNA, ?_⟩
  have hc := (polygonNonalternating_iff_dart_count q hq hn
    (T.image Subtype.val)).mp hNA
  change Fintype.card (Option {c : EdgeChord q e // c ∈ T}) =
    componentCount (smoothingDartPermutation q hq (T.image Subtype.val))
  rw [hc]
  simp only [Fintype.card_option, Fintype.card_coe,
    Finset.card_image_of_injective T Subtype.val_injective]











end
end DirectGLSSW.MixedEdgeComponentRoots
