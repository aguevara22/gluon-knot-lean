import DirectGLSSW.DaughterCarrierOrder
import DirectGLSSW.DaughterFirstReturn
import DirectGLSSW.PolygonNonalternation

set_option autoImplicit false

namespace DirectGLSSW.DaughterFirstReturn

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ} (q : Fin n → PlanarPoint K)
variable (hG2 : cyclicNoTripleIntersections q)
variable (S : Finset (PolygonCrossing q))

open Equiv
open DirectGLSSW.EventSegmentGeometry

theorem retained_sameEdge_eq_of_sameCycle
    (hn : 3 ≤ n)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    {x y : PolygonEvent q}
    (hx : retainedCorner q S x) (hy : retainedCorner q S y)
    (hedge : polygonEventEdge q x = polygonEventEdge q y)
    (hcycle : (DartPerm q hG2 S).SameCycle x y) : x = y := by
  classical
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hG2
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hG2
  have forward : ∀ {x y : PolygonEvent q},
      (letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hG2; x < y) →
      retainedCorner q S x → retainedCorner q S y →
      polygonEventEdge q x = polygonEventEdge q y →
      (DartPerm q hG2 S).SameCycle x y → x = y := by
    intro x y hlt hx hy hedge hcycle
    letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hG2
    letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hG2
    cases y with
    | inl e =>
        cases x with
        | inl f =>
            have hef : f = e := by simpa [polygonEventEdge] using hedge
            subst f
            rfl
        | inr v =>
            have hev : crossingVisitEdge q v = e := by
              simpa [polygonEventEdge] using hedge
            have hparam := (polygonEvent_sameEdge_lt_iff q hG2
              (Sum.inr v) (Sum.inl e) hev).mp hlt
            have hpos := (crossingVisitParameter_spec q v).1
            change crossingVisitParameter q v < 0 at hparam
            exact False.elim ((not_lt_of_ge (le_of_lt hpos)) hparam)
    | inr v =>
        rcases v with ⟨c, b⟩
        have hc : c ∈ S := by simpa [retainedCorner] using hy
        have hsingle : (DartPerm q hG2 {c}).SameCycle x (Sum.inr (c, b)) := by
          have hsub : ({c} : Finset (PolygonCrossing q)) ⊆ S :=
            Finset.singleton_subset_iff.mpr hc
          exact PolygonNonalternation.dart_refines_of_subset q hG2 {c} S hsub hNA hcycle
        let eventEq : Fin (Fintype.card (PolygonEvent q)) ≃ PolygonEvent q :=
          PolygonNonalternation.eventEnumeration q hG2
        let xcoord := eventEq.symm x
        let ycoord := eventEq.symm (Sum.inr (c, b))
        let fcoord := PolygonNonalternation.actualEndpoint q hG2 (c, false)
        let tcoord := PolygonNonalternation.actualEndpoint q hG2 (c, true)
        have hxycoord : xcoord < ycoord := by
          change eventEq.symm x < eventEq.symm (Sum.inr (c, b))
          exact (polygonEventEnumeration q hG2).symm.strictMono hlt
        have hfalse_lt_true_event :
            (Sum.inr (c, false) : PolygonEvent q) < Sum.inr (c, true) := by
          apply (polygonEvent_lt_iff q hG2 _ _).2
          left
          simpa [polygonEventEdge, crossingVisitEdge] using c.property.1
        have hftcoord : fcoord < tcoord := by
          change (eventEq.symm (Sum.inr (c, false))) <
            (eventEq.symm (Sum.inr (c, true)))
          exact (polygonEventEnumeration q hG2).symm.strictMono hfalse_lt_true_event
        let p := ChordNonalternation.dartSmoothing
          (PolygonNonalternation.actualEndpoint q hG2)
          (PolygonNonalternation.actualEndpoint_injective q hG2) {c}
        have hp : p = FiniteCycleOrder.outgoingSplitPerm fcoord tcoord := by
          simp [p, ChordNonalternation.dartSmoothing,
            ChordNonalternation.swapProduct_singleton,
            ChordNonalternation.chordSwap,
            FiniteCycleOrder.outgoingSplitPerm, fcoord, tcoord]
        have hinter : ∀ i, eventEq (p i) = (DartPerm q hG2 {c}) (eventEq i) := by
          intro i
          simpa [p, eventEq, PolygonNonalternation.eventEnumeration, DartPerm] using
            (PolygonNonalternation.dart_intertwines q hG2 {c} i)
        have hsingle' : (DartPerm q hG2 {c}).SameCycle
            (eventEq xcoord) (eventEq ycoord) := by
          simpa [xcoord, ycoord] using hsingle
        have hcycleCoord : p.SameCycle xcoord ycoord := by
          exact (PermutationOrbits.sameCycle_iff_of_intertwining eventEq p (DartPerm q hG2 {c})
            hinter xcoord ycoord).mpr hsingle' 
        have hcycleOut :
            (FiniteCycleOrder.outgoingSplitPerm fcoord tcoord).SameCycle xcoord ycoord := by
          simpa [hp] using hcycleCoord
        have hside :
            (xcoord ∈ FiniteCycleOrder.outgoingIntervalSide fcoord tcoord ↔
             ycoord ∈ FiniteCycleOrder.outgoingIntervalSide fcoord tcoord) :=
          PermutationOrbits.mem_iff_of_sameCycle
            (FiniteCycleOrder.outgoingSplitPerm fcoord tcoord)
            (FiniteCycleOrder.outgoingIntervalSide fcoord tcoord)
            (FiniteCycleOrder.outgoingIntervalSide_invariant fcoord tcoord hftcoord)
            hcycleOut
        cases b with
        | false =>
            have hycoord : ycoord = fcoord := by rfl
            rw [hycoord] at hside
            have hxout : xcoord ∉ FiniteCycleOrder.outgoingIntervalSide fcoord tcoord := by
              change ¬ (fcoord.val ≤ xcoord.val ∧ xcoord.val < tcoord.val)
              have hxf : xcoord.val < fcoord.val := by
                have := hxycoord
                change xcoord.val < fcoord.val at this
                exact this
              omega
            have hyin : ycoord ∈ FiniteCycleOrder.outgoingIntervalSide fcoord tcoord := by
              change fcoord.val ≤ fcoord.val ∧ fcoord.val < tcoord.val
              have hftval : fcoord.val < tcoord.val := hftcoord
              exact ⟨le_rfl, hftval⟩
            have : False := by
              have hxIn := hside.mpr hyin
              exact hxout hxIn
            exact this.elim
        | true =>
            have hycoord : ycoord = tcoord := by rfl
            rw [hycoord] at hside
            have hsameedge_evt : polygonEventEdge q (Sum.inr (c, false)) <
                polygonEventEdge q x := by
              rw [hedge]
              simpa [polygonEventEdge, crossingVisitEdge] using c.property.1
            have hfalse_lt_x_event : (Sum.inr (c, false) : PolygonEvent q) < x := by
              letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hG2
              apply (polygonEvent_lt_iff q hG2 _ _).2
              exact Or.inl hsameedge_evt
            have hfxcoord : fcoord < xcoord := by
              change eventEq.symm (Sum.inr (c, false)) < eventEq.symm x
              exact (polygonEventEnumeration q hG2).symm.strictMono hfalse_lt_x_event
            have hxin : xcoord ∈ FiniteCycleOrder.outgoingIntervalSide fcoord tcoord := by
              change fcoord.val ≤ xcoord.val ∧ xcoord.val < tcoord.val
              exact ⟨by omega, by omega⟩
            have hyout : ycoord ∉ FiniteCycleOrder.outgoingIntervalSide fcoord tcoord := by
              change ¬ (fcoord.val ≤ tcoord.val ∧ tcoord.val < tcoord.val)
              omega
            have : False := by
              have hyIn := hside.mp hxin
              exact hyout hyIn
            exact this.elim
  by_cases hxy : x = y
  · exact hxy
  · rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact forward hlt hx hy hedge hcycle
    · have hrev := forward hgt hy hx hedge.symm hcycle.symm
      exact hrev.symm

noncomputable def daughterCarrier (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) : Fin n :=
  polygonEventEdge q
    (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val)

theorem daughterCarrier_injective
    (hn : 3 ≤ n)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    (root : PolygonEvent q) :
    Function.Injective (daughterCarrier q hG2 S root) := by
  classical
  intro i j hij
  let ci : CornerCoord q hG2 S root := cornerEnumeration q hG2 S root i
  let cj : CornerCoord q hG2 S root := cornerEnumeration q hG2 S root j
  let x := orbitEventAt q hG2 S root ci.val
  let y := orbitEventAt q hG2 S root cj.val
  have hx : retainedCorner q S x := ci.property
  have hy : retainedCorner q S y := cj.property
  have hEdge : polygonEventEdge q x = polygonEventEdge q y := by
    simpa [daughterCarrier, x, y, ci, cj] using hij
  let p := DartPerm q hG2 S
  have hxcomp : PermutationOrbits.componentOf p x =
      PermutationOrbits.componentOf p root := by
    exact (PermutationOrbits.orbitEnumeration p root ci.val).property
  have hycomp : PermutationOrbits.componentOf p y =
      PermutationOrbits.componentOf p root := by
    exact (PermutationOrbits.orbitEnumeration p root cj.val).property
  have hcycle : (DartPerm q hG2 S).SameCycle x y := by
    have hcomp : PermutationOrbits.componentOf p x =
        PermutationOrbits.componentOf p y := hxcomp.trans hycomp.symm
    exact Quotient.exact hcomp
  have hxy : x = y :=
    retained_sameEdge_eq_of_sameCycle q hG2 S hn hNA hx hy hEdge hcycle
  have hOrbit : ci.val = cj.val := by
    apply (PermutationOrbits.orbitEnumeration p root).injective
    exact Subtype.ext hxy
  have hCorner : ci = cj := Subtype.ext hOrbit
  have hFin : i = j := (cornerEnumeration q hG2 S root).injective hCorner
  exact hFin


end DirectGLSSW.DaughterFirstReturn
