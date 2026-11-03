import DirectGLSSW.DaughterFirstReturn
import DirectGLSSW.PolygonNonalternation
import DirectGLSSW.PolygonGeometry

set_option autoImplicit false

namespace DirectGLSSW.DaughterInjectivity

attribute [local instance] Classical.propDecidable

open Equiv
open DirectGLSSW.DaughterFirstReturn
open DirectGLSSW.PolygonNonalternation
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.EventSegmentGeometry

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ}
variable (q : Fin n → PlanarPoint K)
variable (hG2 : cyclicNoTripleIntersections q)
variable (S : Finset (PolygonCrossing q))

def selectedVisitTwin (x y : PolygonEvent q) : Prop :=
  ∃ c : PolygonCrossing q, c ∈ S ∧
    ((x = Sum.inr (c, false) ∧ y = Sum.inr (c, true)) ∨
     (x = Sum.inr (c, true) ∧ y = Sum.inr (c, false)))

theorem selectedVisits_differentDartOrbits
    (hn : 3 ≤ n) (hNA : polygonNonalternating q hG2 S)
    {c : PolygonCrossing q} (hc : c ∈ S) :
    componentOf (DartPerm q hG2 S) (.inr (c, false)) ≠
      componentOf (DartPerm q hG2 S) (.inr (c, true)) := by
  classical
  let T : Finset (PolygonCrossing q) := S.erase c
  have hcT : c ∉ T := by simp [T]
  have hST : S = insert c T := by
    simp [T, hc]
  have hNAInsert : polygonNonalternating q hG2 (insert c T) := by
    simpa [hST] using hNA
  have hsame :
      (smoothingIncomingPermutation q hG2 T).SameCycle
        (Sum.inr (c, false)) (Sum.inr (c, true)) :=
    incoming_sameCycle_before_insert q hG2 T c hcT hNAInsert
  have hdisj : Disjoint T {c} :=
    Finset.disjoint_singleton_right.mpr hcT
  have hSrepr : S = T ∪ {c} := by
    rw [hST]
    ext d
    simp [or_comm]
  have hsingle : smoothingPairing q {c} =
      (Equiv.swap (Sum.inr (c, false) : PolygonEvent q) (Sum.inr (c, true)) :
        Equiv.Perm (PolygonEvent q)) := by
    ext x
    cases x with
    | inl e => simp [smoothingPairing, smoothingPairingMap, Equiv.swap_apply_def]
    | inr v =>
        rcases v with ⟨d, b⟩
        by_cases h : d = c
        · subst d
          cases b <;> simp [smoothingPairing, smoothingPairingMap,
            crossingVisitFlip, Equiv.swap_apply_def, Sum.inr.injEq, Prod.mk.injEq]
        · have hl : (Sum.inr (d, b) : PolygonEvent q) ≠ Sum.inr (c, false) := by
            intro he
            exact h (congrArg Prod.fst (Sum.inr.inj he))
          have hr : (Sum.inr (d, b) : PolygonEvent q) ≠ Sum.inr (c, true) := by
            intro he
            exact h (congrArg Prod.fst (Sum.inr.inj he))
          simp only [Equiv.swap_apply_def]
          simp [smoothingPairing, smoothingPairingMap, h, hl, hr]
  have hnew :
      smoothingIncomingPermutation q hG2 S =
        smoothingIncomingPermutation q hG2 T *
          (Equiv.swap (Sum.inr (c, false) : PolygonEvent q) (Sum.inr (c, true)) :
            Equiv.Perm (PolygonEvent q)) := by
    calc
      smoothingIncomingPermutation q hG2 S =
          smoothingIncomingPermutation q hG2 (T ∪ {c}) := by rw [hSrepr]
      _ = smoothingIncomingPermutation q hG2 T * smoothingPairing q {c} :=
        by simpa only [PolygonEvent] using
          (smoothingIncomingPermutation_union q hG2 T {c} hdisj)
      _ = smoothingIncomingPermutation q hG2 T *
          (Equiv.swap (Sum.inr (c, false) : PolygonEvent q) (Sum.inr (c, true)) :
            Equiv.Perm (PolygonEvent q)) := by
        rw [hsingle]
  have hseparatedIncoming :
      ¬ (smoothingIncomingPermutation q hG2 S).SameCycle
        (Sum.inr (c, false) : PolygonEvent q) (Sum.inr (c, true)) := by
    rw [hnew]
    have hne :
        (Sum.inr (c, false) : PolygonEvent q) ≠ Sum.inr (c, true) := by
      intro h
      have hb := congrArg Prod.snd (Sum.inr.inj h)
      cases hb
    simpa only [PolygonEvent] using
      (@PermutationOrbits.not_sameCycle_mul_swap_of_sameCycle
        (PolygonEvent q) inferInstance inferInstance
        (smoothingIncomingPermutation q hG2 T)
        (Sum.inr (c, false)) (Sum.inr (c, true)) hne hsame)
  intro hDart
  have hImageFalse :
      smoothingComponentEquiv q hG2 S
        (componentOf (smoothingIncomingPermutation q hG2 S)
          (Sum.inr (c, false))) =
        componentOf (DartPerm q hG2 S) (Sum.inr (c, true)) := by
    rw [smoothingComponentEquiv_componentOf]
    simp [DartPerm, smoothingPairing_apply, smoothingPairingMap,
      crossingVisitFlip, hc]
  have hImageTrue :
      smoothingComponentEquiv q hG2 S
        (componentOf (smoothingIncomingPermutation q hG2 S)
          (Sum.inr (c, true))) =
        componentOf (DartPerm q hG2 S) (Sum.inr (c, false)) := by
    rw [smoothingComponentEquiv_componentOf]
    simp [DartPerm, smoothingPairing_apply, smoothingPairingMap,
      crossingVisitFlip, hc]
  have hIncoming :
      componentOf (smoothingIncomingPermutation q hG2 S) (Sum.inr (c, false)) =
      componentOf (smoothingIncomingPermutation q hG2 S) (Sum.inr (c, true)) := by
    apply (smoothingComponentEquiv q hG2 S).injective
    calc
      smoothingComponentEquiv q hG2 S
          (componentOf (smoothingIncomingPermutation q hG2 S)
            (Sum.inr (c, false))) =
        componentOf (DartPerm q hG2 S) (Sum.inr (c, true)) := hImageFalse
      _ = componentOf (DartPerm q hG2 S) (Sum.inr (c, false)) := hDart.symm
      _ = smoothingComponentEquiv q hG2 S
          (componentOf (smoothingIncomingPermutation q hG2 S)
            (Sum.inr (c, true))) := hImageTrue.symm
  exact hseparatedIncoming
    ((componentOf_eq_iff _ _ _).mp hIncoming)

include hG2 in
theorem retainedEventPoint_eq_cases
    (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    {x y : PolygonEvent q}
    (hx : retainedCorner q S x) (hy : retainedCorner q S y)
    (hpoint : polygonEventPoint q x = polygonEventPoint q y) :
    x = y ∨ selectedVisitTwin q S x y := by
  cases x with
  | inl e =>
    cases y with
    | inl f =>
      left
      have hef : e = f :=
        (cyclicNoncollinear_injective hn q hG1) (by simpa [polygonEventPoint] using hpoint)
      subst f
      rfl
    | inr v =>
      exfalso
      have hpt : q e = crossingPoint q v.1 := by
        simpa [polygonEventPoint, crossingVisitPoint] using hpoint
      let edge := crossingVisitEdge q v
      have hInterior : edgeInterior q edge (q e) := by
        rw [hpt]
        exact crossingVisitPoint_mem q v
      have hEnds : q edge ≠ q (cyclicSuccessor edge) := by
        intro h
        apply cyclicTangent_ne_zero hn q hG1 edge
        simp [cyclicTangent, h]
      have hleft : q e ≠ q edge :=
        onOpenSegment_ne_left hEnds hInterior
      have hright : q e ≠ q (cyclicSuccessor edge) :=
        onOpenSegment_ne_right hEnds hInterior
      have he : e ≠ edge := by
        intro h
        subst e
        exact hleft rfl
      have hes : e ≠ cyclicSuccessor edge := by
        intro h
        subst e
        exact hright rfl
      exact cyclic_vertex_not_in_nonincident_edge hn q hG1 edge e he hes hInterior
  | inr v =>
    cases y with
    | inl f =>
      exfalso
      have hpt : q f = crossingPoint q v.1 := by
        simpa [polygonEventPoint, crossingVisitPoint] using hpoint.symm
      let edge := crossingVisitEdge q v
      have hInterior : edgeInterior q edge (q f) := by
        rw [hpt]
        exact crossingVisitPoint_mem q v
      have hEnds : q edge ≠ q (cyclicSuccessor edge) := by
        intro h
        apply cyclicTangent_ne_zero hn q hG1 edge
        simp [cyclicTangent, h]
      have hleft : q f ≠ q edge :=
        onOpenSegment_ne_left hEnds hInterior
      have hright : q f ≠ q (cyclicSuccessor edge) :=
        onOpenSegment_ne_right hEnds hInterior
      have hf : f ≠ edge := by
        intro h
        subst f
        exact hleft rfl
      have hfs : f ≠ cyclicSuccessor edge := by
        intro h
        subst f
        exact hright rfl
      exact cyclic_vertex_not_in_nonincident_edge hn q hG1 edge f hf hfs hInterior
    | inr w =>
      rcases v with ⟨c, b⟩
      rcases w with ⟨d, a⟩
      have hcd : c = d := by
        apply crossingPoint_injective q hG2
        simpa [polygonEventPoint, crossingVisitPoint] using hpoint
      subst d
      cases b <;> cases a
      · left
        rfl
      · right
        refine ⟨c, ?_, Or.inl ⟨rfl, rfl⟩⟩
        simpa [retainedCorner] using hx
      · right
        refine ⟨c, ?_, Or.inr ⟨rfl, rfl⟩⟩
        simpa [retainedCorner] using hx
      · left
        rfl

noncomputable def daughterEvent (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) : PolygonEvent q :=
  orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val

theorem daughterEvent_retained (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    retainedCorner q S (daughterEvent q hG2 S root i) := by
  exact (cornerEnumeration q hG2 S root i).property

theorem daughterEvent_component (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    componentOf (DartPerm q hG2 S) (daughterEvent q hG2 S root i) =
      componentOf (DartPerm q hG2 S) root := by
  exact (PermutationOrbits.orbitEnumeration (DartPerm q hG2 S) root
    (cornerEnumeration q hG2 S root i).val).property

theorem orbitEventAt_injective (root : PolygonEvent q) :
    Function.Injective (orbitEventAt q hG2 S root) := by
  intro i j hij
  exact (PermutationOrbits.orbitEnumeration (DartPerm q hG2 S) root).injective
    (Subtype.ext hij)

theorem daughterEvent_injective (root : PolygonEvent q) :
    Function.Injective (daughterEvent q hG2 S root) := by
  intro i j hij
  have hcoords : (cornerEnumeration q hG2 S root i).val =
      (cornerEnumeration q hG2 S root j).val :=
    orbitEventAt_injective q hG2 S root hij
  have hsub : cornerEnumeration q hG2 S root i =
      cornerEnumeration q hG2 S root j := Subtype.ext hcoords
  exact (cornerEnumeration q hG2 S root).injective hsub

theorem retainedEventPoint_injective_on_dartOrbit
    (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : polygonNonalternating q hG2 S)
    {x y : PolygonEvent q}
    (hx : retainedCorner q S x) (hy : retainedCorner q S y)
    (hOrbit : componentOf (DartPerm q hG2 S) x =
      componentOf (DartPerm q hG2 S) y)
    (hpoint : polygonEventPoint q x = polygonEventPoint q y) :
    x = y := by
  rcases retainedEventPoint_eq_cases q hG2 S hn hG1 hx hy hpoint with hxy | htwin
  · exact hxy
  · rcases htwin with ⟨c, hc, hxy | hyx⟩
    · rcases hxy with ⟨hxe, hye⟩
      have hcomp := hOrbit
      rw [hxe, hye] at hcomp
      exact False.elim
        (selectedVisits_differentDartOrbits q hG2 S hn hNA hc hcomp)
    · rcases hyx with ⟨hxe, hye⟩
      have hcomp := hOrbit
      rw [hxe, hye] at hcomp
      exact False.elim
        (selectedVisits_differentDartOrbits q hG2 S hn hNA hc hcomp.symm)

theorem daughterVertex_injective (hn : 3 ≤ n)
    (hG1 : cyclicNoncollinear q)
    (hNA : polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : retainedCorner q S root) :
    Function.Injective (daughterVertex q hG2 S root) := by
  intro i j hpoint
  let x := daughterEvent q hG2 S root i
  let y := daughterEvent q hG2 S root j
  have hx : retainedCorner q S x := daughterEvent_retained q hG2 S root i
  have hy : retainedCorner q S y := daughterEvent_retained q hG2 S root j
  have hOrbit : componentOf (DartPerm q hG2 S) x =
      componentOf (DartPerm q hG2 S) y := by
    rw [daughterEvent_component, daughterEvent_component]
  have hxy : x = y :=
    retainedEventPoint_injective_on_dartOrbit q hG2 S hn hG1 hNA hx hy hOrbit
      (by simpa [x, y, daughterEvent, daughterVertex] using hpoint)
  exact daughterEvent_injective q hG2 S root hxy

end DirectGLSSW.DaughterInjectivity
