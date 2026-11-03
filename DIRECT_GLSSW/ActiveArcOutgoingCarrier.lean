import ActiveArcNonalternation
import ActiveArcRetainedGapOwnership
import DirectGLSSW.DaughterCarrierOrder

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc PermutationOrbits Nonalternation FiniteCycleOrder RetainedWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

/-- Outgoing labels of the same actual incoming smoothing, with no added physical edge. -/
def outgoingPermutation (S : Finset (Crossing q)) : Equiv.Perm (Event q) :=
  pairing q S * successor q hR.noTriple

theorem outgoing_intertwines (S : Finset (Crossing q)) (i : Fin (Fintype.card (Event q))) :
    eventEnumeration q hR (ChordNonalternation.dartSmoothing (actualEndpoint q hR)
      (actualEndpoint_injective q hR) S i) =
    outgoingPermutation q hR S (eventEnumeration q hR i) := by
  simp only [ChordNonalternation.dartSmoothing,outgoingPermutation,Equiv.Perm.mul_apply]
  rw [swapProduct_intertwines,successor_intertwines]

theorem outgoing_sameCycle_iff (S : Finset (Crossing q)) (x y : Event q) :
    (ChordNonalternation.dartSmoothing (actualEndpoint q hR)
      (actualEndpoint_injective q hR) S).SameCycle
      ((eventEnumeration q hR).symm x) ((eventEnumeration q hR).symm y) ↔
    (outgoingPermutation q hR S).SameCycle x y := by
  simpa using sameCycle_iff_of_intertwining (eventEnumeration q hR) _ _
    (outgoing_intertwines q hR S) ((eventEnumeration q hR).symm x) ((eventEnumeration q hR).symm y)

/-- Nonalternation gives refinement on the identical actual outgoing event labels. -/
theorem outgoing_refines (S U : Finset (Crossing q)) (hSU : S ⊆ U)
    (hU : Nonalternating q hR U) {x y : Event q}
    (hxy : (outgoingPermutation q hR U).SameCycle x y) :
    (outgoingPermutation q hR S).SameCycle x y := by
  apply (outgoing_sameCycle_iff q hR S x y).mp
  exact ChordNonalternation.dartSmoothing_refines_of_subset (actualEndpoint q hR)
    (actualEndpoint_injective q hR) S U hSU ((nonalternating_iff_abstract q hR U).mp hU)
    ((outgoing_sameCycle_iff q hR U x y).mpr hxy)

/-- Two retained outgoing events in one nonalternating component cannot carry the same physical edge tag. -/
theorem retained_sameTag_eq (S : Finset (Crossing q)) (hS : Nonalternating q hR S)
    {x y : Event q} (hx : retained q S x) (hy : retained q S y)
    (htag : edgeTag q x = edgeTag q y)
    (hxy : (outgoingPermutation q hR S).SameCycle x y) : x = y := by
  letI := eventOrder q hR.noTriple
  have forward : ∀ {x y : Event q}, x < y → retained q S x → retained q S y →
      edgeTag q x = edgeTag q y → (outgoingPermutation q hR S).SameCycle x y → False := by
    intro x y hlt _ hyr he hcycle
    cases y with
    | inl j =>
      have hp : parameter q x < 0 := by
        have hh := (event_lt_iff q hR.noTriple x (Sum.inl j)).mp hlt
        rcases hh with hh | hh
        · exact False.elim ((ne_of_lt hh) he)
        · exact hh.2
      exact (not_lt_of_ge (PhysicalSegments.parameter_bounds q x).1) hp
    | inr v =>
      rcases v with ⟨d,b⟩
      have hd : d ∈ S := hyr
      have hsingle := outgoing_refines q hR {d} S (Finset.singleton_subset_iff.mpr hd) hS hcycle
      let E := eventEnumeration q hR
      let u := E.symm x
      let v := E.symm (Sum.inr (d,b))
      let a := actualEndpoint q hR (d,false)
      let z := actualEndpoint q hR (d,true)
      have huv : u < v := (Nonalternation.eventOrderIso q hR).symm.strictMono hlt
      have haz : a < z := by
        apply (Nonalternation.eventOrderIso q hR).symm.strictMono
        apply (event_lt_iff q hR.noTriple _ _).mpr
        left
        exact d.property.1
      have hcoords := (outgoing_sameCycle_iff q hR {d} x (Sum.inr (d,b))).mpr hsingle
      have hsinglePerm : ChordNonalternation.dartSmoothing (actualEndpoint q hR)
          (actualEndpoint_injective q hR) {d} = outgoingSplitPerm a z := by
        simp [ChordNonalternation.dartSmoothing,ChordNonalternation.swapProduct_singleton,
          ChordNonalternation.chordSwap,outgoingSplitPerm,a,z]
      rw [hsinglePerm] at hcoords
      have hside := mem_iff_of_sameCycle (outgoingSplitPerm a z) (outgoingIntervalSide a z)
        (outgoingIntervalSide_invariant a z haz) hcoords
      change (u ∈ outgoingIntervalSide a z ↔ v ∈ outgoingIntervalSide a z) at hside
      cases b with
      | false =>
        have hv : v = a := rfl
        rw [hv] at huv hside
        have hno : u ∉ outgoingIntervalSide a z := by
          change ¬(a.val ≤ u.val ∧ u.val < z.val)
          change u.val < a.val at huv
          omega
        have hin : a ∈ outgoingIntervalSide a z := ⟨le_rfl,haz⟩
        exact hno (hside.mpr hin)
      | true =>
        have hv : v = z := rfl
        rw [hv] at huv hside
        have hau : a < u := by
          apply (Nonalternation.eventOrderIso q hR).symm.strictMono
          apply (event_lt_iff q hR.noTriple _ _).mpr
          left
          rw [he]
          exact d.property.1
        have hin : u ∈ outgoingIntervalSide a z := ⟨hau.le,huv⟩
        have hno : z ∉ outgoingIntervalSide a z := by
          change ¬(a.val ≤ z.val ∧ z.val < z.val)
          omega
        exact hno (hside.mp hin)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact forward hlt hx hy htag hxy
  · exact forward hgt hy hx htag.symm hxy.symm

/-- Pairing converts the incoming convention to the same smoothing's outgoing convention. -/
theorem pairing_incoming (S : Finset (Crossing q)) (x : Event q) :
    pairing q S (incoming q hR.noTriple S x) =
      outgoingPermutation q hR S (pairing q S x) := rfl

/-- Retained incoming labels on one component have distinct paired outgoing edge tags. -/
theorem incoming_retained_sameTag_eq (S : Finset (Crossing q)) (hS : Nonalternating q hR S)
    {x y : Event q} (hx : retained q S x) (hy : retained q S y)
    (htag : edgeTag q (pairing q S x) = edgeTag q (pairing q S y))
    (hxy : (incoming q hR.noTriple S).SameCycle x y) : x = y := by
  apply (pairing q S).injective
  apply retained_sameTag_eq q hR S hS
    (PhysicalSegments.retained_pairing q S x hx) (PhysicalSegments.retained_pairing q S y hy) htag
  exact (sameCycle_iff_of_intertwining (pairing q S) _ _ (pairing_incoming q hR S) x y).mp hxy

/-- Every component uses each physical outgoing carrier at most once.
The terminal tag, when present, represents only the endpoint seam, not an added physical edge. -/
theorem retainedCarrier_injective (S : Finset (Crossing q)) (hS : Nonalternating q hR S)
    (root : Event q) :
    Function.Injective (fun i : Fin (Fintype.card (Corner q hR S root)) =>
      edgeTag q (pairing q S (cornerEvent q hR S root i))) := by
  intro i j hij
  apply cornerEvent_injective q hR S root
  apply incoming_retained_sameTag_eq q hR S hS
    (enumeration q hR S root i).property (enumeration q hR S root j).property hij
  apply (componentOf_eq_iff _ _ _).mp
  exact (orbitEnumeration (incoming q hR.noTriple S) root (enumeration q hR S root i).val).property.trans
    (orbitEnumeration (incoming q hR.noTriple S) root (enumeration q hR S root j).val).property.symm

/-- Carrier of a genuine consecutive retained open side; the terminal seam is excluded by its index. -/
def openSideCarrier (S : Finset (Crossing q)) (i : Fin (openCount q hR S - 1)) : Fin (n+1) :=
  PhysicalSegments.outgoingEdge q S
    (cornerEvent q hR S (start q) ⟨i.val,by change i.val < openCount q hR S; have := i.isLt; omega⟩)
    (open_nonlast_ne_terminal q hR S _ (by
      change i.val + 1 < openCount q hR S
      have := i.isLt; omega))

/-- Actual nonalternating retained open sides have distinct genuine original carrier edges. -/
theorem openSideCarrier_injective (S : Finset (Crossing q)) (hS : Nonalternating q hR S) :
    Function.Injective (openSideCarrier q hR S) := by
  intro i j hij
  have ht := congrArg Fin.val hij
  have he := retainedCarrier_injective q hR S hS (start q) ht
  apply Fin.ext
  exact congrArg (fun k : Fin (Fintype.card (Corner q hR S (start q))) => k.val) he

end DirectGLSSW.ActiveArc.OpenCarrier
