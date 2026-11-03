import ActiveArcPhysicalWords
import DirectGLSSW.ChordNonalternation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Nonalternation
open DirectGLSSW FiniteCycleOrder PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

def eventOrderIso : letI := eventOrder q hR.noTriple;
    Fin (Fintype.card (Event q)) ≃o Event q := by
  letI := eventOrder q hR.noTriple
  exact increasingEnumeration (Event q)

def eventEnumeration : Fin (Fintype.card (Event q)) ≃ Event q :=
  (eventOrderIso q hR).toEquiv

def actualEndpoint (v : Crossing q × Bool) : Fin (Fintype.card (Event q)) :=
  (eventEnumeration q hR).symm (Sum.inr v)

@[simp] theorem eventEnumeration_actualEndpoint (c : Crossing q) (b : Bool) :
    eventEnumeration q hR (actualEndpoint q hR (c,b))=Sum.inr (c,b) := by
  simp [actualEndpoint]

theorem actualEndpoint_injective : Function.Injective (actualEndpoint q hR) := by
  intro a b hab
  have hh := congrArg (eventEnumeration q hR) hab
  have hs : (Sum.inr a : Event q)=Sum.inr b := by
    simpa only [actualEndpoint,Equiv.apply_symm_apply] using hh
  exact Sum.inr.inj hs

def between (x y z : Event q) : Prop := by
  letI := eventOrder q hR.noTriple
  exact strictCyclicBetween x y z

/-- Literal nonalternation on the physical arc's event circle, including endpoint anchors. -/
def Nonalternating (S : Finset (Crossing q)) : Prop :=
  ∀ c∈S, ∀ d∈S, c≠d →
    (between q hR (Sum.inr (c,false)) (Sum.inr (d,false)) (Sum.inr (c,true)) ↔
      between q hR (Sum.inr (c,false)) (Sum.inr (d,true)) (Sum.inr (c,true)))

theorem between_iff_coordinates (x y z : Event q) :
    between q hR x y z ↔ strictCyclicBetween ((eventEnumeration q hR).symm x)
      ((eventEnumeration q hR).symm y) ((eventEnumeration q hR).symm z) := by
  letI := eventOrder q hR.noTriple
  exact (strictCyclicBetween_orderIso (eventOrderIso q hR).symm x y z).symm

theorem nonalternating_iff_abstract (S : Finset (Crossing q)) :
    Nonalternating q hR S ↔ ChordNonalternation.Nonalternating (actualEndpoint q hR) S := by
  simp only [Nonalternating,ChordNonalternation.Nonalternating,between_iff_coordinates,actualEndpoint]

theorem pairing_singleton (c : Crossing q) :
    pairing q {c}=Equiv.swap (Sum.inr (c,false) : Event q) (Sum.inr (c,true)) := by
  classical
  ext x
  cases x with
  | inl i => simp [pairing,pairingMap,Equiv.swap_apply_def]
  | inr v =>
    rcases v with ⟨d,b⟩
    by_cases hd : d=c
    · subst d
      cases b <;> simp [pairing,pairingMap,Equiv.swap_apply_def,Sum.inr.injEq,Prod.mk.injEq]
    · have hl : (Sum.inr (d,b) : Event q)≠Sum.inr (c,false) :=
        fun hh => hd (congrArg Prod.fst (Sum.inr.inj hh))
      have hr : (Sum.inr (d,b) : Event q)≠Sum.inr (c,true) :=
        fun hh => hd (congrArg Prod.fst (Sum.inr.inj hh))
      simp [pairing,pairingMap,Equiv.swap_apply_def,hd,hl,hr]

theorem pairing_empty : pairing q ∅=1 := by
  classical
  ext x
  cases x with
  | inl i => rfl
  | inr v => simp [pairing,pairingMap]

theorem pairing_insert (S : Finset (Crossing q)) (c : Crossing q) (hc : c∉S) :
    pairing q (insert c S)=pairing q {c}*pairing q S := by
  classical
  ext x
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨d,b⟩
    by_cases hd : d=c
    · subst d
      cases b <;> simp [pairing,pairingMap,hc,Equiv.Perm.mul_apply]
    · by_cases hs : d∈S <;> cases b <;> simp [pairing,pairingMap,hd,hs,Equiv.Perm.mul_apply]

theorem singleton_intertwines (c : Crossing q) (i : Fin (Fintype.card (Event q))) :
    eventEnumeration q hR (ChordNonalternation.chordSwap (actualEndpoint q hR) c i)=
      pairing q {c} (eventEnumeration q hR i) := by
  classical
  rw [ChordNonalternation.chordSwap,pairing_singleton]
  have h0 := eventEnumeration_actualEndpoint q hR c false
  have h1 := eventEnumeration_actualEndpoint q hR c true
  by_cases h0i : i=actualEndpoint q hR (c,false)
  · subst i;simp [Equiv.swap_apply_def,h0,h1]
  · by_cases h1i : i=actualEndpoint q hR (c,true)
    · subst i;simp [Equiv.swap_apply_def,h0,h1]
    · have h0i' : eventEnumeration q hR i≠Sum.inr (c,false) := by
        intro hh;apply h0i;apply (eventEnumeration q hR).injective;exact hh.trans h0.symm
      have h1i' : eventEnumeration q hR i≠Sum.inr (c,true) := by
        intro hh;apply h1i;apply (eventEnumeration q hR).injective;exact hh.trans h1.symm
      simp [Equiv.swap_apply_def,h0,h1,h0i,h1i,h0i',h1i']

theorem swapProduct_intertwines (S : Finset (Crossing q)) (i : Fin (Fintype.card (Event q))) :
    eventEnumeration q hR (ChordNonalternation.swapProduct (actualEndpoint q hR)
      (actualEndpoint_injective q hR) S i)=pairing q S (eventEnumeration q hR i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ChordNonalternation.swapProduct_empty,pairing_empty]
  | @insert c S hc ih =>
    rw [ChordNonalternation.swapProduct_insert (actualEndpoint q hR)
      (actualEndpoint_injective q hR) S c hc,Equiv.Perm.mul_apply]
    rw [singleton_intertwines,pairing_insert q S c hc,Equiv.Perm.mul_apply,ih]

theorem successor_intertwines (i : Fin (Fintype.card (Event q))) :
    eventEnumeration q hR (cyclicSuccessorPerm (Fintype.card (Event q)) i)=
      successor q hR.noTriple (eventEnumeration q hR i) := by
  letI := eventOrder q hR.noTriple
  change _=orderedCyclicSuccessor (Event q) _
  rw [orderedCyclicSuccessor_apply]
  simp [eventEnumeration,eventOrderIso,cyclicSuccessorPerm_apply]

theorem incoming_intertwines (S : Finset (Crossing q)) (i : Fin (Fintype.card (Event q))) :
    eventEnumeration q hR (ChordNonalternation.smoothing (actualEndpoint q hR)
      (actualEndpoint_injective q hR) S i)=incoming q hR.noTriple S (eventEnumeration q hR i) := by
  simp only [ChordNonalternation.smoothing,incoming,Equiv.Perm.mul_apply]
  rw [successor_intertwines,swapProduct_intertwines]

/-- Literal physical nonalternation is exactly the maximal count, by the proved finite chord theorem. -/
theorem nonalternating_iff_componentCount (S : Finset (Crossing q)) :
    Nonalternating q hR S ↔ componentCount (incoming q hR.noTriple S)=S.card+1 := by
  letI : Nonempty (Event q) := ⟨start q⟩
  letI : NeZero (Fintype.card (Event q)) := ⟨Nat.ne_of_gt Fintype.card_pos⟩
  rw [← componentCount_eq_of_intertwining (eventEnumeration q hR)
    (ChordNonalternation.smoothing (actualEndpoint q hR) (actualEndpoint_injective q hR) S)
    (incoming q hR.noTriple S) (incoming_intertwines q hR S)]
  exact (nonalternating_iff_abstract q hR S).trans
    (ChordNonalternation.nonalternating_iff_componentCount (actualEndpoint q hR) (actualEndpoint_injective q hR) S)

end DirectGLSSW.ActiveArc.Nonalternation
