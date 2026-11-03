import ActiveArcTinyParentWords

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

abbrev TinyArc := tinyParent q c hcut η
abbrev ParentArc := parent q c hcut
abbrev TinyRegular := regular_tinyParent q hR c hc hcut η hη hη1
abbrev ParentRegular := regular_parent q hR c hcut

def tinySupportOfParent (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) : Nonalternation.Support (TinyArc q c hcut η)
    (TinyRegular q hR c hc hcut η hη hη1) :=
  ⟨parentTinySelection q c hcut η T.val,
    (parentTinySelection_nonalternating q hR c hc hcut η hη hη1 T.val).mpr T.property⟩

theorem crossingFromParent_mem_selection (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (d : Crossing (ParentArc q c hcut)) :
    crossingFromParent q c hcut η d ∈ parentTinySelection q c hcut η T.val ↔ d∈T.val := by
  constructor
  · intro hh
    obtain ⟨e,he,heq⟩ := Finset.mem_map.mp hh
    have hi := crossingFromParent_injective q c hcut η heq
    simpa [hi] using he
  · intro hh
    exact Finset.mem_map.mpr ⟨d,hh,rfl⟩

theorem parentEventIntoTiny_retained (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (x : Event (ParentArc q c hcut)) :
    retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
      (parentEventIntoTiny q c hcut η x) ↔
    retained (ParentArc q c hcut) T.val x := by
  cases x with
  | inl i => simp [retained,parentEventIntoTiny]
  | inr v =>
    rcases v with ⟨d,side⟩
    simpa [retained,parentEventIntoTiny] using crossingFromParent_mem_selection
      (q:=q) (hR:=hR) (c:=c) (hcut:=hcut) (η:=η) T d

theorem tinyParent_eventAt_shift (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (i : Coord (ParentArc q c hcut)
      (ParentRegular q hR c hcut) T.val (start (ParentArc q c hcut))) :
    eventAt (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val) (start (TinyArc q c hcut η))
      ⟨i.val+1,by
        have hcard := DirectGLSSW.PermutationInsertion.inserted_fibreCard
          (incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val)
          (incoming (TinyArc q c hcut η)
            (TinyRegular q hR c hc hcut η hη hη1).noTriple
            (parentTinySelection q c hcut η T.val))
          (start (ParentArc q c hcut)) (start (TinyArc q c hcut η))
          (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
            (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1))
          (tinyParent_incoming_start (q:=q) (hR:=hR) (c:=c) (hc:=hc)
            (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)
          (tinyParent_incoming_step (q:=q) (hR:=hR) (c:=c) (hc:=hc)
            (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)
        have hi := i.isLt
        rw [hcard]
        omega⟩ =
      parentEventIntoTiny q c hcut η
        (eventAt (ParentArc q c hcut) (ParentRegular q hR c hcut)
          T.val (start (ParentArc q c hcut)) i) := by
  let p := incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val
  let r := incoming (TinyArc q c hcut η)
    (TinyRegular q hR c hc hcut η hη hη1).noTriple (parentTinySelection q c hcut η T.val)
  let E := tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)
  have hb := tinyParent_incoming_start (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T
  have hs := tinyParent_incoming_step (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T
  have hcard := DirectGLSSW.PermutationInsertion.inserted_fibreCard p r
    (start (ParentArc q c hcut)) (start (TinyArc q c hcut η)) E hb hs
  have hcard' : Fintype.card (Fibre
      (incoming (TinyArc q c hcut η)
        (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val))
      (componentOf (incoming (TinyArc q c hcut η)
        (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val)) (start (TinyArc q c hcut η))))=
    Fintype.card (Fibre (incoming (ParentArc q c hcut)
      (ParentRegular q hR c hcut).noTriple T.val)
      (componentOf (incoming (ParentArc q c hcut)
        (ParentRegular q hR c hcut).noTriple T.val) (start (ParentArc q c hcut)))) + 1 := by
    simpa [p,r] using hcard
  have hbound : i.val+1<Fintype.card (Fibre
      (incoming (TinyArc q c hcut η)
        (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val))
      (componentOf (incoming (TinyArc q c hcut η)
        (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val)) (start (TinyArc q c hcut η)))) := by
    rw [hcard']
    omega
  change (orbitEnumeration r (start (TinyArc q c hcut η))
      ⟨i.val+1,hbound⟩).val =
    parentEventIntoTiny q c hcut η (orbitEnumeration p (start (ParentArc q c hcut)) i).val
  rw [orbitEnumeration_apply_val,orbitEnumeration_apply_val]
  exact DirectGLSSW.PermutationInsertion.inserted_pow_beforeReturn p r
    (start (ParentArc q c hcut)) (start (TinyArc q c hcut η)) E hb hs i.val i.isLt

def parentOpenCorner (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :=
  Corner (ParentArc q c hcut) (ParentRegular q hR c hcut) T.val (start (ParentArc q c hcut))

def tinyOpenCorner (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :=
  Corner (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
    (parentTinySelection q c hcut η T.val) (start (TinyArc q c hcut η))

def tinyParentCornerMap (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) : Option (parentOpenCorner q hR c hcut T) →
    tinyOpenCorner q hR c hc hcut η hη hη1 T := by
  intro x
  cases x with
  | none =>
    refine ⟨0,?_⟩
    change retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
      (eventAt (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (parentTinySelection q c hcut η T.val) (start (TinyArc q c hcut η)) 0)
    rw [eventAt_zero]
    exact (endpoints_retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)).1
  | some x =>
    let i : Coord (ParentArc q c hcut) (ParentRegular q hR c hcut)
      T.val (start (ParentArc q c hcut)) := x.val
    have hcard := DirectGLSSW.PermutationInsertion.inserted_fibreCard
      (incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val)
      (incoming (TinyArc q c hcut η)
        (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val))
      (start (ParentArc q c hcut)) (start (TinyArc q c hcut η))
      (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1))
      (tinyParent_incoming_start (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)
      (tinyParent_incoming_step (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)
    refine ⟨⟨i.val+1,?_⟩,?_⟩
    · have hi := i.isLt
      rw [hcard]
      omega
    · change retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
        (eventAt (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
          (parentTinySelection q c hcut η T.val) (start (TinyArc q c hcut η))
          ⟨i.val+1,by have hi := i.isLt; rw [hcard]; omega⟩)
      rw [tinyParent_eventAt_shift (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T i]
      exact (parentEventIntoTiny_retained (q:=q) (hR:=hR) (c:=c)
        (hcut:=hcut) (η:=η) T (eventAt (ParentArc q c hcut)
          (ParentRegular q hR c hcut) T.val (start (ParentArc q c hcut)) i)).mpr x.property

end DirectGLSSW.ActiveArc.LiteralTinyParent
