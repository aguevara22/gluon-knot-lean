import ActiveArcTinyParentCornerCount

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

private theorem tinyParent_fibreCard (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :
    Fintype.card (Coord (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val) (start (TinyArc q c hcut η))) =
    Fintype.card (Coord (ParentArc q c hcut) (ParentRegular q hR c hcut)
      T.val (start (ParentArc q c hcut))) + 1 := by
  simpa only [Coord,Fintype.card_fin] using DirectGLSSW.PermutationInsertion.inserted_fibreCard
    (incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val)
    (incoming (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val))
    (start (ParentArc q c hcut)) (start (TinyArc q c hcut η))
    (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1))
    (tinyParent_incoming_start (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)
    (tinyParent_incoming_step (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)

theorem tinyParentCornerMap_bijective (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :
    Function.Bijective (tinyParentCornerMap q hR c hc hcut η hη hη1 T) := by
  constructor
  · intro x y he
    have hv := congrArg (fun z => z.val.val) he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => simp [tinyParentCornerMap] at hv
    | some x =>
      cases y with
      | none => simp [tinyParentCornerMap] at hv
      | some y =>
        congr 1
        apply Subtype.ext
        apply Fin.ext
        simpa only [tinyParentCornerMap,Nat.add_left_inj] using hv
  · intro z
    by_cases hz : z.val.val=0
    · refine ⟨none,?_⟩
      apply Subtype.ext
      apply Fin.ext
      simpa only [tinyParentCornerMap] using hz.symm
    · have hcard := tinyParent_fibreCard q hR c hc hcut η hη hη1 T
      simp only [Coord,Fintype.card_fin] at hcard
      have hzi := z.val.isLt
      let i : Coord (ParentArc q c hcut) (ParentRegular q hR c hcut)
          T.val (start (ParentArc q c hcut)) := ⟨z.val.val-1,by omega⟩
      have hi : i.val+1=z.val.val := by dsimp [i];omega
      have hshift := tinyParent_eventAt_shift q hR c hc hcut η hη hη1 T i
      have hzcoord : (⟨i.val+1,by
          have hh := i.isLt
          omega⟩ : Coord (TinyArc q c hcut η)
            (TinyRegular q hR c hc hcut η hη hη1) (parentTinySelection q c hcut η T.val)
            (start (TinyArc q c hcut η))) = z.val := Fin.ext hi
      rw [hzcoord] at hshift
      have hret := z.property
      change retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
        (eventAt (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
          (parentTinySelection q c hcut η T.val) (start (TinyArc q c hcut η)) z.val) at hret
      rw [hshift] at hret
      have hp := (parentEventIntoTiny_retained q hR c hcut η T
        (eventAt (ParentArc q c hcut) (ParentRegular q hR c hcut)
          T.val (start (ParentArc q c hcut)) i)).mp hret
      refine ⟨some ⟨i,hp⟩,?_⟩
      apply Subtype.ext
      apply Fin.ext
      exact hi

/-- The actual retained corners, including the newly inserted first corner. -/
def tinyParentCornerEquiv (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) : Option (parentOpenCorner q hR c hcut T) ≃
      tinyOpenCorner q hR c hc hcut η hη hη1 T :=
  Equiv.ofBijective _ (tinyParentCornerMap_bijective q hR c hc hcut η hη hη1 T)

theorem tinyParent_openCount (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :
    openCount (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val) =
    openCount (ParentArc q c hcut) (ParentRegular q hR c hcut) T.val + 1 := by
  letI : Fintype (parentOpenCorner q hR c hcut T) := by unfold parentOpenCorner; infer_instance
  letI : Fintype (tinyOpenCorner q hR c hc hcut η hη hη1 T) := by unfold tinyOpenCorner; infer_instance
  have hh := Fintype.card_congr (tinyParentCornerEquiv q hR c hc hcut η hη hη1 T)
  simpa only [Fintype.card_option,parentOpenCorner,tinyOpenCorner,openCount] using hh.symm

theorem tinyParentCornerMap_some_lt_iff (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (x y : parentOpenCorner q hR c hcut T) :
    (tinyParentCornerMap q hR c hc hcut η hη hη1 T (some x)).val <
      (tinyParentCornerMap q hR c hc hcut η hη hη1 T (some y)).val ↔ x.val<y.val := by
  change x.val.val+1 < y.val.val+1 ↔ x.val.val<y.val.val
  omega

theorem tinyParentCornerMap_none_lt_some (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (x : parentOpenCorner q hR c hcut T) :
    (tinyParentCornerMap q hR c hc hcut η hη hη1 T none).val <
      (tinyParentCornerMap q hR c hc hcut η hη hη1 T (some x)).val := by
  change 0 < x.val.val+1
  omega

end DirectGLSSW.ActiveArc.LiteralTinyParent
