import ActiveArcTinyParentRetainedWord
import DirectGLSSW.DaughterPointListFilter

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable

private theorem retainedPointWord_eq_filtered {n : ℕ} (r : Fin (n+2) → PlanarPoint ℝ)
    (hr : Regular r) (S : Finset (Crossing r)) (x : Event r) :
    List.ofFn (RetainedWords.vertex r hr S x) =
      ((orbitWord (incoming r hr.noTriple S) x).filter
        (fun z => decide (retained r S z))).map (eventPoint r) := by
  classical
  let E := RetainedWords.enumeration r hr S x
  have hcoords :
      List.ofFn (fun i : Fin (Fintype.card (RetainedWords.Corner r hr S x)) => (E i).val)=
        (List.ofFn (fun i : RetainedWords.Coord r hr S x => i)).filter
          (fun i => decide (ActiveArc.retained r S (RetainedWords.eventAt r hr S x i))) := by
    have hs₁ : (List.ofFn (fun i : Fin (Fintype.card (RetainedWords.Corner r hr S x)) => (E i).val)).Sorted (· < ·) := by
      apply List.sorted_lt_ofFn_iff.mpr
      intro i j hij
      exact E.strictMono hij
    have hs₂ : ((List.ofFn (fun i : RetainedWords.Coord r hr S x => i)).filter
        (fun i => decide (ActiveArc.retained r S (RetainedWords.eventAt r hr S x i)))).Sorted (· < ·) :=
      (List.sorted_lt_ofFn_iff.mpr strictMono_id).filter _
    apply List.Sorted.eq_of_mem_iff hs₁ hs₂
    intro i
    constructor
    · intro hi
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
      have hret := (E j).property
      rw [hj] at hret
      exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,by simpa using hret⟩
    · intro hi
      obtain ⟨_,hret⟩ := List.mem_filter.mp hi
      have hret' : ActiveArc.retained r S (RetainedWords.eventAt r hr S x i) := by simpa using hret
      let c : RetainedWords.Corner r hr S x := ⟨i,hret'⟩
      exact List.mem_ofFn.mpr ⟨E.symm c,by simp [c]⟩
  have hmapped := congrArg (List.map (RetainedWords.eventAt r hr S x)) hcoords
  have hevents : List.ofFn (RetainedWords.cornerEvent r hr S x)=
      (orbitWord (ActiveArc.incoming r hr.noTriple S) x).filter (fun z => decide (ActiveArc.retained r S z)) := by
    change List.ofFn (fun i => RetainedWords.eventAt r hr S x (E i).val)=
      (List.ofFn (RetainedWords.eventAt r hr S x)).filter (fun z => decide (ActiveArc.retained r S z))
    simpa only [List.map_ofFn,Function.comp_def] using
      hmapped.trans (DaughterPointListFilter.map_filter_comp (RetainedWords.eventAt r hr S x)
        (fun z => decide (ActiveArc.retained r S z)) (List.ofFn fun i : RetainedWords.Coord r hr S x => i))
  have hpoints := congrArg (List.map (ActiveArc.eventPoint r)) hevents
  simpa [RetainedWords.vertex,List.map_ofFn] using hpoints

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

include hR hc hη hη1 in
theorem parentEventIntoTiny_point (x : Event (ParentArc q c hcut)) :
    eventPoint (TinyArc q c hcut η) (parentEventIntoTiny q c hcut η x) =
      eventPoint (ParentArc q c hcut) x := by
  cases x with
  | inl i => simp [eventPoint,parentEventIntoTiny,TinyArc,ParentArc]
  | inr x =>
    rcases x with ⟨d,side⟩
    exact crossingFromParent_point q hR c hc hcut η hη hη1 d

/-- Canonical increasing retained point enumeration of the actual tiny arc. -/
theorem tinyParent_openPointWord (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :
    List.ofFn (RetainedWords.vertex (TinyArc q c hcut η)
      (TinyRegular q hR c hc hcut η hη hη1) (parentTinySelection q c hcut η T.val)
      (start (TinyArc q c hcut η))) =
    tinyParent q c hcut η 0 :: List.ofFn (RetainedWords.vertex (ParentArc q c hcut)
      (ParentRegular q hR c hcut) T.val (start (ParentArc q c hcut))) := by
  rw [retainedPointWord_eq_filtered,retainedPointWord_eq_filtered]
  rw [tinyParent_openEventWord (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T]
  have hret : ∀ x : Event (ParentArc q c hcut),
      decide (retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
        (parentEventIntoTiny q c hcut η x)) =
      decide (retained (ParentArc q c hcut) T.val x) := by
    intro x
    have he := parentEventIntoTiny_retained q hR c hcut η T x
    by_cases hp : retained (ParentArc q c hcut) T.val x
    · have ht := he.mpr hp
      simp only [hp,ht,decide_true]
    · have ht : ¬ retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
          (parentEventIntoTiny q c hcut η x) := fun hh => hp (he.mp hh)
      simp only [hp,ht,decide_false]
  have hstart : decide (retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
      (start (TinyArc q c hcut η)))=true := by
    exact decide_eq_true (endpoints_retained _ _).1
  simp only [List.filter_cons,hstart,ite_true,List.map_cons]
  congr 1
  rw [← DaughterPointListFilter.map_filter_comp]
  simp only [List.map_map]
  change List.map (eventPoint (TinyArc q c hcut η) ∘ parentEventIntoTiny q c hcut η)
    ((orbitWord (incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val)
      (start (ParentArc q c hcut))).filter
        (fun x => decide (retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
          (parentEventIntoTiny q c hcut η x)))) = _
  simp only [hret]
  apply List.map_congr_left
  intro x hx
  exact parentEventIntoTiny_point q hR c hc hcut η hη hη1 x

end DirectGLSSW.ActiveArc.LiteralTinyParent
