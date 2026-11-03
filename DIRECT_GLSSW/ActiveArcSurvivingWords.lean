import ActiveArcSurvivingRetained

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits CompatibleWords RetainedWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
variable (S : Finset (Crossing q)) (hS : ∀ d ∈ S, Survives q t d)
variable (hM : Regular (moveStart q t))

include hS in
theorem source_retainedWord_eq_mapped_reduced :
    letI := eventOrder (moveStart q t) hM.noTriple
    ∀ root : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x},
      List.ofFn (vertex q hR S (eventMap q t ht0 ht1 root.val)) =
      (orbitWord (orderedCyclicSuccessor _ * physicalRetainedPairing (moveStart q t)
        (movingSelection q t ht0 ht1 S)) root).map
        (fun x => eventPoint q (eventMap q t ht0 ht1 x.val)) := by
  letI := eventOrder (moveStart q t) hM.noTriple
  letI := eventOrder q hR.noTriple
  intro root
  rw [retainedWord_eq_reduced q hR S _ ((eventMap_retained q t ht0 ht1 S root.val).mpr root.property)]
  change (orbitWord (orderedCyclicSuccessor _ * physicalRetainedPairing q S)
    (retainedOrderIso q hR t ht0 ht1 S hS hM root)).map (fun x => eventPoint q x.val) = _
  rw [retainedOrderIso_orbitWord q hR t ht0 ht1 S hS hM,List.map_map]
  rfl

include hS in
/-- The literal retained open word changes ONLY at its first point whenever
every selected physical crossing survives the cursor move. -/
theorem open_word :
    List.ofFn (vertex (moveStart q t) hM (movingSelection q t ht0 ht1 S) (start (moveStart q t))) =
      affinePoint (q 0) (q 1) t :: (List.ofFn (vertex q hR S (start q))).tail := by
  letI := eventOrder (moveStart q t) hM.noTriple
  let T := movingSelection q t ht0 ht1 S
  let R := {x : Event (moveStart q t) // retained (moveStart q t) T x}
  let p := orderedCyclicSuccessor R * physicalRetainedPairing (moveStart q t) T
  let root : R := ⟨start (moveStart q t),(endpoints_retained _ T).1⟩
  have hold : List.ofFn (vertex q hR S (start q)) =
      (orbitWord p root).map (fun x => eventPoint q (eventMap q t ht0 ht1 x.val)) :=
    source_retainedWord_eq_mapped_reduced q hR t ht0 ht1 S hS hM root
  have hnew : List.ofFn (vertex (moveStart q t) hM T (start (moveStart q t))) =
      (orbitWord p root).map (fun x => eventPoint (moveStart q t) x.val) :=
    retainedWord_eq_reduced (moveStart q t) hM T _ (endpoints_retained _ T).1
  have hword : orbitWord p root = root :: (orbitWord p root).tail := by
    have hn := orbitWord_nonempty p root
    have hh : (orbitWord p root).head hn = root := by
      rw [List.head_eq_getElem_zero]
      simp [orbitWord,orbitEnumeration_zero]
    calc
      orbitWord p root = (orbitWord p root).head hn :: (orbitWord p root).tail :=
        (List.head_cons_tail (orbitWord p root) hn).symm
      _ = root :: (orbitWord p root).tail := by rw [hh]
  have hn : root ∉ (orbitWord p root).tail := by
    have hnd := orbitWord_nodup p root
    rw [hword] at hnd
    exact (List.nodup_cons.mp hnd).1
  rw [hold,hnew,hword,List.map_cons,List.map_cons,List.tail_cons]
  change moveStart q t 0 :: _ = _
  rw [moveStart_zero]
  congr 1
  apply List.map_congr_left
  intro x hx
  apply eventMap_point q hR t ht0 ht1 x.val
  intro he
  have heq : x = root := Subtype.ext he
  exact hn (heq ▸ hx)

include hS in
/-- Matching retained roots on a closed component give identical literal
point words. Canonical closed-root choices can subsequently be aligned by
the existing component rotation theorem. -/
theorem closed_root_word
    (root : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x})
    (hclosed : componentOf (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) root.val ≠
      openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) :
    List.ofFn (vertex (moveStart q t) hM (movingSelection q t ht0 ht1 S) root.val) =
      List.ofFn (vertex q hR S (eventMap q t ht0 ht1 root.val)) := by
  letI := eventOrder (moveStart q t) hM.noTriple
  let T := movingSelection q t ht0 ht1 S
  let p := orderedCyclicSuccessor {x : Event (moveStart q t) // retained (moveStart q t) T x} *
    physicalRetainedPairing (moveStart q t) T
  rw [source_retainedWord_eq_mapped_reduced q hR t ht0 ht1 S hS hM root,
    retainedWord_eq_reduced (moveStart q t) hM T root.val root.property]
  apply List.map_congr_left
  intro x hx
  apply eventMap_point q hR t ht0 ht1 x.val
  intro he
  have hd := RetainedOrbitDeletion.orbitWord_filter_restrict (Event (moveStart q t))
    (retained (moveStart q t) T) (pairing (moveStart q t) T)
    (physicalRetainedPairing (moveStart q t) T)
    (pairing_fixes_nonretained (moveStart q t) T) (fun _ => rfl) root
  change (orbitWord (incoming (moveStart q t) hM.noTriple T) root.val).filter
      (fun y => decide (retained (moveStart q t) T y)) =
    (orbitWord p root).map Subtype.val at hd
  have hmem : x.val ∈ (orbitWord (incoming (moveStart q t) hM.noTriple T) root.val).filter
      (fun y => decide (retained (moveStart q t) T y)) := by
    rw [hd]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have hh := (mem_orbitWord_iff _ _ _).mp (List.mem_filter.mp hmem).1
  apply hclosed
  apply (componentOf_eq_iff _ _ _).mpr
  simpa only [he] using hh

end DirectGLSSW.ActiveArc.Cursor.Surviving
