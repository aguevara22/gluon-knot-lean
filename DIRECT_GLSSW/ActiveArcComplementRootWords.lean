import ActiveArcRetainedOrbitComponents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- Full original retained event words at any singleton-complement retained
root are exactly the reduced complement event words. -/
theorem complementRetained_orbit_filter (x : ComplementRetained q hR c hc hcut S T) :
    letI := eventOrder q hR.noTriple
    (orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) x.val).filter
      (fun z => decide (retained q (insert c (pieceSelections q hR c hc hcut S T)) z))=
      (orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
        complementRetainedPairing q hR c hc hcut S T) x).map Subtype.val := by
  letI := eventOrder q hR.noTriple
  let z := (complementFlattenOrderIso q hR c hc hcut S T).symm x
  have hd := RetainedOrbitDeletion.orbitWord_filter_restrict (ComplementEvent q hR c)
    (fun x => retained q (insert c (pieceSelections q hR c hc hcut S T)) x.val)
    (complementEventPairing q hR c hc hcut S T) (complementDoublePairing q hR c hc hcut S T)
    (complementEventPairing_fixes_nonretained q hR c hc hcut S T)
    (complementDoublePairing_val q hR c hc hcut S T) z
  have hf := complementFlatten_orbitWord q hR c hc hcut S T z
  change orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
      complementRetainedPairing q hR c hc hcut S T) x=
    (orbitWord (orderedCyclicSuccessor (ComplementDoubleRetained q hR c hc hcut S T) *
      complementDoublePairing q hR c hc hcut S T) z).map (complementFlattenOrderIso q hR c hc hcut S T) at hf
  have ho := orbitWord_map_injective
    (orderedCyclicSuccessor (ComplementEvent q hR c) * complementEventPairing q hR c hc hcut S T)
    (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
    Subtype.val Subtype.val_injective
    (fun y => (complementEvent_incoming q hR c hc hcut S T y).symm) z.val
  change orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) x.val=
    (orbitWord (orderedCyclicSuccessor (ComplementEvent q hR c) *
      complementEventPairing q hR c hc hcut S T) z.val).map Subtype.val at ho
  rw [ho,← DaughterPointListFilter.map_filter_comp,hd,List.map_map,hf,List.map_map]
  rfl

theorem complementRetained_pointWord (x : ComplementRetained q hR c hc hcut S T) :
    letI := eventOrder q hR.noTriple
    List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T)) x.val)=
      (orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
        complementRetainedPairing q hR c hc hcut S T) x).map (fun y => eventPoint q y.val) := by
  letI := eventOrder q hR.noTriple
  rw [retainedWord_eq_filtered,complementRetained_orbit_filter,List.map_map]
  rfl

/-- Exact original component membership on retained complement labels. -/
theorem complementRetained_sameCycle_iff
    (x y : ComplementRetained q hR c hc hcut S T) :
    letI := eventOrder q hR.noTriple
    (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle x.val y.val ↔
      (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
        complementRetainedPairing q hR c hc hcut S T).SameCycle x y := by
  letI := eventOrder q hR.noTriple
  have hd := complementRetained_orbit_filter q hR c hc hcut S T x
  constructor
  · intro hh
    have hm : y.val∈(orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) x.val).filter
        (fun z => decide (retained q (insert c (pieceSelections q hR c hc hcut S T)) z)) :=
      List.mem_filter.mpr ⟨(mem_orbitWord_iff _ _ _).mpr hh,by simp only [y.property.1,decide_true]⟩
    rw [hd] at hm
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
    have he' : z=y := Subtype.ext he
    rw [he'] at hz
    exact (mem_orbitWord_iff _ _ _).mp hz
  · intro hh
    have hm : y.val∈(orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
        complementRetainedPairing q hR c hc hcut S T) x).map Subtype.val :=
      List.mem_map.mpr ⟨y,(mem_orbitWord_iff _ _ _).mpr hh,rfl⟩
    rw [← hd] at hm
    exact (mem_orbitWord_iff _ _ _).mp (List.mem_filter.mp hm).1

end DirectGLSSW.ActiveArc.CompatibleWords
