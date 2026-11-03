import ActiveArcParentWordTransport
import DirectGLSSW.DaughterRootRotation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits SingletonWords RetainedWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- Deletion preserves literal retained event labels, not just point values. -/
theorem retained_orbit_filter_reduced (x : {x : Event q // retained q S x}) :
    letI := eventOrder q hR.noTriple
    (orbitWord (incoming q hR.noTriple S) x.val).filter (fun y => decide (retained q S y))=
      (orbitWord (orderedCyclicSuccessor {x : Event q // retained q S x} *
        physicalRetainedPairing q S) x).map Subtype.val := by
  letI := eventOrder q hR.noTriple
  exact RetainedOrbitDeletion.orbitWord_filter_restrict (Event q) (retained q S)
    (pairing q S) (physicalRetainedPairing q S) (pairing_fixes_nonretained q S) (fun _ => rfl) x

/-- The actual incoming component relation on retained labels is exactly the
reduced component relation. No component equivalence is assumed. -/
theorem retained_sameCycle_iff_reduced
    (x y : {x : Event q // retained q S x}) :
    letI := eventOrder q hR.noTriple
    (incoming q hR.noTriple S).SameCycle x.val y.val ↔
      (orderedCyclicSuccessor {x : Event q // retained q S x} * physicalRetainedPairing q S).SameCycle x y := by
  letI := eventOrder q hR.noTriple
  have hd := retained_orbit_filter_reduced q hR S x
  constructor
  · intro hh
    have hm : y.val∈(orbitWord (incoming q hR.noTriple S) x.val).filter
        (fun z => decide (retained q S z)) :=
      List.mem_filter.mpr ⟨(mem_orbitWord_iff _ _ _).mpr hh,by simp only [y.property,decide_true]⟩
    rw [hd] at hm
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
    have he' : z=y := Subtype.ext he
    rw [he'] at hz
    exact (mem_orbitWord_iff _ _ _).mp hz
  · intro hh
    have hm : y.val∈(orbitWord (orderedCyclicSuccessor {x : Event q // retained q S x} *
        physicalRetainedPairing q S) x).map Subtype.val :=
      List.mem_map.mpr ⟨y,(mem_orbitWord_iff _ _ _).mpr hh,rfl⟩
    rw [← hd] at hm
    exact (mem_orbitWord_iff _ _ _).mp (List.mem_filter.mp hm).1

/-- Changing the actual retained root inside one incoming component only
cyclically rotates its literal physical point word. -/
theorem retainedWord_isRotated_of_sameCycle (x y : Event q)
    (hxy : (incoming q hR.noTriple S).SameCycle x y) :
    List.ofFn (RetainedWords.vertex q hR S x) ~r List.ofFn (RetainedWords.vertex q hR S y) := by
  rw [retainedWord_eq_filtered (a:=n) (b:=0) q hR S x,
    retainedWord_eq_filtered (a:=n) (b:=0) q hR S y]
  exact (DaughterRootRotation.listIsRotated_filter
    (DaughterRootRotation.orbitWord_isRotated_of_sameCycle _ x y hxy)
    (fun z => decide (retained q S z))).map (eventPoint q)

end DirectGLSSW.ActiveArc.CompatibleWords
