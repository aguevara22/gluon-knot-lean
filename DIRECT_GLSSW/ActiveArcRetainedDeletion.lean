import ActiveArcComplementFlattening
import ActiveArcParentReducedPoints
import RetainedOrbitDeletion

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable

/-- Actual incoming retained point words equal their concrete reduced
successor-times-pairing orbit, by deletion of unselected physical visits. -/
theorem retainedWord_eq_reduced {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (S : Finset (Crossing q)) (root : Event q) (hr : retained q S root) :
    letI := eventOrder q hR.noTriple
    List.ofFn (RetainedWords.vertex q hR S root)=
      (orbitWord (orderedCyclicSuccessor {x : Event q // retained q S x} *
        physicalRetainedPairing q S) ⟨root,hr⟩).map (fun x => eventPoint q x.val) := by
  letI := eventOrder q hR.noTriple
  have hd := RetainedOrbitDeletion.orbitWord_filter_restrict (Event q) (retained q S)
    (pairing q S) (physicalRetainedPairing q S) (pairing_fixes_nonretained q S)
    (fun _ => rfl) ⟨root,hr⟩
  change (orbitWord (incoming q hR.noTriple S) root).filter (fun x => decide (retained q S x))=
    (orbitWord (orderedCyclicSuccessor {x : Event q // retained q S x} *
      physicalRetainedPairing q S) ⟨root,hr⟩).map Subtype.val at hd
  rw [retainedWord_eq_filtered (a:=n) (b:=0) q hR S root,hd,List.map_map]
  rfl

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- The original literal retained open word equals the concrete reduced
singleton-complement point word. Erased original-only visits are deleted here. -/
theorem sourceWord_eq_complementReduced :
    letI := eventOrder q hR.noTriple
    List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T)) (start q))=
      (orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
        complementRetainedPairing q hR c hc hcut S T) (complementRetainedStart q hR c hc hcut S T)).map
          (fun x => eventPoint q x.val) := by
  letI := eventOrder q hR.noTriple
  let z : ComplementDoubleRetained q hR c hc hcut S T :=
    ⟨complementEventStart q hR c hc hcut S T,(endpoints_retained q _).1⟩
  have hd := RetainedOrbitDeletion.orbitWord_filter_restrict (ComplementEvent q hR c)
    (fun x => retained q (insert c (pieceSelections q hR c hc hcut S T)) x.val)
    (complementEventPairing q hR c hc hcut S T) (complementDoublePairing q hR c hc hcut S T)
    (complementEventPairing_fixes_nonretained q hR c hc hcut S T)
    (complementDoublePairing_val q hR c hc hcut S T) z
  have hf := complementFlatten_orbitWord q hR c hc hcut S T z
  change orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
        complementRetainedPairing q hR c hc hcut S T) (complementRetainedStart q hR c hc hcut S T)=
    (orbitWord (orderedCyclicSuccessor (ComplementDoubleRetained q hR c hc hcut S T) *
      complementDoublePairing q hR c hc hcut S T) z).map (complementFlattenOrderIso q hR c hc hcut S T) at hf
  rw [retainedWord_eq_filtered,complementEvent_orbitWord,
    ← DaughterPointListFilter.map_filter_comp]
  rw [hd,List.map_map,List.map_map,hf,List.map_map]
  rfl

end DirectGLSSW.ActiveArc.CompatibleWords
