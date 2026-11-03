import ActiveArcParentReducedPairing
import ActiveArcParentBaseFirstReturn
import ActiveArcOrbitEmbedding

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

abbrev ComplementEvent := {x : Event q // (Nonalternation.eventEnumeration q hR).symm x ∈
  complementSide (leftRank q hR c) (rightRank q hR c)}

def complementEventOrderIso :
    letI := eventOrder q hR.noTriple
    Fin (Fintype.card (Event q)-((rightRank q hR c).val-(leftRank q hR c).val)) ≃o
      ComplementEvent q hR c := by
  letI := eventOrder q hR.noTriple
  let e := Nonalternation.eventEnumeration q hR
  let F : complementSide (leftRank q hR c) (rightRank q hR c) ≃ ComplementEvent q hR c :=
    e.subtypeEquiv (by
      intro i
      change i∈complementSide (leftRank q hR c) (rightRank q hR c) ↔
        e.symm (e i)∈complementSide (leftRank q hR c) (rightRank q hR c)
      rw [Equiv.symm_apply_apply])
  refine { toEquiv := (complementOrderIso _ _ (rank_lt q hR c)).toEquiv.trans F
           map_rel_iff' := ?_ }
  intro i j
  change Nonalternation.eventOrderIso q hR (complementOrderIso _ _ (rank_lt q hR c) i).val≤
    Nonalternation.eventOrderIso q hR (complementOrderIso _ _ (rank_lt q hR c) j).val ↔ i≤j
  rw [OrderIso.le_iff_le]
  exact (complementOrderIso _ _ (rank_lt q hR c)).le_iff_le

theorem complementEventOrderIso_val
    (i : Fin (Fintype.card (Event q)-((rightRank q hR c).val-(leftRank q hR c).val))) :
    (complementEventOrderIso q hR c i).val=complementEvents q hR c i := rfl

theorem complementEvent_successor (x : ComplementEvent q hR c) :
    letI := eventOrder q hR.noTriple
    (orderedCyclicSuccessor (ComplementEvent q hR c) x).val=incoming q hR.noTriple {c} x.val := by
  letI := eventOrder q hR.noTriple
  obtain ⟨i,rfl⟩ := (complementEventOrderIso q hR c).surjective x
  rw [orderedCyclicSuccessor_naturality,orderedCyclicSuccessor_fin]
  exact (complementEvents_step q hR c i).symm

/-- The actual piece-support pairing preserves the full singleton complement;
unretained crossing visits are fixed, not manufactured as parent crossings. -/
def complementEventPairing : Equiv.Perm (ComplementEvent q hR c) :=
  (pairing q (pieceSelections q hR c hc hcut S T)).subtypeEquiv (by
    have hf (x : Event q)
        (hx : (Nonalternation.eventEnumeration q hR).symm x∈complementSide (leftRank q hR c) (rightRank q hR c)) :
        (Nonalternation.eventEnumeration q hR).symm (pairing q (pieceSelections q hR c hc hcut S T) x)∈
          complementSide (leftRank q hR c) (rightRank q hR c) := by
      by_cases hr : retained q (insert c (pieceSelections q hR c hc hcut S T)) x
      · exact (complementRetainedPairing q hR c hc hcut S T ⟨x,hr,hx⟩).property.2
      · have hu : ¬retained q (pieceSelections q hR c hc hcut S T) x := by
          intro hh
          apply hr
          cases x with
          | inl i => trivial
          | inr v => exact Finset.mem_insert_of_mem hh
        rwa [pairing_fixes_nonretained q _ _ hu]
    intro x
    constructor
    · exact hf x
    · intro hx
      have hh := hf _ hx
      have he : pairing q (pieceSelections q hR c hc hcut S T)
          (pairing q (pieceSelections q hR c hc hcut S T) x)=x :=
        (pairing q (pieceSelections q hR c hc hcut S T)).left_inv x
      rwa [he] at hh)

def complementEventStart : ComplementEvent q hR c :=
  ⟨start q,(complementRetainedStart q hR c hc hcut S T).property.2⟩

theorem complementEvent_incoming (x : ComplementEvent q hR c) :
    letI := eventOrder q hR.noTriple
    ((orderedCyclicSuccessor (ComplementEvent q hR c) * complementEventPairing q hR c hc hcut S T) x).val=
      incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) x.val := by
  letI := eventOrder q hR.noTriple
  rw [Equiv.Perm.mul_apply,complementEvent_successor,incoming_pieceSelections_as_singleton]
  rfl

theorem complementEvent_orbitWord :
    letI := eventOrder q hR.noTriple
    orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) (start q)=
      (orbitWord (orderedCyclicSuccessor (ComplementEvent q hR c) *
        complementEventPairing q hR c hc hcut S T) (complementEventStart q hR c hc hcut S T)).map Subtype.val := by
  letI := eventOrder q hR.noTriple
  exact orbitWord_map_injective _ _ Subtype.val Subtype.val_injective
    (fun x => (complementEvent_incoming q hR c hc hcut S T x).symm)
    (complementEventStart q hR c hc hcut S T)

end DirectGLSSW.ActiveArc.CompatibleWords
