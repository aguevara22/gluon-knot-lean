import ActiveArcChildReducedPairing
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

abbrev IntervalEvent := {x : Event q // (Nonalternation.eventEnumeration q hR).symm x ∈
  intervalSide (leftRank q hR c) (rightRank q hR c)}

def intervalEventOrderIso :
    letI := eventOrder q hR.noTriple
    Fin ((rightRank q hR c).val-(leftRank q hR c).val) ≃o
      IntervalEvent q hR c := by
  letI := eventOrder q hR.noTriple
  let e := Nonalternation.eventEnumeration q hR
  let F : intervalSide (leftRank q hR c) (rightRank q hR c) ≃ IntervalEvent q hR c :=
    e.subtypeEquiv (by
      intro i
      change i∈intervalSide (leftRank q hR c) (rightRank q hR c) ↔
        e.symm (e i)∈intervalSide (leftRank q hR c) (rightRank q hR c)
      rw [Equiv.symm_apply_apply])
  refine { toEquiv := (intervalOrderIso _ _ (rank_lt q hR c)).toEquiv.trans F
           map_rel_iff' := ?_ }
  intro i j
  change Nonalternation.eventOrderIso q hR (intervalOrderIso _ _ (rank_lt q hR c) i).val≤
    Nonalternation.eventOrderIso q hR (intervalOrderIso _ _ (rank_lt q hR c) j).val ↔ i≤j
  rw [OrderIso.le_iff_le]
  exact (intervalOrderIso _ _ (rank_lt q hR c)).le_iff_le

theorem intervalEventOrderIso_val
    (i : Fin ((rightRank q hR c).val-(leftRank q hR c).val)) :
    (intervalEventOrderIso q hR c i).val=intervalEvents q hR c i := rfl

theorem intervalEvent_successor (x : IntervalEvent q hR c) :
    letI := eventOrder q hR.noTriple
    (orderedCyclicSuccessor (IntervalEvent q hR c) x).val=incoming q hR.noTriple {c} x.val := by
  letI := eventOrder q hR.noTriple
  obtain ⟨i,rfl⟩ := (intervalEventOrderIso q hR c).surjective x
  rw [orderedCyclicSuccessor_naturality,orderedCyclicSuccessor_fin]
  exact (intervalEvents_step q hR c i).symm

/-- The actual piece-support pairing preserves the full singleton interval;
unretained crossing visits are fixed, not manufactured as parent crossings. -/
def intervalEventPairing : Equiv.Perm (IntervalEvent q hR c) :=
  (pairing q (pieceSelections q hR c hc hcut S T)).subtypeEquiv (by
    have hf (x : Event q)
        (hx : (Nonalternation.eventEnumeration q hR).symm x∈intervalSide (leftRank q hR c) (rightRank q hR c)) :
        (Nonalternation.eventEnumeration q hR).symm (pairing q (pieceSelections q hR c hc hcut S T) x)∈
          intervalSide (leftRank q hR c) (rightRank q hR c) := by
      by_cases hr : retained q (insert c (pieceSelections q hR c hc hcut S T)) x
      · exact (intervalRetainedPairing q hR c hc hcut S T ⟨x,hr,hx⟩).property.2
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

theorem intervalEvent_incoming (x : IntervalEvent q hR c) :
    letI := eventOrder q hR.noTriple
    ((orderedCyclicSuccessor (IntervalEvent q hR c) * intervalEventPairing q hR c hc hcut S T) x).val=
      incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) x.val := by
  letI := eventOrder q hR.noTriple
  rw [Equiv.Perm.mul_apply,intervalEvent_successor,incoming_pieceSelections_as_singleton]
  rfl

theorem intervalEvent_orbitWord (x : IntervalEvent q hR c) :
    letI := eventOrder q hR.noTriple
    orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) x.val=
      (orbitWord (orderedCyclicSuccessor (IntervalEvent q hR c) *
        intervalEventPairing q hR c hc hcut S T) x).map Subtype.val := by
  letI := eventOrder q hR.noTriple
  exact orbitWord_map_injective _ _ Subtype.val Subtype.val_injective
    (fun x => (intervalEvent_incoming q hR c hc hcut S T x).symm) x

end DirectGLSSW.ActiveArc.CompatibleWords
