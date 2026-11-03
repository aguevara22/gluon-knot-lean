import ActiveArcComplementCarrier

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

abbrev ComplementDoubleRetained := {x : ComplementEvent q hR c //
  retained q (insert c (pieceSelections q hR c hc hcut S T)) x.val}

def complementFlattenOrderIso :
    letI := eventOrder q hR.noTriple
    ComplementDoubleRetained q hR c hc hcut S T ≃o ComplementRetained q hR c hc hcut S T := by
  letI := eventOrder q hR.noTriple
  exact
    { toFun := fun x => ⟨x.val.val,x.property,x.val.property⟩
      invFun := fun y => ⟨⟨y.val,y.property.2⟩,y.property.1⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_rel_iff' := by intro x y;rfl }

def complementDoublePairing : Equiv.Perm (ComplementDoubleRetained q hR c hc hcut S T) := by
  letI := eventOrder q hR.noTriple
  exact (complementFlattenOrderIso q hR c hc hcut S T).toEquiv.trans
    ((complementRetainedPairing q hR c hc hcut S T).trans
      (complementFlattenOrderIso q hR c hc hcut S T).symm.toEquiv)

theorem complementDoublePairing_val (x : ComplementDoubleRetained q hR c hc hcut S T) :
    (complementDoublePairing q hR c hc hcut S T x).val=
      complementEventPairing q hR c hc hcut S T x.val := rfl

theorem complementFlatten_pairing (x : ComplementDoubleRetained q hR c hc hcut S T) :
    complementFlattenOrderIso q hR c hc hcut S T (complementDoublePairing q hR c hc hcut S T x)=
      complementRetainedPairing q hR c hc hcut S T (complementFlattenOrderIso q hR c hc hcut S T x) := rfl

theorem complementFlatten_incoming (x : ComplementDoubleRetained q hR c hc hcut S T) :
    letI := eventOrder q hR.noTriple
    (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
      complementRetainedPairing q hR c hc hcut S T) (complementFlattenOrderIso q hR c hc hcut S T x)=
      complementFlattenOrderIso q hR c hc hcut S T
        ((orderedCyclicSuccessor (ComplementDoubleRetained q hR c hc hcut S T) *
          complementDoublePairing q hR c hc hcut S T) x) := by
  letI := eventOrder q hR.noTriple
  rw [Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,← complementFlatten_pairing]
  exact orderedCyclicSuccessor_naturality _ (complementFlattenOrderIso q hR c hc hcut S T) _

theorem complementFlatten_orbitWord (x : ComplementDoubleRetained q hR c hc hcut S T) :
    letI := eventOrder q hR.noTriple
    orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
      complementRetainedPairing q hR c hc hcut S T) (complementFlattenOrderIso q hR c hc hcut S T x)=
      (orbitWord (orderedCyclicSuccessor (ComplementDoubleRetained q hR c hc hcut S T) *
        complementDoublePairing q hR c hc hcut S T) x).map (complementFlattenOrderIso q hR c hc hcut S T) := by
  letI := eventOrder q hR.noTriple
  exact orbitWord_map_injective _ _ (complementFlattenOrderIso q hR c hc hcut S T)
    (complementFlattenOrderIso q hR c hc hcut S T).injective
    (complementFlatten_incoming q hR c hc hcut S T) x

theorem complementEventPairing_fixes_nonretained (x : ComplementEvent q hR c)
    (hx : ¬retained q (insert c (pieceSelections q hR c hc hcut S T)) x.val) :
    complementEventPairing q hR c hc hcut S T x=x := by
  apply Subtype.ext
  apply pairing_fixes_nonretained
  intro hr
  apply hx
  cases he : x.val with
  | inl i => trivial
  | inr v =>
    rw [he] at hr
    exact Finset.mem_insert_of_mem hr

end DirectGLSSW.ActiveArc.CompatibleWords
