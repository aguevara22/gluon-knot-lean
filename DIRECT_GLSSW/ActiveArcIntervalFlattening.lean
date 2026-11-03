import ActiveArcIntervalCarrier

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

abbrev IntervalDoubleRetained := {x : IntervalEvent q hR c //
  retained q (insert c (pieceSelections q hR c hc hcut S T)) x.val}

def intervalFlattenOrderIso :
    letI := eventOrder q hR.noTriple
    IntervalDoubleRetained q hR c hc hcut S T ≃o IntervalRetained q hR c hc hcut S T := by
  letI := eventOrder q hR.noTriple
  exact
    { toFun := fun x => ⟨x.val.val,x.property,x.val.property⟩
      invFun := fun y => ⟨⟨y.val,y.property.2⟩,y.property.1⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_rel_iff' := by intro x y;rfl }

def intervalDoublePairing : Equiv.Perm (IntervalDoubleRetained q hR c hc hcut S T) := by
  letI := eventOrder q hR.noTriple
  exact (intervalFlattenOrderIso q hR c hc hcut S T).toEquiv.trans
    ((intervalRetainedPairing q hR c hc hcut S T).trans
      (intervalFlattenOrderIso q hR c hc hcut S T).symm.toEquiv)

theorem intervalDoublePairing_val (x : IntervalDoubleRetained q hR c hc hcut S T) :
    (intervalDoublePairing q hR c hc hcut S T x).val=
      intervalEventPairing q hR c hc hcut S T x.val := rfl

theorem intervalFlatten_pairing (x : IntervalDoubleRetained q hR c hc hcut S T) :
    intervalFlattenOrderIso q hR c hc hcut S T (intervalDoublePairing q hR c hc hcut S T x)=
      intervalRetainedPairing q hR c hc hcut S T (intervalFlattenOrderIso q hR c hc hcut S T x) := rfl

theorem intervalFlatten_incoming (x : IntervalDoubleRetained q hR c hc hcut S T) :
    letI := eventOrder q hR.noTriple
    (orderedCyclicSuccessor (IntervalRetained q hR c hc hcut S T) *
      intervalRetainedPairing q hR c hc hcut S T) (intervalFlattenOrderIso q hR c hc hcut S T x)=
      intervalFlattenOrderIso q hR c hc hcut S T
        ((orderedCyclicSuccessor (IntervalDoubleRetained q hR c hc hcut S T) *
          intervalDoublePairing q hR c hc hcut S T) x) := by
  letI := eventOrder q hR.noTriple
  rw [Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,← intervalFlatten_pairing]
  exact orderedCyclicSuccessor_naturality _ (intervalFlattenOrderIso q hR c hc hcut S T) _

theorem intervalFlatten_orbitWord (x : IntervalDoubleRetained q hR c hc hcut S T) :
    letI := eventOrder q hR.noTriple
    orbitWord (orderedCyclicSuccessor (IntervalRetained q hR c hc hcut S T) *
      intervalRetainedPairing q hR c hc hcut S T) (intervalFlattenOrderIso q hR c hc hcut S T x)=
      (orbitWord (orderedCyclicSuccessor (IntervalDoubleRetained q hR c hc hcut S T) *
        intervalDoublePairing q hR c hc hcut S T) x).map (intervalFlattenOrderIso q hR c hc hcut S T) := by
  letI := eventOrder q hR.noTriple
  exact orbitWord_map_injective _ _ (intervalFlattenOrderIso q hR c hc hcut S T)
    (intervalFlattenOrderIso q hR c hc hcut S T).injective
    (intervalFlatten_incoming q hR c hc hcut S T) x

theorem intervalEventPairing_fixes_nonretained (x : IntervalEvent q hR c)
    (hx : ¬retained q (insert c (pieceSelections q hR c hc hcut S T)) x.val) :
    intervalEventPairing q hR c hc hcut S T x=x := by
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
