import ActiveArcChildRootWords
import ActiveArcParentClosedWords
import DirectGLSSW.PermutationSplitJoin

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable

/-- Undoing one selected physical cut is the actual right multiplication
by the swap of its two incoming visits. -/
theorem incoming_unselected_eq_swap {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hR : Regular q) (c : Crossing q) (U : Finset (Crossing q)) (hu : c ∉ U) :
    incoming q hR.noTriple U = incoming q hR.noTriple (insert c U) *
      (@Equiv.swap (Event q) (Classical.decEq _) (Sum.inr (c,false)) (Sum.inr (c,true))) := by
  ext x
  cases x with
  | inl i => simp [incoming,pairing,pairingMap,Equiv.swap_apply_def]
  | inr v =>
    rcases v with ⟨d,b⟩
    by_cases hd : d=c
    · subst d
      cases b <;> simp [incoming,pairing,pairingMap,Equiv.swap_apply_def,hu]
    · have h0 : (Sum.inr (d,b) : Event q) ≠ Sum.inr (c,false) :=
        fun he => hd (congrArg Prod.fst (Sum.inr.inj he))
      have h1 : (Sum.inr (d,b) : Event q) ≠ Sum.inr (c,true) :=
        fun he => hd (congrArg Prod.fst (Sum.inr.inj he))
      change successor q hR.noTriple (pairing q U (Sum.inr (d,b))) =
        successor q hR.noTriple (pairing q (insert c U)
          ((@Equiv.swap (Event q) (Classical.decEq _) (Sum.inr (c,false)) (Sum.inr (c,true))) (Sum.inr (d,b))))
      rw [@Equiv.swap_apply_of_ne_of_ne (Event q) (Classical.decEq _)
        (Sum.inr (c,false)) (Sum.inr (c,true)) (Sum.inr (d,b)) h0 h1]
      congr 1
      simp only [pairing,pairingMap,Equiv.coe_fn_mk,Finset.mem_insert,hd,false_or]

/-- The two cut visits are the only retained labels deleted when the cut is
unselected. This equivalence is on event labels, before taking point values. -/
theorem retained_unselected_iff {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (c : Crossing q) (U : Finset (Crossing q)) (hu : c ∉ U) (x : Event q) :
    retained q U x ↔ retained q (insert c U) x ∧
      x ≠ Sum.inr (c,false) ∧ x ≠ Sum.inr (c,true) := by
  cases x with
  | inl i => simp [retained]
  | inr v =>
    rcases v with ⟨d,b⟩
    by_cases hd : d=c
    · subst d
      cases b <;> simp [retained,hu]
    · have h0 : (Sum.inr (d,b) : Event q) ≠ Sum.inr (c,false) :=
        fun he => hd (congrArg Prod.fst (Sum.inr.inj he))
      have h1 : (Sum.inr (d,b) : Event q) ≠ Sum.inr (c,true) :=
        fun he => hd (congrArg Prod.fst (Sum.inr.inj he))
      constructor
      · intro hU
        refine ⟨?_,h0,h1⟩
        exact Finset.mem_insert_of_mem hU
      · intro hU
        exact (Finset.mem_insert.mp hU.1).resolve_left hd

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
include hc

/-- First-crossing minimality determines the full physical event successor
of the initial anchor, before any retained-label deletion. -/
theorem successor_start_first : successor q hR.noTriple (start q) = Sum.inr (c,false) := by
  letI := eventOrder q hR.noTriple
  letI : LinearOrder (Fin (a+b+2) ⊕ Visit q) := eventOrder q hR.noTriple
  apply orderedCyclicSuccessor_eq_of_order_spec
  left
  constructor
  · apply (event_lt_iff q hR.noTriple _ _).mpr
    right
    exact ⟨by simp [start,edgeTag,visitEdge,hc.1],(leftParameter_spec q c).1⟩
  · intro z hz
    cases z with
    | inl i =>
      have hi : i≠0 := by
        intro he
        subst i
        exact lt_irrefl (start q) hz
      apply le_of_lt
      apply (event_lt_iff q hR.noTriple _ _).mpr
      left
      simpa only [edgeTag,visitEdge,Bool.false_eq_true,↓reduceIte,hc.1,Fin.val_zero] using
        Fin.pos_iff_ne_zero.mpr hi
    | inr v =>
      rcases v with ⟨d,z⟩
      have hd : (Sum.inr (c,false) : Event q) ≤ (Sum.inr (d,false) : Event q) := by
        by_cases he : d=c
        · subst d;exact le_rfl
        · exact (first_left_lt_other_left q hR c hc d he).le
      cases z
      · exact hd
      · exact le_trans hd (left_visit_lt_right q hR d).le

/-- Smoothing fixes anchors, so every actual selected or unselected support
has the same first full-event step from the moving mark. -/
theorem incoming_start_first (U : Finset (Crossing q)) :
    incoming q hR.noTriple U (start q) = Sum.inr (c,false) :=
  successor_start_first q hR c hc

end DirectGLSSW.ActiveArc.CompatibleWords
