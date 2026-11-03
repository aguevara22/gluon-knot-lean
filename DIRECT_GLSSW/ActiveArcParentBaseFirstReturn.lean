import ActiveArcParentRetainedEquiv
import ActiveArcIncomingFirstReturn

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords PhysicalSegments
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- The exact source smoothing factors through the actual singleton base
permutation. In particular the cut's left-to-right transition is included. -/
theorem incoming_pieceSelections_as_singleton :
    incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))=
      incoming q hR.noTriple {c} * pairing q (pieceSelections q hR c hc hcut S T) := by
  have hn : c∉pieceSelections q hR c hc hcut S T := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut _).mp ⟨S,T,rfl⟩ c hh).1 rfl
  ext x
  change successor q hR.noTriple (pairing q (insert c (pieceSelections q hR c hc hcut S T)) x)=
    successor q hR.noTriple (pairing q {c} (pairing q (pieceSelections q hR c hc hcut S T) x))
  rw [Nonalternation.pairing_insert q _ c hn]
  rfl

/-- Before the first retained return, the actual incoming trajectory follows
the singleton complement successor from the support-paired branch. -/
theorem incoming_pieceSelections_iterate (x : Event q) (d : ℕ)
    (hno : ∀ j : ℕ, 0<j → j<d →
      ¬retained q (insert c (pieceSelections q hR c hc hcut S T))
        ((incoming q hR.noTriple {c} ^ j) (pairing q (pieceSelections q hR c hc hcut S T) x)))
    (k : ℕ) (hk : 0<k) (hkd : k≤d) :
    (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) ^ k) x=
      (incoming q hR.noTriple {c} ^ k) (pairing q (pieceSelections q hR c hc hcut S T) x) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k=0
    · subst k
      simp only [Nat.zero_add,pow_one,incoming_pieceSelections_as_singleton,Equiv.Perm.mul_apply]
    · have hp : 0<k := Nat.pos_of_ne_zero hk0
      have he := ih hp (by omega)
      have hn := hno k hp (by omega)
      have hn' : ¬retained q (pieceSelections q hR c hc hcut S T)
          ((incoming q hR.noTriple {c} ^ k) (pairing q (pieceSelections q hR c hc hcut S T) x)) := by
        intro hr
        apply hn
        generalize (incoming q hR.noTriple {c} ^ k) (pairing q (pieceSelections q hR c hc hcut S T) x)=z at hr ⊢
        cases z with
        | inl i => trivial
        | inr v => exact Finset.mem_insert_of_mem hr
      rw [pow_succ',Equiv.Perm.mul_apply,he,incoming_pieceSelections_as_singleton,
        Equiv.Perm.mul_apply,pairing_fixes_nonretained q _ _ hn',pow_succ',Equiv.Perm.mul_apply]

/-- A proved singleton-base first return determines the actual source next
corner. This internal characterization does not assume daughter-word equality. -/
theorem nextCorner_of_singleton_firstReturn (root : Event q)
    (z : Corner q hR (insert c (pieceSelections q hR c hc hcut S T)) root)
    (d : ℕ) (hd : 0<d)
    (hret : retained q (insert c (pieceSelections q hR c hc hcut S T))
      ((incoming q hR.noTriple {c} ^ d) (pairing q (pieceSelections q hR c hc hcut S T)
        (eventAt q hR (insert c (pieceSelections q hR c hc hcut S T)) root z.val))))
    (hno : ∀ j : ℕ, 0<j → j<d →
      ¬retained q (insert c (pieceSelections q hR c hc hcut S T))
        ((incoming q hR.noTriple {c} ^ j) (pairing q (pieceSelections q hR c hc hcut S T)
          (eventAt q hR (insert c (pieceSelections q hR c hc hcut S T)) root z.val)))) :
    eventAt q hR (insert c (pieceSelections q hR c hc hcut S T)) root
        (nextCorner q hR (insert c (pieceSelections q hR c hc hcut S T)) root z).val=
      (incoming q hR.noTriple {c} ^ d) (pairing q (pieceSelections q hR c hc hcut S T)
        (eventAt q hR (insert c (pieceSelections q hR c hc hcut S T)) root z.val)) := by
  have hf := corner_firstReturn q hR (insert c (pieceSelections q hR c hc hcut S T)) root z
  have heq : d=cornerGap q hR (insert c (pieceSelections q hR c hc hcut S T)) root z := by
    rcases lt_trichotomy d (cornerGap q hR (insert c (pieceSelections q hR c hc hcut S T)) root z) with hlt|he|hlt
    · have hn := hf.2.2 d hd hlt
      rw [incoming_pieceSelections_iterate q hR c hc hcut S T _ d hno d hd le_rfl] at hn
      exact False.elim (hn hret)
    · exact he
    · have hn := hno _ hf.1 hlt
      have hp := incoming_pieceSelections_iterate q hR c hc hcut S T _ d hno _ hf.1 (le_of_lt hlt)
      rw [← hp,hf.2.1] at hn
      exact False.elim (hn (nextCorner q hR (insert c (pieceSelections q hR c hc hcut S T)) root z).property)
  have hp := incoming_pieceSelections_iterate q hR c hc hcut S T _ d hno d hd le_rfl
  rw [heq,hf.2.1] at hp
  simpa only [heq] using hp

end DirectGLSSW.ActiveArc.CompatibleWords
