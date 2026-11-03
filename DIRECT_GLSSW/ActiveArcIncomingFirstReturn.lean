import ActiveArcPhysicalWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.RetainedWords
open PhysicalSegments
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- Until a retained return, incoming smoothing is the ordinary physical
successor starting at the paired outgoing branch. This uses incoming convention. -/
theorem incoming_iterate_from_paired (x : Event q) (d : ℕ)
    (hno : ∀ j : ℕ, 0<j → j<d →
      ¬retained q S ((successor q hR.noTriple ^ j) (pairing q S x)))
    (k : ℕ) (hk : 0<k) (hkd : k≤d) :
    (incoming q hR.noTriple S ^ k) x=(successor q hR.noTriple ^ k) (pairing q S x) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k=0
    · subst k;rfl
    · have hp : 0<k := Nat.pos_of_ne_zero hk0
      have he := ih hp (by omega)
      have hn := hno k hp (by omega)
      rw [pow_succ',Equiv.Perm.mul_apply,he]
      change successor q hR.noTriple (pairing q S ((successor q hR.noTriple ^ k) (pairing q S x)))=_
      rw [pairing_fixes_nonretained q S _ hn,pow_succ',Equiv.Perm.mul_apply]

/-- Native incoming first-return characterization. A proved ordinary-successor
return from the paired branch determines the exact retained next corner. -/
theorem nextCorner_of_successor_firstReturn (root : Event q) (c : Corner q hR S root)
    (d : ℕ) (hd : 0<d)
    (hret : retained q S ((successor q hR.noTriple ^ d)
      (pairing q S (eventAt q hR S root c.val))))
    (hno : ∀ j : ℕ, 0<j → j<d → ¬retained q S ((successor q hR.noTriple ^ j)
      (pairing q S (eventAt q hR S root c.val)))) :
    eventAt q hR S root (nextCorner q hR S root c).val=
      (successor q hR.noTriple ^ d) (pairing q S (eventAt q hR S root c.val)) := by
  have hf := corner_firstReturn q hR S root c
  have heq : d=cornerGap q hR S root c := by
    rcases lt_trichotomy d (cornerGap q hR S root c) with hlt|he|hlt
    · have hn := hf.2.2 d hd hlt
      rw [incoming_iterate_from_paired q hR S _ d hno d hd le_rfl] at hn
      exact False.elim (hn hret)
    · exact he
    · have hn := hno (cornerGap q hR S root c) hf.1 hlt
      have hp := incoming_iterate_from_paired q hR S _ d hno (cornerGap q hR S root c) hf.1 (le_of_lt hlt)
      rw [← hp,hf.2.1] at hn
      exact False.elim (hn (nextCorner q hR S root c).property)
  have hp := incoming_iterate_from_paired q hR S _ d hno d hd le_rfl
  rw [heq,hf.2.1] at hp
  simpa only [heq] using hp

end DirectGLSSW.ActiveArc.RetainedWords
