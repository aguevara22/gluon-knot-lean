import SM.ContactWindows
import SM.PairVisits

/-! The parameter windows contain exactly the actual visits belonging to the
two contact supports, on every nearby generic polygon. This exhausts every
visit rather than only a chosen list of persistent crossings. -/

namespace SM

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n} {M a : ZMod n} {r η : ℝ}

def InContactVisitWindow (M a : ZMod n) (r η : ℝ) {Q : LabelledTuple n}
    (v : Visit Q) : Prop :=
  ∃ slot : Option Bool, v.2.val = contactWindowEdge M a slot ∧
    |visitParameter v - contactWindowCenter r slot| < η

theorem contactAffected_iff_leg (s : Finset (ZMod n)) :
    ContactAffected M a s ↔ ∃ forward : Bool, s = {a, contactLeg forward M} := by
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨forward, hs⟩
    cases forward
    · exact Or.inl hs
    · exact Or.inr hs

theorem affected_visit_in_window (hn : 3 ≤ n) (hQ : G1 Q)
    (hw : ContactParameterWindows P Q M a r η) (v : Visit Q)
    (ha : ContactAffected M a v.1.val) : InContactVisitWindow M a r η v := by
  obtain ⟨forward, hs⟩ := (contactAffected_iff_leg _).mp ha
  have hm : v.2.val ∈ ({a, contactLeg forward M} : Finset (ZMod n)) := by
    simpa only [hs] using v.2.property
  rcases Finset.mem_insert.mp hm with he | he
  · have hp := visitParameter_eq_of_support_pair hn hQ v (contactLeg forward M)
      (by simpa only [he] using hs)
    rw [he] at hp
    refine ⟨none, he, ?_⟩
    change |visitParameter v - r| < η
    rw [hp]
    exact (hw.2.2 forward).1
  · have he : v.2.val = contactLeg forward M := Finset.mem_singleton.mp he
    have hp := visitParameter_eq_of_support_pair hn hQ v a
      (by simpa only [he, Finset.pair_comm] using hs)
    rw [he] at hp
    refine ⟨some forward, he, ?_⟩
    change |visitParameter v - contactEndpoint forward| < η
    rw [hp]
    exact (hw.2.2 forward).2

theorem unaffected_visit_outside_window (hn : 3 ≤ n) (hQ : G1 Q)
    (hw : ContactParameterWindows P Q M a r η) (v : Visit Q)
    (ha : ¬ ContactAffected M a v.1.val) (slot : Option Bool)
    (he : v.2.val = contactWindowEdge M a slot) :
    3 * η < |visitParameter v - contactWindowCenter r slot| := by
  obtain ⟨j, hji, hc, hv⟩ := visit_on_edge_pair v he
  subst v
  rw [pairVisit_parameter hn hQ]
  exact hw.2.1 slot j hc ha

theorem contact_visit_window_iff (hn : 3 ≤ n) (hQ : G1 Q) (hη : 0 < η)
    (hw : ContactParameterWindows P Q M a r η) (v : Visit Q) :
    InContactVisitWindow M a r η v ↔ ContactAffected M a v.1.val := by
  constructor
  · rintro ⟨slot, he, hp⟩
    by_contra ha
    have hout := unaffected_visit_outside_window hn hQ hw v ha slot he
    linarith
  · exact affected_visit_in_window hn hQ hw v

end SM
