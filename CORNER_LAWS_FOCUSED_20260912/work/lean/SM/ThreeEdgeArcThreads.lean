import SM.ThreeEdgeCrossingArc

/-! A thread visit in the actual short arc forces its actual paired visit
into the complementary open arc. No emptiness assumption is introduced. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {f : ZMod n}

theorem twoStepFirstVisit_ne_last (h : IsCrossing P {f, f + 2}) :
    twoStepFirstVisit h ≠ twoStepLastVisit h := by
  intro he
  have hv := congrArg (fun v : Visit P => v.2.val) he
  exact (remote_endpoints f (f + 2) (crossing_pair_remote h)).1 hv.symm

theorem twoStepArc_partner_complement (hn : 3 ≤ n) (hP : Generic P)
    (h : IsCrossing P {f, f + 2}) (c : Crossing P) (hc : c.val ≠ {f, f + 2})
    (i k : {l // l ∈ c.val}) (hik : i ≠ k)
    (hi : twoStepOpenArc hn hP.1 h (visitPosition hn hP.1 ⟨c, i⟩)) :
    traversalBetween (visitPosition hn hP.1 (twoStepLastVisit h))
      (visitPosition hn hP.1 ⟨c, k⟩) (visitPosition hn hP.1 (twoStepFirstVisit h)) := by
  have hlast : visitPosition hn hP.1 (twoStepLastVisit h) ≠ visitPosition hn hP.1 ⟨c, k⟩ := by
    intro he
    have hv := congrArg (fun v : Visit P => v.1.val) (visitPosition_injective hn hP he)
    exact hc hv.symm
  have hfirst : visitPosition hn hP.1 ⟨c, k⟩ ≠ visitPosition hn hP.1 (twoStepFirstVisit h) := by
    intro he
    have hv := congrArg (fun v : Visit P => v.1.val) (visitPosition_injective hn hP he)
    exact hc hv
  have hend : visitPosition hn hP.1 (twoStepFirstVisit h) ≠
      visitPosition hn hP.1 (twoStepLastVisit h) :=
    fun he => twoStepFirstVisit_ne_last h (visitPosition_injective hn hP he)
  apply (traversalBetween_complement hlast hfirst hend).mpr
  intro hk
  exact hc (twoStepArc_no_other_double_visit hn hP.1 h c i k hik hi hk)

theorem twoStepArc_visit_partner (hn : 3 ≤ n) (hP : Generic P)
    (h : IsCrossing P {f, f + 2}) (v : Visit P) (hc : v.1.val ≠ {f, f + 2})
    (hv : twoStepOpenArc hn hP.1 h (visitPosition hn hP.1 v)) :
    ∃ w : Visit P, w.1 = v.1 ∧ w ≠ v ∧
      traversalBetween (visitPosition hn hP.1 (twoStepLastVisit h))
        (visitPosition hn hP.1 w) (visitPosition hn hP.1 (twoStepFirstVisit h)) := by
  rcases v with ⟨c, i⟩
  obtain ⟨k, hki⟩ := crossing_other_visit c i
  refine ⟨⟨c, k⟩, rfl, ?_, twoStepArc_partner_complement hn hP h c hc i k hki.symm hv⟩
  intro he
  exact hki (eq_of_heq (Sigma.mk.inj_iff.mp he).2)

end SM
