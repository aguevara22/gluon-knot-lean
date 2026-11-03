import UniformPLComponent

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Distinct actual arc sources coincide only at a crossing, and are the two
actual outgoing through-branches. No incidence certificate is a premise. -/
theorem actual_distinct_sources_crossing (D : PLLinkDiagram) (a b : Fin D.nArc)
    (hab : a ≠ b) (hs : D.arcSource a = D.arcSource b) :
    ∃ c : Fin D.nCrossing, ∃ i j : Fin 2, i ≠ j ∧
      a = D.outgoing c (D.through c i) ∧ b = D.outgoing c (D.through c j) := by
  classical
  have hc : ∃ c, D.crossingVertex c = D.arcSource a := by
    by_contra hn
    have hr : ∀ c, D.crossingVertex c ≠ D.arcSource a := by simpa only [not_exists] using hn
    obtain ⟨e,he⟩ := Finset.card_eq_one.mp (D.regular_degree_one (D.arcSource a) hr).2
    have ha : a ∈ outgoingArcs D.arcSource (D.arcSource a) := by simp [outgoingArcs]
    have hb : b ∈ outgoingArcs D.arcSource (D.arcSource a) := by simp [outgoingArcs,hs]
    rw [he,Finset.mem_singleton] at ha hb
    exact hab (ha.trans hb.symm)
  obtain ⟨c,hc⟩ := hc
  have out (f : Fin D.nArc) (hf : D.arcSource f = D.crossingVertex c) :
      ∃ i : Fin 2, f = D.outgoing c (D.through c i) := by
    have hports := (D.crossing_incidence_complete c f).mp (Or.inl hf)
    have notinc (i : Fin 2) (hi : f=D.incoming c i) : False := by
      have hin : D.arcSource (D.incoming c i) = D.crossingVertex c := by simpa only [hi] using hf
      exact D.arc_endpoints_distinct _ (hin.trans (D.incoming_target c i).symm)
    rcases hports with h | h | h | h
    · exact False.elim (notinc 0 h)
    · exact False.elim (notinc 1 h)
    · refine ⟨(D.through c).symm 0,?_⟩
      simpa only [Equiv.apply_symm_apply] using h
    · refine ⟨(D.through c).symm 1,?_⟩
      simpa only [Equiv.apply_symm_apply] using h
  obtain ⟨i,hi⟩ := out a hc.symm
  obtain ⟨j,hj⟩ := out b (hs.symm.trans hc.symm)
  refine ⟨c,i,j,?_,hi,hj⟩
  intro hij
  rw [hij] at hi
  exact hab (hi.trans hj.symm)

end DirectGLSSW.HOMFLY.PrincipalTurning

