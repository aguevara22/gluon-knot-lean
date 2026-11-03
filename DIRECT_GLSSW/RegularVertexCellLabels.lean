import RoundedStep

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate3: actual regular vertex degree identifies incoming corner labels. -/
theorem regular_vertex_incoming_unique (D : PLLinkDiagram) (v : Fin D.nVertex)
    (hnoncross : ∀ c, D.crossingVertex c ≠ v) (e f : Fin D.nArc)
    (he : D.arcTarget e = v) (hf : D.arcTarget f = v) : e = f := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (D.regular_degree_one v hnoncross).1
  have hemem : e ∈ incomingArcs D.arcTarget v := by simp [incomingArcs,he]
  have hfmem : f ∈ incomingArcs D.arcTarget v := by simp [incomingArcs,hf]
  have hea : e = a := by simpa only [ha,Finset.mem_singleton] using hemem
  have hfa : f = a := by simpa only [ha,Finset.mem_singleton] using hfmem
  exact hea.trans hfa.symm

/-- Aggregate Gate3: actual regular vertex degree identifies outgoing retained labels. -/
theorem regular_vertex_outgoing_unique (D : PLLinkDiagram) (v : Fin D.nVertex)
    (hnoncross : ∀ c, D.crossingVertex c ≠ v) (e f : Fin D.nArc)
    (he : D.arcSource e = v) (hf : D.arcSource f = v) : e = f := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (D.regular_degree_one v hnoncross).2
  have hemem : e ∈ outgoingArcs D.arcSource v := by simp [outgoingArcs,he]
  have hfmem : f ∈ outgoingArcs D.arcSource v := by simp [outgoingArcs,hf]
  have hea : e = a := by simpa only [ha,Finset.mem_singleton] using hemem
  have hfa : f = a := by simpa only [ha,Finset.mem_singleton] using hfmem
  exact hea.trans hfa.symm

end DirectGLSSW.HOMFLY.PrincipalTurning


