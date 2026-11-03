import ActiveArcRetainedGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.RetainedWords
open DirectGLSSW ActiveArc PhysicalSegments PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- Every retained vertex is an actual anchor or the unique point of a selected physical crossing. -/
theorem vertex_physical_characterization (root : Event q)
    (i : Fin (Fintype.card (Corner q hR S root))) :
    (∃ j : Fin (n+2), cornerEvent q hR S root i=Sum.inl j ∧ vertex q hR S root i=q j) ∨
    (∃ c : Crossing q, ∃ b : Bool, cornerEvent q hR S root i=Sum.inr (c,b) ∧ c∈S ∧
      edgeInterior q c.val.1 (vertex q hR S root i) ∧
      edgeInterior q c.val.2 (vertex q hR S root i) ∧
      ∀ x : PlanarPoint ℝ, edgeInterior q c.val.1 x → edgeInterior q c.val.2 x →
        vertex q hR S root i=x) := by
  have hr : retained q S (cornerEvent q hR S root i) := (enumeration q hR S root i).property
  generalize he : cornerEvent q hR S root i=z at hr
  cases z with
  | inl j =>
    left
    exact ⟨j,rfl,by rw [vertex,he];rfl⟩
  | inr v =>
    right
    refine ⟨v.1,v.2,rfl,hr,?_,?_,?_⟩
    · simpa only [vertex,he,eventPoint] using (crossingPoint_mem q v.1).1
    · simpa only [vertex,he,eventPoint] using (crossingPoint_mem q v.1).2
    · intro x hl hh
      rw [vertex,he]
      exact visitPoint_eq_of_intersection q hR v x hl hh

theorem cornerEvent_injective (root : Event q) : Function.Injective (cornerEvent q hR S root) := by
  intro i j hh
  apply (enumeration q hR S root).injective
  apply Subtype.ext
  apply (orbitEnumeration (incoming q hR.noTriple S) root).injective
  apply Subtype.ext
  exact hh

theorem enumeration_cyclic (root : Event q)
    (i : Fin (Fintype.card (Corner q hR S root))) :
    enumeration q hR S root (cyclicSuccessor i)=
      nextCorner q hR S root (enumeration q hR S root i) := by
  classical
  simp [enumeration,nextCorner,orderedCyclicSuccessor_apply]

theorem open_nonlast_ne_terminal (i : Fin (openCount q hR S))
    (hi : i.val+1<openCount q hR S) : cornerEvent q hR S (start q) i≠terminal q := by
  intro hh
  have he := cornerEvent_injective q hR S (start q)
    (hh.trans (open_cornerEvent_last q hR S).symm)
  have hev := congrArg Fin.val he
  change i.val=openCount q hR S-1 at hev
  omega

/-- Every consecutive side of the retained OPEN word follows a positive physical subsegment.
There is no statement about a last-to-first edge. -/
theorem open_vertex_side_physical (i : Fin (openCount q hR S))
    (hi : i.val+1<openCount q hR S) :
    ∃ e : Fin (n+1), ∃ a b : ℝ, 0≤a ∧ a<b ∧ b≤1 ∧
      vertex q hR S (start q) i=affinePoint (q e.castSucc) (q e.succ) a ∧
      vertex q hR S (start q) ⟨i.val+1,hi⟩=affinePoint (q e.castSucc) (q e.succ) b ∧
      ∀ t : ℝ, vertex q hR S (start q) ⟨i.val+1,hi⟩=affinePoint (q e.castSucc) (q e.succ) t → t=b := by
  let c := enumeration q hR S (start q) i
  have hx := open_nonlast_ne_terminal q hR S i hi
  obtain ⟨a,b,ha,hab,hb,hpoint,hnext,hunique⟩ :=
    retained_side_physical q hR S (start q) c hx
  have hs : cyclicSuccessor i=⟨i.val+1,hi⟩ := by
    apply Fin.ext
    simp only [cyclicSuccessor,cyclicVertexIndex,Nat.add_zero]
    exact Nat.mod_eq_of_lt hi
  have he := enumeration_cyclic q hR S (start q) i
  rw [hs] at he
  have hev : eventAt q hR S (start q) (nextCorner q hR S (start q) c).val=
      cornerEvent q hR S (start q) ⟨i.val+1,hi⟩ := by rw [← he];rfl
  rw [hev] at hnext hunique
  exact ⟨outgoingEdge q S (eventAt q hR S (start q) c.val) hx,a,b,ha,hab,hb,hpoint,hnext,hunique⟩

/-- Closed retained corners lie in their actual closed orbit, so the endpoint seam is absent. -/
theorem closed_corner_ne_terminal (C : Component (incoming q hR.noTriple S))
    (hc : C≠openComponent q hR.noTriple S)
    (i : Fin (Fintype.card (Corner q hR S (closedRoot q hR.noTriple S C hc)))) :
    cornerEvent q hR S (closedRoot q hR.noTriple S C hc) i≠terminal q := by
  let r := closedRoot q hR.noTriple S C hc
  have hh : componentOf (incoming q hR.noTriple S) (cornerEvent q hR S r i)=C :=
    (orbitEnumeration (incoming q hR.noTriple S) r (enumeration q hR S r i).val).property.trans
      (closedRoot_spec q hR.noTriple S C hc).1
  exact (closedComponent_avoids_endpoints q hR.noTriple S C hc ⟨_,hh⟩).2

/-- Every cyclic side of a retained CLOSED word follows a physical edge, including its wrap. -/
theorem closed_vertex_side_physical (C : Component (incoming q hR.noTriple S))
    (hc : C≠openComponent q hR.noTriple S)
    (i : Fin (Fintype.card (Corner q hR S (closedRoot q hR.noTriple S C hc)))) :
    ∃ e : Fin (n+1), ∃ a b : ℝ, 0≤a ∧ a<b ∧ b≤1 ∧
      vertex q hR S (closedRoot q hR.noTriple S C hc) i=affinePoint (q e.castSucc) (q e.succ) a ∧
      vertex q hR S (closedRoot q hR.noTriple S C hc) (cyclicSuccessor i)=
        affinePoint (q e.castSucc) (q e.succ) b ∧
      ∀ t : ℝ, vertex q hR S (closedRoot q hR.noTriple S C hc) (cyclicSuccessor i)=
        affinePoint (q e.castSucc) (q e.succ) t → t=b := by
  let r := closedRoot q hR.noTriple S C hc
  let c := enumeration q hR S r i
  have hx := closed_corner_ne_terminal q hR S C hc i
  obtain ⟨a,b,ha,hab,hb,hpoint,hnext,hunique⟩ := retained_side_physical q hR S r c hx
  have he := enumeration_cyclic q hR S r i
  have hev : eventAt q hR S r (nextCorner q hR S r c).val=
      cornerEvent q hR S r (cyclicSuccessor i) := by rw [← he];rfl
  rw [hev] at hnext hunique
  exact ⟨outgoingEdge q S (eventAt q hR S r c.val) hx,a,b,ha,hab,hb,hpoint,hnext,hunique⟩

end DirectGLSSW.ActiveArc.RetainedWords
