import ActiveArcOpenSideGeometry
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc PhysicalSegments RetainedWords
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- The final retained physical side is on the original final edge. -/
theorem openSideCarrier_last :
    openSideCarrier q hR S ⟨openCount q hR S-2,by have := open_count_ge_two q hR S; omega⟩ = ⟨n,by omega⟩ := by
  letI := eventOrder q hR.noTriple
  have hm := open_count_ge_two q hR S
  let i : Fin (openCount q hR S) := ⟨openCount q hR S-2,by omega⟩
  have hi : i.val+1<openCount q hR S := by dsimp [i]; omega
  let d := enumeration q hR S (start q) i
  have hx : eventAt q hR S (start q) d.val ≠ terminal q := open_nonlast_ne_terminal q hR S i hi
  have hf := corner_firstReturn q hR S (start q) d
  have hb := firstReturn_prefix_bounded q hR S (eventAt q hR S (start q) d.val) hx _ hf.2.2 _ hf.1 le_rfl
  rw [hf.2.1] at hb
  have hs : cyclicSuccessor i=openLast q hR S := by
    apply Fin.ext
    change (i.val+1) % openCount q hR S = openCount q hR S-1
    rw [Nat.mod_eq_of_lt hi]
    dsimp [i]; omega
  have he := enumeration_cyclic q hR S (start q) i
  rw [hs] at he
  have ht : eventAt q hR S (start q) (nextCorner q hR S (start q) d).val=terminal q := by
    rw [← he]
    exact open_cornerEvent_last q hR S
  rw [ht] at hb
  apply Fin.ext
  change (outgoingEdge q S (eventAt q hR S (start q) d.val) hx).val = n
  let e := outgoingEdge q S (eventAt q hR S (start q) d.val) hx
  have heb := e.isLt
  by_contra hne
  have hlt : (eventOrder q hR.noTriple).lt (Sum.inl e.succ) (terminal q) := by
    apply (event_lt_iff q hR.noTriple _ _).mpr
    left
    change e.val+1<n+1
    omega
  exact (not_lt_of_ge hb.2) hlt
end DirectGLSSW.ActiveArc.OpenCarrier
