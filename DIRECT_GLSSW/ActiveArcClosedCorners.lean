import ActiveArcOrbits

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc
open PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
variable (h : NoTriple q) (S : Finset (Crossing q))

theorem successor_strict_before_terminal (x : Event q) (hx : x≠terminal q) :
    letI := eventOrder q h; x<successor q h x := by
  letI := eventOrder q h
  rcases orderedCyclicSuccessor_order_spec (Event q) x with hh|hh
  · exact hh.1
  · exact False.elim (hx (le_antisymm (le_terminal q h x) (hh.1 (terminal q))))

theorem pairing_fixes_nonretained (x : Event q) (hx : ¬retained q S x) :
    pairing q S x=x := by
  classical
  cases x with
  | inl i => exact False.elim (hx True.intro)
  | inr v =>
    change (if v.1∈S then Sum.inr (v.1,!v.2) else Sum.inr v)=Sum.inr v
    exact if_neg hx

/-- An actual closed orbit has a retained event; no fallback root is introduced. -/
theorem closed_retained_exists (C : Component (incoming q h S))
    (hc : C≠openComponent q h S) :
    ∃ x : Event q, componentOf (incoming q h S) x=C ∧ retained q S x := by
  classical
  letI := eventOrder q h
  let F : Finset (Event q) := Finset.univ.filter (fun x => componentOf (incoming q h S) x=C)
  have hF : F.Nonempty := by
    obtain ⟨x⟩ := fibreNonempty (incoming q h S) C
    exact ⟨x.val,by simp [F,x.property]⟩
  let x := F.max' hF
  have hx : componentOf (incoming q h S) x=C := by
    have hm := Finset.max'_mem F hF
    exact (Finset.mem_filter.mp hm).2
  by_contra hh
  push_neg at hh
  have hfix := pairing_fixes_nonretained q S x (hh x hx)
  have hxt : x≠terminal q := (closedComponent_avoids_endpoints q h S C hc ⟨x,hx⟩).2
  have hstep : x < incoming q h S x := by
    change x<successor q h (pairing q S x)
    rw [hfix]
    exact successor_strict_before_terminal q h x hxt
  have hp : incoming q h S x∈F := by simp [F,componentOf_apply,hx]
  have hle : incoming q h S x≤x := Finset.le_max' F _ hp
  exact (not_lt_of_ge hle) hstep

/-- Least actual retained event of this closed orbit. -/
def closedRoot (C : Component (incoming q h S)) (hc : C≠openComponent q h S) : Event q := by
  classical
  letI := eventOrder q h
  exact (Finset.univ.filter (fun x => componentOf (incoming q h S) x=C ∧ retained q S x)).min'
    (by obtain ⟨x,hx⟩ := closed_retained_exists q h S C hc;exact ⟨x,by simp [hx]⟩)

theorem closedRoot_spec (C : Component (incoming q h S)) (hc : C≠openComponent q h S) :
    componentOf (incoming q h S) (closedRoot q h S C hc)=C ∧
      retained q S (closedRoot q h S C hc) := by
  classical
  letI := eventOrder q h
  let F := Finset.univ.filter (fun x : Event q =>
    componentOf (incoming q h S) x=C ∧ retained q S x)
  have hF : F.Nonempty := by
    obtain ⟨x,hx⟩ := closed_retained_exists q h S C hc
    exact ⟨x,by simp [F,hx]⟩
  exact (Finset.mem_filter.mp (Finset.min'_mem F hF)).2

theorem closedRoot_le (C : Component (incoming q h S)) (hc : C≠openComponent q h S)
    (x : Event q) (hx : componentOf (incoming q h S) x=C) (hr : retained q S x) :
    letI := eventOrder q h; closedRoot q h S C hc≤x := by
  classical
  letI := eventOrder q h
  apply Finset.min'_le
  simp [hx,hr]

end DirectGLSSW.ActiveArc
