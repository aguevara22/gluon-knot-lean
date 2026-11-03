import ActiveArcParameterFormula
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationLocality
open DirectGLSSW ActiveArc
variable {n : ℕ} (q r : Fin (n+2) → PlanarPoint ℝ)

/-- The induced visit equivalence keeps the physical crossing branch unchanged. -/
def visitMapEquiv (E : Crossing q ≃ Crossing r) : Visit q ≃ Visit r :=
  Equiv.prodCongr E (Equiv.refl Bool)

/-- The induced actual event equivalence fixes every original anchor label. -/
def eventMapEquiv (E : Crossing q ≃ Crossing r) : Event q ≃ Event r :=
  Equiv.sumCongr (Equiv.refl _) (visitMapEquiv q r E)

theorem visitMapEquiv_edge (E : Crossing q ≃ Crossing r)
    (hlabels : ∀ c, (E c).val=c.val) (v : Visit q) :
    visitEdge r (visitMapEquiv q r E v)=visitEdge q v := by
  rcases v with ⟨c,b⟩
  cases b
  · exact congrArg Prod.fst (hlabels c)
  · exact congrArg Prod.snd (hlabels c)

theorem eventMapEquiv_edgeTag (E : Crossing q ≃ Crossing r)
    (hlabels : ∀ c, (E c).val=c.val) (x : Event q) :
    edgeTag r (eventMapEquiv q r E x)=edgeTag q x := by
  cases x with
  | inl i => rfl
  | inr v => exact congrArg Fin.val (visitMapEquiv_edge q r E hlabels v)

/-- The original fixed-pair quotient recovers the corresponding actual nearby visit. -/
theorem parameterFormula_eq_mapped (hR : Regular r) (E : Crossing q ≃ Crossing r)
    (hlabels : ∀ c, (E c).val=c.val) (v : Visit q) :
    parameterFormula r v.1.val v.2=visitParameter r (visitMapEquiv q r E v) := by
  have h := parameterFormula_eq_actual r hR (visitMapEquiv q r E v)
  change parameterFormula r (E v.1).val v.2=_ at h
  rw [hlabels] at h
  exact h

/-- Internal pointwise assembly: preserved physical labels and actual same-edge visit
order determine the complete anchor-and-visit order. The final neighborhood theorem
proves these inputs rather than assuming a stability premise. -/
theorem eventMapEquiv_order_iff (hQ : Regular q) (hR : Regular r)
    (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
    (hvisit : ∀ v w : Visit q, visitEdge q v=visitEdge q w →
      (visitParameter q v<visitParameter q w ↔
        visitParameter r (visitMapEquiv q r E v)<visitParameter r (visitMapEquiv q r E w)))
    (x y : Event q) :
    (eventOrder q hQ.noTriple).lt x y ↔
      (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y) := by
  rw [event_lt_iff,event_lt_iff,eventMapEquiv_edgeTag q r E hlabels,eventMapEquiv_edgeTag q r E hlabels]
  by_cases he : edgeTag q x=edgeTag q y
  · have hp : parameter q x<parameter q y ↔
        parameter r (eventMapEquiv q r E x)<parameter r (eventMapEquiv q r E y) := by
      cases x with
      | inl i =>
        cases y with
        | inl j => rfl
        | inr v =>
          change 0 < visitParameter q v ↔ 0 < visitParameter r (visitMapEquiv q r E v)
          exact iff_of_true (visitParameter_spec q v).1 (visitParameter_spec r _).1
      | inr v =>
        cases y with
        | inl j =>
          change visitParameter q v < 0 ↔ visitParameter r (visitMapEquiv q r E v) < 0
          exact iff_of_false (not_lt_of_ge (visitParameter_spec q v).1.le)
            (not_lt_of_ge (visitParameter_spec r _).1.le)
        | inr w => exact hvisit v w (Fin.ext he)
    rw [hp]
  · simp only [he,false_and,or_false]

end DirectGLSSW.ActiveArc.ConfigurationLocality
