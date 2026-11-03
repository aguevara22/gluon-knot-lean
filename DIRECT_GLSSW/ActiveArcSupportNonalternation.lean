import ActiveArcParentVisitOrder

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor FiniteCycleOrder
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)

/-- Literal chord compatibility is symmetric on actual, injectively labelled visits. -/
theorem compatible_symm (c d : Crossing q) : Compatible q hR c d ↔ Compatible q hR d c := by
  by_cases hcd : c=d
  · subst d;rfl
  have hne (i j : Bool) : (Nonalternation.actualEndpoint q hR (c,i)).val≠
      (Nonalternation.actualEndpoint q hR (d,j)).val := by
    intro hh
    exact hcd (congrArg Prod.fst ((Nonalternation.actualEndpoint_injective q hR) (Fin.ext hh)))
  have h00:=hne false false
  have h01:=hne false true
  have h10:=hne true false
  have h11:=hne true true
  unfold Compatible
  simp only [Nonalternation.between_iff_coordinates]
  change (strictCyclicBetween (Nonalternation.actualEndpoint q hR (c,false))
      (Nonalternation.actualEndpoint q hR (d,false)) (Nonalternation.actualEndpoint q hR (c,true)) ↔
    strictCyclicBetween (Nonalternation.actualEndpoint q hR (c,false))
      (Nonalternation.actualEndpoint q hR (d,true)) (Nonalternation.actualEndpoint q hR (c,true))) ↔
    (strictCyclicBetween (Nonalternation.actualEndpoint q hR (d,false))
      (Nonalternation.actualEndpoint q hR (c,false)) (Nonalternation.actualEndpoint q hR (d,true)) ↔
    strictCyclicBetween (Nonalternation.actualEndpoint q hR (d,false))
      (Nonalternation.actualEndpoint q hR (c,true)) (Nonalternation.actualEndpoint q hR (d,true)))
  simp only [strictCyclicBetween,Fin.lt_def]
  omega

theorem nonalternating_insert_iff (c : Crossing q) (S : Finset (Crossing q)) (hc : c∉S) :
    Nonalternation.Nonalternating q hR (insert c S) ↔
      Nonalternation.Nonalternating q hR S ∧ ∀ d∈S, Compatible q hR c d := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro d hd e he hde
      exact h d (Finset.mem_insert_of_mem hd) e (Finset.mem_insert_of_mem he) hde
    · intro d hd
      exact h c (Finset.mem_insert_self _ _) d (Finset.mem_insert_of_mem hd)
        (fun hcd => hc (hcd.symm ▸ hd))
  · rintro ⟨hS,hcS⟩ d hd e he hde
    rcases Finset.mem_insert.mp hd with hdc|hds
    · subst d
      rcases Finset.mem_insert.mp he with hec|hes
      · subst e;exact (hde rfl).elim
      · exact hcS e hes
    · rcases Finset.mem_insert.mp he with hec|hes
      · subst e
        exact (compatible_symm q hR d c).mpr (hcS d hds)
      · exact hS d hds e hes hde

/-- Two actual chords in disjoint ordered intervals cannot alternate. -/
theorem compatible_of_separated (d e : Crossing q)
    (hsep : (eventOrder q hR.noTriple).lt (Sum.inr (d,true)) (Sum.inr (e,false))) :
    Compatible q hR d e := by
  letI : LinearOrder (Event q) := eventOrder q hR.noTriple
  let d0 : Event q := Sum.inr (d,false)
  let d1 : Event q := Sum.inr (d,true)
  let e0 : Event q := Sum.inr (e,false)
  let e1 : Event q := Sum.inr (e,true)
  have hd : d0<d1 := left_visit_lt_right q hR d
  have he : e0<e1 := left_visit_lt_right q hR e
  have hs : d1<e0 := hsep
  have h0 : ¬ e0<d1 := not_lt_of_ge (le_of_lt hs)
  have h1 : ¬ e1<d1 := not_lt_of_ge (le_of_lt (lt_trans hs he))
  change strictCyclicBetween d0 e0 d1 ↔ strictCyclicBetween d0 e1 d1
  rw [strictCyclicBetween_iff_of_lt _ _ _ hd,strictCyclicBetween_iff_of_lt _ _ _ hd]
  simp only [h0,h1,and_false]


variable (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)

theorem child_nonalternating_iff (S : Finset (PolygonCrossing (child q hR c hfirst hcut))) :
    PolygonNonalternation.polygonNonalternating (child q hR c hfirst hcut)
      (child_noTriple q hR c hfirst hcut) S ↔
    ∀ d∈S, ∀ e∈S, d≠e → Compatible q hR
      (childCrossingToOriginal q hR c hfirst hcut d) (childCrossingToOriginal q hR c hfirst hcut e) := by
  constructor
  · intro h d hd e he hde
    have hh:=h d hd e he hde
    change childVisitBetween q hR c hfirst hcut (d,false) (e,false) (d,true) ↔
      childVisitBetween q hR c hfirst hcut (d,false) (e,true) (d,true) at hh
    exact (childVisitMap_between q hR c hfirst hcut (d,false) (e,false) (d,true)).trans
      (hh.trans (childVisitMap_between q hR c hfirst hcut (d,false) (e,true) (d,true)).symm)
  · intro h d hd e he hde
    have hh:=h d hd e he hde
    exact (childVisitMap_between q hR c hfirst hcut (d,false) (e,false) (d,true)).symm.trans
      (hh.trans (childVisitMap_between q hR c hfirst hcut (d,false) (e,true) (d,true)))

theorem parent_nonalternating_iff (S : Finset (Crossing (parent q c hcut))) :
    Nonalternation.Nonalternating (parent q c hcut) (regular_parent q hR c hcut) S ↔
    ∀ d∈S, ∀ e∈S, d≠e → Compatible q hR
      (parentCrossingToOriginal q c hcut d) (parentCrossingToOriginal q c hcut e) := by
  constructor
  · intro h d hd e he hde
    have hh:=h d hd e he hde
    exact (parentVisitMap_between q hR c hcut (d,false) (e,false) (d,true)).trans
      (hh.trans (parentVisitMap_between q hR c hcut (d,false) (e,true) (d,true)).symm)
  · intro h d hd e he hde
    have hh:=h d hd e he hde
    exact (parentVisitMap_between q hR c hcut (d,false) (e,false) (d,true)).symm.trans
      (hh.trans (parentVisitMap_between q hR c hcut (d,false) (e,true) (d,true)))

end DirectGLSSW.ActiveArc.Split
