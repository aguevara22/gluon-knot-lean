import ActiveArcSingletonWords
import ActiveArcPieceSelections

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

/-- Both actual visits of each closed-child crossing lie inside the singleton
closed interval; none belongs to the singleton open complement. -/
theorem child_visit_in_interval (d : PolygonCrossing (child q hR c hc.1 hcut)) (v : Bool) :
    (Nonalternation.eventEnumeration q hR).symm
      (Sum.inr (childCrossingToOriginal q hR c hc.1 hcut d,v)) ∈
      intervalSide (leftRank q hR c) (rightRank q hR c) := by
  letI := eventOrder q hR.noTriple
  let e := childCrossingToOriginal q hR c hc.1 hcut d
  have hm : InChild q c e := childCrossingToOriginal_inChild q hR c hc.1 hcut d
  have he : e≠c := by
    intro he;rw [he] at hm;exact crossing_not_inChild q c hc.1 hm
  have h0 := first_left_lt_other_left q hR c hc e he
  have h1 := (right_visit_before_cut_iff q hR c hc hcut e he).mpr hm
  have h01 := left_visit_lt_right q hR e
  apply (rank_interval_iff q hR c _).mpr
  cases v
  · exact ⟨h0,le_of_lt (lt_trans h01 h1)⟩
  · exact ⟨lt_trans h0 h01,le_of_lt h1⟩

theorem childSelection_visit_not_complement
    (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
    (d : Crossing q) (hd : d∈pieceSelections q hR c hc hcut S ∅) (v : Bool) :
    (Nonalternation.eventEnumeration q hR).symm (Sum.inr (d,v)) ∉
      complementSide (leftRank q hR c) (rightRank q hR c) := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hd
  cases z with
  | inl z =>
    intro hh
    exact hh (child_visit_in_interval q hR c hc hcut z v)
  | inr z => exact False.elim (Finset.not_mem_empty z (Finset.inr_mem_disjSum.mp hz))

theorem childSelection_pairing_on_complement
    (S : Finset (PolygonCrossing (child q hR c hc.1 hcut))) (x : Event q)
    (hx : (Nonalternation.eventEnumeration q hR).symm x ∈
      complementSide (leftRank q hR c) (rightRank q hR c)) :
    pairing q (insert c (pieceSelections q hR c hc hcut S ∅)) x=pairing q {c} x := by
  cases x with
  | inl i => rfl
  | inr v =>
    have hn : v.1∉pieceSelections q hR c hc hcut S ∅ :=
      fun hd => childSelection_visit_not_complement q hR c hc hcut S v.1 hd v.2 hx
    change (if v.1∈insert c (pieceSelections q hR c hc hcut S ∅) then
      (Sum.inr (v.1,!v.2) : Event q) else Sum.inr v)=
      (if v.1∈({c} : Finset (Crossing q)) then Sum.inr (v.1,!v.2) else Sum.inr v)
    simp only [Finset.mem_insert,Finset.mem_singleton,hn,or_false]

theorem childSelection_retained_on_complement
    (S : Finset (PolygonCrossing (child q hR c hc.1 hcut))) (x : Event q)
    (hx : (Nonalternation.eventEnumeration q hR).symm x ∈
      complementSide (leftRank q hR c) (rightRank q hR c)) :
    retained q (insert c (pieceSelections q hR c hc hcut S ∅)) x ↔ retained q {c} x := by
  cases x with
  | inl i => rfl
  | inr v =>
    have hn : v.1∉pieceSelections q hR c hc hcut S ∅ :=
      fun hd => childSelection_visit_not_complement q hR c hc hcut S v.1 hd v.2 hx
    simp only [retained,Finset.mem_insert,Finset.mem_singleton,hn,or_false]

end DirectGLSSW.ActiveArc.CompatibleWords
