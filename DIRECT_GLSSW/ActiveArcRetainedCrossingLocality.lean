import ActiveArcRetainedCrossingVisits
import ActiveArcRetainedGapOwnership
import ActiveArcAlternatingSeparation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.RetainedWords
open PhysicalSegments PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

include hR in
theorem regular_anchor_not_edgeInterior (e : Fin (n+1)) (i : Fin (n+2)) :
    ¬edgeInterior q e (q i) := by
  intro hi
  by_cases h0 : i=e.castSucc
  · obtain ⟨t,ht0,ht1,ht⟩ := hi
    rw [h0] at ht
    have he : t=0 := edge_parameter_unique q hR e t 0
      (ht.symm.trans (affinePoint_zero _ _).symm)
    exact (ne_of_gt ht0) he
  · by_cases h1 : i=e.succ
    · obtain ⟨t,ht0,ht1,ht⟩ := hi
      rw [h1] at ht
      have he : t=1 := edge_parameter_unique q hR e t 1
        (ht.symm.trans (affinePoint_one _ _).symm)
      exact (ne_of_lt ht1) he
    · exact hR.anchor_avoid e i h0 h1 hi

include hR in
theorem crossingPoint_ne_anchor_regular (c : Crossing q) (i : Fin (n+2)) :
    crossingPoint q c≠q i := by
  intro he
  have hm := (crossingPoint_mem q c).1
  rw [he] at hm
  exact regular_anchor_not_edgeInterior q hR c.val.1 i hm

/-- An unselected original crossing is never a retained point-word vertex. -/
theorem unselected_crossingPoint_ne_vertex (c : Crossing q) (hc : c∉S)
    (root : Event q) (i : Fin (Fintype.card (Corner q hR S root))) :
    crossingPoint q c≠vertex q hR S root i := by
  have hr : retained q S (cornerEvent q hR S root i) :=
    (enumeration q hR S root i).property
  unfold vertex
  generalize he : cornerEvent q hR S root i=z at hr ⊢
  cases z with
  | inl j => exact crossingPoint_ne_anchor_regular q hR c j
  | inr v =>
    intro hp
    have hcv := crossingPoint_injective q hR.noTriple hp
    apply hc
    rw [hcv]
    exact hr

theorem not_two_retained_sides_of_alternating
    (hS : Nonalternation.Nonalternating q hR S) (c d : Crossing q)
    (hc : c∉S) (hd : d∈S)
    (halt : ¬ (Nonalternation.between q hR (Sum.inr (d,false)) (Sum.inr (c,false)) (Sum.inr (d,true)) ↔
      Nonalternation.between q hR (Sum.inr (d,false)) (Sum.inr (c,true)) (Sum.inr (d,true))))
    (root : Event q) (a b : Corner q hR S root) (hne : a≠b)
    (ha : eventAt q hR S root a.val≠terminal q)
    (hb : eventAt q hR S root b.val≠terminal q)
    (s t : ℝ) (hs0 : 0<s) (hs1 : s<1) (ht0 : 0<t) (ht1 : t<1)
    (hpa : crossingPoint q c=affinePoint (eventPoint q (eventAt q hR S root a.val))
      (eventPoint q (eventAt q hR S root (nextCorner q hR S root a).val)) s)
    (hpb : crossingPoint q c=affinePoint (eventPoint q (eventAt q hR S root b.val))
      (eventPoint q (eventAt q hR S root (nextCorner q hR S root b).val)) t) : False := by
  letI := eventOrder q hR.noTriple
  obtain ⟨u,hu0,hu1⟩ := retained_side_crossing_visit q hR S root a ha c s hs0 hs1 hpa
  obtain ⟨v,hv0,hv1⟩ := retained_side_crossing_visit q hR S root b hb c t ht0 ht1 hpb
  have huv : u≠v := by
    intro he
    subst v
    have hev := retained_gap_owner_unique q hR S root root a b ha hb _ hu0 hu1 hv0 hv1
    apply hne
    apply Subtype.ext
    apply (orbitEnumeration (incoming q hR.noTriple S) root).injective
    apply Subtype.ext
    exact hev
  have hua := retained_interval_component q hR S root a ha _ hu0 (le_of_lt hu1)
  have hvb := retained_interval_component q hR S root b hb _ hv0 (le_of_lt hv1)
  have hdc : d≠c := fun he => hc (he ▸ hd)
  have hsep := Nonalternation.incoming_alternating_components_ne q hR S hS d c hd hdc halt
  cases u <;> cases v
  · exact huv rfl
  · exact hsep (hua.trans hvb.symm)
  · exact hsep (hvb.trans hua.symm)
  · exact huv rfl

/-- The next retained event of a nonterminal open side is literally the next
index in the true open word, not a cyclic closing edge. -/
theorem open_nextCorner_event (i : Fin (openCount q hR S)) (hi : i.val+1<openCount q hR S) :
    eventAt q hR S (start q) (nextCorner q hR S (start q) (enumeration q hR S (start q) i)).val=
      cornerEvent q hR S (start q) ⟨i.val+1,hi⟩ := by
  have he := enumeration_cyclic q hR S (start q) i
  have hs : cyclicSuccessor i=⟨i.val+1,hi⟩ := by
    apply Fin.ext
    simp only [cyclicSuccessor,cyclicVertexIndex,Nat.add_zero]
    exact Nat.mod_eq_of_lt hi
  rw [hs] at he
  rw [← he]
  rfl

/-- An original crossing alternating with a selected chord cannot occur in the
interiors of two distinct physical sides of the literal retained open word. -/
theorem no_open_selfCrossing_of_alternating
    (hS : Nonalternation.Nonalternating q hR S) (c d : Crossing q)
    (hc : c∉S) (hd : d∈S)
    (halt : ¬ (Nonalternation.between q hR (Sum.inr (d,false)) (Sum.inr (c,false)) (Sum.inr (d,true)) ↔
      Nonalternation.between q hR (Sum.inr (d,false)) (Sum.inr (c,true)) (Sum.inr (d,true))))
    (i j : Fin (openCount q hR S)) (hne : i≠j)
    (hi : i.val+1<openCount q hR S) (hj : j.val+1<openCount q hR S)
    (s t : ℝ) (hs0 : 0<s) (hs1 : s<1) (ht0 : 0<t) (ht1 : t<1) :
    ¬ (crossingPoint q c=affinePoint (vertex q hR S (start q) i)
          (vertex q hR S (start q) ⟨i.val+1,hi⟩) s ∧
       crossingPoint q c=affinePoint (vertex q hR S (start q) j)
          (vertex q hR S (start q) ⟨j.val+1,hj⟩) t) := by
  rintro ⟨hpa,hpb⟩
  apply not_two_retained_sides_of_alternating q hR S hS c d hc hd halt (start q)
    (enumeration q hR S (start q) i) (enumeration q hR S (start q) j)
    (fun he => hne ((enumeration q hR S (start q)).injective he))
    (open_nonlast_ne_terminal q hR S i hi) (open_nonlast_ne_terminal q hR S j hj)
    s t hs0 hs1 ht0 ht1
  · rw [open_nextCorner_event q hR S i hi]
    exact hpa
  · rw [open_nextCorner_event q hR S j hj]
    exact hpb

end DirectGLSSW.ActiveArc.RetainedWords
