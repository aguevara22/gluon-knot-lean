import ActiveArcClosedChildCrossings
import ActiveArcNonalternation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor FiniteCycleOrder
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)

/-- Literal nonalternation of one other chord with the designated cut chord. -/
def Compatible (c d : Crossing q) : Prop :=
  Nonalternation.between q hR (Sum.inr (c,false)) (Sum.inr (d,false)) (Sum.inr (c,true)) ↔
    Nonalternation.between q hR (Sum.inr (c,false)) (Sum.inr (d,true)) (Sum.inr (c,true))

theorem left_visit_lt_right (d : Crossing q) :
    (eventOrder q hR.noTriple).lt (Sum.inr (d,false)) (Sum.inr (d,true)) := by
  apply (event_lt_iff q hR.noTriple _ _).mpr
  left
  exact d.property.1

theorem first_left_lt_other_left (c : Crossing q) (hc : FirstCrossing q c)
    (d : Crossing q) (hd : d≠c) :
    (eventOrder q hR.noTriple).lt (Sum.inr (c,false)) (Sum.inr (d,false)) := by
  apply (event_lt_iff q hR.noTriple _ _).mpr
  change c.val.1.val<d.val.1.val ∨ c.val.1.val=d.val.1.val ∧ leftParameter q c<leftParameter q d
  rw [hc.1]
  by_cases hd0 : d.val.1=0
  · right
    exact ⟨by rw [hd0],first_parameter_strict q hR c hc d hd0 hd⟩
  · left
    exact Fin.pos_iff_ne_zero.mpr hd0

theorem right_visit_before_cut_iff (c : Crossing q) (hc : FirstCrossing q c)
    (hcut : c.val.2.val=a) (d : Crossing q) (hd : d≠c) :
    (eventOrder q hR.noTriple).lt (Sum.inr (d,true)) (Sum.inr (c,true)) ↔ InChild q c d := by
  rw [event_lt_iff]
  change (d.val.2.val<c.val.2.val ∨ d.val.2.val=c.val.2.val ∧ rightParameter q d<rightParameter q c) ↔ _
  rw [hcut]
  constructor
  · intro h
    refine ⟨?_,fun hd0 => first_parameter_strict q hR c hc d hd0 hd,?_⟩
    · rcases h with h|h <;> omega
    · intro he;rcases h with h|h
      · omega
      · exact h.2
  · intro h
    rcases lt_or_eq_of_le h.1 with hl|he
    · exact Or.inl hl
    · exact Or.inr ⟨he,h.2.2 he⟩

theorem cut_before_left_visit_iff (c : Crossing q) (hcut : c.val.2.val=a) (d : Crossing q) :
    (eventOrder q hR.noTriple).lt (Sum.inr (c,true)) (Sum.inr (d,false)) ↔ InParent q c d := by
  rw [event_lt_iff]
  change (c.val.2.val<d.val.1.val ∨ c.val.2.val=d.val.1.val ∧ rightParameter q c<leftParameter q d) ↔ _
  rw [hcut]
  constructor
  · intro h
    constructor
    · rcases h with h|h <;> omega
    · intro he;rcases h with h|h
      · omega
      · exact h.2
  · intro h
    rcases lt_or_eq_of_le h.1 with hl|he
    · exact Or.inl hl
    · exact Or.inr ⟨he,h.2 he.symm⟩

/-- At the first physical crossing every compatible other chord lies entirely
in exactly one of the actual child and parent carriers. -/
theorem compatible_iff_regions (c : Crossing q) (hc : FirstCrossing q c)
    (hcut : c.val.2.val=a) (d : Crossing q) (hd : d≠c) :
    Compatible q hR c d ↔ InChild q c d ∨ InParent q c d := by
  letI : LinearOrder (Event q) := eventOrder q hR.noTriple
  let c0 : Event q := Sum.inr (c,false)
  let c1 : Event q := Sum.inr (c,true)
  let d0 : Event q := Sum.inr (d,false)
  let d1 : Event q := Sum.inr (d,true)
  have hcc : c0<c1 := left_visit_lt_right q hR c
  have hdd : d0<d1 := left_visit_lt_right q hR d
  have hcd : c0<d0 := first_left_lt_other_left q hR c hc d hd
  have hcd' := lt_trans hcd hdd
  have hne : d0≠c1 := by
    intro hh;have hb:=congrArg Prod.snd (Sum.inr.inj hh);cases hb
  change (strictCyclicBetween c0 d0 c1 ↔ strictCyclicBetween c0 d1 c1) ↔ _
  rw [strictCyclicBetween_iff_of_lt _ _ _ hcc,strictCyclicBetween_iff_of_lt _ _ _ hcc]
  simp only [hcd,hcd',true_and]
  rw [← right_visit_before_cut_iff q hR c hc hcut d hd,← cut_before_left_visit_iff q hR c hcut d]
  change (d0<c1 ↔ d1<c1) ↔ d1<c1 ∨ c1<d0
  constructor
  · intro h
    by_cases hr : d1<c1
    · exact Or.inl hr
    · right
      have hl : ¬ d0<c1 := fun hl => hr (h.mp hl)
      exact lt_of_le_of_ne (le_of_not_gt hl) hne.symm
  · rintro (hr|hl)
    · exact ⟨fun _ => hr,fun _ => lt_trans hdd hr⟩
    · have hn : ¬ d0<c1 := not_lt_of_ge (le_of_lt hl)
      have hn' : ¬ d1<c1 := not_lt_of_ge (le_of_lt (lt_trans hl hdd))
      exact ⟨fun h => (hn h).elim,fun h => (hn' h).elim⟩

/-- Original physical labels represented by the disjoint union of the two
literal daughter carriers. -/
def pieceCrossingToOriginal (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    PolygonCrossing (child q hR c hc.1 hcut) ⊕ Crossing (parent q c hcut) → Crossing q
  | Sum.inl d => childCrossingToOriginal q hR c hc.1 hcut d
  | Sum.inr d => parentCrossingToOriginal q c hcut d

theorem pieceCrossingToOriginal_injective (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    Function.Injective (pieceCrossingToOriginal q hR c hc hcut) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (childCrossingToOriginal_injective q hR c hc.1 hcut h)
    | inr y =>
      have hx:=childCrossingToOriginal_inChild q hR c hc.1 hcut x
      have hy:=parentCrossingToOriginal_inParent q hR c hcut y
      change childCrossingToOriginal q hR c hc.1 hcut x=parentCrossingToOriginal q c hcut y at h
      rw [h] at hx
      exact (child_parent_disjoint q c _ ⟨hx,hy⟩).elim
  | inr x =>
    cases y with
    | inl y =>
      have hx:=parentCrossingToOriginal_inParent q hR c hcut x
      have hy:=childCrossingToOriginal_inChild q hR c hc.1 hcut y
      change parentCrossingToOriginal q c hcut x=childCrossingToOriginal q hR c hc.1 hcut y at h
      rw [h] at hx
      exact (child_parent_disjoint q c _ ⟨hy,hx⟩).elim
    | inr y => exact congrArg Sum.inr (parentCrossingToOriginal_injective q c hcut h)

theorem pieceCrossing_range (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (d : Crossing q) :
    (∃ e, pieceCrossingToOriginal q hR c hc hcut e=d) ↔ d≠c ∧ Compatible q hR c d := by
  constructor
  · rintro ⟨e,rfl⟩
    cases e with
    | inl e =>
      have hm:=childCrossingToOriginal_inChild q hR c hc.1 hcut e
      have hne : childCrossingToOriginal q hR c hc.1 hcut e≠c := by
        intro hh;rw [hh] at hm;exact crossing_not_inChild q c hc.1 hm
      exact ⟨hne,(compatible_iff_regions q hR c hc hcut _ hne).mpr (Or.inl hm)⟩
    | inr e =>
      have hm:=parentCrossingToOriginal_inParent q hR c hcut e
      have hne : parentCrossingToOriginal q c hcut e≠c := by
        intro hh;rw [hh] at hm;exact crossing_not_inParent q c hcut hm
      exact ⟨hne,(compatible_iff_regions q hR c hc hcut _ hne).mpr (Or.inr hm)⟩
  · rintro ⟨hd,hcompat⟩
    rcases (compatible_iff_regions q hR c hc hcut d hd).mp hcompat with hchild|hparent
    · obtain ⟨e,he⟩:=(childCrossing_range q hR c hc.1 hcut d).mpr hchild
      exact ⟨Sum.inl e,he⟩
    · obtain ⟨e,he⟩:=(parentCrossing_range q hR c hcut d).mpr hparent
      exact ⟨Sum.inr e,he⟩

end DirectGLSSW.ActiveArc.Split
