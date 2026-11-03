import ActiveArcParentClosedComponents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

theorem complement_of_retained_sameCycle
    (x : ComplementRetained q hR c hc hcut S T) (y : Event q)
    (hy : retained q (insert c (pieceSelections q hR c hc hcut S T)) y)
    (hxy : (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle x.val y) :
    (Nonalternation.eventEnumeration q hR).symm y∈complementSide (leftRank q hR c) (rightRank q hR c) := by
  letI := eventOrder q hR.noTriple
  have hm : y∈(orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) x.val).filter
      (fun z => decide (retained q (insert c (pieceSelections q hR c hc hcut S T)) z)) :=
    List.mem_filter.mpr ⟨(mem_orbitWord_iff _ _ _).mpr hxy,by simp only [hy,decide_true]⟩
  rw [complementRetained_orbit_filter] at hm
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hm
  exact z.property.2

/-- Exactly the original closed components whose canonical retained root is
in the actual singleton complement come from the actual parent. -/
theorem parentClosedComponentMap_range
    (D : {D : Component (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) //
      D≠openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))}) :
    (∃ C, parentClosedComponentMap q hR c hc hcut S T C=D) ↔
      (Nonalternation.eventEnumeration q hR).symm
        (closedRoot q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property)∈
        complementSide (leftRank q hR c) (rightRank q hR c) := by
  constructor
  · rintro ⟨C,rfl⟩
    let x := parentClosedRetainedRoot q hR c hcut T C
    let E := parentRetainedOrderIso q hR c hc hcut S T
    let D := parentClosedComponentMap q hR c hc hcut S T C
    have hs := closedRoot_spec q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property
    exact complement_of_retained_sameCycle q hR c hc hcut S T (E x).val _ hs.2
      ((componentOf_eq_iff _ _ _).mp hs.1.symm)
  · intro hcomp
    have hs := closedRoot_spec q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property
    obtain he|⟨y,hy,he⟩ := (retained_complement_range q hR c hc hcut S T _).mp ⟨hs.2,hcomp⟩
    · have hh := hs.1
      rw [he] at hh
      exact False.elim (D.property hh.symm)
    · let x : ParentRetained q c hcut T := ⟨y,hy⟩
      have hn : componentOf (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) y≠
          openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T := by
        intro hp
        have ho := (mapped_parent_open_iff q hR c hc hcut S T x).mpr ((componentOf_eq_iff _ _ _).mp hp)
        have hh := (componentOf_eq_iff _ _ _).mpr ho
        change componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
          (parentEventMap q hR c hc hcut y)=openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) at hh
        rw [he,hs.1] at hh
        exact D.property hh
      let C : {C : Component (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) //
          C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T} :=
        ⟨componentOf (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) y,hn⟩
      refine ⟨C,Subtype.ext ?_⟩
      have hh := parentClosedComponentMap_componentOf q hR c hc hcut S T C x rfl
      change componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
        (parentEventMap q hR c hc hcut y)=(parentClosedComponentMap q hR c hc hcut S T C).val at hh
      rw [he,hs.1] at hh
      exact hh.symm

/-- Proved bijection onto the actual original closed complement components.
The remaining original components belong to the child interval, whose polygon
word correspondence is a separate obligation. -/
def parentClosedComplementEquiv :
    {C : Component (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) //
      C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T} ≃
    {D : {D : Component (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) //
      D≠openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))} //
      (Nonalternation.eventEnumeration q hR).symm
        (closedRoot q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property)∈
        complementSide (leftRank q hR c) (rightRank q hR c)} :=
  Equiv.ofBijective (fun C => ⟨parentClosedComponentMap q hR c hc hcut S T C,
    (parentClosedComponentMap_range q hR c hc hcut S T _).mp ⟨C,rfl⟩⟩) ⟨by
      intro C D he
      exact parentClosedComponentMap_injective q hR c hc hcut S T (congrArg Subtype.val he),by
      intro D
      obtain ⟨C,hC⟩ := (parentClosedComponentMap_range q hR c hc hcut S T D.val).mpr D.property
      exact ⟨C,Subtype.ext hC⟩⟩

theorem parentClosedComplementEquiv_val
    (C : {C : Component (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) //
      C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T}) :
    (parentClosedComplementEquiv q hR c hc hcut S T C).val=parentClosedComponentMap q hR c hc hcut S T C := rfl

end DirectGLSSW.ActiveArc.CompatibleWords
