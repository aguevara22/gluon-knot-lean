import ActiveArcChildClosedComponents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

theorem interval_of_retained_sameCycle
    (x : IntervalRetained q hR c hc hcut S T) (y : Event q)
    (hy : retained q (insert c (pieceSelections q hR c hc hcut S T)) y)
    (hxy : (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle x.val y) :
    (Nonalternation.eventEnumeration q hR).symm y∈intervalSide (leftRank q hR c) (rightRank q hR c) := by
  letI := eventOrder q hR.noTriple
  have hm : y∈(orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) x.val).filter
      (fun z => decide (retained q (insert c (pieceSelections q hR c hc hcut S T)) z)) :=
    List.mem_filter.mpr ⟨(mem_orbitWord_iff _ _ _).mpr hxy,by simp only [hy,decide_true]⟩
  rw [intervalRetained_orbit_filter] at hm
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hm
  exact z.property.2

variable (hAux : Primitive.ClosedAuxiliary q hR)

/-- Exactly the original closed components with retained roots in the actual
singleton child interval come from the actual cyclic child polygon. -/
theorem childComponentMap_range
    (D : {D : Component (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) //
      D≠openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))}) :
    (∃ C, childComponentMap q hR c hc hcut hAux S T C=D) ↔
      (Nonalternation.eventEnumeration q hR).symm
        (closedRoot q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property)∈
        intervalSide (leftRank q hR c) (rightRank q hR c) := by
  constructor
  · rintro ⟨C,rfl⟩
    let x := childCanonicalIncomingRoot q hR c hc hcut hAux S C
    let D := childComponentMap q hR c hc hcut hAux S T C
    have hs := closedRoot_spec q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property
    exact interval_of_retained_sameCycle q hR c hc hcut S T (childRetainedEquiv q hR c hc hcut S T x) _ hs.2
      ((componentOf_eq_iff _ _ _).mp hs.1.symm)
  · intro hint
    have hs := closedRoot_spec q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property
    obtain ⟨y,hy,he⟩ := (retained_interval_range q hR c hc hcut S T _).mp ⟨hs.2,hint⟩
    let x : ChildRetained q hR c hc hcut S := ⟨y,hy⟩
    let C := componentOf (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S)
      (smoothingPairing (child q hR c hc.1 hcut) S y)
    refine ⟨C,Subtype.ext ?_⟩
    have hh := childComponentMap_componentOf q hR c hc hcut hAux S T C x rfl
    change componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (childEventMap q hR c hc hcut y)=(childComponentMap q hR c hc hcut hAux S T C).val at hh
    rw [he,hs.1] at hh
    exact hh.symm

/-- Proved full bijection of actual cyclic child components with the original
closed interval components; original auxiliary only supplies the existing
canonical child root via already derived child CyclicGeneric. -/
def childClosedIntervalEquiv :
    Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S) ≃
    {D : {D : Component (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) //
      D≠openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))} //
      (Nonalternation.eventEnumeration q hR).symm
        (closedRoot q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property)∈
        intervalSide (leftRank q hR c) (rightRank q hR c)} :=
  Equiv.ofBijective (fun C => ⟨childComponentMap q hR c hc hcut hAux S T C,
    (childComponentMap_range q hR c hc hcut S T hAux _).mp ⟨C,rfl⟩⟩) ⟨by
      intro C D he
      exact childComponentMap_injective q hR c hc hcut hAux S T (congrArg Subtype.val he),by
      intro D
      obtain ⟨C,hC⟩ := (childComponentMap_range q hR c hc hcut S T hAux D.val).mpr D.property
      exact ⟨C,Subtype.ext hC⟩⟩

theorem childClosedIntervalEquiv_val
    (C : Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S)) :
    (childClosedIntervalEquiv q hR c hc hcut S T hAux C).val=childComponentMap q hR c hc hcut hAux S T C := rfl

end DirectGLSSW.ActiveArc.CompatibleWords
