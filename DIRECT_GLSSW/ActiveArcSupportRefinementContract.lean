import ActiveArcRetainedCrossingLocality
import ActiveArcNonalternatingRefinement
import ActiveArcGammaM

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor RetainedWords
attribute [local instance] Classical.propDecidable

/-- The complete support-refinement dichotomy at the next physical first-edge
crossing. Alternating selected chords exclude that crossing from the actual
open word; otherwise the original support has a unique independent child and
parent decomposition with additive cardinality. This says nothing about the
subsequent virtual-secant current jump or amplitude-product limit. -/
theorem support_refinement_cases
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (U : Primitive.Support q hR) (hu : c ∉ U.val) :
    ((∃ d ∈ U.val, ¬ Compatible q hR c d) ∧
      (∀ i : Fin (openCount q hR U.val),
        crossingPoint q c ≠ Primitive.OpenVertex q hR U i) ∧
      (∀ (i j : Fin (openCount q hR U.val)), i ≠ j →
        ∀ (hi : i.val+1 < openCount q hR U.val)
          (hj : j.val+1 < openCount q hR U.val)
          (s t : ℝ), 0 < s → s < 1 → 0 < t → t < 1 →
        ¬ (crossingPoint q c = affinePoint (Primitive.OpenVertex q hR U i)
            (Primitive.OpenVertex q hR U ⟨i.val+1,hi⟩) s ∧
           crossingPoint q c = affinePoint (Primitive.OpenVertex q hR U j)
            (Primitive.OpenVertex q hR U ⟨j.val+1,hj⟩) t))) ∨
    ((∀ d ∈ U.val, Compatible q hR c d) ∧
      ∃! p :
        ({S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
          PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
            (child_noTriple q hR c hc.1 hcut) S} ×
         Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)),
        pieceSelections q hR c hc hcut p.1.val p.2.val = U.val ∧
        U.val.card = p.1.val.card + p.2.val.card) := by
  classical
  by_cases hbad : ∃ d ∈ U.val, ¬ Compatible q hR c d
  · left
    refine ⟨hbad, ?_, ?_⟩
    · intro i
      exact unselected_crossingPoint_ne_vertex q hR U.val c hu (start q) i
    · obtain ⟨d,hd,halt⟩ := hbad
      have halt' : ¬ Compatible q hR d c :=
        fun h => halt ((compatible_symm q hR c d).mpr h)
      intro i j hne hi hj s t hs0 hs1 ht0 ht1
      exact no_open_selfCrossing_of_alternating q hR U.val U.property c d hu hd
        halt' i j hne hi hj s t hs0 hs1 ht0 ht1
  · right
    have hcompat : ∀ d ∈ U.val, Compatible q hR c d := by
      intro d hd
      by_contra h
      exact hbad ⟨d,hd,h⟩
    refine ⟨hcompat, ?_⟩
    let E := nonalternatingSelectionEquiv q hR c hc hcut
    let V : {V : Finset (Crossing q) //
        c ∉ V ∧ Nonalternation.Nonalternating q hR (insert c V)} :=
      ⟨U.val,hu,(nonalternating_insert_iff q hR c U.val hu).mpr ⟨U.property,hcompat⟩⟩
    let p := E.symm V
    have hp : pieceSelections q hR c hc hcut p.1.val p.2.val = U.val :=
      congrArg Subtype.val (E.apply_symm_apply V)
    have hcard : U.val.card = p.1.val.card + p.2.val.card := by
      have h := nonalternatingSelectionEquiv_card q hR c hc hcut p.1 p.2
      change (pieceSelections q hR c hc hcut p.1.val p.2.val).card = _ at h
      rw [hp] at h
      exact h
    refine ⟨p,⟨hp,hcard⟩,?_⟩
    intro r hr
    apply E.injective
    apply Subtype.ext
    change pieceSelections q hR c hc hcut r.1.val r.2.val =
      pieceSelections q hR c hc hcut p.1.val p.2.val
    exact hr.1.trans hp.symm

end DirectGLSSW.ActiveArc.Split
