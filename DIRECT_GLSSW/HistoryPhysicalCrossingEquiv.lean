import HistoryPhysicalSuffix
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PolygonDrawingBridge SmoothingCornerGeometry ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- The actual moving open arc has exactly the current unprocessed crossings.
Its original-crossing map is explicitly characterized, not merely cardinality. -/
theorem exists_history_physical_crossing_equiv {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (ξ : ℝ) (hξ0 : 0<ξ) (hξ1 : ξ<1) :
    ∃ a b : ℕ, ∃ hs : a+b=n, ∃ θ : ℝ, ∃ h0 : 0<θ, ∃ h1 : θ<1,
      ActiveArc.Regular (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) ∧
      ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ 0 = historyCursorPoint t c ξ ∧
      ∃ E : ActiveArc.Crossing (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) ≃
        SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c)),
      ∀ d, h.crossingOrigin (E d).val = crossingFin q (exposedCrossingEquiv q 0 hq he
        ((ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ (le_of_lt h0) h1 d).val)) := by
  obtain ⟨a,b,hs,θ,h0,h1,hreg,hpoint,hfilter⟩ := exists_history_physical_suffix q hq he h c hc ξ hξ0 hξ1
  let s := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  let C := {d : ActiveArc.Crossing (cutArc q 0) //
    a ≤ d.val.1.val ∧ (d.val.1.val=a → θ<ActiveArc.leftParameter (cutArc q 0) d)}
  let f : C → SuffixCrossing s (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) :=
    fun d => ⟨crossingFin q (exposedCrossingEquiv q 0 hq he d.val),(hfilter d.val).mp d.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro d e hh
      apply Subtype.ext
      apply (exposedCrossingEquiv q 0 hq he).injective
      apply (crossingFin q).injective
      exact congrArg Subtype.val hh
    · intro d
      let z := (exposedCrossingEquiv q 0 hq he).symm ((crossingFin q).symm d.val)
      have hz : crossingFin q (exposedCrossingEquiv q 0 hq he z)=d.val := by simp only [z,Equiv.apply_symm_apply]
      have hp : a≤z.val.1.val ∧ (z.val.1.val=a → θ<ActiveArc.leftParameter (cutArc q 0) z) := by
        apply (hfilter z).mpr
        simpa only [hz] using d.property
      exact ⟨⟨z,hp⟩,Subtype.ext hz⟩
  let Ep := ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ (le_of_lt h0) h1
  let Eo := Equiv.ofBijective f hf
  let Es := h.suffixCrossingEquiv c hc
  let E := Ep.trans (Eo.trans Es.symm)
  refine ⟨a,b,hs,θ,h0,h1,hreg,hpoint,E,?_⟩
  intro d
  exact congrArg Subtype.val (Es.apply_symm_apply (Eo (Ep d)))
end DirectGLSSW.HOMFLY
