import ActiveArcChildRestart
import ActiveArcParentCrossingCount
import ActiveArcAfterFirstCrossingCount
import ActiveArcSuffixCountDescent

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.ChildRestartRecursion
open DirectGLSSW
open DirectGLSSW.ActiveArc.Cursor
open DirectGLSSW.ActiveArc.Split
open DirectGLSSW.ActiveArc.SingletonWords
open DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW.ActiveArc.ChildRestart
open DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW.GeometricSmoothingWeights
open DirectGLSSW.ExposedOpenPrimitive
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.Gemini
open DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.HOMFLY.Coefficients
attribute [local instance] Classical.propDecidable

/-- A state is an actual active endpoint-inclusive polygonal arc. -/
abbrev ActiveWordState := Σ n : ℕ, Fin (n+2) → PlanarPoint ℝ

def activeWordMeasure (s : ActiveWordState) : ℕ × ℕ :=
  (Fintype.card (Crossing s.2), Fintype.card (Fin (s.1+2)))

abbrev LexLess (x y : ℕ × ℕ) : Prop := Prod.Lex Nat.lt Nat.lt x y

/-- Actual chart output carried as a dependent package. -/
structure ActualRestartResult {a b : ℕ} (hRI : GLSSWRootIndependence)
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q) (hAux : Primitive.ClosedAuxiliary q hR)
    (hu : crossingUnder q (polygonCrossingOfArc q c) =
      (polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0 < planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) where
  m : ℕ
  Q : Fin (m+2) → PlanarPoint ℝ
  hQ : CyclicGeneric Q
  hAuxQ : auxiliaryGenericity Q hQ
  hleftQ : ∀ i, 0 < planarDet (cyclicTangent Q i)
    (cyclicTangent Q (cyclicSuccessor i))
  heQ : LeftExposed Q 0
  hcount : Fintype.card (Crossing (cutArc Q 0)) < Fintype.card (Crossing q)
  hsum : (-1 : ℚ)^(m+2) * separatingSmoothingSum Q hQ hAuxQ =
    (-1 : ℚ)^(a+1) * separatingSmoothingSum (child q hR c hc.1 hcut)
      (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
      (child_auxiliaryGenericity q hR c hc hcut hAux)
  hcoeff : coeff (candidateEvaluator (positivePolygonEventDiagram Q hQ)
      (positivePolygonEventDiagram_nArc_pos Q hQ))
      (1-((positivePolygonEventDiagram Q hQ).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram Q hQ)|) 0 =
    coeff (candidateEvaluator
      (positivePolygonEventDiagram (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux))
      (positivePolygonEventDiagram_nArc_pos _ _))
      (1-((positivePolygonEventDiagram
        (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux))|) 0

theorem actual_under_child_restart_nonempty
    {a b : ℕ} (hRI : GLSSWRootIndependence)
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q) (hAux : Primitive.ClosedAuxiliary q hR)
    (hu : crossingUnder q (polygonCrossingOfArc q c) =
      (polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0 < planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) :
    Nonempty (ActualRestartResult hRI q hR c hc hcut hG1 hAux hu hleft) := by
  obtain ⟨m,Q,hQ,hAuxQ,hleftQ,heQ,hcount,hsum,hcoeff⟩ :=
    exists_actual_under_child_exposed_restart hRI q hR c hc hcut hG1 hAux hu hleft
  exact ⟨⟨m,Q,hQ,hAuxQ,hleftQ,heQ,hcount,hsum,hcoeff⟩⟩

noncomputable def chosenActualRestartResult
    {a b : ℕ} (hRI : GLSSWRootIndependence)
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q) (hAux : Primitive.ClosedAuxiliary q hR)
    (hu : crossingUnder q (polygonCrossingOfArc q c) =
      (polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0 < planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) :
    ActualRestartResult hRI q hR c hc hcut hG1 hAux hu hleft :=
  Classical.choice (actual_under_child_restart_nonempty hRI q hR c hc hcut hG1 hAux hu hleft)

noncomputable def chosenActualRestartState
    {a b : ℕ} (hRI : GLSSWRootIndependence)
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q) (hAux : Primitive.ClosedAuxiliary q hR)
    (hu : crossingUnder q (polygonCrossingOfArc q c) =
      (polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0 < planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) : ActiveWordState :=
  let r := chosenActualRestartResult hRI q hR c hc hcut hG1 hAux hu hleft
  ⟨r.m, cutArc r.Q 0⟩

/-- Legal active-word reductions, including the internally selected actual
uniform exposed restart of a closed first-under child. -/
inductive ActiveStep : ActiveWordState → ActiveWordState → Prop
  | afterFirst {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
      (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
      (t : ℝ) (htc : leftParameter q c<t) (htb : t<afterBound q c) :
      ActiveStep ⟨n, moveStart q t⟩ ⟨n,q⟩
  | parent {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
      (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
      (hcut : c.val.2.val=a) :
      ActiveStep ⟨b,parent q c hcut⟩ ⟨a+b,q⟩
  | cornerSuffix {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ)
      (hR : Regular q)
      (hleft : 0 < planarDet (q 1-q 0) (q 2-q 1))
      (hfree : ∀ c : Crossing q, c.val.1 ≠ 0) :
      ActiveStep ⟨b,suffix (a:=1) (b:=b) q⟩ ⟨1+b,q⟩
  | underChild {a b : ℕ} (hRI : GLSSWRootIndependence)
      (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
      (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
      (hG1 : cyclicNoncollinear q) (hAux : Primitive.ClosedAuxiliary q hR)
      (hu : crossingUnder q (polygonCrossingOfArc q c) =
        (polygonCrossingOfArc q c).val.1)
      (hleft : ∀ i : Fin (a+b), i.val<a →
        0 < planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
          (q i.succ.succ-q i.succ.castSucc)) :
      ActiveStep (chosenActualRestartState hRI q hR c hc hcut hG1 hAux hu hleft)
        ⟨a+b,q⟩

private theorem afterFirst_decreases {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (htc : leftParameter q c<t) (htb : t<afterBound q c) :
    LexLess (activeWordMeasure ⟨n,moveStart q t⟩) (activeWordMeasure ⟨n,q⟩) := by
  have hcount := after_first_crossing_count_lt q hR c hc t htc htb
  change Prod.Lex Nat.lt Nat.lt
    (Fintype.card (Crossing (moveStart q t)), Fintype.card (Fin (n+2)))
    (Fintype.card (Crossing q), Fintype.card (Fin (n+2)))
  exact (Prod.lex_iff).2 (Or.inl hcount)

private theorem parent_decreases {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    LexLess (activeWordMeasure ⟨b,parent q c hcut⟩) (activeWordMeasure ⟨a+b,q⟩) := by
  have hcount := parent_crossing_count_lt q hR c hcut
  change Prod.Lex Nat.lt Nat.lt
    (Fintype.card (Crossing (parent q c hcut)), Fintype.card (Fin (b+2)))
    (Fintype.card (Crossing q), Fintype.card (Fin (a+b+2)))
  exact (Prod.lex_iff).2 (Or.inl hcount)

private theorem cornerSuffix_decreases {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ)
    (hR : Regular q) (hleft : 0 < planarDet (q 1-q 0) (q 2-q 1))
    (hfree : ∀ c : Crossing q, c.val.1 ≠ 0) :
    LexLess (activeWordMeasure ⟨b,suffix (a:=1) (b:=b) q⟩)
      (activeWordMeasure ⟨1+b,q⟩) := by
  have hcount := suffix_crossing_count_le (a:=1) (b:=b) q
  have hvertices : Fintype.card (Fin (b+2)) < Fintype.card (Fin (1+b+2)) := by
    simp only [Fintype.card_fin]
    omega
  change Prod.Lex Nat.lt Nat.lt
    (Fintype.card (Crossing (suffix (a:=1) (b:=b) q)), Fintype.card (Fin (b+2)))
    (Fintype.card (Crossing q), Fintype.card (Fin (1+b+2)))
  rcases lt_or_eq_of_le hcount with hlt|heq
  · exact (Prod.lex_iff).2 (Or.inl hlt)
  · exact (Prod.lex_iff).2 (Or.inr ⟨heq,hvertices⟩)

private theorem underChild_decreases {a b : ℕ}
    (hRI : GLSSWRootIndependence) (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (hcut : c.val.2.val=a) (hG1 : cyclicNoncollinear q)
    (hAux : Primitive.ClosedAuxiliary q hR)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0 < planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) :
    LexLess
      (activeWordMeasure (chosenActualRestartState hRI q hR c hc hcut hG1 hAux hu hleft))
      (activeWordMeasure ⟨a+b,q⟩) := by
  let r := chosenActualRestartResult hRI q hR c hc hcut hG1 hAux hu hleft
  change Prod.Lex Nat.lt Nat.lt
    (Fintype.card (Crossing (cutArc r.Q 0)), Fintype.card (Fin (r.m+2)))
    (Fintype.card (Crossing q), Fintype.card (Fin (a+b+2)))
  exact (Prod.lex_iff).2 (Or.inl r.hcount)

theorem activeStep_decreases {small large : ActiveWordState} (h : ActiveStep small large) :
    LexLess (activeWordMeasure small) (activeWordMeasure large) := by
  cases h with
  | afterFirst q hR c hc t htc htb => exact afterFirst_decreases q hR c hc t htc htb
  | parent q hR c hc hcut => exact parent_decreases q hR c hc hcut
  | cornerSuffix q hR hleft hfree => exact cornerSuffix_decreases q hR hleft hfree
  | underChild hRI q hR c hc hcut hG1 hAux hu hleft =>
      exact underChild_decreases hRI q hR c hc hcut hG1 hAux hu hleft

theorem activeStep_wellFounded : WellFounded ActiveStep := by
  have hp : WellFounded (Prod.Lex Nat.lt Nat.lt) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  have hm : WellFounded (InvImage (Prod.Lex Nat.lt Nat.lt) activeWordMeasure) :=
    InvImage.wf activeWordMeasure hp
  exact hm.mono (by
    intro small large h
    exact activeStep_decreases h)

theorem activeStep_induction {P : ActiveWordState → Prop}
    (s : ActiveWordState)
    (step : ∀ s, (∀ smaller, ActiveStep smaller s → P smaller) → P s) : P s :=
  activeStep_wellFounded.induction s step

end DirectGLSSW.ActiveArc.ChildRestartRecursion
