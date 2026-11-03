import CompleteOverStep
import CompleteUnderStep
import FreeCornerStep
import ActiveArcCombinedRecursion
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.FiniteCalculation
open Cursor Split Primitive RetainedWords OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain
open CompatibleWords SingletonWords

/-- Literal working domain of one actual active arc. This stores geometric
invariants, not an itinerary, a recursive equation, or a promised transition. -/
structure Domain {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) where
  hR : Regular q
  hG : cyclicNoncollinear q
  hAux : ClosedAuxiliary q hR
  hleft : TraversalClosure.RemainingLeft q
  hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
    (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1)
  L : Fin (n+1) ⊕ Unit → CarrierLine
  hL : UniversalLocus L
  hT : PairTransverse L
  hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
    lineValue (L (Sum.inl e)) (q e.succ)=0
  hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0

/-- A finite literal geometric calculation. Every nonterminal constructor
records the actual physical operation, its actual current identity, and finite
calculations of all continuing active arcs. The closed child remains its exact
normalized primitive coefficient; no child induction hypothesis is encoded. -/
inductive Calculation : {n : ℕ} → (q : Fin (n+2) → PlanarPoint ℝ) → Domain q → Prop
  | terminal (q : Fin 2 → PlanarPoint ℝ) (D : Domain q)
      (hvalue : (-1:ℚ)^(List.ofFn q).length * GammaM q D.hR D.hAux=1) : Calculation q D
  | corner {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (D : Domain q)
      (hfree : ∀ c : Crossing q,c.val.1≠0) (S : Domain (suffix q))
      (hvalue : (-1:ℚ)^(List.ofFn q).length * GammaM q D.hR D.hAux =
        (-1:ℚ)^(List.ofFn (suffix q)).length * GammaM (suffix q) S.hR S.hAux)
      (next : Calculation (suffix q) S) : Calculation q D
  | over {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (D : Domain q)
      (c : Crossing q) (hc : FirstCrossing q c)
      (ho : crossingOver q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1)
      (ε : ℝ) (hε : 0<ε) (hct : leftParameter q c<leftParameter q c+ε)
      (htb : leftParameter q c+ε<afterBound q c)
      (A : Domain (moveStart q (leftParameter q c+ε)))
      (hvalue : (-1:ℚ)^(List.ofFn q).length * GammaM q D.hR D.hAux =
        (-1:ℚ)^(List.ofFn (moveStart q (leftParameter q c+ε))).length *
          GammaM (moveStart q (leftParameter q c+ε)) A.hR A.hAux)
      (next : Calculation (moveStart q (leftParameter q c+ε)) A) : Calculation q D
  | under {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (D : Domain q)
      (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
      (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1)
      (ε : ℝ) (hε : 0<ε) (hct : leftParameter q c<leftParameter q c+ε)
      (htb : leftParameter q c+ε<afterBound q c)
      (A : Domain (moveStart q (leftParameter q c+ε))) (P : Domain (parent q c hcut))
      (hvalue :
        let Q := child q D.hR c hc.1 hcut
        let ell := (Finset.univ.filter (fun i : Fin (a+1) =>
          0<planarDet (cyclicTangent Q ((cyclicSuccessorPerm (a+1))⁻¹ i)) (cyclicTangent Q i))).card
        (-1:ℚ)^(List.ofFn q).length * GammaM q D.hR D.hAux =
        (-1:ℚ)^(List.ofFn (moveStart q (leftParameter q c+ε))).length *
          GammaM (moveStart q (leftParameter q c+ε)) A.hR A.hAux -
        ((-1:ℚ)^ell * GeometricSmoothingWeights.separatingSmoothingSum Q
          (child_cyclicGeneric_of_closedAuxiliary q D.hR c hc.1 hcut D.hAux)
          (child_auxiliaryGenericity q D.hR c hc hcut D.hAux)) *
        ((-1:ℚ)^(List.ofFn (parent q c hcut)).length * GammaM (parent q c hcut) P.hR P.hAux))
      (next : Calculation (moveStart q (leftParameter q c+ε)) A)
      (parentNext : Calculation (parent q c hcut) P) : Calculation q D
end DirectGLSSW.ActiveArc.FiniteCalculation
