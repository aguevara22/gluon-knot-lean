import GenericFramedSkein
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.FramedPolynomial
open Coefficients LowestRowContract PrincipalTurning PermutationOrbits

/-- Ordinary integer polynomials evaluated at the existing framed variable. -/
def polynomialValue : Polynomial ℤ →+* HOMFLYCoeff :=
  Polynomial.eval₂RingHom (Int.castRingHom HOMFLYCoeff) framedVariable

theorem framingFactor_mul_eq_zero (P : HOMFLYCoeff)
    (h : (aMonomial - aInvMonomial) * P = 0) : P = 0 := by
  classical
  by_contra hp
  have hs : P.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  obtain ⟨x,hx,hm⟩ := P.support.exists_max_image Prod.fst hs
  have hz : coeff P (x.1+2) x.2 = 0 := by
    by_contra hn
    have hmem : (x.1+2,x.2) ∈ P.support := Finsupp.mem_support_iff.mpr hn
    have := hm _ hmem
    omega
  have he := congrArg (fun Q : HOMFLYCoeff => coeff Q (x.1+1) x.2) h
  rw [sub_mul] at he
  change coeff (aMonomial*P) (x.1+1) x.2 -
    coeff (aInvMonomial*P) (x.1+1) x.2 = 0 at he
  rw [coeff_aMonomial_mul,coeff_aInvMonomial_mul] at he
  have he' : coeff P x.1 x.2 = 0 := by
    simpa only [show x.1+1-1=x.1 by omega,show x.1+1+1=x.1+2 by omega,hz,sub_zero] using he
  exact (Finsupp.mem_support_iff.mp hx) he'

theorem framingFactor_cancel (P Q : HOMFLYCoeff)
    (h : (aMonomial-aInvMonomial)*P = (aMonomial-aInvMonomial)*Q) : P = Q := by
  apply sub_eq_zero.mp
  apply framingFactor_mul_eq_zero
  rw [mul_sub,h,sub_self]

theorem coeff_framedVariable_mul (P : HOMFLYCoeff) (i j : ℤ) :
    coeff (framedVariable * P) i j = coeff P (i-2) j - coeff P i j := by
  rw [framedVariable,pow_two,sub_mul,one_mul,mul_assoc]
  change coeff (aMonomial*(aMonomial*P)) i j - coeff P i j = _
  rw [coeff_aMonomial_mul,coeff_aMonomial_mul]
  congr 2 <;> omega

theorem polynomialValue_nonnegative (F : Polynomial ℤ) :
    ∀ i j : ℤ, i < 0 → coeff (polynomialValue F) i j = 0 := by
  classical
  induction F using Polynomial.induction_on with
  | C a =>
    intro i j hi
    simp only [polynomialValue,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
    change coeff (a : HOMFLYCoeff) i j = 0
    rw [AddMonoidAlgebra.intCast_def]
    simp only [coeff,Finsupp.single_apply]
    split_ifs with heq
    · have hh := congrArg Prod.fst heq
      change (0 : ℤ) = i at hh
      omega
    · rfl
  | add p q hp hq =>
    intro i j hi
    simp only [map_add,coeff,Finsupp.add_apply]
    change coeff (polynomialValue p) i j + coeff (polynomialValue q) i j = 0
    rw [hp i j hi,hq i j hi,add_zero]
  | monomial n a ih =>
    intro i j hi
    have he : Polynomial.C a * Polynomial.X^(n+1) =
        (Polynomial.C a * Polynomial.X^n)*Polynomial.X := by rw [pow_succ,mul_assoc]
    rw [he,map_mul]
    have hx : polynomialValue Polynomial.X = framedVariable := Polynomial.eval₂_X _ _
    rw [hx,mul_comm,coeff_framedVariable_mul,ih _ j (by omega),ih i j hi,sub_self]

theorem polynomialValue_constant (F : Polynomial ℤ) :
    coeff (polynomialValue F) 0 0 = F.eval (-1) := by
  classical
  induction F using Polynomial.induction_on with
  | C a =>
    simp [polynomialValue,coeff,AddMonoidAlgebra.intCast_def]
  | add p q hp hq =>
    simpa only [map_add,coeff,Finsupp.add_apply,Polynomial.eval_add] using congrArg₂ (·+·) hp hq
  | monomial n a ih =>
    have he : Polynomial.C a * Polynomial.X^(n+1) =
        (Polynomial.C a * Polynomial.X^n)*Polynomial.X := by rw [pow_succ,mul_assoc]
    rw [he,map_mul]
    have hx : polynomialValue Polynomial.X = framedVariable := Polynomial.eval₂_X _ _
    rw [hx,mul_comm,coeff_framedVariable_mul]
    rw [show (0 : ℤ)-2 = -2 by omega,
      polynomialValue_nonnegative _ (-2) 0 (by omega),zero_sub,ih,
      Polynomial.eval_mul_X]
    ring


theorem shifted_row_eq_of_polynomialWitness (k : ℤ) (P : HOMFLYCoeff)
    (F : Polynomial ℤ)
    (hF : aPower k * (aMonomial-aInvMonomial) * P =
      framedVariable * polynomialValue F) :
    aPower (k-1) * P = polynomialValue F := by
  have hy : framedVariable = (aMonomial-aInvMonomial)*aMonomial := by
    rw [framedVariable,pow_two,sub_mul,mul_comm aInvMonomial aMonomial,
      aMonomial_mul_aInvMonomial]
  have hc : aPower k * P = aMonomial * polynomialValue F := by
    apply framingFactor_cancel
    calc
      (aMonomial-aInvMonomial)*(aPower k*P) =
          aPower k*(aMonomial-aInvMonomial)*P := by ring
      _ = framedVariable*polynomialValue F := hF
      _ = (aMonomial-aInvMonomial)*(aMonomial*polynomialValue F) := by rw [hy];ring
  calc
    aPower (k-1)*P = aPower (-1)*(aPower k*P) := by
      rw [←mul_assoc,←GeminiLowest.aPower_add]
      congr 2 <;> omega
    _ = aPower (-1)*(aMonomial*polynomialValue F) := congrArg (aPower (-1)*·) hc
    _ = polynomialValue F := by
      rw [GeminiLowest.aPower_neg_one,←mul_assoc,mul_comm aInvMonomial aMonomial,
        aMonomial_mul_aInvMonomial,one_mul]

theorem coeff_aPower_mul (k : ℤ) (P : HOMFLYCoeff) (i j : ℤ) :
    coeff (aPower k * P) i j = coeff P (i-k) j := by
  simp [aPower,coeff,AddMonoidAlgebra.single_mul_apply]
  congr 2 <;> omega

theorem polynomialWitness_corner (k : ℤ) (P : HOMFLYCoeff) (F : Polynomial ℤ)
    (hF : aPower k * (aMonomial-aInvMonomial) * P =
      framedVariable * polynomialValue F) :
    aPower (k-1)*P = polynomialValue F ∧
    (∀ i : ℤ, i < 1-k → coeff P i 0 = 0) ∧
    coeff P (1-k) 0 = F.eval (-1) := by
  have hs := shifted_row_eq_of_polynomialWitness k P F hF
  refine ⟨hs,?_,?_⟩
  · intro i hi
    have he := congrArg (fun Q => coeff Q (i+k-1) 0) hs
    dsimp only at he
    rw [coeff_aPower_mul,show i+k-1-(k-1)=i by omega] at he
    exact he.trans (polynomialValue_nonnegative F _ 0 (by omega))
  · have he := congrArg (fun Q => coeff Q 0 0) hs
    dsimp only at he
    rw [coeff_aPower_mul,show 0-(k-1)=1-k by omega] at he
    exact he.trans (polynomialValue_constant F)

/-- Conditional source corner identity for the existing framed knot row.
The ordinary polynomial witness is supplied, never inferred. -/
theorem framedKnotRow_polynomialWitness_corner
    (H : Evaluator) (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (C : diagramComponent D) (F : Polynomial ℤ)
    (hF : framedKnotRow H D hD C = framedVariable * polynomialValue F) :
    aPower (diagramWrithe D+componentTurnInteger D C-1)*zRow (H D hD) 0 =
      polynomialValue F ∧
    (∀ i : ℤ, i < 1-(diagramWrithe D+componentTurnInteger D C) →
      coeff (zRow (H D hD) 0) i 0 = 0) ∧
    coeff (zRow (H D hD) 0) (1-(diagramWrithe D+componentTurnInteger D C)) 0 =
      F.eval (-1) :=
  polynomialWitness_corner _ _ F hF



theorem coeff_zRow_zero (P : HOMFLYCoeff) (i : ℤ) :
    coeff (zRow P 0) i 0 = coeff P i 0 := by
  simp only [coeff,zRow_apply,ite_true]

theorem framedKnotRow_polynomialWitness_prescribed_corner
    (H : Evaluator) (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (C : diagramComponent D) (F : Polynomial ℤ)
    (hpos : ∀ c : Fin D.nCrossing, crossingSign D c = Sign.pos)
    (hr : 0 ≤ componentTurnInteger D C)
    (hF : framedKnotRow H D hD C = framedVariable * polynomialValue F) :
    (∀ i : ℤ, i < 1-(D.nCrossing : ℤ)-|componentTurnInteger D C| →
      coeff (H D hD) i 0 = 0) ∧
    coeff (H D hD) (1-(D.nCrossing : ℤ)-|componentTurnInteger D C|) 0 = F.eval (-1) := by
  have hw : diagramWrithe D = (D.nCrossing : ℤ) := by
    simp [diagramWrithe,writheSign,hpos]
  have ht : |componentTurnInteger D C| = componentTurnInteger D C := abs_of_nonneg hr
  have hf := framedKnotRow_polynomialWitness_corner H D hD C F hF
  rw [hw] at hf
  simpa only [ht,sub_add_eq_sub_sub,coeff_zRow_zero] using hf.2

theorem framedVariable_polynomialValue (F : Polynomial ℤ) :
    framedVariable * polynomialValue F = polynomialValue (Polynomial.X * F) := by
  rw [map_mul]
  have hx : polynomialValue Polynomial.X = framedVariable := Polynomial.eval₂_X _ _
  rw [hx]

theorem negative_constant_of_polynomialWitness (B : HOMFLYCoeff) (F : Polynomial ℤ)
    (hF : B = framedVariable * polynomialValue F) :
    -coeff B 0 0 = F.eval (-1) := by
  rw [hF,framedVariable_polynomialValue,polynomialValue_constant,
    Polynomial.eval_mul,Polynomial.eval_X]
  ring

theorem polynomialWitness_product_constant (B C : HOMFLYCoeff) (F G : Polynomial ℤ)
    (hF : B = framedVariable * polynomialValue F)
    (hG : C = framedVariable * polynomialValue G) :
    coeff (B*C) 0 0 = coeff B 0 0 * coeff C 0 0 := by
  rw [hF,hG,framedVariable_polynomialValue,framedVariable_polynomialValue,
    ←map_mul,polynomialValue_constant,Polynomial.eval_mul,
    polynomialValue_constant,polynomialValue_constant]

theorem polynomialWitness_subtraction
    (B Bsw BL BR : HOMFLYCoeff) (FL FR : Polynomial ℤ)
    (hL : BL = framedVariable * polynomialValue FL)
    (hR : BR = framedVariable * polynomialValue FR)
    (hskein : B = Bsw + BL*BR) :
    -coeff B 0 0 = -coeff Bsw 0 0 - (-coeff BL 0 0)*(-coeff BR 0 0) := by
  rw [hskein]
  change -(coeff Bsw 0 0 + coeff (BL*BR) 0 0) = _
  rw [polynomialWitness_product_constant BL BR FL FR hL hR]
  ring

theorem framedVariable_negative_constant : -coeff framedVariable 0 0 = 1 := by
  have hF : framedVariable = framedVariable * polynomialValue (1 : Polynomial ℤ) := by
    rw [map_one,mul_one]
  simpa using negative_constant_of_polynomialWitness framedVariable 1 hF



/-- Actual positive connected skein, specialized only after polynomial witnesses
for its two smoothed component rows are supplied. -/
theorem positive_connected_polynomialWitness_subtraction
    (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (hpos : crossingSign D c = Sign.pos) (b : Fin 2)
    (R : ∀ C : diagramComponent (smoothCrossing D c),
      ComponentRestriction (smoothCrossing D c) C)
    (FL FR : Polynomial ℤ)
    (hL : let L := R (rootSelfCutComponents D c (hconn _ _) b (Sum.inl false));
      framedKnotRow Gemini.candidateEvaluator L.diagram L.nonempty
        (PermutationOrbits.componentOf L.diagram.continuation ⟨0,L.nonempty⟩) =
          framedVariable * polynomialValue FL)
    (hR : let E := R (rootSelfCutComponents D c (hconn _ _) b (Sum.inl true));
      framedKnotRow Gemini.candidateEvaluator E.diagram E.nonempty
        (PermutationOrbits.componentOf E.diagram.continuation ⟨0,E.nonempty⟩) =
          framedVariable * polynomialValue FR) :
    let L := R (rootSelfCutComponents D c (hconn _ _) b (Sum.inl false));
    let E := R (rootSelfCutComponents D c (hconn _ _) b (Sum.inl true));
    -coeff (framedKnotRow Gemini.candidateEvaluator D hD
        (PermutationOrbits.componentOf D.continuation ⟨0,hD⟩)) 0 0 =
      -coeff (framedKnotRow Gemini.candidateEvaluator (switchCrossing D c) hD
        (PermutationOrbits.componentOf (switchCrossing D c).continuation ⟨0,hD⟩)) 0 0 -
      (-coeff (framedKnotRow Gemini.candidateEvaluator L.diagram L.nonempty
        (PermutationOrbits.componentOf L.diagram.continuation ⟨0,L.nonempty⟩)) 0 0) *
      (-coeff (framedKnotRow Gemini.candidateEvaluator E.diagram E.nonempty
        (PermutationOrbits.componentOf E.diagram.continuation ⟨0,E.nonempty⟩)) 0 0) := by
  exact polynomialWitness_subtraction _ _ _ _ FL FR hL hR
    (positive_connected_framed_knot_row D hD hconn c hpos b R)

theorem exposed_terminal_negative_constant
    (H : Evaluator) (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D)
    (hconn : ∀ a b : Fin D.nArc, D.continuation.SameCycle a b)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C)
    (hterminal : ∀ c : Fin D.nCrossing, ¬ badAt T c) :
    -coeff (framedKnotRow H D hD C) 0 0 = 1 := by
  rw [framedKnotRow_exposed_terminal H hH D hD T hconn C hhalf hterminal]
  exact framedVariable_negative_constant

end DirectGLSSW.HOMFLY.FramedPolynomial
