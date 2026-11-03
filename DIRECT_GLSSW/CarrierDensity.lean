import CarrierNumeratorPath
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CarrierDensity
open DirectGLSSW.AuxiliaryCarrierChart DirectGLSSW.CarrierNumeratorPath
open DirectGLSSW.CarrierWitnessEvaluation Set

def assignmentNumerator {α : Type*} (a b c d e f : α) (L : α → CarrierLine) : ℝ :=
  carrierTripleNumerator (L a) (L b) (L c) (L d) (L e) (L f)

theorem continuous_carrierPath (L M : CarrierLine) :
    Continuous (carrierPath L M) := by
  unfold carrierPath scalarPath
  fun_prop

theorem continuous_assignmentNumerator {α : Type*} (a b c d e f : α) :
    Continuous (assignmentNumerator a b c d e f) := by
  unfold assignmentNumerator carrierTripleNumerator lineNumerator lineDenominator planarDet
  fun_prop

theorem polynomial_nonzero_dense {p : Polynomial ℝ} (hp : p ≠ 0) :
    Dense {t : ℝ | p.eval t ≠ 0} := by
  have h := (dense_univ : Dense (univ : Set ℝ)).diff_finite
    (Polynomial.finite_setOf_isRoot hp)
  refine Dense.mono ?_ h
  intro t ht
  exact ht.2

theorem dense_assignmentNumerator_ne_zero {α : Type*} (a b c d e f : α)
    (M : α → CarrierLine) (hM : assignmentNumerator a b c d e f M ≠ 0) :
    Dense {L : α → CarrierLine | assignmentNumerator a b c d e f L ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hUn
  obtain ⟨L, hL⟩ := hUn
  let path : ℝ → (α → CarrierLine) := fun t x => carrierPath (L x) (M x) t
  have hpath : Continuous path := continuous_pi (fun x => continuous_carrierPath (L x) (M x))
  have hp : numeratorPathPolynomial L M a b c d e f ≠ 0 :=
    numeratorPathPolynomial_ne_zero L M a b c d e f hM
  have hpre : IsOpen (path ⁻¹' U) := hU.preimage hpath
  have hprene : (path ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [path, carrierPath, scalarPath] using hL
  obtain ⟨t, htU, htn⟩ := (polynomial_nonzero_dense hp).inter_open_nonempty
    (path ⁻¹' U) hpre hprene
  refine ⟨path t, htU, ?_⟩
  change assignmentNumerator a b c d e f (path t) ≠ 0
  have he := numeratorPathPolynomial_eval L M a b c d e f t
  change (numeratorPathPolynomial L M a b c d e f).eval t ≠ 0 at htn
  simpa only [he] using htn

theorem isOpen_assignmentNumerator_ne_zero {α : Type*} (a b c d e f : α) :
    IsOpen {L : α → CarrierLine | assignmentNumerator a b c d e f L ≠ 0} :=
  isOpen_ne_fun (continuous_assignmentNumerator a b c d e f) continuous_const

theorem daughter_triple_numerator_dense
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : DaughterFirstReturn.retainedCorner q S root)
    (i j k : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)))
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
    let prev : Fin m → Fin m := fun v => (cyclicSuccessorPerm m)⁻¹ v
    let car := DaughterFirstReturn.daughterCarrier q hG2 S root
    Dense {L : Fin n → CarrierLine |
      assignmentNumerator (car (prev i)) (car i) (car (prev j)) (car j)
        (car (prev k)) (car k) L ≠ 0} := by
  obtain ⟨M, hM⟩ := daughterCarrierTriple_has_nonzero_numerator
    q hG2 S hn hG1 hNA root hroot i j k hij hjk hik
  dsimp only
  exact dense_assignmentNumerator_ne_zero _ _ _ _ _ _ M hM

end DirectGLSSW.CarrierDensity







