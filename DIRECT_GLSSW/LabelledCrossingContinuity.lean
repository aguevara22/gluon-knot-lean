import CrossingIncidenceNeighborhood

set_option autoImplicit false
namespace DirectGLSSW.LabelledCrossingContinuity
open CrossingRationalParameters CrossingIncidenceNeighborhood
noncomputable section

/-- Identity on the actual unordered edge-pair labels, with transported intersection proofs. -/
def labelEquiv {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) :
    PolygonCrossing P ≃ PolygonCrossing Q where
  toFun c := ⟨c.val,c.property.1,(h c.val.1 c.val.2).mpr c.property.2⟩
  invFun c := ⟨c.val,c.property.1,(h c.val.1 c.val.2).mp c.property.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem labelEquiv_labels {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f)
    (c : PolygonCrossing P) : (labelEquiv P Q h c).val=c.val := rfl

/-- These are concrete facts, proved by the incidence-neighborhood construction;
this proposition only packages the input for the reusable continuity statements. -/
def StableBox {n : ℕ} (P : Configuration n) (η : ℝ) : Prop :=
  ∀ Q, CoordClose η Q P →
    (∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) ∧
    ∀ c : PolygonCrossing P, denominator Q c.val.1 c.val.2≠0

abbrev Box {n : ℕ} (P : Configuration n) (η : ℝ) :=
  {Q : Configuration n // CoordClose η Q P}

def boxCrossing {n : ℕ} (P : Configuration n) (η : ℝ) (hBox : StableBox P η)
    (Q : Box P η) (c : PolygonCrossing P) : PolygonCrossing Q.val :=
  labelEquiv P Q.val (hBox Q.val Q.property).1 c

theorem boxCrossing_parameters {n : ℕ} (P : Configuration n) (η : ℝ)
    (hBox : StableBox P η) (Q : Box P η) (c : PolygonCrossing P) :
    crossingParameterLeft Q.val (boxCrossing P η hBox Q c) =
      leftParameter Q.val c.val.1 c.val.2 ∧
    crossingParameterRight Q.val (boxCrossing P η hBox Q c) =
      rightParameter Q.val c.val.1 c.val.2 :=
  crossingParameters_eq Q.val (boxCrossing P η hBox Q c) ((hBox Q.val Q.property).2 c)

theorem continuous_box_leftParameter {n : ℕ} (P : Configuration n) (η : ℝ)
    (hBox : StableBox P η) (c : PolygonCrossing P) :
    Continuous (fun Q : Box P η => crossingParameterLeft Q.val (boxCrossing P η hBox Q c)) := by
  have heq : (fun Q : Box P η => crossingParameterLeft Q.val (boxCrossing P η hBox Q c)) =
      (fun Q : Box P η => leftParameter Q.val c.val.1 c.val.2) :=
    funext (fun Q => (boxCrossing_parameters P η hBox Q c).1)
  rw [heq]
  unfold leftParameter
  apply Continuous.div _ ((continuous_denominator c.val.1 c.val.2).comp continuous_subtype_val)
    (fun Q => (hBox Q.val Q.property).2 c)
  have hnum : Continuous (fun Q : Configuration n =>
      planarDet (Q c.val.2-Q c.val.1) (cyclicTangent Q c.val.2)) := by
    dsimp [cyclicTangent,planarDet]
    fun_prop
  exact hnum.comp continuous_subtype_val

theorem continuous_box_rightParameter {n : ℕ} (P : Configuration n) (η : ℝ)
    (hBox : StableBox P η) (c : PolygonCrossing P) :
    Continuous (fun Q : Box P η => crossingParameterRight Q.val (boxCrossing P η hBox Q c)) := by
  have heq : (fun Q : Box P η => crossingParameterRight Q.val (boxCrossing P η hBox Q c)) =
      (fun Q : Box P η => rightParameter Q.val c.val.1 c.val.2) :=
    funext (fun Q => (boxCrossing_parameters P η hBox Q c).2)
  rw [heq]
  unfold rightParameter
  apply Continuous.div _ ((continuous_denominator c.val.1 c.val.2).comp continuous_subtype_val)
    (fun Q => (hBox Q.val Q.property).2 c)
  have hnum : Continuous (fun Q : Configuration n =>
      planarDet (Q c.val.2-Q c.val.1) (cyclicTangent Q c.val.1)) := by
    dsimp [cyclicTangent,planarDet]
    fun_prop
  exact hnum.comp continuous_subtype_val

theorem continuous_box_crossingPoint {n : ℕ} (P : Configuration n) (η : ℝ)
    (hBox : StableBox P η) (c : PolygonCrossing P) :
    Continuous (fun Q : Box P η => crossingPoint Q.val (boxCrossing P η hBox Q c)) := by
  have heq : (fun Q : Box P η => crossingPoint Q.val (boxCrossing P η hBox Q c)) =
      (fun Q : Box P η => affinePoint (Q.val c.val.1) (Q.val (cyclicSuccessor c.val.1))
        (crossingParameterLeft Q.val (boxCrossing P η hBox Q c))) := by
    funext Q
    exact (crossingParameterLeft_spec Q.val (boxCrossing P η hBox Q c)).2.2
  rw [heq]
  have hL := continuous_box_leftParameter P η hBox c
  have he : Continuous (fun Q : Box P η => Q.val c.val.1) :=
    (continuous_apply c.val.1).comp continuous_subtype_val
  have hs : Continuous (fun Q : Box P η => Q.val (cyclicSuccessor c.val.1)) :=
    (continuous_apply (cyclicSuccessor c.val.1)).comp continuous_subtype_val
  exact (he.fst.add (hL.mul (hs.fst.sub he.fst))).prodMk
    (he.snd.add (hL.mul (hs.snd.sub he.snd)))









end
end DirectGLSSW.LabelledCrossingContinuity
