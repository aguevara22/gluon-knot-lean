import DirectGLSSW.SpectatorDaughterWords

set_option autoImplicit false
namespace DirectGLSSW.SpectatorProductFactorization
open PrimitiveEdgeGrouping SpectatorDaughterWords PermutationOrbits GeometricSmoothingWeights
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (e : Fin n) (U : OffEdgeSupport P hP e) (T : EdgeCompletion P hP e U)

def edgeComponent : Component (smoothingDartPermutation P hP.g2 U.val) :=
  componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)

theorem completion_pairing_preserves_old_component (x : PolygonEvent P) :
    componentOf (smoothingDartPermutation P hP.g2 U.val) (smoothingPairing P T.val x) =
      componentOf (smoothingDartPermutation P hP.g2 U.val) x := by
  cases x with
  | inl a => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    by_cases hc : c ∈ T.val
    · obtain ⟨h₀,h₁⟩ := completion_dart_visits_in_edge_component P hP e U T c hc
      cases b <;> simp only [smoothingPairing_apply,smoothingPairingMap_visit,
        if_pos hc,crossingVisitFlip,Bool.not_false,Bool.not_true,h₀,h₁]
    · rw [(smoothingPairing_visit_fixed_iff P T.val (c,b)).mpr hc]

theorem completion_dart_preserves_old_component (x : PolygonEvent P) :
    componentOf (smoothingDartPermutation P hP.g2 U.val)
        (smoothingDartPermutation P hP.g2 (U.val ∪ T.val) x) =
      componentOf (smoothingDartPermutation P hP.g2 U.val) x := by
  rw [smoothingDartPermutation_union P hP.g2 U.val T.val (off_on_disjoint P hP e U T)]
  rw [Equiv.Perm.mul_apply,completion_pairing_preserves_old_component,componentOf_apply]

/-- The old component containing an actual final smoothing component. -/
def oldComponentOfFinal :
    Component (smoothingDartPermutation P hP.g2 (U.val ∪ T.val)) →
      Component (smoothingDartPermutation P hP.g2 U.val) :=
  Quotient.lift (componentOf (smoothingDartPermutation P hP.g2 U.val))
    (fun _ _ h => IndexedInvariantPartition.index_eq_of_sameCycle
      (smoothingDartPermutation P hP.g2 (U.val ∪ T.val))
      (componentOf (smoothingDartPermutation P hP.g2 U.val))
      (completion_dart_preserves_old_component P hP e U T) h)

@[simp] theorem oldComponentOfFinal_componentOf (x : PolygonEvent P) :
    oldComponentOfFinal P hP e U T
      (componentOf (smoothingDartPermutation P hP.g2 (U.val ∪ T.val)) x) =
    componentOf (smoothingDartPermutation P hP.g2 U.val) x := rfl

def OldSpectator := {B : Component (smoothingDartPermutation P hP.g2 U.val) //
  B ≠ edgeComponent P hP e U}

def AffectedFinal := {C : Component (smoothingDartPermutation P hP.g2 (U.val ∪ T.val)) //
  oldComponentOfFinal P hP e U T C = edgeComponent P hP e U}

instance oldSpectatorFintype : Fintype (OldSpectator P hP e U) := by
  unfold OldSpectator
  infer_instance

instance affectedFinalFintype : Fintype (AffectedFinal P hP e U T) := by
  unfold AffectedFinal
  infer_instance

def spectatorLift (B : OldSpectator P hP e U) :
    Component (smoothingDartPermutation P hP.g2 (U.val ∪ T.val)) :=
  componentOf (smoothingDartPermutation P hP.g2 (U.val ∪ T.val))
    (componentRoot P hP U.val B.val)

@[simp] theorem oldComponentOfFinal_spectatorLift (B : OldSpectator P hP e U) :
    oldComponentOfFinal P hP e U T (spectatorLift P hP e U T B) = B.val := by
  exact componentRoot_sameComponent P hP U.val B.val

theorem spectator_lift_old_component
    (C : Component (smoothingDartPermutation P hP.g2 (U.val ∪ T.val)))
    (hC : oldComponentOfFinal P hP e U T C ≠ edgeComponent P hP e U) :
    spectatorLift P hP e U T ⟨oldComponentOfFinal P hP e U T C,hC⟩ = C := by
  induction C using Quotient.inductionOn with
  | h x =>
    let p := smoothingDartPermutation P hP.g2 U.val
    let r := componentRoot P hP U.val (componentOf p x)
    have hr : componentOf p r = componentOf p x :=
      componentRoot_sameComponent P hP U.val (componentOf p x)
    have hrne : componentOf p r ≠ edgeComponent P hP e U := by
      rw [hr]
      exact hC
    have hmem : x ∈ orbitWord p r :=
      (mem_orbitWord_iff _ _ _).mpr ((componentOf_eq_iff _ _ _).mp hr)
    rw [← spectator_orbitWord_eq P hP e U T r hrne] at hmem
    exact (componentOf_eq_iff _ _ _).mpr ((mem_orbitWord_iff _ _ _).mp hmem)

/-- Explicit partition into unchanged old spectators and all affected final components. -/
def componentPartition :
    OldSpectator P hP e U ⊕ AffectedFinal P hP e U T ≃
      Component (smoothingDartPermutation P hP.g2 (U.val ∪ T.val)) where
  toFun := Sum.elim (spectatorLift P hP e U T) Subtype.val
  invFun C := if h : oldComponentOfFinal P hP e U T C = edgeComponent P hP e U
    then Sum.inr ⟨C,h⟩ else Sum.inl ⟨oldComponentOfFinal P hP e U T C,h⟩
  left_inv := by
    intro s
    cases s with
    | inl B =>
      simp only [Sum.elim_inl,oldComponentOfFinal_spectatorLift,dif_neg B.property]
      rfl
    | inr C =>
      simp only [Sum.elim_inr,dif_pos C.property]
      rfl
  right_inv := by
    intro C
    dsimp only
    split_ifs with h
    · rfl
    · exact spectator_lift_old_component P hP e U T C h

@[simp] theorem componentPartition_inl (B : OldSpectator P hP e U) :
    componentPartition P hP e U T (Sum.inl B) = spectatorLift P hP e U T B := rfl

@[simp] theorem componentPartition_inr (C : AffectedFinal P hP e U T) :
    componentPartition P hP e U T (Sum.inr C) = C.val := rfl

theorem spectatorLift_amplitude (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity P hP) (B : OldSpectator P hP e U) :
    componentAmplitude P hP (U.val ∪ T.val) hAux T.property.2
      (spectatorLift P hP e U T B) = componentAmplitude P hP U.val hAux U.property.1 B.val := by
  have hx : componentOf (smoothingDartPermutation P hP.g2 U.val)
      (componentRoot P hP U.val B.val) ≠ edgeComponent P hP e U := by
    rw [componentRoot_sameComponent]
    exact B.property
  have h := spectator_componentAmplitude_eq P hP e U T hRI hAux
    (componentRoot P hP U.val B.val) hx
  rw [componentRoot_sameComponent] at h
  exact h

/-- Actual spectator factors are independent of the on-edge completion. -/
theorem componentAmplitudeProduct_factor_spectators (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity P hP) :
    componentAmplitudeProduct P hP (U.val ∪ T.val) hAux T.property.2 =
      (∏ B : OldSpectator P hP e U, componentAmplitude P hP U.val hAux U.property.1 B.val) *
      (∏ C : AffectedFinal P hP e U T,
        componentAmplitude P hP (U.val ∪ T.val) hAux T.property.2 C.val) := by
  let w := componentAmplitude P hP (U.val ∪ T.val) hAux T.property.2
  have h := Fintype.prod_equiv (componentPartition P hP e U T)
    (fun s => w (componentPartition P hP e U T s)) w (fun _ => rfl)
  change (∏ C, w C) = _
  rw [← h,Fintype.prod_sum_type]
  simp only [componentPartition_inl,componentPartition_inr]
  apply congrArg₂ (fun a b : ℚ => a*b)
  · apply Finset.prod_congr rfl
    intro B _
    exact spectatorLift_amplitude P hP e U T hRI hAux B
  · rfl


















end
end DirectGLSSW.SpectatorProductFactorization
