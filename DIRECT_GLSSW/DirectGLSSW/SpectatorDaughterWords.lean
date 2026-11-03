import DirectGLSSW.UncutEdgeComponent
import DirectGLSSW.OrbitWordPrerequisite
import DirectGLSSW.DaughterPointListFilter
import DirectGLSSW.TruncationComponentWeights
import DirectGLSSW.TruncationPointListAdapter

set_option autoImplicit false
namespace DirectGLSSW.SpectatorDaughterWords
open PrimitiveEdgeGrouping UncutEdgeComponent PermutationOrbits DaughterFirstReturn
open GeometricSmoothingWeights
noncomputable section
attribute [local instance] Classical.propDecidable

theorem orbitWord_eq_of_agree_on_component {α : Type*} [Fintype α]
    (p q : Equiv.Perm α) (x : α)
    (hagree : ∀ y, componentOf p y = componentOf p x → q y = p y) :
    orbitWord q x = orbitWord p x := by
  letI : Nonempty (Fibre p (componentOf p x)) := ⟨⟨x,rfl⟩⟩
  have hN : 0 < Fintype.card (Fibre p (componentOf p x)) := Fintype.card_pos
  let f := fun i => (orbitEnumeration p x i).val
  have hf : Function.Injective f := Subtype.val_injective.comp (orbitEnumeration p x).injective
  have hstep : ∀ i, q (f i) = f (cyclicSuccessor i) := by
    intro i
    rw [hagree (f i) (orbitEnumeration p x i).property]
    have hs := congrArg Subtype.val (orbitEnumeration_successor p x i)
    exact hs.symm
  have hw := orbitWord_eq_of_injective_cyclicSuccessor q hN f hf hstep
  simpa only [orbitWord,f,orbitEnumeration_apply_val,Fin.val_zero,pow_zero,Equiv.Perm.one_apply]
    using hw

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (e : Fin n) (U : OffEdgeSupport P hP e) (T : EdgeCompletion P hP e U)

theorem completion_dart_visits_in_edge_component (c : PolygonCrossing P) (hc : c ∈ T.val) :
    componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inr (c,false)) =
        componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e) ∧
    componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inr (c,true)) =
        componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e) := by
  obtain ⟨ha,hb⟩ := completion_visits_in_edge_component P hP e U T c hc
  have hcU : c ∉ U.val := fun h => U.property.2 c h (T.property.1 c hc)
  have ha' := congrArg (smoothingComponentEquiv P hP.g2 U.val) ha
  have hb' := congrArg (smoothingComponentEquiv P hP.g2 U.val) hb
  constructor
  · simpa only [smoothingComponentEquiv_componentOf,
      (smoothingPairing_visit_fixed_iff P U.val (c,false)).mpr hcU,
      smoothingPairing_apply,smoothingPairingMap_anchor] using ha'
  · simpa only [smoothingComponentEquiv_componentOf,
      (smoothingPairing_visit_fixed_iff P U.val (c,true)).mpr hcU,
      smoothingPairing_apply,smoothingPairingMap_anchor] using hb'

theorem completion_pairing_fixes_dart_spectator (x : PolygonEvent P)
    (hx : componentOf (smoothingDartPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)) :
    smoothingPairing P T.val x = x := by
  cases x with
  | inl a => rfl
  | inr v =>
    apply (smoothingPairing_visit_fixed_iff P T.val v).mpr
    intro hc
    obtain ⟨ha,hb⟩ := completion_dart_visits_in_edge_component P hP e U T v.1 hc
    apply hx
    rcases v with ⟨c,b⟩
    cases b
    · exact ha
    · exact hb

theorem completion_dart_fixes_spectator (x : PolygonEvent P)
    (hx : componentOf (smoothingDartPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)) :
    smoothingDartPermutation P hP.g2 (U.val ∪ T.val) x =
      smoothingDartPermutation P hP.g2 U.val x := by
  rw [smoothingDartPermutation_union P hP.g2 U.val T.val (off_on_disjoint P hP e U T)]
  change smoothingPairing P T.val (smoothingDartPermutation P hP.g2 U.val x) = _
  apply completion_pairing_fixes_dart_spectator P hP e U T
  simpa only [componentOf_apply] using hx

theorem spectator_orbitWord_eq (x : PolygonEvent P)
    (hx : componentOf (smoothingDartPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)) :
    orbitWord (smoothingDartPermutation P hP.g2 (U.val ∪ T.val)) x =
      orbitWord (smoothingDartPermutation P hP.g2 U.val) x := by
  apply orbitWord_eq_of_agree_on_component
  intro y hy
  apply completion_dart_fixes_spectator P hP e U T y
  exact fun he => hx (hy.symm.trans he)

theorem spectator_retained_iff (x : PolygonEvent P)
    (hx : componentOf (smoothingDartPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)) :
    retainedCorner P (U.val ∪ T.val) x ↔ retainedCorner P U.val x := by
  cases x with
  | inl a => rfl
  | inr v =>
    have hv : v.1 ∉ T.val := by
      intro hc
      obtain ⟨ha,hb⟩ := completion_dart_visits_in_edge_component P hP e U T v.1 hc
      apply hx
      rcases v with ⟨c,b⟩
      cases b
      · exact ha
      · exact hb
    simp only [retainedCorner,Finset.mem_union,hv,or_false]

/-- The spectator's entire retained geometry, including its root order, is unchanged. -/
theorem spectator_daughterPointList_eq (x : PolygonEvent P)
    (hx : componentOf (smoothingDartPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)) :
    daughterPointList P hP.g2 (U.val ∪ T.val) x = daughterPointList P hP.g2 U.val x := by
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    spectator_orbitWord_eq P hP e U T x hx]
  apply congrArg (List.map (polygonEventPoint P))
  apply List.filter_congr
  intro y hy
  have hyc : componentOf (smoothingDartPermutation P hP.g2 U.val) y =
      componentOf (smoothingDartPermutation P hP.g2 U.val) x :=
    ((componentOf_eq_iff _ _ _).mpr ((mem_orbitWord_iff _ _ _).mp hy)).symm
  have hyne := fun he => hx (hyc.symm.trans he)
  simp only [spectator_retained_iff P hP e U T y hyne]

theorem spectator_rooted_amplitude_eq (hAux : auxiliaryGenericity P hP)
    (x : PolygonEvent P)
    (hx : componentOf (smoothingDartPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)) :
    polygonAmplitude (daughterVertex P hP.g2 (U.val ∪ T.val) x)
      (hAux _ T.property.2 x) =
    polygonAmplitude (daughterVertex P hP.g2 U.val x) (hAux _ U.property.1 x) := by
  apply TruncationPointListAdapter.polygonAmplitude_eq_of_pointList_eq
  exact spectator_daughterPointList_eq P hP e U T x hx

/-- The selected quotient weights also agree, using only the authorized RI premise. -/
theorem spectator_componentAmplitude_eq (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity P hP) (x : PolygonEvent P)
    (hx : componentOf (smoothingDartPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)) :
    componentAmplitude P hP (U.val ∪ T.val) hAux T.property.2
      (componentOf (smoothingDartPermutation P hP.g2 (U.val ∪ T.val)) x) =
    componentAmplitude P hP U.val hAux U.property.1
      (componentOf (smoothingDartPermutation P hP.g2 U.val) x) := by
  rw [TruncationComponentWeights.componentAmplitude_eq_at_root hRI P hP _ hAux
      T.property.2 _ x rfl,
    TruncationComponentWeights.componentAmplitude_eq_at_root hRI P hP _ hAux
      U.property.1 _ x rfl]
  exact spectator_rooted_amplitude_eq P hP e U T hAux x hx










end
end DirectGLSSW.SpectatorDaughterWords
