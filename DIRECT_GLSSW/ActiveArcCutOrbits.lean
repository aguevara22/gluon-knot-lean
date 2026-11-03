import ActiveArcCutSuccessor
import DirectGLSSW.OrbitWordPrerequisite
import DirectGLSSW.DaughterPointListFilter

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive DaughterFirstReturn PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e)
variable (S : Finset (ActiveArc.Crossing (cutArc q e)))

theorem eventEquiv_incoming (x : ActiveArc.Event (cutArc q e)) :
    eventEquiv q e hq he (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S x)=
      smoothingIncomingPermutation q hq.g2 (mappedSupport q e hq he S) (eventEquiv q e hq he x) := by
  change eventEquiv q e hq he
    (ActiveArc.successor (cutArc q e) (cutArc_regular q e hq).noTriple (ActiveArc.pairing (cutArc q e) S x))=_
  rw [← eventEquiv_successor,← eventEquiv_pairing]
  rfl

/-- Incoming-to-dart transport uses the actual pairing, not an equality of conventions. -/
def dartEventEquiv : ActiveArc.Event (cutArc q e) ≃ PolygonEvent q :=
  (eventEquiv q e hq he).trans (smoothingPairing q (mappedSupport q e hq he S))

theorem dartEventEquiv_intertwine (x : ActiveArc.Event (cutArc q e)) :
    dartEventEquiv q e hq he S (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S x)=
      smoothingDartPermutation q hq.g2 (mappedSupport q e hq he S) (dartEventEquiv q e hq he S x) := by
  change smoothingPairing q (mappedSupport q e hq he S)
      (eventEquiv q e hq he (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S x))=_
  rw [eventEquiv_incoming]
  exact (smoothingPermutation_intertwine q hq.g2 (mappedSupport q e hq he S) (eventEquiv q e hq he x)).symm

theorem dartEventEquiv_point (x : ActiveArc.Event (cutArc q e)) :
    polygonEventPoint q (dartEventEquiv q e hq he S x)=ActiveArc.eventPoint (cutArc q e) x := by
  change polygonEventPoint q (smoothingPairing q _ (eventEquiv q e hq he x))=_
  rw [smoothingPairing_point,eventEquiv_point]

theorem pairing_retained (T : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    retainedCorner q T (smoothingPairing q T x) ↔ retainedCorner q T x := by
  classical
  cases x with
  | inl i => rfl
  | inr v =>
    change retainedCorner q T (if v.1∈T then Sum.inr (crossingVisitFlip q v) else Sum.inr v) ↔ _
    split_ifs <;> rfl

theorem dartEventEquiv_retained (x : ActiveArc.Event (cutArc q e)) :
    retainedCorner q (mappedSupport q e hq he S) (dartEventEquiv q e hq he S x) ↔
      ActiveArc.retained (cutArc q e) S x := by
  change retainedCorner q _ (smoothingPairing q _ (eventEquiv q e hq he x)) ↔ _
  rw [pairing_retained,eventEquiv_retained]

/-- Every genuine incoming component corresponds to its actual parent dart component. -/
def dartComponentEquiv :
    Component (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S) ≃
      Component (smoothingDartPermutation q hq.g2 (mappedSupport q e hq he S)) :=
  componentEquivOfIntertwining (dartEventEquiv q e hq he S) _ _ (dartEventEquiv_intertwine q e hq he S)

theorem dartComponentEquiv_componentOf (x : ActiveArc.Event (cutArc q e)) :
    dartComponentEquiv q e hq he S (componentOf (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S) x)=
      componentOf (smoothingDartPermutation q hq.g2 (mappedSupport q e hq he S)) (dartEventEquiv q e hq he S x) := rfl

/-- Transport the whole ordered orbit word through the actual dart equivalence. -/
theorem dart_orbitWord (x : ActiveArc.Event (cutArc q e)) :
    orbitWord (smoothingDartPermutation q hq.g2 (mappedSupport q e hq he S)) (dartEventEquiv q e hq he S x)=
      (orbitWord (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S) x).map (dartEventEquiv q e hq he S) := by
  let p := ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S
  let E := dartEventEquiv q e hq he S
  let f := fun i : Fin (Fintype.card (Fibre p (componentOf p x))) => E (orbitEnumeration p x i).val
  have hf : Function.Injective f := by
    intro i j hh
    apply (orbitEnumeration p x).injective
    apply Subtype.ext
    exact E.injective hh
  have hs : ∀ i, smoothingDartPermutation q hq.g2 (mappedSupport q e hq he S) (f i)=f (cyclicSuccessor i) := by
    intro i
    have hh := congrArg Subtype.val (orbitEnumeration_successor p x i)
    change (orbitEnumeration p x (cyclicSuccessor i)).val=p (orbitEnumeration p x i).val at hh
    change _=E (orbitEnumeration p x (cyclicSuccessor i)).val
    rw [hh]
    exact (dartEventEquiv_intertwine q e hq he S _).symm
  have hw := orbitWord_eq_of_injective_cyclicSuccessor
    (smoothingDartPermutation q hq.g2 (mappedSupport q e hq he S)) Fintype.card_pos f hf hs
  simpa [f,E,p,orbitWord,List.map_ofFn] using hw

/-- Exact filtered physical point-word equality, including its actual chosen root. -/
theorem daughterPointList_eq_active_filtered (x : ActiveArc.Event (cutArc q e)) :
    daughterPointList q hq.g2 (mappedSupport q e hq he S) (dartEventEquiv q e hq he S x)=
      ((orbitWord (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S) x).filter
        (fun z => decide (ActiveArc.retained (cutArc q e) S z))).map (ActiveArc.eventPoint (cutArc q e)) := by
  classical
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,dart_orbitWord]
  rw [← DaughterPointListFilter.map_filter_comp]
  simp only [List.map_map]
  congr 1
  · funext z
    exact dartEventEquiv_point q e hq he S z
  · congr 1
    funext z
    simp only [dartEventEquiv_retained]

end DirectGLSSW.ActiveArc.ExposedChart
