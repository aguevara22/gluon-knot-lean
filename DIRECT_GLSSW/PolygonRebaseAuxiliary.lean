import PolygonRebaseTurning
import DirectGLSSW.GeometricSmoothingWeights
import DirectGLSSW.PolygonNonalternation
import DirectGLSSW.DaughterPointListFilter
import DirectGLSSW.TruncationPointListAdapter
import DirectGLSSW.ChordNonalternation
import NonalternatingBranchOrder

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.PolygonRebase
open DirectGLSSW HOMFLY.PolygonDrawingBridge PolygonNonalternation
  DaughterFirstReturn PermutationOrbits GeometricSmoothingWeights
  ChordNonalternation FiniteCycleOrder
attribute [local instance] Classical.propDecidable

private theorem nonalternating_circular_relabel_iff
    {C D : Type*} [DecidableEq C] [DecidableEq D] {m k : ℕ}
    (e : C × Bool → Fin m) (he : Function.Injective e)
    (f : D × Bool → Fin k) (hf : Function.Injective f)
    (g : C ≃ D) (β : C → Equiv.Perm Bool)
    (hbetween : ∀ x y z : C × Bool,
      strictCyclicBetween (e x) (e y) (e z) ↔
        strictCyclicBetween (f (g x.1, β x.1 x.2))
          (f (g y.1, β y.1 y.2)) (f (g z.1, β z.1 z.2)) )
    (S : Finset C) :
    Nonalternating e S ↔ Nonalternating f (S.map g.toEmbedding) := by
  classical
  let eβ : C × Bool → Fin k := fun x => f (g x.1, β x.1 x.2)
  let β' : D → Equiv.Perm Bool := fun d => β (g.symm d)
  let fβ : D × Bool → Fin k := fun x => f (x.1, β' x.1 x.2)
  let T : Finset D := S.map g.toEmbedding
  have hOrder : Nonalternating e S ↔ Nonalternating eβ S := by
    unfold Nonalternating
    constructor
    · intro h c hc d hd hcd
      have h0 := hbetween (c,false) (d,false) (c,true)
      have h1 := hbetween (c,false) (d,true) (c,true)
      exact h0.symm.trans ((h c hc d hd hcd).trans h1)
    · intro h c hc d hd hcd
      have h0 := hbetween (c,false) (d,false) (c,true)
      have h1 := hbetween (c,false) (d,true) (c,true)
      exact h0.trans ((h c hc d hd hcd).trans h1.symm)
  have hmatch (c : C) (b : Bool) : eβ (c,b) = fβ (g c,b) := by
    simp [eβ, fβ, β', Equiv.apply_symm_apply]
  have hfβ : Function.Injective fβ := by
    intro x y hxy
    have hp : (x.1, β' x.1 x.2) = (y.1, β' y.1 y.2) := hf (by simpa [fβ] using hxy)
    have hfst := congrArg Prod.fst hp
    have hsnd := congrArg Prod.snd hp
    have hb : x.2 = y.2 := by rw [hfst] at hsnd; exact (β' y.1).injective hsnd
    exact Prod.ext hfst hb
  have hmap : Nonalternating eβ S ↔ Nonalternating fβ T := by
    unfold Nonalternating
    constructor
    · intro h d hd d' hd' hdd
      rcases Finset.mem_map.mp hd with ⟨c,hc,rfl⟩
      rcases Finset.mem_map.mp hd' with ⟨c',hc',rfl⟩
      have hcc' : c ≠ c' := fun heq => hdd (congrArg g heq)
      simpa only [hmatch] using h c hc c' hc' hcc'
    · intro h c hc c' hc' hcc'
      have hgg : g c ≠ g c' := fun heq => hcc' (g.injective heq)
      have hh := h (g c) (Finset.mem_map.mpr ⟨c,hc,rfl⟩)
        (g c') (Finset.mem_map.mpr ⟨c',hc',rfl⟩) hgg
      simpa only [hmatch] using hh
  let βinv : D → Equiv.Perm Bool := fun d => (β' d).symm
  have hflip := nonalternating_endpoint_relabel_iff fβ hfβ βinv T
  have hflip' : Nonalternating fβ T ↔ Nonalternating f T := by
    simpa [fβ, βinv] using hflip
  exact hOrder.trans (hmap.trans hflip')

theorem polygonNonalternating_relabel
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n) (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (S' : Finset (PolygonCrossing (q ∘ ρ))) :
    polygonNonalternating (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq).g2 S' ↔
      polygonNonalternating q hq.g2 (S'.map (crossingEquiv q ρ hρ).toEmbedding) := by
  classical
  let hQ := cyclicGeneric_relabel q ρ hρ hq
  let E := crossingEquiv q ρ hρ
  let F := eventEquiv q ρ hρ
  let β := branchBool q ρ
  let es := actualEndpoint (q ∘ ρ) hQ.g2
  let et := actualEndpoint q hq.g2
  letI : LinearOrder (PolygonEvent (q ∘ ρ)) := polygonEventOrder (q ∘ ρ) hQ.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  let a : PolygonEvent (q ∘ ρ) := Sum.inl (ρ.symm ⟨0,by have := hq.size_ge_three; omega⟩)
  have horder (x y : PolygonEvent (q ∘ ρ)) :
      F x < F y ↔ (a ≤ x ∧ y < a) ∨ ((x < a ↔ y < a) ∧ x < y) := by
    exact event_order_cut q hq ρ hρ x y
  have hcircle (x y z : PolygonEvent (q ∘ ρ)) :
      strictCyclicBetween (F x) (F y) (F z) ↔ strictCyclicBetween x y z :=
    strictCyclicBetween_block_rotation F a horder x y z
  have hbetween (x y z : PolygonCrossing (q ∘ ρ) × Bool) :
      strictCyclicBetween (es x) (es y) (es z) ↔
        strictCyclicBetween (et (E x.1, β x.1 x.2))
          (et (E y.1, β y.1 y.2)) (et (E z.1, β z.1 z.2)) := by
    letI : LinearOrder (Fin n ⊕ CrossingVisit (q ∘ ρ)) :=
      polygonEventOrder (q ∘ ρ) hQ.g2
    letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
    have hs : strictCyclicBetween (es x) (es y) (es z) ↔
        strictCyclicBetween (Sum.inr x : PolygonEvent (q ∘ ρ))
          (Sum.inr y : PolygonEvent (q ∘ ρ)) (Sum.inr z : PolygonEvent (q ∘ ρ)) := by
      have hraw := strictCyclicBetween_orderIso
        (DirectGLSSW.polygonEventEnumeration (q ∘ ρ) hQ.g2) (es x) (es y) (es z)
      have hx : DirectGLSSW.polygonEventEnumeration (q ∘ ρ) hQ.g2 (es x) = Sum.inr x := by
        simp [es, PolygonNonalternation.eventEnumeration_actualEndpoint,
          PolygonNonalternation.actualEndpoint, PolygonNonalternation.eventEnumeration]
      have hy : DirectGLSSW.polygonEventEnumeration (q ∘ ρ) hQ.g2 (es y) = Sum.inr y := by
        simp [es, PolygonNonalternation.eventEnumeration_actualEndpoint,
          PolygonNonalternation.actualEndpoint, PolygonNonalternation.eventEnumeration]
      have hz : DirectGLSSW.polygonEventEnumeration (q ∘ ρ) hQ.g2 (es z) = Sum.inr z := by
        simp [es, PolygonNonalternation.eventEnumeration_actualEndpoint,
          PolygonNonalternation.actualEndpoint, PolygonNonalternation.eventEnumeration]
      rw [hx, hy, hz] at hraw
      exact hraw.symm
    have ht : strictCyclicBetween (Sum.inr (E x.1, β x.1 x.2) : PolygonEvent q)
        (Sum.inr (E y.1, β y.1 y.2) : PolygonEvent q)
        (Sum.inr (E z.1, β z.1 z.2) : PolygonEvent q) ↔
        strictCyclicBetween (et (E x.1, β x.1 x.2))
          (et (E y.1, β y.1 y.2)) (et (E z.1, β z.1 z.2)) := by
      have hraw := strictCyclicBetween_orderIso
        (DirectGLSSW.polygonEventEnumeration q hq.g2)
        (et (E x.1, β x.1 x.2)) (et (E y.1, β y.1 y.2)) (et (E z.1, β z.1 z.2))
      have hx : DirectGLSSW.polygonEventEnumeration q hq.g2
          (et (E x.1, β x.1 x.2)) = Sum.inr (E x.1, β x.1 x.2) := by
        simp [et, PolygonNonalternation.eventEnumeration_actualEndpoint,
          PolygonNonalternation.actualEndpoint, PolygonNonalternation.eventEnumeration]
      have hy : DirectGLSSW.polygonEventEnumeration q hq.g2
          (et (E y.1, β y.1 y.2)) = Sum.inr (E y.1, β y.1 y.2) := by
        simp [et, PolygonNonalternation.eventEnumeration_actualEndpoint,
          PolygonNonalternation.actualEndpoint, PolygonNonalternation.eventEnumeration]
      have hz : DirectGLSSW.polygonEventEnumeration q hq.g2
          (et (E z.1, β z.1 z.2)) = Sum.inr (E z.1, β z.1 z.2) := by
        simp [et, PolygonNonalternation.eventEnumeration_actualEndpoint,
          PolygonNonalternation.actualEndpoint, PolygonNonalternation.eventEnumeration]
      rw [hx, hy, hz] at hraw
      exact hraw
    have hevent := hcircle (Sum.inr x : PolygonEvent (q ∘ ρ))
      (Sum.inr y : PolygonEvent (q ∘ ρ)) (Sum.inr z : PolygonEvent (q ∘ ρ))
    simpa only [F, eventEquiv, visitEquiv, E, β] using hs.trans (hevent.symm.trans ht)
  have hsrc : Function.Injective es := PolygonNonalternation.actualEndpoint_injective _ _
  have hdst : Function.Injective et := PolygonNonalternation.actualEndpoint_injective _ _
  have habs := nonalternating_circular_relabel_iff es hsrc et hdst E β hbetween S'
  rw [← polygonNonalternating_iff_abstract, ← polygonNonalternating_iff_abstract] at habs
  exact habs

theorem eventEquiv_pairing_relabel
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n) (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (S' : Finset (PolygonCrossing (q ∘ ρ)))
    (x : PolygonEvent (q ∘ ρ)) :
    smoothingPairing q (S'.map (crossingEquiv q ρ hρ).toEmbedding) (eventEquiv q ρ hρ x) =
      eventEquiv q ρ hρ (smoothingPairing (q ∘ ρ) S' x) := by
  classical
  let E := crossingEquiv q ρ hρ
  let β := branchBool q ρ
  cases x with
  | inl e => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    have hF (v : CrossingVisit (q ∘ ρ)) :
        eventEquiv q ρ hρ (Sum.inr v) = Sum.inr (visitEquiv q ρ hρ v) := rfl
    change smoothingPairingMap q (S'.map E.toEmbedding)
        (eventEquiv q ρ hρ (Sum.inr (c,b))) =
      eventEquiv q ρ hρ (smoothingPairingMap (q ∘ ρ) S' (Sum.inr (c,b)))
    rw [hF, smoothingPairingMap_visit, smoothingPairingMap_visit]
    have hmem : (visitEquiv q ρ hρ (c,b)).1 ∈ S'.map E.toEmbedding ↔ c ∈ S' := by
      simp [visitEquiv, E]
    have hflip : visitEquiv q ρ hρ (c,!b) =
        crossingVisitFlip q (visitEquiv q ρ hρ (c,b)) := by
      cases b <;> by_cases ho : ρ c.val.1 < ρ c.val.2 <;>
        simp [visitEquiv, branchBool, crossingVisitFlip, ho]
    by_cases hc : c ∈ S'
    · rw [if_pos (hmem.mpr hc), if_pos hc]
      have hFflip : eventEquiv q ρ hρ
          (Sum.inr (crossingVisitFlip (q ∘ ρ) (c,b))) =
            Sum.inr (visitEquiv q ρ hρ (c,!b)) := rfl
      rw [hFflip]
      exact congrArg Sum.inr hflip.symm
    · rw [if_neg (mt hmem.mp hc), if_neg hc]
      rfl

private theorem eventEquiv_smoothingDart
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n) (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (S' : Finset (PolygonCrossing (q ∘ ρ))) (x : PolygonEvent (q ∘ ρ)) :
    eventEquiv q ρ hρ (smoothingDartPermutation (q ∘ ρ)
      (cyclicGeneric_relabel q ρ hρ hq).g2 S' x) =
      smoothingDartPermutation q hq.g2 (S'.map (crossingEquiv q ρ hρ).toEmbedding)
        (eventEquiv q ρ hρ x) := by
  rw [smoothingDartPermutation_apply, smoothingDartPermutation_apply]
  rw [← eventEquiv_successor q hq ρ hρ x]
  exact (eventEquiv_pairing_relabel q hq ρ hρ S'
    (polygonEventSuccessor (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq).g2 x)).symm

theorem daughterPointList_relabel
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n) (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (S' : Finset (PolygonCrossing (q ∘ ρ)))
    (root : PolygonEvent (q ∘ ρ)) :
    daughterPointList q hq.g2 (S'.map (crossingEquiv q ρ hρ).toEmbedding)
        (eventEquiv q ρ hρ root) =
      daughterPointList (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq).g2 S' root := by
  classical
  let E := crossingEquiv q ρ hρ
  let F := eventEquiv q ρ hρ
  let S := S'.map E.toEmbedding
  let p' := smoothingDartPermutation (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq).g2 S'
  let p := smoothingDartPermutation q hq.g2 S
  have hword : orbitWord p (F root) = (orbitWord p' root).map F := by
    let f := fun i : Fin (Fintype.card (Fibre p' (componentOf p' root))) =>
      F (orbitEnumeration p' root i).val
    have hf : Function.Injective f := by
      intro i j hij
      apply (orbitEnumeration p' root).injective
      apply Subtype.ext
      exact F.injective hij
    have hs : ∀ i, p (f i) = f (cyclicSuccessor i) := by
      intro i
      have hi := congrArg Subtype.val (orbitEnumeration_successor p' root i)
      change (orbitEnumeration p' root (cyclicSuccessor i)).val = p' (orbitEnumeration p' root i).val at hi
      change p (F (orbitEnumeration p' root i).val) = F (orbitEnumeration p' root (cyclicSuccessor i)).val
      rw [← eventEquiv_smoothingDart q hq ρ hρ S' (orbitEnumeration p' root i).val]
      exact congrArg F hi.symm
    have hw := orbitWord_eq_of_injective_cyclicSuccessor p
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fibre p' (componentOf p' root))))
      f hf hs
    simpa [orbitWord,f,PermutationOrbits.orbitEnumeration_apply_val] using hw
  have hret (x : PolygonEvent (q ∘ ρ)) :
      retainedCorner q S (F x) ↔ retainedCorner (q ∘ ρ) S' x := by
    cases x with
    | inl e => rfl
    | inr v =>
      rcases v with ⟨c,b⟩
      change (crossingEquiv q ρ hρ c) ∈ S ↔ c ∈ S'
      simp [S, E]
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map]
  rw [hword]
  have hpred : (fun x => decide (retainedCorner (q ∘ ρ) S' x)) =
      (fun x => decide (retainedCorner q S (F x))) := by
    funext x
    by_cases hx : retainedCorner (q ∘ ρ) S' x <;> simp [hx, hret x]
  rw [hpred]
  have hfiltered := DaughterPointListFilter.map_filter_comp F
    (fun x => decide (retainedCorner q S x)) (orbitWord p' root)
  rw [← hfiltered, List.map_map]
  have hpoints : (polygonEventPoint q) ∘ F = polygonEventPoint (q ∘ ρ) := by
    funext x
    exact eventEquiv_point q ρ hρ hq x
  rw [hpoints]

theorem auxiliaryGenericity_relabel
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n) (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (hAux : auxiliaryGenericity q hq) :
    auxiliaryGenericity (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq) := by
  classical
  intro S' hS' root
  have hS : polygonNonalternating q hq.g2 (S'.map (crossingEquiv q ρ hρ).toEmbedding) :=
    (polygonNonalternating_relabel q hq ρ hρ S').mp hS'
  have hD := hAux (S'.map (crossingEquiv q ρ hρ).toEmbedding) hS (eventEquiv q ρ hρ root)
  exact TruncationPointListAdapter.cyclicGeneric_of_pointList_eq _ _ hD
    (by simpa [DaughterFirstReturn.daughterPointList] using
      daughterPointList_relabel q hq ρ hρ S' root)

end DirectGLSSW.PolygonRebase
