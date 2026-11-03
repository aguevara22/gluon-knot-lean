import ActiveArcBeforeFirstSupport
import ActiveArcSingletonWords
import ActiveArcOrbitEmbedding

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.BeforeFirst
open DirectGLSSW ActiveArc PermutationOrbits SingletonWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0 ≤ t) (htc : t < leftParameter q c)

@[simp] theorem selectionEquiv_mem (S : Finset (Crossing (moveStart q t)))
    (d : Crossing (moveStart q t)) :
    crossingEquiv_before_first q hR c hc t ht0 htc d ∈ selectionEquiv q hR c hc t ht0 htc S ↔ d ∈ S := by
  exact Finset.mem_map_equiv

theorem eventEquiv_retained (S : Finset (Crossing (moveStart q t))) (x : Event (moveStart q t)) :
    retained q (selectionEquiv q hR c hc t ht0 htc S) (eventEquiv q hR c hc t ht0 htc x) ↔
      retained (moveStart q t) S x := by
  cases x with
  | inl i => rfl
  | inr v => exact selectionEquiv_mem q hR c hc t ht0 htc S v.1

theorem eventEquiv_pairing (S : Finset (Crossing (moveStart q t))) (x : Event (moveStart q t)) :
    eventEquiv q hR c hc t ht0 htc (pairing (moveStart q t) S x) =
      pairing q (selectionEquiv q hR c hc t ht0 htc S) (eventEquiv q hR c hc t ht0 htc x) := by
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨d,b⟩
    by_cases hd : d ∈ S <;> cases b <;>
      simp [pairing,pairingMap,eventEquiv_visit,selectionEquiv_mem,hd]

theorem eventEquiv_successor (x : Event (moveStart q t)) :
    eventEquiv q hR c hc t ht0 htc
      (successor (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple x) =
      successor q hR.noTriple (eventEquiv q hR c hc t ht0 htc x) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (moveStart q t)
    (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple
  exact (orderedCyclicSuccessor_naturality (Event (moveStart q t)) (eventOrderIso q hR c hc t ht0 htc) x).symm

theorem eventEquiv_incoming (S : Finset (Crossing (moveStart q t))) (x : Event (moveStart q t)) :
    eventEquiv q hR c hc t ht0 htc
      (incoming (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S x) =
      incoming q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S)
        (eventEquiv q hR c hc t ht0 htc x) := by
  simp only [incoming,Equiv.Perm.mul_apply,eventEquiv_successor,eventEquiv_pairing]

theorem eventEquiv_orbitWord (S : Finset (Crossing (moveStart q t))) (root : Event (moveStart q t)) :
    orbitWord (incoming q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S))
      (eventEquiv q hR c hc t ht0 htc root) =
      (orbitWord (incoming (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) root).map
        (eventEquiv q hR c hc t ht0 htc) :=
  orbitWord_map_injective _ _ _ (eventEquiv q hR c hc t ht0 htc).injective
    (fun x => (eventEquiv_incoming q hR c hc t ht0 htc S x).symm) root

theorem eventEquiv_retainedEvents (S : Finset (Crossing (moveStart q t))) (root : Event (moveStart q t)) :
    List.ofFn (RetainedWords.cornerEvent q hR (selectionEquiv q hR c hc t ht0 htc S)
      (eventEquiv q hR c hc t ht0 htc root)) =
    (List.ofFn (RetainedWords.cornerEvent (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) S root)).map
      (eventEquiv q hR c hc t ht0 htc) := by
  rw [retainedEvents_eq_filtered (a:=n) (b:=0),retainedEvents_eq_filtered (a:=n) (b:=0),eventEquiv_orbitWord,
    ← DaughterPointListFilter.map_filter_comp]
  simp only [eventEquiv_retained]

/-- Every physical event point except the moving first endpoint is unchanged. -/
theorem eventEquiv_point (x : Event (moveStart q t)) (hx : x ≠ start (moveStart q t)) :
    eventPoint (moveStart q t) x = eventPoint q (eventEquiv q hR c hc t ht0 htc x) := by
  cases x with
  | inl i =>
    exact moveStart_eq q t i (fun h => hx (congrArg Sum.inl h))
  | inr v =>
    exact (crossingEquiv_point q hR t ht0
      (lt_trans htc (leftParameter_spec q c).2.1) v.1).symm

end DirectGLSSW.ActiveArc.Cursor.BeforeFirst
