import ActiveArcConfigurationSupport
import ActiveArcSingletonWords
import ActiveArcOrbitEmbedding
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationTransport
open DirectGLSSW ActiveArc ConfigurationLocality PermutationOrbits SingletonWords RetainedWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q r : Fin (n+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))

theorem event_retained (S : Finset (Crossing q)) (x : Event q) :
    retained r (selectionEquiv q r E S) (eventMapEquiv q r E x) ↔ retained q S x := by
  cases x with
  | inl i => rfl
  | inr v => exact selectionEquiv_mem q r E S v.1

theorem event_pairing (S : Finset (Crossing q)) (x : Event q) :
    eventMapEquiv q r E (pairing q S x)=
      pairing r (selectionEquiv q r E S) (eventMapEquiv q r E x) := by
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨d,b⟩
    change eventMapEquiv q r E (if d∈S then Sum.inr (d,!b) else Sum.inr (d,b)) =
      (if E d∈selectionEquiv q r E S then Sum.inr (E d,!b) else Sum.inr (E d,b))
    simp only [selectionEquiv_mem]
    by_cases hd : d∈S <;> simp only [hd,if_pos,if_neg] <;> rfl

include horder in
theorem event_successor (x : Event q) :
    eventMapEquiv q r E (successor q hQ.noTriple x)=
      successor r hR.noTriple (eventMapEquiv q r E x) := by
  letI := eventOrder q hQ.noTriple
  letI := eventOrder r hR.noTriple
  exact (orderedCyclicSuccessor_naturality (Event q) (eventOrderIso q r hQ hR E horder) x).symm

include horder in
theorem event_incoming (S : Finset (Crossing q)) (x : Event q) :
    eventMapEquiv q r E (incoming q hQ.noTriple S x)=
      incoming r hR.noTriple (selectionEquiv q r E S) (eventMapEquiv q r E x) := by
  simp only [incoming,Equiv.Perm.mul_apply,event_successor q r hQ hR E horder,event_pairing]

include horder in
theorem event_orbitWord (S : Finset (Crossing q)) (root : Event q) :
    orbitWord (incoming r hR.noTriple (selectionEquiv q r E S)) (eventMapEquiv q r E root)=
      (orbitWord (incoming q hQ.noTriple S) root).map (eventMapEquiv q r E) :=
  orbitWord_map_injective _ _ _ (eventMapEquiv q r E).injective
    (fun x => (event_incoming q r hQ hR E horder S x).symm) root

include horder in
/-- Exact retained EVENT words; no unsupported equality of moving point coordinates. -/
theorem event_retainedEvents (S : Finset (Crossing q)) (root : Event q) :
    List.ofFn (cornerEvent r hR (selectionEquiv q r E S) (eventMapEquiv q r E root))=
      (List.ofFn (cornerEvent q hQ S root)).map (eventMapEquiv q r E) := by
  rw [retainedEvents_eq_filtered (a:=n) (b:=0),retainedEvents_eq_filtered (a:=n) (b:=0),
    event_orbitWord q r hQ hR E horder,← DaughterPointListFilter.map_filter_comp]
  simp only [event_retained]

include horder in
theorem retained_count (S : Finset (Crossing q)) (root : Event q) :
    Fintype.card (Corner r hR (selectionEquiv q r E S) (eventMapEquiv q r E root))=
      Fintype.card (Corner q hQ S root) := by
  have h := congrArg List.length (event_retainedEvents q r hQ hR E horder S root)
  simpa only [List.length_ofFn,List.length_map] using h

include horder in
/-- The entire ordered outgoing carrier-label list is unchanged under the actual label/order map. -/
theorem retained_carrier_word (hlabels : ∀ c, (E c).val=c.val)
    (S : Finset (Crossing q)) (root : Event q) :
    List.ofFn (fun i => edgeTag r (pairing r (selectionEquiv q r E S)
      (cornerEvent r hR (selectionEquiv q r E S) (eventMapEquiv q r E root) i)))=
    List.ofFn (fun i => edgeTag q (pairing q S (cornerEvent q hQ S root i))) := by
  have h := congrArg (List.map (fun x => edgeTag r (pairing r (selectionEquiv q r E S) x)))
    (event_retainedEvents q r hQ hR E horder S root)
  have hp (x : Event q) : edgeTag r (pairing r (selectionEquiv q r E S) (eventMapEquiv q r E x))=
      edgeTag q (pairing q S x) := by
    rw [← event_pairing,eventMapEquiv_edgeTag q r E hlabels]
  simpa only [List.map_ofFn,List.map_map,Function.comp_def,hp] using h

end DirectGLSSW.ActiveArc.ConfigurationTransport
