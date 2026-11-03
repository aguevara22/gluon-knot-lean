import ActiveArcConfigurationPointFormula
import CyclicGenericOpenness
import ActiveArcConfigurationEventOrder
import ActiveArcRetainedOrbitComponents
import DirectGLSSW.DaughterRootAmplitude
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationLocality
open DirectGLSSW ActiveArc Filter Topology ConfigurationTransport RetainedWords
open PermutationOrbits CompatibleWords
attribute [local instance] Classical.propDecidable

private theorem generic_of_equal_positions {m k : ℕ}
    (p : Fin m → PlanarPoint ℝ) (r : Fin k → PlanarPoint ℝ) (hmk : m=k)
    (he : ∀ i j, i.val=j.val → r j=p i) (hp : CyclicGeneric p) : CyclicGeneric r := by
  subst k
  have h : r=p := funext (fun i => he i i rfl)
  rwa [h]

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hQ : Regular q)

/-- A fixed actual retained polygon stays generic under every nearby physical
configuration chart; coordinates are compared at equal integer positions. -/
theorem eventually_retained_generic (S : Finset (Crossing q)) (root : Event q)
    (hg : CyclicGeneric (vertex q hQ S root)) :
    ∀ᶠ r in 𝓝 q, ∀ (hR : Regular r) (E : Crossing q ≃ Crossing r)
      (hlabels : ∀ c, (E c).val=c.val)
      (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
        (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y)),
      CyclicGeneric (vertex r hR (selectionEquiv q r E S) (eventMapEquiv q r E root)) := by
  let Q := fun r : Fin (n+2) → PlanarPoint ℝ =>
    fun i => eventPointFormula q r (cornerEvent q hQ S root i)
  have hcont : ContinuousAt Q q := continuousAt_pi.2
    (fun i => eventPointFormula_continuousAt q hQ (cornerEvent q hQ S root i))
  have hrec : Q q=vertex q hQ S root := funext
    (fun i => eventPointFormula_recovery q hQ (cornerEvent q hQ S root i))
  have hgen : CyclicGeneric (Q q) := hrec.symm ▸ hg
  filter_upwards [CyclicGenericLocality.eventually_cyclicGeneric_of_continuousAt Q q hcont hgen]
    with r hr
  intro hR E hlabels horder
  exact generic_of_equal_positions (Q r) _
    (retained_count q r hQ hR E horder S root).symm
    (fun i j hij => retained_vertex_eq_formula q r hQ hR E hlabels horder S root i j hij) hr

/-- The original closed auxiliary condition applies at every actual closed root,
because changing a root rotates the same retained polygon. -/
theorem generic_at_closed_root (hAux : Primitive.ClosedAuxiliary q hQ)
    (S : Primitive.Support q hQ) (x : Event q)
    (hx : componentOf (incoming q hQ.noTriple S.val) x ≠ openComponent q hQ.noTriple S.val) :
    CyclicGeneric (vertex q hQ S.val x) := by
  let C := componentOf (incoming q hQ.noTriple S.val) x
  let y := closedRoot q hQ.noTriple S.val C hx
  have hy : componentOf (incoming q hQ.noTriple S.val) y=C :=
    (closedRoot_spec q hQ.noTriple S.val C hx).1
  have hrot := retainedWord_isRotated_of_sameCycle q hQ S.val y x
    ((componentOf_eq_iff _ _ _).mp hy)
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hrot (hAux S C hx)

/-- All actual closed daughter polygons remain generic in one configuration
neighborhood. No genericity of an open parent polygon is assumed or concluded. -/
theorem eventually_closedAuxiliary (hG1 : cyclicNoncollinear q)
    (hAux : Primitive.ClosedAuxiliary q hQ) :
    ∀ᶠ r in 𝓝 q, ∃ hR : Regular r, Primitive.ClosedAuxiliary r hR := by
  have hf : ∀ᶠ r in 𝓝 q, ∀ (S : Primitive.Support q hQ) (x : Event q),
      componentOf (incoming q hQ.noTriple S.val) x ≠ openComponent q hQ.noTriple S.val →
      ∀ (hR : Regular r) (E : Crossing q ≃ Crossing r)
      (hlabels : ∀ c, (E c).val=c.val)
      (horder : ∀ u v : Event q, (eventOrder q hQ.noTriple).lt u v ↔
        (eventOrder r hR.noTriple).lt (eventMapEquiv q r E u) (eventMapEquiv q r E v)),
      CyclicGeneric (vertex r hR (selectionEquiv q r E S.val) (eventMapEquiv q r E x)) := by
    apply Filter.eventually_all.mpr
    intro S
    apply Filter.eventually_all.mpr
    intro x
    by_cases hx : componentOf (incoming q hQ.noTriple S.val) x ≠ openComponent q hQ.noTriple S.val
    · exact (eventually_retained_generic q hQ S.val x
        (generic_at_closed_root q hQ hAux S x hx)).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hx h))
  filter_upwards [eventually_configuration_event_order q hQ hG1,hf] with r hchart hr
  obtain ⟨hR,E,hlabels,horder⟩ := hchart
  refine ⟨hR,?_⟩
  intro U C hC
  obtain ⟨S,hS⟩ := (supportEquiv q r hQ hR E horder).surjective U
  subst U
  let y := closedRoot r hR.noTriple (selectionEquiv q r E S.val) C hC
  let x := (eventMapEquiv q r E).symm y
  let F := componentEquivOfIntertwining (eventMapEquiv q r E)
    (incoming q hQ.noTriple S.val) (incoming r hR.noTriple (selectionEquiv q r E S.val))
    (event_incoming q r hQ hR E horder S.val)
  have hy : componentOf (incoming r hR.noTriple (selectionEquiv q r E S.val)) y=C :=
    (closedRoot_spec r hR.noTriple (selectionEquiv q r E S.val) C hC).1
  have hx : componentOf (incoming q hQ.noTriple S.val) x ≠ openComponent q hQ.noTriple S.val := by
    intro h
    have hh := congrArg F h
    change componentOf (incoming r hR.noTriple (selectionEquiv q r E S.val))
      (eventMapEquiv q r E x)=openComponent r hR.noTriple (selectionEquiv q r E S.val) at hh
    have hxy : eventMapEquiv q r E x=y := (eventMapEquiv q r E).apply_symm_apply y
    rw [hxy,hy] at hh
    exact hC hh
  have hg := hr S x hx hR E hlabels horder
  have hxy : eventMapEquiv q r E x=y := (eventMapEquiv q r E).apply_symm_apply y
  rw [hxy] at hg
  exact hg




end DirectGLSSW.ActiveArc.ConfigurationLocality
