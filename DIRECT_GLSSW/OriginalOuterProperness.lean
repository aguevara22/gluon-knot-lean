import OriginalSecantProperness
import GeometricSecantRegularity

set_option autoImplicit false
namespace DirectGLSSW.OriginalOuterProperness
open Set Filter Topology CarrierDensity CarrierNumeratorPath
noncomputable section

/-- Literal determinant excluding parallel disjoint endpoint-return directions. -/
def outerNumerator {R : Type*} [CommRing R] (p : Fin 4 → R × R) : R :=
  planarDet (p 0-p 1) (p 2-p 3)

/-- Distinct original vertex labels make this exclusion a proper polynomial. -/
theorem exists_original_nonzero {α : Type*} (labels : Fin 4 → α)
    (hinj : Function.Injective labels) :
    ∃ q : α → ℝ × ℝ, outerNumerator (q ∘ labels) ≠ 0 := by
  classical
  let w : Fin 4 → ℝ × ℝ := ![(0,0), (1,0), (0,0), (0,1)]
  refine ⟨Function.extend labels w (fun _ => (0,0)), ?_⟩
  simp only [outerNumerator, Function.comp_def, hinj.extend_apply]
  dsimp [w, planarDet]
  norm_num

def outerPathPolynomial {α : Type*} (labels : Fin 4 → α)
    (q r : α → ℝ × ℝ) : Polynomial ℝ :=
  outerNumerator (fun i =>
    (scalarPolynomial (q (labels i)).1 (r (labels i)).1,
     scalarPolynomial (q (labels i)).2 (r (labels i)).2))

theorem outerPathPolynomial_eval {α : Type*} (labels : Fin 4 → α)
    (q r : α → ℝ × ℝ) (t : ℝ) :
    (outerPathPolynomial labels q r).eval t =
      outerNumerator (fun i => affinePoint (q (labels i)) (r (labels i)) t) := by
  simp [outerPathPolynomial, outerNumerator, scalarPolynomial, planarDet, affinePoint]

theorem original_outer_locus_dense_open {α : Type*} (labels : Fin 4 → α)
    (hinj : Function.Injective labels) :
    Dense {q : α → ℝ × ℝ | outerNumerator (q ∘ labels) ≠ 0} ∧
    IsOpen {q : α → ℝ × ℝ | outerNumerator (q ∘ labels) ≠ 0} := by
  have hcont : Continuous (fun q : α → ℝ × ℝ => outerNumerator (q ∘ labels)) := by
    unfold outerNumerator planarDet
    fun_prop
  refine ⟨?_, isOpen_ne_fun hcont continuous_const⟩
  obtain ⟨r, hr⟩ := exists_original_nonzero labels hinj
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨q, hq⟩ := hUne
  let path : ℝ → (α → ℝ × ℝ) := fun t a => affinePoint (q a) (r a) t
  have hc : Continuous path := by
    unfold path affinePoint
    fun_prop
  have hp : outerPathPolynomial labels q r ≠ 0 := by
    intro hz
    have he := outerPathPolynomial_eval labels q r 1
    rw [hz, Polynomial.eval_zero] at he
    apply hr
    simpa [affinePoint, Function.comp_def] using he.symm
  have hpre : IsOpen (path ⁻¹' U) := hU.preimage hc
  have hprene : (path ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [path, affinePoint] using hq
  obtain ⟨t, htU, ht⟩ := (polynomial_nonzero_dense hp).inter_open_nonempty _ hpre hprene
  refine ⟨path t, htU, ?_⟩
  simpa only [outerPathPolynomial_eval, path, Function.comp_def] using ht

/-- The finite family of every disjoint four-label secant condition is proper
on the SAME original-parent coordinate space. -/
theorem all_original_outer_locus_dense_open (n : ℕ) :
    Dense {q : Fin n → ℝ × ℝ | ∀ labels : Fin 4 → Fin n,
      Function.Injective labels → outerNumerator (q ∘ labels) ≠ 0} ∧
    IsOpen {q : Fin n → ℝ × ℝ | ∀ labels : Fin 4 → Fin n,
      Function.Injective labels → outerNumerator (q ∘ labels) ≠ 0} := by
  classical
  let A := fun labels : {l : Fin 4 → Fin n // Function.Injective l} =>
    {q : Fin n → ℝ × ℝ | outerNumerator (q ∘ labels.val) ≠ 0}
  have h := CarrierFamilyDensity.finite_family_dense_open A
    (fun i => (original_outer_locus_dense_open i.val i.property).1)
    (fun i => (original_outer_locus_dense_open i.val i.property).2)
  have he : (⋂ i, A i) = {q : Fin n → ℝ × ℝ | ∀ labels : Fin 4 → Fin n,
      Function.Injective labels → outerNumerator (q ∘ labels) ≠ 0} := by
    ext q
    simp [A]
  rwa [he] at h


/-- All original disjoint-secants and outer-edge exclusions share one parent chart. -/
theorem joint_parent_locus_dense_open (n : ℕ) :
    Dense {q : Fin n → ℝ × ℝ |
      (∀ l : Fin 6 → Fin n, Function.Injective l → OriginalSecantProperness.secantNumerator (q ∘ l) ≠ 0) ∧
      (∀ l : Fin 4 → Fin n, Function.Injective l → outerNumerator (q ∘ l) ≠ 0)} ∧
    IsOpen {q : Fin n → ℝ × ℝ |
      (∀ l : Fin 6 → Fin n, Function.Injective l → OriginalSecantProperness.secantNumerator (q ∘ l) ≠ 0) ∧
      (∀ l : Fin 4 → Fin n, Function.Injective l → outerNumerator (q ∘ l) ≠ 0)} := by
  have h6 := OriginalSecantProperness.all_original_secant_locus_dense_open n
  have h4 := all_original_outer_locus_dense_open n
  exact ⟨h6.1.inter_of_isOpen_left h4.1 h6.2, h6.2.inter h4.2⟩

theorem exists_joint_parent_daughters {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (U : Set (Fin n → PlanarPoint ℝ))
    (hU : IsOpen U) (hqU : q ∈ U) :
    ∃ r ∈ U, ∃ hr : CyclicGeneric r,
      GeometricSmoothingWeights.auxiliaryGenericity r hr ∧
      (∀ l : Fin 6 → Fin n, Function.Injective l → OriginalSecantProperness.secantNumerator (r ∘ l) ≠ 0) ∧
      (∀ l : Fin 4 → Fin n, Function.Injective l → outerNumerator (r ∘ l) ≠ 0) := by
  have hg : ∀ᶠ r in 𝓝 q, CyclicGeneric r :=
    (ConfigurationEventLocality.eventually_configuration_event_order q hq).mono
      (fun _ h => h.choose)
  obtain ⟨V, hVsub, hVopen, hqV⟩ := mem_nhds_iff.mp hg
  obtain ⟨r, hrUV, hrsec⟩ := (joint_parent_locus_dense_open n).1.inter_open_nonempty
    (U ∩ V) (hU.inter hVopen) ⟨q, hqU, hqV⟩
  have hr : CyclicGeneric r := hVsub hrUV.2
  let W := U ∩ {r : Fin n → PlanarPoint ℝ |
    (∀ l : Fin 6 → Fin n, Function.Injective l → OriginalSecantProperness.secantNumerator (r ∘ l) ≠ 0) ∧
    (∀ l : Fin 4 → Fin n, Function.Injective l → outerNumerator (r ∘ l) ≠ 0)}
  have hW : W ∈ 𝓝 r := (hU.inter (joint_parent_locus_dense_open n).2).mem_nhds ⟨hrUV.1, hrsec⟩
  obtain ⟨s, hs, hsgen, hsaux, _⟩ :=
    ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds r hr W hW
  exact ⟨s, hs.1, hsgen, hsaux, hs.2⟩







end
end DirectGLSSW.OriginalOuterProperness
