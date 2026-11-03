import ActualAuxiliaryDensity
import CarrierDensity

set_option autoImplicit false
namespace DirectGLSSW.OriginalSecantProperness
open Set Filter Topology CarrierDensity CarrierNumeratorPath
noncomputable section

/-- Cross-multiplied coincidence numerator for two secants meeting the line uv.
The six slots are u,v,A,B,C,D. No division or auxiliary point is used. -/
def secantNumerator {R : Type*} [CommRing R] (p : Fin 6 → R × R) : R :=
  planarDet (p 2-p 3) (p 0-p 3) * planarDet (p 4-p 5) (p 1-p 0) -
    planarDet (p 4-p 5) (p 0-p 5) * planarDet (p 2-p 3) (p 1-p 0)

theorem secantNumerator_ne_zero_iff (p : Fin 6 → ℝ × ℝ)
    (hAB : planarDet (p 2-p 3) (p 1-p 0) ≠ 0)
    (hCD : planarDet (p 4-p 5) (p 1-p 0) ≠ 0) :
    secantNumerator p ≠ 0 ↔
      -planarDet (p 2-p 3) (p 0-p 3) / planarDet (p 2-p 3) (p 1-p 0) ≠
      -planarDet (p 4-p 5) (p 0-p 5) / planarDet (p 4-p 5) (p 1-p 0) := by
  unfold secantNumerator
  simp only [ne_eq, div_eq_div_iff hAB hCD]
  constructor <;> intro h he <;> apply h <;> linarith

/-- Distinct original vertex labels make this exclusion a proper polynomial. -/
theorem exists_original_nonzero {α : Type*} (labels : Fin 6 → α)
    (hinj : Function.Injective labels) :
    ∃ q : α → ℝ × ℝ, secantNumerator (q ∘ labels) ≠ 0 := by
  classical
  let w : Fin 6 → ℝ × ℝ := ![(0,0), (1,0), (0,1), (0,2), (1,1), (1,2)]
  refine ⟨Function.extend labels w (fun _ => (0,0)), ?_⟩
  simp only [secantNumerator, Function.comp_def, hinj.extend_apply]
  dsimp [w, planarDet]
  norm_num

def secantPathPolynomial {α : Type*} (labels : Fin 6 → α)
    (q r : α → ℝ × ℝ) : Polynomial ℝ :=
  secantNumerator (fun i =>
    (scalarPolynomial (q (labels i)).1 (r (labels i)).1,
     scalarPolynomial (q (labels i)).2 (r (labels i)).2))

theorem secantPathPolynomial_eval {α : Type*} (labels : Fin 6 → α)
    (q r : α → ℝ × ℝ) (t : ℝ) :
    (secantPathPolynomial labels q r).eval t =
      secantNumerator (fun i => affinePoint (q (labels i)) (r (labels i)) t) := by
  simp [secantPathPolynomial, secantNumerator, scalarPolynomial, planarDet, affinePoint]

theorem original_secant_locus_dense_open {α : Type*} (labels : Fin 6 → α)
    (hinj : Function.Injective labels) :
    Dense {q : α → ℝ × ℝ | secantNumerator (q ∘ labels) ≠ 0} ∧
    IsOpen {q : α → ℝ × ℝ | secantNumerator (q ∘ labels) ≠ 0} := by
  have hcont : Continuous (fun q : α → ℝ × ℝ => secantNumerator (q ∘ labels)) := by
    unfold secantNumerator planarDet
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
  have hp : secantPathPolynomial labels q r ≠ 0 := by
    intro hz
    have he := secantPathPolynomial_eval labels q r 1
    rw [hz, Polynomial.eval_zero] at he
    apply hr
    simpa [affinePoint, Function.comp_def] using he.symm
  have hpre : IsOpen (path ⁻¹' U) := hU.preimage hc
  have hprene : (path ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [path, affinePoint] using hq
  obtain ⟨t, htU, ht⟩ := (polynomial_nonzero_dense hp).inter_open_nonempty _ hpre hprene
  refine ⟨path t, htU, ?_⟩
  simpa only [secantPathPolynomial_eval, path, Function.comp_def] using ht

/-- The finite family of every disjoint six-label secant condition is proper
on the SAME original-parent coordinate space. -/
theorem all_original_secant_locus_dense_open (n : ℕ) :
    Dense {q : Fin n → ℝ × ℝ | ∀ labels : Fin 6 → Fin n,
      Function.Injective labels → secantNumerator (q ∘ labels) ≠ 0} ∧
    IsOpen {q : Fin n → ℝ × ℝ | ∀ labels : Fin 6 → Fin n,
      Function.Injective labels → secantNumerator (q ∘ labels) ≠ 0} := by
  classical
  let A := fun labels : {l : Fin 6 → Fin n // Function.Injective l} =>
    {q : Fin n → ℝ × ℝ | secantNumerator (q ∘ labels.val) ≠ 0}
  have h := CarrierFamilyDensity.finite_family_dense_open A
    (fun i => (original_secant_locus_dense_open i.val i.property).1)
    (fun i => (original_secant_locus_dense_open i.val i.property).2)
  have he : (⋂ i, A i) = {q : Fin n → ℝ × ℝ | ∀ labels : Fin 6 → Fin n,
      Function.Injective labels → secantNumerator (q ∘ labels) ≠ 0} := by
    ext q
    simp [A]
  rwa [he] at h

/-- One actual original-chart secant exclusion holds simultaneously with ALL
nonalternating daughter genericity in every open generic parent neighborhood.
No fixed-endpoint claim or full auxiliary-domain claim is made. -/
theorem exists_joint_secant_daughters {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (labels : Fin 6 → Fin n) (hinj : Function.Injective labels)
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : IsOpen U) (hqU : q ∈ U) :
    ∃ r ∈ U, ∃ hr : CyclicGeneric r,
      GeometricSmoothingWeights.auxiliaryGenericity r hr ∧
      secantNumerator (r ∘ labels) ≠ 0 := by
  have hg : ∀ᶠ r in 𝓝 q, CyclicGeneric r :=
    (ConfigurationEventLocality.eventually_configuration_event_order q hq).mono
      (fun _ h => h.choose)
  obtain ⟨V, hVsub, hVopen, hqV⟩ := mem_nhds_iff.mp hg
  obtain ⟨r, hrUV, hrsec⟩ := (original_secant_locus_dense_open labels hinj).1.inter_open_nonempty
    (U ∩ V) (hU.inter hVopen) ⟨q, hqU, hqV⟩
  have hr : CyclicGeneric r := hVsub hrUV.2
  let W := U ∩ {r : Fin n → PlanarPoint ℝ | secantNumerator (r ∘ labels) ≠ 0}
  have hW : W ∈ 𝓝 r :=
    (hU.inter (original_secant_locus_dense_open labels hinj).2).mem_nhds ⟨hrUV.1, hrsec⟩
  obtain ⟨s, hs, hsgen, hsaux, _⟩ :=
    ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds r hr W hW
  exact ⟨s, hs.1, hsgen, hsaux, hs.2⟩

theorem exists_joint_all_secants_daughters {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q)
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : IsOpen U) (hqU : q ∈ U) :
    ∃ r ∈ U, ∃ hr : CyclicGeneric r,
      GeometricSmoothingWeights.auxiliaryGenericity r hr ∧
      (∀ labels : Fin 6 → Fin n, Function.Injective labels →
        secantNumerator (r ∘ labels) ≠ 0) := by
  have hg : ∀ᶠ r in 𝓝 q, CyclicGeneric r :=
    (ConfigurationEventLocality.eventually_configuration_event_order q hq).mono
      (fun _ h => h.choose)
  obtain ⟨V, hVsub, hVopen, hqV⟩ := mem_nhds_iff.mp hg
  obtain ⟨r, hrUV, hrsec⟩ := (all_original_secant_locus_dense_open n).1.inter_open_nonempty
    (U ∩ V) (hU.inter hVopen) ⟨q, hqU, hqV⟩
  have hr : CyclicGeneric r := hVsub hrUV.2
  let W := U ∩ {r : Fin n → PlanarPoint ℝ | ∀ labels : Fin 6 → Fin n,
    Function.Injective labels → secantNumerator (r ∘ labels) ≠ 0}
  have hW : W ∈ 𝓝 r :=
    (hU.inter (all_original_secant_locus_dense_open n).2).mem_nhds ⟨hrUV.1, hrsec⟩
  obtain ⟨s, hs, hsgen, hsaux, _⟩ :=
    ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds r hr W hW
  exact ⟨s, hs.1, hsgen, hsaux, hs.2⟩








end
end DirectGLSSW.OriginalSecantProperness
