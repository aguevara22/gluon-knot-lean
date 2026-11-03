import DirectGLSSW.GeometricSmoothingSumTransport
import DirectGLSSW.EdgeCrossingVisits

set_option autoImplicit false
namespace DirectGLSSW.PrimitiveEdgeGrouping
open GeometricSmoothingWeights GeometricSmoothingSumTransport PolygonNonalternation
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P) (e : Fin n)

/-- The actual edge-pair incidence predicate used by EdgeChord. -/
def Incident (c : PolygonCrossing P) : Prop := c.val.1 = e ∨ c.val.2 = e

/-- First-stage separating supports containing no crossing on the chosen edge. -/
def OffEdgeSupport := {U : Finset (PolygonCrossing P) //
  polygonNonalternating P hP.g2 U ∧ ∀ c ∈ U, ¬ Incident P e c}

/-- All actual on-edge completions, including the empty one. Their union with
the first stage must be separating; this is the original primitive's domain. -/
def EdgeCompletion (U : OffEdgeSupport P hP e) :=
  {T : Finset (PolygonCrossing P) //
    (∀ c ∈ T, Incident P e c) ∧ polygonNonalternating P hP.g2 (U.val ∪ T)}

instance offEdgeSupportFintype : Fintype (OffEdgeSupport P hP e) := by
  unfold OffEdgeSupport
  infer_instance

instance edgeCompletionFintype (U : OffEdgeSupport P hP e) :
    Fintype (EdgeCompletion P hP e U) := by
  unfold EdgeCompletion
  infer_instance

theorem off_on_disjoint (U : OffEdgeSupport P hP e) (T : EdgeCompletion P hP e U) :
    Disjoint U.val T.val := by
  apply Finset.disjoint_left.mpr
  intro c hcU hcT
  exact U.property.2 c hcU (T.property.1 c hcT)

theorem filter_off_union (U : OffEdgeSupport P hP e) (T : EdgeCompletion P hP e U) :
    (U.val ∪ T.val).filter (fun c => ¬ Incident P e c) = U.val := by
  ext c
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hc,hn⟩
    rcases hc with hU | hT
    · exact hU
    · exact (hn (T.property.1 c hT)).elim
  · intro hc
    exact ⟨Or.inl hc,U.property.2 c hc⟩

theorem filter_on_union (U : OffEdgeSupport P hP e) (T : EdgeCompletion P hP e U) :
    (U.val ∪ T.val).filter (Incident P e) = T.val := by
  ext c
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hc,hi⟩
    rcases hc with hU | hT
    · exact (U.property.2 c hU hi).elim
    · exact hT
  · intro hc
    exact ⟨Or.inr hc,T.property.1 c hc⟩

theorem filter_partition (S : Finset (PolygonCrossing P)) :
    S.filter (fun c => ¬ Incident P e c) ∪ S.filter (Incident P e) = S := by
  ext c
  simp only [Finset.mem_union,Finset.mem_filter]
  constructor
  · rintro (⟨hc,_⟩ | ⟨hc,_⟩) <;> exact hc
  · intro hc
    by_cases hi : Incident P e c
    · exact Or.inr ⟨hc,hi⟩
    · exact Or.inl ⟨hc,hi⟩

def joinSupport (x : Σ U : OffEdgeSupport P hP e, EdgeCompletion P hP e U) :
    SeparatingSupport P hP := ⟨x.1.val ∪ x.2.val,x.2.property.2⟩

theorem joinSupport_injective : Function.Injective (joinSupport P hP e) := by
  rintro ⟨U,T⟩ ⟨V,R⟩ heq
  have hv : U.val ∪ T.val = V.val ∪ R.val := congrArg Subtype.val heq
  have hU : U = V := by
    apply Subtype.ext
    have hx := congrArg (fun S => S.filter (fun c => ¬ Incident P e c)) hv
    simpa only [filter_off_union] using hx
  subst V
  have hT : T = R := by
    apply Subtype.ext
    have hx := congrArg (fun S => S.filter (Incident P e)) hv
    simpa only [filter_on_union] using hx
  subst R
  rfl

theorem joinSupport_surjective : Function.Surjective (joinSupport P hP e) := by
  intro S
  let U : OffEdgeSupport P hP e :=
    ⟨S.val.filter (fun c => ¬ Incident P e c),
      polygonNonalternating_mono P hP.g2 S.property (Finset.filter_subset _ _),
      fun c hc => (Finset.mem_filter.mp hc).2⟩
  let T : EdgeCompletion P hP e U :=
    ⟨S.val.filter (Incident P e),fun c hc => (Finset.mem_filter.mp hc).2,by
      change polygonNonalternating P hP.g2
        (S.val.filter (fun c => ¬ Incident P e c) ∪ S.val.filter (Incident P e))
      rw [filter_partition]
      exact S.property⟩
  refine ⟨⟨U,T⟩,?_⟩
  exact Subtype.ext (filter_partition P e S.val)

/-- Exact bijection underlying source prop:nonuniform's grouping step. -/
def groupedSupportEquiv :
    (Σ U : OffEdgeSupport P hP e, EdgeCompletion P hP e U) ≃ SeparatingSupport P hP :=
  Equiv.ofBijective (joinSupport P hP e)
    ⟨joinSupport_injective P hP e,joinSupport_surjective P hP e⟩

theorem groupedSupportEquiv_val (U : OffEdgeSupport P hP e) (T : EdgeCompletion P hP e U) :
    (groupedSupportEquiv P hP e ⟨U,T⟩).val = U.val ∪ T.val := rfl

theorem groupedSupport_card (U : OffEdgeSupport P hP e) (T : EdgeCompletion P hP e U) :
    (U.val ∪ T.val).card = U.val.card + T.val.card :=
  Finset.card_union_of_disjoint (off_on_disjoint P hP e U T)

/-- Group the ACTUAL component-amplitude primitive by off-edge cuts. No
spectator factorization or row cancellation is assumed here. -/
theorem separatingSmoothingSum_grouped (hAux : auxiliaryGenericity P hP) :
    separatingSmoothingSum P hP hAux =
      ∑ U : OffEdgeSupport P hP e, (-1 : ℚ)^U.val.card *
        ∑ T : EdgeCompletion P hP e U, (-1 : ℚ)^T.val.card *
          componentAmplitudeProduct P hP (U.val ∪ T.val) hAux T.property.2 := by
  have hsum : separatingSmoothingSum P hP hAux =
      ∑ x : (Σ U : OffEdgeSupport P hP e, EdgeCompletion P hP e U),
        (-1 : ℚ)^(x.1.val.card+x.2.val.card) *
          componentAmplitudeProduct P hP (x.1.val ∪ x.2.val) hAux x.2.property.2 := by
    symm
    unfold separatingSmoothingSum
    apply Fintype.sum_equiv (groupedSupportEquiv P hP e)
    rintro ⟨U,T⟩
    change (-1 : ℚ)^(U.val.card+T.val.card) *
        componentAmplitudeProduct P hP (U.val ∪ T.val) hAux T.property.2 =
      (-1 : ℚ)^((U.val ∪ T.val).card) *
        componentAmplitudeProduct P hP (U.val ∪ T.val) hAux T.property.2
    rw [groupedSupport_card]
  rw [hsum,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [pow_add]
  ring

















end
end DirectGLSSW.PrimitiveEdgeGrouping
