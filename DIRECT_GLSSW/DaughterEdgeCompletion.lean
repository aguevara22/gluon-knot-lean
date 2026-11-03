import DaughterUncutIncidence

set_option autoImplicit false
namespace DirectGLSSW.DaughterEdgeCompletion
open PrimitiveEdgeGrouping DaughterFirstReturn DaughterUncutIncidence
  DaughterPairingLift DaughterUnionNonalternation PolygonNonalternation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (e : Fin n) (U : OffEdgeSupport P hP e)

/-- All separating supports on the whole daughter edge, with the empty support retained. -/
def DaughterEdgeSupport :=
  {T : Finset (EdgeChord (edgeDaughter P hP e U) (daughterChosenEdge P hP e U)) //
    polygonNonalternating (edgeDaughter P hP e U) (edgeDaughterG2 P hP e U) (T.image Subtype.val)}

instance daughterEdgeSupportFintype : Fintype (DaughterEdgeSupport P hP e U) := by
  unfold DaughterEdgeSupport
  infer_instance

def completionOfSupport (T : DaughterEdgeSupport P hP e U) : EdgeCompletion P hP e U :=
  ⟨T.val.map (parentEdgeEmbedding P hP e U),by
    intro c hc
    obtain ⟨d,_,rfl⟩ := Finset.mem_map.mp hc
    exact parentEdgeEmbedding_incident P hP e U d,by
    rw [map_parentEdgeEmbedding_eq_liftedSupport]
    exact (polygonNonalternating_union_liftedSupport_iff P hP U.val U.property.1
      (Sum.inl e) (by trivial) (T.val.image Subtype.val)).mpr T.property⟩

theorem completionOfSupport_injective : Function.Injective (completionOfSupport P hP e U) := by
  intro T R h
  apply Subtype.ext
  exact Finset.map_injective (parentEdgeEmbedding P hP e U) (congrArg Subtype.val h)

theorem completionOfSupport_surjective : Function.Surjective (completionOfSupport P hP e U) := by
  intro T
  let W := Finset.univ.filter (fun d : EdgeChord (edgeDaughter P hP e U)
    (daughterChosenEdge P hP e U) => parentEdgeEmbedding P hP e U d ∈ T.val)
  have hW : W.map (parentEdgeEmbedding P hP e U) = T.val := by
    ext c
    constructor
    · intro hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp hc
      exact (Finset.mem_filter.mp hd).2
    · intro hc
      obtain ⟨d,hd⟩ := exists_preimage_of_completion P hP e U T c hc
      exact Finset.mem_map.mpr ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.symm ▸ hc⟩,hd⟩
  have hNA : polygonNonalternating (edgeDaughter P hP e U) (edgeDaughterG2 P hP e U)
      (W.image Subtype.val) := by
    apply (polygonNonalternating_union_liftedSupport_iff P hP U.val U.property.1
      (Sum.inl e) (by trivial) (W.image Subtype.val)).mp
    rw [← map_parentEdgeEmbedding_eq_liftedSupport,hW]
    exact T.property.2
  exact ⟨⟨W,hNA⟩,Subtype.ext hW⟩

/-- The actual remaining primitive-row completions are exactly daughter
separating on-edge supports; crossings with spectators never enter this type. -/
def edgeCompletionEquiv : DaughterEdgeSupport P hP e U ≃ EdgeCompletion P hP e U :=
  Equiv.ofBijective (completionOfSupport P hP e U)
    ⟨completionOfSupport_injective P hP e U,completionOfSupport_surjective P hP e U⟩

@[simp] theorem edgeCompletionEquiv_val (T : DaughterEdgeSupport P hP e U) :
    (edgeCompletionEquiv P hP e U T).val =
      liftedSupport P hP U.val U.property.1 (Sum.inl e) (by trivial) (T.val.image Subtype.val) :=
  map_parentEdgeEmbedding_eq_liftedSupport P hP e U T.val

@[simp] theorem edgeCompletionEquiv_card (T : DaughterEdgeSupport P hP e U) :
    (edgeCompletionEquiv P hP e U T).val.card = T.val.card := Finset.card_map _

@[simp] theorem edgeCompletionEquiv_nonempty (T : DaughterEdgeSupport P hP e U) :
    (edgeCompletionEquiv P hP e U T).val.Nonempty ↔ T.val.Nonempty := Finset.map_nonempty

@[simp] theorem edgeCompletionEquiv_symm_liftedSupport (T : EdgeCompletion P hP e U) :
    liftedSupport P hP U.val U.property.1 (Sum.inl e) (by trivial)
      (((edgeCompletionEquiv P hP e U).symm T).val.image Subtype.val) = T.val := by
  rw [← edgeCompletionEquiv_val,Equiv.apply_symm_apply]

@[simp] theorem edgeCompletionEquiv_symm_card (T : EdgeCompletion P hP e U) :
    ((edgeCompletionEquiv P hP e U).symm T).val.card = T.val.card := by
  rw [← edgeCompletionEquiv_card,Equiv.apply_symm_apply]












end
end DirectGLSSW.DaughterEdgeCompletion
