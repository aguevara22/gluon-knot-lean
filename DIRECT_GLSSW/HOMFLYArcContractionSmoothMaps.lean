import HOMFLYArcContraction

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
namespace SignedArcContraction
variable {D E : PLLinkDiagram} (R : SignedArcContraction D E)

def smoothCodeMap : SmoothArcCode D → SmoothArcCode E := Sum.map R.arcMap id

def smoothArcMap (e : Fin (D.nArc + 2)) : Fin (E.nArc + 2) :=
  smoothArcEquiv E (R.smoothCodeMap ((smoothArcEquiv D).symm e))

def smoothDeleted : Fin (D.nArc + 2) := smoothArcEquiv D (Sum.inl R.deleted)
def smoothRetained : Fin (D.nArc + 2) := smoothArcEquiv D (Sum.inl R.retained)

def retainedCrossingEquiv (c : Fin D.nCrossing) :
    {d : Fin D.nCrossing // d ≠ c} ≃ {e : Fin E.nCrossing // e ≠ R.crossingEquiv c} where
  toFun d := ⟨R.crossingEquiv d.val, fun h => d.property (R.crossingEquiv.injective h)⟩
  invFun e := ⟨R.crossingEquiv.symm e.val, fun h => e.property (by
    have hh := congrArg R.crossingEquiv h
    simpa using hh)⟩
  left_inv := by intro d; apply Subtype.ext; simp
  right_inv := by intro e; apply Subtype.ext; simp

def smoothCrossingEquiv (c : Fin D.nCrossing) :
    Fin (D.nCrossing - 1) ≃ Fin (E.nCrossing - 1) :=
  (DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm.trans
    ((R.retainedCrossingEquiv c).trans (DirectGLSSW.HOMFLY.smoothCrossingEquiv E (R.crossingEquiv c)))

theorem smoothCodeMap_surjective : Function.Surjective R.smoothCodeMap := by
  intro y
  cases y with
  | inl e =>
    obtain ⟨d, rfl⟩ := R.arcMap_surjective e
    exact ⟨Sum.inl d, rfl⟩
  | inr i => exact ⟨Sum.inr i, rfl⟩

theorem smoothCodeMap_fibers (x y : SmoothArcCode D) :
    R.smoothCodeMap x = R.smoothCodeMap y ↔
      x = y ∨ (x = Sum.inl R.deleted ∧ y = Sum.inl R.retained) ∨
        (x = Sum.inl R.retained ∧ y = Sum.inl R.deleted) := by
  cases x with
  | inl e =>
    cases y with
    | inl f => simpa only [smoothCodeMap, Sum.map_inl, Sum.inl.injEq] using R.arcMap_fibers e f
    | inr j => simp [smoothCodeMap]
  | inr i =>
    cases y with
    | inl f => simp [smoothCodeMap]
    | inr j => simp [smoothCodeMap]

theorem smoothArcMap_surjective : Function.Surjective R.smoothArcMap :=
  (smoothArcEquiv E).surjective.comp (R.smoothCodeMap_surjective.comp (smoothArcEquiv D).symm.surjective)

theorem smoothArcMap_fibers (e f : Fin (D.nArc + 2)) :
    R.smoothArcMap e = R.smoothArcMap f ↔
      e = f ∨ (e = R.smoothDeleted ∧ f = R.smoothRetained) ∨
        (e = R.smoothRetained ∧ f = R.smoothDeleted) := by
  unfold smoothArcMap smoothDeleted smoothRetained
  rw [Equiv.apply_eq_iff_eq, R.smoothCodeMap_fibers]
  simp only [Equiv.apply_eq_iff_eq, Equiv.symm_apply_eq]

theorem smooth_selected_distinct : R.smoothDeleted ≠ R.smoothRetained := by
  intro h
  exact R.distinct (Sum.inl.inj ((smoothArcEquiv D).injective h))

theorem smooth_selected_successor (c : Fin D.nCrossing) :
    (smoothCrossing D c).continuation R.smoothDeleted = R.smoothRetained := by
  have hp : ∀ i, R.deleted ≠ D.incoming c i := fun i => (R.deleted_not_incoming c i).symm
  change smoothArcEquiv D (smoothContinuationGeometryCode D c
    ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl R.deleted)))) = _
  rw [Equiv.symm_apply_apply, smoothContinuationGeometryCode_other_arc D c R.deleted hp, R.successor]
  rfl

/-- Connector labels are fixed; the actual old-arc deletion map intertwines
all child continuation steps except the deleted source arc. -/
theorem smoothCode_continuation (c : Fin D.nCrossing) (x : SmoothArcCode D)
    (hx : x ≠ Sum.inl R.deleted) :
    R.smoothCodeMap (smoothContinuationGeometryCode D c x) =
      smoothContinuationGeometryCode E (R.crossingEquiv c) (R.smoothCodeMap x) := by
  cases x with
  | inl e =>
    have hed : e ≠ R.deleted := fun h => hx (congrArg Sum.inl h)
    by_cases h0 : e = D.incoming c 0
    · subst e
      rw [smoothContinuationGeometryCode_incoming_zero]
      simpa only [smoothCodeMap, Sum.map_inl, Sum.map_inr, id_eq, R.incoming_map] using
        (smoothContinuationGeometryCode_incoming_zero E (R.crossingEquiv c)).symm
    · by_cases h1 : e = D.incoming c 1
      · subst e
        rw [smoothContinuationGeometryCode_incoming_one]
        simpa only [smoothCodeMap, Sum.map_inl, Sum.map_inr, id_eq, R.incoming_map] using
          (smoothContinuationGeometryCode_incoming_one E (R.crossingEquiv c)).symm
      · have heD : ∀ i, e ≠ D.incoming c i := by
          intro i; fin_cases i
          · exact h0
          · exact h1
        have heE : ∀ i, R.arcMap e ≠ E.incoming (R.crossingEquiv c) i := by
          intro i hi
          exact heD i ((R.incoming_reflect c i e hed).mp hi)
        rw [smoothContinuationGeometryCode_other_arc D c e heD]
        simp only [smoothCodeMap, Sum.map_inl]
        rw [smoothContinuationGeometryCode_other_arc E (R.crossingEquiv c) (R.arcMap e) heE,
          R.continuation_map e hed]
  | inr i =>
    change R.smoothCodeMap (smoothContinuationGeometryCode D c (Sum.inr i)) =
      smoothContinuationGeometryCode E (R.crossingEquiv c) (Sum.inr i)
    rw [smoothContinuationGeometryCode_connector D c i,
      smoothContinuationGeometryCode_connector E (R.crossingEquiv c) i]
    simp only [smoothCodeMap, Sum.map_inl, R.outgoing_map, R.through_map]

theorem smooth_continuation_map (c : Fin D.nCrossing) (e : Fin (D.nArc + 2))
    (he : e ≠ R.smoothDeleted) :
    R.smoothArcMap ((smoothCrossing D c).continuation e) =
      (smoothCrossing E (R.crossingEquiv c)).continuation (R.smoothArcMap e) := by
  have hx : (smoothArcEquiv D).symm e ≠ Sum.inl R.deleted := by
    intro h
    exact he (by simpa only [Equiv.apply_symm_apply] using congrArg (smoothArcEquiv D) h)
  have h := R.smoothCode_continuation c ((smoothArcEquiv D).symm e) hx
  simp only [smoothArcMap, smoothCrossing, smoothContinuation, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact congrArg (smoothArcEquiv E) h

end SignedArcContraction
end
end DirectGLSSW.HOMFLY




