import DirectGLSSW.HOMFLY.HOMFYSmoothingCombinatorics
import DirectGLSSW.HOMFLY.HOMFYSmoothingContinuationOtherCrossing
import DirectGLSSW.HOMFLY.HOMFYSmoothingRegularDegree
import DirectGLSSW.HOMFLY.HOMFYSmoothingVertexInjective
import DirectGLSSW.HOMFLY.HOMFYSmoothingArcEndpointDistinct
import DirectGLSSW.HOMFLY.HOMFYSmoothingOtherCrossingTangent
import DirectGLSSW.HOMFLY.HOMFYSmoothingConnectorInteriors
import DirectGLSSW.HOMFLY.HOMFYSmoothingVertexArcAvoid

namespace DirectGLSSW.HOMFLY

private theorem finTwoDiagramCases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

noncomputable def smoothRadius (D : PLLinkDiagram) (c : Fin D.nCrossing) : ℝ :=
  Classical.choose (exists_connector_nonincident_clearance D c)

theorem smoothRadius_pos (D : PLLinkDiagram) (c : Fin D.nCrossing) : 0 < smoothRadius D c :=
  (Classical.choose_spec (exists_connector_nonincident_clearance D c)).1

theorem smoothRadius_le_cutoff (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    smoothRadius D c ≤ crossingCutoffRadius D c :=
  (Classical.choose_spec (exists_connector_nonincident_clearance D c)).2.1

noncomputable def smoothEpsilon (D : PLLinkDiagram) (c : Fin D.nCrossing) : ℝ := smoothRadius D c / 2

theorem smoothEpsilon_pos (D : PLLinkDiagram) (c : Fin D.nCrossing) : 0 < smoothEpsilon D c :=
  div_pos (smoothRadius_pos D c) (by norm_num)

theorem smoothEpsilon_lt_radius (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    smoothEpsilon D c < smoothRadius D c := by
  dsimp [smoothEpsilon]
  linarith [smoothRadius_pos D c]

noncomputable def smoothVertexPoint (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nVertex + 3) → PlanarPoint ℝ := fun v =>
  smoothVertexPointGeometryCode D c (smoothEpsilon D c) ((smoothVertexEquiv D c).symm v)

noncomputable def smoothArcSource (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nArc + 2) → Fin (D.nVertex + 3) := fun e =>
  smoothVertexEquiv D c (smoothArcSourceCode D c ((smoothArcEquiv D).symm e))

noncomputable def smoothArcTarget (D : PLLinkDiagram) (c : Fin D.nCrossing) :
  Fin (D.nArc + 2) → Fin (D.nVertex + 3) := fun e =>
  smoothVertexEquiv D c (smoothArcTargetGeometryCode D c ((smoothArcEquiv D).symm e))

noncomputable def smoothCrossingVertex (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nCrossing - 1) → Fin (D.nVertex + 3) := fun d =>
  smoothVertexEquiv D c (Sum.inl (D.crossingVertex ((smoothCrossingEquiv D c).symm d).val))

noncomputable def smoothIncoming (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nCrossing - 1) → Fin 2 → Fin (D.nArc + 2) := fun d i =>
  smoothArcEquiv D (Sum.inl (D.incoming ((smoothCrossingEquiv D c).symm d).val i))

noncomputable def smoothOutgoing (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nCrossing - 1) → Fin 2 → Fin (D.nArc + 2) := fun d i =>
  smoothArcEquiv D (Sum.inl (D.outgoing ((smoothCrossingEquiv D c).symm d).val i))

noncomputable def smoothThrough (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nCrossing - 1) → Equiv.Perm (Fin 2) := fun d =>
  D.through ((smoothCrossingEquiv D c).symm d).val

noncomputable def smoothContinuation (D : PLLinkDiagram) (c : Fin D.nCrossing) :
  Equiv.Perm (Fin (D.nArc + 2)) :=
  (smoothArcEquiv D).symm.trans ((smoothContinuationGeometryCode D c).trans (smoothArcEquiv D))

noncomputable def smoothCrossing (D : PLLinkDiagram) (c : Fin D.nCrossing) : PLLinkDiagram := by
  classical
  refine {
    nVertex := D.nVertex + 3
    nArc := D.nArc + 2
    nCrossing := D.nCrossing - 1
    vertexPoint := smoothVertexPoint D c
    arcSource := smoothArcSource D c
    arcTarget := smoothArcTarget D c
    crossingVertex := smoothCrossingVertex D c
    crossingVertex_injective := by
      intro x y hxy
      have hcode := (smoothVertexEquiv D c).injective hxy
      have hval := D.crossingVertex_injective (Sum.inl.inj hcode)
      have hinv : (smoothCrossingEquiv D c).symm x =
          (smoothCrossingEquiv D c).symm y := Subtype.ext hval
      exact (smoothCrossingEquiv D c).symm.injective hinv
    incoming := smoothIncoming D c
    outgoing := smoothOutgoing D c
    incoming_target := by
      intro d i
      let old := (smoothCrossingEquiv D c).symm d
      have holdc : old.val ≠ c := old.property
      have hin0 : D.incoming old.val i ≠ D.incoming c 0 := by
        intro heq
        apply holdc
        apply D.crossingVertex_injective
        calc
          D.crossingVertex old.val = D.arcTarget (D.incoming old.val i) :=
            (D.incoming_target old.val i).symm
          _ = D.arcTarget (D.incoming c 0) := by rw [heq]
          _ = D.crossingVertex c := D.incoming_target c 0
      have hin1 : D.incoming old.val i ≠ D.incoming c 1 := by
        intro heq
        apply holdc
        apply D.crossingVertex_injective
        calc
          D.crossingVertex old.val = D.arcTarget (D.incoming old.val i) :=
            (D.incoming_target old.val i).symm
          _ = D.arcTarget (D.incoming c 1) := by rw [heq]
          _ = D.crossingVertex c := D.incoming_target c 1
      dsimp [smoothArcTarget, smoothIncoming, smoothCrossingVertex]
      simp only [Equiv.symm_apply_apply]
      congr 1
      change smoothArcTargetCode D c (Sum.inl (D.incoming old.val i)) =
        Sum.inl (D.crossingVertex old.val)
      simp [smoothArcTargetCode, hin0, hin1, D.incoming_target]
    outgoing_source := by
      intro d i
      let old := (smoothCrossingEquiv D c).symm d
      have holdc : old.val ≠ c := old.property
      have hout0 : D.outgoing old.val i ≠ D.outgoing c 0 := by
        intro heq
        apply holdc
        apply D.crossingVertex_injective
        calc
          D.crossingVertex old.val = D.arcSource (D.outgoing old.val i) :=
            (D.outgoing_source old.val i).symm
          _ = D.arcSource (D.outgoing c 0) := by rw [heq]
          _ = D.crossingVertex c := D.outgoing_source c 0
      have hout1 : D.outgoing old.val i ≠ D.outgoing c 1 := by
        intro heq
        apply holdc
        apply D.crossingVertex_injective
        calc
          D.crossingVertex old.val = D.arcSource (D.outgoing old.val i) :=
            (D.outgoing_source old.val i).symm
          _ = D.arcSource (D.outgoing c 1) := by rw [heq]
          _ = D.crossingVertex c := D.outgoing_source c 1
      dsimp [smoothArcSource, smoothOutgoing, smoothCrossingVertex]
      simp only [Equiv.symm_apply_apply]
      congr 1
      simp [smoothArcSourceCode, hout0, hout1, D.outgoing_source, old]
    four_ports_distinct := by
      intro d
      let old := (smoothCrossingEquiv D c).symm d
      rcases D.four_ports_distinct old.val with ⟨hin, hout, hcross⟩
      constructor
      · intro heq
        apply hin
        exact Sum.inl.inj ((smoothArcEquiv D).injective heq)
      constructor
      · intro heq
        apply hout
        exact Sum.inl.inj ((smoothArcEquiv D).injective heq)
      · intro i j heq
        apply hcross i j
        exact Sum.inl.inj ((smoothArcEquiv D).injective heq)
    crossing_incidence_complete := by
      intro d e
      let oldc := (smoothCrossingEquiv D c).symm d
      let olde := (smoothArcEquiv D).symm e
      have hs : smoothArcSource D c e = smoothCrossingVertex D c d ↔
          smoothArcSourceCode D c olde = Sum.inl (D.crossingVertex oldc.val) := by
        change (smoothVertexEquiv D c (smoothArcSourceCode D c olde) =
          smoothVertexEquiv D c (Sum.inl (D.crossingVertex oldc.val))) ↔ _
        constructor
        · intro h
          exact (smoothVertexEquiv D c).injective h
        · intro h
          exact congrArg (smoothVertexEquiv D c) h
      have ht : smoothArcTarget D c e = smoothCrossingVertex D c d ↔
          smoothArcTargetGeometryCode D c olde = Sum.inl (D.crossingVertex oldc.val) := by
        change (smoothVertexEquiv D c (smoothArcTargetGeometryCode D c olde) =
          smoothVertexEquiv D c (Sum.inl (D.crossingVertex oldc.val))) ↔ _
        constructor
        · intro h
          exact (smoothVertexEquiv D c).injective h
        · intro h
          exact congrArg (smoothVertexEquiv D c) h
      have hi0 : e = smoothIncoming D c d 0 ↔
          olde = Sum.inl (D.incoming oldc.val 0) := by
        change e = smoothArcEquiv D (Sum.inl (D.incoming oldc.val 0)) ↔ _
        constructor
        · intro h
          have hh := congrArg (smoothArcEquiv D).symm h
          simpa using hh
        · intro h
          simpa [olde] using congrArg (smoothArcEquiv D) h
      have hi1 : e = smoothIncoming D c d 1 ↔
          olde = Sum.inl (D.incoming oldc.val 1) := by
        change e = smoothArcEquiv D (Sum.inl (D.incoming oldc.val 1)) ↔ _
        constructor
        · intro h
          have hh := congrArg (smoothArcEquiv D).symm h
          simpa using hh
        · intro h
          simpa [olde] using congrArg (smoothArcEquiv D) h
      have ho0 : e = smoothOutgoing D c d 0 ↔
          olde = Sum.inl (D.outgoing oldc.val 0) := by
        change e = smoothArcEquiv D (Sum.inl (D.outgoing oldc.val 0)) ↔ _
        constructor
        · intro h
          have hh := congrArg (smoothArcEquiv D).symm h
          simpa using hh
        · intro h
          simpa [olde] using congrArg (smoothArcEquiv D) h
      have ho1 : e = smoothOutgoing D c d 1 ↔
          olde = Sum.inl (D.outgoing oldc.val 1) := by
        change e = smoothArcEquiv D (Sum.inl (D.outgoing oldc.val 1)) ↔ _
        constructor
        · intro h
          have hh := congrArg (smoothArcEquiv D).symm h
          simpa using hh
        · intro h
          simpa [olde] using congrArg (smoothArcEquiv D) h
      rw [hs, ht, hi0, hi1, ho0, ho1]
      cases olde with
      | inl e => simpa [smoothArcSourceCode, smoothArcTargetGeometryCode] using
          smoothArcCode_crossing_incidence_complete D c oldc (Sum.inl e)
      | inr i =>
          have hcv : D.crossingVertex c ≠ D.crossingVertex oldc.val := by
            intro h
            exact oldc.property (D.crossingVertex_injective h.symm)
          have htarget : ∀ i : Fin 2, smoothArcTargetGeometryCode D c (Sum.inr i) ≠
              Sum.inl (D.crossingVertex oldc.val) := by
            intro i
            let j := D.through c (otherBranch i)
            have hjcases : j = 0 ∨ j = 1 := finTwoDiagramCases j
            rcases hjcases with hj | hj
            · change smoothRightCutCode D c j ≠ _
              rw [hj]
              simp [smoothRightCutCode]
            · change smoothRightCutCode D c j ≠ _
              rw [hj]
              simp [smoothRightCutCode]
          fin_cases i
          · have hsrc : smoothArcSourceCode D c (Sum.inr 0) ≠
                Sum.inl (D.crossingVertex oldc.val) := by
              simp [smoothArcSourceCode, smoothLeftCutCode, hcv]
            constructor
            · intro he
              rcases he with hs | ht
              · exact False.elim (hsrc hs)
              · exact False.elim (htarget 0 ht)
            · intro hp
              simp [smoothArcSourceCode, smoothLeftCutCode, hcv] at hp
          · have hsrc : smoothArcSourceCode D c (Sum.inr 1) ≠
                Sum.inl (D.crossingVertex oldc.val) := by
              simp [smoothArcSourceCode, smoothLeftCutCode]
            constructor
            · intro he
              rcases he with hs | ht
              · exact False.elim (hsrc hs)
              · exact False.elim (htarget 1 ht)
            · intro hp
              simp [smoothArcSourceCode, smoothLeftCutCode] at hp
    regular_degree_one := by
      intro v hv
      exact smoothGeometryRegularDegreeOne D c v hv
    through := smoothThrough D c
    continuation := smoothContinuation D c
    continuation_incidence := by
      intro e
      simp only [smoothArcTarget, smoothArcSource, smoothContinuation,
        Equiv.trans_apply, Equiv.symm_apply_apply]
      congr 1
      exact smoothArcTargetGeometryCode_continuationGeometryCode D c ((smoothArcEquiv D).symm e)
    continuation_crossing := by
      intro d i
      let old := (smoothCrossingEquiv D c).symm d
      have hgeom := smoothContinuationGeometryCode_other_incoming_transition D c old i
      simp only [smoothContinuation, smoothIncoming, smoothOutgoing, smoothThrough,
        Equiv.trans_apply, Equiv.symm_apply_apply]
      exact congrArg (smoothArcEquiv D) hgeom
    overBranch := fun d => D.overBranch ((smoothCrossingEquiv D c).symm d).val
    vertexPoint_injective := by
      intro v w hvw
      apply (smoothVertexEquiv D c).symm.injective
      apply smoothVertexPointGeometryCode_injective D c (smoothEpsilon D c)
        (smoothEpsilon_pos D c)
        (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c))
      exact hvw
    arc_endpoints_distinct := by
      intro e heq
      have hcode := (smoothVertexEquiv D c).injective heq
      exact smoothGeometryArcCode_source_target_ne D c ((smoothArcEquiv D).symm e) hcode
    arc_interiors_disjoint := by
      intro e f hef s t hs0 hs1 ht0 ht1
      let ec := (smoothArcEquiv D).symm e
      let fc := (smoothArcEquiv D).symm f
      have hcode : ec ≠ fc := by
        intro h
        apply hef
        calc
          e = smoothArcEquiv D ec := (Equiv.apply_symm_apply (smoothArcEquiv D) e).symm
          _ = smoothArcEquiv D fc := congrArg (smoothArcEquiv D) h
          _ = f := Equiv.apply_symm_apply (smoothArcEquiv D) f
      have hρ : smoothEpsilon D c < smoothRadius D c := smoothEpsilon_lt_radius D c
      have hcut : smoothEpsilon D c < crossingCutoffRadius D c :=
        lt_of_lt_of_le hρ (smoothRadius_le_cutoff D c)
      have hclear := (Classical.choose_spec (exists_connector_nonincident_clearance D c)).2.2
      simpa [smoothArcSource, smoothArcTarget, smoothVertexPoint,
        smoothGeometryCodeArcPoint, ec, fc] using
        smoothGeometryCodeArc_interiors_disjoint D c (smoothEpsilon D c)
        (smoothRadius D c) (smoothEpsilon_pos D c) hρ hcut hclear
        ec fc hcode s t hs0 hs1 ht0 ht1
    vertices_avoid_arc_interiors := by
      intro v e t ht0 ht1
      simp only [smoothVertexPoint, smoothArcSource, smoothArcTarget,
        Equiv.symm_apply_apply]
      let x := (smoothVertexEquiv D c).symm v
      let a := (smoothArcEquiv D).symm e
      change smoothVertexPointGeometryCode D c (smoothEpsilon D c) x ≠
        DirectGLSSW.affinePoint
          (smoothVertexPointGeometryCode D c (smoothEpsilon D c)
            (smoothArcSourceCode D c a))
          (smoothVertexPointGeometryCode D c (smoothEpsilon D c)
            (smoothArcTargetGeometryCode D c a)) t
      have hρ : smoothEpsilon D c < smoothRadius D c := smoothEpsilon_lt_radius D c
      have hcut : smoothEpsilon D c < crossingCutoffRadius D c :=
        lt_of_lt_of_le hρ (smoothRadius_le_cutoff D c)
      have hclear := (Classical.choose_spec (exists_connector_nonincident_clearance D c)).2.2
      rcases smoothVertexPointGeometryCode_cutpoint_or_old D c x with hcutpoint | holdvertex
      · obtain ⟨k, hk⟩ := hcutpoint
        rw [hk]
        cases a with
        | inl old =>
            exact smoothCutLabel_oldArc_interior_avoid D c (smoothEpsilon D c)
              (smoothEpsilon_pos D c) hcut k old t ht0 ht1
        | inr i =>
            exact smoothCutLabel_connector_interior_avoid D c (smoothEpsilon D c)
              (smoothEpsilon_pos D c) hcut k i t ht0 ht1
      · obtain ⟨oldv, hx, hvc⟩ := holdvertex
        rw [hx]
        cases a with
        | inl old =>
            exact smoothOldVertex_oldArc_interior_avoid D c (smoothEpsilon D c)
              (smoothEpsilon_pos D c) hcut oldv hvc old t ht0 ht1
        | inr i =>
            exact smoothOldVertex_connector_interior_avoid D c (smoothEpsilon D c)
              (smoothRadius D c) (smoothEpsilon_pos D c) hρ hcut hclear oldv hvc i t ht0 ht1
    through_tangents_positive_collinear := by
      intro d i
      let old := (smoothCrossingEquiv D c).symm d
      have hdc : old.val ≠ c := old.property
      obtain ⟨α, hα, hsrc⟩ := smoothIncomingSourceVector_positive_multiple D c old.val i
        (smoothEpsilon D c) (smoothEpsilon_pos D c)
        (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)) hdc
      obtain ⟨β, hβ, htgt⟩ := smoothOutgoingTargetVector_positive_multiple D c old.val
        (D.through old.val i) (smoothEpsilon D c) (smoothEpsilon_pos D c)
        (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)) hdc
      obtain ⟨μ, hμ, hold⟩ := D.through_tangents_positive_collinear old.val i
      refine ⟨α * μ / β, div_pos (mul_pos hα hμ) hβ, ?_⟩
      have hcv : D.crossingVertex old.val ≠ D.crossingVertex c := by
        intro h
        exact hdc (D.crossingVertex_injective h)
      have hcrosspt : smoothVertexPoint D c (smoothCrossingVertex D c d) =
          D.vertexPoint (D.crossingVertex old.val) := by
        simp [smoothVertexPoint, smoothCrossingVertex, smoothVertexPointGeometryCode, old, hcv]
      have hsourcept : smoothVertexPoint D c
          (smoothArcSource D c (smoothIncoming D c d i)) =
          smoothVertexPointGeometryCode D c (smoothEpsilon D c)
            (smoothArcSourceCode D c (Sum.inl (D.incoming old.val i))) := by
        simp [old, smoothVertexPoint, smoothArcSource, smoothIncoming] <;> rfl
      have htargetpt : smoothVertexPoint D c
          (smoothArcTarget D c (smoothOutgoing D c d (D.through old.val i))) =
          smoothVertexPointGeometryCode D c (smoothEpsilon D c)
            (smoothArcTargetCode D c
              (Sum.inl (D.outgoing old.val (D.through old.val i)))) := by
        simp [old, smoothVertexPoint, smoothArcTarget, smoothOutgoing, smoothThrough] <;> rfl
      simp only [old, smoothThrough]
      rw [hcrosspt, hsourcept, htargetpt, hsrc, htgt, hold]
      calc
        α • (μ • (D.vertexPoint (D.arcTarget (D.outgoing old.val (D.through old.val i))) -
            D.vertexPoint (D.crossingVertex old.val))) =
            (α * μ) • (D.vertexPoint (D.arcTarget (D.outgoing old.val (D.through old.val i))) -
              D.vertexPoint (D.crossingVertex old.val)) := by rw [smul_smul]
        _ = (α * μ / β) • (β •
            (D.vertexPoint (D.arcTarget (D.outgoing old.val (D.through old.val i))) -
              D.vertexPoint (D.crossingVertex old.val))) := by
            rw [smul_smul]
            congr 1
            field_simp
    crossing_transverse := by
      intro d
      let old := (smoothCrossingEquiv D c).symm d
      have hdc : old.val ≠ c := old.property
      obtain ⟨α0, hα0, hsrc0⟩ := smoothIncomingSourceVector_positive_multiple D c old.val 0
        (smoothEpsilon D c) (smoothEpsilon_pos D c)
        (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)) hdc
      obtain ⟨α1, hα1, hsrc1⟩ := smoothIncomingSourceVector_positive_multiple D c old.val 1
        (smoothEpsilon D c) (smoothEpsilon_pos D c)
        (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)) hdc
      have hcv : D.crossingVertex old.val ≠ D.crossingVertex c := by
        intro h
        exact hdc (D.crossingVertex_injective h)
      have hcrosspt : smoothVertexPoint D c (smoothCrossingVertex D c d) =
          D.vertexPoint (D.crossingVertex old.val) := by
        simp [smoothVertexPoint, smoothCrossingVertex, smoothVertexPointGeometryCode, old, hcv]
      have hsourcept0 : smoothVertexPoint D c
          (smoothArcSource D c (smoothIncoming D c d 0)) =
          smoothVertexPointGeometryCode D c (smoothEpsilon D c)
            (smoothArcSourceCode D c (Sum.inl (D.incoming old.val 0))) := by
        simp [old, smoothVertexPoint, smoothArcSource, smoothIncoming] <;> rfl
      have hsourcept1 : smoothVertexPoint D c
          (smoothArcSource D c (smoothIncoming D c d 1)) =
          smoothVertexPointGeometryCode D c (smoothEpsilon D c)
            (smoothArcSourceCode D c (Sum.inl (D.incoming old.val 1))) := by
        simp [old, smoothVertexPoint, smoothArcSource, smoothIncoming] <;> rfl
      rw [hcrosspt, hsourcept0, hsourcept1, hsrc0, hsrc1]
      have hscale : planarDet
          (α0 • (D.vertexPoint (D.crossingVertex old.val) -
            D.vertexPoint (D.arcSource (D.incoming old.val 0))))
          (α1 • (D.vertexPoint (D.crossingVertex old.val) -
            D.vertexPoint (D.arcSource (D.incoming old.val 1)))) =
          α0 * α1 * planarDet
            (D.vertexPoint (D.crossingVertex old.val) -
              D.vertexPoint (D.arcSource (D.incoming old.val 0)))
            (D.vertexPoint (D.crossingVertex old.val) -
              D.vertexPoint (D.arcSource (D.incoming old.val 1))) := by
        rcases D.vertexPoint (D.crossingVertex old.val) -
            D.vertexPoint (D.arcSource (D.incoming old.val 0)) with ⟨x0, y0⟩
        rcases D.vertexPoint (D.crossingVertex old.val) -
            D.vertexPoint (D.arcSource (D.incoming old.val 1)) with ⟨x1, y1⟩
        simp [planarDet]
        ring
      rw [hscale]
      exact mul_ne_zero (mul_ne_zero (ne_of_gt hα0) (ne_of_gt hα1))
        (D.crossing_transverse old.val)
  }
  all_goals { }
