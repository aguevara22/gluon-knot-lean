import ActiveArcCompatibleCurrentJump
import ActiveArcCompatibleCrossedSign

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW Cursor RetainedWords Split SingletonWords Primitive EndpointEventGeometry
attribute [local instance] Classical.propDecidable

/-- The actual compatible current jump with the original crossing's canonical
sign; only finite determinant event isolation remains conditional. -/
theorem exists_compatible_openCurrent_canonical_jump
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S})
    (T : Support (parent q c hcut) (regular_parent q hR c hcut)) :
    let U : Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
      (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr
        ⟨S.property,T.property⟩⟩
    let m := Fintype.card (DaughterFirstReturn.CornerCoord (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
    let W := eventOpenWord q hR U c
    (∀ i j d, i<j → j<d → d≤openCount q hR U.val-1 →
      (i≠0 ∨ j≠m-1 ∨ d≠m) → polygonHDet W i j d≠0) →
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (q 1-q 0) ε)
        (openCount q hR U.val-1) ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (q 1-q 0) (-ε))
        (openCount q hR U.val-1) ∧
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W (q 1-q 0) ε))
          0 (openCount q hR U.val-1) -
        OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W (q 1-q 0) (-ε)))
          0 (openCount q hR U.val-1) =
      scalarSignValue (planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc)) *
        polygonAmplitude (DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
          (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
          (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)) *
        openCurrent (parent q c hcut) (regular_parent q hR c hcut) T := by
  intro U m W hisolated
  obtain ⟨ρ,hρ,hjump⟩ := exists_compatible_openCurrent_jump q hR c hc hcut hRI hAux S T hisolated
  have hsign := compatible_crossed_side_sign q hR c hc hcut hAux S T
  dsimp only at hsign
  have hlen : (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)).length=m := by
    simp only [DaughterFirstReturn.daughterPointList,List.length_ofFn,m]
  have hm : 3≤m := (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)).size_ge_three
  have hm1 : m-1+1=m := by omega
  rw [hlen,hm1] at hsign
  refine ⟨ρ,hρ,?_⟩
  intro ε he her
  obtain ⟨hp,hn,hvalue⟩ := hjump ε he her
  rw [hsign] at hvalue
  exact ⟨hp,hn,hvalue⟩


end DirectGLSSW.ActiveArc.CompatibleWords
