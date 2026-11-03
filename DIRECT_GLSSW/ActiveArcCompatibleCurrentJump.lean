import ActiveArcCompatibleCurrentFactors
import ActiveArcCompatibleRightGap
import OpenCurrentPositiveDirection

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW Cursor RetainedWords Split SingletonWords Primitive EndpointEventGeometry
attribute [local instance] Classical.propDecidable

private theorem cyclicGeneric_eq_length {n m : ℕ} (W : ℕ → PlanarPoint ℝ)
    (h : n=m) (hQ : CyclicGeneric (fun i : Fin m => W i.val)) :
    CyclicGeneric (fun i : Fin n => W i.val) := by
  cases h
  exact hQ

private theorem polygonAmplitude_eq_length {n m : ℕ} (W : ℕ → PlanarPoint ℝ)
    (h : n=m) (hn : CyclicGeneric (fun i : Fin n => W i.val))
    (hm : CyclicGeneric (fun i : Fin m => W i.val)) :
    polygonAmplitude (fun i : Fin n => W i.val) hn =
      polygonAmplitude (fun i : Fin m => W i.val) hm := by
  cases h
  rfl

private theorem polygonAmplitude_eq_fun {n : ℕ} (P Q : Fin n → PlanarPoint ℝ)
    (h : P=Q) (hP : CyclicGeneric P) (hQ : CyclicGeneric Q) :
    polygonAmplitude P hP=polygonAmplitude Q hQ := by
  cases h
  rfl

/-- Actual compatible child/parent current factors, with only the finite
event-isolation condition remaining explicit for this local application. -/
theorem exists_compatible_openCurrent_jump
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
      scalarSignValue (planarDet (q 1-q 0) (W m-W (m-1))) *
        polygonAmplitude (DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
          (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
          (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)) *
        openCurrent (parent q c hcut) (regular_parent q hR c hcut) T := by
  intro U m W hisolated
  obtain ⟨hm,hcount,hprefix,hQ,hparent⟩ :=
    compatible_event_current_factors q hR c hc hcut hAux S T
  change 3≤m at hm
  change CyclicGeneric (fun i : Fin m => W i.val) at hQ
  have hm1 : m-1+1=m := by omega
  have hlen : (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)).length=m := by
    simp only [DaughterFirstReturn.daughterPointList,List.length_ofFn,m]
  have hgeom := compatible_genuine_crossed_side q hR c hc hcut hAux S T
  dsimp only at hgeom
  rw [hlen,hm1] at hgeom
  obtain ⟨hk,hkn,⟨s,hs0,hs1,hcross⟩,htrans⟩ := hgeom
  change m<openCount q hR U.val at hkn
  obtain ⟨β,hβ,hdir⟩ := eventOpenWord_first_direction_positive q hR c hc U
    (cut_not_mem_pieceSelections q hR c hc hcut S.val T.val)
  change W 1-W 0=β • (q 1-q 0) at hdir
  have hdet : planarDet (W 1-W 0) (W m-W (m-1)) =
      β*planarDet (q 1-q 0) (W m-W (m-1)) := by
    rw [hdir]
    simp only [planarDet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  have hvtrans : planarDet (q 1-q 0) (W m-W (m-1))≠0 := by
    intro hz
    apply htrans
    rw [hdet,hz,mul_zero]
  have hKN : m-1<openCount q hR U.val-1 := by omega
  have hcross' : W 0=affinePoint (W (m-1)) (W (m-1+1)) s := by
    simpa only [hm1] using hcross
  have htrans' : planarDet (q 1-q 0) (W (m-1+1)-W (m-1))≠0 := by
    simpa only [hm1] using hvtrans
  have hiso : ∀ i j d, i<j → j<d → d≤openCount q hR U.val-1 →
      (i≠0 ∨ j≠m-1 ∨ d≠m-1+1) → polygonHDet W i j d≠0 := by
    simpa only [hm1] using hisolated
  have hQ' : CyclicGeneric (fun i : Fin (m-1+1) => W i.val) :=
    cyclicGeneric_eq_length W hm1 hQ
  obtain ⟨ρ,hρ,hjump⟩ := exists_boundary_polygon_jump_positive_direction hRI W
    (q 1-q 0) β hβ hdir (openCount q hR U.val-1) (m-1) hKN s
    hs0 hs1 hcross' htrans' hiso hQ'
  refine ⟨ρ,hρ,?_⟩
  intro ε he her
  obtain ⟨hp,hn,hvalue⟩ := hjump ε he her
  simp only [hm1] at hvalue
  have hf : (fun i : Fin m => W i.val)=
      DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0) := funext hprefix
  have hamp := polygonAmplitude_eq_length W hm1 hQ' hQ
  have hampQ := polygonAmplitude_eq_fun _ _ hf hQ
    (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0))
  rw [hamp,hampQ,hparent] at hvalue
  exact ⟨hp,hn,hvalue⟩


end DirectGLSSW.ActiveArc.CompatibleWords
