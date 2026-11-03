import ActiveArcCompatibleCanonicalJump
import CompatiblePairWeightedSum

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW Cursor RetainedWords Split SingletonWords Primitive EndpointEventGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Uniform compatible-family contribution on the explicit finite isolated
event domain. All weights, child/parent words and currents are actual. -/
theorem exists_compatible_pair_current_contribution
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR) :
    let C := GeometricSmoothingWeights.SeparatingSupport (child q hR c hc.1 hcut)
      (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
    let B := Support (parent q c hcut) (regular_parent q hR c hcut)
    let U := fun (S : C) (T : B) => (⟨pieceSelections q hR c hc hcut S.val T.val,
      (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr
        ⟨S.property,T.property⟩⟩ : Support q hR)
    let m := fun S : C => Fintype.card (DaughterFirstReturn.CornerCoord
      (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
    let F := fun (S : C) (T : B) (x : ℝ) => OpenMarkedCurrent.entry
      (polygonSignArray (moveEndpoint (eventOpenWord q hR (U S T) c) (q 1-q 0) x))
      0 (openCount q hR (U S T).val-1)
    let P := fun (S : C) (T : B) =>
      ∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple (U S T).val),
        closedWeight q hR hAux (U S T) D
    (∀ (S : C) (T : B) i j d, i<j → j<d → d≤openCount q hR (U S T).val-1 →
      (i≠0 ∨ j≠m S-1 ∨ d≠m S) → polygonHDet (eventOpenWord q hR (U S T) c) i j d≠0) →
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      (∑ S : C, ∑ T : B,
        (-1 : ℚ)^(S.val.card+T.val.card) * ((F S T ε-F S T (-ε))*P S T)) =
      scalarSignValue (planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc)) *
        (GeometricSmoothingWeights.separatingSmoothingSum
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          GammaM (parent q c hcut) (regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux)) := by
  classical
  intro C B U m F P hisolated
  let A := fun S : C => polygonAmplitude
    (DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
    (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0))
  let M := fun T : B => openCurrent (parent q c hcut) (regular_parent q hR c hcut) T
  let δ := scalarSignValue (planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc))
  let E := fun (p : C×B) (ε : ℝ) =>
    F p.1 p.2 ε-F p.1 p.2 (-ε)=δ*A p.1*M p.2
  have hlocal : ∀ p : C×B, p∈(Finset.univ : Finset (C×B)) →
      ∃ r : ℝ, 0<r ∧ ∀ ε : ℝ, 0<ε → ε<r → E p ε := by
    intro p _
    obtain ⟨r,hr,hjump⟩ := exists_compatible_openCurrent_canonical_jump
      q hR c hc hcut hRI hAux p.1 p.2 (hisolated p.1 p.2)
    refine ⟨r,hr,?_⟩
    intro ε he her
    exact (hjump ε he her).2.2
  obtain ⟨ρ,hρ,hall⟩ := ShortEdgeSignStability.exists_finset_common_radius Finset.univ E hlocal
  refine ⟨ρ,hρ,?_⟩
  intro ε he her
  have hfac := compatible_pair_weighted_sum_factorization q hR c hc hcut hRI hAux
  have heach (S : C) (T : B) : F S T ε-F S T (-ε)=δ*A S*M T :=
    hall ε he her (S,T) (Finset.mem_univ _)
  calc
    _ = ∑ S : C, ∑ T : B,
        δ*((-1 : ℚ)^(S.val.card+T.val.card)*(M T*(A S*P S T))) := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      rw [heach]
      ring
    _ = δ*(∑ S : C, ∑ T : B,
        (-1 : ℚ)^(S.val.card+T.val.card)*(M T*(A S*P S T))) := by
      simp only [Finset.mul_sum]
    _ = _ := congrArg (fun x : ℚ => δ*x) hfac


end DirectGLSSW.ActiveArc.CompatibleWords
