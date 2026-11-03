import ReversalContract.Contract

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW

open DirectGLSSW.GeminiReversalContract
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.DaughterFirstReturn
open DirectGLSSW.GeometricSmoothingWeights
open scoped BigOperators

section SeparatingVertexCount

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
  (S : Finset (PolygonCrossing q))

def cornerCoordEquivFibre (C : Component (smoothingDartPermutation q hq.g2 S)) :
    CornerCoord q hq.g2 S (componentRoot q hq S C) ≃
      {x : Fibre (smoothingDartPermutation q hq.g2 S) C //
        retainedCorner q S x.val} :=
  let p := smoothingDartPermutation q hq.g2 S
  let root := componentRoot q hq S C
  have hroot : componentOf p root = C := componentRoot_sameComponent q hq S C
  { toFun := fun i =>
      ⟨⟨orbitEventAt q hq.g2 S root i.val,
        (orbitEnumeration p root i.val).property.trans hroot⟩,
       i.property⟩
    invFun := fun x =>
      ⟨(orbitEnumeration p root).symm ⟨x.val.val, x.val.property.trans hroot.symm⟩,
       by
         have h := (orbitEnumeration p root).apply_symm_apply
           ⟨x.val.val, x.val.property.trans hroot.symm⟩
         have hval : orbitEventAt q hq.g2 S root
             ((orbitEnumeration p root).symm ⟨x.val.val, x.val.property.trans hroot.symm⟩) =
             x.val.val := congrArg Subtype.val h
         rw [hval]
         exact x.property⟩
    left_inv := fun i => by
      apply Subtype.ext
      exact (orbitEnumeration p root).symm_apply_apply i.val
    right_inv := fun x => by
      apply Subtype.ext
      apply Subtype.ext
      change (orbitEnumeration p root
        ((orbitEnumeration p root).symm ⟨x.val.val, x.val.property.trans hroot.symm⟩)).val =
        x.val.val
      exact congrArg Subtype.val ((orbitEnumeration p root).apply_symm_apply
        ⟨x.val.val, x.val.property.trans hroot.symm⟩) }

def sigmaCornerFibreEquiv :
    (Σ C : Component (smoothingDartPermutation q hq.g2 S),
      {x : Fibre (smoothingDartPermutation q hq.g2 S) C //
        retainedCorner q S x.val}) ≃
      {x : PolygonEvent q // retainedCorner q S x} where
  toFun z := ⟨z.2.val.val, z.2.property⟩
  invFun x := ⟨componentOf (smoothingDartPermutation q hq.g2 S) x.val, ⟨⟨x.val, rfl⟩, x.property⟩⟩
  left_inv := by
    rintro ⟨C, ⟨⟨x, hx⟩, hret⟩⟩
    subst hx
    rfl
  right_inv := by
    rintro ⟨x, hret⟩
    rfl

def retainedCornerEquiv :
    {x : PolygonEvent q // retainedCorner q S x} ≃ (Fin n ⊕ (S × Bool)) where
  toFun x := match x with
    | ⟨.inl e, _⟩ => .inl e
    | ⟨.inr ⟨c, b⟩, h⟩ => .inr (⟨c, h⟩, b)
  invFun y := match y with
    | .inl e => ⟨.inl e, trivial⟩
    | .inr ⟨⟨c, hc⟩, b⟩ => ⟨.inr (c, b), hc⟩
  left_inv := by
    rintro ⟨x, h⟩
    rcases x with e | ⟨c, b⟩ <;> rfl
  right_inv := by
    rintro y
    rcases y with e | ⟨⟨c, hc⟩, b⟩ <;> rfl

theorem smoothingVertexCount_eq :
    smoothingVertexCount q hq S = n + 2 * S.card := by
  classical
  unfold smoothingVertexCount
  have h1 : (∑ C : Component (smoothingDartPermutation q hq.g2 S),
      Fintype.card (CornerCoord q hq.g2 S (componentRoot q hq S C))) =
      ∑ C : Component (smoothingDartPermutation q hq.g2 S),
        Fintype.card {x : Fibre (smoothingDartPermutation q hq.g2 S) C //
          retainedCorner q S x.val} := by
    refine Finset.sum_congr rfl fun C _ => ?_
    exact Fintype.card_congr (cornerCoordEquivFibre q hq S C)
  rw [h1, ← Fintype.card_sigma]
  rw [Fintype.card_congr ((sigmaCornerFibreEquiv q hq S).trans (retainedCornerEquiv q S))]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    Fintype.card_bool, Nat.mul_comm]

theorem separating_vertex_count_thm :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (S : Finset (PolygonCrossing q))
      (_hS : PolygonNonalternation.polygonNonalternating q hq.g2 S),
      smoothingVertexCount q hq S = n + 2 * S.card := by
  intro n q hq S _hS
  exact smoothingVertexCount_eq q hq S

end SeparatingVertexCount

end DirectGLSSW
