import DaughterTurnSigns

set_option autoImplicit false
namespace DirectGLSSW.SmoothingTurnCount
open DaughterFirstReturn DaughterTurns GeometricSmoothingWeights PermutationOrbits
open scoped BigOperators
noncomputable section

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
variable (S : Finset (PolygonCrossing q))

abbrev RetainedEvent := {x : PolygonEvent q // retainedCorner q S x}

noncomputable instance retainedEventFintype : Fintype (RetainedEvent q S) := by
  classical
  unfold RetainedEvent
  infer_instance

abbrev AllCorners := Σ c : Component (smoothingDartPermutation q hq.g2 S),
  Fin (Fintype.card (CornerCoord q hq.g2 S (componentRoot q hq S c)))

def allCornersEvent (z : AllCorners q hq S) : RetainedEvent q S :=
  ⟨orbitEventAt q hq.g2 S (componentRoot q hq S z.1)
    (cornerEnumeration q hq.g2 S (componentRoot q hq S z.1) z.2).val,
    (cornerEnumeration q hq.g2 S (componentRoot q hq S z.1) z.2).property⟩

theorem allCornersEvent_component (z : AllCorners q hq S) :
    componentOf (smoothingDartPermutation q hq.g2 S) (allCornersEvent q hq S z).val = z.1 := by
  exact (orbitEnumeration (smoothingDartPermutation q hq.g2 S) (componentRoot q hq S z.1)
    (cornerEnumeration q hq.g2 S (componentRoot q hq S z.1) z.2).val).property.trans
      (componentRoot_sameComponent q hq S z.1)

theorem allCornersEvent_bijective : Function.Bijective (allCornersEvent q hq S) := by
  constructor
  · rintro ⟨c,i⟩ ⟨d,j⟩ h
    have he := congrArg Subtype.val h
    have hc : c = d := by
      exact (allCornersEvent_component q hq S ⟨c,i⟩).symm.trans
        ((congrArg (componentOf (smoothingDartPermutation q hq.g2 S)) he).trans
          (allCornersEvent_component q hq S ⟨d,j⟩))
    cases hc
    have hij : i = j := by
      apply (cornerEnumeration q hq.g2 S (componentRoot q hq S c)).injective
      apply Subtype.ext
      apply (orbitEnumeration (smoothingDartPermutation q hq.g2 S) (componentRoot q hq S c)).injective
      apply Subtype.ext
      exact he
    cases hij
    rfl
  · intro x
    let c := componentOf (smoothingDartPermutation q hq.g2 S) x.val
    let r := componentRoot q hq S c
    let v : Fibre (smoothingDartPermutation q hq.g2 S)
        (componentOf (smoothingDartPermutation q hq.g2 S) r) :=
      ⟨x.val, (componentRoot_sameComponent q hq S c).symm⟩
    let k := (orbitEnumeration (smoothingDartPermutation q hq.g2 S) r).symm v
    have hk : orbitEventAt q hq.g2 S r k = x.val := by
      exact congrArg Subtype.val
        ((orbitEnumeration (smoothingDartPermutation q hq.g2 S) r).apply_symm_apply v)
    let corner : CornerCoord q hq.g2 S r := ⟨k, by rw [hk]; exact x.property⟩
    let i := (cornerEnumeration q hq.g2 S r).symm corner
    refine ⟨⟨c,i⟩, ?_⟩
    apply Subtype.ext
    change orbitEventAt q hq.g2 S r (cornerEnumeration q hq.g2 S r i).val = x.val
    rw [show cornerEnumeration q hq.g2 S r i = corner from
      (cornerEnumeration q hq.g2 S r).apply_symm_apply corner]
    exact hk

def allCornersEquiv : AllCorners q hq S ≃ RetainedEvent q S :=
  Equiv.ofBijective (allCornersEvent q hq S) (allCornersEvent_bijective q hq S)

def retainedEventEquiv : RetainedEvent q S ≃ Fin n ⊕ (S × Bool) where
  toFun x := match x with
    | ⟨.inl i, _⟩ => .inl i
    | ⟨.inr (c,b), h⟩ => .inr (⟨c,h⟩, b)
  invFun x := match x with
    | .inl i => ⟨.inl i, trivial⟩
    | .inr (c,b) => ⟨.inr (c.val,b), c.property⟩
  left_inv := by rintro ⟨x,h⟩; cases x with
    | inl i => rfl
    | inr v => cases v; rfl
  right_inv := by intro x; cases x with
    | inl i => rfl
    | inr v => cases v; rfl

theorem sum_daughter_leftTurns_eq_retained :
    (∑ c : Component (smoothingDartPermutation q hq.g2 S),
      leftTurnCount (componentPolygon q hq S c)) =
    ∑ x : RetainedEvent q S, if 0 < eventTurnValue q x.val then 1 else 0 := by
  classical
  calc
    _ = ∑ z : AllCorners q hq S,
        if 0 < eventTurnValue q (allCornersEvent q hq S z).val then 1 else 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro c hc
      unfold leftTurnCount
      apply Finset.sum_congr rfl
      intro i hi
      exact if_congr (daughter_leftTurn_iff q hq.g2 S hq.size_ge_three
        (componentRoot q hq S c) (componentRoot_retainedCorner q hq S c) i) rfl rfl
    _ = _ := Fintype.sum_equiv (allCornersEquiv q hq S) _ _ (fun _ => rfl)

/-- Each selected crossing contributes one left corner, in addition to all original left corners.
This holds for every actual smoothing support; daughter G1 and auxiliary genericity are absent. -/
theorem sum_daughter_leftTurnCount :
    (∑ c : Component (smoothingDartPermutation q hq.g2 S),
      leftTurnCount (componentPolygon q hq S c)) = leftTurnCount q + S.card := by
  classical
  rw [sum_daughter_leftTurns_eq_retained]
  let f : Fin n ⊕ (S × Bool) → ℕ := fun x => match x with
    | .inl i => if 0 < turnValue q i then 1 else 0
    | .inr (c,b) => if 0 < eventTurnValue q (.inr (c.val,b)) then 1 else 0
  have hsum : (∑ x : RetainedEvent q S, if 0 < eventTurnValue q x.val then 1 else 0) =
      ∑ x : Fin n ⊕ (S × Bool), f x := by
    apply Fintype.sum_equiv (retainedEventEquiv q S)
    rintro ⟨x,h⟩
    cases x with
    | inl i => rfl
    | inr v => cases v; rfl
  rw [hsum, Fintype.sum_sum_type]
  change leftTurnCount q + (∑ x : S × Bool,
    if 0 < eventTurnValue q (.inr (x.1.val,x.2)) then 1 else 0) = _
  rw [Fintype.sum_prod_type]
  simp only [crossing_leftTurn_sum q hq, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, Fintype.card_coe]

/-- Smoothing retains every original vertex and two new corners per selected crossing. -/
theorem sum_daughter_vertexCount :
    (∑ c : Component (smoothingDartPermutation q hq.g2 S),
      Fintype.card (CornerCoord q hq.g2 S (componentRoot q hq S c))) = n + 2*S.card := by
  classical
  have h := Fintype.card_congr ((allCornersEquiv q hq S).trans (retainedEventEquiv q S))
  simpa [AllCorners, Fintype.card_sigma, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm] using h









end
end DirectGLSSW.SmoothingTurnCount
