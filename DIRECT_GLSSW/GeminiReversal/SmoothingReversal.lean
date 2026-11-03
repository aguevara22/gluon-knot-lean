import GeminiReversal.SeparatingVertexCount
import GeminiReversal.AmplitudeReversal
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW

open DirectGLSSW.GeminiReversalContract
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.DaughterFirstReturn
open DirectGLSSW.GeometricSmoothingWeights
open scoped BigOperators

section AbstractReverseOrbit

theorem intertwine_pow_cancel {α β : Type*} (ψ : α ≃ β)
    (p : Equiv.Perm α) (q : Equiv.Perm β) (hψ : ∀ z, q (ψ (p z)) = ψ z)
    (k : ℕ) (z : α) :
    (q ^ k) (ψ ((p ^ k) z)) = ψ z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply,
        ih (p z), hψ z]

theorem sameCycle_iff_of_reverse_intertwining {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α ≃ β)
    (p : Equiv.Perm α) (q : Equiv.Perm β) (hψ : ∀ z, q (ψ (p z)) = ψ z)
    (x y : α) :
    q.SameCycle (ψ x) (ψ y) ↔ p.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.symm.exists_nat_pow_eq
    have h1 := intertwine_pow_cancel ψ p q hψ k x
    rw [← hk] at h1
    have h2 : ψ ((p ^ k) x) = ψ y := (q ^ k).injective h1
    exact ⟨(k : ℤ), by simpa using ψ.injective h2⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    have h1 := intertwine_pow_cancel ψ p q hψ k x
    rw [hk] at h1
    have hsc : q.SameCycle (ψ y) (ψ x) := ⟨(k : ℤ), by simpa using h1⟩
    exact hsc.symm

def componentEquivOfReverseIntertwining {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α ≃ β)
    (p : Equiv.Perm α) (q : Equiv.Perm β) (hψ : ∀ z, q (ψ (p z)) = ψ z) :
    Component p ≃ Component q :=
  Quotient.congr ψ fun x y =>
    (sameCycle_iff_of_reverse_intertwining ψ p q hψ x y).symm

@[simp] theorem componentEquivOfReverseIntertwining_componentOf
    {α β : Type*} [Fintype α] [Fintype β] (ψ : α ≃ β)
    (p : Equiv.Perm α) (q : Equiv.Perm β) (hψ : ∀ z, q (ψ (p z)) = ψ z) (x : α) :
    componentEquivOfReverseIntertwining ψ p q hψ (componentOf p x) =
      componentOf q (ψ x) := rfl

theorem componentCount_eq_of_reverse_intertwining {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α ≃ β) (p : Equiv.Perm α) (q : Equiv.Perm β) (hψ : ∀ z, q (ψ (p z)) = ψ z) :
    componentCount p = componentCount q :=
  Fintype.card_congr (componentEquivOfReverseIntertwining ψ p q hψ)

def fibreEquivOfReverseIntertwining {α β : Type*} [Fintype α] [Fintype β] (ψ : α ≃ β)
    (p : Equiv.Perm α) (q : Equiv.Perm β) (hψ : ∀ z, q (ψ (p z)) = ψ z) (x : α) :
    Fibre p (componentOf p x) ≃ Fibre q (componentOf q (ψ x)) :=
  ψ.subtypeEquiv fun z => by
    simp only [componentOf_eq_iff]
    exact (sameCycle_iff_of_reverse_intertwining ψ p q hψ z x).symm

theorem pow_card_fibre_apply {α : Type*} [Fintype α] (p : Equiv.Perm α) (x : α) :
    (p ^ Fintype.card (Fibre p (componentOf p x))) x = x := by
  classical
  let c := componentOf p x
  let x₀ : Fibre p c := ⟨x, rfl⟩
  let fp := fibrePerm p c
  have hfp : fp.IsCycleOn (Finset.univ : Finset (Fibre p c)) := by
    simpa [fp] using fibrePerm_isCycleOn p c
  have hmod : Fintype.card (Fibre p c) ≡ 0
      [MOD (Finset.univ : Finset (Fibre p c)).card] := by
    rw [Finset.card_univ]
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)
  have hpow := (hfp.pow_apply_eq_pow_apply (Finset.mem_univ x₀)).mpr hmod
  simpa [fp, x₀, fibrePerm_pow_apply_val] using congrArg Subtype.val hpow

theorem orbitWord_rotate_one_eq_reverse_map {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α ≃ β) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (hψ : ∀ z, q (ψ (p z)) = ψ z) (x : α) :
    (orbitWord q (ψ x)).rotate 1 =
      ((orbitWord p x).reverse).map ψ := by
  have hcard :
      Fintype.card (Fibre q (componentOf q (ψ x))) =
        Fintype.card (Fibre p (componentOf p x)) :=
    (Fintype.card_congr (fibreEquivOfReverseIntertwining ψ p q hψ x)).symm
  let N := Fintype.card (Fibre p (componentOf p x))
  have hpow_q : (q ^ N) (ψ x) = ψ x := by
    change (q ^ Fintype.card (Fibre p (componentOf p x))) (ψ x) = ψ x
    rw [← hcard, pow_card_fibre_apply q (ψ x)]
  have hlen_q : (orbitWord q (ψ x)).length = N := by
    rw [orbitWord_length, hcard]
  have hlen_p : (orbitWord p x).length = N :=
    orbitWord_length p x
  apply List.ext_getElem
  · simp [hlen_q, hlen_p]
  · intro i hi1 hi2
    have hiN : i < N := by simpa [hlen_q] using hi1
    have hrot := List.getElem_rotate (orbitWord q (ψ x)) 1 i hi1
    simp only [hlen_q] at hrot
    rw [hrot]
    have h_lhs :
        (orbitWord q (ψ x))[(i + 1) % N]'(by rw [hlen_q]; exact Nat.mod_lt _ (by omega)) =
          (q ^ (i + 1)) (ψ x) := by
      simp only [orbitWord, List.getElem_ofFn, orbitEnumeration_apply_val]
      by_cases hi' : i + 1 < N
      · rw [Nat.mod_eq_of_lt hi']
      · have hN : i + 1 = N := by omega
        rw [hN, Nat.mod_self, pow_zero, Equiv.Perm.one_apply, hpow_q]
    have h_rhs :
        (((orbitWord p x).reverse).map ψ)[i]'hi2 =
          ψ ((p ^ (N - 1 - i)) x) := by
      simp only [List.getElem_map, List.getElem_reverse, hlen_p,
        orbitWord, List.getElem_ofFn, orbitEnumeration_apply_val, List.length_ofFn]
      rfl
    rw [h_lhs, h_rhs]
    apply (q ^ (N - 1 - i)).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add,
      show N - 1 - i + (i + 1) = N by omega,
      hpow_q,
      intertwine_pow_cancel ψ p q hψ (N - 1 - i) x]

theorem orbitWord_reverse_map_isRotated {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α ≃ β) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (hψ : ∀ z, q (ψ (p z)) = ψ z) (x : α) :
    ((orbitWord p x).reverse).map ψ ~r orbitWord q (ψ x) :=
  List.IsRotated.symm ⟨1, orbitWord_rotate_one_eq_reverse_map ψ p q hψ x⟩

end AbstractReverseOrbit

section CrossingAndEventReversal

variable {n : ℕ}

private theorem min_max_edgeRev_lt {a b : Fin n} (hab : a < b) :
    min (edgeRev a) (edgeRev b) < max (edgeRev a) (edgeRev b) := by
  have hne : edgeRev a ≠ edgeRev b :=
    (edgeRevEquiv n).injective.ne (ne_of_lt hab)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rwa [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
  · rwa [min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt)]

private theorem min_max_edgeRev_involutive {a b : Fin n} (hab : a < b) :
    (min (edgeRev (min (edgeRev a) (edgeRev b)))
        (edgeRev (max (edgeRev a) (edgeRev b))),
      max (edgeRev (min (edgeRev a) (edgeRev b)))
        (edgeRev (max (edgeRev a) (edgeRev b)))) = (a, b) := by
  by_cases h : edgeRev a ≤ edgeRev b
  · rw [min_eq_left h, max_eq_right h, edgeRev_edgeRev, edgeRev_edgeRev,
      min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)]
  · have h' : edgeRev b ≤ edgeRev a := le_of_not_ge h
    rw [min_eq_right h', max_eq_left h', edgeRev_edgeRev, edgeRev_edgeRev,
      min_eq_right (le_of_lt hab), max_eq_left (le_of_lt hab)]

def crossingRevMap (q : Fin n → PlanarPoint ℝ) (c : PolygonCrossing q) :
    PolygonCrossing (reversePolygon q) :=
  ⟨(min (edgeRev c.val.1) (edgeRev c.val.2), max (edgeRev c.val.1) (edgeRev c.val.2)),
    min_max_edgeRev_lt c.property.1, by
      obtain ⟨x, hx1, hx2⟩ := c.property.2
      have hr1 := (edgeInterior_reversePolygon_edgeRev q c.val.1 x).mpr hx1
      have hr2 := (edgeInterior_reversePolygon_edgeRev q c.val.2 x).mpr hx2
      refine ⟨x, ?_⟩
      by_cases h : edgeRev c.val.1 ≤ edgeRev c.val.2
      · rw [min_eq_left h, max_eq_right h]
        exact ⟨hr1, hr2⟩
      · have h' : edgeRev c.val.2 ≤ edgeRev c.val.1 := le_of_not_ge h
        rw [min_eq_right h', max_eq_left h']
        exact ⟨hr2, hr1⟩⟩

def crossingRevInvMap (q : Fin n → PlanarPoint ℝ)
    (d : PolygonCrossing (reversePolygon q)) : PolygonCrossing q :=
  ⟨(min (edgeRev d.val.1) (edgeRev d.val.2), max (edgeRev d.val.1) (edgeRev d.val.2)),
    min_max_edgeRev_lt d.property.1, by
      obtain ⟨x, hx1, hx2⟩ := d.property.2
      have hr1 := (edgeInterior_reversePolygon q d.val.1 x).mp hx1
      have hr2 := (edgeInterior_reversePolygon q d.val.2 x).mp hx2
      refine ⟨x, ?_⟩
      by_cases h : edgeRev d.val.1 ≤ edgeRev d.val.2
      · rw [min_eq_left h, max_eq_right h]
        exact ⟨hr1, hr2⟩
      · have h' : edgeRev d.val.2 ≤ edgeRev d.val.1 := le_of_not_ge h
        rw [min_eq_right h', max_eq_left h']
        exact ⟨hr2, hr1⟩⟩

def crossingRevEquiv (q : Fin n → PlanarPoint ℝ) :
    PolygonCrossing q ≃ PolygonCrossing (reversePolygon q) where
  toFun := crossingRevMap q
  invFun := crossingRevInvMap q
  left_inv c := Subtype.ext (min_max_edgeRev_involutive c.property.1)
  right_inv d := Subtype.ext (min_max_edgeRev_involutive d.property.1)

theorem crossingPoint_crossingRevEquiv (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (c : PolygonCrossing q) :
    crossingPoint (reversePolygon q) (crossingRevEquiv q c) = crossingPoint q c := by
  have hqr := cyclicGeneric_reversePolygon q hq
  have hr1 := (edgeInterior_reversePolygon_edgeRev q c.val.1 (crossingPoint q c)).mpr
    (crossingPoint_mem_left q c)
  have hr2 := (edgeInterior_reversePolygon_edgeRev q c.val.2 (crossingPoint q c)).mpr
    (crossingPoint_mem_right q c)
  symm
  apply crossingPoint_eq_of_mem hqr.size_ge_three (reversePolygon q) hqr.g1
    (crossingRevEquiv q c) (crossingPoint q c)
  · change edgeInterior (reversePolygon q) (min (edgeRev c.val.1) (edgeRev c.val.2)) _
    by_cases h : edgeRev c.val.1 ≤ edgeRev c.val.2
    · rwa [min_eq_left h]
    · rwa [min_eq_right (le_of_not_ge h)]
  · change edgeInterior (reversePolygon q) (max (edgeRev c.val.1) (edgeRev c.val.2)) _
    by_cases h : edgeRev c.val.1 ≤ edgeRev c.val.2
    · rwa [max_eq_right h]
    · rwa [max_eq_left (le_of_not_ge h)]

def visitRevMap (q : Fin n → PlanarPoint ℝ) (v : CrossingVisit q) :
    CrossingVisit (reversePolygon q) :=
  (crossingRevEquiv q v.1,
    if edgeRev v.1.val.1 < edgeRev v.1.val.2 then v.2 else !v.2)

def visitRevInvMap (q : Fin n → PlanarPoint ℝ)
    (w : CrossingVisit (reversePolygon q)) : CrossingVisit q :=
  ((crossingRevEquiv q).symm w.1,
    if edgeRev w.1.val.1 < edgeRev w.1.val.2 then w.2 else !w.2)

private theorem edgeRev_lt_crossingRev_iff {a b : Fin n} (hab : a < b) :
    edgeRev (min (edgeRev a) (edgeRev b)) < edgeRev (max (edgeRev a) (edgeRev b)) ↔
      edgeRev a < edgeRev b := by
  have hne : edgeRev a ≠ edgeRev b :=
    (edgeRevEquiv n).injective.ne (ne_of_lt hab)
  by_cases h : edgeRev a < edgeRev b
  · rw [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h),
      edgeRev_edgeRev, edgeRev_edgeRev]
    exact ⟨fun _ => h, fun _ => hab⟩
  · have hgt : edgeRev b < edgeRev a := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    rw [min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt),
      edgeRev_edgeRev, edgeRev_edgeRev]
    exact ⟨fun hba => False.elim (lt_asymm hab hba), fun h' => False.elim (h h')⟩

def visitRevEquiv (q : Fin n → PlanarPoint ℝ) :
    CrossingVisit q ≃ CrossingVisit (reversePolygon q) where
  toFun := visitRevMap q
  invFun := visitRevInvMap q
  left_inv := by
    rintro ⟨c, b⟩
    apply Prod.ext
    · exact (crossingRevEquiv q).left_inv c
    · dsimp [visitRevMap, visitRevInvMap, crossingRevEquiv, crossingRevMap]
      simp only [edgeRev_lt_crossingRev_iff c.property.1]
      split_ifs <;> simp
  right_inv := by
    rintro ⟨d, b⟩
    apply Prod.ext
    · exact (crossingRevEquiv q).right_inv d
    · dsimp [visitRevMap, visitRevInvMap, crossingRevEquiv, crossingRevInvMap]
      simp only [edgeRev_lt_crossingRev_iff d.property.1]
      split_ifs <;> simp

@[simp] theorem visitRevEquiv_fst (q : Fin n → PlanarPoint ℝ) (v : CrossingVisit q) :
    (visitRevEquiv q v).1 = crossingRevEquiv q v.1 := rfl

theorem crossingVisitEdge_visitRevEquiv (q : Fin n → PlanarPoint ℝ)
    (v : CrossingVisit q) :
    crossingVisitEdge (reversePolygon q) (visitRevEquiv q v) =
      edgeRev (crossingVisitEdge q v) := by
  rcases v with ⟨c, b⟩
  dsimp [crossingVisitEdge, visitRevEquiv, visitRevMap, crossingRevEquiv, crossingRevMap]
  have hne : edgeRev c.val.1 ≠ edgeRev c.val.2 :=
    (edgeRevEquiv n).injective.ne (ne_of_lt c.property.1)
  by_cases h : edgeRev c.val.1 < edgeRev c.val.2
  · rw [if_pos h, min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)]
    cases b <;> rfl
  · have hgt : edgeRev c.val.2 < edgeRev c.val.1 :=
      lt_of_le_of_ne (le_of_not_gt h) hne.symm
    rw [if_neg h, min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt)]
    cases b <;> rfl

theorem crossingVisitPoint_visitRevEquiv (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (v : CrossingVisit q) :
    crossingVisitPoint (reversePolygon q) (visitRevEquiv q v) =
      crossingVisitPoint q v :=
  crossingPoint_crossingRevEquiv q hq v.1

theorem crossingVisitFlip_visitRevEquiv (q : Fin n → PlanarPoint ℝ)
    (v : CrossingVisit q) :
    visitRevEquiv q (crossingVisitFlip q v) =
      crossingVisitFlip (reversePolygon q) (visitRevEquiv q v) := by
  rcases v with ⟨c, b⟩
  apply Prod.ext
  · rfl
  · dsimp [visitRevEquiv, visitRevMap, crossingVisitFlip]
    split_ifs <;> cases b <;> rfl

theorem crossingVisitParameter_visitRevEquiv (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (v : CrossingVisit q) :
    crossingVisitParameter (reversePolygon q) (visitRevEquiv q v) =
      1 - crossingVisitParameter q v := by
  have hqr := cyclicGeneric_reversePolygon q hq
  let e := crossingVisitEdge q v
  have hspec_rev := (crossingVisitParameter_spec (reversePolygon q) (visitRevEquiv q v)).2.2
  have hspec := (crossingVisitParameter_spec q v).2.2
  rw [crossingVisitPoint_visitRevEquiv q hq v,
    crossingVisitEdge_visitRevEquiv q v] at hspec_rev
  have hrev_aff :
      affinePoint (q e) (q (cyclicSuccessor e)) (crossingVisitParameter q v) =
        affinePoint (reversePolygon q (edgeRev e))
          (reversePolygon q (cyclicSuccessor (edgeRev e)))
          (1 - crossingVisitParameter q v) := by
    rw [reversePolygon_edgeRev, cyclicSuccessor_edgeRev, reversePolygon_apply,
      Fin.rev_rev, affinePoint_reverse]
  have heq :
      affinePoint (reversePolygon q (edgeRev e))
        (reversePolygon q (cyclicSuccessor (edgeRev e)))
        (crossingVisitParameter (reversePolygon q) (visitRevEquiv q v)) =
      affinePoint (reversePolygon q (edgeRev e))
        (reversePolygon q (cyclicSuccessor (edgeRev e)))
        (1 - crossingVisitParameter q v) :=
    hspec_rev.symm.trans (hspec.trans hrev_aff)
  have hne :
      reversePolygon q (edgeRev e) ≠
        reversePolygon q (cyclicSuccessor (edgeRev e)) := by
    intro h
    exact cyclicTangent_ne_zero hqr.size_ge_three (reversePolygon q) hqr.g1 (edgeRev e)
      (sub_eq_zero.mpr h.symm)
  exact affinePoint_injective _ _ hne heq

def eventVertexRev (q : Fin n → PlanarPoint ℝ) :
    PolygonEvent q ≃ PolygonEvent (reversePolygon q) :=
  Equiv.sumCongr Fin.revPerm (visitRevEquiv q)

@[simp] theorem eventVertexRev_inl (q : Fin n → PlanarPoint ℝ) (e : Fin n) :
    eventVertexRev q (.inl e) = .inl e.rev := rfl

@[simp] theorem eventVertexRev_inr (q : Fin n → PlanarPoint ℝ) (v : CrossingVisit q) :
    eventVertexRev q (.inr v) = .inr (visitRevEquiv q v) := rfl

theorem polygonEventPoint_eventVertexRev (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (x : PolygonEvent q) :
    polygonEventPoint (reversePolygon q) (eventVertexRev q x) =
      polygonEventPoint q x := by
  cases x with
  | inl e => simp [polygonEventPoint, reversePolygon]
  | inr v => exact crossingVisitPoint_visitRevEquiv q hq v

end CrossingAndEventReversal

section SuccessorAndDartIntertwining

variable {n : ℕ}

theorem polygonEventSuccessor_eq_of_sameEdge_next_or_nextAnchor
    (q : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (a b : PolygonEvent q)
    (hb :
      (polygonEventEdge q b = polygonEventEdge q a ∧
        polygonEventParameter q a < polygonEventParameter q b ∧
        ∀ z : PolygonEvent q, polygonEventEdge q z = polygonEventEdge q a →
          polygonEventParameter q a < polygonEventParameter q z →
          polygonEventParameter q b ≤ polygonEventParameter q z) ∨
      (b = Sum.inl (cyclicSuccessor (polygonEventEdge q a)) ∧
        ∀ z : PolygonEvent q, polygonEventEdge q z = polygonEventEdge q a →
          polygonEventParameter q z ≤ polygonEventParameter q a)) :
    polygonEventSuccessor q hG2 a = b := by
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hG2
  have hs := EventSegmentGeometry.polygonEventSuccessor_sameEdge_next_or_nextAnchor q hG2 hn a
  dsimp at hs
  let y := polygonEventSuccessor q hG2 a
  rcases hs with ⟨hey, hay, hminy⟩ | ⟨hy, hmaxa⟩
  · rcases hb with ⟨heb, hab, hminb⟩ | ⟨_, hmaxa'⟩
    · apply polygonEventKey_injective q hG2
      apply Prod.ext
      · exact hey.trans heb.symm
      · have hyb : polygonEventParameter q y ≤ polygonEventParameter q b := by
          have h := hminy b heb hab
          exact le_of_not_gt
            ((polygonEvent_sameEdge_lt_iff q hG2 b y (heb.trans hey.symm)).not.mp
              (not_lt_of_ge h))
        have hby : polygonEventParameter q b ≤ polygonEventParameter q y :=
          hminb y hey hay
        exact le_antisymm hyb hby
    · exact False.elim ((not_lt_of_ge (hmaxa' y hey)) hay)
  · rcases hb with ⟨heb, hab, _⟩ | ⟨hb', _⟩
    · exact False.elim ((not_lt_of_ge (hmaxa b heb)) hab)
    · exact hy.trans hb'.symm

theorem polygonEventSuccessor_reversePolygon_intertwine
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (x : PolygonEvent q) :
    polygonEventSuccessor (reversePolygon q) (cyclicGeneric_reversePolygon q hq).g2
      (eventVertexRev q (polygonEventSuccessor q hq.g2 x)) =
      eventVertexRev q x := by
  let hqr := cyclicGeneric_reversePolygon q hq
  let e := polygonEventEdge q x
  let y := polygonEventSuccessor q hq.g2 x
  let y' := eventVertexRev q y
  let x' := eventVertexRev q x
  apply polygonEventSuccessor_eq_of_sameEdge_next_or_nextAnchor
    (reversePolygon q) hqr.g2 hqr.size_ge_three y' x'
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  have hs := EventSegmentGeometry.polygonEventSuccessor_sameEdge_next_or_nextAnchor
    q hq.g2 hq.size_ge_three x
  dsimp at hs
  let u : ℝ := if polygonEventEdge q y = e then polygonEventParameter q y else 1
  have hy'_props :
      polygonEventEdge (reversePolygon q) y' = edgeRev e ∧
      polygonEventParameter (reversePolygon q) y' = 1 - u ∧
      polygonEventParameter q x < u ∧
      (∀ z : PolygonEvent q, polygonEventEdge q z = e →
        polygonEventParameter q x < polygonEventParameter q z →
        u ≤ polygonEventParameter q z) := by
    rcases hs with ⟨hey, hxy, hmin⟩ | ⟨hy_anc, hmax⟩
    · have hey' : polygonEventEdge q y = e := hey
      have hu : u = polygonEventParameter q y := if_pos hey'
      cases hy_cases : y with
      | inl ey =>
          have h0 : polygonEventParameter q y = 0 := by simp [hy_cases, polygonEventParameter]
          have hbounds := (polygonEventParameter_bounds q x).1
          linarith
      | inr wy =>
          have hwy_edge : crossingVisitEdge q wy = e := by
            rw [hy_cases] at hey'
            exact hey'
          have hy'_eq : y' = .inr (visitRevEquiv q wy) := by
            simp [y', hy_cases]
          refine ⟨?_, ?_, by linarith, ?_⟩
          · rw [hy'_eq, polygonEventEdge, crossingVisitEdge_visitRevEquiv, hwy_edge]
          · rw [hy'_eq, polygonEventParameter, crossingVisitParameter_visitRevEquiv q hq wy,
              hu, hy_cases, polygonEventParameter]
          · intro z hze hxz
            rw [hu]
            have hle := hmin z hze hxz
            exact le_of_not_gt
              ((polygonEvent_sameEdge_lt_iff q hq.g2 z y (hze.trans hey'.symm)).not.mp
                (not_lt_of_ge hle))
    · have hy_anc' : y = Sum.inl (cyclicSuccessor e) := hy_anc
      have hne : polygonEventEdge q y ≠ e := by
        rw [hy_anc', polygonEventEdge]
        exact cyclicSuccessor_ne_self (by have := hq.size_ge_three; omega) e
      have hu : u = 1 := if_neg hne
      have hy'_eq : y' = .inl (edgeRev e) := by
        change eventVertexRev q y = .inl (edgeRev e)
        rw [hy_anc', eventVertexRev_inl]
        rfl
      refine ⟨by simp [hy'_eq, polygonEventEdge], ?_, ?_, ?_⟩
      · rw [hy'_eq, hu, polygonEventParameter, sub_self]
      · rw [hu]
        exact (polygonEventParameter_bounds q x).2
      · intro z hze hxz
        exact False.elim ((not_lt_of_ge (hmax z hze)) hxz)
  rcases hy'_props with ⟨hy'_edge, hy'_param, hxu, hgap⟩
  cases hx_cases : x with
  | inr wx =>
      left
      have hwx_edge : crossingVisitEdge q wx = e := by
        simp [e, hx_cases, polygonEventEdge]
      have hx'_edge : polygonEventEdge (reversePolygon q) x' = edgeRev e := by
        simp [x', hx_cases, polygonEventEdge, crossingVisitEdge_visitRevEquiv, hwx_edge]
      have hx'_param :
          polygonEventParameter (reversePolygon q) x' = 1 - polygonEventParameter q x := by
        simp [x', hx_cases, polygonEventParameter, crossingVisitParameter_visitRevEquiv q hq wx]
      refine ⟨hx'_edge.trans hy'_edge.symm, by linarith, ?_⟩
      intro z' hz'_edge hz'_lt
      rw [hy'_edge] at hz'_edge
      rw [hy'_param] at hz'_lt
      rw [hx'_param]
      cases z' with
      | inl ez' =>
          have h0 : polygonEventParameter (reversePolygon q) (.inl ez') = 0 := rfl
          rw [h0] at hz'_lt
          have hu_le : u ≤ 1 := by
            dsimp [u]
            split_ifs
            · exact le_of_lt (polygonEventParameter_bounds q y).2
            · exact le_refl 1
          linarith
      | inr wz' =>
          obtain ⟨wz, rfl⟩ := (visitRevEquiv q).surjective wz'
          have hwz_edge : polygonEventEdge q (.inr wz) = e := by
            apply (edgeRevEquiv n).injective
            simpa [polygonEventEdge, crossingVisitEdge_visitRevEquiv] using hz'_edge
          have hwz_param :
              polygonEventParameter (reversePolygon q) (.inr (visitRevEquiv q wz)) =
                1 - polygonEventParameter q (.inr wz) :=
            crossingVisitParameter_visitRevEquiv q hq wz
          rw [hwz_param] at hz'_lt ⊢
          have hlt_u : polygonEventParameter q (.inr wz) < u := by linarith
          have hle_x : polygonEventParameter q (.inr wz) ≤ polygonEventParameter q x :=
            Classical.byContradiction fun hgt =>
              (not_lt_of_ge (hgap (.inr wz) hwz_edge (lt_of_not_ge hgt))) hlt_u
          linarith
  | inl ex =>
      right
      have hex : ex = e := by simp [e, hx_cases, polygonEventEdge]
      have hx_param : polygonEventParameter q x = 0 := by
        simp [hx_cases, polygonEventParameter]
      refine ⟨?_, ?_⟩
      · simp [x', hx_cases, hex, hy'_edge, cyclicSuccessor_edgeRev]
      · intro z' hz'_edge
        rw [hy'_edge] at hz'_edge
        rw [hy'_param]
        cases z' with
        | inl ez' =>
            have h0 : polygonEventParameter (reversePolygon q) (.inl ez') = 0 := rfl
            rw [h0]
            have hu_le : u ≤ 1 := by
              dsimp [u]
              split_ifs
              · exact le_of_lt (polygonEventParameter_bounds q y).2
              · exact le_refl 1
            linarith
        | inr wz' =>
            obtain ⟨wz, rfl⟩ := (visitRevEquiv q).surjective wz'
            have hwz_edge : polygonEventEdge q (.inr wz) = e := by
              apply (edgeRevEquiv n).injective
              simpa [polygonEventEdge, crossingVisitEdge_visitRevEquiv] using hz'_edge
            have hwz_param :
                polygonEventParameter (reversePolygon q) (.inr (visitRevEquiv q wz)) =
                  1 - polygonEventParameter q (.inr wz) :=
              crossingVisitParameter_visitRevEquiv q hq wz
            rw [hwz_param]
            have hwz_pos : polygonEventParameter q x < polygonEventParameter q (.inr wz) := by
              rw [hx_param]
              exact (crossingVisitParameter_spec q wz).1
            have hu_le := hgap (.inr wz) hwz_edge hwz_pos
            linarith

def revSupport (q : Fin n → PlanarPoint ℝ) (S : Finset (PolygonCrossing q)) :
    Finset (PolygonCrossing (reversePolygon q)) :=
  S.map (crossingRevEquiv q).toEmbedding

@[simp] theorem mem_revSupport_iff (q : Fin n → PlanarPoint ℝ)
    (S : Finset (PolygonCrossing q)) (c : PolygonCrossing q) :
    crossingRevEquiv q c ∈ revSupport q S ↔ c ∈ S := by
  simp [revSupport]

@[simp] theorem revSupport_card (q : Fin n → PlanarPoint ℝ)
    (S : Finset (PolygonCrossing q)) :
    (revSupport q S).card = S.card :=
  Finset.card_map _

def supportEquiv (q : Fin n → PlanarPoint ℝ) :
    Finset (PolygonCrossing q) ≃ Finset (PolygonCrossing (reversePolygon q)) where
  toFun := revSupport q
  invFun S' := S'.map (crossingRevEquiv q).symm.toEmbedding
  left_inv S := by
    ext c
    simp [revSupport]
  right_inv S' := by
    ext d
    simp [revSupport]

theorem smoothingPairing_eventVertexRev (q : Fin n → PlanarPoint ℝ)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingPairing (reversePolygon q) (revSupport q S) (eventVertexRev q x) =
      eventVertexRev q (smoothingPairing q S x) := by
  classical
  cases x with
  | inl e => rfl
  | inr v =>
      by_cases hv : v.1 ∈ S
      · have hv_rev : (visitRevEquiv q v).1 ∈ revSupport q S :=
          (mem_revSupport_iff q S v.1).mpr hv
        simp only [eventVertexRev_inr, smoothingPairing_apply, smoothingPairingMap_visit,
          if_pos hv, if_pos hv_rev, crossingVisitFlip_visitRevEquiv]
      · have hv_rev : (visitRevEquiv q v).1 ∉ revSupport q S :=
          (mem_revSupport_iff q S v.1).not.mpr hv
        simp only [eventVertexRev_inr, smoothingPairing_apply, smoothingPairingMap_visit,
          if_neg hv, if_neg hv_rev]

def dartRevEquiv (q : Fin n → PlanarPoint ℝ) (S : Finset (PolygonCrossing q)) :
    PolygonEvent q ≃ PolygonEvent (reversePolygon q) :=
  (smoothingPairing q S).trans (eventVertexRev q)

theorem dartRevEquiv_apply (q : Fin n → PlanarPoint ℝ)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    dartRevEquiv q S x = eventVertexRev q (smoothingPairing q S x) := rfl

theorem dartRevEquiv_point (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    polygonEventPoint (reversePolygon q) (dartRevEquiv q S x) =
      polygonEventPoint q x := by
  rw [dartRevEquiv_apply, polygonEventPoint_eventVertexRev q hq,
    smoothingPairing_point]

theorem retainedCorner_eventVertexRev_iff (q : Fin n → PlanarPoint ℝ)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    retainedCorner (reversePolygon q) (revSupport q S) (eventVertexRev q x) ↔
      retainedCorner q S x := by
  cases x with
  | inl e => simp [retainedCorner]
  | inr v => simp [retainedCorner]

theorem retainedCorner_dartRevEquiv_iff (q : Fin n → PlanarPoint ℝ)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    retainedCorner (reversePolygon q) (revSupport q S) (dartRevEquiv q S x) ↔
      retainedCorner q S x := by
  rw [dartRevEquiv_apply, retainedCorner_eventVertexRev_iff,
    pairing_preserves_retained]

theorem smoothingDartPermutation_reversePolygon_intertwine
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingDartPermutation (reversePolygon q) (cyclicGeneric_reversePolygon q hq).g2
      (revSupport q S)
      (dartRevEquiv q S (smoothingDartPermutation q hq.g2 S x)) =
      dartRevEquiv q S x := by
  have hpair :
      smoothingPairing q S (smoothingDartPermutation q hq.g2 S x) =
        polygonEventSuccessor q hq.g2 x :=
    smoothingPairingMap_involutive q S (polygonEventSuccessor q hq.g2 x)
  rw [dartRevEquiv_apply, hpair, smoothingDartPermutation_apply,
    polygonEventSuccessor_reversePolygon_intertwine q hq x,
    smoothingPairing_eventVertexRev, ← dartRevEquiv_apply]

theorem polygonNonalternating_reversePolygon_iff
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) :
    PolygonNonalternation.polygonNonalternating (reversePolygon q)
      (cyclicGeneric_reversePolygon q hq).g2 (revSupport q S) ↔
      PolygonNonalternation.polygonNonalternating q hq.g2 S := by
  let hqr := cyclicGeneric_reversePolygon q hq
  rw [PolygonNonalternation.polygonNonalternating_iff_dart_count
      (reversePolygon q) hqr.g2 hqr.size_ge_three (revSupport q S),
    PolygonNonalternation.polygonNonalternating_iff_dart_count
      q hq.g2 hq.size_ge_three S,
    revSupport_card]
  have hcomp := componentCount_eq_of_reverse_intertwining
    (dartRevEquiv q S)
    (smoothingDartPermutation q hq.g2 S)
    (smoothingDartPermutation (reversePolygon q) hqr.g2 (revSupport q S))
    (smoothingDartPermutation_reversePolygon_intertwine q hq S)
  rw [hcomp]

end SuccessorAndDartIntertwining

section DaughterAndPrimitiveReversal

variable {n : ℕ}

theorem ofFn_reversePolygon {m : ℕ} (f : Fin m → PlanarPoint ℝ) :
    List.ofFn (reversePolygon f) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn, reversePolygon]
    congr 1
    apply Fin.ext
    dsimp [Fin.rev]
    omega

theorem daughterPointList_reversePolygon_isRotated
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q) :
    List.ofFn (reversePolygon (daughterVertex q hq.g2 S root)) ~r
      List.ofFn (daughterVertex (reversePolygon q)
        (cyclicGeneric_reversePolygon q hq).g2 (revSupport q S)
        (dartRevEquiv q S root)) := by
  classical
  let hqr := cyclicGeneric_reversePolygon q hq
  let ψ := dartRevEquiv q S
  let p := smoothingDartPermutation q hq.g2 S
  let p_rev := smoothingDartPermutation (reversePolygon q) hqr.g2 (revSupport q S)
  change List.ofFn (reversePolygon (daughterVertex q hq.g2 S root)) ~r
    daughterPointList (reversePolygon q) hqr.g2 (revSupport q S) (ψ root)
  rw [ofFn_reversePolygon]
  change (daughterPointList q hq.g2 S root).reverse ~r
    daughterPointList (reversePolygon q) hqr.g2 (revSupport q S) (ψ root)
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map]
  have horb := orbitWord_reverse_map_isRotated ψ p p_rev
    (smoothingDartPermutation_reversePolygon_intertwine q hq S) root
  have hfilt := (DaughterRootRotation.listIsRotated_filter horb
    (fun y => decide (retainedCorner (reversePolygon q) (revSupport q S) y))).map
    (polygonEventPoint (reversePolygon q))
  have hlhs :
      ((((orbitWord p root).reverse).map ψ).filter
        (fun y => decide (retainedCorner (reversePolygon q) (revSupport q S) y))).map
          (polygonEventPoint (reversePolygon q)) =
      (((orbitWord p root).filter
        (fun x => decide (retainedCorner q S x))).map (polygonEventPoint q)).reverse := by
    rw [← DaughterPointListFilter.map_filter_comp, List.map_map]
    have hpred :
        (fun a => decide (retainedCorner (reversePolygon q) (revSupport q S) (ψ a))) =
          (fun a => decide (retainedCorner q S a)) := by
      funext a
      simp [ψ, retainedCorner_dartRevEquiv_iff]
    have hpt :
        (polygonEventPoint (reversePolygon q) ∘ ψ) = polygonEventPoint q := by
      funext a
      exact dartRevEquiv_point q hq S a
    rw [hpred, hpt, List.filter_reverse, List.map_reverse]
  rwa [hlhs] at hfilt

theorem auxiliaryGenericity_reversePolygon
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) :
    auxiliaryGenericity (reversePolygon q) (cyclicGeneric_reversePolygon q hq) := by
  let hqr := cyclicGeneric_reversePolygon q hq
  intro S_rev hS_rev root_rev
  let S := (supportEquiv q).symm S_rev
  have hS_eq : revSupport q S = S_rev := (supportEquiv q).right_inv S_rev
  rw [← hS_eq] at hS_rev ⊢
  have hS : PolygonNonalternation.polygonNonalternating q hq.g2 S :=
    (polygonNonalternating_reversePolygon_iff q hq S).mp hS_rev
  let root := (dartRevEquiv q S).symm root_rev
  have hroot_eq : dartRevEquiv q S root = root_rev :=
    (dartRevEquiv q S).right_inv root_rev
  rw [← hroot_eq]
  have hcg_orig : CyclicGeneric (daughterVertex q hq.g2 S root) :=
    hAux S hS root
  have hcg_rev : CyclicGeneric (reversePolygon (daughterVertex q hq.g2 S root)) :=
    cyclicGeneric_reversePolygon _ hcg_orig
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated
    (daughterPointList_reversePolygon_isRotated q hq S root) hcg_rev

theorem auxiliaryGenericity_reversal_thm :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      auxiliaryGenericity q hq →
        ∃ hqr : CyclicGeneric (reversePolygon q),
          auxiliaryGenericity (reversePolygon q) hqr := by
  intro n q hq hAux
  exact ⟨cyclicGeneric_reversePolygon q hq, auxiliaryGenericity_reversePolygon q hq hAux⟩

def dartComponentEquiv (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) :
    Component (smoothingDartPermutation q hq.g2 S) ≃
      Component (smoothingDartPermutation (reversePolygon q)
        (cyclicGeneric_reversePolygon q hq).g2 (revSupport q S)) :=
  componentEquivOfReverseIntertwining
    (dartRevEquiv q S)
    (smoothingDartPermutation q hq.g2 S)
    (smoothingDartPermutation (reversePolygon q)
      (cyclicGeneric_reversePolygon q hq).g2 (revSupport q S))
    (smoothingDartPermutation_reversePolygon_intertwine q hq S)

theorem componentAmplitude_reversePolygon (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (hAux : auxiliaryGenericity q hq)
    (hAux_rev : auxiliaryGenericity (reversePolygon q) (cyclicGeneric_reversePolygon q hq))
    (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    componentAmplitude (reversePolygon q) (cyclicGeneric_reversePolygon q hq)
      (revSupport q S) hAux_rev
      ((polygonNonalternating_reversePolygon_iff q hq S).mpr hS)
      (dartComponentEquiv q hq S c) =
      (-1 : ℚ) ^ Fintype.card (CornerCoord q hq.g2 S (componentRoot q hq S c)) *
        componentAmplitude q hq S hAux hS c := by
  let hqr := cyclicGeneric_reversePolygon q hq
  let hS_rev := (polygonNonalternating_reversePolygon_iff q hq S).mpr hS
  let c_rev := dartComponentEquiv q hq S c
  let r := componentRoot q hq S c
  let r_rev := componentRoot (reversePolygon q) hqr (revSupport q S) c_rev
  have hsame :
      (smoothingDartPermutation (reversePolygon q) hqr.g2 (revSupport q S)).SameCycle
        (dartRevEquiv q S r) r_rev := by
    apply (componentOf_eq_iff _ _ _).mp
    have h1 :
        componentOf (smoothingDartPermutation (reversePolygon q) hqr.g2 (revSupport q S))
          (dartRevEquiv q S r) = c_rev := by
      change dartComponentEquiv q hq S
        (componentOf (smoothingDartPermutation q hq.g2 S) r) = c_rev
      rw [componentRoot_sameComponent]
    exact h1.trans (componentRoot_sameComponent (reversePolygon q) hqr (revSupport q S) c_rev).symm
  have hrot1 := daughterPointList_reversePolygon_isRotated q hq S r
  have hrot2 := DaughterRootRotation.daughterPointList_isRotated_of_sameCycle
    (reversePolygon q) hqr.g2 (revSupport q S) (dartRevEquiv q S r) r_rev hsame
  have hrot :
      List.ofFn (reversePolygon (componentPolygon q hq S c)) ~r
        List.ofFn (componentPolygon (reversePolygon q) hqr (revSupport q S) c_rev) :=
    hrot1.trans hrot2
  have hcg_orig := hAux S hS r
  have hcg_rev := cyclicGeneric_reversePolygon (componentPolygon q hq S c) hcg_orig
  have hamp_rot := DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated
    hRI hcg_rev hrot
  have hamp_rev := polygonAmplitude_reversePolygon hRI (componentPolygon q hq S c) hcg_orig
  unfold componentAmplitude
  exact hamp_rot.symm.trans hamp_rev

theorem componentAmplitudeProduct_reversePolygon (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (hAux : auxiliaryGenericity q hq)
    (hAux_rev : auxiliaryGenericity (reversePolygon q) (cyclicGeneric_reversePolygon q hq))
    (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S) :
    componentAmplitudeProduct (reversePolygon q) (cyclicGeneric_reversePolygon q hq)
      (revSupport q S) hAux_rev
      ((polygonNonalternating_reversePolygon_iff q hq S).mpr hS) =
      (-1 : ℚ) ^ n * componentAmplitudeProduct q hq S hAux hS := by
  unfold componentAmplitudeProduct
  rw [← Equiv.prod_comp (dartComponentEquiv q hq S)]
  simp only [componentAmplitude_reversePolygon hRI q hq S hAux hAux_rev hS,
    Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  change (-1 : ℚ) ^ smoothingVertexCount q hq S = (-1 : ℚ) ^ n
  rw [smoothingVertexCount_eq q hq S, pow_add, pow_mul]
  norm_num

def separatingSupportEquiv (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    SeparatingSupport q hq ≃
      SeparatingSupport (reversePolygon q) (cyclicGeneric_reversePolygon q hq) where
  toFun S := ⟨revSupport q S.1,
    (polygonNonalternating_reversePolygon_iff q hq S.1).mpr S.2⟩
  invFun S' := ⟨(supportEquiv q).symm S'.1, by
    have h := S'.2
    rw [← (supportEquiv q).right_inv S'.1] at h
    exact (polygonNonalternating_reversePolygon_iff q hq _).mp h⟩
  left_inv S := Subtype.ext ((supportEquiv q).left_inv S.1)
  right_inv S' := Subtype.ext ((supportEquiv q).right_inv S'.1)

theorem separatingSmoothingSum_reversePolygon (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq)
    (hAux_rev : auxiliaryGenericity (reversePolygon q) (cyclicGeneric_reversePolygon q hq)) :
    separatingSmoothingSum (reversePolygon q) (cyclicGeneric_reversePolygon q hq) hAux_rev =
      (-1 : ℚ) ^ n * separatingSmoothingSum q hq hAux := by
  classical
  unfold separatingSmoothingSum
  rw [← Equiv.sum_comp (separatingSupportEquiv q hq), Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  dsimp [separatingSupportEquiv]
  rw [revSupport_card, componentAmplitudeProduct_reversePolygon hRI q hq S.1 hAux hAux_rev S.2]
  ring

theorem normalizedPrimitive_reversePolygon (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq)
    (hAux_rev : auxiliaryGenericity (reversePolygon q) (cyclicGeneric_reversePolygon q hq)) :
    normalizedPrimitive (reversePolygon q) (cyclicGeneric_reversePolygon q hq) hAux_rev =
      normalizedPrimitive q hq hAux := by
  unfold normalizedPrimitive
  rw [separatingSmoothingSum_reversePolygon hRI q hq hAux hAux_rev,
    leftCount_reversePolygon q hq, ← mul_assoc]
  congr 1
  have hle : leftCount q ≤ n := by
    classical
    unfold leftCount
    exact le_trans (Finset.card_le_univ _) (by simp)
  have hexp : n - leftCount q + n = leftCount q + 2 * (n - leftCount q) := by omega
  rw [← pow_add, hexp, pow_add, pow_mul]
  norm_num

set_option linter.unusedVariables false in
theorem primitive_reversal_thm :
    ∀ (hRI : GLSSWRootIndependence) {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq),
      ∃ (hqr : CyclicGeneric (reversePolygon q))
        (hAuxr : auxiliaryGenericity (reversePolygon q) hqr),
        normalizedPrimitive (reversePolygon q) hqr hAuxr =
          normalizedPrimitive q hq hAux := by
  intro hRI n q hq hAux
  exact ⟨cyclicGeneric_reversePolygon q hq,
    auxiliaryGenericity_reversePolygon q hq hAux,
    normalizedPrimitive_reversePolygon hRI q hq hAux
      (auxiliaryGenericity_reversePolygon q hq hAux)⟩

end DaughterAndPrimitiveReversal

end DirectGLSSW
