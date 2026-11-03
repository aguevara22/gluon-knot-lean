import HOMFLYDescendingSelfSmoothing
import HOMFLYFullSkeinStage
import HOMFLYTraversalDifference
import HOMFLYAllBasepointIndependence
import Gemini.PermutationAdjacentSwaps

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.Gemini

open DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients
open Equiv PermutationOrbits

noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  PermutationOrbits.componentFintype D.continuation

/-! ### Part 1: Injectivity of Multiplication by `unlinkFactor` -/

private theorem aMonomial_sq_mul_of_unlinkFactor_mul_eq_zero {R : HOMFLYCoeff}
    (h : unlinkFactor * R = 0) :
    aMonomial * (aMonomial * R) = R := by
  have hz : (aMonomial - aInvMonomial) * R = 0 := by
    calc
      (aMonomial - aInvMonomial) * R =
          (aMonomial - aInvMonomial) * (zInvMonomial * zMonomial) * R := by
        rw [mul_comm zInvMonomial zMonomial, zMonomial_mul_zInvMonomial, mul_one]
      _ = zMonomial * (((aMonomial - aInvMonomial) * zInvMonomial) * R) := by ring
      _ = zMonomial * (unlinkFactor * R) := rfl
      _ = 0 := by rw [h, mul_zero]
  have ha : aMonomial * ((aMonomial - aInvMonomial) * R) = 0 := by
    rw [hz, mul_zero]
  calc
    aMonomial * (aMonomial * R) =
        aMonomial * ((aMonomial - aInvMonomial) * R) +
          (aMonomial * aInvMonomial) * R := by ring
    _ = 0 + 1 * R := by rw [ha, aMonomial_mul_aInvMonomial]
    _ = R := by ring

private theorem coeff_shift_of_unlinkFactor_mul_eq_zero {R : HOMFLYCoeff}
    (h : unlinkFactor * R = 0) (i j : ℤ) :
    ∀ k : ℕ, coeff R i j = coeff R (i - 2 * (k : ℤ)) j
  | 0 => by simp
  | k + 1 => by
      have ih := coeff_shift_of_unlinkFactor_mul_eq_zero h i j k
      have hsq := aMonomial_sq_mul_of_unlinkFactor_mul_eq_zero h
      have hstep : coeff R (i - 2 * (k : ℤ)) j =
          coeff R (i - 2 * (k : ℤ) - 2) j := by
        calc
          coeff R (i - 2 * (k : ℤ)) j =
              coeff (aMonomial * (aMonomial * R)) (i - 2 * (k : ℤ)) j := by
            rw [hsq]
          _ = coeff R (i - 2 * (k : ℤ) - 1 - 1) j := by
            rw [coeff_aMonomial_mul, coeff_aMonomial_mul]
          _ = coeff R (i - 2 * (k : ℤ) - 2) j := by
            congr 1
            omega
      rw [ih, hstep]
      congr 1
      push_cast
      omega

theorem eq_zero_of_unlinkFactor_mul_eq_zero {R : HOMFLYCoeff}
    (h : unlinkFactor * R = 0) : R = 0 := by
  ext ⟨i, j⟩
  change coeff R i j = 0
  by_contra hne
  let S : Finset ℤ := R.support.image Prod.fst
  have hmem : ∀ k : ℕ, i - 2 * (k : ℤ) ∈ S := by
    intro k
    refine Finset.mem_image.mpr ⟨(i - 2 * (k : ℤ), j), ?_, rfl⟩
    rw [Finsupp.mem_support_iff]
    change coeff R (i - 2 * (k : ℤ)) j ≠ 0
    rw [← coeff_shift_of_unlinkFactor_mul_eq_zero h i j k]
    exact hne
  have hS : S.Nonempty := ⟨i - 2 * (0 : ℤ), hmem 0⟩
  let m := S.min' hS
  let k : ℕ := (i - m).toNat + 1
  have hk_mem : i - 2 * (k : ℤ) ∈ S := hmem k
  have hle : m ≤ i - 2 * (k : ℤ) := Finset.min'_le S _ hk_mem
  omega

theorem unlinkFactor_mul_injective {P Q : HOMFLYCoeff}
    (h : unlinkFactor * P = unlinkFactor * Q) : P = Q := by
  have hsub : unlinkFactor * (P - Q) = 0 := by
    rw [mul_sub, h, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_unlinkFactor_mul_eq_zero hsub)

theorem descendingUnlinkValue_smooth_self (D : PLLinkDiagram)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    descendingUnlinkValue (smoothCrossing D c) =
      unlinkFactor * descendingUnlinkValue D := by
  have hD : 0 < diagramComponentCount D := by
    unfold diagramComponentCount
    exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ (D.incoming c 0)⟩
  have hSmoothCount := smooth_componentCount_self D c hself
  have hsmooth : 0 < diagramComponentCount (smoothCrossing D c) := by omega
  rw [descendingUnlinkValue_of_nonempty_components (smoothCrossing D c) hsmooth,
      descendingUnlinkValue_of_nonempty_components D hD, hSmoothCount]
  have hSmoothExponent : diagramComponentCount D + 1 - 1 = (diagramComponentCount D - 1) + 1 := by
    omega
  rw [hSmoothExponent, pow_succ']

/-! ### Part 2: Finite Type Sorting by Weight -/

private def weightLt {α : Type*} [Fintype α]
    (e₀ : α ≃ Fin (Fintype.card α)) (w : α → ℕ) (a b : α) : Prop :=
  w a < w b ∨ (w a = w b ∧ (e₀ a).val < (e₀ b).val)

private theorem weightLt_irrefl {α : Type*} [Fintype α]
    (e₀ : α ≃ Fin (Fintype.card α)) (w : α → ℕ) (a : α) :
    ¬ weightLt e₀ w a a := by
  unfold weightLt
  omega

private theorem weightLt_trans {α : Type*} [Fintype α]
    (e₀ : α ≃ Fin (Fintype.card α)) (w : α → ℕ) {a b c : α}
    (hab : weightLt e₀ w a b) (hbc : weightLt e₀ w b c) :
    weightLt e₀ w a c := by
  unfold weightLt at *
  omega

private theorem weightLt_total {α : Type*} [Fintype α]
    (e₀ : α ≃ Fin (Fintype.card α)) (w : α → ℕ) {a b : α} (hne : a ≠ b) :
    weightLt e₀ w a b ∨ weightLt e₀ w b a := by
  have he : (e₀ a).val ≠ (e₀ b).val := by
    intro h
    exact hne (e₀.injective (Fin.ext h))
  unfold weightLt
  omega

private noncomputable def weightRankFin {α : Type*} [Fintype α]
    (e₀ : α ≃ Fin (Fintype.card α)) (w : α → ℕ) (a : α) :
    Fin (Fintype.card α) :=
  ⟨(Finset.univ.filter (fun b : α => weightLt e₀ w b a)).card, by
    have hnot : a ∉ Finset.univ.filter (fun b : α => weightLt e₀ w b a) := by
      simp [weightLt_irrefl]
    have hssub : Finset.univ.filter (fun b : α => weightLt e₀ w b a) ⊂ Finset.univ :=
      Finset.ssubset_univ_iff.mpr (by
        intro h
        rw [h] at hnot
        exact hnot (Finset.mem_univ a))
    simpa using Finset.card_lt_card hssub⟩

private theorem weightRankFin_strictMono {α : Type*} [Fintype α]
    (e₀ : α ≃ Fin (Fintype.card α)) (w : α → ℕ) {a b : α}
    (hab : weightLt e₀ w a b) :
    weightRankFin e₀ w a < weightRankFin e₀ w b := by
  change (Finset.univ.filter (fun x : α => weightLt e₀ w x a)).card <
    (Finset.univ.filter (fun x : α => weightLt e₀ w x b)).card
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact weightLt_trans e₀ w hx hab
  · intro hEq
    have ha_in : a ∈ Finset.univ.filter (fun x : α => weightLt e₀ w x b) := by
      simp [hab]
    rw [← hEq] at ha_in
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha_in
    exact weightLt_irrefl e₀ w a ha_in

noncomputable def equivFinOfWeight {α : Type*} [Fintype α] (w : α → ℕ) :
    α ≃ Fin (Fintype.card α) := by
  let e₀ := Fintype.equivFin α
  refine Equiv.ofBijective (weightRankFin e₀ w) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro a b hEq
  by_contra hne
  rcases weightLt_total e₀ w hne with hab | hba
  · exact (ne_of_lt (weightRankFin_strictMono e₀ w hab)) hEq
  · exact (ne_of_gt (weightRankFin_strictMono e₀ w hba)) hEq

theorem equivFinOfWeight_lt_of_lt {α : Type*} [Fintype α] (w : α → ℕ)
    {a b : α} (h : w a < w b) :
    equivFinOfWeight w a < equivFinOfWeight w b := by
  let e₀ := Fintype.equivFin α
  exact weightRankFin_strictMono e₀ w (Or.inl h)

/-! ### Part 3: Orbit Powers and Visit Positions Under Disjoint Smoothing -/

theorem smooth_step_of_ne (G : PLLinkDiagram) (x : Fin G.nCrossing)
    (a : Fin G.nArc) (ha : ∀ j : Fin 2, a ≠ G.incoming x j) :
    (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a)) =
      smoothArcEquiv G (Sum.inl (G.continuation a)) := by
  rw [← smoothCode_actual_step G x (Sum.inl a),
    smoothContinuationGeometryCode_other_arc G x a ha]

theorem smooth_pow_eq_of_disjoint (G : PLLinkDiagram) (x : Fin G.nCrossing)
    (root : Fin G.nArc) (m : ℕ)
    (hdisj : ∀ t < m, ∀ j : Fin 2, (G.continuation ^ t) root ≠ G.incoming x j) :
    ∀ t ≤ m,
      ((smoothCrossing G x).continuation ^ t) (smoothArcEquiv G (Sum.inl root)) =
        smoothArcEquiv G (Sum.inl ((G.continuation ^ t) root))
  | 0, _ => rfl
  | t + 1, ht => by
      have ih := smooth_pow_eq_of_disjoint G x root m hdisj t (by omega)
      rw [pow_succ', Perm.mul_apply, ih,
        smooth_step_of_ne G x ((G.continuation ^ t) root) (hdisj t (by omega)),
        pow_succ', Perm.mul_apply]

theorem smooth_sameCycle_unaffected_iff (G : PLLinkDiagram) (x : Fin G.nCrossing)
    (root : Fin G.nArc)
    (hdisj : ∀ t : ℕ, ∀ j : Fin 2, (G.continuation ^ t) root ≠ G.incoming x j)
    (z : Fin (smoothCrossing G x).nArc) :
    componentOf (smoothCrossing G x).continuation z =
        componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl root)) ↔
      ∃ b : Fin G.nArc,
        componentOf G.continuation b = componentOf G.continuation root ∧
          z = smoothArcEquiv G (Sum.inl b) := by
  constructor
  · intro hz
    have hsc : (smoothCrossing G x).continuation.SameCycle
        (smoothArcEquiv G (Sum.inl root)) z :=
      (componentOf_eq_iff _ _ _).mp hz.symm
    obtain ⟨t, ht⟩ := hsc.exists_nat_pow_eq
    have hpow := smooth_pow_eq_of_disjoint G x root t (fun s _ j => hdisj s j) t (le_refl t)
    refine ⟨(G.continuation ^ t) root, componentOf_pow_apply G.continuation t root, ?_⟩
    exact ht.symm.trans hpow
  · rintro ⟨b, hb, rfl⟩
    have hsc : G.continuation.SameCycle root b :=
      (componentOf_eq_iff _ _ _).mp hb.symm
    obtain ⟨t, ht⟩ := hsc.exists_nat_pow_eq
    have hpow := smooth_pow_eq_of_disjoint G x root t (fun s _ j => hdisj s j) t (le_refl t)
    rw [ht] at hpow
    rw [← hpow]
    exact componentOf_pow_apply (smoothCrossing G x).continuation t
      (smoothArcEquiv G (Sum.inl root))

theorem orbitPosition_eq_of_pow {α : Type*} [Fintype α] (p : Perm α)
    (root : α) (t : ℕ)
    (ht : t < Fintype.card (Fibre p (componentOf p root))) :
    ((orbitEnumeration p root).symm
      ⟨(p ^ t) root, componentOf_pow_apply p t root⟩).val = t := by
  have h : orbitEnumeration p root ⟨t, ht⟩ =
      ⟨(p ^ t) root, componentOf_pow_apply p t root⟩ :=
    Subtype.ext (orbitEnumeration_apply_val p root ⟨t, ht⟩)
  rw [← h, Equiv.symm_apply_apply]

theorem visitPosition_eq_of_pow {D : PLLinkDiagram} (T : BasedTraversal D)
    (root e : Fin D.nArc) (t : ℕ)
    (hroot : (T.baseArc (componentOf D.continuation root)).val = root)
    (ht : t < Fintype.card (Fibre D.continuation (componentOf D.continuation root)))
    (he : (D.continuation ^ t) root = e) :
    visitPosition T e = t := by
  subst e
  rw [visitPosition_eq_orbitPosition_of_baseArc T _ root
    (by rw [componentOf_pow_apply]; exact hroot) (componentOf_pow_apply _ _ _)]
  exact orbitPosition_eq_of_pow D.continuation root t ht

theorem visitPosition_lt_card {D : PLLinkDiagram} (T : BasedTraversal D)
    (e : Fin D.nArc) :
    visitPosition T e <
      Fintype.card (Fibre D.continuation (componentOf D.continuation e)) := by
  let C := componentOf D.continuation e
  let base := T.baseArc C
  have hlt := ((orbitEnumeration D.continuation base.val).symm
    ⟨e, (show componentOf D.continuation e = C from rfl).trans base.property.symm⟩).isLt
  have hEq : componentOf D.continuation base.val = C := base.property
  exact hlt.trans_eq (Fintype.card_congr (Equiv.cast (congrArg (Fibre D.continuation) hEq)))

theorem pow_card_fibre_apply {α : Type*} [Fintype α] (p : Perm α) (root : α) :
    (p ^ Fintype.card (Fibre p (componentOf p root))) root = root := by
  let q := fibrePerm p (componentOf p root)
  let x₀ : Fibre p (componentOf p root) := ⟨root, rfl⟩
  have hq : q.IsCycleOn (Finset.univ : Finset (Fibre p (componentOf p root))) := by
    simpa using fibrePerm_isCycleOn p (componentOf p root)
  have hmod : Fintype.card (Fibre p (componentOf p root)) ≡ 0
      [MOD (Finset.univ : Finset (Fibre p (componentOf p root))).card] := by
    simp [Nat.ModEq]
  have hpow := (hq.pow_apply_eq_pow_apply (Finset.mem_univ x₀)).mpr hmod
  simpa [q, x₀] using congrArg Subtype.val hpow

theorem card_fibre_smooth_gt_of_pow_disjoint (G : PLLinkDiagram) (x : Fin G.nCrossing)
    (root : Fin G.nArc) (m : ℕ)
    (hm : m < Fintype.card (Fibre G.continuation (componentOf G.continuation root)))
    (hdisj : ∀ t < m, ∀ j : Fin 2, (G.continuation ^ t) root ≠ G.incoming x j) :
    m < Fintype.card (Fibre (smoothCrossing G x).continuation
      (componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl root)))) := by
  let f : Fin (m + 1) → Fibre (smoothCrossing G x).continuation
      (componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl root))) :=
    fun s => ⟨((smoothCrossing G x).continuation ^ s.val) (smoothArcEquiv G (Sum.inl root)),
      componentOf_pow_apply (smoothCrossing G x).continuation s.val
        (smoothArcEquiv G (Sum.inl root))⟩
  have hf_inj : Function.Injective f := by
    intro s₁ s₂ hEq
    have hv := congrArg Subtype.val hEq
    dsimp [f] at hv
    rw [smooth_pow_eq_of_disjoint G x root m hdisj s₁.val (by omega),
        smooth_pow_eq_of_disjoint G x root m hdisj s₂.val (by omega)] at hv
    have hpow := Sum.inl.inj ((smoothArcEquiv G).injective hv)
    have henum : orbitEnumeration G.continuation root ⟨s₁.val, by omega⟩ =
        orbitEnumeration G.continuation root ⟨s₂.val, by omega⟩ := by
      apply Subtype.ext
      simpa only [orbitEnumeration_apply_val] using hpow
    have hfin := (orbitEnumeration G.continuation root).injective henum
    exact Fin.ext (Fin.mk.inj hfin)
  have hcard := Fintype.card_le_of_injective f hf_inj
  rw [Fintype.card_fin] at hcard
  omega

/-! ### Part 4: Protected Top-Loop Traversal Transport and Deletion -/

theorem rankBefore_trans {n : ℕ} {x y z : Fin n × ℕ}
    (hxy : rankBefore x y) (hyz : rankBefore y z) :
    rankBefore x z := by
  unfold rankBefore at *
  simp only [Fin.lt_def, Fin.ext_iff] at *
  omega

theorem rankBefore_trichotomy {n : ℕ} (x y : Fin n × ℕ) :
    rankBefore x y ∨ x = y ∨ rankBefore y x := by
  unfold rankBefore
  simp only [Prod.ext_iff, Fin.lt_def, Fin.ext_iff]
  omega

def TopProtected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (a : Fin G.nArc) : Prop :=
  rankBefore (visitRank U a) (visitRank U (G.incoming c (otherBranch i))) ∨
    a = G.incoming c (otherBranch i)

theorem topProtected_d1 (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) :
    TopProtected G U c i (G.incoming c (otherBranch i)) :=
  Or.inr rfl

theorem visitPosition_root_eq_zero (G : PLLinkDiagram) (U : BasedTraversal G)
    (root : Fin G.nArc)
    (hroot : (U.baseArc (componentOf G.continuation root)).val = root) :
    visitPosition U root = 0 := by
  have hlt : 0 < Fintype.card (Fibre G.continuation (componentOf G.continuation root)) := by
    have := visitPosition_lt_card U root
    omega
  exact visitPosition_eq_of_pow U root root 0 hroot hlt rfl

theorem visitPosition_d1_pos (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i) :
    0 < visitPosition U (G.incoming c (otherBranch i)) := by
  have hcomp : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hpos0 := visitPosition_root_eq_zero G U (G.incoming c i) hroot
  have hne : visitPosition U (G.incoming c (otherBranch i)) ≠ 0 := by
    intro h0
    apply rootCut_ports_distinct G c i
    apply visitRank_injective U
    unfold visitRank
    rw [hcomp, hpos0, h0]
  omega

theorem topProtected_d0 (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i) :
    TopProtected G U c i (G.incoming c i) := by
  left
  have hcomp : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hpos0 := visitPosition_root_eq_zero G U (G.incoming c i) hroot
  have hpos1 := visitPosition_d1_pos G U c hself i hroot
  unfold rankBefore visitRank
  right
  refine ⟨by dsimp; rw [hcomp], ?_⟩
  dsimp
  omega

theorem topProtected_of_pow_le (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (a : Fin G.nArc)
    (ha : TopProtected G U c i a) (t : ℕ) (ht : t ≤ visitPosition U a) :
    TopProtected G U c i
      ((G.continuation ^ t) (U.baseArc (componentOf G.continuation a)).val) := by
  let root := (U.baseArc (componentOf G.continuation a)).val
  have hroot_comp : componentOf G.continuation root = componentOf G.continuation a :=
    (U.baseArc (componentOf G.continuation a)).property
  have hroot_base : (U.baseArc (componentOf G.continuation root)).val = root := by
    rw [hroot_comp]
  have hlt_a := visitPosition_lt_card U a
  have hlt_t : t < Fintype.card (Fibre G.continuation (componentOf G.continuation root)) := by
    rw [hroot_comp]
    omega
  have hpos_b := visitPosition_eq_of_pow U root ((G.continuation ^ t) root) t hroot_base hlt_t rfl
  have hcomp_b : componentOf G.continuation ((G.continuation ^ t) root) =
      componentOf G.continuation a :=
    (componentOf_pow_apply G.continuation t root).trans hroot_comp
  by_cases hteq : t = visitPosition U a
  · have hb_eq : (G.continuation ^ t) root = a := by
      rw [hteq]
      exact visitPosition_reconstruct U a
    rw [hb_eq]
    exact ha
  · left
    have hrb : rankBefore (visitRank U ((G.continuation ^ t) root)) (visitRank U a) := by
      unfold rankBefore visitRank
      right
      refine ⟨by dsimp; rw [hcomp_b], ?_⟩
      dsimp
      omega
    rcases ha with ha_lt | rfl
    · exact rankBefore_trans hrb ha_lt
    · exact hrb

theorem topProtected_of_component_lt (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (b : Fin G.nArc)
    (hlt : U.componentIndex (componentOf G.continuation b) <
      U.componentIndex (componentOf G.continuation (G.incoming c i))) :
    TopProtected G U c i b := by
  left
  have hcomp : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  unfold rankBefore visitRank
  left
  rw [hcomp]
  exact hlt

theorem topProtected_component_le (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (a : Fin G.nArc) (ha : TopProtected G U c i a) :
    U.componentIndex (componentOf G.continuation a) ≤
      U.componentIndex (componentOf G.continuation (G.incoming c i)) := by
  have hcomp : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  rcases ha with hrb | rfl
  · unfold rankBefore visitRank at hrb
    rw [hcomp] at hrb
    rcases hrb with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq
  · rw [hcomp]

theorem top_ne_self (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j)) :
    c ≠ x := by
  intro h
  subst h
  exact hx i (topProtected_d0 G U c hself i hroot)

theorem top_pow_ne_incoming (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : TopProtected G U c i a)
    (t : ℕ) (ht : t ≤ visitPosition U a) (j : Fin 2) :
    (G.continuation ^ t) (U.baseArc (componentOf G.continuation a)).val ≠
      G.incoming x j := by
  intro h
  exact hx j (h ▸ topProtected_of_pow_le G U c i a ha t ht)

theorem top_pow_smooth_eq (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : TopProtected G U c i a) :
    ((smoothCrossing G x).continuation ^ visitPosition U a)
      (smoothArcEquiv G (Sum.inl (U.baseArc (componentOf G.continuation a)).val)) =
      smoothArcEquiv G (Sum.inl a) := by
  have hpow := smooth_pow_eq_of_disjoint G x
    (U.baseArc (componentOf G.continuation a)).val (visitPosition U a)
    (fun t ht j => top_pow_ne_incoming G U c i x hx a ha t (le_of_lt ht) j)
    (visitPosition U a) (le_refl _)
  rw [visitPosition_reconstruct U a] at hpow
  exact hpow

theorem top_componentOf_smooth_eq_base (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : TopProtected G U c i a) :
    componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a)) =
      componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (U.baseArc (componentOf G.continuation a)).val)) := by
  rw [← top_pow_smooth_eq G U c i x hx a ha, componentOf_pow_apply]

theorem smoothCrossing_incoming_retained (G : PLLinkDiagram) (x c : Fin G.nCrossing)
    (hcx : c ≠ x) (b : Fin 2) :
    (smoothCrossing G x).incoming (smoothCrossingEquiv G x ⟨c, hcx⟩) b =
      smoothArcEquiv G (Sum.inl (G.incoming c b)) := by
  change smoothArcEquiv G (Sum.inl (G.incoming
    (((smoothCrossingEquiv G x).symm (smoothCrossingEquiv G x ⟨c, hcx⟩)).val) b)) = _
  rw [Equiv.symm_apply_apply]

theorem top_smooth_self (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j)) :
    let c' := smoothCrossingEquiv G x ⟨c, top_ne_self G U c hself i hroot x hx⟩
    (smoothCrossing G x).continuation.SameCycle
      ((smoothCrossing G x).incoming c' 0) ((smoothCrossing G x).incoming c' 1) := by
  intro c'
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hsm := top_componentOf_smooth_eq_base G U c i x hx
    (G.incoming c (otherBranch i)) (topProtected_d1 G U c i)
  rw [hcomp_d1, hroot] at hsm
  have hsc : (smoothCrossing G x).continuation.SameCycle
      (smoothArcEquiv G (Sum.inl (G.incoming c i)))
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) :=
    (componentOf_eq_iff _ _ _).mp hsm.symm
  rw [smoothCrossing_incoming_retained G x c (top_ne_self G U c hself i hroot x hx) 0,
      smoothCrossing_incoming_retained G x c (top_ne_self G U c hself i hroot x hx) 1]
  fin_cases i
  · exact hsc
  · exact hsc.symm

theorem top_belowComp_pow_ne (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (C : diagramComponent G)
    (hlt : U.componentIndex C <
      U.componentIndex (componentOf G.continuation (G.incoming c i)))
    (t : ℕ) (j : Fin 2) :
    (G.continuation ^ t) (U.baseArc C).val ≠ G.incoming x j := by
  intro h
  have hcomp : componentOf G.continuation ((G.continuation ^ t) (U.baseArc C).val) = C :=
    (componentOf_pow_apply G.continuation t (U.baseArc C).val).trans (U.baseArc C).property
  have hprot : TopProtected G U c i ((G.continuation ^ t) (U.baseArc C).val) :=
    topProtected_of_component_lt G U c hself i _ (by rw [hcomp]; exact hlt)
  exact hx j (h ▸ hprot)

def IsTopBelowComp (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (C : diagramComponent G) (C' : diagramComponent (smoothCrossing G x)) : Prop :=
  U.componentIndex C < U.componentIndex (componentOf G.continuation (G.incoming c i)) ∧
    componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (U.baseArc C).val)) = C'

theorem isTopBelowComp_unique (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    {C₁ C₂ : diagramComponent G} {C' : diagramComponent (smoothCrossing G x)}
    (h₁ : IsTopBelowComp G U c i x C₁ C') (h₂ : IsTopBelowComp G U c i x C₂ C') :
    C₁ = C₂ := by
  have hiff := smooth_sameCycle_unaffected_iff G x (U.baseArc C₁).val
    (top_belowComp_pow_ne G U c hself i x hx C₁ h₁.1)
    (smoothArcEquiv G (Sum.inl (U.baseArc C₂).val))
  obtain ⟨b, hb_comp, hb_eq⟩ := hiff.mp (h₂.2.trans h₁.2.symm)
  have hval : (U.baseArc C₂).val = b := Sum.inl.inj ((smoothArcEquiv G).injective hb_eq)
  calc
    C₁ = componentOf G.continuation (U.baseArc C₁).val := (U.baseArc C₁).property.symm
    _ = componentOf G.continuation b := hb_comp.symm
    _ = componentOf G.continuation (U.baseArc C₂).val := by rw [hval]
    _ = C₂ := (U.baseArc C₂).property

theorem isTopBelowComp_ne_d0 (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    {C : diagramComponent G} {C' : diagramComponent (smoothCrossing G x)}
    (h : IsTopBelowComp G U c i x C C') :
    C' ≠ componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
  intro hEq
  have hiff := smooth_sameCycle_unaffected_iff G x (U.baseArc C).val
    (top_belowComp_pow_ne G U c hself i x hx C h.1)
    (smoothArcEquiv G (Sum.inl (G.incoming c i)))
  obtain ⟨b, hb_comp, hb_eq⟩ := hiff.mp (hEq.symm.trans h.2.symm)
  have hval : G.incoming c i = b := Sum.inl.inj ((smoothArcEquiv G).injective hb_eq)
  have hC : componentOf G.continuation (G.incoming c i) = C := by
    rw [hval, hb_comp, (U.baseArc C).property]
  exact (ne_of_lt h.1) (congrArg U.componentIndex hC.symm)

noncomputable def topSmoothWeight (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (C' : diagramComponent (smoothCrossing G x)) : ℕ :=
  if h : ∃ C, IsTopBelowComp G U c i x C C' then
    (U.componentIndex (Classical.choose h)).val
  else if C' = componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) then
    (U.componentIndex (componentOf G.continuation (G.incoming c i))).val
  else
    (U.componentIndex (componentOf G.continuation (G.incoming c i))).val + 1

noncomputable def topSmoothBaseArc (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (C' : diagramComponent (smoothCrossing G x)) :
    {e : Fin (smoothCrossing G x).nArc //
      componentOf (smoothCrossing G x).continuation e = C'} :=
  if h : ∃ C, IsTopBelowComp G U c i x C C' then
    ⟨smoothArcEquiv G (Sum.inl (U.baseArc (Classical.choose h)).val),
      (Classical.choose_spec h).2⟩
  else if h0 : C' = componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) then
    ⟨smoothArcEquiv G (Sum.inl (G.incoming c i)), h0.symm⟩
  else
    Classical.choice (fibreNonempty (smoothCrossing G x).continuation C')

noncomputable def topSmoothTraversal (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing) :
    BasedTraversal (smoothCrossing G x) where
  componentIndex := equivFinOfWeight (topSmoothWeight G U c i x)
  baseArc := topSmoothBaseArc G U c i x

theorem topSmoothBaseArc_of_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : TopProtected G U c i a) :
    ((topSmoothTraversal G U c i x).baseArc
      (componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a)))).val =
      smoothArcEquiv G (Sum.inl (U.baseArc (componentOf G.continuation a)).val) := by
  let C := componentOf G.continuation a
  let C' := componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a))
  have hC' : componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (U.baseArc C).val)) = C' :=
    (top_componentOf_smooth_eq_base G U c i x hx a ha).symm
  have hle := topProtected_component_le G U c hself i a ha
  change (topSmoothBaseArc G U c i x C').val = _
  unfold topSmoothBaseArc
  by_cases hlt : U.componentIndex C <
      U.componentIndex (componentOf G.continuation (G.incoming c i))
  · have hex : ∃ C₀, IsTopBelowComp G U c i x C₀ C' := ⟨C, hlt, hC'⟩
    rw [dif_pos hex]
    have huniq := isTopBelowComp_unique G U c hself i x hx
      (Classical.choose_spec hex) ⟨hlt, hC'⟩
    dsimp
    rw [huniq]
  · have hEq_idx : U.componentIndex C =
        U.componentIndex (componentOf G.continuation (G.incoming c i)) :=
      le_antisymm hle (not_lt.mp hlt)
    have hEq_C : C = componentOf G.continuation (G.incoming c i) :=
      U.componentIndex.injective hEq_idx
    have hbase_d0 : (U.baseArc C).val = G.incoming c i := by
      rw [hEq_C, hroot]
    have hC'_d0 : C' = componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
      rw [← hC', hbase_d0]
    have hnot : ¬ ∃ C₀, IsTopBelowComp G U c i x C₀ C' := by
      rintro ⟨C₀, hC₀⟩
      exact isTopBelowComp_ne_d0 G U c hself i x hx hC₀ hC'_d0
    rw [dif_neg hnot, dif_pos hC'_d0, hbase_d0]

theorem topSmoothWeight_of_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : TopProtected G U c i a) :
    topSmoothWeight G U c i x
      (componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a))) =
      (U.componentIndex (componentOf G.continuation a)).val := by
  let C := componentOf G.continuation a
  let C' := componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a))
  have hC' : componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (U.baseArc C).val)) = C' :=
    (top_componentOf_smooth_eq_base G U c i x hx a ha).symm
  have hle := topProtected_component_le G U c hself i a ha
  unfold topSmoothWeight
  by_cases hlt : U.componentIndex C <
      U.componentIndex (componentOf G.continuation (G.incoming c i))
  · have hex : ∃ C₀, IsTopBelowComp G U c i x C₀ C' := ⟨C, hlt, hC'⟩
    rw [dif_pos hex]
    have huniq := isTopBelowComp_unique G U c hself i x hx
      (Classical.choose_spec hex) ⟨hlt, hC'⟩
    rw [huniq]
  · have hEq_idx : U.componentIndex C =
        U.componentIndex (componentOf G.continuation (G.incoming c i)) :=
      le_antisymm hle (not_lt.mp hlt)
    have hEq_C : C = componentOf G.continuation (G.incoming c i) :=
      U.componentIndex.injective hEq_idx
    have hbase_d0 : (U.baseArc C).val = G.incoming c i := by
      rw [hEq_C, hroot]
    have hC'_d0 : C' = componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
      rw [← hC', hbase_d0]
    have hnot : ¬ ∃ C₀, IsTopBelowComp G U c i x C₀ C' := by
      rintro ⟨C₀, hC₀⟩
      exact isTopBelowComp_ne_d0 G U c hself i x hx hC₀ hC'_d0
    rw [dif_neg hnot, if_pos hC'_d0]
    exact congrArg Fin.val hEq_idx.symm

theorem topSmooth_visitPosition_of_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : TopProtected G U c i a) :
    visitPosition (topSmoothTraversal G U c i x) (smoothArcEquiv G (Sum.inl a)) =
      visitPosition U a := by
  let root := (U.baseArc (componentOf G.continuation a)).val
  have hroot_comp : componentOf G.continuation root = componentOf G.continuation a :=
    (U.baseArc (componentOf G.continuation a)).property
  have hbase_sm : ((topSmoothTraversal G U c i x).baseArc
      (componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl root)))).val =
      smoothArcEquiv G (Sum.inl root) := by
    rw [← top_componentOf_smooth_eq_base G U c i x hx a ha]
    exact topSmoothBaseArc_of_protected G U c hself i hroot x hx a ha
  have hlt_a : visitPosition U a <
      Fintype.card (Fibre G.continuation (componentOf G.continuation root)) := by
    rw [hroot_comp]
    exact visitPosition_lt_card U a
  have hlt_sm := card_fibre_smooth_gt_of_pow_disjoint G x root (visitPosition U a) hlt_a
    (fun t ht j => top_pow_ne_incoming G U c i x hx a ha t (le_of_lt ht) j)
  exact visitPosition_eq_of_pow (topSmoothTraversal G U c i x)
    (smoothArcEquiv G (Sum.inl root)) (smoothArcEquiv G (Sum.inl a))
    (visitPosition U a) hbase_sm hlt_sm
    (top_pow_smooth_eq G U c i x hx a ha)

theorem topSmooth_rankBefore_d1_of_not_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (z : Fin (smoothCrossing G x).nArc)
    (hz : ∀ a : Fin G.nArc, TopProtected G U c i a →
      z ≠ (smoothArcEquiv G (Sum.inl a) : Fin (smoothCrossing G x).nArc)) :
    rankBefore
      (visitRank (topSmoothTraversal G U c i x)
        (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))))
      (visitRank (topSmoothTraversal G U c i x) z) := by
  let U' := topSmoothTraversal G U c i x
  let d0 := G.incoming c i
  let d1 := G.incoming c (otherBranch i)
  have hd0 : TopProtected G U c i d0 := topProtected_d0 G U c hself i hroot
  have hd1 : TopProtected G U c i d1 := topProtected_d1 G U c i
  have hcomp_d1_G : componentOf G.continuation d1 = componentOf G.continuation d0 :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hcomp_d1_E : componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl d1)) =
      componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl d0)) := by
    have h := top_componentOf_smooth_eq_base G U c i x hx d1 hd1
    rw [hcomp_d1_G, hroot] at h
    exact h
  by_cases hz_comp : componentOf (smoothCrossing G x).continuation z =
      componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl d0))
  · right
    refine ⟨by change U'.componentIndex _ = U'.componentIndex _; rw [hcomp_d1_E, hz_comp], ?_⟩
    change visitPosition U' (smoothArcEquiv G (Sum.inl d1)) < visitPosition U' z
    rw [topSmooth_visitPosition_of_protected G U c hself i hroot x hx d1 hd1]
    by_contra hle
    have hle' : visitPosition U' z ≤ visitPosition U d1 := by omega
    have hrec := visitPosition_reconstruct U' z
    have hbase_z : (U'.baseArc (componentOf (smoothCrossing G x).continuation z)).val =
        smoothArcEquiv G (Sum.inl d0) := by
      rw [hz_comp]
      have hb := topSmoothBaseArc_of_protected G U c hself i hroot x hx d0 hd0
      rw [hroot] at hb
      exact hb
    rw [hbase_z] at hrec
    have hpow := smooth_pow_eq_of_disjoint G x d0 (visitPosition U d1)
      (fun t ht j => by
        dsimp only [d0]
        rw [← hroot, ← hcomp_d1_G]
        exact top_pow_ne_incoming G U c i x hx d1 hd1 t (le_of_lt ht) j)
      (visitPosition U' z) hle'
    have hz_eq : z = smoothArcEquiv G (Sum.inl ((G.continuation ^ visitPosition U' z) d0)) :=
      hrec.symm.trans hpow
    have hprot_t : TopProtected G U c i ((G.continuation ^ visitPosition U' z) d0) := by
      have hp := topProtected_of_pow_le G U c i d1 hd1 (visitPosition U' z) hle'
      rw [hcomp_d1_G, hroot] at hp
      exact hp
    exact hz ((G.continuation ^ visitPosition U' z) d0) hprot_t hz_eq
  · left
    change U'.componentIndex (componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl d1))) <
      U'.componentIndex (componentOf (smoothCrossing G x).continuation z)
    apply equivFinOfWeight_lt_of_lt (topSmoothWeight G U c i x)
    rw [topSmoothWeight_of_protected G U c hself i hroot x hx d1 hd1, hcomp_d1_G]
    have hnot_below : ¬ ∃ C, IsTopBelowComp G U c i x C
        (componentOf (smoothCrossing G x).continuation z) := by
      rintro ⟨C, hlt, hC'⟩
      have hiff := smooth_sameCycle_unaffected_iff G x (U.baseArc C).val
        (top_belowComp_pow_ne G U c hself i x hx C hlt) z
      obtain ⟨b, hb_comp, hb_eq⟩ := hiff.mp hC'.symm
      rw [(U.baseArc C).property] at hb_comp
      have hb_prot : TopProtected G U c i b :=
        topProtected_of_component_lt G U c hself i b (by rw [hb_comp]; exact hlt)
      exact hz b hb_prot hb_eq
    unfold topSmoothWeight
    rw [dif_neg hnot_below, if_neg hz_comp]
    dsimp only [d0]
    omega

theorem topSmooth_protected_iff (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (z : Fin (smoothCrossing G x).nArc) :
    let c' := smoothCrossingEquiv G x ⟨c, top_ne_self G U c hself i hroot x hx⟩
    TopProtected (smoothCrossing G x) (topSmoothTraversal G U c i x) c' i z ↔
      ∃ a : Fin G.nArc, TopProtected G U c i a ∧
        z = (smoothArcEquiv G (Sum.inl a) : Fin (smoothCrossing G x).nArc) := by
  intro c'
  have hd1_sm : (smoothCrossing G x).incoming c' (otherBranch i) =
      smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))) :=
    smoothCrossing_incoming_retained G x c (top_ne_self G U c hself i hroot x hx) (otherBranch i)
  constructor
  · intro hz_prot
    by_contra hnot
    have hnot' : ∀ a : Fin G.nArc, TopProtected G U c i a →
        z ≠ (smoothArcEquiv G (Sum.inl a) : Fin (smoothCrossing G x).nArc) :=
      fun a ha hEq => hnot ⟨a, ha, hEq⟩
    have hgt := topSmooth_rankBefore_d1_of_not_protected G U c hself i hroot x hx z hnot'
    unfold TopProtected at hz_prot
    rw [hd1_sm] at hz_prot
    rcases hz_prot with hlt | hEq
    · exact rankBefore_asymm hlt hgt
    · exact hnot' (G.incoming c (otherBranch i)) (topProtected_d1 G U c i) hEq
  · rintro ⟨a, ha, rfl⟩
    unfold TopProtected
    rw [hd1_sm]
    rcases ha with hrb | rfl
    · left
      unfold rankBefore visitRank at hrb ⊢
      rw [topSmooth_visitPosition_of_protected G U c hself i hroot x hx a (Or.inl hrb),
          topSmooth_visitPosition_of_protected G U c hself i hroot x hx
            (G.incoming c (otherBranch i)) (topProtected_d1 G U c i)]
      rcases hrb with hlt | ⟨hEq, hpos⟩
      · left
        change equivFinOfWeight (topSmoothWeight G U c i x) _ <
          equivFinOfWeight (topSmoothWeight G U c i x) _
        apply equivFinOfWeight_lt_of_lt
        rw [topSmoothWeight_of_protected G U c hself i hroot x hx a (Or.inl (Or.inl hlt)),
            topSmoothWeight_of_protected G U c hself i hroot x hx
              (G.incoming c (otherBranch i)) (topProtected_d1 G U c i)]
        exact hlt
      · right
        have hcomp_G : componentOf G.continuation a =
            componentOf G.continuation (G.incoming c (otherBranch i)) :=
          U.componentIndex.injective hEq
        have hcomp_E : componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a)) =
            componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) := by
          rw [top_componentOf_smooth_eq_base G U c i x hx a (Or.inl (Or.inr ⟨hEq, hpos⟩)),
              top_componentOf_smooth_eq_base G U c i x hx
                (G.incoming c (otherBranch i)) (topProtected_d1 G U c i),
              hcomp_G]
        exact ⟨congrArg (topSmoothTraversal G U c i x).componentIndex hcomp_E, hpos⟩
    · right; rfl

theorem topSmooth_rankBefore_iff_of_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j))
    (a b : Fin G.nArc)
    (hab : TopProtected G U c i a ∨ TopProtected G U c i b) :
    rankBefore
      (visitRank (topSmoothTraversal G U c i x) (smoothArcEquiv G (Sum.inl a)))
      (visitRank (topSmoothTraversal G U c i x) (smoothArcEquiv G (Sum.inl b))) ↔
      rankBefore (visitRank U a) (visitRank U b) := by
  let U' := topSmoothTraversal G U c i x
  let d1 := G.incoming c (otherBranch i)
  by_cases ha : TopProtected G U c i a
  · by_cases hb : TopProtected G U c i b
    · unfold rankBefore visitRank
      rw [topSmooth_visitPosition_of_protected G U c hself i hroot x hx a ha,
          topSmooth_visitPosition_of_protected G U c hself i hroot x hx b hb]
      constructor
      · rintro (hlt | ⟨hEq, hpos⟩)
        · left
          by_contra hge
          have hle : (U.componentIndex (componentOf G.continuation b)).val ≤
              (U.componentIndex (componentOf G.continuation a)).val := not_lt.mp hge
          rcases lt_or_eq_of_le hle with hlt' | hEq'
          · have hlt_E : U'.componentIndex (componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl b))) <
              U'.componentIndex (componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl a))) := by
              apply equivFinOfWeight_lt_of_lt (topSmoothWeight G U c i x)
              rw [topSmoothWeight_of_protected G U c hself i hroot x hx b hb,
                  topSmoothWeight_of_protected G U c hself i hroot x hx a ha]
              exact hlt'
            exact (lt_asymm hlt) hlt_E
          · have hcomp_G : componentOf G.continuation a = componentOf G.continuation b :=
              U.componentIndex.injective (Fin.ext hEq'.symm)
            have hcomp_E : componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl a)) =
              componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl b)) := by
              rw [top_componentOf_smooth_eq_base G U c i x hx a ha,
                  top_componentOf_smooth_eq_base G U c i x hx b hb, hcomp_G]
            exact (ne_of_lt hlt) (congrArg U'.componentIndex hcomp_E)
        · right
          refine ⟨?_, hpos⟩
          dsimp at hEq ⊢
          by_contra hne
          have hne_val : (U.componentIndex (componentOf G.continuation a)).val ≠
              (U.componentIndex (componentOf G.continuation b)).val :=
            fun h => hne (Fin.ext h)
          rcases lt_or_gt_of_ne hne_val with hlt | hgt
          · have hlt_E : U'.componentIndex (componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl a))) <
              U'.componentIndex (componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl b))) := by
              apply equivFinOfWeight_lt_of_lt (topSmoothWeight G U c i x)
              rw [topSmoothWeight_of_protected G U c hself i hroot x hx a ha,
                  topSmoothWeight_of_protected G U c hself i hroot x hx b hb]
              exact hlt
            exact (ne_of_lt hlt_E) hEq
          · have hgt_E : U'.componentIndex (componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl b))) <
              U'.componentIndex (componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl a))) := by
              apply equivFinOfWeight_lt_of_lt (topSmoothWeight G U c i x)
              rw [topSmoothWeight_of_protected G U c hself i hroot x hx b hb,
                  topSmoothWeight_of_protected G U c hself i hroot x hx a ha]
              exact hgt
            exact (ne_of_gt hgt_E) hEq
      · rintro (hlt | ⟨hEq, hpos⟩)
        · left
          apply equivFinOfWeight_lt_of_lt (topSmoothWeight G U c i x)
          rw [topSmoothWeight_of_protected G U c hself i hroot x hx a ha,
              topSmoothWeight_of_protected G U c hself i hroot x hx b hb]
          exact hlt
        · right
          have hcomp_G : componentOf G.continuation a = componentOf G.continuation b :=
            U.componentIndex.injective hEq
          have hcomp_E : componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl a)) =
            componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl b)) := by
            rw [top_componentOf_smooth_eq_base G U c i x hx a ha,
                top_componentOf_smooth_eq_base G U c i x hx b hb, hcomp_G]
          exact ⟨congrArg U'.componentIndex hcomp_E, hpos⟩
    · have hb_not : ∀ a₀ : Fin G.nArc, TopProtected G U c i a₀ →
          smoothArcEquiv G (Sum.inl b) ≠ smoothArcEquiv G (Sum.inl a₀) := by
        intro a₀ ha₀ hEq
        have hba₀ : b = a₀ := Sum.inl.inj ((smoothArcEquiv G).injective hEq)
        exact hb (hba₀ ▸ ha₀)
      have hgt_E := topSmooth_rankBefore_d1_of_not_protected G U c hself i hroot x hx
        (smoothArcEquiv G (Sum.inl b)) hb_not
      have ha_E : TopProtected (smoothCrossing G x) U'
          (smoothCrossingEquiv G x ⟨c, top_ne_self G U c hself i hroot x hx⟩) i
          (smoothArcEquiv G (Sum.inl a)) :=
        (topSmooth_protected_iff G U c hself i hroot x hx _).mpr ⟨a, ha, rfl⟩
      have hd1_sm : (smoothCrossing G x).incoming
          (smoothCrossingEquiv G x ⟨c, top_ne_self G U c hself i hroot x hx⟩) (otherBranch i) =
          smoothArcEquiv G (Sum.inl d1) :=
        smoothCrossing_incoming_retained G x c (top_ne_self G U c hself i hroot x hx) (otherBranch i)
      unfold TopProtected at ha_E
      rw [hd1_sm] at ha_E
      have hrb_E : rankBefore (visitRank U' (smoothArcEquiv G (Sum.inl a)))
          (visitRank U' (smoothArcEquiv G (Sum.inl b))) := by
        rcases ha_E with hlt_E | hEq_E
        · exact rankBefore_trans hlt_E hgt_E
        · rw [hEq_E]; exact hgt_E
      have hgt_G : rankBefore (visitRank U d1) (visitRank U b) := by
        have hne_d1 : b ≠ d1 := fun h => hb (Or.inr h)
        have hnot_lt : ¬ rankBefore (visitRank U b) (visitRank U d1) :=
          fun h => hb (Or.inl h)
        rcases rankBefore_trichotomy (visitRank U d1) (visitRank U b) with hlt | hEq | hgt
        · exact hlt
        · exact False.elim (hne_d1 (visitRank_injective U hEq.symm))
        · exact False.elim (hnot_lt hgt)
      have hrb_G : rankBefore (visitRank U a) (visitRank U b) := by
        rcases ha with hlt_G | rfl
        · exact rankBefore_trans hlt_G hgt_G
        · exact hgt_G
      exact ⟨fun _ => hrb_G, fun _ => hrb_E⟩
  · have hb : TopProtected G U c i b := hab.resolve_left ha
    have ha_not : ∀ a₀ : Fin G.nArc, TopProtected G U c i a₀ →
        smoothArcEquiv G (Sum.inl a) ≠ smoothArcEquiv G (Sum.inl a₀) := by
      intro a₀ ha₀ hEq
      have haa₀ : a = a₀ := Sum.inl.inj ((smoothArcEquiv G).injective hEq)
      exact ha (haa₀ ▸ ha₀)
    have hgt_E := topSmooth_rankBefore_d1_of_not_protected G U c hself i hroot x hx
      (smoothArcEquiv G (Sum.inl a)) ha_not
    have hb_E : TopProtected (smoothCrossing G x) U'
        (smoothCrossingEquiv G x ⟨c, top_ne_self G U c hself i hroot x hx⟩) i
        (smoothArcEquiv G (Sum.inl b)) :=
      (topSmooth_protected_iff G U c hself i hroot x hx _).mpr ⟨b, hb, rfl⟩
    have hd1_sm : (smoothCrossing G x).incoming
        (smoothCrossingEquiv G x ⟨c, top_ne_self G U c hself i hroot x hx⟩) (otherBranch i) =
        smoothArcEquiv G (Sum.inl d1) :=
      smoothCrossing_incoming_retained G x c (top_ne_self G U c hself i hroot x hx) (otherBranch i)
    unfold TopProtected at hb_E
    rw [hd1_sm] at hb_E
    have hrb_E : rankBefore (visitRank U' (smoothArcEquiv G (Sum.inl b)))
        (visitRank U' (smoothArcEquiv G (Sum.inl a))) := by
      rcases hb_E with hlt_E | hEq_E
      · exact rankBefore_trans hlt_E hgt_E
      · rw [hEq_E]; exact hgt_E
    have hgt_G : rankBefore (visitRank U d1) (visitRank U a) := by
      have hne_d1 : a ≠ d1 := fun h => ha (Or.inr h)
      have hnot_lt : ¬ rankBefore (visitRank U a) (visitRank U d1) :=
        fun h => ha (Or.inl h)
      rcases rankBefore_trichotomy (visitRank U d1) (visitRank U a) with hlt | hEq | hgt
      · exact hlt
      · exact False.elim (hne_d1 (visitRank_injective U hEq.symm))
      · exact False.elim (hnot_lt hgt)
    have hrb_G : rankBefore (visitRank U b) (visitRank U a) := by
      rcases hb with hlt_G | rfl
      · exact rankBefore_trans hlt_G hgt_G
      · exact hgt_G
    exact ⟨fun h => False.elim (rankBefore_asymm h hrb_E),
      fun h => False.elim (rankBefore_asymm h hrb_G)⟩

theorem topSmooth_badCrossings_disjoint (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (hbad : ∀ y ∈ badCrossings U, ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming y j))
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j)) :
    let U' := topSmoothTraversal G U c i x
    let c' := smoothCrossingEquiv G x ⟨c, top_ne_self G U c hself i hroot x hx⟩
    ∀ y' ∈ badCrossings U', ∀ j : Fin 2,
      ¬ TopProtected (smoothCrossing G x) U' c' i ((smoothCrossing G x).incoming y' j) := by
  intro U' c' y' hy' j hprot'
  obtain ⟨⟨y, hyx⟩, rfl⟩ := (smoothCrossingEquiv G x).surjective y'
  rw [smoothCrossing_incoming_retained G x y hyx j] at hprot'
  obtain ⟨a, ha, hEq⟩ := (topSmooth_protected_iff G U c hself i hroot x hx _).mp hprot'
  have hya : G.incoming y j = a := Sum.inl.inj ((smoothArcEquiv G).injective hEq)
  have hy_prot : TopProtected G U c i (G.incoming y j) := hya ▸ ha
  have hab : TopProtected G U c i (G.incoming y 0) ∨ TopProtected G U c i (G.incoming y 1) := by
    fin_cases j
    · exact Or.inl hy_prot
    · exact Or.inr hy_prot
  have hfb := firstVisitedBranch_smooth_eq_of_rankBefore G U x U' y hyx
    (topSmooth_rankBefore_iff_of_protected G U c hself i hroot x hx _ _ hab)
  have hy'_bad : badAt U' (smoothCrossingEquiv G x ⟨y, hyx⟩) := by
    simpa [badCrossings] using hy'
  have hy_bad : badAt U y := by
    unfold badAt at hy'_bad ⊢
    rw [hfb] at hy'_bad
    intro hgood
    apply hy'_bad
    change firstVisitedBranch U y =
      G.overBranch (((smoothCrossingEquiv G x).symm (smoothCrossingEquiv G x ⟨y, hyx⟩)).val)
    rw [Equiv.symm_apply_apply]
    exact hgood
  have hy_mem : y ∈ badCrossings U := by simp [badCrossings, hy_bad]
  exact hbad y hy_mem j hy_prot

theorem topSmooth_root (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming x j)) :
    let U' := topSmoothTraversal G U c i x
    let c' := smoothCrossingEquiv G x ⟨c, top_ne_self G U c hself i hroot x hx⟩
    (U'.baseArc (componentOf (smoothCrossing G x).continuation
      ((smoothCrossing G x).incoming c' i))).val =
      (smoothCrossing G x).incoming c' i := by
  intro U' c'
  rw [smoothCrossing_incoming_retained G x c (top_ne_self G U c hself i hroot x hx) i]
  have hb := topSmoothBaseArc_of_protected G U c hself i hroot x hx
    (G.incoming c i) (topProtected_d0 G U c hself i hroot)
  rw [hroot] at hb
  exact hb

theorem topLoop_deletion {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (G : PLLinkDiagram) (hG : G.nCrossing ≤ n)
    (U : BasedTraversal G) (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (hbad : ∀ y ∈ badCrossings U, ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming y j)) :
    unlinkFactor * descendingLaurentEvaluator G U =
      descendingLaurentEvaluator (smoothCrossing G c) (smoothChildBasedTraversal G c) := by
  classical
  by_cases hne : (badCrossings U).Nonempty
  · have hex : ∃ p ∈ badCrossings U, p = Classical.choose hne :=
      ⟨Classical.choose hne, Classical.choose_spec hne, rfl⟩
    obtain ⟨p, hp_mem, hp_eq⟩ := hex
    have hp_prot : ∀ j : Fin 2, ¬ TopProtected G U c i (G.incoming p j) := hbad p hp_mem
    have hcp : c ≠ p := top_ne_self G U c hself i hroot p hp_prot
    have hpc : p ≠ c := hcp.symm
    have hevalG : descendingLaurentEvaluator G U = descendingEvaluatorPivotBranch G U p :=
      descendingEvaluator_eq_pivotBranch_of_choice G U hne p hp_eq.symm
    have hsw_bad : ∀ y ∈ badCrossings (switchTraversal U p), ∀ j : Fin 2,
        ¬ TopProtected (switchCrossing G p) (switchTraversal U p) c i
          ((switchCrossing G p).incoming y j) := by
      intro y hy j
      rw [badCrossings_switch_erase U p hp_mem] at hy
      exact hbad y (Finset.mem_of_mem_erase hy) j
    have ih_sw := topLoop_deletion outer (switchCrossing G p) hG
      (switchTraversal U p) c hself i hroot hsw_bad
    let U' := topSmoothTraversal G U c i p
    let c' := smoothCrossingEquiv G p ⟨c, hcp⟩
    have hdrop_p := smoothCrossing_crossing_count_drop G p
    have hlt_p : (smoothCrossing G p).nCrossing < n := by omega
    have hsm_le : (smoothCrossing G p).nCrossing ≤ n := le_of_lt hlt_p
    have hsm_eval_U' : descendingLaurentEvaluator (smoothCrossing G p)
        (smoothChildBasedTraversal G p) =
        descendingLaurentEvaluator (smoothCrossing G p) U' :=
      outer.1 (SignedDiagramIso.refl (smoothCrossing G p)) hlt_p
        (smoothChildBasedTraversal G p) U'
    have ih_sm := topLoop_deletion outer (smoothCrossing G p) hsm_le U' c'
      (top_smooth_self G U c hself i hroot p hp_prot) i
      (topSmooth_root G U c hself i hroot p hp_prot)
      (topSmooth_badCrossings_disjoint G U c hself i hroot hbad p hp_prot)
    let p' := smoothCrossingEquiv G c ⟨p, hpc⟩
    have hdrop_c := smoothCrossing_crossing_count_drop G c
    have hlt_c : (smoothCrossing G c).nCrossing < n := by omega
    have hlt_sw_c : (smoothCrossing (switchCrossing G p) c).nCrossing < n := by
      have h1 := smoothCrossing_crossing_count_drop (switchCrossing G p) c
      rw [switch_crossing_count] at h1
      omega
    have h_iso_sw : descendingLaurentEvaluator (smoothCrossing (switchCrossing G p) c)
        (smoothChildBasedTraversal (switchCrossing G p) c) =
        descendingLaurentEvaluator (switchCrossing (smoothCrossing G c) p')
          (switchTraversal (smoothChildBasedTraversal G c) p') :=
      outer.1 (switchSmoothSignedDiagramIso G c p hcp) hlt_sw_c _ _
    have hlt_sm_c : (smoothCrossing (smoothCrossing G c) p').nCrossing < n := by
      have h2 := smoothCrossing_crossing_count_drop (smoothCrossing G c) p'
      omega
    have h_iso_sm : descendingLaurentEvaluator (smoothCrossing (smoothCrossing G p) c')
        (smoothChildBasedTraversal (smoothCrossing G p) c') =
        descendingLaurentEvaluator (smoothCrossing (smoothCrossing G c) p')
          (smoothChildBasedTraversal (smoothCrossing G c) p') :=
      (outer.1 (smoothTwiceSignedDiagramIso G c p hcp) hlt_sm_c _ _).symm
    have hskein_c := outer.2 hlt_c (smoothChildBasedTraversal G c) p'
    rw [hevalG, descendingEvaluatorPivotBranch, mul_add,
      ← mul_assoc, mul_comm unlinkFactor (pivotSwitchFactor G p), mul_assoc,
      ih_sw, h_iso_sw, hsm_eval_U',
      ← mul_assoc, mul_comm unlinkFactor (pivotSmoothFactor G p), mul_assoc,
      ih_sm, h_iso_sm, hskein_c, descendingEvaluatorPivotBranch,
      pivotSwitchFactor_smooth_ne G p c hpc, pivotSmoothFactor_smooth_ne G p c hpc]
  · have hEmpty : badCrossings U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hevalG : descendingLaurentEvaluator G U = descendingUnlinkValue G :=
      descendingLaurentEvaluator_terminal G U (by simp [hne])
    have hgood : ∀ d : Fin G.nCrossing, d ≠ c → ¬ badAt U d := by
      intro d _ hb
      have hmem : d ∈ badCrossings U := by simp [badCrossings, hb]
      rw [hEmpty] at hmem
      exact Finset.not_mem_empty d hmem
    obtain ⟨W, hW⟩ := smoothCrossing_exists_descending_of_baseArc G U
      (componentOf G.continuation (G.incoming c i)) c i hroot.symm hself hgood
    have hdrop_c := smoothCrossing_crossing_count_drop G c
    have hlt_c : (smoothCrossing G c).nCrossing < n := by omega
    have hsm := outer.1 (SignedDiagramIso.refl (smoothCrossing G c)) hlt_c
      (smoothChildBasedTraversal G c) W
    have hevalW : descendingLaurentEvaluator (smoothCrossing G c) W =
        descendingUnlinkValue (smoothCrossing G c) :=
      descendingLaurentEvaluator_terminal (smoothCrossing G c) W
        (by simp [hW])
    rw [hevalG, hsm, hevalW, ← descendingUnlinkValue_smooth_self G c hself]
termination_by (G.nCrossing, (badCrossings U).card)
decreasing_by
  · apply Prod.Lex.right
    have hdrop := badCrossings_switch_card U p hp_mem
    omega
  · apply Prod.Lex.left
    omega

/-! ## Part 5: Protected Bottom-Loop Traversal Transport and `botLoop_deletion` -/

def BotProtected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (a : Fin G.nArc) : Prop :=
  a = G.incoming c i ∨ a = G.incoming c (otherBranch i) ∨
    rankBefore (visitRank U (G.incoming c (otherBranch i))) (visitRank U a)

theorem botProtected_d0 (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) :
    BotProtected G U c i (G.incoming c i) := Or.inl rfl

theorem botProtected_d1 (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) :
    BotProtected G U c i (G.incoming c (otherBranch i)) := Or.inr (Or.inl rfl)

theorem bot_ne_self (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j)) :
    c ≠ x := by
  intro h
  subst x
  exact hx i (botProtected_d0 G U c i)

theorem botProtected_component_ge (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (a : Fin G.nArc)
    (ha : BotProtected G U c i a) :
    U.componentIndex (componentOf G.continuation (G.incoming c i)) ≤
      U.componentIndex (componentOf G.continuation a) := by
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  rcases ha with rfl | rfl | hrb
  · exact le_rfl
  · rw [hcomp_d1]
  · unfold rankBefore visitRank at hrb
    rw [hcomp_d1] at hrb
    rcases hrb with hlt | ⟨hEq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq hEq

theorem botProtected_of_component_gt (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (a : Fin G.nArc)
    (hgt : U.componentIndex (componentOf G.continuation (G.incoming c i)) <
      U.componentIndex (componentOf G.continuation a)) :
    BotProtected G U c i a := by
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  right; right; left
  change U.componentIndex (componentOf G.continuation (G.incoming c (otherBranch i))) <
    U.componentIndex (componentOf G.continuation a)
  rw [hcomp_d1]
  exact hgt

theorem botProtected_same_component_iff (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (a : Fin G.nArc)
    (hcomp : componentOf G.continuation a =
      componentOf G.continuation (G.incoming c i))
    (hne : a ≠ G.incoming c i) :
    BotProtected G U c i a ↔
      visitPosition U (G.incoming c (otherBranch i)) ≤ visitPosition U a := by
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  unfold BotProtected rankBefore visitRank
  dsimp
  rw [hcomp, hcomp_d1]
  constructor
  · rintro (h0 | h1 | (hlt | ⟨_, hpos⟩))
    · exact False.elim (hne h0)
    · rw [h1]
    · exact False.elim (lt_irrefl _ hlt)
    · exact le_of_lt hpos
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | hEq
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, hlt⟩))
    · have ha : a = G.incoming c (otherBranch i) :=
        visitRank_injective U
          (Prod.ext (congrArg U.componentIndex (hcomp.trans hcomp_d1.symm)) hEq.symm)
      exact Or.inr (Or.inl ha)

theorem botProtected_of_pow_d1 (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (s : ℕ)
    (hs : s ≤ Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) -
        visitPosition U (G.incoming c (otherBranch i))) :
    BotProtected G U c i ((G.continuation ^ s) (G.incoming c (otherBranch i))) := by
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hd1_lt : visitPosition U (G.incoming c (otherBranch i)) <
      Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) := by
    have h := visitPosition_lt_card U (G.incoming c (otherBranch i))
    rwa [hcomp_d1] at h
  have hd1_rec : (G.continuation ^ visitPosition U (G.incoming c (otherBranch i)))
      (G.incoming c i) = G.incoming c (otherBranch i) := by
    have h := visitPosition_reconstruct U (G.incoming c (otherBranch i))
    rwa [hcomp_d1, hroot] at h
  have hpow_add : (G.continuation ^ s) (G.incoming c (otherBranch i)) =
      (G.continuation ^ (visitPosition U (G.incoming c (otherBranch i)) + s))
        (G.incoming c i) := by
    rw [add_comm (visitPosition U (G.incoming c (otherBranch i))) s,
      pow_add, Perm.mul_apply, hd1_rec]
  rcases eq_or_lt_of_le hs with hEq | hlt
  · have hsum : visitPosition U (G.incoming c (otherBranch i)) + s =
        Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) := by
      omega
    rw [hpow_add, hsum, pow_card_fibre_apply G.continuation (G.incoming c i)]
    exact botProtected_d0 G U c i
  · have hsum_lt : visitPosition U (G.incoming c (otherBranch i)) + s <
        Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) := by
      omega
    have hcomp_s : componentOf G.continuation
        ((G.continuation ^ s) (G.incoming c (otherBranch i))) =
        componentOf G.continuation (G.incoming c i) := by
      rw [hpow_add]
      exact componentOf_pow_apply G.continuation _ (G.incoming c i)
    have hvp_s : visitPosition U ((G.continuation ^ s) (G.incoming c (otherBranch i))) =
        visitPosition U (G.incoming c (otherBranch i)) + s :=
      visitPosition_eq_of_pow U (G.incoming c i)
        ((G.continuation ^ s) (G.incoming c (otherBranch i)))
        (visitPosition U (G.incoming c (otherBranch i)) + s)
        hroot hsum_lt hpow_add.symm
    have hpos_d1 := visitPosition_d1_pos G U c hself i hroot
    have hne_d0 : (G.continuation ^ s) (G.incoming c (otherBranch i)) ≠ G.incoming c i := by
      intro hEq0
      have hvp0 : visitPosition U ((G.continuation ^ s) (G.incoming c (otherBranch i))) = 0 := by
        rw [hEq0]
        exact visitPosition_root_eq_zero G U (G.incoming c i) hroot
      omega
    exact (botProtected_same_component_iff G U c hself i _ hcomp_s hne_d0).mpr (by omega)

theorem bot_pow_d1_ne_incoming (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (s : ℕ)
    (hs : s ≤ Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) -
        visitPosition U (G.incoming c (otherBranch i)))
    (j : Fin 2) :
    (G.continuation ^ s) (G.incoming c (otherBranch i)) ≠ G.incoming x j := by
  intro h
  exact hx j (h ▸ botProtected_of_pow_d1 G U c hself i hroot s hs)

theorem bot_pow_L_eq_d0 (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j)) :
    ((smoothCrossing G x).continuation ^
      (Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) -
        visitPosition U (G.incoming c (otherBranch i))))
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) =
      smoothArcEquiv G (Sum.inl (G.incoming c i)) := by
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hd1_lt : visitPosition U (G.incoming c (otherBranch i)) <
      Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) := by
    have h := visitPosition_lt_card U (G.incoming c (otherBranch i))
    rwa [hcomp_d1] at h
  have hd1_rec : (G.continuation ^ visitPosition U (G.incoming c (otherBranch i)))
      (G.incoming c i) = G.incoming c (otherBranch i) := by
    have h := visitPosition_reconstruct U (G.incoming c (otherBranch i))
    rwa [hcomp_d1, hroot] at h
  have hpow := smooth_pow_eq_of_disjoint G x (G.incoming c (otherBranch i))
    (Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) -
      visitPosition U (G.incoming c (otherBranch i)))
    (fun s hs j => bot_pow_d1_ne_incoming G U c hself i hroot x hx s (le_of_lt hs) j)
    (Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) -
      visitPosition U (G.incoming c (otherBranch i))) le_rfl
  let L := Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) -
    visitPosition U (G.incoming c (otherBranch i))
  have hL_d0 : (G.continuation ^ L) (G.incoming c (otherBranch i)) = G.incoming c i := by
    have hsum : L + visitPosition U (G.incoming c (otherBranch i)) =
        Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) := by
      omega
    calc
      (G.continuation ^ L) (G.incoming c (otherBranch i))
        = (G.continuation ^ L)
            ((G.continuation ^ visitPosition U (G.incoming c (otherBranch i)))
              (G.incoming c i)) := by rw [hd1_rec]
      _ = (G.continuation ^ (L + visitPosition U (G.incoming c (otherBranch i))))
            (G.incoming c i) := by rw [pow_add, Perm.mul_apply]
      _ = (G.continuation ^
            Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))))
            (G.incoming c i) := by rw [hsum]
      _ = G.incoming c i := pow_card_fibre_apply G.continuation (G.incoming c i)
  rw [hpow, hL_d0]

theorem bot_aboveComp_pow_ne (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (C : diagramComponent G)
    (hgt : U.componentIndex (componentOf G.continuation (G.incoming c i)) <
      U.componentIndex C)
    (t : ℕ) (j : Fin 2) :
    (G.continuation ^ t) (U.baseArc C).val ≠ G.incoming x j := by
  intro h
  have hcomp : componentOf G.continuation ((G.continuation ^ t) (U.baseArc C).val) = C :=
    (componentOf_pow_apply G.continuation t (U.baseArc C).val).trans (U.baseArc C).property
  have hprot : BotProtected G U c i ((G.continuation ^ t) (U.baseArc C).val) :=
    botProtected_of_component_gt G U c hself i _ (by rw [hcomp]; exact hgt)
  exact hx j (h ▸ hprot)

theorem bot_componentOf_smooth_eq_base (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : BotProtected G U c i a) :
    componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a)) =
      componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (U.baseArc (componentOf G.continuation a)).val)) := by
  have hge := botProtected_component_ge G U c hself i a ha
  rcases lt_or_eq_of_le hge with hgt | hEq_idx
  · have hpow := smooth_pow_eq_of_disjoint G x
      (U.baseArc (componentOf G.continuation a)).val (visitPosition U a)
      (fun t _ j => bot_aboveComp_pow_ne G U c hself i x hx (componentOf G.continuation a) hgt t j)
      (visitPosition U a) le_rfl
    rw [visitPosition_reconstruct U a] at hpow
    rw [← hpow]
    exact componentOf_pow_apply (smoothCrossing G x).continuation (visitPosition U a) _
  · have hEq_C : componentOf G.continuation a =
        componentOf G.continuation (G.incoming c i) :=
      U.componentIndex.injective hEq_idx.symm
    have hbase_d0 : (U.baseArc (componentOf G.continuation a)).val = G.incoming c i := by
      rw [hEq_C, hroot]
    rw [hbase_d0]
    by_cases ha0 : a = G.incoming c i
    · rw [ha0]
    · have hle_d1 : visitPosition U (G.incoming c (otherBranch i)) ≤ visitPosition U a :=
        (botProtected_same_component_iff G U c hself i a hEq_C ha0).mp ha
      let N := Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i)))
      let L := N - visitPosition U (G.incoming c (otherBranch i))
      have ha_lt : visitPosition U a < N := by
        have h := visitPosition_lt_card U a
        rwa [hEq_C] at h
      let s := visitPosition U a - visitPosition U (G.incoming c (otherBranch i))
      have hs_le : s ≤ L := by omega
      have hd1_rec : (G.continuation ^ visitPosition U (G.incoming c (otherBranch i)))
          (G.incoming c i) = G.incoming c (otherBranch i) := by
        have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
            componentOf G.continuation (G.incoming c i) :=
          (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
        have h := visitPosition_reconstruct U (G.incoming c (otherBranch i))
        rwa [hcomp_d1, hroot] at h
      have ha_rec : (G.continuation ^ visitPosition U a) (G.incoming c i) = a := by
        have h := visitPosition_reconstruct U a
        rwa [hEq_C, hroot] at h
      have hs_eq : (G.continuation ^ s) (G.incoming c (otherBranch i)) = a := by
        have hsum : s + visitPosition U (G.incoming c (otherBranch i)) = visitPosition U a := by
          omega
        calc
          (G.continuation ^ s) (G.incoming c (otherBranch i))
            = (G.continuation ^ s)
                ((G.continuation ^ visitPosition U (G.incoming c (otherBranch i)))
                  (G.incoming c i)) := by rw [hd1_rec]
          _ = (G.continuation ^ (s + visitPosition U (G.incoming c (otherBranch i))))
                (G.incoming c i) := by rw [pow_add, Perm.mul_apply]
          _ = (G.continuation ^ visitPosition U a) (G.incoming c i) := by rw [hsum]
          _ = a := ha_rec
      have hpow_s := smooth_pow_eq_of_disjoint G x (G.incoming c (otherBranch i)) L
        (fun t ht j => bot_pow_d1_ne_incoming G U c hself i hroot x hx t (le_of_lt ht) j)
        s hs_le
      rw [hs_eq] at hpow_s
      have hL_d0 := bot_pow_L_eq_d0 G U c hself i hroot x hx
      calc
        componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a))
          = componentOf (smoothCrossing G x).continuation
              (((smoothCrossing G x).continuation ^ s)
                (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))) := by
            rw [hpow_s]
        _ = componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) :=
            componentOf_pow_apply _ s _
        _ = componentOf (smoothCrossing G x).continuation
              (((smoothCrossing G x).continuation ^ L)
                (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))) :=
            (componentOf_pow_apply _ L _).symm
        _ = componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
            rw [hL_d0]

theorem bot_smooth_self (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j)) :
    let c' := smoothCrossingEquiv G x ⟨c, bot_ne_self G U c i x hx⟩
    (smoothCrossing G x).continuation.SameCycle
      ((smoothCrossing G x).incoming c' 0) ((smoothCrossing G x).incoming c' 1) := by
  intro c'
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hsm := bot_componentOf_smooth_eq_base G U c hself i hroot x hx
    (G.incoming c (otherBranch i)) (botProtected_d1 G U c i)
  rw [hcomp_d1, hroot] at hsm
  have hsc : (smoothCrossing G x).continuation.SameCycle
      (smoothArcEquiv G (Sum.inl (G.incoming c i)))
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) :=
    (componentOf_eq_iff _ _ _).mp hsm.symm
  rw [smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) 0,
      smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) 1]
  fin_cases i
  · exact hsc
  · exact hsc.symm

def IsBotAboveComp (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (C : diagramComponent G) (C' : diagramComponent (smoothCrossing G x)) : Prop :=
  U.componentIndex (componentOf G.continuation (G.incoming c i)) < U.componentIndex C ∧
    componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (U.baseArc C).val)) = C'

theorem isBotAboveComp_unique (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    {C₁ C₂ : diagramComponent G} {C' : diagramComponent (smoothCrossing G x)}
    (h₁ : IsBotAboveComp G U c i x C₁ C') (h₂ : IsBotAboveComp G U c i x C₂ C') :
    C₁ = C₂ := by
  have hiff := smooth_sameCycle_unaffected_iff G x (U.baseArc C₁).val
    (bot_aboveComp_pow_ne G U c hself i x hx C₁ h₁.1)
    (smoothArcEquiv G (Sum.inl (U.baseArc C₂).val))
  obtain ⟨b, hb_comp, hb_eq⟩ := hiff.mp (h₂.2.trans h₁.2.symm)
  have hval : (U.baseArc C₂).val = b := Sum.inl.inj ((smoothArcEquiv G).injective hb_eq)
  calc
    C₁ = componentOf G.continuation (U.baseArc C₁).val := (U.baseArc C₁).property.symm
    _ = componentOf G.continuation b := hb_comp.symm
    _ = componentOf G.continuation (U.baseArc C₂).val := by rw [hval]
    _ = C₂ := (U.baseArc C₂).property

theorem isBotAboveComp_ne_d0 (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    {C : diagramComponent G} {C' : diagramComponent (smoothCrossing G x)}
    (h : IsBotAboveComp G U c i x C C') :
    C' ≠ componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
  intro hEq
  have hiff := smooth_sameCycle_unaffected_iff G x (U.baseArc C).val
    (bot_aboveComp_pow_ne G U c hself i x hx C h.1)
    (smoothArcEquiv G (Sum.inl (G.incoming c i)))
  obtain ⟨b, hb_comp, hb_eq⟩ := hiff.mp (hEq.symm.trans h.2.symm)
  have hval : G.incoming c i = b := Sum.inl.inj ((smoothArcEquiv G).injective hb_eq)
  have hC : componentOf G.continuation (G.incoming c i) = C := by
    rw [hval, hb_comp, (U.baseArc C).property]
  exact (ne_of_lt h.1) (congrArg U.componentIndex hC)

noncomputable def botSmoothWeight (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (C' : diagramComponent (smoothCrossing G x)) : ℕ :=
  if h : ∃ C, IsBotAboveComp G U c i x C C' then
    1 + (U.componentIndex (Classical.choose h)).val
  else if C' = componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) then
    1 + (U.componentIndex (componentOf G.continuation (G.incoming c i))).val
  else
    0

noncomputable def botSmoothBaseArc (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing)
    (C' : diagramComponent (smoothCrossing G x)) :
    {e : Fin (smoothCrossing G x).nArc //
      componentOf (smoothCrossing G x).continuation e = C'} :=
  if h : ∃ C, IsBotAboveComp G U c i x C C' then
    ⟨smoothArcEquiv G (Sum.inl (U.baseArc (Classical.choose h)).val),
      (Classical.choose_spec h).2⟩
  else if h0 : C' = componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) then
    ⟨smoothArcEquiv G (Sum.inl (G.incoming c i)), h0.symm⟩
  else
    Classical.choice (fibreNonempty (smoothCrossing G x).continuation C')

noncomputable def botSmoothTraversal (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2) (x : Fin G.nCrossing) :
    BasedTraversal (smoothCrossing G x) where
  componentIndex := equivFinOfWeight (botSmoothWeight G U c i x)
  baseArc := botSmoothBaseArc G U c i x

theorem botSmoothBaseArc_of_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : BotProtected G U c i a) :
    ((botSmoothTraversal G U c i x).baseArc
      (componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a)))).val =
      smoothArcEquiv G (Sum.inl (U.baseArc (componentOf G.continuation a)).val) := by
  let C := componentOf G.continuation a
  let C' := componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a))
  have hC' : componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (U.baseArc C).val)) = C' :=
    (bot_componentOf_smooth_eq_base G U c hself i hroot x hx a ha).symm
  have hge := botProtected_component_ge G U c hself i a ha
  change (botSmoothBaseArc G U c i x C').val = _
  unfold botSmoothBaseArc
  by_cases hgt : U.componentIndex (componentOf G.continuation (G.incoming c i)) <
      U.componentIndex C
  · have hex : ∃ C₀, IsBotAboveComp G U c i x C₀ C' := ⟨C, hgt, hC'⟩
    rw [dif_pos hex]
    have huniq := isBotAboveComp_unique G U c hself i x hx
      (Classical.choose_spec hex) ⟨hgt, hC'⟩
    dsimp
    rw [huniq]
  · have hEq_idx : U.componentIndex C =
        U.componentIndex (componentOf G.continuation (G.incoming c i)) :=
      le_antisymm (not_lt.mp hgt) hge
    have hEq_C : C = componentOf G.continuation (G.incoming c i) :=
      U.componentIndex.injective hEq_idx
    have hbase_d0 : (U.baseArc C).val = G.incoming c i := by rw [hEq_C, hroot]
    have hC'_d0 : C' = componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
      rw [← hC', hbase_d0]
    have hnot : ¬ ∃ C₀, IsBotAboveComp G U c i x C₀ C' := by
      rintro ⟨C₀, hC₀⟩
      exact isBotAboveComp_ne_d0 G U c hself i x hx hC₀ hC'_d0
    rw [dif_neg hnot, dif_pos hC'_d0, hbase_d0]

theorem botSmooth_root (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j)) :
    let U' := botSmoothTraversal G U c i x
    let c' := smoothCrossingEquiv G x ⟨c, bot_ne_self G U c i x hx⟩
    (U'.baseArc (componentOf (smoothCrossing G x).continuation
      ((smoothCrossing G x).incoming c' i))).val =
      (smoothCrossing G x).incoming c' i := by
  intro U' c'
  rw [smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) i]
  have hb := botSmoothBaseArc_of_protected G U c hself i hroot x hx
    (G.incoming c i) (botProtected_d0 G U c i)
  rw [hroot] at hb
  exact hb

theorem botSmoothWeight_of_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : BotProtected G U c i a) :
    botSmoothWeight G U c i x
      (componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a))) =
      1 + (U.componentIndex (componentOf G.continuation a)).val := by
  let C := componentOf G.continuation a
  let C' := componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl a))
  have hC' : componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (U.baseArc C).val)) = C' :=
    (bot_componentOf_smooth_eq_base G U c hself i hroot x hx a ha).symm
  have hge := botProtected_component_ge G U c hself i a ha
  unfold botSmoothWeight
  by_cases hgt : U.componentIndex (componentOf G.continuation (G.incoming c i)) <
      U.componentIndex C
  · have hex : ∃ C₀, IsBotAboveComp G U c i x C₀ C' := ⟨C, hgt, hC'⟩
    rw [dif_pos hex]
    have huniq := isBotAboveComp_unique G U c hself i x hx
      (Classical.choose_spec hex) ⟨hgt, hC'⟩
    rw [huniq]
  · have hEq_idx : U.componentIndex C =
        U.componentIndex (componentOf G.continuation (G.incoming c i)) :=
      le_antisymm (not_lt.mp hgt) hge
    have hEq_C : C = componentOf G.continuation (G.incoming c i) :=
      U.componentIndex.injective hEq_idx
    have hbase_d0 : (U.baseArc C).val = G.incoming c i := by rw [hEq_C, hroot]
    have hC'_d0 : C' = componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
      rw [← hC', hbase_d0]
    have hnot : ¬ ∃ C₀, IsBotAboveComp G U c i x C₀ C' := by
      rintro ⟨C₀, hC₀⟩
      exact isBotAboveComp_ne_d0 G U c hself i x hx hC₀ hC'_d0
    rw [dif_neg hnot, if_pos hC'_d0]
    exact congrArg (1 + ·) (congrArg Fin.val hEq_idx.symm)

theorem botSmooth_visitPosition_of_above (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (a : Fin G.nArc)
    (hgt : U.componentIndex (componentOf G.continuation (G.incoming c i)) <
      U.componentIndex (componentOf G.continuation a)) :
    visitPosition (botSmoothTraversal G U c i x) (smoothArcEquiv G (Sum.inl a)) =
      visitPosition U a := by
  let C := componentOf G.continuation a
  have ha : BotProtected G U c i a := botProtected_of_component_gt G U c hself i a hgt
  have hbase_E := botSmoothBaseArc_of_protected G U c hself i hroot x hx a ha
  have hcomp_E := bot_componentOf_smooth_eq_base G U c hself i hroot x hx a ha
  have hpow := smooth_pow_eq_of_disjoint G x (U.baseArc C).val (visitPosition U a)
    (fun t _ j => bot_aboveComp_pow_ne G U c hself i x hx C hgt t j)
    (visitPosition U a) le_rfl
  rw [visitPosition_reconstruct U a] at hpow
  have hbase_root : ((botSmoothTraversal G U c i x).baseArc
      (componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (U.baseArc C).val)))).val =
      smoothArcEquiv G (Sum.inl (U.baseArc C).val) := by
    rw [← hcomp_E]
    exact hbase_E
  have hlt_sm := card_fibre_smooth_gt_of_pow_disjoint G x (U.baseArc C).val (visitPosition U a)
    (by rw [(U.baseArc C).property]; exact visitPosition_lt_card U a)
    (fun t _ j => bot_aboveComp_pow_ne G U c hself i x hx C hgt t j)
  exact visitPosition_eq_of_pow (botSmoothTraversal G U c i x)
    (smoothArcEquiv G (Sum.inl (U.baseArc C).val))
    (smoothArcEquiv G (Sum.inl a))
    (visitPosition U a) hbase_root hlt_sm hpow

theorem botSmooth_visitPosition_add_lt_card (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (s : ℕ)
    (hs : s < Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i))) -
        visitPosition U (G.incoming c (otherBranch i))) :
    let U' := botSmoothTraversal G U c i x
    visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + s <
      Fintype.card (Fibre (smoothCrossing G x).continuation
        (componentOf (smoothCrossing G x).continuation
          (smoothArcEquiv G (Sum.inl (G.incoming c i))))) := by
  intro U'
  let N := Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i)))
  let L := N - visitPosition U (G.incoming c (otherBranch i))
  let N' := Fintype.card (Fibre (smoothCrossing G x).continuation
    (componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i)))))
  have hcomp_d1_G : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hcomp_d1_E : componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) =
      componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
    have h := bot_componentOf_smooth_eq_base G U c hself i hroot x hx
      (G.incoming c (otherBranch i)) (botProtected_d1 G U c i)
    rwa [hcomp_d1_G, hroot] at h
  have hd1'_lt : visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) <
      N' := by
    have h := visitPosition_lt_card U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))
    rwa [hcomp_d1_E] at h
  by_contra hge
  have hge' : N' ≤ visitPosition U'
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + s :=
    not_lt.mp hge
  let s₀ := N' - visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))
  have hs₀_pos : 0 < s₀ := by omega
  have hs₀_lt : s₀ < L := by omega
  have hsum_N' : visitPosition U'
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + s₀ = N' := by omega
  have hbase_d0 : (U'.baseArc (componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i))))).val =
      smoothArcEquiv G (Sum.inl (G.incoming c i)) := by
    have h := botSmoothBaseArc_of_protected G U c hself i hroot x hx
      (G.incoming c i) (botProtected_d0 G U c i)
    rwa [hroot] at h
  have hd1'_rec : ((smoothCrossing G x).continuation ^
      visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))))
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) =
      smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))) := by
    have h := visitPosition_reconstruct U'
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))
    rwa [hcomp_d1_E, hbase_d0] at h
  have hpow_s₀ := smooth_pow_eq_of_disjoint G x (G.incoming c (otherBranch i)) L
    (fun t ht j => bot_pow_d1_ne_incoming G U c hself i hroot x hx t (le_of_lt ht) j)
    s₀ (le_of_lt hs₀_lt)
  have hEq_d0' : smoothArcEquiv G
      (Sum.inl ((G.continuation ^ s₀) (G.incoming c (otherBranch i)))) =
      smoothArcEquiv G (Sum.inl (G.incoming c i)) := by
    have hsum_N'2 : s₀ + visitPosition U'
        (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) = N' := by omega
    calc
      smoothArcEquiv G (Sum.inl ((G.continuation ^ s₀) (G.incoming c (otherBranch i))))
        = ((smoothCrossing G x).continuation ^ s₀)
            (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) := hpow_s₀.symm
      _ = ((smoothCrossing G x).continuation ^ s₀)
            (((smoothCrossing G x).continuation ^
              visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))))
              (smoothArcEquiv G (Sum.inl (G.incoming c i)))) := by rw [hd1'_rec]
      _ = ((smoothCrossing G x).continuation ^
            (s₀ + visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))))
            (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by rw [pow_add, Perm.mul_apply]
      _ = ((smoothCrossing G x).continuation ^ N')
            (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by rw [hsum_N'2]
      _ = smoothArcEquiv G (Sum.inl (G.incoming c i)) :=
            pow_card_fibre_apply (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl (G.incoming c i)))
  have hEq_d0 : (G.continuation ^ s₀) (G.incoming c (otherBranch i)) = G.incoming c i :=
    Sum.inl.inj ((smoothArcEquiv G).injective hEq_d0')
  have hd1_rec : (G.continuation ^ visitPosition U (G.incoming c (otherBranch i)))
      (G.incoming c i) = G.incoming c (otherBranch i) := by
    have h := visitPosition_reconstruct U (G.incoming c (otherBranch i))
    rwa [hcomp_d1_G, hroot] at h
  have hpow_G : (G.continuation ^ (visitPosition U (G.incoming c (otherBranch i)) + s₀))
      (G.incoming c i) = G.incoming c i := by
    rw [add_comm, pow_add, Perm.mul_apply, hd1_rec, hEq_d0]
  have hd1_lt_N : visitPosition U (G.incoming c (otherBranch i)) < N := by
    have h := visitPosition_lt_card U (G.incoming c (otherBranch i))
    rwa [hcomp_d1_G] at h
  have hsum_lt_N : visitPosition U (G.incoming c (otherBranch i)) + s₀ < N := by omega
  have hvp_d0 := visitPosition_eq_of_pow U (G.incoming c i) (G.incoming c i)
    (visitPosition U (G.incoming c (otherBranch i)) + s₀) hroot hsum_lt_N hpow_G
  have hvp_0 := visitPosition_root_eq_zero G U (G.incoming c i) hroot
  omega

theorem botSmooth_visitPosition_of_same_component (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (a : Fin G.nArc) (ha : BotProtected G U c i a)
    (hcomp : componentOf G.continuation a = componentOf G.continuation (G.incoming c i))
    (hne : a ≠ G.incoming c i) :
    let U' := botSmoothTraversal G U c i x
    visitPosition U' (smoothArcEquiv G (Sum.inl a)) =
      visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) +
        (visitPosition U a - visitPosition U (G.incoming c (otherBranch i))) := by
  intro U'
  let N := Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i)))
  let L := N - visitPosition U (G.incoming c (otherBranch i))
  have hle_d1 : visitPosition U (G.incoming c (otherBranch i)) ≤ visitPosition U a :=
    (botProtected_same_component_iff G U c hself i a hcomp hne).mp ha
  have ha_lt : visitPosition U a < N := by
    have h := visitPosition_lt_card U a
    rwa [hcomp] at h
  let s := visitPosition U a - visitPosition U (G.incoming c (otherBranch i))
  have hs_lt : s < L := by omega
  have hcomp_d1_G : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hd1_rec : (G.continuation ^ visitPosition U (G.incoming c (otherBranch i)))
      (G.incoming c i) = G.incoming c (otherBranch i) := by
    have h := visitPosition_reconstruct U (G.incoming c (otherBranch i))
    rwa [hcomp_d1_G, hroot] at h
  have ha_rec : (G.continuation ^ visitPosition U a) (G.incoming c i) = a := by
    have h := visitPosition_reconstruct U a
    rwa [hcomp, hroot] at h
  have hs_eq : (G.continuation ^ s) (G.incoming c (otherBranch i)) = a := by
    have hsum : s + visitPosition U (G.incoming c (otherBranch i)) = visitPosition U a := by
      omega
    calc
      (G.continuation ^ s) (G.incoming c (otherBranch i))
        = (G.continuation ^ s)
            ((G.continuation ^ visitPosition U (G.incoming c (otherBranch i)))
              (G.incoming c i)) := by rw [hd1_rec]
      _ = (G.continuation ^ (s + visitPosition U (G.incoming c (otherBranch i))))
            (G.incoming c i) := by rw [pow_add, Perm.mul_apply]
      _ = (G.continuation ^ visitPosition U a) (G.incoming c i) := by rw [hsum]
      _ = a := ha_rec
  have hpow_s := smooth_pow_eq_of_disjoint G x (G.incoming c (otherBranch i)) L
    (fun t ht j => bot_pow_d1_ne_incoming G U c hself i hroot x hx t (le_of_lt ht) j)
    s (le_of_lt hs_lt)
  rw [hs_eq] at hpow_s
  have hcomp_d1_E : componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) =
      componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
    have h := bot_componentOf_smooth_eq_base G U c hself i hroot x hx
      (G.incoming c (otherBranch i)) (botProtected_d1 G U c i)
    rwa [hcomp_d1_G, hroot] at h
  have hbase_d0 : (U'.baseArc (componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c i))))).val =
      smoothArcEquiv G (Sum.inl (G.incoming c i)) := by
    have h := botSmoothBaseArc_of_protected G U c hself i hroot x hx
      (G.incoming c i) (botProtected_d0 G U c i)
    rwa [hroot] at h
  have hd1'_rec : ((smoothCrossing G x).continuation ^
      visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))))
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) =
      smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))) := by
    have h := visitPosition_reconstruct U'
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))
    rwa [hcomp_d1_E, hbase_d0] at h
  have hpow_E : ((smoothCrossing G x).continuation ^
      (visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + s))
      (smoothArcEquiv G (Sum.inl (G.incoming c i))) = smoothArcEquiv G (Sum.inl a) := by
    rw [add_comm, pow_add, Perm.mul_apply, hd1'_rec, hpow_s]
  have hlt_N' := botSmooth_visitPosition_add_lt_card G U c hself i hroot x hx s hs_lt
  exact visitPosition_eq_of_pow U'
    (smoothArcEquiv G (Sum.inl (G.incoming c i)))
    (smoothArcEquiv G (Sum.inl a))
    (visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + s)
    hbase_d0 hlt_N' hpow_E

theorem botSmooth_rankBefore_d1_of_not_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (z : Fin (smoothCrossing G x).nArc)
    (hz : ∀ a : Fin G.nArc, BotProtected G U c i a →
      z ≠ (smoothArcEquiv G (Sum.inl a) : Fin (smoothCrossing G x).nArc)) :
    let U' := botSmoothTraversal G U c i x
    rankBefore (visitRank U' z)
      (visitRank U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))) := by
  intro U'
  have hd0 : BotProtected G U c i (G.incoming c i) := botProtected_d0 G U c i
  have hd1 : BotProtected G U c i (G.incoming c (otherBranch i)) := botProtected_d1 G U c i
  have hcomp_d1_G : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  have hcomp_d1_E : componentOf (smoothCrossing G x).continuation
      (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) =
      componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by
    have h := bot_componentOf_smooth_eq_base G U c hself i hroot x hx
      (G.incoming c (otherBranch i)) hd1
    rwa [hcomp_d1_G, hroot] at h
  by_cases hz_comp : componentOf (smoothCrossing G x).continuation z =
      componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i)))
  · right
    refine ⟨by change U'.componentIndex _ = U'.componentIndex _; rw [hz_comp, hcomp_d1_E], ?_⟩
    change visitPosition U' z <
      visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))
    by_contra hge
    have hle : visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) ≤
        visitPosition U' z :=
      not_lt.mp hge
    let N := Fintype.card (Fibre G.continuation (componentOf G.continuation (G.incoming c i)))
    let L := N - visitPosition U (G.incoming c (otherBranch i))
    let N' := Fintype.card (Fibre (smoothCrossing G x).continuation
      (componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i)))))
    have hz_lt_N' : visitPosition U' z < N' := by
      have h := visitPosition_lt_card U' z
      rwa [hz_comp] at h
    have hbase_d0 : (U'.baseArc (componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c i))))).val =
        smoothArcEquiv G (Sum.inl (G.incoming c i)) := by
      have h := botSmoothBaseArc_of_protected G U c hself i hroot x hx (G.incoming c i) hd0
      rwa [hroot] at h
    have hd1'_rec : ((smoothCrossing G x).continuation ^
        visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))))
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) =
        smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))) := by
      have h := visitPosition_reconstruct U'
        (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))
      rwa [hcomp_d1_E, hbase_d0] at h
    have hz_rec : ((smoothCrossing G x).continuation ^ visitPosition U' z)
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) = z := by
      have h := visitPosition_reconstruct U' z
      rwa [hz_comp, hbase_d0] at h
    let s := visitPosition U' z -
      visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))
    have hs_rec : ((smoothCrossing G x).continuation ^ s)
        (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) = z := by
      have hsum : s + visitPosition U'
          (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) =
          visitPosition U' z := by omega
      calc
        ((smoothCrossing G x).continuation ^ s)
            (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))
          = ((smoothCrossing G x).continuation ^ s)
              (((smoothCrossing G x).continuation ^
                visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))))
                (smoothArcEquiv G (Sum.inl (G.incoming c i)))) := by rw [hd1'_rec]
        _ = ((smoothCrossing G x).continuation ^
              (s + visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i))))))
              (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by rw [pow_add, Perm.mul_apply]
        _ = ((smoothCrossing G x).continuation ^ visitPosition U' z)
              (smoothArcEquiv G (Sum.inl (G.incoming c i))) := by rw [hsum]
        _ = z := hz_rec
    have hs_lt_L : s < L := by
      by_contra hge_L
      have hle_L : L ≤ s := not_lt.mp hge_L
      have hsum_gt : visitPosition U'
          (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + L ≤
          visitPosition U' z := by
        omega
      have hlt_L : visitPosition U'
          (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + L < N' :=
        lt_of_le_of_lt hsum_gt hz_lt_N'
      have hL_d0 := bot_pow_L_eq_d0 G U c hself i hroot x hx
      have hpow_L_d0 : ((smoothCrossing G x).continuation ^
          (visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + L))
          (smoothArcEquiv G (Sum.inl (G.incoming c i))) =
          smoothArcEquiv G (Sum.inl (G.incoming c i)) := by
        rw [add_comm, pow_add, Perm.mul_apply, hd1'_rec, hL_d0]
      have hvp_d0' := visitPosition_eq_of_pow U'
        (smoothArcEquiv G (Sum.inl (G.incoming c i)))
        (smoothArcEquiv G (Sum.inl (G.incoming c i)))
        (visitPosition U' (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) + L)
        hbase_d0 hlt_L hpow_L_d0
      have hvp_0' := visitPosition_root_eq_zero (smoothCrossing G x) U'
        (smoothArcEquiv G (Sum.inl (G.incoming c i))) hbase_d0
      have hd1_lt_N : visitPosition U (G.incoming c (otherBranch i)) < N := by
        have h := visitPosition_lt_card U (G.incoming c (otherBranch i))
        rwa [hcomp_d1_G] at h
      omega
    have hpow_s := smooth_pow_eq_of_disjoint G x (G.incoming c (otherBranch i)) L
      (fun t ht j => bot_pow_d1_ne_incoming G U c hself i hroot x hx t (le_of_lt ht) j)
      s (le_of_lt hs_lt_L)
    have hz_eq : z = smoothArcEquiv G
        (Sum.inl ((G.continuation ^ s) (G.incoming c (otherBranch i)))) :=
      hs_rec.symm.trans hpow_s
    exact hz ((G.continuation ^ s) (G.incoming c (otherBranch i)))
      (botProtected_of_pow_d1 G U c hself i hroot s (le_of_lt hs_lt_L)) hz_eq
  · left
    change U'.componentIndex (componentOf (smoothCrossing G x).continuation z) <
      U'.componentIndex (componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))))
    apply equivFinOfWeight_lt_of_lt (botSmoothWeight G U c i x)
    rw [botSmoothWeight_of_protected G U c hself i hroot x hx (G.incoming c (otherBranch i)) hd1,
      hcomp_d1_G]
    have hnot_above : ¬ ∃ C, IsBotAboveComp G U c i x C
        (componentOf (smoothCrossing G x).continuation z) := by
      rintro ⟨C, hgt, hC'⟩
      have hiff := smooth_sameCycle_unaffected_iff G x (U.baseArc C).val
        (bot_aboveComp_pow_ne G U c hself i x hx C hgt) z
      obtain ⟨b, hb_comp, hb_eq⟩ := hiff.mp hC'.symm
      rw [(U.baseArc C).property] at hb_comp
      have hb_prot : BotProtected G U c i b :=
        botProtected_of_component_gt G U c hself i b (by rw [hb_comp]; exact hgt)
      exact hz b hb_prot hb_eq
    unfold botSmoothWeight
    rw [dif_neg hnot_above, if_neg hz_comp]
    omega

theorem botSmooth_protected_iff (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (z : Fin (smoothCrossing G x).nArc) :
    let c' := smoothCrossingEquiv G x ⟨c, bot_ne_self G U c i x hx⟩
    BotProtected (smoothCrossing G x) (botSmoothTraversal G U c i x) c' i z ↔
      ∃ a : Fin G.nArc, BotProtected G U c i a ∧
        z = (smoothArcEquiv G (Sum.inl a) : Fin (smoothCrossing G x).nArc) := by
  intro c'
  let U' := botSmoothTraversal G U c i x
  let d0 := G.incoming c i
  let d1 := G.incoming c (otherBranch i)
  have hd0_sm : (smoothCrossing G x).incoming c' i = smoothArcEquiv G (Sum.inl d0) :=
    smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) i
  have hd1_sm : (smoothCrossing G x).incoming c' (otherBranch i) = smoothArcEquiv G (Sum.inl d1) :=
    smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) (otherBranch i)
  constructor
  · intro hz
    by_contra hnot
    have hnot' : ∀ a : Fin G.nArc, BotProtected G U c i a →
        z ≠ (smoothArcEquiv G (Sum.inl a) : Fin (smoothCrossing G x).nArc) :=
      fun a ha hEq => hnot ⟨a, ha, hEq⟩
    have hlt_d1 := botSmooth_rankBefore_d1_of_not_protected G U c hself i hroot x hx z hnot'
    unfold BotProtected at hz
    rw [hd0_sm, hd1_sm] at hz
    rcases hz with hEq0 | hEq1 | hgt_d1
    · exact hnot' d0 (botProtected_d0 G U c i) hEq0
    · exact hnot' d1 (botProtected_d1 G U c i) hEq1
    · exact rankBefore_asymm hlt_d1 hgt_d1
  · rintro ⟨a, ha, rfl⟩
    unfold BotProtected
    rw [hd0_sm, hd1_sm]
    by_cases ha0 : a = d0
    · left; rw [ha0]
    · by_cases ha1 : a = d1
      · right; left; rw [ha1]
      · right; right
        have hcomp_d1_G : componentOf G.continuation d1 = componentOf G.continuation d0 :=
          (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
        have hcomp_d1_E : componentOf (smoothCrossing G x).continuation
            (smoothArcEquiv G (Sum.inl d1)) =
            componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl d0)) := by
          have h := bot_componentOf_smooth_eq_base G U c hself i hroot x hx d1 (botProtected_d1 G U c i)
          rwa [hcomp_d1_G, hroot] at h
        have hge := botProtected_component_ge G U c hself i a ha
        rcases lt_or_eq_of_le hge with hgt | hEq_idx
        · left
          change U'.componentIndex (componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl d1))) <
            U'.componentIndex (componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl a)))
          apply equivFinOfWeight_lt_of_lt (botSmoothWeight G U c i x)
          rw [botSmoothWeight_of_protected G U c hself i hroot x hx d1 (botProtected_d1 G U c i),
              botSmoothWeight_of_protected G U c hself i hroot x hx a ha, hcomp_d1_G]
          exact Nat.add_lt_add_left hgt 1
        · right
          have hEq_C : componentOf G.continuation a = componentOf G.continuation d0 :=
            U.componentIndex.injective hEq_idx.symm
          have hcomp_a_E : componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl a)) =
              componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl d0)) := by
            have h := bot_componentOf_smooth_eq_base G U c hself i hroot x hx a ha
            rwa [hEq_C, hroot] at h
          refine ⟨by change U'.componentIndex _ = U'.componentIndex _; rw [hcomp_d1_E, hcomp_a_E], ?_⟩
          change visitPosition (botSmoothTraversal G U c i x)
              (smoothArcEquiv G (Sum.inl (G.incoming c (otherBranch i)))) <
            visitPosition (botSmoothTraversal G U c i x) (smoothArcEquiv G (Sum.inl a))
          rw [botSmooth_visitPosition_of_same_component G U c hself i hroot x hx a ha hEq_C ha0]
          have hle_vp := (botProtected_same_component_iff G U c hself i a hEq_C ha0).mp ha
          have hne_vp : visitPosition U (G.incoming c (otherBranch i)) ≠ visitPosition U a := by
            intro hEq_vp
            exact ha1 (visitRank_injective U
              (Prod.ext (congrArg U.componentIndex (hEq_C.trans hcomp_d1_G.symm)) hEq_vp.symm))
          omega

theorem botSmooth_rankBefore_iff_of_protected (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j))
    (a b : Fin G.nArc)
    (ha0 : a ≠ G.incoming c i) (hb0 : b ≠ G.incoming c i)
    (hab : BotProtected G U c i a ∨ BotProtected G U c i b) :
    let U' := botSmoothTraversal G U c i x
    rankBefore (visitRank U' (smoothArcEquiv G (Sum.inl a)))
      (visitRank U' (smoothArcEquiv G (Sum.inl b))) ↔
      rankBefore (visitRank U a) (visitRank U b) := by
  intro U'
  let d0 := G.incoming c i
  let d1 := G.incoming c (otherBranch i)
  have hcomp_d1_G : componentOf G.continuation d1 = componentOf G.continuation d0 :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  by_cases ha : BotProtected G U c i a
  · by_cases hb : BotProtected G U c i b
    · have hwa := botSmoothWeight_of_protected G U c hself i hroot x hx a ha
      have hwb := botSmoothWeight_of_protected G U c hself i hroot x hx b hb
      by_cases hcomp : componentOf G.continuation a = componentOf G.continuation b
      · have hcomp_E : componentOf (smoothCrossing G x).continuation
            (smoothArcEquiv G (Sum.inl a)) =
            componentOf (smoothCrossing G x).continuation (smoothArcEquiv G (Sum.inl b)) := by
          rw [bot_componentOf_smooth_eq_base G U c hself i hroot x hx a ha,
              bot_componentOf_smooth_eq_base G U c hself i hroot x hx b hb, hcomp]
        unfold rankBefore visitRank
        dsimp
        rw [hcomp, hcomp_E]
        simp only [lt_irrefl, true_and, false_or]
        have hge_a := botProtected_component_ge G U c hself i a ha
        rcases lt_or_eq_of_le hge_a with hgt_a | hEq_a
        · have hgt_b : U.componentIndex (componentOf G.continuation d0) <
              U.componentIndex (componentOf G.continuation b) := by
            rwa [← hcomp]
          rw [botSmooth_visitPosition_of_above G U c hself i hroot x hx a hgt_a,
              botSmooth_visitPosition_of_above G U c hself i hroot x hx b hgt_b]
        · have hEq_Ca : componentOf G.continuation a = componentOf G.continuation d0 :=
            U.componentIndex.injective hEq_a.symm
          have hEq_Cb : componentOf G.continuation b = componentOf G.continuation d0 :=
            hcomp.symm.trans hEq_Ca
          rw [botSmooth_visitPosition_of_same_component G U c hself i hroot x hx a ha hEq_Ca ha0,
              botSmooth_visitPosition_of_same_component G U c hself i hroot x hx b hb hEq_Cb hb0]
          have hle_a := (botProtected_same_component_iff G U c hself i a hEq_Ca ha0).mp ha
          have hle_b := (botProtected_same_component_iff G U c hself i b hEq_Cb hb0).mp hb
          omega
      · have hne_idx : U.componentIndex (componentOf G.continuation a) ≠
            U.componentIndex (componentOf G.continuation b) :=
          fun h => hcomp (U.componentIndex.injective h)
        rcases lt_or_gt_of_ne hne_idx with hlt | hgt
        · have hlt_E : U'.componentIndex (componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl a))) <
              U'.componentIndex (componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl b))) := by
            apply equivFinOfWeight_lt_of_lt (botSmoothWeight G U c i x)
            rw [hwa, hwb]
            exact Nat.add_lt_add_left hlt 1
          exact ⟨fun _ => Or.inl hlt, fun _ => Or.inl hlt_E⟩
        · have hgt_E : U'.componentIndex (componentOf (smoothCrossing G x).continuation
              (smoothArcEquiv G (Sum.inl b))) <
              U'.componentIndex (componentOf (smoothCrossing G x).continuation
                (smoothArcEquiv G (Sum.inl a))) := by
            apply equivFinOfWeight_lt_of_lt (botSmoothWeight G U c i x)
            rw [hwa, hwb]
            exact Nat.add_lt_add_left hgt 1
          exact ⟨fun h => False.elim (rankBefore_asymm h (Or.inl hgt_E)),
            fun h => False.elim (rankBefore_asymm h (Or.inl hgt))⟩
    · have hnot_b : ∀ e : Fin G.nArc, BotProtected G U c i e →
          (smoothArcEquiv G (Sum.inl b) : Fin (smoothCrossing G x).nArc) ≠
            smoothArcEquiv G (Sum.inl e) := by
        intro e he hEq
        exact hb (Sum.inl.inj ((smoothArcEquiv G).injective hEq) ▸ he)
      have hlt_E := botSmooth_rankBefore_d1_of_not_protected G U c hself i hroot x hx
        (smoothArcEquiv G (Sum.inl b)) hnot_b
      have ha_E : BotProtected (smoothCrossing G x) U'
          (smoothCrossingEquiv G x ⟨c, bot_ne_self G U c i x hx⟩) i
          (smoothArcEquiv G (Sum.inl a)) :=
        (botSmooth_protected_iff G U c hself i hroot x hx _).mpr ⟨a, ha, rfl⟩
      have hd0_sm := smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) i
      have hd1_sm := smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) (otherBranch i)
      unfold BotProtected at ha_E
      rw [hd0_sm, hd1_sm] at ha_E
      have hrb_E : rankBefore (visitRank U' (smoothArcEquiv G (Sum.inl b)))
          (visitRank U' (smoothArcEquiv G (Sum.inl a))) := by
        rcases ha_E with hEq0_E | hEq1_E | hgt_E
        · exact False.elim (ha0 (Sum.inl.inj ((smoothArcEquiv G).injective hEq0_E)))
        · rw [hEq1_E]; exact hlt_E
        · exact rankBefore_trans hlt_E hgt_E
      have hlt_G : rankBefore (visitRank U b) (visitRank U d1) := by
        have hne_d1 : b ≠ d1 := fun h => hb (Or.inr (Or.inl h))
        have hnot_gt : ¬ rankBefore (visitRank U d1) (visitRank U b) :=
          fun h => hb (Or.inr (Or.inr h))
        rcases rankBefore_trichotomy (visitRank U b) (visitRank U d1) with hlt | hEq | hgt
        · exact hlt
        · exact False.elim (hne_d1 (visitRank_injective U hEq))
        · exact False.elim (hnot_gt hgt)
      have hrb_G : rankBefore (visitRank U b) (visitRank U a) := by
        rcases ha with hEq0_G | rfl | hgt_G
        · exact False.elim (ha0 hEq0_G)
        · exact hlt_G
        · exact rankBefore_trans hlt_G hgt_G
      exact ⟨fun h => False.elim (rankBefore_asymm h hrb_E),
        fun h => False.elim (rankBefore_asymm h hrb_G)⟩
  · have hb : BotProtected G U c i b := hab.resolve_left ha
    have hnot_a : ∀ e : Fin G.nArc, BotProtected G U c i e →
        (smoothArcEquiv G (Sum.inl a) : Fin (smoothCrossing G x).nArc) ≠
          smoothArcEquiv G (Sum.inl e) := by
      intro e he hEq
      exact ha (Sum.inl.inj ((smoothArcEquiv G).injective hEq) ▸ he)
    have hlt_E := botSmooth_rankBefore_d1_of_not_protected G U c hself i hroot x hx
      (smoothArcEquiv G (Sum.inl a)) hnot_a
    have hb_E : BotProtected (smoothCrossing G x) U'
        (smoothCrossingEquiv G x ⟨c, bot_ne_self G U c i x hx⟩) i
        (smoothArcEquiv G (Sum.inl b)) :=
      (botSmooth_protected_iff G U c hself i hroot x hx _).mpr ⟨b, hb, rfl⟩
    have hd0_sm := smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) i
    have hd1_sm := smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) (otherBranch i)
    unfold BotProtected at hb_E
    rw [hd0_sm, hd1_sm] at hb_E
    have hrb_E : rankBefore (visitRank U' (smoothArcEquiv G (Sum.inl a)))
        (visitRank U' (smoothArcEquiv G (Sum.inl b))) := by
      rcases hb_E with hEq0_E | hEq1_E | hgt_E
      · exact False.elim (hb0 (Sum.inl.inj ((smoothArcEquiv G).injective hEq0_E)))
      · rw [hEq1_E]; exact hlt_E
      · exact rankBefore_trans hlt_E hgt_E
    have hlt_G : rankBefore (visitRank U a) (visitRank U d1) := by
      have hne_d1 : a ≠ d1 := fun h => ha (Or.inr (Or.inl h))
      have hnot_gt : ¬ rankBefore (visitRank U d1) (visitRank U a) :=
        fun h => ha (Or.inr (Or.inr h))
      rcases rankBefore_trichotomy (visitRank U a) (visitRank U d1) with hlt | hEq | hgt
      · exact hlt
      · exact False.elim (hne_d1 (visitRank_injective U hEq))
      · exact False.elim (hnot_gt hgt)
    have hrb_G : rankBefore (visitRank U a) (visitRank U b) := by
      rcases hb with hEq0_G | rfl | hgt_G
      · exact False.elim (hb0 hEq0_G)
      · exact hlt_G
      · exact rankBefore_trans hlt_G hgt_G
    exact ⟨fun _ => hrb_G, fun _ => hrb_E⟩

theorem botSmooth_badCrossings_disjoint (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (hbad : ∀ y ∈ badCrossings U, ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming y j))
    (x : Fin G.nCrossing)
    (hx : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming x j)) :
    let U' := botSmoothTraversal G U c i x
    let c' := smoothCrossingEquiv G x ⟨c, bot_ne_self G U c i x hx⟩
    ∀ y' ∈ badCrossings U', ∀ j : Fin 2,
      ¬ BotProtected (smoothCrossing G x) U' c' i ((smoothCrossing G x).incoming y' j) := by
  intro U' c' y' hy' j hprot'
  obtain ⟨⟨y, hyx⟩, rfl⟩ := (smoothCrossingEquiv G x).surjective y'
  rw [smoothCrossing_incoming_retained G x y hyx j] at hprot'
  obtain ⟨a, ha, hEq⟩ := (botSmooth_protected_iff G U c hself i hroot x hx _).mp hprot'
  have hya : G.incoming y j = a := Sum.inl.inj ((smoothArcEquiv G).injective hEq)
  have hy_prot : BotProtected G U c i (G.incoming y j) := hya ▸ ha
  have hy'_bad : badAt U' (smoothCrossingEquiv G x ⟨y, hyx⟩) := by
    simpa [badCrossings] using hy'
  by_cases hyc : y = c
  · subst y
    have hcomp_d1_G : componentOf G.continuation (G.incoming c 1) =
        componentOf G.continuation (G.incoming c 0) :=
      (componentOf_eq_iff _ _ _).mpr hself.symm
    have hcomp_d1_E : componentOf (smoothCrossing G x).continuation
        (smoothArcEquiv G (Sum.inl (G.incoming c 1))) =
        componentOf (smoothCrossing G x).continuation
          (smoothArcEquiv G (Sum.inl (G.incoming c 0))) := by
      have hsc := bot_smooth_self G U c hself i hroot x hx
      dsimp only at hsc
      rw [smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) 0,
          smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) 1] at hsc
      exact (componentOf_eq_iff _ _ _).mpr hsc.symm
    have hvp_i_G := visitPosition_root_eq_zero G U (G.incoming c i) hroot
    have hvp_oi_G := visitPosition_d1_pos G U c hself i hroot
    have hvp_i_E := visitPosition_root_eq_zero (smoothCrossing G x) U'
      ((smoothCrossing G x).incoming c' i) (botSmooth_root G U c hself i hroot x hx)
    have hvp_oi_E := visitPosition_d1_pos (smoothCrossing G x) U' c'
      (bot_smooth_self G U c hself i hroot x hx) i (botSmooth_root G U c hself i hroot x hx)
    rw [smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) i] at hvp_i_E
    rw [smoothCrossing_incoming_retained G x c (bot_ne_self G U c i x hx) (otherBranch i)] at hvp_oi_E
    have hrb_c : rankBefore (visitRank U' (smoothArcEquiv G (Sum.inl (G.incoming c 0))))
        (visitRank U' (smoothArcEquiv G (Sum.inl (G.incoming c 1)))) ↔
        rankBefore (visitRank U (G.incoming c 0)) (visitRank U (G.incoming c 1)) := by
      unfold rankBefore visitRank
      dsimp
      rw [hcomp_d1_G, hcomp_d1_E]
      simp only [lt_irrefl, true_and, false_or]
      fin_cases i
      · dsimp [otherBranch] at hvp_i_G hvp_oi_G hvp_i_E hvp_oi_E
        omega
      · dsimp [otherBranch] at hvp_i_G hvp_oi_G hvp_i_E hvp_oi_E
        omega
    have hfb := firstVisitedBranch_smooth_eq_of_rankBefore G U x U' c hyx hrb_c
    have hc_bad : badAt U c := by
      unfold badAt at hy'_bad ⊢
      rw [hfb] at hy'_bad
      intro hgood
      apply hy'_bad
      change firstVisitedBranch U c =
        G.overBranch (((smoothCrossingEquiv G x).symm (smoothCrossingEquiv G x ⟨c, hyx⟩)).val)
      rw [Equiv.symm_apply_apply]
      exact hgood
    exact hbad c (by simp [badCrossings, hc_bad]) j hy_prot
  · have hab : BotProtected G U c i (G.incoming y 0) ∨ BotProtected G U c i (G.incoming y 1) := by
      fin_cases j
      · exact Or.inl hy_prot
      · exact Or.inr hy_prot
    have hy0_ne : G.incoming y 0 ≠ G.incoming c i :=
      incoming_ne_of_crossing_ne G c y hyc 0 i
    have hy1_ne : G.incoming y 1 ≠ G.incoming c i :=
      incoming_ne_of_crossing_ne G c y hyc 1 i
    have hfb := firstVisitedBranch_smooth_eq_of_rankBefore G U x U' y hyx
      (botSmooth_rankBefore_iff_of_protected G U c hself i hroot x hx _ _ hy0_ne hy1_ne hab)
    have hy_bad : badAt U y := by
      unfold badAt at hy'_bad ⊢
      rw [hfb] at hy'_bad
      intro hgood
      apply hy'_bad
      change firstVisitedBranch U y =
        G.overBranch (((smoothCrossingEquiv G x).symm (smoothCrossingEquiv G x ⟨y, hyx⟩)).val)
      rw [Equiv.symm_apply_apply]
      exact hgood
    exact hbad y (by simp [badCrossings, hy_bad]) j hy_prot

theorem botLoop_deletion {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (G : PLLinkDiagram) (hG : G.nCrossing ≤ n)
    (U : BasedTraversal G) (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (hbad : ∀ y ∈ badCrossings U, ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming y j)) :
    unlinkFactor * descendingLaurentEvaluator G U =
      descendingLaurentEvaluator (smoothCrossing G c) (smoothChildBasedTraversal G c) := by
  classical
  by_cases hne : (badCrossings U).Nonempty
  · have hex : ∃ p ∈ badCrossings U, p = Classical.choose hne :=
      ⟨Classical.choose hne, Classical.choose_spec hne, rfl⟩
    obtain ⟨p, hp_mem, hp_eq⟩ := hex
    have hp_prot : ∀ j : Fin 2, ¬ BotProtected G U c i (G.incoming p j) := hbad p hp_mem
    have hcp : c ≠ p := bot_ne_self G U c i p hp_prot
    have hpc : p ≠ c := hcp.symm
    have hevalG : descendingLaurentEvaluator G U = descendingEvaluatorPivotBranch G U p :=
      descendingEvaluator_eq_pivotBranch_of_choice G U hne p hp_eq.symm
    have hsw_bad : ∀ y ∈ badCrossings (switchTraversal U p), ∀ j : Fin 2,
        ¬ BotProtected (switchCrossing G p) (switchTraversal U p) c i
          ((switchCrossing G p).incoming y j) := by
      intro y hy j
      rw [badCrossings_switch_erase U p hp_mem] at hy
      exact hbad y (Finset.mem_of_mem_erase hy) j
    have ih_sw := botLoop_deletion outer (switchCrossing G p) hG
      (switchTraversal U p) c hself i hroot hsw_bad
    let U' := botSmoothTraversal G U c i p
    let c' := smoothCrossingEquiv G p ⟨c, hcp⟩
    have hdrop_p := smoothCrossing_crossing_count_drop G p
    have hlt_p : (smoothCrossing G p).nCrossing < n := by omega
    have hsm_le : (smoothCrossing G p).nCrossing ≤ n := le_of_lt hlt_p
    have hsm_eval_U' : descendingLaurentEvaluator (smoothCrossing G p)
        (smoothChildBasedTraversal G p) =
        descendingLaurentEvaluator (smoothCrossing G p) U' :=
      outer.1 (SignedDiagramIso.refl (smoothCrossing G p)) hlt_p
        (smoothChildBasedTraversal G p) U'
    have ih_sm := botLoop_deletion outer (smoothCrossing G p) hsm_le U' c'
      (bot_smooth_self G U c hself i hroot p hp_prot) i
      (botSmooth_root G U c hself i hroot p hp_prot)
      (botSmooth_badCrossings_disjoint G U c hself i hroot hbad p hp_prot)
    let p' := smoothCrossingEquiv G c ⟨p, hpc⟩
    have hdrop_c := smoothCrossing_crossing_count_drop G c
    have hlt_c : (smoothCrossing G c).nCrossing < n := by omega
    have hlt_sw_c : (smoothCrossing (switchCrossing G p) c).nCrossing < n := by
      have h1 := smoothCrossing_crossing_count_drop (switchCrossing G p) c
      rw [switch_crossing_count] at h1
      omega
    have h_iso_sw : descendingLaurentEvaluator (smoothCrossing (switchCrossing G p) c)
        (smoothChildBasedTraversal (switchCrossing G p) c) =
        descendingLaurentEvaluator (switchCrossing (smoothCrossing G c) p')
          (switchTraversal (smoothChildBasedTraversal G c) p') :=
      outer.1 (switchSmoothSignedDiagramIso G c p hcp) hlt_sw_c _ _
    have hlt_sm_c : (smoothCrossing (smoothCrossing G c) p').nCrossing < n := by
      have h2 := smoothCrossing_crossing_count_drop (smoothCrossing G c) p'
      omega
    have h_iso_sm : descendingLaurentEvaluator (smoothCrossing (smoothCrossing G p) c')
        (smoothChildBasedTraversal (smoothCrossing G p) c') =
        descendingLaurentEvaluator (smoothCrossing (smoothCrossing G c) p')
          (smoothChildBasedTraversal (smoothCrossing G c) p') :=
      (outer.1 (smoothTwiceSignedDiagramIso G c p hcp) hlt_sm_c _ _).symm
    have hskein_c := outer.2 hlt_c (smoothChildBasedTraversal G c) p'
    rw [hevalG, descendingEvaluatorPivotBranch, mul_add,
      ← mul_assoc, mul_comm unlinkFactor (pivotSwitchFactor G p), mul_assoc,
      ih_sw, h_iso_sw, hsm_eval_U',
      ← mul_assoc, mul_comm unlinkFactor (pivotSmoothFactor G p), mul_assoc,
      ih_sm, h_iso_sm, hskein_c, descendingEvaluatorPivotBranch,
      pivotSwitchFactor_smooth_ne G p c hpc, pivotSmoothFactor_smooth_ne G p c hpc]
  · have hEmpty : badCrossings U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hevalG : descendingLaurentEvaluator G U = descendingUnlinkValue G :=
      descendingLaurentEvaluator_terminal G U (by simp [hne])
    have hgood : ∀ d : Fin G.nCrossing, d ≠ c → ¬ badAt U d := by
      intro d _ hb
      have hmem : d ∈ badCrossings U := by simp [badCrossings, hb]
      rw [hEmpty] at hmem
      exact Finset.not_mem_empty d hmem
    obtain ⟨W, hW⟩ := smoothCrossing_exists_descending_of_baseArc G U
      (componentOf G.continuation (G.incoming c i)) c i hroot.symm hself hgood
    have hdrop_c := smoothCrossing_crossing_count_drop G c
    have hlt_c : (smoothCrossing G c).nCrossing < n := by omega
    have hsm := outer.1 (SignedDiagramIso.refl (smoothCrossing G c)) hlt_c
      (smoothChildBasedTraversal G c) W
    have hevalW : descendingLaurentEvaluator (smoothCrossing G c) W =
        descendingUnlinkValue (smoothCrossing G c) :=
      descendingLaurentEvaluator_terminal (smoothCrossing G c) W
        (by simp [hW])
    rw [hevalG, hsm, hevalW, ← descendingUnlinkValue_smooth_self G c hself]
termination_by (G.nCrossing, (badCrossings U).card)
decreasing_by
  · apply Prod.Lex.right
    have hdrop := badCrossings_switch_card U p hp_mem
    omega
  · apply Prod.Lex.left
    omega

/-! ## Part 6: Adjacent Component Swap Invariance in the Presence of a Self-Crossing -/

theorem topProtected_same_component_iff (G : PLLinkDiagram) (U : BasedTraversal G)
    (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (a : Fin G.nArc)
    (hcomp : componentOf G.continuation a =
      componentOf G.continuation (G.incoming c i)) :
    TopProtected G U c i a ↔
      visitPosition U a ≤ visitPosition U (G.incoming c (otherBranch i)) := by
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  unfold TopProtected rankBefore visitRank
  dsimp
  rw [hcomp, hcomp_d1]
  constructor
  · rintro ((hlt | ⟨_, hpos⟩) | h1)
    · exact False.elim (lt_irrefl _ hlt)
    · exact le_of_lt hpos
    · rw [h1]
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | hEq
    · exact Or.inl (Or.inr ⟨rfl, hlt⟩)
    · have ha : a = G.incoming c (otherBranch i) :=
        visitRank_injective U
          (Prod.ext (congrArg U.componentIndex (hcomp.trans hcomp_d1.symm)) hEq)
      exact Or.inr ha

noncomputable def rootAtPortTraversal (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) : BasedTraversal D where
  componentIndex := T.componentIndex
  baseArc C :=
    if h : C = componentOf D.continuation (D.incoming c i) then
      ⟨D.incoming c i, h.symm⟩
    else
      T.baseArc C

theorem rootAtPortTraversal_componentIndex (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) :
    (rootAtPortTraversal D T c i).componentIndex = T.componentIndex := rfl

theorem rootAtPortTraversal_root (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) :
    ((rootAtPortTraversal D T c i).baseArc
      (componentOf D.continuation (D.incoming c i))).val = D.incoming c i := by
  unfold rootAtPortTraversal
  dsimp
  rw [dif_pos rfl]

def NeedMidSwitch (D : PLLinkDiagram) (U V : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) (x : Fin D.nCrossing) : Prop :=
  if ∃ j : Fin 2, TopProtected D U c i (D.incoming x j) then
    badAt U x
  else
    badAt V x

noncomputable def needMidSwitchFinset (D : PLLinkDiagram) (U V : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) : Finset (Fin D.nCrossing) :=
  Finset.univ.filter (NeedMidSwitch D U V c i)

theorem needMidSwitchFinset_switch_erase (D : PLLinkDiagram) (U V : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2)
    (x : Fin D.nCrossing) (hx : x ∈ needMidSwitchFinset D U V c i) :
    needMidSwitchFinset (switchCrossing D x) (switchTraversal U x) (switchTraversal V x) c i =
      (needMidSwitchFinset D U V c i).erase x := by
  have hx_need : NeedMidSwitch D U V c i x := by
    simpa [needMidSwitchFinset] using hx
  ext y
  simp only [needMidSwitchFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, ne_eq]
  change (if ∃ j : Fin 2, TopProtected D U c i (D.incoming y j) then
      badAt (switchTraversal U x) y
    else
      badAt (switchTraversal V x) y) ↔
    y ≠ x ∧ NeedMidSwitch D U V c i y
  by_cases hyx : y = x
  · subst y
    constructor
    · intro hbad'
      unfold NeedMidSwitch at hx_need
      by_cases htop : ∃ j : Fin 2, TopProtected D U c i (D.incoming x j)
      · rw [if_pos htop] at hx_need hbad'
        exact False.elim (((badAt_switch_toggle U x).mp hbad') hx_need)
      · rw [if_neg htop] at hx_need hbad'
        exact False.elim (((badAt_switch_toggle V x).mp hbad') hx_need)
    · rintro ⟨hne, _⟩
      exact False.elim (hne rfl)
  · constructor
    · intro hbad'
      refine ⟨hyx, ?_⟩
      unfold NeedMidSwitch
      by_cases htop : ∃ j : Fin 2, TopProtected D U c i (D.incoming y j)
      · rw [if_pos htop] at hbad' ⊢
        exact (badAt_switch_same U x y hyx).mp hbad'
      · rw [if_neg htop] at hbad' ⊢
        exact (badAt_switch_same V x y hyx).mp hbad'
    · rintro ⟨_, hneed⟩
      unfold NeedMidSwitch at hneed
      by_cases htop : ∃ j : Fin 2, TopProtected D U c i (D.incoming y j)
      · rw [if_pos htop] at hneed ⊢
        exact (badAt_switch_same U x y hyx).mpr hneed
      · rw [if_neg htop] at hneed ⊢
        exact (badAt_switch_same V x y hyx).mpr hneed

theorem descending_adjacentSwap_of_mid_empty {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (U : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf D.continuation (D.incoming c i))).val = D.incoming c i)
    (hIdx : U.componentIndex (componentOf D.continuation (D.incoming c i)) = r)
    (hempty : needMidSwitchFinset D U
      (reindexTraversalComponents U (adjacentComponentSwap r hr)) c i = ∅) :
    descendingLaurentEvaluator D U =
      descendingLaurentEvaluator D
        (reindexTraversalComponents U (adjacentComponentSwap r hr)) := by
  let V := reindexTraversalComponents U (adjacentComponentSwap r hr)
  have hno_need : ∀ x : Fin D.nCrossing, ¬ NeedMidSwitch D U V c i x := by
    intro x hx
    have hmem : x ∈ needMidSwitchFinset D U V c i := by
      simp [needMidSwitchFinset, hx]
    rw [hempty] at hmem
    exact Finset.not_mem_empty x hmem
  have hbadU : ∀ y ∈ badCrossings U, ∀ j : Fin 2, ¬ TopProtected D U c i (D.incoming y j) := by
    intro y hy j htop
    have hy_bad : badAt U y := by simpa [badCrossings] using hy
    have hneed : NeedMidSwitch D U V c i y := by
      unfold NeedMidSwitch
      rw [if_pos ⟨j, htop⟩]
      exact hy_bad
    exact hno_need y hneed
  have hbadV : ∀ y ∈ badCrossings V, ∀ j : Fin 2, ¬ BotProtected D V c i (D.incoming y j) := by
    intro y hy j hbot
    have hy_badV : badAt V y := by simpa [badCrossings] using hy
    have hnot_need := hno_need y
    unfold NeedMidSwitch at hnot_need
    have htop_ex : ∃ j₀ : Fin 2, TopProtected D U c i (D.incoming y j₀) := by
      by_contra hnot_top
      rw [if_neg hnot_top] at hnot_need
      exact hnot_need hy_badV
    rw [if_pos htop_ex] at hnot_need
    have hy_goodU : ¬ badAt U y := hnot_need
    have hfb_ne : firstVisitedBranch V y ≠ firstVisitedBranch U y := by
      intro hfb
      apply hy_badV
      unfold badAt at hy_goodU
      push_neg at hy_goodU
      rw [hfb, hy_goodU]
    have hmixed : (U.componentIndex (componentOf D.continuation (D.incoming y 0)) = r ∧
        (U.componentIndex (componentOf D.continuation (D.incoming y 1))).val = r.val + 1) ∨
      ((U.componentIndex (componentOf D.continuation (D.incoming y 0))).val = r.val + 1 ∧
        U.componentIndex (componentOf D.continuation (D.incoming y 1)) = r) := by
      by_contra hnot_mixed
      exact hfb_ne (firstVisitedBranch_reindex_adjacent_components_of_not_mixed U r hr y hnot_mixed)
    let C_0 := componentOf D.continuation (D.incoming c i)
    have hcomp_c01 : componentOf D.continuation (D.incoming c 1) =
        componentOf D.continuation (D.incoming c 0) :=
      (componentOf_eq_iff _ _ _).mpr hself.symm
    have hyc : y ≠ c := by
      intro hEq
      subst y
      have h0_idx : U.componentIndex (componentOf D.continuation (D.incoming c 0)) = r := by
        fin_cases i
        · exact hIdx
        · rw [← hcomp_c01]; exact hIdx
      have h1_idx : U.componentIndex (componentOf D.continuation (D.incoming c 1)) = r := by
        rw [hcomp_c01]; exact h0_idx
      rcases hmixed with ⟨_, h1⟩ | ⟨h0, _⟩
      · rw [h1_idx] at h1; omega
      · rw [h0_idx] at h0; omega
    have hnot_top_of_r1 : ∀ k : Fin 2,
        (U.componentIndex (componentOf D.continuation (D.incoming y k))).val = r.val + 1 →
        ¬ TopProtected D U c i (D.incoming y k) := by
      intro k hk htk
      have hle := topProtected_component_le D U c hself i (D.incoming y k) htk
      have hle_val : (U.componentIndex (componentOf D.continuation (D.incoming y k))).val ≤
          r.val := by
        rw [← hIdx]
        exact hle
      omega
    have hV_idx_C0 : (V.componentIndex C_0).val = r.val + 1 := by
      change (adjacentComponentSwap r hr (U.componentIndex C_0)).val = r.val + 1
      rw [hIdx, adjacentComponentSwap_apply_val r hr r, if_pos rfl]
    have hnot_bot_of_r1 : ∀ k : Fin 2,
        (U.componentIndex (componentOf D.continuation (D.incoming y k))).val = r.val + 1 →
        ¬ BotProtected D V c i (D.incoming y k) := by
      intro k hk hbk
      have hge := botProtected_component_ge D V c hself i (D.incoming y k) hbk
      have hge_val : (V.componentIndex C_0).val ≤
          (V.componentIndex (componentOf D.continuation (D.incoming y k))).val := hge
      have hVk : (V.componentIndex (componentOf D.continuation (D.incoming y k))).val = r.val := by
        change (adjacentComponentSwap r hr
          (U.componentIndex (componentOf D.continuation (D.incoming y k)))).val = r.val
        rw [adjacentComponentSwap_apply_val r hr]
        have hne_r : U.componentIndex (componentOf D.continuation (D.incoming y k)) ≠ r := by
          intro hEq; rw [hEq] at hk; omega
        have hEq_s : U.componentIndex (componentOf D.continuation (D.incoming y k)) =
            ⟨r.val + 1, hr⟩ := Fin.ext hk
        rw [if_neg hne_r, if_pos hEq_s]
      omega
    have h_contradict_branch : ∀ k : Fin 2,
        U.componentIndex (componentOf D.continuation (D.incoming y k)) = r →
        TopProtected D U c i (D.incoming y k) →
        BotProtected D V c i (D.incoming y k) → False := by
      intro k hk_r htk hbk
      have hcomp_yk : componentOf D.continuation (D.incoming y k) = C_0 :=
        U.componentIndex.injective (hk_r.trans hIdx.symm)
      have hne_d0 : D.incoming y k ≠ D.incoming c i :=
        incoming_ne_of_crossing_ne D c y hyc k i
      have hne_d1 : D.incoming y k ≠ D.incoming c (otherBranch i) :=
        incoming_ne_of_crossing_ne D c y hyc k (otherBranch i)
      have hvp_le : visitPosition U (D.incoming y k) ≤
          visitPosition U (D.incoming c (otherBranch i)) :=
        (topProtected_same_component_iff D U c hself i (D.incoming y k) hcomp_yk).mp htk
      have hvp_ge : visitPosition V (D.incoming c (otherBranch i)) ≤
          visitPosition V (D.incoming y k) :=
        (botProtected_same_component_iff D V c hself i (D.incoming y k) hcomp_yk hne_d0).mp hbk
      rw [visitPosition_reindexTraversalComponents,
          visitPosition_reindexTraversalComponents] at hvp_ge
      have hvp_eq : visitPosition U (D.incoming y k) =
          visitPosition U (D.incoming c (otherBranch i)) :=
        le_antisymm hvp_le hvp_ge
      have hcomp_d1 : componentOf D.continuation (D.incoming c (otherBranch i)) = C_0 :=
        (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle D c hself i).symm
      exact hne_d1 (visitRank_injective U
        (Prod.ext (congrArg U.componentIndex (hcomp_yk.trans hcomp_d1.symm)) hvp_eq))
    obtain ⟨j₀, htop⟩ := htop_ex
    rcases hmixed with ⟨h0_r, h1_r1⟩ | ⟨h0_r1, h1_r⟩
    · have hj₀_0 : j₀ = 0 := by
        fin_cases j₀
        · rfl
        · exact False.elim (hnot_top_of_r1 1 h1_r1 htop)
      have hj_0 : j = 0 := by
        fin_cases j
        · rfl
        · exact False.elim (hnot_bot_of_r1 1 h1_r1 hbot)
      subst hj₀_0; subst hj_0
      exact h_contradict_branch 0 h0_r htop hbot
    · have hj₀_1 : j₀ = 1 := by
        fin_cases j₀
        · exact False.elim (hnot_top_of_r1 0 h0_r1 htop)
        · rfl
      have hj_1 : j = 1 := by
        fin_cases j
        · exact False.elim (hnot_bot_of_r1 0 h0_r1 hbot)
        · rfl
      subst hj₀_1; subst hj_1
      exact h_contradict_branch 1 h1_r htop hbot
  have htop_del := topLoop_deletion outer D (le_of_eq hD) U c hself i hroot hbadU
  have hbot_del := botLoop_deletion outer D (le_of_eq hD) V c hself i hroot hbadV
  exact unlinkFactor_mul_injective (htop_del.trans hbot_del.symm)

theorem descending_adjacentSwap_of_selfCrossing_rooted_aux {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (U : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf D.continuation (D.incoming c i))).val = D.incoming c i)
    (hIdx : U.componentIndex (componentOf D.continuation (D.incoming c i)) = r) :
    descendingLaurentEvaluator D U =
      descendingLaurentEvaluator D
        (reindexTraversalComponents U (adjacentComponentSwap r hr)) := by
  classical
  let V := reindexTraversalComponents U (adjacentComponentSwap r hr)
  by_cases hne : (needMidSwitchFinset D U V c i).Nonempty
  · obtain ⟨x, hx⟩ := hne
    have ih := descending_adjacentSwap_of_selfCrossing_rooted_aux outer
      (switchCrossing D x) hD (switchTraversal U x) r hr c hself i hroot hIdx
    exact (descendingEvaluator_agreement_switch_iff outer D hD U V x).mpr ih
  · have hempty : needMidSwitchFinset D U V c i = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    exact descending_adjacentSwap_of_mid_empty outer D hD U r hr c hself i hroot hIdx hempty
termination_by (needMidSwitchFinset D U
  (reindexTraversalComponents U (adjacentComponentSwap r hr)) c i).card
decreasing_by
  change (needMidSwitchFinset (switchCrossing D x) (switchTraversal U x)
    (switchTraversal V x) c i).card < (needMidSwitchFinset D U V c i).card
  rw [needMidSwitchFinset_switch_erase D U V c i x hx]
  exact Finset.card_erase_lt_of_mem hx

theorem descending_adjacentSwap_of_selfCrossing_left {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hIdx : T.componentIndex (componentOf D.continuation (D.incoming c 0)) = r) :
    descendingLaurentEvaluator D T =
      descendingLaurentEvaluator D
        (reindexTraversalComponents T (adjacentComponentSwap r hr)) := by
  let U := rootAtPortTraversal D T c 0
  let T' := reindexTraversalComponents T (adjacentComponentSwap r hr)
  let U' := reindexTraversalComponents U (adjacentComponentSwap r hr)
  have hTU : descendingLaurentEvaluator D T = descendingLaurentEvaluator D U :=
    descendingEvaluator_eq_of_componentIndex_eq outer hD T U rfl
  have hT'U' : descendingLaurentEvaluator D T' = descendingLaurentEvaluator D U' :=
    descendingEvaluator_eq_of_componentIndex_eq outer hD T' U' rfl
  have hUU' := descending_adjacentSwap_of_selfCrossing_rooted_aux outer D hD U r hr c hself 0
    (rootAtPortTraversal_root D T c 0) hIdx
  exact hTU.trans (hUU'.trans hT'U'.symm)

theorem reindexTraversalComponents_adjacentComponentSwap_involutive
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D) :
    reindexTraversalComponents
      (reindexTraversalComponents T (adjacentComponentSwap r hr))
      (adjacentComponentSwap r hr) = T := by
  apply basedTraversal_ext
  · apply Equiv.ext
    intro C
    exact Equiv.swap_apply_self _ _ (T.componentIndex C)
  · intro C
    rfl

theorem descending_adjacentSwap_of_selfCrossing_right {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hIdx : (T.componentIndex (componentOf D.continuation (D.incoming c 0))).val = r.val + 1) :
    descendingLaurentEvaluator D T =
      descendingLaurentEvaluator D
        (reindexTraversalComponents T (adjacentComponentSwap r hr)) := by
  let T' := reindexTraversalComponents T (adjacentComponentSwap r hr)
  have hIdx' : T'.componentIndex (componentOf D.continuation (D.incoming c 0)) = r := by
    apply Fin.ext
    change (adjacentComponentSwap r hr
      (T.componentIndex (componentOf D.continuation (D.incoming c 0)))).val = r.val
    rw [adjacentComponentSwap_apply_val r hr]
    have hne_r : T.componentIndex (componentOf D.continuation (D.incoming c 0)) ≠ r := by
      intro h; rw [h] at hIdx; omega
    have hEq_s : T.componentIndex (componentOf D.continuation (D.incoming c 0)) =
        ⟨r.val + 1, hr⟩ := Fin.ext hIdx
    rw [if_neg hne_r, if_pos hEq_s]
  have hsymm := descending_adjacentSwap_of_selfCrossing_left outer D hD T' r hr c hself hIdx'
  rw [reindexTraversalComponents_adjacentComponentSwap_involutive T r hr] at hsymm
  exact hsymm.symm

theorem descending_adjacentSwap_of_selfCrossing {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hComp : T.componentIndex (componentOf D.continuation (D.incoming c 0)) = r ∨
      (T.componentIndex (componentOf D.continuation (D.incoming c 0))).val = r.val + 1) :
    descendingLaurentEvaluator D
      (reindexTraversalComponents T (adjacentComponentSwap r hr)) =
        descendingUnlinkValue D := by
  have hEq : descendingLaurentEvaluator D T =
      descendingLaurentEvaluator D
        (reindexTraversalComponents T (adjacentComponentSwap r hr)) := by
    rcases hComp with hLeft | hRight
    · exact descending_adjacentSwap_of_selfCrossing_left outer D hD T r hr c hself hLeft
    · exact descending_adjacentSwap_of_selfCrossing_right outer D hD T r hr c hself hRight
  rw [← hEq]
  exact descendingLaurentEvaluator_terminal D T (by simp [hT])

end

end DirectGLSSW.HOMFLY.Gemini



