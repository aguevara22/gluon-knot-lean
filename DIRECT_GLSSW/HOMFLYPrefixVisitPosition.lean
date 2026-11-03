import HOMFLYProcessedPrefixExclusion
import HOMFLYParentRootTraversal
import HOMFLYOrbitTraversalCoordinates

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PermutationOrbits
open Equiv
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- An injectively preserved initial orbit segment lies before the new first return. -/
theorem prefix_pow_lt_fibre_card (p : Perm α) (q : Perm β) (f : α → β)
    (hf : Function.Injective f) (r : α) (n : ℕ)
    (hn : n < Fintype.card (Fibre p (componentOf p r)))
    (hp : ∀ k : ℕ, k ≤ n → (q ^ k) (f r) = f ((p ^ k) r)) :
    n < Fintype.card (Fibre q (componentOf q (f r))) := by
  let g : Fin (n+1) → Fibre q (componentOf q (f r)) := fun k =>
    ⟨(q ^ k.val) (f r), by simp⟩
  have hg : Function.Injective g := by
    intro i j h
    have hval := congrArg Subtype.val h
    change (q ^ i.val) (f r) = (q ^ j.val) (f r) at hval
    rw [hp i.val (by omega), hp j.val (by omega)] at hval
    have hold := hf hval
    let ii : Fin (Fintype.card (Fibre p (componentOf p r))) := ⟨i.val, by omega⟩
    let jj : Fin (Fintype.card (Fibre p (componentOf p r))) := ⟨j.val, by omega⟩
    have he : orbitEnumeration p r ii = orbitEnumeration p r jj := by
      apply Subtype.ext
      simpa only [orbitEnumeration_apply_val] using hold
    have hv : ii.val = jj.val := congrArg (fun z : Fin (Fintype.card (Fibre p (componentOf p r))) => z.val)
      ((orbitEnumeration p r).injective he)
    exact Fin.ext hv
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at hc
  omega

end DirectGLSSW.PermutationOrbits

namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

/-- Before reaching the first cut port, actual smoothing inserts no connector step. -/
theorem parentRoot_prefix_pow (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (n : ℕ) (hn : n ≤ visitPosition T (D.incoming c (firstVisitedBranch T c))) :
    let r := (T.baseArc (componentOf D.continuation
      (D.incoming c (firstVisitedBranch T c)))).val
    ((smoothCrossing D c).continuation ^ n) (smoothArcEquiv D (Sum.inl r)) =
      smoothArcEquiv D (Sum.inl ((D.continuation ^ n) r)) := by
  dsimp only
  let i := firstVisitedBranch T c
  let a := D.incoming c i
  let b := D.incoming c (otherBranch i)
  let r := (T.baseArc (componentOf D.continuation a)).val
  have hcomp : componentOf D.continuation a = componentOf D.continuation b :=
    (componentOf_eq_iff _ _ _).2 (rootCut_sameCycle D c hself i)
  have ha : componentOf D.continuation a = componentOf D.continuation r :=
    (T.baseArc (componentOf D.continuation a)).property.symm
  have hb : componentOf D.continuation b = componentOf D.continuation r := hcomp.symm.trans ha
  have hpa := visitPosition_eq_orbitPosition_of_baseArc T a r rfl ha
  have hpb := visitPosition_eq_orbitPosition_of_baseArc T b r
    (by dsimp [r]; rw [hcomp]) hb
  have hfirst := firstVisitedBranch_is_first T c
  have hlt : visitPosition T a < visitPosition T b := by
    change rankBefore (visitRank T a) (visitRank T b) at hfirst
    simpa only [rankBefore, visitRank, hcomp, lt_self_iff_false, true_and, false_or] using hfirst
  let ea := (orbitEnumeration D.continuation r).symm ⟨a,ha⟩
  let eb := (orbitEnumeration D.continuation r).symm ⟨b,hb⟩
  have hne : ∀ k : ℕ, k < visitPosition T a →
      ∀ j : Fin 2, (D.continuation ^ k) r ≠ D.incoming c j := by
    intro k hk j
    have hka : k < ea.val := by rw [← hpa]; exact hk
    let kk : Fin (Fintype.card (Fibre D.continuation (componentOf D.continuation r))) :=
      ⟨k,by omega⟩
    have hnot (e : Fin (Fintype.card (Fibre D.continuation (componentOf D.continuation r))))
        (he : k < e.val) : (D.continuation ^ k) r ≠ (orbitEnumeration D.continuation r e).val := by
      intro h
      have hh : orbitEnumeration D.continuation r kk = orbitEnumeration D.continuation r e := by
        apply Subtype.ext
        simpa only [orbitEnumeration_apply_val] using h
      have hv := congrArg Fin.val ((orbitEnumeration D.continuation r).injective hh)
      change k = e.val at hv
      omega
    have hja : j=i ∨ j=otherBranch i := by
      by_cases hj : j=i
      · exact Or.inl hj
      · right
        apply Fin.ext
        have hji : j.val ≠ i.val := fun h => hj (Fin.ext h)
        have hjb := j.isLt
        have hib := i.isLt
        simp only [otherBranch]
        omega
    rcases hja with rfl | rfl
    · have hv : (orbitEnumeration D.continuation r ea).val=a :=
        congrArg Subtype.val ((orbitEnumeration D.continuation r).apply_symm_apply ⟨a,ha⟩)
      change (D.continuation ^ k) r ≠ a
      rw [← hv]; exact hnot ea hka
    · have hv : (orbitEnumeration D.continuation r eb).val=b :=
        congrArg Subtype.val ((orbitEnumeration D.continuation r).apply_symm_apply ⟨b,hb⟩)
      change (D.continuation ^ k) r ≠ b
      rw [← hv]; exact hnot eb (by rw [← hpb]; omega)
  change ((smoothCrossing D c).continuation ^ n) (smoothArcEquiv D (Sum.inl r)) = _
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Perm.mul_apply,ih (by omega)]
    change smoothArcEquiv D (smoothContinuationGeometryCode D c
      ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl ((D.continuation ^ n) r))))) = _
    rw [Equiv.symm_apply_apply,
      smoothContinuationGeometryCode_other_arc D c _ (hne n (by change n+1 ≤ visitPosition T a at hn;omega))]
    rw [pow_succ',Perm.mul_apply]

/-- The actual continuing traversal preserves every original prefix position exactly. -/
theorem parentRoot_prefix_visitPosition (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (x : Fin D.nArc)
    (hx : componentOf D.continuation x =
      componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))
    (hle : visitPosition T x ≤ visitPosition T (D.incoming c (firstVisitedBranch T c))) :
    visitPosition (parentRootSelfSmoothingTraversal D T c hself)
      (smoothArcEquiv D (Sum.inl x)) = visitPosition T x := by
  let a := D.incoming c (firstVisitedBranch T c)
  let r := (T.baseArc (componentOf D.continuation a)).val
  let U := parentRootSelfSmoothingTraversal D T c hself
  let f : Fin D.nArc → Fin (smoothCrossing D c).nArc := fun e => smoothArcEquiv D (Sum.inl e)
  have hf : Function.Injective f := (smoothArcEquiv D).injective.comp Sum.inl_injective
  have hxr : componentOf D.continuation x = componentOf D.continuation r :=
    hx.trans (T.baseArc (componentOf D.continuation a)).property.symm
  have hpos := visitPosition_eq_orbitPosition_of_baseArc T x r
    (by dsimp [r];rw [hx]) hxr
  have hn : visitPosition T x < Fintype.card (Fibre D.continuation (componentOf D.continuation r)) := by
    rw [hpos];exact ((orbitEnumeration D.continuation r).symm ⟨x,hxr⟩).isLt
  have hp : ∀ k : ℕ, k ≤ visitPosition T x →
      ((smoothCrossing D c).continuation ^ k) (f r) = f ((D.continuation ^ k) r) := by
    intro k hk
    exact parentRoot_prefix_pow D T c hself k (le_trans hk hle)
  have hb := prefix_pow_lt_fibre_card D.continuation (smoothCrossing D c).continuation
    f hf r (visitPosition T x) hn hp
  let j : Fin (Fintype.card (Fibre (smoothCrossing D c).continuation
      (componentOf (smoothCrossing D c).continuation (f r)))) := ⟨visitPosition T x,hb⟩
  have hroot : (U.baseArc (componentOf (smoothCrossing D c).continuation (f r))).val=f r := by
    have hc := firstVisited_original_root_component D T c hself
    change componentOf (smoothCrossing D c).continuation (f r) = _ at hc
    rw [hc]
    exact parentRootSelfSmoothingTraversal_baseArc D T c hself (Sum.inl false)
  have hpow : (D.continuation ^ visitPosition T x) r=x := by
    change (D.continuation ^ visitPosition T x)
      (T.baseArc (componentOf D.continuation a)).val = x
    rw [← hx]
    exact visitPosition_reconstruct T x
  have hj : (orbitEnumeration (smoothCrossing D c).continuation (f r) j).val=f x := by
    rw [orbitEnumeration_apply_val,hp _ (le_refl _),hpow]
  have h := visitPosition_orbitEnumeration U (f r) hroot j
  rw [hj] at h
  exact h
end DirectGLSSW.HOMFLY



