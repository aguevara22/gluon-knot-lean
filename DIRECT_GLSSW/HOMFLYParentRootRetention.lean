import HOMFLYRootSelfSmoothingTraversal
import HOMFLYCutUnaffectedOrder

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits
open Equiv
noncomputable section
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Cutting after two ordered visits keeps the old root with the earlier port. -/
theorem root_sameCycle_cut_of_position_lt (p : Perm α) (r a b : α)
    (ha : componentOf p a = componentOf p r)
    (hb : componentOf p b = componentOf p r)
    (hlt : ((orbitEnumeration p r).symm ⟨a, ha⟩).val <
      ((orbitEnumeration p r).symm ⟨b, hb⟩).val) :
    (p * swap a b).SameCycle r a := by
  let e := orbitEnumeration p r
  let ia := e.symm ⟨a, ha⟩
  let ib := e.symm ⟨b, hb⟩
  have hea : (e ia).val = a := congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
  have heb : (e ib).val = b := congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
  have hab : ia.val < ib.val := hlt
  have hne : ∀ n : ℕ, n < ia.val → (p ^ n) r ≠ a ∧ (p ^ n) r ≠ b := by
    intro n hn
    let j : Fin (Fintype.card (Fibre p (componentOf p r))) := ⟨n, by omega⟩
    have hj : (e j).val = (p ^ n) r := orbitEnumeration_apply_val p r j
    constructor
    · intro h
      have he : e j = e ia := Subtype.ext (hj.trans (h.trans hea.symm))
      have hv := congrArg Fin.val (e.injective he)
      change n = ia.val at hv
      omega
    · intro h
      have he : e j = e ib := Subtype.ext (hj.trans (h.trans heb.symm))
      have hv := congrArg Fin.val (e.injective he)
      change n = ib.val at hv
      omega
  have hp : ∀ n : ℕ, n ≤ ia.val → ((p * swap a b) ^ n) r = (p ^ n) r := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rcases hne n (by omega) with ⟨hna, hnb⟩
      rw [pow_succ', Perm.mul_apply, ih (by omega),
        mul_swap_apply_of_ne p hna hnb, pow_succ', Perm.mul_apply]
  refine ⟨(ia.val : ℤ), ?_⟩
  rw [zpow_natCast, hp ia.val (by omega)]
  exact (orbitEnumeration_apply_val p r ia).symm.trans hea

end
end DirectGLSSW.PermutationOrbits

namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

/-- The original traversal root lies on the continuing (earlier-port) cut component. -/
theorem firstVisited_root_sameCycle_cut (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    let i := firstVisitedBranch T c
    let r := (T.baseArc (componentOf D.continuation (D.incoming c i))).val
    (rootCutContinuation D c i).SameCycle r (D.incoming c i) := by
  dsimp only
  let i := firstVisitedBranch T c
  let a := D.incoming c i
  let b := D.incoming c (otherBranch i)
  let r := (T.baseArc (componentOf D.continuation a)).val
  have hcomp : componentOf D.continuation a = componentOf D.continuation b :=
    (componentOf_eq_iff _ _ _).2 (rootCut_sameCycle D c hself i)
  have ha : componentOf D.continuation a = componentOf D.continuation r :=
    (T.baseArc (componentOf D.continuation a)).property.symm
  have hb : componentOf D.continuation b = componentOf D.continuation r :=
    hcomp.symm.trans ha
  have hpa := visitPosition_eq_orbitPosition_of_baseArc T a r rfl ha
  have hpb := visitPosition_eq_orbitPosition_of_baseArc T b r
    (by dsimp [r]; rw [hcomp]) hb
  have hfirst := firstVisitedBranch_is_first T c
  have hlt : visitPosition T a < visitPosition T b := by
    change rankBefore (visitRank T a) (visitRank T b) at hfirst
    simp only [rankBefore, visitRank, hcomp, lt_self_iff_false, true_and, false_or] at hfirst
    exact hfirst
  exact root_sameCycle_cut_of_position_lt D.continuation r a b ha hb
    (by rw [← hpa, ← hpb]; exact hlt)

end
end DirectGLSSW.HOMFLY
