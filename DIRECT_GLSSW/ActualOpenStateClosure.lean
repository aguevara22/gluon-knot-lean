import ActualLegalHistoryTransitions
import OpenHistoryConsumers
import PhysicalTraversalClosure

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.Primitive
open ActiveArc.TraversalClosure ActiveArc.ChildRestartRecursion
open AuxiliaryCarrierChart UniversalCarrierDomain

/-- An open block is a literal history in the existing closed/open state space. -/
theorem literal_open_path_to_literalCarrierPath {s t : ActiveWordState}
    (h : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s t) :
    LiteralCarrierPath (.inr s) (.inr t) := by
  induction h with
  | refl => exact .nil _
  | tail _ step ih => exact literalCarrierPath_snoc ih step

/-- A first event admits a genuine forward choice with all state invariants
and the same literal open history. Neither target G1 nor target AUX is assumed. -/
theorem actual_after_first_full_open_history {s : ActiveWordState} {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hR)
    (hleft : RemainingLeft q) (c : Crossing q) (hc : FirstCrossing q c)
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨n,q⟩) :
    ∃ t : ℝ, leftParameter q c<t ∧ t<afterBound q c ∧
      ∃ hM : Regular (moveStart q t), cyclicNoncollinear (moveStart q t) ∧
        ClosedAuxiliary (moveStart q t) hM ∧ RemainingLeft (moveStart q t) ∧
        Relation.ReflTransGen
          (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v))
          s ⟨n,moveStart q t⟩ := by
  obtain ⟨t,hct,htb,hM,hGm,hAm,hLm⟩ :=
    exists_after_first_full_state q hR hG hAux hleft c hc
  refine ⟨t,hct,htb,hM,hGm,hAm,hLm,?_⟩
  exact hpath.tail (.move q hR t
    (lt_trans (leftParameter_spec q c).1 hct).le
    (lt_of_lt_of_le htb (afterBound_le_one q c)))

/-- At an actual parent, inherited supplied carriers discharge the only
additional far determinant obligation, and all state invariants follow. -/
theorem actual_supplied_parent_full_open_history
    {N : ℕ} (L : Fin N → CarrierLine) (hU : UniversalLocus L)
    (hT : PairTransverse L) {s : ActiveWordState}
    (f : Fin (s.1+1) ⊕ Unit → Fin N) (hf : Function.Injective f)
    (hi : ∀ e : Fin (s.1+1), lineValue (L (f (Sum.inl e))) (s.2 e.castSucc)=0 ∧
      lineValue (L (f (Sum.inl e))) (s.2 e.succ)=0)
    (ht : lineValue (L (f (Sum.inr ()))) (s.2 ⟨s.1+1,by omega⟩)=0)
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hR)
    (hleft : RemainingLeft q) (c : Crossing q) (hc : FirstCrossing q c)
    (hcut : c.val.2.val=a)
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨a+b,q⟩) :
    cyclicNoncollinear (parent q c hcut) ∧
      ClosedAuxiliary (parent q c hcut) (regular_parent q hR c hcut) ∧
      RemainingLeft (parent q c hcut) ∧
      Relation.ReflTransGen
        (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v))
        s ⟨b,parent q c hcut⟩ := by
  have hFar := literal_open_history_parent_far L hU hT f hf hi ht q hR hG hpath c hcut
  obtain ⟨hGP,hAP,hLP⟩ := parent_full_state_of_parentFar q hR hG hAux hleft c hc hcut hFar
  exact ⟨hGP,hAP,hLP,hpath.tail (.parent q hR c hc hcut)⟩

/-- A crossing-free first edge may be removed while preserving the actual
geometry, closed smoothing domain, remaining turns, and literal history. -/
theorem actual_corner_full_open_history {s : ActiveWordState} {b : ℕ}
    (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hR)
    (hleft : RemainingLeft q) (hfree : ∀ c : Crossing q,c.val.1≠0)
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨1+b,q⟩) :
    cyclicNoncollinear (suffix q) ∧
      ClosedAuxiliary (suffix q) (regular_suffix q hR) ∧
      RemainingLeft (suffix q) ∧
      Relation.ReflTransGen
        (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v))
        s ⟨b,suffix q⟩ := by
  obtain ⟨hGS,hAS,hLS⟩ := corner_suffix_state_closure q hR hG hAux hleft hfree
  exact ⟨hGS,hAS,hLS,hpath.tail (.corner q hR (by omega))⟩

end DirectGLSSW.CyclicCarrierClearing
