import LiteralCarrierHistory
import UniversalCarrierStateTransport
import UniversalCycleSecants

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.ChildRestartRecursion

/-- A literal open-to-open step retains the whole supplied family, including
its terminal label. Closed detachment/restart cannot enter this relation. -/
theorem literal_open_step_supplied {N : ℕ} (L : Fin N → CarrierLine)
    {s t : ActiveWordState} (h : LiteralCarrierStep (.inr s) (.inr t))
    (f : Fin (s.1+1) ⊕ Unit → Fin N) (hf : Function.Injective f)
    (hi : ∀ e : Fin (s.1+1), lineValue (L (f (Sum.inl e))) (s.2 e.castSucc)=0 ∧
      lineValue (L (f (Sum.inl e))) (s.2 e.succ)=0)
    (ht : lineValue (L (f (Sum.inr ()))) (s.2 ⟨s.1+1,by omega⟩)=0) :
    ∃ g : Fin (t.1+1) ⊕ Unit → Fin N, Function.Injective g ∧
      g (Sum.inr ())=f (Sum.inr ()) ∧
      (∀ e : Fin (t.1+1), lineValue (L (g (Sum.inl e))) (t.2 e.castSucc)=0 ∧
        lineValue (L (g (Sum.inl e))) (t.2 e.succ)=0) ∧
      lineValue (L (g (Sum.inr ()))) (t.2 ⟨t.1+1,by omega⟩)=0 := by
  cases h with
  | move q hR x hx0 hx1 =>
    exact ⟨f,hf,rfl,supplied_moveStart_incidence q (L ∘ f) hi ht x⟩
  | parent q hR c hc hcut =>
    let g := f ∘ suffixCarrierMap
    have hs := supplied_suffix_incidence q (L ∘ f) hi ht
    exact ⟨g,hf.comp suffixCarrierMap_injective,rfl,
      supplied_moveStart_incidence (suffix q) (L ∘ g) hs.1 hs.2 (rightParameter q c)⟩
  | corner q hR ha =>
    exact ⟨f ∘ suffixCarrierMap,hf.comp suffixCarrierMap_injective,rfl,
      supplied_suffix_incidence q (L ∘ f) hi ht⟩

/-- Finite closure of the existing literal open steps. No new history or
admissibility predicate is defined, and no opaque restart choice is used. -/
theorem literal_open_history_supplied {N : ℕ} (L : Fin N → CarrierLine)
    {s t : ActiveWordState}
    (h : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s t)
    (f : Fin (s.1+1) ⊕ Unit → Fin N) (hf : Function.Injective f)
    (hi : ∀ e : Fin (s.1+1), lineValue (L (f (Sum.inl e))) (s.2 e.castSucc)=0 ∧
      lineValue (L (f (Sum.inl e))) (s.2 e.succ)=0)
    (ht : lineValue (L (f (Sum.inr ()))) (s.2 ⟨s.1+1,by omega⟩)=0) :
    ∃ g : Fin (t.1+1) ⊕ Unit → Fin N, Function.Injective g ∧
      g (Sum.inr ())=f (Sum.inr ()) ∧
      (∀ e : Fin (t.1+1), lineValue (L (g (Sum.inl e))) (t.2 e.castSucc)=0 ∧
        lineValue (L (g (Sum.inl e))) (t.2 e.succ)=0) ∧
      lineValue (L (g (Sum.inr ()))) (t.2 ⟨t.1+1,by omega⟩)=0 := by
  induction h with
  | refl => exact ⟨f,hf,rfl,hi,ht⟩
  | tail hpath hstep ih =>
    obtain ⟨g,hg,hgt,hgi,hge⟩ := ih
    obtain ⟨k,hk,hkt,hki,hke⟩ := literal_open_step_supplied L hstep g hg hgi hge
    exact ⟨k,hk,hkt.trans hgt,hki,hke⟩

/-- Universal event/far determinants, pair transversality and every eligible
cycle's secants all persist along the same finite open history. -/
theorem literal_open_history_inventory {N : ℕ} (L : Fin N → CarrierLine)
    (hU : UniversalLocus L) (hT : PairTransverse L) (hC : allCycleSecantExclusions L)
    {s t : ActiveWordState}
    (h : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s t)
    (f : Fin (s.1+1) ⊕ Unit → Fin N) (hf : Function.Injective f)
    (hi : ∀ e : Fin (s.1+1), lineValue (L (f (Sum.inl e))) (s.2 e.castSucc)=0 ∧
      lineValue (L (f (Sum.inl e))) (s.2 e.succ)=0)
    (ht : lineValue (L (f (Sum.inr ()))) (s.2 ⟨s.1+1,by omega⟩)=0) :
    ∃ g : Fin (t.1+1) ⊕ Unit → Fin N, Function.Injective g ∧
      g (Sum.inr ())=f (Sum.inr ()) ∧
      UniversalLocus (L ∘ g) ∧ PairTransverse (L ∘ g) ∧
      (∀ e : Fin (t.1+1), lineValue (L (g (Sum.inl e))) (t.2 e.castSucc)=0 ∧
        lineValue (L (g (Sum.inl e))) (t.2 e.succ)=0) ∧
      lineValue (L (g (Sum.inr ()))) (t.2 ⟨t.1+1,by omega⟩)=0 ∧
      ∀ (m : ℕ) (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d)
        (k : Fin m → Fin (t.1+1) ⊕ Unit), Function.Injective k →
        cycleSecantExclusions (g ∘ k) L := by
  obtain ⟨g,hg,hgt,hgi,hge⟩ := literal_open_history_supplied L h f hf hi ht
  refine ⟨g,hg,hgt,universalLocus_comap L hU g hg,pairTransverse_comap L hT g hg,hgi,hge,?_⟩
  intro m d hd k hk
  exact allCycleSecantExclusions_apply L hC d hd (g ∘ k) (hg.comp hk)

end DirectGLSSW.CyclicCarrierClearing



