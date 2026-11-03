import OpenHistorySupplied
import UniversalCarrierEventDomain
import UniversalCarrierParentCore
import UniversalCarrierCornerDomain

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.ChildRestartRecursion ActiveArc.RetainedWords ActiveArc.Primitive ActiveArc.OpenCarrier

variable {N : ℕ} (L : Fin N → CarrierLine)
  (hU : UniversalLocus L) (hT : PairTransverse L)
  {s : ActiveWordState} (f : Fin (s.1+1) ⊕ Unit → Fin N) (hf : Function.Injective f)
  (hi : ∀ e : Fin (s.1+1), lineValue (L (f (Sum.inl e))) (s.2 e.castSucc)=0 ∧
    lineValue (L (f (Sum.inl e))) (s.2 e.succ)=0)
  (ht : lineValue (L (f (Sum.inr ()))) (s.2 ⟨s.1+1,by omega⟩)=0)

include L hU hT f hf hi ht

/-- Every actual unselected event word along the open block has its required
nonvanishing, with exactly the baseline intentional-event exception. -/
theorem literal_open_history_event_domain {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨n,q⟩)
    (c : Crossing q) (hc : FirstCrossing q c) :
    ∀ U : Support q hR, c∉U.val → EventCarrierNonvanishing q hR c U := by
  obtain ⟨g,hg,hgt,hgi,hge⟩ := literal_open_history_supplied L hpath f hf hi ht
  exact event_domain_of_supplied q hR c hc (L ∘ g)
    (universalLocus_comap L hU g hg) (pairTransverse_comap L hT g hg) hgi hge

/-- Actual parent far determinants; only the original baseline G1/regularity
inputs at the current state remain, not a far-nonvanishing premise. -/
theorem literal_open_history_parent_far {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q) (hG : cyclicNoncollinear q)
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨a+b,q⟩)
    (c : Crossing q) (hcut : c.val.2.val=a) :
    parentFarLocus q hR c hcut (parentChartLines q) := by
  obtain ⟨g,hg,hgt,hgi,hge⟩ := literal_open_history_supplied L hpath f hf hi ht
  exact canonical_parent_far_of_supplied q hR hG c hcut (L ∘ g)
    (universalLocus_comap L hU g hg) (pairTransverse_comap L hT g hg) hgi hge

/-- Core point-triple genericity for EVERY actual parent support. This is G1
of the rooted word, not a claim of closed cap G2. -/
theorem literal_open_history_parent_core {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨a+b,q⟩)
    (c : Crossing q) (hcut : c.val.2.val=a) :
    ∀ T : Support (parent q c hcut) (regular_parent q hR c hcut),
      ShortEdgeSignStability.CoreHGeneric
        (rootedPolygonWord (OpenVertex _ _ T) (openLast _ _ T.val))
        (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val-1) := by
  obtain ⟨g,hg,hgt,hgi,hge⟩ := literal_open_history_supplied L hpath f hf hi ht
  exact parent_all_support_core_of_supplied q hR c hcut (L ∘ g)
    (universalLocus_comap L hU g hg) (pairTransverse_comap L hT g hg) hgi hge

/-- Actual positive-drop corner words: G1 follows from the same inherited family. -/
theorem literal_open_history_corner_core {n m d : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (h : n=d+m) (hd : 0 < d) (hQ : Regular q)
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨n,q⟩) :
    ∀ U : Support (dropWord q h) (dropWord_regular q h hQ),
      ShortEdgeSignStability.CoreHGeneric
        (rootedPolygonWord (OpenVertex _ _ U) (openLast _ _ U.val))
        (openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1) := by
  obtain ⟨g,hg,hgt,hgi,hge⟩ := literal_open_history_supplied L hpath f hf hi ht
  exact corner_word_core_of_supplied q h hd hQ (L ∘ g)
    (universalLocus_comap L hU g hg) (pairTransverse_comap L hT g hg) hgi hge

/-- The short-first-edge projector's far determinants, including every support
and arbitrary unused prefix coordinate, are derived at the current state. -/
theorem literal_open_history_corner_far {n m d : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (h : n=d+m) (hd : 0 < d) (hQ : Regular q)
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨n,q⟩) :
    ∀ U : Support (dropWord q h) (dropWord_regular q h hQ),
      ∀ (x : PlanarPoint ℝ) (k j : ℕ), 1 < k → k < j →
        j≤openCount (dropWord q h) (dropWord_regular q h hQ) U.val →
        polygonHDet (fun i => if i=0 then x else
          rootedPolygonWord (OpenVertex _ _ U) (openLast _ _ U.val) (i-1)) 1 k j≠0 := by
  obtain ⟨g,hg,hgt,hgi,hge⟩ := literal_open_history_supplied L hpath f hf hi ht
  exact corner_far_of_supplied q h hd hQ (L ∘ g)
    (universalLocus_comap L hU g hg) (pairTransverse_comap L hT g hg) hgi hge

end DirectGLSSW.CyclicCarrierClearing





