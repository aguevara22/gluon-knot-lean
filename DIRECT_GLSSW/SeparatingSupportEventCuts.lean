import SupportCutMembership
import MixedEventOrder
import MixedCapChainRestriction
import SelectedCellClippedWord

set_option autoImplicit false

namespace DirectGLSSW.SeparatingSupportEventCuts
open OrderedCapEvents MixedEdgeChainsV3 FiniteSupportCuts SupportCutMembership
open MixedEdgeSupportOrder MixedEventOrder MixedCapChainRestriction
open MixedConsecutiveCapWord InteriorEdgeEvents ExtendedReturnArcGeometry

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual arc-order restriction is exactly nonalternation, for the rank
equivalence supplied by crossing/event geometry. All event specifications are explicit. -/
theorem support_arcIncreasing_iff_nonalternating
    {n m : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (Q : ℕ → PlanarPoint ℝ) (u v : EventIndex Q m) (huv : u < v)
    (E : DirectGLSSW.EdgeChord q e ≃ ↥(Finset.Ioo u.val v.val))
    (F : DirectGLSSW.EdgeChord q e → EventIndex Q m)
    (hF : ∀ z, (E z).val = (F z).val)
    (offset : ℝ) (htime : ∀ z, eventTime Q m (F z) = (crossingPoint q z.val).1-offset)
    (hpU : eventPair Q m u = (1,2)) (hpV : eventPair Q m v = (n-1,n))
    (hpairs : ∀ z, eventPair Q m (F z) =
      (complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+1,
       complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2))
    (T : {T : Finset (DirectGLSSW.EdgeChord q e) // T.Nonempty}) :
    ArcIncreasing Q m u v huv (nonemptySupportCutsEquiv E T) ↔
      PolygonNonalternation.polygonNonalternating q hq.g2 (T.val.image Subtype.val) := by
  classical
  let C := cutEventChain u v huv (supportCutMap E T.val)
  have hC : C.Pairwise (· < ·) := cutEventChain_pairwise_sorted u v huv _
  have hmem (c : EventIndex Q m) :
      c ∈ C ↔ c = u ∨ c = v ∨ ∃ z ∈ T.val, F z = c :=
    mem_support_cut_chain u v huv E F hF T.val c
  have hFbnd (z : DirectGLSSW.EdgeChord q e) : u < F z ∧ F z < v := by
    have hz := Finset.mem_Ioo.mp (E z).property
    rw [hF z] at hz
    exact hz
  have hpbnd (z : DirectGLSSW.EdgeChord q e) :
      (eventPair Q m u).1 < (eventPair Q m (F z)).1 ∧
      (eventPair Q m (F z)).1 < (eventPair Q m v).1 := by
    rw [hpU,hpV,hpairs]
    have hr := InteriorEdgeEvents.return_rank_interior q hq e z
    dsimp only
    omega
  have hpUV : (eventPair Q m u).1 < (eventPair Q m v).1 := by
    rw [hpU,hpV]
    have hn := hq.size_ge_three
    dsimp only
    omega
  change C.Pairwise (fun c d => (eventPair Q m c).1 < (eventPair Q m d).1) ↔ _
  rw [pairwise_iff_ordered_pairs C hC,
    polygonNonalternating_iff_returnVisitOrder q hq.g2 hq.size_ge_three e hflat hleft]
  constructor
  · intro h c hc d hd _ hcd
    have hcC : F c ∈ C := (hmem _).mpr (Or.inr (Or.inr ⟨c,hc,rfl⟩))
    have hdC : F d ∈ C := (hmem _).mpr (Or.inr (Or.inr ⟨d,hd,rfl⟩))
    exact (event_pair_order_iff_returnVisitBefore q hq e Q F hpairs c d).mp
      (h _ hcC _ hdC ((event_lt_iff_abscissa_lt q e Q F offset htime c d).mpr hcd))
  · intro h a ha b hb hab
    rcases (hmem a).mp ha with rfl | rfl | ⟨c,hc,rfl⟩
    · rcases (hmem b).mp hb with rfl | rfl | ⟨d,hd,rfl⟩
      · exact (lt_irrefl _ hab).elim
      · exact hpUV
      · exact (hpbnd d).1
    · rcases (hmem b).mp hb with rfl | rfl | ⟨d,hd,rfl⟩
      · exact (lt_asymm huv hab).elim
      · exact (lt_irrefl _ hab).elim
      · exact (lt_asymm (hFbnd d).2 hab).elim
    · rcases (hmem b).mp hb with rfl | rfl | ⟨d,hd,rfl⟩
      · exact (lt_asymm (hFbnd c).1 hab).elim
      · exact (hpbnd c).2
      · apply (event_pair_order_iff_returnVisitBefore q hq e Q F hpairs c d).mpr
        exact h c hc d hd (by intro heq; subst d; exact lt_irrefl _ hab)
          ((event_lt_iff_abscissa_lt q e Q F offset htime c d).mp hab)

def separatingSupportFlatten {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) :
    EdgeSeparatingSupport q hq.g2 e hflat hleft ≃
      {T : {T : Finset (DirectGLSSW.EdgeChord q e) // T.Nonempty} //
        PolygonNonalternation.polygonNonalternating q hq.g2 (T.val.image Subtype.val)} where
  toFun T := ⟨⟨T.val,T.property.1⟩,T.property.2⟩
  invFun T := ⟨T.val.val,T.val.property,T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def edgeSupportEventCutEquiv
    {n m : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (Q : ℕ → PlanarPoint ℝ) (u v : EventIndex Q m) (huv : u < v)
    (E : DirectGLSSW.EdgeChord q e ≃ ↥(Finset.Ioo u.val v.val))
    (F : DirectGLSSW.EdgeChord q e → EventIndex Q m)
    (hF : ∀ z, (E z).val = (F z).val)
    (offset : ℝ) (htime : ∀ z, eventTime Q m (F z) = (crossingPoint q z.val).1-offset)
    (hpU : eventPair Q m u = (1,2)) (hpV : eventPair Q m v = (n-1,n))
    (hpairs : ∀ z, eventPair Q m (F z) =
      (complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+1,
       complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2)) :
    EdgeSeparatingSupport q hq.g2 e hflat hleft ≃ ArcIncreasingEventCuts Q m u v huv :=
  (separatingSupportFlatten q hq e hflat hleft).trans
    ((nonemptySupportCutsEquiv E).subtypeEquiv
      (fun T => (support_arcIncreasing_iff_nonalternating q hq e hflat hleft
        Q u v huv E F hF offset htime hpU hpV hpairs T).symm))

theorem edgeSupportEventCutEquiv_card
    {n m : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (Q : ℕ → PlanarPoint ℝ) (u v : EventIndex Q m) (huv : u < v)
    (E : DirectGLSSW.EdgeChord q e ≃ ↥(Finset.Ioo u.val v.val))
    (F : DirectGLSSW.EdgeChord q e → EventIndex Q m)
    (hF : ∀ z, (E z).val = (F z).val)
    (offset : ℝ) (htime : ∀ z, eventTime Q m (F z) = (crossingPoint q z.val).1-offset)
    (hpU : eventPair Q m u = (1,2)) (hpV : eventPair Q m v = (n-1,n))
    (hpairs : ∀ z, eventPair Q m (F z) =
      (complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+1,
       complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2))
    (T : EdgeSeparatingSupport q hq.g2 e hflat hleft) :
    (edgeSupportEventCutEquiv q hq e hflat hleft Q u v huv E F hF offset htime
      hpU hpV hpairs T).val.val.card = T.val.card := by
  exact Finset.card_map (indexEmbedding E)

/-- On the original normalized G1--G2 domain, the geometric event equivalence
supplies the complete support/cut bijection and its cardinality identity.
No global critical-root injectivity, daughter genericity or RI is used here. -/
theorem exists_actual_support_cut_equiv
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0 < ε) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∃ u v : EventIndex Q n,
      eventTime Q n u = 0 ∧
      eventTime Q n v = (q e).1-(q (cyclicSuccessor e)).1 ∧
      ∃ huv : u < v,
      ∃ Φ : EdgeSeparatingSupport q hq.g2 e (hV.trans hU.symm) hleft ≃
        ArcIncreasingEventCuts Q n u v huv,
      ∀ T, (Φ T).val.val.card = T.val.card := by
  dsimp only
  obtain ⟨u,v,E,hu,hv,hpu,hpv,huv,hE,_⟩ :=
    SelectedCellClippedWord.exists_actual_selected_cell_words q hq e hU hV hleft ε hε
  let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
  let E' := E.trans (interiorEventRanksEquiv Q n u v 0
    ((q e).1-(q (cyclicSuccessor e)).1) hu hv)
  let F := fun z => (E z).val
  have hF : ∀ z, (E' z).val = (F z).val := fun _ => rfl
  let Φ := edgeSupportEventCutEquiv q hq e (hV.trans hU.symm) hleft Q u v huv
    E' F hF (q (cyclicSuccessor e)).1 (fun z => (hE z).1)
    hpu hpv (fun z => (hE z).2)
  refine ⟨u,v,hu,hv,huv,Φ,?_⟩
  intro T
  exact edgeSupportEventCutEquiv_card q hq e (hV.trans hU.symm) hleft Q u v huv
    E' F hF (q (cyclicSuccessor e)).1 (fun z => (hE z).1)
    hpu hpv (fun z => (hE z).2) T





end
end DirectGLSSW.SeparatingSupportEventCuts
