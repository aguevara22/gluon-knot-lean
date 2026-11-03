import MixedCapChainAlgebra
import DirectGLSSW.CutEventAdapterV3

set_option autoImplicit false

namespace DirectGLSSW.MixedCapChainRestriction
open scoped BigOperators
open OrderedCapEvents MixedEdgeChainsV3 ExtendedReturnArcGeometry
open CapCriticalTimes CapCriticalEventGeometry

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Nonempty cuts in horizontal order whose complete event chain also follows the return arc. -/
def ArcIncreasing (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (u v : EventIndex q n) (huv : u < v) (S : NonemptyIntervalCuts u.val v.val) : Prop :=
  List.Pairwise (fun c d => (eventPair q n c).1 < (eventPair q n d).1)
    (cutEventChain u v (Fin.lt_iff_val_lt_val.mp huv)
      ⟨S.val, (Finset.mem_erase.mp S.property).2⟩)

abbrev ArcIncreasingEventCuts (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (u v : EventIndex q n) (huv : u < v) :=
  {S : NonemptyIntervalCuts u.val v.val // ArcIncreasing q n u v huv S}

instance arcIncreasingEventCutsFintype (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (u v : EventIndex q n) (huv : u < v) : Fintype (ArcIncreasingEventCuts q n u v huv) :=
  inferInstanceAs (Fintype {S : NonemptyIntervalCuts u.val v.val // ArcIncreasing q n u v huv S})

theorem signed_cut_term_zero_of_not_arcIncreasing
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (u v : EventIndex q n) (huv : u < v)
    (S : NonemptyIntervalCuts u.val v.val) (hbad : ¬ ArcIncreasing q n u v huv S) :
    (-1 : ℚ) ^ (S.val.card+1) *
      branchProduct (eventIntervalArray q n) (cutVertices u.val v.val S.val) = 0 := by
  let T : IntervalCutSet u.val v.val := ⟨S.val,(Finset.mem_erase.mp S.property).2⟩
  have hz := event_branchProduct_zero_of_arc_order_failure
    (cutEventChain u v (Fin.lt_iff_val_lt_val.mp huv) T)
    (cutEventChain_pairwise_sorted u v (Fin.lt_iff_val_lt_val.mp huv) T) hbad
  rw [cutEventChain_values_eq_cutVertices] at hz
  change branchProduct (eventIntervalArray q n) (cutVertices u.val v.val S.val) = 0 at hz
  simp only [hz, mul_zero]

/-- Removing reverse-arc chains changes no term: each removed product contains a zero factor. -/
theorem event_cut_sum_eq_arcIncreasing_sum
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (u v : EventIndex q n) (huv : u < v) :
    (∑ S ∈ ((Finset.Ioo u.val v.val).powerset).erase ∅,
      (-1 : ℚ) ^ (S.card+1) *
        branchProduct (eventIntervalArray q n) (cutVertices u.val v.val S)) =
    ∑ S : ArcIncreasingEventCuts q n u v huv,
      (-1 : ℚ) ^ (S.val.val.card+1) *
        branchProduct (eventIntervalArray q n) (cutVertices u.val v.val S.val.val) := by
  let f : NonemptyIntervalCuts u.val v.val → ℚ := fun S =>
    (-1 : ℚ) ^ (S.val.card+1) *
      branchProduct (eventIntervalArray q n) (cutVertices u.val v.val S.val)
  let good := Finset.univ.filter (ArcIncreasing q n u v huv)
  calc
    _ = ∑ S : NonemptyIntervalCuts u.val v.val, f S :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ S ∈ good, f S := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro S _ hnot
      have hbad : ¬ ArcIncreasing q n u v huv S := by simpa [good] using hnot
      exact signed_cut_term_zero_of_not_arcIncreasing q n u v huv S hbad
    _ = _ := by
      exact Finset.sum_subtype good (by intro S; simp [good]) f

theorem exists_amplitude_eq_arcIncreasingCutSum (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (hturn : planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn)) *
      planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn)) < 0)
    (ε : ℝ) (hε : 0 < ε) (hbound : ε < geometricRadius hn P)
    (hroots : Set.InjOn (criticalRoot (extendedArc hn P ε))
      ↑(criticalPairs (extendedArc hn P ε) n)) :
    ∃ cU cV : EventIndex (extendedArc hn P ε) n,
      eventTime (extendedArc hn P ε) n cU = 0 ∧
      eventTime (extendedArc hn P ε) n cV = (P (lastIndex hn)).1 - (P (zeroIndex hn)).1 ∧
      ∃ hlt : cU < cV,
      polygonAmplitude P hP =
        ∑ S : ArcIncreasingEventCuts (extendedArc hn P ε) n cU cV hlt,
          (-1 : ℚ) ^ (S.val.val.card+1) *
            branchProduct (eventIntervalArray (extendedArc hn P ε) n)
              (cutVertices cU.val cV.val S.val.val) := by
  obtain ⟨cU,cV,hTU,hTV,hlt,hvalue⟩ :=
    MixedCapChainAlgebra.exists_amplitude_eq_event_cut_sum
      hRI hn P hP hU hV hleft hturn ε hε hbound hroots
  refine ⟨cU,cV,hTU,hTV,hlt,?_⟩
  exact hvalue.trans (event_cut_sum_eq_arcIncreasing_sum _ _ cU cV hlt)







end
end DirectGLSSW.MixedCapChainRestriction
