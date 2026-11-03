import ActiveArcCutOrbits

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e)
variable (S : Finset (ActiveArc.Crossing (cutArc q e)))

/-- The previously constructed retained vertex word is exactly the filtered actual orbit. -/
theorem active_retainedWord_eq_filtered (x : ActiveArc.Event (cutArc q e)) :
    List.ofFn (RetainedWords.vertex (cutArc q e) (cutArc_regular q e hq) S x)=
      ((orbitWord (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S) x).filter
        (fun z => decide (ActiveArc.retained (cutArc q e) S z))).map (ActiveArc.eventPoint (cutArc q e)) := by
  classical
  let r := cutArc q e
  let hr := cutArc_regular q e hq
  let E := RetainedWords.enumeration r hr S x
  have hcoords :
      List.ofFn (fun i : Fin (Fintype.card (RetainedWords.Corner r hr S x)) => (E i).val)=
        (List.ofFn (fun i : RetainedWords.Coord r hr S x => i)).filter
          (fun i => decide (ActiveArc.retained r S (RetainedWords.eventAt r hr S x i))) := by
    have hs₁ : (List.ofFn (fun i : Fin (Fintype.card (RetainedWords.Corner r hr S x)) => (E i).val)).Sorted (· < ·) := by
      apply List.sorted_lt_ofFn_iff.mpr
      intro i j hij
      exact E.strictMono hij
    have hs₂ : ((List.ofFn (fun i : RetainedWords.Coord r hr S x => i)).filter
        (fun i => decide (ActiveArc.retained r S (RetainedWords.eventAt r hr S x i)))).Sorted (· < ·) :=
      (List.sorted_lt_ofFn_iff.mpr strictMono_id).filter _
    apply List.Sorted.eq_of_mem_iff hs₁ hs₂
    intro i
    constructor
    · intro hi
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
      have hret := (E j).property
      rw [hj] at hret
      exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,by simpa using hret⟩
    · intro hi
      obtain ⟨_,hret⟩ := List.mem_filter.mp hi
      have hret' : ActiveArc.retained r S (RetainedWords.eventAt r hr S x i) := by simpa using hret
      let c : RetainedWords.Corner r hr S x := ⟨i,hret'⟩
      exact List.mem_ofFn.mpr ⟨E.symm c,by simp [c]⟩
  have hmapped := congrArg (List.map (RetainedWords.eventAt r hr S x)) hcoords
  have hevents : List.ofFn (RetainedWords.cornerEvent r hr S x)=
      (orbitWord (ActiveArc.incoming r hr.noTriple S) x).filter (fun z => decide (ActiveArc.retained r S z)) := by
    change List.ofFn (fun i => RetainedWords.eventAt r hr S x (E i).val)=
      (List.ofFn (RetainedWords.eventAt r hr S x)).filter (fun z => decide (ActiveArc.retained r S z))
    simpa only [List.map_ofFn,Function.comp_def] using
      hmapped.trans (DaughterPointListFilter.map_filter_comp (RetainedWords.eventAt r hr S x)
        (fun z => decide (ActiveArc.retained r S z)) (List.ofFn fun i : RetainedWords.Coord r hr S x => i))
  have hpoints := congrArg (List.map (ActiveArc.eventPoint r)) hevents
  simpa [RetainedWords.vertex,r,hr,List.map_ofFn] using hpoints

/-- Exact retained point-word transport to the genuine daughter rooted at its paired event. -/
theorem daughterPointList_eq_retainedWord (x : ActiveArc.Event (cutArc q e)) :
    DaughterFirstReturn.daughterPointList q hq.g2 (mappedSupport q e hq he S)
      (dartEventEquiv q e hq he S x)=
        List.ofFn (RetainedWords.vertex (cutArc q e) (cutArc_regular q e hq) S x) := by
  exact (daughterPointList_eq_active_filtered q e hq he S x).trans
    (active_retainedWord_eq_filtered q e hq S x).symm

/-- The open retained word is rooted at the actual anchor immediately after the removed edge. -/
theorem open_daughterPointList_eq_retainedWord :
    DaughterFirstReturn.daughterPointList q hq.g2 (mappedSupport q e hq he S)
      (Sum.inl (cyclicSuccessor e))=
        List.ofFn (RetainedWords.vertex (cutArc q e) (cutArc_regular q e hq) S (ActiveArc.start (cutArc q e))) := by
  have hh := daughterPointList_eq_retainedWord q e hq he S (ActiveArc.start (cutArc q e))
  have hx : dartEventEquiv q e hq he S (ActiveArc.start (cutArc q e))=Sum.inl (cyclicSuccessor e) := rfl
  rw [hx] at hh
  exact hh

/-- Three matched retained points preserve their actual corner determinant exactly. -/
theorem dartEventEquiv_corner_det (x y z : ActiveArc.Event (cutArc q e)) :
    planarDet (polygonEventPoint q (dartEventEquiv q e hq he S y)-polygonEventPoint q (dartEventEquiv q e hq he S x))
      (polygonEventPoint q (dartEventEquiv q e hq he S z)-polygonEventPoint q (dartEventEquiv q e hq he S y))=
    planarDet (ActiveArc.eventPoint (cutArc q e) y-ActiveArc.eventPoint (cutArc q e) x)
      (ActiveArc.eventPoint (cutArc q e) z-ActiveArc.eventPoint (cutArc q e) y) := by
  rw [dartEventEquiv_point,dartEventEquiv_point,dartEventEquiv_point]

end DirectGLSSW.ActiveArc.ExposedChart
