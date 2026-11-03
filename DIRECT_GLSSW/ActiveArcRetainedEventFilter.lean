import ActiveArcCompatibleWordSplice

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.RetainedWords
open DirectGLSSW ActiveArc PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q)) (root : Event q)

/-- The ordered retained-coordinate enumeration is the ambient orbit list
filtered by the actual retained-event predicate. -/
theorem cornerCoordinateList_eq_filter :
    List.ofFn (fun i : Fin (Fintype.card (Corner q hR S root)) =>
      (enumeration q hR S root i).val) =
      (List.ofFn (fun i : Coord q hR S root => i)).filter
        (fun i => decide (retained q S (eventAt q hR S root i))) := by
  classical
  let e := enumeration q hR S root
  have hs₁ : (List.ofFn (fun i : Fin (Fintype.card (Corner q hR S root)) => (e i).val)).Sorted (· < ·) := by
    apply List.sorted_lt_ofFn_iff.mpr
    intro i j hij
    change (e i).val < (e j).val
    exact e.strictMono hij
  have hs₂ : ((List.ofFn (fun i : Coord q hR S root => i)).filter
      (fun i => decide (retained q S (eventAt q hR S root i)))).Sorted (· < ·) :=
    (List.sorted_lt_ofFn_iff.mpr strictMono_id).filter _
  apply List.Sorted.eq_of_mem_iff hs₁ hs₂
  intro i
  constructor
  · intro hi
    rcases List.mem_ofFn.mp hi with ⟨j,hj⟩
    have hret : retained q S (eventAt q hR S root (e j).val) := (e j).property
    rw [hj] at hret
    exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,by simpa using hret⟩
  · intro hi
    rcases List.mem_filter.mp hi with ⟨_,hret⟩
    have hret' : retained q S (eventAt q hR S root i) := by simpa using hret
    let c : Corner q hR S root := ⟨i,hret'⟩
    refine List.mem_ofFn.mpr ⟨e.symm c,?_⟩
    simp [e,c]

/-- Exact event labels in the retained word, before applying eventPoint. -/
theorem cornerEventList_eq_filtered_orbitWord :
    List.ofFn (cornerEvent q hR S root) =
      (orbitWord (incoming q hR.noTriple S) root).filter
        (fun x => decide (retained q S x)) := by
  classical
  have hcoords := cornerCoordinateList_eq_filter q hR S root
  have hmapped := congrArg (List.map (eventAt q hR S root)) hcoords
  have hword : orbitWord (incoming q hR.noTriple S) root =
      List.ofFn (eventAt q hR S root) := rfl
  calc
    List.ofFn (cornerEvent q hR S root) =
        (orbitWord (incoming q hR.noTriple S) root).filter
          (fun x => decide (retained q S x)) := by
      rw [hword]
      simpa only [List.map_ofFn] using hmapped.trans
        (DirectGLSSW.DaughterPointListFilter.map_filter_comp
          (eventAt q hR S root) (fun x => decide (retained q S x))
          (List.ofFn fun i : Coord q hR S root => i))

end DirectGLSSW.ActiveArc.RetainedWords
