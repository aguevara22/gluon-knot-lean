import FilteredCoordinateGap
import ActiveArcCoordinateGapOrder

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.RetainedWords
open DirectGLSSW ActiveArc PermutationOrbits FiniteFirstReturn
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- Literal event-prefix retention counts determine the physical retained
gap around an omitted event, via ordered coordinates and first return. -/
theorem open_gap_of_filtered_prefix_count
    (j : Coord q hR S (start q)) (hj : ¬retained q S (eventAt q hR S (start q) j))
    (m : ℕ) (hm0 : 0<m) (hmM : m<openCount q hR S)
    (hm : (((orbitWord (incoming q hR.noTriple S) (start q)).take j.val).filter
      (fun x => decide (retained q S x))).length=m) :
    (eventOrder q hR.noTriple).lt
      (pairing q S (cornerEvent q hR S (start q) ⟨m-1,by change m-1<openCount q hR S;omega⟩))
      (eventAt q hR S (start q) j) ∧
    (eventOrder q hR.noTriple).lt (eventAt q hR S (start q) j)
      (cornerEvent q hR S (start q) ⟨m,hmM⟩) := by
  let P : Coord q hR S (start q) → Prop := fun i => retained q S (eventAt q hR S (start q) i)
  let e := fun i : Fin (openCount q hR S) => (enumeration q hR S (start q) i).val
  have he := cornerCoordinateList_eq_filter q hR S (start q)
  have hmap := DaughterPointListFilter.map_filter_comp (eventAt q hR S (start q))
    (fun x => decide (retained q S x))
    ((List.ofFn (fun i : Coord q hR S (start q) => i)).take j.val)
  have hlength := congrArg List.length hmap
  simp only [List.map_take,List.map_ofFn,List.length_map] at hlength
  have hm' : (((List.ofFn (fun i : Coord q hR S (start q) => i)).take j.val).filter
      (fun i => decide (P i))).length=m := by
    exact hlength.trans hm
  have hbr := filtered_coordinate_bracket P e he j hj m hm' hm0 hmM
  have hkn : m-1+1<openCount q hR S := by omega
  have horder := open_coordinate_gap_order q hR S (m-1) hkn j hbr.1
    (by simpa only [Nat.sub_add_cancel (by omega : 1≤m)] using hbr.2)
  simpa only [Nat.sub_add_cancel (by omega : 1≤m)] using horder

end DirectGLSSW.ActiveArc.RetainedWords
