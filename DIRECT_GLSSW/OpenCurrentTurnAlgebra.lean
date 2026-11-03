import OpenCurrentShortFirst
import OpenCurrentFirstEdgeFactor

set_option autoImplicit false
namespace DirectGLSSW.OpenCurrentShortFirst

/-- Both conditional cut-list calculations composed: only far-row agreement
remains for the subsequent actual moving-word geometry to supply. -/
theorem entry_short_first (H : TripleArray) (i N : ℕ)
    (hfar : ∀ k j, i+1<k → k<j → j≤N → H i k j=H (i+1) k j)
    (j : ℕ) (hij : i+1<j) (hjN : j≤N) :
    OpenMarkedCurrent.entry H i j=
      (((1+H i (i+1) (i+2))/2)-1) * OpenMarkedCurrent.entry H (i+1) j := by
  apply OpenMarkedCurrent.entry_first_edge_factor H _ hij
  intro k hk hkj
  exact ordinaryCurrent_short_first H i N hfar k hk (hkj.trans hjN)

theorem entry_one_edge (H : TripleArray) (i : ℕ) :
    OpenMarkedCurrent.entry H i (i+1)=1 :=
  OpenMarkedCurrent.entry_adjacent_eq_one H i

end DirectGLSSW.OpenCurrentShortFirst
#check @DirectGLSSW.OpenCurrentShortFirst.phi_eq_weightedCutSum
#check @DirectGLSSW.OpenCurrentShortFirst.weightedCutSum_congr_weights
#check @DirectGLSSW.OpenCurrentShortFirst.ordinaryCurrent_short_first
#check @DirectGLSSW.OpenCurrentShortFirst.entry_short_first


