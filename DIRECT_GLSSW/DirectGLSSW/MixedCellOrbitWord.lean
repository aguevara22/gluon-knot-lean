import DirectGLSSW.MixedConsecutiveCapWord
import FirstCellOrbitWord
import InternalCellOrbitWord
import TerminalCellOrbitWord

set_option autoImplicit false
namespace DirectGLSSW.MixedCellOrbitWord
open MixedConsecutiveCapWord MixedEdgeRetainedWord DaughterFirstReturn

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

theorem daughterPointList_eq_cellEventWord
    (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
    (i : Fin (L.length+1)) :
    daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i) =
      (cellEventWord q hq e L i).map (polygonEventPoint q) := by
  by_cases hzero : L.length = 0
  · have hnil : L = [] := List.length_eq_zero.mp hzero
    subst L
    have hi : i = ⟨0, by omega⟩ := by apply Fin.ext; have hi := i.isLt; omega
    subst i
    exact MixedConsecutiveCapWord.daughterPointList_empty_eq_cellEventWord q hq e
  · have hlen : 0 < L.length := Nat.pos_of_ne_zero hzero
    by_cases hfirst : i.val = 0
    · exact FirstCellOrbitWord.daughterPointList_first_eq_cellEventWord
        q hq e hflat hleft L hL hlen i hfirst
    · by_cases hlast : i.val = L.length
      · exact TerminalCellOrbitWord.daughterPointList_terminal_eq_cellEventWord
          q hq e hflat hleft L hL hlen i hlast
      · have hi0 : 0 < i.val := by omega
        have hiL : i.val < L.length := by omega
        exact InternalCellOrbitWord.daughterPointList_internal_eq_cellEventWord
          q hq e hflat hleft L hL i hi0 hiL

end DirectGLSSW.MixedCellOrbitWord
