import ActiveArcExposedSupports
import DirectGLSSW.OpenMarkedCurrent
import DirectGLSSW.RealPolygons

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

abbrev Support := Nonalternation.Support q hR
abbrev Components (S : Support q hR) := Component (incoming q hR.noTriple S.val)
abbrev OpenVertex (S : Support q hR) := RetainedWords.vertex q hR S.val (start q)
abbrev ClosedVertex (S : Support q hR) (C : Components q hR S)
    (hc : C≠openComponent q hR.noTriple S.val) :=
  RetainedWords.vertex q hR S.val (closedRoot q hR.noTriple S.val C hc)

/-- The ordinary signed interval-cut current of the true retained open word.
The total word extension wraps indices; all used interval indices lie in its one traversal. -/
def openCurrent (S : Support q hR) : ℚ :=
  OpenMarkedCurrent.entry (polygonSignArray
    (rootedPolygonWord (OpenVertex q hR S) (RetainedWords.openLast q hR S.val)))
      0 (RetainedWords.openCount q hR S.val-1)

/-- Reading from the final retained index gives the original ordered open word in range. -/
theorem openCurrent_word (S : Support q hR) (k : ℕ)
    (hk : k<RetainedWords.openCount q hR S.val) :
    rootedPolygonWord (OpenVertex q hR S) (RetainedWords.openLast q hR S.val) k=
      OpenVertex q hR S ⟨k,hk⟩ := by
  unfold rootedPolygonWord
  congr 1
  apply Fin.ext
  change ((RetainedWords.openCount q hR S.val-1)+1+k)%RetainedWords.openCount q hR S.val=k
  have hp := RetainedWords.open_count_ge_two q hR S.val
  rw [Nat.sub_add_cancel (by omega),Nat.add_mod_left,Nat.mod_eq_of_lt hk]

/-- Only actual closed retained daughter polygons need the source auxiliary genericity. -/
def ClosedAuxiliary : Prop :=
  ∀ S : Support q hR, ∀ C : Components q hR S,
    ∀ hc : C≠openComponent q hR.noTriple S.val, CyclicGeneric (ClosedVertex q hR S C hc)

/-- Actual closed amplitude; the open orbit's neutral extension is excluded from the product. -/
def closedWeight (hAux : ClosedAuxiliary q hR) (S : Support q hR) (C : Components q hR S) : ℚ :=
  if hc : C≠openComponent q hR.noTriple S.val then
    polygonAmplitude (ClosedVertex q hR S C hc) (hAux S C hc) else 1

/-- Source ΓM: physical nonalternating supports, one true open M, and actual closed A factors. -/
def GammaM (hAux : ClosedAuxiliary q hR) : ℚ :=
  ∑ S : Support q hR, (-1 : ℚ)^S.val.card *
    (openCurrent q hR S * ∏ C ∈ Finset.univ.erase (openComponent q hR.noTriple S.val),
      closedWeight q hR hAux S C)

theorem GammaM_closed_factor_count (S : Support q hR) :
    (Finset.univ.erase (openComponent q hR.noTriple S.val)).card=S.val.card :=
  Nonalternation.closed_component_count q hR S

end DirectGLSSW.ActiveArc.Primitive
