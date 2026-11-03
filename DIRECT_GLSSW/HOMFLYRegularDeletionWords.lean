import HOMFLYRegularDeletionComponents
import InsertedRootedWordFilter

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
namespace SignedRegularDeletion
variable {D E : PLLinkDiagram} (R : SignedRegularDeletion D E)

theorem orbitWord_transport (root : Fin D.nArc) :
    orbitWord E.continuation (R.arcMap root) =
      ((orbitWord D.continuation root).filter (fun e => decide (e ≠ R.deleted))).map R.arcMap := by
  classical
  have h := PermutationInsertion.inserted_orbitWord_filter E.continuation D.continuation
    (R.arcMap R.retained) R.deleted R.survivingArcEquiv.symm R.insert_extra
    (fun e => by
      have hs := R.insert_step e
      by_cases hc : E.continuation e = R.arcMap R.retained <;> simpa [hc] using hs) root
  have hdrop : PermutationInsertion.dropPoint (R.arcMap R.retained) R.deleted
      R.survivingArcEquiv.symm root = R.arcMap root := by
    by_cases hr : root = R.deleted
    · subst root
      simp only [PermutationInsertion.dropPoint, dif_pos rfl]
      exact R.map_deleted.symm
    · simp only [PermutationInsertion.dropPoint, dif_neg hr, Equiv.symm_symm]
      rfl
  rw [hdrop] at h
  have hf : (orbitWord D.continuation root).filter (fun e => decide (e ≠ R.deleted)) =
      (orbitWord E.continuation (R.arcMap root)).map
        (fun e => (R.survivingArcEquiv.symm e).val) := by
    trans (orbitWord D.continuation root).filter
      (fun y => @decide (y ≠ R.deleted)
        (@instDecidableNot (y = R.deleted) (Classical.propDecidable (y = R.deleted))))
    · apply List.filter_congr
      intro y hy
      by_cases hd : y = R.deleted <;> simp [hd]
    · exact h
  rw [hf, List.map_map]
  symm
  calc
    _ = (orbitWord E.continuation (R.arcMap root)).map id := by
      apply List.map_congr_left
      intro e he
      exact R.lift_map e
    _ = _ := List.map_id _

end SignedRegularDeletion
end
end DirectGLSSW.HOMFLY


