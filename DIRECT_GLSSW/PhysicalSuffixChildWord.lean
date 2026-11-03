import PhysicalSuffixCrossingData
import PhysicalClosedSingletonRoot
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalKnotSplit
open Split Cursor PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {A a b : ℕ} (q : Fin (A+(a+b)+2) → PlanarPoint ℝ) (hR : Regular q)
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1)
    (hM : Regular (moveStart (suffixWord q A (a+b) rfl) θ))
    (d : Crossing (moveStart (suffixWord q A (a+b) rfl) θ))
    (hd0 : d.val.1=0) (hdcut : d.val.2.val=a)

theorem physical_child_suffix_word :
    List.ofFn (child (moveStart (suffixWord q A (a+b) rfl) θ) hM d hd0 hdcut) =
      crossingPoint q (suffixWordCrossingEquiv q hR A (a+b) rfl θ h0 h1 d).val ::
        List.ofFn (fun i : Fin a => q ⟨A+i.val+1,by omega⟩) := by
  rw [List.ofFn_succ, child_zero]
  rw [suffixWordCrossingEquiv_point q hR A (a+b) rfl θ h0 h1 d]
  congr 1

theorem mapped_singleton_closed_word_isRotated_child (x : Event q)
    (hx : componentOf (incoming q hR.noTriple
      {(suffixWordCrossingEquiv q hR A (a+b) rfl θ h0 h1 d).val}) x ≠
      openComponent q hR.noTriple {(suffixWordCrossingEquiv q hR A (a+b) rfl θ h0 h1 d).val}) :
    List.ofFn (RetainedWords.vertex q hR
      {(suffixWordCrossingEquiv q hR A (a+b) rfl θ h0 h1 d).val} x) ~r
      List.ofFn (child (moveStart (suffixWord q A (a+b) rfl) θ) hM d hd0 hdcut) := by
  rw [physical_child_suffix_word q hR θ h0 h1 hM d hd0 hdcut]
  let z := (suffixWordCrossingEquiv q hR A (a+b) rfl θ h0 h1 d).val
  have hl : z.val.1.val=A := by
    rw [suffixWordCrossingEquiv_left_label,hd0]
    simp
  have hr : z.val.2.val=A+a := by
    rw [suffixWordCrossingEquiv_right_label,hdcut]
  have hh := closed_singleton_word_offset_isRotated (a:=A) (b:=a+b) q hR z x hx
  have he : z.val.2.val-z.val.1.val=a := by omega
  have hw : List.ofFn (fun i : Fin (z.val.2.val-z.val.1.val) =>
      q ⟨z.val.1.val+i.val+1,by have := z.val.2.isLt;omega⟩) =
      List.ofFn (fun i : Fin a => q ⟨A+i.val+1,by omega⟩) := by
    rw [List.ofFn_congr he]
    apply congrArg List.ofFn
    funext i
    congr 1
    apply Fin.ext
    simp [hl]
  simpa only [hw] using hh
end DirectGLSSW.ActiveArc.PhysicalKnotSplit
