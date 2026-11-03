import ActiveArcRetainedEventFilter
import ActiveArcRetainedCrossingLocality

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.RetainedWords
open DirectGLSSW ActiveArc PermutationOrbits PhysicalSegments FiniteFirstReturn
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- Strict physical order throughout a first-return gap, derived from the
actual nonretained successor steps. -/
theorem firstReturn_iterates_strict (x : Event q) (d i j : ℕ)
    (hi : 0 < i) (hij : i < j) (hjd : j ≤ d)
    (hno : ∀ k, 0<k → k<d → ¬retained q S ((incoming q hR.noTriple S ^ k) x)) :
    (eventOrder q hR.noTriple).lt ((incoming q hR.noTriple S ^ i) x)
      ((incoming q hR.noTriple S ^ j) x) := by
  letI := eventOrder q hR.noTriple
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : i=j
    · subst j
      exact firstReturn_prefix_step q hR S x d i hi (by omega) hno
    · exact lt_trans (ih (by omega) (by omega))
        (firstReturn_prefix_step q hR S x d j (by omega) (by omega) hno)

/-- Orbit-coordinate bracketing between consecutive retained labels yields
strict physical event order in that exact nonclosing open side. -/
theorem open_coordinate_gap_order
    (k : ℕ) (hkn : k+1<openCount q hR S) (j : Coord q hR S (start q))
    (hj0 : (enumeration q hR S (start q) ⟨k,by change k<openCount q hR S;omega⟩).val.val<j.val)
    (hj1 : j.val<(enumeration q hR S (start q) ⟨k+1,hkn⟩).val.val) :
    (eventOrder q hR.noTriple).lt
      (pairing q S (cornerEvent q hR S (start q) ⟨k,by change k<openCount q hR S;omega⟩))
      (eventAt q hR S (start q) j) ∧
    (eventOrder q hR.noTriple).lt (eventAt q hR S (start q) j)
      (cornerEvent q hR S (start q) ⟨k+1,hkn⟩) := by
  let i : Fin (openCount q hR S) := ⟨k,by omega⟩
  let z := enumeration q hR S (start q) i
  let z' := enumeration q hR S (start q) ⟨k+1,hkn⟩
  have hn : nextCorner q hR S (start q) z=z' := by
    have h := enumeration_cyclic q hR S (start q) i
    have hs : cyclicSuccessor i=⟨k+1,hkn⟩ := by
      apply Fin.ext
      simp only [cyclicSuccessor,cyclicVertexIndex,Nat.add_zero,i]
      exact Nat.mod_eq_of_lt hkn
    rw [hs] at h
    exact h.symm
  change z.val.val < j.val at hj0
  change j.val < z'.val.val at hj1
  have hzz : z.val.val<z'.val.val := lt_trans hj0 hj1
  have hd : cornerGap q hR S (start q) z = z'.val.val-z.val.val := by
    unfold cornerGap
    rw [hn]
    exact if_pos hzz
  let m := forwardGap z.val j
  have hm : m=j.val-z.val.val := if_pos hj0
  have hm0 : 0<m := forwardGap_pos _ _
  have hmd : m<cornerGap q hR S (start q) z := by rw [hm,hd];omega
  have hiter : (incoming q hR.noTriple S ^ m) (eventAt q hR S (start q) z.val)=
      eventAt q hR S (start q) j := by
    rw [← eventAt_iterate]
    exact congrArg (eventAt q hR S (start q)) (cyclicSuccessor_pow_forwardGap z.val j)
  have hx : eventAt q hR S (start q) z.val≠terminal q := open_nonlast_ne_terminal q hR S i hkn
  have hf := corner_firstReturn q hR S (start q) z
  have hlow := (firstReturn_prefix_bounded q hR S _ hx _ hf.2.2 m hm0 hmd.le).1
  have hupp := firstReturn_iterates_strict q hR S _ _ m _ hm0 hmd le_rfl hf.2.2
  rw [hiter] at hlow hupp
  rw [hf.2.1,hn] at hupp
  exact ⟨hlow,hupp⟩

end DirectGLSSW.ActiveArc.RetainedWords
