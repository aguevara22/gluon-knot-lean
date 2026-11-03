import DirectGLSSW.FinitePhiInverse
import DirectGLSSW.NearData
import DirectGLSSW.RealPolygons
import DirectGLSSW.TreeWeights

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW

/-- The public finite carrier for strict upper-triangular source intervals `0..N`. -/
abbrev FiniteIntervalValues0N (N : ℕ) := FiniteIntervalValues 0 N

/-- The finite restriction of the source array to legal interval pairs. -/
def finiteSourceValues0N (N : ℕ) : FiniteIntervalValues0N N :=
  fun p => source p.val.1.val p.val.2.val

/-- The existing finite triangular map has a unique preimage of the actual source. -/
theorem existsUnique_finitePhi_source (D H : TripleArray) (N : ℕ) :
    ∃! X : FiniteIntervalValues0N N,
      finitePhi D H 0 N X = finiteSourceValues0N N := by
  exact existsUnique_finitePhi_preimage D H 0 N (finiteSourceValues0N N)

private theorem finiteIntervalExtension0N_apply (N : ℕ)
    (X : FiniteIntervalValues0N N) (p : FiniteIntervalPair 0 N) :
    finiteIntervalExtension 0 N X p.val.1.val p.val.2.val = X p := by
  unfold finiteIntervalExtension
  have hvalid : 0 ≤ p.val.1.val ∧ p.val.1.val < p.val.2.val ∧ p.val.2.val ≤ N := by
    refine ⟨p.property.1, p.property.2, ?_⟩
    have hj := p.val.2.isLt
    omega
  rw [dif_pos hvalid]

/-- Every finite source preimage agrees entrywise with the ordinary current. -/
theorem finitePhi_source_eq_ordinaryCurrent (D H : TripleArray) (N : ℕ)
    (X : FiniteIntervalValues0N N)
    (hX : finitePhi D H 0 N X = finiteSourceValues0N N)
    (p : FiniteIntervalPair 0 N) :
    X p = ordinaryCurrent D H p.val.1.val p.val.2.val := by
  have hwindow : ∀ i j, 0 ≤ i → i < j → j ≤ N →
      phi D H (finiteIntervalExtension 0 N X) i j = source i j := by
    intro i j hi hij hj
    let p : FiniteIntervalPair 0 N :=
      ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), ⟨hi, hij⟩⟩
    calc
      phi D H (finiteIntervalExtension 0 N X) i j = finitePhi D H 0 N X p := rfl
      _ = finiteSourceValues0N N p := congrFun hX p
      _ = source i j := rfl
  have hunique := ordinaryCurrent_unique_on_interval D H
      (finiteIntervalExtension 0 N X) 0 N hwindow
  calc
    X p = finiteIntervalExtension 0 N X p.val.1.val p.val.2.val :=
      (finiteIntervalExtension0N_apply N X p).symm
    _ = ordinaryCurrent D H p.val.1.val p.val.2.val :=
      hunique _ _ p.property.1 p.property.2 (by have h := p.val.2.isLt; omega)

/-- The concrete marked output has the exact finite inverse form of `ep:near-free`. -/
theorem markedAmplitude_near_free_source (D H : TripleArray)
    {i j : ℕ} (hij : i < j) :
    markedAmplitude D H i j =
      phi (fun _ _ _ => (0 : ℚ)) (fun a b c => -H a b c)
        (inverseCurrent (fun _ _ _ => (0 : ℚ)) H source) i j := by
  calc
    markedAmplitude D H i j =
        markedAmplitude (fun _ _ _ => (0 : ℚ)) H i j :=
      markedAmplitude_zero_near D H hij
    _ = phi (fun _ _ _ => (0 : ℚ)) (fun a b c => -H a b c)
          (ordinaryCurrent (fun _ _ _ => (0 : ℚ)) H) i j := rfl
    _ = phi (fun _ _ _ => (0 : ℚ)) (fun a b c => -H a b c)
          (inverseCurrent (fun _ _ _ => (0 : ℚ)) H source) i j := by
      apply phi_congr_upper
      · intro a b hab
        have hwindow := ordinaryCurrent_unique_on_interval
          (fun _ _ _ => (0 : ℚ)) H
          (inverseCurrent (fun _ _ _ => (0 : ℚ)) H source) a b
          (by
            intro x y _ hxy _
            exact inverseCurrent_phi (fun _ _ _ => (0 : ℚ)) H source x y)
        exact (hwindow a b le_rfl hab le_rfl).symm
      · exact hij

/-- At the defining root, the real polygon amplitude has the exact near-free
array inverse form, with no root-independence premise. -/
theorem polygonAmplitude_near_free_source {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq =
      phi (fun _ _ _ => (0 : ℚ))
        (fun a b c => -polygonSignArray
          (rootedPolygonWord q ⟨0, by have hsize := hq.size_ge_three; omega⟩) a b c)
        (inverseCurrent (fun _ _ _ => (0 : ℚ))
          (polygonSignArray
            (rootedPolygonWord q ⟨0, by have hsize := hq.size_ge_three; omega⟩))
          source) 0 (n - 1) := by
  let H : TripleArray :=
    polygonSignArray
      (rootedPolygonWord q ⟨0, by have hsize := hq.size_ge_three; omega⟩)
  calc
    polygonAmplitude q hq = markedTreeSum H H 0 (n - 1) := by
      simpa [H] using polygonAmplitude_eq_markedTreeSum q hq
    _ = markedAmplitude H H 0 (n - 1) :=
      markedTreeSum_eq_markedAmplitude H H (by have hsize := hq.size_ge_three; omega)
    _ = phi (fun _ _ _ => (0 : ℚ)) (fun a b c => -H a b c)
          (inverseCurrent (fun _ _ _ => (0 : ℚ)) H source) 0 (n - 1) :=
      markedAmplitude_near_free_source H H (by have hsize := hq.size_ge_three; omega)

end DirectGLSSW
