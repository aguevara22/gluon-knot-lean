import DirectGLSSW.ShortEdgeCyclicGeometry
import DirectGLSSW.ShortEdgeCyclicRelabel

namespace DirectGLSSW.ShortEdgeInsertionRotation

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeCutFibers

def coreRootBefore {n : ℕ} (hn : 3 ≤ n) (a : Fin n) : Fin n :=
  ⟨if 2 ≤ a.val then a.val - 2 else n + a.val - 2, by
    have ha := a.isLt
    split_ifs <;> omega⟩

def parentRootBefore {n : ℕ} (hn : 3 ≤ n) (a : Fin n) : Fin (n + 1) :=
  ⟨if 2 ≤ a.val then a.val - 2 else (n + 1) + a.val - 2, by
    have ha := a.isLt
    split_ifs <;> omega⟩

theorem coreRootBefore_index1 {n : ℕ} (hn : 3 ≤ n) (a : Fin n) :
    cyclicVertexIndex (coreRootBefore hn a) 1 = a := by
  apply Fin.ext
  change ((coreRootBefore hn a).val + 1 + 1) % n = a.val
  by_cases ha2 : 2 ≤ a.val
  · simp only [coreRootBefore, if_pos ha2]
    have hs : a.val - 2 + 1 + 1 = a.val := by omega
    rw [hs, Nat.mod_eq_of_lt a.isLt]
  · simp only [coreRootBefore, if_neg ha2]
    have hs : n + a.val - 2 + 1 + 1 = n + a.val := by omega
    rw [hs, Nat.add_mod]
    simp [Nat.mod_eq_of_lt a.isLt]

theorem parentRootBefore_index2 {n : ℕ} (hn : 3 ≤ n) (a : Fin n) :
    cyclicVertexIndex (parentRootBefore hn a) 2 = ⟨a.val + 1, by omega⟩ := by
  apply Fin.ext
  change ((parentRootBefore hn a).val + 1 + 2) % (n + 1) = a.val + 1
  by_cases ha2 : 2 ≤ a.val
  · simp only [parentRootBefore, if_pos ha2]
    have hs : a.val - 2 + 1 + 2 = a.val + 1 := by omega
    rw [hs, Nat.mod_eq_of_lt (by omega)]
  · simp only [parentRootBefore, if_neg ha2]
    have hs : (n + 1) + a.val - 2 + 1 + 2 = (n + 1) + (a.val + 1) := by omega
    rw [hs, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : a.val + 1 < n + 1)]

theorem parentIndex_collapse {n : ℕ} (hn : 3 ≤ n) (a : Fin n)
    (k : ℕ) (hk : k < n + 1) :
    collapseFin a (cyclicVertexIndex (parentRootBefore hn a) k) =
      cyclicVertexIndex (coreRootBefore hn a) (collapseAfter 1 k) := by
  have hkcore : collapseAfter 1 k < n := by
    unfold collapseAfter
    split_ifs <;> omega
  apply Fin.ext
  change collapseAfter a.val (cyclicVertexIndex (parentRootBefore hn a) k).val =
    (cyclicVertexIndex (coreRootBefore hn a) (collapseAfter 1 k)).val
  rw [cyclicVertexIndex_val (parentRootBefore hn a) hk,
    cyclicVertexIndex_val (coreRootBefore hn a) hkcore]
  by_cases ha2 : 2 ≤ a.val
  · simp [parentRootBefore, coreRootBefore, ha2, collapseAfter]
    split_ifs <;> omega
  · have ha01 : a.val = 0 ∨ a.val = 1 := by omega
    rcases ha01 with ha0 | ha1
    · simp [parentRootBefore, coreRootBefore, ha2, ha0, collapseAfter] <;>
        split_ifs <;> omega
    · simp [parentRootBefore, coreRootBefore, ha2, ha1, collapseAfter] <;>
        split_ifs <;> omega

private theorem insertCyclicAfter_eq_collapseFin_of_ne_newB {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a : Fin n) (ε : ℝ) (v : PlanarPoint ℝ)
    (i : Fin (n + 1)) (hi : i ≠ ⟨a.val + 1, by omega⟩) :
    insertCyclicAfter q a ε v i = q (collapseFin a i) := by
  by_cases hle : i.val ≤ a.val
  · simp only [insertCyclicAfter, dif_pos hle]
    congr 1
    apply Fin.ext
    simp [collapseFin, collapseAfter, hle]
  · have hmid : i.val ≠ a.val + 1 := by
      intro h
      exact hi (Fin.ext h)
    simp [insertCyclicAfter, collapseFin, collapseAfter, hle, hmid]

theorem insertCyclicAfter_rotated {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (a : Fin n) (ε : ℝ) (v : PlanarPoint ℝ) (i : Fin (n + 1)) :
    insertCyclicAfter q a ε v
        (cyclicVertexEquiv (parentRootBefore hn a) i) =
      insertCyclicAfter (fun j => q (cyclicVertexEquiv (coreRootBefore hn a) j))
        ⟨1, by omega⟩ ε v i := by
  let b : Fin (n + 1) := ⟨a.val + 1, by omega⟩
  let i₂ : Fin (n + 1) := ⟨2, by omega⟩
  have hb : cyclicVertexIndex (parentRootBefore hn a) 2 = b := by
    simpa [b] using parentRootBefore_index2 hn a
  have hrot₂ : cyclicVertexEquiv (parentRootBefore hn a) i₂ = b := by
    simpa [cyclicVertexEquiv, i₂, b] using hb
  by_cases hi₂ : i = i₂
  · subst i
    rw [hrot₂]
    have hcoreOne : cyclicVertexEquiv (coreRootBefore hn a) (⟨1, by omega⟩ : Fin n) = a := by
      change cyclicVertexIndex (coreRootBefore hn a) 1 = a
      exact coreRootBefore_index1 hn a
    simp [insertCyclicAfter, b, i₂, hcoreOne]
  · have hleftB : cyclicVertexEquiv (parentRootBefore hn a) i ≠ b := by
      intro h
      apply hi₂
      apply (Equiv.injective (cyclicVertexEquiv (parentRootBefore hn a)))
      simpa [hrot₂] using h
    have hrightB : i ≠ ⟨2, by omega⟩ := by
      intro h
      apply hi₂
      simpa [i₂] using h
    have hleft := insertCyclicAfter_eq_collapseFin_of_ne_newB q a ε v
      (cyclicVertexEquiv (parentRootBefore hn a) i) hleftB
    have hright := insertCyclicAfter_eq_collapseFin_of_ne_newB
      (fun j => q (cyclicVertexEquiv (coreRootBefore hn a) j)) ⟨1, by omega⟩ ε v i hrightB
    rw [hleft, hright]
    have hparent : cyclicVertexEquiv (parentRootBefore hn a) i =
        cyclicVertexIndex (parentRootBefore hn a) i.val := rfl
    have hcore : cyclicVertexEquiv (coreRootBefore hn a) (collapseFin ⟨1, by omega⟩ i) =
        cyclicVertexIndex (coreRootBefore hn a) (collapseAfter 1 i.val) := rfl
    change q (collapseFin a (cyclicVertexEquiv (parentRootBefore hn a) i)) =
      q (cyclicVertexEquiv (coreRootBefore hn a) (collapseFin ⟨1, by omega⟩ i))
    rw [hparent, hcore, ← parentIndex_collapse hn a i.val i.isLt]

end DirectGLSSW.ShortEdgeInsertionRotation
