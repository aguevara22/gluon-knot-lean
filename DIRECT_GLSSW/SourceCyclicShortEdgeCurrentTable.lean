import SourceShortEdgeCurrentTable
import DirectGLSSW.ShortEdgeInsertionRotation
import DirectGLSSW.ShortEdgeDirectionExistence

namespace DirectGLSSW.ShortEdgeCurrentGeometry

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeInsertionRotation
open DirectGLSSW.ShortEdgeWeighted

/-- Root the cyclic word two positions before the designated vertex. The
literal opened word then places that vertex at index 1, with its predecessor
at index 0. -/
noncomputable def sourceCoreWordBefore {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint ℝ) (a : Fin n) : ℕ → PlanarPoint ℝ :=
  rootedPolygonWord q (coreRootBefore hn a)

theorem sourceCoreWordBefore_one {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint ℝ) (a : Fin n) :
    sourceCoreWordBefore hn q a 1 = q a := by
  change q (cyclicVertexIndex (coreRootBefore hn a) 1) = q a
  rw [coreRootBefore_index1 hn a]

/-- The opened word is the last-root presentation of the cyclic relabelling
used by the insertion-rotation identity. -/
theorem sourceCoreWordBefore_eq_lastRoot_relabel {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint ℝ) (a : Fin n) (k : ℕ) :
    sourceCoreWordBefore hn q a k =
      rootedPolygonWord
        (fun j => q (cyclicVertexEquiv (coreRootBefore hn a) j))
        (lastCoreRoot (by omega : 0 < n)) k := by
  apply congrArg q
  apply Fin.ext
  change ((coreRootBefore hn a).val + 1 + k) % n =
      ((coreRootBefore hn a).val + 1 +
        ((n - 1 + 1 + k) % n)) % n
  have hlast : n - 1 + 1 = n := by omega
  rw [hlast]
  simp [Nat.add_mod]

/-- The actual cyclic insertion, after the source root rotation, is exactly
the finite open insertion consumed by the current-table theorem. -/
theorem sourceCoreWordBefore_insertCyclicAfter_rotated {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a : Fin n)
    (ε : ℝ) (v : PlanarPoint ℝ) (i : Fin (n + 1)) :
    insertCyclicAfter q a ε v
        (cyclicVertexEquiv (parentRootBefore hn a) i) =
      ShortEdgeSignStability.insertAfter
        (sourceCoreWordBefore hn q a) 1 ε v i.val := by
  let qρ : Fin n → PlanarPoint ℝ :=
    fun j => q (cyclicVertexEquiv (coreRootBefore hn a) j)
  rw [insertCyclicAfter_rotated]
  rw [← parentLastRootWord_eval qρ ⟨1, by omega⟩ ε v i.val i.isLt]
  rw [insertedLastRootWord_eq_openInsertAfter (by omega : 0 < n)
    qρ ⟨1, by omega⟩ ε v i.val (by omega)]
  congr 1
  funext k
  exact (sourceCoreWordBefore_eq_lastRoot_relabel hn q a k).symm

/-- Every cyclically indexed source vertex is covered: choose the literal
root preceding its predecessor, so the finite linear current-table API sees
the designated vertex at index 1. The inserted far array is the actual sign
array of the rotated cyclic insertion, by `insertedLastRootWord_eq_openInsertAfter`.
-/
theorem source_cyclic_exists_shortEdge_actual_current_table
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (hq : cyclicNoncollinear q) (a : Fin n) (v : PlanarPoint ℝ)
    (havoid : ∀ x : Fin n, x ≠ a → planarDet v (q x - q a) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ i j : ℕ, i < j → j ≤ n →
        ordinaryCurrent
            (D1 1 (ShortEdgeSignRealization.shortSign
              (sourceCoreWordBefore hn q a) 1 v)
              (H0 (ShortEdgeSignRealization.coreHSign
                (sourceCoreWordBefore hn q a))))
            (polygonSignArray (ShortEdgeSignStability.insertAfter
              (sourceCoreWordBefore hn q a) 1 ε v)) i j =
          parentTable 1 (by omega)
            (ShortEdgeSignRealization.shortSign
              (sourceCoreWordBefore hn q a) 1 v)
            (ordinaryCurrent
              (D0 1 (ShortEdgeSignRealization.shortSign
                (sourceCoreWordBefore hn q a) 1 v)
                (H0 (ShortEdgeSignRealization.coreHSign
                  (sourceCoreWordBefore hn q a))))
              (H0 (ShortEdgeSignRealization.coreHSign
                (sourceCoreWordBefore hn q a)))) i j := by
  classical
  let r : Fin n := coreRootBefore hn a
  let ρ : Fin n ≃ Fin n := cyclicVertexEquiv r
  let qρ : Fin n → PlanarPoint ℝ := q ∘ ρ
  let w : ℕ → PlanarPoint ℝ := sourceCoreWordBefore hn q a
  have hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e) :=
    cyclicVertexEquiv_commutes_successor r
  have hρa : ρ ⟨1, by omega⟩ = a := by
    change cyclicVertexIndex r 1 = a
    exact coreRootBefore_index1 hn a
  have hqρ : cyclicNoncollinear qρ :=
    cyclicNoncollinear_relabel q ρ hρ hq
  have hcore : ShortEdgeSignStability.CoreHGeneric w (n - 1) := by
    intro i k j hik hkj hj
    have hroot := rootedPolygonWord_noncollinear q hq r i k j (by omega) hik hkj hj
    exact hroot
  have havoidρ : ∀ x : Fin n, x ≠ ⟨1, by omega⟩ →
      planarDet v (qρ x - qρ ⟨1, by omega⟩) ≠ 0 := by
    intro x hx
    change planarDet v (q (ρ x) - q (ρ ⟨1, by omega⟩)) ≠ 0
    rw [hρa]
    apply havoid
    intro hxa
    apply hx
    apply ρ.injective
    simpa [hρa] using hxa
  have hdir : ShortEdgeSignStability.DirectionGeneric w (n - 1) 1 v := by
    intro x hx hx1
    have hxlt : x < n := by omega
    let xC : Fin n := cyclicVertexIndex r x
    have hxC : xC ≠ a := by
      intro hxa
      have heq : cyclicVertexIndex r x = cyclicVertexIndex r 1 := by
        change xC = a at hxa
        rw [← coreRootBefore_index1 hn a] at hxa
        exact hxa
      have hidx := cyclicVertexIndex_injective r hxlt (by omega : 1 < n) heq
      exact hx1 hidx
    change planarDet v (q xC - q (cyclicVertexIndex r 1)) ≠ 0
    rw [coreRootBefore_index1 hn a]
    exact havoid xC hxC
  have ha : 0 < 1 := by omega
  have haN : 1 ≤ n - 1 := by omega
  obtain ⟨δ, hδ, htable⟩ := source_exists_shortEdge_actual_current_table
    w (n - 1) 1 v ha haN hcore hdir
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ i j hij hj
  have hj' : j ≤ (n - 1) + 1 := by omega
  simpa [w, sourceCoreWordBefore] using htable ε hε hεδ i j hij hj'

end DirectGLSSW.ShortEdgeCurrentGeometry
