import DirectGLSSW.ShortEdgeCurrentTable
import DirectGLSSW.EndpointDirectSource
import SourceShortEdgeFarStability

/-!
# Actual short-edge current table

Compose the geometric one-sided sign stability theorem with the finite
parent-table uniqueness theorem. The near gate arrays are the explicit source
gauge choices; the far array is the actual inserted polygon sign array.
-/

namespace DirectGLSSW.ShortEdgeCurrentGeometry

open DirectGLSSW
open DirectGLSSW.ShortEdgeWeighted

/-- For an actual sufficiently short insertion, the finite source table is the
ordinary current for the chosen pulled-back near array and actual inserted
polygon signs. The bound is the finite parent-word interval `j ≤ N + 1`.
No identity between parent and inserted currents is assumed. -/
theorem source_exists_shortEdge_actual_current_table
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (ha : 0 < a) (haN : a ≤ N)
    (hcore : ShortEdgeSignStability.CoreHGeneric q N)
    (hdir : ShortEdgeSignStability.DirectionGeneric q N a v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ i j : ℕ, i < j → j ≤ N + 1 →
        ordinaryCurrent
            (D1 a (ShortEdgeSignRealization.shortSign q a v)
              (H0 (ShortEdgeSignRealization.coreHSign q)))
            (polygonSignArray (ShortEdgeSignStability.insertAfter q a ε v)) i j =
          parentTable a ha (ShortEdgeSignRealization.shortSign q a v)
            (ordinaryCurrent
              (D0 a (ShortEdgeSignRealization.shortSign q a v)
                (H0 (ShortEdgeSignRealization.coreHSign q)))
              (H0 (ShortEdgeSignRealization.coreHSign q))) i j := by
  obtain ⟨δ, hδ, hstable⟩ :=
    ShortEdgeSignStability.source_shortEdge_far_sign_stability
      q N a v haN hcore hdir
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ i j hij hj
  have hgeom := (hstable ε hε hεδ).2.1
  have hlocal :
      ordinaryCurrent
          (D1 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
          (H1 a (ShortEdgeSignRealization.shortSign q a v)
            (ShortEdgeSignRealization.coreHSign q)) i j =
        ordinaryCurrent
          (D1 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
          (polygonSignArray (ShortEdgeSignStability.insertAfter q a ε v)) i j := by
    apply ordinaryCurrent_congr_interval_fixed_near
    · exact hij
    · intro x k y hix hxk hky hyj
      exact hgeom x k y hxk hky (by omega)
  have htable :=
    ShortEdgeWeighted.CurrentTableImpl.parentTable_eq_ordinaryCurrent
      a ha (ShortEdgeSignRealization.shortSign q a v)
      (H0 (ShortEdgeSignRealization.coreHSign q))
      (ShortEdgeSignRealization.coreHSign q) hij
  exact hlocal.symm.trans htable.symm

/-- The five source interval cases, with the actual inserted ordinary current
on the left. `parentTable` has one collapsed case on the two sides of the
short pair, followed by `AB`, `AY`, `XB`, and strict spanning. -/
theorem source_shortEdge_actual_current_table_cases
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (ha : 0 < a) (haN : a ≤ N)
    (hcore : ShortEdgeSignStability.CoreHGeneric q N)
    (hdir : ShortEdgeSignStability.DirectionGeneric q N a v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      let t := ShortEdgeSignRealization.shortSign q a v
      let H := ShortEdgeSignRealization.coreHSign q
      let D := H0 H
      let U := ordinaryCurrent (D0 a t D) (H0 H)
      let B := ordinaryCurrent (D1 a t D)
        (polygonSignArray (ShortEdgeSignStability.insertAfter q a ε v))
      ∀ i j : ℕ, i < j → j ≤ N + 1 →
        (j ≤ a ∨ a + 1 ≤ i →
          B i j = U (ShortEdgeWeighted.collapseAfter a i)
            (ShortEdgeWeighted.collapseAfter a j)) ∧
        (i = a ∧ j = a + 1 → B i j = 1) ∧
        (i = a ∧ a + 1 < j →
          B i j = ((ShortEdgeWeighted.beta a t - (t (ShortEdgeWeighted.collapseAfter a j)).value) / 2) *
            U a (ShortEdgeWeighted.collapseAfter a j)) ∧
        (i < a ∧ j = a + 1 →
          B i j = ((ShortEdgeWeighted.alpha a ha t - (t i).value) / 2) * U i a) ∧
        (i < a ∧ a + 1 < j →
          B i j = ShortEdgeWeighted.kappa a ha t *
            U i (ShortEdgeWeighted.collapseAfter a j)) := by
  obtain ⟨δ, hδ, hstable⟩ :=
    ShortEdgeSignStability.source_shortEdge_far_sign_stability
      q N a v haN hcore hdir
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  dsimp only
  intro i j hij hj
  have hgeom := (hstable ε hε hεδ).2.1
  have hlocal :
      ordinaryCurrent (D1 a (ShortEdgeSignRealization.shortSign q a v)
          (H0 (ShortEdgeSignRealization.coreHSign q)))
        (H1 a (ShortEdgeSignRealization.shortSign q a v)
          (ShortEdgeSignRealization.coreHSign q)) i j =
      ordinaryCurrent (D1 a (ShortEdgeSignRealization.shortSign q a v)
          (H0 (ShortEdgeSignRealization.coreHSign q)))
        (polygonSignArray (ShortEdgeSignStability.insertAfter q a ε v)) i j := by
    apply ordinaryCurrent_congr_interval_fixed_near
    · exact hij
    · intro x k y hix hxk hky hyj
      exact hgeom x k y hxk hky (by omega)
  have htable :=
    ShortEdgeWeighted.CurrentTableImpl.parentTable_eq_ordinaryCurrent
      a ha (ShortEdgeSignRealization.shortSign q a v)
      (H0 (ShortEdgeSignRealization.coreHSign q))
      (ShortEdgeSignRealization.coreHSign q) hij
  have hcur := hlocal.symm.trans htable.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro haway
    calc
      _ = parentTable a ha (ShortEdgeSignRealization.shortSign q a v)
          (ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
            (H0 (ShortEdgeSignRealization.coreHSign q))) i j := hcur
      _ = ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
          (H0 (ShortEdgeSignRealization.coreHSign q)))
          (H0 (ShortEdgeSignRealization.coreHSign q))
          (ShortEdgeWeighted.collapseAfter a i) (ShortEdgeWeighted.collapseAfter a j) := by
        rcases haway with hbefore | hafter
        · have hia : i < a := by omega
          have hieq : i ≠ a := by omega
          have hjne : j ≠ a + 1 := by omega
          have hjfar : ¬ a + 1 < j := by omega
          simp [parentTable, hbefore, hia, hieq, hjne, hjfar]
        · have hia : ¬ i < a := by omega
          have hieq : i ≠ a := by omega
          have hja : a + 1 ≤ i := hafter
          simp [parentTable, hia, hieq, hja]
  · intro hAB
    rcases hAB with ⟨hi, hj⟩
    subst i
    subst j
    calc
      _ = parentTable a ha (ShortEdgeSignRealization.shortSign q a v)
          (ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
            (H0 (ShortEdgeSignRealization.coreHSign q))) a (a + 1) := hcur
      _ = 1 := by simp [parentTable]
  · intro hAY
    rcases hAY with ⟨hi, hjA⟩
    subst i
    calc
      _ = parentTable a ha (ShortEdgeSignRealization.shortSign q a v)
          (ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
            (H0 (ShortEdgeSignRealization.coreHSign q))) a j := hcur
      _ = ((ShortEdgeWeighted.beta a (ShortEdgeSignRealization.shortSign q a v) -
            (ShortEdgeSignRealization.shortSign q a v
              (ShortEdgeWeighted.collapseAfter a j)).value) / 2) *
          ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
            (H0 (ShortEdgeSignRealization.coreHSign q)) a
              (ShortEdgeWeighted.collapseAfter a j) := by
        simp [parentTable, hjA, show j ≠ a + 1 by omega]
  · intro hXB
    rcases hXB with ⟨hiA, hj⟩
    subst j
    calc
      _ = parentTable a ha (ShortEdgeSignRealization.shortSign q a v)
          (ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
            (H0 (ShortEdgeSignRealization.coreHSign q))) i (a + 1) := hcur
      _ = ((ShortEdgeWeighted.alpha a ha (ShortEdgeSignRealization.shortSign q a v) -
            (ShortEdgeSignRealization.shortSign q a v i).value) / 2) *
          ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
            (H0 (ShortEdgeSignRealization.coreHSign q)) i a := by
        simp [parentTable, hiA, show i ≠ a by omega]
  · rintro ⟨hiA, hjA⟩
    calc
      _ = parentTable a ha (ShortEdgeSignRealization.shortSign q a v)
          (ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
            (H0 (ShortEdgeSignRealization.coreHSign q))) i j := hcur
      _ = ShortEdgeWeighted.kappa a ha (ShortEdgeSignRealization.shortSign q a v) *
          ordinaryCurrent (D0 a (ShortEdgeSignRealization.shortSign q a v)
            (H0 (ShortEdgeSignRealization.coreHSign q)))
            (H0 (ShortEdgeSignRealization.coreHSign q)) i
              (ShortEdgeWeighted.collapseAfter a j) := by
        simp [parentTable, hiA, hjA, show i ≠ a by omega,
          show j ≠ a + 1 by omega]

end DirectGLSSW.ShortEdgeCurrentGeometry
