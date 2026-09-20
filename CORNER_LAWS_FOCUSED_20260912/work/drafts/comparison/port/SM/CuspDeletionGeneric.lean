-- Ported <HH:MM>Z 2026-09-15 from work/drafts/comparison/Comparison_Assembled.lean lines 772-936 (comparison lane §4, unit U-CM-CUSPGEN: the `cu_*` helpers `cu_fused_interior_true/false`, `cu_deletionIndex_adjacent/_remote/_two_prev`, `cu_remote_prev/_deleted`, `cu_lift`, `cu_lift_remote`, `cu_lift_interior` and the leaf `cusp_deletion_generic` (PROVED, frozen statement)) by the pod executor; body verbatim except this header, the import block (SM.CuspDefinition, SM.DeletionIndices, SM.DeletedTuple, SM.GenericTopology, SM.ZeroTriples — compile-verified sufficient), the module docstring (new), the draft's file-level line 49 `open WallGerm SoftDuplication Carrier` reduced to `open WallGerm` (the namespaces `SoftDuplication`, `Carrier` are not in this module's import closure; nothing here uses them) and the DROPPED section-comment line 770 (`### The cusp law — the ONE open leaf of the lane. …`, stale: the leaf is proved).  Wrappers `namespace SM` / `end SM` repeated.
import SM.CuspDefinition
import SM.DeletionIndices
import SM.DeletedTuple
import SM.GenericTopology
import SM.ZeroTriples

/-! # Genericity of the cusp deletion (sm-6:335-359) — comparison lane unit U-CM-CUSPGEN (library material)

Source: work/drafts/comparison/Comparison_Assembled.lean §4 (U_CUSPGEN_REPORT.md; PLAN_FINAL.md §3.4).  At a simple cusp wall
`w : WallGerm (n + 1)` whose deletion `Q = P(0) ∖ j` satisfies (G1), `Q` is generic (`cusp_deletion_generic`): the fused edge
`[A, B]` lies in the longer of `E_{j−1}(0)`, `E_j(0)` (`w.cusp_cases`), three pairwise remote edges of `Q` with a common
relative-interior point lift injectively (`cu_lift`) to three pairwise remote edges of the centre with a common point, contrary
to `concurrences = ∅`.  Pure accepted geometry; no dependence on the C rows.  Consumer: `cu_cuspLawC_of` (SM/CInherits.lean). -/

namespace SM

open WallGerm

/-! #### Helpers of unit U-CM-CUSPGEN (prefix `cu_`): the fused-edge containments (PLAN_FINAL.md §3.4
step 2), the `deletionIndex` adjacency / remoteness transfer (steps 3-4), the edge lift `cu_lift`
(a function `ZMod n → ZMod (n+1)`; fused edge `−1 ↦ k ∈ {j−1, j}` by the cusp case). -/

/-- Case `true` (`B = μ_{j+1}` strictly between `A = μ_{j−1}` and `M = μ_j`): the relative interior of
the fused edge `[A, B]` of `Q = P ∖ j` lies in the relative interior of `E_{j−1}(P) = [A, M]`
(parameter product `q·t`). -/
theorem cu_fused_interior_true {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hb : StrictBetween (P (j - 1)) (P (j + 1)) (P j)) {x : Plane}
    (hx : x ∈ edgeInterior (deleteVertex P j) (-1)) : x ∈ edgeInterior P (j - 1) := by
  obtain ⟨q, hq0, hq1, hq⟩ := hx
  simp only [edgePoint, deleteVertex_last, edge_deleteVertex_last] at hq
  obtain ⟨_, t, ht0, ht1, ht⟩ := hb
  refine ⟨q * t, mul_pos hq0 ht0, by nlinarith, ?_⟩
  simp only [edgePoint, edge, sub_add_cancel]
  rw [hq, ht]
  ext <;> dsimp <;> ring

/-- Case `false` (`A = μ_{j−1}` strictly between `M = μ_j` and `B = μ_{j+1}`): the relative interior of
the fused edge `[A, B]` lies in the relative interior of `E_j(P) = [M, B]` (parameter `t + q(1−t)`). -/
theorem cu_fused_interior_false {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hb : StrictBetween (P j) (P (j - 1)) (P (j + 1))) {x : Plane}
    (hx : x ∈ edgeInterior (deleteVertex P j) (-1)) : x ∈ edgeInterior P j := by
  obtain ⟨q, hq0, hq1, hq⟩ := hx
  simp only [edgePoint, deleteVertex_last, edge_deleteVertex_last] at hq
  obtain ⟨_, t, ht0, ht1, ht⟩ := hb
  refine ⟨t + q * (1 - t), by nlinarith, by nlinarith, ?_⟩
  simp only [edgePoint, edge]
  rw [hq, ht]
  ext <;> dsimp <;> ring

/-- Two retained labels whose images under `deletionIndex j` are adjacent in `P` are adjacent in `Q`
(`deletionIndex_next` for `i ≠ −1`, injectivity). -/
theorem cu_deletionIndex_adjacent {n : ℕ} [NeZero n] (j : ZMod (n + 1)) {a b : ZMod n}
    (ha : a ≠ -1) (hb : b ≠ -1)
    (h : adjacent (deletionIndex j a) (deletionIndex j b)) : adjacent a b := by
  rcases h with h | h | h
  · left
    have he : deletionIndex j (b + 1) = deletionIndex j a := by
      rw [deletionIndex_next j hb]
      linear_combination h
    have := deletionIndex_injective j he
    linear_combination this
  · right; left
    have := deletionIndex_injective j (sub_eq_zero.mp h)
    linear_combination this
  · right; right
    have he : deletionIndex j (a + 1) = deletionIndex j b := by
      rw [deletionIndex_next j ha]
      linear_combination -h
    have := deletionIndex_injective j he
    linear_combination -this

/-- Remoteness of two retained edges transfers from `Q` to `P`. -/
theorem cu_deletionIndex_remote {n : ℕ} [NeZero n] (j : ZMod (n + 1)) {a b : ZMod n}
    (ha : a ≠ -1) (hb : b ≠ -1) (h : remote a b) :
    remote (deletionIndex j a) (deletionIndex j b) :=
  fun hadj => h (cu_deletionIndex_adjacent j ha hb hadj)

/-- `deletionIndex j (−2) = j − 2`: the retained edge before the fused one is the old `E_{j−2}`. -/
theorem cu_deletionIndex_two_prev {n : ℕ} [NeZero n] [Nontrivial (ZMod n)] (j : ZMod (n + 1)) :
    deletionIndex j (-2 : ZMod n) = j - 2 := by
  have h2 : (-2 : ZMod n) ≠ -1 := fun he => one_ne_zero (by linear_combination -he)
  have he := deletionIndex_next j h2
  rw [show (-2 : ZMod n) + 1 = -1 by ring, deletionIndex_last] at he
  linear_combination -he

/-- A retained edge remote from the fused edge in `Q` is remote from `E_{j−1}` in `P`: the neighbours
`j−2 = deletionIndex j (−2)` and `j` of `j−1` are excluded by remoteness resp. `deletionIndex_ne_deleted`. -/
theorem cu_remote_prev {n : ℕ} [NeZero n] [Nontrivial (ZMod n)] (j : ZMod (n + 1)) {a : ZMod n}
    (ha : a ≠ -1) (h : remote a (-1)) : remote (deletionIndex j a) (j - 1) := by
  rintro (hadj | hadj | hadj)
  · exact deletionIndex_ne_deleted j a (by linear_combination -hadj)
  · exact deletionIndex_ne_prev j ha (by linear_combination -hadj)
  · apply h
    right; right
    have he : deletionIndex j a = deletionIndex j (-2) := by
      rw [cu_deletionIndex_two_prev]
      linear_combination -hadj
    have := deletionIndex_injective j he
    linear_combination -this

/-- A retained edge remote from the fused edge in `Q` is remote from `E_j` in `P`: the neighbours
`j+1 = deletionIndex j 0` and `j−1` of `j` are excluded by remoteness resp. `deletionIndex_ne_prev`. -/
theorem cu_remote_deleted {n : ℕ} [NeZero n] (j : ZMod (n + 1)) {a : ZMod n}
    (ha : a ≠ -1) (h : remote a (-1)) : remote (deletionIndex j a) j := by
  rintro (hadj | hadj | hadj)
  · apply h
    left
    have he : deletionIndex j a = deletionIndex j 0 := by
      rw [deletionIndex_zero]
      linear_combination -hadj
    have := deletionIndex_injective j he
    linear_combination -this
  · exact deletionIndex_ne_deleted j a (by linear_combination -hadj)
  · exact deletionIndex_ne_prev j ha (by linear_combination -hadj)

/-- The edge lift `Q → P`: retained edges to their retained label `deletionIndex j i`, the fused edge
`−1` to `k` (`= j − 1` in case `true`, `= j` in case `false`). -/
def cu_lift {n : ℕ} [NeZero n] (j k : ZMod (n + 1)) (i : ZMod n) : ZMod (n + 1) :=
  if i = -1 then k else deletionIndex j i

/-- The lift carries remote pairs of `Q` to remote pairs of `P` (hence is injective on them). -/
theorem cu_lift_remote {n : ℕ} [NeZero n] [Nontrivial (ZMod n)] {j k : ZMod (n + 1)}
    (hk : k = j - 1 ∨ k = j) {a b : ZMod n} (h : remote a b) :
    remote (cu_lift j k a) (cu_lift j k b) := by
  by_cases ha : a = -1
  · by_cases hb : b = -1
    · exact ((remote_endpoints a b h).1 (hb.trans ha.symm)).elim
    · subst ha
      simp only [cu_lift, ↓reduceIte, hb]
      have hb' : remote b (-1) := remote_symm h
      rcases hk with hk | hk <;> rw [hk]
      · exact remote_symm (cu_remote_prev j hb hb')
      · exact remote_symm (cu_remote_deleted j hb hb')
  · by_cases hb : b = -1
    · subst hb
      simp only [cu_lift, ↓reduceIte, ha]
      rcases hk with hk | hk <;> rw [hk]
      · exact cu_remote_prev j ha h
      · exact cu_remote_deleted j ha h
    · simp only [cu_lift, ha, hb, ↓reduceIte]
      exact cu_deletionIndex_remote j ha hb h

/-- Relative-interior points of every edge of `Q` lie in the relative interior of the lifted edge of
`P`, given the fused-edge containment (`edgeInterior_deleteVertex` for retained edges). -/
theorem cu_lift_interior {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j k : ZMod (n + 1)}
    (hfused : ∀ x ∈ edgeInterior (deleteVertex P j) (-1), x ∈ edgeInterior P k)
    {i : ZMod n} {x : Plane} (hx : x ∈ edgeInterior (deleteVertex P j) i) :
    x ∈ edgeInterior P (cu_lift j k i) := by
  by_cases hi : i = -1
  · subst hi
    simpa only [cu_lift, ↓reduceIte] using hfused x hx
  · simp only [cu_lift, hi, ↓reduceIte]
    rwa [edgeInterior_deleteVertex P j hi] at hx

/-- LEAF (unit U-CM-CUSPGEN; sm-6:335-359): at a simple cusp wall whose deletion `Q = P(0) ∖ j`
satisfies (G1), `Q` is generic.  (G2): `CuspAt` gives `A = μ_{j−1}(0)`, `M = μ_j(0)`, `B = μ_{j+1}(0)`
collinear with `M` outside `[A, B]` (`collinear_exterior_cases`, SM/CuspBetweenness.lean), so the fused
edge `[A, B]` lies in the longer of `E_{j−1}(0) = [A, M]`, `E_j(0) = [M, B]` and its relative interior in
that edge's; three pairwise remote edges of `Q` with a common relative-interior point lift injectively to
three pairwise remote edges of the centre with a common point, contrary to `Z_c = ∅`
(`concurrences = ∅`).  Frozen statement.  The domain is NOT narrowed (TARGETS: "the deletion satisfies
G1", threaded cusps included). -/
theorem cusp_deletion_generic {n : ℕ} [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hf : w.CuspAt j) (hQ1 : G1 (deleteVertex w.center j)) : Generic (deleteVertex w.center j) := by
  refine ⟨hQ1, ?_⟩
  have hn : 3 ≤ n := by have := hf.1; omega
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨k, hk, hfused⟩ : ∃ k : ZMod (n + 1), (k = j - 1 ∨ k = j) ∧
      ∀ x ∈ edgeInterior (deleteVertex w.center j) (-1), x ∈ edgeInterior w.center k := by
    rcases (w.cusp_cases hf).1 with hA | hB
    · exact ⟨j - 1, Or.inl rfl, fun x hx => cu_fused_interior_true hA hx⟩
    · exact ⟨j, Or.inr rfl, fun x hx => cu_fused_interior_false hB hx⟩
  rintro ⟨a, b, c, x, hab, hbc, hac, ha, hb, hc⟩
  have rab := g1_common_interiors_remote hn hQ1 hab ha hb
  have rbc := g1_common_interiors_remote hn hQ1 hbc hb hc
  have rac := g1_common_interiors_remote hn hQ1 hac ha hc
  have hm := (mem_concurrenceTriples w.center {cu_lift j k a, cu_lift j k b, cu_lift j k c}).mpr
    ((concurrenceTriple_iff (cu_lift_remote hk rab) (cu_lift_remote hk rbc)
      (cu_lift_remote hk rac)).mpr
      ⟨x, cu_lift_interior hfused ha, cu_lift_interior hfused hb, cu_lift_interior hfused hc⟩)
  have hce : concurrenceTriples w.center = ∅ := by
    simpa only [WallGerm.concurrences] using hf.2.2.1
  simp only [hce, Finset.notMem_empty] at hm

end SM
