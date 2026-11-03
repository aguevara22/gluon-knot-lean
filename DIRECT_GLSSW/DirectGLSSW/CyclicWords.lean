import DirectGLSSW.SpinorRecursion
import DirectGLSSW.TreeWeights
import Mathlib.Data.Fintype.Card

/-!
# Opening a cyclic polygon at a root edge

Source: Section 1 and `ep:H`. The root labelled r is the directed edge from
q_r to q_(r+1). Its complementary boundary word starts at q_(r+1) and ends
at q_r. No quotient by cyclic symmetry or assumption of root independence
is used. These indexing and determinant statements are generic-field
prerequisites; real G1–G2 polygon and smoothing definitions remain separate.
-/

namespace DirectGLSSW

/-- The kth vertex after the chosen root edge, with explicit cyclic indexing. -/
def cyclicVertexIndex {n : ℕ} (root : Fin n) (k : ℕ) : Fin n :=
  ⟨(root.val + 1 + k) % n, Nat.mod_lt _ (by have := root.isLt; omega)⟩

/-- Reading the complementary boundary after the chosen root edge. -/
def rootedPolygonWord {K : Type*} {n : ℕ}
    (q : Fin n → PlanarPoint K) (root : Fin n) (k : ℕ) : PlanarPoint K :=
  q (cyclicVertexIndex root k)

/-- On one traversal the modular index wraps at most once. -/
theorem cyclicVertexIndex_val {n : ℕ} (root : Fin n) {k : ℕ} (hk : k < n) :
    (cyclicVertexIndex root k).val =
      if root.val + 1 + k < n then root.val + 1 + k else root.val + 1 + k - n := by
  unfold cyclicVertexIndex
  dsimp only
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Distinct positions before one full turn have distinct original labels. -/
theorem cyclicVertexIndex_injective {n : ℕ} (root : Fin n) {a b : ℕ}
    (ha : a < n) (hb : b < n) (h : cyclicVertexIndex root a = cyclicVertexIndex root b) :
    a = b := by
  have hv := congrArg Fin.val h
  rw [cyclicVertexIndex_val root ha, cyclicVertexIndex_val root hb] at hv
  split_ifs at hv <;> omega

/-- The final vertex of the complementary word is the start of the root edge. -/
theorem cyclicVertexIndex_last {n : ℕ} (root : Fin n) :
    cyclicVertexIndex root (n - 1) = root := by
  apply Fin.ext
  have hn : 0 < n := by have := root.isLt; omega
  change (root.val + 1 + (n - 1)) % n = root.val
  have heq : root.val + 1 + (n - 1) = root.val + n := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt root.isLt]

/-- Taking n more steps returns the same labelled vertex. -/
theorem cyclicVertexIndex_periodic {n : ℕ} (root : Fin n) (k : ℕ) :
    cyclicVertexIndex root (k + n) = cyclicVertexIndex root k := by
  apply Fin.ext
  change (root.val + 1 + (k + n)) % n = (root.val + 1 + k) % n
  rw [← Nat.add_assoc, Nat.add_mod_right]

/-- The final point of the open word is exactly the root edge's initial point. -/
theorem rootedPolygonWord_last {K : Type*} {n : ℕ}
    (q : Fin n → PlanarPoint K) (root : Fin n) :
    rootedPolygonWord q root (n - 1) = q root := by
  simp only [rootedPolygonWord, cyclicVertexIndex_last]

/-- The determinant form of noncollinearity for every three distinct labels. -/
def cyclicNoncollinear {K : Type*} [CommRing K] {n : ℕ}
    (q : Fin n → PlanarPoint K) : Prop :=
  ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
    planarDet (q b - q c) (q a - q c) ≠ 0

/-- Opening a noncollinear cyclic word discharges every interval gate's
nonvanishing condition; no physical gate uses the arbitrary total extension. -/
theorem rootedPolygonWord_noncollinear {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (q : Fin n → PlanarPoint K)
    (hq : cyclicNoncollinear q) (root : Fin n) :
    IntervalNoncollinear (rootedPolygonWord q root) 0 (n - 1) := by
  intro a b c _ hab hbc hcn
  have hc : c < n := by have := root.isLt; omega
  have hb : b < n := by omega
  have ha : a < n := by omega
  apply hq (cyclicVertexIndex root a) (cyclicVertexIndex root b) (cyclicVertexIndex root c)
  · intro h; have := cyclicVertexIndex_injective root ha hb h; omega
  · intro h; have := cyclicVertexIndex_injective root hb hc h; omega
  · intro h; have := cyclicVertexIndex_injective root ha hc h; omega

/-- One traversal of the opened word visits every original vertex once. -/
theorem cyclicVertexIndex_bijective {n : ℕ} (root : Fin n) :
    Function.Bijective (fun k : Fin n => cyclicVertexIndex root k.val) := by
  apply Finite.injective_iff_bijective.mp
  intro a b h
  exact Fin.ext (cyclicVertexIndex_injective root a.isLt b.isLt h)

/-- Explicit cyclic relabelling equivalence, with bijectivity proved separately. -/
noncomputable def cyclicVertexEquiv {n : ℕ} (root : Fin n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun k => cyclicVertexIndex root k.val) (cyclicVertexIndex_bijective root)

/-- The omitted root edge has the original forward orientation. -/
def cyclicRootEdge {K : Type*} [CommRing K] {n : ℕ}
    (q : Fin n → PlanarPoint K) (root : Fin n) : PlanarPoint K :=
  q (cyclicVertexIndex root 0) - q root

/-- The complementary momenta and the actual root edge sum to zero. -/
theorem rootedPolygonWord_momentum_conservation {K : Type*} [CommRing K] {n : ℕ}
    (q : Fin n → PlanarPoint K) (root : Fin n) :
    (∑ k ∈ Finset.range (n - 1), polygonMomentum (rootedPolygonWord q root) k) +
      cyclicRootEdge q root = 0 := by
  have hsum := polygonMomentum_sum (rootedPolygonWord q root) 0 (n - 1)
  simp only [Nat.zero_add] at hsum
  rw [hsum]
  simp [polygonChord, cyclicRootEdge, rootedPolygonWord, cyclicVertexIndex_last]

/-- For at least three labelled vertices, determinant noncollinearity implies
that different labels really are different points. -/
theorem cyclicNoncollinear_injective {K : Type*} [CommRing K] {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint K) (hq : cyclicNoncollinear q) :
    Function.Injective q := by
  classical
  intro a b hpoint
  by_contra hab
  have hcard : ({a, b} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have hsmall : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_not_mem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  apply hq a b c hab (Ne.symm hc.2) (Ne.symm hc.1)
  simp [hpoint, planarDet, mul_comm]

/-- The published independent recursion evaluated after a specified root edge.
This definition neither assumes nor enforces independence of that edge. -/
noncomputable def rootedSpinorAmplitude {K : Type*} [Field K] [LinearOrder K]
    {n : ℕ} (q : Fin n → PlanarPoint K) (root : Fin n) : ℚ :=
  spinorAmplitude (rootedPolygonWord q root) 0 (n - 1)

/-- On a noncollinear cyclic word of at least three vertices, the independent
published recursion is exactly the concrete note-convention marked-tree sum. -/
theorem rootedSpinorAmplitude_eq_markedTreeSum {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint K) (hq : cyclicNoncollinear q) (root : Fin n) :
    rootedSpinorAmplitude q root =
      markedTreeSum (polygonSignArray (rootedPolygonWord q root))
        (polygonSignArray (rootedPolygonWord q root)) 0 (n - 1) := by
  unfold rootedSpinorAmplitude
  rw [spinorAmplitude_eq_marked _ (by omega) (rootedPolygonWord_noncollinear q hq root)]
  exact (markedTreeSum_eq_markedAmplitude _ _ (by omega)).symm

/-- Root independence for this concrete cyclic word is an explicit proposition.
It is not proved or built into the amplitude definition. The final theorem's
global hypothesis on real generic polygons remains to be assembled. -/
def RootIndependentOn {K : Type*} [Field K] [LinearOrder K]
    {n : ℕ} (q : Fin n → PlanarPoint K) : Prop :=
  ∀ root₁ root₂ : Fin n, rootedSpinorAmplitude q root₁ = rootedSpinorAmplitude q root₂

/-- A concrete counterclockwise triangle, valid over every ordered field. -/
def standardTriangle {K : Type*} [Zero K] [One K] (k : Fin 3) : PlanarPoint K :=
  if k.val = 0 then (0, 0) else if k.val = 1 then (1, 0) else (0, 1)

/-- The noncollinearity condition has a genuine three-vertex instance. -/
theorem standardTriangle_noncollinear {K : Type*} [Field K] :
    cyclicNoncollinear (standardTriangle (K := K)) := by
  intro a b c hab hbc hac
  have hab' : a.val ≠ b.val := Fin.val_ne_iff.mpr hab
  have hbc' : b.val ≠ c.val := Fin.val_ne_iff.mpr hbc
  have hac' : a.val ≠ c.val := Fin.val_ne_iff.mpr hac
  have cases3 (k : Fin 3) : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases cases3 a with ha | ha | ha <;>
    rcases cases3 b with hb | hb | hb <;>
    rcases cases3 c with hc | hc | hc <;>
    norm_num [standardTriangle, planarDet, ha, hb, hc] at *

/-- The original recursion gives the same exact normalization at each root
of this concrete triangle. This is an example, not general root independence. -/
theorem rootedSpinorAmplitude_standardTriangle {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (root : Fin 3) :
    rootedSpinorAmplitude (standardTriangle (K := K)) root = -1 := by
  rw [rootedSpinorAmplitude_eq_markedTreeSum (by omega) _ standardTriangle_noncollinear root,
    markedTreeSum_eq_markedAmplitude _ _ (by omega)]
  change markedAmplitude _ _ 0 (0 + 2) = -1
  rw [markedAmplitude_triangle]
  have hr : root.val = 0 ∨ root.val = 1 ∨ root.val = 2 := by omega
  rcases hr with hr | hr | hr <;>
    norm_num [polygonSignArray, polygonHDet, scalarSignValue, planarDet,
      rootedPolygonWord, cyclicVertexIndex, standardTriangle, hr]

/-- Root independence is nonvacuous on the displayed triangle. -/
theorem standardTriangle_rootIndependent {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : RootIndependentOn (standardTriangle (K := K)) := by
  intro r s
  rw [rootedSpinorAmplitude_standardTriangle, rootedSpinorAmplitude_standardTriangle]

end DirectGLSSW
