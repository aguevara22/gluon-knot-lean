import DirectGLSSW.GeometricGates
import DirectGLSSW.ShortEdgeCutFibers
import DirectGLSSW.RealPolygons
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Short-edge determinant stability for an open finite polygon word.
This proves only finite open-word G1/sign stability, not cyclic G2.
-/

namespace DirectGLSSW.ShortEdgeSignStability

open DirectGLSSW
open DirectGLSSW.ShortEdgeCutFibers

def CoreHGeneric (q : ℕ → PlanarPoint ℝ) (N : ℕ) : Prop :=
  ∀ i k j, i < k → k < j → j ≤ N → polygonHDet q i k j ≠ 0

def DirectionGeneric (q : ℕ → PlanarPoint ℝ) (N a : ℕ)
    (v : PlanarPoint ℝ) : Prop :=
  ∀ x, x ≤ N → x ≠ a → planarDet v (q x - q a) ≠ 0

def insertAfter (q : ℕ → PlanarPoint ℝ) (a : ℕ) (ε : ℝ)
    (v : PlanarPoint ℝ) (i : ℕ) : PlanarPoint ℝ :=
  if i ≤ a then q i else if i = a + 1 then
    ((q a).1 + ε * v.1, (q a).2 + ε * v.2) else q (i - 1)

def boundedTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range (N + 2) ×ˢ (Finset.range (N + 2) ×ˢ Finset.range (N + 2))

def FarTriple (N a i k j : ℕ) : Prop :=
  i < k ∧ k < j ∧ j ≤ N + 1 ∧
    ShortEdgeCutFibers.avoidsInsertedPair a i k j

theorem insertAfter_zero (q : ℕ → PlanarPoint ℝ) (a i : ℕ)
    (v : PlanarPoint ℝ) :
    insertAfter q a 0 v i = q (ShortEdgeCutFibers.collapseAfter a i) := by
  by_cases hi : i ≤ a
  · simp [insertAfter, ShortEdgeCutFibers.collapseAfter, hi]
  · by_cases hs : i = a + 1
    · subst i
      apply Prod.ext <;> simp [insertAfter, ShortEdgeCutFibers.collapseAfter, hi, zero_mul]
    · simp [insertAfter, ShortEdgeCutFibers.collapseAfter, hi, hs]

theorem collapseAfter_triple_order_bounded
    (a i k j N : ℕ) (haN : a ≤ N)
    (hik : i < k) (hkj : k < j) (hj : j ≤ N + 1)
    (hfar : ShortEdgeCutFibers.avoidsInsertedPair a i k j) :
    ShortEdgeCutFibers.collapseAfter a i < ShortEdgeCutFibers.collapseAfter a k ∧
    ShortEdgeCutFibers.collapseAfter a k < ShortEdgeCutFibers.collapseAfter a j ∧
    ShortEdgeCutFibers.collapseAfter a j ≤ N := by
  have ho := ShortEdgeCutFibers.collapseAfter_triple_order a i k j hik hkj hfar
  refine ⟨ho.1, ho.2, ?_⟩
  by_cases hja : j ≤ a
  · rw [ShortEdgeCutFibers.collapseAfter_eq_of_le a j hja]
    exact le_trans hja haN
  · rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega

theorem polygonHDet_insertedPair_left
    (q : ℕ → PlanarPoint ℝ) (a : ℕ) (ε : ℝ) (v : PlanarPoint ℝ)
    (x : ℕ) (hx : x < a) :
    polygonHDet (insertAfter q a ε v) x a (a + 1) =
      -ε * planarDet v (q x - q a) := by
  simp [polygonHDet, planarDet, insertAfter, hx.le,
    Nat.not_le.mpr (by omega : a < a + 1)] <;> ring

theorem polygonHDet_insertedPair_right
    (q : ℕ → PlanarPoint ℝ) (a : ℕ) (ε : ℝ) (v : PlanarPoint ℝ)
    (y : ℕ) (hy : a < y) :
    polygonHDet (insertAfter q a ε v) a (a + 1) (y + 1) =
      -ε * planarDet v (q y - q a) := by
  have hv : insertAfter q a ε v (y + 1) = q y := by
    unfold insertAfter
    have h1 : ¬ y + 1 ≤ a := by omega
    have h2 : y + 1 ≠ a + 1 := by omega
    rw [if_neg h1, if_neg h2]
    have hsub : y + 1 - 1 = y := by omega
    simp [hsub]
  unfold polygonHDet
  rw [hv]
  simp [planarDet, insertAfter,
    Nat.not_le.mpr (by omega : a < a + 1)] <;> ring

/-- A strict triple contains at most one index whose inserted coordinate varies.
Consequently its H determinant is affine in ε. -/
theorem polygonHDet_inserted_affine
    (q : ℕ → PlanarPoint ℝ) (a i k j : ℕ) (v : PlanarPoint ℝ)
    (hik : i < k) (hkj : k < j) :
    ∀ ε : ℝ,
      polygonHDet (insertAfter q a ε v) i k j =
        polygonHDet (insertAfter q a 0 v) i k j +
          ε * (polygonHDet (insertAfter q a 1 v) i k j -
            polygonHDet (insertAfter q a 0 v) i k j) := by
  intro ε
  by_cases hi : i = a + 1
  · have hk : k ≠ a + 1 := by omega
    have hj : j ≠ a + 1 := by omega
    simp [polygonHDet, planarDet, insertAfter, hi, hk, hj,
      Nat.not_le.mpr (by omega : a < a + 1),
      Nat.not_le.mpr (by omega : a + 1 < k),
      Nat.not_le.mpr (by omega : a + 1 < j)] <;> ring
  · by_cases hk : k = a + 1
    · have hj : j ≠ a + 1 := by omega
      have hiA : i ≤ a := by omega
      simp [polygonHDet, planarDet, insertAfter, hi, hk, hj, hiA,
        Nat.not_le.mpr (by omega : a < a + 1),
        Nat.not_le.mpr (by omega : a + 1 < j)] <;> ring
    · by_cases hj : j = a + 1
      · have hiA : i ≤ a := by omega
        have hkA : k ≤ a := by omega
        simp [polygonHDet, planarDet, insertAfter, hi, hk, hj, hiA, hkA,
          Nat.not_le.mpr (by omega : a < a + 1)] <;> ring
      · simp [polygonHDet, planarDet, insertAfter, hi, hk, hj] <;> ring

/-- Algebraic substitute for a continuity radius: an affine perturbation of a
nonzero real number retains its sign on an explicit positive interval. -/
theorem exists_affine_sign_radius (d c : ℝ) (hd : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      d + ε * c ≠ 0 ∧ (d + ε * c < 0 ↔ d < 0) := by
  let δ : ℝ := |d| / (2 * (|c| + 1))
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hcden : 0 < 2 * (|c| + 1) := by positivity
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos hdabs hcden
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hmul : ε * (2 * (|c| + 1)) < |d| := by
    apply (lt_div_iff₀ hcden).mp
    simpa [δ] using hεδ
  have hsmall : |ε * c| < |d| / 2 := by
    rw [abs_mul, abs_of_pos hε]
    linarith [abs_nonneg c, abs_nonneg d]
  have hsmall_bounds := abs_lt.mp hsmall
  by_cases hneg : d < 0
  · have habs : |d| = -d := abs_of_neg hneg
    have hsum : d + ε * c < 0 := by linarith
    exact ⟨ne_of_lt hsum, ⟨fun _ => hneg, fun _ => hsum⟩⟩
  · have hpos : 0 < d := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hd)
    have habs : |d| = d := abs_of_pos hpos
    have hsum : 0 < d + ε * c := by linarith
    have hnot : ¬ d < 0 := not_lt_of_ge (le_of_lt hpos)
    have hnotSum : ¬ d + ε * c < 0 := not_lt_of_ge (le_of_lt hsum)
    exact ⟨ne_of_gt hsum, by simp [hnot, hnotSum]⟩

theorem exists_finset_common_radius {α : Type*} (s : Finset α)
    (P : α → ℝ → Prop)
    (h : ∀ x, x ∈ s → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ → P x ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ x, x ∈ s → P x ε := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, by norm_num, ?_⟩
      intro ε _ _ x hx
      simp at hx
  | @insert x s hx ih =>
      intro h
      obtain ⟨δx, hδx, hgoodx⟩ := h x (by simp)
      have htail : ∀ y, y ∈ s → ∃ δ : ℝ, 0 < δ ∧
          ∀ ε : ℝ, 0 < ε → ε < δ → P y ε := by
        intro y hy
        exact h y (by simp [hy])
      obtain ⟨δs, hδs, hgoods⟩ := ih htail
      have hmin : 0 < min δx δs := lt_min hδx hδs
      refine ⟨min δx δs, hmin, ?_⟩
      intro ε hε hεδ y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hgoodx ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
      · exact hgoods ε hε (lt_of_lt_of_le hεδ (min_le_right _ _)) y hy

theorem exists_far_sign_radius
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (haN : a ≤ N) (hcore : CoreHGeneric q N)
    (i k j : ℕ) (hik : i < k) (hkj : k < j) (hj : j ≤ N + 1)
    (hfar : ShortEdgeCutFibers.avoidsInsertedPair a i k j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      polygonHDet (insertAfter q a ε v) i k j ≠ 0 ∧
      (polygonHDet (insertAfter q a ε v) i k j < 0 ↔
        polygonHDet q (ShortEdgeCutFibers.collapseAfter a i)
          (ShortEdgeCutFibers.collapseAfter a k)
          (ShortEdgeCutFibers.collapseAfter a j) < 0) := by
  have ho := collapseAfter_triple_order_bounded a i k j N haN hik hkj hj hfar
  have hcore0 := hcore _ _ _ ho.1 ho.2.1 ho.2.2
  let d := polygonHDet (insertAfter q a 0 v) i k j
  let c := polygonHDet (insertAfter q a 1 v) i k j - d
  have hdeq : d = polygonHDet q (ShortEdgeCutFibers.collapseAfter a i)
      (ShortEdgeCutFibers.collapseAfter a k) (ShortEdgeCutFibers.collapseAfter a j) := by
    dsimp [d, polygonHDet]
    simp only [insertAfter_zero]
  have hd : d ≠ 0 := by rw [hdeq]; exact hcore0
  have haff : ∀ ε : ℝ,
      polygonHDet (insertAfter q a ε v) i k j = d + ε * c := by
    intro ε
    have heq := polygonHDet_inserted_affine q a i k j v hik hkj ε
    simpa [d, c] using heq
  obtain ⟨δ, hδ, hsign⟩ := exists_affine_sign_radius d c hd
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  rw [haff ε]
  constructor
  · exact (hsign ε hε hεδ).1
  · simpa [hdeq] using (hsign ε hε hεδ).2

/-- The finite family of all triples in the new word shares one radius. -/
theorem exists_uniform_far_sign_radius
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (haN : a ≤ N) (hcore : CoreHGeneric q N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ i k j, FarTriple N a i k j →
        polygonHDet (insertAfter q a ε v) i k j ≠ 0 ∧
        (polygonHDet (insertAfter q a ε v) i k j < 0 ↔
          polygonHDet q (ShortEdgeCutFibers.collapseAfter a i)
            (ShortEdgeCutFibers.collapseAfter a k)
            (ShortEdgeCutFibers.collapseAfter a j) < 0) := by
  let s := boundedTriples N
  have hlocal : ∀ t, t ∈ s → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        (FarTriple N a t.1 t.2.1 t.2.2 →
          polygonHDet (insertAfter q a ε v) t.1 t.2.1 t.2.2 ≠ 0 ∧
          (polygonHDet (insertAfter q a ε v) t.1 t.2.1 t.2.2 < 0 ↔
            polygonHDet q (ShortEdgeCutFibers.collapseAfter a t.1)
              (ShortEdgeCutFibers.collapseAfter a t.2.1)
              (ShortEdgeCutFibers.collapseAfter a t.2.2) < 0)) := by
    intro t ht
    by_cases hfar : FarTriple N a t.1 t.2.1 t.2.2
    · rcases hfar with ⟨hik, hkj, hj, hAvoid⟩
      obtain ⟨δ, hδ, hgood⟩ := exists_far_sign_radius q N a v haN hcore
        t.1 t.2.1 t.2.2 hik hkj hj hAvoid
      exact ⟨δ, hδ, fun ε hε hεδ _ => hgood ε hε hεδ⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro ε _ _ hf
      exact False.elim (hfar hf)
  obtain ⟨δ, hδ, hgood⟩ := exists_finset_common_radius s
    (fun t ε => FarTriple N a t.1 t.2.1 t.2.2 →
      polygonHDet (insertAfter q a ε v) t.1 t.2.1 t.2.2 ≠ 0 ∧
      (polygonHDet (insertAfter q a ε v) t.1 t.2.1 t.2.2 < 0 ↔
        polygonHDet q (ShortEdgeCutFibers.collapseAfter a t.1)
          (ShortEdgeCutFibers.collapseAfter a t.2.1)
          (ShortEdgeCutFibers.collapseAfter a t.2.2) < 0)) hlocal
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ i k j hfar
  have hmem : (i, k, j) ∈ s := by
    simp [s, boundedTriples]
    rcases hfar with ⟨_, _, hj, _⟩
    omega
  exact hgood ε hε hεδ (i, k, j) hmem hfar

structure ShortEdgeStability
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (ε : ℝ) (haN : a ≤ N)
    (hcore : CoreHGeneric q N) (hdir : DirectionGeneric q N a v) : Prop where
  insertedG1 : CoreHGeneric (insertAfter q a ε v) (N + 1)
  farSigns : ∀ i k j (hik : i < k) (hkj : k < j)
      (hj : j ≤ N + 1) (hfar : ShortEdgeCutFibers.avoidsInsertedPair a i k j),
    polygonHSign (insertAfter q a ε v) i k j
        (insertedG1 i k j hik hkj hj) =
      polygonHSign q (ShortEdgeCutFibers.collapseAfter a i)
        (ShortEdgeCutFibers.collapseAfter a k) (ShortEdgeCutFibers.collapseAfter a j)
        (hcore _ _ _
          (collapseAfter_triple_order_bounded a i k j N haN hik hkj hj hfar).1
          (collapseAfter_triple_order_bounded a i k j N haN hik hkj hj hfar).2.1
          (collapseAfter_triple_order_bounded a i k j N haN hik hkj hj hfar).2.2)
  pairLeft : ∀ x, x < a →
    polygonHDet (insertAfter q a ε v) x a (a + 1) =
      -ε * planarDet v (q x - q a)
  pairRight : ∀ y, a < y → y ≤ N →
    polygonHDet (insertAfter q a ε v) a (a + 1) (y + 1) =
      -ε * planarDet v (q y - q a)

theorem exists_shortEdge_sign_stability
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (ha : 0 < a) (haNlt : a < N) (haN : a ≤ N)
    (hcore : CoreHGeneric q N) (hdir : DirectionGeneric q N a v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ShortEdgeStability q N a v ε haN hcore hdir := by
  obtain ⟨δ, hδ, hfarData⟩ := exists_uniform_far_sign_radius q N a v haN hcore
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hfarData := hfarData ε hε hεδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k j hik hkj hj
    by_cases hfar : ShortEdgeCutFibers.avoidsInsertedPair a i k j
    · exact (hfarData i k j ⟨hik, hkj, hj, hfar⟩).1
    · have hboth :
          (i = a ∨ k = a ∨ j = a) ∧ (i = a + 1 ∨ k = a + 1 ∨ j = a + 1) := by
        apply not_not.mp
        simpa [ShortEdgeCutFibers.avoidsInsertedPair,
          ShortEdgeCutFibers.containsIndex] using hfar
      rcases hboth with ⟨hA, hB⟩
      have hpair :
          (i < a ∧ k = a ∧ j = a + 1) ∨
          (i = a ∧ k = a + 1 ∧ a + 1 < j) := by
        rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
          simp_all <;> omega
      rcases hpair with ⟨hleft, hk, hj'⟩ | ⟨hi', hk', hright⟩
      · subst k; subst j
        rw [polygonHDet_insertedPair_left q a ε v i hleft]
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (ne_of_gt hε)
        · exact hdir i (by omega) (by omega)
      · subst i; subst k
        have hidx : j = (j - 1) + 1 := by omega
        rw [hidx, polygonHDet_insertedPair_right q a ε v (j - 1) (by omega)]
        have hy : j - 1 ≤ N := by omega
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (ne_of_gt hε)
        · exact hdir (j - 1) hy (by omega)
  · intro i k j hik hkj hj hfar
    have hData := hfarData i k j ⟨hik, hkj, hj, hfar⟩
    have ho := collapseAfter_triple_order_bounded a i k j N haN hik hkj hj hfar
    have hCore := hcore _ _ _ ho.1 ho.2.1 ho.2.2
    have hNew : polygonHDet (insertAfter q a ε v) i k j ≠ 0 := hData.1
    by_cases hneg : polygonHDet q (ShortEdgeCutFibers.collapseAfter a i)
        (ShortEdgeCutFibers.collapseAfter a k) (ShortEdgeCutFibers.collapseAfter a j) < 0
    · have hnewneg := hData.2.mpr hneg
      simp [polygonHSign, nonzeroScalarSign, hneg, hnewneg]
    · have hcorepos : 0 < polygonHDet q (ShortEdgeCutFibers.collapseAfter a i)
          (ShortEdgeCutFibers.collapseAfter a k) (ShortEdgeCutFibers.collapseAfter a j) :=
        lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hCore)
      have hnot : ¬ polygonHDet (insertAfter q a ε v) i k j < 0 :=
        mt hData.2.mp hneg
      have hnewpos : 0 < polygonHDet (insertAfter q a ε v) i k j :=
        lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hNew)
      simp [polygonHSign, nonzeroScalarSign, hneg, hnewpos.not_lt]
  · exact polygonHDet_insertedPair_left q a ε v
  · exact fun y hy hyN => polygonHDet_insertedPair_right q a ε v y hy

end DirectGLSSW.ShortEdgeSignStability
