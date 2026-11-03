import DirectGLSSW.HorizontalComplement
import DirectGLSSW.ShortEdgeBoundedCongruence

set_option autoImplicit false

namespace DirectGLSSW.HorizontalShortEdge

open DirectGLSSW.ShortEdgeCyclicAdapter

/-- The actual word complementary to the inserted horizontal root edge. -/
def horizontalComplementWord {n : ℕ} (q : Fin (n + 1) → PlanarPoint ℝ)
    (epsilon : ℝ) (k : ℕ) : PlanarPoint ℝ :=
  if k = 0 then ((q ⟨0, by omega⟩).1 - epsilon, 0)
  else if hk : k < n + 1 then q ⟨k, hk⟩ else q ⟨0, by omega⟩

theorem horizontalComplementWord_rooted {n : ℕ}
    (q : Fin (n + 1) → PlanarPoint ℝ)
    (hzero : (q ⟨0, by omega⟩).2 = 0) (epsilon : ℝ)
    (k : ℕ) (hk : k ≤ n + 1) :
    rootedPolygonWord (insertCyclicAfter q ⟨0, by omega⟩ epsilon (-1, 0))
      ⟨0, by omega⟩ k = horizontalComplementWord q epsilon k := by
  change (q (0 : Fin (n + 1))).2 = 0 at hzero
  by_cases hlast : k = n + 1
  · subst k
    have hidx : cyclicVertexIndex (⟨0, by omega⟩ : Fin (n + 1 + 1)) (n + 1) =
        ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [cyclicVertexIndex, Nat.add_comm]
    rw [rootedPolygonWord, hidx]
    simp [insertCyclicAfter, horizontalComplementWord]
  · have hkn : k < n + 1 := by omega
    have hidx : cyclicVertexIndex (⟨0, by omega⟩ : Fin (n + 1 + 1)) k =
        ⟨k + 1, by omega⟩ := by
      apply Fin.ext
      change (0 + 1 + k) % (n + 1 + 1) = k + 1
      rw [show 0 + 1 + k = k + 1 by omega, Nat.mod_eq_of_lt (by omega)]
    rw [rootedPolygonWord, hidx]
    by_cases hkzero : k = 0
    · subst k
      simp [insertCyclicAfter, horizontalComplementWord,
        hzero, sub_eq_add_neg]
    · have hkone : k + 1 ≠ 1 := by omega
      simp [insertCyclicAfter, horizontalComplementWord,
        hkzero, hkone, hkn]

theorem polygonAmplitude_eq_horizontalComplement {n : ℕ}
    (q : Fin (n + 1) → PlanarPoint ℝ)
    (hzero : (q ⟨0, by omega⟩).2 = 0) (epsilon : ℝ)
    (hp : CyclicGeneric (insertCyclicAfter q ⟨0, by omega⟩ epsilon (-1, 0))) :
    polygonAmplitude (insertCyclicAfter q ⟨0, by omega⟩ epsilon (-1, 0)) hp =
      markedAmplitude
        (fun _ k _ => scalarSignValue (horizontalComplementWord q epsilon k).2)
        (polygonSignArray (horizontalComplementWord q epsilon)) 0 (n + 1) := by
  rw [polygonAmplitude_eq_markedTreeSum,
    markedTreeSum_eq_markedAmplitude _ _ (by omega)]
  apply markedAmplitude_congr_interval _ _ _ _ (by omega)
  intro a b c _ hab hbc hcn
  unfold polygonSignArray polygonHDet
  rw [horizontalComplementWord_rooted q hzero epsilon a (by omega),
    horizontalComplementWord_rooted q hzero epsilon b (by omega),
    horizontalComplementWord_rooted q hzero epsilon c (by omega)]

theorem exists_horizontal_capExpansion (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin (n + 1) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hzero : (q ⟨0, by omega⟩).2 = 0)
    (hothers : ∀ x : Fin (n + 1), x ≠ ⟨0, by omega⟩ → (q x).2 ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < delta →
      ∃ hp : CyclicGeneric (insertCyclicAfter q ⟨0, by omega⟩ epsilon (-1, 0)),
        capCutExpansion (j := n + 1)
          (fun k => scalarSignValue (horizontalComplementWord q epsilon k).2)
          (ordinaryCurrent
            (fun _ k _ => scalarSignValue (horizontalComplementWord q epsilon k).2)
            (polygonSignArray (horizontalComplementWord q epsilon))) 0 =
          ((scalarSignValue (q ⟨n, by omega⟩).2 +
            scalarSignValue (q ⟨1, by have := hq.size_ge_three; omega⟩).2) / 2) *
            polygonAmplitude q hq := by
  have hn : 2 ≤ n := by have := hq.size_ge_three; omega
  have hpred : cyclicSuccessor (⟨n, by omega⟩ : Fin (n + 1)) = ⟨0, by omega⟩ := by
    apply Fin.ext
    simp [cyclicSuccessor, cyclicVertexIndex]
  have hsucc : cyclicSuccessor (⟨0, by omega⟩ : Fin (n + 1)) = ⟨1, by omega⟩ := by
    apply Fin.ext
    simp [cyclicSuccessor, cyclicVertexIndex, Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
  obtain ⟨delta, hdelta, hsmall⟩ := exists_horizontal_shortEdge_insertion hRI q hq
    ⟨0, by omega⟩ hzero hothers ⟨n, by omega⟩ hpred
  refine ⟨delta, hdelta, ?_⟩
  intro epsilon hepsilon hlt
  obtain ⟨hp, hvalue⟩ := hsmall epsilon hepsilon hlt
  refine ⟨hp, ?_⟩
  have hstart : horizontalComplementWord q epsilon 0 =
      ((q ⟨0, by omega⟩).1 - epsilon, 0) := by
    simp [horizontalComplementWord]
  have hfinish : horizontalComplementWord q epsilon (n + 1) =
      ((q ⟨0, by omega⟩).1, 0) := by
    simp [horizontalComplementWord, ← hzero]
  rw [← horizontal_word_marked_cap_expansion (horizontalComplementWord q epsilon)
    (n + 1) (q ⟨0, by omega⟩).1 epsilon hepsilon (by omega) hstart hfinish,
    ← polygonAmplitude_eq_horizontalComplement q hzero epsilon hp]
  simpa only [hsucc] using hvalue






end DirectGLSSW.HorizontalShortEdge
