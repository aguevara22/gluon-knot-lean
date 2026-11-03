import DirectGLSSW.RealPolygons
import DirectGLSSW.ShortEdgeSignStability
import DirectGLSSW.ShortEdgeCyclicAdapter

namespace DirectGLSSW.ShortEdgeCyclicG1

open DirectGLSSW

private theorem polygonHDet_rotate {q : ℕ → PlanarPoint ℝ} (a b c : ℕ) :
    polygonHDet q a b c = polygonHDet q b c a := by
  unfold polygonHDet planarDet
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

private theorem polygonHDet_swap_first {q : ℕ → PlanarPoint ℝ} (a b c : ℕ) :
    polygonHDet q a b c = -polygonHDet q b a c := by
  unfold polygonHDet planarDet
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

private theorem polygonHDet_swap_last {q : ℕ → PlanarPoint ℝ} (a b c : ℕ) :
    polygonHDet q a b c = -polygonHDet q a c b := by
  unfold polygonHDet planarDet
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

private theorem polygonHDet_ne_of_distinct_bounded
    (q : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hordered : ∀ i k j, i < k → k < j → j ≤ N → polygonHDet q i k j ≠ 0)
    (i k j : ℕ) (hi : i ≤ N) (hk : k ≤ N) (hj : j ≤ N)
    (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) :
    polygonHDet q i k j ≠ 0 := by
  by_cases hik' : i < k
  · by_cases hkj' : k < j
    · exact hordered i k j hik' hkj' hj
    · have hjk : j < k := by omega
      by_cases hij' : i < j
      · have h := hordered i j k hij' hjk hk
        rw [polygonHDet_swap_last (q := q) i k j]
        exact neg_ne_zero.mpr h
      · have hji : j < i := by omega
        have h := hordered j i k hji hik' hk
        rw [polygonHDet_rotate (q := q) i k j, polygonHDet_rotate (q := q) k j i]
        exact h
  · have hki : k < i := by omega
    by_cases hij' : i < j
    · have h := hordered k i j hki hij' hj
      rw [polygonHDet_swap_first (q := q) i k j]
      exact neg_ne_zero.mpr h
    · have hji : j < i := by omega
      by_cases hkj' : k < j
      · have h := hordered k j i hkj' hji hi
        rw [polygonHDet_rotate (q := q) i k j]
        exact h
      · have hjk : j < k := by omega
        have h := hordered j k i hjk hki hi
        rw [polygonHDet_rotate (q := q) i k j,
          polygonHDet_swap_first (q := q) k j i]
        exact neg_ne_zero.mpr h

theorem inserted_cyclicNoncollinear_of_openStability
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a : Fin n)
    (ε : ℝ) (v : PlanarPoint ℝ)
    (hcore : ShortEdgeSignStability.CoreHGeneric
      (fun k => rootedPolygonWord q
        (DirectGLSSW.ShortEdgeCyclicAdapter.lastCoreRoot (by omega : 0 < n)) k)
      (n - 1))
    (hdir : ShortEdgeSignStability.DirectionGeneric
      (fun k => rootedPolygonWord q
        (DirectGLSSW.ShortEdgeCyclicAdapter.lastCoreRoot (by omega : 0 < n)) k)
      (n - 1) a.val v)
    (hst : ShortEdgeSignStability.ShortEdgeStability
      (fun k => rootedPolygonWord q
        (DirectGLSSW.ShortEdgeCyclicAdapter.lastCoreRoot (by omega : 0 < n)) k)
      (n - 1) a.val v ε (by omega) hcore hdir) :
    cyclicNoncollinear (DirectGLSSW.ShortEdgeCyclicAdapter.insertCyclicAfter q a ε v) := by
  let w : ℕ → PlanarPoint ℝ := fun k => rootedPolygonWord q
    (DirectGLSSW.ShortEdgeCyclicAdapter.lastCoreRoot (by omega : 0 < n)) k
  let p : ℕ → PlanarPoint ℝ := ShortEdgeSignStability.insertAfter w a.val ε v
  have hordered : ∀ i k j, i < k → k < j → j ≤ n → polygonHDet p i k j ≠ 0 := by
    intro i k j hik hkj hj
    have hs := hst.insertedG1 i k j hik hkj (by omega)
    simpa [p, w, Nat.sub_add_cancel (by omega : 1 ≤ n)] using hs
  have hindex (x : ℕ) (hx : x ≤ n) :
      DirectGLSSW.ShortEdgeCyclicAdapter.insertCyclicAfter q a ε v
        ⟨x, by omega⟩ = p x := by
    calc
      _ = rootedPolygonWord
          (DirectGLSSW.ShortEdgeCyclicAdapter.insertCyclicAfter q a ε v)
          (DirectGLSSW.ShortEdgeCyclicAdapter.lastParentRoot n) x :=
            (DirectGLSSW.ShortEdgeCyclicAdapter.parentLastRootWord_eval
              q a ε v x (by omega)).symm
      _ = ShortEdgeSignStability.insertAfter w a.val ε v x :=
            DirectGLSSW.ShortEdgeCyclicAdapter.insertedLastRootWord_eq_openInsertAfter
              (by omega) q a ε v x hx
      _ = p x := rfl
  intro A B C hAB hBC hAC
  change planarDet
    (DirectGLSSW.ShortEdgeCyclicAdapter.insertCyclicAfter q a ε v B -
      DirectGLSSW.ShortEdgeCyclicAdapter.insertCyclicAfter q a ε v C)
    (DirectGLSSW.ShortEdgeCyclicAdapter.insertCyclicAfter q a ε v A -
      DirectGLSSW.ShortEdgeCyclicAdapter.insertCyclicAfter q a ε v C) ≠ 0
  rw [hindex B.val (by have := B.isLt; omega),
    hindex C.val (by have := C.isLt; omega),
    hindex A.val (by have := A.isLt; omega)]
  change polygonHDet p A.val B.val C.val ≠ 0
  exact polygonHDet_ne_of_distinct_bounded p n hordered A.val B.val C.val
    (by have := A.isLt; omega) (by have := B.isLt; omega) (by have := C.isLt; omega)
    (by intro h; exact hAB (Fin.ext h))
    (by intro h; exact hBC (Fin.ext h))
    (by intro h; exact hAC (Fin.ext h))

end DirectGLSSW.ShortEdgeCyclicG1
