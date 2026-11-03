import DirectGLSSW.CyclicWords
import DirectGLSSW.ShortEdgeSignStability

namespace DirectGLSSW.ShortEdgeCyclicAdapter

open DirectGLSSW

def lastCoreRoot {n : ℕ} (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

def lastParentRoot (n : ℕ) : Fin (n + 1) :=
  ⟨n, by omega⟩

def insertCyclicAfter {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a : Fin n) (ε : ℝ) (v : PlanarPoint ℝ) : Fin (n + 1) → PlanarPoint ℝ :=
  fun i =>
    if h : i.val ≤ a.val then q ⟨i.val, lt_of_le_of_lt h a.isLt⟩ else
    if hmid : i.val = a.val + 1 then
      ((q a).1 + ε * v.1, (q a).2 + ε * v.2) else
      q ⟨i.val - 1, by have := i.isLt; have := a.isLt; omega⟩

theorem coreLastRootWord_eval {n : ℕ} (hn : 0 < n)
    (q : Fin n → PlanarPoint ℝ) (k : ℕ) (hk : k < n) :
    rootedPolygonWord q (lastCoreRoot hn) k = q ⟨k, hk⟩ := by
  apply congrArg q
  apply Fin.ext
  rw [cyclicVertexIndex_val (lastCoreRoot hn) hk]
  simp [lastCoreRoot]
  split_ifs <;> omega

theorem parentLastRootWord_eval {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a : Fin n) (ε : ℝ) (v : PlanarPoint ℝ)
    (k : ℕ) (hk : k < n + 1) :
    rootedPolygonWord (insertCyclicAfter q a ε v) (lastParentRoot n) k =
      insertCyclicAfter q a ε v ⟨k, hk⟩ := by
  apply congrArg (insertCyclicAfter q a ε v)
  apply Fin.ext
  rw [cyclicVertexIndex_val (lastParentRoot n) hk]
  simp [lastParentRoot]

theorem insertedLastRootWord_eq_openInsertAfter {n : ℕ} (hn : 0 < n)
    (q : Fin n → PlanarPoint ℝ) (a : Fin n) (ε : ℝ) (v : PlanarPoint ℝ)
    (k : ℕ) (hk : k ≤ n) :
    rootedPolygonWord (insertCyclicAfter q a ε v) (lastParentRoot n) k =
      ShortEdgeSignStability.insertAfter
        (fun x => rootedPolygonWord q (lastCoreRoot hn) x) a.val ε v k := by
  rw [parentLastRootWord_eval q a ε v k (by omega)]
  unfold insertCyclicAfter ShortEdgeSignStability.insertAfter
  by_cases hle : k ≤ a.val
  · have hkcore : k < n := by have := a.isLt; omega
    simp [hle]
    rw [coreLastRootWord_eval hn q k hkcore]
  · by_cases hmid : k = a.val + 1
    · have ha : a.val < n := a.isLt
      simp [hle, hmid]
      rw [coreLastRootWord_eval hn q a.val ha]
      have hidx : (⟨a.val, ha⟩ : Fin n) = a := Fin.ext rfl
      rw [hidx]
      simp
    · have hki : a.val + 1 < k := by omega
      have hkcore : k - 1 < n := by have := a.isLt; omega
      simp [hle, hmid]
      rw [coreLastRootWord_eval hn q (k - 1) hkcore]

theorem coreHGeneric_of_cyclicNoncollinear {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint ℝ) (hq : cyclicNoncollinear q) :
    ShortEdgeSignStability.CoreHGeneric
      (fun k => rootedPolygonWord q (lastCoreRoot (by omega : 0 < n)) k) (n - 1) := by
  intro i k j hik hkj hj
  have hinterval := rootedPolygonWord_noncollinear q hq
    (lastCoreRoot (by omega : 0 < n))
  exact hinterval i k j (by omega) hik hkj hj

end DirectGLSSW.ShortEdgeCyclicAdapter
