import DirectGLSSW.CapActualBranches
import DirectGLSSW.CapMarkedPairing
import DirectGLSSW.CapCutExpansion
import DirectGLSSW.HorizontalComplement
import DirectGLSSW.NearData
import DirectGLSSW.RealPolygons
import DirectGLSSW.CyclicWords
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.ClippedCapPairing

open DirectGLSSW
open scoped BigOperators

/-- The finite cap word c,q₁,…,qₘ,d where q₀=d. -/
def clippedCapWord (q : ℕ → PlanarPoint ℝ) (c : PlanarPoint ℝ) (m : ℕ) :
    Fin (m + 2) → PlanarPoint ℝ :=
  fun i => CapActualBranches.capWord q c m i.val

/-- The actual polygon amplitude of a two-endpoint horizontal cap is the
first-to-last global pairing with the internal height signs. -/
theorem polygonAmplitude_eq_twoEndpoint_globalCapPairing
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (c : PlanarPoint ℝ) (m : ℕ) (hm : 0 < m)
    (hc : c.2 = 0) (hd : (q 0).2 = 0) (hcd : c.1 < (q 0).1)
    (hcap : CyclicGeneric (clippedCapWord q c m)) :
    polygonAmplitude (clippedCapWord q c m) hcap =
      globalCapPairing
        (CapActualBranches.capEndpointMatrix q c (fun k => scalarSignValue (q k).2) m)
        (CapActualBranches.capInternalMatrix q (fun k => scalarSignValue (q k).2) m)
        (CapActualBranches.capTerminalMatrix q (fun k => scalarSignValue (q k).2) m)
        (fun r : Fin m => scalarSignValue (q (r.val + 1)).2)
        ⟨0, by omega⟩ ⟨m - 1, by omega⟩ := by
  let N := m + 2
  let Q := clippedCapWord q c m
  let root : Fin N := ⟨m + 1, by omega⟩
  let cap : ℕ → PlanarPoint ℝ := CapActualBranches.capWord q c m
  let near : ℕ → ℚ := fun k => scalarSignValue (q k).2
  let nearTriple : TripleArray := fun _ k _ => near k
  let H : TripleArray := polygonSignArray cap
  let Hroot : TripleArray := polygonSignArray (rootedPolygonWord Q root)
  have hidx (k : ℕ) (hk : k ≤ m + 1) :
      cyclicVertexIndex root k = (⟨k, by omega⟩ : Fin N) := by
    apply Fin.ext
    change (root.val + 1 + k) % N = k
    have hsum : root.val + 1 + k = k + N := by dsimp [root, N]; omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hword (k : ℕ) (hk : k ≤ m + 1) :
      rootedPolygonWord Q root k = cap k := by
    rw [rootedPolygonWord, hidx k hk]
    rfl
  have hinterval : ∀ a b z, 0 ≤ a → a < b → b < z → z ≤ m + 1 →
      Hroot a b z = H a b z := by
    intro a b z _ hab hbz hzm
    have ha := hword a (by omega)
    have hb := hword b (by omega)
    have hz := hword z hzm
    simp [Hroot, H, polygonSignArray, polygonHDet, ha, hb, hz]
  have hmarked_root :
      polygonAmplitude Q hcap = markedAmplitude nearTriple H 0 (m + 1) := by
    have hroot := polygonAmplitude_eq_rootedSpinorAmplitude hRI Q hcap root
    have htree := rootedSpinorAmplitude_eq_markedTreeSum
      (by omega) Q hcap.g1 root
    calc
      polygonAmplitude Q hcap = rootedSpinorAmplitude Q root := hroot
      _ = markedTreeSum Hroot Hroot 0 (N - 1) := htree
      _ = markedAmplitude Hroot Hroot 0 (m + 1) := by
        simpa [N] using markedTreeSum_eq_markedAmplitude Hroot Hroot (by omega)
      _ = markedAmplitude nearTriple H 0 (m + 1) := by
        exact markedAmplitude_congr_interval Hroot nearTriple Hroot H (by omega) hinterval
  have hstart : cap 0 = ((q 0).1 - ((q 0).1 - c.1), 0) := by
    change c = _
    apply Prod.ext
    · ring
    · exact hc
  have hfinish : cap (m + 1) = ((q 0).1, 0) := by
    change (if m + 1 = 0 then c else if m + 1 = m + 1 then q 0 else q (m + 1)) = _
    rw [if_neg (by omega : m + 1 ≠ 0), if_pos rfl]
    exact Prod.ext rfl hd
  have heps : 0 < (q 0).1 - c.1 := by linarith
  have htop : ∀ k, k ∈ Finset.Ioo 0 (m + 1) → H 0 k (m + 1) = near k := by
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    have hpoint : cap k = q k := by
      change (if k = 0 then c else if k = m + 1 then q 0 else q k) = q k
      rw [if_neg (by omega : k ≠ 0), if_neg (by omega : k ≠ m + 1)]
    calc
      H 0 k (m + 1) = scalarSignValue (cap k).2 :=
        HorizontalShortEdge.horizontal_word_top_sign cap (m + 1) (q 0).1
          ((q 0).1 - c.1) heps hstart hfinish k
      _ = near k := by simp [near, hpoint]
  have hmarked_cut := markedAmplitude_eq_capCutExpansion_middleNear
    near H (by omega : 0 + 1 < m + 1) htop
  have hcut_sum :
      capCutExpansion (j := m + 1) near
        (ordinaryCurrent (fun _ k _ => near k) H) 0 =
      weightedCutSumNonempty near
        (CapActualBranches.capActualBranch q c near m) 0 (m + 1) := by
    symm
    simpa [CapActualBranches.capActualBranch, cap, near, H] using
      weightedCutSumNonempty_eq_capCutExpansion near
        (CapActualBranches.capActualBranch q c near m) (by omega : 0 < m + 1)
  have hglobal := CapActualBranches.weightedCutSumNonempty_cap_actual_eq_globalCapPairing
    q c near (n := m) (by omega)
  calc
    polygonAmplitude Q hcap = markedAmplitude nearTriple H 0 (m + 1) := hmarked_root
    _ = capCutExpansion (j := m + 1) near
        (ordinaryCurrent (fun _ k _ => near k) H) 0 := hmarked_cut
    _ = weightedCutSumNonempty near
        (CapActualBranches.capActualBranch q c near m) 0 (m + 1) := hcut_sum
    _ = globalCapPairing
        (CapActualBranches.capEndpointMatrix q c near m)
        (CapActualBranches.capInternalMatrix q near m)
        (CapActualBranches.capTerminalMatrix q near m)
        (fun r : Fin m => near (r.val + 1))
        ⟨0, by omega⟩ ⟨m - 1, by omega⟩ := hglobal




end DirectGLSSW.ClippedCapPairing
