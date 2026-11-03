import DirectGLSSW.ClippedCapPairing
import DirectGLSSW.CapSubwordBridge
import DirectGLSSW.GlobalCapAlgebra
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.DistinctCapSubword

open DirectGLSSW
open DirectGLSSW.CapActualBranches
open DirectGLSSW.CapSubwordBridge
open DirectGLSSW.CapMatrixRestriction
open DirectGLSSW.ClippedCapPairing

/-- Concrete `F(c)` endpoint factor for a fixed larger word with terminal
point `q 0`. -/
noncomputable def capStartFactor (q : ℕ → PlanarPoint ℝ)
    (c : PlanarPoint ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  capEndpointMatrix q c (fun k => scalarSignValue (q k).2) n

/-- Concrete `U(d) = S R G(d)` factor; its final factor uses the unchanged
terminal point `q 0`. -/
noncomputable def capTerminalFactor (q : ℕ → PlanarPoint ℝ)
    (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal (GlobalCapAlgebra.lineCapHeights q n) *
    globalCapResolvent
      (capInternalMatrix q (fun k => scalarSignValue (q k).2) n)
      (GlobalCapAlgebra.lineCapHeights q n) *
    capTerminalMatrix q (fun k => scalarSignValue (q k).2) n

/-- The actual larger cap pairing factors as its start endpoint factor times
`S R G(d)`, preserving the original terminal point `d = q 0`. -/
theorem actual_globalCapPairing_eq_start_mul_terminal
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : PlanarPoint ℝ) :
    globalCapPairing
        (capEndpointMatrix q c (fun k => scalarSignValue (q k).2) n)
        (capInternalMatrix q (fun k => scalarSignValue (q k).2) n)
        (capTerminalMatrix q (fun k => scalarSignValue (q k).2) n)
        (fun r : Fin n => scalarSignValue (q (r.val + 1)).2) =
      capStartFactor q c n * capTerminalFactor q n := by
  have hh : GlobalCapAlgebra.lineCapHeights q n =
      (fun r : Fin n => scalarSignValue (q (r.val + 1)).2) := rfl
  unfold globalCapPairing capStartFactor capTerminalFactor
  rw [hh]
  simp [Matrix.mul_assoc]

/-- The finite cap theorem with caller-supplied near data that agrees with
its internal vertex heights. -/
theorem polygonAmplitude_eq_twoEndpoint_globalCapPairing_withNear
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (c : PlanarPoint ℝ) (m : ℕ) (hm : 0 < m)
    (hc : c.2 = 0) (hd : (q 0).2 = 0) (hcd : c.1 < (q 0).1)
    (hcap : CyclicGeneric (clippedCapWord q c m))
    (near : ℕ → ℚ)
    (hnear : ∀ r : Fin m,
      near (r.val + 1) = scalarSignValue (q (r.val + 1)).2) :
    polygonAmplitude (clippedCapWord q c m) hcap =
      globalCapPairing
        (capEndpointMatrix q c near m)
        (capInternalMatrix q near m)
        (capTerminalMatrix q near m)
        (fun r : Fin m => near (r.val + 1))
        ⟨0, by omega⟩ ⟨m - 1, by omega⟩ := by
  let N := m + 2
  let Q := clippedCapWord q c m
  let root : Fin N := ⟨m + 1, by omega⟩
  let cap : ℕ → PlanarPoint ℝ := capWord q c m
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
    have hr : (⟨k - 1, by omega⟩ : Fin m).val + 1 = k := by simp; omega
    calc
      H 0 k (m + 1) = scalarSignValue (cap k).2 :=
        HorizontalShortEdge.horizontal_word_top_sign cap (m + 1) (q 0).1
          ((q 0).1 - c.1) heps hstart hfinish k
      _ = scalarSignValue (q k).2 := by rw [hpoint]
      _ = near k := by
        have hknear := hnear ⟨k - 1, by omega⟩
        simpa [hr] using hknear.symm
  have hgap : 0 + 1 < m + 1 := by omega
  have hmarked_cut := markedAmplitude_eq_capCutExpansion_middleNear near H hgap htop
  have hcut_sum :
      capCutExpansion (j := m + 1) near
        (ordinaryCurrent (fun _ k _ => near k) H) 0 =
      weightedCutSumNonempty near
        (capActualBranch q c near m) 0 (m + 1) := by
    symm
    simpa [capActualBranch, cap, H] using
      weightedCutSumNonempty_eq_capCutExpansion near
        (capActualBranch q c near m) (by omega)
  have hglobal := weightedCutSumNonempty_cap_actual_eq_globalCapPairing
    q c near (n := m) (by omega)
  calc
    polygonAmplitude Q hcap = markedAmplitude nearTriple H 0 (m + 1) := hmarked_root
    _ = capCutExpansion (j := m + 1) near
        (ordinaryCurrent (fun _ k _ => near k) H) 0 := hmarked_cut
    _ = weightedCutSumNonempty near
        (capActualBranch q c near m) 0 (m + 1) := hcut_sum
    _ = globalCapPairing
        (capEndpointMatrix q c near m)
        (capInternalMatrix q near m)
        (capTerminalMatrix q near m)
        (fun r : Fin m => near (r.val + 1))
        ⟨0, by omega⟩ ⟨m - 1, by omega⟩ := hglobal

/-- An arbitrary actual entry of the larger cap pairing is the amplitude of
its selected consecutive cap, with the original terminal point `q 0`. -/
theorem actual_globalCapPairing_entry_eq_selected_cap_amplitude
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (_hd0 : (q 0).2 = 0)
    (a b : Fin n) (hab : a.val ≤ b.val)
    (c : PlanarPoint ℝ) (hc0 : c.2 = 0) (hcd : c.1 < (q 0).1)
    (hcap : CyclicGeneric
      (fun i : Fin ((b.val - a.val + 1) + 2) =>
        capWord (capSubwordNat q a.val (b.val - a.val + 1)) c
          (b.val - a.val + 1) i.val)) :
    globalCapPairing
        (capEndpointMatrix q c (fun k => scalarSignValue (q k).2) n)
        (capInternalMatrix q (fun k => scalarSignValue (q k).2) n)
        (capTerminalMatrix q (fun k => scalarSignValue (q k).2) n)
        (fun r : Fin n => scalarSignValue (q (r.val + 1)).2) a b =
      polygonAmplitude
        (fun i : Fin ((b.val - a.val + 1) + 2) =>
          capWord (capSubwordNat q a.val (b.val - a.val + 1)) c
            (b.val - a.val + 1) i.val) hcap := by
  let m := b.val - a.val + 1
  let qAB := capSubwordNat q a.val m
  let d := fun k => scalarSignValue (q k).2
  let dAB := capSubwordNear d a.val
  have hm : 0 < m := by dsimp [m]; omega
  have hbound : a.val + m ≤ n := by
    dsimp [m]
    have hb := b.isLt
    omega
  let e := consecutiveBlockEmbedding a.val hbound
  have he0 : e ⟨0, by omega⟩ = a := by
    apply Fin.ext
    simp [e, consecutiveBlockEmbedding]
  have heb : e ⟨m - 1, by omega⟩ = b := by
    apply Fin.ext
    dsimp [e, consecutiveBlockEmbedding, m]
    omega
  have hblock := capPairing_submatrix_consecutive q c d hbound
  have hentry := congrArg
    (fun M : Matrix (Fin m) (Fin m) ℚ => M ⟨0, by omega⟩ ⟨m - 1, by omega⟩)
    hblock
  change globalCapPairing
      (capEndpointMatrix q c d n)
      (capInternalMatrix q d n)
      (capTerminalMatrix q d n)
      (fun r : Fin n => d (r.val + 1)) (e ⟨0, by omega⟩) (e ⟨m - 1, by omega⟩) = _ at hentry
  rw [he0, heb] at hentry
  dsimp only at hentry
  have hnear : ∀ r : Fin m,
      dAB (r.val + 1) = scalarSignValue (qAB (r.val + 1)).2 := by
    intro r
    have hrpos : 0 < r.val + 1 := by omega
    have hrbound : r.val + 1 ≤ m := by have := r.isLt; omega
    simp [dAB, d, capSubwordNear, qAB, capSubwordNat, capSubwordFin,
      hrpos.ne', hrbound]
  have hcapAB : CyclicGeneric (clippedCapWord qAB c m) := by
    simpa [m, qAB, capSubwordNat, clippedCapWord] using hcap
  have hlocal := polygonAmplitude_eq_twoEndpoint_globalCapPairing_withNear
    hRI qAB c m hm hc0 (by simp [qAB, capSubwordNat, capSubwordFin, _hd0]) hcd
    hcapAB dAB hnear
  have hlocal' :
      globalCapPairing
          (capEndpointMatrix qAB c dAB m)
          (capInternalMatrix qAB dAB m)
          (capTerminalMatrix qAB dAB m)
          (fun r : Fin m => dAB (r.val + 1))
          ⟨0, by omega⟩ ⟨m - 1, by omega⟩ =
        polygonAmplitude
          (fun i : Fin (m + 2) => capWord qAB c m i.val) hcap := by
    simpa [clippedCapWord, m, qAB, capSubwordNat] using hlocal.symm
  calc
    globalCapPairing
        (capEndpointMatrix q c d n)
        (capInternalMatrix q d n)
        (capTerminalMatrix q d n)
        (fun r : Fin n => d (r.val + 1)) a b =
      globalCapPairing
          (capEndpointMatrix qAB c dAB m)
          (capInternalMatrix qAB dAB m)
          (capTerminalMatrix qAB dAB m)
          (fun r : Fin m => dAB (r.val + 1))
          ⟨0, by omega⟩ ⟨m - 1, by omega⟩ := hentry
    _ = polygonAmplitude
          (fun i : Fin (m + 2) => capWord qAB c m i.val) hcap := hlocal'
    _ = polygonAmplitude
          (fun i : Fin ((b.val - a.val + 1) + 2) =>
            capWord (capSubwordNat q a.val (b.val - a.val + 1)) c
              (b.val - a.val + 1) i.val) hcap := by
      rfl

/-- The selected actual entry is the corresponding `F(c) U(d)` matrix
entry, with terminal factor `U(d) = S R G(d)`. -/
theorem capStart_mul_capTerminal_entry_eq_selected_cap_amplitude
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hd0 : (q 0).2 = 0)
    (a b : Fin n) (hab : a.val ≤ b.val)
    (c : PlanarPoint ℝ) (hc0 : c.2 = 0) (hcd : c.1 < (q 0).1)
    (hcap : CyclicGeneric
      (fun i : Fin ((b.val - a.val + 1) + 2) =>
        capWord (capSubwordNat q a.val (b.val - a.val + 1)) c
          (b.val - a.val + 1) i.val)) :
    (capStartFactor q c n * capTerminalFactor q n) a b =
      polygonAmplitude
        (fun i : Fin ((b.val - a.val + 1) + 2) =>
          capWord (capSubwordNat q a.val (b.val - a.val + 1)) c
            (b.val - a.val + 1) i.val) hcap := by
  have hfactor := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℚ => M a b)
    (actual_globalCapPairing_eq_start_mul_terminal q n c)
  calc
    (capStartFactor q c n * capTerminalFactor q n) a b =
      globalCapPairing
        (capEndpointMatrix q c (fun k => scalarSignValue (q k).2) n)
        (capInternalMatrix q (fun k => scalarSignValue (q k).2) n)
        (capTerminalMatrix q (fun k => scalarSignValue (q k).2) n)
        (fun r : Fin n => scalarSignValue (q (r.val + 1)).2) a b := hfactor.symm
    _ = polygonAmplitude
        (fun i : Fin ((b.val - a.val + 1) + 2) =>
          capWord (capSubwordNat q a.val (b.val - a.val + 1)) c
            (b.val - a.val + 1) i.val) hcap :=
      actual_globalCapPairing_entry_eq_selected_cap_amplitude
        hRI q n hd0 a b hab c hc0 hcd hcap








end DirectGLSSW.DistinctCapSubword
