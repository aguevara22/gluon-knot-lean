import DirectGLSSW.GlobalCapEntry
import DirectGLSSW.EndpointRowDirect
import DirectGLSSW.CurrentTranslation
import DirectGLSSW.RealPolygons
import DirectGLSSW.NearData
import DirectGLSSW.TreeWeights

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.EndpointMarkedCap
open DirectGLSSW
open scoped BigOperators

private theorem translateTriple_one_apply_local (A : TripleArray) :
    CurrentTranslation.translateTriple 1 A = fun x k y => A (x + 1) (k + 1) (y + 1) := by
  funext x k y
  simp only [CurrentTranslation.translateTriple]
  congr 1 <;> omega

private theorem translateInterval_one_apply_local (b : IntervalArray) :
    CurrentTranslation.translateInterval 1 b = fun x y => b (x + 1) (y + 1) := by
  funext x y
  simp only [CurrentTranslation.translateInterval]
  congr 1 <;> omega

private theorem cutContribution_succ_translate_local (D H : TripleArray) (b : IntervalArray)
    (i j : ℕ) (S : Finset ℕ) :
    cutContribution D H b (i + 1) (j + 1) (S.image Nat.succ) =
      cutContribution (CurrentTranslation.translateTriple 1 D)
        (CurrentTranslation.translateTriple 1 H)
        (CurrentTranslation.translateInterval 1 b) i j S := by
  unfold cutContribution
  rw [ShortEdgeWeighted.cutVertices_succ_image]
  have hg := ShortEdgeWeighted.gateProduct_map D H Nat.succ i j (cutVertices i j S)
  have hb := ShortEdgeWeighted.branchProduct_map b Nat.succ (cutVertices i j S)
  rw [hg, hb, ← translateTriple_one_apply_local, ← translateTriple_one_apply_local,
    ← translateInterval_one_apply_local]

private theorem phi_succ_translate_local (D H : TripleArray) (b : IntervalArray)
    (i j : ℕ) :
    phi (CurrentTranslation.translateTriple 1 D) (CurrentTranslation.translateTriple 1 H)
        (CurrentTranslation.translateInterval 1 b) i j = phi D H b (i + 1) (j + 1) := by
  classical
  let P := Finset.Ioo i j
  let Q := Finset.Ioo (i + 1) (j + 1)
  have hsucc : ∀ S ∈ P.powerset, S.image Nat.succ ∈ Q.powerset := by
    intro S hS
    apply Finset.mem_powerset.mpr
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hyI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hS hy)
    simp only [P, Q, Finset.mem_Ioo]
    omega
  have hpred : ∀ T ∈ Q.powerset, T.image Nat.pred ∈ P.powerset := by
    intro T hT
    apply Finset.mem_powerset.mpr
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hyI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hy)
    have hypos : 0 < y := by simp only [Q, Finset.mem_Ioo] at hyI; omega
    have hp : Nat.pred y + 1 = y := Nat.succ_pred_eq_of_pos hypos
    rw [← hp] at hyI
    simp only [P, Finset.mem_Ioo]
    omega
  have hleft : ∀ (S : Finset ℕ), S ∈ P.powerset →
      (S.image Nat.succ).image Nat.pred = S := by
    intro S hS
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
      rw [← hzy, Nat.pred_succ]
      exact hz
    · intro hx
      refine ⟨Nat.succ x, ⟨x, hx, rfl⟩, ?_⟩
      simp
  have hright : ∀ (T : Finset ℕ), T ∈ Q.powerset →
      (T.image Nat.pred).image Nat.succ = T := by
    intro T hT
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
      have hzI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hz)
      have hzpos : 0 < z := by simp only [Q, Finset.mem_Ioo] at hzI; omega
      rw [← hzy, Nat.succ_pred_eq_of_pos hzpos]
      exact hz
    · intro hx
      have hxI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hx)
      have hxpos : 0 < x := by simp only [Q, Finset.mem_Ioo] at hxI; omega
      refine ⟨Nat.pred x, ⟨x, hx, rfl⟩, ?_⟩
      exact Nat.succ_pred_eq_of_pos hxpos
  unfold phi
  change (∑ S ∈ P.powerset,
      cutContribution (CurrentTranslation.translateTriple 1 D)
        (CurrentTranslation.translateTriple 1 H)
        (CurrentTranslation.translateInterval 1 b) i j S) =
    ∑ T ∈ Q.powerset, cutContribution D H b (i + 1) (j + 1) T
  symm
  refine Finset.sum_bij'
    (fun T _ => T.image Nat.pred)
    (fun S _ => S.image Nat.succ) ?_ ?_ ?_ ?_ ?_
  · exact hpred
  · exact hsucc
  · exact hright
  · exact hleft
  · intro T hT
    calc
      cutContribution D H b (i + 1) (j + 1) T =
          cutContribution D H b (i + 1) (j + 1) ((T.image Nat.pred).image Nat.succ) := by
            congr 1
            exact (hright T hT).symm
      _ = cutContribution (CurrentTranslation.translateTriple 1 D)
            (CurrentTranslation.translateTriple 1 H)
            (CurrentTranslation.translateInterval 1 b) i j (T.image Nat.pred) :=
              cutContribution_succ_translate_local D H b i j (T.image Nat.pred)

private theorem translateTriple_succ_local (s : ℕ) (A : TripleArray) :
    CurrentTranslation.translateTriple (s + 1) A =
      CurrentTranslation.translateTriple 1 (CurrentTranslation.translateTriple s A) := by
  funext x k y
  simp only [CurrentTranslation.translateTriple]
  congr 1 <;> omega

private theorem translateInterval_succ_local (s : ℕ) (A : IntervalArray) :
    CurrentTranslation.translateInterval (s + 1) A =
      CurrentTranslation.translateInterval 1 (CurrentTranslation.translateInterval s A) := by
  funext x y
  simp only [CurrentTranslation.translateInterval]
  congr 1 <;> omega

private theorem phi_translate_local (D H : TripleArray) (b : IntervalArray)
    (s i j : ℕ) :
    phi (CurrentTranslation.translateTriple s D) (CurrentTranslation.translateTriple s H)
      (CurrentTranslation.translateInterval s b) i j = phi D H b (s + i) (s + j) := by
  induction s generalizing i j with
  | zero =>
      have hD : CurrentTranslation.translateTriple 0 D = D := by
        funext x k y
        simp [CurrentTranslation.translateTriple]
      have hH : CurrentTranslation.translateTriple 0 H = H := by
        funext x k y
        simp [CurrentTranslation.translateTriple]
      have hb : CurrentTranslation.translateInterval 0 b = b := by
        funext x y
        simp [CurrentTranslation.translateInterval]
      rw [hD, hH, hb]
      simp
  | succ s ih =>
      rw [translateTriple_succ_local s D, translateTriple_succ_local s H,
        translateInterval_succ_local s b, phi_succ_translate_local]
      rw [ih (i + 1) (j + 1)]
      congr 1 <;> omega

private theorem markedAmplitude_translate
    (D H : TripleArray) (s i j : ℕ) (hij : i < j) :
    markedAmplitude (CurrentTranslation.translateTriple s D)
      (CurrentTranslation.translateTriple s H) i j =
    markedAmplitude D H (s + i) (s + j) := by
  unfold markedAmplitude
  let B : IntervalArray := ordinaryCurrent D H
  have hcurr : ∀ x y, x < y →
      ordinaryCurrent (CurrentTranslation.translateTriple s D)
        (CurrentTranslation.translateTriple s H) x y = B (s + x) (s + y) := by
    intro x y hxy
    exact CurrentTranslation.ordinaryCurrent_translate D H s x y hxy
  have hinterval : ∀ x y, x < y →
      ordinaryCurrent (CurrentTranslation.translateTriple s D)
        (CurrentTranslation.translateTriple s H) x y =
      CurrentTranslation.translateInterval s B x y := by
    intro x y hxy
    exact hcurr x y hxy
  have hDneg : (fun x k y => -(CurrentTranslation.translateTriple s H) x k y) =
      CurrentTranslation.translateTriple s (fun x k y => -H x k y) := by
    funext x k y
    simp [CurrentTranslation.translateTriple]
  rw [hDneg]
  calc
    phi (CurrentTranslation.translateTriple s D)
        (CurrentTranslation.translateTriple s (fun x k y => -H x k y))
        (ordinaryCurrent (CurrentTranslation.translateTriple s D)
          (CurrentTranslation.translateTriple s H)) i j =
      phi (CurrentTranslation.translateTriple s D)
        (CurrentTranslation.translateTriple s (fun x k y => -H x k y))
        (CurrentTranslation.translateInterval s B) i j := by
          exact phi_congr_upper
            (CurrentTranslation.translateTriple s D)
            (CurrentTranslation.translateTriple s (fun x k y => -H x k y))
            (fun x y hxy => hinterval x y hxy) hij
    _ = phi D (fun a b c => -H a b c) B (s + i) (s + j) := by
          exact phi_translate_local D (fun a b c => -H a b c) B s i j

private theorem endpointPoint_subword {n : ℕ} (q : ℕ → PlanarPoint ℝ)
    (a b : Fin n) (hab : a.val < b.val) :
    ∀ x (hx : x ≤ b.val - a.val + 1),
      GlobalCapEntry.lineCapCore q a b ⟨x, by have hb := b.isLt; omega⟩ =
        EndpointCurrent.endpointWord q a.val (a.val + x) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp [GlobalCapEntry.lineCapCore, CapSubwordBridge.capSubwordFin,
      EndpointCurrent.endpointWord]
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
    have hb := b.isLt
    have hfin : x < b.val - a.val + 1 + 1 := by omega
    simp [GlobalCapEntry.lineCapCore, CapSubwordBridge.capSubwordFin,
      EndpointCurrent.endpointWord, hx0, hfin]

theorem endpointMarked_lineCapCore (hRI : GLSSWRootIndependence)
    {n : ℕ} (d : ℕ → ℚ) (q : ℕ → PlanarPoint ℝ)
    (a b : Fin n) (hab : a.val < b.val)
    (hcap : CyclicGeneric (GlobalCapEntry.lineCapCore q a b)) :
    EndpointCurrent.endpointMarked d (polygonSignArray q) a.val b.val =
      polygonAmplitude (GlobalCapEntry.lineCapCore q a b) hcap := by
  let Q := GlobalCapEntry.lineCapCore q a b
  let m := b.val - a.val + 1
  let rlast : Fin (m + 1) := ⟨m, by dsimp [m]; omega⟩
  let W : ℕ → PlanarPoint ℝ := rootedPolygonWord Q rlast
  have hQ : CyclicGeneric Q := by simpa [Q] using hcap
  have hsize : 3 ≤ m + 1 := by dsimp [m]; omega
  have hW : ∀ x, x ≤ m → W x = EndpointCurrent.endpointWord q a.val (a.val + x) := by
    intro x hx
    have hxFin : x < m + 1 := by omega
    have hroot : rlast.val + 1 + x = m + 1 + x := by simp [rlast]
    have hindex : cyclicVertexIndex rlast x = ⟨x, hxFin⟩ := by
      apply Fin.ext
      simp only [cyclicVertexIndex]
      have hsum : m + 1 + x = x + (m + 1) := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hxFin]
    rw [show W x = Q (cyclicVertexIndex rlast x) by rfl, hindex]
    have hx' : x ≤ b.val - a.val + 1 := by simpa [m] using hx
    have hpoint := endpointPoint_subword q a b hab x hx'
    simpa [Q] using hpoint
  have hsign : ∀ x y z, 0 ≤ x → x < y → y < z → z ≤ m →
      polygonSignArray W x y z =
        CurrentTranslation.translateTriple a.val
          (polygonSignArray (fun x => EndpointCurrent.endpointWord q a.val x)) x y z := by
    intro x y z hx hxy hyz hz
    have hxW := hW x (by omega)
    have hyW := hW y (by omega)
    have hzW := hW z (by omega)
    simp [CurrentTranslation.translateTriple, polygonSignArray, polygonHDet,
      hxW, hyW, hzW]
  have hrootamp : polygonAmplitude Q hQ =
      markedAmplitude (fun _ k _ => d (a.val + k)) (polygonSignArray W) 0 m := by
    calc
      polygonAmplitude Q hQ = rootedSpinorAmplitude Q rlast :=
        polygonAmplitude_eq_rootedSpinorAmplitude hRI Q hQ rlast
      _ = markedTreeSum (polygonSignArray W) (polygonSignArray W) 0 m := by
        simpa [W, m] using rootedSpinorAmplitude_eq_markedTreeSum hsize Q hQ.g1 rlast
      _ = markedAmplitude (polygonSignArray W) (polygonSignArray W) 0 m :=
        markedTreeSum_eq_markedAmplitude _ _ (by dsimp [m]; omega)
      _ = markedAmplitude (fun _ k _ => d (a.val + k)) (polygonSignArray W) 0 m :=
        (markedAmplitude_near_independent _ _ _ (by dsimp [m]; omega)).symm
  have hlocal : markedAmplitude (fun _ k _ => d (a.val + k))
      (polygonSignArray W) 0 m =
      markedAmplitude
        (CurrentTranslation.translateTriple a.val (fun _ k _ => d k))
        (CurrentTranslation.translateTriple a.val
          (polygonSignArray (fun x => EndpointCurrent.endpointWord q a.val x))) 0 m := by
    apply markedAmplitude_congr_interval _ _ _ _ (by dsimp [m]; omega)
    intro x y z h0 hxy hyz hz
    exact hsign x y z h0 hxy hyz (by simpa [m] using hz)
  have hmarkedTranslate := markedAmplitude_translate
    (fun _ k _ => d k)
    (polygonSignArray (fun x => EndpointCurrent.endpointWord q a.val x))
    a.val 0 m (by dsimp [m]; omega)
  have hfar : ∀ x y z, a.val ≤ x → x < y → y < z → z ≤ b.val + 1 →
      polygonSignArray (fun x => EndpointCurrent.endpointWord q a.val x) x y z =
        EndpointCurrent.endpointFar a.val (polygonSignArray q) x y z := by
    intro x y z hax hxy hyz hz
    exact EndpointCurrent.endpointFar_polygonSignArray_congr q hax hxy hyz
  have htoFar := markedAmplitude_congr_interval
    (fun _ k _ => d k) (fun _ k _ => d k)
    (polygonSignArray (fun x => EndpointCurrent.endpointWord q a.val x))
    (EndpointCurrent.endpointFar a.val (polygonSignArray q))
    (by omega) hfar
  rw [EndpointCurrent.endpointMarked, if_pos (by omega : a.val ≤ b.val)]
  calc
    markedAmplitude (fun _ k _ => d k)
        (EndpointCurrent.endpointFar a.val (polygonSignArray q)) a.val (b.val + 1) =
      polygonAmplitude Q hQ := by
        calc
          _ = markedAmplitude (fun _ k _ => d k)
              (polygonSignArray (fun x => EndpointCurrent.endpointWord q a.val x))
              a.val (b.val + 1) := htoFar.symm
          _ = markedAmplitude
              (CurrentTranslation.translateTriple a.val (fun _ k _ => d k))
              (CurrentTranslation.translateTriple a.val
                (polygonSignArray (fun x => EndpointCurrent.endpointWord q a.val x))) 0 m := by
                  have hmval : a.val + m = b.val + 1 := by dsimp [m]; omega
                  simpa [Nat.zero_add, hmval] using hmarkedTranslate.symm
          _ = markedAmplitude (fun _ k _ => d (a.val + k))
              (polygonSignArray W) 0 m := hlocal.symm
          _ = polygonAmplitude Q hQ := hrootamp.symm


theorem lineCapPairing_endpointMarked (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (hothers : ∀ k, 0 < k → k ≤ n → (q k).2 ≠ 0)
    (a b : Fin n)
    (hcap : a.val < b.val →
      CyclicGeneric (GlobalCapEntry.lineCapCore q a b)) :
    GlobalCapAlgebra.lineCapPairing q n a b =
      ((GlobalCapAlgebra.lineCapHeights q n a +
        GlobalCapAlgebra.lineCapHeights q n b) / 2) *
      EndpointCurrent.endpointMarked
        (fun k => scalarSignValue (q k).2) (polygonSignArray q) a.val b.val := by
  by_cases hab : a.val < b.val
  · rw [GlobalCapEntry.lineCapPairing_entry hRI q n hzero hothers a b hab (hcap hab)]
    rw [endpointMarked_lineCapCore hRI (fun k => scalarSignValue (q k).2)
      q a b hab (hcap hab)]
  · by_cases heq : a = b
    · subst b
      rw [GlobalCapAlgebra.lineCapPairing_diagonal,
        EndpointCurrent.endpointMarked_diagonal]
      ring
    · have hne : a.val ≠ b.val := fun h => heq (Fin.ext h)
      have hba : b.val < a.val := by omega
      rw [GlobalCapAlgebra.lineCapPairing_below q n a b hba]
      have hnot : ¬ a.val ≤ b.val := by omega
      simp [EndpointCurrent.endpointMarked, hnot]













end DirectGLSSW.EndpointMarkedCap
