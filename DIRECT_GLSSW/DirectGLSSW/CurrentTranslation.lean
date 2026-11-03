import DirectGLSSW.ShortEdgeWeighted
import DirectGLSSW.CurrentFidelity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.CurrentTranslation
open DirectGLSSW
open scoped BigOperators

def translateTriple (s : ℕ) (A : TripleArray) : TripleArray :=
  fun x k y => A (s + x) (s + k) (s + y)

def translateInterval (s : ℕ) (b : IntervalArray) : IntervalArray :=
  fun x y => b (s + x) (s + y)

private theorem translateTriple_one_apply (A : TripleArray) :
    translateTriple 1 A = fun x k y => A (x + 1) (k + 1) (y + 1) := by
  funext x k y
  simp only [translateTriple]
  congr 1 <;> omega

private theorem translateInterval_one_apply (b : IntervalArray) :
    translateInterval 1 b = fun x y => b (x + 1) (y + 1) := by
  funext x y
  simp only [translateInterval]
  congr 1 <;> omega

private theorem cutContribution_succ_translate (D H : TripleArray) (b : IntervalArray)
    (i j : ℕ) (S : Finset ℕ) :
    cutContribution D H b (i + 1) (j + 1) (S.image Nat.succ) =
      cutContribution (translateTriple 1 D) (translateTriple 1 H)
        (translateInterval 1 b) i j S := by
  unfold cutContribution
  rw [ShortEdgeWeighted.cutVertices_succ_image]
  have hg := ShortEdgeWeighted.gateProduct_map D H Nat.succ i j (cutVertices i j S)
  have hb := ShortEdgeWeighted.branchProduct_map b Nat.succ (cutVertices i j S)
  rw [hg, hb, ← translateTriple_one_apply, ← translateTriple_one_apply,
    ← translateInterval_one_apply]

private theorem phi_succ_translate (D H : TripleArray) (b : IntervalArray)
    (i j : ℕ) :
    phi (translateTriple 1 D) (translateTriple 1 H) (translateInterval 1 b) i j =
      phi D H b (i + 1) (j + 1) := by
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
      cutContribution (translateTriple 1 D) (translateTriple 1 H)
        (translateInterval 1 b) i j S) =
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
    have hS : (T.image Nat.pred) ⊆ P := Finset.mem_powerset.mp (hpred T hT)
    calc
      cutContribution D H b (i + 1) (j + 1) T =
          cutContribution D H b (i + 1) (j + 1)
            ((T.image Nat.pred).image Nat.succ) := by
              congr 1
              exact (hright T hT).symm
      _ = cutContribution (translateTriple 1 D) (translateTriple 1 H)
            (translateInterval 1 b) i j (T.image Nat.pred) :=
              cutContribution_succ_translate D H b i j (T.image Nat.pred)

theorem ordinaryCurrent_translate_succ (D H : TripleArray) (i j : ℕ)
    (hij : i < j) :
    ordinaryCurrent (translateTriple 1 D) (translateTriple 1 H) i j =
      ordinaryCurrent D H (i + 1) (j + 1) := by
  let X : IntervalArray := translateInterval 1 (ordinaryCurrent D H)
  have hX : ∀ x y, x < y →
      phi (translateTriple 1 D) (translateTriple 1 H) X x y = source x y := by
    intro x y hxy
    change phi (translateTriple 1 D) (translateTriple 1 H)
      (translateInterval 1 (ordinaryCurrent D H)) x y = source x y
    rw [phi_succ_translate]
    have hsource : source (x + 1) (y + 1) = source x y := by
      by_cases he : y = x + 1
      · subst y
        simp [source, Nat.add_assoc]
      · have hshift : y + 1 ≠ (x + 1) + 1 := by omega
        simp [source, he, hshift]
    rw [← hsource]
    exact ordinaryCurrent_phi D H (by omega)
  have hu := ordinaryCurrent_unique (translateTriple 1 D) (translateTriple 1 H) X hX hij
  simpa [X, translateInterval, Nat.add_comm] using hu.symm

private theorem translateTriple_succ (s : ℕ) (A : TripleArray) :
    translateTriple (s + 1) A = translateTriple 1 (translateTriple s A) := by
  funext x k y
  simp only [translateTriple]
  congr 1 <;> omega

theorem ordinaryCurrent_translate (D H : TripleArray) (s i j : ℕ)
    (hij : i < j) :
    ordinaryCurrent (translateTriple s D) (translateTriple s H) i j =
      ordinaryCurrent D H (s + i) (s + j) := by
  induction s generalizing i j with
  | zero =>
      have hD : translateTriple 0 D = D := by
        funext x k y
        simp [translateTriple]
      have hH : translateTriple 0 H = H := by
        funext x k y
        simp [translateTriple]
      rw [hD, hH]
      simp
  | succ s ih =>
      rw [translateTriple_succ s D, translateTriple_succ s H]
      calc
        ordinaryCurrent (translateTriple 1 (translateTriple s D))
            (translateTriple 1 (translateTriple s H)) i j =
            ordinaryCurrent (translateTriple s D) (translateTriple s H) (i + 1) (j + 1) :=
              ordinaryCurrent_translate_succ _ _ i j hij
        _ = ordinaryCurrent D H (s + (i + 1)) (s + (j + 1)) := ih (i + 1) (j + 1) (by omega)
        _ = ordinaryCurrent D H ((s + 1) + i) ((s + 1) + j) := by
          have hi : s + (i + 1) = (s + 1) + i := by omega
          have hj : s + (j + 1) = (s + 1) + j := by omega
          rw [hi, hj]









end DirectGLSSW.CurrentTranslation
