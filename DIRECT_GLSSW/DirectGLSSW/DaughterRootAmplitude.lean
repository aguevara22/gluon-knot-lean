import DirectGLSSW.ShortEdgeCyclicRelabel
import DirectGLSSW.DaughterRootRotation

set_option autoImplicit false

namespace DirectGLSSW.DaughterRootAmplitude

open DirectGLSSW
open DirectGLSSW.DaughterFirstReturn
open DirectGLSSW.DaughterRootRotation

private theorem cyclicShift_val {n k : ℕ} (hk : k < n)
    (i : Fin n) :
    ((cyclicSuccessorPerm n ^ k) i).val = (i.val + k) % n := by
  cases k with
  | zero =>
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ t =>
      have ht : t < n := by omega
      rw [cyclicSuccessorPerm_pow_succ]
      change (i.val + 1 + t) % n = (i.val + (t + 1)) % n
      congr 1
      omega

private theorem cyclicShift_commutes {n k : ℕ} :
    ∀ e : Fin n,
      (cyclicSuccessorPerm n ^ k) (cyclicSuccessor e) =
        cyclicSuccessor ((cyclicSuccessorPerm n ^ k) e) := by
  intro e
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      simp only [Equiv.Perm.mul_apply]
      exact congrArg cyclicSuccessor (ih e)

theorem cyclicGeneric_ofFn_isRotated
    {m n : ℕ} {q : Fin n → PlanarPoint ℝ} {r : Fin m → PlanarPoint ℝ}
    (hrot : List.ofFn q ~r List.ofFn r) (hq : CyclicGeneric q) :
    CyclicGeneric r := by
  classical
  obtain ⟨k, hk⟩ := hrot
  have hlen : n = m := by
    have h := congrArg List.length hk
    simpa using h
  subst m
  let k' := k % n
  have hnpos : 0 < n := by have := hq.size_ge_three; omega
  have hk' : (List.ofFn q).rotate k' = List.ofFn r := by
    have hmod := (List.rotate_mod (List.ofFn q) k).trans hk
    simpa [k', List.length_ofFn] using hmod
  let σ : Equiv.Perm (Fin n) := cyclicSuccessorPerm n ^ k'
  have hσval (i : Fin n) :
      (σ i).val = (i.val + k') % n := by
    exact cyclicShift_val (Nat.mod_lt _ hnpos) i
  have hrel : r = q ∘ σ := by
    funext i
    let l₁ : {l : List (PlanarPoint ℝ) // l.length = n} :=
      ⟨(List.ofFn q).rotate k', by simp⟩
    let l₂ : {l : List (PlanarPoint ℝ) // l.length = n} :=
      ⟨List.ofFn r, by simp⟩
    have hsub : l₁ = l₂ := Subtype.ext hk'
    have hget := congrArg
      (fun l : {l : List (PlanarPoint ℝ) // l.length = n} =>
        l.val[i.val]'(by rw [l.property]; exact i.isLt)) hsub
    have hrotget := List.getElem_rotate (List.ofFn q) k' i.val (by
      rw [List.length_rotate, List.length_ofFn]
      exact i.isLt)
    change ((List.ofFn q).rotate k')[i.val]'_ = (List.ofFn r)[i.val]'_ at hget
    rw [hrotget] at hget
    have hpoint :
        (⟨(i.val + k') % n, Nat.mod_lt _ hnpos⟩ : Fin n) = σ i := by
      apply Fin.ext
      exact (hσval i).symm
    simpa [List.getElem_ofFn, hpoint] using hget.symm
  exact hrel ▸ cyclicGeneric_relabel q σ
    (cyclicShift_commutes) hq

theorem polygonAmplitude_ofFn_isRotated (hRI : GLSSWRootIndependence)
    {m n : ℕ} {q : Fin n → PlanarPoint ℝ} {r : Fin m → PlanarPoint ℝ}
    (hq : CyclicGeneric q) (hrot : List.ofFn q ~r List.ofFn r) :
    polygonAmplitude q hq =
      polygonAmplitude r (cyclicGeneric_ofFn_isRotated hrot hq) := by
  classical
  obtain ⟨k, hk⟩ := hrot
  have hlen : n = m := by
    have h := congrArg List.length hk
    simpa using h
  subst m
  have hrotWitness : List.ofFn q ~r List.ofFn r := ⟨k, hk⟩
  have hnpos : 0 < n := by have := hq.size_ge_three; omega
  have hrotate : (List.ofFn q).rotate (k % n) = List.ofFn r := by
    have hmod := (List.rotate_mod (List.ofFn q) k).trans hk
    simpa [List.length_ofFn] using hmod
  let k' := k % n
  let σ : Equiv.Perm (Fin n) := cyclicSuccessorPerm n ^ k'
  have hσ : ∀ e, σ (cyclicSuccessor e) = cyclicSuccessor (σ e) := by
    simpa [σ] using cyclicShift_commutes
  have hrel : r = q ∘ σ := by
    let l₁ : {l : List (PlanarPoint ℝ) // l.length = n} :=
      ⟨(List.ofFn q).rotate k', by simp⟩
    let l₂ : {l : List (PlanarPoint ℝ) // l.length = n} :=
      ⟨List.ofFn r, by simp⟩
    have hsub : l₁ = l₂ := Subtype.ext hrotate
    funext i
    have hσval (j : Fin n) :
        (σ j).val = (j.val + k') % n := by
      exact cyclicShift_val (Nat.mod_lt _ hnpos) j
    have hget := congrArg
      (fun l : {l : List (PlanarPoint ℝ) // l.length = n} =>
        l.val[i.val]'(by rw [l.property]; exact i.isLt)) hsub
    have hrotget := List.getElem_rotate (List.ofFn q) k' i.val (by
      rw [List.length_rotate, List.length_ofFn]
      exact i.isLt)
    change ((List.ofFn q).rotate k')[i.val]'_ = (List.ofFn r)[i.val]'_ at hget
    rw [hrotget] at hget
    have hpoint :
        (⟨(i.val + k') % n, Nat.mod_lt _ hnpos⟩ : Fin n) = σ i := by
      apply Fin.ext
      exact (hσval i).symm
    simpa [List.getElem_ofFn, hpoint] using hget.symm
  let p₁ : {t : Fin n → PlanarPoint ℝ // CyclicGeneric t} :=
    ⟨r, cyclicGeneric_ofFn_isRotated hrotWitness hq⟩
  let p₂ : {t : Fin n → PlanarPoint ℝ // CyclicGeneric t} :=
    ⟨q ∘ σ, cyclicGeneric_relabel q σ hσ hq⟩
  have hp : p₁ = p₂ := by
    exact Subtype.ext hrel
  have hamp := congrArg
    (fun z : {t : Fin n → PlanarPoint ℝ // CyclicGeneric t} => polygonAmplitude z.1 z.2) hp
  dsimp [p₁, p₂] at hamp
  calc
    polygonAmplitude q hq = polygonAmplitude (q ∘ σ)
        (cyclicGeneric_relabel q σ hσ hq) :=
          (polygonAmplitude_relabel hRI hq σ hσ).symm
    _ = polygonAmplitude r (cyclicGeneric_ofFn_isRotated hrotWitness hq) := hamp.symm

theorem daughterCyclicGeneric_of_sameCycle
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x y : PolygonEvent q)
    (hxy : (smoothingDartPermutation q hG2 S).SameCycle x y)
    (hx : CyclicGeneric (daughterVertex q hG2 S x)) :
    CyclicGeneric (daughterVertex q hG2 S y) := by
  apply cyclicGeneric_ofFn_isRotated
    (daughterPointList_isRotated_of_sameCycle q hG2 S x y hxy)
  exact hx

theorem daughterPolygonAmplitude_eq_of_sameCycle
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x y : PolygonEvent q)
    (hxy : (smoothingDartPermutation q hG2 S).SameCycle x y)
    (hx : CyclicGeneric (daughterVertex q hG2 S x)) :
    polygonAmplitude (daughterVertex q hG2 S x) hx =
      polygonAmplitude (daughterVertex q hG2 S y)
        (daughterCyclicGeneric_of_sameCycle q hG2 S x y hxy hx) := by
  apply polygonAmplitude_ofFn_isRotated hRI hx
  exact daughterPointList_isRotated_of_sameCycle q hG2 S x y hxy








end DirectGLSSW.DaughterRootAmplitude
