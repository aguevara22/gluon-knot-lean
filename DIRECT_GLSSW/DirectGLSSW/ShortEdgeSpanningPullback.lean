import DirectGLSSW.ShortEdgeWeighted

namespace DirectGLSSW.ShortEdgeWeighted.SpanningPullbackImpl

def liftAt (a x : ℕ) : ℕ := if x < a then x else x + 1

theorem collapse_liftAfter_all (a x : ℕ) :
    ShortEdgeCutFibers.collapseAfter a (ShortEdgeCutFibers.liftAfter a x) = x := by
  by_cases h : x ≤ a
  · simp [ShortEdgeCutFibers.liftAfter, ShortEdgeCutFibers.collapseAfter, h]
  · have hgt : a < x := by omega
    simp [ShortEdgeCutFibers.liftAfter, ShortEdgeCutFibers.collapseAfter,
      Nat.not_le.mpr hgt]
    omega

theorem liftAfter_avoids_insertedB (a x : ℕ) :
    ShortEdgeCutFibers.liftAfter a x ≠ a + 1 := by
  by_cases h : x ≤ a
  · simp [ShortEdgeCutFibers.liftAfter, h]
    omega
  · have hgt : a < x := by omega
    simp [ShortEdgeCutFibers.liftAfter, Nat.not_le.mpr hgt]
    omega

theorem collapse_liftAt_all (a x : ℕ) :
    ShortEdgeCutFibers.collapseAfter a (liftAt a x) = x := by
  by_cases h : x < a
  · simp [liftAt, ShortEdgeCutFibers.collapseAfter, h, Nat.le_of_lt h]
  · have hax : a ≤ x := by omega
    simp [liftAt, ShortEdgeCutFibers.collapseAfter, h, hax]
    omega

theorem liftAt_avoids_insertedA (a x : ℕ) :
    liftAt a x ≠ a := by
  by_cases h : x < a
  · simp [liftAt, h]
    omega
  · have hax : a ≤ x := by omega
    simp [liftAt, h, hax]
    omega

theorem D1_liftAfter_eq_D0 (a : ℕ) (t : ℕ → Sign) (D : TripleArray)
    (i k j : ℕ) :
    D1 a t D (ShortEdgeCutFibers.liftAfter a i)
      (ShortEdgeCutFibers.liftAfter a k) (ShortEdgeCutFibers.liftAfter a j) =
      D0 a t D i k j := by
  have hkB := liftAfter_avoids_insertedB a k
  have hjB := liftAfter_avoids_insertedB a j
  simp [D1, collapse_liftAfter_all, hkB, hjB]

theorem H1_liftAfter_eq_H0 (a : ℕ) (t : ℕ → Sign)
    (H : ℕ → ℕ → ℕ → Sign) (i k j : ℕ) :
    H1 a t H (ShortEdgeCutFibers.liftAfter a i)
      (ShortEdgeCutFibers.liftAfter a k) (ShortEdgeCutFibers.liftAfter a j) =
      H0 H i k j := by
  have hkB := liftAfter_avoids_insertedB a k
  have hjB := liftAfter_avoids_insertedB a j
  simp [H1, collapse_liftAfter_all, hkB, hjB]

theorem D1_liftAt_eq_D0 (a : ℕ) (t : ℕ → Sign) (D : TripleArray)
    (i k j : ℕ) :
    D1 a t D (liftAt a i) (liftAt a k) (liftAt a j) = D0 a t D i k j := by
  have hiA := liftAt_avoids_insertedA a i
  have hkA := liftAt_avoids_insertedA a k
  simp [D1, collapse_liftAt_all, hiA, hkA]

theorem H1_liftAt_eq_H0 (a : ℕ) (t : ℕ → Sign)
    (H : ℕ → ℕ → ℕ → Sign) (i k j : ℕ) :
    H1 a t H (liftAt a i) (liftAt a k) (liftAt a j) = H0 H i k j := by
  have hiA := liftAt_avoids_insertedA a i
  have hkA := liftAt_avoids_insertedA a k
  simp [H1, collapse_liftAt_all, hiA, hkA]

theorem gateProduct_liftAfter_pullback (a : ℕ) (t : ℕ → Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) (η : Sign)
    (i j : ℕ) (v : List ℕ) :
    gateProduct (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
      (ShortEdgeCutFibers.liftAfter a i) (ShortEdgeCutFibers.liftAfter a j)
      (v.map (ShortEdgeCutFibers.liftAfter a)) =
    gateProduct (D0 a t D) (fun x k y => -η.value * H0 H x k y) i j v := by
  let f := ShortEdgeCutFibers.liftAfter a
  let G1 := fun x k y => -η.value * H1 a t H x k y
  let G0 := fun x k y => -η.value * H0 H x k y
  have hD : (fun x k y => D1 a t D (f x) (f k) (f y)) = D0 a t D := by
    funext x k y
    exact D1_liftAfter_eq_D0 a t D x k y
  have hG : (fun x k y => G1 (f x) (f k) (f y)) = G0 := by
    funext x k y
    change -η.value * H1 a t H (f x) (f k) (f y) =
      -η.value * H0 H x k y
    rw [H1_liftAfter_eq_H0]
  calc
    gateProduct (D1 a t D) G1 (f i) (f j) (v.map f) =
        gateProduct (fun x k y => D1 a t D (f x) (f k) (f y))
          (fun x k y => G1 (f x) (f k) (f y)) i j v :=
      DirectGLSSW.ShortEdgeWeighted.gateProduct_map
        (D1 a t D) G1 f i j v
    _ = gateProduct (D0 a t D) G0 i j v := by rw [hD, hG]

theorem gateProduct_liftAt_pullback (a : ℕ) (t : ℕ → Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) (η : Sign)
    (i j : ℕ) (v : List ℕ) :
    gateProduct (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
      (liftAt a i) (liftAt a j) (v.map (liftAt a)) =
    gateProduct (D0 a t D) (fun x k y => -η.value * H0 H x k y) i j v := by
  let f := liftAt a
  let G1 := fun x k y => -η.value * H1 a t H x k y
  let G0 := fun x k y => -η.value * H0 H x k y
  have hD : (fun x k y => D1 a t D (f x) (f k) (f y)) = D0 a t D := by
    funext x k y
    exact D1_liftAt_eq_D0 a t D x k y
  have hG : (fun x k y => G1 (f x) (f k) (f y)) = G0 := by
    funext x k y
    change -η.value * H1 a t H (f x) (f k) (f y) =
      -η.value * H0 H x k y
    rw [H1_liftAt_eq_H0]
  calc
    gateProduct (D1 a t D) G1 (f i) (f j) (v.map f) =
        gateProduct (fun x k y => D1 a t D (f x) (f k) (f y))
          (fun x k y => G1 (f x) (f k) (f y)) i j v :=
      DirectGLSSW.ShortEdgeWeighted.gateProduct_map
        (D1 a t D) G1 f i j v
    _ = gateProduct (D0 a t D) G0 i j v := by rw [hD, hG]

end DirectGLSSW.ShortEdgeWeighted.SpanningPullbackImpl
