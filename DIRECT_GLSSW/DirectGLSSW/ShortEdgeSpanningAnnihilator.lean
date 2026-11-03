import DirectGLSSW.ShortEdgeWeighted

namespace DirectGLSSW.ShortEdgeWeighted.SpanningAnnihilatorImpl

theorem coreContribution_annihilate
    (a i j L R : ℕ) (S : Finset ℕ)
    (t : ℕ → Sign) (η : Sign) (D : TripleArray)
    (H : ℕ → ℕ → ℕ → Sign) (U : IntervalArray)
    (htriple : (L, a, R) ∈
      (cutVertices i j S).zip
        ((cutVertices i j S).tail.zip (cutVertices i j S).tail.tail)) :
    ((t L).value - η.value * (H i a j).value) *
      cutContribution (D0 a t D) (fun x k y => -η.value * H0 H x k y)
        U i j S = 0
 := by
  let f : ℚ := ((t L).value + η.value * (H i a j).value) / 2
  let q : ℚ := (t L).value - η.value * (H i a j).value
  let v := cutVertices i j S
  let gates := (v.zip (v.tail.zip v.tail.tail)).map
    (fun (x, k, y) => (D0 a t D x k y - (-η.value * H0 H i k j)) / 2)
  have hmem : f ∈ gates := by
    apply List.mem_map.mpr
    refine ⟨(L, a, R), htriple, ?_⟩
    simp [D0, H0, f]
  obtain ⟨pre, post, hgates⟩ := List.mem_iff_append.mp hmem
  have hlocal : q * f = 0 := by
    dsimp [q, f]
    cases ht : t L <;> cases η <;> cases hh : H i a j <;>
      norm_num [Sign.value]
  change q * (gates.prod * branchProduct U v) = 0
  rw [hgates, List.prod_append, List.prod_cons]
  calc
    q * (pre.prod * (f * post.prod) * branchProduct U v) =
        (q * f) * (pre.prod * post.prod * branchProduct U v) := by ring
    _ = 0 := by rw [hlocal]; simp

end DirectGLSSW.ShortEdgeWeighted.SpanningAnnihilatorImpl
