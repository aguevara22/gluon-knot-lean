import DirectGLSSW.ShortEdgeWeighted

namespace DirectGLSSW.ShortEdgeWeighted.WordMembershipImpl

theorem triple_mem_splice (pre post : List ℕ) (L a R : ℕ) :
    (L,a,R) ∈ (pre ++ [L,a,R] ++ post).zip
      ((pre ++ [L,a,R] ++ post).tail.zip (pre ++ [L,a,R] ++ post).tail.tail)
 := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
      cases pre with
      | nil => simp
      | cons y ys =>
          cases ys with
          | nil => simp
          | cons z zs =>
              simp only [List.cons_append, List.tail_cons, List.zip_cons_cons,
                List.mem_cons] at ih ⊢
              exact Or.inr ih

end DirectGLSSW.ShortEdgeWeighted.WordMembershipImpl
