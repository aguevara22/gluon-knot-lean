import DirectGLSSW.ShortEdgeWeighted

/-!
# Isolated left-endpoint short-edge contribution identity

This module lives in an isolated implementation lane. It proves only the
finite-array left-endpoint two-lift contribution identity from
`ep:endpoint-two-lifts`; it makes no geometric realization claim.
-/

namespace DirectGLSSW.ShortEdgeWeighted.LeftEndpointImpl
open scoped BigOperators

private theorem sort_image_succ (S : Finset ℕ) :
    (S.image Nat.succ).sort (· ≤ ·) = (S.sort (· ≤ ·)).map Nat.succ := by
  have hmap := Multiset.map_sort (r := (· ≤ ·)) (r' := (· ≤ ·)) Nat.succ S.1 (by
    intro x hx y hy
    omega)
  have hinj : Set.InjOn Nat.succ (S : Set ℕ) := by
    intro x hx y hy hxy
    exact Nat.succ.inj hxy
  rw [← Finset.sort_val, ← Finset.sort_val, Finset.image_val_of_injOn hinj]
  exact hmap.symm

private theorem liftedCuts_eq_image_succ
    (a c : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo a c) :
    DirectGLSSW.ShortEdgeCutFibers.liftedCuts a S = S.image Nat.succ := by
  ext x
  simp only [DirectGLSSW.ShortEdgeCutFibers.liftedCuts,
    Finset.mem_image, DirectGLSSW.ShortEdgeCutFibers.liftAfter]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hya := (Finset.mem_Ioo.mp (hS hy)).1
    simp [Nat.not_le_of_gt hya] at hxy
    exact ⟨y, hy, hxy⟩
  · rintro ⟨y, hy, rfl⟩
    have hya := (Finset.mem_Ioo.mp (hS hy)).1
    refine ⟨y, hy, ?_⟩
    simp [Nat.not_le_of_gt hya]

private theorem sort_image_succ_insert_front
    (a : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, a < x) :
    (S.image Nat.succ ∪ {a + 1}).sort (· ≤ ·) =
      (a + 1) :: (S.image Nat.succ).sort (· ≤ ·) := by
  have hleft :
      ((S.image Nat.succ ∪ {a + 1}).sort (· ≤ ·)).Pairwise (· < ·) :=
    Finset.sort_sorted_lt _
  have hright :
      ((a + 1) :: (S.image Nat.succ).sort (· ≤ ·)).Pairwise (· < ·) := by
    apply List.pairwise_cons.mpr
    constructor
    · intro x hx
      have hxS : x ∈ S.image Nat.succ := (Finset.mem_sort _).mp hx
      rcases Finset.mem_image.mp hxS with ⟨y, hy, rfl⟩
      have hya := hS y hy
      omega
    · exact Finset.sort_sorted_lt _
  apply List.Sorted.eq_of_mem_iff hleft hright
  intro x
  simp only [List.mem_cons, Finset.mem_sort, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_image]
  exact or_comm

private theorem lifted_cutVertices
    (a j c : ℕ) (S : Finset ℕ)
    (hc : c + 1 = j)
    (hS : S ⊆ Finset.Ioo a c) :
    DirectGLSSW.cutVertices a j
        (DirectGLSSW.ShortEdgeCutFibers.liftedCuts a S) =
      a :: (DirectGLSSW.cutVertices a c S).tail.map Nat.succ := by
  have hsort := sort_image_succ S
  have hlift := liftedCuts_eq_image_succ a c S hS
  rw [hlift]
  simp only [DirectGLSSW.cutVertices, List.tail_cons]
  rw [hsort]
  simp [List.map_append, hc]

private theorem lifted_cutVertices_shortLeaf
    (a j c : ℕ) (S : Finset ℕ)
    (hc : c + 1 = j)
    (hS : S ⊆ Finset.Ioo a c) :
    DirectGLSSW.cutVertices a j
        (DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate a S
          DirectGLSSW.ShortEdgeCutFibers.EndpointLiftMode.shortLeaf) =
      a :: ((a + 1) ::
        (DirectGLSSW.cutVertices a c S).tail.map Nat.succ) := by
  have hsort := sort_image_succ S
  have hsortFront := sort_image_succ_insert_front a S (by
    intro x hx
    exact (Finset.mem_Ioo.mp (hS hx)).1)
  have hlift := liftedCuts_eq_image_succ a c S hS
  rw [show DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate a S
      DirectGLSSW.ShortEdgeCutFibers.EndpointLiftMode.shortLeaf =
        DirectGLSSW.ShortEdgeCutFibers.liftedCuts a S ∪ {a + 1} by
    simp [DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate]]
  rw [hlift]
  simp only [DirectGLSSW.cutVertices]
  rw [hsortFront]
  rw [hsort]
  simp [List.map_append, hc]

private theorem collapse_succ_of_gt {a x : ℕ} (hax : a < x) :
    DirectGLSSW.ShortEdgeCutFibers.collapseAfter a (x + 1) = x := by
  rw [DirectGLSSW.ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt]
  · omega
  · omega

private theorem branchProduct_cons_cons
    (b : DirectGLSSW.IntervalArray) (x y : ℕ) (ys : List ℕ) :
    DirectGLSSW.branchProduct b (x :: y :: ys) =
      b x y * DirectGLSSW.branchProduct b (y :: ys) := by
  simp [DirectGLSSW.branchProduct]

private theorem parent_branch_succ
    (a : ℕ) (ha : 0 < a) (t : ℕ → DirectGLSSW.Sign)
    (U : DirectGLSSW.IntervalArray) (xs : List ℕ)
    (hxs : ∀ x ∈ xs, a < x) :
    DirectGLSSW.branchProduct
        (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U)
        (xs.map Nat.succ) = DirectGLSSW.branchProduct U xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hx := hxs x (by simp)
          have hy := hxs y (by simp)
          have hcx := collapse_succ_of_gt hx
          have hcy := collapse_succ_of_gt hy
          have htail : ∀ z ∈ y :: ys, a < z := by
            intro z hz
            have hz' : z = y ∨ z ∈ ys := by simpa using hz
            exact hxs z (by simp only [List.mem_cons]; exact Or.inr hz')
          have htable :
              DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U
                  (x + 1) (y + 1) = U x y := by
            have hgt : a + 1 < y + 1 := by omega
            have hxne : x + 1 ≠ a := by omega
            have hxnotlt : ¬ x + 1 < a := by omega
            simp [DirectGLSSW.ShortEdgeWeighted.parentTable, hgt, hcx, hcy,
              hxne, hxnotlt]
          calc
            DirectGLSSW.branchProduct
                (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U)
                (List.map Nat.succ (x :: y :: ys)) =
                DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U
                    (x + 1) (y + 1) *
                  DirectGLSSW.branchProduct
                    (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U)
                    (List.map Nat.succ (y :: ys)) := by
              simp only [List.map_cons]
              exact branchProduct_cons_cons _ _ _ _
            _ = U x y * DirectGLSSW.branchProduct U (y :: ys) := by
              rw [htable, ih htail]
            _ = DirectGLSSW.branchProduct U (x :: y :: ys) := by
              rw [branchProduct_cons_cons]

private theorem gateProduct_cons3
    (D G : DirectGLSSW.TripleArray) (i j x y z : ℕ) (ys : List ℕ) :
    DirectGLSSW.gateProduct D G i j (x :: y :: z :: ys) =
      ((D x y z - G i y j) / 2) *
        DirectGLSSW.gateProduct D G i j (y :: z :: ys) := by
  simp [DirectGLSSW.gateProduct]

private theorem parent_gate_succ_tail
    (a j c : ℕ) (hac : a < c) (hc : c + 1 = j)
    (t : ℕ → DirectGLSSW.Sign) (D : DirectGLSSW.TripleArray)
    (H : ℕ → ℕ → ℕ → DirectGLSSW.Sign) (η : DirectGLSSW.Sign)
    (xs : List ℕ) (hxs : ∀ x ∈ xs, a < x) :
    DirectGLSSW.gateProduct
        (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
        (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H x k y)
        a j (xs.map Nat.succ) =
      DirectGLSSW.gateProduct
        (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
        (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H x k y)
        a c xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          cases ys with
          | nil => rfl
          | cons z zs =>
              have hx := hxs x (by simp)
              have hy := hxs y (by simp)
              have hz := hxs z (by simp)
              have htail : ∀ q ∈ y :: z :: zs, a < q := by
                intro q hq
                exact hxs q (by simp [hq])
              have hcx := collapse_succ_of_gt hx
              have hcy := collapse_succ_of_gt hy
              have hcz := collapse_succ_of_gt hz
              have hJ : a < j := by omega
              have hpred : j - 1 = c := by omega
              have hyne : y ≠ a := by omega
              have hyplus : a + 1 < y + 1 := by omega
              have hjne : j ≠ a + 1 := by omega
              have hfalse : ¬ (y + 1 = a ∧ z = a) := by omega
              have hfirst :
                  (DirectGLSSW.ShortEdgeWeighted.D1 a t D (x + 1) (y + 1) (z + 1) -
                    (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                      a (y + 1) j) / 2 =
                  (DirectGLSSW.ShortEdgeWeighted.D0 a t D x y z -
                    (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                      a y c) / 2 := by
                simp [DirectGLSSW.ShortEdgeWeighted.D1,
                  DirectGLSSW.ShortEdgeWeighted.D0,
                  DirectGLSSW.ShortEdgeWeighted.H1,
                  DirectGLSSW.ShortEdgeWeighted.H0,
                  DirectGLSSW.ShortEdgeCutFibers.collapseAfter,
                  Nat.not_le_of_gt hx, Nat.not_le_of_gt hy,
                  Nat.not_le_of_gt hz, hcx, hcy, hcz, hyne, hyplus, hjne,
                  Nat.not_le_of_gt hJ, hc, hfalse]
                rw [hpred]
                <;> ring
              calc
                DirectGLSSW.gateProduct
                    (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
                    (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                    a j (List.map Nat.succ (x :: y :: z :: zs)) =
                  ((DirectGLSSW.ShortEdgeWeighted.D1 a t D (x + 1) (y + 1) (z + 1) -
                    (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                      a (y + 1) j) / 2) *
                    DirectGLSSW.gateProduct
                      (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
                      (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                      a j (List.map Nat.succ (y :: z :: zs)) := by
                    simp only [List.map_cons]
                    exact gateProduct_cons3 _ _ _ _ _ _ _ _
                _ = ((DirectGLSSW.ShortEdgeWeighted.D0 a t D x y z -
                    (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                      a y c) / 2) *
                    DirectGLSSW.gateProduct
                      (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
                      (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                      a c (y :: z :: zs) := by
                    rw [hfirst, ih htail]
                _ = DirectGLSSW.gateProduct
                      (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
                      (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                      a c (x :: y :: z :: zs) := by
                    symm
                    exact gateProduct_cons3 _ _ _ _ _ _ _ _

private theorem parent_gate_root_succ_tail
    (a j c : ℕ) (hac : a < c) (hc : c + 1 = j)
    (t : ℕ → DirectGLSSW.Sign) (D : DirectGLSSW.TripleArray)
    (H : ℕ → ℕ → ℕ → DirectGLSSW.Sign) (η : DirectGLSSW.Sign)
    (xs : List ℕ) (hxs : ∀ x ∈ xs, a < x) :
    DirectGLSSW.gateProduct
        (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
        (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H x k y)
        a j (a :: xs.map Nat.succ) =
      DirectGLSSW.gateProduct
        (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
        (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H x k y)
        a c (a :: xs) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hx := hxs x (by simp)
          have hy := hxs y (by simp)
          have htail : ∀ z ∈ x :: y :: ys, a < z := by
            intro z hz
            exact hxs z (by simp [hz])
          have hcx := collapse_succ_of_gt hx
          have hcy := collapse_succ_of_gt hy
          have hJ : a < j := by omega
          have hpred : j - 1 = c := by omega
          have hxne : x ≠ a := by omega
          have hxplus : a + 1 < x + 1 := by omega
          have hjne : j ≠ a + 1 := by omega
          have hfalse : ¬ (x + 1 = a ∧ y = a) := by omega
          have hfirst :
              (DirectGLSSW.ShortEdgeWeighted.D1 a t D a (x + 1) (y + 1) -
                (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                  a (x + 1) j) / 2 =
              (DirectGLSSW.ShortEdgeWeighted.D0 a t D a x y -
                (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                  a x c) / 2 := by
            simp [DirectGLSSW.ShortEdgeWeighted.D1,
              DirectGLSSW.ShortEdgeWeighted.D0,
              DirectGLSSW.ShortEdgeWeighted.H1,
              DirectGLSSW.ShortEdgeWeighted.H0,
              DirectGLSSW.ShortEdgeCutFibers.collapseAfter,
              Nat.not_le_of_gt hx, Nat.not_le_of_gt hy,
              hcx, hcy, hxne, hxplus, hjne, Nat.not_le_of_gt hJ, hc, hfalse]
            rw [hpred]
            <;> ring
          calc
            DirectGLSSW.gateProduct
                (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
                (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                a j (a :: (x :: y :: ys).map Nat.succ) =
              ((DirectGLSSW.ShortEdgeWeighted.D1 a t D a (x + 1) (y + 1) -
                (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                  a (x + 1) j) / 2) *
                DirectGLSSW.gateProduct
                  (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
                  (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                  a j ((x :: y :: ys).map Nat.succ) := by
                simp only [List.map_cons]
                exact gateProduct_cons3 _ _ _ _ _ _ _ _
            _ = ((DirectGLSSW.ShortEdgeWeighted.D0 a t D a x y -
                (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                  a x c) / 2) *
                DirectGLSSW.gateProduct
                  (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
                  (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                  a c (x :: y :: ys) := by
                rw [hfirst, parent_gate_succ_tail a j c hac hc t D H η
                  (x :: y :: ys) htail]
            _ = DirectGLSSW.gateProduct
                  (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
                  (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                  a c (a :: x :: y :: ys) := by
                symm
                exact gateProduct_cons3 _ _ _ _ _ _ _ _

private theorem parent_gate_map_root_succ_tail
    (a j c : ℕ) (hac : a < c) (hc : c + 1 = j)
    (t : ℕ → DirectGLSSW.Sign) (D : DirectGLSSW.TripleArray)
    (H : ℕ → ℕ → ℕ → DirectGLSSW.Sign) (η : DirectGLSSW.Sign)
    (xs : List ℕ) (hxs : ∀ x ∈ xs, a < x) :
    DirectGLSSW.gateProduct
        (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
        (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H x k y)
        a j ((a :: xs).map Nat.succ) =
      DirectGLSSW.gateProduct
        (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
        (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H x k y)
        a c (a :: xs) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hx := hxs x (by simp)
          have hy := hxs y (by simp)
          have htail : ∀ z ∈ x :: y :: ys, a < z := by
            intro z hz
            exact hxs z (by simp [hz])
          have hcx := collapse_succ_of_gt hx
          have hcy := collapse_succ_of_gt hy
          have hJ : a < j := by omega
          have hpred : j - 1 = c := by omega
          have hxne : x ≠ a := by omega
          have hxplus : a + 1 < x + 1 := by omega
          have hjne : j ≠ a + 1 := by omega
          have hfalse : ¬ (x + 1 = a ∧ y = a) := by omega
          have hfirst :
              (DirectGLSSW.ShortEdgeWeighted.D1 a t D (a + 1) (x + 1) (y + 1) -
                (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
                  a (x + 1) j) / 2 =
              (DirectGLSSW.ShortEdgeWeighted.D0 a t D a x y -
                (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
                  a x c) / 2 := by
            simp [DirectGLSSW.ShortEdgeWeighted.D0,
              DirectGLSSW.ShortEdgeWeighted.D1,
              DirectGLSSW.ShortEdgeWeighted.H1,
              DirectGLSSW.ShortEdgeWeighted.H0,
              DirectGLSSW.ShortEdgeCutFibers.collapseAfter,
              Nat.not_le_of_gt hx, Nat.not_le_of_gt hy,
              hcx, hcy, hxne, hxplus, hjne, Nat.not_le_of_gt hJ, hc, hfalse]
            rw [hpred]
            <;> ring
          rw [show ((a :: x :: y :: ys).map Nat.succ) =
              (a + 1) :: (x + 1) :: (y + 1) :: ys.map Nat.succ by
            simp only [List.map_cons]]
          simp only [DirectGLSSW.gateProduct, List.tail_cons,
            List.zip_cons_cons, List.map_cons, List.prod_cons]
          rw [hfirst]
          exact congrArg _ (parent_gate_succ_tail a j c hac hc t D H η
            (x :: y :: ys) htail)

private theorem endpoint_two_lift_words
    (a j c : ℕ) (ha : 0 < a) (hac : a < c) (hc : c + 1 = j)
    (t : ℕ → DirectGLSSW.Sign) (U : DirectGLSSW.IntervalArray)
    (η : DirectGLSSW.Sign) (D : DirectGLSSW.TripleArray)
    (H : ℕ → ℕ → ℕ → DirectGLSSW.Sign)
    (x : ℕ) (ys : List ℕ)
    (hx : a < x) (hys : ∀ y ∈ ys, a < y) :
    DirectGLSSW.gateProduct
        (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
        (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
        a j (a :: (x :: ys).map Nat.succ) *
      DirectGLSSW.branchProduct
        (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U)
        (a :: (x :: ys).map Nat.succ) +
    DirectGLSSW.gateProduct
        (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
        (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q)
        a j (a :: ((a + 1) :: (x :: ys).map Nat.succ)) *
      DirectGLSSW.branchProduct
        (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U)
        (a :: ((a + 1) :: (x :: ys).map Nat.succ)) =
      ((DirectGLSSW.ShortEdgeWeighted.beta a t +
          η.value * (t c).value) / 2) *
        (DirectGLSSW.gateProduct
            (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
            (fun p k q => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q)
            a c (a :: x :: ys) *
          DirectGLSSW.branchProduct U (a :: x :: ys)) := by
  let G1 := fun p k q =>
    -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H p k q
  let G0 := fun p k q =>
    -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H p k q
  have htail : ∀ y ∈ x :: ys, a < y := by
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hys y hy
  have hbranchTail := parent_branch_succ a ha t U (x :: ys) htail
  have hbranchTail' :
      DirectGLSSW.branchProduct
          (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U)
          ((x + 1) :: ys.map Nat.succ) = DirectGLSSW.branchProduct U (x :: ys) := by
    simpa only [List.map_cons] using hbranchTail
  have hbranchYs := parent_branch_succ a ha t U ys hys
  have hgateCore := parent_gate_root_succ_tail a j c hac hc t D H η (x :: ys) htail
  have hgateMap := parent_gate_map_root_succ_tail a j c hac hc t D H η (x :: ys) htail
  have hcollapseX := collapse_succ_of_gt hx
  have hpred : j - 1 = c := by omega
  have hxne : x ≠ a := by omega
  have hbranchHead :
      DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U a (x + 1) =
        ((DirectGLSSW.ShortEdgeWeighted.beta a t - (t x).value) / 2) * U a x := by
    have hgt : a + 1 < x + 1 := by omega
    simp [DirectGLSSW.ShortEdgeWeighted.parentTable, hgt, hcollapseX, hxne]
  have hbranchLeafHead :
      DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U a (a + 1) = 1 := by
    simp [DirectGLSSW.ShortEdgeWeighted.parentTable]
  have hbranchLeafNext :
      DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U (a + 1) (x + 1) =
        U a x := by
    have hcollapseB := DirectGLSSW.ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (a + 1)
      (by omega)
    simp [DirectGLSSW.ShortEdgeWeighted.parentTable,
      DirectGLSSW.ShortEdgeCutFibers.collapseAfter, hcollapseB, hcollapseX,
      Nat.ne_of_gt hx, Nat.not_le_of_gt hx, hxne]
  have hgateLeaf :
      (DirectGLSSW.ShortEdgeWeighted.D1 a t D a (a + 1) (x + 1) -
        G1 a (a + 1) j) / 2 =
        ((t x).value + η.value * (t c).value) / 2 := by
    have hcCollapse : DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j = c := by
      rw [DirectGLSSW.ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt]
      · omega
      · omega
    simp [G1, DirectGLSSW.ShortEdgeWeighted.D1,
      DirectGLSSW.ShortEdgeWeighted.H1,
      DirectGLSSW.ShortEdgeCutFibers.collapseAfter,
      Nat.not_le_of_gt hx, Nat.not_le_of_gt (by omega : a < j), hcollapseX,
      hpred, hcCollapse]
  have hbranchUnsplit :
      DirectGLSSW.branchProduct
          (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U)
          (a :: (x :: ys).map Nat.succ) =
        ((DirectGLSSW.ShortEdgeWeighted.beta a t - (t x).value) / 2) *
          DirectGLSSW.branchProduct U (a :: x :: ys) := by
    rw [show a :: (x :: ys).map Nat.succ = a :: (x + 1) :: (ys.map Nat.succ) by
      simp only [List.map_cons]]
    rw [branchProduct_cons_cons, branchProduct_cons_cons]
    rw [hbranchHead]
    rw [hbranchTail']
    ring
  have hbranchLeaf :
      DirectGLSSW.branchProduct
          (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U)
          (a :: ((a + 1) :: (x :: ys).map Nat.succ)) =
        DirectGLSSW.branchProduct U (a :: x :: ys) := by
    rw [show a :: ((a + 1) :: (x :: ys).map Nat.succ) =
        a :: (a + 1) :: (x + 1) :: (ys.map Nat.succ) by simp only [List.map_cons]]
    rw [branchProduct_cons_cons, branchProduct_cons_cons]
    rw [hbranchLeafHead, hbranchLeafNext, hbranchTail']
    simp [DirectGLSSW.branchProduct]
  have hgateUnsplit :
      DirectGLSSW.gateProduct
          (DirectGLSSW.ShortEdgeWeighted.D1 a t D) G1 a j
          (a :: (x :: ys).map Nat.succ) =
        DirectGLSSW.gateProduct
          (DirectGLSSW.ShortEdgeWeighted.D0 a t D) G0 a c (a :: x :: ys) := by
    simpa [G1, G0, List.map_cons] using hgateCore
  have hgateShort :
      DirectGLSSW.gateProduct
          (DirectGLSSW.ShortEdgeWeighted.D1 a t D) G1 a j
          (a :: ((a + 1) :: (x :: ys).map Nat.succ)) =
        ((t x).value + η.value * (t c).value) / 2 *
          DirectGLSSW.gateProduct
            (DirectGLSSW.ShortEdgeWeighted.D0 a t D) G0 a c (a :: x :: ys) := by
    have hlist :
        a :: ((a + 1) :: (x :: ys).map Nat.succ) =
          a :: (a + 1) :: (x + 1) :: ys.map Nat.succ := by
      simp only [List.map_cons]
    rw [hlist, gateProduct_cons3, hgateLeaf]
    have hmapList :
        (a :: x :: ys).map Nat.succ = (a + 1) :: (x + 1) :: ys.map Nat.succ := by
      simp only [List.map_cons]
    rw [hmapList] at hgateMap
    rw [hgateMap]
  simp only [G1, G0] at hgateUnsplit hgateShort ⊢
  rw [hgateUnsplit, hbranchUnsplit, hgateShort, hbranchLeaf]
  ring

theorem leftEndpointContribution_twoLifts
    (a j : ℕ) (ha : 0 < a) (hBj : a + 1 < j)
    (t : ℕ → DirectGLSSW.Sign) (U : DirectGLSSW.IntervalArray)
    (η : DirectGLSSW.Sign) (D : DirectGLSSW.TripleArray)
    (H : ℕ → ℕ → ℕ → DirectGLSSW.Sign)
    (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo a (DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j)) :
    DirectGLSSW.cutContribution
        (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
        (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H x k y)
        (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U) a j
        (DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate a S
          DirectGLSSW.ShortEdgeCutFibers.EndpointLiftMode.unsplit) +
      DirectGLSSW.cutContribution
        (DirectGLSSW.ShortEdgeWeighted.D1 a t D)
        (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H1 a t H x k y)
        (DirectGLSSW.ShortEdgeWeighted.parentTable a ha t U) a j
        (DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate a S
          DirectGLSSW.ShortEdgeCutFibers.EndpointLiftMode.shortLeaf) =
      ((DirectGLSSW.ShortEdgeWeighted.beta a t +
          η.value * (t (DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j)).value) / 2) *
        DirectGLSSW.cutContribution
          (DirectGLSSW.ShortEdgeWeighted.D0 a t D)
          (fun x k y => -η.value * DirectGLSSW.ShortEdgeWeighted.H0 H x k y)
          U a (DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j) S := by
  have hc_lt : a < DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j := by
    rw [DirectGLSSW.ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt]
    · omega
    · omega
  have hc_succ : DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j + 1 = j := by
    rw [DirectGLSSW.ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt]
    · omega
    · omega
  have hSpos : ∀ x ∈ S, a < x := by
    intro x hx
    exact (Finset.mem_Ioo.mp (hS hx)).1
  let L := S.sort (· ≤ ·) ++ [DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j]
  have hLpos : ∀ x ∈ L, a < x := by
    intro x hx
    simp only [L, List.mem_append, List.mem_singleton] at hx
    rcases hx with hxS | rfl
    · exact hSpos x ((Finset.mem_sort _).mp hxS)
    · exact hc_lt
  have hLne : L ≠ [] := by simp [L]
  cases hL : L with
  | nil => exact (hLne hL).elim
  | cons x ys =>
      have hCoreList : DirectGLSSW.cutVertices a
          (DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j) S = a :: x :: ys := by
        change a :: L = a :: x :: ys
        rw [hL]
      have hx : a < x := hLpos x (by simp [hL])
      have hys : ∀ y ∈ ys, a < y := by
        intro y hy
        apply hLpos y
        rw [hL]
        simp [hy]
      have hUnsplitList := lifted_cutVertices a j
        (DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j) S hc_succ hS
      have hLeafList := lifted_cutVertices_shortLeaf a j
        (DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j) S hc_succ hS
      rw [hCoreList] at hUnsplitList hLeafList
      simp only [List.tail_cons] at hUnsplitList hLeafList
      simp only [DirectGLSSW.cutContribution]
      have hCandU : DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate a S
          DirectGLSSW.ShortEdgeCutFibers.EndpointLiftMode.unsplit =
          DirectGLSSW.ShortEdgeCutFibers.liftedCuts a S := by
        simp [DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate]
      have hCandL : DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate a S
          DirectGLSSW.ShortEdgeCutFibers.EndpointLiftMode.shortLeaf =
          DirectGLSSW.ShortEdgeCutFibers.liftedCuts a S ∪ {a + 1} := by
        simp [DirectGLSSW.ShortEdgeCutFibers.leftEndpointCandidate]
      have hLeafList' : DirectGLSSW.cutVertices a j
          (DirectGLSSW.ShortEdgeCutFibers.liftedCuts a S ∪ {a + 1}) =
          a :: (a + 1) :: (x :: ys).map Nat.succ := by
        simpa [hCandL] using hLeafList
      rw [hCandU, hCandL]
      rw [hUnsplitList, hLeafList']
      rw [hCoreList]
      simpa [DirectGLSSW.cutVertices, List.tail_cons] using
        endpoint_two_lift_words a j
          (DirectGLSSW.ShortEdgeCutFibers.collapseAfter a j)
          ha hc_lt hc_succ t U η D H x ys hx hys

end DirectGLSSW.ShortEdgeWeighted.LeftEndpointImpl
