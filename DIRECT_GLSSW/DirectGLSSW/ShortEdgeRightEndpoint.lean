import DirectGLSSW.ShortEdgeWeighted

open scoped BigOperators

namespace DirectGLSSW.ShortEdgeRightEndpoint

open DirectGLSSW
open DirectGLSSW.ShortEdgeWeighted

theorem liftedCuts_eq_self
    (a i : ℕ) (S : Finset ℕ) (hi : i < a)
    (hS : S ⊆ Finset.Ioo i a) :
    ShortEdgeCutFibers.liftedCuts a S = S := by
  ext x
  simp only [ShortEdgeCutFibers.liftedCuts, Finset.mem_image,
    ShortEdgeCutFibers.liftAfter]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hya : y < a := (Finset.mem_Ioo.mp (hS hy)).2
    simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hya] at hxy
    simpa [hxy] using hy
  · intro hx
    have hxa : x < a := (Finset.mem_Ioo.mp (hS hx)).2
    exact ⟨x, hx, by simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hxa]⟩

theorem sort_insert_largest
    (a i : ℕ) (S : Finset ℕ) (hi : i < a)
    (hS : S ⊆ Finset.Ioo i a) :
    (S ∪ {a}).sort (· ≤ ·) = S.sort (· ≤ ·) ++ [a] := by
  have hleft : List.Sorted (· < ·) ((S ∪ {a}).sort (· ≤ ·)) :=
    Finset.sort_sorted_lt _
  have hright : List.Sorted (· < ·) (S.sort (· ≤ ·) ++ [a]) := by
    change List.Pairwise (· < ·) (S.sort (· ≤ ·) ++ [a])
    rw [List.pairwise_append]
    refine ⟨Finset.sort_sorted_lt S, ?_, ?_⟩
    · simp
    · intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst y
      have hxS : x ∈ S := (Finset.mem_sort _).mp hx
      exact (Finset.mem_Ioo.mp (hS hxS)).2
  apply List.Sorted.eq_of_mem_iff hleft hright
  intro x
  simp [Finset.mem_sort, List.mem_append, List.mem_singleton, Finset.mem_union]

theorem rightEndpoint_unsplit_word
    (a i : ℕ) (S : Finset ℕ) (hi : i < a)
    (hS : S ⊆ Finset.Ioo i a) :
    cutVertices i (a + 1)
      (ShortEdgeCutFibers.rightEndpointCandidate a S
        ShortEdgeCutFibers.EndpointLiftMode.unsplit) =
      i :: (S.sort (· ≤ ·) ++ [a + 1]) := by
  rw [show ShortEdgeCutFibers.rightEndpointCandidate a S
      ShortEdgeCutFibers.EndpointLiftMode.unsplit =
      ShortEdgeCutFibers.liftedCuts a S by
        simp [ShortEdgeCutFibers.rightEndpointCandidate]]
  rw [liftedCuts_eq_self a i S hi hS]
  rfl

theorem rightEndpoint_shortLeaf_word
    (a i : ℕ) (S : Finset ℕ) (hi : i < a)
    (hS : S ⊆ Finset.Ioo i a) :
    cutVertices i (a + 1)
      (ShortEdgeCutFibers.rightEndpointCandidate a S
        ShortEdgeCutFibers.EndpointLiftMode.shortLeaf) =
      i :: (S.sort (· ≤ ·) ++ [a, a + 1]) := by
  rw [show ShortEdgeCutFibers.rightEndpointCandidate a S
      ShortEdgeCutFibers.EndpointLiftMode.shortLeaf = S ∪ {a} by
        calc
          ShortEdgeCutFibers.rightEndpointCandidate a S
              ShortEdgeCutFibers.EndpointLiftMode.shortLeaf =
              ShortEdgeCutFibers.liftedCuts a S ∪ {a} := by
                simp [ShortEdgeCutFibers.rightEndpointCandidate]
          _ = S ∪ {a} := by rw [liftedCuts_eq_self a i S hi hS]]
  change i :: ((S ∪ {a}).sort (· ≤ ·) ++ [a + 1]) = _
  rw [sort_insert_largest a i S hi hS]
  simp [List.append_assoc]

private theorem branchProduct_cons (b : IntervalArray) (x y : ℕ) (L : List ℕ) :
    branchProduct b (x :: y :: L) = b x y * branchProduct b (y :: L) := by
  simp [branchProduct, List.zip_cons_cons]

private theorem branchProduct_append_two (b : IntervalArray) :
    ∀ (P : List ℕ) (x y : ℕ),
      branchProduct b (P ++ [x, y]) = branchProduct b (P ++ [x]) * b x y := by
  intro P
  induction P with
  | nil => intro x y; simp [branchProduct]
  | cons z P ih =>
      intro x y
      cases P with
      | nil => simp [List.cons_append, branchProduct]
      | cons w P =>
          change b z w * branchProduct b (w :: (P ++ [x, y])) =
            (b z w * branchProduct b (w :: (P ++ [x]))) * b x y
          have h : branchProduct b (w :: (P ++ [x, y])) =
              branchProduct b (w :: (P ++ [x])) * b x y := by
            simpa only [List.cons_append] using ih x y
          rw [h]
          ring

private theorem gateProduct_cons (D H : TripleArray) (i j : ℕ)
    (x k y : ℕ) (L : List ℕ) :
    gateProduct D H i j (x :: k :: y :: L) =
      ((D x k y - H i k j) / 2) * gateProduct D H i j (k :: y :: L) := by
  simp [gateProduct, List.zip_cons_cons]

private theorem gateProduct_append_two (D H : TripleArray) (i j : ℕ) :
    ∀ (P : List ℕ) (p x y : ℕ),
      gateProduct D H i j (P ++ [p, x, y]) =
        gateProduct D H i j (P ++ [p, x]) * ((D p x y - H i x j) / 2) := by
  intro P
  induction P with
  | nil => intro p x y; simp [gateProduct]
  | cons z P ih =>
      intro p x y
      cases P with
      | nil =>
          change gateProduct D H i j (z :: [p, x, y]) =
            gateProduct D H i j (z :: [p, x]) * ((D p x y - H i x j) / 2)
          simp [gateProduct, List.zip_cons_cons]
      | cons w P =>
          cases P with
          | nil =>
              change gateProduct D H i j (z :: w :: p :: x :: y :: []) =
                gateProduct D H i j (z :: w :: p :: x :: []) *
                  ((D p x y - H i x j) / 2)
              simp [gateProduct_cons, gateProduct]
              ring
          | cons q P =>
              simp only [List.cons_append, gateProduct_cons]
              have h : gateProduct D H i j (w :: q :: (P ++ [p, x, y])) =
                  gateProduct D H i j (w :: q :: (P ++ [p, x])) *
                    ((D p x y - H i x j) / 2) := by
                simpa only [List.cons_append] using ih p x y
              rw [h]
              ring

private theorem gateFactor_parent_eq
    (a i e x k y : ℕ) (ha : 0 < a) (hi : i < a)
    (he : e = a ∨ e = a + 1) (hx : x ≤ a) (hk : k < a)
    (hy : y ≤ a + 1) (t : ℕ → Sign) (D : TripleArray)
    (H : ℕ → ℕ → ℕ → Sign) (η : Sign) :
    ((ShortEdgeWeighted.D1 a t D x k y -
        (fun p q r => -η.value * ShortEdgeWeighted.H1 a t H p q r) i k e) / 2) =
      ((ShortEdgeWeighted.D0 a t D x k (ShortEdgeCutFibers.collapseAfter a y) -
        (fun p q r => -η.value * ShortEdgeWeighted.H0 H p q r) i k a) / 2) := by
  have hci : ShortEdgeCutFibers.collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (Nat.le_of_lt hi)
  have hck : ShortEdgeCutFibers.collapseAfter a k = k :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a k (Nat.le_of_lt hk)
  have hce : ShortEdgeCutFibers.collapseAfter a e = a := by
    rcases he with he | he
    · rw [he]
      exact ShortEdgeCutFibers.collapseAfter_eq_of_le a a le_rfl
    · rw [he]
      exact ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (a + 1) (by omega)
  have hka : k ≠ a := by omega
  have hka1 : k ≠ a + 1 := by omega
  have hxa : x ≠ a + 1 := by omega
  simp [ShortEdgeWeighted.D1, ShortEdgeWeighted.D0,
    ShortEdgeWeighted.H1, ShortEdgeWeighted.H0,
    hci, hck, hce, hka, hka1, hxa,
    ShortEdgeCutFibers.collapseAfter_eq_of_le a x hx]

private theorem gateProduct_endpoint_parent
    (a i e j : ℕ) (ha : 0 < a) (hi : i < a)
    (he : e = a ∨ e = a + 1) (hj : j = a ∨ j = a + 1)
    (t : ℕ → Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    (η : Sign) :
    ∀ P : List ℕ, (∀ x ∈ P, x < a) →
      gateProduct (ShortEdgeWeighted.D1 a t D)
        (fun p k q => -η.value * ShortEdgeWeighted.H1 a t H p k q)
        i e (P ++ [j]) =
      gateProduct (ShortEdgeWeighted.D0 a t D)
        (fun p k q => -η.value * ShortEdgeWeighted.H0 H p k q)
        i a (P ++ [a]) := by
  have hce : ShortEdgeCutFibers.collapseAfter a e = a := by
    rcases he with he | he
    · rw [he]
      exact ShortEdgeCutFibers.collapseAfter_eq_of_le a a le_rfl
    · rw [he]
      exact ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (a + 1) (by omega)
  have hcj : ShortEdgeCutFibers.collapseAfter a j = a := by
    rcases hj with hj | hj
    · rw [hj]
      exact ShortEdgeCutFibers.collapseAfter_eq_of_le a a le_rfl
    · rw [hj]
      exact ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (a + 1) (by omega)
  intro P
  induction P with
  | nil => intro _; simp [gateProduct]
  | cons x xs ih =>
      intro hP
      cases xs with
      | nil => simp [gateProduct]
      | cons k ks =>
          have hx : x < a := hP x (by simp)
          have hk : k < a := hP k (by simp)
          cases ks with
          | nil =>
              have hfactor := gateFactor_parent_eq a i e x k j ha hi he
                (Nat.le_of_lt hx) hk (by omega) t D H η
              change gateProduct (ShortEdgeWeighted.D1 a t D)
                  (fun p q r => -η.value * ShortEdgeWeighted.H1 a t H p q r)
                  i e (x :: k :: j :: []) =
                gateProduct (ShortEdgeWeighted.D0 a t D)
                  (fun p q r => -η.value * ShortEdgeWeighted.H0 H p q r)
                  i a (x :: k :: a :: [])
              have hleft :
                  gateProduct (ShortEdgeWeighted.D1 a t D)
                    (fun p q r => -η.value * ShortEdgeWeighted.H1 a t H p q r)
                    i e (x :: k :: j :: []) =
                    (ShortEdgeWeighted.D1 a t D x k j -
                      (fun p q r => -η.value * ShortEdgeWeighted.H1 a t H p q r) i k e) / 2 := by
                simp [gateProduct]
              have hright :
                  gateProduct (ShortEdgeWeighted.D0 a t D)
                    (fun p q r => -η.value * ShortEdgeWeighted.H0 H p q r)
                    i a (x :: k :: a :: []) =
                    (ShortEdgeWeighted.D0 a t D x k a -
                      (fun p q r => -η.value * ShortEdgeWeighted.H0 H p q r) i k a) / 2 := by
                simp [gateProduct]
              rw [hleft, hright, hfactor, hcj]
          | cons y ys =>
              have hy : y < a := hP y (by simp)
              have htail : ∀ z ∈ k :: y :: ys, z < a := by
                intro z hz
                have hz' : z = k ∨ z = y ∨ z ∈ ys := by simpa using hz
                rcases hz' with rfl | rfl | hz'
                · exact hk
                · exact hy
                · exact hP z (by simp [hz'])
              have hfactor := gateFactor_parent_eq a i e x k y ha hi he
                (Nat.le_of_lt hx) hk (by omega) t D H η
              change ((ShortEdgeWeighted.D1 a t D x k y -
                  (fun p q r => -η.value * ShortEdgeWeighted.H1 a t H p q r) i k e) / 2) *
                  gateProduct (ShortEdgeWeighted.D1 a t D)
                    (fun p q r => -η.value * ShortEdgeWeighted.H1 a t H p q r)
                    i e (k :: y :: (ys ++ [j])) =
                ((ShortEdgeWeighted.D0 a t D x k y -
                  (fun p q r => -η.value * ShortEdgeWeighted.H0 H p q r) i k a) / 2) *
                  gateProduct (ShortEdgeWeighted.D0 a t D)
                    (fun p q r => -η.value * ShortEdgeWeighted.H0 H p q r)
                    i a (k :: y :: (ys ++ [a]))
              rw [hfactor]
              rw [ShortEdgeCutFibers.collapseAfter_eq_of_le a y (Nat.le_of_lt hy)]
              have hgate :
                  gateProduct (ShortEdgeWeighted.D1 a t D)
                    (fun p q r => -η.value * ShortEdgeWeighted.H1 a t H p q r)
                    i e (k :: y :: (ys ++ [j])) =
                  gateProduct (ShortEdgeWeighted.D0 a t D)
                    (fun p q r => -η.value * ShortEdgeWeighted.H0 H p q r)
                    i a (k :: y :: (ys ++ [a])) := by
                simpa only [List.cons_append] using ih htail
              rw [hgate]

private theorem parentTable_core_edge
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (x y : ℕ) (hx : x < a) (hy : y ≤ a) :
    ShortEdgeWeighted.parentTable a ha t U x y = U x y := by
  have hcx := ShortEdgeCutFibers.collapseAfter_eq_of_le a x (Nat.le_of_lt hx)
  have hcy := ShortEdgeCutFibers.collapseAfter_eq_of_le a y hy
  unfold ShortEdgeWeighted.parentTable
  split_ifs with h1 h2 h3 h4
  · omega
  · omega
  · omega
  · omega
  · simp [hcx, hcy]

private theorem parentTable_right_endpoint
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (x : ℕ) (hx : x < a) :
    ShortEdgeWeighted.parentTable a ha t U x (a + 1) =
      ((ShortEdgeWeighted.alpha a ha t - (t x).value) / 2) * U x a := by
  have hcx := ShortEdgeCutFibers.collapseAfter_eq_of_le a x (Nat.le_of_lt hx)
  have hxa : x ≠ a := by omega
  unfold ShortEdgeWeighted.parentTable
  simp [hxa, hx, hcx, ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (a + 1) (by omega)]

private theorem branchProduct_parent_core
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray) :
    ∀ P : List ℕ, (∀ x ∈ P, x < a) →
      branchProduct (ShortEdgeWeighted.parentTable a ha t U) (P ++ [a]) =
        branchProduct U (P ++ [a]) := by
  intro P
  induction P with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro hP
      cases xs with
      | nil =>
          have hx : x < a := hP x (by simp)
          simp [branchProduct, ShortEdgeWeighted.parentTable,
            ShortEdgeCutFibers.collapseAfter, hx, (Nat.le_of_lt hx)]
      | cons y ys =>
          have hx : x < a := hP x (by simp)
          have hy : y < a := hP y (by simp)
          have htail : ∀ z ∈ y :: ys, z < a := by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hy
            · exact hP z (by simp [hz])
          have htable := parentTable_core_edge a ha t U x y hx (Nat.le_of_lt hy)
          have hrest := ih htail
          change ShortEdgeWeighted.parentTable a ha t U x y *
                branchProduct (ShortEdgeWeighted.parentTable a ha t U)
                  (y :: (ys ++ [a])) =
              U x y * branchProduct U (y :: (ys ++ [a]))
          rw [htable]
          have hrest' :
              branchProduct (ShortEdgeWeighted.parentTable a ha t U)
                  (y :: (ys ++ [a])) = branchProduct U (y :: (ys ++ [a])) := by
            simpa only [List.cons_append] using hrest
          rw [hrest']

private theorem branchProduct_unsplit_endpoint
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (x : ℕ) (hx : x < a) :
    ∀ Q : List ℕ, (∀ z ∈ Q, z < a) →
      branchProduct (ShortEdgeWeighted.parentTable a ha t U)
          (Q ++ [x, a + 1]) =
        branchProduct U (Q ++ [x, a]) *
          ((ShortEdgeWeighted.alpha a ha t - (t x).value) / 2) := by
  intro Q
  induction Q with
  | nil =>
      intro _
      simp [branchProduct, ShortEdgeWeighted.parentTable,
        ShortEdgeWeighted.alpha, ShortEdgeCutFibers.collapseAfter, hx,
        (by omega : x ≠ a)]
      split_ifs <;> try omega
      ring
  | cons q qs ih =>
      intro hQ
      have hq : q < a := hQ q (by simp)
      have htail : ∀ z ∈ qs, z < a := by
        intro z hz
        exact hQ z (by simp [hz])
      have hrest := ih htail
      cases qs with
      | nil =>
          have htable := parentTable_core_edge a ha t U q x hq (Nat.le_of_lt hx)
          change ShortEdgeWeighted.parentTable a ha t U q x *
                branchProduct (ShortEdgeWeighted.parentTable a ha t U) [x, a + 1] =
              U q x * branchProduct U [x, a] *
                ((ShortEdgeWeighted.alpha a ha t - (t x).value) / 2)
          rw [htable]
          simp only [branchProduct] at hrest ⊢
          simpa [mul_assoc] using congrArg (fun z => U q x * z) hrest
      | cons y ys =>
          have hy : y < a := hQ y (by simp)
          have htable := parentTable_core_edge a ha t U q y hq (Nat.le_of_lt hy)
          change ShortEdgeWeighted.parentTable a ha t U q y *
                branchProduct (ShortEdgeWeighted.parentTable a ha t U)
                  (y :: (ys ++ [x, a + 1])) =
              U q y * branchProduct U (y :: (ys ++ [x, a])) *
                ((ShortEdgeWeighted.alpha a ha t - (t x).value) / 2)
          rw [htable]
          have hrest' :
              branchProduct (ShortEdgeWeighted.parentTable a ha t U)
                  (y :: (ys ++ [x, a + 1])) =
                branchProduct U (y :: (ys ++ [x, a])) *
                  ((ShortEdgeWeighted.alpha a ha t - (t x).value) / 2) := by
            simpa only [List.cons_append] using hrest
          rw [hrest']
          ring

private theorem exists_append_singleton {α : Type} (l : List α) (hne : l ≠ []) :
    ∃ Q x, l = Q ++ [x] := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
      cases xs with
      | nil => exact ⟨[], x, rfl⟩
      | cons y ys =>
          obtain ⟨Q, z, hQ⟩ := ih (by simp)
          refine ⟨x :: Q, z, ?_⟩
          simp [hQ, List.cons_append]

/-- The right endpoint two-lift contribution identity for arbitrary arrays. -/
theorem rightEndpointContribution_twoLifts
    (a i : ℕ) (ha : 0 < a) (hiA : i < a)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign) (D : TripleArray)
    (H : ℕ → ℕ → ℕ → Sign) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo (ShortEdgeCutFibers.collapseAfter a i) a) :
    cutContribution (ShortEdgeWeighted.D1 a t D)
        (fun x k y => -η.value * ShortEdgeWeighted.H1 a t H x k y)
        (ShortEdgeWeighted.parentTable a ha t U) i (a + 1)
        (ShortEdgeCutFibers.rightEndpointCandidate a S
          ShortEdgeCutFibers.EndpointLiftMode.unsplit) +
      cutContribution (ShortEdgeWeighted.D1 a t D)
        (fun x k y => -η.value * ShortEdgeWeighted.H1 a t H x k y)
        (ShortEdgeWeighted.parentTable a ha t U) i (a + 1)
        (ShortEdgeCutFibers.rightEndpointCandidate a S
          ShortEdgeCutFibers.EndpointLiftMode.shortLeaf) =
      ((ShortEdgeWeighted.alpha a ha t +
          η.value * (t (ShortEdgeCutFibers.collapseAfter a i)).value) / 2) *
        cutContribution (ShortEdgeWeighted.D0 a t D)
          (fun x k y => -η.value * ShortEdgeWeighted.H0 H x k y)
          U (ShortEdgeCutFibers.collapseAfter a i) a S := by
  have hiC : ShortEdgeCutFibers.collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (Nat.le_of_lt hiA)
  have hSc : S ⊆ Finset.Ioo i a := by simpa [hiC] using hS
  let P : List ℕ := i :: S.sort (· ≤ ·)
  have hP : ∀ x ∈ P, x < a := by
    intro x hx
    simp only [P, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hiA
    · exact (Finset.mem_Ioo.mp (hSc ((Finset.mem_sort _).mp hx))).2
  have hCoreWord : cutVertices i a S = P ++ [a] := by
    simp [P, cutVertices, List.cons_append]
  have hUnsplitWord := rightEndpoint_unsplit_word a i S hiA hSc
  have hLeafWord := rightEndpoint_shortLeaf_word a i S hiA hSc
  have hUnsplit :
      ShortEdgeCutFibers.rightEndpointCandidate a S
          ShortEdgeCutFibers.EndpointLiftMode.unsplit = S := by
    simp [ShortEdgeCutFibers.rightEndpointCandidate,
      liftedCuts_eq_self a i S hiA hSc]
  have hLeaf :
      ShortEdgeCutFibers.rightEndpointCandidate a S
          ShortEdgeCutFibers.EndpointLiftMode.shortLeaf = S ∪ {a} := by
    calc
      ShortEdgeCutFibers.rightEndpointCandidate a S
          ShortEdgeCutFibers.EndpointLiftMode.shortLeaf =
          ShortEdgeCutFibers.liftedCuts a S ∪ {a} := by
            simp [ShortEdgeCutFibers.rightEndpointCandidate]
      _ = S ∪ {a} := by rw [liftedCuts_eq_self a i S hiA hSc]
  have hParentUnsplit :
      cutVertices i (a + 1) (ShortEdgeCutFibers.rightEndpointCandidate a S
        ShortEdgeCutFibers.EndpointLiftMode.unsplit) = P ++ [a + 1] := by
    rw [hUnsplit]
    rw [hUnsplit] at hUnsplitWord
    simpa [P, List.cons_append] using hUnsplitWord
  have hParentLeaf :
      cutVertices i (a + 1) (ShortEdgeCutFibers.rightEndpointCandidate a S
        ShortEdgeCutFibers.EndpointLiftMode.shortLeaf) = (P ++ [a]) ++ [a + 1] := by
    rw [hLeaf]
    rw [hLeaf] at hLeafWord
    simpa [P, List.cons_append, List.append_assoc] using hLeafWord
  obtain ⟨Q, x, hQx⟩ := exists_append_singleton P (by simp [P])
  have hx : x < a := by
    apply hP x
    rw [hQx]
    simp
  have hQ : ∀ z ∈ Q, z < a := by
    intro z hz
    apply hP z
    rw [hQx]
    simp [hz]
  let G1 := fun x k y => -η.value * ShortEdgeWeighted.H1 a t H x k y
  let G0 := fun x k y => -η.value * ShortEdgeWeighted.H0 H x k y
  have hGateUnsplit := gateProduct_endpoint_parent a i (a + 1) (a + 1) ha hiA
    (Or.inr rfl) (Or.inr rfl) t D H η P hP
  have hBranchCore := branchProduct_parent_core a ha t U P hP
  have hBranchUnsplit := branchProduct_unsplit_endpoint a ha t U x hx Q hQ
  have hGateLeafFactor := gateProduct_append_two
    (ShortEdgeWeighted.D1 a t D) G1 i (a + 1) Q x a (a + 1)
  have hBranchLeafFactor := branchProduct_append_two
    (ShortEdgeWeighted.parentTable a ha t U) (Q ++ [x]) a (a + 1)
  have hTableShort : ShortEdgeWeighted.parentTable a ha t U a (a + 1) = 1 := by
    simp [ShortEdgeWeighted.parentTable]
  have hLocalGate :
      (ShortEdgeWeighted.D1 a t D x a (a + 1) - G1 i a (a + 1)) / 2 =
        ((t x).value + η.value * (t i).value) / 2 := by
    have hcx := ShortEdgeCutFibers.collapseAfter_eq_of_le a x (Nat.le_of_lt hx)
    have hci := ShortEdgeCutFibers.collapseAfter_eq_of_le a i (Nat.le_of_lt hiA)
    simp [G1, ShortEdgeWeighted.D1, ShortEdgeWeighted.H1,
      hx, hiA, hcx, hci,
      (by omega : x ≠ a), (by omega : x ≠ a + 1),
      (by omega : i ≠ a), (by omega : a ≠ a + 1)]
  have hGateLeaf :
      gateProduct (ShortEdgeWeighted.D1 a t D) G1 i (a + 1)
          ((Q ++ [x]) ++ [a, a + 1]) =
        ((t x).value + η.value * (t i).value) / 2 *
          gateProduct (ShortEdgeWeighted.D0 a t D) G0 i a (P ++ [a]) := by
    have hprefix :
        gateProduct (ShortEdgeWeighted.D1 a t D) G1 i (a + 1)
            ((Q ++ [x]) ++ [a]) =
          gateProduct (ShortEdgeWeighted.D0 a t D) G0 i a (P ++ [a]) := by
      have hGateLeafCore := gateProduct_endpoint_parent a i (a + 1) a ha hiA
        (Or.inr rfl) (Or.inl rfl) t D H η P hP
      simpa [G1, G0, hQx, List.append_assoc] using hGateLeafCore
    have happend :
        gateProduct (ShortEdgeWeighted.D1 a t D) G1 i (a + 1)
            ((Q ++ [x]) ++ [a, a + 1]) =
          gateProduct (ShortEdgeWeighted.D1 a t D) G1 i (a + 1)
            ((Q ++ [x]) ++ [a]) *
            ((ShortEdgeWeighted.D1 a t D x a (a + 1) - G1 i a (a + 1)) / 2) := by
      simpa [List.append_assoc] using hGateLeafFactor
    rw [hprefix, hLocalGate] at happend
    calc
      gateProduct (ShortEdgeWeighted.D1 a t D) G1 i (a + 1)
          ((Q ++ [x]) ++ [a, a + 1]) =
        gateProduct (ShortEdgeWeighted.D0 a t D) G0 i a (P ++ [a]) *
          (((t x).value + η.value * (t i).value) / 2) := happend
      _ = ((t x).value + η.value * (t i).value) / 2 *
          gateProduct (ShortEdgeWeighted.D0 a t D) G0 i a (P ++ [a]) := by ring
  have hBranchLeaf :
      branchProduct (ShortEdgeWeighted.parentTable a ha t U)
          ((Q ++ [x]) ++ [a, a + 1]) = branchProduct U (P ++ [a]) := by
    rw [hBranchLeafFactor, hTableShort]
    simp only [mul_one]
    have hprefix' :
        branchProduct (ShortEdgeWeighted.parentTable a ha t U)
            ((Q ++ [x]) ++ [a]) = branchProduct U (P ++ [a]) := by
      simpa [hQx, List.append_assoc] using hBranchCore
    rw [hprefix']
  have hUnsplitGate' :
      gateProduct (ShortEdgeWeighted.D1 a t D) G1 i (a + 1) (P ++ [a + 1]) =
        gateProduct (ShortEdgeWeighted.D0 a t D) G0 i a (P ++ [a]) := hGateUnsplit
  have hUnsplitBranch' :
      branchProduct (ShortEdgeWeighted.parentTable a ha t U) (P ++ [a + 1]) =
      branchProduct U (P ++ [a]) *
          ((ShortEdgeWeighted.alpha a ha t - (t x).value) / 2) := by
    simpa [hQx, List.append_assoc] using hBranchUnsplit
  have hGateLeaf' :
      gateProduct (ShortEdgeWeighted.D1 a t D)
          (fun x k y => -η.value * ShortEdgeWeighted.H1 a t H x k y)
          i (a + 1) (P ++ [a] ++ [a + 1]) =
        ((t x).value + η.value * (t i).value) / 2 *
          gateProduct (ShortEdgeWeighted.D0 a t D)
            (fun x k y => -η.value * ShortEdgeWeighted.H0 H x k y)
            i a (P ++ [a]) := by
    simpa [G1, G0, hQx, List.append_assoc] using hGateLeaf
  have hBranchLeaf' :
      branchProduct (ShortEdgeWeighted.parentTable a ha t U)
          (P ++ [a] ++ [a + 1]) = branchProduct U (P ++ [a]) := by
    simpa [hQx, List.append_assoc] using hBranchLeaf
  simp only [cutContribution]
  rw [hParentUnsplit, hParentLeaf]
  rw [hiC, hCoreWord]
  rw [hUnsplitGate', hUnsplitBranch', hGateLeaf', hBranchLeaf']
  simp only [G1, G0]
  ring

end DirectGLSSW.ShortEdgeRightEndpoint
