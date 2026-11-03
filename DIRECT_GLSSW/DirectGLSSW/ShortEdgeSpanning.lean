import DirectGLSSW.ShortEdgeWeighted

namespace DirectGLSSW.ShortEdgeWeighted
open scoped BigOperators

private theorem splitAroundList {a : ℕ} {xs : List ℕ} (ha : a ∈ xs) :
    ∃ s t, xs = s ++ a :: t := by
  exact List.mem_iff_append.mp ha

private theorem exists_snoc_of_ne_nil {α : Type} : ∀ xs : List α, xs ≠ [] →
    ∃ pre x, xs = pre ++ [x]
  | [], h => (h rfl).elim
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: xs, _ => by
      obtain ⟨pre, z, hz⟩ := exists_snoc_of_ne_nil (y :: xs) (by simp)
      exact ⟨x :: pre, z, by simp [hz]⟩

private theorem exists_cons_of_ne_nil {α : Type} {xs : List α} (h : xs ≠ []) :
    ∃ x post, xs = x :: post := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => exact ⟨x, xs, rfl⟩

private theorem coreWord_neighborhood (a i j : ℕ) (S : Finset ℕ)
    (haS : a ∈ S) (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j))
    (hiA : i < a) (hBj : a + 1 < j) :
    ∃ pre L R post,
      cutVertices (ShortEdgeCutFibers.collapseAfter a i)
          (ShortEdgeCutFibers.collapseAfter a j) S = pre ++ [L, a, R] ++ post ∧
        L < a ∧ a < R := by
  have haSort : a ∈ S.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr haS
  obtain ⟨s, t, hsort⟩ := splitAroundList haSort
  let pfx := i :: s
  let sfx := t ++ [ShortEdgeCutFibers.collapseAfter a j]
  obtain ⟨pre, L, hp⟩ := exists_snoc_of_ne_nil pfx (by simp [pfx])
  obtain ⟨R, post, hq⟩ := exists_cons_of_ne_nil (xs := sfx) (by simp [sfx])
  have hp' : i :: s = pre ++ [L] := by simpa [pfx] using hp
  have hq' : t ++ [ShortEdgeCutFibers.collapseAfter a j] = R :: post := by
    simpa [sfx] using hq
  have hci : ShortEdgeCutFibers.collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hCore : i < ShortEdgeCutFibers.collapseAfter a j := by
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  let v := cutVertices i (ShortEdgeCutFibers.collapseAfter a j) S
  have hvPair : v.Pairwise (· < ·) := by
    simpa [v] using cutVertices_pairwise hCore hS
  have hword : v = pre ++ [L, a, R] ++ post := by
    simp only [v, cutVertices, hsort]
    calc
      i :: ((s ++ a :: t) ++ [ShortEdgeCutFibers.collapseAfter a j]) =
          (i :: s) ++ a :: (t ++ [ShortEdgeCutFibers.collapseAfter a j]) := by
        simp only [List.cons_append, List.append_assoc]
      _ = (pre ++ [L]) ++ a :: (R :: post) := by
        rw [hp', hq']
      _ = pre ++ [L, a, R] ++ post := by simp [List.append_assoc]
  have hseg : List.Sublist [L, a, R] v := by
    rw [hword]
    exact (List.sublist_append_left [L, a, R] post).trans
      ((List.sublist_append_right pre [L, a, R]).append_right post)
  have hsegPair := List.Pairwise.sublist hseg hvPair
  simp only [List.pairwise_cons, List.pairwise_singleton] at hsegPair
  exact ⟨pre, L, R, post, by simpa [v, hci] using hword,
    hsegPair.1 a (by simp), hsegPair.2.1 R (by simp)⟩

private theorem threeLiftScalar (α β : ℚ) (a b h η : Sign) :
    (α - a.value) / 2 * ((a.value + η.value * h.value) / 2) +
      (β - b.value) / 2 * ((a.value + η.value * h.value) / 2) +
      (a.value + η.value * h.value) * (b.value + η.value * h.value) / 4 =
    ((α + β) / 2) * ((a.value + η.value * h.value) / 2) := by
  have hcancel := DirectGLSSW.spanning_three_lifts a b h η
  calc
    _ = ((α + β) / 2) * ((a.value + η.value * h.value) / 2) +
        (-(a.value + b.value) * (a.value + η.value * h.value) / 4 +
          (a.value + η.value * h.value) * (b.value + η.value * h.value) / 4) := by ring
    _ = ((α + β) / 2) * ((a.value + η.value * h.value) / 2) := by
      rw [hcancel]
      ring

private theorem strictCutWord_eq_of_toFinset {xs ys : List ℕ}
    (hxs : xs.Pairwise (· < ·)) (hys : ys.Pairwise (· < ·))
    (hset : xs.toFinset = ys.toFinset) : xs = ys := by
  have hxsN : xs.Nodup := hxs.imp (fun h => Nat.ne_of_lt h)
  have hysN : ys.Nodup := hys.imp (fun h => Nat.ne_of_lt h)
  have hxsSort := (List.toFinset_sort (· ≤ ·) hxsN).mpr
    (hxs.imp (fun h => Nat.le_of_lt h))
  have hysSort := (List.toFinset_sort (· ≤ ·) hysN).mpr
    (hys.imp (fun h => Nat.le_of_lt h))
  calc
    xs = Finset.sort (· ≤ ·) xs.toFinset := hxsSort.symm
    _ = Finset.sort (· ≤ ·) ys.toFinset := by rw [hset]
    _ = ys := hysSort

private theorem pairwise_rel_append {α : Type} {R : α → α → Prop} :
    ∀ (xs ys : List α), (xs ++ ys).Pairwise R →
      ∀ x ∈ xs, ∀ y ∈ ys, R x y
  | [], ys, _, x, hx, _, _ => by simp at hx
  | z :: xs, ys, h, x, hx, y, hy => by
      change (z :: (xs ++ ys)).Pairwise R at h
      simp only [List.pairwise_cons] at h
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h.1 y (List.mem_append.mpr (Or.inr hy))
      · exact pairwise_rel_append xs ys h.2 x hx y hy

private theorem liftAfter_strictMono (a : ℕ) : StrictMono (ShortEdgeCutFibers.liftAfter a) := by
  intro x y hxy
  by_cases hx : x ≤ a <;> by_cases hy : y ≤ a <;>
    simp [ShortEdgeCutFibers.liftAfter, hx, hy] <;> omega

private theorem sort_image_liftAfter (a : ℕ) (S : Finset ℕ) :
    (S.image (ShortEdgeCutFibers.liftAfter a)).sort (· ≤ ·) =
      (S.sort (· ≤ ·)).map (ShortEdgeCutFibers.liftAfter a) := by
  have hmap := Multiset.map_sort (r := (· ≤ ·)) (r' := (· ≤ ·))
    (ShortEdgeCutFibers.liftAfter a) S.1 (by
      intro x hx y hy
      constructor
      · intro hxy
        by_cases heq : x = y
        · subst y
          exact le_rfl
        · exact Nat.le_of_lt (liftAfter_strictMono a (lt_of_le_of_ne hxy heq))
      · intro hxy
        by_contra hnot
        have hyx : y < x := lt_of_not_ge hnot
        exact (not_lt_of_ge hxy) (liftAfter_strictMono a hyx))
  have hinj : Set.InjOn (ShortEdgeCutFibers.liftAfter a) (S : Set ℕ) := by
    intro x hx y hy hxy
    exact (liftAfter_strictMono a).injective hxy
  rw [← Finset.sort_val, ← Finset.sort_val, Finset.image_val_of_injOn hinj]
  exact hmap.symm

private theorem cutVertices_lifted_span
    (a i j : ℕ) (S : Finset ℕ) (hiA : i < a) (hBj : a + 1 < j) :
    cutVertices i j (ShortEdgeCutFibers.liftedCuts a S) =
      (cutVertices (ShortEdgeCutFibers.collapseAfter a i)
        (ShortEdgeCutFibers.collapseAfter a j) S).map
        (ShortEdgeCutFibers.liftAfter a) := by
  have hci := ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hcj := ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)
  have hleft : ShortEdgeCutFibers.liftAfter a
      (ShortEdgeCutFibers.collapseAfter a i) = i := by
    rw [hci]
    simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hiA]
  have hjcore : a < ShortEdgeCutFibers.collapseAfter a j := by rw [hcj]; omega
  have hright : ShortEdgeCutFibers.liftAfter a
      (ShortEdgeCutFibers.collapseAfter a j) = j := by
    rw [hcj]
    change (if j - 1 ≤ a then j - 1 else (j - 1) + 1) = j
    rw [if_neg (by omega)]
    have hjge1 : 1 ≤ j := by omega
    exact Nat.sub_add_cancel hjge1
  change i :: ((S.image (ShortEdgeCutFibers.liftAfter a)).sort (· ≤ ·) ++ [j]) =
    ShortEdgeCutFibers.liftAfter a (ShortEdgeCutFibers.collapseAfter a i) ::
      ((S.sort (· ≤ ·) ++ [ShortEdgeCutFibers.collapseAfter a j]).map
        (ShortEdgeCutFibers.liftAfter a))
  rw [sort_image_liftAfter]
  simp only [List.map_append, List.map_singleton, hleft, hright]

theorem spanCandidate_cutAtA_word
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (S : Finset ℕ) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j)) :
    cutVertices i j (ShortEdgeCutFibers.spanCandidate a S
      ShortEdgeCutFibers.SpanLiftMode.cutAtA) =
      (cutVertices (ShortEdgeCutFibers.collapseAfter a i)
        (ShortEdgeCutFibers.collapseAfter a j) S).map
          (ShortEdgeCutFibers.liftAfter a) := by
  have haLift : a ∈ ShortEdgeCutFibers.liftedCuts a S := by
    exact Finset.mem_image.mpr ⟨a, haS, by simp [ShortEdgeCutFibers.liftAfter]⟩
  have hCandidate : ShortEdgeCutFibers.spanCandidate a S
      ShortEdgeCutFibers.SpanLiftMode.cutAtA = ShortEdgeCutFibers.liftedCuts a S := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ShortEdgeCutFibers.spanCandidate, haLift]
    · simp [ShortEdgeCutFibers.spanCandidate, hxa]
  rw [hCandidate]
  exact cutVertices_lifted_span a i j S hiA hBj

private theorem cutVertices_span_mem_ne_a
    (a i j : ℕ) (S : Finset ℕ) (hiA : i < a) (hBj : a + 1 < j)
    (haNotS : a ∉ S) {x : ℕ}
    (hx : x ∈ cutVertices (ShortEdgeCutFibers.collapseAfter a i)
      (ShortEdgeCutFibers.collapseAfter a j) S) : x ≠ a := by
  have hci := ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hcj := ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)
  change x ∈ ShortEdgeCutFibers.collapseAfter a i ::
    (S.sort (· ≤ ·) ++ [ShortEdgeCutFibers.collapseAfter a j]) at hx
  simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hx
  rcases hx with hxI | hx
  · rw [hxI, hci]
    omega
  · rcases hx with hxS | hxJ
    · have hxS' : x ∈ S := (Finset.mem_sort (· ≤ ·)).mp hxS
      intro hxa
      subst x
      exact haNotS hxS'
    · have hxJ' : x = ShortEdgeCutFibers.collapseAfter a j := by simpa using hxJ
      rw [hxJ', hcj]
      omega

private theorem branchProduct_congr_span {b₁ b₂ : IntervalArray} {v : List ℕ}
    (h : ∀ x y, (x, y) ∈ v.zip v.tail → b₁ x y = b₂ x y) :
    branchProduct b₁ v = branchProduct b₂ v := by
  unfold branchProduct
  congr 1
  apply List.map_congr_left
  rintro ⟨x, y⟩ hxy
  exact h x y hxy

private theorem gateProduct_congr_span {D₁ D₂ H₁ H₂ : TripleArray}
    {i j : ℕ} {v : List ℕ}
    (hD : ∀ x k y, (x, k, y) ∈ v.zip (v.tail.zip v.tail.tail) →
      D₁ x k y = D₂ x k y)
    (hH : ∀ x k y, (x, k, y) ∈ v.zip (v.tail.zip v.tail.tail) →
      H₁ i k j = H₂ i k j) :
    gateProduct D₁ H₁ i j v = gateProduct D₂ H₂ i j v := by
  unfold gateProduct
  congr 1
  apply List.map_congr_left
  rintro ⟨x, k, y⟩ hxyz
  change (D₁ x k y - H₁ i k j) / 2 = (D₂ x k y - H₂ i k j) / 2
  rw [hD x k y hxyz, hH x k y hxyz]

private theorem collapseAfter_succ_span (a x : ℕ) (h : a ≤ x) :
    ShortEdgeCutFibers.collapseAfter a (x + 1) = x := by
  rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (x + 1) (by omega)]
  omega

private theorem liftAfter_ne_a_span (a x : ℕ) (h : x ≠ a) :
    ShortEdgeCutFibers.liftAfter a x ≠ a := by
  by_cases hx : x ≤ a
  · simp [ShortEdgeCutFibers.liftAfter, hx]
    omega
  · simp [ShortEdgeCutFibers.liftAfter, hx]
    omega

private theorem liftAfter_ne_succ_span (a x : ℕ) (h : x ≠ a) :
    ShortEdgeCutFibers.liftAfter a x ≠ a + 1 := by
  by_cases hx : x ≤ a
  · simp [ShortEdgeCutFibers.liftAfter, hx]
    omega
  · simp [ShortEdgeCutFibers.liftAfter, hx]
    omega

private theorem parentTable_lift_interval
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    {x y : ℕ} (hxy : x < y) (hxa : x ≠ a) (hya : y ≠ a) :
    parentTable a ha t U (ShortEdgeCutFibers.liftAfter a x)
        (ShortEdgeCutFibers.liftAfter a y) =
      (if x < a ∧ a < y then kappa a ha t else 1) * U x y := by
  by_cases hcross : x < a ∧ a < y
  · have hx : ShortEdgeCutFibers.liftAfter a x = x := by
      simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hcross.1]
    have hy : ShortEdgeCutFibers.liftAfter a y = y + 1 := by
      simp [ShortEdgeCutFibers.liftAfter, Nat.not_le_of_gt hcross.2]
    have hcy := collapseAfter_succ_span a y (by omega)
    have hyplus : a + 1 < y + 1 := by omega
    simp [parentTable, hx, hy, hcross.1, hcross.2, hyplus, hcy, hxa, hya]
  · have hxle : x ≤ a ∨ a < x := by omega
    rcases hxle with hxle | hxgt
    · have hyle : y < a := by
        by_cases hya' : a < y
        · exact False.elim (hcross ⟨by omega, hya'⟩)
        · omega
      have hylele : y ≤ a := Nat.le_of_lt hyle
      have hyaPlus : y ≠ a + 1 := by omega
      have hyaFar : ¬ (a + 1 < y) := by omega
      have hyaCross : ¬ (a < y) := by omega
      have hx : ShortEdgeCutFibers.liftAfter a x = x := by
        simp [ShortEdgeCutFibers.liftAfter, hxle]
      have hy : ShortEdgeCutFibers.liftAfter a y = y := by
        simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt (by omega : y < a)]
      have hcx : ShortEdgeCutFibers.collapseAfter a
          (ShortEdgeCutFibers.liftAfter a x) = x := by
        rw [hx]
        exact ShortEdgeCutFibers.collapseAfter_eq_of_le a x hxle
      have hcy : ShortEdgeCutFibers.collapseAfter a
          (ShortEdgeCutFibers.liftAfter a y) = y := by
        rw [hy]
        exact ShortEdgeCutFibers.collapseAfter_eq_of_le a y hylele
      unfold parentTable
      simp [hx, hy, hcx, hcy, hyle, hxa, hya,
        hyaPlus, hyaFar, hyaCross,
        ShortEdgeCutFibers.collapseAfter_eq_of_le a x hxle,
        ShortEdgeCutFibers.collapseAfter_eq_of_le a y hylele]
    · have hygt : a < y := by omega
      have hx : ShortEdgeCutFibers.liftAfter a x = x + 1 := by
        simp [ShortEdgeCutFibers.liftAfter, Nat.not_le_of_gt hxgt]
      have hy : ShortEdgeCutFibers.liftAfter a y = y + 1 := by
        simp [ShortEdgeCutFibers.liftAfter, Nat.not_le_of_gt hygt]
      have hcx := collapseAfter_succ_span a x (by omega)
      have hcy := collapseAfter_succ_span a y (by omega)
      have hxne : x + 1 ≠ a := by omega
      have hyne : y + 1 ≠ a + 1 := by omega
      have hxnotlt : ¬ x + 1 < a := by omega
      rw [hx, hy]
      simp [parentTable, hcx, hcy, hxne, hyne, hxnotlt, hxgt, hcross]

private theorem branchProduct_strictSpan
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (v : List ℕ) :
    ∀ x : ℕ, (hSorted : (x :: v).Pairwise (· < ·)) →
      (hNoA : ∀ z ∈ x :: v, z ≠ a) → x < a →
      (∃ z ∈ v, a < z) →
      branchProduct (parentTable a ha t U)
          ((x :: v).map (ShortEdgeCutFibers.liftAfter a)) =
        kappa a ha t * branchProduct U (x :: v) := by
  induction v with
  | nil =>
      intro x _ _ _ hx
      simp at hx
  | cons y ys ih =>
      intro x hSorted hNoA hxlt hHigh
      have hCons := List.pairwise_cons.mp hSorted
      have hxy : x < y := hCons.1 y (by simp)
      have hTailSorted : (y :: ys).Pairwise (· < ·) := hCons.2
      have hya : y ≠ a := hNoA y (by simp)
      by_cases hay : a < y
      · have hTailAbove : ∀ z ∈ y :: ys, a < z := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hay
          · have hyz : y < z := (List.pairwise_cons.mp hTailSorted).1 z hz
            omega
        have hTailProduct :
            branchProduct (parentTable a ha t U)
                ((y :: ys).map (ShortEdgeCutFibers.liftAfter a)) =
              branchProduct U (y :: ys) := by
          rw [branchProduct_map]
          apply branchProduct_congr_span
          intro p q hpq
          have hmem := (adjacent_mem_iff hTailSorted).mp hpq
          have hp : a < p := hTailAbove p hmem.1
          have hq : a < q := hTailAbove q hmem.2.1
          have hnotp : ¬ p < a := by omega
          rw [parentTable_lift_interval a ha t U hmem.2.2.1 (by omega) (by omega)]
          simp [hp, hq, hnotp]
        have hFactor : parentTable a ha t U
            (ShortEdgeCutFibers.liftAfter a x)
            (ShortEdgeCutFibers.liftAfter a y) = kappa a ha t * U x y := by
          have hxyne : x ≠ a := hNoA x (by simp)
          rw [parentTable_lift_interval a ha t U hxy hxyne hya]
          simp [hxlt, hay]
        have hRec₁ : branchProduct (parentTable a ha t U)
            ((x :: y :: ys).map (ShortEdgeCutFibers.liftAfter a)) =
          parentTable a ha t U (ShortEdgeCutFibers.liftAfter a x)
            (ShortEdgeCutFibers.liftAfter a y) *
            branchProduct (parentTable a ha t U)
              ((y :: ys).map (ShortEdgeCutFibers.liftAfter a)) := by
          simp [branchProduct]
        have hRec₂ : branchProduct U (x :: y :: ys) =
            U x y * branchProduct U (y :: ys) := by simp [branchProduct]
        rw [hRec₁, hFactor, hTailProduct, hRec₂]
        ring
      · have hylta : y < a := by omega
        have hHighTail : ∃ z ∈ ys, a < z := by
          rcases hHigh with ⟨z, hz, hza⟩
          rcases List.mem_cons.mp hz with rfl | hz
          · omega
          · exact ⟨z, hz, hza⟩
        have hNoATail : ∀ z ∈ y :: ys, z ≠ a := by
          intro z hz
          exact hNoA z (List.mem_cons.mpr (Or.inr hz))
        have hTailProduct := ih y hTailSorted hNoATail hylta hHighTail
        have hFactor : parentTable a ha t U
            (ShortEdgeCutFibers.liftAfter a x)
            (ShortEdgeCutFibers.liftAfter a y) = U x y := by
          have hxyne : x ≠ a := hNoA x (by simp)
          rw [parentTable_lift_interval a ha t U hxy hxyne hya]
          have hnoty : ¬ a < y := by omega
          simp [hxlt, hylta, hnoty]
        have hRec₁ : branchProduct (parentTable a ha t U)
            ((x :: y :: ys).map (ShortEdgeCutFibers.liftAfter a)) =
          parentTable a ha t U (ShortEdgeCutFibers.liftAfter a x)
            (ShortEdgeCutFibers.liftAfter a y) *
            branchProduct (parentTable a ha t U)
              ((y :: ys).map (ShortEdgeCutFibers.liftAfter a)) := by
          simp [branchProduct]
        have hRec₂ : branchProduct U (x :: y :: ys) =
            U x y * branchProduct U (y :: ys) := by simp [branchProduct]
        rw [hRec₁, hFactor, hTailProduct, hRec₂]
        ring

theorem spanNoCoreCutContribution
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray)
    (η : Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j))
    (haNotS : a ∉ S) :
    cutContribution (D1 a t D)
        (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i j (ShortEdgeCutFibers.liftedCuts a S) =
      kappa a ha t *
        cutContribution (D0 a t D)
          (fun x k y => -η.value * H0 H x k y)
          U (ShortEdgeCutFibers.collapseAfter a i)
            (ShortEdgeCutFibers.collapseAfter a j) S := by
  classical
  have hci := ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hcj := ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)
  have hiLift : ShortEdgeCutFibers.liftAfter a
      (ShortEdgeCutFibers.collapseAfter a i) = i := by
    rw [hci]
    simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hiA]
  have hjCoreLt : a < ShortEdgeCutFibers.collapseAfter a j := by rw [hcj]; omega
  have hjLift : ShortEdgeCutFibers.liftAfter a
      (ShortEdgeCutFibers.collapseAfter a j) = j := by
    rw [hcj]
    change (if j - 1 ≤ a then j - 1 else (j - 1) + 1) = j
    rw [if_neg (by omega)]
    exact Nat.sub_add_cancel (by omega)
  have hijCore : ShortEdgeCutFibers.collapseAfter a i < ShortEdgeCutFibers.collapseAfter a j := by omega
  let v := cutVertices (ShortEdgeCutFibers.collapseAfter a i)
    (ShortEdgeCutFibers.collapseAfter a j) S
  have hvSorted : v.Pairwise (· < ·) := by
    apply cutVertices_pairwise hijCore
    simpa [hci] using hS
  have hvNoA : ∀ x ∈ v, x ≠ a := by
    intro x hx
    exact cutVertices_span_mem_ne_a a i j S hiA hBj haNotS hx
  have hHigh : ∃ x ∈ v.tail, a < x := by
    refine ⟨ShortEdgeCutFibers.collapseAfter a j, ?_, hjCoreLt⟩
    simp [v, cutVertices]
  have hSortedFull :
      (ShortEdgeCutFibers.collapseAfter a i :: v.tail).Pairwise (· < ·) := by
    change v.Pairwise (· < ·)
    exact hvSorted
  have hNoAFull : ∀ x ∈ ShortEdgeCutFibers.collapseAfter a i :: v.tail, x ≠ a := by
    intro x hx
    change x ∈ v at hx
    exact hvNoA x hx
  have hBranch := branchProduct_strictSpan a ha t U v.tail
    (ShortEdgeCutFibers.collapseAfter a i) hSortedFull hNoAFull (by rw [hci]; exact hiA) hHigh
  have hGateCore :
        gateProduct
            (fun x k y => D1 a t D (ShortEdgeCutFibers.liftAfter a x)
              (ShortEdgeCutFibers.liftAfter a k) (ShortEdgeCutFibers.liftAfter a y))
            (fun x k y => -η.value * H1 a t H
              (ShortEdgeCutFibers.liftAfter a x) (ShortEdgeCutFibers.liftAfter a k)
              (ShortEdgeCutFibers.liftAfter a y))
            (ShortEdgeCutFibers.collapseAfter a i)
            (ShortEdgeCutFibers.collapseAfter a j) v =
          gateProduct (D0 a t D) (fun x k y => -η.value * H0 H x k y)
            (ShortEdgeCutFibers.collapseAfter a i)
            (ShortEdgeCutFibers.collapseAfter a j) v := by
      apply gateProduct_congr_span
      · intro x k y hxyz
        have htrip := (triple_mem_iff hvSorted).mp hxyz
        have hleft := (adjacent_mem_iff hvSorted).mp htrip.1
        have hright := (adjacent_mem_iff hvSorted).mp htrip.2
        have hxn := hvNoA x hleft.1
        have hkn := hvNoA k hleft.2.1
        have hyn := hvNoA y hright.2.1
        simp [D1, D0, liftAfter_ne_a_span a x hxn,
          liftAfter_ne_a_span a k hkn, liftAfter_ne_a_span a y hyn,
          liftAfter_ne_succ_span a k hkn,
          ShortEdgeCutFibers.collapseAfter_liftAfter_of_ne a x hxn,
          ShortEdgeCutFibers.collapseAfter_liftAfter_of_ne a k hkn,
          ShortEdgeCutFibers.collapseAfter_liftAfter_of_ne a y hyn]
      · intro x k y hxyz
        have htrip := (triple_mem_iff hvSorted).mp hxyz
        have hleft := (adjacent_mem_iff hvSorted).mp htrip.1
        have hkn := hvNoA k hleft.2.1
        have hOuterI : ShortEdgeCutFibers.collapseAfter a i ≠ a := by rw [hci]; omega
        have hOuterJ : ShortEdgeCutFibers.collapseAfter a j ≠ a := by rw [hcj]; omega
        simp [H1, H0, liftAfter_ne_a_span a (ShortEdgeCutFibers.collapseAfter a i) hOuterI,
          liftAfter_ne_a_span a k hkn,
          liftAfter_ne_a_span a (ShortEdgeCutFibers.collapseAfter a j) hOuterJ,
          liftAfter_ne_succ_span a k hkn,
          ShortEdgeCutFibers.collapseAfter_liftAfter_of_ne a
            (ShortEdgeCutFibers.collapseAfter a i) hOuterI,
          ShortEdgeCutFibers.collapseAfter_liftAfter_of_ne a k hkn,
          ShortEdgeCutFibers.collapseAfter_liftAfter_of_ne a
            (ShortEdgeCutFibers.collapseAfter a j) hOuterJ]
  have hGate :
        gateProduct (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
            i j (cutVertices i j (ShortEdgeCutFibers.liftedCuts a S)) =
          gateProduct (D0 a t D) (fun x k y => -η.value * H0 H x k y)
            (ShortEdgeCutFibers.collapseAfter a i)
            (ShortEdgeCutFibers.collapseAfter a j) v := by
    rw [cutVertices_lifted_span a i j S hiA hBj]
    calc
      gateProduct (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
            i j (v.map (ShortEdgeCutFibers.liftAfter a)) =
          gateProduct (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
            (ShortEdgeCutFibers.liftAfter a (ShortEdgeCutFibers.collapseAfter a i))
            (ShortEdgeCutFibers.liftAfter a (ShortEdgeCutFibers.collapseAfter a j))
            (v.map (ShortEdgeCutFibers.liftAfter a)) := by rw [hiLift, hjLift]
      _ = gateProduct
            (fun x k y => D1 a t D (ShortEdgeCutFibers.liftAfter a x)
              (ShortEdgeCutFibers.liftAfter a k) (ShortEdgeCutFibers.liftAfter a y))
            (fun x k y => -η.value * H1 a t H
              (ShortEdgeCutFibers.liftAfter a x) (ShortEdgeCutFibers.liftAfter a k)
              (ShortEdgeCutFibers.liftAfter a y))
            (ShortEdgeCutFibers.collapseAfter a i)
            (ShortEdgeCutFibers.collapseAfter a j) v := by
              exact gateProduct_map (D1 a t D)
                (fun x k y => -η.value * H1 a t H x k y)
                (ShortEdgeCutFibers.liftAfter a)
                (ShortEdgeCutFibers.collapseAfter a i)
                (ShortEdgeCutFibers.collapseAfter a j) v
      _ = gateProduct (D0 a t D) (fun x k y => -η.value * H0 H x k y)
            (ShortEdgeCutFibers.collapseAfter a i)
            (ShortEdgeCutFibers.collapseAfter a j) v := hGateCore
  have hBranchExact :
        branchProduct (parentTable a ha t U)
            (cutVertices i j (ShortEdgeCutFibers.liftedCuts a S)) =
          kappa a ha t * branchProduct U v := by
    rw [cutVertices_lifted_span a i j S hiA hBj]
    simpa [v] using hBranch
  unfold cutContribution
  rw [hGate, hBranchExact]
  ring

theorem spanCandidate_cutAtB_word
    (a i j : ℕ) (hiA : i < a) (hBj : a + 1 < j)
    (S : Finset ℕ) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j)) :
    cutVertices i j (ShortEdgeCutFibers.spanCandidate a S
      ShortEdgeCutFibers.SpanLiftMode.cutAtB) =
      (cutVertices (ShortEdgeCutFibers.collapseAfter a i)
        (ShortEdgeCutFibers.collapseAfter a j) S).map
          (fun x => if x < a then x else x + 1) := by
  classical
  let f : ℕ → ℕ := fun x => if x < a then x else x + 1
  have hf : StrictMono f := by
    intro x y hxy
    by_cases hx : x < a <;> by_cases hy : y < a <;>
      simp [f, hx, hy] <;> omega
  have hAgree : ∀ x ∈ S.erase a, f x = ShortEdgeCutFibers.liftAfter a x := by
    intro x hx
    have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
    by_cases hxlt : x < a
    · simp [f, ShortEdgeCutFibers.liftAfter, hxlt, Nat.le_of_lt hxlt]
    · have hxgt : a < x := by omega
      simp [f, ShortEdgeCutFibers.liftAfter, hxlt, Nat.not_le_of_gt hxgt]
  have hEraseLift : (S.erase a).image (ShortEdgeCutFibers.liftAfter a) =
      (ShortEdgeCutFibers.liftedCuts a S).erase a := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨y, (Finset.mem_erase.mp hy).2, rfl⟩⟩
      intro hEq
      have hya : y = a := by
        apply (liftAfter_strictMono a).injective
        simpa [ShortEdgeCutFibers.liftAfter] using hEq
      exact (Finset.mem_erase.mp hy).1 hya
    · intro hx
      rcases Finset.mem_erase.mp hx with ⟨hxa, hxS⟩
      rcases Finset.mem_image.mp hxS with ⟨y, hyS, hxy⟩
      have hya : y ≠ a := by
        intro h
        subst y
        apply hxa
        simpa [ShortEdgeCutFibers.liftAfter] using hxy.symm
      exact Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hya, hyS⟩,
        hxy⟩
  have hSsplit : S.erase a ∪ {a} = S := by
    calc
      S.erase a ∪ {a} = insert a (S.erase a) := by ext x; simp [or_comm]
      _ = S := Finset.insert_erase haS
  have hT : ShortEdgeCutFibers.spanCandidate a S
      ShortEdgeCutFibers.SpanLiftMode.cutAtB = S.image f := by
    calc
      ShortEdgeCutFibers.spanCandidate a S ShortEdgeCutFibers.SpanLiftMode.cutAtB =
          (ShortEdgeCutFibers.liftedCuts a S).erase a ∪ {a + 1} := by
            ext x
            simp [ShortEdgeCutFibers.spanCandidate]
      _ = (S.erase a).image f ∪ {f a} := by
            rw [← hEraseLift]
            have hImage : (S.erase a).image (ShortEdgeCutFibers.liftAfter a) =
                (S.erase a).image f := by
              ext x
              simp only [Finset.mem_image]
              constructor
              · rintro ⟨y, hy, rfl⟩
                exact ⟨y, hy, hAgree y hy⟩
              · rintro ⟨y, hy, hxy⟩
                exact ⟨y, hy, (hAgree y hy).symm.trans hxy⟩
            rw [hImage]
            congr 1
            simp [f]
      _ = S.image f := by
            calc
              (S.erase a).image f ∪ {f a} = (S.erase a ∪ {a}).image f := by
                rw [Finset.image_union, Finset.image_singleton]
              _ = S.image f := by rw [hSsplit]
  have hValid := ShortEdgeCutFibers.spanCandidate_valid a i j S
    ShortEdgeCutFibers.SpanLiftMode.cutAtB hiA hBj haS hS
  have hiCore : ShortEdgeCutFibers.collapseAfter a i <
      ShortEdgeCutFibers.collapseAfter a j := by
    rw [ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega),
      ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hci : ShortEdgeCutFibers.collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hCoreJ : a < j - 1 := by omega
  have hfjEq : (if j - 1 < a then j - 1 else j - 1 + 1) = j := by
    rw [if_neg (by omega)]
    exact Nat.sub_add_cancel (by omega)
  have hfj : f (ShortEdgeCutFibers.collapseAfter a j) = j := by
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    change (if j - 1 < a then j - 1 else j - 1 + 1) = j
    exact hfjEq
  have hS' : S ⊆ Finset.Ioo (ShortEdgeCutFibers.collapseAfter a i)
      (ShortEdgeCutFibers.collapseAfter a j) := by simpa [hci] using hS
  have hCoreWord := cutVertices_pairwise hiCore hS'
  have hActual := cutVertices_pairwise (by omega) hValid.1
  have hTarget : ((cutVertices (ShortEdgeCutFibers.collapseAfter a i)
      (ShortEdgeCutFibers.collapseAfter a j) S).map f).Pairwise (· < ·) :=
    hCoreWord.map f (fun _ _ hxy => hf hxy)
  apply strictCutWord_eq_of_toFinset hActual hTarget
  rw [hT]
  ext x
  simp [List.mem_toFinset, cutVertices, f, hiA, hci,
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega),
    ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega), hfjEq]

set_option maxHeartbeats 1000000 in
theorem spanCandidate_cutAtBoth_word
    (a i j : ℕ) (hiA : i < a) (hBj : a + 1 < j)
    (S : Finset ℕ) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j)) :
    ∃ pre L R post,
      cutVertices (ShortEdgeCutFibers.collapseAfter a i)
          (ShortEdgeCutFibers.collapseAfter a j) S = pre ++ [L, a, R] ++ post ∧
        L < a ∧ a < R ∧
        cutVertices i j (ShortEdgeCutFibers.spanCandidate a S
          ShortEdgeCutFibers.SpanLiftMode.cutAtBoth) =
          pre.map (ShortEdgeCutFibers.liftAfter a) ++
            [L, a, a + 1, R + 1] ++ post.map (ShortEdgeCutFibers.liftAfter a) := by
  classical
  obtain ⟨pre, L, R, post, hword, hLa, haR⟩ :=
    coreWord_neighborhood a i j S haS hS hiA hBj
  let v := cutVertices (ShortEdgeCutFibers.collapseAfter a i)
    (ShortEdgeCutFibers.collapseAfter a j) S
  let P := pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L]
  let Q := post.map (ShortEdgeCutFibers.liftAfter a)
  let W := P ++ [a, a + 1, R + 1] ++ Q
  have hci : ShortEdgeCutFibers.collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hCoreIneq : ShortEdgeCutFibers.collapseAfter a i <
      ShortEdgeCutFibers.collapseAfter a j := by
    rw [hci, ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hCorePair : v.Pairwise (· < ·) := by
    apply cutVertices_pairwise hCoreIneq
    simpa [v, hci] using hS
  have hCorePair' : (pre ++ [L, a, R] ++ post).Pairwise (· < ·) := by
    simpa [v, hword] using hCorePair
  have hCorePairAssoc : (pre ++ ([L, a, R] ++ post)).Pairwise (· < ·) := by
    simpa [List.append_assoc] using hCorePair'
  have hPostA : ∀ y ∈ post, a < y := by
    intro y hy
    exact pairwise_rel_append (pre ++ [L, a, R]) post hCorePair' a (by simp) y hy
  have hPostR : ∀ y ∈ post, R < y := by
    intro y hy
    exact pairwise_rel_append (pre ++ [L, a, R]) post hCorePair' R (by simp) y hy
  have hPreLift : ∀ x ∈ pre, ShortEdgeCutFibers.liftAfter a x = x := by
    intro x hx
    have hxlt : x < a := by
      exact pairwise_rel_append pre ([L, a, R] ++ post) hCorePairAssoc x hx a (by simp)
    simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hxlt]
  have hPostLift : ∀ y ∈ post, ShortEdgeCutFibers.liftAfter a y = y + 1 := by
    intro y hy
    have hygt := hPostA y hy
    simp [ShortEdgeCutFibers.liftAfter, Nat.not_le_of_gt hygt]
  have hMapWord : v.map (ShortEdgeCutFibers.liftAfter a) =
      P ++ [a, R + 1] ++ Q := by
    change (cutVertices (ShortEdgeCutFibers.collapseAfter a i)
      (ShortEdgeCutFibers.collapseAfter a j) S).map _ = _
    rw [hword]
    simp [P, Q, List.map_append, hPreLift, hPostLift, Nat.le_of_lt hLa,
      ShortEdgeCutFibers.liftAfter, Nat.not_le_of_gt haR]
  have hMapPair : (v.map (ShortEdgeCutFibers.liftAfter a)).Pairwise (· < ·) :=
    hCorePair.map _ (fun _ _ hxy => liftAfter_strictMono a hxy)
  have hPSub : List.Sublist P (v.map (ShortEdgeCutFibers.liftAfter a)) := by
    rw [hMapWord]
    dsimp [P, Q]
    simpa [List.append_assoc] using
      (List.sublist_append_left (pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L])
        ([a, R + 1] ++ post.map (ShortEdgeCutFibers.liftAfter a)))
  have hPPair : P.Pairwise (· < ·) := List.Pairwise.sublist hPSub hMapPair
  have hQSub : List.Sublist Q (v.map (ShortEdgeCutFibers.liftAfter a)) := by
    rw [hMapWord]
    dsimp [P, Q]
    simpa [List.append_assoc] using List.sublist_append_right
      (pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L, a, R + 1])
      (post.map (ShortEdgeCutFibers.liftAfter a))
  have hQPair : Q.Pairwise (· < ·) := List.Pairwise.sublist hQSub hMapPair
  have hMapCross : ∀ x ∈ P, ∀ y ∈ ([a, R + 1] ++ Q), x < y := by
    intro x hx y hy
    have hMapPairWord : (P ++ ([a, R + 1] ++ Q)).Pairwise (· < ·) := by
      simpa [P, Q, hMapWord, List.append_assoc] using hMapPair
    exact pairwise_rel_append P ([a, R + 1] ++ Q) hMapPairWord x hx y hy
  have hCorePostA : ∀ y ∈ Q, a + 1 < y := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
    have haz := hPostA z hz
    have hzl := hPostLift z hz
    omega
  have hCorePostR : ∀ y ∈ Q, R + 1 < y := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
    have hRz := hPostR z hz
    have hzl := hPostLift z hz
    omega
  have hMiddle : ([a, a + 1, R + 1] ++ Q).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨?_, hQPair, ?_⟩
    · simp [List.pairwise_cons]
      omega
    · intro x hx y hy
      simp only [List.mem_cons, List.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | hx
      · exact Nat.lt_of_lt_of_le (by omega) (Nat.le_of_lt (hCorePostA y hy))
      · exact hCorePostA y hy
      · exact hCorePostR y hy
      · exact False.elim (by simp at hx)
  have hCross : ∀ x ∈ P, ∀ y ∈ ([a, a + 1, R + 1] ++ Q), x < y := by
    intro x hx y hy
    rcases List.mem_append.mp hy with hym | hyq
    · simp only [List.mem_cons, List.mem_singleton] at hym
      rcases hym with hya | hyap | hyR | hfalse
      · simpa [hya] using hMapCross x hx a (by simp)
      · have hxa := hMapCross x hx a (by simp)
        omega
      · simpa [hyR] using hMapCross x hx (R + 1) (by simp)
      · exact False.elim (by simp at hfalse)
    · exact hMapCross x hx y (List.mem_append.mpr (Or.inr hyq))
  have hWPair : W.Pairwise (· < ·) := by
    dsimp [W]
    have hPairNorm : (P ++ ([a, a + 1, R + 1] ++ Q)).Pairwise (· < ·) :=
      List.pairwise_append.mpr ⟨hPPair, hMiddle, hCross⟩
    simpa [List.append_assoc] using hPairNorm
  have hOnlyA : ShortEdgeCutFibers.spanCandidate a S
      ShortEdgeCutFibers.SpanLiftMode.cutAtA = ShortEdgeCutFibers.liftedCuts a S := by
    ext x
    have haLift : a ∈ ShortEdgeCutFibers.liftedCuts a S := by
      exact Finset.mem_image.mpr ⟨a, haS, by simp [ShortEdgeCutFibers.liftAfter]⟩
    by_cases hxa : x = a
    · subst x
      simp [ShortEdgeCutFibers.spanCandidate, haLift]
    · simp [ShortEdgeCutFibers.spanCandidate, hxa]
  have hBothSet : ShortEdgeCutFibers.spanCandidate a S
      ShortEdgeCutFibers.SpanLiftMode.cutAtBoth =
        ShortEdgeCutFibers.liftedCuts a S ∪ {a + 1} := by
    ext x
    have haLift : a ∈ ShortEdgeCutFibers.liftedCuts a S := by
      exact Finset.mem_image.mpr ⟨a, haS, by simp [ShortEdgeCutFibers.liftAfter]⟩
    by_cases hxa : x = a
    · subst x
      simp [ShortEdgeCutFibers.spanCandidate, haLift]
    · simp [ShortEdgeCutFibers.spanCandidate, hxa]
  have hActual := cutVertices_pairwise (by omega)
    (ShortEdgeCutFibers.spanCandidate_valid a i j S
      ShortEdgeCutFibers.SpanLiftMode.cutAtBoth hiA hBj haS hS).1
  refine ⟨pre, L, R, post, hword, hLa, haR, ?_⟩
  have hWPair' : (pre.map (ShortEdgeCutFibers.liftAfter a) ++
      [L, a, a + 1, R + 1] ++ post.map (ShortEdgeCutFibers.liftAfter a)).Pairwise (· < ·) := by
    simpa [W, P, Q, List.append_assoc] using hWPair
  apply strictCutWord_eq_of_toFinset hActual hWPair'
  have hTargetSet : W.toFinset = (v.map (ShortEdgeCutFibers.liftAfter a)).toFinset ∪ {a + 1} := by
    rw [hMapWord]
    ext x
    simp [W, P, Q, List.mem_toFinset, List.mem_map]
    aesop
  have hActualSet : (cutVertices i j
      (ShortEdgeCutFibers.spanCandidate a S
        ShortEdgeCutFibers.SpanLiftMode.cutAtBoth)).toFinset =
      (v.map (ShortEdgeCutFibers.liftAfter a)).toFinset ∪ {a + 1} := by
    rw [hBothSet]
    have hiLift : ShortEdgeCutFibers.liftAfter a i = i := by
      simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hiA]
    have hjcore : a < j - 1 := by omega
    have hjLift : ShortEdgeCutFibers.liftAfter a (j - 1) = j := by
      simp [ShortEdgeCutFibers.liftAfter, Nat.not_le_of_gt hjcore]
      omega
    ext x
    simp [cutVertices, v, ShortEdgeCutFibers.liftedCuts,
      List.mem_toFinset, Finset.mem_sort,
      ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega),
      ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega), hiLift, hjLift]
    aesop
  calc
    (cutVertices i j (ShortEdgeCutFibers.spanCandidate a S
      ShortEdgeCutFibers.SpanLiftMode.cutAtBoth)).toFinset =
        (v.map (ShortEdgeCutFibers.liftAfter a)).toFinset ∪ {a + 1} := hActualSet
    _ = W.toFinset := hTargetSet.symm
  simpa [W, P, Q, List.append_assoc]

end DirectGLSSW.ShortEdgeWeighted
