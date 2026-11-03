import DirectGLSSW.ShortEdgeCutFibers
import DirectGLSSW.CutRepresentation
import DirectGLSSW.CutIncidence

/-!
# Concrete finite-array short-edge algebra

This is a private implementation lane. It defines the proposed arrays and
parent table from the manuscript's finite algebra; it does not assert a
geometric realization or the full short-edge amplitude theorem.
-/

namespace DirectGLSSW.ShortEdgeWeighted
open scoped BigOperators

abbrev collapseAfter := ShortEdgeCutFibers.collapseAfter

/-- Gauge-fixed near data on the inserted edge. -/
def D0 (a : ℕ) (t : ℕ → Sign) (D : TripleArray) : TripleArray :=
  fun i k j => if k = a then (t i).value else D i k j

/-- The core far sign, viewed as a rational-valued triple array. -/
def H0 (H : ℕ → ℕ → ℕ → Sign) : TripleArray :=
  fun i k j => (H i k j).value

/-- Pulled-back near data on the parent after short-edge insertion. -/
def D1 (a : ℕ) (t : ℕ → Sign) (D : TripleArray) : TripleArray := fun i k j =>
  if k = a ∧ j = a + 1 then (t (collapseAfter a i)).value
  else if i = a ∧ k = a + 1 then (t (collapseAfter a j)).value
  else D0 a t D (collapseAfter a i) (collapseAfter a k) (collapseAfter a j)

/-- Pulled-back far data on the parent after short-edge insertion. -/
def H1 (a : ℕ) (t : ℕ → Sign) (H : ℕ → ℕ → ℕ → Sign) : TripleArray := fun i k j =>
  if k = a ∧ j = a + 1 then (t (collapseAfter a i)).value
  else if i = a ∧ k = a + 1 then (t (collapseAfter a j)).value
  else H0 H (collapseAfter a i) (collapseAfter a k) (collapseAfter a j)

def alpha (a : ℕ) (_ha : 0 < a) (t : ℕ → Sign) : ℚ := (t (a - 1)).value
def beta (a : ℕ) (t : ℕ → Sign) : ℚ := (t (a + 1)).value
def kappa (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) : ℚ :=
  (alpha a ha t + beta a t) / 2

/-- The proposed table is total, but its mathematical claims below use i<j. -/
def parentTable (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray) :
    IntervalArray := fun i j =>
  if i = a ∧ j = a + 1 then 1
  else if i = a ∧ a + 1 < j then
    ((beta a t - (t (collapseAfter a j)).value) / 2) * U a (collapseAfter a j)
  else if i < a ∧ j = a + 1 then
    ((alpha a ha t - (t i).value) / 2) * U i a
  else if i < a ∧ a + 1 < j then
    kappa a ha t * U i (collapseAfter a j)
  else U (collapseAfter a i) (collapseAfter a j)

/-- The marked/ordinary gate convention, parameterized by `η`. -/
def PhiEta (η : Sign) (D H : TripleArray) (b : IntervalArray)
    (i j : ℕ) : ℚ :=
  phi D (fun x k y => -η.value * H x k y) b i j

/-- Branch products commute with relabeling every vertex. -/
theorem branchProduct_map (b : IntervalArray) (f : ℕ → ℕ) :
    ∀ v : List ℕ,
    branchProduct b (v.map f) =
      branchProduct (fun x y => b (f x) (f y)) v := by
  intro v
  induction v with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      change b (f x) (f y) * branchProduct b (List.map f (y :: ys)) =
        b (f x) (f y) * branchProduct (fun x y => b (f x) (f y)) (y :: ys)
      rw [ih]

/-- Gate products commute with relabeling every vertex and both interval ends. -/
theorem gateProduct_map (D H : TripleArray) (f : ℕ → ℕ) (i j : ℕ) :
    ∀ v : List ℕ,
    gateProduct D H (f i) (f j) (v.map f) =
      gateProduct (fun x k y => D (f x) (f k) (f y))
        (fun x k y => H (f x) (f k) (f y)) i j v := by
  intro v
  induction v with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      cases ys with
      | nil => rfl
      | cons z zs =>
        change ((D (f x) (f y) (f z) - H (f i) (f y) (f j)) / 2) *
          gateProduct D H (f i) (f j) (List.map f (y :: z :: zs)) =
          ((D (f x) (f y) (f z) - H (f i) (f y) (f j)) / 2) *
          gateProduct (fun x k y => D (f x) (f k) (f y))
            (fun x k y => H (f x) (f k) (f y)) i j (y :: z :: zs)
        rw [ih]

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

/-- Sorted cut words commute with the successor relabeling. -/
theorem cutVertices_succ_image (i j : ℕ) (S : Finset ℕ) :
    cutVertices (i + 1) (j + 1) (S.image Nat.succ) =
      (cutVertices i j S).map Nat.succ := by
  simp [cutVertices, sort_image_succ, Nat.add_comm]

private theorem cutVertices_mem_bounds {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {x : ℕ}
    (hx : x ∈ cutVertices i j S) : i ≤ x ∧ x ≤ j := by
  change x ∈ i :: (S.sort (· ≤ ·) ++ [j]) at hx
  simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hx
  rcases hx with hxi | hx
  · subst x
    exact ⟨le_rfl, Nat.le_of_lt hij⟩
  · rcases hx with hxS | hxj
    · have hxS : x ∈ S := (Finset.mem_sort (· ≤ ·)).mp hxS
      have h := Finset.mem_Ioo.mp (hS hxS)
      omega
    · simp at hxj
      subst x
      exact ⟨Nat.le_of_lt hij, le_rfl⟩

private theorem collapseAfter_succ (a x : ℕ) (h : a ≤ x) :
    collapseAfter a (x + 1) = x := by
  have hlt : a < x + 1 := by omega
  calc
    collapseAfter a (x + 1) = (x + 1) - 1 :=
      ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (x + 1) hlt
    _ = x := by omega

private theorem branchProduct_congr {b₁ b₂ : IntervalArray} {v : List ℕ}
    (h : ∀ x y, (x, y) ∈ v.zip v.tail → b₁ x y = b₂ x y) :
    branchProduct b₁ v = branchProduct b₂ v := by
  unfold branchProduct
  congr 1
  apply List.map_congr_left
  rintro ⟨x, y⟩ hxy
  exact h x y hxy

private theorem gateProduct_congr {D₁ D₂ H₁ H₂ : TripleArray}
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

private theorem contribution_before
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (η : Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} {S : Finset ℕ} (hij : i < j) (hj : j ≤ a)
    (hS : S ⊆ Finset.Ioo i j) :
    cutContribution (D1 a t D)
      (fun x k y => -η.value * H1 a t H x k y)
      (parentTable a ha t U) i j S =
    cutContribution (D0 a t D)
      (fun x k y => -η.value * H0 H x k y)
      U i j S := by
  have hword := cutVertices_pairwise hij hS
  unfold cutContribution
  congr 1
  · apply gateProduct_congr
    · intro x k y hxyz
      have hxy := (triple_mem_iff hword).mp hxyz
      have hleft := (adjacent_mem_iff hword).mp hxy.1
      have hright := (adjacent_mem_iff hword).mp hxy.2
      have hx := cutVertices_mem_bounds hij hS hleft.1
      have hy := cutVertices_mem_bounds hij hS hright.2.1
      have hklt : k < a := by
        have hk := cutVertices_mem_bounds hij hS hleft.2.1
        omega
      have hxlt : x < a := by
        have hxk := (adjacent_mem_iff hword).mp hxy.1
        omega
      have hcx : collapseAfter a x = x :=
        ShortEdgeCutFibers.collapseAfter_eq_of_le a x (by omega)
      have hck : collapseAfter a k = k :=
        ShortEdgeCutFibers.collapseAfter_eq_of_le a k (by omega)
      have hcy : collapseAfter a y = y :=
        ShortEdgeCutFibers.collapseAfter_eq_of_le a y (by omega)
      have hki : k ≠ a := by omega
      have hxi : x ≠ a := by omega
      simp [D1, H1, D0, H0, hcx, hck, hcy, hki, hxi]
    · intro x k y hxyz
      have hxy := (triple_mem_iff hword).mp hxyz
      have hleft := (adjacent_mem_iff hword).mp hxy.1
      have hright := (adjacent_mem_iff hword).mp hxy.2
      have hxk := cutVertices_mem_bounds hij hS hleft.1
      have hkj := cutVertices_mem_bounds hij hS hright.2.1
      have hklt : k < a := by omega
      have hilt : i < a := by omega
      have hki : k ≠ a := by omega
      have hii : i ≠ a := by omega
      simp [H1, H0, hilt, hklt, hii, hki,
        ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega),
        ShortEdgeCutFibers.collapseAfter_eq_of_le a k (by omega),
        ShortEdgeCutFibers.collapseAfter_eq_of_le a j (by omega)]
  · apply branchProduct_congr
    intro x y hxy
    have hb := (adjacent_mem_iff hword).mp hxy
    have hx := cutVertices_mem_bounds hij hS hb.1
    have hy := cutVertices_mem_bounds hij hS hb.2.1
    have hxa : x < a := by omega
    have hya : y ≤ a := by omega
    have hxi : x ≠ a := by omega
    have hyi : y ≠ a + 1 := by omega
    have hys : ¬ a + 1 < y := by omega
    simp [parentTable, hxi, hxa, hyi, hys,
      ShortEdgeCutFibers.collapseAfter_eq_of_le a x (by omega),
      ShortEdgeCutFibers.collapseAfter_eq_of_le a y (by omega)]

private theorem contribution_after
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (η : Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} (hij : i < j) (hi : a ≤ i)
    {S : Finset ℕ} (hS : S ⊆ Finset.Ioo i j) :
    cutContribution (D1 a t D)
      (fun x k y => -η.value * H1 a t H x k y)
      (parentTable a ha t U) (i + 1) (j + 1) (S.image Nat.succ) =
    cutContribution (D0 a t D)
      (fun x k y => -η.value * H0 H x k y)
      U i j S := by
  have hword := cutVertices_pairwise hij hS
  unfold cutContribution
  rw [cutVertices_succ_image]
  change gateProduct (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
      (Nat.succ i) (Nat.succ j) ((cutVertices i j S).map Nat.succ) *
    branchProduct (parentTable a ha t U) ((cutVertices i j S).map Nat.succ) = _
  rw [gateProduct_map, branchProduct_map]
  congr 1
  · apply gateProduct_congr
    · intro x k y hxyz
      have hxy := (triple_mem_iff hword).mp hxyz
      have hleft := (adjacent_mem_iff hword).mp hxy.1
      have hright := (adjacent_mem_iff hword).mp hxy.2
      have hx := cutVertices_mem_bounds hij hS hleft.1
      have hk := cutVertices_mem_bounds hij hS hleft.2.1
      have hy := cutVertices_mem_bounds hij hS hright.2.1
      have hka : k + 1 ≠ a := by omega
      have hxa : x + 1 ≠ a := by omega
      have hcx := collapseAfter_succ a x (by omega)
      have hck := collapseAfter_succ a k (by omega)
      have hcy := collapseAfter_succ a y (by omega)
      simp [D1, D0, hka, hxa, hcx, hck, hcy]
    · intro x k y hxyz
      have hxy := (triple_mem_iff hword).mp hxyz
      have hleft := (adjacent_mem_iff hword).mp hxy.1
      have hx := cutVertices_mem_bounds hij hS hleft.1
      have hk := cutVertices_mem_bounds hij hS hleft.2.1
      have hy := cutVertices_mem_bounds hij hS ((adjacent_mem_iff hword).mp hxy.2).2.1
      have hka : k + 1 ≠ a := by omega
      have hxa : x + 1 ≠ a := by omega
      have hIa : i + 1 ≠ a := by omega
      have hcx := collapseAfter_succ a x (by omega)
      have hck := collapseAfter_succ a k (by omega)
      have hcy := collapseAfter_succ a y (by omega)
      have hci := collapseAfter_succ a i hi
      have hcj := collapseAfter_succ a j (by omega)
      simp [H1, H0, hka, hIa, hcx, hck, hcy, hci, hcj]
  · apply branchProduct_congr
    intro x y hxy
    have hb := (adjacent_mem_iff hword).mp hxy
    have hx := cutVertices_mem_bounds hij hS hb.1
    have hy := cutVertices_mem_bounds hij hS hb.2.1
    have hxa : x + 1 ≠ a := by omega
    have hlt : ¬ x + 1 < a := by omega
    have hcx := collapseAfter_succ a x (by omega)
    have hcy := collapseAfter_succ a y (by omega)
    simp [parentTable, hxa, hlt, hcx, hcy]

/-- Strictly before the inserted pair, every cut contribution is unchanged. -/
theorem awayPhi_before
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (η : Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} (hij : i < j) (hj : j ≤ a) :
    PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U) i j =
      PhiEta η (D0 a t D) (H0 H) U i j := by
  unfold PhiEta phi
  apply Finset.sum_congr rfl
  intro S hS
  exact contribution_before a ha t U η D H hij hj (Finset.mem_powerset.mp hS)

/-- Above the inserted pair, successor relabeling gives the strict-away identity. -/
theorem awayPhi_after
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (η : Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} (hij : i < j) (hi : a ≤ i) :
    PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U) (i + 1) (j + 1) =
      PhiEta η (D0 a t D) (H0 H) U i j := by
  classical
  let P := Finset.Ioo (i + 1) (j + 1)
  let Q := Finset.Ioo i j
  have hpred : ∀ T ∈ P.powerset, (T.image Nat.pred) ∈ Q.powerset := by
    intro T hT
    apply Finset.mem_powerset.mpr
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hyI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hy)
    simp only [P, Finset.mem_Ioo] at hyI ⊢
    have hypos : 0 < y := by omega
    have hp : Nat.pred y + 1 = y := Nat.succ_pred_eq_of_pos hypos
    rw [← hp] at hyI
    change Nat.pred y ∈ Finset.Ioo i j
    simp only [Finset.mem_Ioo]
    constructor
    · have hlo : i + 1 < Nat.pred y + 1 := by simpa using hyI.1
      omega
    · have hhi : Nat.pred y + 1 < j + 1 := by simpa using hyI.2
      omega
  have hsucc : ∀ S ∈ Q.powerset, (S.image Nat.succ) ∈ P.powerset := by
    intro S hS
    apply Finset.mem_powerset.mpr
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hyI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hS hy)
    simp only [P, Finset.mem_Ioo]
    omega
  have hleft : ∀ (T : Finset ℕ), T ∈ P.powerset →
      (T.image Nat.pred).image Nat.succ = T := by
    intro T hT
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
      have hzI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hz)
      have hzpos : 0 < z := by simp only [P, Finset.mem_Ioo] at hzI; omega
      have hzp : Nat.succ (Nat.pred z) = z := Nat.succ_pred_eq_of_pos hzpos
      have hyz : Nat.succ y = z := by
        calc
          Nat.succ y = Nat.succ (Nat.pred z) := by rw [hzy]
          _ = z := hzp
      change Nat.succ y ∈ T
      rw [hyz]
      exact hz
    · intro hx
      have hxI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hx)
      have hxpos : 0 < x := by simp only [P, Finset.mem_Ioo] at hxI; omega
      refine ⟨Nat.pred x, ⟨x, hx, rfl⟩, ?_⟩
      exact Nat.succ_pred_eq_of_pos hxpos
  have hright : ∀ (S : Finset ℕ), S ∈ Q.powerset →
      (S.image Nat.succ).image Nat.pred = S := by
    intro S hS
    ext x
    simp
  unfold PhiEta phi
  change (∑ T ∈ P.powerset,
      cutContribution (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) (i + 1) (j + 1) T) =
    ∑ S ∈ Q.powerset,
      cutContribution (D0 a t D) (fun x k y => -η.value * H0 H x k y) U i j S
  refine Finset.sum_bij'
    (fun T _ => T.image Nat.pred)
    (fun S _ => S.image Nat.succ) ?_ ?_ ?_ ?_ ?_
  · exact hpred
  · exact hsucc
  · exact hleft
  · exact hright
  · intro T hT
    have hS : (T.image Nat.pred) ⊆ Finset.Ioo i j :=
      Finset.mem_powerset.mp (hpred T hT)
    have hT_eq : T = (T.image Nat.pred).image Nat.succ := (hleft T hT).symm
    conv_lhs => rw [hT_eq]
    exact contribution_after a ha t U η D H hij hi hS

/-- The exact strict-away identity on either side of the inserted pair. -/
theorem awayPhi
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (η : Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} (hij : i < j) (haway : j ≤ a ∨ a + 1 ≤ i) :
    PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U) i j =
      PhiEta η (D0 a t D) (H0 H) U (collapseAfter a i) (collapseAfter a j) := by
  rcases haway with hbefore | hafter
  · have hci := ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
    have hcj := ShortEdgeCutFibers.collapseAfter_eq_of_le a j hbefore
    simpa [hci, hcj] using awayPhi_before a ha t U η D H hij hbefore
  · have hi0 : a ≤ i - 1 := by omega
    have hij0 : i - 1 < j - 1 := by omega
    have hI : i - 1 + 1 = i := by omega
    have hJ : j - 1 + 1 = j := by omega
    have hci : collapseAfter a i = i - 1 :=
      ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a i (by omega)
    have hcj : collapseAfter a j = j - 1 :=
      ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)
    calc
      PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U) i j =
          PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U)
            (i - 1 + 1) (j - 1 + 1) := by rw [hI, hJ]
      _ = PhiEta η (D0 a t D) (H0 H) U (i - 1) (j - 1) :=
        awayPhi_after a ha t U η D H hij0 hi0
      _ = PhiEta η (D0 a t D) (H0 H) U
            (collapseAfter a i) (collapseAfter a j) := by rw [hci, hcj]

/-- The adjacent inserted pair has its unary weight, independent of the arrays. -/
theorem shortpairPhi1 (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (η : Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U) a (a + 1) = 1 := by
  unfold PhiEta phi
  have hIoo : Finset.Ioo a (a + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    simp only [Finset.mem_Ioo] at hx
    omega
  rw [hIoo]
  simp [parentTable]

end DirectGLSSW.ShortEdgeWeighted
