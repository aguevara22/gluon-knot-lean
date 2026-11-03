import DirectGLSSW.IntervalCurrent

namespace DirectGLSSW.ShortEdgeCutFibers
open DirectGLSSW

def collapseAfter (a i : ℕ) : ℕ := if i ≤ a then i else i - 1

def liftAfter (a i : ℕ) : ℕ := if i ≤ a then i else i + 1

def containsIndex (x i k j : ℕ) : Prop := i = x ∨ k = x ∨ j = x

def avoidsInsertedPair (a i k j : ℕ) : Prop :=
  ¬ (containsIndex a i k j ∧ containsIndex (a + 1) i k j)

def collapsedInteriorCuts (a i j : ℕ) (T : Finset ℕ) : Finset ℕ :=
  ((T.image (collapseAfter a)).erase (collapseAfter a i)).erase (collapseAfter a j)

def liftedCuts (a : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (liftAfter a)

def ShortEdgeCutFiber (a i j : ℕ) (S : Finset ℕ) :=
  {T : Finset ℕ // T ⊆ Finset.Ioo i j ∧ collapsedInteriorCuts a i j T = S}

inductive EndpointLiftMode where
  | unsplit
  | shortLeaf
  deriving DecidableEq

inductive SpanLiftMode where
  | cutAtA
  | cutAtB
  | cutAtBoth
  deriving DecidableEq

def leftEndpointCandidate (a : ℕ) (S : Finset ℕ) (m : EndpointLiftMode) : Finset ℕ :=
  liftedCuts a S ∪ if m = EndpointLiftMode.shortLeaf then {a + 1} else ∅

def rightEndpointCandidate (a : ℕ) (S : Finset ℕ) (m : EndpointLiftMode) : Finset ℕ :=
  liftedCuts a S ∪ if m = EndpointLiftMode.shortLeaf then {a} else ∅

theorem collapseAfter_eq_of_le (a i : ℕ) (h : i ≤ a) :
    collapseAfter a i = i := by
  simp [collapseAfter, h]

theorem collapseAfter_eq_sub_one_of_lt (a i : ℕ) (h : a < i) :
    collapseAfter a i = i - 1 := by
  simp [collapseAfter, Nat.not_le.mpr h]

theorem collapseAfter_liftAfter_of_ne (a i : ℕ) (h : i ≠ a) :
    collapseAfter a (liftAfter a i) = i := by
  by_cases hi : i ≤ a
  · simp [liftAfter, collapseAfter, hi]
  · have hgt : a < i := by omega
    simp [liftAfter, collapseAfter, Nat.not_le.mpr hgt]
    omega

theorem liftAfter_collapseAfter_of_ne_succ (a i : ℕ) (h : i ≠ a + 1) :
    liftAfter a (collapseAfter a i) = i := by
  by_cases hle : i ≤ a
  · simp [collapseAfter, liftAfter, hle]
  · have hgt : a < i := by omega
    by_cases hs : i = a + 1
    · exact False.elim (h hs)
    · have hlt : a < i - 1 := by omega
      simp [collapseAfter, liftAfter, Nat.not_le.mpr hgt, Nat.not_le.mpr hlt]
      omega

theorem collapseAfter_triple_order
    (a i k j : ℕ) (hik : i < k) (hkj : k < j)
    (hAvoid : avoidsInsertedPair a i k j) :
    collapseAfter a i < collapseAfter a k ∧
      collapseAfter a k < collapseAfter a j := by
  simp only [avoidsInsertedPair, containsIndex] at hAvoid
  constructor
  · by_cases hi : i ≤ a
    · by_cases hk : k ≤ a
      · simp [collapseAfter, hi, hk]
        omega
      · have hneq : ¬ (i = a ∧ k = a + 1) := by
          intro h
          apply hAvoid
          constructor
          · exact Or.inl h.1
          · exact Or.inr (Or.inl h.2)
        simp [collapseAfter, hi, hk]
        omega
    · have hk : ¬ k ≤ a := by omega
      simp [collapseAfter, hi, hk]
      omega
  · by_cases hk : k ≤ a
    · by_cases hj : j ≤ a
      · simp [collapseAfter, hk, hj]
        omega
      · have hneq : ¬ (k = a ∧ j = a + 1) := by
          intro h
          apply hAvoid
          constructor
          · exact Or.inr (Or.inl h.1)
          · exact Or.inr (Or.inr h.2)
        simp [collapseAfter, hk, hj]
        omega
    · have hj : ¬ j ≤ a := by omega
      simp [collapseAfter, hk, hj]
      omega

theorem leftEndpoint_fiber_decomposition
    (a j : ℕ) (S T : Finset ℕ)
    (hABj : a + 1 < j)
    (hS : S ⊆ Finset.Ioo a (collapseAfter a j))
    (hT : T ⊆ Finset.Ioo a j)
    (hCuts : collapsedInteriorCuts a a j T = S) :
    T = liftedCuts a S ∪ if a + 1 ∈ T then {a + 1} else ∅ := by
  ext x
  constructor
  · intro hxT
    by_cases hspecial : x = a + 1
    · subst x
      simp [hxT]
    · have hxI := hT hxT
      simp only [Finset.mem_Ioo] at hxI
      have hax : a + 1 < x := by
        omega
      have hy := collapseAfter_eq_sub_one_of_lt a x (by omega)
      have hya : collapseAfter a x ≠ a := by omega
      have hyj : collapseAfter a x ≠ collapseAfter a j := by
        rw [collapseAfter_eq_sub_one_of_lt a j (by omega), hy]
        omega
      have hyS : collapseAfter a x ∈ S := by
        rw [← hCuts]
        change collapseAfter a x ∈
          ((T.image (collapseAfter a)).erase (collapseAfter a a)).erase (collapseAfter a j)
        apply Finset.mem_erase.mpr
        refine ⟨hyj, ?_⟩
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_image.mpr ⟨x, hxT, rfl⟩⟩
        simpa [collapseAfter] using hya
      have hback := liftAfter_collapseAfter_of_ne_succ a x hspecial
      apply Finset.mem_union.mpr
      left
      change x ∈ S.image (liftAfter a)
      exact Finset.mem_image.mpr ⟨collapseAfter a x, hyS, hback⟩
  · intro hx
    rcases Finset.mem_union.mp hx with hxbase | hxspecial
    · rcases Finset.mem_image.mp hxbase with ⟨y, hyS, hxy⟩
      subst x
      have hyI := hS hyS
      simp only [Finset.mem_Ioo] at hyI
      have hya : y ≠ collapseAfter a a := by
        rw [collapseAfter_eq_of_le a a (by omega)]
        omega
      have hyj : y ≠ collapseAfter a j := by
        have hj := collapseAfter_eq_sub_one_of_lt a j (by omega)
        rw [hj]
        omega
      have hyImage : y ∈ T.image (collapseAfter a) := by
        have hy1 : y ∈ (T.image (collapseAfter a)).erase (collapseAfter a a) := by
          rw [← hCuts] at hyS
          exact (Finset.mem_erase.mp hyS).2
        exact (Finset.mem_erase.mp hy1).2
      rcases Finset.mem_image.mp hyImage with ⟨z, hzT, hyz⟩
      have hzNe : z ≠ a + 1 := by
        intro hz
        subst z
        have : collapseAfter a (a + 1) = a := by
          simp [collapseAfter]
        rw [this] at hyz
        omega
      have hzback := liftAfter_collapseAfter_of_ne_succ a z hzNe
      have : liftAfter a y = z := by simpa [hyz] using hzback
      rw [this]
      exact hzT
    · by_cases hmem : a + 1 ∈ T
      · have hEq : x = a + 1 := by simpa [hmem] using hxspecial
        rw [hEq]
        exact hmem
      · simp [hmem] at hxspecial

theorem rightEndpoint_fiber_decomposition
    (a i : ℕ) (S T : Finset ℕ)
    (hiA : i < a)
    (hS : S ⊆ Finset.Ioo (collapseAfter a i) a)
    (hT : T ⊆ Finset.Ioo i (a + 1))
    (hCuts : collapsedInteriorCuts a i (a + 1) T = S) :
    T = liftedCuts a S ∪ if a ∈ T then {a} else ∅ := by
  ext x
  constructor
  · intro hxT
    by_cases hspecial : x = a
    · subst x
      simp [hxT]
    · have hxI := hT hxT
      simp only [Finset.mem_Ioo] at hxI
      have hxa : x < a := by omega
      have hy := collapseAfter_eq_of_le a x (by omega)
      have hyi : collapseAfter a x ≠ collapseAfter a i := by
        rw [collapseAfter_eq_of_le a i (by omega), hy]
        omega
      have hya : collapseAfter a x ≠ collapseAfter a (a + 1) := by
        have ha : collapseAfter a (a + 1) = a := by
          simp [collapseAfter]
        rw [hy, ha]
        omega
      have hyS : collapseAfter a x ∈ S := by
        rw [← hCuts]
        change collapseAfter a x ∈
          ((T.image (collapseAfter a)).erase (collapseAfter a i)).erase
            (collapseAfter a (a + 1))
        apply Finset.mem_erase.mpr
        refine ⟨hya, ?_⟩
        apply Finset.mem_erase.mpr
        refine ⟨hyi, Finset.mem_image.mpr ⟨x, hxT, rfl⟩⟩
      have hLift : liftAfter a (collapseAfter a x) = x := by
        simpa [hy] using (show liftAfter a x = x by simp [liftAfter, Nat.le_of_lt (by omega : x < a)])
      apply Finset.mem_union.mpr
      left
      change x ∈ S.image (liftAfter a)
      exact Finset.mem_image.mpr ⟨collapseAfter a x, hyS, hLift⟩
  · intro hx
    rcases Finset.mem_union.mp hx with hxbase | hxspecial
    · rcases Finset.mem_image.mp hxbase with ⟨y, hyS, hxy⟩
      subst x
      have hyI := hS hyS
      simp only [Finset.mem_Ioo] at hyI
      have hyi : y ≠ collapseAfter a i := by omega
      have hya : y ≠ collapseAfter a (a + 1) := by
        have ha : collapseAfter a (a + 1) = a := by
          simp [collapseAfter]
        rw [ha]
        omega
      have hyImage : y ∈ T.image (collapseAfter a) := by
        have hy1 : y ∈ (T.image (collapseAfter a)).erase (collapseAfter a i) := by
          rw [← hCuts] at hyS
          exact (Finset.mem_erase.mp hyS).2
        exact (Finset.mem_erase.mp hy1).2
      rcases Finset.mem_image.mp hyImage with ⟨z, hzT, hyz⟩
      have hzNe : z ≠ a + 1 := by
        intro hz
        subst z
        have ha : collapseAfter a (a + 1) = a := by simp [collapseAfter]
        rw [ha] at hyz
        omega
      have hzback := liftAfter_collapseAfter_of_ne_succ a z hzNe
      have hzEq : liftAfter a y = z := by simpa [hyz] using hzback
      have hyLift : liftAfter a y = y := by
        simp [liftAfter, Nat.le_of_lt hyI.2]
      have hzY : z = y := by
        calc
          z = liftAfter a y := hzEq.symm
          _ = y := hyLift
      rw [hyLift, ← hzY]
      exact hzT
    · by_cases hmem : a ∈ T
      · have hEq : x = a := by simpa [hmem] using hxspecial
        rw [hEq]
        exact hmem
      · simp [hmem] at hxspecial

theorem away_fiber_decomposition
    (a i j : ℕ) (S T : Finset ℕ)
    (hij : i < j) (hAway : j ≤ a ∨ a + 1 ≤ i)
    (hS : S ⊆ Finset.Ioo (collapseAfter a i) (collapseAfter a j))
    (hT : T ⊆ Finset.Ioo i j)
    (hCuts : collapsedInteriorCuts a i j T = S) :
    T = liftedCuts a S := by
  ext x
  constructor
  · intro hxT
    have hxI := hT hxT
    simp only [Finset.mem_Ioo] at hxI
    have hnotpair : x ≠ a + 1 := by
      rcases hAway with hbefore | hafter
      · omega
      · omega
    have hback := liftAfter_collapseAfter_of_ne_succ a x hnotpair
    have hyS : collapseAfter a x ∈ S := by
      rw [← hCuts]
      have hnoti : collapseAfter a x ≠ collapseAfter a i := by
        rcases hAway with hbefore | hafter
        · have hxi : i ≤ a := by omega
          have hxle : x ≤ a := by omega
          simp [collapseAfter, hxi, hxle]
          omega
        · have hxi : a < i := by omega
          have hxgt : a < x := by omega
          simp [collapseAfter, Nat.not_le_of_gt hxi, Nat.not_le_of_gt hxgt]
          omega
      have hnotj : collapseAfter a x ≠ collapseAfter a j := by
        rcases hAway with hbefore | hafter
        · have hxle : x ≤ a := by omega
          have hjle : j ≤ a := hbefore
          simp [collapseAfter, hxle, hjle]
          omega
        · have hxgt : a < x := by omega
          have hjgt : a < j := by omega
          simp [collapseAfter, Nat.not_le_of_gt hxgt, Nat.not_le_of_gt hjgt]
          omega
      change collapseAfter a x ∈
        ((T.image (collapseAfter a)).erase (collapseAfter a i)).erase (collapseAfter a j)
      apply Finset.mem_erase.mpr
      refine ⟨hnotj, ?_⟩
      apply Finset.mem_erase.mpr
      refine ⟨hnoti, Finset.mem_image.mpr ⟨x, hxT, rfl⟩⟩
    change x ∈ S.image (liftAfter a)
    exact Finset.mem_image.mpr ⟨collapseAfter a x, hyS, hback⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hyS, hxy⟩
    have hyI := hS hyS
    simp only [Finset.mem_Ioo] at hyI
    have hnoti : y ≠ collapseAfter a i := by omega
    have hnotj : y ≠ collapseAfter a j := by omega
    have hyImage : y ∈ T.image (collapseAfter a) := by
      have hy1 : y ∈ (T.image (collapseAfter a)).erase (collapseAfter a i) := by
        rw [← hCuts] at hyS
        exact (Finset.mem_erase.mp hyS).2
      exact (Finset.mem_erase.mp hy1).2
    rcases Finset.mem_image.mp hyImage with ⟨z, hzT, hyz⟩
    have hya : y ≠ a := by
      rcases hAway with hbefore | hafter
      · have hj : collapseAfter a j = j := collapseAfter_eq_of_le a j (by omega)
        rw [hj] at hyI
        omega
      · have hi : collapseAfter a i = i - 1 := collapseAfter_eq_sub_one_of_lt a i (by omega)
        rw [hi] at hyI
        omega
    have hzNe : z ≠ a + 1 := by
      intro hz
      subst z
      have ha : collapseAfter a (a + 1) = a := by
        simp [collapseAfter]
      rw [ha] at hyz
      omega
    have hzback := liftAfter_collapseAfter_of_ne_succ a z hzNe
    have hzy : z = liftAfter a y := by simpa [hyz] using hzback.symm
    have hxz : x = z := by
      calc
        x = liftAfter a y := hxy.symm
        _ = z := hzy.symm
    rw [hxz]
    exact hzT

theorem leftEndpointCandidate_valid
    (a j : ℕ) (S : Finset ℕ) (m : EndpointLiftMode)
    (hABj : a + 1 < j)
    (hS : S ⊆ Finset.Ioo a (collapseAfter a j)) :
    leftEndpointCandidate a S m ⊆ Finset.Ioo a j ∧
      collapsedInteriorCuts a a j (leftEndpointCandidate a S m) = S := by
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hxbase | hxspecial
    · rcases Finset.mem_image.mp hxbase with ⟨y, hyS, rfl⟩
      have hyI := hS hyS
      simp only [Finset.mem_Ioo] at hyI
      have hj := collapseAfter_eq_sub_one_of_lt a j (by omega)
      simp only [Finset.mem_Ioo]
      simp [liftAfter, Nat.not_le_of_gt hyI.1]
      omega
    · by_cases hm : m = EndpointLiftMode.shortLeaf
      · simp [hm] at hxspecial
        simp only [Finset.mem_Ioo]
        omega
      · simp [hm] at hxspecial
  · have hj : collapseAfter a j = j - 1 := by
      exact collapseAfter_eq_sub_one_of_lt a j (by omega)
    have hja : ¬ j ≤ a := by omega
    have hcollapse : (liftedCuts a S).image (collapseAfter a) = S := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
        rcases Finset.mem_image.mp hx with ⟨z, hzS, hxz⟩
        subst x
        have hzI := hS hzS
        simp only [Finset.mem_Ioo] at hzI
        have hback := collapseAfter_liftAfter_of_ne a z (by omega)
        have : z = y := by simpa [hback] using hxy
        simpa [this] using hzS
      · intro hyS
        have hyI := hS hyS
        simp only [Finset.mem_Ioo] at hyI
        have hback := collapseAfter_liftAfter_of_ne a y (by omega)
        refine Finset.mem_image.mpr ⟨liftAfter a y, Finset.mem_image.mpr ⟨y, hyS, rfl⟩, ?_⟩
        simpa [hback]
    have haS : a ∉ S := by
      intro ha
      have h := hS ha
      simp only [Finset.mem_Ioo] at h
      omega
    have hjS : j - 1 ∉ S := by
      intro hmem
      have h := hS hmem
      simp only [Finset.mem_Ioo] at h
      omega
    cases m with
    | unsplit =>
        simp [leftEndpointCandidate, collapsedInteriorCuts, hcollapse, hja, haS, hjS, collapseAfter]
    | shortLeaf =>
        have hpair : ({a + 1} : Finset ℕ).image (collapseAfter a) = {a} := by
          ext y
          simp [collapseAfter]
        simp [leftEndpointCandidate, collapsedInteriorCuts, Finset.image_union,
          hcollapse, hpair, hja, haS, hjS, collapseAfter, Finset.erase_union_distrib]

theorem rightEndpointCandidate_valid
    (a i : ℕ) (S : Finset ℕ) (m : EndpointLiftMode)
    (hiA : i < a)
    (hS : S ⊆ Finset.Ioo (collapseAfter a i) a) :
    rightEndpointCandidate a S m ⊆ Finset.Ioo i (a + 1) ∧
      collapsedInteriorCuts a i (a + 1) (rightEndpointCandidate a S m) = S := by
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hxbase | hxspecial
    · rcases Finset.mem_image.mp hxbase with ⟨y, hyS, rfl⟩
      have hyI := hS hyS
      simp only [Finset.mem_Ioo] at hyI
      have hia : i ≤ a := by omega
      rw [collapseAfter_eq_of_le a i hia] at hyI
      simp only [Finset.mem_Ioo]
      simp [liftAfter, Nat.le_of_lt hyI.2]
      omega
    · by_cases hm : m = EndpointLiftMode.shortLeaf
      · simp [hm] at hxspecial
        simp only [Finset.mem_Ioo]
        omega
      · simp [hm] at hxspecial
  · have hi : collapseAfter a i = i := by
      exact collapseAfter_eq_of_le a i (by omega)
    have hia : i ≤ a := by omega
    have hiaNe : i ≠ a := by omega
    have hja : ¬ a + 1 ≤ a := by omega
    have hj : collapseAfter a (a + 1) = a := by
      simp [collapseAfter, hja]
    have hcollapse : (liftedCuts a S).image (collapseAfter a) = S := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
        rcases Finset.mem_image.mp hx with ⟨z, hzS, hxz⟩
        subst x
        have hzI := hS hzS
        simp only [Finset.mem_Ioo] at hzI
        have hback := collapseAfter_liftAfter_of_ne a z (by omega)
        have hEq : z = y := by simpa [hback] using hxy
        simpa [hEq] using hzS
      · intro hyS
        have hyI := hS hyS
        simp only [Finset.mem_Ioo] at hyI
        have hback := collapseAfter_liftAfter_of_ne a y (by omega)
        refine Finset.mem_image.mpr ⟨liftAfter a y, Finset.mem_image.mpr ⟨y, hyS, rfl⟩, ?_⟩
        simpa [hback]
    have hiS : i ∉ S := by
      intro hmem
      have h := hS hmem
      simp only [Finset.mem_Ioo] at h
      omega
    have haS : a ∉ S := by
      intro hmem
      have h := hS hmem
      simp only [Finset.mem_Ioo] at h
      omega
    cases m with
    | unsplit =>
        simp [rightEndpointCandidate, collapsedInteriorCuts, hcollapse, hia, hja,
          hiS, haS, collapseAfter]
    | shortLeaf =>
        have hpair : ({a} : Finset ℕ).image (collapseAfter a) = {a} := by
          ext y
          simp [collapseAfter]
        simp [rightEndpointCandidate, collapsedInteriorCuts, Finset.image_union,
          hcollapse, hpair, hia, hiaNe, hja, hiS, haS, collapseAfter,
          Finset.erase_union_distrib, Finset.erase_singleton]

theorem away_liftedCuts_valid
    (a i j : ℕ) (S : Finset ℕ)
    (hij : i < j) (hAway : j ≤ a ∨ a + 1 ≤ i)
    (hS : S ⊆ Finset.Ioo (collapseAfter a i) (collapseAfter a j)) :
    liftedCuts a S ⊆ Finset.Ioo i j ∧
      collapsedInteriorCuts a i j (liftedCuts a S) = S := by
  have hcollapse : (liftedCuts a S).image (collapseAfter a) = S := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
      rcases Finset.mem_image.mp hx with ⟨z, hzS, hxz⟩
      rw [← hxz] at hxy
      have hzI := hS hzS
      simp only [Finset.mem_Ioo] at hzI
      have hne : z ≠ a := by
        rcases hAway with hbefore | hafter
        · have hj : collapseAfter a j = j := collapseAfter_eq_of_le a j (by omega)
          rw [hj] at hzI
          omega
        · have hi : collapseAfter a i = i - 1 := collapseAfter_eq_sub_one_of_lt a i (by omega)
          rw [hi] at hzI
          omega
      have hback := collapseAfter_liftAfter_of_ne a z hne
      have hEq : z = y := by simpa [hback] using hxy
      simpa [hEq] using hzS
    · intro hyS
      have hyI := hS hyS
      simp only [Finset.mem_Ioo] at hyI
      have hne : y ≠ a := by
        rcases hAway with hbefore | hafter
        · have hi : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
          have hj : collapseAfter a j = j := collapseAfter_eq_of_le a j (by omega)
          rw [hi, hj] at hyI
          omega
        · have hi : collapseAfter a i = i - 1 := collapseAfter_eq_sub_one_of_lt a i (by omega)
          rw [hi] at hyI
          omega
      have hback := collapseAfter_liftAfter_of_ne a y hne
      refine Finset.mem_image.mpr ⟨liftAfter a y, Finset.mem_image.mpr ⟨y, hyS, rfl⟩, ?_⟩
      simpa [hback]
  have hiS : collapseAfter a i ∉ S := by
    intro hx
    have h := hS hx
    simp only [Finset.mem_Ioo] at h
    omega
  have hjS : collapseAfter a j ∉ S := by
    intro hx
    have h := hS hx
    simp only [Finset.mem_Ioo] at h
    omega
  constructor
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hyS, rfl⟩
    have hyI := hS hyS
    simp only [Finset.mem_Ioo] at hyI
    rcases hAway with hbefore | hafter
    · have hi : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
      have hj : collapseAfter a j = j := collapseAfter_eq_of_le a j (by omega)
      rw [hi, hj] at hyI
      have hle : y ≤ a := by omega
      have hLift : liftAfter a y = y := by simp [liftAfter, hle]
      rw [hLift]
      simpa only [Finset.mem_Ioo] using hyI
    · have hi : collapseAfter a i = i - 1 := collapseAfter_eq_sub_one_of_lt a i (by omega)
      have hj : collapseAfter a j = j - 1 := collapseAfter_eq_sub_one_of_lt a j (by omega)
      rw [hi, hj] at hyI
      have hgt : a < y := by omega
      have hLift : liftAfter a y = y + 1 := by simp [liftAfter, Nat.not_le_of_gt hgt]
      rw [hLift]
      simp only [Finset.mem_Ioo]
      omega
  · simp [collapsedInteriorCuts, hcollapse, hiS, hjS]

noncomputable def shortEdge_cutFiber_away
    (a i j : ℕ) (S : Finset ℕ)
    (hij : i < j) (hAway : j ≤ a ∨ a + 1 ≤ i)
    (hS : S ⊆ Finset.Ioo (collapseAfter a i) (collapseAfter a j)) :
    ShortEdgeCutFiber a i j S ≃ PUnit := by
  refine
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨liftedCuts a S, away_liftedCuts_valid a i j S hij hAway hS⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    apply Subtype.ext
    exact (away_fiber_decomposition a i j S T.1 hij hAway hS T.2.1 T.2.2).symm
  · intro u
    cases u
    rfl

noncomputable def shortEdge_cutFiber_leftEndpoint
    (a j : ℕ) (S : Finset ℕ)
    (hABj : a + 1 < j)
    (hS : S ⊆ Finset.Ioo a (collapseAfter a j)) :
    ShortEdgeCutFiber a a j S ≃ EndpointLiftMode := by
  refine
    { toFun := fun T => if a + 1 ∈ T.1 then EndpointLiftMode.shortLeaf else EndpointLiftMode.unsplit
      invFun := fun m => ⟨leftEndpointCandidate a S m, leftEndpointCandidate_valid a j S m hABj hS⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    apply Subtype.ext
    have hdec := leftEndpoint_fiber_decomposition a j S T.1 hABj hS T.2.1 T.2.2
    by_cases hm : a + 1 ∈ T.1
    · simpa [leftEndpointCandidate, hm] using hdec.symm
    · simpa [leftEndpointCandidate, hm] using hdec.symm
  · intro m
    cases m with
    | unsplit =>
        have hnot : a + 1 ∉ liftedCuts a S := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨y, hyS, hy⟩
          have hyI := hS hyS
          simp only [Finset.mem_Ioo] at hyI
          have hgt : a < y := hyI.1
          simp [liftAfter, Nat.not_le_of_gt hgt] at hy
          omega
        simp [leftEndpointCandidate, hnot]
    | shortLeaf =>
        simp [leftEndpointCandidate]

noncomputable def shortEdge_cutFiber_rightEndpoint
    (a i : ℕ) (S : Finset ℕ)
    (hiA : i < a)
    (hS : S ⊆ Finset.Ioo (collapseAfter a i) a) :
    ShortEdgeCutFiber a i (a + 1) S ≃ EndpointLiftMode := by
  refine
    { toFun := fun T => if a ∈ T.1 then EndpointLiftMode.shortLeaf else EndpointLiftMode.unsplit
      invFun := fun m => ⟨rightEndpointCandidate a S m, rightEndpointCandidate_valid a i S m hiA hS⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    apply Subtype.ext
    have hdec := rightEndpoint_fiber_decomposition a i S T.1 hiA hS T.2.1 T.2.2
    by_cases hm : a ∈ T.1
    · simpa [rightEndpointCandidate, hm] using hdec.symm
    · simpa [rightEndpointCandidate, hm] using hdec.symm
  · intro m
    cases m with
    | unsplit =>
        have hnot : a ∉ liftedCuts a S := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨y, hyS, hy⟩
          have hyI := hS hyS
          simp only [Finset.mem_Ioo] at hyI
          have hlt : y < a := hyI.2
          simp [liftAfter, Nat.le_of_lt hlt] at hy
          omega
        simp [rightEndpointCandidate, hnot]
    | shortLeaf =>
        simp [rightEndpointCandidate]

def spanCandidate (a : ℕ) (S : Finset ℕ) (m : SpanLiftMode) : Finset ℕ :=
  (liftedCuts a S).erase a ∪
    (if m = SpanLiftMode.cutAtA ∨ m = SpanLiftMode.cutAtBoth then {a} else ∅) ∪
    (if m = SpanLiftMode.cutAtB ∨ m = SpanLiftMode.cutAtBoth then {a + 1} else ∅)

theorem spanCandidate_valid
    (a i j : ℕ) (S : Finset ℕ) (m : SpanLiftMode)
    (hiA : i < a) (hBj : a + 1 < j) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j)) :
    spanCandidate a S m ⊆ Finset.Ioo i j ∧
      collapsedInteriorCuts a i j (spanCandidate a S m) = S := by
  have hja : collapseAfter a j = j - 1 := collapseAfter_eq_sub_one_of_lt a j (by omega)
  have hBaseSubset : (liftedCuts a S).erase a ⊆ Finset.Ioo i j := by
    intro x hx
    have hxa := (Finset.mem_erase.mp hx).1
    have hxbase := (Finset.mem_erase.mp hx).2
    rcases Finset.mem_image.mp hxbase with ⟨y, hyS, hxy⟩
    have hyI := hS hyS
    simp only [Finset.mem_Ioo] at hyI
    rw [hja] at hyI
    have hyne : y ≠ a := by
      intro heq
      subst y
      simp [liftAfter] at hxy
      exact hxa hxy.symm
    by_cases hylt : y < a
    · have hLift : liftAfter a y = y := by simp [liftAfter, Nat.le_of_lt hylt]
      rw [hLift] at hxy
      simp only [Finset.mem_Ioo]
      omega
    · have hygt : a < y := by omega
      have hLift : liftAfter a y = y + 1 := by simp [liftAfter, Nat.not_le_of_gt hygt]
      rw [hLift] at hxy
      simp only [Finset.mem_Ioo]
      omega
  constructor
  · intro x hx
    change x ∈
      (((liftedCuts a S).erase a ∪
          (if m = SpanLiftMode.cutAtA ∨ m = SpanLiftMode.cutAtBoth then {a} else ∅)) ∪
        (if m = SpanLiftMode.cutAtB ∨ m = SpanLiftMode.cutAtBoth then {a + 1} else ∅)) at hx
    rcases Finset.mem_union.mp hx with hxmain | hxB
    · rcases Finset.mem_union.mp hxmain with hxbase | hxA
      · exact hBaseSubset hxbase
      · by_cases hmode : m = SpanLiftMode.cutAtA ∨ m = SpanLiftMode.cutAtBoth
        · simp [hmode, Finset.mem_singleton] at hxA
          subst x
          simp only [Finset.mem_Ioo]
          omega
        · simp [hmode] at hxA
    · by_cases hmode : m = SpanLiftMode.cutAtB ∨ m = SpanLiftMode.cutAtBoth
      · simp [hmode, Finset.mem_singleton] at hxB
        subst x
        simp only [Finset.mem_Ioo]
        omega
      · simp [hmode] at hxB
  · have hja : collapseAfter a j = j - 1 := collapseAfter_eq_sub_one_of_lt a j (by omega)
    have hi : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
    have haS' : a ∉ S.erase a := Finset.not_mem_erase a S
    have hbase : ((liftedCuts a S).erase a).image (collapseAfter a) = S.erase a := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
        have hxa := (Finset.mem_erase.mp hx).1
        have hxbase := (Finset.mem_erase.mp hx).2
        rcases Finset.mem_image.mp hxbase with ⟨z, hzS, hxz⟩
        rw [← hxz] at hxy
        have hzne : z ≠ a := by
          intro heq
          subst z
          simp [liftAfter] at hxz
          exact hxa hxz.symm
        have hback := collapseAfter_liftAfter_of_ne a z hzne
        have hEq : z = y := by simpa [hback] using hxy
        exact Finset.mem_erase.mpr ⟨by simpa [hEq] using hzne, by simpa [hEq] using hzS⟩
      · intro hy
        have hya := (Finset.mem_erase.mp hy).1
        have hyS := (Finset.mem_erase.mp hy).2
        have hback := collapseAfter_liftAfter_of_ne a y hya
        have hLiftNe : liftAfter a y ≠ a := by
          by_cases hyle : y < a
          · simp [liftAfter, Nat.le_of_lt hyle]
            omega
          · have hygt : a < y := by omega
            simp [liftAfter, Nat.not_le_of_gt hygt]
            omega
        refine Finset.mem_image.mpr ⟨liftAfter a y, Finset.mem_erase.mpr ⟨hLiftNe, Finset.mem_image.mpr ⟨y, hyS, rfl⟩⟩, ?_⟩
        simpa [hback]
    have hleft : ({a} : Finset ℕ).image (collapseAfter a) = {a} := by
      ext y
      simp [collapseAfter]
    have hright : ({a + 1} : Finset ℕ).image (collapseAfter a) = {a} := by
      ext y
      simp [collapseAfter]
    have hiS : i ∉ S := by
      intro hmem
      have h := hS hmem
      simp only [Finset.mem_Ioo] at h
      omega
    have hjS : j - 1 ∉ S := by
      intro hmem
      have h := hS hmem
      simp only [Finset.mem_Ioo] at h
      omega
    have hiaNe : i ≠ a := by omega
    have hjNe : j - 1 ≠ a := by omega
    have hErasePair : (({a} : Finset ℕ).erase i).erase (j - 1) = {a} := by
      have hnoti : i ∉ ({a} : Finset ℕ) := by simp [hiaNe]
      have hnotj : j - 1 ∉ ({a} : Finset ℕ) := by simp [hjNe]
      rw [Finset.erase_eq_of_not_mem hnoti, Finset.erase_eq_of_not_mem hnotj]
    have hSunion : S.erase a ∪ {a} = S := by
      calc
        S.erase a ∪ {a} = {a} ∪ S.erase a := Finset.union_comm _ _
        _ = insert a (S.erase a) := by rfl
        _ = S := Finset.insert_erase haS
    cases m <;> simp [spanCandidate, collapsedInteriorCuts, Finset.image_union,
      hbase, hleft, hright, hja, hi, haS, haS', hiS, hjS,
      Finset.erase_union_distrib, Finset.erase_singleton, hErasePair, hSunion]

theorem span_fiber_decomposition
    (a i j : ℕ) (S T : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j)
    (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j))
    (hT : T ⊆ Finset.Ioo i j)
    (hCuts : collapsedInteriorCuts a i j T = S) :
    T = ((liftedCuts a S).erase a ∪ if a ∈ T then {a} else ∅) ∪
        if a + 1 ∈ T then {a + 1} else ∅ := by
  ext x
  constructor
  · intro hxT
    by_cases hxa : x = a
    · subst x
      simp [hxT]
    · by_cases hxb : x = a + 1
      · subst x
        simp [hxT]
      · have hxI := hT hxT
        simp only [Finset.mem_Ioo] at hxI
        have hja : collapseAfter a j = j - 1 := collapseAfter_eq_sub_one_of_lt a j (by omega)
        have hcxBounds : i < collapseAfter a x ∧ collapseAfter a x < j - 1 := by
          by_cases hxle : x ≤ a
          · rw [collapseAfter_eq_of_le a x hxle]
            omega
          · have hax : a + 1 < x := by omega
            rw [collapseAfter_eq_sub_one_of_lt a x (by omega)]
            omega
        have hci : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
        have hcxNeI : collapseAfter a x ≠ collapseAfter a i := by rw [hci]; omega
        have hcxNeJ : collapseAfter a x ≠ collapseAfter a j := by rw [hja]; omega
        have hyImage : collapseAfter a x ∈ T.image (collapseAfter a) :=
          Finset.mem_image.mpr ⟨x, hxT, rfl⟩
        have hyS : collapseAfter a x ∈ S := by
          rw [← hCuts]
          change collapseAfter a x ∈
            ((T.image (collapseAfter a)).erase (collapseAfter a i)).erase (collapseAfter a j)
          exact Finset.mem_erase.mpr ⟨hcxNeJ, Finset.mem_erase.mpr ⟨hcxNeI, hyImage⟩⟩
        have hback := liftAfter_collapseAfter_of_ne_succ a x hxb
        have hxLift : x ∈ liftedCuts a S := by
          change x ∈ S.image (liftAfter a)
          exact Finset.mem_image.mpr ⟨collapseAfter a x, hyS, hback⟩
        simp [hxa, hxb, hxT, Finset.mem_erase.mpr ⟨hxa, hxLift⟩]
  · intro hx
    rcases Finset.mem_union.mp hx with hxmain | hxB
    · rcases Finset.mem_union.mp hxmain with hxbase | hxA
      · rcases Finset.mem_erase.mp hxbase with ⟨hya, hxLift⟩
        rcases Finset.mem_image.mp hxLift with ⟨y, hyS, hxy⟩
        subst x
        have hyI := hS hyS
        simp only [Finset.mem_Ioo] at hyI
        have hja : collapseAfter a j = j - 1 := collapseAfter_eq_sub_one_of_lt a j (by omega)
        have hci : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
        have hyNeI : y ≠ collapseAfter a i := by rw [hci]; omega
        have hyNeJ : y ≠ collapseAfter a j := by rw [hja]; omega
        have hyImage : y ∈ T.image (collapseAfter a) := by
          have hyS' : y ∈ collapsedInteriorCuts a i j T := by rw [hCuts]; exact hyS
          change y ∈ ((T.image (collapseAfter a)).erase (collapseAfter a i)).erase (collapseAfter a j) at hyS'
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hyS').2).2
        rcases Finset.mem_image.mp hyImage with ⟨z, hzT, hyz⟩
        have hza : z ≠ a + 1 := by
          intro heq
          subst z
          have hc : collapseAfter a (a + 1) = a := by simp [collapseAfter]
          rw [hc] at hyz
          have hyEq : y = a := by simpa using hyz.symm
          apply hya
          simp [hyEq, liftAfter]
        have hzback := liftAfter_collapseAfter_of_ne_succ a z hza
        have hzy : liftAfter a y = z := by simpa [hyz] using hzback
        rw [hzy]
        exact hzT
      · by_cases hmem : a ∈ T
        · have hEq : x = a := by simpa [hmem] using hxA
          rw [hEq]
          exact hmem
        · simp [hmem] at hxA
    · by_cases hmem : a + 1 ∈ T
      · have hEq : x = a + 1 := by simpa [hmem] using hxB
        rw [hEq]
        exact hmem
      · simp [hmem] at hxB

theorem span_fiber_pair_nonempty
    (a i j : ℕ) (S T : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j))
    (hT : T ⊆ Finset.Ioo i j)
    (hCuts : collapsedInteriorCuts a i j T = S) :
    a ∈ T ∨ a + 1 ∈ T := by
  have hi : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
  have hj : collapseAfter a j = j - 1 := collapseAfter_eq_sub_one_of_lt a j (by omega)
  have hnoti : a ≠ collapseAfter a i := by rw [hi]; omega
  have hnotj : a ≠ collapseAfter a j := by rw [hj]; omega
  have haImage : a ∈ T.image (collapseAfter a) := by
    have haCuts : a ∈ collapsedInteriorCuts a i j T := by
      rw [hCuts]
      exact haS
    have ha1 : a ∈ (T.image (collapseAfter a)).erase (collapseAfter a i) := by
      rw [collapsedInteriorCuts] at haCuts
      exact (Finset.mem_erase.mp haCuts).2
    exact (Finset.mem_erase.mp ha1).2
  rcases Finset.mem_image.mp haImage with ⟨x, hxT, hxa⟩
  by_cases hle : x ≤ a
  · have hcollapse := collapseAfter_eq_of_le a x hle
    rw [hcollapse] at hxa
    exact Or.inl (by simpa [hxa] using hxT)
  · have hgt : a < x := by omega
    have hcollapse := collapseAfter_eq_sub_one_of_lt a x hgt
    rw [hcollapse] at hxa
    have hxEq : x = a + 1 := by omega
    exact Or.inr (by simpa [hxEq] using hxT)

noncomputable def shortEdge_cutFiber_span_at_cut
    (a i j : ℕ) (S : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j)) :
    ShortEdgeCutFiber a i j S ≃ SpanLiftMode := by
  refine
    { toFun := fun T =>
        if a ∈ T.1 then
          if a + 1 ∈ T.1 then SpanLiftMode.cutAtBoth else SpanLiftMode.cutAtA
        else SpanLiftMode.cutAtB
      invFun := fun m => ⟨spanCandidate a S m, spanCandidate_valid a i j S m hiA hBj haS hS⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    apply Subtype.ext
    have hpair := span_fiber_pair_nonempty a i j S T.1 hiA hBj haS hS T.2.1 T.2.2
    have hdec := span_fiber_decomposition a i j S T.1 hiA hBj haS hS T.2.1 T.2.2
    by_cases hA : a ∈ T.1 <;> by_cases hB : a + 1 ∈ T.1
    · rw [hdec]
      simp [spanCandidate, hA, hB]
    · rw [hdec]
      simp [spanCandidate, hA, hB]
    · rw [hdec]
      simp [spanCandidate, hA, hB]
    · exact False.elim (hpair.elim (hA) (hB))
  · intro m
    have hnotA : a ∉ (liftedCuts a S).erase a := Finset.not_mem_erase a (liftedCuts a S)
    have hnotB : a + 1 ∉ (liftedCuts a S).erase a := by
      intro hmem
      rcases Finset.mem_erase.mp hmem with ⟨_, hbase⟩
      rcases Finset.mem_image.mp hbase with ⟨y, hyS, hya⟩
      have hyI := hS hyS
      simp only [Finset.mem_Ioo] at hyI
      by_cases hyle : y ≤ a
      · have hLift := liftAfter a y
        simp [liftAfter, hyle] at hya
        omega
      · have hgt : a < y := by omega
        simp [liftAfter, Nat.not_le_of_gt hgt] at hya
        omega
    cases m with
    | cutAtA =>
        simp [spanCandidate, hnotA, hnotB]
    | cutAtB =>
        simp [spanCandidate, hnotA, hnotB]
    | cutAtBoth =>
        simp [spanCandidate, hnotA, hnotB]

theorem span_no_cut_liftedCuts_valid
    (a i j : ℕ) (S : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j) (haS : a ∉ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j)) :
    liftedCuts a S ⊆ Finset.Ioo i j ∧
      collapsedInteriorCuts a i j (liftedCuts a S) = S := by
  have hja : collapseAfter a j = j - 1 := collapseAfter_eq_sub_one_of_lt a j (by omega)
  have hi : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
  have hcollapse : (liftedCuts a S).image (collapseAfter a) = S := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
      rcases Finset.mem_image.mp hx with ⟨z, hzS, hxz⟩
      rw [← hxz] at hxy
      have hne : z ≠ a := by
        intro heq
        subst z
        exact haS hzS
      have hback := collapseAfter_liftAfter_of_ne a z hne
      have hEq : z = y := by simpa [hback] using hxy
      simpa [hEq] using hzS
    · intro hyS
      have hne : y ≠ a := by intro heq; subst y; exact haS hyS
      have hback := collapseAfter_liftAfter_of_ne a y hne
      refine Finset.mem_image.mpr ⟨liftAfter a y, Finset.mem_image.mpr ⟨y, hyS, rfl⟩, ?_⟩
      simpa [hback]
  have hiS : i ∉ S := by
    intro hx
    have h := hS hx
    simp only [Finset.mem_Ioo] at h
    omega
  have hjS : j - 1 ∉ S := by
    intro hx
    have h := hS hx
    rw [hja] at h
    simp only [Finset.mem_Ioo] at h
    omega
  constructor
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hyS, rfl⟩
    have hyI := hS hyS
    rw [hja] at hyI
    simp only [Finset.mem_Ioo] at hyI
    have hyne : y ≠ a := by intro heq; subst y; exact haS hyS
    by_cases hyle : y < a
    · have hLift : liftAfter a y = y := by simp [liftAfter, Nat.le_of_lt hyle]
      rw [hLift]
      simp only [Finset.mem_Ioo]
      omega
    · have hygt : a < y := by omega
      have hLift : liftAfter a y = y + 1 := by simp [liftAfter, Nat.not_le_of_gt hygt]
      rw [hLift]
      simp only [Finset.mem_Ioo]
      omega
  · simp [collapsedInteriorCuts, hcollapse, hi, hja, hiS, hjS]

theorem span_fiber_no_cut_decomposition
    (a i j : ℕ) (S T : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j)
    (haS : a ∉ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j))
    (hT : T ⊆ Finset.Ioo i j)
    (hCuts : collapsedInteriorCuts a i j T = S) :
    T = liftedCuts a S := by
  have hja : collapseAfter a j = j - 1 := collapseAfter_eq_sub_one_of_lt a j (by omega)
  have hi : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
  have hpair : a ∉ T ∧ a + 1 ∉ T := by
    have haImage : a ∉ collapsedInteriorCuts a i j T := by rw [hCuts]; exact haS
    constructor
    · intro haT
      apply haImage
      rw [collapsedInteriorCuts]
      have hca : collapseAfter a a = a := by simp [collapseAfter]
      have hci : collapseAfter a i ≠ a := by rw [hi]; omega
      have hcj : collapseAfter a j ≠ a := by rw [hja]; omega
      exact Finset.mem_erase.mpr ⟨Ne.symm hcj, Finset.mem_erase.mpr ⟨Ne.symm hci,
        Finset.mem_image.mpr ⟨a, haT, hca⟩⟩⟩
    · intro habT
      apply haImage
      rw [collapsedInteriorCuts]
      have hca : collapseAfter a (a + 1) = a := by simp [collapseAfter]
      have hci : collapseAfter a i ≠ a := by rw [hi]; omega
      have hcj : collapseAfter a j ≠ a := by rw [hja]; omega
      exact Finset.mem_erase.mpr ⟨Ne.symm hcj, Finset.mem_erase.mpr ⟨Ne.symm hci,
        Finset.mem_image.mpr ⟨a + 1, habT, hca⟩⟩⟩
  ext x
  constructor
  · intro hxT
    have hxI := hT hxT
    simp only [Finset.mem_Ioo] at hxI
    have hxneA : x ≠ a := by
      intro heq
      subst x
      exact hpair.1 hxT
    have hxneB : x ≠ a + 1 := by
      intro heq
      subst x
      exact hpair.2 hxT
    have hcxBounds : i < collapseAfter a x ∧ collapseAfter a x < j - 1 := by
      by_cases hxle : x ≤ a
      · have hne : x < a := by omega
        rw [collapseAfter_eq_of_le a x hxle]
        omega
      · have hgt : a + 1 < x := by omega
        rw [collapseAfter_eq_sub_one_of_lt a x (by omega)]
        omega
    have hcxNeI : collapseAfter a x ≠ collapseAfter a i := by rw [hi]; omega
    have hcxNeJ : collapseAfter a x ≠ collapseAfter a j := by rw [hja]; omega
    have hyS : collapseAfter a x ∈ S := by
      rw [← hCuts]
      change collapseAfter a x ∈
        ((T.image (collapseAfter a)).erase (collapseAfter a i)).erase (collapseAfter a j)
      exact Finset.mem_erase.mpr ⟨hcxNeJ, Finset.mem_erase.mpr ⟨hcxNeI,
        Finset.mem_image.mpr ⟨x, hxT, rfl⟩⟩⟩
    have hback := liftAfter_collapseAfter_of_ne_succ a x hxneB
    change x ∈ S.image (liftAfter a)
    exact Finset.mem_image.mpr ⟨collapseAfter a x, hyS, hback⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hyS, hxy⟩
    have hyI := hS hyS
    rw [hja] at hyI
    simp only [Finset.mem_Ioo] at hyI
    have hyNeI : y ≠ collapseAfter a i := by rw [hi]; omega
    have hyNeJ : y ≠ collapseAfter a j := by rw [hja]; omega
    have hyImage : y ∈ T.image (collapseAfter a) := by
      have hyS' : y ∈ collapsedInteriorCuts a i j T := by rw [hCuts]; exact hyS
      change y ∈ ((T.image (collapseAfter a)).erase (collapseAfter a i)).erase (collapseAfter a j) at hyS'
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hyS').2).2
    rcases Finset.mem_image.mp hyImage with ⟨z, hzT, hyz⟩
    have hzne : z ≠ a + 1 := by
      intro hz
      subst z
      have hc : collapseAfter a (a + 1) = a := by simp [collapseAfter]
      rw [hc] at hyz
      have hyEq : y = a := by simpa using hyz.symm
      exact haS (by simpa [hyEq] using hyS)
    have hzback := liftAfter_collapseAfter_of_ne_succ a z hzne
    have hzy : liftAfter a y = z := by simpa [hyz] using hzback
    rw [← hxy, hzy]
    exact hzT

noncomputable def shortEdge_cutFiber_span_away_from_cut
    (a i j : ℕ) (S : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j) (haS : a ∉ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j)) :
    ShortEdgeCutFiber a i j S ≃ PUnit := by
  refine
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨liftedCuts a S, span_no_cut_liftedCuts_valid a i j S hiA hBj haS hS⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    apply Subtype.ext
    exact (span_fiber_no_cut_decomposition a i j S T.1 hiA hBj haS hS T.2.1 T.2.2).symm
  · intro u
    cases u
    rfl

end DirectGLSSW.ShortEdgeCutFibers
