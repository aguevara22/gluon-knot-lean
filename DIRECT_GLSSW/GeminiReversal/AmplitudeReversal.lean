import GeminiReversal.CyclicGenericReversal

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW

open DirectGLSSW.GeminiReversalContract
open scoped BigOperators

section CutReversal

def revCutSet (m : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (fun x => m - x)

theorem revCutSet_subset (m : ℕ) {i j : ℕ} {S : Finset ℕ}
    (_hij : i < j) (hjm : j ≤ m) (hS : S ⊆ Finset.Ioo i j) :
    revCutSet m S ⊆ Finset.Ioo (m - j) (m - i) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hxI := Finset.mem_Ioo.mp (hS hx)
  exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩

theorem revCutSet_revCutSet (m : ℕ) {i j : ℕ} {S : Finset ℕ}
    (hjm : j ≤ m) (hS : S ⊆ Finset.Ioo i j) :
    revCutSet m (revCutSet m S) = S := by
  ext x
  simp only [revCutSet, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hzI := Finset.mem_Ioo.mp (hS hz)
    have hsub : m - (m - z) = z := by omega
    rwa [hsub]
  · intro hx
    have hxI := Finset.mem_Ioo.mp (hS hx)
    exact ⟨m - x, ⟨x, hx, rfl⟩, by omega⟩

@[simp] theorem revCutSet_empty (m : ℕ) : revCutSet m ∅ = ∅ := by
  simp [revCutSet]

theorem revCutSet_card (m : ℕ) {i j : ℕ} {S : Finset ℕ}
    (hjm : j ≤ m) (hS : S ⊆ Finset.Ioo i j) :
    (revCutSet m S).card = S.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  dsimp at hab
  have haI := Finset.mem_Ioo.mp (hS ha)
  have hbI := Finset.mem_Ioo.mp (hS hb)
  omega

theorem mem_cutVertices_iff {i j : ℕ} {S : Finset ℕ} {x : ℕ} :
    x ∈ cutVertices i j S ↔ x = i ∨ x ∈ S ∨ x = j := by
  simp [cutVertices, or_assoc]

theorem cutVertices_bounds {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {x : ℕ}
    (hx : x ∈ cutVertices i j S) :
    i ≤ x ∧ x ≤ j := by
  rcases mem_cutVertices_iff.mp hx with rfl | hxS | rfl
  · exact ⟨le_refl _, Nat.le_of_lt hij⟩
  · have hxI := Finset.mem_Ioo.mp (hS hxS)
    exact ⟨Nat.le_of_lt hxI.1, Nat.le_of_lt hxI.2⟩
  · exact ⟨Nat.le_of_lt hij, le_refl _⟩

theorem mem_cutVertices_revCutSet_iff {m i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hjm : j ≤ m) (hS : S ⊆ Finset.Ioo i j) {x : ℕ} :
    x ∈ cutVertices (m - j) (m - i) (revCutSet m S) ↔
      x ≤ m ∧ m - x ∈ cutVertices i j S := by
  rw [mem_cutVertices_iff, mem_cutVertices_iff]
  simp only [revCutSet, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨y, hy, rfl⟩ | rfl)
    · refine ⟨by omega, Or.inr (Or.inr (by omega))⟩
    · have hyI := Finset.mem_Ioo.mp (hS hy)
      refine ⟨by omega, Or.inr (Or.inl ?_)⟩
      have hsub : m - (m - y) = y := by omega
      rwa [hsub]
    · refine ⟨by omega, Or.inl (by omega)⟩
  · rintro ⟨hxm, hmx | hmx | hmx⟩
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inl ⟨m - x, hmx, by omega⟩)
    · exact Or.inl (by omega)

theorem cutEdges_revCutSet_mem_iff {m i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hjm : j ≤ m) (hS : S ⊆ Finset.Ioo i j) {a b : ℕ} :
    (a, b) ∈ cutEdges (m - j) (m - i) (revCutSet m S) ↔
      b ≤ m ∧ (m - b, m - a) ∈ cutEdges i j S := by
  have hmij : m - j < m - i := by omega
  have hrevS := revCutSet_subset m hij hjm hS
  rw [cutEdges_mem_iff hmij hrevS, cutEdges_mem_iff hij hS]
  rw [mem_cutVertices_revCutSet_iff hij hjm hS,
    mem_cutVertices_revCutSet_iff hij hjm hS]
  constructor
  · rintro ⟨⟨ham, ha⟩, ⟨hbm, hb⟩, hab, hsep⟩
    refine ⟨hbm, hb, ha, by omega, ?_⟩
    intro x hx
    have hxb := cutVertices_bounds hij hS hx
    have hmx : m - x ∈ cutVertices (m - j) (m - i) (revCutSet m S) := by
      rw [mem_cutVertices_revCutSet_iff hij hjm hS]
      refine ⟨by omega, ?_⟩
      have hsub : m - (m - x) = x := by omega
      rwa [hsub]
    rcases hsep (m - x) hmx with h1 | h2
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · rintro ⟨hbm, hb, ha, hba, hsep⟩
    have ham : a ≤ m := by omega
    refine ⟨⟨ham, ha⟩, ⟨hbm, hb⟩, by omega, ?_⟩
    intro y hy
    obtain ⟨hym, hmy⟩ := (mem_cutVertices_revCutSet_iff hij hjm hS).mp hy
    rcases hsep (m - y) hmy with h1 | h2
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

theorem branchProduct_revCutSet (X : IntervalArray) {m i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hjm : j ≤ m) (hS : S ⊆ Finset.Ioo i j) :
    branchProduct X (cutVertices (m - j) (m - i) (revCutSet m S)) =
      branchProduct (fun a b => X (m - b) (m - a)) (cutVertices i j S) := by
  have hmij : m - j < m - i := by omega
  have hrevS := revCutSet_subset m hij hjm hS
  rw [branchProduct_eq_prod_cutEdges X hmij hrevS,
    branchProduct_eq_prod_cutEdges (fun a b => X (m - b) (m - a)) hij hS]
  refine Finset.prod_bij'
    (fun e _ => (m - e.2, m - e.1))
    (fun e _ => (m - e.2, m - e.1)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    exact ((cutEdges_revCutSet_mem_iff hij hjm hS).mp he).2
  · intro e he
    have he' := (cutEdges_mem_iff hij hS).mp he
    have hb := (cutVertices_bounds hij hS he'.2.1).2
    have ha := (cutVertices_bounds hij hS he'.1).2
    rw [cutEdges_revCutSet_mem_iff hij hjm hS]
    refine ⟨by omega, ?_⟩
    have h1 : m - (m - e.1) = e.1 := by omega
    have h2 : m - (m - e.2) = e.2 := by omega
    rwa [h1, h2]
  · intro e he
    have hbm := ((cutEdges_revCutSet_mem_iff hij hjm hS).mp he).1
    have hlt := ((cutEdges_mem_iff hmij hrevS).mp he).2.2.1
    ext <;> dsimp <;> omega
  · intro e he
    have he' := (cutEdges_mem_iff hij hS).mp he
    have hb := (cutVertices_bounds hij hS he'.2.1).2
    have ha := (cutVertices_bounds hij hS he'.1).2
    ext <;> dsimp <;> omega
  · intro e he
    have hbm := ((cutEdges_revCutSet_mem_iff hij hjm hS).mp he).1
    have hlt := ((cutEdges_mem_iff hmij hrevS).mp he).2.2.1
    dsimp
    have h1 : m - (m - e.1) = e.1 := by omega
    have h2 : m - (m - e.2) = e.2 := by omega
    rw [h1, h2]

theorem branchProduct_sign_telescope (X Y : IntervalArray) {i j : ℕ} {l : List ℕ}
    (hpw : (i :: l ++ [j]).Pairwise (· < ·))
    (hXY : ∀ a b, (a, b) ∈ (i :: l ++ [j]).zip (l ++ [j]) →
      X a b = (-1 : ℚ) ^ (b - a - 1) * Y a b) :
    (-1 : ℚ) ^ l.length * branchProduct X (i :: l ++ [j]) =
      (-1 : ℚ) ^ (j - i - 1) * branchProduct Y (i :: l ++ [j]) := by
  induction l generalizing i with
  | nil =>
      have hXij := hXY i j (by simp)
      simp [branchProduct, hXij]
  | cons k ks ih =>
      have hcons := List.pairwise_cons.mp hpw
      have hik : i < k := hcons.1 k (by simp)
      have hpw' : (k :: ks ++ [j]).Pairwise (· < ·) := hcons.2
      have hkj : k < j := (List.pairwise_cons.mp hpw').1 j (by simp)
      have hXik : X i k = (-1 : ℚ) ^ (k - i - 1) * Y i k := hXY i k (by simp)
      have ih' := ih hpw' (fun a b hab => hXY a b (by
        simp only [List.cons_append, List.zip_cons_cons, List.mem_cons]
        exact Or.inr hab))
      have hexp : k - i - 1 + (j - k - 1) + 1 = j - i - 1 := by omega
      calc
        (-1 : ℚ) ^ (k :: ks).length * branchProduct X (i :: k :: ks ++ [j]) =
            (-1 : ℚ) * X i k * ((-1 : ℚ) ^ ks.length * branchProduct X (k :: ks ++ [j])) := by
          simp only [List.length_cons, pow_succ, branchProduct, List.cons_append,
            List.tail_cons, List.zip_cons_cons, List.map_cons, List.prod_cons]
          ring
        _ = (-1 : ℚ) * ((-1 : ℚ) ^ (k - i - 1) * Y i k) *
              ((-1 : ℚ) ^ (j - k - 1) * branchProduct Y (k :: ks ++ [j])) := by
          rw [hXik, ih']
        _ = ((-1 : ℚ) ^ (k - i - 1) * (-1 : ℚ) ^ (j - k - 1) * (-1 : ℚ) ^ 1) *
              (Y i k * branchProduct Y (k :: ks ++ [j])) := by
          ring
        _ = (-1 : ℚ) ^ (j - i - 1) * branchProduct Y (i :: k :: ks ++ [j]) := by
          rw [← pow_add, ← pow_add, hexp]
          simp only [branchProduct, List.cons_append, List.tail_cons,
            List.zip_cons_cons, List.map_cons, List.prod_cons]

theorem gateProduct_zero_near_revCutSet (H₁ H₂ : TripleArray) {m i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hjm : j ≤ m) (hS : S ⊆ Finset.Ioo i j)
    (hH : ∀ a b c, a < b → b < c → c ≤ m → H₁ a b c = - H₂ (m - c) (m - b) (m - a)) :
    gateProduct (fun _ _ _ => 0) H₁ (m - j) (m - i)
        (cutVertices (m - j) (m - i) (revCutSet m S)) =
      (-1 : ℚ) ^ S.card * gateProduct (fun _ _ _ => 0) H₂ i j (cutVertices i j S) := by
  have hmij : m - j < m - i := by omega
  have hrevS := revCutSet_subset m hij hjm hS
  rw [gateProduct_zero_near H₁ hmij hrevS, gateProduct_zero_near H₂ hij hS]
  have hinj : Set.InjOn (fun k => m - k) (S : Set ℕ) := by
    intro a ha b hb hab
    dsimp at hab
    have haI := Finset.mem_Ioo.mp (hS ha)
    have hbI := Finset.mem_Ioo.mp (hS hb)
    omega
  rw [revCutSet, Finset.prod_image hinj]
  have hprod :
      (∏ k ∈ S, -H₁ (m - j) (m - k) (m - i) / 2) =
        ∏ k ∈ S, ((-1 : ℚ) * (-H₂ i k j / 2)) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkI := Finset.mem_Ioo.mp (hS hk)
    have hHk := hH (m - j) (m - k) (m - i) (by omega) (by omega) (by omega)
    have h1 : m - (m - i) = i := by omega
    have h2 : m - (m - k) = k := by omega
    have h3 : m - (m - j) = j := by omega
    rw [h1, h2, h3] at hHk
    rw [hHk]
    ring
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_const]

theorem cutContribution_zero_near_revCutSet (H₁ H₂ : TripleArray) (X₁ X₂ : IntervalArray)
    {m i j : ℕ} {S : Finset ℕ} (hij : i < j) (hjm : j ≤ m) (hS : S ⊆ Finset.Ioo i j)
    (hH : ∀ a b c, a < b → b < c → c ≤ m → H₁ a b c = - H₂ (m - c) (m - b) (m - a))
    (hX : ∀ a b, (a, b) ∈ (cutVertices i j S).zip (cutVertices i j S).tail →
      X₁ (m - b) (m - a) = (-1 : ℚ) ^ (b - a - 1) * X₂ a b) :
    cutContribution (fun _ _ _ => 0) H₁ X₁ (m - j) (m - i) (revCutSet m S) =
      (-1 : ℚ) ^ (j - i - 1) * cutContribution (fun _ _ _ => 0) H₂ X₂ i j S := by
  unfold cutContribution
  rw [gateProduct_zero_near_revCutSet H₁ H₂ hij hjm hS hH,
    branchProduct_revCutSet X₁ hij hjm hS]
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort (· ≤ ·)
  have htel := branchProduct_sign_telescope
    (fun a b => X₁ (m - b) (m - a)) X₂
    (cutVertices_pairwise hij hS)
    (fun a b hab => hX a b (by simpa only [cutVertices, List.tail_cons] using hab))
  calc
    ((-1 : ℚ) ^ S.card * gateProduct (fun _ _ _ => 0) H₂ i j (cutVertices i j S)) *
        branchProduct (fun a b => X₁ (m - b) (m - a)) (cutVertices i j S) =
      gateProduct (fun _ _ _ => 0) H₂ i j (cutVertices i j S) *
        ((-1 : ℚ) ^ (S.sort (· ≤ ·)).length *
          branchProduct (fun a b => X₁ (m - b) (m - a)) (i :: S.sort (· ≤ ·) ++ [j])) := by
        rw [hlen]
        change _ = gateProduct (fun _ _ _ => 0) H₂ i j (cutVertices i j S) *
          ((-1 : ℚ) ^ S.card *
            branchProduct (fun a b => X₁ (m - b) (m - a)) (cutVertices i j S))
        ring
    _ = gateProduct (fun _ _ _ => 0) H₂ i j (cutVertices i j S) *
        ((-1 : ℚ) ^ (j - i - 1) * branchProduct X₂ (i :: S.sort (· ≤ ·) ++ [j])) := by
        rw [htel]
    _ = (-1 : ℚ) ^ (j - i - 1) *
        (gateProduct (fun _ _ _ => 0) H₂ i j (cutVertices i j S) *
          branchProduct X₂ (cutVertices i j S)) := by
        change gateProduct (fun _ _ _ => 0) H₂ i j (cutVertices i j S) *
          ((-1 : ℚ) ^ (j - i - 1) * branchProduct X₂ (cutVertices i j S)) = _
        ring

theorem nonUnary_zero_near_reverse (H₁ H₂ : TripleArray) (X₁ X₂ : IntervalArray)
    {m i j : ℕ} (hij : i < j) (hjm : j ≤ m)
    (hH : ∀ a b c, a < b → b < c → c ≤ m → H₁ a b c = - H₂ (m - c) (m - b) (m - a))
    (hX : ∀ a b, i ≤ a → a < b → b ≤ j → b - a < j - i →
      X₁ (m - b) (m - a) = (-1 : ℚ) ^ (b - a - 1) * X₂ a b) :
    nonUnary (fun _ _ _ => 0) H₁ X₁ (m - j) (m - i) =
      (-1 : ℚ) ^ (j - i - 1) * nonUnary (fun _ _ _ => 0) H₂ X₂ i j := by
  unfold nonUnary
  rw [Finset.mul_sum]
  refine Finset.sum_bij'
    (fun S _ => revCutSet m S)
    (fun S _ => revCutSet m S) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hS
    have hS' := Finset.mem_powerset.mp hsub
    have hmij : m - j < m - i := by omega
    have hS_orig : revCutSet m S ⊆ Finset.Ioo i j := by
      have h1 := revCutSet_subset m hmij (by omega) hS'
      have hi' : m - (m - i) = i := by omega
      have hj' : m - (m - j) = j := by omega
      rwa [hi', hj'] at h1
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr hS_orig⟩
    intro hempty
    dsimp at hempty
    apply hne
    have hcard := revCutSet_card m (by omega) hS'
    rw [hempty, Finset.card_empty] at hcard
    exact Finset.card_eq_zero.mp hcard.symm
  · intro S hS
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hS
    have hS' := Finset.mem_powerset.mp hsub
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr (revCutSet_subset m hij hjm hS')⟩
    intro hempty
    dsimp at hempty
    apply hne
    have hcard := revCutSet_card m hjm hS'
    rw [hempty, Finset.card_empty] at hcard
    exact Finset.card_eq_zero.mp hcard.symm
  · intro S hS
    have hS' := Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
    exact revCutSet_revCutSet m (by omega) hS'
  · intro S hS
    have hS' := Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
    exact revCutSet_revCutSet m hjm hS'
  · intro S hS
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hS
    have hS' := Finset.mem_powerset.mp hsub
    have hsne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hrev := revCutSet_revCutSet m (by omega) hS'
    have hS_orig : revCutSet m S ⊆ Finset.Ioo i j := by
      have h1 := revCutSet_subset m (by omega : m - j < m - i) (by omega) hS'
      have hi' : m - (m - i) = i := by omega
      have hj' : m - (m - j) = j := by omega
      rwa [hi', hj'] at h1
    have hne_orig : (revCutSet m S).Nonempty := by
      rw [revCutSet]
      exact hsne.image _
    have h := cutContribution_zero_near_revCutSet H₁ H₂ X₁ X₂ hij hjm hS_orig hH
      (fun a b hab => by
        obtain ⟨hia, hablt, hbj, hlt⟩ := cutVertices_branch_bounds hij hS_orig hne_orig hab
        exact hX a b hia hablt hbj hlt)
    rwa [hrev] at h

theorem phi_zero_near_reverse (H₁ H₂ : TripleArray) (X₁ X₂ : IntervalArray)
    {m i j : ℕ} (hij : i < j) (hjm : j ≤ m)
    (hH : ∀ a b c, a < b → b < c → c ≤ m → H₁ a b c = - H₂ (m - c) (m - b) (m - a))
    (hX : ∀ a b, i ≤ a → a < b → b ≤ j →
      X₁ (m - b) (m - a) = (-1 : ℚ) ^ (b - a - 1) * X₂ a b) :
    phi (fun _ _ _ => 0) H₁ X₁ (m - j) (m - i) =
      (-1 : ℚ) ^ (j - i - 1) * phi (fun _ _ _ => 0) H₂ X₂ i j := by
  rw [phi_eq_unary_add, phi_eq_unary_add, mul_add]
  congr 1
  · exact hX i j (le_refl i) hij (le_refl j)
  · exact nonUnary_zero_near_reverse H₁ H₂ X₁ X₂ hij hjm hH
      (fun a b hia hab hbj _ => hX a b hia hab hbj)

theorem ordinaryCurrent_zero_near_reverse (H₁ H₂ : TripleArray)
    {m i j : ℕ} (hij : i < j) (hjm : j ≤ m)
    (hH : ∀ a b c, a < b → b < c → c ≤ m → H₁ a b c = - H₂ (m - c) (m - b) (m - a)) :
    ordinaryCurrent (fun _ _ _ => 0) H₁ (m - j) (m - i) =
      (-1 : ℚ) ^ (j - i - 1) * ordinaryCurrent (fun _ _ _ => 0) H₂ i j := by
  generalize hd : j - i = d
  induction d using Nat.strong_induction_on generalizing i j with
  | h d ih =>
      subst hd
      have hmij : m - j < m - i := by omega
      rw [ordinaryCurrent_recurrence _ _ hmij, ordinaryCurrent_recurrence _ _ hij]
      have hsrc : source (m - j) (m - i) = (-1 : ℚ) ^ (j - i - 1) * source i j := by
        unfold source
        by_cases h1 : j = i + 1
        · have h2 : m - i = m - j + 1 := by omega
          have h3 : j - i - 1 = 0 := by omega
          simp [h1, h2, h3]
        · have h2 : m - i ≠ m - j + 1 := by omega
          simp [h1, h2]
      have hnu := nonUnary_zero_near_reverse H₁ H₂
        (ordinaryCurrent (fun _ _ _ => 0) H₁)
        (ordinaryCurrent (fun _ _ _ => 0) H₂) hij hjm hH
        (fun a b hia hab hbj hlt =>
          ih (b - a) hlt hab (by omega) rfl)
      rw [hsrc, hnu]
      ring

theorem markedAmplitude_zero_near_reverse (H₁ H₂ : TripleArray)
    {m i j : ℕ} (hij : i < j) (hjm : j ≤ m)
    (hH : ∀ a b c, a < b → b < c → c ≤ m → H₁ a b c = - H₂ (m - c) (m - b) (m - a)) :
    markedAmplitude (fun _ _ _ => 0) H₁ (m - j) (m - i) =
      (-1 : ℚ) ^ (j - i - 1) * markedAmplitude (fun _ _ _ => 0) H₂ i j := by
  unfold markedAmplitude
  refine phi_zero_near_reverse
    (fun a b c => -H₁ a b c) (fun a b c => -H₂ a b c)
    (ordinaryCurrent (fun _ _ _ => 0) H₁)
    (ordinaryCurrent (fun _ _ _ => 0) H₂) hij hjm ?_ ?_
  · intro a b c hab hbc hcm
    dsimp
    rw [hH a b c hab hbc hcm, neg_neg]
  · intro a b _ hab hbj
    exact ordinaryCurrent_zero_near_reverse H₁ H₂ hab (le_trans hbj hjm) hH

end CutReversal

section PolygonWordReversal

theorem cyclicVertexIndex_edgeRev_rev {n : ℕ} (root : Fin n) {k : ℕ} (hk : k < n) :
    (cyclicVertexIndex (edgeRev root) k).rev = cyclicVertexIndex root (n - 1 - k) := by
  have hn : 0 < n := root.pos
  have hr : root.val < n := root.isLt
  have hnk : n - 1 - k < n := by omega
  apply Fin.ext
  simp only [edgeRev, cyclicSuccessor, Fin.val_rev,
    cyclicVertexIndex_val _ hn, cyclicVertexIndex_val _ hk, cyclicVertexIndex_val _ hnk]
  split_ifs <;> omega

theorem rootedPolygonWord_reversePolygon_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (root : Fin n) {k : ℕ} (hk : k < n) :
    rootedPolygonWord (reversePolygon q) (edgeRev root) k =
      rootedPolygonWord q root (n - 1 - k) := by
  simp only [rootedPolygonWord, reversePolygon_apply, cyclicVertexIndex_edgeRev_rev root hk]

theorem scalarSignValue_neg (x : ℝ) :
    scalarSignValue (-x) = - scalarSignValue x := by
  unfold scalarSignValue
  rcases lt_trichotomy x 0 with hlt | rfl | hgt
  · have h1 : -x ≠ 0 := by linarith
    have h2 : ¬ (-x < 0) := by linarith
    have h3 : x ≠ 0 := ne_of_lt hlt
    simp [h1, h2, h3, hlt]
  · simp
  · have h1 : -x ≠ 0 := by linarith
    have h2 : -x < 0 := by linarith
    have h3 : x ≠ 0 := ne_of_gt hgt
    have h4 : ¬ (x < 0) := by linarith
    simp [h1, h2, h3, h4]

theorem polygonHDet_reversePolygon_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (root : Fin n) {a b c : ℕ} (_hab : a < b) (_hbc : b < c) (hcm : c ≤ n - 1) :
    polygonHDet (rootedPolygonWord (reversePolygon q) (edgeRev root)) a b c =
      - polygonHDet (rootedPolygonWord q root) (n - 1 - c) (n - 1 - b) (n - 1 - a) := by
  have hn : 0 < n := root.pos
  have ha : a < n := by omega
  have hb : b < n := by omega
  have hc : c < n := by omega
  simp only [polygonHDet,
    rootedPolygonWord_reversePolygon_edgeRev q root ha,
    rootedPolygonWord_reversePolygon_edgeRev q root hb,
    rootedPolygonWord_reversePolygon_edgeRev q root hc,
    planarDet, Prod.fst_sub, Prod.snd_sub]
  ring

theorem polygonSignArray_reversePolygon_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (root : Fin n) {a b c : ℕ} (hab : a < b) (hbc : b < c) (hcm : c ≤ n - 1) :
    polygonSignArray (rootedPolygonWord (reversePolygon q) (edgeRev root)) a b c =
      - polygonSignArray (rootedPolygonWord q root) (n - 1 - c) (n - 1 - b) (n - 1 - a) := by
  simp only [polygonSignArray, polygonHDet_reversePolygon_edgeRev q root hab hbc hcm,
    scalarSignValue_neg]

theorem rootedSpinorAmplitude_reversePolygon_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (root : Fin n) :
    rootedSpinorAmplitude (reversePolygon q) (edgeRev root) =
      (-1 : ℚ) ^ n * rootedSpinorAmplitude q root := by
  have hqr := cyclicGeneric_reversePolygon q hq
  have hn3 : 3 ≤ n := hq.size_ge_three
  have hm : 0 < n - 1 := by omega
  let H_rev := polygonSignArray (rootedPolygonWord (reversePolygon q) (edgeRev root))
  let H := polygonSignArray (rootedPolygonWord q root)
  have h1 : rootedSpinorAmplitude (reversePolygon q) (edgeRev root) =
      markedAmplitude (fun _ _ _ => 0) H_rev 0 (n - 1) := by
    rw [rootedSpinorAmplitude_eq_markedTreeSum hn3 (reversePolygon q) hqr.g1 (edgeRev root),
      markedTreeSum_eq_markedAmplitude H_rev H_rev hm,
      markedAmplitude_zero_near H_rev H_rev hm]
  have h2 : rootedSpinorAmplitude q root =
      markedAmplitude (fun _ _ _ => 0) H 0 (n - 1) := by
    rw [rootedSpinorAmplitude_eq_markedTreeSum hn3 q hq.g1 root,
      markedTreeSum_eq_markedAmplitude H H hm,
      markedAmplitude_zero_near H H hm]
  rw [h1, h2]
  have hrev := markedAmplitude_zero_near_reverse H_rev H
    (m := n - 1) (i := 0) (j := n - 1) hm (le_refl _)
    (fun a b c hab hbc hcm => polygonSignArray_reversePolygon_edgeRev q root hab hbc hcm)
  simp only [Nat.sub_self, Nat.sub_zero] at hrev
  rw [hrev]
  congr 1
  have hexp : n = (n - 1 - 1) + 2 := by omega
  rw [hexp, pow_add]
  norm_num

theorem polygonAmplitude_reversePolygon (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude (reversePolygon q) (cyclicGeneric_reversePolygon q hq) =
      (-1 : ℚ) ^ n * polygonAmplitude q hq := by
  let hqr := cyclicGeneric_reversePolygon q hq
  let r0 : Fin n := ⟨0, by have := hq.size_ge_three; omega⟩
  rw [polygonAmplitude_eq_rootedSpinorAmplitude hRI (reversePolygon q) hqr (edgeRev r0),
    polygonAmplitude_eq_rootedSpinorAmplitude hRI q hq r0]
  exact rootedSpinorAmplitude_reversePolygon_edgeRev q hq r0

theorem amplitude_reversal_thm :
    ∀ (hRI : GLSSWRootIndependence) {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      ∃ hqr : CyclicGeneric (reversePolygon q),
        polygonAmplitude (reversePolygon q) hqr = (-1 : ℚ) ^ n * polygonAmplitude q hq := by
  intro hRI n q hq
  exact ⟨cyclicGeneric_reversePolygon q hq, polygonAmplitude_reversePolygon hRI q hq⟩

end PolygonWordReversal

end DirectGLSSW
