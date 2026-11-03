import DirectGLSSW.CutGaps

/-!
# Incidence and product bridges for actual finite cut lists

Source: `ep:Phi`, `ep:factorization`. Finite triples retain the ordered
predecessor, middle, and successor from the existing cut list. These are
combinatorial prerequisites, provisional pending independent review.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- Adjacency is precisely increasing vertex membership with no intervening vertex. -/
theorem adjacent_mem_iff {v : List ℕ} (hv : v.Pairwise (· < ·)) {a b : ℕ} :
    (a, b) ∈ v.zip v.tail ↔
      a ∈ v ∧ b ∈ v ∧ a < b ∧ ∀ x ∈ v, x ≤ a ∨ b ≤ x := by
  constructor
  · exact adjacent_separation hv
  · intro hab
    induction v with
    | nil => simp at hab
    | cons y ys ih =>
        cases ys with
        | nil => simp only [List.mem_singleton] at hab; omega
        | cons z zs =>
            have hy := List.pairwise_cons.mp hv
            have hz := List.pairwise_cons.mp hy.2
            by_cases hay : a = y
            · subst a
              have hyz : y < z := hy.1 z (by simp)
              have hzb : z ≤ b := by
                rcases List.mem_cons.mp hab.2.1 with hby | hb
                · omega
                · rcases List.mem_cons.mp hb with hbz | hb
                  · omega
                  · exact Nat.le_of_lt (hz.1 b hb)
              have hsplit := hab.2.2.2 z (by simp)
              have hbz : b = z := by omega
              subst b
              simp
            · have ha : a ∈ z :: zs := (List.mem_cons.mp hab.1).resolve_left hay
              have hya := hy.1 a ha
              have hb : b ∈ z :: zs := by
                rcases List.mem_cons.mp hab.2.1 with hby | hb
                · omega
                · exact hb
              have ht := ih hy.2 ⟨ha, hb, hab.2.2.1,
                fun x hx => hab.2.2.2 x (by simp [hx])⟩
              simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
              exact Or.inr ht

/-- Finite triples use exactly the source's three consecutive vertices. -/
def cutTriples (i j : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  let v := cutVertices i j S
  (v.zip (v.tail.zip v.tail.tail)).toFinset

/-- The adjacency characterization specialized to the source cut vertices. -/
theorem cutEdges_mem_iff {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {a b : ℕ} :
    (a, b) ∈ cutEdges i j S ↔
      a ∈ cutVertices i j S ∧ b ∈ cutVertices i j S ∧ a < b ∧
      ∀ x ∈ cutVertices i j S, x ≤ a ∨ b ≤ x := by
  simpa only [cutEdges, List.mem_toFinset] using
    adjacent_mem_iff (cutVertices_pairwise hij hS) (a := a) (b := b)

private theorem zip_nodup_left {α β : Type*} {v : List α} (hv : v.Nodup)
    (w : List β) : (v.zip w).Nodup := by
  induction v generalizing w with
  | nil => simp
  | cons a v ih =>
      cases w with
      | nil => simp
      | cons b w =>
          rw [List.zip_cons_cons, List.nodup_cons]
          have hv' := List.nodup_cons.mp hv
          refine ⟨?_, ih hv'.2 w⟩
          intro h
          exact hv'.1 (List.of_mem_zip h).1

/-- Passing adjacent edges to a finset does not discard multiplicities. -/
theorem cutEdges_list_nodup {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    ((cutVertices i j S).zip (cutVertices i j S).tail).Nodup :=
  zip_nodup_left (cutVertices_pairwise hij hS).nodup _

/-- Passing consecutive triples to a finset does not discard multiplicities. -/
theorem cutTriples_list_nodup {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    ((cutVertices i j S).zip
      ((cutVertices i j S).tail.zip (cutVertices i j S).tail.tail)).Nodup :=
  zip_nodup_left (cutVertices_pairwise hij hS).nodup _

/-- The original list branch product equals the finite edge product. -/
theorem branchProduct_eq_prod_cutEdges (X : IntervalArray) {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    branchProduct X (cutVertices i j S) = ∏ e ∈ cutEdges i j S, X e.1 e.2 := by
  exact (List.prod_toFinset (fun e : ℕ × ℕ => X e.1 e.2)
    (cutEdges_list_nodup hij hS)).symm

/-- The original list gate product equals the finite ordered-triple product. -/
theorem gateProduct_eq_prod_cutTriples (D H : TripleArray) {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    gateProduct D H i j (cutVertices i j S) =
      ∏ t ∈ cutTriples i j S, (D t.1 t.2.1 t.2.2 - H i t.2.1 j) / 2 := by
  exact (List.prod_toFinset
    (fun t : ℕ × ℕ × ℕ => (D t.1 t.2.1 t.2.2 - H i t.2.1 j) / 2)
    (cutTriples_list_nodup hij hS)).symm

/-- Two adjacent edges with the same initial vertex have the same final vertex. -/
theorem adjacent_same_first {v : List ℕ} (hv : v.Pairwise (· < ·)) {a b c : ℕ}
    (hab : (a, b) ∈ v.zip v.tail) (hac : (a, c) ∈ v.zip v.tail) : b = c := by
  obtain ⟨_, hb, hablt, hsep₁⟩ := adjacent_separation hv hab
  obtain ⟨_, hc, haclt, hsep₂⟩ := adjacent_separation hv hac
  have h₁ := hsep₁ c hc
  have h₂ := hsep₂ b hb
  omega

/-- Two adjacent edges with the same final vertex have the same initial vertex. -/
theorem adjacent_same_last {v : List ℕ} (hv : v.Pairwise (· < ·)) {a b c : ℕ}
    (hac : (a, c) ∈ v.zip v.tail) (hbc : (b, c) ∈ v.zip v.tail) : a = b := by
  obtain ⟨ha, _, haclt, hsep₁⟩ := adjacent_separation hv hac
  obtain ⟨hb, _, hbclt, hsep₂⟩ := adjacent_separation hv hbc
  have h₁ := hsep₁ b hb
  have h₂ := hsep₂ a ha
  omega

/-- Consecutive triples are precisely two adjacent edges with a shared middle vertex. -/
theorem triple_mem_iff {v : List ℕ} (hv : v.Pairwise (· < ·)) {a b c : ℕ} :
    (a, b, c) ∈ v.zip (v.tail.zip v.tail.tail) ↔
      (a, b) ∈ v.zip v.tail ∧ (b, c) ∈ v.zip v.tail := by
  induction v with
  | nil => simp
  | cons y ys ih =>
      cases ys with
      | nil => simp
      | cons z zs =>
          have hy := List.pairwise_cons.mp hv
          have hyz : y < z := hy.1 z (by simp)
          cases zs with
          | nil =>
              constructor
              · intro ht; simp at ht
              · rintro ⟨hab, hbc⟩
                have hab' : a = y ∧ b = z := by simpa using hab
                have hbc' : b = y ∧ c = z := by simpa using hbc
                omega
          | cons w ws =>
              have ih' := ih hy.2
              constructor
              · intro ht
                change (a, b, c) ∈ (y, z, w) ::
                  ((z :: w :: ws).zip ((w :: ws).zip ws)) at ht
                rcases List.mem_cons.mp ht with ht | ht
                · have ht' : a = y ∧ b = z ∧ c = w := by simpa using ht
                  rcases ht' with ⟨rfl, rfl, rfl⟩
                  exact ⟨by simp, by simp⟩
                · have hh := ih'.mp ht
                  exact ⟨List.mem_cons_of_mem _ hh.1, List.mem_cons_of_mem _ hh.2⟩
              · rintro ⟨hab, hbc⟩
                change (a, b) ∈ (y, z) :: ((z :: w :: ws).zip (w :: ws)) at hab
                change (b, c) ∈ (y, z) :: ((z :: w :: ws).zip (w :: ws)) at hbc
                change (a, b, c) ∈ (y, z, w) ::
                  ((z :: w :: ws).zip ((w :: ws).zip ws))
                rcases List.mem_cons.mp hab with hab | hab
                · have hab' : a = y ∧ b = z := Prod.mk.inj hab
                  rcases hab' with ⟨ha, hb⟩
                  subst a
                  subst b
                  rcases List.mem_cons.mp hbc with hbc | hbc
                  · have heq := congrArg Prod.fst hbc
                    simp only at heq
                    omega
                  · have he : (z, w) ∈ (z :: w :: ws).zip (w :: ws) := by simp
                    have hcw := adjacent_same_first hy.2 hbc he
                    subst c
                    exact List.mem_cons_self
                · rcases List.mem_cons.mp hbc with hbc | hbc
                  · have hbc' : b = y ∧ c = z := Prod.mk.inj hbc
                    rcases hbc' with ⟨hb, hc⟩
                    subst b
                    subst c
                    have hb : y ∈ z :: w :: ws := List.mem_cons_of_mem z (List.of_mem_zip hab).2
                    have hyy := hy.1 y hb
                    omega
                  · exact List.mem_cons_of_mem _ (ih'.mpr ⟨hab, hbc⟩)

/-- The finite triple support is the incidence relation of two finite cut edges. -/
theorem cutTriples_mem_iff {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {a b c : ℕ} :
    (a, b, c) ∈ cutTriples i j S ↔
      (a, b) ∈ cutEdges i j S ∧ (b, c) ∈ cutEdges i j S := by
  simpa only [cutTriples, cutEdges, List.mem_toFinset] using
    triple_mem_iff (cutVertices_pairwise hij hS) (a := a) (b := b) (c := c)

/-- On the actual triple support, the internal cut determines both neighbors. -/
theorem cutTriples_middle_injective {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {t u : ℕ × ℕ × ℕ}
    (ht : t ∈ cutTriples i j S) (hu : u ∈ cutTriples i j S)
    (hm : t.2.1 = u.2.1) : t = u := by
  rcases t with ⟨a, b, c⟩
  rcases u with ⟨d, e, f⟩
  dsimp at hm
  subst e
  have ht' := (cutTriples_mem_iff hij hS).mp ht
  have hu' := (cutTriples_mem_iff hij hS).mp hu
  simp only [cutEdges, List.mem_toFinset] at ht' hu'
  have had := adjacent_same_last (cutVertices_pairwise hij hS) ht'.1 hu'.1
  have hcf := adjacent_same_first (cutVertices_pairwise hij hS) ht'.2 hu'.2
  subst d
  subst f
  rfl

private theorem triple_middle_list (i j : ℕ) (l : List ℕ) :
    ((i :: l ++ [j]).zip ((l ++ [j]).zip (l ++ [j]).tail)).map
      (fun t : ℕ × ℕ × ℕ => t.2.1) = l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y ys =>
          simpa only [List.cons_append, List.tail_cons, List.zip_cons_cons, List.map_cons]
            using congrArg (List.cons x) (ih x)

/-- Every selected internal cut is the middle vertex of a triple, exactly once. -/
theorem cutTriples_middle_image {i j : ℕ} {S : Finset ℕ}
    (_hij : i < j) (_hS : S ⊆ Finset.Ioo i j) :
    (cutTriples i j S).image (fun t => t.2.1) = S := by
  ext k
  have h : k ∈ (((i :: S.sort (· ≤ ·) ++ [j]).zip
      ((S.sort (· ≤ ·) ++ [j]).zip (S.sort (· ≤ ·) ++ [j]).tail)).map
      (fun t : ℕ × ℕ × ℕ => t.2.1)) ↔ k ∈ S.sort (· ≤ ·) := by
    rw [triple_middle_list]
  simpa only [List.mem_map, Finset.mem_sort, cutTriples, cutVertices,
    List.tail_cons, Finset.mem_image, List.mem_toFinset] using h

/-- A triple's middle vertex is one of the selected cuts. -/
theorem cutTriples_middle_mem {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cutTriples i j S) : t.2.1 ∈ S := by
  rw [← cutTriples_middle_image hij hS]
  exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

end DirectGLSSW
