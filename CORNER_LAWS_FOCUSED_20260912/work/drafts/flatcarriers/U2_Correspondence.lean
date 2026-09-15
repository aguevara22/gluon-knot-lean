import SM.FlatCarriersDefs

/-! U2 — Centre spec by transport, carrier correspondences, cycle identities
(def:flat-carriers / cor:flat-carriers, work/drafts/flatcarriers/PLAN_FINAL.md §5 "### U2").

Written 2026-09-13 by the U2 prover subagent on top of the built module `SM.FlatCarriersDefs`.
Everything here is sorry-free. The interface lemmas of U1 are taken as explicit hypotheses,
named as in PLAN_FINAL.md:
* `identify_sides_marks` : `(geoMarkList C).map (markTransport (hs b)) = geoMarkList T`;
* `identify_deletion_marks` : `(((geoMarkList C).erase (inl j)).map delMark : Cycle _) = geoMarkList D`;
* `independent_supports` (one side) : `IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property
  (transportSupport (hs b) S)` — only for the centre's `traced_successor`.
Both pairing facts (`visitTransport`/`fusionVisitEquiv` commute with `visitTwin`) are PROVED here.

Contents.
1. List lemmas: `List.next` commutes with an injective map (`list_next_map`), `List.next` on an
   erased list (`list_next_erase`).
2. `SameCycle` under a conjugating equivalence (`sameCycle_of_equiv_conj`).
3. Intrinsic centre lemmas on any `hP : CrossingGeometry P`: `successor_gap`
   (`geoMarkSuccessor_no_mark_between`), the successor lies on the outgoing edge
   (`geoMarkSuccessor_on_edge`), `inherited_pieces` (`geoSmoothingSegment_mem_edgeSegment`),
   `ρ a ≠ a` (`geoMarkSuccessor_ne_self`), and `geoCarrierSpec_of_traced_successor`.
4. Side ↔ centre: `selectedMarkPerm`, `ρ`, `ρ_S` commute with `markTransport`; owner-iff; mark and
   corner lists transport; `traced_successor` transports (`correspond_sides_of_marks`,
   `centre_carriers_of_marks`).
5. Centre ↔ deletion: the skip-`μ_j` permutation `skipJ`; `ρ_S^D b = delMark (skipJ (fusionMark b))`;
   owner-iff; surjectivity; `ρ_S^C (inl j) ≠ inl j` (`correspond_deletion_of_marks`); the mark-,
   corner- and plane-cycle identities (`central_vs_deletion_cycles_of_marks`,
   `others_unchanged_of_marks`); corner counts (`geoCornerCount_deletion_through_mu_j`,
   `geoCornerCount_deletion_other`; side: `geoCornerCount_markTransport`).
6. `unique_through_mu_j_data`, `same_retained_crossings_of_marks`.
7. The U2 bundle `flat_carriers_U2` (all U2 goals in one statement, exact field bodies).
Also: `sumLawfulBEq`, a `LawfulBEq (α ⊕ β)` instance (the marks' `List.erase` elaborates to
`Sum.instBEq`, which core leaves without a `LawfulBEq` instance). -/

namespace SM

open Carrier GeoCarrier

/-! ## 1. List lemmas -/

section ListLemmas

/-- `Sum.instBEq` is lawful when its components are (needed because `List.erase` on marks
`ZMod n ⊕ Visit P` elaborates to `Sum.instBEq`, which has no `LawfulBEq` instance in core). -/
instance sumLawfulBEq {α β : Type*} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp only [BEq.beq, Sum.instBEq.beq] at h
    · rw [eq_of_beq h]
    · exact absurd h Bool.false_ne_true
    · exact absurd h Bool.false_ne_true
    · rw [eq_of_beq h]
  rfl {a} := by
    cases a <;> simp only [BEq.beq, Sum.instBEq.beq] <;> exact beq_self_eq_true _

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `List.next` commutes with a map that is injective on the list. -/
theorem list_next_map (f : α → β) (l : List α) (hl : l.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (x : α) (hx : x ∈ l) (hfx : f x ∈ l.map f) :
    (l.map f).next (f x) hfx = f (l.next x hx) := by
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  have hmap : (l.map f).Nodup := List.Nodup.map_on hf hl
  have hi' : i < (l.map f).length := by simpa using hi
  have hgen : ∀ (y : β) (hy : y ∈ l.map f), y = (l.map f)[i]'hi' →
      (l.map f).next y hy = (l.map f)[(i + 1) % (l.map f).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi')) := by
    intro y hy hyi
    subst hyi
    exact List.next_getElem (l.map f) hmap i hi'
  have hgen' : ∀ (y : α) (hy : y ∈ l), y = l[i]'hi →
      l.next y hy = l[(i + 1) % l.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
    intro y hy hyi
    subst hyi
    exact List.next_getElem l hl i hi
  rw [hgen (f x) hfx (by rw [List.getElem_map, hxi]), hgen' x hx hxi.symm, List.getElem_map]
  simp only [List.length_map]

/-- `List.next` in a list with a fresh head `y`, at an element of the tail: it is the tail's own
successor, except that the tail's last element goes to `y` (whose successor is the tail's head). -/
theorem list_next_cons_of_mem (M : List α) (hM : M.Nodup) (y : α) (hy : y ∉ M)
    (x : α) (hx : x ∈ M) (hx' : x ∈ y :: M) :
    M.next x hx =
      if (y :: M).next x hx' = y then (y :: M).next y List.mem_cons_self
      else (y :: M).next x hx' := by
  have hN : (y :: M).Nodup := List.nodup_cons.mpr ⟨hy, hM⟩
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  have hi1 : i + 1 < (y :: M).length := by simp; omega
  have hgenM : ∀ (z : α) (hz : z ∈ M), z = M[i]'hi →
      M.next z hz = M[(i + 1) % M.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
    intro z hz hzi
    subst hzi
    exact List.next_getElem M hM i hi
  have hgenN : ∀ (z : α) (hz : z ∈ y :: M), z = (y :: M)[i + 1]'hi1 →
      (y :: M).next z hz = (y :: M)[(i + 1 + 1) % (y :: M).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hi1)) := by
    intro z hz hzi
    subst hzi
    exact List.next_getElem (y :: M) hN (i + 1) hi1
  have hxN : x = (y :: M)[i + 1]'hi1 := by rw [List.getElem_cons_succ]; exact hxi.symm
  rw [hgenM x hx hxi.symm, hgenN x hx' hxN]
  have hlen : (y :: M).length = M.length + 1 := rfl
  by_cases hlast : i + 1 < M.length
  · -- not the last element of `M`
    have h1 : (i + 1) % M.length = i + 1 := Nat.mod_eq_of_lt hlast
    have h2 : (i + 1 + 1) % (y :: M).length = i + 1 + 1 := by
      rw [hlen]; exact Nat.mod_eq_of_lt (by omega)
    have hne : (y :: M)[(i + 1 + 1) % (y :: M).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hi1)) ≠ y := by
      intro he
      apply hy
      have hmem : (y :: M)[(i + 1 + 1) % (y :: M).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hi1)) ∈ M := by
        have hidx : (i + 1 + 1) % (y :: M).length = (i + 1) + 1 := h2
        have hgetc : ∀ (k : ℕ) (hk : k < (y :: M).length), k = i + 1 + 1 →
            (y :: M)[k]'hk ∈ M := by
          intro k hk hk'
          subst hk'
          rw [List.getElem_cons_succ]
          exact List.getElem_mem _
        exact hgetc _ _ hidx
      rw [he] at hmem
      exact hmem
    rw [ite_eq_right hne]
    have hgetc : ∀ (k : ℕ) (hk : k < (y :: M).length), k = i + 1 + 1 →
        (y :: M)[k]'hk = M[i + 1]'hlast := by
      intro k hk hk'
      subst hk'
      exact List.getElem_cons_succ ..
    rw [hgetc _ _ h2]
    have hgetM : ∀ (k : ℕ) (hk : k < M.length), k = i + 1 → M[k]'hk = M[i + 1]'hlast := by
      intro k hk hk'
      subst hk'
      rfl
    exact hgetM _ _ h1
  · -- the last element of `M`
    have hil : i + 1 = M.length := by omega
    have hpos : 0 < M.length := by omega
    have h1 : (i + 1) % M.length = 0 := by rw [hil]; exact Nat.mod_self _
    have h2 : (i + 1 + 1) % (y :: M).length = 0 := by rw [hlen, hil]; exact Nat.mod_self _
    have hgety : ∀ (k : ℕ) (hk : k < (y :: M).length), k = 0 → (y :: M)[k]'hk = y := by
      intro k hk hk'
      subst hk'
      rfl
    rw [hgety _ _ h2, ite_eq_left rfl]
    have hgenY : (y :: M).next y List.mem_cons_self =
        (y :: M)[(0 + 1) % (y :: M).length]'(Nat.mod_lt _ (by simp)) :=
      List.next_getElem (y :: M) hN 0 (by simp)
    rw [hgenY]
    have h3 : (0 + 1) % (y :: M).length = 1 := by rw [hlen]; exact Nat.mod_eq_of_lt (by omega)
    have hget1 : ∀ (k : ℕ) (hk : k < (y :: M).length), k = 1 → (y :: M)[k]'hk = M[0]'hpos := by
      intro k hk hk'
      subst hk'
      exact List.getElem_cons_succ ..
    rw [hget1 _ _ h3]
    have hget0 : ∀ (k : ℕ) (hk : k < M.length), k = 0 → M[k]'hk = M[0]'hpos := by
      intro k hk hk'
      subst hk'
      rfl
    exact hget0 _ _ h1

/-- `List.next` on a nodup list with one element `y` erased: the successor of `x ≠ y` is the old
successor, or the old successor of `y` when the old successor of `x` is `y`. -/
theorem list_next_erase [BEq α] [LawfulBEq α] (l : List α) (hl : l.Nodup) (x y : α)
    (hx : x ∈ l) (hy : y ∈ l) (hx' : x ∈ l.erase y) :
    (l.erase y).next x hx' = if l.next x hx = y then l.next y hy else l.next x hx := by
  obtain ⟨B, A, hBA⟩ := List.append_of_mem hy
  have hl' : (B ++ y :: A).Nodup := hBA ▸ hl
  have hyB : y ∉ B := by
    intro hyB
    have := List.nodup_append.mp hl'
    exact this.2.2 y hyB y List.mem_cons_self rfl
  have herase : l.erase y = B ++ A := by
    rw [hBA, List.erase_append_right _ hyB, List.erase_cons_head]
  -- rotate `y` to the head
  have hrot : l ~r y :: (A ++ B) := by
    rw [hBA]
    have : B ++ y :: A = B ++ (y :: A) := rfl
    rw [this]
    have h2 : (y :: A) ++ B = y :: (A ++ B) := rfl
    rw [← h2]
    exact List.isRotated_append
  have hrotE : l.erase y ~r A ++ B := by
    rw [herase]
    exact List.isRotated_append
  have hM : (A ++ B).Nodup := hrotE.nodup_iff.mp (hl.erase y)
  have hyM : y ∉ A ++ B := by
    intro hyM
    have hN : (y :: (A ++ B)).Nodup := hrot.nodup_iff.mp hl
    exact (List.nodup_cons.mp hN).1 hyM
  have hxM : x ∈ A ++ B := hrotE.mem_iff.mp hx'
  have hxN : x ∈ y :: (A ++ B) := hrot.mem_iff.mp hx
  have hyN : y ∈ y :: (A ++ B) := List.mem_cons_self
  rw [List.isRotated_next_eq hrotE (hl.erase y) hx',
    List.isRotated_next_eq hrot hl hx, List.isRotated_next_eq hrot hl hy]
  exact list_next_cons_of_mem (A ++ B) hM y hyM x hxM hxN

end ListLemmas

/-! ## 2. `SameCycle` under a conjugating equivalence -/

section PermLemmas

/-- If `g ∘ e = e ∘ f` for an equivalence `e`, the cycles of `g` are the images of the cycles of
`f`. -/
theorem sameCycle_of_equiv_conj {α β : Type*} (f : Equiv.Perm α) (g : Equiv.Perm β) (e : α ≃ β)
    (h : ∀ a, g (e a) = e (f a)) (a b : α) : g.SameCycle (e a) (e b) ↔ f.SameCycle a b := by
  have hinv : ∀ a, g⁻¹ (e a) = e (f⁻¹ a) := by
    intro a
    rw [Equiv.Perm.inv_def, Equiv.Perm.inv_def, Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]
  have hz : ∀ (k : ℤ) (a : α), (g ^ k) (e a) = e ((f ^ k) a) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro a; simp
    | succ i ih =>
      intro a
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, ih]
    | pred i ih =>
      intro a
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, ih]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hz] at hk
    exact e.injective hk
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hz, hk]⟩

end PermLemmas

/-! ## 3. Intrinsic centre lemmas (any `hP : CrossingGeometry P`) -/

namespace GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- `successor_gap`: no mark lies strictly between a mark and its `ρ`-successor on the marked
traversal circle (port of `nextMark_no_mark_between` to the geometric record domain, through
`sorted_next_no_cyclic_between` on `geoMarkLinearOrder`). -/
theorem geoMarkSuccessor_no_mark_between (hP : CrossingGeometry P) (a u : Mark P) :
    ¬ traversalBetween (geoMarkPosition hP a) (geoMarkPosition hP u)
      (geoMarkPosition hP (geoMarkSuccessor hP a)) := by
  classical
  let d : DecidableEq (Mark P) := inferInstance
  let _ := geoMarkLinearOrder hP
  have hnext : (geoMarkList hP).next a (mem_geoMarkList hP a) = geoMarkSuccessor hP a := rfl
  have hnext' : @List.next (Mark P) d (Finset.univ : Finset (Mark P)).sort a
      ((Finset.mem_sort _).mpr (Finset.mem_univ a)) = geoMarkSuccessor hP a := hnext
  have hd : d = (fun a b : Mark P => LinearOrder.toDecidableEq a b) :=
    Subsingleton.elim _ _
  rw [hd] at hnext'
  have hg := sorted_next_no_cyclic_between (Finset.univ : Finset (Mark P))
    (Finset.mem_univ a) (Finset.mem_univ _) hnext' u (Finset.mem_univ u)
  exact hg

theorem geoMarkKey_vertex (hP : CrossingGeometry P) (i : ZMod n) :
    geoMarkKey hP (Sum.inl i) = (i.val : ℝ) := by
  simp [geoMarkKey, geoMarkPosition, traversalKey]

/-- A marked circle with at least two vertices has at least two marks. -/
theorem geoMarkList_two_le_length (hn : 2 ≤ n) (hP : CrossingGeometry P) :
    2 ≤ (geoMarkList hP).length := by
  have h01 : (Sum.inl (0 : ZMod n) : Mark P) ≠ Sum.inl 1 := by
    intro h
    have h' : (0 : ZMod n) = 1 := Sum.inl.inj h
    have hv := congrArg ZMod.val h'
    rw [ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    exact zero_ne_one hv
  have h0 := mem_geoMarkList hP (Sum.inl 0)
  have h1 := mem_geoMarkList hP (Sum.inl 1)
  rcases hL : geoMarkList hP with _ | ⟨z, _ | ⟨w, R⟩⟩
  · rw [hL] at h0
    simp at h0
  · rw [hL] at h0 h1
    simp only [List.mem_singleton] at h0 h1
    exact absurd (h0.trans h1.symm) h01
  · simp

/-- On a marked circle with at least two marks, no mark is its own `ρ`-successor. -/
theorem geoMarkSuccessor_ne_self (hn : 2 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    geoMarkSuccessor hP a ≠ a := by
  intro he
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem (mem_geoMarkList hP a)
  have hlen := geoMarkList_two_le_length hn hP
  have hgen : ∀ (y : Mark P), y = (geoMarkList hP)[i]'hi →
      geoMarkSuccessor hP y = (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
    intro y hy
    subst hy
    exact geoMarkSuccessor_getElem hP i hi
  have h2 := hgen a hia.symm
  rw [he] at h2
  rw [← hia] at h2
  have h3 := ((geoMarkList_nodup hP).getElem_inj_iff).mp h2
  by_cases hc : i + 1 < (geoMarkList hP).length
  · rw [Nat.mod_eq_of_lt hc] at h3
    omega
  · have hc' : i + 1 = (geoMarkList hP).length := by omega
    rw [hc', Nat.mod_self] at h3
    omega

theorem geoSmoothingSuccessor_vertex_ne_self (hn : 2 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    geoSmoothingSuccessor hP S (Sum.inl i) ≠ Sum.inl i :=
  geoMarkSuccessor_ne_self hn hP (Sum.inl i)

theorem zmod_val_add_one_of_lt {i : ZMod n} (h : i.val + 1 < n) : (i + 1).val = i.val + 1 := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < n),
    Nat.mod_eq_of_lt h]

theorem zmod_add_one_eq_zero_of_val {i : ZMod n} (h : i.val + 1 = n) : i + 1 = 0 := by
  have hcast : ((i.val + 1 : ℕ) : ZMod n) = 0 := by
    rw [h]
    exact ZMod.natCast_self n
  rw [← hcast]
  push_cast
  rw [ZMod.natCast_zmod_val]

/-- The `ρ`-successor of a mark lies on the closed edge segment of the mark's edge, at a parameter
not smaller than the mark's own (the same edge further on, or the next vertex). Intrinsic
consequence of `successor_gap`: an intermediate vertex would lie strictly between. -/
theorem geoMarkSuccessor_on_edge (hP : CrossingGeometry P) (a : Mark P) :
    ∃ t : ℝ, (geoMarkPosition hP a).2.val ≤ t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP (geoMarkSuccessor hP a)) =
        edgePoint P (geoMarkPosition hP a).1 t := by
  set p := geoMarkPosition hP a with hp
  set q := geoMarkPosition hP (geoMarkSuccessor hP a) with hq
  have hgap : ∀ u : Mark P, ¬ traversalBetween p (geoMarkPosition hP u) q :=
    geoMarkSuccessor_no_mark_between hP a
  have hkp : traversalKey p = (p.1.val : ℝ) + p.2.val := rfl
  have hkq : traversalKey q = (q.1.val : ℝ) + q.2.val := rfl
  have hkv : ∀ i : ZMod n, traversalKey (geoMarkPosition hP (Sum.inl i)) = (i.val : ℝ) := by
    intro i
    simp [geoMarkPosition, traversalKey]
  have hs0 : 0 ≤ p.2.val := p.2.property.1
  have hs1 : p.2.val < 1 := p.2.property.2
  have hu0 : 0 ≤ q.2.val := q.2.property.1
  have hu1 : q.2.val < 1 := q.2.property.2
  have hpn : p.1.val < n := ZMod.val_lt _
  have hqn : q.1.val < n := ZMod.val_lt _
  have hev : traversalEvaluation P q = edgePoint P q.1 q.2.val := rfl
  have hvert : ∀ i : ZMod n, edgePoint P (i + 1) 0 = edgePoint P i 1 := by
    intro i
    simp [edgePoint, edge]
  rcases lt_trichotomy (traversalKey p) (traversalKey q) with hlt | heq | hgt
  · -- `p` before `q`: no vertex strictly between
    have hno : ∀ i : ZMod n, ¬ (traversalKey p < (i.val : ℝ) ∧ (i.val : ℝ) < traversalKey q) := by
      intro i hi
      apply hgap (Sum.inl i)
      unfold traversalBetween
      rw [hkv]
      exact Or.inl hi
    by_cases hcut : p.1.val + 1 < n
    · have hvn : (p.1 + 1).val = p.1.val + 1 := zmod_val_add_one_of_lt hcut
      have h1 := hno (p.1 + 1)
      rw [hvn] at h1
      push_cast at h1
      have hle : traversalKey q ≤ (p.1.val : ℝ) + 1 :=
        le_of_not_gt (fun hcon => h1 ⟨by rw [hkp]; linarith, hcon⟩)
      have hq1 : q.1.val = p.1.val ∨ q.1.val = p.1.val + 1 := by
        rw [hkq] at hle
        rw [hkp, hkq] at hlt
        have h2 : (q.1.val : ℝ) ≤ (p.1.val : ℝ) + 1 := by linarith
        have h3 : (p.1.val : ℝ) < (q.1.val : ℝ) + 1 := by linarith
        have h2' : q.1.val ≤ p.1.val + 1 := by exact_mod_cast h2
        have h3' : p.1.val < q.1.val + 1 := by exact_mod_cast h3
        omega
      rcases hq1 with h | h
      · have hqp : q.1 = p.1 := ZMod.val_injective n h
        refine ⟨q.2.val, ?_, hu1.le, by rw [hev, hqp]⟩
        rw [hkp, hkq, h] at hlt
        linarith
      · have hqp : q.1 = p.1 + 1 := ZMod.val_injective n (h.trans hvn.symm)
        have hq20 : q.2.val = 0 := by
          rw [hkq, h] at hle
          push_cast at hle
          linarith
        refine ⟨1, hs1.le, le_refl 1, ?_⟩
        rw [hev, hqp, hq20, hvert]
    · have hcut' : p.1.val + 1 = n := by omega
      have hqp : q.1 = p.1 := by
        apply ZMod.val_injective n
        rw [hkp, hkq] at hlt
        have h3 : (p.1.val : ℝ) < (q.1.val : ℝ) + 1 := by linarith
        have h3' : p.1.val < q.1.val + 1 := by exact_mod_cast h3
        omega
      refine ⟨q.2.val, ?_, hu1.le, by rw [hev, hqp]⟩
      rw [hkp, hkq, hqp] at hlt
      linarith
  · -- equal keys: `q = p`
    have hpq : p = q := traversalKey_injective heq
    exact ⟨p.2.val, le_refl _, hs1.le, by rw [hev, ← hpq]⟩
  · -- `q` before `p`: every mark lies between `q` and `p`
    have hno : ∀ i : ZMod n,
        ¬ ((i.val : ℝ) < traversalKey q) ∧ ¬ (traversalKey p < (i.val : ℝ)) := by
      intro i
      constructor
      · intro hi
        apply hgap (Sum.inl i)
        unfold traversalBetween
        rw [hkv]
        exact Or.inr (Or.inl ⟨hi, hgt⟩)
      · intro hi
        apply hgap (Sum.inl i)
        unfold traversalBetween
        rw [hkv]
        exact Or.inr (Or.inr ⟨hgt, hi⟩)
    have h0 : traversalKey q ≤ 0 := by
      have h0' := (hno 0).1
      rw [ZMod.val_zero] at h0'
      push_cast at h0'
      exact not_lt.mp h0'
    have hq10 : q.1.val = 0 := by
      rw [hkq] at h0
      have h0' : (q.1.val : ℝ) ≤ 0 := by linarith
      have h0'' : q.1.val ≤ 0 := by exact_mod_cast h0'
      omega
    have hq20 : q.2.val = 0 := by
      rw [hkq, hq10] at h0
      push_cast at h0
      linarith
    have hcut : p.1.val + 1 = n := by
      by_contra hne
      have hcut' : p.1.val + 1 < n := by omega
      have hvn : (p.1 + 1).val = p.1.val + 1 := zmod_val_add_one_of_lt hcut'
      have h1 := not_lt.mp (hno (p.1 + 1)).2
      rw [hvn, hkp] at h1
      push_cast at h1
      linarith
    have hq1 : q.1 = p.1 + 1 := by
      rw [zmod_add_one_eq_zero_of_val hcut]
      exact (ZMod.val_eq_zero q.1).mp hq10
    refine ⟨1, hs1.le, le_refl 1, ?_⟩
    rw [hev, hq1, hq20, hvert]

/-- The two visits of a crossing evaluate to the same plane point, so the outgoing slot of a mark
(the mark itself, or its twin at a selected visit) has the mark's plane point. -/
theorem geoMarkPosition_evaluation_selectedMarkPerm (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP (selectedMarkPerm S a)) =
      traversalEvaluation P (geoMarkPosition hP a) := by
  cases a with
  | inl i => rfl
  | inr v =>
    rw [selectedMarkPerm_visit, geoMarkPosition_evaluation_visit,
      geoMarkPosition_evaluation_visit, selectedVisitTwin_crossing]

/-- `inherited_pieces`: the straight subsegment from a mark to its `ρ_S`-successor lies in the
closed edge segment of the edge of the outgoing slot. -/
theorem geoSmoothingSegment_mem_edgeSegment (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    geoSmoothingSegment hP S a u ∈ edgeSegment P (geoMarkPosition hP (selectedMarkPerm S a)).1 := by
  obtain ⟨t, hst, ht1, hev⟩ := geoMarkSuccessor_on_edge hP (selectedMarkPerm S a)
  have hs0 : 0 ≤ (geoMarkPosition hP (selectedMarkPerm S a)).2.val :=
    (geoMarkPosition hP (selectedMarkPerm S a)).2.property.1
  have hpa : traversalEvaluation P (geoMarkPosition hP a) =
      edgePoint P (geoMarkPosition hP (selectedMarkPerm S a)).1
        (geoMarkPosition hP (selectedMarkPerm S a)).2.val := by
    rw [← geoMarkPosition_evaluation_selectedMarkPerm hP S a]
    rfl
  have hsucc : geoSmoothingSuccessor hP S a = geoMarkSuccessor hP (selectedMarkPerm S a) := rfl
  refine ⟨(geoMarkPosition hP (selectedMarkPerm S a)).2.val +
    u * (t - (geoMarkPosition hP (selectedMarkPerm S a)).2.val), ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [geoSmoothingSegment, hsucc, hev, hpa]
    simp only [edgePoint]
    module

/-- Every field of `GeoCarrierSpec` except `traced_successor` is intrinsic to the geometric record
domain; `traced_successor` is supplied (at the centre: by transport from a side). -/
theorem geoCarrierSpec_of_traced_successor (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (hts : ∀ (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length),
      geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
        (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))) :
    GeoCarrierSpec hP S where
  mark_vertex i := ⟨geoMarkPosition_evaluation_vertex hP i, rfl, rfl⟩
  mark_visit v := ⟨geoMarkPosition_evaluation_visit hP v, rfl, rfl,
    (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1,
    (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).2⟩
  marks_injective := geoMarkPosition_injective hP
  successor_gap := geoMarkSuccessor_no_mark_between hP
  reconnection _ := rfl
  reconnect_selected v hv := ⟨geoSmoothingSuccessor_visit_of_mem hP S v hv, by
    rw [geoSmoothingSuccessor_visit_of_mem hP S (visitTwin v)
      (by rw [visitTwin_crossing]; exact hv), visitTwin_involutive]⟩
  keep_unselected v hv := geoSmoothingSuccessor_visit_of_not_mem hP S v hv
  keep_vertex _ := rfl
  carriers := geoOwner_eq_iff hP S
  traced_curve _ := rfl
  traced_marks q := ⟨geoComponentMarkList_nodup hP S q, geoComponentMarkList_length_pos hP S q,
    mem_geoComponentMarkList hP S q⟩
  traced_successor := hts
  straight_pieces _ _ := rfl
  inherited_pieces a u hu0 hu1 := geoSmoothingSegment_mem_edgeSegment hP S a u hu0 hu1
  corners _ := rfl
  corner_vertex i := isTrueCorner_vertex S i
  corner_visit v := isTrueCorner_visit S v

end
end GeoCarrier

/-! ## 4. Side ↔ centre: transport of the reconnection along `markTransport` -/

section SideTransport

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {m : ℕ} [NeZero m] {P Q : LabelledTuple m}

omit [NeZero m] in
/-- The visit identification commutes with the pairing of the two visits of a crossing
(`common_gauss_word.4`, `same_pairing.1`). -/
theorem visitTransport_visitTwin (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (v : Visit P) :
    visitTransport hs (visitTwin v) = visitTwin (visitTransport hs v) := by
  apply visitTwin_unique
  · rw [visitTransport_crossing, visitTransport_crossing, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v ((visitTransport hs).injective h)

omit [NeZero m] in
theorem mem_transportSupport_iff (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) (x : Crossing P) :
    crossingTransport hs x ∈ transportSupport hs S ↔ x ∈ S := by
  unfold transportSupport
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]

omit [NeZero m] in
theorem markTransport_vertex (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (i : ZMod m) :
    markTransport hs (Sum.inl i) = Sum.inl i := rfl

omit [NeZero m] in
theorem markTransport_visit (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (v : Visit P) :
    markTransport hs (Sum.inr v) = Sum.inr (visitTransport hs v) := rfl

/-- The selected exchange commutes with the identification of marks. -/
theorem selectedMarkPerm_markTransport (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) (a : Mark P) :
    selectedMarkPerm (transportSupport hs S) (markTransport hs a) =
      markTransport hs (selectedMarkPerm S a) := by
  cases a with
  | inl i => rfl
  | inr v =>
    rw [markTransport_visit, selectedMarkPerm_visit, selectedMarkPerm_visit, markTransport_visit]
    congr 1
    by_cases hv : v.1 ∈ S
    · have hv' : (visitTransport hs v).1 ∈ transportSupport hs S := by
        rw [visitTransport_crossing, mem_transportSupport_iff]
        exact hv
      rw [selectedVisitTwin_of_mem _ _ hv', selectedVisitTwin_of_mem _ _ hv,
        visitTransport_visitTwin]
    · have hv' : (visitTransport hs v).1 ∉ transportSupport hs S := by
        rw [visitTransport_crossing, mem_transportSupport_iff]
        exact hv
      rw [selectedVisitTwin_of_not_mem _ _ hv', selectedVisitTwin_of_not_mem _ _ hv]

/-- `ρ` commutes with the identification once the marked circles correspond (U1's
`identify_sides_marks`): `List.next` commutes with an injective map. -/
theorem geoMarkSuccessor_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ) (a : Mark P) :
    geoMarkSuccessor hQ (markTransport hs a) = markTransport hs (geoMarkSuccessor hP a) := by
  rw [geoMarkSuccessor_apply, geoMarkSuccessor_apply, geoNextMark_eq_list_next,
    geoNextMark_eq_list_next]
  have hmem : markTransport hs a ∈ (geoMarkList hP).map (markTransport hs) :=
    List.mem_map_of_mem (mem_geoMarkList hP a)
  rw [list_next_congr hmarks.symm (markTransport hs a) _ hmem]
  exact list_next_map (markTransport hs) (geoMarkList hP) (geoMarkList_nodup hP)
    (fun x _ y _ h => (markTransport hs).injective h) a (mem_geoMarkList hP a) hmem

/-- `ρ_S` commutes with the identification (`correspond_sides.1`). -/
theorem geoSmoothingSuccessor_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoSmoothingSuccessor hQ (transportSupport hs S) (markTransport hs a) =
      markTransport hs (geoSmoothingSuccessor hP S a) := by
  rw [geoSmoothingSuccessor_apply, geoSmoothingSuccessor_apply, selectedMarkPerm_markTransport,
    geoMarkSuccessor_markTransport hP hQ hs hmarks]

/-- Two marks lie on one carrier iff their images do (`correspond_sides.2`). -/
theorem geoOwner_markTransport_iff (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a a' : Mark P) :
    geoOwner hP S a = geoOwner hP S a' ↔
      geoOwner hQ (transportSupport hs S) (markTransport hs a) =
        geoOwner hQ (transportSupport hs S) (markTransport hs a') := by
  rw [geoOwner_eq_iff, geoOwner_eq_iff]
  exact (sameCycle_of_equiv_conj (geoSmoothingSuccessor hP S)
    (geoSmoothingSuccessor hQ (transportSupport hs S)) (markTransport hs)
    (geoSmoothingSuccessor_markTransport hP hQ hs hmarks S) a a').symm

/-- The marks of a carrier transport, in inherited order, to the marks of its copy. -/
theorem geoComponentMarkList_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a : Mark P) :
    (geoComponentMarkList hP S (geoOwner hP S a)).map (markTransport hs) =
      geoComponentMarkList hQ (transportSupport hs S)
        (geoOwner hQ (transportSupport hs S) (markTransport hs a)) := by
  unfold geoComponentMarkList
  rw [← hmarks, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp]
  exact decide_eq_decide.mpr (geoOwner_markTransport_iff hP hQ hs hmarks S x a)

theorem isTrueCorner_markTransport (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) (a : Mark P) :
    IsTrueCorner (transportSupport hs S) (markTransport hs a) ↔ IsTrueCorner S a := by
  cases a with
  | inl i => exact Iff.rfl
  | inr v =>
    rw [markTransport_visit, isTrueCorner_visit, isTrueCorner_visit, visitTransport_crossing,
      mem_transportSupport_iff]

/-- The corners of a carrier transport, in inherited order, to the corners of its copy. -/
theorem geoComponentCornerList_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a : Mark P) :
    (geoComponentCornerList hP S (geoOwner hP S a)).map (markTransport hs) =
      geoComponentCornerList hQ (transportSupport hs S)
        (geoOwner hQ (transportSupport hs S) (markTransport hs a)) := by
  unfold geoComponentCornerList
  rw [← geoComponentMarkList_markTransport hP hQ hs hmarks S a, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp]
  exact decide_eq_decide.mpr (isTrueCorner_markTransport hs S x).symm

theorem geoCornerCount_markTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoCornerCount hP S (geoOwner hP S a) =
      geoCornerCount hQ (transportSupport hs S)
        (geoOwner hQ (transportSupport hs S) (markTransport hs a)) := by
  unfold geoCornerCount
  rw [← geoComponentCornerList_markTransport hP hQ hs hmarks S a, List.length_map]

/-- `traced_successor` transports back along the identification: if consecutive marks of every
carrier of `Q` are `ρ_S`-successors, so are those of every carrier of `P`. -/
theorem traced_successor_of_transport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hmarks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ)
    (S : Finset (Crossing P))
    (hQts : ∀ (q : GeoComponent hQ (transportSupport hs S))
      (i : Fin (geoComponentMarkList hQ (transportSupport hs S) q).length),
      geoSmoothingSuccessor hQ (transportSupport hs S)
          ((geoComponentMarkList hQ (transportSupport hs S) q)[i.val]'i.isLt) =
        (geoComponentMarkList hQ (transportSupport hs S) q)[(i.val + 1) %
          (geoComponentMarkList hQ (transportSupport hs S) q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))) :
    ∀ (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length),
      geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
        (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)) := by
  intro q i
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP S q
  have hL := geoComponentMarkList_markTransport hP hQ hs hmarks S a
  have hgen : ∀ (l : List (Mark Q)),
      l = geoComponentMarkList hQ (transportSupport hs S)
        (geoOwner hQ (transportSupport hs S) (markTransport hs a)) →
      ∀ (k : ℕ) (hk : k < l.length),
        geoSmoothingSuccessor hQ (transportSupport hs S) (l[k]'hk) =
          l[(k + 1) % l.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le k) hk)) := by
    intro l hl k hk
    subst hl
    exact hQts _ ⟨k, hk⟩
  have h := hgen _ hL i.val (by rw [List.length_map]; exact i.isLt)
  simp only [List.getElem_map] at h
  rw [geoSmoothingSuccessor_markTransport hP hQ hs hmarks S] at h
  have h' := (markTransport hs).injective h
  simpa only [List.length_map] using h'

end
end SideTransport

/-! ## 4b. The flat instantiation: `correspond_sides`, the centre `GeoCarrierSpec` -/

section FlatSides

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- cor:flat-carriers (i), sides: `correspond_sides`, from U1's `identify_sides_marks`. -/
theorem correspond_sides_of_marks (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center))
    (identify_sides_marks : ∀ b : Bool,
      (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
        geoMarkList (flatSideCG hn g b t)) :
    ∀ b : Bool,
    (∀ a : Mark g.center,
      geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
          (markTransport (hs b) a) =
        markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
    (∀ a a' : Mark g.center,
      geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a')) :=
  fun b =>
    ⟨geoSmoothingSuccessor_markTransport _ _ (hs b) (identify_sides_marks b) S,
     geoOwner_markTransport_iff _ _ (hs b) (identify_sides_marks b) S⟩

/-- On a generic side, consecutive marks of a carrier are `ρ_S`-successors (the accepted
`componentMarkList_getElem_successor`, for a decomposition). -/
theorem side_traced_successor (hn : 3 ≤ n) (g : WallGerm (n + 1)) (b : Bool)
    (t : g.SideParameter) (S_T : Finset (Crossing (g.sideTuple b t).val))
    (hST : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property S_T) :
    ∀ (q : GeoComponent (flatSideCG hn g b t) S_T)
      (i : Fin (geoComponentMarkList (flatSideCG hn g b t) S_T q).length),
      geoSmoothingSuccessor (flatSideCG hn g b t) S_T
          ((geoComponentMarkList (flatSideCG hn g b t) S_T q)[i.val]'i.isLt) =
        (geoComponentMarkList (flatSideCG hn g b t) S_T q)[(i.val + 1) %
          (geoComponentMarkList (flatSideCG hn g b t) S_T q).length]'
          (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)) := by
  intro q i
  have hgen : ∀ (l : List (Mark (g.sideTuple b t).val)),
      l = componentMarkList (flat_hn1 hn) (g.sideTuple b t).property S_T
        (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property S_T q) →
      ∀ (k : ℕ) (hk : k < l.length),
        smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property S_T (l[k]'hk) =
          l[(k + 1) % l.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le k) hk)) := by
    intro l hl k hk
    subst hl
    exact componentMarkList_getElem_successor (flat_hn1 hn) (g.sideTuple b t).property hST _
      ⟨k, hk⟩
  have h := hgen _ (geoComponentMarkList_eq_generic (flat_hn1 hn) (g.sideTuple b t).property S_T q)
    i.val i.isLt
  rw [← geoSmoothingSuccessor_eq_generic (flat_hn1 hn) (g.sideTuple b t).property S_T] at h
  exact h

/-- def:flat-carriers sentence 2 at the centre: `centre_carriers : GeoCarrierSpec C S`, from U1's
`identify_sides_marks` (one side) and `independent_supports` (that side's `S_T` is a
decomposition). -/
theorem centre_carriers_of_marks (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) (b : Bool)
    (identify_sides_marks :
      (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
        geoMarkList (flatSideCG hn g b t))
    (independent_supports :
      IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S :=
  geoCarrierSpec_of_traced_successor _ S
    (traced_successor_of_transport _ _ (hs b) identify_sides_marks S
      (side_traced_successor hn g b t _ independent_supports))

end FlatSides

/-! ## 5. Centre ↔ deletion: the skip-`μ_j` conjugation -/

section Deletion

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- `fusionVisit_crossing`, restated with the germ's `hz` so that `rw` matches syntactically. -/
theorem fusionVisitEquiv_fst (v : Visit g.center) :
    (fusionVisitEquiv hn hz hb hc v).1 = fusionCrossingEquiv hn hz hb hc v.1 := rfl

/-- The fused-edge identification commutes with the pairing of the two visits of a crossing
(`common_gauss_word.5`, `same_pairing.2`). -/
theorem fusionVisitEquiv_visitTwin (v : Visit g.center) :
    fusionVisitEquiv hn hz hb hc (visitTwin v) = visitTwin (fusionVisitEquiv hn hz hb hc v) := by
  apply visitTwin_unique
  · rw [fusionVisitEquiv_fst, fusionVisitEquiv_fst, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v ((fusionVisitEquiv hn hz hb hc).injective h)

theorem mem_deletionSupport_iff (S : Finset (Crossing g.center)) (x : Crossing g.center) :
    fusionCrossingEquiv hn hz hb hc x ∈ deletionSupport hn g j hz hb hc S ↔ x ∈ S := by
  unfold deletionSupport
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem delMark_vertex (k : ZMod (n + 1)) :
    delMark hn g j hz hb hc (Sum.inl k) = Sum.inl (fusionIndex j k) := rfl

theorem delMark_visit (v : Visit g.center) :
    delMark hn g j hz hb hc (Sum.inr v) = Sum.inr (fusionVisitEquiv hn hz hb hc v) := rfl

theorem fusionMark_vertex (i : ZMod n) :
    fusionMark hn g j hz hb hc (Sum.inl i) = Sum.inl (deletionIndex j i) := rfl

theorem fusionMark_visit (w : Visit (deleteVertex g.center j)) :
    fusionMark hn g j hz hb hc (Sum.inr w) = Sum.inr ((fusionVisitEquiv hn hz hb hc).symm w) := rfl

/-- The selected exchange commutes with `delMark`. -/
theorem selectedMarkPerm_delMark (S : Finset (Crossing g.center)) (a : Mark g.center) :
    selectedMarkPerm (deletionSupport hn g j hz hb hc S) (delMark hn g j hz hb hc a) =
      delMark hn g j hz hb hc (selectedMarkPerm S a) := by
  cases a with
  | inl k => rfl
  | inr v =>
    rw [delMark_visit, selectedMarkPerm_visit, selectedMarkPerm_visit, delMark_visit]
    congr 1
    by_cases hv : v.1 ∈ S
    · have hv' : (fusionVisitEquiv hn hz hb hc v).1 ∈ deletionSupport hn g j hz hb hc S := by
        rw [fusionVisitEquiv_fst, mem_deletionSupport_iff]
        exact hv
      rw [selectedVisitTwin_of_mem _ _ hv', selectedVisitTwin_of_mem _ _ hv,
        fusionVisitEquiv_visitTwin]
    · have hv' : (fusionVisitEquiv hn hz hb hc v).1 ∉ deletionSupport hn g j hz hb hc S := by
        rw [fusionVisitEquiv_fst, mem_deletionSupport_iff]
        exact hv
      rw [selectedVisitTwin_of_not_mem _ _ hv', selectedVisitTwin_of_not_mem _ _ hv]

omit [NeZero n] hn hz hb hc in
theorem selectedMarkPerm_ne_deleted (S : Finset (Crossing g.center)) (a : Mark g.center)
    (ha : a ≠ Sum.inl j) : selectedMarkPerm S a ≠ Sum.inl j := by
  cases a with
  | inl k => exact ha
  | inr v => exact Sum.inr_ne_inl

/-- `ρ` on the deletion, read at the centre through `delMark`, from U1's `identify_deletion_marks`:
the centre successor, skipping the erased mark `μ_j`. -/
theorem geoMarkSuccessor_delMark
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (a : Mark g.center) (ha : a ≠ Sum.inl j) :
    geoMarkSuccessor (flatDeletionCG hn g j hz hb hc) (delMark hn g j hz hb hc a) =
      delMark hn g j hz hb hc
        (if geoMarkSuccessor (flatCentreCG hn g j hz hb hc) a = Sum.inl j
          then geoMarkSuccessor (flatCentreCG hn g j hz hb hc) (Sum.inl j)
          else geoMarkSuccessor (flatCentreCG hn g j hz hb hc) a) := by
  have hrot : (((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
      (delMark hn g j hz hb hc)) ~r geoMarkList (flatDeletionCG hn g j hz hb hc) :=
    Cycle.coe_eq_coe.mp identify_deletion_marks
  have hnodC := geoMarkList_nodup (flatCentreCG hn g j hz hb hc)
  have haE : a ∈ (geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j) :=
    (List.mem_erase_of_ne ha).mpr (mem_geoMarkList _ a)
  have hmemM : delMark hn g j hz hb hc a ∈
      ((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) :=
    List.mem_map_of_mem haE
  have hinj : ∀ x ∈ (geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j),
      ∀ y ∈ (geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j),
      delMark hn g j hz hb hc x = delMark hn g j hz hb hc y → x = y := by
    intro x hx y hy hxy
    have hx' : x ≠ Sum.inl j := (hnodC.mem_erase_iff.mp hx).1
    have hy' : y ≠ Sum.inl j := (hnodC.mem_erase_iff.mp hy).1
    rw [← fusionMark_delMark hn g j hz hb hc x hx', ← fusionMark_delMark hn g j hz hb hc y hy',
      hxy]
  have hnodM := List.Nodup.map_on hinj (hnodC.erase (Sum.inl j))
  rw [geoMarkSuccessor_apply, geoNextMark_eq_list_next,
    ← List.isRotated_next_eq hrot hnodM hmemM,
    list_next_map _ _ (hnodC.erase (Sum.inl j)) hinj a haE hmemM,
    list_next_erase _ hnodC a (Sum.inl j) (mem_geoMarkList _ a) (mem_geoMarkList _ _) haE]
  rfl

/-- The reconnected centre successor with the mark `μ_j` skipped:
`ρ_S ∘ swap (μ_j, ρ_S⁻¹ μ_j)`. It fixes `μ_j`, and elsewhere follows `ρ_S`, jumping over `μ_j`. -/
def skipJ (S : Finset (Crossing g.center)) : Equiv.Perm (Mark g.center) :=
  (Equiv.swap (Sum.inl j)
    ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))).trans
    (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S)

omit [NeZero n] in
theorem skipJ_apply (S : Finset (Crossing g.center)) (x : Mark g.center) :
    skipJ hn g j hz hb hc S x =
      geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S
        (Equiv.swap (Sum.inl j)
          ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j)) x) := rfl

omit [NeZero n] in
theorem skipJ_deleted (S : Finset (Crossing g.center)) :
    skipJ hn g j hz hb hc S (Sum.inl j) = Sum.inl j := by
  rw [skipJ_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

omit [NeZero n] in
theorem skipJ_apply_of_ne (S : Finset (Crossing g.center)) (x : Mark g.center)
    (hx : x ≠ Sum.inl j) :
    skipJ hn g j hz hb hc S x =
      if geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S x = Sum.inl j
        then geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
        else geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S x := by
  rw [skipJ_apply]
  by_cases h : geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S x = Sum.inl j
  · rw [ite_eq_left h]
    have hx' : x = (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j) := by
      rw [← h, Equiv.symm_apply_apply]
    rw [hx', Equiv.swap_apply_right]
  · rw [ite_eq_right h]
    have hxp : x ≠ (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j) := by
      intro he
      apply h
      rw [he, Equiv.apply_symm_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hx hxp]

omit [NeZero n] in
theorem skipJ_ne_deleted_iff (S : Finset (Crossing g.center)) (x : Mark g.center) :
    skipJ hn g j hz hb hc S x ≠ Sum.inl j ↔ x ≠ Sum.inl j := by
  constructor
  · intro h hx
    apply h
    rw [hx, skipJ_deleted]
  · intro hx h
    exact hx ((skipJ hn g j hz hb hc S).injective (h.trans (skipJ_deleted hn g j hz hb hc S).symm))

/-- `ρ_S` on the deletion is the skip-`μ_j` centre successor read through `fusionMark`/`delMark`. -/
theorem geoSmoothingSuccessor_deletion (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b : Mark (deleteVertex g.center j)) :
    geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
      delMark hn g j hz hb hc (skipJ hn g j hz hb hc S (fusionMark hn g j hz hb hc b)) := by
  have hb' : fusionMark hn g j hz hb hc b ≠ Sum.inl j := fusionMark_ne_deleted hn g j hz hb hc b
  rw [skipJ_apply_of_ne hn g j hz hb hc S _ hb', geoSmoothingSuccessor_apply]
  have h1 : selectedMarkPerm (deletionSupport hn g j hz hb hc S) b =
      delMark hn g j hz hb hc (selectedMarkPerm S (fusionMark hn g j hz hb hc b)) := by
    rw [← selectedMarkPerm_delMark hn g j hz hb hc S (fusionMark hn g j hz hb hc b),
      delMark_fusionMark]
  rw [h1, geoMarkSuccessor_delMark hn g j hz hb hc identify_deletion_marks _
    (selectedMarkPerm_ne_deleted g j S _ hb')]
  rfl

/-- `correspond_deletion.1`: the deletion's arc from a mark is the centre's arc from the same
mark, skipping `μ_j`. -/
theorem correspond_deletion_successor (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    ∀ b : Mark (deleteVertex g.center j),
      geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        delMark hn g j hz hb hc
          (if geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
              Sum.inl j
            then geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
            else geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S
              (fusionMark hn g j hz hb hc b)) := by
  intro b
  rw [geoSmoothingSuccessor_deletion hn g j hz hb hc S identify_deletion_marks b,
    skipJ_apply_of_ne hn g j hz hb hc S _ (fusionMark_ne_deleted hn g j hz hb hc b)]

omit [NeZero n] in
/-- Away from `μ_j`, the cycles of the skip permutation are the cycles of `ρ_S` (with `μ_j`
removed). -/
theorem sameCycle_skipJ_iff (S : Finset (Crossing g.center)) (x y : Mark g.center)
    (hx : x ≠ Sum.inl j) (hy : y ≠ Sum.inl j) :
    (skipJ hn g j hz hb hc S).SameCycle x y ↔
      (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).SameCycle x y := by
  set ρ := geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S with hρ
  set σ := skipJ hn g j hz hb hc S with hσ
  constructor
  · intro h
    obtain ⟨k, _, hk⟩ := h.exists_pow_eq'
    have hstep : ∀ z, ρ.SameCycle z (σ z) := by
      intro z
      by_cases hzj : z = Sum.inl j
      · rw [hzj, hσ, skipJ_deleted]
      · rw [hσ, skipJ_apply_of_ne hn g j hz hb hc S z hzj]
        split_ifs with h1
        · rw [← h1]
          exact ⟨2, by rw [zpow_two, Equiv.Perm.mul_apply]⟩
        · exact ⟨1, by rw [zpow_one]⟩
    have hpow : ∀ (m : ℕ) (z : Mark g.center), ρ.SameCycle z ((σ ^ m) z) := by
      intro m
      induction m with
      | zero =>
        intro z
        simp only [pow_zero, Equiv.Perm.one_apply]
        exact Equiv.Perm.SameCycle.refl _ _
      | succ m ih =>
        intro z
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact (ih z).trans (hstep _)
    rw [← hk]
    exact hpow k x
  · intro h
    obtain ⟨k, _, hk⟩ := h.exists_pow_eq'
    have hQ : ∀ (m : ℕ),
        ((ρ ^ m) x ≠ Sum.inl j → σ.SameCycle x ((ρ ^ m) x)) ∧
        ((ρ ^ m) x = Sum.inl j → σ.SameCycle x (ρ (Sum.inl j))) := by
      intro m
      induction m with
      | zero =>
        simp only [pow_zero, Equiv.Perm.one_apply]
        exact ⟨fun _ => Equiv.Perm.SameCycle.refl _ _, fun h0 => absurd h0 hx⟩
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        by_cases hzj : (ρ ^ m) x = Sum.inl j
        · have h2 := ih.2 hzj
          rw [hzj]
          exact ⟨fun _ => h2, fun _ => h2⟩
        · have h1 := ih.1 hzj
          constructor
          · intro hne
            have hs : σ ((ρ ^ m) x) = ρ ((ρ ^ m) x) := by
              rw [hσ, skipJ_apply_of_ne hn g j hz hb hc S _ hzj, ite_eq_right hne]
            rw [← hs]
            exact Equiv.Perm.sameCycle_apply_right.mpr h1
          · intro heq
            have hs : σ ((ρ ^ m) x) = ρ (Sum.inl j) := by
              rw [hσ, skipJ_apply_of_ne hn g j hz hb hc S _ hzj, ite_eq_left heq]
            rw [← hs]
            exact Equiv.Perm.sameCycle_apply_right.mpr h1
    have hfin := (hQ k).1 (by rw [hk]; exact hy)
    rw [hk] at hfin
    exact hfin

/-- `correspond_deletion.2`: two deletion marks lie on one carrier iff their centre images do. -/
theorem geoOwner_deletion_iff (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b b' : Mark (deleteVertex g.center j)) :
    geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b' ↔
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b') := by
  rw [geoOwner_eq_iff, geoOwner_eq_iff]
  set σ := skipJ hn g j hz hb hc S with hσ
  have hU : ∀ x, σ x ≠ Sum.inl j ↔ x ≠ Sum.inl j := skipJ_ne_deleted_iff hn g j hz hb hc S
  let e : Mark (deleteVertex g.center j) ≃ {x : Mark g.center // x ≠ Sum.inl j} :=
    { toFun := fun b => ⟨fusionMark hn g j hz hb hc b, fusionMark_ne_deleted hn g j hz hb hc b⟩
      invFun := fun x => delMark hn g j hz hb hc x.1
      left_inv := fun b => delMark_fusionMark hn g j hz hb hc b
      right_inv := fun x => Subtype.ext (fusionMark_delMark hn g j hz hb hc x.1 x.2) }
  have hconj : ∀ b, (σ.subtypePerm hU) (e b) =
      e (geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) b) := by
    intro b
    apply Subtype.ext
    change σ (fusionMark hn g j hz hb hc b) =
      fusionMark hn g j hz hb hc (geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) b)
    rw [geoSmoothingSuccessor_deletion hn g j hz hb hc S identify_deletion_marks b,
      fusionMark_delMark hn g j hz hb hc _ ((hU _).mpr (fusionMark_ne_deleted hn g j hz hb hc b))]
  rw [← sameCycle_of_equiv_conj _ (σ.subtypePerm hU) e hconj b b',
    Equiv.Perm.sameCycle_subtypePerm]
  exact sameCycle_skipJ_iff hn g j hz hb hc S _ _ (fusionMark_ne_deleted hn g j hz hb hc b)
    (fusionMark_ne_deleted hn g j hz hb hc b')

omit [NeZero n] in
/-- `central_vs_deletion_through_mu_j.1`: the mark after `μ_j` is not `μ_j`. -/
theorem geoSmoothingSuccessor_deleted_ne (S : Finset (Crossing g.center)) :
    geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j :=
  geoSmoothingSuccessor_vertex_ne_self (by omega) _ S j

/-- `correspond_deletion.3`: every centre carrier is the centre copy of a deletion carrier. -/
theorem centre_carrier_surjective_deletion (S : Finset (Crossing g.center)) :
    ∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      ∃ b : Mark (deleteVertex g.center j),
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) = q := by
  intro q
  obtain ⟨a, ha⟩ := geoOwner_surjective _ S q
  by_cases haj : a = Sum.inl j
  · refine ⟨delMark hn g j hz hb hc (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a), ?_⟩
    rw [fusionMark_delMark hn g j hz hb hc _
      (by rw [haj]; exact geoSmoothingSuccessor_deleted_ne hn g j hz hb hc S),
      geoOwner_successor, ha]
  · exact ⟨delMark hn g j hz hb hc a, by rw [fusionMark_delMark hn g j hz hb hc a haj, ha]⟩

/-- cor:flat-carriers (i), deletion: `correspond_deletion`, from U1's `identify_deletion_marks`. -/
theorem correspond_deletion_of_marks (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    (∀ b : Mark (deleteVertex g.center j),
      geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        delMark hn g j hz hb hc
          (if geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
              Sum.inl j
            then geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
            else geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S
              (fusionMark hn g j hz hb hc b))) ∧
    (∀ b b' : Mark (deleteVertex g.center j),
      geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b' ↔
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) ∧
    (∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      ∃ b : Mark (deleteVertex g.center j),
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) = q) :=
  ⟨correspond_deletion_successor hn g j hz hb hc S identify_deletion_marks,
   geoOwner_deletion_iff hn g j hz hb hc S identify_deletion_marks,
   centre_carrier_surjective_deletion hn g j hz hb hc S⟩

/-! ### Cycle identities -/

/-- The marks of a deletion carrier are, up to rotation, the marks of its centre copy with `μ_j`
erased, read on the deletion. -/
theorem geoComponentMarkList_deletion_rotated (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b : Mark (deleteVertex g.center j)) :
    geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) ~r
      ((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).erase
          (Sum.inl j)).map (delMark hn g j hz hb hc) := by
  have hrot : (((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
      (delMark hn g j hz hb hc)) ~r geoMarkList (flatDeletionCG hn g j hz hb hc) :=
    Cycle.coe_eq_coe.mp identify_deletion_marks
  have hnodC := geoMarkList_nodup (flatCentreCG hn g j hz hb hc)
  unfold geoComponentMarkList
  refine (hrot.symm.filter _).trans ?_
  rw [List.filter_map, List.erase_filter]
  have heq : List.filter ((fun m => decide (geoOwner (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) m =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) ∘
        delMark hn g j hz hb hc)
        ((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)) =
      List.filter (fun m => decide (geoOwner (flatCentreCG hn g j hz hb hc) S m =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)))
        ((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)) := by
    apply List.filter_congr
    intro x hx
    have hx' : x ≠ Sum.inl j := (hnodC.mem_erase_iff.mp hx).1
    simp only [Function.comp]
    apply decide_eq_decide.mpr
    rw [geoOwner_deletion_iff hn g j hz hb hc S identify_deletion_marks,
      fusionMark_delMark hn g j hz hb hc x hx']
  rw [heq]

theorem isTrueCorner_delMark (S : Finset (Crossing g.center)) (a : Mark g.center) :
    IsTrueCorner (deletionSupport hn g j hz hb hc S) (delMark hn g j hz hb hc a) ↔
      IsTrueCorner S a := by
  cases a with
  | inl k => exact Iff.rfl
  | inr v =>
    rw [delMark_visit, isTrueCorner_visit, isTrueCorner_visit, fusionVisitEquiv_fst,
      mem_deletionSupport_iff]

/-- The corners of a deletion carrier are, up to rotation, the corners of its centre copy with
`μ_j` erased, read on the deletion. -/
theorem geoComponentCornerList_deletion_rotated (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b : Mark (deleteVertex g.center j)) :
    geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) ~r
      ((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).erase
          (Sum.inl j)).map (delMark hn g j hz hb hc) := by
  unfold geoComponentCornerList
  refine ((geoComponentMarkList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
    b).filter _).trans ?_
  rw [List.filter_map, List.erase_filter]
  have heq : List.filter ((fun a => decide (IsTrueCorner (deletionSupport hn g j hz hb hc S) a)) ∘
        delMark hn g j hz hb hc)
        ((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).erase
            (Sum.inl j)) =
      List.filter (fun a => decide (IsTrueCorner S a))
        ((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).erase
            (Sum.inl j)) := by
    apply List.filter_congr
    intro x _
    simp only [Function.comp]
    exact decide_eq_decide.mpr (isTrueCorner_delMark hn g j hz hb hc S x)
  rw [heq]

/-- A deletion mark and its centre image have the same plane point (`deleteVertex_apply`,
`crossingPoint_fusion`). -/
theorem geoMarkPosition_evaluation_fusionMark (m : Mark (deleteVertex g.center j)) :
    traversalEvaluation (deleteVertex g.center j)
        (geoMarkPosition (flatDeletionCG hn g j hz hb hc) m) =
      traversalEvaluation g.center
        (geoMarkPosition (flatCentreCG hn g j hz hb hc) (fusionMark hn g j hz hb hc m)) := by
  cases m with
  | inl i =>
    rw [fusionMark_vertex, geoMarkPosition_evaluation_vertex, geoMarkPosition_evaluation_vertex,
      deleteVertex_apply]
  | inr w =>
    rw [fusionMark_visit, geoMarkPosition_evaluation_visit, geoMarkPosition_evaluation_visit]
    have h := crossingPoint_fusion hn hz hb hc ((fusionVisitEquiv hn hz hb hc).symm w).1
    have hw : fusionCrossing hn hz hb hc ((fusionVisitEquiv hn hz hb hc).symm w).1 = w.1 := by
      change fusionCrossingEquiv hn hz hb hc _ = _
      rw [← fusionVisitEquiv_fst, Equiv.apply_symm_apply]
    rw [← hw, h]

/-- `central_vs_deletion_through_mu_j.2,.3`: the marks (corners) of the central carrier through
`μ_j`, with `μ_j` erased and read on the deletion, are the marks (corners) of its deletion copy,
as cycles. -/
theorem central_vs_deletion_cycles_of_marks (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j ∧
    ((((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) ∧
    ((((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) := by
  have hne := geoSmoothingSuccessor_deleted_ne hn g j hz hb hc S
  refine ⟨hne, ?_, ?_⟩
  · apply Cycle.coe_eq_coe.mpr
    have h := geoComponentMarkList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
      (delMark hn g j hz hb hc (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))
    rw [fusionMark_delMark hn g j hz hb hc _ hne, geoOwner_successor] at h
    exact h.symm
  · apply Cycle.coe_eq_coe.mpr
    have h := geoComponentCornerList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
      (delMark hn g j hz hb hc (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))
    rw [fusionMark_delMark hn g j hz hb hc _ hne, geoOwner_successor] at h
    exact h.symm

/-- cor:flat-carriers (i): `others_unchanged`, from U1's `identify_deletion_marks`. -/
theorem others_unchanged_of_marks (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    ∀ b : Mark (deleteVertex g.center j),
    geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
      centralCarrierThroughJ hn g j hz hb hc S →
    (((geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
          (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
      (geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
          Cycle (Mark g.center)) ∧
    (((geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
          (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
      (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
          Cycle (Mark g.center)) ∧
    geoComponentPlaneCycle (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      geoComponentPlaneCycle (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
  intro b hne
  have hnotmem : Sum.inl j ∉ geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
      (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
    rw [mem_geoComponentMarkList]
    exact fun h => hne h.symm
  have hnotmem' : Sum.inl j ∉ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
    rw [mem_geoComponentCornerList]
    exact fun h => hne h.1.symm
  have hmap : ∀ (l : List (Mark g.center)), Sum.inl j ∉ l →
      (l.map (delMark hn g j hz hb hc)).map (fusionMark hn g j hz hb hc) = l := by
    intro l hl
    rw [List.map_map]
    refine (List.map_congr_left ?_).trans (List.map_id _)
    intro x hx
    exact fusionMark_delMark hn g j hz hb hc x (fun he => hl (he ▸ hx))
  have h1 : (geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        (fusionMark hn g j hz hb hc) ~r
      geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
    have h := (geoComponentMarkList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
      b).map (fusionMark hn g j hz hb hc)
    rw [List.erase_eq_self_iff.mpr hnotmem, hmap _ hnotmem] at h
    exact h
  have h2 : (geoComponentCornerList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        (fusionMark hn g j hz hb hc) ~r
      geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
    have h := (geoComponentCornerList_deletion_rotated hn g j hz hb hc S identify_deletion_marks
      b).map (fusionMark hn g j hz hb hc)
    rw [List.erase_eq_self_iff.mpr hnotmem', hmap _ hnotmem'] at h
    exact h
  refine ⟨Cycle.coe_eq_coe.mpr h1, Cycle.coe_eq_coe.mpr h2, ?_⟩
  unfold geoComponentPlaneCycle
  apply Cycle.coe_eq_coe.mpr
  have h3 := h1.map (fun m => traversalEvaluation g.center
    (geoMarkPosition (flatCentreCG hn g j hz hb hc) m))
  rw [List.map_map] at h3
  have heq : (geoComponentMarkList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        (fun m => traversalEvaluation (deleteVertex g.center j)
          (geoMarkPosition (flatDeletionCG hn g j hz hb hc) m)) =
      (geoComponentMarkList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        ((fun m => traversalEvaluation g.center
          (geoMarkPosition (flatCentreCG hn g j hz hb hc) m)) ∘ fusionMark hn g j hz hb hc) :=
    List.map_congr_left (fun m _ => geoMarkPosition_evaluation_fusionMark hn g j hz hb hc m)
  rw [heq]
  exact h3

/-- Corner counts (for U4/U5): the deletion copy of the carrier through `μ_j` has exactly one
corner fewer than the central copy. -/
theorem geoCornerCount_deletion_through_mu_j (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    geoCornerCount (flatCentreCG hn g j hz hb hc) S (centralCarrierThroughJ hn g j hz hb hc S) =
      geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) + 1 := by
  have h := (central_vs_deletion_cycles_of_marks hn g j hz hb hc S identify_deletion_marks).2.2
  have hlen := (Cycle.coe_eq_coe.mp h).perm.length_eq
  have hmem : Sum.inl j ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (centralCarrierThroughJ hn g j hz hb hc S) :=
    (mem_geoComponentCornerList _ _ _ _).mpr ⟨rfl, isTrueCorner_vertex S j⟩
  rw [List.length_map, List.length_erase_of_mem hmem] at hlen
  have hpos := geoComponentCornerList_length_pos (flatCentreCG hn g j hz hb hc) S
    (centralCarrierThroughJ hn g j hz hb hc S)
  unfold geoCornerCount
  omega

/-- Corner counts (for U4/U5): every other carrier has the same number of corners at the centre
and on the deletion. -/
theorem geoCornerCount_deletion_other (S : Finset (Crossing g.center))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (b : Mark (deleteVertex g.center j))
    (hne : geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
      centralCarrierThroughJ hn g j hz hb hc S) :
    geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      geoCornerCount (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) := by
  have h := (others_unchanged_of_marks hn g j hz hb hc S identify_deletion_marks b hne).2.1
  have hlen := (Cycle.coe_eq_coe.mp h).perm.length_eq
  rw [List.length_map] at hlen
  exact hlen

end
end Deletion

/-! ## 6. `unique_through_mu_j`, `same_retained_crossings` -/

section Unique

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

omit [NeZero n] in
/-- cor:flat-carriers (i): `unique_through_mu_j` (centre: `flat_center_geometry` injectivity and
`flat_germ_spatial_data` at the parameter `0`; sides: `g1_vertices_injective` and
`flat_germ_spatial_data` at the side parameter). -/
theorem unique_through_mu_j_data (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) :
    (∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      (∃ a : Mark g.center, geoOwner (flatCentreCG hn g j hz hb hc) S a = q ∧
        traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) =
          g.center j) ↔
      q = centralCarrierThroughJ hn g j hz hb hc S) ∧
    (∀ (b : Bool) (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S)),
      (∃ a : Mark (g.sideTuple b t).val,
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) a = q ∧
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) a) =
          (g.sideTuple b t).val j) ↔
      q = geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) := by
  constructor
  · have hinj : Function.Injective g.center := (flat_center_geometry (by omega) hz hb).1
    have hcv : ∀ (c : Crossing g.center) (k : ZMod (n + 1)), crossingPoint c ≠ g.center k :=
      (flat_germ_spatial_data (by omega) g hz hb hc g.zeroParameter).2.2
    intro q
    constructor
    · rintro ⟨a, ha, hpt⟩
      cases a with
      | inl i =>
        rw [geoMarkPosition_evaluation_vertex] at hpt
        have hij : i = j := hinj hpt
        rw [← ha, hij]
        rfl
      | inr v =>
        rw [geoMarkPosition_evaluation_visit] at hpt
        exact absurd hpt (hcv v.1 j)
    · rintro rfl
      exact ⟨Sum.inl j, rfl, geoMarkPosition_evaluation_vertex _ j⟩
  · intro b q
    have hinj : Function.Injective (g.sideTuple b t).val :=
      g1_vertices_injective (flat_hn1 hn) (g.sideTuple b t).property.1
    have hcv : ∀ (c : Crossing (g.sideTuple b t).val) (k : ZMod (n + 1)),
        crossingPoint c ≠ (g.sideTuple b t).val k :=
      (flat_germ_spatial_data (by omega) g hz hb hc (g.sideTime b t)).2.2
    constructor
    · rintro ⟨a, ha, hpt⟩
      cases a with
      | inl i =>
        rw [geoMarkPosition_evaluation_vertex] at hpt
        have hij : i = j := hinj hpt
        rw [← ha, hij]
      | inr v =>
        rw [geoMarkPosition_evaluation_visit] at hpt
        exact absurd hpt (hcv v.1 j)
    · rintro rfl
      exact ⟨Sum.inl j, rfl, geoMarkPosition_evaluation_vertex _ j⟩

/-- cor:flat-carriers (ii): `same_retained_crossings`, from U1's `identify_sides_marks` and
`identify_deletion_marks`. -/
theorem same_retained_crossings_of_marks (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center))
    (identify_sides_marks : ∀ b : Bool,
      (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
        geoMarkList (flatSideCG hn g b t))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))) :
    (∀ (b : Bool) (a : Mark g.center) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a) ↔
      crossingTransport (hs b) x ∈ geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) ∧
    (∀ (b : Mark (deleteVertex g.center j)) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) ↔
      fusionCrossingEquiv hn hz hb hc x ∈
        geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) := by
  constructor
  · intro b a x
    unfold geoCarrierCrossings
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [mem_transportSupport_iff]
    apply and_congr Iff.rfl
    constructor
    · intro h w hw
      obtain ⟨v, rfl⟩ := (visitTransport (hs b)).surjective w
      rw [visitTransport_crossing] at hw
      have hv : v.1 = x := (crossingTransport (hs b)).injective hw
      have hvo := h v hv
      rw [geoOwner_markTransport_iff _ _ (hs b) (identify_sides_marks b) S] at hvo
      exact hvo
    · intro h v hv
      have hvo := h (visitTransport (hs b) v) (by rw [visitTransport_crossing, hv])
      rw [geoOwner_markTransport_iff _ _ (hs b) (identify_sides_marks b) S]
      exact hvo
  · intro b x
    unfold geoCarrierCrossings
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [mem_deletionSupport_iff]
    apply and_congr Iff.rfl
    constructor
    · intro h w hw
      obtain ⟨v, rfl⟩ := (fusionVisitEquiv hn hz hb hc).surjective w
      rw [fusionVisitEquiv_fst] at hw
      have hv : v.1 = x := (fusionCrossingEquiv hn hz hb hc).injective hw
      have hvo := h v hv
      rw [← delMark_visit, geoOwner_deletion_iff hn g j hz hb hc S identify_deletion_marks,
        fusionMark_delMark hn g j hz hb hc _ Sum.inr_ne_inl]
      exact hvo
    · intro h v hv
      have hvo := h (fusionVisitEquiv hn hz hb hc v) (by rw [fusionVisitEquiv_fst, hv])
      rw [← delMark_visit, geoOwner_deletion_iff hn g j hz hb hc S identify_deletion_marks,
        fusionMark_delMark hn g j hz hb hc _ Sum.inr_ne_inl] at hvo
      exact hvo

end Unique

/-! ## 7. The U2 bundle -/

section Bundle

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- Everything U2 delivers, from U1's interface lemmas `identify_sides_marks`,
`identify_deletion_marks`, `independent_supports` (sides). Conjuncts, in order, with the exact
field statements of `FlatCarriersDefinitionData` / `FlatCarriersData`: `centre_carriers`,
`correspond_sides`, `correspond_deletion`, `unique_through_mu_j`,
`central_vs_deletion_through_mu_j.1-.3` (the two geometric conjuncts `StrictBetween` / positive
multiples are U3's), `others_unchanged`, `same_retained_crossings`. -/
theorem flat_carriers_U2 (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center))
    (identify_sides_marks : ∀ b : Bool,
      (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport (hs b)) =
        geoMarkList (flatSideCG hn g b t))
    (identify_deletion_marks :
      ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
          Cycle (Mark (deleteVertex g.center j))) =
        (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j))))
    (independent_supports : ∀ b : Bool,
      IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    -- `centre_carriers`
    GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S ∧
    -- `correspond_sides`
    (∀ b : Bool,
      (∀ a : Mark g.center,
        geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
            (markTransport (hs b) a) =
          markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
      (∀ a a' : Mark g.center,
        geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
            geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a'))) ∧
    -- `correspond_deletion`
    ((∀ b : Mark (deleteVertex g.center j),
      geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        delMark hn g j hz hb hc
          (if geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
              Sum.inl j
            then geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
            else geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S
              (fusionMark hn g j hz hb hc b))) ∧
    (∀ b b' : Mark (deleteVertex g.center j),
      geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b' ↔
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) ∧
    (∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      ∃ b : Mark (deleteVertex g.center j),
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) = q)) ∧
    -- `unique_through_mu_j`
    ((∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      (∃ a : Mark g.center, geoOwner (flatCentreCG hn g j hz hb hc) S a = q ∧
        traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) =
          g.center j) ↔
      q = centralCarrierThroughJ hn g j hz hb hc S) ∧
    (∀ (b : Bool) (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S)),
      (∃ a : Mark (g.sideTuple b t).val,
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) a = q ∧
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) a) =
          (g.sideTuple b t).val j) ↔
      q = geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j))) ∧
    -- `central_vs_deletion_through_mu_j.1-.3`
    (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j ∧
    ((((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) ∧
    ((((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j)))) ∧
    -- `others_unchanged`
    (∀ b : Mark (deleteVertex g.center j),
    geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
      centralCarrierThroughJ hn g j hz hb hc S →
    (((geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
          (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
      (geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
          Cycle (Mark g.center)) ∧
    (((geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
          (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
      (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
          Cycle (Mark g.center)) ∧
    geoComponentPlaneCycle (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      geoComponentPlaneCycle (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))) ∧
    -- `same_retained_crossings`
    ((∀ (b : Bool) (a : Mark g.center) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a) ↔
      crossingTransport (hs b) x ∈ geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) ∧
    (∀ (b : Mark (deleteVertex g.center j)) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) ↔
      fusionCrossingEquiv hn hz hb hc x ∈
        geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))) :=
  ⟨centre_carriers_of_marks hn g j hz hb hc t hs S true (identify_sides_marks true)
      (independent_supports true),
   correspond_sides_of_marks hn g j hz hb hc t hs S identify_sides_marks,
   correspond_deletion_of_marks hn g j hz hb hc S identify_deletion_marks,
   unique_through_mu_j_data hn g j hz hb hc t hs S,
   central_vs_deletion_cycles_of_marks hn g j hz hb hc S identify_deletion_marks,
   others_unchanged_of_marks hn g j hz hb hc S identify_deletion_marks,
   same_retained_crossings_of_marks hn g j hz hb hc t hs S identify_sides_marks
     identify_deletion_marks⟩

end Bundle

end SM
