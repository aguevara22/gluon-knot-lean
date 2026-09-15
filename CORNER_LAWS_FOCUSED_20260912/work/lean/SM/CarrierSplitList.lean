import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Set.Function
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import SM.InterlaceSupports
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import SM.CarrierMarks
import SM.CarrierSuccessor
import SM.CarrierVisitTwin
import SM.CarrierSmoothing
import SM.CarrierSingleSwitch
import SM.CarrierOrbitRefinement
import SM.CycleFiltering
import SM.CarrierFilteredCycles
import SM.CarrierCycleList

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierSplitList.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

variable {α : Type*} [DecidableEq α]

/-- Adjacent-transposition products concatenate at their shared endpoint.
No distinctness assumption is needed for this algebraic identity. -/
theorem formPerm_append_shared (L R : List α) (a : α) :
    (L ++ a :: R).formPerm = (L ++ [a]).formPerm * (a :: R).formPerm := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => rfl
    | cons y L =>
      simpa only [List.cons_append, List.formPerm_cons_cons, mul_assoc] using
        congrArg (fun q : Equiv.Perm α => Equiv.swap x y * q) ih

/-- Relabelling a list conjugates its actual adjacent-transposition product. -/
theorem formPerm_map_perm (f : Equiv.Perm α) (L : List α) :
    (L.map f).formPerm = f * L.formPerm * f⁻¹ := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => simp
    | cons y L =>
      change Equiv.swap (f x) (f y) * ((y :: L).map f).formPerm =
        f * (Equiv.swap x y * (y :: L).formPerm) * f⁻¹
      rw [ih, Equiv.swap_apply_apply]
      simp [mul_assoc]

/-- Swapping an absent alternative head changes only the head of a cycle list. -/
theorem formPerm_conj_swap_head (a b : α) (L : List α)
    (ha : a ∉ L) (hb : b ∉ L) :
    Equiv.swap a b * (a :: L).formPerm * Equiv.swap a b = (b :: L).formPerm := by
  have hm : L.map (Equiv.swap a b) = L := by
    calc
      L.map (Equiv.swap a b) = L.map id := by
        apply List.map_congr_left
        intro x hx
        exact Equiv.swap_apply_of_ne_of_ne
          (fun he => ha (he ▸ hx)) (fun he => hb (he ▸ hx))
      _ = L := by simp
  simpa only [List.map_cons, Equiv.swap_apply_left, hm, Equiv.swap_inv] using
    (formPerm_map_perm (Equiv.swap a b) (a :: L)).symm

/-- Disjoint node lists give disjoint permutation supports, including singleton lists. -/
theorem formPerm_disjoint_of_disjoint (L R : List α) (h : L.Disjoint R) :
    Equiv.Perm.Disjoint L.formPerm R.formPerm := by
  intro x
  by_cases hx : x ∈ L
  · exact Or.inr (List.formPerm_apply_of_notMem (fun hr => h hx hr))
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

/-- The two source split lists are duplicate-free and have disjoint node sets.
The original list's exact Nodup hypothesis supplies every endpoint exclusion. -/
theorem splitList_child_data (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: B).Nodup ∧ (b :: A).Nodup ∧ (a :: B).Disjoint (b :: A) := by
  rcases List.nodup_cons.mp h with ⟨ha, hAB⟩
  rcases List.nodup_append'.mp hAB with ⟨hA, hbB, hAd⟩
  rcases List.nodup_cons.mp hbB with ⟨hb, hB⟩
  have haA : a ∉ A := fun hx => ha (List.mem_append.mpr (Or.inl hx))
  have haB : a ∉ B := fun hx =>
    ha (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b hx)))
  have hab : a ≠ b := by
    intro he
    apply ha
    simp [he]
  have hbA : b ∉ A := fun hx => hAd hx List.mem_cons_self
  refine ⟨List.nodup_cons.mpr ⟨haB, hB⟩, List.nodup_cons.mpr ⟨hbA, hA⟩, ?_⟩
  intro x hx hy
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases List.mem_cons.mp hy with he | hy
    · exact hab he
    · exact haA hy
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact hb hx
    · exact hAd hy (List.mem_cons_of_mem b hx)

/-- Switching the two outgoing slots splits the concrete old cyclic list into
exactly the source's two products. Either open arc may be empty. -/
theorem splitList_identity (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: (A ++ b :: B)).formPerm * Equiv.swap a b =
      (a :: B).formPerm * (b :: A).formPerm := by
  obtain ⟨haB, hbA, hd⟩ := splitList_child_data a b A B h
  have haA : a ∉ A := fun hx => h.notMem (List.mem_append.mpr (Or.inl hx))
  have hbB : b ∉ B := h.of_cons.of_append_right.notMem
  have hshort : ((a :: A) ++ [b]).Nodup := by
    have ht : (((a :: A) ++ [b]) ++ B).Nodup := by
      simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using h
    exact ht.of_append_left
  have hrotN : (b :: a :: A).Nodup := by
    simpa only [List.append_nil] using (List.nodup_middle.mp hshort)
  have hrot : ((a :: A) ++ [b]).formPerm = (b :: a :: A).formPerm := by
    simpa only [List.rotate_cons_succ, List.rotate_zero] using
      (List.formPerm_rotate_one (b :: a :: A) hrotN)
  have hconjA := formPerm_conj_swap_head a b A haA hbA.notMem
  have hconjB : Equiv.swap a b * (b :: B).formPerm * Equiv.swap a b =
      (a :: B).formPerm := by
    simpa only [Equiv.swap_comm b a] using
      (formPerm_conj_swap_head b a B hbB haB.notMem)
  calc
    (a :: (A ++ b :: B)).formPerm * Equiv.swap a b =
        (Equiv.swap a b * (a :: A).formPerm * (b :: B).formPerm) *
          Equiv.swap a b := by
      rw [show a :: (A ++ b :: B) = (a :: A) ++ b :: B from rfl,
        formPerm_append_shared, hrot, List.formPerm_cons_cons, Equiv.swap_comm b a]
    _ = (Equiv.swap a b * (a :: A).formPerm * Equiv.swap a b) *
        (Equiv.swap a b * (b :: B).formPerm * Equiv.swap a b) := by
      simp [mul_assoc]
    _ = (b :: A).formPerm * (a :: B).formPerm := by rw [hconjA, hconjB]
    _ = (a :: B).formPerm * (b :: A).formPerm :=
      (formPerm_disjoint_of_disjoint (a :: B) (b :: A) hd).commute.eq.symm

/-- A product with a disjoint list cycle remains a cycle on the first node set.
The proof uses integer powers and includes one-node cycles. -/
theorem formPerm_mul_isCycleOn_left (L R : List α) (hL : L.Nodup)
    (hd : L.Disjoint R) :
    (L.formPerm * R.formPerm).IsCycleOn {x | x ∈ L} := by
  have hc := hL.isCycleOn_formPerm
  have hfix : ∀ x ∈ L, R.formPerm x = x := fun x hx =>
    List.formPerm_apply_of_notMem (fun hr => hd hx hr)
  have hz (x : α) (hx : x ∈ L) (k : ℤ) :
      ((L.formPerm * R.formPerm) ^ k) x = (L.formPerm ^ k) x := by
    rw [(formPerm_disjoint_of_disjoint L R hd).commute.mul_zpow,
      Equiv.Perm.mul_apply,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (hfix x hx) k]
  refine ⟨hc.1.congr ?_, ?_⟩
  · intro x hx
    exact (show (L.formPerm * R.formPerm) x = L.formPerm x by
      rw [Equiv.Perm.mul_apply, hfix x hx]).symm
  · intro x hx y hy
    obtain ⟨k, hk⟩ := hc.2 hx hy
    exact ⟨k, (hz x hx k).trans hk⟩

/-- The child containing the incoming endpoint a is the complete cycle a,B. -/
theorem splitList_left_isCycleOn (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).IsCycleOn
      {x | x ∈ a :: B} := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  rw [splitList_identity a b A B h]
  exact formPerm_mul_isCycleOn_left (a :: B) (b :: A) hL hd

/-- The child containing the incoming endpoint b is the complete cycle b,A. -/
theorem splitList_right_isCycleOn (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).IsCycleOn
      {x | x ∈ b :: A} := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  rw [splitList_identity a b A B h,
    (formPerm_disjoint_of_disjoint (a :: B) (b :: A) hd).commute.eq]
  exact formPerm_mul_isCycleOn_left (b :: A) (a :: B) hR hd.symm

/-- The entire successor orbit of a is exactly its source split list. -/
theorem splitList_left_sameCycle_iff (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) (x : α) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle a x ↔
      x ∈ a :: B := by
  have hc := splitList_left_isCycleOn a b A B h
  constructor
  · rintro ⟨k, rfl⟩
    exact (hc.1.perm_zpow k).mapsTo List.mem_cons_self
  · intro hx
    exact hc.2 List.mem_cons_self hx

/-- The entire successor orbit of b is exactly its source split list. -/
theorem splitList_right_sameCycle_iff (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) (x : α) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle b x ↔
      x ∈ b :: A := by
  have hc := splitList_right_isCycleOn a b A B h
  constructor
  · rintro ⟨k, rfl⟩
    exact (hc.1.perm_zpow k).mapsTo List.mem_cons_self
  · intro hx
    exact hc.2 List.mem_cons_self hx

/-- The two incoming endpoint marks belong to different successor orbits. -/
theorem splitList_not_sameCycle (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ¬ ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle a b := by
  intro hc
  have hb := (splitList_left_sameCycle_iff a b A B h b).mp hc
  exact (splitList_child_data a b A B h).2.2 hb List.mem_cons_self

end SM.Carrier
