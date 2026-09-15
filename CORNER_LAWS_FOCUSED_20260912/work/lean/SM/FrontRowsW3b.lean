-- Ported 17:38Z 2026-09-14 from work/drafts/frontrows/FrontRows_W3b_Delta.lean (front certificate rows lane, last delta: the type-II move material of unit U6, the leaf typeII_move, P_typeII, rows 78 ng:front-II and 83 ng:local-front-bound, certificate_laws and word_bound; imports SM.FrontRowsW3) by the pod executor; body verbatim.
import SM.FrontRowsW3

/-! # Front certificate rows — last delta: the type-II move leaf, rows 78 and 83, `certificate_laws`, `word_bound`

Certificate rows lane, last delta (decision D-FR1: the lane is ported incrementally as fully proved modules): the
type-II move leaf, rows 78 ng:front-II and 83 ng:local-front-bound, `certificate_laws` and `word_bound`.  This module
imports `SM.FrontRowsW3` (which imports `SM.FrontRowsW2S` and `SM.FrontRowsW2`: rows 76 ng:commutation, 77 ng:front-I,
79 ng:front-III, 80 ng:deletions, 81 ng:circle, 82 ng:cusp-skein, the five row-statement structures, the infrastructure
blocks U1-U8 and the leaves `represent`, `typeIII_site`, `typeI_move`, `crossedCusp_move`) and adds, in this order:
* **the continuation of the U6 infrastructure block** (`SM.FrontRows.U6`, re-opened with the block's header `open`
  and `noncomputable section`): sections H3-H5 — the type-II variant (b) (`l_{m+1} σ_m σ_{m+1} ↦ l_m`): the moved
  diagram, its specification and the remaining specification fields, `U6.typeII_b`; sections I1-I5 — the type-II
  variant (d) (`σ_{m+1} σ_m r_{m+1} ↦ r_m`): the word level, the block passage, the moved diagram, the specification,
  `U6.typeII_d`; section J — the dispatch `U6.typeII_move_proof` over the four variants of `IsTypeII` (`typeII_a`,
  `typeII_c` are in `SM.FrontRowsW3`).  Verbatim from `W3_U6.lean` L22209-25423 (W3_U6_REPORT.md), whose prefix
  L11103-22207 is the block already ported in `SM.FrontRowsW3`.  The continuation declares two further global tactic
  macros, `bII_pair` and `dII_pair` (the nine of the ported block, `cc_mem` … `cII_pair`, are imported, not re-declared).
* **the leaf `SM.FrontRows.typeII_move`** (ng:front-II: the two standard realizations of a type-II pair are related by
  an oriented Reidemeister-II site through a vertex-moved diagram carrying the named record of `realize W'`): docstring
  and statement verbatim from `Skeleton_W2.lean` L11103-11111, body `U6.typeII_move_proof h` (`W3_U6.lean` L25428-25436).
* **the polynomial consumer** `SM.FrontRows.P_typeII` (`Δd = 0` through `P_reidemeister_II` and `presentations`),
  verbatim from `Skeleton_W2.lean` L14625-14629.
* **row 78**: `SM.ng_front_II : NgFrontIIClauses`, verbatim from `Skeleton_W2.lean` L14765-14772, assembled from the
  count leaf `typeII_counts` (`SM.FrontRowsW2`) and `P_typeII`.
* **`SM.FrontRows.certificate_laws`** (the seven laws of the descent `Moves.Laws` for the moves of `SM.ng_finite_word`
  with the geometric `s`, `B` of the realization and the syntactic base: rows 76(1), 77, 78, 79 for `pres_B`; rows 80,
  81(1) for `del_B`; row 82 for `skein_B`; `base_defect_nonneg` for `base_B`) and **`SM.FrontRows.word_bound`** (`B ≥ 0`
  on every closed oriented word's realization, consuming the accepted literature interface `SM.ng_finite_word` through
  `ng_finite_word_bound`), verbatim from `Skeleton_W2.lean` L14842-14876.
* **row 83**: `SM.ng_local_front_bound : NgLocalFrontBoundClauses` (the representation clause of ng:commutation carries
  `D`, `w` and the rounding's record to a word, `presentations` carries `P`, the word bound gives `B ≥ 0`), verbatim
  from `Skeleton_W2.lean` L14878-14889.

Every declaration in this module is fully proved: the axioms of `SM.FrontRows.typeII_move` and `U6.typeII_move_proof`
are `[propext, Classical.choice, Quot.sound]`; those of `SM.ng_front_II`, `SM.FrontRows.P_typeII` and
`SM.FrontRows.certificate_laws` are `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` is the accepted
literature interface reached through `P`); those of `SM.FrontRows.word_bound` and `SM.ng_local_front_bound` are
`[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]`.  Nothing declared in the three ported modules
is re-declared here.  Provenance and line map: `work/drafts/frontrows/W3B_DELTA_REPORT.md`.

Checked with `cd work/lean && lake env lean`. -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

namespace FrontRows

section Leaves

/-! ### U6 infrastructure, continued — the type-II variants (b) and (d) and the dispatch (verbatim from `W3_U6.lean`
L22209-25423; the block's header L11110-11114 is re-opened, its first part L11103-22207 is in `SM.FrontRowsW3`) -/

namespace U6

open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4

noncomputable section

/-! #### H3. The type-II variant (b): the moved diagram (the cusp arc is lifted above the through-strand) -/

/-- the realization's positions of the through-strand's vertices (variant (b), unmoved) -/
def pvA3 (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h)
  | 2 => (((k + 2 : ℕ) : ℝ), h - 1)
  | _ => (((k + 3 : ℕ) : ℝ), h - 2)

/-- the realization's positions of the cusp arc's seven vertices (variant (b)) -/
def pvB3 (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => (((k + 3 : ℕ) : ℝ), h - 1)
  | 1 => (((k + 2 : ℕ) : ℝ), h - 2)
  | 2 => (((k + 1 : ℕ) : ℝ), h - 2)
  | 3 => ((k : ℝ) + 1 / 2, h - 3 / 2)
  | 4 => (((k + 1 : ℕ) : ℝ), h - 1)
  | 5 => (((k + 2 : ℕ) : ℝ), h)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the moved positions of the cusp arc's vertices (variant (b)): the arc is lifted above the through-strand -/
def mvB3 (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => (((k + 3 : ℕ) : ℝ), h - 1)
  | 1 => (((k + 2 : ℕ) : ℝ), h - 3 / 8)
  | 2 => (((k + 1 : ℕ) : ℝ), h + 1 / 8)
  | 3 => ((k : ℝ) + 1 / 2, h + 3 / 8)
  | 4 => (((k + 1 : ℕ) : ℝ), h + 5 / 8)
  | 5 => (((k + 2 : ℕ) : ℝ), h)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the four moved slots of the type-II variant (b) -/
def IsMovedB (k m : ℕ) (s : ℕ × ℕ) : Prop :=
  s = (k + 2, m + 2) ∨ s = (k + 1, m + 2) ∨ s = (k, 0) ∨ s = (k + 1, m + 1)

/-- the moved vertex function of the type-II variant (b) -/
def mvIIb (W : Word) (k m : ℕ) (h : ℝ) (u : Slot W) : Plane :=
  if u.1 = (k + 2, m + 2) then mvB3 k h 1
  else if u.1 = (k + 1, m + 2) then mvB3 k h 2
  else if u.1 = (k, 0) then mvB3 k h 3
  else if u.1 = (k + 1, m + 1) then mvB3 k h 4
  else pt .std W u.1

section MvIIb

variable (W : Word) (k m : ℕ) (h : ℝ)

theorem mvIIb_of_not_moved {u : Slot W} (hu : ¬ IsMovedB k m u.1) : mvIIb W k m h u = pt .std W u.1 := by
  unfold IsMovedB at hu
  simp only [not_or] at hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  simp [mvIIb, h1, h2, h3, h4]

theorem mvIIb_v1 {u : Slot W} (hu : u.1 = (k + 2, m + 2)) : mvIIb W k m h u = mvB3 k h 1 := by simp [mvIIb, hu]
theorem mvIIb_v2 {u : Slot W} (hu : u.1 = (k + 1, m + 2)) : mvIIb W k m h u = mvB3 k h 2 := by simp [mvIIb, hu]
theorem mvIIb_v3 {u : Slot W} (hu : u.1 = (k, 0)) : mvIIb W k m h u = mvB3 k h 3 := by simp [mvIIb, hu]
theorem mvIIb_v4 {u : Slot W} (hu : u.1 = (k + 1, m + 1)) : mvIIb W k m h u = mvB3 k h 4 := by simp [mvIIb, hu]

theorem mvIIb_of_ext {u : Slot W} (hu : ExtSl k (k + 3) u.1) : mvIIb W k m h u = pt .std W u.1 := by
  apply mvIIb_of_not_moved
  obtain ⟨j, p, hu'⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu'] at hu ⊢
  unfold ExtSl at hu
  unfold IsMovedB
  simp only [Prod.mk.injEq]
  split_ifs at hu with h0 <;> omega

theorem mvIIb_xcoord (u : Slot W) : (mvIIb W k m h u).1 = (pt .std W u.1).1 := by
  by_cases hmv : IsMovedB k m u.1
  · unfold IsMovedB at hmv
    rcases hmv with e | e | e | e
    · rw [mvIIb_v1 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvIIb_v2 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvIIb_v3 W k m h e, e, std_pt_cusp]; rfl
    · rw [mvIIb_v4 W k m h e, e, std_pt_cut _ (by omega)]; rfl
  · rw [mvIIb_of_not_moved W k m h hmv]

theorem mvIIb_injective (n : ℕ) : Function.Injective (mvIIb W k m (-(n : ℝ))) := by
  have ng : ∀ i, 1 ≤ i → i ≤ 4 → ∀ s, mvB3 k (-(n : ℝ)) i ≠ pt .std W s := by
    intro i hi1 hi2 s
    interval_cases i
    · have := nonGrid_eighth (n + 1) (-3) (by decide)
      have e : -(n : ℝ) - 3 / 8 = -((n + 1 : ℕ) : ℝ) + 1 + ((-3 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ), -(n : ℝ) - 3 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth (n + 1) 1 (by decide)
      have e : -(n : ℝ) + 1 / 8 = -((n + 1 : ℕ) : ℝ) + 1 + ((1 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 1 : ℕ) : ℝ), -(n : ℝ) + 1 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth (n + 1) 3 (by decide)
      have e : -(n : ℝ) + 3 / 8 = -((n + 1 : ℕ) : ℝ) + 1 + ((3 : ℤ) : ℝ) / 8 := by push_cast; ring
      show ((k : ℝ) + 1 / 2, -(n : ℝ) + 3 / 8) ≠ _
      rw [e]; exact this.ne_pt_half W k s
    · have := nonGrid_eighth (n + 1) 5 (by decide)
      have e : -(n : ℝ) + 5 / 8 = -((n + 1 : ℕ) : ℝ) + 1 + ((5 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 1 : ℕ) : ℝ), -(n : ℝ) + 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
  have hval : ∀ u : Slot W, IsMovedB k m u.1 → ∃ i, 1 ≤ i ∧ i ≤ 4 ∧ mvIIb W k m (-(n : ℝ)) u = mvB3 k (-(n : ℝ)) i ∧
      (i = 1 → u.1 = (k + 2, m + 2)) ∧ (i = 2 → u.1 = (k + 1, m + 2)) ∧ (i = 3 → u.1 = (k, 0)) ∧
      (i = 4 → u.1 = (k + 1, m + 1)) := by
    intro u hu
    unfold IsMovedB at hu
    rcases hu with e | e | e | e
    · exact ⟨1, le_rfl, by norm_num, mvIIb_v1 W k m _ e, fun _ => e, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · exact ⟨2, by norm_num, by norm_num, mvIIb_v2 W k m _ e, fun h => absurd h (by norm_num), fun _ => e,
        fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, mvIIb_v3 W k m _ e, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num), fun _ => e, fun h => absurd h (by norm_num)⟩
    · exact ⟨4, by norm_num, le_rfl, mvIIb_v4 W k m _ e, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ => e⟩
  have hdist : ∀ i j, 1 ≤ i → i ≤ 4 → 1 ≤ j → j ≤ 4 → mvB3 k (-(n : ℝ)) i = mvB3 k (-(n : ℝ)) j → i = j := by
    intro i j hi1 hi2 hj1 hj2 he
    interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; have := congrArg Prod.snd he; simp only [mvB3] at this; linarith)
  intro u v huv
  by_cases hu : IsMovedB k m u.1
  · obtain ⟨i, hi1, hi2, hui, hu1, hu2, hu3, hu4⟩ := hval u hu
    by_cases hv : IsMovedB k m v.1
    · obtain ⟨j, hj1, hj2, hvj, hv1, hv2, hv3, hv4⟩ := hval v hv
      have := hdist i j hi1 hi2 hj1 hj2 (hui.symm.trans (huv.trans hvj))
      subst this
      apply Subtype.ext
      interval_cases i
      · rw [hu1 rfl, hv1 rfl]
      · rw [hu2 rfl, hv2 rfl]
      · rw [hu3 rfl, hv3 rfl]
      · rw [hu4 rfl, hv4 rfl]
    · rw [hui, mvIIb_of_not_moved W k m _ hv] at huv
      exact absurd huv (ng i hi1 hi2 _)
  · by_cases hv : IsMovedB k m v.1
    · obtain ⟨j, hj1, hj2, hvj, -⟩ := hval v hv
      rw [hvj, mvIIb_of_not_moved W k m _ hu] at huv
      exact absurd huv.symm (ng j hj1 hj2 _)
    · rw [mvIIb_of_not_moved W k m _ hu, mvIIb_of_not_moved W k m _ hv] at huv
      exact pt_inj _ _ huv

end MvIIb

section IIbVertices

variable (k : ℕ) (h : ℝ)

theorem pvA3_int : ∀ i, 1 ≤ i → i ≤ 2 → pvA3 k h i ∈ interior (polygon (tIIL k h)) := by
  intro i h1 h2
  interval_cases i
  · have := tIIL_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tIIL_int_cut2 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem pvA3_mem : ∀ i, i ≤ 3 → pvA3 k h i ∈ polygon (tIIL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIL_mem_left k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · exact interior_subset (pvA3_int k h i h0 (by omega))
  · have : i = 3 := by omega
    subst this
    have := tIIL_mem_right k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem pvB3_int : ∀ i, 1 ≤ i → i ≤ 5 → pvB3 k h i ∈ interior (polygon (tIIL k h)) := by
  intro i h1 h5
  interval_cases i
  · have := tIIL_int_cut2 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIL_int_cut1 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIL_int_cuspL k h (-(3 / 2)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIL_int_cut1 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIL_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem pvB3_mem : ∀ i, i ≤ 6 → pvB3 k h i ∈ polygon (tIIL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIL_mem_right k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  rcases Nat.lt_or_ge i 6 with h6 | h6
  · exact interior_subset (pvB3_int k h i h0 (by omega))
  · have : i = 6 := by omega
    subst this
    have := tIIL_mem_right k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem mvB3_int : ∀ i, 1 ≤ i → i ≤ 5 → mvB3 k h i ∈ interior (polygon (tIIL k h)) := by
  intro i h1 h5
  interval_cases i
  · have := tIIL_int_cut2 k h (-(3 / 8)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · exact tIIL_int_cut1 k h (1 / 8) (by norm_num) (by norm_num)
  · exact tIIL_int_cuspL k h (3 / 8) (by norm_num) (by norm_num)
  · exact tIIL_int_cut1 k h (5 / 8) (by norm_num) (by norm_num)
  · have := tIIL_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem mvB3_mem : ∀ i, i ≤ 6 → mvB3 k h i ∈ polygon (tIIL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIL_mem_right k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  rcases Nat.lt_or_ge i 6 with h6 | h6
  · exact interior_subset (mvB3_int k h i h0 (by omega))
  · have : i = 6 := by omega
    subst this
    have := tIIL_mem_right k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

/-! the geometric facts of the same-column pairs of the moved variant (b) -/

macro "bII_pair" : tactic => `(tactic| (
  intro τ τ' h0 h1 h0' h1' he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [pvA3, mvB3, segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy))

theorem bII_NM_T0C2 : NoMeet (pvA3 k h 0) (pvA3 k h 1) (mvB3 k h 2) (mvB3 k h 3) := by bII_pair; linarith
theorem bII_NM_T0C3 : NoMeet (pvA3 k h 0) (pvA3 k h 1) (mvB3 k h 3) (mvB3 k h 4) := by bII_pair; linarith
theorem bII_NM_T1C1 : NoMeet (pvA3 k h 1) (pvA3 k h 2) (mvB3 k h 1) (mvB3 k h 2) := by bII_pair; linarith
theorem bII_NM_T1C4 : NoMeet (pvA3 k h 1) (pvA3 k h 2) (mvB3 k h 4) (mvB3 k h 5) := by bII_pair; linarith
theorem bII_NM_T2C0 : NoMeet (pvA3 k h 2) (pvA3 k h 3) (mvB3 k h 0) (mvB3 k h 1) := by bII_pair; linarith
theorem bII_NM_T2C5 : NoMeet (pvA3 k h 2) (pvA3 k h 3) (mvB3 k h 5) (mvB3 k h 6) := by bII_pair; linarith
theorem bII_NM_C1C4 : NoMeet (mvB3 k h 1) (mvB3 k h 2) (mvB3 k h 4) (mvB3 k h 5) := by bII_pair; linarith
theorem bII_NM_C0C5 : NoMeet (mvB3 k h 0) (mvB3 k h 1) (mvB3 k h 5) (mvB3 k h 6) := by bII_pair; linarith
theorem bII_OJ234 : OnlyAtJoint (mvB3 k h 2) (mvB3 k h 3) (mvB3 k h 4) := by
  bII_pair; constructor <;> linarith

end IIbVertices

/-! #### H4. The type-II variant (b): the specification -/

section TypeIIbSpec

open U3

variable (X Y : Word) (m : ℕ) (d t : Bool) (hm : 1 ≤ m)
  (hW : (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y) X.length m = t)

local notation "Vb" => X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y
local notation "Pb" => [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)]
local notation "Vb'" => X ++ [Letter.l m d] ++ Y
local notation "Pb'" => [Letter.l m d]
local notation "hB" => (-(m : ℝ))

/-- the moved vertex function of the type-II variant (b) -/
def bMv : Slot Vb → Plane := mvIIb Vb X.length m hB

theorem bMv_apply (u : Slot Vb) : bMv X Y m d u = mvIIb Vb X.length m hB u := rfl

include hm

theorem b_pt_T : ∀ i, i ≤ 3 → pt .std Vb (tvT3 X.length m i) = pvA3 X.length hB i := by
  intro i hi
  interval_cases i
  · show pt .std Vb (X.length, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA3])
  · show pt .std Vb (X.length + 1, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA3])
  · show pt .std Vb (X.length + 2, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA3]; push_cast; ring)
  · show pt .std Vb (X.length + 3, m + 2) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA3]; push_cast; ring)

theorem b_pt_C : ∀ i, i ≤ 6 → pt .std Vb (tvC3 X.length m i) = pvB3 X.length hB i := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
  intro i hi
  interval_cases i
  · show pt .std Vb (X.length + 3, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB3]; push_cast; ring)
  · show pt .std Vb (X.length + 2, m + 2) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB3]; push_cast; ring)
  · show pt .std Vb (X.length + 1, m + 2) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB3]; push_cast; ring)
  · show pt .std Vb (X.length, 0) = _
    rw [std_pt_cusp, hℓ₀]; exact Prod.ext rfl (by simp only [pvB3, idx]; push_cast; ring)
  · show pt .std Vb (X.length + 1, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB3]; push_cast; ring)
  · show pt .std Vb (X.length + 2, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB3])
  · show pt .std Vb (X.length + 3, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB3])

theorem b_mv_T : ∀ i, i ≤ 3 → ∀ u : Slot Vb, u.1 = tvT3 X.length m i → bMv X Y m d u = pvA3 X.length hB i := by
  intro i hi u hu
  have hnm : ¬ IsMovedB X.length m u.1 := by
    rw [hu]; interval_cases i <;> simp only [IsMovedB, tvT3, Prod.mk.injEq] <;> omega
  rw [bMv_apply, mvIIb_of_not_moved _ _ _ _ hnm, hu]
  exact b_pt_T X Y m d hm i hi

theorem b_mv_C : ∀ i, i ≤ 6 → ∀ u : Slot Vb, u.1 = tvC3 X.length m i → bMv X Y m d u = mvB3 X.length hB i := by
  intro i hi u hu
  rw [bMv_apply]
  interval_cases i
  · rw [mvIIb_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedB, tvC3, Prod.mk.injEq]; omega), hu,
      b_pt_C X Y m d hm 0 (by norm_num)]; rfl
  · exact mvIIb_v1 _ _ _ _ hu
  · exact mvIIb_v2 _ _ _ _ hu
  · exact mvIIb_v3 _ _ _ _ hu
  · exact mvIIb_v4 _ _ _ _ hu
  · rw [mvIIb_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedB, tvC3, Prod.mk.injEq]; omega), hu,
      b_pt_C X Y m d hm 5 (by norm_num)]; rfl
  · rw [mvIIb_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedB, tvC3, Prod.mk.injEq]; omega), hu,
      b_pt_C X Y m d hm 6 (by norm_num)]; rfl

omit hm in
theorem tvT3_inj : ∀ i j, i ≤ 3 → j ≤ 3 → tvT3 X.length m i = tvT3 X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tvT3, Prod.mk.injEq] at he; omega)

omit hm in
theorem tvC3_inj : ∀ i j, i ≤ 6 → j ≤ 6 → tvC3 X.length m i = tvC3 X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tvC3, Prod.mk.injEq] at he; omega)

theorem tvT3_ne_tvC3 : ∀ i j, i ≤ 3 → j ≤ 6 → tvT3 X.length m i ≠ tvC3 X.length m j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> simp only [tvT3, tvC3, Prod.mk.injEq] at he <;> omega

include hW ht

theorem bT_mv_slot : ∀ j, j ≤ 3 → bMv X Y m d ((bT X Y m d t hm hW).slot hW j) =
    if t then pvA3 X.length hB j else pvA3 X.length hB (3 - j) := by
  intro j hj
  have hs := bT_slot_val X Y m d t hm hW ht j hj
  cases t
  · simp only [tvTd3, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact b_mv_T X Y m d hm (3 - j) (by omega) _ hs
  · simp only [tvTd3, ↓reduceIte] at hs ⊢
    exact b_mv_T X Y m d hm j hj _ hs

theorem bT_pt_slot : ∀ j, j ≤ 3 → pt .std Vb ((bT X Y m d t hm hW).slot hW j).1 =
    if t then pvA3 X.length hB j else pvA3 X.length hB (3 - j) := by
  intro j hj
  have hs := bT_slot_val X Y m d t hm hW ht j hj
  cases t
  · simp only [tvTd3, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact b_pt_T X Y m d hm (3 - j) (by omega)
  · simp only [tvTd3, ↓reduceIte] at hs ⊢
    rw [hs]; exact b_pt_T X Y m d hm j hj

theorem bC_mv_slot : ∀ j, j ≤ 6 → bMv X Y m d ((bC X Y m d hm hW).slot hW j) =
    if d then mvB3 X.length hB j else mvB3 X.length hB (6 - j) := by
  intro j hj
  have hs := bC_slot_val X Y m d t hm hW ht j hj
  cases d
  · simp only [tvCd3, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact b_mv_C X Y m false hm (6 - j) (by omega) _ hs
  · simp only [tvCd3, ↓reduceIte] at hs ⊢
    exact b_mv_C X Y m true hm j hj _ hs

theorem bC_pt_slot : ∀ j, j ≤ 6 → pt .std Vb ((bC X Y m d hm hW).slot hW j).1 =
    if d then pvB3 X.length hB j else pvB3 X.length hB (6 - j) := by
  intro j hj
  have hs := bC_slot_val X Y m d t hm hW ht j hj
  cases d
  · simp only [tvCd3, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact b_pt_C X Y m false hm (6 - j) (by omega)
  · simp only [tvCd3, ↓reduceIte] at hs ⊢
    rw [hs]; exact b_pt_C X Y m true hm j hj

omit ht in
theorem bT_next_slot : ∀ j, j < 3 → next hW ((bT X Y m d t hm hW).slot hW j) = (bT X Y m d t hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

omit ht in
theorem bC_next_slot : ∀ j, j < 6 → next hW ((bC X Y m d hm hW).slot hW j) = (bC X Y m d hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

theorem bT_chain_in : ∀ j, j < 3 → PieceIn (tIIL X.length hB) hW (bMv X Y m d) ((bT X Y m d t hm hW).slot hW j) ∧
    PieceIn (tIIL X.length hB) hW (ptv .std) ((bT X Y m d t hm hW).slot hW j) := by
  intro j hj
  have e := bT_next_slot X Y m d t hm hW j hj
  have key : SegIn (tIIL X.length hB) (if t then pvA3 X.length hB j else pvA3 X.length hB (3 - j))
      (if t then pvA3 X.length hB (j + 1) else pvA3 X.length hB (3 - (j + 1))) := by
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (pvA3_mem _ _ _ (by omega)) (pvA3_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pvA3_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pvA3_int _ _ _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (pvA3_mem _ _ _ (by omega)) (pvA3_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pvA3_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pvA3_int _ _ _ (by omega) (by omega))
  constructor
  · show SegIn _ (bMv X Y m d _) (bMv X Y m d (next hW _))
    rw [e, bT_mv_slot X Y m d t hm hW ht j (by omega), bT_mv_slot X Y m d t hm hW ht (j + 1) (by omega)]
    exact key
  · show SegIn _ (pt .std Vb _) (pt .std Vb (next hW _).1)
    rw [e, bT_pt_slot X Y m d t hm hW ht j (by omega), bT_pt_slot X Y m d t hm hW ht (j + 1) (by omega)]
    exact key

theorem bC_chain_in : ∀ j, j < 6 → PieceIn (tIIL X.length hB) hW (bMv X Y m d) ((bC X Y m d hm hW).slot hW j) ∧
    PieceIn (tIIL X.length hB) hW (ptv .std) ((bC X Y m d hm hW).slot hW j) := by
  intro j hj
  have e := bC_next_slot X Y m d hm hW j hj
  have key : ∀ (f : ℕ → Plane), (∀ i, i ≤ 6 → f i ∈ polygon (tIIL X.length hB)) →
      (∀ i, 1 ≤ i → i ≤ 5 → f i ∈ interior (polygon (tIIL X.length hB))) →
      SegIn (tIIL X.length hB) (if d then f j else f (6 - j)) (if d then f (j + 1) else f (6 - (j + 1))) := by
    intro f hmem hint
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (hmem _ (by omega)) (hmem _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (hint _ (by norm_num) (by norm_num))
      · exact Or.inl (hint _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (hmem _ (by omega)) (hmem _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (hint _ (by norm_num) (by norm_num))
      · exact Or.inl (hint _ (by omega) (by omega))
  constructor
  · show SegIn _ (bMv X Y m d _) (bMv X Y m d (next hW _))
    rw [e, bC_mv_slot X Y m d t hm hW ht j (by omega), bC_mv_slot X Y m d t hm hW ht (j + 1) (by omega)]
    exact key _ (mvB3_mem _ _) (mvB3_int _ _)
  · show SegIn _ (pt .std Vb _) (pt .std Vb (next hW _).1)
    rw [e, bC_pt_slot X Y m d t hm hW ht j (by omega), bC_pt_slot X Y m d t hm hW ht (j + 1) (by omega)]
    exact key _ (pvB3_mem _ _) (pvB3_int _ _)

theorem bT_vert : ∀ j, 0 < j → j < 3 → bMv X Y m d ((bT X Y m d t hm hW).slot hW j) ∈ interior (polygon (tIIL X.length hB)) ∧
    pt .std Vb ((bT X Y m d t hm hW).slot hW j).1 ∈ interior (polygon (tIIL X.length hB)) := by
  intro j h0 hj
  rw [bT_mv_slot X Y m d t hm hW ht j (by omega), bT_pt_slot X Y m d t hm hW ht j (by omega)]
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨pvA3_int _ _ _ (by omega) (by omega), pvA3_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨pvA3_int _ _ _ (by omega) (by omega), pvA3_int _ _ _ (by omega) (by omega)⟩

theorem bC_vert : ∀ j, 0 < j → j < 6 → bMv X Y m d ((bC X Y m d hm hW).slot hW j) ∈ interior (polygon (tIIL X.length hB)) ∧
    pt .std Vb ((bC X Y m d hm hW).slot hW j).1 ∈ interior (polygon (tIIL X.length hB)) := by
  intro j h0 hj
  rw [bC_mv_slot X Y m d t hm hW ht j (by omega), bC_pt_slot X Y m d t hm hW ht j (by omega)]
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨mvB3_int _ _ _ (by omega) (by omega), pvB3_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨mvB3_int _ _ _ (by omega) (by omega), pvB3_int _ _ _ (by omega) (by omega)⟩

omit hW ht in
theorem b_moved : ∀ u : Slot Vb, bMv X Y m d u = pt .std Vb u.1 ∨
    (bMv X Y m d u ∈ interior (polygon (tIIL X.length hB)) ∧ pt .std Vb u.1 ∈ interior (polygon (tIIL X.length hB))) := by
  intro u
  by_cases hmv : IsMovedB X.length m u.1
  · right
    have : ∃ i, 1 ≤ i ∧ i ≤ 4 ∧ u.1 = tvC3 X.length m i := by
      unfold IsMovedB at hmv
      rcases hmv with e | e | e | e
      · exact ⟨1, by norm_num, by norm_num, e⟩
      · exact ⟨2, by norm_num, by norm_num, e⟩
      · exact ⟨3, by norm_num, by norm_num, e⟩
      · exact ⟨4, by norm_num, by norm_num, e⟩
    obtain ⟨i, hi1, hi2, hu⟩ := this
    rw [b_mv_C X Y m d hm i (by omega) u hu, hu, b_pt_C X Y m d hm i (by omega)]
    exact ⟨mvB3_int _ _ _ (by omega) (by omega), pvB3_int _ _ _ (by omega) (by omega)⟩
  · left
    rw [bMv_apply, mvIIb_of_not_moved _ _ _ _ hmv]

/-- the chain slot carrying the through-vertex `tvT3 i` -/
theorem bT_chain_of (i : ℕ) (hi : i ≤ 3) {u : Slot Vb} (hu : u.1 = tvT3 X.length m i)
    (hd : (t = true ∧ i < 3) ∨ (t = false ∧ 0 < i)) : OnChain hW (bT X Y m d t hm hW) u := by
  cases t
  · refine ⟨3 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · show 3 - i < 3; omega
    · rw [bT_slot_val X Y m d false hm hW ht (3 - i) (by omega), hu]
      simp only [tvTd3, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [bT_slot_val X Y m d true hm hW ht i hi, hu]
      simp only [tvTd3, ↓reduceIte]

/-- the chain slot carrying the cusp-arc vertex `tvC3 i` -/
theorem bC_chain_of (i : ℕ) (hi : i ≤ 6) {u : Slot Vb} (hu : u.1 = tvC3 X.length m i)
    (hd : (d = true ∧ i < 6) ∨ (d = false ∧ 0 < i)) : OnChain hW (bC X Y m d hm hW) u := by
  cases d
  · refine ⟨6 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · show 6 - i < 6; omega
    · rw [bC_slot_val X Y m false t hm hW ht (6 - i) (by omega), hu]
      simp only [tvCd3, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [bC_slot_val X Y m true t hm hW ht i hi, hu]
      simp only [tvCd3, ↓reduceIte]

omit hm ht in
/-- an unchanged spectator piece with an explicit outside witness -/
theorem b_spec {u : Slot Vb} {j p j' p' : ℕ} (hu : u.1 = (j, p)) (hn : (next hW u).1 = (j', p'))
    (hp : p ≠ 0) (hp' : p' ≠ 0) (h1 : ¬ IsMovedB X.length m (j, p)) (h2 : ¬ IsMovedB X.length m (j', p'))
    (hout : SegOut (tIIL X.length hB) ((j : ℝ), -(p : ℝ)) ((j' : ℝ), -(p' : ℝ))) :
    Unch .std hW (bMv X Y m d) u ∧ PieceOut (tIIL X.length hB) hW (ptv .std) u := by
  constructor
  · constructor
    · rw [bMv_apply, mvIIb_of_not_moved _ _ _ _ (hu ▸ h1)]
    · rw [bMv_apply, mvIIb_of_not_moved _ _ _ _ (hn ▸ h2)]
  · show SegOut _ (pt .std Vb u.1) (pt .std Vb (next hW u).1)
    rw [hu, hn, std_pt_cut _ hp, std_pt_cut _ hp']
    exact hout

omit hm hW ht in
theorem b_hmv : ∀ v : Slot Vb, ExtSl X.length (X.length + 3) v.1 → bMv X Y m d v = pt .std Vb v.1 :=
  fun v hv => by rw [bMv_apply]; exact mvIIb_of_ext _ _ _ _ hv

/-- THE CLASSIFICATION of the type-II variant (b). -/
theorem b_rest : ∀ u : Slot Vb, OnChain hW (bT X Y m d t hm hW) u ∨ OnChain hW (bC X Y m d hm hW) u ∨
    (Unch .std hW (bMv X Y m d) u ∧ PieceOut (tIIL X.length hB) hW (ptv .std) u) := by
  intro u
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  -- the numeric side conditions of the spectators
  have above : ∀ {q : ℕ}, q < m → hB + 1 ≤ -(q : ℝ) := fun {q} hq => by
    have : (q : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : q + 1 ≤ m)
    linarith
  have below : ∀ {q : ℕ}, m + 3 ≤ q → -(q : ℝ) ≤ hB - 3 := fun {q} hq => by
    have : (m : ℝ) + 3 ≤ q := by exact_mod_cast hq
    linarith
  have slant : ∀ {q : ℕ}, m + 1 ≤ q → -(q : ℝ) ≤ hB - 1 := fun {q} hq => by
    have : (m : ℝ) + 1 ≤ q := by exact_mod_cast hq
    linarith
  have chainT := bT_chain_of X Y m d t hm hW ht
  have chainC := bC_chain_of X Y m d t hm hW ht
  have nm : ∀ a b : ℕ, b ≠ 0 → (a ≠ X.length + 2 ∨ b ≠ m + 2) → (a ≠ X.length + 1 ∨ b ≠ m + 2) →
      (a ≠ X.length + 1 ∨ b ≠ m + 1) → ¬ IsMovedB X.length m (a, b) := by
    intro a b h0 h1 h2 h3 h
    unfold IsMovedB at h
    simp only [Prod.mk.injEq] at h
    omega
  by_cases hext : ExtCol X Pb (colOf u)
  · right; right
    have hext' := (b_extCol X m d _).1 hext
    exact ⟨unch_of_extCol .std hW _ (b_hmv X Y m d) hext',
      pieceOut_of_extCol _ .std hW _ (tIIL_xge_mem _ _) (tIIL_xle_mem _ _) (unch_pt _ _ _) hext'⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, b_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inr (Or.inl (chainC 3 (by norm_num) hu
        (by cases d; exact Or.inr ⟨rfl, by norm_num⟩; exact Or.inl ⟨rfl, by norm_num⟩)))
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₁] at this
      simp [isCrossing] at this
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₂] at this
      simp [isCrossing] at this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vb j p
  · -- leftward pieces
    rw [block_col_false hu hp hb, b_extCol] at hext
    have : j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    rcases this with rfl | rfl | rfl
    · -- cut `|X|+1`, column `|X|`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := b_A11 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have htt : t = false := by rw [hpe, D1] at hb; exact hb
          exact Or.inl (chainT 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
        · have hd : d = false := by rw [hpe, D2] at hb; exact hb
          exact Or.inr (Or.inl (chainC 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
        · have hd : d = true := by rw [hpe, D3] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := b_A13 X Y m d hW hu hp hb hpm3
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp (by omega) (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ (by omega) (by omega) (by omega) (by omega))
          (tIIL_out_slant' _ _ (by omega) (slant (q := p - 2) (by omega)))))
    · -- cut `|X|+2`, column `|X|+1`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := b_A15 X Y m d hW hu hp hb hpm
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = false := by rw [hpe, D4] at hb; exact hb
          exact Or.inr (Or.inl (chainC 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
        · have htt : t = false := by rw [hpe, D5] at hb; exact hb
          exact Or.inl (chainT 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
        · have hd : d = true := by rw [hpe, D6] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := b_A18 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_below _ _ (below hpm3) _ _)))
    · -- cut `|X|+3`, column `|X|+2`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := b_A19 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = false := by rw [hpe, D7] at hb; exact hb
          exact Or.inr (Or.inl (chainC 6 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
        · have hd : d = true := by rw [hpe, D8] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 0 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
        · have htt : t = false := by rw [hpe, D9] at hb; exact hb
          exact Or.inl (chainT 3 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := b_A22 X Y m d hW hu hp hb hpm3
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_below _ _ (below hpm3) _ _)))
  · -- rightward pieces
    rw [block_col_true hu hp hb, b_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · -- cut `|X|`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := b_A1 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
      · -- `p = m`: the entry of the through-strand
        have htt : t = true := by rw [← hpe] at hb; rw [← ht]; exact hb
        exact Or.inl (chainT 0 (by norm_num) (by rw [hu, ← hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := b_A2 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp (by omega) (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ (by omega) (by omega) (by omega) (by omega)) (tIIL_out_slant _ _ (slant (by omega)))))
    · -- cut `|X|+1`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := b_A3 X Y m d hW hu hp hb hpm
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have htt : t = true := by rw [hpe, D1] at hb; exact hb
          exact Or.inl (chainT 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
        · have hd : d = true := by rw [hpe, D2] at hb; exact hb
          exact Or.inr (Or.inl (chainC 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
        · have hd : d = false := by rw [hpe, D3] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := b_A6 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_below _ _ (below hpm3) _ _)))
    · -- cut `|X|+2`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := b_A7 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = true := by rw [hpe, D4] at hb; exact hb
          exact Or.inr (Or.inl (chainC 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
        · have htt : t = true := by rw [hpe, D5] at hb; exact hb
          exact Or.inl (chainT 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
        · have hd : d = false := by rw [hpe, D6] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := b_A10 X Y m d hW hu hp hb hpm3
        exact Or.inr (Or.inr (b_spec X Y m d hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIL_out_below _ _ (below hpm3) _ _)))

end TypeIIbSpec

/-! #### H5. The type-II variant (b): the remaining specification fields -/

section TypeIIbSpec2

open U3

variable (X Y : Word) (m : ℕ) (d t : Bool) (hm : 1 ≤ m)
  (hW : (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y) X.length m = t)

local notation "Vb" => X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y
local notation "Pb" => [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)]
local notation "Vb'" => X ++ [Letter.l m d] ++ Y
local notation "Pb'" => [Letter.l m d]
local notation "hB" => (-(m : ℝ))

include hm hW ht

theorem bT_slot_ne : ∀ j j', j ≤ 3 → j' ≤ 3 → j ≠ j' → (bT X Y m d t hm hW).slot hW j ≠ (bT X Y m d t hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [bT_slot_val X Y m d t hm hW ht j hj, bT_slot_val X Y m d t hm hW ht j' hj'] at h'
  cases t
  · simp only [tvTd3, Bool.false_eq_true, ↓reduceIte] at h'
    have := tvT3_inj X m (3 - j) (3 - j') (by omega) (by omega) h'
    omega
  · simp only [tvTd3, ↓reduceIte] at h'
    exact hne (tvT3_inj X m j j' hj hj' h')

theorem bC_slot_ne : ∀ j j', j ≤ 6 → j' ≤ 6 → j ≠ j' → (bC X Y m d hm hW).slot hW j ≠ (bC X Y m d hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [bC_slot_val X Y m d t hm hW ht j hj, bC_slot_val X Y m d t hm hW ht j' hj'] at h'
  cases d
  · simp only [tvCd3, Bool.false_eq_true, ↓reduceIte] at h'
    have := tvC3_inj X m (6 - j) (6 - j') (by omega) (by omega) h'
    omega
  · simp only [tvCd3, ↓reduceIte] at h'
    exact hne (tvC3_inj X m j j' hj hj' h')

theorem b_disj : ∀ j j', j ≤ 3 → j' ≤ 6 → (bT X Y m d t hm hW).slot hW j ≠ (bC X Y m d hm hW).slot hW j' := by
  intro j j' hj hj' h
  have h' := congrArg Subtype.val h
  rw [bT_slot_val X Y m d t hm hW ht j hj, bC_slot_val X Y m d t hm hW ht j' hj'] at h'
  cases t <;> cases d <;> simp only [tvTd3, tvCd3, Bool.false_eq_true, ↓reduceIte] at h' <;>
    exact tvT3_ne_tvC3 X m hm _ _ (by omega) (by omega) h'

theorem b_prevOut₁ : Unch .std hW (bMv X Y m d) (prev hW (bT X Y m d t hm hW).u₀) ∧
    PieceOut (tIIL X.length hB) hW (ptv .std) (prev hW (bT X Y m d t hm hW).u₀) := by
  rcases b_rest X Y m d t hm hW ht (prev hW (bT X Y m d t hm hW).u₀) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · exfalso
    have hj' : j < 3 := hj
    have : (bT X Y m d t hm hW).slot hW (j + 1) = (bT X Y m d t hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact bT_slot_ne X Y m d t hm hW ht (j + 1) 0 (by omega) (by omega) (by omega) this
  · exfalso
    have hj' : j < 6 := hj
    have : (bC X Y m d hm hW).slot hW (j + 1) = (bT X Y m d t hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact b_disj X Y m d t hm hW ht 0 (j + 1) (by omega) (by omega) this.symm
  · exact h

theorem b_stopOut₁ : Unch .std hW (bMv X Y m d) ((bT X Y m d t hm hW).slot hW 3) ∧
    PieceOut (tIIL X.length hB) hW (ptv .std) ((bT X Y m d t hm hW).slot hW 3) := by
  rcases b_rest X Y m d t hm hW ht ((bT X Y m d t hm hW).slot hW 3) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · have hj' : j < 3 := hj
    exact absurd hjs (bT_slot_ne X Y m d t hm hW ht j 3 (by omega) le_rfl (by omega))
  · have hj' : j < 6 := hj
    exact absurd hjs.symm (b_disj X Y m d t hm hW ht 3 j le_rfl (by omega))
  · exact h

theorem b_prevOut₂ : Unch .std hW (bMv X Y m d) (prev hW (bC X Y m d hm hW).u₀) ∧
    PieceOut (tIIL X.length hB) hW (ptv .std) (prev hW (bC X Y m d hm hW).u₀) := by
  rcases b_rest X Y m d t hm hW ht (prev hW (bC X Y m d hm hW).u₀) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · exfalso
    have hj' : j < 3 := hj
    have : (bT X Y m d t hm hW).slot hW (j + 1) = (bC X Y m d hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact b_disj X Y m d t hm hW ht (j + 1) 0 (by omega) (by omega) this
  · exfalso
    have hj' : j < 6 := hj
    have : (bC X Y m d hm hW).slot hW (j + 1) = (bC X Y m d hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact bC_slot_ne X Y m d t hm hW ht (j + 1) 0 (by omega) (by omega) (by omega) this
  · exact h

theorem b_stopOut₂ : Unch .std hW (bMv X Y m d) ((bC X Y m d hm hW).slot hW 6) ∧
    PieceOut (tIIL X.length hB) hW (ptv .std) ((bC X Y m d hm hW).slot hW 6) := by
  rcases b_rest X Y m d t hm hW ht ((bC X Y m d hm hW).slot hW 6) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · have hj' : j < 3 := hj
    exact absurd hjs (b_disj X Y m d t hm hW ht j 6 (by omega) le_rfl)
  · have hj' : j < 6 := hj
    exact absurd hjs (bC_slot_ne X Y m d t hm hW ht j 6 (by omega) le_rfl (by omega))
  · exact h

omit hm hW ht in
/-- a grid point of the disc is a vertex of one of the two arcs -/
theorem b_vertex_of_mem {u : Slot Vb} (hmem : pt .std Vb u.1 ∈ polygon (tIIL X.length hB)) :
    (∃ i, i ≤ 3 ∧ u.1 = tvT3 X.length m i) ∨ (∃ i, i ≤ 6 ∧ u.1 = tvC3 X.length m i) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu] at hmem
  by_cases hp : p = 0
  · subst hp
    rw [std_pt_cusp] at hmem
    obtain ⟨b1, b2, -, -, -⟩ := tIIL_mem_bounds X.length hB hmem
    have e1 : 2 * X.length ≤ 2 * j + 1 := by exact_mod_cast (by linarith : (2 * X.length : ℝ) ≤ 2 * j + 1)
    have e2 : 2 * j + 1 ≤ 2 * X.length + 6 := by exact_mod_cast (by linarith : (2 * j + 1 : ℝ) ≤ 2 * X.length + 6)
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inr ⟨3, by norm_num, hu⟩
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₁] at this
      simp [isCrossing] at this
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₂] at this
      simp [isCrossing] at this
  · rw [std_pt_cut _ hp] at hmem
    obtain ⟨b1, b2, b3, b4, b5⟩ := tIIL_mem_bounds X.length hB hmem
    have e1 : X.length ≤ j := by exact_mod_cast b1
    have e2 : j ≤ X.length + 3 := by exact_mod_cast (by linarith : (j : ℝ) ≤ X.length + 3)
    have e3 : 2 * p ≤ 2 * m + 5 := by exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 2 * m + 5)
    have e4 : 4 * m ≤ 4 * p + 3 := by exact_mod_cast (by linarith : (4 * m : ℝ) ≤ 4 * p + 3)
    have e5 : 4 * p + 8 * X.length ≤ 4 * m + 8 * j + 3 := by
      exact_mod_cast (by linarith : (4 * p + 8 * X.length : ℝ) ≤ 4 * m + 8 * j + 3)
    have hj : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    have hpp : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · have : p = m := by omega
      subst this
      exact Or.inl ⟨0, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inl ⟨1, by norm_num, hu⟩
      · exact Or.inr ⟨4, by norm_num, hu⟩
      · exact Or.inr ⟨2, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inr ⟨5, by norm_num, hu⟩
      · exact Or.inl ⟨2, by norm_num, hu⟩
      · exact Or.inr ⟨1, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inr ⟨6, by norm_num, hu⟩
      · exact Or.inr ⟨0, by norm_num, hu⟩
      · exact Or.inl ⟨3, by norm_num, hu⟩

theorem b_touch : ∀ u : Slot Vb, PieceOut (tIIL X.length hB) hW (ptv .std) u → pt .std Vb u.1 ∈ polygon (tIIL X.length hB) →
    u = (bT X Y m d t hm hW).slot hW 3 ∨ u = (bC X Y m d hm hW).slot hW 6 := by
  intro u hout hmem
  have hchainT : ∀ j', j' < 3 → u ≠ (bT X Y m d t hm hW).slot hW j' := by
    intro j' hj' he
    rw [he] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (bT_chain_in X Y m d t hm hW ht j' hj').2
  have hchainC : ∀ j', j' < 6 → u ≠ (bC X Y m d hm hW).slot hW j' := by
    intro j' hj' he
    rw [he] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (bC_chain_in X Y m d t hm hW ht j' hj').2
  rcases b_vertex_of_mem X Y m d hmem with ⟨i, hi, hu⟩ | ⟨i, hi, hu⟩
  · left
    have hs := bT_slot_val X Y m d t hm hW ht
    cases t
    · have hu' : u = (bT X Y m d false hm hW).slot hW (3 - i) := by
        apply Subtype.ext
        rw [hs (3 - i) (by omega), hu]
        simp only [tvTd3, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact hu'
      · exact absurd hu' (hchainT (3 - i) (by omega))
    · have hu' : u = (bT X Y m d true hm hW).slot hW i := by
        apply Subtype.ext
        rw [hs i hi, hu]
        simp only [tvTd3, ↓reduceIte]
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact absurd hu' (hchainT i h3)
      · have : i = 3 := by omega
        subst this
        exact hu'
  · right
    have hs := bC_slot_val X Y m d t hm hW ht
    cases d
    · have hu' : u = (bC X Y m false hm hW).slot hW (6 - i) := by
        apply Subtype.ext
        rw [hs (6 - i) (by omega), hu]
        simp only [tvCd3, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact hu'
      · exact absurd hu' (hchainC (6 - i) (by omega))
    · have hu' : u = (bC X Y m true hm hW).slot hW i := by
        apply Subtype.ext
        rw [hs i hi, hu]
        simp only [tvCd3, ↓reduceIte]
      rcases Nat.lt_or_ge i 6 with h6 | h6
      · exact absurd hu' (hchainC i h6)
      · have : i = 6 := by omega
        subst this
        exact hu'

omit hm ht in
theorem b_exits : ∀ u : Slot Vb, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch .std hW (bMv X Y m d) v ∧
    PieceOut (tIIL X.length hB) hW (ptv .std) v := by
  intro u
  have hno : ∀ k', X.length ≤ k' → k' < X.length + 3 → ∀ m', letterAt Vb k' ≠ .r m' := by
    intro k' h1 h2 m'
    obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
    have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [hℓ₀]; exact fun h => by cases h
    · rw [hℓ₁]; exact fun h => by cases h
    · rw [hℓ₂]; exact fun h => by cases h
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_r hW X.length (X.length + 3) hno u
  exact ⟨v, hsc, unch_of_extCol .std hW _ (b_hmv X Y m d) hcol,
    pieceOut_of_extCol _ .std hW _ (tIIL_xge_mem _ _) (tIIL_xle_mem _ _) (unch_pt _ _ _) hcol⟩

omit hm hW ht in
/-- the crossing letters of the block: `σ_m` at column `|X|+1`, `σ_{m+1}` at column `|X|+2` -/
theorem b_σcol {k' m' : ℕ} (hℓ : letterAt Vb k' = .σ m') (hext : ¬ ExtCol X Pb k') :
    (k' = X.length + 1 ∧ m = m') ∨ (k' = X.length + 2 ∧ m + 1 = m') := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
  rw [b_extCol] at hext
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀] at hℓ; cases hℓ
  · rw [hℓ₁] at hℓ; exact Or.inl ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [hℓ₂] at hℓ; exact Or.inr ⟨rfl, Letter.σ.inj hℓ⟩

/-- the over strand of each block crossing lies on the through-strand -/
theorem b_σA_chain {k' m' : ℕ} (hk : k' < (Vb).length) (hℓ : letterAt Vb k' = .σ m') (hext : ¬ ExtCol X Pb k') :
    OnChain hW (bT X Y m d t hm hW) (σSlotA hW hk hℓ) := by
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  have hv := σSlotA_val hW hk hℓ
  rcases b_σcol X Y m d hℓ hext with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [D1] at hv
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact bT_chain_of X Y m d false hm hW ht 2 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact bT_chain_of X Y m d true hm hW ht 1 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · rw [D5] at hv
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact bT_chain_of X Y m d false hm hW ht 3 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact bT_chain_of X Y m d true hm hW ht 2 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

theorem b_hK : ∀ (k' m' : ℕ) (hk : k' < (Vb).length) (hℓ : letterAt Vb k' = .σ m'),
    ExtCol X Pb k' ↔ Unch .std hW (bMv X Y m d) (σSlotA hW hk hℓ) ∧ Unch .std hW (bMv X Y m d) (σSlotB hW hk hℓ) := by
  intro k' m' hk hℓ
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  constructor
  · intro hext
    have hext' := (b_extCol X m d k').1 hext
    exact ⟨unch_of_extCol .std hW _ (b_hmv X Y m d) (by rw [(σSlotA_spec hW hk hℓ).1]; exact hext'),
      unch_of_extCol .std hW _ (b_hmv X Y m d) (by rw [(σSlotB_spec hW hk hℓ).1]; exact hext')⟩
  · rintro ⟨-, hB'⟩
    by_contra hext
    have hv := σSlotB_val hW hk hℓ
    rcases b_σcol X Y m d hℓ hext with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- column `|X|+1`: the under slot is the lifted arm vertex or leads to it
      rw [D2] at hv
      cases d
      · simp only [Bool.false_eq_true, ↓reduceIte] at hv
        have h2 := hB'.2
        have hn : (next hW (σSlotB hW hk hℓ)).1 = tvC3 X.length m 4 := b_A16 X Y m false hW hv D4
        rw [b_mv_C X Y m false hm 4 (by norm_num) _ hn, hn, b_pt_C X Y m false hm 4 (by norm_num)] at h2
        have := congrArg Prod.snd h2
        simp only [mvB3, pvB3] at this
        linarith
      · simp only [↓reduceIte] at hv
        have h1 := hB'.1
        have hv' : (σSlotB hW hk hℓ).1 = tvC3 X.length m 4 := hv
        rw [b_mv_C X Y m true hm 4 (by norm_num) _ hv', hv', b_pt_C X Y m true hm 4 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvB3, pvB3] at this
        linarith
    · -- column `|X|+2`
      rw [show m + 1 + 1 = m + 2 from rfl, D6] at hv
      cases d
      · simp only [Bool.not_false, ↓reduceIte] at hv
        have h1 := hB'.1
        have hv' : (σSlotB hW hk hℓ).1 = tvC3 X.length m 1 := hv
        rw [b_mv_C X Y m false hm 1 (by norm_num) _ hv', hv', b_pt_C X Y m false hm 1 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvB3, pvB3] at this
        linarith
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
        have h2 := hB'.2
        have hn : (next hW (σSlotB hW hk hℓ)).1 = tvC3 X.length m 1 := b_A20 X Y m true hW hv D8
        rw [b_mv_C X Y m true hm 1 (by norm_num) _ hn, hn, b_pt_C X Y m true hm 1 (by norm_num)] at h2
        have := congrArg Prod.snd h2
        simp only [mvB3, pvB3] at this
        linarith

theorem b_hKout : ∀ (k' m' : ℕ) (hk : k' < (Vb).length) (hℓ : letterAt Vb k' = .σ m'),
    ExtCol X Pb k' ↔ PieceOut (tIIL X.length hB) hW (ptv .std) (σSlotA hW hk hℓ) := by
  intro k' m' hk hℓ
  constructor
  · intro hext
    exact pieceOut_of_extCol _ .std hW _ (tIIL_xge_mem _ _) (tIIL_xle_mem _ _) (unch_pt _ _ _)
      (by rw [(σSlotA_spec hW hk hℓ).1]; exact (b_extCol X m d k').1 hext)
  · intro hout
    by_contra hext
    obtain ⟨j, hj, hjs⟩ := b_σA_chain X Y m d t hm hW ht hk hℓ hext
    have hj' : j < 3 := hj
    rw [← hjs] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (bT_chain_in X Y m d t hm hW ht j hj').2

theorem b_cross : ∃ (k₁ m₁ : ℕ) (hk₁ : k₁ < (Vb).length) (hℓ₁ : letterAt Vb k₁ = .σ m₁) (k₂ m₂ : ℕ) (hk₂ : k₂ < (Vb).length)
    (hℓ₂ : letterAt Vb k₂ = .σ m₂), k₁ ≠ k₂ ∧ ¬ ExtCol X Pb k₁ ∧ ¬ ExtCol X Pb k₂ ∧
    (∀ (kk mm : ℕ) (_hk : kk < (Vb).length) (_hℓ : letterAt Vb kk = .σ mm), ¬ ExtCol X Pb kk → kk = k₁ ∨ kk = k₂) ∧
    ((OnChain hW (bT X Y m d t hm hW) (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW (bT X Y m d t hm hW) (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW (bC X Y m d hm hW) (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW (bC X Y m d hm hW) (σSlotB hW hk₂ hℓ₂)) ∨
     (OnChain hW (bC X Y m d hm hW) (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW (bC X Y m d hm hW) (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW (bT X Y m d t hm hW) (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW (bT X Y m d t hm hW) (σSlotB hW hk₂ hℓ₂))) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  have hk₁ : X.length + 1 < (Vb).length := by rw [b_length]; omega
  have hk₂ : X.length + 2 < (Vb).length := by rw [b_length]; omega
  have hext₁ : ¬ ExtCol X Pb (X.length + 1) := by rw [b_extCol]; omega
  have hext₂ : ¬ ExtCol X Pb (X.length + 2) := by rw [b_extCol]; omega
  refine ⟨X.length + 1, m, hk₁, hℓ₁, X.length + 2, m + 1, hk₂, hℓ₂, by omega, hext₁, hext₂, ?_, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
  · intro kk mm _ hℓ hext
    rcases b_σcol X Y m d hℓ hext with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · exact b_σA_chain X Y m d t hm hW ht hk₁ hℓ₁ hext₁
  · exact b_σA_chain X Y m d t hm hW ht hk₂ hℓ₂ hext₂
  · have hv := σSlotB_val hW hk₁ hℓ₁
    rw [D2] at hv
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact bC_chain_of X Y m false t hm hW ht 5 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact bC_chain_of X Y m true t hm hW ht 4 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · have hv := σSlotB_val hW hk₂ hℓ₂
    rw [show m + 1 + 1 = m + 2 from rfl, D6] at hv
    cases d
    · simp only [Bool.not_false, ↓reduceIte] at hv
      exact bC_chain_of X Y m false t hm hW ht 1 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
      exact bC_chain_of X Y m true t hm hW ht 0 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

/-- pieces of the through-strand never share a column -/
theorem b_pairs_TT : ∀ j j', j < 3 → j' < 3 → j ≠ j' →
    colOf ((bT X Y m d t hm hW).slot hW j) = colOf ((bT X Y m d t hm hW).slot hW j') → False := by
  intro j j' hj hj' hjj hc
  rw [bT_col X Y m d t hm hW ht j hj, bT_col X Y m d t hm hW ht j' hj'] at hc
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc
    interval_cases j <;> interval_cases j' <;> first | exact hjj rfl | (norm_num [colT] at hc <;> omega)
  · simp only [↓reduceIte] at hc
    interval_cases j <;> interval_cases j' <;> first | exact hjj rfl | (norm_num [colT] at hc <;> omega)

/-- the same-column pairs of a through-piece and a cusp-arc piece -/
theorem b_pairs_TC : ∀ j j', j < 3 → j' < 6 →
    colOf ((bT X Y m d t hm hW).slot hW j) = colOf ((bC X Y m d hm hW).slot hW j') →
    MeetSpec .std hW (bMv X Y m d) (ExtCol X Pb) ((bT X Y m d t hm hW).slot hW j) ((bC X Y m d hm hW).slot hW j') := by
  intro j j' hj hj' hc
  rw [bT_col X Y m d t hm hW ht j hj, bC_col X Y m d t hm hW ht j' hj'] at hc
  have hnT := bT_next_slot X Y m d t hm hW
  have hnC := bC_next_slot X Y m d hm hW
  have hmvT := bT_mv_slot X Y m d t hm hW ht
  have hmvC := bC_mv_slot X Y m d t hm hW ht
  cases t <;> cases d
  · -- `t = false`, `d = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 0 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (bII_NM_T2C5 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 5 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (bII_NM_T2C0 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (bII_NM_T1C4 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (bII_NM_T1C1 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 2 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (bII_NM_T0C3 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 3 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (bII_NM_T0C2 _ _).revl.revr
  · -- `t = false`, `d = true`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 0 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (bII_NM_T2C0 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 5 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (bII_NM_T2C5 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (bII_NM_T1C1 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (bII_NM_T1C4 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 2 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (bII_NM_T0C2 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 3 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (bII_NM_T0C3 _ _).revl
  · -- `t = true`, `d = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 2 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (bII_NM_T0C3 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 3 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (bII_NM_T0C2 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (bII_NM_T1C4 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (bII_NM_T1C1 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 0 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (bII_NM_T2C5 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 5 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (bII_NM_T2C0 _ _).revr
  · -- `t = true`, `d = true`
    simp only [↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 2 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (bII_NM_T0C2 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 3 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (bII_NM_T0C3 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (bII_NM_T1C1 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (bII_NM_T1C4 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 0 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (bII_NM_T2C0 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 5 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (bII_NM_T2C5 _ _)

/-- the same-column pairs of two cusp-arc pieces -/
theorem b_pairs_CC : ∀ j j', j < 6 → j' < 6 → j ≠ j' →
    colOf ((bC X Y m d hm hW).slot hW j) = colOf ((bC X Y m d hm hW).slot hW j') →
    MeetSpec .std hW (bMv X Y m d) (ExtCol X Pb) ((bC X Y m d hm hW).slot hW j) ((bC X Y m d hm hW).slot hW j') := by
  intro j j' hj hj' hjj hc
  rw [bC_col X Y m d t hm hW ht j hj, bC_col X Y m d t hm hW ht j' hj'] at hc
  have hn := bC_next_slot X Y m d hm hW
  have hmv := bC_mv_slot X Y m d t hm hW ht
  cases d
  · -- `d = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact (bII_NM_C0C5 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (bII_NM_C1C4 _ _).symm.revl.revr
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (bII_OJ234 _ _).rev
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (bII_OJ234 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (bII_NM_C1C4 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (bII_NM_C0C5 _ _).revl.revr
  · -- `d = true`
    simp only [↓reduceIte] at hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact bII_NM_C0C5 _ _
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact bII_NM_C1C4 _ _
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact bII_OJ234 _ _
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact bII_OJ234 _ _
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (bII_NM_C1C4 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (bII_NM_C0C5 _ _).symm

theorem b_pairs : ∀ u v : Slot Vb, (OnChain hW (bT X Y m d t hm hW) u ∨ OnChain hW (bC X Y m d hm hW) u) →
    (OnChain hW (bT X Y m d t hm hW) v ∨ OnChain hW (bC X Y m d hm hW) v) →
    u ≠ v → colOf u = colOf v → MeetSpec .std hW (bMv X Y m d) (ExtCol X Pb) u v := by
  intro u v hu hv hne hc
  rcases hu with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> rcases hv with ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩
  · exact (b_pairs_TT X Y m d t hm hW ht j j' hj hj' (fun h => hne (by rw [h])) hc).elim
  · exact b_pairs_TC X Y m d t hm hW ht j j' hj hj' hc
  · exact (b_pairs_TC X Y m d t hm hW ht j' j hj' hj hc.symm).symm
  · exact b_pairs_CC X Y m d t hm hW ht j j' hj hj' (fun h => hne (by rw [h])) hc

theorem b_genericData : GenericData .std hW (bMv X Y m d) (ExtCol X Pb) :=
  genericData_of' (tIIL X.length hB) .std hW (bMv X Y m d) (ExtCol X Pb)
    (fun u => OnChain hW (bT X Y m d t hm hW) u ∨ OnChain hW (bC X Y m d hm hW) u)
    (mvIIb_injective _ _ _ m) (mvIIb_xcoord _ _ _ _)
    (fun u => by
      rcases b_rest X Y m d t hm hW ht u with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h)
    (fun u hu => by
      rcases hu with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact (bT_chain_in X Y m d t hm hW ht j hj).1
      · exact (bC_chain_in X Y m d t hm hW ht j hj).1)
    (b_pairs X Y m d t hm hW ht)
    (fun k' m' hk hℓ hA' hB' => (b_hK X Y m d t hm hW ht k' m' hk hℓ).2 ⟨hA', hB'⟩)

theorem b_riiSpec : RIISpec (tIIL X.length hB) .std hW (bMv X Y m d) (ExtCol X Pb) (bT X Y m d t hm hW) (bC X Y m d hm hW) where
  disc := tIIL_isDisc _ _
  hK := b_hK X Y m d t hm hW ht
  hKout := b_hKout X Y m d t hm hW ht
  moved := b_moved X Y m d hm
  chain₁ := bT_chain_in X Y m d t hm hW ht
  chain₂ := bC_chain_in X Y m d t hm hW ht
  vert₁ := bT_vert X Y m d t hm hW ht
  vert₂ := bC_vert X Y m d t hm hW ht
  rest := b_rest X Y m d t hm hW ht
  prevOut₁ := b_prevOut₁ X Y m d t hm hW ht
  stopOut₁ := b_stopOut₁ X Y m d t hm hW ht
  prevOut₂ := b_prevOut₂ X Y m d t hm hW ht
  stopOut₂ := b_stopOut₂ X Y m d t hm hW ht
  disj := fun j hj j' hj' => b_disj X Y m d t hm hW ht j j' (Nat.le_of_lt hj) (Nat.le_of_lt hj')
  touch := b_touch X Y m d t hm hW ht
  exits := b_exits X Y m d hW
  cross := b_cross X Y m d t hm hW ht

theorem b_riiData (hne : Vb ≠ []) :
    Nonempty (RIIData (polygon (tIIL X.length hB))
      (mvDiagram .std hW hne (bMv X Y m d) (ExtCol X Pb) (b_genericData X Y m d t hm hW ht)) (rlDiagram .std hW hne)) :=
  riiData_of hne (b_genericData X Y m d t hm hW ht) (b_riiSpec X Y m d t hm hW ht)

theorem b_recordIso (hne : Vb ≠ []) (W' : OWord) (hW'eq : W'.letters = Vb') :
    Nonempty (RecordIso (mvDiagram .std hW hne (bMv X Y m d) (ExtCol X Pb) (b_genericData X Y m d t hm hW ht)).record
      (realize W').diagram.record) := by
  have hW' : (Vb').Closed := by have := W'.closed; rwa [hW'eq] at this
  refine ⟨vertexMovedRecordIso' X Pb Y Pb' (by simp) (b_sameEffect X Y m d hm hW) hW hW' .std hne _ _ _ _
    (slotDiagramData_of .std hW hne (bMv X Y m d) (ExtCol X Pb) (b_genericData X Y m d t hm hW ht) (b_hK X Y m d t hm hW ht))
    (b_passage X Y m d hm hW hW') (b_hexit X Y m d hW) (a'_hexit X Y m d hW') ?_ W' hW'eq (by simp)⟩
  intro k' hk1 hk2
  simp only [List.length_cons, List.length_nil] at hk2
  have : k' = X.length := by omega
  subst this
  rw [a'_letters X Y m d]; rfl

omit hW ht in
/-- LEAF CASE (type II, variant (b): `l_{m+1} d σ_m σ_{m+1} ↦ l_m d`). -/
theorem typeII_b {W W' : OWord} (hWeq : W.letters = Vb) (hW'eq : W'.letters = Vb') :
    ∃ D : Diagram, RII D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨Wl, hWl⟩ := W
  simp only at hWeq
  subst hWeq
  have hne : Vb ≠ [] := by simp
  rw [realize_eq_realizeAt ⟨_, hWl⟩ hne]
  exact ⟨mvDiagram .std hWl hne (bMv X Y m d) (ExtCol X Pb) (b_genericData X Y m d _ hm hWl rfl),
    ⟨polygon (tIIL X.length hB), Or.inl (b_riiData X Y m d _ hm hWl rfl hne)⟩,
    b_recordIso X Y m d _ hm hWl rfl hne W' hW'eq⟩

end TypeIIbSpec2

/-! #### I1. The type-II variant (d): `σ_{m+1} σ_m r_{m+1} ↦ r_m`, the word level -/

/-- the through-strand's vertices (entry at cut `k`, index `m+2`): under both crossings, out at `(k+3, m)` -/
def tvT4 (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k, m + 2)
  | 1 => (k + 1, m + 1)
  | 2 => (k + 2, m)
  | _ => (k + 3, m)

/-- the cusp arc's vertices, from the upper arm `(k, m)` through the right cusp to the lower arm `(k, m+1)` -/
def tvC4 (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k, m)
  | 1 => (k + 1, m)
  | 2 => (k + 2, m + 1)
  | 3 => (k + 2, 0)
  | 4 => (k + 2, m + 2)
  | 5 => (k + 1, m + 2)
  | _ => (k, m + 1)

def tvTd4 (k m : ℕ) (t : Bool) (j : ℕ) : ℕ × ℕ := if t then tvT4 k m j else tvT4 k m (3 - j)
def tvCd4 (k m : ℕ) (e : Bool) (j : ℕ) : ℕ × ℕ := if e then tvC4 k m j else tvC4 k m (6 - j)

section TypeIIdWord

open U3

variable (X Y : Word) (m : ℕ) (t e : Bool) (hm : 1 ≤ m)
  (hW : (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y) X.length (m + 2) = t)
  (he : bit (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y) (X.length + 2) (m + 1) = e)

local notation "Vd" => X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y
local notation "Pd" => [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)]
local notation "Vd'" => X ++ [Letter.r m] ++ Y
local notation "Pd'" => [Letter.r m]

theorem d_letters : letterAt Vd X.length = .σ (m + 1) ∧ letterAt Vd (X.length + 1) = .σ m ∧
    letterAt Vd (X.length + 2) = .r (m + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have := letterAt_block X Pd Y (i := 0) (by simp); simpa using this
  · have := letterAt_block X Pd Y (i := 1) (by simp); simpa using this
  · have := letterAt_block X Pd Y (i := 2) (by simp); simpa using this

theorem d_length : (Vd).length = X.length + 3 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem d_extCol (k : ℕ) : ExtCol X Pd k ↔ k + 1 ≤ X.length ∨ X.length + 3 ≤ k := by
  unfold ExtCol; simp

theorem d_shift : shiftIdx X Pd Pd' (X.length + 3) = X.length + 1 := by
  unfold shiftIdx; simp

theorem d_cut_start : cut Vd' X.length = cut Vd X.length := by
  unfold cut
  rw [List.append_assoc, List.take_left' rfl, List.append_assoc, List.take_left' rfl]

theorem d_bit_start (p : ℕ) : bit Vd' X.length p = bit Vd X.length p := by
  rw [bit_eq, bit_eq, d_cut_start]

include hW

include hm in
theorem d_sameEffect : SameEffect X Pd Pd' :=
  sameEffect_of_replace X Pd Y Pd' hW (fun c c' h => run_typeII_r_right hm h)

include hm in
theorem d_cut_end : cut Vd' (X.length + 1) = cut Vd (X.length + 3) := by
  have hE := d_sameEffect X Y m hm hW
  unfold SameEffect at hE
  unfold cut
  rw [List.take_left' (by simp), List.take_left' (by simp), hE]

include hm in
theorem d_bit_end (p : ℕ) : bit Vd' (X.length + 1) p = bit Vd (X.length + 3) p := by
  rw [bit_eq, bit_eq, d_cut_end X Y m hm hW]

theorem d_cutlen : m + 2 ≤ (cut Vd X.length).length ∧ (cut Vd (X.length + 1)).length = (cut Vd X.length).length ∧
    (cut Vd (X.length + 2)).length = (cut Vd (X.length + 1)).length ∧
    (cut Vd (X.length + 3)).length + 2 = (cut Vd (X.length + 2)).length := by
  have hk₀ : X.length < (Vd).length := by rw [d_length]; omega
  have hk₁ : X.length + 1 < (Vd).length := by rw [d_length]; omega
  have hk₂ : X.length + 2 < (Vd).length := by rw [d_length]; omega
  obtain ⟨-, h2, h3, -, -⟩ := σ_facts hW hk₀ (d_letters X Y m).1
  obtain ⟨-, -, h3', -, -⟩ := σ_facts hW hk₁ (d_letters X Y m).2.1
  obtain ⟨D⟩ := decomp hW (X.length + 2) hk₂
  have h1 := D.length_add
  have har : (letterAt Vd (X.length + 2)).arity = 2 := by rw [(d_letters X Y m).2.2]; rfl
  have hco : (letterAt Vd (X.length + 2)).coarity = 0 := by rw [(d_letters X Y m).2.2]; rfl
  rw [har, hco, show X.length + 2 + 1 = X.length + 3 from rfl] at h1
  rw [show X.length + 1 + 1 = X.length + 2 from rfl] at h3'
  exact ⟨h2, h3, h3', by omega⟩

include hm ht he in
/-- the bits: the cusp arms carry `e`, `!e`; the through-strand carries `t` -/
theorem d_bits :
    bit Vd X.length m = e ∧ bit Vd X.length (m + 1) = !e ∧
    bit Vd (X.length + 1) m = e ∧ bit Vd (X.length + 1) (m + 1) = t ∧ bit Vd (X.length + 1) (m + 2) = !e ∧
    bit Vd (X.length + 2) m = t ∧ bit Vd (X.length + 2) (m + 2) = !e ∧ bit Vd (X.length + 3) m = t := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
  have hk₀ : X.length < (Vd).length := by rw [d_length]; omega
  have hk₁ : X.length + 1 < (Vd).length := by rw [d_length]; omega
  have hk₂ : X.length + 2 < (Vd).length := by rw [d_length]; omega
  obtain ⟨-, -, -, h4, h5⟩ := σ_facts hW hk₀ hℓ₀
  obtain ⟨-, -, -, h4', h5'⟩ := σ_facts hW hk₁ hℓ₁
  obtain ⟨-, hr⟩ := r_bits hW hk₂ hℓ₂
  rw [show m + 1 + 1 = m + 2 from rfl] at h4 h5 hr
  have E7 : bit Vd (X.length + 2) (m + 2) = !e := by
    rw [he] at hr
    exact U3.bool_eq_not_of_ne (Ne.symm hr)
  have E3 : bit Vd (X.length + 1) m = e := by rw [← he, h4']
  have E1 : bit Vd X.length m = e := by
    rw [← E3, bit_succ_of_lt hW hk₀ hm (by rw [hℓ₀]; simp only [idx]; omega)]
  have E5 : bit Vd (X.length + 1) (m + 2) = !e := by
    have := bit_succ_of_ge hW hk₁ (p := m + 2) (by rw [hℓ₁]; simp only [idx, arity]; omega)
    rw [hℓ₁] at this
    simp only [coarity, arity] at this
    rw [show m + 2 + 2 - 2 = m + 2 by omega] at this
    rw [← this, E7]
  have E2 : bit Vd X.length (m + 1) = !e := by rw [← h4, E5]
  have E4 : bit Vd (X.length + 1) (m + 1) = t := by rw [h5, ht]
  have E6 : bit Vd (X.length + 2) m = t := by rw [h5', E4]
  have E8 : bit Vd (X.length + 3) m = t := by
    rw [bit_succ_of_lt hW hk₂ hm (by rw [hℓ₂]; simp only [idx]; omega), E6]
  exact ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩

/-! the successor table (columns `|X|`: `σ_{m+1}`, `|X|+1`: `σ_m`, `|X|+2`: `r_{m+1}`) -/

theorem d_A1 {s : Slot Vd} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vd X.length p = true)
    (hpm : p < m + 1) : (next hW s).1 = (X.length + 1, p) ∧ bit Vd (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(d_letters X Y m).1]; exact hpm)

theorem d_A2 {s : Slot Vd} (hs : s.1 = (X.length, m + 1)) (hb : bit Vd X.length (m + 1) = true) :
    (next hW s).1 = (X.length + 1, m + 2) :=
  next_σ_right_idx hW (d_letters X Y m).1 hs hb

theorem d_A3 {s : Slot Vd} (hs : s.1 = (X.length, m + 2)) (hb : bit Vd X.length (m + 2) = true) :
    (next hW s).1 = (X.length + 1, m + 1) :=
  next_σ_right_succ hW (d_letters X Y m).1 hs hb

theorem d_A4 {s : Slot Vd} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vd X.length p = true)
    (hpm : m + 3 ≤ p) : (next hW s).1 = (X.length + 1, p) ∧ bit Vd (X.length + 1) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(d_letters X Y m).1]; simp only [idx, arity]; omega)
  rw [(d_letters X Y m).1] at this
  simpa [coarity, arity] using this

theorem d_A5 {s : Slot Vd} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vd (X.length + 1) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vd (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(d_letters X Y m).2.1]; exact hpm)

theorem d_A6 {s : Slot Vd} (hs : s.1 = (X.length + 1, m)) (hb : bit Vd (X.length + 1) m = true) :
    (next hW s).1 = (X.length + 2, m + 1) :=
  next_σ_right_idx hW (d_letters X Y m).2.1 hs hb

theorem d_A7 {s : Slot Vd} (hs : s.1 = (X.length + 1, m + 1)) (hb : bit Vd (X.length + 1) (m + 1) = true) :
    (next hW s).1 = (X.length + 2, m) :=
  next_σ_right_succ hW (d_letters X Y m).2.1 hs hb

theorem d_A8 {s : Slot Vd} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vd (X.length + 1) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vd (X.length + 2) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(d_letters X Y m).2.1]; simpa [idx, arity] using hpm)
  rw [(d_letters X Y m).2.1] at this
  simpa [coarity, arity] using this

theorem d_A9 {s : Slot Vd} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vd (X.length + 2) p = true) (hpm : p < m + 1) :
    (next hW s).1 = (X.length + 3, p) ∧ bit Vd (X.length + 3) p = true :=
  next_right_lt hW hs hp hb (by rw [(d_letters X Y m).2.2]; exact hpm)

theorem d_A10 {s : Slot Vd} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p = m + 1 ∨ p = m + 2)
    (hb : bit Vd (X.length + 2) p = true) : (next hW s).1 = (X.length + 2, 0) :=
  next_arm_r hW (by have := slot_col_lt hW hs; omega) (d_letters X Y m).2.2 hs (by omega) hb

theorem d_A11 {s : Slot Vd} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vd (X.length + 2) p = true) (hpm : m + 3 ≤ p) :
    (next hW s).1 = (X.length + 3, p - 2) ∧ bit Vd (X.length + 3) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(d_letters X Y m).2.2]; simp only [idx, arity]; omega)
  rw [(d_letters X Y m).2.2] at this
  simpa [coarity, arity] using this

include he in
theorem d_A12 {s : Slot Vd} (hs : s.1 = (X.length + 2, 0)) :
    (next hW s).1 = (X.length + 2, if e then m + 2 else m + 1) := by
  rw [next_cusp_r hW (d_letters X Y m).2.2 hs, he]

theorem d_A13 {s : Slot Vd} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vd (X.length + 1) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length, q) ∧ bit Vd X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (d_letters X Y m).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem d_A14 {s : Slot Vd} (hs : s.1 = (X.length + 1, m + 1)) (hb : bit Vd (X.length + 1) (m + 1) = false) :
    (next hW s).1 = (X.length, m + 2) :=
  next_σ_left_idx hW (d_letters X Y m).1 hs hb

theorem d_A15 {s : Slot Vd} (hs : s.1 = (X.length + 1, m + 2)) (hb : bit Vd (X.length + 1) (m + 2) = false) :
    (next hW s).1 = (X.length, m + 1) :=
  next_σ_left_succ hW (d_letters X Y m).1 hs hb

theorem d_A16 {s : Slot Vd} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vd (X.length + 1) q = false) (hqm : m + 3 ≤ q) :
    (next hW s).1 = (X.length, q) ∧ bit Vd X.length q = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (d_letters X Y m).1]; simp only [idx, coarity]; omega)
  rw [Nat.add_sub_cancel, (d_letters X Y m).1] at this
  simpa [arity, coarity] using this

theorem d_A17 {s : Slot Vd} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vd (X.length + 2) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vd (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e2, (d_letters X Y m).2.1]; exact hqm)
  rwa [e2] at this

theorem d_A18 {s : Slot Vd} (hs : s.1 = (X.length + 2, m)) (hb : bit Vd (X.length + 2) m = false) :
    (next hW s).1 = (X.length + 1, m + 1) :=
  next_σ_left_idx hW (d_letters X Y m).2.1 hs hb

theorem d_A19 {s : Slot Vd} (hs : s.1 = (X.length + 2, m + 1)) (hb : bit Vd (X.length + 2) (m + 1) = false) :
    (next hW s).1 = (X.length + 1, m) :=
  next_σ_left_succ hW (d_letters X Y m).2.1 hs hb

theorem d_A20 {s : Slot Vd} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vd (X.length + 2) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vd (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e2, (d_letters X Y m).2.1]; simpa [idx, coarity] using hqm)
  rw [e2, (d_letters X Y m).2.1] at this
  simpa [arity, coarity] using this

theorem d_A21 {s : Slot Vd} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vd (X.length + 3) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length + 2, q) ∧ bit Vd (X.length + 2) q = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_lt hW hs hq hb (by rw [e3, (d_letters X Y m).2.2]; exact hqm)
  rwa [e3] at this

theorem d_A22 {s : Slot Vd} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vd (X.length + 3) q = false) (hqm : m + 1 ≤ q) :
    (next hW s).1 = (X.length + 2, q + 2) ∧ bit Vd (X.length + 2) (q + 2) = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_ge hW hs hq hb (by rw [e3, (d_letters X Y m).2.2]; simp only [idx, coarity]; omega)
  rw [e3, (d_letters X Y m).2.2] at this
  simpa [arity, coarity] using this

theorem d_hexit : ∀ u : Slot Vd, ∃ n, ExtPiece X Pd Y ((next hW)^[n] u) := by
  apply hexit_of_no_l X Pd Y hW
  intro k' h1 h2 m' d'
  simp only [List.length_cons, List.length_nil] at h2
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀]; exact fun h => by cases h
  · rw [hℓ₁]; exact fun h => by cases h
  · rw [hℓ₂]; exact fun h => by cases h

/-! the two chains -/

include hm in
theorem d_isSlot_T0 : IsSlot Vd (tvTd4 X.length m t 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := d_cutlen X Y m hW
  have hlen := d_length X Y m
  cases t
  · have e : tvTd4 X.length m false 0 = (X.length + 3, m) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)
  · have e : tvTd4 X.length m true 0 = (X.length, m + 2) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)

include hm in
theorem d_isSlot_C0 : IsSlot Vd (tvCd4 X.length m e 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := d_cutlen X Y m hW
  have hlen := d_length X Y m
  cases e
  · have e : tvCd4 X.length m false 0 = (X.length, m + 1) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)
  · have e : tvCd4 X.length m true 0 = (X.length, m) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)

include hm in
/-- the arc of the through-strand: three pieces -/
def dT : Chain Vd := ⟨⟨tvTd4 X.length m t 0, d_isSlot_T0 X Y m t hm hW⟩, 3, by norm_num⟩

include hm in
/-- the arc of the cusp: six pieces -/
def dC : Chain Vd := ⟨⟨tvCd4 X.length m e 0, d_isSlot_C0 X Y m e hm hW⟩, 6, by norm_num⟩

include hm ht he in
theorem dT_slot_val : ∀ j, j ≤ 3 → ((dT X Y m t hm hW).slot hW j).1 = tvTd4 X.length m t j := by
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  have s0 : ((dT X Y m t hm hW).slot hW 0).1 = tvTd4 X.length m t 0 := rfl
  intro j hj
  cases t
  · simp only [tvTd4, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((dT X Y m false hm hW).slot hW 1).1 = tvT4 X.length m 2 := by
      rw [Chain.slot_succ]; exact (d_A21 X Y m hW s0 (by omega) E8 (by omega)).1
    have s2 : ((dT X Y m false hm hW).slot hW 2).1 = tvT4 X.length m 1 := by
      rw [Chain.slot_succ]; exact d_A18 X Y m hW s1 E6
    have s3 : ((dT X Y m false hm hW).slot hW 3).1 = tvT4 X.length m 0 := by
      rw [Chain.slot_succ]; exact d_A14 X Y m hW s2 E4
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
  · simp only [tvTd4, ↓reduceIte] at s0 ⊢
    have s1 : ((dT X Y m true hm hW).slot hW 1).1 = tvT4 X.length m 1 := by
      rw [Chain.slot_succ]; exact d_A3 X Y m hW s0 ht
    have s2 : ((dT X Y m true hm hW).slot hW 2).1 = tvT4 X.length m 2 := by
      rw [Chain.slot_succ]; exact d_A7 X Y m hW s1 E4
    have s3 : ((dT X Y m true hm hW).slot hW 3).1 = tvT4 X.length m 3 := by
      rw [Chain.slot_succ]; exact (d_A9 X Y m hW s2 (by omega) E6 (by omega)).1
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3

include hm ht he in
theorem dC_slot_val : ∀ j, j ≤ 6 → ((dC X Y m e hm hW).slot hW j).1 = tvCd4 X.length m e j := by
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  have s0 : ((dC X Y m e hm hW).slot hW 0).1 = tvCd4 X.length m e 0 := rfl
  intro j hj
  cases e
  · simp only [tvCd4, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((dC X Y m false hm hW).slot hW 1).1 = tvC4 X.length m 5 := by
      rw [Chain.slot_succ]; exact d_A2 X Y m hW s0 (by rw [E2]; rfl)
    have s2 : ((dC X Y m false hm hW).slot hW 2).1 = tvC4 X.length m 4 := by
      rw [Chain.slot_succ]; exact (d_A8 X Y m hW s1 (by omega) (by rw [E5]; rfl) le_rfl).1
    have s3 : ((dC X Y m false hm hW).slot hW 3).1 = tvC4 X.length m 3 := by
      rw [Chain.slot_succ]; exact d_A10 X Y m hW s2 (Or.inr rfl) (by rw [E7]; rfl)
    have s4 : ((dC X Y m false hm hW).slot hW 4).1 = tvC4 X.length m 2 := by
      rw [Chain.slot_succ, d_A12 X Y m false hW he s3]; rfl
    have s5 : ((dC X Y m false hm hW).slot hW 5).1 = tvC4 X.length m 1 := by
      rw [Chain.slot_succ]; exact d_A19 X Y m hW s4 he
    have s6 : ((dC X Y m false hm hW).slot hW 6).1 = tvC4 X.length m 0 := by
      rw [Chain.slot_succ]; exact (d_A13 X Y m hW s5 (by omega) E3 (by omega)).1
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
  · simp only [tvCd4, ↓reduceIte] at s0 ⊢
    have s1 : ((dC X Y m true hm hW).slot hW 1).1 = tvC4 X.length m 1 := by
      rw [Chain.slot_succ]; exact (d_A1 X Y m hW s0 (by omega) E1 (by omega)).1
    have s2 : ((dC X Y m true hm hW).slot hW 2).1 = tvC4 X.length m 2 := by
      rw [Chain.slot_succ]; exact d_A6 X Y m hW s1 E3
    have s3 : ((dC X Y m true hm hW).slot hW 3).1 = tvC4 X.length m 3 := by
      rw [Chain.slot_succ]; exact d_A10 X Y m hW s2 (Or.inl rfl) he
    have s4 : ((dC X Y m true hm hW).slot hW 4).1 = tvC4 X.length m 4 := by
      rw [Chain.slot_succ, d_A12 X Y m true hW he s3]; rfl
    have s5 : ((dC X Y m true hm hW).slot hW 5).1 = tvC4 X.length m 5 := by
      rw [Chain.slot_succ]; exact (d_A20 X Y m hW s4 (by omega) (by rw [E7]; rfl) le_rfl).1
    have s6 : ((dC X Y m true hm hW).slot hW 6).1 = tvC4 X.length m 6 := by
      rw [Chain.slot_succ]; exact d_A15 X Y m hW s5 (by rw [E5]; rfl)
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6

include hm ht he in
theorem dT_col : ∀ j, j < 3 → colOf ((dT X Y m t hm hW).slot hW j) = if t then colT X.length j else colT X.length (2 - j) := by
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  have hv := dT_slot_val X Y m t e hm hW ht he
  intro j hj
  cases t
  · simp only [tvTd4, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvT4] using E8)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp; omega) (by simpa [tvT4] using E6)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp) (by simpa [tvT4] using E4)]; rfl
  · simp only [tvTd4, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp) (by simpa [tvT4] using ht)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp) (by simpa [tvT4] using E4)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp; omega) (by simpa [tvT4] using E6)]; rfl

include hm ht he in
theorem dC_col : ∀ j, j < 6 → colOf ((dC X Y m e hm hW).slot hW j) = colC2 X.length j := by
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  have hv := dC_slot_val X Y m t e hm hW ht he
  intro j hj
  cases e
  · simp only [tvCd4, Bool.false_eq_true, ↓reduceIte] at hv
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp) (by simpa [tvC4] using E2)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp) (by simpa [tvC4] using E5)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp) (by simpa [tvC4] using E7)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_false (hv 4 (by norm_num)) (by simp) (by simpa [tvC4] using he)]; rfl
    · rw [block_col_false (hv 5 (by norm_num)) (by simp; omega) (by simpa [tvC4] using E3)]; rfl
  · simp only [tvCd4, ↓reduceIte] at hv
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvC4] using E1)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp; omega) (by simpa [tvC4] using E3)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp) (by simpa [tvC4] using he)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_false (hv 4 (by norm_num)) (by simp) (by simpa [tvC4] using E7)]; rfl
    · rw [block_col_false (hv 5 (by norm_num)) (by simp) (by simpa [tvC4] using E5)]; rfl

include hm ht he in
theorem dT_col3 : ExtCol X Pd (colOf ((dT X Y m t hm hW).slot hW 3)) := by
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  have hv := dT_slot_val X Y m t e hm hW ht he 3 le_rfl
  rw [d_extCol]
  cases t
  · simp only [tvTd4, Bool.false_eq_true, ↓reduceIte, tvT4] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) ht]; omega
  · simp only [tvTd4, ↓reduceIte, tvT4] at hv
    rw [block_col_true hv (by omega) E8]; omega

include hm ht he in
theorem dC_col6 : ExtCol X Pd (colOf ((dC X Y m e hm hW).slot hW 6)) := by
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  have hv := dC_slot_val X Y m t e hm hW ht he 6 le_rfl
  rw [d_extCol]
  cases e
  · simp only [tvCd4, Bool.false_eq_true, ↓reduceIte, tvC4] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) E1]; omega
  · simp only [tvCd4, ↓reduceIte, tvC4] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) (by rw [E2]; rfl)]; omega

end TypeIIdWord

/-! #### I2. The type-II variant (d): the block passage (the target word `X ++ [r_m] ++ Y` is that of variant (c)) -/

section TypeIIdPassage

open U3

variable (X Y : Word) (m : ℕ) (t e : Bool) (hm : 1 ≤ m)
  (hW : (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y).Closed)
  (hW' : (X ++ [Letter.r m] ++ Y).Closed)

local notation "Vd" => X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y
local notation "Pd" => [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)]
local notation "Vd'" => X ++ [Letter.r m] ++ Y
local notation "Pd'" => [Letter.r m]

include hm hW hW'

/-- THE BLOCK PASSAGE of the type-II variant (d). -/
theorem d_passage : Passage X Pd Y Pd' hW hW' := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ :=
    d_bits X Y m (bit Vd X.length (m + 2)) (bit Vd (X.length + 2) (m + 1)) hm hW rfl rfl
  have hP : Pd ≠ [] := by simp
  have hE := d_sameEffect X Y m hm hW
  have shiftL : ∀ p, extPair X Pd Pd' (X.length, p) = (X.length, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pd Pd' le_rfl]
  have shiftR : ∀ p, extPair X Pd Pd' (X.length + 3, p) = (X.length + 1, p) := by
    intro p; simp only [extPair, d_shift X m]
  constructor
  intro b hext hcol
  let b' : Slot Vd' := ⟨extPair X Pd Pd' b.1, isSlot_ext X Pd Y Pd' hP hE b.2 hext⟩
  have hb'v : b'.1 = extPair X Pd Pd' b.1 := rfl
  -- the through-strand, as the chain `dT`
  have curlT : b = (dT X Y m (bit Vd X.length (m + 2)) hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Vd), (next hW)^[n] b = c ∧ ExtCol X Pd (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pd (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot Vd'), b'.1 = extPair X Pd Pd' b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pd Pd' c.1 ∧ ∀ i < m', ¬ ExtCol X Pd' (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨3, (dT X Y m _ hm hW).slot hW 3, by rw [hb]; rfl, dT_col3 X Y m _ _ hm hW rfl rfl, ?_, ?_⟩
    · intro i hi
      have h := dT_col X Y m _ _ hm hW rfl rfl i hi
      rw [hb]
      show ¬ ExtCol X Pd (colOf ((dT X Y m _ hm hW).slot hW i))
      rw [h, d_extCol]
      cases bit Vd X.length (m + 2) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> interval_cases i <;> simp [colT]
    · have h0 := dT_slot_val X Y m _ _ hm hW rfl rfl 0 (by norm_num)
      have h3 := dT_slot_val X Y m _ _ hm hW rfl rfl 3 le_rfl
      rw [Chain.slot_zero] at h0
      cases hE0 : bit Vd X.length (m + 2)
      · -- leftward: `W'`: `(|X|+1, m)` leftward under the cusp of `r_m` to `(|X|, m+2)`
        rw [hE0] at h0 h3 hb
        have hb0 : b.1 = (X.length + 3, m) := by rw [hb]; exact h0
        have hc3 : ((dT X Y m false hm hW).slot hW 3).1 = (X.length, m + 2) := h3
        have hslot : IsSlot Vd' (X.length + 1, m) := by
          have := isSlot_ext X Pd Y Pd' hP hE (s := (X.length + 3, m)) (hb0 ▸ b.2)
            (isExtSlot_cut_right X Pd (p := m) (by omega))
          rwa [shiftR] at this
        have hbit' : bit Vd' (X.length + 1) m = false := by rw [d_bit_end X Y m hm hW, E8, hE0]
        refine ⟨1, ⟨(X.length + 1, m), hslot⟩, by rw [hb0, shiftR], ?_, ?_⟩
        · rw [hc3, shiftL, Function.iterate_one]
          exact (c'_L6 X Y m hW' (s := ⟨_, hslot⟩) (q := m) rfl (by omega) hbit' le_rfl).1
        · intro i hi
          have : i = 0 := by omega
          subst this
          rw [Function.iterate_zero, id, block_col_false (s := ⟨_, hslot⟩) (k := X.length + 1) (p := m) rfl (by omega) hbit',
            c'_extCol]; omega
      · rw [hE0] at h0 h3 hb
        have hb0 : b.1 = (X.length, m + 2) := by rw [hb]; exact h0
        have hc3 : ((dT X Y m true hm hW).slot hW 3).1 = (X.length + 3, m) := h3
        have hslot : IsSlot Vd' (X.length, m + 2) := by
          have := isSlot_ext X Pd Y Pd' hP hE (s := (X.length, m + 2)) (hb0 ▸ b.2)
            (isExtSlot_cut_left X Pd (p := m + 2) (by omega))
          rwa [shiftL] at this
        have hbit' : bit Vd' X.length (m + 2) = true := by rw [d_bit_start, hE0]
        refine ⟨1, ⟨(X.length, m + 2), hslot⟩, by rw [hb0, shiftL], ?_, ?_⟩
        · rw [hc3, shiftR, Function.iterate_one]
          have := (c'_L4 X Y m hW' (s := ⟨_, hslot⟩) (p := m + 2) rfl (by omega) hbit' le_rfl).1
          rwa [show m + 2 - 2 = m by omega] at this
        · intro i hi
          have : i = 0 := by omega
          subst this
          rw [Function.iterate_zero, id, block_col_true (s := ⟨_, hslot⟩) (k := X.length) (p := m + 2) rfl (by omega) hbit',
            c'_extCol]; omega
  -- the cusp arc, as the chain `dC`
  have curlC : b = (dC X Y m (bit Vd (X.length + 2) (m + 1)) hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Vd), (next hW)^[n] b = c ∧ ExtCol X Pd (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pd (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot Vd'), b'.1 = extPair X Pd Pd' b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pd Pd' c.1 ∧ ∀ i < m', ¬ ExtCol X Pd' (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨6, (dC X Y m _ hm hW).slot hW 6, by rw [hb]; rfl, dC_col6 X Y m _ _ hm hW rfl rfl, ?_, ?_⟩
    · intro i hi
      have h := dC_col X Y m _ _ hm hW rfl rfl i hi
      rw [hb]
      show ¬ ExtCol X Pd (colOf ((dC X Y m _ hm hW).slot hW i))
      rw [h, d_extCol]
      interval_cases i <;> simp [colC2]
    · have h0 := dC_slot_val X Y m _ _ hm hW rfl rfl 0 (by norm_num)
      have h6 := dC_slot_val X Y m _ _ hm hW rfl rfl 6 le_rfl
      rw [Chain.slot_zero] at h0
      -- `W'`: `(|X|, m)` (`e`) or `(|X|, m+1)` (`!e`) rightward into the cusp of `r_m`, out along the other arm
      cases hE0 : bit Vd (X.length + 2) (m + 1)
      · rw [hE0] at h0 h6 hb
        have hb0 : b.1 = (X.length, m + 1) := by rw [hb]; exact h0
        have hc6 : ((dC X Y m false hm hW).slot hW 6).1 = (X.length, m) := h6
        have hslot : IsSlot Vd' (X.length, m + 1) := by
          have := isSlot_ext X Pd Y Pd' hP hE (s := (X.length, m + 1)) (hb0 ▸ b.2)
            (isExtSlot_cut_left X Pd (p := m + 1) (by omega))
          rwa [shiftL] at this
        have hbit' : bit Vd' X.length (m + 1) = true := by rw [d_bit_start, E2, hE0]; rfl
        have hbm' : bit Vd' X.length m = false := by rw [d_bit_start, E1, hE0]
        have h1' := c'_L2 X Y m hW' (s := ⟨_, hslot⟩) rfl (Or.inr rfl) hbit'
        have h2' := c'_L3 X Y m hW' h1'
        rw [hbm'] at h2'
        simp only [Bool.false_eq_true, ↓reduceIte] at h2'
        refine ⟨2, ⟨_, hslot⟩, by rw [hb0, shiftL], ?_, ?_⟩
        · rw [hc6, shiftL, Function.iterate_succ_apply', Function.iterate_one, h2']
        · intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · rw [Function.iterate_zero, id, block_col_true (s := ⟨_, hslot⟩) (k := X.length) (p := m + 1) rfl (by omega) hbit',
              c'_extCol]; omega
          · rw [Function.iterate_one, block_col_vertex h1', c'_extCol]; omega
      · rw [hE0] at h0 h6 hb
        have hb0 : b.1 = (X.length, m) := by rw [hb]; exact h0
        have hc6 : ((dC X Y m true hm hW).slot hW 6).1 = (X.length, m + 1) := h6
        have hslot : IsSlot Vd' (X.length, m) := by
          have := isSlot_ext X Pd Y Pd' hP hE (s := (X.length, m)) (hb0 ▸ b.2)
            (isExtSlot_cut_left X Pd (p := m) (by omega))
          rwa [shiftL] at this
        have hbit' : bit Vd' X.length m = true := by rw [d_bit_start, E1, hE0]
        have h1' := c'_L2 X Y m hW' (s := ⟨_, hslot⟩) rfl (Or.inl rfl) hbit'
        have h2' := c'_L3 X Y m hW' h1'
        rw [hbit'] at h2'
        simp only [↓reduceIte] at h2'
        refine ⟨2, ⟨_, hslot⟩, by rw [hb0, shiftL], ?_, ?_⟩
        · rw [hc6, shiftL, Function.iterate_succ_apply', Function.iterate_one, h2']
        · intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · rw [Function.iterate_zero, id, block_col_true (s := ⟨_, hslot⟩) (k := X.length) (p := m) rfl (by omega) hbit',
              c'_extCol]; omega
          · rw [Function.iterate_one, block_col_vertex h1', c'_extCol]; omega
  rcases (entry_iff X Pd Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hb'1 : b'.1 = (X.length, p) := by rw [hb'v, hb, shiftL]
    have hbit' : bit Vd' X.length p = true := by rw [d_bit_start, hbit]
    have hcol0 : ¬ ExtCol X Pd (colOf b) := by rw [block_col_true hb hp hbit, d_extCol]; omega
    have hcol0' : ¬ ExtCol X Pd' (colOf b') := by rw [block_col_true hb'1 hp hbit', c'_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := d_A1 X Y m hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := d_A5 X Y m hW h1 hp hb1 hpm
      obtain ⟨h3, hb3⟩ := d_A9 X Y m hW h2 hp hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := c'_L1 X Y m hW' hb'1 hp hbit' hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pd) hcol0
        (passage_step hW (ExtCol X Pd) (by rw [block_col_true h1 hp hb1, d_extCol]; omega)
        (passage_step hW (ExtCol X Pd) (by rw [block_col_true h2 hp hb2, d_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pd') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h3 hp hb3, d_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftR]
    rcases lt_or_ge p (m + 3) with hpm3 | hpm3
    · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
      rcases this with hpe | hpe | hpe
      · -- the cusp arc entered along `(|X|, m)`: `e = true`
        apply curlC
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvCd4 X.length m (bit Vd (X.length + 2) (m + 1)) 0
        rw [hpe, E1] at hbit
        rw [hbit]; rfl
      · -- entered along `(|X|, m+1)`: `e = false`
        apply curlC
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvCd4 X.length m (bit Vd (X.length + 2) (m + 1)) 0
        rw [hpe, E2] at hbit
        have he : bit Vd (X.length + 2) (m + 1) = false := by simpa using hbit
        rw [he]; rfl
      · -- the through-strand, rightward
        apply curlT
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvTd4 X.length m (bit Vd X.length (m + 2)) 0
        rw [hpe] at hbit
        rw [hbit]; rfl
    · obtain ⟨h1, hb1⟩ := d_A4 X Y m hW hb hp hbit hpm3
      obtain ⟨h2, hb2⟩ := d_A8 X Y m hW h1 hp hb1 (by omega)
      obtain ⟨h3, hb3⟩ := d_A11 X Y m hW h2 hp hb2 hpm3
      obtain ⟨h1', hb1'⟩ := c'_L4 X Y m hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pd) hcol0
        (passage_step hW (ExtCol X Pd) (by rw [block_col_true h1 hp hb1, d_extCol]; omega)
        (passage_step hW (ExtCol X Pd) (by rw [block_col_true h2 hp hb2, d_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pd') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h3 (by omega) hb3, d_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftR]
  · -- from the right at `(|X|+3, q)`
    replace hb : b.1 = (X.length + 3, p) := hb
    replace hbit : bit Vd (X.length + 3) p = false := hbit
    have hb'1 : b'.1 = (X.length + 1, p) := by rw [hb'v, hb, shiftR]
    have hbit' : bit Vd' (X.length + 1) p = false := by rw [d_bit_end X Y m hm hW, hbit]
    have hcol0 : ¬ ExtCol X Pd (colOf b) := by rw [block_col_false hb hp hbit, d_extCol]; omega
    have hcol0' : ¬ ExtCol X Pd' (colOf b') := by rw [block_col_false hb'1 hp hbit', c'_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := d_A21 X Y m hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := d_A17 X Y m hW h1 hp hb1 hpm
      obtain ⟨h3, hb3⟩ := d_A13 X Y m hW h2 hp hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := c'_L5 X Y m hW' hb'1 hp hbit' hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pd) hcol0
        (passage_step hW (ExtCol X Pd) (by rw [block_col_false h1 hp hb1, d_extCol]; omega)
        (passage_step hW (ExtCol X Pd) (by rw [block_col_false h2 hp hb2, d_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pd') hcol0' (passage_end hW')
      have hk3 := (cutSlot_facts hW h3 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 hp hb3, d_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftL]
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
    · -- `p = m`: the through-strand, leftward
      subst hpe
      apply curlT
      apply Subtype.ext
      rw [hb]
      show _ = tvTd4 X.length m (bit Vd X.length (m + 2)) 0
      rw [← E8, hbit]; rfl
    · obtain ⟨h1, hb1⟩ := d_A22 X Y m hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := d_A20 X Y m hW h1 (by omega) hb1 (by omega)
      obtain ⟨h3, hb3⟩ := d_A16 X Y m hW h2 (by omega) hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := c'_L6 X Y m hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pd) hcol0
        (passage_step hW (ExtCol X Pd) (by rw [block_col_false h1 (by omega) hb1, d_extCol]; omega)
        (passage_step hW (ExtCol X Pd) (by rw [block_col_false h2 (by omega) hb2, d_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pd') hcol0' (passage_end hW')
      have hk3 := (cutSlot_facts hW h3 (by omega)).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 (by omega) hb3, d_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftL]

end TypeIIdPassage

/-! #### I3. The type-II variant (d): the moved diagram (the cusp arc is lifted above the through-strand) -/

/-- the realization's positions of the through-strand's vertices (variant (d), unmoved) -/
def pvA4 (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h - 2)
  | 1 => (((k + 1 : ℕ) : ℝ), h - 1)
  | 2 => (((k + 2 : ℕ) : ℝ), h)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the realization's positions of the cusp arc's seven vertices (variant (d)) -/
def pvB4 (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h)
  | 2 => (((k + 2 : ℕ) : ℝ), h - 1)
  | 3 => (((k + 2 : ℕ) : ℝ) + 1 / 2, h - 3 / 2)
  | 4 => (((k + 2 : ℕ) : ℝ), h - 2)
  | 5 => (((k + 1 : ℕ) : ℝ), h - 2)
  | _ => ((k : ℝ), h - 1)

/-- the moved positions of the cusp arc's vertices (variant (d)): the arc is lifted above the through-strand -/
def mvB4 (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h)
  | 2 => (((k + 2 : ℕ) : ℝ), h + 5 / 8)
  | 3 => (((k + 2 : ℕ) : ℝ) + 1 / 2, h + 3 / 8)
  | 4 => (((k + 2 : ℕ) : ℝ), h + 1 / 8)
  | 5 => (((k + 1 : ℕ) : ℝ), h - 3 / 8)
  | _ => ((k : ℝ), h - 1)

/-- the four moved slots of the type-II variant (d) -/
def IsMovedD (k m : ℕ) (s : ℕ × ℕ) : Prop :=
  s = (k + 2, m + 1) ∨ s = (k + 2, 0) ∨ s = (k + 2, m + 2) ∨ s = (k + 1, m + 2)

/-- the moved vertex function of the type-II variant (d) -/
def mvIId (W : Word) (k m : ℕ) (h : ℝ) (u : Slot W) : Plane :=
  if u.1 = (k + 2, m + 1) then mvB4 k h 2
  else if u.1 = (k + 2, 0) then mvB4 k h 3
  else if u.1 = (k + 2, m + 2) then mvB4 k h 4
  else if u.1 = (k + 1, m + 2) then mvB4 k h 5
  else pt .std W u.1

section MvIId

variable (W : Word) (k m : ℕ) (h : ℝ)

theorem mvIId_of_not_moved {u : Slot W} (hu : ¬ IsMovedD k m u.1) : mvIId W k m h u = pt .std W u.1 := by
  unfold IsMovedD at hu
  simp only [not_or] at hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  simp [mvIId, h1, h2, h3, h4]

theorem mvIId_v2 {u : Slot W} (hu : u.1 = (k + 2, m + 1)) : mvIId W k m h u = mvB4 k h 2 := by simp [mvIId, hu]
theorem mvIId_v3 {u : Slot W} (hu : u.1 = (k + 2, 0)) : mvIId W k m h u = mvB4 k h 3 := by simp [mvIId, hu]
theorem mvIId_v4 {u : Slot W} (hu : u.1 = (k + 2, m + 2)) : mvIId W k m h u = mvB4 k h 4 := by simp [mvIId, hu]
theorem mvIId_v5 {u : Slot W} (hu : u.1 = (k + 1, m + 2)) : mvIId W k m h u = mvB4 k h 5 := by simp [mvIId, hu]

theorem mvIId_of_ext {u : Slot W} (hu : ExtSl k (k + 3) u.1) : mvIId W k m h u = pt .std W u.1 := by
  apply mvIId_of_not_moved
  obtain ⟨j, p, hu'⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu'] at hu ⊢
  unfold ExtSl at hu
  unfold IsMovedD
  simp only [Prod.mk.injEq]
  split_ifs at hu with h0 <;> omega

theorem mvIId_xcoord (u : Slot W) : (mvIId W k m h u).1 = (pt .std W u.1).1 := by
  by_cases hmv : IsMovedD k m u.1
  · unfold IsMovedD at hmv
    rcases hmv with e | e | e | e
    · rw [mvIId_v2 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvIId_v3 W k m h e, e, std_pt_cusp]; rfl
    · rw [mvIId_v4 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvIId_v5 W k m h e, e, std_pt_cut _ (by omega)]; rfl
  · rw [mvIId_of_not_moved W k m h hmv]

theorem mvIId_injective (n : ℕ) : Function.Injective (mvIId W k m (-(n : ℝ))) := by
  have ng : ∀ i, 2 ≤ i → i ≤ 5 → ∀ s, mvB4 k (-(n : ℝ)) i ≠ pt .std W s := by
    intro i hi1 hi2 s
    interval_cases i
    · have := nonGrid_eighth (n + 1) 5 (by decide)
      have e : -(n : ℝ) + 5 / 8 = -((n + 1 : ℕ) : ℝ) + 1 + ((5 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ), -(n : ℝ) + 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth (n + 1) 3 (by decide)
      have e : -(n : ℝ) + 3 / 8 = -((n + 1 : ℕ) : ℝ) + 1 + ((3 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ) + 1 / 2, -(n : ℝ) + 3 / 8) ≠ _
      rw [e]; exact this.ne_pt_half W (k + 2) s
    · have := nonGrid_eighth (n + 1) 1 (by decide)
      have e : -(n : ℝ) + 1 / 8 = -((n + 1 : ℕ) : ℝ) + 1 + ((1 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ), -(n : ℝ) + 1 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth (n + 1) (-3) (by decide)
      have e : -(n : ℝ) - 3 / 8 = -((n + 1 : ℕ) : ℝ) + 1 + ((-3 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 1 : ℕ) : ℝ), -(n : ℝ) - 3 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
  have hval : ∀ u : Slot W, IsMovedD k m u.1 → ∃ i, 2 ≤ i ∧ i ≤ 5 ∧ mvIId W k m (-(n : ℝ)) u = mvB4 k (-(n : ℝ)) i ∧
      (i = 2 → u.1 = (k + 2, m + 1)) ∧ (i = 3 → u.1 = (k + 2, 0)) ∧ (i = 4 → u.1 = (k + 2, m + 2)) ∧
      (i = 5 → u.1 = (k + 1, m + 2)) := by
    intro u hu
    unfold IsMovedD at hu
    rcases hu with e | e | e | e
    · exact ⟨2, le_rfl, by norm_num, mvIId_v2 W k m _ e, fun _ => e, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, mvIId_v3 W k m _ e, fun h => absurd h (by norm_num), fun _ => e,
        fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · exact ⟨4, by norm_num, by norm_num, mvIId_v4 W k m _ e, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num), fun _ => e, fun h => absurd h (by norm_num)⟩
    · exact ⟨5, by norm_num, le_rfl, mvIId_v5 W k m _ e, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ => e⟩
  have hdist : ∀ i j, 2 ≤ i → i ≤ 5 → 2 ≤ j → j ≤ 5 → mvB4 k (-(n : ℝ)) i = mvB4 k (-(n : ℝ)) j → i = j := by
    intro i j hi1 hi2 hj1 hj2 he
    interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; have := congrArg Prod.snd he; simp only [mvB4] at this; linarith)
  intro u v huv
  by_cases hu : IsMovedD k m u.1
  · obtain ⟨i, hi1, hi2, hui, hu2, hu3, hu4, hu5⟩ := hval u hu
    by_cases hv : IsMovedD k m v.1
    · obtain ⟨j, hj1, hj2, hvj, hv2, hv3, hv4, hv5⟩ := hval v hv
      have := hdist i j hi1 hi2 hj1 hj2 (hui.symm.trans (huv.trans hvj))
      subst this
      apply Subtype.ext
      interval_cases i
      · rw [hu2 rfl, hv2 rfl]
      · rw [hu3 rfl, hv3 rfl]
      · rw [hu4 rfl, hv4 rfl]
      · rw [hu5 rfl, hv5 rfl]
    · rw [hui, mvIId_of_not_moved W k m _ hv] at huv
      exact absurd huv (ng i hi1 hi2 _)
  · by_cases hv : IsMovedD k m v.1
    · obtain ⟨j, hj1, hj2, hvj, -⟩ := hval v hv
      rw [hvj, mvIId_of_not_moved W k m _ hu] at huv
      exact absurd huv.symm (ng j hj1 hj2 _)
    · rw [mvIId_of_not_moved W k m _ hu, mvIId_of_not_moved W k m _ hv] at huv
      exact pt_inj _ _ huv

end MvIId

section IIdVertices

variable (k : ℕ) (h : ℝ)

theorem pvA4_int : ∀ i, 1 ≤ i → i ≤ 2 → pvA4 k h i ∈ interior (polygon (tIIR k h)) := by
  intro i h1 h2
  interval_cases i
  · have := tIIR_int_cut1 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIR_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem pvA4_mem : ∀ i, i ≤ 3 → pvA4 k h i ∈ polygon (tIIR k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIR_mem_left k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · exact interior_subset (pvA4_int k h i h0 (by omega))
  · have : i = 3 := by omega
    subst this
    have := tIIR_mem_right k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem pvB4_int : ∀ i, 1 ≤ i → i ≤ 5 → pvB4 k h i ∈ interior (polygon (tIIR k h)) := by
  intro i h1 h5
  interval_cases i
  · have := tIIR_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tIIR_int_cut2 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIR_int_cuspR k h (-(3 / 2)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIR_int_cut2 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIR_int_cut1 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem pvB4_mem : ∀ i, i ≤ 6 → pvB4 k h i ∈ polygon (tIIR k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIR_mem_left k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  rcases Nat.lt_or_ge i 6 with h6 | h6
  · exact interior_subset (pvB4_int k h i h0 (by omega))
  · have : i = 6 := by omega
    subst this
    have := tIIR_mem_left k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem mvB4_int : ∀ i, 1 ≤ i → i ≤ 5 → mvB4 k h i ∈ interior (polygon (tIIR k h)) := by
  intro i h1 h5
  interval_cases i
  · have := tIIR_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · exact tIIR_int_cut2 k h (5 / 8) (by norm_num) (by norm_num)
  · exact tIIR_int_cuspR k h (3 / 8) (by norm_num) (by norm_num)
  · exact tIIR_int_cut2 k h (1 / 8) (by norm_num) (by norm_num)
  · have := tIIR_int_cut1 k h (-(3 / 8)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem mvB4_mem : ∀ i, i ≤ 6 → mvB4 k h i ∈ polygon (tIIR k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIR_mem_left k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  rcases Nat.lt_or_ge i 6 with h6 | h6
  · exact interior_subset (mvB4_int k h i h0 (by omega))
  · have : i = 6 := by omega
    subst this
    have := tIIR_mem_left k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

/-! the geometric facts of the same-column pairs of the moved variant (d) -/

macro "dII_pair" : tactic => `(tactic| (
  intro τ τ' h0 h1 h0' h1' he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [pvA4, mvB4, segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy))

theorem dII_NM_T0C0 : NoMeet (pvA4 k h 0) (pvA4 k h 1) (mvB4 k h 0) (mvB4 k h 1) := by dII_pair; linarith
theorem dII_NM_T0C5 : NoMeet (pvA4 k h 0) (pvA4 k h 1) (mvB4 k h 5) (mvB4 k h 6) := by dII_pair; linarith
theorem dII_NM_T1C1 : NoMeet (pvA4 k h 1) (pvA4 k h 2) (mvB4 k h 1) (mvB4 k h 2) := by dII_pair; linarith
theorem dII_NM_T1C4 : NoMeet (pvA4 k h 1) (pvA4 k h 2) (mvB4 k h 4) (mvB4 k h 5) := by dII_pair; linarith
theorem dII_NM_T2C2 : NoMeet (pvA4 k h 2) (pvA4 k h 3) (mvB4 k h 2) (mvB4 k h 3) := by dII_pair; linarith
theorem dII_NM_T2C3 : NoMeet (pvA4 k h 2) (pvA4 k h 3) (mvB4 k h 3) (mvB4 k h 4) := by dII_pair; linarith
theorem dII_NM_C0C5 : NoMeet (mvB4 k h 0) (mvB4 k h 1) (mvB4 k h 5) (mvB4 k h 6) := by dII_pair; linarith
theorem dII_NM_C1C4 : NoMeet (mvB4 k h 1) (mvB4 k h 2) (mvB4 k h 4) (mvB4 k h 5) := by dII_pair; linarith
theorem dII_OJ234 : OnlyAtJoint (mvB4 k h 2) (mvB4 k h 3) (mvB4 k h 4) := by
  dII_pair; constructor <;> linarith

end IIdVertices

/-! #### I4. The type-II variant (d): the specification -/

section TypeIIdSpec

open U3

variable (X Y : Word) (m : ℕ) (t e : Bool) (hm : 1 ≤ m)
  (hW : (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y) X.length (m + 2) = t)
  (he : bit (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y) (X.length + 2) (m + 1) = e)

local notation "Vd" => X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y
local notation "Pd" => [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)]
local notation "Vd'" => X ++ [Letter.r m] ++ Y
local notation "Pd'" => [Letter.r m]
local notation "hB" => (-(m : ℝ))

/-- the moved vertex function of the type-II variant (d) -/
def dMv : Slot Vd → Plane := mvIId Vd X.length m hB

theorem dMv_apply (u : Slot Vd) : dMv X Y m u = mvIId Vd X.length m hB u := rfl

include hm

theorem d_pt_T : ∀ i, i ≤ 3 → pt .std Vd (tvT4 X.length m i) = pvA4 X.length hB i := by
  intro i hi
  interval_cases i
  · show pt .std Vd (X.length, m + 2) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA4]; push_cast; ring)
  · show pt .std Vd (X.length + 1, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA4]; push_cast; ring)
  · show pt .std Vd (X.length + 2, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA4])
  · show pt .std Vd (X.length + 3, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA4])

theorem d_pt_C : ∀ i, i ≤ 6 → pt .std Vd (tvC4 X.length m i) = pvB4 X.length hB i := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
  intro i hi
  interval_cases i
  · show pt .std Vd (X.length, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB4])
  · show pt .std Vd (X.length + 1, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB4])
  · show pt .std Vd (X.length + 2, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB4]; push_cast; ring)
  · show pt .std Vd (X.length + 2, 0) = _
    rw [std_pt_cusp, hℓ₂]; exact Prod.ext rfl (by simp only [pvB4, idx]; push_cast; ring)
  · show pt .std Vd (X.length + 2, m + 2) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB4]; push_cast; ring)
  · show pt .std Vd (X.length + 1, m + 2) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB4]; push_cast; ring)
  · show pt .std Vd (X.length, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB4]; push_cast; ring)

theorem d_mv_T : ∀ i, i ≤ 3 → ∀ u : Slot Vd, u.1 = tvT4 X.length m i → dMv X Y m u = pvA4 X.length hB i := by
  intro i hi u hu
  have hnm : ¬ IsMovedD X.length m u.1 := by
    rw [hu]; interval_cases i <;> simp only [IsMovedD, tvT4, Prod.mk.injEq] <;> omega
  rw [dMv_apply, mvIId_of_not_moved _ _ _ _ hnm, hu]
  exact d_pt_T X Y m hm i hi

theorem d_mv_C : ∀ i, i ≤ 6 → ∀ u : Slot Vd, u.1 = tvC4 X.length m i → dMv X Y m u = mvB4 X.length hB i := by
  intro i hi u hu
  rw [dMv_apply]
  interval_cases i
  · rw [mvIId_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedD, tvC4, Prod.mk.injEq]; omega), hu,
      d_pt_C X Y m hm 0 (by norm_num)]; rfl
  · rw [mvIId_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedD, tvC4, Prod.mk.injEq]; omega), hu,
      d_pt_C X Y m hm 1 (by norm_num)]; rfl
  · exact mvIId_v2 _ _ _ _ hu
  · exact mvIId_v3 _ _ _ _ hu
  · exact mvIId_v4 _ _ _ _ hu
  · exact mvIId_v5 _ _ _ _ hu
  · rw [mvIId_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedD, tvC4, Prod.mk.injEq]; omega), hu,
      d_pt_C X Y m hm 6 (by norm_num)]; rfl

omit hm in
theorem tvT4_inj : ∀ i j, i ≤ 3 → j ≤ 3 → tvT4 X.length m i = tvT4 X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tvT4, Prod.mk.injEq] at he; omega)

omit hm in
theorem tvC4_inj : ∀ i j, i ≤ 6 → j ≤ 6 → tvC4 X.length m i = tvC4 X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tvC4, Prod.mk.injEq] at he; omega)

theorem tvT4_ne_tvC4 : ∀ i j, i ≤ 3 → j ≤ 6 → tvT4 X.length m i ≠ tvC4 X.length m j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> simp only [tvT4, tvC4, Prod.mk.injEq] at he <;> omega

include hW ht he

theorem dT_mv_slot : ∀ j, j ≤ 3 → dMv X Y m ((dT X Y m t hm hW).slot hW j) =
    if t then pvA4 X.length hB j else pvA4 X.length hB (3 - j) := by
  intro j hj
  have hs := dT_slot_val X Y m t e hm hW ht he j hj
  cases t
  · simp only [tvTd4, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact d_mv_T X Y m hm (3 - j) (by omega) _ hs
  · simp only [tvTd4, ↓reduceIte] at hs ⊢
    exact d_mv_T X Y m hm j hj _ hs

theorem dT_pt_slot : ∀ j, j ≤ 3 → pt .std Vd ((dT X Y m t hm hW).slot hW j).1 =
    if t then pvA4 X.length hB j else pvA4 X.length hB (3 - j) := by
  intro j hj
  have hs := dT_slot_val X Y m t e hm hW ht he j hj
  cases t
  · simp only [tvTd4, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact d_pt_T X Y m hm (3 - j) (by omega)
  · simp only [tvTd4, ↓reduceIte] at hs ⊢
    rw [hs]; exact d_pt_T X Y m hm j hj

theorem dC_mv_slot : ∀ j, j ≤ 6 → dMv X Y m ((dC X Y m e hm hW).slot hW j) =
    if e then mvB4 X.length hB j else mvB4 X.length hB (6 - j) := by
  intro j hj
  have hs := dC_slot_val X Y m t e hm hW ht he j hj
  cases e
  · simp only [tvCd4, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact d_mv_C X Y m hm (6 - j) (by omega) _ hs
  · simp only [tvCd4, ↓reduceIte] at hs ⊢
    exact d_mv_C X Y m hm j hj _ hs

theorem dC_pt_slot : ∀ j, j ≤ 6 → pt .std Vd ((dC X Y m e hm hW).slot hW j).1 =
    if e then pvB4 X.length hB j else pvB4 X.length hB (6 - j) := by
  intro j hj
  have hs := dC_slot_val X Y m t e hm hW ht he j hj
  cases e
  · simp only [tvCd4, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact d_pt_C X Y m hm (6 - j) (by omega)
  · simp only [tvCd4, ↓reduceIte] at hs ⊢
    rw [hs]; exact d_pt_C X Y m hm j hj

omit ht he in
theorem dT_next_slot : ∀ j, j < 3 → next hW ((dT X Y m t hm hW).slot hW j) = (dT X Y m t hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

omit ht he in
theorem dC_next_slot : ∀ j, j < 6 → next hW ((dC X Y m e hm hW).slot hW j) = (dC X Y m e hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

theorem dT_chain_in : ∀ j, j < 3 → PieceIn (tIIR X.length hB) hW (dMv X Y m) ((dT X Y m t hm hW).slot hW j) ∧
    PieceIn (tIIR X.length hB) hW (ptv .std) ((dT X Y m t hm hW).slot hW j) := by
  intro j hj
  have e' := dT_next_slot X Y m t hm hW j hj
  have key : SegIn (tIIR X.length hB) (if t then pvA4 X.length hB j else pvA4 X.length hB (3 - j))
      (if t then pvA4 X.length hB (j + 1) else pvA4 X.length hB (3 - (j + 1))) := by
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (pvA4_mem _ _ _ (by omega)) (pvA4_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pvA4_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pvA4_int _ _ _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (pvA4_mem _ _ _ (by omega)) (pvA4_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pvA4_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pvA4_int _ _ _ (by omega) (by omega))
  constructor
  · show SegIn _ (dMv X Y m _) (dMv X Y m (next hW _))
    rw [e', dT_mv_slot X Y m t e hm hW ht he j (by omega), dT_mv_slot X Y m t e hm hW ht he (j + 1) (by omega)]
    exact key
  · show SegIn _ (pt .std Vd _) (pt .std Vd (next hW _).1)
    rw [e', dT_pt_slot X Y m t e hm hW ht he j (by omega), dT_pt_slot X Y m t e hm hW ht he (j + 1) (by omega)]
    exact key

theorem dC_chain_in : ∀ j, j < 6 → PieceIn (tIIR X.length hB) hW (dMv X Y m) ((dC X Y m e hm hW).slot hW j) ∧
    PieceIn (tIIR X.length hB) hW (ptv .std) ((dC X Y m e hm hW).slot hW j) := by
  intro j hj
  have e' := dC_next_slot X Y m e hm hW j hj
  have key : ∀ (f : ℕ → Plane), (∀ i, i ≤ 6 → f i ∈ polygon (tIIR X.length hB)) →
      (∀ i, 1 ≤ i → i ≤ 5 → f i ∈ interior (polygon (tIIR X.length hB))) →
      SegIn (tIIR X.length hB) (if e then f j else f (6 - j)) (if e then f (j + 1) else f (6 - (j + 1))) := by
    intro f hmem hint
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (hmem _ (by omega)) (hmem _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (hint _ (by norm_num) (by norm_num))
      · exact Or.inl (hint _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (hmem _ (by omega)) (hmem _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (hint _ (by norm_num) (by norm_num))
      · exact Or.inl (hint _ (by omega) (by omega))
  constructor
  · show SegIn _ (dMv X Y m _) (dMv X Y m (next hW _))
    rw [e', dC_mv_slot X Y m t e hm hW ht he j (by omega), dC_mv_slot X Y m t e hm hW ht he (j + 1) (by omega)]
    exact key _ (mvB4_mem _ _) (mvB4_int _ _)
  · show SegIn _ (pt .std Vd _) (pt .std Vd (next hW _).1)
    rw [e', dC_pt_slot X Y m t e hm hW ht he j (by omega), dC_pt_slot X Y m t e hm hW ht he (j + 1) (by omega)]
    exact key _ (pvB4_mem _ _) (pvB4_int _ _)

theorem dT_vert : ∀ j, 0 < j → j < 3 → dMv X Y m ((dT X Y m t hm hW).slot hW j) ∈ interior (polygon (tIIR X.length hB)) ∧
    pt .std Vd ((dT X Y m t hm hW).slot hW j).1 ∈ interior (polygon (tIIR X.length hB)) := by
  intro j h0 hj
  rw [dT_mv_slot X Y m t e hm hW ht he j (by omega), dT_pt_slot X Y m t e hm hW ht he j (by omega)]
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨pvA4_int _ _ _ (by omega) (by omega), pvA4_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨pvA4_int _ _ _ (by omega) (by omega), pvA4_int _ _ _ (by omega) (by omega)⟩

theorem dC_vert : ∀ j, 0 < j → j < 6 → dMv X Y m ((dC X Y m e hm hW).slot hW j) ∈ interior (polygon (tIIR X.length hB)) ∧
    pt .std Vd ((dC X Y m e hm hW).slot hW j).1 ∈ interior (polygon (tIIR X.length hB)) := by
  intro j h0 hj
  rw [dC_mv_slot X Y m t e hm hW ht he j (by omega), dC_pt_slot X Y m t e hm hW ht he j (by omega)]
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨mvB4_int _ _ _ (by omega) (by omega), pvB4_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨mvB4_int _ _ _ (by omega) (by omega), pvB4_int _ _ _ (by omega) (by omega)⟩

omit hW ht he in
theorem d_moved : ∀ u : Slot Vd, dMv X Y m u = pt .std Vd u.1 ∨
    (dMv X Y m u ∈ interior (polygon (tIIR X.length hB)) ∧ pt .std Vd u.1 ∈ interior (polygon (tIIR X.length hB))) := by
  intro u
  by_cases hmv : IsMovedD X.length m u.1
  · right
    have : ∃ i, 2 ≤ i ∧ i ≤ 5 ∧ u.1 = tvC4 X.length m i := by
      unfold IsMovedD at hmv
      rcases hmv with e' | e' | e' | e'
      · exact ⟨2, by norm_num, by norm_num, e'⟩
      · exact ⟨3, by norm_num, by norm_num, e'⟩
      · exact ⟨4, by norm_num, by norm_num, e'⟩
      · exact ⟨5, by norm_num, by norm_num, e'⟩
    obtain ⟨i, hi1, hi2, hu⟩ := this
    rw [d_mv_C X Y m hm i (by omega) u hu, hu, d_pt_C X Y m hm i (by omega)]
    exact ⟨mvB4_int _ _ _ (by omega) (by omega), pvB4_int _ _ _ (by omega) (by omega)⟩
  · left
    rw [dMv_apply, mvIId_of_not_moved _ _ _ _ hmv]

/-- the chain slot carrying the through-vertex `tvT4 i` -/
theorem dT_chain_of (i : ℕ) (hi : i ≤ 3) {u : Slot Vd} (hu : u.1 = tvT4 X.length m i)
    (hd : (t = true ∧ i < 3) ∨ (t = false ∧ 0 < i)) : OnChain hW (dT X Y m t hm hW) u := by
  cases t
  · refine ⟨3 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · show 3 - i < 3; omega
    · rw [dT_slot_val X Y m false e hm hW ht he (3 - i) (by omega), hu]
      simp only [tvTd4, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [dT_slot_val X Y m true e hm hW ht he i hi, hu]
      simp only [tvTd4, ↓reduceIte]

/-- the chain slot carrying the cusp-arc vertex `tvC4 i` -/
theorem dC_chain_of (i : ℕ) (hi : i ≤ 6) {u : Slot Vd} (hu : u.1 = tvC4 X.length m i)
    (hd : (e = true ∧ i < 6) ∨ (e = false ∧ 0 < i)) : OnChain hW (dC X Y m e hm hW) u := by
  cases e
  · refine ⟨6 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · show 6 - i < 6; omega
    · rw [dC_slot_val X Y m t false hm hW ht he (6 - i) (by omega), hu]
      simp only [tvCd4, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [dC_slot_val X Y m t true hm hW ht he i hi, hu]
      simp only [tvCd4, ↓reduceIte]

omit hm ht he in
/-- an unchanged spectator piece with an explicit outside witness -/
theorem d_spec {u : Slot Vd} {j p j' p' : ℕ} (hu : u.1 = (j, p)) (hn : (next hW u).1 = (j', p'))
    (hp : p ≠ 0) (hp' : p' ≠ 0) (h1 : ¬ IsMovedD X.length m (j, p)) (h2 : ¬ IsMovedD X.length m (j', p'))
    (hout : SegOut (tIIR X.length hB) ((j : ℝ), -(p : ℝ)) ((j' : ℝ), -(p' : ℝ))) :
    Unch .std hW (dMv X Y m) u ∧ PieceOut (tIIR X.length hB) hW (ptv .std) u := by
  constructor
  · constructor
    · rw [dMv_apply, mvIId_of_not_moved _ _ _ _ (hu ▸ h1)]
    · rw [dMv_apply, mvIId_of_not_moved _ _ _ _ (hn ▸ h2)]
  · show SegOut _ (pt .std Vd u.1) (pt .std Vd (next hW u).1)
    rw [hu, hn, std_pt_cut _ hp, std_pt_cut _ hp']
    exact hout

omit hm hW ht he in
theorem d_hmv : ∀ v : Slot Vd, ExtSl X.length (X.length + 3) v.1 → dMv X Y m v = pt .std Vd v.1 :=
  fun v hv => by rw [dMv_apply]; exact mvIId_of_ext _ _ _ _ hv

/-- THE CLASSIFICATION of the type-II variant (d). -/
theorem d_rest : ∀ u : Slot Vd, OnChain hW (dT X Y m t hm hW) u ∨ OnChain hW (dC X Y m e hm hW) u ∨
    (Unch .std hW (dMv X Y m) u ∧ PieceOut (tIIR X.length hB) hW (ptv .std) u) := by
  intro u
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  have above : ∀ {q : ℕ}, q < m → hB + 1 ≤ -(q : ℝ) := fun {q} hq => by
    have : (q : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : q + 1 ≤ m)
    linarith
  have below : ∀ {q : ℕ}, m + 3 ≤ q → -(q : ℝ) ≤ hB - 3 := fun {q} hq => by
    have : (m : ℝ) + 3 ≤ q := by exact_mod_cast hq
    linarith
  have slant : ∀ {q : ℕ}, m + 1 ≤ q → -(q : ℝ) ≤ hB - 1 := fun {q} hq => by
    have : (m : ℝ) + 1 ≤ q := by exact_mod_cast hq
    linarith
  have chainT := dT_chain_of X Y m t e hm hW ht he
  have chainC := dC_chain_of X Y m t e hm hW ht he
  have nm : ∀ a b : ℕ, b ≠ 0 → (a ≠ X.length + 2 ∨ b ≠ m + 1) → (a ≠ X.length + 2 ∨ b ≠ m + 2) →
      (a ≠ X.length + 1 ∨ b ≠ m + 2) → ¬ IsMovedD X.length m (a, b) := by
    intro a b h0 h1 h2 h3 h
    unfold IsMovedD at h
    simp only [Prod.mk.injEq] at h
    omega
  by_cases hext : ExtCol X Pd (colOf u)
  · right; right
    have hext' := (d_extCol X m _).1 hext
    exact ⟨unch_of_extCol .std hW _ (d_hmv X Y m) hext',
      pieceOut_of_extCol _ .std hW _ (tIIR_xge_mem _ _) (tIIR_xle_mem _ _) (unch_pt _ _ _) hext'⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, d_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₀] at this
      simp [isCrossing] at this
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₁] at this
      simp [isCrossing] at this
    · exact Or.inr (Or.inl (chainC 3 (by norm_num) hu
        (by cases e; exact Or.inr ⟨rfl, by norm_num⟩; exact Or.inl ⟨rfl, by norm_num⟩)))
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vd j p
  · -- leftward pieces
    rw [block_col_false hu hp hb, d_extCol] at hext
    have : j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    rcases this with rfl | rfl | rfl
    · -- cut `|X|+1`, column `|X|`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := d_A13 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hee : e = false := by rw [hpe, E3] at hb; exact hb
          exact Or.inr (Or.inl (chainC 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
        · have htt : t = false := by rw [hpe, E4] at hb; exact hb
          exact Or.inl (chainT 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
        · have hee : e = true := by rw [hpe, E5] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := d_A16 X Y m hW hu hp hb hpm3
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_below _ _ (below hpm3) _ _)))
    · -- cut `|X|+2`, column `|X|+1`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := d_A17 X Y m hW hu hp hb hpm
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have htt : t = false := by rw [hpe, E6] at hb; exact hb
          exact Or.inl (chainT 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
        · have hee : e = false := by rw [hpe, he] at hb; exact hb
          exact Or.inr (Or.inl (chainC 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
        · have hee : e = true := by rw [hpe, E7] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := d_A20 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_below _ _ (below hpm3) _ _)))
    · -- cut `|X|+3`, column `|X|+2`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := d_A21 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
      · have htt : t = false := by rw [← hpe] at hb; rw [← E8]; exact hb
        exact Or.inl (chainT 3 (by norm_num) (by rw [hu, ← hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := d_A22 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp (by omega) (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ (by omega) (by omega) (by omega) (by omega)) (tIIR_out_slant' _ _ (slant (by omega)))))
  · -- rightward pieces
    rw [block_col_true hu hp hb, d_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · -- cut `|X|`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := d_A1 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hee : e = true := by rw [hpe, E1] at hb; exact hb
          exact Or.inr (Or.inl (chainC 0 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
        · have hee : e = false := by rw [hpe, E2] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 6 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
        · have htt : t = true := by rw [hpe] at hb; rw [← ht]; exact hb
          exact Or.inl (chainT 0 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := d_A4 X Y m hW hu hp hb hpm3
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_below _ _ (below hpm3) _ _)))
    · -- cut `|X|+1`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := d_A5 X Y m hW hu hp hb hpm
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hee : e = true := by rw [hpe, E3] at hb; exact hb
          exact Or.inr (Or.inl (chainC 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
        · have htt : t = true := by rw [hpe, E4] at hb; exact hb
          exact Or.inl (chainT 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
        · have hee : e = false := by rw [hpe, E5] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := d_A8 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_below _ _ (below hpm3) _ _)))
    · -- cut `|X|+2`
      rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := d_A9 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp hp (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ hp (by omega) (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have htt : t = true := by rw [hpe, E6] at hb; exact hb
          exact Or.inl (chainT 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
        · have hee : e = true := by rw [hpe] at hb; rw [← he]; exact hb
          exact Or.inr (Or.inl (chainC 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
        · have hee : e = false := by rw [hpe, E7] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := d_A11 X Y m hW hu hp hb hpm3
        exact Or.inr (Or.inr (d_spec X Y m hW hu h1 hp (by omega) (nm _ _ hp (by omega) (by omega) (by omega))
          (nm _ _ (by omega) (by omega) (by omega) (by omega))
          (tIIR_out_slant _ _ (by omega) (slant (q := p - 2) (by omega)))))

end TypeIIdSpec

/-! #### I5. The type-II variant (d): the remaining specification fields -/

section TypeIIdSpec2

open U3

variable (X Y : Word) (m : ℕ) (t e : Bool) (hm : 1 ≤ m)
  (hW : (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y) X.length (m + 2) = t)
  (he : bit (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y) (X.length + 2) (m + 1) = e)

local notation "Vd" => X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y
local notation "Pd" => [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)]
local notation "Vd'" => X ++ [Letter.r m] ++ Y
local notation "Pd'" => [Letter.r m]
local notation "hB" => (-(m : ℝ))

include hm hW ht he

theorem dT_slot_ne : ∀ j j', j ≤ 3 → j' ≤ 3 → j ≠ j' → (dT X Y m t hm hW).slot hW j ≠ (dT X Y m t hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [dT_slot_val X Y m t e hm hW ht he j hj, dT_slot_val X Y m t e hm hW ht he j' hj'] at h'
  cases t
  · simp only [tvTd4, Bool.false_eq_true, ↓reduceIte] at h'
    have := tvT4_inj X m (3 - j) (3 - j') (by omega) (by omega) h'
    omega
  · simp only [tvTd4, ↓reduceIte] at h'
    exact hne (tvT4_inj X m j j' hj hj' h')

theorem dC_slot_ne : ∀ j j', j ≤ 6 → j' ≤ 6 → j ≠ j' → (dC X Y m e hm hW).slot hW j ≠ (dC X Y m e hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [dC_slot_val X Y m t e hm hW ht he j hj, dC_slot_val X Y m t e hm hW ht he j' hj'] at h'
  cases e
  · simp only [tvCd4, Bool.false_eq_true, ↓reduceIte] at h'
    have := tvC4_inj X m (6 - j) (6 - j') (by omega) (by omega) h'
    omega
  · simp only [tvCd4, ↓reduceIte] at h'
    exact hne (tvC4_inj X m j j' hj hj' h')

theorem d_disj : ∀ j j', j ≤ 3 → j' ≤ 6 → (dT X Y m t hm hW).slot hW j ≠ (dC X Y m e hm hW).slot hW j' := by
  intro j j' hj hj' h
  have h' := congrArg Subtype.val h
  rw [dT_slot_val X Y m t e hm hW ht he j hj, dC_slot_val X Y m t e hm hW ht he j' hj'] at h'
  cases t <;> cases e <;> simp only [tvTd4, tvCd4, Bool.false_eq_true, ↓reduceIte] at h' <;>
    exact tvT4_ne_tvC4 X m hm _ _ (by omega) (by omega) h'

theorem d_prevOut₁ : Unch .std hW (dMv X Y m) (prev hW (dT X Y m t hm hW).u₀) ∧
    PieceOut (tIIR X.length hB) hW (ptv .std) (prev hW (dT X Y m t hm hW).u₀) := by
  rcases d_rest X Y m t e hm hW ht he (prev hW (dT X Y m t hm hW).u₀) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · exfalso
    have hj' : j < 3 := hj
    have : (dT X Y m t hm hW).slot hW (j + 1) = (dT X Y m t hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact dT_slot_ne X Y m t e hm hW ht he (j + 1) 0 (by omega) (by omega) (by omega) this
  · exfalso
    have hj' : j < 6 := hj
    have : (dC X Y m e hm hW).slot hW (j + 1) = (dT X Y m t hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact d_disj X Y m t e hm hW ht he 0 (j + 1) (by omega) (by omega) this.symm
  · exact h

theorem d_stopOut₁ : Unch .std hW (dMv X Y m) ((dT X Y m t hm hW).slot hW 3) ∧
    PieceOut (tIIR X.length hB) hW (ptv .std) ((dT X Y m t hm hW).slot hW 3) := by
  rcases d_rest X Y m t e hm hW ht he ((dT X Y m t hm hW).slot hW 3) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · have hj' : j < 3 := hj
    exact absurd hjs (dT_slot_ne X Y m t e hm hW ht he j 3 (by omega) le_rfl (by omega))
  · have hj' : j < 6 := hj
    exact absurd hjs.symm (d_disj X Y m t e hm hW ht he 3 j le_rfl (by omega))
  · exact h

theorem d_prevOut₂ : Unch .std hW (dMv X Y m) (prev hW (dC X Y m e hm hW).u₀) ∧
    PieceOut (tIIR X.length hB) hW (ptv .std) (prev hW (dC X Y m e hm hW).u₀) := by
  rcases d_rest X Y m t e hm hW ht he (prev hW (dC X Y m e hm hW).u₀) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · exfalso
    have hj' : j < 3 := hj
    have : (dT X Y m t hm hW).slot hW (j + 1) = (dC X Y m e hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact d_disj X Y m t e hm hW ht he (j + 1) 0 (by omega) (by omega) this
  · exfalso
    have hj' : j < 6 := hj
    have : (dC X Y m e hm hW).slot hW (j + 1) = (dC X Y m e hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact dC_slot_ne X Y m t e hm hW ht he (j + 1) 0 (by omega) (by omega) (by omega) this
  · exact h

theorem d_stopOut₂ : Unch .std hW (dMv X Y m) ((dC X Y m e hm hW).slot hW 6) ∧
    PieceOut (tIIR X.length hB) hW (ptv .std) ((dC X Y m e hm hW).slot hW 6) := by
  rcases d_rest X Y m t e hm hW ht he ((dC X Y m e hm hW).slot hW 6) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · have hj' : j < 3 := hj
    exact absurd hjs (d_disj X Y m t e hm hW ht he j 6 (by omega) le_rfl)
  · have hj' : j < 6 := hj
    exact absurd hjs (dC_slot_ne X Y m t e hm hW ht he j 6 (by omega) le_rfl (by omega))
  · exact h

omit hm hW ht he in
/-- a grid point of the disc is a vertex of one of the two arcs -/
theorem d_vertex_of_mem {u : Slot Vd} (hmem : pt .std Vd u.1 ∈ polygon (tIIR X.length hB)) :
    (∃ i, i ≤ 3 ∧ u.1 = tvT4 X.length m i) ∨ (∃ i, i ≤ 6 ∧ u.1 = tvC4 X.length m i) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu] at hmem
  by_cases hp : p = 0
  · subst hp
    rw [std_pt_cusp] at hmem
    obtain ⟨b1, b2, -, -, -⟩ := tIIR_mem_bounds X.length hB hmem
    have e1 : 2 * X.length ≤ 2 * j + 1 := by exact_mod_cast (by linarith : (2 * X.length : ℝ) ≤ 2 * j + 1)
    have e2 : 2 * j + 1 ≤ 2 * X.length + 6 := by exact_mod_cast (by linarith : (2 * j + 1 : ℝ) ≤ 2 * X.length + 6)
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₀] at this
      simp [isCrossing] at this
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₁] at this
      simp [isCrossing] at this
    · exact Or.inr ⟨3, by norm_num, hu⟩
  · rw [std_pt_cut _ hp] at hmem
    obtain ⟨b1, b2, b3, b4, b5⟩ := tIIR_mem_bounds X.length hB hmem
    have e1 : X.length ≤ j := by exact_mod_cast b1
    have e2 : j ≤ X.length + 3 := by exact_mod_cast (by linarith : (j : ℝ) ≤ X.length + 3)
    have e3 : 2 * p ≤ 2 * m + 5 := by exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 2 * m + 5)
    have e4 : 4 * m ≤ 4 * p + 3 := by exact_mod_cast (by linarith : (4 * m : ℝ) ≤ 4 * p + 3)
    have e5 : 4 * p + 8 * j ≤ 4 * m + 8 * X.length + 27 := by
      exact_mod_cast (by linarith : (4 * p + 8 * j : ℝ) ≤ 4 * m + 8 * X.length + 27)
    have hj : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    have hpp : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inr ⟨0, by norm_num, hu⟩
      · exact Or.inr ⟨6, by norm_num, hu⟩
      · exact Or.inl ⟨0, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inr ⟨1, by norm_num, hu⟩
      · exact Or.inl ⟨1, by norm_num, hu⟩
      · exact Or.inr ⟨5, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inl ⟨2, by norm_num, hu⟩
      · exact Or.inr ⟨2, by norm_num, hu⟩
      · exact Or.inr ⟨4, by norm_num, hu⟩
    · have : p = m := by omega
      subst this
      exact Or.inl ⟨3, by norm_num, hu⟩

theorem d_touch : ∀ u : Slot Vd, PieceOut (tIIR X.length hB) hW (ptv .std) u → pt .std Vd u.1 ∈ polygon (tIIR X.length hB) →
    u = (dT X Y m t hm hW).slot hW 3 ∨ u = (dC X Y m e hm hW).slot hW 6 := by
  intro u hout hmem
  have hchainT : ∀ j', j' < 3 → u ≠ (dT X Y m t hm hW).slot hW j' := by
    intro j' hj' he'
    rw [he'] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (dT_chain_in X Y m t e hm hW ht he j' hj').2
  have hchainC : ∀ j', j' < 6 → u ≠ (dC X Y m e hm hW).slot hW j' := by
    intro j' hj' he'
    rw [he'] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (dC_chain_in X Y m t e hm hW ht he j' hj').2
  rcases d_vertex_of_mem X Y m hmem with ⟨i, hi, hu⟩ | ⟨i, hi, hu⟩
  · left
    have hs := dT_slot_val X Y m t e hm hW ht he
    cases t
    · have hu' : u = (dT X Y m false hm hW).slot hW (3 - i) := by
        apply Subtype.ext
        rw [hs (3 - i) (by omega), hu]
        simp only [tvTd4, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact hu'
      · exact absurd hu' (hchainT (3 - i) (by omega))
    · have hu' : u = (dT X Y m true hm hW).slot hW i := by
        apply Subtype.ext
        rw [hs i hi, hu]
        simp only [tvTd4, ↓reduceIte]
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact absurd hu' (hchainT i h3)
      · have : i = 3 := by omega
        subst this
        exact hu'
  · right
    have hs := dC_slot_val X Y m t e hm hW ht he
    cases e
    · have hu' : u = (dC X Y m false hm hW).slot hW (6 - i) := by
        apply Subtype.ext
        rw [hs (6 - i) (by omega), hu]
        simp only [tvCd4, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact hu'
      · exact absurd hu' (hchainC (6 - i) (by omega))
    · have hu' : u = (dC X Y m true hm hW).slot hW i := by
        apply Subtype.ext
        rw [hs i hi, hu]
        simp only [tvCd4, ↓reduceIte]
      rcases Nat.lt_or_ge i 6 with h6 | h6
      · exact absurd hu' (hchainC i h6)
      · have : i = 6 := by omega
        subst this
        exact hu'

omit hm ht he in
theorem d_exits : ∀ u : Slot Vd, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch .std hW (dMv X Y m) v ∧
    PieceOut (tIIR X.length hB) hW (ptv .std) v := by
  intro u
  have hno : ∀ k', X.length ≤ k' → k' < X.length + 3 → ∀ m' d', letterAt Vd k' ≠ .l m' d' := by
    intro k' h1 h2 m' d'
    obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
    have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [hℓ₀]; exact fun h => by cases h
    · rw [hℓ₁]; exact fun h => by cases h
    · rw [hℓ₂]; exact fun h => by cases h
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_l hW X.length (X.length + 3) hno u
  exact ⟨v, hsc, unch_of_extCol .std hW _ (d_hmv X Y m) hcol,
    pieceOut_of_extCol _ .std hW _ (tIIR_xge_mem _ _) (tIIR_xle_mem _ _) (unch_pt _ _ _) hcol⟩

omit hm hW ht he in
/-- the crossing letters of the block: `σ_{m+1}` at column `|X|`, `σ_m` at column `|X|+1` -/
theorem d_σcol {k' m' : ℕ} (hℓ : letterAt Vd k' = .σ m') (hext : ¬ ExtCol X Pd k') :
    (k' = X.length ∧ m + 1 = m') ∨ (k' = X.length + 1 ∧ m = m') := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
  rw [d_extCol] at hext
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀] at hℓ; exact Or.inl ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [hℓ₁] at hℓ; exact Or.inr ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [hℓ₂] at hℓ; cases hℓ

/-- the over strand of each block crossing lies on the cusp arc -/
theorem d_σA_chain {k' m' : ℕ} (hk : k' < (Vd).length) (hℓ : letterAt Vd k' = .σ m') (hext : ¬ ExtCol X Pd k') :
    OnChain hW (dC X Y m e hm hW) (σSlotA hW hk hℓ) := by
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  have hv := σSlotA_val hW hk hℓ
  rcases d_σcol X Y m hℓ hext with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [E2] at hv
    cases e
    · simp only [Bool.not_false, ↓reduceIte] at hv
      exact dC_chain_of X Y m t false hm hW ht he 6 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
      exact dC_chain_of X Y m t true hm hW ht he 5 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · rw [E3] at hv
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact dC_chain_of X Y m t false hm hW ht he 2 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact dC_chain_of X Y m t true hm hW ht he 1 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

theorem d_hK : ∀ (k' m' : ℕ) (hk : k' < (Vd).length) (hℓ : letterAt Vd k' = .σ m'),
    ExtCol X Pd k' ↔ Unch .std hW (dMv X Y m) (σSlotA hW hk hℓ) ∧ Unch .std hW (dMv X Y m) (σSlotB hW hk hℓ) := by
  intro k' m' hk hℓ
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  constructor
  · intro hext
    have hext' := (d_extCol X m k').1 hext
    exact ⟨unch_of_extCol .std hW _ (d_hmv X Y m) (by rw [(σSlotA_spec hW hk hℓ).1]; exact hext'),
      unch_of_extCol .std hW _ (d_hmv X Y m) (by rw [(σSlotB_spec hW hk hℓ).1]; exact hext')⟩
  · rintro ⟨hA', -⟩
    by_contra hext
    have hv := σSlotA_val hW hk hℓ
    rcases d_σcol X Y m hℓ hext with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- column `|X|`: the over slot is the lifted arm vertex or leads to it
      rw [E2] at hv
      cases e
      · simp only [Bool.not_false, ↓reduceIte] at hv
        have h2 := hA'.2
        have hb2 : bit Vd X.length (m + 1) = true := by rw [E2]; rfl
        have hn : (next hW (σSlotA hW hk hℓ)).1 = tvC4 X.length m 5 := d_A2 X Y m hW hv hb2
        rw [d_mv_C X Y m hm 5 (by norm_num) _ hn, hn, d_pt_C X Y m hm 5 (by norm_num)] at h2
        have := congrArg Prod.snd h2
        simp only [mvB4, pvB4] at this
        linarith
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
        have h1 := hA'.1
        have hv' : (σSlotA hW hk hℓ).1 = tvC4 X.length m 5 := hv
        rw [d_mv_C X Y m hm 5 (by norm_num) _ hv', hv', d_pt_C X Y m hm 5 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvB4, pvB4] at this
        linarith
    · -- column `|X|+1`
      rw [E3] at hv
      cases e
      · simp only [Bool.false_eq_true, ↓reduceIte] at hv
        have h1 := hA'.1
        have hv' : (σSlotA hW hk hℓ).1 = tvC4 X.length m 2 := hv
        rw [d_mv_C X Y m hm 2 (by norm_num) _ hv', hv', d_pt_C X Y m hm 2 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvB4, pvB4] at this
        linarith
      · simp only [↓reduceIte] at hv
        have h2 := hA'.2
        have hn : (next hW (σSlotA hW hk hℓ)).1 = tvC4 X.length m 2 := d_A6 X Y m hW hv E3
        rw [d_mv_C X Y m hm 2 (by norm_num) _ hn, hn, d_pt_C X Y m hm 2 (by norm_num)] at h2
        have := congrArg Prod.snd h2
        simp only [mvB4, pvB4] at this
        linarith

theorem d_hKout : ∀ (k' m' : ℕ) (hk : k' < (Vd).length) (hℓ : letterAt Vd k' = .σ m'),
    ExtCol X Pd k' ↔ PieceOut (tIIR X.length hB) hW (ptv .std) (σSlotA hW hk hℓ) := by
  intro k' m' hk hℓ
  constructor
  · intro hext
    exact pieceOut_of_extCol _ .std hW _ (tIIR_xge_mem _ _) (tIIR_xle_mem _ _) (unch_pt _ _ _)
      (by rw [(σSlotA_spec hW hk hℓ).1]; exact (d_extCol X m k').1 hext)
  · intro hout
    by_contra hext
    obtain ⟨j, hj, hjs⟩ := d_σA_chain X Y m t e hm hW ht he hk hℓ hext
    have hj' : j < 6 := hj
    rw [← hjs] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (dC_chain_in X Y m t e hm hW ht he j hj').2

theorem d_cross : ∃ (k₁ m₁ : ℕ) (hk₁ : k₁ < (Vd).length) (hℓ₁ : letterAt Vd k₁ = .σ m₁) (k₂ m₂ : ℕ) (hk₂ : k₂ < (Vd).length)
    (hℓ₂ : letterAt Vd k₂ = .σ m₂), k₁ ≠ k₂ ∧ ¬ ExtCol X Pd k₁ ∧ ¬ ExtCol X Pd k₂ ∧
    (∀ (kk mm : ℕ) (_hk : kk < (Vd).length) (_hℓ : letterAt Vd kk = .σ mm), ¬ ExtCol X Pd kk → kk = k₁ ∨ kk = k₂) ∧
    ((OnChain hW (dT X Y m t hm hW) (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW (dT X Y m t hm hW) (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW (dC X Y m e hm hW) (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW (dC X Y m e hm hW) (σSlotB hW hk₂ hℓ₂)) ∨
     (OnChain hW (dC X Y m e hm hW) (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW (dC X Y m e hm hW) (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW (dT X Y m t hm hW) (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW (dT X Y m t hm hW) (σSlotB hW hk₂ hℓ₂))) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := d_letters X Y m
  obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := d_bits X Y m t e hm hW ht he
  have hk₀ : X.length < (Vd).length := by rw [d_length]; omega
  have hk₁ : X.length + 1 < (Vd).length := by rw [d_length]; omega
  have hext₀ : ¬ ExtCol X Pd X.length := by rw [d_extCol]; omega
  have hext₁ : ¬ ExtCol X Pd (X.length + 1) := by rw [d_extCol]; omega
  refine ⟨X.length, m + 1, hk₀, hℓ₀, X.length + 1, m, hk₁, hℓ₁, by omega, hext₀, hext₁, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · intro kk mm _ hℓ hext
    rcases d_σcol X Y m hℓ hext with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · exact d_σA_chain X Y m t e hm hW ht he hk₀ hℓ₀ hext₀
  · exact d_σA_chain X Y m t e hm hW ht he hk₁ hℓ₁ hext₁
  · have hv := σSlotB_val hW hk₀ hℓ₀
    rw [show m + 1 + 1 = m + 2 from rfl, ht] at hv
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact dT_chain_of X Y m false e hm hW ht he 1 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact dT_chain_of X Y m true e hm hW ht he 0 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · have hv := σSlotB_val hW hk₁ hℓ₁
    rw [E4] at hv
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact dT_chain_of X Y m false e hm hW ht he 2 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact dT_chain_of X Y m true e hm hW ht he 1 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

/-- pieces of the through-strand never share a column -/
theorem d_pairs_TT : ∀ j j', j < 3 → j' < 3 → j ≠ j' →
    colOf ((dT X Y m t hm hW).slot hW j) = colOf ((dT X Y m t hm hW).slot hW j') → False := by
  intro j j' hj hj' hjj hc
  rw [dT_col X Y m t e hm hW ht he j hj, dT_col X Y m t e hm hW ht he j' hj'] at hc
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc
    interval_cases j <;> interval_cases j' <;> first | exact hjj rfl | (norm_num [colT] at hc <;> omega)
  · simp only [↓reduceIte] at hc
    interval_cases j <;> interval_cases j' <;> first | exact hjj rfl | (norm_num [colT] at hc <;> omega)

/-- the same-column pairs of a through-piece and a cusp-arc piece -/
theorem d_pairs_TC : ∀ j j', j < 3 → j' < 6 →
    colOf ((dT X Y m t hm hW).slot hW j) = colOf ((dC X Y m e hm hW).slot hW j') →
    MeetSpec .std hW (dMv X Y m) (ExtCol X Pd) ((dT X Y m t hm hW).slot hW j) ((dC X Y m e hm hW).slot hW j') := by
  intro j j' hj hj' hc
  rw [dT_col X Y m t e hm hW ht he j hj, dC_col X Y m t e hm hW ht he j' hj'] at hc
  have hnT := dT_next_slot X Y m t hm hW
  have hnC := dC_next_slot X Y m e hm hW
  have hmvT := dT_mv_slot X Y m t e hm hW ht he
  have hmvC := dC_mv_slot X Y m t e hm hW ht he
  cases t <;> cases e
  · -- `t = false`, `e = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 2 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (dII_NM_T2C3 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 3 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (dII_NM_T2C2 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (dII_NM_T1C4 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (dII_NM_T1C1 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 0 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (dII_NM_T0C5 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 5 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (dII_NM_T0C0 _ _).revl.revr
  · -- `t = false`, `e = true`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 2 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (dII_NM_T2C2 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 3 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (dII_NM_T2C3 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (dII_NM_T1C1 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (dII_NM_T1C4 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 0 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (dII_NM_T0C0 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 5 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (dII_NM_T0C5 _ _).revl
  · -- `t = true`, `e = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 0 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (dII_NM_T0C5 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 5 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (dII_NM_T0C0 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (dII_NM_T1C4 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (dII_NM_T1C1 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 2 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (dII_NM_T2C3 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 3 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (dII_NM_T2C2 _ _).revr
  · -- `t = true`, `e = true`
    simp only [↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 0 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (dII_NM_T0C0 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 5 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (dII_NM_T0C5 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (dII_NM_T1C1 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (dII_NM_T1C4 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 2 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (dII_NM_T2C2 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 3 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (dII_NM_T2C3 _ _)

/-- the same-column pairs of two cusp-arc pieces -/
theorem d_pairs_CC : ∀ j j', j < 6 → j' < 6 → j ≠ j' →
    colOf ((dC X Y m e hm hW).slot hW j) = colOf ((dC X Y m e hm hW).slot hW j') →
    MeetSpec .std hW (dMv X Y m) (ExtCol X Pd) ((dC X Y m e hm hW).slot hW j) ((dC X Y m e hm hW).slot hW j') := by
  intro j j' hj hj' hjj hc
  rw [dC_col X Y m t e hm hW ht he j hj, dC_col X Y m t e hm hW ht he j' hj'] at hc
  have hn := dC_next_slot X Y m e hm hW
  have hmv := dC_mv_slot X Y m t e hm hW ht he
  cases e
  · -- `e = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact (dII_NM_C0C5 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (dII_NM_C1C4 _ _).symm.revl.revr
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (dII_OJ234 _ _).rev
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (dII_OJ234 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (dII_NM_C1C4 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (dII_NM_C0C5 _ _).revl.revr
  · -- `e = true`
    simp only [↓reduceIte] at hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact dII_NM_C0C5 _ _
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact dII_NM_C1C4 _ _
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact dII_OJ234 _ _
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact dII_OJ234 _ _
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (dII_NM_C1C4 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (dII_NM_C0C5 _ _).symm

theorem d_pairs : ∀ u v : Slot Vd, (OnChain hW (dT X Y m t hm hW) u ∨ OnChain hW (dC X Y m e hm hW) u) →
    (OnChain hW (dT X Y m t hm hW) v ∨ OnChain hW (dC X Y m e hm hW) v) →
    u ≠ v → colOf u = colOf v → MeetSpec .std hW (dMv X Y m) (ExtCol X Pd) u v := by
  intro u v hu hv hne hc
  rcases hu with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> rcases hv with ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩
  · exact (d_pairs_TT X Y m t e hm hW ht he j j' hj hj' (fun h => hne (by rw [h])) hc).elim
  · exact d_pairs_TC X Y m t e hm hW ht he j j' hj hj' hc
  · exact (d_pairs_TC X Y m t e hm hW ht he j' j hj' hj hc.symm).symm
  · exact d_pairs_CC X Y m t e hm hW ht he j j' hj hj' (fun h => hne (by rw [h])) hc

theorem d_genericData : GenericData .std hW (dMv X Y m) (ExtCol X Pd) :=
  genericData_of' (tIIR X.length hB) .std hW (dMv X Y m) (ExtCol X Pd)
    (fun u => OnChain hW (dT X Y m t hm hW) u ∨ OnChain hW (dC X Y m e hm hW) u)
    (mvIId_injective _ _ _ m) (mvIId_xcoord _ _ _ _)
    (fun u => by
      rcases d_rest X Y m t e hm hW ht he u with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h)
    (fun u hu => by
      rcases hu with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact (dT_chain_in X Y m t e hm hW ht he j hj).1
      · exact (dC_chain_in X Y m t e hm hW ht he j hj).1)
    (d_pairs X Y m t e hm hW ht he)
    (fun k' m' hk hℓ hA' hB' => (d_hK X Y m t e hm hW ht he k' m' hk hℓ).2 ⟨hA', hB'⟩)

theorem d_riiSpec : RIISpec (tIIR X.length hB) .std hW (dMv X Y m) (ExtCol X Pd) (dT X Y m t hm hW) (dC X Y m e hm hW) where
  disc := tIIR_isDisc _ _
  hK := d_hK X Y m t e hm hW ht he
  hKout := d_hKout X Y m t e hm hW ht he
  moved := d_moved X Y m hm
  chain₁ := dT_chain_in X Y m t e hm hW ht he
  chain₂ := dC_chain_in X Y m t e hm hW ht he
  vert₁ := dT_vert X Y m t e hm hW ht he
  vert₂ := dC_vert X Y m t e hm hW ht he
  rest := d_rest X Y m t e hm hW ht he
  prevOut₁ := d_prevOut₁ X Y m t e hm hW ht he
  stopOut₁ := d_stopOut₁ X Y m t e hm hW ht he
  prevOut₂ := d_prevOut₂ X Y m t e hm hW ht he
  stopOut₂ := d_stopOut₂ X Y m t e hm hW ht he
  disj := fun j hj j' hj' => d_disj X Y m t e hm hW ht he j j' (Nat.le_of_lt hj) (Nat.le_of_lt hj')
  touch := d_touch X Y m t e hm hW ht he
  exits := d_exits X Y m hW
  cross := d_cross X Y m t e hm hW ht he

theorem d_riiData (hne : Vd ≠ []) :
    Nonempty (RIIData (polygon (tIIR X.length hB))
      (mvDiagram .std hW hne (dMv X Y m) (ExtCol X Pd) (d_genericData X Y m t e hm hW ht he)) (rlDiagram .std hW hne)) :=
  riiData_of hne (d_genericData X Y m t e hm hW ht he) (d_riiSpec X Y m t e hm hW ht he)

theorem d_recordIso (hne : Vd ≠ []) (W' : OWord) (hW'eq : W'.letters = Vd') :
    Nonempty (RecordIso (mvDiagram .std hW hne (dMv X Y m) (ExtCol X Pd) (d_genericData X Y m t e hm hW ht he)).record
      (realize W').diagram.record) := by
  have hW' : (Vd').Closed := by have := W'.closed; rwa [hW'eq] at this
  refine ⟨vertexMovedRecordIso' X Pd Y Pd' (by simp) (d_sameEffect X Y m hm hW) hW hW' .std hne _ _ _ _
    (slotDiagramData_of .std hW hne (dMv X Y m) (ExtCol X Pd) (d_genericData X Y m t e hm hW ht he) (d_hK X Y m t e hm hW ht he))
    (d_passage X Y m hm hW hW') (d_hexit X Y m hW) (c'_hexit X Y m hW') ?_ W' hW'eq (by simp)⟩
  intro k' hk1 hk2
  simp only [List.length_cons, List.length_nil] at hk2
  have : k' = X.length := by omega
  subst this
  rw [c'_letters X Y m]; rfl

omit hW ht he in
/-- LEAF CASE (type II, variant (d): `σ_{m+1} σ_m r_{m+1} ↦ r_m`). -/
theorem typeII_d {W W' : OWord} (hWeq : W.letters = Vd) (hW'eq : W'.letters = Vd') :
    ∃ D : Diagram, RII D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨Wl, hWl⟩ := W
  simp only at hWeq
  subst hWeq
  have hne : Vd ≠ [] := by simp
  rw [realize_eq_realizeAt ⟨_, hWl⟩ hne]
  exact ⟨mvDiagram .std hWl hne (dMv X Y m) (ExtCol X Pd) (d_genericData X Y m _ _ hm hWl rfl rfl),
    ⟨polygon (tIIR X.length hB), Or.inl (d_riiData X Y m _ _ hm hWl rfl rfl hne)⟩,
    d_recordIso X Y m _ _ hm hWl rfl rfl hne W' hW'eq⟩

end TypeIIdSpec2

/-! #### J. The type-II leaf: the four variants -/

/-- LEAF (ng:front-II): the four patterns of `IsTypeII`, each realized by a vertex-moved diagram related to the
realization by a Reidemeister-II site and carrying the record of the target word. -/
theorem typeII_move_proof {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    ∃ D : Diagram, RII D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨X, Y, m, ⟨d, hm, hWeq, hW'eq⟩ | ⟨d, hm, hWeq, hW'eq⟩ | ⟨hm, hWeq, hW'eq⟩ | ⟨hm, hWeq, hW'eq⟩⟩ := h
  · exact typeII_a X Y m d hm hWeq hW'eq
  · exact typeII_b X Y m d hm hWeq hW'eq
  · exact typeII_c X Y m hm hWeq hW'eq
  · exact typeII_d X Y m hm hWeq hW'eq

end

end U6

/-- LEAF (ng:front-II, sm-3:1979-1984 "the through-strand is under at both crossings [or over at both] ...
After rounding the cusp, the arcs bound an empty ordinary bigon with one common over-strand: an oriented
Reidemeister-II site"): a diagram `D` — `realize W` with the through-strand's two interior vertices in the
block lifted past the cusp arms — related to `realize W` by `RII` (the bigon disappears) and carrying the
named record of `realize W'` (no crossing left in the block; exterior visits and the block's connections of
the boundary slots agree).  All four variants of `IsTypeII` (right-cusp versions: the same strands backwards). -/
theorem typeII_move {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    ∃ D : Diagram, RII D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := U6.typeII_move_proof h

end Leaves

/-! ## Glue: the polynomial consumer (verbatim from `Skeleton_W2.lean` L14625-14630) -/

/-- ng:front-II: `Δd = 0` (`P_reidemeister_II` to the vertex-moved diagram, then its record). -/
theorem P_typeII {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := typeII_move h
  exact (P_reidemeister_II hR).symm.trans (presentations _ _ hrec)

end FrontRows

open FrontRows

/-! ## Assembly of row 78 (verbatim from `Skeleton_W2.lean` L14765-14773) -/

/-- **ng:front-II** (row 78), assembled. -/
theorem ng_front_II : NgFrontIIClauses where
  typeII_D := fun _ _ h => (typeII_counts h).1
  typeII_w := fun _ _ h => (typeII_counts h).2
  typeII_d := fun _ _ h => by rw [P_typeII h]
  typeII_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(typeII_counts h).1, (typeII_counts h).2, P_typeII h]

/-! ## Row 83: `certificate_laws`, `word_bound` and `ng_local_front_bound` (verbatim from `Skeleton_W2.lean` L14842-14891) -/

namespace FrontRows

/-! ## Row 83: the word bound, then the smooth front -/

/-- The seven laws of the descent (`Moves.Laws`) for the moves of `SM.ng_finite_word` with the geometric
`s`, `B` of the realization and the axiom's syntactic base: `pres_B` = rows 76(1), 77, 78, 79; `del_B` =
rows 80, 81(1); `skein_B` = row 82; `base_B` = row 81(2-3) on the syntactic base (`base_defect_nonneg`);
the three `s` laws are the accepted `wordMoves_pres_s/del_s/skein_s` (definitionally the same fields). -/
theorem certificate_laws :
    (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect) OWord.IsStandardCircleBase).Laws where
  pres_B := fun F F' h => by
    rcases h with h | h | h | h
    · exact ng_commutation.comm_B F F' h
    · exact ng_front_I.typeI_B F F' h
    · exact ng_front_II.typeII_B F F' h
    · exact ng_front_III.typeIII_B F F' h
  pres_s := fun F F' h => wordMoves_pres_s F F' h
  del_B := fun F F' h => by
    rcases h with h | h | h
    · exact ng_deletions.zigzag_B F F' h
    · exact ng_deletions.crossedCusp_B F F' h
    · exact (ng_circle.circleDeletion_B F F' h).symm.le
  del_s := fun F F' h => wordMoves_del_s F F' h
  skein_B := fun F F' C h => ng_cusp_skein.earlier_branch F F' C h
  skein_s := fun F F' C h => wordMoves_skein_s F F' C h
  base_B := fun W hW => base_defect_nonneg W hW

/-- ng:local-front-bound on words (sm-3:2313-2343, the degree induction along the principal chains of
Literature input ng:finite-word): `B ≥ 0` on every closed oriented word's realization.  Consumes
`SM.ng_finite_word`.  The named companion of row 83 (not a field: the printed clause is on the smooth
class). -/
theorem word_bound : ∀ W : OWord, 0 ≤ (realize W).defect :=
  ng_finite_word_bound _ _ certificate_laws

end FrontRows

/-- **ng:local-front-bound** (row 83), assembled: the representation clause of ng:commutation carries `D`,
`w` and the rounding's record to a word; rp:record-polynomial (`presentations`) carries `P`; the word
bound gives `B ≥ 0`; display ng:defect converts (sm-3:2343). -/
theorem ng_local_front_bound : NgLocalFrontBoundClauses where
  front_inequality := fun F S hS => by
    obtain ⟨W, hD, hw, -, hrec⟩ := ng_commutation.represent F
    have hP : P S = P (realize W).diagram := presentations S _ (hrec S hS)
    have h0 := FrontRows.word_bound W
    rw [← F.defect_nonneg_iff S]
    unfold SmoothFront.defect SmoothFront.dOf
    rw [hD, hw, hP]
    exact h0

end SM
