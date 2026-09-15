import SM.FrontRealize

/-! Front block, lane β, unit β2 (2026-09-14): module `SM/FrontRealizeCorrespondence.lean` (intended home).
Adopted design work/reports/front-block-design-FINAL-20260913.md (§2 G1, §4, §9 FR-5); β1 report
work/drafts/front/BETA1_REPORT.md §5 items 1-3.

# The grid realization, part 3: letters ↔ singularities

For a closed nonempty word `W` and any placement `pl`, `F := realizeAt pl hW hne` satisfies:
* strands ↔ slots (`slotOf`, `strandOfSlot`), and the rightward bit `F.xdir` of the strand leaving a cut
  slot `(k, p)` is the cut bit `bit W k p` (`xdir_eq`, `xdir_cut`);
* the cusps of `F` are exactly the cusp vertices (`isCusp_iff`), left cusps the `l` letters, right cusps the
  `r` letters, and a cusp is downward iff the letter's `downBit` is `1` (`isDownCusp_iff`);
* the crossings of `F` are in bijection with the `σ` letters (`crossingEquiv`): the crossing of column `k`
  is `{strand of pass m (m+1), strand of pass (m+1) m}`, its double point the centre of the column, the
  over strand the one descending from position `m` to `m+1`, and its sign is `+1` iff the two bits at
  positions `m`, `m+1` agree (`sign_eq`);
* the counts: `F.crossingCount = W.crossingCount`, `F.cuspCount = W.cuspCount`, `F.sCount = W.sCount`,
  `F.downCount = W.downCountFrom []`, `F.writhe = W.writheFrom []` (part 4 below).

All declarations live in `SM.FrontRealize`.  Checked with `lake env lean` (sorry-free, standard axioms). -/

namespace SM.FrontRealize

open SM SM.Link SM.FrontWord SM.FrontWord.Letter

noncomputable section

section Corr

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])
include hW

/-- The strand whose tail is a given slot. -/
def strandOfSlot (u : Slot W) : (realizeAt pl hW hne).Γ.Strand := (idxEquiv hW).symm u

theorem slotOf_strandOfSlot (u : Slot W) : slotOf pl hW hne (strandOfSlot pl hW hne u) = u :=
  (idxEquiv hW).apply_symm_apply u

theorem strandOfSlot_slotOf (s : (realizeAt pl hW hne).Γ.Strand) : strandOfSlot pl hW hne (slotOf pl hW hne s) = s :=
  (idxEquiv hW).symm_apply_apply s

theorem strandOfSlot_injective : Function.Injective (strandOfSlot pl hW hne) := (idxEquiv hW).symm.injective

/-- The strands are the slots. -/
def strandEquiv : (realizeAt pl hW hne).Γ.Strand ≃ Slot W := idxEquiv hW

@[simp] theorem strandEquiv_apply (s) : strandEquiv pl hW hne s = slotOf pl hW hne s := rfl
@[simp] theorem strandEquiv_symm_apply (u) : (strandEquiv pl hW hne).symm u = strandOfSlot pl hW hne u := rfl

/-! ### The direction bit -/

theorem dir_eq' (s : (realizeAt pl hW hne).Γ.Strand) :
    (realizeAt pl hW hne).Γ.dir s = pt pl W (next hW (slotOf pl hW hne s)).1 - pt pl W (slotOf pl hW hne s).1 :=
  dir_eq pl hW hne s

/-- The rightward bit of a strand is the `xsign` of its slot. -/
theorem xdir_eq (s : (realizeAt pl hW hne).Γ.Strand) : (realizeAt pl hW hne).xdir s = xsign (slotOf pl hW hne s) := by
  have h := dir_slot_fst_pos_iff pl hW (slotOf pl hW hne s)
  rw [← dir_eq'] at h
  unfold PLFront.xdir
  cases hx : xsign (slotOf pl hW hne s)
  · rw [hx] at h; simp only [Bool.false_eq_true, iff_false] at h; exact decide_eq_false h
  · rw [hx] at h; exact decide_eq_true (h.2 rfl)

/-- The rightward bit of the strand leaving the cut slot `(k, p)` is the cut bit `bit W k p`. -/
theorem xdir_cut {k p : ℕ} (h : IsSlot W (k, p)) (hp : p ≠ 0) :
    (realizeAt pl hW hne).xdir (strandOfSlot pl hW hne ⟨(k, p), h⟩) = bit W k p := by
  rw [xdir_eq, slotOf_strandOfSlot, xsign_cut rfl hp]

omit hW in
/-- the cut bit as a list element -/
theorem bit_eq_getElem {k m : ℕ} (h : m - 1 < (cut W k).length) : bit W k m = (cut W k)[m - 1] := by
  rw [bit_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-! ### Cusps -/

/-- `PLFront.prev` is the strand arriving at the tail slot. -/
theorem slotOf_prev (s : (realizeAt pl hW hne).Γ.Strand) :
    slotOf pl hW hne ((realizeAt pl hW hne).prev s) = prev hW (slotOf pl hW hne s) := by
  obtain ⟨i, j⟩ := s
  exact slotOf_pred pl hW hne i j

theorem eIn_eq (s : (realizeAt pl hW hne).Γ.Strand) :
    (realizeAt pl hW hne).eIn s = pt pl W (slotOf pl hW hne s).1 - pt pl W (prev hW (slotOf pl hW hne s)).1 := by
  unfold PLFront.eIn
  rw [dir_eq', slotOf_prev, next_prev]

theorem eOut_eq (s : (realizeAt pl hW hne).Γ.Strand) :
    (realizeAt pl hW hne).eOut s = pt pl W (next hW (slotOf pl hW hne s)).1 - pt pl W (slotOf pl hW hne s).1 :=
  dir_eq' pl hW hne s

/-- A strand starts at a cusp iff its tail slot is a cusp vertex. -/
theorem isCusp_iff (s : (realizeAt pl hW hne).Γ.Strand) :
    (realizeAt pl hW hne).IsCusp s ↔ (slotOf pl hW hne s).1.2 = 0 := by
  set u := slotOf pl hW hne s with hu
  have hx : xsign u = xsign (prev hW u) ↔ u.1.2 ≠ 0 := by
    have := xsign_next_iff hW (prev hW u); rwa [next_prev] at this
  have ha := dir_slot_fst_pos_iff pl hW (prev hW u)
  rw [next_prev] at ha
  have hb := dir_slot_fst_pos_iff pl hW u
  have hne1 := dir_slot_fst_ne_zero pl hW (prev hW u)
  rw [next_prev] at hne1
  have hne2 := dir_slot_fst_ne_zero pl hW u
  unfold PLFront.IsCusp
  rw [eIn_eq, eOut_eq, ← hu]
  have ha0 : xsign (prev hW u) = false → (pt pl W u.1 - pt pl W (prev hW u).1).1 < 0 := fun hp =>
    lt_of_le_of_ne (not_lt.1 (fun hh => by rw [ha, hp] at hh; exact absurd hh (by decide))) hne1
  have ha1 : xsign (prev hW u) = true → 0 < (pt pl W u.1 - pt pl W (prev hW u).1).1 := fun hp => ha.2 hp
  have hb0 : xsign u = false → (pt pl W (next hW u).1 - pt pl W u.1).1 < 0 := fun hq =>
    lt_of_le_of_ne (not_lt.1 (fun hh => by rw [hb, hq] at hh; exact absurd hh (by decide))) hne2
  have hb1 : xsign u = true → 0 < (pt pl W (next hW u).1 - pt pl W u.1).1 := fun hq => hb.2 hq
  constructor
  · intro h
    by_contra hc
    have hxx := hx.2 hc
    cases hq : xsign u
    · have hp : xsign (prev hW u) = false := hxx.symm.trans hq
      have := ha0 hp; have := hb0 hq; nlinarith
    · have hp : xsign (prev hW u) = true := hxx.symm.trans hq
      have := ha1 hp; have := hb1 hq; nlinarith
  · intro hc
    have hxx : xsign u ≠ xsign (prev hW u) := fun hh => (hx.1 hh) hc
    cases hq : xsign u <;> cases hp : xsign (prev hW u)
    · exact absurd (hq.trans hp.symm) hxx
    · have := ha1 hp; have := hb0 hq; nlinarith
    · have := ha0 hp; have := hb1 hq; nlinarith
    · exact absurd (hq.trans hp.symm) hxx

/-- The arms at a left cusp `(k, 0)` with letter `l m d`. -/
theorem arms_l {u : Slot W} {k m : ℕ} {d : Bool} (hu : u.1 = (k, 0)) (hℓ : letterAt W k = .l m d) :
    pt pl W (next hW u).1 - pt pl W u.1 = (pl.w k / 2, if d then 1 / 2 else -(1 / 2)) ∧
    pt pl W u.1 - pt pl W (prev hW u).1 = (-(pl.w k / 2), if d then 1 / 2 else -(1 / 2)) := by
  have hn : (next hW u).1 = nextPair W (k, 0) := by rw [next_val, hu]
  have hp : (prev hW u).1 = prevPair W (k, 0) := by rw [prev_val, hu]
  have hm : 1 ≤ m := by
    have := u.2; rw [hu] at this
    rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
    · obtain ⟨D⟩ := decomp hW k hk; rw [hℓ] at D; have := D.hm; simpa [idx] using this
    · simp at h0
  rw [hn, hp, nextPair_cusp_l W hℓ, prevPair_cusp_l W hℓ, hu, pt_cusp, hℓ,
    pt_cut pl W (by split_ifs <;> omega), pt_cut pl W (by split_ifs <;> omega)]
  simp only [idx]
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩ <;> refine Prod.ext ?_ ?_ <;> simp [Placement.w, Placement.mid] <;> ring
  · simp only [↓reduceIte]
    refine ⟨?_, ?_⟩ <;> refine Prod.ext ?_ ?_ <;> simp [Placement.w, Placement.mid] <;> ring

/-- The arms at a right cusp `(k, 0)` with letter `r m`; `b = bit W k m` is the bit of the upper arm. -/
theorem arms_r {u : Slot W} {k m : ℕ} (hu : u.1 = (k, 0)) (hℓ : letterAt W k = .r m) :
    pt pl W (next hW u).1 - pt pl W u.1 = (-(pl.w k / 2), if bit W k m then -(1 / 2) else 1 / 2) ∧
    pt pl W u.1 - pt pl W (prev hW u).1 = (pl.w k / 2, if bit W k m then -(1 / 2) else 1 / 2) := by
  have hn : (next hW u).1 = nextPair W (k, 0) := by rw [next_val, hu]
  have hp : (prev hW u).1 = prevPair W (k, 0) := by rw [prev_val, hu]
  have hm : 1 ≤ m := by
    have := u.2; rw [hu] at this
    rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
    · obtain ⟨D⟩ := decomp hW k hk; rw [hℓ] at D; have := D.hm; simpa [idx] using this
    · simp at h0
  rw [hn, hp, nextPair_cusp_r W hℓ, prevPair_cusp_r W hℓ, hu, pt_cusp, hℓ,
    pt_cut pl W (by split_ifs <;> omega), pt_cut pl W (by split_ifs <;> omega)]
  simp only [idx]
  cases bit W k m
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩ <;> refine Prod.ext ?_ ?_ <;> simp [Placement.w, Placement.mid] <;> ring
  · simp only [↓reduceIte]
    refine ⟨?_, ?_⟩ <;> refine Prod.ext ?_ ?_ <;> simp [Placement.w, Placement.mid] <;> ring

/-- Left cusps are the `l` letters. -/
theorem isLeftCusp_iff (s : (realizeAt pl hW hne).Γ.Strand) :
    (realizeAt pl hW hne).IsLeftCusp s ↔
      (slotOf pl hW hne s).1.2 = 0 ∧ ∃ m d, letterAt W (slotOf pl hW hne s).1.1 = .l m d := by
  set u := slotOf pl hW hne s with hu
  constructor
  · intro h
    have hc : (realizeAt pl hW hne).IsCusp s := h.isCusp
    rw [isCusp_iff, ← hu] at hc
    refine ⟨hc, ?_⟩
    rcases letterAt_of_cusp (W := W) (s := u) hc with ⟨m, d, hℓ⟩ | ⟨m, hℓ⟩
    · exact ⟨m, d, hℓ⟩
    · exfalso
      obtain ⟨h1, -⟩ := arms_r pl hW (u := u) (k := u.1.1) (m := m) (Prod.ext rfl hc) hℓ
      have h2 := h.2
      rw [eOut_eq, ← hu, h1] at h2
      simp only at h2
      linarith [pl.w_pos u.1.1]
  · rintro ⟨hc, m, d, hℓ⟩
    obtain ⟨h1, h2⟩ := arms_l pl hW (u := u) (k := u.1.1) (Prod.ext rfl hc) hℓ
    constructor
    · rw [eIn_eq, ← hu, h2]; simp only; linarith [pl.w_pos u.1.1]
    · rw [eOut_eq, ← hu, h1]; simp only; linarith [pl.w_pos u.1.1]

/-- Right cusps are the `r` letters. -/
theorem isRightCusp_iff (s : (realizeAt pl hW hne).Γ.Strand) :
    (realizeAt pl hW hne).IsRightCusp s ↔
      (slotOf pl hW hne s).1.2 = 0 ∧ ∃ m, letterAt W (slotOf pl hW hne s).1.1 = .r m := by
  set u := slotOf pl hW hne s with hu
  constructor
  · intro h
    have hc : (realizeAt pl hW hne).IsCusp s := h.isCusp
    rw [isCusp_iff, ← hu] at hc
    refine ⟨hc, ?_⟩
    rcases letterAt_of_cusp (W := W) (s := u) hc with ⟨m, d, hℓ⟩ | ⟨m, hℓ⟩
    · exfalso
      obtain ⟨h1, -⟩ := arms_l pl hW (u := u) (k := u.1.1) (Prod.ext rfl hc) hℓ
      have h2 := h.2
      rw [eOut_eq, ← hu, h1] at h2
      simp only at h2
      linarith [pl.w_pos u.1.1]
    · exact ⟨m, hℓ⟩
  · rintro ⟨hc, m, hℓ⟩
    obtain ⟨h1, h2⟩ := arms_r pl hW (u := u) (k := u.1.1) (Prod.ext rfl hc) hℓ
    constructor
    · rw [eIn_eq, ← hu, h2]; simp only; linarith [pl.w_pos u.1.1]
    · rw [eOut_eq, ← hu, h1]; simp only; linarith [pl.w_pos u.1.1]

/-- The letter-tracing down bit of a cusp letter is `1` exactly when the geometric cusp is downward:
`l _ d` is downward iff `d = false`; `r m` iff the upper strand at position `m` travels rightward. -/
theorem isDownCusp_iff (s : (realizeAt pl hW hne).Γ.Strand) :
    (realizeAt pl hW hne).IsDownCusp s ↔
      (slotOf pl hW hne s).1.2 = 0 ∧
        (letterAt W (slotOf pl hW hne s).1.1).downBit (cut W (slotOf pl hW hne s).1.1) = 1 := by
  set u := slotOf pl hW hne s with hu
  have hcusp : (realizeAt pl hW hne).IsCusp s ↔ u.1.2 = 0 := isCusp_iff pl hW hne s
  have hw := pl.w_pos u.1.1
  constructor
  · rintro ⟨hc, hd⟩
    have hc' := hcusp.1 hc
    refine ⟨hc', ?_⟩
    unfold PLFront.cuspDisc at hd
    rw [eIn_eq, eOut_eq, ← hu] at hd
    rcases letterAt_of_cusp (W := W) (s := u) hc' with ⟨m, d, hℓ⟩ | ⟨m, hℓ⟩
    · obtain ⟨h1, h2⟩ := arms_l pl hW (u := u) (k := u.1.1) (Prod.ext rfl hc') hℓ
      rw [h1, h2] at hd
      rw [hℓ]
      cases d
      · rfl
      · exfalso; simp [det] at hd; nlinarith
    · obtain ⟨h1, h2⟩ := arms_r pl hW (u := u) (k := u.1.1) (Prod.ext rfl hc') hℓ
      rw [h1, h2] at hd
      rw [hℓ]
      simp only [downBit]
      have hu0 : u.1 = (u.1.1, 0) := Prod.ext rfl hc'
      have hm : 1 ≤ m := by
        have := u.2; rw [hu0] at this
        rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
        · obtain ⟨D⟩ := decomp hW u.1.1 hk; rw [hℓ] at D; have := D.hm; simpa [idx] using this
        · simp at h0
      have hlen : m + 1 ≤ (cut W u.1.1).length := by
        have := u.2; rw [hu0] at this
        rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
        · obtain ⟨D⟩ := decomp hW u.1.1 hk; rw [hℓ] at D; exact D.bits_r.2
        · simp at h0
      cases hb : bit W u.1.1 m
      · exfalso; rw [hb] at hd; simp [det] at hd; nlinarith
      · rw [List.drop_eq_getElem_cons (by omega)]
        have : (cut W u.1.1)[m - 1] = true := by rw [← bit_eq_getElem (by omega)]; exact hb
        simp [this]
  · rintro ⟨hc, hd⟩
    refine ⟨hcusp.2 hc, ?_⟩
    unfold PLFront.cuspDisc
    rw [eIn_eq, eOut_eq, ← hu]
    rcases letterAt_of_cusp (W := W) (s := u) hc with ⟨m, d, hℓ⟩ | ⟨m, hℓ⟩
    · obtain ⟨h1, h2⟩ := arms_l pl hW (u := u) (k := u.1.1) (Prod.ext rfl hc) hℓ
      rw [h1, h2]
      rw [hℓ] at hd
      cases d
      · simp [det]; nlinarith
      · simp [downBit] at hd
    · obtain ⟨h1, h2⟩ := arms_r pl hW (u := u) (k := u.1.1) (Prod.ext rfl hc) hℓ
      rw [h1, h2]
      rw [hℓ] at hd
      simp only [downBit] at hd
      cases hb : bit W u.1.1 m
      · exfalso
        have hu0 : u.1 = (u.1.1, 0) := Prod.ext rfl hc
        have hlen : m + 1 ≤ (cut W u.1.1).length := by
          have := u.2; rw [hu0] at this
          rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
          · obtain ⟨D⟩ := decomp hW u.1.1 hk; rw [hℓ] at D; exact D.bits_r.2
          · simp at h0
        rw [List.drop_eq_getElem_cons (by omega)] at hd
        have : (cut W u.1.1)[m - 1] = false := by rw [← bit_eq_getElem (by omega)]; exact hb
        simp [this] at hd
      · simp [det]; nlinarith

/-! ### Crossings: the `σ` letters -/

/-- The bookkeeping of a crossing letter `σ m` at column `k`. -/
theorem σ_facts {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    1 ≤ m ∧ m + 1 ≤ (cut W k).length ∧ (cut W (k + 1)).length = (cut W k).length ∧
    bit W (k + 1) (m + 1) = bit W k m ∧ bit W (k + 1) m = bit W k (m + 1) := by
  obtain ⟨D⟩ := decomp hW k hk
  rw [hℓ] at D
  obtain ⟨h1, h2, h3, h4⟩ := D.bits_σ
  have hm := D.hm
  simp only [idx] at hm
  refine ⟨hm, h3, h4, ?_, ?_⟩
  · rw [bit_succ, bit_eq]; exact h1
  · rw [bit_eq, bit_succ]; exact h2

omit hW in
theorem isSlot_cut {k p : ℕ} (hp : 1 ≤ p) (hpk : p ≤ (cut W k).length) (hk : k ≤ W.length) : IsSlot W (k, p) :=
  Or.inr ⟨hp, hpk, hk⟩

/-- The slot whose piece is the strand of `σ_m` descending from position `m` to `m+1` (`pass m (m+1)`). -/
def σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) : Slot W :=
  if bit W k m then ⟨(k, m), isSlot_cut (σ_facts hW hk hℓ).1 (by have := (σ_facts hW hk hℓ).2.1; omega) hk.le⟩
  else ⟨(k + 1, m + 1), isSlot_cut (by omega) (by obtain ⟨-, h2, h3, -, -⟩ := σ_facts hW hk hℓ; omega) hk⟩

/-- The slot whose piece is the strand of `σ_m` ascending from position `m+1` to `m` (`pass (m+1) m`). -/
def σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) : Slot W :=
  if bit W k (m + 1) then ⟨(k, m + 1), isSlot_cut (by omega) (σ_facts hW hk hℓ).2.1 hk.le⟩
  else ⟨(k + 1, m), isSlot_cut (σ_facts hW hk hℓ).1 (by obtain ⟨-, h2, h3, -, -⟩ := σ_facts hW hk hℓ; omega) hk⟩

theorem σSlotA_spec {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    colOf (σSlotA hW hk hℓ) = k ∧ shapeOf (σSlotA hW hk hℓ) = .pass m (m + 1) ∧
    xsign (σSlotA hW hk hℓ) = bit W k m := by
  obtain ⟨hm, -, -, hb1, -⟩ := σ_facts hW hk hℓ
  unfold σSlotA
  cases hb : bit W k m
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hb] at hb1
    refine ⟨?_, ?_, ?_⟩
    · simp [colOf, hb1]
    · simp [shapeOf, hb1, hℓ, posL_σ_idx_succ]
    · rw [xsign_cut rfl (show m + 1 ≠ 0 by omega), hb1]
  · simp only [↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · simp [colOf, hb, show m ≠ 0 by omega]
    · simp [shapeOf, hb, hℓ, posR_σ_idx, show m ≠ 0 by omega]
    · rw [xsign_cut rfl (show m ≠ 0 by omega), hb]

theorem σSlotB_spec {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    colOf (σSlotB hW hk hℓ) = k ∧ shapeOf (σSlotB hW hk hℓ) = .pass (m + 1) m ∧
    xsign (σSlotB hW hk hℓ) = bit W k (m + 1) := by
  obtain ⟨hm, -, -, -, hb2⟩ := σ_facts hW hk hℓ
  unfold σSlotB
  cases hb : bit W k (m + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hb] at hb2
    refine ⟨?_, ?_, ?_⟩
    · simp [colOf, hb2, show m ≠ 0 by omega]
    · simp [shapeOf, hb2, hℓ, posL_σ_idx, show m ≠ 0 by omega]
    · rw [xsign_cut rfl (show m ≠ 0 by omega), hb2]
  · simp only [↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · simp [colOf, hb]
    · simp [shapeOf, hb, hℓ, posR_σ_idx_succ]
    · rw [xsign_cut rfl (show m + 1 ≠ 0 by omega), hb]

/-- The successor and predecessor of a passing slot lie in other columns. -/
theorem colOf_next_ne_of_pass {u : Slot W} {p q : ℕ} (h : shapeOf u = .pass p q) :
    colOf (next hW u) ≠ colOf u ∧ colOf (prev hW u) ≠ colOf u := by
  rcases next_cases hW u with
    ⟨k, p', q', hs, hp, hb, hn, hq, hbq, -, -⟩ | ⟨k, p', m, hs, hp, hb, hℓ, hpm, hn, -, -⟩ |
    ⟨k, p', q', hs, hp, hb, hn, hq, hbq, -, hk1, -⟩ | ⟨k, p', m, d, hs, hp, hb, hℓ, hpm, hn, -, -, hk1, -⟩ |
    ⟨k, m, d, hs, hℓ, hn, -, -, -, -⟩ | ⟨k, m, hs, hℓ, hn, -, -, -⟩
  · have hp0 : p' ≠ 0 := by omega
    have hcol : colOf u = k := by simp [colOf, hs, hb, hp0]
    have hcn : colOf (next hW u) = k + 1 := by simp [colOf, hn, hbq, show q' ≠ 0 by omega]
    refine ⟨by omega, ?_⟩
    -- `prev u` is a rightward cut slot or a left cusp in column `k − 1`
    have hk1 : 1 ≤ k := (cutSlot_pos hW hp (by
      have := u.2; rw [hs] at this
      rcases this with ⟨h0, -⟩ | ⟨-, h1, -⟩
      · simp at h0; omega
      · exact h1)).1
    have hpu : (next hW (prev hW u)).1 = (k, p') := by rw [next_prev, hs]
    rcases next_cases hW (prev hW u) with
      ⟨k', p'', q'', hs', hp', hb', hn', -, -, -, -⟩ | ⟨k', p'', m, hs', hp', hb', hℓ, -, hn', -, -⟩ |
      ⟨k', p'', q'', hs', hp', hb', hn', -, hbq', -, -, -⟩ | ⟨k', p'', m, d, hs', hp', hb', hℓ, -, hn', -, -, -, -⟩ |
      ⟨k', m, d, hs', hℓ, hn', -, -, -, -⟩ | ⟨k', m, hs', hℓ, hn', -, -, -⟩
    · rw [hpu] at hn'; simp only [Prod.mk.injEq] at hn'; obtain ⟨rfl, rfl⟩ := hn'
      rw [hcol]; simp [colOf, hs', hb', show p'' ≠ 0 by omega]
    · rw [hpu] at hn'; simp at hn'; omega
    · rw [hpu] at hn'; simp only [Prod.mk.injEq] at hn'; obtain ⟨hk', rfl⟩ := hn'
      -- `prev u` leftward: then `u` is leftward, contradicting `hb`
      exfalso; rw [hk', hbq'] at hb; exact absurd hb (by decide)
    · rw [hpu] at hn'; simp at hn'; omega
    · rw [hpu] at hn'; simp only [Prod.mk.injEq] at hn'; obtain ⟨hk', -⟩ := hn'
      rw [hcol]; simp [colOf, hs']; omega
    · rw [hpu] at hn'; simp only [Prod.mk.injEq] at hn'; obtain ⟨rfl, -⟩ := hn'
      exfalso
      -- the successor of a right cusp is leftward
      have := xsign_next_of_cut hW (s := prev hW u) (by rw [next_prev, hs]; simpa using hp0)
      rw [next_prev, xsign_cusp_r hs' hℓ, xsign_cut hs hp0, hb] at this
      exact absurd this (by decide)
  · -- `u` enters a right cusp: its shape is an arm, not a pass
    exfalso
    have hp0 : p' ≠ 0 := by omega
    have hpq : (Letter.r m).posR p' = none := by
      rcases hpm with rfl | rfl
      · exact posR_r_idx _
      · exact posR_r_idx_succ _
    have : shapeOf u = .armR m p' := by simp [shapeOf, hs, hb, hℓ, hpq, idx, hp0]
    rw [h] at this; cases this
  · have hp0 : p' ≠ 0 := by omega
    have hcol : colOf u = k - 1 := by simp [colOf, hs, hb, hp0]
    have hq0 : q' ≠ 0 := by omega
    have hk2 : 1 ≤ k - 1 := (cutSlot_pos hW hq (by
      have := (next hW u).2; rw [hn] at this
      rcases this with ⟨h0, -⟩ | ⟨-, h1, -⟩
      · simp at h0; omega
      · exact h1)).1
    have hcn : colOf (next hW u) = k - 1 - 1 := by simp [colOf, hn, hbq, hq0]
    refine ⟨by omega, ?_⟩
    have hpu : (next hW (prev hW u)).1 = (k, p') := by rw [next_prev, hs]
    rcases next_cases hW (prev hW u) with
      ⟨k', p'', q'', hs', hp', hb', hn', -, -, -, -⟩ | ⟨k', p'', m, hs', hp', hb', hℓ, -, hn', -, -⟩ |
      ⟨k', p'', q'', hs', hp', hb', hn', -, -, -, -, -⟩ | ⟨k', p'', m, d, hs', hp', hb', hℓ, -, hn', -, -, -, -⟩ |
      ⟨k', m, d, hs', hℓ, hn', -, -, -, -⟩ | ⟨k', m, hs', hℓ, hn', -, -, -⟩
    · rw [hpu] at hn'; simp only [Prod.mk.injEq] at hn'; obtain ⟨rfl, rfl⟩ := hn'
      exfalso
      have := xsign_next_of_cut hW (s := prev hW u) (by rw [next_prev, hs]; simpa using hp0)
      rw [next_prev, xsign_cut hs' (by omega), xsign_cut hs hp0, hb, hb'] at this
      exact absurd this (by decide)
    · rw [hpu] at hn'; simp at hn'; omega
    · rw [hpu] at hn'; simp only [Prod.mk.injEq] at hn'; obtain ⟨hk', rfl⟩ := hn'
      rw [hcol]; simp [colOf, hs', hb', show p'' ≠ 0 by omega]; omega
    · rw [hpu] at hn'; simp at hn'; omega
    · rw [hpu] at hn'; simp only [Prod.mk.injEq] at hn'; obtain ⟨hk', -⟩ := hn'
      exfalso
      have := xsign_next_of_cut hW (s := prev hW u) (by rw [next_prev, hs]; simpa using hp0)
      rw [next_prev, xsign_cusp_l hs' hℓ, xsign_cut hs hp0, hb] at this
      exact absurd this (by decide)
    · rw [hpu] at hn'; simp only [Prod.mk.injEq] at hn'; obtain ⟨rfl, -⟩ := hn'
      rw [hcol]; simp [colOf, hs']; omega
  · exfalso
    have hp0 : p' ≠ 0 := by omega
    have hpq : (Letter.l m d).posL p' = none := by
      rcases hpm with rfl | rfl
      · exact posL_l_idx _ _
      · exact posL_l_idx_succ _ _
    have : shapeOf u = .armL m p' := by simp [shapeOf, hs, hb, hℓ, hpq, idx, hp0]
    rw [h] at this; cases this
  · exfalso
    have : shapeOf u = .armL m (if d then m else m + 1) := by simp [shapeOf, hs, hℓ]
    rw [h] at this; cases this
  · exfalso
    have : shapeOf u = .armR m (if bit W k m then m + 1 else m) := by simp [shapeOf, hs, hℓ]
    rw [h] at this; cases this

theorem σSlotA_ne_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    σSlotA hW hk hℓ ≠ σSlotB hW hk hℓ := by
  intro h
  have h1 := (σSlotA_spec hW hk hℓ).2.1
  have h2 := (σSlotB_spec hW hk hℓ).2.1
  rw [h, h2] at h1
  cases h1

theorem adjacent_iff' (s t : (realizeAt pl hW hne).Γ.Strand) :
    (realizeAt pl hW hne).Γ.Adjacent s t ↔
      slotOf pl hW hne t = slotOf pl hW hne s ∨ slotOf pl hW hne t = next hW (slotOf pl hW hne s) ∨
        slotOf pl hW hne t = prev hW (slotOf pl hW hne s) := adjacent_iff pl hW hne s t

theorem mem_seg_iff' (s : (realizeAt pl hW hne).Γ.Strand) (q : Plane) :
    q ∈ (realizeAt pl hW hne).Γ.seg s ↔ ∃ τ, 0 ≤ τ ∧ τ ≤ 1 ∧ q = piecePt pl (slotOf pl hW hne s) τ :=
  mem_seg_iff pl hW hne s q

theorem mem_interior_iff' (s : (realizeAt pl hW hne).Γ.Strand) (q : Plane) :
    q ∈ (realizeAt pl hW hne).Γ.interior s ↔ ∃ τ, 0 < τ ∧ τ < 1 ∧ q = piecePt pl (slotOf pl hW hne s) τ :=
  mem_interior_iff pl hW hne s q

/-- The two `σ`-slots cross at the centre of the column. -/
theorem σ_meet {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    piecePt pl (σSlotA hW hk hℓ) (1 / 2) = piecePt pl (σSlotB hW hk hℓ) (1 / 2) := by
  obtain ⟨hc1, hs1, -⟩ := σSlotA_spec hW hk hℓ
  obtain ⟨hc2, hs2, -⟩ := σSlotB_spec hW hk hℓ
  unfold piecePt
  rw [hc1, hc2, hs1, hs2, Shape.par_pass, Shape.par_pass]
  congr 2
  push_cast; ring

/-- The strands of two slots in one column with the two `σ` shapes are not adjacent. -/
theorem not_adjacent_of_σ {u v : Slot W} {m : ℕ} (hc : colOf u = colOf v)
    (hS : (shapeOf u = .pass m (m + 1) ∧ shapeOf v = .pass (m + 1) m) ∨
      (shapeOf u = .pass (m + 1) m ∧ shapeOf v = .pass m (m + 1))) :
    ¬ (realizeAt pl hW hne).Γ.Adjacent (strandOfSlot pl hW hne u) (strandOfSlot pl hW hne v) := by
  rw [adjacent_iff', slotOf_strandOfSlot, slotOf_strandOfSlot]
  have hne' : shapeOf u ≠ shapeOf v := by
    rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> intro h <;> cases h <;> omega
  have hpass : ∃ p q, shapeOf u = .pass p q := by
    rcases hS with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact ⟨_, _, h1⟩
  obtain ⟨p, q, hpq⟩ := hpass
  obtain ⟨hn, hp⟩ := colOf_next_ne_of_pass hW hpq
  rintro (h | h | h)
  · exact hne' (by rw [h])
  · exact hn (by rw [← h, hc])
  · exact hp (by rw [← h, hc])

/-- The crossing of a `σ` letter. -/
def crossingOf {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) : (realizeAt pl hW hne).Γ.Crossing :=
  ⟨{strandOfSlot pl hW hne (σSlotA hW hk hℓ), strandOfSlot pl hW hne (σSlotB hW hk hℓ)},
    ⟨_, _, rfl, not_adjacent_of_σ pl hW hne ((σSlotA_spec hW hk hℓ).1.trans (σSlotB_spec hW hk hℓ).1.symm)
        (Or.inl ⟨(σSlotA_spec hW hk hℓ).2.1, (σSlotB_spec hW hk hℓ).2.1⟩),
      ⟨piecePt pl (σSlotA hW hk hℓ) (1 / 2),
        (mem_seg_iff pl hW hne _ _).2 ⟨1 / 2, by norm_num, by norm_num, by rw [slotOf_strandOfSlot]⟩,
        (mem_seg_iff pl hW hne _ _).2 ⟨1 / 2, by norm_num, by norm_num, by
          rw [slotOf_strandOfSlot]; exact σ_meet pl hW hk hℓ⟩⟩⟩⟩

theorem crossingOf_val {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    (crossingOf pl hW hne hk hℓ).val =
      {strandOfSlot pl hW hne (σSlotA hW hk hℓ), strandOfSlot pl hW hne (σSlotB hW hk hℓ)} := rfl

/-- Every crossing is the crossing of a `σ` letter: the two strands lie in one column whose letter is
`σ m`, with the two `σ` shapes. -/
theorem crossing_char (x : (realizeAt pl hW hne).Γ.Crossing) {s t : (realizeAt pl hW hne).Γ.Strand}
    (hs : s ∈ x.val) (ht : t ∈ x.val) (hst : s ≠ t) :
    colOf (slotOf pl hW hne s) = colOf (slotOf pl hW hne t) ∧
    ∃ m, letterAt W (colOf (slotOf pl hW hne s)) = .σ m ∧
      ((shapeOf (slotOf pl hW hne s) = .pass m (m + 1) ∧ shapeOf (slotOf pl hW hne t) = .pass (m + 1) m) ∨
       (shapeOf (slotOf pl hW hne s) = .pass (m + 1) m ∧ shapeOf (slotOf pl hW hne t) = .pass m (m + 1))) := by
  obtain ⟨hna, hmeet⟩ := (realizeAt pl hW hne).Γ.crossing_pair_spec x hs ht hst
  obtain ⟨q, hqs, hqt⟩ := hmeet
  rw [mem_seg_iff'] at hqs hqt
  obtain ⟨τ, hτ0, hτ1, rfl⟩ := hqs
  obtain ⟨τ', hτ0', hτ1', hq⟩ := hqt
  set u := slotOf pl hW hne s with hu
  set v := slotOf pl hW hne t with hv
  rcases common_point pl hW u v hτ0 hτ1 hτ0' hτ1' hq with ⟨huv, -⟩ | ⟨c, -, hcu, hcv⟩ |
    ⟨hcol, -, -, m, hℓ, hS⟩
  · exact absurd ((adjacent_iff' pl hW hne s t).2 (Or.inl huv.symm)) hna
  · exfalso
    apply hna
    rw [adjacent_iff', ← hu, ← hv]
    rcases hcu with hcu | hcu <;> rcases hcv with hcv | hcv
    · exact Or.inl (hcv.symm.trans hcu)
    · right; right; rw [← hcu, hcv, prev_next]
    · exact Or.inr (Or.inl (hcv.symm.trans hcu))
    · exact Or.inl (next_injective hW (hcv.symm.trans hcu))
  · exact ⟨hcol, m, hℓ, hS⟩

/-- The `σ` letters (as column indices). -/
abbrev σIdx : Type := {k : Fin W.length // (letterAt W k).isCrossing = true}

omit hW in
theorem σIdx_letter (k : σIdx (W := W)) : ∃ m, letterAt W k.1 = .σ m := by
  have := k.2
  cases h : letterAt W k.1 with
  | l m d => rw [h] at this; simp [isCrossing] at this
  | r m => rw [h] at this; simp [isCrossing] at this
  | σ m => exact ⟨m, rfl⟩

/-- The column of a crossing. -/
def colOfCrossing (x : (realizeAt pl hW hne).Γ.Crossing) : σIdx (W := W) :=
  ⟨⟨colOf (slotOf pl hW hne ((realizeAt pl hW hne).strandA x)), (piece_spec pl hW _).1⟩, by
    obtain ⟨-, m, hℓ, -⟩ := crossing_char pl hW hne x ((realizeAt pl hW hne).strandA_mem x)
      ((realizeAt pl hW hne).strandB_mem x) ((realizeAt pl hW hne).strandB_ne_strandA x).symm
    rw [hℓ]; rfl⟩

/-- The crossing of a `σ` letter, indexed. -/
def crossingOfIdx (k : σIdx (W := W)) : (realizeAt pl hW hne).Γ.Crossing :=
  crossingOf pl hW hne k.1.2 (Classical.choose_spec (σIdx_letter k))

theorem slot_mem_crossingOf {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    {s : (realizeAt pl hW hne).Γ.Strand} (hs : s ∈ (crossingOf pl hW hne hk hℓ).val) :
    slotOf pl hW hne s = σSlotA hW hk hℓ ∨ slotOf pl hW hne s = σSlotB hW hk hℓ := by
  rw [crossingOf_val] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · left; exact slotOf_strandOfSlot pl hW hne _
  · right; exact slotOf_strandOfSlot pl hW hne _

theorem colOfCrossing_crossingOfIdx (k : σIdx (W := W)) : colOfCrossing pl hW hne (crossingOfIdx pl hW hne k) = k := by
  apply Subtype.ext
  apply Fin.ext
  show colOf (slotOf pl hW hne ((realizeAt pl hW hne).strandA (crossingOfIdx pl hW hne k))) = k.1
  have hmem := (realizeAt pl hW hne).strandA_mem (crossingOfIdx pl hW hne k)
  unfold crossingOfIdx at hmem ⊢
  rcases slot_mem_crossingOf pl hW hne _ _ hmem with h | h
  · rw [h]; exact (σSlotA_spec hW _ _).1
  · rw [h]; exact (σSlotB_spec hW _ _).1

theorem crossingOfIdx_colOfCrossing (x : (realizeAt pl hW hne).Γ.Crossing) :
    crossingOfIdx pl hW hne (colOfCrossing pl hW hne x) = x := by
  apply Subtype.ext
  have hx : x.val = {(realizeAt pl hW hne).strandA x, (realizeAt pl hW hne).strandB x} :=
    (realizeAt pl hW hne).Γ.eq_pair_other x ((realizeAt pl hW hne).strandA_mem x)
  obtain ⟨hcol, m, hℓ, hS⟩ := crossing_char pl hW hne x ((realizeAt pl hW hne).strandA_mem x)
    ((realizeAt pl hW hne).strandB_mem x) ((realizeAt pl hW hne).strandB_ne_strandA x).symm
  unfold crossingOfIdx
  have hk1 : ((colOfCrossing pl hW hne x).1 : ℕ) =
      colOf (slotOf pl hW hne ((realizeAt pl hW hne).strandA x)) := rfl
  have hℓ' : letterAt W (colOfCrossing pl hW hne x).1 =
      .σ (Classical.choose (σIdx_letter (colOfCrossing pl hW hne x))) :=
    Classical.choose_spec (σIdx_letter (colOfCrossing pl hW hne x))
  have hmm : Classical.choose (σIdx_letter (colOfCrossing pl hW hne x)) = m := by
    have h2 : letterAt W (colOfCrossing pl hW hne x).1 = .σ m := by rw [hk1]; exact hℓ
    exact Letter.σ.inj (hℓ'.symm.trans h2)
  have hA := σSlotA_spec hW (colOfCrossing pl hW hne x).1.2 hℓ'
  have hB := σSlotB_spec hW (colOfCrossing pl hW hne x).1.2 hℓ'
  rw [crossingOf_val, hx]
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := slot_eq_of_piece_eq hW pl (hA.1.trans hk1) (hA.2.1.trans (by rw [hmm, h1]))
    have e2 := slot_eq_of_piece_eq hW pl (hB.1.trans (hk1.trans hcol)) (hB.2.1.trans (by rw [hmm, h2]))
    rw [e1, e2, strandOfSlot_slotOf, strandOfSlot_slotOf]
  · have e1 := slot_eq_of_piece_eq hW pl (hA.1.trans (hk1.trans hcol)) (hA.2.1.trans (by rw [hmm, h2]))
    have e2 := slot_eq_of_piece_eq hW pl (hB.1.trans hk1) (hB.2.1.trans (by rw [hmm, h1]))
    rw [e1, e2, strandOfSlot_slotOf, strandOfSlot_slotOf, Finset.pair_comm]

/-- The crossings of the realization are the `σ` letters. -/
def crossingEquiv : (realizeAt pl hW hne).Γ.Crossing ≃ σIdx (W := W) where
  toFun := colOfCrossing pl hW hne
  invFun := crossingOfIdx pl hW hne
  left_inv := crossingOfIdx_colOfCrossing pl hW hne
  right_inv := colOfCrossing_crossingOfIdx pl hW hne

theorem crossingEquiv_symm_apply (k : σIdx (W := W)) :
    (crossingEquiv pl hW hne).symm k = crossingOfIdx pl hW hne k := rfl

/-- The double point of the crossing of `σ_m` at column `k` is the centre of the column. -/
theorem crossingPoint_crossingOf {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    (realizeAt pl hW hne).Γ.crossingPoint (crossingOf pl hW hne hk hℓ) = (pl.mid k, -(m : ℝ) - 1 / 2) := by
  symm
  apply (realizeAt pl hW hne).generic.common_point_unique
  intro u hu
  rcases slot_mem_crossingOf pl hW hne hk hℓ hu with h | h
  · rw [mem_seg_iff', h]
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    obtain ⟨hc, hs, -⟩ := σSlotA_spec hW hk hℓ
    unfold piecePt
    rw [hc, hs, Shape.par_pass]
    simp [Placement.A, Placement.mid]; constructor <;> push_cast <;> ring
  · rw [mem_seg_iff', h]
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    obtain ⟨hc, hs, -⟩ := σSlotB_spec hW hk hℓ
    unfold piecePt
    rw [hc, hs, Shape.par_pass]
    simp [Placement.A, Placement.mid]; constructor <;> push_cast <;> ring

/-- The slope of the strand descending from position `m` to `m+1` is negative, that of the ascending
strand positive: the descending strand is over ("smaller dz/dx"). -/
theorem slope_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    (realizeAt pl hW hne).slope (strandOfSlot pl hW hne (σSlotA hW hk hℓ)) = -1 / pl.w k ∧
    (realizeAt pl hW hne).slope (strandOfSlot pl hW hne (σSlotB hW hk hℓ)) = 1 / pl.w k := by
  obtain ⟨hcA, hsA, -⟩ := σSlotA_spec hW hk hℓ
  obtain ⟨hcB, hsB, -⟩ := σSlotB_spec hW hk hℓ
  have hw := (pl.w_pos k).ne'
  unfold PLFront.slope
  rw [dir_eq', dir_eq', slotOf_strandOfSlot, slotOf_strandOfSlot, dir_slot_eq, dir_slot_eq, hcA, hcB, hsA, hsB,
    Shape.vec_pass, Shape.vec_pass]
  constructor
  · cases xsign (σSlotA hW hk hℓ) <;> simp <;> push_cast <;> field_simp <;> ring
  · cases xsign (σSlotB hW hk hℓ) <;> simp <;> push_cast <;> field_simp <;> ring

theorem overStrand_crossingOf {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    (realizeAt pl hW hne).overStrand (crossingOf pl hW hne hk hℓ) = strandOfSlot pl hW hne (σSlotA hW hk hℓ) := by
  set x := crossingOf pl hW hne hk hℓ with hx
  have hmem := (realizeAt pl hW hne).overStrand_mem x
  rw [crossingOf_val] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact h
  · exfalso
    have hlt := (realizeAt pl hW hne).slope_overStrand_lt x
    have hunder : (realizeAt pl hW hne).diagram.underStrand x = strandOfSlot pl hW hne (σSlotA hW hk hℓ) := by
      refine ((realizeAt pl hW hne).diagram.eq_under_of_mem_of_ne x ?_ ?_).symm
      · show _ ∈ x.val
        rw [crossingOf_val]; exact Finset.mem_insert_self _ _
      · show _ ≠ (realizeAt pl hW hne).overStrand x
        rw [h]
        intro he
        exact σSlotA_ne_σSlotB hW hk hℓ (strandOfSlot_injective pl hW hne he)
    rw [h, hunder] at hlt
    obtain ⟨hA, hB⟩ := slope_σSlotA pl hW hne hk hℓ
    rw [hA, hB] at hlt
    have hw := pl.w_pos k
    rw [div_lt_div_iff_of_pos_right hw] at hlt
    linarith

/-- The sign of the crossing of `σ_m` at column `k`: positive iff the two bits at positions `m`, `m+1`
agree (the printed rule "both arrows pointing right … positive"). -/
theorem sign_crossingOf {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    ((realizeAt pl hW hne).diagram.sign (crossingOf pl hW hne hk hℓ) : ℤ) =
      if bit W k m = bit W k (m + 1) then 1 else -1 := by
  rw [PLFront.sign_eq_ite]
  have hunder : (realizeAt pl hW hne).diagram.underStrand (crossingOf pl hW hne hk hℓ) =
      strandOfSlot pl hW hne (σSlotB hW hk hℓ) := by
    refine ((realizeAt pl hW hne).diagram.eq_under_of_mem_of_ne (crossingOf pl hW hne hk hℓ) ?_ ?_).symm
    · show _ ∈ (crossingOf pl hW hne hk hℓ).val
      rw [crossingOf_val]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · show _ ≠ (realizeAt pl hW hne).overStrand (crossingOf pl hW hne hk hℓ)
      rw [overStrand_crossingOf]
      intro he
      exact σSlotA_ne_σSlotB hW hk hℓ (strandOfSlot_injective pl hW hne he).symm
  rw [overStrand_crossingOf, hunder, xdir_eq, xdir_eq, slotOf_strandOfSlot,
    slotOf_strandOfSlot, (σSlotA_spec hW hk hℓ).2.2, (σSlotB_spec hW hk hℓ).2.2]

/-- The sign of a crossing letter at its cut: `signBit`. -/
theorem signBit_σ {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    (Letter.σ m).signBit (cut W k) = if bit W k m = bit W k (m + 1) then 1 else -1 := by
  obtain ⟨hm, hlen, -, -, -⟩ := σ_facts hW hk hℓ
  have h1 : (cut W k).drop (m - 1) = (cut W k)[m - 1] :: (cut W k).drop (m - 1 + 1) :=
    List.drop_eq_getElem_cons (by omega)
  have h2 : (cut W k).drop (m - 1 + 1) = (cut W k)[m - 1 + 1] :: (cut W k).drop (m - 1 + 1 + 1) :=
    List.drop_eq_getElem_cons (by omega)
  have e1 : (cut W k)[m - 1] = bit W k m := (bit_eq_getElem (by omega)).symm
  have e2 : (cut W k)[m - 1 + 1] = bit W k (m + 1) := by
    rw [bit_eq, List.getD_eq_getElem?_getD, show m + 1 - 1 = m - 1 + 1 by omega,
      List.getElem?_eq_getElem (by omega)]; rfl
  simp only [signBit]
  rw [h1, h2, e1, e2]

theorem sign_crossingOf_eq_signBit {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    ((realizeAt pl hW hne).diagram.sign (crossingOf pl hW hne hk hℓ) : ℤ) = (letterAt W k).signBit (cut W k) := by
  rw [sign_crossingOf, hℓ, signBit_σ hW hk hℓ]

theorem sign_crossingOfIdx (k : σIdx (W := W)) :
    ((realizeAt pl hW hne).diagram.sign (crossingOfIdx pl hW hne k) : ℤ) = (letterAt W k.1).signBit (cut W k.1) :=
  sign_crossingOf_eq_signBit pl hW hne k.1.2 (Classical.choose_spec (σIdx_letter k))

/-! ### The counts -/

/-- The cusp letters (as column indices). -/
abbrev cuspIdx : Type := {k : Fin W.length // (letterAt W k).isCrossing = false}

omit hW in
theorem isSlot_cuspIdx (k : cuspIdx (W := W)) : IsSlot W (k.1, 0) := Or.inl ⟨rfl, k.1.2, k.2⟩

/-- The cusp vertices are the cusp letters. -/
def cuspSlotEquiv : {u : Slot W // u.1.2 = 0} ≃ cuspIdx (W := W) where
  toFun u := ⟨⟨u.1.1.1, by
      have := u.1.2; rcases this with ⟨-, hk, -⟩ | ⟨h, -, -⟩
      · exact hk
      · have := u.2; omega⟩, by
      have := u.1.2; rcases this with ⟨-, -, hσ⟩ | ⟨h, -, -⟩
      · exact hσ
      · have := u.2; omega⟩
  invFun k := ⟨⟨(k.1, 0), isSlot_cuspIdx k⟩, rfl⟩
  left_inv u := by
    apply Subtype.ext; apply Subtype.ext
    have := u.2
    exact Prod.ext rfl this.symm
  right_inv k := by
    apply Subtype.ext; apply Fin.ext; rfl

/-- The cusp strands are the cusp letters. -/
def cuspStrandEquiv : {s : (realizeAt pl hW hne).Γ.Strand // (realizeAt pl hW hne).IsCusp s} ≃ cuspIdx (W := W) :=
  ((strandEquiv pl hW hne).subtypeEquiv (fun s => isCusp_iff pl hW hne s)).trans cuspSlotEquiv

omit hW in
/-- Counting the positions of a list where a Boolean predicate holds. -/
theorem card_fin_filter {α : Type*} (p : α → Bool) :
    ∀ L : List α, Fintype.card {i : Fin L.length // p L[i] = true} = L.countP p
  | [] => by simp
  | a :: L => by
    rw [List.countP_cons, ← card_fin_filter p L, Fintype.card_subtype, Fintype.card_subtype,
      Finset.card_filter, Finset.card_filter]
    show ∑ i : Fin (L.length + 1), (if p (a :: L)[i] = true then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    exact Nat.add_comm _ _

omit hW in
theorem card_cuspIdx : Fintype.card (cuspIdx (W := W)) = W.cuspCount := by
  unfold cuspIdx Word.cuspCount
  have : ∀ i : Fin W.length, ((letterAt W i).isCrossing = false) ↔ ((!(W[i]).isCrossing) = true) := by
    intro i; rw [letterAt_eq W i.2]; show (W[i.1]).isCrossing = false ↔ _; cases (W[i.1]).isCrossing <;> simp
  rw [Fintype.card_congr (Equiv.subtypeEquivRight this)]
  exact card_fin_filter (fun ℓ => !ℓ.isCrossing) W

omit hW in
theorem card_σIdx : Fintype.card (σIdx (W := W)) = W.crossingCount := by
  unfold σIdx Word.crossingCount
  have : ∀ i : Fin W.length, ((letterAt W i).isCrossing = true) ↔ ((W[i]).isCrossing = true) := by
    intro i; rw [letterAt_eq W i.2]; rfl
  rw [Fintype.card_congr (Equiv.subtypeEquivRight this)]
  exact card_fin_filter (fun ℓ => ℓ.isCrossing) W

theorem crossingCount_eq : (realizeAt pl hW hne).crossingCount = W.crossingCount := by
  unfold PLFront.crossingCount
  rw [Fintype.card_congr (crossingEquiv pl hW hne), card_σIdx]

theorem cuspCount_eq : (realizeAt pl hW hne).cuspCount = W.cuspCount := by
  unfold PLFront.cuspCount
  rw [Nat.card_congr (cuspStrandEquiv pl hW hne), Nat.card_eq_fintype_card, card_cuspIdx]

/-- `s(F) = s(W)`: every letter is one singularity. -/
theorem sCount_eq : (realizeAt pl hW hne).sCount = W.sCount := by
  unfold PLFront.sCount Word.sCount
  rw [crossingCount_eq, cuspCount_eq]

/-! ### Letter tracing: `D` and `w` -/

omit hW in
/-- The letter-traced down count of a typed word is the sum of the letters' down bits at their cuts. -/
theorem downCountFrom_eq_sum : ∀ (V : Word) (c : Cuts), (∃ c', Word.run V c = some c') →
    V.downCountFrom c = ∑ i : Fin V.length, (V[i]).downBit ((Word.run (V.take i) c).getD [])
  | [], c, _ => by simp [Word.downCountFrom]
  | a :: V, c, ⟨c', h⟩ => by
    rw [Word.run_cons] at h
    obtain ⟨c₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have ih := downCountFrom_eq_sum V c₁ ⟨c', h2⟩
    simp only [Word.downCountFrom, h1]
    show _ = ∑ i : Fin (V.length + 1), (a :: V)[i].downBit ((Word.run (List.take (↑i) (a :: V)) c).getD [])
    rw [Fin.sum_univ_succ, ih]
    simp only [Fin.getElem_fin, Fin.val_zero, List.take_zero, Word.run_nil, Option.getD_some,
      List.getElem_cons_zero, Fin.val_succ, List.take_succ_cons, Word.run_cons, h1, Option.bind_some,
      List.getElem_cons_succ]

omit hW in
/-- The letter-traced writhe of a typed word is the sum of the letters' sign bits at their cuts. -/
theorem writheFrom_eq_sum : ∀ (V : Word) (c : Cuts), (∃ c', Word.run V c = some c') →
    V.writheFrom c = ∑ i : Fin V.length, (V[i]).signBit ((Word.run (V.take i) c).getD [])
  | [], c, _ => by simp [Word.writheFrom]
  | a :: V, c, ⟨c', h⟩ => by
    rw [Word.run_cons] at h
    obtain ⟨c₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have ih := writheFrom_eq_sum V c₁ ⟨c', h2⟩
    simp only [Word.writheFrom, h1]
    show _ = ∑ i : Fin (V.length + 1), (a :: V)[i].signBit ((Word.run (List.take (↑i) (a :: V)) c).getD [])
    rw [Fin.sum_univ_succ, ih]
    simp only [Fin.getElem_fin, Fin.val_zero, List.take_zero, Word.run_nil, Option.getD_some,
      List.getElem_cons_zero, Fin.val_succ, List.take_succ_cons, Word.run_cons, h1, Option.bind_some,
      List.getElem_cons_succ]

theorem downCountFrom_nil_eq_sum : W.downCountFrom [] = ∑ i : Fin W.length, (letterAt W i).downBit (cut W i) := by
  rw [downCountFrom_eq_sum W [] ⟨[], hW⟩]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [letterAt_eq W i.2]; rfl

theorem writheFrom_nil_eq_sum : W.writheFrom [] = ∑ i : Fin W.length, (letterAt W i).signBit (cut W i) := by
  rw [writheFrom_eq_sum W [] ⟨[], hW⟩]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [letterAt_eq W i.2]; rfl

omit hW in
/-- A down bit is `0` or `1`, and `0` at a crossing letter. -/
theorem downBit_eq_ite (ℓ : Letter) (c : Cuts) :
    ℓ.downBit c = if ℓ.isCrossing = false ∧ ℓ.downBit c = 1 then 1 else 0 := by
  cases ℓ with
  | l m d => cases d <;> simp [downBit, isCrossing]
  | r m =>
    simp only [downBit, isCrossing, true_and]
    split <;> simp_all
  | σ m => simp [downBit, isCrossing]

omit hW in
/-- A sign bit vanishes at a cusp letter. -/
theorem signBit_eq_zero_of_cusp {ℓ : Letter} (h : ℓ.isCrossing = false) (c : Cuts) : ℓ.signBit c = 0 := by
  cases ℓ <;> simp_all [signBit, isCrossing]

/-- `D(F)`: the downward cusps are the cusp letters with down bit `1`. -/
theorem downCount_eq : (realizeAt pl hW hne).downCount = W.downCountFrom [] := by
  unfold PLFront.downCount
  rw [downCountFrom_nil_eq_sum hW]
  have e : {s : (realizeAt pl hW hne).Γ.Strand // (realizeAt pl hW hne).IsDownCusp s} ≃
      {k : Fin W.length // (letterAt W k).isCrossing = false ∧ (letterAt W k).downBit (cut W k) = 1} :=
    ((strandEquiv pl hW hne).subtypeEquiv
      (q := fun u : Slot W => u.1.2 = 0 ∧ (letterAt W u.1.1).downBit (cut W u.1.1) = 1)
      (fun s => isDownCusp_iff pl hW hne s)).trans
    (((Equiv.subtypeSubtypeEquivSubtypeInter (fun u : Slot W => u.1.2 = 0)
      (fun u : Slot W => (letterAt W u.1.1).downBit (cut W u.1.1) = 1)).symm).trans
    (((cuspSlotEquiv (W := W)).subtypeEquiv
      (q := fun k : cuspIdx (W := W) => (letterAt W k.1).downBit (cut W k.1) = 1) (fun u => Iff.rfl)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun k : Fin W.length => (letterAt W k).isCrossing = false)
      (fun k : Fin W.length => (letterAt W k).downBit (cut W k) = 1))))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (downBit_eq_ite _ _).symm

/-- `w(F)`: the writhe is the sum of the sign bits of the crossing letters at their cuts. -/
theorem writhe_eq : (realizeAt pl hW hne).writhe = W.writheFrom [] := by
  rw [PLFront.writhe_eq_sum, writheFrom_nil_eq_sum hW]
  have h1 : ∑ x : (realizeAt pl hW hne).Γ.Crossing, ((realizeAt pl hW hne).diagram.sign x : ℤ) =
      ∑ k : σIdx (W := W), ((realizeAt pl hW hne).diagram.sign (crossingOfIdx pl hW hne k) : ℤ) :=
    (Fintype.sum_equiv (crossingEquiv pl hW hne).symm _ _ (fun k => rfl)).symm
  have h2 : ∑ k : σIdx (W := W), ((realizeAt pl hW hne).diagram.sign (crossingOfIdx pl hW hne k) : ℤ) =
      ∑ k : σIdx (W := W), (letterAt W k.1).signBit (cut W k.1) :=
    Finset.sum_congr rfl (fun k _ => sign_crossingOfIdx pl hW hne k)
  rw [h1, h2]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun k : Fin W.length => (letterAt W k).isCrossing = true))
    (by simp) (fun k => (letterAt W k).signBit (cut W k)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · exact (signBit_eq_zero_of_cusp (by simpa using h) _).symm

end Corr

end

end SM.FrontRealize

/-! ## 5. The correspondence for `SM.realize` (FINAL §4; β1 report §5 items 1-2) -/

namespace SM

open SM.FrontWord SM.FrontRealize

section Realize

variable (W : OWord)

/-- `s(realize W) = s(W)`: every letter is one singularity (nonempty words). -/
theorem realize_sCount (h : W.letters ≠ []) : (realize W).sCount = W.sCountSyn := by
  rw [realize_eq_realizeAt W h]; exact sCount_eq _ _ _

theorem realize_crossingCount (h : W.letters ≠ []) : (realize W).crossingCount = W.letters.crossingCount := by
  rw [realize_eq_realizeAt W h]; exact crossingCount_eq _ _ _

theorem realize_cuspCount (h : W.letters ≠ []) : (realize W).cuspCount = W.letters.cuspCount := by
  rw [realize_eq_realizeAt W h]; exact cuspCount_eq _ _ _

/-- `D(realize W)` is the letter-traced down count. -/
theorem realize_downCount (h : W.letters ≠ []) : (realize W).downCount = W.downCountSyn := by
  rw [realize_eq_realizeAt W h]; exact downCount_eq _ _ _

/-- `w(realize W)` is the letter-traced writhe. -/
theorem realize_writhe (h : W.letters ≠ []) : (realize W).writhe = W.writheSyn := by
  rw [realize_eq_realizeAt W h]; exact writhe_eq _ _ _

/-- The realization of the empty word is the standard circle: `s = 2`. -/
theorem realize_nil_sCount (h : W.letters = []) : (realize W).sCount = 2 := by
  rw [realize_nil W h]
  have := sCount_eq .std stdCircleWord.closed stdCircleWord_ne_nil
  rw [this]; decide

/-! ### The word moves with the geometric readings (FINAL §4 `wordMoves`) -/

/-- FINAL §4: the moves of ng:finite-word on closed oriented words, with `s`, `B` and the base read on the
realization. -/
noncomputable def wordMoves : Moves :=
  wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect) (fun W => (realize W).IsStandardCircles)

/-- The shape of the literature input ng:finite-word on `wordMoves` (the axiom itself is declared in the
statement unit, policy name `SM.ng_finite_word`). -/
def ng_finite_word_statement : Prop := FiniteWordStatement wordMoves

theorem wordMoves_s (W : OWord) : wordMoves.s W = (realize W).sCount := rfl
theorem wordMoves_B (W : OWord) : wordMoves.B W = (realize W).defect := rfl
theorem wordMoves_Base (W : OWord) : wordMoves.Base W ↔ (realize W).IsStandardCircles := Iff.rfl
theorem wordMoves_Pres (W W' : OWord) : wordMoves.Pres W W' ↔ Pres W W' := Iff.rfl
theorem wordMoves_Del (W W' : OWord) : wordMoves.Del W W' ↔ Del W W' := Iff.rfl
theorem wordMoves_Skein (A A' C : OWord) : wordMoves.Skein A A' C ↔ Skein A A' C := Iff.rfl

/-- The geometric `s` of a closed word: its length for nonempty words, `2` for the empty word. -/
theorem realize_sCount_eq_ite (W : OWord) :
    (realize W).sCount = if W.letters = [] then 2 else W.letters.length := by
  split_ifs with h
  · exact realize_nil_sCount W h
  · rw [realize_sCount W h, OWord.sCountSyn, Word.sCount_eq_length]

/-- An empty zigzag is never the whole of a closed word (the two-letter words `l_m r_{m+1}`, `l_{m+1} r_m`
are not typed from the empty cut). -/
theorem IsZigzagDeletion.ne_nil {W W' : Word} (h : IsZigzagDeletion W W') (hW : W.Closed) : W' ≠ [] := by
  obtain ⟨X, Y, m, d, hm, hpat, rfl⟩ := h
  intro hXY
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hXY
  rcases hpat with rfl | rfl
  · simp only [List.nil_append, List.append_nil] at hW
    obtain ⟨c₁, h1, -⟩ := run_two_iff.1 hW
    obtain ⟨A, L, L', -, hA, hAL, -, -⟩ := Letter.step_eq_some_iff.1 h1
    have hA0 : A = [] := (List.append_eq_nil_iff.1 hAL.symm).1
    simp only [Letter.idx] at hA
    rw [hA0] at hA
    have : m = 1 := by simp at hA; omega
    subst this
    cases d <;> exact absurd hW (by decide)
  · simp only [List.nil_append, List.append_nil] at hW
    obtain ⟨c₁, h1, -⟩ := run_two_iff.1 hW
    obtain ⟨A, L, L', -, hA, hAL, -, -⟩ := Letter.step_eq_some_iff.1 h1
    have hA0 : A = [] := (List.append_eq_nil_iff.1 hAL.symm).1
    simp only [Letter.idx] at hA
    rw [hA0] at hA
    simp at hA; omega

/-- No move starts from the empty word. -/
theorem Pres.source_ne_nil {F F' : OWord} (h : Pres F F') : F.letters ≠ [] := by
  rcases h with (h | h) | h | h | h
  · obtain ⟨X, Y, a, b, hF, -⟩ := h; rw [hF]; simp
  · obtain ⟨X, Y, a, b, -, hpat⟩ := h; rcases hpat with ⟨-, hF⟩ | ⟨-, hF⟩ <;> rw [hF] <;> simp
  · obtain ⟨X, Y, m, d, hpat, -⟩ := h; rcases hpat with ⟨-, hF⟩ | ⟨-, hF⟩ <;> rw [hF] <;> simp
  · obtain ⟨X, Y, m, hpat⟩ := h
    rcases hpat with ⟨d, -, hF, -⟩ | ⟨d, -, hF, -⟩ | ⟨-, hF, -⟩ | ⟨-, hF, -⟩ <;> rw [hF] <;> simp
  · obtain ⟨X, Y, m, -, hpat⟩ := h; rcases hpat with ⟨hF, -⟩ | ⟨hF, -⟩ <;> rw [hF] <;> simp

/-- A `B`-preserving move onto the empty word (only a type-I deletion can) starts from a word of at least
two letters. -/
theorem Pres.two_le_of_target_nil {F F' : OWord} (h : Pres F F') (h1 : F'.letters = []) :
    2 ≤ F.letters.length := by
  rcases h with (h | h) | h | h | h
  · obtain ⟨X, Y, a, b, -, hpat⟩ := h
    rcases hpat with ⟨-, hF'⟩ | ⟨-, hF'⟩ <;> rw [hF'] at h1 <;> simp at h1
  · obtain ⟨X, Y, a, b, hF', -⟩ := h; rw [hF'] at h1; simp at h1
  · obtain ⟨X, Y, m, d, hpat, -⟩ := h
    rcases hpat with ⟨-, hF⟩ | ⟨-, hF⟩ <;> rw [hF] <;> simp <;> omega
  · obtain ⟨X, Y, m, hpat⟩ := h
    rcases hpat with ⟨d, -, -, hF'⟩ | ⟨d, -, -, hF'⟩ | ⟨-, -, hF'⟩ | ⟨-, -, hF'⟩ <;> rw [hF'] at h1 <;> simp at h1
  · obtain ⟨X, Y, m, -, hpat⟩ := h
    rcases hpat with ⟨-, hF'⟩ | ⟨-, hF'⟩ <;> rw [hF'] at h1 <;> simp at h1

/-- The `s`-clauses of the laws for `wordMoves` (β1's `laws_s_of_syn` needed `s = sCountSyn` everywhere;
here the empty word is handled separately: it is isolated under every move). -/
theorem wordMoves_pres_s (F F' : OWord) (h : wordMoves.Pres F F') : wordMoves.s F' ≤ wordMoves.s F := by
  rw [wordMoves_s, wordMoves_s, realize_sCount_eq_ite, realize_sCount_eq_ite]
  have hsyn := Pres.sCountSyn_le h
  unfold OWord.sCountSyn at hsyn
  rw [Word.sCount_eq_length, Word.sCount_eq_length] at hsyn
  rw [ite_eq_right (Pres.source_ne_nil h)]
  by_cases h1 : F'.letters = []
  · rw [ite_eq_left h1]; exact Pres.two_le_of_target_nil h h1
  · rw [ite_eq_right h1]; exact hsyn

theorem wordMoves_del_s (F F' : OWord) (h : wordMoves.Del F F') : wordMoves.s F' < wordMoves.s F := by
  rw [wordMoves_s, wordMoves_s, realize_sCount_eq_ite, realize_sCount_eq_ite]
  have hsyn := Del.sCountSyn_lt h
  unfold OWord.sCountSyn at hsyn
  rw [Word.sCount_eq_length, Word.sCount_eq_length] at hsyn
  have hF' : F'.letters ≠ [] := by
    rcases h with h | h | h
    · exact IsZigzagDeletion.ne_nil h F.closed
    · obtain ⟨X, Y, i, -, hpat⟩ := h
      rcases hpat with ⟨d, -, hF'⟩ | ⟨-, hF'⟩ <;> rw [hF'] <;> simp
    · obtain ⟨X, Y, m, d, -, -, hF', hne⟩ := h
      rw [hF']; exact hne
  have hF : F.letters ≠ [] := by
    intro hF
    rw [hF] at hsyn; simp at hsyn
  rw [ite_eq_right hF', ite_eq_right hF]
  exact hsyn

theorem wordMoves_skein_s (A A' C : OWord) (h : wordMoves.Skein A A' C) :
    wordMoves.s A' = wordMoves.s A ∧ wordMoves.s C < wordMoves.s A := by
  rw [wordMoves_s, wordMoves_s, wordMoves_s, realize_sCount_eq_ite, realize_sCount_eq_ite, realize_sCount_eq_ite]
  obtain ⟨h1, h2⟩ := Skein.sCountSyn h
  unfold OWord.sCountSyn at h1 h2
  rw [Word.sCount_eq_length, Word.sCount_eq_length] at h1 h2
  have hne : A.letters ≠ [] ∧ A'.letters ≠ [] ∧ C.letters ≠ [] := by
    rcases h with h | h <;> obtain ⟨X, Y, m, d, a, P, L, -, -, -, hA, hA', hC⟩ := h <;>
      refine ⟨?_, ?_, ?_⟩ <;>
      first
      | (rw [hA]; simp)
      | (rw [hA']; simp)
      | (rcases hC with ⟨-, hC⟩ | ⟨-, hC⟩ <;> rw [hC] <;> simp)
  rw [ite_eq_right hne.1, ite_eq_right hne.2.1, ite_eq_right hne.2.2]
  exact ⟨h1, h2⟩

end Realize

end SM
