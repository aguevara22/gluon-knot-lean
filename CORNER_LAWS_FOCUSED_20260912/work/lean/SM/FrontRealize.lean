import SM.FrontRealizeSlots


/-! Ported 2026-09-14 05:50Z from work/drafts/front/FrontRealize.lean (front lane β2, grid realization of front words; report work/drafts/front/BETA2_REPORT.md). Library module (not a row): the PL realization `SM.realize : OWord → PLFront` and its correspondence with the word layer. Only this header added (one prose word reworded). -/
/-! Front block, lane β, unit β2 (2026-09-14): module `SM/FrontRealize.lean` (intended home).
Adopted design work/reports/front-block-design-FINAL-20260913.md (§2 G1, §4 `realize`, §7, §9 FR-5);
β1 report work/drafts/front/BETA1_REPORT.md §5.

# The grid realization, part 2: the geometry, `realize : OWord → PLFront`

The slots of `SM/FrontRealizeSlots.lean` are placed in the plane by a *placement* `pl` (a strictly
increasing sequence of column boundaries `pl.x k`; the standard placement is `pl.x k = k`):
* the cut slot `(k, p)` at `(pl.x k, −p)` — position `p` of cut `k` at integer height `−p`, the top strand
  highest;
* the cusp vertex `(k, 0)` of the cusp letter `ℓ_k` with index `m` at the middle of its column,
  `(pl.x k + w_k / 2, −(m + 1/2))`, between the heights of the two cut positions `m`, `m+1` its arms join.

Every edge of the realization is the segment from a slot to its successor.  Normalized to the unit
column, an edge has one of three SHAPES: a *pass* `(0, −p) — (1, −q)` of a strand crossing the column
from position `p` to position `q = posR p` (horizontal above the letter, sloped below it by the letter's
strand-count change, the two strands of `σ_m` exchanging heights and crossing at `(1/2, −(m + 1/2))`),
a left-cusp *arm* `(1/2, −(m + 1/2)) — (1, −j)`, `j ∈ {m, m+1}`, or a right-cusp arm
`(0, −j) — (1/2, −(m + 1/2))`.  Pieces of one column are disjoint except the two arms of a cusp (meeting
at the cusp vertex) and the two strands of a crossing letter (meeting once, transversally, in their
interiors); pieces of adjacent columns meet only at common cut slots.  This gives `Shadow.Generic`, and
every edge is nonvertical, so the realization is a `PLFront`.

Conventions (FR-5: the realization is a proof device; every convention documented):
* over strand = smaller slope (`PLFront.diagram`): at `σ_m` the strand descending from position `m` to
  `m+1` (slope `−1/w_k`) is over — the printed "smaller dz/dx" rule, not a convention of ours;
* the empty word (closed, isolated under every move) is sent to the standard circle `l₁ r₁` so that
  `realize` is total on `OWord`; every correspondence lemma is stated for nonempty words;
* `realizeAt pl` for an arbitrary placement is provided for the move rows (two words differing in one
  factor are realized with the factor blocks in the same rectangle, `SM/FrontRealizeGeometry.lean`).

All declarations live in `SM.FrontRealize` (`SM.realize` at top level).  Checked with `lake env lean`
(placeholder-free, standard axioms). -/

namespace SM.FrontRealize

open SM SM.Link SM.FrontWord SM.FrontWord.Letter

noncomputable section

/-! ## 1. Placements: column boundaries -/

/-- A *placement* of the columns: strictly increasing boundaries `x 0 < x 1 < …`; column `k` is the
strip `[x k, x (k+1)]`. -/
structure Placement where
  x : ℕ → ℝ
  strictMono : StrictMono x

namespace Placement

/-- the standard placement `x k = k` -/
def std : Placement := ⟨fun k => (k : ℝ), Nat.strictMono_cast⟩

@[simp] theorem std_x (k : ℕ) : std.x k = k := rfl

variable (pl : Placement)

/-- the width of column `k` -/
def w (k : ℕ) : ℝ := pl.x (k + 1) - pl.x k

theorem w_pos (k : ℕ) : 0 < pl.w k := sub_pos.2 (pl.strictMono (Nat.lt_succ_self k))

theorem x_add_w (k : ℕ) : pl.x k + pl.w k = pl.x (k + 1) := by unfold w; ring

/-- the midpoint of column `k` (the x-coordinate of its cusp vertex) -/
def mid (k : ℕ) : ℝ := pl.x k + pl.w k / 2

theorem x_lt_mid (k : ℕ) : pl.x k < pl.mid k := by unfold mid; linarith [pl.w_pos k]

theorem mid_lt_x_succ (k : ℕ) : pl.mid k < pl.x (k + 1) := by
  unfold mid; rw [← pl.x_add_w k]; linarith [pl.w_pos k]

theorem x_le_x_iff {a b : ℕ} : pl.x a ≤ pl.x b ↔ a ≤ b := pl.strictMono.le_iff_le
theorem x_lt_x_iff {a b : ℕ} : pl.x a < pl.x b ↔ a < b := pl.strictMono.lt_iff_lt
theorem x_injective : Function.Injective pl.x := pl.strictMono.injective

/-- The affine map of the unit column onto column `k`: `(u, z) ↦ (x k + w k · u, z)`. -/
def A (k : ℕ) (q : Plane) : Plane := (pl.x k + pl.w k * q.1, q.2)

@[simp] theorem A_fst (k : ℕ) (q : Plane) : (pl.A k q).1 = pl.x k + pl.w k * q.1 := rfl
@[simp] theorem A_snd (k : ℕ) (q : Plane) : (pl.A k q).2 = q.2 := rfl

theorem A_injective (k : ℕ) : Function.Injective (pl.A k) := by
  intro q q' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [A_fst, A_snd] at h1 h2
  have hw := pl.w_pos k
  exact Prod.ext (by nlinarith) h2

theorem A_zero_fst (k : ℕ) (z : ℝ) : pl.A k (0, z) = (pl.x k, z) := by simp [A]
theorem A_one_fst (k : ℕ) (z : ℝ) : pl.A k (1, z) = (pl.x (k + 1), z) := by
  simp [A, x_add_w]
theorem A_half_fst (k : ℕ) (z : ℝ) : pl.A k (1 / 2, z) = (pl.mid k, z) := by
  simp [A, mid]; ring

/-- The x-coordinates of column `k` are the strip `[x k, x (k+1)]`. -/
theorem A_fst_mem {k : ℕ} {q : Plane} (h0 : 0 ≤ q.1) (h1 : q.1 ≤ 1) :
    pl.x k ≤ (pl.A k q).1 ∧ (pl.A k q).1 ≤ pl.x (k + 1) := by
  have hw := pl.w_pos k
  simp only [A_fst]
  constructor
  · nlinarith
  · rw [← pl.x_add_w k]; nlinarith

/-- A sum `x k + w k · u` with `u ∈ [0, 1]` equal to a boundary `x j` forces `j ∈ {k, k+1}` with `u` the
corresponding end. -/
theorem A_fst_eq_x {k j : ℕ} {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) (h : pl.x k + pl.w k * u = pl.x j) :
    (j = k ∧ u = 0) ∨ (j = k + 1 ∧ u = 1) := by
  have hw := pl.w_pos k
  have hle : pl.x k ≤ pl.x j := by rw [← h]; nlinarith
  have hge : pl.x j ≤ pl.x (k + 1) := by rw [← h, ← pl.x_add_w k]; nlinarith
  rw [pl.x_le_x_iff] at hle hge
  rcases Nat.eq_or_lt_of_le hle with hjk | hjk
  · left
    refine ⟨hjk.symm, ?_⟩
    subst hjk
    have : pl.w k * u = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · right
    have hjk' : j = k + 1 := by omega
    refine ⟨hjk', ?_⟩
    subst hjk'
    rw [← pl.x_add_w k] at h
    have : pl.w k * u = pl.w k := by linarith
    have : pl.w k * (u - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith

/-- A sum `x k + w k · u` with `u ∈ [0, 1]` equal to a midpoint `mid j` forces `j = k`, `u = 1/2`. -/
theorem A_fst_eq_mid {k j : ℕ} {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) (h : pl.x k + pl.w k * u = pl.mid j) :
    j = k ∧ u = 1 / 2 := by
  have hw := pl.w_pos k
  have hle : pl.x k ≤ pl.mid j := by rw [← h]; nlinarith
  have hge : pl.mid j ≤ pl.x (k + 1) := by rw [← h, ← pl.x_add_w k]; nlinarith
  have h1' : k ≤ j := by
    by_contra hc
    rw [not_le] at hc
    have := pl.mid_lt_x_succ j
    have : pl.x (j + 1) ≤ pl.x k := (pl.x_le_x_iff).2 hc
    linarith
  have h2' : j ≤ k := by
    by_contra hc
    rw [not_le] at hc
    have := pl.x_lt_mid j
    have : pl.x (k + 1) ≤ pl.x j := (pl.x_le_x_iff).2 hc
    linarith
  have hjk : j = k := le_antisymm h2' h1'
  subst hjk
  refine ⟨rfl, ?_⟩
  unfold mid at h
  have : pl.w j * u = pl.w j * (1 / 2) := by linarith
  exact mul_left_cancel₀ hw.ne' this

end Placement

/-! ## 2. Grid points of the slots -/

variable (pl : Placement) (W : Word)

/-- The plane point of a slot: `(x k, −p)` at position `p ≥ 1` of cut `k`; the cusp vertex of column `k`
at `(mid k, −(m + 1/2))` with `m` the letter's index. -/
def pt (s : ℕ × ℕ) : Plane :=
  if s.2 = 0 then (pl.mid s.1, -((letterAt W s.1).idx : ℝ) - 1 / 2) else (pl.x s.1, -(s.2 : ℝ))

theorem pt_cut {k p : ℕ} (hp : p ≠ 0) : pt pl W (k, p) = (pl.x k, -(p : ℝ)) := by simp [pt, hp]

theorem pt_cusp (k : ℕ) : pt pl W (k, 0) = (pl.mid k, -((letterAt W k).idx : ℝ) - 1 / 2) := by simp [pt]

/-- `(a : ℝ) ≠ b + 1/2` for naturals `a`, `b`. -/
theorem nat_ne_add_half (a b : ℕ) : (a : ℝ) ≠ (b : ℝ) + 1 / 2 := by
  intro h
  have h3 : ((2 * a : ℕ) : ℝ) = ((2 * b + 1 : ℕ) : ℝ) := by push_cast; linarith
  have := Nat.cast_injective h3
  omega

/-- `-(a : ℝ) ≠ -b - 1/2` for naturals `a`, `b`. -/
theorem neg_nat_ne (a b : ℕ) : -(a : ℝ) ≠ -(b : ℝ) - 1 / 2 := by
  intro h
  exact nat_ne_add_half a b (by linarith)

/-- Distinct slots have distinct points. -/
theorem pt_injective : Function.Injective (fun s : Slot W => pt pl W s.1) := by
  rintro ⟨⟨k, p⟩, hs⟩ ⟨⟨k', p'⟩, hs'⟩ h
  simp only at h
  by_cases hp : p = 0 <;> by_cases hp' : p' = 0
  · subst hp hp'
    rw [pt_cusp, pt_cusp] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    have : k = k' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := pl.mid_lt_x_succ k
        have := pl.x_lt_mid k'
        have : pl.x (k + 1) ≤ pl.x k' := pl.x_le_x_iff.2 hlt
        linarith
      · have := pl.mid_lt_x_succ k'
        have := pl.x_lt_mid k
        have : pl.x (k' + 1) ≤ pl.x k := pl.x_le_x_iff.2 hlt
        linarith
    subst this; rfl
  · subst hp
    rw [pt_cusp, pt_cut pl W hp'] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    exfalso
    obtain ⟨-, h2⟩ := pl.A_fst_eq_mid (k := k') (u := 0) le_rfl zero_le_one (by rw [mul_zero, add_zero]; exact h1.symm)
    norm_num at h2
  · subst hp'
    rw [pt_cut pl W hp, pt_cusp] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    exfalso
    obtain ⟨-, h2⟩ := pl.A_fst_eq_mid (k := k) (u := 0) le_rfl zero_le_one (by rw [mul_zero, add_zero]; exact h1)
    norm_num at h2
  · rw [pt_cut pl W hp, pt_cut pl W hp'] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    have hk : k = k' := pl.x_injective h1
    have hp'' : p = p' := by exact_mod_cast (neg_inj.1 h2)
    subst hk hp''; rfl

theorem pt_inj {s t : Slot W} (h : pt pl W s.1 = pt pl W t.1) : s = t := pt_injective pl W h

/-! ## 3. The three shapes of a normalized edge -/

/-- The shape of an edge in the unit column: a strand *passing* the column from position `p` to `q`, a
left-cusp *arm* (`m` the letter's index, `j ∈ {m, m+1}` the position of its far end), or a right-cusp
arm. -/
inductive Shape
  | pass (p q : ℕ)
  | armL (m j : ℕ)
  | armR (m j : ℕ)
  deriving DecidableEq

namespace Shape

/-- the left endpoint (smaller x) of the normalized piece -/
def left : Shape → Plane
  | pass p _ => (0, -(p : ℝ))
  | armL m _ => (1 / 2, -(m : ℝ) - 1 / 2)
  | armR _ j => (0, -(j : ℝ))

/-- the right endpoint -/
def right : Shape → Plane
  | pass _ q => (1, -(q : ℝ))
  | armL _ j => (1, -(j : ℝ))
  | armR m _ => (1 / 2, -(m : ℝ) - 1 / 2)

/-- the point of the normalized piece at parameter `t ∈ [0, 1]` from the left end -/
def par (S : Shape) (t : ℝ) : Plane := S.left + t • (S.right - S.left)

theorem par_zero (S : Shape) : S.par 0 = S.left := by simp [par]
theorem par_one (S : Shape) : S.par 1 = S.right := by simp [par]

theorem left_fst_lt_right_fst (S : Shape) : S.left.1 < S.right.1 := by
  cases S <;> simp [left, right] <;> norm_num

theorem left_fst_nonneg (S : Shape) : 0 ≤ S.left.1 := by cases S <;> simp [left]
theorem right_fst_le_one (S : Shape) : S.right.1 ≤ 1 := by cases S <;> simp [right] <;> norm_num

/-- the x-coordinate of the piece at parameter `t` lies in `[0, 1]` -/
theorem par_fst_mem (S : Shape) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ (S.par t).1 ∧ (S.par t).1 ≤ 1 := by
  have hl := S.left_fst_nonneg
  have hr := S.right_fst_le_one
  have hlr := S.left_fst_lt_right_fst
  simp only [par, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
  constructor <;> nlinarith

/-- The admissible shapes of a column with letter `ℓ`. -/
def Admissible (ℓ : Letter) : Shape → Prop
  | pass p q => 1 ≤ p ∧ ℓ.posR p = some q ∧ 1 ≤ q
  | armL m j => (∃ d, ℓ = .l m d) ∧ (j = m ∨ j = m + 1)
  | armR m j => ℓ = .r m ∧ (j = m ∨ j = m + 1)

end Shape

/-! ## 4. The piece of a slot -/

section Piece

variable {W}

/-- The column in which the edge leaving a slot lies. -/
def colOf (s : Slot W) : ℕ :=
  if s.1.2 = 0 then s.1.1 else if bit W s.1.1 s.1.2 then s.1.1 else s.1.1 - 1

/-- The normalized shape of the edge leaving a slot. -/
def shapeOf (s : Slot W) : Shape :=
  if s.1.2 = 0 then
    match letterAt W s.1.1 with
    | .l m d => .armL m (if d then m else m + 1)
    | .r m => .armR m (if bit W s.1.1 m then m + 1 else m)
    | .σ _ => .pass 0 0
  else if bit W s.1.1 s.1.2 then
    match (letterAt W s.1.1).posR s.1.2 with
    | some q => .pass s.1.2 q
    | none => .armR (letterAt W s.1.1).idx s.1.2
  else
    match (letterAt W (s.1.1 - 1)).posL s.1.2 with
    | some q => .pass q s.1.2
    | none => .armL (letterAt W (s.1.1 - 1)).idx s.1.2

variable (hW : W.Closed)
include hW

/-- The specification of the piece of a slot: its column is a real column whose letter admits the
shape, and the slot and its successor are the two ends of the placed piece, in the order of the
x-direction `xsign`. -/
theorem piece_spec (s : Slot W) :
    colOf s < W.length ∧ (shapeOf s).Admissible (letterAt W (colOf s)) ∧
    pt pl W s.1 = pl.A (colOf s) (if xsign s then (shapeOf s).left else (shapeOf s).right) ∧
    pt pl W (next hW s).1 = pl.A (colOf s) (if xsign s then (shapeOf s).right else (shapeOf s).left) := by
  rcases next_cases hW s with
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, hpq, hk⟩ | ⟨k, p, m, hs, hp, hb, hℓ, hpm, hn, hne, hk⟩ |
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, hpq, hk1, hk⟩ | ⟨k, p, m, d, hs, hp, hb, hℓ, hpm, hn, hb1, hb2, hk1, hk⟩ |
    ⟨k, m, d, hs, hℓ, hn, hb1, hb2, hm, hk⟩ | ⟨k, m, hs, hℓ, hn, hne, hm, hk⟩
  · -- (1) rightward pass
    have hp0 : p ≠ 0 := by omega
    have hcol : colOf s = k := by simp [colOf, hs, hb, hp0]
    have hsh : shapeOf s = .pass p q := by simp [shapeOf, hs, hb, hpq, hp0]
    have hx := xsign_cut hs hp0
    rw [hb] at hx
    refine ⟨by rw [hcol]; exact hk, ?_, ?_, ?_⟩
    · rw [hcol, hsh]; exact ⟨hp, hpq, hq⟩
    · rw [hcol, hsh, hx, hs, pt_cut pl W hp0]; simp [Shape.left, Placement.A_zero_fst]
    · rw [hcol, hsh, hx, hn, pt_cut pl W (by omega)]; simp [Shape.right, Placement.A_one_fst]
  · -- (2) rightward into a right cusp
    have hp0 : p ≠ 0 := by omega
    have hcol : colOf s = k := by simp [colOf, hs, hb, hp0]
    have hpq : (Letter.r m).posR p = none := by
      rcases hpm with rfl | rfl
      · exact posR_r_idx _
      · exact posR_r_idx_succ _
    have hsh : shapeOf s = .armR m p := by simp [shapeOf, hs, hb, hℓ, hpq, idx, hp0]
    have hx := xsign_cut hs hp0
    rw [hb] at hx
    refine ⟨by rw [hcol]; exact hk, ?_, ?_, ?_⟩
    · rw [hcol, hsh]; exact ⟨hℓ, hpm⟩
    · rw [hcol, hsh, hx, hs, pt_cut pl W hp0]; simp [Shape.left, Placement.A_zero_fst]
    · rw [hcol, hsh, hx, hn, pt_cusp, hℓ]; simp [Shape.right, Placement.A, Placement.mid, idx, div_eq_mul_inv]
  · -- (3) leftward pass
    have hp0 : p ≠ 0 := by omega
    have hcol : colOf s = k - 1 := by simp [colOf, hs, hb, hp0]
    have hsh : shapeOf s = .pass q p := by simp [shapeOf, hs, hb, hpq, hp0]
    obtain ⟨D⟩ := decomp hW (k - 1) (by omega)
    have hk' : k - 1 + 1 = k := by omega
    rw [hk'] at D
    have hpk : p ≤ (cut W k).length := by
      have := s.2; rw [hs] at this
      rcases this with ⟨h0, -⟩ | ⟨-, h1, -⟩
      · simp at h0; omega
      · exact h1
    obtain ⟨-, -, -, hqp⟩ := D.posL_some hp hpk hpq
    have hx := xsign_cut hs hp0
    rw [hb] at hx
    refine ⟨by rw [hcol]; omega, ?_, ?_, ?_⟩
    · rw [hcol, hsh]; exact ⟨hq, hqp, hp⟩
    · rw [hcol, hsh, hx, hs, pt_cut pl W hp0]; simp [Shape.right, Placement.A_one_fst, hk']
    · rw [hcol, hsh, hx, hn, pt_cut pl W (by omega)]; simp [Shape.left, Placement.A_zero_fst]
  · -- (4) leftward into a left cusp
    have hp0 : p ≠ 0 := by omega
    have hcol : colOf s = k - 1 := by simp [colOf, hs, hb, hp0]
    have hpq : (Letter.l m d).posL p = none := by
      rcases hpm with rfl | rfl
      · exact posL_l_idx _ _
      · exact posL_l_idx_succ _ _
    have hsh : shapeOf s = .armL m p := by simp [shapeOf, hs, hb, hℓ, hpq, idx, hp0]
    have hk' : k - 1 + 1 = k := by omega
    have hx := xsign_cut hs hp0
    rw [hb] at hx
    refine ⟨by rw [hcol]; omega, ?_, ?_, ?_⟩
    · rw [hcol, hsh]; exact ⟨⟨d, hℓ⟩, hpm⟩
    · rw [hcol, hsh, hx, hs, pt_cut pl W hp0]; simp [Shape.right, Placement.A_one_fst, hk']
    · rw [hcol, hsh, hx, hn, pt_cusp, hℓ]; simp [Shape.left, Placement.A, Placement.mid, idx, div_eq_mul_inv]
  · -- (5) out of a left cusp
    have hcol : colOf s = k := by simp [colOf, hs]
    have hsh : shapeOf s = .armL m (if d then m else m + 1) := by simp [shapeOf, hs, hℓ]
    have hx := xsign_cusp_l hs hℓ
    refine ⟨by rw [hcol]; exact hk, ?_, ?_, ?_⟩
    · rw [hcol, hsh]; exact ⟨⟨d, hℓ⟩, by cases d <;> simp⟩
    · rw [hcol, hsh, hx, hs, pt_cusp, hℓ]; simp [Shape.left, Placement.A, Placement.mid, idx, div_eq_mul_inv]
    · rw [hcol, hsh, hx, hn, pt_cut pl W (by split_ifs <;> omega)]
      cases d <;> simp [Shape.right, Placement.A_one_fst]
  · -- (6) out of a right cusp
    have hcol : colOf s = k := by simp [colOf, hs]
    have hsh : shapeOf s = .armR m (if bit W k m then m + 1 else m) := by simp [shapeOf, hs, hℓ]
    have hx := xsign_cusp_r hs hℓ
    refine ⟨by rw [hcol]; exact hk, ?_, ?_, ?_⟩
    · rw [hcol, hsh]; exact ⟨hℓ, by split_ifs <;> simp⟩
    · rw [hcol, hsh, hx, hs, pt_cusp, hℓ]; simp [Shape.right, Placement.A, Placement.mid, idx, div_eq_mul_inv]
    · rw [hcol, hsh, hx, hn, pt_cut pl W (by split_ifs <;> omega)]
      cases hb : bit W k m <;> simp [hb, Shape.left, Placement.A_zero_fst]

/-- The two ends of the piece of a slot are the points of the slot and of its successor (as a set). -/
theorem ends_eq (s : Slot W) :
    ({pt pl W s.1, pt pl W (next hW s).1} : Set Plane) =
      {pl.A (colOf s) (shapeOf s).left, pl.A (colOf s) (shapeOf s).right} := by
  obtain ⟨-, -, h1, h2⟩ := piece_spec pl hW s
  rw [h1, h2]
  cases xsign s
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact Set.pair_comm _ _
  · simp only [↓reduceIte]

/-- The piece (column and shape) determines the slot. -/
theorem slot_eq_of_piece_eq (pl : Placement) {s t : Slot W} (hc : colOf s = colOf t) (hsh : shapeOf s = shapeOf t) :
    s = t := by
  have h := ends_eq pl hW s
  rw [hc, hsh, ← ends_eq pl hW t] at h
  have hs : pt pl W s.1 ∈ ({pt pl W t.1, pt pl W (next hW t).1} : Set Plane) := by
    rw [← h]; exact Set.mem_insert _ _
  have hn : pt pl W (next hW s).1 ∈ ({pt pl W t.1, pt pl W (next hW t).1} : Set Plane) := by
    rw [← h]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hn
  rcases hs with hs | hs
  · exact pt_inj pl _ hs
  · have h1 : s = next hW t := pt_inj pl _ hs
    rcases hn with hn | hn
    · have h2 : next hW s = t := pt_inj pl _ hn
      exfalso
      apply next_next_ne hW t
      rw [← h1, h2]
    · have h2 : next hW s = next hW t := pt_inj pl _ hn
      exact next_injective hW h2

end Piece

/-! ## 5. Intersections inside one column (normalized) -/

namespace Shape

theorem par_pass (p q : ℕ) (t : ℝ) : (pass p q).par t = (t, -(p : ℝ) + t * ((p : ℝ) - q)) := by
  simp only [par, left, right, Prod.mk_add_mk, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

theorem par_armL (m j : ℕ) (t : ℝ) :
    (armL m j).par t = (1 / 2 + t / 2, -(m : ℝ) - 1 / 2 + t * ((m : ℝ) + 1 / 2 - j)) := by
  simp only [par, left, right, Prod.mk_add_mk, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

theorem par_armR (m j : ℕ) (t : ℝ) :
    (armR m j).par t = (t / 2, -(j : ℝ) + t * ((j : ℝ) - m - 1 / 2)) := by
  simp only [par, left, right, Prod.mk_add_mk, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

/-- the x-coordinate along a piece is strictly increasing in the parameter -/
theorem par_fst_injective (S : Shape) : Function.Injective (fun t : ℝ => (S.par t).1) := by
  intro t t' h
  have hlr := S.left_fst_lt_right_fst
  simp only [par, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at h
  have : (t - t') * (S.right.1 - S.left.1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

theorem par_injective (S : Shape) : Function.Injective S.par := fun t t' h =>
  S.par_fst_injective (congrArg Prod.fst h)

/-- x-coordinate `0` is reached only at the left end of a pass or of a right arm -/
theorem par_fst_eq_zero {S : Shape} {t : ℝ} (ht : 0 ≤ t) (h : (S.par t).1 = 0) :
    t = 0 ∧ S.left.1 = 0 := by
  cases S with
  | pass p q => rw [par_pass] at h; exact ⟨h, rfl⟩
  | armL m j => rw [par_armL] at h; simp only at h; linarith
  | armR m j => rw [par_armR] at h; simp only at h; exact ⟨by linarith, rfl⟩

/-- x-coordinate `1` is reached only at the right end of a pass or of a left arm -/
theorem par_fst_eq_one {S : Shape} {t : ℝ} (ht : t ≤ 1) (h : (S.par t).1 = 1) :
    t = 1 ∧ S.right.1 = 1 := by
  cases S with
  | pass p q => rw [par_pass] at h; exact ⟨h, rfl⟩
  | armL m j => rw [par_armL] at h; simp only at h; exact ⟨by linarith, rfl⟩
  | armR m j => rw [par_armR] at h; simp only at h; linarith

/-- The order of positions is preserved across a column, except by the crossing letter on its two
strands. -/
theorem posR_order {ℓ : Letter} {p q p' q' : ℕ} (h : ℓ.posR p = some q) (h' : ℓ.posR p' = some q')
    (hpp : p < p') :
    q < q' ∨ (∃ m, ℓ = .σ m ∧ p = m ∧ p' = m + 1 ∧ q = m + 1 ∧ q' = m) := by
  cases ℓ with
  | l m d =>
    rw [posR_l] at h h'
    left
    by_cases h1 : p < m
    · rw [ite_eq_left h1] at h; obtain rfl := Option.some.inj h
      by_cases h1' : p' < m
      · rw [ite_eq_left h1'] at h'; obtain rfl := Option.some.inj h'; exact hpp
      · rw [ite_eq_right h1'] at h'; obtain rfl := Option.some.inj h'; omega
    · rw [ite_eq_right h1] at h; obtain rfl := Option.some.inj h
      rw [ite_eq_right (by omega)] at h'; obtain rfl := Option.some.inj h'; omega
  | r m =>
    rw [posR_r] at h h'
    left
    by_cases h1 : p < m
    · rw [ite_eq_left h1] at h; obtain rfl := Option.some.inj h
      by_cases h1' : p' < m
      · rw [ite_eq_left h1'] at h'; obtain rfl := Option.some.inj h'; exact hpp
      · rw [ite_eq_right h1'] at h'
        by_cases h2' : p' < m + 2
        · rw [ite_eq_left h2'] at h'; exact absurd h' (by simp)
        · rw [ite_eq_right h2'] at h'; obtain rfl := Option.some.inj h'; omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : p < m + 2
      · rw [ite_eq_left h2] at h; exact absurd h (by simp)
      · rw [ite_eq_right h2] at h; obtain rfl := Option.some.inj h
        rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h'; obtain rfl := Option.some.inj h'; omega
  | σ m =>
    rw [posR_σ] at h h'
    by_cases h1 : p < m
    · rw [ite_eq_left h1] at h; obtain rfl := Option.some.inj h
      left
      by_cases h1' : p' < m
      · rw [ite_eq_left h1'] at h'; obtain rfl := Option.some.inj h'; exact hpp
      · rw [ite_eq_right h1'] at h'
        by_cases h2' : p' < m + 2
        · rw [ite_eq_left h2'] at h'; obtain rfl := Option.some.inj h'; split_ifs <;> omega
        · rw [ite_eq_right h2'] at h'; obtain rfl := Option.some.inj h'; omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : p < m + 2
      · rw [ite_eq_left h2] at h; obtain rfl := Option.some.inj h
        have h1' : ¬ p' < m := by omega
        rw [ite_eq_right h1'] at h'
        by_cases h2' : p' < m + 2
        · rw [ite_eq_left h2'] at h'; obtain rfl := Option.some.inj h'
          have hp : p = m := by omega
          have hp' : p' = m + 1 := by omega
          right
          refine ⟨m, rfl, hp, hp', ?_, ?_⟩
          · rw [ite_eq_left hp]
          · rw [ite_eq_right (by omega)]
        · rw [ite_eq_right h2'] at h'; obtain rfl := Option.some.inj h'; left; split_ifs <;> omega
      · rw [ite_eq_right h2] at h; obtain rfl := Option.some.inj h
        rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h'; obtain rfl := Option.some.inj h'
        left; exact hpp

/-- `posR` is injective on its domain. -/
theorem posR_inj {ℓ : Letter} {p p' q : ℕ} (h : ℓ.posR p = some q) (h' : ℓ.posR p' = some q) : p = p' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rcases posR_order h h' hlt with h1 | ⟨m, -, -, -, h2, h3⟩
    · exact lt_irrefl _ h1
    · omega
  · rcases posR_order h' h hlt with h1 | ⟨m, -, -, -, h2, h3⟩
    · exact lt_irrefl _ h1
    · omega

/-- A pass and a left-cusp arm of the same column never meet. -/
theorem pass_armL_absurd {m p q j : ℕ} {d : Bool} (hpq : (Letter.l m d).posR p = some q) (hj : j = m ∨ j = m + 1)
    {t t' : ℝ} (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) (h : (pass p q).par t = (armL m j).par t') : False := by
  rw [par_pass, par_armL, Prod.mk.injEq] at h
  obtain ⟨hx, hz⟩ := h
  rw [posR_l] at hpq
  split_ifs at hpq with hpm
  · obtain rfl := Option.some.inj hpq
    have hpm' : (p : ℝ) + 1 ≤ m := by exact_mod_cast hpm
    rcases hj with rfl | rfl
    · nlinarith
    · push_cast at hz; nlinarith
  · obtain rfl := Option.some.inj hpq
    have hpm' : (m : ℝ) ≤ p := by exact_mod_cast (not_lt.1 hpm)
    push_cast at hz
    rcases hj with rfl | rfl
    · nlinarith
    · push_cast at hz; nlinarith

/-- A pass and a right-cusp arm of the same column never meet. -/
theorem pass_armR_absurd {m p q j : ℕ} (hpq : (Letter.r m).posR p = some q) (hj : j = m ∨ j = m + 1)
    {t t' : ℝ} (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) (h : (pass p q).par t = (armR m j).par t') : False := by
  rw [par_pass, par_armR, Prod.mk.injEq] at h
  obtain ⟨hx, hz⟩ := h
  rw [posR_r] at hpq
  by_cases hpm : p < m
  · rw [ite_eq_left hpm] at hpq
    obtain rfl := Option.some.inj hpq
    have hpm' : (p : ℝ) + 1 ≤ m := by exact_mod_cast hpm
    rcases hj with rfl | rfl
    · nlinarith
    · push_cast at hz; nlinarith
  · rw [ite_eq_right hpm] at hpq
    by_cases hpm2 : p < m + 2
    · rw [ite_eq_left hpm2] at hpq; exact absurd hpq (by simp)
    · rw [ite_eq_right hpm2] at hpq
      obtain rfl := Option.some.inj hpq
      have hpm' : (m : ℝ) + 2 ≤ p := by exact_mod_cast (not_lt.1 hpm2)
      have hq : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [hq] at hz
      rcases hj with rfl | rfl
      · nlinarith
      · push_cast at hz; nlinarith

/-- Two distinct admissible pieces of one column meet only as the two strands of a crossing letter (at
the centre, in their interiors) or as the two arms of a cusp (at the cusp vertex). -/
theorem meet {ℓ : Letter} {S S' : Shape} (hS : S.Admissible ℓ) (hS' : S'.Admissible ℓ) (hne : S ≠ S')
    {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) (h : S.par t = S'.par t') :
    (∃ m, ℓ = .σ m ∧ t = 1 / 2 ∧ t' = 1 / 2 ∧
      ((S = .pass m (m + 1) ∧ S' = .pass (m + 1) m) ∨ (S = .pass (m + 1) m ∧ S' = .pass m (m + 1)))) ∨
    (t = 0 ∧ t' = 0 ∧ ∃ m j j', S = .armL m j ∧ S' = .armL m j') ∨
    (t = 1 ∧ t' = 1 ∧ ∃ m j j', S = .armR m j ∧ S' = .armR m j') := by
  cases S with
  | pass p q =>
    cases S' with
    | pass p' q' =>
      obtain ⟨hp, hpq, hq⟩ := hS
      obtain ⟨hp', hpq', hq'⟩ := hS'
      rw [par_pass, par_pass, Prod.mk.injEq] at h
      obtain ⟨rfl, hz⟩ := h
      rcases lt_trichotomy p p' with hlt | heq | hgt
      · rcases posR_order hpq hpq' hlt with hqq | ⟨m, hℓ, hp1, hp2, hq1, hq2⟩
        · exfalso
          have h1 : ((p : ℝ) + 1) ≤ p' := by exact_mod_cast hlt
          have h2 : ((q : ℝ) + 1) ≤ q' := by exact_mod_cast hqq
          have e : ((p' : ℝ) - p) * (1 - t) + ((q' : ℝ) - q) * t = 0 := by linear_combination hz
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p' - p - 1) (by linarith : (0 : ℝ) ≤ 1 - t),
            mul_nonneg (by linarith : (0 : ℝ) ≤ q' - q - 1) ht0]
        · left
          subst hℓ hp1 hp2 hq1 hq2
          push_cast at hz
          exact ⟨_, rfl, by linarith, by linarith, Or.inl ⟨rfl, rfl⟩⟩
      · subst heq
        rw [hpq] at hpq'
        obtain rfl := Option.some.inj hpq'
        exact absurd rfl hne
      · rcases posR_order hpq' hpq hgt with hqq | ⟨m, hℓ, hp1, hp2, hq1, hq2⟩
        · exfalso
          have h1 : ((p' : ℝ) + 1) ≤ p := by exact_mod_cast hgt
          have h2 : ((q' : ℝ) + 1) ≤ q := by exact_mod_cast hqq
          have e : ((p : ℝ) - p') * (1 - t) + ((q : ℝ) - q') * t = 0 := by linear_combination -hz
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p - p' - 1) (by linarith : (0 : ℝ) ≤ 1 - t),
            mul_nonneg (by linarith : (0 : ℝ) ≤ q - q' - 1) ht0]
        · left
          subst hℓ hp1 hp2 hq1 hq2
          push_cast at hz
          exact ⟨_, rfl, by linarith, by linarith, Or.inr ⟨rfl, rfl⟩⟩
    | armL m j =>
      obtain ⟨⟨d, rfl⟩, hj⟩ := hS'
      exact (pass_armL_absurd hS.2.1 hj ht0' ht1' h).elim
    | armR m j =>
      obtain ⟨rfl, hj⟩ := hS'
      exact (pass_armR_absurd hS.2.1 hj ht0' ht1' h).elim
  | armL m j =>
    cases S' with
    | pass p q =>
      obtain ⟨⟨d, rfl⟩, hj⟩ := hS
      exact (pass_armL_absurd hS'.2.1 hj ht0 ht1 h.symm).elim
    | armL m' j' =>
      obtain ⟨⟨d, hℓ⟩, hj⟩ := hS
      obtain ⟨⟨d', hℓ'⟩, hj'⟩ := hS'
      rw [hℓ] at hℓ'
      obtain ⟨rfl, rfl⟩ := Letter.l.inj hℓ'
      have hjj : j ≠ j' := fun hjj => hne (by rw [hjj])
      rw [par_armL, par_armL, Prod.mk.injEq] at h
      obtain ⟨hx, hz⟩ := h
      have htt : t = t' := by linarith
      subst htt
      have hjj' : (j : ℝ) ≠ j' := by exact_mod_cast hjj
      have : t * ((j' : ℝ) - j) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · right; left; exact ⟨h0, h0, m, j, j', rfl, rfl⟩
      · exact absurd (by linarith : (j : ℝ) = j') hjj'
    | armR m' j' =>
      obtain ⟨⟨d, hℓ⟩, -⟩ := hS
      obtain ⟨hℓ', -⟩ := hS'
      rw [hℓ] at hℓ'; cases hℓ'
  | armR m j =>
    cases S' with
    | pass p q =>
      obtain ⟨rfl, hj⟩ := hS
      exact (pass_armR_absurd hS'.2.1 hj ht0 ht1 h.symm).elim
    | armL m' j' =>
      obtain ⟨hℓ, -⟩ := hS
      obtain ⟨⟨d, hℓ'⟩, -⟩ := hS'
      rw [hℓ] at hℓ'; cases hℓ'
    | armR m' j' =>
      obtain ⟨hℓ, hj⟩ := hS
      obtain ⟨hℓ', hj'⟩ := hS'
      rw [hℓ] at hℓ'
      obtain rfl := Letter.r.inj hℓ'
      have hjj : j ≠ j' := fun hjj => hne (by rw [hjj])
      rw [par_armR, par_armR, Prod.mk.injEq] at h
      obtain ⟨hx, hz⟩ := h
      have htt : t = t' := by linarith
      subst htt
      have hjj' : (j : ℝ) ≠ j' := by exact_mod_cast hjj
      have : (1 - t) * ((j' : ℝ) - j) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · right; right; exact ⟨by linarith, by linarith, m, j, j', rfl, rfl⟩
      · exact absurd (by linarith : (j : ℝ) = j') hjj'

/-- the direction vector of the normalized piece -/
def vec (S : Shape) : Plane := S.right - S.left

theorem vec_pass (p q : ℕ) : (pass p q).vec = (1, (p : ℝ) - q) := by
  simp only [vec, left, right, Prod.mk_sub_mk]; ext <;> simp <;> ring

theorem par_eq (S : Shape) (t : ℝ) : S.par t = S.left + t • S.vec := rfl

end Shape

/-! ## 6. The shadow of a closed word -/

section Shadow

variable (pl : Placement) {W : Word} (hW : W.Closed)
include hW

theorem isSlot_zero (hne : W ≠ []) : IsSlot W (0, 0) := by
  obtain ⟨d, hd⟩ := letterAt_zero hW hne
  left
  exact ⟨rfl, List.length_pos_of_ne_nil hne, by rw [hd]; rfl⟩

theorem nonempty_orbit (hne : W ≠ []) : Nonempty (Orbit hW) :=
  ⟨orbitOf hW ⟨(0, 0), isSlot_zero hW hne⟩⟩

/-- The shadow of the realization: one component per cycle of the successor permutation, its vertices
the points of the slots in cycle order. -/
def shadowOf (hne : W ≠ []) : Shadow where
  c := numComp hW
  hc := @Fintype.card_pos _ _ (nonempty_orbit hW hne)
  comp := fun i => ⟨period hW (rep hW i), three_le_period hW _, fun j => pt pl W (toSlot hW ⟨i, j⟩).1⟩

variable (hne : W ≠ [])

theorem shadowOf_c : (shadowOf pl hW hne).c = numComp hW := rfl

theorem shadowOf_comp_k (i : Fin (numComp hW)) : ((shadowOf pl hW hne).comp i).k = period hW (rep hW i) := rfl

/-- the strands of the shadow are the strand indices -/
theorem shadowOf_Strand : (shadowOf pl hW hne).Strand = Idx hW := rfl

/-- The slot at the tail of a strand. -/
def slotOf (s : (shadowOf pl hW hne).Strand) : Slot W := toSlot hW s

theorem slotOf_injective : Function.Injective (slotOf pl hW hne) := toSlot_injective hW

theorem slotOf_surjective : Function.Surjective (slotOf pl hW hne) := toSlot_surjective hW

theorem slotOf_succ (i : Fin (shadowOf pl hW hne).c) (j : ZMod ((shadowOf pl hW hne).comp i).k) :
    slotOf pl hW hne ⟨i, j + 1⟩ = next hW (slotOf pl hW hne ⟨i, j⟩) := toSlot_succ hW i j

theorem slotOf_pred (i : Fin (shadowOf pl hW hne).c) (j : ZMod ((shadowOf pl hW hne).comp i).k) :
    slotOf pl hW hne ⟨i, j - 1⟩ = prev hW (slotOf pl hW hne ⟨i, j⟩) := toSlot_pred hW i j

theorem tail_eq (s : (shadowOf pl hW hne).Strand) :
    (shadowOf pl hW hne).tail s = pt pl W (slotOf pl hW hne s).1 := rfl

theorem head_eq (s : (shadowOf pl hW hne).Strand) :
    (shadowOf pl hW hne).head s = pt pl W (next hW (slotOf pl hW hne s)).1 := by
  obtain ⟨i, j⟩ := s
  show pt pl W (slotOf pl hW hne ⟨i, j + 1⟩).1 = _
  rw [slotOf_succ]

theorem dir_eq (s : (shadowOf pl hW hne).Strand) :
    (shadowOf pl hW hne).dir s = pt pl W (next hW (slotOf pl hW hne s)).1 - pt pl W (slotOf pl hW hne s).1 := by
  rw [← head_eq, ← tail_eq]; rfl

/-- the direction of the strand arriving at the tail of `⟨i, j⟩` -/
theorem dir_pred_eq (i : Fin (shadowOf pl hW hne).c) (j : ZMod ((shadowOf pl hW hne).comp i).k) :
    (shadowOf pl hW hne).dir ⟨i, j - 1⟩ =
      pt pl W (slotOf pl hW hne ⟨i, j⟩).1 - pt pl W (prev hW (slotOf pl hW hne ⟨i, j⟩)).1 := by
  rw [dir_eq, slotOf_pred, next_prev]

omit hW in
/-- `A k` is affine. -/
theorem A_affine (k : ℕ) (a b : Plane) (t : ℝ) :
    pl.A k a + t • (pl.A k b - pl.A k a) = pl.A k (a + t • (b - a)) := by
  refine Prod.ext ?_ ?_ <;> simp [Placement.A] <;> ring

/-- The point of the piece of a slot at parameter `τ`. -/
def piecePt (u : Slot W) (τ : ℝ) : Plane := pl.A (colOf u) ((shapeOf u).par τ)

/-- The edge points of a strand are the points of its slot's piece (the parameter reversed for a
leftward strand). -/
theorem edgePoint_eq (s : (shadowOf pl hW hne).Strand) (t : ℝ) :
    edgePoint ((shadowOf pl hW hne).comp s.1).P s.2 t =
      piecePt pl (slotOf pl hW hne s) (if xsign (slotOf pl hW hne s) then t else 1 - t) := by
  obtain ⟨-, -, h1, h2⟩ := piece_spec pl hW (slotOf pl hW hne s)
  have e : edgePoint ((shadowOf pl hW hne).comp s.1).P s.2 t =
      (shadowOf pl hW hne).tail s + t • ((shadowOf pl hW hne).head s - (shadowOf pl hW hne).tail s) := rfl
  rw [e, tail_eq, head_eq, h1, h2, A_affine]
  unfold piecePt
  cases xsign (slotOf pl hW hne s)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    simp only [Shape.par]
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  · simp only [↓reduceIte]
    rfl

theorem mem_seg_iff (s : (shadowOf pl hW hne).Strand) (q : Plane) :
    q ∈ (shadowOf pl hW hne).seg s ↔ ∃ τ, 0 ≤ τ ∧ τ ≤ 1 ∧ q = piecePt pl (slotOf pl hW hne s) τ := by
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    rw [edgePoint_eq]
    cases xsign (slotOf pl hW hne s)
    · exact ⟨1 - t, by linarith, by linarith, by simp⟩
    · exact ⟨t, ht0, ht1, by simp⟩
  · rintro ⟨τ, hτ0, hτ1, rfl⟩
    cases hx : xsign (slotOf pl hW hne s)
    · refine ⟨1 - τ, by linarith, by linarith, ?_⟩
      rw [edgePoint_eq, hx]; simp
    · refine ⟨τ, hτ0, hτ1, ?_⟩
      rw [edgePoint_eq, hx]; simp

theorem mem_interior_iff (s : (shadowOf pl hW hne).Strand) (q : Plane) :
    q ∈ (shadowOf pl hW hne).interior s ↔ ∃ τ, 0 < τ ∧ τ < 1 ∧ q = piecePt pl (slotOf pl hW hne s) τ := by
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    rw [edgePoint_eq]
    cases xsign (slotOf pl hW hne s)
    · exact ⟨1 - t, by linarith, by linarith, by simp⟩
    · exact ⟨t, ht0, ht1, by simp⟩
  · rintro ⟨τ, hτ0, hτ1, rfl⟩
    cases hx : xsign (slotOf pl hW hne s)
    · refine ⟨1 - τ, by linarith, by linarith, ?_⟩
      rw [edgePoint_eq, hx]; simp
    · refine ⟨τ, hτ0, hτ1, ?_⟩
      rw [edgePoint_eq, hx]; simp

/-- Adjacency of strands is adjacency of slots along the successor. -/
theorem adjacent_iff (s t : (shadowOf pl hW hne).Strand) :
    (shadowOf pl hW hne).Adjacent s t ↔
      slotOf pl hW hne t = slotOf pl hW hne s ∨ slotOf pl hW hne t = next hW (slotOf pl hW hne s) ∨
        slotOf pl hW hne t = prev hW (slotOf pl hW hne s) := by
  obtain ⟨i, a⟩ := s
  obtain ⟨j, b⟩ := t
  constructor
  · intro h
    have hij : i = j := h.fst_eq
    subst hij
    have hadj := ((shadowOf pl hW hne).adjacent_mk_iff i a b).1 h
    rcases hadj with h1 | h1 | h1
    · right; right
      rw [← slotOf_pred, show a - 1 = b by rw [sub_eq_iff_eq_add.1 h1]; ring]
    · left
      rw [sub_eq_zero.1 h1]
    · right; left
      rw [← slotOf_succ, show b = a + 1 by rw [sub_eq_iff_eq_add.1 h1]; ring]
  · intro h
    rcases h with h1 | h1 | h1
    · have := slotOf_injective pl hW hne h1
      rw [this]
      exact Shadow.Adjacent.refl _ _
    · rw [← slotOf_succ] at h1
      have := slotOf_injective pl hW hne h1
      rw [this]
      exact ((shadowOf pl hW hne).adjacent_mk_iff i a (a + 1)).2 (Or.inr (Or.inr (by ring)))
    · rw [← slotOf_pred] at h1
      have := slotOf_injective pl hW hne h1
      rw [this]
      exact ((shadowOf pl hW hne).adjacent_mk_iff i a (a - 1)).2 (Or.inl (by ring))

/-- The tail of `s` is incident to `t` when the two slots coincide or `s` follows `t`. -/
theorem incidentTail_of (s t : (shadowOf pl hW hne).Strand)
    (h : slotOf pl hW hne s = slotOf pl hW hne t ∨ slotOf pl hW hne s = next hW (slotOf pl hW hne t)) :
    (shadowOf pl hW hne).IncidentTail s t := by
  obtain ⟨j, b⟩ := t
  rcases h with h1 | h1
  · have := slotOf_injective pl hW hne h1
    rw [this]
    exact ((shadowOf pl hW hne).incidentTail_mk_iff j b b).2 (Or.inr rfl)
  · rw [← slotOf_succ] at h1
    have := slotOf_injective pl hW hne h1
    rw [this]
    exact ((shadowOf pl hW hne).incidentTail_mk_iff j (b + 1) b).2 (Or.inl (by ring))

end Shadow

/-! ## 7. Genericity: pieces meet only at common slots and at the crossings of `σ` letters -/

section Generic

variable (pl : Placement) {W : Word} (hW : W.Closed)
include hW

/-- The point of a slot is an end of its piece. -/
theorem pt_eq_piecePt (u : Slot W) : pt pl W u.1 = piecePt pl u (if xsign u then 0 else 1) := by
  obtain ⟨-, -, h1, -⟩ := piece_spec pl hW u
  rw [h1]; unfold piecePt
  cases xsign u <;> simp [Shape.par_zero, Shape.par_one]

/-- The point of the successor is the other end of the piece. -/
theorem pt_next_eq_piecePt (u : Slot W) : pt pl W (next hW u).1 = piecePt pl u (if xsign u then 1 else 0) := by
  obtain ⟨-, -, -, h2⟩ := piece_spec pl hW u
  rw [h2]; unfold piecePt
  cases xsign u <;> simp [Shape.par_zero, Shape.par_one]

/-- An end of the piece of `u` is the point of `u` or of `next u`. -/
theorem endpoint_mem (u : Slot W) {E : Plane} (hE : E = (shapeOf u).left ∨ E = (shapeOf u).right) :
    ∃ c : Slot W, pt pl W c.1 = pl.A (colOf u) E ∧ (c = u ∨ c = next hW u) := by
  obtain ⟨-, -, h1, h2⟩ := piece_spec pl hW u
  cases hx : xsign u <;> rw [hx] at h1 h2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
  · rcases hE with rfl | rfl
    · exact ⟨next hW u, h2, Or.inr rfl⟩
    · exact ⟨u, h1, Or.inl rfl⟩
  · rcases hE with rfl | rfl
    · exact ⟨u, h1, Or.inl rfl⟩
    · exact ⟨next hW u, h2, Or.inr rfl⟩

/-- Two pieces in columns `colOf u < colOf v` can only meet at the common cut line, at a common slot. -/
theorem common_point_lt (u v : Slot W) {τ τ' : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hτ0' : 0 ≤ τ') (hτ1' : τ' ≤ 1)
    (hlt : colOf u < colOf v) (h : piecePt pl u τ = piecePt pl v τ') :
    ∃ c : Slot W, pt pl W c.1 = piecePt pl u τ ∧ (c = u ∨ c = next hW u) ∧ (c = v ∨ c = next hW v) := by
  unfold piecePt at h
  have hx := congrArg Prod.fst h
  simp only [Placement.A_fst] at hx
  obtain ⟨hu0, hu1⟩ := (shapeOf u).par_fst_mem hτ0 hτ1
  obtain ⟨hv0, hv1⟩ := (shapeOf v).par_fst_mem hτ0' hτ1'
  have h1 : pl.x (colOf u + 1) ≤ pl.x (colOf v) := pl.x_le_x_iff.2 hlt
  have hwu := pl.w_pos (colOf u)
  have hwv := pl.w_pos (colOf v)
  have hxw := pl.x_add_w (colOf u)
  have e1 : pl.w (colOf u) * ((shapeOf u).par τ).1 ≤ pl.w (colOf u) := by nlinarith
  have e2 : 0 ≤ pl.w (colOf v) * ((shapeOf v).par τ').1 := by nlinarith
  have hu : ((shapeOf u).par τ).1 = 1 := by
    have : pl.w (colOf u) * ((shapeOf u).par τ).1 = pl.w (colOf u) := by linarith
    have : pl.w (colOf u) * (((shapeOf u).par τ).1 - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  have hv : ((shapeOf v).par τ').1 = 0 := by
    have : pl.w (colOf v) * ((shapeOf v).par τ').1 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  obtain ⟨rfl, -⟩ := Shape.par_fst_eq_one hτ1 hu
  obtain ⟨rfl, -⟩ := Shape.par_fst_eq_zero hτ0' hv
  rw [Shape.par_one, Shape.par_zero] at h
  obtain ⟨c, hc, hcu⟩ := endpoint_mem pl hW u (Or.inr rfl)
  obtain ⟨c', hc', hcv⟩ := endpoint_mem pl hW v (Or.inl rfl)
  have : c = c' := pt_inj pl _ (by rw [hc, hc', h])
  subst this
  exact ⟨c, by rw [hc]; unfold piecePt; rw [Shape.par_one], hcu, hcv⟩

/-- The common points of two pieces: the same piece at the same parameter, a common slot at an end of
both, or the crossing of the two strands of a `σ` letter at the centre of its column. -/
theorem common_point (u v : Slot W) {τ τ' : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hτ0' : 0 ≤ τ') (hτ1' : τ' ≤ 1)
    (h : piecePt pl u τ = piecePt pl v τ') :
    (u = v ∧ τ = τ') ∨
    (∃ c : Slot W, pt pl W c.1 = piecePt pl u τ ∧ (c = u ∨ c = next hW u) ∧ (c = v ∨ c = next hW v)) ∨
    (colOf u = colOf v ∧ τ = 1 / 2 ∧ τ' = 1 / 2 ∧ ∃ m, letterAt W (colOf u) = .σ m ∧
      ((shapeOf u = .pass m (m + 1) ∧ shapeOf v = .pass (m + 1) m) ∨
       (shapeOf u = .pass (m + 1) m ∧ shapeOf v = .pass m (m + 1)))) := by
  rcases lt_trichotomy (colOf u) (colOf v) with hlt | heq | hgt
  · exact Or.inr (Or.inl (common_point_lt pl hW u v hτ0 hτ1 hτ0' hτ1' hlt h))
  · have hpar : (shapeOf u).par τ = (shapeOf v).par τ' := by
      unfold piecePt at h
      rw [heq] at h
      exact pl.A_injective _ h
    by_cases hsh : shapeOf u = shapeOf v
    · left
      have huv : u = v := slot_eq_of_piece_eq hW pl heq hsh
      subst huv
      exact ⟨rfl, (shapeOf u).par_injective hpar⟩
    · obtain ⟨-, hadm, -, -⟩ := piece_spec pl hW u
      obtain ⟨-, hadm', -, -⟩ := piece_spec pl hW v
      rw [← heq] at hadm'
      rcases Shape.meet hadm hadm' hsh hτ0 hτ1 hτ0' hτ1' hpar with
        ⟨m, hℓ, rfl, rfl, hS⟩ | ⟨rfl, rfl, m, j, j', hSu, hSv⟩ | ⟨rfl, rfl, m, j, j', hSu, hSv⟩
      · exact Or.inr (Or.inr ⟨heq, rfl, rfl, m, hℓ, hS⟩)
      · right; left
        have hl : (shapeOf u).par 0 = (shapeOf u).left := Shape.par_zero _
        have hl' : (shapeOf v).par 0 = (shapeOf v).left := Shape.par_zero _
        obtain ⟨c, hc, hcu⟩ := endpoint_mem pl hW u (Or.inl rfl)
        obtain ⟨c', hc', hcv⟩ := endpoint_mem pl hW v (Or.inl rfl)
        have : c = c' := pt_inj pl _ (by
          rw [hc, hc']
          unfold piecePt at h
          rw [hl, hl'] at h
          exact h)
        subst this
        exact ⟨c, by rw [hc]; unfold piecePt; rw [hl], hcu, hcv⟩
      · right; left
        have hl : (shapeOf u).par 1 = (shapeOf u).right := Shape.par_one _
        have hl' : (shapeOf v).par 1 = (shapeOf v).right := Shape.par_one _
        obtain ⟨c, hc, hcu⟩ := endpoint_mem pl hW u (Or.inr rfl)
        obtain ⟨c', hc', hcv⟩ := endpoint_mem pl hW v (Or.inr rfl)
        have : c = c' := pt_inj pl _ (by
          rw [hc, hc']
          unfold piecePt at h
          rw [hl, hl'] at h
          exact h)
        subst this
        exact ⟨c, by rw [hc]; unfold piecePt; rw [hl], hcu, hcv⟩
  · obtain ⟨c, hc, hcv, hcu⟩ := common_point_lt pl hW v u hτ0' hτ1' hτ0 hτ1 hgt h.symm
    exact Or.inr (Or.inl ⟨c, by rw [hc, h], hcu, hcv⟩)

/-- The direction vector of the edge leaving a slot: the placed direction of its shape, reversed for a
leftward strand. -/
theorem dir_slot_eq (u : Slot W) :
    pt pl W (next hW u).1 - pt pl W u.1 =
      (if xsign u then (1 : ℝ) else -1) • (pl.w (colOf u) * (shapeOf u).vec.1, (shapeOf u).vec.2) := by
  obtain ⟨-, -, h1, h2⟩ := piece_spec pl hW u
  rw [h1, h2]
  cases xsign u <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    refine Prod.ext ?_ ?_ <;> simp [Placement.A, Shape.vec] <;> ring

theorem dir_slot_fst_ne_zero (u : Slot W) : (pt pl W (next hW u).1 - pt pl W u.1).1 ≠ 0 := by
  rw [dir_slot_eq]
  have hw := pl.w_pos (colOf u)
  have hv : 0 < (shapeOf u).vec.1 := by
    simp only [Shape.vec, Prod.fst_sub]; linarith [(shapeOf u).left_fst_lt_right_fst]
  cases xsign u <;> simp <;> constructor <;> positivity

/-- The sign of the x-component of the edge leaving a slot is its `xsign`. -/
theorem dir_slot_fst_pos_iff (u : Slot W) : 0 < (pt pl W (next hW u).1 - pt pl W u.1).1 ↔ xsign u = true := by
  rw [dir_slot_eq]
  have hw := pl.w_pos (colOf u)
  have hv : 0 < (shapeOf u).vec.1 := by
    simp only [Shape.vec, Prod.fst_sub]; linarith [(shapeOf u).left_fst_lt_right_fst]
  cases xsign u
  · simp; nlinarith
  · simp; positivity

/-- At a cusp vertex the two arms have the same nonzero z-component (so they are not antiparallel). -/
theorem cusp_arms {u : Slot W} {k : ℕ} (hu : u.1 = (k, 0)) :
    (pt pl W u.1 - pt pl W (prev hW u).1).2 = (pt pl W (next hW u).1 - pt pl W u.1).2 ∧
    (pt pl W (next hW u).1 - pt pl W u.1).2 ≠ 0 := by
  have hn : (next hW u).1 = nextPair W (k, 0) := by rw [next_val, hu]
  have hp : (prev hW u).1 = prevPair W (k, 0) := by rw [prev_val, hu]
  rcases letterAt_of_cusp (W := W) (s := u) (by rw [hu]) with ⟨m, d, hℓ⟩ | ⟨m, hℓ⟩
  · rw [hu] at hℓ
    have hm : 1 ≤ m := by
      have := u.2; rw [hu] at this
      rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
      · obtain ⟨D⟩ := decomp hW k hk; rw [hℓ] at D; have := D.hm; simpa [idx] using this
      · simp at h0
    rw [hn, hp, nextPair_cusp_l W hℓ, prevPair_cusp_l W hℓ, hu, pt_cusp, hℓ,
      pt_cut pl W (by split_ifs <;> omega), pt_cut pl W (by split_ifs <;> omega)]
    simp only [idx, Prod.snd_sub]
    refine ⟨?_, ?_⟩
    · cases d <;> simp <;> ring
    · cases d <;> simp <;> ring_nf <;> norm_num
  · rw [hu] at hℓ
    have hm : 1 ≤ m := by
      have := u.2; rw [hu] at this
      rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
      · obtain ⟨D⟩ := decomp hW k hk; rw [hℓ] at D; have := D.hm; simpa [idx] using this
      · simp at h0
    rw [hn, hp, nextPair_cusp_r W hℓ, prevPair_cusp_r W hℓ, hu, pt_cusp, hℓ,
      pt_cut pl W (by split_ifs <;> omega), pt_cut pl W (by split_ifs <;> omega)]
    simp only [idx, Prod.snd_sub]
    refine ⟨?_, ?_⟩
    · cases bit W k m <;> simp <;> ring
    · cases bit W k m <;> simp <;> ring_nf <;> norm_num

variable (hne : W ≠ [])

/-- Every component is a regular polygon: nonzero edges, no antiparallel consecutive edges. -/
theorem regular (i : Fin (shadowOf pl hW hne).c) : Regular ((shadowOf pl hW hne).comp i).P := by
  intro j
  have hout : edge ((shadowOf pl hW hne).comp i).P j = (shadowOf pl hW hne).dir ⟨i, j⟩ := rfl
  have hin : edge ((shadowOf pl hW hne).comp i).P (j - 1) = (shadowOf pl hW hne).dir ⟨i, j - 1⟩ := rfl
  rw [hout, hin, dir_pred_eq, dir_eq]
  set u := slotOf pl hW hne ⟨i, j⟩ with hu
  have hne1 : pt pl W u.1 - pt pl W (prev hW u).1 ≠ 0 := by
    have := dir_slot_fst_ne_zero pl hW (prev hW u)
    rw [next_prev] at this
    intro h0; apply this; rw [h0]; rfl
  have hne2 : pt pl W (next hW u).1 - pt pl W u.1 ≠ 0 := by
    have := dir_slot_fst_ne_zero pl hW u
    intro h0; apply this; rw [h0]; rfl
  refine ⟨hne1, hne2, ?_⟩
  rintro ⟨r, hr, hrv⟩
  by_cases hcut : u.1.2 = 0
  · -- a cusp vertex: equal nonzero z-components
    obtain ⟨hz, hz0⟩ := cusp_arms pl hW (u := u) (k := u.1.1) (Prod.ext rfl hcut)
    have h2 := congrArg Prod.snd hrv
    simp only [Prod.smul_snd, smul_eq_mul] at h2
    rw [← hz] at h2 hz0
    have : (r - 1) * (pt pl W u.1 - pt pl W (prev hW u).1).2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact hz0 h'
  · -- a cut slot: same x-direction on both sides
    have hx : xsign (prev hW u) = xsign u := by
      have := xsign_next_iff hW (prev hW u)
      rw [next_prev] at this
      exact (this.2 hcut).symm
    have h1 := dir_slot_fst_pos_iff pl hW (prev hW u)
    rw [next_prev] at h1
    have h2 := dir_slot_fst_pos_iff pl hW u
    have hf := congrArg Prod.fst hrv
    simp only [Prod.smul_fst, smul_eq_mul] at hf
    have hne1' := dir_slot_fst_ne_zero pl hW (prev hW u)
    rw [next_prev] at hne1'
    cases hxs : xsign u
    · rw [hxs] at h2 hx
      rw [hx] at h1
      have a1 : (pt pl W u.1 - pt pl W (prev hW u).1).1 < 0 := by
        have : ¬ 0 < (pt pl W u.1 - pt pl W (prev hW u).1).1 := fun h => by simpa using h1.1 h
        exact lt_of_le_of_ne (not_lt.1 this) hne1'
      have a2 : (pt pl W (next hW u).1 - pt pl W u.1).1 < 0 := by
        have : ¬ 0 < (pt pl W (next hW u).1 - pt pl W u.1).1 := fun h => by simpa using h2.1 h
        exact lt_of_le_of_ne (not_lt.1 this) (dir_slot_fst_ne_zero pl hW u)
      nlinarith
    · rw [hxs] at h2 hx
      rw [hx] at h1
      have a1 : 0 < (pt pl W u.1 - pt pl W (prev hW u).1).1 := h1.2 rfl
      have a2 : 0 < (pt pl W (next hW u).1 - pt pl W u.1).1 := h2.2 rfl
      nlinarith

/-- No vertex lies on an edge segment other than its two incident edges. -/
theorem tail_off (s t : (shadowOf pl hW hne).Strand) (hinc : ¬ (shadowOf pl hW hne).IncidentTail s t) :
    (shadowOf pl hW hne).tail s ∉ (shadowOf pl hW hne).seg t := by
  intro hmem
  rw [mem_seg_iff] at hmem
  obtain ⟨τ', hτ0', hτ1', hq⟩ := hmem
  rw [tail_eq, pt_eq_piecePt pl hW] at hq
  set u := slotOf pl hW hne s
  set v := slotOf pl hW hne t
  have hτ0 : (0 : ℝ) ≤ if xsign u then 0 else 1 := by split_ifs <;> norm_num
  have hτ1 : (if xsign u then (0 : ℝ) else 1) ≤ 1 := by split_ifs <;> norm_num
  rcases common_point pl hW u v hτ0 hτ1 hτ0' hτ1' hq with ⟨huv, -⟩ | ⟨c, hc, hcu, hcv⟩ | ⟨-, hτ, -⟩
  · exact hinc (incidentTail_of pl hW hne s t (Or.inl huv))
  · rw [← pt_eq_piecePt pl hW] at hc
    have hcu' : c = u := pt_inj pl _ hc
    subst hcu'
    exact hinc (incidentTail_of pl hW hne s t hcv)
  · split_ifs at hτ <;> norm_num at hτ

/-- Non-adjacent edges that meet are the two strands of a `σ` letter: transverse. -/
theorem transverse (s t : (shadowOf pl hW hne).Strand) (hna : ¬ (shadowOf pl hW hne).Adjacent s t)
    (hmeet : ((shadowOf pl hW hne).seg s ∩ (shadowOf pl hW hne).seg t).Nonempty) :
    det ((shadowOf pl hW hne).dir s) ((shadowOf pl hW hne).dir t) ≠ 0 := by
  obtain ⟨q, hqs, hqt⟩ := hmeet
  rw [mem_seg_iff] at hqs hqt
  obtain ⟨τ, hτ0, hτ1, rfl⟩ := hqs
  obtain ⟨τ', hτ0', hτ1', hq⟩ := hqt
  set u := slotOf pl hW hne s with hu
  set v := slotOf pl hW hne t with hv
  rcases common_point pl hW u v hτ0 hτ1 hτ0' hτ1' hq with ⟨huv, -⟩ | ⟨c, -, hcu, hcv⟩ |
    ⟨hcol, -, -, m, hℓ, hS⟩
  · exact absurd ((adjacent_iff pl hW hne s t).2 (Or.inl huv.symm)) hna
  · exfalso
    apply hna
    rw [adjacent_iff, ← hu, ← hv]
    rcases hcu with hcu | hcu <;> rcases hcv with hcv | hcv
    · exact Or.inl (hcv.symm.trans hcu)
    · right; right; rw [← hcu, hcv, prev_next]
    · exact Or.inr (Or.inl (hcv.symm.trans hcu))
    · exact Or.inl (next_injective hW (hcv.symm.trans hcu))
  · rw [dir_eq, dir_eq, dir_slot_eq, dir_slot_eq]
    rw [← hu, ← hv, hcol]
    have hw := pl.w_pos (colOf v)
    rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, Shape.vec_pass, Shape.vec_pass] <;>
      cases xsign u <;> cases xsign v <;> simp [det] <;> push_cast <;> intro h0 <;> nlinarith [hw]

/-- A common interior point of two edges is a `σ` crossing (never a common slot). -/
theorem interior_meet {s t : (shadowOf pl hW hne).Strand} (hst : s ≠ t) {τ τ' : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hτ0' : 0 < τ') (hτ1' : τ' < 1)
    (hq : piecePt pl (slotOf pl hW hne s) τ = piecePt pl (slotOf pl hW hne t) τ') :
    colOf (slotOf pl hW hne s) = colOf (slotOf pl hW hne t) ∧
    ∃ m, letterAt W (colOf (slotOf pl hW hne s)) = .σ m ∧
      ((shapeOf (slotOf pl hW hne s) = .pass m (m + 1) ∧ shapeOf (slotOf pl hW hne t) = .pass (m + 1) m) ∨
       (shapeOf (slotOf pl hW hne s) = .pass (m + 1) m ∧ shapeOf (slotOf pl hW hne t) = .pass m (m + 1))) := by
  set u := slotOf pl hW hne s
  set v := slotOf pl hW hne t
  rcases common_point pl hW u v hτ0.le hτ1.le hτ0'.le hτ1'.le hq with ⟨huv, -⟩ | ⟨c, hc, hcu, -⟩ |
    ⟨hcol, -, -, m, hℓ, hS⟩
  · exact absurd (slotOf_injective pl hW hne huv) hst
  · exfalso
    have hend : ∃ τ₀ : ℝ, (τ₀ = 0 ∨ τ₀ = 1) ∧ pt pl W c.1 = piecePt pl u τ₀ := by
      rcases hcu with hcu | hcu
      · rw [hcu]; exact ⟨_, by cases xsign u <;> simp, pt_eq_piecePt pl hW u⟩
      · rw [hcu]; exact ⟨_, by cases xsign u <;> simp, pt_next_eq_piecePt pl hW u⟩
    obtain ⟨τ₀, hτ₀, he⟩ := hend
    rw [hc] at he
    unfold piecePt at he
    have := (shapeOf u).par_injective (pl.A_injective _ he)
    rcases hτ₀ with rfl | rfl <;> linarith
  · exact ⟨hcol, m, hℓ, hS⟩

/-- No point lies in the interior of three distinct edges. -/
theorem no_triple : ¬ ∃ s t r : (shadowOf pl hW hne).Strand, s ≠ t ∧ t ≠ r ∧ s ≠ r ∧
    ((shadowOf pl hW hne).interior s ∩ (shadowOf pl hW hne).interior t ∩
      (shadowOf pl hW hne).interior r).Nonempty := by
  rintro ⟨s, t, r, hst, htr, hsr, q, ⟨hqs, hqt⟩, hqr⟩
  rw [mem_interior_iff] at hqs hqt hqr
  obtain ⟨τ₁, h10, h11, rfl⟩ := hqs
  obtain ⟨τ₂, h20, h21, hq2⟩ := hqt
  obtain ⟨τ₃, h30, h31, hq3⟩ := hqr
  obtain ⟨hc12, m, hℓ, hS12⟩ := interior_meet pl hW hne hst h10 h11 h20 h21 hq2
  obtain ⟨hc13, m', hℓ', hS13⟩ := interior_meet pl hW hne hsr h10 h11 h30 h31 hq3
  rw [hℓ] at hℓ'
  obtain rfl := Letter.σ.inj hℓ'
  -- the shapes of `t` and `r` are both the other strand of the crossing: `t = r`
  have : shapeOf (slotOf pl hW hne t) = shapeOf (slotOf pl hW hne r) := by
    rcases hS12 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hS13 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · rw [h2, h2']
    · rw [h1] at h1'; cases h1'
    · rw [h1] at h1'; cases h1'
    · rw [h2, h2']
  exact htr (slotOf_injective pl hW hne (slot_eq_of_piece_eq hW pl (hc12.symm.trans hc13) this))

/-- The shadow of a closed word is generic. -/
theorem generic : (shadowOf pl hW hne).Generic where
  regular := regular pl hW hne
  tail_off := tail_off pl hW hne
  transverse := transverse pl hW hne
  no_triple := no_triple pl hW hne

/-- Every edge of the realization is nonvertical. -/
theorem nonvertical (s : (shadowOf pl hW hne).Strand) : ((shadowOf pl hW hne).dir s).1 ≠ 0 := by
  rw [dir_eq]; exact dir_slot_fst_ne_zero pl hW _

end Generic

/-! ## 8. The realization -/

/-- The grid realization of a nonempty closed word with the placement `pl`. -/
def realizeAt (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) : PLFront :=
  ⟨shadowOf pl hW hne, generic pl hW hne, nonvertical pl hW hne⟩

@[simp] theorem realizeAt_Γ (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) :
    (realizeAt pl hW hne).Γ = shadowOf pl hW hne := rfl

/-- The standard front circle `l₁ r₁`, the realization of the empty word (convention: `realize` is total
on `OWord`; the empty word is isolated under every move). -/
def stdCircleWord : OWord := ⟨[.l 1 true, .r 1], by decide⟩

theorem stdCircleWord_ne_nil : stdCircleWord.letters ≠ [] := by simp [stdCircleWord]

end

end SM.FrontRealize

namespace SM

open SM.FrontWord SM.FrontRealize

/-- FINAL §4: the grid realization `realize : OWord → PLFront` (standard placement; the empty word is
sent to the standard circle). -/
noncomputable def realize (W : OWord) : PLFront :=
  if h : W.letters = [] then realizeAt .std stdCircleWord.closed stdCircleWord_ne_nil
  else realizeAt .std W.closed h

theorem realize_eq_realizeAt (W : OWord) (h : W.letters ≠ []) : realize W = realizeAt .std W.closed h := by
  simp [realize, h]

theorem realize_nil (W : OWord) (h : W.letters = []) :
    realize W = realizeAt .std stdCircleWord.closed stdCircleWord_ne_nil := by
  simp [realize, h]

end SM
