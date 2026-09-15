import SM.FrontRealizeCorrespondence

/-! Front block, lane β, unit β2 (2026-09-14): module `SM/FrontRealizeGeometry.lean` (intended home).
Adopted design work/reports/front-block-design-FINAL-20260913.md (§5 rows 77-82, §8 risk 3: "one shared
grid-geometry module (column rectangles as `IsDisc`, `Clean`, `OutsideMatch` between two words agreeing
outside a column) built once and reused by 77-82").

# The grid realization, part 4: the shared grid geometry for the move rows

The move rows replace a factor of a closed word inside a block of consecutive columns.  This module
provides, for a realization `realizeAt pl hW hne`:
* the axis-parallel rectangles `rect a b H` as discs (`isDisc_rect`) and the *block rectangle*
  `blockRect pl a b H` spanning the columns `a, …, b−1`, with membership / interior / frontier
  characterizations;
* the height bound `hgt W`: the whole trace lies strictly between the heights `−hgt W` and `hgt W`
  (`abs_piecePt_snd_lt`), so a block rectangle of height `hgt W` is met only through its two vertical sides;
* inside / outside: a piece of an exterior column is outside the block (touching it at most at a boundary
  cut slot), a piece of a block column is inside (`piecePt_mem_interior_blockRect_of`, …); the same for
  traversal points (`eval_eq_piecePt`);
* `Clean (blockRect pl a b (hgt W)) (realizeAt pl hW hne).diagram` under the exit criterion "every
  component has a strand in an exterior column" (`clean_blockRect`);
* the crossing of a `σ` letter lies in the open block iff its column does (`crossingPoint_mem_interior_iff`);
* two closed words `X ++ P ++ Y`, `X ++ P' ++ Y` with NONEMPTY factors of the same typing effect
  (`SameEffect`, the hypothesis shape of `Word.Closed.replace`), realized with placements agreeing outside
  the block (`PlAgree`: same boundaries up to `|X|`, the same boundaries after the blocks), bundled as
  `BlockSetup`: the exterior slots correspond (`extSlot`; `pt`, `xsign`, `colOf`, `next`, `prev`
  compatibility), and the two realizations agree outside the block rectangle in the accepted sense —
  `BlockSetup.outsideMatch : OutsideMatch B.U B.F.diagram B.F'.diagram` (points, directions, outer
  crossings with over/under occurrences), hence `AgreeOutside`.

Two limitations, for the move rows (recorded for FINAL §5): (i) the deletion moves with an EMPTY factor
(`P' = []`: type I, the empty zigzag) cannot be a literal exterior match of the two standard realizations —
the columns of `Y` shift and no letter realizes a straight through-strand — so rows 77 and 80 need a padded
or planar-isotopy argument (e.g. compare the curl with the empty zigzag `l_m r_{m+1}`, which is a
crossing-free single arc, both factors nonempty); (ii) the component bijection of `MoveMatch` is not
provided here: it needs the extra hypothesis that the two blocks connect their boundary slots in the same
way (true for the Reidemeister patterns, false for the smoothing), and the induced bijection of cycles.

All declarations live in `SM.FrontRealize`.  Checked with `lake env lean` (sorry-free, standard axioms). -/

namespace SM.FrontRealize

open SM SM.Link SM.FrontWord SM.FrontWord.Letter

noncomputable section

/-! ## 1. Rectangles -/

/-- The closed axis-parallel rectangle `[a, b] × [−H, H]`. -/
def rect (a b H : ℝ) : Set Plane := Set.Icc a b ×ˢ Set.Icc (-H) H

theorem mem_rect_iff {a b H : ℝ} {q : Plane} : q ∈ rect a b H ↔ (a ≤ q.1 ∧ q.1 ≤ b) ∧ (-H ≤ q.2 ∧ q.2 ≤ H) := by
  simp only [rect, Set.mem_prod, Set.mem_Icc]

theorem interior_rect (a b H : ℝ) : interior (rect a b H) = Set.Ioo a b ×ˢ Set.Ioo (-H) H := by
  rw [rect, interior_prod_eq, interior_Icc, interior_Icc]

theorem mem_interior_rect_iff {a b H : ℝ} {q : Plane} :
    q ∈ interior (rect a b H) ↔ (a < q.1 ∧ q.1 < b) ∧ (-H < q.2 ∧ q.2 < H) := by
  rw [interior_rect]; simp only [Set.mem_prod, Set.mem_Ioo]

theorem frontier_rect {a b H : ℝ} (hab : a ≤ b) (hH : 0 ≤ H) :
    frontier (rect a b H) = Set.Icc a b ×ˢ {-H, H} ∪ {a, b} ×ˢ Set.Icc (-H) H := by
  rw [rect, frontier_prod_eq, closure_Icc, closure_Icc, frontier_Icc hab, frontier_Icc (by linarith)]

/-- A point of the frontier of a rectangle with `|z| < H` lies on one of the two vertical sides. -/
theorem mem_frontier_rect_iff {a b H : ℝ} (hab : a ≤ b) (hH : 0 ≤ H) {q : Plane} (hz : |q.2| < H) :
    q ∈ frontier (rect a b H) ↔ (q.1 = a ∨ q.1 = b) ∧ (-H ≤ q.2 ∧ q.2 ≤ H) := by
  rw [frontier_rect hab hH]
  have h1 : q.2 ≠ -H := by intro h; rw [abs_lt] at hz; linarith
  have h2 : q.2 ≠ H := by intro h; rw [abs_lt] at hz; linarith
  simp [Set.mem_prod, Set.mem_Icc, h1, h2]

/-- Every rectangle with `a < b`, `0 < H` is a disc in the accepted sense. -/
theorem isDisc_rect {a b H : ℝ} (hab : a < b) (hH : 0 < H) : IsDisc (rect a b H) := by
  refine ⟨(convex_Icc a b).prod (convex_Icc (-H) H), isCompact_Icc.prod isCompact_Icc, ?_⟩
  refine ⟨((a + b) / 2, 0), ?_⟩
  rw [mem_interior_rect_iff]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, hH⟩

/-! ## 2. Block rectangles and the height bound -/

/-- The block rectangle of the columns `a, …, b − 1` of a placement, of half-height `H`. -/
def blockRect (pl : Placement) (a b : ℕ) (H : ℝ) : Set Plane := rect (pl.x a) (pl.x b) H

theorem isDisc_blockRect (pl : Placement) {a b : ℕ} (hab : a < b) {H : ℝ} (hH : 0 < H) :
    IsDisc (blockRect pl a b H) := isDisc_rect (pl.x_lt_x_iff.2 hab) hH

/-- The half-height used for the block rectangles of a word: strictly above every height of the trace. -/
def hgt (W : Word) : ℝ := 2 * W.length + 3

theorem hgt_pos (W : Word) : 0 < hgt W := by unfold hgt; positivity

section Height

variable (pl : Placement) {W : Word} (hW : W.Closed)
include hW

/-- Every slot lies at height `≥ −(2|W| + 2)` and `≤ 0`. -/
theorem pt_snd_bounds (u : Slot W) : -(2 * (W.length : ℝ) + 2) ≤ (pt pl W u.1).2 ∧ (pt pl W u.1).2 ≤ 0 := by
  obtain ⟨⟨k, p⟩, hs⟩ := u
  have hb := isSlot_bound W hs
  simp only at hb
  by_cases hp : p = 0
  · subst hp
    rw [pt_cusp]
    simp only
    rcases hs with ⟨-, hk, -⟩ | ⟨h0, -⟩
    · obtain ⟨D⟩ := decomp hW k hk
      have hm : (letterAt W k).idx ≤ 2 * W.length + 1 := by
        have h1 := D.hm
        have h2 := D.length_c
        have h3 := cutLen_le W k
        unfold cutLen at h3
        have h4 : k ≤ W.length := hk.le
        omega
      have hm' : ((letterAt W k).idx : ℝ) ≤ 2 * W.length + 1 := by exact_mod_cast hm
      constructor <;> linarith
    · simp at h0
  · rw [pt_cut pl W hp]
    simp only
    have : (p : ℝ) ≤ 2 * W.length := by exact_mod_cast hb.2
    constructor <;> linarith

/-- The height of every point of a piece lies in `[−(2|W| + 2), 0]`. -/
theorem piecePt_snd_bounds (u : Slot W) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    -(2 * (W.length : ℝ) + 2) ≤ (piecePt pl u τ).2 ∧ (piecePt pl u τ).2 ≤ 0 := by
  obtain ⟨-, -, hu, hn⟩ := piece_spec pl hW u
  have hb1 := pt_snd_bounds pl hW u
  have hb2 := pt_snd_bounds pl hW (next hW u)
  unfold piecePt
  simp only [Placement.A_snd, Shape.par, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
  cases hx : xsign u
  · rw [hx] at hu hn
    simp only [Bool.false_eq_true, ↓reduceIte] at hu hn
    rw [hu] at hb1; rw [hn] at hb2
    simp only [Placement.A_snd] at hb1 hb2
    constructor <;> nlinarith
  · rw [hx] at hu hn
    simp only [↓reduceIte] at hu hn
    rw [hu] at hb1; rw [hn] at hb2
    simp only [Placement.A_snd] at hb1 hb2
    constructor <;> nlinarith

/-- No point of the trace reaches the height `hgt W` in absolute value. -/
theorem abs_piecePt_snd_lt (u : Slot W) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) : |(piecePt pl u τ).2| < hgt W := by
  obtain ⟨hlo, hhi⟩ := piecePt_snd_bounds pl hW u h0 h1
  unfold hgt
  rw [abs_lt]; constructor <;> linarith

theorem abs_piecePt_snd_lt' (u : Slot W) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) {H : ℝ} (hH : hgt W ≤ H) :
    |(piecePt pl u τ).2| < H := lt_of_lt_of_le (abs_piecePt_snd_lt pl hW u h0 h1) hH

end Height

/-! ## 3. Inside and outside a block -/

section InOut

variable (pl : Placement) {W : Word} (hW : W.Closed)
include hW

/-- The x-coordinate of a piece point lies in the strip of its column. -/
theorem piecePt_fst_mem (u : Slot W) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    pl.x (colOf u) ≤ (piecePt pl u τ).1 ∧ (piecePt pl u τ).1 ≤ pl.x (colOf u + 1) := by
  obtain ⟨hp0, hp1⟩ := (shapeOf u).par_fst_mem h0 h1
  exact pl.A_fst_mem hp0 hp1

/-- A piece point on the left boundary of its column is the left end of the piece. -/
theorem piecePt_fst_eq_left (u : Slot W) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (h : (piecePt pl u τ).1 = pl.x (colOf u)) : τ = 0 ∧ (shapeOf u).left.1 = 0 := by
  unfold piecePt at h
  simp only [Placement.A_fst] at h
  have hw := pl.w_pos (colOf u)
  have : ((shapeOf u).par τ).1 = 0 := by
    have : pl.w (colOf u) * ((shapeOf u).par τ).1 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  exact Shape.par_fst_eq_zero h0 this

/-- A piece point on the right boundary of its column is the right end of the piece. -/
theorem piecePt_fst_eq_right (u : Slot W) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (h : (piecePt pl u τ).1 = pl.x (colOf u + 1)) : τ = 1 ∧ (shapeOf u).right.1 = 1 := by
  unfold piecePt at h
  simp only [Placement.A_fst] at h
  have hw := pl.w_pos (colOf u)
  rw [← pl.x_add_w] at h
  have : ((shapeOf u).par τ).1 = 1 := by
    have : pl.w (colOf u) * (((shapeOf u).par τ).1 - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  exact Shape.par_fst_eq_one h1 this

/-- A piece of a column left of the block lies outside the open block; it touches the block only at the
left side, at its right end. -/
theorem piecePt_fst_le_of_col_lt (u : Slot W) {a : ℕ} (hk : colOf u + 1 ≤ a) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (piecePt pl u τ).1 ≤ pl.x a := by
  have := (piecePt_fst_mem pl hW u h0 h1).2
  exact le_trans this (pl.x_le_x_iff.2 hk)

theorem piecePt_fst_ge_of_col_ge (u : Slot W) {b : ℕ} (hk : b ≤ colOf u) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    pl.x b ≤ (piecePt pl u τ).1 := by
  have := (piecePt_fst_mem pl hW u h0 h1).1
  exact le_trans (pl.x_le_x_iff.2 hk) this

/-- An exterior piece never enters the open block. -/
theorem piecePt_notMem_interior_of_ext (u : Slot W) {a b : ℕ}
    (hk : colOf u + 1 ≤ a ∨ b ≤ colOf u) {H : ℝ} {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    piecePt pl u τ ∉ interior (blockRect pl a b H) := by
  rw [blockRect, mem_interior_rect_iff]
  rintro ⟨⟨hlt1, hlt2⟩, -⟩
  rcases hk with hk | hk
  · exact absurd (piecePt_fst_le_of_col_lt pl hW u hk h0 h1) (not_le.2 hlt1)
  · exact absurd (piecePt_fst_ge_of_col_ge pl hW u hk h0 h1) (not_le.2 hlt2)

/-- An exterior piece point in the closed block is an end of the piece on a boundary side. -/
theorem piecePt_mem_blockRect_of_ext (u : Slot W) {a b : ℕ} (hab : a ≤ b)
    (hk : colOf u + 1 ≤ a ∨ b ≤ colOf u) {H : ℝ} {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (h : piecePt pl u τ ∈ blockRect pl a b H) :
    (τ = 1 ∧ colOf u + 1 = a ∧ (piecePt pl u τ).1 = pl.x a) ∨ (τ = 0 ∧ colOf u = b ∧ (piecePt pl u τ).1 = pl.x b) := by
  rw [blockRect, mem_rect_iff] at h
  obtain ⟨⟨hx1, hx2⟩, -⟩ := h
  rcases hk with hk | hk
  · left
    have hle := piecePt_fst_le_of_col_lt pl hW u hk h0 h1
    have hx : (piecePt pl u τ).1 = pl.x a := le_antisymm hle hx1
    have hmem := (piecePt_fst_mem pl hW u h0 h1).2
    have hle2 : pl.x a ≤ pl.x (colOf u + 1) := hx ▸ hmem
    have hka : a ≤ colOf u + 1 := pl.x_le_x_iff.1 hle2
    have hka' : colOf u + 1 = a := le_antisymm hk hka
    refine ⟨?_, hka', hx⟩
    exact (piecePt_fst_eq_right pl hW u h0 h1 (by rw [hka']; exact hx)).1
  · right
    have hge := piecePt_fst_ge_of_col_ge pl hW u hk h0 h1
    have hx : (piecePt pl u τ).1 = pl.x b := le_antisymm hx2 hge
    have hmem := (piecePt_fst_mem pl hW u h0 h1).1
    have hle2 : pl.x (colOf u) ≤ pl.x b := hx ▸ hmem
    have hkb : colOf u ≤ b := pl.x_le_x_iff.1 hle2
    have hkb' : colOf u = b := le_antisymm hkb hk
    refine ⟨?_, hkb', hx⟩
    exact (piecePt_fst_eq_left pl hW u h0 h1 (by rw [hkb']; exact hx)).1

/-- A piece of a block column lies in the closed block (of height `hgt W`). -/
theorem piecePt_mem_blockRect_of_int (u : Slot W) {a b : ℕ} (hka : a ≤ colOf u) (hkb : colOf u + 1 ≤ b)
    {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) {H : ℝ} (hH : hgt W ≤ H) : piecePt pl u τ ∈ blockRect pl a b H := by
  rw [blockRect, mem_rect_iff]
  obtain ⟨hx1, hx2⟩ := piecePt_fst_mem pl hW u h0 h1
  have hz := abs_piecePt_snd_lt' pl hW u h0 h1 hH
  rw [abs_lt] at hz
  exact ⟨⟨le_trans (pl.x_le_x_iff.2 hka) hx1, le_trans hx2 (pl.x_le_x_iff.2 hkb)⟩, hz.1.le, hz.2.le⟩

/-- An interior point (`0 < τ < 1`) of a piece of a block column lies in the open block. -/
theorem piecePt_mem_interior_blockRect_of_int (u : Slot W) {a b : ℕ} (hka : a ≤ colOf u) (hkb : colOf u + 1 ≤ b)
    {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {H : ℝ} (hH : hgt W ≤ H) : piecePt pl u τ ∈ interior (blockRect pl a b H) := by
  rw [blockRect, mem_interior_rect_iff]
  obtain ⟨hx1, hx2⟩ := piecePt_fst_mem pl hW u h0.le h1.le
  have hz := abs_piecePt_snd_lt' pl hW u h0.le h1.le hH
  rw [abs_lt] at hz
  refine ⟨⟨?_, ?_⟩, hz.1, hz.2⟩
  · rcases lt_or_eq_of_le hx1 with h | h
    · exact lt_of_le_of_lt (pl.x_le_x_iff.2 hka) h
    · exfalso
      obtain ⟨hτ, -⟩ := piecePt_fst_eq_left pl hW u h0.le h1.le h.symm
      linarith
  · rcases lt_or_eq_of_le hx2 with h | h
    · exact lt_of_lt_of_le h (pl.x_le_x_iff.2 hkb)
    · exfalso
      obtain ⟨hτ, -⟩ := piecePt_fst_eq_right pl hW u h0.le h1.le h
      linarith

/-- A piece point on the frontier of the block of height `hgt W` lies on a vertical side. -/
theorem piecePt_mem_frontier_iff (u : Slot W) {a b : ℕ} (hab : a ≤ b) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    {H : ℝ} (hH : hgt W ≤ H) :
    piecePt pl u τ ∈ frontier (blockRect pl a b H) ↔
      (piecePt pl u τ).1 = pl.x a ∨ (piecePt pl u τ).1 = pl.x b := by
  rw [blockRect, mem_frontier_rect_iff (pl.x_le_x_iff.2 hab) (le_trans (hgt_pos W).le hH)
    (abs_piecePt_snd_lt' pl hW u h0 h1 hH)]
  have hz := abs_piecePt_snd_lt' pl hW u h0 h1 hH
  rw [abs_lt] at hz
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, hz.1.le, hz.2.le⟩

/-- A piece point on a cut line `pl.x j` is an end of the piece at a cut slot: the left end if `j = colOf u`,
the right end if `j = colOf u + 1`. -/
theorem piecePt_fst_eq_x (u : Slot W) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) {j : ℕ}
    (h : (piecePt pl u τ).1 = pl.x j) :
    (j = colOf u ∧ τ = 0) ∨ (j = colOf u + 1 ∧ τ = 1) := by
  unfold piecePt at h
  simp only [Placement.A_fst] at h
  obtain ⟨hp0, hp1⟩ := (shapeOf u).par_fst_mem h0 h1
  rcases pl.A_fst_eq_x hp0 hp1 h with ⟨hj, hu⟩ | ⟨hj, hu⟩
  · exact Or.inl ⟨hj, (Shape.par_fst_eq_zero h0 hu).1⟩
  · exact Or.inr ⟨hj, (Shape.par_fst_eq_one h1 hu).1⟩

variable (hne : W ≠ [])

/-- Traversal points evaluate to piece points. -/
theorem eval_eq_piecePt (p : (realizeAt pl hW hne).Γ.Pt) :
    (realizeAt pl hW hne).Γ.eval p =
      piecePt pl (slotOf pl hW hne ⟨p.1, p.2.1⟩)
        (if xsign (slotOf pl hW hne ⟨p.1, p.2.1⟩) then p.2.2.val else 1 - p.2.2.val) := by
  obtain ⟨i, j, t⟩ := p
  exact edgePoint_eq pl hW hne ⟨i, j⟩ t.val

/-- The traversal point of a strand `s` at parameter `t` (the edge point). -/
def travPt (s : (realizeAt pl hW hne).Γ.Strand) (t : Set.Ico (0 : ℝ) 1) : (realizeAt pl hW hne).Γ.Pt :=
  ⟨s.1, (s.2, t)⟩

theorem eval_travPt (s : (realizeAt pl hW hne).Γ.Strand) (t : Set.Ico (0 : ℝ) 1) :
    (realizeAt pl hW hne).Γ.eval (travPt pl hW hne s t) =
      piecePt pl (slotOf pl hW hne s) (if xsign (slotOf pl hW hne s) then t.val else 1 - t.val) :=
  edgePoint_eq pl hW hne s t.val

/-- The strand of a traversal point. -/
def strandPt (p : (realizeAt pl hW hne).Γ.Pt) : (realizeAt pl hW hne).Γ.Strand := ⟨p.1, p.2.1⟩

theorem travPt_strandPt (p : (realizeAt pl hW hne).Γ.Pt) : travPt pl hW hne (strandPt pl hW hne p) p.2.2 = p := rfl

/-- The parameter of a traversal point along its piece (`t` or `1 − t`), in `[0, 1]`. -/
def parOf (p : (realizeAt pl hW hne).Γ.Pt) : ℝ :=
  if xsign (slotOf pl hW hne (strandPt pl hW hne p)) then p.2.2.val else 1 - p.2.2.val

theorem parOf_mem (p : (realizeAt pl hW hne).Γ.Pt) : 0 ≤ parOf pl hW hne p ∧ parOf pl hW hne p ≤ 1 := by
  unfold parOf
  have := p.2.2.2
  split_ifs <;> constructor <;> linarith [this.1, this.2]

theorem eval_eq_piecePt_parOf (p : (realizeAt pl hW hne).Γ.Pt) :
    (realizeAt pl hW hne).Γ.eval p = piecePt pl (slotOf pl hW hne (strandPt pl hW hne p)) (parOf pl hW hne p) :=
  eval_eq_piecePt pl hW hne p

/-- A traversal point whose piece parameter is an end has parameter `0`: the tail point of its strand (its
parameter `t < 1` excludes the head). -/
theorem parOf_eq_end (p : (realizeAt pl hW hne).Γ.Pt) (h : parOf pl hW hne p = 0 ∨ parOf pl hW hne p = 1) :
    p.2.2.val = 0 ∧ (realizeAt pl hW hne).Γ.eval p = pt pl W (slotOf pl hW hne (strandPt pl hW hne p)).1 := by
  have ht := p.2.2.2
  unfold parOf at h
  have hval : p.2.2.val = 0 := by
    split_ifs at h with hx <;> rcases h with h | h <;> first | exact h | linarith [ht.1, ht.2]
  refine ⟨hval, ?_⟩
  rw [eval_eq_piecePt_parOf, pt_eq_piecePt pl hW]
  unfold parOf
  rw [hval]
  simp

end InOut

/-! ## 4. Cleanness of a block rectangle -/

section Clean

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])
include hW

/-- A traversal point on the frontier of the block is the tail point of a strand starting at a boundary cut
slot. -/
theorem frontier_pt (p : (realizeAt pl hW hne).Γ.Pt) {a b : ℕ} (hab : a ≤ b) {H : ℝ} (hH : hgt W ≤ H)
    (h : (realizeAt pl hW hne).Γ.eval p ∈ frontier (blockRect pl a b H)) :
    p.2.2.val = 0 ∧ (realizeAt pl hW hne).Γ.eval p = pt pl W (slotOf pl hW hne (strandPt pl hW hne p)).1 := by
  rw [eval_eq_piecePt_parOf] at h
  obtain ⟨h0, h1⟩ := parOf_mem pl hW hne p
  rw [piecePt_mem_frontier_iff pl hW _ hab h0 h1 hH] at h
  apply parOf_eq_end
  rcases h with h | h
  · rcases piecePt_fst_eq_x pl hW _ h0 h1 h with ⟨-, hτ⟩ | ⟨-, hτ⟩
    · exact Or.inl hτ
    · exact Or.inr hτ
  · rcases piecePt_fst_eq_x pl hW _ h0 h1 h with ⟨-, hτ⟩ | ⟨-, hτ⟩
    · exact Or.inl hτ
    · exact Or.inr hτ

/-- Two traversal points with the same evaluation on the frontier coincide. -/
theorem frontier_injOn_blockRect {a b : ℕ} (hab : a ≤ b) {H : ℝ} (hH : hgt W ≤ H) :
    Set.InjOn (realizeAt pl hW hne).Γ.eval
      {p | (realizeAt pl hW hne).Γ.eval p ∈ frontier (blockRect pl a b H)} := by
  intro p hp q hq hpq
  obtain ⟨hp0, hpe⟩ := frontier_pt pl hW hne p hab hH hp
  obtain ⟨hq0, hqe⟩ := frontier_pt pl hW hne q hab hH hq
  rw [hpe, hqe] at hpq
  have hslot : slotOf pl hW hne (strandPt pl hW hne p) = slotOf pl hW hne (strandPt pl hW hne q) :=
    pt_inj pl _ hpq
  have hstr : strandPt pl hW hne p = strandPt pl hW hne q := slotOf_injective pl hW hne hslot
  rw [← travPt_strandPt pl hW hne p, ← travPt_strandPt pl hW hne q, hstr]
  congr 1
  exact Subtype.ext (hp0.trans hq0.symm)

/-- The exit criterion for the block `[a, b)`: every component has a strand in an exterior column. -/
def ExitsBlock (a b : ℕ) : Prop :=
  ∀ i : Fin (realizeAt pl hW hne).Γ.c, ∃ s : (realizeAt pl hW hne).Γ.Strand, s.1 = i ∧
    (colOf (slotOf pl hW hne s) + 1 ≤ a ∨ b ≤ colOf (slotOf pl hW hne s))

/-- The midpoint of an exterior strand lies strictly outside the block rectangle. -/
theorem midpoint_notMem_blockRect (s : (realizeAt pl hW hne).Γ.Strand) {a b : ℕ}
    (hk : colOf (slotOf pl hW hne s) + 1 ≤ a ∨ b ≤ colOf (slotOf pl hW hne s)) {H : ℝ} :
    (realizeAt pl hW hne).Γ.eval (travPt pl hW hne s ⟨1 / 2, by norm_num, by norm_num⟩) ∉ blockRect pl a b H := by
  rw [eval_travPt]
  have hτ : (if xsign (slotOf pl hW hne s) then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by split_ifs <;> norm_num
  rw [hτ]
  intro h
  have hab : a ≤ b := by
    rw [blockRect, mem_rect_iff] at h
    obtain ⟨⟨hx1, hx2⟩, -⟩ := h
    exact pl.x_le_x_iff.1 (le_trans hx1 hx2)
  rcases piecePt_mem_blockRect_of_ext pl hW _ hab hk (by norm_num) (by norm_num) h with ⟨hτ', -⟩ | ⟨hτ', -⟩ <;>
    norm_num at hτ'

/-- The block rectangle of height `hgt W` is met cleanly whenever every component has an exterior strand:
the frontier is met only at boundary cut slots, each once; no component lies inside. -/
theorem clean_blockRect {a b : ℕ} (hab : a ≤ b) {H : ℝ} (hH : hgt W ≤ H) (hexit : ExitsBlock pl hW hne a b) :
    Clean (blockRect pl a b H) (realizeAt pl hW hne).diagram where
  frontier_injOn := frontier_injOn_blockRect pl hW hne hab hH
  exits := fun i => by
    obtain ⟨⟨i', j⟩, hs, hk⟩ := hexit i
    simp only at hs
    subst hs
    exact ⟨(j, ⟨1 / 2, by norm_num, by norm_num⟩), midpoint_notMem_blockRect pl hW hne ⟨i', j⟩ hk⟩

/-- The double point of the crossing of `σ_m` at column `k` lies in the open block `[a, b)` iff its column
does. -/
theorem crossingPoint_mem_interior_iff {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) {a b : ℕ}
    {H : ℝ} (hH : hgt W ≤ H) :
    (realizeAt pl hW hne).Γ.crossingPoint (crossingOf pl hW hne hk hℓ) ∈ interior (blockRect pl a b H) ↔
      a ≤ k ∧ k < b := by
  rw [crossingPoint_crossingOf, blockRect, mem_interior_rect_iff]
  simp only
  have hz : -(m : ℝ) - 1 / 2 ∈ Set.Ioo (-H) H := by
    obtain ⟨-, hlen, -, -, -⟩ := σ_facts hW hk hℓ
    have h3 := cutLen_le W k
    unfold cutLen at h3
    have hm : (m : ℝ) ≤ 2 * W.length := by exact_mod_cast (by omega : m ≤ 2 * W.length)
    unfold hgt at hH
    constructor <;> linarith
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    constructor
    · by_contra hc
      rw [not_le] at hc
      have := pl.mid_lt_x_succ k
      have := pl.x_le_x_iff.2 (show k + 1 ≤ a by omega)
      linarith
    · by_contra hc
      rw [not_lt] at hc
      have := pl.x_lt_mid k
      have := pl.x_le_x_iff.2 hc
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, hz.1, hz.2⟩
    · exact lt_of_le_of_lt (pl.x_le_x_iff.2 h1) (pl.x_lt_mid k)
    · exact lt_of_lt_of_le (pl.mid_lt_x_succ k) (pl.x_le_x_iff.2 h2)

end Clean

/-! ## 5. Two words agreeing outside a block: the exterior slot correspondence

`W = X ++ P ++ Y` and `W' = X ++ P' ++ Y` with the same typing effect of the factors `P`, `P'` (as in
`Word.Closed.replace`).  The block of `W` is the columns `|X|, …, |X| + |P| − 1`; outside it the two words
have the same cuts, letters and bits, up to the index shift `shiftIdx` on the columns after the block. -/

section Block

variable (X P Y P' : Word)

/-- The column/cut index of `W'` corresponding to an exterior index of `W`. -/
def shiftIdx (k : ℕ) : ℕ := if k ≤ X.length then k else k - (X.length + P.length) + (X.length + P'.length)

/-- An index is *exterior* (for cuts) when it lies before or at the left boundary, or at or after the right
boundary. -/
def ExtCut (k : ℕ) : Prop := k ≤ X.length ∨ X.length + P.length ≤ k

/-- An index is an *exterior column* when it lies strictly before the block or at or after it. -/
def ExtCol (k : ℕ) : Prop := k + 1 ≤ X.length ∨ X.length + P.length ≤ k

/-- The same typing effect of the factors: `run (X ++ P) [] = run (X ++ P') []`. -/
def SameEffect : Prop := Word.run (X ++ P) [] = Word.run (X ++ P') []

/-- A slot is *exterior* when its cut (for a cut slot) or its column (for a cusp vertex) is exterior. -/
def IsExtSlot (s : ℕ × ℕ) : Prop := if s.2 = 0 then ExtCol X P s.1 else ExtCut X P s.1

/-- The exterior slot of `W'` corresponding to an exterior slot of `W`. -/
def extPair (s : ℕ × ℕ) : ℕ × ℕ := (shiftIdx X P P' s.1, s.2)

/-- The exterior slots of `W`. -/
abbrev ExtSlot : Type := {u : Slot (X ++ P ++ Y) // IsExtSlot X P u.1}

theorem shiftIdx_of_le {k : ℕ} (hk : k ≤ X.length) : shiftIdx X P P' k = k := by simp [shiftIdx, hk]

theorem ExtCol.extCut {k : ℕ} (h : ExtCol X P k) : ExtCut X P k := by
  unfold ExtCol at h; unfold ExtCut; omega

theorem ExtCol.extCut_succ {k : ℕ} (h : ExtCol X P k) : ExtCut X P (k + 1) := by
  unfold ExtCol at h; unfold ExtCut; omega

theorem sameEffect_of_replace (hW : (X ++ P ++ Y).Closed)
    (h : ∀ c c' : Cuts, Word.run P c = some c' → Word.run P' c = some c') : SameEffect X P P' := by
  obtain ⟨c₀, c₁, hX, hP, -⟩ := hW.exists_run
  unfold SameEffect
  rw [Word.run_append, Word.run_append, hX, Option.bind_some, Option.bind_some, hP, h c₀ c₁ hP]

theorem SameEffect.symm (h : SameEffect X P P') : SameEffect X P' P := Eq.symm h

theorem extPair_cusp (k : ℕ) : extPair X P P' (k, 0) = (shiftIdx X P P' k, 0) := rfl

theorem extPair_cut (k p : ℕ) : extPair X P P' (k, p) = (shiftIdx X P P' k, p) := rfl

-- The block is nonempty (`P ≠ []`): the left and right boundary cuts differ.  (The deletion moves with
-- `P' = []` cannot be modelled by a literal exterior match; see the module docstring, section 5.)
variable (hP : P ≠ [])
include hP

theorem P_length_pos : 0 < P.length := List.length_pos_iff_ne_nil.2 hP

theorem shiftIdx_of_ge {k : ℕ} (hk : X.length + P.length ≤ k) :
    shiftIdx X P P' k = k - (X.length + P.length) + (X.length + P'.length) := by
  have := P_length_pos P hP
  unfold shiftIdx
  split_ifs with h
  · omega
  · rfl

theorem shiftIdx_succ {k : ℕ} (h : ExtCol X P k) : shiftIdx X P P' (k + 1) = shiftIdx X P P' k + 1 := by
  have := P_length_pos P hP
  unfold ExtCol at h
  unfold shiftIdx
  split_ifs <;> omega

theorem shiftIdx_pred {k : ℕ} (h : ExtCol X P (k - 1)) (hk : 1 ≤ k) :
    shiftIdx X P P' (k - 1) = shiftIdx X P P' k - 1 := by
  have := P_length_pos P hP
  unfold ExtCol at h
  unfold shiftIdx
  split_ifs <;> omega

theorem shiftIdx_le_length {k : ℕ} (h : ExtCut X P k) (hk : k ≤ (X ++ P ++ Y).length) :
    shiftIdx X P P' k ≤ (X ++ P' ++ Y).length := by
  have := P_length_pos P hP
  unfold ExtCut at h
  simp only [List.length_append] at hk ⊢
  unfold shiftIdx
  split_ifs <;> omega

theorem shiftIdx_lt_length {k : ℕ} (h : ExtCol X P k) (hk : k < (X ++ P ++ Y).length) :
    shiftIdx X P P' k < (X ++ P' ++ Y).length := by
  have := P_length_pos P hP
  unfold ExtCol at h
  simp only [List.length_append] at hk ⊢
  unfold shiftIdx
  split_ifs <;> omega

/-- Exterior letters agree (after the shift). -/
theorem letterAt_ext {k : ℕ} (h : ExtCol X P k) :
    letterAt (X ++ P ++ Y) k = letterAt (X ++ P' ++ Y) (shiftIdx X P P' k) := by
  rcases h with h | h
  · rw [shiftIdx_of_le X P P' (by omega)]
    unfold letterAt
    rw [List.append_assoc, List.append_assoc, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [shiftIdx_of_ge X P P' hP h]
    unfold letterAt
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append]; omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_append]; omega)]
    congr 1
    simp only [List.length_append]; omega

variable (hE : SameEffect X P P')
include hE

/-- Exterior cuts agree (after the shift). -/
theorem cut_ext {k : ℕ} (h : ExtCut X P k) : cut (X ++ P ++ Y) k = cut (X ++ P' ++ Y) (shiftIdx X P P' k) := by
  rcases h with h | h
  · rw [shiftIdx_of_le X P P' h]
    unfold cut
    rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length h, List.take_append_of_le_length h]
  · rw [shiftIdx_of_ge X P P' hP h]
    unfold cut
    have e1 : (X ++ P ++ Y).take k = (X ++ P) ++ Y.take (k - (X ++ P).length) := by
      rw [List.take_append, List.take_of_length_le (by simp only [List.length_append]; omega)]
    have e2 : (X ++ P' ++ Y).take (k - (X.length + P.length) + (X.length + P'.length)) =
        (X ++ P') ++ Y.take (k - (X ++ P).length) := by
      rw [List.take_append, List.take_of_length_le (by simp only [List.length_append]; omega)]
      congr 2
      simp only [List.length_append]; omega
    rw [e1, e2, Word.run_append (X ++ P), Word.run_append (X ++ P'), hE]

theorem bit_ext {k : ℕ} (h : ExtCut X P k) (p : ℕ) :
    bit (X ++ P ++ Y) k p = bit (X ++ P' ++ Y) (shiftIdx X P P' k) p := by
  rw [bit_eq, bit_eq, cut_ext X P Y P' hP hE h]

theorem isSlot_ext {s : ℕ × ℕ} (hs : IsSlot (X ++ P ++ Y) s) (he : IsExtSlot X P s) :
    IsSlot (X ++ P' ++ Y) (extPair X P P' s) := by
  obtain ⟨k, p⟩ := s
  unfold IsExtSlot at he
  simp only at he
  rcases hs with ⟨hp0, hk, hσ⟩ | ⟨hp1, hpk, hkn⟩
  · simp only at hp0 hk hσ
    subst hp0
    rw [if_pos rfl] at he
    left
    refine ⟨rfl, shiftIdx_lt_length X P Y P' hP he hk, ?_⟩
    show (letterAt (X ++ P' ++ Y) (shiftIdx X P P' k)).isCrossing = false
    rw [← letterAt_ext X P Y P' hP he]; exact hσ
  · simp only at hp1 hpk hkn
    rw [if_neg (by omega)] at he
    right
    refine ⟨hp1, ?_, shiftIdx_le_length X P Y P' hP he hkn⟩
    show p ≤ (cut (X ++ P' ++ Y) (shiftIdx X P P' k)).length
    rw [← cut_ext X P Y P' hP hE he]; exact hpk

/-- The corresponding slot of `W'`. -/
def extSlot (u : ExtSlot X P Y) : Slot (X ++ P' ++ Y) := ⟨extPair X P P' u.1.1, isSlot_ext X P Y P' hP hE u.1.2 u.2⟩

theorem extSlot_val (u : ExtSlot X P Y) : (extSlot X P Y P' hP hE u).1 = extPair X P P' u.1.1 := rfl

end Block

/-! ### Placements agreeing outside the block -/

section BlockPlacement

variable (X P Y P' : Word) (pl pl' : Placement)

/-- Two placements agree outside the block: the same boundaries up to `|X|` and the same boundaries after the
blocks (shifted). -/
def PlAgree : Prop := ∀ k, ExtCut X P k → pl.x k = pl'.x (shiftIdx X P P' k)

theorem plAgree_of (hP : P ≠ []) (hlo : ∀ k ≤ X.length, pl.x k = pl'.x k)
    (hhi : ∀ j, pl.x (X.length + P.length + j) = pl'.x (X.length + P'.length + j)) : PlAgree X P P' pl pl' := by
  intro k hk
  rcases hk with hk | hk
  · rw [shiftIdx_of_le X P P' hk]; exact hlo k hk
  · rw [shiftIdx_of_ge X P P' hP hk]
    have := hhi (k - (X.length + P.length))
    rw [show X.length + P.length + (k - (X.length + P.length)) = k by omega] at this
    rw [this]; congr 1; omega

variable (hP : P ≠ []) (hE : SameEffect X P P') (hpl : PlAgree X P P' pl pl')
include hP hE hpl

/-- Exterior slots have the same points in both realizations. -/
theorem pt_ext (u : ExtSlot X P Y) :
    pt pl (X ++ P ++ Y) u.1.1 = pt pl' (X ++ P' ++ Y) (extSlot X P Y P' hP hE u).1 := by
  obtain ⟨⟨⟨k, p⟩, hs⟩, he⟩ := u
  rw [extSlot_val]
  unfold IsExtSlot at he
  simp only at he
  by_cases hp : p = 0
  · subst hp
    rw [if_pos rfl] at he
    rw [extPair_cusp, pt_cusp, pt_cusp, ← letterAt_ext X P Y P' hP he]
    have h1 := hpl k he.extCut
    have h2 := hpl (k + 1) he.extCut_succ
    rw [shiftIdx_succ X P P' hP he] at h2
    unfold Placement.mid Placement.w
    rw [h1, h2]
  · rw [if_neg hp] at he
    rw [extPair_cut, pt_cut pl _ hp, pt_cut pl' _ hp, hpl k he]

end BlockPlacement

/-! ### Exterior pieces: the successor commutes with the correspondence -/

section BlockNext

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
variable (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE

omit hE in
/-- The inverse shift: `shiftIdx X P' P ∘ shiftIdx X P P' = id` on exterior indices (both blocks nonempty). -/
theorem shiftIdx_inv (hP' : P' ≠ []) {k : ℕ} (h : ExtCut X P k) : shiftIdx X P' P (shiftIdx X P P' k) = k := by
  have := P_length_pos P hP
  have := P_length_pos P' hP'
  unfold ExtCut at h
  unfold shiftIdx
  split_ifs <;> omega

omit hE in
theorem extCut_shift {k : ℕ} (h : ExtCut X P k) : ExtCut X P' (shiftIdx X P P' k) := by
  have := P_length_pos P hP
  unfold ExtCut at h ⊢
  unfold shiftIdx
  split_ifs <;> omega

omit hE in
theorem extCol_shift {k : ℕ} (h : ExtCol X P k) : ExtCol X P' (shiftIdx X P P' k) := by
  have := P_length_pos P hP
  unfold ExtCol at h ⊢
  unfold shiftIdx
  split_ifs <;> omega

omit hE in
theorem isExtSlot_extPair {s : ℕ × ℕ} (he : IsExtSlot X P s) : IsExtSlot X P' (extPair X P P' s) := by
  obtain ⟨k, p⟩ := s
  by_cases hp : p = 0
  · subst hp
    simp only [IsExtSlot, extPair, ↓reduceIte] at he ⊢
    exact extCol_shift X P P' hP he
  · simp only [IsExtSlot, extPair, hp, ↓reduceIte] at he ⊢
    exact extCut_shift X P P' hP he

omit hE in
theorem extPair_inv (hP' : P' ≠ []) {s : ℕ × ℕ} (he : IsExtSlot X P s) : extPair X P' P (extPair X P P' s) = s := by
  obtain ⟨k, p⟩ := s
  simp only [extPair, Prod.mk.injEq, and_true]
  by_cases hp : p = 0
  · simp only [IsExtSlot, hp, ↓reduceIte] at he
    exact shiftIdx_inv X P P' hP hP' he.extCut
  · simp only [IsExtSlot, hp, ↓reduceIte] at he
    exact shiftIdx_inv X P P' hP hP' he

omit hP hE in
theorem xsign_val {V : Word} (u : Slot V) :
    xsign u = if u.1.2 = 0 then (match letterAt V u.1.1 with | .l _ _ => true | _ => false) else bit V u.1.1 u.1.2 := rfl

/-- `xsign` is preserved by the correspondence. -/
theorem xsign_ext (u : ExtSlot X P Y) : xsign (extSlot X P Y P' hP hE u) = xsign u.1 := by
  have he := u.2
  rw [xsign_val, xsign_val, extSlot_val]
  obtain ⟨k, p, hkp⟩ : ∃ k p, u.1.1 = (k, p) := ⟨_, _, rfl⟩
  rw [hkp] at he ⊢
  simp only [extPair]
  by_cases hp : p = 0
  · simp only [IsExtSlot, hp, ↓reduceIte] at he ⊢
    rw [← letterAt_ext X P Y P' hP he]
  · simp only [IsExtSlot, hp, ↓reduceIte] at he ⊢
    rw [← bit_ext X P Y P' hP hE he]

/-- A slot with an exterior piece is an exterior slot. -/
theorem isExtSlot_of_extCol (u : Slot (X ++ P ++ Y)) (h : ExtCol X P (colOf u)) : IsExtSlot X P u.1 := by
  obtain ⟨⟨k, p⟩, hs⟩ := u
  unfold IsExtSlot
  simp only
  by_cases hp : p = 0
  · subst hp
    rw [if_pos rfl]
    simpa [colOf] using h
  · rw [if_neg hp]
    unfold colOf at h
    simp only [hp, ↓reduceIte] at h
    unfold ExtCol at h; unfold ExtCut
    split_ifs at h <;> omega

include hW in
/-- The column of the piece is preserved (shifted) by the correspondence. -/
theorem colOf_ext (u : ExtSlot X P Y) (h : ExtCol X P (colOf u.1)) :
    colOf (extSlot X P Y P' hP hE u) = shiftIdx X P P' (colOf u.1) := by
  have he := u.2
  have hs := u.1.2
  unfold colOf
  rw [extSlot_val]
  obtain ⟨k, p, hkp⟩ : ∃ k p, u.1.1 = (k, p) := ⟨_, _, rfl⟩
  unfold colOf at h
  rw [hkp] at he hs h ⊢
  simp only [extPair]
  by_cases hp : p = 0
  · simp [hp]
  · simp only [IsExtSlot, hp, ↓reduceIte] at he h ⊢
    have hbb := bit_ext X P Y P' hP hE he p
    simp only [← hbb]
    split_ifs with hb
    · rfl
    · have hk : 1 ≤ k := (cutSlot_pos hW (by
        rcases hs with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · simp at h0; omega
        · exact h1) (by
        rcases hs with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · simp at h0; omega
        · exact h2)).1
      simp only [hb, ↓reduceIte] at h
      exact (shiftIdx_pred X P P' hP h hk).symm

include hW hW' in
/-- The successor of a slot with an exterior piece: its successor is exterior, and the correspondence
commutes with `next`. -/
theorem next_ext (u : ExtSlot X P Y) (h : ExtCol X P (colOf u.1)) :
    IsExtSlot X P (next hW u.1).1 ∧ (next hW' (extSlot X P Y P' hP hE u)).1 = extPair X P P' (next hW u.1).1 := by
  have he := u.1.2
  simp only [next_val, extSlot_val]
  rcases next_cases hW u.1 with
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, hpq, hk⟩ | ⟨k, p, m, hs, hp, hb, hℓ, hpm, hn, hne, hk⟩ |
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, hpq, hk1, hk⟩ | ⟨k, p, m, d, hs, hp, hb, hℓ, hpm, hn, hb1, hb2, hk1, hk⟩ |
    ⟨k, m, d, hs, hℓ, hn, hb1, hb2, hm, hk⟩ | ⟨k, m, hs, hℓ, hn, hne, hm, hk⟩
  · -- rightward pass
    have hp0 : p ≠ 0 := by omega
    have hcol : colOf u.1 = k := by simp only [colOf, hs, hp0, hb, ↓reduceIte]
    rw [hcol] at h
    rw [next_val, hs] at hn
    rw [hs, hn, extPair_cut, extPair_cut]
    refine ⟨?_, ?_⟩
    · unfold IsExtSlot; simp only [show q ≠ 0 by omega, ↓reduceIte]; exact h.extCut_succ
    · rw [nextPair_right _ hp0 (by rw [← bit_ext X P Y P' hP hE h.extCut]; exact hb)
        (by rw [← letterAt_ext X P Y P' hP h]; exact hpq), shiftIdx_succ X P P' hP h]
  · -- rightward into a right cusp
    have hp0 : p ≠ 0 := by omega
    have hcol : colOf u.1 = k := by simp only [colOf, hs, hp0, hb, ↓reduceIte]
    rw [hcol] at h
    rw [next_val, hs] at hn
    rw [hs, hn, extPair_cut, extPair_cusp]
    refine ⟨?_, ?_⟩
    · unfold IsExtSlot; simp only [↓reduceIte]; exact h
    · have hpq : (letterAt (X ++ P' ++ Y) (shiftIdx X P P' k)).posR p = none := by
        rw [← letterAt_ext X P Y P' hP h, hℓ]
        rcases hpm with rfl | rfl
        · exact posR_r_idx _
        · exact posR_r_idx_succ _
      rw [nextPair_right_none _ hp0 (by rw [← bit_ext X P Y P' hP hE h.extCut]; exact hb) hpq]
  · -- leftward pass
    have hp0 : p ≠ 0 := by omega
    have hcol : colOf u.1 = k - 1 := by simp only [colOf, hs, hp0, hb, ↓reduceIte, Bool.false_eq_true]
    rw [hcol] at h
    have hk' : ExtCut X P k := by unfold ExtCol at h; unfold ExtCut; omega
    rw [next_val, hs] at hn
    rw [hs, hn, extPair_cut, extPair_cut]
    refine ⟨?_, ?_⟩
    · unfold IsExtSlot; simp only [show q ≠ 0 by omega, ↓reduceIte]; exact h.extCut
    · rw [nextPair_left _ hp0 (by rw [← bit_ext X P Y P' hP hE hk']; exact hb)
        (by rw [← shiftIdx_pred X P P' hP h hk1, ← letterAt_ext X P Y P' hP h]; exact hpq),
        shiftIdx_pred X P P' hP h hk1]
  · -- leftward into a left cusp
    have hp0 : p ≠ 0 := by omega
    have hcol : colOf u.1 = k - 1 := by simp only [colOf, hs, hp0, hb, ↓reduceIte, Bool.false_eq_true]
    rw [hcol] at h
    have hk' : ExtCut X P k := by unfold ExtCol at h; unfold ExtCut; omega
    rw [next_val, hs] at hn
    rw [hs, hn, extPair_cut, extPair_cusp]
    refine ⟨?_, ?_⟩
    · unfold IsExtSlot; simp only [↓reduceIte]; exact h
    · have hpq : (letterAt (X ++ P' ++ Y) (shiftIdx X P P' k - 1)).posL p = none := by
        rw [← shiftIdx_pred X P P' hP h hk1, ← letterAt_ext X P Y P' hP h, hℓ]
        rcases hpm with rfl | rfl
        · exact posL_l_idx _ _
        · exact posL_l_idx_succ _ _
      rw [nextPair_left_none _ hp0 (by rw [← bit_ext X P Y P' hP hE hk']; exact hb) hpq,
        shiftIdx_pred X P P' hP h hk1]
  · -- out of a left cusp
    have hcol : colOf u.1 = k := by simp only [colOf, hs, ↓reduceIte]
    rw [hcol] at h
    rw [next_val, hs] at hn
    rw [hs, hn, extPair_cusp, extPair_cut]
    refine ⟨?_, ?_⟩
    · unfold IsExtSlot; simp only [show (if d then m else m + 1) ≠ 0 by cases d <;> simp <;> omega, ↓reduceIte]
      exact h.extCut_succ
    · rw [nextPair_cusp_l _ (by rw [← letterAt_ext X P Y P' hP h]; exact hℓ), shiftIdx_succ X P P' hP h]
  · -- out of a right cusp
    have hcol : colOf u.1 = k := by simp only [colOf, hs, ↓reduceIte]
    rw [hcol] at h
    rw [next_val, hs] at hn
    rw [hs, hn, extPair_cusp, extPair_cut]
    refine ⟨?_, ?_⟩
    · unfold IsExtSlot; simp only [show (if bit (X ++ P ++ Y) k m then m + 1 else m) ≠ 0 by split_ifs <;> omega,
        ↓reduceIte]
      exact h.extCut
    · rw [nextPair_cusp_r _ (by rw [← letterAt_ext X P Y P' hP h]; exact hℓ),
        ← bit_ext X P Y P' hP hE h.extCut]

end BlockNext

/-! ## 6. The outside match of two realizations agreeing outside a block -/

section OutMatch

variable (X P Y P' : Word) (hP : P ≠ []) (hP' : P' ≠ []) (hE : SameEffect X P P')
variable (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
variable (pl pl' : Placement) (hpl : PlAgree X P P' pl pl')

include hP in
theorem ne_nil_of_block : X ++ P ++ Y ≠ [] := by
  intro h
  obtain ⟨h1, -⟩ := List.append_eq_nil_iff.1 h
  obtain ⟨-, h2⟩ := List.append_eq_nil_iff.1 h1
  exact hP h2

include hP hP' hpl in
theorem plAgree_symm : PlAgree X P' P pl' pl := by
  intro k' hk'
  have hk : ExtCut X P (shiftIdx X P' P k') := extCut_shift X P' P hP' hk'
  have h1 := hpl _ hk
  rw [shiftIdx_inv X P' P hP' hP hk'] at h1
  exact h1.symm

/-- The common half-height of the two realizations. -/
def blockH : ℝ := max (hgt (X ++ P ++ Y)) (hgt (X ++ P' ++ Y))

theorem hgt_le_blockH : hgt (X ++ P ++ Y) ≤ blockH X P Y P' := le_max_left _ _
theorem hgt_le_blockH' : hgt (X ++ P' ++ Y) ≤ blockH X P Y P' := le_max_right _ _

/-- The block rectangle of `W` (in `pl`). -/
def blockU : Set Plane := blockRect pl X.length (X.length + P.length) (blockH X P Y P')

include hP hpl in
/-- The same rectangle, read in `W'` and `pl'`. -/
theorem blockU_eq : blockU X P Y P' pl = blockRect pl' X.length (X.length + P'.length) (blockH X P Y P') := by
  unfold blockU blockRect
  have h1 := hpl X.length (Or.inl le_rfl)
  have h2 := hpl (X.length + P.length) (Or.inr le_rfl)
  rw [shiftIdx_of_le X P P' le_rfl] at h1
  rw [shiftIdx_of_ge X P P' hP le_rfl, Nat.sub_self, zero_add] at h2
  rw [h1, h2]

/-! ### Outside traversal points -/

variable {V : Word} (hV : V.Closed) (hneV : V ≠ []) (plV : Placement)
include hV

/-- The evaluation of a traversal point as a point on the segment from its slot to the successor. -/
theorem eval_eq_lin (p : (realizeAt plV hV hneV).Γ.Pt) :
    (realizeAt plV hV hneV).Γ.eval p =
      pt plV V (slotOf plV hV hneV (strandPt plV hV hneV p)).1 +
        p.2.2.val • (pt plV V (next hV (slotOf plV hV hneV (strandPt plV hV hneV p))).1 -
          pt plV V (slotOf plV hV hneV (strandPt plV hV hneV p)).1) := by
  obtain ⟨i, j, t⟩ := p
  show edgePoint ((shadowOf plV hV hneV).comp i).P j t.val =
    pt plV V (slotOf plV hV hneV ⟨i, j⟩).1 +
      t.val • (pt plV V (next hV (slotOf plV hV hneV ⟨i, j⟩)).1 - pt plV V (slotOf plV hV hneV ⟨i, j⟩).1)
  have e : edgePoint ((shadowOf plV hV hneV).comp i).P j t.val =
      (shadowOf plV hV hneV).tail ⟨i, j⟩ + t.val • ((shadowOf plV hV hneV).head ⟨i, j⟩ - (shadowOf plV hV hneV).tail ⟨i, j⟩) := rfl
  rw [e, tail_eq, head_eq]

end OutMatch

section OutMatch2

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
variable (hW : (X ++ P ++ Y).Closed) (pl : Placement)

/-- A point of the piece of `u` at parameter `t ∈ [0, 1)` (as a traversal point) is outside the open
block iff the piece is exterior or the point is the tail of a boundary cut slot. -/
def OutPt (u : Slot (X ++ P ++ Y)) (t : ℝ) : Prop := ExtCol X P (colOf u) ∨ (t = 0 ∧ IsExtSlot X P u.1)

include hW

include hP in
/-- The point of an exterior slot is not in the open block. -/
theorem pt_notMem_interior_of_ext (u : Slot (X ++ P ++ Y)) (he : IsExtSlot X P u.1) {H : ℝ} :
    pt pl (X ++ P ++ Y) u.1 ∉ interior (blockRect pl X.length (X.length + P.length) H) := by
  rw [blockRect, mem_interior_rect_iff]
  rintro ⟨⟨h1, h2⟩, -⟩
  obtain ⟨⟨k, p⟩, hs⟩ := u
  unfold IsExtSlot at he
  simp only at he
  by_cases hp : p = 0
  · subst hp
    rw [if_pos rfl] at he
    rw [pt_cusp] at h1 h2
    simp only at h1 h2
    rcases he with he | he
    · have := pl.mid_lt_x_succ k
      have := pl.x_le_x_iff.2 he
      linarith
    · have := pl.x_lt_mid k
      have := pl.x_le_x_iff.2 he
      linarith
  · rw [if_neg hp] at he
    rw [pt_cut pl _ hp] at h1 h2
    simp only at h1 h2
    rcases he with he | he
    · have := pl.x_le_x_iff.2 he; linarith
    · have := pl.x_le_x_iff.2 he; linarith

include hP in
/-- The characterization of the traversal points outside the open block. -/
theorem notMem_interior_iff_outPt (hne : X ++ P ++ Y ≠ []) (p : (realizeAt pl hW hne).Γ.Pt) {H : ℝ}
    (hH : hgt (X ++ P ++ Y) ≤ H) :
    (realizeAt pl hW hne).Γ.eval p ∉ interior (blockRect pl X.length (X.length + P.length) H) ↔
      OutPt X P Y (slotOf pl hW hne (strandPt pl hW hne p)) p.2.2.val := by
  set u := slotOf pl hW hne (strandPt pl hW hne p) with hu
  have ht := p.2.2.2
  constructor
  · intro h
    by_cases hc : ExtCol X P (colOf u)
    · exact Or.inl hc
    · right
      have hka : X.length ≤ colOf u := by unfold ExtCol at hc; omega
      have hkb : colOf u + 1 ≤ X.length + P.length := by unfold ExtCol at hc; omega
      rw [eval_eq_piecePt_parOf] at h
      obtain ⟨h0, h1⟩ := parOf_mem pl hW hne p
      have hτ : parOf pl hW hne p = 0 ∨ parOf pl hW hne p = 1 := by
        by_contra hcon
        rw [not_or] at hcon
        exact h (piecePt_mem_interior_blockRect_of_int pl hW _ hka hkb (lt_of_le_of_ne h0 (Ne.symm hcon.1))
          (lt_of_le_of_ne h1 hcon.2) hH)
      obtain ⟨ht0, he⟩ := parOf_eq_end pl hW hne p hτ
      refine ⟨ht0, ?_⟩
      -- the point is `pt u`, not in the open block: `u` is a boundary cut slot
      rw [eval_eq_piecePt_parOf, ← hu] at he
      rw [he] at h
      rw [blockRect, mem_interior_rect_iff] at h
      obtain ⟨k, q, hkq⟩ : ∃ k q, u.1 = (k, q) := ⟨_, _, rfl⟩
      unfold IsExtSlot
      rw [hkq]
      simp only
      by_cases hq : q = 0
      · exfalso
        subst hq
        have hcol : colOf u = k := by simp [colOf, hkq]
        rw [hkq, pt_cusp] at h
        apply h
        have hz := abs_piecePt_snd_lt' pl hW u h0 h1 hH
        rw [he, hkq, pt_cusp] at hz
        simp only at hz
        rw [abs_lt] at hz
        refine ⟨⟨?_, ?_⟩, hz.1, hz.2⟩
        · exact lt_of_le_of_lt (pl.x_le_x_iff.2 (hcol ▸ hka)) (pl.x_lt_mid k)
        · exact lt_of_lt_of_le (pl.mid_lt_x_succ k) (pl.x_le_x_iff.2 (hcol ▸ hkb))
      · rw [if_neg hq]
        rw [hkq, pt_cut pl _ hq] at h
        have hz := abs_piecePt_snd_lt' pl hW u h0 h1 hH
        rw [he, hkq, pt_cut pl _ hq] at hz
        simp only at hz h
        rw [abs_lt] at hz
        unfold ExtCut
        by_contra hcon
        rw [not_or, not_le, not_le] at hcon
        apply h
        refine ⟨⟨?_, ?_⟩, hz.1, hz.2⟩
        · exact pl.x_lt_x_iff.2 hcon.1
        · exact pl.x_lt_x_iff.2 hcon.2
  · rintro (hc | ⟨ht0, he⟩)
    · rw [eval_eq_piecePt_parOf]
      obtain ⟨h0, h1⟩ := parOf_mem pl hW hne p
      exact piecePt_notMem_interior_of_ext pl hW _ hc h0 h1
    · rw [eval_eq_lin hW hne pl p, ht0, zero_smul, add_zero]
      exact pt_notMem_interior_of_ext X P Y hP hW pl u he

end OutMatch2

/-! ### The bundled setting and the point correspondence -/

/-- Two closed words `X ++ P ++ Y`, `X ++ P' ++ Y` with nonempty factors of the same typing effect, realized
with placements agreeing outside the block. -/
structure BlockSetup where
  X : Word
  P : Word
  Y : Word
  P' : Word
  hP : P ≠ []
  hP' : P' ≠ []
  hE : SameEffect X P P'
  hW : (X ++ P ++ Y).Closed
  hW' : (X ++ P' ++ Y).Closed
  pl : Placement
  pl' : Placement
  hpl : PlAgree X P P' pl pl'

namespace BlockSetup

variable (B : BlockSetup)

/-- The symmetric setting (the roles of the two words exchanged). -/
def symm : BlockSetup :=
  ⟨B.X, B.P', B.Y, B.P, B.hP', B.hP, B.hE.symm, B.hW', B.hW, B.pl', B.pl, plAgree_symm B.X B.P B.P' B.hP B.hP' B.pl B.pl' B.hpl⟩

theorem symm_symm : B.symm.symm = B := rfl

theorem hne : B.X ++ B.P ++ B.Y ≠ [] := ne_nil_of_block B.X B.P B.Y B.hP
theorem hne' : B.X ++ B.P' ++ B.Y ≠ [] := ne_nil_of_block B.X B.P' B.Y B.hP'

/-- the first realization -/
abbrev F : PLFront := realizeAt B.pl B.hW B.hne
/-- the second realization -/
abbrev F' : PLFront := realizeAt B.pl' B.hW' B.hne'

/-- the block rectangle (in `pl`) -/
def U : Set Plane := blockU B.X B.P B.Y B.P' B.pl

theorem U_eq : B.U = blockRect B.pl B.X.length (B.X.length + B.P.length) (blockH B.X B.P B.Y B.P') := rfl

theorem U_eq' : B.U = blockRect B.pl' B.X.length (B.X.length + B.P'.length) (blockH B.X B.P B.Y B.P') :=
  blockU_eq B.X B.P B.Y B.P' B.hP B.pl B.pl' B.hpl

theorem symm_U : B.symm.U = B.U := by
  rw [U_eq', symm, U_eq]
  unfold blockH
  simp only [max_comm]

theorem hgt_le : hgt (B.X ++ B.P ++ B.Y) ≤ blockH B.X B.P B.Y B.P' := le_max_left _ _
theorem hgt_le' : hgt (B.X ++ B.P' ++ B.Y) ≤ blockH B.X B.P B.Y B.P' := le_max_right _ _

/-- the slot at the tail of the strand of a traversal point -/
abbrev slotPt (p : B.F.Γ.Pt) : Slot (B.X ++ B.P ++ B.Y) := slotOf B.pl B.hW B.hne (strandPt B.pl B.hW B.hne p)

/-- a fixed point of the second realization (used only off the exterior) -/
def junk' : B.F'.Γ.Pt :=
  travPt B.pl' B.hW' B.hne' (strandOfSlot B.pl' B.hW' B.hne' ⟨(0, 0), isSlot_zero B.hW' B.hne'⟩) ⟨0, le_rfl, zero_lt_one⟩

open Classical in
/-- The point correspondence: a traversal point on an exterior slot goes to the traversal point with the
same parameter on the corresponding strand of the other realization. -/
def φfun (p : B.F.Γ.Pt) : B.F'.Γ.Pt :=
  if h : IsExtSlot B.X B.P (B.slotPt p).1 then
    travPt B.pl' B.hW' B.hne'
      (strandOfSlot B.pl' B.hW' B.hne' (extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨B.slotPt p, h⟩)) p.2.2
  else B.junk'

theorem φfun_of {p : B.F.Γ.Pt} (h : IsExtSlot B.X B.P (B.slotPt p).1) :
    B.φfun p = travPt B.pl' B.hW' B.hne'
      (strandOfSlot B.pl' B.hW' B.hne' (extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨B.slotPt p, h⟩)) p.2.2 := by
  unfold φfun; rw [dif_pos h]

theorem slotPt_φfun {p : B.F.Γ.Pt} (h : IsExtSlot B.X B.P (B.slotPt p).1) :
    B.symm.slotPt (B.φfun p) = extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨B.slotPt p, h⟩ := by
  rw [φfun_of B h]
  exact slotOf_strandOfSlot _ _ _ _

theorem param_φfun {p : B.F.Γ.Pt} (h : IsExtSlot B.X B.P (B.slotPt p).1) : (B.φfun p).2.2 = p.2.2 := by
  rw [φfun_of B h]; rfl

/-- An exterior slot's successor is exterior when its piece is; packaged as the slot equation. -/
theorem next_extSlot (u : Slot (B.X ++ B.P ++ B.Y)) (he : IsExtSlot B.X B.P u.1) (h : ExtCol B.X B.P (colOf u)) :
    next B.hW' (extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨u, he⟩) =
      extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨next B.hW u, (next_ext B.X B.P B.Y B.P' B.hP B.hE B.hW B.hW' ⟨u, he⟩ h).1⟩ :=
  Subtype.ext (next_ext B.X B.P B.Y B.P' B.hP B.hE B.hW B.hW' ⟨u, he⟩ h).2

theorem pt_extSlot (u : Slot (B.X ++ B.P ++ B.Y)) (he : IsExtSlot B.X B.P u.1) :
    pt B.pl' (B.X ++ B.P' ++ B.Y) (extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨u, he⟩).1 = pt B.pl (B.X ++ B.P ++ B.Y) u.1 :=
  (pt_ext B.X B.P B.Y B.P' B.pl B.pl' B.hP B.hE B.hpl ⟨u, he⟩).symm

/-- `φfun` preserves the evaluation on outside points. -/
theorem eval_φfun {p : B.F.Γ.Pt} (hout : OutPt B.X B.P B.Y (B.slotPt p) p.2.2.val) :
    B.F'.Γ.eval (B.φfun p) = B.F.Γ.eval p := by
  have he : IsExtSlot B.X B.P (B.slotPt p).1 := by
    rcases hout with h | ⟨-, h⟩
    · exact isExtSlot_of_extCol B.X B.P B.Y B.P' B.hP B.hE _ h
    · exact h
  rw [eval_eq_lin B.hW' B.hne' B.pl' (B.φfun p), eval_eq_lin B.hW B.hne B.pl p]
  have hs : slotOf B.pl' B.hW' B.hne' (strandPt B.pl' B.hW' B.hne' (B.φfun p)) =
      extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨B.slotPt p, he⟩ := slotPt_φfun B he
  rw [hs, param_φfun B he, pt_extSlot]
  rcases hout with h | ⟨ht0, -⟩
  · rw [next_extSlot B _ he h, pt_extSlot]
  · rw [ht0]; simp

/-- The correspondence is inverted by the symmetric one. -/
theorem φfun_symm {p : B.F.Γ.Pt} (h : IsExtSlot B.X B.P (B.slotPt p).1) : B.symm.φfun (B.φfun p) = p := by
  have h' : IsExtSlot B.symm.X B.symm.P (B.symm.slotPt (B.φfun p)).1 := by
    rw [slotPt_φfun B h]
    exact isExtSlot_extPair B.X B.P B.P' B.hP h
  rw [B.symm.φfun_of h']
  have hslot : extSlot B.symm.X B.symm.P B.symm.Y B.symm.P' B.symm.hP B.symm.hE ⟨B.symm.slotPt (B.φfun p), h'⟩ =
      B.slotPt p := by
    apply Subtype.ext
    rw [extSlot_val]
    show extPair B.X B.P' B.P (B.symm.slotPt (B.φfun p)).1 = _
    rw [slotPt_φfun B h, extSlot_val]
    exact extPair_inv B.X B.P B.P' B.hP B.hP' h
  rw [param_φfun B h]
  have : ∀ (v : Slot (B.X ++ B.P ++ B.Y)) (hv : v = B.slotPt p),
      travPt B.pl B.hW B.hne (strandOfSlot B.pl B.hW B.hne v) p.2.2 = p := by
    intro v hv
    subst hv
    show travPt B.pl B.hW B.hne (strandOfSlot B.pl B.hW B.hne (slotOf B.pl B.hW B.hne (strandPt B.pl B.hW B.hne p))) p.2.2 = p
    rw [strandOfSlot_slotOf]
    exact travPt_strandPt B.pl B.hW B.hne p
  exact this _ hslot

/-- Outside traversal points have exterior slots. -/
theorem isExtSlot_of_outside {p : B.F.Γ.Pt} (hout : B.F.Γ.eval p ∉ interior B.U) :
    IsExtSlot B.X B.P (B.slotPt p).1 := by
  rw [U_eq, notMem_interior_iff_outPt B.X B.P B.Y B.hP B.hW B.pl B.hne p B.hgt_le] at hout
  rcases hout with h | ⟨-, h⟩
  · exact isExtSlot_of_extCol B.X B.P B.Y B.P' B.hP B.hE _ h
  · exact h

theorem outPt_of_outside {p : B.F.Γ.Pt} (hout : B.F.Γ.eval p ∉ interior B.U) :
    OutPt B.X B.P B.Y (B.slotPt p) p.2.2.val := by
  rw [U_eq, notMem_interior_iff_outPt B.X B.P B.Y B.hP B.hW B.pl B.hne p B.hgt_le] at hout
  exact hout

/-- `φfun` maps outside points to outside points. -/
theorem φfun_outside {p : B.F.Γ.Pt} (hout : B.F.Γ.eval p ∉ interior B.U) : B.F'.Γ.eval (B.φfun p) ∉ interior B.U := by
  rw [eval_φfun B (outPt_of_outside B hout)]; exact hout

/-- The outside traversal points of the two realizations correspond. -/
def outEquiv : B.F.Γ.Outside B.U ≃ B.F'.Γ.Outside B.U where
  toFun p := ⟨B.φfun p.1, φfun_outside B p.2⟩
  invFun q := ⟨B.symm.φfun q.1, by
    have := B.symm.φfun_outside (p := q.1) (by rw [symm_U]; exact q.2)
    rw [symm_U] at this; exact this⟩
  left_inv p := Subtype.ext (φfun_symm B (isExtSlot_of_outside B p.2))
  right_inv q := Subtype.ext (B.symm.φfun_symm (B.symm.isExtSlot_of_outside (p := q.1) (by rw [symm_U]; exact q.2)))

theorem outEquiv_apply (p : B.F.Γ.Outside B.U) : (B.outEquiv p).1 = B.φfun p.1 := rfl

/-! ### Strictly exterior points: the directions -/

/-- A slot strictly outside the block: a cut slot at a cut strictly before `|X|` or strictly after
`|X| + |P|`, or a cusp vertex of an exterior column. -/
def StrictOut (u : Slot (B.X ++ B.P ++ B.Y)) : Prop :=
  (u.1.2 ≠ 0 ∧ (u.1.1 < B.X.length ∨ B.X.length + B.P.length < u.1.1)) ∨ (u.1.2 = 0 ∧ ExtCol B.X B.P u.1.1)

theorem strictOut_of_pt_notMem (u : Slot (B.X ++ B.P ++ B.Y)) (h : pt B.pl (B.X ++ B.P ++ B.Y) u.1 ∉ B.U) :
    B.StrictOut u := by
  rw [U_eq, blockRect, mem_rect_iff] at h
  obtain ⟨hz1, hz2⟩ := pt_snd_bounds B.pl B.hW u
  have hH := B.hgt_le
  unfold hgt at hH
  have hz : -(blockH B.X B.P B.Y B.P') ≤ (pt B.pl (B.X ++ B.P ++ B.Y) u.1).2 ∧
      (pt B.pl (B.X ++ B.P ++ B.Y) u.1).2 ≤ blockH B.X B.P B.Y B.P' := ⟨by linarith, by linarith⟩
  have hx : ¬ (B.pl.x B.X.length ≤ (pt B.pl (B.X ++ B.P ++ B.Y) u.1).1 ∧
      (pt B.pl (B.X ++ B.P ++ B.Y) u.1).1 ≤ B.pl.x (B.X.length + B.P.length)) := fun hx => h ⟨hx, hz⟩
  rw [not_and_or, not_le, not_le] at hx
  obtain ⟨⟨k, q⟩, hs⟩ := u
  unfold StrictOut
  simp only
  by_cases hq : q = 0
  · subst hq
    right
    refine ⟨rfl, ?_⟩
    rw [pt_cusp] at hx
    simp only at hx
    unfold ExtCol
    rcases hx with hx | hx
    · left
      have := B.pl.x_lt_mid k
      have : B.pl.x k < B.pl.x B.X.length := by linarith
      have := B.pl.x_lt_x_iff.1 this
      omega
    · right
      have := B.pl.mid_lt_x_succ k
      have : B.pl.x (B.X.length + B.P.length) < B.pl.x (k + 1) := by linarith
      have := B.pl.x_lt_x_iff.1 this
      omega
  · left
    refine ⟨hq, ?_⟩
    rw [pt_cut B.pl _ hq] at hx
    simp only at hx
    rcases hx with hx | hx
    · exact Or.inl (B.pl.x_lt_x_iff.1 hx)
    · exact Or.inr (B.pl.x_lt_x_iff.1 hx)

theorem StrictOut.extCol {u : Slot (B.X ++ B.P ++ B.Y)} (h : B.StrictOut u) : ExtCol B.X B.P (colOf u) := by
  obtain ⟨⟨k, q⟩, hs⟩ := u
  unfold StrictOut at h
  simp only at h
  unfold colOf ExtCol
  simp only
  rcases h with ⟨hq, hk⟩ | ⟨hq, hk⟩
  · rw [if_neg hq]
    split_ifs <;> omega
  · rw [if_pos hq]; exact hk

theorem StrictOut.extCol_prev {u : Slot (B.X ++ B.P ++ B.Y)} (h : B.StrictOut u) :
    ExtCol B.X B.P (colOf (prev B.hW u)) := by
  have hnp : next B.hW (prev B.hW u) = u := next_prev B.hW u
  rcases next_cases B.hW (prev B.hW u) with
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, -, -⟩ | ⟨k, p, m, hs, hp, hb, hℓ, -, hn, -, -⟩ |
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, -, hk1, -⟩ | ⟨k, p, m, d, hs, hp, hb, hℓ, -, hn, -, -, hk1, -⟩ |
    ⟨k, m, d, hs, hℓ, hn, -, -, hm, -⟩ | ⟨k, m, hs, hℓ, hn, -, hm, -⟩
  all_goals rw [hnp] at hn
  all_goals unfold StrictOut at h; rw [hn] at h; simp only at h
  · have hcol : colOf (prev B.hW u) = k := by simp only [colOf, hs, show p ≠ 0 by omega, hb, ↓reduceIte]
    rw [hcol]; unfold ExtCol
    rcases h with ⟨-, hk⟩ | ⟨h0, -⟩
    · omega
    · omega
  · have hcol : colOf (prev B.hW u) = k := by simp only [colOf, hs, show p ≠ 0 by omega, hb, ↓reduceIte]
    rw [hcol]
    rcases h with ⟨h0, -⟩ | ⟨-, hk⟩
    · exact absurd rfl h0
    · exact hk
  · have hcol : colOf (prev B.hW u) = k - 1 := by
      simp only [colOf, hs, show p ≠ 0 by omega, hb, ↓reduceIte, Bool.false_eq_true]
    rw [hcol]; unfold ExtCol
    rcases h with ⟨-, hk⟩ | ⟨h0, -⟩
    · omega
    · omega
  · have hcol : colOf (prev B.hW u) = k - 1 := by
      simp only [colOf, hs, show p ≠ 0 by omega, hb, ↓reduceIte, Bool.false_eq_true]
    rw [hcol]
    rcases h with ⟨h0, -⟩ | ⟨-, hk⟩
    · exact absurd rfl h0
    · exact hk
  · have hcol : colOf (prev B.hW u) = k := by simp only [colOf, hs, ↓reduceIte]
    rw [hcol]; unfold ExtCol
    rcases h with ⟨-, hk⟩ | ⟨h0, -⟩
    · omega
    · exfalso; split_ifs at h0 <;> omega
  · have hcol : colOf (prev B.hW u) = k := by simp only [colOf, hs, ↓reduceIte]
    rw [hcol]; unfold ExtCol
    rcases h with ⟨-, hk⟩ | ⟨h0, -⟩
    · omega
    · exfalso; split_ifs at h0 <;> omega

/-- A point strictly outside the block lies on an exterior piece. -/
theorem extCol_of_notMem {p : B.F.Γ.Pt} (h : B.F.Γ.eval p ∉ B.U) : ExtCol B.X B.P (colOf (B.slotPt p)) := by
  have hout : B.F.Γ.eval p ∉ interior B.U := fun h' => h (interior_subset h')
  rcases outPt_of_outside B hout with hc | ⟨ht0, -⟩
  · exact hc
  · rw [eval_eq_lin B.hW B.hne B.pl p, ht0, zero_smul, add_zero] at h
    exact (strictOut_of_pt_notMem B _ h).extCol

/-- the arriving direction at the tail of `⟨i, j⟩`, on the realization -/
theorem dir_pred_eq' {V : Word} (plV : Placement) (hV : V.Closed) (hneV : V ≠ [])
    (i : Fin (realizeAt plV hV hneV).Γ.c) (j : ZMod ((realizeAt plV hV hneV).Γ.comp i).k) :
    (realizeAt plV hV hneV).Γ.dir ⟨i, j - 1⟩ =
      pt plV V (slotOf plV hV hneV ⟨i, j⟩).1 - pt plV V (prev hV (slotOf plV hV hneV ⟨i, j⟩)).1 :=
  dir_pred_eq plV hV hneV i j

/-- The direction of the strand carrying an outside point (at a point strictly outside) is preserved. -/
theorem dir_φfun {p : B.F.Γ.Pt} (h : B.F.Γ.eval p ∉ B.U) :
    B.F'.Γ.dir (strandPt B.pl' B.hW' B.hne' (B.φfun p)) = B.F.Γ.dir (strandPt B.pl B.hW B.hne p) := by
  have hout : B.F.Γ.eval p ∉ interior B.U := fun h' => h (interior_subset h')
  have he := isExtSlot_of_outside B hout
  have hc := extCol_of_notMem B h
  rw [dir_eq', dir_eq']
  have hs : slotOf B.pl' B.hW' B.hne' (strandPt B.pl' B.hW' B.hne' (B.φfun p)) =
      extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨B.slotPt p, he⟩ := slotPt_φfun B he
  rw [hs, next_extSlot B _ he hc, pt_extSlot, pt_extSlot]

/-- The predecessor of a strictly exterior slot corresponds. -/
theorem prev_extSlot (u : Slot (B.X ++ B.P ++ B.Y)) (he : IsExtSlot B.X B.P u.1) (hst : B.StrictOut u) :
    prev B.hW' (extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨u, he⟩) =
      extSlot B.X B.P B.Y B.P' B.hP B.hE
        ⟨prev B.hW u, isExtSlot_of_extCol B.X B.P B.Y B.P' B.hP B.hE _ hst.extCol_prev⟩ := by
  have hep := isExtSlot_of_extCol B.X B.P B.Y B.P' B.hP B.hE _ hst.extCol_prev
  have h1 := next_extSlot B (prev B.hW u) hep hst.extCol_prev
  have h2 : extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨u, he⟩ =
      extSlot B.X B.P B.Y B.P' B.hP B.hE
        ⟨next B.hW (prev B.hW u), (next_ext B.X B.P B.Y B.P' B.hP B.hE B.hW B.hW' ⟨prev B.hW u, hep⟩ hst.extCol_prev).1⟩ := by
    apply Subtype.ext
    rw [extSlot_val, extSlot_val]
    simp only [next_prev]
  rw [h2, ← h1, prev_next]

/-- The arriving direction at a point strictly outside is preserved. -/
theorem dir_before_φfun {p : B.F.Γ.Pt} (h : B.F.Γ.eval p ∉ B.U) :
    B.F'.Γ.dir (B.F'.Γ.strandBefore (B.φfun p)) = B.F.Γ.dir (B.F.Γ.strandBefore p) := by
  have hout : B.F.Γ.eval p ∉ interior B.U := fun h' => h (interior_subset h')
  have he := isExtSlot_of_outside B hout
  by_cases ht : p.2.2.val = 0
  · have ht' : (B.φfun p).2.2.val = 0 := by rw [param_φfun B he]; exact ht
    rw [Shadow.strandBefore_of_zero _ p ht, Shadow.strandBefore_of_zero _ (B.φfun p) ht']
    have hstrict : B.StrictOut (B.slotPt p) := by
      rw [eval_eq_lin B.hW B.hne B.pl p, ht, zero_smul, add_zero] at h
      exact strictOut_of_pt_notMem B _ h
    have hprev := prev_extSlot B (B.slotPt p) he hstrict
    have hφ := φfun_of B he
    set s' := strandOfSlot B.pl' B.hW' B.hne' (extSlot B.X B.P B.Y B.P' B.hP B.hE ⟨B.slotPt p, he⟩) with hs'
    obtain ⟨i, j, t⟩ := p
    rw [hφ]
    show (realizeAt B.pl' B.hW' B.hne').Γ.dir ⟨s'.1, s'.2 - 1⟩ = (realizeAt B.pl B.hW B.hne).Γ.dir ⟨i, j - 1⟩
    rw [dir_pred_eq', dir_pred_eq']
    show pt B.pl' _ (slotOf B.pl' B.hW' B.hne' s').1 - pt B.pl' _ (prev B.hW' (slotOf B.pl' B.hW' B.hne' s')).1 = _
    rw [hs', slotOf_strandOfSlot, hprev, pt_extSlot, pt_extSlot]
    rfl
  · have ht' : (B.φfun p).2.2.val ≠ 0 := by rw [param_φfun B he]; exact ht
    rw [Shadow.strandBefore_of_ne_zero _ p ht, Shadow.strandBefore_of_ne_zero _ (B.φfun p) ht']
    exact dir_φfun B h

end BlockSetup

/-! ### Crossings of `σ` letters: congruence, the crossing parameter, the under strand -/

section CrossingFacts

variable {V : Word} (plV : Placement) (hV : V.Closed) (hneV : V ≠ [])
include hV

theorem crossingOf_congr {k m m' : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m) (hℓ' : letterAt V k = .σ m') :
    crossingOf plV hV hneV hk hℓ = crossingOf plV hV hneV hk hℓ' := by
  have : m = m' := Letter.σ.inj (hℓ.symm.trans hℓ')
  subst this
  rfl

theorem crossingOf_congr_idx {k k' m m' : ℕ} (hkk : k = k') (hk : k < V.length) (hk' : k' < V.length)
    (hℓ : letterAt V k = .σ m) (hℓ' : letterAt V k' = .σ m') :
    crossingOf plV hV hneV hk hℓ = crossingOf plV hV hneV hk' hℓ' := by
  subst hkk
  exact crossingOf_congr plV hV hneV hk hℓ hℓ'

theorem crossingOf_eq_crossingOfIdx {k m : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m) :
    crossingOf plV hV hneV hk hℓ = crossingOfIdx plV hV hneV ⟨⟨k, hk⟩, by rw [hℓ]; rfl⟩ :=
  crossingOf_congr plV hV hneV hk hℓ _

theorem colOfCrossing_crossingOf {k m : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m) :
    ((colOfCrossing plV hV hneV (crossingOf plV hV hneV hk hℓ)).1 : ℕ) = k := by
  rw [crossingOf_eq_crossingOfIdx, colOfCrossing_crossingOfIdx]

/-- Every crossing is the crossing of its column's letter. -/
theorem eq_crossingOf (x : (realizeAt plV hV hneV).Γ.Crossing) :
    x = crossingOf plV hV hneV (colOfCrossing plV hV hneV x).1.2
      (Classical.choose_spec (σIdx_letter (colOfCrossing plV hV hneV x))) :=
  (crossingOfIdx_colOfCrossing plV hV hneV x).symm

theorem piecePt_σSlotA_half {k m : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m) :
    piecePt plV (σSlotA hV hk hℓ) (1 / 2) = (plV.mid k, -(m : ℝ) - 1 / 2) := by
  obtain ⟨hc, hs, -⟩ := σSlotA_spec hV hk hℓ
  unfold piecePt
  rw [hc, hs, Shape.par_pass]
  simp [Placement.A, Placement.mid]; constructor <;> push_cast <;> ring

theorem piecePt_σSlotB_half {k m : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m) :
    piecePt plV (σSlotB hV hk hℓ) (1 / 2) = (plV.mid k, -(m : ℝ) - 1 / 2) := by
  obtain ⟨hc, hs, -⟩ := σSlotB_spec hV hk hℓ
  unfold piecePt
  rw [hc, hs, Shape.par_pass]
  simp [Placement.A, Placement.mid]; constructor <;> push_cast <;> ring

/-- Both strands of a `σ` crossing pass the double point at parameter `1/2`. -/
theorem crossingParam_eq_half {k m : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m)
    {s : (realizeAt plV hV hneV).Γ.Strand} (hs : s ∈ (crossingOf plV hV hneV hk hℓ).val) :
    (realizeAt plV hV hneV).diagram.crossingParam (crossingOf plV hV hneV hk hℓ) hs = 1 / 2 := by
  obtain ⟨-, -, hspec⟩ := (realizeAt plV hV hneV).diagram.crossingParam_spec (crossingOf plV hV hneV hk hℓ) hs
  have hhalf : edgePoint ((realizeAt plV hV hneV).Γ.comp s.1).P s.2 (1 / 2) =
      (realizeAt plV hV hneV).Γ.crossingPoint (crossingOf plV hV hneV hk hℓ) := by
    have e := edgePoint_eq plV hV hneV s (1 / 2)
    have hτ : (if xsign (slotOf plV hV hneV s) then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by
      split_ifs <;> norm_num
    rw [hτ] at e
    rw [crossingPoint_crossingOf]
    show edgePoint ((shadowOf plV hV hneV).comp s.1).P s.2 (1 / 2) = _
    rw [e]
    rcases slot_mem_crossingOf plV hV hneV hk hℓ hs with h | h
    · rw [h]; exact piecePt_σSlotA_half plV hV hk hℓ
    · rw [h]; exact piecePt_σSlotB_half plV hV hk hℓ
  have hne0 : edge ((realizeAt plV hV hneV).Γ.comp s.1).P s.2 ≠ 0 :=
    (realizeAt plV hV hneV).Γ.edge_ne_zero (realizeAt plV hV hneV).generic s
  exact edgePoint_injective hne0 (hspec.symm.trans hhalf.symm)

theorem underStrand_crossingOf {k m : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m) :
    (realizeAt plV hV hneV).diagram.underStrand (crossingOf plV hV hneV hk hℓ) =
      strandOfSlot plV hV hneV (σSlotB hV hk hℓ) := by
  refine ((realizeAt plV hV hneV).diagram.eq_under_of_mem_of_ne (crossingOf plV hV hneV hk hℓ) ?_ ?_).symm
  · show _ ∈ (crossingOf plV hV hneV hk hℓ).val
    rw [crossingOf_val]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · show _ ≠ (realizeAt plV hV hneV).overStrand (crossingOf plV hV hneV hk hℓ)
    rw [overStrand_crossingOf]
    intro he
    exact σSlotA_ne_σSlotB hV hk hℓ (strandOfSlot_injective plV hV hneV he).symm

/-- The over occurrence of a `σ` crossing, as a traversal point. -/
theorem visitPt_overVisit_crossingOf {k m : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m) :
    (realizeAt plV hV hneV).diagram.visitPt ((realizeAt plV hV hneV).diagram.overVisit (crossingOf plV hV hneV hk hℓ)) =
      travPt plV hV hneV (strandOfSlot plV hV hneV (σSlotA hV hk hℓ)) ⟨1 / 2, by norm_num, by norm_num⟩ := by
  have key : ∀ (s : (realizeAt plV hV hneV).Γ.Strand) (hs : s = strandOfSlot plV hV hneV (σSlotA hV hk hℓ))
      (c : ℝ) (hc : c = 1 / 2) (h0 : 0 ≤ c) (h1 : c < 1),
      (⟨s.1, (s.2, ⟨c, h0, h1⟩)⟩ : (realizeAt plV hV hneV).Γ.Pt) =
        travPt plV hV hneV (strandOfSlot plV hV hneV (σSlotA hV hk hℓ)) ⟨1 / 2, by norm_num, by norm_num⟩ := by
    intro s hs c hc h0 h1
    subst hs; subst hc; rfl
  exact key _ (overStrand_crossingOf plV hV hneV hk hℓ) _
    (crossingParam_eq_half plV hV hneV hk hℓ ((realizeAt plV hV hneV).diagram.over_mem _))
    ((realizeAt plV hV hneV).diagram.crossingParam_pos _ _).le ((realizeAt plV hV hneV).diagram.crossingParam_lt_one _ _)

/-- The under occurrence of a `σ` crossing, as a traversal point. -/
theorem visitPt_underVisit_crossingOf {k m : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .σ m) :
    (realizeAt plV hV hneV).diagram.visitPt ((realizeAt plV hV hneV).diagram.underVisit (crossingOf plV hV hneV hk hℓ)) =
      travPt plV hV hneV (strandOfSlot plV hV hneV (σSlotB hV hk hℓ)) ⟨1 / 2, by norm_num, by norm_num⟩ := by
  have key : ∀ (s : (realizeAt plV hV hneV).Γ.Strand) (hs : s = strandOfSlot plV hV hneV (σSlotB hV hk hℓ))
      (c : ℝ) (hc : c = 1 / 2) (h0 : 0 ≤ c) (h1 : c < 1),
      (⟨s.1, (s.2, ⟨c, h0, h1⟩)⟩ : (realizeAt plV hV hneV).Γ.Pt) =
        travPt plV hV hneV (strandOfSlot plV hV hneV (σSlotB hV hk hℓ)) ⟨1 / 2, by norm_num, by norm_num⟩ := by
    intro s hs c hc h0 h1
    subst hs; subst hc; rfl
  exact key _ (underStrand_crossingOf plV hV hneV hk hℓ) _
    (crossingParam_eq_half plV hV hneV hk hℓ ((realizeAt plV hV hneV).diagram.under_mem _))
    ((realizeAt plV hV hneV).diagram.crossingParam_pos _ _).le ((realizeAt plV hV hneV).diagram.crossingParam_lt_one _ _)

end CrossingFacts

/-! ### The `σ` slots of an exterior column correspond -/

section SigmaExt

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
variable (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE hW

theorem isExtSlot_σSlotA {k m : ℕ} (hk : k < (X ++ P ++ Y).length) (hℓ : letterAt (X ++ P ++ Y) k = .σ m)
    (hcol : ExtCol X P k) : IsExtSlot X P (σSlotA hW hk hℓ).1 := by
  unfold σSlotA
  split_ifs <;> simp only [IsExtSlot, ↓reduceIte, show m ≠ 0 by have := (σ_facts hW hk hℓ).1; omega,
    show m + 1 ≠ 0 by omega]
  · exact hcol.extCut
  · exact hcol.extCut_succ

theorem isExtSlot_σSlotB {k m : ℕ} (hk : k < (X ++ P ++ Y).length) (hℓ : letterAt (X ++ P ++ Y) k = .σ m)
    (hcol : ExtCol X P k) : IsExtSlot X P (σSlotB hW hk hℓ).1 := by
  unfold σSlotB
  split_ifs <;> simp only [IsExtSlot, ↓reduceIte, show m ≠ 0 by have := (σ_facts hW hk hℓ).1; omega,
    show m + 1 ≠ 0 by omega]
  · exact hcol.extCut
  · exact hcol.extCut_succ

include hW' in
theorem extSlot_σSlotA {k m : ℕ} (hk : k < (X ++ P ++ Y).length) (hℓ : letterAt (X ++ P ++ Y) k = .σ m)
    (hcol : ExtCol X P k) :
    extSlot X P Y P' hP hE ⟨σSlotA hW hk hℓ, isExtSlot_σSlotA X P Y P' hP hE hW hk hℓ hcol⟩ =
      σSlotA hW' (shiftIdx_lt_length X P Y P' hP hcol hk) ((letterAt_ext X P Y P' hP hcol).symm.trans hℓ) := by
  apply Subtype.ext
  rw [extSlot_val]
  have hbb := bit_ext X P Y P' hP hE hcol.extCut m
  unfold σSlotA
  simp only [← hbb]
  cases hb : bit (X ++ P ++ Y) k m
  · simp only [Bool.false_eq_true, ↓reduceIte, extPair, shiftIdx_succ X P P' hP hcol]
  · simp only [↓reduceIte, extPair]

include hW' in
theorem extSlot_σSlotB {k m : ℕ} (hk : k < (X ++ P ++ Y).length) (hℓ : letterAt (X ++ P ++ Y) k = .σ m)
    (hcol : ExtCol X P k) :
    extSlot X P Y P' hP hE ⟨σSlotB hW hk hℓ, isExtSlot_σSlotB X P Y P' hP hE hW hk hℓ hcol⟩ =
      σSlotB hW' (shiftIdx_lt_length X P Y P' hP hcol hk) ((letterAt_ext X P Y P' hP hcol).symm.trans hℓ) := by
  apply Subtype.ext
  rw [extSlot_val]
  have hbb := bit_ext X P Y P' hP hE hcol.extCut (m + 1)
  unfold σSlotB
  simp only [← hbb]
  cases hb : bit (X ++ P ++ Y) k (m + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte, extPair, shiftIdx_succ X P P' hP hcol]
  · simp only [↓reduceIte, extPair]

end SigmaExt

namespace BlockSetup

variable (B : BlockSetup)

/-- the column of a crossing, as a natural number -/
abbrev colx (x : B.F.Γ.Crossing) : ℕ := (colOfCrossing B.pl B.hW B.hne x).1

theorem colx_lt (x : B.F.Γ.Crossing) : B.colx x < (B.X ++ B.P ++ B.Y).length := (colOfCrossing B.pl B.hW B.hne x).1.2

/-- the letter of the column of a crossing -/
theorem letter_colx (x : B.F.Γ.Crossing) :
    letterAt (B.X ++ B.P ++ B.Y) (B.colx x) = .σ (Classical.choose (σIdx_letter (colOfCrossing B.pl B.hW B.hne x))) :=
  Classical.choose_spec (σIdx_letter (colOfCrossing B.pl B.hW B.hne x))

/-- A crossing is outer iff its column is exterior. -/
theorem outer_iff (x : B.F.Γ.Crossing) : B.F.Γ.crossingPoint x ∉ interior B.U ↔ ExtCol B.X B.P (B.colx x) := by
  have h1 : B.F.Γ.crossingPoint x =
      B.F.Γ.crossingPoint (crossingOf B.pl B.hW B.hne (B.colx_lt x) (B.letter_colx x)) :=
    congrArg _ (eq_crossingOf B.pl B.hW B.hne x)
  rw [h1, U_eq, crossingPoint_mem_interior_iff B.pl B.hW B.hne _ _ B.hgt_le]
  unfold ExtCol
  constructor
  · intro h; omega
  · intro h; omega

/-- The corresponding crossing of the second realization (for an exterior column). -/
def ψfunGen (x : B.F.Γ.Crossing) (hx : ExtCol B.X B.P (B.colx x)) : B.F'.Γ.Crossing :=
  crossingOf B.pl' B.hW' B.hne' (shiftIdx_lt_length B.X B.P B.Y B.P' B.hP hx (B.colx_lt x))
    ((letterAt_ext B.X B.P B.Y B.P' B.hP hx).symm.trans (B.letter_colx x))

theorem colx_ψfunGen (x : B.F.Γ.Crossing) (hx : ExtCol B.X B.P (B.colx x)) :
    B.symm.colx (B.ψfunGen x hx) = shiftIdx B.X B.P B.P' (B.colx x) :=
  colOfCrossing_crossingOf B.pl' B.hW' B.hne' _ _

theorem extCol_ψfunGen (x : B.F.Γ.Crossing) (hx : ExtCol B.X B.P (B.colx x)) :
    ExtCol B.symm.X B.symm.P (B.symm.colx (B.ψfunGen x hx)) := by
  rw [colx_ψfunGen]
  exact extCol_shift B.X B.P B.P' B.hP hx

theorem ψfunGen_symm (x : B.F.Γ.Crossing) (hx : ExtCol B.X B.P (B.colx x))
    (hx' : ExtCol B.symm.X B.symm.P (B.symm.colx (B.ψfunGen x hx))) :
    B.symm.ψfunGen (B.ψfunGen x hx) hx' = x := by
  conv_rhs => rw [eq_crossingOf B.pl B.hW B.hne x]
  unfold ψfunGen
  apply crossingOf_congr_idx
  show shiftIdx B.X B.P' B.P (B.symm.colx (B.ψfunGen x hx)) = B.colx x
  rw [colx_ψfunGen]
  exact shiftIdx_inv B.X B.P B.P' B.hP B.hP' hx.extCut

/-- The outer crossings of the two realizations correspond. -/
def outerEquiv : B.F.diagram.OuterCrossing B.U ≃ B.F'.diagram.OuterCrossing B.U where
  toFun x := ⟨B.ψfunGen x.1 ((B.outer_iff x.1).1 x.2), by
    have h := B.symm.outer_iff (B.ψfunGen x.1 ((B.outer_iff x.1).1 x.2))
    rw [symm_U] at h
    exact h.2 (B.extCol_ψfunGen _ _)⟩
  invFun y := ⟨B.symm.ψfunGen y.1 (by have h := B.symm.outer_iff y.1; rw [symm_U] at h; exact h.1 y.2), by
    have h := B.outer_iff (B.symm.ψfunGen y.1 (by have h := B.symm.outer_iff y.1; rw [symm_U] at h; exact h.1 y.2))
    exact h.2 (B.symm.extCol_ψfunGen _ _)⟩
  left_inv x := Subtype.ext (B.ψfunGen_symm x.1 ((B.outer_iff x.1).1 x.2) (B.extCol_ψfunGen _ _))
  right_inv y := Subtype.ext (B.symm.ψfunGen_symm y.1
    (by have h := B.symm.outer_iff y.1; rw [symm_U] at h; exact h.1 y.2) (B.symm.extCol_ψfunGen _ _))

theorem outerEquiv_apply (x : B.F.diagram.OuterCrossing B.U) :
    (B.outerEquiv x).1 = B.ψfunGen x.1 ((B.outer_iff x.1).1 x.2) := rfl

/-- The over occurrence of an exterior `σ` crossing corresponds. -/
theorem φfun_visitPt_over {k m : ℕ} (hk : k < (B.X ++ B.P ++ B.Y).length) (hℓ : letterAt (B.X ++ B.P ++ B.Y) k = .σ m)
    (hcol : ExtCol B.X B.P k) :
    B.φfun (B.F.diagram.visitPt (B.F.diagram.overVisit (crossingOf B.pl B.hW B.hne hk hℓ))) =
      B.F'.diagram.visitPt (B.F'.diagram.overVisit (crossingOf B.pl' B.hW' B.hne'
        (shiftIdx_lt_length B.X B.P B.Y B.P' B.hP hcol hk) ((letterAt_ext B.X B.P B.Y B.P' B.hP hcol).symm.trans hℓ))) := by
  rw [visitPt_overVisit_crossingOf, visitPt_overVisit_crossingOf]
  have he : IsExtSlot B.X B.P (B.slotPt (travPt B.pl B.hW B.hne (strandOfSlot B.pl B.hW B.hne (σSlotA B.hW hk hℓ))
      ⟨1 / 2, by norm_num, by norm_num⟩)).1 := by
    show IsExtSlot B.X B.P (slotOf B.pl B.hW B.hne (strandOfSlot B.pl B.hW B.hne (σSlotA B.hW hk hℓ))).1
    rw [slotOf_strandOfSlot]
    exact isExtSlot_σSlotA B.X B.P B.Y B.P' B.hP B.hE B.hW hk hℓ hcol
  rw [φfun_of B he]
  have hu : (⟨B.slotPt (travPt B.pl B.hW B.hne (strandOfSlot B.pl B.hW B.hne (σSlotA B.hW hk hℓ))
      ⟨1 / 2, by norm_num, by norm_num⟩), he⟩ : ExtSlot B.X B.P B.Y) =
      ⟨σSlotA B.hW hk hℓ, isExtSlot_σSlotA B.X B.P B.Y B.P' B.hP B.hE B.hW hk hℓ hcol⟩ :=
    Subtype.ext (slotOf_strandOfSlot B.pl B.hW B.hne _)
  rw [hu, extSlot_σSlotA B.X B.P B.Y B.P' B.hP B.hE B.hW B.hW' hk hℓ hcol]
  rfl

/-- The under occurrence of an exterior `σ` crossing corresponds. -/
theorem φfun_visitPt_under {k m : ℕ} (hk : k < (B.X ++ B.P ++ B.Y).length) (hℓ : letterAt (B.X ++ B.P ++ B.Y) k = .σ m)
    (hcol : ExtCol B.X B.P k) :
    B.φfun (B.F.diagram.visitPt (B.F.diagram.underVisit (crossingOf B.pl B.hW B.hne hk hℓ))) =
      B.F'.diagram.visitPt (B.F'.diagram.underVisit (crossingOf B.pl' B.hW' B.hne'
        (shiftIdx_lt_length B.X B.P B.Y B.P' B.hP hcol hk) ((letterAt_ext B.X B.P B.Y B.P' B.hP hcol).symm.trans hℓ))) := by
  rw [visitPt_underVisit_crossingOf, visitPt_underVisit_crossingOf]
  have he : IsExtSlot B.X B.P (B.slotPt (travPt B.pl B.hW B.hne (strandOfSlot B.pl B.hW B.hne (σSlotB B.hW hk hℓ))
      ⟨1 / 2, by norm_num, by norm_num⟩)).1 := by
    show IsExtSlot B.X B.P (slotOf B.pl B.hW B.hne (strandOfSlot B.pl B.hW B.hne (σSlotB B.hW hk hℓ))).1
    rw [slotOf_strandOfSlot]
    exact isExtSlot_σSlotB B.X B.P B.Y B.P' B.hP B.hE B.hW hk hℓ hcol
  rw [φfun_of B he]
  have hu : (⟨B.slotPt (travPt B.pl B.hW B.hne (strandOfSlot B.pl B.hW B.hne (σSlotB B.hW hk hℓ))
      ⟨1 / 2, by norm_num, by norm_num⟩), he⟩ : ExtSlot B.X B.P B.Y) =
      ⟨σSlotB B.hW hk hℓ, isExtSlot_σSlotB B.X B.P B.Y B.P' B.hP B.hE B.hW hk hℓ hcol⟩ :=
    Subtype.ext (slotOf_strandOfSlot B.pl B.hW B.hne _)
  rw [hu, extSlot_σSlotB B.X B.P B.Y B.P' B.hP B.hE B.hW B.hW' hk hℓ hcol]
  rfl

/-- **The outside match** of the two realizations relative to the block rectangle (FINAL §8 risk 3). -/
def outsideMatch : OutsideMatch B.U B.F.diagram B.F'.diagram where
  φ := B.outEquiv
  eval_eq := fun p => B.eval_φfun (B.outPt_of_outside p.2)
  dir_pos := fun p h => ⟨1, one_pos, by rw [one_smul]; exact B.dir_φfun h⟩
  dir_pos_before := fun p h => ⟨1, one_pos, by rw [one_smul]; exact B.dir_before_φfun h⟩
  ψ := B.outerEquiv
  over_eq := fun x => by
    apply Subtype.ext
    have key := B.φfun_visitPt_over (B.colx_lt x.1) (B.letter_colx x.1) ((B.outer_iff x.1).1 x.2)
    exact (congrArg (fun y => B.φfun (B.F.diagram.visitPt (B.F.diagram.overVisit y)))
      (eq_crossingOf B.pl B.hW B.hne x.1)).trans key
  under_eq := fun x => by
    apply Subtype.ext
    have key := B.φfun_visitPt_under (B.colx_lt x.1) (B.letter_colx x.1) ((B.outer_iff x.1).1 x.2)
    exact (congrArg (fun y => B.φfun (B.F.diagram.visitPt (B.F.diagram.underVisit y)))
      (eq_crossingOf B.pl B.hW B.hne x.1)).trans key

/-- The two realizations agree outside the block. -/
theorem agreeOutside : AgreeOutside B.U B.F.diagram B.F'.diagram := ⟨B.outsideMatch⟩

end BlockSetup

end

end SM.FrontRealize
