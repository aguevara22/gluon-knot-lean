import SM.FrontRowsW2S

/-! # Front certificate rows — wave-3 delta: the front-move leaves and rows 77, 79, 80

Certificate rows lane, wave-3 delta (decision D-FR1: the lane is ported incrementally as fully proved modules).
This module imports `SM.FrontRowsW2S` (which imports `SM.FrontRowsW2`: rows 81 ng:circle and 82 ng:cusp-skein with
the shared infrastructure U1-U4, U7, U8D, U8R; then the U8R sweep block, the leaf `represent` and row 76
ng:commutation) and adds, in this order:
* **the five row-statement structures** `SM.NgFrontIClauses`, `SM.NgFrontIIClauses`, `SM.NgFrontIIIClauses`,
  `SM.NgDeletionsClauses`, `SM.NgLocalFrontBoundClauses`, verbatim from `Skeleton_W2.lean` L74-102 and L119-122
  (= `Statements_FINAL.lean`).  All five are declared here, so that the last delta (rows 78 and 83) declares none.
* **the U5 infrastructure block** (`SM.FrontRows.U5`: the band disc, the block hypothesis `Blk`, the chains, the
  crossings, the arc cover, the visits, the two-word comparison `Pair`, the general site `Pair.site_of` and the two
  patterns `site₁₂`/`site₂₁`) and **the leaf `SM.FrontRows.typeIII_site`** (ng:front-III: the two standard
  realizations of a type-III pair form an `RIIIData` site in the band disc), verbatim from `W3_U5.lean`
  (W3_U5_REPORT.md).
* **the U6 infrastructure block** (`SM.FrontRows.U6`: the generic slot-level assembly of `RIData`/`RIIData` on a
  vertex-moved slot diagram, the crossed-cusp and type-I geometries with their proofs `crossedCusp_move_proof`,
  `typeI_move_proof`, and the type-II helpers for the variants (a), (c) and the word level of (b)) and **the leaves
  `SM.FrontRows.typeI_move`** (ng:front-I: a kink removed by `RI` through a vertex-moved diagram carrying the named
  record of `realize W'`) and **`SM.FrontRows.crossedCusp_move`** (ng:deletions, crossed cusp: the same through the
  arms' exchange), verbatim from `W3_U6.lean` (W3_U6_REPORT.md).  The block also declares nine global tactic macros
  (`cc_mem`, `ccr_mem`, `tI_mem`, `tI_pair`, `tU_pair`, `tIIL_mem`, `tIIR_mem`, `aII_pair`, `cII_pair`), which importers see.
* **the polynomial consumers** `SM.FrontRows.P_typeIII`, `P_typeI`, `P_crossedCusp` (`Δd = 0` through
  `P_reidemeister_III/I` and `presentations`), verbatim from `Skeleton_W2.lean` L14619-14623, L14631-14641.
* **rows 77, 79, 80**: `SM.ng_front_I : NgFrontIClauses`, `SM.ng_front_III : NgFrontIIIClauses`,
  `SM.ng_deletions : NgDeletionsClauses`, verbatim from `Skeleton_W2.lean` L14757-14764, L14774-14804, assembled
  from the count leaves `typeI_counts`, `typeIII_counts`, `zigzag_counts`, `crossedCusp_counts`, the polynomial
  leaf `P_zigzag` and the nonemptiness helpers (all in `SM.FrontRowsW2`) and the three consumers above.

Every declaration in this module is fully proved: the axioms of `SM.ng_front_I`, `SM.ng_front_III`,
`SM.ng_deletions` are `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` is the accepted literature
interface reached through `P`); those of `SM.FrontRows.typeIII_site`, `typeI_move`, `crossedCusp_move` are
`[propext, Classical.choice, Quot.sound]`.  Provenance and line map: `work/drafts/frontrows/W3_DELTA_REPORT.md`.

NOT in this module — the last delta (`import SM.FrontRowsW3`) adds exactly these and declares nothing else: the
leaf `SM.FrontRows.typeII_move` (`Skeleton_W2.lean` L11103-11112; its variants (b) and (d) are being proved in a
follow-up unit, whose helpers `U6.typeII_b`, `U6.typeII_d`, `U6.typeII_move_proof` go there too), its consumer
`P_typeII` (L14625-14629), row 78 `ng_front_II` (L14765-14772), `certificate_laws` and `word_bound`
(L14842-14877), and row 83 `ng_local_front_bound` (L14878-14889).

Checked with `cd work/lean && lake env lean`. -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

/-! ## Statements of rows 77, 78, 79, 80 and 83 (verbatim from `Skeleton_W2.lean` L74-102 and L119-122 = `Statements_FINAL.lean`) -/

structure NgFrontIClauses : Prop where
  typeI_B : ∀ W W' : OWord, IsTypeI W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgFrontIIClauses : Prop where
  typeII_D : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  typeII_w : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  typeII_d : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  typeII_B : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgFrontIIIClauses : Prop where
  typeIII_D : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  typeIII_w : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  typeIII_d : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  typeIII_B : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgDeletionsClauses : Prop where
  zigzag_s : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').sCount + 2 = (realize W).sCount
  zigzag_B : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect
  crossedCusp_s : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').sCount + 1 = (realize W).sCount
  crossedCusp_B : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect

structure NgLocalFrontBoundClauses : Prop where
  front_inequality : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1

namespace FrontRows

section Leaves

/-! ### L-geo (units U5, U6 on the geometry core U4) — the disc-local moves through the accepted
`RIData`/`RIIData`/`RIIIData` (`P_reidemeister_I/II/III`).  The move disc is a convex polygon hugging the
active strands (spectator strands run parallel one unit away, so such a disc exists; the full-height block
rectangle is NOT admissible: `ArcCover` forbids spectators).  For the length-changing patterns the comparison
diagram is a vertex-moved copy `D` of `realize W` (same shadow structure, the active strand's interior vertices
moved inside the disc, the removed crossings gone, everything else literally equal: `MoveMatch` with the
identity), whose named record is that of `realize W'` (record core U2, "active set" variant). -/

/-! ### U5 infrastructure -/

namespace U5

open SM.FrontRealize SM.FrontWord.Letter Equiv U4

noncomputable section

/-! #### A. The band disc `[x_k, x_{k+3}] × [−(m+2)−¼, −m+¼]` (standard placement) -/

/-- the four half-planes of the band -/
def bandL (k m : ℕ) : List HalfPlane :=
  [HalfPlane.xge (Placement.std.x k), HalfPlane.xle (Placement.std.x (k + 3)),
   HalfPlane.yge (-((m : ℝ) + 2) - 1 / 4), HalfPlane.yle (-(m : ℝ) + 1 / 4)]

/-- the band disc -/
abbrev band (k m : ℕ) : Set Plane := polygon (bandL k m)

theorem xge_mem_bandL (k m : ℕ) : HalfPlane.xge (Placement.std.x k) ∈ bandL k m := by simp [bandL]
theorem xle_mem_bandL (k m : ℕ) : HalfPlane.xle (Placement.std.x (k + 3)) ∈ bandL k m := by simp [bandL]
theorem yge_mem_bandL (k m : ℕ) : HalfPlane.yge (-((m : ℝ) + 2) - 1 / 4) ∈ bandL k m := by simp [bandL]
theorem yle_mem_bandL (k m : ℕ) : HalfPlane.yle (-(m : ℝ) + 1 / 4) ∈ bandL k m := by simp [bandL]

theorem mem_band_iff (k m : ℕ) (q : Plane) :
    q ∈ band k m ↔
      (k : ℝ) ≤ q.1 ∧ q.1 ≤ (k : ℝ) + 3 ∧ -((m : ℝ) + 2) - 1 / 4 ≤ q.2 ∧ q.2 ≤ -(m : ℝ) + 1 / 4 := by
  rw [mem_polygon_iff]
  simp only [bandL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yge, HalfPlane.b_yge,
    HalfPlane.f_yle, HalfPlane.b_yle, Placement.std_x]
  push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, h4⟩

theorem mem_interior_band_iff (k m : ℕ) (q : Plane) :
    q ∈ interior (band k m) ↔
      (k : ℝ) < q.1 ∧ q.1 < (k : ℝ) + 3 ∧ -((m : ℝ) + 2) - 1 / 4 < q.2 ∧ q.2 < -(m : ℝ) + 1 / 4 := by
  rw [mem_interior_polygon_iff]
  simp only [bandL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yge, HalfPlane.b_yge,
    HalfPlane.f_yle, HalfPlane.b_yle, Placement.std_x]
  push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, h4⟩

theorem isDisc_band (k m : ℕ) : IsDisc (band k m) := by
  refine isDisc_polygon (bandL k m) (a := k) (b := (k : ℝ) + 3) (c := -((m : ℝ) + 2) - 1 / 4)
    (d := -(m : ℝ) + 1 / 4) ?_ ?_
  · intro q hq; exact (mem_band_iff k m q).1 hq
  · refine ⟨((k : ℝ) + 1, -(m : ℝ) - 1), ?_⟩
    intro h hh
    simp only [bandL, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl <;>
      simp only [HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yge,
        HalfPlane.b_yge, HalfPlane.f_yle, HalfPlane.b_yle, Placement.std_x]
    all_goals first | linarith | (push_cast; linarith)

/-- a segment with both ends in the closed band `[k, k+3] × [−(m+2), −m]`, not both on the same vertical
side, is inside -/
theorem segIn_band {k m : ℕ} {p₀ p₁ : Plane}
    (h0 : (k : ℝ) ≤ p₀.1 ∧ p₀.1 ≤ (k : ℝ) + 3 ∧ -((m : ℝ) + 2) ≤ p₀.2 ∧ p₀.2 ≤ -(m : ℝ))
    (h1 : (k : ℝ) ≤ p₁.1 ∧ p₁.1 ≤ (k : ℝ) + 3 ∧ -((m : ℝ) + 2) ≤ p₁.2 ∧ p₁.2 ≤ -(m : ℝ))
    (hx : (k : ℝ) < p₀.1 ∨ (k : ℝ) < p₁.1) (hx' : p₀.1 < (k : ℝ) + 3 ∨ p₁.1 < (k : ℝ) + 3) :
    SegIn (bandL k m) p₀ p₁ := by
  intro h hh
  simp only [bandL, List.mem_cons, List.not_mem_nil, or_false] at hh
  obtain ⟨h01, h02, h03, h04⟩ := h0
  obtain ⟨h11, h12, h13, h14⟩ := h1
  rcases hh with rfl | rfl | rfl | rfl
  · simp only [HalfPlane.f_xge, HalfPlane.b_xge, Placement.std_x]
    refine ⟨by linarith, by linarith, ?_⟩
    rcases hx with hx | hx
    · left; linarith
    · right; linarith
  · simp only [HalfPlane.f_xle, HalfPlane.b_xle, Placement.std_x]
    push_cast
    refine ⟨by linarith, by linarith, ?_⟩
    rcases hx' with hx' | hx'
    · left; linarith
    · right; linarith
  · simp only [HalfPlane.f_yge, HalfPlane.b_yge]
    exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
  · simp only [HalfPlane.f_yle, HalfPlane.b_yle]
    exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩

/-- a segment strictly above the band is outside -/
theorem segOut_band_above {k m : ℕ} {p₀ p₁ : Plane} (h0 : -(m : ℝ) + 1 / 4 < p₀.2)
    (h1 : -(m : ℝ) + 1 / 4 < p₁.2) : SegOut (bandL k m) p₀ p₁ :=
  segOut_of_lt _ (yle_mem_bandL k m) (by simpa using h0) (by simpa using h1)

/-- a segment strictly below the band is outside -/
theorem segOut_band_below {k m : ℕ} {p₀ p₁ : Plane} (h0 : p₀.2 < -((m : ℝ) + 2) - 1 / 4)
    (h1 : p₁.2 < -((m : ℝ) + 2) - 1 / 4) : SegOut (bandL k m) p₀ p₁ :=
  segOut_of_lt _ (yge_mem_bandL k m) (by simp only [HalfPlane.f_yge, HalfPlane.b_yge]; linarith)
    (by simp only [HalfPlane.f_yge, HalfPlane.b_yge]; linarith)

theorem std_mid (c : ℕ) : Placement.std.mid c = (c : ℝ) + 1 / 2 := by
  simp only [Placement.mid, Placement.w, Placement.std_x]; push_cast; ring

theorem pt_std_cut (V : Word) {k p : ℕ} (hp : p ≠ 0) : pt .std V (k, p) = ((k : ℝ), -(p : ℝ)) := by
  rw [pt_cut _ _ hp]; rfl

/-! #### B. The position swap of a `σ` letter -/

/-- the position map of `σ a`: exchanges `a` and `a+1` -/
def swp (a p : ℕ) : ℕ := if p = a then a + 1 else if p = a + 1 then a else p

theorem posR_σ_eq (a p : ℕ) : (Letter.σ a).posR p = some (swp a p) := by
  rw [posR_σ]; unfold swp; split_ifs <;> first | rfl | (exfalso; omega)

theorem posL_σ_eq (a p : ℕ) : (Letter.σ a).posL p = some (swp a p) := by
  rw [posL_σ]; unfold swp; split_ifs <;> first | rfl | (exfalso; omega)

theorem swp_swp (a p : ℕ) : swp a (swp a p) = p := by unfold swp; split_ifs <;> omega

theorem swp_inj {a p q : ℕ} (h : swp a p = swp a q) : p = q := by
  have := congrArg (swp a) h; rwa [swp_swp, swp_swp] at this

theorem swp_mem {a m p : ℕ} (ha : a = m ∨ a = m + 1) (hp : m ≤ p ∧ p ≤ m + 2) :
    m ≤ swp a p ∧ swp a p ≤ m + 2 := by
  unfold swp; split_ifs <;> omega

theorem swp_of_not {a m p : ℕ} (ha : a = m ∨ a = m + 1) (hp : ¬ (m ≤ p ∧ p ≤ m + 2)) : swp a p = p := by
  unfold swp; split_ifs <;> omega

/-! #### C. The block hypothesis and the single-word facts -/

/-- The block hypothesis: columns `k, k+1, k+2` of `V` carry `σ (a i)` with `a i ∈ {m, m+1}`, `1 ≤ m`, and the
cut before the block has at least `m+2` strands. -/
structure Blk (V : Word) (k m : ℕ) (a : ℕ → ℕ) : Prop where
  hk : k + 3 ≤ V.length
  hm : 1 ≤ m
  letter : ∀ i, i < 3 → letterAt V (k + i) = .σ (a i)
  idx : ∀ i, i < 3 → a i = m ∨ a i = m + 1
  len : m + 2 ≤ (cut V k).length

section OneWord

variable {V : Word} (hV : V.Closed) {k m : ℕ} {a : ℕ → ℕ}
include hV

/-- the vertices of the realization -/
abbrev pt₀ (V : Word) : Slot V → Plane := fun u => pt .std V u.1

/-- the bit of a strand is carried across a `σ` column -/
theorem bit_swp {k' : ℕ} (hk' : k' < V.length) {b : ℕ} (hℓ : letterAt V k' = .σ b) {p : ℕ}
    (hp : 1 ≤ p) (hpc : p ≤ (cut V k').length) : bit V (k' + 1) (swp b p) = bit V k' p := by
  obtain ⟨D⟩ := decomp hV k' hk'
  rw [hℓ] at D
  have := D.posR_some hp hpc (posR_σ_eq b p)
  rw [bit_eq, bit_eq]; exact this.2.2.1

theorem cutSlot_facts' {u : Slot V} {k' p : ℕ} (hu : u.1 = (k', p)) (hp : p ≠ 0) :
    1 ≤ p ∧ p ≤ (cut V k').length ∧ 0 < k' ∧ k' < V.length := by
  have hs := u.2
  rw [hu] at hs
  rcases hs with ⟨h0, -, -⟩ | ⟨h1, h2, -⟩
  · exact absurd h0 hp
  · exact ⟨h1, h2, cutSlot_pos hV h1 h2⟩

/-- one rightward step through a `σ` column -/
theorem step_right {u : Slot V} {k' p b : ℕ} (hu : u.1 = (k', p)) (hp : p ≠ 0)
    (hb : bit V k' p = true) (hℓ : letterAt V k' = .σ b) :
    (next hV u).1 = (k' + 1, swp b p) ∧ bit V (k' + 1) (swp b p) = true := by
  obtain ⟨hp1, hpc, -, hk'⟩ := cutSlot_facts' hV hu hp
  refine ⟨?_, ?_⟩
  · rw [next_val, hu, nextPair_right V hp hb (by rw [hℓ]; exact posR_σ_eq b p)]
  · rw [bit_swp hV hk' hℓ hp1 hpc, hb]

/-- one leftward step through a `σ` column -/
theorem step_left {u : Slot V} {k' q b : ℕ} (hu : u.1 = (k' + 1, q)) (hq : q ≠ 0)
    (hb : bit V (k' + 1) q = false) (hℓ : letterAt V k' = .σ b) :
    (next hV u).1 = (k', swp b q) ∧ bit V k' (swp b q) = false := by
  obtain ⟨hq1, hqc, -, hk1⟩ := cutSlot_facts' hV hu hq
  have hk' : k' < V.length := by omega
  refine ⟨?_, ?_⟩
  · rw [next_val, hu, nextPair_left V hq hb (by rw [Nat.add_sub_cancel, hℓ]; exact posL_σ_eq b q)]
    simp
  · obtain ⟨D⟩ := decomp hV k' hk'
    rw [hℓ] at D
    have := D.posL_some hq1 hqc (posL_σ_eq b q)
    rw [bit_eq, this.2.2.1, ← bit_eq, hb]

namespace Blk

variable (hB : Blk V k m a)
include hB

omit hV in
theorem hk_i (i : ℕ) (hi : i < 3) : k + i < V.length := by have := hB.hk; omega

omit hV in
theorem idx_pos (i : ℕ) (hi : i < 3) : 1 ≤ a i := by
  rcases hB.idx i hi with h | h <;> have := hB.hm <;> omega

omit hV in
theorem not_r (k' : ℕ) (h1 : k ≤ k') (h2 : k' < k + 3) (m' : ℕ) : letterAt V k' ≠ .r m' := by
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 3 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
  rw [hB.letter i hi]; exact fun h => by cases h

omit hV in
theorem isCrossing_blk (k' : ℕ) (h1 : k ≤ k') (h2 : k' < k + 3) : (letterAt V k').isCrossing = true := by
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 3 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
  rw [hB.letter i hi]; rfl

omit hV in
/-- a cusp slot lies outside the block -/
theorem cusp_ext (u : Slot V) (h0 : u.1.2 = 0) : u.1.1 < k ∨ k + 3 ≤ u.1.1 := by
  obtain ⟨⟨k', p⟩, hs⟩ := u
  simp only at h0
  subst h0
  rcases hs with ⟨-, -, hσ⟩ | ⟨h1, -, -⟩
  · by_contra hc
    push Not at hc
    rw [hB.isCrossing_blk k' hc.1 hc.2] at hσ
    cases hσ
  · omega

omit hV hB in
theorem cusp_letter_ext (hB : Blk V k m a) {k' : ℕ} (hs : IsSlot V (k', 0)) : k' < k ∨ k + 3 ≤ k' :=
  hB.cusp_ext ⟨(k', 0), hs⟩ rfl

theorem cutLen (i : ℕ) (hi : i ≤ 3) : (cut V (k + i)).length = (cut V k).length := by
  induction i with
  | zero => rfl
  | succ n ih =>
    have := (σ_facts hV (hB.hk_i n (by omega)) (hB.letter n (by omega))).2.2.1
    rw [show k + (n + 1) = k + n + 1 by omega, this, ih (by omega)]

/-- bits of spectator positions are unchanged across the block -/
theorem bit_spec (i : ℕ) (hi : i ≤ 3) {p : ℕ} (hp0 : p ≠ 0) (hp : ¬ (m ≤ p ∧ p ≤ m + 2)) :
    bit V (k + i) p = bit V k p := by
  induction i with
  | zero => rfl
  | succ n ih =>
    have hkn := hB.hk_i n (by omega)
    have hℓ := hB.letter n (by omega)
    have ha := hB.idx n (by omega)
    by_cases hpc : p ≤ (cut V (k + n)).length
    · have := bit_swp hV hkn hℓ (by omega) hpc
      rw [swp_of_not ha hp] at this
      rw [show k + (n + 1) = k + n + 1 by omega, this, ih (by omega)]
    · -- out of range on both sides: both bits are `false`
      have h1 : bit V (k + n) p = false := by
        rw [bit_eq]; apply List.getD_eq_default; omega
      have h2 : bit V (k + (n + 1)) p = false := by
        rw [bit_eq]; apply List.getD_eq_default
        rw [show k + (n + 1) = k + n + 1 by omega,
          (σ_facts hV hkn hℓ).2.2.1]; omega
      rw [h2, ← ih (by omega), h1]

end Blk

/-! positions along the block -/

/-- the position of the strand entering at position `p` at cut `k`, after `i` columns -/
def pos (a : ℕ → ℕ) (p : ℕ) : ℕ → ℕ
  | 0 => p
  | i + 1 => swp (a i) (pos a p i)

omit hV in
@[simp] theorem pos_zero (a : ℕ → ℕ) (p : ℕ) : pos a p 0 = p := rfl
omit hV in
theorem pos_succ (a : ℕ → ℕ) (p i : ℕ) : pos a p (i + 1) = swp (a i) (pos a p i) := rfl

namespace Blk

variable (hB : Blk V k m a)
include hB

omit hV in
theorem pos_mem {p : ℕ} (hp : m ≤ p ∧ p ≤ m + 2) : ∀ i, i ≤ 3 → m ≤ pos a p i ∧ pos a p i ≤ m + 2 := by
  intro i
  induction i with
  | zero => intro _; exact hp
  | succ n ih => intro hn; rw [pos_succ]; exact swp_mem (hB.idx n (by omega)) (ih (by omega))

omit hV in
theorem pos_ne_zero {p : ℕ} (hp : m ≤ p ∧ p ≤ m + 2) (i : ℕ) (hi : i ≤ 3) : pos a p i ≠ 0 := by
  have := hB.pos_mem hp i hi; have := hB.hm; omega

omit hV hB in
theorem pos_inj {p q : ℕ} (i : ℕ) (h : pos a p i = pos a q i) : p = q := by
  induction i with
  | zero => exact h
  | succ n ih => exact ih (swp_inj h)

theorem bit_pos {p : ℕ} (hp : m ≤ p ∧ p ≤ m + 2) : ∀ i, i ≤ 3 → bit V (k + i) (pos a p i) = bit V k p := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hmem := hB.pos_mem hp n (by omega)
    have hlen : pos a p n ≤ (cut V (k + n)).length := by
      rw [hB.cutLen hV n (by omega)]; have := hB.len; omega
    rw [show k + (n + 1) = k + n + 1 by omega, pos_succ,
      bit_swp hV (hB.hk_i n (by omega)) (hB.letter n (by omega)) (by have := hB.hm; omega) hlen, ih (by omega)]

theorem isSlot_pos {p : ℕ} (hp : m ≤ p ∧ p ≤ m + 2) (i : ℕ) (hi : i ≤ 3) : IsSlot V (k + i, pos a p i) := by
  have hmem := hB.pos_mem hp i hi
  refine isSlot_cut (by have := hB.hm; omega) ?_ (by have := hB.hk; omega)
  rw [hB.cutLen hV i hi]; have := hB.len; omega

/-- the rightward passage of an active strand through the block -/
theorem iterate_right {p : ℕ} (hp : m ≤ p ∧ p ≤ m + 2) (hb : bit V k p = true) (u : Slot V)
    (hu : u.1 = (k, p)) : ∀ i, i ≤ 3 → ((next hV)^[i] u).1 = (k + i, pos a p i) := by
  intro i
  induction i with
  | zero => intro _; simpa using hu
  | succ n ih =>
    intro hn
    rw [Function.iterate_succ_apply']
    have h1 := ih (by omega)
    have hbn : bit V (k + n) (pos a p n) = true := by rw [hB.bit_pos hV hp n (by omega)]; exact hb
    exact (step_right hV h1 (hB.pos_ne_zero hp n (by omega)) hbn (hB.letter n (by omega))).1

/-- the leftward passage of an active strand through the block (entering at cut `k+3` at the exit position
of the strand at position `p`) -/
theorem iterate_left {p : ℕ} (hp : m ≤ p ∧ p ≤ m + 2) (hb : bit V k p = false) (u : Slot V)
    (hu : u.1 = (k + 3, pos a p 3)) : ∀ i, i ≤ 3 → ((next hV)^[i] u).1 = (k + (3 - i), pos a p (3 - i)) := by
  intro i
  induction i with
  | zero => intro _; simpa using hu
  | succ n ih =>
    intro hn
    rw [Function.iterate_succ_apply']
    have h1 := ih (by omega)
    have e : 3 - n = (2 - n) + 1 := by omega
    have e2 : 3 - (n + 1) = 2 - n := by omega
    rw [e] at h1
    have hbn : bit V (k + (2 - n) + 1) (pos a p (2 - n + 1)) = false := by
      have := hB.bit_pos hV hp (2 - n + 1) (by omega)
      rw [hb] at this; exact this
    have := (step_left hV h1 (hB.pos_ne_zero hp (2 - n + 1) (by omega)) hbn (hB.letter (2 - n) (by omega))).1
    rw [e2, this, pos_succ, swp_swp]
    rfl

end Blk

/-! #### D. Piece classification relative to the band -/

omit hV in
theorem segIn_band_nat {k m i₀ i₁ p₀ p₁ : ℕ} (hi₀ : i₀ ≤ 3) (hi₁ : i₁ ≤ 3) (hp₀ : m ≤ p₀ ∧ p₀ ≤ m + 2)
    (hp₁ : m ≤ p₁ ∧ p₁ ≤ m + 2) (hx : 1 ≤ i₀ ∨ 1 ≤ i₁) (hx' : i₀ ≤ 2 ∨ i₁ ≤ 2) :
    SegIn (bandL k m) (((k + i₀ : ℕ) : ℝ), -(p₀ : ℝ)) (((k + i₁ : ℕ) : ℝ), -(p₁ : ℝ)) := by
  have h0 : (i₀ : ℝ) ≤ 3 := by exact_mod_cast hi₀
  have h1 : (i₁ : ℝ) ≤ 3 := by exact_mod_cast hi₁
  have hp0l : (m : ℝ) ≤ p₀ := by exact_mod_cast hp₀.1
  have hp0u : (p₀ : ℝ) ≤ m + 2 := by exact_mod_cast hp₀.2
  have hp1l : (m : ℝ) ≤ p₁ := by exact_mod_cast hp₁.1
  have hp1u : (p₁ : ℝ) ≤ m + 2 := by exact_mod_cast hp₁.2
  apply segIn_band
  · push_cast; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · push_cast; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · push_cast
    rcases hx with hx | hx
    · left; have : (1 : ℝ) ≤ i₀ := by exact_mod_cast hx
      linarith
    · right; have : (1 : ℝ) ≤ i₁ := by exact_mod_cast hx
      linarith
  · push_cast
    rcases hx' with hx' | hx'
    · left; have : (i₀ : ℝ) ≤ 2 := by exact_mod_cast hx'
      linarith
    · right; have : (i₁ : ℝ) ≤ 2 := by exact_mod_cast hx'
      linarith

omit hV in
theorem segOut_band_nat {k m : ℕ} {x₀ x₁ : ℝ} {p : ℕ} (hp : ¬ (m ≤ p ∧ p ≤ m + 2)) :
    SegOut (bandL k m) (x₀, -(p : ℝ)) (x₁, -(p : ℝ)) := by
  rcases (by omega : p + 1 ≤ m ∨ m + 3 ≤ p) with h | h
  · have : (p : ℝ) + 1 ≤ m := by exact_mod_cast h
    exact segOut_band_above (by simp only; linarith) (by simp only; linarith)
  · have : (m : ℝ) + 3 ≤ p := by exact_mod_cast h
    exact segOut_band_below (by simp only; linarith) (by simp only; linarith)

omit hV in
theorem mem_interior_band_nat {k m i p : ℕ} (hi : 1 ≤ i ∧ i ≤ 2) (hp : m ≤ p ∧ p ≤ m + 2) :
    (((k + i : ℕ) : ℝ), -(p : ℝ)) ∈ interior (band k m) := by
  rw [mem_interior_band_iff]
  have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
  have h2 : (i : ℝ) ≤ 2 := by exact_mod_cast hi.2
  have h3 : (m : ℝ) ≤ p := by exact_mod_cast hp.1
  have h4 : (p : ℝ) ≤ m + 2 := by exact_mod_cast hp.2
  push_cast
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

omit hV in
theorem colOf_pair {u : Slot V} {k' p : ℕ} (hu : u.1 = (k', p)) :
    colOf u = if p = 0 then k' else if bit V k' p then k' else k' - 1 := by
  obtain ⟨⟨k'', p''⟩, hs⟩ := u
  simp only [Prod.mk.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  exact U2.colOf_mk _ _ hs

/-- the piece before a rightward cut slot lies in the previous column -/
theorem colOf_prev_of_true {u : Slot V} {k' p : ℕ} (hu : u.1 = (k', p)) (hp : p ≠ 0)
    (hb : bit V k' p = true) : colOf (prev hV u) = k' - 1 := by
  obtain ⟨hp1, hpc, hk0, hk'⟩ := cutSlot_facts' hV hu hp
  obtain ⟨D⟩ := decomp hV (k' - 1) (by omega)
  rw [Nat.sub_add_cancel hk0] at D
  cases hq : (letterAt V (k' - 1)).posL p with
  | none =>
    have e : (prev hV u).1 = (k' - 1, 0) := by rw [prev_val, hu, prevPair_right_none V hp hb hq]
    rw [colOf_pair e]; simp
  | some q =>
    have e : (prev hV u).1 = (k' - 1, q) := by rw [prev_val, hu, prevPair_right V hp hb hq]
    have hh := D.posL_some hp1 hpc hq
    have hbq : bit V (k' - 1) q = true := by rw [bit_eq, hh.2.2.1, ← bit_eq, hb]
    rw [colOf_pair e]; simp [show q ≠ 0 by omega, hbq]

/-- the piece before a leftward cut slot lies in the slot's own column -/
theorem colOf_prev_of_false {u : Slot V} {k' p : ℕ} (hu : u.1 = (k', p)) (hp : p ≠ 0)
    (hb : bit V k' p = false) : colOf (prev hV u) = k' := by
  obtain ⟨hp1, hpc, -, hk'⟩ := cutSlot_facts' hV hu hp
  obtain ⟨D⟩ := decomp hV k' hk'
  cases hq : (letterAt V k').posR p with
  | none =>
    have e : (prev hV u).1 = (k', 0) := by rw [prev_val, hu, prevPair_left_none V hp hb hq]
    rw [colOf_pair e]; simp
  | some q =>
    have e : (prev hV u).1 = (k' + 1, q) := by rw [prev_val, hu, prevPair_left V hp hb hq]
    have hh := D.posR_some hp1 hpc hq
    have hbq : bit V (k' + 1) q = false := by rw [bit_eq, hh.2.2.1, ← bit_eq, hb]
    rw [colOf_pair e]; simp [show q ≠ 0 by omega, hbq]

namespace Blk

variable (hB : Blk V k m a)
include hB

omit hB in
/-- the exterior pieces are outside the band -/
theorem pieceOut_ext {u : Slot V} (hcol : colOf u + 1 ≤ k ∨ k + 3 ≤ colOf u) :
    PieceOut (bandL k m) hV (pt₀ V) u :=
  pieceOut_of_extCol (bandL k m) .std hV (pt₀ V) (xge_mem_bandL k m) (xle_mem_bandL k m) ⟨rfl, rfl⟩ hcol

theorem pieceIn_right (u : Slot V) {i p : ℕ} (hu : u.1 = (k + i, p)) (hi : i ≤ 2) (hp : m ≤ p ∧ p ≤ m + 2)
    (hb : bit V (k + i) p = true) : PieceIn (bandL k m) hV (pt₀ V) u := by
  have hp0 : p ≠ 0 := by have := hB.hm; omega
  obtain ⟨hn, -⟩ := step_right hV hu hp0 hb (hB.letter i (by omega))
  have hq := swp_mem (hB.idx i (by omega)) hp
  have hq0 : swp (a i) p ≠ 0 := by have := hB.hm; omega
  unfold PieceIn
  simp only [pt₀]
  rw [hu, hn, pt_std_cut V hp0, pt_std_cut V hq0]
  exact segIn_band_nat (i₀ := i) (i₁ := i + 1) (by omega) (by omega) hp hq (Or.inr (by omega)) (Or.inl hi)

theorem pieceIn_left (u : Slot V) {i p : ℕ} (hu : u.1 = (k + i + 1, p)) (hi : i ≤ 2) (hp : m ≤ p ∧ p ≤ m + 2)
    (hb : bit V (k + i + 1) p = false) : PieceIn (bandL k m) hV (pt₀ V) u := by
  have hp0 : p ≠ 0 := by have := hB.hm; omega
  obtain ⟨hn, -⟩ := step_left hV hu hp0 hb (hB.letter i (by omega))
  have hq := swp_mem (hB.idx i (by omega)) hp
  have hq0 : swp (a i) p ≠ 0 := by have := hB.hm; omega
  unfold PieceIn
  simp only [pt₀]
  rw [hu, hn, pt_std_cut V hp0, pt_std_cut V hq0]
  exact segIn_band_nat (i₀ := i + 1) (i₁ := i) (by omega) (by omega) hp hq (Or.inl (by omega)) (Or.inr hi)

theorem pieceOut_spec_right (u : Slot V) {i p : ℕ} (hu : u.1 = (k + i, p)) (hi : i ≤ 2) (hp0 : p ≠ 0)
    (hp : ¬ (m ≤ p ∧ p ≤ m + 2)) (hb : bit V (k + i) p = true) : PieceOut (bandL k m) hV (pt₀ V) u := by
  obtain ⟨hn, -⟩ := step_right hV hu hp0 hb (hB.letter i (by omega))
  rw [swp_of_not (hB.idx i (by omega)) hp] at hn
  unfold PieceOut
  simp only [pt₀]
  rw [hu, hn, pt_std_cut V hp0, pt_std_cut V hp0]
  exact segOut_band_nat hp

theorem pieceOut_spec_left (u : Slot V) {i p : ℕ} (hu : u.1 = (k + i + 1, p)) (hi : i ≤ 2) (hp0 : p ≠ 0)
    (hp : ¬ (m ≤ p ∧ p ≤ m + 2)) (hb : bit V (k + i + 1) p = false) : PieceOut (bandL k m) hV (pt₀ V) u := by
  obtain ⟨hn, -⟩ := step_left hV hu hp0 hb (hB.letter i (by omega))
  rw [swp_of_not (hB.idx i (by omega)) hp] at hn
  unfold PieceOut
  simp only [pt₀]
  rw [hu, hn, pt_std_cut V hp0, pt_std_cut V hp0]
  exact segOut_band_nat hp

/-- **Classification**: every piece of the realization is inside or outside the band. -/
theorem classify (u : Slot V) : PieceIn (bandL k m) hV (pt₀ V) u ∨ PieceOut (bandL k m) hV (pt₀ V) u := by
  obtain ⟨⟨k', p⟩, hs⟩ := u
  have hcol := U2.colOf_mk k' p hs
  by_cases hp0 : p = 0
  · right
    subst hp0
    have hc := hB.cusp_letter_ext hs
    refine pieceOut_ext hV ?_
    rw [hcol]; simp only [↓reduceIte]; omega
  · obtain ⟨hp1, hpc, hk0, hk'⟩ := cutSlot_facts' hV (u := ⟨(k', p), hs⟩) rfl hp0
    simp only [hp0, ↓reduceIte] at hcol
    by_cases hext : k' < k ∨ k + 3 < k'
    · right
      refine pieceOut_ext hV ?_
      rw [hcol]; split_ifs <;> omega
    · push Not at hext
      by_cases hpm : m ≤ p ∧ p ≤ m + 2
      · cases hb : bit V k' p
        · by_cases hkk : k' = k
          · right
            refine pieceOut_ext hV ?_
            rw [hcol, hb]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
          · left
            obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ 2 ∧ k' = k + i + 1 := ⟨k' - k - 1, by omega, by omega⟩
            exact hB.pieceIn_left hV ⟨(k + i + 1, p), hs⟩ rfl hi hpm hb
        · by_cases hkk : k' = k + 3
          · right
            refine pieceOut_ext hV ?_
            rw [hcol, hb]; simp only [↓reduceIte]; omega
          · left
            obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ 2 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
            exact hB.pieceIn_right hV ⟨(k + i, p), hs⟩ rfl hi hpm hb
      · right
        cases hb : bit V k' p
        · by_cases hkk : k' = k
          · refine pieceOut_ext hV ?_
            rw [hcol, hb]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
          · obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ 2 ∧ k' = k + i + 1 := ⟨k' - k - 1, by omega, by omega⟩
            exact hB.pieceOut_spec_left hV ⟨(k + i + 1, p), hs⟩ rfl hi hp0 hpm hb
        · by_cases hkk : k' = k + 3
          · refine pieceOut_ext hV ?_
            rw [hcol, hb]; simp only [↓reduceIte]; omega
          · obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ 2 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
            exact hB.pieceOut_spec_right hV ⟨(k + i, p), hs⟩ rfl hi hp0 hpm hb

omit hV in
/-- the vertices in the open band: the six interior active slots -/
theorem pt_mem_interior_iff (u : Slot V) :
    pt₀ V u ∈ interior (band k m) ↔ (u.1.1 = k + 1 ∨ u.1.1 = k + 2) ∧ m ≤ u.1.2 ∧ u.1.2 ≤ m + 2 := by
  obtain ⟨⟨k', p⟩, hs⟩ := u
  simp only [pt₀]
  by_cases hp0 : p = 0
  · subst hp0
    have hc := hB.cusp_letter_ext hs
    rw [pt_cusp, mem_interior_band_iff, std_mid]
    simp only
    constructor
    · rintro ⟨h1, h2, -, -⟩
      exfalso
      rcases hc with hc | hc
      · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hc
        linarith
      · have : (k : ℝ) + 3 ≤ k' := by exact_mod_cast hc
        linarith
    · rintro ⟨-, h, -⟩; have := hB.hm; omega
  · rw [pt_std_cut V hp0, mem_interior_band_iff]
    simp only
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have e1 : k < k' := by exact_mod_cast h1
      have e2 : k' < k + 3 := by exact_mod_cast (show (k' : ℝ) < ((k + 3 : ℕ) : ℝ) by push_cast; linarith)
      have e3 : p < m + 3 := by exact_mod_cast (show (p : ℝ) < ((m + 3 : ℕ) : ℝ) by push_cast; linarith)
      have e4 : m < p + 1 := by exact_mod_cast (show (m : ℝ) < ((p + 1 : ℕ) : ℝ) by push_cast; linarith)
      omega
    · rintro ⟨h1, h2, h3⟩
      have e2 : (m : ℝ) ≤ p := by exact_mod_cast h2
      have e3 : (p : ℝ) ≤ m + 2 := by exact_mod_cast h3
      rcases h1 with rfl | rfl <;> push_cast <;> exact ⟨by linarith, by linarith, by linarith, by linarith⟩

omit hB in
theorem not_mem_interior_of_pieceOut {u : Slot V} (h : PieceOut (bandL k m) hV (pt₀ V) u) :
    pt₀ V u ∉ interior (band k m) :=
  h.left_notMem_interior

/-- every component leaves the band -/
theorem exits : ExitsMv (bandL k m) hV (pt₀ V) :=
  exitsMv_of_ext hV (bandL k m) .std (pt₀ V) (xge_mem_bandL k m) (xle_mem_bandL k m) (fun _ _ => ⟨rfl, rfl⟩)
    (fun u => exists_ext_of_no_r hV k (k + 3) (fun k' h1 h2 m' => hB.not_r k' h1 h2 m') u)

/-- every cycle reaches a vertex outside the open band -/
theorem exists_out (u : Slot V) : ∃ n : ℕ, pt₀ V (((nextPerm hV) ^ n) u) ∉ interior (band k m) := by
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_r hV k (k + 3) (fun k' h1 h2 m' => hB.not_r k' h1 h2 m') u
  obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hV hsc
  refine ⟨n, ?_⟩
  rw [U2.nextPerm_pow_apply hV, hn]
  exact not_mem_interior_of_pieceOut hV (pieceOut_ext hV hcol)

/-- the realization meets the band cleanly -/
theorem clean (hne : V ≠ []) : Clean (band k m) (realizeAt .std hV hne).diagram :=
  clean_mv (bandL k m) .std hV hne (pt₀ V) (pt_injective .std V) (hB.classify hV) (hB.exits hV)
    (generic .std hV hne) (realizeAt .std hV hne).overStrand (realizeAt .std hV hne).overStrand_mem

/-! #### E. The chains of the three active strands -/

/-- the cut index of the `t`-th slot of a chain traversed rightward (`b = true`) or leftward -/
def cidx (b : Bool) (t : ℕ) : ℕ := if b then t else 3 - t

omit hV hB in
theorem cidx_le {b : Bool} {t : ℕ} (ht : t ≤ 3) : cidx b t ≤ 3 := by unfold cidx; split_ifs <;> omega

/-- the chain of the strand entering the block at position `m + j` (rightward from cut `k` if its bit is `true`,
leftward from cut `k+3` otherwise) -/
def chain (j : ℕ) (hj : j < 3) : Chain V :=
  if bit V k (m + j) then ⟨⟨(k, m + j), hB.isSlot_pos hV ⟨by omega, by omega⟩ 0 (by omega)⟩, 3, by norm_num⟩
  else ⟨⟨(k + 3, pos a (m + j) 3), hB.isSlot_pos hV ⟨by omega, by omega⟩ 3 le_rfl⟩, 3, by norm_num⟩

theorem chain_n (j : ℕ) (hj : j < 3) : (hB.chain hV j hj).n = 3 := by unfold chain; split_ifs <;> rfl

theorem chain_u₀ (j : ℕ) (hj : j < 3) :
    (hB.chain hV j hj).u₀.1 = if bit V k (m + j) then (k, m + j) else (k + 3, pos a (m + j) 3) := by
  unfold chain; split_ifs <;> rfl

theorem chain_slot (j : ℕ) (hj : j < 3) (t : ℕ) (ht : t ≤ 3) :
    ((hB.chain hV j hj).slot hV t).1 =
      (k + cidx (bit V k (m + j)) t, pos a (m + j) (cidx (bit V k (m + j)) t)) := by
  have hp : m ≤ m + j ∧ m + j ≤ m + 2 := ⟨by omega, by omega⟩
  unfold Chain.slot cidx
  cases hb : bit V k (m + j)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hB.iterate_left hV hp hb _ (by rw [hB.chain_u₀ hV j hj, hb]; simp) t ht
  · simp only [↓reduceIte]
    exact hB.iterate_right hV hp hb _ (by rw [hB.chain_u₀ hV j hj, hb]; simp) t ht

theorem chain_slot_bit (j : ℕ) (hj : j < 3) (t : ℕ) (ht : t ≤ 3) :
    bit V (k + cidx (bit V k (m + j)) t) (pos a (m + j) (cidx (bit V k (m + j)) t)) = bit V k (m + j) :=
  hB.bit_pos hV ⟨by omega, by omega⟩ _ (cidx_le ht)

omit hV in
theorem chain_slot_pos_mem (j : ℕ) (hj : j < 3) (t : ℕ) (ht : t ≤ 3) :
    m ≤ pos a (m + j) (cidx (bit V k (m + j)) t) ∧ pos a (m + j) (cidx (bit V k (m + j)) t) ≤ m + 2 :=
  hB.pos_mem ⟨by omega, by omega⟩ _ (cidx_le ht)

/-- the chains are chains of inside pieces -/
theorem chain_isChain (j : ℕ) (hj : j < 3) : (hB.chain hV j hj).IsChain (bandL k m) hV (pt₀ V) where
  pieceIn t ht := by
    rw [hB.chain_n] at ht
    have hs := hB.chain_slot hV j hj t (by omega)
    have hbt := hB.chain_slot_bit hV j hj t (by omega)
    have hpm := hB.chain_slot_pos_mem j hj t (by omega)
    cases hb : bit V k (m + j)
    · rw [hb] at hs hbt hpm
      simp only [cidx, Bool.false_eq_true, ↓reduceIte] at hs hbt hpm
      have e : k + (3 - t) = k + (2 - t) + 1 := by omega
      rw [e] at hs hbt
      exact hB.pieceIn_left hV _ hs (by omega) hpm hbt
    · rw [hb] at hs hbt hpm
      simp only [cidx, ↓reduceIte] at hs hbt hpm
      exact hB.pieceIn_right hV _ hs (by omega) hpm hbt
  vertex_interior t ht0 ht := by
    rw [hB.chain_n] at ht
    have hs := hB.chain_slot hV j hj t (by omega)
    have hpm := hB.chain_slot_pos_mem j hj t (by omega)
    have hp0 : pos a (m + j) (cidx (bit V k (m + j)) t) ≠ 0 := by have := hB.hm; omega
    simp only [pt₀]
    rw [hs, pt_std_cut V hp0]
    apply mem_interior_band_nat _ hpm
    unfold cidx; split_ifs <;> omega
  out_prev := by
    have hu := hB.chain_u₀ hV j hj
    have hp0 : m + j ≠ 0 := by have := hB.hm; omega
    cases hb : bit V k (m + j)
    · rw [hb] at hu
      simp only [Bool.false_eq_true, ↓reduceIte] at hu
      have hb3 : bit V (k + 3) (pos a (m + j) 3) = false := by
        rw [hB.bit_pos hV ⟨by omega, by omega⟩ 3 le_rfl, hb]
      refine pieceOut_ext hV (Or.inr ?_)
      rw [colOf_prev_of_false hV hu (hB.pos_ne_zero ⟨by omega, by omega⟩ 3 le_rfl) hb3]
    · rw [hb] at hu
      simp only [↓reduceIte] at hu
      obtain ⟨-, -, hk0, -⟩ := cutSlot_facts' hV hu hp0
      refine pieceOut_ext hV (Or.inl ?_)
      rw [colOf_prev_of_true hV hu hp0 hb]; omega
  out_stop := by
    rw [hB.chain_n]
    have hs := hB.chain_slot hV j hj 3 le_rfl
    have hbt := hB.chain_slot_bit hV j hj 3 le_rfl
    have hp0 : m + j ≠ 0 := by have := hB.hm; omega
    cases hb : bit V k (m + j)
    · rw [hb] at hs hbt
      simp only [cidx, Bool.false_eq_true, ↓reduceIte, Nat.sub_self, Nat.add_zero, pos_zero] at hs hbt
      obtain ⟨-, -, hk0, -⟩ := cutSlot_facts' hV hs hp0
      refine pieceOut_ext hV (Or.inl ?_)
      rw [colOf_pair hs]; simp only [hp0, hbt, Bool.false_eq_true, ↓reduceIte]; omega
    · rw [hb] at hs hbt
      simp only [cidx, ↓reduceIte] at hs hbt
      refine pieceOut_ext hV (Or.inr ?_)
      rw [colOf_pair hs]; simp only [hB.pos_ne_zero (p := m + j) ⟨by omega, by omega⟩ 3 le_rfl, hbt, ↓reduceIte]; omega

/-! #### F. The crossings of the block -/

/-- the crossing of column `k + i` -/
def xcol (hne : V ≠ []) (i : ℕ) (hi : i < 3) : (realizeAt .std hV hne).Γ.Crossing :=
  crossingOf .std hV hne (hB.hk_i i hi) (hB.letter i hi)

theorem xcol_ne (hne : V ≠ []) {i i' : ℕ} (hi : i < 3) (hi' : i' < 3) (h : i ≠ i') :
    hB.xcol hV hne i hi ≠ hB.xcol hV hne i' hi' := by
  intro he
  have h1 := colOfCrossing_crossingOf .std hV hne (hB.hk_i i hi) (hB.letter i hi)
  have h2 := colOfCrossing_crossingOf .std hV hne (hB.hk_i i' hi') (hB.letter i' hi')
  unfold xcol at he
  rw [he] at h1
  rw [h1] at h2
  omega

omit hB in
/-- every crossing is the crossing of some `σ` column (forgetting the dependence on the crossing) -/
theorem crossing_cases (hne : V ≠ []) (y : (realizeAt .std hV hne).Γ.Crossing) :
    ∃ (c : ℕ) (hc : c < V.length) (m' : ℕ) (hℓ : letterAt V c = .σ m'), y = crossingOf .std hV hne hc hℓ :=
  ⟨_, _, _, _, eq_crossingOf .std hV hne y⟩

/-- the crossings in the open band are exactly the three block crossings -/
theorem crossingPoint_mem_interior_iff (hne : V ≠ []) (y : (realizeAt .std hV hne).Γ.Crossing) :
    (realizeAt .std hV hne).Γ.crossingPoint y ∈ interior (band k m) ↔
      ∃ i, ∃ hi : i < 3, y = hB.xcol hV hne i hi := by
  obtain ⟨c, hc, m', hℓ', rfl⟩ := crossing_cases hV hne y
  rw [crossingPoint_crossingOf, mem_interior_band_iff, std_mid]
  simp only
  constructor
  · rintro ⟨h1, h2, -, -⟩
    have e1 : k < c + 1 := by exact_mod_cast (show (k : ℝ) < ((c + 1 : ℕ) : ℝ) by push_cast; linarith)
    have e2 : c < k + 3 := by exact_mod_cast (show (c : ℝ) < ((k + 3 : ℕ) : ℝ) by push_cast; linarith)
    refine ⟨c - k, by omega, ?_⟩
    unfold Blk.xcol
    exact crossingOf_congr_idx .std hV hne (by omega) hc (hB.hk_i (c - k) (by omega)) hℓ'
      (hB.letter (c - k) (by omega))
  · rintro ⟨i, hi, he⟩
    unfold Blk.xcol at he
    have hcol := colOfCrossing_crossingOf .std hV hne hc hℓ'
    rw [he, colOfCrossing_crossingOf] at hcol
    -- hcol : k + i = c
    have hm'' : m' = a i := by
      have := hB.letter i hi
      rw [← hcol] at hℓ'
      exact Letter.σ.inj (hℓ'.symm.trans this)
    subst hm''
    have hai : (a i : ℝ) = m ∨ (a i : ℝ) = m + 1 := by
      rcases hB.idx i hi with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    have hci : (c : ℝ) = k + i := by rw [← hcol]; push_cast; ring
    have hi2 : (i : ℝ) ≤ 2 := by exact_mod_cast (show i ≤ 2 by omega)
    rw [hci]
    rcases hai with h | h <;> rw [h] <;> exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Blk

/-! #### G. Active slots, the arc cover -/

/-- an *active* slot: its piece is one of the nine block pieces of the three strands -/
def Active (V : Word) (k m : ℕ) (u : Slot V) : Prop :=
  ∃ i p, u.1 = (k + i, p) ∧ i ≤ 3 ∧ (m ≤ p ∧ p ≤ m + 2) ∧
    (bit V (k + i) p = true → i ≤ 2) ∧ (bit V (k + i) p = false → 1 ≤ i)

omit hV in
/-- the position after `i` columns is `pos a (m + j) i` for a unique strand `j` -/
theorem pos_surj {a : ℕ → ℕ} {m : ℕ} (i : ℕ) (hmem : ∀ j, j < 3 → m ≤ pos a (m + j) i ∧ pos a (m + j) i ≤ m + 2)
    {p : ℕ} (hp : m ≤ p ∧ p ≤ m + 2) : ∃ j, j < 3 ∧ pos a (m + j) i = p := by
  by_contra h
  push Not at h
  have h0 := hmem 0 (by norm_num)
  have h1 := hmem 1 (by norm_num)
  have h2 := hmem 2 (by norm_num)
  have n01 : pos a (m + 0) i ≠ pos a (m + 1) i := fun e => by have := Blk.pos_inj i e; omega
  have n02 : pos a (m + 0) i ≠ pos a (m + 2) i := fun e => by have := Blk.pos_inj i e; omega
  have n12 : pos a (m + 1) i ≠ pos a (m + 2) i := fun e => by have := Blk.pos_inj i e; omega
  have := h 0 (by norm_num)
  have := h 1 (by norm_num)
  have := h 2 (by norm_num)
  omega

namespace Blk

variable (hB : Blk V k m a)
include hB

theorem pieceIn_of_active {u : Slot V} (h : Active V k m u) : PieceIn (bandL k m) hV (pt₀ V) u := by
  obtain ⟨i, p, hu, hi, hp, hR, hL⟩ := h
  cases hb : bit V (k + i) p
  · have hi1 := hL hb
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact hB.pieceIn_left hV u hu (by omega) hp hb
  · exact hB.pieceIn_right hV u hu (hR hb) hp hb

/-- every slot is active or its piece is outside the band -/
theorem active_or_out (u : Slot V) : Active V k m u ∨ PieceOut (bandL k m) hV (pt₀ V) u := by
  obtain ⟨⟨k', p⟩, hs⟩ := u
  have hcol := U2.colOf_mk k' p hs
  by_cases hp0 : p = 0
  · right
    subst hp0
    have hc := hB.cusp_letter_ext hs
    refine pieceOut_ext hV ?_
    rw [hcol]; simp only [↓reduceIte]; omega
  · obtain ⟨hp1, hpc, hk0, hk'⟩ := cutSlot_facts' hV (u := ⟨(k', p), hs⟩) rfl hp0
    simp only [hp0, ↓reduceIte] at hcol
    by_cases hext : k' < k ∨ k + 3 < k'
    · right
      refine pieceOut_ext hV ?_
      rw [hcol]; split_ifs <;> omega
    · push Not at hext
      by_cases hpm : m ≤ p ∧ p ≤ m + 2
      · cases hb : bit V k' p
        · by_cases hkk : k' = k
          · right
            refine pieceOut_ext hV ?_
            rw [hcol, hb]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
          · left
            refine ⟨k' - k, p, Prod.ext (show k' = k + (k' - k) by omega) rfl, by omega, hpm, ?_, fun _ => by omega⟩
            intro hb'; rw [show k + (k' - k) = k' by omega, hb] at hb'; cases hb'
        · by_cases hkk : k' = k + 3
          · right
            refine pieceOut_ext hV ?_
            rw [hcol, hb]; simp only [↓reduceIte]; omega
          · left
            refine ⟨k' - k, p, Prod.ext (show k' = k + (k' - k) by omega) rfl, by omega, hpm, fun _ => by omega, ?_⟩
            intro hb'; rw [show k + (k' - k) = k' by omega, hb] at hb'; cases hb'
      · right
        cases hb : bit V k' p
        · by_cases hkk : k' = k
          · refine pieceOut_ext hV ?_
            rw [hcol, hb]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
          · obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ 2 ∧ k' = k + i + 1 := ⟨k' - k - 1, by omega, by omega⟩
            exact hB.pieceOut_spec_left hV ⟨(k + i + 1, p), hs⟩ rfl hi hp0 hpm hb
        · by_cases hkk : k' = k + 3
          · refine pieceOut_ext hV ?_
            rw [hcol, hb]; simp only [↓reduceIte]; omega
          · obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ 2 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
            exact hB.pieceOut_spec_right hV ⟨(k + i, p), hs⟩ rfl hi hp0 hpm hb

theorem active_of_pieceIn {u : Slot V} (h : PieceIn (bandL k m) hV (pt₀ V) u) : Active V k m u :=
  (hB.active_or_out hV u).resolve_right fun ho => not_pieceIn_of_pieceOut (bandL k m) hV (pt₀ V) ho h

theorem classify' (u : Slot V) : PieceIn (bandL k m) hV (pt₀ V) u ∨ PieceOut (bandL k m) hV (pt₀ V) u :=
  (hB.active_or_out hV u).imp (hB.pieceIn_of_active hV) id

/-- an active slot is a slot of one of the three chains -/
theorem active_mem_chain {u : Slot V} (h : Active V k m u) :
    ∃ j, ∃ hj : j < 3, ∃ t, t < 3 ∧ (hB.chain hV j hj).slot hV t = u := by
  obtain ⟨i, p, hu, hi, hp, hR, hL⟩ := h
  obtain ⟨j, hj, hpos⟩ := pos_surj i (fun j hj => hB.pos_mem ⟨by omega, by omega⟩ i hi) hp
  have hbj : bit V k (m + j) = bit V (k + i) p := by
    rw [← hB.bit_pos hV (p := m + j) ⟨by omega, by omega⟩ i hi, hpos]
  refine ⟨j, hj, ?_⟩
  cases hb : bit V (k + i) p
  · have hi1 := hL hb
    rw [hb] at hbj
    refine ⟨3 - i, by omega, Subtype.ext ?_⟩
    rw [hB.chain_slot hV j hj (3 - i) (by omega), hbj, hu]
    simp only [cidx, Bool.false_eq_true, ↓reduceIte]
    rw [show 3 - (3 - i) = i by omega, hpos]
  · have hi2 := hR hb
    rw [hb] at hbj
    refine ⟨i, by omega, Subtype.ext ?_⟩
    rw [hB.chain_slot hV j hj i hi, hbj, hu]
    simp only [cidx, ↓reduceIte]
    rw [hpos]

/-- slots of different chains differ -/
theorem chain_slot_ne {j j' : ℕ} (hj : j < 3) (hj' : j' < 3) (hjj : j ≠ j') {t t' : ℕ} (ht : t ≤ 3) (ht' : t' ≤ 3) :
    (hB.chain hV j hj).slot hV t ≠ (hB.chain hV j' hj').slot hV t' := by
  intro he
  have h1 := hB.chain_slot hV j hj t ht
  have h2 := hB.chain_slot hV j' hj' t' ht'
  rw [he, h2] at h1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨h1a, h1b⟩ := h1
  have e : cidx (bit V k (m + j')) t' = cidx (bit V k (m + j)) t := by omega
  rw [e] at h1b
  have := pos_inj _ h1b
  omega

theorem chain_ne {j j' : ℕ} (hj : j < 3) (hj' : j' < 3) (hjj : j ≠ j') : hB.chain hV j hj ≠ hB.chain hV j' hj' := by
  intro he
  have := hB.chain_slot_ne hV hj hj' hjj (t := 0) (t' := 0) (by omega) (by omega)
  exact this (by rw [he])

omit hV in
/-- the vertices in the closed band are the cut slots of the block cuts at active positions -/
theorem pt_mem_band (u : Slot V) (h : pt₀ V u ∈ band k m) :
    ∃ k' p, u.1 = (k', p) ∧ p ≠ 0 ∧ k ≤ k' ∧ k' ≤ k + 3 ∧ m ≤ p ∧ p ≤ m + 2 := by
  obtain ⟨⟨k', p⟩, hs⟩ := u
  simp only [pt₀] at h
  by_cases hp0 : p = 0
  · exfalso
    subst hp0
    have hc := hB.cusp_letter_ext hs
    rw [pt_cusp, mem_band_iff, std_mid] at h
    simp only at h
    obtain ⟨h1, h2, -, -⟩ := h
    rcases hc with hc | hc
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hc
      linarith
    · have : (k : ℝ) + 3 ≤ k' := by exact_mod_cast hc
      linarith
  · rw [pt_std_cut V hp0, mem_band_iff] at h
    simp only at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨k', p, rfl, hp0, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast h1
    · exact_mod_cast (show (k' : ℝ) ≤ ((k + 3 : ℕ) : ℝ) by push_cast; linarith)
    · have : m < p + 1 := by exact_mod_cast (show (m : ℝ) < ((p + 1 : ℕ) : ℝ) by push_cast; linarith)
      omega
    · have : p < m + 3 := by exact_mod_cast (show (p : ℝ) < ((m + 3 : ℕ) : ℝ) by push_cast; linarith)
      omega

omit hB in
/-- the predecessor of a rightward exit slot: the last block piece of its strand -/
theorem prev_of_true_σ {u : Slot V} {k' p b : ℕ} (hu : u.1 = (k' + 1, p)) (hp : p ≠ 0)
    (hb : bit V (k' + 1) p = true) (hℓ : letterAt V k' = .σ b) :
    (prev hV u).1 = (k', swp b p) ∧ bit V k' (swp b p) = true := by
  obtain ⟨hp1, hpc, -, hk1⟩ := cutSlot_facts' hV hu hp
  have hk' : k' < V.length := by omega
  obtain ⟨D⟩ := decomp hV k' hk'
  rw [hℓ] at D
  have hh := D.posL_some hp1 hpc (posL_σ_eq b p)
  refine ⟨?_, ?_⟩
  · rw [prev_val, hu, prevPair_right V hp hb (by rw [Nat.add_sub_cancel, hℓ]; exact posL_σ_eq b p)]
    simp
  · rw [bit_eq, hh.2.2.1, ← bit_eq, hb]

omit hB in
/-- the predecessor of a leftward exit slot: the first block piece of its strand -/
theorem prev_of_false_σ {u : Slot V} {k' p b : ℕ} (hu : u.1 = (k', p)) (hp : p ≠ 0)
    (hb : bit V k' p = false) (hℓ : letterAt V k' = .σ b) :
    (prev hV u).1 = (k' + 1, swp b p) ∧ bit V (k' + 1) (swp b p) = false := by
  obtain ⟨hp1, hpc, -, hk'⟩ := cutSlot_facts' hV hu hp
  obtain ⟨D⟩ := decomp hV k' hk'
  rw [hℓ] at D
  have hh := D.posR_some hp1 hpc (posR_σ_eq b p)
  refine ⟨?_, ?_⟩
  · rw [prev_val, hu, prevPair_left V hp hb (by rw [hℓ]; exact posR_σ_eq b p)]
  · rw [bit_eq, hh.2.2.1, ← bit_eq, hb]

/-- no touching from outside: an outside piece whose tail is in the band is preceded by an inside piece -/
theorem touch (u : Slot V) (ho : PieceOut (bandL k m) hV (pt₀ V) u) (hmem : pt₀ V u ∈ band k m) :
    PieceIn (bandL k m) hV (pt₀ V) (prev hV u) := by
  obtain ⟨k', p, hu, hp0, hk1, hk2, hpm1, hpm2⟩ := hB.pt_mem_band u hmem
  have hna : ¬ Active V k m u := fun ha => not_pieceIn_of_pieceOut (bandL k m) hV (pt₀ V) ho (hB.pieceIn_of_active hV ha)
  cases hb : bit V k' p
  · -- leftward: the slot must be `(k, p)`
    have hkk : k' = k := by
      by_contra hne
      apply hna
      refine ⟨k' - k, p, by rw [hu]; exact Prod.ext (show k' = k + (k' - k) by omega) rfl, by omega, ⟨hpm1, hpm2⟩, ?_, fun _ => by omega⟩
      intro hb'; rw [show k + (k' - k) = k' by omega, hb] at hb'; cases hb'
    subst hkk
    obtain ⟨hn, hbn⟩ := prev_of_false_σ hV hu hp0 hb (hB.letter 0 (by norm_num))
    exact hB.pieceIn_left hV _ (i := 0) hn (by norm_num) (swp_mem (hB.idx 0 (by norm_num)) ⟨hpm1, hpm2⟩) hbn
  · -- rightward: the slot must be `(k + 3, p)`
    have hkk : k' = k + 3 := by
      by_contra hne
      apply hna
      refine ⟨k' - k, p, by rw [hu]; exact Prod.ext (show k' = k + (k' - k) by omega) rfl, by omega, ⟨hpm1, hpm2⟩, fun _ => by omega, ?_⟩
      intro hb'; rw [show k + (k' - k) = k' by omega, hb] at hb'; cases hb'
    subst hkk
    obtain ⟨hn, hbn⟩ := prev_of_true_σ hV (k' := k + 2) hu hp0 hb (hB.letter 2 (by norm_num))
    exact hB.pieceIn_right hV _ (i := 2) hn (by norm_num) (swp_mem (hB.idx 2 (by norm_num)) ⟨hpm1, hpm2⟩) hbn

/-- the three chains -/
def chains : List (Chain V) := [hB.chain hV 0 (by norm_num), hB.chain hV 1 (by norm_num), hB.chain hV 2 (by norm_num)]

theorem mem_chains_iff (c : Chain V) : c ∈ hB.chains hV ↔ ∃ j, ∃ hj : j < 3, c = hB.chain hV j hj := by
  simp only [chains, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    · left; rfl
    · right; left; rfl
    · right; right; rfl

/-- **the arc cover of the band by the three strands** -/
theorem arcCover (hne : V ≠ []) :
    (shadowMv .std hV hne (pt₀ V)).ArcCover (band k m) (arcsOf .std hV hne (pt₀ V) (hB.chains hV)) := by
  refine arcCover_of (bandL k m) .std hV hne (pt₀ V) (hB.chains hV) ?_ (hB.classify' hV) ?_ ?_ (hB.touch hV)
  · intro c hc
    obtain ⟨j, hj, rfl⟩ := (hB.mem_chains_iff hV c).1 hc
    exact hB.chain_isChain hV j hj
  · intro u hu
    obtain ⟨j, hj, t, ht, hteq⟩ := hB.active_mem_chain hV (hB.active_of_pieceIn hV hu)
    exact ⟨hB.chain hV j hj, (hB.mem_chains_iff hV _).2 ⟨j, hj, rfl⟩, t, by rw [hB.chain_n]; exact ht, hteq⟩
  · intro c hc c' hc' hcc t ht t' ht'
    obtain ⟨j, hj, rfl⟩ := (hB.mem_chains_iff hV c).1 hc
    obtain ⟨j', hj', rfl⟩ := (hB.mem_chains_iff hV c').1 hc'
    rw [hB.chain_n] at ht ht'
    have hjj : j ≠ j' := fun e => hcc (by subst e; rfl)
    exact hB.chain_slot_ne hV hj hj' hjj (by omega) (by omega)

theorem arcsOf_chains (hne : V ≠ []) :
    arcsOf .std hV hne (pt₀ V) (hB.chains hV) =
      {(hB.chain hV 0 (by norm_num)).toArc .std hV hne (pt₀ V), (hB.chain hV 1 (by norm_num)).toArc .std hV hne (pt₀ V),
        (hB.chain hV 2 (by norm_num)).toArc .std hV hne (pt₀ V)} := by
  ext x
  simp only [arcsOf, chains, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left]

/-! #### H. Visits of the block crossings along the chains -/

/-- the parameter `1/2` -/
def half : Set.Ico (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

omit hB in
/-- the traversal point of a visit, in the `travMv` vocabulary -/
theorem visitPt_eq (hne : V ≠ []) (v : (realizeAt .std hV hne).diagram.Γ.Visit) :
    (realizeAt .std hV hne).diagram.visitPt v =
      travMv .std hV hne (pt₀ V) (slotOf .std hV hne v.2.1)
        ⟨(realizeAt .std hV hne).diagram.crossingParam v.1 v.2.2,
          ((realizeAt .std hV hne).diagram.crossingParam_pos v.1 v.2.2).le,
          (realizeAt .std hV hne).diagram.crossingParam_lt_one v.1 v.2.2⟩ := by
  apply pt_ext'
  · show v.2.1 = (idxEquiv hV).symm (idxEquiv hV v.2.1)
    exact (Equiv.symm_apply_apply _ _).symm
  · rfl

omit hB in
theorem travMv_congr (hne : V ≠ []) (u : Slot V) {s s' : Set.Ico (0 : ℝ) 1} (h : s.val = s'.val) :
    travMv .std hV hne (pt₀ V) u s = travMv .std hV hne (pt₀ V) u s' := by
  rw [Subtype.ext h]

omit hB in
theorem travMv_inj (hne : V ≠ []) {u u' : Slot V} {s s' : Set.Ico (0 : ℝ) 1}
    (h : travMv .std hV hne (pt₀ V) u s = travMv .std hV hne (pt₀ V) u' s') : u = u' ∧ s = s' := by
  have h1 := congrArg (slotPtMv .std hV hne (pt₀ V)) h
  rw [slotPtMv_travMv, slotPtMv_travMv] at h1
  have h2 := congrArg (fun p : (shadowMv .std hV hne (pt₀ V)).Pt => p.2.2) h
  exact ⟨h1, h2⟩

theorem crossingParam_xcol (hne : V ≠ []) (i : ℕ) (hi : i < 3) {s : (realizeAt .std hV hne).Γ.Strand}
    (hs : s ∈ (hB.xcol hV hne i hi).val) :
    (realizeAt .std hV hne).diagram.crossingParam (hB.xcol hV hne i hi) hs = 1 / 2 :=
  crossingParam_eq_half .std hV hne (hB.hk_i i hi) (hB.letter i hi) hs

theorem slot_mem_xcol (hne : V ≠ []) (i : ℕ) (hi : i < 3) {s : (realizeAt .std hV hne).Γ.Strand}
    (hs : s ∈ (hB.xcol hV hne i hi).val) :
    slotOf .std hV hne s = σSlotA hV (hB.hk_i i hi) (hB.letter i hi) ∨
      slotOf .std hV hne s = σSlotB hV (hB.hk_i i hi) (hB.letter i hi) :=
  slot_mem_crossingOf .std hV hne (hB.hk_i i hi) (hB.letter i hi) hs

theorem strandA_mem_xcol (hne : V ≠ []) (i : ℕ) (hi : i < 3) :
    strandOfSlot .std hV hne (σSlotA hV (hB.hk_i i hi) (hB.letter i hi)) ∈ (hB.xcol hV hne i hi).val := by
  unfold xcol; rw [crossingOf_val]; exact Finset.mem_insert_self _ _

theorem strandB_mem_xcol (hne : V ≠ []) (i : ℕ) (hi : i < 3) :
    strandOfSlot .std hV hne (σSlotB hV (hB.hk_i i hi) (hB.letter i hi)) ∈ (hB.xcol hV hne i hi).val := by
  unfold xcol; rw [crossingOf_val]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem crossingParam_eq_of (hne : V ≠ []) (i : ℕ) (hi : i < 3) (x : (realizeAt .std hV hne).Γ.Crossing)
    (hx : x = hB.xcol hV hne i hi) {s : (realizeAt .std hV hne).Γ.Strand} (hs : s ∈ x.val) :
    (realizeAt .std hV hne).diagram.crossingParam x hs = 1 / 2 := by
  subst hx; exact hB.crossingParam_xcol hV hne i hi hs

/-- the traversal point of a visit of a block crossing: its strand's slot at parameter `1/2` -/
theorem visitPt_xcol (hne : V ≠ []) (i : ℕ) (hi : i < 3) (v : (realizeAt .std hV hne).diagram.Γ.Visit)
    (hv : v.1 = hB.xcol hV hne i hi) :
    (realizeAt .std hV hne).diagram.visitPt v = travMv .std hV hne (pt₀ V) (slotOf .std hV hne v.2.1) half := by
  rw [visitPt_eq]
  exact travMv_congr hV hne _ (hB.crossingParam_eq_of hV hne i hi v.1 hv v.2.2)

omit hB in
/-- a visit from a crossing and one of its strands -/
def mkVisit (hne : V ≠ []) (x : (realizeAt .std hV hne).Γ.Crossing) (s : (realizeAt .std hV hne).Γ.Strand)
    (hs : s ∈ x.val) : (realizeAt .std hV hne).diagram.Γ.Visit := ⟨x, ⟨s, hs⟩⟩

omit hB in
theorem mkVisit_fst (hne : V ≠ []) (x : (realizeAt .std hV hne).Γ.Crossing) (s : (realizeAt .std hV hne).Γ.Strand)
    (hs : s ∈ x.val) : (mkVisit hV hne x s hs).1 = x := rfl

omit hB in
theorem mkVisit_strand (hne : V ≠ []) (x : (realizeAt .std hV hne).Γ.Crossing) (s : (realizeAt .std hV hne).Γ.Strand)
    (hs : s ∈ x.val) : (mkVisit hV hne x s hs).2.1 = s := rfl

/-- the over strand of a block crossing is on the chain carrying `σSlotA` -/
theorem overOn_xcol (hne : V ≠ []) (i : ℕ) (hi : i < 3) (c : Chain V) (hc : c.IsChain (bandL k m) hV (pt₀ V))
    {t : ℕ} (ht : t < c.n) (hA : σSlotA hV (hB.hk_i i hi) (hB.letter i hi) = c.slot hV t) :
    (realizeAt .std hV hne).diagram.OverOn (c.toArc .std hV hne (pt₀ V)) (hB.xcol hV hne i hi) := by
  unfold Diagram.OverOn
  rw [hB.visitPt_xcol hV hne i hi ((realizeAt .std hV hne).diagram.overVisit (hB.xcol hV hne i hi)) rfl]
  have e : slotOf .std hV hne ((realizeAt .std hV hne).diagram.overVisit (hB.xcol hV hne i hi)).2.1 = c.slot hV t := by
    show slotOf .std hV hne ((realizeAt .std hV hne).overStrand (hB.xcol hV hne i hi)) = _
    unfold Blk.xcol
    rw [overStrand_crossingOf, slotOf_strandOfSlot, hA]
  rw [e]
  exact hc.mem_of_slot .std hne ht _

/-- the under strand of a block crossing is on the chain carrying `σSlotB` -/
theorem underOn_xcol (hne : V ≠ []) (i : ℕ) (hi : i < 3) (c : Chain V) (hc : c.IsChain (bandL k m) hV (pt₀ V))
    {t : ℕ} (ht : t < c.n) (hBs : σSlotB hV (hB.hk_i i hi) (hB.letter i hi) = c.slot hV t) :
    (realizeAt .std hV hne).diagram.UnderOn (c.toArc .std hV hne (pt₀ V)) (hB.xcol hV hne i hi) := by
  unfold Diagram.UnderOn
  rw [hB.visitPt_xcol hV hne i hi ((realizeAt .std hV hne).diagram.underVisit (hB.xcol hV hne i hi)) rfl]
  have e : slotOf .std hV hne ((realizeAt .std hV hne).diagram.underVisit (hB.xcol hV hne i hi)).2.1 = c.slot hV t := by
    show slotOf .std hV hne ((realizeAt .std hV hne).diagram.underStrand (hB.xcol hV hne i hi)) = _
    unfold Blk.xcol
    rw [underStrand_crossingOf, slotOf_strandOfSlot, hBs]
  rw [e]
  exact hc.mem_of_slot .std hne ht _

/-- **the traversal order of two block crossings along a chain**: given by the slot indices of their strands on
the chain (the other strand of each crossing being off the chain) -/
theorem beforeOn_xcol_iff (hne : V ≠ []) {i i' : ℕ} (hi : i < 3) (hi' : i' < 3) (c : Chain V)
    (hc : c.IsChain (bandL k m) hV (pt₀ V)) {t t' : ℕ} (ht : t < c.n) (ht' : t' < c.n)
    (hx : ∀ s, s ∈ (hB.xcol hV hne i hi).val →
      slotOf .std hV hne s = c.slot hV t ∨ ∀ j, j < c.n → slotOf .std hV hne s ≠ c.slot hV j)
    (hx' : ∃ s, ∃ _ : s ∈ (hB.xcol hV hne i hi).val, slotOf .std hV hne s = c.slot hV t)
    (hy : ∀ s, s ∈ (hB.xcol hV hne i' hi').val →
      slotOf .std hV hne s = c.slot hV t' ∨ ∀ j, j < c.n → slotOf .std hV hne s ≠ c.slot hV j)
    (hy' : ∃ s, ∃ _ : s ∈ (hB.xcol hV hne i' hi').val, slotOf .std hV hne s = c.slot hV t') :
    (realizeAt .std hV hne).diagram.BeforeOn (c.toArc .std hV hne (pt₀ V)) (hB.xcol hV hne i hi)
      (hB.xcol hV hne i' hi') ↔ t < t' := by
  have hper := hc.n_lt_period
  constructor
  · rintro ⟨v, w, hv, hw, hb⟩
    have hv2 : v.2.1 ∈ (hB.xcol hV hne i hi).val := by rw [← hv]; exact v.2.2
    have hw2 : w.2.1 ∈ (hB.xcol hV hne i' hi').val := by rw [← hw]; exact w.2.2
    rw [hB.visitPt_xcol hV hne i hi v hv, hB.visitPt_xcol hV hne i' hi' w hw] at hb
    obtain ⟨j, hj, τ, hτ, -⟩ := (hc.inner_iff .std hne _).1 hb.inner_left
    obtain ⟨j', hj', τ', hτ', -⟩ := (hc.inner_iff .std hne _).1 hb.inner_right
    obtain ⟨e1, -⟩ := travMv_inj hV hne hτ
    obtain ⟨e2, -⟩ := travMv_inj hV hne hτ'
    have hjt : j = t := by
      rcases hx _ hv2 with h | h
      · exact iterate_injOn hV c.u₀ (by omega) (by omega) (e1.symm.trans h)
      · exact absurd e1 (h j hj)
    have hjt' : j' = t' := by
      rcases hy _ hw2 with h | h
      · exact iterate_injOn hV c.u₀ (by omega) (by omega) (e2.symm.trans h)
      · exact absurd e2 (h j' hj')
    subst hjt hjt'
    rw [e1, e2] at hb
    have := (hc.before_iff .std hne hj hj' half half (Or.inr (by norm_num [half])) (Or.inr (by norm_num [half]))).1 hb
    rcases this with h | ⟨-, h⟩
    · exact h
    · exact absurd h (lt_irrefl _)
  · intro htt
    obtain ⟨s, hs, es⟩ := hx'
    obtain ⟨s', hs', es'⟩ := hy'
    refine ⟨mkVisit hV hne _ s hs, mkVisit hV hne _ s' hs', rfl, rfl, ?_⟩
    rw [hB.visitPt_xcol hV hne i hi (mkVisit hV hne _ s hs) rfl, hB.visitPt_xcol hV hne i' hi' (mkVisit hV hne _ s' hs') rfl,
      mkVisit_strand, mkVisit_strand, es, es']
    exact (hc.before_iff .std hne ht ht' half half (Or.inr (by norm_num [half])) (Or.inr (by norm_num [half]))).2
      (Or.inl htt)

/-! the identification of the `σ` slots of the block crossings with chain slots -/

omit hB in
theorem σSlotA_val {k' b : ℕ} (hk : k' < V.length) (hℓ : letterAt V k' = .σ b) :
    (σSlotA hV hk hℓ).1 = if bit V k' b then (k', b) else (k' + 1, b + 1) := by
  unfold σSlotA; split_ifs <;> rfl

omit hB in
theorem σSlotB_val {k' b : ℕ} (hk : k' < V.length) (hℓ : letterAt V k' = .σ b) :
    (σSlotB hV hk hℓ).1 = if bit V k' (b + 1) then (k', b + 1) else (k' + 1, b) := by
  unfold σSlotB; split_ifs <;> rfl

/-- the descending strand of column `k+i` is the strand `j` at position `a i` there -/
theorem σSlotA_eq_chain (j : ℕ) (hj : j < 3) (i : ℕ) (hi : i < 3) (h : pos a (m + j) i = a i) :
    σSlotA hV (hB.hk_i i hi) (hB.letter i hi) =
      (hB.chain hV j hj).slot hV (if bit V k (m + j) then i else 2 - i) := by
  apply Subtype.ext
  rw [σSlotA_val hV]
  have hb := hB.bit_pos hV (p := m + j) ⟨by omega, by omega⟩ i (by omega)
  rw [h] at hb
  have hsucc : pos a (m + j) (i + 1) = a i + 1 := by rw [pos_succ, h]; unfold swp; simp
  cases hbj : bit V k (m + j)
  · rw [hbj] at hb
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [hB.chain_slot hV j hj (2 - i) (by omega), hbj]
    simp only [cidx, Bool.false_eq_true, ↓reduceIte]
    rw [show 3 - (2 - i) = i + 1 by omega, hsucc]
    rfl
  · rw [hbj] at hb
    simp only [hb, ↓reduceIte]
    rw [hB.chain_slot hV j hj i (by omega), hbj]
    simp only [cidx, ↓reduceIte, h]

/-- the ascending strand of column `k+i` is the strand `j` at position `a i + 1` there -/
theorem σSlotB_eq_chain (j : ℕ) (hj : j < 3) (i : ℕ) (hi : i < 3) (h : pos a (m + j) i = a i + 1) :
    σSlotB hV (hB.hk_i i hi) (hB.letter i hi) =
      (hB.chain hV j hj).slot hV (if bit V k (m + j) then i else 2 - i) := by
  apply Subtype.ext
  rw [σSlotB_val hV]
  have hb := hB.bit_pos hV (p := m + j) ⟨by omega, by omega⟩ i (by omega)
  rw [h] at hb
  have hsucc : pos a (m + j) (i + 1) = a i := by
    rw [pos_succ, h]; unfold swp; simp
  cases hbj : bit V k (m + j)
  · rw [hbj] at hb
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [hB.chain_slot hV j hj (2 - i) (by omega), hbj]
    simp only [cidx, Bool.false_eq_true, ↓reduceIte]
    rw [show 3 - (2 - i) = i + 1 by omega, hsucc]
    rfl
  · rw [hbj] at hb
    simp only [hb, ↓reduceIte]
    rw [hB.chain_slot hV j hj i (by omega), hbj]
    simp only [cidx, ↓reduceIte, h]

/-- the hypotheses of `beforeOn_xcol_iff` for a crossing whose two strands lie on the chains `j ≠ j'` -/
theorem xcol_slots (hne : V ≠ []) (i : ℕ) (hi : i < 3) {j : ℕ} (hj : j < 3) {t : ℕ} {j' : ℕ}
    (hj' : j' < 3) {t'' : ℕ} (ht'' : t'' ≤ 3) (hjj : j ≠ j')
    (h : (σSlotA hV (hB.hk_i i hi) (hB.letter i hi) = (hB.chain hV j hj).slot hV t ∧
          σSlotB hV (hB.hk_i i hi) (hB.letter i hi) = (hB.chain hV j' hj').slot hV t'') ∨
         (σSlotB hV (hB.hk_i i hi) (hB.letter i hi) = (hB.chain hV j hj).slot hV t ∧
          σSlotA hV (hB.hk_i i hi) (hB.letter i hi) = (hB.chain hV j' hj').slot hV t'')) :
    (∀ s, s ∈ (hB.xcol hV hne i hi).val →
      slotOf .std hV hne s = (hB.chain hV j hj).slot hV t ∨
        ∀ jj, jj < (hB.chain hV j hj).n → slotOf .std hV hne s ≠ (hB.chain hV j hj).slot hV jj) ∧
    (∃ s, ∃ _ : s ∈ (hB.xcol hV hne i hi).val, slotOf .std hV hne s = (hB.chain hV j hj).slot hV t) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases hB.slot_mem_xcol hV hne i hi hs with hsA | hsB
    · rcases h with ⟨hA, -⟩ | ⟨-, hA⟩
      · left; rw [hsA, hA]
      · right; intro jj hjjn; rw [hB.chain_n] at hjjn; rw [hsA, hA]
        exact hB.chain_slot_ne hV hj' hj hjj.symm ht'' (by omega)
    · rcases h with ⟨-, hBs⟩ | ⟨hBs, -⟩
      · right; intro jj hjjn; rw [hB.chain_n] at hjjn; rw [hsB, hBs]
        exact hB.chain_slot_ne hV hj' hj hjj.symm ht'' (by omega)
      · left; rw [hsB, hBs]
  · rcases h with ⟨hA, -⟩ | ⟨hBs, -⟩
    · exact ⟨_, hB.strandA_mem_xcol hV hne i hi, by rw [slotOf_strandOfSlot, hA]⟩
    · exact ⟨_, hB.strandB_mem_xcol hV hne i hi, by rw [slotOf_strandOfSlot, hBs]⟩

end Blk

end OneWord

/-! #### I. Two words agreeing outside the block -/

/-- the vertices outside the open band -/
def Out (V : Word) (k m : ℕ) (u : Slot V) : Prop := pt₀ V u ∉ interior (band k m)

theorem Blk.out_iff {V : Word} {k m : ℕ} {a : ℕ → ℕ} (hB : Blk V k m a) (u : Slot V) :
    Out V k m u ↔ ¬ ((u.1.1 = k + 1 ∨ u.1.1 = k + 2) ∧ m ≤ u.1.2 ∧ u.1.2 ≤ m + 2) := by
  unfold Out; rw [hB.pt_mem_interior_iff]

theorem nextPair_fst_of_false {V : Word} {k' p : ℕ} (hp : p ≠ 0) (hb : bit V k' p = false) :
    (nextPair V (k', p)).1 = k' - 1 := by
  cases h : (letterAt V (k' - 1)).posL p
  · rw [nextPair_left_none V hp hb h]
  · rw [nextPair_left V hp hb h]

section TwoWords

variable {V V' : Word} (hV : V.Closed) (hV' : V'.Closed) {k m : ℕ} {a a' : ℕ → ℕ}

/-- The pair hypothesis: both words carry a block at `k` (`Blk`), have the same length, agree in letters and cuts
outside the block, and their blocks permute the three active positions in the same way. -/
structure Pair (V V' : Word) (k m : ℕ) (a a' : ℕ → ℕ) : Prop where
  blk : Blk V k m a
  blk' : Blk V' k m a'
  len : V.length = V'.length
  letter_ext : ∀ k', k' < k ∨ k + 3 ≤ k' → letterAt V k' = letterAt V' k'
  cut_ext : ∀ k', k' ≤ k ∨ k + 3 ≤ k' → cut V k' = cut V' k'
  pos3 : ∀ p, m ≤ p ∧ p ≤ m + 2 → pos a p 3 = pos a' p 3

namespace Pair

variable (hP : Pair V V' k m a a')
include hV hV' hP

omit hV hV' in
theorem symm : Pair V' V k m a' a :=
  ⟨hP.blk', hP.blk, hP.len.symm, fun k' h => (hP.letter_ext k' h).symm, fun k' h => (hP.cut_ext k' h).symm,
    fun p hp => (hP.pos3 p hp).symm⟩

theorem cutLen_eq (k' : ℕ) : (cut V k').length = (cut V' k').length := by
  by_cases h : k' ≤ k ∨ k + 3 ≤ k'
  · rw [hP.cut_ext k' h]
  · push Not at h
    obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ 3 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
    rw [hP.blk.cutLen hV i hi, hP.blk'.cutLen hV' i hi, hP.cut_ext k (Or.inl le_rfl)]

omit hV hV' in
theorem isCrossing_eq (k' : ℕ) : (letterAt V k').isCrossing = (letterAt V' k').isCrossing := by
  by_cases h : k' < k ∨ k + 3 ≤ k'
  · rw [hP.letter_ext k' h]
  · push Not at h
    rw [hP.blk.isCrossing_blk k' h.1 h.2, hP.blk'.isCrossing_blk k' h.1 h.2]

theorem isSlot_iff (s : ℕ × ℕ) : IsSlot V s ↔ IsSlot V' s :=
  isSlot_congr V V' s.1 s.2 hP.len (hP.cutLen_eq hV hV' s.1) (hP.isCrossing_eq s.1)

/-- the slot bijection: the identity on pairs -/
def ψ : Slot V ≃ Slot V' := sameSlotEquiv V V' (hP.isSlot_iff hV hV')

@[simp] theorem ψ_val (u : Slot V) : (hP.ψ hV hV' u).1 = u.1 := rfl
@[simp] theorem ψ_symm_val (u : Slot V') : ((hP.ψ hV hV').symm u).1 = u.1 := rfl

theorem ψ_symm : (hP.ψ hV hV').symm = hP.symm.ψ hV' hV := Equiv.ext fun _ => Subtype.ext rfl

omit hV hV' in
/-- the vertices agree (no cusp slot in the block) -/
theorem pt_eq (s : ℕ × ℕ) (hs : IsSlot V s) : pt .std V s = pt .std V' s := by
  obtain ⟨k', p⟩ := s
  apply pt_congr V V' .std k' p
  intro hp0
  subst hp0
  rw [hP.letter_ext k' (hP.blk.cusp_letter_ext hs)]

theorem pt₀_ψ (u : Slot V) : pt₀ V' (hP.ψ hV hV' u) = pt₀ V u := (hP.pt_eq u.1 u.2).symm

theorem out_ψ (u : Slot V) : Out V' k m (hP.ψ hV hV' u) ↔ Out V k m u := by
  unfold Out; rw [hP.pt₀_ψ hV hV' u]

omit hV hV' in
theorem bit_agree_ext (k' : ℕ) (h : k' ≤ k ∨ k + 3 ≤ k') (q : ℕ) : bit V k' q = bit V' k' q := by
  rw [FrontRealize.bit_eq, FrontRealize.bit_eq, hP.cut_ext k' h]

/-- bits agree except at the six interior active slots -/
theorem bit_agree {k' p : ℕ} (hp0 : p ≠ 0) (h : ¬ ((k' = k + 1 ∨ k' = k + 2) ∧ m ≤ p ∧ p ≤ m + 2)) :
    bit V k' p = bit V' k' p := by
  by_cases hext : k' ≤ k ∨ k + 3 ≤ k'
  · exact hP.bit_agree_ext k' hext p
  · push Not at hext
    have hpm : ¬ (m ≤ p ∧ p ≤ m + 2) := fun hpm => h ⟨by omega, hpm⟩
    obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ 3 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
    rw [hP.blk.bit_spec hV i hi hp0 hpm, hP.blk'.bit_spec hV' i hi hp0 hpm]
    exact hP.bit_agree_ext k (Or.inl le_rfl) p

omit hV hV' in
theorem posR_agree {k' p : ℕ} (h : (k' < k ∨ k + 3 ≤ k') ∨ ¬ (m ≤ p ∧ p ≤ m + 2)) :
    (letterAt V k').posR p = (letterAt V' k').posR p := by
  by_cases hext : k' < k ∨ k + 3 ≤ k'
  · rw [hP.letter_ext k' hext]
  · push Not at hext
    have hpm : ¬ (m ≤ p ∧ p ≤ m + 2) := h.resolve_left (by omega)
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < 3 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
    rw [hP.blk.letter i hi, hP.blk'.letter i hi, posR_σ_eq, posR_σ_eq, swp_of_not (hP.blk.idx i hi) hpm,
      swp_of_not (hP.blk'.idx i hi) hpm]

omit hV hV' in
theorem posL_agree {k' p : ℕ} (h : (k' < k ∨ k + 3 ≤ k') ∨ ¬ (m ≤ p ∧ p ≤ m + 2)) :
    (letterAt V k').posL p = (letterAt V' k').posL p := by
  by_cases hext : k' < k ∨ k + 3 ≤ k'
  · rw [hP.letter_ext k' hext]
  · push Not at hext
    have hpm : ¬ (m ≤ p ∧ p ≤ m + 2) := h.resolve_left (by omega)
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < 3 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
    rw [hP.blk.letter i hi, hP.blk'.letter i hi, posL_σ_eq, posL_σ_eq, swp_of_not (hP.blk.idx i hi) hpm,
      swp_of_not (hP.blk'.idx i hi) hpm]

/-- **the successors agree** at a vertex outside the open band whose successor is also outside -/
theorem nextPair_agree (u : Slot V) (hu : Out V k m u) (hnu : Out V k m (next hV u)) :
    nextPair V u.1 = nextPair V' u.1 := by
  obtain ⟨⟨k', p⟩, hs⟩ := u
  rw [hP.blk.out_iff] at hu hnu
  simp only at hu
  apply nextPair_congr V V' k' p
  · intro hp0; subst hp0
    exact hP.letter_ext k' (hP.blk.cusp_letter_ext hs)
  · intro hp0; subst hp0
    exact hP.bit_agree_ext k' (by have := hP.blk.cusp_letter_ext hs; omega)
  · intro hp0; exact hP.bit_agree hV hV' hp0 hu
  · intro hp0 hb
    apply hP.posR_agree
    by_contra hc
    push Not at hc
    have hk' : k = k' := by omega
    subst hk'
    obtain ⟨hn, -⟩ := step_right hV (u := ⟨(k, p), hs⟩) rfl hp0 hb (hP.blk.letter 0 (by norm_num))
    rw [hn] at hnu
    exact hnu ⟨Or.inl rfl, swp_mem (hP.blk.idx 0 (by norm_num)) hc.2⟩
  · intro hp0 hb
    apply hP.posL_agree
    by_contra hc
    push Not at hc
    obtain ⟨-, -, hk0, -⟩ := cutSlot_facts' hV (u := ⟨(k', p), hs⟩) rfl hp0
    have hk' : k' = k + 3 := by omega
    subst hk'
    obtain ⟨hn, -⟩ := step_left hV (u := ⟨(k + 3, p), hs⟩) (k' := k + 2) rfl hp0 hb (hP.blk.letter 2 (by norm_num))
    rw [hn] at hnu
    exact hnu ⟨Or.inr rfl, swp_mem (hP.blk.idx 2 (by norm_num)) hc.2⟩

theorem ψ_next (u : Slot V) (hu : Out V k m u) (hnu : Out V k m (next hV u)) :
    hP.ψ hV hV' (next hV u) = next hV' (hP.ψ hV hV' u) :=
  sameSlotEquiv_next V V' hV hV' _ u (hP.nextPair_agree hV hV' u hu hnu)

omit hV' in
/-- a vertex outside the open band whose successor is inside is an entry: `(k, p)` rightward or `(k+3, q)`
leftward, at an active position -/
theorem entry_of (u : Slot V) (hu : Out V k m u) (hnu : ¬ Out V k m (next hV u)) :
    (∃ p, u.1 = (k, p) ∧ (m ≤ p ∧ p ≤ m + 2) ∧ bit V k p = true) ∨
    (∃ q, u.1 = (k + 3, q) ∧ (m ≤ q ∧ q ≤ m + 2) ∧ bit V (k + 3) q = false) := by
  obtain ⟨⟨k', p⟩, hs⟩ := u
  rw [hP.blk.out_iff] at hu hnu
  push Not at hnu
  simp only at hu
  have hm := hP.blk.hm
  by_cases hp0 : p = 0
  · exfalso
    subst hp0
    have hc := hP.blk.cusp_letter_ext hs
    rcases letterAt_of_cusp (s := ⟨(k', 0), hs⟩) rfl with ⟨m', d, hℓ⟩ | ⟨m', hℓ⟩
    · have e := nextPair_cusp_l V hℓ
      rw [next_val, e] at hnu
      simp only at hnu
      omega
    · have e := nextPair_cusp_r V hℓ
      rw [next_val, e] at hnu
      simp only at hnu
      omega
  · cases hb : bit V k' p
    · right
      cases hq : (letterAt V (k' - 1)).posL p
      · rw [next_val, nextPair_left_none V hp0 hb hq] at hnu
        simp only at hnu
        omega
      · rename_i q
        rw [next_val, nextPair_left V hp0 hb hq] at hnu
        simp only at hnu
        obtain ⟨-, -, hk0, -⟩ := cutSlot_facts' hV (u := ⟨(k', p), hs⟩) rfl hp0
        have hk' : k' = k + 3 := by
          by_contra hne
          have hk1 : k' - 1 = k + 1 := by omega
          have hpm : ¬ (m ≤ p ∧ p ≤ m + 2) := fun hpm => hu ⟨Or.inr (by omega), hpm⟩
          rw [hk1, hP.blk.letter 1 (by norm_num), posL_σ_eq, swp_of_not (hP.blk.idx 1 (by norm_num)) hpm] at hq
          have := Option.some.inj hq
          omega
        subst hk'
        refine ⟨p, rfl, ?_, hb⟩
        rw [show k + 3 - 1 = k + 2 by omega, hP.blk.letter 2 (by norm_num), posL_σ_eq] at hq
        have hq' := Option.some.inj hq
        subst hq'
        by_contra hpm
        rw [swp_of_not (hP.blk.idx 2 (by norm_num)) hpm] at hnu
        exact hpm hnu.2
    · left
      cases hq : (letterAt V k').posR p
      · rw [next_val, nextPair_right_none V hp0 hb hq] at hnu
        simp only at hnu
        omega
      · rename_i q
        rw [next_val, nextPair_right V hp0 hb hq] at hnu
        simp only at hnu
        have hk' : k' = k := by
          by_contra hne
          have hk1 : k' = k + 1 := by omega
          have hpm : ¬ (m ≤ p ∧ p ≤ m + 2) := fun hpm => hu ⟨Or.inl hk1, hpm⟩
          rw [hk1, hP.blk.letter 1 (by norm_num), posR_σ_eq, swp_of_not (hP.blk.idx 1 (by norm_num)) hpm] at hq
          have := Option.some.inj hq
          omega
        refine ⟨p, by show (k', p) = (k, p); rw [hk'], ?_, by rw [← hk']; exact hb⟩
        rw [hk', show k = k + 0 by rfl, hP.blk.letter 0 (by norm_num), posR_σ_eq] at hq
        have hq' := Option.some.inj hq
        subst hq'
        by_contra hpm
        rw [swp_of_not (hP.blk.idx 0 (by norm_num)) hpm] at hnu
        exact hpm hnu.2

omit hV' in
/-- the passage through the block starting at a rightward entry: the three following vertices, the last one outside -/
theorem passage_right {u : Slot V} {p : ℕ} (hu : u.1 = (k, p)) (hp : m ≤ p ∧ p ≤ m + 2) (hb : bit V k p = true) :
    ¬ Out V k m (next hV u) ∧ ¬ Out V k m (next hV (next hV u)) ∧ Out V k m (next hV (next hV (next hV u))) ∧
      (next hV (next hV (next hV u))).1 = (k + 3, pos a p 3) := by
  have h1 := hP.blk.iterate_right hV hp hb u hu 1 (by norm_num)
  have h2 := hP.blk.iterate_right hV hp hb u hu 2 (by norm_num)
  have h3 := hP.blk.iterate_right hV hp hb u hu 3 le_rfl
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at h1 h2 h3
  refine ⟨?_, ?_, ?_, h3⟩
  · rw [hP.blk.out_iff, h1]; push Not
    exact ⟨Or.inl rfl, hP.blk.pos_mem hp 1 (by norm_num)⟩
  · rw [hP.blk.out_iff, h2]; push Not
    exact ⟨Or.inr rfl, hP.blk.pos_mem hp 2 (by norm_num)⟩
  · rw [hP.blk.out_iff, h3]; simp

omit hV' in
/-- the passage through the block starting at a leftward entry -/
theorem passage_left {u : Slot V} {p : ℕ} (hu : u.1 = (k + 3, pos a p 3)) (hp : m ≤ p ∧ p ≤ m + 2)
    (hb : bit V k p = false) :
    ¬ Out V k m (next hV u) ∧ ¬ Out V k m (next hV (next hV u)) ∧ Out V k m (next hV (next hV (next hV u))) ∧
      (next hV (next hV (next hV u))).1 = (k, p) := by
  have h1 := hP.blk.iterate_left hV hp hb u hu 1 (by norm_num)
  have h2 := hP.blk.iterate_left hV hp hb u hu 2 (by norm_num)
  have h3 := hP.blk.iterate_left hV hp hb u hu 3 le_rfl
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at h1 h2 h3
  simp only [Nat.sub_self, Nat.add_zero, pos_zero] at h3
  refine ⟨?_, ?_, ?_, h3⟩
  · rw [hP.blk.out_iff, h1]; push Not
    exact ⟨Or.inr rfl, hP.blk.pos_mem hp 2 (by norm_num)⟩
  · rw [hP.blk.out_iff, h2]; push Not
    exact ⟨Or.inl rfl, hP.blk.pos_mem hp 1 (by norm_num)⟩
  · rw [hP.blk.out_iff, h3]; simp

open Classical in
/-- the induced bijection of the vertices outside the open band -/
noncomputable def φ : {u : Slot V // Out V k m u} ≃ {u' : Slot V' // Out V' k m u'} :=
  (hP.ψ hV hV').subtypeEquiv (fun u => (hP.out_ψ hV hV' u).symm)

theorem φ_val (u : {u : Slot V // Out V k m u}) : (hP.φ hV hV' u).1 = hP.ψ hV hV' u.1 := rfl

open Classical in
/-- **conjugate first returns**: the first return to the outside vertices is carried by the slot bijection (a step
outside is literally the same; an entry is followed by the same three-step passage in both words) -/
theorem conj_firstReturn (u : {u : Slot V // Out V k m u}) :
    firstReturn (nextPerm hV') (Out V' k m) (hP.φ hV hV' u) = hP.φ hV hV' (firstReturn (nextPerm hV) (Out V k m) u) := by
  apply Subtype.ext
  rw [φ_val]
  by_cases hn : Out V k m (next hV u.1)
  · rw [firstReturn_apply_of_mem (nextPerm hV') (Out V' k m) _ (by
      show Out V' k m (next hV' (hP.ψ hV hV' u.1))
      rw [← hP.ψ_next hV hV' u.1 u.2 hn, hP.out_ψ]; exact hn)]
    rw [firstReturn_apply_of_mem (nextPerm hV) (Out V k m) u hn]
    show next hV' (hP.ψ hV hV' u.1) = hP.ψ hV hV' (next hV u.1)
    exact (hP.ψ_next hV hV' u.1 u.2 hn).symm
  · rcases hP.entry_of hV u.1 u.2 hn with ⟨p, hu, hp, hb⟩ | ⟨q, hu, hq, hb⟩
    · -- rightward entry
      obtain ⟨n1, n2, n3, e3⟩ := hP.passage_right hV hu hp hb
      have hb' : bit V' k p = true := by rw [← hP.bit_agree_ext k (Or.inl le_rfl) p]; exact hb
      have hu' : (hP.ψ hV hV' u.1).1 = (k, p) := by rw [ψ_val, hu]
      obtain ⟨n1', n2', n3', e3'⟩ := hP.symm.passage_right hV' hu' hp hb'
      rw [firstReturn_apply_of_not_mem₂ (nextPerm hV) (Out V k m) u n1 n2 n3,
        firstReturn_apply_of_not_mem₂ (nextPerm hV') (Out V' k m) (hP.φ hV hV' u) n1' n2' n3']
      apply Subtype.ext
      show (next hV' (next hV' (next hV' (hP.ψ hV hV' u.1)))).1 = (next hV (next hV (next hV u.1))).1
      rw [e3', e3, hP.pos3 p hp]
    · -- leftward entry: `q = pos a p 3` for the strand entering at `p`
      obtain ⟨j, hj, hpq⟩ := pos_surj 3 (fun j hj => hP.blk.pos_mem ⟨by omega, by omega⟩ 3 le_rfl) hq
      have hp : m ≤ m + j ∧ m + j ≤ m + 2 := ⟨by omega, by omega⟩
      have hbp : bit V k (m + j) = false := by
        rw [← hP.blk.bit_pos hV hp 3 le_rfl, hpq]; exact hb
      rw [← hpq] at hu
      obtain ⟨n1, n2, n3, e3⟩ := hP.passage_left hV hu hp hbp
      have hu' : (hP.ψ hV hV' u.1).1 = (k + 3, pos a' (m + j) 3) := by rw [ψ_val, hu, hP.pos3 _ hp]
      have hbp' : bit V' k (m + j) = false := by rw [← hP.bit_agree_ext k (Or.inl le_rfl)]; exact hbp
      obtain ⟨n1', n2', n3', e3'⟩ := hP.symm.passage_left hV' hu' hp hbp'
      rw [firstReturn_apply_of_not_mem₂ (nextPerm hV) (Out V k m) u n1 n2 n3,
        firstReturn_apply_of_not_mem₂ (nextPerm hV') (Out V' k m) (hP.φ hV hV' u) n1' n2' n3']
      apply Subtype.ext
      show (next hV' (next hV' (next hV' (hP.ψ hV hV' u.1)))).1 = (next hV (next hV (next hV u.1))).1
      rw [e3', e3]

omit hV' in
theorem exists_out' (u : Slot V) : ∃ n : ℕ, Out V k m (((nextPerm hV) ^ n) u) := hP.blk.exists_out hV u

open Classical in
/-- the components correspond (conjugate first returns to the outside vertices) -/
noncomputable def orbitEquiv : Orbit hV ≃ Orbit hV' :=
  U2.cycleEquiv (nextPerm hV) (nextPerm hV') (Out V k m) (Out V' k m) (hP.φ hV hV') (hP.conj_firstReturn hV hV')
    (hP.exists_out' hV) (hP.symm.exists_out' hV')

open Classical in
theorem orbitEquiv_orbitOf (u : Slot V) (hu : Out V k m u) :
    hP.orbitEquiv hV hV' (orbitOf hV u) = orbitOf hV' (hP.ψ hV hV' u) :=
  U2.cycleEquiv_mk (nextPerm hV) (nextPerm hV') (Out V k m) (Out V' k m) (hP.φ hV hV') (hP.conj_firstReturn hV hV')
    (hP.exists_out' hV) (hP.symm.exists_out' hV') ⟨u, hu⟩

/-- the component bijection -/
noncomputable def e : Fin (numComp hV) ≃ Fin (numComp hV') :=
  (Fintype.equivFin (Orbit hV)).symm.trans ((hP.orbitEquiv hV hV').trans (Fintype.equivFin (Orbit hV')))

theorem he (u : Slot V) (hu : pt₀ V u ∉ interior (band k m)) :
    U2.slotComp hV' (hP.ψ hV hV' u) = hP.e hV hV' (U2.slotComp hV u) := by
  rw [U2.slotComp_eq_equivFin, U2.slotComp_eq_equivFin]
  simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [hP.orbitEquiv_orbitOf hV hV' u hu]

/-- **the match data** of the two realizations relative to the band -/
theorem matchData : MatchData (bandL k m) hV hV' (pt₀ V) (pt₀ V') (hP.ψ hV hV') where
  cl := hP.blk.classify' hV
  cl' := hP.blk'.classify' hV'
  out_iff u := by
    by_cases hnp : nextPair V u.1 = nextPair V' u.1
    · unfold PieceOut
      have e1 : pt₀ V' (hP.ψ hV hV' u) = pt₀ V u := hP.pt₀_ψ hV hV' u
      have e2 : pt₀ V' (next hV' (hP.ψ hV hV' u)) = pt₀ V (next hV u) := by
        show pt .std V' (next hV' (hP.ψ hV hV' u)).1 = pt .std V (next hV u).1
        rw [next_val, next_val, ψ_val, ← hnp]
        exact (hP.pt_eq (nextPair V u.1) (isSlot_nextPair hV u.2)).symm
      rw [e1, e2]
    · have hnot : ¬ PieceOut (bandL k m) hV (pt₀ V) u := fun ho =>
        hnp (hP.nextPair_agree hV hV' u ho.left_notMem_interior ho.right_notMem_interior)
      have hnot' : ¬ PieceOut (bandL k m) hV' (pt₀ V') (hP.ψ hV hV' u) := fun ho => hnp (by
        have := hP.symm.nextPair_agree hV' hV (hP.ψ hV hV' u) ho.left_notMem_interior ho.right_notMem_interior
        rw [ψ_val] at this
        exact this.symm)
      exact iff_of_false hnot hnot'
  pt_eq u _ := hP.pt₀_ψ hV hV' u
  int_iff u := by rw [hP.pt₀_ψ hV hV' u]
  next_eq u ho := hP.ψ_next hV hV' u ho.left_notMem_interior ho.right_notMem_interior

/-- the `σ` slots of a column whose pieces are outside are exterior columns, and correspond literally -/
theorem sigmaCorr : SigmaCorr (bandL k m) hV hV' (pt₀ V) (hP.ψ hV hV') (fun _ => True) (fun _ => True) := by
  intro k' m' hk hℓ _ hout
  have hext : k' < k ∨ k + 3 ≤ k' := by
    by_contra hc
    push Not at hc
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < 3 ∧ k' = k + i := ⟨k' - k, by omega, by omega⟩
    have hm' : m' = a i := Letter.σ.inj (hℓ.symm.trans (hP.blk.letter i hi))
    subst hm'
    obtain ⟨j, hj, hpos⟩ := pos_surj i (fun j hj => hP.blk.pos_mem ⟨by omega, by omega⟩ i (by omega))
      (p := a i) (by have := hP.blk.idx i hi; omega)
    have hA := hP.blk.σSlotA_eq_chain hV j hj i hi hpos
    have hin := (hP.blk.chain_isChain hV j hj).pieceIn (if bit V k (m + j) then i else 2 - i)
      (by rw [hP.blk.chain_n]; split_ifs <;> omega)
    rw [← hA] at hin
    exact not_pieceIn_of_pieceOut (bandL k m) hV (pt₀ V) hout hin
  refine ⟨k', m', by rw [← hP.len]; exact hk, by rw [← hP.letter_ext k' hext]; exact hℓ, trivial, ?_, ?_⟩
  · apply Subtype.ext
    rw [ψ_val, Blk.σSlotA_val hV, Blk.σSlotA_val hV', hP.bit_agree_ext k' (by omega) m']
  · apply Subtype.ext
    rw [ψ_val, Blk.σSlotB_val hV, Blk.σSlotB_val hV', hP.bit_agree_ext k' (by omega) (m' + 1)]

theorem sigmaCorr' : SigmaCorr (bandL k m) hV' hV (pt₀ V') (hP.ψ hV hV').symm (fun _ => True) (fun _ => True) := by
  rw [hP.ψ_symm]; exact hP.symm.sigmaCorr hV' hV

end Pair

end TwoWords

/-! #### J. The site -/

theorem pos_one (a : ℕ → ℕ) (p : ℕ) : pos a p 1 = swp (a 0) p := rfl
theorem pos_two (a : ℕ → ℕ) (p : ℕ) : pos a p 2 = swp (a 1) (swp (a 0) p) := rfl
theorem pos_three (a : ℕ → ℕ) (p : ℕ) : pos a p 3 = swp (a 2) (swp (a 1) (swp (a 0) p)) := rfl

/-- the chain index of column `i` on the strand `j` -/
def tj (V : Word) (k m j i : ℕ) : ℕ := if bit V k (m + j) then i else 2 - i

theorem tj_lt (V : Word) (k m j : ℕ) {i : ℕ} (hi : i < 3) : tj V k m j i < 3 := by unfold tj; split_ifs <;> omega

section Site

variable {V : Word} (hV : V.Closed) {k m : ℕ} {a : ℕ → ℕ}

namespace Blk

variable (hB : Blk V k m a)
include hV hB

theorem chain_u₀_ne {j j' : ℕ} (hj : j < 3) (hj' : j' < 3) (hjj : j ≠ j') :
    (hB.chain hV j hj).u₀ ≠ (hB.chain hV j' hj').u₀ :=
  hB.chain_slot_ne hV hj hj' hjj (t := 0) (t' := 0) (by omega) (by omega)

/-- the over strand of the crossing of column `k+i` is the strand `j` at position `a i` -/
theorem over_chain (hne : V ≠ []) (i : ℕ) (hi : i < 3) (j : ℕ) (hj : j < 3) (h : pos a (m + j) i = a i) :
    (realizeAt .std hV hne).diagram.OverOn ((hB.chain hV j hj).toArc .std hV hne (pt₀ V)) (hB.xcol hV hne i hi) :=
  hB.overOn_xcol hV hne i hi _ (hB.chain_isChain hV j hj) (t := tj V k m j i)
    (by rw [hB.chain_n]; exact tj_lt V k m j hi) (hB.σSlotA_eq_chain hV j hj i hi h)

/-- the under strand of the crossing of column `k+i` is the strand `j` at position `a i + 1` -/
theorem under_chain (hne : V ≠ []) (i : ℕ) (hi : i < 3) (j : ℕ) (hj : j < 3) (h : pos a (m + j) i = a i + 1) :
    (realizeAt .std hV hne).diagram.UnderOn ((hB.chain hV j hj).toArc .std hV hne (pt₀ V)) (hB.xcol hV hne i hi) :=
  hB.underOn_xcol hV hne i hi _ (hB.chain_isChain hV j hj) (t := tj V k m j i)
    (by rw [hB.chain_n]; exact tj_lt V k m j hi) (hB.σSlotB_eq_chain hV j hj i hi h)

/-- the order of two crossings along the strand `j`, from the chain indices of their columns -/
theorem before_chain_iff (hne : V ≠ []) {i i' : ℕ} (hi : i < 3) (hi' : i' < 3) (j : ℕ) (hj : j < 3)
    {j₁ : ℕ} (hj₁ : j₁ < 3) (hjj₁ : j ≠ j₁) {j₂ : ℕ} (hj₂ : j₂ < 3) (hjj₂ : j ≠ j₂)
    (h₁ : (pos a (m + j) i = a i ∧ pos a (m + j₁) i = a i + 1) ∨ (pos a (m + j) i = a i + 1 ∧ pos a (m + j₁) i = a i))
    (h₂ : (pos a (m + j) i' = a i' ∧ pos a (m + j₂) i' = a i' + 1) ∨
      (pos a (m + j) i' = a i' + 1 ∧ pos a (m + j₂) i' = a i')) :
    (realizeAt .std hV hne).diagram.BeforeOn ((hB.chain hV j hj).toArc .std hV hne (pt₀ V)) (hB.xcol hV hne i hi)
      (hB.xcol hV hne i' hi') ↔ tj V k m j i < tj V k m j i' := by
  have hx := hB.xcol_slots hV hne i hi hj (t := tj V k m j i) hj₁ (t'' := tj V k m j₁ i) (by have := tj_lt V k m j₁ hi; omega) hjj₁
    (h₁.imp (fun h => ⟨hB.σSlotA_eq_chain hV j hj i hi h.1, hB.σSlotB_eq_chain hV j₁ hj₁ i hi h.2⟩)
      (fun h => ⟨hB.σSlotB_eq_chain hV j hj i hi h.1, hB.σSlotA_eq_chain hV j₁ hj₁ i hi h.2⟩))
  have hy := hB.xcol_slots hV hne i' hi' hj (t := tj V k m j i') hj₂ (t'' := tj V k m j₂ i') (by have := tj_lt V k m j₂ hi'; omega) hjj₂
    (h₂.imp (fun h => ⟨hB.σSlotA_eq_chain hV j hj i' hi' h.1, hB.σSlotB_eq_chain hV j₂ hj₂ i' hi' h.2⟩)
      (fun h => ⟨hB.σSlotB_eq_chain hV j hj i' hi' h.1, hB.σSlotA_eq_chain hV j₂ hj₂ i' hi' h.2⟩))
  exact hB.beforeOn_xcol_iff hV hne hi hi' _ (hB.chain_isChain hV j hj) (by rw [hB.chain_n]; exact tj_lt V k m j hi)
    (by rw [hB.chain_n]; exact tj_lt V k m j hi') hx.1 hx.2 hy.1 hy.2

theorem xcol_three_iff (hne : V ≠ []) (y : (realizeAt .std hV hne).Γ.Crossing) {i₁ i₂ i₃ : ℕ} (h1 : i₁ < 3)
    (h2 : i₂ < 3) (h3 : i₃ < 3) (d12 : i₁ ≠ i₂) (d13 : i₁ ≠ i₃) (d23 : i₂ ≠ i₃) :
    (∃ i, ∃ hi : i < 3, y = hB.xcol hV hne i hi) ↔
      y = hB.xcol hV hne i₁ h1 ∨ y = hB.xcol hV hne i₂ h2 ∨ y = hB.xcol hV hne i₃ h3 := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases (by omega : i = i₁ ∨ i = i₂ ∨ i = i₃) with rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; rfl
  · rintro (rfl | rfl | rfl)
    · exact ⟨i₁, h1, rfl⟩
    · exact ⟨i₂, h2, rfl⟩
    · exact ⟨i₃, h3, rfl⟩

end Blk

end Site

section SiteTwo

variable {V V' : Word} (hV : V.Closed) (hV' : V'.Closed) {k m : ℕ} {a a' : ℕ → ℕ}

namespace Pair

variable (hP : Pair V V' k m a a')
include hV hV' hP

/-- the entry and exit slots of the strands agree as pairs -/
theorem chain_end_pair (j : ℕ) (hj : j < 3) (t : ℕ) (ht : t = 0 ∨ t = 3) :
    ((hP.blk'.chain hV' j hj).slot hV' t).1 = ((hP.blk.chain hV j hj).slot hV t).1 := by
  have hb : bit V' k (m + j) = bit V k (m + j) := (hP.bit_agree_ext k (Or.inl le_rfl) (m + j)).symm
  have h3 := hP.pos3 (m + j) ⟨by omega, by omega⟩
  rw [hP.blk'.chain_slot hV' j hj t (by omega), hP.blk.chain_slot hV j hj t (by omega), hb]
  rcases ht with rfl | rfl <;> cases hbv : bit V k (m + j) <;>
    simp only [Blk.cidx, Bool.false_eq_true, ↓reduceIte, Nat.sub_self, Nat.sub_zero, pos_zero, h3]

theorem chain_end_pt (j : ℕ) (hj : j < 3) (t : ℕ) (ht : t = 0 ∨ t = 3) :
    pt₀ V' ((hP.blk'.chain hV' j hj).slot hV' t) = pt₀ V ((hP.blk.chain hV j hj).slot hV t) := by
  show pt .std V' _ = pt .std V _
  rw [hP.chain_end_pair hV hV' j hj t ht]
  exact (hP.pt_eq ((hP.blk.chain hV j hj).slot hV t).1 ((hP.blk.chain hV j hj).slot hV t).2).symm

omit hV hV' in
theorem tj_eq (j i : ℕ) : tj V' k m j i = tj V k m j i := by
  unfold tj; rw [hP.bit_agree_ext k (Or.inl le_rfl) (m + j)]

/-- the move match -/
noncomputable def moveMatch (hne : V ≠ []) (hne' : V' ≠ []) :
    MoveMatch (band k m) (realizeAt .std hV hne).diagram (realizeAt .std hV' hne').diagram :=
  (hP.matchData hV hV').moveMatch .std hne hne' (generic .std hV hne) (realizeAt .std hV hne).overStrand
    (realizeAt .std hV hne).overStrand_mem (fun _ => True) (realizeAt_data' .std hV hne) (generic .std hV' hne')
    (realizeAt .std hV' hne').overStrand (realizeAt .std hV' hne').overStrand_mem (fun _ => True)
    (realizeAt_data' .std hV' hne') (hP.sigmaCorr hV hV') (hP.sigmaCorr' hV hV') (hP.e hV hV') (hP.he hV hV')

omit hV hV' hP in
theorem rev_aux {b : Bool} {i i' i₁' i₂' : ℕ} (hi : i < 3) (hi' : i' < 3) (hi₁ : i₁' < 3) (hi₂ : i₂' < 3)
    (h1 : i < i' ↔ i₂' < i₁') (h2 : i' < i ↔ i₁' < i₂') :
    ((if b then i else 2 - i) < (if b then i' else 2 - i')) ↔ ((if b then i₂' else 2 - i₂') < (if b then i₁' else 2 - i₁')) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- **The RIII site between two realizations agreeing outside a three-`σ` block with the same strand permutation**,
given the columns of the three crossings (`a` over `b` at column `iAB`, `a` over `c` at `iAC`, `b` over `c` at
`iBC`, and likewise primed for the second word) and the reversal of the visit orders. -/
theorem site_of (hne : V ≠ []) (hne' : V' ≠ []) (iAB iAC iBC iAB' iAC' iBC' : ℕ)
    (hAB3 : iAB < 3) (hAC3 : iAC < 3) (hBC3 : iBC < 3) (hAB3' : iAB' < 3) (hAC3' : iAC' < 3) (hBC3' : iBC' < 3)
    (hd1 : iAB ≠ iAC) (hd2 : iAB ≠ iBC) (hd3 : iAC ≠ iBC) (hd1' : iAB' ≠ iAC') (hd2' : iAB' ≠ iBC') (hd3' : iAC' ≠ iBC')
    (hAB : pos a (m + 0) iAB = a iAB ∧ pos a (m + 1) iAB = a iAB + 1)
    (hAC : pos a (m + 0) iAC = a iAC ∧ pos a (m + 2) iAC = a iAC + 1)
    (hBC : pos a (m + 1) iBC = a iBC ∧ pos a (m + 2) iBC = a iBC + 1)
    (hAB' : pos a' (m + 0) iAB' = a' iAB' ∧ pos a' (m + 1) iAB' = a' iAB' + 1)
    (hAC' : pos a' (m + 0) iAC' = a' iAC' ∧ pos a' (m + 2) iAC' = a' iAC' + 1)
    (hBC' : pos a' (m + 1) iBC' = a' iBC' ∧ pos a' (m + 2) iBC' = a' iBC' + 1)
    (hrevA : (iAB < iAC ↔ iAC' < iAB') ∧ (iAC < iAB ↔ iAB' < iAC'))
    (hrevB : (iAB < iBC ↔ iBC' < iAB') ∧ (iBC < iAB ↔ iAB' < iBC'))
    (hrevC : (iAC < iBC ↔ iBC' < iAC') ∧ (iBC < iAC ↔ iAC' < iBC')) :
    Nonempty (RIIIData (band k m) (realizeAt .std hV hne).diagram (realizeAt .std hV' hne').diagram) := by
  have hB := hP.blk
  have hB' := hP.blk'
  have h0 : (0 : ℕ) < 3 := by norm_num
  have h1 : (1 : ℕ) < 3 := by norm_num
  have h2 : (2 : ℕ) < 3 := by norm_num
  refine ⟨{
    frame := ⟨isDisc_band k m, hB.clean hV hne, hB'.clean hV' hne'⟩
    out := hP.moveMatch hV hV' hne hne'
    a := (hB.chain hV 0 h0).toArc .std hV hne (pt₀ V)
    b := (hB.chain hV 1 h1).toArc .std hV hne (pt₀ V)
    c := (hB.chain hV 2 h2).toArc .std hV hne (pt₀ V)
    a' := (hB'.chain hV' 0 h0).toArc .std hV' hne' (pt₀ V')
    b' := (hB'.chain hV' 1 h1).toArc .std hV' hne' (pt₀ V')
    c' := (hB'.chain hV' 2 h2).toArc .std hV' hne' (pt₀ V')
    ab := Chain.toArc_ne .std hV hne (pt₀ V) (hB.chain_u₀_ne hV h0 h1 (by norm_num))
    bc := Chain.toArc_ne .std hV hne (pt₀ V) (hB.chain_u₀_ne hV h1 h2 (by norm_num))
    ac := Chain.toArc_ne .std hV hne (pt₀ V) (hB.chain_u₀_ne hV h0 h2 (by norm_num))
    ab' := Chain.toArc_ne .std hV' hne' (pt₀ V') (hB'.chain_u₀_ne hV' h0 h1 (by norm_num))
    bc' := Chain.toArc_ne .std hV' hne' (pt₀ V') (hB'.chain_u₀_ne hV' h1 h2 (by norm_num))
    ac' := Chain.toArc_ne .std hV' hne' (pt₀ V') (hB'.chain_u₀_ne hV' h0 h2 (by norm_num))
    cover := by have h := hB.arcCover hV hne; rw [hB.arcsOf_chains hV hne] at h; exact h
    cover' := by have h := hB'.arcCover hV' hne'; rw [hB'.arcsOf_chains hV' hne'] at h; exact h
    a_start := by
      have e1 := Chain.eval_startPt .std hV' hne' (pt₀ V') (hB'.chain hV' 0 h0)
      have e2 := Chain.eval_startPt .std hV hne (pt₀ V) (hB.chain hV 0 h0)
      exact e1.trans ((hP.chain_end_pt hV hV' 0 h0 0 (Or.inl rfl)).trans e2.symm)
    a_stop := by
      have e1 := Chain.eval_stopPt .std hV' hne' (pt₀ V') (hB'.chain hV' 0 h0)
      have e2 := Chain.eval_stopPt .std hV hne (pt₀ V) (hB.chain hV 0 h0)
      rw [hB'.chain_n] at e1
      rw [hB.chain_n] at e2
      exact e1.trans ((hP.chain_end_pt hV hV' 0 h0 3 (Or.inr rfl)).trans e2.symm)
    b_start := by
      have e1 := Chain.eval_startPt .std hV' hne' (pt₀ V') (hB'.chain hV' 1 h1)
      have e2 := Chain.eval_startPt .std hV hne (pt₀ V) (hB.chain hV 1 h1)
      exact e1.trans ((hP.chain_end_pt hV hV' 1 h1 0 (Or.inl rfl)).trans e2.symm)
    b_stop := by
      have e1 := Chain.eval_stopPt .std hV' hne' (pt₀ V') (hB'.chain hV' 1 h1)
      have e2 := Chain.eval_stopPt .std hV hne (pt₀ V) (hB.chain hV 1 h1)
      rw [hB'.chain_n] at e1
      rw [hB.chain_n] at e2
      exact e1.trans ((hP.chain_end_pt hV hV' 1 h1 3 (Or.inr rfl)).trans e2.symm)
    c_start := by
      have e1 := Chain.eval_startPt .std hV' hne' (pt₀ V') (hB'.chain hV' 2 h2)
      have e2 := Chain.eval_startPt .std hV hne (pt₀ V) (hB.chain hV 2 h2)
      exact e1.trans ((hP.chain_end_pt hV hV' 2 h2 0 (Or.inl rfl)).trans e2.symm)
    c_stop := by
      have e1 := Chain.eval_stopPt .std hV' hne' (pt₀ V') (hB'.chain hV' 2 h2)
      have e2 := Chain.eval_stopPt .std hV hne (pt₀ V) (hB.chain hV 2 h2)
      rw [hB'.chain_n] at e1
      rw [hB.chain_n] at e2
      exact e1.trans ((hP.chain_end_pt hV hV' 2 h2 3 (Or.inr rfl)).trans e2.symm)
    xab := hB.xcol hV hne iAB hAB3
    xac := hB.xcol hV hne iAC hAC3
    xbc := hB.xcol hV hne iBC hBC3
    xab_ne_xac := hB.xcol_ne hV hne hAB3 hAC3 hd1
    xab_ne_xbc := hB.xcol_ne hV hne hAB3 hBC3 hd2
    xac_ne_xbc := hB.xcol_ne hV hne hAC3 hBC3 hd3
    inner_iff := fun y => (hB.crossingPoint_mem_interior_iff hV hne y).trans
      (hB.xcol_three_iff hV hne y hAB3 hAC3 hBC3 hd1 hd2 hd3)
    sep_ab := Or.inl ⟨hB.over_chain hV hne iAB hAB3 0 h0 hAB.1, hB.under_chain hV hne iAB hAB3 1 h1 hAB.2⟩
    sep_ac := Or.inl ⟨hB.over_chain hV hne iAC hAC3 0 h0 hAC.1, hB.under_chain hV hne iAC hAC3 2 h2 hAC.2⟩
    sep_bc := Or.inl ⟨hB.over_chain hV hne iBC hBC3 1 h1 hBC.1, hB.under_chain hV hne iBC hBC3 2 h2 hBC.2⟩
    xab' := hB'.xcol hV' hne' iAB' hAB3'
    xac' := hB'.xcol hV' hne' iAC' hAC3'
    xbc' := hB'.xcol hV' hne' iBC' hBC3'
    xab_ne_xac' := hB'.xcol_ne hV' hne' hAB3' hAC3' hd1'
    xab_ne_xbc' := hB'.xcol_ne hV' hne' hAB3' hBC3' hd2'
    xac_ne_xbc' := hB'.xcol_ne hV' hne' hAC3' hBC3' hd3'
    inner_iff' := fun y => (hB'.crossingPoint_mem_interior_iff hV' hne' y).trans
      (hB'.xcol_three_iff hV' hne' y hAB3' hAC3' hBC3' hd1' hd2' hd3')
    sep_ab' := Or.inl ⟨hB'.over_chain hV' hne' iAB' hAB3' 0 h0 hAB'.1, hB'.under_chain hV' hne' iAB' hAB3' 1 h1 hAB'.2⟩
    sep_ac' := Or.inl ⟨hB'.over_chain hV' hne' iAC' hAC3' 0 h0 hAC'.1, hB'.under_chain hV' hne' iAC' hAC3' 2 h2 hAC'.2⟩
    sep_bc' := Or.inl ⟨hB'.over_chain hV' hne' iBC' hBC3' 1 h1 hBC'.1, hB'.under_chain hV' hne' iBC' hBC3' 2 h2 hBC'.2⟩
    top_ab := hB.over_chain hV hne iAB hAB3 0 h0 hAB.1
    top_ac := hB.over_chain hV hne iAC hAC3 0 h0 hAC.1
    mid_bc := hB.over_chain hV hne iBC hBC3 1 h1 hBC.1
    top_ab' := hB'.over_chain hV' hne' iAB' hAB3' 0 h0 hAB'.1
    top_ac' := hB'.over_chain hV' hne' iAC' hAC3' 0 h0 hAC'.1
    mid_bc' := hB'.over_chain hV' hne' iBC' hBC3' 1 h1 hBC'.1
    rev_a := by
      rw [hB.before_chain_iff hV hne hAB3 hAC3 0 h0 h1 (by norm_num) h2 (by norm_num) (Or.inl hAB) (Or.inl hAC),
        hB'.before_chain_iff hV' hne' hAC3' hAB3' 0 h0 h2 (by norm_num) h1 (by norm_num) (Or.inl hAC') (Or.inl hAB'),
        hP.tj_eq, hP.tj_eq]
      exact rev_aux hAB3 hAC3 hAB3' hAC3' hrevA.1 hrevA.2
    rev_b := by
      rw [hB.before_chain_iff hV hne hAB3 hBC3 1 h1 h0 (by norm_num) h2 (by norm_num) (Or.inr ⟨hAB.2, hAB.1⟩) (Or.inl hBC),
        hB'.before_chain_iff hV' hne' hBC3' hAB3' 1 h1 h2 (by norm_num) h0 (by norm_num) (Or.inl hBC') (Or.inr ⟨hAB'.2, hAB'.1⟩),
        hP.tj_eq, hP.tj_eq]
      exact rev_aux hAB3 hBC3 hAB3' hBC3' hrevB.1 hrevB.2
    rev_c := by
      rw [hB.before_chain_iff hV hne hAC3 hBC3 2 h2 h0 (by norm_num) h1 (by norm_num) (Or.inr ⟨hAC.2, hAC.1⟩) (Or.inr ⟨hBC.2, hBC.1⟩),
        hB'.before_chain_iff hV' hne' hBC3' hAC3' 2 h2 h1 (by norm_num) h0 (by norm_num) (Or.inr ⟨hBC'.2, hBC'.1⟩) (Or.inr ⟨hAC'.2, hAC'.1⟩),
        hP.tj_eq, hP.tj_eq]
      exact rev_aux hAC3 hBC3 hAC3' hBC3' hrevC.1 hrevC.2 }⟩

end Pair

end SiteTwo

/-! #### K. The two type-III patterns -/

/-- the letter indices of `σ_{m+1} σ_m σ_{m+1}` -/
def a₁ (m : ℕ) : ℕ → ℕ := fun i => if i = 1 then m else m + 1
/-- the letter indices of `σ_m σ_{m+1} σ_m` -/
def a₂ (m : ℕ) : ℕ → ℕ := fun i => if i = 1 then m + 1 else m

@[simp] theorem a₁_zero (m : ℕ) : a₁ m 0 = m + 1 := rfl
@[simp] theorem a₁_one (m : ℕ) : a₁ m 1 = m := rfl
@[simp] theorem a₁_two (m : ℕ) : a₁ m 2 = m + 1 := rfl
@[simp] theorem a₂_zero (m : ℕ) : a₂ m 0 = m := rfl
@[simp] theorem a₂_one (m : ℕ) : a₂ m 1 = m + 1 := rfl
@[simp] theorem a₂_two (m : ℕ) : a₂ m 2 = m := rfl

/-- the first pattern `σ_{m+1} σ_m σ_{m+1}` -/
abbrev P₁ (m : ℕ) : Word := [.σ (m + 1), .σ m, .σ (m + 1)]
/-- the second pattern `σ_m σ_{m+1} σ_m` -/
abbrev P₂ (m : ℕ) : Word := [.σ m, .σ (m + 1), .σ m]

theorem blk₁ (X Y : Word) (m : ℕ) (hm : 1 ≤ m) (hV : (X ++ P₁ m ++ Y).Closed) :
    Blk (X ++ P₁ m ++ Y) X.length m (a₁ m) where
  hk := by simp
  hm := hm
  letter i hi := by
    interval_cases i
    · exact U3.letterAt_block X (P₁ m) Y (by norm_num)
    · exact U3.letterAt_block X (P₁ m) Y (by norm_num)
    · exact U3.letterAt_block X (P₁ m) Y (by norm_num)
  idx i hi := by interval_cases i <;> simp
  len := by
    have hℓ : letterAt (X ++ P₁ m ++ Y) X.length = .σ (m + 1) := U3.letterAt_block X (P₁ m) Y (i := 0) (by norm_num)
    exact (σ_facts hV (by simp) hℓ).2.1

theorem blk₂ (X Y : Word) (m : ℕ) (hm : 1 ≤ m) (hV : (X ++ P₂ m ++ Y).Closed) :
    Blk (X ++ P₂ m ++ Y) X.length m (a₂ m) where
  hk := by simp
  hm := hm
  letter i hi := by
    interval_cases i
    · exact U3.letterAt_block X (P₂ m) Y (by norm_num)
    · exact U3.letterAt_block X (P₂ m) Y (by norm_num)
    · exact U3.letterAt_block X (P₂ m) Y (by norm_num)
  idx i hi := by interval_cases i <;> simp
  len := by
    have hℓ0 : letterAt (X ++ P₂ m ++ Y) X.length = .σ m := U3.letterAt_block X (P₂ m) Y (i := 0) (by norm_num)
    have hℓ1 : letterAt (X ++ P₂ m ++ Y) (X.length + 1) = .σ (m + 1) := U3.letterAt_block X (P₂ m) Y (i := 1) (by norm_num)
    have h1 := (σ_facts hV (by simp) hℓ1).2.1
    rw [(σ_facts hV (by simp) hℓ0).2.2.1] at h1
    exact h1

theorem shiftIdx_eq_self (X P P' : Word) (h : P.length = P'.length) (k : ℕ)
    (hk : k ≤ X.length ∨ X.length + P.length ≤ k) : shiftIdx X P P' k = k := by
  unfold shiftIdx; split_ifs <;> omega

theorem sameEffect₁₂ (X Y : Word) (m : ℕ) (hm : 1 ≤ m) (hV : (X ++ P₁ m ++ Y).Closed) : SameEffect X (P₁ m) (P₂ m) :=
  sameEffect_of_replace X (P₁ m) Y (P₂ m) hV fun c c' h => by
    obtain ⟨A, p, q, r, L, hA, rfl, rfl⟩ := run_typeIII_aux hm h
    exact (run_typeIII_of_split hm hA).2

theorem pos3₁₂ (m p : ℕ) (_hp : m ≤ p ∧ p ≤ m + 2) : pos (a₁ m) p 3 = pos (a₂ m) p 3 := by
  rw [pos_three, pos_three]
  simp only [a₁_zero, a₁_one, a₁_two, a₂_zero, a₂_one, a₂_two]
  unfold swp; split_ifs <;> omega

/-- the pair hypothesis of the type-III move -/
theorem pair₁₂ (X Y : Word) (m : ℕ) (hm : 1 ≤ m) (hV : (X ++ P₁ m ++ Y).Closed) (hV' : (X ++ P₂ m ++ Y).Closed) :
    Pair (X ++ P₁ m ++ Y) (X ++ P₂ m ++ Y) X.length m (a₁ m) (a₂ m) where
  blk := blk₁ X Y m hm hV
  blk' := blk₂ X Y m hm hV'
  len := by simp
  letter_ext k' h := by
    have := letterAt_ext X (P₁ m) Y (P₂ m) (by simp) (k := k')
      (by unfold ExtCol; simp only [List.length_cons, List.length_nil]; omega)
    rwa [shiftIdx_eq_self X (P₁ m) (P₂ m) rfl k' (by simp only [List.length_cons, List.length_nil]; omega)] at this
  cut_ext k' h := by
    have := cut_ext X (P₁ m) Y (P₂ m) (by simp) (sameEffect₁₂ X Y m hm hV) (k := k')
      (by unfold ExtCut; simp only [List.length_cons, List.length_nil]; omega)
    rwa [shiftIdx_eq_self X (P₁ m) (P₂ m) rfl k' (by simp only [List.length_cons, List.length_nil]; omega)] at this
  pos3 p hp := pos3₁₂ m p hp

theorem tbl₁ (m : ℕ) :
    (pos (a₁ m) (m + 0) 2 = a₁ m 2 ∧ pos (a₁ m) (m + 1) 2 = a₁ m 2 + 1) ∧
    (pos (a₁ m) (m + 0) 1 = a₁ m 1 ∧ pos (a₁ m) (m + 2) 1 = a₁ m 1 + 1) ∧
    (pos (a₁ m) (m + 1) 0 = a₁ m 0 ∧ pos (a₁ m) (m + 2) 0 = a₁ m 0 + 1) := by
  simp only [pos_two, pos_one, pos_zero, a₁_zero, a₁_one, a₁_two, and_true]
  unfold swp; split_ifs <;> omega

theorem tbl₂ (m : ℕ) :
    (pos (a₂ m) (m + 0) 0 = a₂ m 0 ∧ pos (a₂ m) (m + 1) 0 = a₂ m 0 + 1) ∧
    (pos (a₂ m) (m + 0) 1 = a₂ m 1 ∧ pos (a₂ m) (m + 2) 1 = a₂ m 1 + 1) ∧
    (pos (a₂ m) (m + 1) 2 = a₂ m 2 ∧ pos (a₂ m) (m + 2) 2 = a₂ m 2 + 1) := by
  simp only [pos_two, pos_one, pos_zero, a₂_zero, a₂_one, a₂_two, and_true]
  unfold swp; split_ifs <;> omega

/-- the site for `σ_{m+1} σ_m σ_{m+1} ↦ σ_m σ_{m+1} σ_m` -/
theorem site₁₂ (X Y : Word) (m : ℕ) (hm : 1 ≤ m) (hV : (X ++ P₁ m ++ Y).Closed) (hV' : (X ++ P₂ m ++ Y).Closed)
    (hne : X ++ P₁ m ++ Y ≠ []) (hne' : X ++ P₂ m ++ Y ≠ []) :
    Nonempty (RIIIData (band X.length m) (realizeAt .std hV hne).diagram (realizeAt .std hV' hne').diagram) :=
  (pair₁₂ X Y m hm hV hV').site_of hV hV' hne hne' 2 1 0 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (tbl₁ m).1 (tbl₁ m).2.1 (tbl₁ m).2.2 (tbl₂ m).1 (tbl₂ m).2.1 (tbl₂ m).2.2
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- the site for `σ_m σ_{m+1} σ_m ↦ σ_{m+1} σ_m σ_{m+1}` -/
theorem site₂₁ (X Y : Word) (m : ℕ) (hm : 1 ≤ m) (hV : (X ++ P₂ m ++ Y).Closed) (hV' : (X ++ P₁ m ++ Y).Closed)
    (hne : X ++ P₂ m ++ Y ≠ []) (hne' : X ++ P₁ m ++ Y ≠ []) :
    Nonempty (RIIIData (band X.length m) (realizeAt .std hV hne).diagram (realizeAt .std hV' hne').diagram) :=
  (pair₁₂ X Y m hm hV' hV).symm.site_of hV hV' hne hne' 0 1 2 2 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (tbl₂ m).1 (tbl₂ m).2.1 (tbl₂ m).2.2 (tbl₁ m).1 (tbl₁ m).2.1 (tbl₁ m).2.2
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

end

end U5

/-- LEAF (ng:front-III, sm-3:1995-2003 "an actual ordinary Reidemeister-III configuration ... The three
over/under choices give one strict height order ... Each physical pair crosses on both sides with the same
over/under bit and transported arrows"): the two standard realizations (same length, no cusp letter, so the
spectators are literally identical horizontal pieces) form an `RIII` site in the band disc
`[x_k, x_{k+3}] × [−(m+2)−ε, −m+ε]`; the arcs are the three strands entering at positions `m, m+1, m+2`,
named by height, the visit order along each arc reversed.  Either direction of `IsTypeIII` (the data are
symmetric in the two diagrams). -/
theorem typeIII_site {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    ∃ U : Set Plane, Nonempty (RIIIData U (realize W).diagram (realize W').diagram) := by
  obtain ⟨X, Y, m, hm, hpat⟩ := h
  have hne : W.letters ≠ [] := by rcases hpat with ⟨hW, -⟩ | ⟨hW, -⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by rcases hpat with ⟨-, hW'⟩ | ⟨-, hW'⟩ <;> rw [hW'] <;> simp
  rw [realize_eq_realizeAt W hne, realize_eq_realizeAt W' hne']
  refine ⟨U5.band X.length m, ?_⟩
  have hcl := W.closed
  have hcl' := W'.closed
  rcases hpat with ⟨hW, hW'⟩ | ⟨hW, hW'⟩
  · rw [hW] at hcl hne; rw [hW'] at hcl' hne'
    have := U5.site₁₂ X Y m hm hcl hcl' hne hne'
    convert this using 3 <;> simp only [hW, hW']
  · rw [hW] at hcl hne; rw [hW'] at hcl' hne'
    have := U5.site₂₁ X Y m hm hcl hcl' hne hne'
    convert this using 3 <;> simp only [hW, hW']

/-! ### U6 infrastructure -/

/-! Unit U6 (`typeII_move`, `typeI_move`, `crossedCusp_move`; PLAN_FINAL.md §4 "L-geo", §5 "U6 geo I/II/X").
Section A: a generic assembly of the accepted `RIData` from slot-level data on a vertex-moved slot diagram
(U4's `polygon`, `PieceIn`/`PieceOut`, `GenericData`, `MatchData`, `Chain`), consumed by the concrete
patterns of sections B-D. -/

namespace U6

open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4

noncomputable section

section Helpers

variable (L : List HalfPlane) (pl : Placement) {W : Word} (hW : W.Closed) (mv : Slot W → Plane)

/-- the realization's vertex function -/
abbrev ptv : Slot W → Plane := fun u => pt pl W u.1

omit hW in
theorem ptv_apply (u : Slot W) : ptv pl (W := W) u = pt pl W u.1 := rfl

theorem pieceOut_unch_iff {u : Slot W} (hu : Unch pl hW mv u) :
    PieceOut L hW mv u ↔ PieceOut L hW (ptv pl) u := by
  unfold PieceOut; rw [hu.1, hu.2]

theorem pieceIn_unch_iff {u : Slot W} (hu : Unch pl hW mv u) :
    PieceIn L hW mv u ↔ PieceIn L hW (ptv pl) u := by
  unfold PieceIn; rw [hu.1, hu.2]

include hW in
/-- the cut of a slot is its column or the next one; a cusp vertex sits at its column -/
theorem cut_spec (u : Slot W) :
    (u.1.1 = colOf u ∨ u.1.1 = colOf u + 1) ∧ (u.1.2 = 0 → u.1.1 = colOf u) := by
  obtain ⟨⟨k, p⟩, hs⟩ := u
  simp only [colOf]
  by_cases hp : p = 0
  · simp [hp]
  · simp only [hp, ↓reduceIte, false_implies, and_true]
    split_ifs with hb
    · exact Or.inl rfl
    · have hk : 0 < k := by
        rcases hs with ⟨h, -⟩ | ⟨h1, h2, -⟩
        · exact absurd h hp
        · exact (cutSlot_pos hW h1 h2).1
      right; omega

/-- the successor's cut is the column or the next one; a cusp successor sits at the column -/
theorem next_cut_spec (u : Slot W) :
    ((next hW u).1.1 = colOf u ∨ (next hW u).1.1 = colOf u + 1) ∧ ((next hW u).1.2 = 0 → (next hW u).1.1 = colOf u) := by
  rcases next_cases hW u with
    ⟨k, p, q, hs, hp, hb, hn, hq, -, -, -⟩ | ⟨k, p, m, hs, hp, hb, -, -, hn, -, -⟩ |
    ⟨k, p, q, hs, hp, hb, hn, hq, -, -, hk1, -⟩ | ⟨k, p, m, d, hs, hp, hb, -, -, hn, -, -, hk1, -⟩ |
    ⟨k, m, d, hs, -, hn, -, -, hm, -⟩ | ⟨k, m, hs, -, hn, -, hm, -⟩
  · rw [U3.colOf_val hs, hn]; simp [show p ≠ 0 by omega, hb, show q ≠ 0 by omega]
  · rw [U3.colOf_val hs, hn]; simp [show p ≠ 0 by omega, hb]
  · rw [U3.colOf_val hs, hn]; simp [show p ≠ 0 by omega, hb, show q ≠ 0 by omega]
  · rw [U3.colOf_val hs, hn]; simp [show p ≠ 0 by omega, hb]
  · rw [U3.colOf_val hs, hn]; cases d <;> simp
    omega
  · rw [U3.colOf_val hs, hn]; cases bit W k m <;> simp

/-- The slots of `W` that a block move `[a, b)` never moves: cut slots at cuts `≤ a` or `≥ b`, cusp vertices of
columns outside `[a, b)` (= `IsExtSlot` for `a = |X|`, `b = |X| + |P|`). -/
def ExtSl (a b : ℕ) (s : ℕ × ℕ) : Prop := if s.2 = 0 then (s.1 + 1 ≤ a ∨ b ≤ s.1) else (s.1 ≤ a ∨ b ≤ s.1)

omit hW in
theorem extSl_iff_isExtSlot (X P : Word) (s : ℕ × ℕ) : ExtSl X.length (X.length + P.length) s ↔ IsExtSlot X P s := by
  unfold ExtSl IsExtSlot ExtCol ExtCut; exact Iff.rfl

/-- A piece of an exterior column is unchanged when the move leaves the exterior slots in place. -/
theorem unch_of_extCol {a b : ℕ} (hmv : ∀ v : Slot W, ExtSl a b v.1 → mv v = pt pl W v.1)
    {u : Slot W} (hcol : colOf u + 1 ≤ a ∨ b ≤ colOf u) : Unch pl hW mv u := by
  obtain ⟨h1, h2⟩ := cut_spec hW u
  obtain ⟨h3, h4⟩ := next_cut_spec hW u
  constructor
  · apply hmv; unfold ExtSl; split_ifs with h0
    · rw [h2 h0]; exact hcol
    · omega
  · apply hmv; unfold ExtSl; split_ifs with h0
    · rw [h4 h0]; exact hcol
    · omega

/-- An inside piece and an outside piece meet only at shared ends (given an injective vertex map). -/
theorem meetSpec_of_in_out (K : ℕ → Prop) (hinj : Function.Injective mv) {u v : Slot W}
    (hu : PieceIn L hW mv u) (hv : PieceOut L hW mv v) : MeetSpec pl hW mv K u v := by
  have hu' : SegIn L (mv u) (mv (next hW u)) := hu
  have hv' : SegOut L (mv v) (mv (next hW v)) := hv
  intro τ τ' h0 h1 h0' h1' he
  have hmem : segPt (mv v) (mv (next hW v)) τ' ∈ polygon L := he ▸ hu'.mem h0 h1
  rcases hv'.eq_end_of_mem h0' h1' hmem with rfl | rfl
  · simp only [segPt_zero] at he
    have hnot : mv v ∉ interior (polygon L) := hv'.left_notMem_interior
    rcases eq_or_lt_of_le h0 with rfl | h0''
    · simp only [segPt_zero] at he
      exact Or.inl ⟨hinj he, rfl⟩
    rcases eq_or_lt_of_le h1 with rfl | h1''
    · simp only [segPt_one] at he
      exact Or.inr (Or.inl ⟨(hinj he).symm, rfl, rfl⟩)
    · exact absurd (he ▸ hu'.mem_interior h0'' h1'') hnot
  · simp only [segPt_one] at he
    have hnot : mv (next hW v) ∉ interior (polygon L) := hv'.right_notMem_interior
    rcases eq_or_lt_of_le h0 with rfl | h0''
    · simp only [segPt_zero] at he
      exact Or.inr (Or.inr (Or.inl ⟨hinj he, rfl, rfl⟩))
    rcases eq_or_lt_of_le h1 with rfl | h1''
    · simp only [segPt_one] at he
      exact Or.inl ⟨next_injective hW (hinj he), rfl⟩
    · exact absurd (he ▸ hu'.mem_interior h0'' h1'') hnot

/-- **Genericity from chain data**: the non-chain pieces are unchanged and outside, the chain pieces are inside,
same-column chain pairs satisfy the meeting specification, and a `σ` column with both crossing pieces unchanged
is in `K`. -/
theorem genericData_of (K : ℕ → Prop) (c : Chain W) (hinj : Function.Injective mv)
    (hx : ∀ u, (mv u).1 = (pt pl W u.1).1)
    (hrest : ∀ u, (∃ j, j < c.n ∧ c.slot hW j = u) ∨ (Unch pl hW mv u ∧ PieceOut L hW (ptv pl) u))
    (hchain : ∀ j, j < c.n → PieceIn L hW mv (c.slot hW j))
    (hpairs : ∀ j j', j < c.n → j' < c.n → c.slot hW j ≠ c.slot hW j' →
      colOf (c.slot hW j) = colOf (c.slot hW j') → MeetSpec pl hW mv K (c.slot hW j) (c.slot hW j'))
    (hKu : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      Unch pl hW mv (σSlotA hW hk hℓ) → Unch pl hW mv (σSlotB hW hk hℓ) → K k) :
    GenericData pl hW mv K where
  inj := hinj
  xcoord := hx
  meet := by
    intro u v huv hc
    rcases hrest u with ⟨j, hj, rfl⟩ | ⟨huu, huo⟩
    · rcases hrest v with ⟨j', hj', rfl⟩ | ⟨hvu, hvo⟩
      · exact hpairs j j' hj hj' huv hc
      · exact meetSpec_of_in_out L pl hW mv K hinj (hchain j hj) ((pieceOut_unch_iff L pl hW mv hvu).2 hvo)
    · rcases hrest v with ⟨j', hj', rfl⟩ | ⟨hvu, hvo⟩
      · exact (meetSpec_of_in_out L pl hW mv K hinj (hchain j' hj') ((pieceOut_unch_iff L pl hW mv huu).2 huo)).symm
      · exact meetSpec_of_unch pl hW mv K huu hvu hKu

end Helpers

/-! #### A2. The `RIData` assembly -/

section Assembly

variable (L : List HalfPlane) (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane)
  (K : ℕ → Prop)

/-- the vertex-moved diagram of `mv` -/
abbrev mvDiagram (d : GenericData pl hW mv K) : Diagram :=
  U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) (generic_of pl hW hne mv K d) (ovMv pl hW hne mv) (ovMv_mem pl hW hne mv)

/-- the realization's diagram in slot-diagram form (`realizeAt_diagram_eq` is `rfl`) -/
abbrev rlDiagram : Diagram :=
  U2.mkDiagram pl hW hne (vertsOf pl hW hne (ptv pl)) (generic pl hW hne) (realizeAt pl hW hne).overStrand
    (realizeAt pl hW hne).overStrand_mem

theorem rlDiagram_eq : rlDiagram pl hW hne = (realizeAt pl hW hne).diagram := rfl

/-- **The slot-level specification of a Reidemeister-I site** between the vertex-moved diagram (crossing-free
side) and the realization (one kink) in the polygon `L`, along one chain `c`. -/
structure RISpec (c : Chain W) : Prop where
  disc : IsDisc (polygon L)
  hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
    K k ↔ Unch pl hW mv (σSlotA hW hk hℓ) ∧ Unch pl hW mv (σSlotB hW hk hℓ)
  hKout : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
    K k ↔ PieceOut L hW (ptv pl) (σSlotA hW hk hℓ)
  moved : ∀ u, mv u = pt pl W u.1 ∨ (mv u ∈ interior (polygon L) ∧ pt pl W u.1 ∈ interior (polygon L))
  chain : ∀ j, j < c.n → PieceIn L hW mv (c.slot hW j) ∧ PieceIn L hW (ptv pl) (c.slot hW j)
  vert : ∀ j, 0 < j → j < c.n → mv (c.slot hW j) ∈ interior (polygon L) ∧ pt pl W (c.slot hW j).1 ∈ interior (polygon L)
  rest : ∀ u, (∃ j, j < c.n ∧ c.slot hW j = u) ∨ (Unch pl hW mv u ∧ PieceOut L hW (ptv pl) u)
  prevOut : Unch pl hW mv (prev hW c.u₀) ∧ PieceOut L hW (ptv pl) (prev hW c.u₀)
  stopOut : Unch pl hW mv (c.slot hW c.n) ∧ PieceOut L hW (ptv pl) (c.slot hW c.n)
  touch : ∀ u, PieceOut L hW (ptv pl) u → pt pl W u.1 ∈ polygon L → u = c.slot hW c.n
  exits : ∀ u : Slot W, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch pl hW mv v ∧ PieceOut L hW (ptv pl) v
  kink : ∃ (k₀ m₀ : ℕ) (_hk₀ : k₀ < W.length) (_hℓ₀ : letterAt W k₀ = .σ m₀), ¬ K k₀ ∧
    ∀ (k m : ℕ) (_hk : k < W.length) (_hℓ : letterAt W k = .σ m), ¬ K k → k = k₀

variable {L pl hW mv K}

/-- the pieces are classified on both sides and the outside pieces agree -/
theorem RISpec.cl {c : Chain W} (S : RISpec L pl hW mv K c) : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u := fun u => by
  rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨hu, ho⟩
  · exact Or.inl (S.chain j hj).1
  · exact Or.inr ((pieceOut_unch_iff L pl hW mv hu).2 ho)

theorem RISpec.cl' {c : Chain W} (S : RISpec L pl hW mv K c) : ∀ u, PieceIn L hW (ptv pl) u ∨ PieceOut L hW (ptv pl) u :=
  fun u => by
  rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨hu, ho⟩
  · exact Or.inl (S.chain j hj).2
  · exact Or.inr ho

theorem RISpec.out_iff {c : Chain W} (S : RISpec L pl hW mv K c) : ∀ u, PieceOut L hW mv u ↔ PieceOut L hW (ptv pl) u :=
  fun u => by
  rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨hu, ho⟩
  · exact ⟨fun h => absurd (S.chain j hj).1 (not_pieceIn_of_pieceOut L hW mv h),
      fun h => absurd (S.chain j hj).2 (not_pieceIn_of_pieceOut L hW _ h)⟩
  · exact pieceOut_unch_iff L pl hW mv hu

theorem RISpec.matchData {c : Chain W} (S : RISpec L pl hW mv K c) :
    MatchData L hW hW mv (ptv pl) (Equiv.refl _) where
  cl := S.cl
  cl' := S.cl'
  out_iff := S.out_iff
  pt_eq := fun u hu => by
    rcases S.moved u with h | ⟨h1, -⟩
    · exact h.symm
    · exact absurd h1 hu
  int_iff := fun u => by
    rcases S.moved u with h | ⟨h1, h2⟩
    · show mv u ∈ _ ↔ pt pl W u.1 ∈ _
      rw [h]
    · exact ⟨fun _ => h2, fun _ => h1⟩
  next_eq := fun _ _ => rfl

theorem RISpec.isChain {c : Chain W} (S : RISpec L pl hW mv K c) : c.IsChain L hW mv where
  pieceIn := fun j hj => (S.chain j hj).1
  vertex_interior := fun j h0 hj => (S.vert j h0 hj).1
  out_prev := (pieceOut_unch_iff L pl hW mv S.prevOut.1).2 S.prevOut.2
  out_stop := (pieceOut_unch_iff L pl hW mv S.stopOut.1).2 S.stopOut.2

theorem RISpec.isChain' {c : Chain W} (S : RISpec L pl hW mv K c) : c.IsChain L hW (ptv pl) where
  pieceIn := fun j hj => (S.chain j hj).2
  vertex_interior := fun j h0 hj => (S.vert j h0 hj).2
  out_prev := S.prevOut.2
  out_stop := S.stopOut.2

/-- the entry vertex is unmoved -/
theorem RISpec.mv_u₀ {c : Chain W} (S : RISpec L pl hW mv K c) : mv c.u₀ = pt pl W c.u₀.1 := by
  rcases S.moved c.u₀ with h | ⟨h1, -⟩
  · exact h
  · exfalso
    have ho : SegOut L (mv (prev hW c.u₀)) (mv (next hW (prev hW c.u₀))) := S.isChain.out_prev
    rw [next_prev] at ho
    exact ho.right_notMem_interior h1

/-- the stop vertex is unmoved -/
theorem RISpec.mv_stop {c : Chain W} (S : RISpec L pl hW mv K c) : mv (c.slot hW c.n) = pt pl W (c.slot hW c.n).1 := by
  rcases S.moved (c.slot hW c.n) with h | ⟨h1, -⟩
  · exact h
  · exfalso
    have ho : SegOut L (mv (c.slot hW c.n)) (mv (next hW (c.slot hW c.n))) := S.isChain.out_stop
    exact ho.left_notMem_interior h1

theorem chain_slot_pred (c : Chain W) : prev hW (c.slot hW c.n) = c.slot hW (c.n - 1) := by
  have e : c.slot hW c.n = next hW (c.slot hW (c.n - 1)) := by
    rw [← Chain.slot_succ, Nat.sub_add_cancel c.hn]
  rw [e, prev_next]

theorem RISpec.arcCover {c : Chain W} (S : RISpec L pl hW mv K c) :
    (shadowMv pl hW hne mv).ArcCover (polygon L) {c.toArc pl hW hne mv} := by
  have e : ({c.toArc pl hW hne mv} : Set (shadowMv pl hW hne mv).Arc) = arcsOf pl hW hne mv [c] := by
    ext a; simp [arcsOf]
  rw [e]
  refine arcCover_of L pl hW hne mv [c] (fun c' hc' => by rw [List.mem_singleton] at hc'; rw [hc']; exact S.isChain)
    S.cl ?_ ?_ ?_
  · intro u hu
    rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨huu, ho⟩
    · exact ⟨c, List.mem_singleton_self _, j, hj, rfl⟩
    · exact absurd hu (not_pieceIn_of_pieceOut L hW mv ((pieceOut_unch_iff L pl hW mv huu).2 ho))
  · intro c' hc' c'' hc'' hne'
    rw [List.mem_singleton] at hc' hc''
    exact absurd (hc'.trans hc''.symm) hne'
  · intro u hu hmem
    have hni : mv u ∉ interior (polygon L) := SegOut.left_notMem_interior hu
    have hpt : mv u = pt pl W u.1 := by
      rcases S.moved u with h | ⟨h1, -⟩
      · exact h
      · exact absurd h1 hni
    have hu' : PieceOut L hW (ptv pl) u := (S.out_iff u).1 hu
    have he := S.touch u hu' (hpt ▸ hmem)
    rw [he, chain_slot_pred]
    exact (S.chain _ (by have := c.hn; omega)).1

theorem RISpec.arcCover' {c : Chain W} (S : RISpec L pl hW mv K c) :
    (shadowMv pl hW hne (ptv pl)).ArcCover (polygon L) {c.toArc pl hW hne (ptv pl)} := by
  have e : ({c.toArc pl hW hne (ptv pl)} : Set (shadowMv pl hW hne (ptv pl)).Arc) = arcsOf pl hW hne (ptv pl) [c] := by
    ext a; simp [arcsOf]
  rw [e]
  refine arcCover_of L pl hW hne (ptv pl) [c] (fun c' hc' => by rw [List.mem_singleton] at hc'; rw [hc']; exact S.isChain')
    S.cl' ?_ ?_ ?_
  · intro u hu
    rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨-, ho⟩
    · exact ⟨c, List.mem_singleton_self _, j, hj, rfl⟩
    · exact absurd hu (not_pieceIn_of_pieceOut L hW _ ho)
  · intro c' hc' c'' hc'' hne'
    rw [List.mem_singleton] at hc' hc''
    exact absurd (hc'.trans hc''.symm) hne'
  · intro u hu hmem
    have he := S.touch u hu hmem
    rw [he, chain_slot_pred]
    exact (S.chain _ (by have := c.hn; omega)).2

theorem RISpec.exitsMv {c : Chain W} (S : RISpec L pl hW mv K c) : ExitsMv L hW mv :=
  exitsMv_of_sameCycle L hW mv fun u => by
    obtain ⟨v, hsc, hunch, hout⟩ := S.exits u
    exact ⟨v, hsc, (pieceOut_unch_iff L pl hW mv hunch).2 hout⟩

theorem RISpec.exitsMv' {c : Chain W} (S : RISpec L pl hW mv K c) : ExitsMv L hW (ptv pl) :=
  exitsMv_of_sameCycle L hW (ptv pl) fun u => by
    obtain ⟨v, hsc, -, hout⟩ := S.exits u
    exact ⟨v, hsc, hout⟩

/-- **The Reidemeister-I site** from the specification: the vertex-moved diagram is the crossing-free side, the
realization carries the kink. -/
theorem riData_of {c : Chain W} (d : GenericData pl hW mv K) (S : RISpec L pl hW mv K c) :
    Nonempty (RIData (polygon L) (mvDiagram pl hW hne mv K d) (rlDiagram pl hW hne)) := by
  classical
  have data := slotDiagramData_of pl hW hne mv K d S.hK
  have data' := realizeAt_data' pl hW hne
  have hσ : SigmaCorr L hW hW mv (Equiv.refl _) K (fun _ => True) :=
    fun k m hk hℓ _ _ => ⟨k, m, hk, hℓ, trivial, rfl, rfl⟩
  have hσ' : SigmaCorr L hW hW (ptv pl) (Equiv.refl _).symm (fun _ => True) K :=
    fun k m hk hℓ _ ho => ⟨k, m, hk, hℓ, (S.hKout k m hk hℓ).2 ho, rfl, rfl⟩
  obtain ⟨k₀, m₀, hk₀, hℓ₀, hK₀, huniq⟩ := S.kink
  refine ⟨{ frame := ⟨S.disc, clean_mv L pl hW hne mv d.inj S.cl S.exitsMv _ _ _,
              clean_mv L pl hW hne (ptv pl) (fun u v h => pt_inj pl W h) S.cl' S.exitsMv' _ _ _⟩
            out := S.matchData.moveMatch pl hne hne (generic_of pl hW hne mv K d) (ovMv pl hW hne mv)
              (ovMv_mem pl hW hne mv) K data (generic pl hW hne) (realizeAt pl hW hne).overStrand
              (realizeAt pl hW hne).overStrand_mem (fun _ => True) data' hσ hσ' (Equiv.refl _) (fun _ _ => rfl)
            a := c.toArc pl hW hne mv
            a' := c.toArc pl hW hne (ptv pl)
            cover := S.arcCover hne
            cover' := S.arcCover' hne
            start_eq := ?_
            stop_eq := ?_
            no_inner := ?_
            kink := ⟨σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₀ hℓ₀, (data'.cross _).2 ⟨k₀, m₀, hk₀, hℓ₀, trivial, rfl⟩⟩
            inner_iff' := ?_ }⟩
  · show (shadowMv pl hW hne (ptv pl)).eval (c.toArc pl hW hne (ptv pl)).startPt =
      (shadowMv pl hW hne mv).eval (c.toArc pl hW hne mv).startPt
    rw [Chain.eval_startPt, Chain.eval_startPt, S.mv_u₀]
  · show (shadowMv pl hW hne (ptv pl)).eval (c.toArc pl hW hne (ptv pl)).stopPt =
      (shadowMv pl hW hne mv).eval (c.toArc pl hW hne mv).stopPt
    rw [Chain.eval_stopPt, Chain.eval_stopPt, S.mv_stop]
  · intro x
    obtain ⟨k, m, hk, hℓ, hKk, hx⟩ := (data.cross x.val).1 x.2
    have hs : stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ) ∈ x.val := by
      rw [hx]; exact mem_σpair_A pl hW hne _ hk hℓ
    show (shadowMv pl hW hne mv).crossingPoint x ∉ interior (polygon L)
    rw [crossingPoint_notMem_interior_iff L pl hW hne mv S.cl (generic_of pl hW hne mv K d) x hs]
    show PieceOut L hW mv (idxEquiv hW (stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ)))
    rw [idxEquiv_stStrand]
    exact (pieceOut_unch_iff L pl hW mv ((S.hK k m hk hℓ).1 hKk).1).2 ((S.hKout k m hk hℓ).1 hKk)
  · intro y
    obtain ⟨k, m, hk, hℓ, -, hy⟩ := (data'.cross y.val).1 y.2
    have hs : stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) ∈ y.val := by
      rw [hy]; exact mem_σpair_A pl hW hne _ hk hℓ
    have hiff := crossingPoint_notMem_interior_iff L pl hW hne (ptv pl) S.cl' (generic pl hW hne) y hs
    have e : slotMv pl hW hne (ptv pl) (stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ)) =
        σSlotA hW hk hℓ := idxEquiv_stStrand pl hW hne _ _
    rw [e] at hiff
    show (shadowMv pl hW hne (ptv pl)).crossingPoint y ∈ interior (polygon L) ↔ _
    by_cases hKk : K k
    · have hno := hiff.2 ((S.hKout k m hk hℓ).1 hKk)
      refine ⟨fun h => absurd h hno, fun h => ?_⟩
      exfalso
      have hval : y.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₀ hℓ₀ := by rw [h]
      rw [hy] at hval
      have hmem : stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) ∈
          σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₀ hℓ₀ := by rw [← hval]; exact mem_σpair_A pl hW hne _ hk hℓ
      have hc := colOf_of_mem_σpair pl hW hne _ hk₀ hℓ₀ hmem
      rw [idxEquiv_stStrand, (σSlotA_spec hW hk hℓ).1] at hc
      exact hK₀ (hc ▸ hKk)
    · have hk0 : k = k₀ := huniq k m hk hℓ hKk
      subst hk0
      have hm0 : m = m₀ := by
        have := hℓ.symm.trans hℓ₀
        cases this; rfl
      subst hm0
      refine ⟨fun _ => Subtype.ext hy, fun _ => ?_⟩
      by_contra h
      exact hKk ((S.hKout k m hk hℓ).2 (hiff.1 h))

end Assembly

/-! #### A3. Exits of a block without left (or right) cusps -/

section HexitGeneric

variable (X P Y : Word) (hW : (X ++ P ++ Y).Closed)
include hW

/-- every component of a word meets the exterior of a block without left cusps -/
theorem hexit_of_no_l (hno : ∀ k, X.length ≤ k → k < X.length + P.length → ∀ m d, letterAt (X ++ P ++ Y) k ≠ .l m d) :
    ∀ u : Slot (X ++ P ++ Y), ∃ n, ExtPiece X P Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_l hW X.length (X.length + P.length) hno u
  obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW hsc
  exact ⟨n, by rw [hn]; exact hcol⟩

/-- every component of a word meets the exterior of a block without right cusps -/
theorem hexit_of_no_r (hno : ∀ k, X.length ≤ k → k < X.length + P.length → ∀ m, letterAt (X ++ P ++ Y) k ≠ .r m) :
    ∀ u : Slot (X ++ P ++ Y), ∃ n, ExtPiece X P Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_r hW X.length (X.length + P.length) hno u
  obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW hsc
  exact ⟨n, by rw [hn]; exact hcol⟩

end HexitGeneric

section StdGeom

theorem std_pt_cut (W : Word) {j p : ℕ} (hp : p ≠ 0) : pt .std W (j, p) = ((j : ℝ), -(p : ℝ)) := by
  rw [pt_cut _ _ hp]; rfl

theorem std_mid (j : ℕ) : Placement.std.mid j = (j : ℝ) + 1 / 2 := by
  show (j : ℝ) + (((j + 1 : ℕ) : ℝ) - j) / 2 = (j : ℝ) + 1 / 2
  push_cast; ring

theorem std_pt_cusp (W : Word) (j : ℕ) : pt .std W (j, 0) = ((j : ℝ) + 1 / 2, -((letterAt W j).idx : ℝ) - 1 / 2) := by
  rw [pt_cusp, std_mid]

/-- the crossed-cusp disc: `[k, k+2] × [−i−3/2, −i+1/2]` cut by the line `y ≥ −i + 1/4 − 2(x − k)` -/
def ccL (k i : ℕ) : List HalfPlane :=
  [HalfPlane.xge (k : ℝ), HalfPlane.xle ((k : ℝ) + 2), HalfPlane.yle (-(i : ℝ) + 1 / 2), HalfPlane.yge (-(i : ℝ) - 3 / 2),
    HalfPlane.above (-(i : ℝ) + 1 / 4 + 2 * k) (-2)]

example (k i : ℕ) : ((k : ℝ) + 1, -(i : ℝ) - 3 / 4) ∈ interior (polygon (ccL k i)) := by
  simp only [ccL, mem_interior_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

example (k i : ℕ) : SegIn (ccL k i) ((k : ℝ) + 1 / 2, -(i : ℝ) - 1 / 2) ((k : ℝ) + 1, -(i : ℝ) - 3 / 4) := by
  simp only [ccL, SegIn, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    first | linarith | (left; linarith)

/-- a spectator below the block in column `k`: `pass p (p+2)` with `i ≤ p` -/
example (k i p : ℕ) (hp : i ≤ p) : SegOut (ccL k i) ((k : ℝ), -(p : ℝ)) ((k : ℝ) + 1, -(p : ℝ) - 2) := by
  have hp' : (i : ℝ) ≤ p := by exact_mod_cast hp
  refine segOut_of_lt (HalfPlane.above (-(i : ℝ) + 1 / 4 + 2 * k) (-2)) (by simp [ccL]) ?_ ?_ <;>
    simp only [HalfPlane.f_above, HalfPlane.b_above] <;> linarith

/-- a spectator above the block: horizontal at height `−p`, `p < i` -/
example (k i p : ℕ) (hp : p < i) : SegOut (ccL k i) ((k : ℝ) + 1, -(p : ℝ)) ((k : ℝ) + 2, -(p : ℝ)) := by
  have hp' : (p : ℝ) + 1 ≤ i := by exact_mod_cast hp
  refine segOut_of_lt (HalfPlane.yle (-(i : ℝ) + 1 / 2)) (by simp [ccL]) ?_ ?_ <;>
    simp only [HalfPlane.f_yle, HalfPlane.b_yle] <;> linarith

theorem ccL_isDisc (k i : ℕ) : IsDisc (polygon (ccL k i)) := by
  refine isDisc_polygon (ccL k i) (a := k) (b := (k : ℝ) + 2) (c := -(i : ℝ) - 3 / 2) (d := -(i : ℝ) + 1 / 2) ?_
    ⟨((k : ℝ) + 1, -(i : ℝ) - 1 / 2), ?_⟩
  · intro q hq
    simp only [ccL, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
      HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
      HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at hq
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]
  · simp only [ccL, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
      HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
      HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end StdGeom

/-! #### B. The crossed-cusp shortcut, left variant `l_i d σ_i ↦ l_i (!d)` (ng:deletions, sm-3:2027-2033) -/

section CrossedCuspLeftWord

open U3

variable (X Y : Word) (i : ℕ) (d : Bool) (hW : (X ++ [Letter.l i d, Letter.σ i] ++ Y).Closed)

local notation "Vc" => X ++ [Letter.l i d, Letter.σ i] ++ Y
local notation "Pc" => [Letter.l i d, Letter.σ i]
local notation "Vc'" => X ++ [Letter.l i (!d)] ++ Y
local notation "Pc'" => [Letter.l i (!d)]

theorem cl_letters : letterAt Vc X.length = .l i d ∧ letterAt Vc (X.length + 1) = .σ i := by
  constructor
  · have := letterAt_block X Pc Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pc Y (i := 1) (by simp)
    simpa using this

theorem cl_length : (Vc).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem cl'_letters : letterAt Vc' X.length = .l i (!d) := by
  have := letterAt_block X Pc' Y (i := 0) (by simp)
  simpa using this

theorem cl'_length : (Vc').length = X.length + 1 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem cl_extCol (k : ℕ) : ExtCol X Pc k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by
  unfold ExtCol; simp

theorem cl'_extCol (k : ℕ) : ExtCol X Pc' k ↔ k + 1 ≤ X.length ∨ X.length + 1 ≤ k := by
  unfold ExtCol; simp

theorem cl_shift : shiftIdx X Pc Pc' (X.length + 2) = X.length + 1 := by
  unfold shiftIdx; simp

include hW

theorem cl_i_pos : 1 ≤ i := (l_bits hW (by rw [cl_length]; omega) (cl_letters X Y i d).1).1

/-- the bits at the two block cuts: `d, !d` after the cusp, exchanged after the crossing -/
theorem cl_bits :
    bit Vc (X.length + 1) i = d ∧ bit Vc (X.length + 1) (i + 1) = !d ∧
    bit Vc (X.length + 2) i = !d ∧ bit Vc (X.length + 2) (i + 1) = d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := cl_letters X Y i d
  have hk₀ : X.length < (Vc).length := by rw [cl_length]; omega
  have hk₁ : X.length + 1 < (Vc).length := by rw [cl_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, -, -, h3, h4⟩ := σ_facts hW hk₁ hℓ₁
  exact ⟨h1, h2, by rw [h4, h2], by rw [h3, h1]⟩

theorem cl_cutlen : i + 1 ≤ (cut Vc (X.length + 1)).length ∧ (cut Vc (X.length + 2)).length = (cut Vc (X.length + 1)).length := by
  have hk₁ : X.length + 1 < (Vc).length := by rw [cl_length]; omega
  obtain ⟨-, h2, h3, -, -⟩ := σ_facts hW hk₁ (cl_letters X Y i d).2
  exact ⟨h2, h3⟩

/-! the successor table of the block `l_i d σ_i` (columns `|X|`, `|X|+1`) -/

theorem cl_T1 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc X.length p = true)
    (hpi : p < i) : (next hW s).1 = (X.length + 1, p) ∧ bit Vc (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(cl_letters X Y i d).1]; exact hpi)

theorem cl_T2 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc X.length p = true)
    (hpi : i ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Vc (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(cl_letters X Y i d).1]; simpa [idx, arity] using hpi)
  rwa [(cl_letters X Y i d).1] at this

theorem cl_T3 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 1) p = true) (hpi : p < i) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vc (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(cl_letters X Y i d).2]; exact hpi)

theorem cl_T4 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 1) p = true) (hpi : i + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vc (X.length + 2) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(cl_letters X Y i d).2]; simpa [idx, arity] using hpi)
  rw [(cl_letters X Y i d).2] at this
  simpa [coarity, arity] using this

theorem cl_T5 {s : Slot Vc} (hs : s.1 = (X.length + 1, i)) (hb : bit Vc (X.length + 1) i = true) :
    (next hW s).1 = (X.length + 2, i + 1) :=
  next_σ_right_idx hW (cl_letters X Y i d).2 hs hb

theorem cl_T6 {s : Slot Vc} (hs : s.1 = (X.length + 1, i + 1)) (hb : bit Vc (X.length + 1) (i + 1) = true) :
    (next hW s).1 = (X.length + 2, i) :=
  next_σ_right_succ hW (cl_letters X Y i d).2 hs hb

theorem cl_T7 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 1) q = false) (hqi : q < i) :
    (next hW s).1 = (X.length, q) ∧ bit Vc X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (cl_letters X Y i d).1]; exact hqi)
  rwa [Nat.add_sub_cancel] at this

theorem cl_T8 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = i ∨ q = i + 1)
    (hb : bit Vc (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (cl_letters X Y i d).1 hs hq hb

theorem cl_T9 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 1) q = false) (hqi : i + 2 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Vc X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (cl_letters X Y i d).1]; simpa [idx, coarity] using hqi)
  rw [Nat.add_sub_cancel, (cl_letters X Y i d).1] at this
  simpa [arity, coarity] using this

theorem cl_T10 {s : Slot Vc} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then i else i + 1) :=
  next_cusp_l hW (cl_letters X Y i d).1 hs

theorem cl_T11 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 2) q = false) (hqi : q < i) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vc (X.length + 1) q = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e, (cl_letters X Y i d).2]; exact hqi)
  rwa [e] at this

theorem cl_T12 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 2) q = false) (hqi : i + 2 ≤ q) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vc (X.length + 1) q = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e, (cl_letters X Y i d).2]; simpa [idx, coarity] using hqi)
  rw [e, (cl_letters X Y i d).2] at this
  simpa [arity, coarity] using this

theorem cl_T13 {s : Slot Vc} (hs : s.1 = (X.length + 2, i)) (hb : bit Vc (X.length + 2) i = false) :
    (next hW s).1 = (X.length + 1, i + 1) :=
  next_σ_left_idx hW (cl_letters X Y i d).2 hs hb

theorem cl_T14 {s : Slot Vc} (hs : s.1 = (X.length + 2, i + 1)) (hb : bit Vc (X.length + 2) (i + 1) = false) :
    (next hW s).1 = (X.length + 1, i) :=
  next_σ_left_succ hW (cl_letters X Y i d).2 hs hb

/-- the traversal from the cusp vertex reaches the exterior (two steps: the rightward arm, then the crossing) -/
theorem cl_reach_v0 {u : Slot Vc} (hu : u.1 = (X.length, 0)) :
    ∃ n, ExtPiece X Pc Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3, B4⟩ := cl_bits X Y i d hW
  have h1 := cl_T10 X Y i d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Vc (X.length + 1) i = true := by rw [B1, hd]
    have h2 := cl_T5 X Y i d hW h1 hb1
    have hb2 : bit Vc (X.length + 2) (i + 1) = true := by rw [B4, hd]
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pc (colOf _)
    rw [block_col_true h2 (by omega) hb2, cl_extCol]; omega
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Vc (X.length + 1) (i + 1) = true := by rw [B2, hd]; rfl
    have h2 := cl_T6 X Y i d hW h1 hb1
    have hb2 : bit Vc (X.length + 2) i = true := by rw [B3, hd]; rfl
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pc (colOf _)
    have hi := cl_i_pos X Y i d hW
    rw [block_col_true h2 (by omega) hb2, cl_extCol]; omega

/-- every component of the crossed-cusp word meets the exterior -/
theorem cl_hexit : ∀ u : Slot Vc, ∃ n, ExtPiece X Pc Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨B1, B2, B3, B4⟩ := cl_bits X Y i d hW
  have hi := cl_i_pos X Y i d hW
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pc (colOf u)
  · exact reach_self hW hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, cl_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact cl_reach_v0 X Y i d hW hu
    · exfalso
      have := vertex_not_crossing hu
      rw [(cl_letters X Y i d).2] at this
      simp [isCrossing] at this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vc k p
  · rw [block_col_false hu hp hb, cl_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, hb1⟩ := cl_T7 X Y i d hW hu hp hb hpi
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, cl_extCol]; omega
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · have h1 := cl_T8 X Y i d hW hu (by omega) hb
        exact reach_of_next hW (cl_reach_v0 X Y i d hW h1)
      · obtain ⟨h1, hb1⟩ := cl_T9 X Y i d hW hu hp hb hpi2
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, cl_extCol]; omega
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, hb1⟩ := cl_T11 X Y i d hW hu hp hb hpi
        obtain ⟨h2, hb2⟩ := cl_T7 X Y i d hW h1 hp hb1 hpi
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, cl_extCol]; omega
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · -- `p = i` or `p = i + 1`: the entry of the crossed cusp
        rcases Nat.eq_or_lt_of_le hpi with rfl | hpi1
        · have h1 := cl_T13 X Y i d hW hu hb
          have hb1 : bit Vc (X.length + 1) (i + 1) = false := by
            rw [B2]; rw [B3] at hb; cases d <;> simp_all
          have h2 := cl_T8 X Y i d hW h1 (Or.inr rfl) hb1
          exact reach_of_next hW (reach_of_next hW (cl_reach_v0 X Y i d hW h2))
        · have hpe : p = i + 1 := by omega
          rw [hpe] at hu hb
          have h1 := cl_T14 X Y i d hW hu hb
          have hb1 : bit Vc (X.length + 1) i = false := by rw [B1]; rw [B4] at hb; exact hb
          have h2 := cl_T8 X Y i d hW h1 (Or.inl rfl) hb1
          exact reach_of_next hW (reach_of_next hW (cl_reach_v0 X Y i d hW h2))
      · obtain ⟨h1, hb1⟩ := cl_T12 X Y i d hW hu hp hb hpi2
        obtain ⟨h2, hb2⟩ := cl_T9 X Y i d hW h1 (by omega) hb1 hpi2
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, cl_extCol]; omega
  · rw [block_col_true hu hp hb, cl_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, hb1⟩ := cl_T1 X Y i d hW hu hp hb hpi
        obtain ⟨h2, hb2⟩ := cl_T3 X Y i d hW h1 hp hb1 hpi
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h2 hp hb2, cl_extCol]; omega
      · obtain ⟨h1, hb1⟩ := cl_T2 X Y i d hW hu hp hb hpi
        obtain ⟨h2, hb2⟩ := cl_T4 X Y i d hW h1 (by omega) hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h2 (by omega) hb2, cl_extCol]; omega
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, hb1⟩ := cl_T3 X Y i d hW hu hp hb hpi
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pc (colOf _)
        rw [block_col_true h1 hp hb1, cl_extCol]; omega
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · rcases Nat.eq_or_lt_of_le hpi with rfl | hpi1
        · have h1 := cl_T5 X Y i d hW hu hb
          have hb1 : bit Vc (X.length + 2) (i + 1) = true := by rw [B4]; rw [B1] at hb; exact hb
          refine reach_of_next hW (reach_self hW ?_)
          show ExtCol X Pc (colOf _)
          rw [block_col_true h1 (by omega) hb1, cl_extCol]; omega
        · have hpe : p = i + 1 := by omega
          rw [hpe] at hu hb
          have h1 := cl_T6 X Y i d hW hu hb
          have hb1 : bit Vc (X.length + 2) i = true := by rw [B3]; rw [B2] at hb; exact hb
          refine reach_of_next hW (reach_self hW ?_)
          show ExtCol X Pc (colOf _)
          rw [block_col_true h1 (by omega) hb1, cl_extCol]; omega
      · obtain ⟨h1, hb1⟩ := cl_T4 X Y i d hW hu hp hb hpi2
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pc (colOf _)
        rw [block_col_true h1 (by omega) hb1, cl_extCol]; omega

theorem cl_sameEffect : SameEffect X Pc Pc' := by
  have hi := cl_i_pos X Y i d hW
  exact sameEffect_of_replace X Pc Y Pc' hW (fun c c' h => run_crossedCusp_l hi h)

end CrossedCuspLeftWord

section CrossedCuspLeftPassage

open U3

variable (X Y : Word) (i : ℕ) (d : Bool) (hW : (X ++ [Letter.l i d, Letter.σ i] ++ Y).Closed)
  (hW' : (X ++ [Letter.l i (!d)] ++ Y).Closed)

local notation "Vc" => X ++ [Letter.l i d, Letter.σ i] ++ Y
local notation "Pc" => [Letter.l i d, Letter.σ i]
local notation "Vc'" => X ++ [Letter.l i (!d)] ++ Y
local notation "Pc'" => [Letter.l i (!d)]

/-- the cut before the block is the same in both words -/
theorem cl_cut_start : cut Vc' X.length = cut Vc X.length := by
  unfold cut
  rw [List.append_assoc, List.take_left' rfl, List.append_assoc, List.take_left' rfl]

include hW in
/-- the cut after the block is the same in both words (`SameEffect`) -/
theorem cl_cut_end : cut Vc' (X.length + 1) = cut Vc (X.length + 2) := by
  have hE := cl_sameEffect X Y i d hW
  unfold cut
  rw [List.take_left' (by simp), List.take_left' (by simp)]
  unfold SameEffect at hE
  rw [hE]

theorem cl_bit_start (p : ℕ) : bit Vc' X.length p = bit Vc X.length p := by
  rw [bit_eq, bit_eq, cl_cut_start]

include hW in
theorem cl_bit_end (p : ℕ) : bit Vc' (X.length + 1) p = bit Vc (X.length + 2) p := by
  rw [bit_eq, bit_eq, cl_cut_end X Y i d hW]

include hW' in
theorem cl'_bits : bit Vc' (X.length + 1) i = !d ∧ bit Vc' (X.length + 1) (i + 1) = d := by
  have hk₀ : X.length < (Vc').length := by rw [cl'_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hW' hk₀ (cl'_letters X Y i d)
  exact ⟨h1, by rw [h2, Bool.not_not]⟩

include hW'

/-! the successor table of the block `l_i (!d)` of `W'` (column `|X|`) -/

theorem cl'_T1 {s : Slot Vc'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc' X.length p = true)
    (hpi : p < i) : (next hW' s).1 = (X.length + 1, p) ∧ bit Vc' (X.length + 1) p = true :=
  next_right_lt hW' hs hp hb (by rw [cl'_letters X Y i d]; exact hpi)

theorem cl'_T2 {s : Slot Vc'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc' X.length p = true)
    (hpi : i ≤ p) : (next hW' s).1 = (X.length + 1, p + 2) ∧ bit Vc' (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW' hs hp hb (by rw [cl'_letters X Y i d]; simpa [idx, arity] using hpi)
  rwa [cl'_letters X Y i d] at this

theorem cl'_T3 {s : Slot Vc'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc' (X.length + 1) q = false) (hqi : q < i) :
    (next hW' s).1 = (X.length, q) ∧ bit Vc' X.length q = false := by
  have := next_left_lt hW' hs hq hb (by rw [Nat.add_sub_cancel, cl'_letters X Y i d]; exact hqi)
  rwa [Nat.add_sub_cancel] at this

theorem cl'_T4 {s : Slot Vc'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = i ∨ q = i + 1)
    (hb : bit Vc' (X.length + 1) q = false) : (next hW' s).1 = (X.length, 0) :=
  next_arm_l hW' (by have := slot_col_lt hW' hs; omega) (cl'_letters X Y i d) hs hq hb

theorem cl'_T5 {s : Slot Vc'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc' (X.length + 1) q = false) (hqi : i + 2 ≤ q) :
    (next hW' s).1 = (X.length, q - 2) ∧ bit Vc' X.length (q - 2) = false := by
  have := next_left_ge hW' hs hq hb (by rw [Nat.add_sub_cancel, cl'_letters X Y i d]; simpa [idx, coarity] using hqi)
  rw [Nat.add_sub_cancel, cl'_letters X Y i d] at this
  simpa [arity, coarity] using this

theorem cl'_T6 {s : Slot Vc'} (hs : s.1 = (X.length, 0)) :
    (next hW' s).1 = (X.length + 1, if !d then i else i + 1) :=
  next_cusp_l hW' (cl'_letters X Y i d) hs

/-- the cusp vertex of `W'` reaches the exterior in one step -/
theorem cl'_reach_v0 {u : Slot Vc'} (hu : u.1 = (X.length, 0)) :
    ∃ n, ExtPiece X Pc' Y ((next hW')^[n] u) := by
  obtain ⟨B1, B2⟩ := cl'_bits X Y i d hW'
  have h1 := cl'_T6 X Y i d hW' hu
  have hi : 1 ≤ i := (l_bits hW' (vertex_lt hu) (cl'_letters X Y i d)).1
  refine reach_of_next hW' (reach_self hW' ?_)
  show ExtCol X Pc' (colOf _)
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Vc' (X.length + 1) (i + 1) = true := by rw [B2, hd]
    rw [block_col_true h1 (by omega) hb1, cl'_extCol]; omega
  · rw [ite_eq_left (by simp [hd])] at h1
    have hb1 : bit Vc' (X.length + 1) i = true := by rw [B1, hd]; rfl
    rw [block_col_true h1 (by omega) hb1, cl'_extCol]; omega

/-- every component of `W'` meets the exterior -/
theorem cl'_hexit : ∀ u : Slot Vc', ∃ n, ExtPiece X Pc' Y ((next hW')^[n] u) := by
  intro u
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pc' (colOf u)
  · exact reach_self hW' hext
  have hi : 1 ≤ i := (l_bits hW' (by rw [cl'_length]; omega) (cl'_letters X Y i d)).1
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, cl'_extCol] at hext
    have : k = X.length := by omega
    subst this
    exact cl'_reach_v0 X Y i d hW' hu
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW' hu hp
  cases hb : bit Vc' k p
  · rw [block_col_false hu hp hb, cl'_extCol] at hext
    have : k = X.length + 1 := by omega
    subst this
    rcases lt_or_ge p i with hpi | hpi
    · obtain ⟨h1, hb1⟩ := cl'_T3 X Y i d hW' hu hp hb hpi
      refine reach_of_next hW' (reach_self hW' ?_)
      show ExtCol X Pc' (colOf _)
      have := (cutSlot_facts hW' h1 hp).2.2.1
      rw [block_col_false h1 hp hb1, cl'_extCol]; omega
    rcases lt_or_ge p (i + 2) with hpi2 | hpi2
    · have h1 := cl'_T4 X Y i d hW' hu (by omega) hb
      exact reach_of_next hW' (cl'_reach_v0 X Y i d hW' h1)
    · obtain ⟨h1, hb1⟩ := cl'_T5 X Y i d hW' hu hp hb hpi2
      refine reach_of_next hW' (reach_self hW' ?_)
      show ExtCol X Pc' (colOf _)
      have := (cutSlot_facts hW' h1 (by omega)).2.2.1
      rw [block_col_false h1 (by omega) hb1, cl'_extCol]; omega
  · rw [block_col_true hu hp hb, cl'_extCol] at hext
    have : k = X.length := by omega
    subst this
    rcases lt_or_ge p i with hpi | hpi
    · obtain ⟨h1, hb1⟩ := cl'_T1 X Y i d hW' hu hp hb hpi
      refine reach_of_next hW' (reach_self hW' ?_)
      show ExtCol X Pc' (colOf _)
      rw [block_col_true h1 hp hb1, cl'_extCol]; omega
    · obtain ⟨h1, hb1⟩ := cl'_T2 X Y i d hW' hu hp hb hpi
      refine reach_of_next hW' (reach_self hW' ?_)
      show ExtCol X Pc' (colOf _)
      rw [block_col_true h1 (by omega) hb1, cl'_extCol]; omega

include hW

/-- THE BLOCK PASSAGE of the crossed cusp: through-strands pass straight, the entering arm exits as the other arm. -/
theorem cl_passage : Passage X Pc Y Pc' hW hW' := by
  obtain ⟨hℓ₀, hℓ₁⟩ := cl_letters X Y i d
  obtain ⟨B1, B2, B3, B4⟩ := cl_bits X Y i d hW
  obtain ⟨B1', B2'⟩ := cl'_bits X Y i d hW'
  have hi := cl_i_pos X Y i d hW
  have hP : Pc ≠ [] := by simp
  have hE := cl_sameEffect X Y i d hW
  have shiftL : ∀ p, extPair X Pc Pc' (X.length, p) = (X.length, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pc Pc' le_rfl]
  have shiftR : ∀ p, extPair X Pc Pc' (X.length + 2, p) = (X.length + 1, p) := by
    intro p; simp only [extPair, cl_shift X i d]
  constructor
  intro b hext hcol
  let b' : Slot Vc' := ⟨extPair X Pc Pc' b.1, isSlot_ext X Pc Y Pc' hP hE b.2 hext⟩
  have hb'v : b'.1 = extPair X Pc Pc' b.1 := rfl
  rcases (entry_iff X Pc Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`: straight through in both words
    have hb'1 : b'.1 = (X.length, p) := by rw [hb'v, hb, shiftL]
    have hbit' : bit Vc' X.length p = true := by rw [cl_bit_start, hbit]
    have hcol0 : ¬ ExtCol X Pc (colOf b) := by rw [block_col_true hb hp hbit, cl_extCol]; omega
    have hcol0' : ¬ ExtCol X Pc' (colOf b') := by rw [block_col_true hb'1 hp hbit', cl'_extCol]; omega
    rcases lt_or_ge p i with hpi | hpi
    · obtain ⟨h1, hb1⟩ := cl_T1 X Y i d hW hb hp hbit hpi
      obtain ⟨h2, hb2⟩ := cl_T3 X Y i d hW h1 hp hb1 hpi
      obtain ⟨h1', hb1'⟩ := cl'_T1 X Y i d hW' hb'1 hp hbit' hpi
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h1 hp hb1, cl_extCol]; omega) (passage_end hW))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h2 hp hb2, cl_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, shiftR]
    · obtain ⟨h1, hb1⟩ := cl_T2 X Y i d hW hb hp hbit hpi
      obtain ⟨h2, hb2⟩ := cl_T4 X Y i d hW h1 (by omega) hb1 (by omega)
      obtain ⟨h1', hb1'⟩ := cl'_T2 X Y i d hW' hb'1 hp hbit' hpi
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h1 (by omega) hb1, cl_extCol]; omega) (passage_end hW))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h2 (by omega) hb2, cl_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, shiftR]
  · -- from the right at `(|X|+2, q)`
    replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Vc (X.length + 2) p = false := hbit
    have hb'1 : b'.1 = (X.length + 1, p) := by rw [hb'v, hb, shiftR]
    have hbit' : bit Vc' (X.length + 1) p = false := by rw [cl_bit_end X Y i d hW, hbit]
    have hcol0 : ¬ ExtCol X Pc (colOf b) := by rw [block_col_false hb hp hbit, cl_extCol]; omega
    have hcol0' : ¬ ExtCol X Pc' (colOf b') := by rw [block_col_false hb'1 hp hbit', cl'_extCol]; omega
    rcases lt_or_ge p i with hpi | hpi
    · obtain ⟨h1, hb1⟩ := cl_T11 X Y i d hW hb hp hbit hpi
      obtain ⟨h2, hb2⟩ := cl_T7 X Y i d hW h1 hp hb1 hpi
      obtain ⟨h1', hb1'⟩ := cl'_T3 X Y i d hW' hb'1 hp hbit' hpi
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 hp hb1, cl_extCol]; omega) (passage_end hW))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0' (passage_end hW')
      have hk2 := (cutSlot_facts hW h2 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h2 hp hb2, cl_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, shiftL]
    rcases lt_or_ge p (i + 2) with hpi2 | hpi2
    · -- the entering arm: `p = i` (then `d = true`) or `p = i + 1` (then `d = false`)
      rcases Nat.eq_or_lt_of_le hpi with hpe | hpi1
      · subst hpe
        have hd : d = true := by rw [B3] at hbit; simpa using hbit
        have h1 := cl_T13 X Y i d hW hb hbit
        have hb1 : bit Vc (X.length + 1) (i + 1) = false := by rw [B2, hd]; rfl
        have h2 := cl_T8 X Y i d hW h1 (Or.inr rfl) hb1
        have h3 := cl_T10 X Y i d hW h2
        rw [ite_eq_left hd] at h3
        have hb3 : bit Vc (X.length + 1) i = true := by rw [B1, hd]
        have h4 := cl_T5 X Y i d hW h3 hb3
        have hb4 : bit Vc (X.length + 2) (i + 1) = true := by rw [B4, hd]
        -- `W'`: `(|X|+1, i)` leftward into the cusp, out at `(|X|+1, i+1)`
        have h1' := cl'_T4 X Y i d hW' hb'1 (Or.inl rfl) hbit'
        have h2' := cl'_T6 X Y i d hW' h1'
        rw [ite_eq_right (by simp [hd])] at h2'
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
          (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 (by omega) hb1, cl_extCol]; omega)
          (passage_step hW (ExtCol X Pc) (by rw [block_col_vertex h2, cl_extCol]; omega)
          (passage_step hW (ExtCol X Pc) (by rw [block_col_true h3 (by omega) hb3, cl_extCol]; omega) (passage_end hW))))
        obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0'
          (passage_step hW' (ExtCol X Pc') (by rw [block_col_vertex h1', cl'_extCol]; omega) (passage_end hW'))
        refine ⟨n, _, hc, by rw [block_col_true h4 (by omega) hb4, cl_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc', h2', h4, shiftR]
      · have hpe : p = i + 1 := by omega
        subst hpe
        have hd : d = false := by rw [B4] at hbit; exact hbit
        have h1 := cl_T14 X Y i d hW hb hbit
        have hb1 : bit Vc (X.length + 1) i = false := by rw [B1, hd]
        have h2 := cl_T8 X Y i d hW h1 (Or.inl rfl) hb1
        have h3 := cl_T10 X Y i d hW h2
        rw [ite_eq_right (by simp [hd])] at h3
        have hb3 : bit Vc (X.length + 1) (i + 1) = true := by rw [B2, hd]; rfl
        have h4 := cl_T6 X Y i d hW h3 hb3
        have hb4 : bit Vc (X.length + 2) i = true := by rw [B3, hd]; rfl
        have h1' := cl'_T4 X Y i d hW' hb'1 (Or.inr rfl) hbit'
        have h2' := cl'_T6 X Y i d hW' h1'
        rw [ite_eq_left (by simp [hd])] at h2'
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
          (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 (by omega) hb1, cl_extCol]; omega)
          (passage_step hW (ExtCol X Pc) (by rw [block_col_vertex h2, cl_extCol]; omega)
          (passage_step hW (ExtCol X Pc) (by rw [block_col_true h3 (by omega) hb3, cl_extCol]; omega) (passage_end hW))))
        obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0'
          (passage_step hW' (ExtCol X Pc') (by rw [block_col_vertex h1', cl'_extCol]; omega) (passage_end hW'))
        refine ⟨n, _, hc, by rw [block_col_true h4 (by omega) hb4, cl_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc', h2', h4, shiftR]
    · obtain ⟨h1, hb1⟩ := cl_T12 X Y i d hW hb hp hbit hpi2
      obtain ⟨h2, hb2⟩ := cl_T9 X Y i d hW h1 (by omega) hb1 hpi2
      obtain ⟨h1', hb1'⟩ := cl'_T5 X Y i d hW' hb'1 hp hbit' hpi2
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 (by omega) hb1, cl_extCol]; omega) (passage_end hW))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0' (passage_end hW')
      have hk2 := (cutSlot_facts hW h2 (by omega)).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h2 (by omega) hb2, cl_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, shiftL]

end CrossedCuspLeftPassage

/-! #### B3. Vertex moves on one cut; non-grid heights -/

section MvTwo

variable (W : Word) (k i : ℕ) (y₁ y₂ : ℝ)

/-- Two cut vertices of cut `k` at positions `i`, `i+1` moved to heights `y₁`, `y₂` (same x), everything else the
realization's grid point (standard placement). -/
def mv2 (u : Slot W) : Plane :=
  if u.1 = (k, i) then ((k : ℝ), y₁) else if u.1 = (k, i + 1) then ((k : ℝ), y₂) else pt .std W u.1

theorem mv2_of_ne {u : Slot W} (h1 : u.1 ≠ (k, i)) (h2 : u.1 ≠ (k, i + 1)) : mv2 W k i y₁ y₂ u = pt .std W u.1 := by
  simp [mv2, h1, h2]

theorem mv2_of_cut_ne {u : Slot W} (h : u.1.1 ≠ k) : mv2 W k i y₁ y₂ u = pt .std W u.1 :=
  mv2_of_ne W k i y₁ y₂ (fun e => h (by rw [e])) (fun e => h (by rw [e]))

theorem mv2_of_pos_ne {u : Slot W} (h1 : u.1.2 ≠ i) (h2 : u.1.2 ≠ i + 1) : mv2 W k i y₁ y₂ u = pt .std W u.1 :=
  mv2_of_ne W k i y₁ y₂ (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))

theorem mv2_fst {u : Slot W} (hu : u.1 = (k, i)) : mv2 W k i y₁ y₂ u = ((k : ℝ), y₁) := by
  simp [mv2, hu]

theorem mv2_snd {u : Slot W} (hu : u.1 = (k, i + 1)) : mv2 W k i y₁ y₂ u = ((k : ℝ), y₂) := by
  simp [mv2, hu]

theorem mv2_xcoord (hi : 1 ≤ i) (u : Slot W) : (mv2 W k i y₁ y₂ u).1 = (pt .std W u.1).1 := by
  by_cases h1 : u.1 = (k, i)
  · rw [mv2_fst W k i y₁ y₂ h1, h1, std_pt_cut _ (by omega)]
  by_cases h2 : u.1 = (k, i + 1)
  · rw [mv2_snd W k i y₁ y₂ h2, h2, std_pt_cut _ (by omega)]
  · rw [mv2_of_ne W k i y₁ y₂ h1 h2]

/-- a height that is neither an integer `−p` nor a half-integer `−m − 1/2`: no grid point has it -/
def NonGrid (y : ℝ) : Prop := (∀ p : ℕ, y ≠ -(p : ℝ)) ∧ (∀ m : ℕ, y ≠ -(m : ℝ) - 1 / 2)

theorem nonGrid_three_quarter (i : ℕ) : NonGrid (-(i : ℝ) - 3 / 4) := by
  constructor
  · intro p h
    have h4 : ((4 * p : ℕ) : ℝ) = ((4 * i + 3 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective (R := ℝ) h4
    omega
  · intro m h
    have h4 : ((4 * m + 2 : ℕ) : ℝ) = ((4 * i + 3 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective (R := ℝ) h4
    omega

theorem nonGrid_quarter (i : ℕ) : NonGrid (-(i : ℝ) - 1 / 4) := by
  constructor
  · intro p h
    have h4 : ((4 * p : ℕ) : ℝ) = ((4 * i + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective (R := ℝ) h4
    omega
  · intro m h
    have h4 : ((4 * m + 2 : ℕ) : ℝ) = ((4 * i + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective (R := ℝ) h4
    omega

/-- a non-grid height is not the height of any grid point -/
theorem NonGrid.ne_pt {y : ℝ} (hy : NonGrid y) (x : ℝ) (s : ℕ × ℕ) : (x, y) ≠ pt .std W s := by
  intro h
  have h2 := congrArg Prod.snd h
  simp only at h2
  by_cases hp : s.2 = 0
  · obtain ⟨a, b⟩ := s
    simp only at hp
    subst hp
    rw [std_pt_cusp] at h2
    exact hy.2 _ h2
  · obtain ⟨a, b⟩ := s
    rw [std_pt_cut _ hp] at h2
    exact hy.1 _ h2

theorem mv2_injective (hy : y₁ ≠ y₂) (hy₁ : NonGrid y₁) (hy₂ : NonGrid y₂) : Function.Injective (mv2 W k i y₁ y₂) := by
  intro u v h
  by_cases hu1 : u.1 = (k, i)
  · rw [mv2_fst W k i y₁ y₂ hu1] at h
    by_cases hv1 : v.1 = (k, i)
    · exact Subtype.ext (hu1.trans hv1.symm)
    by_cases hv2 : v.1 = (k, i + 1)
    · rw [mv2_snd W k i y₁ y₂ hv2] at h
      exact absurd (congrArg Prod.snd h) hy
    · rw [mv2_of_ne W k i y₁ y₂ hv1 hv2] at h
      exact absurd h (hy₁.ne_pt W _ _)
  by_cases hu2 : u.1 = (k, i + 1)
  · rw [mv2_snd W k i y₁ y₂ hu2] at h
    by_cases hv1 : v.1 = (k, i)
    · rw [mv2_fst W k i y₁ y₂ hv1] at h
      exact absurd (congrArg Prod.snd h).symm hy
    by_cases hv2 : v.1 = (k, i + 1)
    · exact Subtype.ext (hu2.trans hv2.symm)
    · rw [mv2_of_ne W k i y₁ y₂ hv1 hv2] at h
      exact absurd h (hy₂.ne_pt W _ _)
  rw [mv2_of_ne W k i y₁ y₂ hu1 hu2] at h
  by_cases hv1 : v.1 = (k, i)
  · rw [mv2_fst W k i y₁ y₂ hv1] at h
    exact absurd h.symm (hy₁.ne_pt W _ _)
  by_cases hv2 : v.1 = (k, i + 1)
  · rw [mv2_snd W k i y₁ y₂ hv2] at h
    exact absurd h.symm (hy₂.ne_pt W _ _)
  · rw [mv2_of_ne W k i y₁ y₂ hv1 hv2] at h
    exact pt_inj _ _ h

end MvTwo

/-! #### B4. The crossed-cusp disc: numeric facts -/

section CcNumeric

/-- unfold membership in the crossed-cusp polygon to five inequalities and close them by `linarith` -/
macro "cc_mem" : tactic => `(tactic| (
  simp only [ccL, mem_polygon_iff, mem_interior_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, or_false, HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle,
    HalfPlane.b_yle, HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith))

variable (k i : ℕ)

theorem cc_int_a : (((k + 1 : ℕ) : ℝ), -(i : ℝ) - 3 / 4) ∈ interior (polygon (ccL k i)) := by push_cast; cc_mem
theorem cc_int_b : (((k + 1 : ℕ) : ℝ), -(i : ℝ) - 1 / 4) ∈ interior (polygon (ccL k i)) := by push_cast; cc_mem
theorem cc_int_i : (((k + 1 : ℕ) : ℝ), -(i : ℝ)) ∈ interior (polygon (ccL k i)) := by push_cast; cc_mem
theorem cc_int_i1 : (((k + 1 : ℕ) : ℝ), -((i + 1 : ℕ) : ℝ)) ∈ interior (polygon (ccL k i)) := by push_cast; cc_mem
theorem cc_int_cusp : ((k : ℝ) + 1 / 2, -(i : ℝ) - 1 / 2) ∈ interior (polygon (ccL k i)) := by cc_mem
theorem cc_mem_ri : (((k + 2 : ℕ) : ℝ), -(i : ℝ)) ∈ polygon (ccL k i) := by push_cast; cc_mem
theorem cc_mem_ri1 : (((k + 2 : ℕ) : ℝ), -((i + 1 : ℕ) : ℝ)) ∈ polygon (ccL k i) := by push_cast; cc_mem

theorem cc_xge_mem : HalfPlane.xge (Placement.std.x k) ∈ ccL k i := by simp [ccL]
theorem cc_xle_mem : HalfPlane.xle (Placement.std.x (k + 2)) ∈ ccL k i := by
  have e : Placement.std.x (k + 2) = (k : ℝ) + 2 := by rw [Placement.std_x]; push_cast; ring
  rw [e]; simp [ccL]

/-- a horizontal spectator above the block (`p < i`), in either block column -/
theorem cc_out_above {p : ℕ} (hp : p < i) (x₀ x₁ : ℝ) : SegOut (ccL k i) (x₀, -(p : ℝ)) (x₁, -(p : ℝ)) := by
  have hp' : (p : ℝ) + 1 ≤ i := by exact_mod_cast hp
  refine segOut_of_lt (HalfPlane.yle (-(i : ℝ) + 1 / 2)) (by simp [ccL]) ?_ ?_ <;>
    simp only [HalfPlane.f_yle, HalfPlane.b_yle] <;> linarith

/-- a horizontal spectator below the block in the crossing column (`i + 2 ≤ p`) -/
theorem cc_out_below {p : ℕ} (hp : i + 2 ≤ p) (x₀ x₁ : ℝ) : SegOut (ccL k i) (x₀, -(p : ℝ)) (x₁, -(p : ℝ)) := by
  have hp' : (i : ℝ) + 2 ≤ p := by exact_mod_cast hp
  refine segOut_of_lt (HalfPlane.yge (-(i : ℝ) - 3 / 2)) (by simp [ccL]) ?_ ?_ <;>
    simp only [HalfPlane.f_yge, HalfPlane.b_yge] <;> linarith

/-- the pushed-down spectator of the cusp column: `pass p (p+2)` with `i ≤ p` -/
theorem cc_out_slant {p : ℕ} (hp : i ≤ p) :
    SegOut (ccL k i) ((k : ℝ), -(p : ℝ)) (((k + 1 : ℕ) : ℝ), -((p + 2 : ℕ) : ℝ)) := by
  have hp' : (i : ℝ) ≤ p := by exact_mod_cast hp
  refine segOut_of_lt (HalfPlane.above (-(i : ℝ) + 1 / 4 + 2 * k) (-2)) (by simp [ccL]) ?_ ?_ <;>
    simp only [HalfPlane.f_above, HalfPlane.b_above] <;> push_cast <;> linarith

/-- a cut point of the standard grid inside the crossed-cusp polygon lies at cut `k+1` or `k+2`, position `i` or `i+1` -/
theorem cc_mem_cut {j p : ℕ} (h : ((j : ℝ), -(p : ℝ)) ∈ polygon (ccL k i)) : (j = k + 1 ∨ j = k + 2) ∧ (p = i ∨ p = i + 1) := by
  simp only [ccL, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e1 : k ≤ j := by exact_mod_cast (by linarith : (k : ℝ) ≤ j)
  have e2 : j ≤ k + 2 := by exact_mod_cast (by linarith : (j : ℝ) ≤ k + 2)
  have e3 : 2 * i ≤ 2 * p + 1 := by exact_mod_cast (by linarith : (2 * i : ℝ) ≤ 2 * p + 1)
  have e4 : 2 * p ≤ 2 * i + 3 := by exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 2 * i + 3)
  have e5 : 4 * p + 1 + 8 * k ≤ 4 * i + 8 * j := by
    exact_mod_cast (by linarith : (4 * p + 1 + 8 * k : ℝ) ≤ 4 * i + 8 * j)
  omega

/-- a cusp vertex of the standard grid inside the crossed-cusp polygon lies in column `k` or `k+1` -/
theorem cc_mem_cusp {j : ℕ} (y : ℝ) (h : ((j : ℝ) + 1 / 2, y) ∈ polygon (ccL k i)) : j = k ∨ j = k + 1 := by
  simp only [ccL, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at h
  obtain ⟨h1, h2, -, -, -⟩ := h
  have e1 : 2 * k ≤ 2 * j + 1 := by exact_mod_cast (by linarith : (2 * k : ℝ) ≤ 2 * j + 1)
  have e2 : 2 * j + 1 ≤ 2 * k + 4 := by exact_mod_cast (by linarith : (2 * j + 1 : ℝ) ≤ 2 * k + 4)
  omega

end CcNumeric

/-! #### B5. The crossed cusp, left variant: the chain and the moved vertices -/

section SigmaSlotVal

variable {W : Word} (hW : W.Closed)

theorem σSlotA_val {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    (σSlotA hW hk hℓ).1 = if bit W k m then (k, m) else (k + 1, m + 1) := by
  unfold σSlotA; split_ifs <;> rfl

theorem σSlotB_val {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    (σSlotB hW hk hℓ).1 = if bit W k (m + 1) then (k, m + 1) else (k + 1, m) := by
  unfold σSlotB; split_ifs <;> rfl

end SigmaSlotVal

/-- the position of the rightward arm of `l_i d` at the cut after it -/
def posA : ℕ → Bool → ℕ
  | i, true => i
  | i, false => i + 1

/-- the position of the leftward arm of `l_i d` at the cut after it -/
def posB : ℕ → Bool → ℕ
  | i, true => i + 1
  | i, false => i

theorem posA_true (i : ℕ) : posA i true = i := rfl
theorem posA_false (i : ℕ) : posA i false = i + 1 := rfl
theorem posB_true (i : ℕ) : posB i true = i + 1 := rfl
theorem posB_false (i : ℕ) : posB i false = i := rfl

theorem posA_eq_ite (i : ℕ) (d : Bool) : posA i d = if d then i else i + 1 := by cases d <;> rfl
theorem posB_eq_ite (i : ℕ) (d : Bool) : posB i d = if d then i + 1 else i := by cases d <;> rfl
theorem posA_mem (i : ℕ) (d : Bool) : posA i d = i ∨ posA i d = i + 1 := by cases d <;> simp [posA]
theorem posB_mem (i : ℕ) (d : Bool) : posB i d = i ∨ posB i d = i + 1 := by cases d <;> simp [posB]
theorem posA_ne_posB (i : ℕ) (d : Bool) : posA i d ≠ posB i d := by cases d <;> simp [posA, posB]
theorem posA_le (i : ℕ) (d : Bool) : i ≤ posA i d ∧ posA i d ≤ i + 1 := by cases d <;> simp [posA]
theorem posB_le (i : ℕ) (d : Bool) : i ≤ posB i d ∧ posB i d ≤ i + 1 := by cases d <;> simp [posB]

section CrossedCuspLeftChain

open U3

variable (X Y : Word) (i : ℕ) (d : Bool) (hW : (X ++ [Letter.l i d, Letter.σ i] ++ Y).Closed)

local notation "Vc" => X ++ [Letter.l i d, Letter.σ i] ++ Y
local notation "Pc" => [Letter.l i d, Letter.σ i]
local notation "Vc'" => X ++ [Letter.l i (!d)] ++ Y
local notation "Pc'" => [Letter.l i (!d)]

/-- the moved vertices: the two arm ends at cut `|X|+1` exchanged (heights `−i−3/4`, `−i−1/4`) -/
def clMv : Slot Vc → Plane := mv2 Vc (X.length + 1) i (-(i : ℝ) - 3 / 4) (-(i : ℝ) - 1 / 4)

theorem clMv_apply (u : Slot Vc) : clMv X Y i d u = mv2 Vc (X.length + 1) i (-(i : ℝ) - 3 / 4) (-(i : ℝ) - 1 / 4) u := rfl

include hW

theorem cl_bitA1 : bit Vc (X.length + 1) (posA i d) = true := by
  obtain ⟨B1, B2, -, -⟩ := cl_bits X Y i d hW
  cases d
  · rw [posA_false, B2]; rfl
  · rw [posA_true, B1]

theorem cl_bitB1 : bit Vc (X.length + 1) (posB i d) = false := by
  obtain ⟨B1, B2, -, -⟩ := cl_bits X Y i d hW
  cases d
  · rw [posB_false, B1]
  · rw [posB_true, B2]; rfl

theorem cl_bitA2 : bit Vc (X.length + 2) (posA i d) = false := by
  obtain ⟨-, -, B3, B4⟩ := cl_bits X Y i d hW
  cases d
  · rw [posA_false, B4]
  · rw [posA_true, B3]; rfl

theorem cl_bitB2 : bit Vc (X.length + 2) (posB i d) = true := by
  obtain ⟨-, -, B3, B4⟩ := cl_bits X Y i d hW
  cases d
  · rw [posB_false, B3]; rfl
  · rw [posB_true, B4]

theorem cl_isSlot_u0 : IsSlot Vc (X.length + 2, posA i d) := by
  obtain ⟨h1, h2⟩ := cl_cutlen X Y i d hW
  have := posA_le i d
  have hi := cl_i_pos X Y i d hW
  exact isSlot_cut (by omega) (by rw [h2]; omega) (by rw [cl_length]; omega)

/-- the arc of the crossed cusp in the realization: entry `(|X|+2, posA)` (leftward), four pieces -/
def clChain : Chain Vc := ⟨⟨(X.length + 2, posA i d), cl_isSlot_u0 X Y i d hW⟩, 4, by norm_num⟩

theorem cl_s0 : ((clChain X Y i d hW).slot hW 0).1 = (X.length + 2, posA i d) := rfl

theorem cl_s1 : ((clChain X Y i d hW).slot hW 1).1 = (X.length + 1, posB i d) := by
  rw [Chain.slot_succ]
  have hb := cl_bitA2 X Y i d hW
  cases d
  · rw [posA_false] at hb; rw [posB_false]
    exact cl_T14 X Y i false hW (cl_s0 X Y i false hW) hb
  · rw [posA_true] at hb; rw [posB_true]
    exact cl_T13 X Y i true hW (cl_s0 X Y i true hW) hb

theorem cl_s2 : ((clChain X Y i d hW).slot hW 2).1 = (X.length, 0) := by
  rw [Chain.slot_succ]
  exact cl_T8 X Y i d hW (cl_s1 X Y i d hW) (posB_mem i d) (cl_bitB1 X Y i d hW)

theorem cl_s3 : ((clChain X Y i d hW).slot hW 3).1 = (X.length + 1, posA i d) := by
  rw [Chain.slot_succ, posA_eq_ite]
  exact cl_T10 X Y i d hW (cl_s2 X Y i d hW)

theorem cl_s4 : ((clChain X Y i d hW).slot hW 4).1 = (X.length + 2, posB i d) := by
  rw [Chain.slot_succ]
  have hb := cl_bitA1 X Y i d hW
  cases d
  · rw [posA_false] at hb; rw [posB_false]
    exact cl_T6 X Y i false hW (cl_s3 X Y i false hW) hb
  · rw [posA_true] at hb; rw [posB_true]
    exact cl_T5 X Y i true hW (cl_s3 X Y i true hW) hb

/-- the height of the moved leftward-arm end: `−i−1/4` if `d` (position `i+1`), `−i−3/4` otherwise -/
def hB : ℕ → Bool → ℝ
  | i, true => -(i : ℝ) - 1 / 4
  | i, false => -(i : ℝ) - 3 / 4

/-- the height of the moved rightward-arm end -/
def hA : ℕ → Bool → ℝ
  | i, true => -(i : ℝ) - 3 / 4
  | i, false => -(i : ℝ) - 1 / 4

theorem cl_mv0 : clMv X Y i d ((clChain X Y i d hW).slot hW 0) = (((X.length + 2 : ℕ) : ℝ), -((posA i d : ℕ) : ℝ)) := by
  rw [clMv_apply, mv2_of_cut_ne _ _ _ _ _ (by rw [cl_s0]; omega), cl_s0, std_pt_cut _ (by have := posA_le i d; have := cl_i_pos X Y i d hW; omega)]

theorem cl_mv1 : clMv X Y i d ((clChain X Y i d hW).slot hW 1) = (((X.length + 1 : ℕ) : ℝ), hB i d) := by
  have h := cl_s1 X Y i d hW
  rw [clMv_apply]
  cases d
  · rw [posB_false] at h; rw [mv2_fst _ _ _ _ _ h]; rfl
  · rw [posB_true] at h; rw [mv2_snd _ _ _ _ _ h]; rfl

theorem cl_mv2 : clMv X Y i d ((clChain X Y i d hW).slot hW 2) = ((X.length : ℝ) + 1 / 2, -(i : ℝ) - 1 / 2) := by
  rw [clMv_apply, mv2_of_cut_ne _ _ _ _ _ (by rw [cl_s2]; omega), cl_s2, std_pt_cusp, (cl_letters X Y i d).1]; rfl

theorem cl_mv3 : clMv X Y i d ((clChain X Y i d hW).slot hW 3) = (((X.length + 1 : ℕ) : ℝ), hA i d) := by
  have h := cl_s3 X Y i d hW
  rw [clMv_apply]
  cases d
  · rw [posA_false] at h; rw [mv2_snd _ _ _ _ _ h]; rfl
  · rw [posA_true] at h; rw [mv2_fst _ _ _ _ _ h]; rfl

theorem cl_mv4 : clMv X Y i d ((clChain X Y i d hW).slot hW 4) = (((X.length + 2 : ℕ) : ℝ), -((posB i d : ℕ) : ℝ)) := by
  rw [clMv_apply, mv2_of_cut_ne _ _ _ _ _ (by rw [cl_s4]; omega), cl_s4, std_pt_cut _ (by have := posB_le i d; have := cl_i_pos X Y i d hW; omega)]

theorem cl_pt0 : pt .std Vc ((clChain X Y i d hW).slot hW 0).1 = (((X.length + 2 : ℕ) : ℝ), -((posA i d : ℕ) : ℝ)) := by
  rw [cl_s0, std_pt_cut _ (by have := posA_le i d; have := cl_i_pos X Y i d hW; omega)]

theorem cl_pt1 : pt .std Vc ((clChain X Y i d hW).slot hW 1).1 = (((X.length + 1 : ℕ) : ℝ), -((posB i d : ℕ) : ℝ)) := by
  rw [cl_s1, std_pt_cut _ (by have := posB_le i d; have := cl_i_pos X Y i d hW; omega)]

theorem cl_pt2 : pt .std Vc ((clChain X Y i d hW).slot hW 2).1 = ((X.length : ℝ) + 1 / 2, -(i : ℝ) - 1 / 2) := by
  rw [cl_s2, std_pt_cusp, (cl_letters X Y i d).1]; rfl

theorem cl_pt3 : pt .std Vc ((clChain X Y i d hW).slot hW 3).1 = (((X.length + 1 : ℕ) : ℝ), -((posA i d : ℕ) : ℝ)) := by
  rw [cl_s3, std_pt_cut _ (by have := posA_le i d; have := cl_i_pos X Y i d hW; omega)]

theorem cl_pt4 : pt .std Vc ((clChain X Y i d hW).slot hW 4).1 = (((X.length + 2 : ℕ) : ℝ), -((posB i d : ℕ) : ℝ)) := by
  rw [cl_s4, std_pt_cut _ (by have := posB_le i d; have := cl_i_pos X Y i d hW; omega)]

end CrossedCuspLeftChain

/-! #### B6. The crossed cusp, left variant: the specification and the leaf case -/

section CrossedCuspLeftSpec

open U3

variable (X Y : Word) (i : ℕ) (d : Bool) (hW : (X ++ [Letter.l i d, Letter.σ i] ++ Y).Closed)

local notation "Vc" => X ++ [Letter.l i d, Letter.σ i] ++ Y
local notation "Pc" => [Letter.l i d, Letter.σ i]
local notation "Vc'" => X ++ [Letter.l i (!d)] ++ Y
local notation "Pc'" => [Letter.l i (!d)]

include hW

/-- the exterior slots are unmoved -/
theorem cl_hmv : ∀ v : Slot Vc, ExtSl X.length (X.length + 2) v.1 → clMv X Y i d v = pt .std Vc v.1 := by
  intro v hv
  have hi := cl_i_pos X Y i d hW
  rw [clMv_apply]
  unfold ExtSl at hv
  split_ifs at hv with h0
  · exact mv2_of_pos_ne _ _ _ _ _ (by omega) (by omega)
  · exact mv2_of_cut_ne _ _ _ _ _ (by omega)

omit hW in
/-- the only crossing letter of the block is the `σ_i` of column `|X|+1` -/
theorem cl_σcol {k' m : ℕ} (hℓ : letterAt Vc k' = .σ m) (hext : ¬ ExtCol X Pc k') :
    k' = X.length + 1 ∧ i = m := by
  rw [cl_extCol] at hext
  have : k' = X.length ∨ k' = X.length + 1 := by omega
  rcases this with rfl | rfl
  · rw [(cl_letters X Y i d).1] at hℓ; cases hℓ
  · rw [(cl_letters X Y i d).2] at hℓ
    exact ⟨rfl, Letter.σ.inj hℓ⟩

/-- the over strand of the block crossing is a chain piece -/
theorem cl_σA_chain {m : ℕ} (hk : X.length + 1 < (Vc).length) (hℓ : letterAt Vc (X.length + 1) = .σ m) :
    ∃ j, j < 4 ∧ (clChain X Y i d hW).slot hW j = σSlotA hW hk hℓ := by
  have hm : i = m := by rw [(cl_letters X Y i d).2] at hℓ; exact Letter.σ.inj hℓ
  subst hm
  have hv := σSlotA_val hW hk hℓ
  obtain ⟨B1, -, -, -⟩ := cl_bits X Y i d hW
  rw [B1] at hv
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte] at hv
    exact ⟨0, by norm_num, Subtype.ext ((cl_s0 X Y i false hW).trans hv.symm)⟩
  · simp only [↓reduceIte] at hv
    exact ⟨3, by norm_num, Subtype.ext ((cl_s3 X Y i true hW).trans hv.symm)⟩

theorem cl_hK : ∀ (k' m : ℕ) (hk : k' < (Vc).length) (hℓ : letterAt Vc k' = .σ m),
    ExtCol X Pc k' ↔ Unch .std hW (clMv X Y i d) (σSlotA hW hk hℓ) ∧ Unch .std hW (clMv X Y i d) (σSlotB hW hk hℓ) := by
  intro k' m hk hℓ
  constructor
  · intro hext
    have hext' := (cl_extCol X i d k').1 hext
    exact ⟨unch_of_extCol .std hW _ (cl_hmv X Y i d hW) (by rw [(σSlotA_spec hW hk hℓ).1]; exact hext'),
      unch_of_extCol .std hW _ (cl_hmv X Y i d hW) (by rw [(σSlotB_spec hW hk hℓ).1]; exact hext')⟩
  · rintro ⟨hA, -⟩
    by_contra hext
    obtain ⟨rfl, rfl⟩ := cl_σcol X Y i d hℓ hext
    have hv := σSlotA_val hW hk hℓ
    obtain ⟨B1, -, -, B4⟩ := cl_bits X Y i d hW
    rw [B1] at hv
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      have h2 := hA.2
      rw [cl_T14 X Y i false hW hv B4, clMv_apply, mv2_fst _ _ _ _ _ (cl_T14 X Y i false hW hv B4)] at h2
      exact (nonGrid_three_quarter i).ne_pt _ _ _ h2
    · simp only [↓reduceIte] at hv
      have h1 := hA.1
      rw [clMv_apply, mv2_fst _ _ _ _ _ hv] at h1
      exact (nonGrid_three_quarter i).ne_pt _ _ _ h1

/-- membership facts of the five chain vertices -/
theorem cl_mem0 : clMv X Y i d ((clChain X Y i d hW).slot hW 0) ∈ polygon (ccL X.length i) ∧
    pt .std Vc ((clChain X Y i d hW).slot hW 0).1 ∈ polygon (ccL X.length i) := by
  rw [cl_mv0, cl_pt0]
  cases d
  · exact ⟨cc_mem_ri1 _ _, cc_mem_ri1 _ _⟩
  · exact ⟨cc_mem_ri _ _, cc_mem_ri _ _⟩

theorem cl_int1 : clMv X Y i d ((clChain X Y i d hW).slot hW 1) ∈ interior (polygon (ccL X.length i)) ∧
    pt .std Vc ((clChain X Y i d hW).slot hW 1).1 ∈ interior (polygon (ccL X.length i)) := by
  rw [cl_mv1, cl_pt1]
  cases d
  · exact ⟨cc_int_a _ _, cc_int_i _ _⟩
  · exact ⟨cc_int_b _ _, cc_int_i1 _ _⟩

theorem cl_int2 : clMv X Y i d ((clChain X Y i d hW).slot hW 2) ∈ interior (polygon (ccL X.length i)) ∧
    pt .std Vc ((clChain X Y i d hW).slot hW 2).1 ∈ interior (polygon (ccL X.length i)) := by
  rw [cl_mv2, cl_pt2]
  exact ⟨cc_int_cusp _ _, cc_int_cusp _ _⟩

theorem cl_int3 : clMv X Y i d ((clChain X Y i d hW).slot hW 3) ∈ interior (polygon (ccL X.length i)) ∧
    pt .std Vc ((clChain X Y i d hW).slot hW 3).1 ∈ interior (polygon (ccL X.length i)) := by
  rw [cl_mv3, cl_pt3]
  cases d
  · exact ⟨cc_int_b _ _, cc_int_i1 _ _⟩
  · exact ⟨cc_int_a _ _, cc_int_i _ _⟩

theorem cl_mem4 : clMv X Y i d ((clChain X Y i d hW).slot hW 4) ∈ polygon (ccL X.length i) ∧
    pt .std Vc ((clChain X Y i d hW).slot hW 4).1 ∈ polygon (ccL X.length i) := by
  rw [cl_mv4, cl_pt4]
  cases d
  · exact ⟨cc_mem_ri _ _, cc_mem_ri _ _⟩
  · exact ⟨cc_mem_ri1 _ _, cc_mem_ri1 _ _⟩

theorem cl_chain_in : ∀ j, j < 4 → PieceIn (ccL X.length i) hW (clMv X Y i d) ((clChain X Y i d hW).slot hW j) ∧
    PieceIn (ccL X.length i) hW (ptv .std) ((clChain X Y i d hW).slot hW j) := by
  intro j hj
  interval_cases j
  · have e : next hW ((clChain X Y i d hW).slot hW 0) = (clChain X Y i d hW).slot hW 1 := (Chain.slot_succ hW _ 0).symm
    constructor
    · show SegIn _ (clMv X Y i d _) (clMv X Y i d (next hW _))
      rw [e]; exact segIn_of_interior_right (cl_mem0 X Y i d hW).1 (cl_int1 X Y i d hW).1
    · show SegIn _ (pt .std Vc _) (pt .std Vc (next hW _).1)
      rw [e]; exact segIn_of_interior_right (cl_mem0 X Y i d hW).2 (cl_int1 X Y i d hW).2
  · have e : next hW ((clChain X Y i d hW).slot hW 1) = (clChain X Y i d hW).slot hW 2 := (Chain.slot_succ hW _ 1).symm
    constructor
    · show SegIn _ (clMv X Y i d _) (clMv X Y i d (next hW _))
      rw [e]; exact segIn_of_interior_left (cl_int1 X Y i d hW).1 (interior_subset (cl_int2 X Y i d hW).1)
    · show SegIn _ (pt .std Vc _) (pt .std Vc (next hW _).1)
      rw [e]; exact segIn_of_interior_left (cl_int1 X Y i d hW).2 (interior_subset (cl_int2 X Y i d hW).2)
  · have e : next hW ((clChain X Y i d hW).slot hW 2) = (clChain X Y i d hW).slot hW 3 := (Chain.slot_succ hW _ 2).symm
    constructor
    · show SegIn _ (clMv X Y i d _) (clMv X Y i d (next hW _))
      rw [e]; exact segIn_of_interior_left (cl_int2 X Y i d hW).1 (interior_subset (cl_int3 X Y i d hW).1)
    · show SegIn _ (pt .std Vc _) (pt .std Vc (next hW _).1)
      rw [e]; exact segIn_of_interior_left (cl_int2 X Y i d hW).2 (interior_subset (cl_int3 X Y i d hW).2)
  · have e : next hW ((clChain X Y i d hW).slot hW 3) = (clChain X Y i d hW).slot hW 4 := (Chain.slot_succ hW _ 3).symm
    constructor
    · show SegIn _ (clMv X Y i d _) (clMv X Y i d (next hW _))
      rw [e]; exact segIn_of_interior_left (cl_int3 X Y i d hW).1 (cl_mem4 X Y i d hW).1
    · show SegIn _ (pt .std Vc _) (pt .std Vc (next hW _).1)
      rw [e]; exact segIn_of_interior_left (cl_int3 X Y i d hW).2 (cl_mem4 X Y i d hW).2

theorem cl_vert : ∀ j, 0 < j → j < 4 → clMv X Y i d ((clChain X Y i d hW).slot hW j) ∈ interior (polygon (ccL X.length i)) ∧
    pt .std Vc ((clChain X Y i d hW).slot hW j).1 ∈ interior (polygon (ccL X.length i)) := by
  intro j h0 hj
  interval_cases j
  · exact cl_int1 X Y i d hW
  · exact cl_int2 X Y i d hW
  · exact cl_int3 X Y i d hW

theorem cl_moved : ∀ u : Slot Vc, clMv X Y i d u = pt .std Vc u.1 ∨
    (clMv X Y i d u ∈ interior (polygon (ccL X.length i)) ∧ pt .std Vc u.1 ∈ interior (polygon (ccL X.length i))) := by
  intro u
  have hi := cl_i_pos X Y i d hW
  by_cases h1 : u.1 = (X.length + 1, i)
  · right
    rw [clMv_apply, mv2_fst _ _ _ _ _ h1, h1, std_pt_cut _ (by omega)]
    exact ⟨cc_int_a _ _, cc_int_i _ _⟩
  by_cases h2 : u.1 = (X.length + 1, i + 1)
  · right
    rw [clMv_apply, mv2_snd _ _ _ _ _ h2, h2, std_pt_cut _ (by omega)]
    exact ⟨cc_int_b _ _, cc_int_i1 _ _⟩
  · left
    rw [clMv_apply, mv2_of_ne _ _ _ _ _ h1 h2]

/-- an unchanged spectator piece with an explicit outside witness -/
theorem cl_spec {u : Slot Vc} {j p j' p' : ℕ} (hu : u.1 = (j, p)) (hn : (next hW u).1 = (j', p'))
    (hp : p ≠ 0) (hp' : p' ≠ 0)
    (h1 : j ≠ X.length + 1 ∨ (p ≠ i ∧ p ≠ i + 1)) (h2 : j' ≠ X.length + 1 ∨ (p' ≠ i ∧ p' ≠ i + 1))
    (hout : SegOut (ccL X.length i) ((j : ℝ), -(p : ℝ)) ((j' : ℝ), -(p' : ℝ))) :
    Unch .std hW (clMv X Y i d) u ∧ PieceOut (ccL X.length i) hW (ptv .std) u := by
  constructor
  · constructor
    · rw [clMv_apply]; apply mv2_of_ne <;> rw [hu] <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
    · rw [clMv_apply]; apply mv2_of_ne <;> rw [hn] <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
  · show SegOut _ (pt .std Vc u.1) (pt .std Vc (next hW u).1)
    rw [hu, hn, std_pt_cut _ hp, std_pt_cut _ hp']
    exact hout

/-- THE CLASSIFICATION: every piece is a chain piece or an unchanged outside piece. -/
theorem cl_rest : ∀ u : Slot Vc, (∃ j, j < 4 ∧ (clChain X Y i d hW).slot hW j = u) ∨
    (Unch .std hW (clMv X Y i d) u ∧ PieceOut (ccL X.length i) hW (ptv .std) u) := by
  intro u
  obtain ⟨B1, B2, B3, B4⟩ := cl_bits X Y i d hW
  have hi := cl_i_pos X Y i d hW
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pc (colOf u)
  · right
    have hext' := (cl_extCol X i d _).1 hext
    exact ⟨unch_of_extCol .std hW _ (cl_hmv X Y i d hW) hext',
      pieceOut_of_extCol _ .std hW _ (cc_xge_mem _ _) (cc_xle_mem _ _) (unch_pt _ _ _) hext'⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, cl_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact Or.inl ⟨2, by norm_num, Subtype.ext ((cl_s2 X Y i d hW).trans hu.symm)⟩
    · exfalso
      have := vertex_not_crossing hu
      rw [(cl_letters X Y i d).2] at this
      simp [isCrossing] at this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vc j p
  · rw [block_col_false hu hp hb, cl_extCol] at hext
    have : j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, -⟩ := cl_T7 X Y i d hW hu hp hb hpi
        exact Or.inr (cl_spec X Y i d hW hu h1 hp hp (Or.inr ⟨by omega, by omega⟩) (Or.inl (by omega))
          (cc_out_above _ _ hpi _ _))
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · left
        refine ⟨1, by norm_num, Subtype.ext ((cl_s1 X Y i d hW).trans ?_)⟩
        rw [hu]
        congr 1
        cases d
        · show i = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exact h
          · exfalso; have : p = i + 1 := by omega
            rw [this, B2] at hb; cases hb
        · show i + 1 = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exfalso; rw [← h, B1] at hb; cases hb
          · omega
      · obtain ⟨h1, -⟩ := cl_T9 X Y i d hW hu hp hb hpi2
        have hout := cc_out_slant X.length i (p := p - 2) (by omega)
        rw [show p - 2 + 2 = p by omega] at hout
        exact Or.inr (cl_spec X Y i d hW hu h1 hp (by omega) (Or.inr ⟨by omega, by omega⟩) (Or.inl (by omega))
          hout.symm)
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, -⟩ := cl_T11 X Y i d hW hu hp hb hpi
        exact Or.inr (cl_spec X Y i d hW hu h1 hp hp (Or.inl (by omega)) (Or.inr ⟨by omega, by omega⟩)
          (cc_out_above _ _ hpi _ _))
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · left
        refine ⟨0, by norm_num, Subtype.ext ((cl_s0 X Y i d hW).trans ?_)⟩
        rw [hu]
        congr 1
        cases d
        · show i + 1 = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exfalso; rw [← h, B3] at hb; cases hb
          · omega
        · show i = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exact h
          · exfalso; have : p = i + 1 := by omega
            rw [this, B4] at hb; cases hb
      · obtain ⟨h1, -⟩ := cl_T12 X Y i d hW hu hp hb hpi2
        exact Or.inr (cl_spec X Y i d hW hu h1 hp hp (Or.inl (by omega)) (Or.inr ⟨by omega, by omega⟩)
          (cc_out_below _ _ hpi2 _ _))
  · rw [block_col_true hu hp hb, cl_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, -⟩ := cl_T1 X Y i d hW hu hp hb hpi
        exact Or.inr (cl_spec X Y i d hW hu h1 hp hp (Or.inl (by omega)) (Or.inr ⟨by omega, by omega⟩)
          (cc_out_above _ _ hpi _ _))
      · obtain ⟨h1, -⟩ := cl_T2 X Y i d hW hu hp hb hpi
        exact Or.inr (cl_spec X Y i d hW hu h1 hp (by omega) (Or.inl (by omega)) (Or.inr ⟨by omega, by omega⟩)
          (cc_out_slant _ _ hpi))
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, -⟩ := cl_T3 X Y i d hW hu hp hb hpi
        exact Or.inr (cl_spec X Y i d hW hu h1 hp hp (Or.inr ⟨by omega, by omega⟩) (Or.inl (by omega))
          (cc_out_above _ _ hpi _ _))
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · left
        refine ⟨3, by norm_num, Subtype.ext ((cl_s3 X Y i d hW).trans ?_)⟩
        rw [hu]
        congr 1
        cases d
        · show i + 1 = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exfalso; rw [← h, B1] at hb; cases hb
          · omega
        · show i = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exact h
          · exfalso; have : p = i + 1 := by omega
            rw [this, B2] at hb; cases hb
      · obtain ⟨h1, -⟩ := cl_T4 X Y i d hW hu hp hb hpi2
        exact Or.inr (cl_spec X Y i d hW hu h1 hp hp (Or.inr ⟨by omega, by omega⟩) (Or.inl (by omega))
          (cc_out_below _ _ hpi2 _ _))

end CrossedCuspLeftSpec

/-! #### B7. The crossed cusp, left variant: the remaining specification fields and the leaf case -/

section CrossedCuspLeftFinal

open U3

variable (X Y : Word) (i : ℕ) (d : Bool) (hW : (X ++ [Letter.l i d, Letter.σ i] ++ Y).Closed)

local notation "Vc" => X ++ [Letter.l i d, Letter.σ i] ++ Y
local notation "Pc" => [Letter.l i d, Letter.σ i]
local notation "Vc'" => X ++ [Letter.l i (!d)] ++ Y
local notation "Pc'" => [Letter.l i (!d)]

include hW

/-- the five chain vertices are pairwise distinct slots -/
theorem cl_slot_ne : ∀ j j', j < 5 → j' < 5 → j ≠ j' → (clChain X Y i d hW).slot hW j ≠ (clChain X Y i d hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  have hab := posA_ne_posB i d
  interval_cases j <;> interval_cases j' <;> first | exact absurd rfl hne | (
    simp only [cl_s0, cl_s1, cl_s2, cl_s3, cl_s4, Prod.mk.injEq] at h'; omega)

theorem cl_prevOut : Unch .std hW (clMv X Y i d) (prev hW (clChain X Y i d hW).u₀) ∧
    PieceOut (ccL X.length i) hW (ptv .std) (prev hW (clChain X Y i d hW).u₀) := by
  rcases cl_rest X Y i d hW (prev hW (clChain X Y i d hW).u₀) with ⟨j, hj, hjs⟩ | h
  · exfalso
    have : (clChain X Y i d hW).slot hW (j + 1) = (clChain X Y i d hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact cl_slot_ne X Y i d hW (j + 1) 0 (by omega) (by omega) (by omega) this
  · exact h

theorem cl_stopOut : Unch .std hW (clMv X Y i d) ((clChain X Y i d hW).slot hW 4) ∧
    PieceOut (ccL X.length i) hW (ptv .std) ((clChain X Y i d hW).slot hW 4) := by
  rcases cl_rest X Y i d hW ((clChain X Y i d hW).slot hW 4) with ⟨j, hj, hjs⟩ | h
  · exact absurd hjs (cl_slot_ne X Y i d hW j 4 (by omega) (by omega) (by omega))
  · exact h

theorem cl_touch : ∀ u : Slot Vc, PieceOut (ccL X.length i) hW (ptv .std) u → pt .std Vc u.1 ∈ polygon (ccL X.length i) →
    u = (clChain X Y i d hW).slot hW 4 := by
  intro u hout hmem
  have hi := cl_i_pos X Y i d hW
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu] at hmem
  have hchain : ∀ j', j' < 4 → u ≠ (clChain X Y i d hW).slot hW j' := by
    intro j' hj' he
    rw [he] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (cl_chain_in X Y i d hW j' hj').2
  by_cases hp : p = 0
  · subst hp
    rw [std_pt_cusp] at hmem
    rcases cc_mem_cusp X.length i _ hmem with rfl | rfl
    · exact absurd (Subtype.ext (hu.trans (cl_s2 X Y i d hW).symm)) (hchain 2 (by norm_num))
    · exfalso
      have := vertex_not_crossing hu
      rw [(cl_letters X Y i d).2] at this
      simp [isCrossing] at this
  · rw [std_pt_cut _ hp] at hmem
    obtain ⟨hj, hp'⟩ := cc_mem_cut X.length i hmem
    have hpos : p = posA i d ∨ p = posB i d := by cases d <;> simp only [posA, posB] <;> omega
    rcases hj with rfl | rfl
    · rcases hpos with rfl | rfl
      · exact absurd (Subtype.ext (hu.trans (cl_s3 X Y i d hW).symm)) (hchain 3 (by norm_num))
      · exact absurd (Subtype.ext (hu.trans (cl_s1 X Y i d hW).symm)) (hchain 1 (by norm_num))
    · rcases hpos with rfl | rfl
      · exact absurd (Subtype.ext (hu.trans (cl_s0 X Y i d hW).symm)) (hchain 0 (by norm_num))
      · exact Subtype.ext (hu.trans (cl_s4 X Y i d hW).symm)

theorem cl_exits : ∀ u : Slot Vc, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch .std hW (clMv X Y i d) v ∧
    PieceOut (ccL X.length i) hW (ptv .std) v := by
  intro u
  have hno : ∀ k', X.length ≤ k' → k' < X.length + 2 → ∀ m, letterAt Vc k' ≠ .r m := by
    intro k' h1 h2 m
    have : k' = X.length ∨ k' = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rw [(cl_letters X Y i d).1]; exact fun h => by cases h
    · rw [(cl_letters X Y i d).2]; exact fun h => by cases h
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_r hW X.length (X.length + 2) hno u
  exact ⟨v, hsc, unch_of_extCol .std hW _ (cl_hmv X Y i d hW) hcol,
    pieceOut_of_extCol _ .std hW _ (cc_xge_mem _ _) (cc_xle_mem _ _) (unch_pt _ _ _) hcol⟩

omit hW in
theorem cl_kink : ∃ (k₀ m₀ : ℕ) (_hk₀ : k₀ < (Vc).length) (_hℓ₀ : letterAt Vc k₀ = .σ m₀), ¬ ExtCol X Pc k₀ ∧
    ∀ (k m : ℕ) (_hk : k < (Vc).length) (_hℓ : letterAt Vc k = .σ m), ¬ ExtCol X Pc k → k = k₀ :=
  ⟨X.length + 1, i, by rw [cl_length]; omega, (cl_letters X Y i d).2, by rw [cl_extCol]; omega,
    fun k m _ hℓ hext => (cl_σcol X Y i d hℓ hext).1⟩

theorem cl_hKout : ∀ (k' m : ℕ) (hk : k' < (Vc).length) (hℓ : letterAt Vc k' = .σ m),
    ExtCol X Pc k' ↔ PieceOut (ccL X.length i) hW (ptv .std) (σSlotA hW hk hℓ) := by
  intro k' m hk hℓ
  constructor
  · intro hext
    exact pieceOut_of_extCol _ .std hW _ (cc_xge_mem _ _) (cc_xle_mem _ _) (unch_pt _ _ _)
      (by rw [(σSlotA_spec hW hk hℓ).1]; exact (cl_extCol X i d k').1 hext)
  · intro hout
    by_contra hext
    obtain ⟨rfl, rfl⟩ := cl_σcol X Y i d hℓ hext
    obtain ⟨j, hj, hjs⟩ := cl_σA_chain X Y i d hW hk hℓ
    rw [← hjs] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (cl_chain_in X Y i d hW j hj).2

theorem cl_col0 : colOf ((clChain X Y i d hW).slot hW 0) = X.length + 1 := by
  have hi := cl_i_pos X Y i d hW
  have := posA_le i d
  rw [block_col_false (cl_s0 X Y i d hW) (by omega) (cl_bitA2 X Y i d hW)]; omega

theorem cl_col1 : colOf ((clChain X Y i d hW).slot hW 1) = X.length := by
  have hi := cl_i_pos X Y i d hW
  have := posB_le i d
  rw [block_col_false (cl_s1 X Y i d hW) (by omega) (cl_bitB1 X Y i d hW)]; omega

theorem cl_col2 : colOf ((clChain X Y i d hW).slot hW 2) = X.length := block_col_vertex (cl_s2 X Y i d hW)

theorem cl_col3 : colOf ((clChain X Y i d hW).slot hW 3) = X.length + 1 := by
  have hi := cl_i_pos X Y i d hW
  have := posA_le i d
  rw [block_col_true (cl_s3 X Y i d hW) (by omega) (cl_bitA1 X Y i d hW)]

/-- the two arms meet only at the cusp vertex -/
theorem cl_meet12 : MeetSpec .std hW (clMv X Y i d) (ExtCol X Pc) ((clChain X Y i d hW).slot hW 1)
    ((clChain X Y i d hW).slot hW 2) := by
  intro τ τ' h0 h1 h0' h1' he
  have e1 : next hW ((clChain X Y i d hW).slot hW 1) = (clChain X Y i d hW).slot hW 2 := (Chain.slot_succ hW _ 1).symm
  have e2 : next hW ((clChain X Y i d hW).slot hW 2) = (clChain X Y i d hW).slot hW 3 := (Chain.slot_succ hW _ 2).symm
  rw [e1, e2, cl_mv1, cl_mv2, cl_mv3] at he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy
  refine Or.inr (Or.inl ⟨e1.symm, ?_, ?_⟩)
  · cases d <;> simp only [hA, hB] at hy <;> linarith
  · cases d <;> simp only [hA, hB] at hy <;> linarith

/-- the two crossing pieces of the moved diagram do not meet -/
theorem cl_meet03 : MeetSpec .std hW (clMv X Y i d) (ExtCol X Pc) ((clChain X Y i d hW).slot hW 0)
    ((clChain X Y i d hW).slot hW 3) := by
  intro τ τ' h0 h1 h0' h1' he
  have e1 : next hW ((clChain X Y i d hW).slot hW 0) = (clChain X Y i d hW).slot hW 1 := (Chain.slot_succ hW _ 0).symm
  have e2 : next hW ((clChain X Y i d hW).slot hW 3) = (clChain X Y i d hW).slot hW 4 := (Chain.slot_succ hW _ 3).symm
  rw [e1, e2, cl_mv0, cl_mv1, cl_mv3, cl_mv4] at he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy
  exfalso
  cases d <;> simp only [hA, hB, posA, posB] at hx hy <;> push_cast at hx hy <;> linarith

theorem cl_pairs : ∀ j j', j < 4 → j' < 4 → (clChain X Y i d hW).slot hW j ≠ (clChain X Y i d hW).slot hW j' →
    colOf ((clChain X Y i d hW).slot hW j) = colOf ((clChain X Y i d hW).slot hW j') →
    MeetSpec .std hW (clMv X Y i d) (ExtCol X Pc) ((clChain X Y i d hW).slot hW j) ((clChain X Y i d hW).slot hW j') := by
  intro j j' hj hj' hne hc
  have c0 := cl_col0 X Y i d hW
  have c1 := cl_col1 X Y i d hW
  have c2 := cl_col2 X Y i d hW
  have c3 := cl_col3 X Y i d hW
  interval_cases j <;> interval_cases j'
  · exact absurd rfl hne
  · rw [c0, c1] at hc; omega
  · rw [c0, c2] at hc; omega
  · exact cl_meet03 X Y i d hW
  · rw [c1, c0] at hc; omega
  · exact absurd rfl hne
  · exact cl_meet12 X Y i d hW
  · rw [c1, c3] at hc; omega
  · rw [c2, c0] at hc; omega
  · exact (cl_meet12 X Y i d hW).symm
  · exact absurd rfl hne
  · rw [c2, c3] at hc; omega
  · exact (cl_meet03 X Y i d hW).symm
  · rw [c3, c1] at hc; omega
  · rw [c3, c2] at hc; omega
  · exact absurd rfl hne

theorem cl_genericData : GenericData .std hW (clMv X Y i d) (ExtCol X Pc) :=
  genericData_of (ccL X.length i) .std hW (clMv X Y i d) (ExtCol X Pc) (clChain X Y i d hW)
    (mv2_injective _ _ _ _ _ (by norm_num) (nonGrid_three_quarter i) (nonGrid_quarter i))
    (mv2_xcoord _ _ _ _ _ (cl_i_pos X Y i d hW)) (cl_rest X Y i d hW) (fun j hj => (cl_chain_in X Y i d hW j hj).1)
    (cl_pairs X Y i d hW) (fun k m hk hℓ hA hB => (cl_hK X Y i d hW k m hk hℓ).2 ⟨hA, hB⟩)

theorem cl_riSpec : RISpec (ccL X.length i) .std hW (clMv X Y i d) (ExtCol X Pc) (clChain X Y i d hW) where
  disc := ccL_isDisc _ _
  hK := cl_hK X Y i d hW
  hKout := cl_hKout X Y i d hW
  moved := cl_moved X Y i d hW
  chain := cl_chain_in X Y i d hW
  vert := cl_vert X Y i d hW
  rest := cl_rest X Y i d hW
  prevOut := cl_prevOut X Y i d hW
  stopOut := cl_stopOut X Y i d hW
  touch := cl_touch X Y i d hW
  exits := cl_exits X Y i d hW
  kink := cl_kink X Y i d

theorem cl_riData (hne : Vc ≠ []) :
    Nonempty (RIData (polygon (ccL X.length i)) (mvDiagram .std hW hne (clMv X Y i d) (ExtCol X Pc) (cl_genericData X Y i d hW))
      (rlDiagram .std hW hne)) :=
  riData_of hne (cl_genericData X Y i d hW) (cl_riSpec X Y i d hW)

theorem cl_recordIso (hne : Vc ≠ []) (W' : OWord) (hW'eq : W'.letters = Vc') :
    Nonempty (RecordIso (mvDiagram .std hW hne (clMv X Y i d) (ExtCol X Pc) (cl_genericData X Y i d hW)).record
      (realize W').diagram.record) := by
  have hW' : (Vc').Closed := by have := W'.closed; rwa [hW'eq] at this
  refine ⟨vertexMovedRecordIso' X Pc Y Pc' (by simp) (cl_sameEffect X Y i d hW) hW hW' .std hne _ _ _ _
    (slotDiagramData_of .std hW hne (clMv X Y i d) (ExtCol X Pc) (cl_genericData X Y i d hW) (cl_hK X Y i d hW))
    (cl_passage X Y i d hW hW') (cl_hexit X Y i d hW) (cl'_hexit X Y i d hW') ?_ W' hW'eq (by simp)⟩
  intro k' hk1 hk2
  simp only [List.length_cons, List.length_nil] at hk2
  have : k' = X.length := by omega
  subst this
  rw [cl'_letters X Y i d]; rfl

omit hW in
/-- LEAF CASE (crossed cusp, left variant `l_i d σ_i ↦ l_i (!d)`). -/
theorem crossedCusp_left {W W' : OWord} (hWeq : W.letters = Vc) (hW'eq : W'.letters = Vc') :
    ∃ D : Diagram, RI D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨Wl, hWl⟩ := W
  simp only at hWeq
  subst hWeq
  have hne : Vc ≠ [] := by simp
  rw [realize_eq_realizeAt ⟨_, hWl⟩ hne]
  exact ⟨mvDiagram .std hWl hne (clMv X Y i d) (ExtCol X Pc) (cl_genericData X Y i d hWl),
    ⟨polygon (ccL X.length i), Or.inl (cl_riData X Y i d hWl hne)⟩, cl_recordIso X Y i d hWl hne W' hW'eq⟩

end CrossedCuspLeftFinal

/-! #### C. The crossed-cusp shortcut, right variant `σ_i r_i ↦ r_i` -/

section CrossedCuspRightWord

open U3

variable (X Y : Word) (i : ℕ) (e : Bool) (hW : (X ++ [Letter.σ i, Letter.r i] ++ Y).Closed)
  (he : bit (X ++ [Letter.σ i, Letter.r i] ++ Y) X.length i = e)

local notation "Vr" => X ++ [Letter.σ i, Letter.r i] ++ Y
local notation "Pr" => [Letter.σ i, Letter.r i]
local notation "Vr'" => X ++ [Letter.r i] ++ Y
local notation "Pr'" => [Letter.r i]

theorem cr_letters : letterAt Vr X.length = .σ i ∧ letterAt Vr (X.length + 1) = .r i := by
  constructor
  · have := letterAt_block X Pr Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pr Y (i := 1) (by simp)
    simpa using this

theorem cr_length : (Vr).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem cr'_letters : letterAt Vr' X.length = .r i := by
  have := letterAt_block X Pr' Y (i := 0) (by simp)
  simpa using this

theorem cr'_length : (Vr').length = X.length + 1 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem cr_extCol (k : ℕ) : ExtCol X Pr k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by
  unfold ExtCol; simp

theorem cr'_extCol (k : ℕ) : ExtCol X Pr' k ↔ k + 1 ≤ X.length ∨ X.length + 1 ≤ k := by
  unfold ExtCol; simp

theorem cr_shift : shiftIdx X Pr Pr' (X.length + 2) = X.length + 1 := by
  unfold shiftIdx; simp

theorem cr_cut_start : cut Vr' X.length = cut Vr X.length := by
  unfold cut
  rw [List.append_assoc, List.take_left' rfl, List.append_assoc, List.take_left' rfl]

theorem cr_bit_start (p : ℕ) : bit Vr' X.length p = bit Vr X.length p := by
  rw [bit_eq, bit_eq, cr_cut_start]

include hW

theorem cr_i_pos : 1 ≤ i := σ_idx_pos hW (cr_letters X Y i).1

theorem cr_cutlen : i + 1 ≤ (cut Vr X.length).length ∧ (cut Vr (X.length + 1)).length = (cut Vr X.length).length := by
  have hk : X.length < (Vr).length := by rw [cr_length]; omega
  obtain ⟨-, h2, h3, -, -⟩ := σ_facts hW hk (cr_letters X Y i).1
  exact ⟨h2, h3⟩

theorem cr_sameEffect : SameEffect X Pr Pr' := by
  have hi := cr_i_pos X Y i hW
  exact sameEffect_of_replace X Pr Y Pr' hW (fun c c' h => run_crossedCusp_r hi h)

theorem cr_cut_end : cut Vr' (X.length + 1) = cut Vr (X.length + 2) := by
  have hE := cr_sameEffect X Y i hW
  unfold cut
  rw [List.take_left' (by simp), List.take_left' (by simp)]
  unfold SameEffect at hE
  rw [hE]

theorem cr_bit_end (p : ℕ) : bit Vr' (X.length + 1) p = bit Vr (X.length + 2) p := by
  rw [bit_eq, bit_eq, cr_cut_end X Y i hW]

include he

/-- the bits at the two block cuts: `e, !e` before the crossing, exchanged after it -/
theorem cr_bits :
    bit Vr X.length i = e ∧ bit Vr X.length (i + 1) = !e ∧
    bit Vr (X.length + 1) i = !e ∧ bit Vr (X.length + 1) (i + 1) = e := by
  obtain ⟨hℓ₀, hℓ₁⟩ := cr_letters X Y i
  have hk₀ : X.length < (Vr).length := by rw [cr_length]; omega
  have hk₁ : X.length + 1 < (Vr).length := by rw [cr_length]; omega
  obtain ⟨-, -, -, h3, h4⟩ := σ_facts hW hk₀ hℓ₀
  obtain ⟨-, h5⟩ := r_bits hW hk₁ hℓ₁
  rw [h3, he] at h5
  have h6 : bit Vr (X.length + 1) i = !e := by
    cases e <;> cases h : bit Vr (X.length + 1) i <;> simp_all
  exact ⟨he, by rw [← h4, h6], h6, by rw [h3, he]⟩

omit he

/-! the successor table of the block `σ_i r_i` (columns `|X|`, `|X|+1`) -/

theorem cr_T1 {s : Slot Vr} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vr X.length p = true)
    (hpi : p < i) : (next hW s).1 = (X.length + 1, p) ∧ bit Vr (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(cr_letters X Y i).1]; exact hpi)

theorem cr_T2 {s : Slot Vr} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vr X.length p = true)
    (hpi : i + 2 ≤ p) : (next hW s).1 = (X.length + 1, p) ∧ bit Vr (X.length + 1) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(cr_letters X Y i).1]; simpa [idx, arity] using hpi)
  rw [(cr_letters X Y i).1] at this
  simpa [coarity, arity] using this

theorem cr_T3 {s : Slot Vr} (hs : s.1 = (X.length, i)) (hb : bit Vr X.length i = true) :
    (next hW s).1 = (X.length + 1, i + 1) :=
  next_σ_right_idx hW (cr_letters X Y i).1 hs hb

theorem cr_T4 {s : Slot Vr} (hs : s.1 = (X.length, i + 1)) (hb : bit Vr X.length (i + 1) = true) :
    (next hW s).1 = (X.length + 1, i) :=
  next_σ_right_succ hW (cr_letters X Y i).1 hs hb

theorem cr_T5 {s : Slot Vr} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vr (X.length + 1) p = true) (hpi : p < i) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vr (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(cr_letters X Y i).2]; exact hpi)

theorem cr_T6 {s : Slot Vr} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vr (X.length + 1) p = true) (hpi : i + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p - 2) ∧ bit Vr (X.length + 2) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(cr_letters X Y i).2]; simpa [idx, arity] using hpi)
  rw [(cr_letters X Y i).2] at this
  simpa [coarity, arity] using this

theorem cr_T7 {s : Slot Vr} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p = i ∨ p = i + 1)
    (hb : bit Vr (X.length + 1) p = true) : (next hW s).1 = (X.length + 1, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (cr_letters X Y i).2 hs hp hb

theorem cr_T8 {s : Slot Vr} (hs : s.1 = (X.length + 1, 0)) :
    (next hW s).1 = (X.length + 1, if bit Vr (X.length + 1) i then i + 1 else i) :=
  next_cusp_r hW (cr_letters X Y i).2 hs

theorem cr_T9 {s : Slot Vr} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vr (X.length + 1) q = false) (hqi : q < i) :
    (next hW s).1 = (X.length, q) ∧ bit Vr X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (cr_letters X Y i).1]; exact hqi)
  rwa [Nat.add_sub_cancel] at this

theorem cr_T10 {s : Slot Vr} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vr (X.length + 1) q = false) (hqi : i + 2 ≤ q) :
    (next hW s).1 = (X.length, q) ∧ bit Vr X.length q = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (cr_letters X Y i).1]; simpa [idx, coarity] using hqi)
  rw [Nat.add_sub_cancel, (cr_letters X Y i).1] at this
  simpa [arity, coarity] using this

theorem cr_T11 {s : Slot Vr} (hs : s.1 = (X.length + 1, i)) (hb : bit Vr (X.length + 1) i = false) :
    (next hW s).1 = (X.length, i + 1) :=
  next_σ_left_idx hW (cr_letters X Y i).1 hs hb

theorem cr_T12 {s : Slot Vr} (hs : s.1 = (X.length + 1, i + 1)) (hb : bit Vr (X.length + 1) (i + 1) = false) :
    (next hW s).1 = (X.length, i) :=
  next_σ_left_succ hW (cr_letters X Y i).1 hs hb

theorem cr_T13 {s : Slot Vr} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vr (X.length + 2) q = false) (hqi : q < i) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vr (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e2, (cr_letters X Y i).2]; exact hqi)
  rwa [e2] at this

theorem cr_T14 {s : Slot Vr} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vr (X.length + 2) q = false) (hqi : i ≤ q) :
    (next hW s).1 = (X.length + 1, q + 2) ∧ bit Vr (X.length + 1) (q + 2) = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e2, (cr_letters X Y i).2]; simpa [idx, coarity] using hqi)
  rw [e2, (cr_letters X Y i).2] at this
  simpa [arity, coarity] using this

theorem cr_hexit : ∀ u : Slot Vr, ∃ n, ExtPiece X Pr Y ((next hW)^[n] u) := by
  apply hexit_of_no_l X Pr Y hW
  intro k' h1 h2 m d
  simp only [List.length_cons, List.length_nil] at h2
  have : k' = X.length ∨ k' = X.length + 1 := by omega
  rcases this with rfl | rfl
  · rw [(cr_letters X Y i).1]; exact fun h => by cases h
  · rw [(cr_letters X Y i).2]; exact fun h => by cases h

end CrossedCuspRightWord

section CrossedCuspRightPassage

open U3

variable (X Y : Word) (i : ℕ) (e : Bool) (hW : (X ++ [Letter.σ i, Letter.r i] ++ Y).Closed)
  (hW' : (X ++ [Letter.r i] ++ Y).Closed)

local notation "Vr" => X ++ [Letter.σ i, Letter.r i] ++ Y
local notation "Pr" => [Letter.σ i, Letter.r i]
local notation "Vr'" => X ++ [Letter.r i] ++ Y
local notation "Pr'" => [Letter.r i]

include hW'

theorem cr'_T1 {s : Slot Vr'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vr' X.length p = true)
    (hpi : p < i) : (next hW' s).1 = (X.length + 1, p) ∧ bit Vr' (X.length + 1) p = true :=
  next_right_lt hW' hs hp hb (by rw [cr'_letters X Y i]; exact hpi)

theorem cr'_T2 {s : Slot Vr'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vr' X.length p = true)
    (hpi : i + 2 ≤ p) : (next hW' s).1 = (X.length + 1, p - 2) ∧ bit Vr' (X.length + 1) (p - 2) = true := by
  have := next_right_ge hW' hs hp hb (by rw [cr'_letters X Y i]; simpa [idx, arity] using hpi)
  rw [cr'_letters X Y i] at this
  simpa [coarity, arity] using this

theorem cr'_T3 {s : Slot Vr'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p = i ∨ p = i + 1)
    (hb : bit Vr' X.length p = true) : (next hW' s).1 = (X.length, 0) :=
  next_arm_r hW' (slot_col_lt hW' hs) (cr'_letters X Y i) hs hp hb

theorem cr'_T4 {s : Slot Vr'} (hs : s.1 = (X.length, 0)) :
    (next hW' s).1 = (X.length, if bit Vr' X.length i then i + 1 else i) :=
  next_cusp_r hW' (cr'_letters X Y i) hs

theorem cr'_T5 {s : Slot Vr'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vr' (X.length + 1) q = false) (hqi : q < i) :
    (next hW' s).1 = (X.length, q) ∧ bit Vr' X.length q = false := by
  have := next_left_lt hW' hs hq hb (by rw [Nat.add_sub_cancel, cr'_letters X Y i]; exact hqi)
  rwa [Nat.add_sub_cancel] at this

theorem cr'_T6 {s : Slot Vr'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vr' (X.length + 1) q = false) (hqi : i ≤ q) :
    (next hW' s).1 = (X.length, q + 2) ∧ bit Vr' X.length (q + 2) = false := by
  have := next_left_ge hW' hs hq hb (by rw [Nat.add_sub_cancel, cr'_letters X Y i]; simpa [idx, coarity] using hqi)
  rw [Nat.add_sub_cancel, cr'_letters X Y i] at this
  simpa [arity, coarity] using this

theorem cr'_hexit : ∀ u : Slot Vr', ∃ n, ExtPiece X Pr' Y ((next hW')^[n] u) := by
  apply hexit_of_no_l X Pr' Y hW'
  intro k' h1 h2 m d
  simp only [List.length_cons, List.length_nil] at h2
  have : k' = X.length := by omega
  subst this
  rw [cr'_letters X Y i]; exact fun h => by cases h

include hW

/-- THE BLOCK PASSAGE of the right crossed cusp. -/
theorem cr_passage : Passage X Pr Y Pr' hW hW' := by
  obtain ⟨hℓ₀, hℓ₁⟩ := cr_letters X Y i
  obtain ⟨B1, B2, B3, B4⟩ := cr_bits X Y i (bit Vr X.length i) hW rfl
  have hi := cr_i_pos X Y i hW
  have hP : Pr ≠ [] := by simp
  have hE := cr_sameEffect X Y i hW
  have shiftL : ∀ p, extPair X Pr Pr' (X.length, p) = (X.length, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pr Pr' le_rfl]
  have shiftR : ∀ p, extPair X Pr Pr' (X.length + 2, p) = (X.length + 1, p) := by
    intro p; simp only [extPair, cr_shift X i]
  constructor
  intro b hext hcol
  let b' : Slot Vr' := ⟨extPair X Pr Pr' b.1, isSlot_ext X Pr Y Pr' hP hE b.2 hext⟩
  have hb'v : b'.1 = extPair X Pr Pr' b.1 := rfl
  rcases (entry_iff X Pr Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hb'1 : b'.1 = (X.length, p) := by rw [hb'v, hb, shiftL]
    have hbit' : bit Vr' X.length p = true := by rw [cr_bit_start, hbit]
    have hcol0 : ¬ ExtCol X Pr (colOf b) := by rw [block_col_true hb hp hbit, cr_extCol]; omega
    have hcol0' : ¬ ExtCol X Pr' (colOf b') := by rw [block_col_true hb'1 hp hbit', cr'_extCol]; omega
    rcases lt_or_ge p i with hpi | hpi
    · obtain ⟨h1, hb1⟩ := cr_T1 X Y i hW hb hp hbit hpi
      obtain ⟨h2, hb2⟩ := cr_T5 X Y i hW h1 hp hb1 hpi
      obtain ⟨h1', hb1'⟩ := cr'_T1 X Y i hW' hb'1 hp hbit' hpi
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pr) hcol0
        (passage_step hW (ExtCol X Pr) (by rw [block_col_true h1 hp hb1, cr_extCol]; omega) (passage_end hW))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pr') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h2 hp hb2, cr_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, shiftR]
    rcases lt_or_ge p (i + 2) with hpi2 | hpi2
    · -- the entering arm `p ∈ {i, i+1}`: through the crossing, the cusp, the crossing again
      have hpA : p = posA i (bit Vr X.length i) := by
        rcases Nat.eq_or_lt_of_le hpi with h | h
        · rw [← h] at hbit ⊢; rw [hbit]; rfl
        · have hpe : p = i + 1 := by omega
          rw [hpe] at hbit ⊢
          have : bit Vr X.length i = false := by rw [B2] at hbit; simpa using hbit
          rw [this]; rfl
      -- `W`: (|X|, posA) → (|X|+1, posB) → cusp → (|X|+1, posA) → (|X|, posB)
      have h1 : (next hW b).1 = (X.length + 1, posB i (bit Vr X.length i)) := by
        rw [hpA] at hb hbit
        cases hE0 : bit Vr X.length i
        · rw [hE0] at hb hbit; exact cr_T4 X Y i hW hb hbit
        · rw [hE0] at hb hbit; exact cr_T3 X Y i hW hb hbit
      have hb1 : bit Vr (X.length + 1) (posB i (bit Vr X.length i)) = true := by
        cases hE0 : bit Vr X.length i
        · rw [hE0] at B3; rw [posB_false, B3]; rfl
        · rw [hE0] at B4; rw [posB_true, B4]
      have h2 := cr_T7 X Y i hW h1 (posB_mem _ _) hb1
      have h3 : (next hW (next hW (next hW b))).1 = (X.length + 1, posA i (bit Vr X.length i)) := by
        rw [cr_T8 X Y i hW h2, B3]
        cases bit Vr X.length i <;> rfl
      have hb3 : bit Vr (X.length + 1) (posA i (bit Vr X.length i)) = false := by
        cases hE0 : bit Vr X.length i
        · rw [hE0] at B4; rw [posA_false, B4]
        · rw [hE0] at B3; rw [posA_true, B3]; rfl
      have h4 : (next hW (next hW (next hW (next hW b)))).1 = (X.length, posB i (bit Vr X.length i)) := by
        cases hE0 : bit Vr X.length i
        · rw [hE0] at h3 hb3; rw [posA_false] at h3 hb3; rw [posB_false]
          exact cr_T12 X Y i hW h3 hb3
        · rw [hE0] at h3 hb3; rw [posA_true] at h3 hb3; rw [posB_true]
          exact cr_T11 X Y i hW h3 hb3
      have hb4 : bit Vr X.length (posB i (bit Vr X.length i)) = false := by
        cases hE0 : bit Vr X.length i
        · rw [posB_false]; exact hE0
        · rw [hE0] at B2; rw [posB_true, B2]; rfl
      -- `W'`: (|X|, posA) → cusp → (|X|, posB)
      have h1' := cr'_T3 X Y i hW' hb'1 (by rw [hpA]; exact posA_mem _ _) hbit'
      have h2' : (next hW' (next hW' b')).1 = (X.length, posB i (bit Vr X.length i)) := by
        rw [cr'_T4 X Y i hW' h1', cr_bit_start]
        cases bit Vr X.length i <;> rfl
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pr) hcol0
        (passage_step hW (ExtCol X Pr) (by rw [block_col_true h1 (by have := posB_le i (bit Vr X.length i); omega) hb1, cr_extCol]; omega)
        (passage_step hW (ExtCol X Pr) (by rw [block_col_vertex h2, cr_extCol]; omega)
        (passage_step hW (ExtCol X Pr) (by rw [block_col_false h3 (by have := posA_le i (bit Vr X.length i); omega) hb3, cr_extCol]; omega) (passage_end hW))))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pr') hcol0'
        (passage_step hW' (ExtCol X Pr') (by rw [block_col_vertex h1', cr'_extCol]; omega) (passage_end hW'))
      have hk4 := (cutSlot_facts hW h4 (by have := posB_le i (bit Vr X.length i); omega)).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h4 (by have := posB_le i (bit Vr X.length i); omega) hb4, cr_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h2', h4, shiftL]
    · obtain ⟨h1, hb1⟩ := cr_T2 X Y i hW hb hp hbit hpi2
      obtain ⟨h2, hb2⟩ := cr_T6 X Y i hW h1 hp hb1 hpi2
      obtain ⟨h1', hb1'⟩ := cr'_T2 X Y i hW' hb'1 hp hbit' hpi2
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pr) hcol0
        (passage_step hW (ExtCol X Pr) (by rw [block_col_true h1 hp hb1, cr_extCol]; omega) (passage_end hW))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pr') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h2 (by omega) hb2, cr_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, shiftR]
  · -- from the right at `(|X|+2, q)`
    replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Vr (X.length + 2) p = false := hbit
    have hb'1 : b'.1 = (X.length + 1, p) := by rw [hb'v, hb, shiftR]
    have hbit' : bit Vr' (X.length + 1) p = false := by rw [cr_bit_end X Y i hW, hbit]
    have hcol0 : ¬ ExtCol X Pr (colOf b) := by rw [block_col_false hb hp hbit, cr_extCol]; omega
    have hcol0' : ¬ ExtCol X Pr' (colOf b') := by rw [block_col_false hb'1 hp hbit', cr'_extCol]; omega
    rcases lt_or_ge p i with hpi | hpi
    · obtain ⟨h1, hb1⟩ := cr_T13 X Y i hW hb hp hbit hpi
      obtain ⟨h2, hb2⟩ := cr_T9 X Y i hW h1 hp hb1 hpi
      obtain ⟨h1', hb1'⟩ := cr'_T5 X Y i hW' hb'1 hp hbit' hpi
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pr) hcol0
        (passage_step hW (ExtCol X Pr) (by rw [block_col_false h1 hp hb1, cr_extCol]; omega) (passage_end hW))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pr') hcol0' (passage_end hW')
      have hk2 := (cutSlot_facts hW h2 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h2 hp hb2, cr_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, shiftL]
    · obtain ⟨h1, hb1⟩ := cr_T14 X Y i hW hb hp hbit hpi
      obtain ⟨h2, hb2⟩ := cr_T10 X Y i hW h1 (by omega) hb1 (by omega)
      obtain ⟨h1', hb1'⟩ := cr'_T6 X Y i hW' hb'1 hp hbit' hpi
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pr) hcol0
        (passage_step hW (ExtCol X Pr) (by rw [block_col_false h1 (by omega) hb1, cr_extCol]; omega) (passage_end hW))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pr') hcol0' (passage_end hW')
      have hk2 := (cutSlot_facts hW h2 (by omega)).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h2 (by omega) hb2, cr_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, shiftL]

end CrossedCuspRightPassage

/-! #### C3. The right crossed-cusp disc: numeric facts (the mirror image of `ccL`) -/

section CcrNumeric

/-- the right crossed-cusp disc: `[k, k+2] × [−i−3/2, −i+1/2]` cut by the line `y ≥ −i + 1/4 + 2(x − (k+2))` -/
def ccLr (k i : ℕ) : List HalfPlane :=
  [HalfPlane.xge (k : ℝ), HalfPlane.xle ((k : ℝ) + 2), HalfPlane.yle (-(i : ℝ) + 1 / 2), HalfPlane.yge (-(i : ℝ) - 3 / 2),
    HalfPlane.above (-(i : ℝ) + 1 / 4 - 2 * k - 4) 2]

macro "ccr_mem" : tactic => `(tactic| (
  simp only [ccLr, mem_polygon_iff, mem_interior_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, or_false, HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle,
    HalfPlane.b_yle, HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith))

variable (k i : ℕ)

theorem ccr_int_a : (((k + 1 : ℕ) : ℝ), -(i : ℝ) - 3 / 4) ∈ interior (polygon (ccLr k i)) := by push_cast; ccr_mem
theorem ccr_int_b : (((k + 1 : ℕ) : ℝ), -(i : ℝ) - 1 / 4) ∈ interior (polygon (ccLr k i)) := by push_cast; ccr_mem
theorem ccr_int_i : (((k + 1 : ℕ) : ℝ), -(i : ℝ)) ∈ interior (polygon (ccLr k i)) := by push_cast; ccr_mem
theorem ccr_int_i1 : (((k + 1 : ℕ) : ℝ), -((i + 1 : ℕ) : ℝ)) ∈ interior (polygon (ccLr k i)) := by push_cast; ccr_mem
theorem ccr_int_cusp : (((k + 1 : ℕ) : ℝ) + 1 / 2, -(i : ℝ) - 1 / 2) ∈ interior (polygon (ccLr k i)) := by push_cast; ccr_mem
theorem ccr_mem_li : ((k : ℝ), -(i : ℝ)) ∈ polygon (ccLr k i) := by ccr_mem
theorem ccr_mem_li1 : ((k : ℝ), -((i + 1 : ℕ) : ℝ)) ∈ polygon (ccLr k i) := by push_cast; ccr_mem

theorem ccr_xge_mem : HalfPlane.xge (Placement.std.x k) ∈ ccLr k i := by simp [ccLr]
theorem ccr_xle_mem : HalfPlane.xle (Placement.std.x (k + 2)) ∈ ccLr k i := by
  have e : Placement.std.x (k + 2) = (k : ℝ) + 2 := by rw [Placement.std_x]; push_cast; ring
  rw [e]; simp [ccLr]

theorem ccr_out_above {p : ℕ} (hp : p < i) (x₀ x₁ : ℝ) : SegOut (ccLr k i) (x₀, -(p : ℝ)) (x₁, -(p : ℝ)) := by
  have hp' : (p : ℝ) + 1 ≤ i := by exact_mod_cast hp
  refine segOut_of_lt (HalfPlane.yle (-(i : ℝ) + 1 / 2)) (by simp [ccLr]) ?_ ?_ <;>
    simp only [HalfPlane.f_yle, HalfPlane.b_yle] <;> linarith

theorem ccr_out_below {p : ℕ} (hp : i + 2 ≤ p) (x₀ x₁ : ℝ) : SegOut (ccLr k i) (x₀, -(p : ℝ)) (x₁, -(p : ℝ)) := by
  have hp' : (i : ℝ) + 2 ≤ p := by exact_mod_cast hp
  refine segOut_of_lt (HalfPlane.yge (-(i : ℝ) - 3 / 2)) (by simp [ccLr]) ?_ ?_ <;>
    simp only [HalfPlane.f_yge, HalfPlane.b_yge] <;> linarith

/-- the pulled-up spectator of the right-cusp column: `pass (q+2) q` with `i ≤ q` -/
theorem ccr_out_slant {q : ℕ} (hq : i ≤ q) :
    SegOut (ccLr k i) (((k + 1 : ℕ) : ℝ), -((q + 2 : ℕ) : ℝ)) (((k + 2 : ℕ) : ℝ), -(q : ℝ)) := by
  have hq' : (i : ℝ) ≤ q := by exact_mod_cast hq
  refine segOut_of_lt (HalfPlane.above (-(i : ℝ) + 1 / 4 - 2 * k - 4) 2) (by simp [ccLr]) ?_ ?_ <;>
    simp only [HalfPlane.f_above, HalfPlane.b_above] <;> push_cast <;> linarith

theorem ccr_mem_cut {j p : ℕ} (h : ((j : ℝ), -(p : ℝ)) ∈ polygon (ccLr k i)) : (j = k ∨ j = k + 1) ∧ (p = i ∨ p = i + 1) := by
  simp only [ccLr, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e1 : k ≤ j := by exact_mod_cast (by linarith : (k : ℝ) ≤ j)
  have e2 : j ≤ k + 2 := by exact_mod_cast (by linarith : (j : ℝ) ≤ k + 2)
  have e3 : 2 * i ≤ 2 * p + 1 := by exact_mod_cast (by linarith : (2 * i : ℝ) ≤ 2 * p + 1)
  have e4 : 2 * p ≤ 2 * i + 3 := by exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 2 * i + 3)
  have e5 : 4 * p + 8 * j + 1 ≤ 4 * i + 8 * k + 16 := by
    exact_mod_cast (by linarith : (4 * p + 8 * j + 1 : ℝ) ≤ 4 * i + 8 * k + 16)
  omega

theorem ccr_mem_cusp {j : ℕ} (y : ℝ) (h : ((j : ℝ) + 1 / 2, y) ∈ polygon (ccLr k i)) : j = k ∨ j = k + 1 := by
  simp only [ccLr, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at h
  obtain ⟨h1, h2, -, -, -⟩ := h
  have e1 : 2 * k ≤ 2 * j + 1 := by exact_mod_cast (by linarith : (2 * k : ℝ) ≤ 2 * j + 1)
  have e2 : 2 * j + 1 ≤ 2 * k + 4 := by exact_mod_cast (by linarith : (2 * j + 1 : ℝ) ≤ 2 * k + 4)
  omega

theorem ccLr_isDisc : IsDisc (polygon (ccLr k i)) := by
  refine isDisc_polygon (ccLr k i) (a := k) (b := (k : ℝ) + 2) (c := -(i : ℝ) - 3 / 2) (d := -(i : ℝ) + 1 / 2) ?_
    ⟨((k : ℝ) + 1, -(i : ℝ) - 1 / 2), ?_⟩
  · intro q hq
    simp only [ccLr, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
      HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
      HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at hq
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]
  · simp only [ccLr, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
      HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
      HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end CcrNumeric

/-! #### C5. The right crossed cusp: chain, moved vertices, specification, leaf case -/

section CrossedCuspRightGeom

open U3

variable (X Y : Word) (i : ℕ) (e : Bool) (hW : (X ++ [Letter.σ i, Letter.r i] ++ Y).Closed)
  (he : bit (X ++ [Letter.σ i, Letter.r i] ++ Y) X.length i = e)

local notation "Vr" => X ++ [Letter.σ i, Letter.r i] ++ Y
local notation "Pr" => [Letter.σ i, Letter.r i]
local notation "Vr'" => X ++ [Letter.r i] ++ Y
local notation "Pr'" => [Letter.r i]

/-- the moved vertices: the two crossing ends at cut `|X|+1` uncrossed (heights `−i−3/4`, `−i−1/4`) -/
def crMv : Slot Vr → Plane := mv2 Vr (X.length + 1) i (-(i : ℝ) - 3 / 4) (-(i : ℝ) - 1 / 4)

theorem crMv_apply (u : Slot Vr) : crMv X Y i u = mv2 Vr (X.length + 1) i (-(i : ℝ) - 3 / 4) (-(i : ℝ) - 1 / 4) u := rfl

include hW he

theorem cr_bitA0 : bit Vr X.length (posA i e) = true := by
  obtain ⟨B1, B2, -, -⟩ := cr_bits X Y i e hW he
  cases e
  · rw [posA_false, B2]; rfl
  · rw [posA_true, B1]

theorem cr_bitB0 : bit Vr X.length (posB i e) = false := by
  obtain ⟨B1, B2, -, -⟩ := cr_bits X Y i e hW he
  cases e
  · rw [posB_false, B1]
  · rw [posB_true, B2]; rfl

theorem cr_bitA1 : bit Vr (X.length + 1) (posA i e) = false := by
  obtain ⟨-, -, B3, B4⟩ := cr_bits X Y i e hW he
  cases e
  · rw [posA_false, B4]
  · rw [posA_true, B3]; rfl

theorem cr_bitB1 : bit Vr (X.length + 1) (posB i e) = true := by
  obtain ⟨-, -, B3, B4⟩ := cr_bits X Y i e hW he
  cases e
  · rw [posB_false, B3]; rfl
  · rw [posB_true, B4]

omit he in
theorem cr_isSlot_u0 : IsSlot Vr (X.length, posA i e) := by
  obtain ⟨h1, -⟩ := cr_cutlen X Y i hW
  have := posA_le i e
  have hi := cr_i_pos X Y i hW
  exact isSlot_cut (by omega) (by omega) (by rw [cr_length]; omega)

omit he in
/-- the arc of the right crossed cusp in the realization: entry `(|X|, posA)` (rightward), four pieces -/
def crChain : Chain Vr := ⟨⟨(X.length, posA i e), cr_isSlot_u0 X Y i e hW⟩, 4, by norm_num⟩

omit he in
theorem cr_s0 : ((crChain X Y i e hW).slot hW 0).1 = (X.length, posA i e) := rfl

theorem cr_s1 : ((crChain X Y i e hW).slot hW 1).1 = (X.length + 1, posB i e) := by
  rw [Chain.slot_succ]
  have hb := cr_bitA0 X Y i e hW he
  cases e
  · rw [posA_false] at hb; rw [posB_false]
    exact cr_T4 X Y i hW (cr_s0 X Y i false hW) hb
  · rw [posA_true] at hb; rw [posB_true]
    exact cr_T3 X Y i hW (cr_s0 X Y i true hW) hb

theorem cr_s2 : ((crChain X Y i e hW).slot hW 2).1 = (X.length + 1, 0) := by
  rw [Chain.slot_succ]
  exact cr_T7 X Y i hW (cr_s1 X Y i e hW he) (posB_mem i e) (cr_bitB1 X Y i e hW he)

theorem cr_s3 : ((crChain X Y i e hW).slot hW 3).1 = (X.length + 1, posA i e) := by
  rw [Chain.slot_succ, cr_T8 X Y i hW (cr_s2 X Y i e hW he), (cr_bits X Y i e hW he).2.2.1]
  cases e <;> rfl

theorem cr_s4 : ((crChain X Y i e hW).slot hW 4).1 = (X.length, posB i e) := by
  rw [Chain.slot_succ]
  have hb := cr_bitA1 X Y i e hW he
  cases e
  · rw [posA_false] at hb; rw [posB_false]
    exact cr_T12 X Y i hW (cr_s3 X Y i false hW he) hb
  · rw [posA_true] at hb; rw [posB_true]
    exact cr_T11 X Y i hW (cr_s3 X Y i true hW he) hb

omit he in
theorem cr_mv0 : crMv X Y i ((crChain X Y i e hW).slot hW 0) = ((X.length : ℝ), -((posA i e : ℕ) : ℝ)) := by
  rw [crMv_apply, mv2_of_cut_ne _ _ _ _ _ (by rw [cr_s0]; omega), cr_s0,
    std_pt_cut _ (by have := posA_le i e; have := cr_i_pos X Y i hW; omega)]

theorem cr_mv1 : crMv X Y i ((crChain X Y i e hW).slot hW 1) = (((X.length + 1 : ℕ) : ℝ), hB i e) := by
  have h := cr_s1 X Y i e hW he
  rw [crMv_apply]
  cases e
  · rw [posB_false] at h; rw [mv2_fst _ _ _ _ _ h]; rfl
  · rw [posB_true] at h; rw [mv2_snd _ _ _ _ _ h]; rfl

theorem cr_mv2 : crMv X Y i ((crChain X Y i e hW).slot hW 2) = (((X.length + 1 : ℕ) : ℝ) + 1 / 2, -(i : ℝ) - 1 / 2) := by
  rw [crMv_apply, mv2_of_pos_ne _ _ _ _ _ (by rw [cr_s2 X Y i e hW he]; have := cr_i_pos X Y i hW; omega)
    (by rw [cr_s2 X Y i e hW he]; omega), cr_s2 X Y i e hW he, std_pt_cusp, (cr_letters X Y i).2]; rfl

theorem cr_mv3 : crMv X Y i ((crChain X Y i e hW).slot hW 3) = (((X.length + 1 : ℕ) : ℝ), hA i e) := by
  have h := cr_s3 X Y i e hW he
  rw [crMv_apply]
  cases e
  · rw [posA_false] at h; rw [mv2_snd _ _ _ _ _ h]; rfl
  · rw [posA_true] at h; rw [mv2_fst _ _ _ _ _ h]; rfl

theorem cr_mv4 : crMv X Y i ((crChain X Y i e hW).slot hW 4) = ((X.length : ℝ), -((posB i e : ℕ) : ℝ)) := by
  rw [crMv_apply, mv2_of_cut_ne _ _ _ _ _ (by rw [cr_s4 X Y i e hW he]; omega), cr_s4 X Y i e hW he,
    std_pt_cut _ (by have := posB_le i e; have := cr_i_pos X Y i hW; omega)]

omit he in
theorem cr_pt0 : pt .std Vr ((crChain X Y i e hW).slot hW 0).1 = ((X.length : ℝ), -((posA i e : ℕ) : ℝ)) := by
  rw [cr_s0, std_pt_cut _ (by have := posA_le i e; have := cr_i_pos X Y i hW; omega)]

theorem cr_pt1 : pt .std Vr ((crChain X Y i e hW).slot hW 1).1 = (((X.length + 1 : ℕ) : ℝ), -((posB i e : ℕ) : ℝ)) := by
  rw [cr_s1 X Y i e hW he, std_pt_cut _ (by have := posB_le i e; have := cr_i_pos X Y i hW; omega)]

theorem cr_pt2 : pt .std Vr ((crChain X Y i e hW).slot hW 2).1 = (((X.length + 1 : ℕ) : ℝ) + 1 / 2, -(i : ℝ) - 1 / 2) := by
  rw [cr_s2 X Y i e hW he, std_pt_cusp, (cr_letters X Y i).2]; rfl

theorem cr_pt3 : pt .std Vr ((crChain X Y i e hW).slot hW 3).1 = (((X.length + 1 : ℕ) : ℝ), -((posA i e : ℕ) : ℝ)) := by
  rw [cr_s3 X Y i e hW he, std_pt_cut _ (by have := posA_le i e; have := cr_i_pos X Y i hW; omega)]

theorem cr_pt4 : pt .std Vr ((crChain X Y i e hW).slot hW 4).1 = ((X.length : ℝ), -((posB i e : ℕ) : ℝ)) := by
  rw [cr_s4 X Y i e hW he, std_pt_cut _ (by have := posB_le i e; have := cr_i_pos X Y i hW; omega)]

omit he in
theorem cr_hmv : ∀ v : Slot Vr, ExtSl X.length (X.length + 2) v.1 → crMv X Y i v = pt .std Vr v.1 := by
  intro v hv
  have hi := cr_i_pos X Y i hW
  rw [crMv_apply]
  unfold ExtSl at hv
  split_ifs at hv with h0
  · exact mv2_of_pos_ne _ _ _ _ _ (by omega) (by omega)
  · exact mv2_of_cut_ne _ _ _ _ _ (by omega)

omit hW he in
/-- the only crossing letter of the block is the `σ_i` of column `|X|` -/
theorem cr_σcol {k' m : ℕ} (hℓ : letterAt Vr k' = .σ m) (hext : ¬ ExtCol X Pr k') :
    k' = X.length ∧ i = m := by
  rw [cr_extCol] at hext
  have : k' = X.length ∨ k' = X.length + 1 := by omega
  rcases this with rfl | rfl
  · rw [(cr_letters X Y i).1] at hℓ
    exact ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [(cr_letters X Y i).2] at hℓ; cases hℓ

theorem cr_σA_chain {m : ℕ} (hk : X.length < (Vr).length) (hℓ : letterAt Vr X.length = .σ m) :
    ∃ j, j < 4 ∧ (crChain X Y i e hW).slot hW j = σSlotA hW hk hℓ := by
  have hm : i = m := by rw [(cr_letters X Y i).1] at hℓ; exact Letter.σ.inj hℓ
  subst hm
  have hv := σSlotA_val hW hk hℓ
  rw [he] at hv
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte] at hv
    exact ⟨3, by norm_num, Subtype.ext ((cr_s3 X Y i false hW he).trans hv.symm)⟩
  · simp only [↓reduceIte] at hv
    exact ⟨0, by norm_num, Subtype.ext ((cr_s0 X Y i true hW).trans hv.symm)⟩

theorem cr_hK : ∀ (k' m : ℕ) (hk : k' < (Vr).length) (hℓ : letterAt Vr k' = .σ m),
    ExtCol X Pr k' ↔ Unch .std hW (crMv X Y i) (σSlotA hW hk hℓ) ∧ Unch .std hW (crMv X Y i) (σSlotB hW hk hℓ) := by
  intro k' m hk hℓ
  constructor
  · intro hext
    have hext' := (cr_extCol X i k').1 hext
    exact ⟨unch_of_extCol .std hW _ (cr_hmv X Y i hW) (by rw [(σSlotA_spec hW hk hℓ).1]; exact hext'),
      unch_of_extCol .std hW _ (cr_hmv X Y i hW) (by rw [(σSlotB_spec hW hk hℓ).1]; exact hext')⟩
  · rintro ⟨hA, -⟩
    by_contra hext
    obtain ⟨rfl, rfl⟩ := cr_σcol X Y i hℓ hext
    have hv := σSlotA_val hW hk hℓ
    rw [he] at hv
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      have h1 := hA.1
      rw [crMv_apply, mv2_snd _ _ _ _ _ hv] at h1
      exact (nonGrid_quarter i).ne_pt _ _ _ h1
    · simp only [↓reduceIte] at hv
      have h2 := hA.2
      rw [cr_T3 X Y i hW hv he, crMv_apply, mv2_snd _ _ _ _ _ (cr_T3 X Y i hW hv he)] at h2
      exact (nonGrid_quarter i).ne_pt _ _ _ h2

omit he in
theorem cr_mem0 : crMv X Y i ((crChain X Y i e hW).slot hW 0) ∈ polygon (ccLr X.length i) ∧
    pt .std Vr ((crChain X Y i e hW).slot hW 0).1 ∈ polygon (ccLr X.length i) := by
  rw [cr_mv0, cr_pt0]
  cases e
  · exact ⟨ccr_mem_li1 _ _, ccr_mem_li1 _ _⟩
  · exact ⟨ccr_mem_li _ _, ccr_mem_li _ _⟩

theorem cr_int1 : crMv X Y i ((crChain X Y i e hW).slot hW 1) ∈ interior (polygon (ccLr X.length i)) ∧
    pt .std Vr ((crChain X Y i e hW).slot hW 1).1 ∈ interior (polygon (ccLr X.length i)) := by
  rw [cr_mv1 X Y i e hW he, cr_pt1 X Y i e hW he]
  cases e
  · exact ⟨ccr_int_a _ _, ccr_int_i _ _⟩
  · exact ⟨ccr_int_b _ _, ccr_int_i1 _ _⟩

theorem cr_int2 : crMv X Y i ((crChain X Y i e hW).slot hW 2) ∈ interior (polygon (ccLr X.length i)) ∧
    pt .std Vr ((crChain X Y i e hW).slot hW 2).1 ∈ interior (polygon (ccLr X.length i)) := by
  rw [cr_mv2 X Y i e hW he, cr_pt2 X Y i e hW he]
  exact ⟨ccr_int_cusp _ _, ccr_int_cusp _ _⟩

theorem cr_int3 : crMv X Y i ((crChain X Y i e hW).slot hW 3) ∈ interior (polygon (ccLr X.length i)) ∧
    pt .std Vr ((crChain X Y i e hW).slot hW 3).1 ∈ interior (polygon (ccLr X.length i)) := by
  rw [cr_mv3 X Y i e hW he, cr_pt3 X Y i e hW he]
  cases e
  · exact ⟨ccr_int_b _ _, ccr_int_i1 _ _⟩
  · exact ⟨ccr_int_a _ _, ccr_int_i _ _⟩

theorem cr_mem4 : crMv X Y i ((crChain X Y i e hW).slot hW 4) ∈ polygon (ccLr X.length i) ∧
    pt .std Vr ((crChain X Y i e hW).slot hW 4).1 ∈ polygon (ccLr X.length i) := by
  rw [cr_mv4 X Y i e hW he, cr_pt4 X Y i e hW he]
  cases e
  · exact ⟨ccr_mem_li _ _, ccr_mem_li _ _⟩
  · exact ⟨ccr_mem_li1 _ _, ccr_mem_li1 _ _⟩

theorem cr_chain_in : ∀ j, j < 4 → PieceIn (ccLr X.length i) hW (crMv X Y i) ((crChain X Y i e hW).slot hW j) ∧
    PieceIn (ccLr X.length i) hW (ptv .std) ((crChain X Y i e hW).slot hW j) := by
  intro j hj
  interval_cases j
  · have e1 : next hW ((crChain X Y i e hW).slot hW 0) = (crChain X Y i e hW).slot hW 1 := (Chain.slot_succ hW _ 0).symm
    constructor
    · show SegIn _ (crMv X Y i _) (crMv X Y i (next hW _))
      rw [e1]; exact segIn_of_interior_right (cr_mem0 X Y i e hW).1 (cr_int1 X Y i e hW he).1
    · show SegIn _ (pt .std Vr _) (pt .std Vr (next hW _).1)
      rw [e1]; exact segIn_of_interior_right (cr_mem0 X Y i e hW).2 (cr_int1 X Y i e hW he).2
  · have e1 : next hW ((crChain X Y i e hW).slot hW 1) = (crChain X Y i e hW).slot hW 2 := (Chain.slot_succ hW _ 1).symm
    constructor
    · show SegIn _ (crMv X Y i _) (crMv X Y i (next hW _))
      rw [e1]; exact segIn_of_interior_left (cr_int1 X Y i e hW he).1 (interior_subset (cr_int2 X Y i e hW he).1)
    · show SegIn _ (pt .std Vr _) (pt .std Vr (next hW _).1)
      rw [e1]; exact segIn_of_interior_left (cr_int1 X Y i e hW he).2 (interior_subset (cr_int2 X Y i e hW he).2)
  · have e1 : next hW ((crChain X Y i e hW).slot hW 2) = (crChain X Y i e hW).slot hW 3 := (Chain.slot_succ hW _ 2).symm
    constructor
    · show SegIn _ (crMv X Y i _) (crMv X Y i (next hW _))
      rw [e1]; exact segIn_of_interior_left (cr_int2 X Y i e hW he).1 (interior_subset (cr_int3 X Y i e hW he).1)
    · show SegIn _ (pt .std Vr _) (pt .std Vr (next hW _).1)
      rw [e1]; exact segIn_of_interior_left (cr_int2 X Y i e hW he).2 (interior_subset (cr_int3 X Y i e hW he).2)
  · have e1 : next hW ((crChain X Y i e hW).slot hW 3) = (crChain X Y i e hW).slot hW 4 := (Chain.slot_succ hW _ 3).symm
    constructor
    · show SegIn _ (crMv X Y i _) (crMv X Y i (next hW _))
      rw [e1]; exact segIn_of_interior_left (cr_int3 X Y i e hW he).1 (cr_mem4 X Y i e hW he).1
    · show SegIn _ (pt .std Vr _) (pt .std Vr (next hW _).1)
      rw [e1]; exact segIn_of_interior_left (cr_int3 X Y i e hW he).2 (cr_mem4 X Y i e hW he).2

theorem cr_vert : ∀ j, 0 < j → j < 4 → crMv X Y i ((crChain X Y i e hW).slot hW j) ∈ interior (polygon (ccLr X.length i)) ∧
    pt .std Vr ((crChain X Y i e hW).slot hW j).1 ∈ interior (polygon (ccLr X.length i)) := by
  intro j h0 hj
  interval_cases j
  · exact cr_int1 X Y i e hW he
  · exact cr_int2 X Y i e hW he
  · exact cr_int3 X Y i e hW he

omit he in
theorem cr_moved : ∀ u : Slot Vr, crMv X Y i u = pt .std Vr u.1 ∨
    (crMv X Y i u ∈ interior (polygon (ccLr X.length i)) ∧ pt .std Vr u.1 ∈ interior (polygon (ccLr X.length i))) := by
  intro u
  have hi := cr_i_pos X Y i hW
  by_cases h1 : u.1 = (X.length + 1, i)
  · right
    rw [crMv_apply, mv2_fst _ _ _ _ _ h1, h1, std_pt_cut _ (by omega)]
    exact ⟨ccr_int_a _ _, ccr_int_i _ _⟩
  by_cases h2 : u.1 = (X.length + 1, i + 1)
  · right
    rw [crMv_apply, mv2_snd _ _ _ _ _ h2, h2, std_pt_cut _ (by omega)]
    exact ⟨ccr_int_b _ _, ccr_int_i1 _ _⟩
  · left
    rw [crMv_apply, mv2_of_ne _ _ _ _ _ h1 h2]

omit he in
theorem cr_spec {u : Slot Vr} {j p j' p' : ℕ} (hu : u.1 = (j, p)) (hn : (next hW u).1 = (j', p'))
    (hp : p ≠ 0) (hp' : p' ≠ 0)
    (h1 : j ≠ X.length + 1 ∨ (p ≠ i ∧ p ≠ i + 1)) (h2 : j' ≠ X.length + 1 ∨ (p' ≠ i ∧ p' ≠ i + 1))
    (hout : SegOut (ccLr X.length i) ((j : ℝ), -(p : ℝ)) ((j' : ℝ), -(p' : ℝ))) :
    Unch .std hW (crMv X Y i) u ∧ PieceOut (ccLr X.length i) hW (ptv .std) u := by
  constructor
  · constructor
    · rw [crMv_apply]; apply mv2_of_ne <;> rw [hu] <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
    · rw [crMv_apply]; apply mv2_of_ne <;> rw [hn] <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
  · show SegOut _ (pt .std Vr u.1) (pt .std Vr (next hW u).1)
    rw [hu, hn, std_pt_cut _ hp, std_pt_cut _ hp']
    exact hout

/-- THE CLASSIFICATION for the right crossed cusp. -/
theorem cr_rest : ∀ u : Slot Vr, (∃ j, j < 4 ∧ (crChain X Y i e hW).slot hW j = u) ∨
    (Unch .std hW (crMv X Y i) u ∧ PieceOut (ccLr X.length i) hW (ptv .std) u) := by
  intro u
  obtain ⟨B1, B2, B3, B4⟩ := cr_bits X Y i e hW he
  have hi := cr_i_pos X Y i hW
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pr (colOf u)
  · right
    have hext' := (cr_extCol X i _).1 hext
    exact ⟨unch_of_extCol .std hW _ (cr_hmv X Y i hW) hext',
      pieceOut_of_extCol _ .std hW _ (ccr_xge_mem _ _) (ccr_xle_mem _ _) (unch_pt _ _ _) hext'⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, cr_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exfalso
      have := vertex_not_crossing hu
      rw [(cr_letters X Y i).1] at this
      simp [isCrossing] at this
    · exact Or.inl ⟨2, by norm_num, Subtype.ext ((cr_s2 X Y i e hW he).trans hu.symm)⟩
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vr j p
  · rw [block_col_false hu hp hb, cr_extCol] at hext
    have : j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, -⟩ := cr_T9 X Y i hW hu hp hb hpi
        exact Or.inr (cr_spec X Y i hW hu h1 hp hp (Or.inr ⟨by omega, by omega⟩) (Or.inl (by omega))
          (ccr_out_above _ _ hpi _ _))
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · left
        refine ⟨3, by norm_num, Subtype.ext ((cr_s3 X Y i e hW he).trans ?_)⟩
        rw [hu]
        congr 1
        cases e
        · show i + 1 = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exfalso; rw [← h, B3] at hb; cases hb
          · omega
        · show i = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exact h
          · exfalso; have : p = i + 1 := by omega
            rw [this, B4] at hb; cases hb
      · obtain ⟨h1, -⟩ := cr_T10 X Y i hW hu hp hb hpi2
        exact Or.inr (cr_spec X Y i hW hu h1 hp hp (Or.inr ⟨by omega, by omega⟩) (Or.inl (by omega))
          (ccr_out_below _ _ hpi2 _ _))
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, -⟩ := cr_T13 X Y i hW hu hp hb hpi
        exact Or.inr (cr_spec X Y i hW hu h1 hp hp (Or.inl (by omega)) (Or.inr ⟨by omega, by omega⟩)
          (ccr_out_above _ _ hpi _ _))
      · obtain ⟨h1, -⟩ := cr_T14 X Y i hW hu hp hb hpi
        exact Or.inr (cr_spec X Y i hW hu h1 hp (by omega) (Or.inl (by omega)) (Or.inr ⟨by omega, by omega⟩)
          (ccr_out_slant _ _ hpi).symm)
  · rw [block_col_true hu hp hb, cr_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, -⟩ := cr_T1 X Y i hW hu hp hb hpi
        exact Or.inr (cr_spec X Y i hW hu h1 hp hp (Or.inl (by omega)) (Or.inr ⟨by omega, by omega⟩)
          (ccr_out_above _ _ hpi _ _))
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · left
        refine ⟨0, by norm_num, Subtype.ext ((cr_s0 X Y i e hW).trans ?_)⟩
        rw [hu]
        congr 1
        cases e
        · show i + 1 = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exfalso; rw [← h, B1] at hb; cases hb
          · omega
        · show i = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exact h
          · exfalso; have : p = i + 1 := by omega
            rw [this, B2] at hb; cases hb
      · obtain ⟨h1, -⟩ := cr_T2 X Y i hW hu hp hb hpi2
        exact Or.inr (cr_spec X Y i hW hu h1 hp hp (Or.inl (by omega)) (Or.inr ⟨by omega, by omega⟩)
          (ccr_out_below _ _ hpi2 _ _))
    · rcases lt_or_ge p i with hpi | hpi
      · obtain ⟨h1, -⟩ := cr_T5 X Y i hW hu hp hb hpi
        exact Or.inr (cr_spec X Y i hW hu h1 hp hp (Or.inr ⟨by omega, by omega⟩) (Or.inl (by omega))
          (ccr_out_above _ _ hpi _ _))
      rcases lt_or_ge p (i + 2) with hpi2 | hpi2
      · left
        refine ⟨1, by norm_num, Subtype.ext ((cr_s1 X Y i e hW he).trans ?_)⟩
        rw [hu]
        congr 1
        cases e
        · show i = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exact h
          · exfalso; have : p = i + 1 := by omega
            rw [this, B4] at hb; cases hb
        · show i + 1 = p
          rcases Nat.eq_or_lt_of_le hpi with h | h
          · exfalso; rw [← h, B3] at hb; cases hb
          · omega
      · obtain ⟨h1, -⟩ := cr_T6 X Y i hW hu hp hb hpi2
        have hout := ccr_out_slant X.length i (q := p - 2) (by omega)
        rw [show p - 2 + 2 = p by omega] at hout
        exact Or.inr (cr_spec X Y i hW hu h1 hp (by omega) (Or.inr ⟨by omega, by omega⟩) (Or.inl (by omega)) hout)

theorem cr_slot_ne : ∀ j j', j < 5 → j' < 5 → j ≠ j' → (crChain X Y i e hW).slot hW j ≠ (crChain X Y i e hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  have hab := posA_ne_posB i e
  have hi := cr_i_pos X Y i hW
  have := posA_le i e
  have := posB_le i e
  have s0 := cr_s0 X Y i e hW
  have s1 := cr_s1 X Y i e hW he
  have s2 := cr_s2 X Y i e hW he
  have s3 := cr_s3 X Y i e hW he
  have s4 := cr_s4 X Y i e hW he
  interval_cases j <;> interval_cases j' <;> first | exact absurd rfl hne | (
    simp only [s0, s1, s2, s3, s4, Prod.mk.injEq] at h'; omega)

theorem cr_prevOut : Unch .std hW (crMv X Y i) (prev hW (crChain X Y i e hW).u₀) ∧
    PieceOut (ccLr X.length i) hW (ptv .std) (prev hW (crChain X Y i e hW).u₀) := by
  rcases cr_rest X Y i e hW he (prev hW (crChain X Y i e hW).u₀) with ⟨j, hj, hjs⟩ | h
  · exfalso
    have : (crChain X Y i e hW).slot hW (j + 1) = (crChain X Y i e hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact cr_slot_ne X Y i e hW he (j + 1) 0 (by omega) (by omega) (by omega) this
  · exact h

theorem cr_stopOut : Unch .std hW (crMv X Y i) ((crChain X Y i e hW).slot hW 4) ∧
    PieceOut (ccLr X.length i) hW (ptv .std) ((crChain X Y i e hW).slot hW 4) := by
  rcases cr_rest X Y i e hW he ((crChain X Y i e hW).slot hW 4) with ⟨j, hj, hjs⟩ | h
  · exact absurd hjs (cr_slot_ne X Y i e hW he j 4 (by omega) (by omega) (by omega))
  · exact h

theorem cr_touch : ∀ u : Slot Vr, PieceOut (ccLr X.length i) hW (ptv .std) u → pt .std Vr u.1 ∈ polygon (ccLr X.length i) →
    u = (crChain X Y i e hW).slot hW 4 := by
  intro u hout hmem
  have hi := cr_i_pos X Y i hW
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu] at hmem
  have hchain : ∀ j', j' < 4 → u ≠ (crChain X Y i e hW).slot hW j' := by
    intro j' hj' he'
    rw [he'] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (cr_chain_in X Y i e hW he j' hj').2
  by_cases hp : p = 0
  · subst hp
    rw [std_pt_cusp] at hmem
    rcases ccr_mem_cusp X.length i _ hmem with rfl | rfl
    · exfalso
      have := vertex_not_crossing hu
      rw [(cr_letters X Y i).1] at this
      simp [isCrossing] at this
    · exact absurd (Subtype.ext (hu.trans (cr_s2 X Y i e hW he).symm)) (hchain 2 (by norm_num))
  · rw [std_pt_cut _ hp] at hmem
    obtain ⟨hj, hp'⟩ := ccr_mem_cut X.length i hmem
    have hpos : p = posA i e ∨ p = posB i e := by cases e <;> simp only [posA, posB] <;> omega
    rcases hj with rfl | rfl
    · rcases hpos with rfl | rfl
      · exact absurd (Subtype.ext (hu.trans (cr_s0 X Y i e hW).symm)) (hchain 0 (by norm_num))
      · exact Subtype.ext (hu.trans (cr_s4 X Y i e hW he).symm)
    · rcases hpos with rfl | rfl
      · exact absurd (Subtype.ext (hu.trans (cr_s3 X Y i e hW he).symm)) (hchain 3 (by norm_num))
      · exact absurd (Subtype.ext (hu.trans (cr_s1 X Y i e hW he).symm)) (hchain 1 (by norm_num))

omit he in
theorem cr_exits : ∀ u : Slot Vr, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch .std hW (crMv X Y i) v ∧
    PieceOut (ccLr X.length i) hW (ptv .std) v := by
  intro u
  have hno : ∀ k', X.length ≤ k' → k' < X.length + 2 → ∀ m d, letterAt Vr k' ≠ .l m d := by
    intro k' h1 h2 m d
    have : k' = X.length ∨ k' = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rw [(cr_letters X Y i).1]; exact fun h => by cases h
    · rw [(cr_letters X Y i).2]; exact fun h => by cases h
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_l hW X.length (X.length + 2) hno u
  exact ⟨v, hsc, unch_of_extCol .std hW _ (cr_hmv X Y i hW) hcol,
    pieceOut_of_extCol _ .std hW _ (ccr_xge_mem _ _) (ccr_xle_mem _ _) (unch_pt _ _ _) hcol⟩

omit hW he in
theorem cr_kink : ∃ (k₀ m₀ : ℕ) (_hk₀ : k₀ < (Vr).length) (_hℓ₀ : letterAt Vr k₀ = .σ m₀), ¬ ExtCol X Pr k₀ ∧
    ∀ (k m : ℕ) (_hk : k < (Vr).length) (_hℓ : letterAt Vr k = .σ m), ¬ ExtCol X Pr k → k = k₀ :=
  ⟨X.length, i, by rw [cr_length]; omega, (cr_letters X Y i).1, by rw [cr_extCol]; omega,
    fun k m _ hℓ hext => (cr_σcol X Y i hℓ hext).1⟩

theorem cr_hKout : ∀ (k' m : ℕ) (hk : k' < (Vr).length) (hℓ : letterAt Vr k' = .σ m),
    ExtCol X Pr k' ↔ PieceOut (ccLr X.length i) hW (ptv .std) (σSlotA hW hk hℓ) := by
  intro k' m hk hℓ
  constructor
  · intro hext
    exact pieceOut_of_extCol _ .std hW _ (ccr_xge_mem _ _) (ccr_xle_mem _ _) (unch_pt _ _ _)
      (by rw [(σSlotA_spec hW hk hℓ).1]; exact (cr_extCol X i k').1 hext)
  · intro hout
    by_contra hext
    obtain ⟨rfl, rfl⟩ := cr_σcol X Y i hℓ hext
    obtain ⟨j, hj, hjs⟩ := cr_σA_chain X Y i e hW he hk hℓ
    rw [← hjs] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (cr_chain_in X Y i e hW he j hj).2

theorem cr_col0 : colOf ((crChain X Y i e hW).slot hW 0) = X.length := by
  have hi := cr_i_pos X Y i hW
  have := posA_le i e
  rw [block_col_true (cr_s0 X Y i e hW) (by omega) (cr_bitA0 X Y i e hW he)]

theorem cr_col1 : colOf ((crChain X Y i e hW).slot hW 1) = X.length + 1 := by
  have hi := cr_i_pos X Y i hW
  have := posB_le i e
  rw [block_col_true (cr_s1 X Y i e hW he) (by omega) (cr_bitB1 X Y i e hW he)]

theorem cr_col2 : colOf ((crChain X Y i e hW).slot hW 2) = X.length + 1 := block_col_vertex (cr_s2 X Y i e hW he)

theorem cr_col3 : colOf ((crChain X Y i e hW).slot hW 3) = X.length := by
  have hi := cr_i_pos X Y i hW
  have := posA_le i e
  rw [block_col_false (cr_s3 X Y i e hW he) (by omega) (cr_bitA1 X Y i e hW he)]; omega

/-- the two arms meet only at the cusp vertex -/
theorem cr_meet12 : MeetSpec .std hW (crMv X Y i) (ExtCol X Pr) ((crChain X Y i e hW).slot hW 1)
    ((crChain X Y i e hW).slot hW 2) := by
  intro τ τ' h0 h1 h0' h1' hEq
  have e1 : next hW ((crChain X Y i e hW).slot hW 1) = (crChain X Y i e hW).slot hW 2 := (Chain.slot_succ hW _ 1).symm
  have e2 : next hW ((crChain X Y i e hW).slot hW 2) = (crChain X Y i e hW).slot hW 3 := (Chain.slot_succ hW _ 2).symm
  rw [e1, e2, cr_mv1 X Y i e hW he, cr_mv2 X Y i e hW he, cr_mv3 X Y i e hW he] at hEq
  have hx := congrArg Prod.fst hEq
  have hy := congrArg Prod.snd hEq
  simp only [segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy
  refine Or.inr (Or.inl ⟨e1.symm, ?_, ?_⟩)
  · cases e <;> simp only [hA, hB] at hy <;> linarith
  · cases e <;> simp only [hA, hB] at hy <;> linarith

/-- the two crossing pieces of the moved diagram do not meet -/
theorem cr_meet03 : MeetSpec .std hW (crMv X Y i) (ExtCol X Pr) ((crChain X Y i e hW).slot hW 0)
    ((crChain X Y i e hW).slot hW 3) := by
  intro τ τ' h0 h1 h0' h1' hEq
  have e1 : next hW ((crChain X Y i e hW).slot hW 0) = (crChain X Y i e hW).slot hW 1 := (Chain.slot_succ hW _ 0).symm
  have e2 : next hW ((crChain X Y i e hW).slot hW 3) = (crChain X Y i e hW).slot hW 4 := (Chain.slot_succ hW _ 3).symm
  rw [e1, e2, cr_mv0 X Y i e hW, cr_mv1 X Y i e hW he, cr_mv3 X Y i e hW he, cr_mv4 X Y i e hW he] at hEq
  have hx := congrArg Prod.fst hEq
  have hy := congrArg Prod.snd hEq
  simp only [segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy
  exfalso
  cases e <;> simp only [hA, hB, posA, posB] at hx hy <;> push_cast at hx hy <;> linarith

theorem cr_pairs : ∀ j j', j < 4 → j' < 4 → (crChain X Y i e hW).slot hW j ≠ (crChain X Y i e hW).slot hW j' →
    colOf ((crChain X Y i e hW).slot hW j) = colOf ((crChain X Y i e hW).slot hW j') →
    MeetSpec .std hW (crMv X Y i) (ExtCol X Pr) ((crChain X Y i e hW).slot hW j) ((crChain X Y i e hW).slot hW j') := by
  intro j j' hj hj' hne hc
  have c0 := cr_col0 X Y i e hW he
  have c1 := cr_col1 X Y i e hW he
  have c2 := cr_col2 X Y i e hW he
  have c3 := cr_col3 X Y i e hW he
  interval_cases j <;> interval_cases j'
  · exact absurd rfl hne
  · rw [c0, c1] at hc; omega
  · rw [c0, c2] at hc; omega
  · exact cr_meet03 X Y i e hW he
  · rw [c1, c0] at hc; omega
  · exact absurd rfl hne
  · exact cr_meet12 X Y i e hW he
  · rw [c1, c3] at hc; omega
  · rw [c2, c0] at hc; omega
  · exact (cr_meet12 X Y i e hW he).symm
  · exact absurd rfl hne
  · rw [c2, c3] at hc; omega
  · exact (cr_meet03 X Y i e hW he).symm
  · rw [c3, c1] at hc; omega
  · rw [c3, c2] at hc; omega
  · exact absurd rfl hne

theorem cr_genericData : GenericData .std hW (crMv X Y i) (ExtCol X Pr) :=
  genericData_of (ccLr X.length i) .std hW (crMv X Y i) (ExtCol X Pr) (crChain X Y i e hW)
    (mv2_injective _ _ _ _ _ (by norm_num) (nonGrid_three_quarter i) (nonGrid_quarter i))
    (mv2_xcoord _ _ _ _ _ (cr_i_pos X Y i hW)) (cr_rest X Y i e hW he) (fun j hj => (cr_chain_in X Y i e hW he j hj).1)
    (cr_pairs X Y i e hW he) (fun k m hk hℓ hA hB => (cr_hK X Y i e hW he k m hk hℓ).2 ⟨hA, hB⟩)

theorem cr_riSpec : RISpec (ccLr X.length i) .std hW (crMv X Y i) (ExtCol X Pr) (crChain X Y i e hW) where
  disc := ccLr_isDisc _ _
  hK := cr_hK X Y i e hW he
  hKout := cr_hKout X Y i e hW he
  moved := cr_moved X Y i hW
  chain := cr_chain_in X Y i e hW he
  vert := cr_vert X Y i e hW he
  rest := cr_rest X Y i e hW he
  prevOut := cr_prevOut X Y i e hW he
  stopOut := cr_stopOut X Y i e hW he
  touch := cr_touch X Y i e hW he
  exits := cr_exits X Y i hW
  kink := cr_kink X Y i

theorem cr_riData (hne : Vr ≠ []) :
    Nonempty (RIData (polygon (ccLr X.length i))
      (mvDiagram .std hW hne (crMv X Y i) (ExtCol X Pr) (cr_genericData X Y i e hW he)) (rlDiagram .std hW hne)) :=
  riData_of hne (cr_genericData X Y i e hW he) (cr_riSpec X Y i e hW he)

theorem cr_recordIso (hne : Vr ≠ []) (W' : OWord) (hW'eq : W'.letters = Vr') :
    Nonempty (RecordIso (mvDiagram .std hW hne (crMv X Y i) (ExtCol X Pr) (cr_genericData X Y i e hW he)).record
      (realize W').diagram.record) := by
  have hW' : (Vr').Closed := by have := W'.closed; rwa [hW'eq] at this
  refine ⟨vertexMovedRecordIso' X Pr Y Pr' (by simp) (cr_sameEffect X Y i hW) hW hW' .std hne _ _ _ _
    (slotDiagramData_of .std hW hne (crMv X Y i) (ExtCol X Pr) (cr_genericData X Y i e hW he) (cr_hK X Y i e hW he))
    (cr_passage X Y i hW hW') (cr_hexit X Y i hW) (cr'_hexit X Y i hW') ?_ W' hW'eq (by simp)⟩
  intro k' hk1 hk2
  simp only [List.length_cons, List.length_nil] at hk2
  have : k' = X.length := by omega
  subst this
  rw [cr'_letters X Y i]; rfl

omit hW he in
/-- LEAF CASE (crossed cusp, right variant `σ_i r_i ↦ r_i`). -/
theorem crossedCusp_right {W W' : OWord} (hWeq : W.letters = Vr) (hW'eq : W'.letters = Vr') :
    ∃ D : Diagram, RI D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨Wl, hWl⟩ := W
  simp only at hWeq
  subst hWeq
  have hne : Vr ≠ [] := by simp
  rw [realize_eq_realizeAt ⟨_, hWl⟩ hne]
  exact ⟨mvDiagram .std hWl hne (crMv X Y i) (ExtCol X Pr) (cr_genericData X Y i _ hWl rfl),
    ⟨polygon (ccLr X.length i), Or.inl (cr_riData X Y i _ hWl rfl hne)⟩, cr_recordIso X Y i _ hWl rfl hne W' hW'eq⟩

end CrossedCuspRightGeom

/-! #### D. The leaf `crossedCusp_move` -/

/-- ng:deletions, crossed-cusp shortcut: both variants. -/
theorem crossedCusp_move_proof {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨X, Y, i, -, ⟨d, hWeq, hW'eq⟩ | ⟨hWeq, hW'eq⟩⟩ := h
  · exact crossedCusp_left X Y i d hWeq hW'eq
  · exact crossedCusp_right X Y i hWeq hW'eq

/-! #### E. The front type-I move, left variant `l_m d σ_{m−1} r_m ↦ (nothing)` (ng:front-I, sm-3:1955-1963) -/

/-- the ten vertices of the type-I curl `l_m σ_{m−1} r_m`, in the traversal order of a rightward through-strand -/
def tv (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k, m - 1)
  | 1 => (k + 1, m - 1)
  | 2 => (k + 2, m)
  | 3 => (k + 2, 0)
  | 4 => (k + 2, m + 1)
  | 5 => (k + 1, m + 1)
  | 6 => (k, 0)
  | 7 => (k + 1, m)
  | 8 => (k + 2, m - 1)
  | _ => (k + 3, m - 1)

/-- the chain vertex `j` of the curl: `tv j` for a rightward through-strand, `tv (9 − j)` for a leftward one -/
def tvd (k m : ℕ) (d : Bool) (j : ℕ) : ℕ × ℕ := if d then tv k m j else tv k m (9 - j)

section TypeILeftWord

open U3

variable (X Y : Word) (m : ℕ) (d : Bool) (hm : 2 ≤ m) (hW : (X ++ [Letter.l m d, Letter.σ (m - 1), Letter.r m] ++ Y).Closed)

local notation "Vt" => X ++ [Letter.l m d, Letter.σ (m - 1), Letter.r m] ++ Y
local notation "Pt" => [Letter.l m d, Letter.σ (m - 1), Letter.r m]

theorem tl_letters : letterAt Vt X.length = .l m d ∧ letterAt Vt (X.length + 1) = .σ (m - 1) ∧
    letterAt Vt (X.length + 2) = .r m := by
  refine ⟨?_, ?_, ?_⟩
  · have := letterAt_block X Pt Y (i := 0) (by simp); simpa using this
  · have := letterAt_block X Pt Y (i := 1) (by simp); simpa using this
  · have := letterAt_block X Pt Y (i := 2) (by simp); simpa using this

theorem tl_length : (Vt).length = X.length + 3 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem tl_extCol (k : ℕ) : ExtCol X Pt k ↔ k + 1 ≤ X.length ∨ X.length + 3 ≤ k := by
  unfold ExtCol; simp

theorem tl_shift : shiftIdx X Pt [] (X.length + 3) = X.length := by
  unfold shiftIdx; simp

include hW

include hm in
theorem tl_sameEffect : SameEffect X Pt [] :=
  sameEffect_of_replace X Pt Y [] hW (fun c c' h => by obtain rfl := run_typeI_left hm h; rfl)

include hm in
theorem tl_cut_end : cut Vt (X.length + 3) = cut Vt X.length := by
  have hE := tl_sameEffect X Y m d hm hW
  unfold SameEffect at hE
  unfold cut
  rw [List.take_left' (by simp), List.append_assoc, List.take_left' rfl, hE, List.append_nil]

theorem tl_cutlen : m - 1 ≤ (cut Vt X.length).length := by
  have hk : X.length < (Vt).length := by rw [tl_length]; omega
  obtain ⟨D⟩ := decomp hW X.length hk
  have h1 := D.length_c
  have hidx : (letterAt Vt X.length).idx = m := by rw [(tl_letters X Y m d).1]; rfl
  have har : (letterAt Vt X.length).arity = 0 := by rw [(tl_letters X Y m d).1]; rfl
  omega

include hm in
/-- the bits of the curl: the through-strand travels with the cusp bit `d` everywhere -/
theorem tl_bits :
    bit Vt X.length (m - 1) = d ∧ bit Vt (X.length + 1) (m - 1) = d ∧ bit Vt (X.length + 1) m = d ∧
    bit Vt (X.length + 1) (m + 1) = !d ∧ bit Vt (X.length + 2) (m - 1) = d ∧ bit Vt (X.length + 2) m = d ∧
    bit Vt (X.length + 2) (m + 1) = !d ∧ bit Vt (X.length + 3) (m - 1) = d := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tl_letters X Y m d
  have hk₀ : X.length < (Vt).length := by rw [tl_length]; omega
  have hk₁ : X.length + 1 < (Vt).length := by rw [tl_length]; omega
  have hk₂ : X.length + 2 < (Vt).length := by rw [tl_length]; omega
  obtain ⟨-, B1, B2⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, -, -, h4, h5⟩ := σ_facts hW hk₁ hℓ₁
  rw [show m - 1 + 1 = m by omega] at h4 h5
  obtain ⟨-, h6⟩ := r_bits hW hk₂ hℓ₂
  have B7 : bit Vt (X.length + 2) (m + 1) = !d := by
    have := bit_succ_of_ge hW hk₁ (p := m + 1) (by rw [hℓ₁]; simp only [idx, arity]; omega)
    rw [hℓ₁] at this
    simp only [coarity, arity] at this
    rw [show m + 1 + 2 - 2 = m + 1 by omega] at this
    rw [this, B2]
  have B6 : bit Vt (X.length + 2) m = d := by
    rw [B7] at h6
    exact bool_eq_of_not_ne h6.symm
  have B3 : bit Vt (X.length + 1) (m - 1) = d := by rw [← h4, B6]
  have B0 : bit Vt X.length (m - 1) = d := by
    rw [← bit_succ_of_lt hW hk₀ (by omega) (by rw [hℓ₀]; simp only [idx]; omega), B3]
  have B5 : bit Vt (X.length + 2) (m - 1) = d := by rw [h5, B1]
  have B8 : bit Vt (X.length + 3) (m - 1) = d := by
    rw [bit_succ_of_lt hW hk₂ (by omega) (by rw [hℓ₂]; simp only [idx]; omega), B5]
  exact ⟨B0, B3, B1, B2, B5, B6, B7, B8⟩

/-! the successor table of the block `l_m σ_{m−1} r_m` (columns `|X|`, `|X|+1`, `|X|+2`) -/

theorem tl_T1 {s : Slot Vt} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vt X.length p = true)
    (hpm : p < m) : (next hW s).1 = (X.length + 1, p) ∧ bit Vt (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(tl_letters X Y m d).1]; exact hpm)

theorem tl_T2 {s : Slot Vt} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vt X.length p = true)
    (hpm : m ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Vt (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(tl_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(tl_letters X Y m d).1] at this

theorem tl_T3 {s : Slot Vt} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vt (X.length + 1) p = true) (hpm : p < m - 1) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vt (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(tl_letters X Y m d).2.1]; exact hpm)

include hm in
theorem tl_T4 {s : Slot Vt} (hs : s.1 = (X.length + 1, m - 1)) (hb : bit Vt (X.length + 1) (m - 1) = true) :
    (next hW s).1 = (X.length + 2, m) := by
  have := next_σ_right_idx hW (tl_letters X Y m d).2.1 hs hb
  rwa [show m - 1 + 1 = m by omega] at this

include hm in
theorem tl_T5 {s : Slot Vt} (hs : s.1 = (X.length + 1, m)) (hb : bit Vt (X.length + 1) m = true) :
    (next hW s).1 = (X.length + 2, m - 1) :=
  next_σ_right_succ hW (tl_letters X Y m d).2.1 (by rw [hs, show m - 1 + 1 = m by omega])
    (by rw [show m - 1 + 1 = m by omega]; exact hb)

include hm in
theorem tl_T6 {s : Slot Vt} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vt (X.length + 1) p = true) (hpm : m + 1 ≤ p) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vt (X.length + 2) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(tl_letters X Y m d).2.1]; simp only [idx, arity]; omega)
  rw [(tl_letters X Y m d).2.1] at this
  simpa [coarity, arity] using this

theorem tl_T7 {s : Slot Vt} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vt (X.length + 2) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 3, p) ∧ bit Vt (X.length + 3) p = true :=
  next_right_lt hW hs hp hb (by rw [(tl_letters X Y m d).2.2]; exact hpm)

theorem tl_T8 {s : Slot Vt} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p = m ∨ p = m + 1)
    (hb : bit Vt (X.length + 2) p = true) : (next hW s).1 = (X.length + 2, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (tl_letters X Y m d).2.2 hs hp hb

theorem tl_T9 {s : Slot Vt} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vt (X.length + 2) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 3, p - 2) ∧ bit Vt (X.length + 3) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(tl_letters X Y m d).2.2]; simpa [idx, arity] using hpm)
  rw [(tl_letters X Y m d).2.2] at this
  simpa [coarity, arity] using this

theorem tl_T10 {s : Slot Vt} (hs : s.1 = (X.length + 2, 0)) :
    (next hW s).1 = (X.length + 2, if bit Vt (X.length + 2) m then m + 1 else m) :=
  next_cusp_r hW (tl_letters X Y m d).2.2 hs

theorem tl_T11 {s : Slot Vt} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vt (X.length + 1) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length, q) ∧ bit Vt X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (tl_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem tl_T12 {s : Slot Vt} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m ∨ q = m + 1)
    (hb : bit Vt (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (tl_letters X Y m d).1 hs hq hb

theorem tl_T13 {s : Slot Vt} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vt (X.length + 1) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Vt X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (tl_letters X Y m d).1]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, (tl_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem tl_T14 {s : Slot Vt} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m else m + 1) :=
  next_cusp_l hW (tl_letters X Y m d).1 hs

theorem tl_T15 {s : Slot Vt} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vt (X.length + 2) q = false) (hqm : q < m - 1) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vt (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e2, (tl_letters X Y m d).2.1]; exact hqm)
  rwa [e2] at this

include hm in
theorem tl_T16 {s : Slot Vt} (hs : s.1 = (X.length + 2, m - 1)) (hb : bit Vt (X.length + 2) (m - 1) = false) :
    (next hW s).1 = (X.length + 1, m) := by
  have := next_σ_left_idx hW (tl_letters X Y m d).2.1 hs hb
  rwa [show m - 1 + 1 = m by omega] at this

include hm in
theorem tl_T17 {s : Slot Vt} (hs : s.1 = (X.length + 2, m)) (hb : bit Vt (X.length + 2) m = false) :
    (next hW s).1 = (X.length + 1, m - 1) :=
  next_σ_left_succ hW (tl_letters X Y m d).2.1 (by rw [hs, show m - 1 + 1 = m by omega])
    (by rw [show m - 1 + 1 = m by omega]; exact hb)

include hm in
theorem tl_T18 {s : Slot Vt} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vt (X.length + 2) q = false) (hqm : m + 1 ≤ q) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vt (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e2, (tl_letters X Y m d).2.1]; simp only [idx, coarity]; omega)
  rw [e2, (tl_letters X Y m d).2.1] at this
  simpa [arity, coarity] using this

theorem tl_T19 {s : Slot Vt} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vt (X.length + 3) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 2, q) ∧ bit Vt (X.length + 2) q = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_lt hW hs hq hb (by rw [e3, (tl_letters X Y m d).2.2]; exact hqm)
  rwa [e3] at this

theorem tl_T20 {s : Slot Vt} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vt (X.length + 3) q = false) (hqm : m ≤ q) :
    (next hW s).1 = (X.length + 2, q + 2) ∧ bit Vt (X.length + 2) (q + 2) = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_ge hW hs hq hb (by rw [e3, (tl_letters X Y m d).2.2]; simpa [idx, coarity] using hqm)
  rw [e3, (tl_letters X Y m d).2.2] at this
  simpa [arity, coarity] using this

/-! the chain of the curl -/

include hm in
theorem tl_isSlot_u0 : IsSlot Vt (tvd X.length m d 0) := by
  have h1 := tl_cutlen X Y m d hW
  have h2 := tl_cut_end X Y m d hm hW
  have hlen := tl_length X Y m d
  cases d
  · have e0 : tvd X.length m false 0 = (X.length + 3, m - 1) := rfl
    rw [e0]
    exact isSlot_cut (by omega) (by rw [h2]; exact h1) (by omega)
  · have e0 : tvd X.length m true 0 = (X.length, m - 1) := rfl
    rw [e0]
    exact isSlot_cut (by omega) h1 (by omega)

include hm in
/-- the arc of the curl in the realization: nine pieces from the entry of the through-strand -/
def tlChain : Chain Vt := ⟨⟨tvd X.length m d 0, tl_isSlot_u0 X Y m d hm hW⟩, 9, by norm_num⟩

include hm in
theorem tl_slot_val : ∀ j, j ≤ 9 → ((tlChain X Y m d hm hW).slot hW j).1 = tvd X.length m d j := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩ := tl_bits X Y m d hm hW
  have s0 : ((tlChain X Y m d hm hW).slot hW 0).1 = tvd X.length m d 0 := rfl
  intro j hj
  cases d
  · -- leftward through-strand: the vertices in reverse
    simp only [tvd, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((tlChain X Y m false hm hW).slot hW 1).1 = tv X.length m 8 := by
      rw [Chain.slot_succ]; exact (tl_T19 X Y m false hW s0 (by omega) B7 (by omega)).1
    have s2 : ((tlChain X Y m false hm hW).slot hW 2).1 = tv X.length m 7 := by
      rw [Chain.slot_succ]; exact tl_T16 X Y m false hm hW s1 B4
    have s3 : ((tlChain X Y m false hm hW).slot hW 3).1 = tv X.length m 6 := by
      rw [Chain.slot_succ]; exact tl_T12 X Y m false hW s2 (Or.inl rfl) B2
    have s4 : ((tlChain X Y m false hm hW).slot hW 4).1 = tv X.length m 5 := by
      rw [Chain.slot_succ, tl_T14 X Y m false hW s3]; rfl
    have s5 : ((tlChain X Y m false hm hW).slot hW 5).1 = tv X.length m 4 := by
      rw [Chain.slot_succ]; exact (tl_T6 X Y m false hm hW s4 (by omega) B3 le_rfl).1
    have s6 : ((tlChain X Y m false hm hW).slot hW 6).1 = tv X.length m 3 := by
      rw [Chain.slot_succ]; exact tl_T8 X Y m false hW s5 (Or.inr rfl) B6
    have s7 : ((tlChain X Y m false hm hW).slot hW 7).1 = tv X.length m 2 := by
      rw [Chain.slot_succ, tl_T10 X Y m false hW s6, B5]; rfl
    have s8 : ((tlChain X Y m false hm hW).slot hW 8).1 = tv X.length m 1 := by
      rw [Chain.slot_succ]; exact tl_T17 X Y m false hm hW s7 B5
    have s9 : ((tlChain X Y m false hm hW).slot hW 9).1 = tv X.length m 0 := by
      rw [Chain.slot_succ]; exact (tl_T11 X Y m false hW s8 (by omega) B1 (by omega)).1
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
    · exact s8
    · exact s9
  · simp only [tvd, ↓reduceIte] at s0 ⊢
    have s1 : ((tlChain X Y m true hm hW).slot hW 1).1 = tv X.length m 1 := by
      rw [Chain.slot_succ]; exact (tl_T1 X Y m true hW s0 (by omega) B0 (by omega)).1
    have s2 : ((tlChain X Y m true hm hW).slot hW 2).1 = tv X.length m 2 := by
      rw [Chain.slot_succ]; exact tl_T4 X Y m true hm hW s1 B1
    have s3 : ((tlChain X Y m true hm hW).slot hW 3).1 = tv X.length m 3 := by
      rw [Chain.slot_succ]; exact tl_T8 X Y m true hW s2 (Or.inl rfl) B5
    have s4 : ((tlChain X Y m true hm hW).slot hW 4).1 = tv X.length m 4 := by
      rw [Chain.slot_succ, tl_T10 X Y m true hW s3, B5]; rfl
    have s5 : ((tlChain X Y m true hm hW).slot hW 5).1 = tv X.length m 5 := by
      rw [Chain.slot_succ]; exact (tl_T18 X Y m true hm hW s4 (by omega) B6 le_rfl).1
    have s6 : ((tlChain X Y m true hm hW).slot hW 6).1 = tv X.length m 6 := by
      rw [Chain.slot_succ]; exact tl_T12 X Y m true hW s5 (Or.inr rfl) B3
    have s7 : ((tlChain X Y m true hm hW).slot hW 7).1 = tv X.length m 7 := by
      rw [Chain.slot_succ, tl_T14 X Y m true hW s6]; rfl
    have s8 : ((tlChain X Y m true hm hW).slot hW 8).1 = tv X.length m 8 := by
      rw [Chain.slot_succ]; exact tl_T5 X Y m true hm hW s7 B2
    have s9 : ((tlChain X Y m true hm hW).slot hW 9).1 = tv X.length m 9 := by
      rw [Chain.slot_succ]; exact (tl_T7 X Y m true hW s8 (by omega) B4 (by omega)).1
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
    · exact s8
    · exact s9

end TypeILeftWord

section TypeILeftPassage

open U3

variable (X Y : Word) (m : ℕ) (d : Bool) (hm : 2 ≤ m) (hW : (X ++ [Letter.l m d, Letter.σ (m - 1), Letter.r m] ++ Y).Closed)

local notation "Vt" => X ++ [Letter.l m d, Letter.σ (m - 1), Letter.r m] ++ Y
local notation "Pt" => [Letter.l m d, Letter.σ (m - 1), Letter.r m]

/-- the column of the `j`-th piece of the curl (rightward through-strand) -/
def tcol (k : ℕ) : ℕ → ℕ
  | 0 => k
  | 1 => k + 1
  | 2 => k + 2
  | 3 => k + 2
  | 4 => k + 1
  | 5 => k
  | 6 => k
  | 7 => k + 1
  | _ => k + 2

include hm hW

theorem tl_col : ∀ j, j < 9 → colOf ((tlChain X Y m d hm hW).slot hW j) = if d then tcol X.length j else tcol X.length (8 - j) := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩ := tl_bits X Y m d hm hW
  have hv := tl_slot_val X Y m d hm hW
  intro j hj
  cases d
  · simp only [tvd, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp; omega) (by simpa [tv] using B7)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp; omega) (by simpa [tv] using B4)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp; omega) (by simpa [tv] using B2)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_true (hv 4 (by norm_num)) (by simp) (by simpa [tv] using B3)]; rfl
    · rw [block_col_true (hv 5 (by norm_num)) (by simp) (by simpa [tv] using B6)]; rfl
    · rw [block_col_vertex (hv 6 (by norm_num))]; rfl
    · rw [block_col_false (hv 7 (by norm_num)) (by simp; omega) (by simpa [tv] using B5)]; rfl
    · rw [block_col_false (hv 8 (by norm_num)) (by simp; omega) (by simpa [tv] using B1)]; rfl
  · simp only [tvd, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp; omega) (by simpa [tv] using B0)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp; omega) (by simpa [tv] using B1)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp; omega) (by simpa [tv] using B5)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_false (hv 4 (by norm_num)) (by simp) (by simpa [tv] using B6)]; rfl
    · rw [block_col_false (hv 5 (by norm_num)) (by simp) (by simpa [tv] using B3)]; rfl
    · rw [block_col_vertex (hv 6 (by norm_num))]; rfl
    · rw [block_col_true (hv 7 (by norm_num)) (by simp; omega) (by simpa [tv] using B2)]; rfl
    · rw [block_col_true (hv 8 (by norm_num)) (by simp; omega) (by simpa [tv] using B4)]; rfl

theorem tl_col_block : ∀ j, j < 9 → ¬ ExtCol X Pt (colOf ((tlChain X Y m d hm hW).slot hW j)) := by
  intro j hj
  rw [tl_col X Y m d hm hW j hj, tl_extCol]
  cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> interval_cases j <;> simp [tcol]

/-- the stop of the curl is an exterior piece -/
theorem tl_col9 : ExtCol X Pt (colOf ((tlChain X Y m d hm hW).slot hW 9)) := by
  obtain ⟨B0, -, -, -, -, -, -, B7⟩ := tl_bits X Y m d hm hW
  have hv := tl_slot_val X Y m d hm hW 9 le_rfl
  rw [tl_extCol]
  cases d
  · simp only [tvd, Bool.false_eq_true, ↓reduceIte, tv] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) B0]; omega
  · simp only [tvd, ↓reduceIte, tv] at hv
    rw [block_col_true hv (by omega) B7]; omega

/-- every component meets the exterior: a component inside the block would contain the right cusp, i.e. the curl -/
theorem tl_exits_core : ∀ u : Slot Vt, ∃ v, (nextPerm hW).SameCycle u v ∧ (colOf v + 1 ≤ X.length ∨ X.length + 3 ≤ colOf v) := by
  intro u
  by_contra hex
  have hall : ∀ v, (nextPerm hW).SameCycle u v → X.length ≤ colOf v ∧ colOf v < X.length + 3 := by
    intro v hv
    by_contra h
    exact hex ⟨v, hv, by omega⟩
  obtain ⟨⟨v, hsc, hv0, ⟨m', hℓ⟩, ha, hb⟩, -⟩ := exists_cusps_of_no_ext hW X.length (X.length + 3) u hall
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tl_letters X Y m d
  have hj : v.1.1 = X.length + 2 := by
    have : v.1.1 = X.length ∨ v.1.1 = X.length + 1 ∨ v.1.1 = X.length + 2 := by omega
    rcases this with h | h | h
    · rw [h, hℓ₀] at hℓ; cases hℓ
    · rw [h, hℓ₁] at hℓ; cases hℓ
    · exact h
  have hv : v.1 = (X.length + 2, 0) := Prod.ext hj hv0
  -- `v` is the chain vertex `tv 3`, at chain index `3` (rightward) or `6` (leftward)
  have hchain : ∃ j, j < 9 ∧ (tlChain X Y m d hm hW).slot hW j = v := by
    have hs := tl_slot_val X Y m d hm hW
    cases d
    · exact ⟨6, by norm_num, Subtype.ext ((hs 6 (by norm_num)).trans hv.symm)⟩
    · exact ⟨3, by norm_num, Subtype.ext ((hs 3 (by norm_num)).trans hv.symm)⟩
  obtain ⟨j, hj9, hjs⟩ := hchain
  have hsc9 : (nextPerm hW).SameCycle v ((tlChain X Y m d hm hW).slot hW 9) := by
    refine sameCycle_of_iterate hW (a := 9 - j) (b := 0) ?_
    rw [← hjs]
    show (next hW)^[9 - j] ((next hW)^[j] (tlChain X Y m d hm hW).u₀) = (next hW)^[9] (tlChain X Y m d hm hW).u₀
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
  have h9 := hall _ (hsc.trans hsc9)
  have := tl_col9 X Y m d hm hW
  rw [tl_extCol] at this
  omega

theorem tl_hexit : ∀ u : Slot Vt, ∃ n, ExtPiece X Pt Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨v, hsc, hcol⟩ := tl_exits_core X Y m d hm hW u
  obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW hsc
  exact ⟨n, by rw [hn]; show ExtCol X Pt (colOf v); rw [tl_extCol]; exact hcol⟩

/-- THE BLOCK PASSAGE of the curl: every through-strand exits at its own position (`P' = []`). -/
theorem tl_passage (hW' : (X ++ [] ++ Y).Closed) : Passage X Pt Y [] hW hW' := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tl_letters X Y m d
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩ := tl_bits X Y m d hm hW
  have hP : Pt ≠ [] := by simp
  have hE := tl_sameEffect X Y m d hm hW
  constructor
  intro b hext hcol
  have side : ∀ {c : Slot Vt}, extPair X Pt [] b.1 = extPair X Pt [] c.1 →
      ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pt [] b.1 ∧
        ((next hW')^[m'] b').1 = extPair X Pt [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) :=
    fun hbc => ⟨0, ⟨_, isSlot_ext X Pt Y [] hP hE b.2 hext⟩, rfl, hbc, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  have shiftL : ∀ p, extPair X Pt [] (X.length, p) = extPair X Pt [] (X.length + 3, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pt [] le_rfl, tl_shift X m d]
  -- the curl itself: `b` is the entry of the chain
  have curl : b = (tlChain X Y m d hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Vt), (next hW)^[n] b = c ∧ ExtCol X Pt (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pt (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pt [] b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pt [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨9, (tlChain X Y m d hm hW).slot hW 9, by rw [hb]; rfl, tl_col9 X Y m d hm hW, ?_, side ?_⟩
    · intro i hi
      have := tl_col_block X Y m d hm hW i hi
      rwa [hb] at *
    · rw [hb]
      have h0 := tl_slot_val X Y m d hm hW 0 (by norm_num)
      have h9 := tl_slot_val X Y m d hm hW 9 le_rfl
      rw [Chain.slot_zero] at h0
      rw [h0, h9]
      cases d
      · simp only [tvd, Bool.false_eq_true, ↓reduceIte, tv]; exact (shiftL _).symm
      · simp only [tvd, ↓reduceIte, tv]; exact shiftL _
  rcases (entry_iff X Pt Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hcol0 : ¬ ExtCol X Pt (colOf b) := by rw [block_col_true hb hp hbit, tl_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · rcases Nat.eq_or_lt_of_le (Nat.le_sub_one_of_lt hpm) with hpe | hpe
      · -- `p = m − 1`: the through-strand, `d = true`
        have hd : d = true := by rw [hpe, B0] at hbit; exact hbit
        apply curl
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvd X.length m d 0
        rw [hd]; rfl
      · obtain ⟨h1, hb1⟩ := tl_T1 X Y m d hW hb hp hbit hpm
        obtain ⟨h2, hb2⟩ := tl_T3 X Y m d hW h1 hp hb1 (by omega)
        obtain ⟨h3, hb3⟩ := tl_T7 X Y m d hW h2 hp hb2 hpm
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pt) hcol0
          (passage_step hW (ExtCol X Pt) (by rw [block_col_true h1 hp hb1, tl_extCol]; omega)
          (passage_step hW (ExtCol X Pt) (by rw [block_col_true h2 hp hb2, tl_extCol]; omega) (passage_end hW)))
        refine ⟨n, _, hc, by rw [block_col_true h3 hp hb3, tl_extCol]; omega, hmin, side ?_⟩
        rw [hb, h3]; exact shiftL p
    · obtain ⟨h1, hb1⟩ := tl_T2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := tl_T6 X Y m d hm hW h1 (by omega) hb1 (by omega)
      obtain ⟨h3, hb3⟩ := tl_T9 X Y m d hW h2 (by omega) hb2 (by omega)
      rw [show p + 2 - 2 = p by omega] at h3 hb3
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pt) hcol0
        (passage_step hW (ExtCol X Pt) (by rw [block_col_true h1 (by omega) hb1, tl_extCol]; omega)
        (passage_step hW (ExtCol X Pt) (by rw [block_col_true h2 (by omega) hb2, tl_extCol]; omega) (passage_end hW)))
      refine ⟨n, _, hc, by rw [block_col_true h3 hp hb3, tl_extCol]; omega, hmin, side ?_⟩
      rw [hb, h3]; exact shiftL p
  · -- from the right at `(|X|+3, q)`
    replace hb : b.1 = (X.length + 3, p) := hb
    replace hbit : bit Vt (X.length + 3) p = false := hbit
    have hcol0 : ¬ ExtCol X Pt (colOf b) := by rw [block_col_false hb hp hbit, tl_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · rcases Nat.eq_or_lt_of_le (Nat.le_sub_one_of_lt hpm) with hpe | hpe
      · have hd : d = false := by rw [hpe, B7] at hbit; exact hbit
        apply curl
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvd X.length m d 0
        rw [hd]; rfl
      · obtain ⟨h1, hb1⟩ := tl_T19 X Y m d hW hb hp hbit hpm
        obtain ⟨h2, hb2⟩ := tl_T15 X Y m d hW h1 hp hb1 (by omega)
        obtain ⟨h3, hb3⟩ := tl_T11 X Y m d hW h2 hp hb2 hpm
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pt) hcol0
          (passage_step hW (ExtCol X Pt) (by rw [block_col_false h1 hp hb1, tl_extCol]; omega)
          (passage_step hW (ExtCol X Pt) (by rw [block_col_false h2 hp hb2, tl_extCol]; omega) (passage_end hW)))
        have hk3 := (cutSlot_facts hW h3 hp).2.2.1
        refine ⟨n, _, hc, by rw [block_col_false h3 hp hb3, tl_extCol]; omega, hmin, side ?_⟩
        rw [hb, h3]; exact (shiftL p).symm
    · obtain ⟨h1, hb1⟩ := tl_T20 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := tl_T18 X Y m d hm hW h1 (by omega) hb1 (by omega)
      obtain ⟨h3, hb3⟩ := tl_T13 X Y m d hW h2 (by omega) hb2 (by omega)
      rw [show p + 2 - 2 = p by omega] at h3 hb3
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pt) hcol0
        (passage_step hW (ExtCol X Pt) (by rw [block_col_false h1 (by omega) hb1, tl_extCol]; omega)
        (passage_step hW (ExtCol X Pt) (by rw [block_col_false h2 (by omega) hb2, tl_extCol]; omega) (passage_end hW)))
      have hk3 := (cutSlot_facts hW h3 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 hp hb3, tl_extCol]; omega, hmin, side ?_⟩
      rw [hb, h3]; exact (shiftL p).symm

end TypeILeftPassage

/-! #### E3. The type-I disc family and the segment-pair helpers -/

section TIDisc

/-- the type-I disc with top height `h`: `[k, k+3] × [h−5/2, h+3/4]` cut by the two slanted lines
`y ≥ h − 3/4 − 2(x − k)` and `y ≥ h − 3/4 + 2(x − (k+3))` (one unit above the spectator trough) -/
def tL (k : ℕ) (h : ℝ) : List HalfPlane :=
  [HalfPlane.xge (k : ℝ), HalfPlane.xle ((k : ℝ) + 3), HalfPlane.yle (h + 3 / 4), HalfPlane.yge (h - 5 / 2),
    HalfPlane.above (h - 3 / 4 + 2 * k) (-2), HalfPlane.above (h - 3 / 4 - 2 * ((k : ℝ) + 3)) 2]

macro "tI_mem" : tactic => `(tactic| (
  simp only [tL, mem_polygon_iff, mem_interior_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, or_false, HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle,
    HalfPlane.b_yle, HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith))

variable (k : ℕ) (h : ℝ)

theorem tI_int_cut1 (r : ℝ) (hr1 : -5 / 2 < r) (hr2 : r < 3 / 4) :
    (((k + 1 : ℕ) : ℝ), h + r) ∈ interior (polygon (tL k h)) := by push_cast; tI_mem
theorem tI_int_cut2 (r : ℝ) (hr1 : -5 / 2 < r) (hr2 : r < 3 / 4) :
    (((k + 2 : ℕ) : ℝ), h + r) ∈ interior (polygon (tL k h)) := by push_cast; tI_mem
theorem tI_int_cuspL (r : ℝ) (hr1 : -7 / 4 < r) (hr2 : r < 3 / 4) :
    ((k : ℝ) + 1 / 2, h + r) ∈ interior (polygon (tL k h)) := by tI_mem
theorem tI_int_cuspR (r : ℝ) (hr1 : -7 / 4 < r) (hr2 : r < 3 / 4) :
    (((k + 2 : ℕ) : ℝ) + 1 / 2, h + r) ∈ interior (polygon (tL k h)) := by push_cast; tI_mem
theorem tI_mem_left : ((k : ℝ), h) ∈ polygon (tL k h) := by tI_mem
theorem tI_mem_right : (((k + 3 : ℕ) : ℝ), h) ∈ polygon (tL k h) := by push_cast; tI_mem

theorem tI_xge_mem : HalfPlane.xge (Placement.std.x k) ∈ tL k h := by simp [tL]
theorem tI_xle_mem : HalfPlane.xle (Placement.std.x (k + 3)) ∈ tL k h := by
  have e : Placement.std.x (k + 3) = (k : ℝ) + 3 := by rw [Placement.std_x]; push_cast; ring
  rw [e]; simp [tL]

/-- a horizontal spectator above the block -/
theorem tI_out_above {y : ℝ} (hy : h + 1 ≤ y) (x₀ x₁ : ℝ) : SegOut (tL k h) (x₀, y) (x₁, y) := by
  refine segOut_of_lt (HalfPlane.yle (h + 3 / 4)) (by simp [tL]) ?_ ?_ <;>
    simp only [HalfPlane.f_yle, HalfPlane.b_yle] <;> linarith

/-- a horizontal spectator below the block (the bottom of the trough) -/
theorem tI_out_below {y : ℝ} (hy : y ≤ h - 3) (x₀ x₁ : ℝ) : SegOut (tL k h) (x₀, y) (x₁, y) := by
  refine segOut_of_lt (HalfPlane.yge (h - 5 / 2)) (by simp [tL]) ?_ ?_ <;>
    simp only [HalfPlane.f_yge, HalfPlane.b_yge] <;> linarith

/-- the pushed-down spectator of the left cusp column -/
theorem tI_out_slantL {y : ℝ} (hy : y ≤ h - 1) : SegOut (tL k h) ((k : ℝ), y) (((k + 1 : ℕ) : ℝ), y - 2) := by
  refine segOut_of_lt (HalfPlane.above (h - 3 / 4 + 2 * k) (-2)) (by simp [tL]) ?_ ?_ <;>
    simp only [HalfPlane.f_above, HalfPlane.b_above] <;> push_cast <;> linarith

/-- the pulled-up spectator of the right cusp column -/
theorem tI_out_slantR {y : ℝ} (hy : y ≤ h - 1) : SegOut (tL k h) (((k + 2 : ℕ) : ℝ), y - 2) (((k + 3 : ℕ) : ℝ), y) := by
  refine segOut_of_lt (HalfPlane.above (h - 3 / 4 - 2 * ((k : ℝ) + 3)) 2) (by simp [tL]) ?_ ?_ <;>
    simp only [HalfPlane.f_above, HalfPlane.b_above] <;> push_cast <;> linarith

/-- the six inequalities of a point of the disc, unfolded -/
theorem tI_mem_bounds {x y : ℝ} (hmem : (x, y) ∈ polygon (tL k h)) :
    (k : ℝ) ≤ x ∧ x ≤ k + 3 ∧ h - 5 / 2 ≤ y ∧ y ≤ h + 3 / 4 ∧ h - 3 / 4 + 2 * k - 2 * x ≤ y ∧
      h - 3 / 4 - 2 * ((k : ℝ) + 3) + 2 * x ≤ y := by
  simp only [tL, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at hmem
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hmem
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem tL_isDisc : IsDisc (polygon (tL k h)) := by
  refine isDisc_polygon (tL k h) (a := k) (b := (k : ℝ) + 3) (c := h - 5 / 2) (d := h + 3 / 4) ?_
    ⟨((k : ℝ) + 3 / 2, h - 1 / 2), ?_⟩
  · intro q hq
    obtain ⟨h1, h2, h3, h4, -, -⟩ := tI_mem_bounds k h (x := q.1) (y := q.2) hq
    exact ⟨h1, h2, h3, h4⟩
  · simp only [tL, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
      HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
      HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end TIDisc

/-! #### E4. Segment pairs: no meeting, meeting only at the joint -/

section SegPairs

/-- two closed segments do not meet -/
def NoMeet (A B C D : Plane) : Prop :=
  ∀ τ τ' : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ τ' → τ' ≤ 1 → segPt A B τ ≠ segPt C D τ'

theorem NoMeet.symm {A B C D : Plane} (h : NoMeet A B C D) : NoMeet C D A B :=
  fun τ τ' h0 h1 h0' h1' he => h τ' τ h0' h1' h0 h1 he.symm

theorem NoMeet.revl {A B C D : Plane} (h : NoMeet A B C D) : NoMeet B A C D := by
  intro τ τ' h0 h1 h0' h1' he
  rw [← segPt_reverse] at he
  exact h (1 - τ) τ' (by linarith) (by linarith) h0' h1' he

theorem NoMeet.revr {A B C D : Plane} (h : NoMeet A B C D) : NoMeet A B D C := h.symm.revl.symm

/-- two consecutive segments `A → B → C` meet only at their common end `B` -/
def OnlyAtJoint (A B C : Plane) : Prop :=
  ∀ τ τ' : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ τ' → τ' ≤ 1 → segPt A B τ = segPt B C τ' → τ = 1 ∧ τ' = 0

theorem OnlyAtJoint.rev {A B C : Plane} (h : OnlyAtJoint A B C) : OnlyAtJoint C B A := by
  intro τ τ' h0 h1 h0' h1' he
  have e1 : segPt C B τ = segPt B C (1 - τ) := (segPt_reverse C B τ).symm
  have e2 : segPt B A τ' = segPt A B (1 - τ') := (segPt_reverse B A τ').symm
  rw [e1, e2] at he
  obtain ⟨f1, f2⟩ := h (1 - τ') (1 - τ) (by linarith) (by linarith) (by linarith) (by linarith) he.symm
  constructor <;> linarith

variable (pl : Placement) {W : Word} (hW : W.Closed) (mv : Slot W → Plane) (K : ℕ → Prop)

theorem meetSpec_of_noMeet {u v : Slot W} (h : NoMeet (mv u) (mv (next hW u)) (mv v) (mv (next hW v))) :
    MeetSpec pl hW mv K u v :=
  fun τ τ' h0 h1 h0' h1' he => absurd he (h τ τ' h0 h1 h0' h1')

/-- `v = next u` and the two pieces meet only at the shared vertex -/
theorem meetSpec_of_joint {u v : Slot W} (hv : v = next hW u) (h : OnlyAtJoint (mv u) (mv v) (mv (next hW v))) :
    MeetSpec pl hW mv K u v := by
  intro τ τ' h0 h1 h0' h1' he
  rw [← hv] at he
  obtain ⟨e1, e2⟩ := h τ τ' h0 h1 h0' h1' he
  exact Or.inr (Or.inl ⟨hv, e1, e2⟩)

/-- `u = next v` and the two pieces meet only at the shared vertex -/
theorem meetSpec_of_joint' {u v : Slot W} (hu : u = next hW v) (h : OnlyAtJoint (mv v) (mv u) (mv (next hW u))) :
    MeetSpec pl hW mv K u v :=
  (meetSpec_of_joint pl hW mv K hu h).symm

end SegPairs

/-! #### E5. The type-I curl, left variant: the moved diagram -/

/-- the moved positions of the ten curl vertices (top height `h`): the embedded shallow Z; the entry, its
neighbour, and the two exit vertices are unmoved -/
def mvv (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h)
  | 2 => (((k + 2 : ℕ) : ℝ), h + 5 / 8)
  | 3 => (((k + 2 : ℕ) : ℝ) + 1 / 2, h + 3 / 8)
  | 4 => (((k + 2 : ℕ) : ℝ), h + 1 / 8)
  | 5 => (((k + 1 : ℕ) : ℝ), h - 1 / 8)
  | 6 => ((k : ℝ) + 1 / 2, h - 3 / 8)
  | 7 => (((k + 1 : ℕ) : ℝ), h - 5 / 8)
  | 8 => (((k + 2 : ℕ) : ℝ), h)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the realization's positions of the ten curl vertices (top height `h = −(m−1)`) -/
def pvv (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h)
  | 2 => (((k + 2 : ℕ) : ℝ), h - 1)
  | 3 => (((k + 2 : ℕ) : ℝ) + 1 / 2, h - 3 / 2)
  | 4 => (((k + 2 : ℕ) : ℝ), h - 2)
  | 5 => (((k + 1 : ℕ) : ℝ), h - 2)
  | 6 => ((k : ℝ) + 1 / 2, h - 3 / 2)
  | 7 => (((k + 1 : ℕ) : ℝ), h - 1)
  | 8 => (((k + 2 : ℕ) : ℝ), h)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the six moved slots of the curl -/
def IsMovedT (k m : ℕ) (s : ℕ × ℕ) : Prop :=
  s = (k + 2, m) ∨ s = (k + 2, 0) ∨ s = (k + 2, m + 1) ∨ s = (k + 1, m + 1) ∨ s = (k, 0) ∨ s = (k + 1, m)

/-- the moved vertex function of the type-I curl -/
def mvT (W : Word) (k m : ℕ) (h : ℝ) (u : Slot W) : Plane :=
  if u.1 = (k + 2, m) then mvv k h 2
  else if u.1 = (k + 2, 0) then mvv k h 3
  else if u.1 = (k + 2, m + 1) then mvv k h 4
  else if u.1 = (k + 1, m + 1) then mvv k h 5
  else if u.1 = (k, 0) then mvv k h 6
  else if u.1 = (k + 1, m) then mvv k h 7
  else pt .std W u.1

section MvT

variable (W : Word) (k m : ℕ) (h : ℝ)

theorem mvT_of_not_moved {u : Slot W} (hu : ¬ IsMovedT k m u.1) : mvT W k m h u = pt .std W u.1 := by
  unfold IsMovedT at hu
  simp only [not_or] at hu
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
  simp [mvT, h1, h2, h3, h4, h5, h6]

theorem mvT_v2 {u : Slot W} (hu : u.1 = (k + 2, m)) : mvT W k m h u = mvv k h 2 := by simp [mvT, hu]
theorem mvT_v3 (hm : 1 ≤ m) {u : Slot W} (hu : u.1 = (k + 2, 0)) : mvT W k m h u = mvv k h 3 := by
  simp [mvT, hu, show (0 : ℕ) ≠ m by omega]
theorem mvT_v4 {u : Slot W} (hu : u.1 = (k + 2, m + 1)) : mvT W k m h u = mvv k h 4 := by
  simp [mvT, hu]
theorem mvT_v5 {u : Slot W} (hu : u.1 = (k + 1, m + 1)) : mvT W k m h u = mvv k h 5 := by
  simp [mvT, hu]
theorem mvT_v6 (hm : 1 ≤ m) {u : Slot W} (hu : u.1 = (k, 0)) : mvT W k m h u = mvv k h 6 := by
  simp [mvT, hu, show (0 : ℕ) ≠ m by omega]
theorem mvT_v7 {u : Slot W} (hu : u.1 = (k + 1, m)) : mvT W k m h u = mvv k h 7 := by
  simp [mvT, hu]

/-- the slots of the exterior are unmoved -/
theorem mvT_of_ext (hm : 1 ≤ m) {u : Slot W} (hu : ExtSl k (k + 3) u.1) : mvT W k m h u = pt .std W u.1 := by
  apply mvT_of_not_moved
  obtain ⟨j, p, hu'⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu'] at hu ⊢
  unfold ExtSl at hu
  unfold IsMovedT
  simp only [Prod.mk.injEq]
  split_ifs at hu with h0 <;> omega

theorem mvT_xcoord (hm : 1 ≤ m) (u : Slot W) : (mvT W k m h u).1 = (pt .std W u.1).1 := by
  by_cases hmv : IsMovedT k m u.1
  · unfold IsMovedT at hmv
    rcases hmv with e | e | e | e | e | e
    · rw [mvT_v2 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvT_v3 W k m h hm e, e, std_pt_cusp]; rfl
    · rw [mvT_v4 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvT_v5 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvT_v6 W k m h hm e, e, std_pt_cusp]; rfl
    · rw [mvT_v7 W k m h e, e, std_pt_cut _ (by omega)]; rfl
  · rw [mvT_of_not_moved W k m h hmv]

/-- a non-grid height on a half-integer vertical: no grid point -/
theorem NonGrid.ne_pt_half {y : ℝ} (hy : NonGrid y) (j : ℕ) (s : ℕ × ℕ) : ((j : ℝ) + 1 / 2, y) ≠ pt .std W s := by
  intro h
  by_cases hp : s.2 = 0
  · obtain ⟨a, b⟩ := s
    simp only at hp
    subst hp
    rw [std_pt_cusp] at h
    exact hy.2 _ (congrArg Prod.snd h)
  · obtain ⟨a, b⟩ := s
    rw [std_pt_cut _ hp] at h
    exact nat_ne_add_half a j (congrArg Prod.fst h).symm

/-- `h + o/8` with `h = −n + 1` (an integer) and `o` odd is a non-grid height -/
theorem nonGrid_eighth (n : ℕ) (o : ℤ) (ho : o % 2 = 1) : NonGrid (-(n : ℝ) + 1 + (o : ℝ) / 8) := by
  constructor
  · intro p hp
    have h8 : ((8 * (p : ℤ) - 8 * (n : ℤ) + 8 : ℤ) : ℝ) = ((-o : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective (α := ℝ) h8
    omega
  · intro q hq
    have h8 : ((8 * (q : ℤ) - 8 * (n : ℤ) + 12 : ℤ) : ℝ) = ((-o : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective (α := ℝ) h8
    omega

theorem mvT_injective (n : ℕ) (hm : 1 ≤ m) : Function.Injective (mvT W k m (-(n : ℝ) + 1)) := by
  have ng : ∀ i, 2 ≤ i → i ≤ 7 → ∀ s, mvv k (-(n : ℝ) + 1) i ≠ pt .std W s := by
    intro i hi1 hi2 s
    interval_cases i
    · have := nonGrid_eighth n 5 (by decide)
      have e : -(n : ℝ) + 1 + 5 / 8 = -(n : ℝ) + 1 + ((5 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ), -(n : ℝ) + 1 + 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth n 3 (by decide)
      have e : -(n : ℝ) + 1 + 3 / 8 = -(n : ℝ) + 1 + ((3 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ) + 1 / 2, -(n : ℝ) + 1 + 3 / 8) ≠ _
      rw [e]; exact this.ne_pt_half W (k + 2) s
    · have := nonGrid_eighth n 1 (by decide)
      have e : -(n : ℝ) + 1 + 1 / 8 = -(n : ℝ) + 1 + ((1 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ), -(n : ℝ) + 1 + 1 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth n (-1) (by decide)
      have e : -(n : ℝ) + 1 - 1 / 8 = -(n : ℝ) + 1 + ((-1 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 1 : ℕ) : ℝ), -(n : ℝ) + 1 - 1 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth n (-3) (by decide)
      have e : -(n : ℝ) + 1 - 3 / 8 = -(n : ℝ) + 1 + ((-3 : ℤ) : ℝ) / 8 := by push_cast; ring
      show ((k : ℝ) + 1 / 2, -(n : ℝ) + 1 - 3 / 8) ≠ _
      rw [e]; exact this.ne_pt_half W k s
    · have := nonGrid_eighth n (-5) (by decide)
      have e : -(n : ℝ) + 1 - 5 / 8 = -(n : ℝ) + 1 + ((-5 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 1 : ℕ) : ℝ), -(n : ℝ) + 1 - 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
  -- the moved values are pairwise distinct
  have hval : ∀ u : Slot W, IsMovedT k m u.1 → ∃ i, 2 ≤ i ∧ i ≤ 7 ∧ mvT W k m (-(n : ℝ) + 1) u = mvv k (-(n : ℝ) + 1) i ∧
      u.1 = tv k m i := by
    intro u hu
    unfold IsMovedT at hu
    rcases hu with e | e | e | e | e | e
    · exact ⟨2, by norm_num, by norm_num, mvT_v2 W k m _ e, e⟩
    · exact ⟨3, by norm_num, by norm_num, mvT_v3 W k m _ hm e, e⟩
    · exact ⟨4, by norm_num, by norm_num, mvT_v4 W k m _ e, e⟩
    · exact ⟨5, by norm_num, by norm_num, mvT_v5 W k m _ e, e⟩
    · exact ⟨6, by norm_num, by norm_num, mvT_v6 W k m _ hm e, e⟩
    · exact ⟨7, by norm_num, by norm_num, mvT_v7 W k m _ e, e⟩
  have hdist : ∀ i j, 2 ≤ i → i ≤ 7 → 2 ≤ j → j ≤ 7 → mvv k (-(n : ℝ) + 1) i = mvv k (-(n : ℝ) + 1) j → i = j := by
    intro i j hi1 hi2 hj1 hj2 he
    interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; have := congrArg Prod.snd he; simp only [mvv] at this; linarith)
  intro u v huv
  by_cases hu : IsMovedT k m u.1
  · obtain ⟨i, hi1, hi2, hui, hu'⟩ := hval u hu
    by_cases hv : IsMovedT k m v.1
    · obtain ⟨j, hj1, hj2, hvj, hv'⟩ := hval v hv
      have := hdist i j hi1 hi2 hj1 hj2 (hui.symm.trans (huv.trans hvj))
      subst this
      exact Subtype.ext (hu'.trans hv'.symm)
    · rw [hui, mvT_of_not_moved W k m _ hv] at huv
      exact absurd huv (ng i hi1 hi2 _)
  · by_cases hv : IsMovedT k m v.1
    · obtain ⟨j, hj1, hj2, hvj, -⟩ := hval v hv
      rw [hvj, mvT_of_not_moved W k m _ hu] at huv
      exact absurd huv.symm (ng j hj1 hj2 _)
    · rw [mvT_of_not_moved W k m _ hu, mvT_of_not_moved W k m _ hv] at huv
      exact pt_inj _ _ huv

end MvT

/-! #### E6. The vertex positions of the curl and their membership -/

section TIVertices

variable (k : ℕ) (h : ℝ)

theorem mvv_int : ∀ i, 1 ≤ i → i ≤ 8 → mvv k h i ∈ interior (polygon (tL k h)) := by
  intro i h1 h8
  interval_cases i
  · have := tI_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · exact tI_int_cut2 k h (5 / 8) (by norm_num) (by norm_num)
  · exact tI_int_cuspR k h (3 / 8) (by norm_num) (by norm_num)
  · exact tI_int_cut2 k h (1 / 8) (by norm_num) (by norm_num)
  · have := tI_int_cut1 k h (-(1 / 8)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cuspL k h (-(3 / 8)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut1 k h (-(5 / 8)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem pvv_int : ∀ i, 1 ≤ i → i ≤ 8 → pvv k h i ∈ interior (polygon (tL k h)) := by
  intro i h1 h8
  interval_cases i
  · have := tI_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tI_int_cut2 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cuspR k h (-(3 / 2)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut2 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut1 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cuspL k h (-(3 / 2)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut1 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem mvv_mem : ∀ i, i ≤ 9 → mvv k h i ∈ polygon (tL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · exact tI_mem_left k h
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · exact interior_subset (mvv_int k h i h0 (by omega))
  · have : i = 9 := by omega
    subst this
    exact tI_mem_right k h

theorem pvv_mem : ∀ i, i ≤ 9 → pvv k h i ∈ polygon (tL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · exact tI_mem_left k h
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · exact interior_subset (pvv_int k h i h0 (by omega))
  · have : i = 9 := by omega
    subst this
    exact tI_mem_right k h

/-- a piece with both ends in the polygon and one end in the open polygon is inside -/
theorem segIn_of_mem {L : List HalfPlane} {p₀ p₁ : Plane} (h0 : p₀ ∈ polygon L) (h1 : p₁ ∈ polygon L)
    (hint : p₀ ∈ interior (polygon L) ∨ p₁ ∈ interior (polygon L)) : SegIn L p₀ p₁ := by
  rcases hint with hi | hi
  · exact segIn_of_interior_left hi h1
  · exact segIn_of_interior_right h0 hi

/-! the geometric facts of the same-column pairs of the moved curl -/

macro "tI_pair" : tactic => `(tactic| (
  intro τ τ' h0 h1 h0' h1' he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [mvv, segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy))

theorem tI_NM05 : NoMeet (mvv k h 0) (mvv k h 1) (mvv k h 5) (mvv k h 6) := by tI_pair; linarith
theorem tI_NM06 : NoMeet (mvv k h 0) (mvv k h 1) (mvv k h 6) (mvv k h 7) := by tI_pair; linarith
theorem tI_NM14 : NoMeet (mvv k h 1) (mvv k h 2) (mvv k h 4) (mvv k h 5) := by tI_pair; linarith
theorem tI_NM17 : NoMeet (mvv k h 1) (mvv k h 2) (mvv k h 7) (mvv k h 8) := by tI_pair; linarith
theorem tI_NM47 : NoMeet (mvv k h 4) (mvv k h 5) (mvv k h 7) (mvv k h 8) := by tI_pair; linarith
theorem tI_NM28 : NoMeet (mvv k h 2) (mvv k h 3) (mvv k h 8) (mvv k h 9) := by tI_pair; linarith
theorem tI_NM38 : NoMeet (mvv k h 3) (mvv k h 4) (mvv k h 8) (mvv k h 9) := by tI_pair; linarith
theorem tI_OJ56 : OnlyAtJoint (mvv k h 5) (mvv k h 6) (mvv k h 7) := by
  tI_pair; constructor <;> linarith
theorem tI_OJ23 : OnlyAtJoint (mvv k h 2) (mvv k h 3) (mvv k h 4) := by
  tI_pair; constructor <;> linarith

/-- the out witnesses in the natural-number forms of the grid -/
theorem tI_out_slantL' {p : ℕ} (hp : -(p : ℝ) ≤ h - 1) :
    SegOut (tL k h) ((k : ℝ), -(p : ℝ)) (((k + 1 : ℕ) : ℝ), -((p + 2 : ℕ) : ℝ)) := by
  have := tI_out_slantL k h hp
  have e : -((p + 2 : ℕ) : ℝ) = -(p : ℝ) - 2 := by push_cast; ring
  rwa [e]

theorem tI_out_slantL'' {q : ℕ} (hq : 2 ≤ q) (hy : -((q - 2 : ℕ) : ℝ) ≤ h - 1) :
    SegOut (tL k h) (((k + 1 : ℕ) : ℝ), -(q : ℝ)) ((k : ℝ), -((q - 2 : ℕ) : ℝ)) := by
  have := (tI_out_slantL k h hy).symm
  have e : -((q - 2 : ℕ) : ℝ) - 2 = -(q : ℝ) := by rw [Nat.cast_sub hq]; push_cast; ring
  rwa [e] at this

theorem tI_out_slantR' {p : ℕ} (hp : 2 ≤ p) (hy : -((p - 2 : ℕ) : ℝ) ≤ h - 1) :
    SegOut (tL k h) (((k + 2 : ℕ) : ℝ), -(p : ℝ)) (((k + 3 : ℕ) : ℝ), -((p - 2 : ℕ) : ℝ)) := by
  have := tI_out_slantR k h hy
  have e : -((p - 2 : ℕ) : ℝ) - 2 = -(p : ℝ) := by rw [Nat.cast_sub hp]; push_cast; ring
  rwa [e] at this

theorem tI_out_slantR'' {q : ℕ} (hq : -(q : ℝ) ≤ h - 1) :
    SegOut (tL k h) (((k + 3 : ℕ) : ℝ), -(q : ℝ)) (((k + 2 : ℕ) : ℝ), -((q + 2 : ℕ) : ℝ)) := by
  have := (tI_out_slantR k h hq).symm
  have e : -((q + 2 : ℕ) : ℝ) = -(q : ℝ) - 2 := by push_cast; ring
  rwa [e]

end TIVertices

/-! #### E7. The type-I curl, left variant: the specification and the leaf case -/

section TypeILeftSpec

open U3

variable (X Y : Word) (m : ℕ) (d : Bool) (hm : 2 ≤ m) (hW : (X ++ [Letter.l m d, Letter.σ (m - 1), Letter.r m] ++ Y).Closed)

local notation "Vt" => X ++ [Letter.l m d, Letter.σ (m - 1), Letter.r m] ++ Y
local notation "Pt" => [Letter.l m d, Letter.σ (m - 1), Letter.r m]
local notation "hT" => (-(m : ℝ) + 1)

/-- the moved vertex function of the left type-I curl -/
def tlMv : Slot Vt → Plane := mvT Vt X.length m hT

theorem tlMv_apply (u : Slot Vt) : tlMv X Y m d u = mvT Vt X.length m hT u := rfl

include hm

theorem tl_hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]

/-- the vertices of `tv` in `tv`-injective form -/
theorem tv_inj : ∀ i j, i ≤ 9 → j ≤ 9 → tv X.length m i = tv X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tv, Prod.mk.injEq] at he; omega)

theorem tl_pt_tv : ∀ i, i ≤ 9 → pt .std Vt (tv X.length m i) = pvv X.length hT i := by
  have hm1 := tl_hm1 m hm
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tl_letters X Y m d
  intro i hi
  interval_cases i
  · show pt .std Vt (X.length, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvv]; rw [hm1]; ring)
  · show pt .std Vt (X.length + 1, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvv]; rw [hm1]; ring)
  · show pt .std Vt (X.length + 2, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvv]; ring)
  · show pt .std Vt (X.length + 2, 0) = _
    rw [std_pt_cusp, hℓ₂]; exact Prod.ext rfl (by simp only [pvv, idx]; ring)
  · show pt .std Vt (X.length + 2, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvv]; push_cast; ring)
  · show pt .std Vt (X.length + 1, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvv]; push_cast; ring)
  · show pt .std Vt (X.length, 0) = _
    rw [std_pt_cusp, hℓ₀]; exact Prod.ext rfl (by simp only [pvv, idx]; ring)
  · show pt .std Vt (X.length + 1, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvv]; ring)
  · show pt .std Vt (X.length + 2, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvv]; rw [hm1]; ring)
  · show pt .std Vt (X.length + 3, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvv]; rw [hm1]; ring)

theorem tl_mv_tv : ∀ i, i ≤ 9 → ∀ u : Slot Vt, u.1 = tv X.length m i → tlMv X Y m d u = mvv X.length hT i := by
  intro i hi u hu
  rw [tlMv_apply]
  have hnm : ∀ i, i = 0 ∨ i = 1 ∨ i = 8 ∨ i = 9 → ¬ IsMovedT X.length m (tv X.length m i) := by
    intro i hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp only [IsMovedT, tv, Prod.mk.injEq] <;> omega
  interval_cases i
  · rw [mvT_of_not_moved _ _ _ _ (hu ▸ hnm 0 (by simp)), hu, tl_pt_tv X Y m d hm 0 (by norm_num)]; rfl
  · rw [mvT_of_not_moved _ _ _ _ (hu ▸ hnm 1 (by simp)), hu, tl_pt_tv X Y m d hm 1 (by norm_num)]; rfl
  · exact mvT_v2 _ _ _ _ hu
  · exact mvT_v3 _ _ _ _ (by omega) hu
  · exact mvT_v4 _ _ _ _ hu
  · exact mvT_v5 _ _ _ _ hu
  · exact mvT_v6 _ _ _ _ (by omega) hu
  · exact mvT_v7 _ _ _ _ hu
  · rw [mvT_of_not_moved _ _ _ _ (hu ▸ hnm 8 (by simp)), hu, tl_pt_tv X Y m d hm 8 (by norm_num)]; rfl
  · rw [mvT_of_not_moved _ _ _ _ (hu ▸ hnm 9 (by simp)), hu, tl_pt_tv X Y m d hm 9 (by norm_num)]; rfl

include hW

theorem tl_mv_slot : ∀ j, j ≤ 9 → tlMv X Y m d ((tlChain X Y m d hm hW).slot hW j) =
    if d then mvv X.length hT j else mvv X.length hT (9 - j) := by
  intro j hj
  have hs := tl_slot_val X Y m d hm hW j hj
  cases d
  · simp only [tvd, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact tl_mv_tv X Y m false hm (9 - j) (by omega) _ hs
  · simp only [tvd, ↓reduceIte] at hs ⊢
    exact tl_mv_tv X Y m true hm j hj _ hs

theorem tl_pt_slot : ∀ j, j ≤ 9 → pt .std Vt ((tlChain X Y m d hm hW).slot hW j).1 =
    if d then pvv X.length hT j else pvv X.length hT (9 - j) := by
  intro j hj
  have hs := tl_slot_val X Y m d hm hW j hj
  cases d
  · simp only [tvd, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact tl_pt_tv X Y m false hm (9 - j) (by omega)
  · simp only [tvd, ↓reduceIte] at hs ⊢
    rw [hs]; exact tl_pt_tv X Y m true hm j hj

theorem tl_next_slot : ∀ j, j < 9 → next hW ((tlChain X Y m d hm hW).slot hW j) = (tlChain X Y m d hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

theorem tl_chain_in : ∀ j, j < 9 → PieceIn (tL X.length hT) hW (tlMv X Y m d) ((tlChain X Y m d hm hW).slot hW j) ∧
    PieceIn (tL X.length hT) hW (ptv .std) ((tlChain X Y m d hm hW).slot hW j) := by
  intro j hj
  have e := tl_next_slot X Y m d hm hW j hj
  constructor
  · show SegIn _ (tlMv X Y m d _) (tlMv X Y m d (next hW _))
    rw [e, tl_mv_slot X Y m d hm hW j (by omega), tl_mv_slot X Y m d hm hW (j + 1) (by omega)]
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (mvv_mem _ _ _ (by omega)) (mvv_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (mvv_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (mvv_int _ _ _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (mvv_mem _ _ _ (by omega)) (mvv_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (mvv_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (mvv_int _ _ _ (by omega) (by omega))
  · show SegIn _ (pt .std Vt _) (pt .std Vt (next hW _).1)
    rw [e, tl_pt_slot X Y m d hm hW j (by omega), tl_pt_slot X Y m d hm hW (j + 1) (by omega)]
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (pvv_mem _ _ _ (by omega)) (pvv_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pvv_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pvv_int _ _ _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (pvv_mem _ _ _ (by omega)) (pvv_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pvv_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pvv_int _ _ _ (by omega) (by omega))

theorem tl_vert : ∀ j, 0 < j → j < 9 → tlMv X Y m d ((tlChain X Y m d hm hW).slot hW j) ∈ interior (polygon (tL X.length hT)) ∧
    pt .std Vt ((tlChain X Y m d hm hW).slot hW j).1 ∈ interior (polygon (tL X.length hT)) := by
  intro j h0 hj
  rw [tl_mv_slot X Y m d hm hW j (by omega), tl_pt_slot X Y m d hm hW j (by omega)]
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨mvv_int _ _ _ (by omega) (by omega), pvv_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨mvv_int _ _ _ (by omega) (by omega), pvv_int _ _ _ (by omega) (by omega)⟩

omit hW in
theorem tl_moved : ∀ u : Slot Vt, tlMv X Y m d u = pt .std Vt u.1 ∨
    (tlMv X Y m d u ∈ interior (polygon (tL X.length hT)) ∧ pt .std Vt u.1 ∈ interior (polygon (tL X.length hT))) := by
  intro u
  by_cases hmv : IsMovedT X.length m u.1
  · right
    have : ∃ i, 2 ≤ i ∧ i ≤ 7 ∧ u.1 = tv X.length m i := by
      unfold IsMovedT at hmv
      rcases hmv with e | e | e | e | e | e
      · exact ⟨2, by norm_num, by norm_num, e⟩
      · exact ⟨3, by norm_num, by norm_num, e⟩
      · exact ⟨4, by norm_num, by norm_num, e⟩
      · exact ⟨5, by norm_num, by norm_num, e⟩
      · exact ⟨6, by norm_num, by norm_num, e⟩
      · exact ⟨7, by norm_num, by norm_num, e⟩
    obtain ⟨i, hi1, hi2, hu⟩ := this
    rw [tl_mv_tv X Y m d hm i (by omega) u hu, hu, tl_pt_tv X Y m d hm i (by omega)]
    exact ⟨mvv_int _ _ _ (by omega) (by omega), pvv_int _ _ _ (by omega) (by omega)⟩
  · left
    rw [tlMv_apply, mvT_of_not_moved _ _ _ _ hmv]

/-- the chain slot carrying the vertex `tv i` -/
theorem tl_chain_of (i : ℕ) (hi : i ≤ 9) {u : Slot Vt} (hu : u.1 = tv X.length m i)
    (hd : (d = true ∧ i < 9) ∨ (d = false ∧ 0 < i)) :
    ∃ j, j < 9 ∧ (tlChain X Y m d hm hW).slot hW j = u := by
  cases d
  · refine ⟨9 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · omega
    · rw [tl_slot_val X Y m false hm hW (9 - i) (by omega), hu]
      simp only [tvd, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [tl_slot_val X Y m true hm hW i hi, hu]
      simp only [tvd, ↓reduceIte]

omit hm in
/-- an unchanged spectator piece with an explicit outside witness -/
theorem tl_spec {u : Slot Vt} {j p j' p' : ℕ} (hu : u.1 = (j, p)) (hn : (next hW u).1 = (j', p'))
    (hp : p ≠ 0) (hp' : p' ≠ 0) (h1 : ¬ IsMovedT X.length m (j, p)) (h2 : ¬ IsMovedT X.length m (j', p'))
    (hout : SegOut (tL X.length hT) ((j : ℝ), -(p : ℝ)) ((j' : ℝ), -(p' : ℝ))) :
    Unch .std hW (tlMv X Y m d) u ∧ PieceOut (tL X.length hT) hW (ptv .std) u := by
  constructor
  · constructor
    · rw [tlMv_apply, mvT_of_not_moved _ _ _ _ (hu ▸ h1)]
    · rw [tlMv_apply, mvT_of_not_moved _ _ _ _ (hn ▸ h2)]
  · show SegOut _ (pt .std Vt u.1) (pt .std Vt (next hW u).1)
    rw [hu, hn, std_pt_cut _ hp, std_pt_cut _ hp']
    exact hout

omit hW in
theorem tl_hmv : ∀ v : Slot Vt, ExtSl X.length (X.length + 3) v.1 → tlMv X Y m d v = pt .std Vt v.1 :=
  fun v hv => by rw [tlMv_apply]; exact mvT_of_ext _ _ _ _ (by omega) hv

/-- THE CLASSIFICATION of the type-I curl. -/
theorem tl_rest : ∀ u : Slot Vt, (∃ j, j < 9 ∧ (tlChain X Y m d hm hW).slot hW j = u) ∨
    (Unch .std hW (tlMv X Y m d) u ∧ PieceOut (tL X.length hT) hW (ptv .std) u) := by
  intro u
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩ := tl_bits X Y m d hm hW
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tl_letters X Y m d
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  -- the numeric side conditions of the spectators
  have above : ∀ {q : ℕ}, q < m - 1 → hT + 1 ≤ -(q : ℝ) := fun {q} hq => by
    have : (q : ℝ) + 2 ≤ m := by exact_mod_cast (by omega : q + 2 ≤ m)
    linarith
  have below : ∀ {q : ℕ}, m + 2 ≤ q → -(q : ℝ) ≤ hT - 3 := fun {q} hq => by
    have : (m : ℝ) + 2 ≤ q := by exact_mod_cast hq
    linarith
  have slant : ∀ {q : ℕ}, m ≤ q → -(q : ℝ) ≤ hT - 1 := fun {q} hq => by
    have : (m : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have chain := tl_chain_of X Y m d hm hW
  by_cases hext : ExtCol X Pt (colOf u)
  · right
    have hext' := (tl_extCol X m d _).1 hext
    exact ⟨unch_of_extCol .std hW _ (tl_hmv X Y m d hm) hext',
      pieceOut_of_extCol _ .std hW _ (tI_xge_mem _ _) (tI_xle_mem _ _) (unch_pt _ _ _) hext'⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, tl_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl (chain 6 (by norm_num) hu (by cases d; exact Or.inr ⟨rfl, by norm_num⟩; exact Or.inl ⟨rfl, by norm_num⟩))
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₁] at this
      simp [isCrossing] at this
    · exact Or.inl (chain 3 (by norm_num) hu (by cases d; exact Or.inr ⟨rfl, by norm_num⟩; exact Or.inl ⟨rfl, by norm_num⟩))
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vt j p
  · rw [block_col_false hu hp hb, tl_extCol] at hext
    have : j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    rcases this with rfl | rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · rcases Nat.eq_or_lt_of_le (Nat.le_sub_one_of_lt hpm) with hpe | hpe
        · -- `(|X|+1, m−1)` leftward: the through-strand, `d = false`
          have hd : d = false := by rw [hpe, B1] at hb; exact hb
          exact Or.inl (chain 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · obtain ⟨h1, -⟩ := tl_T11 X Y m d hW hu hp hb hpm
          exact Or.inr (tl_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedT, Prod.mk.injEq]; omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
            (tI_out_above _ _ (above hpe) _ _))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- `(|X|+1, m)` leftward: the arm `tv 7`, `d = false`
          have hd : d = false := by rw [← hpe, B2] at hb; exact hb
          exact Or.inl (chain 7 (by norm_num) (by rw [hu, ← hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · have hpe' : p = m + 1 := by omega
          have hd : d = true := by rw [hpe', B3] at hb; simpa using hb
          exact Or.inl (chain 5 (by norm_num) (by rw [hu, hpe']; rfl) (Or.inl ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tl_T13 X Y m d hW hu hp hb hpm2
        exact Or.inr (tl_spec X Y m d hW hu h1 hp (by omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (tI_out_slantL'' _ _ (by omega) (slant (q := p - 2) (by omega))))
    · rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := tl_T15 X Y m d hW hu hp hb hpm
        exact Or.inr (tl_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedT, Prod.mk.injEq]; omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (tI_out_above _ _ (above hpm) _ _))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = false := by rw [hpe, B4] at hb; exact hb
          exact Or.inl (chain 8 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B5] at hb; exact hb
          exact Or.inl (chain 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · have hd : d = true := by rw [hpe, B6] at hb; simpa using hb
          exact Or.inl (chain 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tl_T18 X Y m d hm hW hu hp hb (by omega)
        exact Or.inr (tl_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedT, Prod.mk.injEq]; omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (tI_out_below _ _ (below hpm2) _ _))
    · rcases lt_or_ge p m with hpm | hpm
      · rcases Nat.eq_or_lt_of_le (Nat.le_sub_one_of_lt hpm) with hpe | hpe
        · have hd : d = false := by rw [hpe, B7] at hb; exact hb
          exact Or.inl (chain 9 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · obtain ⟨h1, -⟩ := tl_T19 X Y m d hW hu hp hb hpm
          exact Or.inr (tl_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedT, Prod.mk.injEq]; omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
            (tI_out_above _ _ (above hpe) _ _))
      · obtain ⟨h1, -⟩ := tl_T20 X Y m d hW hu hp hb hpm
        exact Or.inr (tl_spec X Y m d hW hu h1 hp (by omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (by simp only [IsMovedT, Prod.mk.injEq]; omega) (tI_out_slantR'' _ _ (slant hpm)))
  · rw [block_col_true hu hp hb, tl_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · rcases Nat.eq_or_lt_of_le (Nat.le_sub_one_of_lt hpm) with hpe | hpe
        · have hd : d = true := by rw [hpe, B0] at hb; exact hb
          exact Or.inl (chain 0 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · obtain ⟨h1, -⟩ := tl_T1 X Y m d hW hu hp hb hpm
          exact Or.inr (tl_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedT, Prod.mk.injEq]; omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
            (tI_out_above _ _ (above hpe) _ _))
      · obtain ⟨h1, -⟩ := tl_T2 X Y m d hW hu hp hb hpm
        exact Or.inr (tl_spec X Y m d hW hu h1 hp (by omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (by simp only [IsMovedT, Prod.mk.injEq]; omega) (tI_out_slantL' _ _ (slant hpm)))
    · rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := tl_T3 X Y m d hW hu hp hb hpm
        exact Or.inr (tl_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedT, Prod.mk.injEq]; omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (tI_out_above _ _ (above hpm) _ _))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = true := by rw [hpe, B1] at hb; exact hb
          exact Or.inl (chain 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · have hd : d = true := by rw [hpe, B2] at hb; exact hb
          exact Or.inl (chain 7 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B3] at hb; simpa using hb
          exact Or.inl (chain 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tl_T6 X Y m d hm hW hu hp hb (by omega)
        exact Or.inr (tl_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedT, Prod.mk.injEq]; omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (tI_out_below _ _ (below hpm2) _ _))
    · rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := tl_T7 X Y m d hW hu hp hb (by omega)
        exact Or.inr (tl_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedT, Prod.mk.injEq]; omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (tI_out_above _ _ (above hpm) _ _))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = true := by rw [hpe, B4] at hb; exact hb
          exact Or.inl (chain 8 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · have hd : d = true := by rw [hpe, B5] at hb; exact hb
          exact Or.inl (chain 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B6] at hb; simpa using hb
          exact Or.inl (chain 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tl_T9 X Y m d hW hu hp hb hpm2
        exact Or.inr (tl_spec X Y m d hW hu h1 hp (by omega) (by simp only [IsMovedT, Prod.mk.injEq]; omega)
          (by simp only [IsMovedT, Prod.mk.injEq]; omega) (tI_out_slantR' _ _ (by omega) (slant (q := p - 2) (by omega))))

theorem tl_slot_ne : ∀ j j', j ≤ 9 → j' ≤ 9 → j ≠ j' → (tlChain X Y m d hm hW).slot hW j ≠ (tlChain X Y m d hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [tl_slot_val X Y m d hm hW j hj, tl_slot_val X Y m d hm hW j' hj'] at h'
  cases d
  · simp only [tvd, Bool.false_eq_true, ↓reduceIte] at h'
    have := tv_inj X m hm (9 - j) (9 - j') (by omega) (by omega) h'
    omega
  · simp only [tvd, ↓reduceIte] at h'
    exact hne (tv_inj X m hm j j' hj hj' h')

theorem tl_prevOut : Unch .std hW (tlMv X Y m d) (prev hW (tlChain X Y m d hm hW).u₀) ∧
    PieceOut (tL X.length hT) hW (ptv .std) (prev hW (tlChain X Y m d hm hW).u₀) := by
  rcases tl_rest X Y m d hm hW (prev hW (tlChain X Y m d hm hW).u₀) with ⟨j, hj, hjs⟩ | h
  · exfalso
    have : (tlChain X Y m d hm hW).slot hW (j + 1) = (tlChain X Y m d hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact tl_slot_ne X Y m d hm hW (j + 1) 0 (by omega) (by omega) (by omega) this
  · exact h

theorem tl_stopOut : Unch .std hW (tlMv X Y m d) ((tlChain X Y m d hm hW).slot hW 9) ∧
    PieceOut (tL X.length hT) hW (ptv .std) ((tlChain X Y m d hm hW).slot hW 9) := by
  rcases tl_rest X Y m d hm hW ((tlChain X Y m d hm hW).slot hW 9) with ⟨j, hj, hjs⟩ | h
  · exact absurd hjs (tl_slot_ne X Y m d hm hW j 9 (by omega) (by omega) (by omega))
  · exact h

omit hW in
/-- a grid point of the disc is a curl vertex -/
theorem tl_vertex_of_mem {u : Slot Vt} (hmem : pt .std Vt u.1 ∈ polygon (tL X.length hT)) :
    ∃ i, i ≤ 9 ∧ u.1 = tv X.length m i := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tl_letters X Y m d
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu] at hmem
  by_cases hp : p = 0
  · subst hp
    rw [std_pt_cusp] at hmem
    obtain ⟨b1, b2, -, -, -, -⟩ := tI_mem_bounds X.length hT hmem
    have e1 : 2 * X.length ≤ 2 * j + 1 := by exact_mod_cast (by linarith : (2 * X.length : ℝ) ≤ 2 * j + 1)
    have e2 : 2 * j + 1 ≤ 2 * X.length + 6 := by exact_mod_cast (by linarith : (2 * j + 1 : ℝ) ≤ 2 * X.length + 6)
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact ⟨6, by norm_num, hu⟩
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₁] at this
      simp [isCrossing] at this
    · exact ⟨3, by norm_num, hu⟩
  · rw [std_pt_cut _ hp] at hmem
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tI_mem_bounds X.length hT hmem
    have e1 : X.length ≤ j := by exact_mod_cast b1
    have e2 : j ≤ X.length + 3 := by exact_mod_cast (by linarith : (j : ℝ) ≤ X.length + 3)
    have e3 : 2 * p ≤ 2 * m + 3 := by exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 2 * m + 3)
    have e4 : 4 * m ≤ 4 * p + 7 := by exact_mod_cast (by linarith : (4 * m : ℝ) ≤ 4 * p + 7)
    have e5 : 4 * p + 1 + 8 * X.length ≤ 4 * m + 8 * j := by
      exact_mod_cast (by linarith : (4 * p + 1 + 8 * X.length : ℝ) ≤ 4 * m + 8 * j)
    have e6 : 4 * p + 8 * j + 1 ≤ 4 * m + 8 * X.length + 24 := by
      exact_mod_cast (by linarith : (4 * p + 8 * j + 1 : ℝ) ≤ 4 * m + 8 * X.length + 24)
    have hj : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    have hpp : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · have : p = m - 1 := by omega
      exact ⟨0, by norm_num, by rw [hu, this]; rfl⟩
    · rcases hpp with rfl | rfl | rfl
      · exact ⟨1, by norm_num, hu⟩
      · exact ⟨7, by norm_num, hu⟩
      · exact ⟨5, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact ⟨8, by norm_num, hu⟩
      · exact ⟨2, by norm_num, hu⟩
      · exact ⟨4, by norm_num, hu⟩
    · have : p = m - 1 := by omega
      exact ⟨9, by norm_num, by rw [hu, this]; rfl⟩

theorem tl_touch : ∀ u : Slot Vt, PieceOut (tL X.length hT) hW (ptv .std) u → pt .std Vt u.1 ∈ polygon (tL X.length hT) →
    u = (tlChain X Y m d hm hW).slot hW 9 := by
  intro u hout hmem
  obtain ⟨i, hi, hu⟩ := tl_vertex_of_mem X Y m d hm hmem
  have hchain : ∀ j', j' < 9 → u ≠ (tlChain X Y m d hm hW).slot hW j' := by
    intro j' hj' he
    rw [he] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (tl_chain_in X Y m d hm hW j' hj').2
  have hs := tl_slot_val X Y m d hm hW
  cases d
  · -- `u = slot (9 − i)`
    have hu' : u = (tlChain X Y m false hm hW).slot hW (9 - i) := by
      apply Subtype.ext
      rw [hs (9 - i) (by omega), hu]
      simp only [tvd, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · exact hu'
    · exact absurd hu' (hchain (9 - i) (by omega))
  · have hu' : u = (tlChain X Y m true hm hW).slot hW i := by
      apply Subtype.ext
      rw [hs i hi, hu]
      simp only [tvd, ↓reduceIte]
    rcases Nat.lt_or_ge i 9 with h9 | h9
    · exact absurd hu' (hchain i h9)
    · have : i = 9 := by omega
      subst this
      exact hu'

theorem tl_exits : ∀ u : Slot Vt, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch .std hW (tlMv X Y m d) v ∧
    PieceOut (tL X.length hT) hW (ptv .std) v := by
  intro u
  obtain ⟨v, hsc, hcol⟩ := tl_exits_core X Y m d hm hW u
  exact ⟨v, hsc, unch_of_extCol .std hW _ (tl_hmv X Y m d hm) hcol,
    pieceOut_of_extCol _ .std hW _ (tI_xge_mem _ _) (tI_xle_mem _ _) (unch_pt _ _ _) hcol⟩

omit hW hm in
/-- the only crossing letter of the block is the `σ_{m−1}` of column `|X|+1` -/
theorem tl_σcol {k' m' : ℕ} (hℓ : letterAt Vt k' = .σ m') (hext : ¬ ExtCol X Pt k') :
    k' = X.length + 1 ∧ m - 1 = m' := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tl_letters X Y m d
  rw [tl_extCol] at hext
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀] at hℓ; cases hℓ
  · rw [hℓ₁] at hℓ; exact ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [hℓ₂] at hℓ; cases hℓ

omit hW hm in
theorem tl_kink : ∃ (k₀ m₀ : ℕ) (_hk₀ : k₀ < (Vt).length) (_hℓ₀ : letterAt Vt k₀ = .σ m₀), ¬ ExtCol X Pt k₀ ∧
    ∀ (k m : ℕ) (_hk : k < (Vt).length) (_hℓ : letterAt Vt k = .σ m), ¬ ExtCol X Pt k → k = k₀ :=
  ⟨X.length + 1, m - 1, by rw [tl_length]; omega, (tl_letters X Y m d).2.1, by rw [tl_extCol]; omega,
    fun k m' _ hℓ hext => (tl_σcol X Y m d hℓ hext).1⟩

/-- the over strand of the block crossing, as a chain piece -/
theorem tl_σA_chain (hk : X.length + 1 < (Vt).length) (hℓ : letterAt Vt (X.length + 1) = .σ (m - 1)) :
    ∃ j, j < 9 ∧ (tlChain X Y m d hm hW).slot hW j = σSlotA hW hk hℓ := by
  obtain ⟨-, B1, -, -, -, -, -, -⟩ := tl_bits X Y m d hm hW
  have hv := σSlotA_val hW hk hℓ
  rw [B1, show m - 1 + 1 = m by omega] at hv
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte] at hv
    exact tl_chain_of X Y m false hm hW 2 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
  · simp only [↓reduceIte] at hv
    exact tl_chain_of X Y m true hm hW 1 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

theorem tl_hK : ∀ (k' m' : ℕ) (hk : k' < (Vt).length) (hℓ : letterAt Vt k' = .σ m'),
    ExtCol X Pt k' ↔ Unch .std hW (tlMv X Y m d) (σSlotA hW hk hℓ) ∧ Unch .std hW (tlMv X Y m d) (σSlotB hW hk hℓ) := by
  intro k' m' hk hℓ
  constructor
  · intro hext
    have hext' := (tl_extCol X m d k').1 hext
    exact ⟨unch_of_extCol .std hW _ (tl_hmv X Y m d hm) (by rw [(σSlotA_spec hW hk hℓ).1]; exact hext'),
      unch_of_extCol .std hW _ (tl_hmv X Y m d hm) (by rw [(σSlotB_spec hW hk hℓ).1]; exact hext')⟩
  · rintro ⟨hA, -⟩
    by_contra hext
    obtain ⟨rfl, rfl⟩ := tl_σcol X Y m d hℓ hext
    obtain ⟨-, B1, -, -, -, -, -, -⟩ := tl_bits X Y m d hm hW
    have hv := σSlotA_val hW hk hℓ
    rw [B1, show m - 1 + 1 = m by omega] at hv
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      have hv' : (σSlotA hW hk hℓ).1 = tv X.length m 2 := hv
      have h1 := hA.1
      rw [tl_mv_tv X Y m false hm 2 (by norm_num) _ hv', hv', tl_pt_tv X Y m false hm 2 (by norm_num)] at h1
      have := congrArg Prod.snd h1
      simp only [mvv, pvv] at this
      linarith
    · simp only [↓reduceIte] at hv
      have h2 := hA.2
      have hn : (next hW (σSlotA hW hk hℓ)).1 = tv X.length m 2 := tl_T4 X Y m true hm hW hv B1
      rw [tl_mv_tv X Y m true hm 2 (by norm_num) _ hn, hn, tl_pt_tv X Y m true hm 2 (by norm_num)] at h2
      have := congrArg Prod.snd h2
      simp only [mvv, pvv] at this
      linarith

theorem tl_hKout : ∀ (k' m' : ℕ) (hk : k' < (Vt).length) (hℓ : letterAt Vt k' = .σ m'),
    ExtCol X Pt k' ↔ PieceOut (tL X.length hT) hW (ptv .std) (σSlotA hW hk hℓ) := by
  intro k' m' hk hℓ
  constructor
  · intro hext
    exact pieceOut_of_extCol _ .std hW _ (tI_xge_mem _ _) (tI_xle_mem _ _) (unch_pt _ _ _)
      (by rw [(σSlotA_spec hW hk hℓ).1]; exact (tl_extCol X m d k').1 hext)
  · intro hout
    by_contra hext
    obtain ⟨rfl, rfl⟩ := tl_σcol X Y m d hℓ hext
    obtain ⟨j, hj, hjs⟩ := tl_σA_chain X Y m d hm hW hk hℓ
    rw [← hjs] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (tl_chain_in X Y m d hm hW j hj).2

/-- the same-column chain pairs: the 18 ordered pairs of pieces sharing a column, both directions -/
theorem tl_pairs : ∀ j j', j < 9 → j' < 9 → (tlChain X Y m d hm hW).slot hW j ≠ (tlChain X Y m d hm hW).slot hW j' →
    colOf ((tlChain X Y m d hm hW).slot hW j) = colOf ((tlChain X Y m d hm hW).slot hW j') →
    MeetSpec .std hW (tlMv X Y m d) (ExtCol X Pt) ((tlChain X Y m d hm hW).slot hW j) ((tlChain X Y m d hm hW).slot hW j') := by
  intro j j' hj hj' hne hc
  have hjj : j ≠ j' := fun h => hne (by rw [h])
  clear hne
  rw [tl_col X Y m d hm hW j hj, tl_col X Y m d hm hW j' hj'] at hc
  have hn := tl_next_slot X Y m d hm hW
  have hmv := tl_mv_slot X Y m d hm hW
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [tcol] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact (tI_NM38 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 6 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 6 (by norm_num), hmv (6 + 1) (by norm_num)]
      exact (tI_NM28 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (tI_NM47 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 7 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 7 (by norm_num), hmv (7 + 1) (by norm_num)]
      exact (tI_NM17 _ _).symm.revl.revr
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (tI_OJ56 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 2 (by norm_num), hn 8 (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num),
        hmv 8 (by norm_num), hmv (8 + 1) (by norm_num)]
      exact (tI_NM06 _ _).symm.revl.revr
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (tI_OJ56 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 3 (by norm_num), hn 8 (by norm_num), hmv 3 (by norm_num), hmv (3 + 1) (by norm_num),
        hmv 8 (by norm_num), hmv (8 + 1) (by norm_num)]
      exact (tI_NM05 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (tI_NM47 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 7 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 7 (by norm_num), hmv (7 + 1) (by norm_num)]
      exact (tI_NM14 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (tI_NM38 _ _).revl.revr
    · apply meetSpec_of_joint .std hW _ _ ((hn 5 (by norm_num)).symm)
      rw [hn (5 + 1) (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num), hmv (5 + 1 + 1) (by norm_num)]
      exact (tI_OJ23 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 6 (by norm_num), hn 0 (by norm_num), hmv 6 (by norm_num), hmv (6 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (tI_NM28 _ _).revl.revr
    · apply meetSpec_of_joint' .std hW _ _ ((hn 5 (by norm_num)).symm)
      rw [hn (5 + 1) (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num), hmv (5 + 1 + 1) (by norm_num)]
      exact (tI_OJ23 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 7 (by norm_num), hn 1 (by norm_num), hmv 7 (by norm_num), hmv (7 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (tI_NM17 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 7 (by norm_num), hn 4 (by norm_num), hmv 7 (by norm_num), hmv (7 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (tI_NM14 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 8 (by norm_num), hn 2 (by norm_num), hmv 8 (by norm_num), hmv (8 + 1) (by norm_num),
        hmv 2 (by norm_num), hmv (2 + 1) (by norm_num)]
      exact (tI_NM06 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 8 (by norm_num), hn 3 (by norm_num), hmv 8 (by norm_num), hmv (8 + 1) (by norm_num),
        hmv 3 (by norm_num), hmv (3 + 1) (by norm_num)]
      exact (tI_NM05 _ _).revl.revr
  · simp only [↓reduceIte] at hc hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [tcol] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact tI_NM05 _ _
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 6 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 6 (by norm_num), hmv (6 + 1) (by norm_num)]
      exact tI_NM06 _ _
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact tI_NM14 _ _
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 7 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 7 (by norm_num), hmv (7 + 1) (by norm_num)]
      exact tI_NM17 _ _
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact tI_OJ23 _ _
    · apply meetSpec_of_noMeet
      rw [hn 2 (by norm_num), hn 8 (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num),
        hmv 8 (by norm_num), hmv (8 + 1) (by norm_num)]
      exact tI_NM28 _ _
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact tI_OJ23 _ _
    · apply meetSpec_of_noMeet
      rw [hn 3 (by norm_num), hn 8 (by norm_num), hmv 3 (by norm_num), hmv (3 + 1) (by norm_num),
        hmv 8 (by norm_num), hmv (8 + 1) (by norm_num)]
      exact tI_NM38 _ _
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (tI_NM14 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 7 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 7 (by norm_num), hmv (7 + 1) (by norm_num)]
      exact tI_NM47 _ _
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (tI_NM05 _ _).symm
    · apply meetSpec_of_joint .std hW _ _ ((hn 5 (by norm_num)).symm)
      rw [hn (5 + 1) (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num), hmv (5 + 1 + 1) (by norm_num)]
      exact tI_OJ56 _ _
    · apply meetSpec_of_noMeet
      rw [hn 6 (by norm_num), hn 0 (by norm_num), hmv 6 (by norm_num), hmv (6 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (tI_NM06 _ _).symm
    · apply meetSpec_of_joint' .std hW _ _ ((hn 5 (by norm_num)).symm)
      rw [hn (5 + 1) (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num), hmv (5 + 1 + 1) (by norm_num)]
      exact tI_OJ56 _ _
    · apply meetSpec_of_noMeet
      rw [hn 7 (by norm_num), hn 1 (by norm_num), hmv 7 (by norm_num), hmv (7 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (tI_NM17 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 7 (by norm_num), hn 4 (by norm_num), hmv 7 (by norm_num), hmv (7 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (tI_NM47 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 8 (by norm_num), hn 2 (by norm_num), hmv 8 (by norm_num), hmv (8 + 1) (by norm_num),
        hmv 2 (by norm_num), hmv (2 + 1) (by norm_num)]
      exact (tI_NM28 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 8 (by norm_num), hn 3 (by norm_num), hmv 8 (by norm_num), hmv (8 + 1) (by norm_num),
        hmv 3 (by norm_num), hmv (3 + 1) (by norm_num)]
      exact (tI_NM38 _ _).symm

theorem tl_genericData : GenericData .std hW (tlMv X Y m d) (ExtCol X Pt) :=
  genericData_of (tL X.length hT) .std hW (tlMv X Y m d) (ExtCol X Pt) (tlChain X Y m d hm hW)
    (mvT_injective _ _ _ m (by omega)) (mvT_xcoord _ _ _ _ (by omega)) (tl_rest X Y m d hm hW)
    (fun j hj => (tl_chain_in X Y m d hm hW j hj).1) (tl_pairs X Y m d hm hW)
    (fun k m' hk hℓ hA hB => (tl_hK X Y m d hm hW k m' hk hℓ).2 ⟨hA, hB⟩)

theorem tl_riSpec : RISpec (tL X.length hT) .std hW (tlMv X Y m d) (ExtCol X Pt) (tlChain X Y m d hm hW) where
  disc := tL_isDisc _ _
  hK := tl_hK X Y m d hm hW
  hKout := tl_hKout X Y m d hm hW
  moved := tl_moved X Y m d hm
  chain := tl_chain_in X Y m d hm hW
  vert := tl_vert X Y m d hm hW
  rest := tl_rest X Y m d hm hW
  prevOut := tl_prevOut X Y m d hm hW
  stopOut := tl_stopOut X Y m d hm hW
  touch := tl_touch X Y m d hm hW
  exits := tl_exits X Y m d hm hW
  kink := tl_kink X Y m d

theorem tl_riData (hne : Vt ≠ []) :
    Nonempty (RIData (polygon (tL X.length hT))
      (mvDiagram .std hW hne (tlMv X Y m d) (ExtCol X Pt) (tl_genericData X Y m d hm hW)) (rlDiagram .std hW hne)) :=
  riData_of hne (tl_genericData X Y m d hm hW) (tl_riSpec X Y m d hm hW)

theorem tl_recordIso (hne : Vt ≠ []) (W' : OWord) (hW'eq : W'.letters = X ++ Y) :
    Nonempty (RecordIso (mvDiagram .std hW hne (tlMv X Y m d) (ExtCol X Pt) (tl_genericData X Y m d hm hW)).record
      (realize W').diagram.record) := by
  have hW' : (X ++ [] ++ Y).Closed := by have := W'.closed; rw [hW'eq] at this; simpa using this
  have hne' : X ++ Y ≠ [] := u1_typeI_target_ne_nil (W := Vt) (Or.inl ⟨hm, rfl⟩) hW
  refine ⟨vertexMovedRecordIso' X Pt Y [] (by simp) (tl_sameEffect X Y m d hm hW) hW hW' .std hne _ _ _ _
    (slotDiagramData_of .std hW hne (tlMv X Y m d) (ExtCol X Pt) (tl_genericData X Y m d hm hW) (tl_hK X Y m d hm hW))
    (tl_passage X Y m d hm hW hW') (tl_hexit X Y m d hm hW) ?_ ?_ W' (by simpa using hW'eq) (by simpa using hne')⟩
  · intro u; exact ⟨0, by show ExtCol X [] (colOf u); unfold ExtCol; simp; omega⟩
  · intro k hk1 hk2; simp at hk2; omega

omit hW in
/-- LEAF CASE (type I, left variant `l_m d σ_{m−1} r_m ↦ (nothing)`). -/
theorem typeI_left {W W' : OWord} (hWeq : W.letters = Vt) (hW'eq : W'.letters = X ++ Y) :
    ∃ D : Diagram, RI D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨Wl, hWl⟩ := W
  simp only at hWeq
  subst hWeq
  have hne : Vt ≠ [] := by simp
  rw [realize_eq_realizeAt ⟨_, hWl⟩ hne]
  exact ⟨mvDiagram .std hWl hne (tlMv X Y m d) (ExtCol X Pt) (tl_genericData X Y m d hm hWl),
    ⟨polygon (tL X.length hT), Or.inl (tl_riData X Y m d hm hWl hne)⟩, tl_recordIso X Y m d hm hWl hne W' hW'eq⟩

end TypeILeftSpec

/-! #### F. The front type-I move, right variant `l_m d σ_{m+1} r_m ↦ (nothing)` (ng:front-I, sm-3:1955-1963) -/

/-- the ten vertices of the type-I curl `l_m σ_{m+1} r_m`, in the traversal order of a rightward through-strand
(`d = false`) -/
def tw (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k, m)
  | 1 => (k + 1, m + 2)
  | 2 => (k + 2, m + 1)
  | 3 => (k + 2, 0)
  | 4 => (k + 2, m)
  | 5 => (k + 1, m)
  | 6 => (k, 0)
  | 7 => (k + 1, m + 1)
  | 8 => (k + 2, m + 2)
  | _ => (k + 3, m)

/-- the chain vertex `j`: `tw j` for a rightward through-strand (`d = false`), `tw (9 − j)` for a leftward one -/
def twd (k m : ℕ) (d : Bool) (j : ℕ) : ℕ × ℕ := if d then tw k m (9 - j) else tw k m j

section TypeIRightWord

open U3

variable (X Y : Word) (m : ℕ) (d : Bool) (hm : 1 ≤ m) (hW : (X ++ [Letter.l m d, Letter.σ (m + 1), Letter.r m] ++ Y).Closed)

local notation "Vu" => X ++ [Letter.l m d, Letter.σ (m + 1), Letter.r m] ++ Y
local notation "Pu" => [Letter.l m d, Letter.σ (m + 1), Letter.r m]

theorem tu_letters : letterAt Vu X.length = .l m d ∧ letterAt Vu (X.length + 1) = .σ (m + 1) ∧
    letterAt Vu (X.length + 2) = .r m := by
  refine ⟨?_, ?_, ?_⟩
  · have := letterAt_block X Pu Y (i := 0) (by simp); simpa using this
  · have := letterAt_block X Pu Y (i := 1) (by simp); simpa using this
  · have := letterAt_block X Pu Y (i := 2) (by simp); simpa using this

theorem tu_length : (Vu).length = X.length + 3 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem tu_extCol (k : ℕ) : ExtCol X Pu k ↔ k + 1 ≤ X.length ∨ X.length + 3 ≤ k := by
  unfold ExtCol; simp

theorem tu_shift : shiftIdx X Pu [] (X.length + 3) = X.length := by
  unfold shiftIdx; simp

include hW

include hm in
theorem tu_sameEffect : SameEffect X Pu [] :=
  sameEffect_of_replace X Pu Y [] hW (fun c c' h => by obtain rfl := run_typeI_right hm h; rfl)

include hm in
theorem tu_cut_end : cut Vu (X.length + 3) = cut Vu X.length := by
  have hE := tu_sameEffect X Y m d hm hW
  unfold SameEffect at hE
  unfold cut
  rw [List.take_left' (by simp), List.append_assoc, List.take_left' rfl, hE, List.append_nil]

theorem tu_cutlen : m ≤ (cut Vu X.length).length := by
  have hk : X.length < (Vu).length := by rw [tu_length]; omega
  have hk₁ : X.length + 1 < (Vu).length := by rw [tu_length]; omega
  obtain ⟨-, h2, -, -, -⟩ := σ_facts hW hk₁ (tu_letters X Y m d).2.1
  obtain ⟨D⟩ := decomp hW X.length hk
  have h1 := D.length_add
  have har : (letterAt Vu X.length).arity = 0 := by rw [(tu_letters X Y m d).1]; rfl
  have hco : (letterAt Vu X.length).coarity = 2 := by rw [(tu_letters X Y m d).1]; rfl
  omega

include hm in
/-- the bits of the curl: the through-strand travels with the bit `!d` everywhere -/
theorem tu_bits :
    bit Vu X.length m = !d ∧ bit Vu (X.length + 1) m = d ∧ bit Vu (X.length + 1) (m + 1) = !d ∧
    bit Vu (X.length + 1) (m + 2) = !d ∧ bit Vu (X.length + 2) m = d ∧ bit Vu (X.length + 2) (m + 1) = !d ∧
    bit Vu (X.length + 2) (m + 2) = !d ∧ bit Vu (X.length + 3) m = !d := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tu_letters X Y m d
  have hk₀ : X.length < (Vu).length := by rw [tu_length]; omega
  have hk₁ : X.length + 1 < (Vu).length := by rw [tu_length]; omega
  have hk₂ : X.length + 2 < (Vu).length := by rw [tu_length]; omega
  obtain ⟨-, B1, B2⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, -, -, h4, h5⟩ := σ_facts hW hk₁ hℓ₁
  obtain ⟨-, h6⟩ := r_bits hW hk₂ hℓ₂
  have B4 : bit Vu (X.length + 2) m = d := by
    rw [bit_succ_of_lt hW hk₁ (by omega) (by rw [hℓ₁]; simp only [idx]; omega), B1]
  have B5 : bit Vu (X.length + 2) (m + 1) = !d := by
    rw [B4] at h6
    exact bool_eq_not_of_ne h6.symm
  have B6 : bit Vu (X.length + 2) (m + 2) = !d := by rw [h4, B2]
  have B3 : bit Vu (X.length + 1) (m + 2) = !d := by rw [← h5, B5]
  have B0 : bit Vu X.length m = !d := by
    have := bit_succ_of_ge hW hk₀ (p := m) (by rw [hℓ₀]; simp only [idx, arity]; omega)
    rw [hℓ₀] at this
    simp only [coarity, arity] at this
    rw [show m + 2 - 0 = m + 2 by omega] at this
    rw [← this, B3]
  have B7 : bit Vu (X.length + 3) m = !d := by
    have := bit_succ_of_ge hW hk₂ (p := m + 2) (by rw [hℓ₂]; simp only [idx, arity]; omega)
    rw [hℓ₂] at this
    simp only [coarity, arity] at this
    rw [show m + 2 + 0 - 2 = m by omega] at this
    rw [this, B6]
  exact ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩

/-! the successor table of the block `l_m σ_{m+1} r_m` -/

theorem tu_T1 {s : Slot Vu} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vu X.length p = true)
    (hpm : p < m) : (next hW s).1 = (X.length + 1, p) ∧ bit Vu (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(tu_letters X Y m d).1]; exact hpm)

theorem tu_T2 {s : Slot Vu} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vu X.length p = true)
    (hpm : m ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Vu (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(tu_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(tu_letters X Y m d).1] at this

theorem tu_T3 {s : Slot Vu} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vu (X.length + 1) p = true) (hpm : p < m + 1) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vu (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(tu_letters X Y m d).2.1]; exact hpm)

theorem tu_T4 {s : Slot Vu} (hs : s.1 = (X.length + 1, m + 1)) (hb : bit Vu (X.length + 1) (m + 1) = true) :
    (next hW s).1 = (X.length + 2, m + 2) :=
  next_σ_right_idx hW (tu_letters X Y m d).2.1 hs hb

theorem tu_T5 {s : Slot Vu} (hs : s.1 = (X.length + 1, m + 2)) (hb : bit Vu (X.length + 1) (m + 2) = true) :
    (next hW s).1 = (X.length + 2, m + 1) :=
  next_σ_right_succ hW (tu_letters X Y m d).2.1 hs hb

theorem tu_T6 {s : Slot Vu} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vu (X.length + 1) p = true) (hpm : m + 3 ≤ p) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vu (X.length + 2) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(tu_letters X Y m d).2.1]; simp only [idx, arity]; omega)
  rw [(tu_letters X Y m d).2.1] at this
  simpa [coarity, arity] using this

theorem tu_T7 {s : Slot Vu} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vu (X.length + 2) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 3, p) ∧ bit Vu (X.length + 3) p = true :=
  next_right_lt hW hs hp hb (by rw [(tu_letters X Y m d).2.2]; exact hpm)

theorem tu_T8 {s : Slot Vu} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p = m ∨ p = m + 1)
    (hb : bit Vu (X.length + 2) p = true) : (next hW s).1 = (X.length + 2, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (tu_letters X Y m d).2.2 hs hp hb

theorem tu_T9 {s : Slot Vu} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vu (X.length + 2) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 3, p - 2) ∧ bit Vu (X.length + 3) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(tu_letters X Y m d).2.2]; simpa [idx, arity] using hpm)
  rw [(tu_letters X Y m d).2.2] at this
  simpa [coarity, arity] using this

theorem tu_T10 {s : Slot Vu} (hs : s.1 = (X.length + 2, 0)) :
    (next hW s).1 = (X.length + 2, if bit Vu (X.length + 2) m then m + 1 else m) :=
  next_cusp_r hW (tu_letters X Y m d).2.2 hs

theorem tu_T11 {s : Slot Vu} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vu (X.length + 1) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length, q) ∧ bit Vu X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (tu_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem tu_T12 {s : Slot Vu} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m ∨ q = m + 1)
    (hb : bit Vu (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (tu_letters X Y m d).1 hs hq hb

theorem tu_T13 {s : Slot Vu} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vu (X.length + 1) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Vu X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (tu_letters X Y m d).1]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, (tu_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem tu_T14 {s : Slot Vu} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m else m + 1) :=
  next_cusp_l hW (tu_letters X Y m d).1 hs

theorem tu_T15 {s : Slot Vu} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vu (X.length + 2) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vu (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e2, (tu_letters X Y m d).2.1]; exact hqm)
  rwa [e2] at this

theorem tu_T16 {s : Slot Vu} (hs : s.1 = (X.length + 2, m + 1)) (hb : bit Vu (X.length + 2) (m + 1) = false) :
    (next hW s).1 = (X.length + 1, m + 2) :=
  next_σ_left_idx hW (tu_letters X Y m d).2.1 hs hb

theorem tu_T17 {s : Slot Vu} (hs : s.1 = (X.length + 2, m + 2)) (hb : bit Vu (X.length + 2) (m + 2) = false) :
    (next hW s).1 = (X.length + 1, m + 1) :=
  next_σ_left_succ hW (tu_letters X Y m d).2.1 hs hb

theorem tu_T18 {s : Slot Vu} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vu (X.length + 2) q = false) (hqm : m + 3 ≤ q) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vu (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e2, (tu_letters X Y m d).2.1]; simp only [idx, coarity]; omega)
  rw [e2, (tu_letters X Y m d).2.1] at this
  simpa [arity, coarity] using this

theorem tu_T19 {s : Slot Vu} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vu (X.length + 3) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 2, q) ∧ bit Vu (X.length + 2) q = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_lt hW hs hq hb (by rw [e3, (tu_letters X Y m d).2.2]; exact hqm)
  rwa [e3] at this

theorem tu_T20 {s : Slot Vu} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vu (X.length + 3) q = false) (hqm : m ≤ q) :
    (next hW s).1 = (X.length + 2, q + 2) ∧ bit Vu (X.length + 2) (q + 2) = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_ge hW hs hq hb (by rw [e3, (tu_letters X Y m d).2.2]; simpa [idx, coarity] using hqm)
  rw [e3, (tu_letters X Y m d).2.2] at this
  simpa [arity, coarity] using this

/-! the chain of the curl -/

include hm in
theorem tu_isSlot_u0 : IsSlot Vu (twd X.length m d 0) := by
  have h1 := tu_cutlen X Y m d hW
  have h2 := tu_cut_end X Y m d hm hW
  have hlen := tu_length X Y m d
  cases d
  · have e0 : twd X.length m false 0 = (X.length, m) := rfl
    rw [e0]
    exact isSlot_cut hm h1 (by omega)
  · have e0 : twd X.length m true 0 = (X.length + 3, m) := rfl
    rw [e0]
    exact isSlot_cut hm (by rw [h2]; exact h1) (by omega)

include hm in
/-- the arc of the curl in the realization: nine pieces from the entry of the through-strand -/
def tuChain : Chain Vu := ⟨⟨twd X.length m d 0, tu_isSlot_u0 X Y m d hm hW⟩, 9, by norm_num⟩

include hm in
theorem tu_slot_val : ∀ j, j ≤ 9 → ((tuChain X Y m d hm hW).slot hW j).1 = twd X.length m d j := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩ := tu_bits X Y m d hm hW
  have s0 : ((tuChain X Y m d hm hW).slot hW 0).1 = twd X.length m d 0 := rfl
  intro j hj
  cases d
  · -- rightward through-strand: forward
    simp only [twd, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((tuChain X Y m false hm hW).slot hW 1).1 = tw X.length m 1 := by
      rw [Chain.slot_succ]; exact (tu_T2 X Y m false hW s0 (by omega) B0 le_rfl).1
    have s2 : ((tuChain X Y m false hm hW).slot hW 2).1 = tw X.length m 2 := by
      rw [Chain.slot_succ]; exact tu_T5 X Y m false hW s1 B3
    have s3 : ((tuChain X Y m false hm hW).slot hW 3).1 = tw X.length m 3 := by
      rw [Chain.slot_succ]; exact tu_T8 X Y m false hW s2 (Or.inr rfl) B5
    have s4 : ((tuChain X Y m false hm hW).slot hW 4).1 = tw X.length m 4 := by
      rw [Chain.slot_succ, tu_T10 X Y m false hW s3, B4]; rfl
    have s5 : ((tuChain X Y m false hm hW).slot hW 5).1 = tw X.length m 5 := by
      rw [Chain.slot_succ]; exact (tu_T15 X Y m false hW s4 (by omega) B4 (by omega)).1
    have s6 : ((tuChain X Y m false hm hW).slot hW 6).1 = tw X.length m 6 := by
      rw [Chain.slot_succ]; exact tu_T12 X Y m false hW s5 (Or.inl rfl) B1
    have s7 : ((tuChain X Y m false hm hW).slot hW 7).1 = tw X.length m 7 := by
      rw [Chain.slot_succ, tu_T14 X Y m false hW s6]; rfl
    have s8 : ((tuChain X Y m false hm hW).slot hW 8).1 = tw X.length m 8 := by
      rw [Chain.slot_succ]; exact tu_T4 X Y m false hW s7 B2
    have s9 : ((tuChain X Y m false hm hW).slot hW 9).1 = tw X.length m 9 := by
      rw [Chain.slot_succ]
      have := (tu_T9 X Y m false hW s8 (by omega) B6 le_rfl).1
      rwa [show m + 2 - 2 = m by omega] at this
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
    · exact s8
    · exact s9
  · -- leftward through-strand: the vertices in reverse
    simp only [twd, ↓reduceIte] at s0 ⊢
    have s1 : ((tuChain X Y m true hm hW).slot hW 1).1 = tw X.length m 8 := by
      rw [Chain.slot_succ]; exact (tu_T20 X Y m true hW s0 (by omega) B7 le_rfl).1
    have s2 : ((tuChain X Y m true hm hW).slot hW 2).1 = tw X.length m 7 := by
      rw [Chain.slot_succ]; exact tu_T17 X Y m true hW s1 B6
    have s3 : ((tuChain X Y m true hm hW).slot hW 3).1 = tw X.length m 6 := by
      rw [Chain.slot_succ]; exact tu_T12 X Y m true hW s2 (Or.inr rfl) B2
    have s4 : ((tuChain X Y m true hm hW).slot hW 4).1 = tw X.length m 5 := by
      rw [Chain.slot_succ, tu_T14 X Y m true hW s3]; rfl
    have s5 : ((tuChain X Y m true hm hW).slot hW 5).1 = tw X.length m 4 := by
      rw [Chain.slot_succ]; exact (tu_T3 X Y m true hW s4 (by omega) B1 (by omega)).1
    have s6 : ((tuChain X Y m true hm hW).slot hW 6).1 = tw X.length m 3 := by
      rw [Chain.slot_succ]; exact tu_T8 X Y m true hW s5 (Or.inl rfl) B4
    have s7 : ((tuChain X Y m true hm hW).slot hW 7).1 = tw X.length m 2 := by
      rw [Chain.slot_succ, tu_T10 X Y m true hW s6, B4]; rfl
    have s8 : ((tuChain X Y m true hm hW).slot hW 8).1 = tw X.length m 1 := by
      rw [Chain.slot_succ]; exact tu_T16 X Y m true hW s7 B5
    have s9 : ((tuChain X Y m true hm hW).slot hW 9).1 = tw X.length m 0 := by
      rw [Chain.slot_succ]
      have := (tu_T13 X Y m true hW s8 (by omega) B3 le_rfl).1
      rwa [show m + 2 - 2 = m by omega] at this
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
    · exact s8
    · exact s9

include hm in
theorem tu_col : ∀ j, j < 9 → colOf ((tuChain X Y m d hm hW).slot hW j) = if d then tcol X.length (8 - j) else tcol X.length j := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩ := tu_bits X Y m d hm hW
  have hv := tu_slot_val X Y m d hm hW
  intro j hj
  cases d
  · simp only [twd, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp; omega) (by simpa [tw] using B0)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp) (by simpa [tw] using B3)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp) (by simpa [tw] using B5)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_false (hv 4 (by norm_num)) (by simp; omega) (by simpa [tw] using B4)]; rfl
    · rw [block_col_false (hv 5 (by norm_num)) (by simp; omega) (by simpa [tw] using B1)]; rfl
    · rw [block_col_vertex (hv 6 (by norm_num))]; rfl
    · rw [block_col_true (hv 7 (by norm_num)) (by simp) (by simpa [tw] using B2)]; rfl
    · rw [block_col_true (hv 8 (by norm_num)) (by simp) (by simpa [tw] using B6)]; rfl
  · simp only [twd, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp; omega) (by simpa [tw] using B7)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp) (by simpa [tw] using B6)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp) (by simpa [tw] using B2)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_true (hv 4 (by norm_num)) (by simp; omega) (by simpa [tw] using B1)]; rfl
    · rw [block_col_true (hv 5 (by norm_num)) (by simp; omega) (by simpa [tw] using B4)]; rfl
    · rw [block_col_vertex (hv 6 (by norm_num))]; rfl
    · rw [block_col_false (hv 7 (by norm_num)) (by simp) (by simpa [tw] using B5)]; rfl
    · rw [block_col_false (hv 8 (by norm_num)) (by simp) (by simpa [tw] using B3)]; rfl

include hm in
theorem tu_col_block : ∀ j, j < 9 → ¬ ExtCol X Pu (colOf ((tuChain X Y m d hm hW).slot hW j)) := by
  intro j hj
  rw [tu_col X Y m d hm hW j hj, tu_extCol]
  cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> interval_cases j <;> simp [tcol]

include hm in
theorem tu_col9 : ExtCol X Pu (colOf ((tuChain X Y m d hm hW).slot hW 9)) := by
  obtain ⟨B0, -, -, -, -, -, -, B7⟩ := tu_bits X Y m d hm hW
  have hv := tu_slot_val X Y m d hm hW 9 le_rfl
  rw [tu_extCol]
  cases d
  · simp only [twd, Bool.false_eq_true, ↓reduceIte, tw] at hv
    rw [block_col_true hv (by omega) B7]; omega
  · simp only [twd, ↓reduceIte, tw] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) B0]; omega

include hm in
theorem tu_exits_core : ∀ u : Slot Vu, ∃ v, (nextPerm hW).SameCycle u v ∧ (colOf v + 1 ≤ X.length ∨ X.length + 3 ≤ colOf v) := by
  intro u
  by_contra hex
  have hall : ∀ v, (nextPerm hW).SameCycle u v → X.length ≤ colOf v ∧ colOf v < X.length + 3 := by
    intro v hv
    by_contra h
    exact hex ⟨v, hv, by omega⟩
  obtain ⟨⟨v, hsc, hv0, ⟨m', hℓ⟩, ha, hb⟩, -⟩ := exists_cusps_of_no_ext hW X.length (X.length + 3) u hall
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tu_letters X Y m d
  have hj : v.1.1 = X.length + 2 := by
    have : v.1.1 = X.length ∨ v.1.1 = X.length + 1 ∨ v.1.1 = X.length + 2 := by omega
    rcases this with h | h | h
    · rw [h, hℓ₀] at hℓ; cases hℓ
    · rw [h, hℓ₁] at hℓ; cases hℓ
    · exact h
  have hv : v.1 = (X.length + 2, 0) := Prod.ext hj hv0
  have hchain : ∃ j, j < 9 ∧ (tuChain X Y m d hm hW).slot hW j = v := by
    have hs := tu_slot_val X Y m d hm hW
    cases d
    · exact ⟨3, by norm_num, Subtype.ext ((hs 3 (by norm_num)).trans hv.symm)⟩
    · exact ⟨6, by norm_num, Subtype.ext ((hs 6 (by norm_num)).trans hv.symm)⟩
  obtain ⟨j, hj9, hjs⟩ := hchain
  have hsc9 : (nextPerm hW).SameCycle v ((tuChain X Y m d hm hW).slot hW 9) := by
    refine sameCycle_of_iterate hW (a := 9 - j) (b := 0) ?_
    rw [← hjs]
    show (next hW)^[9 - j] ((next hW)^[j] (tuChain X Y m d hm hW).u₀) = (next hW)^[9] (tuChain X Y m d hm hW).u₀
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
  have h9 := hall _ (hsc.trans hsc9)
  have := tu_col9 X Y m d hm hW
  rw [tu_extCol] at this
  omega

include hm in
theorem tu_hexit : ∀ u : Slot Vu, ∃ n, ExtPiece X Pu Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨v, hsc, hcol⟩ := tu_exits_core X Y m d hm hW u
  obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW hsc
  exact ⟨n, by rw [hn]; show ExtCol X Pu (colOf v); rw [tu_extCol]; exact hcol⟩

include hm in
/-- THE BLOCK PASSAGE of the curl `l_m σ_{m+1} r_m` (`P' = []`). -/
theorem tu_passage (hW' : (X ++ [] ++ Y).Closed) : Passage X Pu Y [] hW hW' := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tu_letters X Y m d
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩ := tu_bits X Y m d hm hW
  have hP : Pu ≠ [] := by simp
  have hE := tu_sameEffect X Y m d hm hW
  constructor
  intro b hext hcol
  have side : ∀ {c : Slot Vu}, extPair X Pu [] b.1 = extPair X Pu [] c.1 →
      ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pu [] b.1 ∧
        ((next hW')^[m'] b').1 = extPair X Pu [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) :=
    fun hbc => ⟨0, ⟨_, isSlot_ext X Pu Y [] hP hE b.2 hext⟩, rfl, hbc, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  have shiftL : ∀ p, extPair X Pu [] (X.length, p) = extPair X Pu [] (X.length + 3, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pu [] le_rfl, tu_shift X m d]
  have curl : b = (tuChain X Y m d hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Vu), (next hW)^[n] b = c ∧ ExtCol X Pu (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pu (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pu [] b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pu [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨9, (tuChain X Y m d hm hW).slot hW 9, by rw [hb]; rfl, tu_col9 X Y m d hm hW, ?_, side ?_⟩
    · intro i hi
      have := tu_col_block X Y m d hm hW i hi
      rwa [hb] at *
    · rw [hb]
      have h0 := tu_slot_val X Y m d hm hW 0 (by norm_num)
      have h9 := tu_slot_val X Y m d hm hW 9 le_rfl
      rw [Chain.slot_zero] at h0
      rw [h0, h9]
      cases d
      · simp only [twd, Bool.false_eq_true, ↓reduceIte, tw]; exact shiftL _
      · simp only [twd, ↓reduceIte, tw]; exact (shiftL _).symm
  rcases (entry_iff X Pu Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hcol0 : ¬ ExtCol X Pu (colOf b) := by rw [block_col_true hb hp hbit, tu_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := tu_T1 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := tu_T3 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨h3, hb3⟩ := tu_T7 X Y m d hW h2 hp hb2 hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pu) hcol0
        (passage_step hW (ExtCol X Pu) (by rw [block_col_true h1 hp hb1, tu_extCol]; omega)
        (passage_step hW (ExtCol X Pu) (by rw [block_col_true h2 hp hb2, tu_extCol]; omega) (passage_end hW)))
      refine ⟨n, _, hc, by rw [block_col_true h3 hp hb3, tu_extCol]; omega, hmin, side ?_⟩
      rw [hb, h3]; exact shiftL p
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
    · -- `p = m`: the through-strand, `d = false`
      have hd : d = false := by rw [← hpe, B0] at hbit; simpa using hbit
      apply curl
      apply Subtype.ext
      rw [hb, ← hpe]
      show _ = twd X.length m d 0
      rw [hd]; rfl
    · obtain ⟨h1, hb1⟩ := tu_T2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := tu_T6 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨h3, hb3⟩ := tu_T9 X Y m d hW h2 (by omega) hb2 (by omega)
      rw [show p + 2 - 2 = p by omega] at h3 hb3
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pu) hcol0
        (passage_step hW (ExtCol X Pu) (by rw [block_col_true h1 (by omega) hb1, tu_extCol]; omega)
        (passage_step hW (ExtCol X Pu) (by rw [block_col_true h2 (by omega) hb2, tu_extCol]; omega) (passage_end hW)))
      refine ⟨n, _, hc, by rw [block_col_true h3 hp hb3, tu_extCol]; omega, hmin, side ?_⟩
      rw [hb, h3]; exact shiftL p
  · -- from the right at `(|X|+3, q)`
    replace hb : b.1 = (X.length + 3, p) := hb
    replace hbit : bit Vu (X.length + 3) p = false := hbit
    have hcol0 : ¬ ExtCol X Pu (colOf b) := by rw [block_col_false hb hp hbit, tu_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := tu_T19 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := tu_T15 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨h3, hb3⟩ := tu_T11 X Y m d hW h2 hp hb2 hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pu) hcol0
        (passage_step hW (ExtCol X Pu) (by rw [block_col_false h1 hp hb1, tu_extCol]; omega)
        (passage_step hW (ExtCol X Pu) (by rw [block_col_false h2 hp hb2, tu_extCol]; omega) (passage_end hW)))
      have hk3 := (cutSlot_facts hW h3 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 hp hb3, tu_extCol]; omega, hmin, side ?_⟩
      rw [hb, h3]; exact (shiftL p).symm
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
    · have hd : d = true := by rw [← hpe, B7] at hbit; simpa using hbit
      apply curl
      apply Subtype.ext
      rw [hb, ← hpe]
      show _ = twd X.length m d 0
      rw [hd]; rfl
    · obtain ⟨h1, hb1⟩ := tu_T20 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := tu_T18 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨h3, hb3⟩ := tu_T13 X Y m d hW h2 (by omega) hb2 (by omega)
      rw [show p + 2 - 2 = p by omega] at h3 hb3
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pu) hcol0
        (passage_step hW (ExtCol X Pu) (by rw [block_col_false h1 (by omega) hb1, tu_extCol]; omega)
        (passage_step hW (ExtCol X Pu) (by rw [block_col_false h2 (by omega) hb2, tu_extCol]; omega) (passage_end hW)))
      have hk3 := (cutSlot_facts hW h3 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 hp hb3, tu_extCol]; omega, hmin, side ?_⟩
      rw [hb, h3]; exact (shiftL p).symm

end TypeIRightWord

/-! #### F5. The type-I curl, right variant: the moved diagram -/

/-- the moved positions of the ten vertices of the curl `l_m σ_{m+1} r_m` (top height `h = −m`) -/
def mvw (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h + 3 / 8)
  | 2 => (((k + 2 : ℕ) : ℝ), h + 5 / 8)
  | 3 => (((k + 2 : ℕ) : ℝ) + 1 / 2, h + 1 / 4)
  | 4 => (((k + 2 : ℕ) : ℝ), h)
  | 5 => (((k + 1 : ℕ) : ℝ), h)
  | 6 => ((k : ℝ) + 1 / 2, h - 1 / 4)
  | 7 => (((k + 1 : ℕ) : ℝ), h - 3 / 8)
  | 8 => (((k + 2 : ℕ) : ℝ), h - 5 / 8)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the realization's positions of the ten vertices -/
def pww (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h - 2)
  | 2 => (((k + 2 : ℕ) : ℝ), h - 1)
  | 3 => (((k + 2 : ℕ) : ℝ) + 1 / 2, h - 1 / 2)
  | 4 => (((k + 2 : ℕ) : ℝ), h)
  | 5 => (((k + 1 : ℕ) : ℝ), h)
  | 6 => ((k : ℝ) + 1 / 2, h - 1 / 2)
  | 7 => (((k + 1 : ℕ) : ℝ), h - 1)
  | 8 => (((k + 2 : ℕ) : ℝ), h - 2)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the six moved slots -/
def IsMovedU (k m : ℕ) (s : ℕ × ℕ) : Prop :=
  s = (k + 1, m + 2) ∨ s = (k + 2, m + 1) ∨ s = (k + 2, 0) ∨ s = (k, 0) ∨ s = (k + 1, m + 1) ∨ s = (k + 2, m + 2)

/-- the moved vertex function -/
def mvU (W : Word) (k m : ℕ) (h : ℝ) (u : Slot W) : Plane :=
  if u.1 = (k + 1, m + 2) then mvw k h 1
  else if u.1 = (k + 2, m + 1) then mvw k h 2
  else if u.1 = (k + 2, 0) then mvw k h 3
  else if u.1 = (k, 0) then mvw k h 6
  else if u.1 = (k + 1, m + 1) then mvw k h 7
  else if u.1 = (k + 2, m + 2) then mvw k h 8
  else pt .std W u.1

section MvU

variable (W : Word) (k m : ℕ) (h : ℝ)

theorem mvU_of_not_moved {u : Slot W} (hu : ¬ IsMovedU k m u.1) : mvU W k m h u = pt .std W u.1 := by
  unfold IsMovedU at hu
  simp only [not_or] at hu
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
  simp [mvU, h1, h2, h3, h4, h5, h6]

theorem mvU_v1 {u : Slot W} (hu : u.1 = (k + 1, m + 2)) : mvU W k m h u = mvw k h 1 := by simp [mvU, hu]
theorem mvU_v2 {u : Slot W} (hu : u.1 = (k + 2, m + 1)) : mvU W k m h u = mvw k h 2 := by simp [mvU, hu]
theorem mvU_v3 {u : Slot W} (hu : u.1 = (k + 2, 0)) : mvU W k m h u = mvw k h 3 := by simp [mvU, hu]
theorem mvU_v6 {u : Slot W} (hu : u.1 = (k, 0)) : mvU W k m h u = mvw k h 6 := by simp [mvU, hu]
theorem mvU_v7 {u : Slot W} (hu : u.1 = (k + 1, m + 1)) : mvU W k m h u = mvw k h 7 := by simp [mvU, hu]
theorem mvU_v8 {u : Slot W} (hu : u.1 = (k + 2, m + 2)) : mvU W k m h u = mvw k h 8 := by simp [mvU, hu]

theorem mvU_of_ext {u : Slot W} (hu : ExtSl k (k + 3) u.1) : mvU W k m h u = pt .std W u.1 := by
  apply mvU_of_not_moved
  obtain ⟨j, p, hu'⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu'] at hu ⊢
  unfold ExtSl at hu
  unfold IsMovedU
  simp only [Prod.mk.injEq]
  split_ifs at hu with h0 <;> omega

theorem mvU_xcoord (u : Slot W) : (mvU W k m h u).1 = (pt .std W u.1).1 := by
  by_cases hmv : IsMovedU k m u.1
  · unfold IsMovedU at hmv
    rcases hmv with e | e | e | e | e | e
    · rw [mvU_v1 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvU_v2 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvU_v3 W k m h e, e, std_pt_cusp]; rfl
    · rw [mvU_v6 W k m h e, e, std_pt_cusp]; rfl
    · rw [mvU_v7 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvU_v8 W k m h e, e, std_pt_cut _ (by omega)]; rfl
  · rw [mvU_of_not_moved W k m h hmv]

/-- `−n + o/8` with `o` odd is a non-grid height -/
theorem nonGrid_eighth0 (n : ℕ) (o : ℤ) (ho : o % 2 = 1) : NonGrid (-(n : ℝ) + (o : ℝ) / 8) := by
  constructor
  · intro p hp
    have h8 : ((8 * (p : ℤ) - 8 * (n : ℤ) : ℤ) : ℝ) = ((-o : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective (α := ℝ) h8
    omega
  · intro q hq
    have h8 : ((8 * (q : ℤ) - 8 * (n : ℤ) + 4 : ℤ) : ℝ) = ((-o : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective (α := ℝ) h8
    omega

/-- `−n + o/4` with `o` odd is a non-grid height -/
theorem nonGrid_quarter0 (n : ℕ) (o : ℤ) (ho : o % 2 = 1) : NonGrid (-(n : ℝ) + (o : ℝ) / 4) := by
  constructor
  · intro p hp
    have h4 : ((4 * (p : ℤ) - 4 * (n : ℤ) : ℤ) : ℝ) = ((-o : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective (α := ℝ) h4
    omega
  · intro q hq
    have h4 : ((4 * (q : ℤ) - 4 * (n : ℤ) + 2 : ℤ) : ℝ) = ((-o : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective (α := ℝ) h4
    omega

theorem mvU_injective (n : ℕ) : Function.Injective (mvU W k m (-(n : ℝ))) := by
  have ng : ∀ i, 1 ≤ i → i ≤ 8 → i ≠ 4 → i ≠ 5 → ∀ s, mvw k (-(n : ℝ)) i ≠ pt .std W s := by
    intro i hi1 hi2 hi4 hi5 s
    interval_cases i
    · have := nonGrid_eighth0 n 3 (by decide)
      have e : -(n : ℝ) + 3 / 8 = -(n : ℝ) + ((3 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 1 : ℕ) : ℝ), -(n : ℝ) + 3 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth0 n 5 (by decide)
      have e : -(n : ℝ) + 5 / 8 = -(n : ℝ) + ((5 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ), -(n : ℝ) + 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_quarter0 n 1 (by decide)
      have e : -(n : ℝ) + 1 / 4 = -(n : ℝ) + ((1 : ℤ) : ℝ) / 4 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ) + 1 / 2, -(n : ℝ) + 1 / 4) ≠ _
      rw [e]; exact this.ne_pt_half W (k + 2) s
    · exact absurd rfl hi4
    · exact absurd rfl hi5
    · have := nonGrid_quarter0 n (-1) (by decide)
      have e : -(n : ℝ) - 1 / 4 = -(n : ℝ) + ((-1 : ℤ) : ℝ) / 4 := by push_cast; ring
      show ((k : ℝ) + 1 / 2, -(n : ℝ) - 1 / 4) ≠ _
      rw [e]; exact this.ne_pt_half W k s
    · have := nonGrid_eighth0 n (-3) (by decide)
      have e : -(n : ℝ) - 3 / 8 = -(n : ℝ) + ((-3 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 1 : ℕ) : ℝ), -(n : ℝ) - 3 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · have := nonGrid_eighth0 n (-5) (by decide)
      have e : -(n : ℝ) - 5 / 8 = -(n : ℝ) + ((-5 : ℤ) : ℝ) / 8 := by push_cast; ring
      show (((k + 2 : ℕ) : ℝ), -(n : ℝ) - 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
  have hval : ∀ u : Slot W, IsMovedU k m u.1 → ∃ i, 1 ≤ i ∧ i ≤ 8 ∧ i ≠ 4 ∧ i ≠ 5 ∧
      mvU W k m (-(n : ℝ)) u = mvw k (-(n : ℝ)) i ∧ u.1 = tw k m i := by
    intro u hu
    unfold IsMovedU at hu
    rcases hu with e | e | e | e | e | e
    · exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num, mvU_v1 W k m _ e, e⟩
    · exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num, mvU_v2 W k m _ e, e⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, mvU_v3 W k m _ e, e⟩
    · exact ⟨6, by norm_num, by norm_num, by norm_num, by norm_num, mvU_v6 W k m _ e, e⟩
    · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num, mvU_v7 W k m _ e, e⟩
    · exact ⟨8, by norm_num, by norm_num, by norm_num, by norm_num, mvU_v8 W k m _ e, e⟩
  have hdist : ∀ i j, 1 ≤ i → i ≤ 8 → i ≠ 4 → i ≠ 5 → 1 ≤ j → j ≤ 8 → j ≠ 4 → j ≠ 5 →
      mvw k (-(n : ℝ)) i = mvw k (-(n : ℝ)) j → i = j := by
    intro i j hi1 hi2 hi4 hi5 hj1 hj2 hj4 hj5 he
    interval_cases i <;> interval_cases j <;> first | rfl | omega | (exfalso; have := congrArg Prod.snd he; simp only [mvw] at this; linarith)
  intro u v huv
  by_cases hu : IsMovedU k m u.1
  · obtain ⟨i, hi1, hi2, hi4, hi5, hui, hu'⟩ := hval u hu
    by_cases hv : IsMovedU k m v.1
    · obtain ⟨j, hj1, hj2, hj4, hj5, hvj, hv'⟩ := hval v hv
      have := hdist i j hi1 hi2 hi4 hi5 hj1 hj2 hj4 hj5 (hui.symm.trans (huv.trans hvj))
      subst this
      exact Subtype.ext (hu'.trans hv'.symm)
    · rw [hui, mvU_of_not_moved W k m _ hv] at huv
      exact absurd huv (ng i hi1 hi2 hi4 hi5 _)
  · by_cases hv : IsMovedU k m v.1
    · obtain ⟨j, hj1, hj2, hj4, hj5, hvj, -⟩ := hval v hv
      rw [hvj, mvU_of_not_moved W k m _ hu] at huv
      exact absurd huv.symm (ng j hj1 hj2 hj4 hj5 _)
    · rw [mvU_of_not_moved W k m _ hu, mvU_of_not_moved W k m _ hv] at huv
      exact pt_inj _ _ huv

end MvU

section TURVertices

variable (k : ℕ) (h : ℝ)

theorem mvw_int : ∀ i, 1 ≤ i → i ≤ 8 → mvw k h i ∈ interior (polygon (tL k h)) := by
  intro i h1 h8
  interval_cases i
  · exact tI_int_cut1 k h (3 / 8) (by norm_num) (by norm_num)
  · exact tI_int_cut2 k h (5 / 8) (by norm_num) (by norm_num)
  · exact tI_int_cuspR k h (1 / 4) (by norm_num) (by norm_num)
  · have := tI_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tI_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tI_int_cuspL k h (-(1 / 4)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut1 k h (-(3 / 8)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut2 k h (-(5 / 8)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem pww_int : ∀ i, 1 ≤ i → i ≤ 8 → pww k h i ∈ interior (polygon (tL k h)) := by
  intro i h1 h8
  interval_cases i
  · have := tI_int_cut1 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut2 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cuspR k h (-(1 / 2)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tI_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tI_int_cuspL k h (-(1 / 2)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut1 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tI_int_cut2 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem mvw_mem : ∀ i, i ≤ 9 → mvw k h i ∈ polygon (tL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · exact tI_mem_left k h
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · exact interior_subset (mvw_int k h i h0 (by omega))
  · have : i = 9 := by omega
    subst this
    exact tI_mem_right k h

theorem pww_mem : ∀ i, i ≤ 9 → pww k h i ∈ polygon (tL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · exact tI_mem_left k h
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · exact interior_subset (pww_int k h i h0 (by omega))
  · have : i = 9 := by omega
    subst this
    exact tI_mem_right k h

macro "tU_pair" : tactic => `(tactic| (
  intro τ τ' h0 h1 h0' h1' he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [mvw, segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy))

theorem tU_NM05 : NoMeet (mvw k h 0) (mvw k h 1) (mvw k h 5) (mvw k h 6) := by tU_pair; linarith
theorem tU_NM06 : NoMeet (mvw k h 0) (mvw k h 1) (mvw k h 6) (mvw k h 7) := by tU_pair; linarith
theorem tU_NM14 : NoMeet (mvw k h 1) (mvw k h 2) (mvw k h 4) (mvw k h 5) := by tU_pair; linarith
theorem tU_NM17 : NoMeet (mvw k h 1) (mvw k h 2) (mvw k h 7) (mvw k h 8) := by tU_pair; linarith
theorem tU_NM47 : NoMeet (mvw k h 4) (mvw k h 5) (mvw k h 7) (mvw k h 8) := by tU_pair; linarith
theorem tU_NM28 : NoMeet (mvw k h 2) (mvw k h 3) (mvw k h 8) (mvw k h 9) := by tU_pair; linarith
theorem tU_NM38 : NoMeet (mvw k h 3) (mvw k h 4) (mvw k h 8) (mvw k h 9) := by tU_pair; linarith
theorem tU_OJ56 : OnlyAtJoint (mvw k h 5) (mvw k h 6) (mvw k h 7) := by
  tU_pair; constructor <;> linarith
theorem tU_OJ23 : OnlyAtJoint (mvw k h 2) (mvw k h 3) (mvw k h 4) := by
  tU_pair; constructor <;> linarith

end TURVertices

/-! #### F7. The type-I curl, right variant: the specification and the leaf case -/

section TypeIRightSpec

open U3

variable (X Y : Word) (m : ℕ) (d : Bool) (hm : 1 ≤ m) (hW : (X ++ [Letter.l m d, Letter.σ (m + 1), Letter.r m] ++ Y).Closed)

local notation "Vu" => X ++ [Letter.l m d, Letter.σ (m + 1), Letter.r m] ++ Y
local notation "Pu" => [Letter.l m d, Letter.σ (m + 1), Letter.r m]
local notation "hU" => (-(m : ℝ))

/-- the moved vertex function of the right type-I curl -/
def tuMv : Slot Vu → Plane := mvU Vu X.length m hU

theorem tuMv_apply (u : Slot Vu) : tuMv X Y m d u = mvU Vu X.length m hU u := rfl

include hm in
theorem tw_inj : ∀ i j, i ≤ 9 → j ≤ 9 → tw X.length m i = tw X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tw, Prod.mk.injEq] at he; omega)

include hm in
theorem tu_pt_tw : ∀ i, i ≤ 9 → pt .std Vu (tw X.length m i) = pww X.length hU i := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tu_letters X Y m d
  intro i hi
  interval_cases i
  · show pt .std Vu (X.length, m) = _
    rw [std_pt_cut _ (by omega)]; rfl
  · show pt .std Vu (X.length + 1, m + 2) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pww]; push_cast; ring)
  · show pt .std Vu (X.length + 2, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pww]; push_cast; ring)
  · show pt .std Vu (X.length + 2, 0) = _
    rw [std_pt_cusp, hℓ₂]; exact Prod.ext rfl (by simp only [pww, idx])
  · show pt .std Vu (X.length + 2, m) = _
    rw [std_pt_cut _ (by omega)]; rfl
  · show pt .std Vu (X.length + 1, m) = _
    rw [std_pt_cut _ (by omega)]; rfl
  · show pt .std Vu (X.length, 0) = _
    rw [std_pt_cusp, hℓ₀]; exact Prod.ext rfl (by simp only [pww, idx])
  · show pt .std Vu (X.length + 1, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pww]; push_cast; ring)
  · show pt .std Vu (X.length + 2, m + 2) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pww]; push_cast; ring)
  · show pt .std Vu (X.length + 3, m) = _
    rw [std_pt_cut _ (by omega)]; rfl

include hm in
theorem tu_mv_tw : ∀ i, i ≤ 9 → ∀ u : Slot Vu, u.1 = tw X.length m i → tuMv X Y m d u = mvw X.length hU i := by
  intro i hi u hu
  rw [tuMv_apply]
  have hnm : ∀ i, i = 0 ∨ i = 4 ∨ i = 5 ∨ i = 9 → ¬ IsMovedU X.length m (tw X.length m i) := by
    intro i hi h
    rcases hi with rfl | rfl | rfl | rfl <;> rcases h with h | h | h | h | h | h <;>
      simp only [tw, Prod.mk.injEq] at h <;> omega
  interval_cases i
  · rw [mvU_of_not_moved _ _ _ _ (hu ▸ hnm 0 (by simp)), hu, tu_pt_tw X Y m d hm 0 (by norm_num)]; rfl
  · exact mvU_v1 _ _ _ _ hu
  · exact mvU_v2 _ _ _ _ hu
  · exact mvU_v3 _ _ _ _ hu
  · rw [mvU_of_not_moved _ _ _ _ (hu ▸ hnm 4 (by simp)), hu, tu_pt_tw X Y m d hm 4 (by norm_num)]; rfl
  · rw [mvU_of_not_moved _ _ _ _ (hu ▸ hnm 5 (by simp)), hu, tu_pt_tw X Y m d hm 5 (by norm_num)]; rfl
  · exact mvU_v6 _ _ _ _ hu
  · exact mvU_v7 _ _ _ _ hu
  · exact mvU_v8 _ _ _ _ hu
  · rw [mvU_of_not_moved _ _ _ _ (hu ▸ hnm 9 (by simp)), hu, tu_pt_tw X Y m d hm 9 (by norm_num)]; rfl

include hm hW

theorem tu_mv_slot : ∀ j, j ≤ 9 → tuMv X Y m d ((tuChain X Y m d hm hW).slot hW j) =
    if d then mvw X.length hU (9 - j) else mvw X.length hU j := by
  intro j hj
  have hs := tu_slot_val X Y m d hm hW j hj
  cases d
  · simp only [twd, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact tu_mv_tw X Y m false hm j hj _ hs
  · simp only [twd, ↓reduceIte] at hs ⊢
    exact tu_mv_tw X Y m true hm (9 - j) (by omega) _ hs

theorem tu_pt_slot : ∀ j, j ≤ 9 → pt .std Vu ((tuChain X Y m d hm hW).slot hW j).1 =
    if d then pww X.length hU (9 - j) else pww X.length hU j := by
  intro j hj
  have hs := tu_slot_val X Y m d hm hW j hj
  cases d
  · simp only [twd, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact tu_pt_tw X Y m false hm j hj
  · simp only [twd, ↓reduceIte] at hs ⊢
    rw [hs]; exact tu_pt_tw X Y m true hm (9 - j) (by omega)

theorem tu_next_slot : ∀ j, j < 9 → next hW ((tuChain X Y m d hm hW).slot hW j) = (tuChain X Y m d hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

theorem tu_chain_in : ∀ j, j < 9 → PieceIn (tL X.length hU) hW (tuMv X Y m d) ((tuChain X Y m d hm hW).slot hW j) ∧
    PieceIn (tL X.length hU) hW (ptv .std) ((tuChain X Y m d hm hW).slot hW j) := by
  intro j hj
  have e := tu_next_slot X Y m d hm hW j hj
  constructor
  · show SegIn _ (tuMv X Y m d _) (tuMv X Y m d (next hW _))
    rw [e, tu_mv_slot X Y m d hm hW j (by omega), tu_mv_slot X Y m d hm hW (j + 1) (by omega)]
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (mvw_mem _ _ _ (by omega)) (mvw_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (mvw_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (mvw_int _ _ _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (mvw_mem _ _ _ (by omega)) (mvw_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (mvw_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (mvw_int _ _ _ (by omega) (by omega))
  · show SegIn _ (pt .std Vu _) (pt .std Vu (next hW _).1)
    rw [e, tu_pt_slot X Y m d hm hW j (by omega), tu_pt_slot X Y m d hm hW (j + 1) (by omega)]
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (pww_mem _ _ _ (by omega)) (pww_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pww_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pww_int _ _ _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (pww_mem _ _ _ (by omega)) (pww_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pww_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pww_int _ _ _ (by omega) (by omega))

theorem tu_vert : ∀ j, 0 < j → j < 9 → tuMv X Y m d ((tuChain X Y m d hm hW).slot hW j) ∈ interior (polygon (tL X.length hU)) ∧
    pt .std Vu ((tuChain X Y m d hm hW).slot hW j).1 ∈ interior (polygon (tL X.length hU)) := by
  intro j h0 hj
  rw [tu_mv_slot X Y m d hm hW j (by omega), tu_pt_slot X Y m d hm hW j (by omega)]
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨mvw_int _ _ _ (by omega) (by omega), pww_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨mvw_int _ _ _ (by omega) (by omega), pww_int _ _ _ (by omega) (by omega)⟩

omit hW in
theorem tu_moved : ∀ u : Slot Vu, tuMv X Y m d u = pt .std Vu u.1 ∨
    (tuMv X Y m d u ∈ interior (polygon (tL X.length hU)) ∧ pt .std Vu u.1 ∈ interior (polygon (tL X.length hU))) := by
  intro u
  by_cases hmv : IsMovedU X.length m u.1
  · right
    have : ∃ i, 1 ≤ i ∧ i ≤ 8 ∧ u.1 = tw X.length m i := by
      unfold IsMovedU at hmv
      rcases hmv with e | e | e | e | e | e
      · exact ⟨1, by norm_num, by norm_num, e⟩
      · exact ⟨2, by norm_num, by norm_num, e⟩
      · exact ⟨3, by norm_num, by norm_num, e⟩
      · exact ⟨6, by norm_num, by norm_num, e⟩
      · exact ⟨7, by norm_num, by norm_num, e⟩
      · exact ⟨8, by norm_num, by norm_num, e⟩
    obtain ⟨i, hi1, hi2, hu⟩ := this
    rw [tu_mv_tw X Y m d hm i (by omega) u hu, hu, tu_pt_tw X Y m d hm i (by omega)]
    exact ⟨mvw_int _ _ _ (by omega) (by omega), pww_int _ _ _ (by omega) (by omega)⟩
  · left
    rw [tuMv_apply, mvU_of_not_moved _ _ _ _ hmv]

/-- the chain slot carrying the vertex `tw i` -/
theorem tu_chain_of (i : ℕ) (hi : i ≤ 9) {u : Slot Vu} (hu : u.1 = tw X.length m i)
    (hd : (d = false ∧ i < 9) ∨ (d = true ∧ 0 < i)) :
    ∃ j, j < 9 ∧ (tuChain X Y m d hm hW).slot hW j = u := by
  cases d
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [tu_slot_val X Y m false hm hW i hi, hu]
      simp only [twd, Bool.false_eq_true, ↓reduceIte]
  · refine ⟨9 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · omega
    · rw [tu_slot_val X Y m true hm hW (9 - i) (by omega), hu]
      simp only [twd, ↓reduceIte, Nat.sub_sub_self hi]

omit hm in
theorem tu_spec {u : Slot Vu} {j p j' p' : ℕ} (hu : u.1 = (j, p)) (hn : (next hW u).1 = (j', p'))
    (hp : p ≠ 0) (hp' : p' ≠ 0) (h1 : ¬ IsMovedU X.length m (j, p)) (h2 : ¬ IsMovedU X.length m (j', p'))
    (hout : SegOut (tL X.length hU) ((j : ℝ), -(p : ℝ)) ((j' : ℝ), -(p' : ℝ))) :
    Unch .std hW (tuMv X Y m d) u ∧ PieceOut (tL X.length hU) hW (ptv .std) u := by
  constructor
  · constructor
    · rw [tuMv_apply, mvU_of_not_moved _ _ _ _ (hu ▸ h1)]
    · rw [tuMv_apply, mvU_of_not_moved _ _ _ _ (hn ▸ h2)]
  · show SegOut _ (pt .std Vu u.1) (pt .std Vu (next hW u).1)
    rw [hu, hn, std_pt_cut _ hp, std_pt_cut _ hp']
    exact hout

omit hm hW in
theorem tu_hmv : ∀ v : Slot Vu, ExtSl X.length (X.length + 3) v.1 → tuMv X Y m d v = pt .std Vu v.1 :=
  fun v hv => by rw [tuMv_apply]; exact mvU_of_ext _ _ _ _ hv

/-- THE CLASSIFICATION of the right type-I curl. -/
theorem tu_rest : ∀ u : Slot Vu, (∃ j, j < 9 ∧ (tuChain X Y m d hm hW).slot hW j = u) ∨
    (Unch .std hW (tuMv X Y m d) u ∧ PieceOut (tL X.length hU) hW (ptv .std) u) := by
  intro u
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7⟩ := tu_bits X Y m d hm hW
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tu_letters X Y m d
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  have above : ∀ {q : ℕ}, q < m → hU + 1 ≤ -(q : ℝ) := fun {q} hq => by
    have : (q : ℝ) + 1 ≤ m := by exact_mod_cast hq
    linarith
  have below : ∀ {q : ℕ}, m + 3 ≤ q → -(q : ℝ) ≤ hU - 3 := fun {q} hq => by
    have : (m : ℝ) + 3 ≤ q := by exact_mod_cast hq
    linarith
  have slant : ∀ {q : ℕ}, m + 1 ≤ q → -(q : ℝ) ≤ hU - 1 := fun {q} hq => by
    have : (m : ℝ) + 1 ≤ q := by exact_mod_cast hq
    linarith
  have chain := tu_chain_of X Y m d hm hW
  by_cases hext : ExtCol X Pu (colOf u)
  · right
    have hext' := (tu_extCol X m d _).1 hext
    exact ⟨unch_of_extCol .std hW _ (tu_hmv X Y m d) hext',
      pieceOut_of_extCol _ .std hW _ (tI_xge_mem _ _) (tI_xle_mem _ _) (unch_pt _ _ _) hext'⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, tu_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl (chain 6 (by norm_num) hu (by cases d; exact Or.inl ⟨rfl, by norm_num⟩; exact Or.inr ⟨rfl, by norm_num⟩))
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₁] at this
      simp [isCrossing] at this
    · exact Or.inl (chain 3 (by norm_num) hu (by cases d; exact Or.inl ⟨rfl, by norm_num⟩; exact Or.inr ⟨rfl, by norm_num⟩))
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vu j p
  · rw [block_col_false hu hp hb, tu_extCol] at hext
    have : j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    rcases this with rfl | rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := tu_T11 X Y m d hW hu hp hb hpm
        exact Or.inr (tu_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_above _ _ (above hpm) _ _))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = false := by rw [hpe, B1] at hb; exact hb
          exact Or.inl (chain 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · have hd : d = true := by rw [hpe, B2] at hb; simpa using hb
          exact Or.inl (chain 7 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · have hd : d = true := by rw [hpe, B3] at hb; simpa using hb
          exact Or.inl (chain 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tu_T13 X Y m d hW hu hp hb (by omega)
        exact Or.inr (tu_spec X Y m d hW hu h1 hp (by omega) (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (tI_out_slantL'' _ _ (by omega) (slant (q := p - 2) (by omega))))
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := tu_T15 X Y m d hW hu hp hb (by omega)
        exact Or.inr (tu_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_above _ _ (above hpm) _ _))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = false := by rw [hpe, B4] at hb; exact hb
          exact Or.inl (chain 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · have hd : d = true := by rw [hpe, B5] at hb; simpa using hb
          exact Or.inl (chain 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · have hd : d = true := by rw [hpe, B6] at hb; simpa using hb
          exact Or.inl (chain 8 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tu_T18 X Y m d hW hu hp hb hpm3
        exact Or.inr (tu_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_below _ _ (below hpm3) _ _))
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := tu_T19 X Y m d hW hu hp hb hpm
        exact Or.inr (tu_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_above _ _ (above hpm) _ _))
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
      · have hd : d = true := by rw [← hpe, B7] at hb; simpa using hb
        exact Or.inl (chain 9 (by norm_num) (by rw [hu, ← hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tu_T20 X Y m d hW hu hp hb hpm
        exact Or.inr (tu_spec X Y m d hW hu h1 hp (by omega) (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_slantR'' _ _ (slant hpe)))
  · rw [block_col_true hu hp hb, tu_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := tu_T1 X Y m d hW hu hp hb hpm
        exact Or.inr (tu_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_above _ _ (above hpm) _ _))
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
      · have hd : d = false := by rw [← hpe, B0] at hb; simpa using hb
        exact Or.inl (chain 0 (by norm_num) (by rw [hu, ← hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tu_T2 X Y m d hW hu hp hb hpm
        exact Or.inr (tu_spec X Y m d hW hu h1 hp (by omega) (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_slantL' _ _ (slant hpe)))
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := tu_T3 X Y m d hW hu hp hb (by omega)
        exact Or.inr (tu_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_above _ _ (above hpm) _ _))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = true := by rw [hpe, B1] at hb; exact hb
          exact Or.inl (chain 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B2] at hb; simpa using hb
          exact Or.inl (chain 7 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B3] at hb; simpa using hb
          exact Or.inl (chain 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tu_T6 X Y m d hW hu hp hb hpm3
        exact Or.inr (tu_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_below _ _ (below hpm3) _ _))
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, -⟩ := tu_T7 X Y m d hW hu hp hb hpm
        exact Or.inr (tu_spec X Y m d hW hu h1 hp hp (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega) (tI_out_above _ _ (above hpm) _ _))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = true := by rw [hpe, B4] at hb; exact hb
          exact Or.inl (chain 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B5] at hb; simpa using hb
          exact Or.inl (chain 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B6] at hb; simpa using hb
          exact Or.inl (chain 8 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩))
      · obtain ⟨h1, -⟩ := tu_T9 X Y m d hW hu hp hb (by omega)
        exact Or.inr (tu_spec X Y m d hW hu h1 hp (by omega) (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (by simp only [IsMovedU, Prod.mk.injEq]; omega)
          (tI_out_slantR' _ _ (by omega) (slant (q := p - 2) (by omega))))

theorem tu_slot_ne : ∀ j j', j ≤ 9 → j' ≤ 9 → j ≠ j' → (tuChain X Y m d hm hW).slot hW j ≠ (tuChain X Y m d hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [tu_slot_val X Y m d hm hW j hj, tu_slot_val X Y m d hm hW j' hj'] at h'
  cases d
  · simp only [twd, Bool.false_eq_true, ↓reduceIte] at h'
    exact hne (tw_inj X m hm j j' hj hj' h')
  · simp only [twd, ↓reduceIte] at h'
    have := tw_inj X m hm (9 - j) (9 - j') (by omega) (by omega) h'
    omega

theorem tu_prevOut : Unch .std hW (tuMv X Y m d) (prev hW (tuChain X Y m d hm hW).u₀) ∧
    PieceOut (tL X.length hU) hW (ptv .std) (prev hW (tuChain X Y m d hm hW).u₀) := by
  rcases tu_rest X Y m d hm hW (prev hW (tuChain X Y m d hm hW).u₀) with ⟨j, hj, hjs⟩ | h
  · exfalso
    have : (tuChain X Y m d hm hW).slot hW (j + 1) = (tuChain X Y m d hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact tu_slot_ne X Y m d hm hW (j + 1) 0 (by omega) (by omega) (by omega) this
  · exact h

theorem tu_stopOut : Unch .std hW (tuMv X Y m d) ((tuChain X Y m d hm hW).slot hW 9) ∧
    PieceOut (tL X.length hU) hW (ptv .std) ((tuChain X Y m d hm hW).slot hW 9) := by
  rcases tu_rest X Y m d hm hW ((tuChain X Y m d hm hW).slot hW 9) with ⟨j, hj, hjs⟩ | h
  · exact absurd hjs (tu_slot_ne X Y m d hm hW j 9 (by omega) (by omega) (by omega))
  · exact h

omit hm hW in
/-- a grid point of the disc is a curl vertex -/
theorem tu_vertex_of_mem {u : Slot Vu} (hmem : pt .std Vu u.1 ∈ polygon (tL X.length hU)) :
    ∃ i, i ≤ 9 ∧ u.1 = tw X.length m i := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tu_letters X Y m d
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu] at hmem
  by_cases hp : p = 0
  · subst hp
    rw [std_pt_cusp] at hmem
    obtain ⟨b1, b2, -, -, -, -⟩ := tI_mem_bounds X.length hU hmem
    have e1 : 2 * X.length ≤ 2 * j + 1 := by exact_mod_cast (by linarith : (2 * X.length : ℝ) ≤ 2 * j + 1)
    have e2 : 2 * j + 1 ≤ 2 * X.length + 6 := by exact_mod_cast (by linarith : (2 * j + 1 : ℝ) ≤ 2 * X.length + 6)
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact ⟨6, by norm_num, hu⟩
    · exfalso
      have := vertex_not_crossing hu
      rw [hℓ₁] at this
      simp [isCrossing] at this
    · exact ⟨3, by norm_num, hu⟩
  · rw [std_pt_cut _ hp] at hmem
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tI_mem_bounds X.length hU hmem
    have e1 : X.length ≤ j := by exact_mod_cast b1
    have e2 : j ≤ X.length + 3 := by exact_mod_cast (by linarith : (j : ℝ) ≤ X.length + 3)
    have e3 : 2 * p ≤ 2 * m + 5 := by exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 2 * m + 5)
    have e4 : 4 * m ≤ 4 * p + 3 := by exact_mod_cast (by linarith : (4 * m : ℝ) ≤ 4 * p + 3)
    have e5 : 4 * p + 8 * X.length ≤ 4 * m + 3 + 8 * j := by
      exact_mod_cast (by linarith : (4 * p + 8 * X.length : ℝ) ≤ 4 * m + 3 + 8 * j)
    have e6 : 4 * p + 8 * j ≤ 4 * m + 3 + 8 * X.length + 24 := by
      exact_mod_cast (by linarith : (4 * p + 8 * j : ℝ) ≤ 4 * m + 3 + 8 * X.length + 24)
    have hj : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    have hpp : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · have : p = m := by omega
      exact ⟨0, by norm_num, by rw [hu, this]; rfl⟩
    · rcases hpp with rfl | rfl | rfl
      · exact ⟨5, by norm_num, hu⟩
      · exact ⟨7, by norm_num, hu⟩
      · exact ⟨1, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact ⟨4, by norm_num, hu⟩
      · exact ⟨2, by norm_num, hu⟩
      · exact ⟨8, by norm_num, hu⟩
    · have : p = m := by omega
      exact ⟨9, by norm_num, by rw [hu, this]; rfl⟩

theorem tu_touch : ∀ u : Slot Vu, PieceOut (tL X.length hU) hW (ptv .std) u → pt .std Vu u.1 ∈ polygon (tL X.length hU) →
    u = (tuChain X Y m d hm hW).slot hW 9 := by
  intro u hout hmem
  obtain ⟨i, hi, hu⟩ := tu_vertex_of_mem X Y m d hmem
  have hchain : ∀ j', j' < 9 → u ≠ (tuChain X Y m d hm hW).slot hW j' := by
    intro j' hj' he
    rw [he] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (tu_chain_in X Y m d hm hW j' hj').2
  have hs := tu_slot_val X Y m d hm hW
  cases d
  · have hu' : u = (tuChain X Y m false hm hW).slot hW i := by
      apply Subtype.ext
      rw [hs i hi, hu]
      simp only [twd, Bool.false_eq_true, ↓reduceIte]
    rcases Nat.lt_or_ge i 9 with h9 | h9
    · exact absurd hu' (hchain i h9)
    · have : i = 9 := by omega
      subst this
      exact hu'
  · have hu' : u = (tuChain X Y m true hm hW).slot hW (9 - i) := by
      apply Subtype.ext
      rw [hs (9 - i) (by omega), hu]
      simp only [twd, ↓reduceIte, Nat.sub_sub_self hi]
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · exact hu'
    · exact absurd hu' (hchain (9 - i) (by omega))

theorem tu_exits : ∀ u : Slot Vu, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch .std hW (tuMv X Y m d) v ∧
    PieceOut (tL X.length hU) hW (ptv .std) v := by
  intro u
  obtain ⟨v, hsc, hcol⟩ := tu_exits_core X Y m d hm hW u
  exact ⟨v, hsc, unch_of_extCol .std hW _ (tu_hmv X Y m d) hcol,
    pieceOut_of_extCol _ .std hW _ (tI_xge_mem _ _) (tI_xle_mem _ _) (unch_pt _ _ _) hcol⟩

omit hm hW in
theorem tu_σcol {k' m' : ℕ} (hℓ : letterAt Vu k' = .σ m') (hext : ¬ ExtCol X Pu k') :
    k' = X.length + 1 ∧ m + 1 = m' := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := tu_letters X Y m d
  rw [tu_extCol] at hext
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀] at hℓ; cases hℓ
  · rw [hℓ₁] at hℓ; exact ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [hℓ₂] at hℓ; cases hℓ

omit hm hW in
theorem tu_kink : ∃ (k₀ m₀ : ℕ) (_hk₀ : k₀ < (Vu).length) (_hℓ₀ : letterAt Vu k₀ = .σ m₀), ¬ ExtCol X Pu k₀ ∧
    ∀ (k m : ℕ) (_hk : k < (Vu).length) (_hℓ : letterAt Vu k = .σ m), ¬ ExtCol X Pu k → k = k₀ :=
  ⟨X.length + 1, m + 1, by rw [tu_length]; omega, (tu_letters X Y m d).2.1, by rw [tu_extCol]; omega,
    fun k m' _ hℓ hext => (tu_σcol X Y m d hℓ hext).1⟩

theorem tu_σA_chain (hk : X.length + 1 < (Vu).length) (hℓ : letterAt Vu (X.length + 1) = .σ (m + 1)) :
    ∃ j, j < 9 ∧ (tuChain X Y m d hm hW).slot hW j = σSlotA hW hk hℓ := by
  obtain ⟨-, -, B2, -, -, -, -, -⟩ := tu_bits X Y m d hm hW
  have hv := σSlotA_val hW hk hℓ
  rw [B2] at hv
  cases d
  · simp only [Bool.not_false, ↓reduceIte] at hv
    exact tu_chain_of X Y m false hm hW 7 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
    exact tu_chain_of X Y m true hm hW 8 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)

theorem tu_hK : ∀ (k' m' : ℕ) (hk : k' < (Vu).length) (hℓ : letterAt Vu k' = .σ m'),
    ExtCol X Pu k' ↔ Unch .std hW (tuMv X Y m d) (σSlotA hW hk hℓ) ∧ Unch .std hW (tuMv X Y m d) (σSlotB hW hk hℓ) := by
  intro k' m' hk hℓ
  constructor
  · intro hext
    have hext' := (tu_extCol X m d k').1 hext
    exact ⟨unch_of_extCol .std hW _ (tu_hmv X Y m d) (by rw [(σSlotA_spec hW hk hℓ).1]; exact hext'),
      unch_of_extCol .std hW _ (tu_hmv X Y m d) (by rw [(σSlotB_spec hW hk hℓ).1]; exact hext')⟩
  · rintro ⟨hA, -⟩
    by_contra hext
    obtain ⟨rfl, rfl⟩ := tu_σcol X Y m d hℓ hext
    obtain ⟨-, -, B2, -, -, -, -, -⟩ := tu_bits X Y m d hm hW
    have hv := σSlotA_val hW hk hℓ
    rw [B2] at hv
    have h1 := hA.1
    cases d
    · simp only [Bool.not_false, ↓reduceIte] at hv
      have hv' : (σSlotA hW hk hℓ).1 = tw X.length m 7 := hv
      rw [tu_mv_tw X Y m false hm 7 (by norm_num) _ hv', hv', tu_pt_tw X Y m false hm 7 (by norm_num)] at h1
      have := congrArg Prod.snd h1
      simp only [mvw, pww] at this
      linarith
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
      have hv' : (σSlotA hW hk hℓ).1 = tw X.length m 8 := hv
      rw [tu_mv_tw X Y m true hm 8 (by norm_num) _ hv', hv', tu_pt_tw X Y m true hm 8 (by norm_num)] at h1
      have := congrArg Prod.snd h1
      simp only [mvw, pww] at this
      linarith

theorem tu_hKout : ∀ (k' m' : ℕ) (hk : k' < (Vu).length) (hℓ : letterAt Vu k' = .σ m'),
    ExtCol X Pu k' ↔ PieceOut (tL X.length hU) hW (ptv .std) (σSlotA hW hk hℓ) := by
  intro k' m' hk hℓ
  constructor
  · intro hext
    exact pieceOut_of_extCol _ .std hW _ (tI_xge_mem _ _) (tI_xle_mem _ _) (unch_pt _ _ _)
      (by rw [(σSlotA_spec hW hk hℓ).1]; exact (tu_extCol X m d k').1 hext)
  · intro hout
    by_contra hext
    obtain ⟨rfl, rfl⟩ := tu_σcol X Y m d hℓ hext
    obtain ⟨j, hj, hjs⟩ := tu_σA_chain X Y m d hm hW hk hℓ
    rw [← hjs] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (tu_chain_in X Y m d hm hW j hj).2

/-- the same-column chain pairs: the 18 ordered pairs of pieces sharing a column, both directions -/
theorem tu_pairs : ∀ j j', j < 9 → j' < 9 → (tuChain X Y m d hm hW).slot hW j ≠ (tuChain X Y m d hm hW).slot hW j' →
    colOf ((tuChain X Y m d hm hW).slot hW j) = colOf ((tuChain X Y m d hm hW).slot hW j') →
    MeetSpec .std hW (tuMv X Y m d) (ExtCol X Pu) ((tuChain X Y m d hm hW).slot hW j) ((tuChain X Y m d hm hW).slot hW j') := by
  intro j j' hj hj' hne hc
  have hjj : j ≠ j' := fun h => hne (by rw [h])
  clear hne
  rw [tu_col X Y m d hm hW j hj, tu_col X Y m d hm hW j' hj'] at hc
  have hn := tu_next_slot X Y m d hm hW
  have hmv := tu_mv_slot X Y m d hm hW
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [tcol] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact tU_NM05 _ _
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 6 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 6 (by norm_num), hmv (6 + 1) (by norm_num)]
      exact tU_NM06 _ _
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact tU_NM14 _ _
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 7 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 7 (by norm_num), hmv (7 + 1) (by norm_num)]
      exact tU_NM17 _ _
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact tU_OJ23 _ _
    · apply meetSpec_of_noMeet
      rw [hn 2 (by norm_num), hn 8 (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num),
        hmv 8 (by norm_num), hmv (8 + 1) (by norm_num)]
      exact tU_NM28 _ _
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact tU_OJ23 _ _
    · apply meetSpec_of_noMeet
      rw [hn 3 (by norm_num), hn 8 (by norm_num), hmv 3 (by norm_num), hmv (3 + 1) (by norm_num),
        hmv 8 (by norm_num), hmv (8 + 1) (by norm_num)]
      exact tU_NM38 _ _
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (tU_NM14 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 7 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 7 (by norm_num), hmv (7 + 1) (by norm_num)]
      exact tU_NM47 _ _
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (tU_NM05 _ _).symm
    · apply meetSpec_of_joint .std hW _ _ ((hn 5 (by norm_num)).symm)
      rw [hn (5 + 1) (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num), hmv (5 + 1 + 1) (by norm_num)]
      exact tU_OJ56 _ _
    · apply meetSpec_of_noMeet
      rw [hn 6 (by norm_num), hn 0 (by norm_num), hmv 6 (by norm_num), hmv (6 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (tU_NM06 _ _).symm
    · apply meetSpec_of_joint' .std hW _ _ ((hn 5 (by norm_num)).symm)
      rw [hn (5 + 1) (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num), hmv (5 + 1 + 1) (by norm_num)]
      exact tU_OJ56 _ _
    · apply meetSpec_of_noMeet
      rw [hn 7 (by norm_num), hn 1 (by norm_num), hmv 7 (by norm_num), hmv (7 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (tU_NM17 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 7 (by norm_num), hn 4 (by norm_num), hmv 7 (by norm_num), hmv (7 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (tU_NM47 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 8 (by norm_num), hn 2 (by norm_num), hmv 8 (by norm_num), hmv (8 + 1) (by norm_num),
        hmv 2 (by norm_num), hmv (2 + 1) (by norm_num)]
      exact (tU_NM28 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 8 (by norm_num), hn 3 (by norm_num), hmv 8 (by norm_num), hmv (8 + 1) (by norm_num),
        hmv 3 (by norm_num), hmv (3 + 1) (by norm_num)]
      exact (tU_NM38 _ _).symm
  · simp only [↓reduceIte] at hc hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [tcol] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact (tU_NM38 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 6 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 6 (by norm_num), hmv (6 + 1) (by norm_num)]
      exact (tU_NM28 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (tU_NM47 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 7 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 7 (by norm_num), hmv (7 + 1) (by norm_num)]
      exact (tU_NM17 _ _).symm.revl.revr
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (tU_OJ56 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 2 (by norm_num), hn 8 (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num),
        hmv 8 (by norm_num), hmv (8 + 1) (by norm_num)]
      exact (tU_NM06 _ _).symm.revl.revr
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (tU_OJ56 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 3 (by norm_num), hn 8 (by norm_num), hmv 3 (by norm_num), hmv (3 + 1) (by norm_num),
        hmv 8 (by norm_num), hmv (8 + 1) (by norm_num)]
      exact (tU_NM05 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (tU_NM47 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 7 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 7 (by norm_num), hmv (7 + 1) (by norm_num)]
      exact (tU_NM14 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (tU_NM38 _ _).revl.revr
    · apply meetSpec_of_joint .std hW _ _ ((hn 5 (by norm_num)).symm)
      rw [hn (5 + 1) (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num), hmv (5 + 1 + 1) (by norm_num)]
      exact (tU_OJ23 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 6 (by norm_num), hn 0 (by norm_num), hmv 6 (by norm_num), hmv (6 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (tU_NM28 _ _).revl.revr
    · apply meetSpec_of_joint' .std hW _ _ ((hn 5 (by norm_num)).symm)
      rw [hn (5 + 1) (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num), hmv (5 + 1 + 1) (by norm_num)]
      exact (tU_OJ23 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 7 (by norm_num), hn 1 (by norm_num), hmv 7 (by norm_num), hmv (7 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (tU_NM17 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 7 (by norm_num), hn 4 (by norm_num), hmv 7 (by norm_num), hmv (7 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (tU_NM14 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 8 (by norm_num), hn 2 (by norm_num), hmv 8 (by norm_num), hmv (8 + 1) (by norm_num),
        hmv 2 (by norm_num), hmv (2 + 1) (by norm_num)]
      exact (tU_NM06 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 8 (by norm_num), hn 3 (by norm_num), hmv 8 (by norm_num), hmv (8 + 1) (by norm_num),
        hmv 3 (by norm_num), hmv (3 + 1) (by norm_num)]
      exact (tU_NM05 _ _).revl.revr

theorem tu_genericData : GenericData .std hW (tuMv X Y m d) (ExtCol X Pu) :=
  genericData_of (tL X.length hU) .std hW (tuMv X Y m d) (ExtCol X Pu) (tuChain X Y m d hm hW)
    (mvU_injective _ _ _ m) (mvU_xcoord _ _ _ _) (tu_rest X Y m d hm hW)
    (fun j hj => (tu_chain_in X Y m d hm hW j hj).1) (tu_pairs X Y m d hm hW)
    (fun k m' hk hℓ hA hB => (tu_hK X Y m d hm hW k m' hk hℓ).2 ⟨hA, hB⟩)

theorem tu_riSpec : RISpec (tL X.length hU) .std hW (tuMv X Y m d) (ExtCol X Pu) (tuChain X Y m d hm hW) where
  disc := tL_isDisc _ _
  hK := tu_hK X Y m d hm hW
  hKout := tu_hKout X Y m d hm hW
  moved := tu_moved X Y m d hm
  chain := tu_chain_in X Y m d hm hW
  vert := tu_vert X Y m d hm hW
  rest := tu_rest X Y m d hm hW
  prevOut := tu_prevOut X Y m d hm hW
  stopOut := tu_stopOut X Y m d hm hW
  touch := tu_touch X Y m d hm hW
  exits := tu_exits X Y m d hm hW
  kink := tu_kink X Y m d

theorem tu_riData (hne : Vu ≠ []) :
    Nonempty (RIData (polygon (tL X.length hU))
      (mvDiagram .std hW hne (tuMv X Y m d) (ExtCol X Pu) (tu_genericData X Y m d hm hW)) (rlDiagram .std hW hne)) :=
  riData_of hne (tu_genericData X Y m d hm hW) (tu_riSpec X Y m d hm hW)

theorem tu_recordIso (hne : Vu ≠ []) (W' : OWord) (hW'eq : W'.letters = X ++ Y) :
    Nonempty (RecordIso (mvDiagram .std hW hne (tuMv X Y m d) (ExtCol X Pu) (tu_genericData X Y m d hm hW)).record
      (realize W').diagram.record) := by
  have hW' : (X ++ [] ++ Y).Closed := by have := W'.closed; rw [hW'eq] at this; simpa using this
  have hne' : X ++ Y ≠ [] := u1_typeI_target_ne_nil (W := Vu) (Or.inr ⟨hm, rfl⟩) hW
  refine ⟨vertexMovedRecordIso' X Pu Y [] (by simp) (tu_sameEffect X Y m d hm hW) hW hW' .std hne _ _ _ _
    (slotDiagramData_of .std hW hne (tuMv X Y m d) (ExtCol X Pu) (tu_genericData X Y m d hm hW) (tu_hK X Y m d hm hW))
    (tu_passage X Y m d hm hW hW') (tu_hexit X Y m d hm hW) ?_ ?_ W' (by simpa using hW'eq) (by simpa using hne')⟩
  · intro u; exact ⟨0, by show ExtCol X [] (colOf u); unfold ExtCol; simp; omega⟩
  · intro k hk1 hk2; simp at hk2; omega

omit hW in
/-- LEAF CASE (type I, right variant `l_m d σ_{m+1} r_m ↦ (nothing)`). -/
theorem typeI_right {W W' : OWord} (hWeq : W.letters = Vu) (hW'eq : W'.letters = X ++ Y) :
    ∃ D : Diagram, RI D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨Wl, hWl⟩ := W
  simp only at hWeq
  subst hWeq
  have hne : Vu ≠ [] := by simp
  rw [realize_eq_realizeAt ⟨_, hWl⟩ hne]
  exact ⟨mvDiagram .std hWl hne (tuMv X Y m d) (ExtCol X Pu) (tu_genericData X Y m d hm hWl),
    ⟨polygon (tL X.length hU), Or.inl (tu_riData X Y m d hm hWl hne)⟩, tu_recordIso X Y m d hm hWl hne W' hW'eq⟩

end TypeIRightSpec

/-! #### G. The leaf `typeI_move` -/

/-- ng:front-I: both curl words. -/
theorem typeI_move_proof {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨X, Y, m, d, ⟨hm, hWeq⟩ | ⟨hm, hWeq⟩, hW'eq⟩ := h
  · exact typeI_left X Y m d hm hWeq hW'eq
  · exact typeI_right X Y m d hm hWeq hW'eq


/-! #### H. The `RIIData` assembly (two chains, two block crossings) -/

section AssemblyII

variable (L : List HalfPlane) (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane)
  (K : ℕ → Prop)

/-- the occurrence of the over strand of a `σ` crossing of the realization, as a traversal point of the slot
diagram -/
theorem overVisit_eq {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    (x : (rlDiagram pl hW hne).Γ.Crossing) (hx : x.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk hℓ) :
    ∃ t : Set.Ico (0 : ℝ) 1, (rlDiagram pl hW hne).visitPt ((rlDiagram pl hW hne).overVisit x) =
      travMv pl hW hne (ptv pl) (σSlotA hW hk hℓ) t := by
  have data' := realizeAt_data' pl hW hne
  have hov : (rlDiagram pl hW hne).overStrand x = stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) :=
    data'.overStrand x k m hk hℓ hx
  refine ⟨⟨(rlDiagram pl hW hne).crossingParam x ((rlDiagram pl hW hne).over_mem x),
    ((rlDiagram pl hW hne).crossingParam_pos x _).le, (rlDiagram pl hW hne).crossingParam_lt_one x _⟩, ?_⟩
  apply pt_ext'
  · show (rlDiagram pl hW hne).overStrand x = strandMv pl hW hne (ptv pl) (σSlotA hW hk hℓ)
    exact hov
  · rfl

/-- the occurrence of the under strand -/
theorem underVisit_eq {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    (x : (rlDiagram pl hW hne).Γ.Crossing) (hx : x.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk hℓ) :
    ∃ t : Set.Ico (0 : ℝ) 1, (rlDiagram pl hW hne).visitPt ((rlDiagram pl hW hne).underVisit x) =
      travMv pl hW hne (ptv pl) (σSlotB hW hk hℓ) t := by
  have data' := realizeAt_data' pl hW hne
  have hov : (rlDiagram pl hW hne).overStrand x = stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) :=
    data'.overStrand x k m hk hℓ hx
  have hmemA : stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) ∈ x.val := by
    rw [hx]; exact mem_σpair_A pl hW hne _ hk hℓ
  have hun : (rlDiagram pl hW hne).underStrand x = stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotB hW hk hℓ) := by
    have h := slot_other pl hW hne (vertsOf pl hW hne (ptv pl)) (generic pl hW hne) (realizeAt pl hW hne).overStrand
      (realizeAt pl hW hne).overStrand_mem (fun _ => True) data' hmemA
    rw [idxEquiv_stStrand, σtwin_σSlotA] at h
    have hgen : ∀ (s : (rlDiagram pl hW hne).Γ.Strand) (hs : s ∈ x.val),
        s = stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) →
        (rlDiagram pl hW hne).Γ.other x hs = (rlDiagram pl hW hne).Γ.other x hmemA := by
      intro s hs e
      subst e
      rfl
    show (rlDiagram pl hW hne).Γ.other x ((rlDiagram pl hW hne).over_mem x) = _
    rw [hgen _ _ hov]
    exact (eq_stStrand_iff pl hW hne _ _ _).2 h
  refine ⟨⟨(rlDiagram pl hW hne).crossingParam x ((rlDiagram pl hW hne).under_mem x),
    ((rlDiagram pl hW hne).crossingParam_pos x _).le, (rlDiagram pl hW hne).crossingParam_lt_one x _⟩, ?_⟩
  apply pt_ext'
  · show (rlDiagram pl hW hne).underStrand x = strandMv pl hW hne (ptv pl) (σSlotB hW hk hℓ)
    exact hun
  · rfl

/-- a chain carrying the over strand of a block crossing carries its over occurrence -/
theorem overOn_of_chain {c : Chain W} (hc : c.IsChain L hW (ptv pl)) {k m : ℕ} (hk : k < W.length)
    (hℓ : letterAt W k = .σ m) (x : (rlDiagram pl hW hne).Γ.Crossing)
    (hx : x.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk hℓ) {j : ℕ} (hj : j < c.n)
    (hs : c.slot hW j = σSlotA hW hk hℓ) : (rlDiagram pl hW hne).OverOn (c.toArc pl hW hne (ptv pl)) x := by
  obtain ⟨t, ht⟩ := overVisit_eq pl hW hne hk hℓ x hx
  show (c.toArc pl hW hne (ptv pl)).Mem ((rlDiagram pl hW hne).visitPt ((rlDiagram pl hW hne).overVisit x))
  rw [ht, ← hs]
  exact hc.mem_of_slot pl hne hj t

theorem underOn_of_chain {c : Chain W} (hc : c.IsChain L hW (ptv pl)) {k m : ℕ} (hk : k < W.length)
    (hℓ : letterAt W k = .σ m) (x : (rlDiagram pl hW hne).Γ.Crossing)
    (hx : x.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk hℓ) {j : ℕ} (hj : j < c.n)
    (hs : c.slot hW j = σSlotB hW hk hℓ) : (rlDiagram pl hW hne).UnderOn (c.toArc pl hW hne (ptv pl)) x := by
  obtain ⟨t, ht⟩ := underVisit_eq pl hW hne hk hℓ x hx
  show (c.toArc pl hW hne (ptv pl)).Mem ((rlDiagram pl hW hne).visitPt ((rlDiagram pl hW hne).underVisit x))
  rw [ht, ← hs]
  exact hc.mem_of_slot pl hne hj t

/-- a chain piece as a membership statement -/
def OnChain (c : Chain W) (u : Slot W) : Prop := ∃ j, j < c.n ∧ c.slot hW j = u

/-- **The slot-level specification of a Reidemeister-II site** between the vertex-moved diagram (two disjoint arcs,
no crossing) and the realization (a bigon with two crossings) in the polygon `L`, along the chains `c₁`, `c₂`. -/
structure RIISpec (c₁ c₂ : Chain W) : Prop where
  disc : IsDisc (polygon L)
  hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
    K k ↔ Unch pl hW mv (σSlotA hW hk hℓ) ∧ Unch pl hW mv (σSlotB hW hk hℓ)
  hKout : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
    K k ↔ PieceOut L hW (ptv pl) (σSlotA hW hk hℓ)
  moved : ∀ u, mv u = pt pl W u.1 ∨ (mv u ∈ interior (polygon L) ∧ pt pl W u.1 ∈ interior (polygon L))
  chain₁ : ∀ j, j < c₁.n → PieceIn L hW mv (c₁.slot hW j) ∧ PieceIn L hW (ptv pl) (c₁.slot hW j)
  chain₂ : ∀ j, j < c₂.n → PieceIn L hW mv (c₂.slot hW j) ∧ PieceIn L hW (ptv pl) (c₂.slot hW j)
  vert₁ : ∀ j, 0 < j → j < c₁.n → mv (c₁.slot hW j) ∈ interior (polygon L) ∧ pt pl W (c₁.slot hW j).1 ∈ interior (polygon L)
  vert₂ : ∀ j, 0 < j → j < c₂.n → mv (c₂.slot hW j) ∈ interior (polygon L) ∧ pt pl W (c₂.slot hW j).1 ∈ interior (polygon L)
  rest : ∀ u, OnChain hW c₁ u ∨ OnChain hW c₂ u ∨ (Unch pl hW mv u ∧ PieceOut L hW (ptv pl) u)
  prevOut₁ : Unch pl hW mv (prev hW c₁.u₀) ∧ PieceOut L hW (ptv pl) (prev hW c₁.u₀)
  stopOut₁ : Unch pl hW mv (c₁.slot hW c₁.n) ∧ PieceOut L hW (ptv pl) (c₁.slot hW c₁.n)
  prevOut₂ : Unch pl hW mv (prev hW c₂.u₀) ∧ PieceOut L hW (ptv pl) (prev hW c₂.u₀)
  stopOut₂ : Unch pl hW mv (c₂.slot hW c₂.n) ∧ PieceOut L hW (ptv pl) (c₂.slot hW c₂.n)
  disj : ∀ j, j < c₁.n → ∀ j', j' < c₂.n → c₁.slot hW j ≠ c₂.slot hW j'
  touch : ∀ u, PieceOut L hW (ptv pl) u → pt pl W u.1 ∈ polygon L → u = c₁.slot hW c₁.n ∨ u = c₂.slot hW c₂.n
  exits : ∀ u : Slot W, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch pl hW mv v ∧ PieceOut L hW (ptv pl) v
  cross : ∃ (k₁ m₁ : ℕ) (hk₁ : k₁ < W.length) (hℓ₁ : letterAt W k₁ = .σ m₁) (k₂ m₂ : ℕ) (hk₂ : k₂ < W.length)
    (hℓ₂ : letterAt W k₂ = .σ m₂), k₁ ≠ k₂ ∧ ¬ K k₁ ∧ ¬ K k₂ ∧
    (∀ (k m : ℕ) (_hk : k < W.length) (_hℓ : letterAt W k = .σ m), ¬ K k → k = k₁ ∨ k = k₂) ∧
    ((OnChain hW c₁ (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW c₁ (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW c₂ (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW c₂ (σSlotB hW hk₂ hℓ₂)) ∨
     (OnChain hW c₂ (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW c₂ (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW c₁ (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW c₁ (σSlotB hW hk₂ hℓ₂)))

variable {L pl hW mv K}

theorem RIISpec.cl {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u := fun u => by
  rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨hu, ho⟩
  · exact Or.inl (S.chain₁ j hj).1
  · exact Or.inl (S.chain₂ j hj).1
  · exact Or.inr ((pieceOut_unch_iff L pl hW mv hu).2 ho)

theorem RIISpec.cl' {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : ∀ u, PieceIn L hW (ptv pl) u ∨ PieceOut L hW (ptv pl) u :=
  fun u => by
  rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨-, ho⟩
  · exact Or.inl (S.chain₁ j hj).2
  · exact Or.inl (S.chain₂ j hj).2
  · exact Or.inr ho

theorem RIISpec.out_iff {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) :
    ∀ u, PieceOut L hW mv u ↔ PieceOut L hW (ptv pl) u := fun u => by
  rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨hu, ho⟩
  · exact ⟨fun h => absurd (S.chain₁ j hj).1 (not_pieceIn_of_pieceOut L hW mv h),
      fun h => absurd (S.chain₁ j hj).2 (not_pieceIn_of_pieceOut L hW _ h)⟩
  · exact ⟨fun h => absurd (S.chain₂ j hj).1 (not_pieceIn_of_pieceOut L hW mv h),
      fun h => absurd (S.chain₂ j hj).2 (not_pieceIn_of_pieceOut L hW _ h)⟩
  · exact pieceOut_unch_iff L pl hW mv hu

theorem RIISpec.matchData {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) :
    MatchData L hW hW mv (ptv pl) (Equiv.refl _) where
  cl := S.cl
  cl' := S.cl'
  out_iff := S.out_iff
  pt_eq := fun u hu => by
    rcases S.moved u with h | ⟨h1, -⟩
    · exact h.symm
    · exact absurd h1 hu
  int_iff := fun u => by
    rcases S.moved u with h | ⟨h1, h2⟩
    · show mv u ∈ _ ↔ pt pl W u.1 ∈ _
      rw [h]
    · exact ⟨fun _ => h2, fun _ => h1⟩
  next_eq := fun _ _ => rfl

theorem RIISpec.isChain₁ {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : c₁.IsChain L hW mv where
  pieceIn := fun j hj => (S.chain₁ j hj).1
  vertex_interior := fun j h0 hj => (S.vert₁ j h0 hj).1
  out_prev := (pieceOut_unch_iff L pl hW mv S.prevOut₁.1).2 S.prevOut₁.2
  out_stop := (pieceOut_unch_iff L pl hW mv S.stopOut₁.1).2 S.stopOut₁.2

theorem RIISpec.isChain₂ {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : c₂.IsChain L hW mv where
  pieceIn := fun j hj => (S.chain₂ j hj).1
  vertex_interior := fun j h0 hj => (S.vert₂ j h0 hj).1
  out_prev := (pieceOut_unch_iff L pl hW mv S.prevOut₂.1).2 S.prevOut₂.2
  out_stop := (pieceOut_unch_iff L pl hW mv S.stopOut₂.1).2 S.stopOut₂.2

theorem RIISpec.isChain₁' {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : c₁.IsChain L hW (ptv pl) where
  pieceIn := fun j hj => (S.chain₁ j hj).2
  vertex_interior := fun j h0 hj => (S.vert₁ j h0 hj).2
  out_prev := S.prevOut₁.2
  out_stop := S.stopOut₁.2

theorem RIISpec.isChain₂' {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : c₂.IsChain L hW (ptv pl) where
  pieceIn := fun j hj => (S.chain₂ j hj).2
  vertex_interior := fun j h0 hj => (S.vert₂ j h0 hj).2
  out_prev := S.prevOut₂.2
  out_stop := S.stopOut₂.2

theorem RIISpec.u₀_ne {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : c₁.u₀ ≠ c₂.u₀ :=
  S.disj 0 c₁.hn 0 c₂.hn

/-- the entry and stop vertices of both chains are unmoved -/
theorem RIISpec.mv_u₀ {c : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) (hc : c.IsChain L hW mv) : mv c.u₀ = pt pl W c.u₀.1 := by
  rcases S.moved c.u₀ with h | ⟨h1, -⟩
  · exact h
  · exfalso
    have ho : SegOut L (mv (prev hW c.u₀)) (mv (next hW (prev hW c.u₀))) := hc.out_prev
    rw [next_prev] at ho
    exact ho.right_notMem_interior h1

theorem RIISpec.mv_stop {c : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) (hc : c.IsChain L hW mv) :
    mv (c.slot hW c.n) = pt pl W (c.slot hW c.n).1 := by
  rcases S.moved (c.slot hW c.n) with h | ⟨h1, -⟩
  · exact h
  · exfalso
    have ho : SegOut L (mv (c.slot hW c.n)) (mv (next hW (c.slot hW c.n))) := hc.out_stop
    exact ho.left_notMem_interior h1

theorem RIISpec.arcCover {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) :
    (shadowMv pl hW hne mv).ArcCover (polygon L) {c₁.toArc pl hW hne mv, c₂.toArc pl hW hne mv} := by
  have e : ({c₁.toArc pl hW hne mv, c₂.toArc pl hW hne mv} : Set (shadowMv pl hW hne mv).Arc) = arcsOf pl hW hne mv [c₁, c₂] := by
    ext a; simp [arcsOf, or_comm]
  rw [e]
  refine arcCover_of L pl hW hne mv [c₁, c₂] ?_ S.cl ?_ ?_ ?_
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact S.isChain₁
    · exact S.isChain₂
  · intro u hu
    rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨huu, ho⟩
    · exact ⟨c₁, by simp, j, hj, rfl⟩
    · exact ⟨c₂, by simp, j, hj, rfl⟩
    · exact absurd hu (not_pieceIn_of_pieceOut L hW mv ((pieceOut_unch_iff L pl hW mv huu).2 ho))
  · intro c hc c' hc' hne' j hj j' hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
    · exact absurd rfl hne'
    · exact S.disj j hj j' hj'
    · exact fun h => S.disj j' hj' j hj h.symm
    · exact absurd rfl hne'
  · intro u hu hmem
    have hni : mv u ∉ interior (polygon L) := SegOut.left_notMem_interior hu
    have hpt : mv u = pt pl W u.1 := by
      rcases S.moved u with h | ⟨h1, -⟩
      · exact h
      · exact absurd h1 hni
    have hu' : PieceOut L hW (ptv pl) u := (S.out_iff u).1 hu
    rcases S.touch u hu' (hpt ▸ hmem) with he | he
    · rw [he, chain_slot_pred]
      exact (S.chain₁ _ (by have := c₁.hn; omega)).1
    · rw [he, chain_slot_pred]
      exact (S.chain₂ _ (by have := c₂.hn; omega)).1

theorem RIISpec.arcCover' {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) :
    (shadowMv pl hW hne (ptv pl)).ArcCover (polygon L) {c₁.toArc pl hW hne (ptv pl), c₂.toArc pl hW hne (ptv pl)} := by
  have e : ({c₁.toArc pl hW hne (ptv pl), c₂.toArc pl hW hne (ptv pl)} : Set (shadowMv pl hW hne (ptv pl)).Arc) =
      arcsOf pl hW hne (ptv pl) [c₁, c₂] := by
    ext a; simp [arcsOf, or_comm]
  rw [e]
  refine arcCover_of L pl hW hne (ptv pl) [c₁, c₂] ?_ S.cl' ?_ ?_ ?_
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact S.isChain₁'
    · exact S.isChain₂'
  · intro u hu
    rcases S.rest u with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨-, ho⟩
    · exact ⟨c₁, by simp, j, hj, rfl⟩
    · exact ⟨c₂, by simp, j, hj, rfl⟩
    · exact absurd hu (not_pieceIn_of_pieceOut L hW _ ho)
  · intro c hc c' hc' hne' j hj j' hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
    · exact absurd rfl hne'
    · exact S.disj j hj j' hj'
    · exact fun h => S.disj j' hj' j hj h.symm
    · exact absurd rfl hne'
  · intro u hu hmem
    rcases S.touch u hu hmem with he | he
    · rw [he, chain_slot_pred]
      exact (S.chain₁ _ (by have := c₁.hn; omega)).2
    · rw [he, chain_slot_pred]
      exact (S.chain₂ _ (by have := c₂.hn; omega)).2

theorem RIISpec.exitsMv {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : ExitsMv L hW mv :=
  exitsMv_of_sameCycle L hW mv fun u => by
    obtain ⟨v, hsc, hunch, hout⟩ := S.exits u
    exact ⟨v, hsc, (pieceOut_unch_iff L pl hW mv hunch).2 hout⟩

theorem RIISpec.exitsMv' {c₁ c₂ : Chain W} (S : RIISpec L pl hW mv K c₁ c₂) : ExitsMv L hW (ptv pl) :=
  exitsMv_of_sameCycle L hW (ptv pl) fun u => by
    obtain ⟨v, hsc, -, hout⟩ := S.exits u
    exact ⟨v, hsc, hout⟩

/-- two `σ` pairs of different columns are different crossings -/
theorem σpair_ne_of_col {k₁ m₁ k₂ m₂ : ℕ} (hk₁ : k₁ < W.length) (hℓ₁ : letterAt W k₁ = .σ m₁)
    (hk₂ : k₂ < W.length) (hℓ₂ : letterAt W k₂ = .σ m₂) (hne' : k₁ ≠ k₂) (V : (shadowOf pl hW hne).Vertices) :
    σpair pl hW hne V hk₁ hℓ₁ ≠ σpair pl hW hne V hk₂ hℓ₂ := by
  intro h
  have hmem : stStrand pl hW hne V (σSlotA hW hk₁ hℓ₁) ∈ σpair pl hW hne V hk₂ hℓ₂ := by
    rw [← h]; exact mem_σpair_A pl hW hne _ hk₁ hℓ₁
  have hc := colOf_of_mem_σpair pl hW hne _ hk₂ hℓ₂ hmem
  rw [idxEquiv_stStrand, (σSlotA_spec hW hk₁ hℓ₁).1] at hc
  exact hne' hc

/-- **The Reidemeister-II site** from the specification. -/
theorem riiData_of {c₁ c₂ : Chain W} (d : GenericData pl hW mv K) (S : RIISpec L pl hW mv K c₁ c₂) :
    Nonempty (RIIData (polygon L) (mvDiagram pl hW hne mv K d) (rlDiagram pl hW hne)) := by
  classical
  have data := slotDiagramData_of pl hW hne mv K d S.hK
  have data' := realizeAt_data' pl hW hne
  have hσ : SigmaCorr L hW hW mv (Equiv.refl _) K (fun _ => True) :=
    fun k m hk hℓ _ _ => ⟨k, m, hk, hℓ, trivial, rfl, rfl⟩
  have hσ' : SigmaCorr L hW hW (ptv pl) (Equiv.refl _).symm (fun _ => True) K :=
    fun k m hk hℓ _ ho => ⟨k, m, hk, hℓ, (S.hKout k m hk hℓ).2 ho, rfl, rfl⟩
  obtain ⟨k₁, m₁, hk₁, hℓ₁, k₂, m₂, hk₂, hℓ₂, hk12, hK₁, hK₂, huniq, hsides⟩ := S.cross
  let x₁ : (rlDiagram pl hW hne).Γ.Crossing :=
    ⟨σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₁ hℓ₁, (data'.cross _).2 ⟨k₁, m₁, hk₁, hℓ₁, trivial, rfl⟩⟩
  let x₂ : (rlDiagram pl hW hne).Γ.Crossing :=
    ⟨σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₂ hℓ₂, (data'.cross _).2 ⟨k₂, m₂, hk₂, hℓ₂, trivial, rfl⟩⟩
  have hx₁ : x₁.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₁ hℓ₁ := rfl
  have hx₂ : x₂.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₂ hℓ₂ := rfl
  -- the inner crossings of the realization are exactly `x₁`, `x₂`
  have hinner : ∀ y : (rlDiagram pl hW hne).Γ.Crossing,
      (shadowMv pl hW hne (ptv pl)).crossingPoint y ∈ interior (polygon L) ↔ y = x₁ ∨ y = x₂ := by
    intro y
    obtain ⟨k, m, hk, hℓ, -, hy⟩ := (data'.cross y.val).1 y.2
    have hs : stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) ∈ y.val := by
      rw [hy]; exact mem_σpair_A pl hW hne _ hk hℓ
    have hiff := crossingPoint_notMem_interior_iff L pl hW hne (ptv pl) S.cl' (generic pl hW hne) y hs
    have e : slotMv pl hW hne (ptv pl) (stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ)) =
        σSlotA hW hk hℓ := idxEquiv_stStrand pl hW hne _ _
    rw [e] at hiff
    by_cases hKk : K k
    · have hno := hiff.2 ((S.hKout k m hk hℓ).1 hKk)
      refine ⟨fun h => absurd h hno, fun h => ?_⟩
      exfalso
      rcases h with h | h
      · have hval : y.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₁ hℓ₁ := by rw [h]
        rw [hy] at hval
        have hmem : stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) ∈
            σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₁ hℓ₁ := by rw [← hval]; exact mem_σpair_A pl hW hne _ hk hℓ
        have hc := colOf_of_mem_σpair pl hW hne _ hk₁ hℓ₁ hmem
        rw [idxEquiv_stStrand, (σSlotA_spec hW hk hℓ).1] at hc
        exact hK₁ (hc ▸ hKk)
      · have hval : y.val = σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₂ hℓ₂ := by rw [h]
        rw [hy] at hval
        have hmem : stStrand pl hW hne (vertsOf pl hW hne (ptv pl)) (σSlotA hW hk hℓ) ∈
            σpair pl hW hne (vertsOf pl hW hne (ptv pl)) hk₂ hℓ₂ := by rw [← hval]; exact mem_σpair_A pl hW hne _ hk hℓ
        have hc := colOf_of_mem_σpair pl hW hne _ hk₂ hℓ₂ hmem
        rw [idxEquiv_stStrand, (σSlotA_spec hW hk hℓ).1] at hc
        exact hK₂ (hc ▸ hKk)
    · have hin : (shadowMv pl hW hne (ptv pl)).crossingPoint y ∈ interior (polygon L) := by
        by_contra h
        exact hKk ((S.hKout k m hk hℓ).2 (hiff.1 h))
      refine ⟨fun _ => ?_, fun _ => hin⟩
      rcases huniq k m hk hℓ hKk with rfl | rfl
      · have hm : m = m₁ := by
          have := hℓ.symm.trans hℓ₁
          cases this; rfl
        subst hm
        exact Or.inl (Subtype.ext hy)
      · have hm : m = m₂ := by
          have := hℓ.symm.trans hℓ₂
          cases this; rfl
        subst hm
        exact Or.inr (Subtype.ext hy)
  refine ⟨{ frame := ⟨S.disc, clean_mv L pl hW hne mv d.inj S.cl S.exitsMv _ _ _,
              clean_mv L pl hW hne (ptv pl) (fun u v h => pt_inj pl W h) S.cl' S.exitsMv' _ _ _⟩
            out := S.matchData.moveMatch pl hne hne (generic_of pl hW hne mv K d) (ovMv pl hW hne mv)
              (ovMv_mem pl hW hne mv) K data (generic pl hW hne) (realizeAt pl hW hne).overStrand
              (realizeAt pl hW hne).overStrand_mem (fun _ => True) data' hσ hσ' (Equiv.refl _) (fun _ _ => rfl)
            a := c₁.toArc pl hW hne mv
            b := c₂.toArc pl hW hne mv
            a' := c₁.toArc pl hW hne (ptv pl)
            b' := c₂.toArc pl hW hne (ptv pl)
            ab := Chain.toArc_ne pl hW hne mv S.u₀_ne
            ab' := Chain.toArc_ne pl hW hne (ptv pl) S.u₀_ne
            cover := S.arcCover hne
            cover' := S.arcCover' hne
            a_start := ?_
            a_stop := ?_
            b_start := ?_
            b_stop := ?_
            no_inner := ?_
            x₁ := x₁
            x₂ := x₂
            ne := fun h => σpair_ne_of_col hne hk₁ hℓ₁ hk₂ hℓ₂ hk12 _ (congrArg Subtype.val h)
            inner_iff' := hinner
            sep₁ := ?_
            sep₂ := ?_
            same_over := ?_ }⟩
  · show (shadowMv pl hW hne (ptv pl)).eval (c₁.toArc pl hW hne (ptv pl)).startPt =
      (shadowMv pl hW hne mv).eval (c₁.toArc pl hW hne mv).startPt
    rw [Chain.eval_startPt, Chain.eval_startPt, S.mv_u₀ S.isChain₁]
  · show (shadowMv pl hW hne (ptv pl)).eval (c₁.toArc pl hW hne (ptv pl)).stopPt =
      (shadowMv pl hW hne mv).eval (c₁.toArc pl hW hne mv).stopPt
    rw [Chain.eval_stopPt, Chain.eval_stopPt, S.mv_stop S.isChain₁]
  · show (shadowMv pl hW hne (ptv pl)).eval (c₂.toArc pl hW hne (ptv pl)).startPt =
      (shadowMv pl hW hne mv).eval (c₂.toArc pl hW hne mv).startPt
    rw [Chain.eval_startPt, Chain.eval_startPt, S.mv_u₀ S.isChain₂]
  · show (shadowMv pl hW hne (ptv pl)).eval (c₂.toArc pl hW hne (ptv pl)).stopPt =
      (shadowMv pl hW hne mv).eval (c₂.toArc pl hW hne mv).stopPt
    rw [Chain.eval_stopPt, Chain.eval_stopPt, S.mv_stop S.isChain₂]
  · intro x
    obtain ⟨k, m, hk, hℓ, hKk, hx⟩ := (data.cross x.val).1 x.2
    have hs : stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ) ∈ x.val := by
      rw [hx]; exact mem_σpair_A pl hW hne _ hk hℓ
    show (shadowMv pl hW hne mv).crossingPoint x ∉ interior (polygon L)
    rw [crossingPoint_notMem_interior_iff L pl hW hne mv S.cl (generic_of pl hW hne mv K d) x hs]
    show PieceOut L hW mv (idxEquiv hW (stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ)))
    rw [idxEquiv_stStrand]
    exact (pieceOut_unch_iff L pl hW mv ((S.hK k m hk hℓ).1 hKk).1).2 ((S.hKout k m hk hℓ).1 hKk)
  · -- sep₁
    rcases hsides with ⟨⟨j, hj, hs⟩, -, ⟨j', hj', hs'⟩, -⟩ | ⟨⟨j, hj, hs⟩, -, ⟨j', hj', hs'⟩, -⟩
    · exact Or.inl ⟨overOn_of_chain L pl hW hne S.isChain₁' hk₁ hℓ₁ x₁ hx₁ hj hs,
        underOn_of_chain L pl hW hne S.isChain₂' hk₁ hℓ₁ x₁ hx₁ hj' hs'⟩
    · exact Or.inr ⟨overOn_of_chain L pl hW hne S.isChain₂' hk₁ hℓ₁ x₁ hx₁ hj hs,
        underOn_of_chain L pl hW hne S.isChain₁' hk₁ hℓ₁ x₁ hx₁ hj' hs'⟩
  · -- sep₂
    rcases hsides with ⟨-, ⟨j, hj, hs⟩, -, ⟨j', hj', hs'⟩⟩ | ⟨-, ⟨j, hj, hs⟩, -, ⟨j', hj', hs'⟩⟩
    · exact Or.inl ⟨overOn_of_chain L pl hW hne S.isChain₁' hk₂ hℓ₂ x₂ hx₂ hj hs,
        underOn_of_chain L pl hW hne S.isChain₂' hk₂ hℓ₂ x₂ hx₂ hj' hs'⟩
    · exact Or.inr ⟨overOn_of_chain L pl hW hne S.isChain₂' hk₂ hℓ₂ x₂ hx₂ hj hs,
        underOn_of_chain L pl hW hne S.isChain₁' hk₂ hℓ₂ x₂ hx₂ hj' hs'⟩
  · -- same_over
    rcases hsides with ⟨⟨j, hj, hs⟩, ⟨j', hj', hs'⟩, -, -⟩ | ⟨⟨j, hj, hs⟩, ⟨j', hj', hs'⟩, -, -⟩
    · exact Or.inl ⟨overOn_of_chain L pl hW hne S.isChain₁' hk₁ hℓ₁ x₁ hx₁ hj hs,
        overOn_of_chain L pl hW hne S.isChain₁' hk₂ hℓ₂ x₂ hx₂ hj' hs'⟩
    · exact Or.inr ⟨overOn_of_chain L pl hW hne S.isChain₂' hk₁ hℓ₁ x₁ hx₁ hj hs,
        overOn_of_chain L pl hW hne S.isChain₂' hk₂ hℓ₂ x₂ hx₂ hj' hs'⟩

end AssemblyII

/-! #### H2. Genericity from an active set; the type-II disc families -/

section GenericAct

variable (L : List HalfPlane) (pl : Placement) {W : Word} (hW : W.Closed) (mv : Slot W → Plane) (K : ℕ → Prop)

/-- **Genericity from an active set of pieces**: non-active pieces are unchanged and outside, active pieces are
inside, same-column active pairs satisfy the meeting specification, and a `σ` column with both crossing pieces
unchanged is in `K`. -/
theorem genericData_of' (Act : Slot W → Prop) (hinj : Function.Injective mv)
    (hx : ∀ u, (mv u).1 = (pt pl W u.1).1)
    (hrest : ∀ u, Act u ∨ (Unch pl hW mv u ∧ PieceOut L hW (ptv pl) u))
    (hact : ∀ u, Act u → PieceIn L hW mv u)
    (hpairs : ∀ u v, Act u → Act v → u ≠ v → colOf u = colOf v → MeetSpec pl hW mv K u v)
    (hKu : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      Unch pl hW mv (σSlotA hW hk hℓ) → Unch pl hW mv (σSlotB hW hk hℓ) → K k) :
    GenericData pl hW mv K where
  inj := hinj
  xcoord := hx
  meet := by
    intro u v huv hc
    rcases hrest u with hu | ⟨huu, huo⟩
    · rcases hrest v with hv | ⟨hvu, hvo⟩
      · exact hpairs u v hu hv huv hc
      · exact meetSpec_of_in_out L pl hW mv K hinj (hact u hu) ((pieceOut_unch_iff L pl hW mv hvu).2 hvo)
    · rcases hrest v with hv | ⟨hvu, hvo⟩
      · exact (meetSpec_of_in_out L pl hW mv K hinj (hact v hv) ((pieceOut_unch_iff L pl hW mv huu).2 huo)).symm
      · exact meetSpec_of_unch pl hW mv K huu hvu hKu

end GenericAct

section TIIDisc

/-- the type-II disc of the left-cusp variants: `[k, k+3] × [h−5/2, h+3/4]` cut by the left slant
`y ≥ h − 3/4 − 2(x − k)` -/
def tIIL (k : ℕ) (h : ℝ) : List HalfPlane :=
  [HalfPlane.xge (k : ℝ), HalfPlane.xle ((k : ℝ) + 3), HalfPlane.yle (h + 3 / 4), HalfPlane.yge (h - 5 / 2),
    HalfPlane.above (h - 3 / 4 + 2 * k) (-2)]

/-- the type-II disc of the right-cusp variants: cut by the right slant `y ≥ h − 3/4 + 2(x − (k+3))` -/
def tIIR (k : ℕ) (h : ℝ) : List HalfPlane :=
  [HalfPlane.xge (k : ℝ), HalfPlane.xle ((k : ℝ) + 3), HalfPlane.yle (h + 3 / 4), HalfPlane.yge (h - 5 / 2),
    HalfPlane.above (h - 3 / 4 - 2 * ((k : ℝ) + 3)) 2]

macro "tIIL_mem" : tactic => `(tactic| (
  simp only [tIIL, mem_polygon_iff, mem_interior_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, or_false, HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle,
    HalfPlane.b_yle, HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith))

macro "tIIR_mem" : tactic => `(tactic| (
  simp only [tIIR, mem_polygon_iff, mem_interior_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, or_false, HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle,
    HalfPlane.b_yle, HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith))

variable (k : ℕ) (h : ℝ)

/-! the left family -/

theorem tIIL_int_cut1 (r : ℝ) (hr1 : -5 / 2 < r) (hr2 : r < 3 / 4) :
    (((k + 1 : ℕ) : ℝ), h + r) ∈ interior (polygon (tIIL k h)) := by push_cast; tIIL_mem
theorem tIIL_int_cut2 (r : ℝ) (hr1 : -5 / 2 < r) (hr2 : r < 3 / 4) :
    (((k + 2 : ℕ) : ℝ), h + r) ∈ interior (polygon (tIIL k h)) := by push_cast; tIIL_mem
theorem tIIL_int_cuspL (r : ℝ) (hr1 : -7 / 4 < r) (hr2 : r < 3 / 4) :
    ((k : ℝ) + 1 / 2, h + r) ∈ interior (polygon (tIIL k h)) := by tIIL_mem
theorem tIIL_mem_left (r : ℝ) (hr1 : -3 / 4 ≤ r) (hr2 : r ≤ 3 / 4) : ((k : ℝ), h + r) ∈ polygon (tIIL k h) := by tIIL_mem
theorem tIIL_mem_right (r : ℝ) (hr1 : -5 / 2 ≤ r) (hr2 : r ≤ 3 / 4) :
    (((k + 3 : ℕ) : ℝ), h + r) ∈ polygon (tIIL k h) := by push_cast; tIIL_mem
theorem tIIL_xge_mem : HalfPlane.xge (Placement.std.x k) ∈ tIIL k h := by simp [tIIL]
theorem tIIL_xle_mem : HalfPlane.xle (Placement.std.x (k + 3)) ∈ tIIL k h := by
  have e : Placement.std.x (k + 3) = (k : ℝ) + 3 := by rw [Placement.std_x]; push_cast; ring
  rw [e]; simp [tIIL]
theorem tIIL_out_above {y : ℝ} (hy : h + 1 ≤ y) (x₀ x₁ : ℝ) : SegOut (tIIL k h) (x₀, y) (x₁, y) := by
  refine segOut_of_lt (HalfPlane.yle (h + 3 / 4)) (by simp [tIIL]) ?_ ?_ <;>
    simp only [HalfPlane.f_yle, HalfPlane.b_yle] <;> linarith
theorem tIIL_out_below {y : ℝ} (hy : y ≤ h - 3) (x₀ x₁ : ℝ) : SegOut (tIIL k h) (x₀, y) (x₁, y) := by
  refine segOut_of_lt (HalfPlane.yge (h - 5 / 2)) (by simp [tIIL]) ?_ ?_ <;>
    simp only [HalfPlane.f_yge, HalfPlane.b_yge] <;> linarith
theorem tIIL_out_slant {p : ℕ} (hp : -(p : ℝ) ≤ h - 1) :
    SegOut (tIIL k h) ((k : ℝ), -(p : ℝ)) (((k + 1 : ℕ) : ℝ), -((p + 2 : ℕ) : ℝ)) := by
  refine segOut_of_lt (HalfPlane.above (h - 3 / 4 + 2 * k) (-2)) (by simp [tIIL]) ?_ ?_ <;>
    simp only [HalfPlane.f_above, HalfPlane.b_above] <;> push_cast <;> linarith
theorem tIIL_out_slant' {q : ℕ} (hq : 2 ≤ q) (hy : -((q - 2 : ℕ) : ℝ) ≤ h - 1) :
    SegOut (tIIL k h) (((k + 1 : ℕ) : ℝ), -(q : ℝ)) ((k : ℝ), -((q - 2 : ℕ) : ℝ)) := by
  have := (tIIL_out_slant k h (p := q - 2) hy).symm
  rwa [show q - 2 + 2 = q by omega] at this
theorem tIIL_mem_bounds {x y : ℝ} (hmem : (x, y) ∈ polygon (tIIL k h)) :
    (k : ℝ) ≤ x ∧ x ≤ k + 3 ∧ h - 5 / 2 ≤ y ∧ y ≤ h + 3 / 4 ∧ h - 3 / 4 + 2 * k - 2 * x ≤ y := by
  simp only [tIIL, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at hmem
  obtain ⟨h1, h2, h3, h4, h5⟩ := hmem
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
theorem tIIL_isDisc : IsDisc (polygon (tIIL k h)) := by
  refine isDisc_polygon (tIIL k h) (a := k) (b := (k : ℝ) + 3) (c := h - 5 / 2) (d := h + 3 / 4) ?_
    ⟨((k : ℝ) + 3 / 2, h - 1 / 2), ?_⟩
  · intro q hq
    obtain ⟨h1, h2, h3, h4, -⟩ := tIIL_mem_bounds k h (x := q.1) (y := q.2) hq
    exact ⟨h1, h2, h3, h4⟩
  · simp only [tIIL, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
      HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
      HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! the right family -/

theorem tIIR_int_cut1 (r : ℝ) (hr1 : -5 / 2 < r) (hr2 : r < 3 / 4) :
    (((k + 1 : ℕ) : ℝ), h + r) ∈ interior (polygon (tIIR k h)) := by push_cast; tIIR_mem
theorem tIIR_int_cut2 (r : ℝ) (hr1 : -5 / 2 < r) (hr2 : r < 3 / 4) :
    (((k + 2 : ℕ) : ℝ), h + r) ∈ interior (polygon (tIIR k h)) := by push_cast; tIIR_mem
theorem tIIR_int_cuspR (r : ℝ) (hr1 : -7 / 4 < r) (hr2 : r < 3 / 4) :
    (((k + 2 : ℕ) : ℝ) + 1 / 2, h + r) ∈ interior (polygon (tIIR k h)) := by push_cast; tIIR_mem
theorem tIIR_mem_left (r : ℝ) (hr1 : -5 / 2 ≤ r) (hr2 : r ≤ 3 / 4) : ((k : ℝ), h + r) ∈ polygon (tIIR k h) := by tIIR_mem
theorem tIIR_mem_right (r : ℝ) (hr1 : -3 / 4 ≤ r) (hr2 : r ≤ 3 / 4) :
    (((k + 3 : ℕ) : ℝ), h + r) ∈ polygon (tIIR k h) := by push_cast; tIIR_mem
theorem tIIR_xge_mem : HalfPlane.xge (Placement.std.x k) ∈ tIIR k h := by simp [tIIR]
theorem tIIR_xle_mem : HalfPlane.xle (Placement.std.x (k + 3)) ∈ tIIR k h := by
  have e : Placement.std.x (k + 3) = (k : ℝ) + 3 := by rw [Placement.std_x]; push_cast; ring
  rw [e]; simp [tIIR]
theorem tIIR_out_above {y : ℝ} (hy : h + 1 ≤ y) (x₀ x₁ : ℝ) : SegOut (tIIR k h) (x₀, y) (x₁, y) := by
  refine segOut_of_lt (HalfPlane.yle (h + 3 / 4)) (by simp [tIIR]) ?_ ?_ <;>
    simp only [HalfPlane.f_yle, HalfPlane.b_yle] <;> linarith
theorem tIIR_out_below {y : ℝ} (hy : y ≤ h - 3) (x₀ x₁ : ℝ) : SegOut (tIIR k h) (x₀, y) (x₁, y) := by
  refine segOut_of_lt (HalfPlane.yge (h - 5 / 2)) (by simp [tIIR]) ?_ ?_ <;>
    simp only [HalfPlane.f_yge, HalfPlane.b_yge] <;> linarith
/-- the pulled-up spectator of the right-cusp column: from `(k+2, −p)` to `(k+3, −(p−2))` -/
theorem tIIR_out_slant {p : ℕ} (hp : 2 ≤ p) (hy : -((p - 2 : ℕ) : ℝ) ≤ h - 1) :
    SegOut (tIIR k h) (((k + 2 : ℕ) : ℝ), -(p : ℝ)) (((k + 3 : ℕ) : ℝ), -((p - 2 : ℕ) : ℝ)) := by
  have hy' : -((p : ℝ) - 2) ≤ h - 1 := by rwa [Nat.cast_sub hp, Nat.cast_ofNat] at hy
  refine segOut_of_lt (HalfPlane.above (h - 3 / 4 - 2 * ((k : ℝ) + 3)) 2) (by simp [tIIR]) ?_ ?_ <;>
    simp only [HalfPlane.f_above, HalfPlane.b_above] <;> push_cast [Nat.cast_sub hp] <;> linarith
theorem tIIR_out_slant' {q : ℕ} (hq : -(q : ℝ) ≤ h - 1) :
    SegOut (tIIR k h) (((k + 3 : ℕ) : ℝ), -(q : ℝ)) (((k + 2 : ℕ) : ℝ), -((q + 2 : ℕ) : ℝ)) := by
  have := (tIIR_out_slant k h (p := q + 2) (by omega) (by rwa [show q + 2 - 2 = q by omega])).symm
  rwa [show q + 2 - 2 = q by omega] at this
theorem tIIR_mem_bounds {x y : ℝ} (hmem : (x, y) ∈ polygon (tIIR k h)) :
    (k : ℝ) ≤ x ∧ x ≤ k + 3 ∧ h - 5 / 2 ≤ y ∧ y ≤ h + 3 / 4 ∧ h - 3 / 4 - 2 * ((k : ℝ) + 3) + 2 * x ≤ y := by
  simp only [tIIR, mem_polygon_iff, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
    HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
    HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above] at hmem
  obtain ⟨h1, h2, h3, h4, h5⟩ := hmem
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
theorem tIIR_isDisc : IsDisc (polygon (tIIR k h)) := by
  refine isDisc_polygon (tIIR k h) (a := k) (b := (k : ℝ) + 3) (c := h - 5 / 2) (d := h + 3 / 4) ?_
    ⟨((k : ℝ) + 3 / 2, h - 1 / 2), ?_⟩
  · intro q hq
    obtain ⟨h1, h2, h3, h4, -⟩ := tIIR_mem_bounds k h (x := q.1) (y := q.2) hq
    exact ⟨h1, h2, h3, h4⟩
  · simp only [tIIR, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false,
      HalfPlane.f_xge, HalfPlane.b_xge, HalfPlane.f_xle, HalfPlane.b_xle, HalfPlane.f_yle, HalfPlane.b_yle,
      HalfPlane.f_yge, HalfPlane.b_yge, HalfPlane.f_above, HalfPlane.b_above]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end TIIDisc

/-! #### I. The front type-II move, variant (a) `l_{m−1} d σ_m σ_{m−1} ↦ l_m d` (ng:front-II, sm-3:1977-1984) -/

/-- the four vertices of the through-strand (rightward order) -/
def tvT (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k, m - 1)
  | 1 => (k + 1, m + 1)
  | 2 => (k + 2, m)
  | _ => (k + 3, m - 1)

/-- the seven vertices of the cusp arc (order of the leftward lower arm, `d = true`) -/
def tvC (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k + 3, m + 1)
  | 1 => (k + 2, m + 1)
  | 2 => (k + 1, m)
  | 3 => (k, 0)
  | 4 => (k + 1, m - 1)
  | 5 => (k + 2, m - 1)
  | _ => (k + 3, m)

def tvTd (k m : ℕ) (t : Bool) (j : ℕ) : ℕ × ℕ := if t then tvT k m j else tvT k m (3 - j)
def tvCd (k m : ℕ) (d : Bool) (j : ℕ) : ℕ × ℕ := if d then tvC k m j else tvC k m (6 - j)

/-- the columns of the through-strand pieces and of the cusp pieces -/
def colT (k : ℕ) : ℕ → ℕ
  | 0 => k
  | 1 => k + 1
  | _ => k + 2
def colC (k : ℕ) : ℕ → ℕ
  | 0 => k + 2
  | 1 => k + 1
  | 2 => k
  | 3 => k
  | 4 => k + 1
  | _ => k + 2

section TypeIIaWord

open U3

variable (X Y : Word) (m : ℕ) (d t : Bool) (hm : 2 ≤ m)
  (hW : (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y) X.length (m - 1) = t)

local notation "Va" => X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y
local notation "Pa" => [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)]
local notation "Va'" => X ++ [Letter.l m d] ++ Y
local notation "Pa'" => [Letter.l m d]

theorem a_letters : letterAt Va X.length = .l (m - 1) d ∧ letterAt Va (X.length + 1) = .σ m ∧
    letterAt Va (X.length + 2) = .σ (m - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have := letterAt_block X Pa Y (i := 0) (by simp); simpa using this
  · have := letterAt_block X Pa Y (i := 1) (by simp); simpa using this
  · have := letterAt_block X Pa Y (i := 2) (by simp); simpa using this

theorem a_length : (Va).length = X.length + 3 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem a'_letters : letterAt Va' X.length = .l m d := by
  have := letterAt_block X Pa' Y (i := 0) (by simp); simpa using this

theorem a'_length : (Va').length = X.length + 1 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem a_extCol (k : ℕ) : ExtCol X Pa k ↔ k + 1 ≤ X.length ∨ X.length + 3 ≤ k := by
  unfold ExtCol; simp

theorem a'_extCol (k : ℕ) : ExtCol X Pa' k ↔ k + 1 ≤ X.length ∨ X.length + 1 ≤ k := by
  unfold ExtCol; simp

theorem a_shift : shiftIdx X Pa Pa' (X.length + 3) = X.length + 1 := by
  unfold shiftIdx; simp

theorem a_cut_start : cut Va' X.length = cut Va X.length := by
  unfold cut
  rw [List.append_assoc, List.take_left' rfl, List.append_assoc, List.take_left' rfl]

theorem a_bit_start (p : ℕ) : bit Va' X.length p = bit Va X.length p := by
  rw [bit_eq, bit_eq, a_cut_start]

include hW

include hm in
theorem a_sameEffect : SameEffect X Pa Pa' :=
  sameEffect_of_replace X Pa Y Pa' hW (fun c c' h => run_typeII_l_left hm h)

include hm in
theorem a_cut_end : cut Va' (X.length + 1) = cut Va (X.length + 3) := by
  have hE := a_sameEffect X Y m d hm hW
  unfold SameEffect at hE
  unfold cut
  rw [List.take_left' (by simp), List.take_left' (by simp), hE]

include hm in
theorem a_bit_end (p : ℕ) : bit Va' (X.length + 1) p = bit Va (X.length + 3) p := by
  rw [bit_eq, bit_eq, a_cut_end X Y m d hm hW]

theorem a_cutlen : m + 1 ≤ (cut Va (X.length + 1)).length ∧ (cut Va (X.length + 2)).length = (cut Va (X.length + 1)).length ∧
    (cut Va (X.length + 3)).length = (cut Va (X.length + 2)).length ∧ (cut Va (X.length + 1)).length = (cut Va X.length).length + 2 := by
  have hk₀ : X.length < (Va).length := by rw [a_length]; omega
  have hk₁ : X.length + 1 < (Va).length := by rw [a_length]; omega
  have hk₂ : X.length + 2 < (Va).length := by rw [a_length]; omega
  obtain ⟨-, h2, h3, -, -⟩ := σ_facts hW hk₁ (a_letters X Y m d).2.1
  obtain ⟨-, -, h3', -, -⟩ := σ_facts hW hk₂ (a_letters X Y m d).2.2
  obtain ⟨D⟩ := decomp hW X.length hk₀
  have h1 := D.length_add
  have har : (letterAt Va X.length).arity = 0 := by rw [(a_letters X Y m d).1]; rfl
  have hco : (letterAt Va X.length).coarity = 2 := by rw [(a_letters X Y m d).1]; rfl
  exact ⟨h2, h3, h3', by omega⟩

include hm ht in
/-- the bits: the arms carry `d`, `!d`; the through-strand carries `t` -/
theorem a_bits :
    bit Va (X.length + 1) (m - 1) = d ∧ bit Va (X.length + 1) m = !d ∧ bit Va (X.length + 1) (m + 1) = t ∧
    bit Va (X.length + 2) (m - 1) = d ∧ bit Va (X.length + 2) m = t ∧ bit Va (X.length + 2) (m + 1) = !d ∧
    bit Va (X.length + 3) (m - 1) = t ∧ bit Va (X.length + 3) m = d ∧ bit Va (X.length + 3) (m + 1) = !d := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
  have hk₀ : X.length < (Va).length := by rw [a_length]; omega
  have hk₁ : X.length + 1 < (Va).length := by rw [a_length]; omega
  have hk₂ : X.length + 2 < (Va).length := by rw [a_length]; omega
  obtain ⟨-, B1, B2⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, -, -, h4, h5⟩ := σ_facts hW hk₁ hℓ₁
  obtain ⟨-, -, -, h4', h5'⟩ := σ_facts hW hk₂ hℓ₂
  rw [show m - 1 + 1 = m by omega] at h4' h5' B2
  have B3 : bit Va (X.length + 1) (m + 1) = t := by
    have := bit_succ_of_ge hW hk₀ (p := m - 1) (by rw [hℓ₀]; simp only [idx, arity]; omega)
    rw [hℓ₀] at this
    simp only [coarity, arity] at this
    rw [show m - 1 + 2 - 0 = m + 1 by omega] at this
    rw [this, ht]
  have B4 : bit Va (X.length + 2) (m - 1) = d := by
    rw [bit_succ_of_lt hW hk₁ (by omega) (by rw [hℓ₁]; simp only [idx]; omega), B1]
  have B5 : bit Va (X.length + 2) m = t := by rw [h5, B3]
  have B6 : bit Va (X.length + 2) (m + 1) = !d := by rw [h4, B2]
  have B7 : bit Va (X.length + 3) (m - 1) = t := by rw [h5', B5]
  have B8 : bit Va (X.length + 3) m = d := by rw [h4', B4]
  have B9 : bit Va (X.length + 3) (m + 1) = !d := by
    have := bit_succ_of_ge hW hk₂ (p := m + 1) (by rw [hℓ₂]; simp only [idx, arity]; omega)
    rw [hℓ₂] at this
    simp only [coarity, arity] at this
    rw [show m + 1 + 2 - 2 = m + 1 by omega] at this
    rw [this, B6]
  exact ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩

/-! the successor table (columns `|X|`: `l_{m−1}`, `|X|+1`: `σ_m`, `|X|+2`: `σ_{m−1}`) -/

theorem a_A1 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Va X.length p = true)
    (hpm : p < m - 1) : (next hW s).1 = (X.length + 1, p) ∧ bit Va (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(a_letters X Y m d).1]; exact hpm)

theorem a_A2 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Va X.length p = true)
    (hpm : m - 1 ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Va (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(a_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(a_letters X Y m d).1] at this

theorem a_A3 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Va (X.length + 1) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Va (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(a_letters X Y m d).2.1]; exact hpm)

theorem a_A4 {s : Slot Va} (hs : s.1 = (X.length + 1, m)) (hb : bit Va (X.length + 1) m = true) :
    (next hW s).1 = (X.length + 2, m + 1) :=
  next_σ_right_idx hW (a_letters X Y m d).2.1 hs hb

theorem a_A5 {s : Slot Va} (hs : s.1 = (X.length + 1, m + 1)) (hb : bit Va (X.length + 1) (m + 1) = true) :
    (next hW s).1 = (X.length + 2, m) :=
  next_σ_right_succ hW (a_letters X Y m d).2.1 hs hb

theorem a_A6 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Va (X.length + 1) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Va (X.length + 2) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(a_letters X Y m d).2.1]; simpa [idx, arity] using hpm)
  rw [(a_letters X Y m d).2.1] at this
  simpa [coarity, arity] using this

theorem a_A7 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Va (X.length + 2) p = true) (hpm : p < m - 1) :
    (next hW s).1 = (X.length + 3, p) ∧ bit Va (X.length + 3) p = true :=
  next_right_lt hW hs hp hb (by rw [(a_letters X Y m d).2.2]; exact hpm)

include hm in
theorem a_A8 {s : Slot Va} (hs : s.1 = (X.length + 2, m - 1)) (hb : bit Va (X.length + 2) (m - 1) = true) :
    (next hW s).1 = (X.length + 3, m) := by
  have := next_σ_right_idx hW (a_letters X Y m d).2.2 hs hb
  rwa [show m - 1 + 1 = m by omega] at this

include hm in
theorem a_A9 {s : Slot Va} (hs : s.1 = (X.length + 2, m)) (hb : bit Va (X.length + 2) m = true) :
    (next hW s).1 = (X.length + 3, m - 1) :=
  next_σ_right_succ hW (a_letters X Y m d).2.2 (by rw [hs, show m - 1 + 1 = m by omega])
    (by rw [show m - 1 + 1 = m by omega]; exact hb)

include hm in
theorem a_A10 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Va (X.length + 2) p = true) (hpm : m + 1 ≤ p) :
    (next hW s).1 = (X.length + 3, p) ∧ bit Va (X.length + 3) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(a_letters X Y m d).2.2]; simp only [idx, arity]; omega)
  rw [(a_letters X Y m d).2.2] at this
  simpa [coarity, arity] using this

theorem a_A11 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 1) q = false) (hqm : q < m - 1) :
    (next hW s).1 = (X.length, q) ∧ bit Va X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (a_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

include hm in
theorem a_A12 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m - 1 ∨ q = m)
    (hb : bit Va (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (a_letters X Y m d).1 hs (by omega) hb

include hm in
theorem a_A13 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 1) q = false) (hqm : m + 1 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Va X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (a_letters X Y m d).1]; simp only [idx, coarity]; omega)
  rw [Nat.add_sub_cancel, (a_letters X Y m d).1] at this
  simpa [arity, coarity] using this

include hm in
theorem a_A14 {s : Slot Va} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m - 1 else m) := by
  rw [next_cusp_l hW (a_letters X Y m d).1 hs]
  cases d <;> simp <;> omega

theorem a_A15 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 2) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Va (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e2, (a_letters X Y m d).2.1]; exact hqm)
  rwa [e2] at this

theorem a_A16 {s : Slot Va} (hs : s.1 = (X.length + 2, m)) (hb : bit Va (X.length + 2) m = false) :
    (next hW s).1 = (X.length + 1, m + 1) :=
  next_σ_left_idx hW (a_letters X Y m d).2.1 hs hb

theorem a_A17 {s : Slot Va} (hs : s.1 = (X.length + 2, m + 1)) (hb : bit Va (X.length + 2) (m + 1) = false) :
    (next hW s).1 = (X.length + 1, m) :=
  next_σ_left_succ hW (a_letters X Y m d).2.1 hs hb

theorem a_A18 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 2) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Va (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e2, (a_letters X Y m d).2.1]; simpa [idx, coarity] using hqm)
  rw [e2, (a_letters X Y m d).2.1] at this
  simpa [arity, coarity] using this

theorem a_A19 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 3) q = false) (hqm : q < m - 1) :
    (next hW s).1 = (X.length + 2, q) ∧ bit Va (X.length + 2) q = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_lt hW hs hq hb (by rw [e3, (a_letters X Y m d).2.2]; exact hqm)
  rwa [e3] at this

include hm in
theorem a_A20 {s : Slot Va} (hs : s.1 = (X.length + 3, m - 1)) (hb : bit Va (X.length + 3) (m - 1) = false) :
    (next hW s).1 = (X.length + 2, m) := by
  have := next_σ_left_idx hW (a_letters X Y m d).2.2 hs hb
  rwa [show m - 1 + 1 = m by omega] at this

include hm in
theorem a_A21 {s : Slot Va} (hs : s.1 = (X.length + 3, m)) (hb : bit Va (X.length + 3) m = false) :
    (next hW s).1 = (X.length + 2, m - 1) :=
  next_σ_left_succ hW (a_letters X Y m d).2.2 (by rw [hs, show m - 1 + 1 = m by omega])
    (by rw [show m - 1 + 1 = m by omega]; exact hb)

include hm in
theorem a_A22 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 3) q = false) (hqm : m + 1 ≤ q) :
    (next hW s).1 = (X.length + 2, q) ∧ bit Va (X.length + 2) q = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_ge hW hs hq hb (by rw [e3, (a_letters X Y m d).2.2]; simp only [idx, coarity]; omega)
  rw [e3, (a_letters X Y m d).2.2] at this
  simpa [arity, coarity] using this

theorem a_hexit : ∀ u : Slot Va, ∃ n, ExtPiece X Pa Y ((next hW)^[n] u) := by
  apply hexit_of_no_r X Pa Y hW
  intro k' h1 h2 m'
  simp only [List.length_cons, List.length_nil] at h2
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀]; exact fun h => by cases h
  · rw [hℓ₁]; exact fun h => by cases h
  · rw [hℓ₂]; exact fun h => by cases h

/-! the two chains -/

include hm in
theorem a_isSlot_T0 : IsSlot Va (tvTd X.length m t 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := a_cutlen X Y m d hW
  have hlen := a_length X Y m d
  cases t
  · have e : tvTd X.length m false 0 = (X.length + 3, m - 1) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)
  · have e : tvTd X.length m true 0 = (X.length, m - 1) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)

include hm in
theorem a_isSlot_C0 : IsSlot Va (tvCd X.length m d 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := a_cutlen X Y m d hW
  have hlen := a_length X Y m d
  cases d
  · have e : tvCd X.length m false 0 = (X.length + 3, m) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)
  · have e : tvCd X.length m true 0 = (X.length + 3, m + 1) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)

include hm in
/-- the arc of the through-strand: three pieces -/
def aT : Chain Va := ⟨⟨tvTd X.length m t 0, a_isSlot_T0 X Y m d t hm hW⟩, 3, by norm_num⟩

include hm in
/-- the arc of the cusp: six pieces -/
def aC : Chain Va := ⟨⟨tvCd X.length m d 0, a_isSlot_C0 X Y m d hm hW⟩, 6, by norm_num⟩

include hm ht in
theorem aT_slot_val : ∀ j, j ≤ 3 → ((aT X Y m d t hm hW).slot hW j).1 = tvTd X.length m t j := by
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  have s0 : ((aT X Y m d t hm hW).slot hW 0).1 = tvTd X.length m t 0 := rfl
  intro j hj
  cases t
  · simp only [tvTd, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((aT X Y m d false hm hW).slot hW 1).1 = tvT X.length m 2 := by
      rw [Chain.slot_succ]; exact a_A20 X Y m d hm hW s0 B7
    have s2 : ((aT X Y m d false hm hW).slot hW 2).1 = tvT X.length m 1 := by
      rw [Chain.slot_succ]; exact a_A16 X Y m d hW s1 B5
    have s3 : ((aT X Y m d false hm hW).slot hW 3).1 = tvT X.length m 0 := by
      rw [Chain.slot_succ]
      have := (a_A13 X Y m d hm hW s2 (by omega) B3 (by omega)).1
      rwa [show m + 1 - 2 = m - 1 by omega] at this
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
  · simp only [tvTd, ↓reduceIte] at s0 ⊢
    have s1 : ((aT X Y m d true hm hW).slot hW 1).1 = tvT X.length m 1 := by
      rw [Chain.slot_succ]
      have := (a_A2 X Y m d hW s0 (by omega) ht le_rfl).1
      rwa [show m - 1 + 2 = m + 1 by omega] at this
    have s2 : ((aT X Y m d true hm hW).slot hW 2).1 = tvT X.length m 2 := by
      rw [Chain.slot_succ]; exact a_A5 X Y m d hW s1 B3
    have s3 : ((aT X Y m d true hm hW).slot hW 3).1 = tvT X.length m 3 := by
      rw [Chain.slot_succ]; exact a_A9 X Y m d hm hW s2 B5
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3

include hm ht in
theorem aC_slot_val : ∀ j, j ≤ 6 → ((aC X Y m d hm hW).slot hW j).1 = tvCd X.length m d j := by
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  have s0 : ((aC X Y m d hm hW).slot hW 0).1 = tvCd X.length m d 0 := rfl
  intro j hj
  cases d
  · simp only [tvCd, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((aC X Y m false hm hW).slot hW 1).1 = tvC X.length m 5 := by
      rw [Chain.slot_succ]; exact a_A21 X Y m false hm hW s0 B8
    have s2 : ((aC X Y m false hm hW).slot hW 2).1 = tvC X.length m 4 := by
      rw [Chain.slot_succ]; exact (a_A15 X Y m false hW s1 (by omega) B4 (by omega)).1
    have s3 : ((aC X Y m false hm hW).slot hW 3).1 = tvC X.length m 3 := by
      rw [Chain.slot_succ]; exact a_A12 X Y m false hm hW s2 (Or.inl rfl) B1
    have s4 : ((aC X Y m false hm hW).slot hW 4).1 = tvC X.length m 2 := by
      rw [Chain.slot_succ, a_A14 X Y m false hm hW s3]; rfl
    have s5 : ((aC X Y m false hm hW).slot hW 5).1 = tvC X.length m 1 := by
      rw [Chain.slot_succ]; exact a_A4 X Y m false hW s4 B2
    have s6 : ((aC X Y m false hm hW).slot hW 6).1 = tvC X.length m 0 := by
      rw [Chain.slot_succ]; exact (a_A10 X Y m false hm hW s5 (by omega) B6 le_rfl).1
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
  · simp only [tvCd, ↓reduceIte] at s0 ⊢
    have s1 : ((aC X Y m true hm hW).slot hW 1).1 = tvC X.length m 1 := by
      rw [Chain.slot_succ]; exact (a_A22 X Y m true hm hW s0 (by omega) B9 le_rfl).1
    have s2 : ((aC X Y m true hm hW).slot hW 2).1 = tvC X.length m 2 := by
      rw [Chain.slot_succ]; exact a_A17 X Y m true hW s1 B6
    have s3 : ((aC X Y m true hm hW).slot hW 3).1 = tvC X.length m 3 := by
      rw [Chain.slot_succ]; exact a_A12 X Y m true hm hW s2 (Or.inr rfl) B2
    have s4 : ((aC X Y m true hm hW).slot hW 4).1 = tvC X.length m 4 := by
      rw [Chain.slot_succ, a_A14 X Y m true hm hW s3]; rfl
    have s5 : ((aC X Y m true hm hW).slot hW 5).1 = tvC X.length m 5 := by
      rw [Chain.slot_succ]; exact (a_A3 X Y m true hW s4 (by omega) B1 (by omega)).1
    have s6 : ((aC X Y m true hm hW).slot hW 6).1 = tvC X.length m 6 := by
      rw [Chain.slot_succ]; exact a_A8 X Y m true hm hW s5 B4
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6

include hm ht in
theorem aT_col : ∀ j, j < 3 → colOf ((aT X Y m d t hm hW).slot hW j) = if t then colT X.length j else colT X.length (2 - j) := by
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  have hv := aT_slot_val X Y m d t hm hW ht
  intro j hj
  cases t
  · simp only [tvTd, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvT] using B7)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp; omega) (by simpa [tvT] using B5)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp) (by simpa [tvT] using B3)]; rfl
  · simp only [tvTd, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvT] using ht)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp) (by simpa [tvT] using B3)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp; omega) (by simpa [tvT] using B5)]; rfl

include hm ht in
theorem aC_col : ∀ j, j < 6 → colOf ((aC X Y m d hm hW).slot hW j) = colC X.length j := by
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  have hv := aC_slot_val X Y m d t hm hW ht
  intro j hj
  cases d
  · simp only [tvCd, Bool.false_eq_true, ↓reduceIte] at hv
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvC] using B8)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp; omega) (by simpa [tvC] using B4)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp; omega) (by simpa [tvC] using B1)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_true (hv 4 (by norm_num)) (by simp; omega) (by simpa [tvC] using B2)]; rfl
    · rw [block_col_true (hv 5 (by norm_num)) (by simp) (by simpa [tvC] using B6)]; rfl
  · simp only [tvCd, ↓reduceIte] at hv
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp) (by simpa [tvC] using B9)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp) (by simpa [tvC] using B6)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp; omega) (by simpa [tvC] using B2)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_true (hv 4 (by norm_num)) (by simp; omega) (by simpa [tvC] using B1)]; rfl
    · rw [block_col_true (hv 5 (by norm_num)) (by simp; omega) (by simpa [tvC] using B4)]; rfl

include hm ht in
theorem aT_col3 : ExtCol X Pa (colOf ((aT X Y m d t hm hW).slot hW 3)) := by
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  have hv := aT_slot_val X Y m d t hm hW ht 3 le_rfl
  rw [a_extCol]
  cases t
  · simp only [tvTd, Bool.false_eq_true, ↓reduceIte, tvT] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) ht]; omega
  · simp only [tvTd, ↓reduceIte, tvT] at hv
    rw [block_col_true hv (by omega) B7]; omega

include hm ht in
theorem aC_col6 : ExtCol X Pa (colOf ((aC X Y m d hm hW).slot hW 6)) := by
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  have hv := aC_slot_val X Y m d t hm hW ht 6 le_rfl
  rw [a_extCol]
  cases d
  · simp only [tvCd, Bool.false_eq_true, ↓reduceIte, tvC] at hv
    rw [block_col_true hv (by omega) B9]; omega
  · simp only [tvCd, ↓reduceIte, tvC] at hv
    rw [block_col_true hv (by omega) B8]; omega

end TypeIIaWord

section TypeIIaPassage

open U3

variable (X Y : Word) (m : ℕ) (d t : Bool) (hm : 2 ≤ m)
  (hW : (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y).Closed)
  (hW' : (X ++ [Letter.l m d] ++ Y).Closed)

local notation "Va" => X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y
local notation "Pa" => [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)]
local notation "Va'" => X ++ [Letter.l m d] ++ Y
local notation "Pa'" => [Letter.l m d]

include hW'

theorem a'_bits : bit Va' (X.length + 1) m = d ∧ bit Va' (X.length + 1) (m + 1) = !d := by
  have hk₀ : X.length < (Va').length := by rw [a'_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hW' hk₀ (a'_letters X Y m d)
  exact ⟨h1, h2⟩

theorem a'_L1 {s : Slot Va'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Va' X.length p = true)
    (hpm : p < m) : (next hW' s).1 = (X.length + 1, p) ∧ bit Va' (X.length + 1) p = true :=
  next_right_lt hW' hs hp hb (by rw [a'_letters X Y m d]; exact hpm)

theorem a'_L2 {s : Slot Va'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Va' X.length p = true)
    (hpm : m ≤ p) : (next hW' s).1 = (X.length + 1, p + 2) ∧ bit Va' (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW' hs hp hb (by rw [a'_letters X Y m d]; simpa [idx, arity] using hpm)
  rwa [a'_letters X Y m d] at this

theorem a'_L3 {s : Slot Va'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Va' (X.length + 1) q = false) (hqm : q < m) :
    (next hW' s).1 = (X.length, q) ∧ bit Va' X.length q = false := by
  have := next_left_lt hW' hs hq hb (by rw [Nat.add_sub_cancel, a'_letters X Y m d]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem a'_L4 {s : Slot Va'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m ∨ q = m + 1)
    (hb : bit Va' (X.length + 1) q = false) : (next hW' s).1 = (X.length, 0) :=
  next_arm_l hW' (by have := slot_col_lt hW' hs; omega) (a'_letters X Y m d) hs hq hb

theorem a'_L5 {s : Slot Va'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Va' (X.length + 1) q = false) (hqm : m + 2 ≤ q) :
    (next hW' s).1 = (X.length, q - 2) ∧ bit Va' X.length (q - 2) = false := by
  have := next_left_ge hW' hs hq hb (by rw [Nat.add_sub_cancel, a'_letters X Y m d]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, a'_letters X Y m d] at this
  simpa [arity, coarity] using this

theorem a'_L6 {s : Slot Va'} (hs : s.1 = (X.length, 0)) :
    (next hW' s).1 = (X.length + 1, if d then m else m + 1) :=
  next_cusp_l hW' (a'_letters X Y m d) hs

theorem a'_hexit : ∀ u : Slot Va', ∃ n, ExtPiece X Pa' Y ((next hW')^[n] u) := by
  apply hexit_of_no_r X Pa' Y hW'
  intro k' h1 h2 m'
  simp only [List.length_cons, List.length_nil] at h2
  have : k' = X.length := by omega
  subst this
  rw [a'_letters X Y m d]; exact fun h => by cases h

include hm hW

/-- THE BLOCK PASSAGE of the type-II variant (a). -/
theorem a_passage : Passage X Pa Y Pa' hW hW' := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d (bit Va X.length (m - 1)) hm hW rfl
  obtain ⟨B1', B2'⟩ := a'_bits X Y m d hW'
  have hP : Pa ≠ [] := by simp
  have hE := a_sameEffect X Y m d hm hW
  have shiftL : ∀ p, extPair X Pa Pa' (X.length, p) = (X.length, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pa Pa' le_rfl]
  have shiftR : ∀ p, extPair X Pa Pa' (X.length + 3, p) = (X.length + 1, p) := by
    intro p; simp only [extPair, a_shift X m d]
  constructor
  intro b hext hcol
  let b' : Slot Va' := ⟨extPair X Pa Pa' b.1, isSlot_ext X Pa Y Pa' hP hE b.2 hext⟩
  have hb'v : b'.1 = extPair X Pa Pa' b.1 := rfl
  -- the through-strand, as the chain `aT` (with `t := bit Va |X| (m−1)`)
  have curlT : b = (aT X Y m d (bit Va X.length (m - 1)) hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Va), (next hW)^[n] b = c ∧ ExtCol X Pa (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pa (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot Va'), b'.1 = extPair X Pa Pa' b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pa Pa' c.1 ∧ ∀ i < m', ¬ ExtCol X Pa' (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨3, (aT X Y m d _ hm hW).slot hW 3, by rw [hb]; rfl, aT_col3 X Y m d _ hm hW rfl, ?_, ?_⟩
    · intro i hi
      have h := aT_col X Y m d _ hm hW rfl i hi
      rw [hb]
      show ¬ ExtCol X Pa (colOf ((aT X Y m d _ hm hW).slot hW i))
      rw [h, a_extCol]
      cases bit Va X.length (m - 1) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> interval_cases i <;> simp [colT]
    · have h0 := aT_slot_val X Y m d _ hm hW rfl 0 (by norm_num)
      have h3 := aT_slot_val X Y m d _ hm hW rfl 3 le_rfl
      rw [Chain.slot_zero] at h0
      cases hE0 : bit Va X.length (m - 1)
      · -- leftward: `W'`: `(|X|+1, m−1)` leftward through `l_m d` to `(|X|, m−1)`
        rw [hE0] at h0 h3 hb
        have hb0 : b.1 = (X.length + 3, m - 1) := by rw [hb]; exact h0
        have hc3 : ((aT X Y m d false hm hW).slot hW 3).1 = (X.length, m - 1) := h3
        have hslot : IsSlot Va' (X.length + 1, m - 1) := by
          have := isSlot_ext X Pa Y Pa' hP hE (s := (X.length + 3, m - 1)) (hb0 ▸ b.2)
            (by show IsExtSlot X Pa (X.length + 3, m - 1); simp only [IsExtSlot, ExtCut, ExtCol, List.length_cons, List.length_nil]; split_ifs <;> omega)
          rwa [shiftR] at this
        have hbit' : bit Va' (X.length + 1) (m - 1) = false := by rw [a_bit_end X Y m d hm hW, B7, hE0]
        refine ⟨1, ⟨(X.length + 1, m - 1), hslot⟩, by rw [hb0, shiftR], ?_, ?_⟩
        · rw [hc3, shiftL, Function.iterate_one]
          exact (a'_L3 X Y m d hW' (s := ⟨_, hslot⟩) (q := m - 1) rfl (by omega) hbit' (by omega)).1
        · intro i hi
          have : i = 0 := by omega
          subst this
          rw [Function.iterate_zero, id, block_col_false (s := ⟨_, hslot⟩) (k := X.length + 1) (p := m - 1) rfl (by omega) hbit',
            a'_extCol]; omega
      · rw [hE0] at h0 h3 hb
        have hb0 : b.1 = (X.length, m - 1) := by rw [hb]; exact h0
        have hc3 : ((aT X Y m d true hm hW).slot hW 3).1 = (X.length + 3, m - 1) := h3
        have hslot : IsSlot Va' (X.length, m - 1) := by
          have := isSlot_ext X Pa Y Pa' hP hE (s := (X.length, m - 1)) (hb0 ▸ b.2)
            (by show IsExtSlot X Pa (X.length, m - 1); simp only [IsExtSlot, ExtCut, ExtCol, List.length_cons, List.length_nil]; split_ifs <;> omega)
          rwa [shiftL] at this
        have hbit' : bit Va' X.length (m - 1) = true := by rw [a_bit_start, hE0]
        refine ⟨1, ⟨(X.length, m - 1), hslot⟩, by rw [hb0, shiftL], ?_, ?_⟩
        · rw [hc3, shiftR, Function.iterate_one]
          exact (a'_L1 X Y m d hW' (s := ⟨_, hslot⟩) (p := m - 1) rfl (by omega) hbit' (by omega)).1
        · intro i hi
          have : i = 0 := by omega
          subst this
          rw [Function.iterate_zero, id, block_col_true (s := ⟨_, hslot⟩) (k := X.length) (p := m - 1) rfl (by omega) hbit',
            a'_extCol]; omega
  -- the cusp arc, as the chain `aC`
  have curlC : b = (aC X Y m d hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Va), (next hW)^[n] b = c ∧ ExtCol X Pa (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pa (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot Va'), b'.1 = extPair X Pa Pa' b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pa Pa' c.1 ∧ ∀ i < m', ¬ ExtCol X Pa' (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨6, (aC X Y m d hm hW).slot hW 6, by rw [hb]; rfl, aC_col6 X Y m d _ hm hW rfl, ?_, ?_⟩
    · intro i hi
      have h := aC_col X Y m d _ hm hW rfl i hi
      rw [hb]
      show ¬ ExtCol X Pa (colOf ((aC X Y m d hm hW).slot hW i))
      rw [h, a_extCol]
      interval_cases i <;> simp [colC]
    · have h0 := aC_slot_val X Y m d _ hm hW rfl 0 (by norm_num)
      have h6 := aC_slot_val X Y m d _ hm hW rfl 6 le_rfl
      rw [Chain.slot_zero] at h0
      -- `W'`: `(|X|+1, m+1)` (`d`) or `(|X|+1, m)` (`!d`) leftward into the cusp of `l_m d`, out along the other arm
      rcases Bool.eq_false_or_eq_true d with hd | hd
      · have hb0 : b.1 = (X.length + 3, m + 1) := by rw [hb, h0, hd]; rfl
        have hc6 : ((aC X Y m d hm hW).slot hW 6).1 = (X.length + 3, m) := by rw [h6, hd]; rfl
        have hslot : IsSlot Va' (X.length + 1, m + 1) := by
          have := isSlot_ext X Pa Y Pa' hP hE (s := (X.length + 3, m + 1)) (hb0 ▸ b.2)
            (by show IsExtSlot X Pa (X.length + 3, m + 1); simp only [IsExtSlot, ExtCut, ExtCol, List.length_cons, List.length_nil]; split_ifs <;> omega)
          rwa [shiftR] at this
        have hbit' : bit Va' (X.length + 1) (m + 1) = false := by rw [B2', hd]; rfl
        have h1' := a'_L4 X Y m d hW' (s := ⟨_, hslot⟩) rfl (Or.inr rfl) hbit'
        have h2' := a'_L6 X Y m d hW' h1'
        rw [ite_eq_left hd] at h2'
        refine ⟨2, ⟨_, hslot⟩, by rw [hb0, shiftR], ?_, ?_⟩
        · rw [hc6, shiftR, Function.iterate_succ_apply', Function.iterate_one, h2']
        · intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · rw [Function.iterate_zero, id, block_col_false (s := ⟨_, hslot⟩) (k := X.length + 1) (p := m + 1) rfl (by omega) hbit',
              a'_extCol]; omega
          · rw [Function.iterate_one, block_col_vertex h1', a'_extCol]; omega

      · have hb0 : b.1 = (X.length + 3, m) := by rw [hb, h0, hd]; rfl
        have hc6 : ((aC X Y m d hm hW).slot hW 6).1 = (X.length + 3, m + 1) := by rw [h6, hd]; rfl
        have hslot : IsSlot Va' (X.length + 1, m) := by
          have := isSlot_ext X Pa Y Pa' hP hE (s := (X.length + 3, m)) (hb0 ▸ b.2)
            (by show IsExtSlot X Pa (X.length + 3, m); simp only [IsExtSlot, ExtCut, ExtCol, List.length_cons, List.length_nil]; split_ifs <;> omega)
          rwa [shiftR] at this
        have hbit' : bit Va' (X.length + 1) m = false := by rw [B1', hd]
        have h1' := a'_L4 X Y m d hW' (s := ⟨_, hslot⟩) rfl (Or.inl rfl) hbit'
        have h2' := a'_L6 X Y m d hW' h1'
        rw [ite_eq_right (by simp [hd])] at h2'
        refine ⟨2, ⟨_, hslot⟩, by rw [hb0, shiftR], ?_, ?_⟩
        · rw [hc6, shiftR, Function.iterate_succ_apply', Function.iterate_one, h2']
        · intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · rw [Function.iterate_zero, id, block_col_false (s := ⟨_, hslot⟩) (k := X.length + 1) (p := m) rfl (by omega) hbit',
              a'_extCol]; omega
          · rw [Function.iterate_one, block_col_vertex h1', a'_extCol]; omega
  rcases (entry_iff X Pa Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hb'1 : b'.1 = (X.length, p) := by rw [hb'v, hb, shiftL]
    have hbit' : bit Va' X.length p = true := by rw [a_bit_start, hbit]
    have hcol0 : ¬ ExtCol X Pa (colOf b) := by rw [block_col_true hb hp hbit, a_extCol]; omega
    have hcol0' : ¬ ExtCol X Pa' (colOf b') := by rw [block_col_true hb'1 hp hbit', a'_extCol]; omega
    rcases lt_or_ge p (m - 1) with hpm | hpm
    · obtain ⟨h1, hb1⟩ := a_A1 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := a_A3 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨h3, hb3⟩ := a_A7 X Y m d hW h2 hp hb2 hpm
      obtain ⟨h1', hb1'⟩ := a'_L1 X Y m d hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa) hcol0
        (passage_step hW (ExtCol X Pa) (by rw [block_col_true h1 hp hb1, a_extCol]; omega)
        (passage_step hW (ExtCol X Pa) (by rw [block_col_true h2 hp hb2, a_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pa') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h3 hp hb3, a_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftR]
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
    · -- `p = m − 1`: the through-strand (rightward)
      subst hpe
      apply curlT
      apply Subtype.ext
      rw [hb]
      show _ = tvTd X.length m (bit Va X.length (m - 1)) 0
      rw [hbit]; rfl
    · obtain ⟨h1, hb1⟩ := a_A2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := a_A6 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨h3, hb3⟩ := a_A10 X Y m d hm hW h2 (by omega) hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := a'_L2 X Y m d hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa) hcol0
        (passage_step hW (ExtCol X Pa) (by rw [block_col_true h1 (by omega) hb1, a_extCol]; omega)
        (passage_step hW (ExtCol X Pa) (by rw [block_col_true h2 (by omega) hb2, a_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pa') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h3 (by omega) hb3, a_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftR]
  · -- from the right at `(|X|+3, q)`
    replace hb : b.1 = (X.length + 3, p) := hb
    replace hbit : bit Va (X.length + 3) p = false := hbit
    have hb'1 : b'.1 = (X.length + 1, p) := by rw [hb'v, hb, shiftR]
    have hbit' : bit Va' (X.length + 1) p = false := by rw [a_bit_end X Y m d hm hW, hbit]
    have hcol0 : ¬ ExtCol X Pa (colOf b) := by rw [block_col_false hb hp hbit, a_extCol]; omega
    have hcol0' : ¬ ExtCol X Pa' (colOf b') := by rw [block_col_false hb'1 hp hbit', a'_extCol]; omega
    rcases lt_or_ge p (m - 1) with hpm | hpm
    · obtain ⟨h1, hb1⟩ := a_A19 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := a_A15 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨h3, hb3⟩ := a_A11 X Y m d hW h2 hp hb2 hpm
      obtain ⟨h1', hb1'⟩ := a'_L3 X Y m d hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa) hcol0
        (passage_step hW (ExtCol X Pa) (by rw [block_col_false h1 hp hb1, a_extCol]; omega)
        (passage_step hW (ExtCol X Pa) (by rw [block_col_false h2 hp hb2, a_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pa') hcol0' (passage_end hW')
      have hk3 := (cutSlot_facts hW h3 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 hp hb3, a_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftL]
    rcases lt_or_ge p (m + 2) with hpm2 | hpm2
    · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
      rcases this with hpe | hpe | hpe
      · -- the through-strand, leftward
        apply curlT
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvTd X.length m (bit Va X.length (m - 1)) 0
        rw [hpe, B7] at hbit
        rw [hbit]; rfl
      · -- the cusp arc entered along `(|X|+3, m)`: `d = false`
        apply curlC
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvCd X.length m d 0
        rw [hpe, B8] at hbit
        rw [hbit]; rfl
      · -- entered along `(|X|+3, m+1)`: `d = true`
        apply curlC
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvCd X.length m d 0
        rw [hpe, B9] at hbit
        have hd : d = true := by simpa using hbit
        rw [hd]; rfl
    · obtain ⟨h1, hb1⟩ := a_A22 X Y m d hm hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := a_A18 X Y m d hW h1 hp hb1 hpm2
      obtain ⟨h3, hb3⟩ := a_A13 X Y m d hm hW h2 hp hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := a'_L5 X Y m d hW' hb'1 hp hbit' hpm2
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa) hcol0
        (passage_step hW (ExtCol X Pa) (by rw [block_col_false h1 hp hb1, a_extCol]; omega)
        (passage_step hW (ExtCol X Pa) (by rw [block_col_false h2 hp hb2, a_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pa') hcol0' (passage_end hW')
      have hk3 := (cutSlot_facts hW h3 (by omega)).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 (by omega) hb3, a_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftL]

end TypeIIaPassage

/-! #### F3. The type-II variant (a): the moved diagram -/

/-- the moved positions of the through-strand's four vertices (entry height `h`): the two interior vertices are
lifted above the cusp arc -/
def mvA (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h + 5 / 8)
  | 2 => (((k + 2 : ℕ) : ℝ), h + 5 / 8)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the realization's positions of the through-strand's vertices -/
def pvA (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h - 2)
  | 2 => (((k + 2 : ℕ) : ℝ), h - 1)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the positions of the cusp arc's seven vertices (unmoved) -/
def pvB (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => (((k + 3 : ℕ) : ℝ), h - 2)
  | 1 => (((k + 2 : ℕ) : ℝ), h - 2)
  | 2 => (((k + 1 : ℕ) : ℝ), h - 1)
  | 3 => ((k : ℝ) + 1 / 2, h - 1 / 2)
  | 4 => (((k + 1 : ℕ) : ℝ), h)
  | 5 => (((k + 2 : ℕ) : ℝ), h)
  | _ => (((k + 3 : ℕ) : ℝ), h - 1)

/-- the two moved slots of the type-II variant (a) -/
def IsMovedA (k m : ℕ) (s : ℕ × ℕ) : Prop := s = (k + 1, m + 1) ∨ s = (k + 2, m)

/-- the moved vertex function of the type-II variant (a) -/
def mvIIa (W : Word) (k m : ℕ) (h : ℝ) (u : Slot W) : Plane :=
  if u.1 = (k + 1, m + 1) then mvA k h 1
  else if u.1 = (k + 2, m) then mvA k h 2
  else pt .std W u.1

section MvIIa

variable (W : Word) (k m : ℕ) (h : ℝ)

theorem mvIIa_of_not_moved {u : Slot W} (hu : ¬ IsMovedA k m u.1) : mvIIa W k m h u = pt .std W u.1 := by
  unfold IsMovedA at hu
  simp only [not_or] at hu
  obtain ⟨h1, h2⟩ := hu
  simp [mvIIa, h1, h2]

theorem mvIIa_v1 {u : Slot W} (hu : u.1 = (k + 1, m + 1)) : mvIIa W k m h u = mvA k h 1 := by simp [mvIIa, hu]
theorem mvIIa_v2 {u : Slot W} (hu : u.1 = (k + 2, m)) : mvIIa W k m h u = mvA k h 2 := by
  simp [mvIIa, hu]

/-- the slots of the exterior are unmoved -/
theorem mvIIa_of_ext {u : Slot W} (hu : ExtSl k (k + 3) u.1) : mvIIa W k m h u = pt .std W u.1 := by
  apply mvIIa_of_not_moved
  obtain ⟨j, p, hu'⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu'] at hu ⊢
  unfold ExtSl at hu
  unfold IsMovedA
  simp only [Prod.mk.injEq]
  split_ifs at hu with h0 <;> omega

theorem mvIIa_xcoord (hm : 1 ≤ m) (u : Slot W) : (mvIIa W k m h u).1 = (pt .std W u.1).1 := by
  by_cases hmv : IsMovedA k m u.1
  · unfold IsMovedA at hmv
    rcases hmv with e | e
    · rw [mvIIa_v1 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvIIa_v2 W k m h e, e, std_pt_cut _ (by omega)]; rfl
  · rw [mvIIa_of_not_moved W k m h hmv]

theorem mvIIa_injective (n : ℕ) : Function.Injective (mvIIa W k m (-(n : ℝ) + 1)) := by
  have ng : ∀ i, 1 ≤ i → i ≤ 2 → ∀ s, mvA k (-(n : ℝ) + 1) i ≠ pt .std W s := by
    intro i hi1 hi2 s
    have := nonGrid_eighth n 5 (by decide)
    have e : -(n : ℝ) + 1 + 5 / 8 = -(n : ℝ) + 1 + ((5 : ℤ) : ℝ) / 8 := by push_cast; ring
    interval_cases i
    · show (((k + 1 : ℕ) : ℝ), -(n : ℝ) + 1 + 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · show (((k + 2 : ℕ) : ℝ), -(n : ℝ) + 1 + 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
  have hval : ∀ u : Slot W, IsMovedA k m u.1 → ∃ i, 1 ≤ i ∧ i ≤ 2 ∧ mvIIa W k m (-(n : ℝ) + 1) u = mvA k (-(n : ℝ) + 1) i ∧
      (i = 1 → u.1 = (k + 1, m + 1)) ∧ (i = 2 → u.1 = (k + 2, m)) := by
    intro u hu
    unfold IsMovedA at hu
    rcases hu with e | e
    · exact ⟨1, le_rfl, by norm_num, mvIIa_v1 W k m _ e, fun _ => e, fun h => absurd h (by norm_num)⟩
    · exact ⟨2, by norm_num, le_rfl, mvIIa_v2 W k m _ e, fun h => absurd h (by norm_num), fun _ => e⟩
  have hdist : ∀ i j, 1 ≤ i → i ≤ 2 → 1 ≤ j → j ≤ 2 → mvA k (-(n : ℝ) + 1) i = mvA k (-(n : ℝ) + 1) j → i = j := by
    intro i j hi1 hi2 hj1 hj2 he
    interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; have := congrArg Prod.fst he; simp only [mvA] at this; push_cast at this; linarith)
  intro u v huv
  by_cases hu : IsMovedA k m u.1
  · obtain ⟨i, hi1, hi2, hui, hu1, hu2⟩ := hval u hu
    by_cases hv : IsMovedA k m v.1
    · obtain ⟨j, hj1, hj2, hvj, hv1, hv2⟩ := hval v hv
      have := hdist i j hi1 hi2 hj1 hj2 (hui.symm.trans (huv.trans hvj))
      subst this
      apply Subtype.ext
      interval_cases i
      · rw [hu1 rfl, hv1 rfl]
      · rw [hu2 rfl, hv2 rfl]
    · rw [hui, mvIIa_of_not_moved W k m _ hv] at huv
      exact absurd huv (ng i hi1 hi2 _)
  · by_cases hv : IsMovedA k m v.1
    · obtain ⟨j, hj1, hj2, hvj, -⟩ := hval v hv
      rw [hvj, mvIIa_of_not_moved W k m _ hu] at huv
      exact absurd huv.symm (ng j hj1 hj2 _)
    · rw [mvIIa_of_not_moved W k m _ hu, mvIIa_of_not_moved W k m _ hv] at huv
      exact pt_inj _ _ huv

end MvIIa

section IIaVertices

variable (k : ℕ) (h : ℝ)

theorem mvA_int : ∀ i, 1 ≤ i → i ≤ 2 → mvA k h i ∈ interior (polygon (tIIL k h)) := by
  intro i h1 h2
  interval_cases i
  · exact tIIL_int_cut1 k h (5 / 8) (by norm_num) (by norm_num)
  · exact tIIL_int_cut2 k h (5 / 8) (by norm_num) (by norm_num)

theorem pvA_int : ∀ i, 1 ≤ i → i ≤ 2 → pvA k h i ∈ interior (polygon (tIIL k h)) := by
  intro i h1 h2
  interval_cases i
  · have := tIIL_int_cut1 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIL_int_cut2 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem pvB_int : ∀ i, 1 ≤ i → i ≤ 5 → pvB k h i ∈ interior (polygon (tIIL k h)) := by
  intro i h1 h5
  interval_cases i
  · have := tIIL_int_cut2 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIL_int_cut1 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIL_int_cuspL k h (-(1 / 2)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIL_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tIIL_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem mvA_mem : ∀ i, i ≤ 3 → mvA k h i ∈ polygon (tIIL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIL_mem_left k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · exact interior_subset (mvA_int k h i h0 (by omega))
  · have : i = 3 := by omega
    subst this
    have := tIIL_mem_right k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem pvA_mem : ∀ i, i ≤ 3 → pvA k h i ∈ polygon (tIIL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIL_mem_left k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · exact interior_subset (pvA_int k h i h0 (by omega))
  · have : i = 3 := by omega
    subst this
    have := tIIL_mem_right k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem pvB_mem : ∀ i, i ≤ 6 → pvB k h i ∈ polygon (tIIL k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIL_mem_right k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  rcases Nat.lt_or_ge i 6 with h6 | h6
  · exact interior_subset (pvB_int k h i h0 (by omega))
  · have : i = 6 := by omega
    subst this
    have := tIIL_mem_right k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

/-! the geometric facts of the same-column pairs of the moved variant (a) -/

macro "aII_pair" : tactic => `(tactic| (
  intro τ τ' h0 h1 h0' h1' he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [mvA, pvB, segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy))

theorem aII_NM_T0C2 : NoMeet (mvA k h 0) (mvA k h 1) (pvB k h 2) (pvB k h 3) := by aII_pair; linarith
theorem aII_NM_T0C3 : NoMeet (mvA k h 0) (mvA k h 1) (pvB k h 3) (pvB k h 4) := by aII_pair; linarith
theorem aII_NM_T1C1 : NoMeet (mvA k h 1) (mvA k h 2) (pvB k h 1) (pvB k h 2) := by aII_pair; linarith
theorem aII_NM_T1C4 : NoMeet (mvA k h 1) (mvA k h 2) (pvB k h 4) (pvB k h 5) := by aII_pair; linarith
theorem aII_NM_T2C0 : NoMeet (mvA k h 2) (mvA k h 3) (pvB k h 0) (pvB k h 1) := by aII_pair; linarith
theorem aII_NM_T2C5 : NoMeet (mvA k h 2) (mvA k h 3) (pvB k h 5) (pvB k h 6) := by aII_pair; linarith
theorem aII_NM_C1C4 : NoMeet (pvB k h 1) (pvB k h 2) (pvB k h 4) (pvB k h 5) := by aII_pair; linarith
theorem aII_NM_C0C5 : NoMeet (pvB k h 0) (pvB k h 1) (pvB k h 5) (pvB k h 6) := by aII_pair; linarith
theorem aII_OJ234 : OnlyAtJoint (pvB k h 2) (pvB k h 3) (pvB k h 4) := by
  aII_pair; constructor <;> linarith

end IIaVertices

/-! #### F4. The type-II variant (a): the specification -/

section TypeIIaSpec

open U3

variable (X Y : Word) (m : ℕ) (d t : Bool) (hm : 2 ≤ m)
  (hW : (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y) X.length (m - 1) = t)

local notation "Va" => X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y
local notation "Pa" => [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)]
local notation "Va'" => X ++ [Letter.l m d] ++ Y
local notation "Pa'" => [Letter.l m d]
local notation "hA" => (-(m : ℝ) + 1)

/-- the moved vertex function of the type-II variant (a) -/
def aMv : Slot Va → Plane := mvIIa Va X.length m hA

theorem aMv_apply (u : Slot Va) : aMv X Y m d u = mvIIa Va X.length m hA u := rfl

include hm

theorem a_hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]

theorem a_pt_T : ∀ i, i ≤ 3 → pt .std Va (tvT X.length m i) = pvA X.length hA i := by
  have hm1 := a_hm1 m hm
  intro i hi
  interval_cases i
  · show pt .std Va (X.length, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA]; rw [hm1]; ring)
  · show pt .std Va (X.length + 1, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA]; push_cast; ring)
  · show pt .std Va (X.length + 2, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA]; ring)
  · show pt .std Va (X.length + 3, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA]; rw [hm1]; ring)

theorem a_pt_C : ∀ i, i ≤ 6 → pt .std Va (tvC X.length m i) = pvB X.length hA i := by
  have hm1 := a_hm1 m hm
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
  intro i hi
  interval_cases i
  · show pt .std Va (X.length + 3, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB]; push_cast; ring)
  · show pt .std Va (X.length + 2, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB]; push_cast; ring)
  · show pt .std Va (X.length + 1, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB]; ring)
  · show pt .std Va (X.length, 0) = _
    rw [std_pt_cusp, hℓ₀]; exact Prod.ext rfl (by simp only [pvB, idx]; rw [hm1]; ring)
  · show pt .std Va (X.length + 1, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB]; rw [hm1]; ring)
  · show pt .std Va (X.length + 2, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB]; rw [hm1]; ring)
  · show pt .std Va (X.length + 3, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB]; ring)

theorem a_mv_T : ∀ i, i ≤ 3 → ∀ u : Slot Va, u.1 = tvT X.length m i → aMv X Y m d u = mvA X.length hA i := by
  intro i hi u hu
  rw [aMv_apply]
  interval_cases i
  · rw [mvIIa_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedA, tvT, Prod.mk.injEq]; omega), hu,
      a_pt_T X Y m d hm 0 (by norm_num)]; rfl
  · exact mvIIa_v1 _ _ _ _ hu
  · exact mvIIa_v2 _ _ _ _ hu
  · rw [mvIIa_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedA, tvT, Prod.mk.injEq]; omega), hu,
      a_pt_T X Y m d hm 3 (by norm_num)]; rfl

theorem a_mv_C : ∀ i, i ≤ 6 → ∀ u : Slot Va, u.1 = tvC X.length m i → aMv X Y m d u = pvB X.length hA i := by
  intro i hi u hu
  have hnm : ¬ IsMovedA X.length m u.1 := by
    rw [hu]; interval_cases i <;> simp only [IsMovedA, tvC, Prod.mk.injEq] <;> omega
  rw [aMv_apply, mvIIa_of_not_moved _ _ _ _ hnm, hu]
  exact a_pt_C X Y m d hm i hi

omit hm in
/-- the vertices of the two arcs are pairwise distinct -/
theorem tvT_inj : ∀ i j, i ≤ 3 → j ≤ 3 → tvT X.length m i = tvT X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tvT, Prod.mk.injEq] at he; omega)

theorem tvC_inj : ∀ i j, i ≤ 6 → j ≤ 6 → tvC X.length m i = tvC X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tvC, Prod.mk.injEq] at he; omega)

theorem tvT_ne_tvC : ∀ i j, i ≤ 3 → j ≤ 6 → tvT X.length m i ≠ tvC X.length m j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> simp only [tvT, tvC, Prod.mk.injEq] at he <;> omega

include hW ht

theorem aT_mv_slot : ∀ j, j ≤ 3 → aMv X Y m d ((aT X Y m d t hm hW).slot hW j) =
    if t then mvA X.length hA j else mvA X.length hA (3 - j) := by
  intro j hj
  have hs := aT_slot_val X Y m d t hm hW ht j hj
  cases t
  · simp only [tvTd, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact a_mv_T X Y m d hm (3 - j) (by omega) _ hs
  · simp only [tvTd, ↓reduceIte] at hs ⊢
    exact a_mv_T X Y m d hm j hj _ hs

theorem aT_pt_slot : ∀ j, j ≤ 3 → pt .std Va ((aT X Y m d t hm hW).slot hW j).1 =
    if t then pvA X.length hA j else pvA X.length hA (3 - j) := by
  intro j hj
  have hs := aT_slot_val X Y m d t hm hW ht j hj
  cases t
  · simp only [tvTd, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact a_pt_T X Y m d hm (3 - j) (by omega)
  · simp only [tvTd, ↓reduceIte] at hs ⊢
    rw [hs]; exact a_pt_T X Y m d hm j hj

theorem aC_mv_slot : ∀ j, j ≤ 6 → aMv X Y m d ((aC X Y m d hm hW).slot hW j) =
    if d then pvB X.length hA j else pvB X.length hA (6 - j) := by
  intro j hj
  have hs := aC_slot_val X Y m d t hm hW ht j hj
  cases d
  · simp only [tvCd, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact a_mv_C X Y m false hm (6 - j) (by omega) _ hs
  · simp only [tvCd, ↓reduceIte] at hs ⊢
    exact a_mv_C X Y m true hm j hj _ hs

theorem aC_pt_slot : ∀ j, j ≤ 6 → pt .std Va ((aC X Y m d hm hW).slot hW j).1 =
    if d then pvB X.length hA j else pvB X.length hA (6 - j) := by
  intro j hj
  have hs := aC_slot_val X Y m d t hm hW ht j hj
  cases d
  · simp only [tvCd, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact a_pt_C X Y m false hm (6 - j) (by omega)
  · simp only [tvCd, ↓reduceIte] at hs ⊢
    rw [hs]; exact a_pt_C X Y m true hm j hj

omit ht in
theorem aT_next_slot : ∀ j, j < 3 → next hW ((aT X Y m d t hm hW).slot hW j) = (aT X Y m d t hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

omit ht in
theorem aC_next_slot : ∀ j, j < 6 → next hW ((aC X Y m d hm hW).slot hW j) = (aC X Y m d hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

theorem aT_chain_in : ∀ j, j < 3 → PieceIn (tIIL X.length hA) hW (aMv X Y m d) ((aT X Y m d t hm hW).slot hW j) ∧
    PieceIn (tIIL X.length hA) hW (ptv .std) ((aT X Y m d t hm hW).slot hW j) := by
  intro j hj
  have e := aT_next_slot X Y m d t hm hW j hj
  constructor
  · show SegIn _ (aMv X Y m d _) (aMv X Y m d (next hW _))
    rw [e, aT_mv_slot X Y m d t hm hW ht j (by omega), aT_mv_slot X Y m d t hm hW ht (j + 1) (by omega)]
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (mvA_mem _ _ _ (by omega)) (mvA_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (mvA_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (mvA_int _ _ _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (mvA_mem _ _ _ (by omega)) (mvA_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (mvA_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (mvA_int _ _ _ (by omega) (by omega))
  · show SegIn _ (pt .std Va _) (pt .std Va (next hW _).1)
    rw [e, aT_pt_slot X Y m d t hm hW ht j (by omega), aT_pt_slot X Y m d t hm hW ht (j + 1) (by omega)]
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine segIn_of_mem (pvA_mem _ _ _ (by omega)) (pvA_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pvA_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pvA_int _ _ _ (by omega) (by omega))
    · simp only [↓reduceIte]
      refine segIn_of_mem (pvA_mem _ _ _ (by omega)) (pvA_mem _ _ _ (by omega)) ?_
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · exact Or.inr (pvA_int _ _ _ (by norm_num) (by norm_num))
      · exact Or.inl (pvA_int _ _ _ (by omega) (by omega))

theorem aC_chain_in : ∀ j, j < 6 → PieceIn (tIIL X.length hA) hW (aMv X Y m d) ((aC X Y m d hm hW).slot hW j) ∧
    PieceIn (tIIL X.length hA) hW (ptv .std) ((aC X Y m d hm hW).slot hW j) := by
  intro j hj
  have e := aC_next_slot X Y m d hm hW j hj
  have key : ∀ (f : ℕ → Plane), (∀ i, i ≤ 6 → f i ∈ polygon (tIIL X.length hA)) →
      (∀ i, 1 ≤ i → i ≤ 5 → f i ∈ interior (polygon (tIIL X.length hA))) →
      SegIn (tIIL X.length hA) (if d then f j else f (6 - j)) (if d then f (j + 1) else f (6 - (j + 1))) := by
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
  · show SegIn _ (aMv X Y m d _) (aMv X Y m d (next hW _))
    rw [e, aC_mv_slot X Y m d t hm hW ht j (by omega), aC_mv_slot X Y m d t hm hW ht (j + 1) (by omega)]
    exact key _ (pvB_mem _ _) (pvB_int _ _)
  · show SegIn _ (pt .std Va _) (pt .std Va (next hW _).1)
    rw [e, aC_pt_slot X Y m d t hm hW ht j (by omega), aC_pt_slot X Y m d t hm hW ht (j + 1) (by omega)]
    exact key _ (pvB_mem _ _) (pvB_int _ _)

theorem aT_vert : ∀ j, 0 < j → j < 3 → aMv X Y m d ((aT X Y m d t hm hW).slot hW j) ∈ interior (polygon (tIIL X.length hA)) ∧
    pt .std Va ((aT X Y m d t hm hW).slot hW j).1 ∈ interior (polygon (tIIL X.length hA)) := by
  intro j h0 hj
  rw [aT_mv_slot X Y m d t hm hW ht j (by omega), aT_pt_slot X Y m d t hm hW ht j (by omega)]
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨mvA_int _ _ _ (by omega) (by omega), pvA_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨mvA_int _ _ _ (by omega) (by omega), pvA_int _ _ _ (by omega) (by omega)⟩

theorem aC_vert : ∀ j, 0 < j → j < 6 → aMv X Y m d ((aC X Y m d hm hW).slot hW j) ∈ interior (polygon (tIIL X.length hA)) ∧
    pt .std Va ((aC X Y m d hm hW).slot hW j).1 ∈ interior (polygon (tIIL X.length hA)) := by
  intro j h0 hj
  rw [aC_mv_slot X Y m d t hm hW ht j (by omega), aC_pt_slot X Y m d t hm hW ht j (by omega)]
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨pvB_int _ _ _ (by omega) (by omega), pvB_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨pvB_int _ _ _ (by omega) (by omega), pvB_int _ _ _ (by omega) (by omega)⟩

omit hW ht in
theorem a_moved : ∀ u : Slot Va, aMv X Y m d u = pt .std Va u.1 ∨
    (aMv X Y m d u ∈ interior (polygon (tIIL X.length hA)) ∧ pt .std Va u.1 ∈ interior (polygon (tIIL X.length hA))) := by
  intro u
  by_cases hmv : IsMovedA X.length m u.1
  · right
    unfold IsMovedA at hmv
    rcases hmv with e | e
    · have h2 : pt .std Va (X.length + 1, m + 1) = pvA X.length hA 1 := a_pt_T X Y m d hm 1 (by norm_num)
      rw [a_mv_T X Y m d hm 1 (by norm_num) u e, e, h2]
      exact ⟨mvA_int _ _ _ (by norm_num) (by norm_num), pvA_int _ _ _ (by norm_num) (by norm_num)⟩
    · have h2 : pt .std Va (X.length + 2, m) = pvA X.length hA 2 := a_pt_T X Y m d hm 2 (by norm_num)
      rw [a_mv_T X Y m d hm 2 (by norm_num) u e, e, h2]
      exact ⟨mvA_int _ _ _ (by norm_num) (by norm_num), pvA_int _ _ _ (by norm_num) (by norm_num)⟩
  · left
    rw [aMv_apply, mvIIa_of_not_moved _ _ _ _ hmv]

/-- the chain slot carrying the through-vertex `tvT i` -/
theorem aT_chain_of (i : ℕ) (hi : i ≤ 3) {u : Slot Va} (hu : u.1 = tvT X.length m i)
    (hd : (t = true ∧ i < 3) ∨ (t = false ∧ 0 < i)) : OnChain hW (aT X Y m d t hm hW) u := by
  cases t
  · refine ⟨3 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · show 3 - i < 3; omega
    · rw [aT_slot_val X Y m d false hm hW ht (3 - i) (by omega), hu]
      simp only [tvTd, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [aT_slot_val X Y m d true hm hW ht i hi, hu]
      simp only [tvTd, ↓reduceIte]

/-- the chain slot carrying the cusp-arc vertex `tvC i` -/
theorem aC_chain_of (i : ℕ) (hi : i ≤ 6) {u : Slot Va} (hu : u.1 = tvC X.length m i)
    (hd : (d = true ∧ i < 6) ∨ (d = false ∧ 0 < i)) : OnChain hW (aC X Y m d hm hW) u := by
  cases d
  · refine ⟨6 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · show 6 - i < 6; omega
    · rw [aC_slot_val X Y m false t hm hW ht (6 - i) (by omega), hu]
      simp only [tvCd, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [aC_slot_val X Y m true t hm hW ht i hi, hu]
      simp only [tvCd, ↓reduceIte]

omit hm ht in
/-- an unchanged spectator piece with an explicit outside witness -/
theorem a_spec {u : Slot Va} {j p j' p' : ℕ} (hu : u.1 = (j, p)) (hn : (next hW u).1 = (j', p'))
    (hp : p ≠ 0) (hp' : p' ≠ 0) (h1 : ¬ IsMovedA X.length m (j, p)) (h2 : ¬ IsMovedA X.length m (j', p'))
    (hout : SegOut (tIIL X.length hA) ((j : ℝ), -(p : ℝ)) ((j' : ℝ), -(p' : ℝ))) :
    Unch .std hW (aMv X Y m d) u ∧ PieceOut (tIIL X.length hA) hW (ptv .std) u := by
  constructor
  · constructor
    · rw [aMv_apply, mvIIa_of_not_moved _ _ _ _ (hu ▸ h1)]
    · rw [aMv_apply, mvIIa_of_not_moved _ _ _ _ (hn ▸ h2)]
  · show SegOut _ (pt .std Va u.1) (pt .std Va (next hW u).1)
    rw [hu, hn, std_pt_cut _ hp, std_pt_cut _ hp']
    exact hout

omit hm hW ht in
theorem a_hmv : ∀ v : Slot Va, ExtSl X.length (X.length + 3) v.1 → aMv X Y m d v = pt .std Va v.1 :=
  fun v hv => by rw [aMv_apply]; exact mvIIa_of_ext _ _ _ _ hv

/-- THE CLASSIFICATION of the type-II variant (a). -/
theorem a_rest : ∀ u : Slot Va, OnChain hW (aT X Y m d t hm hW) u ∨ OnChain hW (aC X Y m d hm hW) u ∨
    (Unch .std hW (aMv X Y m d) u ∧ PieceOut (tIIL X.length hA) hW (ptv .std) u) := by
  intro u
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  -- the numeric side conditions of the spectators
  have above : ∀ {q : ℕ}, q < m - 1 → hA + 1 ≤ -(q : ℝ) := fun {q} hq => by
    have : (q : ℝ) + 2 ≤ m := by exact_mod_cast (by omega : q + 2 ≤ m)
    linarith
  have below : ∀ {q : ℕ}, m + 2 ≤ q → -(q : ℝ) ≤ hA - 3 := fun {q} hq => by
    have : (m : ℝ) + 2 ≤ q := by exact_mod_cast hq
    linarith
  have slant : ∀ {q : ℕ}, m ≤ q → -(q : ℝ) ≤ hA - 1 := fun {q} hq => by
    have : (m : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have chainT := aT_chain_of X Y m d t hm hW ht
  have chainC := aC_chain_of X Y m d t hm hW ht
  have nm : ∀ a b : ℕ, (a ≠ X.length + 1 ∨ b ≠ m + 1) → (a ≠ X.length + 2 ∨ b ≠ m) → ¬ IsMovedA X.length m (a, b) := by
    intro a b h1 h2 h
    unfold IsMovedA at h
    simp only [Prod.mk.injEq] at h
    omega
  by_cases hext : ExtCol X Pa (colOf u)
  · right; right
    have hext' := (a_extCol X m d _).1 hext
    exact ⟨unch_of_extCol .std hW _ (a_hmv X Y m d) hext',
      pieceOut_of_extCol _ .std hW _ (tIIL_xge_mem _ _) (tIIL_xle_mem _ _) (unch_pt _ _ _) hext'⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, a_extCol] at hext
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
  cases hb : bit Va j p
  · -- leftward pieces
    rw [block_col_false hu hp hb, a_extCol] at hext
    have : j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    rcases this with rfl | rfl | rfl
    · -- cut `|X|+1`, column `|X|`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := a_A11 X Y m d hW hu hp hb hpm
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = false := by rw [hpe, B1] at hb; exact hb
          exact Or.inr (Or.inl (chainC 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
        · have hd : d = true := by rw [hpe, B2] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
        · have htt : t = false := by rw [hpe, B3] at hb; exact hb
          exact Or.inl (chainT 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := a_A13 X Y m d hm hW hu hp hb (by omega)
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp (by omega) (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_slant' _ _ (by omega) (slant (q := p - 2) (by omega)))))
    · -- cut `|X|+2`, column `|X|+1`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := a_A15 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = false := by rw [hpe, B4] at hb; exact hb
          exact Or.inr (Or.inl (chainC 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
        · have htt : t = false := by rw [hpe, B5] at hb; exact hb
          exact Or.inl (chainT 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
        · have hd : d = true := by rw [hpe, B6] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := a_A18 X Y m d hW hu hp hb hpm2
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_below _ _ (below hpm2) _ _)))
    · -- cut `|X|+3`, column `|X|+2`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := a_A19 X Y m d hW hu hp hb hpm
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have htt : t = false := by rw [hpe, B7] at hb; exact hb
          exact Or.inl (chainT 3 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B8] at hb; exact hb
          exact Or.inr (Or.inl (chainC 6 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
        · have hd : d = true := by rw [hpe, B9] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 0 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := a_A22 X Y m d hm hW hu hp hb (by omega)
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_below _ _ (below hpm2) _ _)))
  · -- rightward pieces
    rw [block_col_true hu hp hb, a_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · -- cut `|X|`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := a_A1 X Y m d hW hu hp hb hpm
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
      · -- `p = m − 1`: the entry of the through-strand
        have htt : t = true := by rw [← hpe] at hb; rw [← ht]; exact hb
        exact Or.inl (chainT 0 (by norm_num) (by rw [hu, ← hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := a_A2 X Y m d hW hu hp hb hpm
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp (by omega) (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_slant _ _ (slant (by omega)))))
    · -- cut `|X|+1`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := a_A3 X Y m d hW hu hp hb (by omega)
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = true := by rw [hpe, B1] at hb; exact hb
          exact Or.inr (Or.inl (chainC 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
        · have hd : d = false := by rw [hpe, B2] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
        · have htt : t = true := by rw [hpe, B3] at hb; exact hb
          exact Or.inl (chainT 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := a_A6 X Y m d hW hu hp hb hpm2
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_below _ _ (below hpm2) _ _)))
    · -- cut `|X|+2`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := a_A7 X Y m d hW hu hp hb hpm
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hd : d = true := by rw [hpe, B4] at hb; exact hb
          exact Or.inr (Or.inl (chainC 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hd, by norm_num⟩)))
        · have htt : t = true := by rw [hpe, B5] at hb; exact hb
          exact Or.inl (chainT 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
        · have hd : d = false := by rw [hpe, B6] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hd, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := a_A10 X Y m d hm hW hu hp hb (by omega)
        exact Or.inr (Or.inr (a_spec X Y m d hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIL_out_below _ _ (below hpm2) _ _)))

end TypeIIaSpec

/-! #### F5. The type-II variant (a): the remaining specification fields -/

section TypeIIaSpec2

open U3

variable (X Y : Word) (m : ℕ) (d t : Bool) (hm : 2 ≤ m)
  (hW : (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y) X.length (m - 1) = t)

local notation "Va" => X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y
local notation "Pa" => [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)]
local notation "Va'" => X ++ [Letter.l m d] ++ Y
local notation "Pa'" => [Letter.l m d]
local notation "hA" => (-(m : ℝ) + 1)

include hm hW ht

theorem aT_slot_ne : ∀ j j', j ≤ 3 → j' ≤ 3 → j ≠ j' → (aT X Y m d t hm hW).slot hW j ≠ (aT X Y m d t hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [aT_slot_val X Y m d t hm hW ht j hj, aT_slot_val X Y m d t hm hW ht j' hj'] at h'
  cases t
  · simp only [tvTd, Bool.false_eq_true, ↓reduceIte] at h'
    have := tvT_inj X m (3 - j) (3 - j') (by omega) (by omega) h'
    omega
  · simp only [tvTd, ↓reduceIte] at h'
    exact hne (tvT_inj X m j j' hj hj' h')

theorem aC_slot_ne : ∀ j j', j ≤ 6 → j' ≤ 6 → j ≠ j' → (aC X Y m d hm hW).slot hW j ≠ (aC X Y m d hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [aC_slot_val X Y m d t hm hW ht j hj, aC_slot_val X Y m d t hm hW ht j' hj'] at h'
  cases d
  · simp only [tvCd, Bool.false_eq_true, ↓reduceIte] at h'
    have := tvC_inj X m hm (6 - j) (6 - j') (by omega) (by omega) h'
    omega
  · simp only [tvCd, ↓reduceIte] at h'
    exact hne (tvC_inj X m hm j j' hj hj' h')

theorem a_disj : ∀ j j', j ≤ 3 → j' ≤ 6 → (aT X Y m d t hm hW).slot hW j ≠ (aC X Y m d hm hW).slot hW j' := by
  intro j j' hj hj' h
  have h' := congrArg Subtype.val h
  rw [aT_slot_val X Y m d t hm hW ht j hj, aC_slot_val X Y m d t hm hW ht j' hj'] at h'
  cases t <;> cases d <;> simp only [tvTd, tvCd, Bool.false_eq_true, ↓reduceIte] at h' <;>
    exact tvT_ne_tvC X m hm _ _ (by omega) (by omega) h'

theorem a_prevOut₁ : Unch .std hW (aMv X Y m d) (prev hW (aT X Y m d t hm hW).u₀) ∧
    PieceOut (tIIL X.length hA) hW (ptv .std) (prev hW (aT X Y m d t hm hW).u₀) := by
  rcases a_rest X Y m d t hm hW ht (prev hW (aT X Y m d t hm hW).u₀) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · exfalso
    have hj' : j < 3 := hj
    have : (aT X Y m d t hm hW).slot hW (j + 1) = (aT X Y m d t hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact aT_slot_ne X Y m d t hm hW ht (j + 1) 0 (by omega) (by omega) (by omega) this
  · exfalso
    have hj' : j < 6 := hj
    have : (aC X Y m d hm hW).slot hW (j + 1) = (aT X Y m d t hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact a_disj X Y m d t hm hW ht 0 (j + 1) (by omega) (by omega) this.symm
  · exact h

theorem a_stopOut₁ : Unch .std hW (aMv X Y m d) ((aT X Y m d t hm hW).slot hW 3) ∧
    PieceOut (tIIL X.length hA) hW (ptv .std) ((aT X Y m d t hm hW).slot hW 3) := by
  rcases a_rest X Y m d t hm hW ht ((aT X Y m d t hm hW).slot hW 3) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · have hj' : j < 3 := hj
    exact absurd hjs (aT_slot_ne X Y m d t hm hW ht j 3 (by omega) le_rfl (by omega))
  · have hj' : j < 6 := hj
    exact absurd hjs.symm (a_disj X Y m d t hm hW ht 3 j le_rfl (by omega))
  · exact h

theorem a_prevOut₂ : Unch .std hW (aMv X Y m d) (prev hW (aC X Y m d hm hW).u₀) ∧
    PieceOut (tIIL X.length hA) hW (ptv .std) (prev hW (aC X Y m d hm hW).u₀) := by
  rcases a_rest X Y m d t hm hW ht (prev hW (aC X Y m d hm hW).u₀) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · exfalso
    have hj' : j < 3 := hj
    have : (aT X Y m d t hm hW).slot hW (j + 1) = (aC X Y m d hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact a_disj X Y m d t hm hW ht (j + 1) 0 (by omega) (by omega) this
  · exfalso
    have hj' : j < 6 := hj
    have : (aC X Y m d hm hW).slot hW (j + 1) = (aC X Y m d hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact aC_slot_ne X Y m d t hm hW ht (j + 1) 0 (by omega) (by omega) (by omega) this
  · exact h

theorem a_stopOut₂ : Unch .std hW (aMv X Y m d) ((aC X Y m d hm hW).slot hW 6) ∧
    PieceOut (tIIL X.length hA) hW (ptv .std) ((aC X Y m d hm hW).slot hW 6) := by
  rcases a_rest X Y m d t hm hW ht ((aC X Y m d hm hW).slot hW 6) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · have hj' : j < 3 := hj
    exact absurd hjs (a_disj X Y m d t hm hW ht j 6 (by omega) le_rfl)
  · have hj' : j < 6 := hj
    exact absurd hjs (aC_slot_ne X Y m d t hm hW ht j 6 (by omega) le_rfl (by omega))
  · exact h

omit hW ht in
/-- a grid point of the disc is a vertex of one of the two arcs -/
theorem a_vertex_of_mem {u : Slot Va} (hmem : pt .std Va u.1 ∈ polygon (tIIL X.length hA)) :
    (∃ i, i ≤ 3 ∧ u.1 = tvT X.length m i) ∨ (∃ i, i ≤ 6 ∧ u.1 = tvC X.length m i) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu] at hmem
  by_cases hp : p = 0
  · subst hp
    rw [std_pt_cusp] at hmem
    obtain ⟨b1, b2, -, -, -⟩ := tIIL_mem_bounds X.length hA hmem
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
    obtain ⟨b1, b2, b3, b4, b5⟩ := tIIL_mem_bounds X.length hA hmem
    have e1 : X.length ≤ j := by exact_mod_cast b1
    have e2 : j ≤ X.length + 3 := by exact_mod_cast (by linarith : (j : ℝ) ≤ X.length + 3)
    have e3 : 2 * p ≤ 2 * m + 3 := by exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 2 * m + 3)
    have e4 : 4 * m ≤ 4 * p + 7 := by exact_mod_cast (by linarith : (4 * m : ℝ) ≤ 4 * p + 7)
    have e5 : 4 * p + 1 + 8 * X.length ≤ 4 * m + 8 * j := by
      exact_mod_cast (by linarith : (4 * p + 1 + 8 * X.length : ℝ) ≤ 4 * m + 8 * j)
    have hj : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    have hpp : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · have : p = m - 1 := by omega
      exact Or.inl ⟨0, by norm_num, by rw [hu, this]; rfl⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inr ⟨4, by norm_num, hu⟩
      · exact Or.inr ⟨2, by norm_num, hu⟩
      · exact Or.inl ⟨1, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inr ⟨5, by norm_num, hu⟩
      · exact Or.inl ⟨2, by norm_num, hu⟩
      · exact Or.inr ⟨1, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inl ⟨3, by norm_num, hu⟩
      · exact Or.inr ⟨6, by norm_num, hu⟩
      · exact Or.inr ⟨0, by norm_num, hu⟩

theorem a_touch : ∀ u : Slot Va, PieceOut (tIIL X.length hA) hW (ptv .std) u → pt .std Va u.1 ∈ polygon (tIIL X.length hA) →
    u = (aT X Y m d t hm hW).slot hW 3 ∨ u = (aC X Y m d hm hW).slot hW 6 := by
  intro u hout hmem
  have hchainT : ∀ j', j' < 3 → u ≠ (aT X Y m d t hm hW).slot hW j' := by
    intro j' hj' he
    rw [he] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (aT_chain_in X Y m d t hm hW ht j' hj').2
  have hchainC : ∀ j', j' < 6 → u ≠ (aC X Y m d hm hW).slot hW j' := by
    intro j' hj' he
    rw [he] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (aC_chain_in X Y m d t hm hW ht j' hj').2
  rcases a_vertex_of_mem X Y m d hm hmem with ⟨i, hi, hu⟩ | ⟨i, hi, hu⟩
  · left
    have hs := aT_slot_val X Y m d t hm hW ht
    cases t
    · have hu' : u = (aT X Y m d false hm hW).slot hW (3 - i) := by
        apply Subtype.ext
        rw [hs (3 - i) (by omega), hu]
        simp only [tvTd, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact hu'
      · exact absurd hu' (hchainT (3 - i) (by omega))
    · have hu' : u = (aT X Y m d true hm hW).slot hW i := by
        apply Subtype.ext
        rw [hs i hi, hu]
        simp only [tvTd, ↓reduceIte]
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact absurd hu' (hchainT i h3)
      · have : i = 3 := by omega
        subst this
        exact hu'
  · right
    have hs := aC_slot_val X Y m d t hm hW ht
    cases d
    · have hu' : u = (aC X Y m false hm hW).slot hW (6 - i) := by
        apply Subtype.ext
        rw [hs (6 - i) (by omega), hu]
        simp only [tvCd, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact hu'
      · exact absurd hu' (hchainC (6 - i) (by omega))
    · have hu' : u = (aC X Y m true hm hW).slot hW i := by
        apply Subtype.ext
        rw [hs i hi, hu]
        simp only [tvCd, ↓reduceIte]
      rcases Nat.lt_or_ge i 6 with h6 | h6
      · exact absurd hu' (hchainC i h6)
      · have : i = 6 := by omega
        subst this
        exact hu'

omit hm ht in
theorem a_exits : ∀ u : Slot Va, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch .std hW (aMv X Y m d) v ∧
    PieceOut (tIIL X.length hA) hW (ptv .std) v := by
  intro u
  have hno : ∀ k', X.length ≤ k' → k' < X.length + 3 → ∀ m', letterAt Va k' ≠ .r m' := by
    intro k' h1 h2 m'
    obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
    have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [hℓ₀]; exact fun h => by cases h
    · rw [hℓ₁]; exact fun h => by cases h
    · rw [hℓ₂]; exact fun h => by cases h
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_r hW X.length (X.length + 3) hno u
  exact ⟨v, hsc, unch_of_extCol .std hW _ (a_hmv X Y m d) hcol,
    pieceOut_of_extCol _ .std hW _ (tIIL_xge_mem _ _) (tIIL_xle_mem _ _) (unch_pt _ _ _) hcol⟩

omit hm hW ht in
/-- the crossing letters of the block: `σ_m` at column `|X|+1`, `σ_{m−1}` at column `|X|+2` -/
theorem a_σcol {k' m' : ℕ} (hℓ : letterAt Va k' = .σ m') (hext : ¬ ExtCol X Pa k') :
    (k' = X.length + 1 ∧ m = m') ∨ (k' = X.length + 2 ∧ m' = m - 1) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
  rw [a_extCol] at hext
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀] at hℓ; cases hℓ
  · rw [hℓ₁] at hℓ; exact Or.inl ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [hℓ₂] at hℓ; exact Or.inr ⟨rfl, (Letter.σ.inj hℓ).symm⟩

/-- the over strand of each block crossing lies on the cusp arc -/
theorem a_σA_chain {k' m' : ℕ} (hk : k' < (Va).length) (hℓ : letterAt Va k' = .σ m') (hext : ¬ ExtCol X Pa k') :
    OnChain hW (aC X Y m d hm hW) (σSlotA hW hk hℓ) := by
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  have hv := σSlotA_val hW hk hℓ
  rcases a_σcol X Y m d hℓ hext with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [B2] at hv
    cases d
    · simp only [Bool.not_false, ↓reduceIte] at hv
      exact aC_chain_of X Y m false t hm hW ht 2 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
      exact aC_chain_of X Y m true t hm hW ht 1 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · rw [B4] at hv
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      rw [show m - 1 + 1 = m by omega] at hv
      exact aC_chain_of X Y m false t hm hW ht 6 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact aC_chain_of X Y m true t hm hW ht 5 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

theorem a_hK : ∀ (k' m' : ℕ) (hk : k' < (Va).length) (hℓ : letterAt Va k' = .σ m'),
    ExtCol X Pa k' ↔ Unch .std hW (aMv X Y m d) (σSlotA hW hk hℓ) ∧ Unch .std hW (aMv X Y m d) (σSlotB hW hk hℓ) := by
  intro k' m' hk hℓ
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  constructor
  · intro hext
    have hext' := (a_extCol X m d k').1 hext
    exact ⟨unch_of_extCol .std hW _ (a_hmv X Y m d) (by rw [(σSlotA_spec hW hk hℓ).1]; exact hext'),
      unch_of_extCol .std hW _ (a_hmv X Y m d) (by rw [(σSlotB_spec hW hk hℓ).1]; exact hext')⟩
  · rintro ⟨-, hB⟩
    by_contra hext
    have hv := σSlotB_val hW hk hℓ
    rcases a_σcol X Y m d hℓ hext with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- column `|X|+1`: the under slot is a moved through-vertex
      rw [B3] at hv
      have h1 := hB.1
      cases t
      · simp only [Bool.false_eq_true, ↓reduceIte] at hv
        have hv' : (σSlotB hW hk hℓ).1 = tvT X.length m 2 := hv
        rw [a_mv_T X Y m d hm 2 (by norm_num) _ hv', hv', a_pt_T X Y m d hm 2 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvA, pvA] at this
        linarith
      · simp only [↓reduceIte] at hv
        have hv' : (σSlotB hW hk hℓ).1 = tvT X.length m 1 := hv
        rw [a_mv_T X Y m d hm 1 (by norm_num) _ hv', hv', a_pt_T X Y m d hm 1 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvA, pvA] at this
        linarith
    · -- column `|X|+2`
      rw [show m - 1 + 1 = m by omega, B5] at hv
      cases t
      · simp only [Bool.false_eq_true, ↓reduceIte] at hv
        have h2 := hB.2
        have hn : (next hW (σSlotB hW hk hℓ)).1 = tvT X.length m 2 := a_A20 X Y m d hm hW hv B7
        rw [a_mv_T X Y m d hm 2 (by norm_num) _ hn, hn, a_pt_T X Y m d hm 2 (by norm_num)] at h2
        have := congrArg Prod.snd h2
        simp only [mvA, pvA] at this
        linarith
      · simp only [↓reduceIte] at hv
        have h1 := hB.1
        have hv' : (σSlotB hW hk hℓ).1 = tvT X.length m 2 := hv
        rw [a_mv_T X Y m d hm 2 (by norm_num) _ hv', hv', a_pt_T X Y m d hm 2 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvA, pvA] at this
        linarith

theorem a_hKout : ∀ (k' m' : ℕ) (hk : k' < (Va).length) (hℓ : letterAt Va k' = .σ m'),
    ExtCol X Pa k' ↔ PieceOut (tIIL X.length hA) hW (ptv .std) (σSlotA hW hk hℓ) := by
  intro k' m' hk hℓ
  constructor
  · intro hext
    exact pieceOut_of_extCol _ .std hW _ (tIIL_xge_mem _ _) (tIIL_xle_mem _ _) (unch_pt _ _ _)
      (by rw [(σSlotA_spec hW hk hℓ).1]; exact (a_extCol X m d k').1 hext)
  · intro hout
    by_contra hext
    obtain ⟨j, hj, hjs⟩ := a_σA_chain X Y m d t hm hW ht hk hℓ hext
    have hj' : j < 6 := hj
    rw [← hjs] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (aC_chain_in X Y m d t hm hW ht j hj').2

theorem a_cross : ∃ (k₁ m₁ : ℕ) (hk₁ : k₁ < (Va).length) (hℓ₁ : letterAt Va k₁ = .σ m₁) (k₂ m₂ : ℕ) (hk₂ : k₂ < (Va).length)
    (hℓ₂ : letterAt Va k₂ = .σ m₂), k₁ ≠ k₂ ∧ ¬ ExtCol X Pa k₁ ∧ ¬ ExtCol X Pa k₂ ∧
    (∀ (kk mm : ℕ) (_hk : kk < (Va).length) (_hℓ : letterAt Va kk = .σ mm), ¬ ExtCol X Pa kk → kk = k₁ ∨ kk = k₂) ∧
    ((OnChain hW (aT X Y m d t hm hW) (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW (aT X Y m d t hm hW) (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW (aC X Y m d hm hW) (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW (aC X Y m d hm hW) (σSlotB hW hk₂ hℓ₂)) ∨
     (OnChain hW (aC X Y m d hm hW) (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW (aC X Y m d hm hW) (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW (aT X Y m d t hm hW) (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW (aT X Y m d t hm hW) (σSlotB hW hk₂ hℓ₂))) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := a_letters X Y m d
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := a_bits X Y m d t hm hW ht
  have hk₁ : X.length + 1 < (Va).length := by rw [a_length]; omega
  have hk₂ : X.length + 2 < (Va).length := by rw [a_length]; omega
  have hext₁ : ¬ ExtCol X Pa (X.length + 1) := by rw [a_extCol]; omega
  have hext₂ : ¬ ExtCol X Pa (X.length + 2) := by rw [a_extCol]; omega
  refine ⟨X.length + 1, m, hk₁, hℓ₁, X.length + 2, m - 1, hk₂, hℓ₂, by omega, hext₁, hext₂, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · intro kk mm _ hℓ hext
    rcases a_σcol X Y m d hℓ hext with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · exact a_σA_chain X Y m d t hm hW ht hk₁ hℓ₁ hext₁
  · exact a_σA_chain X Y m d t hm hW ht hk₂ hℓ₂ hext₂
  · have hv := σSlotB_val hW hk₁ hℓ₁
    rw [B3] at hv
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact aT_chain_of X Y m d false hm hW ht 2 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact aT_chain_of X Y m d true hm hW ht 1 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · have hv := σSlotB_val hW hk₂ hℓ₂
    rw [show m - 1 + 1 = m by omega, B5] at hv
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact aT_chain_of X Y m d false hm hW ht 3 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact aT_chain_of X Y m d true hm hW ht 2 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

/-- pieces of the through-strand never share a column -/
theorem a_pairs_TT : ∀ j j', j < 3 → j' < 3 → j ≠ j' →
    colOf ((aT X Y m d t hm hW).slot hW j) = colOf ((aT X Y m d t hm hW).slot hW j') → False := by
  intro j j' hj hj' hjj hc
  rw [aT_col X Y m d t hm hW ht j hj, aT_col X Y m d t hm hW ht j' hj'] at hc
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc
    interval_cases j <;> interval_cases j' <;> first | exact hjj rfl | (norm_num [colT] at hc <;> omega)
  · simp only [↓reduceIte] at hc
    interval_cases j <;> interval_cases j' <;> first | exact hjj rfl | (norm_num [colT] at hc <;> omega)

/-- the same-column pairs of a through-piece and a cusp-arc piece -/
theorem a_pairs_TC : ∀ j j', j < 3 → j' < 6 →
    colOf ((aT X Y m d t hm hW).slot hW j) = colOf ((aC X Y m d hm hW).slot hW j') →
    MeetSpec .std hW (aMv X Y m d) (ExtCol X Pa) ((aT X Y m d t hm hW).slot hW j) ((aC X Y m d hm hW).slot hW j') := by
  intro j j' hj hj' hc
  rw [aT_col X Y m d t hm hW ht j hj, aC_col X Y m d t hm hW ht j' hj'] at hc
  have hnT := aT_next_slot X Y m d t hm hW
  have hnC := aC_next_slot X Y m d hm hW
  have hmvT := aT_mv_slot X Y m d t hm hW ht
  have hmvC := aC_mv_slot X Y m d t hm hW ht
  cases t <;> cases d
  · -- `t = false`, `d = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 0 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (aII_NM_T2C5 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 5 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (aII_NM_T2C0 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (aII_NM_T1C4 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (aII_NM_T1C1 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 2 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (aII_NM_T0C3 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 3 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (aII_NM_T0C2 _ _).revl.revr
  · -- `t = false`, `d = true`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 0 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (aII_NM_T2C0 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 5 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (aII_NM_T2C5 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (aII_NM_T1C1 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (aII_NM_T1C4 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 2 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (aII_NM_T0C2 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 3 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (aII_NM_T0C3 _ _).revl
  · -- `t = true`, `d = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 2 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (aII_NM_T0C3 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 3 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (aII_NM_T0C2 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (aII_NM_T1C4 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (aII_NM_T1C1 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 0 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (aII_NM_T2C5 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 5 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (aII_NM_T2C0 _ _).revr
  · -- `t = true`, `d = true`
    simp only [↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 2 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (aII_NM_T0C2 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 3 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (aII_NM_T0C3 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (aII_NM_T1C1 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (aII_NM_T1C4 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 0 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (aII_NM_T2C0 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 5 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (aII_NM_T2C5 _ _)

/-- the same-column pairs of two cusp-arc pieces -/
theorem a_pairs_CC : ∀ j j', j < 6 → j' < 6 → j ≠ j' →
    colOf ((aC X Y m d hm hW).slot hW j) = colOf ((aC X Y m d hm hW).slot hW j') →
    MeetSpec .std hW (aMv X Y m d) (ExtCol X Pa) ((aC X Y m d hm hW).slot hW j) ((aC X Y m d hm hW).slot hW j') := by
  intro j j' hj hj' hjj hc
  rw [aC_col X Y m d t hm hW ht j hj, aC_col X Y m d t hm hW ht j' hj'] at hc
  have hn := aC_next_slot X Y m d hm hW
  have hmv := aC_mv_slot X Y m d t hm hW ht
  cases d
  · -- `d = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact (aII_NM_C0C5 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (aII_NM_C1C4 _ _).symm.revl.revr
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (aII_OJ234 _ _).rev
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (aII_OJ234 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (aII_NM_C1C4 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (aII_NM_C0C5 _ _).revl.revr
  · -- `d = true`
    simp only [↓reduceIte] at hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [colC] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact aII_NM_C0C5 _ _
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact aII_NM_C1C4 _ _
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact aII_OJ234 _ _
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact aII_OJ234 _ _
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (aII_NM_C1C4 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (aII_NM_C0C5 _ _).symm

theorem a_pairs : ∀ u v : Slot Va, (OnChain hW (aT X Y m d t hm hW) u ∨ OnChain hW (aC X Y m d hm hW) u) →
    (OnChain hW (aT X Y m d t hm hW) v ∨ OnChain hW (aC X Y m d hm hW) v) →
    u ≠ v → colOf u = colOf v → MeetSpec .std hW (aMv X Y m d) (ExtCol X Pa) u v := by
  intro u v hu hv hne hc
  rcases hu with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> rcases hv with ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩
  · exact (a_pairs_TT X Y m d t hm hW ht j j' hj hj' (fun h => hne (by rw [h])) hc).elim
  · exact a_pairs_TC X Y m d t hm hW ht j j' hj hj' hc
  · exact (a_pairs_TC X Y m d t hm hW ht j' j hj' hj hc.symm).symm
  · exact a_pairs_CC X Y m d t hm hW ht j j' hj hj' (fun h => hne (by rw [h])) hc

theorem a_genericData : GenericData .std hW (aMv X Y m d) (ExtCol X Pa) :=
  genericData_of' (tIIL X.length hA) .std hW (aMv X Y m d) (ExtCol X Pa)
    (fun u => OnChain hW (aT X Y m d t hm hW) u ∨ OnChain hW (aC X Y m d hm hW) u)
    (mvIIa_injective _ _ _ m) (mvIIa_xcoord _ _ _ _ (by omega))
    (fun u => by
      rcases a_rest X Y m d t hm hW ht u with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h)
    (fun u hu => by
      rcases hu with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact (aT_chain_in X Y m d t hm hW ht j hj).1
      · exact (aC_chain_in X Y m d t hm hW ht j hj).1)
    (a_pairs X Y m d t hm hW ht)
    (fun k' m' hk hℓ hA' hB => (a_hK X Y m d t hm hW ht k' m' hk hℓ).2 ⟨hA', hB⟩)

theorem a_riiSpec : RIISpec (tIIL X.length hA) .std hW (aMv X Y m d) (ExtCol X Pa) (aT X Y m d t hm hW) (aC X Y m d hm hW) where
  disc := tIIL_isDisc _ _
  hK := a_hK X Y m d t hm hW ht
  hKout := a_hKout X Y m d t hm hW ht
  moved := a_moved X Y m d hm
  chain₁ := aT_chain_in X Y m d t hm hW ht
  chain₂ := aC_chain_in X Y m d t hm hW ht
  vert₁ := aT_vert X Y m d t hm hW ht
  vert₂ := aC_vert X Y m d t hm hW ht
  rest := a_rest X Y m d t hm hW ht
  prevOut₁ := a_prevOut₁ X Y m d t hm hW ht
  stopOut₁ := a_stopOut₁ X Y m d t hm hW ht
  prevOut₂ := a_prevOut₂ X Y m d t hm hW ht
  stopOut₂ := a_stopOut₂ X Y m d t hm hW ht
  disj := fun j hj j' hj' => a_disj X Y m d t hm hW ht j j' (Nat.le_of_lt hj) (Nat.le_of_lt hj')
  touch := a_touch X Y m d t hm hW ht
  exits := a_exits X Y m d hW
  cross := a_cross X Y m d t hm hW ht

theorem a_riiData (hne : Va ≠ []) :
    Nonempty (RIIData (polygon (tIIL X.length hA))
      (mvDiagram .std hW hne (aMv X Y m d) (ExtCol X Pa) (a_genericData X Y m d t hm hW ht)) (rlDiagram .std hW hne)) :=
  riiData_of hne (a_genericData X Y m d t hm hW ht) (a_riiSpec X Y m d t hm hW ht)

theorem a_recordIso (hne : Va ≠ []) (W' : OWord) (hW'eq : W'.letters = Va') :
    Nonempty (RecordIso (mvDiagram .std hW hne (aMv X Y m d) (ExtCol X Pa) (a_genericData X Y m d t hm hW ht)).record
      (realize W').diagram.record) := by
  have hW' : (Va').Closed := by have := W'.closed; rwa [hW'eq] at this
  refine ⟨vertexMovedRecordIso' X Pa Y Pa' (by simp) (a_sameEffect X Y m d hm hW) hW hW' .std hne _ _ _ _
    (slotDiagramData_of .std hW hne (aMv X Y m d) (ExtCol X Pa) (a_genericData X Y m d t hm hW ht) (a_hK X Y m d t hm hW ht))
    (a_passage X Y m d hm hW hW') (a_hexit X Y m d hW) (a'_hexit X Y m d hW') ?_ W' hW'eq (by simp)⟩
  intro k' hk1 hk2
  simp only [List.length_cons, List.length_nil] at hk2
  have : k' = X.length := by omega
  subst this
  rw [a'_letters X Y m d]; rfl

omit hW ht in
/-- LEAF CASE (type II, variant (a): `l_{m−1} d σ_m σ_{m−1} ↦ l_m d`). -/
theorem typeII_a {W W' : OWord} (hWeq : W.letters = Va) (hW'eq : W'.letters = Va') :
    ∃ D : Diagram, RII D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨Wl, hWl⟩ := W
  simp only at hWeq
  subst hWeq
  have hne : Va ≠ [] := by simp
  rw [realize_eq_realizeAt ⟨_, hWl⟩ hne]
  exact ⟨mvDiagram .std hWl hne (aMv X Y m d) (ExtCol X Pa) (a_genericData X Y m d _ hm hWl rfl),
    ⟨polygon (tIIL X.length hA), Or.inl (a_riiData X Y m d _ hm hWl rfl hne)⟩,
    a_recordIso X Y m d _ hm hWl rfl hne W' hW'eq⟩

end TypeIIaSpec2

/-! #### G1. The type-II variant (c): `σ_{m−1} σ_m r_{m−1} ↦ r_m`, the word level -/

/-- the through-strand's vertices (entry at cut `k`, index `m−1`): under both crossings, out at `(k+3, m−1)` -/
def tvT2 (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k, m - 1)
  | 1 => (k + 1, m)
  | 2 => (k + 2, m + 1)
  | _ => (k + 3, m - 1)

/-- the cusp arc's vertices, from the upper arm `(k, m)` through the right cusp to the lower arm `(k, m+1)` -/
def tvC2 (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k, m)
  | 1 => (k + 1, m - 1)
  | 2 => (k + 2, m - 1)
  | 3 => (k + 2, 0)
  | 4 => (k + 2, m)
  | 5 => (k + 1, m + 1)
  | _ => (k, m + 1)

def tvTd2 (k m : ℕ) (t : Bool) (j : ℕ) : ℕ × ℕ := if t then tvT2 k m j else tvT2 k m (3 - j)
def tvCd2 (k m : ℕ) (e : Bool) (j : ℕ) : ℕ × ℕ := if e then tvC2 k m j else tvC2 k m (6 - j)

/-- the columns of the six cusp-arc pieces -/
def colC2 (k : ℕ) : ℕ → ℕ
  | 0 => k
  | 1 => k + 1
  | 2 => k + 2
  | 3 => k + 2
  | 4 => k + 1
  | _ => k

section TypeIIcWord

open U3

variable (X Y : Word) (m : ℕ) (t e : Bool) (hm : 2 ≤ m)
  (hW : (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y) X.length (m - 1) = t)
  (he : bit (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y) (X.length + 2) (m - 1) = e)

local notation "Vc" => X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y
local notation "Pc" => [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)]
local notation "Vc'" => X ++ [Letter.r m] ++ Y
local notation "Pc'" => [Letter.r m]

theorem c_letters : letterAt Vc X.length = .σ (m - 1) ∧ letterAt Vc (X.length + 1) = .σ m ∧
    letterAt Vc (X.length + 2) = .r (m - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have := letterAt_block X Pc Y (i := 0) (by simp); simpa using this
  · have := letterAt_block X Pc Y (i := 1) (by simp); simpa using this
  · have := letterAt_block X Pc Y (i := 2) (by simp); simpa using this

theorem c_length : (Vc).length = X.length + 3 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem c'_letters : letterAt Vc' X.length = .r m := by
  have := letterAt_block X Pc' Y (i := 0) (by simp); simpa using this

theorem c'_length : (Vc').length = X.length + 1 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem c_extCol (k : ℕ) : ExtCol X Pc k ↔ k + 1 ≤ X.length ∨ X.length + 3 ≤ k := by
  unfold ExtCol; simp

theorem c'_extCol (k : ℕ) : ExtCol X Pc' k ↔ k + 1 ≤ X.length ∨ X.length + 1 ≤ k := by
  unfold ExtCol; simp

theorem c_shift : shiftIdx X Pc Pc' (X.length + 3) = X.length + 1 := by
  unfold shiftIdx; simp

theorem c_cut_start : cut Vc' X.length = cut Vc X.length := by
  unfold cut
  rw [List.append_assoc, List.take_left' rfl, List.append_assoc, List.take_left' rfl]

theorem c_bit_start (p : ℕ) : bit Vc' X.length p = bit Vc X.length p := by
  rw [bit_eq, bit_eq, c_cut_start]

include hW

include hm in
theorem c_sameEffect : SameEffect X Pc Pc' :=
  sameEffect_of_replace X Pc Y Pc' hW (fun c c' h => run_typeII_r_left hm h)

include hm in
theorem c_cut_end : cut Vc' (X.length + 1) = cut Vc (X.length + 3) := by
  have hE := c_sameEffect X Y m hm hW
  unfold SameEffect at hE
  unfold cut
  rw [List.take_left' (by simp), List.take_left' (by simp), hE]

include hm in
theorem c_bit_end (p : ℕ) : bit Vc' (X.length + 1) p = bit Vc (X.length + 3) p := by
  rw [bit_eq, bit_eq, c_cut_end X Y m hm hW]

theorem c_cutlen : m + 1 ≤ (cut Vc (X.length + 1)).length ∧ (cut Vc X.length).length = (cut Vc (X.length + 1)).length ∧
    (cut Vc (X.length + 2)).length = (cut Vc (X.length + 1)).length ∧
    (cut Vc (X.length + 3)).length + 2 = (cut Vc (X.length + 2)).length := by
  have hk₀ : X.length < (Vc).length := by rw [c_length]; omega
  have hk₁ : X.length + 1 < (Vc).length := by rw [c_length]; omega
  have hk₂ : X.length + 2 < (Vc).length := by rw [c_length]; omega
  obtain ⟨-, -, h3, -, -⟩ := σ_facts hW hk₀ (c_letters X Y m).1
  obtain ⟨-, h2', h3', -, -⟩ := σ_facts hW hk₁ (c_letters X Y m).2.1
  obtain ⟨D⟩ := decomp hW (X.length + 2) hk₂
  have h1 := D.length_add
  have har : (letterAt Vc (X.length + 2)).arity = 2 := by rw [(c_letters X Y m).2.2]; rfl
  have hco : (letterAt Vc (X.length + 2)).coarity = 0 := by rw [(c_letters X Y m).2.2]; rfl
  rw [har, hco, show X.length + 2 + 1 = X.length + 3 from rfl] at h1
  exact ⟨h2', h3.symm, h3', by omega⟩

include hm ht he in
/-- the bits: the cusp arms carry `e`, `!e`; the through-strand carries `t` -/
theorem c_bits :
    bit Vc X.length m = e ∧ bit Vc X.length (m + 1) = !e ∧
    bit Vc (X.length + 1) (m - 1) = e ∧ bit Vc (X.length + 1) m = t ∧ bit Vc (X.length + 1) (m + 1) = !e ∧
    bit Vc (X.length + 2) m = !e ∧ bit Vc (X.length + 2) (m + 1) = t ∧ bit Vc (X.length + 3) (m - 1) = t := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
  have hk₀ : X.length < (Vc).length := by rw [c_length]; omega
  have hk₁ : X.length + 1 < (Vc).length := by rw [c_length]; omega
  have hk₂ : X.length + 2 < (Vc).length := by rw [c_length]; omega
  obtain ⟨-, -, -, h4, h5⟩ := σ_facts hW hk₀ hℓ₀
  obtain ⟨-, -, -, h4', h5'⟩ := σ_facts hW hk₁ hℓ₁
  obtain ⟨-, hr⟩ := r_bits hW hk₂ hℓ₂
  rw [show m - 1 + 1 = m by omega] at h4 h5 hr
  have C7 : bit Vc (X.length + 2) m = !e := by
    rw [he] at hr
    exact U3.bool_eq_not_of_ne (Ne.symm hr)
  have C3 : bit Vc (X.length + 1) (m - 1) = e := by
    rw [← he, bit_succ_of_lt hW hk₁ (by omega) (by rw [hℓ₁]; simp only [idx]; omega)]
  have C1 : bit Vc X.length m = e := by rw [← h5, C3]
  have C5 : bit Vc (X.length + 1) (m + 1) = !e := by rw [← h5', C7]
  have C2 : bit Vc X.length (m + 1) = !e := by
    have := bit_succ_of_ge hW hk₀ (p := m + 1) (by rw [hℓ₀]; simp only [idx, arity]; omega)
    rw [hℓ₀] at this
    simp only [coarity, arity] at this
    rw [show m + 1 + 2 - 2 = m + 1 by omega] at this
    rw [← this, C5]
  have C4 : bit Vc (X.length + 1) m = t := by rw [h4, ht]
  have C8 : bit Vc (X.length + 2) (m + 1) = t := by rw [h4', C4]
  have C9 : bit Vc (X.length + 3) (m - 1) = t := by
    have := bit_succ_of_ge hW hk₂ (p := m + 1) (by rw [hℓ₂]; simp only [idx, arity]; omega)
    rw [hℓ₂] at this
    simp only [coarity, arity] at this
    rw [show m + 1 + 0 - 2 = m - 1 by omega] at this
    rw [this, C8]
  exact ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩

/-! the successor table (columns `|X|`: `σ_{m−1}`, `|X|+1`: `σ_m`, `|X|+2`: `r_{m−1}`) -/

theorem c_A1 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc X.length p = true)
    (hpm : p < m - 1) : (next hW s).1 = (X.length + 1, p) ∧ bit Vc (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(c_letters X Y m).1]; exact hpm)

include hm in
theorem c_A2 {s : Slot Vc} (hs : s.1 = (X.length, m - 1)) (hb : bit Vc X.length (m - 1) = true) :
    (next hW s).1 = (X.length + 1, m) := by
  have := next_σ_right_idx hW (c_letters X Y m).1 hs hb
  rwa [show m - 1 + 1 = m by omega] at this

include hm in
theorem c_A3 {s : Slot Vc} (hs : s.1 = (X.length, m)) (hb : bit Vc X.length m = true) :
    (next hW s).1 = (X.length + 1, m - 1) :=
  next_σ_right_succ hW (c_letters X Y m).1 (by rw [hs, show m - 1 + 1 = m by omega])
    (by rw [show m - 1 + 1 = m by omega]; exact hb)

include hm in
theorem c_A4 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc X.length p = true)
    (hpm : m + 1 ≤ p) : (next hW s).1 = (X.length + 1, p) ∧ bit Vc (X.length + 1) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(c_letters X Y m).1]; simp only [idx, arity]; omega)
  rw [(c_letters X Y m).1] at this
  simpa [coarity, arity] using this

theorem c_A5 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 1) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vc (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(c_letters X Y m).2.1]; exact hpm)

theorem c_A6 {s : Slot Vc} (hs : s.1 = (X.length + 1, m)) (hb : bit Vc (X.length + 1) m = true) :
    (next hW s).1 = (X.length + 2, m + 1) :=
  next_σ_right_idx hW (c_letters X Y m).2.1 hs hb

theorem c_A7 {s : Slot Vc} (hs : s.1 = (X.length + 1, m + 1)) (hb : bit Vc (X.length + 1) (m + 1) = true) :
    (next hW s).1 = (X.length + 2, m) :=
  next_σ_right_succ hW (c_letters X Y m).2.1 hs hb

theorem c_A8 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 1) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vc (X.length + 2) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(c_letters X Y m).2.1]; simpa [idx, arity] using hpm)
  rw [(c_letters X Y m).2.1] at this
  simpa [coarity, arity] using this

theorem c_A9 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 2) p = true) (hpm : p < m - 1) :
    (next hW s).1 = (X.length + 3, p) ∧ bit Vc (X.length + 3) p = true :=
  next_right_lt hW hs hp hb (by rw [(c_letters X Y m).2.2]; exact hpm)

include hm in
theorem c_A10 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p = m - 1 ∨ p = m)
    (hb : bit Vc (X.length + 2) p = true) : (next hW s).1 = (X.length + 2, 0) :=
  next_arm_r hW (by have := slot_col_lt hW hs; omega) (c_letters X Y m).2.2 hs (by omega) hb

include hm in
theorem c_A11 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 2) p = true) (hpm : m + 1 ≤ p) :
    (next hW s).1 = (X.length + 3, p - 2) ∧ bit Vc (X.length + 3) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(c_letters X Y m).2.2]; simp only [idx, arity]; omega)
  rw [(c_letters X Y m).2.2] at this
  simpa [coarity, arity] using this

include hm he in
theorem c_A12 {s : Slot Vc} (hs : s.1 = (X.length + 2, 0)) :
    (next hW s).1 = (X.length + 2, if e then m else m - 1) := by
  rw [next_cusp_r hW (c_letters X Y m).2.2 hs, he]
  cases e <;> simp <;> omega

theorem c_A13 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 1) q = false) (hqm : q < m - 1) :
    (next hW s).1 = (X.length, q) ∧ bit Vc X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (c_letters X Y m).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

include hm in
theorem c_A14 {s : Slot Vc} (hs : s.1 = (X.length + 1, m - 1)) (hb : bit Vc (X.length + 1) (m - 1) = false) :
    (next hW s).1 = (X.length, m) := by
  have := next_σ_left_idx hW (c_letters X Y m).1 hs hb
  rwa [show m - 1 + 1 = m by omega] at this

include hm in
theorem c_A15 {s : Slot Vc} (hs : s.1 = (X.length + 1, m)) (hb : bit Vc (X.length + 1) m = false) :
    (next hW s).1 = (X.length, m - 1) :=
  next_σ_left_succ hW (c_letters X Y m).1 (by rw [hs, show m - 1 + 1 = m by omega])
    (by rw [show m - 1 + 1 = m by omega]; exact hb)

include hm in
theorem c_A16 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 1) q = false) (hqm : m + 1 ≤ q) :
    (next hW s).1 = (X.length, q) ∧ bit Vc X.length q = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (c_letters X Y m).1]; simp only [idx, coarity]; omega)
  rw [Nat.add_sub_cancel, (c_letters X Y m).1] at this
  simpa [arity, coarity] using this

theorem c_A17 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 2) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vc (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e2, (c_letters X Y m).2.1]; exact hqm)
  rwa [e2] at this

theorem c_A18 {s : Slot Vc} (hs : s.1 = (X.length + 2, m)) (hb : bit Vc (X.length + 2) m = false) :
    (next hW s).1 = (X.length + 1, m + 1) :=
  next_σ_left_idx hW (c_letters X Y m).2.1 hs hb

theorem c_A19 {s : Slot Vc} (hs : s.1 = (X.length + 2, m + 1)) (hb : bit Vc (X.length + 2) (m + 1) = false) :
    (next hW s).1 = (X.length + 1, m) :=
  next_σ_left_succ hW (c_letters X Y m).2.1 hs hb

theorem c_A20 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 2) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vc (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e2, (c_letters X Y m).2.1]; simpa [idx, coarity] using hqm)
  rw [e2, (c_letters X Y m).2.1] at this
  simpa [arity, coarity] using this

theorem c_A21 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 3) q = false) (hqm : q < m - 1) :
    (next hW s).1 = (X.length + 2, q) ∧ bit Vc (X.length + 2) q = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_lt hW hs hq hb (by rw [e3, (c_letters X Y m).2.2]; exact hqm)
  rwa [e3] at this

theorem c_A22 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 3) q = false) (hqm : m - 1 ≤ q) :
    (next hW s).1 = (X.length + 2, q + 2) ∧ bit Vc (X.length + 2) (q + 2) = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_ge hW hs hq hb (by rw [e3, (c_letters X Y m).2.2]; simp only [idx, coarity]; omega)
  rw [e3, (c_letters X Y m).2.2] at this
  simpa [arity, coarity] using this

theorem c_hexit : ∀ u : Slot Vc, ∃ n, ExtPiece X Pc Y ((next hW)^[n] u) := by
  apply hexit_of_no_l X Pc Y hW
  intro k' h1 h2 m' d'
  simp only [List.length_cons, List.length_nil] at h2
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀]; exact fun h => by cases h
  · rw [hℓ₁]; exact fun h => by cases h
  · rw [hℓ₂]; exact fun h => by cases h

/-! the two chains -/

include hm in
theorem c_isSlot_T0 : IsSlot Vc (tvTd2 X.length m t 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := c_cutlen X Y m hW
  have hlen := c_length X Y m
  cases t
  · have e : tvTd2 X.length m false 0 = (X.length + 3, m - 1) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)
  · have e : tvTd2 X.length m true 0 = (X.length, m - 1) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)

include hm in
theorem c_isSlot_C0 : IsSlot Vc (tvCd2 X.length m e 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := c_cutlen X Y m hW
  have hlen := c_length X Y m
  cases e
  · have e : tvCd2 X.length m false 0 = (X.length, m + 1) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)
  · have e : tvCd2 X.length m true 0 = (X.length, m) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)

include hm in
/-- the arc of the through-strand: three pieces -/
def cT : Chain Vc := ⟨⟨tvTd2 X.length m t 0, c_isSlot_T0 X Y m t hm hW⟩, 3, by norm_num⟩

include hm in
/-- the arc of the cusp: six pieces -/
def cC : Chain Vc := ⟨⟨tvCd2 X.length m e 0, c_isSlot_C0 X Y m e hm hW⟩, 6, by norm_num⟩

include hm ht he in
theorem cT_slot_val : ∀ j, j ≤ 3 → ((cT X Y m t hm hW).slot hW j).1 = tvTd2 X.length m t j := by
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  have s0 : ((cT X Y m t hm hW).slot hW 0).1 = tvTd2 X.length m t 0 := rfl
  intro j hj
  cases t
  · simp only [tvTd2, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((cT X Y m false hm hW).slot hW 1).1 = tvT2 X.length m 2 := by
      rw [Chain.slot_succ]
      have := (c_A22 X Y m hW s0 (by omega) C9 le_rfl).1
      rwa [show m - 1 + 2 = m + 1 by omega] at this
    have s2 : ((cT X Y m false hm hW).slot hW 2).1 = tvT2 X.length m 1 := by
      rw [Chain.slot_succ]; exact c_A19 X Y m hW s1 C8
    have s3 : ((cT X Y m false hm hW).slot hW 3).1 = tvT2 X.length m 0 := by
      rw [Chain.slot_succ]; exact c_A15 X Y m hm hW s2 C4
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
  · simp only [tvTd2, ↓reduceIte] at s0 ⊢
    have s1 : ((cT X Y m true hm hW).slot hW 1).1 = tvT2 X.length m 1 := by
      rw [Chain.slot_succ]; exact c_A2 X Y m hm hW s0 ht
    have s2 : ((cT X Y m true hm hW).slot hW 2).1 = tvT2 X.length m 2 := by
      rw [Chain.slot_succ]; exact c_A6 X Y m hW s1 C4
    have s3 : ((cT X Y m true hm hW).slot hW 3).1 = tvT2 X.length m 3 := by
      rw [Chain.slot_succ]
      have := (c_A11 X Y m hm hW s2 (by omega) C8 le_rfl).1
      rwa [show m + 1 - 2 = m - 1 by omega] at this
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3

include hm ht he in
theorem cC_slot_val : ∀ j, j ≤ 6 → ((cC X Y m e hm hW).slot hW j).1 = tvCd2 X.length m e j := by
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  have s0 : ((cC X Y m e hm hW).slot hW 0).1 = tvCd2 X.length m e 0 := rfl
  intro j hj
  cases e
  · simp only [tvCd2, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((cC X Y m false hm hW).slot hW 1).1 = tvC2 X.length m 5 := by
      rw [Chain.slot_succ]; exact (c_A4 X Y m hm hW s0 (by omega) C2 le_rfl).1
    have s2 : ((cC X Y m false hm hW).slot hW 2).1 = tvC2 X.length m 4 := by
      rw [Chain.slot_succ]; exact c_A7 X Y m hW s1 C5
    have s3 : ((cC X Y m false hm hW).slot hW 3).1 = tvC2 X.length m 3 := by
      rw [Chain.slot_succ]; exact c_A10 X Y m hm hW s2 (Or.inr rfl) C7
    have s4 : ((cC X Y m false hm hW).slot hW 4).1 = tvC2 X.length m 2 := by
      rw [Chain.slot_succ, c_A12 X Y m false hm hW he s3]; rfl
    have s5 : ((cC X Y m false hm hW).slot hW 5).1 = tvC2 X.length m 1 := by
      rw [Chain.slot_succ]; exact (c_A17 X Y m hW s4 (by omega) he (by omega)).1
    have s6 : ((cC X Y m false hm hW).slot hW 6).1 = tvC2 X.length m 0 := by
      rw [Chain.slot_succ]; exact c_A14 X Y m hm hW s5 C3
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
  · simp only [tvCd2, ↓reduceIte] at s0 ⊢
    have s1 : ((cC X Y m true hm hW).slot hW 1).1 = tvC2 X.length m 1 := by
      rw [Chain.slot_succ]; exact c_A3 X Y m hm hW s0 C1
    have s2 : ((cC X Y m true hm hW).slot hW 2).1 = tvC2 X.length m 2 := by
      rw [Chain.slot_succ]; exact (c_A5 X Y m hW s1 (by omega) C3 (by omega)).1
    have s3 : ((cC X Y m true hm hW).slot hW 3).1 = tvC2 X.length m 3 := by
      rw [Chain.slot_succ]; exact c_A10 X Y m hm hW s2 (Or.inl rfl) he
    have s4 : ((cC X Y m true hm hW).slot hW 4).1 = tvC2 X.length m 4 := by
      rw [Chain.slot_succ, c_A12 X Y m true hm hW he s3]; rfl
    have s5 : ((cC X Y m true hm hW).slot hW 5).1 = tvC2 X.length m 5 := by
      rw [Chain.slot_succ]; exact c_A18 X Y m hW s4 C7
    have s6 : ((cC X Y m true hm hW).slot hW 6).1 = tvC2 X.length m 6 := by
      rw [Chain.slot_succ]; exact (c_A16 X Y m hm hW s5 (by omega) C5 le_rfl).1
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6

include hm ht he in
theorem cT_col : ∀ j, j < 3 → colOf ((cT X Y m t hm hW).slot hW j) = if t then colT X.length j else colT X.length (2 - j) := by
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  have hv := cT_slot_val X Y m t e hm hW ht he
  intro j hj
  cases t
  · simp only [tvTd2, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvT2] using C9)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp) (by simpa [tvT2] using C8)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp; omega) (by simpa [tvT2] using C4)]; rfl
  · simp only [tvTd2, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvT2] using ht)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp; omega) (by simpa [tvT2] using C4)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp) (by simpa [tvT2] using C8)]; rfl

include hm ht he in
theorem cC_col : ∀ j, j < 6 → colOf ((cC X Y m e hm hW).slot hW j) = colC2 X.length j := by
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  have hv := cC_slot_val X Y m t e hm hW ht he
  intro j hj
  cases e
  · simp only [tvCd2, Bool.false_eq_true, ↓reduceIte] at hv
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp) (by simpa [tvC2] using C2)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp) (by simpa [tvC2] using C5)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp; omega) (by simpa [tvC2] using C7)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_false (hv 4 (by norm_num)) (by simp; omega) (by simpa [tvC2] using he)]; rfl
    · rw [block_col_false (hv 5 (by norm_num)) (by simp; omega) (by simpa [tvC2] using C3)]; rfl
  · simp only [tvCd2, ↓reduceIte] at hv
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvC2] using C1)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp; omega) (by simpa [tvC2] using C3)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp; omega) (by simpa [tvC2] using he)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_false (hv 4 (by norm_num)) (by simp; omega) (by simpa [tvC2] using C7)]; rfl
    · rw [block_col_false (hv 5 (by norm_num)) (by simp) (by simpa [tvC2] using C5)]; rfl

include hm ht he in
theorem cT_col3 : ExtCol X Pc (colOf ((cT X Y m t hm hW).slot hW 3)) := by
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  have hv := cT_slot_val X Y m t e hm hW ht he 3 le_rfl
  rw [c_extCol]
  cases t
  · simp only [tvTd2, Bool.false_eq_true, ↓reduceIte, tvT2] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) ht]; omega
  · simp only [tvTd2, ↓reduceIte, tvT2] at hv
    rw [block_col_true hv (by omega) C9]; omega

include hm ht he in
theorem cC_col6 : ExtCol X Pc (colOf ((cC X Y m e hm hW).slot hW 6)) := by
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  have hv := cC_slot_val X Y m t e hm hW ht he 6 le_rfl
  rw [c_extCol]
  cases e
  · simp only [tvCd2, Bool.false_eq_true, ↓reduceIte, tvC2] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) C1]; omega
  · simp only [tvCd2, ↓reduceIte, tvC2] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) C2]; omega

end TypeIIcWord

/-! #### G2. The type-II variant (c): the block passage -/

/-- an exterior cut slot at the left cut of the block -/
theorem isExtSlot_cut_left (X P : Word) {p : ℕ} (hp : p ≠ 0) : IsExtSlot X P (X.length, p) := by
  simp only [IsExtSlot, ExtCut, hp, ↓reduceIte]
  exact Or.inl le_rfl

/-- an exterior cut slot at the right cut of the block -/
theorem isExtSlot_cut_right (X P : Word) {p : ℕ} (hp : p ≠ 0) : IsExtSlot X P (X.length + P.length, p) := by
  simp only [IsExtSlot, ExtCut, hp, ↓reduceIte]
  exact Or.inr le_rfl

section TypeIIcPassage

open U3

variable (X Y : Word) (m : ℕ) (t e : Bool) (hm : 2 ≤ m)
  (hW : (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y).Closed)
  (hW' : (X ++ [Letter.r m] ++ Y).Closed)

local notation "Vc" => X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y
local notation "Pc" => [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)]
local notation "Vc'" => X ++ [Letter.r m] ++ Y
local notation "Pc'" => [Letter.r m]

include hW'

theorem c'_L1 {s : Slot Vc'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc' X.length p = true)
    (hpm : p < m) : (next hW' s).1 = (X.length + 1, p) ∧ bit Vc' (X.length + 1) p = true :=
  next_right_lt hW' hs hp hb (by rw [c'_letters X Y m]; exact hpm)

theorem c'_L2 {s : Slot Vc'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p = m ∨ p = m + 1)
    (hb : bit Vc' X.length p = true) : (next hW' s).1 = (X.length, 0) :=
  next_arm_r hW' (by rw [c'_length]; omega) (c'_letters X Y m) hs hp hb

theorem c'_L3 {s : Slot Vc'} (hs : s.1 = (X.length, 0)) :
    (next hW' s).1 = (X.length, if bit Vc' X.length m then m + 1 else m) :=
  next_cusp_r hW' (c'_letters X Y m) hs

theorem c'_L4 {s : Slot Vc'} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc' X.length p = true)
    (hpm : m + 2 ≤ p) : (next hW' s).1 = (X.length + 1, p - 2) ∧ bit Vc' (X.length + 1) (p - 2) = true := by
  have := next_right_ge hW' hs hp hb (by rw [c'_letters X Y m]; simp only [idx, arity]; omega)
  rw [c'_letters X Y m] at this
  simpa [coarity, arity] using this

theorem c'_L5 {s : Slot Vc'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc' (X.length + 1) q = false) (hqm : q < m) :
    (next hW' s).1 = (X.length, q) ∧ bit Vc' X.length q = false := by
  have := next_left_lt hW' hs hq hb (by rw [Nat.add_sub_cancel, c'_letters X Y m]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem c'_L6 {s : Slot Vc'} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc' (X.length + 1) q = false) (hqm : m ≤ q) :
    (next hW' s).1 = (X.length, q + 2) ∧ bit Vc' X.length (q + 2) = false := by
  have := next_left_ge hW' hs hq hb (by rw [Nat.add_sub_cancel, c'_letters X Y m]; simp only [idx, coarity]; omega)
  rw [Nat.add_sub_cancel, c'_letters X Y m] at this
  simpa [arity, coarity] using this

theorem c'_hexit : ∀ u : Slot Vc', ∃ n, ExtPiece X Pc' Y ((next hW')^[n] u) := by
  apply hexit_of_no_l X Pc' Y hW'
  intro k' h1 h2 m' d'
  simp only [List.length_cons, List.length_nil] at h2
  have : k' = X.length := by omega
  subst this
  rw [c'_letters X Y m]; exact fun h => by cases h

include hm hW

/-- THE BLOCK PASSAGE of the type-II variant (c). -/
theorem c_passage : Passage X Pc Y Pc' hW hW' := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ :=
    c_bits X Y m (bit Vc X.length (m - 1)) (bit Vc (X.length + 2) (m - 1)) hm hW rfl rfl
  have hP : Pc ≠ [] := by simp
  have hE := c_sameEffect X Y m hm hW
  have shiftL : ∀ p, extPair X Pc Pc' (X.length, p) = (X.length, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pc Pc' le_rfl]
  have shiftR : ∀ p, extPair X Pc Pc' (X.length + 3, p) = (X.length + 1, p) := by
    intro p; simp only [extPair, c_shift X m]
  constructor
  intro b hext hcol
  let b' : Slot Vc' := ⟨extPair X Pc Pc' b.1, isSlot_ext X Pc Y Pc' hP hE b.2 hext⟩
  have hb'v : b'.1 = extPair X Pc Pc' b.1 := rfl
  -- the through-strand, as the chain `cT`
  have curlT : b = (cT X Y m (bit Vc X.length (m - 1)) hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Vc), (next hW)^[n] b = c ∧ ExtCol X Pc (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pc (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot Vc'), b'.1 = extPair X Pc Pc' b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pc Pc' c.1 ∧ ∀ i < m', ¬ ExtCol X Pc' (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨3, (cT X Y m _ hm hW).slot hW 3, by rw [hb]; rfl, cT_col3 X Y m _ _ hm hW rfl rfl, ?_, ?_⟩
    · intro i hi
      have h := cT_col X Y m _ _ hm hW rfl rfl i hi
      rw [hb]
      show ¬ ExtCol X Pc (colOf ((cT X Y m _ hm hW).slot hW i))
      rw [h, c_extCol]
      cases bit Vc X.length (m - 1) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> interval_cases i <;> simp [colT]
    · have h0 := cT_slot_val X Y m _ _ hm hW rfl rfl 0 (by norm_num)
      have h3 := cT_slot_val X Y m _ _ hm hW rfl rfl 3 le_rfl
      rw [Chain.slot_zero] at h0
      cases hE0 : bit Vc X.length (m - 1)
      · -- leftward: `W'`: `(|X|+1, m−1)` leftward through `r_m` to `(|X|, m−1)`
        rw [hE0] at h0 h3 hb
        have hb0 : b.1 = (X.length + 3, m - 1) := by rw [hb]; exact h0
        have hc3 : ((cT X Y m false hm hW).slot hW 3).1 = (X.length, m - 1) := h3
        have hslot : IsSlot Vc' (X.length + 1, m - 1) := by
          have := isSlot_ext X Pc Y Pc' hP hE (s := (X.length + 3, m - 1)) (hb0 ▸ b.2)
            (isExtSlot_cut_right X Pc (p := m - 1) (by omega))
          rwa [shiftR] at this
        have hbit' : bit Vc' (X.length + 1) (m - 1) = false := by rw [c_bit_end X Y m hm hW, C9, hE0]
        refine ⟨1, ⟨(X.length + 1, m - 1), hslot⟩, by rw [hb0, shiftR], ?_, ?_⟩
        · rw [hc3, shiftL, Function.iterate_one]
          exact (c'_L5 X Y m hW' (s := ⟨_, hslot⟩) (q := m - 1) rfl (by omega) hbit' (by omega)).1
        · intro i hi
          have : i = 0 := by omega
          subst this
          rw [Function.iterate_zero, id, block_col_false (s := ⟨_, hslot⟩) (k := X.length + 1) (p := m - 1) rfl (by omega) hbit',
            c'_extCol]; omega
      · rw [hE0] at h0 h3 hb
        have hb0 : b.1 = (X.length, m - 1) := by rw [hb]; exact h0
        have hc3 : ((cT X Y m true hm hW).slot hW 3).1 = (X.length + 3, m - 1) := h3
        have hslot : IsSlot Vc' (X.length, m - 1) := by
          have := isSlot_ext X Pc Y Pc' hP hE (s := (X.length, m - 1)) (hb0 ▸ b.2)
            (isExtSlot_cut_left X Pc (p := m - 1) (by omega))
          rwa [shiftL] at this
        have hbit' : bit Vc' X.length (m - 1) = true := by rw [c_bit_start, hE0]
        refine ⟨1, ⟨(X.length, m - 1), hslot⟩, by rw [hb0, shiftL], ?_, ?_⟩
        · rw [hc3, shiftR, Function.iterate_one]
          exact (c'_L1 X Y m hW' (s := ⟨_, hslot⟩) (p := m - 1) rfl (by omega) hbit' (by omega)).1
        · intro i hi
          have : i = 0 := by omega
          subst this
          rw [Function.iterate_zero, id, block_col_true (s := ⟨_, hslot⟩) (k := X.length) (p := m - 1) rfl (by omega) hbit',
            c'_extCol]; omega
  -- the cusp arc, as the chain `cC`
  have curlC : b = (cC X Y m (bit Vc (X.length + 2) (m - 1)) hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Vc), (next hW)^[n] b = c ∧ ExtCol X Pc (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pc (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot Vc'), b'.1 = extPair X Pc Pc' b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pc Pc' c.1 ∧ ∀ i < m', ¬ ExtCol X Pc' (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨6, (cC X Y m _ hm hW).slot hW 6, by rw [hb]; rfl, cC_col6 X Y m _ _ hm hW rfl rfl, ?_, ?_⟩
    · intro i hi
      have h := cC_col X Y m _ _ hm hW rfl rfl i hi
      rw [hb]
      show ¬ ExtCol X Pc (colOf ((cC X Y m _ hm hW).slot hW i))
      rw [h, c_extCol]
      interval_cases i <;> simp [colC2]
    · have h0 := cC_slot_val X Y m _ _ hm hW rfl rfl 0 (by norm_num)
      have h6 := cC_slot_val X Y m _ _ hm hW rfl rfl 6 le_rfl
      rw [Chain.slot_zero] at h0
      -- `W'`: `(|X|, m)` (`e`) or `(|X|, m+1)` (`!e`) rightward into the cusp of `r_m`, out along the other arm
      cases hE0 : bit Vc (X.length + 2) (m - 1)
      · rw [hE0] at h0 h6 hb
        have hb0 : b.1 = (X.length, m + 1) := by rw [hb]; exact h0
        have hc6 : ((cC X Y m false hm hW).slot hW 6).1 = (X.length, m) := h6
        have hslot : IsSlot Vc' (X.length, m + 1) := by
          have := isSlot_ext X Pc Y Pc' hP hE (s := (X.length, m + 1)) (hb0 ▸ b.2)
            (isExtSlot_cut_left X Pc (p := m + 1) (by omega))
          rwa [shiftL] at this
        have hbit' : bit Vc' X.length (m + 1) = true := by rw [c_bit_start, C2, hE0]; rfl
        have hbm' : bit Vc' X.length m = false := by rw [c_bit_start, C1, hE0]
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
        have hc6 : ((cC X Y m true hm hW).slot hW 6).1 = (X.length, m + 1) := h6
        have hslot : IsSlot Vc' (X.length, m) := by
          have := isSlot_ext X Pc Y Pc' hP hE (s := (X.length, m)) (hb0 ▸ b.2)
            (isExtSlot_cut_left X Pc (p := m) (by omega))
          rwa [shiftL] at this
        have hbit' : bit Vc' X.length m = true := by rw [c_bit_start, C1, hE0]
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
  rcases (entry_iff X Pc Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hb'1 : b'.1 = (X.length, p) := by rw [hb'v, hb, shiftL]
    have hbit' : bit Vc' X.length p = true := by rw [c_bit_start, hbit]
    have hcol0 : ¬ ExtCol X Pc (colOf b) := by rw [block_col_true hb hp hbit, c_extCol]; omega
    have hcol0' : ¬ ExtCol X Pc' (colOf b') := by rw [block_col_true hb'1 hp hbit', c'_extCol]; omega
    rcases lt_or_ge p (m - 1) with hpm | hpm
    · obtain ⟨h1, hb1⟩ := c_A1 X Y m hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := c_A5 X Y m hW h1 hp hb1 (by omega)
      obtain ⟨h3, hb3⟩ := c_A9 X Y m hW h2 hp hb2 hpm
      obtain ⟨h1', hb1'⟩ := c'_L1 X Y m hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h1 hp hb1, c_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h2 hp hb2, c_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h3 hp hb3, c_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftR]
    rcases lt_or_ge p (m + 2) with hpm2 | hpm2
    · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
      rcases this with hpe | hpe | hpe
      · -- the through-strand, rightward
        subst hpe
        apply curlT
        apply Subtype.ext
        rw [hb]
        show _ = tvTd2 X.length m (bit Vc X.length (m - 1)) 0
        rw [hbit]; rfl
      · -- the cusp arc entered along `(|X|, m)`: `e = true`
        apply curlC
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvCd2 X.length m (bit Vc (X.length + 2) (m - 1)) 0
        rw [hpe, C1] at hbit
        rw [hbit]; rfl
      · -- entered along `(|X|, m+1)`: `e = false`
        apply curlC
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvCd2 X.length m (bit Vc (X.length + 2) (m - 1)) 0
        rw [hpe, C2] at hbit
        have he : bit Vc (X.length + 2) (m - 1) = false := by simpa using hbit
        rw [he]; rfl
    · obtain ⟨h1, hb1⟩ := c_A4 X Y m hm hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := c_A8 X Y m hW h1 hp hb1 hpm2
      obtain ⟨h3, hb3⟩ := c_A11 X Y m hm hW h2 hp hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := c'_L4 X Y m hW' hb'1 hp hbit' hpm2
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h1 hp hb1, c_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h2 hp hb2, c_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h3 (by omega) hb3, c_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftR]
  · -- from the right at `(|X|+3, q)`
    replace hb : b.1 = (X.length + 3, p) := hb
    replace hbit : bit Vc (X.length + 3) p = false := hbit
    have hb'1 : b'.1 = (X.length + 1, p) := by rw [hb'v, hb, shiftR]
    have hbit' : bit Vc' (X.length + 1) p = false := by rw [c_bit_end X Y m hm hW, hbit]
    have hcol0 : ¬ ExtCol X Pc (colOf b) := by rw [block_col_false hb hp hbit, c_extCol]; omega
    have hcol0' : ¬ ExtCol X Pc' (colOf b') := by rw [block_col_false hb'1 hp hbit', c'_extCol]; omega
    rcases lt_or_ge p (m - 1) with hpm | hpm
    · obtain ⟨h1, hb1⟩ := c_A21 X Y m hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := c_A17 X Y m hW h1 hp hb1 (by omega)
      obtain ⟨h3, hb3⟩ := c_A13 X Y m hW h2 hp hb2 hpm
      obtain ⟨h1', hb1'⟩ := c'_L5 X Y m hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 hp hb1, c_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h2 hp hb2, c_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0' (passage_end hW')
      have hk3 := (cutSlot_facts hW h3 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 hp hb3, c_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftL]
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
    · -- `p = m − 1`: the through-strand, leftward
      subst hpe
      apply curlT
      apply Subtype.ext
      rw [hb]
      show _ = tvTd2 X.length m (bit Vc X.length (m - 1)) 0
      rw [← C9, hbit]; rfl
    · obtain ⟨h1, hb1⟩ := c_A22 X Y m hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := c_A20 X Y m hW h1 (by omega) hb1 (by omega)
      obtain ⟨h3, hb3⟩ := c_A16 X Y m hm hW h2 (by omega) hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := c'_L6 X Y m hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc) hcol0
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 (by omega) hb1, c_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h2 (by omega) hb2, c_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pc') hcol0' (passage_end hW')
      have hk3 := (cutSlot_facts hW h3 (by omega)).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 (by omega) hb3, c_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftL]

end TypeIIcPassage

/-! #### G3. The type-II variant (c): the moved diagram -/

/-- the realization's positions of the through-strand's vertices (variant (c)) -/
def pvA2 (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h)
  | 1 => (((k + 1 : ℕ) : ℝ), h - 1)
  | 2 => (((k + 2 : ℕ) : ℝ), h - 2)
  | _ => (((k + 3 : ℕ) : ℝ), h)

/-- the positions of the cusp arc's seven vertices (variant (c), unmoved) -/
def pvB2 (k : ℕ) (h : ℝ) : ℕ → Plane
  | 0 => ((k : ℝ), h - 1)
  | 1 => (((k + 1 : ℕ) : ℝ), h)
  | 2 => (((k + 2 : ℕ) : ℝ), h)
  | 3 => (((k + 2 : ℕ) : ℝ) + 1 / 2, h - 1 / 2)
  | 4 => (((k + 2 : ℕ) : ℝ), h - 1)
  | 5 => (((k + 1 : ℕ) : ℝ), h - 2)
  | _ => ((k : ℝ), h - 2)

/-- the two moved slots of the type-II variant (c) -/
def IsMovedC (k m : ℕ) (s : ℕ × ℕ) : Prop := s = (k + 1, m) ∨ s = (k + 2, m + 1)

/-- the moved vertex function of the type-II variant (c): the same lifted positions as variant (a) -/
def mvIIc (W : Word) (k m : ℕ) (h : ℝ) (u : Slot W) : Plane :=
  if u.1 = (k + 1, m) then mvA k h 1
  else if u.1 = (k + 2, m + 1) then mvA k h 2
  else pt .std W u.1

section MvIIc

variable (W : Word) (k m : ℕ) (h : ℝ)

theorem mvIIc_of_not_moved {u : Slot W} (hu : ¬ IsMovedC k m u.1) : mvIIc W k m h u = pt .std W u.1 := by
  unfold IsMovedC at hu
  simp only [not_or] at hu
  obtain ⟨h1, h2⟩ := hu
  simp [mvIIc, h1, h2]

theorem mvIIc_v1 {u : Slot W} (hu : u.1 = (k + 1, m)) : mvIIc W k m h u = mvA k h 1 := by simp [mvIIc, hu]
theorem mvIIc_v2 {u : Slot W} (hu : u.1 = (k + 2, m + 1)) : mvIIc W k m h u = mvA k h 2 := by
  simp [mvIIc, hu]

theorem mvIIc_of_ext {u : Slot W} (hu : ExtSl k (k + 3) u.1) : mvIIc W k m h u = pt .std W u.1 := by
  apply mvIIc_of_not_moved
  obtain ⟨j, p, hu'⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu'] at hu ⊢
  unfold ExtSl at hu
  unfold IsMovedC
  simp only [Prod.mk.injEq]
  split_ifs at hu with h0 <;> omega

theorem mvIIc_xcoord (hm : 1 ≤ m) (u : Slot W) : (mvIIc W k m h u).1 = (pt .std W u.1).1 := by
  by_cases hmv : IsMovedC k m u.1
  · unfold IsMovedC at hmv
    rcases hmv with e | e
    · rw [mvIIc_v1 W k m h e, e, std_pt_cut _ (by omega)]; rfl
    · rw [mvIIc_v2 W k m h e, e, std_pt_cut _ (by omega)]; rfl
  · rw [mvIIc_of_not_moved W k m h hmv]

theorem mvIIc_injective (n : ℕ) : Function.Injective (mvIIc W k m (-(n : ℝ) + 1)) := by
  have ng : ∀ i, 1 ≤ i → i ≤ 2 → ∀ s, mvA k (-(n : ℝ) + 1) i ≠ pt .std W s := by
    intro i hi1 hi2 s
    have := nonGrid_eighth n 5 (by decide)
    have e : -(n : ℝ) + 1 + 5 / 8 = -(n : ℝ) + 1 + ((5 : ℤ) : ℝ) / 8 := by push_cast; ring
    interval_cases i
    · show (((k + 1 : ℕ) : ℝ), -(n : ℝ) + 1 + 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
    · show (((k + 2 : ℕ) : ℝ), -(n : ℝ) + 1 + 5 / 8) ≠ _
      rw [e]; exact this.ne_pt W _ _
  have hval : ∀ u : Slot W, IsMovedC k m u.1 → ∃ i, 1 ≤ i ∧ i ≤ 2 ∧ mvIIc W k m (-(n : ℝ) + 1) u = mvA k (-(n : ℝ) + 1) i ∧
      (i = 1 → u.1 = (k + 1, m)) ∧ (i = 2 → u.1 = (k + 2, m + 1)) := by
    intro u hu
    unfold IsMovedC at hu
    rcases hu with e | e
    · exact ⟨1, le_rfl, by norm_num, mvIIc_v1 W k m _ e, fun _ => e, fun h => absurd h (by norm_num)⟩
    · exact ⟨2, by norm_num, le_rfl, mvIIc_v2 W k m _ e, fun h => absurd h (by norm_num), fun _ => e⟩
  have hdist : ∀ i j, 1 ≤ i → i ≤ 2 → 1 ≤ j → j ≤ 2 → mvA k (-(n : ℝ) + 1) i = mvA k (-(n : ℝ) + 1) j → i = j := by
    intro i j hi1 hi2 hj1 hj2 he
    interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; have := congrArg Prod.fst he; simp only [mvA] at this; push_cast at this; linarith)
  intro u v huv
  by_cases hu : IsMovedC k m u.1
  · obtain ⟨i, hi1, hi2, hui, hu1, hu2⟩ := hval u hu
    by_cases hv : IsMovedC k m v.1
    · obtain ⟨j, hj1, hj2, hvj, hv1, hv2⟩ := hval v hv
      have := hdist i j hi1 hi2 hj1 hj2 (hui.symm.trans (huv.trans hvj))
      subst this
      apply Subtype.ext
      interval_cases i
      · rw [hu1 rfl, hv1 rfl]
      · rw [hu2 rfl, hv2 rfl]
    · rw [hui, mvIIc_of_not_moved W k m _ hv] at huv
      exact absurd huv (ng i hi1 hi2 _)
  · by_cases hv : IsMovedC k m v.1
    · obtain ⟨j, hj1, hj2, hvj, -⟩ := hval v hv
      rw [hvj, mvIIc_of_not_moved W k m _ hu] at huv
      exact absurd huv.symm (ng j hj1 hj2 _)
    · rw [mvIIc_of_not_moved W k m _ hu, mvIIc_of_not_moved W k m _ hv] at huv
      exact pt_inj _ _ huv

end MvIIc

section IIcVertices

variable (k : ℕ) (h : ℝ)

theorem mvA_intR : ∀ i, 1 ≤ i → i ≤ 2 → mvA k h i ∈ interior (polygon (tIIR k h)) := by
  intro i h1 h2
  interval_cases i
  · exact tIIR_int_cut1 k h (5 / 8) (by norm_num) (by norm_num)
  · exact tIIR_int_cut2 k h (5 / 8) (by norm_num) (by norm_num)

theorem pvA2_int : ∀ i, 1 ≤ i → i ≤ 2 → pvA2 k h i ∈ interior (polygon (tIIR k h)) := by
  intro i h1 h2
  interval_cases i
  · have := tIIR_int_cut1 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIR_int_cut2 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem pvB2_int : ∀ i, 1 ≤ i → i ≤ 5 → pvB2 k h i ∈ interior (polygon (tIIR k h)) := by
  intro i h1 h5
  interval_cases i
  · have := tIIR_int_cut1 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tIIR_int_cut2 k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  · have := tIIR_int_cuspR k h (-(1 / 2)) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIR_int_cut2 k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  · have := tIIR_int_cut1 k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

theorem mvA_memR : ∀ i, i ≤ 3 → mvA k h i ∈ polygon (tIIR k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIR_mem_left k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · exact interior_subset (mvA_intR k h i h0 (by omega))
  · have : i = 3 := by omega
    subst this
    have := tIIR_mem_right k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem pvA2_mem : ∀ i, i ≤ 3 → pvA2 k h i ∈ polygon (tIIR k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIR_mem_left k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · exact interior_subset (pvA2_int k h i h0 (by omega))
  · have : i = 3 := by omega
    subst this
    have := tIIR_mem_right k h 0 (by norm_num) (by norm_num); rwa [add_zero] at this

theorem pvB2_mem : ∀ i, i ≤ 6 → pvB2 k h i ∈ polygon (tIIR k h) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have := tIIR_mem_left k h (-1) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this
  rcases Nat.lt_or_ge i 6 with h6 | h6
  · exact interior_subset (pvB2_int k h i h0 (by omega))
  · have : i = 6 := by omega
    subst this
    have := tIIR_mem_left k h (-2) (by norm_num) (by norm_num); rwa [← sub_eq_add_neg] at this

/-! the geometric facts of the same-column pairs of the moved variant (c) -/

macro "cII_pair" : tactic => `(tactic| (
  intro τ τ' h0 h1 h0' h1' he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [mvA, pvB2, segPt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at hx hy
  push_cast at hx hy))

theorem cII_NM_T0C0 : NoMeet (mvA k h 0) (mvA k h 1) (pvB2 k h 0) (pvB2 k h 1) := by cII_pair; linarith
theorem cII_NM_T0C5 : NoMeet (mvA k h 0) (mvA k h 1) (pvB2 k h 5) (pvB2 k h 6) := by cII_pair; linarith
theorem cII_NM_T1C1 : NoMeet (mvA k h 1) (mvA k h 2) (pvB2 k h 1) (pvB2 k h 2) := by cII_pair; linarith
theorem cII_NM_T1C4 : NoMeet (mvA k h 1) (mvA k h 2) (pvB2 k h 4) (pvB2 k h 5) := by cII_pair; linarith
theorem cII_NM_T2C2 : NoMeet (mvA k h 2) (mvA k h 3) (pvB2 k h 2) (pvB2 k h 3) := by cII_pair; linarith
theorem cII_NM_T2C3 : NoMeet (mvA k h 2) (mvA k h 3) (pvB2 k h 3) (pvB2 k h 4) := by cII_pair; linarith
theorem cII_NM_C0C5 : NoMeet (pvB2 k h 0) (pvB2 k h 1) (pvB2 k h 5) (pvB2 k h 6) := by cII_pair; linarith
theorem cII_NM_C1C4 : NoMeet (pvB2 k h 1) (pvB2 k h 2) (pvB2 k h 4) (pvB2 k h 5) := by cII_pair; linarith
theorem cII_OJ234 : OnlyAtJoint (pvB2 k h 2) (pvB2 k h 3) (pvB2 k h 4) := by
  cII_pair; constructor <;> linarith

end IIcVertices

/-! #### G4. The type-II variant (c): the specification -/

section TypeIIcSpec

open U3

variable (X Y : Word) (m : ℕ) (t e : Bool) (hm : 2 ≤ m)
  (hW : (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y) X.length (m - 1) = t)
  (he : bit (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y) (X.length + 2) (m - 1) = e)

local notation "Vc" => X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y
local notation "Pc" => [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)]
local notation "Vc'" => X ++ [Letter.r m] ++ Y
local notation "Pc'" => [Letter.r m]
local notation "hA" => (-(m : ℝ) + 1)

/-- the moved vertex function of the type-II variant (c) -/
def cMv : Slot Vc → Plane := mvIIc Vc X.length m hA

theorem cMv_apply (u : Slot Vc) : cMv X Y m u = mvIIc Vc X.length m hA u := rfl

include hm

theorem c_pt_T : ∀ i, i ≤ 3 → pt .std Vc (tvT2 X.length m i) = pvA2 X.length hA i := by
  have hm1 := a_hm1 m hm
  intro i hi
  interval_cases i
  · show pt .std Vc (X.length, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA2]; rw [hm1]; ring)
  · show pt .std Vc (X.length + 1, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA2]; ring)
  · show pt .std Vc (X.length + 2, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA2]; push_cast; ring)
  · show pt .std Vc (X.length + 3, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvA2]; rw [hm1]; ring)

theorem c_pt_C : ∀ i, i ≤ 6 → pt .std Vc (tvC2 X.length m i) = pvB2 X.length hA i := by
  have hm1 := a_hm1 m hm
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
  intro i hi
  interval_cases i
  · show pt .std Vc (X.length, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB2]; ring)
  · show pt .std Vc (X.length + 1, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB2]; rw [hm1]; ring)
  · show pt .std Vc (X.length + 2, m - 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB2]; rw [hm1]; ring)
  · show pt .std Vc (X.length + 2, 0) = _
    rw [std_pt_cusp, hℓ₂]; exact Prod.ext rfl (by simp only [pvB2, idx]; rw [hm1]; ring)
  · show pt .std Vc (X.length + 2, m) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB2]; ring)
  · show pt .std Vc (X.length + 1, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB2]; push_cast; ring)
  · show pt .std Vc (X.length, m + 1) = _
    rw [std_pt_cut _ (by omega)]; exact Prod.ext rfl (by simp only [pvB2]; push_cast; ring)

theorem c_mv_T : ∀ i, i ≤ 3 → ∀ u : Slot Vc, u.1 = tvT2 X.length m i → cMv X Y m u = mvA X.length hA i := by
  intro i hi u hu
  rw [cMv_apply]
  interval_cases i
  · rw [mvIIc_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedC, tvT2, Prod.mk.injEq]; omega), hu,
      c_pt_T X Y m hm 0 (by norm_num)]; rfl
  · exact mvIIc_v1 _ _ _ _ hu
  · exact mvIIc_v2 _ _ _ _ hu
  · rw [mvIIc_of_not_moved _ _ _ _ (by rw [hu]; simp only [IsMovedC, tvT2, Prod.mk.injEq]; omega), hu,
      c_pt_T X Y m hm 3 (by norm_num)]; rfl

theorem c_mv_C : ∀ i, i ≤ 6 → ∀ u : Slot Vc, u.1 = tvC2 X.length m i → cMv X Y m u = pvB2 X.length hA i := by
  intro i hi u hu
  have hnm : ¬ IsMovedC X.length m u.1 := by
    rw [hu]; interval_cases i <;> simp only [IsMovedC, tvC2, Prod.mk.injEq] <;> omega
  rw [cMv_apply, mvIIc_of_not_moved _ _ _ _ hnm, hu]
  exact c_pt_C X Y m hm i hi

omit hm in
theorem tvT2_inj : ∀ i j, i ≤ 3 → j ≤ 3 → tvT2 X.length m i = tvT2 X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tvT2, Prod.mk.injEq] at he; omega)

theorem tvC2_inj : ∀ i j, i ≤ 6 → j ≤ 6 → tvC2 X.length m i = tvC2 X.length m j → i = j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; simp only [tvC2, Prod.mk.injEq] at he; omega)

theorem tvT2_ne_tvC2 : ∀ i j, i ≤ 3 → j ≤ 6 → tvT2 X.length m i ≠ tvC2 X.length m j := by
  intro i j hi hj he
  interval_cases i <;> interval_cases j <;> simp only [tvT2, tvC2, Prod.mk.injEq] at he <;> omega

include hW ht he

theorem cT_mv_slot : ∀ j, j ≤ 3 → cMv X Y m ((cT X Y m t hm hW).slot hW j) =
    if t then mvA X.length hA j else mvA X.length hA (3 - j) := by
  intro j hj
  have hs := cT_slot_val X Y m t e hm hW ht he j hj
  cases t
  · simp only [tvTd2, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact c_mv_T X Y m hm (3 - j) (by omega) _ hs
  · simp only [tvTd2, ↓reduceIte] at hs ⊢
    exact c_mv_T X Y m hm j hj _ hs

theorem cT_pt_slot : ∀ j, j ≤ 3 → pt .std Vc ((cT X Y m t hm hW).slot hW j).1 =
    if t then pvA2 X.length hA j else pvA2 X.length hA (3 - j) := by
  intro j hj
  have hs := cT_slot_val X Y m t e hm hW ht he j hj
  cases t
  · simp only [tvTd2, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact c_pt_T X Y m hm (3 - j) (by omega)
  · simp only [tvTd2, ↓reduceIte] at hs ⊢
    rw [hs]; exact c_pt_T X Y m hm j hj

theorem cC_mv_slot : ∀ j, j ≤ 6 → cMv X Y m ((cC X Y m e hm hW).slot hW j) =
    if e then pvB2 X.length hA j else pvB2 X.length hA (6 - j) := by
  intro j hj
  have hs := cC_slot_val X Y m t e hm hW ht he j hj
  cases e
  · simp only [tvCd2, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact c_mv_C X Y m hm (6 - j) (by omega) _ hs
  · simp only [tvCd2, ↓reduceIte] at hs ⊢
    exact c_mv_C X Y m hm j hj _ hs

theorem cC_pt_slot : ∀ j, j ≤ 6 → pt .std Vc ((cC X Y m e hm hW).slot hW j).1 =
    if e then pvB2 X.length hA j else pvB2 X.length hA (6 - j) := by
  intro j hj
  have hs := cC_slot_val X Y m t e hm hW ht he j hj
  cases e
  · simp only [tvCd2, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]; exact c_pt_C X Y m hm (6 - j) (by omega)
  · simp only [tvCd2, ↓reduceIte] at hs ⊢
    rw [hs]; exact c_pt_C X Y m hm j hj

omit ht he in
theorem cT_next_slot : ∀ j, j < 3 → next hW ((cT X Y m t hm hW).slot hW j) = (cT X Y m t hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

omit ht he in
theorem cC_next_slot : ∀ j, j < 6 → next hW ((cC X Y m e hm hW).slot hW j) = (cC X Y m e hm hW).slot hW (j + 1) :=
  fun j _ => (Chain.slot_succ hW _ j).symm

theorem cT_chain_in : ∀ j, j < 3 → PieceIn (tIIR X.length hA) hW (cMv X Y m) ((cT X Y m t hm hW).slot hW j) ∧
    PieceIn (tIIR X.length hA) hW (ptv .std) ((cT X Y m t hm hW).slot hW j) := by
  intro j hj
  have e' := cT_next_slot X Y m t hm hW j hj
  have key : ∀ (f : ℕ → Plane), (∀ i, i ≤ 3 → f i ∈ polygon (tIIR X.length hA)) →
      (∀ i, 1 ≤ i → i ≤ 2 → f i ∈ interior (polygon (tIIR X.length hA))) →
      SegIn (tIIR X.length hA) (if t then f j else f (3 - j)) (if t then f (j + 1) else f (3 - (j + 1))) := by
    intro f hmem hint
    cases t
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
  · show SegIn _ (cMv X Y m _) (cMv X Y m (next hW _))
    rw [e', cT_mv_slot X Y m t e hm hW ht he j (by omega), cT_mv_slot X Y m t e hm hW ht he (j + 1) (by omega)]
    exact key _ (mvA_memR _ _) (mvA_intR _ _)
  · show SegIn _ (pt .std Vc _) (pt .std Vc (next hW _).1)
    rw [e', cT_pt_slot X Y m t e hm hW ht he j (by omega), cT_pt_slot X Y m t e hm hW ht he (j + 1) (by omega)]
    exact key _ (pvA2_mem _ _) (pvA2_int _ _)

theorem cC_chain_in : ∀ j, j < 6 → PieceIn (tIIR X.length hA) hW (cMv X Y m) ((cC X Y m e hm hW).slot hW j) ∧
    PieceIn (tIIR X.length hA) hW (ptv .std) ((cC X Y m e hm hW).slot hW j) := by
  intro j hj
  have e' := cC_next_slot X Y m e hm hW j hj
  have key : ∀ (f : ℕ → Plane), (∀ i, i ≤ 6 → f i ∈ polygon (tIIR X.length hA)) →
      (∀ i, 1 ≤ i → i ≤ 5 → f i ∈ interior (polygon (tIIR X.length hA))) →
      SegIn (tIIR X.length hA) (if e then f j else f (6 - j)) (if e then f (j + 1) else f (6 - (j + 1))) := by
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
  · show SegIn _ (cMv X Y m _) (cMv X Y m (next hW _))
    rw [e', cC_mv_slot X Y m t e hm hW ht he j (by omega), cC_mv_slot X Y m t e hm hW ht he (j + 1) (by omega)]
    exact key _ (pvB2_mem _ _) (pvB2_int _ _)
  · show SegIn _ (pt .std Vc _) (pt .std Vc (next hW _).1)
    rw [e', cC_pt_slot X Y m t e hm hW ht he j (by omega), cC_pt_slot X Y m t e hm hW ht he (j + 1) (by omega)]
    exact key _ (pvB2_mem _ _) (pvB2_int _ _)

theorem cT_vert : ∀ j, 0 < j → j < 3 → cMv X Y m ((cT X Y m t hm hW).slot hW j) ∈ interior (polygon (tIIR X.length hA)) ∧
    pt .std Vc ((cT X Y m t hm hW).slot hW j).1 ∈ interior (polygon (tIIR X.length hA)) := by
  intro j h0 hj
  rw [cT_mv_slot X Y m t e hm hW ht he j (by omega), cT_pt_slot X Y m t e hm hW ht he j (by omega)]
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨mvA_intR _ _ _ (by omega) (by omega), pvA2_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨mvA_intR _ _ _ (by omega) (by omega), pvA2_int _ _ _ (by omega) (by omega)⟩

theorem cC_vert : ∀ j, 0 < j → j < 6 → cMv X Y m ((cC X Y m e hm hW).slot hW j) ∈ interior (polygon (tIIR X.length hA)) ∧
    pt .std Vc ((cC X Y m e hm hW).slot hW j).1 ∈ interior (polygon (tIIR X.length hA)) := by
  intro j h0 hj
  rw [cC_mv_slot X Y m t e hm hW ht he j (by omega), cC_pt_slot X Y m t e hm hW ht he j (by omega)]
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨pvB2_int _ _ _ (by omega) (by omega), pvB2_int _ _ _ (by omega) (by omega)⟩
  · simp only [↓reduceIte]
    exact ⟨pvB2_int _ _ _ (by omega) (by omega), pvB2_int _ _ _ (by omega) (by omega)⟩

omit hW ht he in
theorem c_moved : ∀ u : Slot Vc, cMv X Y m u = pt .std Vc u.1 ∨
    (cMv X Y m u ∈ interior (polygon (tIIR X.length hA)) ∧ pt .std Vc u.1 ∈ interior (polygon (tIIR X.length hA))) := by
  intro u
  by_cases hmv : IsMovedC X.length m u.1
  · right
    unfold IsMovedC at hmv
    rcases hmv with e' | e'
    · have h2 : pt .std Vc (X.length + 1, m) = pvA2 X.length hA 1 := c_pt_T X Y m hm 1 (by norm_num)
      rw [c_mv_T X Y m hm 1 (by norm_num) u e', e', h2]
      exact ⟨mvA_intR _ _ _ (by norm_num) (by norm_num), pvA2_int _ _ _ (by norm_num) (by norm_num)⟩
    · have h2 : pt .std Vc (X.length + 2, m + 1) = pvA2 X.length hA 2 := c_pt_T X Y m hm 2 (by norm_num)
      rw [c_mv_T X Y m hm 2 (by norm_num) u e', e', h2]
      exact ⟨mvA_intR _ _ _ (by norm_num) (by norm_num), pvA2_int _ _ _ (by norm_num) (by norm_num)⟩
  · left
    rw [cMv_apply, mvIIc_of_not_moved _ _ _ _ hmv]

/-- the chain slot carrying the through-vertex `tvT2 i` -/
theorem cT_chain_of (i : ℕ) (hi : i ≤ 3) {u : Slot Vc} (hu : u.1 = tvT2 X.length m i)
    (hd : (t = true ∧ i < 3) ∨ (t = false ∧ 0 < i)) : OnChain hW (cT X Y m t hm hW) u := by
  cases t
  · refine ⟨3 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · show 3 - i < 3; omega
    · rw [cT_slot_val X Y m false e hm hW ht he (3 - i) (by omega), hu]
      simp only [tvTd2, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [cT_slot_val X Y m true e hm hW ht he i hi, hu]
      simp only [tvTd2, ↓reduceIte]

/-- the chain slot carrying the cusp-arc vertex `tvC2 i` -/
theorem cC_chain_of (i : ℕ) (hi : i ≤ 6) {u : Slot Vc} (hu : u.1 = tvC2 X.length m i)
    (hd : (e = true ∧ i < 6) ∨ (e = false ∧ 0 < i)) : OnChain hW (cC X Y m e hm hW) u := by
  cases e
  · refine ⟨6 - i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · show 6 - i < 6; omega
    · rw [cC_slot_val X Y m t false hm hW ht he (6 - i) (by omega), hu]
      simp only [tvCd2, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
  · refine ⟨i, ?_, Subtype.ext ?_⟩
    · rcases hd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    · rw [cC_slot_val X Y m t true hm hW ht he i hi, hu]
      simp only [tvCd2, ↓reduceIte]

omit hm ht he in
/-- an unchanged spectator piece with an explicit outside witness -/
theorem c_spec {u : Slot Vc} {j p j' p' : ℕ} (hu : u.1 = (j, p)) (hn : (next hW u).1 = (j', p'))
    (hp : p ≠ 0) (hp' : p' ≠ 0) (h1 : ¬ IsMovedC X.length m (j, p)) (h2 : ¬ IsMovedC X.length m (j', p'))
    (hout : SegOut (tIIR X.length hA) ((j : ℝ), -(p : ℝ)) ((j' : ℝ), -(p' : ℝ))) :
    Unch .std hW (cMv X Y m) u ∧ PieceOut (tIIR X.length hA) hW (ptv .std) u := by
  constructor
  · constructor
    · rw [cMv_apply, mvIIc_of_not_moved _ _ _ _ (hu ▸ h1)]
    · rw [cMv_apply, mvIIc_of_not_moved _ _ _ _ (hn ▸ h2)]
  · show SegOut _ (pt .std Vc u.1) (pt .std Vc (next hW u).1)
    rw [hu, hn, std_pt_cut _ hp, std_pt_cut _ hp']
    exact hout

omit hm hW ht he in
theorem c_hmv : ∀ v : Slot Vc, ExtSl X.length (X.length + 3) v.1 → cMv X Y m v = pt .std Vc v.1 :=
  fun v hv => by rw [cMv_apply]; exact mvIIc_of_ext _ _ _ _ hv

/-- THE CLASSIFICATION of the type-II variant (c). -/
theorem c_rest : ∀ u : Slot Vc, OnChain hW (cT X Y m t hm hW) u ∨ OnChain hW (cC X Y m e hm hW) u ∨
    (Unch .std hW (cMv X Y m) u ∧ PieceOut (tIIR X.length hA) hW (ptv .std) u) := by
  intro u
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  have above : ∀ {q : ℕ}, q < m - 1 → hA + 1 ≤ -(q : ℝ) := fun {q} hq => by
    have : (q : ℝ) + 2 ≤ m := by exact_mod_cast (by omega : q + 2 ≤ m)
    linarith
  have below : ∀ {q : ℕ}, m + 2 ≤ q → -(q : ℝ) ≤ hA - 3 := fun {q} hq => by
    have : (m : ℝ) + 2 ≤ q := by exact_mod_cast hq
    linarith
  have slant : ∀ {q : ℕ}, m ≤ q → -(q : ℝ) ≤ hA - 1 := fun {q} hq => by
    have : (m : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have chainT := cT_chain_of X Y m t e hm hW ht he
  have chainC := cC_chain_of X Y m t e hm hW ht he
  have nm : ∀ a b : ℕ, (a ≠ X.length + 1 ∨ b ≠ m) → (a ≠ X.length + 2 ∨ b ≠ m + 1) → ¬ IsMovedC X.length m (a, b) := by
    intro a b h1 h2 h
    unfold IsMovedC at h
    simp only [Prod.mk.injEq] at h
    omega
  by_cases hext : ExtCol X Pc (colOf u)
  · right; right
    have hext' := (c_extCol X m _).1 hext
    exact ⟨unch_of_extCol .std hW _ (c_hmv X Y m) hext',
      pieceOut_of_extCol _ .std hW _ (tIIR_xge_mem _ _) (tIIR_xle_mem _ _) (unch_pt _ _ _) hext'⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, c_extCol] at hext
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
  cases hb : bit Vc j p
  · -- leftward pieces
    rw [block_col_false hu hp hb, c_extCol] at hext
    have : j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    rcases this with rfl | rfl | rfl
    · -- cut `|X|+1`, column `|X|`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := c_A13 X Y m hW hu hp hb hpm
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hee : e = false := by rw [hpe, C3] at hb; exact hb
          exact Or.inr (Or.inl (chainC 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
        · have htt : t = false := by rw [hpe, C4] at hb; exact hb
          exact Or.inl (chainT 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
        · have hee : e = true := by rw [hpe, C5] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := c_A16 X Y m hm hW hu hp hb (by omega)
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_below _ _ (below hpm2) _ _)))
    · -- cut `|X|+2`, column `|X|+1`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := c_A17 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hee : e = false := by rw [hpe, he] at hb; exact hb
          exact Or.inr (Or.inl (chainC 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
        · have hee : e = true := by rw [hpe, C7] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
        · have htt : t = false := by rw [hpe, C8] at hb; exact hb
          exact Or.inl (chainT 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := c_A20 X Y m hW hu hp hb hpm2
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_below _ _ (below hpm2) _ _)))
    · -- cut `|X|+3`, column `|X|+2`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := c_A21 X Y m hW hu hp hb hpm
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
      · have htt : t = false := by rw [← hpe] at hb; rw [← C9]; exact hb
        exact Or.inl (chainT 3 (by norm_num) (by rw [hu, ← hpe]; rfl) (Or.inr ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := c_A22 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp (by omega) (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_slant' _ _ (slant (by omega)))))
  · -- rightward pieces
    rw [block_col_true hu hp hb, c_extCol] at hext
    have : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · -- cut `|X|`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := c_A1 X Y m hW hu hp hb hpm
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have htt : t = true := by rw [hpe] at hb; rw [← ht]; exact hb
          exact Or.inl (chainT 0 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
        · have hee : e = true := by rw [hpe, C1] at hb; exact hb
          exact Or.inr (Or.inl (chainC 0 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
        · have hee : e = false := by rw [hpe, C2] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 6 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := c_A4 X Y m hm hW hu hp hb (by omega)
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_below _ _ (below hpm2) _ _)))
    · -- cut `|X|+1`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := c_A5 X Y m hW hu hp hb (by omega)
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hee : e = true := by rw [hpe, C3] at hb; exact hb
          exact Or.inr (Or.inl (chainC 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
        · have htt : t = true := by rw [hpe, C4] at hb; exact hb
          exact Or.inl (chainT 1 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
        · have hee : e = false := by rw [hpe, C5] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 5 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
      · obtain ⟨h1, -⟩ := c_A8 X Y m hW hu hp hb hpm2
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_below _ _ (below hpm2) _ _)))
    · -- cut `|X|+2`
      rcases lt_or_ge p (m - 1) with hpm | hpm
      · obtain ⟨h1, -⟩ := c_A9 X Y m hW hu hp hb hpm
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp hp (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_above _ _ (above hpm) _ _)))
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
        rcases this with hpe | hpe | hpe
        · have hee : e = true := by rw [hpe] at hb; rw [← he]; exact hb
          exact Or.inr (Or.inl (chainC 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨hee, by norm_num⟩)))
        · have hee : e = false := by rw [hpe, C7] at hb; simpa using hb
          exact Or.inr (Or.inl (chainC 4 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inr ⟨hee, by norm_num⟩)))
        · have htt : t = true := by rw [hpe, C8] at hb; exact hb
          exact Or.inl (chainT 2 (by norm_num) (by rw [hu, hpe]; rfl) (Or.inl ⟨htt, by norm_num⟩))
      · obtain ⟨h1, -⟩ := c_A11 X Y m hm hW hu hp hb (by omega)
        exact Or.inr (Or.inr (c_spec X Y m hW hu h1 hp (by omega) (nm _ _ (by omega) (by omega))
          (nm _ _ (by omega) (by omega)) (tIIR_out_slant _ _ (by omega) (slant (q := p - 2) (by omega)))))

end TypeIIcSpec

/-! #### G5. The type-II variant (c): the remaining specification fields -/

section TypeIIcSpec2

open U3

variable (X Y : Word) (m : ℕ) (t e : Bool) (hm : 2 ≤ m)
  (hW : (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y) X.length (m - 1) = t)
  (he : bit (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y) (X.length + 2) (m - 1) = e)

local notation "Vc" => X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y
local notation "Pc" => [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)]
local notation "Vc'" => X ++ [Letter.r m] ++ Y
local notation "Pc'" => [Letter.r m]
local notation "hA" => (-(m : ℝ) + 1)

include hm hW ht he

theorem cT_slot_ne : ∀ j j', j ≤ 3 → j' ≤ 3 → j ≠ j' → (cT X Y m t hm hW).slot hW j ≠ (cT X Y m t hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [cT_slot_val X Y m t e hm hW ht he j hj, cT_slot_val X Y m t e hm hW ht he j' hj'] at h'
  cases t
  · simp only [tvTd2, Bool.false_eq_true, ↓reduceIte] at h'
    have := tvT2_inj X m (3 - j) (3 - j') (by omega) (by omega) h'
    omega
  · simp only [tvTd2, ↓reduceIte] at h'
    exact hne (tvT2_inj X m j j' hj hj' h')

theorem cC_slot_ne : ∀ j j', j ≤ 6 → j' ≤ 6 → j ≠ j' → (cC X Y m e hm hW).slot hW j ≠ (cC X Y m e hm hW).slot hW j' := by
  intro j j' hj hj' hne h
  have h' := congrArg Subtype.val h
  rw [cC_slot_val X Y m t e hm hW ht he j hj, cC_slot_val X Y m t e hm hW ht he j' hj'] at h'
  cases e
  · simp only [tvCd2, Bool.false_eq_true, ↓reduceIte] at h'
    have := tvC2_inj X m hm (6 - j) (6 - j') (by omega) (by omega) h'
    omega
  · simp only [tvCd2, ↓reduceIte] at h'
    exact hne (tvC2_inj X m hm j j' hj hj' h')

theorem c_disj : ∀ j j', j ≤ 3 → j' ≤ 6 → (cT X Y m t hm hW).slot hW j ≠ (cC X Y m e hm hW).slot hW j' := by
  intro j j' hj hj' h
  have h' := congrArg Subtype.val h
  rw [cT_slot_val X Y m t e hm hW ht he j hj, cC_slot_val X Y m t e hm hW ht he j' hj'] at h'
  cases t <;> cases e <;> simp only [tvTd2, tvCd2, Bool.false_eq_true, ↓reduceIte] at h' <;>
    exact tvT2_ne_tvC2 X m hm _ _ (by omega) (by omega) h'

theorem c_prevOut₁ : Unch .std hW (cMv X Y m) (prev hW (cT X Y m t hm hW).u₀) ∧
    PieceOut (tIIR X.length hA) hW (ptv .std) (prev hW (cT X Y m t hm hW).u₀) := by
  rcases c_rest X Y m t e hm hW ht he (prev hW (cT X Y m t hm hW).u₀) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · exfalso
    have hj' : j < 3 := hj
    have : (cT X Y m t hm hW).slot hW (j + 1) = (cT X Y m t hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact cT_slot_ne X Y m t e hm hW ht he (j + 1) 0 (by omega) (by omega) (by omega) this
  · exfalso
    have hj' : j < 6 := hj
    have : (cC X Y m e hm hW).slot hW (j + 1) = (cT X Y m t hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact c_disj X Y m t e hm hW ht he 0 (j + 1) (by omega) (by omega) this.symm
  · exact h

theorem c_stopOut₁ : Unch .std hW (cMv X Y m) ((cT X Y m t hm hW).slot hW 3) ∧
    PieceOut (tIIR X.length hA) hW (ptv .std) ((cT X Y m t hm hW).slot hW 3) := by
  rcases c_rest X Y m t e hm hW ht he ((cT X Y m t hm hW).slot hW 3) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · have hj' : j < 3 := hj
    exact absurd hjs (cT_slot_ne X Y m t e hm hW ht he j 3 (by omega) le_rfl (by omega))
  · have hj' : j < 6 := hj
    exact absurd hjs.symm (c_disj X Y m t e hm hW ht he 3 j le_rfl (by omega))
  · exact h

theorem c_prevOut₂ : Unch .std hW (cMv X Y m) (prev hW (cC X Y m e hm hW).u₀) ∧
    PieceOut (tIIR X.length hA) hW (ptv .std) (prev hW (cC X Y m e hm hW).u₀) := by
  rcases c_rest X Y m t e hm hW ht he (prev hW (cC X Y m e hm hW).u₀) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · exfalso
    have hj' : j < 3 := hj
    have : (cT X Y m t hm hW).slot hW (j + 1) = (cC X Y m e hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact c_disj X Y m t e hm hW ht he (j + 1) 0 (by omega) (by omega) this
  · exfalso
    have hj' : j < 6 := hj
    have : (cC X Y m e hm hW).slot hW (j + 1) = (cC X Y m e hm hW).slot hW 0 := by
      rw [Chain.slot_succ, hjs, Chain.slot_zero, next_prev]
    exact cC_slot_ne X Y m t e hm hW ht he (j + 1) 0 (by omega) (by omega) (by omega) this
  · exact h

theorem c_stopOut₂ : Unch .std hW (cMv X Y m) ((cC X Y m e hm hW).slot hW 6) ∧
    PieceOut (tIIR X.length hA) hW (ptv .std) ((cC X Y m e hm hW).slot hW 6) := by
  rcases c_rest X Y m t e hm hW ht he ((cC X Y m e hm hW).slot hW 6) with ⟨j, hj, hjs⟩ | ⟨j, hj, hjs⟩ | h
  · have hj' : j < 3 := hj
    exact absurd hjs (c_disj X Y m t e hm hW ht he j 6 (by omega) le_rfl)
  · have hj' : j < 6 := hj
    exact absurd hjs (cC_slot_ne X Y m t e hm hW ht he j 6 (by omega) le_rfl (by omega))
  · exact h

omit hW ht he in
/-- a grid point of the disc is a vertex of one of the two arcs -/
theorem c_vertex_of_mem {u : Slot Vc} (hmem : pt .std Vc u.1 ∈ polygon (tIIR X.length hA)) :
    (∃ i, i ≤ 3 ∧ u.1 = tvT2 X.length m i) ∨ (∃ i, i ≤ 6 ∧ u.1 = tvC2 X.length m i) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
  obtain ⟨j, p, hu⟩ : ∃ j p, u.1 = (j, p) := ⟨_, _, rfl⟩
  rw [hu] at hmem
  by_cases hp : p = 0
  · subst hp
    rw [std_pt_cusp] at hmem
    obtain ⟨b1, b2, -, -, -⟩ := tIIR_mem_bounds X.length hA hmem
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
    obtain ⟨b1, b2, b3, b4, b5⟩ := tIIR_mem_bounds X.length hA hmem
    have e1 : X.length ≤ j := by exact_mod_cast b1
    have e2 : j ≤ X.length + 3 := by exact_mod_cast (by linarith : (j : ℝ) ≤ X.length + 3)
    have e3 : 2 * p ≤ 2 * m + 3 := by exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 2 * m + 3)
    have e4 : 4 * m ≤ 4 * p + 7 := by exact_mod_cast (by linarith : (4 * m : ℝ) ≤ 4 * p + 7)
    have e5 : 4 * p + 8 * j + 1 ≤ 4 * m + 8 * X.length + 24 := by
      exact_mod_cast (by linarith : (4 * p + 8 * j + 1 : ℝ) ≤ 4 * m + 8 * X.length + 24)
    have hj : j = X.length ∨ j = X.length + 1 ∨ j = X.length + 2 ∨ j = X.length + 3 := by omega
    have hpp : p = m - 1 ∨ p = m ∨ p = m + 1 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inl ⟨0, by norm_num, hu⟩
      · exact Or.inr ⟨0, by norm_num, hu⟩
      · exact Or.inr ⟨6, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inr ⟨1, by norm_num, hu⟩
      · exact Or.inl ⟨1, by norm_num, hu⟩
      · exact Or.inr ⟨5, by norm_num, hu⟩
    · rcases hpp with rfl | rfl | rfl
      · exact Or.inr ⟨2, by norm_num, hu⟩
      · exact Or.inr ⟨4, by norm_num, hu⟩
      · exact Or.inl ⟨2, by norm_num, hu⟩
    · have : p = m - 1 := by omega
      exact Or.inl ⟨3, by norm_num, by rw [hu, this]; rfl⟩

theorem c_touch : ∀ u : Slot Vc, PieceOut (tIIR X.length hA) hW (ptv .std) u → pt .std Vc u.1 ∈ polygon (tIIR X.length hA) →
    u = (cT X Y m t hm hW).slot hW 3 ∨ u = (cC X Y m e hm hW).slot hW 6 := by
  intro u hout hmem
  have hchainT : ∀ j', j' < 3 → u ≠ (cT X Y m t hm hW).slot hW j' := by
    intro j' hj' he'
    rw [he'] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (cT_chain_in X Y m t e hm hW ht he j' hj').2
  have hchainC : ∀ j', j' < 6 → u ≠ (cC X Y m e hm hW).slot hW j' := by
    intro j' hj' he'
    rw [he'] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (cC_chain_in X Y m t e hm hW ht he j' hj').2
  rcases c_vertex_of_mem X Y m hm hmem with ⟨i, hi, hu⟩ | ⟨i, hi, hu⟩
  · left
    have hs := cT_slot_val X Y m t e hm hW ht he
    cases t
    · have hu' : u = (cT X Y m false hm hW).slot hW (3 - i) := by
        apply Subtype.ext
        rw [hs (3 - i) (by omega), hu]
        simp only [tvTd2, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact hu'
      · exact absurd hu' (hchainT (3 - i) (by omega))
    · have hu' : u = (cT X Y m true hm hW).slot hW i := by
        apply Subtype.ext
        rw [hs i hi, hu]
        simp only [tvTd2, ↓reduceIte]
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact absurd hu' (hchainT i h3)
      · have : i = 3 := by omega
        subst this
        exact hu'
  · right
    have hs := cC_slot_val X Y m t e hm hW ht he
    cases e
    · have hu' : u = (cC X Y m false hm hW).slot hW (6 - i) := by
        apply Subtype.ext
        rw [hs (6 - i) (by omega), hu]
        simp only [tvCd2, Bool.false_eq_true, ↓reduceIte, Nat.sub_sub_self hi]
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact hu'
      · exact absurd hu' (hchainC (6 - i) (by omega))
    · have hu' : u = (cC X Y m true hm hW).slot hW i := by
        apply Subtype.ext
        rw [hs i hi, hu]
        simp only [tvCd2, ↓reduceIte]
      rcases Nat.lt_or_ge i 6 with h6 | h6
      · exact absurd hu' (hchainC i h6)
      · have : i = 6 := by omega
        subst this
        exact hu'

omit hm ht he in
theorem c_exits : ∀ u : Slot Vc, ∃ v, (nextPerm hW).SameCycle u v ∧ Unch .std hW (cMv X Y m) v ∧
    PieceOut (tIIR X.length hA) hW (ptv .std) v := by
  intro u
  have hno : ∀ k', X.length ≤ k' → k' < X.length + 3 → ∀ m' d', letterAt Vc k' ≠ .l m' d' := by
    intro k' h1 h2 m' d'
    obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
    have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [hℓ₀]; exact fun h => by cases h
    · rw [hℓ₁]; exact fun h => by cases h
    · rw [hℓ₂]; exact fun h => by cases h
  obtain ⟨v, hsc, hcol⟩ := exists_ext_of_no_l hW X.length (X.length + 3) hno u
  exact ⟨v, hsc, unch_of_extCol .std hW _ (c_hmv X Y m) hcol,
    pieceOut_of_extCol _ .std hW _ (tIIR_xge_mem _ _) (tIIR_xle_mem _ _) (unch_pt _ _ _) hcol⟩

omit hm hW ht he in
/-- the crossing letters of the block: `σ_{m−1}` at column `|X|`, `σ_m` at column `|X|+1` -/
theorem c_σcol {k' m' : ℕ} (hℓ : letterAt Vc k' = .σ m') (hext : ¬ ExtCol X Pc k') :
    (k' = X.length ∧ m - 1 = m') ∨ (k' = X.length + 1 ∧ m = m') := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
  rw [c_extCol] at hext
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀] at hℓ; exact Or.inl ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [hℓ₁] at hℓ; exact Or.inr ⟨rfl, Letter.σ.inj hℓ⟩
  · rw [hℓ₂] at hℓ; cases hℓ

/-- the over strand of each block crossing lies on the through-strand -/
theorem c_σA_chain {k' m' : ℕ} (hk : k' < (Vc).length) (hℓ : letterAt Vc k' = .σ m') (hext : ¬ ExtCol X Pc k') :
    OnChain hW (cT X Y m t hm hW) (σSlotA hW hk hℓ) := by
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  have hv := σSlotA_val hW hk hℓ
  rcases c_σcol X Y m hℓ hext with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [ht, show m - 1 + 1 = m by omega] at hv
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact cT_chain_of X Y m false e hm hW ht he 1 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact cT_chain_of X Y m true e hm hW ht he 0 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · rw [C4] at hv
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact cT_chain_of X Y m false e hm hW ht he 2 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact cT_chain_of X Y m true e hm hW ht he 1 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

theorem c_hK : ∀ (k' m' : ℕ) (hk : k' < (Vc).length) (hℓ : letterAt Vc k' = .σ m'),
    ExtCol X Pc k' ↔ Unch .std hW (cMv X Y m) (σSlotA hW hk hℓ) ∧ Unch .std hW (cMv X Y m) (σSlotB hW hk hℓ) := by
  intro k' m' hk hℓ
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  constructor
  · intro hext
    have hext' := (c_extCol X m k').1 hext
    exact ⟨unch_of_extCol .std hW _ (c_hmv X Y m) (by rw [(σSlotA_spec hW hk hℓ).1]; exact hext'),
      unch_of_extCol .std hW _ (c_hmv X Y m) (by rw [(σSlotB_spec hW hk hℓ).1]; exact hext')⟩
  · rintro ⟨hA', -⟩
    by_contra hext
    have hv := σSlotA_val hW hk hℓ
    rcases c_σcol X Y m hℓ hext with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- column `|X|`: the over slot is the entry of the through-strand or its first moved vertex
      rw [ht, show m - 1 + 1 = m by omega] at hv
      cases t
      · simp only [Bool.false_eq_true, ↓reduceIte] at hv
        have h1 := hA'.1
        have hv' : (σSlotA hW hk hℓ).1 = tvT2 X.length m 1 := hv
        rw [c_mv_T X Y m hm 1 (by norm_num) _ hv', hv', c_pt_T X Y m hm 1 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvA, pvA2] at this
        linarith
      · simp only [↓reduceIte] at hv
        have h2 := hA'.2
        have hn : (next hW (σSlotA hW hk hℓ)).1 = tvT2 X.length m 1 := c_A2 X Y m hm hW hv ht
        rw [c_mv_T X Y m hm 1 (by norm_num) _ hn, hn, c_pt_T X Y m hm 1 (by norm_num)] at h2
        have := congrArg Prod.snd h2
        simp only [mvA, pvA2] at this
        linarith
    · -- column `|X|+1`: the over slot is a moved through-vertex
      rw [C4] at hv
      have h1 := hA'.1
      cases t
      · simp only [Bool.false_eq_true, ↓reduceIte] at hv
        have hv' : (σSlotA hW hk hℓ).1 = tvT2 X.length m 2 := hv
        rw [c_mv_T X Y m hm 2 (by norm_num) _ hv', hv', c_pt_T X Y m hm 2 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvA, pvA2] at this
        linarith
      · simp only [↓reduceIte] at hv
        have hv' : (σSlotA hW hk hℓ).1 = tvT2 X.length m 1 := hv
        rw [c_mv_T X Y m hm 1 (by norm_num) _ hv', hv', c_pt_T X Y m hm 1 (by norm_num)] at h1
        have := congrArg Prod.snd h1
        simp only [mvA, pvA2] at this
        linarith

theorem c_hKout : ∀ (k' m' : ℕ) (hk : k' < (Vc).length) (hℓ : letterAt Vc k' = .σ m'),
    ExtCol X Pc k' ↔ PieceOut (tIIR X.length hA) hW (ptv .std) (σSlotA hW hk hℓ) := by
  intro k' m' hk hℓ
  constructor
  · intro hext
    exact pieceOut_of_extCol _ .std hW _ (tIIR_xge_mem _ _) (tIIR_xle_mem _ _) (unch_pt _ _ _)
      (by rw [(σSlotA_spec hW hk hℓ).1]; exact (c_extCol X m k').1 hext)
  · intro hout
    by_contra hext
    obtain ⟨j, hj, hjs⟩ := c_σA_chain X Y m t e hm hW ht he hk hℓ hext
    have hj' : j < 3 := hj
    rw [← hjs] at hout
    exact not_pieceIn_of_pieceOut _ _ _ hout (cT_chain_in X Y m t e hm hW ht he j hj').2

theorem c_cross : ∃ (k₁ m₁ : ℕ) (hk₁ : k₁ < (Vc).length) (hℓ₁ : letterAt Vc k₁ = .σ m₁) (k₂ m₂ : ℕ) (hk₂ : k₂ < (Vc).length)
    (hℓ₂ : letterAt Vc k₂ = .σ m₂), k₁ ≠ k₂ ∧ ¬ ExtCol X Pc k₁ ∧ ¬ ExtCol X Pc k₂ ∧
    (∀ (kk mm : ℕ) (_hk : kk < (Vc).length) (_hℓ : letterAt Vc kk = .σ mm), ¬ ExtCol X Pc kk → kk = k₁ ∨ kk = k₂) ∧
    ((OnChain hW (cT X Y m t hm hW) (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW (cT X Y m t hm hW) (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW (cC X Y m e hm hW) (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW (cC X Y m e hm hW) (σSlotB hW hk₂ hℓ₂)) ∨
     (OnChain hW (cC X Y m e hm hW) (σSlotA hW hk₁ hℓ₁) ∧ OnChain hW (cC X Y m e hm hW) (σSlotA hW hk₂ hℓ₂) ∧
      OnChain hW (cT X Y m t hm hW) (σSlotB hW hk₁ hℓ₁) ∧ OnChain hW (cT X Y m t hm hW) (σSlotB hW hk₂ hℓ₂))) := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := c_letters X Y m
  obtain ⟨C1, C2, C3, C4, C5, C7, C8, C9⟩ := c_bits X Y m t e hm hW ht he
  have hk₀ : X.length < (Vc).length := by rw [c_length]; omega
  have hk₁ : X.length + 1 < (Vc).length := by rw [c_length]; omega
  have hext₀ : ¬ ExtCol X Pc X.length := by rw [c_extCol]; omega
  have hext₁ : ¬ ExtCol X Pc (X.length + 1) := by rw [c_extCol]; omega
  refine ⟨X.length, m - 1, hk₀, hℓ₀, X.length + 1, m, hk₁, hℓ₁, by omega, hext₀, hext₁, ?_, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
  · intro kk mm _ hℓ hext
    rcases c_σcol X Y m hℓ hext with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · exact c_σA_chain X Y m t e hm hW ht he hk₀ hℓ₀ hext₀
  · exact c_σA_chain X Y m t e hm hW ht he hk₁ hℓ₁ hext₁
  · have hv := σSlotB_val hW hk₀ hℓ₀
    rw [show m - 1 + 1 = m by omega, C1] at hv
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact cC_chain_of X Y m t false hm hW ht he 1 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [↓reduceIte] at hv
      exact cC_chain_of X Y m t true hm hW ht he 0 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)
  · have hv := σSlotB_val hW hk₁ hℓ₁
    rw [C5] at hv
    cases e
    · simp only [Bool.not_false, ↓reduceIte] at hv
      exact cC_chain_of X Y m t false hm hW ht he 5 (by norm_num) hv (Or.inr ⟨rfl, by norm_num⟩)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
      exact cC_chain_of X Y m t true hm hW ht he 4 (by norm_num) hv (Or.inl ⟨rfl, by norm_num⟩)

/-- pieces of the through-strand never share a column -/
theorem c_pairs_TT : ∀ j j', j < 3 → j' < 3 → j ≠ j' →
    colOf ((cT X Y m t hm hW).slot hW j) = colOf ((cT X Y m t hm hW).slot hW j') → False := by
  intro j j' hj hj' hjj hc
  rw [cT_col X Y m t e hm hW ht he j hj, cT_col X Y m t e hm hW ht he j' hj'] at hc
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc
    interval_cases j <;> interval_cases j' <;> first | exact hjj rfl | (norm_num [colT] at hc <;> omega)
  · simp only [↓reduceIte] at hc
    interval_cases j <;> interval_cases j' <;> first | exact hjj rfl | (norm_num [colT] at hc <;> omega)

/-- the same-column pairs of a through-piece and a cusp-arc piece -/
theorem c_pairs_TC : ∀ j j', j < 3 → j' < 6 →
    colOf ((cT X Y m t hm hW).slot hW j) = colOf ((cC X Y m e hm hW).slot hW j') →
    MeetSpec .std hW (cMv X Y m) (ExtCol X Pc) ((cT X Y m t hm hW).slot hW j) ((cC X Y m e hm hW).slot hW j') := by
  intro j j' hj hj' hc
  rw [cT_col X Y m t e hm hW ht he j hj, cC_col X Y m t e hm hW ht he j' hj'] at hc
  have hnT := cT_next_slot X Y m t hm hW
  have hnC := cC_next_slot X Y m e hm hW
  have hmvT := cT_mv_slot X Y m t e hm hW ht he
  have hmvC := cC_mv_slot X Y m t e hm hW ht he
  cases t <;> cases e
  · -- `t = false`, `e = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 2 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (cII_NM_T2C3 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 3 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (cII_NM_T2C2 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (cII_NM_T1C4 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (cII_NM_T1C1 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 0 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (cII_NM_T0C5 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 5 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (cII_NM_T0C0 _ _).revl.revr
  · -- `t = false`, `e = true`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 2 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (cII_NM_T2C2 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 3 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (cII_NM_T2C3 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (cII_NM_T1C1 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (cII_NM_T1C4 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 0 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (cII_NM_T0C0 _ _).revl
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 5 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (cII_NM_T0C5 _ _).revl
  · -- `t = true`, `e = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 0 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (cII_NM_T0C5 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 5 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (cII_NM_T0C0 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (cII_NM_T1C4 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (cII_NM_T1C1 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 2 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (cII_NM_T2C3 _ _).revr
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 3 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (cII_NM_T2C2 _ _).revr
  · -- `t = true`, `e = true`
    simp only [↓reduceIte] at hc hmvT hmvC
    interval_cases j <;> interval_cases j' <;> first | (exfalso; norm_num [colT, colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 0 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 0 (by norm_num), hmvC (0 + 1) (by norm_num)]
      exact (cII_NM_T0C0 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 0 (by norm_num), hnC 5 (by norm_num), hmvT 0 (by norm_num), hmvT (0 + 1) (by norm_num),
        hmvC 5 (by norm_num), hmvC (5 + 1) (by norm_num)]
      exact (cII_NM_T0C5 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 1 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 1 (by norm_num), hmvC (1 + 1) (by norm_num)]
      exact (cII_NM_T1C1 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 1 (by norm_num), hnC 4 (by norm_num), hmvT 1 (by norm_num), hmvT (1 + 1) (by norm_num),
        hmvC 4 (by norm_num), hmvC (4 + 1) (by norm_num)]
      exact (cII_NM_T1C4 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 2 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 2 (by norm_num), hmvC (2 + 1) (by norm_num)]
      exact (cII_NM_T2C2 _ _)
    · apply meetSpec_of_noMeet
      rw [hnT 2 (by norm_num), hnC 3 (by norm_num), hmvT 2 (by norm_num), hmvT (2 + 1) (by norm_num),
        hmvC 3 (by norm_num), hmvC (3 + 1) (by norm_num)]
      exact (cII_NM_T2C3 _ _)

/-- the same-column pairs of two cusp-arc pieces -/
theorem c_pairs_CC : ∀ j j', j < 6 → j' < 6 → j ≠ j' →
    colOf ((cC X Y m e hm hW).slot hW j) = colOf ((cC X Y m e hm hW).slot hW j') →
    MeetSpec .std hW (cMv X Y m) (ExtCol X Pc) ((cC X Y m e hm hW).slot hW j) ((cC X Y m e hm hW).slot hW j') := by
  intro j j' hj hj' hjj hc
  rw [cC_col X Y m t e hm hW ht he j hj, cC_col X Y m t e hm hW ht he j' hj'] at hc
  have hn := cC_next_slot X Y m e hm hW
  have hmv := cC_mv_slot X Y m t e hm hW ht he
  cases e
  · -- `e = false`
    simp only [Bool.false_eq_true, ↓reduceIte] at hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact (cII_NM_C0C5 _ _).symm.revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact (cII_NM_C1C4 _ _).symm.revl.revr
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (cII_OJ234 _ _).rev
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact (cII_OJ234 _ _).rev
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (cII_NM_C1C4 _ _).revl.revr
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (cII_NM_C0C5 _ _).revl.revr
  · -- `e = true`
    simp only [↓reduceIte] at hmv
    interval_cases j <;> interval_cases j' <;> first | (exfalso; exact hjj rfl) | (exfalso; norm_num [colC2] at hc <;> omega) | skip
    · apply meetSpec_of_noMeet
      rw [hn 0 (by norm_num), hn 5 (by norm_num), hmv 0 (by norm_num), hmv (0 + 1) (by norm_num),
        hmv 5 (by norm_num), hmv (5 + 1) (by norm_num)]
      exact cII_NM_C0C5 _ _
    · apply meetSpec_of_noMeet
      rw [hn 1 (by norm_num), hn 4 (by norm_num), hmv 1 (by norm_num), hmv (1 + 1) (by norm_num),
        hmv 4 (by norm_num), hmv (4 + 1) (by norm_num)]
      exact cII_NM_C1C4 _ _
    · apply meetSpec_of_joint .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact cII_OJ234 _ _
    · apply meetSpec_of_joint' .std hW _ _ ((hn 2 (by norm_num)).symm)
      rw [hn (2 + 1) (by norm_num), hmv 2 (by norm_num), hmv (2 + 1) (by norm_num), hmv (2 + 1 + 1) (by norm_num)]
      exact cII_OJ234 _ _
    · apply meetSpec_of_noMeet
      rw [hn 4 (by norm_num), hn 1 (by norm_num), hmv 4 (by norm_num), hmv (4 + 1) (by norm_num),
        hmv 1 (by norm_num), hmv (1 + 1) (by norm_num)]
      exact (cII_NM_C1C4 _ _).symm
    · apply meetSpec_of_noMeet
      rw [hn 5 (by norm_num), hn 0 (by norm_num), hmv 5 (by norm_num), hmv (5 + 1) (by norm_num),
        hmv 0 (by norm_num), hmv (0 + 1) (by norm_num)]
      exact (cII_NM_C0C5 _ _).symm

theorem c_pairs : ∀ u v : Slot Vc, (OnChain hW (cT X Y m t hm hW) u ∨ OnChain hW (cC X Y m e hm hW) u) →
    (OnChain hW (cT X Y m t hm hW) v ∨ OnChain hW (cC X Y m e hm hW) v) →
    u ≠ v → colOf u = colOf v → MeetSpec .std hW (cMv X Y m) (ExtCol X Pc) u v := by
  intro u v hu hv hne hc
  rcases hu with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> rcases hv with ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩
  · exact (c_pairs_TT X Y m t e hm hW ht he j j' hj hj' (fun h => hne (by rw [h])) hc).elim
  · exact c_pairs_TC X Y m t e hm hW ht he j j' hj hj' hc
  · exact (c_pairs_TC X Y m t e hm hW ht he j' j hj' hj hc.symm).symm
  · exact c_pairs_CC X Y m t e hm hW ht he j j' hj hj' (fun h => hne (by rw [h])) hc

theorem c_genericData : GenericData .std hW (cMv X Y m) (ExtCol X Pc) :=
  genericData_of' (tIIR X.length hA) .std hW (cMv X Y m) (ExtCol X Pc)
    (fun u => OnChain hW (cT X Y m t hm hW) u ∨ OnChain hW (cC X Y m e hm hW) u)
    (mvIIc_injective _ _ _ m) (mvIIc_xcoord _ _ _ _ (by omega))
    (fun u => by
      rcases c_rest X Y m t e hm hW ht he u with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h)
    (fun u hu => by
      rcases hu with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact (cT_chain_in X Y m t e hm hW ht he j hj).1
      · exact (cC_chain_in X Y m t e hm hW ht he j hj).1)
    (c_pairs X Y m t e hm hW ht he)
    (fun k' m' hk hℓ hA' hB => (c_hK X Y m t e hm hW ht he k' m' hk hℓ).2 ⟨hA', hB⟩)

theorem c_riiSpec : RIISpec (tIIR X.length hA) .std hW (cMv X Y m) (ExtCol X Pc) (cT X Y m t hm hW) (cC X Y m e hm hW) where
  disc := tIIR_isDisc _ _
  hK := c_hK X Y m t e hm hW ht he
  hKout := c_hKout X Y m t e hm hW ht he
  moved := c_moved X Y m hm
  chain₁ := cT_chain_in X Y m t e hm hW ht he
  chain₂ := cC_chain_in X Y m t e hm hW ht he
  vert₁ := cT_vert X Y m t e hm hW ht he
  vert₂ := cC_vert X Y m t e hm hW ht he
  rest := c_rest X Y m t e hm hW ht he
  prevOut₁ := c_prevOut₁ X Y m t e hm hW ht he
  stopOut₁ := c_stopOut₁ X Y m t e hm hW ht he
  prevOut₂ := c_prevOut₂ X Y m t e hm hW ht he
  stopOut₂ := c_stopOut₂ X Y m t e hm hW ht he
  disj := fun j hj j' hj' => c_disj X Y m t e hm hW ht he j j' (Nat.le_of_lt hj) (Nat.le_of_lt hj')
  touch := c_touch X Y m t e hm hW ht he
  exits := c_exits X Y m hW
  cross := c_cross X Y m t e hm hW ht he

theorem c_riiData (hne : Vc ≠ []) :
    Nonempty (RIIData (polygon (tIIR X.length hA))
      (mvDiagram .std hW hne (cMv X Y m) (ExtCol X Pc) (c_genericData X Y m t e hm hW ht he)) (rlDiagram .std hW hne)) :=
  riiData_of hne (c_genericData X Y m t e hm hW ht he) (c_riiSpec X Y m t e hm hW ht he)

theorem c_recordIso (hne : Vc ≠ []) (W' : OWord) (hW'eq : W'.letters = Vc') :
    Nonempty (RecordIso (mvDiagram .std hW hne (cMv X Y m) (ExtCol X Pc) (c_genericData X Y m t e hm hW ht he)).record
      (realize W').diagram.record) := by
  have hW' : (Vc').Closed := by have := W'.closed; rwa [hW'eq] at this
  refine ⟨vertexMovedRecordIso' X Pc Y Pc' (by simp) (c_sameEffect X Y m hm hW) hW hW' .std hne _ _ _ _
    (slotDiagramData_of .std hW hne (cMv X Y m) (ExtCol X Pc) (c_genericData X Y m t e hm hW ht he) (c_hK X Y m t e hm hW ht he))
    (c_passage X Y m hm hW hW') (c_hexit X Y m hW) (c'_hexit X Y m hW') ?_ W' hW'eq (by simp)⟩
  intro k' hk1 hk2
  simp only [List.length_cons, List.length_nil] at hk2
  have : k' = X.length := by omega
  subst this
  rw [c'_letters X Y m]; rfl

omit hW ht he in
/-- LEAF CASE (type II, variant (c): `σ_{m−1} σ_m r_{m−1} ↦ r_m`). -/
theorem typeII_c {W W' : OWord} (hWeq : W.letters = Vc) (hW'eq : W'.letters = Vc') :
    ∃ D : Diagram, RII D (realize W).diagram ∧ Nonempty (RecordIso D.record (realize W').diagram.record) := by
  obtain ⟨Wl, hWl⟩ := W
  simp only at hWeq
  subst hWeq
  have hne : Vc ≠ [] := by simp
  rw [realize_eq_realizeAt ⟨_, hWl⟩ hne]
  exact ⟨mvDiagram .std hWl hne (cMv X Y m) (ExtCol X Pc) (c_genericData X Y m _ _ hm hWl rfl rfl),
    ⟨polygon (tIIR X.length hA), Or.inl (c_riiData X Y m _ _ hm hWl rfl rfl hne)⟩,
    c_recordIso X Y m _ _ hm hWl rfl rfl hne W' hW'eq⟩

end TypeIIcSpec2

/-! #### H1. The type-II variant (b): `l_{m+1} d σ_m σ_{m+1} ↦ l_m d`, the word level -/

/-- the through-strand's vertices (entry at cut `k`, index `m`): over both crossings, out at `(k+3, m+2)` -/
def tvT3 (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k, m)
  | 1 => (k + 1, m)
  | 2 => (k + 2, m + 1)
  | _ => (k + 3, m + 2)

/-- the cusp arc's vertices, from the lower arm `(k+3, m+1)` through the left cusp to the upper arm `(k+3, m)` -/
def tvC3 (k m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (k + 3, m + 1)
  | 1 => (k + 2, m + 2)
  | 2 => (k + 1, m + 2)
  | 3 => (k, 0)
  | 4 => (k + 1, m + 1)
  | 5 => (k + 2, m)
  | _ => (k + 3, m)

def tvTd3 (k m : ℕ) (t : Bool) (j : ℕ) : ℕ × ℕ := if t then tvT3 k m j else tvT3 k m (3 - j)
def tvCd3 (k m : ℕ) (d : Bool) (j : ℕ) : ℕ × ℕ := if d then tvC3 k m j else tvC3 k m (6 - j)

section TypeIIbWord

open U3

variable (X Y : Word) (m : ℕ) (d t : Bool) (hm : 1 ≤ m)
  (hW : (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y).Closed)
  (ht : bit (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y) X.length m = t)

local notation "Vb" => X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y
local notation "Pb" => [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)]
local notation "Vb'" => X ++ [Letter.l m d] ++ Y
local notation "Pb'" => [Letter.l m d]

theorem b_letters : letterAt Vb X.length = .l (m + 1) d ∧ letterAt Vb (X.length + 1) = .σ m ∧
    letterAt Vb (X.length + 2) = .σ (m + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have := letterAt_block X Pb Y (i := 0) (by simp); simpa using this
  · have := letterAt_block X Pb Y (i := 1) (by simp); simpa using this
  · have := letterAt_block X Pb Y (i := 2) (by simp); simpa using this

theorem b_length : (Vb).length = X.length + 3 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem b_extCol (k : ℕ) : ExtCol X Pb k ↔ k + 1 ≤ X.length ∨ X.length + 3 ≤ k := by
  unfold ExtCol; simp

theorem b_shift : shiftIdx X Pb Pb' (X.length + 3) = X.length + 1 := by
  unfold shiftIdx; simp

theorem b_cut_start : cut Vb' X.length = cut Vb X.length := by
  unfold cut
  rw [List.append_assoc, List.take_left' rfl, List.append_assoc, List.take_left' rfl]

theorem b_bit_start (p : ℕ) : bit Vb' X.length p = bit Vb X.length p := by
  rw [bit_eq, bit_eq, b_cut_start]

include hW

include hm in
theorem b_sameEffect : SameEffect X Pb Pb' :=
  sameEffect_of_replace X Pb Y Pb' hW (fun c c' h => run_typeII_l_right hm h)

include hm in
theorem b_cut_end : cut Vb' (X.length + 1) = cut Vb (X.length + 3) := by
  have hE := b_sameEffect X Y m d hm hW
  unfold SameEffect at hE
  unfold cut
  rw [List.take_left' (by simp), List.take_left' (by simp), hE]

include hm in
theorem b_bit_end (p : ℕ) : bit Vb' (X.length + 1) p = bit Vb (X.length + 3) p := by
  rw [bit_eq, bit_eq, b_cut_end X Y m d hm hW]

theorem b_cutlen : m + 2 ≤ (cut Vb (X.length + 1)).length ∧ (cut Vb (X.length + 2)).length = (cut Vb (X.length + 1)).length ∧
    (cut Vb (X.length + 3)).length = (cut Vb (X.length + 2)).length ∧ (cut Vb (X.length + 1)).length = (cut Vb X.length).length + 2 := by
  have hk₀ : X.length < (Vb).length := by rw [b_length]; omega
  have hk₁ : X.length + 1 < (Vb).length := by rw [b_length]; omega
  have hk₂ : X.length + 2 < (Vb).length := by rw [b_length]; omega
  obtain ⟨-, -, h3, -, -⟩ := σ_facts hW hk₁ (b_letters X Y m d).2.1
  obtain ⟨-, h2', h3', -, -⟩ := σ_facts hW hk₂ (b_letters X Y m d).2.2
  obtain ⟨D⟩ := decomp hW X.length hk₀
  have h1 := D.length_add
  have har : (letterAt Vb X.length).arity = 0 := by rw [(b_letters X Y m d).1]; rfl
  have hco : (letterAt Vb X.length).coarity = 2 := by rw [(b_letters X Y m d).1]; rfl
  rw [har, hco] at h1
  rw [show X.length + 1 + 1 = X.length + 2 from rfl] at h3
  rw [show X.length + 2 + 1 = X.length + 3 from rfl] at h3'
  exact ⟨by omega, h3, h3', by omega⟩

include hm ht in
/-- the bits: the arms carry `d`, `!d`; the through-strand carries `t` -/
theorem b_bits :
    bit Vb (X.length + 1) m = t ∧ bit Vb (X.length + 1) (m + 1) = d ∧ bit Vb (X.length + 1) (m + 2) = !d ∧
    bit Vb (X.length + 2) m = d ∧ bit Vb (X.length + 2) (m + 1) = t ∧ bit Vb (X.length + 2) (m + 2) = !d ∧
    bit Vb (X.length + 3) m = d ∧ bit Vb (X.length + 3) (m + 1) = !d ∧ bit Vb (X.length + 3) (m + 2) = t := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
  have hk₀ : X.length < (Vb).length := by rw [b_length]; omega
  have hk₁ : X.length + 1 < (Vb).length := by rw [b_length]; omega
  have hk₂ : X.length + 2 < (Vb).length := by rw [b_length]; omega
  obtain ⟨-, D2, D3⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, -, -, h4, h5⟩ := σ_facts hW hk₁ hℓ₁
  obtain ⟨-, -, -, h4', h5'⟩ := σ_facts hW hk₂ hℓ₂
  have D1 : bit Vb (X.length + 1) m = t := by
    rw [bit_succ_of_lt hW hk₀ hm (by rw [hℓ₀]; simp only [idx]; omega), ht]
  have D6 : bit Vb (X.length + 2) (m + 2) = !d := by
    have := bit_succ_of_ge hW hk₁ (p := m + 2) (by rw [hℓ₁]; simp only [idx, arity]; omega)
    rw [hℓ₁] at this
    simp only [coarity, arity] at this
    rw [show m + 2 + 2 - 2 = m + 2 by omega] at this
    rw [this, D3]
  have D4 : bit Vb (X.length + 2) m = d := by rw [h5, D2]
  have D5 : bit Vb (X.length + 2) (m + 1) = t := by rw [h4, D1]
  have D7 : bit Vb (X.length + 3) m = d := by
    rw [bit_succ_of_lt hW hk₂ (by omega) (by rw [hℓ₂]; simp only [idx]; omega), D4]
  have D8 : bit Vb (X.length + 3) (m + 1) = !d := by rw [h5', D6]
  have D9 : bit Vb (X.length + 3) (m + 2) = t := by rw [h4', D5]
  exact ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩

/-! the successor table (columns `|X|`: `l_{m+1}`, `|X|+1`: `σ_m`, `|X|+2`: `σ_{m+1}`) -/

theorem b_A1 {s : Slot Vb} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vb X.length p = true)
    (hpm : p < m + 1) : (next hW s).1 = (X.length + 1, p) ∧ bit Vb (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(b_letters X Y m d).1]; exact hpm)

theorem b_A2 {s : Slot Vb} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vb X.length p = true)
    (hpm : m + 1 ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Vb (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(b_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(b_letters X Y m d).1] at this

theorem b_A3 {s : Slot Vb} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vb (X.length + 1) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vb (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(b_letters X Y m d).2.1]; exact hpm)

theorem b_A4 {s : Slot Vb} (hs : s.1 = (X.length + 1, m)) (hb : bit Vb (X.length + 1) m = true) :
    (next hW s).1 = (X.length + 2, m + 1) :=
  next_σ_right_idx hW (b_letters X Y m d).2.1 hs hb

theorem b_A5 {s : Slot Vb} (hs : s.1 = (X.length + 1, m + 1)) (hb : bit Vb (X.length + 1) (m + 1) = true) :
    (next hW s).1 = (X.length + 2, m) :=
  next_σ_right_succ hW (b_letters X Y m d).2.1 hs hb

theorem b_A6 {s : Slot Vb} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vb (X.length + 1) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vb (X.length + 2) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(b_letters X Y m d).2.1]; simpa [idx, arity] using hpm)
  rw [(b_letters X Y m d).2.1] at this
  simpa [coarity, arity] using this

theorem b_A7 {s : Slot Vb} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vb (X.length + 2) p = true) (hpm : p < m + 1) :
    (next hW s).1 = (X.length + 3, p) ∧ bit Vb (X.length + 3) p = true :=
  next_right_lt hW hs hp hb (by rw [(b_letters X Y m d).2.2]; exact hpm)

theorem b_A8 {s : Slot Vb} (hs : s.1 = (X.length + 2, m + 1)) (hb : bit Vb (X.length + 2) (m + 1) = true) :
    (next hW s).1 = (X.length + 3, m + 2) :=
  next_σ_right_idx hW (b_letters X Y m d).2.2 hs hb

theorem b_A9 {s : Slot Vb} (hs : s.1 = (X.length + 2, m + 2)) (hb : bit Vb (X.length + 2) (m + 2) = true) :
    (next hW s).1 = (X.length + 3, m + 1) :=
  next_σ_right_succ hW (b_letters X Y m d).2.2 hs hb

theorem b_A10 {s : Slot Vb} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0)
    (hb : bit Vb (X.length + 2) p = true) (hpm : m + 3 ≤ p) :
    (next hW s).1 = (X.length + 3, p) ∧ bit Vb (X.length + 3) p = true := by
  have := next_right_ge hW hs hp hb (by rw [(b_letters X Y m d).2.2]; simp only [idx, arity]; omega)
  rw [(b_letters X Y m d).2.2] at this
  simpa [coarity, arity] using this

theorem b_A11 {s : Slot Vb} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vb (X.length + 1) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length, q) ∧ bit Vb X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (b_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem b_A12 {s : Slot Vb} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m + 1 ∨ q = m + 2)
    (hb : bit Vb (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (b_letters X Y m d).1 hs (by omega) hb

theorem b_A13 {s : Slot Vb} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vb (X.length + 1) q = false) (hqm : m + 3 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Vb X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (b_letters X Y m d).1]; simp only [idx, coarity]; omega)
  rw [Nat.add_sub_cancel, (b_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem b_A14 {s : Slot Vb} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m + 1 else m + 2) := by
  rw [next_cusp_l hW (b_letters X Y m d).1 hs]

theorem b_A15 {s : Slot Vb} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vb (X.length + 2) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vb (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e2, (b_letters X Y m d).2.1]; exact hqm)
  rwa [e2] at this

theorem b_A16 {s : Slot Vb} (hs : s.1 = (X.length + 2, m)) (hb : bit Vb (X.length + 2) m = false) :
    (next hW s).1 = (X.length + 1, m + 1) :=
  next_σ_left_idx hW (b_letters X Y m d).2.1 hs hb

theorem b_A17 {s : Slot Vb} (hs : s.1 = (X.length + 2, m + 1)) (hb : bit Vb (X.length + 2) (m + 1) = false) :
    (next hW s).1 = (X.length + 1, m) :=
  next_σ_left_succ hW (b_letters X Y m d).2.1 hs hb

theorem b_A18 {s : Slot Vb} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vb (X.length + 2) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vb (X.length + 1) q = false := by
  have e2 : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e2, (b_letters X Y m d).2.1]; simpa [idx, coarity] using hqm)
  rw [e2, (b_letters X Y m d).2.1] at this
  simpa [arity, coarity] using this

theorem b_A19 {s : Slot Vb} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vb (X.length + 3) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length + 2, q) ∧ bit Vb (X.length + 2) q = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_lt hW hs hq hb (by rw [e3, (b_letters X Y m d).2.2]; exact hqm)
  rwa [e3] at this

theorem b_A20 {s : Slot Vb} (hs : s.1 = (X.length + 3, m + 1)) (hb : bit Vb (X.length + 3) (m + 1) = false) :
    (next hW s).1 = (X.length + 2, m + 2) :=
  next_σ_left_idx hW (b_letters X Y m d).2.2 hs hb

theorem b_A21 {s : Slot Vb} (hs : s.1 = (X.length + 3, m + 2)) (hb : bit Vb (X.length + 3) (m + 2) = false) :
    (next hW s).1 = (X.length + 2, m + 1) :=
  next_σ_left_succ hW (b_letters X Y m d).2.2 hs hb

theorem b_A22 {s : Slot Vb} {q : ℕ} (hs : s.1 = (X.length + 3, q)) (hq : q ≠ 0)
    (hb : bit Vb (X.length + 3) q = false) (hqm : m + 3 ≤ q) :
    (next hW s).1 = (X.length + 2, q) ∧ bit Vb (X.length + 2) q = false := by
  have e3 : X.length + 3 - 1 = X.length + 2 := by omega
  have := next_left_ge hW hs hq hb (by rw [e3, (b_letters X Y m d).2.2]; simp only [idx, coarity]; omega)
  rw [e3, (b_letters X Y m d).2.2] at this
  simpa [arity, coarity] using this

theorem b_hexit : ∀ u : Slot Vb, ∃ n, ExtPiece X Pb Y ((next hW)^[n] u) := by
  apply hexit_of_no_r X Pb Y hW
  intro k' h1 h2 m'
  simp only [List.length_cons, List.length_nil] at h2
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
  have : k' = X.length ∨ k' = X.length + 1 ∨ k' = X.length + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hℓ₀]; exact fun h => by cases h
  · rw [hℓ₁]; exact fun h => by cases h
  · rw [hℓ₂]; exact fun h => by cases h

/-! the two chains -/

include hm in
theorem b_isSlot_T0 : IsSlot Vb (tvTd3 X.length m t 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := b_cutlen X Y m d hW
  have hlen := b_length X Y m d
  cases t
  · have e : tvTd3 X.length m false 0 = (X.length + 3, m + 2) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)
  · have e : tvTd3 X.length m true 0 = (X.length, m) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)

include hm in
theorem b_isSlot_C0 : IsSlot Vb (tvCd3 X.length m d 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := b_cutlen X Y m d hW
  have hlen := b_length X Y m d
  cases d
  · have e : tvCd3 X.length m false 0 = (X.length + 3, m) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)
  · have e : tvCd3 X.length m true 0 = (X.length + 3, m + 1) := rfl
    rw [e]; exact isSlot_cut (by omega) (by omega) (by omega)

include hm in
/-- the arc of the through-strand: three pieces -/
def bT : Chain Vb := ⟨⟨tvTd3 X.length m t 0, b_isSlot_T0 X Y m d t hm hW⟩, 3, by norm_num⟩

include hm in
/-- the arc of the cusp: six pieces -/
def bC : Chain Vb := ⟨⟨tvCd3 X.length m d 0, b_isSlot_C0 X Y m d hm hW⟩, 6, by norm_num⟩

include hm ht in
theorem bT_slot_val : ∀ j, j ≤ 3 → ((bT X Y m d t hm hW).slot hW j).1 = tvTd3 X.length m t j := by
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  have s0 : ((bT X Y m d t hm hW).slot hW 0).1 = tvTd3 X.length m t 0 := rfl
  intro j hj
  cases t
  · simp only [tvTd3, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((bT X Y m d false hm hW).slot hW 1).1 = tvT3 X.length m 2 := by
      rw [Chain.slot_succ]; exact b_A21 X Y m d hW s0 D9
    have s2 : ((bT X Y m d false hm hW).slot hW 2).1 = tvT3 X.length m 1 := by
      rw [Chain.slot_succ]; exact b_A17 X Y m d hW s1 D5
    have s3 : ((bT X Y m d false hm hW).slot hW 3).1 = tvT3 X.length m 0 := by
      rw [Chain.slot_succ]; exact (b_A11 X Y m d hW s2 (by omega) D1 (by omega)).1
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
  · simp only [tvTd3, ↓reduceIte] at s0 ⊢
    have s1 : ((bT X Y m d true hm hW).slot hW 1).1 = tvT3 X.length m 1 := by
      rw [Chain.slot_succ]; exact (b_A1 X Y m d hW s0 (by omega) ht (by omega)).1
    have s2 : ((bT X Y m d true hm hW).slot hW 2).1 = tvT3 X.length m 2 := by
      rw [Chain.slot_succ]; exact b_A4 X Y m d hW s1 D1
    have s3 : ((bT X Y m d true hm hW).slot hW 3).1 = tvT3 X.length m 3 := by
      rw [Chain.slot_succ]; exact b_A8 X Y m d hW s2 D5
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3

include hm ht in
theorem bC_slot_val : ∀ j, j ≤ 6 → ((bC X Y m d hm hW).slot hW j).1 = tvCd3 X.length m d j := by
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  have s0 : ((bC X Y m d hm hW).slot hW 0).1 = tvCd3 X.length m d 0 := rfl
  intro j hj
  cases d
  · simp only [tvCd3, Bool.false_eq_true, ↓reduceIte] at s0 ⊢
    have s1 : ((bC X Y m false hm hW).slot hW 1).1 = tvC3 X.length m 5 := by
      rw [Chain.slot_succ]; exact (b_A19 X Y m false hW s0 (by omega) D7 (by omega)).1
    have s2 : ((bC X Y m false hm hW).slot hW 2).1 = tvC3 X.length m 4 := by
      rw [Chain.slot_succ]; exact b_A16 X Y m false hW s1 D4
    have s3 : ((bC X Y m false hm hW).slot hW 3).1 = tvC3 X.length m 3 := by
      rw [Chain.slot_succ]; exact b_A12 X Y m false hW s2 (Or.inl rfl) D2
    have s4 : ((bC X Y m false hm hW).slot hW 4).1 = tvC3 X.length m 2 := by
      rw [Chain.slot_succ, b_A14 X Y m false hW s3]; rfl
    have s5 : ((bC X Y m false hm hW).slot hW 5).1 = tvC3 X.length m 1 := by
      rw [Chain.slot_succ]; exact (b_A6 X Y m false hW s4 (by omega) D3 le_rfl).1
    have s6 : ((bC X Y m false hm hW).slot hW 6).1 = tvC3 X.length m 0 := by
      rw [Chain.slot_succ]; exact b_A9 X Y m false hW s5 D6
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
  · simp only [tvCd3, ↓reduceIte] at s0 ⊢
    have s1 : ((bC X Y m true hm hW).slot hW 1).1 = tvC3 X.length m 1 := by
      rw [Chain.slot_succ]; exact b_A20 X Y m true hW s0 D8
    have s2 : ((bC X Y m true hm hW).slot hW 2).1 = tvC3 X.length m 2 := by
      rw [Chain.slot_succ]; exact (b_A18 X Y m true hW s1 (by omega) D6 le_rfl).1
    have s3 : ((bC X Y m true hm hW).slot hW 3).1 = tvC3 X.length m 3 := by
      rw [Chain.slot_succ]; exact b_A12 X Y m true hW s2 (Or.inr rfl) D3
    have s4 : ((bC X Y m true hm hW).slot hW 4).1 = tvC3 X.length m 4 := by
      rw [Chain.slot_succ, b_A14 X Y m true hW s3]; rfl
    have s5 : ((bC X Y m true hm hW).slot hW 5).1 = tvC3 X.length m 5 := by
      rw [Chain.slot_succ]; exact b_A5 X Y m true hW s4 D2
    have s6 : ((bC X Y m true hm hW).slot hW 6).1 = tvC3 X.length m 6 := by
      rw [Chain.slot_succ]; exact (b_A7 X Y m true hW s5 (by omega) D4 (by omega)).1
    interval_cases j
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6

include hm ht in
theorem bT_col : ∀ j, j < 3 → colOf ((bT X Y m d t hm hW).slot hW j) = if t then colT X.length j else colT X.length (2 - j) := by
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  have hv := bT_slot_val X Y m d t hm hW ht
  intro j hj
  cases t
  · simp only [tvTd3, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp) (by simpa [tvT3] using D9)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp) (by simpa [tvT3] using D5)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp; omega) (by simpa [tvT3] using D1)]; rfl
  · simp only [tvTd3, ↓reduceIte] at hv ⊢
    interval_cases j
    · rw [block_col_true (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvT3] using ht)]; rfl
    · rw [block_col_true (hv 1 (by norm_num)) (by simp; omega) (by simpa [tvT3] using D1)]; rfl
    · rw [block_col_true (hv 2 (by norm_num)) (by simp) (by simpa [tvT3] using D5)]; rfl

include hm ht in
theorem bC_col : ∀ j, j < 6 → colOf ((bC X Y m d hm hW).slot hW j) = colC X.length j := by
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  have hv := bC_slot_val X Y m d t hm hW ht
  intro j hj
  cases d
  · simp only [tvCd3, Bool.false_eq_true, ↓reduceIte] at hv
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp; omega) (by simpa [tvC3] using D7)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp; omega) (by simpa [tvC3] using D4)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp) (by simpa [tvC3] using D2)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_true (hv 4 (by norm_num)) (by simp) (by simpa [tvC3] using D3)]; rfl
    · rw [block_col_true (hv 5 (by norm_num)) (by simp) (by simpa [tvC3] using D6)]; rfl
  · simp only [tvCd3, ↓reduceIte] at hv
    interval_cases j
    · rw [block_col_false (hv 0 (by norm_num)) (by simp) (by simpa [tvC3] using D8)]; rfl
    · rw [block_col_false (hv 1 (by norm_num)) (by simp) (by simpa [tvC3] using D6)]; rfl
    · rw [block_col_false (hv 2 (by norm_num)) (by simp) (by simpa [tvC3] using D3)]; rfl
    · rw [block_col_vertex (hv 3 (by norm_num))]; rfl
    · rw [block_col_true (hv 4 (by norm_num)) (by simp) (by simpa [tvC3] using D2)]; rfl
    · rw [block_col_true (hv 5 (by norm_num)) (by simp; omega) (by simpa [tvC3] using D4)]; rfl

include hm ht in
theorem bT_col3 : ExtCol X Pb (colOf ((bT X Y m d t hm hW).slot hW 3)) := by
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  have hv := bT_slot_val X Y m d t hm hW ht 3 le_rfl
  rw [b_extCol]
  cases t
  · simp only [tvTd3, Bool.false_eq_true, ↓reduceIte, tvT3] at hv
    have hk := (cutSlot_facts hW hv (by omega)).2.2.1
    rw [block_col_false hv (by omega) ht]; omega
  · simp only [tvTd3, ↓reduceIte, tvT3] at hv
    rw [block_col_true hv (by omega) D9]; omega

include hm ht in
theorem bC_col6 : ExtCol X Pb (colOf ((bC X Y m d hm hW).slot hW 6)) := by
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d t hm hW ht
  have hv := bC_slot_val X Y m d t hm hW ht 6 le_rfl
  rw [b_extCol]
  cases d
  · simp only [tvCd3, Bool.false_eq_true, ↓reduceIte, tvC3] at hv
    rw [block_col_true hv (by omega) D8]; omega
  · simp only [tvCd3, ↓reduceIte, tvC3] at hv
    rw [block_col_true hv (by omega) D7]; omega

end TypeIIbWord

/-! #### H2. The type-II variant (b): the block passage (the target word `X ++ [l_m d] ++ Y` is that of variant (a)) -/

section TypeIIbPassage

open U3

variable (X Y : Word) (m : ℕ) (d t : Bool) (hm : 1 ≤ m)
  (hW : (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y).Closed)
  (hW' : (X ++ [Letter.l m d] ++ Y).Closed)

local notation "Vb" => X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y
local notation "Pb" => [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)]
local notation "Vb'" => X ++ [Letter.l m d] ++ Y
local notation "Pb'" => [Letter.l m d]

include hm hW hW'

/-- THE BLOCK PASSAGE of the type-II variant (b). -/
theorem b_passage : Passage X Pb Y Pb' hW hW' := by
  obtain ⟨hℓ₀, hℓ₁, hℓ₂⟩ := b_letters X Y m d
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ := b_bits X Y m d (bit Vb X.length m) hm hW rfl
  obtain ⟨B1', B2'⟩ := a'_bits X Y m d hW'
  have hP : Pb ≠ [] := by simp
  have hE := b_sameEffect X Y m d hm hW
  have shiftL : ∀ p, extPair X Pb Pb' (X.length, p) = (X.length, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pb Pb' le_rfl]
  have shiftR : ∀ p, extPair X Pb Pb' (X.length + 3, p) = (X.length + 1, p) := by
    intro p; simp only [extPair, b_shift X m d]
  constructor
  intro b hext hcol
  let b' : Slot Vb' := ⟨extPair X Pb Pb' b.1, isSlot_ext X Pb Y Pb' hP hE b.2 hext⟩
  have hb'v : b'.1 = extPair X Pb Pb' b.1 := rfl
  -- the through-strand, as the chain `bT` (with `t := bit Vb |X| m`)
  have curlT : b = (bT X Y m d (bit Vb X.length m) hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Vb), (next hW)^[n] b = c ∧ ExtCol X Pb (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pb (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot Vb'), b'.1 = extPair X Pb Pb' b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pb Pb' c.1 ∧ ∀ i < m', ¬ ExtCol X Pb' (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨3, (bT X Y m d _ hm hW).slot hW 3, by rw [hb]; rfl, bT_col3 X Y m d _ hm hW rfl, ?_, ?_⟩
    · intro i hi
      have h := bT_col X Y m d _ hm hW rfl i hi
      rw [hb]
      show ¬ ExtCol X Pb (colOf ((bT X Y m d _ hm hW).slot hW i))
      rw [h, b_extCol]
      cases bit Vb X.length m <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> interval_cases i <;> simp [colT]
    · have h0 := bT_slot_val X Y m d _ hm hW rfl 0 (by norm_num)
      have h3 := bT_slot_val X Y m d _ hm hW rfl 3 le_rfl
      rw [Chain.slot_zero] at h0
      cases hE0 : bit Vb X.length m
      · -- leftward: `W'`: `(|X|+1, m+2)` leftward under the cusp of `l_m d` to `(|X|, m)`
        rw [hE0] at h0 h3 hb
        have hb0 : b.1 = (X.length + 3, m + 2) := by rw [hb]; exact h0
        have hc3 : ((bT X Y m d false hm hW).slot hW 3).1 = (X.length, m) := h3
        have hslot : IsSlot Vb' (X.length + 1, m + 2) := by
          have := isSlot_ext X Pb Y Pb' hP hE (s := (X.length + 3, m + 2)) (hb0 ▸ b.2)
            (isExtSlot_cut_right X Pb (p := m + 2) (by omega))
          rwa [shiftR] at this
        have hbit' : bit Vb' (X.length + 1) (m + 2) = false := by rw [b_bit_end X Y m d hm hW, D9, hE0]
        refine ⟨1, ⟨(X.length + 1, m + 2), hslot⟩, by rw [hb0, shiftR], ?_, ?_⟩
        · rw [hc3, shiftL, Function.iterate_one]
          have := (a'_L5 X Y m d hW' (s := ⟨_, hslot⟩) (q := m + 2) rfl (by omega) hbit' le_rfl).1
          rwa [show m + 2 - 2 = m by omega] at this
        · intro i hi
          have : i = 0 := by omega
          subst this
          rw [Function.iterate_zero, id, block_col_false (s := ⟨_, hslot⟩) (k := X.length + 1) (p := m + 2) rfl (by omega) hbit',
            a'_extCol]; omega
      · rw [hE0] at h0 h3 hb
        have hb0 : b.1 = (X.length, m) := by rw [hb]; exact h0
        have hc3 : ((bT X Y m d true hm hW).slot hW 3).1 = (X.length + 3, m + 2) := h3
        have hslot : IsSlot Vb' (X.length, m) := by
          have := isSlot_ext X Pb Y Pb' hP hE (s := (X.length, m)) (hb0 ▸ b.2)
            (isExtSlot_cut_left X Pb (p := m) (by omega))
          rwa [shiftL] at this
        have hbit' : bit Vb' X.length m = true := by rw [b_bit_start, hE0]
        refine ⟨1, ⟨(X.length, m), hslot⟩, by rw [hb0, shiftL], ?_, ?_⟩
        · rw [hc3, shiftR, Function.iterate_one]
          exact (a'_L2 X Y m d hW' (s := ⟨_, hslot⟩) (p := m) rfl (by omega) hbit' le_rfl).1
        · intro i hi
          have : i = 0 := by omega
          subst this
          rw [Function.iterate_zero, id, block_col_true (s := ⟨_, hslot⟩) (k := X.length) (p := m) rfl (by omega) hbit',
            a'_extCol]; omega
  -- the cusp arc, as the chain `bC`
  have curlC : b = (bC X Y m d hm hW).u₀ →
      ∃ (n : ℕ) (c : Slot Vb), (next hW)^[n] b = c ∧ ExtCol X Pb (colOf c) ∧
        (∀ i < n, ¬ ExtCol X Pb (colOf ((next hW)^[i] b))) ∧
        ∃ (m' : ℕ) (b' : Slot Vb'), b'.1 = extPair X Pb Pb' b.1 ∧
          ((next hW')^[m'] b').1 = extPair X Pb Pb' c.1 ∧ ∀ i < m', ¬ ExtCol X Pb' (colOf ((next hW')^[i] b')) := by
    intro hb
    refine ⟨6, (bC X Y m d hm hW).slot hW 6, by rw [hb]; rfl, bC_col6 X Y m d _ hm hW rfl, ?_, ?_⟩
    · intro i hi
      have h := bC_col X Y m d _ hm hW rfl i hi
      rw [hb]
      show ¬ ExtCol X Pb (colOf ((bC X Y m d hm hW).slot hW i))
      rw [h, b_extCol]
      interval_cases i <;> simp [colC]
    · have h0 := bC_slot_val X Y m d _ hm hW rfl 0 (by norm_num)
      have h6 := bC_slot_val X Y m d _ hm hW rfl 6 le_rfl
      rw [Chain.slot_zero] at h0
      rcases Bool.eq_false_or_eq_true d with hd | hd
      · have hb0 : b.1 = (X.length + 3, m + 1) := by rw [hb, h0, hd]; rfl
        have hc6 : ((bC X Y m d hm hW).slot hW 6).1 = (X.length + 3, m) := by rw [h6, hd]; rfl
        have hslot : IsSlot Vb' (X.length + 1, m + 1) := by
          have := isSlot_ext X Pb Y Pb' hP hE (s := (X.length + 3, m + 1)) (hb0 ▸ b.2)
            (isExtSlot_cut_right X Pb (p := m + 1) (by omega))
          rwa [shiftR] at this
        have hbit' : bit Vb' (X.length + 1) (m + 1) = false := by rw [B2', hd]; rfl
        have h1' := a'_L4 X Y m d hW' (s := ⟨_, hslot⟩) rfl (Or.inr rfl) hbit'
        have h2' := a'_L6 X Y m d hW' h1'
        rw [ite_eq_left hd] at h2'
        refine ⟨2, ⟨_, hslot⟩, by rw [hb0, shiftR], ?_, ?_⟩
        · rw [hc6, shiftR, Function.iterate_succ_apply', Function.iterate_one, h2']
        · intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · rw [Function.iterate_zero, id, block_col_false (s := ⟨_, hslot⟩) (k := X.length + 1) (p := m + 1) rfl (by omega) hbit',
              a'_extCol]; omega
          · rw [Function.iterate_one, block_col_vertex h1', a'_extCol]; omega
      · have hb0 : b.1 = (X.length + 3, m) := by rw [hb, h0, hd]; rfl
        have hc6 : ((bC X Y m d hm hW).slot hW 6).1 = (X.length + 3, m + 1) := by rw [h6, hd]; rfl
        have hslot : IsSlot Vb' (X.length + 1, m) := by
          have := isSlot_ext X Pb Y Pb' hP hE (s := (X.length + 3, m)) (hb0 ▸ b.2)
            (isExtSlot_cut_right X Pb (p := m) (by omega))
          rwa [shiftR] at this
        have hbit' : bit Vb' (X.length + 1) m = false := by rw [B1', hd]
        have h1' := a'_L4 X Y m d hW' (s := ⟨_, hslot⟩) rfl (Or.inl rfl) hbit'
        have h2' := a'_L6 X Y m d hW' h1'
        rw [ite_eq_right (by simp [hd])] at h2'
        refine ⟨2, ⟨_, hslot⟩, by rw [hb0, shiftR], ?_, ?_⟩
        · rw [hc6, shiftR, Function.iterate_succ_apply', Function.iterate_one, h2']
        · intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · rw [Function.iterate_zero, id, block_col_false (s := ⟨_, hslot⟩) (k := X.length + 1) (p := m) rfl (by omega) hbit',
              a'_extCol]; omega
          · rw [Function.iterate_one, block_col_vertex h1', a'_extCol]; omega
  rcases (entry_iff X Pb Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hb'1 : b'.1 = (X.length, p) := by rw [hb'v, hb, shiftL]
    have hbit' : bit Vb' X.length p = true := by rw [b_bit_start, hbit]
    have hcol0 : ¬ ExtCol X Pb (colOf b) := by rw [block_col_true hb hp hbit, b_extCol]; omega
    have hcol0' : ¬ ExtCol X Pb' (colOf b') := by rw [block_col_true hb'1 hp hbit', a'_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := b_A1 X Y m d hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := b_A3 X Y m d hW h1 hp hb1 hpm
      obtain ⟨h3, hb3⟩ := b_A7 X Y m d hW h2 hp hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := a'_L1 X Y m d hW' hb'1 hp hbit' hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pb) hcol0
        (passage_step hW (ExtCol X Pb) (by rw [block_col_true h1 hp hb1, b_extCol]; omega)
        (passage_step hW (ExtCol X Pb) (by rw [block_col_true h2 hp hb2, b_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pb') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h3 hp hb3, b_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftR]
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
    · -- `p = m`: the through-strand (rightward)
      subst hpe
      apply curlT
      apply Subtype.ext
      rw [hb]
      show _ = tvTd3 X.length m (bit Vb X.length m) 0
      rw [hbit]; rfl
    · obtain ⟨h1, hb1⟩ := b_A2 X Y m d hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := b_A6 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨h3, hb3⟩ := b_A10 X Y m d hW h2 (by omega) hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := a'_L2 X Y m d hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pb) hcol0
        (passage_step hW (ExtCol X Pb) (by rw [block_col_true h1 (by omega) hb1, b_extCol]; omega)
        (passage_step hW (ExtCol X Pb) (by rw [block_col_true h2 (by omega) hb2, b_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pb') hcol0' (passage_end hW')
      refine ⟨n, _, hc, by rw [block_col_true h3 (by omega) hb3, b_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftR]
  · -- from the right at `(|X|+3, q)`
    replace hb : b.1 = (X.length + 3, p) := hb
    replace hbit : bit Vb (X.length + 3) p = false := hbit
    have hb'1 : b'.1 = (X.length + 1, p) := by rw [hb'v, hb, shiftR]
    have hbit' : bit Vb' (X.length + 1) p = false := by rw [b_bit_end X Y m d hm hW, hbit]
    have hcol0 : ¬ ExtCol X Pb (colOf b) := by rw [block_col_false hb hp hbit, b_extCol]; omega
    have hcol0' : ¬ ExtCol X Pb' (colOf b') := by rw [block_col_false hb'1 hp hbit', a'_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := b_A19 X Y m d hW hb hp hbit (by omega)
      obtain ⟨h2, hb2⟩ := b_A15 X Y m d hW h1 hp hb1 hpm
      obtain ⟨h3, hb3⟩ := b_A11 X Y m d hW h2 hp hb2 (by omega)
      obtain ⟨h1', hb1'⟩ := a'_L3 X Y m d hW' hb'1 hp hbit' hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pb) hcol0
        (passage_step hW (ExtCol X Pb) (by rw [block_col_false h1 hp hb1, b_extCol]; omega)
        (passage_step hW (ExtCol X Pb) (by rw [block_col_false h2 hp hb2, b_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pb') hcol0' (passage_end hW')
      have hk3 := (cutSlot_facts hW h3 hp).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 hp hb3, b_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftL]
    rcases lt_or_ge p (m + 3) with hpm3 | hpm3
    · have : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
      rcases this with hpe | hpe | hpe
      · -- the cusp arc entered along `(|X|+3, m)`: `d = false`
        apply curlC
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvCd3 X.length m d 0
        rw [hpe, D7] at hbit
        rw [hbit]; rfl
      · -- entered along `(|X|+3, m+1)`: `d = true`
        apply curlC
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvCd3 X.length m d 0
        rw [hpe, D8] at hbit
        have hd : d = true := by simpa using hbit
        rw [hd]; rfl
      · -- the through-strand, leftward
        apply curlT
        apply Subtype.ext
        rw [hb, hpe]
        show _ = tvTd3 X.length m (bit Vb X.length m) 0
        rw [hpe, D9] at hbit
        rw [hbit]; rfl
    · obtain ⟨h1, hb1⟩ := b_A22 X Y m d hW hb hp hbit hpm3
      obtain ⟨h2, hb2⟩ := b_A18 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨h3, hb3⟩ := b_A13 X Y m d hW h2 hp hb2 hpm3
      obtain ⟨h1', hb1'⟩ := a'_L5 X Y m d hW' hb'1 hp hbit' (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pb) hcol0
        (passage_step hW (ExtCol X Pb) (by rw [block_col_false h1 hp hb1, b_extCol]; omega)
        (passage_step hW (ExtCol X Pb) (by rw [block_col_false h2 hp hb2, b_extCol]; omega) (passage_end hW)))
      obtain ⟨n', hc', hmin'⟩ := passage_step hW' (ExtCol X Pb') hcol0' (passage_end hW')
      have hk3 := (cutSlot_facts hW h3 (by omega)).2.2.1
      refine ⟨n, _, hc, by rw [block_col_false h3 (by omega) hb3, b_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h3, shiftL]

end TypeIIbPassage
end

end U6

/-! The leaf `typeII_move` (`Skeleton_W2.lean` L11103-11112; ng:front-II, row 78) is not in this module: its
variants (b) and (d) are being proved in a follow-up unit; it goes into the last delta with `P_typeII`. -/

/-- LEAF (ng:front-I, sm-3:1955-1963 "After rounding its two cusps, the unique crossing bounds an empty
ordinary monogon"): a diagram `D` — `realize W` with the curl's vertices moved so that the strand runs
through the block crossing-free — related to `realize W` by `RI` (the kink) and carrying the named record of
`realize W' = realize (X ++ Y)`. -/
theorem typeI_move {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := U6.typeI_move_proof h

/-- LEAF (ng:deletions, sm-3:2027-2033 "a cusp whose own arms cross once.  Replace it by the uncrossed cusp
with the same two oriented boundary attachments.  After rounding, ordinary Reidemeister I deletes its empty
monogon"): a diagram `D` — `realize W` with the arms' interior vertices exchanged so that they no longer
cross — related to `realize W` by `RI` (a kink of sign −1) and carrying the named record of `realize W'`
(`l_i (!d)`: the bit flip is the arms' exchange of exits). -/
theorem crossedCusp_move {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := U6.crossedCusp_move_proof h

end Leaves

/-! ## Glue: the polynomial consumers (verbatim from `Skeleton_W2.lean` L14619-14624, L14631-14642) -/

/-- ng:front-III: `Δd = 0` (`P_reidemeister_III` on the site). -/
theorem P_typeIII {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨U, hU⟩ := typeIII_site h
  exact P_reidemeister_III ⟨U, Or.inl hU⟩

/-- ng:front-I: `Δd = 0` (`P_reidemeister_I`, then the record). -/
theorem P_typeI {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := typeI_move h
  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)

/-- ng:deletions, crossed cusp: `Δd = 0`. -/
theorem P_crossedCusp {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := crossedCusp_move h
  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)

end FrontRows

open FrontRows

/-! ## Assembly of rows 77, 79 and 80 (verbatim from `Skeleton_W2.lean` L14757-14764, L14774-14804) -/

/-- **ng:front-I** (row 77), assembled: display ng:type-I-counts and `Δd = 0` give `ΔB = 0` (sm-3:1967). -/
theorem ng_front_I : NgFrontIClauses where
  typeI_B := fun _ _ h => by
    obtain ⟨hD, hw⟩ := typeI_counts h
    unfold PLFront.defect
    rw [P_typeI h, hD, hw]
    push_cast; ring

/-- **ng:front-III** (row 79), assembled. -/
theorem ng_front_III : NgFrontIIIClauses where
  typeIII_D := fun _ _ h => (typeIII_counts h).1
  typeIII_w := fun _ _ h => (typeIII_counts h).2
  typeIII_d := fun _ _ h => by rw [P_typeIII h]
  typeIII_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(typeIII_counts h).1, (typeIII_counts h).2, P_typeIII h]

/-- **ng:deletions** (row 80), assembled: the `s` clauses from the accepted syntactic counts through
`realize_sCount` (both words nonempty), the `B` clauses from the count displays and the polynomial leaves. -/
theorem ng_deletions : NgDeletionsClauses where
  zigzag_s := fun W W' h => by
    rw [realize_sCount W h.source_ne_nil, realize_sCount W' (IsZigzagDeletion.ne_nil h W.closed)]
    exact h.sCount
  zigzag_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := zigzag_counts h
    unfold PLFront.defect
    rw [P_zigzag h, hw]
    rcases hD with hD | hD
    · rw [hD]
    · rw [hD]; push_cast; omega
  crossedCusp_s := fun W W' h => by
    rw [realize_sCount W h.ne_nil.1, realize_sCount W' h.ne_nil.2]
    exact h.sCount
  crossedCusp_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := crossedCusp_counts h
    unfold PLFront.defect
    rw [P_crossedCusp h, hw]
    rcases hD with hD | hD <;> omega

end SM
