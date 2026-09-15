import SM.RotationTheorem
import SM.Crossings
import SM.Generic
import SM.TurnLift

/-! # Row 104 cb:embedded-rotation — self-contained skeleton (polygonal secant / Hopf route)

Written 2026-09-14 by the pldiscs probe; plan: work/drafts/pldiscs/ER_PLAN.md; feasibility:
PLDISCS_FEASIBILITY.md §1. Source: reference/SM/sm-3-statesum.tex:4760-4764 (proof 4765-4800).

Layout. §1 statement part, byte-identical to EmbeddedRotation_Statement.lean lines 22-50 (the three
definitions) and 52-54 (the row theorem header; its body is the assembly of §6). §2 route
definitions. §3-§5 the leaves of units U-A, U-B, U-C, all `sorry`. §6 the assembly: every theorem
there is proved from the leaves; `#print axioms SM.cb_embedded_rotation` shows `sorryAx` only
through the leaves. Check: `cd work/lean && lake env lean ../drafts/pldiscs/EmbeddedRotation_Skeleton.lean`. -/

namespace SM

open Set

variable {n : ℕ}

/-! ## §1 Statement part (verbatim from EmbeddedRotation_Statement.lean:22-50) -/

/-- **Embedded polygon** (sm-3:4762 "embedded"): the closed polygonal curve is simple. Rendered on
def:polygon's own vocabulary: every edge is nonzero, remote edge segments are disjoint, and two
consecutive edge segments meet exactly in their common vertex. Flat vertices (zero principal
turn, sm-3:4791 "including zero at a straight subdivision") are allowed. -/
structure Embedded (P : LabelledTuple n) : Prop where
  edge_ne_zero : ∀ i, edge P i ≠ 0
  remote_disjoint : ∀ i j, remote i j → Disjoint (edgeSegment P i) (edgeSegment P j)
  consecutive : ∀ i, edgeSegment P i ∩ edgeSegment P (i + 1) = {P (i + 1)}

/-- Vertex `i` is a supporting (convex-hull) vertex of `P` in direction `N`: the whole polygon
lies in the closed half-plane `{x | ⟪N, x − P i⟫ ≥ 0}`. At such a vertex the bounded complementary
region lies on the side of the polygon, so "traversal orientation around the bounded region" is
read there: left turn = bounded region on the left. -/
def IsSupportingVertex (P : LabelledTuple n) (N : Plane) (i : ZMod n) : Prop :=
  N ≠ 0 ∧ ∀ j, 0 ≤ planeDot N (P j - P i)

/-- Row 104, one field per printed clause (sm-3:4762-4764). -/
structure EmbeddedRotationData [NeZero n] (P : LabelledTuple n) : Prop where
  /-- "has rotation +1 or −1" -/
  pm_one : rotationNumber P = 1 ∨ rotationNumber P = -1
  /-- "according to its traversal orientation around the bounded complementary region":
  at every supporting vertex a left turn (bounded region on the left) forces `+1`, a right
  turn forces `−1`. -/
  orientation : ∀ (N : Plane) (i : ZMod n), IsSupportingVertex P N i →
    (0 < principalTurn P i → rotationNumber P = 1) ∧
    (principalTurn P i < 0 → rotationNumber P = -1)
  /-- non-vacuity of the orientation clause: an embedded polygon has a supporting vertex with a
  nonzero turn (the lowest-leftmost vertex), so the sign is determined. -/
  exists_supporting : ∃ (N : Plane) (i : ZMod n), IsSupportingVertex P N i ∧ principalTurn P i ≠ 0

/-! ## §2 Route definitions

`γ = traversal P` is the piecewise-affine traversal, `γ (k + t) = P k + t • edge P k`, period `n`.
The secant direction `secantDir P (s, t) = normalize (γ t − γ s)` is defined and continuous on the
convex `secantRegion n = {½ ≤ t − s ≤ n − ½, 0 ≤ s, t ≤ n}`; the clamp retraction `secantRetract n`
maps `ℝ²` onto it and is the identity there, so `secantDir P ∘ secantRetract n` is a continuous unit
map on `ℝ²` and `exists_lift_of_unit` (TurnLift.lean:83) gives a global angle `Θ`, an `IsSecantLift`.
The boundary of the region is the diagonal `t = s + ½`, the top `t = n`, the cut `t = s + n − ½`
and the left side `s = 0`; `boundary_telescoping` is the (trivial) closed-loop identity. -/

/-- The traversal `γ_P : ℝ → Plane`: on `[k, k+1]`, `γ (k + t) = P k + t • edge P k`. -/
noncomputable def traversal (P : LabelledTuple n) (x : ℝ) : Plane :=
  edgePoint P ((⌊x⌋ : ℤ) : ZMod n) (Int.fract x)

/-- The secant region `R = {(s,t) : 0 ≤ s, t ≤ n, ½ ≤ t − s ≤ n − ½}` (convex). -/
def secantRegion (n : ℕ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.2 ≤ n ∧ 1 / 2 ≤ p.2 - p.1 ∧ p.2 - p.1 ≤ n - 1 / 2}

/-- Clamp retraction of `ℝ²` onto the secant region: clamp `d = t − s` to `[½, n − ½]`, then
`s` to `[0, n − d]`, and return `(s, s + d)`. -/
noncomputable def secantRetract (n : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  let d := max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))
  let s := max 0 (min ((n : ℝ) - d) p.1)
  (s, s + d)

/-- The secant direction `normalize (γ t − γ s)`. -/
noncomputable def secantDir (P : LabelledTuple n) (p : ℝ × ℝ) : Plane :=
  normalize (traversal P p.2 - traversal P p.1)

/-- A secant lift: a continuous angle `Θ : ℝ² → ℝ` with `secantDir P = (cos Θ, sin Θ)` on the region. -/
def IsSecantLift (P : LabelledTuple n) (Θ : ℝ × ℝ → ℝ) : Prop :=
  Continuous Θ ∧ ∀ p ∈ secantRegion n, secantDir P p = (Real.cos (Θ p), Real.sin (Θ p))

/-- Boundary pieces of the secant region, as paths in `ℝ²`. -/
noncomputable def diagPath (s : ℝ) : ℝ × ℝ := (s, s + 1 / 2)
def topPath (n : ℕ) (s : ℝ) : ℝ × ℝ := (s, (n : ℝ))
noncomputable def cutPath (n : ℕ) (s : ℝ) : ℝ × ℝ := (s, s + ((n : ℝ) - 1 / 2))
def leftPath (t : ℝ) : ℝ × ℝ := (0, t)

/-- The closed-loop identity around the boundary of the secant region (pure telescoping of a global
function; no homotopy is needed). -/
theorem boundary_telescoping (n : ℕ) (Θ : ℝ × ℝ → ℝ) :
    Θ (diagPath ((n : ℝ) - 1 / 2)) - Θ (diagPath 0) =
      (Θ (topPath n ((n : ℝ) - 1 / 2)) - Θ (topPath n (1 / 2))) +
        (Θ (cutPath n (1 / 2)) - Θ (cutPath n 0)) +
        (Θ (leftPath ((n : ℝ) - 1 / 2)) - Θ (leftPath (1 / 2))) := by
  simp only [diagPath, topPath, cutPath, leftPath, sub_add_cancel, add_sub_cancel, zero_add]
  ring

/-- Restricting a secant lift along a path inside the region gives an `IsLiftOn`. -/
theorem IsSecantLift.isLiftOn_comp {P : LabelledTuple n} {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ)
    {φ : ℝ → ℝ × ℝ} {a b : ℝ} (hφ : ContinuousOn φ (Icc a b))
    (hmem : ∀ s ∈ Icc a b, φ s ∈ secantRegion n) :
    IsLiftOn (fun s => secantDir P (φ s)) (fun s => Θ (φ s)) a b :=
  ⟨hΘ.1.comp_continuousOn hφ, fun s hs => hΘ.2 (φ s) (hmem s hs)⟩

/-! ## §3 Unit U-A — traversal calculus, embeddedness, shifts, bridges (all `sorry`) -/

/-- A1. Period `n`. -/
theorem traversal_add_nat (P : LabelledTuple n) (x : ℝ) :
    traversal P (x + n) = traversal P x := by
  have hfl : ⌊x + (n : ℝ)⌋ = ⌊x⌋ + (n : ℤ) := Int.floor_add_natCast x n
  have hfr : Int.fract (x + (n : ℝ)) = Int.fract x := Int.fract_add_natCast x n
  simp only [traversal, hfl, hfr, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]

/-- Helper for A2/A3: the affine formula on the closed piece `[k, k+1]`, in the form
`γ y = P k + (y − k) • e_k`. At `y = k + 1` the two candidate formulas agree since
`edgePoint P (k+1) 0 = P (k+1) = P k + e_k`. -/
theorem ea_traversal_eq_on_Icc (P : LabelledTuple n) (k : ℤ) {y : ℝ} (hy0 : (k : ℝ) ≤ y)
    (hy1 : y ≤ k + 1) :
    traversal P y = P (k : ZMod n) + (y - k) • edge P (k : ZMod n) := by
  rcases hy1.lt_or_eq with hlt | heq
  · have hfl : ⌊y⌋ = k := Int.floor_eq_iff.mpr ⟨hy0, hlt⟩
    have hfr : Int.fract y = y - k := by rw [← Int.self_sub_floor, hfl]
    simp only [traversal, edgePoint, hfl, hfr]
  · have hfl : ⌊y⌋ = k + 1 := by rw [heq, Int.floor_add_one, Int.floor_intCast]
    have hfr : Int.fract y = 0 := by rw [heq, Int.fract_add_one, Int.fract_intCast]
    rw [traversal, hfl, hfr, edgePoint, zero_smul, add_zero, heq, Int.cast_add, Int.cast_one]
    simp [edge]

/-- Helper for A2: a function that is continuous on every closed unit piece `[k, k+1]` is
continuous (at an integer, glue the two adjacent pieces with `ContinuousOn.union_of_isClosed`). -/
theorem ea_continuous_of_continuousOn_Icc {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : ∀ k : ℤ, ContinuousOn f (Icc (k : ℝ) (k + 1))) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  have hxk : x = ⌊x⌋ + Int.fract x := (Int.floor_add_fract x).symm
  rcases (Int.fract_nonneg x).lt_or_eq with hpos | hzero
  · have hmem : Icc ((⌊x⌋ : ℤ) : ℝ) ((⌊x⌋ : ℤ) + 1) ∈ nhds x :=
      Icc_mem_nhds (by linarith) (Int.lt_floor_add_one x)
    exact (hf ⌊x⌋).continuousAt hmem
  · have hx : x = (⌊x⌋ : ℝ) := by rw [← hzero] at hxk; linarith
    have hunion : ContinuousOn f
        (Icc ((⌊x⌋ - 1 : ℤ) : ℝ) ((⌊x⌋ - 1 : ℤ) + 1) ∪ Icc ((⌊x⌋ : ℤ) : ℝ) ((⌊x⌋ : ℤ) + 1)) :=
      (hf (⌊x⌋ - 1)).union_of_isClosed (hf ⌊x⌋) isClosed_Icc isClosed_Icc
    have hmem : Icc ((⌊x⌋ - 1 : ℤ) : ℝ) ((⌊x⌋ - 1 : ℤ) + 1) ∪ Icc ((⌊x⌋ : ℤ) : ℝ) ((⌊x⌋ : ℤ) + 1)
        ∈ nhds x := by
      apply Filter.mem_of_superset
        (Ioo_mem_nhds (a := (⌊x⌋ : ℝ) - 1) (b := (⌊x⌋ : ℝ) + 1) (by linarith) (by linarith))
      intro y hy
      rcases le_or_gt y (⌊x⌋ : ℝ) with hle | hgt
      · left
        exact ⟨by push_cast; linarith [hy.1], by push_cast; linarith⟩
      · right
        exact ⟨hgt.le, hy.2.le⟩
    exact hunion.continuousAt hmem

/-- A2. Continuity (the pieces agree at the integers since `edgePoint P k 1 = P (k+1)`). -/
theorem continuous_traversal (P : LabelledTuple n) : Continuous (traversal P) := by
  apply ea_continuous_of_continuousOn_Icc
  intro k
  have hc : Continuous (fun y : ℝ => P (k : ZMod n) + (y - k) • edge P (k : ZMod n)) :=
    continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  exact hc.continuousOn.congr (fun y hy => ea_traversal_eq_on_Icc P k hy.1 hy.2)

/-- A3. The affine formula on `[k, k+1]`. -/
theorem traversal_int_add (P : LabelledTuple n) (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    traversal P ((k : ℝ) + t) = P (k : ZMod n) + t • edge P (k : ZMod n) := by
  rw [ea_traversal_eq_on_Icc P k (by linarith) (by linarith), add_sub_cancel_left]

/-- A4. Diagonal, constant piece: for `s ∈ [k, k+½]`, `γ(s+½) − γ(s) = ½ e_k`. -/
theorem traversal_diag_const (P : LabelledTuple n) (k : ℕ) (hk : k < n) {s : ℝ}
    (hs : (k : ℝ) ≤ s) (hs' : s ≤ k + 1 / 2) :
    traversal P (s + 1 / 2) - traversal P s = (1 / 2 : ℝ) • edge P (k : ZMod n) := by
  have h1 := ea_traversal_eq_on_Icc P (k : ℤ) (y := s) (by push_cast; linarith)
    (by push_cast; linarith)
  have h2 := ea_traversal_eq_on_Icc P (k : ℤ) (y := s + 1 / 2) (by push_cast; linarith)
    (by push_cast; linarith)
  rw [h1, h2]
  push_cast
  module

/-- A5. Diagonal, cone piece: for `s ∈ [k+½, k+1]`,
`γ(s+½) − γ(s) = (k+1−s) e_k + (s−k−½) e_{k+1}` (a positive combination). -/
theorem traversal_diag_cone (P : LabelledTuple n) (k : ℕ) (hk : k < n) {s : ℝ}
    (hs : (k : ℝ) + 1 / 2 ≤ s) (hs' : s ≤ k + 1) :
    traversal P (s + 1 / 2) - traversal P s =
      ((k : ℝ) + 1 - s) • edge P (k : ZMod n) + (s - k - 1 / 2) • edge P ((k : ZMod n) + 1) := by
  have h1 := ea_traversal_eq_on_Icc P (k : ℤ) (y := s) (by push_cast; linarith)
    (by push_cast; linarith)
  have h2 := ea_traversal_eq_on_Icc P ((k : ℤ) + 1) (y := s + 1 / 2) (by push_cast; linarith)
    (by push_cast; linarith)
  rw [h1, h2]
  push_cast
  have he : P ((k : ZMod n) + 1) = P (k : ZMod n) + edge P (k : ZMod n) := by simp [edge]
  rw [he]
  module

/-- A6. Cut piece: for `s ∈ [0, ½]`, `γ(s + n − ½) − γ(s) = −((½ − s) e_{−1} + s e_0)`. -/
theorem traversal_cut_cone [NeZero n] (P : LabelledTuple n) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    traversal P (s + ((n : ℝ) - 1 / 2)) - traversal P s =
      -(((1 / 2 : ℝ) - s) • edge P (-1) + s • edge P 0) := by
  have h0 : s + ((n : ℝ) - 1 / 2) = (s - 1 / 2) + n := by ring
  rw [h0, traversal_add_nat]
  have h1 := ea_traversal_eq_on_Icc P (-1 : ℤ) (y := s - 1 / 2) (by push_cast; linarith)
    (by push_cast; linarith)
  have h2 := ea_traversal_eq_on_Icc P (0 : ℤ) (y := s) (by push_cast; linarith)
    (by push_cast; linarith)
  rw [h1, h2]
  push_cast
  have he : P (0 : ZMod n) = P (-1) + edge P (-1) := by simp [edge]
  rw [he]
  module

/-- A7. Embedded polygons are regular (a doubled-back consecutive pair would overlap). -/
theorem Embedded.regular (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P) : Regular P := by
  rw [regular_iff_edges]
  intro i
  refine ⟨h.edge_ne_zero i, ?_⟩
  rintro ⟨r, hr, hri⟩
  have hcons := h.consecutive (i - 1)
  rw [sub_add_cancel] at hcons
  have h1r : 0 < 1 - r := by linarith
  set t : ℝ := 1 / (1 - r) with ht
  have ht0 : 0 < t := one_div_pos.mpr h1r
  have ht1 : t ≤ 1 := by rw [ht, div_le_one h1r]; linarith
  have htr : 1 + t * r = t := by rw [ht]; field_simp; ring
  have hPi : P i = P (i - 1) + edge P (i - 1) := by simp [edge]
  have hx : edgePoint P i t ∈ edgeSegment P (i - 1) ∩ edgeSegment P i := by
    refine ⟨⟨1 + t * r, by rw [htr]; exact ht0.le, by rw [htr]; exact ht1, ?_⟩,
      ⟨t, ht0.le, ht1, rfl⟩⟩
    simp only [edgePoint, hri, hPi]
    module
  rw [hcons] at hx
  have hx' : edgePoint P i t = P i := hx
  have hz : t • edge P i = 0 := by
    have := hx'
    simp only [edgePoint] at this
    exact add_eq_left.mp this
  rcases smul_eq_zero.mp hz with h0 | h0
  · exact ht0.ne' h0
  · exact h.edge_ne_zero i h0

/-- Helper for A8: if the point of edge `i` at parameter `t` is the far endpoint `P (i+1)` and the
edge is nonzero, then `t = 1`. -/
theorem ea_param_eq_one_of_edgePoint_eq_next {P : LabelledTuple n} {i : ZMod n}
    (he : edge P i ≠ 0) {t : ℝ} (ht : edgePoint P i t = P (i + 1)) : t = 1 := by
  have h1 : t • edge P i = edge P i := by
    have h2 : P (i + 1) = P i + edge P i := by simp [edge]
    rw [h2] at ht
    exact add_left_cancel ht
  have hz : (t - 1) • edge P i = 0 := by rw [sub_smul, one_smul, h1, sub_self]
  rcases smul_eq_zero.mp hz with h0 | h0
  · linarith
  · exact (he h0).elim

/-- A8. Embedded ⇒ the traversal is injective modulo the period. -/
theorem Embedded.traversal_injective (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P)
    {x y : ℝ} (hxy : traversal P x = traversal P y) : ∃ m : ℤ, y = x + m * n := by
  have hxk : x = ⌊x⌋ + Int.fract x := (Int.floor_add_fract x).symm
  have hyl : y = ⌊y⌋ + Int.fract y := (Int.floor_add_fract y).symm
  have ha0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have ha1 : Int.fract x < 1 := Int.fract_lt_one x
  have hb0 : 0 ≤ Int.fract y := Int.fract_nonneg y
  have hb1 : Int.fract y < 1 := Int.fract_lt_one y
  set k : ℤ := ⌊x⌋ with hk
  set l : ℤ := ⌊y⌋ with hl
  set a : ℝ := Int.fract x with ha
  set b : ℝ := Int.fract y with hb
  set i : ZMod n := (k : ZMod n) with hi
  set j : ZMod n := (l : ZMod n) with hj
  have heq : edgePoint P i a = edgePoint P j b := hxy
  have hxi : edgePoint P i a ∈ edgeSegment P i := ⟨a, ha0, ha1.le, rfl⟩
  have hyj : edgePoint P j b ∈ edgeSegment P j := ⟨b, hb0, hb1.le, rfl⟩
  have hyi : edgePoint P i a ∈ edgeSegment P j := by rw [heq]; exact hyj
  by_cases hadj : adjacent i j
  · rcases hadj with hm1 | h0 | hp1
    · -- `i = j + 1`: the common point of segments `j`, `j+1` is `P (j+1)`, forcing `b = 1`.
      exfalso
      have hij : i = j + 1 := by linear_combination -hm1
      have hcons := h.consecutive j
      rw [← hij] at hcons
      have hmem : edgePoint P j b ∈ edgeSegment P j ∩ edgeSegment P i := ⟨hyj, heq ▸ hxi⟩
      rw [hcons] at hmem
      have hmem' : edgePoint P j b = P (j + 1) := by rw [← hij]; exact hmem
      exact hb1.ne (ea_param_eq_one_of_edgePoint_eq_next (h.edge_ne_zero j) hmem')
    · -- `i = j`: same edge, `edgePoint` is injective, so `a = b` and `l − k ∈ nℤ`.
      have hji : j = i := sub_eq_zero.mp h0
      rw [hji] at heq
      have hab : a = b := edgePoint_injective (h.edge_ne_zero i) heq
      have hkl : (k : ZMod n) = (l : ZMod n) := hji.symm
      obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub k l n).mp hkl
      refine ⟨m, ?_⟩
      have hm' : (l : ℝ) - k = n * m := by exact_mod_cast hm
      rw [hyl, hxk, ← hab]
      linarith
    · -- `j = i + 1`: the common point of segments `i`, `i+1` is `P (i+1)`, forcing `a = 1`.
      exfalso
      have hji : j = i + 1 := by linear_combination hp1
      have hcons := h.consecutive i
      rw [← hji] at hcons
      have hmem : edgePoint P i a ∈ edgeSegment P i ∩ edgeSegment P j := ⟨hxi, hyi⟩
      rw [hcons] at hmem
      have hmem' : edgePoint P i a = P (i + 1) := by rw [← hji]; exact hmem
      exact ha1.ne (ea_param_eq_one_of_edgePoint_eq_next (h.edge_ne_zero i) hmem')
  · -- remote: the segments are disjoint, but share the point.
    exfalso
    exact Set.disjoint_left.mp (h.remote_disjoint i j hadj) hxi hyi

/-- A9. On the secant region (`0 < t − s < n`) the secant vector is nonzero. -/
theorem Embedded.traversal_sub_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P)
    {p : ℝ × ℝ} (hp : p ∈ secantRegion n) : traversal P p.2 - traversal P p.1 ≠ 0 := by
  intro h0
  have heq : traversal P p.1 = traversal P p.2 := (sub_eq_zero.mp h0).symm
  obtain ⟨m, hm⟩ := h.traversal_injective hn heq
  obtain ⟨_, _, h1, h2⟩ := hp
  rw [hm, add_sub_cancel_left] at h1 h2
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by
    by_contra hc
    have hc' : (m : ℝ) ≤ 0 := not_lt.mp hc
    nlinarith
  have hm1 : (1 : ℤ) ≤ m := by
    have : (0 : ℤ) < m := by exact_mod_cast hmpos
    omega
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  nlinarith

/-- A10. `Embedded` is shift-invariant (`edgeSegment_shift`, `edge_shift`; `remote` is on indices). -/
theorem Embedded.shift {P : LabelledTuple n} (h : Embedded P) (a : ZMod n) :
    Embedded (shift a P) := by
  refine ⟨fun i => ?_, fun i j hr => ?_, fun i => ?_⟩
  · rw [edge_shift]
    exact h.edge_ne_zero _
  · rw [edgeSegment_shift, edgeSegment_shift]
    apply h.remote_disjoint
    simpa only [remote, adjacent, add_sub_add_right_eq_sub] using hr
  · have hc := h.consecutive (i + a)
    rw [add_right_comm] at hc
    rw [edgeSegment_shift, edgeSegment_shift]
    exact hc

/-- A11 (bridge for lem:corner-values (i), sm-3:4803 `m_Q = 0`): a generic polygon without crossings
is embedded (`g1_successive_intersection` for the consecutive clause; `IsEmpty (Crossing P)` for the
remote clause). -/
theorem embedded_of_generic_of_isEmpty_crossing [NeZero n] [Nontrivial (ZMod n)] (hn : 3 ≤ n)
    {P : LabelledTuple n} (hg : Generic P) (hc : IsEmpty (Crossing P)) : Embedded P := by
  refine ⟨fun i => g1_edge_ne_zero hn hg.1 i, fun i j hr => ?_,
    fun i => g1_successive_intersection hn hg.1 i⟩
  by_contra hnd
  rw [Set.not_disjoint_iff_nonempty_inter] at hnd
  exact hc.false ⟨{i, j}, i, j, rfl, hr, hnd⟩

/-! ## §4 Unit U-B — retraction, lift, increment lemmas (all `sorry` except the two one-liners) -/

/-- B1. The retraction lands in the region (`n ≥ 1`). -/
theorem secantRetract_mem (hn : 1 ≤ n) (p : ℝ × ℝ) : secantRetract n p ∈ secantRegion n := by
  sorry

/-- B2. The retraction is the identity on the region. -/
theorem secantRetract_eq_self {p : ℝ × ℝ} (hp : p ∈ secantRegion n) : secantRetract n p = p := by
  sorry

/-- B3. The retraction is continuous (max/min of continuous functions). -/
theorem continuous_secantRetract (n : ℕ) : Continuous (secantRetract n) := by
  sorry

/-- B4 (sector lemma). A direction path staying in the closed positive cone of a regular pair
`(u, v)`, from the ray of `u` to the ray of `v`, has lift increment exactly `principalAngle u v`
(zero for a positively collinear pair). Proof: `θ s − θ a − principalAngle u (c s)` is continuous
(`Complex.continuousAt_arg` on `slitPlane`, `regularPair_slitPlane` pattern), takes values in `2πℤ`,
vanishes at `a` (`const_of_circleExp_eq_one`). -/
theorem increment_eq_principalAngle_of_cone {u v : Plane} (huv : RegularPair u v)
    {c : ℝ → Plane} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn c (Icc a b))
    (hcone : ∀ s ∈ Icc a b, ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (α ≠ 0 ∨ β ≠ 0) ∧ c s = α • u + β • v)
    (ha : ∃ r : ℝ, 0 < r ∧ c a = r • u) (hb : ∃ r : ℝ, 0 < r ∧ c b = r • v)
    {θ : ℝ → ℝ} (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) :
    θ b - θ a = principalAngle u v := by
  sorry

/-- B5 (half-plane bound). A nonvanishing path in a closed half-plane has `|lift increment| ≤ π`:
`cos (θ s − θ_N) ≥ 0`, so `θ − θ_N` maps the connected `[a,b]` into `⋃_m [2πm − π/2, 2πm + π/2]`
and stays in one component (`IsPreconnected.image`). -/
theorem abs_increment_le_pi_of_halfplane {N : Plane} (hN : N ≠ 0) {c : ℝ → Plane} {a b : ℝ}
    (hab : a ≤ b) (hc0 : ∀ s ∈ Icc a b, c s ≠ 0) (hhalf : ∀ s ∈ Icc a b, 0 ≤ planeDot N (c s))
    {θ : ℝ → ℝ} (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) :
    |θ b - θ a| ≤ Real.pi := by
  sorry

/-- B6. Negating a direction path shifts its lift by `π` (`cos (x+π) = −cos x`, `sin (x+π) = −sin x`). -/
theorem IsLiftOn.neg {u : ℝ → Plane} {θ : ℝ → ℝ} {a b : ℝ} (h : IsLiftOn u θ a b) :
    IsLiftOn (fun s => -u s) (fun s => θ s + Real.pi) a b := by
  sorry

/-- B7. The increment of a lift of `normalize ∘ c` is `≡ arg (c b) − arg (c a)` modulo `2π`
(`IsLiftOn.circleExp_coe`, `Complex.arg` of a positive multiple). -/
theorem increment_coe_angle {c : ℝ → Plane} {a b : ℝ} (hab : a ≤ b)
    (hca : c a ≠ 0) (hcb : c b ≠ 0)
    {θ : ℝ → ℝ} (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) :
    ((θ b - θ a : ℝ) : Real.Angle) =
      ((planeComplex (c b)).arg : Real.Angle) - ((planeComplex (c a)).arg : Real.Angle) := by
  sorry

/-- B8 (proved). The secant direction is a unit vector on the region. -/
theorem secantDir_unit (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P) {p : ℝ × ℝ}
    (hp : p ∈ secantRegion n) : euclideanLength (secantDir P p) = 1 :=
  euclideanLength_normalize (h.traversal_sub_ne_zero hn hp)

/-- B9 (proved). The secant direction is continuous on the region. -/
theorem continuousOn_secantDir (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P) :
    ContinuousOn (secantDir P) (secantRegion n) := by
  have hf : Continuous (fun p : ℝ × ℝ => traversal P p.2 - traversal P p.1) :=
    ((continuous_traversal P).comp continuous_snd).sub ((continuous_traversal P).comp continuous_fst)
  have hne : ∀ p ∈ secantRegion n, traversal P p.2 - traversal P p.1 ≠ 0 :=
    fun p hp => h.traversal_sub_ne_zero hn hp
  have hlen : ContinuousOn (fun p : ℝ × ℝ => euclideanLength (traversal P p.2 - traversal P p.1))
      (secantRegion n) :=
    ((continuous_planeComplex.comp hf).norm).continuousOn
  have hinv : ContinuousOn
      (fun p : ℝ × ℝ => (euclideanLength (traversal P p.2 - traversal P p.1))⁻¹) (secantRegion n) :=
    hlen.inv₀ (fun p hp => (euclideanLength_pos (hne p hp)).ne')
  unfold secantDir normalize
  exact hinv.smul hf.continuousOn

/-! ## §5 Unit U-C — the four boundary increments and the supporting vertex (all `sorry`) -/

/-- C1 (S7). Diagonal `t = s + ½`, `s ∈ [0, n − ½]`: `2n − 1` pieces, constant on `[k, k+½]`
(`IsLiftOn.increment_eq_zero_of_const` with A4) and a cone sweep on `[k+½, k+1]` giving `ϑ_{k+1}`
(B4 with A5); telescoping over the pieces (`sum_range_natCast_eq_sum_zmod`, TurnLift.lean:291)
gives every turn except `ϑ_0`. -/
theorem diag_increment [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hreg : Regular P)
    (h : Embedded P) {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) :
    Θ ((n : ℝ) - 1 / 2, (n : ℝ)) - Θ (0, 1 / 2) =
      (∑ i : ZMod n, principalTurn P i) - principalTurn P 0 := by
  sorry

/-- C2 (S8). Cut `t = s + n − ½`, `s ∈ [0, ½]`: the negated cone sweep at vertex `0` (A6, B6, B4)
gives `ϑ_0`. -/
theorem cut_increment [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hreg : Regular P)
    (h : Embedded P) {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) :
    Θ (1 / 2, (n : ℝ)) - Θ (0, (n : ℝ) - 1 / 2) = principalTurn P 0 := by
  sorry

/-- C3 (S8). Top leg `t = n`: `secantDir P (s, n) = −secantDir P (0, s)` (A1), so its increment
equals the left leg's (B6, `IsLiftOn.increment_eq`). -/
theorem top_increment_eq_left [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P)
    {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) :
    Θ ((n : ℝ) - 1 / 2, (n : ℝ)) - Θ (1 / 2, (n : ℝ)) =
      Θ (0, (n : ℝ) - 1 / 2) - Θ (0, 1 / 2) := by
  sorry

/-- C4 (S9). Left leg `s = 0`, `t ∈ [½, n − ½]`, at a supporting base vertex: the secant vectors
`γ t − P 0` lie in the closed half-plane of `N` (convex combinations), so `|I| ≤ π` (B5); the leg
runs from `½ e_0` to `−½ e_{−1}` (A3, A1), so `I ≡ π − ϑ_0` (B7, `principalTurn_coe_angle`,
`Complex.arg_neg_coe_angle`). -/
theorem left_increment [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hreg : Regular P)
    (h : Embedded P) {N : Plane} (hsupp : IsSupportingVertex P N 0)
    {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) :
    |Θ (0, (n : ℝ) - 1 / 2) - Θ (0, 1 / 2)| ≤ Real.pi ∧
    ((Θ (0, (n : ℝ) - 1 / 2) - Θ (0, 1 / 2) : ℝ) : Real.Angle) =
      (Real.pi : Real.Angle) - (principalTurn P 0 : Real.Angle) := by
  sorry

/-- C5 (S10). The lowest-leftmost vertex is supporting for `N = (1, 0)` and has a nonzero turn
(a flat turn there would make both incident edges vertical and antiparallel, contradicting
`consecutive`). -/
theorem exists_supporting_vertex_turn_ne_zero [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (h : Embedded P) :
    ∃ (N : Plane) (i : ZMod n), IsSupportingVertex P N i ∧ principalTurn P i ≠ 0 := by
  sorry

/-! ## §6 Assembly — proved from the leaves -/

/-- Supporting vertices transport along cyclic shifts. -/
theorem isSupportingVertex_shift (P : LabelledTuple n) (N : Plane) (i a : ZMod n) :
    IsSupportingVertex (shift a P) N i ↔ IsSupportingVertex P N (i + a) := by
  unfold IsSupportingVertex
  constructor
  · rintro ⟨hN, h⟩
    refine ⟨hN, fun j => ?_⟩
    simpa [shift, sub_add_cancel] using h (j - a)
  · rintro ⟨hN, h⟩
    exact ⟨hN, fun j => h (j + a)⟩

/-- The global secant lift exists: retract, lift on `ℝ × ℝ`, restrict. -/
theorem exists_secant_lift (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P) :
    ∃ Θ : ℝ × ℝ → ℝ, IsSecantLift P Θ := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hmem : ∀ p, secantRetract n p ∈ secantRegion n := secantRetract_mem hn1
  have hu : Continuous (fun p => secantDir P (secantRetract n p)) :=
    (continuousOn_secantDir hn h).comp_continuous (continuous_secantRetract n) hmem
  have h1 : ∀ p, euclideanLength (secantDir P (secantRetract n p)) = 1 :=
    fun p => secantDir_unit hn h (hmem p)
  obtain ⟨Θ, hΘc, hΘ⟩ := exists_lift_of_unit hu h1
  refine ⟨Θ, hΘc, fun p hp => ?_⟩
  have := hΘ p
  rwa [secantRetract_eq_self hp] at this

/-- The key identity `Σ ϑ_i = 2 I + 2 ϑ_0` (boundary telescoping + C1-C3). -/
theorem sum_principalTurn_eq_two_mul [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (hreg : Regular P) (h : Embedded P) {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) :
    ∑ i : ZMod n, principalTurn P i =
      2 * (Θ (0, (n : ℝ) - 1 / 2) - Θ (0, 1 / 2)) + 2 * principalTurn P 0 := by
  have h1 := diag_increment hn hreg h hΘ
  have h2 := cut_increment hn hreg h hΘ
  have h3 := top_increment_eq_left hn h hΘ
  linarith

/-- Arithmetic: from `S = 2I + 2t`, `|I| ≤ π`, `I ≡ π − t (mod 2π)`, `|t| < π`:
`S = ±2π`, with the sign of `t` when `t ≠ 0`. -/
theorem assembly {S I t : ℝ} (hS : S = 2 * I + 2 * t) (hI : |I| ≤ Real.pi)
    (hcong : ((I : ℝ) : Real.Angle) = (Real.pi : Real.Angle) - (t : Real.Angle))
    (ht : -Real.pi < t ∧ t < Real.pi) :
    (S = 2 * Real.pi ∨ S = -(2 * Real.pi)) ∧ (0 < t → S = 2 * Real.pi) ∧
      (t < 0 → S = -(2 * Real.pi)) := by
  have hpi := Real.pi_pos
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hcong
  obtain ⟨k, hk⟩ := hcong
  obtain ⟨hI1, hI2⟩ := abs_le.mp hI
  have hk1 : (k : ℝ) < 1 := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hk2 : (-2 : ℝ) < k := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hk1' : k < 1 := by exact_mod_cast hk1
  have hk2' : -2 < k := by exact_mod_cast hk2
  have hcase : k = 0 ∨ k = -1 := by omega
  rcases hcase with rfl | rfl
  · simp only [Int.cast_zero, mul_zero] at hk
    refine ⟨Or.inl (by linarith), fun _ => by linarith, fun hneg => ?_⟩
    exfalso
    linarith
  · simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one] at hk
    refine ⟨Or.inr (by linarith), fun hpos => ?_, fun _ => by linarith⟩
    exfalso
    linarith

theorem rotationNumber_eq_one_of_sum [NeZero n] {P : LabelledTuple n}
    (h : ∑ i : ZMod n, principalTurn P i = 2 * Real.pi) : rotationNumber P = 1 := by
  unfold rotationNumber
  rw [h]
  exact div_self (by positivity)

theorem rotationNumber_eq_neg_one_of_sum [NeZero n] {P : LabelledTuple n}
    (h : ∑ i : ZMod n, principalTurn P i = -(2 * Real.pi)) : rotationNumber P = -1 := by
  unfold rotationNumber
  rw [h, neg_div, div_self (by positivity)]

/-- The row at a supporting base vertex `0`. -/
theorem based_rotation [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hreg : Regular P)
    (hemb : Embedded P) {N : Plane} (hsupp : IsSupportingVertex P N 0) :
    (rotationNumber P = 1 ∨ rotationNumber P = -1) ∧
      (0 < principalTurn P 0 → rotationNumber P = 1) ∧
      (principalTurn P 0 < 0 → rotationNumber P = -1) := by
  obtain ⟨Θ, hΘ⟩ := exists_secant_lift hn hemb
  have hsum := sum_principalTurn_eq_two_mul hn hreg hemb hΘ
  obtain ⟨hI, hcong⟩ := left_increment hn hreg hemb hsupp hΘ
  have ht : -Real.pi < principalTurn P 0 ∧ principalTurn P 0 < Real.pi :=
    principalAngle_bounds (hreg 0)
  obtain ⟨h1, h2, h3⟩ := assembly hsum hI hcong ht
  refine ⟨?_, fun hpos => rotationNumber_eq_one_of_sum (h2 hpos),
    fun hneg => rotationNumber_eq_neg_one_of_sum (h3 hneg)⟩
  rcases h1 with h1 | h1
  · exact Or.inl (rotationNumber_eq_one_of_sum h1)
  · exact Or.inr (rotationNumber_eq_neg_one_of_sum h1)

/-- **cb:embedded-rotation** (sm-3:4760-4764). -/
theorem cb_embedded_rotation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hreg : Regular P) (hemb : Embedded P) : EmbeddedRotationData P := by
  have key : ∀ (N : Plane) (i : ZMod n), IsSupportingVertex P N i →
      (rotationNumber P = 1 ∨ rotationNumber P = -1) ∧
        (0 < principalTurn P i → rotationNumber P = 1) ∧
        (principalTurn P i < 0 → rotationNumber P = -1) := by
    intro N i hs
    have hQreg : Regular (shift i P) := (regular_shift i P).mpr hreg
    have hQemb : Embedded (shift i P) := hemb.shift i
    have hQs : IsSupportingVertex (shift i P) N 0 := by
      rw [isSupportingVertex_shift, zero_add]
      exact hs
    have hQt : principalTurn (shift i P) 0 = principalTurn P i := by
      rw [principalTurn_shift, zero_add]
    have hb := based_rotation hn hQreg hQemb hQs
    rw [rotationNumber_shift, hQt] at hb
    exact hb
  obtain ⟨N, i, hs, hne⟩ := exists_supporting_vertex_turn_ne_zero hn hemb
  exact { pm_one := (key N i hs).1
          orientation := fun N i hs => (key N i hs).2
          exists_supporting := ⟨N, i, hs, hne⟩ }

#print axioms cb_embedded_rotation

end SM
