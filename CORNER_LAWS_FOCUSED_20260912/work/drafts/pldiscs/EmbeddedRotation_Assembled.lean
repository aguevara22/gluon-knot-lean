import SM.RotationTheorem
import SM.Crossings
import SM.Generic
import SM.TurnLift

/-! # Row 104 cb:embedded-rotation — self-contained proof (polygonal secant / Hopf route)

Assembled 2026-09-14 by the pldiscs probe from `EmbeddedRotation_Skeleton.lean` and the unit files
`ER_UA.lean`, `ER_UB.lean`, `ER_UC.lean` (assembly report: ER_ASSEMBLY_REPORT.md; plan: ER_PLAN.md;
feasibility: PLDISCS_FEASIBILITY.md §1). Source: reference/SM/sm-3-statesum.tex:4760-4764
(proof 4765-4800).

Layout. §1 statement part, byte-identical to EmbeddedRotation_Statement.lean lines 22-50 (the three
definitions) and 52-54 (the row theorem header; its body is the assembly of §6). §2 route
definitions. §3-§5 the leaves of units U-A, U-B, U-C, every one proved; unit helpers carry the
prefixes `ea_`, `eb_`, `ec_`. §6 the assembly: every theorem there is proved from the leaves. The
axiom set of `SM.cb_embedded_rotation` is exactly `[propext, Classical.choice, Quot.sound]`.
Check: `cd work/lean && lake env lean ../drafts/pldiscs/EmbeddedRotation_Assembled.lean`. -/

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

/-! ## §3 Unit U-A — traversal calculus, embeddedness, shifts, bridges (all proved; helpers `ea_`) -/

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

/-! ## §4 Unit U-B — retraction, lift, increment lemmas (all proved; helpers `eb_`) -/

/-- B1. The retraction lands in the region (`n ≥ 1`). -/
theorem secantRetract_mem (hn : 1 ≤ n) (p : ℝ × ℝ) : secantRetract n p ∈ secantRegion n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : (1 / 2 : ℝ) ≤ max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1)) := le_max_left _ _
  have hd2 : max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1)) ≤ (n : ℝ) - 1 / 2 :=
    max_le (by linarith) (min_le_left _ _)
  have hs1 : (0 : ℝ) ≤ max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1) :=
    le_max_left _ _
  have hs2 : max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1) ≤
      (n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1)) :=
    max_le (by linarith) (min_le_left _ _)
  refine ⟨hs1, ?_, ?_, ?_⟩
  · show max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1) +
      max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1)) ≤ (n : ℝ)
    linarith
  · show (1 / 2 : ℝ) ≤ max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1) +
      max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1)) -
      max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1)
    linarith
  · show max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1) +
      max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1)) -
      max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1) ≤ (n : ℝ) - 1 / 2
    linarith

/-- B2. The retraction is the identity on the region. -/
theorem secantRetract_eq_self {p : ℝ × ℝ} (hp : p ∈ secantRegion n) : secantRetract n p = p := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hd : max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1)) = p.2 - p.1 := by
    rw [min_eq_right h4, max_eq_right h3]
  have hs : max 0 (min ((n : ℝ) - (p.2 - p.1)) p.1) = p.1 := by
    rw [min_eq_right (by linarith), max_eq_right h1]
  show (max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1),
    max 0 (min ((n : ℝ) - max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) p.1) +
      max (1 / 2 : ℝ) (min ((n : ℝ) - 1 / 2) (p.2 - p.1))) = p
  rw [hd, hs]
  ext
  · rfl
  · show p.1 + (p.2 - p.1) = p.2
    ring

/-- B3. The retraction is continuous (max/min of continuous functions). -/
theorem continuous_secantRetract (n : ℕ) : Continuous (secantRetract n) := by
  unfold secantRetract
  fun_prop

/-- Nonnegative combinations of a regular pair, not both coefficients zero, are never nonpositive
multiples of `u`: in particular nonzero, and `(u, α u + β v)` is again a regular pair. -/
theorem eb_regularPair_cone {u v : Plane} (huv : RegularPair u v) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hne : α ≠ 0 ∨ β ≠ 0) : RegularPair u (α • u + β • v) := by
  obtain ⟨hu, hv, hneg⟩ := huv
  have key : ∀ r : ℝ, r ≤ 0 → α • u + β • v ≠ r • u := by
    intro r hr heq
    have hβv : β • v = (r - α) • u := by
      rw [sub_smul, ← heq]
      abel
    rcases eq_or_lt_of_le hβ with hβ0 | hβpos
    · -- β = 0: then α ≠ 0, α > 0, and (r − α) • u = 0 forces r = α > 0
      subst hβ0
      have hα0 : α ≠ 0 := hne.resolve_right (fun h => h rfl)
      rw [zero_smul] at hβv
      rcases smul_eq_zero.mp hβv.symm with h | h
      · have : r = α := by linarith
        exact hα0 (by linarith [lt_of_le_of_ne hα (Ne.symm hα0)])
      · exact hu h
    · -- β > 0: v = ((r − α)/β) • u with (r − α)/β ≤ 0
      have hv' : v = ((r - α) / β) • u := by
        rw [div_eq_inv_mul, mul_smul, ← hβv, smul_smul, inv_mul_cancel₀ hβpos.ne', one_smul]
      rcases eq_or_lt_of_le (show r - α ≤ 0 by linarith) with h0 | hlt
      · -- r = α = 0: v = 0
        rw [h0, zero_div, zero_smul] at hv'
        exact hv hv'
      · exact hneg ⟨(r - α) / β, div_neg_of_neg_of_pos hlt hβpos, hv'⟩
  refine ⟨hu, ?_, ?_⟩
  · intro h
    exact key 0 le_rfl (by rw [h, zero_smul])
  · rintro ⟨r, hr, hrv⟩
    exact key r hr.le hrv

/-- The argument forgets positive scalars: `principalAngle u (r • v) = principalAngle u v`. -/
theorem eb_principalAngle_smul_right {r : ℝ} (hr : 0 < r) (u v : Plane) :
    principalAngle u (r • v) = principalAngle u v := by
  unfold principalAngle cornerRotor
  rw [planeComplex_smul, Complex.real_smul, mul_left_comm, Complex.arg_real_mul _ hr]

/-- `arg` of a normalised vector is `arg` of the vector. -/
theorem eb_arg_planeComplex_normalize {w : Plane} (hw : w ≠ 0) :
    (planeComplex (normalize w)).arg = (planeComplex w).arg := by
  rw [normalize, planeComplex_smul, Complex.real_smul,
    Complex.arg_real_mul _ (inv_pos.mpr (euclideanLength_pos hw))]

/-- A lift of `normalize ∘ c` on `[a, b]` is, modulo `2π`, the argument of `c`. -/
theorem eb_coe_angle_eq_arg {c : ℝ → Plane} {a b : ℝ} {θ : ℝ → ℝ}
    (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) {s : ℝ} (hs : s ∈ Icc a b) (hcs : c s ≠ 0) :
    ((θ s : ℝ) : Real.Angle) = ((planeComplex (c s)).arg : Real.Angle) := by
  have h := hθ.circleExp_coe hs
  have h2 : ((Circle.exp (θ s) : Circle) : ℂ) = planeComplex (normalize (c s)) := h
  rw [← eb_arg_planeComplex_normalize hcs, ← h2, ← Real.Angle.toCircle_coe,
    Real.Angle.arg_toCircle]

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
  have hreg : ∀ s ∈ Icc a b, RegularPair u (c s) := by
    intro s hs
    obtain ⟨α, β, hα, hβ, hne, hcs⟩ := hcone s hs
    rw [hcs]
    exact eb_regularPair_cone huv hα hβ hne
  have hne : ∀ s ∈ Icc a b, c s ≠ 0 := fun s hs => (hreg s hs).2.1
  have hcont : ContinuousOn (fun s => θ s - principalAngle u (c s)) (Icc a b) := by
    refine hθ.1.sub ?_
    intro s hs
    have h1 : ContinuousWithinAt (fun s => cornerRotor u (c s)) (Icc a b) s := by
      unfold cornerRotor
      exact continuousWithinAt_const.mul
        (continuous_planeComplex.continuousAt.comp_continuousWithinAt (hc s hs))
    exact ContinuousAt.comp_continuousWithinAt (g := Complex.arg) (f := fun s => cornerRotor u (c s))
      (Complex.continuousAt_arg (regularPair_slitPlane (hreg s hs))) h1
  have hconst : θ b - principalAngle u (c b) = θ a - principalAngle u (c a) := by
    refine Circle.isCoveringMap_exp.constOn_of_comp isPreconnected_Icc hcont
      (fun s hs s' hs' => ?_) ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
    show Circle.exp (θ s - principalAngle u (c s)) = Circle.exp (θ s' - principalAngle u (c s'))
    rw [← Real.Angle.toCircle_coe, ← Real.Angle.toCircle_coe]
    congr 1
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub, eb_coe_angle_eq_arg hθ hs (hne s hs),
      eb_coe_angle_eq_arg hθ hs' (hne s' hs'), principalAngle_coe_angle huv.1 (hne s hs),
      principalAngle_coe_angle huv.1 (hne s' hs')]
    abel
  obtain ⟨ra, hra, hca⟩ := ha
  obtain ⟨rb, hrb, hcb⟩ := hb
  have h0 : principalAngle u (c a) = 0 :=
    (principalAngle_eq_zero_iff huv.1 (hne a ⟨le_rfl, hab⟩)).mpr ⟨ra, hra, hca⟩
  have h1 : principalAngle u (c b) = principalAngle u v := by
    rw [hcb, eb_principalAngle_smul_right hrb]
  linarith

/-- Between two points with nonnegative cosine more than `π` apart lies a point with negative
cosine (the odd multiple of `π` in between). -/
theorem eb_exists_cos_neg_of_gt_pi {x y : ℝ} (hx : 0 ≤ Real.cos x) (hy : 0 ≤ Real.cos y)
    (hxy : Real.pi < y - x) : ∃ z ∈ Ioo x y, Real.cos z < 0 := by
  have hpi := Real.pi_pos
  have h2pi : 0 < 2 * Real.pi := by positivity
  set t := toIcoMod h2pi (-(Real.pi / 2)) x with ht
  set k := toIcoDiv h2pi (-(Real.pi / 2)) x with hk
  have hmem : t ∈ Ico (-(Real.pi / 2)) (-(Real.pi / 2) + 2 * Real.pi) := toIcoMod_mem_Ico h2pi _ _
  have hxt : x = t + k * (2 * Real.pi) := by
    have := toIcoMod_add_toIcoDiv_zsmul h2pi (-(Real.pi / 2)) x
    rw [zsmul_eq_mul] at this
    exact this.symm
  have hcosx : Real.cos x = Real.cos t := by
    rw [hxt, Real.cos_add_int_mul_two_pi]
  have ht2 : t ≤ Real.pi / 2 := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    have : Real.cos t < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt hcon' (by linarith [hmem.2])
    linarith
  refine ⟨k * (2 * Real.pi) + Real.pi, ⟨by linarith, ?_⟩, ?_⟩
  · by_contra hcon
    have hcon' := not_lt.mp hcon
    have hy' : Real.cos y = Real.cos (y - k * (2 * Real.pi)) := by
      rw [← Real.cos_add_int_mul_two_pi (y - k * (2 * Real.pi)) k]
      ring_nf
    have : Real.cos (y - k * (2 * Real.pi)) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [hmem.1]) (by linarith)
    linarith
  · rw [Real.cos_int_mul_two_pi_add_pi]
    norm_num

/-- A continuous real function on `[a, b]` with nonnegative cosine moves by at most `π`. -/
theorem eb_abs_sub_le_pi_of_cos_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hcos : ∀ s ∈ Icc a b, 0 ≤ Real.cos (f s)) :
    |f b - f a| ≤ Real.pi := by
  rw [abs_le]
  constructor
  · by_contra h
    have h' := not_le.mp h
    obtain ⟨z, hz, hcz⟩ := eb_exists_cos_neg_of_gt_pi (hcos b ⟨hab, le_rfl⟩)
      (hcos a ⟨le_rfl, hab⟩) (by linarith)
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' hab hf (Ioo_subset_Icc_self hz)
    have := hcos s hs
    rw [hfs] at this
    linarith
  · by_contra h
    have h' := not_le.mp h
    obtain ⟨z, hz, hcz⟩ := eb_exists_cos_neg_of_gt_pi (hcos a ⟨le_rfl, hab⟩)
      (hcos b ⟨hab, le_rfl⟩) h'
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab hf (Ioo_subset_Icc_self hz)
    have := hcos s hs
    rw [hfs] at this
    linarith

/-- `⟪N, (cos t, sin t)⟫ = |N| cos (t − arg N)`. -/
theorem eb_planeDot_cos_sin (N : Plane) (t : ℝ) :
    planeDot N (Real.cos t, Real.sin t) =
      euclideanLength N * Real.cos (t - (planeComplex N).arg) := by
  have h1 := Complex.norm_mul_cos_arg (planeComplex N)
  have h2 := Complex.norm_mul_sin_arg (planeComplex N)
  have hre : (planeComplex N).re = N.1 := rfl
  have him : (planeComplex N).im = N.2 := rfl
  rw [hre] at h1
  rw [him] at h2
  unfold planeDot euclideanLength
  rw [Real.cos_sub]
  linear_combination (-Real.cos t) * h1 + (-Real.sin t) * h2

/-- B5 (half-plane bound). A nonvanishing path in a closed half-plane has `|lift increment| ≤ π`:
`cos (θ s − θ_N) ≥ 0`, so `θ − θ_N` maps the connected `[a,b]` into `⋃_m [2πm − π/2, 2πm + π/2]`
and stays in one component (`IsPreconnected.image`). -/
theorem abs_increment_le_pi_of_halfplane {N : Plane} (hN : N ≠ 0) {c : ℝ → Plane} {a b : ℝ}
    (hab : a ≤ b) (hc0 : ∀ s ∈ Icc a b, c s ≠ 0) (hhalf : ∀ s ∈ Icc a b, 0 ≤ planeDot N (c s))
    {θ : ℝ → ℝ} (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) :
    |θ b - θ a| ≤ Real.pi := by
  have hNpos : 0 < euclideanLength N := euclideanLength_pos hN
  have hcos : ∀ s ∈ Icc a b, 0 ≤ Real.cos (θ s - (planeComplex N).arg) := by
    intro s hs
    have hL : 0 < euclideanLength (c s) := euclideanLength_pos (hc0 s hs)
    have hn : normalize (c s) = (Real.cos (θ s), Real.sin (θ s)) := hθ.2 s hs
    have hcs : c s = euclideanLength (c s) • (Real.cos (θ s), Real.sin (θ s)) := by
      rw [← hn, normalize, smul_inv_smul₀ hL.ne']
    have h := hhalf s hs
    rw [hcs, planeDot_smul_right, eb_planeDot_cos_sin] at h
    exact (mul_nonneg_iff_of_pos_left hNpos).mp ((mul_nonneg_iff_of_pos_left hL).mp h)
  have := eb_abs_sub_le_pi_of_cos_nonneg (f := fun s => θ s - (planeComplex N).arg) hab
    (hθ.1.sub continuousOn_const) hcos
  rwa [show θ b - (planeComplex N).arg - (θ a - (planeComplex N).arg) = θ b - θ a by ring] at this

/-- B6. Negating a direction path shifts its lift by `π` (`cos (x+π) = −cos x`, `sin (x+π) = −sin x`). -/
theorem IsLiftOn.neg {u : ℝ → Plane} {θ : ℝ → ℝ} {a b : ℝ} (h : IsLiftOn u θ a b) :
    IsLiftOn (fun s => -u s) (fun s => θ s + Real.pi) a b := by
  refine ⟨h.1.add continuousOn_const, fun s hs => ?_⟩
  show -u s = (Real.cos (θ s + Real.pi), Real.sin (θ s + Real.pi))
  rw [h.2 s hs, Real.cos_add_pi, Real.sin_add_pi]
  rfl

/-- B7. The increment of a lift of `normalize ∘ c` is `≡ arg (c b) − arg (c a)` modulo `2π`
(`IsLiftOn.circleExp_coe`, `Complex.arg` of a positive multiple). -/
theorem increment_coe_angle {c : ℝ → Plane} {a b : ℝ} (hab : a ≤ b)
    (hca : c a ≠ 0) (hcb : c b ≠ 0)
    {θ : ℝ → ℝ} (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) :
    ((θ b - θ a : ℝ) : Real.Angle) =
      ((planeComplex (c b)).arg : Real.Angle) - ((planeComplex (c a)).arg : Real.Angle) := by
  rw [Real.Angle.coe_sub, eb_coe_angle_eq_arg hθ ⟨hab, le_rfl⟩ hcb,
    eb_coe_angle_eq_arg hθ ⟨le_rfl, hab⟩ hca]

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

/-! ## §5 Unit U-C — the four boundary increments and the supporting vertex (all proved; helpers `ec_`) -/

/-- U-C helper: changing the direction path pointwise on `[a, b]` preserves `IsLiftOn`. -/
theorem ec_isLiftOn_congr {u u' : ℝ → Plane} {θ : ℝ → ℝ} {a b : ℝ} (h : IsLiftOn u θ a b)
    (hu : ∀ s ∈ Icc a b, u s = u' s) : IsLiftOn u' θ a b :=
  ⟨h.1, fun s hs => (hu s hs) ▸ h.2 s hs⟩

/-- U-C helper: the diagonal `s ↦ (s, s + ½)` restricted to `[a, b] ⊆ [0, n − ½]` lies in the
region, so `Θ` along it is an `IsLiftOn` of the diagonal secant direction. -/
theorem ec_diag_lift (hn : 3 ≤ n) {P : LabelledTuple n} {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ (n : ℝ) - 1 / 2) :
    IsLiftOn (fun s => secantDir P (s, s + 1 / 2)) (fun s => Θ (s, s + 1 / 2)) a b := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  refine hΘ.isLiftOn_comp (φ := fun s => (s, s + 1 / 2)) (by fun_prop) (fun s hs => ?_)
  obtain ⟨hs0, hs1⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith

/-- U-C helper (C1, constant piece `[k, k+½]`, A4): the diagonal direction is constant, so the
lift has no increment. -/
theorem ec_diag_const_step (hn : 3 ≤ n) {P : LabelledTuple n} {Θ : ℝ × ℝ → ℝ}
    (hΘ : IsSecantLift P Θ) (k : ℕ) (hk : k < n) :
    Θ ((k : ℝ) + 1 / 2, (k : ℝ) + 1 / 2 + 1 / 2) = Θ ((k : ℝ), (k : ℝ) + 1 / 2) := by
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hlift := ec_diag_lift hn hΘ (a := (k : ℝ)) (b := (k : ℝ) + 1 / 2) (by positivity)
    (by linarith)
  refine hlift.increment_eq_zero_of_const (by linarith)
    (v := normalize ((1 / 2 : ℝ) • edge P (k : ZMod n))) (fun s hs => ?_)
  simp only [secantDir]
  rw [traversal_diag_const P k hk hs.1 hs.2]

/-- U-C helper (C1, cone piece `[k+½, k+1]`, A5 + B4): the diagonal direction sweeps the positive
cone from ray `e_k` to ray `e_{k+1}`, so the lift increment is `ϑ_{k+1}`. -/
theorem ec_diag_cone_step (hn : 3 ≤ n) {P : LabelledTuple n} (hreg : Regular P)
    {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) (k : ℕ) (hk : k + 1 < n) :
    Θ ((k : ℝ) + 1, (k : ℝ) + 1 + 1 / 2) - Θ ((k : ℝ) + 1 / 2, (k : ℝ) + 1 / 2 + 1 / 2) =
      principalTurn P ((k : ZMod n) + 1) := by
  have hk' : (k : ℝ) + 1 + 1 ≤ n := by exact_mod_cast hk
  have hkn : k < n := by omega
  have hlift := ec_diag_lift hn hΘ (a := (k : ℝ) + 1 / 2) (b := (k : ℝ) + 1) (by positivity)
    (by linarith)
  have hlift' : IsLiftOn
      (fun s => normalize (((k : ℝ) + 1 - s) • edge P (k : ZMod n) +
        (s - k - 1 / 2) • edge P ((k : ZMod n) + 1)))
      (fun s => Θ (s, s + 1 / 2)) ((k : ℝ) + 1 / 2) ((k : ℝ) + 1) := by
    refine ec_isLiftOn_congr hlift (fun s hs => ?_)
    simp only [secantDir]
    rw [traversal_diag_cone P k hkn hs.1 hs.2]
  have huv : RegularPair (edge P (k : ZMod n)) (edge P ((k : ZMod n) + 1)) := by
    have := hreg ((k : ZMod n) + 1)
    rwa [add_sub_cancel_right] at this
  have key := increment_eq_principalAngle_of_cone huv (by linarith) (by fun_prop) ?_ ?_ ?_ hlift'
  · rw [key]
    unfold principalTurn
    rw [add_sub_cancel_right]
  · intro s hs
    refine ⟨(k : ℝ) + 1 - s, s - k - 1 / 2, by linarith [hs.2], by linarith [hs.1], ?_, rfl⟩
    rcases eq_or_ne ((k : ℝ) + 1 - s) 0 with h0 | h0
    · right
      intro h1
      linarith
    · exact Or.inl h0
  · refine ⟨1 / 2, by norm_num, ?_⟩
    simp only [show (k : ℝ) + 1 - (k + 1 / 2) = 1 / 2 by ring,
      show (k : ℝ) + 1 / 2 - k - 1 / 2 = 0 by ring, zero_smul, add_zero]
  · refine ⟨1 / 2, by norm_num, ?_⟩
    simp only [show (k : ℝ) + 1 - (k + 1) = 0 by ring,
      show (k : ℝ) + 1 - k - 1 / 2 = 1 / 2 by ring, zero_smul, zero_add]

/-- C1 (S7). Diagonal `t = s + ½`, `s ∈ [0, n − ½]`: `2n − 1` pieces, constant on `[k, k+½]`
(`IsLiftOn.increment_eq_zero_of_const` with A4) and a cone sweep on `[k+½, k+1]` giving `ϑ_{k+1}`
(B4 with A5); telescoping over the pieces (`sum_range_natCast_eq_sum_zmod`, TurnLift.lean:291)
gives every turn except `ϑ_0`. -/
theorem diag_increment [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hreg : Regular P)
    (h : Embedded P) {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) :
    Θ ((n : ℝ) - 1 / 2, (n : ℝ)) - Θ (0, 1 / 2) =
      (∑ i : ZMod n, principalTurn P i) - principalTurn P 0 := by
  -- partial sums along the diagonal: `Θ(m, m+½) = Θ(0, ½) + Σ_{k<m} ϑ_{k+1}` for `m < n`
  have hind : ∀ m : ℕ, m < n →
      Θ ((m : ℝ), (m : ℝ) + 1 / 2) =
        Θ (0, 1 / 2) + ∑ k ∈ Finset.range m, principalTurn P ((k : ZMod n) + 1) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp
    | succ m ih =>
      intro hm
      have hm' : m < n := by omega
      have h1 := ih hm'
      have h2 := ec_diag_const_step hn hΘ m hm'
      have h3 := ec_diag_cone_step hn hreg hΘ m hm
      rw [Finset.sum_range_succ]
      push_cast
      linarith
  have hn1 : n - 1 < n := by omega
  have h1 := hind (n - 1) hn1
  have h2 := ec_diag_const_step hn hΘ (n - 1) hn1
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_pred (by omega)
  rw [hc] at h1 h2
  have e1 : ((n : ℝ) - 1 / 2, (n : ℝ)) = ((n : ℝ) - 1 + 1 / 2, (n : ℝ) - 1 + 1 / 2 + 1 / 2) := by
    ext <;> simp <;> ring
  -- reindex `Σ_{k<n-1} ϑ_{k+1} = Σ_{k<n} ϑ_k − ϑ_0 = Σ_{i : ZMod n} ϑ_i − ϑ_0`
  have hsum : ∑ k ∈ Finset.range (n - 1), principalTurn P ((k : ZMod n) + 1) =
      (∑ i : ZMod n, principalTurn P i) - principalTurn P 0 := by
    have := Finset.sum_range_succ' (fun k : ℕ => principalTurn P (k : ZMod n)) (n - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), sum_range_natCast_eq_sum_zmod (principalTurn P)]
      at this
    push_cast at this
    linarith
  rw [e1, h2, h1, hsum]
  ring

/-- C2 (S8). Cut `t = s + n − ½`, `s ∈ [0, ½]`: the negated cone sweep at vertex `0` (A6, B6, B4)
gives `ϑ_0`. -/
theorem cut_increment [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hreg : Regular P)
    (h : Embedded P) {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) :
    Θ (1 / 2, (n : ℝ)) - Θ (0, (n : ℝ) - 1 / 2) = principalTurn P 0 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  -- the cut path `s ↦ (s, s + n − ½)` on `[0, ½]` lies in the region
  have hmem : ∀ s ∈ Icc (0 : ℝ) (1 / 2),
      ((s, s + ((n : ℝ) - 1 / 2)) : ℝ × ℝ) ∈ secantRegion n := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith
  have hlift : IsLiftOn (fun s => secantDir P (s, s + ((n : ℝ) - 1 / 2)))
      (fun s => Θ (s, s + ((n : ℝ) - 1 / 2))) 0 (1 / 2) :=
    hΘ.isLiftOn_comp (φ := fun s => (s, s + ((n : ℝ) - 1 / 2))) (by fun_prop) hmem
  -- A6: the secant vector is the negated cone path from ray `e_{−1}` to ray `e_0`
  have hlift' : IsLiftOn
      (fun s => -(normalize (((1 / 2 : ℝ) - s) • edge P (-1) + s • edge P 0)))
      (fun s => Θ (s, s + ((n : ℝ) - 1 / 2))) 0 (1 / 2) := by
    refine ec_isLiftOn_congr hlift (fun s hs => ?_)
    simp only [secantDir]
    rw [traversal_cut_cone P hs.1 hs.2, normalize_neg]
  -- B6: `Θ + π` lifts the cone path itself
  have hlift'' : IsLiftOn
      (fun s => normalize (((1 / 2 : ℝ) - s) • edge P (-1) + s • edge P 0))
      (fun s => Θ (s, s + ((n : ℝ) - 1 / 2)) + Real.pi) 0 (1 / 2) := by
    have := hlift'.neg
    simpa only [neg_neg] using this
  have huv : RegularPair (edge P (-1)) (edge P 0) := by
    have := hreg 0
    rwa [zero_sub] at this
  -- B4
  have key : Θ (1 / 2, 1 / 2 + ((n : ℝ) - 1 / 2)) + Real.pi -
      (Θ (0, 0 + ((n : ℝ) - 1 / 2)) + Real.pi) = principalAngle (edge P (-1)) (edge P 0) := by
    refine increment_eq_principalAngle_of_cone huv (by norm_num) (by fun_prop) ?_ ?_ ?_ hlift''
    · intro s hs
      refine ⟨(1 / 2 : ℝ) - s, s, by linarith [hs.2], hs.1, ?_, rfl⟩
      rcases eq_or_ne s 0 with h0 | h0
      · left
        rw [h0]
        norm_num
      · exact Or.inr h0
    · exact ⟨1 / 2, by norm_num, by simp⟩
    · exact ⟨1 / 2, by norm_num, by simp⟩
  have e1 : (1 / 2 : ℝ) + ((n : ℝ) - 1 / 2) = n := by ring
  have e2 : (0 : ℝ) + ((n : ℝ) - 1 / 2) = (n : ℝ) - 1 / 2 := by ring
  rw [e1, e2] at key
  unfold principalTurn
  rw [zero_sub]
  linarith

/-- C3 (S8). Top leg `t = n`: `secantDir P (s, n) = −secantDir P (0, s)` (A1), so its increment
equals the left leg's (B6, `IsLiftOn.increment_eq`). -/
theorem top_increment_eq_left [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P)
    {Θ : ℝ × ℝ → ℝ} (hΘ : IsSecantLift P Θ) :
    Θ ((n : ℝ) - 1 / 2, (n : ℝ)) - Θ (1 / 2, (n : ℝ)) =
      Θ (0, (n : ℝ) - 1 / 2) - Θ (0, 1 / 2) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hab : (1 / 2 : ℝ) ≤ (n : ℝ) - 1 / 2 := by linarith
  have hmemT : ∀ s ∈ Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2),
      ((s, (n : ℝ)) : ℝ × ℝ) ∈ secantRegion n := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith
  have hmemL : ∀ s ∈ Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2),
      (((0 : ℝ), s) : ℝ × ℝ) ∈ secantRegion n := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith
  have hT : IsLiftOn (fun s => secantDir P (s, (n : ℝ))) (fun s => Θ (s, (n : ℝ)))
      (1 / 2) ((n : ℝ) - 1 / 2) :=
    hΘ.isLiftOn_comp (φ := fun s => (s, (n : ℝ))) (by fun_prop) hmemT
  have hL : IsLiftOn (fun s => secantDir P (0, s)) (fun s => Θ (0, s))
      (1 / 2) ((n : ℝ) - 1 / 2) :=
    hΘ.isLiftOn_comp (φ := fun s => ((0 : ℝ), s)) (by fun_prop) hmemL
  -- A1: `γ n = γ 0`, so the top direction is the negated left direction
  have h0 : traversal P (n : ℝ) = traversal P 0 := by
    have := traversal_add_nat P 0
    rwa [zero_add] at this
  have hT' : IsLiftOn (fun s => -(secantDir P (0, s))) (fun s => Θ (s, (n : ℝ)))
      (1 / 2) ((n : ℝ) - 1 / 2) := by
    refine ec_isLiftOn_congr hT (fun s hs => ?_)
    simp only [secantDir]
    rw [h0, ← normalize_neg, neg_sub]
  -- B6 + uniqueness of increments
  have hL' := hL.neg
  have := IsLiftOn.increment_eq hab hT' hL'
  linarith

/-- U-C helper: `planeDot` is additive in its second argument. -/
theorem ec_planeDot_add_right (N u v : Plane) :
    planeDot N (u + v) = planeDot N u + planeDot N v := by
  simp only [planeDot, Prod.fst_add, Prod.snd_add]
  ring

/-- U-C helper (C4): at a supporting base vertex `0`, every traversal point lies in the closed
half-plane of `N` (it is a convex combination of two vertices). -/
theorem ec_planeDot_traversal_sub_nonneg {P : LabelledTuple n} {N : Plane}
    (hsupp : IsSupportingVertex P N 0) (t : ℝ) : 0 ≤ planeDot N (traversal P t - P 0) := by
  have hf0 := Int.fract_nonneg t
  have hf1 := (Int.fract_lt_one t).le
  have e : traversal P t - P 0 =
      (1 - Int.fract t) • (P ((⌊t⌋ : ℤ) : ZMod n) - P 0) +
        Int.fract t • (P (((⌊t⌋ : ℤ) : ZMod n) + 1) - P 0) := by
    simp only [traversal, edgePoint, edge]
    module
  rw [e, ec_planeDot_add_right, planeDot_smul_right, planeDot_smul_right]
  exact add_nonneg (mul_nonneg (by linarith) (hsupp.2 _)) (mul_nonneg hf0 (hsupp.2 _))

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
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hab : (1 / 2 : ℝ) ≤ (n : ℝ) - 1 / 2 := by linarith
  have hmemL : ∀ t ∈ Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2),
      (((0 : ℝ), t) : ℝ × ℝ) ∈ secantRegion n := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith
  have h0 : traversal P 0 = P 0 := by
    simp [traversal, edgePoint]
  -- the left leg lifts `normalize (γ t − P 0)`
  have hL : IsLiftOn (fun t => normalize (traversal P t - P 0)) (fun t => Θ (0, t))
      (1 / 2) ((n : ℝ) - 1 / 2) := by
    refine ec_isLiftOn_congr
      (hΘ.isLiftOn_comp (φ := fun t => ((0 : ℝ), t)) (by fun_prop) hmemL) (fun t ht => ?_)
    simp only [secantDir, h0]
  have hc0 : ∀ t ∈ Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2), traversal P t - P 0 ≠ 0 := by
    intro t ht
    have := h.traversal_sub_ne_zero hn (hmemL t ht)
    simpa only [h0] using this
  have hhalf : ∀ t ∈ Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2), 0 ≤ planeDot N (traversal P t - P 0) :=
    fun t _ => ec_planeDot_traversal_sub_nonneg hsupp t
  refine ⟨abs_increment_le_pi_of_halfplane hsupp.1 hab hc0 hhalf hL, ?_⟩
  -- B7 and the endpoint values `½ e_0`, `−½ e_{−1}`
  have hca : traversal P (1 / 2) - P 0 ≠ 0 := hc0 _ ⟨le_rfl, hab⟩
  have hcb : traversal P ((n : ℝ) - 1 / 2) - P 0 ≠ 0 := hc0 _ ⟨hab, le_rfl⟩
  have key := increment_coe_angle hab hca hcb hL
  have e1 : traversal P (1 / 2) - P 0 = (1 / 2 : ℝ) • edge P 0 := by
    have := traversal_int_add P 0 (t := 1 / 2) (by norm_num) (by norm_num)
    rw [Int.cast_zero, zero_add] at this
    rw [this]
    simp
  have e2 : traversal P ((n : ℝ) - 1 / 2) - P 0 = -((1 / 2 : ℝ) • edge P (-1)) := by
    have h1 : traversal P ((n : ℝ) - 1 / 2) = traversal P (-1 / 2) := by
      have := traversal_add_nat P (-1 / 2)
      rw [← this]
      congr 1
      ring
    have h2 := traversal_int_add P (-1) (t := 1 / 2) (by norm_num) (by norm_num)
    push_cast at h2
    have h3 : (-1 : ℝ) + 1 / 2 = -1 / 2 := by norm_num
    rw [h3] at h2
    rw [h1, h2]
    simp only [edge, neg_add_cancel]
    module
  rw [e1, e2] at key
  have hne : planeComplex ((1 / 2 : ℝ) • edge P (-1)) ≠ 0 :=
    planeComplex_ne_zero (smul_ne_zero (by norm_num) (h.edge_ne_zero _))
  rw [key, principalTurn_coe_angle hreg 0, zero_sub, planeComplex_neg,
    Complex.arg_neg_coe_angle hne, planeComplex_smul, planeComplex_smul, Complex.real_smul,
    Complex.real_smul, Complex.arg_real_mul _ (by norm_num), Complex.arg_real_mul _ (by norm_num)]
  abel

/-- C5 (S10). The lowest-leftmost vertex is supporting for `N = (1, 0)` and has a nonzero turn
(a flat turn there would make both incident edges vertical and antiparallel, contradicting
`consecutive`). -/
theorem exists_supporting_vertex_turn_ne_zero [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (h : Embedded P) :
    ∃ (N : Plane) (i : ZMod n), IsSupportingVertex P N i ∧ principalTurn P i ≠ 0 := by
  -- the lexicographically (x, y)-least vertex
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ
    (fun j : ZMod n => toLex ((P j).1, (P j).2)) Finset.univ_nonempty
  have hmin : ∀ j, (P i).1 < (P j).1 ∨ (P i).1 = (P j).1 ∧ (P i).2 ≤ (P j).2 := by
    intro j
    have := hi j (Finset.mem_univ j)
    rw [Prod.Lex.le_iff] at this
    simpa using this
  have hx : ∀ j, (P i).1 ≤ (P j).1 := by
    intro j
    rcases hmin j with h1 | ⟨h1, -⟩
    · exact h1.le
    · exact h1.le
  refine ⟨(1, 0), i, ⟨?_, fun j => ?_⟩, ?_⟩
  · intro h0
    have := congrArg Prod.fst h0
    simp at this
  · simp only [planeDot, Prod.fst_sub, Prod.snd_sub]
    have := hx j
    linarith
  · -- a zero turn would make both incident edges vertical and antiparallel
    intro hzero
    have hu := h.edge_ne_zero (i - 1)
    have hv := h.edge_ne_zero i
    obtain ⟨r, hr, hre⟩ := (principalAngle_eq_zero_iff hu hv).mp hzero
    have hi1 : (i - 1) + 1 = i := sub_add_cancel i 1
    have hu1 : (edge P (i - 1)).1 = (P i).1 - (P (i - 1)).1 := by
      simp only [edge, hi1, Prod.fst_sub]
    have hu2 : (edge P (i - 1)).2 = (P i).2 - (P (i - 1)).2 := by
      simp only [edge, hi1, Prod.snd_sub]
    have hv1 : (edge P i).1 = (P (i + 1)).1 - (P i).1 := by
      simp only [edge, Prod.fst_sub]
    have hv2 : (edge P i).2 = (P (i + 1)).2 - (P i).2 := by
      simp only [edge, Prod.snd_sub]
    have hre1 : (edge P i).1 = r * (edge P (i - 1)).1 := by
      rw [hre]
      rfl
    have hre2 : (edge P i).2 = r * (edge P (i - 1)).2 := by
      rw [hre]
      rfl
    have ha := hx (i - 1)
    have hb := hx (i + 1)
    have hu1z : (edge P (i - 1)).1 = 0 := by nlinarith
    have hxa : (P i).1 = (P (i - 1)).1 := by linarith
    have hxb : (P i).1 = (P (i + 1)).1 := by nlinarith
    have hya : (P i).2 ≤ (P (i - 1)).2 := by
      rcases hmin (i - 1) with h1 | ⟨-, h2⟩
      · exact absurd hxa h1.ne
      · exact h2
    have hyb : (P i).2 ≤ (P (i + 1)).2 := by
      rcases hmin (i + 1) with h1 | ⟨-, h2⟩
      · exact absurd hxb h1.ne
      · exact h2
    have hu2z : (edge P (i - 1)).2 = 0 := by nlinarith
    exact hu (Prod.ext hu1z hu2z)

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

end SM
