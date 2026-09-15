import CV.Rotation
import SM.NarrowSector
import SM.UniformRotation

/-! Ported 2026-09-14 from work/drafts/CV_uniformrot.lean (prover subagent; statement designed per work/reports/cv-lane-plan-20260913.md §153). Row CV:lem:uniformrot, main declaration `CV.uniformrot` (bundle `CV.UniformRotData`). Only this header added. -/

/-! # CV lane, rotation bounds for uniform and one-dissent polygons (reference/R/CV/d3_floor.tex, frozen)

Row 153 of the CV lane: CV:lem:uniformrot (d3_floor.tex:263–276; printed proof 277–302), "rotation
bounds for uniform and one-dissent polygons". "Here `rot` is as in Definition def:rot" (265).

Decision F2 (work/AUTHOR_NOTES.md, 2026-09-13): stated on CV's printed domain, the regular locus `𝓡_c`
of labelled tuples, with CV's own `rot` (CV.Rotation). SM's `rotationNumber` enters only through the
accepted theorem `rot_eq_rotationNumber`, never as an identification.

## Printed notion → Lean

* "closed polygon" with `c` corners: `L : LabelledTuple c`, `[NeZero c]`; corners `L i` for `i : ZMod c`,
  edges `δ_i = edge L i = L (i+1) − L i` (CV def:rot index convention, see CV.Rotation).
* "all of whose principal turns exist": `Regular L` — `CV.Regular` (CV.Setup, def:regular (B): nonzero
  edges, no doubling back), which is "every principal turn exists" (`regular_iff_principalTurns`) and is
  `SM.Regular` (`regular_iff_sm`). A regular polygon has `c ≥ 3` (`Regular.three_le`), so "a polygon has at
  least three corners" (278–279) needs no separate hypothesis.
* "principal turn" `τ_i`: `principalTurn L i = principalAngle (edge L (i−1)) (edge L i) ∈ (−π, π)`
  (CV.Setup; equal to `SM.principalTurn` by `principalTurn_eq_sm`; its sign is `turn L i`,
  `SM.principalTurn_sign`). "positive" / "negative" are the strict `0 < principalTurn L i` /
  `principalTurn L i < 0`.
* "`rot(L)`": `CV.rot L hL : ℤ` (CV:def:rot, polygon part, CV.Rotation), with lem:turnlift (ii)
  `two_pi_mul_rot : 2π · rot L hL = Σ_i principalTurn L i`. "`r = rot(L)` an integer" (274) is the type.
* "`L` has three corners": `c = 3`, taken as a hypothesis on the same `L` (so the equality clauses are
  conditionals, as printed: "with equality if `L` has three corners").
* (ii) "exactly one negative principal turn": an index `a` with `principalTurn L a < 0` and
  `∀ i ≠ a, 0 ≤ principalTurn L i`. The others are only NON-negative: d3:288–291 says the hypothesis
  "names one negative turn and admits turns equal to zero, which `Π` omits".
* (ii) "of magnitude `α ∈ (0, π)`": `α = −principalTurn L a`. That `0 < α < π` is automatic for a
  principal turn (`dissent_magnitude`, from `principalAngle_bounds`), so it is not a hypothesis.
* (ii) "`Π` the sum of the positive ones": `∑ i ∈ Finset.univ.erase a, principalTurn L i`, the sum over
  all corners other than `a`; zero turns contribute nothing, so this is the sum over the positive turns
  (`sum_pos_turns_eq_sum_erase`).

## Relation to SM and what had to be re-proved

The accepted `SM.uniform_rotation` (SM/UniformRotation.lean:64) states its clauses with `turn = ±1`
hypotheses; its one-dissent conjunct assumes every other turn is STRICTLY positive (`turn P i = 1` for
`i ≠ a`), and `SM.rotationNumber_ge_one_of_other_left_zero` (line 29) likewise. The printed (ii) admits
zero turns, so the bound `r ≥ 1` is re-proved here by the printed dual-vector argument (d3:284–302):
cut after the negative corner (`SM.shift a`), the edge directions then lie in a closed angular interval
of width `Π < π` swept from `δ_0`; the bisecting unit direction has positive dot product with every
edge (`positive_edge_projection_of_short_prefix_nonneg`), contradicting `Σ δ_i = 0`
(`SM.no_positive_edge_projection`). The SM/NarrowSector pieces `edge_projection_from_prefix_index`,
`turnPrefix_lt_pi_of_rotation_nonpos` and `no_positive_edge_projection` carry no positivity hypothesis
and are reused; only the prefix bounds (`turnPrefix_nonneg_of_nonneg`, `turnPrefix_mono_of_nonneg`) are
redone under non-negativity ("a zero turn does not widen that interval", 288).

Clause (i) is proved as printed: `2π rot(L) = Σ τ_i > 0` gives `rot(L) ≥ 1`; "with three corners the
sum is also below `3π`" is `SM.rotationNumber_strict_bound` (`2|rot| < c`, from `Σ|τ_i| < cπ`); the
negative claims come from orientation reversal (`rot_reversal`, `SM.principalTurn_reversal`).

## Readings chosen

(a) "equality in absolute value for three corners" in the negative case is rendered as `rot L hL = −1`
(equivalent to `|rot L hL| = 1` given `rot L hL ≤ −1`). (b) `α` is written `−principalTurn L a`
(`= |principalTurn L a|` since the turn is negative). (c) The plan entry (work/reports/cv-lane-plan-
20260913.md §153) proposed one conjunction; per the row-bundle convention of CV.Rotation the clauses
are fields of `UniformRotData`, one per printed clause, and `uniformrot : UniformRotData` is the row
declaration.

Row declaration: `CV.uniformrot : UniformRotData`. -/

namespace CV

open SM

/-! ## The dual-vector argument under non-negativity (d3_floor.tex:284–302) -/

section Prefix

variable {n : ℕ} [NeZero n]

/-- `SM.turnPrefix_nonneg` with the turns away from index `0` only NON-negative ("admits turns equal
to zero", d3:286). -/
theorem turnPrefix_nonneg_of_nonneg {P : LabelledTuple n}
    (hp : ∀ i : ZMod n, i ≠ 0 → 0 ≤ SM.principalTurn P i) {k : ℕ} (hk : k < n) :
    0 ≤ turnPrefix P k := by
  apply Finset.sum_nonneg
  intro j hj
  have hjk := Finset.mem_range.mp hj
  exact hp _ (natIndex_ne_zero (by omega) (by omega))

/-- `SM.turnPrefix_mono` under the same weakening: the prefix sums are monotone. -/
theorem turnPrefix_mono_of_nonneg {P : LabelledTuple n}
    (hp : ∀ i : ZMod n, i ≠ 0 → 0 ≤ SM.principalTurn P i) {k l : ℕ}
    (hkl : k ≤ l) (hl : l < n) : turnPrefix P k ≤ turnPrefix P l := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
  intro j hj _
  have hjl := Finset.mem_range.mp hj
  exact hp _ (natIndex_ne_zero (by omega) (by omega))

/-- The dual vector `u` of the printed proof (d3:289–296): when the turns away from index `0` are
non-negative and their sum `Π = turnPrefix P (n−1)` is below `π`, "every edge direction of `L` lies in
a closed angular interval `I` of width `Π < π`", and the unit vector bisecting `I` has
"`⟨u, δ⟩ > 0` for every direction `δ ∈ I`, hence for every edge of `L`". -/
theorem positive_edge_projection_of_short_prefix_nonneg {P : LabelledTuple n} (h : SM.Regular P)
    (hp : ∀ i : ZMod n, i ≠ 0 → 0 ≤ SM.principalTurn P i)
    (hL : turnPrefix P (n - 1) < Real.pi) :
    ∀ i : ZMod n, 0 < planeDot
      (unitDirection ((planeComplex (edge P 0)).arg + turnPrefix P (n - 1) / 2)) (edge P i) := by
  intro i
  rw [edge_projection_from_prefix_index h i]
  have hn : n - 1 < n := by have hz := NeZero.ne n; omega
  have hb1 := turnPrefix_nonneg_of_nonneg hp i.val_lt
  have hb2 := turnPrefix_mono_of_nonneg hp (show i.val ≤ n - 1 by have := i.val_lt; omega) hn
  have hc : 0 < Real.cos (turnPrefix P i.val - turnPrefix P (n - 1) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  exact mul_pos (euclideanLength_pos (h i).2.1) hc

/-- "Suppose `r ≤ 0`. Then `Π ≤ α < π` … But the edges of a closed polygon sum to zero, so
`0 = ⟨u, Σ δ_i⟩ = Σ ⟨u, δ_i⟩ > 0`, a contradiction" (d3:284–302), in SM's normalisation with the
exceptional corner at index `0` (its turn may have any sign) and all other turns non-negative:
`rotationNumber P > 0`. `SM.rotationNumber_pos_of_other_principalTurns_pos` is the strict case. -/
theorem rotationNumber_pos_of_other_principalTurns_nonneg {P : LabelledTuple n}
    (h : SM.Regular P) (hp : ∀ i : ZMod n, i ≠ 0 → 0 ≤ SM.principalTurn P i) :
    0 < rotationNumber P := by
  by_contra hr
  have hL := turnPrefix_lt_pi_of_rotation_nonpos h (le_of_not_gt hr)
  exact no_positive_edge_projection P _
    (positive_edge_projection_of_short_prefix_nonneg h hp hL)

end Prefix

/-! ## Clause (i) (d3_floor.tex:267–271; proof 278–283) -/

section Uniform

variable {c : ℕ} [NeZero c]

/-- "each `τ_i > 0`, so the sum is positive and `rot(L) > 0`; being an integer, `rot(L) ≥ 1`"
(278–281), from `2π rot(L) = Σ_i τ_i` (lem:turnlift (ii), `two_pi_mul_rot`). -/
theorem one_le_rot_of_pos {L : LabelledTuple c} (hL : Regular L)
    (hp : ∀ i, 0 < principalTurn L i) : 1 ≤ rot L hL := by
  have h := two_pi_mul_rot L hL
  have hs : 0 < ∑ i, principalTurn L i :=
    Finset.sum_pos (fun i _ => hp i) Finset.univ_nonempty
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hr : (0 : ℝ) < rot L hL := (mul_pos_iff_of_pos_left h2).mp (by rw [h]; exact hs)
  have hz : (0 : ℤ) < rot L hL := by exact_mod_cast hr
  omega

/-- "With three corners the sum is also below `3π`" (281): `2|rot(L)| < c` (`SM.rotationNumber_strict_bound`,
from `Σ_i |τ_i| < cπ`), so for `c = 3` the integer `rot(L)` satisfies `|rot(L)| ≤ 1`. -/
theorem abs_rot_le_one_of_three {L : LabelledTuple c} (hL : Regular L) (h3 : c = 3) :
    |rot L hL| ≤ 1 := by
  have hb := rotationNumber_strict_bound ((regular_iff_sm L).mp hL)
  rw [← rot_eq_rotationNumber hL] at hb
  have h3' : (c : ℝ) = 3 := by exact_mod_cast h3
  rw [h3'] at hb
  have hlt : ((|rot L hL| : ℤ) : ℝ) < 2 := by rw [Int.cast_abs]; linarith
  have hlt' : |rot L hL| < 2 := by exact_mod_cast hlt
  obtain ⟨h1, h2⟩ := abs_lt.mp hlt'
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- "with equality if `L` has three corners" (269), positive case: "forcing `rot(L) = 1`" (281–282). -/
theorem rot_eq_one_of_pos_three {L : LabelledTuple c} (hL : Regular L)
    (hp : ∀ i, 0 < principalTurn L i) (h3 : c = 3) : rot L hL = 1 := by
  have h1 := one_le_rot_of_pos hL hp
  have h2 := (abs_le.mp (abs_rot_le_one_of_three hL h3)).2
  omega

/-- "If all turns are negative, `rot(L) ≤ −1`" (269–270): "Orientation reversal in the same lemma gives
both negative claims" (282–283) — the reversal has principal turns `−τ_{2−i} > 0`
(`SM.principalTurn_reversal`) and `rot(reversal L) = −rot(L)` (`rot_reversal`). -/
theorem rot_le_neg_one_of_neg {L : LabelledTuple c} (hL : Regular L)
    (hn : ∀ i, principalTurn L i < 0) : rot L hL ≤ -1 := by
  have hSM := (regular_iff_sm L).mp hL
  have hrev : Regular (reversal L) := regular_reversal' hL
  have hpos : ∀ i, 0 < principalTurn (reversal L) i := by
    intro i
    have hi := hn (2 - i)
    rw [principalTurn_eq_sm] at hi ⊢
    rw [SM.principalTurn_reversal hSM i]
    linarith
  have h1 := one_le_rot_of_pos hrev hpos
  rw [rot_reversal hL hrev] at h1
  omega

/-- "again with equality in absolute value for three corners" (270–271), i.e. `rot(L) = −1`. -/
theorem rot_eq_neg_one_of_neg_three {L : LabelledTuple c} (hL : Regular L)
    (hn : ∀ i, principalTurn L i < 0) (h3 : c = 3) : rot L hL = -1 := by
  have h1 := rot_le_neg_one_of_neg hL hn
  have h2 := (abs_le.mp (abs_rot_le_one_of_three hL h3)).1
  omega

end Uniform

/-! ## Clause (ii) (d3_floor.tex:272–275; proof 284–302) -/

section OneDissent

variable {c : ℕ} [NeZero c]

omit [NeZero c] in
/-- "of magnitude `α ∈ (0, π)`" (272–273) is automatic: a principal turn lies in `(−π, π)`
(`principalAngle_bounds`), so a negative one has `0 < α = −τ_a < π`. -/
theorem dissent_magnitude {L : LabelledTuple c} (hL : Regular L) {a : ZMod c}
    (ha : principalTurn L a < 0) :
    0 < -principalTurn L a ∧ -principalTurn L a < Real.pi := by
  have hb : -Real.pi < principalTurn L a ∧ principalTurn L a < Real.pi :=
    principalAngle_bounds (((regular_iff_sm L).mp hL) a)
  exact ⟨by linarith, by linarith [hb.1]⟩

/-- "let `Π` be the sum of the positive ones" (273): with one negative turn at `a` and the others
non-negative, the sum over the positive turns is the sum over all corners other than `a` — the zero
turns, which "`Π` omits" (286–287), contribute nothing. -/
theorem sum_pos_turns_eq_sum_erase {L : LabelledTuple c} {a : ZMod c}
    (ha : principalTurn L a < 0) (hother : ∀ i, i ≠ a → 0 ≤ principalTurn L i) :
    ∑ i ∈ Finset.univ.filter (fun i => 0 < principalTurn L i), principalTurn L i =
      ∑ i ∈ Finset.univ.erase a, principalTurn L i := by
  apply Finset.sum_subset
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    exact absurd hi' (not_lt.mpr ha.le)
  · intro i hi hni
    have hia := (Finset.mem_erase.mp hi).1
    have hnpos : ¬ 0 < principalTurn L i := fun h =>
      hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact le_antisymm (not_lt.mp hnpos) (hother i hia)

/-- "`Π − α = 2π r` with `r = rot(L)`" (273–274): "The identity is Lemma lem:turnlift (ii)" (284),
`two_pi_mul_rot`, with the sum split at the dissenting corner `a`. -/
theorem sum_erase_sub_eq {L : LabelledTuple c} (hL : Regular L) (a : ZMod c) :
    (∑ i ∈ Finset.univ.erase a, principalTurn L i) - (-principalTurn L a) =
      2 * Real.pi * rot L hL := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ a), two_pi_mul_rot L hL]
  ring

/-- "and `r ≥ 1`" (275; proof 284–302): "Cut the traversal of `L` immediately after the negative
corner" — the cyclic shift `SM.shift a L` puts it at index `0` (`principalTurn_shift`,
`rotationNumber_shift`) — and run the dual-vector argument
(`rotationNumber_pos_of_other_principalTurns_nonneg`); an integer above `0` is at least `1`. The sign
of the turn at `a` is not needed for this bound. -/
theorem one_le_rot_of_one_dissent {L : LabelledTuple c} (hL : Regular L) (a : ZMod c)
    (hother : ∀ i, i ≠ a → 0 ≤ principalTurn L i) : 1 ≤ rot L hL := by
  have hSM : SM.Regular L := (regular_iff_sm L).mp hL
  have hs : SM.Regular (shift a L) := (regular_shift a L).mpr hSM
  have ht : ∀ i : ZMod c, i ≠ 0 → 0 ≤ SM.principalTurn (shift a L) i := by
    intro i hi
    rw [principalTurn_shift, ← principalTurn_eq_sm]
    apply hother
    intro he
    apply hi
    have he' : i + a = 0 + a := by simpa only [zero_add] using he
    exact add_right_cancel he'
  have hpos : 0 < rotationNumber L := by
    have h0 := rotationNumber_pos_of_other_principalTurns_nonneg hs ht
    rwa [rotationNumber_shift] at h0
  have h1 : (1 : ℝ) ≤ rot L hL := by
    rw [rot_eq_rotationNumber hL]
    exact rotationNumber_ge_one_of_pos hSM hpos
  exact_mod_cast h1

end OneDissent

/-! ## Row bundle -/

/-- CV lem:uniformrot (d3_floor.tex:263–276), clause by clause; "Here `rot` is as in Definition
def:rot" (265), i.e. `CV.rot` of CV.Rotation. "Principal turns exist" is `Regular L`; `L` has `c`
corners. -/
structure UniformRotData : Prop where
  /-- (i) "Let `L` be a closed polygon all of whose principal turns exist and are positive. Then
  `rot(L) ≥ 1`" (267–269). -/
  pos_ge_one : ∀ (c : ℕ) [NeZero c] (L : LabelledTuple c) (hL : Regular L),
    (∀ i, 0 < principalTurn L i) → 1 ≤ rot L hL
  /-- (i) "with equality if `L` has three corners" (269): `c = 3` forces `rot(L) = 1`. -/
  pos_three : ∀ (c : ℕ) [NeZero c] (L : LabelledTuple c) (hL : Regular L),
    (∀ i, 0 < principalTurn L i) → c = 3 → rot L hL = 1
  /-- (i) "If all turns are negative, `rot(L) ≤ −1`" (269–270). -/
  neg_le_neg_one : ∀ (c : ℕ) [NeZero c] (L : LabelledTuple c) (hL : Regular L),
    (∀ i, principalTurn L i < 0) → rot L hL ≤ -1
  /-- (i) "again with equality in absolute value for three corners" (270–271): `|rot(L)| = 1`, which
  with the sign of the previous clause is `rot(L) = −1`. -/
  neg_three : ∀ (c : ℕ) [NeZero c] (L : LabelledTuple c) (hL : Regular L),
    (∀ i, principalTurn L i < 0) → c = 3 → rot L hL = -1
  /-- (ii) "Let `L` be a closed polygon whose principal turns all exist, with exactly one negative
  principal turn, of magnitude `α ∈ (0, π)`, and let `Π` be the sum of the positive ones. Then
  `Π − α = 2π r` with `r = rot(L)` an integer, and `r ≥ 1`" (272–275). The one negative turn is the
  one at `a`; the others are non-negative (zero turns admitted, d3:288–291); `α = −principalTurn L a`,
  and `0 < α < π` is automatic (`dissent_magnitude`); `Π` is the sum over `Finset.univ.erase a`, which
  equals the sum over the positive turns because zero turns contribute nothing
  (`sum_pos_turns_eq_sum_erase`); `r = rot L hL : ℤ` is an integer by type. -/
  one_dissent : ∀ (c : ℕ) [NeZero c] (L : LabelledTuple c) (hL : Regular L) (a : ZMod c),
    principalTurn L a < 0 → (∀ i, i ≠ a → 0 ≤ principalTurn L i) →
      (∑ i ∈ Finset.univ.erase a, principalTurn L i) - (-principalTurn L a) =
          2 * Real.pi * rot L hL ∧
        1 ≤ rot L hL

/-- CV lem:uniformrot (row 153). -/
theorem uniformrot : UniformRotData where
  pos_ge_one := fun _ _ _ hL hp => one_le_rot_of_pos hL hp
  pos_three := fun _ _ _ hL hp h3 => rot_eq_one_of_pos_three hL hp h3
  neg_le_neg_one := fun _ _ _ hL hn => rot_le_neg_one_of_neg hL hn
  neg_three := fun _ _ _ hL hn h3 => rot_eq_neg_one_of_neg_three hL hn h3
  one_dissent := fun _ _ _ hL a _ hother =>
    ⟨sum_erase_sub_eq hL a, one_le_rot_of_one_dissent hL a hother⟩

end CV
