import SM.CeSmoothingRecord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # SM ce:rounding — ordinary rounding of the exact cusp germs (FIXED STATEMENT, FINAL)

Source: reference/SM/sm-3-statesum.tex:3029-3062 (lemma environment; statement 3031-3058, `\status`
3059-3061, `\end{lemma}` 3062), proof 3063-3169.  Judge's synthesis of the two architects' designs
(PLAN_A.md, PLAN_B.md); verdict, clause map, chain and units in PLAN_FINAL.md.

**Vocabulary is IMPORTED, not restated.**  The shared spatial-link vocabulary of rows 89/90/91 lives
in the library module SM/CeSmoothingRecord.lean (row 90, ported 2026-09-14 08:17Z; AUTHOR_NOTES
decision D-1: "rows 89 and 91 MUST import the vocabulary from SM/CeSmoothingRecord.lean rather than
redeclare the memo's sketch"): `SpatialLink`, `projLoop`, `height`, `IsCusp`, `cuspSet`,
`ExactCuspGerm`, `CuspedProjection`, `RegularGenericProjection`, `HeightMarking`,
`CleanCuspSmoothing` (WITH the row-90 field `collar`), `SpatialFamily` (jointly `C^∞` on `ℝ × ℝ`),
`CuspRoundingFamily` (the memo's conclusion structure, which row 90 quantifies over), and the proved
consequences `CleanCuspSmoothing.isDoubleOf_iff`, `deriv_eq_of_isDouble`, `occSetOf_eq`,
`crossSignOf_eq`, `eval_eq_of_isDouble`.

Check: `cd work/lean && lake env lean ../drafts/cerounding/Statements_FINAL.lean` — 0 errors, exactly
ONE `sorry` (= `SM.ce_rounding : CeRoundingData`, proved in Skeleton_FINAL.lean from the chain).

## The printed statement (sm-3:3031-3058, verbatim)

"Let L be a smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³,
and write p = (x,z) for its projection. Its only failures of regularity are finitely many isolated
cusps; all other projected coincidences are finitely many transverse double points. Assume there are
no triple points or cusps on another branch, and the two y heights at every double point are
distinct. At every cusp assume the exact germ, on a parameter interval with smooth coordinate
u = y − y₀,
  x = x₀ + A u²,  y = y₀ + u,  z = z₀ + A y₀ u² + (2A/3) u³,  A ≠ 0.          (ce:exact-germ)
The coordinate u may increase or decrease along the prescribed component orientation, which is not
changed. The formula is a hypothesis, not an appeal to a classification of singularities.

There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L, fixed
outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an ordinary
finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and retains every
original crossing with its oriented decorated data. All original parameter circles, component labels
and traversal orientations are retained. With no cusps take the constant family.
This is an ordinary spatial deformation, not asserted Legendrian or positive transverse, and it
carries no self-linking transport statement."

## Printed clause → Lean (hypotheses; all in the imported class `CuspedProjection`)

| tex | printed | Lean |
|---|---|---|
| 3031-3032 | a smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³ | `L : SpatialLink c`, `0 < c`: `T : Fin c → ℝ → Space`, `C^∞` (`smooth`), 1-periodic (`periodic`, FR-3), jointly injective on the union of circles (`embedded`), nonvanishing derivative (`regular`); orientation = parameter direction (T-1) |
| 3032 | write p = (x,z) for its projection | `L.projLoop i : SmoothLoop`, `γ = xzOf (L.T i)` (the plain-loop vocabulary `IsDoubleOf`, `occSetOf`, `crossSignOf` of SM/FrontRecordBridge.lean applies) |
| 3033-3034 | its only failures of regularity are finitely many isolated cusps | `IsCusp i t := deriv (xzOf (L.T i)) t = 0`; `cuspSet` (fundamental period) `.Finite` (`cusps_finite`; a finite set is isolated) |
| 3034-3035 | all other projected coincidences are finitely many transverse double points | `doubles_finite`, `transverse` (det of the projected velocities ≠ 0) |
| 3035-3036 | no triple points or cusps on another branch | `no_triple`; "cusps on another branch" is a CONSEQUENCE of `transverse` (`CuspedProjection.not_isCusp_of_isDouble`, proved below: `det 0 v = 0`) — no extra field |
| 3036 | the two y heights at every double point are distinct | `heights_distinct` (`height p = yOf (L.T p.1) p.2`) |
| 3037-3042 | at every cusp the exact germ on a parameter interval with smooth coordinate u = y − y₀ | `exact_germ : ∀ p ∈ cuspSet, ExactCuspGerm p.1 p.2` = `∃ A ≠ 0, ∃ δ > 0`, `y′ ≠ 0` on `(t₀−δ, t₀+δ)` (so `u` is a smooth coordinate there, of either direction) and the three displayed formulas with `u = y t − y t₀` |
| 3043-3046 | u may increase or decrease; orientation not changed; the formula is a hypothesis | `y′ ≠ 0` of either sign; the family keeps the parameter (below); `exact_germ` is a field of the hypothesis class |

## Printed clause → Lean (conclusion; witness `CuspRoundingWitness L`, bundle `CeRoundingData`)

| tex | printed | Lean |
|---|---|---|
| 3048-3049 | a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings | `fam : SpatialFamily c` (`G : ℝ → SpatialLink c`, each slice embedded and regular; `joint_smooth : ContDiff ℝ ∞` of the uncurried map on `ℝ × ℝ` — the memo's/library's reading, see CE-5) |
| 3049 | with L_0 = L | `start : fam.G 0 = L` |
| 3049-3050 | fixed outside disjoint cusp parameter intervals | `a b : L.cuspSet → ℝ`, `a_lt`, `lt_b`, `len`, `fixed_outside` (library fields); "disjoint" ON THE CIRCLE: `intervals_disjoint_circle` (this file; the library's `intervals_disjoint` is its `n = 0` case) |
| 3050-3051 | for every λ > 0 its xz projection is an ordinary finite regular generic diagram | `generic : 0 < λ → λ ≤ 1 → (fam.G λ).RegularGenericProjection` (regular, finitely many transverse double points, no triple point, distinct heights — the over rule "smaller y over" is then determined); the POLYGONAL reading of that diagram (`HeightMarking`, FR-1) is the consumer's hypothesis, not asserted (CE-6) |
| 3051-3052 | it cleanly smooths the cusps | `clean` (library: `Nonempty (L.CleanCuspSmoothing (fam.G λ).projLoop)`, the definition sentence of ce:smoothing-record incl. `collar`) and, literally, `U` + `clean_in` (this file): the clean smoothing happens in the neighbourhoods `U k` and on the SAME intervals `(a k, b k)` as the fixing clause, for every `λ ∈ (0,1]` |
| 3052 | creates no crossing, and retains every original crossing | `same_doubles : IsDoubleOf (fam.G λ).projLoop p q ↔ IsDoubleOf L.projLoop p q` (→ = creates none, ← = retains all) |
| 3052-3053 | with its oriented decorated data | `same_data`: the over-first tangent-determinant sign (`crossSignOf`) and the height order (over = smaller `y`) are unchanged; pairing and cyclic order are literally unchanged (same parameters on the same circles); the oriented branches themselves are unchanged as a THEOREM (`CuspRoundingFamily.deriv_eq_of_isDouble`, below), not a field |
| 3053-3054 | all original parameter circles, component labels and traversal orientations are retained | structural: every slice is a `SpatialLink c` on the same `Fin c` and the same 1-periodic parameter, in the parameter direction (T-1); the family changes only `T`; bundle field `circles_retained` states the checkable residue |
| 3054 | with no cusps take the constant family | `CeRoundingData.const_of_no_cusps`: when `cuspSet = ∅` the constant family `fun _ => L` is a witness |
| 3055-3057 | ordinary spatial deformation; not Legendrian / positive transverse; no sl transport | disclaimer: no contact condition and no `sl` occur in the conclusion; nothing to prove |

## Readings recorded (CE-1..CE-9; to be cited in the review)

CE-1 orientation = parameter direction; smooth = `C^∞`; a parameter circle = a 1-periodic map of `ℝ`
(T-1, FR-3).  CE-2 "spatial embedding" = injective on the union of the circles + nonvanishing
derivative (an embedding of a compact 1-manifold is an injective immersion; cp:finite-contact-path
says "with nonvanishing parameter derivative").  CE-3 "cusp" = zero of the projected velocity.
CE-4 "smooth coordinate u = y − y₀ on a parameter interval" = `y′ ≠ 0` on the open interval (strictly
monotone `u`, either direction).  CE-5 "jointly smooth family, 0 ≤ λ ≤ 1" = the library's
`SpatialFamily`: `G : ℝ → SpatialLink c` with `ContDiff ℝ ∞` of the uncurried map on `ℝ × ℝ`; the
printed clauses concern `[0,1]` and the values elsewhere carry no printed claim ("embeddedness outside
[0,1] is not claimed", sm-3:3103-3104); the type nevertheless makes every slice a `SpatialLink`.  The
construction meets this with the time clamp `μ = Real.smoothTransition λ` (on `[0,1]` the printed
family in the reparametrized time `μ`); a literal alternative (`ContDiffOn` on `Icc 0 1 ×ˢ univ`,
design B) is equivalent up to this reparametrization and is recorded for the row-91 unit.  CE-6
"ordinary finite regular generic diagram" = `RegularGenericProjection`, the SM's own smooth diagram
notion (sm-3:341-343) with the height over-rule of fd:contact; the polygonal record-carrying
`Diagram` is the consumer's FR-1 reading (`HeightMarking`) and is NOT produced by the row (GAP-1,
closed by design).  CE-7 "cleanly smooths" = `CleanCuspSmoothing` (the definition sentence of
ce:smoothing-record, field for field the accepted `GeomRounding`, plus row 90's `collar`), with one
neighbourhood and one interval per cusp for the whole family.  CE-8 "oriented decorated data" = sign +
height order at the unchanged parameters (the branches are unchanged too, as a theorem).  CE-9
"disjoint cusp parameter intervals" = disjoint on the circle (modulo `ℤ`).

## What this file adds to the imported vocabulary

* `CuspRoundingWitness L extends CuspRoundingFamily L` with `intervals_disjoint_circle` (CE-9), `U`,
  `clean_in` (CE-7).  Row 90 quantifies over `CuspRoundingFamily L`; every witness projects to one
  (`toCuspRoundingFamily`), so row 90's `D_ε` fields are non-vacuous once the row is proved (its K-3).
  RECOMMENDED for the row-90 unit: fold the three fields into `CuspRoundingFamily` (replace
  `intervals_disjoint` by the circle version; add `U`; strengthen `clean` to `clean_in`) — then this
  extension collapses to the library structure and nothing else changes (row 90 uses only `fam.G 1`,
  `clean 1`, `same_doubles`, `same_data`).
* `CeRoundingData` — one field per printed sentence of the conclusion (the accepted `RoundingData`
  pattern, SM/Rounding.lean §6): `exists_family` carries the theorem; the other fields are the printed
  sentences read on a witness (projections), plus `const_of_no_cusps`.
* `SpatialLink.ext'`, `CuspedProjection.not_isCusp_of_isDouble` (the printed "no cusps on another
  branch"), `CuspRoundingFamily.deriv_eq_of_isDouble` (unchanged branches at the old crossings). -/

namespace SM

open Link SmoothFront
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. Clause readings proved on the imported vocabulary -/

namespace SpatialLink

variable {c : ℕ} (L : SpatialLink c)

/-- two `SpatialLink`s with the same maps are equal (the other fields are proofs) -/
theorem ext' {L L' : SpatialLink c} (h : L.T = L'.T) : L = L' := by
  cases L; cases L'; cases h; rfl

/-- "no … cusps on another branch": a double point never sits at a cusp — a consequence of
`transverse`, since the determinant with a vanishing velocity is `0` -/
theorem CuspedProjection.not_isCusp_of_isDouble (h : L.CuspedProjection) {p q : Fin c × ℝ}
    (hd : IsDoubleOf L.projLoop p q) : ¬ L.IsCusp p.1 p.2 := by
  intro hc
  apply h.transverse p q hd
  unfold IsCusp at hc
  rw [hc]
  simp [det]

end SpatialLink

namespace CuspRoundingFamily

variable {c : ℕ} {L : SpatialLink c} (R : CuspRoundingFamily L)

/-- "retains every original crossing with its oriented [decorated data]": the oriented branches
(projected velocities) at every original double point are `L`'s — a consequence of `clean` through
the library's `CleanCuspSmoothing.deriv_eq_of_isDouble`.  A theorem, not a field: the printed
decorated data (sign, height order) are the fields of `same_data`. -/
theorem deriv_eq_of_isDouble (hfin : L.cuspSet.Finite) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    {p q : Fin c × ℝ} (hd : IsDoubleOf L.projLoop p q) :
    deriv (xzOf ((R.fam.G lam).T p.1)) p.2 = deriv (xzOf (L.T p.1)) p.2 :=
  (Classical.choice (R.clean lam h0 h1)).deriv_eq_of_isDouble hfin hd

end CuspRoundingFamily

/-! ## 2. Row 89 ce:rounding: the conclusion as a witness structure -/

/-- The conclusion of ce:rounding as delivered by row 89: the library's `CuspRoundingFamily L`
(row 90's object; "a jointly smooth family L_λ … of oriented spatial embeddings with L_0 = L, fixed
outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an ordinary
finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and retains every
original crossing with its oriented decorated data. All original parameter circles, component labels
and traversal orientations are retained.") together with two clauses the memo's structure
understates, read literally:
* "disjoint cusp parameter intervals": disjoint ON THE CIRCLE — no integer translate of one interval
  of a circle meets another interval of the same circle (the library's `intervals_disjoint` is the
  `n = 0` case);
* "It cleanly smooths the cusps": in one clean cusp neighbourhood `U k` per cusp (the printed `V`),
  chosen once for the whole family, and on the SAME parameter intervals `(a k, b k)` on which it is
  "fixed outside" (the printed proof: "Each modified portion is one regular embedded oriented arc in
  a clean cusp neighbourhood").
The family is indexed by all of `ℝ` (`SpatialFamily`); the printed clauses concern `0 ≤ λ ≤ 1`. -/
structure CuspRoundingWitness {c : ℕ} (L : SpatialLink c) extends CuspRoundingFamily L where
  /-- "disjoint cusp parameter intervals", on the circle -/
  intervals_disjoint_circle : ∀ k k', k ≠ k' → k.1.1 = k'.1.1 → ∀ n : ℤ,
    Disjoint (Set.Ioo (a k) (b k)) (Set.Ioo (a k' + n) (b k' + n))
  /-- the clean cusp neighbourhoods, one per cusp, for the whole family -/
  U : L.cuspSet → Set Plane
  /-- "It cleanly smooths the cusps": in `U`, on the intervals `(a, b)` of the fixing clause -/
  clean_in : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
    ∃ cs : L.CleanCuspSmoothing (fam.G lam).projLoop, cs.U = U ∧ cs.a = a ∧ cs.b = b

/-! ## 3. The row bundle: one field per printed sentence of the conclusion -/

/-- Lemma ce:rounding (sm-3:3029-3062), one field per printed sentence.  `exists_family` carries the
theorem; the remaining fields are the printed sentences read on a witness (projections of
`CuspRoundingWitness`, in the pattern of the accepted `RoundingData`), plus the printed "With no cusps
take the constant family".  The two closing disclaimers ("an ordinary spatial deformation, not
asserted Legendrian or positive transverse … no self-linking transport statement") assert nothing
and have no field. -/
structure CeRoundingData : Prop where
  /-- "There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L,
  fixed outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an
  ordinary finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and
  retains every original crossing with its oriented decorated data." — for every `L` of the printed
  input class on a nonempty union of circles -/
  exists_family : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    Nonempty (CuspRoundingWitness L)
  /-- "a jointly smooth family L_λ … of oriented spatial embeddings with L_0 = L": joint `C^∞`
  smoothness of the uncurried map, every slice embedded and regular, start at `L` -/
  smooth_embeddings_start : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L),
    (∀ i, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (W.fam.G p.1).T i p.2)) ∧
    (∀ (lam : ℝ) (i j : Fin c) (s t : ℝ), (W.fam.G lam).T i s = (W.fam.G lam).T j t →
      i = j ∧ SameT s t) ∧
    (∀ (lam : ℝ) (i : Fin c) (t : ℝ), deriv ((W.fam.G lam).T i) t ≠ 0) ∧
    W.fam.G 0 = L
  /-- "fixed outside disjoint cusp parameter intervals" (disjoint on the circle) -/
  fixed_outside_disjoint : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L),
    (∀ k, W.a k < k.1.2 ∧ k.1.2 < W.b k ∧ W.b k - W.a k < 1) ∧
    (∀ k k', k ≠ k' → k.1.1 = k'.1.1 → ∀ n : ℤ,
      Disjoint (Set.Ioo (W.a k) (W.b k)) (Set.Ioo (W.a k' + n) (W.b k' + n))) ∧
    ∀ (lam : ℝ) (i : Fin c) (t : ℝ),
      (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (W.a k) (W.b k)) →
      (W.fam.G lam).T i t = L.T i t
  /-- "such that for every λ > 0 its xz projection is an ordinary finite regular generic diagram" -/
  generic_slices : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L) (lam : ℝ),
    0 < lam → lam ≤ 1 → (W.fam.G lam).RegularGenericProjection
  /-- "It cleanly smooths the cusps, creates no crossing, and retains every original crossing with
  its oriented decorated data." -/
  clean_no_new_retains : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L) (lam : ℝ),
    0 < lam → lam ≤ 1 →
    (∃ cs : L.CleanCuspSmoothing (W.fam.G lam).projLoop, cs.U = W.U ∧ cs.a = W.a ∧ cs.b = W.b) ∧
    (∀ p q : Fin c × ℝ, IsDoubleOf (W.fam.G lam).projLoop p q ↔ IsDoubleOf L.projLoop p q) ∧
    ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
      crossSignOf (W.fam.G lam).projLoop p q = crossSignOf L.projLoop p q ∧
      ((W.fam.G lam).height p < (W.fam.G lam).height q ↔ L.height p < L.height q)
  /-- "All original parameter circles, component labels and traversal orientations are retained":
  every slice lives on the same `c` parameter circles `ℝ/ℤ` (1-periodic in the same parameter), and
  outside the cusp intervals it is `L` itself -/
  circles_retained : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L) (lam : ℝ) (i : Fin c),
    Function.Periodic ((W.fam.G lam).T i) 1 ∧
    ∀ t : ℝ, (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (W.a k) (W.b k)) →
      (W.fam.G lam).T i t = L.T i t
  /-- "With no cusps take the constant family": for a cuspless `L` of the class the constant family
  is a witness -/
  const_of_no_cusps : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    L.cuspSet = ∅ → ∃ W : CuspRoundingWitness L, ∀ lam : ℝ, W.fam.G lam = L

/-- row 90's object: a witness is in particular a `CuspRoundingFamily` (non-vacuity of the class row
90 quantifies over, its K-3) -/
theorem CeRoundingData.exists_cuspRoundingFamily (h : CeRoundingData) {c : ℕ} (L : SpatialLink c)
    (hc : 0 < c) (hL : L.CuspedProjection) : Nonempty (CuspRoundingFamily L) :=
  let ⟨W⟩ := h.exists_family L hc hL
  ⟨W.toCuspRoundingFamily⟩

-- SKELETON-CUT (Skeleton_FINAL.lean reproduces everything above this line byte for byte)

/-- Lemma ce:rounding (row 89).  The only `sorry` of this file. -/
theorem ce_rounding : CeRoundingData := by
  sorry

end

end SM
