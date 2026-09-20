# W3B_G_REPORT.md — Wave 3b, Unit G: the `j = 2` bigon sites on smoothing outputs (row 177 (6))

Written 2026-09-15 (bounded window, HARD STOP 00:30 UTC; audit A-177-1) by the Unit-G prover.
File: `work/drafts/moves/W3B_G.lean` = `W3_A1_Assembled.lean` (7827 lines) + the `w3bg_` block (section `Row177_6`,
right after `open Smoothing`) + the two owned `sorry` bodies replaced.  Compiles with `lake env lean` in ≈ 35 s
under load, **0 errors**; the two identity checks pass (`check_W3_identity.py W3_A1_Assembled.lean W3B_G.lean`:
all frozen blocks IDENTICAL; `check_W3_statements.py W3B_G.lean`: 42/42 skeleton statements byte-identical, no
skeleton declaration missing).  Nothing under `work/lean` touched; `lake build` never run.

## 0. Result in one paragraph

Both sub-leaves of Unit G, `w3g_bigonData_smooth_arcST` and `w3g_bigonData_smooth_arcTS`, are **FALSE as stated**
(rule 3).  The culprit is the single field `BigonData.hk : j + 3 ≤ (D.Γ.comp i).k`, i.e. `5 ≤ k` for `j = 2`: in the
self model (`sS`, `tS` on one component) the component carrying `cutStartS, arcST, cutEndT` has `kI − dd + 2`
strands, which equals **4** exactly when `t = s − 2` on that component (one old strand between the two cut points —
the smoothed crossing `x` is a kink); every other hypothesis of the frozen statement is satisfiable in that
configuration (`y` on `s` before `x`, `z` on `t` after `x`, the triangle `x y z` inside the kink loop, `clear` and
`clear_vertex` hold since the closing strand and the two vertices are outside the triangle).  Nothing in
`SpliceModel` excludes it (`cut_val` only gives `val + 2 < k`).  **Everything else in both statements is proved**:
`w3bg_bigonData_smooth_arcST_of_five` / `w3bg_bigonData_smooth_arcTS_of_five` are the frozen statements plus the one
hypothesis `hk5 : 5 ≤ k` on the component of the cut-start strand, sorry-free, `#print axioms` = `[propext,
Classical.choice, Quot.sound]`.  The two frozen sub-leaves now reduce to exactly that hypothesis (their `sorry` body is
`exact w3bg_…_of_five … (by sorry)`), so `w3g_*` still carry `sorryAx`, through `hk5` only.  In `D`'s own terms the
missing hypothesis is the **non-kink condition** `⟨s.1, s.2 − 1⟩ ≠ ⟨t.1, t.2 + 1⟩` (`arcST`) / `⟨t.1, t.2 − 1⟩ ≠
⟨s.1, s.2 + 1⟩` (`arcTS`): `w3bg_hk5_arcST_of_not_kink` / `_arcTS_` derive `5 ≤ k` from it by the model laws alone, and
`w3bg_bigonData_smooth_arcST_of_not_kink` / `_arcTS_of_not_kink` are the corrected sub-leaves with that hypothesis.

## 1. Closed / open / black boxes

| sub-leaf | state |
|---|---|
| `w3g_bigonData_smooth_arcST` (frozen, :9052, sorry :9072) | **open, FALSE as stated**; body = reduction to `hk5` (one `sorry`, the hypothesis `5 ≤ (Γ₀.comp (M.strandOf cutStartS _).1).k`) |
| `w3g_bigonData_smooth_arcTS` (frozen, :9082, sorry :9101) | **open, FALSE as stated**; body = reduction to `hk5` on the component of `cutStartT` |
| `w3bg_bigonData_smooth_arcST_of_five` (:7860) (new, corrected) | **PROVED**, sorry-free, standard axioms |
| `w3bg_bigonData_smooth_arcTS_of_five` (:8385) (new, corrected) | **PROVED**, sorry-free, standard axioms |
| `w3bg_hk5_arcST_of_not_kink` (:8911), `w3bg_hk5_arcTS_of_not_kink` (:8950) (new) | **PROVED**, standard axioms — `5 ≤ k` from the non-kink condition, model-independent |
| `w3bg_not_kink_of_ne_comp` (:9031) (new) | PROVED — in the mixed case (`s.1 ≠ t.1`) both non-kink conditions are trivial |
| `w3bg_bigonData_smooth_arcST_of_not_kink` (:8989), `_arcTS_of_not_kink` (:9010) (new) | **PROVED**, standard axioms — the corrected sub-leaves in `D`'s terms |

Black boxes consumed: none (Unit G uses only the accepted library `SM/Smoothing.lean`, `SM/BigonDeletion.lean`
(`um7_edgePt_mem_segment_iff`) and Mathlib).  No other unit's sub-leaf is touched or used.

`grep -c sorry`: before 10, after 11 — the 11th is a *comment line* in the `w3bg_` header mentioning `sorry`; the
`sorry` **terms** are 10 before and 10 after (the 8 untouched ones of Units B/E/H + the two `(by sorry)` for `hk5`
at the two `w3g_` sites).  `#print axioms` (scratch copy `W3B_G_Axioms.lean`, exit 0): `w3bg_…_of_five` ×2 and
`w3bg_line_convexHull` → `[propext, Classical.choice, Quot.sound]`; `w3g_bigonData_smooth_arcST/TS` →
`[propext, sorryAx, Classical.choice, Quot.sound]`.

## 2. The counterexample to `hk` (why rule 3 applies)

`compB` of the self model (Smoothing §7b) is `⟨kI − dd + 2, …⟩` with `dd = (bS − aS).val ∈ [2, kI − 2]`; its edges
are `old ⟨i, b+1+m⟩` (`m < kI − dd − 1`), `cutStartS`, `arcST`, `cutEndT`.  With `b = a − 2` (so `dd = kI − 2`)
it has 4 edges: `cutEndT, old (a−1), cutStartS, arcST`.  Concretely `P(a−2) = (0,0)`, `P(a−1) = (2,0)`,
`P(a) = (1,1)`, `P(a+1) = (1,−1)`: strand `a = [(1,1),(1,−1)]` crosses strand `a−2 = [(0,0),(2,0)]` at `x = (1,0)`;
`g` through `y = (1, ½)` (on `a` before `x`) and `z = (1½, 0)` (on `a−2` after `x`).  All hypotheses of the frozen
statement hold, `j = 2`, `k = 4`, `hk : 5 ≤ 4` fails.  Model-independently: the labels `a−1 … a+3` of the component
carry `old ⟨s.1, s.2−1⟩, cutStartS, arcST, cutEndT, old ⟨t.1, t.2+1⟩`, so `k ≥ 5` iff the first and last differ iff
`⟨s.1, s.2−1⟩ ≠ ⟨t.1, t.2+1⟩` — this is exactly `w3bg_hk5_arcST_of_not_kink` (and `k = 3` is impossible since it would
identify `old …` with `cutEndT`).  For the realiser: the condition says the RIII triangle's crossing `x = e ∩ f` is not
a kink of the one-component lift (the strand before `e` is not the strand after `f`); whether the 177 configuration
implies it is the parent's question (I did not check `esc_interface`'s hypotheses).

## 3. What the proof does (`w3bg_bigonData_smooth_arcST_of_five`, ≈ 520 lines; TS is the `s ↔ t`, `y ↔ z` copy)

Labels: `uIn := strandOf cutStartS`, `⟨uIn.1, uIn.2 + 1⟩ = strandOf arcST`, `⟨uIn.1, uIn.2 + 2⟩ = strandOf cutEndT`
(`kind_succ` + `kind_injective`); `hy/hz`: `y₀ = liftCrossing y` (`liftCrossing_origCrossing` transported along
`hy₀`), whose strands are `liftStrand y s = cutStartS` (by `hys`) and `liftStrand y g = old g`
(`w3bg_val_liftCrossing`, `w3bg_liftStrand_*`); `run_free`: `kind_ne_arc_of_mem`; `no_io`: a crossing on `cutStartS`
and `cutEndT` would have `origCrossing = x`, against `origCrossing_ne`; `same_over`: on `(D^x).switch y₀` the over
strand at `y₀` is `D^x`'s under strand, `orig` of which is `D.underStrand y` (`toDiagram_underStrand_orig`), at `z₀`
it is `overStrand₀ z₀` with `orig = D.overStrand z`; `orig_injOn_crossing` turns `hover` into the disjunction.
Parameters: the four `crossingParam`s of the switched diagram, `hty …` from `crossingParam_spec` (no relation to
`D`'s parameters is needed).  Geometry — the ONLY tool is the **line lemma** `w3bg_line_convexHull`: if the
generators of `S` lie on the segment `[a, b]` of the line `det v (· − p) = 0` or strictly on one side
(`0 < det v (· − p) * k`), the line meets `conv S` only in `[a, b]` (proof: `segment a b ∪ {open half-plane}` is
convex, `convexHull_min`; Mathlib's `convexJoin` file is not imported here, so this replaces it).  `in_iff`: line `s`,
`a, b = y, s⁻`, the far generators `t⁺, z` have `det es (· − p) · det es et > 0` (this is where `hzt` enters — the
orientation caveat D4), then `um7_edgePt_mem_segment_iff` on `Γ₀` gives `ty ≤ t`; `out_iff`: line `t`, `a, b = t⁺, z`,
far generators `y, s⁻` (uses `hys`); `s_iff`: line `g` through `y`, `a, b = y, z`, far generators `s⁻, t⁺` — their
strict side needs the **clearance** `ε < τs − t_y(s)` and `ε < t_z(t) − τt` from `r₁_le_dist_crossingPoint` +
`SmallEps.mul_es_lt / mul_et_lt` (so `s⁻ ∈ [y, x]`, `t⁺ ∈ [x, z]`), and the sign constant `k_g = det e_g (p − y)`
with `det e_g (t⁺ − y) · k_g > 0` by eliminating `det e_g e_t` through `det e_g (z − y) = 0`.  `clear`: old kinds via
`clear` and `K ⊆ Δ = conv{x, y, z}` (`s⁻ ∈ [y, x]`, `t⁺ ∈ [x, z]`, `convexHull_min`); `cutEndS`/`cutStartT` by the
line lemma + parameter comparison on `s`/`t`; `arcTS` by the two closed half-planes `det es (· − p) · d ≥ 0`,
`det et (· − p) · d ≥ 0` containing `K` (`w3bg_convexHull_subset_halfPlane'`), which force `θ = 1` and `θ = 0` on the
arc.  `clear_vertex` and `hsy`-independence: the hypothesis `clear_vertex` is NOT used (the vertex `P(a)` is excluded
by `in_iff` itself); `hsy`, `htz` are used only through `hys`, `hzt`.

## 4. D4 / D5 (what the realiser must supply; not derivable inside the sub-leaves)

* D4 (orientation): the sub-leaves take `hys, hzt` (ST: `y` before `x` on `s`, `z` after `x` on `t`; TS: the reverse)
  as hypotheses and use them exactly once each (the strict side of the far generators in `in_iff`/`out_iff`).  In the
  two other combinations the proof breaks precisely there (the far generators would straddle the line), consistent
  with the printed caveat "no bigon exists".  Deriving the coherent case from the 177 sign table is the realiser's job
  (D4 of the skeleton report), untouched here.
* D5 (`same_over`): the hypothesis `hover : D.overStrand y = g ↔ D.overStrand z ≠ g` is consumed as described in §3;
  for the *switched* output it is exactly what is needed because the switch at `y₀` flips one bit.  Not derived here.
* NEW (rule 3): `hk5` / the non-kink condition `⟨s.1, s.2−1⟩ ≠ ⟨t.1, t.2+1⟩` (ST) resp. `⟨t.1, t.2−1⟩ ≠ ⟨s.1, s.2+1⟩`
  (TS) must be added by the realiser or to the frozen statements at port time.  On a one-component lift with `n`
  strands it says the smoothed crossing `x` is not a kink (`f ≠ e − 2` resp. `e ≠ f − 2` in labels).

## 5. Checks, numbers, pitfalls

* Final file: 9202 lines (7827 + 1375 new).  Full compile `lake env lean ../drafts/moves/W3B_G.lean`: **0 errors**
  (≈ 30–36 s under load; last run 22:44 UTC / 6:44pm ET).  `sorry` lines: 4094 (B, optional), 7552, 7570, 7603 (E),
  9072, 9101 (G: the two `(by sorry)` = `hk5`), 9132, 9145, 9154, 9195 (H).  Identity checks: `check_W3_identity.py`: `G11_ConfigSw` structure,
  namespace block, `G11_core_sw_statement`, `G11_core_sw` statement, `esc_switch_riii_of_chain` all IDENTICAL (the
  line `imports = draft's + SM.BigonDeletion: False` is pre-existing — it prints `False` on `W3_A1_Assembled.lean`
  against itself too); `check_W3_statements.py`: 42/42 byte-identical, `w3a_` count 20, no missing names.
* New material: 1375 lines, all `w3bg_`-prefixed, all inside section `Row177_6` before the frozen `w3g_` docstrings.
* Pitfalls met: (i) `Mathlib.Analysis.Convex.Join` (`convexJoin_segments`, `convexHull_insert`, `convexHull_union`) is
  NOT in the import closure — hence the segment-∪-open-half-plane convexity route; (ii) `((toDiagram …).switch y₀).Γ`
  is only *defeq* to `Γ₀`: `rw` with `Γ₀`-typed equations fails on goals typed through the switch (`HAdd` on two
  syntactically different `ZMod`s, `rw [M.seg_eq]`); the cure is `show`/type ascriptions to the `Γ₀` form before
  rewriting (`hOut`, `hqu' := (M.seg_eq u).subset hqu`); (iii) BigonData field names `y z hy hz htz` collide with the
  statement's hypothesis names — harmless in Lean, but any mechanical `s ↔ t` renaming must skip the field names,
  `occurs_old hgs hgt`, the `(y := …)` named arguments and the frozen hypothesis order; (iv) `rw [hκ] at hu_eq` with a
  dependent `Occurs` proof needs `subst` instead; (v) `push_neg` is deprecated for `push Not`.
* Time: started 22:01 UTC, ST proved 22:28, TS 22:35, full compile clean 22:39, hk5 lemmas 22:41, final compile 22:44 (all UTC; ET = −4h).  Well inside the 00:30 UTC hard stop.
