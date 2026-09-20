# U_TRANS_REPORT — unit TRANS (U5, `u_transport`), prover report

File: `work/drafts/contact/U_TRANS.lean` (copy of `Skeleton_FINAL.lean`; only §5.4 touched).
Check: `cd work/lean && lake env lean ../drafts/contact/U_TRANS.lean` → 0 errors, 10 warnings
"declaration uses sorry" (the other units' leaves: `u_circle`, `u_sl_radius`, `u_sl_family`,
`u_sl_reparam`, `u_sl_isotopy`, `u_legendrianFront`, `u_spatialOf`, `u_reading`, `u_regular`,
`u_family`).  `grep -c sorry`: 12 before → 11 after (the 11 = 10 remaining leaf bodies + the
docstring mention at line 19).  `diff Skeleton_FINAL.lean U_TRANS.lean`: one insertion block
(helpers, lines 567-690) and the replaced body of `u_transport` (lines 692-714); the only removed
line is `  sorry`.  No definition, structure, axiom, statement, name or docstring changed.

Axiom footprint (checked on a scratch copy with `#print axioms`):
`SM.u_transport` and `SM.utr_transport_of` depend on `[propext, Classical.choice, Quot.sound]` only —
no `sorryAx`, no `SM.src_contact` (the unit is pure transport on the accepted layer).

## Leaves

| leaf | status |
|---|---|
| `u_transport : U_transport` | **PROVED** |

No leaf left; no leaf believed false; no missing hypothesis found.  The statement is true as frozen.

## Proof route (as in PLAN_FINAL §6 U5, with one simplification)

`U_transport` gives `Lc`, `sp : SpatialLink 1`, `F : SmoothFront`, `G : Fin 1 → SmoothLoop`,
`S`, `hsp : sp.T i t = toSpace (Lc (2πt))`, `hF : IsLegendrianFrontOf Lc F`,
`r : sp.CleanCuspSmoothing G`, `m : F.Marking S`; wants `Nonempty (sp.HeightMarking G S) ∧ F.IsRounding S`.

1. **Dissolve `F.c = 1`.**  `obtain ⟨c, hc, comp, …⟩ := F; have : c = 1 := hF.one; subst`.  After this
   `F.c ≡ 1` definitionally, so `sp : SpatialLink 1` IS a `SpatialLink F.c` and `G : Fin 1 → SmoothLoop`
   IS a `Fin F.c → SmoothLoop` — no `Fin.cast`, no transport of `G` along `F.c = 1`.  All helpers are
   stated in the natural generality `sp : SpatialLink F.c`, `G : Fin F.c → SmoothLoop`.
2. **Two identities from `hsp` + `hF`** (proved inside the leaf):
   * `hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ` — `funext`, `hF.front`, `hsp`, then `rfl`
     (`xzOf (toSpace v) t = (v 0, v 2) = GenericFront.front Lc θ`).
   * `hleg : ∀ i t, (deriv (F.comp i).γ t).2 = yOf (sp.T i) t * (deriv (F.comp i).γ t).1` — the front
     loop is `t ↦ front Lc (2πt)`; `utr_hasDerivAt_front` computes its derivative
     `(2π·L′(2πt) 0, 2π·L′(2πt) 2)` (chain rule `HasDerivAt.scomp`, coordinates through
     `EuclideanSpace.proj`, `HasDerivAt.prodMk`); `yOf (sp.T i) t = Lc (2πt) 1` by `hsp`; then
     `linear_combination (2π) * (hF.hyp.legendrian (2πt))` with `GenericFront.alpha` unfolded
     (`α(L′) = L′ 2 − L 1 · L′ 0 = 0`).
3. **`utr_transport_of hproj hleg r m`**:
   * `geom : F.GeomRounding G := utr_geomRounding hproj r` — field for field from the
     `CleanCuspSmoothing` through `utr_cuspEquiv : F.Cusp ≃ sp.cuspSet` (the identity on parameters,
     `Equiv.subtypeEquivRight`; `F.IsCusp p ↔ sp.IsCusp p.1 p.2` is `vel_def` + `hproj`);
     `collar` is dropped; `center`, `clean`, `arc_in`, `arc_simple` rewrite `xzOf (sp.T _)` to
     `(F.comp _).γ` by `hproj`; `agree` goes through `e.symm` + `Equiv.apply_symm_apply`.
   * `F.IsRounding S := ⟨⟨G, geom, m⟩⟩` (the marking is the given slope-rule marking of `F`; the
     accepted `Rounding` structure asks for exactly `F.Marking S`).
   * `HeightMarking`: `SmoothFront.GeomMarking.ofMarking geom m : GeomMarking G S` (accepted,
     FrontGeomModel.lean) is a slope-rule reading of `G`; `utr_heightMarking_of_geomMarking` turns a
     slope-rule reading into the height-rule reading given `slopeOf G p < slopeOf G q ↔ sp.height p <
     sp.height q` at every `IsDoubleOf G p q` (the analogue of the accepted
     `HeightMarking.ofHeightOrder`); that equivalence is an EQUALITY of both sides:
     `geom.slopeOf_eq hd : slopeOf G p = F.slope p` (accepted, FrontRecordBridge) and
     `utr_slope_eq_height hleg hd : F.slope p = sp.height p` — `slope = z′/x′ = y·x′/x′ = y` with
     `x′ ≠ 0` from the accepted `F.vel_fst_ne_zero_of_isDouble` (cusps are not double points).
     Signs need no separate argument: `sgn_eq` of the `GeomMarking` is already `crossSignOf G`, which is
     what `HeightMarking.sgn_eq` asks for (so `CleanCuspSmoothing.crossSignOf_eq` was not needed —
     the sign transport happened inside the accepted `GeomMarking.ofMarking` via `GeomRounding.crossSignOf_eq`).

Simplification vs the plan: the plan routed the height marking through `CleanCuspSmoothing.occEquiv`
and `crossSignOf_eq`; the accepted `GeomMarking.ofMarking` (FrontGeomModel) already does the
occurrence/sign transport once `GeomRounding F G` is in hand, so the only new content is
"slope = height on a Legendrian at its double points" and the `GeomRounding` construction.
About 150 lines instead of the estimated 600.

## Helpers added (all `utr_`, all immediately before `u_transport` in §5.4)

| name | kind | content |
|---|---|---|
| `utr_isCusp_iff` | theorem | `F.IsCusp p ↔ sp.IsCusp p.1 p.2` under `hproj` |
| `utr_mem_cuspSet_iff` | theorem | `p ∈ F.cuspSet ↔ p ∈ sp.cuspSet` |
| `utr_cuspEquiv` | def | `F.Cusp ≃ sp.cuspSet` (identity on values) |
| `utr_cuspEquiv_apply_val`, `utr_cuspEquiv_symm_apply_val` | @[simp] theorems | `rfl` value lemmas |
| `utr_geomRounding` | def | `sp.CleanCuspSmoothing G → F.GeomRounding G` |
| `utr_heightMarking_of_geomMarking` | def | `GeomMarking G S → sp.HeightMarking G S` given slope-order = height-order at double points |
| `utr_slope_eq_height` | theorem | `F.slope p = sp.height p` at a double point of a Legendrian front |
| `utr_transport_of` | theorem | `U_transport`'s conclusion for `sp : SpatialLink F.c` from `hproj`, `hleg` |
| `utr_hasDerivAt_front` | theorem | `HasDerivAt (fun t => front Lc (2πt)) (2π·L′ 0, 2π·L′ 2) t` for smooth `Lc` |

Hypothesis shapes reusable by other units (U2/U3 produce exactly these objects):
`hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ` and
`hleg : ∀ i t, (deriv (F.comp i).γ t).2 = yOf (sp.T i) t * (deriv (F.comp i).γ t).1`.
`utr_hasDerivAt_front` is the front-velocity formula U2 needs for `no_vertical` (`x′ = 2π·L′ 0`).

## Mathlib / library pitfalls met

* `IsDoubleOf`, `slopeOf`, `crossSignOf`, `OccOf`, `GeomMarking` live in namespace `SM.SmoothFront`;
  the skeleton does not `open SmoothFront` (CeSmoothingRecord does), so they must be written
  `SmoothFront.IsDoubleOf` etc. in this file.  (`HeightMarking`'s own fields mention `OccOf G`
  resolved inside its defining file; from outside, qualify.)
* `ContDiff.differentiable` needs `1 ≤ ∞` in `WithTop ℕ∞`: the codebase idiom `(by decide)` works.
* `HasDerivAt.scomp` takes the point explicitly: `hL.scomp t hm`.
* Coordinates of an `EuclideanSpace ℝ (Fin 3)` curve: `(EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).hasFDerivAt.comp_hasDerivAt t h`,
  then `simpa [Function.comp_def, GenericFront.front]` closes `proj i (c • v) = c * v i` and the
  `∘`-shape (precedent: `td_hasDerivAt_snd_coord`, TransverseNeighborhood.lean).
* `subst` on `F.c = 1` after `obtain ⟨c, …⟩ := F` works (`have hone' : c = 1 := hone; subst hone'`);
  the structure-literal projections reduce definitionally, and `refine utr_transport_of (sp := sp) ?_ ?_ r m`
  unifies `SpatialLink 1` with `SpatialLink {c := 1, …}.c` without help.

## For the assembler

* `u_transport` is closed; `U_package_of u_legendrianFront u_spatialOf u_reading u_transport` needs
  only U2, U3, U4 now.  Nothing in this unit depends on `SM.src_contact`.
* If U2/U3 build `F` FROM `sp` (plan §6, `F.comp 0 = sp.projLoop 0` by `rfl`), `hproj` becomes `rfl`;
  the leaf does not rely on that and works with the propositional `IsLegendrianFrontOf` as frozen.
* The helpers were checked in a scratch file importing the same six modules before insertion; the
  compile of `U_TRANS.lean` takes ~9 s with the cached imports.
