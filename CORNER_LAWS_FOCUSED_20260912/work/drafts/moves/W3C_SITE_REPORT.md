# W3C unit SITE — report (`work/drafts/moves/W3C_SITE.lean`)

Unit SITE of wave W3C, run 2026-09-15 23:19 – 23:55 UTC (bounded window, audit A-177-2).  File:
`W3C_SITE.lean` = `W3B_Assembled.lean` (11851 lines) + 433 lines of `w3cs_` material + the non-kink block (12285 →
12339 lines).  Compiles with `lake env lean` from `work/lean`: **0 errors** (warnings: the pre-existing deprecations and
`declaration uses sorry`).  Nothing under `work/lean` touched; no frozen statement, name or docstring edited.

## 0. Result

* **β1′ `w3bi_site_data` is PROVED**: `w3cs__w3bi_site_data_data_proof : w3bi_site_data`, and the leaf body of
  `w3bi_site_data_data` is now `exact w3cs__w3bi_site_data_data_proof` (statement byte-identical).
  `#print axioms` (on a scratch copy of the file): `SM.Link.w3bi_site_data_data` depends on
  `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**.  Consequently `w3bi_bigon_pair_data` and everything
  downstream that consumed β1′ lose that leaf; the remaining `sorry` leaves of `w3bi_extreme_selected` are the ones of
  the other units (§3).
* **D4 (the coherent orientation) HOLDS for every sign pattern** — no failure case.  It is not a half-plane
  computation but an identity: with `y − x = α·dir a`, `z − x = β·dir b`, `y − z = γ·dir c` (crossing parameters),
  taking `det(·, dir c)` gives `α·det(a,c) = β·det(b,c)`; the alternating triple has `sign det(a,c) = −sign det(b,c)`,
  and `α ≠ 0` (else `y = x` by `crossingPoint_injective`), so `α, β` have opposite signs — exactly
  `(τ_y < τs ∧ τt < τ_z) ∨ (τs < τ_y ∧ τ_z < τt)` (`w3cs_opposite_signs`, `w3cs_siteData_of_triangle`).  The
  `C.order` hypothesis (`x` before `y` on `m`) is NOT needed.
* **D5 (`hover`) PROVED** from the positive over-strand convention (`w3cs_pos_overStrand_eq_iff`: on
  `Γ.positiveDiagram` the over strand at `{s, t}` is `s` iff `det(dir s, dir t) > 0`) and the same alternating triple.
* **The NON-KINK condition of unit G is stated, not derived** (`w3cs_NotKink`, `w3cs_not_kink_arcST/_arcTS`
  projections, black box `w3cs_not_kink_site` / `w3cs_not_kink_site_data` with ONE new `sorry`).  Reason (§4): it is
  NOT implied by the site data — explicit counterexample — and at the lift level it is a combinatorial statement about
  the corner polygon that the leaf's hypotheses do not obviously give.

`grep -c sorry`: 8 before (W3B_Assembled) → **8 after** (7 after closing β1′, +1 for the new non-kink black box).
Sorry-using declarations: 7 before → 7 after (`w3bi_site_data_data` out, `w3cs_not_kink_site_data` in).

## 1. What was proved (all `w3cs_`, inserted in `section W3BI_REAL` just before `w3bi_site_data_data`)

D-level (any generic shadow `Γ`, `D := Γ.positiveDiagram hΓ`):
| name | content |
|---|---|
| `w3cs_det_lin`, `w3cs_det_self`, `w3cs_det_smul_self` | bilinearity facts for `det` |
| `w3cs_crossingParam_congr` | `crossingParam` depends only on the strand |
| `w3cs_sub_eq` | `pt y − pt x = (τ_y − τ_x) • dir s` for two crossings on one strand `s` |
| `w3cs_pos_overStrand_eq_iff` | positive over strand at `{s, t}` is `s` ↔ `0 < det(dir s, dir t)` |
| `w3cs_opposite_signs` | the D4 sign lemma |
| **`w3cs_siteData_of_triangle`** | `x = {a,b}`, `y = {a,c}`, `z = {b,c}`, alternating `sign det(a,b), det(a,c), det(b,c)`, closed triangle clear of other strands and all vertices ⟹ `w3bi_SiteData D x (pt y) (pt z)`.  Case split `sS D x = a` (then `tS = b`, `g = c`, `y` at `py`: first disjunct) / `sS D x = b` (roles of `y, z` swap, `y` at `pz`: second disjunct); the orientation disjunct swaps with it, `hover` is read backwards (`hover'`). |

Lift level (`section W3CS_Lift`, the W3E variable context):
| name | content |
|---|---|
| `w3cs_exact_symm` | `ExactTriangleVisitOrders P P' ↔` the `P' P` form (copy of `s174_exact_symm`, which is not imported here) |
| **`w3cs_site_data_lift`** | `w3bi_SiteData (geoPositiveLift hn hG hT q) x_H (pt x_eg) (pt x_fg)` from `hX`, `htri`, the alternating `crossingSign P` triple and `pt x_H = pt x_ef`.  The three lift crossings are `(singleCrossingEquiv).symm (xPair hmp/hmq/hpq)` (`G11_cfg_hmp/hmq/hpq`), identified with `x_H` by `Shadow.single_crossingPoint` + `gu2_xmp_eq` + `crossingPoint_injective`; strands `⟨0, G11_mE⟩ ⟨0, G11_pE⟩ ⟨0, G11_qE⟩` (`Finset.map_insert/map_singleton`, `singleStrandEquiv`); the alternating triple on `X` by `G11_carrierSign` ×3 (`(G11_vef hcef).2.val = e` etc. by `rfl`); `clear` from `G11_cfg_clear_frontier` + `G11_cfg_clear_vertex` through `G11_preconnected_meets_frontier` (the closed-triangle form, as `G11_ConfigSw.clear_edge`); `clear_vertex` from `G11_cfg_clear_vertex`. |
| `w3cs_triangle_transport` | `triangleCrossings P' ⊆ geoCarrierCrossings hP' T' q'` from `hcarr` and `htri` (stated over `CrossingGeometry` so that `hcarr` unifies) |
| **`w3cs__w3bi_site_data_data_proof`** | the leaf: the site glue of `w3bi_wall_data_of` verbatim (`esc_contact_owns`, `GT_empty_wall`, `GT_geoCarrierCrossings_eq_of_good`, `esc_contact_unique`, `subst`), the alternating triple `w3e_alt_of_completeLocal hGT t ht hef heg hfg hK` (its `strandSign` IS `crossingSign` by `rfl`), transported to `t'` by `hR.sign_eq`; `unfold CV.carrierDiagram`; `w3cs_site_data_lift` on each side (`hs`, `hX` for `t`; `fun s => (hs s).symm`, `w3cs_exact_symm hs hX`, `w3cs_triangle_transport` for `t'`). |

Not needed after all: `esc_lift_crossing` (the lift crossings are named directly), `w3e_xs_point` (proved in the
assembled file anyway), `C.order` / `hord`, `w3e_configOfSw` (nothing goes through `G11_ConfigSw`; the three
`G11_cfg_*` facts and `G11_carrierSign` suffice), `gu2_mem_segment_*`, `gu4_det_*`, any half-plane geometry.

## 2. Checks

* `lake env lean ../drafts/moves/W3C_SITE.lean` (from `work/lean`): exit 0, **0 errors**.
* `check_W3_identity.py Port_GenericTransportSw_draft.lean W3C_SITE.lean`: `G11_ConfigSw` structure, `namespace
  G11_ConfigSw` block, `G11_core_sw_statement`, `G11_core_sw` statement, `esc_switch_riii_of_chain`: all **IDENTICAL**
  (the two trailing `False` lines — imports and "`G11_core_sw` body starts with sorry" — are the same pre-existing
  checker notes as in W3B_REAL_REPORT §0: the imports gained `RProof.RALedgers` in wave B, and the body is proved).
* `check_W3_statements.py W3C_SITE.lean` (from `work/drafts/moves`): 42/42 skeleton statements byte-identical,
  `w3a_` count 20, no declaration missing.
* `#print axioms` on a scratch copy: `w3cs__w3bi_site_data_data_proof` and `w3bi_site_data_data`:
  `[propext, Classical.choice, Quot.sound]`.

## 3. Sorry map after this unit (7 declarations, 8 `sorry` tokens)

| declaration | owner | status |
|---|---|---|
| `w3b_reparam_switch` (:4093) | pre-existing (unit (b) helper, not in the β-leaf list) | untouched |
| `w3g_bigonData_smooth_arcST` / `_arcTS` (the two `(by sorry)` = `hk5`) | unit G | untouched — FALSE as stated (kink); corrected `_of_five` / `_of_not_kink` forms PROVED |
| `w3bi_esc_outer_data` | unit OUTER | untouched (black box) |
| `w3bi_bigonData_smooth_arcST_switch_z` / `_arcTS_switch_z` | unit SWITCH-Z | untouched (black boxes) |
| `w3cs_not_kink_site_data` | **this unit, NEW, OPEN** | the non-kink condition at the site, §4 |

Closed by this unit: `w3bi_site_data_data` (β1′).

## 4. The NON-KINK condition (`w3cs_NotKink`, `w3cs_not_kink_site`) — why it is stated and not derived

The assembler needs, for `w3bg_bigonData_smooth_arcST_of_not_kink` at the lift crossing `x_H` (and `x_L`),
`hkink : ⟨(sS D x).1, (sS D x).2 − 1⟩ ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩` (`arcST`) and the `arcTS` twin.  On the
one-component lift both strands are `⟨0, ·⟩`, so the pair of conditions says `{a, b} = {m, p}` are not at cyclic
distance `2` in the corner polygon `X = geoCornerPolygon` (a label-form lemma `⟨0, a−1⟩ ≠ ⟨0, b+1⟩ ↔ a − 1 ≠ b + 1` was
dropped: the binop elaborator does not unify the two `ZMod ((positiveDiagram).Γ.comp _).k` types; use `Sigma.mk.inj` /
`congrArg (singleStrandEquiv A)` at the point of use).

**(a) It does not follow from `w3bi_SiteData`.**  Counterexample (any generic one-component polygon containing
these four consecutive vertices, with `q` a further edge): `X(m−2) = (2, −1)`, `X(m−1) = (1, 1)`, `X(m) = (0, 0)`,
`X(m+1) = (3, 0)`; then `p := m − 2 = [(2,−1),(1,1)]` and `m = [(0,0),(3,0)]` cross at `x = (1.5, 0)` (a kink loop
`x → (1,1) → (0,0) → x` with the single edge `m − 1` between `p` and `m`); take `q` along `(1.5, 1) → (0.5, −1)`
(direction `(−1, −2)`): it crosses `m` at `y = (1, 0)` and `p` at `z = (1.25, 0.5)`, both on the loop sides.  Signs:
`det(dm, dp) = det((3,0),(−1,2)) = 6 > 0`, `det(dm, dq) = det((3,0),(−1,−2)) = −6 < 0`,
`det(dp, dq) = det((−1,2),(−1,−2)) = 4 > 0` — the alternating triple `(+, −, +)`; the triangle `conv{x, y, z}` lies
strictly inside the loop triangle `conv{x, X(m−1), X(m)}`, so edge `m − 1` and all vertices miss it (`clear`,
`clear_vertex` hold), and D4/D5 hold by `w3cs_siteData_of_triangle`.  So `w3bi_SiteData` holds at a kink; the
smoothing of `x` there splits off the `4`-gon `x⁻, m−1-piece, x⁺` + cuts and `BigonData.hk : 5 ≤ k` fails — exactly
unit G's finding.  Hence the condition must come from the 177 configuration, not from the site data.

**(b) At the lift level.**  `m = G11_mE` is the carrier edge (piece of `e`) through `x_ef`, `p = G11_pE` the piece of
`f`.  `p = m − 2` means the corner polygon runs `p → (m−1) → m`: the vertex between `p` and `m − 1` is a `P`-vertex
(`X_P(f+1)`) or a smoothed crossing `c ∈ T` on `f`; the vertex between `m − 1` and `m` is `X_P(e)` or a smoothed
crossing `c' ∈ T` on `e`.  `outsideSupports` excludes from `Q` only the three triangle crossings (Cores.lean:455), so
`c, c'` on `f, e` with far strands are allowed; `IsSimpleRIII`'s `remote e f` (Events.lean:1133) excludes adjacency
of `e, f` in `P` but not distance `2`; `LocalizationData.adjacent` (Cores.lean:622) constrains visit orders on
`e, f, g`, not the label distance.  None of the available hypotheses visibly forbids the four combinations, and I
had no time to look for an argument through the Gauss-word/adjacency data (`w3bi_wall_data_lift`'s
`nextVisit a₁ = a₂ ∨ …`) or through `LocalizationData`'s disc.  Rule (4): stated as a black box, one `sorry`.

**What a proof would need**: either (i) a hypothesis on the event that `e, f` (and `f, e`) are not at label distance
`2` in `P` AND that no `T`-crossing lies on `e` or `f` between `X_P(e)`/`X_P(f+1)` and `x_ef` (then `m = e`, `p = f`
as whole edges and the condition is `e ≠ f ± 2`), or (ii) a corner-polygon lemma: the two carrier edges of a retained
crossing are never at distance `2` unless the polygon has a monogon through that crossing, plus an argument that the
K3-side triangle (with `y, z` on the loop sides by D4) cannot sit in such a monogon — I do not see one; the
counterexample of (a) is a genuine polygon, so (ii) needs data beyond the local triangle.

## 5. Notes for the assembler

* Wire: `w3bi_site_data_data` is now proved; no change of consumers needed (`w3bi_bigon_pair_of` etc. compile as before).
* For unit G's corrected forms: `w3cs_not_kink_arcST D x (h : w3cs_NotKink D x)` / `w3cs_not_kink_arcTS` give the
  `hkink` binders; `w3cs_not_kink_site_data` provides `w3cs_NotKink` at `x_H` and `x_L` under exactly the binder list
  of `w3bi_site_data`.  A consumer that switches at `z₀` (the `switch_z` forms) needs the same two conditions.
* Names introduced (all `w3cs_`): `w3cs_det_lin`, `w3cs_det_self`, `w3cs_det_smul_self`, `w3cs_crossingParam_congr`,
  `w3cs_sub_eq`, `w3cs_pos_overStrand_eq_iff`, `w3cs_opposite_signs`, `w3cs_siteData_of_triangle`, `w3cs_exact_symm`,
  `w3cs_site_data_lift`, `w3cs_triangle_transport`, `w3cs__w3bi_site_data_data_proof`, `w3cs_NotKink`,
  `w3cs_not_kink_arcST`, `w3cs_not_kink_arcTS`, `w3cs_not_kink_site`, `w3cs_not_kink_site_data`.
* Pitfalls met: `set D := Γ.positiveDiagram hΓ` makes later `rw`/`simp` fail ("not type-correct under implicit
  transparency") — use the explicit term; rewriting under `≠` needs `iff_of_true/false` rather than `rw`;
  `Finset.mem_insert` via `simp` fails when the membership is typed at `(positiveDiagram).Γ.Strand` — ascribe the
  `Finset Γ.Strand` type; `w3cs_triangle_transport` must be stated over `CrossingGeometry` (a `CarrierGeometry` is
  not recoverable from its `.cg` by unification).

## 6. Timeline (UTC)

23:19 start, reading (REAL §8, RALedgers, GeoPositiveLift, PieceIntrinsic, LinkDiagram, GenericTransport helpers);
23:33 stage 1 (D-level) compiles; 23:42 stage 2 (lift + assembly) compiles in scratch; 23:45 target compiles, 0
errors; 23:46 axioms / statement check; 23:48 identity check; 23:52 non-kink block + this report; 23:54 final compile: exit 0, 0 errors, `grep -c sorry` = 8, 7 sorry-using
declarations, identity 5/5 IDENTICAL, statements 42/42.
