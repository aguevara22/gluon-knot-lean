# G11_U5_REPORT — unit U5 (D5–D7: clean, move match, arc covers)

File: `work/drafts/rlane2/G11_U5.lean` (2392 lines; the skeleton is 1086 lines, +1289 lines of `gu5_*` helpers
inserted immediately before the `/-- **D5.**` docstring, +4 leaf bodies). Compile
(`cd work/lean && lake env lean ../drafts/rlane2/G11_U5.lean`): **exit 0, 0 errors, 45 × `declaration uses sorry`
(= 49 − 4), no other warning.** `grep -c sorry`: 50 before (49 leaves + 1 docstring mention) → 46 after.
`diff G11_Skeleton.lean G11_U5.lean` removes exactly the four `sorry` bodies; no statement, definition, name or
docstring was touched. Nothing under `work/lean` was written.

## Leaves proved (4 of 4)

| leaf | body | what it is |
|---|---|---|
| `clean_M₀` | `gu5_clean π π.X₀_generic (gu5_side₀ π)` | `Clean π.U π.M₀` |
| `clean_M₁` | `gu5_clean π π.X₁_generic (gu5_side₁ π)` | `Clean π.U π.M₁` |
| `exists_moveMatch` | `⟨gu5_moveMatch π⟩` | `Nonempty (MoveMatch π.U π.M₀ π.M₁)` |
| `exists_arcCovers` | arcs `gu5_arcE … π.p'`, `gu5_arcE … π.q'`, `gu5_arcM …` on both sides, `gu5_arcCover` | the three arcs, disjoint, covering, same six ends |

Leaves left: none in this unit. (`G11_two_crossings_absurd` untouched, as instructed.)

## Black boxes used (statements only)

U3: `X₀_generic`, `X₁_generic` (only through `M₀`, `M₁` and `edge_ne_zero`), `disc_isDisc` (convex + compact ⇒ closed),
`triangle_sub_interior` (the three double points are in `interior U`). **Not used:** `X₀_cross_*`, `inner_M₀`,
`inner_M₁`, `X₁_cross_*`, `X₁_sign_*` — the clean/match/arc facts follow from the configuration alone
(`disc_clear_edge`, `disc_clear_vertex`, `theta_sub`, `C.gen`, `C.hmp/hmq/hpq`).

## Route actually taken (differences from the plan sketch)

* **One generic side.** `structure gu5_Side π Y : Prop` (fields `eq`: edges `≠ mB, mC` of `Y` agree with `X₀`;
  `segB`, `segC`: the edges `mB`, `mC` of `Y` lie in `interior U`) is proved for `X₀` (`gu5_side₀`) and `X₁`
  (`gu5_side₁`, via `Function.update_of_ne`, and `[p_in, w] ∪ [w, p_out] ⊆ Θ = conv{p_in, w, p_out} ⊆ interior U`
  from `theta_sub`). `gu5_clean`, `gu5_arcCover`, `gu5_isArc_*` are proved once for any side.
* **Clean without `inner_M₀/M₁`.** A frontier point lies on `mA, mD, p'` or `q'` (`gu5_Side.frontier_label`:
  `mB, mC` points are interior, other labels are foreign edges of `X`, excluded by `disc_clear_edge`); two such points
  with one plane point are on the same strand (then `edgePoint_injective`) or on two of `m, p, q`, whose common
  point is the double point (`gu5_common_point`, from `C.gen.common_point_unique` + `single_crossingPoint`), which is in
  `Δ ⊆ interior U` — not on the frontier. `exits`: the traversal point `(mA, 0)` evaluates to `X m ∉ U`.
* **Entry/exit parameters by `sInf`, not by IVT.** `gu5_entry`/`gu5_exit`: along `t ↦ A + t•v` with
  `f s₀ ∉ U`, `f s₁ ∈ interior U`, the parameter `a := sInf {t ∈ [s₀,s₁] | f t ∈ U}` satisfies
  `f t ∈ U ↔ a ≤ t`, `f t ∈ interior U ↔ a < t` on `[s₀,s₁]` (`IsClosed.csInf_mem`,
  `Convex.combo_interior_closure_mem_interior`, openness of the preimage of `interior U`). `gu5_both` combines the
  two for an edge with both endpoints outside (`disc_clear_vertex`) and an interior point (`x_pq`), giving the
  parameter interval `[a, b]`, `0 < a < b < 1`, of `p` and of `q` inside `U` (`gu5_exists_p/q`);
  `gu5_exists_A/D` give the entry parameter on `mA` (`X m ∉ U`, `p_in ∈ interior U`) and the exit parameter on `mD`.
  This is the general "segment ∩ convex body is an interval with frontier ends" fact the plan asked for; no
  barycentric coordinates were needed.
* **The move match is literally the identity.** `M₀.Γ.Pt`, `M₀.Γ.Strand`, `Finset M₀.Γ.Strand` are definitionally
  the `M₁` versions (both `single ⟨k+3, _, ·⟩`), so `gu5_φ := Equiv.subtypeEquiv (Equiv.refl _) gu5_outside_iff`
  and `gu5_ψ` keeps the strand pair (`gu5_ψ_to/inv`, `left_inv/right_inv := Subtype.ext (Subtype.ext rfl)`).
  Over/under strands agree by uniqueness of the positive strand (`positiveDiagram_det_pos` + `det_swap`,
  `gu5_overStrand_eq`), crossing parameters by `edgePoint_injective` (`gu5_crossingParam_eq`), the traversal
  points by `Shadow.mk_eq_mk_iff` + `Diagram.crossingParam_congr` (`gu5_over_eq`, `gu5_under_eq`).
  `dir_pos_before`: at a vertex `(j, 0)` strictly outside `U`, `j ∉ {mB, mC, mD}` (`X₀ mD = p_out ∈ Θ`), so the arriving
  edge `j − 1 ∉ {mB, mC}`. `e := Equiv.refl _`, `comp_eq := fun _ => rfl`.
* **Arcs.** `gu5_ArcParams π` bundles the six parameters `ap < bp`, `aq < bq`, `aA`, `bD` with their `U`/`interior U`
  characterizations (`gu5_exists_arcParams`). Arcs: `gu5_arcE π Y j ha hab hb := ⟨0, (j, a), (j, b)⟩` (used with
  `j = p'`, `j = q'`) and `gu5_arcM π Y … := ⟨0, (mA, aA), (mD, bD)⟩`, **identical data on both sides**, so the six end
  equalities are `gu5_edgePoint_X₁` (unmoved edges). Membership characterizations: `gu5_arcE_mem_iff`/`inner_iff`
  (`j' = j ∧ a ≤ θ ≤ b`), `gu5_arcM_mem_iff`/`inner_iff` (`(j = mA ∧ aA ≤ θ) ∨ j = mB ∨ j = mC ∨ (j = mD ∧ θ ≤ bD)`),
  via the new span-three betweenness lemma `gu5_between_m` (modelled on `Smoothing.traversalBetween_span_two`).

## For the assembler / unit U6 (`riii`)

`exists_arcCovers` is existential, so U6 cannot see which arcs were chosen. The concrete data are public helpers of
this file and should be used directly when the units are merged:
* the arcs `gu5_arcE π π.X₀ π.p' A.hp0.le A.hp A.hp1`, `… π.q' A.hq0.le A.hq A.hq1`,
  `gu5_arcM π π.X₀ A.hA0.le A.hA1 A.hD0.le A.hD1` (and the same with `π.X₁`) for any `A : gu5_ArcParams π`
  (`gu5_exists_arcParams π : Nonempty _`); their `IsArc` (`gu5_isArc_arcP/Q/M`), `ArcCover` (`gu5_arcCover`),
  `Mem`/`Inner` characterizations (above) — these give `OverOn`/`UnderOn` at once: e.g. `OverOn (arc p') x` ↔ the over
  visit of `x` is on `p'` with parameter in `[A.ap, A.bp]`, which for `x_mp, x_pq, x_mp'` follows from
  `A.Up` + the crossing point being in `interior U` (`gu5_xmp_mem`, `gu5_xpq_mem`, `inner_M₁`).
* `BeforeOn` along `p'`/`q'` reduces (via `gu5_arcE_inner_iff`, `traversalBetween_same_edge`) to comparing the
  crossing parameters on `p`; along the `m`-arc (`gu5_arcM_inner_iff`, `gu5_between_m`) to the label order
  `mB < mC` (`gu5_mB_val`, `gu5_mC_val`).
* the move match is `gu5_moveMatch π : MoveMatch π.U π.M₀ π.M₁` (a `def`, not just `Nonempty`), with
  `gu5_φ_val : (gu5_φ π p).1 = p.1` and `gu5_ψ_val : (gu5_ψ π x).1.val = x.1.val` both `rfl`.
* label/vertex arithmetic of `X₀` that every geometric unit needs and each is presumably re-deriving:
  `gu5_mA_val … gu5_mD_val` (`= m.val, m.val+1, +2, +3`), `gu5_X₀_mA/mB/mC/mD/mD_succ`, `gu5_X₀_lab`,
  `gu5_X₀_lab_succ`, `gu5_edgePoint_lab`, `gu5_edgeSegment_lab` (`edgeSegment X₀ (G11_lab m i) = edgeSegment X i`),
  `gu5_label_cases` (every label of `X₀` is `mA, mB, mC, mD` or `G11_lab m i`, `i ≠ m`), `gu5_lab_ne`, `gu5_lab_inj`,
  `gu5_edgePoint_mA/mB/mC/mD` (the pieces as re-parametrizations of `edgePoint X m`), `gu5_edgePoint_X₁`,
  `gu5_edge_X₁`, `gu5_edgeSegment_X₁` (edges `≠ mB, mC` of `X₁` are those of `X₀`), `gu5_X₁_mB/mC/mD`.
  The assembler may want to dedupe these against the U3/U4 files.

## Pitfalls met (Lean / Mathlib, this pin)

* `if_pos`/`if_neg` are deprecated → `ite_eq_left`/`ite_eq_right`; `Set.mem_setOf_eq` deprecated (avoid; use
  `rintro`/anonymous constructors on set-builder membership); `div_add_div_same` does not exist here (used
  `field_simp; ring`).
* `Shadow.single_pt_ext` (CChamber.lean) is **not** in the import closure of `RProof.X1Rows3`; re-proved as
  `gu5_pt_ext` (general `C' : PolyComp`).
* Numerals `(0 : Fin π.M₀.Γ.c)` do not elaborate (`M₀` is a non-reducible `def`): always write `(0 : Fin 1)` and
  `Subsingleton.elim (α := Fin 1) i (0 : Fin 1)`. After `rintro ⟨i, j, θ⟩` on a `Pt` of `M₀.Γ`, `j : ZMod (M₀.Γ.comp i).k`;
  a binop like `j - 1` with expected type `ZMod (k+3)` fails (heterogeneous `HSub`) — build `⟨i, j - 1⟩` as a strand
  and `change j - 1 = π.mB at e` instead, and close `j = j - 1 + 1` with `exact (sub_add_cancel j 1).symm`
  (`rw [sub_add_cancel]` fails: motive not type-correct at reducible transparency).
* `rw` with a lemma whose LHS mentions `crossingPoint ⟨x.1.val, _⟩` fails on `Crossing` (a `def` hiding the subtype);
  use `(congrArg (fun z : Plane => z ∉ interior π.U) h).mpr` instead.
* Dot notation on a structure lemma whose first explicit argument is the section variable `π` (e.g.
  `hS.mem_label`) puts the object at `hS` and then still expects `π`; wrap those lemmas in
  `section variable {π} … end`.
* `Equiv.refl _ : π.M₀.Γ.Pt ≃ π.M₁.Γ.Pt` typechecks (defeq shadows); `Equiv.subtypeEquiv (Equiv.refl _) h` gives the
  identity outside match directly.
* `module` closes the edge re-parametrization identities only if **both** `edgePoint` and `edge` are unfolded on
  both sides (`unfold edgePoint edge` twice, after rewriting the vertices).

## Truth / hypotheses

Every leaf is true as stated and proved; no missing hypothesis, no counterexample. The only smallness facts used are the
ones in `G11_Params` (`theta_sub`, `disc_clear_edge`, `disc_clear_vertex`) plus `triangle_sub_interior` and
`disc_isDisc` from U3.
