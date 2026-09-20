# R176W2_MIXED_REPORT — row 176 (R:extreme_transport), the MIXED unit: `r176_mixed_bridge` PROVED

MIXED prover (subagent), 2026-09-15 22:34–23:06 UTC / 6:34–7:06pm ET.  File:
`work/drafts/moves/R176W2_MIXED.lean` = `R176_Port_draft.lean` (6339 lines, byte-identical, `cmp`-checked) + the
`r176m_` appendix (496 lines, 24 declarations, all prefixed; nothing above the appendix touched).  Compile command:
`cd work/lean && lake env lean ../drafts/moves/R176W2_MIXED.lean`.  Nothing under `work/lean` written; no `lake build`.

## 0. Result and checks

**`r176_mixed_bridge` is TRUE as stated and PROVED**: `theorem r176m_mixed_bridge_proof : r176_mixed_bridge`, on the
standard axioms only (`propext, Classical.choice, Quot.sound`).  The frozen Prop was not edited; the composition needs
NO change.  Bonus: `r176m_extreme_transport_of_curl_outer (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L) :
RowShape @ExtremeTransportData` — the row now hangs on exactly two open Props (#1 and #2 of R176_ASSEMBLY_REPORT §5).

| item | result |
|---|---|
| compile | **exit 0, 0 errors**, ~45 s; **no warning from the appendix** (the draft's own two harmless warnings only) |
| `grep -c sorry` | before **1**, after **1** — the single hit is the word "sorry" in the frozen header COMMENT (line 1: "33 `sorry` leaves"); there is no `sorry` term in the file, before or after |
| `#print axioms r176m_mixed_bridge_proof` (scratch copy) | `propext, Classical.choice, Quot.sound` |
| `#print axioms r176m_extreme_transport_of_curl_outer` | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact` (= those of `r176_extreme_transport_of_curl_outer_mixed`, the six registered literature axioms), no `sorryAx` |
| frozen material | every declaration above the appendix unchanged (`head -6339` `cmp`-identical to `R176_Port_draft.lean`); the appendix is a closed `namespace RProof … end RProof` block, so the file's final `end RProof` is the appendix's |
| estimate vs actual | estimated 400–700 lines; actual 496 (incl. ~60 lines of docstrings/section headers) |

## 1. The route: a COUNT, not a bijection with `r176l_mixedSet`

The task sketch (bijection of the mixed crossings of `D_A` with `r176l_mixedSet` through `r176s_smooth_comp_eq_pair_iff`
/ `_self_iff` and `KA_eq / KB_eq`) has one gap: `r176_OuterDataL` fixes the kink `r` only by `KB_eq`
(`K_B = liftBlock Λ₁ ∪ {r}`), `r_not`, `r_curl` — it does **not** say which parent crossing labels `r` (morally the lift
of the other selected local crossing `v'`).  A crossing-by-crossing identification "mixed in `D_A` ⇔ label in
`r176l_mixedSet`" would need `liftLabel r ∈ Sf`, which the outer data does not carry; rule (2) would have forced a new
`r176m` Prop for it.  The count needs nothing of the kind:

```
#crossings(D_A) = #chords(ρ) − 1                       (κ : crossings of D_A ≃ chords ≠ {v₀, τ v₀})
               = #K_A + #K_B + #mixed(D_A)             (a crossing of D_A is self-j, self-i or mixed)
#K_A = #Λ₂-retained,  #K_B = #Λ₁-retained + 1          (KA_eq, KB_eq, r_not; liftLabel bijective on liftBlock)
#chords(ρ) = #retained q₀'                             (liftLabel bijective)
           = #Λ₁ + #Λ₂ + #mixedSet + 2                 (r176l_card_retained + r176l_selectedPart_card)
⇒  mixedSignSum D_A i j = #mixed(D_A) = #mixedSet.
```
`mixedSignSum = #mixed` is `r176l_mixedSignSum_eq_card` with all signs `+1` (`geoPositiveLift_sign` transported through
`r176s_DA_iso.sgn_eq`, `Record.smooth_sgn`).  So the bridge holds for ANY `r` satisfying `KB_eq / r_not` — `r_curl` and
`_hy` are not used.

## 2. The appendix (`r176m_`, 24 declarations)

| § | declaration | content |
|---|---|---|
| M1 | `r176m_crossingOf_not_mem_KA/_KB` | `{x, τ x} ∉ K_A`, `∉ K_B` (`r176s_arcA_ne_self`) |
| M1 | `r176m_KA_KB_disjoint` | a chord in both would put the two smoothing components together (`smooth_comps_ne_of_self`) |
| M1 | `r176m_card_rest` | `#{c ≠ {x,τx}, ∉ K_A, ∉ K_B} + #K_A + #K_B + 1 = #ρ.Crossing` (indicator sum, pointwise `= 1`) |
| M2 | `r176m_κ` | `w ↦ crossingOf (ι.Φ (overVisit w)).1`, the chord of `D` under a crossing of `D_A` |
| M2 | `r176m_comp_eq_j_iff / _i_iff` | the component of an occurrence of `D_A` is `j` (resp. `i`) iff its lift lies on `A` (resp. `B`): `r176s_smooth_comp_eq_pair_iff / _self_iff` + `ι.comp_eq` + `Equiv.eq_symm_apply` |
| M2 | `r176m_comp_i_or_j` | two components (`r176s_DA_componentCount`, `omega` on `Fin` values) |
| M2 | `r176m_Φ_underVisit` | `ι.Φ (underVisit w) = (ρ.smooth v).pair (ι.Φ (overVisit w))` |
| M2 | **`r176m_isMixed_iff`** | `r176l_IsMixed D_A i j w ↔ κ w ∉ K_A ∧ κ w ∉ K_B` (`r176s_crossKeep_KA_iff / _KB_iff`, four-case split) |
| M2 | `r176m_κ_ne`, `r176m_κ_injective`, `r176m_κ_surj` | `κ` is a bijection onto the chords `≠ {v, τ v}` |
| M2 | `r176m_card_mixed_eq` | `#mixed(D_A) = #{c ≠ {v,τv}, ∉ K_A, ∉ K_B}` (`Finset.card_bij κ`) |
| M2 | `r176m_DA_sign` | `D_A` keeps the signs (`ι.sgn_eq`, `smooth_sgn`) |
| M2 | `r176m_mixedSignSum_eq` | `mixedSignSum D_A i j = #{…}` on a positive `D` (`r176l_mixedSignSum_eq_card`) |
| M3 | `r176m_card_filter_of_inj`, `r176m_card_of_bij` | ABSTRACT Finset counts for an injection `f : α → β` (see §5, the whnf gotcha) |
| M3 | `r176m_mem_liftBlock` | `p ∈ liftBlock W ↔ liftLabel p ∈ W` |
| M3 | `r176m_card_liftBlock`, `r176m_card_record_crossing` | `#(liftBlock W) = #W` for `W ⊆ retained`; `#chords = #retained` (`liftLabel_injective`, `liftLabel_mem`, `exists_liftLabel_eq`) |
| M3 | **`r176m_bridge_count`** | on `geoPositiveLift q` with `KA_eq / KB_eq / r_not` and `W₁ W₂ ⊆ retained`: `mixedSignSum + #W₁ + #W₂ + 2 = #retained q` (generic: no event binders) |
| M4 | **`r176m_mixed_bridge_proof : r176_mixed_bridge`** | the event level: the case-1 successor facts derived exactly as in `r176l_portDataRest_case1` (`hXL, hT, hjT, hρa, hlt_b, hρb, hnb_c`), `hSf` from the binder `_hSf`, `r176l_lt_c_of_indep` → `hρc`, `r176l_children_case1`, `r176l_card_retained`, `r176l_selectedPart_card`; `r176m_bridge_count` at `hG := r176s_cgL hn ht'`, `W₁ := retained Λ₁`, `W₂ := retained Λ₂` with `O.subB, O.subA, O.r, O.KA_eq, O.KB_eq, O.r_not`; `linarith` |
| M5 | `r176m_extreme_transport_of_curl_outer` | `r176_extreme_transport_of_curl_outer_mixed hcurl hout r176m_mixed_bridge_proof` |

Fields of `r176_OuterDataL` consumed: `v₀ hv₀ subA subB KA_eq r KB_eq r_not`.  NOT needed: `r_curl`; of the binders,
`_hy`, `_hcomp`, `_hu _hv _hju _hjv _huv` are unused (`_habc` IS used, for `hXL`; `_hlt_a`, `_hSf` are used).

## 3. What the composition needs changed

Nothing.  `r176_mixed_bridge` is proved as frozen.  `RProof.extreme_transport` is now
`r176m_extreme_transport_of_curl_outer <curl> <outer>` once #1 (`r176s_curl_removal`) and #2 (`r176_outer_carriers_L`)
are proved.  No defect found in any frozen statement met (`r176l_mixedSet`, `r176l_Children`, `r176l_card_retained`,
`r176s_DA_*`, `r176s_smooth_comp_eq_*`, `r176_OuterDataL`).

## 4. Black boxes

* `r176_outer_carriers_L` — untouched, not asserted; its DATA `r176_OuterDataL` consumed as the hypothesis `O` of the
  frozen Prop.  No new fact about the outer carriers was needed (no new `r176m` Prop, no `sorry`).
* `r176s_curl_removal` — untouched.
* Everything else consumed is a proved theorem of the draft or the library.

## 5. Port notes

* §M1–§M2 are GENERAL record/diagram lemmas (any one-component `D`, any self-crossing occurrence `v`): the bijection
  `κ` of the crossings of the library smoothing with the chords off `{v, τ v}`, the mixed ↔ "off `K_A ∪ K_B`"
  characterisation, sign preservation.  Destination: next to `r176s_smoothRestrictIso` (SM/Smoothing.lean neighbourhood
  / `SM/LinkRecordExtras.lean`).
* §M3 `r176m_card_liftBlock`, `r176m_card_record_crossing`, `r176m_mem_liftBlock` → `CV/GroupedKnot.lean` (section
  LiftLabel).  `r176m_card_filter_of_inj`, `r176m_card_of_bij` are Mathlib-style helpers (`Finset.card_bij` wrappers).
* **whnf gotcha (cost ~10 min):** on `(geoPositiveLift hn hG hT q).record.Crossing`, any `exact`/`show`/anonymous
  constructor whose defeq check crosses `Set`-membership in `liftBlock` vs `Finset`-membership of the label, or
  re-unifies a `Fintype`/`Finset.univ` instance, hits `(deterministic) timeout at whnf` (Lean unfolds
  `geoPositiveLift`).  `Finset.univ.filter` itself and instance synthesis are fine.  Cure used here: rewrite with the
  membership lemma `r176m_mem_liftBlock` under `Finset.filter_congr`, then apply the ABSTRACT counting lemma to
  `CV.liftLabel`; for set equations (`hKA`, `hKB`) rewrite by `ext` + `simp only [Finset.mem_filter, …, hKB,
  Set.mem_union, Set.mem_singleton_iff]` rather than `rw` on the whole filter (the `Set.decidableUnion` instance
  differs from the classical one).  The same care is advisable for the #2 prover.
* A second elaboration gotcha: `(ρ.smooth v).M` vs `{w // ρ.SmoothKeep v w}` — build equalities as terms
  (`Subtype.ext h`, `obtain ⟨m, hm⟩ : ∃ m, ι.Φ m = (⟨c.rep, hkeep⟩ : (ρ.smooth v).M)`) rather than `rw
  [Equiv.apply_symm_apply]`, whose motive fails on the mismatch.
* Deprecations met in this Mathlib: `if_neg/if_pos` → `ite_eq_right/ite_eq_left`; `Set.mem_setOf_eq` →
  `Set.mem_ofPred_eq` (the appendix already uses the new names; no warnings).

## 6. Files

* `work/drafts/moves/R176W2_MIXED.lean` — the deliverable (6835 lines = 6339 draft + 496 appendix).
* `work/drafts/moves/R176W2_MIXED_REPORT.md` — this report.
* Scratch (session scratchpad, not deliverables): `appendix.lean`, `test.lean`, `diag*.lean`, `final_ax.lean`
  (`#print axioms` copy).
