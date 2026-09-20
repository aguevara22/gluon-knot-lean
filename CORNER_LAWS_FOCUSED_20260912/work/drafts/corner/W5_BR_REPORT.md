# W5_BR_REPORT.md — unit W5-BR (wave 5, prefix `w5b_`), written by the pod executor at 10:46Z 2026-09-19

**Why the executor wrote this report.** The W5-BR unit agent (workflow wf_7f807cbc-8ff) finished its file and its full compile at
10:37Z, then died on a transient API error (HTTP 500) while running its last `#print axioms` probe, before writing this report. Everything
below is taken from the unit's file `W5_BR.lean`, its compile log and its probe file (`<scratchpad>/w5br/{full.log,log.txt,W5_BR_axioms.lean}`),
re-run by the executor. No content was added or changed by the executor.

## 1. File
- `work/drafts/corner/W5_BR.lean` (1 295 069 bytes) = `W4_Assembled.lean` + ONE inserted block: `diff W4_Assembled.lean W5_BR.lean` =
  `19853a19854,21509` (1 656 lines, 0 deletions), inserted immediately before the docstring of `w4_box_returnedRows`, inside
  `section W4Bigon` (built by the unit's `mkfull.sh`: W4 lines 1-19853 + the `w5b_` block + W4 lines 19854-end).
- Full compile `cd work/lean && lake env lean ../drafts/corner/W5_BR.lean` (unit's full.log, 10:37Z): **0 errors**, 34 s wall; warnings =
  `declaration uses sorry` at 4437, 18053, 18494 (the W4 superseded boxes, untouched), 21035, 21432, 21441, 21458 (this unit's four
  black boxes, §3), 21513 (`w4_box_returnedRows`, untouched), 21578 (`s7_bigon_law_at`, untouched). `grep -c sorry`: 20 (16 in W4 + 4 boxes).

## 2. What the block proves (unit header, W5_BR.lean:19854-19861)
The BRANCH DATA of the returned row — the record fields (`record`, `ne`, `comp₁`, `comp₂`) of `s7k_InterlacingData` /
`s7k_NoninterlacingData` at the actual carriers `q_H = owner μ_M` (high, `P₂(t)`), `q_L` (low, `P₀(t)`), `L₁`, `L₂` (the halves),
PROVED from KL1's record bridge, a generic smoothing/restriction lemma for one-circle Gauss records (Part 0), the κ-sorted split word of
the contact carrier's Gauss list (Part 2, on SPLIT/FB3/B3's arc lemmas) and U110-D's Gauss-record transport (Part 3), modulo ONE black
box consumed from unit W5-RT (`w5b_box_returnedData`); the turn fields and the curl fields are stated as exact `w5b_` Props and left as
black boxes. Section headings inside the block (line offsets within the block):
  - L1 (+19853): /-! ### Unit W5-BR (wave 5, prefix `w5b_`; W4_ASSEMBLY_REPORT §5 W5-BR): the BRANCH DATA of the returned row —
  - L111 (+19853): /-! #### Part 0b — smoothing a one-circle Gauss record at a self-crossing and restricting to one component.
  - L304 (+19853): /-! #### Part 0c — the two successors on a side are `List.next` on the kept list; the record isomorphism. -/
  - L453 (+19853): /-! #### Part 0d — the split word of a Gauss list at a self-crossing gives the two sides. -/
  - L672 (+19853): /-! #### Part 2a — the split of a strictly sorted list at an element and its maximum. -/
  - L790 (+19853): /-! #### Part 2b — on a side polygon `Q` (SPLIT's `s7p_SideData`), the Gauss list of a crossing set `X`
  - L946 (+19853): /-! #### Part 2c — the kept crossings of the two arcs are the images of the half crossing sets. -/
  - L1104 (+19853): /-! #### Part 3a — the wall vocabulary (F's spelling): the lift `T = s7f_lift T₀` of an eligible decomposition
  - L1206 (+19853): /-! #### Part 3b — the half visit maps on `P₂(t)`: same-edge order (RET's `s7r_first/second_order` on the
  - L1347 (+19853): /-! #### Part 3d — the component identifications: with `G := gaussRecord (cg P₂) X_H ≅ (record D_H)`
  - L1474 (+19853): /-! #### Part 5a — the noninterlacing case: the component of the smoothing carrying the `A`-arc side is the
  - L1535 (+19853): /-! #### Part 6 — **W5-BR's deliverables**: the branch data of `s7k_InterlacingData` / `s7k_NoninterlacingData`

**Deliverables (Part 6, sorry-free modulo the boxes of §3):**
- `w5b_interlacingData` (L21475): under `s7f_Interlacing hn h t`, `carrierWeight … q_L ≠ 0`, a diagram `DA` with
  `ι : RecordIso DA.record ((positiveLift … (lift T₀) q_H hT).record.smooth (w5b_v …))`: `∃ i j : Fin DA.Γ.c, s7k_InterlacingData hn (s7f_hP₂ …)
  (s7f_hP₀ …) hT hT₀ q_H q_L … h₁ h₂ hS₁ hS₂ L₁ L₂ (w5b_v …) DA i j`. Proof: `w5b_components_of_interlacing` (record/ne/comp fields, std
  axioms) + `w5b_box_interlacingTurnData` (rotation, pattern₁, pattern₂).
- `w5b_noninterlacingData` (L21492): likewise for `¬ s7f_Interlacing`, `s7k_NoninterlacingData`; proof: `w5b_components_of_not_interlacing`
  + `w5b_box_noninterlacingTurnData` (rotation, patterns) + `w5b_box_curlData` (value, writhe).
- Supporting PROVED lemmas (all on the standard axioms only, executor's re-run of the unit's probe): `w5b_GaussSide.recordIso_gauss`,
  `w5b_GaussSplit.gauss_iso_A`, `w5b_GaussSplit.comp_ne`, `w5b_sorted_split`, `w5b_exists_gaussSplit`, `w5b_keptFinset_A_eq`,
  `w5b_keptFinset_B_eq_of_interlacing`, `w5b_gaussIso₁`, `w5b_gaussIso₂`, `w5b_v_fst`, `w5b_components_of_interlacing`,
  `w5b_components_of_not_interlacing`. Structures: `w5b_GaussSide` (L20012), `w5b_GaussSplit` (L20312), `w5b_ReturnedData` (L21020),
  `w5b_InterlacingTurnData` (L21404), `w5b_NoninterlacingTurnData` (L21414), `w5b_CurlData` (L21448).

## 3. Black boxes left by this unit (rule (3): stated exactly as consumed; each carries sorryAx)
1. `w5b_box_returnedData (hE : T₀ ∈ w4_EligDec hn g h t) : w5b_ReturnedData hn g h h₁ h₂ t T₀` (L21035) — CONSUMED FROM W5-RT: the
   returned-transport data at an eligible decomposition below the radius of `s7a2_exists_intervalLocal`. W5-RT delivered
   `w5t_returnedTransport_of` / `w5t_ReturnedTransport` (W5_RT_REPORT.md); the assembler must check that `w5b_ReturnedData` (L21020) is
   discharged by it (field-by-field) — this is the intended identification, not a new Prop.
2. `w5b_box_interlacingTurnData (hI : s7f_Interlacing hn h t) (hW : carrierWeight … q_L ≠ 0) : w5b_InterlacingTurnData …` (L21432) — the turn
   fields (rotation, pattern₁, pattern₂) of the interlacing branch: sm-4's rotation/pattern bookkeeping on the corner correspondence of
   `q_H` with `L₁ ⊔ L₂` (U110-I `s7i_interlacing_absolute` on A2's centre polygon `L*`, `rot L* = rot q_H = rot q_L`). OPEN (geometric).
3. `w5b_box_noninterlacingTurnData (hI : ¬ s7f_Interlacing hn h t) (hW : …) : w5b_NoninterlacingTurnData …` (L21441) — the turn fields of
   the noninterlacing branch: one-dissent half patterns under `wt(q_L) ≠ 0` (sm-4:742-757; `s7c_dissent_halves_of_noninterlacing`,
   `s7i_noninterlacing_absolute`). OPEN (geometric).
4. `w5b_box_curlData (DA : Diagram) (i : Fin DA.Γ.c) (hrec : Nonempty (RecordIso (DA.knotRestrict i).record …)) : w5b_CurlData DA i` (L21458) —
   the curl fields (value, writhe) of the noninterlacing branch: `cb_products … .product` on the carrier of `T ∪ {x}` through `μ_M` (self-
   crossings `ι₁ X_{L₁} ∪ {y}`) against the blocks of `L₁`; the writhe by counting the crossings of the record. OPEN.

Axiom footprint of the deliverables (executor's re-run, 10:47Z): `w5b_interlacingData`: [propext, sorryAx, Classical.choice, Quot.sound];
`w5b_noninterlacingData`: [propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm]; `w5b_box_returnedData`: [std, sorryAx].
Boxes 2-4 are the ONLY sorryAx sources on the path of the two deliverables besides box 1.

## 4. Consequence for the assembler
B2' (`w4_box_returnedRows`) is NOT closed by wave 5 alone: with SITE (row data), ROW (B2' composition modulo boxes), RT (returned
transport, closes box 1 by identification) and BR (record fields), the remaining sorryAx sources under B2' are BR's boxes 2-4 (turn
fields ×2, curl fields) plus whatever ROW's composition still names. Expected assembler output: `W5_Assembled.lean` with the exact
list of remaining boxes and a wave-6 specification for them (the turn-field boxes are U110-I / dissent bookkeeping; the curl box is
cb_products on a one-newborn carrier).
