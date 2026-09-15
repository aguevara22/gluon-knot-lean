#!/bin/bash
# Assemble work/drafts/rlane/RLaneCores_Assembled.lean from the fixed statement file and the
# delivered units, by exact line ranges (hunks re-derived from `diff RLaneCores_statement.lean U_*.lean`).
set -euo pipefail
cd /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts
S=RLaneCores_statement.lean
OUT=rlane/RLaneCores_Assembled.lean
{
  sed -n '1p' $S                              # import Bridge.B3
  echo 'import CV.TripleEvents'               # U_L line 2 (needed by unit L)
  sed -n '2,6p' $S                            # remaining imports + blank
  cat <<'HDR'
/-! **RProof.Cores — assembled (2026-09-14).** The fixed statement file `RLaneCores_statement.lean`
(bundles and the four row theorems byte-identical) with the delivered proof-lane units spliced in:
unit L (`RProof.L`, proof of `localization`), unit P1 (`RProof.P1`, `ParityData` from
`LocalizationData`), unit F1 (proof of the engine `indep_partition` and `RProof.F1`, the fibre
partition), units G1+G2 (`RProof.G1`, `RProof.G2`, the sign classification and the local table). The
four row theorems are closed from `localization` via `P1.parityData`, `F1.fibre_partition_of_rows`,
`G2.generic_table_of_parity`. No `sorry`. Intended home: `work/lean/RProof/Cores.lean`. -/

HDR
  sed -n '7,119p' $S                          # up to indep_partition ':= by'
  sed -n '127,191p' rlane/U_F1.lean           # engine proof (replaces stmt line 120 'sorry')
  sed -n '121,620p' $S
  sed -n '622,951p' rlane/U_L.lean            # unit L block (after stmt line 620)
  sed -n '621,629p' $S                        # localization docstring + statement
  sed -n '961,979p' rlane/U_L.lean            # localization proof (replaces stmt line 630 'sorry')
  sed -n '631,721p' $S
  sed -n '722,1394p' rlane/U_P1.lean          # unit P1 block (after stmt line 721)
  sed -n '722,729p' $S                        # parity docstring + statement
  cat <<'CLOSE'
  -- Assembly: the radius of row 164 carries `ParityData` (unit P1).
  obtain ⟨δ, h1, h2, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  exact ⟨δ, h1, h2, P1.parityData hL⟩
CLOSE
  sed -n '731,823p' $S
  sed -n '895,1226p' rlane/U_F1.lean          # unit F1 block (after stmt line 823)
  sed -n '824,832p' $S                        # fibre_partition docstring + statement
  cat <<'CLOSE'
  -- Assembly: rows 164 and 167 at the common radius (unit F1).
  exact F1.fibre_partition_of_rows (localization E e f g h3 h4e h4f h4g hE)
    (parity E e f g h3 h4e h4f h4g hE)
CLOSE
  sed -n '834,1061p' $S
  sed -n '1062,2607p' rlane/U_G2.lean         # units G1 + G2 block (after stmt line 1061)
  echo                                        # blank line after `end G2` (cosmetic)
  sed -n '1062,1070p' $S                      # generic_table docstring + statement
  cat <<'CLOSE'
  -- Assembly: the good radius of unit G1 and the parity radius (unit G2).
  exact G2.generic_table_of_parity hE (parity E e f g h3 h4e h4f h4g hE)
CLOSE
  sed -n '1072,1073p' $S
} > $OUT
wc -l $OUT
