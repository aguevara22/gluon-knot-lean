# Verification on the origin machine — 2026-09-12 (revision 3, after the cold-start test)

Run on the origin machine on this package's final bytes (macOS arm64; elan; Lean
leanprover/lean4:v4.34.0-rc2; Mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0
from the pinned lake-manifest.json). A fresh agent on a bare Debian 12 machine
obtained the same counts through setup.sh (COLD_TEST.md). The recipient's
setup.sh must reproduce them before any new Lean is written.

```sh
cd work/lean && lake build && cd ../..
python3 tools/check_lean.py work/lean
```

| check | result |
|---|---|
| lake build (work/lean) | success, 3,539 jobs (328 project modules) |
| tools/check_lean.py work/lean | passed: 40 mapped declarations, 4271 audited |
| receipt binds the shipped bundle and project bytes | True (38 bundle files, 334 project files) |
| accepted rows | 40; map and review statement hashes equal the fresh audit hashes; review source hashes equal the SM15 files |
| axioms used by mapped declarations | Classical.choice, Quot.sound, propext |
| sorry in work/lean | 0 files |
| stage 1 | not established (expected: 112 claims pending) |

Receipt files under work/checks (shipped in the required archive):

| file | sha256 |
|---|---|
| stage-development.json | 4820e49d8f842684af2f801eb648509db866e1c092b04826e4e7d73a6076dafb |
| declaration-audit.json | 449f20d3e48801a8cb99cfdcf590c53c4bab268858526023265db15227dfc541 |
| lean-check.log | 436aadcc1548c01dbcbbb499549665c07e1476935773eeaee6e0abaf7eec9063 |
