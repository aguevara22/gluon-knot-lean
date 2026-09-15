# Lean setup and acceptance

Work only in the copy initialized by `python3 tools/bootstrap.py`. The exact pins
are Lean `leanprover/lean4:v4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, with a resolved lake-manifest.json.
Use Python 3.10 or newer for the handoff tools.
Install elan from its official release/installer if missing, then in work/lean:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build
```

If dependencies have not yet been cloned, use `lake update` once and record the
resolved manifest; preserve the exact pins. A cache failure can be resolved by
building the pinned sources. The recipient supplies adequate compute. No setup
choice requires the author. Add Mathlib imports as actual modules need them.

From the bundle root, run `python3 tools/check_lean.py work/lean` during development.
It writes declaration hashes and axiom output to work/checks/. Populate the seeded
work/lean/lean-declarations.json with declaration/module names, implementer in
author, independent reviewer, statement_sha256, parameters_reviewed=true,
definition_equivalence_reviewed=true, review_file relative to work/ and status.
For every source row preserve source, line and labels (including clause aliases).

Review files are JSON: id, reviewer, statement_sha256, verdict="faithful", reason,
source_sha256. The latter hashes the supplied source file. Reasons compare the
full source domain/conclusion to the Lean type and definition; clause rows cover
only their specified clause. Extra R/bridge/final rows cite and compare the full
clauses in their reason. Review cannot be self-signed. Type/definition changes
invalidate the hash. A successful axiom audit is not a semantic fidelity review.
Hashes also bind the local helper definitions giving each type its meaning.
Changing an unmapped helper can therefore require renewed review. Keep the
supplied Supplemental/Audit.lean unchanged in the working project.

Finally run `python3 tools/check_lean.py work/lean --stage 1`. In this package that
requires **all** focused rows, including the complete R/bridge/final theorem.
Stages 2 and 3 are deliberately unavailable. No certificate lane is required.
No theorem may use sorryAx, native_decide axioms or any unregistered axiom. The
final theorem must have no extra R/law assumptions; independent parameter review
must check this because #print axioms does not detect explicit proof parameters.
`python3 tools/check_lean.py work/lean --all` is equivalent here. Complete
FINAL_REVIEW.md before delivery. Receipts bind code, reviews, sources and policy.
`python3 tools/selftest_acceptance.py` runs a synthetic complete acceptance cycle
and stale-review controls; it does not formalize the commissioned mathematics.
