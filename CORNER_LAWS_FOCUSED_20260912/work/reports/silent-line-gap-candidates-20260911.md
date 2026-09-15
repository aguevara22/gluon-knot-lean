# Full silent-line gap lemma checked as a candidate

Checkpoint085 proves SM.silent_line_gap and its determinant-collinearity wrapper
SM.silent_line_gap_of_collinear for source pf:line-gap. For every weak polygon,
fixed root and strictly increasing selected collinear list of at least three
vertices, the proof finds a nontrivial positive gap. When the list includes both
actual root endpoints, it also finds a nontrivial negative gap. Signs use the
printed endpoint ratio, with arbitrary affine orientation. The wrapper derives
coordinates and their injectivity from actual geometry.

Six groups add34 kernel-checked candidate declarations, including helpers:
WeakLineGeometry8 (session98317), FiniteLineGaps3 (15599),
WeakLineSelections9 (98027), LineCoordinateNormalization10 (63737),
WeakSelectedLineCoordinates2 (74872), SilentLineGap2 (23877).
All successful axiom traces use only propext, Classical.choice and Quot.sound.
The exact two failed attempts70739 and10149 are preserved; repairs changed no
theorem types. The verifier passed34 traces,26 evidence files,832 frozen baseline
hashes and327 unchanged canonical modules. All51 quoted hash bindings in four
sealed nonauthor technical reviews were verified; reviews found no defect in
scope. Same-model technical review is not stronger fidelity approval.

These remain candidates pending stronger statement/definition-fidelity review
and controlled canonical integration/checker acceptance. Accepted source proofs
remain19/132 (14.39%), original checklist38/191 (19.90%), expanded checklist
39/192 (20.31%), and final corner targets0/8. No source claim was newly accepted.
Accepted definitions, axioms, declaration map, sources and prior passing
candidates remain unchanged. This is a rooted-tree dependency.

Evidence: checks/SilentLineGap.body.lean, its prototype receipt,
checks/checkpoint-085-verification.json and checkpoints/goal-turn-085-candidates.json.
Next: decisions/formal-cancellation-after-line-gap.md, proving simultaneous
silent-variable cancellation for all inverse coordinates and the full-root
reversed-far output, then cor:polyform. No author question is needed.
