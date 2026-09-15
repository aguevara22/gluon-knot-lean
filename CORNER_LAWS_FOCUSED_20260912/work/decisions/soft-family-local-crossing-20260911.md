# Actual soft incoming/return crossing wrapper

Authored by /root/review_contraction_candidates, the same currently available model as root. This is implementation, not independent self-review or stronger-model fidelity approval. No Lean kernel/build/audit was run. Root owns checking and independent review; prior frozen and accepted state remains unchanged.

Four declarations implement only the incoming/return pair from lem:soft-generic, source lines 1079-1109 within the full proof read at 1013-1150.

- softIncoming_return_difference: for every n>=3 and actual insertion label j, the enlarged return label minus the mapped incoming label is exactly 2.
- softIncoming_return_remote: the adjacent possibilities force n+1 to divide 3, 2 or 1, respectively, contradicting n+1>=4. Parent arity three and every physical wrap case remain covered.
- softIncoming_return_segment_parameters: the two actual closed edge segments intersect exactly when their local affine equations have parameters in [0,1]. The incoming start/direction follow from old-vertex and old-edge preservation; the return start/direction follow from the new-vertex and return-edge formulas. Both implications preserve the same point and real parameters.
- softFamily_local_crossing: n>=3, parent G1 and actual SoftAdmissible produce one positive radius on which both actual segment intersection and actual unordered IsCrossing are equivalent to the conjunction softAttachmentMinus = turn P j and softAttachmentPlus = turn P j.

The final theorem derives the original direction determinant from g1_turn_nonzero and the attachment determinants from the actual admissibility clauses. It invokes softLocal_small_crossing_sector at P(j), P(j-1), P(j+1), then rewrites the sign conditions through the existing turn and attachment definitions. isCrossing_pair requires only the remoteness proved here. No genericity of the enlarged tuple, independent height-sign premise or unpublished soft-family result is assumed.

This is one local-pair theorem. It does not enumerate all crossings or assert enlarged G1/G2, a generic chamber, global absence of other newborn pairs, unique point limits, or Gauss-word adjacency. The segment-translation helper holds at every real parameter; the crossing conclusion expressly uses every 0<epsilon<delta.

The prototype inherits canonical imports and receipt-bound bodies from SoftInsertionTuple and SoftLocalDeterminants, and explicitly imports SM.Crossings. Bodies are ordered by actual position in their frozen passing prototypes and deduplicated. All seven bodies, including the new one, occur exactly once. The draft-dependency-bindings JSON records source-receipt and full-body hashes; exact first drafts are preserved. There is no dependency on unpublished SoftFamilyG1 or turn-persistence work.

## Artifact hashes

- work/checks/SoftFamilyLocalCrossing.body.lean: 07230f4aad3bd90f97166a7dcb432230d15fe0ac262650f80558e463721ea50b
- work/checks/SoftFamilyLocalCrossing.prototype.lean: 42db9e4d551b933378d6a034388a9fec0f7c0778df15c5c7ba87c9503b984b08
- work/checks/SoftFamilyLocalCrossing-first-draft.body.lean: 07230f4aad3bd90f97166a7dcb432230d15fe0ac262650f80558e463721ea50b
- work/checks/SoftFamilyLocalCrossing-first-draft.prototype.lean: 42db9e4d551b933378d6a034388a9fec0f7c0778df15c5c7ba87c9503b984b08
- work/checks/SoftFamilyLocalCrossing-body-dependencies.json: 142744d873402e793f2f1cfbd2432af89f0d4115087695a054ddbadb2001e416
- work/checks/SoftFamilyLocalCrossing-draft-dependency-bindings.json: ca713c5e7c3552342e9788fd0128b7f78766e6be5ed4f4df988313e1e41a9244

Source reference/SM/sm-2-amplitude.tex: 014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf
