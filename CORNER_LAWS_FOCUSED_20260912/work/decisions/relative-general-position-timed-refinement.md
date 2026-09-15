# Actual timed coordinate approximation — checkpoint056

Source: reference/SM/sm-1-polygons.tex1385–1558. The actual curve/cube construction
is in the audited library. All subsequent timed path, collar, germ, graph and
strong event-certificate bodies are frozen, kernel checked and independently
reviewed external prototypes. See checkpoints/goal-turn-056.json for exact evidence.

Port exact bodies into new modules TimedCoordinatePolyline,
MultiCellCoordinatePolyline, GlobalTimedCollars, GlobalTimedGerms,
SmoothControlGraph and GlobalEventCertificate. Keep the entire multi-cell body
together to preserve proof text. Imports may change; definitions/proofs may not.
Preserve all273 prior SM files. Build, obtain independent exact port-binding
review and run whole audit057 before treating them as audited library results.

The global path has N*(2n) fine time cells. Quotient and remainder retain the
coarse cell and coordinate labels; the actual local parameter is N*(2n)*t-k.
Fine-cell inclusion, join compatibility, labelled endpoints, synchronous true
Euclidean error, regularity, collision freedom and finite nongeneric times are
proved. First/last coarse cells give positive-width Generic collars. Each actual
nongeneric time has strict interior local time and a rescaled actual WallGerm.
The stronger TimedEventCertificate exposes its exact fine cell, named root,
local/global path identities, nonzero derivative and same-point ambient C-infinity
graph. An explicit open smooth graph with smooth projection inverse supplies the
source hypersurface meaning. No separate manifold API is needed for that meaning.

Remaining: classify a sole point-control zero by actual cyclic adjacency and
regular betweenness into F, V-bigon, V-sliding, E or C; exclude the n=3 collinear
regular triangle. A sole concurrence-control zero is a wall only at a genuinely
nongeneric time. Derive its unique active remote interior concurrence and the
three crossing-order sign changes from the exact T/determinant/parameter identity.
Do not use uniqueness for already-simple germs to infer these existence clauses.
Derive needed other-control local persistence from central nonvanishing and
continuity or expose the existing stronger patch result in a new theorem.
Regularity excludes cusp. Assemble all source clauses and independently review
before accepting thm:relgp. All corner laws, soft theorem and unconditional R remain
required. No original proof increment arises from these partial constructions.
