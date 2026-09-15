You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma against ONE printed source statement.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source statement, verbatim (frame SM15):
   work/reviews/lem-soft-generic-source-excerpt-lines-1017-1052.tex.txt
   = reference/SM/sm-2-amplitude.tex lines 1017-1052 (lem:soft-generic, clauses (i)-(iv)). For
   notation read reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex (def:polygon,
   def:chirotope (turns), def:generic (G1, G2, 𝒰_n), def:crossings (X(P), crossing points and
   parameters, visits), def:chamber (chambers, labelled chambers), def:gauss (Gauss word, visits,
   cyclic adjacency), def:interlace), reference/SM/sm-2-amplitude.tex lines 996-1015 (def:soft, the
   ACCEPTED-pending definition this lemma builds on) and the proof of lem:soft-generic at lines
   1053-1156 only to disambiguate notation.
2. The Lean statement with its proof replaced by `sorry`:
   work/reviews/lem-soft-generic-reviewer-input-statement.lean.txt (main declaration
   `SM.soft_family_generic`; its docstring maps the source notation to Lean names — verify it, do
   not trust it).
3. The Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are
   not under review): SoftInsertionTuple, SoftInsertionIndices, SoftInsertionSuccessors,
   SoftParentEdges (softParentEdge), SoftCrossingTransport (SoftCrossingPersistence,
   softInheritedCrossing, softInheritedVisit), SoftCrossingClassification
   (SoftCrossingClassificationAt), SoftNewbornVisits / SoftNewbornVertexArc / SoftInheritedCrossingData
   / SoftGaussGeometry (softNewbornCrossing, softNewbornIncomingVisit, softNewbornReturnVisit,
   softNewbornPoint, softNewbornIncomingParameter, softNewbornReturnParameter, softInheritedPoint,
   softAttachmentVertexPosition, softInsertedVertexPosition), Crossings, CrossingEquiv,
   CrossingParameters / EdgeParameters (edgeParameter, crossingPoint, visitParameter, pairVisit,
   Visit), Traversal (traversalEvaluation, traversalBetween, visitPosition), GaussDefinition /
   GaussWord / GaussCycle (gaussWord, gaussCycle, nextGaussVisit), Chambers, CyclicChambers
   (labelledChamber, chamber, polygonProjection, GenericTuple), Polygon, Chirotope, Generic, Segment.
   Follow any further definition you need (grep work/lean/SM for `def <name>`).
   Do NOT open work/lean/SM/SoftGenericLemma.lean or work/lean/SM/SoftFamilyAssembly.lean (proofs).

YOUR TASK. Compare the four printed clauses with the Lean type:
  (i) P_ε generic, all in one chamber, the soft edge meets other edges only at its incident
      endpoints (check the two intersection equalities and the disjointness clause — do they say
      exactly this, for the right edges?);
  (ii) every original vertex other than M retains its turn sign; turns at M and M_ε are −χ_− and
      −χ_+; unchanged edge directions fixed; D_ε → v; sgn det(u, D_ε) = τ and sgn det(D_ε, u) = −τ
      (check the limit statement and the sign identities, and which Lean objects are u, v, D_ε, τ);
  (iii) identification of edges with parents (softParentEdge), persistence of every parent crossing,
      convergence of point and parameters to parent values, inherited visits keep their order along
      each directed edge, and the determinant sign of ordered edge directions at each inherited
      crossing is unchanged (check the limits, the order-preservation clause, and the sign clause);
  (iv) same-sign or mixed sector: these are all the crossings and the Gauss word is the parent's
      (bijectivity of the inherited-crossing map and the mapped Gauss word); loop sector: exactly one
      additional crossing y between the return edge and E_{j−1}, tending to M, whose visits a, b bound
      the oriented traversal arc from a through M, M_ε to b containing no other crossing visit, so the
      two newborn visits are cyclically adjacent and deleting them gives the parent's Gauss word.
  Also check the hypotheses (P generic, q admissible, standing n ≥ 3), the existence of ε₀ (= δ)
  such that everything holds for 0 < ε < ε₀, and the form of the limits (Tendsto as ε → 0 along
  all reals vs. the source's ε → 0⁺: is the Lean stronger, weaker, or equivalent, given how the
  functions are defined off the positive interval?). Expand the local definitions to primitives.
  Say where the Lean type is STRONGER or WEAKER than the source; any printed sub-clause with no
  Lean counterpart is a discrepancy. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": string (clause-by-clause, cite line numbers),
  "discrepancies": [strings], "stronger_than_source": [strings], "weaker_than_source": [strings],
  "supporting_definitions_inspected": [Lean names], "reviewer_files_read": [relative paths]
