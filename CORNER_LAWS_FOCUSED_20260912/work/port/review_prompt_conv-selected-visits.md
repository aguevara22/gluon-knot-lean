You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the row and must not read its proofs. Your job is a DEFINITION/CONVENTION-fidelity
review of one row against one printed source convention.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim (frame SM15): work/reviews/conv-selected-visits-source-excerpt-lines-29-52.tex.txt
   = reference/SM/sm-3-statesum.tex lines 29-52 (conv:selected-visits and the explanatory
   rem:selected-visits). Context: sm-3 lines 1-27 (def:decomposition, def:smoothing: cutting the
   traversal circle at the two visits of each selected crossing and reconnecting) and the proof of
   lem:carriers, sm-3 lines 96-116 ("Finite successor model": marks, the successor permutation ρ,
   the swapped permutation ρ_S with ρ_S(a) = ρ(b), ρ_S(b) = ρ(a), "the node a retains its incoming
   arc and leaves along the old outgoing arc at b. This also implements the incoming-visit
   convention explicitly"). Notation: reference/SM/sm-1-polygons.tex (def:crossings ~138: visits,
   def:gauss ~249: the traversal circle Γ(P) and visit order).
2. The Lean row with every proof replaced by `sorry`:
   work/reviews/conv-selected-visits-reviewer-input-statement.lean.txt (main declaration
   `SM.selected_visits_convention`; bundle `SelectedVisitsConventionData`).
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): CarrierMarks (Mark, markPosition, markKey, markList), CarrierSuccessor (markCycle,
   nextMark, prevMark, markSuccessor), CarrierVisitTwin (visitTwin, selectedVisitTwin,
   selectedVisitTwinPerm), CarrierSmoothing (selectedMarkPerm, smoothingSuccessor, Component, owner),
   Traversal (TraversalPoint, traversalEvaluation, traversalBetween), GaussVisits (Visit,
   visitPosition), Crossings, InterlaceSupports / DecompositionDefinition (IsDecomposition =
   independent support), Polygon. Do NOT open work/lean/SM/SelectedVisitsConvention.lean (proofs).

YOUR TASK. The source convention: at a selected crossing with traversal visits a, b, reconnect the
incoming arc at a to the outgoing arc at b and the incoming arc at b to the outgoing arc at a;
assign the original visit a to the resulting cycle containing the incoming one-sided arc at a
(likewise b); unselected visits retain their ordinary traversal ownership; thus a selected visit is
assigned to one abstract carrier even though the two carriers through the smoothing site have the
same point of the plane; it specifies endpoint ownership only, the geometric reconnection is
unchanged. The Lean row adopts the finite successor model of the source's own proof (marks =
vertices and visits on the traversal circle, ρ = markSuccessor, ρ_S = smoothingSuccessor =
ρ ∘ selectedMarkPerm, carriers = cycles of ρ_S, owner = own cycle). Decide: (a) is ρ (markSuccessor)
really the successor on the traversal circle marked at all vertices and visits (expand markList /
markKey / markPosition: sorted by traversal position)? (b) is the reconnection clause exactly the
printed one (incoming arc at a → outgoing arc at b, and vice versa)? (c) is "assign a to the cycle
containing the incoming one-sided arc at a" captured — the incoming arc at a is traversed under ρ_S
by (ρ_S)⁻¹(a), which the row identifies as selectedMarkPerm S (ρ⁻¹ a) with the same plane point as
ρ⁻¹(a) and the same owner as a; is owner a (a's own ρ_S-cycle) the printed assignment? (d)
unselected visits and vertices keep ρ; (e) same plane point of the two visits, distinct carriers for
an independent S; (f) the domain: every generic P with n ≥ 3 and every decomposition S (independent
set) — is the independence hypothesis appropriate for the convention (the source states it for
selected crossings of a decomposition)? Is anything printed missing, vacuous, stronger or weaker?
Note explicitly whether adopting the source proof's successor model as the definition of carriers
and ownership is a faithful reading of the convention (the source says the model "implements the
incoming-visit convention explicitly"). Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": string (cite source lines 29-52 / 96-116 and
  statement-file lines), "discrepancies": [strings], "stronger_than_source": [strings],
  "weaker_than_source": [strings], "supporting_definitions_inspected": [Lean names],
  "reviewer_files_read": [relative paths]
