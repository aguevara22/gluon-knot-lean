You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row of the CV lane against ONE printed source statement of the paper "CV"
(reference/R/CV/, frozen): CV:lem:homflyrows (row 157), Lean declaration `CV.homflyrows : CV.CVHomflyRowsData`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-lem-homflyrows-source-excerpt-lines-117-141.tex.txt (= reference/R/CV/d6_vertexedge.tex
   117-141: R = ℤ[a^{±1}, z^{±1}], δ = (a − a⁻¹)/z; (i) P_{K#J} = P_K P_J for oriented knots K, J and P_{K⊔J} = δ P_K P_J for an
   oriented knot K and an oriented link J; (ii) the two-component z^{-1} row with the linking number λ; and clause (iii) — read it).
   Context, ONLY to fix notation: d6_vertexedge.tex 142-262 (the printed proof — read only to learn which objects the statement
   names, e.g. how the connected sum, the split union and λ are meant), reference/R/CV/d10_axioms.tex (ax:homfly: CV's P and its
   normalization — accepted as CV.ax_homfly), reference/SM/sm-4-knotlaws.tex 230-266 (the SM paper's lem:homflyrows, whose Lean
   rendering SM.homflyrows this row consumes), reference/SM/sm-3-statesum.tex 1362-1437 (marked diagrams and clean marked joins:
   the SM reading of K # J), 1538-1545 (mp:zero-link: linking sums as mixed crossing-sign sums), 325-351 (def:positive-lift: the
   polygonal class; LinkEquiv = "the oriented link presented by D"). You MAY read the accepted review file's readings for the SM
   counterpart only through the fixed statement file work/drafts/MarkedProducts_statement.lean (notation map and the bundle
   HomflyRowsData with its docstrings; its theorems are sorried there).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cv-lem-homflyrows-reviewer-input-statement.lean.txt
   (module CV/HomflyRows.lean: the definitions IsLinkingNumber, IsSplitUnionFamily, IsSplitChain and the bundle CVHomflyRowsData
   with fields connected_sum, knot_split_link, two_component_row, split_union_family are UNDER REVIEW; helper lemmas' proofs are
   not). Its module docstring maps the printed notation — verify, do not trust. Do NOT open work/lean/CV/HomflyRows.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/Axioms.lean (AxHomflyData,
   CV.ax_homfly — how CV's P is the library's homfly), CV/RecordHomfly.lean (accepted CV:def:homfly), SM/LinkInterfaces.lean
   (homfly), SM/LinkLaurentRing.lean (R, R.delta, R.a, R.aInv, R.z, zRow, coeffAt), SM/LinkMoves.lean (LinkEquiv, IsMarkedInterval,
   IsSplitCircleAddition), SM/LinkDiagram.lean (Diagram, componentCount, restrict, sign, writhe), SM/LinkDiagramRecord.lean
   (Diagram.record), SM/LinkRecord.lean (Record, RecordIso, Record.joinRecord), SM/ZeroLink.lean (mixedSignSum — the accepted
   mp:zero-link rendering of 2·lk), SM/Stack.lean (blockRestrict, BlockOrdered), SM/MarkedProducts.lean ONLY the definitions
   MarkedDiagram, IsCleanMarkedJoin, Diagram.knotRestrict, twoLinking, twoLambda, aPow, IsSplitUnion, P_splitUnion (statement),
   HomflyRowsData (bundle) — use grep; do not read its proofs.

YOUR TASK: decide whether the bundle renders exactly the printed lemma. (i) "for oriented knots K, J, P_{K#J} = P_K P_J": the
field connected_sum quantifies over one-component diagrams K, J standing for their LinkEquiv classes and over any clean marked
join of marked representatives LinkEquiv to K, J — is the class-level reading faithful (the printed K # J is the connected sum of
oriented knots; is "any clean marked join of any marked representatives" exactly that, and does the field claim well-definedness of
# on classes or only the identity for every realization?); "for an oriented knot K and an oriented link J, P_{K⊔J} = δ P_K P_J":
knot_split_link with IsSplitUnion (two component blocks with no crossing between them whose block restrictions have the records
of representatives) — is that the printed split union (disjoint page images)? is δ rendered as R.delta = (a − a⁻¹)·z⁻¹? (ii) "D
an oriented link diagram with ordered components D₁, D₂ and linking number λ: [z^{-1}] P_D = …": two_component_row with
IsLinkingNumber D i j ℓ := 2ℓ = mixedSignSum D i j (the linking number as half the mixed crossing-sign sum — is that CV's λ? is
the factor-2 bookkeeping exact in aPow (−(2ℓ))?), knot restrictions D.restrict {i}, coefficient order, "[z^0] of the PRODUCT" as
printed; (iii) whatever the printed clause (iii) says (split unions of several knots / a family) versus split_union_family with
IsSplitUnionFamily (n-block split diagram) — is the n-block reading the printed statement, is the binary parenthesization
IsSplitChain part of the row or supplementary? Hypotheses: printed knot hypotheses (componentCount = 1) and 1 ≤ n kept — are
they printed? Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed clause without a Lean
counterpart or Lean clause without a printed counterpart is a discrepancy (label non-blocking ones). Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
