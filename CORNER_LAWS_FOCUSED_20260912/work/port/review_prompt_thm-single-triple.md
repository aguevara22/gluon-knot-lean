You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem against ONE printed source statement.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source statement, verbatim (frame SM15):
   work/reviews/thm-single-triple-source-excerpt-lines-234-274.tex.txt
   which is reference/SM/sm-2-amplitude.tex lines 234-274. For notation you may read all of
   reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex (def:polygon, def:chirotope,
   def:generic, def:germ at lines ~680-700, def:walls) and reference/SM/sm-2-amplitude.tex
   (def:root, def:gates, def:treesum, def:nearfar, lem:farout at lines 1-200; the proof of the
   theorem at lines 275-378 may be read ONLY to disambiguate notation, not as part of the claim).
2. The Lean statement under review with its proof replaced by `sorry`:
   work/reviews/thm-single-triple-reviewer-input-statement.lean.txt
   (the main declaration is `SM.WallGerm.single_triple_wall_response`; the file also contains
   the four local definitions `SM.gapE`, `SM.gapB`, `SM.wallU`, `SM.wallV` that the statement uses).
3. The Lean definition modules the statement refers to, under work/lean/SM/ (read the definitions
   and their docstrings; helper proofs in those files are not under review). Start with:
   Polygon, Chirotope, Generic, ZeroTriples, WallGerm, GermSides, GermSignChange, RootBoundary,
   FiniteCompositions, Gates, TreeCoefficient, NearFar, NearFarTriangular, FarOnlyOutput,
   RestrictedWordRoot, ConsecutiveTriples, CriticalCutSplit, BoundaryTripleSupports,
   CriticalContractionPositions, CriticalContractionBounds, ContractedGeometricWord,
   CollinearGateSigns, EuclideanPlane. Follow any further definition you need.
   Do NOT open work/lean/SM/SingleTripleWallResponse.lean (it contains the proof).

GLOSSARY (source -> Lean), to be verified by you, not assumed:
  wall germ t -> P(t) : `w : WallGerm n` (radius, continuous curve on (-radius, radius),
    generic off 0, non-generic at 0); P(0) = `w.center`; P_± : `w.curve s` for s>0 / s<0.
  Z_pt, Z_c : `pointZeroTriples w.center`, `concurrenceTriples w.center`.
  "φ changes sign at 0" : `w.SignChanges φ`.
  root g; boundary word a_k = μ_{g+k+1} : `boundaryWord w.center g k`, `boundaryIndex g k`.
  x<y<z critical boundary positions : `t : IncreasingBoundaryTriple n` (t.lower, t.middle, t.upper);
    K = {a_x,a_y,a_z} as vertex labels : `t.vertexSet g`.
  I_* = [x,z] : `t.spanInterval`; L = [x,y] : `t.leftInterval`; R = [y,z] : `t.rightInterval`;
    F = [0,N] : `fullBoundaryInterval hn`.
  H(x,y,z) = χ(a_z,a_y,a_x) (def:nearfar geometric array) : `geometricBoundaryArray P g t`.
  δ = (H⁺ − H⁻)/2 : the integer `d` with `H⁺ − H⁻ = 2*d`.
  a_v = p_* + ξ_v ω : `boundaryWord w.center g t.lower = p + x • ω` etc.
  ε_L, ε_R : `wallLeftEpsilon x y z`, `wallRightEpsilon x y z`.
  𝓔_J = F_H(c)_J, 𝓑_J = F_{-H}(c)_J with c = F_H^{-1}(E) (lem:farout(iii)) : `gapE H J`, `gapB H J`
    where `farOnlyCoordinates H` is c and `farTransform` is F.
  𝓤_J, 𝓥_J : `wallU`, `wallV`.
  Q (arc a_x..a_z replaced by the edge a_x a_z, at t=0, root g retained) :
    `contractedWordTuple w.center g t`, rooted at index 0.
  A_g(P) : `treeCoefficient P hP g hn : ℤ`.

YOUR TASK. Compare the printed statement with the Lean type clause by clause:
  (a) domain and hypotheses: is every printed hypothesis present, and is any hypothesis added
      that the source does not have? (In particular examine `hK`, the pairwise physical
      distinctness of the three vertices of K, against the words "a single triple of pairwise
      distinct vertices", and the hypothesis that the sign change is stated for some ordering
      a,b,c of K.)
  (b) quantifiers: "sufficiently close punctured sides", "for J = L,R", the affine writing of
      the three wall points, the existence/uniqueness of the increasing reading x<y<z.
  (c) conclusions: afr:wall-data (δ ∈ {-1,1}), afr:wall-epsilons, afr:wall-uv, the properties
      of Q (satisfies (G1), at least three vertices, retains the physical root g),
      afr:wall-proper and afr:wall-full, and the evaluation convention (gap and contracted
      coefficients at the wall centre).
  (d) definitions: expand every local Lean definition the type uses down to the accepted
      primitives and check it denotes the source object (e.g. that `contractedWordTuple` really
      is Q, that `gapE`/`gapB` are lem:farout's 𝓔_J/𝓑_J, that the two epsilons are the printed
      sign ratios, that `geometricBoundaryArray` is the printed H).
  Say explicitly where the Lean type is STRONGER than the source, where it is WEAKER, and
  whether any clause is vacuous or trivially satisfiable. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object (no prose around it) with keys:
  "verdict": "faithful" | "not faithful",
  "reason": a substantive clause-by-clause comparison in plain text (several paragraphs; cite
            source line numbers and Lean line numbers of the statement file),
  "discrepancies": [ list of strings; empty if none ],
  "stronger_than_source": [ list of strings ],
  "weaker_than_source": [ list of strings ],
  "supporting_definitions_inspected": [ fully qualified Lean names you expanded ],
  "reviewer_files_read": [ paths relative to the working directory ]
