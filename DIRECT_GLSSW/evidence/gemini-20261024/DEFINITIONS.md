# Audit of Meaning-Carrying Definitions (`audit/DEFINITIONS.md`)

This document records the complete semantic and well-definedness audit of every meaning-carrying definition in the frozen statement `DirectGLSSW.joint_normalized_homfly_corner_identity` (`project/ArmstrongFrozen/Frozen/JointNormalizedHomflyCornerIdentity.lean:23–74`) and its transitive proof closure across `project/`.

---

## 1. Polygon Domain and Planar Geometry Chain

### 1.1 `PlanarPoint`, `planarDet`, `edgeInterior`, `cyclicSuccessorPerm`, `cyclicTangent`
- **Locations**:
  - `project/DirectGLSSW/PolygonGeometry.lean:15–52`
- **Definitions**:
  - `PlanarPoint K := K × K`
  - `planarDet (u v : PlanarPoint K) : K := u.1 * v.2 - u.2 * v.1`
  - `affinePoint (p q : PlanarPoint K) (t : K) : PlanarPoint K := ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)`
  - `edgeInterior (q : Fin n → PlanarPoint K) (e : Fin n) (x : PlanarPoint K) : Prop := ∃ t : K, 0 < t ∧ t < 1 ∧ x = affinePoint (q e) (q (cyclicSuccessor e)) t`
  - `cyclicSuccessorPerm (n : ℕ) : Equiv.Perm (Fin n)` maps `i ↦ i + 1 mod n` (for `n > 0`) with inverse `(cyclicSuccessorPerm n)⁻¹ i = i - 1 mod n`.
  - `cyclicTangent (q : Fin n → PlanarPoint K) (e : Fin n) : PlanarPoint K := q (cyclicSuccessor e) - q e`
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to standard planar determinant $\det(u,v) = u_1 v_2 - u_2 v_1$, open segment $e_i^\circ = \{(1-t)v_i + t v_{i+1} : 0 < t < 1\}$, and edge displacement vector $v_{i+1} - v_i$ (`project/reference/direct_glssw_corner_proof.tex:61–84`).
  - `PUBLIC_CARRIER`: Clean standard types (`ℝ × ℝ`, `Fin n`); no hidden assumptions.
  - `WELL_DEFINEDNESS`: Total polynomial/arithmetic definitions; for $n \ge 3$, `cyclicSuccessorPerm n` is the exact cyclic shift on $\mathbb{Z}/n\mathbb{Z}$.
  - `CHARACTERIZATION`: `cyclicTangent_ne_zero` (`PolygonGeometry.lean:133–143`) proves every edge vector is nonzero under G1 (`cyclicNoncollinear`).
  - `CHOICE_INDEPENDENCE`: Canonical coordinate definitions; no arbitrary choices.
  - `DEFINITION_VERDICT`: **PASS** (`project/DirectGLSSW/PolygonGeometry.lean:15–143`).

### 1.2 `cyclicNoncollinear`, `cyclicNoTripleIntersections`, `CyclicGeneric`
- **Locations**:
  - `project/DirectGLSSW/PolygonGeometry.lean:54–66`
  - `project/DirectGLSSW/RealPolygons.lean:15–19`
- **Definitions**:
  - `cyclicNoncollinear (q : Fin n → PlanarPoint K) : Prop := ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c → planarDet (q b - q c) (q a - q c) ≠ 0`
  - `cyclicNoTripleIntersections (q : Fin n → PlanarPoint K) : Prop := ∀ e f g : Fin n, ∀ x : PlanarPoint K, e ≠ f → f ≠ g → e ≠ g → ¬ (edgeInterior q e x ∧ edgeInterior q f x ∧ edgeInterior q g x)`
  - `CyclicGeneric (q : Fin n → PlanarPoint ℝ) : Prop` is a structure with three fields: `size_ge_three : 3 ≤ n`, `g1 : cyclicNoncollinear q`, and `g2 : cyclicNoTripleIntersections q`.
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to manuscript conditions **(G1)** (no three distinct vertices are collinear) and **(G2)** (no three distinct open edges share a common point) for closed polygons with $n \ge 3$ (`project/reference/direct_glssw_corner_proof.tex:71–74`). Under G1, no vertex lies on an open edge of two other vertices, and no two open edges overlap collinearly (`PolygonCrossings.lean:45–118`).
  - `PUBLIC_CARRIER`: Contains only `3 ≤ n`, `g1`, and `g2`. Does **not** smuggle in daughter G1, non-parallel secants, or auxiliary genericity.
  - `WELL_DEFINEDNESS`: Pure first-order geometric predicates over `ℝ`.
  - `CHARACTERIZATION`: `CyclicGenericLocality.eventually_cyclicGeneric` and `generic_locus_isOpen` (`WorkingChamberDensity.lean:10–15`) prove `CyclicGeneric` defines an open subset of $(\mathbb{R}^2)^n$.
  - `CHOICE_INDEPENDENCE`: Invariant under cyclic relabeling (`cyclicGeneric_relabel`).
  - `DEFINITION_VERDICT`: **PASS** (`project/DirectGLSSW/PolygonGeometry.lean:54–66`, `project/DirectGLSSW/RealPolygons.lean:15–19`).

---

## 2. GLSSW Spinor-Gate Recursion and Root-Independence Chain

### 2.1 `scalarSignValue`, `scalarPositiveStep`, `spinorBracket`
- **Locations**:
  - `project/DirectGLSSW/SpinorGates.lean:14–48`
- **Definitions**:
  - `scalarSignValue (x : K) : ℚ := if x = 0 then 0 else if x < 0 then -1 else 1`
  - `scalarPositiveStep (x : K) : ℚ := if 0 < x then 1 else 0`
  - `spinorBracket (p q r : PlanarPoint K) : K := planarDet (p - r) (q - r)`
- **Audit Fields**:
  - `BODY_MATCH`: Matches $\operatorname{sgn}(x) \in \{\pm 1\}$ and $\Theta(x) = \mathbf{1}_{x > 0}$ for all $x \ne 0$, and the homogeneous planar determinant $\langle A_a A_b A_c \rangle = \det(v_a - v_c, v_b - v_c)$ in the patch $(1, x, y)$ (`project/reference/direct_glssw_corner_proof.tex:76–84`).
  - `PUBLIC_CARRIER`: Total functions on `K` (`ℝ`).
  - `WELL_DEFINEDNESS` & **Nonzero-Gate Audit**: Although `scalarSignValue 0 = 0`, `scalarPositiveStep 0 = 0`, and Lean's division satisfies `x / 0 = 0`, Theorem `spinorOrdinaryVertex_eq_gateProduct` and Theorem `spinorMarkedVertex_eq_gateProduct` (`SpinorVertices.lean:58–143`) together with `rootedPolygonWord_noncollinear` (`RootedAmplitude.lean:38–83`) prove that for every polygon satisfying G1 (`cyclicNoncollinear q`), **every near determinant `spinorBracket (q a) (q b) (q c)` and every far determinant `spinorBracket (q i) (q b) (q j)` appearing in any valid cut tuple of the recursion is strictly nonzero** (`hd : polygonHDet q a b c ≠ 0` and `hh : polygonHDet q i b j ≠ 0`). Thus the `0`-defaults of `scalarSignValue`, `scalarPositiveStep`, and `/ 0` are never evaluated on the G1 domain.
  - `CHARACTERIZATION`: `scalarSignValue_mul_scalarPositiveStep_neg_div` (`SpinorGates.lean:100–131`) proves that for $d \ne 0, h \ne 0$, $\operatorname{sgn}(d)\Theta(\mp h/d) = \frac{\operatorname{sgn}(d) \mp \operatorname{sgn}(h)}{2}$, matching `linearGate` (`Gates.lean:32–42`).
  - `CHOICE_INDEPENDENCE`: Exact algebraic definitions.
  - `DEFINITION_VERDICT`: **PASS** (`project/DirectGLSSW/SpinorGates.lean:14–131`).

### 2.2 `spinorOrdinaryVertex`, `spinorMarkedVertex`, `spinorPreAmplitude`, `spinorAmplitude`, `rootedSpinorAmplitude`, `polygonAmplitude`, `GLSSWRootIndependence`
- **Locations**:
  - `project/DirectGLSSW/SpinorVertices.lean:18–143`
  - `project/DirectGLSSW/SpinorRecursion.lean:18–160`
  - `project/DirectGLSSW/RootedAmplitude.lean:18–125`
  - `project/DirectGLSSW/RealPolygons.lean:21–23`
- **Definitions**:
  - `spinorOrdinaryVertex w i j S` and `spinorMarkedVertex w i j S` multiply the $m-1$ corner factors for `S.sort (· ≤ ·)` using `- (spinorBracket ... / spinorBracket ...)` (ordinary, $\varepsilon = +1$) and `+ (spinorBracket ... / spinorBracket ...)` (marked, $\varepsilon = -1$).
  - `spinorPreAmplitude w i j`: base case `1` if `j ≤ i + 1`; otherwise sums `- spinorOrdinaryVertex w i j S * ∏ ... spinorPreAmplitude` over cut sets `S ⊆ Ioo i j` with `2 ≤ S.card` (i.e., $m = |S| + 1 \ge 3$ branches), with overall minus sign.
  - `spinorAmplitude w i j`: base case `1` if `j ≤ i + 1`; otherwise sums `- (spinorOrdinaryVertex w i j S - spinorMarkedVertex w i j S) * ∏ ... spinorPreAmplitude` over **all** cut sets `S ⊆ Ioo i j` (including `S = ∅`, the unary $m=1$ branch, which vanishes for `spinorPreAmplitude` since `spinorOrdinaryVertex w i j ∅ = 1` requires $2 \le S.\text{card}$ whereas `spinorOrdinaryVertex - spinorMarkedVertex` at $S = \emptyset$ is $1 - 1 = 0$, and for $|S| = 1$, i.e. binary $m=2$ split, contributes `-(G⁺ - G⁻)`).
  - `rootedSpinorAmplitude (q : Fin n → PlanarPoint K) (root : Fin n) : ℚ := spinorAmplitude (rootedPolygonWord q root) 0 (n - 1)`
  - `polygonAmplitude (q : Fin n → PlanarPoint ℝ) (_hq : CyclicGeneric q) : ℚ := rootedSpinorAmplitude q ⟨0, by omega⟩`
  - `GLSSWRootIndependence : Prop := ∀ (n : ℕ) (q : Fin n → PlanarPoint ℝ), CyclicGeneric q → ∀ root₁ root₂ : Fin n, rootedSpinorAmplitude q root₁ = rootedSpinorAmplitude q root₂`
- **Explicit LHS Audit Answers**:
  1. **Matches published GLSSW tree recursion (`arXiv:2602.12176`, Eqs. (2)–(11))?** Yes: `spinorPreAmplitude` ($\tilde{\mathcal{A}}$) sums over $m \ge 3$ (`2 ≤ S.card`) with negative sign and ordinary vertex weight $\mathcal{V}_+$, while `spinorAmplitude` ($\mathcal{A}$) sums over all cuts with vertex weight $-(\mathcal{V}_+ - \mathcal{V}_-)$.
  2. **Is `polygonAmplitude` defined independently of HOMFLY, daughters, and knot diagrams?** Yes: `DirectGLSSW/RootedAmplitude.lean` and its imports (`SpinorRecursion`, `SpinorVertices`, `SpinorGates`, `TreeWeights`, `GeometricGates`, `Gates`, `CyclicWords`, `PolygonGeometry`) do not import any `HOMFLY`, `Daughter`, or knot module.
  3. **Are gate denominators nonzero at every recursive call on the G1 domain?** Yes: proved by `spinorAmplitude_eq_treeRecursion` and `rootedSpinorAmplitude_eq_rootedPolygonAmplitude` (`SpinorRecursion.lean:105–158`, `RootedAmplitude.lean:85–123`).
  4. **Is `GLSSWRootIndependence` a pure property of the independent recursion?** Yes: it states root-independence of `rootedSpinorAmplitude` on `CyclicGeneric` polygons and makes no reference to HOMFLY or knot invariants.
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to GLSSW recursion (`arXiv:2602.12176`, Eqs. (2)–(11)) and manuscript §2.1 (`direct_glssw_corner_proof.tex:75–93`).
  - `PUBLIC_CARRIER`: Clean types (`(Fin n → PlanarPoint ℝ) → CyclicGeneric q → ℚ`).
  - `WELL_DEFINEDNESS`: Terminates by strong recursion on `j - i`; all denominators nonzero under G1.
  - `CHARACTERIZATION`: `rootedSpinorAmplitude_eq_rootedPolygonAmplitude` (`RootedAmplitude.lean:115–123`) identifies the spinor-ratio recursion with the linear-gate recursion.
  - `CHOICE_INDEPENDENCE`: Root choice `0` in `polygonAmplitude` is made independent of root by the explicit hypothesis `GLSSWRootIndependence`.
  - `DEFINITION_VERDICT`: **PASS** (`project/DirectGLSSW/SpinorRecursion.lean:18–160`, `project/DirectGLSSW/RootedAmplitude.lean:18–125`, `project/DirectGLSSW/RealPolygons.lean:21–23`).

---

## 3. PL Link Diagrams and Normalized HOMFLY Evaluator Chain

### 3.1 `PLLinkDiagram`, `BasedTraversal`, `crossingSign`, `switchCrossing`, `smoothCrossing`, `badCrossings`
- **Locations**:
  - `project/DirectGLSSW/HOMFLY/PLDiagrams.lean:54–215`
  - `project/DirectGLSSW/HOMFLY/BasedTraversal.lean:26–95`
  - `project/DirectGLSSW/HOMFLY/HOMFLYSkeinEvaluator.lean:20–52`
- **Definitions**:
  - `PLLinkDiagram`: finite embedded oriented piecewise-linear link diagram in $\mathbb{R}^2$ with explicit vertex coordinates, directed arcs, 4-valent transverse crossings (`crossing_transverse`), degree-(1,1) regular vertices (`regular_degree_one`), positively collinear through-branches (`through_tangents_positive_collinear`), disjoint open arc interiors (`arc_interiors_disjoint`), and over-branch selection (`overBranch`).
  - `crossingDet D c := planarDet (strandTangent D c (D.overBranch c)) (strandTangent D c (otherBranch (D.overBranch c)))`
  - `crossingSign D c := nonzeroScalarSign (crossingDet D c) (crossingDet_ne_zero D c)` (`Sign.pos` if $\det(t_{\mathrm{over}}, t_{\mathrm{under}}) > 0$, `Sign.neg` if $< 0$).
  - `switchCrossing D c`: flips `D.overBranch c` to `otherBranch (D.overBranch c)`, keeping geometry and continuation unchanged.
  - `smoothCrossing D c`: swaps `D.through c` by `Equiv.swap 0 1` and updates `D.continuation` at the two incoming ports of $c$ (`HOMFLYSkeinEvaluator.lean:22–50`) to perform the oriented smoothing $L_0$ at $c$.
  - `BasedTraversal D`: component ordering `componentIndex` and base arc `baseArc C` on each component.
  - `badCrossings T`: set of crossings $c$ where the first-visited branch in the lexicographic traversal order `(componentOrder, arcOffset)` is the under-branch (`firstVisitedBranch T c ≠ D.overBranch c`).
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to manuscript §2.2 and §5.1–5.2 (`direct_glssw_corner_proof.tex:98–128, 1060–1147`).
  - `PUBLIC_CARRIER`: Standard combinatorial/geometric PL link diagram fields; all 24 fields of `PLLinkDiagram` and 2 fields of `BasedTraversal` are `TYPING`.
  - `WELL_DEFINEDNESS`: `crossingDet_ne_zero` is proved from `D.crossing_transverse`; `smoothCrossing` is proved to satisfy all `PLLinkDiagram` invariants (`HOMFLYSkeinEvaluator.lean:22–50`).
  - `CHARACTERIZATION`: `badCrossings_switch_card` proves switching the first bad crossing strictly decreases `(badCrossings T).card`.
  - `CHOICE_INDEPENDENCE`: Independence of `BasedTraversal` is proved for `Gemini.candidateEvaluator` (`NormalizedEvaluatorUniqueness.lean:100–110`).
  - `DEFINITION_VERDICT`: **PASS** (`project/DirectGLSSW/HOMFLY/PLDiagrams.lean:54–215`, `project/DirectGLSSW/HOMFLY/BasedTraversal.lean:26–95`).

### 3.2 `HOMFLYCoeff`, `coeff`, `aMonomial`, `aInvMonomial`, `zMonomial`, `unlinkFactor`, `descendingLaurentEvaluator`, `IsNormalizedDescendingSkeinEvaluator`, `Gemini.candidateEvaluator`
- **Locations**:
  - `project/DirectGLSSW/HOMFLY/Coefficients.lean:15–125`
  - `project/DirectGLSSW/HOMFLY/HOMFLYSkeinEvaluator.lean:54–140`
  - `project/NormalizedEvaluatorUniqueness.lean:15–112`
  - `project/Gemini/Solution.lean:15–45`
- **Definitions**:
  - `HOMFLYCoeff := AddMonoidAlgebra ℤ (ℤ × ℤ)` (representing $\mathbb{Z}[a^{\pm 1}, z^{\pm 1}]$).
  - `coeff (p : HOMFLYCoeff) (i j : ℤ) : ℤ := p (i, j)` (extracts the coefficient $c_{i,j}$ of $a^i z^j$).
  - `aMonomial := single (1, 0) 1`, `aInvMonomial := single (-1, 0) 1`, `zMonomial := single (0, 1) 1`, `zInvMonomial := single (0, -1) 1`.
  - `unlinkFactor := (aMonomial - aInvMonomial) * zInvMonomial` ($\delta = (a - a^{-1})z^{-1}$).
  - `descendingLaurentEvaluator D T`: recursive descending skein tree evaluator in `HOMFLYCoeff` using complexity `(D.nCrossing, (badCrossings T).card)`.
  - `IsNormalizedDescendingSkeinEvaluator H`: requires $H(D) = \delta^{k-1}$ whenever `badCrossings T = ∅`, and $a^{-1} H(L_+) - a H(L_-) = z H(L_0)$ at every crossing.
  - `Gemini.candidateEvaluator D hD`: canonical normalized HOMFLY evaluator (`NormalizedEvaluatorUniqueness.lean:26`).
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to manuscript Eq. `eq:homfly-conventions`:
    $$a^{-1} H(L_+) - a H(L_-) = z H(L_0), \qquad H(\bigcirc) = 1, \qquad \delta = \frac{a - a^{-1}}{z}, \qquad H(L) = \sum_{i,j \in \mathbb{Z}} c_{i,j}(L) a^i z^j.$$
  - `PUBLIC_CARRIER`: Clean signature `(D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff`.
  - `WELL_DEFINEDNESS`: Terminates by lexicographic induction on `(nCrossing, badCrossings.card)`.
  - `CHARACTERIZATION`: `JointCandidateAssembly.lean:18–79` proves unconditionally that `Gemini.candidateEvaluator` satisfies `IsNormalizedDescendingSkeinEvaluator`, uniqueness among all such evaluators, agreement with `descendingLaurentEvaluator D T` for every `T`, `SignedDiagramIso` invariance, and `SignedRegularDeletion` invariance.
  - `CHOICE_INDEPENDENCE`: Uniqueness and traversal independence proved unconditionally (`NormalizedEvaluatorUniqueness.lean:65–110`).
  - `DEFINITION_VERDICT`: **PASS** (`project/DirectGLSSW/HOMFLY/Coefficients.lean:15–125`, `project/DirectGLSSW/HOMFLY/HOMFLYSkeinEvaluator.lean:54–140`, `project/NormalizedEvaluatorUniqueness.lean:15–112`).

---

## 4. Crossings, Smoothing Permutations, Non-Alternation, and Uniform Supports Chain

### 4.1 `PolygonCrossing`, `PolygonEvent`, `smoothingDartPermutation`, `polygonNonalternating`
- **Locations**:
  - `project/DirectGLSSW/PolygonCrossings.lean:15–120`
  - `project/DirectGLSSW/PolygonEvents.lean:15–130`
  - `project/DirectGLSSW/SmoothingPermutations.lean:15–110`
  - `project/DirectGLSSW/PolygonNonalternation.lean:15–65`
- **Definitions**:
  - `PolygonCrossing q`: unordered interior edge intersections encoded canonically by `{p : Fin n × Fin n // p.1.val < p.2.val ∧ edgeInteriorCrosses q p.1 p.2}`.
  - `PolygonEvent q := Fin n ⊕ (PolygonCrossing q × Bool)`: either a vertex anchor `.inl e` ($t=0$ on edge $e$) or a crossing visit `.inr (c, b)` (`b = false` on edge `c.1`, `b = true` on edge `c.2`).
  - `smoothingPairing q S`: flips `(c, b) ↦ (c, !b)` for $c \in S$ and fixes all other events.
  - `smoothingDartPermutation q hG2 S := (smoothingPairing q S).trans (polygonEventSuccessor q hG2)` (first advances along the elementary subsegment to its terminal event, then applies the smoothing switch if at a crossing in $S$).
  - `polygonNonalternating q hG2 S`: on every parent edge $e$, no two consecutive $S$-visits along $e$ have opposite transverse crossing signs (`crossingSignAlongEdge`).
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to oriented smoothing of $P$ at $S \subseteq \mathcal{C}(P)$ and the non-alternating separating support condition $\mathcal{D}_{\mathrm{sep}}(P)$ (`direct_glssw_corner_proof.tex:130–156, 402–468`).
  - `PUBLIC_CARRIER`: Clean finite types parameterized by `(q, hG2, S)`.
  - `WELL_DEFINEDNESS`: Under G2 (`cyclicNoTripleIntersections q`), crossing parameters along each edge are strictly ordered, making `polygonEventSuccessor q hG2` a well-defined single-cycle permutation on `PolygonEvent q`.
  - `CHARACTERIZATION`: `DaughterInjectivity.selectedVisits_differentDartOrbits` proves Lemma `lem:sep-support`: for any `polygonNonalternating` support $S$, every $c \in S$ has its two visits in distinct cycles of `smoothingDartPermutation`, and every daughter visits each parent edge at most once (`daughterCarrier_injective`).
  - `CHOICE_INDEPENDENCE`: Canonical ordering along each edge.
  - `DEFINITION_VERDICT`: **PASS** (`project/DirectGLSSW/PolygonCrossings.lean`, `project/DirectGLSSW/PolygonEvents.lean`, `project/DirectGLSSW/SmoothingPermutations.lean`, `project/DirectGLSSW/PolygonNonalternation.lean`).

### 4.2 `retainedCorner`, `CornerCoord`, `daughterSideVector`, `uniformDaughterSupport` (`Supports`)
- **Locations**:
  - `project/DirectGLSSW/DaughterFirstReturn.lean:21–100, 204–509`
  - `project/UniformDaughterSupportCharacterization.lean:10–146`
- **Definitions**:
  - `retainedCorner q S x`: `True` if `x = .inl e` (original polygon vertex), `v.1 ∈ S` if `x = .inr v` (smoothed crossing corner), and `False` if `x = .inr v` with `v.1 ∉ S` (unselected crossing where the daughter passes straight through).
  - `CornerCoord q hG2 S root`: subtype of orbit coordinates of `root` under `smoothingDartPermutation` at which `retainedCorner q S` holds, ordered cyclically by `cornerEnumeration`.
  - `daughterSideVector q hG2 S root i`: displacement vector `daughterVertex (cyclicSuccessor i) - daughterVertex i` between consecutive retained corners of the daughter cycle.
  - `Supports` (in the frozen theorem) / `uniformDaughterSupport q hq S`: `polygonNonalternating q hq.g2 S` AND for every component `C` of `smoothingDartPermutation q hq.g2 S`, there exists a retained corner `root` in `C` such that all consecutive retained-side determinants `planarDet (daughterSideVector prev) (daughterSideVector i)` are strictly positive OR all are strictly negative.
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to $\mathcal{D}_{\mathrm{u}}(P)$ (`direct_glssw_corner_proof.tex:130–156`).
  - `PUBLIC_CARRIER`: Exact match to the frozen theorem's `Supports` subtype (`JointNormalizedHomflyCornerIdentity.lean:42–59`).
  - `WELL_DEFINEDNESS` & **Non-Filtering Audit**: Does `∃ root, retainedCorner q S root ∧ componentOf ... root = C` ever discard a valid daughter component? **No**: Theorem `everyDartOrbit_hasCorner` (`DaughterFirstReturn.lean:204–260`) and `exists_retained_root` (`SharpDaughterRotationDegree.lean:111–117`) prove that for every $n \ge 3$, every cycle $C$ of `smoothingDartPermutation` contains at least one retained corner. Furthermore, Theorem `daughterSide_positive_multiple` (`DaughterFirstReturn.lean:417–485`) proves every `daughterSideVector` is a positive scalar multiple of the parent edge tangent `cyclicTangent q e`, and `daughterUniform_iff_carrier` (`UniformDaughterSupportCharacterization.lean:109–146`) proves the uniformity condition is completely independent of which retained `root` in $C$ is chosen!
  - `CHARACTERIZATION`: `eventually_uniformDaughterSupport_map_iff` (`UniformDaughterSupportLocality.lean:188–206`) proves local stability of `Supports` on the full parent G1–G2 domain.
  - `CHOICE_INDEPENDENCE`: Proved root-independent by `daughterUniform_iff_carrier`.
  - `DEFINITION_VERDICT`: **PASS** (`project/DirectGLSSW/DaughterFirstReturn.lean:21–509`, `project/UniformDaughterSupportCharacterization.lean:10–146`).

---

## 5. Daughter Positive Diagram $K_Q$, Rotation Number $r(Q)$, and Corner State Sum Chain

### 5.1 `positivePolygonEventDiagram`, `SharpDaughter.sharpDaughterDiagram`, `SharpDaughter.arc_count_pos`
- **Locations**:
  - `project/DirectGLSSW/HOMFLY/PositiveDiagram.lean:19–79`
  - `project/PolygonPositiveDiagram.lean:64–91`
  - `project/SharpDaughterGeometry.lean:10–203`
  - `project/SharpDaughterDiagram.lean:10–183`
  - `project/SharpDaughterCharacterization.lean:10–188`
  - `project/SharpDaughterSelfCrossingCount.lean:14–45`
- **Definitions**:
  - `positivePolygonEventDiagram q hq`: the embedded PL link diagram of parent polygon `q` with positive overstrand selection at every crossing (`0 < planarDet (strandTangent D c (overBranch c)) (strandTangent D c (otherBranch (overBranch c)))`).
  - `SharpDaughter.sharpDaughterDiagram q hq S C hNA`: for any parent `hq : CyclicGeneric q`, separating support `hNA : polygonNonalternating q hq.g2 S`, and smoothed component `C`, restricts `positivePolygonEventDiagram q hq` to the arcs in `Arc = Fibre (smoothingDartPermutation q hq.g2 S) C` and crossings in `Crossing = {c // c ∉ S ∧ ∀ i : Fin 2, componentOf P (outgoing c i) = C}`.
- **Explicit Daughter $K_Q$ Audit Answers**:
  1. **Constructed on the full parent G1–G2 domain without assuming daughter G1?** Yes: `sharpDaughterDiagram` takes only `(q, hq : CyclicGeneric q, S, C, hNA : polygonNonalternating q hq.g2 S)` (`SharpDaughterDiagram.lean:8–9, 36, 73`). No daughter G1 hypothesis is present.
  2. **Retains only self-crossings of $Q$ outside $S$?** Yes: `actual_crossing_retained_iff` (`SharpDaughterCharacterization.lean:46–62`) and `sharpDaughterDiagram_selfCrossingCount` (`SharpDaughterSelfCrossingCount.lean:14–36`) prove that `sharpDaughterDiagram.nCrossing` counts precisely `{c : PolygonCrossing q // c ∉ S ∧ ∀ b : Bool, componentOf (P q hq S) (Sum.inr (c, b)) = C}`.
  3. **Ignores mixed crossings with other daughters and smoothed crossings in $S$?** Yes: `selected_crossing_regular` and `mixed_crossing_regular` (`SharpDaughterCharacterization.lean:122–145`) prove that smoothed crossings in $S$ and mixed crossings between $C$ and other components become regular degree-(1,1) subdivision vertices in `sharpDaughterDiagram`, contributing `0` to `nCrossing` and leaving `H` invariant by `SignedRegularDeletion`.
  4. **Uses the manuscript's positive overstrand convention $\det(t_{\mathrm{over}}, t_{\mathrm{under}}) > 0$?** Yes: `sharpDaughterDiagram_crossingSign` (`SharpDaughterDiagram.lean:176–181`) and `positiveDiagram_crossingDet_pos` (`PositiveDiagram.lean:45–50`) prove that at every crossing of `sharpDaughterDiagram`, $\det(t_{\mathrm{over}}, t_{\mathrm{under}}) > 0$ and `crossingSign = Sign.pos`.
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to $K_Q$ and $c(Q)$ in manuscript §2.3 (`direct_glssw_corner_proof.tex:140–156`).
  - `PUBLIC_CARRIER`: Depends only on parent `hq : CyclicGeneric q`, `S`, `C`, and `hNA`.
  - `WELL_DEFINEDNESS`: All 24 `PLLinkDiagram` axioms are proved for `sharpDaughterDiagram` (`SharpDaughterDiagram.lean:73–139`), using `both_visits_not_selected` (`SharpDaughterGeometry.lean:129–140`, from Lemma `lem:sep-support`) to show a selected crossing $c \in S$ never has both visits in the same component $C$.
  - `CHARACTERIZATION`: `sharpDaughterDiagram_componentCount` proves `diagramComponentCount = 1`; `GeneralSharpRetained.corner_coefficient` (`GeneralSharpRetainedCorner.lean:35–48`) proves that when daughter G1 also holds, `sharpDaughterDiagram` has the exact same HOMFLY polynomial, crossing count, and rotation integer as `positivePolygonEventDiagram (daughterVertex q hq.g2 S root)`.
  - `CHOICE_INDEPENDENCE`: Constructed directly from the component `C : Component (smoothingDartPermutation q hq.g2 S)` without choosing a root.
  - `DEFINITION_VERDICT`: **PASS** (`project/SharpDaughterGeometry.lean`, `project/SharpDaughterDiagram.lean`, `project/SharpDaughterCharacterization.lean`, `project/SharpDaughterSelfCrossingCount.lean`).

### 5.2 `SharpDaughterRotation.sharpDaughterRotationInteger` and Rounding Characterization
- **Locations**:
  - `project/PrincipalTurning.lean:10–73`
  - `project/HalfTurnExclusion.lean:8–67`
  - `project/GlobalRoundedCurve.lean:8–114`
  - `project/ContinuousRoundedTangent.lean:9–85`
  - `project/CornerTangentLift.lean:8–65`
  - `project/AngleLiftUniqueness.lean:10–35`
  - `project/ActualAdmissibleRounding.lean:9–72`
  - `project/SharpDaughterTurns.lean:13–167`
  - `project/SharpDaughterRotationDegree.lean:12–150`
  - `project/SharpDaughterRotationInteger.lean:14–95`
- **Definitions**:
  - `turn D e := Complex.arg (arcVector D (D.continuation e) / arcVector D e)`
  - `totalTurn D := ∑ e : Fin D.nArc, turn D e`
  - `sharpDaughterRotationInteger q hq S C hNA := Classical.choose (existsUnique_component_actual_rotation_integer q hq S C hNA)`
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to manuscript rotation number $r(Q) \in \mathbb{Z}$, defined as $\frac{1}{2\pi}$ times the total signed turning angle of $Q$ (sum of exterior turns in $(-\pi, \pi)$ at the retained corners, equal to the tangent winding degree of any admissible short-turn $C^1$ rounding of $Q$) (`direct_glssw_corner_proof.tex:116–128, 140–156`).
  - `PUBLIC_CARRIER`: Takes `(q, hq, S, C, hNA) → ℤ`; no daughter G1 hypothesis or fallback default.
  - `WELL_DEFINEDNESS`: `turn_ne_pi` and `turn_mem_open_semicircle` (`HalfTurnExclusion.lean:49–67`) prove that for every arc $e$ of any `PLLinkDiagram`, consecutive arcs cannot point in opposite directions (otherwise their open segments would overlap, violating `arc_interiors_disjoint`), so `turn D e ∈ (-π, π)` strictly! `totalTurn_coe_angle_zero` proves `(totalTurn D : Real.Angle) = 0`, so `existsUnique_turnInteger` proves there is a **unique** integer $r \in \mathbb{Z}$ with `totalTurn D = r * (2 * π)`.
  - `CHARACTERIZATION`: `sharpDaughterRotationInteger_spec` and `sharpDaughterRotationInteger_characterization` (`SharpDaughterRotationInteger.lean:17–55`) prove that `r = sharpDaughterRotationInteger q hq S C hNA` simultaneously satisfies:
    1. `totalTurn (sharpDaughterDiagram q hq S C hNA) = r * (2 * π)` (sum over all elementary arcs),
    2. `cornerTotalTurn q hq S root hroot = r * (2 * π)` for every retained corner `root` of $C$ (sum of principal angles between consecutive `daughterSideVector`s, since `incomingTurn_noncorner` vanishes at all unselected crossings),
    3. `actualTangentLift ... (t + L) - actualTangentLift ... t = r * (2 * π)` for the explicit $C^1$ quadratic corner rounding `roundedComponentCurve` at every `δ : RoundingFraction`,
    4. `f L - f 0 = r * (2 * π)` for **any** continuous angle lift `f : ℝ → ℝ` of `(roundedComponentVelocity ... t).arg`.
  - `CHOICE_INDEPENDENCE`: Uniqueness (`existsUnique_component_actual_rotation_integer`), root-independence (`cornerTotalTurn_root_independent`), rounding-parameter `δ` independence, and continuous lift `f` independence (`continuous_angle_lifts_same_increment`) are all proved.
  - `DEFINITION_VERDICT`: **PASS** (`project/SharpDaughterRotationInteger.lean:14–95`, `project/SharpDaughterRotationDegree.lean:12–150`).

### 5.3 `leftTurnCount` (`ell`) and `cornerStateSum`
- **Locations**:
  - `project/ArmstrongFrozen/Frozen/JointNormalizedHomflyCornerIdentity.lean:39–73`
  - `project/CornerStateSumLocality.lean:16–53, 223–285`
- **Definitions**:
  - `ell : ℕ := (Finset.univ.filter (fun i : Fin n => 0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i)) (cyclicTangent q i))).card`
  - `cornerStateSum H q hq : ℤ := (-1 : ℤ) ^ ell * ∑ S : Supports, (-1 : ℤ) ^ S.val.card * ∏ C : Component (smoothingDartPermutation q hq.g2 S.val), coeff (H (sharpDaughterDiagram q hq S.val C S.property.1) (arc_count_pos ...)) (1 - (sharpDaughterDiagram ...).nCrossing - |sharpDaughterRotationInteger q hq S.val C S.property.1|) 0`
- **Audit Fields**:
  - `BODY_MATCH`: Exact match to the RHS of Theorem `thm:main` (`direct_glssw_corner_proof.tex:158–165`):
    $$(-1)^{\ell(P)} \sum_{S \in \mathcal{D}_{\mathrm{u}}(P)} (-1)^{|S|} \prod_{Q \in \pi_0(P_S)} c_{1 - c(Q) - |r(Q)|,\, 0}(K_Q).$$
    At vertex $i$, the incoming edge is $i - 1 = (\text{cyclicSuccessorPerm } n)^{-1} i$ and the outgoing edge is $i$, so `0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i)) (cyclicTangent q i)` is the exact left-turn condition $\det(v_i - v_{i-1}, v_{i+1} - v_i) > 0$.
  - `PUBLIC_CARRIER`: In the frozen theorem, the RHS is expanded inline (`JointNormalizedHomflyCornerIdentity.lean:39–73`), and `cornerStateSum_eq_literal` (`CornerStateSumLocality.lean:223–262`) proves `rfl` definitional equality between `cornerStateSum H q hq` and the inline frozen RHS.
  - `WELL_DEFINEDNESS`: Finite sum and product over `Fintype` instances; cast from `ℤ` to `ℚ` matches the manuscript's integer state sum equals rational amplitude claim.
  - `CHARACTERIZATION`: `eventually_cornerStateSum_eq` (`CornerStateSumLocality.lean:267–285`) proves local constancy of `cornerStateSum H q hq` on the full parent G1–G2 domain.
  - `CHOICE_INDEPENDENCE`: Summands and factors are indexed by `Supports` and `Component` without choosing representatives.
  - `DEFINITION_VERDICT`: **PASS** (`project/CornerStateSumLocality.lean:16–285`).

---

## 6. Internal Working-Domain and Auxiliary Definitions Audit

| Internal Definition | Location | Audit Summary | Verdict |
|---|---|---|---|
| `auxiliaryGenericity` | `project/DirectGLSSW/GeometricSmoothingWeights.lean` | Requires that for every separating support $S \in \mathcal{D}_{\mathrm{sep}}(P)$ and retained corner `root`, the retained-vertex daughter polygon `daughterVertex q hq.g2 S root` satisfies `CyclicGeneric` (specifically daughter G1, since daughter G2 already holds on the parent G1–G2 domain by `daughter_no_triple`). Used only internally and discharged by chamber density (`WorkingReconstruction.lean`, `GenericCornerIdentityContinuation.lean`). | **PASS** |
| `separatingSmoothingSum` | `project/DirectGLSSW/GeometricSmoothingWeights.lean` | Literal alternating sum $\Gamma(P) = \sum_{S \in \mathcal{D}_{\mathrm{sep}}(P)} (-1)^{|S|} \prod_{C} \mathcal{A}(Q_C)$ over separating supports on the auxiliary domain. | **PASS** |
| `workingAuxiliaryDomain` | `project/WorkingAuxiliaryDomain.lean:10–12` | `{r \| CyclicGeneric r ∧ eval ... c ≠ 0}` for a nonzero polynomial $c$ obtained by clearing carrier denominators (`CyclicCarrierClearing.lean`). Proved open and dense in every G1–G2 chamber (`WorkingChamberDensity.lean:24–44`). | **PASS** |
| `GammaM` & `tinyParent` | `project/ActiveArcGammaM.lean`, `project/ActiveArcLiteralTinySourceCut.lean` | Literal open-arc primitive $\Gamma_{\mathrm{m}}(A)$ and physical tiny-parent polygon `Fin.cons (affinePoint crossingPoint (q 0) η) parent` used in the cursor recursion (`un:transport-lemma`). No artificial projector or proxy. | **PASS** |
| `PrimitiveContinuation.fullPrimitive` | `project/PrimitiveContinuation.lean` | Optional continuation object; **verified outside the 1,475-module transitive import closure** of `ArmstrongFrozen.Frozen.JointNormalizedHomflyCornerIdentity` and never used to replace manuscript $\Gamma$. | **PASS (Excluded)** |

---

## Summary Table of Mandatory Definition Verdicts

| Chain / Symbol Group | `BODY_MATCH` | `PUBLIC_CARRIER` | `WELL_DEFINEDNESS` | `CHARACTERIZATION` | `CHOICE_INDEPENDENCE` | `DEFINITION_VERDICT` |
|---|---|---|---|---|---|---|
| `CyclicGeneric`, `cyclicNoncollinear`, `cyclicNoTripleIntersections`, `edgeInterior`, `planarDet`, `cyclicTangent`, `cyclicSuccessorPerm` | PASS | PASS | PASS | PASS | PASS | **PASS** |
| `GLSSWRootIndependence`, `polygonAmplitude`, `rootedSpinorAmplitude`, `spinorAmplitude`, `spinorPreAmplitude`, `spinorOrdinaryVertex`, `spinorMarkedVertex`, `scalarSignValue`, `scalarPositiveStep`, `spinorBracket` | PASS | PASS | PASS | PASS | PASS | **PASS** |
| `PLLinkDiagram`, `BasedTraversal`, `HOMFLYCoeff`, `coeff`, `unlinkFactor`, `aMonomial`, `aInvMonomial`, `zMonomial`, `crossingSign`, `switchCrossing`, `smoothCrossing`, `badCrossings`, `descendingLaurentEvaluator`, `IsNormalizedDescendingSkeinEvaluator`, `SignedDiagramIso`, `SignedRegularDeletion` | PASS | PASS | PASS | PASS | PASS | **PASS** |
| `PolygonCrossing`, `PolygonEvent`, `smoothingDartPermutation`, `PolygonNonalternation.polygonNonalternating` | PASS | PASS | PASS | PASS | PASS | **PASS** |
| `DaughterFirstReturn.retainedCorner`, `DaughterFirstReturn.CornerCoord`, `DaughterFirstReturn.daughterSideVector`, `Supports` | PASS | PASS | PASS | PASS | PASS | **PASS** |
| `SharpDaughter.sharpDaughterDiagram`, `SharpDaughter.arc_count_pos`, `SharpDaughterRotation.sharpDaughterRotationInteger`, `cornerStateSum` | PASS | PASS | PASS | PASS | PASS | **PASS** |
