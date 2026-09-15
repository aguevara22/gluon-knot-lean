# Glossary: source notation to Lean names (accepted rows and standing conventions)

Generated from work/lean/lean-declarations.json on 2026-09-12. Read the module for the exact definition.

## Notation

| source | Lean | module |
|---|---|---|
| P, a labelled polygon (n vertices) | `LabelledTuple n` (= `ZMod n → Plane`); cyclic quotient `Polygon n hn`; `GenericTuple n`, `GenericPolygon n` bundle genericity | SM.Polygon, SM.Generic |
| μ_i, vertex i | `P i` with `i : ZMod n` | SM.Polygon |
| E_i, edge vector; edge segment | `edge P i`, `edgeSegment P i`, `edgeInterior P i` | SM.Polygon, SM.Segment |
| χ_ijk, chirotope | `chi P i j k : SignType` | SM.Chirotope |
| τ_i, turn; ℓ(P), left turns; z(P), zero turns | `turn P i`, `leftTurns P`, `rightTurns P`, `zeroTurns P` | SM.Chirotope, SM.ShiftTheorem |
| (G1), (G2), generic locus 𝒰_n | `G1 P`, `G2 P`, `Generic P` | SM.Generic |
| regular locus ℛ_n; rot(P) | `Regular P`; `rotationNumber P` | SM.RegularDefinition, SM.RotationNumber |
| σP, shift; P̄, reversal | `shift k P` (σ = `shift 1`); `reversal P` (i ↦ 2−i) | SM.Reversal |
| X(P), crossings | `Crossing P`, `crossingData` | SM.Crossings, SM.CrossingEquiv |
| chambers | `chamber` (components of the cyclic quotient), `labelledChamber` (components of `GenericTuple n`), `polygonProjection` | SM.CyclicChambers, SM.Chambers |
| Gauss word, interlacement, visible/silent, weakly generic | `gaussWord`, `interlacement_definition`, `visible_signature_definition`, `weak_definition` | SM.GaussDefinition, SM.InterlaceDefinition, SM.VisibleDefinition, SM.WeakGeneric |
| admissible (n, r); fibres | `Admissible n r`; `nonempty_fibres` | SM.Admissible, SM.Fibres |
| wall germs, named walls, sides | `WallGerm n`, `wall_germ_definition`, `named_walls_definition`, `flat_sides`, `wall_sides`, `cusp_sides_of_continuous_curve` | SM.WallGerm, SM.GermDefinition, SM.NamedWallsDefinition, SM.FlatSides, SM.WallSides, SM.CuspCurve |
| deletion halves, children | `deletion_halves_definition`, `children` | SM.DeletionHalvesDefinition, SM.Children |
| root g, gates, tree sum A_g | `rootData`, `gatesData`, `treesumData`, `treeCoefficient P hP g hn : ℤ` | SM.RootBoundary, SM.Gates, SM.TreeCoefficient |
| near/far data | `nearfarData`, `farout` | SM.NearFar, SM.Farout |
| standing conventions | `[NeZero n]` or `hn : 3 ≤ n` where the source says n ≥ 3; signs are `SignType` {−1,0,1}; coordinates are real pairs (`Plane`) | everywhere |

## Accepted rows (source label, main declaration, module)

| row | declaration | module |
|---|---|---|
| `def:polygon` | `SM.polygonData` | SM.Polygon |
| `def:chirotope` | `SM.chirotopeData` | SM.Chirotope |
| `lem:chi-basic` | `SM.chi_basic` | SM.Chirotope |
| `def:generic` | `SM.Generic` | SM.Generic |
| `lem:g1` | `SM.g1` | SM.G1Consequences |
| `def:crossings` | `SM.crossingData` | SM.CrossingEquiv |
| `lem:crossing-test` | `SM.crossing_test` | SM.Crossings |
| `lem:wall-segment-stability` | `SM.wall_segment_stability` | SM.WallSegmentStability |
| `def:chamber` | `SM.chamber_definition` | SM.CyclicChambers |
| `prop:chambers` | `SM.chambers` | SM.ChamberPaths |
| `def:gauss` | `SM.gauss_definition` | SM.GaussDefinition |
| `def:interlace` | `SM.interlacement_definition` | SM.InterlaceDefinition |
| `def:visible` | `SM.visible_signature_definition` | SM.VisibleDefinition |
| `def:weak` | `SM.weak_definition` | SM.WeakGeneric |
| `def:regular` | `SM.regular_definition` | SM.RegularDefinition |
| `def:shift` | `SM.reversal_definition` | SM.Reversal |
| `lem:rot` | `SM.rotation_number` | SM.RotationTheorem |
| `lem:uniformrot` | `SM.uniform_rotation` | SM.UniformRotation |
| `lem:shift` | `SM.shift_reversal` | SM.ShiftTheorem |
| `def:admissible` | `SM.admissible_definition` | SM.Admissible |
| `lem:fibres` | `SM.nonempty_fibres` | SM.Fibres |
| `def:germ` | `SM.wall_germ_definition` | SM.GermDefinition |
| `lem:triple-sides` | `SM.triple_sides` | SM.TripleSides |
| `def:walls` | `SM.named_walls_definition` | SM.NamedWallsDefinition |
| `lem:flat-sides` | `SM.flat_sides` | SM.FlatSides |
| `lem:wall-sides` | `SM.wall_sides` | SM.WallSides |
| `lem:cusp-sides` | `SM.cusp_sides_of_continuous_curve` | SM.CuspCurve |
| `def:deletion-halves` | `SM.deletion_halves_definition` | SM.DeletionHalvesDefinition |
| `lem:children` | `SM.children` | SM.Children |
| `lem:transport-polynomials` | `SM.transport_polynomials` | SM.TransportPolynomials |
| `thm:relgp` | `SM.relative_general_position` | SM.RelativeGeneralPosition |
| `def:root` | `SM.rootData` | SM.RootBoundary |
| `def:gates` | `SM.gatesData` | SM.Gates |
| `lem:gates-nonzero` | `SM.gates_nonzero` | SM.Gates |
| `def:treesum` | `SM.treesumData` | SM.TreeCoefficient |
| `lem:treesum-trees` | `SM.treesum_trees` | SM.PlaneTreeFormal |
| `prop:A-chamber` | `SM.A_chamber` | SM.TreeChamber |
| `def:nearfar` | `SM.nearfarData` | SM.NearFar |
| `lem:farout` | `SM.farout` | SM.Farout |
| `lem:weak-open` | `SM.weak_open` | SM.WeakOpen |

Every accepted row has a review file under work/reviews/ whose `reason` describes the encoding in words.

