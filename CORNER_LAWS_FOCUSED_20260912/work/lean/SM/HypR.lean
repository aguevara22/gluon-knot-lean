-- Ported 15:19Z 2026-09-14 from work/drafts/hypr/HypR.lean Parts 1-2 (hyp:R architect unit) by the pod executor; body verbatim; Part 3 (the consumer check against the Bridge lane) is Bridge/SmR.lean.
import SM.CornerStateSum
import SM.NamedWallPredicates
import SM.WallCenterKinds
import SM.GermSides
import SM.CChamber

/-! # Row hyp:R — SM's Hypothesis R, the Prop `SM.hyp_R` (draft, work/drafts/hypr/HypR.lean)

Source hyp:R (reference/SM/sm-4-knotlaws.tex:1149-1151, frame SM15; blueprint/EXTRACTS.json segment
1149-1151, action HYPOTHESIS):

> `\begin{hypothesis}[R]\label{hyp:R}`
> `At every simple triple wall, $C(P_+)=C(P_-)$. \status{hyp}`
> `\end{hypothesis}`

This row is a `\status{hyp}` row: the DEFINITION of a proposition, not a claim (blueprint/NODES.tsv:119,
action HYPOTHESIS; tools/claims.py puts HYPOTHESIS in its SKIP set). Its checker-fixed name is `SM.hyp_R`
(work/lean/axiom-policy.json `"hypothesis": {"declaration": "SM.hyp_R", "label": "hyp:R", "mode":
"explicit_parameter"}`; tools/check_lean.py:104 and tools/bootstrap.py:33 hard-code `{'hyp:R': 'SM.hyp_R'}`).
Nothing here is an axiom: consumers take `SM.hyp_R` as an explicit hypothesis (thm:comparison), and the
Bridge lane's row Bridge:theorem (`Bridge.sm_R : SM.hyp_R`, BRIDGE.md §3 (19)-(21)) will PROVE it from
`RProof.cv_R : CV.hyp_R` once that R-lane row lands; the consumer chain is checked below.

## Notation (every notion of the printed sentence, with its accepted row)

* "wall" / "simple ... wall" — def:germ (sm-1-polygons.tex:680-695, accepted row `SM.wall_germ_definition`,
  SM/GermDefinition.lean): a wall germ is `g : WallGerm n` (SM/WallGerm.lean: `radius > 0`, a continuous
  `curve : Ioo (-radius) radius → LabelledTuple n`, generic off the centre, not generic at the centre).
  def:walls (sm-1:737-777, accepted row `SM.named_walls_definition`, SM/NamedWallsDefinition.lean): "A wall germ
  is *simple of one of the following types*"; type (T) "*Triple at {e,f,g}*: `Z_pt = ∅`, `Z_c = {{e,f,g}}`, and on
  each of the three edges the two crossing parameters of the other two edges (which exist on both sides by
  lem:triple-sides) have a difference that changes sign at 0" (sm-1:762-766).
* "simple triple wall" — `g.TripleAt e f k` (SM/NamedWallPredicates.lean:30-34, the (T) predicate consumed by
  the accepted lem:wall-sides `SM.wall_sides`, thm:uniqueness (d) `SM.uniqueness`, cor:A-lawful `triple_law`,
  and Bridge:B1-B4): `g.pointZeros = ∅ ∧ g.concurrences = {{e, f, k}} ∧` the three `SignChanges` of
  `edgeParameter P e f - edgeParameter P e k` etc. The triple is the unordered set `{e, f, k}` and `TripleAt`
  is invariant under permuting it (`WallGerm.tripleAt_support_iff`, SM/UnorderedWallTriples.lean); "simple
  of type (T)" is `g.HasWallKind .triple = ∃ e f k, g.TripleAt e f k` (SM/WallCenterKinds.lean:56), see
  `hyp_R_iff_hasWallKind`.
* "the sides `P₋`, `P₊`" — def:germ: "Its *sides* `P₋` and `P₊` are the chambers containing `P((−ε,0))` and
  `P((0,ε))`; each of these two sets is connected and generic, hence lies in one chamber. For a function `F`
  that is constant on chambers, `F(P_±)` denotes its value on the respective side." Rendered exactly as in the
  accepted C-rows prop:C-silent (`SM.prop_C_silent`, the same printed phrase "`C(P₊) = C(P₋)`", SM/CSilent.lean),
  thm:uniqueness (d) and cor:A-lawful `triple_law`: the generic polygons of the two sides are
  `g.sideTuple true tp` (parameter `+tp`) and `g.sideTuple false tm` (parameter `−tm`) for side parameters
  `tp, tm : g.SideParameter = Ioo 0 g.radius`, and the equation is read at every pair of side points. Each side
  image lies in one chamber (`WallGerm.sidePolygon_mem_side`, SM/GermSides.lean) on which `C` is constant by the
  accepted prop:C-chamber (`SM.prop_C_chamber`), so this all-sides point-value form is equivalent to the printed
  chamber-value equality (`hyp_R_iff_base`, `hyp_R_iff_diagonal` below), exactly as CV:ax:R's R6 form
  (`CV.hyp_R`, work/reviews/cv-ax-R.json) is equivalent to CV's chamber values under prop:chamberinv (ii).
* "`C`" — def:C (sm-3-statesum.tex:1688-1700, accepted row `SM.corner_state_sum_definition`): the corner state
  sum `cornerStateSum hn hP : ℤ` (SM/CornerStateSum.lean:166) of a generic labelled polygon `P` with
  `hn : 3 ≤ n`, `hP : Generic P`, `[NeZero n]`.
* Presupposition binders (labelled, not printed clauses; the same as prop:C-silent's): `[NeZero n]` (ZMod
  indexing of `TripleAt` and `cornerStateSum`), `hn : 3 ≤ n` (needed by `cornerStateSum`; nothing printed is
  lost — a pairwise remote triple of edges needs `n ≥ 6`).

## Relation to the Bridge lane's consumption

`RProof.smR_shape_of_hyp_R` (work/lean/RProof/X1Rows.lean:2982) concludes the DIAGONAL form
`∀ ... g.TripleAt e f k → ∀ t : g.SideParameter, C (g.sideTuple true t) = C (g.sideTuple false t)`, i.e.
`SM.HypRDiagonal` below (`smR_shape_conclusion_is_diagonal` type-checks by `rfl`). `SM.hyp_R` is its
two-parameter strengthening; the two are equivalent (`hyp_R_iff_diagonal`, via prop:C-chamber), and CV's R6
form yields `SM.hyp_R` directly with independent `tp, tm` (`hyp_R_of_cv_hyp_R`, the same proof as
`smR_shape_of_hyp_R`), so `sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` is PROVED from accepted rows and
`Bridge.sm_R := sm_R_of_cv_R RProof.cv_R` is the one-line row Bridge:theorem once `RProof.cv_R` exists.

Checked with `cd work/lean && lake env lean ../drafts/hypr/HypR.lean` (no sorry). -/

namespace SM
/-! ## Part 1 — the definition (intended home: work/lean/SM/HypR.lean, imports SM.CornerStateSum,
SM.NamedWallPredicates only) -/

/-- **Hypothesis R (row hyp:R, `SM.hyp_R`)**, the printed sentence sm-4-knotlaws.tex:1150 "At every simple
triple wall, `C(P₊) = C(P₋)`" as a proposition: for every wall germ `g` on `n ≥ 3` vertices that is simple of
type (T) at a triple `{e, f, k}` (def:walls (T), `g.TripleAt e f k`), the corner state sums (def:C,
`cornerStateSum`) of the generic polygons on its two sides (def:germ; `g.sideTuple true tp` at parameter
`+tp`, `g.sideTuple false tm` at parameter `−tm`) agree, for all side parameters `tp, tm ∈ (0, radius)` — the
same rendering of "`C(P₊) = C(P₋)`" as the accepted prop:C-silent (`SM.prop_C_silent`). This is a
`\status{hyp}` row: a definition of a `Prop`, not a claim; it is proved by the Bridge lane (`Bridge.sm_R`)
from `RProof.cv_R : CV.hyp_R`. -/
def hyp_R : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k →
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property =
        cornerStateSum hn (g.sideTuple false tm).property

/-- `hyp_R` unfolds to the expected `∀`-statement (sanity, `Iff.rfl`). -/
theorem hyp_R_iff :
    hyp_R ↔
      ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k →
        ∀ tp tm : g.SideParameter,
          cornerStateSum hn (g.sideTuple true tp).property =
            cornerStateSum hn (g.sideTuple false tm).property :=
  Iff.rfl

/-- "At every simple triple wall" = at every wall germ that is simple of type (T) (def:walls; the kind
predicate `HasWallKind .triple = ∃ e f k, TripleAt e f k` of SM/WallCenterKinds.lean). -/
theorem hyp_R_iff_hasWallKind :
    hyp_R ↔
      ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n), g.HasWallKind .triple →
        ∀ tp tm : g.SideParameter,
          cornerStateSum hn (g.sideTuple true tp).property =
            cornerStateSum hn (g.sideTuple false tm).property := by
  constructor
  · intro h n _ hn g hg tp tm
    obtain ⟨e, f, k, hT⟩ := hg
    exact h n hn g e f k hT tp tm
  · intro h n _ hn g e f k hT tp tm
    exact h n hn g ⟨e, f, k, hT⟩ tp tm

/-! ## Part 2 — the side value is a chamber value (needs the accepted prop:C-chamber and def:germ's sides;
intended home: the same module or SM/HypRSides.lean) -/

/-- The corner state sum is constant along one punctured side of a wall germ: the side image lies in one
chamber (`WallGerm.sidePolygon_mem_side`, def:germ) on which `C` is constant (`SM.prop_C_chamber`, accepted).
(The same fact as `Bridge.cornerStateSum_sideTuple_eq_base`, stated for two arbitrary side parameters.) -/
theorem cornerStateSum_side_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (b : Bool)
    (t t' : g.SideParameter) :
    cornerStateSum hn (g.sideTuple b t).property = cornerStateSum hn (g.sideTuple b t').property :=
  calc cornerStateSum hn (g.sideTuple b t).property
      = cornerStateSum hn (g.sideTuple b g.sideBase).property :=
        (prop_C_chamber.constant n hn (g.sideTuple b g.sideBase) (g.sideTuple b t)
          (g.sidePolygon_mem_side b t)).symm
    _ = cornerStateSum hn (g.sideTuple b t').property :=
        prop_C_chamber.constant n hn (g.sideTuple b g.sideBase) (g.sideTuple b t')
          (g.sidePolygon_mem_side b t')

/-- The diagonal (one side parameter for both sides) form of Hypothesis R — literally the conclusion of
`RProof.smR_shape_of_hyp_R` (work/lean/RProof/X1Rows.lean:2982-2986). -/
def HypRDiagonal : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k →
    ∀ t : g.SideParameter,
      cornerStateSum hn (g.sideTuple true t).2 = cornerStateSum hn (g.sideTuple false t).2

/-- The chamber-value form: `C` at the base point `radius/2` of each side, i.e. the value of `C` on the side
chambers `g.side true`, `g.side false` of def:germ (`WallGerm.side b = chamber (g.sidePolygon b g.sideBase)`,
SM/GermSides.lean). -/
def HypRBase : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k →
    cornerStateSum hn (g.sideTuple true g.sideBase).property =
      cornerStateSum hn (g.sideTuple false g.sideBase).property

theorem hypRDiagonal_of_hyp_R (h : hyp_R) : HypRDiagonal :=
  fun n _ hn g e f k hT t => h n hn g e f k hT t t

theorem hypRBase_of_hypRDiagonal (h : HypRDiagonal) : HypRBase :=
  fun n _ hn g e f k hT => h n hn g e f k hT g.sideBase

/-- The chamber-value form gives the all-sides form (prop:C-chamber along each side). -/
theorem hyp_R_of_hypRBase (h : HypRBase) : hyp_R := by
  intro n _ hn g e f k hT tp tm
  calc cornerStateSum hn (g.sideTuple true tp).property
      = cornerStateSum hn (g.sideTuple true g.sideBase).property :=
        cornerStateSum_side_eq hn g true tp g.sideBase
    _ = cornerStateSum hn (g.sideTuple false g.sideBase).property := h n hn g e f k hT
    _ = cornerStateSum hn (g.sideTuple false tm).property :=
        cornerStateSum_side_eq hn g false g.sideBase tm

/-- FR-HR-1: the three readings of "`C(P₊) = C(P₋)`" — all side points (`hyp_R`, the accepted C-row
convention), one common parameter (`HypRDiagonal`, the Bridge consumer's shape), the chamber values
(`HypRBase`, def:germ's `F(P_±)`) — are equivalent under the accepted prop:C-chamber. -/
theorem hyp_R_iff_diagonal : hyp_R ↔ HypRDiagonal :=
  ⟨hypRDiagonal_of_hyp_R, fun h => hyp_R_of_hypRBase (hypRBase_of_hypRDiagonal h)⟩

theorem hyp_R_iff_base : hyp_R ↔ HypRBase :=
  ⟨fun h => hypRBase_of_hypRDiagonal (hypRDiagonal_of_hyp_R h), hyp_R_of_hypRBase⟩

end SM
