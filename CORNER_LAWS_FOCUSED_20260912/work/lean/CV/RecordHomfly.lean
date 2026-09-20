import SM.GaussRecordDefinition
import SM.PolynomialBlock
import CV.Axioms

/-! Ported 2026-09-14 from work/drafts/CV_record_homfly.lean (prover subagent; statements per work/reports/cv-lane-plan-20260913.md §140-§141). Rows CV:def:record (`CV.record_definition`, bundle `CV.RecordDefinitionData`) and CV:def:homfly (`CV.homfly_definition`, bundle `CV.HomflyDefinitionData`). Only this header added. -/

/-! # CV lane, rows 140 and 141 — CV:def:record and CV:def:homfly, on the SM record layer

Source: reference/R/CV/d1_setup.tex, `def:record` (lines 522–551, "record, and record isomorphism")
and `def:homfly` (lines 552–564, "HOMFLY–PT normalization").  Plan entries:
work/reports/cv-lane-plan-20260913.md §140 and §141, gaps G12 and G13.  Written 2026-09-14 by a
Claude Code prover subagent; checked with `lake env lean` (placeholder-free).

Row declarations: `CV.record_definition : CV.RecordDefinitionData` (140) and
`CV.homfly_definition : CV.HomflyDefinitionData` (141).  Each field of a `…DefinitionData`
structure renders one printed clause and is named after it; the SM rendering of the same object is
the accepted row def:gauss-record (`SM.gauss_record_definition`, SM/GaussRecordDefinition.lean),
whose fields are reused wherever CV's sentence is SM's sentence.

## CV:def:record — printed notions and their Lean renderings (namespace `SM.Link`)

* "an oriented circle Γ": the SM `Record` (SM/LinkRecord.lean) carries a finite set `comps` of
  parametrizing circles; CV's record has exactly one, `ρ.componentCount = 1` (`CV.SingleCircle ρ`).
  For "the record of a link diagram" (`Diagram.record`, SM/LinkDiagramRecord.lean) the circle is
  "its traversal circle": `D.record.comps = Fin D.Γ.c`, one circle when `D.componentCount = 1`.
* "a finite subset V ⊂ Γ of marked points": the finite occurrence type `ρ.M` (`Fintype`), read as
  a subset of the oriented circle through the *forward successor* `ρ.succ : Perm ρ.M`: on a single
  circle it is one cycle through all marked points (`∀ v w, ρ.succ.SameCycle v w`).  The cyclic
  order of V on Γ is the orbit order of `succ`; this is SM's design (def:gauss-record "forward
  successor s"), and the G13 equivalence below shows the two carry the same isomorphisms.  On the
  record of a diagram the marked points are "the preimages of its crossings", `D.Γ.Visit` (a
  crossing together with one of its two strands), `succ = nextVisit` (the next occurrence forward
  along the traversal circle), and the cyclic order of Γ is `Diagram.VisitBetween`, oriented
  betweenness of the traversal coordinates `visitCoord` on the circle `[0, k)` (`cycBetween`).
* "a partition of V into two-element sets, the double points": the fixed-point-free involution
  `ρ.pair`; the double points are `ρ.Crossing = {p : Finset ρ.M // ∃ v, p = {v, ρ.pair v}}`, each
  of cardinality two (`Record.Crossing.card_eq_two`), every marked point in exactly one
  (`crossingOf`, `crossingOf_eq_iff`).  On a diagram, "the crossing correspondence":
  `pair = twin` (the other occurrence of the same crossing, `(twin v).1 = v.1`).
* "for each double point a designation of one of its two points as the over position and the
  other as the under position": the bit `ρ.isOver : ρ.M → Bool`, opposite on the two points of a
  double point (`bit_pair : isOver (pair v) = !isOver v`).  On a diagram: set exactly when the
  occurrence's strand is the chosen over strand (`record_isOver_iff`).
* "for each double point a sign in {±1}": `ρ.sgn : ρ.M → SignType`, constant on the two points
  of a double point (`sgn_pair`) and never `0` (`sgn_eq_one_or_neg_one`).  On a diagram: the
  crossing sign `D.sign` (`sgn det(u_O, u_U)`, eq:gauss-cross-sign).
* "A record isomorphism … is a bijection φ : V → V′ that (a) preserves the cyclic order …; (b)
  carries double points to double points; (c) carries over positions to over positions and under
  to under; (d) preserves signs": the SM named record isomorphism `RecordIso ρ ρ'` (a bijection
  `Φ : ρ.M ≃ ρ'.M`, with the component bijection `e`, preserving successor, pairing, bits, signs).
  CV's four clauses are rendered *literally* for a bare bijection `Φ`:
  (a) `CV.PreservesCyclicOrder D D' Φ`: "for all v₁, v₂, v₃ ∈ V occurring in that cyclic order on
      Γ, the points φv₁, φv₂, φv₃ occur in that cyclic order on Γ′" —
      `∀ v w u, D.VisitBetween v w u → D'.VisitBetween (Φ v) (Φ w) (Φ u)` (one direction, as
      printed; for a bijection the converse follows, `CV.visitBetween_iff_of_preservesCyclicOrder`);
  (b) `CV.CarriesDoublePoints Φ`: the image of every double point is a double point,
      `∀ x : ρ.Crossing, ∃ x' : ρ'.Crossing, x.1.map Φ = x'.1` (equivalent to SM's `pair_eq`,
      `CV.carriesDoublePoints_iff`);
  (c) `CV.CarriesOverUnder Φ`: over positions go to over positions and under to under
      (equivalent to SM's `bit_eq`, `CV.carriesOverUnder_iff`);
  (d) `∀ v, ρ'.sgn (Φ v) = ρ.sgn v` (SM's `sgn_eq`).
  Gap G13 (cyclic order ↔ successor): on the records of one-component diagrams, a bijection `Φ`
  satisfies (a)–(d) exactly when it is the occurrence bijection of a `RecordIso`
  (`CV.recordIso_iff`, field `iso_iff`).  Its content is the accepted
  `Diagram.nextVisit_comm_iff_visitBetween_iff` (SM/LinkDiagramRecord.lean §G: successor
  preservation ⇔ preservation of the oriented cyclic order on every component, for every
  component size — with fewer than three marks both are automatic), together with the reduction of
  the printed one-directional (a) to the two-directional form (trichotomy and asymmetry of
  `cycBetween`).  So G13 needs no new cyclic-order machinery: `VisitBetween` is the cyclic order of
  the traversal circle, and the accepted lemma already gives both directions.
* "Condition (a) says exactly that φ extends to an orientation-preserving homeomorphism Γ → Γ′
  carrying V onto V′": rendered as the accepted extension clause of def:gauss-record — every
  record isomorphism of diagram records extends to orientation-preserving (cyclic-order-preserving)
  bijections of the parametrizing circles carrying each occurrence to its image
  (`RecordIso.ExtendsToCircleMaps`, from the stronger accepted `ExtendsPiecewiseAffine`,
  `SM.gauss_record_definition.extension`).  The two remaining sentences of that paragraph — the
  converse direction ("exactly") and "any two such extensions are isotopic through such
  homeomorphisms" (with its proof sketch) — are the printed justification of clause (a), not part
  of the defined notion; the isotopy statement has no rendering in the library (no homotopy theory
  of circle maps is in scope) and is NOT stated.  This is recorded as the one printed sentence of
  the row without a Lean counterpart.
* "Records are isomorphic when such a φ exists; the relation is an equivalence":
  `CV.Isomorphic ρ ρ' := Nonempty (RecordIso ρ ρ')`, `Equivalence CV.Isomorphic`
  (`RecordIso.refl/symm/trans`).
* Domain: CV's records are one-circle records, its diagrams one-component ("connected generic
  immersed circle", d10_axioms.tex:525–531).  The data clauses are stated for one-circle records
  and for the record of every diagram (the multi-component SM statements specialise); the
  isomorphism characterisation (G13) is stated for one-component diagrams, CV's domain — for
  several circles CV's definition has no component bijection, so nothing more is claimed.

## CV:def:homfly — printed notions and their Lean renderings

* "P_H": the HOMFLY–PT polynomial `SM.homfly : Diagram → R` fixed once by `Classical.choose` from
  `SM.lit_homfly`, with `R = ℤ[a^{±1}, z^{±1}]` (`SM.Link.R`, `R.a`, `R.aInv`, `R.z`, `R.zInv`).
  `P_H(L)` for an oriented link `L` is `homfly D` on a diagram `D` presenting it; descent to the
  link is CV:ax:homfly's clause `CV.ax_homfly.descent`.
* "P(○) = 1": value `1` on every one-component crossing-free diagram (`Diagram.IsCrossingFreeCircle`,
  design decision D10) — field `unknot`.
* "aP(L₊) − a⁻¹P(L₋) = zP(L₀)": CV's skein has the SAME sign and variable convention as SM's
  lit:homfly / lp:core (`a P_{D₊} − a⁻¹ P_{D₋} = z P_{D₀}`); rendered on `IsSkeinTriple D₊ D₋ D₀`
  (D₋ the switch of D₊ at a positive crossing, D₀ an oriented smoothing there; design decision D3) —
  field `skein`.
* "P(L ⊔ ○) = (a − a⁻¹)/z · P(L)": `L ⊔ ○` is `IsSplitCircleAddition D D'` (lp:split-circle,
  SM/LinkMoves.lean: `D'` is `D` plus one crossing-free component having no crossings with `D`,
  anywhere in the plane); division by `z` in `R` is multiplication by `R.zInv`, so the right-hand
  side is `(R.a − R.aInv) * R.zInv * homfly D`, which is `R.delta * homfly D` by the definition of
  `R.delta` — field `split_circle`, proved from `SM.split_circle.split` (`P D' = R.delta * P D`) and
  `SM.lp_core.eq_homfly` (`P = homfly`).  Gap G12 (a polygonal kink/RI realisation) is therefore
  NOT needed: the accepted lp:split-circle already carries the identity.
* "P_H is normalized by the first two identities": the two identities pin `P_H` among link
  invariants — every `Q : Diagram → R` depending only on the presented link (`LinkEquiv`-descent),
  with `Q(○) = 1` and the skein, equals `homfly` — field `normalized`, which is the uniqueness
  clause of CV:ax:homfly (`CV.ax_homfly.unique`, proved through lp:coefficient-transport).
* "the third is their consequence, obtained by applying the skein relation at a crossing between
  L and a split unknot, and is displayed because it fixes the reader's convention for a split
  component": rendered as the theorem that every such normalised invariant `Q` satisfies the
  split-circle identity — field `split_circle_consequence`.  The printed derivation route (skein
  at a kink; needs an RI realisation) is replaced by the library's: `Q = homfly` by `normalized`,
  then `split_circle`.  What is proved is exactly the printed claim (the third identity follows
  from the first two for the normalised invariant); the route is not part of the claim. -/

namespace CV

open SM SM.Link

/-! ## Row 140 — CV:def:record (d1_setup.tex:522–551) -/

/-- CV's record has a single oriented circle Γ: an SM record with exactly one parametrizing
circle. -/
def SingleCircle (ρ : Record) : Prop := ρ.componentCount = 1

theorem SingleCircle.subsingleton_comps {ρ : Record} (h : SingleCircle ρ) : Subsingleton ρ.comps :=
  Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h)

/-- On a single circle the forward successor is one cycle through all marked points ("a finite
subset V ⊂ Γ" of an oriented circle: the cyclic order of V is the orbit order of `succ`). -/
theorem SingleCircle.sameCycle {ρ : Record} (h : SingleCircle ρ) (v w : ρ.M) :
    ρ.succ.SameCycle v w :=
  haveI := h.subsingleton_comps
  ρ.succ_cycle v w (Subsingleton.elim _ _)

/-- Every marked point lies in exactly one double point ("a partition of V into two-element
sets"). -/
theorem exists_unique_crossing (ρ : Record) (v : ρ.M) : ∃! x : ρ.Crossing, v ∈ x.1 :=
  ⟨ρ.crossingOf v, ρ.mem_crossingOf v, fun x hx => ((ρ.crossingOf_eq_iff v x).2 hx).symm⟩

/-- The record of a one-component diagram has a single circle, "its traversal circle". -/
theorem singleCircle_record {D : Diagram} (hD : D.componentCount = 1) : SingleCircle D.record := by
  unfold SingleCircle
  rw [D.record_componentCount]
  exact hD

/-! ### The four clauses (a)–(d) of a record isomorphism, as printed -/

/-- Clause (a), on the records of diagrams, where the oriented circle is the traversal circle and
its cyclic order is `Diagram.VisitBetween`: "for all v₁, v₂, v₃ ∈ V occurring in that cyclic order on
Γ, the points φv₁, φv₂, φv₃ occur in that cyclic order on Γ′". -/
def PreservesCyclicOrder (D D' : Diagram) (Φ : D.Γ.Visit ≃ D'.Γ.Visit) : Prop :=
  ∀ v w u, D.VisitBetween v w u → D'.VisitBetween (Φ v) (Φ w) (Φ u)

/-- Clause (b): "carries double points to double points" — the image of every double point
`{v, pair v}` of `ρ` is a double point of `ρ'`. -/
def CarriesDoublePoints {ρ ρ' : Record} (Φ : ρ.M ≃ ρ'.M) : Prop :=
  ∀ x : ρ.Crossing, ∃ x' : ρ'.Crossing, x.1.map Φ.toEmbedding = x'.1

/-- Clause (c): "carries over positions to over positions and under to under". -/
def CarriesOverUnder {ρ ρ' : Record} (Φ : ρ.M ≃ ρ'.M) : Prop :=
  (∀ v, ρ.isOver v = true → ρ'.isOver (Φ v) = true) ∧
  (∀ v, ρ.isOver v = false → ρ'.isOver (Φ v) = false)

/-- The image of the double point through `v` is `{Φ v, Φ (pair v)}`. -/
theorem crossingOf_map {ρ ρ' : Record} (Φ : ρ.M ≃ ρ'.M) (v : ρ.M) :
    (ρ.crossingOf v).1.map Φ.toEmbedding = {Φ v, Φ (ρ.pair v)} := by
  simp [Record.crossingOf, Finset.map_insert]

/-- Clause (b) is SM's `pair_eq`: a bijection carries double points to double points exactly when it
commutes with the pairing involutions. -/
theorem carriesDoublePoints_iff {ρ ρ' : Record} (Φ : ρ.M ≃ ρ'.M) :
    CarriesDoublePoints Φ ↔ ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v) := by
  constructor
  · intro h v
    obtain ⟨x', hx'⟩ := h (ρ.crossingOf v)
    rw [crossingOf_map] at hx'
    obtain ⟨p, w, hp⟩ := x'
    simp only at hx'
    subst hp
    have h1 : Φ v ∈ ({w, ρ'.pair w} : Finset ρ'.M) := by rw [← hx']; simp
    have h2 : Φ (ρ.pair v) ∈ ({w, ρ'.pair w} : Finset ρ'.M) := by rw [← hx']; simp
    have hne : Φ (ρ.pair v) ≠ Φ v := fun h => ρ.pair_ne v (Φ.injective h)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd (h2.trans h1.symm) hne
      · rw [h2, h1]
    · rcases h2 with h2 | h2
      · rw [h2, h1, ρ'.pair_invol]
      · exact absurd (h2.trans h1.symm) hne
  · intro h x
    obtain ⟨p, v, rfl⟩ := x
    refine ⟨ρ'.crossingOf (Φ v), ?_⟩
    change ({v, ρ.pair v} : Finset ρ.M).map Φ.toEmbedding = {Φ v, ρ'.pair (Φ v)}
    rw [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding, h v]

/-- Clause (c) is SM's `bit_eq`. -/
theorem carriesOverUnder_iff {ρ ρ' : Record} (Φ : ρ.M ≃ ρ'.M) :
    CarriesOverUnder Φ ↔ ∀ v, ρ'.isOver (Φ v) = ρ.isOver v := by
  constructor
  · rintro ⟨h1, h2⟩ v
    cases hv : ρ.isOver v
    · exact h2 v hv
    · exact h1 v hv
  · intro h
    exact ⟨fun v hv => by rw [h, hv], fun v hv => by rw [h, hv]⟩

/-! ### Reduction of the printed one-directional clause (a) to the two-directional form -/

/-- Oriented betweenness of three distinct reals on the circle is total: `b` lies before `c` going
forward from `a`, or `c` before `b`. -/
theorem cycBetween_total {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cycBetween a b c ∨ cycBetween a c b := by
  unfold cycBetween
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  all_goals first
    | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-- Oriented betweenness is asymmetric in its last two arguments. -/
theorem cycBetween_asymm {a b c : ℝ} (h : cycBetween a b c) : ¬ cycBetween a c b := by
  unfold cycBetween at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rintro (⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩) <;> linarith

/-- The three points of an oriented betweenness are pairwise distinct. -/
theorem cycBetween_ne {a b c : ℝ} (h : cycBetween a b c) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  unfold cycBetween at h
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-- The one-component `hcomp` hypothesis of SM's §G lemmas is automatic: all occurrences of a
one-component diagram lie on its one circle. -/
theorem compOf_eq_of_single {D : Diagram} (hD : D.componentCount = 1) (v w : D.Γ.Visit) :
    D.compOf v = D.compOf w :=
  haveI : Subsingleton (Fin D.Γ.c) := Fin.subsingleton_iff_le_one.mpr (le_of_eq hD)
  Subsingleton.elim _ _

/-- For a bijection of the occurrences of two one-component diagrams, the printed one-directional
clause (a) already gives the two-directional form: distinct occurrences of one circle have distinct
coordinates, oriented betweenness is total and asymmetric. -/
theorem visitBetween_iff_of_preservesCyclicOrder {D D' : Diagram} (hD : D.componentCount = 1)
    (Φ : D.Γ.Visit ≃ D'.Γ.Visit) (h : PreservesCyclicOrder D D' Φ) (v w u : D.Γ.Visit) :
    D'.VisitBetween (Φ v) (Φ w) (Φ u) ↔ D.VisitBetween v w u := by
  refine ⟨fun h' => ?_, h v w u⟩
  obtain ⟨h1, h2, h3⟩ := cycBetween_ne h'
  have hvw : D.visitCoord v ≠ D.visitCoord w := fun heq =>
    h1 (by rw [D.visitCoord_injOn (compOf_eq_of_single hD v w) heq])
  have hvu : D.visitCoord v ≠ D.visitCoord u := fun heq =>
    h2 (by rw [D.visitCoord_injOn (compOf_eq_of_single hD v u) heq])
  have hwu : D.visitCoord w ≠ D.visitCoord u := fun heq =>
    h3 (by rw [D.visitCoord_injOn (compOf_eq_of_single hD w u) heq])
  rcases cycBetween_total hvw hvu hwu with hb | hb
  · exact hb
  · exact absurd (h v u w hb) (cycBetween_asymm h')

/-! ### The record isomorphisms of CV are the named record isomorphisms of SM (Gap G13) -/

/-- CV's clauses (a)–(d) for a bijection `Φ` of the marked points of two diagram records. -/
structure IsRecordIsoData (D D' : Diagram) (Φ : D.Γ.Visit ≃ D'.Γ.Visit) : Prop where
  /-- "(a) preserves the cyclic order" -/
  cyclic_order : PreservesCyclicOrder D D' Φ
  /-- "(b) carries double points to double points" -/
  double_points : CarriesDoublePoints (ρ := D.record) (ρ' := D'.record) Φ
  /-- "(c) carries over positions to over positions and under to under" -/
  over_under : CarriesOverUnder (ρ := D.record) (ρ' := D'.record) Φ
  /-- "(d) preserves signs" -/
  signs : ∀ v, D'.record.sgn (Φ v) = D.record.sgn v

/-- The occurrence bijection of a named record isomorphism between the records of two one-component
diagrams satisfies (a)–(d): (a) is the accepted `RecordIso.visitBetween_iff`, (b)–(d) are
`pair_eq`, `bit_eq`, `sgn_eq`. -/
theorem isRecordIsoData_of_recordIso {D D' : Diagram} (hD : D.componentCount = 1)
    (ι : RecordIso D.record D'.record) : IsRecordIsoData D D' ι.Φ where
  cyclic_order v w u hb :=
    (ι.visitBetween_iff v w u (compOf_eq_of_single hD w v) (compOf_eq_of_single hD u v)).2 hb
  double_points := (carriesDoublePoints_iff ι.Φ).2 ι.pair_eq
  over_under := (carriesOverUnder_iff ι.Φ).2 ι.bit_eq
  signs := ι.sgn_eq

/-- A bijection of the occurrences of two one-component diagrams satisfying (a)–(d) is the occurrence
bijection of a named record isomorphism: the component bijection is the unique one between the two
single circles, and the successor clause is the accepted
`Diagram.nextVisit_comm_of_visitBetween_iff` (§G: cyclic-order preservation gives successor
preservation on every component). -/
noncomputable def recordIsoOfData {D D' : Diagram} (hD : D.componentCount = 1)
    (hD' : D'.componentCount = 1) (Φ : D.Γ.Visit ≃ D'.Γ.Visit) (h : IsRecordIsoData D D' Φ) :
    RecordIso D.record D'.record where
  e := finCongr (show D.Γ.c = D'.Γ.c from hD.trans hD'.symm)
  Φ := Φ
  comp_eq _ :=
    haveI : Subsingleton (Fin D'.Γ.c) := Fin.subsingleton_iff_le_one.mpr (le_of_eq hD')
    Subsingleton.elim _ _
  succ_eq v :=
    Diagram.nextVisit_comm_of_visitBetween_iff D Φ
      (fun _ _ => iff_of_true (compOf_eq_of_single hD' _ _) (compOf_eq_of_single hD _ _))
      (fun v w u _ _ => visitBetween_iff_of_preservesCyclicOrder hD Φ h.cyclic_order v w u) v
  pair_eq := (carriesDoublePoints_iff (ρ := D.record) (ρ' := D'.record) Φ).1 h.double_points
  bit_eq := (carriesOverUnder_iff (ρ := D.record) (ρ' := D'.record) Φ).1 h.over_under
  sgn_eq := h.signs

@[simp] theorem recordIsoOfData_Φ {D D' : Diagram} (hD : D.componentCount = 1)
    (hD' : D'.componentCount = 1) (Φ : D.Γ.Visit ≃ D'.Γ.Visit) (h : IsRecordIsoData D D' Φ) :
    (recordIsoOfData hD hD' Φ h).Φ = Φ := rfl

/-- **Gap G13 closed on CV's domain.**  For one-component diagrams `D`, `D'`, a bijection `Φ` of the
marked points satisfies CV's clauses (a)–(d) exactly when it is the occurrence bijection of a named
record isomorphism `RecordIso D.record D'.record` of SM. -/
theorem recordIso_iff {D D' : Diagram} (hD : D.componentCount = 1) (hD' : D'.componentCount = 1)
    (Φ : D.Γ.Visit ≃ D'.Γ.Visit) :
    IsRecordIsoData D D' Φ ↔ ∃ ι : RecordIso D.record D'.record, ι.Φ = Φ :=
  ⟨fun h => ⟨recordIsoOfData hD hD' Φ h, rfl⟩,
   fun ⟨ι, hι⟩ => hι ▸ isRecordIsoData_of_recordIso hD ι⟩

/-! ### Isomorphic records -/

/-- "Records are isomorphic when such a φ exists." -/
def Isomorphic (ρ ρ' : Record) : Prop := Nonempty (RecordIso ρ ρ')

/-- "the relation is an equivalence." -/
theorem isomorphic_equivalence : Equivalence Isomorphic where
  refl ρ := ⟨RecordIso.refl ρ⟩
  symm := fun ⟨i⟩ => ⟨i.symm⟩
  trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩

/-! ### The row bundle -/

/-- CV:def:record (d1_setup.tex:522–551) as printed, on the SM record layer; one field per printed
clause, see the module docstring for every reading. -/
structure RecordDefinitionData : Prop where
  /-- "A record consists of an oriented circle Γ; a finite subset V ⊂ Γ of marked points; a
  partition of V into two-element sets, the double points; for each double point a designation of
  one of its two points as the over position and the other as the under position; and for each
  double point a sign in {±1}."  On a single-circle record: the marked points are finite; the
  forward successor is one cycle through all of them (V sits on the one oriented circle); every
  double point has two points and every marked point lies in exactly one double point; the two
  points of a double point carry opposite over/under designations; the sign is a property of the
  double point and lies in {±1}. -/
  record : ∀ ρ : Record, SingleCircle ρ →
    Finite ρ.M ∧ (∀ v w, ρ.succ.SameCycle v w) ∧
    (∀ x : ρ.Crossing, x.1.card = 2) ∧ (∀ v, ∃! x : ρ.Crossing, v ∈ x.1) ∧
    (∀ v, ρ.isOver (ρ.pair v) = !ρ.isOver v) ∧
    (∀ v, ρ.sgn (ρ.pair v) = ρ.sgn v ∧ (ρ.sgn v = 1 ∨ ρ.sgn v = -1))
  /-- "The record of a link diagram is the one obtained by taking Γ to be its traversal circle, V
  the preimages of its crossings, the partition the crossing correspondence, and the over/under and
  sign data those of the diagram": the record of a one-component diagram has a single circle; its
  marked points are the crossing occurrences (a crossing with one of its two strands); the successor
  is the next occurrence forward along the traversal circle (nothing of the circle lies strictly
  between an occurrence and its successor); the pairing is the other occurrence of the same
  crossing; the over bit is set exactly when the occurrence's strand is the over strand; the sign is
  the diagram's crossing sign. -/
  diagram_record : ∀ D : Diagram,
    (D.componentCount = 1 → SingleCircle D.record) ∧
    D.record.M = D.Γ.Visit ∧
    (∀ v, D.record.succ v = D.nextVisit v ∧
      ∀ u, D.compOf u = D.compOf v → ¬ D.VisitBetween v u (D.record.succ v)) ∧
    (∀ v, D.record.pair v = D.twin v ∧ (D.record.pair v).1 = v.1) ∧
    (∀ v, D.record.isOver v = true ↔ v.2.val = D.overStrand v.1) ∧
    (∀ v, D.record.sgn v = D.sign v.1)
  /-- "A record isomorphism … is a bijection φ : V → V′ that … (b) carries double points to double
  points; (c) carries over positions to over positions and under to under; (d) preserves signs":
  every named record isomorphism `RecordIso ρ ρ'` of SM is such a bijection, and it preserves the
  successor (SM's form of clause (a)). -/
  iso : ∀ (ρ ρ' : Record) (ι : RecordIso ρ ρ'),
    Function.Bijective ι.Φ ∧ CarriesDoublePoints ι.Φ ∧ CarriesOverUnder ι.Φ ∧
    (∀ v, ρ'.sgn (ι.Φ v) = ρ.sgn v) ∧ (∀ v, ι.Φ (ρ.succ v) = ρ'.succ (ι.Φ v))
  /-- "(a) preserves the cyclic order: for all v₁, v₂, v₃ ∈ V occurring in that cyclic order on Γ,
  the points φv₁, φv₂, φv₃ occur in that cyclic order on Γ′" — with (b), (c), (d): on the records of
  one-component diagrams a bijection of the marked points satisfies (a)–(d) exactly when it is the
  occurrence bijection of a named record isomorphism (Gap G13: cyclic order ↔ successor). -/
  iso_iff : ∀ (D D' : Diagram), D.componentCount = 1 → D'.componentCount = 1 →
    ∀ Φ : D.Γ.Visit ≃ D'.Γ.Visit,
      IsRecordIsoData D D' Φ ↔ ∃ ι : RecordIso D.record D'.record, ι.Φ = Φ
  /-- "Condition (a) says exactly that φ extends to an orientation-preserving homeomorphism Γ → Γ′
  carrying V onto V′": every record isomorphism of diagram records extends to orientation-preserving
  bijections of the traversal circles carrying each marked point to its image (the accepted
  extension clause of def:gauss-record; the isotopy sentence is not rendered, see the docstring). -/
  extension : ∀ (D D' : Diagram) (ι : RecordIso D.record D'.record), ι.ExtendsToCircleMaps
  /-- "Records are isomorphic when such a φ exists; the relation is an equivalence." -/
  equivalence : Equivalence Isomorphic

/-- **CV:def:record** (d1_setup.tex:522–551): the CV record notions on the SM record layer.  The
data clauses are the accepted def:gauss-record fields (`SM.gauss_record_definition`); the
isomorphism characterisation is `CV.recordIso_iff` (accepted §G of SM/LinkDiagramRecord.lean plus
the trichotomy reduction); the extension is the accepted piecewise-affine extension; the equivalence
is `RecordIso.refl/symm/trans`. -/
theorem record_definition : RecordDefinitionData where
  record := fun ρ h =>
    ⟨inferInstance, h.sameCycle, Record.Crossing.card_eq_two ρ, exists_unique_crossing ρ,
     ρ.bit_pair, fun v => ⟨ρ.sgn_pair v, ρ.sgn_eq_one_or_neg_one v⟩⟩
  diagram_record := fun D =>
    ⟨singleCircle_record, (gauss_record_definition.occurrences D).1,
     fun v => ⟨(gauss_record_definition.successor D v).1,
       fun u hu => (gauss_record_definition.successor D v).2.2 u hu⟩,
     fun v => ⟨(gauss_record_definition.pairing D v).1, (gauss_record_definition.pairing D v).2.1⟩,
     fun v => (gauss_record_definition.bits D v).1,
     fun v => D.record_sgn v⟩
  iso := fun _ _ ι =>
    ⟨ι.Φ.bijective, (carriesDoublePoints_iff ι.Φ).2 ι.pair_eq,
     (carriesOverUnder_iff ι.Φ).2 ι.bit_eq, ι.sgn_eq, ι.succ_eq⟩
  iso_iff := fun _ _ hD hD' Φ => recordIso_iff hD hD' Φ
  extension := fun D D' ι => (gauss_record_definition.extension D D' ι).toExtendsToCircleMaps
  equivalence := isomorphic_equivalence

/-! ## Row 141 — CV:def:homfly (d1_setup.tex:552–564) -/

/-- CV:def:homfly (d1_setup.tex:552–564) as printed, for the HOMFLY–PT polynomial
`homfly : Diagram → R` of lit:homfly; one field per printed clause, see the module docstring. -/
structure HomflyDefinitionData : Prop where
  /-- "P(○) = 1". -/
  unknot : ∀ D : Diagram, D.IsCrossingFreeCircle → homfly D = 1
  /-- "aP(L₊) − a⁻¹P(L₋) = zP(L₀)" — the same sign and variable convention as SM's lit:homfly. -/
  skein : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
    R.a * homfly Dp - R.aInv * homfly Dm = R.z * homfly D0
  /-- "P(L ⊔ ○) = (a − a⁻¹)/z · P(L)": adding a split crossing-free circle multiplies by
  `(a − a⁻¹) z⁻¹` (`= R.delta`). -/
  split_circle : ∀ D D' : Diagram, IsSplitCircleAddition D D' →
    homfly D' = (R.a - R.aInv) * R.zInv * homfly D
  /-- "P_H is normalized by the first two identities": they pin `P_H` among link invariants — every
  `Q : Diagram → R` depending only on the presented link, with `Q(○) = 1` and the skein, is
  `homfly` (CV:ax:homfly's uniqueness clause). -/
  normalized : ∀ Q : Diagram → R,
    (∀ D D' : Diagram, LinkEquiv D D' → Q D = Q D') →
    (∀ D : Diagram, D.IsCrossingFreeCircle → Q D = 1) →
    (∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
      R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0) →
    Q = homfly
  /-- "the third is their consequence": every link invariant normalised by the first two identities
  satisfies the third. -/
  split_circle_consequence : ∀ Q : Diagram → R,
    (∀ D D' : Diagram, LinkEquiv D D' → Q D = Q D') →
    (∀ D : Diagram, D.IsCrossingFreeCircle → Q D = 1) →
    (∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
      R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0) →
    ∀ D D' : Diagram, IsSplitCircleAddition D D' → Q D' = (R.a - R.aInv) * R.zInv * Q D

/-- The split-circle identity for `homfly`: lp:split-circle (`SM.split_circle.split`,
`P D' = δ P D`) transported along lp:core's `P = homfly`, with `δ = (a − a⁻¹) z⁻¹` unfolded. -/
theorem homfly_split_circle {D D' : Diagram} (h : IsSplitCircleAddition D D') :
    homfly D' = (R.a - R.aInv) * R.zInv * homfly D := by
  have hs := SM.split_circle.split D D' h
  rw [SM.lp_core.eq_homfly D, SM.lp_core.eq_homfly D'] at hs
  rw [hs]
  rfl

/-- **CV:def:homfly** (d1_setup.tex:552–564).  The two normalising identities are CV:ax:homfly's
`unknot` and `skein` (lit:homfly for `homfly`); "normalized by" is its `unique`; the split-circle
display is lp:split-circle transported along `P = homfly` (`homfly_split_circle`), and "the third is
their consequence" follows for every normalised invariant by `unique` then `homfly_split_circle`.
No kink/RI realisation (Gap G12) is used. -/
theorem homfly_definition : HomflyDefinitionData where
  unknot := ax_homfly.unknot
  skein := ax_homfly.skein
  split_circle := fun _ _ h => homfly_split_circle h
  normalized := ax_homfly.unique
  split_circle_consequence := fun Q hdesc hunknot hskein D D' h => by
    rw [ax_homfly.unique Q hdesc hunknot hskein]
    exact homfly_split_circle h

end CV

