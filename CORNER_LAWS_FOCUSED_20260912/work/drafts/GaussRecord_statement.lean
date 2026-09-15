import SM.LinkDiagramRecord

/-! Source def:gauss-record (reference/SM/sm-3-statesum.tex:352, frame SM15): the crossing record of a
diagram and named record isomorphisms. Main declaration: `SM.gauss_record_definition`. STATEMENT
DRAFT: the field `extension` (the piecewise-linear circle map extending `Φ`) awaits its proof.

Notation (Chapter-3 layer, modules SM/LinkDiagram, SM/LinkRecord, SM/LinkDiagramRecord, namespace
`SM.Link`). The printed setting is one oriented circle `C` mapped by a generic immersion `γ` into the
oriented sphere with over/under choices at its transverse double points; the Lean setting is an
oriented link diagram `D : Diagram` (def:positive-lift) whose parametrizing circles are the
components' traversal circles (`D.Γ.Pt`, traversal points with the accepted `traversalKey`
coordinate), read one circle at a time (`D.compOf v` is the circle carrying an occurrence). The
crossing-occurrence set `M` is `D.Γ.Visit` (a crossing together with one of its two strands); the
record `D.record : Record` carries the forward successor `succ = nextVisit` (the next occurrence
along the oriented circle, in the cyclic order of traversal coordinates, `cycBetween`), the pairing
`pair = twin` (the other occurrence of the same crossing), the over/under bit `isOver` (the strand
of the occurrence is the chosen over strand) and the crossing sign `sgn = sign = sgn det(u_O, u_U)`
(eq:gauss-cross-sign, `dir` = edge direction). A named record isomorphism is `RecordIso ρ ρ'`: a
bijection `Φ : M ≃ M'` (with a bijection `e` of the circles respected by `Φ`) preserving successor,
pairing, bits and signs; `VisitBetween v w u` is the oriented cyclic order of three occurrences on
one circle; `ι.ExtendsToCircleMaps` says there are orientation-preserving bijections of the
parametrizing circles extending `Φ`. -/

namespace SM

open Link

/-- def:gauss-record as printed on SM15, read on the records of oriented link diagrams. -/
structure GaussRecordDefinitionData : Prop where
  /-- "Its finite crossing-occurrence set `M`": the occurrences of a diagram are its visits, each
  carried by one parametrizing circle. -/
  occurrences : ∀ D : Diagram, D.record.M = D.Γ.Visit ∧ ∀ v, D.record.comp v = D.compOf v
  /-- "forward successor `s`": the next occurrence on the same circle in the oriented cyclic order —
  no occurrence of that circle lies strictly between an occurrence and its successor. -/
  successor : ∀ (D : Diagram) (v : D.Γ.Visit),
    D.record.succ v = D.nextVisit v ∧ D.record.comp (D.record.succ v) = D.record.comp v ∧
    ∀ u, D.record.comp u = D.record.comp v →
      ¬ cycBetween (D.visitCoord v) (D.visitCoord u) (D.visitCoord (D.record.succ v))
  /-- "pairing involution `τ` without fixed points": the two occurrences of one crossing. -/
  pairing : ∀ (D : Diagram) (v : D.Γ.Visit),
    D.record.pair v = D.twin v ∧ (D.record.pair v).1 = v.1 ∧ D.record.pair v ≠ v ∧
    D.record.pair (D.record.pair v) = v
  /-- "an over/under bit at each occurrence": set exactly when the occurrence's strand is the
  chosen over strand; the two occurrences of a crossing carry opposite bits. -/
  bits : ∀ (D : Diagram) (v : D.Γ.Visit),
    (D.record.isOver v = true ↔ v.2.val = D.overStrand v.1) ∧
    D.record.isOver (D.record.pair v) = !D.record.isOver v
  /-- "crossing signs `σ(c) = sgn det(u_{c,O}, u_{c,U})`" (eq:gauss-cross-sign): stored on both
  occurrences of the crossing, never zero. -/
  signs : ∀ (D : Diagram) (v : D.Γ.Visit),
    D.record.sgn v = SignType.sign (det (D.Γ.dir (D.overStrand v.1)) (D.Γ.dir (D.underStrand v.1))) ∧
    D.record.sgn (D.record.pair v) = D.record.sgn v ∧ D.record.sgn v ≠ 0
  /-- "A named record isomorphism is a bijection `Φ : M → M'` preserving successor, pairing,
  over/under bits and these signs." -/
  iso : ∀ (ρ ρ' : Record) (ι : RecordIso ρ ρ'),
    Function.Bijective ι.Φ ∧ (∀ v, ι.Φ (ρ.succ v) = ρ'.succ (ι.Φ v)) ∧
    (∀ v, ι.Φ (ρ.pair v) = ρ'.pair (ι.Φ v)) ∧ (∀ v, ρ'.isOver (ι.Φ v) = ρ.isOver v) ∧
    (∀ v, ρ'.sgn (ι.Φ v) = ρ.sgn v) ∧ (∀ v, ρ'.comp (ι.Φ v) = ι.e (ρ.comp v))
  /-- "The parametrizing circles are oriented; the finite bijection must preserve their cyclic
  orders": a named record isomorphism of diagram records preserves the oriented cyclic order of the
  occurrences on each circle (so it never reverses a traversal). -/
  cyclic_order : ∀ (D D' : Diagram) (ι : RecordIso D.record D'.record) (v w u : D.Γ.Visit),
    D.compOf w = D.compOf v → D.compOf u = D.compOf v →
    (D'.VisitBetween (ι.Φ v) (ι.Φ w) (ι.Φ u) ↔ D.VisitBetween v w u)
  /-- "After a finite subdivision we choose an orientation-preserving piecewise-linear circle map
  `Φ̄ : C → C'` extending `Φ` … If `M` is empty, choose any positive circle parametrization": every
  named record isomorphism of diagram records extends to orientation-preserving bijections of the
  parametrizing circles carrying each occurrence to its image. -/
  extension : ∀ (D D' : Diagram) (ι : RecordIso D.record D'.record), ι.ExtendsToCircleMaps

theorem gauss_record_definition : GaussRecordDefinitionData where
  occurrences := fun D => ⟨rfl, fun v => D.record_comp v⟩
  successor := fun D v =>
    ⟨D.record_succ_apply v, D.record.succ_comp v, fun u hu => D.record_succ_no_between v u hu⟩
  pairing := fun D v => ⟨D.record_pair_apply v, D.twin_fst v, D.record.pair_ne v, D.record.pair_invol v⟩
  bits := fun D v => ⟨by rw [D.record_isOver_iff]; exact Iff.rfl, D.record.bit_pair v⟩
  signs := fun D v => ⟨rfl, D.record.sgn_pair v, D.record.sgn_ne v⟩
  iso := fun _ _ ι => ⟨ι.Φ.bijective, ι.succ_eq, ι.pair_eq, ι.bit_eq, ι.sgn_eq, ι.comp_eq⟩
  cyclic_order := fun _ _ ι v w u hw hu => ι.visitBetween_iff v w u hw hu
  extension := sorry

end SM
