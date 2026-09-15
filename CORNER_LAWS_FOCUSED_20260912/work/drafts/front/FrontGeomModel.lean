import SM.FrontRecordBridge

/-! # The geometric model of `S(F)` carries the front's record (front lane γ, decision D-F6)

Intended home: `SM/FrontGeomModel.lean`.  Imports `SM.FrontRecordBridge` (row ng:smoothing-record)
and through it `SM.FrontSmooth` (row ng:front-domain).  Not a row; a library extension.

## Why this module exists (executor decision D-F6, work/AUTHOR_NOTES.md "Four accepts, one split
verdict, one library decision", 2026-09-14)

The accepted row ng:front-domain reads a rounding of a front `F : SmoothFront` as
`F.Rounding S = ⟨G, geom : F.GeomRounding G, marking : F.Marking S⟩`, `F.IsRounding S :=
Nonempty (F.Rounding S)`.  All three reviewers of ng:smoothing-record observed that no field ties
the polygonal diagram `S` to the rounded curves `G`: the marking is a marking of **the front's own**
named record (`F.Occ`, `F.eval`, `F.slope`, `F.crossSign`), so "S(F) has F's record" sits in the
definition, and the row's clauses follow from the composite marking isomorphism without the
geometry.  The content of the printed proof (sm-3:1851-1862) — "A cusp replacement inside a clean
cusp disc creates no crossing and changes no successor of an old crossing visit along the oriented
parameter circle … Every crossing pairing, sign and over/under bit is determined by germs outside
the cusp discs, which are unchanged" — was kernel-checked only as library lemmas about `G` versus
`F` (`GeomRounding.isDoubleOf_iff`, `occSetOf_eq`, `slopeOf_eq`, `crossSignOf_eq` in
SM/FrontRecordBridge.lean), not as a statement about the diagram `S`.

D-F6: the accepted declarations are **not** rewritten (rule 2).  Instead the library is extended,
here, by the geometric model and the theorem that closes the gap:

* `GeomMarking G S` — "the polygonal diagram `S` carries the named record of the smooth loops
  `G`" — defined on a plain loop family `G : Fin c → SmoothLoop` **exactly** as `SmoothFront.Marking`
  is defined on the front, field for field, with `G`'s own notions in place of `F`'s: the
  occurrences are `OccOf G = ↥(occSetOf G)` (the double-point parameters of `G` in the fundamental
  period), meeting is `(G p.1).γ p.2 = (G q.1).γ q.2` (the relation inside `IsDoubleOf`/`occSetOf`),
  over = smaller `slopeOf G`, sign = `crossSignOf G` (the sign of the determinant of `G`'s tangents).
  Nothing about `F` enters the definition.
* `Marking.ofGeom (geom : F.GeomRounding G) (m : GeomMarking G S) : F.Marking S` — **the
  theorem**: a polygonal diagram carrying the named record of the rounded curves carries the
  front's record.  Its proof is exactly the printed proof: the occurrences are the same parameters
  on the same oriented circles (`occSetOf_eq`: "creates no crossing … changes no successor"), so
  the occurrence bijection is transported along the set equality; distinct occurrences meet under
  `G` iff they meet under `F` (`isDoubleOf_iff`); the slopes and the tangent-determinant signs at
  every double point are the front's (`slopeOf_eq`, `crossSignOf_eq`: "determined by germs outside
  the cusp discs, which are unchanged"); the circles are literally shared (`e` is kept).
* `GeomMarking.ofMarking`, the converse, so the two readings are interchangeable on a rounding.
* `isRounding_of_geomModel : F.GeomRounding G → Nonempty (GeomMarking G S) → F.IsRounding S` and
  `isRounding_iff_geomModel : F.IsRounding S ↔ ∃ G, Nonempty (F.GeomRounding G) ∧
  Nonempty (GeomMarking G S)`: the accepted `IsRounding` is equivalent to the fully geometric reading
  "some clean-disc cusp replacement `G` of `F` exists and `S` is a polygonal reading of `G`", in
  which the front's record is never mentioned.

Consequently the printed statement of ng:smoothing-record holds for diagrams that carry the record
of the *rounded curves*: `recordIso_nonempty_of_geomModels` and `P_eq_of_geomModels` (§5).

Fidelity notes.  FR-1 (polygonal reading) and FR-4 (the rounded curves live on the front's parameter
circles) of the design are inherited unchanged; `GeomMarking` is FR-1 applied to `G` instead of
`F`.  The only non-syntactic ingredient of the transport is that the two occurrence sets are equal
as *sets of parameters* (`occSetOf_eq`), so the cyclic orders (`cycBetween` on the parameters) and
the circles need no argument at all — this is the printed "changes no successor of an old crossing
visit along the oriented parameter circle". -/

namespace SM

open Link Filter Topology

noncomputable section
open Classical

namespace SmoothFront

/-! ## 1. The occurrences of a family of smooth loops -/

variable {c : ℕ}

/-- the occurrence type of a family of loops (finite once a `GeomMarking` exists,
`GeomMarking.finite_occ`); on `F.comp` it is `F.Occ` by `rfl` -/
abbrev OccOf (G : Fin c → SmoothLoop) : Type := occSetOf G

theorem occOf_comp (F : SmoothFront) : OccOf F.comp = F.Occ := rfl

theorem OccOf.mem_Ico {G : Fin c → SmoothLoop} (p : OccOf G) : p.1.2 ∈ Set.Ico (0 : ℝ) 1 := p.2.1

/-- distinct occurrences are distinct parameters of the circles (both lie in the fundamental
period) -/
theorem OccOf.not_sameParam_of_ne {G : Fin c → SmoothLoop} {p q : OccOf G} (hne : p ≠ q) :
    ¬ SameParam p.1 q.1 :=
  fun hs => hne (Subtype.ext (SameParam.eq_of_mem_Ico p.2.1 q.2.1 hs))

/-- two distinct occurrences of the loops with the same image form a double point of the loops -/
theorem OccOf.isDoubleOf_of_ne {G : Fin c → SmoothLoop} {p q : OccOf G} (hne : p ≠ q)
    (he : (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2) : IsDoubleOf G p.1 q.1 :=
  ⟨OccOf.not_sameParam_of_ne hne, he⟩

/-- the same for the front's occurrences -/
theorem Occ.not_sameParam_of_ne {F : SmoothFront} {p q : F.Occ} (hne : p ≠ q) :
    ¬ SameParam p.1 q.1 :=
  fun hs => hne (Subtype.ext (SameParam.eq_of_mem_Ico p.2.1 q.2.1 hs))

/-! ## 2. `GeomMarking`: a polygonal diagram carrying the named record of smooth loops

Field for field the accepted `SmoothFront.Marking` (SM/FrontSmooth.lean §7), with the front's
notions replaced by those of the loop family `G` (SM/FrontRecordBridge.lean §2):

| `Marking F S` | `GeomMarking G S` |
|---|---|
| `F.Occ = ↥F.occSet` | `OccOf G = ↥(occSetOf G)` |
| `F.eval p = F.eval q` | `(G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2` |
| `F.slope p.1` | `slopeOf G p.1` |
| `F.crossSign p.1 q.1` | `crossSignOf G p.1 q.1` |

(`F.eval p` is `(F.comp p.1).γ p.2` by definition; on `G = F.comp` every entry of the right column
is the left one by `rfl` — `GeomMarking.ofComp`, `GeomMarking.toMarkingComp` below are the field-by-field
witnesses.) -/

/-- The polygonal reading of the smooth loops `G` (FR-1 applied to the rounded curves; sm-3:337-343,
lem:gauss-pl-model): the polygonal `Diagram S` carries the full named record of `G` — its component
circles (crossing-free ones included), its crossing occurrences (the double-point parameters), their
cyclic order along each oriented parameter circle, the pairing of the two occurrences of each double
point, the over/under bits (over = smaller `dz/dx` of `G`) and the signs (the over-first
tangent-determinant sign of `G`).  The front `F` does not occur. -/
structure GeomMarking (G : Fin c → SmoothLoop) (S : Diagram) where
  /-- the component circles, crossing-free ones included -/
  e : Fin c ≃ Fin S.Γ.c
  /-- the crossing occurrences -/
  Φ : OccOf G ≃ S.Γ.Visit
  /-- an occurrence keeps its circle -/
  comp_eq : ∀ p : OccOf G, S.compOf (Φ p) = e p.1.1
  /-- the cyclic order of the occurrences along each oriented circle -/
  between_iff : ∀ p q r : OccOf G, p.1.1 = q.1.1 → q.1.1 = r.1.1 →
    (cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (S.visitCoord (Φ p)) (S.visitCoord (Φ q)) (S.visitCoord (Φ r)))
  /-- the pairing of the two occurrences of each double point -/
  pair_eq : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 → Φ q = S.twin (Φ p)
  /-- the over/under bits: over = smaller slope -/
  over_iff : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
    (S.overBit (Φ p) = true ↔ slopeOf G p.1 < slopeOf G q.1)
  /-- the signs: the over-first tangent-determinant sign -/
  sgn_eq : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
    slopeOf G p.1 < slopeOf G q.1 → ((S.sign (Φ p).1 : ℤ)) = crossSignOf G p.1 q.1

namespace GeomMarking

variable {G : Fin c → SmoothLoop} {S : Diagram}

/-- a diagram carrying the record of `G` has `G`'s number of circles -/
theorem c_eq (m : GeomMarking G S) : S.Γ.c = c := (Fin.equiv_iff_eq.mp ⟨m.e⟩).symm

theorem componentCount_eq (m : GeomMarking G S) : S.componentCount = c := m.c_eq

/-- the occurrence set of `G` is finite once a polygonal reading exists (the visits of a `Diagram`
form a `Fintype`) -/
theorem finite_occ (m : GeomMarking G S) : (occSetOf G).Finite :=
  Set.finite_coe_iff.mp (Finite.of_equiv S.Γ.Visit m.Φ.symm)

theorem card_visit_eq (m : GeomMarking G S) : Nat.card S.Γ.Visit = Nat.card (OccOf G) :=
  (Nat.card_congr m.Φ).symm

/-- the under branch of a marked double point carries bit `false` -/
theorem under_bit (m : GeomMarking G S) {p q : OccOf G} (hne : p ≠ q)
    (he : (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2) (hs : slopeOf G p.1 < slopeOf G q.1) :
    S.overBit (m.Φ q) = false := by
  have h := m.over_iff q p hne.symm he.symm
  rcases Bool.eq_false_or_eq_true (S.overBit (m.Φ q)) with hb | hb
  · exact absurd (h.mp hb) (lt_asymm hs)
  · exact hb

/-- sanity: on the front's own components a `GeomMarking` is a `Marking`, field by field -/
def toMarkingComp {F : SmoothFront} {S : Diagram} (m : GeomMarking F.comp S) : F.Marking S :=
  ⟨m.e, m.Φ, m.comp_eq, m.between_iff, m.pair_eq, m.over_iff, m.sgn_eq⟩

/-- sanity: a `Marking` of the front is a `GeomMarking` of its components, field by field -/
def ofComp {F : SmoothFront} {S : Diagram} (m : F.Marking S) : GeomMarking F.comp S :=
  ⟨m.e, m.Φ, m.comp_eq, m.between_iff, m.pair_eq, m.over_iff, m.sgn_eq⟩

end GeomMarking

/-! ## 3. Transport along a rounding: the occurrences are the same parameters -/

namespace GeomRounding

variable {F : SmoothFront} {G : Fin F.c → SmoothLoop} (r : F.GeomRounding G)
include r

/-- "changes no successor of an old crossing visit along the oriented parameter circle": the
occurrences of the rounded curves *are* the occurrences of the front, as the same parameters of the
same oriented circles (`occSetOf_eq`) -/
def occEquiv : OccOf G ≃ F.Occ := Equiv.setCongr r.occSetOf_eq

@[simp] theorem occEquiv_apply_val (p : OccOf G) : (r.occEquiv p).1 = p.1 := rfl

@[simp] theorem occEquiv_symm_apply_val (p : F.Occ) : (r.occEquiv.symm p).1 = p.1 := rfl

/-- "creates no crossing": two distinct parameters meet under the rounded curves iff they meet
under the front -/
theorem eval_eq_iff {p q : Param F.c} (h : ¬ SameParam p q) :
    (G p.1).γ p.2 = (G q.1).γ q.2 ↔ F.eval p = F.eval q :=
  ⟨fun he => ((r.isDoubleOf_iff p q).mp ⟨h, he⟩).2,
    fun he => ((r.isDoubleOf_iff p q).mpr ⟨h, he⟩).2⟩

/-- a double point of the rounded curves is a double point of the front -/
theorem isDouble_of_occOf_ne {p q : OccOf G} (hne : p ≠ q)
    (he : (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2) : F.IsDouble p.1 q.1 :=
  (r.isDoubleOf_iff p.1 q.1).mp (OccOf.isDoubleOf_of_ne hne he)

end GeomRounding

/-! ## 4. The theorem: a polygonal reading of the rounded curves is a reading of the front -/

namespace Marking

variable {F : SmoothFront} {G : Fin F.c → SmoothLoop} {S : Diagram}

/-- **D-F6.**  A polygonal diagram carrying the named record of the rounded curves `G` of a
clean-disc cusp replacement of `F` carries the named record of `F`: the printed proof of
ng:smoothing-record (sm-3:1851-1862) as a kernel-checked statement about the diagram `S`.  The
circles and the occurrence bijection are kept, the occurrences being the same parameters on the
same oriented circles (`GeomRounding.occEquiv`, from `occSetOf_eq`); the cyclic orders are the
cyclic orders of those parameters and need no argument; meeting, slopes and signs are transported
by `isDoubleOf_iff`, `slopeOf_eq`, `crossSignOf_eq`. -/
def ofGeom (r : F.GeomRounding G) (m : GeomMarking G S) : F.Marking S where
  e := m.e
  Φ := r.occEquiv.symm.trans m.Φ
  comp_eq p := m.comp_eq (r.occEquiv.symm p)
  between_iff p q s hpq hqs :=
    m.between_iff (r.occEquiv.symm p) (r.occEquiv.symm q) (r.occEquiv.symm s) hpq hqs
  pair_eq p q hne he :=
    m.pair_eq (r.occEquiv.symm p) (r.occEquiv.symm q) (fun h => hne (r.occEquiv.symm.injective h))
      ((r.eval_eq_iff (Occ.not_sameParam_of_ne hne)).mpr he)
  over_iff p q hne he := by
    have hd : F.IsDouble p.1 q.1 := Occ.isDouble_of_ne F hne he
    have h : (S.overBit (m.Φ (r.occEquiv.symm p)) = true ↔ slopeOf G p.1 < slopeOf G q.1) :=
      m.over_iff (r.occEquiv.symm p) (r.occEquiv.symm q)
        (fun h => hne (r.occEquiv.symm.injective h))
        ((r.eval_eq_iff (Occ.not_sameParam_of_ne hne)).mpr he)
    rw [r.slopeOf_eq hd, r.slopeOf_eq hd.symm] at h
    exact h
  sgn_eq p q hne he hs := by
    have hd : F.IsDouble p.1 q.1 := Occ.isDouble_of_ne F hne he
    have hs' : slopeOf G p.1 < slopeOf G q.1 := by
      rw [r.slopeOf_eq hd, r.slopeOf_eq hd.symm]; exact hs
    have h : ((S.sign (m.Φ (r.occEquiv.symm p)).1 : ℤ)) = crossSignOf G p.1 q.1 :=
      m.sgn_eq (r.occEquiv.symm p) (r.occEquiv.symm q)
        (fun h => hne (r.occEquiv.symm.injective h))
        ((r.eval_eq_iff (Occ.not_sameParam_of_ne hne)).mpr he) hs'
    rw [r.crossSignOf_eq hd] at h
    exact h

@[simp] theorem ofGeom_e (r : F.GeomRounding G) (m : GeomMarking G S) : (ofGeom r m).e = m.e := rfl

@[simp] theorem ofGeom_Φ (r : F.GeomRounding G) (m : GeomMarking G S) (p : F.Occ) :
    (ofGeom r m).Φ p = m.Φ (r.occEquiv.symm p) := rfl

end Marking

namespace GeomMarking

variable {F : SmoothFront} {G : Fin F.c → SmoothLoop} {S : Diagram}

/-- the converse: a polygonal reading of the front is a polygonal reading of its rounded curves -/
def ofMarking (r : F.GeomRounding G) (m : F.Marking S) : GeomMarking G S where
  e := m.e
  Φ := r.occEquiv.trans m.Φ
  comp_eq p := m.comp_eq (r.occEquiv p)
  between_iff p q s hpq hqs := m.between_iff (r.occEquiv p) (r.occEquiv q) (r.occEquiv s) hpq hqs
  pair_eq p q hne he :=
    m.pair_eq (r.occEquiv p) (r.occEquiv q) (fun h => hne (r.occEquiv.injective h))
      ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mp he)
  over_iff p q hne he := by
    have hd : F.IsDouble p.1 q.1 := r.isDouble_of_occOf_ne hne he
    have h : (S.overBit (m.Φ (r.occEquiv p)) = true ↔ F.slope p.1 < F.slope q.1) :=
      m.over_iff (r.occEquiv p) (r.occEquiv q) (fun h => hne (r.occEquiv.injective h))
        ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mp he)
    rw [← r.slopeOf_eq hd, ← r.slopeOf_eq hd.symm] at h
    exact h
  sgn_eq p q hne he hs := by
    have hd : F.IsDouble p.1 q.1 := r.isDouble_of_occOf_ne hne he
    have hs' : F.slope p.1 < F.slope q.1 := by
      rw [← r.slopeOf_eq hd, ← r.slopeOf_eq hd.symm]; exact hs
    have h : ((S.sign (m.Φ (r.occEquiv p)).1 : ℤ)) = F.crossSign p.1 q.1 :=
      m.sgn_eq (r.occEquiv p) (r.occEquiv q) (fun h => hne (r.occEquiv.injective h))
        ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mp he) hs'
    rw [← r.crossSignOf_eq hd] at h
    exact h

@[simp] theorem ofMarking_e (r : F.GeomRounding G) (m : F.Marking S) : (ofMarking r m).e = m.e :=
  rfl

@[simp] theorem ofMarking_Φ (r : F.GeomRounding G) (m : F.Marking S) (p : OccOf G) :
    (ofMarking r m).Φ p = m.Φ (r.occEquiv p) := rfl

/-- the two transports are inverse: back and forth is the identity on the front's reading -/
theorem ofGeom_ofMarking (r : F.GeomRounding G) (m : F.Marking S) :
    Marking.ofGeom r (ofMarking r m) = m := by
  obtain ⟨e, Φ, _, _, _, _, _⟩ := m
  simp only [Marking.ofGeom, ofMarking, Marking.mk.injEq, true_and]
  ext p
  simp

/-- and on the loops' reading -/
theorem ofMarking_ofGeom (r : F.GeomRounding G) (m : GeomMarking G S) :
    ofMarking r (Marking.ofGeom r m) = m := by
  obtain ⟨e, Φ, _, _, _, _, _⟩ := m
  simp only [Marking.ofGeom, ofMarking, GeomMarking.mk.injEq, true_and]
  ext p
  simp

end GeomMarking

/-! ## 5. `IsRounding` in the geometric model -/

/-- the readings of the front and of its rounded curves exist together -/
theorem GeomRounding.marking_nonempty_iff {F : SmoothFront} {G : Fin F.c → SmoothLoop}
    (r : F.GeomRounding G) (S : Diagram) :
    Nonempty (F.Marking S) ↔ Nonempty (GeomMarking G S) :=
  ⟨fun h => h.elim fun m => ⟨GeomMarking.ofMarking r m⟩,
    fun h => h.elim fun m => ⟨Marking.ofGeom r m⟩⟩

/-- a rounding `S(F)` carries the named record of its own rounded curves -/
def Rounding.geomMarking {F : SmoothFront} {S : Diagram} (ρ : F.Rounding S) : GeomMarking ρ.G S :=
  GeomMarking.ofMarking ρ.geom ρ.marking

/-- **D-F6, main theorem.**  If `G` is a clean-disc cusp replacement of `F` and the polygonal
diagram `S` carries the named record of `G`, then `S` is an `S(F)` in the sense of the accepted
row ng:front-domain — the front's record never has to be read off `S` directly. -/
theorem isRounding_of_geomModel {F : SmoothFront} {G : Fin F.c → SmoothLoop}
    (geom : F.GeomRounding G) {S : Diagram} (h : Nonempty (GeomMarking G S)) : F.IsRounding S :=
  h.elim fun m => ⟨⟨G, geom, Marking.ofGeom geom m⟩⟩

/-- **D-F6.**  The accepted `IsRounding` equals the fully geometric reading: some clean-disc cusp
replacement `G` of `F` exists and `S` is a polygonal reading of *`G`* (its double points, cyclic
orders, pairing, slopes and tangent signs).  Compare the accepted `isRounding_iff`, in which the
second conjunct is a reading of `F`. -/
theorem isRounding_iff_geomModel (F : SmoothFront) (S : Diagram) :
    F.IsRounding S ↔
      ∃ G : Fin F.c → SmoothLoop, Nonempty (F.GeomRounding G) ∧ Nonempty (GeomMarking G S) := by
  constructor
  · rintro ⟨ρ⟩
    exact ⟨ρ.G, ⟨ρ.geom⟩, ⟨ρ.geomMarking⟩⟩
  · rintro ⟨G, ⟨geom⟩, h⟩
    exact isRounding_of_geomModel geom h

/-- ng:smoothing-record in the geometric model: two polygonal diagrams carrying the named records
of two clean-disc cusp replacements `G`, `G'` of one front have isomorphic named records -/
theorem recordIso_nonempty_of_geomModels {F : SmoothFront} {G G' : Fin F.c → SmoothLoop}
    (geom : F.GeomRounding G) (geom' : F.GeomRounding G') {S S' : Diagram}
    (h : Nonempty (GeomMarking G S)) (h' : Nonempty (GeomMarking G' S')) :
    Nonempty (RecordIso S.record S'.record) :=
  (isRounding_of_geomModel geom h).recordIso_nonempty (isRounding_of_geomModel geom' h')

/-- "Consequently P_{S(F)} does not depend on the choice of rounding", in the geometric model
(through the accepted `presentations`, hence with the row's axiom `SM.lp_lm` via `P`) -/
theorem P_eq_of_geomModels {F : SmoothFront} {G G' : Fin F.c → SmoothLoop}
    (geom : F.GeomRounding G) (geom' : F.GeomRounding G') {S S' : Diagram}
    (h : Nonempty (GeomMarking G S)) (h' : Nonempty (GeomMarking G' S')) : P S = P S' :=
  (isRounding_of_geomModel geom h).P_eq (isRounding_of_geomModel geom' h')

end SmoothFront

end

end SM
