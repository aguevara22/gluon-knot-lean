import SM.FrontRealizeGeometry
import SM.FrontRealizeBase
import SM.FrontRealizeDeform
import SM.FrontInterfaces
import SM.FrontWordsBase
import SM.FrontGeomModel
import SM.PolynomialBlock

/-! # Front certificate rows 76-83 — PROOF SKELETON (FINAL, judge 2026-09-14)

work/drafts/frontrows/Skeleton_FINAL.lean.  The definitions and the eight bundles are copied verbatim from
Statements_FINAL.lean; the eight row theorems are ASSEMBLED at the end from the named LEAVES of section
"Leaves" (26 placeholders, none a row); all glue is proved.  Plan and unit split: PLAN_FINAL.md (units U1-U8).

Leaf groups (PLAN_FINAL.md §5):
* **L-deg** (U1): Laurent-degree arithmetic on `R` — `delta_ne_zero`, `degAZ_delta`, the two skein degree
  bounds (displays ng:skein-plus/minus, ng:degree-plus/minus).
* **L-cnt** (U1): the count changes `ΔD`, `Δw` of each pattern on the realization, through the accepted letter
  tracing (`realize_downCount`, `realize_writhe`) — displays ng:type-I-counts, ng:zigzag-counts,
  ng:crossed-cusp-counts, ng:circle-counts and the (t,u) table.
* **L-rec** (U3, on the record core U2): named-record isomorphisms for the moves that are NOT Reidemeister moves
  of the ordinary diagram — commutation, zigzag deletion, circle deletion (`Record.addFree`), the cusp-skein
  site (switch record + smoothing record + sign), and the uniqueness of the compatible smoothing.
* **L-geo** (U5, U6 on the geometry core U4): the disc-local moves — type III directly between the two standard
  realizations (`RIIIData` in a band disc hugging the three strands), types I, II and the crossed cusp through
  a vertex-moved diagram `D` (same shadow structure as `realize W`, the active strand's interior vertices moved
  inside a convex disc hugging the active strands; `RI`/`RII` there) whose named record is that of `realize W'`.
  NOT through the full-height block rectangle `BlockSetup.U`: `ArcCover` (LinkMoves.lean:208) forbids
  spectator strands inside the move disc (PLAN_FINAL.md §3 F1).
* **L-PL** (U7): the planarity fact `D = c` for an arbitrary PL union of standard circles (row 81 sentence 2).
* **L-smooth** (U8): the smooth clauses of row 76 (nonsingular deformation; representation).

Every leaf below is a TRUE statement about the accepted objects (audited in PLAN_FINAL.md §4); no leaf fixes a
move disc.  Checked with `cd work/lean && lake env lean`. -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

/-! ## Statements (verbatim from Statements_FINAL.lean) -/

structure SmoothFront.NonsingularDeformation (F F' : SmoothFront) where
  path : ℝ → SmoothFront
  start : path 0 = F
  stop : path 1 = F'
  c_eq : ∀ t, (path t).c = F.c
  smooth : ∀ i : Fin F.c, ContDiffOn ℝ ∞
    (fun p : ℝ × ℝ => ((path p.1).comp (Fin.cast (c_eq p.1).symm i)).γ p.2) (Set.Icc 0 1 ×ˢ Set.univ)

structure NgCommutationClauses : Prop where
  comm_D : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  comm_w : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).writhe = (realize W').writhe
  comm_d : ∀ W W' : OWord, IsComm W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  comm_B : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).defect = (realize W').defect
  deform_D : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.downCount = F'.downCount
  deform_w : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.writhe = F'.writhe
  deform_d : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → degAZ (P S) = degAZ (P S')
  deform_B : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → F.defect S = F'.defect S'
  represent : ∀ F : SmoothFront, ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)

structure NgFrontIClauses : Prop where
  typeI_B : ∀ W W' : OWord, IsTypeI W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgFrontIIClauses : Prop where
  typeII_D : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  typeII_w : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  typeII_d : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  typeII_B : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgFrontIIIClauses : Prop where
  typeIII_D : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  typeIII_w : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  typeIII_d : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  typeIII_B : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgDeletionsClauses : Prop where
  zigzag_s : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').sCount + 2 = (realize W).sCount
  zigzag_B : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect
  crossedCusp_s : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').sCount + 1 = (realize W).sCount
  crossedCusp_B : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect

structure NgCircleClauses : Prop where
  circleDeletion_B : ∀ W W' : OWord, IsCircleDeletion W.letters W'.letters →
    (realize W).defect = (realize W').defect
  single_B : ∀ F : PLFront, F.IsStandardCircles → F.Γ.c = 1 → F.defect = 0
  union_B : ∀ F : PLFront, F.IsStandardCircles → F.defect = 0

structure NgCuspSkeinClauses : Prop where
  earlier_branch : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    min (realize A').defect (realize C).defect ≤ (realize A).defect
  unique_smoothing : ∀ A A' C C' : OWord, IsCuspSkein A.letters A'.letters C.letters →
    IsCuspSkein A.letters A'.letters C'.letters → C.letters = C'.letters
  smoothing_s : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    (realize C).sCount + 1 = (realize A).sCount
  principal_s : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    (realize A').sCount = (realize A).sCount

structure NgLocalFrontBoundClauses : Prop where
  front_inequality : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1

/-! ### Nonemptiness helpers (the `s` clauses read `realize_sCount`, which needs a nonempty word) -/

namespace FrontWord

theorem IsZigzagDeletion.source_ne_nil {W W' : Word} (h : IsZigzagDeletion W W') : W ≠ [] := by
  obtain ⟨X, Y, m, d, -, hpat, -⟩ := h
  rcases hpat with rfl | rfl <;> simp

theorem IsCrossedCuspShortcut.ne_nil {W W' : Word} (h : IsCrossedCuspShortcut W W') : W ≠ [] ∧ W' ≠ [] := by
  obtain ⟨X, Y, i, -, hpat⟩ := h
  rcases hpat with ⟨d, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem IsCuspSkeinStep.ne_nil {A A' C : Word} (h : IsCuspSkeinStep A A' C) : A ≠ [] ∧ A' ≠ [] ∧ C ≠ [] := by
  obtain ⟨X, Y, m, d, a, P, L, -, -, -, rfl, rfl, hC⟩ := h
  rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

theorem IsCuspSkein.ne_nil {A A' C : Word} (h : IsCuspSkein A A' C) : A ≠ [] ∧ A' ≠ [] ∧ C ≠ [] := by
  rcases h with h | h
  · exact h.ne_nil
  · obtain ⟨h1, h2, h3⟩ := h.ne_nil; exact ⟨h2, h1, h3⟩

end FrontWord

namespace FrontRows

/-! ## Leaves -/

section Leaves

/-! ### L-deg (unit U1) — Laurent-degree arithmetic (def:adeg, `SM/LinkLaurentRing.lean`) -/

/-- LEAF: `δ = (a − a⁻¹) z⁻¹ ≠ 0` (units and the domain `R`). -/
theorem delta_ne_zero : R.delta ≠ 0 := sorry

/-- LEAF (ng:circle, sm-3:2060-2061 "The leading a coefficient of δ is z⁻¹, in degree one"): `deg_a δ = 1`. -/
theorem degAZ_delta : degAZ R.delta = 1 := sorry

/-- LEAF (display ng:skein-plus solved for degrees, sm-3:2137-2146 "The degree of a nonzero sum is at most
the maximum of the summand degrees.  Multiplication by a^k shifts degree by k, and multiplication by z
does not change it"): from `f = a⁻² g + a⁻¹ z h`, `deg_a f ≤ max (deg_a g − 2) (deg_a h − 1)`
(`degA_add_le`, `degAZ_mul`, `degA_aInv`, `degA_z`). -/
theorem degAZ_le_of_eq_pos {f g h : R} (hg : g ≠ 0) (hh : h ≠ 0)
    (e : f = R.aInv * R.aInv * g + R.aInv * R.z * h) (hf : f ≠ 0) :
    degAZ f ≤ max (degAZ g - 2) (degAZ h - 1) := sorry

/-- LEAF (display ng:skein-minus solved for degrees, sm-3:2140-2148): from `f = a² g − a z h`,
`deg_a f ≤ max (deg_a g + 2) (deg_a h + 1)`. -/
theorem degAZ_le_of_eq_neg {f g h : R} (hg : g ≠ 0) (hh : h ≠ 0)
    (e : f = R.a * R.a * g - R.a * R.z * h) (hf : f ≠ 0) :
    degAZ f ≤ max (degAZ g + 2) (degAZ h + 1) := sorry

/-! ### L-cnt (unit U1) — the count changes on the realization, through the accepted letter tracing
(`realize_downCount`, `realize_writhe` = β1's `downCountFrom`/`writheFrom` over `X ++ P ++ Y` at the typed
cut before the factor; the printed displays are the factor's own contribution) -/

/-- LEAF (ng:commutation, sm-3:1929-1933 "The cusp directions and crossing signs are unchanged, so D and w
are unchanged as well"). -/
theorem comm_counts {W W' : OWord} (h : IsComm W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := sorry

/-- LEAF (display ng:type-I-counts, sm-3:1964-1966, deletion direction: the curl carries exactly one downward
cusp — "Exactly one of the two cusps is downward and one is upward" — and one positive crossing — "Its
crossing is also positive"). -/
theorem typeI_counts {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount + 1 ∧ (realize W).writhe = (realize W').writhe + 1 :=
  sorry

/-- LEAF (ng:front-II, sm-3:1979-1987 "Their signs are opposite ... The same upper and lower cusp arms remain
after deletion.  Thus Δw = ΔD = 0"). -/
theorem typeII_counts {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := sorry

/-- LEAF (ng:front-III, sm-3:1997-2001 "Each physical pair crosses on both sides with the same over/under bit
and transported arrows" — no cusp letter, signs preserved). -/
theorem typeIII_counts {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := sorry

/-- LEAF (display ng:zigzag-counts, sm-3:2020-2022: `Δw = 0`, `ΔD ∈ {0, −2}` — "Their directions are both
downward or both upward"). -/
theorem zigzag_counts {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    (realize W).writhe = (realize W').writhe ∧
    ((realize W).downCount = (realize W').downCount ∨ (realize W).downCount = (realize W').downCount + 2) :=
  sorry

/-- LEAF (display ng:crossed-cusp-counts, sm-3:2030-2036 "the old crossing has sign −1.  Deletion raises w by
one and flips the cusp direction ... If the old cusp was downward, ΔD = −1; otherwise ΔD = 1"). -/
theorem crossedCusp_counts {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    (realize W').writhe = (realize W).writhe + 1 ∧
    ((realize W').downCount + 1 = (realize W).downCount ∨ (realize W').downCount = (realize W).downCount + 1) :=
  sorry

/-- LEAF (display ng:circle-counts, sm-3:2064-2068: `D_before = D_after + 1`, "The writhe is unchanged"). -/
theorem circleDeletion_counts {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    (realize W).writhe = (realize W').writhe ∧ (realize W).downCount = (realize W').downCount + 1 := sorry

/-- LEAF (the (t,u) table sm-3:2107-2126 "the same downward-cusp count in all three diagrams", and
sm-3:2129-2131 "Their writhes are w₀+1, w₀−1, w₀": the two principal branches carry opposite signs at the
one crossing, so `w_A + w_{A'} = 2 w_C`; which is which is fixed by the sign of the site, `skein_site`). -/
theorem skein_counts {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    (realize A).downCount = (realize C).downCount ∧ (realize A').downCount = (realize C).downCount ∧
    (realize A).writhe + (realize A').writhe = 2 * (realize C).writhe := sorry

/-! ### L-rec (unit U3, on the record core U2) — named-record isomorphisms (rp:record-polynomial
`presentations`, lp:split-circle in record form `P_addFree`, the accepted smoothing gate
`exists_smoothing_record_visit`).  Record of a realization: visits = the two slots of each `σ` letter,
successor = the next `σ` slot along the slot cycle `next` (`toSlot_succ`, `crossingParam_eq_half`), twin = the
other slot of the column, over = the descending strand (`overStrand_crossingOf`), sign = `sign_crossingOf`;
exterior slots of two words correspond by the index shift (`shiftIdx`, `next_ext`). -/

/-- LEAF (ng:commutation, sm-3:1929-1933 "After cusp rounding this is a positive page isotopy; equivalently,
the full named records are the same"). -/
theorem comm_recordIso {W W' : OWord} (h : IsComm W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := sorry

/-- LEAF (ng:deletions, sm-3:2017-2019: after rounding the zigzag "is a simple ordinary arc, positively page
isotopic relative to its endpoints to the straightened arc" — no crossing is touched; every strand passes
through the block, the exterior visits and their cyclic orders are unchanged). -/
theorem zigzag_recordIso {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := sorry

/-- LEAF (ng:circle, sm-3:2054-2059 "A standard circle separated by the word procedure has no mixed crossings
... Lemma lp:split-circle permits this nesting"): the record of the word with the circle is the record of the
remainder with one free (crossing-free) component added. -/
theorem circle_recordIso_addFree {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := sorry

/-- The data one principal direction of the interchange supplies for its earlier branch `A` (sm-3:2091-2099
"Exchanging over and under at that crossing makes their local ordered crossing records identical, including
the boundary attachments.  After gluing any same actual exterior, the full named records are identical.  Thus
their polynomial values are the two crossing choices at one ordinary skein site"; sm-3:2119-2126 "Only the one
compatible smoothing is used"): the crossing `x` of the `σ` letter of `A`'s factor; the named record of
`realize A'` is that of the switch of `realize A` at `x`; an oriented smoothing of `realize A` at `x` (the
accepted `exists_smoothing_record_visit` supplies one with record `(realize A).record.smooth v`) carries the
named record of `realize C`; and the sign of `x` is the writhe difference `w_A − w_C` (the exterior writhe
`w₀` is `w_C`). -/
def SkeinSite (A A' C : OWord) : Prop :=
  ∃ x : (realize A).diagram.Γ.Crossing,
    Nonempty (RecordIso (realize A').diagram.record ((realize A).diagram.switch x).record) ∧
    (∃ D₀ : Diagram, IsOrientedSmoothing (realize A).diagram x D₀ ∧
      Nonempty (RecordIso D₀.record (realize C).diagram.record)) ∧
    ((realize A).diagram.sign x : ℤ) = (realize A).writhe - (realize C).writhe

/-- LEAF (ng:cusp-skein, the site for the printed direction `A = l_{m+1} σ_m`, `A' = l_m σ_{m+1}`, smoothing
`C_top`/`C_bottom` by the (t,u) table).  The other principal direction is the same leaf applied to
`IsCuspSkeinStep A' A C` (glue `skein_ineq_backward`). -/
theorem skein_site {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) : SkeinSite A A' C :=
  sorry

/-- LEAF (ng:cusp-skein "the unique compatible smoothing", FR-12): the interchange determines `C` — the two
principal words differ first at the cusp letter, which fixes `X`, `m`, `d`, `Y`; the through-strand bit is
read from `run X []`; the reverse-direction case is contradictory (`l (m+1) = l m'`, `l m = l (m'+1)`). -/
theorem skein_unique {A A' C C' : Word} (h : IsCuspSkein A A' C) (h' : IsCuspSkein A A' C') : C = C' :=
  sorry

/-! ### L-geo (units U5, U6 on the geometry core U4) — the disc-local moves through the accepted
`RIData`/`RIIData`/`RIIIData` (`P_reidemeister_I/II/III`).  The move disc is a convex polygon hugging the
active strands (spectator strands run parallel one unit away, so such a disc exists; the full-height block
rectangle is NOT admissible: `ArcCover` forbids spectators).  For the length-changing patterns the comparison
diagram is a vertex-moved copy `D` of `realize W` (same shadow structure, the active strand's interior vertices
moved inside the disc, the removed crossings gone, everything else literally equal: `MoveMatch` with the
identity), whose named record is that of `realize W'` (record core U2, "active set" variant). -/

/-- LEAF (ng:front-III, sm-3:1995-2003 "an actual ordinary Reidemeister-III configuration ... The three
over/under choices give one strict height order ... Each physical pair crosses on both sides with the same
over/under bit and transported arrows"): the two standard realizations (same length, no cusp letter, so the
spectators are literally identical horizontal pieces) form an `RIII` site in the band disc
`[x_k, x_{k+3}] × [−(m+2)−ε, −m+ε]`; the arcs are the three strands entering at positions `m, m+1, m+2`,
named by height, the visit order along each arc reversed.  Either direction of `IsTypeIII` (the data are
symmetric in the two diagrams). -/
theorem typeIII_site {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    ∃ U : Set Plane, Nonempty (RIIIData U (realize W).diagram (realize W').diagram) := sorry

/-- LEAF (ng:front-II, sm-3:1979-1984 "the through-strand is under at both crossings [or over at both] ...
After rounding the cusp, the arcs bound an empty ordinary bigon with one common over-strand: an oriented
Reidemeister-II site"): a diagram `D` — `realize W` with the through-strand's two interior vertices in the
block lifted past the cusp arms — related to `realize W` by `RII` (the bigon disappears) and carrying the
named record of `realize W'` (no crossing left in the block; exterior visits and the block's connections of
the boundary slots agree).  All four variants of `IsTypeII` (right-cusp versions: the same strands backwards). -/
theorem typeII_move {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    ∃ D : Diagram, RII D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-- LEAF (ng:front-I, sm-3:1955-1963 "After rounding its two cusps, the unique crossing bounds an empty
ordinary monogon"): a diagram `D` — `realize W` with the curl's vertices moved so that the strand runs
through the block crossing-free — related to `realize W` by `RI` (the kink) and carrying the named record of
`realize W' = realize (X ++ Y)`. -/
theorem typeI_move {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-- LEAF (ng:deletions, sm-3:2027-2033 "a cusp whose own arms cross once.  Replace it by the uncrossed cusp
with the same two oriented boundary attachments.  After rounding, ordinary Reidemeister I deletes its empty
monogon"): a diagram `D` — `realize W` with the arms' interior vertices exchanged so that they no longer
cross — related to `realize W` by `RI` (a kink of sign −1) and carrying the named record of `realize W'`
(`l_i (!d)`: the bit flip is the arms' exchange of exits). -/
theorem crossedCusp_move {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-! ### L-PL (unit U7) — the planarity fact for an arbitrary PL union of standard circles -/

section u7_helpers

/-! ### U7 helpers: PL chains as graphs of continuous functions -/

/-- The closed segment from `x` to `y`, as the image of `[0,1]`. -/
def u7_seg (x y : Plane) : Set Plane := (fun t : ℝ => x + t • (y - x)) '' Set.Icc (0 : ℝ) 1

theorem u7_mem_seg_iff {x y p : Plane} :
    p ∈ u7_seg x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = x + t • (y - x) := by
  simp only [u7_seg, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩

theorem u7_seg_symm (x y : Plane) : u7_seg x y = u7_seg y x := by
  ext p
  simp only [u7_mem_seg_iff]
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> simp <;> ring
  · rintro ⟨t, h0, h1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> simp <;> ring

theorem u7_seg_isCompact (x y : Plane) : IsCompact (u7_seg x y) :=
  isCompact_Icc.image (by fun_prop)

theorem u7_left_mem_seg (x y : Plane) : x ∈ u7_seg x y :=
  u7_mem_seg_iff.2 ⟨0, le_rfl, zero_le_one, by simp⟩

theorem u7_right_mem_seg (x y : Plane) : y ∈ u7_seg x y :=
  u7_mem_seg_iff.2 ⟨1, zero_le_one, le_rfl, by simp⟩

/-- The x-range of a segment whose endpoints are ordered by `x`. -/
theorem u7_seg_fst_mem {x y p : Plane} (hxy : x.1 ≤ y.1) (hp : p ∈ u7_seg x y) :
    x.1 ≤ p.1 ∧ p.1 ≤ y.1 := by
  obtain ⟨t, h0, h1, rfl⟩ := u7_mem_seg_iff.1 hp
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
  constructor <;> nlinarith

/-- On a nonvertical segment the x-coordinate determines the point. -/
theorem u7_seg_eq_of_fst_eq {x y p q : Plane} (hxy : x.1 ≠ y.1) (hp : p ∈ u7_seg x y)
    (hq : q ∈ u7_seg x y) (h : p.1 = q.1) : p = q := by
  obtain ⟨t, -, -, rfl⟩ := u7_mem_seg_iff.1 hp
  obtain ⟨u, -, -, rfl⟩ := u7_mem_seg_iff.1 hq
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at h
  have hne : y.1 - x.1 ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have : t = u := mul_right_cancel₀ hne (by linarith)
  rw [this]

/-- The polygonal chain through `v 0, …, v n`. -/
def u7_chain (v : ℕ → Plane) (n : ℕ) : Set Plane := ⋃ j ∈ Set.Iio n, u7_seg (v j) (v (j + 1))

theorem u7_mem_chain_iff {v : ℕ → Plane} {n : ℕ} {p : Plane} :
    p ∈ u7_chain v n ↔ ∃ j, j < n ∧ p ∈ u7_seg (v j) (v (j + 1)) := by
  simp only [u7_chain, Set.mem_iUnion, Set.mem_Iio, exists_prop]

theorem u7_chain_isCompact (v : ℕ → Plane) (n : ℕ) : IsCompact (u7_chain v n) :=
  (Set.finite_Iio n).isCompact_biUnion fun _ _ => u7_seg_isCompact _ _

theorem u7_chain_lt {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    {a b : ℕ} (hab : a < b) (hb : b ≤ n) : (v a).1 < (v b).1 := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  induction d with
  | zero => exact hv a (by omega)
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hv (a + d + 1) (by omega)
    rw [show a + (d + 1) + 1 = a + d + 1 + 1 by ring]
    exact h1.trans h2

theorem u7_chain_strictMono {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    StrictMonoOn (fun j => (v j).1) (Set.Iic n) := fun _ _ _ hb hab =>
  u7_chain_lt hv hab (Set.mem_Iic.1 hb)

theorem u7_chain_mono {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) : (v a).1 ≤ (v b).1 := by
  rcases hab.lt_or_eq with h | rfl
  · exact (u7_chain_lt hv h hb).le
  · exact le_rfl

theorem u7_chain_injOn {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    Set.InjOn Prod.fst (u7_chain v n) := by
  intro p hp q hq hpq
  obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
  obtain ⟨j', hj', hqj⟩ := u7_mem_chain_iff.1 hq
  wlog hle : j ≤ j' generalizing p q j j'
  · exact (this hq hp hpq.symm j' hj' hqj j hj hpj (by omega)).symm
  rcases hle.lt_or_eq with hlt | rfl
  · have h1 := u7_seg_fst_mem (hv j hj).le hpj
    have h2 := u7_seg_fst_mem (hv j' hj').le hqj
    have h3 : (v (j + 1)).1 ≤ (v j').1 := u7_chain_mono hv hlt hj'.le
    have e1 : p.1 = (v (j + 1)).1 := by linarith
    have e2 : q.1 = (v j').1 := by linarith
    have hp' : p = v (j + 1) := u7_seg_eq_of_fst_eq (hv j hj).ne hpj (u7_right_mem_seg _ _) e1
    have hq' : q = v j' := u7_seg_eq_of_fst_eq (hv j' hj').ne hqj (u7_left_mem_seg _ _) e2
    have hjj : j + 1 = j' := by
      by_contra hne
      have hlt' : j + 1 < j' := by omega
      have := (u7_chain_strictMono hv) (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hj'.le) hlt'
      simp only at this
      linarith
    rw [hp', hq', hjj]
  · exact u7_seg_eq_of_fst_eq (hv j hj).ne hpj hqj hpq

theorem u7_chain_fst_subset {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    Prod.fst '' u7_chain v n ⊆ Set.Icc (v 0).1 (v n).1 := by
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
  have h1 := u7_seg_fst_mem (hv j hj).le hpj
  have h2 := u7_chain_mono hv (Nat.zero_le j) hj.le
  have h3 := u7_chain_mono hv (Nat.succ_le_of_lt hj) le_rfl
  exact ⟨by linarith, by linarith⟩

theorem u7_chain_exists_piece {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Icc (v 0).1 (v n).1) :
    ∃ j, j < n ∧ (v j).1 ≤ x ∧ x ≤ (v (j + 1)).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hxn : x ≤ (v n).1
    · rcases Nat.eq_zero_or_pos n with rfl | hn'
      · exact ⟨0, by omega, hx.1, hx.2⟩
      · obtain ⟨j, hj, h1, h2⟩ := ih (fun j hj => hv j (by omega)) hn' ⟨hx.1, hxn⟩
        exact ⟨j, by omega, h1, h2⟩
    · exact ⟨n, by omega, (not_le.1 hxn).le, hx.2⟩

theorem u7_chain_fst_image {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    (hn : 0 < n) : Prod.fst '' u7_chain v n = Set.Icc (v 0).1 (v n).1 := by
  refine Set.Subset.antisymm (u7_chain_fst_subset hv) ?_
  intro x hx
  obtain ⟨j, hj, h1, h2⟩ := u7_chain_exists_piece hv hn hx
  have hd : 0 < (v (j + 1)).1 - (v j).1 := sub_pos.2 (hv j hj)
  refine ⟨v j + ((x - (v j).1) / ((v (j + 1)).1 - (v j).1)) • (v (j + 1) - v j), ?_, ?_⟩
  · exact u7_mem_chain_iff.2 ⟨j, hj, u7_mem_seg_iff.2
      ⟨_, div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith), rfl⟩⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    field_simp
    ring

/-- A compact set that is the graph of a function over `Icc a b` is the graph of a continuous
function (compact → Hausdorff bijections are homeomorphisms). -/
theorem u7_exists_graphFun {K : Set Plane} {a b : ℝ} (hab : a ≤ b) (hK : IsCompact K)
    (hinj : Set.InjOn Prod.fst K) (himg : Prod.fst '' K = Set.Icc a b) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x ∈ Set.Icc a b, (x, f x) ∈ K) ∧ (∀ p ∈ K, f p.1 = p.2) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let φ : K → Set.Icc a b := fun p => ⟨p.1.1, himg ▸ Set.mem_image_of_mem Prod.fst p.2⟩
  have hφc : Continuous φ := Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
  have hφinj : Function.Injective φ := by
    intro p q hpq
    exact Subtype.ext (hinj p.2 q.2 (congrArg Subtype.val hpq))
  have hφsurj : Function.Surjective φ := by
    intro x
    have hx : (x : ℝ) ∈ Prod.fst '' K := by rw [himg]; exact x.2
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨⟨p, hp⟩, Subtype.ext hpx⟩
  let e : K ≃ Set.Icc a b := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hec : Continuous e := hφc
  let h : K ≃ₜ Set.Icc a b := hec.homeoOfEquivCompactToT2
  have h1 : ∀ p : K, ((h p : Set.Icc a b) : ℝ) = (p.1).1 := fun p => rfl
  have hkey : ∀ x ∈ Set.Icc a b, ((h.symm (Set.projIcc a b hab x)).1).1 = x := by
    intro x hx
    have := h1 (h.symm (Set.projIcc a b hab x))
    rw [h.apply_symm_apply] at this
    rw [← this]
    exact congrArg Subtype.val (Set.projIcc_of_mem hab hx)
  have hmem : ∀ x ∈ Set.Icc a b, (x, ((h.symm (Set.projIcc a b hab x)).1).2) ∈ K := by
    intro x hx
    have hp := (h.symm (Set.projIcc a b hab x)).2
    rw [show (x, ((h.symm (Set.projIcc a b hab x)).1).2) = (h.symm (Set.projIcc a b hab x)).1 from
      Prod.ext (hkey x hx).symm rfl]
    exact hp
  refine ⟨fun x => ((h.symm (Set.projIcc a b hab x)).1).2, ?_, hmem, ?_⟩
  · exact continuous_snd.comp (continuous_subtype_val.comp (h.symm.continuous.comp continuous_projIcc))
  · intro p hp
    have hx : p.1 ∈ Set.Icc a b := himg ▸ ⟨p, hp, rfl⟩
    have := hinj (hmem p.1 hx) hp rfl
    have h2 : ((p.1, ((h.symm (Set.projIcc a b hab p.1)).1).2) : Plane).2 = p.2 := congrArg Prod.snd this
    exact h2


/-! ### U7 helpers: PL-front facts -/

variable (F : PLFront)

/-- The segment of a strand `⟨i, m⟩` as `u7_seg` between its two vertices. -/
theorem u7_seg_eq (i : Fin F.Γ.c) (m : ZMod (F.Γ.comp i).k) :
    F.Γ.seg ⟨i, m⟩ = u7_seg ((F.Γ.comp i).P m) ((F.Γ.comp i).P (m + 1)) := by
  ext p
  rw [Shadow.seg_mk, u7_mem_seg_iff]
  simp only [edgeSegment, edgePoint, edge, Set.mem_ofPred_eq]

/-- Along a run of vertices none of which is a cusp, the rightward bit is constant. -/
theorem u7_xdir_run (i : Fin F.Γ.c) (a : ZMod (F.Γ.comp i).k) (n : ℕ)
    (hno : ∀ j : ℕ, 0 < j → j < n → ¬ F.IsCusp ⟨i, a + j⟩) :
    ∀ j : ℕ, j < n → F.xdir ⟨i, a + j⟩ = F.xdir ⟨i, a⟩ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hnc := hno (j + 1) (Nat.succ_pos j) hj
    have h := F.xdir_prev_eq_of_not_isCusp hnc
    have hprev : F.prev ⟨i, a + ((j + 1 : ℕ) : ZMod (F.Γ.comp i).k)⟩ = ⟨i, a + j⟩ := by
      simp only [PLFront.prev, Nat.cast_succ]
      congr 1
      ring
    rw [hprev] at h
    rw [← h]
    exact ih (by omega)

/-- A vertex at which the rightward bit changes is a cusp. -/
theorem u7_isCusp_of_xdir_ne {s : F.Γ.Strand} (h : F.xdir (F.prev s) ≠ F.xdir s) : F.IsCusp s := by
  by_contra hc
  exact h (F.xdir_prev_eq_of_not_isCusp hc)

/-- The two arms of a cusp meet only at the cusp vertex (they are not collinear). -/
theorem u7_seg_prev_inter_cusp {s : F.Γ.Strand} (h : F.IsCusp s) {p : Plane}
    (hp : p ∈ F.Γ.seg (F.prev s)) (hq : p ∈ F.Γ.seg s) : p = F.Γ.tail s := by
  obtain ⟨i, m⟩ := s
  have hprev : F.prev ⟨i, m⟩ = ⟨i, m - 1⟩ := rfl
  rw [hprev, u7_seg_eq, sub_add_cancel] at hp
  rw [u7_seg_eq] at hq
  obtain ⟨t₁, -, -, hp'⟩ := u7_mem_seg_iff.1 hp
  obtain ⟨t₂, -, -, hq'⟩ := u7_mem_seg_iff.1 hq
  set P := (F.Γ.comp i).P with hP
  have hIn : F.eIn ⟨i, m⟩ = P m - P (m - 1) := by
    show F.Γ.dir ⟨i, m - 1⟩ = P m - P (m - 1)
    rw [Shadow.dir_mk]
    simp only [edge, hP]
    rw [sub_add_cancel]
  have hOut : F.eOut ⟨i, m⟩ = P (m + 1) - P m := rfl
  have hdet := F.cusp_det_ne_zero h
  rw [hIn, hOut] at hdet
  have hrel : (t₁ - 1) • (P m - P (m - 1)) = t₂ • (P (m + 1) - P m) := by
    have e := hp'.symm.trans hq'
    ext
    · have := congrArg Prod.fst e
      simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at this ⊢
      linarith
    · have := congrArg Prod.snd e
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul] at this ⊢
      linarith
  have hdet0 : t₂ * det (P m - P (m - 1)) (P (m + 1) - P m) = 0 := by
    have h3 : det (P m - P (m - 1)) (t₂ • (P (m + 1) - P m)) =
        t₂ * det (P m - P (m - 1)) (P (m + 1) - P m) := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [← h3, ← hrel]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    ring
  have ht₂ : t₂ = 0 := by
    rcases mul_eq_zero.1 hdet0 with h0 | h0
    · exact h0
    · exact absurd h0 hdet
  rw [hq', ht₂, zero_smul, add_zero]
  rfl


/-- The planarity fact on one component: with a unique left cusp `⟨i, ℓ⟩`, a unique right cusp `⟨i, r⟩`
and no crossing, the left cusp is downward iff the right cusp is not.  The two x-monotone arcs are graphs
of continuous functions over `[a, b]` whose difference never vanishes inside, so its sign at the two
ends agrees; the sign at each end is read off the arm heights (`isDownCusp_iff_armIn_above`). -/
theorem u7_down_iff_not_down (h : F.IsStandardCircles) (i : Fin F.Γ.c) (ℓ r : ZMod (F.Γ.comp i).k)
    (hL : F.IsLeftCusp ⟨i, ℓ⟩) (hR : F.IsRightCusp ⟨i, r⟩)
    (hLu : ∀ m, F.IsLeftCusp ⟨i, m⟩ → m = ℓ) (hRu : ∀ m, F.IsRightCusp ⟨i, m⟩ → m = r) :
    (F.IsDownCusp ⟨i, ℓ⟩ ↔ ¬ F.IsDownCusp ⟨i, r⟩) := by
  classical
  have hcusp : ∀ m, F.IsCusp ⟨i, m⟩ → m = ℓ ∨ m = r := fun m hm => by
    rcases (F.isCusp_iff _).1 hm with hl | hr
    · exact Or.inl (hLu m hl)
    · exact Or.inr (hRu m hr)
  have hℓr : ℓ ≠ r := by
    intro e
    subst e
    exact F.not_isLeftCusp_and_isRightCusp _ ⟨hL, hR⟩
  -- the number of rightward strands `n` and of leftward strands `m`
  set n := (r - ℓ).val with hn
  have hnk : n < (F.Γ.comp i).k := ZMod.val_lt _
  have hn0 : 0 < n := ZMod.val_pos.2 (sub_ne_zero.2 hℓr.symm)
  have hncast : (n : ZMod (F.Γ.comp i).k) = r - ℓ := ZMod.natCast_zmod_val _
  set m := (F.Γ.comp i).k - n with hm
  have hm0 : 0 < m := by omega
  have hmcast : (m : ZMod (F.Γ.comp i).k) = ℓ - r := by
    rw [hm, Nat.cast_sub hnk.le, ZMod.natCast_self, hncast]; ring
  have hcast_inj : ∀ j j' : ℕ, j < (F.Γ.comp i).k → j' < (F.Γ.comp i).k →
      (j : ZMod (F.Γ.comp i).k) = j' → j = j' := fun j j' hj hj' e => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at e
    exact e
  -- the rightward bits along the two runs
  have hA : ∀ j : ℕ, j < n → F.xdir ⟨i, ℓ + j⟩ = true := by
    have hrun := u7_xdir_run F i ℓ n (fun j hj0 hjn hc => by
      rcases hcusp _ hc with e | e
      · have e' : (j : ZMod (F.Γ.comp i).k) = ((0 : ℕ) : ZMod (F.Γ.comp i).k) := by
          rw [Nat.cast_zero]; exact (add_eq_left).1 e
        have := hcast_inj j 0 (by omega) (by omega) e'
        omega
      · have e' : (j : ZMod (F.Γ.comp i).k) = (n : ZMod (F.Γ.comp i).k) := by
          rw [hncast]; exact eq_sub_of_add_eq' e
        have := hcast_inj j n (by omega) hnk e'
        omega)
    intro j hj
    rw [hrun j hj]
    exact (F.xdir_eq_true_iff _).2 hL.2
  have hB : ∀ j : ℕ, j < m → F.xdir ⟨i, r + j⟩ = false := by
    have hrun := u7_xdir_run F i r m (fun j hj0 hjm hc => by
      rcases hcusp _ hc with e | e
      · have e' : (j : ZMod (F.Γ.comp i).k) = (m : ZMod (F.Γ.comp i).k) := by
          rw [hmcast]; exact eq_sub_of_add_eq' e
        have := hcast_inj j m (by omega) (by omega) e'
        omega
      · have e' : (j : ZMod (F.Γ.comp i).k) = ((0 : ℕ) : ZMod (F.Γ.comp i).k) := by
          rw [Nat.cast_zero]; exact (add_eq_left).1 e
        have := hcast_inj j 0 (by omega) (by omega) e'
        omega)
    intro j hj
    rw [hrun j hj]
    exact (F.xdir_eq_false_iff _).2 hR.2
  -- the two vertex chains
  set vA : ℕ → Plane := fun j => (F.Γ.comp i).P (ℓ + j) with hvAdef
  set vB : ℕ → Plane := fun j => (F.Γ.comp i).P (r + ((m - j : ℕ) : ZMod (F.Γ.comp i).k)) with hvBdef
  have hdirA : ∀ j : ℕ, F.Γ.dir ⟨i, ℓ + j⟩ = (F.Γ.comp i).P (ℓ + j + 1) - (F.Γ.comp i).P (ℓ + j) :=
    fun j => rfl
  have hdirB : ∀ j : ℕ, F.Γ.dir ⟨i, r + j⟩ = (F.Γ.comp i).P (r + j + 1) - (F.Γ.comp i).P (r + j) :=
    fun j => rfl
  have hvA : ∀ j, j < n → (vA j).1 < (vA (j + 1)).1 := fun j hj => by
    have hx := (F.xdir_eq_true_iff ⟨i, ℓ + j⟩).1 (hA j hj)
    rw [hdirA] at hx
    simp only [hvAdef, Nat.cast_succ, ← add_assoc]
    simp only [Prod.fst_sub] at hx
    linarith
  have hvB : ∀ j, j < m → (vB j).1 < (vB (j + 1)).1 := fun j hj => by
    have e1 : m - j = (m - (j + 1)) + 1 := by omega
    have hx := (F.xdir_eq_false_iff ⟨i, r + ((m - (j + 1) : ℕ) : ZMod (F.Γ.comp i).k)⟩).1
      (hB _ (by omega))
    rw [hdirB] at hx
    simp only [hvBdef]
    rw [e1, Nat.cast_succ, ← add_assoc]
    simp only [Prod.fst_sub] at hx
    linarith
  -- the strands' segments are the chain pieces
  have hsegA : ∀ j : ℕ, F.Γ.seg ⟨i, ℓ + j⟩ = u7_seg (vA j) (vA (j + 1)) := fun j => by
    rw [u7_seg_eq]
    simp only [hvAdef, Nat.cast_succ, ← add_assoc]
  have hsegB : ∀ j : ℕ, j < m →
      F.Γ.seg ⟨i, r + ((m - (j + 1) : ℕ) : ZMod (F.Γ.comp i).k)⟩ = u7_seg (vB j) (vB (j + 1)) :=
    fun j hj => by
    rw [u7_seg_eq, u7_seg_symm]
    simp only [hvBdef]
    rw [show m - j = (m - (j + 1)) + 1 by omega, Nat.cast_succ, ← add_assoc]
  set KA := u7_chain vA n with hKA
  set KB := u7_chain vB m with hKB
  have hKA_mem : ∀ p ∈ KA, ∃ j, j < n ∧ p ∈ F.Γ.seg ⟨i, ℓ + j⟩ := fun p hp => by
    obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
    exact ⟨j, hj, by rw [hsegA j]; exact hpj⟩
  have hKB_mem : ∀ p ∈ KB, ∃ j, j < m ∧ p ∈ F.Γ.seg ⟨i, r + j⟩ := fun p hp => by
    obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
    exact ⟨m - (j + 1), by omega, by rw [hsegB j hj]; exact hpj⟩
  -- endpoints
  have hvA0 : vA 0 = (F.Γ.comp i).P ℓ := by simp [hvAdef]
  have hvAn : vA n = (F.Γ.comp i).P r := by
    simp only [hvAdef]; rw [hncast]; congr 1; ring
  have hvB0 : vB 0 = (F.Γ.comp i).P ℓ := by
    simp only [hvBdef, Nat.sub_zero]; rw [hmcast]; congr 1; ring
  have hvBm : vB m = (F.Γ.comp i).P r := by simp [hvBdef]
  set a := ((F.Γ.comp i).P ℓ).1 with ha
  set b := ((F.Γ.comp i).P r).1 with hb
  have hab : a < b := by
    have := u7_chain_lt hvA hn0 le_rfl
    rwa [hvA0, hvAn] at this
  obtain ⟨fA, hfAc, hfA1, hfA2⟩ := u7_exists_graphFun hab.le (u7_chain_isCompact vA n)
    (u7_chain_injOn hvA) (by rw [u7_chain_fst_image hvA hn0, hvA0, hvAn])
  obtain ⟨fB, hfBc, hfB1, hfB2⟩ := u7_exists_graphFun hab.le (u7_chain_isCompact vB m)
    (u7_chain_injOn hvB) (by rw [u7_chain_fst_image hvB hm0, hvB0, hvBm])
  set g : ℝ → ℝ := fun x => fB x - fA x with hg
  have hgc : Continuous g := hfBc.sub hfAc
  -- (B) the two arcs never meet strictly between the cusps: no crossing, and adjacent strands of
  -- opposite bits meet at a cusp vertex only
  have hg0 : ∀ x ∈ Set.Ioo a b, g x ≠ 0 := by
    intro x hx hgx
    have hxI : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
    have hpA := hfA1 x hxI
    have hpB := hfB1 x hxI
    have heq : fB x = fA x := sub_eq_zero.1 hgx
    rw [heq] at hpB
    obtain ⟨j, hj, hpj⟩ := hKA_mem _ hpA
    obtain ⟨j', hj', hpj'⟩ := hKB_mem _ hpB
    have hs : F.xdir ⟨i, ℓ + j⟩ = true := hA j hj
    have ht : F.xdir ⟨i, r + j'⟩ = false := hB j' hj'
    have hvertex : ∀ q : ZMod (F.Γ.comp i).k, ((x, fA x) : Plane) = (F.Γ.comp i).P q →
        F.IsCusp ⟨i, q⟩ → False := by
      intro q hpq hc
      have hx1 : x = ((F.Γ.comp i).P q).1 := congrArg Prod.fst hpq
      rcases hcusp q hc with e | e
      · rw [e] at hx1
        exact absurd hx1 (ne_of_gt hx.1)
      · rw [e] at hx1
        exact absurd hx1 (ne_of_lt hx.2)
    by_cases hadj : F.Γ.Adjacent ⟨i, ℓ + j⟩ ⟨i, r + j'⟩
    · rw [Shadow.adjacent_mk_iff] at hadj
      rcases hadj with h1 | h1 | h1
      · have e : r + (j' : ZMod (F.Γ.comp i).k) = ℓ + j - 1 := by linear_combination h1
        have hts : (⟨i, r + j'⟩ : F.Γ.Strand) = F.prev ⟨i, ℓ + j⟩ := by
          show _ = (⟨i, ℓ + j - 1⟩ : F.Γ.Strand)
          rw [e]
        have hc : F.IsCusp ⟨i, ℓ + j⟩ := u7_isCusp_of_xdir_ne F (by rw [← hts, ht, hs]; decide)
        have hp := u7_seg_prev_inter_cusp F hc (by rw [← hts]; exact hpj') hpj
        exact hvertex _ hp hc
      · have e : r + (j' : ZMod (F.Γ.comp i).k) = ℓ + j := by linear_combination h1
        rw [e, hs] at ht
        exact Bool.noConfusion ht
      · have e : ℓ + (j : ZMod (F.Γ.comp i).k) = r + j' - 1 := by
          linear_combination (-1 : ZMod (F.Γ.comp i).k) * h1
        have hst : (⟨i, ℓ + j⟩ : F.Γ.Strand) = F.prev ⟨i, r + j'⟩ := by
          show _ = (⟨i, r + j' - 1⟩ : F.Γ.Strand)
          rw [e]
        have hc : F.IsCusp ⟨i, r + j'⟩ := u7_isCusp_of_xdir_ne F (by rw [← hst, ht, hs]; decide)
        have hp := u7_seg_prev_inter_cusp F hc (by rw [← hst]; exact hpj) hpj'
        exact hvertex _ hp hc
    · have hcr : F.Γ.IsCrossing {⟨i, ℓ + j⟩, ⟨i, r + j'⟩} :=
        F.Γ.isCrossing_pair hadj ⟨_, hpj, hpj'⟩
      exact h.1.elim (⟨_, hcr⟩ : F.Γ.Crossing)
  -- (C) hence `g` has constant sign on `(a, b)` (intermediate value theorem)
  have hsign : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, 0 < g x → 0 < g y := by
    intro x hx y hy hgx
    by_contra hgy
    have hgy' : g y < 0 := lt_of_le_of_ne (not_lt.1 hgy) (hg0 y hy)
    obtain ⟨z, hz, hz0⟩ :=
      isPreconnected_Ioo.intermediate_value hy hx hgc.continuousOn ⟨hgy'.le, hgx.le⟩
    exact hg0 z hz hz0
  -- (D) the sign near the left cusp reads the arm heights there
  have hLc := hL.isCusp
  set e₁ := F.eOut ⟨i, ℓ⟩ with he₁
  set e₂ := F.armIn ⟨i, ℓ⟩ with he₂
  have he₁1 : 0 < e₁.1 := hL.2
  have he₂1 : 0 < e₂.1 := by
    have := hL.1
    simp only [he₂, PLFront.armIn, Prod.fst_neg]
    linarith
  have he₁def : e₁ = (F.Γ.comp i).P (ℓ + 1) - (F.Γ.comp i).P ℓ := rfl
  have he₂def : e₂ = (F.Γ.comp i).P (ℓ - 1) - (F.Γ.comp i).P ℓ := by
    show -(F.Γ.dir ⟨i, ℓ - 1⟩) = _
    rw [Shadow.dir_mk]
    simp only [edge]
    rw [sub_add_cancel, neg_sub]
  set δ := min e₁.1 e₂.1 / 2 with hδ
  have hmin : 0 < min e₁.1 e₂.1 := lt_min he₁1 he₂1
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < e₁.1 := by have := min_le_left e₁.1 e₂.1; rw [hδ]; linarith
  have hδ2 : δ < e₂.1 := by have := min_le_right e₁.1 e₂.1; rw [hδ]; linarith
  have hpA : ((F.Γ.comp i).P ℓ + (δ / e₁.1) • e₁) ∈ KA := by
    refine u7_mem_chain_iff.2 ⟨0, hn0, ?_⟩
    rw [← hsegA 0, Nat.cast_zero, add_zero, u7_seg_eq]
    exact u7_mem_seg_iff.2 ⟨δ / e₁.1, div_nonneg hδ0.le he₁1.le, (div_le_one he₁1).2 hδ1.le, rfl⟩
  have hpB : ((F.Γ.comp i).P ℓ + (δ / e₂.1) • e₂) ∈ KB := by
    refine u7_mem_chain_iff.2 ⟨0, hm0, ?_⟩
    rw [← hsegB 0 hm0]
    have e : r + ((m - (0 + 1) : ℕ) : ZMod (F.Γ.comp i).k) = ℓ - 1 := by
      rw [Nat.zero_add, Nat.cast_pred hm0, hmcast]; ring
    rw [e, u7_seg_eq, sub_add_cancel, u7_seg_symm]
    exact u7_mem_seg_iff.2 ⟨δ / e₂.1, div_nonneg hδ0.le he₂1.le, (div_le_one he₂1).2 hδ2.le,
      by rw [he₂def]⟩
  have hfAδ : fA (a + δ) = ((F.Γ.comp i).P ℓ).2 + (δ / e₁.1) * e₁.2 := by
    have h1 := hfA2 _ hpA
    have hx : ((F.Γ.comp i).P ℓ + (δ / e₁.1) • e₁).1 = a + δ := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_mul_cancel₀ _ he₁1.ne']
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hfBδ : fB (a + δ) = ((F.Γ.comp i).P ℓ).2 + (δ / e₂.1) * e₂.2 := by
    have h1 := hfB2 _ hpB
    have hx : ((F.Γ.comp i).P ℓ + (δ / e₂.1) • e₂).1 = a + δ := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_mul_cancel₀ _ he₂1.ne']
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hgδ : g (a + δ) = δ * (PLFront.armHeight e₂ - PLFront.armHeight e₁) := by
    simp only [hg, hfAδ, hfBδ, PLFront.armHeight, abs_of_pos he₁1, abs_of_pos he₂1]
    ring
  have hL_iff : F.IsDownCusp ⟨i, ℓ⟩ ↔ 0 < g (a + δ) := by
    rw [F.isDownCusp_iff_armIn_above hLc, hgδ]
    show PLFront.armHeight e₁ < PLFront.armHeight e₂ ↔ _
    constructor
    · intro hlt
      exact mul_pos hδ0 (sub_pos.2 hlt)
    · intro hpos
      by_contra hle
      have := mul_nonneg hδ0.le (sub_nonneg.2 (not_lt.1 hle))
      linarith
  have haδ : a + δ ∈ Set.Ioo a b := by
    refine ⟨by linarith, ?_⟩
    have h1 : (vA 1).1 = a + e₁.1 := by
      simp only [hvAdef, Nat.cast_one, he₁def, Prod.fst_sub]
      rw [ha]; ring
    have h2 := u7_chain_mono hvA (show 1 ≤ n from hn0) le_rfl
    rw [hvAn] at h2
    linarith [hb]
  -- (E) the sign near the right cusp reads the arm heights there
  have hRc := hR.isCusp
  set e₃ := F.eOut ⟨i, r⟩ with he₃
  set e₄ := F.armIn ⟨i, r⟩ with he₄
  have he₃1 : e₃.1 < 0 := hR.2
  have he₄1 : e₄.1 < 0 := by
    have := hR.1
    simp only [he₄, PLFront.armIn, Prod.fst_neg]
    linarith
  have he₃def : e₃ = (F.Γ.comp i).P (r + 1) - (F.Γ.comp i).P r := rfl
  have he₄def : e₄ = (F.Γ.comp i).P (r - 1) - (F.Γ.comp i).P r := by
    show -(F.Γ.dir ⟨i, r - 1⟩) = _
    rw [Shadow.dir_mk]
    simp only [edge]
    rw [sub_add_cancel, neg_sub]
  set δ' := min (-e₃.1) (-e₄.1) / 2 with hδ'
  have hmin' : 0 < min (-e₃.1) (-e₄.1) := lt_min (by linarith) (by linarith)
  have hδ'0 : 0 < δ' := by rw [hδ']; linarith
  have hδ'3 : δ' < -e₃.1 := by have := min_le_left (-e₃.1) (-e₄.1); rw [hδ']; linarith
  have hδ'4 : δ' < -e₄.1 := by have := min_le_right (-e₃.1) (-e₄.1); rw [hδ']; linarith
  have hpB' : ((F.Γ.comp i).P r + (δ' / (-e₃.1)) • e₃) ∈ KB := by
    refine u7_mem_chain_iff.2 ⟨m - 1, by omega, ?_⟩
    rw [← hsegB (m - 1) (by omega)]
    have e : r + ((m - (m - 1 + 1) : ℕ) : ZMod (F.Γ.comp i).k) = r := by
      rw [show m - (m - 1 + 1) = 0 by omega, Nat.cast_zero, add_zero]
    rw [e, u7_seg_eq]
    exact u7_mem_seg_iff.2 ⟨δ' / (-e₃.1), div_nonneg hδ'0.le (by linarith),
      (div_le_one (by linarith)).2 hδ'3.le, rfl⟩
  have hpA' : ((F.Γ.comp i).P r + (δ' / (-e₄.1)) • e₄) ∈ KA := by
    refine u7_mem_chain_iff.2 ⟨n - 1, by omega, ?_⟩
    rw [← hsegA (n - 1)]
    have e : ℓ + ((n - 1 : ℕ) : ZMod (F.Γ.comp i).k) = r - 1 := by
      rw [Nat.cast_pred hn0, hncast]; ring
    rw [e, u7_seg_eq, sub_add_cancel, u7_seg_symm]
    exact u7_mem_seg_iff.2 ⟨δ' / (-e₄.1), div_nonneg hδ'0.le (by linarith),
      (div_le_one (by linarith)).2 hδ'4.le, by rw [he₄def]⟩
  have hfBδ' : fB (b - δ') = ((F.Γ.comp i).P r).2 + (δ' / (-e₃.1)) * e₃.2 := by
    have h1 := hfB2 _ hpB'
    have hx : ((F.Γ.comp i).P r + (δ' / (-e₃.1)) • e₃).1 = b - δ' := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_neg, neg_mul, div_mul_cancel₀ _ he₃1.ne, ← sub_eq_add_neg]
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hfAδ' : fA (b - δ') = ((F.Γ.comp i).P r).2 + (δ' / (-e₄.1)) * e₄.2 := by
    have h1 := hfA2 _ hpA'
    have hx : ((F.Γ.comp i).P r + (δ' / (-e₄.1)) • e₄).1 = b - δ' := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_neg, neg_mul, div_mul_cancel₀ _ he₄1.ne, ← sub_eq_add_neg]
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hgδ' : g (b - δ') = δ' * (PLFront.armHeight e₃ - PLFront.armHeight e₄) := by
    simp only [hg, hfAδ', hfBδ', PLFront.armHeight, abs_of_neg he₃1, abs_of_neg he₄1]
    ring
  have hR_iff : F.IsDownCusp ⟨i, r⟩ ↔ g (b - δ') < 0 := by
    rw [F.isDownCusp_iff_armIn_above hRc, hgδ']
    show PLFront.armHeight e₃ < PLFront.armHeight e₄ ↔ _
    constructor
    · intro hlt
      exact mul_neg_of_pos_of_neg hδ'0 (sub_neg.2 hlt)
    · intro hneg
      by_contra hle
      have := mul_nonneg hδ'0.le (sub_nonneg.2 (not_lt.1 hle))
      linarith
  have hbδ' : b - δ' ∈ Set.Ioo a b := by
    refine ⟨?_, by linarith⟩
    have h1 : (vA (n - 1)).1 = b + e₄.1 := by
      simp only [hvAdef]
      rw [Nat.cast_pred hn0, hncast, he₄def, Prod.fst_sub,
        show ℓ + (r - ℓ - 1) = r - 1 by ring, hb]
      ring
    have h2 := u7_chain_mono hvA (Nat.zero_le (n - 1)) (Nat.sub_le n 1)
    rw [hvA0] at h2
    linarith [ha]
  -- (F) conclusion: `L` down ↔ `g > 0` on `(a, b)` ↔ `R` not down
  constructor
  · intro hdL hdR
    have h1 := hL_iff.1 hdL
    have h2 := hR_iff.1 hdR
    have := hsign _ haδ _ hbδ' h1
    linarith
  · intro hndR
    have h2 : 0 < g (b - δ') :=
      lt_of_le_of_ne (not_lt.1 (fun hlt => hndR (hR_iff.2 hlt))) (hg0 _ hbδ').symm
    exact hL_iff.2 (hsign _ hbδ' _ haδ h2)


/-- Each component of a union of standard circles has exactly one downward cusp: its two cusps are the
unique left and right cusps, and `u7_down_iff_not_down` says exactly one of them is downward. -/
theorem u7_card_down_eq_one (h : F.IsStandardCircles) (i : Fin F.Γ.c) :
    Nat.card {s : F.Γ.Strand // s.1 = i ∧ F.IsDownCusp s} = 1 := by
  obtain ⟨hLc, hRc⟩ := h.2 i
  rw [Nat.card_eq_one_iff_unique] at hLc hRc
  obtain ⟨⟨hLsub⟩, ⟨⟨L, hLi, hL⟩⟩⟩ := hLc
  obtain ⟨⟨hRsub⟩, ⟨⟨R, hRi, hR⟩⟩⟩ := hRc
  have hLu : ∀ s, s.1 = i → F.IsLeftCusp s → s = L := fun s hs hsl =>
    congrArg Subtype.val (hLsub ⟨s, hs, hsl⟩ ⟨L, hLi, hL⟩)
  have hRu : ∀ s, s.1 = i → F.IsRightCusp s → s = R := fun s hs hsr =>
    congrArg Subtype.val (hRsub ⟨s, hs, hsr⟩ ⟨R, hRi, hR⟩)
  obtain ⟨iL, ℓ⟩ := L
  obtain ⟨iR, r⟩ := R
  simp only at hLi hRi
  subst hLi
  subst hRi
  have hiff := u7_down_iff_not_down F h iR ℓ r hL hR
    (fun q hq => by have := hLu ⟨iR, q⟩ rfl hq; simpa using this)
    (fun q hq => by have := hRu ⟨iR, q⟩ rfl hq; simpa using this)
  have hcusp : ∀ s : F.Γ.Strand, s.1 = iR → F.IsCusp s → s = ⟨iR, ℓ⟩ ∨ s = ⟨iR, r⟩ :=
    fun s hs hc => by
    rcases (F.isCusp_iff s).1 hc with hl | hr
    · exact Or.inl (hLu s hs hl)
    · exact Or.inr (hRu s hs hr)
  rw [Nat.card_eq_one_iff_unique]
  by_cases hdL : F.IsDownCusp ⟨iR, ℓ⟩
  · have hdR : ¬ F.IsDownCusp ⟨iR, r⟩ := hiff.1 hdL
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨iR, ℓ⟩, rfl, hdL⟩⟩⟩
    have ha : a.1 = ⟨iR, ℓ⟩ := by
      rcases hcusp a.1 a.2.1 a.2.2.isCusp with e | e
      · exact e
      · exact absurd (e ▸ a.2.2) hdR
    have hb : b.1 = ⟨iR, ℓ⟩ := by
      rcases hcusp b.1 b.2.1 b.2.2.isCusp with e | e
      · exact e
      · exact absurd (e ▸ b.2.2) hdR
    exact Subtype.ext (ha.trans hb.symm)
  · have hdR : F.IsDownCusp ⟨iR, r⟩ := by
      by_contra hc
      exact hdL (hiff.2 hc)
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨iR, r⟩, rfl, hdR⟩⟩⟩
    have ha : a.1 = ⟨iR, r⟩ := by
      rcases hcusp a.1 a.2.1 a.2.2.isCusp with e | e
      · exact absurd (e ▸ a.2.2) hdL
      · exact e
    have hb : b.1 = ⟨iR, r⟩ := by
      rcases hcusp b.1 b.2.1 b.2.2.isCusp with e | e
      · exact absurd (e ▸ b.2.2) hdL
      · exact e
    exact Subtype.ext (ha.trans hb.symm)

end u7_helpers

/-- LEAF (ng:circle, sm-3:2053-2054 "A simple crossing-free component with exactly one left and one right
cusp has D = 1"): on a `PLFront`, the two x-monotone PL arcs between the cusps of a component never meet, so
one lies above the other and exactly one cusp is traversed upper arm → lower arm.  (Accepted for
realizations: `FrontRealizeStandard.IsStandardCircles.downCount_eq_c`; word-layer fallback FR-11.) -/
theorem PLFront.IsStandardCircles.downCount_eq_c_general (F : PLFront) (h : F.IsStandardCircles) :
    F.downCount = F.Γ.c := by
  unfold PLFront.downCount
  rw [PLFront.card_subtype_eq_sum_comp]
  rw [Finset.sum_congr rfl fun i _ => u7_card_down_eq_one F h i]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  exact Finset.card_fin _

/-! ### L-smooth (unit U8) — the smooth clauses of row 76 -/

/-- LEAF (ng:commutation, sm-3:1934-1936 "A deformation without a singular event preserves the records, D and
w: signs, cusp directions and cyclic attachments cannot change"): `D`.  Along a jointly smooth family inside
the class, the cusp set `{x' = 0}` is a covering of `[0,1]` (`x'' ≠ 0` at every zero, vertical tangencies
excluded), on which the discriminant `x''·det(γ'', γ''')` is continuous and nonzero. -/
theorem deform_downCount (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.downCount = F'.downCount := sorry

/-- LEAF: the same for `w` (the transverse double points form a covering of `[0,1]`, no accumulation at a
semicubical cusp, `crossSign` continuous and nonzero). -/
theorem deform_writhe (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.writhe = F'.writhe := sorry

/-- LEAF: the same for the records of the roundings, hence (sm-3:1936-1937 "Lemma rp:record-polynomial gives
scalar equality") the polynomial: the `Marking` of `F` transports along the family to a `Marking` of `F'`. -/
theorem deform_P (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) (S S' : Diagram)
    (hS : F.IsRounding S) (hS' : F'.IsRounding S') : P S = P S' := sorry

/-- LEAF = THE REPRESENTATION THEOREM (ng:commutation sm-3:1924-1925, proof 1938-1947 "separate them by small
local x translations ... Reading successive vertical cuts then gives the finite elementary word"): the
block's analytic bridge (FINAL §8 risk 1; 7.5-11k lines; attacked last; rows 76 and 83 wait for it). -/
theorem represent (F : SmoothFront) : ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) := sorry

end Leaves

/-! ## Glue (all proved) -/

/-! ### Degrees -/

/-- `deg_a δ^n = n` (`degAZ_mul` in the domain `R`). -/
theorem degAZ_delta_pow (n : ℕ) : degAZ (R.delta ^ n) = n := by
  induction n with
  | zero => simp [degAZ, degA_one]
  | succ n ih =>
    rw [pow_succ, degAZ_mul (pow_ne_zero _ delta_ne_zero) delta_ne_zero, ih, degAZ_delta]
    push_cast; ring

/-- "Solving the skein relation separately in the two directions" (sm-3:2132-2142): the recursion at a
positive crossing, solved for the switched diagram. -/
theorem switch_of_recursion_pos {f g h : R} (e : f = R.aInv * R.aInv * g + R.aInv * R.z * h) :
    g = R.a * R.a * f - R.a * R.z * h := by
  subst e
  linear_combination (-(g * (R.a * R.aInv + 1) + R.a * R.z * h)) * R.a_mul_aInv

/-- The recursion at a negative crossing, solved for the switched diagram. -/
theorem switch_of_recursion_neg {f g h : R} (e : f = R.a * R.a * g - R.a * R.z * h) :
    g = R.aInv * R.aInv * f + R.aInv * R.z * h := by
  subst e
  linear_combination (-(g * (R.a * R.aInv + 1) - R.aInv * R.z * h)) * R.a_mul_aInv

/-! ### Polynomial equalities from the leaves -/

/-- ng:commutation: `Δd = 0` (T-rec + rp:record-polynomial). -/
theorem P_comm {W W' : OWord} (h : IsComm W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram :=
  presentations _ _ (comm_recordIso h)

/-- ng:deletions, zigzag: `Δd = 0`. -/
theorem P_zigzag {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram :=
  presentations _ _ (zigzag_recordIso h)

/-- ng:circle (sm-3:2059 "For nonempty remainder, P_before = δ P_after"): lp:split-circle in record form. -/
theorem P_circleDeletion {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    P (realize W).diagram = R.delta * P (realize W').diagram :=
  P_addFree _ _ (circle_recordIso_addFree h)

/-- ng:front-III: `Δd = 0` (`P_reidemeister_III` on the site). -/
theorem P_typeIII {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨U, hU⟩ := typeIII_site h
  exact P_reidemeister_III ⟨U, Or.inl hU⟩

/-- ng:front-II: `Δd = 0` (`P_reidemeister_II` to the vertex-moved diagram, then its record). -/
theorem P_typeII {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := typeII_move h
  exact (P_reidemeister_II hR).symm.trans (presentations _ _ hrec)

/-- ng:front-I: `Δd = 0` (`P_reidemeister_I`, then the record). -/
theorem P_typeI {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := typeI_move h
  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)

/-- ng:deletions, crossed cusp: `Δd = 0`. -/
theorem P_crossedCusp {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := crossedCusp_move h
  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)


/-! ### The base and the standard circles -/

/-- ng:circle's second sentence for an arbitrary PL union of standard circles: `D = c` (L-PL), `w = 0`,
`P = δ^{c−1}` (lp:split-circle's crossing-free clause), so `B = c − (c − 1) − 1 = 0`. -/
theorem PLFront.IsStandardCircles.defect_eq_zero (F : PLFront) (h : F.IsStandardCircles) : F.defect = 0 := by
  rw [h.defect_eq, PLFront.IsStandardCircles.downCount_eq_c_general F h, P_crossingFree h.1, degAZ_delta_pow]
  have hc := F.Γ.hc
  have hcc : F.diagram.componentCount = F.Γ.c := rfl
  omega

/-- The base clause of the descent on the syntactic base of `SM.ng_finite_word` (ng:circle's `B = 0` for the
base, with the accepted planarity fact for realizations — independent of L-PL). -/
theorem base_defect_nonneg (W : OWord) (hW : W.IsStandardCircleBase) : 0 ≤ (realize W).defect := by
  have hstd := realize_isStandardCircles_of_base W hW
  have hD := realize_downCount_eq_c_of_base W hW
  rw [hstd.defect_eq, hD, P_crossingFree hstd.1, degAZ_delta_pow]
  have hc := (realize W).Γ.hc
  have hcc : (realize W).diagram.componentCount = (realize W).Γ.c := rfl
  omega

/-! ### The cusp-skein inequality from a site (display ng:skein-defect, sm-3:2127-2163) -/

/-- Display ng:skein-defect, first line, for the earlier branch `A` of the printed direction: the site lives
in `A`; positive `x` uses ng:skein-plus/degree-plus, negative `x` ng:skein-minus/degree-minus. -/
theorem skein_ineq_forward {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨x, hrec, ⟨D₀, hsm, hrec₀⟩, hsign⟩ := skein_site h
  obtain ⟨hDA, hDA', hw⟩ := skein_counts h
  have hPA' : P (realize A').diagram = P ((realize A).diagram.switch x) := presentations _ _ hrec
  have hP₀ : P D₀ = P (realize C).diagram := presentations _ _ hrec₀
  unfold PLFront.defect
  rw [hDA, hDA']
  rcases (realize A).diagram.sign_eq_one_or_neg_one x with h1 | h1
  · have hpos : (realize A).diagram.IsPositive x := ((realize A).diagram.isPositive_iff_sign_eq_one x).2 h1
    have e := P_recursion_pos hsm hpos
    rw [← hPA', hP₀] at e
    have hb := degAZ_le_of_eq_pos (P_ne_zero _) (P_ne_zero _) e (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)
  · have hneg : ¬ (realize A).diagram.IsPositive x := by
      intro hp
      have := ((realize A).diagram.isPositive_iff_sign_eq_one x).1 hp
      rw [this] at h1; exact absurd h1 (by decide)
    have e := P_recursion_neg hsm hneg
    rw [← hPA', hP₀] at e
    have hb := degAZ_le_of_eq_neg (P_ne_zero _) (P_ne_zero _) e (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

/-- Display ng:skein-defect, second line ("the other principal direction", sm-3:2164-2166 "Reflected ...
templates follow by relabeling their actual attachments and arrows in this local calculation"): the site
lives in `A'`, and the recursion is solved the other way (`switch_of_recursion_pos/neg`). -/
theorem skein_ineq_backward {A A' C : OWord} (h : IsCuspSkeinStep A'.letters A.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨x, hrec, ⟨D₀, hsm, hrec₀⟩, hsign⟩ := skein_site h
  obtain ⟨hDA', hDA, hw⟩ := skein_counts h
  have hPA : P (realize A).diagram = P ((realize A').diagram.switch x) := presentations _ _ hrec
  have hP₀ : P D₀ = P (realize C).diagram := presentations _ _ hrec₀
  unfold PLFront.defect
  rw [hDA, hDA']
  rcases (realize A').diagram.sign_eq_one_or_neg_one x with h1 | h1
  · have hpos : (realize A').diagram.IsPositive x := ((realize A').diagram.isPositive_iff_sign_eq_one x).2 h1
    have e := P_recursion_pos hsm hpos
    rw [← hPA, hP₀] at e
    have e' := switch_of_recursion_pos e
    have hb := degAZ_le_of_eq_neg (P_ne_zero _) (P_ne_zero _) e' (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)
  · have hneg : ¬ (realize A').diagram.IsPositive x := by
      intro hp
      have := ((realize A').diagram.isPositive_iff_sign_eq_one x).1 hp
      rw [this] at h1; exact absurd h1 (by decide)
    have e := P_recursion_neg hsm hneg
    rw [← hPA, hP₀] at e
    have e' := switch_of_recursion_neg e
    have hb := degAZ_le_of_eq_pos (P_ne_zero _) (P_ne_zero _) e' (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

end FrontRows

open FrontRows

/-! ## Assembly of the rows -/

/-- **ng:commutation** (row 76), assembled. -/
theorem ng_commutation : NgCommutationClauses where
  comm_D := fun _ _ h => (comm_counts h).1
  comm_w := fun _ _ h => (comm_counts h).2
  comm_d := fun _ _ h => by rw [P_comm h]
  comm_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(comm_counts h).1, (comm_counts h).2, P_comm h]
  deform_D := deform_downCount
  deform_w := deform_writhe
  deform_d := fun F F' h S S' hS hS' => by rw [deform_P F F' h S S' hS hS']
  deform_B := fun F F' h S S' hS hS' => by
    unfold SmoothFront.defect SmoothFront.dOf
    rw [deform_downCount F F' h, deform_writhe F F' h, deform_P F F' h S S' hS hS']
  represent := represent

/-- **ng:front-I** (row 77), assembled: display ng:type-I-counts and `Δd = 0` give `ΔB = 0` (sm-3:1967). -/
theorem ng_front_I : NgFrontIClauses where
  typeI_B := fun _ _ h => by
    obtain ⟨hD, hw⟩ := typeI_counts h
    unfold PLFront.defect
    rw [P_typeI h, hD, hw]
    push_cast; ring

/-- **ng:front-II** (row 78), assembled. -/
theorem ng_front_II : NgFrontIIClauses where
  typeII_D := fun _ _ h => (typeII_counts h).1
  typeII_w := fun _ _ h => (typeII_counts h).2
  typeII_d := fun _ _ h => by rw [P_typeII h]
  typeII_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(typeII_counts h).1, (typeII_counts h).2, P_typeII h]

/-- **ng:front-III** (row 79), assembled. -/
theorem ng_front_III : NgFrontIIIClauses where
  typeIII_D := fun _ _ h => (typeIII_counts h).1
  typeIII_w := fun _ _ h => (typeIII_counts h).2
  typeIII_d := fun _ _ h => by rw [P_typeIII h]
  typeIII_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(typeIII_counts h).1, (typeIII_counts h).2, P_typeIII h]

/-- **ng:deletions** (row 80), assembled: the `s` clauses from the accepted syntactic counts through
`realize_sCount` (both words nonempty), the `B` clauses from the count displays and the polynomial leaves. -/
theorem ng_deletions : NgDeletionsClauses where
  zigzag_s := fun W W' h => by
    rw [realize_sCount W h.source_ne_nil, realize_sCount W' (IsZigzagDeletion.ne_nil h W.closed)]
    exact h.sCount
  zigzag_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := zigzag_counts h
    unfold PLFront.defect
    rw [P_zigzag h, hw]
    rcases hD with hD | hD
    · rw [hD]
    · rw [hD]; push_cast; omega
  crossedCusp_s := fun W W' h => by
    rw [realize_sCount W h.ne_nil.1, realize_sCount W' h.ne_nil.2]
    exact h.sCount
  crossedCusp_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := crossedCusp_counts h
    unfold PLFront.defect
    rw [P_crossedCusp h, hw]
    rcases hD with hD | hD <;> omega

/-- **ng:circle** (row 81), assembled: display ng:circle-counts with `deg_a (δ P) = deg_a P + 1` ("Its
product with the leading coefficient of P_after is nonzero because the coefficient ring is an integral
domain", sm-3:2061-2063: `degAZ_mul` in the domain `R`). -/
theorem ng_circle : NgCircleClauses where
  circleDeletion_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := circleDeletion_counts h
    have hdeg : degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram) + 1 := by
      rw [P_circleDeletion h, degAZ_mul delta_ne_zero (P_ne_zero _), degAZ_delta]; ring
    unfold PLFront.defect
    rw [hdeg, hw, hD]
    push_cast; ring
  single_B := fun F h _ => PLFront.IsStandardCircles.defect_eq_zero F h
  union_B := fun F h => PLFront.IsStandardCircles.defect_eq_zero F h

/-- **ng:cusp-skein** (row 82), assembled. -/
theorem ng_cusp_skein : NgCuspSkeinClauses where
  earlier_branch := fun _ _ _ h => by
    rcases h with h | h
    · exact skein_ineq_forward h
    · exact skein_ineq_backward h
  unique_smoothing := fun _ _ _ _ h h' => skein_unique h h'
  smoothing_s := fun A A' C h => by
    obtain ⟨hA, -, hC⟩ := h.ne_nil
    rw [realize_sCount A hA, realize_sCount C hC]
    exact h.sCount.2
  principal_s := fun A A' C h => by
    obtain ⟨hA, hA', -⟩ := h.ne_nil
    rw [realize_sCount A hA, realize_sCount A' hA']
    exact h.sCount.1

/-- Both displayed inequalities of ng:skein-defect (sm-3:2158-2163) from the row (the interchange is
symmetric in its principal branches). -/
theorem ng_cusp_skein_both {A A' C : OWord} (h : IsCuspSkein A.letters A'.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect ∧
    min (realize A).defect (realize C).defect ≤ (realize A').defect :=
  ⟨ng_cusp_skein.earlier_branch A A' C h, ng_cusp_skein.earlier_branch A' A C h.symm⟩

namespace FrontRows

/-! ## Row 83: the word bound, then the smooth front -/

/-- The seven laws of the descent (`Moves.Laws`) for the moves of `SM.ng_finite_word` with the geometric
`s`, `B` of the realization and the axiom's syntactic base: `pres_B` = rows 76(1), 77, 78, 79; `del_B` =
rows 80, 81(1); `skein_B` = row 82; `base_B` = row 81(2-3) on the syntactic base (`base_defect_nonneg`);
the three `s` laws are the accepted `wordMoves_pres_s/del_s/skein_s` (definitionally the same fields). -/
theorem certificate_laws :
    (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect) OWord.IsStandardCircleBase).Laws where
  pres_B := fun F F' h => by
    rcases h with h | h | h | h
    · exact ng_commutation.comm_B F F' h
    · exact ng_front_I.typeI_B F F' h
    · exact ng_front_II.typeII_B F F' h
    · exact ng_front_III.typeIII_B F F' h
  pres_s := fun F F' h => wordMoves_pres_s F F' h
  del_B := fun F F' h => by
    rcases h with h | h | h
    · exact ng_deletions.zigzag_B F F' h
    · exact ng_deletions.crossedCusp_B F F' h
    · exact (ng_circle.circleDeletion_B F F' h).symm.le
  del_s := fun F F' h => wordMoves_del_s F F' h
  skein_B := fun F F' C h => ng_cusp_skein.earlier_branch F F' C h
  skein_s := fun F F' C h => wordMoves_skein_s F F' C h
  base_B := fun W hW => base_defect_nonneg W hW

/-- ng:local-front-bound on words (sm-3:2313-2343, the degree induction along the principal chains of
Literature input ng:finite-word): `B ≥ 0` on every closed oriented word's realization.  Consumes
`SM.ng_finite_word`.  The named companion of row 83 (not a field: the printed clause is on the smooth
class). -/
theorem word_bound : ∀ W : OWord, 0 ≤ (realize W).defect :=
  ng_finite_word_bound _ _ certificate_laws

end FrontRows

/-- **ng:local-front-bound** (row 83), assembled: the representation clause of ng:commutation carries `D`,
`w` and the rounding's record to a word; rp:record-polynomial (`presentations`) carries `P`; the word
bound gives `B ≥ 0`; display ng:defect converts (sm-3:2343). -/
theorem ng_local_front_bound : NgLocalFrontBoundClauses where
  front_inequality := fun F S hS => by
    obtain ⟨W, hD, hw, -, hrec⟩ := ng_commutation.represent F
    have hP : P S = P (realize W).diagram := presentations S _ (hrec S hS)
    have h0 := FrontRows.word_bound W
    rw [← F.defect_nonneg_iff S]
    unfold SmoothFront.defect SmoothFront.dOf
    rw [hD, hw, hP]
    exact h0

end SM
