import SM.LocalPolynomial

/-! Front block, lane β, unit β1 (2026-09-14): module `SM/FrontPL.lean` (intended home), graft G1 of the
adopted front-block design (work/reports/front-block-design-FINAL-20260913.md, §2 "Graft G1", §4, §11).

# PL fronts: the realization class of the word layer

A *PL front* is an accepted generic polygonal shadow (`SM.Link.Shadow.Generic`: regular components, no
vertex on a non-incident edge, transverse double points, no triple point) all of whose edges are
nonvertical.  It is NOT the printed smooth class of ng:front-domain (sm-3:1825-1841; that class is row 73,
module `SM/FrontSmooth.lean`, design B); it is the device on which the certificate rows 77-82 and the
literature interface ng:finite-word are checked, on grid realizations of oriented Rutherford words
(FINAL §9 FR-5).  Every PL front is already a `Diagram`: a wedge cusp is a legal corner of
`Shadow.Generic`, because `RegularPair` forbids only antiparallel consecutive edges.

Printed clauses rendered here (sm-3:1825-1837), in the PL reading:
* "ordinary semicubical cusps ... nonvertical limiting tangent": a cusp is a vertex at which the
  x-direction of the traversal reverses (`IsCusp`); both arms leave it to one x-side, so it is a left or a
  right cusp (`IsLeftCusp`, `IsRightCusp`, `isLeftCusp_xor_isRightCusp`);
* "no vertical tangencies on regular arcs": every edge has nonzero x-component (`nonvertical`);
* "Cusps meet no other strand or singularity": `Generic.tail_off` (accepted);
* "At a crossing the branch with smaller dz/dx is over": `overStrand`, `slope_overStrand_lt`;
* "A downward cusp is traversed from its locally upper arm to its locally lower arm": `IsDownCusp`
  (`isDownCusp_iff_armIn_above` is the literal reading with arm heights);
* `D(F)`, `w(F)`, `s(F)`: `downCount`, `writhe` (the accepted writhe of `diagram`), `sCount`;
* `B(F) = D − w − deg_a P_{S(F)} − 1` (display ng:defect, sm-3:1897-1898) with the identity rounding
  `S(F) = F.diagram`: `defect`;
* the base of ng:finite-word / ng:circle (sm-3:2046-2049): `IsStandardCircles`.

Correction to design A's sketch (recorded for the review): A wrote `IsDownCusp s := IsCusp s ∧ 0 < det (eIn s)
(eOut s)`.  That is the printed clause only at a LEFT cusp; at a right cusp the orientation of the two arms
as rays from the vertex is reversed and the sign flips (`isDownCusp_iff_of_isRightCusp`).  The definition
below carries the factor `(eOut s).1` (the x-side of the arms), exactly as design B's smooth criterion
carries the factor `x''` (FINAL §1, row "downward cusp").

All declarations live in `SM.PLFront`.  Checked with `lake env lean` (sorry-free, standard axioms). -/

namespace SM

open SM.Link

noncomputable section

/-! ## The class -/

/-- A *PL front*: a generic polygonal shadow all of whose edges are nonvertical.  Cusps are DERIVED:
the vertices at which the x-direction of the traversal reverses. -/
structure PLFront where
  /-- the finite union of closed oriented polygons ("a nonempty finite union of parameter circles") -/
  Γ : Shadow
  /-- "finitely many transverse double points ... no other singularities"; "cusps meet no other strand" -/
  generic : Γ.Generic
  /-- "no vertical tangencies on regular arcs" and "the limiting tangent at every cusp is nonvertical":
  every edge has a nonzero x-component -/
  nonvertical : ∀ s : Γ.Strand, (Γ.dir s).1 ≠ 0

namespace PLFront

/-! ### A two-vector sanity lemma (the printed sign rule) -/

/-- For two nonvertical directions with `slope o < slope u`: `det o u > 0 ↔ o.1 * u.1 > 0`.  Printed
(sm-3:1908-1912): "With both arrows pointing right, the over-first tangent representatives (1,−1),(1,1)
have determinant 2, so this crossing is positive." -/
theorem det_pos_iff_of_slope_lt {o u : Plane} (ho : o.1 ≠ 0) (hu : u.1 ≠ 0)
    (h : o.2 / o.1 < u.2 / u.1) : 0 < det o u ↔ 0 < o.1 * u.1 := by
  have key : det o u = o.1 * u.1 * (u.2 / u.1 - o.2 / o.1) := by
    unfold det; field_simp
  rw [key]
  have hpos : 0 < u.2 / u.1 - o.2 / o.1 := sub_pos.mpr h
  exact mul_pos_iff_of_pos_right hpos

/-- `det o u = o.1 * u.1 * (slope u − slope o)` for nonvertical `o`, `u`. -/
theorem det_eq_mul_slope_sub {o u : Plane} (ho : o.1 ≠ 0) (hu : u.1 ≠ 0) :
    det o u = o.1 * u.1 * (u.2 / u.1 - o.2 / o.1) := by
  unfold det; field_simp

/-- Nonvertical directions with equal slopes have `det = 0`. -/
theorem det_eq_zero_of_slope_eq {o u : Plane} (ho : o.1 ≠ 0) (hu : u.1 ≠ 0)
    (h : o.2 / o.1 = u.2 / u.1) : det o u = 0 := by
  rw [det_eq_mul_slope_sub ho hu, h, sub_self, mul_zero]

variable (F : PLFront)

/-! ### Vertices, incident edges, cusps -/

/-- The strand arriving at the tail vertex of `s`. -/
def prev (s : F.Γ.Strand) : F.Γ.Strand := ⟨s.1, s.2 - 1⟩

/-- The incoming edge vector at the tail vertex of `s`. -/
def eIn (s : F.Γ.Strand) : Plane := F.Γ.dir (F.prev s)

/-- The outgoing edge vector at the tail vertex of `s`. -/
def eOut (s : F.Γ.Strand) : Plane := F.Γ.dir s

theorem eIn_fst_ne_zero (s : F.Γ.Strand) : (F.eIn s).1 ≠ 0 := F.nonvertical (F.prev s)

theorem eOut_fst_ne_zero (s : F.Γ.Strand) : (F.eOut s).1 ≠ 0 := F.nonvertical s

/-- The tail vertex of `s` is a *cusp*: the x-direction reverses there ("semicubical cusp" read in the PL
class: both arms leave the vertex to the same x-side). -/
def IsCusp (s : F.Γ.Strand) : Prop := (F.eIn s).1 * (F.eOut s).1 < 0

/-- A *left* cusp: both arms extend to the right (the traversal arrives moving left, leaves moving right). -/
def IsLeftCusp (s : F.Γ.Strand) : Prop := (F.eIn s).1 < 0 ∧ 0 < (F.eOut s).1

/-- A *right* cusp: both arms extend to the left. -/
def IsRightCusp (s : F.Γ.Strand) : Prop := 0 < (F.eIn s).1 ∧ (F.eOut s).1 < 0

/-- The cusp discriminant `x_out · det(eIn, eOut)`: positive iff the traversal arrives on the locally
upper arm (`isDownCusp_iff_armIn_above`).  The factor `(eOut s).1` is the common x-side of the two arms
(design B's `x''` factor, FINAL §1). -/
def cuspDisc (s : F.Γ.Strand) : ℝ := (F.eOut s).1 * det (F.eIn s) (F.eOut s)

/-- "A downward cusp is traversed from its locally upper arm to its locally lower arm." -/
def IsDownCusp (s : F.Γ.Strand) : Prop := F.IsCusp s ∧ 0 < F.cuspDisc s

/-- An upward cusp: traversed from the locally lower arm to the locally upper arm. -/
def IsUpCusp (s : F.Γ.Strand) : Prop := F.IsCusp s ∧ F.cuspDisc s < 0

/-- The slope `dz/dx` of a strand (well defined: every edge is nonvertical). -/
def slope (s : F.Γ.Strand) : ℝ := (F.Γ.dir s).2 / (F.Γ.dir s).1

/-- The rightward bit of a strand: `true` iff its x-component is positive.  This is the direction bit of
the word layer (`SM.FrontWord.Cuts`). -/
def xdir (s : F.Γ.Strand) : Bool := decide (0 < (F.Γ.dir s).1)

theorem xdir_eq_true_iff (s : F.Γ.Strand) : F.xdir s = true ↔ 0 < (F.Γ.dir s).1 := by
  simp [xdir]

theorem xdir_eq_false_iff (s : F.Γ.Strand) : F.xdir s = false ↔ (F.Γ.dir s).1 < 0 := by
  have := F.nonvertical s
  simp only [xdir, decide_eq_false_iff_not, not_lt]
  exact ⟨fun h => lt_of_le_of_ne h this, le_of_lt⟩

/-! ### Cusps are left xor right, down xor up -/

theorem isCusp_iff (s : F.Γ.Strand) : F.IsCusp s ↔ F.IsLeftCusp s ∨ F.IsRightCusp s := by
  unfold IsCusp IsLeftCusp IsRightCusp
  have hi := F.eIn_fst_ne_zero s
  have ho := F.eOut_fst_ne_zero s
  constructor
  · intro h
    rcases lt_or_gt_of_ne hi with hi' | hi'
    · exact Or.inl ⟨hi', by nlinarith⟩
    · exact Or.inr ⟨hi', by nlinarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact mul_neg_of_neg_of_pos h1 h2
    · exact mul_neg_of_pos_of_neg h1 h2

theorem IsLeftCusp.isCusp {s : F.Γ.Strand} (h : F.IsLeftCusp s) : F.IsCusp s :=
  (F.isCusp_iff s).2 (Or.inl h)

theorem IsRightCusp.isCusp {s : F.Γ.Strand} (h : F.IsRightCusp s) : F.IsCusp s :=
  (F.isCusp_iff s).2 (Or.inr h)

theorem not_isLeftCusp_and_isRightCusp (s : F.Γ.Strand) : ¬ (F.IsLeftCusp s ∧ F.IsRightCusp s) := by
  rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
  exact lt_asymm h1 h2

theorem isLeftCusp_xor_isRightCusp {s : F.Γ.Strand} (h : F.IsCusp s) :
    Xor (F.IsLeftCusp s) (F.IsRightCusp s) := by
  rcases (F.isCusp_iff s).1 h with hl | hr
  · exact Or.inl ⟨hl, fun hr => F.not_isLeftCusp_and_isRightCusp s ⟨hl, hr⟩⟩
  · exact Or.inr ⟨hr, fun hl => F.not_isLeftCusp_and_isRightCusp s ⟨hl, hr⟩⟩

/-- At a non-cusp vertex the x-direction is preserved: the rightward bit is constant along a regular
(cusp-free) run of strands. -/
theorem not_isCusp_iff (s : F.Γ.Strand) : ¬ F.IsCusp s ↔ 0 < (F.eIn s).1 * (F.eOut s).1 := by
  unfold IsCusp
  have : (F.eIn s).1 * (F.eOut s).1 ≠ 0 := mul_ne_zero (F.eIn_fst_ne_zero s) (F.eOut_fst_ne_zero s)
  constructor
  · intro h; exact lt_of_le_of_ne (not_lt.1 h) this.symm
  · intro h; exact not_lt.2 h.le

theorem xdir_prev_eq_of_not_isCusp {s : F.Γ.Strand} (h : ¬ F.IsCusp s) : F.xdir (F.prev s) = F.xdir s := by
  have hp := (F.not_isCusp_iff s).1 h
  unfold xdir
  have hi : (F.eIn s).1 = (F.Γ.dir (F.prev s)).1 := rfl
  have ho : (F.eOut s).1 = (F.Γ.dir s).1 := rfl
  rw [hi, ho] at hp
  rcases lt_or_gt_of_ne (F.nonvertical (F.prev s)) with h1 | h1
  · have h2 : (F.Γ.dir s).1 < 0 := by nlinarith
    simp [h1.not_gt, h2.not_gt]
  · have h2 : 0 < (F.Γ.dir s).1 := by nlinarith
    simp [h1, h2]

theorem xdir_prev_ne_of_isCusp {s : F.Γ.Strand} (h : F.IsCusp s) : F.xdir (F.prev s) ≠ F.xdir s := by
  unfold IsCusp at h
  unfold xdir
  have hi : (F.eIn s).1 = (F.Γ.dir (F.prev s)).1 := rfl
  have ho : (F.eOut s).1 = (F.Γ.dir s).1 := rfl
  rw [hi, ho] at h
  rcases lt_or_gt_of_ne (F.nonvertical (F.prev s)) with h1 | h1
  · have h2 : 0 < (F.Γ.dir s).1 := by nlinarith
    simp [h1.not_gt, h2]
  · have h2 : (F.Γ.dir s).1 < 0 := by nlinarith
    simp [h1, h2.not_gt]

/-- At a cusp the two arms are not collinear: the accepted `Regular` forbids antiparallel consecutive
edges, and two parallel edges with opposite x-signs are antiparallel.  (Design A's proof, verbatim.) -/
theorem cusp_det_ne_zero {s : F.Γ.Strand} (h : F.IsCusp s) : det (F.eIn s) (F.eOut s) ≠ 0 := by
  intro hdet
  have hreg : RegularPair (edge (F.Γ.comp s.1).P (s.2 - 1)) (edge (F.Γ.comp s.1).P s.2) :=
    F.generic.regular s.1 s.2
  obtain ⟨hu, hv, hnot⟩ := hreg
  have hu1 : (F.eIn s).1 ≠ 0 := F.nonvertical (F.prev s)
  apply hnot
  refine ⟨(F.eOut s).1 / (F.eIn s).1, ?_, ?_⟩
  · have hc : (F.eIn s).1 * (F.eOut s).1 < 0 := h
    rcases lt_or_gt_of_ne hu1 with hneg | hpos
    · exact div_neg_of_pos_of_neg (by nlinarith) hneg
    · exact div_neg_of_neg_of_pos (by nlinarith) hpos
  · have hd : (F.eIn s).1 * (F.eOut s).2 = (F.eIn s).2 * (F.eOut s).1 := by
      unfold det at hdet; linarith
    ext
    · show (F.eOut s).1 = (F.eOut s).1 / (F.eIn s).1 * (F.eIn s).1
      field_simp
    · show (F.eOut s).2 = (F.eOut s).1 / (F.eIn s).1 * (F.eIn s).2
      field_simp
      linarith

theorem cuspDisc_ne_zero {s : F.Γ.Strand} (h : F.IsCusp s) : F.cuspDisc s ≠ 0 :=
  mul_ne_zero (F.eOut_fst_ne_zero s) (F.cusp_det_ne_zero h)

theorem isDownCusp_or_isUpCusp {s : F.Γ.Strand} (h : F.IsCusp s) : F.IsDownCusp s ∨ F.IsUpCusp s := by
  rcases lt_or_gt_of_ne (F.cuspDisc_ne_zero h) with hneg | hpos
  · exact Or.inr ⟨h, hneg⟩
  · exact Or.inl ⟨h, hpos⟩

theorem not_isDownCusp_and_isUpCusp (s : F.Γ.Strand) : ¬ (F.IsDownCusp s ∧ F.IsUpCusp s) := by
  rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
  exact lt_asymm h1 h2

/-- Every cusp is downward xor upward (the source's "every cusp of an oriented front is traversed either
downward or upward", src:contact sm-3:3349-3350). -/
theorem isDownCusp_xor_isUpCusp {s : F.Γ.Strand} (h : F.IsCusp s) :
    Xor (F.IsDownCusp s) (F.IsUpCusp s) := by
  rcases F.isDownCusp_or_isUpCusp h with hd | hu
  · exact Or.inl ⟨hd, fun hu => F.not_isDownCusp_and_isUpCusp s ⟨hd, hu⟩⟩
  · exact Or.inr ⟨hu, fun hd => F.not_isDownCusp_and_isUpCusp s ⟨hd, hu⟩⟩

theorem IsDownCusp.isCusp {s : F.Γ.Strand} (h : F.IsDownCusp s) : F.IsCusp s := h.1

theorem IsUpCusp.isCusp {s : F.Γ.Strand} (h : F.IsUpCusp s) : F.IsCusp s := h.1

theorem isUpCusp_iff_not_isDownCusp {s : F.Γ.Strand} (h : F.IsCusp s) :
    F.IsUpCusp s ↔ ¬ F.IsDownCusp s := by
  constructor
  · intro hu hd; exact F.not_isDownCusp_and_isUpCusp s ⟨hd, hu⟩
  · intro hd; exact (F.isDownCusp_or_isUpCusp h).resolve_left hd

/-- At a left cusp the down condition is `0 < det (eIn) (eOut)` (design A's formula). -/
theorem isDownCusp_iff_of_isLeftCusp {s : F.Γ.Strand} (h : F.IsLeftCusp s) :
    F.IsDownCusp s ↔ 0 < det (F.eIn s) (F.eOut s) := by
  have hc := h.isCusp
  have ho : 0 < (F.eOut s).1 := h.2
  unfold IsDownCusp cuspDisc
  constructor
  · rintro ⟨-, hp⟩; exact pos_of_mul_pos_right hp ho.le
  · intro hd; exact ⟨hc, mul_pos ho hd⟩

/-- At a right cusp the down condition is `det (eIn) (eOut) < 0` (the sign flips with the x-side). -/
theorem isDownCusp_iff_of_isRightCusp {s : F.Γ.Strand} (h : F.IsRightCusp s) :
    F.IsDownCusp s ↔ det (F.eIn s) (F.eOut s) < 0 := by
  have hc := h.isCusp
  have ho : (F.eOut s).1 < 0 := h.2
  unfold IsDownCusp cuspDisc
  constructor
  · rintro ⟨-, hp⟩
    by_contra hnot
    have : (F.eOut s).1 * det (F.eIn s) (F.eOut s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ho.le (not_lt.1 hnot)
    linarith
  · intro hd; exact ⟨hc, mul_pos_of_neg_of_neg ho hd⟩

/-! ### The literal reading: arms as rays from the vertex, the upper arm has larger height per unit |x| -/

/-- The incoming arm as a ray from the vertex (the reversed incoming edge). -/
def armIn (s : F.Γ.Strand) : Plane := -F.eIn s

/-- The outgoing arm as a ray from the vertex. -/
def armOut (s : F.Γ.Strand) : Plane := F.eOut s

/-- The height of a ray per unit of horizontal distance: `z / |x|`.  For two rays leaving a vertex to the
same x-side, the ray of larger `armHeight` is the locally upper arm. -/
def armHeight (v : Plane) : ℝ := v.2 / |v.1|

/-- "A downward cusp is traversed from its locally upper arm to its locally lower arm": the cusp is downward
iff the incoming arm is the upper one. -/
theorem isDownCusp_iff_armIn_above {s : F.Γ.Strand} (h : F.IsCusp s) :
    F.IsDownCusp s ↔ armHeight (F.armOut s) < armHeight (F.armIn s) := by
  have hi := F.eIn_fst_ne_zero s
  have ho := F.eOut_fst_ne_zero s
  have hc : (F.eIn s).1 * (F.eOut s).1 < 0 := h
  unfold IsDownCusp cuspDisc armHeight armIn armOut det
  have hai : |(-F.eIn s).1| = |(F.eIn s).1| := by simp
  rw [hai]
  have hpi : 0 < |(F.eIn s).1| := abs_pos.2 hi
  have hpo : 0 < |(F.eOut s).1| := abs_pos.2 ho
  rw [div_lt_div_iff₀ hpo hpi]
  simp only [Prod.snd_neg]
  constructor
  · rintro ⟨-, hp⟩
    rcases lt_or_gt_of_ne ho with hn | hpos
    · rw [abs_of_neg hn, abs_of_pos (by nlinarith : 0 < (F.eIn s).1)]
      nlinarith
    · rw [abs_of_pos hpos, abs_of_neg (by nlinarith : (F.eIn s).1 < 0)]
      nlinarith
  · intro hlt
    refine ⟨h, ?_⟩
    rcases lt_or_gt_of_ne ho with hn | hpos
    · rw [abs_of_neg hn, abs_of_pos (by nlinarith : 0 < (F.eIn s).1)] at hlt
      nlinarith
    · rw [abs_of_pos hpos, abs_of_neg (by nlinarith : (F.eIn s).1 < 0)] at hlt
      nlinarith

/-! ### The over rule: the branch with smaller `dz/dx` is over -/

/-- One strand of a crossing (a choice). -/
def strandA (x : F.Γ.Crossing) : F.Γ.Strand := Classical.choose x.2

theorem strandA_mem (x : F.Γ.Crossing) : F.strandA x ∈ x.val := by
  obtain ⟨t, hx, -, -⟩ := Classical.choose_spec x.2
  rw [hx]; simp [strandA]

/-- The other strand of a crossing. -/
def strandB (x : F.Γ.Crossing) : F.Γ.Strand := F.Γ.other x (F.strandA_mem x)

theorem strandB_mem (x : F.Γ.Crossing) : F.strandB x ∈ x.val := F.Γ.other_mem x (F.strandA_mem x)

theorem strandB_ne_strandA (x : F.Γ.Crossing) : F.strandB x ≠ F.strandA x := F.Γ.other_ne x (F.strandA_mem x)

theorem not_adjacent_strandA_strandB (x : F.Γ.Crossing) : ¬ F.Γ.Adjacent (F.strandA x) (F.strandB x) :=
  F.Γ.not_adjacent_other x (F.strandA_mem x)

theorem det_strandA_strandB_ne_zero (x : F.Γ.Crossing) :
    det (F.Γ.dir (F.strandA x)) (F.Γ.dir (F.strandB x)) ≠ 0 :=
  F.generic.transverse _ _ (F.not_adjacent_strandA_strandB x) (F.Γ.seg_inter_other_nonempty x (F.strandA_mem x))

/-- The two branches of a crossing have different slopes (transversality). -/
theorem slope_strandA_ne_slope_strandB (x : F.Γ.Crossing) : F.slope (F.strandA x) ≠ F.slope (F.strandB x) := by
  intro h
  exact F.det_strandA_strandB_ne_zero x
    (det_eq_zero_of_slope_eq (F.nonvertical _) (F.nonvertical _) h)

/-- "At a crossing the branch with smaller dz/dx is over." -/
def overStrand (x : F.Γ.Crossing) : F.Γ.Strand :=
  if F.slope (F.strandA x) < F.slope (F.strandB x) then F.strandA x else F.strandB x

theorem overStrand_mem (x : F.Γ.Crossing) : F.overStrand x ∈ x.val := by
  unfold overStrand
  split_ifs
  · exact F.strandA_mem x
  · exact F.strandB_mem x

/-- The front read as an ordinary polygonal diagram: same shadow, over strand = smaller slope.  In the PL
class the cusp vertices are legal (non-antiparallel) corners, so this is a `Diagram`; it is its own
rounding `S(F)` (design A's identity-rounding fact, FINAL §2 G1 (ii)). -/
def diagram : Diagram := ⟨F.Γ, F.generic, F.overStrand, F.overStrand_mem⟩

@[simp] theorem diagram_Γ : F.diagram.Γ = F.Γ := rfl

@[simp] theorem diagram_overStrand : F.diagram.overStrand = F.overStrand := rfl

/-- The under strand of the front's diagram is the other branch. -/
theorem diagram_underStrand (x : F.Γ.Crossing) :
    F.diagram.underStrand x = if F.slope (F.strandA x) < F.slope (F.strandB x) then F.strandB x else F.strandA x := by
  unfold Diagram.underStrand
  simp only [diagram_Γ, diagram_overStrand]
  by_cases h : F.slope (F.strandA x) < F.slope (F.strandB x)
  · rw [ite_eq_left h]
    have e : F.overStrand x = F.strandA x := ite_eq_left h
    -- `other x (over_mem)` with `over = strandA` is `strandB`
    have : F.Γ.other x (F.overStrand_mem x) = F.Γ.other x (e ▸ F.strandA_mem x) := by
      congr 1
    rw [this]
    exact (F.Γ.eq_other_of_mem_of_ne x (e ▸ F.strandA_mem x) (F.strandB_mem x)
      (by rw [e]; exact F.strandB_ne_strandA x)).symm
  · rw [ite_eq_right h]
    have e : F.overStrand x = F.strandB x := ite_eq_right h
    exact (F.Γ.eq_other_of_mem_of_ne x (F.overStrand_mem x) (F.strandA_mem x)
      (by rw [e]; exact (F.strandB_ne_strandA x).symm)).symm

/-- The over strand has the strictly smaller slope. -/
theorem slope_overStrand_lt (x : F.Γ.Crossing) :
    F.slope (F.overStrand x) < F.slope (F.diagram.underStrand x) := by
  rw [diagram_underStrand]
  unfold overStrand
  by_cases h : F.slope (F.strandA x) < F.slope (F.strandB x)
  · rw [ite_eq_left h, ite_eq_left h]; exact h
  · rw [ite_eq_right h, ite_eq_right h]
    exact lt_of_le_of_ne (not_lt.1 h) (F.slope_strandA_ne_slope_strandB x).symm

/-- The printed sign rule on a PL front: a crossing is positive iff the x-components of its two branches
have the same sign ("both arrows pointing right ... positive"; opposite arrows give sign −1, ng:deletions
sm-3:2030-2031). -/
theorem isPositive_iff (x : F.Γ.Crossing) :
    F.diagram.IsPositive x ↔ 0 < (F.Γ.dir (F.overStrand x)).1 * (F.Γ.dir (F.diagram.underStrand x)).1 := by
  unfold Diagram.IsPositive
  simp only [diagram_Γ, diagram_overStrand]
  exact det_pos_iff_of_slope_lt (F.nonvertical _) (F.nonvertical _) (F.slope_overStrand_lt x)

/-- The sign rule in the word layer's terms: positive iff the two rightward bits agree. -/
theorem isPositive_iff_xdir_eq (x : F.Γ.Crossing) :
    F.diagram.IsPositive x ↔ F.xdir (F.overStrand x) = F.xdir (F.diagram.underStrand x) := by
  rw [isPositive_iff]
  have ho := F.nonvertical (F.overStrand x)
  have hu := F.nonvertical (F.diagram.underStrand x)
  unfold xdir
  rcases lt_or_gt_of_ne ho with h1 | h1 <;> rcases lt_or_gt_of_ne hu with h2 | h2
  · simp [h1.not_gt, h2.not_gt, mul_pos_of_neg_of_neg h1 h2]
  · simp [h1.not_gt, h2, (mul_neg_of_neg_of_pos h1 h2).not_gt]
  · simp [h1, h2.not_gt, (mul_neg_of_pos_of_neg h1 h2).not_gt]
  · simp [h1, h2, mul_pos h1 h2]

theorem sign_eq_one_iff_xdir_eq (x : F.Γ.Crossing) :
    F.diagram.sign x = 1 ↔ F.xdir (F.overStrand x) = F.xdir (F.diagram.underStrand x) :=
  (F.diagram.isPositive_iff_sign_eq_one x).symm.trans (F.isPositive_iff_xdir_eq x)

theorem sign_eq_neg_one_iff_xdir_ne (x : F.Γ.Crossing) :
    F.diagram.sign x = -1 ↔ F.xdir (F.overStrand x) ≠ F.xdir (F.diagram.underStrand x) :=
  (F.diagram.sign_eq_neg_one_iff x).trans (not_congr (F.isPositive_iff_xdir_eq x))

/-- The integer sign of a crossing of a PL front, as a function of the two rightward bits. -/
theorem sign_eq_ite (x : F.Γ.Crossing) :
    (F.diagram.sign x : ℤ) = if F.xdir (F.overStrand x) = F.xdir (F.diagram.underStrand x) then 1 else -1 := by
  by_cases h : F.xdir (F.overStrand x) = F.xdir (F.diagram.underStrand x)
  · rw [ite_eq_left h, (F.sign_eq_one_iff_xdir_eq x).2 h]; rfl
  · rw [ite_eq_right h, (F.sign_eq_neg_one_iff_xdir_ne x).2 h]; rfl

/-! ### The counts `D(F)`, `w(F)`, `s(F)` and `B(F)` -/

/-- `D(F)`: the number of downward cusps. -/
def downCount : ℕ := Nat.card {s : F.Γ.Strand // F.IsDownCusp s}

/-- the number of upward cusps -/
def upCount : ℕ := Nat.card {s : F.Γ.Strand // F.IsUpCusp s}

/-- the number of cusps -/
def cuspCount : ℕ := Nat.card {s : F.Γ.Strand // F.IsCusp s}

/-- the number of left cusps -/
def leftCount : ℕ := Nat.card {s : F.Γ.Strand // F.IsLeftCusp s}

/-- the number of right cusps -/
def rightCount : ℕ := Nat.card {s : F.Γ.Strand // F.IsRightCusp s}

/-- `w(F)`: "the sum of the over-first tangent-determinant crossing signs" = the accepted writhe of the
front's diagram. -/
def writhe : ℤ := F.diagram.writhe

/-- the number of crossings -/
def crossingCount : ℕ := Fintype.card F.Γ.Crossing

/-- `s(F)`: "the number of crossings plus cusps". -/
def sCount : ℕ := F.crossingCount + F.cuspCount

/-- `B(F) = D(F) − w(F) − d(F) − 1` (display ng:defect) with `d(F) = deg_a P_{S(F)}` read on the identity
rounding `S(F) = F.diagram` (def:adeg's `degAZ`). -/
def defect : ℤ := (F.downCount : ℤ) - F.writhe - degAZ (P F.diagram) - 1

theorem defect_def : F.defect = (F.downCount : ℤ) - F.writhe - degAZ (P F.diagram) - 1 := rfl

theorem writhe_eq_sum : F.writhe = ∑ x : F.Γ.Crossing, (F.diagram.sign x : ℤ) := rfl

/-- The writhe of a PL front as a sum over its crossings of the bit-comparison signs. -/
theorem writhe_eq_sum_ite :
    F.writhe = ∑ x : F.Γ.Crossing,
      (if F.xdir (F.overStrand x) = F.xdir (F.diagram.underStrand x) then (1 : ℤ) else -1) := by
  rw [writhe_eq_sum]
  exact Finset.sum_congr rfl fun x _ => F.sign_eq_ite x

/-- Counting a subtype split by a disjoint disjunction. -/
theorem card_subtype_add_of_iff {α : Type*} [Fintype α] (p q r : α → Prop)
    (hpqr : ∀ a, p a ↔ q a ∨ r a) (hdisj : ∀ a, ¬ (q a ∧ r a)) :
    Nat.card {a // p a} = Nat.card {a // q a} + Nat.card {a // r a} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (Finset.univ.filter p) = (Finset.univ.filter q) ∪ (Finset.univ.filter r) := by
    ext a; simp [hpqr a]
  rw [h1, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro a _ hq hr
  exact hdisj a ⟨hq, hr⟩

/-- Every cusp is downward or upward, not both: `cusps = D + U`. -/
theorem cuspCount_eq_downCount_add_upCount : F.cuspCount = F.downCount + F.upCount := by
  unfold cuspCount downCount upCount
  exact card_subtype_add_of_iff _ _ _
    (fun s => ⟨fun h => F.isDownCusp_or_isUpCusp h, fun h => h.elim (fun hd => hd.isCusp) (fun hu => hu.isCusp)⟩)
    (fun s => F.not_isDownCusp_and_isUpCusp s)

/-- Every cusp is a left or a right cusp, not both: `cusps = left + right`. -/
theorem cuspCount_eq_leftCount_add_rightCount : F.cuspCount = F.leftCount + F.rightCount := by
  unfold cuspCount leftCount rightCount
  exact card_subtype_add_of_iff _ _ _ (fun s => F.isCusp_iff s) (fun s => F.not_isLeftCusp_and_isRightCusp s)

theorem downCount_le_cuspCount : F.downCount ≤ F.cuspCount := by
  rw [cuspCount_eq_downCount_add_upCount]; exact Nat.le_add_right _ _

theorem sCount_eq : F.sCount = F.crossingCount + F.downCount + F.upCount := by
  rw [sCount, cuspCount_eq_downCount_add_upCount, Nat.add_assoc]

/-! ### The base: unions of standard front circles (ng:circle, sm-3:2046-2049) -/

/-- "A simple crossing-free component with exactly one left and one right cusp": a *union of standard
front circles* is a PL front with no crossing all of whose components have exactly one left and one right
cusp.  Nesting is allowed (lp:split-circle); the base of ng:finite-word.  Geometric predicate on the
realization (FINAL §2 G1 (iii)): it avoids a syntactic base that would wrongly admit the crossing-free
zigzag word `l₁ l₂ r₁ r₂`. -/
def IsStandardCircles : Prop :=
  IsEmpty F.Γ.Crossing ∧
  ∀ i : Fin F.Γ.c, Nat.card {s : F.Γ.Strand // s.1 = i ∧ F.IsLeftCusp s} = 1 ∧
    Nat.card {s : F.Γ.Strand // s.1 = i ∧ F.IsRightCusp s} = 1

theorem IsStandardCircles.writhe_eq_zero (h : F.IsStandardCircles) : F.writhe = 0 :=
  F.diagram.writhe_eq_zero_of_isEmpty h.1

theorem IsStandardCircles.crossingCount_eq_zero (h : F.IsStandardCircles) : F.crossingCount = 0 := by
  unfold crossingCount
  have := h.1
  exact Fintype.card_eq_zero

/-- A count over strands splits as a sum over components. -/
theorem card_subtype_eq_sum_comp (p : F.Γ.Strand → Prop) :
    Nat.card {s : F.Γ.Strand // p s} = ∑ i : Fin F.Γ.c, Nat.card {s : F.Γ.Strand // s.1 = i ∧ p s} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun s : F.Γ.Strand => s.1) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ext s
  simp [and_comm]

/-- A union of standard circles has exactly two cusps per component. -/
theorem IsStandardCircles.cuspCount_eq (h : F.IsStandardCircles) : F.cuspCount = 2 * F.Γ.c := by
  rw [cuspCount_eq_leftCount_add_rightCount, leftCount, rightCount,
    card_subtype_eq_sum_comp, card_subtype_eq_sum_comp]
  have h1 : ∑ i : Fin F.Γ.c, Nat.card {s : F.Γ.Strand // s.1 = i ∧ F.IsLeftCusp s} = ∑ _i : Fin F.Γ.c, 1 :=
    Finset.sum_congr rfl fun i _ => (h.2 i).1
  have h2 : ∑ i : Fin F.Γ.c, Nat.card {s : F.Γ.Strand // s.1 = i ∧ F.IsRightCusp s} = ∑ _i : Fin F.Γ.c, 1 :=
    Finset.sum_congr rfl fun i _ => (h.2 i).2
  rw [h1, h2]
  simp
  ring

theorem IsStandardCircles.sCount_eq (h : F.IsStandardCircles) : F.sCount = 2 * F.Γ.c := by
  rw [sCount, h.crossingCount_eq_zero, h.cuspCount_eq, Nat.zero_add]

/-- The defect of a union of standard circles is `D − deg_a P − 1` (no crossings). -/
theorem IsStandardCircles.defect_eq (h : F.IsStandardCircles) :
    F.defect = (F.downCount : ℤ) - degAZ (P F.diagram) - 1 := by
  rw [defect, h.writhe_eq_zero, sub_zero]

end PLFront

end

end SM
