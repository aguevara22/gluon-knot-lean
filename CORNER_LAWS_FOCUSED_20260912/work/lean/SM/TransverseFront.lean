import SM.FrontGeomModel


/-! Ported 2026-09-14 04:58Z from work/drafts/front/TransverseFront.lean (front-lane statement unit, report work/drafts/front/TRANSVERSE_REPORT.md): row def:transverse-front (92), main declaration `SM.transverse_front_definition`, bundle `TransverseFrontDefinitionData`. Only this header added. -/
/-! # Generic positive transverse fronts (Definition def:transverse-front)

Source: reference/SM/sm-3-statesum.tex:3328-3340 (row 92 of tools/claims.py, frame SM15, the DEFINE
row of the contact dictionary).  Consumers read for this unit: the literature block src:contact
(sm-3:3342-3366: "For a generic positive transverse front (Definition def:transverse-front),
self-linking equals its front writhe") and Theorem fd:contact (sm-3:3404-3430: "In the xz front
page the smaller-y branch is over, and its crossing sign is sgn det_xz(u_O, u_U). For a generic
positive transverse front (Definition def:transverse-front) one has sl(T) = Σ_q sgn det_xz(u_O(q),
u_U(q))"; "Let T be an individual smooth positive transverse knot whose specified xz projection
D_T is an ordinary finite regular generic diagram").  Style: the accepted front row ng:front-domain
(SM/FrontSmooth.lean; FR-1..FR-4) and its plain-loop vocabulary (SM/FrontRecordBridge.lean §2,
SM/FrontGeomModel.lean).  Main declaration: `SM.transverse_front_definition :
TransverseFrontDefinitionData`.

## The printed text (sm-3:3328-3340, verbatim)

"In (ℝ³, ker(dz − y dx)), a generic positive transverse front is the oriented knot diagram in the
(x,z) plane obtained from a smooth oriented embedded knot T with z′ − y x′ > 0 whose xz projection
is an immersion of the parameter circle with finitely many transverse double points and no triple
point, the over strand at each double point being the branch of smaller y. It has no cusp. At a
vertical tangent, x′ = 0, the inequality gives z′ > 0: every vertical tangent of a generic positive
transverse front points upward, a consequence and not a hypothesis. The diagram determines its
writhe and its over/under counts; the knot T is named separately where it is used."

## Printed notion → Lean

| printed | Lean |
|---|---|
| `(ℝ³, ker(dz − y dx))` | `Space = ℝ × ℝ × ℝ` with `(x, y, z) = (p.1, p.2.1, p.2.2)`; `contactForm p v = v.z − p.y · v.x` (the form `dz − y dx` at `p` on `v`) |
| a smooth oriented embedded knot `T` | `TransverseKnot`: `T : ℝ → Space`, `ContDiff ℝ ∞ T`, `Function.Periodic T 1` (the parameter circle, FR-3), `embedded` = injective on the circle (`T s = T t → SameT s t`); orientation = the parameter direction (T-1) |
| `z′ − y x′ > 0` | `positive : ∀ t, 0 < z′ t − y t · x′ t`, i.e. `0 < contactForm (T t) (T′ t)` (`positive_contactForm`) |
| the `xz` projection | `xzOf T t = (x t, z t)`, packaged as the `SmoothLoop` `K.xz` (so the front's curve is literally a `SmoothLoop`) |
| an immersion of the parameter circle | `immersion : ∀ t, deriv (xzOf T) t ≠ 0` (a consequence of positivity, `vel_ne_zero_of_positive`; kept as the printed clause) |
| finitely many transverse double points | `doubles_finite` (ordered pairs of distinct parameters of `[0,1)` with equal projection: a finite set, `doubleSet`), `transverse` (`det` of the two projected velocities `≠ 0`) |
| no triple point | `no_triple` |
| the oriented knot diagram in the `(x,z)` plane | `SmoothKnotDiagram`: one `SmoothLoop` (regular, finitely many transverse double points, no triple point — the accepted layer's "regular smooth immersion with finitely many transverse double points" of one oriented circle, sm-3:341-343) "with over/under choices at its transverse double points" (def:gauss-record, sm-3:353-356): a relation `isOver` on the parameters, one branch over at every double point |
| obtained from `T` | `TransverseKnot.front : SmoothKnotDiagram`, `loop = K.xz` |
| the over strand at each double point being the branch of smaller `y` | `K.front.isOver s t ↔ K.IsDouble s t ∧ y s < y t` (T-2) |
| a generic positive transverse front | `IsGenericPositiveTransverseFront D := ∃ K : TransverseKnot, K.front = D` |
| "It has no cusp." (consequence) | `K.front.vel t ≠ 0` for every `t`: the cusp criterion of `SmoothFront` (`IsCusp p ↔ vel p = 0`) never holds; the front is NOT a `SmoothFront` (T-3, `SmoothFront.comp_ne_xz`) |
| every vertical tangent points upward (consequence) | `vertical_up : x′ t = 0 → 0 < z′ t`, PROVED from positivity; and such tangents exist (`exists_vertical_tangent`, Rolle) |
| its writhe | `SmoothKnotDiagram.writhe = ∑ q ∈ crossingPairs, crossSign q.1 q.2`, `crossingPairs` = the double points each once in over-first order `(over, under)`, `crossSign = sgn det(u_O, u_U)` — the sum of fd:front-writhe |
| its over/under counts | T-4: the over-passages `overOcc` and under-passages `underOcc` of the traversal (the occurrence parameters at which the strand is over / under), their tallies `overCount`, `underCount`; each equals the number of crossings, they partition the occurrence set |
| the diagram determines them | `writhe`, `overCount`, `underCount` are functions of the `SmoothKnotDiagram` alone; `front_ext`: the front of `K` depends on `T` only through its projection and the `y`-order at its double points |
| the knot `T` is named separately | the knot is the separate object `K : TransverseKnot`; the front is `K.front`; `IsGenericPositiveTransverseFront D ↔ ∃ K, K.front = D` |

## Readings recorded (T-1..T-5; see TRANSVERSE_REPORT.md)

* **T-1 (smooth, oriented, embedded).** "smooth" = `C^∞` and a parameter circle = a 1-periodic map of
  `ℝ` (FR-3 of the accepted front row); "oriented" = the parameter direction (both for `T` and for
  the diagram), which is what `z′ − y x′ > 0` refers to; "embedded" = injective on the circle.  The
  immersion of `T` itself is a consequence (`deriv_T_ne_zero`, from positivity), not a field.
* **T-2 (over = smaller `y`).** The over/under datum of the front is the relation `isOver s t :=
  IsDouble s t ∧ y s < y t` on parameters; at a double point the two `y`-values differ because `T` is
  embedded (`y_ne_of_isDouble`), so exactly one branch is over (`isOver_xor`).  This is the source
  observer's rule of fd:contact ("The source observer is on the negative-y side looking in the
  positive y direction, so smaller y is over"), not the Legendrian smaller-slope rule of
  ng:front-domain; the two rules are different relations and the existing polygonal reading
  `GeomMarking` (over = smaller slope) does NOT apply to transverse fronts (risk R-3).
* **T-3 (no cusp; not a `SmoothFront`).** "It has no cusp" is `vel ≠ 0` everywhere (the accepted cusp
  criterion `IsCusp ↔ vel = 0` negated), a consequence of the immersion clause and, independently, of
  positivity.  The projection cannot be viewed as a `SmoothFront`: it has vertical tangents
  (`exists_vertical_tangent`, Rolle) on regular arcs, which `SmoothFront.no_vertical` forbids
  (`SmoothFront.comp_ne_xz`).  So the front lives in the plain-loop vocabulary (`SmoothLoop`,
  `IsDoubleOf`, `occSetOf`, `crossSignOf` of SM/FrontRecordBridge.lean §2), bridged by
  `isDoubleOf_loops`, `crossSignOf_loops`, `mem_occSetOf_loops`.
* **T-4 (over/under counts).** The phrase occurs once in the document (sm-3:3337).  It is read as the
  tallies of the over/under bits along the traversal (def:gauss-record: "an over/under bit at each
  occurrence"; rem:crossing-record: "the over/under bit of each visit"): `overOcc` / `underOcc` are
  the occurrence parameters (in `[0,1)`) whose strand is over / under at their double point, and
  `overCount`, `underCount` their cardinalities.  For a one-component diagram each double point
  contributes one over- and one under-passage, so both tallies equal the crossing number
  (`overCount_eq`, `underCount_eq`) and they partition the occurrence set (`overOcc_union_underOcc`,
  `disjoint_overOcc_underOcc`); the theorem content is the injectivity of the partner map, i.e. "no
  triple point".  The alternative reading "the number of positive and negative crossings" is
  `crossingPairs.filter (crossSign = ±1)` and is derivable from the same data; it is not the phrase.
* **T-5 (determination).** "The diagram determines its writhe and its over/under counts" is rendered
  (a) definitionally — `writhe`, `overCount`, `underCount` take a `SmoothKnotDiagram`, never a knot —
  and (b) as the extensionality `front_ext`: two knots with the same projection and the same
  `y`-order at the double points have the same front, hence the same writhe and counts; nothing else
  about `y` (its values, `y′`) enters.

Fidelity risks R-1..R-6 are in TRANSVERSE_REPORT.md. -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. Standard contact space `(ℝ³, ker(dz − y dx))` -/

/-- the ambient space `ℝ³`; a point is `(x, y, z) = (p.1, p.2.1, p.2.2)` -/
abbrev Space := ℝ × ℝ × ℝ

/-- the `x`-coordinate function of a space curve -/
def xOf (T : ℝ → Space) : ℝ → ℝ := fun t => (T t).1
/-- the `y`-coordinate function of a space curve -/
def yOf (T : ℝ → Space) : ℝ → ℝ := fun t => (T t).2.1
/-- the `z`-coordinate function of a space curve -/
def zOf (T : ℝ → Space) : ℝ → ℝ := fun t => (T t).2.2
/-- the `xz` projection of a space curve, a plane curve `(x t, z t)` -/
def xzOf (T : ℝ → Space) : ℝ → Plane := fun t => (xOf T t, zOf T t)

theorem xOf_def (T : ℝ → Space) (t : ℝ) : xOf T t = (T t).1 := rfl
theorem yOf_def (T : ℝ → Space) (t : ℝ) : yOf T t = (T t).2.1 := rfl
theorem zOf_def (T : ℝ → Space) (t : ℝ) : zOf T t = (T t).2.2 := rfl
theorem xzOf_def (T : ℝ → Space) (t : ℝ) : xzOf T t = (xOf T t, zOf T t) := rfl

/-- the standard contact form `α = dz − y dx` at the point `p`, evaluated on the vector `v`:
`α_p(v) = v_z − p_y · v_x`; the contact structure is `ker α` -/
def contactForm (p v : Space) : ℝ := v.2.2 - p.2.1 * v.1

theorem contactForm_def (p v : Space) : contactForm p v = v.2.2 - p.2.1 * v.1 := rfl

/-! ## 2. One parameter circle: the same point, periodic functions -/

/-- two parameters of the circle `ℝ/ℤ` name the same point (the one-circle case of `SameParam`) -/
def SameT (s t : ℝ) : Prop := ∃ n : ℤ, t = s + n

namespace SameT

theorem refl (s : ℝ) : SameT s s := ⟨0, by simp⟩

theorem symm {s t : ℝ} (h : SameT s t) : SameT t s := by
  obtain ⟨n, hn⟩ := h
  exact ⟨-n, by rw [hn]; push_cast; ring⟩

theorem trans {r s t : ℝ} (h : SameT r s) (h' : SameT s t) : SameT r t := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  exact ⟨n + m, by rw [hm, hn]; push_cast; ring⟩

/-- On the fundamental period `[0,1)` the relation is equality. -/
theorem eq_of_mem_Ico {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : SameT s t) : s = t := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have h1' : (n : ℝ) < 1 := by linarith
  have h2' : (-1 : ℝ) < n := by linarith
  have h3 : n < 1 := by exact_mod_cast h1'
  have h4 : -1 < n := by exact_mod_cast h2'
  have hn0 : n = 0 := by omega
  subst hn0
  simp only [Int.cast_zero, add_zero] at hn
  exact hn.symm

theorem iff_eq_of_mem_Ico {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    SameT s t ↔ s = t :=
  ⟨eq_of_mem_Ico hs ht, fun h => h ▸ refl s⟩

theorem iff_of_sameT {s s' t t' : ℝ} (hs : SameT s s') (ht : SameT t t') :
    SameT s' t' ↔ SameT s t :=
  ⟨fun h => hs.trans (h.trans ht.symm), fun h => hs.symm.trans (h.trans ht)⟩

/-- on one circle (`Fin 1`) the accepted `SameParam` is `SameT` -/
theorem sameParam_iff {i j : Fin 1} {s t : ℝ} : SameParam (i, s) (j, t) ↔ SameT s t := by
  constructor
  · rintro ⟨-, n, hn⟩; exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩; exact ⟨Subsingleton.elim i j, n, hn⟩

end SameT

/-- a 1-periodic function takes the same value at parameters naming the same point -/
theorem eq_of_sameT_of_periodic {α : Type*} {f : ℝ → α} (hf : Function.Periodic f 1) {s t : ℝ}
    (h : SameT s t) : f t = f s := by
  obtain ⟨n, hn⟩ := h
  rw [hn]
  have := hf.int_mul n s
  simpa using this

/-! ## 3. Smooth knot diagrams with over/under choices

The accepted layer's smooth diagram (sm-3:341-343 "a regular smooth immersion with finitely many
transverse double points", def:gauss-record "with over/under choices at its transverse double
points"), for one oriented circle.  The over/under choice is a relation on parameters: `over s t`
says that at the double point `(s, t)` the branch through `s` is over. -/

/-- A one-component smooth knot diagram in the oriented `(x,z)` plane: a regular `C^∞` 1-periodic
plane curve with finitely many transverse double points, no triple point, and an over/under choice
at every double point. -/
structure SmoothKnotDiagram where
  /-- the plane curve, a `C^∞` 1-periodic map of the oriented parameter circle -/
  loop : SmoothLoop
  /-- regular: an immersion of the parameter circle (no cusp) -/
  immersion : ∀ t : ℝ, deriv loop.γ t ≠ 0
  /-- finitely many double points: the ordered pairs of distinct parameters of the fundamental period
  with equal image form a finite set -/
  doubles_finite :
    {q : ℝ × ℝ | q.1 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
      loop.γ q.1 = loop.γ q.2}.Finite
  /-- transverse double points: independent velocities -/
  transverse : ∀ s t : ℝ, ¬ SameT s t → loop.γ s = loop.γ t →
    det (deriv loop.γ s) (deriv loop.γ t) ≠ 0
  /-- no triple point -/
  no_triple : ∀ r s t : ℝ, ¬ SameT r s → ¬ SameT s t → ¬ SameT r t →
    loop.γ r = loop.γ s → loop.γ s = loop.γ t → False
  /-- the over/under choice: `over s t` = at the double point `(s, t)` the branch through `s` is
  over, the branch through `t` under -/
  isOver : ℝ → ℝ → Prop
  /-- the choice concerns the two branches of a double point only -/
  isOver_isDouble : ∀ s t : ℝ, isOver s t → ¬ SameT s t ∧ loop.γ s = loop.γ t
  /-- at every double point exactly one branch is over -/
  isOver_xor : ∀ s t : ℝ, ¬ SameT s t → loop.γ s = loop.γ t → Xor (isOver s t) (isOver t s)
  /-- the choice is made at the points of the circle (invariant under the period) -/
  isOver_congr : ∀ s s' t t' : ℝ, SameT s s' → SameT t t' → (isOver s t ↔ isOver s' t')

namespace SmoothKnotDiagram

variable (D : SmoothKnotDiagram)

/-- the point of the plane at a parameter -/
def eval (t : ℝ) : Plane := D.loop.γ t
/-- the velocity `γ′` -/
def vel (t : ℝ) : Plane := deriv D.loop.γ t

theorem eval_def (t : ℝ) : D.eval t = D.loop.γ t := rfl
theorem vel_def (t : ℝ) : D.vel t = deriv D.loop.γ t := rfl

theorem vel_ne_zero (t : ℝ) : D.vel t ≠ 0 := D.immersion t

/-- a double point, as an ordered pair of parameters of distinct points of the circle -/
def IsDouble (s t : ℝ) : Prop := ¬ SameT s t ∧ D.eval s = D.eval t

theorem eval_of_sameT {s t : ℝ} (h : SameT s t) : D.eval t = D.eval s :=
  eq_of_sameT_of_periodic D.loop.periodic h

theorem vel_of_sameT {s t : ℝ} (h : SameT s t) : D.vel t = D.vel s :=
  eq_of_sameT_of_periodic D.loop.deriv_periodic h

theorem IsDouble.symm {s t : ℝ} (h : D.IsDouble s t) : D.IsDouble t s :=
  ⟨fun h' => h.1 h'.symm, h.2.symm⟩

theorem IsDouble.eval_eq {s t : ℝ} (h : D.IsDouble s t) : D.eval s = D.eval t := h.2

theorem isDouble_iff_of_sameT {s s' t t' : ℝ} (hs : SameT s s') (ht : SameT t t') :
    D.IsDouble s' t' ↔ D.IsDouble s t := by
  unfold IsDouble
  rw [D.eval_of_sameT hs, D.eval_of_sameT ht, SameT.iff_of_sameT hs ht]

theorem det_vel_ne_zero_of_isDouble {s t : ℝ} (h : D.IsDouble s t) :
    det (D.vel s) (D.vel t) ≠ 0 :=
  D.transverse s t h.1 h.2

theorem isDouble_of_isOver {s t : ℝ} (h : D.isOver s t) : D.IsDouble s t := D.isOver_isDouble s t h

theorem isOver_or_isOver {s t : ℝ} (h : D.IsDouble s t) : D.isOver s t ∨ D.isOver t s := by
  rcases D.isOver_xor s t h.1 h.2 with h' | h'
  · exact Or.inl h'.1
  · exact Or.inr h'.1

theorem not_isOver_and_isOver (s t : ℝ) : ¬ (D.isOver s t ∧ D.isOver t s) := by
  rintro ⟨h1, h2⟩
  have hd := D.isDouble_of_isOver h1
  rcases D.isOver_xor s t hd.1 hd.2 with h' | h'
  · exact h'.2 h2
  · exact h'.2 h1

/-- Given a double point with an over branch, the partner of a fundamental-period parameter is unique
("no triple point"). -/
theorem eq_of_isDouble_of_isDouble {s t t' : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (ht' : t' ∈ Set.Ico (0 : ℝ) 1) (h : D.IsDouble s t) (h' : D.IsDouble s t') : t = t' := by
  by_contra hne
  have hst : ¬ SameT t t' := fun hs => hne (SameT.eq_of_mem_Ico ht ht' hs)
  exact D.no_triple s t t' h.1 hst h'.1 h.2 (h.2.symm.trans h'.2)

/-! ### Crossing signs -/

/-- the over-first tangent-determinant crossing sign of the pair `(over, under)`:
`sgn det_xz(u_O, u_U)` of fd:contact -/
def crossSign (s t : ℝ) : ℤ := if 0 < det (D.vel s) (D.vel t) then 1 else -1

theorem crossSign_eq_one_or_neg_one (s t : ℝ) : D.crossSign s t = 1 ∨ D.crossSign s t = -1 := by
  unfold crossSign; split_ifs <;> simp

theorem crossSign_eq_one_iff (s t : ℝ) : D.crossSign s t = 1 ↔ 0 < det (D.vel s) (D.vel t) := by
  unfold crossSign
  split_ifs with hd
  · exact ⟨fun _ => hd, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hd⟩

theorem crossSign_eq_neg_one_iff {s t : ℝ} (h : D.IsDouble s t) :
    D.crossSign s t = -1 ↔ det (D.vel s) (D.vel t) < 0 := by
  have hne := D.det_vel_ne_zero_of_isDouble h
  unfold crossSign
  split_ifs with hd
  · exact ⟨fun h1 => absurd h1 (by norm_num), fun h1 => absurd (lt_trans h1 hd) (lt_irrefl _)⟩
  · exact ⟨fun _ => lt_of_le_of_ne (not_lt.mp hd) hne, fun _ => rfl⟩

/-- The crossing sign is the accepted `SignType.sign (det u_o u_u)` of def:positive-lift, read in
`ℤ`. -/
theorem crossSign_eq_sign {s t : ℝ} (h : D.IsDouble s t) :
    D.crossSign s t = ((SignType.sign (det (D.vel s) (D.vel t)) : SignType) : ℤ) := by
  have hne := D.det_vel_ne_zero_of_isDouble h
  unfold crossSign
  split_ifs with hd
  · rw [sign_pos hd]; simp
  · rw [sign_neg (lt_of_le_of_ne (not_lt.mp hd) hne)]; simp

/-- Reversing the order of the branches reverses the sign (the sign is "over-first"). -/
theorem crossSign_swap {s t : ℝ} (h : D.IsDouble s t) : D.crossSign t s = - D.crossSign s t := by
  have hne := D.det_vel_ne_zero_of_isDouble h
  unfold crossSign
  rw [det_swap]
  split_ifs with h1 h2 h2
  · exact absurd (lt_trans h2 (neg_pos.mp h1)) (lt_irrefl _)
  · norm_num
  · norm_num
  · exact absurd (lt_of_le_of_ne (not_lt.mp h2) hne) (fun h3 => h1 (neg_pos.mpr h3))

theorem crossSign_of_sameT {s s' t t' : ℝ} (hs : SameT s s') (ht : SameT t t') :
    D.crossSign s' t' = D.crossSign s t := by
  unfold crossSign; rw [D.vel_of_sameT hs, D.vel_of_sameT ht]

/-! ### The finite set of double points, the crossings, the writhe -/

/-- the double points as ordered pairs of parameters in the fundamental period -/
def doubleSet : Finset (ℝ × ℝ) := D.doubles_finite.toFinset

theorem mem_doubleSet {q : ℝ × ℝ} :
    q ∈ D.doubleSet ↔ q.1 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
      D.eval q.1 = D.eval q.2 := by
  unfold doubleSet; rw [Set.Finite.mem_toFinset]; exact Iff.rfl

theorem isDouble_of_mem_doubleSet {q : ℝ × ℝ} (hq : q ∈ D.doubleSet) : D.IsDouble q.1 q.2 := by
  rw [mem_doubleSet] at hq
  obtain ⟨h1, h2, hne, he⟩ := hq
  exact ⟨fun hs => hne (SameT.eq_of_mem_Ico h1 h2 hs), he⟩

theorem fst_mem_Ico_of_mem_doubleSet {q : ℝ × ℝ} (hq : q ∈ D.doubleSet) :
    q.1 ∈ Set.Ico (0 : ℝ) 1 := (D.mem_doubleSet.mp hq).1

theorem snd_mem_Ico_of_mem_doubleSet {q : ℝ × ℝ} (hq : q ∈ D.doubleSet) :
    q.2 ∈ Set.Ico (0 : ℝ) 1 := (D.mem_doubleSet.mp hq).2.1

theorem swap_mem_doubleSet_iff {q : ℝ × ℝ} : q.swap ∈ D.doubleSet ↔ q ∈ D.doubleSet := by
  simp only [mem_doubleSet, Prod.fst_swap, Prod.snd_swap]
  constructor
  · rintro ⟨h1, h2, hne, he⟩; exact ⟨h2, h1, hne.symm, he.symm⟩
  · rintro ⟨h1, h2, hne, he⟩; exact ⟨h2, h1, hne.symm, he.symm⟩

/-- the crossings: each double point once, as its over-first pair `(over, under)` -/
def crossingPairs : Finset (ℝ × ℝ) := D.doubleSet.filter fun q => D.isOver q.1 q.2

theorem mem_crossingPairs {q : ℝ × ℝ} :
    q ∈ D.crossingPairs ↔ q ∈ D.doubleSet ∧ D.isOver q.1 q.2 := by
  unfold crossingPairs; rw [Finset.mem_filter]

theorem crossingPairs_subset_doubleSet : D.crossingPairs ⊆ D.doubleSet := Finset.filter_subset _ _

theorem isOver_of_mem_crossingPairs {q : ℝ × ℝ} (hq : q ∈ D.crossingPairs) : D.isOver q.1 q.2 :=
  (D.mem_crossingPairs.mp hq).2

theorem isDouble_of_mem_crossingPairs {q : ℝ × ℝ} (hq : q ∈ D.crossingPairs) :
    D.IsDouble q.1 q.2 :=
  D.isDouble_of_mem_doubleSet (D.crossingPairs_subset_doubleSet hq)

theorem mem_crossingPairs_or_swap {q : ℝ × ℝ} (hq : q ∈ D.doubleSet) :
    q ∈ D.crossingPairs ∨ q.swap ∈ D.crossingPairs := by
  have hd := D.isDouble_of_mem_doubleSet hq
  rcases D.isOver_or_isOver hd with h | h
  · exact Or.inl (D.mem_crossingPairs.mpr ⟨hq, h⟩)
  · exact Or.inr (D.mem_crossingPairs.mpr ⟨D.swap_mem_doubleSet_iff.mpr hq, h⟩)

theorem not_swap_mem_crossingPairs {q : ℝ × ℝ} (hq : q ∈ D.crossingPairs) :
    q.swap ∉ D.crossingPairs := by
  intro h'
  have h1 := (D.mem_crossingPairs.mp hq).2
  have h2 := (D.mem_crossingPairs.mp h').2
  simp only [Prod.fst_swap, Prod.snd_swap] at h2
  exact D.not_isOver_and_isOver q.1 q.2 ⟨h1, h2⟩

/-- Each double point enters `crossingPairs` exactly once: in exactly one of its two orders. -/
theorem crossingPairs_xor_swap {q : ℝ × ℝ} (hq : q ∈ D.doubleSet) :
    Xor (q ∈ D.crossingPairs) (q.swap ∈ D.crossingPairs) := by
  rcases D.mem_crossingPairs_or_swap hq with h | h
  · exact Or.inl ⟨h, D.not_swap_mem_crossingPairs h⟩
  · exact Or.inr ⟨h, fun h' => D.not_swap_mem_crossingPairs h' h⟩

/-- the writhe: the sum over the double points, each once in over-first order, of
`sgn det_xz(u_O, u_U)` (the right-hand side of fd:front-writhe) -/
def writhe : ℤ := ∑ q ∈ D.crossingPairs, D.crossSign q.1 q.2

/-- the number of crossings (double points) -/
def crossingCount : ℕ := D.crossingPairs.card

theorem writhe_def : D.writhe = ∑ q ∈ D.crossingPairs, D.crossSign q.1 q.2 := rfl
theorem crossingCount_def : D.crossingCount = D.crossingPairs.card := rfl

/-- the writhe is bounded by the number of crossings -/
theorem abs_writhe_le : |D.writhe| ≤ D.crossingCount := by
  unfold writhe crossingCount
  calc |∑ q ∈ D.crossingPairs, D.crossSign q.1 q.2|
      ≤ ∑ q ∈ D.crossingPairs, |D.crossSign q.1 q.2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ D.crossingPairs, (1 : ℤ) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rcases D.crossSign_eq_one_or_neg_one q.1 q.2 with h | h <;> rw [h] <;> norm_num
    _ = D.crossingPairs.card := by simp

/-! ### Occurrences and the over/under counts (T-4) -/

/-- the crossing occurrences: the fundamental-period parameters lying on a double point -/
def occSet : Finset ℝ := D.doubleSet.image Prod.fst

/-- the over-passages: the occurrences at which the strand is the over branch -/
def overOcc : Finset ℝ := D.crossingPairs.image Prod.fst

/-- the under-passages: the occurrences at which the strand is the under branch -/
def underOcc : Finset ℝ := D.crossingPairs.image Prod.snd

/-- the over count: the number of over-passages of the traversal -/
def overCount : ℕ := D.overOcc.card

/-- the under count: the number of under-passages of the traversal -/
def underCount : ℕ := D.underOcc.card

theorem overCount_def : D.overCount = D.overOcc.card := rfl
theorem underCount_def : D.underCount = D.underOcc.card := rfl

theorem mem_occSet {s : ℝ} :
    s ∈ D.occSet ↔ s ∈ Set.Ico (0 : ℝ) 1 ∧
      ∃ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ s ≠ t ∧ D.eval s = D.eval t := by
  unfold occSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨h1, h2, hne, he⟩ := D.mem_doubleSet.mp hq
    exact ⟨h1, q.2, h2, hne, he⟩
  · rintro ⟨hs, t, ht, hne, he⟩
    exact ⟨(s, t), D.mem_doubleSet.mpr ⟨hs, ht, hne, he⟩, rfl⟩

theorem mem_overOcc {s : ℝ} :
    s ∈ D.overOcc ↔ ∃ t : ℝ, (s, t) ∈ D.crossingPairs := by
  unfold overOcc
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, hq⟩
  · rintro ⟨t, ht⟩; exact ⟨(s, t), ht, rfl⟩

theorem mem_underOcc {t : ℝ} :
    t ∈ D.underOcc ↔ ∃ s : ℝ, (s, t) ∈ D.crossingPairs := by
  unfold underOcc
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q.1, hq⟩
  · rintro ⟨s, hs⟩; exact ⟨(s, t), hs, rfl⟩

/-- the over branch of a crossing is determined by its parameter ("no triple point") -/
theorem fst_injOn_crossingPairs : Set.InjOn Prod.fst (D.crossingPairs : Set (ℝ × ℝ)) := by
  intro q hq q' hq' heq
  rw [Finset.mem_coe] at hq hq'
  have h2 := D.snd_mem_Ico_of_mem_doubleSet (D.crossingPairs_subset_doubleSet hq)
  have h2' := D.snd_mem_Ico_of_mem_doubleSet (D.crossingPairs_subset_doubleSet hq')
  have hd := D.isDouble_of_mem_crossingPairs hq
  have hd' := D.isDouble_of_mem_crossingPairs hq'
  rw [heq] at hd
  exact Prod.ext heq (D.eq_of_isDouble_of_isDouble h2 h2' hd hd')

/-- the under branch of a crossing is determined by its parameter ("no triple point") -/
theorem snd_injOn_crossingPairs : Set.InjOn Prod.snd (D.crossingPairs : Set (ℝ × ℝ)) := by
  intro q hq q' hq' heq
  rw [Finset.mem_coe] at hq hq'
  have h1 := D.fst_mem_Ico_of_mem_doubleSet (D.crossingPairs_subset_doubleSet hq)
  have h1' := D.fst_mem_Ico_of_mem_doubleSet (D.crossingPairs_subset_doubleSet hq')
  have hd := (D.isDouble_of_mem_crossingPairs hq).symm
  have hd' := (D.isDouble_of_mem_crossingPairs hq').symm
  rw [heq] at hd
  exact Prod.ext (D.eq_of_isDouble_of_isDouble h1 h1' hd hd') heq

/-- each double point contributes exactly one over-passage: the over count is the crossing number -/
theorem overCount_eq : D.overCount = D.crossingCount :=
  Finset.card_image_of_injOn D.fst_injOn_crossingPairs

/-- each double point contributes exactly one under-passage: the under count is the crossing number -/
theorem underCount_eq : D.underCount = D.crossingCount :=
  Finset.card_image_of_injOn D.snd_injOn_crossingPairs

/-- every occurrence is an over-passage or an under-passage -/
theorem overOcc_union_underOcc : D.overOcc ∪ D.underOcc = D.occSet := by
  ext s
  rw [Finset.mem_union, mem_overOcc, mem_underOcc]
  constructor
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · unfold occSet; rw [Finset.mem_image]
      exact ⟨(s, t), D.crossingPairs_subset_doubleSet ht, rfl⟩
    · unfold occSet; rw [Finset.mem_image]
      exact ⟨(s, t), D.swap_mem_doubleSet_iff.mp (D.crossingPairs_subset_doubleSet ht), rfl⟩
  · intro hs
    unfold occSet at hs; rw [Finset.mem_image] at hs
    obtain ⟨q, hq, rfl⟩ := hs
    rcases D.mem_crossingPairs_or_swap hq with h | h
    · exact Or.inl ⟨q.2, h⟩
    · exact Or.inr ⟨q.2, h⟩

/-- no occurrence is both an over- and an under-passage -/
theorem disjoint_overOcc_underOcc : Disjoint D.overOcc D.underOcc := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  obtain ⟨t, ht⟩ := D.mem_overOcc.mp hs
  obtain ⟨t', ht'⟩ := D.mem_underOcc.mp hs'
  have h2 := D.snd_mem_Ico_of_mem_doubleSet (D.crossingPairs_subset_doubleSet ht)
  have h1' := D.fst_mem_Ico_of_mem_doubleSet (D.crossingPairs_subset_doubleSet ht')
  have hd := D.isDouble_of_mem_crossingPairs ht
  have hd' := (D.isDouble_of_mem_crossingPairs ht').symm
  have htt : t = t' := D.eq_of_isDouble_of_isDouble h2 h1' hd hd'
  subst htt
  exact D.not_swap_mem_crossingPairs ht ht'

/-- the occurrences are twice the crossings -/
theorem card_occSet : D.occSet.card = 2 * D.crossingCount := by
  rw [← D.overOcc_union_underOcc, Finset.card_union_of_disjoint D.disjoint_overOcc_underOcc,
    ← overCount_def, ← underCount_def, D.overCount_eq, D.underCount_eq]
  ring

/-! ### Extensionality: a diagram is its curve with its over/under choices -/

theorem ext' {D D' : SmoothKnotDiagram} (hl : D.loop = D'.loop) (ho : D.isOver = D'.isOver) :
    D = D' := by
  obtain ⟨l, i, f, tr, nt, o, oi, ox, oc⟩ := D
  obtain ⟨l', i', f', tr', nt', o', oi', ox', oc'⟩ := D'
  simp only at hl ho
  subst hl; subst ho
  rfl

theorem ext_iff' {D D' : SmoothKnotDiagram} : D = D' ↔ D.loop = D'.loop ∧ D.isOver = D'.isOver :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext' h.1 h.2⟩

/-! ### Bridge to the accepted plain-loop vocabulary (one circle, `Fin 1`) -/

/-- the diagram as a family of loops on one circle, the accepted vocabulary of
SM/FrontRecordBridge.lean §2 (`IsDoubleOf`, `occSetOf`, `crossSignOf`) -/
def loops : Fin 1 → SmoothLoop := fun _ => D.loop

theorem loops_apply (i : Fin 1) : D.loops i = D.loop := rfl

theorem isDoubleOf_loops (i j : Fin 1) (s t : ℝ) :
    SmoothFront.IsDoubleOf D.loops (i, s) (j, t) ↔ D.IsDouble s t := by
  unfold SmoothFront.IsDoubleOf IsDouble loops eval
  rw [SameT.sameParam_iff]

theorem crossSignOf_loops (i j : Fin 1) (s t : ℝ) :
    SmoothFront.crossSignOf D.loops (i, s) (j, t) = D.crossSign s t := rfl

theorem slopeOf_loops (i : Fin 1) (s : ℝ) :
    SmoothFront.slopeOf D.loops (i, s) = (D.vel s).2 / (D.vel s).1 := rfl

theorem mem_occSetOf_loops (i : Fin 1) (s : ℝ) :
    (i, s) ∈ SmoothFront.occSetOf D.loops ↔ s ∈ D.occSet := by
  rw [SmoothFront.mem_occSetOf, mem_occSet]
  constructor
  · rintro ⟨hs, ⟨j, t⟩, ht, hne, he⟩
    exact ⟨hs, t, ht, fun h => hne (by rw [h, Subsingleton.elim i j]), he⟩
  · rintro ⟨hs, t, ht, hne, he⟩
    exact ⟨hs, (i, t), ht, fun h => hne (congrArg Prod.snd h), he⟩

end SmoothKnotDiagram

/-! ## 4. The knot `T` (sm-3:3329-3334), one field per printed clause -/

/-- "a smooth oriented embedded knot T with z′ − y x′ > 0 whose xz projection is an immersion of the
parameter circle with finitely many transverse double points and no triple point", in
`(ℝ³, ker(dz − y dx))`.  The orientation is the parameter direction (T-1); derivatives are those of
the coordinate functions `xOf T`, `yOf T`, `zOf T` (the printed `x′, y′, z′`). -/
structure TransverseKnot where
  /-- the knot, a map of the parameter circle to `ℝ³` -/
  T : ℝ → Space
  /-- "smooth" -/
  smooth : ContDiff ℝ ∞ T
  /-- the parameter circle `ℝ/ℤ` -/
  periodic : Function.Periodic T 1
  /-- "embedded": injective on the circle -/
  embedded : ∀ s t : ℝ, T s = T t → SameT s t
  /-- "with z′ − y x′ > 0": positively transverse to `ker(dz − y dx)` -/
  positive : ∀ t : ℝ, 0 < deriv (zOf T) t - yOf T t * deriv (xOf T) t
  /-- "whose xz projection is an immersion of the parameter circle" -/
  immersion : ∀ t : ℝ, deriv (xzOf T) t ≠ 0
  /-- "with finitely many ... double points": the ordered pairs of distinct parameters of the
  fundamental period with equal projection form a finite set -/
  doubles_finite :
    {q : ℝ × ℝ | q.1 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
      xzOf T q.1 = xzOf T q.2}.Finite
  /-- "transverse double points": at a double point of the projection the two projected velocities
  are independent -/
  transverse : ∀ s t : ℝ, ¬ SameT s t → xzOf T s = xzOf T t →
    det (deriv (xzOf T) s) (deriv (xzOf T) t) ≠ 0
  /-- "and no triple point" -/
  no_triple : ∀ r s t : ℝ, ¬ SameT r s → ¬ SameT s t → ¬ SameT r t →
    xzOf T r = xzOf T s → xzOf T s = xzOf T t → False

namespace TransverseKnot

variable (K : TransverseKnot)

/-! ### Coordinates, smoothness, periodicity, derivatives -/

theorem smooth_x : ContDiff ℝ ∞ (xOf K.T) := K.smooth.fst
theorem smooth_y : ContDiff ℝ ∞ (yOf K.T) := K.smooth.snd.fst
theorem smooth_z : ContDiff ℝ ∞ (zOf K.T) := K.smooth.snd.snd
theorem smooth_xz : ContDiff ℝ ∞ (xzOf K.T) := K.smooth_x.prodMk K.smooth_z

theorem periodic_x : Function.Periodic (xOf K.T) 1 := fun t => by
  show (K.T (t + 1)).1 = (K.T t).1
  rw [K.periodic t]
theorem periodic_y : Function.Periodic (yOf K.T) 1 := fun t => by
  show (K.T (t + 1)).2.1 = (K.T t).2.1
  rw [K.periodic t]
theorem periodic_z : Function.Periodic (zOf K.T) 1 := fun t => by
  show (K.T (t + 1)).2.2 = (K.T t).2.2
  rw [K.periodic t]
theorem periodic_xz : Function.Periodic (xzOf K.T) 1 := fun t => by
  show (xOf K.T (t + 1), zOf K.T (t + 1)) = (xOf K.T t, zOf K.T t)
  rw [K.periodic_x t, K.periodic_z t]

theorem hasDerivAt_x (t : ℝ) : HasDerivAt (xOf K.T) (deriv (xOf K.T) t) t :=
  ((K.smooth_x.differentiable (by decide)) t).hasDerivAt
theorem hasDerivAt_y (t : ℝ) : HasDerivAt (yOf K.T) (deriv (yOf K.T) t) t :=
  ((K.smooth_y.differentiable (by decide)) t).hasDerivAt
theorem hasDerivAt_z (t : ℝ) : HasDerivAt (zOf K.T) (deriv (zOf K.T) t) t :=
  ((K.smooth_z.differentiable (by decide)) t).hasDerivAt

/-- the projected velocity is `(x′, z′)` -/
theorem hasDerivAt_xz (t : ℝ) :
    HasDerivAt (xzOf K.T) (deriv (xOf K.T) t, deriv (zOf K.T) t) t :=
  (K.hasDerivAt_x t).prodMk (K.hasDerivAt_z t)

theorem deriv_xz (t : ℝ) : deriv (xzOf K.T) t = (deriv (xOf K.T) t, deriv (zOf K.T) t) :=
  (K.hasDerivAt_xz t).deriv

/-- the velocity of `T` is `(x′, y′, z′)` -/
theorem hasDerivAt_T (t : ℝ) :
    HasDerivAt K.T (deriv (xOf K.T) t, deriv (yOf K.T) t, deriv (zOf K.T) t) t :=
  (K.hasDerivAt_x t).prodMk ((K.hasDerivAt_y t).prodMk (K.hasDerivAt_z t))

theorem deriv_T (t : ℝ) :
    deriv K.T t = (deriv (xOf K.T) t, deriv (yOf K.T) t, deriv (zOf K.T) t) :=
  (K.hasDerivAt_T t).deriv

theorem xOf_of_sameT {s t : ℝ} (h : SameT s t) : xOf K.T t = xOf K.T s :=
  eq_of_sameT_of_periodic K.periodic_x h
theorem yOf_of_sameT {s t : ℝ} (h : SameT s t) : yOf K.T t = yOf K.T s :=
  eq_of_sameT_of_periodic K.periodic_y h
theorem zOf_of_sameT {s t : ℝ} (h : SameT s t) : zOf K.T t = zOf K.T s :=
  eq_of_sameT_of_periodic K.periodic_z h
theorem xzOf_of_sameT {s t : ℝ} (h : SameT s t) : xzOf K.T t = xzOf K.T s :=
  eq_of_sameT_of_periodic K.periodic_xz h

/-! ### Positivity and its consequences -/

/-- `z′ − y x′` is the contact form `dz − y dx` on the velocity of `T`, so positivity reads
`0 < α_{T(t)}(T′(t))` -/
theorem positive_contactForm (t : ℝ) : 0 < contactForm (K.T t) (deriv K.T t) := by
  rw [deriv_T]
  exact K.positive t

theorem contactForm_eq (t : ℝ) :
    contactForm (K.T t) (deriv K.T t) = deriv (zOf K.T) t - yOf K.T t * deriv (xOf K.T) t := by
  rw [deriv_T]; rfl

/-- "At a vertical tangent, x′ = 0, the inequality gives z′ > 0": every vertical tangent points
upward — a consequence of positivity, not a hypothesis. -/
theorem vertical_up {t : ℝ} (h : deriv (xOf K.T) t = 0) : 0 < deriv (zOf K.T) t := by
  have := K.positive t
  rw [h] at this
  simpa using this

/-- Positivity alone makes the projection an immersion: `(x′, z′) = 0` would give `z′ − y x′ = 0`.
So the printed clause `immersion` adds no strength. -/
theorem vel_ne_zero_of_positive (t : ℝ) : deriv (xzOf K.T) t ≠ 0 := by
  intro h
  rw [deriv_xz] at h
  have hx : deriv (xOf K.T) t = 0 := by have := congrArg Prod.fst h; simpa using this
  have hz : deriv (zOf K.T) t = 0 := by have := congrArg Prod.snd h; simpa using this
  have := K.positive t
  rw [hx, hz] at this
  simp at this

/-- `T` is an immersion (with `embedded`, an embedded circle): its velocity never vanishes -/
theorem deriv_T_ne_zero (t : ℝ) : deriv K.T t ≠ 0 := by
  intro h
  apply K.vel_ne_zero_of_positive t
  rw [deriv_xz, deriv_T] at *
  have hx : deriv (xOf K.T) t = 0 := congrArg Prod.fst h
  have hz : deriv (zOf K.T) t = 0 := congrArg (fun v : Space => v.2.2) h
  rw [hx, hz]; rfl

/-- A closed curve has a vertical tangent (Rolle on the periodic `x`), and there `z′ > 0`: the front
has upward vertical tangents.  In particular it is not on the domain of ng:front-domain
(`SmoothFront.comp_ne_xz`). -/
theorem exists_vertical_tangent : ∃ t : ℝ, deriv (xOf K.T) t = 0 ∧ 0 < deriv (zOf K.T) t := by
  have hcont : ContinuousOn (xOf K.T) (Set.Icc 0 1) := K.smooth_x.continuous.continuousOn
  have hper : xOf K.T 0 = xOf K.T 1 := by
    have h := K.periodic_x 0
    simp only [zero_add] at h
    exact h.symm
  obtain ⟨t, -, ht⟩ := exists_deriv_eq_zero (by norm_num : (0 : ℝ) < 1) hcont hper
  exact ⟨t, ht, K.vertical_up ht⟩

/-! ### The front: the `xz` projection with the smaller-`y` over rule -/

/-- the `xz` projection as a `SmoothLoop` (`C^∞`, 1-periodic): the curve of the front -/
def xz : SmoothLoop where
  γ := xzOf K.T
  smooth := K.smooth_xz
  periodic := K.periodic_xz

@[simp] theorem xz_γ : K.xz.γ = xzOf K.T := rfl

/-- a double point of the projection -/
def IsDouble (s t : ℝ) : Prop := ¬ SameT s t ∧ xzOf K.T s = xzOf K.T t

/-- At a double point of the projection the two branches have distinct `y` (`T` is embedded), so
"the branch of smaller y" is well defined. -/
theorem y_ne_of_isDouble {s t : ℝ} (h : K.IsDouble s t) : yOf K.T s ≠ yOf K.T t := by
  intro hy
  apply h.1
  apply K.embedded
  have hx : xOf K.T s = xOf K.T t := (Prod.ext_iff.mp h.2).1
  have hz : zOf K.T s = zOf K.T t := (Prod.ext_iff.mp h.2).2
  exact Prod.ext hx (Prod.ext hy hz)

theorem isDouble_iff_of_sameT {s s' t t' : ℝ} (hs : SameT s s') (ht : SameT t t') :
    K.IsDouble s' t' ↔ K.IsDouble s t := by
  unfold IsDouble
  rw [K.xzOf_of_sameT hs, K.xzOf_of_sameT ht, SameT.iff_of_sameT hs ht]

/-- "the over strand at each double point being the branch of smaller y" -/
def IsOver (s t : ℝ) : Prop := K.IsDouble s t ∧ yOf K.T s < yOf K.T t

/-- "the oriented knot diagram in the (x,z) plane obtained from" `T`: the `xz` projection with the
smaller-`y` over rule -/
def front : SmoothKnotDiagram where
  loop := K.xz
  immersion := K.immersion
  doubles_finite := K.doubles_finite
  transverse := K.transverse
  no_triple := K.no_triple
  isOver := K.IsOver
  isOver_isDouble := fun _ _ h => h.1
  isOver_xor := fun s t hne he => by
    have hy := K.y_ne_of_isDouble ⟨hne, he⟩
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · exact Or.inl ⟨⟨⟨hne, he⟩, hlt⟩, fun h' => lt_asymm hlt h'.2⟩
    · exact Or.inr ⟨⟨⟨fun h' => hne h'.symm, he.symm⟩, hgt⟩, fun h' => lt_asymm hgt h'.2⟩
  isOver_congr := fun s s' t t' hs ht => by
    unfold IsOver
    rw [K.isDouble_iff_of_sameT hs ht, K.yOf_of_sameT hs, K.yOf_of_sameT ht]

@[simp] theorem front_loop : K.front.loop = K.xz := rfl
theorem front_loop_γ : K.front.loop.γ = xzOf K.T := rfl
theorem front_eval (t : ℝ) : K.front.eval t = (xOf K.T t, zOf K.T t) := rfl
theorem front_vel (t : ℝ) : K.front.vel t = (deriv (xOf K.T) t, deriv (zOf K.T) t) := K.deriv_xz t
theorem front_isDouble (s t : ℝ) : K.front.IsDouble s t ↔ K.IsDouble s t := Iff.rfl
theorem front_isOver (s t : ℝ) : K.front.isOver s t ↔ K.IsDouble s t ∧ yOf K.T s < yOf K.T t := Iff.rfl

/-- "It has no cusp": the velocity of the front never vanishes (the accepted cusp criterion
`IsCusp ↔ vel = 0` never holds) -/
theorem front_vel_ne_zero (t : ℝ) : K.front.vel t ≠ 0 := K.immersion t

/-- the front's vertical tangents point upward, in the front's own vocabulary -/
theorem front_vertical_up {t : ℝ} (h : (K.front.vel t).1 = 0) : 0 < (K.front.vel t).2 := by
  rw [front_vel] at h ⊢
  exact K.vertical_up h

/-- The front depends on `T` only through its projection and the `y`-order at its double points
(T-5): two knots with the same projection and the same over rule have the same front. -/
theorem front_ext {K K' : TransverseKnot} (hl : K.xz = K'.xz)
    (ho : ∀ s t : ℝ, K.IsDouble s t → (yOf K.T s < yOf K.T t ↔ yOf K'.T s < yOf K'.T t)) :
    K.front = K'.front := by
  have hγ : xzOf K.T = xzOf K'.T := congrArg SmoothLoop.γ hl
  have hd : ∀ s t, K.IsDouble s t ↔ K'.IsDouble s t := fun s t => by
    unfold IsDouble; rw [hγ]
  refine SmoothKnotDiagram.ext' hl ?_
  funext s t
  apply propext
  show K.IsOver s t ↔ K'.IsOver s t
  unfold IsOver
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(hd s t).mp h1, (ho s t h1).mp h2⟩
  · rintro ⟨h1, h2⟩
    have h1' := (hd s t).mpr h1
    exact ⟨h1', (ho s t h1').mpr h2⟩

end TransverseKnot

/-- "a generic positive transverse front is the oriented knot diagram in the (x,z) plane obtained
from a smooth oriented embedded knot T" with the printed properties: a diagram is one iff it is the
front of some `TransverseKnot`. -/
def IsGenericPositiveTransverseFront (D : SmoothKnotDiagram) : Prop :=
  ∃ K : TransverseKnot, K.front = D

theorem TransverseKnot.isGenericPositiveTransverseFront_front (K : TransverseKnot) :
    IsGenericPositiveTransverseFront K.front := ⟨K, rfl⟩

/-! ## 5. The front is not on the domain of ng:front-domain (T-3) -/

/-- The projection of a transverse knot is never a component of a `SmoothFront`: it has a vertical
tangent on a regular arc (`exists_vertical_tangent`, and its velocity is nonzero there), which
`SmoothFront.no_vertical` forbids.  So transverse fronts live in the plain-loop vocabulary. -/
theorem SmoothFront.comp_ne_xz (F : SmoothFront) (i : Fin F.c) (K : TransverseKnot) :
    F.comp i ≠ K.xz := by
  intro h
  obtain ⟨t, hx, -⟩ := K.exists_vertical_tangent
  have hreg : deriv (F.comp i).γ t ≠ 0 := by rw [h]; exact K.immersion t
  apply F.no_vertical i t hreg
  rw [h, TransverseKnot.xz_γ, K.deriv_xz]
  exact hx

/-! ## 6. The row bundle: one field per printed clause (sm-3:3328-3340) -/

/-- Definition def:transverse-front (sm-3:3328-3340), one field per printed clause; the two
consequence sentences are the fields marked "(consequence)". -/
structure TransverseFrontDefinitionData : Prop where
  /-- "In (ℝ³, ker(dz − y dx))" (3329): the ambient space is `ℝ³` with coordinates `(x, y, z)` and
  the contact form `α = dz − y dx`, `α_p(v) = v_z − p_y v_x`. -/
  contact_space : ∀ p v : Space, contactForm p v = v.2.2 - p.2.1 * v.1
  /-- "a smooth oriented embedded knot T" (3330-3331): a `C^∞` map of the parameter circle
  (1-periodic, oriented by the parameter, T-1), injective on the circle, and an immersion (the
  latter a consequence of positivity, `deriv_T_ne_zero`). -/
  knot : ∀ K : TransverseKnot, ContDiff ℝ ∞ K.T ∧ Function.Periodic K.T 1 ∧
    (∀ s t : ℝ, K.T s = K.T t → SameT s t) ∧ ∀ t : ℝ, deriv K.T t ≠ 0
  /-- "with z′ − y x′ > 0" (3331): positivity of the contact form on the velocity. -/
  positive : ∀ (K : TransverseKnot) (t : ℝ),
    0 < deriv (zOf K.T) t - yOf K.T t * deriv (xOf K.T) t ∧
    contactForm (K.T t) (deriv K.T t) = deriv (zOf K.T) t - yOf K.T t * deriv (xOf K.T) t
  /-- "whose xz projection is an immersion of the parameter circle" (3331-3332): the front's curve
  is the `SmoothLoop` `(x t, z t)` and its velocity `(x′, z′)` never vanishes. -/
  projection : ∀ (K : TransverseKnot),
    (∀ t : ℝ, K.front.loop.γ t = ((K.T t).1, (K.T t).2.2)) ∧
    (∀ t : ℝ, K.front.vel t = (deriv (xOf K.T) t, deriv (zOf K.T) t)) ∧
    ∀ t : ℝ, K.front.vel t ≠ 0
  /-- "with finitely many transverse double points" (3332-3333): the double points of the
  projection (distinct parameters of the fundamental period with equal projection) form the finite
  set `doubleSet`, and at each of them the projected velocities are independent. -/
  double_points : ∀ K : TransverseKnot,
    (∀ q : ℝ × ℝ, q ∈ K.front.doubleSet ↔
      q.1 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
        xzOf K.T q.1 = xzOf K.T q.2) ∧
    ∀ s t : ℝ, K.front.IsDouble s t → det (K.front.vel s) (K.front.vel t) ≠ 0
  /-- "and no triple point" (3333-3334) -/
  no_triple : ∀ (K : TransverseKnot) (r s t : ℝ), ¬ SameT r s → ¬ SameT s t → ¬ SameT r t →
    xzOf K.T r = xzOf K.T s → xzOf K.T s = xzOf K.T t → False
  /-- "the over strand at each double point being the branch of smaller y" (3334-3335): the over
  relation of the front is `IsDouble s t ∧ y s < y t` (T-2), and at every double point exactly one
  branch is over. -/
  over_rule : ∀ (K : TransverseKnot) (s t : ℝ),
    (K.front.isOver s t ↔ K.front.IsDouble s t ∧ yOf K.T s < yOf K.T t) ∧
    (K.front.IsDouble s t → Xor (K.front.isOver s t) (K.front.isOver t s))
  /-- "It has no cusp." (3335) — consequence: the velocity of the front never vanishes (the accepted
  cusp criterion `IsCusp ↔ vel = 0` never holds; T-3). -/
  no_cusp : ∀ (K : TransverseKnot) (t : ℝ), K.front.vel t ≠ 0
  /-- "At a vertical tangent, x′ = 0, the inequality gives z′ > 0: every vertical tangent of a
  generic positive transverse front points upward, a consequence and not a hypothesis."
  (3335-3338) — consequence, PROVED from positivity, in coordinates and in the front's vocabulary. -/
  vertical_up : ∀ (K : TransverseKnot) (t : ℝ),
    (deriv (xOf K.T) t = 0 → 0 < deriv (zOf K.T) t) ∧
    ((K.front.vel t).1 = 0 → 0 < (K.front.vel t).2)
  /-- "The diagram determines its writhe and its over/under counts" (3338-3339), the quantities:
  the writhe is the sum over the double points, each once in over-first order `(over, under)`, of
  `sgn det_xz(u_O, u_U)` (the sum of fd:front-writhe); the over/under counts are the tallies of the
  over- and under-passages of the traversal, each equal to the crossing number and together
  partitioning the occurrence set (T-4). -/
  writhe_counts : ∀ D : SmoothKnotDiagram,
    D.writhe = ∑ q ∈ D.crossingPairs, D.crossSign q.1 q.2 ∧
    (∀ q : ℝ × ℝ, q ∈ D.crossingPairs ↔ q ∈ D.doubleSet ∧ D.isOver q.1 q.2) ∧
    (∀ q : ℝ × ℝ, q ∈ D.doubleSet → Xor (q ∈ D.crossingPairs) (q.swap ∈ D.crossingPairs)) ∧
    (∀ s t : ℝ, D.IsDouble s t →
      D.crossSign s t = ((SignType.sign (det (D.vel s) (D.vel t)) : SignType) : ℤ)) ∧
    D.overCount = D.crossingCount ∧ D.underCount = D.crossingCount ∧
    D.overOcc ∪ D.underOcc = D.occSet ∧ Disjoint D.overOcc D.underOcc
  /-- "The diagram determines its writhe and its over/under counts" (3338-3339), the determination
  (T-5): the front of `T` depends on `T` only through its projection and the `y`-order at the double
  points, so two knots agreeing there have the same front, writhe, over count and under count; and
  the quantities are functions of the diagram alone. -/
  determined : ∀ K K' : TransverseKnot, K.xz = K'.xz →
    (∀ s t : ℝ, K.IsDouble s t → (yOf K.T s < yOf K.T t ↔ yOf K'.T s < yOf K'.T t)) →
    K.front = K'.front ∧ K.front.writhe = K'.front.writhe ∧
    K.front.overCount = K'.front.overCount ∧ K.front.underCount = K'.front.underCount
  /-- "the knot T is named separately where it is used" (3339-3340): the front is the diagram of a
  separately named knot `K`; a diagram is a generic positive transverse front iff it is `K.front`
  for some `K`, and the front of every `K` is one. -/
  knot_named : (∀ D : SmoothKnotDiagram,
      IsGenericPositiveTransverseFront D ↔ ∃ K : TransverseKnot, K.front = D) ∧
    ∀ K : TransverseKnot, IsGenericPositiveTransverseFront K.front

/-- Definition def:transverse-front (sm-3:3328-3340). -/
theorem transverse_front_definition : TransverseFrontDefinitionData where
  contact_space := fun _ _ => rfl
  knot := fun K => ⟨K.smooth, K.periodic, K.embedded, K.deriv_T_ne_zero⟩
  positive := fun K t => ⟨K.positive t, K.contactForm_eq t⟩
  projection := fun K => ⟨fun _ => rfl, K.front_vel, K.front_vel_ne_zero⟩
  double_points := fun K =>
    ⟨fun _ => K.front.mem_doubleSet, fun _ _ h => K.front.det_vel_ne_zero_of_isDouble h⟩
  no_triple := fun K => K.no_triple
  over_rule := fun K s t =>
    ⟨Iff.rfl, fun h => K.front.isOver_xor s t h.1 h.2⟩
  no_cusp := fun K => K.front_vel_ne_zero
  vertical_up := fun K _ => ⟨fun h => K.vertical_up h, fun h => K.front_vertical_up h⟩
  writhe_counts := fun D =>
    ⟨rfl, fun _ => D.mem_crossingPairs, fun _ h => D.crossingPairs_xor_swap h,
      fun _ _ h => D.crossSign_eq_sign h, D.overCount_eq, D.underCount_eq,
      D.overOcc_union_underOcc, D.disjoint_overOcc_underOcc⟩
  determined := fun K K' hl ho =>
    have h := TransverseKnot.front_ext hl ho
    ⟨h, by rw [h], by rw [h], by rw [h]⟩
  knot_named := ⟨fun _ => Iff.rfl, fun K => K.isGenericPositiveTransverseFront_front⟩

end

end SM
