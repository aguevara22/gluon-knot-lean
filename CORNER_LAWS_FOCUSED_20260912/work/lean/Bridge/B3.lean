import Bridge.B1

/-! Ported verbatim 2026-09-13 from work/drafts/Bridge_B3.lean (implementer subagent of the pod executor; checked with `lake env lean`, no sorry, standard axioms); only this header added and `#print axioms` lines removed. Row Bridge:B3 → `Bridge.B3` (with `Bridge.B3_unsorted`). -/

/-! Bridge lane, row 181 (Bridge:B3).
Source: reference/BRIDGE/BRIDGE.md §2, B3 at lines 493–636; coordinates as in BRIDGE.md §0 (SM_MAP):
`p_i = μ_i`, `d_i = edge P i`, CV's `e_i` is SM's `E_i`, so a CV polygon and an SM labelled tuple
are the same `LabelledTuple n`, and the CV event of a type-`T` germ is `Bridge.eventOfTriple`
(Bridge/B1.lean), with the same radius and the same curve definitionally.

**Lemma B3** (BRIDGE.md:495). "The three parameter-difference sign changes in SM type $T$,
together with its central conditions, imply CV transversality for the zero set (3)."

Route (BRIDGE.md (4)–(11)). For a base edge `a` and two edges `b, c` crossing it, CV's parameter
factorization (`CV_PARAMETERS`, d1_setup.tex:198–207; Lean `CV.G4_factorization`, row 131) reads
`G4_{a;b,c} = (τ_b − τ_c) D_b D_c` with `D_b = det(d_b, d_a)`, `D_c = det(d_c, d_a)` (BRIDGE.md (7)),
and `τ_b = t_b` is SM's `edgeParameter P a b` (`CV.crossParam_eq_edgeParameter`). Along a type-`T`
germ the two central activations persist on the whole interval (`Bridge.crosses_const`, B2), so
`K(t) = D_b(t) D_c(t)` is continuous and nowhere zero on the connected interval, hence of one sign
(`Bridge.neg_iff_of_ne_zero`, the intermediate value theorem), so `K(t) K(−t) > 0`. SM's exact
sign-change hypothesis `δ_a(t) δ_a(−t) < 0` for `δ_a = τ_b − τ_c` then gives (BRIDGE.md (8))
`G4_{a;b,c}(P(t)) G4_{a;b,c}(P(−t)) = δ_a(t) δ_a(−t) K(t) K(−t) < 0`. For the `G3` member,
`G3_{e,f,g} = −G4_{e;f,g}` as polynomials (`CV_IDENTITIES`, d8a_dictionary.tex:429–435; Lean
`CV.G4_eq_neg_G3`; BRIDGE.md (11)), and the constant factor `−1` "does not affect the sign-change
test, because the product of the two values is multiplied by `(−1)² = 1`". B2 lists the four members
of `Z`, and SM's three sign changes are measured on `e`, `f`, `k` respectively — exactly the base
edges of the three `G4` members `G4_{e;f,k}`, `G4_{f;e,k}`, `G4_{k;e,f}` of B2.

Library facts consumed (all accepted): `Bridge.B2`, `Bridge.eventOfTriple_*`, `Bridge.crosses_const`,
`Bridge.neg_iff_of_ne_zero`, `Bridge.tripleAt_crosses_center`, `Bridge.exists_sorted_tripleAt`
(Bridge/B1.lean); `CV.G4_factorization`, `CV.crossParam_eq_edgeParameter`, `CV.G4_eq_neg_G3`,
`CV.Crosses.det_ne_zero'`, `CV.crosses_comm`, `CV.continuous_det` (CV/Setup.lean, row 131);
`SM.WallGerm.TripleAt`, `SM.WallGerm.SignChanges` (SM/NamedWallPredicates.lean,
SM/GermSignChange.lean); `SM.continuous_edge`.

Shape decisions.
* `CV.Event.SignChanges (eventOfTriple hn g h) φ` and `g.SignChanges φ` are the same formula on the
  same data (`eventOfTriple_radius`, `eventOfTriple_sideCurve` are `rfl`), so the identification
  `signChanges_eventOfTriple_iff` is `Iff.rfl`.
* Because the activations are constant on the *whole* germ interval (B2's `crosses_const`), the
  product `K` is nonzero everywhere, and the witness radius `δ` of SM's sign change is reused
  unchanged for the CV sign change; BRIDGE.md's "one symmetric neighbourhood on which all six such
  determinants are nonzero" is the whole interval here.
* `B3` is stated for the increasing representatives `rep e < rep f < rep k`, matching `B2`;
  `B3_unsorted` removes the ordering hypotheses through `exists_sorted_tripleAt`, using that
  `eventOfTriple hn g h` does not depend on the naming of the triple (its data fields are
  `g.radius`, `g.curve`; the rest are proofs). -/

namespace Bridge

open SM

variable {n : ℕ} [NeZero n]

/-! ### The identification of the two sign-change predicates -/

/-- The germ form of "changes sign at `t = 0`" is the same on the CV event and on the SM germ
(same radius, same side curves; `eventOfTriple_radius`, `eventOfTriple_sideCurve`). -/
theorem signChanges_eventOfTriple_iff (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (φ : LabelledTuple n → ℝ) :
    (eventOfTriple hn g h).SignChanges φ ↔ g.SignChanges φ := Iff.rfl

/-! ### Elementary sign facts -/

omit [NeZero n] in
/-- A continuous real function without zeros on a preconnected space has a positive product of any
two of its values (BRIDGE.md B3: "It is continuous, nonzero, and of one sign on that neighbourhood.
Therefore `K(t)K(−t) > 0`"). -/
theorem mul_pos_of_ne_zero_const {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {φ : X → ℝ} (hφ : Continuous φ) (h0 : ∀ x, φ x ≠ 0) (a b : X) : 0 < φ a * φ b := by
  rcases lt_or_gt_of_ne (h0 a) with ha | ha
  · exact mul_pos_of_neg_of_neg ha ((neg_iff_of_ne_zero hφ h0 a b).mp ha)
  · rcases lt_or_gt_of_ne (h0 b) with hb | hb
    · exact absurd ((neg_iff_of_ne_zero hφ h0 a b).mpr hb) (not_lt.mpr ha.le)
    · exact mul_pos ha hb

omit [NeZero n] in
/-- BRIDGE.md (8): "The inequality follows from one strictly negative factor and one strictly
positive factor." -/
theorem mul_mul_neg_of_neg_of_pos {x y u v : ℝ} (h1 : x * y < 0) (h2 : 0 < u * v) :
    x * u * (y * v) < 0 := by
  have : x * u * (y * v) = (x * y) * (u * v) := by ring
  rw [this]
  exact mul_neg_of_neg_of_pos h1 h2

omit [NeZero n] in
/-- "Multiplication by the constant `−1` does not affect the sign-change test, because the product
of the two values is multiplied by `(−1)² = 1`" (BRIDGE.md B3). -/
theorem signChanges_neg {g : WallGerm n} {φ : LabelledTuple n → ℝ} (h : g.SignChanges φ) :
    g.SignChanges (fun P => -φ P) := by
  obtain ⟨δ, hδ, hδr, h⟩ := h
  exact ⟨δ, hδ, hδr, fun t ht => by simpa only [neg_mul_neg] using h t ht⟩

/-! ### The factorization along the germ -/

omit [NeZero n] in
/-- BRIDGE.md (7) with SM's parameters: at a polygon where `b` and `c` both cross `a`,
`G4_{a;b,c} = (τ_b − τ_c) · (D_b D_c)` with `τ_b = edgeParameter P a b`, `D_b = det(d_b, d_a)`
(`CV.G4_factorization` and `CV.crossParam_eq_edgeParameter`). -/
theorem G4_eq_paramDiff_mul {P : LabelledTuple n} {a b c : ZMod n}
    (hab : CV.Crosses P a b) (hac : CV.Crosses P a c) :
    CV.G4 P a b c = (edgeParameter P a b - edgeParameter P a c) *
      (det (edge P b) (edge P a) * det (edge P c) (edge P a)) := by
  rw [CV.G4_factorization P a b c hab.det_ne_zero' hac.det_ne_zero',
    CV.crossParam_eq_edgeParameter, CV.crossParam_eq_edgeParameter, mul_assoc]

omit [NeZero n] in
/-- `K(t) = D_b(t) D_c(t)` of BRIDGE.md B3, as a function of the germ parameter. -/
def dirProd (g : WallGerm n) (a b c : ZMod n) (u : g.Parameter) : ℝ :=
  det (edge (g.curve u) b) (edge (g.curve u) a) * det (edge (g.curve u) c) (edge (g.curve u) a)

omit [NeZero n] in
theorem continuous_dirProd (g : WallGerm n) (a b c : ZMod n) : Continuous (dirProd g a b c) :=
  ((CV.continuous_det (continuous_edge b) (continuous_edge a)).comp g.continuous_curve).mul
    ((CV.continuous_det (continuous_edge c) (continuous_edge a)).comp g.continuous_curve)

/-- A central activation of a type-`T` germ (`Z_pt = ∅`) holds at every time of the germ interval
(B2's `crosses_const`). -/
theorem crosses_all (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) {a b : ZMod n}
    (hc : CV.Crosses g.center a b) (t : g.Parameter) : CV.Crosses (g.curve t) a b :=
  (crosses_const hn hz a b g.zeroParameter t).mp hc

theorem crosses_sideTuple (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) {a b : ZMod n}
    (hc : CV.Crosses g.center a b) (β : Bool) (t : g.SideParameter) :
    CV.Crosses (g.sideTuple β t).val a b :=
  crosses_all hn hz hc (g.sideTime β t)

/-- "Every relevant central pair has independent directions by B1, so each denominator in (4) is
nonzero" — here at every time of the germ, since activations are constant along it. -/
theorem dirProd_ne_zero (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) {a b c : ZMod n}
    (hab : CV.Crosses g.center a b) (hac : CV.Crosses g.center a c) (u : g.Parameter) :
    dirProd g a b c u ≠ 0 :=
  mul_ne_zero (crosses_all hn hz hab u).det_ne_zero' (crosses_all hn hz hac u).det_ne_zero'

/-- "`K(t)K(−t) > 0` for all sufficiently small positive `t`" (BRIDGE.md B3) — for every `t` of
the germ interval. -/
theorem dirProd_mul_pos (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) {a b c : ZMod n}
    (hab : CV.Crosses g.center a b) (hac : CV.Crosses g.center a c) (t : g.SideParameter) :
    0 < dirProd g a b c (g.sideTime true t) * dirProd g a b c (g.sideTime false t) :=
  mul_pos_of_ne_zero_const (continuous_dirProd g a b c) (dirProd_ne_zero hn hz hab hac) _ _

/-! ### One `G4` member from its parameter-difference sign change -/

/-- BRIDGE.md (8): if `b, c` cross the base edge `a` at the centre of a type-`T` germ and SM's
parameter difference `τ_b − τ_c` along `a` changes sign, then `G4_{a;b,c}` changes sign:
`G4_{a;b,c}(P(t)) G4_{a;b,c}(P(−t)) = δ_a(t) δ_a(−t) K(t) K(−t) < 0`. -/
theorem g4_signChanges (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) {a b c : ZMod n}
    (hab : CV.Crosses g.center a b) (hac : CV.Crosses g.center a c)
    (hs : g.SignChanges (fun P => edgeParameter P a b - edgeParameter P a c)) :
    g.SignChanges (fun P => CV.G4 P a b c) := by
  obtain ⟨δ, hδ, hδr, hs⟩ := hs
  refine ⟨δ, hδ, hδr, fun t ht => ?_⟩
  have hG : ∀ β : Bool, CV.G4 (g.sideTuple β t).val a b c =
      (edgeParameter (g.sideTuple β t).val a b - edgeParameter (g.sideTuple β t).val a c) *
        dirProd g a b c (g.sideTime β t) :=
    fun β => G4_eq_paramDiff_mul (crosses_sideTuple hn hz hab β t) (crosses_sideTuple hn hz hac β t)
  show CV.G4 (g.sideTuple true t).val a b c * CV.G4 (g.sideTuple false t).val a b c < 0
  rw [hG true, hG false]
  exact mul_mul_neg_of_neg_of_pos (hs t ht) (dirProd_mul_pos hn hz hab hac t)

/-! ### The `G3` member -/

/-- BRIDGE.md (11): `G3_{e,f,g} = −G4_{e;f,g}`, "hence the product of the two `G3` values equals
the product of the two `e`-based `G4` values, which is strictly negative by (8). `G3` changes
sign." -/
theorem g3_signChanges (hn : 3 ≤ n) {g : WallGerm n} (hz : g.pointZeros = ∅) {e f k : ZMod n}
    (hef : CV.Crosses g.center e f) (hek : CV.Crosses g.center e k)
    (hs : g.SignChanges (fun P => edgeParameter P e f - edgeParameter P e k)) :
    g.SignChanges (fun P => CV.G3 P e f k) := by
  have hid : (fun P : LabelledTuple n => CV.G3 P e f k) = fun P => -CV.G4 P e f k :=
    funext fun P => neg_eq_iff_eq_neg.mp (CV.G4_eq_neg_G3 P e f k).symm
  rw [hid]
  exact signChanges_neg (g4_signChanges hn hz hef hek hs)

/-! ### B3 -/

/-- **Bridge B3** (BRIDGE.md:495). "The three parameter-difference sign changes in SM type $T$,
together with its central conditions, imply CV transversality for the zero set (3)."

Stated, like `B2`, for the increasing representatives `ē < f̄ < k̄` of the central triple: every
member of the zero set of the CV event `eventOfTriple hn g h` — by `B2` one of `G3_{e,f,k}`,
`G4_{e;f,k}`, `G4_{f;e,k}`, `G4_{k;e,f}` — changes sign at `t = 0`. The three `G4` members
inherit their sign changes from SM's three parameter-difference sign changes measured along
`e`, `f`, `k` (BRIDGE.md (8)); the `G3` member from `G3_{e,f,k} = −G4_{e;f,k}` (BRIDGE.md (11)).
"No derivative, differentiability, nonzero speed, or additional wall hypothesis was used." -/
theorem B3 (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n} (h : g.TripleAt e f k)
    (hef : CV.rep e < CV.rep f) (hfk : CV.rep f < CV.rep k) :
    (eventOfTriple hn g h).Transversal := by
  have hz : g.pointZeros = ∅ := h.1
  obtain ⟨cef, cfk, cek⟩ := tripleAt_crosses_center hn h
  have cfe := (CV.crosses_comm _ _ _).mp cef
  have cke := (CV.crosses_comm _ _ _).mp cek
  have ckf := (CV.crosses_comm _ _ _).mp cfk
  intro m hm
  rw [B2 hn g h hef hfk] at hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rw [signChanges_eventOfTriple_iff]
  rcases hm with rfl | rfl | rfl | rfl
  · exact g3_signChanges hn hz cef cek h.2.2.1
  · exact g4_signChanges hn hz cef cek h.2.2.1
  · exact g4_signChanges hn hz cfe cfk h.2.2.2.1
  · exact g4_signChanges hn hz cke ckf h.2.2.2.2

/-- `B3` without the ordering hypotheses: the event `eventOfTriple hn g h` does not depend on the
naming of the central triple (its data are `g.radius` and `g.curve`), and every type-`T` germ can
be named by its increasing representatives (`exists_sorted_tripleAt`, BRIDGE.md §0). -/
theorem B3_unsorted (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n} (h : g.TripleAt e f k) :
    (eventOfTriple hn g h).Transversal := by
  obtain ⟨e', f', k', -, hef, hfk, h'⟩ := exists_sorted_tripleAt g h
  exact B3 hn g h' hef hfk

end Bridge
