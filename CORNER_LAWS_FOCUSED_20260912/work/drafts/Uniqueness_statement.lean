import SM.ALawful

/-! Source thm:uniqueness (reference/SM/sm-6-comparison.tex:201, frame SM15): uniqueness (Theorem 1 of
the main text). Main declaration: `SM.uniqueness`. STATEMENT DRAFT (proof to be supplied).

Notation. A function `F` assigning an integer to every generic polygon of every arity is
`F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ`, where `GenericPolygon n` is the space of generic
polygons (cyclic orbits of generic labelled tuples, def:polygon / def:chamber) and a generic labelled
tuple `P` with `hP : Generic P` presents the polygon `polygonProjection ⟨P, hP⟩`. The hypotheses
(a)–(f) are those of the accepted law rows read for `F`: (a) constancy on chambers
(`chamber`, def:chamber) and no jump across simple silent walls of types (E) `ExtensionAt` and (C)
`PureCutAt` (def:walls; sides `w.sideTuple true t = P_+`, `w.sideTuple false s = P_-`); (b) the flat
law at every simple flat wall `w.FlatAt j` with sides named by the turn at `j` (`P_right`: turn `-1`,
`P_left`: turn `1`, as in thm:A-S3) and the deletion `deleteVertex w.center j = P(0) ∖ j` (generic by
lem:children; the hypothesis takes any genericity witness); (c) the vertex–edge law at every simple
vertex–edge wall `w.VertexEdgeAt M a` (both branches), with `s = w.contactSign M a` and the halves
`firstHalf`/`secondHalf w.center M a = λ₁, λ₂` (generic by lem:children); (d) the triple law at
`w.TripleAt e f k`; (e) the soft theorem `F(P_ε) = ((χ_- + χ_+)/2) F(P)` for all small `ε` at every
admissible soft insertion `softInsertion P j q ε` into a generic `P`
(`softAmplitudeMultiplier P j q = (χ_- + χ_+)/2`, def:soft); (f) `F(K_1) = -1`, `F(K_{-1}) = +1` with
`K_1 = star 1`, `K_{-1} = starNeg 1` (def:star). The conclusion `F(P) = A(P)` uses
`amplitude P hP.1 hn` (cor:A-lawful: `A(P) = A_g(P)` for any root). -/

namespace SM

open WallGerm SoftDuplication

/-- The hypotheses (a)–(f) of thm:uniqueness on a function `F` on generic polygons of all arities. -/
structure UniquenessHypotheses (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) : Prop where
  /-- (a) `F` is constant on chambers. -/
  chamber : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericPolygon n),
    Q ∈ chamber P → F n Q = F n P
  /-- (a) `F` is unchanged across simple silent walls (types (E) and (C)). -/
  silent : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n),
    (∀ M a : ZMod n, w.ExtensionAt M a → ∀ s t : w.SideParameter,
      F n (polygonProjection (w.sideTuple true t)) =
        F n (polygonProjection (w.sideTuple false s))) ∧
    (∀ i j k : ZMod n, w.PureCutAt i j k → ∀ s t : w.SideParameter,
      F n (polygonProjection (w.sideTuple true t)) =
        F n (polygonProjection (w.sideTuple false s)))
  /-- (b) the flat law `F(P_right) - F(P_left) = F(P(0) ∖ j)` at every simple flat wall. -/
  flat : ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.FlatAt j)
    (hdel : Generic (deleteVertex w.center j))
    (sRight sLeft : w.Parameter) (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0),
    turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
    F (n + 1) (polygonProjection ⟨w.curve sRight, w.generic_punctured sRight hRight0⟩) -
      F (n + 1) (polygonProjection ⟨w.curve sLeft, w.generic_punctured sLeft hLeft0⟩) =
      F n (polygonProjection ⟨deleteVertex w.center j, hdel⟩)
  /-- (c) the vertex–edge law `F(P_+) - F(P_-) = s F(λ₁) F(λ₂)` at every simple vertex–edge wall,
  both branches. -/
  vertex_edge : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n)
    (hc : w.VertexEdgeAt M a) (h₁ : Generic (firstHalf w.center M a))
    (h₂ : Generic (secondHalf w.center M a)) (s t : w.SideParameter),
    F n (polygonProjection (w.sideTuple true t)) -
      F n (polygonProjection (w.sideTuple false s)) =
      (w.contactSign M a : ℤ) *
        (F (firstHalfSize M a) (polygonProjection ⟨firstHalf w.center M a, h₁⟩) *
          F (secondHalfSize M a) (polygonProjection ⟨secondHalf w.center M a, h₂⟩))
  /-- (d) `F(P_+) = F(P_-)` at every simple triple wall. -/
  triple : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (e f k : ZMod n),
    w.TripleAt e f k → ∀ s t : w.SideParameter,
      F n (polygonProjection (w.sideTuple true t)) =
        F n (polygonProjection (w.sideTuple false s))
  /-- (e) the soft theorem `F(P_ε) = ((χ_- + χ_+)/2) F(P)` for all small `ε`, at every soft
  insertion of an admissible vector into a generic polygon. -/
  soft : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ hQ : Generic (softInsertion P j q ε),
      (F (n + 1) (polygonProjection ⟨softInsertion P j q ε, hQ⟩) : ℚ) =
        softAmplitudeMultiplier P j q * (F n (polygonProjection ⟨P, hP⟩) : ℚ)
  /-- (f) `F(K_1) = -1` and `F(K_{-1}) = +1`. -/
  triangles :
    F 3 (polygonProjection (⟨star 1, (star_generic_law le_rfl).1.2.2.2.1⟩ : GenericTuple 3)) = -1 ∧
    F 3 (polygonProjection
      (⟨starNeg 1, (star_generic_law le_rfl).1.2.2.2.2.1⟩ : GenericTuple 3)) = 1

/-- thm:uniqueness as printed on SM15: a function `F` on generic polygons of every arity `n ≥ 3`
satisfying (a)–(f) equals `A` on every generic polygon. -/
theorem uniqueness (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      F n (polygonProjection ⟨P, hP⟩) = amplitude P hP.1 hn := by
  sorry

end SM
