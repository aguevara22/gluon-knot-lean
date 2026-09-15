import SM.MycyclicTheorem
import SM.RelativeGeneralPosition
import SM.Children

/-! Source lem:transport (reference/SM/sm-5-transport.tex:299, frame SM15): transport. Main
declaration: `SM.transport_lemma`. STATEMENT DRAFT (proof to be supplied by the prover subagents).

Notation. The vertex count is written `n + 1` (every `n ≥ 3` has this form; the flat case deletes
one vertex, `deleteVertex : LabelledTuple (n + 1) → ZMod (n + 1) → LabelledTuple n`). `P, Z` generic
labelled tuples in the same fibre `(n, r)`: `Generic P`, `Generic Z`, `rotationNumber P = r =
rotationNumber Z` (admissibility of `(n + 1, r)` follows from lem:fibres and is not assumed).
`σ^k Z = shift k Z`. A piecewise-affine path in `ℛ_n`: a continuous `path : unitInterval →
LabelledTuple (n + 1)` with `Regular (path t)` for all `t`, affine (`a + t • b`) on each cell of a
uniform mesh `uniformMeshCell N hN j` of `[0, 1]`. Generic except at finitely many parameters:
`{t | ¬ Generic (path t)}.Finite`. At each such parameter the path is a simple wall germ (def:germ,
def:walls: `WallGerm`, `WallGerm.Simple`) whose curve is the path near `t` and whose centre is
`path t`, of type (F) `FlatAt`, (V) `VertexEdgeAt`, (T) `TripleAt`, (E) `ExtensionAt` or (C)
`PureCutAt`; at each (F) the deletion `deleteVertex (path t) j` is generic, at each (V) both halves
`firstHalf (path t) M a`, `secondHalf (path t) M a` (def:deletion-halves) are generic, all with fewer
than `n + 1` vertices (the deletion by its type, the halves by `firstHalfSize M a < n + 1`,
`secondHalfSize M a < n + 1`). -/

namespace SM

open Set

/-- lem:transport as printed on SM15. -/
theorem transport_lemma {n : ℕ} (hn : 3 ≤ n + 1) {r : ℤ} {P Z : LabelledTuple (n + 1)}
    (hP : Generic P) (hZ : Generic Z) (hrP : rotationNumber P = r) (hrZ : rotationNumber Z = r) :
    ∃ k : ZMod (n + 1), ((((n + 1 : ℕ) : ℤ), r) ≠ (4, 0) → k = 0) ∧
      ∃ path : unitInterval → LabelledTuple (n + 1),
        Continuous path ∧ path 0 = P ∧ path 1 = shift k Z ∧
        (∀ t, Regular (path t)) ∧
        (∃ (N : ℕ) (hN : 0 < N), ∀ j : Fin N, ∃ a b : LabelledTuple (n + 1),
          ∀ t ∈ uniformMeshCell N hN j, path t = a + (t : ℝ) • b) ∧
        {t : unitInterval | ¬ Generic (path t)}.Finite ∧
        (∀ t, ¬ Generic (path t) → ∃ g : WallGerm (n + 1),
          g.center = path t ∧
          (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
            g.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
          g.Simple ∧
          ((∃ j : ZMod (n + 1), g.FlatAt j ∧ Generic (deleteVertex (path t) j)) ∨
           (∃ M a : ZMod (n + 1), g.VertexEdgeAt M a ∧
              Generic (firstHalf (path t) M a) ∧ Generic (secondHalf (path t) M a) ∧
              firstHalfSize M a < n + 1 ∧ secondHalfSize M a < n + 1) ∨
           (∃ e f k : ZMod (n + 1), g.TripleAt e f k) ∨
           (∃ M a : ZMod (n + 1), g.ExtensionAt M a) ∨
           (∃ i j k : ZMod (n + 1), g.PureCutAt i j k))) := by
  sorry

end SM
