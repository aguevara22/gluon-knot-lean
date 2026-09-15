import SM.MycyclicTheorem
import SM.RelativeGeneralPosition
import SM.Children

/-! Source lem:transport (reference/SM/sm-5-transport.tex:299, frame SM15): transport. Main
declaration: `SM.transport_lemma`.

Assembly of three library theorems: `SM.mycyclic` (a path in the fibre, up to a shift in the
`(4, 0)` case), `SM.relative_general_position` (perturbation of the path to a piecewise-affine
regular path in relative general position whose nongeneric events are simple wall germs of a
unique regular kind) and `SM.children` (genericity of the deletion at a flat wall and of both
halves at a vertex-edge wall). Helper names carry the prefix `tlA_`. -/

namespace SM

open Set

/-- Admissibility of `(n, r)` from one generic labelled tuple of rotation `r`
(lem:fibres, `hasGenericPolygonRotation_iff`). -/
theorem tlA_admissible {n : ℕ} [NeZero n] (hn : 3 ≤ n) {r : ℤ} {P : LabelledTuple n}
    (hP : Generic P) (hrP : rotationNumber P = r) : Admissible (n : ℤ) r :=
  (genericFibre_nonempty_iff hn r).mp ⟨polygonProjection ⟨P, hP⟩, hrP⟩

/-- Scalar-coordinate affine data on a set of parameters gives tuple-form affine data. -/
theorem tlA_affine {n : ℕ} (path : unitInterval → LabelledTuple n) (S : Set unitInterval)
    (a b : ScalarCoordinate n → ℝ)
    (h : ∀ t ∈ S, scalarCoordinates (path t) = fun z => a z + (t : ℝ) * b z) :
    ∃ a' b' : LabelledTuple n, ∀ t ∈ S, path t = a' + (t : ℝ) • b' := by
  refine ⟨tupleOfScalarCoordinates a, tupleOfScalarCoordinates b, fun t ht => ?_⟩
  rw [← tupleOf_scalarCoordinates (path t), h t ht]
  funext i
  ext <;> simp [tupleOfScalarCoordinates]

/-- The whole path-existence conjunction of lem:transport for a target `Q` joined to `P`
inside the fibre `ℛ_{n+1} ∩ rot⁻¹(r)`. -/
theorem tlA_of_joined {n : ℕ} (hn : 3 ≤ n + 1) {r : ℤ} {P Q : LabelledTuple (n + 1)}
    (hP : Generic P) (hQ : Generic Q)
    (hJ : JoinedIn {Q : LabelledTuple (n + 1) | Regular Q ∧ rotationNumber Q = r} P Q) :
    ∃ path : unitInterval → LabelledTuple (n + 1),
      Continuous path ∧ path 0 = P ∧ path 1 = Q ∧
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
  obtain ⟨γ, hγ⟩ := hJ
  have hreg : ∀ t, Regular (γ t) := fun t => (hγ t).1
  have h0 : Generic (γ 0) := by rw [γ.source]; exact hP
  have h1 : Generic (γ 1) := by rw [γ.target]; exact hQ
  obtain ⟨R⟩ := relative_general_position hn γ γ.continuous hreg h0 h1 1 one_pos
  refine ⟨R.path, R.continuous, by rw [R.first, γ.source], by rw [R.last, γ.target],
    R.regular, ?_, R.finite_nongeneric, ?_⟩
  · refine ⟨R.cellCount, R.cellCount_pos, fun j => ?_⟩
    obtain ⟨a, b, hab⟩ := R.affine_on_cells j
    exact tlA_affine R.path _ a b hab
  · intro t hng
    obtain ⟨g, hc, hcurve, hsimple, kind, hkind, -⟩ := R.event t hng
    refine ⟨g, hc, hcurve, hsimple, ?_⟩
    cases kind with
    | flat =>
      obtain ⟨j, hj⟩ := hkind
      refine Or.inl ⟨j, hj, ?_⟩
      have hn3 : 3 ≤ n := by have := hj.1; omega
      have : NeZero n := ⟨by omega⟩
      obtain ⟨hg, -⟩ := children.1 n inferInstance hn3 g j hj
      rw [← hc]
      exact hg
    | bigon =>
      obtain ⟨M, a, h⟩ := hkind
      have hch := children.2 (n + 1) inferInstance hn g M a h.1
      rw [hc] at hch
      exact Or.inr (Or.inl ⟨M, a, h.1, hch.1, hch.2.1, by omega, by omega⟩)
    | sliding =>
      obtain ⟨M, a, h⟩ := hkind
      have hch := children.2 (n + 1) inferInstance hn g M a h.1
      rw [hc] at hch
      exact Or.inr (Or.inl ⟨M, a, h.1, hch.1, hch.2.1, by omega, by omega⟩)
    | triple => exact Or.inr (Or.inr (Or.inl hkind))
    | extension => exact Or.inr (Or.inr (Or.inr (Or.inl hkind)))
    | cut => exact Or.inr (Or.inr (Or.inr (Or.inr hkind)))

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
  have hregP : Regular P := generic_regular hn hP
  have hregZ : Regular Z := generic_regular hn hZ
  have ha : Admissible ((n + 1 : ℕ) : ℤ) r := tlA_admissible hn hP hrP
  have hM := mycyclic ha
  by_cases h4 : (((n + 1 : ℕ) : ℤ), r) = (4, 0)
  · obtain ⟨k, hk⟩ := hM.joined_shift P Z hregP hregZ hrP hrZ h4
    refine ⟨k, fun h => absurd h4 h, ?_⟩
    exact tlA_of_joined hn hP ((generic_shift k Z).mpr hZ) hk
  · refine ⟨0, fun _ => rfl, ?_⟩
    rw [shift_zero]
    exact tlA_of_joined hn hP hZ (hM.joined P Z hregP hregZ hrP hrZ h4)

end SM

#print axioms SM.transport_lemma
