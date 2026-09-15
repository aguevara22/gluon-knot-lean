import SM.MycyclicTheorem
import SM.RelativeGeneralPosition
import SM.Children

/-! Source lem:transport (reference/SM/sm-5-transport.tex:299, frame SM15): transport. Main
declaration: `SM.transport_lemma`. Proof: assembly of thm:mycyclic (`SM.mycyclic`), thm:relgp
(`SM.relative_general_position`) and lem:children (`SM.children`). Helper names carry the
prefix `tlB_`. -/

namespace SM

open Set

variable {n : ℕ}

/-- Scalar-coordinate affine formula → tuple affine formula. -/
theorem tlB_affine_tuple {m : ℕ} (X : LabelledTuple m) (a b : ScalarCoordinate m → ℝ) (c : ℝ)
    (h : scalarCoordinates X = fun z => a z + c * b z) :
    X = tupleOfScalarCoordinates a + c • tupleOfScalarCoordinates b := by
  have h2 : X = tupleOfScalarCoordinates (scalarCoordinates X) :=
    (tupleOf_scalarCoordinates X).symm
  rw [h2, h]
  funext i
  ext <;> simp [tupleOfScalarCoordinates]

/-- The (V) children clause, with the centre rewritten to the path value. -/
theorem tlB_vertex (hn : 3 ≤ n + 1) (X : LabelledTuple (n + 1)) (g : WallGerm (n + 1))
    (hc : g.center = X) {M a : ZMod (n + 1)} (hv : g.VertexEdgeAt M a) :
    Generic (firstHalf X M a) ∧ Generic (secondHalf X M a) ∧
      firstHalfSize M a < n + 1 ∧ secondHalfSize M a < n + 1 := by
  obtain ⟨h1, h2, ⟨_, h3⟩, ⟨_, h4⟩, _⟩ := children.2 (n + 1) inferInstance hn g M a hv
  rw [hc] at h1 h2
  exact ⟨h1, h2, by omega, by omega⟩

/-- The (F) children clause, with the centre rewritten to the path value. -/
theorem tlB_flat (X : LabelledTuple (n + 1)) (g : WallGerm (n + 1))
    (hc : g.center = X) {j : ZMod (n + 1)} (hf : g.FlatAt j) :
    Generic (deleteVertex X j) := by
  have h3 : 3 ≤ n := by have := hf.1; omega
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hg, -⟩ := children.1 n inferInstance h3 g j hf
  rw [hc] at hg
  exact hg

/-- One nongeneric event: the unique regular wall kind, converted to the five-way
disjunction of lem:transport (bigon and sliding both feed the (V) clause). -/
theorem tlB_event (hn : 3 ≤ n + 1) (X : LabelledTuple (n + 1)) (g : WallGerm (n + 1))
    (hc : g.center = X) (hk : ∃! kind : RegularWallKind, g.HasRegularWallKind kind) :
    ((∃ j : ZMod (n + 1), g.FlatAt j ∧ Generic (deleteVertex X j)) ∨
     (∃ M a : ZMod (n + 1), g.VertexEdgeAt M a ∧
        Generic (firstHalf X M a) ∧ Generic (secondHalf X M a) ∧
        firstHalfSize M a < n + 1 ∧ secondHalfSize M a < n + 1) ∨
     (∃ e f k : ZMod (n + 1), g.TripleAt e f k) ∨
     (∃ M a : ZMod (n + 1), g.ExtensionAt M a) ∨
     (∃ i j k : ZMod (n + 1), g.PureCutAt i j k)) := by
  obtain ⟨kind, hkind, -⟩ := hk
  cases kind with
  | flat =>
    obtain ⟨j, hj⟩ := hkind
    exact Or.inl ⟨j, hj, tlB_flat X g hc hj⟩
  | bigon =>
    obtain ⟨M, a, hb⟩ := hkind
    exact Or.inr (Or.inl ⟨M, a, hb.1, tlB_vertex hn X g hc hb.1⟩)
  | sliding =>
    obtain ⟨M, a, hs⟩ := hkind
    exact Or.inr (Or.inl ⟨M, a, hs.1, tlB_vertex hn X g hc hs.1⟩)
  | triple => exact Or.inr (Or.inr (Or.inl hkind))
  | extension => exact Or.inr (Or.inr (Or.inr (Or.inl hkind)))
  | cut => exact Or.inr (Or.inr (Or.inr (Or.inr hkind)))

/-- A relative-general-position path yields the path conjunction of lem:transport. -/
theorem tlB_path_of_rgp (hn : 3 ≤ n + 1) {γ : unitInterval → LabelledTuple (n + 1)} {δ : ℝ}
    (R : RelativeGeneralPositionPath γ δ) :
    Continuous R.path ∧ R.path 0 = γ 0 ∧ R.path 1 = γ 1 ∧
      (∀ t, Regular (R.path t)) ∧
      (∃ (N : ℕ) (hN : 0 < N), ∀ j : Fin N, ∃ a b : LabelledTuple (n + 1),
        ∀ t ∈ uniformMeshCell N hN j, R.path t = a + (t : ℝ) • b) ∧
      {t : unitInterval | ¬ Generic (R.path t)}.Finite ∧
      (∀ t, ¬ Generic (R.path t) → ∃ g : WallGerm (n + 1),
        g.center = R.path t ∧
        (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
          g.curve s = R.path ⟨(t : ℝ) + s.val, hs⟩) ∧
        g.Simple ∧
        ((∃ j : ZMod (n + 1), g.FlatAt j ∧ Generic (deleteVertex (R.path t) j)) ∨
         (∃ M a : ZMod (n + 1), g.VertexEdgeAt M a ∧
            Generic (firstHalf (R.path t) M a) ∧ Generic (secondHalf (R.path t) M a) ∧
            firstHalfSize M a < n + 1 ∧ secondHalfSize M a < n + 1) ∨
         (∃ e f k : ZMod (n + 1), g.TripleAt e f k) ∨
         (∃ M a : ZMod (n + 1), g.ExtensionAt M a) ∨
         (∃ i j k : ZMod (n + 1), g.PureCutAt i j k))) := by
  refine ⟨R.continuous, R.first, R.last, R.regular, ?_, R.finite_nongeneric, ?_⟩
  · refine ⟨R.cellCount, R.cellCount_pos, fun j => ?_⟩
    obtain ⟨a, b, hab⟩ := R.affine_on_cells j
    exact ⟨tupleOfScalarCoordinates a, tupleOfScalarCoordinates b,
      fun t ht => tlB_affine_tuple _ a b _ (hab t ht)⟩
  · intro t hng
    obtain ⟨g, hc, hcurve, hsimple, hk⟩ := R.event t hng
    exact ⟨g, hc, hcurve, hsimple, tlB_event hn _ g hc hk⟩

/-- A path in the regular fibre with generic endpoints yields the transport path. -/
theorem tlB_of_joined (hn : 3 ≤ n + 1) {r : ℤ} {P Q : LabelledTuple (n + 1)}
    (hP : Generic P) (hQ : Generic Q)
    (h : JoinedIn {X : LabelledTuple (n + 1) | Regular X ∧ rotationNumber X = r} P Q) :
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
  obtain ⟨γ, hγ⟩ := h
  have hreg : ∀ t, Regular (γ t) := fun t => (hγ t).1
  have h0 : Generic (γ 0) := by rw [γ.source]; exact hP
  have h1 : Generic (γ 1) := by rw [γ.target]; exact hQ
  obtain ⟨R⟩ := relative_general_position hn γ γ.continuous hreg h0 h1 1 one_pos
  obtain ⟨hcont, hfirst, hlast, hrest⟩ := tlB_path_of_rgp hn R
  refine ⟨R.path, hcont, ?_, ?_, hrest⟩
  · rw [hfirst, γ.source]
  · rw [hlast, γ.target]

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
  have hadm : Admissible ((n + 1 : ℕ) : ℤ) r :=
    (generic_rotation_exists_iff hn r).mp ⟨P, hP, hrP⟩
  have hPreg : Regular P := generic_regular hn hP
  have hZreg : Regular Z := generic_regular hn hZ
  have D := mycyclic (n := n + 1) hadm
  by_cases h4 : ((((n + 1 : ℕ) : ℤ)), r) = (4, 0)
  · obtain ⟨k, hk⟩ := D.joined_shift P Z hPreg hZreg hrP hrZ h4
    refine ⟨k, fun h => absurd h4 h, ?_⟩
    exact tlB_of_joined hn hP ((generic_shift k Z).mpr hZ) hk
  · have hk := D.joined P Z hPreg hZreg hrP hrZ h4
    refine ⟨0, fun _ => rfl, ?_⟩
    rw [shift_zero]
    exact tlB_of_joined hn hP hZ hk

end SM
