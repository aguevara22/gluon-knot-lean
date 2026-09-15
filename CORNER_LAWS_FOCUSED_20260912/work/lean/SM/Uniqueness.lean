import SM.ALawful

set_option linter.unusedVariables false

/-! Source thm:uniqueness (reference/SM/sm-6-comparison.tex:201, frame SM15): uniqueness (Theorem 1 of
the main text). Main declaration: `SM.uniqueness`. Statement fixed by the executor
(work/drafts/Uniqueness_statement.lean); proof by a Claude Code prover subagent (workflow prove-uniqueness / attempt A), checked
with `lake env lean` (sorry-free, standard axioms) and ported verbatim from work/drafts/UniquenessA.lean (only the #print line
removed and this sentence added); attempt B (work/drafts/UniquenessB.lean, a symmetric formulation) compiles as well and is kept
as a cross-check.

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

/-! ### Helpers (all prefixed `unA_`) -/

open Filter Topology

open Classical in
/-- `Δ(P) = F(P) - A(P)` as a total function on labelled tuples (zero off the generic locus). -/
noncomputable def unA_delta (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (P : LabelledTuple n) : ℤ :=
  if h : Generic P then F n (polygonProjection ⟨P, h⟩) - amplitude P h.1 hn else 0

theorem unA_delta_of_generic (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    unA_delta F hn P = F n (polygonProjection ⟨P, hP⟩) - amplitude P hP.1 hn := by
  simp [unA_delta, hP]

theorem unA_delta_tuple (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (Q : GenericTuple n) :
    unA_delta F hn Q.val = F n (polygonProjection Q) - amplitude Q.val Q.property.1 hn :=
  unA_delta_of_generic F hn Q.property

/-- `Δ(P) = 0` iff `F(P) = A(P)`. -/
theorem unA_eq_of_delta_zero (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (h : unA_delta F hn P = 0) :
    F n (polygonProjection ⟨P, hP⟩) = amplitude P hP.1 hn := by
  rw [unA_delta_of_generic F hn hP] at h
  exact sub_eq_zero.mp h

theorem unA_delta_zero_of_eq (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (h : F n (polygonProjection ⟨P, hP⟩) = amplitude P hP.1 hn) : unA_delta F hn P = 0 := by
  rw [unA_delta_of_generic F hn hP, h, sub_self]

/-! ### (A) near a generic point of a continuous family, the polygons stay in one chamber -/

theorem unA_chamber_eventually {n : ℕ} [NeZero n] (hn : 3 ≤ n) {X : Type*} [TopologicalSpace X]
    {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X} (hx : Generic (γ x)) :
    ∀ᶠ y in 𝓝 x, ∃ hy : Generic (γ y),
      polygonProjection ⟨γ y, hy⟩ ∈ chamber (polygonProjection ⟨γ x, hx⟩) := by
  have := genericTuple_locallyPathConnected hn
  let P₀ : GenericTuple n := ⟨γ x, hx⟩
  have hU : IsOpen (labelledChamber P₀) := isOpen_connectedComponent
  have hV : IsOpen (Subtype.val '' labelledChamber P₀) :=
    (isOpen_Generic hn).isOpenMap_subtype_val _ hU
  have hmem : γ x ∈ Subtype.val '' labelledChamber P₀ := ⟨P₀, mem_connectedComponent, rfl⟩
  have hev : ∀ᶠ y in 𝓝 x, γ y ∈ Subtype.val '' labelledChamber P₀ :=
    hγ.continuousAt.preimage_mem_nhds (hV.mem_nhds hmem)
  filter_upwards [hev] with y hy
  obtain ⟨Q, hQ, hQy⟩ := hy
  have hy : Generic (γ y) := hQy ▸ Q.property
  refine ⟨hy, ?_⟩
  have hQ' : (⟨γ y, hy⟩ : GenericTuple n) ∈ labelledChamber P₀ := by
    have : (⟨γ y, hy⟩ : GenericTuple n) = Q := Subtype.ext hQy.symm
    rw [this]; exact hQ
  rw [← projection_labelledChamber_eq_chamber hn P₀]
  exact ⟨_, hQ', rfl⟩

/-- Eventual constancy of `Δ` at a generic point of a continuous family. -/
theorem unA_delta_eventually_eq (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {n : ℕ} [NeZero n] (hn : 3 ≤ n) {X : Type*}
    [TopologicalSpace X] {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X}
    (hx : Generic (γ x)) :
    ∀ᶠ y in 𝓝 x, unA_delta F hn (γ y) = unA_delta F hn (γ x) := by
  filter_upwards [unA_chamber_eventually hn hγ hx,
    ri_treeCoefficient_eventually_eq_of_generic hn hγ hx 0] with y hyF hyA
  obtain ⟨hy, hch⟩ := hyF
  obtain ⟨_, hA⟩ := hyA
  rw [unA_delta_of_generic F hn hy, unA_delta_of_generic F hn hx,
    hF.chamber n hn _ _ hch]
  have hA' : amplitude (γ y) hy.1 hn = amplitude (γ x) hx.1 hn := hA
  rw [hA']

/-! ### (C) constancy of Δ along a path with finitely many zero-jump walls -/
theorem unA_delta_const_along_path (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (path : unitInterval → LabelledTuple n) (hcont : Continuous path)
    (hfin : {t : unitInterval | ¬ Generic (path t)}.Finite)
    (hwall : ∀ t, ¬ Generic (path t) → ∃ w : WallGerm n,
        (∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Set.Icc (0 : ℝ) 1,
          w.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
        ∀ s₁ s₂ : w.Parameter, s₁.val < 0 → 0 < s₂.val →
          unA_delta F hn (w.curve s₂) = unA_delta F hn (w.curve s₁))
    (h0 : Generic (path 0)) (h1 : Generic (path 1)) :
    unA_delta F hn (path 0) = unA_delta F hn (path 1) := by
  refine ri_eq_of_locallyConstant_off_finite (fun t => unA_delta F hn (path t))
    {t : unitInterval | ¬ Generic (path t)} hfin ?_ ?_ (by simpa using h0) (by simpa using h1)
  · intro t ht
    have hgen : Generic (path t) := by simpa using ht
    exact unA_delta_eventually_eq F hF hn hcont hgen
  · intro t ht
    obtain ⟨w, hcurve, hjump⟩ := hwall t ht
    let sPlus : w.Parameter := ⟨w.radius / 2, by constructor <;> linarith [w.radius_pos]⟩
    let sMinus : w.Parameter := ⟨-(w.radius / 2), by constructor <;> linarith [w.radius_pos]⟩
    have hPlus : 0 < sPlus.val := by show 0 < w.radius / 2; linarith [w.radius_pos]
    have hMinus : sMinus.val < 0 := by show -(w.radius / 2) < 0; linarith [w.radius_pos]
    refine ⟨unA_delta F hn (w.curve sPlus), ?_⟩
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨w.radius, w.radius_pos, fun u hu hne => ?_⟩
    have hd : |(u : ℝ) - (t : ℝ)| < w.radius := by
      rw [Subtype.dist_eq, Real.dist_eq] at hu; exact hu
    let s : w.Parameter := ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hd⟩
    have hs0 : s.val ≠ 0 := sub_ne_zero.mpr (fun he => hne (Subtype.ext he))
    obtain ⟨hs, he⟩ := hcurve s
    have htu : (⟨(t : ℝ) + s.val, hs⟩ : unitInterval) = u := by
      apply Subtype.ext; show (t : ℝ) + ((u : ℝ) - (t : ℝ)) = u; ring
    rw [htu] at he
    show unA_delta F hn (path u) = unA_delta F hn (w.curve sPlus)
    rw [← he]
    rcases lt_or_gt_of_ne hs0 with hneg | hpos
    · rw [hjump s sPlus hneg hPlus]
    · rw [hjump sMinus s hMinus hpos, hjump sMinus sPlus hMinus hPlus]

/-! ### shift invariance of Δ -/
theorem unA_delta_shift (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) {Z : LabelledTuple n} (hZ : Generic Z) (k : ZMod n) :
    unA_delta F hn (shift k Z) = unA_delta F hn Z := by
  have hZk : Generic (shift k Z) := (generic_shift k Z).mpr hZ
  rw [unA_delta_of_generic F hn hZk, unA_delta_of_generic F hn hZ]
  have hproj : polygonProjection (⟨shift k Z, hZk⟩ : GenericTuple n) =
      polygonProjection ⟨Z, hZ⟩ := projection_genericShift k ⟨Z, hZ⟩
  have hA : amplitude (shift k Z) hZk.1 hn = amplitude Z hZ.1 hn :=
    A_lawful.shift_invariant n hn Z hZ k
  rw [hproj, hA]

/-! ### (B-F) flat wall: Δ has zero jump given the IH at the deletion -/
theorem unA_flat_wall_delta_eq (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {m : ℕ} [NeZero m] (hm : 3 ≤ m) (w : WallGerm (m + 1))
    (j : ZMod (m + 1)) (hf : w.FlatAt j) (hQ : Generic (deleteVertex w.center j))
    (IH : unA_delta F hm (deleteVertex w.center j) = 0)
    (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    unA_delta F (by omega) (w.curve s₂) = unA_delta F (by omega) (w.curve s₁) := by
  have hlawF := hF.flat m w j hf hQ
  have hlawA := (A_lawful.flat_law m w j hf).2
  obtain ⟨b, ⟨hR, hL⟩, -⟩ := w.flat_named_sides hf
  have hg2 := w.generic_punctured s₂ h₂.ne'
  have hg1 := w.generic_punctured s₁ h₁.ne
  rw [unA_delta_of_generic F _ hg2, unA_delta_of_generic F _ hg1]
  rw [unA_delta_of_generic F hm hQ] at IH
  have hAdel : amplitude (deleteVertex w.center j) (g1_deleteVertex hf.2.1) (by have := hf.1; omega) =
      amplitude (deleteVertex w.center j) hQ.1 hm := rfl
  cases b with
  | true =>
    have hL' : w.FlatLeftSide j false := hL
    have ht2 : turn (w.curve s₂) j = -1 := by
      have := hR ⟨s₂.val, h₂, s₂.property.2⟩
      rwa [w.ri_sideTuple_true_val s₂ h₂] at this
    have ht1 : turn (w.curve s₁) j = 1 := by
      have := hL' ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
      rwa [w.ri_sideTuple_false_val s₁ h₁] at this
    have eF := hlawF s₂ s₁ h₂.ne' h₁.ne ht2 ht1
    have eA := hlawA s₂ s₁ h₂.ne' h₁.ne ht2 ht1
    rw [hAdel] at eA
    linarith
  | false =>
    have hL' : w.FlatLeftSide j true := hL
    have ht1 : turn (w.curve s₁) j = -1 := by
      have := hR ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
      rwa [w.ri_sideTuple_false_val s₁ h₁] at this
    have ht2 : turn (w.curve s₂) j = 1 := by
      have := hL' ⟨s₂.val, h₂, s₂.property.2⟩
      rwa [w.ri_sideTuple_true_val s₂ h₂] at this
    have eF := hlawF s₁ s₂ h₁.ne h₂.ne' ht1 ht2
    have eA := hlawA s₁ s₂ h₁.ne h₂.ne' ht1 ht2
    rw [hAdel] at eA
    linarith

/-! ### (B-V) vertex–edge wall -/
theorem unA_vertexEdge_wall_delta_eq (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n)
    (hc : w.VertexEdgeAt M a)
    (IH1 : F (firstHalfSize M a)
        (polygonProjection ⟨firstHalf w.center M a, (A_lawful.vertex_edge_law n hn w M a hc).1⟩) =
      amplitude (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
        (contactHalfSizes_bounds hn hc.1).1.1)
    (IH2 : F (secondHalfSize M a)
        (polygonProjection ⟨secondHalf w.center M a, (A_lawful.vertex_edge_law n hn w M a hc).2.1⟩) =
      amplitude (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
        (contactHalfSizes_bounds hn hc.1).2.1)
    (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    unA_delta F hn (w.curve s₂) = unA_delta F hn (w.curve s₁) := by
  obtain ⟨hg1, hg2, hlawA⟩ := A_lawful.vertex_edge_law n hn w M a hc
  let t : w.SideParameter := ⟨s₂.val, h₂, s₂.property.2⟩
  let s : w.SideParameter := ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
  have e2 : (w.sideTuple true t).val = w.curve s₂ := w.ri_sideTuple_true_val s₂ h₂
  have e1 : (w.sideTuple false s).val = w.curve s₁ := w.ri_sideTuple_false_val s₁ h₁
  rw [← e2, ← e1, unA_delta_tuple, unA_delta_tuple]
  have eF := hF.vertex_edge n hn w M a hc hg1 hg2 s t
  have eA := hlawA s t
  rw [IH1, IH2] at eF
  linarith

/-! ### (B-TEC) triple / extension / cut walls -/
theorem unA_silent_wall_delta_eq (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n)
    (hw : (∃ e f k, w.TripleAt e f k) ∨ (∃ M a, w.ExtensionAt M a) ∨ (∃ i j k, w.PureCutAt i j k))
    (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    unA_delta F hn (w.curve s₂) = unA_delta F hn (w.curve s₁) := by
  let t : w.SideParameter := ⟨s₂.val, h₂, s₂.property.2⟩
  let s : w.SideParameter := ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
  have e2 : (w.sideTuple true t).val = w.curve s₂ := w.ri_sideTuple_true_val s₂ h₂
  have e1 : (w.sideTuple false s).val = w.curve s₁ := w.ri_sideTuple_false_val s₁ h₁
  rw [← e2, ← e1, unA_delta_tuple, unA_delta_tuple]
  have keyF : F n (polygonProjection (w.sideTuple true t)) =
      F n (polygonProjection (w.sideTuple false s)) := by
    rcases hw with ⟨e, f, k, hT⟩ | ⟨M, a, hE⟩ | ⟨i, j, k, hC⟩
    · exact hF.triple n hn w e f k hT s t
    · exact (hF.silent n hn w).1 M a hE s t
    · exact (hF.silent n hn w).2 i j k hC s t
  have keyA : amplitude (w.sideTuple true t).val (w.sideTuple true t).property.1 hn =
      amplitude (w.sideTuple false s).val (w.sideTuple false s).property.1 hn := by
    rcases hw with ⟨e, f, k, hT⟩ | ⟨M, a, hE⟩ | ⟨i, j, k, hC⟩
    · exact A_lawful.triple_law n hn w e f k hT s t
    · exact (A_lawful.silent n hn w).1 M a hE s t
    · exact (A_lawful.silent n hn w).2 i j k hC s t
  rw [keyF, keyA]

/-- The induction hypothesis: `F = A` at every arity below `N`. -/
def unA_Below (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (N : ℕ) : Prop :=
  ∀ k < N, ∀ [NeZero k] (hk : 3 ≤ k) (Q : LabelledTuple k) (hQ : Generic Q),
    F k (polygonProjection ⟨Q, hQ⟩) = amplitude Q hQ.1 hk

/-! ### (C') Δ is transported from P to the target along the path of `SM.transport_lemma` -/
theorem unA_delta_eq_target_of_transport (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {m : ℕ} [NeZero (m + 1)] (hm : 3 ≤ m + 1)
    (IH : unA_Below F (m + 1)) {r : ℤ} {P Z : LabelledTuple (m + 1)}
    (hP : Generic P) (hZ : Generic Z) (hrP : rotationNumber P = r) (hrZ : rotationNumber Z = r) :
    unA_delta F hm P = unA_delta F hm Z := by
  obtain ⟨k, -, path, hcont, h0, h1, -, -, hfin, hwall⟩ :=
    transport_lemma hm hP hZ hrP hrZ
  rw [← unA_delta_shift F hm hZ k, ← h0, ← h1]
  apply unA_delta_const_along_path F hF hm path hcont hfin _ (h0 ▸ hP)
    (h1 ▸ (generic_shift k Z).mpr hZ)
  intro t ht
  obtain ⟨w, hcenter, hcurve, -, halt⟩ := hwall t ht
  refine ⟨w, hcurve, ?_⟩
  intro s₁ s₂ h₁ h₂
  rcases halt with ⟨j, hf, hdel⟩ | ⟨M, a, hc, hfst, hsnd, hlt1, hlt2⟩ | hT | hE | hC
  · have hQ : Generic (deleteVertex w.center j) := by rw [hcenter]; exact hdel
    have hm3 : 3 ≤ m := by have := hf.1; omega
    have : NeZero m := ⟨by omega⟩
    exact unA_flat_wall_delta_eq F hF hm3 w j hf hQ
      (unA_delta_zero_of_eq F hm3 hQ (IH m (by omega) hm3 _ hQ)) s₁ s₂ h₁ h₂
  · have hb := contactHalfSizes_bounds hm hc.1
    exact unA_vertexEdge_wall_delta_eq F hF hm w M a hc
      (IH _ hlt1 hb.1.1 _ (A_lawful.vertex_edge_law _ hm w M a hc).1)
      (IH _ hlt2 hb.2.1 _ (A_lawful.vertex_edge_law _ hm w M a hc).2.1) s₁ s₂ h₁ h₂
  · exact unA_silent_wall_delta_eq F hF hm w (Or.inl hT) s₁ s₂ h₁ h₂
  · exact unA_silent_wall_delta_eq F hF hm w (Or.inr (Or.inl hE)) s₁ s₂ h₁ h₂
  · exact unA_silent_wall_delta_eq F hF hm w (Or.inr (Or.inr hC)) s₁ s₂ h₁ h₂

/-! ### (D) anchor values (prop:anchor-values) for `F` and for `A`: `Δ(P_ε) = mult · Δ(P)` -/
theorem unA_softAnchor_delta (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {m : ℕ} [NeZero m] (A : SoftAnchorData m) :
    (unA_delta F (by have := A.parent_card; omega)
        (softInsertion A.parent A.vertex A.vector A.param) : ℚ) =
      softAmplitudeMultiplier A.parent A.vertex A.vector *
        (unA_delta F A.parent_card A.parent : ℚ) := by
  have hm := A.parent_card
  have hm1 : 3 ≤ m + 1 := by omega
  obtain ⟨δF, hδF, hsoftF⟩ :=
    hF.soft m hm A.parent A.parent_generic A.vertex A.vector A.admissible
  obtain ⟨ε₁, hε₁, hsoftA⟩ :=
    A_lawful.soft_theorem m hm A.parent A.parent_generic A.vertex A.vector A.admissible
  obtain ⟨ε', hε'pos, hε'param, hε'δ, hε'ε₁⟩ :
      ∃ ε' : ℝ, 0 < ε' ∧ ε' < A.param ∧ ε' < δF ∧ ε' < ε₁ := by
    have hmin : 0 < min (min A.param δF) ε₁ := lt_min (lt_min A.param_pos hδF) hε₁
    have h1 : min (min A.param δF) ε₁ ≤ A.param := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min A.param δF) ε₁ ≤ δF := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : min (min A.param δF) ε₁ ≤ ε₁ := min_le_right _ _
    exact ⟨min (min A.param δF) ε₁ / 2, by linarith, by linarith, by linarith, by linarith⟩
  have hε'bound : ε' < A.bound := hε'param.trans A.param_lt
  obtain ⟨B, hB⟩ := A.bound_spec
  obtain ⟨hQ', -, hch'⟩ := hB ε' hε'pos hε'bound
  obtain ⟨hQ, -, hch⟩ := hB A.param A.param_pos A.param_lt
  have hFch : F (m + 1) (polygonProjection ⟨softInsertion A.parent A.vertex A.vector A.param, hQ⟩) =
      F (m + 1) (polygonProjection ⟨softInsertion A.parent A.vertex A.vector ε', hQ'⟩) := by
    rw [hF.chamber (m + 1) hm1 _ _ hch, hF.chamber (m + 1) hm1 _ _ hch']
  have hAch : amplitude (softInsertion A.parent A.vertex A.vector A.param) hQ.1 hm1 =
      amplitude (softInsertion A.parent A.vertex A.vector ε') hQ'.1 hm1 := by
    rw [(A_lawful.chamber_constant (m + 1) hm1 B _).2 hch,
      (A_lawful.chamber_constant (m + 1) hm1 B _).2 hch']
  have hFs := hsoftF ε' hε'pos hε'δ hQ'
  obtain ⟨hQ'', hAs⟩ := hsoftA ε' hε'pos hε'ε₁
  have hAs' : (amplitude (softInsertion A.parent A.vertex A.vector ε') hQ'.1 hm1 : ℚ) =
      softAmplitudeMultiplier A.parent A.vertex A.vector *
        (amplitude A.parent A.parent_generic.1 hm : ℚ) := hAs
  rw [unA_delta_of_generic F hm1 hQ, unA_delta_of_generic F hm A.parent_generic]
  push_cast
  rw [hFch, hAch, hFs, hAs']
  ring

/-- Zero anchors: `Δ(Z) = 0` (mixed sector, multiplier `0`). -/
theorem unA_zeroAnchor_delta (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {m : ℕ} [NeZero m] {r : ℤ} (A : ZeroAnchor m r) :
    unA_delta F (by have := A.parent_card; omega) A.polygon = 0 := by
  have h := unA_softAnchor_delta F hF A.toSoftAnchorData
  rw [softAmplitudeMultiplier_mixed _ _ _ A.admissible A.mixed, zero_mul] at h
  exact_mod_cast h

/-- Loop anchors: `Δ(Y) = τ_j(P) Δ(P) = 0` when `Δ(P) = 0` at the parent. -/
theorem unA_loopAnchor_delta (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {m : ℕ} [NeZero m] (A : SoftAnchorData m)
    (hloop : softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
      softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex)
    (hparent : unA_delta F A.parent_card A.parent = 0) :
    unA_delta F (by have := A.parent_card; omega) A.polygon = 0 := by
  have h := unA_softAnchor_delta F hF A
  rw [softAmplitudeMultiplier_loop _ _ _ hloop, hparent, Int.cast_zero, mul_zero] at h
  exact_mod_cast h

/-- `Δ = 0` at every anchor, given the induction hypothesis below `m + 1`. -/
theorem unA_anchor_delta (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) {m : ℕ} [NeZero m] (hm : 3 ≤ m) (IH : unA_Below F (m + 1))
    {r : ℤ} (A : Anchor m r) :
    unA_delta F (by omega) A.polygon = 0 := by
  cases A with
  | zero hZ A₀ => exact unA_zeroAnchor_delta F hF A₀
  | loop hL hr A₀ =>
    exact unA_loopAnchor_delta F hF A₀.toSoftAnchorData A₀.loop
      (unA_delta_zero_of_eq F A₀.parent_card A₀.parent_generic
        (IH m (by omega) A₀.parent_card _ A₀.parent_generic))
  | loopZero hL₀ A₀ =>
    exact unA_loopAnchor_delta F hF A₀.toSoftAnchorData A₀.loop
      (unA_delta_zero_of_eq F A₀.parent_card A₀.parent_generic
        (IH m (by omega) A₀.parent_card _ A₀.parent_generic))

/-! ### (E) the strong induction -/
theorem unA_all (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (hF : UniquenessHypotheses F) :
    ∀ n : ℕ, ∀ [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      F n (polygonProjection ⟨P, hP⟩) = amplitude P hP.1 hn := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro _ hn P hP
  have hIH : unA_Below F n := fun k hk _ hk3 Q hQ => IH k hk hk3 Q hQ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨r, hr⟩ := rotationNumber_integer (generic_regular hn hP)
  apply unA_eq_of_delta_zero F hn hP
  by_cases h3 : m + 1 = 3
  · -- base `n = 3`: transport to the triangle star `K_1` or `K_{-1}`
    have hm2 : m = 2 := by omega
    subst hm2
    rcases (rotationNumber_triangle (generic_regular hn hP)).2.1 with h1 | h1
    · have hZ : Generic (star 1) := (star_generic_law le_rfl).1.2.2.2.1
      have hrZ : rotationNumber (star 1) = ((1 : ℤ) : ℝ) := by
        rw [(star_generic_law le_rfl).1.2.1.2.2.2.2]; simp
      have hrP : rotationNumber P = ((1 : ℤ) : ℝ) := by rw [h1]; simp
      rw [unA_delta_eq_target_of_transport F hF hn hIH hP hZ hrP hrZ,
        unA_delta_of_generic F hn hZ]
      have e1 : F 3 (polygonProjection ⟨star 1, hZ⟩) = -1 := hF.triangles.1
      have e2 : amplitude (star 1) hZ.1 hn = -1 := A_lawful.triangles.1
      linarith
    · have hZ : Generic (starNeg 1) := (star_generic_law le_rfl).1.2.2.2.2.1
      have hrZ : rotationNumber (starNeg 1) = ((-1 : ℤ) : ℝ) := by
        rw [(star_generic_law le_rfl).1.2.2.2.2.2.2]; simp
      have hrP : rotationNumber P = ((-1 : ℤ) : ℝ) := by rw [h1]; simp
      rw [unA_delta_eq_target_of_transport F hF hn hIH hP hZ hrP hrZ,
        unA_delta_of_generic F hn hZ]
      have e1 : F 3 (polygonProjection ⟨starNeg 1, hZ⟩) = 1 := hF.triangles.2
      have e2 : amplitude (starNeg 1) hZ.1 hn = 1 := A_lawful.triangles.2
      linarith
  · -- step `n ≥ 4`: transport to an anchor for `(n, r)`
    have hm3 : 3 ≤ m := by omega
    have : NeZero m := ⟨by omega⟩
    have hadm : Admissible ((m + 1 : ℕ) : ℤ) r := generic_rotation_admissible hn hP r hr
    have hadm' : Admissible ((m : ℤ) + 1) r := by push_cast at hadm; exact hadm
    obtain ⟨A⟩ := anchor_exists r hadm' (by omega)
    rw [unA_delta_eq_target_of_transport F hF hn hIH hP A.polygon_generic hr A.polygon_rotation]
    exact unA_anchor_delta F hF hm3 hIH A

/-- thm:uniqueness as printed on SM15: a function `F` on generic polygons of every arity `n ≥ 3`
satisfying (a)–(f) equals `A` on every generic polygon. -/
theorem uniqueness (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      F n (polygonProjection ⟨P, hP⟩) = amplitude P hP.1 hn :=
  unA_all F hF

end SM

