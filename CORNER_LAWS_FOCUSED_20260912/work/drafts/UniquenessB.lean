import SM.ALawful

set_option linter.unusedVariables false

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


/-! ### Helpers (all prefixed `unB_`)

Strategy. Any two functions `F, G` satisfying (a)–(f) agree (`unB_agree_all`): put
`Δ = F − G` as a total function on labelled tuples (`unB_delta`, zero off the generic locus) and
argue by strong induction on the arity, transporting `Δ` along the path of lem:transport
(`SM.transport_lemma`) to an anchor (n ≥ 4) or to a star triangle (n = 3). The amplitude `A`
satisfies (a)–(f) by cor:A-lawful (`unB_A_hypotheses`), which gives thm:uniqueness. -/

open Filter Topology

section Helpers

variable {F G : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ}

/-! #### Chamber constancy along continuous families -/

/-- Chamber constancy (a) read on labelled chambers: the projection maps the labelled chamber of
`P` into the chamber of its polygon. -/
theorem unB_eq_of_labelledChamber (hF : UniquenessHypotheses F) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (P Q : GenericTuple n) (hQ : Q ∈ labelledChamber P) :
    F n (polygonProjection Q) = F n (polygonProjection P) :=
  hF.chamber n hn _ _
    (continuous_polygonProjection.image_connectedComponent_subset P ⟨Q, hQ, rfl⟩)

/-- Along a continuous family of labelled tuples, the members near a generic member are generic
and lie in its labelled chamber. -/
theorem unB_eventually_labelledChamber {n : ℕ} (hn : 3 ≤ n) {X : Type*} [TopologicalSpace X]
    {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X} (hx : Generic (γ x)) :
    ∀ᶠ y in 𝓝 x, ∃ hy : Generic (γ y),
      (⟨γ y, hy⟩ : GenericTuple n) ∈ labelledChamber ⟨γ x, hx⟩ := by
  have hopen : IsOpen (labelledChamber (⟨γ x, hx⟩ : GenericTuple n)) :=
    (labelledChambers_open_pathConnected hn _).1
  have hmem : labelledChamber (⟨γ x, hx⟩ : GenericTuple n) ∈ 𝓝 (⟨γ x, hx⟩ : GenericTuple n) :=
    hopen.mem_nhds mem_connectedComponent
  obtain ⟨U, hU, hUsub⟩ := (mem_nhds_induced Subtype.val _ _).mp hmem
  have h1 : γ ⁻¹' U ∈ 𝓝 x := hγ.continuousAt.preimage_mem_nhds hU
  have h2 : ∀ᶠ y in 𝓝 x, Generic (γ y) := hγ.continuousAt.eventually (generic_persists hn hx)
  filter_upwards [h1, h2] with y hyU hy
  exact ⟨hy, hUsub hyU⟩

/-! #### `Δ = F − G` as a total function on labelled tuples -/

open Classical in
/-- `Δ(P) = F(P) − G(P)` on generic tuples, `0` elsewhere. -/
noncomputable def unB_delta (F G : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) {n : ℕ}
    [NeZero n] (P : LabelledTuple n) : ℤ :=
  if hP : Generic P then
    F n (polygonProjection ⟨P, hP⟩) - G n (polygonProjection ⟨P, hP⟩)
  else 0

theorem unB_delta_of_generic (F G : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) {n : ℕ}
    [NeZero n] {P : LabelledTuple n} (hP : Generic P) :
    unB_delta F G P = F n (polygonProjection ⟨P, hP⟩) - G n (polygonProjection ⟨P, hP⟩) := by
  simp [unB_delta, hP]

/-- `Δ` is invariant under the cyclic shift (both `F` and `G` are functions of the polygon). -/
theorem unB_delta_shift {n : ℕ} [NeZero n] (k : ZMod n) {Z : LabelledTuple n} (hZ : Generic Z) :
    unB_delta F G (shift k Z) = unB_delta F G Z := by
  have hZk : Generic (shift k Z) := (generic_shift k Z).mpr hZ
  rw [unB_delta_of_generic F G hZk, unB_delta_of_generic F G hZ]
  have h : polygonProjection (⟨shift k Z, hZk⟩ : GenericTuple n) = polygonProjection ⟨Z, hZ⟩ :=
    projection_genericShift k ⟨Z, hZ⟩
  rw [h]

/-- `Δ` is locally constant at a generic member of a continuous family (chamber constancy). -/
theorem unB_delta_eventually_eq (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) {X : Type*} [TopologicalSpace X]
    {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X} (hx : Generic (γ x)) :
    ∀ᶠ y in 𝓝 x, unB_delta F G (γ y) = unB_delta F G (γ x) := by
  filter_upwards [unB_eventually_labelledChamber hn hγ hx] with y hy
  obtain ⟨hy, hmem⟩ := hy
  rw [unB_delta_of_generic F G hy, unB_delta_of_generic F G hx,
    unB_eq_of_labelledChamber hF hn _ _ hmem, unB_eq_of_labelledChamber hG hn _ _ hmem]

end Helpers

/-! #### The amplitude `A` as a function on polygons satisfying (a)–(f) -/

/-- The descended amplitude on the polygon spaces of every arity (`0` below arity `3`). -/
noncomputable def unB_Apoly : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ :=
  fun n _ Q => if hn : 3 ≤ n then alA_polygonAmplitude hn Q else 0

theorem unB_Apoly_projection {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : GenericTuple n) :
    unB_Apoly n (polygonProjection P) = amplitude P.val P.property.1 hn := by
  simp only [unB_Apoly, hn, ↓reduceDIte]
  rfl

/-- cor:A-lawful read as the hypotheses (a)–(f) of thm:uniqueness for `A`. -/
theorem unB_A_hypotheses : UniquenessHypotheses unB_Apoly where
  chamber := by
    intro n _ hn P Q hQ
    induction P using Quotient.inductionOn with
    | h P =>
    induction Q using Quotient.inductionOn with
    | h Q =>
    simp only [unB_Apoly, hn, ↓reduceDIte]
    exact (A_lawful.chamber_constant n hn P Q).2 hQ
  silent := by
    intro n _ hn w
    obtain ⟨hE, hC⟩ := A_lawful.silent n hn w
    refine ⟨fun M a h s t => ?_, fun i j k h s t => ?_⟩
    · rw [unB_Apoly_projection hn, unB_Apoly_projection hn]
      exact hE M a h s t
    · rw [unB_Apoly_projection hn, unB_Apoly_projection hn]
      exact hC i j k h s t
  flat := by
    intro n _ w j hf hdel sRight sLeft hRight0 hLeft0 hR hL
    have hn : 3 ≤ n := by have := hf.1; omega
    have hn1 : 3 ≤ n + 1 := by omega
    rw [unB_Apoly_projection hn1, unB_Apoly_projection hn1, unB_Apoly_projection hn]
    exact (A_lawful.flat_law n w j hf).2 sRight sLeft hRight0 hLeft0 hR hL
  vertex_edge := by
    intro n _ hn w M a hc h₁ h₂ s t
    have hb := contactHalfSizes_bounds hn hc.1
    rw [unB_Apoly_projection hn, unB_Apoly_projection hn, unB_Apoly_projection hb.1.1,
      unB_Apoly_projection hb.2.1]
    exact (A_lawful.vertex_edge_law n hn w M a hc).2.2 s t
  triple := by
    intro n _ hn w e f k h s t
    rw [unB_Apoly_projection hn, unB_Apoly_projection hn]
    exact A_lawful.triple_law n hn w e f k h s t
  soft := by
    intro n _ hn P hP j q hq
    obtain ⟨ε₁, hε₁, h⟩ := A_lawful.soft_theorem n hn P hP j q hq
    refine ⟨ε₁, hε₁, fun ε hε hεlt hQ => ?_⟩
    obtain ⟨hQ', heq⟩ := h ε hε hεlt
    rw [unB_Apoly_projection (by omega), unB_Apoly_projection hn]
    exact heq
  triangles := by
    constructor
    · rw [unB_Apoly_projection (by norm_num)]
      exact alA_star_one
    · rw [unB_Apoly_projection (by norm_num)]
      exact alA_starNeg_one

section Transport

variable {F G : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ}

/-! #### Wall jumps of `Δ` -/

/-- At a simple flat wall the jump of `Δ` is `Δ(P(0) ∖ j)`, which vanishes once `F = G` at the
deletion. -/
theorem unB_flat_wall_delta_eq (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {n : ℕ} [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.FlatAt j)
    (hQ : Generic (deleteVertex w.center j))
    (IH : F n (polygonProjection ⟨deleteVertex w.center j, hQ⟩) =
      G n (polygonProjection ⟨deleteVertex w.center j, hQ⟩))
    (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    unB_delta F G (w.curve s₂) = unB_delta F G (w.curve s₁) := by
  obtain ⟨b, ⟨hR, hL⟩, -⟩ := w.flat_named_sides hf
  have hg2 := w.generic_punctured s₂ h₂.ne'
  have hg1 := w.generic_punctured s₁ h₁.ne
  rw [unB_delta_of_generic F G hg2, unB_delta_of_generic F G hg1]
  cases b with
  | true =>
    have hL' : w.FlatLeftSide j false := hL
    have ht2 : turn (w.curve s₂) j = -1 := by
      have := hR ⟨s₂.val, h₂, s₂.property.2⟩
      rwa [w.ri_sideTuple_true_val s₂ h₂] at this
    have ht1 : turn (w.curve s₁) j = 1 := by
      have := hL' ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
      rwa [w.ri_sideTuple_false_val s₁ h₁] at this
    have eF := hF.flat n w j hf hQ s₂ s₁ h₂.ne' h₁.ne ht2 ht1
    have eG := hG.flat n w j hf hQ s₂ s₁ h₂.ne' h₁.ne ht2 ht1
    linarith
  | false =>
    have hL' : w.FlatLeftSide j true := hL
    have ht1 : turn (w.curve s₁) j = -1 := by
      have := hR ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
      rwa [w.ri_sideTuple_false_val s₁ h₁] at this
    have ht2 : turn (w.curve s₂) j = 1 := by
      have := hL' ⟨s₂.val, h₂, s₂.property.2⟩
      rwa [w.ri_sideTuple_true_val s₂ h₂] at this
    have eF := hF.flat n w j hf hQ s₁ s₂ h₁.ne h₂.ne' ht1 ht2
    have eG := hG.flat n w j hf hQ s₁ s₂ h₁.ne h₂.ne' ht1 ht2
    linarith

/-- At a simple vertex–edge wall the jump of `Δ` is
`s (F(λ₁)F(λ₂) − G(λ₁)G(λ₂))`, which vanishes once `F = G` on both halves. -/
theorem unB_vertexEdge_wall_delta_eq (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n) (hc : w.VertexEdgeAt M a)
    (h₁ : Generic (firstHalf w.center M a)) (h₂ : Generic (secondHalf w.center M a))
    (IH1 : F (firstHalfSize M a) (polygonProjection ⟨firstHalf w.center M a, h₁⟩) =
      G (firstHalfSize M a) (polygonProjection ⟨firstHalf w.center M a, h₁⟩))
    (IH2 : F (secondHalfSize M a) (polygonProjection ⟨secondHalf w.center M a, h₂⟩) =
      G (secondHalfSize M a) (polygonProjection ⟨secondHalf w.center M a, h₂⟩))
    (s₁ s₂ : w.Parameter) (hs₁ : s₁.val < 0) (hs₂ : 0 < s₂.val) :
    unB_delta F G (w.curve s₂) = unB_delta F G (w.curve s₁) := by
  let t : w.SideParameter := ⟨s₂.val, hs₂, s₂.property.2⟩
  let s : w.SideParameter := ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
  have hg2 := w.generic_punctured s₂ hs₂.ne'
  have hg1 := w.generic_punctured s₁ hs₁.ne
  have e2 : w.sideTuple true t = ⟨w.curve s₂, hg2⟩ := Subtype.ext (w.ri_sideTuple_true_val s₂ hs₂)
  have e1 : w.sideTuple false s = ⟨w.curve s₁, hg1⟩ :=
    Subtype.ext (w.ri_sideTuple_false_val s₁ hs₁)
  have eF := hF.vertex_edge n hn w M a hc h₁ h₂ s t
  have eG := hG.vertex_edge n hn w M a hc h₁ h₂ s t
  rw [e2, e1] at eF eG
  rw [IH1, IH2] at eF
  rw [unB_delta_of_generic F G hg2, unB_delta_of_generic F G hg1]
  linarith

/-- At a simple triple, extension or pure-cut wall `Δ` does not jump. -/
theorem unB_silent_wall_delta_eq (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n)
    (hw : (∃ e f k, w.TripleAt e f k) ∨ (∃ M a, w.ExtensionAt M a) ∨
      (∃ i j k, w.PureCutAt i j k))
    (s₁ s₂ : w.Parameter) (hs₁ : s₁.val < 0) (hs₂ : 0 < s₂.val) :
    unB_delta F G (w.curve s₂) = unB_delta F G (w.curve s₁) := by
  let t : w.SideParameter := ⟨s₂.val, hs₂, s₂.property.2⟩
  let s : w.SideParameter := ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
  have hg2 := w.generic_punctured s₂ hs₂.ne'
  have hg1 := w.generic_punctured s₁ hs₁.ne
  have e2 : w.sideTuple true t = ⟨w.curve s₂, hg2⟩ := Subtype.ext (w.ri_sideTuple_true_val s₂ hs₂)
  have e1 : w.sideTuple false s = ⟨w.curve s₁, hg1⟩ :=
    Subtype.ext (w.ri_sideTuple_false_val s₁ hs₁)
  have key : ∀ (H : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ), UniquenessHypotheses H →
      H n (polygonProjection (w.sideTuple true t)) =
        H n (polygonProjection (w.sideTuple false s)) := by
    intro H hH
    rcases hw with ⟨e, f, k, hT⟩ | ⟨M, a, hE⟩ | ⟨i, j, k, hC⟩
    · exact hH.triple n hn w e f k hT s t
    · exact (hH.silent n hn w).1 M a hE s t
    · exact (hH.silent n hn w).2 i j k hC s t
  have kF := key F hF
  have kG := key G hG
  rw [e2, e1] at kF kG
  rw [unB_delta_of_generic F G hg2, unB_delta_of_generic F G hg1, kF, kG]

/-! #### Constancy of `Δ` along a path with finitely many zero-jump walls -/

theorem unB_delta_const_along_path (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (path : unitInterval → LabelledTuple n) (hcont : Continuous path)
    (hfin : {t : unitInterval | ¬ Generic (path t)}.Finite)
    (hwall : ∀ t, ¬ Generic (path t) → ∃ w : WallGerm n,
        (∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Set.Icc (0 : ℝ) 1,
          w.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
        ∀ s₁ s₂ : w.Parameter, s₁.val < 0 → 0 < s₂.val →
          unB_delta F G (w.curve s₂) = unB_delta F G (w.curve s₁))
    (h0 : Generic (path 0)) (h1 : Generic (path 1)) :
    unB_delta F G (path 0) = unB_delta F G (path 1) := by
  refine ri_eq_of_locallyConstant_off_finite (fun t => unB_delta F G (path t))
    {t : unitInterval | ¬ Generic (path t)} hfin ?_ ?_ (by simpa using h0) (by simpa using h1)
  · intro t ht
    have hgen : Generic (path t) := by simpa using ht
    exact unB_delta_eventually_eq hF hG hn hcont hgen
  · intro t ht
    obtain ⟨w, hcurve, hjump⟩ := hwall t ht
    let sPlus : w.Parameter := ⟨w.radius / 2, by constructor <;> linarith [w.radius_pos]⟩
    let sMinus : w.Parameter := ⟨-(w.radius / 2), by constructor <;> linarith [w.radius_pos]⟩
    have hPlus : 0 < sPlus.val := by show 0 < w.radius / 2; linarith [w.radius_pos]
    have hMinus : sMinus.val < 0 := by show -(w.radius / 2) < 0; linarith [w.radius_pos]
    refine ⟨unB_delta F G (w.curve sPlus), ?_⟩
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
    show unB_delta F G (path u) = unB_delta F G (w.curve sPlus)
    rw [← he]
    rcases lt_or_gt_of_ne hs0 with hneg | hpos
    · rw [hjump s sPlus hneg hPlus]
    · rw [hjump sMinus s hMinus hpos, hjump sMinus sPlus hMinus hPlus]

/-! #### The induction hypothesis and transport to a target -/

/-- `F = G` on every generic polygon of arity `3 ≤ k < N`. -/
def unB_AgreeBelow (F G : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (N : ℕ) : Prop :=
  ∀ k < N, ∀ [NeZero k] (hk : 3 ≤ k) (Q : LabelledTuple k) (hQ : Generic Q),
    F k (polygonProjection ⟨Q, hQ⟩) = G k (polygonProjection ⟨Q, hQ⟩)

/-- `Δ` is transported from `P` to (a shift of) any generic target `Z` of the same rotation
along the path of lem:transport, given `F = G` below the current arity. -/
theorem unB_delta_eq_target_of_transport (hF : UniquenessHypotheses F)
    (hG : UniquenessHypotheses G) {m : ℕ} (hm : 3 ≤ m + 1)
    (IH : unB_AgreeBelow F G (m + 1)) {r : ℤ} {P Z : LabelledTuple (m + 1)}
    (hP : Generic P) (hZ : Generic Z) (hrP : rotationNumber P = r) (hrZ : rotationNumber Z = r) :
    ∃ k : ZMod (m + 1), ((((m + 1 : ℕ) : ℤ), r) ≠ (4, 0) → k = 0) ∧
      unB_delta F G P = unB_delta F G (shift k Z) := by
  obtain ⟨k, hk, path, hcont, h0, h1, -, -, hfin, hwall⟩ := transport_lemma hm hP hZ hrP hrZ
  refine ⟨k, hk, ?_⟩
  rw [← h0, ← h1]
  apply unB_delta_const_along_path hF hG hm path hcont hfin _ (h0 ▸ hP)
    (h1 ▸ (generic_shift k Z).mpr hZ)
  intro t ht
  obtain ⟨w, hcenter, hcurve, -, halt⟩ := hwall t ht
  refine ⟨w, hcurve, ?_⟩
  intro s₁ s₂ h₁ h₂
  rcases halt with ⟨j, hf, hdel⟩ | ⟨M, a, hc, hfst, hsnd, hlt1, hlt2⟩ | hT | hE | hC
  · have hQ : Generic (deleteVertex w.center j) := by rw [hcenter]; exact hdel
    have hm3 : 3 ≤ m := by have := hf.1; omega
    have : NeZero m := ⟨by omega⟩
    exact unB_flat_wall_delta_eq hF hG w j hf hQ (IH m (by omega) hm3 _ hQ) s₁ s₂ h₁ h₂
  · have hfst' : Generic (firstHalf w.center M a) := by rw [hcenter]; exact hfst
    have hsnd' : Generic (secondHalf w.center M a) := by rw [hcenter]; exact hsnd
    have hb := contactHalfSizes_bounds hm hc.1
    exact unB_vertexEdge_wall_delta_eq hF hG hm w M a hc hfst' hsnd'
      (IH _ hlt1 hb.1.1 _ hfst') (IH _ hlt2 hb.2.1 _ hsnd') s₁ s₂ h₁ h₂
  · exact unB_silent_wall_delta_eq hF hG hm w (Or.inl hT) s₁ s₂ h₁ h₂
  · exact unB_silent_wall_delta_eq hF hG hm w (Or.inr (Or.inl hE)) s₁ s₂ h₁ h₂
  · exact unB_silent_wall_delta_eq hF hG hm w (Or.inr (Or.inr hC)) s₁ s₂ h₁ h₂

/-! #### Anchor values (prop:anchor-values, from (a) and (e) alone) -/

/-- prop:anchor-values: for a function satisfying (a) and (e), the value at the anchor
`P^{(j,q)}_ε` is `((χ_- + χ_+)/2) · F(P)`: the soft theorem holds for small `ε'`, and `P_ε`,
`P_ε'` lie in one chamber. -/
theorem unB_soft_anchor_value (hF : UniquenessHypotheses F) {m : ℕ} [NeZero m]
    (A : SoftAnchorData m) :
    (F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) : ℚ) =
      softAmplitudeMultiplier A.parent A.vertex A.vector *
        (F m (polygonProjection ⟨A.parent, A.parent_generic⟩) : ℚ) := by
  obtain ⟨δ, hδ, hsoft⟩ :=
    hF.soft m A.parent_card A.parent A.parent_generic A.vertex A.vector A.admissible
  set ε' : ℝ := min A.param δ / 2 with hε'
  have hmin_pos : 0 < min A.param δ := lt_min A.param_pos hδ
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have hε'δ : ε' < δ := by
    have := min_le_right A.param δ
    rw [hε']; linarith
  have hε'b : ε' < A.bound := by
    have := min_le_left A.param δ
    have := A.param_lt
    rw [hε']; linarith
  obtain ⟨B, hB⟩ := A.bound_spec
  obtain ⟨hQ1, -, hc1⟩ := hB A.param A.param_pos A.param_lt
  obtain ⟨hQ2, -, hc2⟩ := hB ε' hε'pos hε'b
  have hm1 : 3 ≤ m + 1 := by have := A.parent_card; omega
  have h1 : F (m + 1) (polygonProjection ⟨softInsertion A.parent A.vertex A.vector A.param, hQ1⟩) =
      F (m + 1) (polygonProjection B) := hF.chamber (m + 1) hm1 _ _ hc1
  have h2 : F (m + 1) (polygonProjection ⟨softInsertion A.parent A.vertex A.vector ε', hQ2⟩) =
      F (m + 1) (polygonProjection B) := hF.chamber (m + 1) hm1 _ _ hc2
  have h3 := hsoft ε' hε'pos hε'δ hQ2
  have hpoly : (⟨A.polygon, A.polygon_generic⟩ : GenericTuple (m + 1)) =
      ⟨softInsertion A.parent A.vertex A.vector A.param, hQ1⟩ := rfl
  rw [hpoly, h1, ← h2, h3]

/-- At a zero anchor the value is `0` (mixed sector). -/
theorem unB_value_zeroAnchor (hF : UniquenessHypotheses F) {m : ℕ} [NeZero m] {r : ℤ}
    (A : ZeroAnchor m r) :
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) = 0 :=
  softAmplitude_integer_mixed A.parent A.vertex A.vector A.admissible A.mixed _ _
    (unB_soft_anchor_value hF A.toSoftAnchorData)

/-- At a loop anchor the value is `τ_j(P) · F(P)` (loop sector). -/
theorem unB_value_loopAnchor (hF : UniquenessHypotheses F) {m : ℕ} [NeZero m]
    (A : SoftAnchorData m)
    (hloop : softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
      softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex) :
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) =
      (turn A.parent A.vertex : ℤ) * F m (polygonProjection ⟨A.parent, A.parent_generic⟩) :=
  softAmplitude_integer_loop A.parent A.vertex A.vector hloop _ _ (unB_soft_anchor_value hF A)

theorem unB_delta_zeroAnchor (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {m : ℕ} [NeZero m] {r : ℤ} (A : ZeroAnchor m r) : unB_delta F G A.polygon = 0 := by
  rw [unB_delta_of_generic F G A.polygon_generic, unB_value_zeroAnchor hF A,
    unB_value_zeroAnchor hG A, sub_zero]

theorem unB_delta_loopAnchor (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {m : ℕ} [NeZero m] (IH : unB_AgreeBelow F G (m + 1)) (A : SoftAnchorData m)
    (hloop : softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
      softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex) :
    unB_delta F G A.polygon = 0 := by
  rw [unB_delta_of_generic F G A.polygon_generic, unB_value_loopAnchor hF A hloop,
    unB_value_loopAnchor hG A hloop, IH m (by omega) A.parent_card A.parent A.parent_generic,
    sub_self]

/-- `Δ = 0` at every anchor, given `F = G` below the anchor's arity. -/
theorem unB_delta_anchor (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {m : ℕ} [NeZero m] {r : ℤ} (IH : unB_AgreeBelow F G (m + 1)) (A : Anchor m r) :
    unB_delta F G A.polygon = 0 := by
  cases A with
  | zero hZ A₀ => exact unB_delta_zeroAnchor hF hG A₀
  | loop hL hr A₀ => exact unB_delta_loopAnchor hF hG IH A₀.toSoftAnchorData A₀.loop
  | loopZero hL₀ A₀ => exact unB_delta_loopAnchor hF hG IH A₀.toSoftAnchorData A₀.loop

/-! #### The base `n = 3`: transport to `K_1` or `K_{-1}` -/

theorem unB_delta_triangle (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G)
    {P : LabelledTuple 3} (hP : Generic P) : unB_delta F G P = 0 := by
  have hreg := generic_regular le_rfl hP
  obtain ⟨-, hrot, -⟩ := rotationNumber_triangle hreg
  have hIH : unB_AgreeBelow F G 3 := fun k hk _ hk3 Q hQ => absurd hk3 (by omega)
  have hne : ∀ r : ℤ, (((2 + 1 : ℕ) : ℤ), r) ≠ (4, 0) := by
    intro r h
    have := congrArg Prod.fst h
    norm_num at this
  rcases hrot with h1 | h1
  · have hZ : Generic (star 1) := (star_generic_law le_rfl).1.2.2.2.1
    have hrZ : rotationNumber (star 1) = ((1 : ℤ) : ℝ) := by
      rw [(star_generic_law le_rfl).1.2.1.2.2.2.2]; simp
    have hrP : rotationNumber P = ((1 : ℤ) : ℝ) := by rw [h1]; simp
    obtain ⟨k, hk, hΔ⟩ :=
      unB_delta_eq_target_of_transport (m := 2) hF hG (by norm_num) hIH hP hZ hrP hrZ
    rw [hΔ, hk (hne 1), shift_zero, unB_delta_of_generic F G hZ, hF.triangles.1, hG.triangles.1]
    simp
  · have hZ : Generic (starNeg 1) := (star_generic_law le_rfl).1.2.2.2.2.1
    have hrZ : rotationNumber (starNeg 1) = ((-1 : ℤ) : ℝ) := by
      rw [(star_generic_law le_rfl).1.2.2.2.2.2.2]; simp
    have hrP : rotationNumber P = ((-1 : ℤ) : ℝ) := by rw [h1]; simp
    obtain ⟨k, hk, hΔ⟩ :=
      unB_delta_eq_target_of_transport (m := 2) hF hG (by norm_num) hIH hP hZ hrP hrZ
    rw [hΔ, hk (hne (-1)), shift_zero, unB_delta_of_generic F G hZ, hF.triangles.2,
      hG.triangles.2]
    simp

/-! #### The strong induction -/

/-- `F = G` on every generic polygon of arity `n`. -/
abbrev unB_AgreeAt (F G : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (n : ℕ) : Prop :=
  ∀ [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    F n (polygonProjection ⟨P, hP⟩) = G n (polygonProjection ⟨P, hP⟩)

/-- Any two functions satisfying (a)–(f) agree on every generic polygon of every arity. -/
theorem unB_agree_all (hF : UniquenessHypotheses F) (hG : UniquenessHypotheses G) :
    ∀ n : ℕ, unB_AgreeAt F G n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro _ hn P hP
  have hIH : unB_AgreeBelow F G n := fun k hk _ hk3 Q hQ => IH k hk hk3 Q hQ
  suffices hΔ : unB_delta F G P = 0 by
    rw [unB_delta_of_generic F G hP] at hΔ
    exact sub_eq_zero.mp hΔ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases h3 : m + 1 = 3
  · have hm : m = 2 := by omega
    subst hm
    exact unB_delta_triangle hF hG hP
  · have hm : 3 ≤ m := by omega
    have : NeZero m := ⟨by omega⟩
    obtain ⟨r, hr⟩ := rotationNumber_integer (generic_regular hn hP)
    have hadm : Admissible ((m + 1 : ℕ) : ℤ) r := generic_rotation_admissible hn hP r hr
    have hadm' : Admissible ((m : ℤ) + 1) r := by
      have h : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rwa [h] at hadm
    obtain ⟨A⟩ := anchor_exists r hadm' (by omega)
    have hZ := A.polygon_generic
    have hrZ := A.polygon_rotation
    obtain ⟨k, -, hΔ⟩ := unB_delta_eq_target_of_transport hF hG hn hIH hP hZ hr hrZ
    rw [hΔ, unB_delta_shift k hZ]
    exact unB_delta_anchor hF hG hIH A

end Transport

/-- thm:uniqueness as printed on SM15: a function `F` on generic polygons of every arity `n ≥ 3`
satisfying (a)–(f) equals `A` on every generic polygon. -/
theorem uniqueness (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : UniquenessHypotheses F) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      F n (polygonProjection ⟨P, hP⟩) = amplitude P hP.1 hn := by
  intro n _ hn P hP
  rw [unB_agree_all hF unB_A_hypotheses n hn P hP, unB_Apoly_projection hn]

end SM

#print axioms SM.uniqueness
