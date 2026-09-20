-- Ported 18:08Z 2026-09-15 from work/drafts/cvtail/Wave1_Assembled.lean lines 702-1763 (CV/R tail lane, row 165 CV:singleton_D_i: §2 = SingletonPieceOn, SingletonDiData, cvt_omega1_eq_zero_of_gap, SingletonDiData.of_degree_gap, SingletonSplitData, singleton_D_i_of, U-SPLIT's cvt165s_ helpers (sections Cvt165sPattern, Cvt165s with its nine sub-sections, kept exactly), the leaf cvt_singleton_split and the row) by the pod executor; body verbatim except this header, the import block (CV.PieceHomflyTransport and SM.ZeroRotationSeed supply homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq and principalAngle_swap, imported in Wave1 through CV.ChamberInvRow and the §5 SM imports), and the namespace/section opening lines (Wave1 241-247) and closing `end` / `end CV` (1765/1767) repeated around the §2 block. Row 165: `CV.singleton_D_i : CV.SingletonDiData := singleton_D_i_of cvt_singleton_split (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC)`.
import CV.CarrierFloor
import CV.PieceHomflyTransport
import SM.ZeroRotationSeed

namespace CV

open SM SM.Link SM.Carrier SM.GeoCarrier
open scoped ContDiff

noncomputable section
open Classical

/-! ## 2. Row 165 CV:singleton_D_i — thm:s7universal (D)(i) (d6_vertexedge.tex:2682-2687)

"(i) Let S ∈ Ind(G_P), let A be a uniform carrier of S, and let {c} be a singleton residual piece of S
carried by A. Then min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2, so the factor Ω₁(S,A) of Definition def:X1
is zero."  `f_A = [z^0] P_{S,A}` (def:markeddata), `P_{S,A} = groupedPoly`, `1 − w_{S,A} − R(A) = slot`,
`Ω₁(S,A) = Omega1` (CV:def:X1); "uniform carrier" = CV:def:wind's `CarrierUniform`; the degree bound in
support form (every `a^d z^0` present has `d ≥ slot + 2`; vacuous when `f_A = 0`, FR-CV-165-1). -/

/-- "`{c}` a singleton residual piece of `S` carried by `A`": `c ∈ U(S)`, its piece has label set `{c}`,
and that piece is assigned to `q` (def:X1 / lem:carriers (iv)) — exactly the shape produced by the
accepted `ExtremePairZeroData.third_singleton_piece` (FR-CV-165-2). -/
structure SingletonPieceOn {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (c : Crossing P) : Prop where
  mem_U : c ∈ U hP S
  labels : pieceLabels hP S (pieceOf hP S c mem_U) = {c}
  owner : pieceOf hP S c mem_U ∈ piecesOn hP S q

/-- **Row 165** (proposed row declaration `CV.singleton_D_i : SingletonDiData`), the two printed clauses. -/
structure SingletonDiData : Prop where
  /-- "min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2" -/
  degree_gap : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c →
      ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d
  /-- "so the factor Ω₁(S,A) of Definition def:X1 is zero" -/
  factor_zero : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c → Omega1 hn hG hS q = 0

/-- The printed "so": the coefficient at the slot lies two degrees below the lowest present degree. PROVED. -/
theorem cvt_omega1_eq_zero_of_gap {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hgap : ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d) :
    Omega1 hn hG hS q = 0 := by
  by_contra hne
  have := hgap (slot hn hG hS q) hne
  omega

/-- The bundle from its first clause. PROVED. -/
theorem SingletonDiData.of_degree_gap
    (hgap : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
      {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
      CarrierUniform hG.crossingGeometry S q →
      ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c →
        ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d) :
    SingletonDiData where
  degree_gap := hgap
  factor_zero := by
    intro n _ hn P hG S hS q hq c hc
    exact cvt_omega1_eq_zero_of_gap hn hG hS q (hgap hn hG hS q hq c hc)

/-- The split interface (unit U-SPLIT of THIS lane, on the geo layer — the corner lane's cb:singleton
split `sg_daughters_*` lives on SM's `Component`/`IsDecomposition`, so it cannot be consumed here,
FR-CV-165-3): smoothing `c` splits the uniform carrier `A` of `S` into two carriers `Λ₁, Λ₂` of
`S' = S ∪ {c}` with `P_{S,A} = P_{S',Λ₁} P_{S',Λ₂}` (the pieces "literally the same objects" +
`P_{{c}} = 1`), `w_{S,A} = w_{S',Λ₁} + w_{S',Λ₂} + 1`, `R(A) = R(Λ₁) + R(Λ₂)` (turnlift (ii) +
uniformrot signs), one loop uniform and the other one-dissent (d6:2890-2935). -/
def SingletonSplitData : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c →
      ∃ hS' : insert c S ∈ Ind hG.crossingGeometry,
      ∃ q₁ q₂ : GeoComponent hG.crossingGeometry (insert c S),
        groupedPoly hn hG hS q = groupedPoly hn hG hS' q₁ * groupedPoly hn hG hS' q₂ ∧
        groupedWrithe hG q = groupedWrithe hG q₁ + groupedWrithe hG q₂ + 1 ∧
        (carrierR hn hG hS q : ℤ) = carrierR hn hG hS' q₁ + carrierR hn hG hS' q₂ ∧
        UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry (insert c S) q₁) ∧
        UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry (insert c S) q₂)

/-- **Row 165 from the split and the carrier floor** (the printed proof d6:2890-2947; the two floors add
through `mindegAZ_mul` on the nonzero factors — the corner lane's FR-CC-3 route, FR-CV-165-4). PROVED. -/
theorem singleton_D_i_of (hsplit : SingletonSplitData) (hfloor : CarrierSlotFloor) : SingletonDiData := by
  refine SingletonDiData.of_degree_gap ?_
  intro n _ hn P hG S hS q hq c hc d hd
  · obtain ⟨hS', q₁, q₂, hpoly, hwrithe, hrot, halt₁, halt₂⟩ := hsplit hn hG hS q hq c hc
    have h₁ := hfloor hn hG hS' q₁ halt₁
    have h₂ := hfloor hn hG hS' q₂ halt₂
    have hne₁ := cvt_groupedPoly_ne_zero hn hG hS' q₁
    have hne₂ := cvt_groupedPoly_ne_zero hn hG hS' q₂
    rw [hpoly] at hd
    have hle := (mindegAZ_spec (mul_ne_zero hne₁ hne₂)).2 d 0 hd
    rw [mindegAZ_mul hne₁ hne₂] at hle
    unfold slot at h₁ h₂ ⊢
    rw [hwrithe, hrot]
    omega

/-! ### U-SPLIT helpers (prefix `cvt165s_`): the singleton split on the geo layer.

Route (PLAN_FINAL §4, U-SPLIT (a)–(e); template: the corner lane's U103-B/E units on SM's `Component`,
ported here to `GeoComponent`/`piecesOn`/`groupedPoly`):
(a) `insert c S ∈ Ind` (`geoIndependent_insert_unselected`), `U(insert c S) = U(S) ∖ {c}` membership-wise, and
    `Piece (insert c S) ≃ {H : Piece S // pieceLabels H ≠ {c}}` label-preserving (Mathlib `induceHomOfLE`;
    `c` is isolated in `G_P[U(S)]` because its piece is `{c}`);
(b) the carrier split: `Λ₁ = geoOwner (insert c S) (inr v)`, `Λ₂ = geoOwner (insert c S) (inr (visitTwin v))` for a
    visit `v` of `c` (`geoComponentForgetSwitch_fiber_affected`, `geoOwner_insert_eq_imp`,
    `geo_selected_visits_separated`);
(c) `piecesOn S A = insert (pieceOf c) ((piecesOn S' Λ₁ ∪ piecesOn S' Λ₂).map emb)`; `pieceHomfly` is a function
    of the labels (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`, lem:pieceintrinsic) and
    `pieceHomfly (pieceOf c) = 1` (lc:single-crossing), `pieceWrithe (pieceOf c) = 1`;
(d) rotation: the real principal turn of a corner is a function of its corner MARK
    (`geoCornerPolygon_edge_smul/_edge_pred_smul` + `principalAngle_smul`), `2π rot = Σ` over the corner-mark
    finset, inherited corners keep their turn, the two smoothing corners cancel (`principalAngle_swap`); the
    signs put all three integers on one ray (lem:uniformrot);
(e) the sign pattern of each daughter (uniform with `A`'s sign or one dissent) gives `UniformOrOneDissentCV`
    in the literal reversal form (`principalTurn_reversal`). -/

/-! (e), polygon side: signed turn patterns, the rays of lem:uniformrot, and the literal reversal form. -/

section Cvt165sPattern

/-- Two nonzero signs agree or are opposite. -/
theorem cvt165s_signType_eq_or_neg {σ τ : SignType} (hσ : σ ≠ 0) (hτ : τ ≠ 0) : σ = τ ∨ σ = -τ := by
  revert hσ hτ
  revert σ τ
  decide

variable {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : Regular L)

include hL in
theorem cvt165s_sign_principalTurn (k : ZMod c) : SignType.sign (principalTurn L k) = turn L k := by
  rw [principalTurn_eq_sm]
  exact SM.principalTurn_sign ((regular_iff_sm L).mp hL) k

omit [NeZero c] in
include hL in
theorem cvt165s_principalTurn_reversal (k : ZMod c) :
    principalTurn (reversal L) k = -principalTurn L (2 - k) := by
  rw [principalTurn_eq_sm, principalTurn_eq_sm]
  exact SM.principalTurn_reversal ((regular_iff_sm L).mp hL) k

include hL in
/-- lem:uniformrot read at a signed pattern: a regular polygon that is uniform of sign `τ` or has exactly
one dissent `−τ` has its rotation on the ray of `τ` (`one_le_rot_of_pos`, `one_le_rot_of_one_dissent`,
and their reversal forms). -/
theorem cvt165s_rot_ray (τ : SignType)
    (h : (∀ k, turn L k = τ) ∨ (∃ k₀, turn L k₀ = -τ ∧ ∀ k, k ≠ k₀ → turn L k = τ)) :
    (τ = 1 → 1 ≤ rot L hL) ∧ (τ = -1 → rot L hL ≤ -1) := by
  have hsign := cvt165s_sign_principalTurn L hL
  constructor
  · rintro rfl
    rcases h with h | ⟨k₀, -, hoth⟩
    · exact one_le_rot_of_pos hL fun k => sign_eq_one_iff.mp ((hsign k).trans (h k))
    · exact one_le_rot_of_one_dissent hL k₀ fun k hk =>
        (sign_eq_one_iff.mp ((hsign k).trans (hoth k hk))).le
  · rintro rfl
    have hrev : Regular (reversal L) := regular_reversal' hL
    have hrevturn := cvt165s_principalTurn_reversal L hL
    have key : 1 ≤ rot (reversal L) hrev := by
      rcases h with h | ⟨k₀, -, hoth⟩
      · refine one_le_rot_of_pos hrev fun k => ?_
        rw [hrevturn]
        have := sign_eq_neg_one_iff.mp ((hsign (2 - k)).trans (h (2 - k)))
        linarith
      · refine one_le_rot_of_one_dissent hrev (2 - k₀) fun k hk => ?_
        rw [hrevturn]
        have hne : 2 - k ≠ k₀ := fun he => hk (by rw [← he, sub_sub_cancel])
        have := sign_eq_neg_one_iff.mp ((hsign (2 - k)).trans (hoth (2 - k) hne))
        linarith
    rw [rot_reversal hL hrev] at key
    omega

include hL in
/-- (e) A signed pattern gives the literal reversal form `UniformOrOneDissentCV`. -/
theorem cvt165s_uniformOrOneDissent_of_pattern (τ : SignType) (hτ0 : τ ≠ 0)
    (h : (∀ k, turn L k = τ) ∨ (∃ k₀, turn L k₀ = -τ ∧ ∀ k, k ≠ k₀ → turn L k = τ)) :
    UniformOrOneDissentCV L := by
  have hsign := cvt165s_sign_principalTurn L hL
  have hrevturn := cvt165s_principalTurn_reversal L hL
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · right
    rcases h with h | ⟨k₀, hk₀, hoth⟩
    · left
      intro k
      rw [hrevturn]
      have := sign_eq_neg_one_iff.mp ((hsign (2 - k)).trans (h (2 - k)))
      linarith
    · right
      refine ⟨2 - k₀, ?_, fun j hj => ?_⟩
      · rw [hrevturn, sub_sub_cancel]
        have h1 : turn L k₀ = 1 := by
          rw [hk₀]
          decide
        have := sign_eq_one_iff.mp ((hsign k₀).trans h1)
        linarith
      · rw [hrevturn]
        have hne : 2 - j ≠ k₀ := fun he => hj (by rw [← he, sub_sub_cancel])
        have := sign_eq_neg_one_iff.mp ((hsign (2 - j)).trans (hoth (2 - j) hne))
        linarith
  · exact absurd rfl hτ0
  · left
    rcases h with h | ⟨k₀, hk₀, hoth⟩
    · left
      exact fun k => sign_eq_one_iff.mp ((hsign k).trans (h k))
    · right
      exact ⟨k₀, sign_eq_neg_one_iff.mp ((hsign k₀).trans hk₀),
        fun j hj => sign_eq_one_iff.mp ((hsign j).trans (hoth j hj))⟩


/-- Two integers on one ray have additive absolute values (the `ω`-free arithmetic of (d), kept outside the
classical-instance region so that `omega` may be used). -/
theorem cvt165s_abs_add_of_ray (a b : ℤ) :
    (a ≤ -1 → b ≤ -1 → |a + b| = |a| + |b|) ∧ (1 ≤ a → 1 ≤ b → |a + b| = |a| + |b|) := by
  constructor
  · intro ha hb
    rw [abs_of_neg (by omega), abs_of_neg (by omega), abs_of_neg (by omega)]
    ring
  · intro ha hb
    rw [abs_of_pos (by omega), abs_of_pos (by omega), abs_of_pos (by omega)]

end Cvt165sPattern

section Cvt165s

/- The library states everything about `insert`, `∪`, `filter` on `Crossing P` with the classical
`DecidableEq` (every CV/SM module has `attribute [local instance high] Classical.propDecidable`); the frozen
statements of this file elaborate `insert c S` with the global `RProof.instDecidableEqCrossing`. The helpers
below follow the library; the leaf bridges the two through `cvt165s_insert_eq` (a `Subsingleton` fact). -/
attribute [local instance high] Classical.propDecidable

/-- `insert` does not depend on the `DecidableEq` instance (bridge between the frozen statement's instance
and the library's classical one). -/
theorem cvt165s_insert_eq {α : Type*} [inst : DecidableEq α] (a : α) (s : Finset α) :
    @insert α (Finset α) (@Finset.instInsert α inst) a s =
      @insert α (Finset α) (@Finset.instInsert α fun x y => Classical.propDecidable (x = y)) a s :=
  congrArg (fun i : DecidableEq α => @insert α (Finset α) (@Finset.instInsert α i) a s)
    (Subsingleton.elim _ _)

section Cvt165sGraph

variable {V : Type*} (G : SimpleGraph V) {s t : Set V} {c : V}

/-- An isolated vertex of `G[s]` reaches no other vertex of `G[s]`. -/
theorem cvt165s_not_reachable_of_isolated (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    {z : s} (hz : z.1 ≠ c) : ¬ (G.induce s).Reachable ⟨c, hcs⟩ z := by
  rintro ⟨p⟩
  cases p with
  | nil => exact hz rfl
  | cons h _ => exact hc _ (Subtype.mem _) h.symm

/-- A walk of `G[s]` between vertices other than the isolated `c` never visits `c`: reachability descends
to `G[t]`, `t = s ∖ {c}` (given membership-wise). -/
theorem cvt165s_reachable_descend (hc : ∀ x ∈ s, ¬ G.Adj x c) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c)
    {x y : s} (hx : x.1 ≠ c) (hy : y.1 ≠ c) (h : (G.induce s).Reachable x y) :
    (G.induce t).Reachable ⟨x.1, (ht _).mpr ⟨x.2, hx⟩⟩ ⟨y.1, (ht _).mpr ⟨y.2, hy⟩⟩ := by
  obtain ⟨p⟩ := h
  revert hx hy
  induction p with
  | nil => intro _ _; exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih =>
    intro hu hw
    have hv : v.1 ≠ c := by
      intro hvc
      have h' : G.Adj u.1 v.1 := huv
      rw [hvc] at h'
      exact hc _ u.2 h'
    exact (SimpleGraph.Adj.reachable
      (show (G.induce t).Adj ⟨u.1, (ht _).mpr ⟨u.2, hu⟩⟩ ⟨v.1, (ht _).mpr ⟨v.2, hv⟩⟩ from huv)).trans
      (ih hv hw)

/-- The inclusion `G[t] ↪ G[s]` on connected components. -/
def cvt165s_compMap (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    (G.induce t).ConnectedComponent → (G.induce s).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (G.induceHomOfLE fun x hx => ((ht x).mp hx).1).toHom

theorem cvt165s_compMap_mk (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (x : t) :
    cvt165s_compMap G ht ((G.induce t).connectedComponentMk x) =
      (G.induce s).connectedComponentMk ⟨x.1, ((ht x).mp x.2).1⟩ := rfl

theorem cvt165s_compMap_injective (hc : ∀ x ∈ s, ¬ G.Adj x c) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    Function.Injective (cvt165s_compMap G ht) := by
  intro C D
  refine SimpleGraph.ConnectedComponent.ind₂ (fun x y h => ?_) C D
  rw [cvt165s_compMap_mk, cvt165s_compMap_mk, SimpleGraph.ConnectedComponent.eq] at h
  exact SimpleGraph.ConnectedComponent.sound
    (cvt165s_reachable_descend G hc ht ((ht _).mp x.2).2 ((ht _).mp y.2).2 h)

theorem cvt165s_mem_range_compMap_iff (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (C : (G.induce s).ConnectedComponent) :
    C ∈ Set.range (cvt165s_compMap G ht) ↔ C ≠ (G.induce s).connectedComponentMk ⟨c, hcs⟩ := by
  refine SimpleGraph.ConnectedComponent.ind (fun x => ?_) C
  constructor
  · rintro ⟨D, hD⟩ hx
    refine SimpleGraph.ConnectedComponent.ind (fun z hD => ?_) D hD
    rw [cvt165s_compMap_mk, hx, SimpleGraph.ConnectedComponent.eq] at hD
    exact cvt165s_not_reachable_of_isolated G hc hcs ((ht _).mp z.2).2 hD.symm
  · intro hx
    have hxc : x.1 ≠ c := fun h => hx (congrArg _ (Subtype.ext h))
    exact ⟨(G.induce t).connectedComponentMk ⟨x.1, (ht _).mpr ⟨x.2, hxc⟩⟩, rfl⟩

/-- **The components of `G[s ∖ {c}]` are the components of `G[s]` other than that of the isolated `c`.** -/
def cvt165s_compEquiv (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    (G.induce t).ConnectedComponent ≃
      {C : (G.induce s).ConnectedComponent // C ≠ (G.induce s).connectedComponentMk ⟨c, hcs⟩} :=
  (Equiv.ofInjective _ (cvt165s_compMap_injective G hc ht)).trans
    (Equiv.subtypeEquivRight (cvt165s_mem_range_compMap_iff G hc hcs ht))

theorem cvt165s_compEquiv_apply_val (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (D : (G.induce t).ConnectedComponent) :
    (cvt165s_compEquiv G hc hcs ht D).1 = cvt165s_compMap G ht D := rfl

/-- Vertex by vertex: `x` lies in the component `e D` of `G[s]` iff it lies in `D`. -/
theorem cvt165s_compEquiv_mem_iff (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (D : (G.induce t).ConnectedComponent) (x : V) :
    (∃ hx : x ∈ s, (G.induce s).connectedComponentMk ⟨x, hx⟩ = (cvt165s_compEquiv G hc hcs ht D).1) ↔
      ∃ hx : x ∈ t, (G.induce t).connectedComponentMk ⟨x, hx⟩ = D := by
  refine SimpleGraph.ConnectedComponent.ind (fun z => ?_) D
  rw [cvt165s_compEquiv_apply_val, cvt165s_compMap_mk]
  constructor
  · rintro ⟨hx, h⟩
    rw [SimpleGraph.ConnectedComponent.eq] at h
    have hxc : x ≠ c := by
      intro hxc
      have hxe : (⟨x, hx⟩ : s) = ⟨c, hcs⟩ := Subtype.ext hxc
      rw [hxe] at h
      exact cvt165s_not_reachable_of_isolated G hc hcs ((ht _).mp z.2).2 h
    exact ⟨(ht x).mpr ⟨hx, hxc⟩, SimpleGraph.ConnectedComponent.sound
      (cvt165s_reachable_descend G hc ht hxc ((ht _).mp z.2).2 h)⟩
  · rintro ⟨hx, h⟩
    refine ⟨((ht x).mp hx).1, ?_⟩
    have := congrArg (cvt165s_compMap G ht) h
    rw [cvt165s_compMap_mk, cvt165s_compMap_mk] at this
    exact this

end Cvt165sGraph

/-! (a) The pieces of `insert c S` when the piece of `c` is `{c}`: `c` is isolated in `G_P[U(S)]`, and
`U(insert c S) = U(S) ∖ {c}`. -/

section Cvt165sPieces

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)}
  {c : Crossing P}

/-- The piece of `c` is `{c}` ⇒ no undominated crossing interlaces `c` (an interlacing undominated
crossing would lie in the piece of `c`). -/
theorem cvt165s_not_interlaces (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) :
    ∀ x ∈ U hP S, ¬ GeometricInterlaces hP x c := by
  intro x hx hI
  have hadj : (residualGraph hP S).Adj ⟨x, hx⟩ ⟨c, hcU⟩ := hI
  have hH : pieceOf hP S x hx = pieceOf hP S c hcU :=
    SimpleGraph.ConnectedComponent.sound hadj.reachable
  have hxc : x ∈ pieceLabels hP S (pieceOf hP S c hcU) := (mem_pieceLabels hP S _ x).mpr ⟨hx, hH⟩
  rw [hlab, Finset.mem_singleton] at hxc
  subst hxc
  exact geometricInterlaces_irrefl hP x hI

/-- `U(insert c S) = U(S) ∖ {c}`, membership-wise. -/
theorem cvt165s_mem_U_insert_iff (hiso : ∀ x ∈ U hP S, ¬ GeometricInterlaces hP x c) (x : Crossing P) :
    x ∈ U hP (insert c S) ↔ x ∈ U hP S ∧ x ≠ c := by
  rw [mem_U_iff, mem_U_iff]
  constructor
  · rintro ⟨hxS', hxI⟩
    refine ⟨⟨fun h => hxS' (Finset.mem_insert_of_mem h), fun y hy => hxI y (Finset.mem_insert_of_mem hy)⟩,
      fun hxc => hxS' (hxc ▸ Finset.mem_insert_self c S)⟩
  · rintro ⟨⟨hxS, hxI⟩, hxc⟩
    refine ⟨fun h => ?_, fun y hy => ?_⟩
    · rcases Finset.mem_insert.mp h with h | h
      · exact hxc h
      · exact hxS h
    · rcases Finset.mem_insert.mp hy with h | hy
      · rw [h]
        exact hiso x ((mem_U_iff hP S x).mpr ⟨hxS, hxI⟩)
      · exact hxI y hy

theorem cvt165s_mem_U_set (hcU : c ∈ U hP S) : c ∈ (↑(U hP S) : Set (Crossing P)) :=
  Finset.mem_coe.mpr hcU

theorem cvt165s_mem_U_insert_iff_set (hiso : ∀ x ∈ U hP S, ¬ GeometricInterlaces hP x c) (x : Crossing P) :
    x ∈ (↑(U hP (insert c S)) : Set (Crossing P)) ↔ x ∈ (↑(U hP S) : Set (Crossing P)) ∧ x ≠ c := by
  rw [Finset.mem_coe, Finset.mem_coe]
  exact cvt165s_mem_U_insert_iff hP hiso x

theorem cvt165s_adj_isolated (hiso : ∀ x ∈ U hP S, ¬ GeometricInterlaces hP x c) :
    ∀ x ∈ (↑(U hP S) : Set (Crossing P)), ¬ (geometricInterlacementGraph hP).Adj x c :=
  fun x hx => hiso x (Finset.mem_coe.mp hx)

/-- A piece has the labels `{c}` iff it is the piece of `c`. -/
theorem cvt165s_pieceLabels_eq_singleton_iff (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H : Piece hP S) :
    pieceLabels hP S H = {c} ↔ H = pieceOf hP S c hcU := by
  constructor
  · intro h
    have hcH : c ∈ pieceLabels hP S H := by
      rw [h]
      exact Finset.mem_singleton_self c
    obtain ⟨_, hH⟩ := (mem_pieceLabels hP S H c).mp hcH
    exact hH.symm
  · rintro rfl
    exact hlab

/-- **`Piece (insert c S) ≃ {H : Piece S // pieceLabels H ≠ {c}}`**, label-preserving
(`cvt165s_pieceEquiv_labels`). -/
def cvt165s_pieceEquiv (hcU : c ∈ U hP S) (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) :
    Piece hP (insert c S) ≃ {H : Piece hP S // pieceLabels hP S H ≠ {c}} :=
  (cvt165s_compEquiv (geometricInterlacementGraph hP)
      (cvt165s_adj_isolated hP (cvt165s_not_interlaces hP hcU hlab)) (cvt165s_mem_U_set hP hcU)
      (cvt165s_mem_U_insert_iff_set hP (cvt165s_not_interlaces hP hcU hlab))).trans
    (Equiv.subtypeEquivRight fun H =>
      (not_congr (cvt165s_pieceLabels_eq_singleton_iff hP hcU hlab H)).symm)

/-- **Label-preserving**: the labels of `e H'` (as a piece of `S`) are the labels of `H'` (as a piece of
`insert c S`). -/
theorem cvt165s_pieceEquiv_labels (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H' : Piece hP (insert c S)) :
    pieceLabels hP S (cvt165s_pieceEquiv hP hcU hlab H').1 = pieceLabels hP (insert c S) H' := by
  ext x
  rw [mem_pieceLabels, mem_pieceLabels]
  exact cvt165s_compEquiv_mem_iff (geometricInterlacementGraph hP)
    (cvt165s_adj_isolated hP (cvt165s_not_interlaces hP hcU hlab)) (cvt165s_mem_U_set hP hcU)
    (cvt165s_mem_U_insert_iff_set hP (cvt165s_not_interlaces hP hcU hlab)) H' x

/-- The pieces of `insert c S` as pieces of `S`. -/
def cvt165s_pieceEmbedding (hcU : c ∈ U hP S) (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) :
    Piece hP (insert c S) ↪ Piece hP S :=
  (cvt165s_pieceEquiv hP hcU hlab).toEmbedding.trans (Function.Embedding.subtype _)

theorem cvt165s_pieceEmbedding_apply (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H' : Piece hP (insert c S)) :
    cvt165s_pieceEmbedding hP hcU hlab H' = (cvt165s_pieceEquiv hP hcU hlab H').1 := rfl

theorem cvt165s_pieceLabels_pieceEmbedding (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H' : Piece hP (insert c S)) :
    pieceLabels hP S (cvt165s_pieceEmbedding hP hcU hlab H') = pieceLabels hP (insert c S) H' :=
  cvt165s_pieceEquiv_labels hP hcU hlab H'

/-- A piece of `S` is in the range of the embedding iff it is not the piece `{c}`. -/
theorem cvt165s_mem_range_pieceEmbedding_iff (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H : Piece hP S) :
    (∃ H', cvt165s_pieceEmbedding hP hcU hlab H' = H) ↔ pieceLabels hP S H ≠ {c} := by
  constructor
  · rintro ⟨H', rfl⟩
    exact (cvt165s_pieceEquiv hP hcU hlab H').2
  · intro h
    exact ⟨(cvt165s_pieceEquiv hP hcU hlab).symm ⟨H, h⟩, by
      rw [cvt165s_pieceEmbedding_apply, Equiv.apply_symm_apply]⟩

theorem cvt165s_pieceOf_notMem_map (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (T : Finset (Piece hP (insert c S))) :
    pieceOf hP S c hcU ∉ T.map (cvt165s_pieceEmbedding hP hcU hlab) := by
  rw [Finset.mem_map]
  rintro ⟨H', -, hH'⟩
  exact (cvt165s_pieceEquiv hP hcU hlab H').2
    ((cvt165s_pieceLabels_eq_singleton_iff hP hcU hlab _).mpr hH')

/-- `w(H)` is carried by the embedding (the labels are literally the same). -/
theorem cvt165s_pieceWrithe_pieceEmbedding (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H' : Piece hP (insert c S)) :
    pieceWrithe hP S (cvt165s_pieceEmbedding hP hcU hlab H') = pieceWrithe hP (insert c S) H' := by
  unfold pieceWrithe
  rw [cvt165s_pieceLabels_pieceEmbedding]

/-- `w({c}) = 1`. -/
theorem cvt165s_pieceWrithe_singleton (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) :
    pieceWrithe hP S (pieceOf hP S c hcU) = 1 := by
  simp [pieceWrithe, hlab]

end Cvt165sPieces

/-! (b) The carrier split: for a visit `v` of `c`, the two daughters are the carriers of `v` and of
`visitTwin v` at `insert c S`; every mark of `A` lies on exactly one of them and no other mark does. -/

section Cvt165sOwner

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)}
  {q : GeoComponent hP S} {v : Visit P} (hc : SingletonPieceOn hP S q v.1)

include hc in
theorem cvt165s_notMem : v.1 ∉ S := ((mem_U_iff hP S v.1).mp hc.mem_U).1

include hc in
/-- Both visits of `c` lie on `A` (the piece `{c}` is assigned to `A`). -/
theorem cvt165s_owner_visit (w : Visit P) (hw : w.1 = v.1) : geoOwner hP S (Sum.inr w) = q := by
  have h := (mem_piecesOn hP S q _).mp hc.owner
  refine h v.1 ?_ w hw
  rw [hc.labels]
  exact Finset.mem_singleton_self _

include hc in
theorem cvt165s_owner_eq_twin :
    geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr (visitTwin v)) := by
  rw [cvt165s_owner_visit hP hc v rfl, cvt165s_owner_visit hP hc (visitTwin v) (visitTwin_crossing v)]

include hc in
theorem cvt165s_sameCycle :
    (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)) :=
  (geoOwner_eq_iff hP S _ _).mp (cvt165s_owner_eq_twin hP hc)

include hc in
/-- (a) `insert c S ∈ Ind(G_P)`: `c ∈ U(S)` interlaces no element of `S`. -/
theorem cvt165s_geoIndependent_insert (hS : S ∈ Ind hP) : GeoIndependent hP (insert v.1 S) :=
  geoIndependent_insert_unselected hP (geoIndependent_of_mem_Ind hP hS)
    (mem_geoSupportUnselected_of_mem_U hP hc.mem_U)

include hc in
theorem cvt165s_mem_Ind_insert (hS : S ∈ Ind hP) : insert v.1 S ∈ Ind hP :=
  (mem_Ind_iff_geoIndependent hP _).mpr (cvt165s_geoIndependent_insert hP hc hS)

include hc in
/-- The two daughters are distinct (conv:selected-visits separates the two visits of the selected `c`). -/
theorem cvt165s_daughters_ne (hS : S ∈ Ind hP) :
    geoOwner hP (insert v.1 S) (Sum.inr v) ≠ geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)) :=
  geo_selected_visits_separated hP (cvt165s_geoIndependent_insert hP hc hS) v (Finset.mem_insert_self _ _)

include hc in
/-- A mark of a daughter is a mark of `A` (the reconnection refines the carriers). -/
theorem cvt165s_owner_of_insert {m : Mark P}
    (h : geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr v) ∨
      geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v))) :
    geoOwner hP S m = q := by
  rcases h with h | h
  · rw [geoOwner_insert_eq_imp hP S v (cvt165s_notMem hP hc) (cvt165s_sameCycle hP hc) h]
    exact cvt165s_owner_visit hP hc v rfl
  · rw [geoOwner_insert_eq_imp hP S v (cvt165s_notMem hP hc) (cvt165s_sameCycle hP hc) h]
    exact cvt165s_owner_visit hP hc (visitTwin v) (visitTwin_crossing v)

include hc in
/-- A mark of `A` lies on one of the two daughters (the fibre of the forget map over `A` is exactly
the two daughters). -/
theorem cvt165s_owner_insert_of (hS : S ∈ Ind hP) {m : Mark P} (hm : geoOwner hP S m = q) :
    geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr v) ∨
      geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)) := by
  obtain ⟨-, hfib⟩ := geoComponentForgetSwitch_fiber_affected hP S
    (geoInheritsMarkOrder_of_independent hP (geoIndependent_of_mem_Ind hP hS)) v
    (cvt165s_notMem hP hc) (cvt165s_owner_eq_twin hP hc)
  rw [Finset.ext_iff] at hfib
  have hmem := (hfib (geoOwner hP (insert v.1 S) m)).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [geoComponentForgetSwitch_owner, hm, cvt165s_owner_visit hP hc v rfl]⟩)
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

include hc in
/-- **The marks of `A` are exactly the marks of the two daughters.** -/
theorem cvt165s_owner_iff (hS : S ∈ Ind hP) (m : Mark P) :
    geoOwner hP S m = q ↔
      geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr v) ∨
        geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)) :=
  ⟨cvt165s_owner_insert_of hP hc hS, cvt165s_owner_of_insert hP hc⟩

end Cvt165sOwner

/-! (c) The pieces carried by the daughters, and the factorisation of `P_{S,A}` and `w_{S,A}`. -/

section Cvt165sProducts

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)}

/-- Distinct carriers carry disjoint sets of pieces (lem:carriers (iv)). -/
theorem cvt165s_piecesOn_disjoint (hS : S ∈ Ind hP) {q r : GeoComponent hP S} (hqr : q ≠ r) :
    Disjoint (piecesOn hP S q) (piecesOn hP S r) := by
  rw [Finset.disjoint_left]
  intro H h1 h2
  rw [mem_piecesOn_iff hP hS] at h1 h2
  exact hqr (h1.symm.trans h2)

/-- The carrier of a piece is the carrier of any visit of any of its labels. -/
theorem cvt165s_pieceOwner_eq_owner (hS : S ∈ Ind hP) (H : Piece hP S) {x : Crossing P}
    (hx : x ∈ pieceLabels hP S H) (w : Visit P) (hw : w.1 = x) :
    pieceOwner hP hS H = geoOwner hP S (Sum.inr w) :=
  (pieceOwner_spec hP hS H x hx w hw).symm

variable {q : GeoComponent hP S} {v : Visit P} (hc : SingletonPieceOn hP S q v.1)

include hc in
/-- A piece of `insert c S` (read as a piece of `S`) is carried by `A` iff it is carried by one of the
two daughters. -/
theorem cvt165s_mem_piecesOn_pieceEmbedding_iff (hS : S ∈ Ind hP) (H' : Piece hP (insert v.1 S)) :
    cvt165s_pieceEmbedding hP hc.mem_U hc.labels H' ∈ piecesOn hP S q ↔
      H' ∈ piecesOn hP (insert v.1 S) (geoOwner hP (insert v.1 S) (Sum.inr v)) ∨
        H' ∈ piecesOn hP (insert v.1 S) (geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v))) := by
  have hS' := cvt165s_mem_Ind_insert hP hc hS
  obtain ⟨x₀, hx₀⟩ := pieceLabels_nonempty hP (insert v.1 S) H'
  have hx₀' : x₀ ∈ pieceLabels hP S (cvt165s_pieceEmbedding hP hc.mem_U hc.labels H') := by
    rw [cvt165s_pieceLabels_pieceEmbedding]
    exact hx₀
  obtain ⟨j, -, -⟩ := crossing_visits_exist x₀
  rw [mem_piecesOn_iff hP hS, mem_piecesOn_iff hP hS', mem_piecesOn_iff hP hS',
    cvt165s_pieceOwner_eq_owner hP hS _ hx₀' ⟨x₀, j⟩ rfl,
    cvt165s_pieceOwner_eq_owner hP hS' H' hx₀ ⟨x₀, j⟩ rfl]
  exact cvt165s_owner_iff hP hc hS _

include hc in
/-- **The pieces carried by `A` are the piece `{c}` and the pieces carried by the two daughters.** -/
theorem cvt165s_piecesOn_eq (hS : S ∈ Ind hP) :
    piecesOn hP S q =
      insert (pieceOf hP S v.1 hc.mem_U)
        ((piecesOn hP (insert v.1 S) (geoOwner hP (insert v.1 S) (Sum.inr v)) ∪
          piecesOn hP (insert v.1 S) (geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)))).map
            (cvt165s_pieceEmbedding hP hc.mem_U hc.labels)) := by
  ext H
  rw [Finset.mem_insert, Finset.mem_map]
  by_cases h : pieceLabels hP S H = {v.1}
  · have hH : H = pieceOf hP S v.1 hc.mem_U :=
      (cvt165s_pieceLabels_eq_singleton_iff hP hc.mem_U hc.labels H).mp h
    subst hH
    exact ⟨fun _ => Or.inl rfl, fun _ => hc.owner⟩
  · obtain ⟨H', hH'⟩ := (cvt165s_mem_range_pieceEmbedding_iff hP hc.mem_U hc.labels H).mpr h
    subst hH'
    rw [cvt165s_mem_piecesOn_pieceEmbedding_iff hP hc hS H', ← Finset.mem_union]
    constructor
    · intro hT
      exact Or.inr ⟨H', hT, rfl⟩
    · rintro (h1 | ⟨H'', hH'', hE⟩)
      · exact absurd ((cvt165s_pieceLabels_eq_singleton_iff hP hc.mem_U hc.labels _).mpr h1) h
      · rw [(cvt165s_pieceEmbedding hP hc.mem_U hc.labels).injective hE] at hH''
        exact hH''

end Cvt165sProducts

section Cvt165sHomfly

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hD : Diagrammatic P)

/-- **`P_H` is a function of the labels of `H`** (lem:pieceintrinsic through
`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`): two pieces, of `S` and of `S'`, with the same
labels have the same polynomial. -/
theorem cvt165s_pieceHomfly_eq_of_labels {S S' : Finset (Crossing P)} (hS : S ∈ Ind hD.crossingGeometry)
    (hS' : S' ∈ Ind hD.crossingGeometry) (H : Piece hD.crossingGeometry S) (H' : Piece hD.crossingGeometry S')
    (h : pieceLabels hD.crossingGeometry S H = pieceLabels hD.crossingGeometry S' H') :
    pieceHomfly hn hD hS H = pieceHomfly hn hD hS' H' := by
  have hcr : geoCarrierCrossings hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) =
      geoCarrierCrossings hD.crossingGeometry (S' ∪ pieceSupport hD hS' H') (pieceCarrier hD hS' H') := by
    rw [pieceCarrier_geoCarrierCrossings, pieceCarrier_geoCarrierCrossings]
    exact h
  unfold pieceHomfly pieceDiagram
  exact homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn (CarrierGeometry.ofDiagrammatic hD)
    (pieceSupport_geoIndependent hD hS H) (pieceSupport_geoIndependent hD hS' H') _ _ hcr

/-- **`P_{{c}} = 1`** (lc:single-crossing): the piece diagram of a singleton piece is a one-circle
diagram with exactly one crossing. -/
theorem cvt165s_pieceHomfly_singleton {S : Finset (Crossing P)} (hS : S ∈ Ind hD.crossingGeometry)
    {c : Crossing P} (hcU : c ∈ U hD.crossingGeometry S)
    (hlab : pieceLabels hD.crossingGeometry S (pieceOf hD.crossingGeometry S c hcU) = {c}) :
    pieceHomfly hn hD hS (pieceOf hD.crossingGeometry S c hcU) = 1 := by
  unfold pieceHomfly
  rw [← P_eq_homfly]
  have hcc : c ∈ pieceLabels hD.crossingGeometry S (pieceOf hD.crossingGeometry S c hcU) := by
    rw [hlab]
    exact Finset.mem_singleton_self c
  let e := pieceShadowCrossingEquiv hn hD hS (pieceOf hD.crossingGeometry S c hcU)
  refine single_crossing.one_crossing _ (e.symm ⟨c, hcc⟩) (pieceDiagram_componentCount hn hD hS _) ?_
  have hmem : ∀ z : Crossing P,
      z ∈ pieceLabels hD.crossingGeometry S (pieceOf hD.crossingGeometry S c hcU) → z = c := by
    intro z hz
    rw [hlab] at hz
    exact Finset.mem_singleton.mp hz
  intro y
  apply e.injective
  apply Subtype.ext
  rw [Equiv.apply_symm_apply]
  exact hmem _ (e y).2

end Cvt165sHomfly

section Cvt165sSplitAlgebra

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : Generic P) {S : Finset (Crossing P)}
  (hS : S ∈ Ind hG.crossingGeometry) {q : GeoComponent hG.crossingGeometry S} {v : Visit P}
  (hc : SingletonPieceOn hG.crossingGeometry S q v.1)

include hc in
/-- **(c) `P_{S,A} = P_{S',Λ₁} P_{S',Λ₂}`**: the pieces are literally the same objects and `P_{{c}} = 1`. -/
theorem cvt165s_groupedPoly_split :
    groupedPoly hn hG hS q =
      groupedPoly hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v)) *
        groupedPoly hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v))) := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  have hone : pieceHomfly hn (hG.diagrammatic hn) hS (pieceOf hG.crossingGeometry S v.1 hc.mem_U) = 1 :=
    cvt165s_pieceHomfly_singleton hn (hG.diagrammatic hn) hS hc.mem_U hc.labels
  unfold groupedPoly
  rw [cvt165s_piecesOn_eq hG.crossingGeometry hc hS,
    Finset.prod_insert (cvt165s_pieceOf_notMem_map hG.crossingGeometry hc.mem_U hc.labels _),
    Finset.prod_map, hone, one_mul,
    Finset.prod_union (cvt165s_piecesOn_disjoint hG.crossingGeometry hS'
      (cvt165s_daughters_ne hG.crossingGeometry hc hS))]
  congr 1 <;>
    exact Finset.prod_congr rfl fun H' _ =>
      cvt165s_pieceHomfly_eq_of_labels hn (hG.diagrammatic hn) hS hS' _ H'
        (cvt165s_pieceLabels_pieceEmbedding hG.crossingGeometry hc.mem_U hc.labels H')

include hS hc in
/-- **(c) `w_{S,A} = w_{S',Λ₁} + w_{S',Λ₂} + 1`**: the same pieces, and `w({c}) = 1`. -/
theorem cvt165s_groupedWrithe_split :
    groupedWrithe hG q =
      groupedWrithe hG (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v)) +
        groupedWrithe hG (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v))) + 1 := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  unfold groupedWrithe
  rw [cvt165s_piecesOn_eq hG.crossingGeometry hc hS,
    Finset.sum_insert (cvt165s_pieceOf_notMem_map hG.crossingGeometry hc.mem_U hc.labels _),
    Finset.sum_map, cvt165s_pieceWrithe_singleton hG.crossingGeometry hc.mem_U hc.labels,
    Finset.sum_union (cvt165s_piecesOn_disjoint hG.crossingGeometry hS'
      (cvt165s_daughters_ne hG.crossingGeometry hc hS))]
  simp only [cvt165s_pieceWrithe_pieceEmbedding hG.crossingGeometry hc.mem_U hc.labels]
  ring

end Cvt165sSplitAlgebra

/-! (d)–(e) Rotation additivity and the sign patterns: the real principal turn and the turn sign of a corner
are functions of its corner MARK and of the support only. -/

section Cvt165sRot

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)

/-- The real principal turn of a corner mark: the principal angle from the original incoming direction to
the original outgoing direction (lem:carriers (ii)). -/
noncomputable def cvt165s_markPrincipalTurn (S : Finset (Crossing P)) (m : Mark P) : ℝ :=
  principalAngle (edge P (geoInEdge hP m)) (edge P (geoOutSlot hP S m).1)

/-- The turn sign of a corner mark. -/
noncomputable def cvt165s_markTurn (S : Finset (Crossing P)) (m : Mark P) : SignType :=
  SignType.sign (det (edge P (geoInEdge hP m)) (edge P (geoOutSlot hP S m).1))

/-- The principal turn of the corner polygon at its `k`-th corner is the mark principal turn of that corner
(both corner edges are positive multiples of the original directions). -/
theorem cvt165s_principalTurn_eq_mark (hn : 3 ≤ n) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    principalTurn (geoCornerPolygon hP S q) k = cvt165s_markPrincipalTurn hP S (geoCornerMark hP S q k) := by
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred_smul hn hP hS q k
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge_smul hn hP hS q k
  unfold principalTurn cvt165s_markPrincipalTurn
  rw [he₁, he₂, principalAngle_smul hc₁ hc₂]

theorem cvt165s_turn_eq_mark (hn : 3 ≤ n) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k = cvt165s_markTurn hP S (geoCornerMark hP S q k) :=
  geoCornerPolygon_turn_eq_sign_of_independent hn hP hS q k

/-- The corner marks of the carrier `q` at `S` as a finset: the true corners of `S` owned by `q`. -/
noncomputable def cvt165s_cornerSet (S : Finset (Crossing P)) (q : GeoComponent hP S) : Finset (Mark P) :=
  Finset.univ.filter fun m => geoOwner hP S m = q ∧ IsTrueCorner S m

theorem cvt165s_mem_cornerSet (S : Finset (Crossing P)) (q : GeoComponent hP S) (m : Mark P) :
    m ∈ cvt165s_cornerSet hP S q ↔ geoOwner hP S m = q ∧ IsTrueCorner S m := by
  simp only [cvt165s_cornerSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `geoCornerMark` enumerates the corner set exactly once. -/
theorem cvt165s_image_cornerMark (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    Finset.univ.image (geoCornerMark hP S q) = cvt165s_cornerSet hP S q := by
  ext m
  rw [Finset.mem_image, cvt165s_mem_cornerSet]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact geoCornerMark_mem hP S q k
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q m h1 h2
    exact ⟨k, Finset.mem_univ _, hk⟩

/-- A sum over the corners of `q` is a sum over its corner-mark finset. -/
theorem cvt165s_sum_corners (S : Finset (Crossing P)) (q : GeoComponent hP S) (f : Mark P → ℝ) :
    ∑ k, f (geoCornerMark hP S q k) = ∑ m ∈ cvt165s_cornerSet hP S q, f m := by
  rw [← cvt165s_image_cornerMark, Finset.sum_image]
  intro i _ j _ hij
  exact geoCornerMark_injective hP S q hij

/-- **Inherited corners keep their principal turn** under `S → insert c S`: the incoming edge is
support-free and the outgoing slot of a true corner of `S` is unchanged. -/
theorem cvt165s_markPrincipalTurn_insert (S : Finset (Crossing P)) (c : Crossing P) (m : Mark P)
    (hm : IsTrueCorner S m) :
    cvt165s_markPrincipalTurn hP (insert c S) m = cvt165s_markPrincipalTurn hP S m := by
  unfold cvt165s_markPrincipalTurn
  cases m with
  | inl i => rw [geoOutSlot_vertex, geoOutSlot_vertex]
  | inr w =>
    have hw : w.1 ∈ S := hm
    rw [geoOutSlot_selected hP S w hw, geoOutSlot_selected hP (insert c S) w (Finset.mem_insert_of_mem hw)]

/-- The same for the turn sign. -/
theorem cvt165s_markTurn_insert (S : Finset (Crossing P)) (c : Crossing P) (m : Mark P)
    (hm : IsTrueCorner S m) :
    cvt165s_markTurn hP (insert c S) m = cvt165s_markTurn hP S m := by
  unfold cvt165s_markTurn
  cases m with
  | inl i => rw [geoOutSlot_vertex, geoOutSlot_vertex]
  | inr w =>
    have hw : w.1 ∈ S := hm
    rw [geoOutSlot_selected hP S w hw, geoOutSlot_selected hP (insert c S) w (Finset.mem_insert_of_mem hw)]

/-- **The two smoothing corners of a selected crossing cancel** in the real turn ledger: their principal
angles are `∠(d_i, d_j)` and `∠(d_j, d_i)` on a transverse pair (G5). -/
theorem cvt165s_new_turns_cancel (hn : 3 ≤ n) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    cvt165s_markPrincipalTurn hP S (Sum.inr v) + cvt165s_markPrincipalTurn hP S (Sum.inr (visitTwin v)) = 0 := by
  have hdet := geo_visit_corner_det_ne_zero hn hP S v hv
  have hv' : (visitTwin v).1 ∈ S := by
    rw [visitTwin_crossing]
    exact hv
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv] at hdet
  unfold cvt165s_markPrincipalTurn
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv, geoInEdge_visit hn hP (visitTwin v),
    geoOutSlot_selected hP S (visitTwin v) hv', visitTwin_involutive,
    principalAngle_swap (regularPair_of_det_ne_zero hdet)]
  ring

/-- The turn sign at a selected visit is nonzero (transversality). -/
theorem cvt165s_markTurn_visit_ne_zero (hn : 3 ≤ n) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    cvt165s_markTurn hP S (Sum.inr v) ≠ 0 :=
  sign_ne_zero.mpr (geo_visit_corner_det_ne_zero hn hP S v hv)

/-- The true corners of `insert c S` are those of `S` and the two visits of `c`. -/
theorem cvt165s_isTrueCorner_insert (S : Finset (Crossing P)) (c : Crossing P) (v₀ : Visit P)
    (hv₀ : v₀.1 = c) (m : Mark P) :
    IsTrueCorner (insert c S) m ↔ IsTrueCorner S m ∨ m = Sum.inr v₀ ∨ m = Sum.inr (visitTwin v₀) := by
  cases m with
  | inl i => exact ⟨fun _ => Or.inl trivial, fun _ => trivial⟩
  | inr w =>
    rw [isTrueCorner_visit, isTrueCorner_visit, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · right
        rcases visit_eq_or_twin v₀ w (h.trans hv₀.symm) with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | h | h)
      · exact Or.inr h
      · left
        rw [Sum.inr.inj h]
        exact hv₀
      · left
        rw [Sum.inr.inj h, visitTwin_crossing]
        exact hv₀

theorem cvt165s_cornerSet_disjoint (S : Finset (Crossing P)) {q r : GeoComponent hP S} (hqr : q ≠ r) :
    Disjoint (cvt165s_cornerSet hP S q) (cvt165s_cornerSet hP S r) := by
  rw [Finset.disjoint_left]
  intro m hq hr
  rw [cvt165s_mem_cornerSet] at hq hr
  exact hqr (hq.1.symm.trans hr.1)

/-- **The corner ledger of the split**: the corner marks of the two daughters at `insert c S` are the corner
marks of `A` at `S` together with the two visits of `c`. -/
theorem cvt165s_cornerSet_union (S : Finset (Crossing P)) (q : GeoComponent hP S) (v₀ : Visit P)
    (hown0 : ∀ w : Visit P, w.1 = v₀.1 → geoOwner hP S (Sum.inr w) = q)
    (q₁ q₂ : GeoComponent hP (insert v₀.1 S))
    (hown : ∀ m : Mark P, geoOwner hP S m = q ↔
      geoOwner hP (insert v₀.1 S) m = q₁ ∨ geoOwner hP (insert v₀.1 S) m = q₂) :
    cvt165s_cornerSet hP (insert v₀.1 S) q₁ ∪ cvt165s_cornerSet hP (insert v₀.1 S) q₂ =
      cvt165s_cornerSet hP S q ∪ {Sum.inr v₀, Sum.inr (visitTwin v₀)} := by
  ext m
  rw [Finset.mem_union, Finset.mem_union, cvt165s_mem_cornerSet, cvt165s_mem_cornerSet,
    cvt165s_mem_cornerSet, Finset.mem_insert, Finset.mem_singleton,
    cvt165s_isTrueCorner_insert S v₀.1 v₀ rfl m, ← or_and_right, ← hown m]
  have hA₀ : geoOwner hP S (Sum.inr v₀) = q := hown0 v₀ rfl
  have hA₁ : geoOwner hP S (Sum.inr (visitTwin v₀)) = q := hown0 (visitTwin v₀) (visitTwin_crossing v₀)
  constructor
  · rintro ⟨hm, hT | hm₀ | hm₁⟩
    · exact Or.inl ⟨hm, hT⟩
    · exact Or.inr (Or.inl hm₀)
    · exact Or.inr (Or.inr hm₁)
  · rintro (⟨hm, hT⟩ | rfl | rfl)
    · exact ⟨hm, Or.inl hT⟩
    · exact ⟨hA₀, Or.inr (Or.inl rfl)⟩
    · exact ⟨hA₁, Or.inr (Or.inr rfl)⟩

/-- The two visits of the unselected `c` are not corners of `S`. -/
theorem cvt165s_cornerSet_disjoint_visits (S : Finset (Crossing P)) (q : GeoComponent hP S) (v₀ : Visit P)
    (hcS : v₀.1 ∉ S) :
    Disjoint (cvt165s_cornerSet hP S q) {Sum.inr v₀, Sum.inr (visitTwin v₀)} := by
  rw [Finset.disjoint_left]
  intro m hm hm'
  rw [cvt165s_mem_cornerSet] at hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm'
  rcases hm' with rfl | rfl
  · exact hcS hm.2
  · exact hcS ((visitTwin_crossing v₀) ▸ hm.2)

end Cvt165sRot



section Cvt165sDaughterPattern

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P) (hn : 3 ≤ n)
  {S : Finset (Crossing P)} (hS : S ∈ Ind hP) {q : GeoComponent hP S} {v : Visit P}
  (hc : SingletonPieceOn hP S q v.1)

include hn hS hc in
/-- **The signed turn pattern of a daughter.** Every corner of the daughter `Λ` other than its visit `w` of
`c` is a corner of `A` (owned by `A`, a true corner of `S`), hence turns by `τ`; the corner at `w` turns by
`markTurn (inr w) ∈ {τ, −τ}`. -/
theorem cvt165s_daughter_pattern (Λ : GeoComponent hP (insert v.1 S))
    (hΛ : Λ = geoOwner hP (insert v.1 S) (Sum.inr v) ∨ Λ = geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)))
    (w : Visit P) (hw : w.1 = v.1) (hwΛ : geoOwner hP (insert v.1 S) (Sum.inr w) = Λ)
    (τ : SignType) (hτ0 : τ ≠ 0) (hτ : ∀ k, turn (geoCornerPolygon hP S q) k = τ) :
    (∀ k, turn (geoCornerPolygon hP (insert v.1 S) Λ) k = τ) ∨
      (∃ k₀, turn (geoCornerPolygon hP (insert v.1 S) Λ) k₀ = -τ ∧
        ∀ k, k ≠ k₀ → turn (geoCornerPolygon hP (insert v.1 S) Λ) k = τ) := by
  have hind : GeoIndependent hP S := geoIndependent_of_mem_Ind hP hS
  have hind' : GeoIndependent hP (insert v.1 S) := cvt165s_geoIndependent_insert hP hc hS
  have hwS' : w.1 ∈ insert v.1 S := by
    rw [hw]
    exact Finset.mem_insert_self _ _
  have hwT : IsTrueCorner (insert v.1 S) (Sum.inr w) := hwS'
  -- every corner of `Λ` other than `inr w` is an inherited corner of `A`, of turn `τ`
  have hother : ∀ k, geoCornerMark hP (insert v.1 S) Λ k ≠ Sum.inr w →
      turn (geoCornerPolygon hP (insert v.1 S) Λ) k = τ := by
    intro k hk
    rw [cvt165s_turn_eq_mark hP hn hind' Λ k]
    obtain ⟨hmΛ, hmT'⟩ := geoCornerMark_mem hP (insert v.1 S) Λ k
    have hmA : geoOwner hP S (geoCornerMark hP (insert v.1 S) Λ k) = q := by
      apply cvt165s_owner_of_insert hP hc
      rcases hΛ with hΛ | hΛ
      · exact Or.inl (hmΛ.trans hΛ)
      · exact Or.inr (hmΛ.trans hΛ)
    rcases (cvt165s_isTrueCorner_insert S v.1 w hw _).mp hmT' with hT | hmw | hmw
    · obtain ⟨k', hk'⟩ := geoCornerMark_exists_of_owner hP S q _ hmA hT
      rw [cvt165s_markTurn_insert hP S v.1 _ hT, ← hk', ← cvt165s_turn_eq_mark hP hn hind q k']
      exact hτ k'
    · exact absurd hmw hk
    · exfalso
      apply geo_selected_visits_separated hP hind' w hwS'
      rw [hwΛ, ← hmw]
      exact hmΛ.symm
  -- the corner at `w`
  obtain ⟨k₀, hk₀⟩ := geoCornerMark_exists_of_owner hP (insert v.1 S) Λ (Sum.inr w) hwΛ hwT
  have hk₀turn : turn (geoCornerPolygon hP (insert v.1 S) Λ) k₀ =
      cvt165s_markTurn hP (insert v.1 S) (Sum.inr w) := by
    rw [cvt165s_turn_eq_mark hP hn hind' Λ k₀, hk₀]
  have hw0 : cvt165s_markTurn hP (insert v.1 S) (Sum.inr w) ≠ 0 :=
    cvt165s_markTurn_visit_ne_zero hP hn (insert v.1 S) w hwS'
  rcases cvt165s_signType_eq_or_neg hw0 hτ0 with h | h
  · left
    intro k
    by_cases hk : geoCornerMark hP (insert v.1 S) Λ k = Sum.inr w
    · have hkk : k = k₀ := geoCornerMark_injective hP _ Λ (hk.trans hk₀.symm)
      rw [hkk, hk₀turn, h]
    · exact hother k hk
  · right
    refine ⟨k₀, by rw [hk₀turn, h], fun k hk => hother k fun hk' => ?_⟩
    exact hk (geoCornerMark_injective hP _ Λ (hk'.trans hk₀.symm))

end Cvt165sDaughterPattern

section Cvt165sSplitRot

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : Generic P) {S : Finset (Crossing P)}
  (hS : S ∈ Ind hG.crossingGeometry) {q : GeoComponent hG.crossingGeometry S}

/-- **`2π rot(L) = Σ` over the corner marks of `L`** of the mark principal turn. -/
theorem cvt165s_two_pi_rot (q : GeoComponent hG.crossingGeometry S) :
    2 * Real.pi * (rot (geoCornerPolygon hG.crossingGeometry S q) (carrierPolygon_cvRegular hn hG hS q) : ℝ) =
      ∑ m ∈ cvt165s_cornerSet hG.crossingGeometry S q, cvt165s_markPrincipalTurn hG.crossingGeometry S m := by
  rw [two_pi_mul_rot, ← cvt165s_sum_corners]
  exact Finset.sum_congr rfl fun k _ =>
    cvt165s_principalTurn_eq_mark hG.crossingGeometry hn (geoIndependent_of_mem_Ind _ hS) q k

variable {v : Visit P} (hc : SingletonPieceOn hG.crossingGeometry S q v.1)

include hc in
/-- **(d), real form: `rot(A) = rot(Λ₁) + rot(Λ₂)`** — every inherited corner keeps its principal turn and
the two new smoothing corners cancel. -/
theorem cvt165s_rot_add :
    (rot (geoCornerPolygon hG.crossingGeometry S q) (carrierPolygon_cvRegular hn hG hS q) : ℝ) =
      rot (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v)))
          (carrierPolygon_cvRegular hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS) _) +
        rot (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v))))
          (carrierPolygon_cvRegular hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS) _) := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  have hvne : (Sum.inr v : Mark P) ≠ Sum.inr (visitTwin v) := by
    intro h
    exact visitTwin_ne v (Sum.inr.inj h).symm
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2π
  rw [mul_add, cvt165s_two_pi_rot hn hG hS q, cvt165s_two_pi_rot hn hG hS', cvt165s_two_pi_rot hn hG hS',
    ← Finset.sum_union (cvt165s_cornerSet_disjoint _ _ (cvt165s_daughters_ne _ hc hS)),
    cvt165s_cornerSet_union _ S q v (fun w hw => cvt165s_owner_visit _ hc w hw) _ _
      (cvt165s_owner_iff _ hc hS),
    Finset.sum_union (cvt165s_cornerSet_disjoint_visits _ S q v (cvt165s_notMem _ hc)),
    Finset.sum_pair hvne, cvt165s_new_turns_cancel _ hn (insert v.1 S) v (Finset.mem_insert_self _ _),
    add_zero]
  exact Finset.sum_congr rfl fun m hm =>
    (cvt165s_markPrincipalTurn_insert _ S v.1 m ((cvt165s_mem_cornerSet _ S q m).mp hm).2).symm

include hn hS hc in
/-- The daughter patterns, at the two daughters. -/
theorem cvt165s_daughter_patterns (hq : CarrierUniform hG.crossingGeometry S q) :
    ∃ τ : SignType, τ ≠ 0 ∧
      (∀ k, turn (geoCornerPolygon hG.crossingGeometry S q) k = τ) ∧
      ((∀ k, turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) k = τ) ∨
        (∃ k₀, turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
            (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) k₀ = -τ ∧
          ∀ k, k ≠ k₀ → turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
            (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) k = τ)) ∧
      ((∀ k, turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) k = τ) ∨
        (∃ k₀, turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
            (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) k₀ = -τ ∧
          ∀ k, k ≠ k₀ → turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
            (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) k = τ)) := by
  obtain ⟨τ, hτ0, hτ⟩ := hq
  exact ⟨τ, hτ0, hτ,
    cvt165s_daughter_pattern hG.crossingGeometry hn hS hc _ (Or.inl rfl) v rfl rfl τ hτ0 hτ,
    cvt165s_daughter_pattern hG.crossingGeometry hn hS hc _ (Or.inr rfl) (visitTwin v) (visitTwin_crossing v)
      rfl τ hτ0 hτ⟩

include hc in
/-- **(d) `R(A) = R(Λ₁) + R(Λ₂)`**: the real rotations add and all three lie on the ray of `A`'s sign
(lem:uniformrot), so the absolute values add. -/
theorem cvt165s_carrierR_split (hq : CarrierUniform hG.crossingGeometry S q) :
    (carrierR hn hG hS q : ℤ) =
      carrierR hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v)) +
        carrierR hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v))) := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  obtain ⟨τ, hτ0, -, hp₁, hp₂⟩ := cvt165s_daughter_patterns hn hG hS hc hq
  have hsum := cvt165s_rot_add hn hG hS hc
  have hsumZ : rot (geoCornerPolygon hG.crossingGeometry S q) (carrierPolygon_cvRegular hn hG hS q) =
      rot _ (carrierPolygon_cvRegular hn hG hS' (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) +
        rot _ (carrierPolygon_cvRegular hn hG hS'
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) := by
    exact_mod_cast hsum
  have hr₁ := cvt165s_rot_ray _ (carrierPolygon_cvRegular hn hG hS' _) τ hp₁
  have hr₂ := cvt165s_rot_ray _ (carrierPolygon_cvRegular hn hG hS' _) τ hp₂
  rw [carrierR_cast, carrierR_cast, carrierR_cast, hsumZ]
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · exact (cvt165s_abs_add_of_ray _ _).1 (hr₁.2 rfl) (hr₂.2 rfl)
  · exact absurd rfl hτ0
  · exact (cvt165s_abs_add_of_ray _ _).2 (hr₁.1 rfl) (hr₂.1 rfl)

include hn hS hc in
/-- **(e)** Both daughters are uniform or one-dissent after reversal. -/
theorem cvt165s_daughters_alt (hq : CarrierUniform hG.crossingGeometry S q) :
    UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
        (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) ∧
      UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
        (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  obtain ⟨τ, hτ0, -, hp₁, hp₂⟩ := cvt165s_daughter_patterns hn hG hS hc hq
  exact ⟨cvt165s_uniformOrOneDissent_of_pattern _ (carrierPolygon_cvRegular hn hG hS' _) τ hτ0 hp₁,
    cvt165s_uniformOrOneDissent_of_pattern _ (carrierPolygon_cvRegular hn hG hS' _) τ hτ0 hp₂⟩

end Cvt165sSplitRot

end Cvt165s


/-- LEAF (unit U-SPLIT, ~1.5-2.5k lines): the split interface on the geo layer. -/
theorem cvt_singleton_split : SingletonSplitData := by
  intro n _ hn P hG S hS q hq c hc
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  have hc' : SingletonPieceOn hG.crossingGeometry S q (⟨c, i⟩ : Visit P).1 := hc
  rw [cvt165s_insert_eq c S]
  exact ⟨cvt165s_mem_Ind_insert hG.crossingGeometry hc' hS, _, _,
    cvt165s_groupedPoly_split hn hG hS hc', cvt165s_groupedWrithe_split hG hS hc',
    cvt165s_carrierR_split hn hG hS hc' hq, (cvt165s_daughters_alt hn hG hS hc' hq).1,
    (cvt165s_daughters_alt hn hG hS hc' hq).2⟩

/-- **Row 165, CV:singleton_D_i** (proposed name `CV.singleton_D_i`; declared and mapped only when
row 99 (C) lands). -/
theorem singleton_D_i : SingletonDiData :=
  singleton_D_i_of cvt_singleton_split (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC)

end

end CV
