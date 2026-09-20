import SM.CBProducts
import SM.CX1
import SM.EmbeddedRotation
import SM.UniformRotation
import SM.Reversal
import SM.SingleCrossing
import SM.Children
import SM.DeletionHalvesDefinition
import SM.NamedWallsDefinition
import SM.NamedWallSides
import SM.SoftGenericLemma
import SM.SoftAmplitudeSectors
import SM.HypR
import SM.LinkPositiveLift
import SM.CChamber
import SM.GermSides
import SM.VertexSides
import SM.CarrierFloorRows
-- Corner_RowClosureProbe.lean — the merge assembler's ROW-CLOSURE PROBE (2026-09-15, scratch, not a product): Corner_Assembled.lean with the §0 copies (lines 60-92) deleted, `import SM.CarrierFloorRows` added, the four §6 bodies composed (`exact cb_singleton_of_floor SM.thm_floor` etc.), `#print axioms` appended before `end SM`.  0 errors.

/-! # Statements_FINAL — the corner chain after thm:floor: rows 103 cb:singleton, 105 lem:corner-values,
110 thm:C-S7, 112 thm:C-soft (judge's decision, 2026-09-15)

Companion of work/drafts/corner/PLAN_FINAL.md (winner: DESIGN_B's skeleton, with DESIGN_A's grafts).
Check: `cd work/lean && lake env lean ../drafts/corner/Statements_FINAL.lean`.

Every `sorry` is either (a) a LEAF of the unit decomposition of PLAN_FINAL.md §4 (frozen statement, to be
proved in a byte-identical skeleton copy), or (b) one of the four ROW THEOREMS of §6, which become
one-liners `… (thm_floor)` once row 100 (`SM.thm_floor : FloorTheoremData`, floor lane) is accepted.
Everything else is PROVED from accepted declarations: the four row-level assemblies
`cb_singleton_of_floor`, `corner_values_of_singleton`, `thm_C_S7_of`, `thm_C_soft_of_cornerValues`,
row 105 clause (i) (`corner_values_i`, UNCONDITIONAL — grafted from Sketch_A), the floor-interface bridge
`carrierUniformOrOneDissent_of_signed`, and the companions.

Sources (frame SM15): reference/SM/sm-3-statesum.tex 4697-4702 (103; proof 4703-4759), 4801-4809 (105;
proof 4810-4820); reference/SM/sm-4-knotlaws.tex 267-274 (110; proof 275-908), 984-991 (112; proof
992-1147).  Dependencies (tools/claims.py): 103 ← thm:floor; 105 ← cb:singleton; 110 ← cb:singleton,
thm:floor; 112 ← lem:corner-values.  Fixed target names (work/lean/axiom-policy.json): `SM.thm_C_S7`,
`SM.thm_C_soft`.  Proposed: `SM.cb_singleton : CbSingletonData`, `SM.corner_values : CornerValuesData`.

§0 is a VERBATIM copy of the floor lane's interface (work/drafts/floor/Statements_FINAL.lean §7:
`AllLeftOrOneRight`, `CarrierUniformOrOneDissent` in the literal reversal form, `FloorTheoremData` with the
ℤ ∧ ℝ display) — NOT the Gap2Statements §8 shape both designs assumed; to be deleted when the floor lane's
module lands (the names then resolve to the accepted ones).  Only `a_floor`'s first conjunct is consumed
(rows 103, 110); `z_parity` is never used (FR-CC-10). -/

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## §0 The row-100 interface (VERBATIM from work/drafts/floor/Statements_FINAL.lean §7) and the bridge
from the signed form the proof routes produce. -/

section Floor

variable {n : ℕ} [NeZero n]

/-! (§0 copies of AllLeftOrOneRight, CarrierUniformOrOneDissent, FloorTheoremData DELETED in this probe:
the names resolve to the accepted SM/CarrierFloor.lean §7 via import SM.CarrierFloorRows.) -/

/-! ### The bridge (judge's addition, PROVED).  The proof routes of rows 103 and 110 produce turn
patterns in the SIGNED form "uniform of sign `τ`, or one dissent `−τ` among turns `τ`" (this is how
lem:uniformrot `uniform_rotation` is stated); the floor lane's hypothesis is the literal reversal form.
`turn_reversal` (SM/Reversal.lean:61) converts. -/

/-- "uniform with sign `τ`, or exactly one dissent" — the output shape of the leaves. -/
def SignedUniformOrOneDissent {m : ℕ} (Q : LabelledTuple m) : Prop :=
  ∃ τ : SignType, τ ≠ 0 ∧
    ((∀ j, turn Q j = τ) ∨ (∃ j₀, turn Q j₀ = -τ ∧ ∀ j, j ≠ j₀ → turn Q j = τ))

theorem allLeftOrOneRight_of_signed {m : ℕ} (Q : LabelledTuple m)
    (h : SignedUniformOrOneDissent Q) : AllLeftOrOneRight Q ∨ AllLeftOrOneRight (reversal Q) := by
  obtain ⟨τ, hτ, h⟩ := h
  rcases SignType.trichotomy τ with h1 | h1 | h1
  · -- `τ = −1`: after reversal every turn is left (`turn (reversal Q) i = −turn Q (2 − i)`)
    subst h1
    right
    rcases h with hall | ⟨j₀, hj₀, hoth⟩
    · left
      intro i
      rw [turn_reversal, hall]; decide
    · right
      refine ⟨2 - j₀, ?_, ?_⟩
      · rw [turn_reversal]
        have : (2 : ZMod m) - (2 - j₀) = j₀ := by ring
        rw [this, hj₀]; decide
      · intro i hi
        rw [turn_reversal, hoth]
        · decide
        · intro h2; apply hi; rw [← h2]; ring
  · exact absurd h1 hτ
  · subst h1
    left
    rcases h with hall | ⟨j₀, hj₀, hoth⟩
    · exact Or.inl hall
    · exact Or.inr ⟨j₀, hj₀, hoth⟩

/-- The floor's hypothesis from the signed turn pattern of a carrier. -/
theorem carrierUniformOrOneDissent_of_signed (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    (h : SignedUniformOrOneDissent (ccpCornerPolygon hn hP S q)) :
    CarrierUniformOrOneDissent hn hP S q :=
  allLeftOrOneRight_of_signed _ h

/-- A uniform carrier (def:uniform) has the signed pattern. -/
theorem signedUniformOrOneDissent_of_uniform (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (h : CarrierUniform hn hP S q) :
    SignedUniformOrOneDissent (ccpCornerPolygon hn hP S q) := by
  obtain ⟨τ, hτ, hall⟩ := h
  exact ⟨τ, hτ, Or.inl hall⟩

/-- The one conjunct of `a_floor` this lane consumes, taken at a signed turn pattern. -/
theorem FloorTheoremData.slot_le_of_signed (hF : FloorTheoremData) (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (h : SignedUniformOrOneDissent (ccpCornerPolygon hn hP S q)) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) :=
  (hF.a_floor hn P hP S hS q (carrierUniformOrOneDissent_of_signed hn hP S q h)).1

end Floor

/-! ## §1 Shared algebra (PROVED): the corner polynomial is nonzero; a product whose two factors satisfy
`a`-floors has zero coefficients below the summed floor. -/

section Algebra

variable {n : ℕ} [NeZero n]

/-- `H⁺_Q ≠ 0` (lp:core "P_D ≠ 0", identified with `homfly` by `P_eq_homfly`). -/
theorem cornerHomfly_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) :
    cornerHomfly hn hP S q hS ≠ 0 := by
  unfold cornerHomfly
  rw [← P_eq_homfly]
  exact lp_core.ne_zero _

/-- The degree argument shared by cb:singleton (eq. cb:singleton-gap) and the noninterlacing branch of
thm:C-S7 (eq. s7c:noninterlacing-extraction): if `k₁ ≤ mindeg_a f`, `k₂ ≤ mindeg_a g` with `f, g ≠ 0`,
every coefficient of `f g` at an `a`-degree `< k₁ + k₂` vanishes (`mindegAZ_mul`, LinkLaurentRing.lean:757).
FR-CC-3: this replaces the printed `[z⁰]`-row bookkeeping; no `z`-parity is consumed. -/
theorem coeffAt_mul_eq_zero_of_lt_floor {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) {k₁ k₂ d k : ℤ}
    (h₁ : k₁ ≤ mindegAZ f) (h₂ : k₂ ≤ mindegAZ g) (hd : d < k₁ + k₂) :
    coeffAt d k (f * g) = 0 := by
  by_contra hne
  have hle := (mindegAZ_spec (mul_ne_zero hf hg)).2 d k hne
  rw [mindegAZ_mul hf hg] at hle
  omega

end Algebra

/-! ## §2 Row 103 cb:singleton (sm-3:4697-4702; proof 4703-4759) -/

section Singleton

variable {n : ℕ} [NeZero n]

/-- **cb:singleton as printed**, one field: "Let `A` be a uniform carrier of `S`, and suppose one of its
self-crossing labels `c` interlaces no other self-crossing of `A`. Then `c(A) = 0`."
Binder as def:C / cb:blocks (`hn : 3 ≤ n`, `hP : Generic P`, `hS : IsDecomposition hn hP S`; FR-CC-2);
"self-crossing labels of `A`" = `carrierCrossings hn hP S A` (def:smoothing; lem:carriers (iii));
"interlaces no other self-crossing" = `∀ c' ∈ carrierCrossings … A, c' ≠ c → ¬ Interlaces hn hP c c'`
(def:interlace, in `G_P`; FR-CC-1); "uniform" = `CarrierUniform` (def:uniform);
`c(A) = cornerCoefficient hn hP S A hS` (def:C, the total coefficient). -/
structure CbSingletonData : Prop where
  isolated_zero : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (A : Component hn hP S),
    CarrierUniform hn hP S A →
    ∀ c ∈ carrierCrossings hn hP S A,
      (∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') →
      cornerCoefficient hn hP S A hS = 0

/-! ### Leaves of row 103 (frozen; units U103-A … U103-E of PLAN_FINAL.md §4). Prefix `sg_`. -/

/-- U103-A. An isolated self-crossing of `A` is undominated by `S` and interlaces NO undominated label (an
undominated interlacer would lie on `A` by lem:carriers (iv), hence be a self-crossing of `A`);
consequently `insert c S` is a decomposition (accepted `greedy_independent`, CBProducts.lean:1911) with
`U(insert c S) = U(S) ∖ {c}` (accepted `greedy_step`, :1917). -/
theorem sg_isolated_undominated (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hiso : ∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') :
    c ∈ supportUnselected hn hP S ∧
      (∀ x ∈ supportUnselected hn hP S, Interlaces hn hP x c → x ∈ carrierCrossings hn hP S A) ∧
      supportUnselected hn hP (insert c S) = (supportUnselected hn hP S).erase c := by
  -- `c` is unselected and both of its visits are owned by `A` (def:smoothing)
  obtain ⟨hcS, hcA⟩ := (mem_carrierCrossings hn hP S A c).mp hc
  -- (1) `c ∈ U(S)`: it is not selected, and it interlaces no selected label, because a
  -- neighbour of `S` has its two visits on different carriers (lem:carriers (iii),
  -- `neighbor_visit_owners_ne`), whereas both visits of `c` lie on `A`.
  have hcU : c ∈ supportUnselected hn hP S := by
    rw [mem_supportUnselected]
    refine ⟨hcS, fun hN => ?_⟩
    obtain ⟨i, _, _⟩ := crossing_visits_exist c
    exact neighbor_visit_owners_ne hn hP hS hN ⟨c, i⟩ rfl
      ((hcA ⟨c, i⟩ rfl).trans (hcA (visitTwin ⟨c, i⟩) rfl).symm)
  -- (2) an undominated label `x` interlacing `c` is a self-crossing of `A`: its two visits lie
  -- on one carrier `B` (lem:carriers (iii), `unselected_nonneighbor_*`) and alternate with the
  -- two visits of `c` on `A` (def:interlace unfolds to two `crossingVisitBetween`, i.e. two
  -- `traversalBetween` on `visitPosition`s), so `B = A` by the noncrossing assignment
  -- (lem:carriers (iv), `carriers_noncrossing_owner_eq`).
  have hint : ∀ x ∈ supportUnselected hn hP S, Interlaces hn hP x c →
      x ∈ carrierCrossings hn hP S A := by
    intro x hx hxc
    obtain ⟨-, x₀, x₁, c₀, c₁, -, -, h₀, h₁⟩ := hxc
    have hxB := unselected_nonneighbor_mem_carrierCrossings hn hP hS hx ⟨x, x₀⟩ rfl
    have hown : owner hn hP S (Sum.inr ⟨x, x₀⟩) = owner hn hP S (Sum.inr ⟨c, c₀⟩) :=
      carriers_noncrossing_owner_eq hn hP hS ⟨x, x₀⟩ ⟨c, c₀⟩ ⟨x, x₁⟩ ⟨c, c₁⟩ h₀ h₁
        (unselected_nonneighbor_both_visits_one_carrier hn hP hS hx ⟨x, x₀⟩ ⟨x, x₁⟩ rfl rfl)
        ((hcA ⟨c, c₀⟩ rfl).trans (hcA ⟨c, c₁⟩ rfl).symm)
    rwa [hown, hcA ⟨c, c₀⟩ rfl] at hxB
  refine ⟨hcU, hint, ?_⟩
  -- (3) eq. cb:greedy-step (`greedy_step`): `U(S ∪ {c}) = U(S) ∖ ({c} ∪ N(c))`; and
  -- `N(c) ∩ U(S) = ∅`: an undominated interlacer of `c` is a self-crossing of `A` by (2), which
  -- the isolation hypothesis forbids (`interlaces_symm` turns `x ~ c` into `c ~ x`).
  rw [greedy_step hn hP S c]
  ext y
  rw [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, mem_supportNeighbors]
  constructor
  · rintro ⟨hy, hN⟩
    exact ⟨fun h => hN (Or.inl h), hy⟩
  · rintro ⟨hyc, hy⟩
    refine ⟨hy, ?_⟩
    rintro (h | ⟨x, hx, hyx⟩)
    · exact hyc h
    · rw [Finset.mem_singleton] at hx
      rw [hx] at hyx
      exact hiso y (hint y hy hyx) hyc (interlaces_symm hn hP hyx)

/-! ### U103-B (helper unit, prefix `sgb_`): the blocks of `insert c S` are the blocks of `S` other than `{c}`.
Generic part: `G : SimpleGraph V`, `s : Set V`, `c ∈ s` isolated in `G[s]`, `t = s ∖ {c}` (given membership-wise).
The components of `G[t]` are the components of `G[s]` other than the component `{c}`, and the inclusion
`G[t] ↪ G[s]` (Mathlib `induceHomOfLE`) realises the correspondence vertex by vertex. -/

section SgbGraph

variable {V : Type*} (G : SimpleGraph V) {s t : Set V} {c : V}

/-- An isolated vertex of `G[s]` reaches no other vertex of `G[s]`. -/
theorem sgb_not_reachable_of_isolated (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    {z : s} (hz : z.1 ≠ c) : ¬ (G.induce s).Reachable ⟨c, hcs⟩ z := by
  rintro ⟨p⟩
  cases p with
  | nil => exact hz rfl
  | cons h _ => exact hc _ (Subtype.mem _) h.symm

/-- A walk of `G[s]` between vertices other than the isolated `c` never visits `c`: reachability
descends to `G[t]`, `t = s ∖ {c}`. -/
theorem sgb_reachable_descend (hc : ∀ x ∈ s, ¬ G.Adj x c) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c)
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
def sgb_compMap (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    (G.induce t).ConnectedComponent → (G.induce s).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (G.induceHomOfLE fun x hx => ((ht x).mp hx).1).toHom

theorem sgb_compMap_mk (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (x : t) :
    sgb_compMap G ht ((G.induce t).connectedComponentMk x) =
      (G.induce s).connectedComponentMk ⟨x.1, ((ht x).mp x.2).1⟩ := rfl

theorem sgb_compMap_injective (hc : ∀ x ∈ s, ¬ G.Adj x c) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    Function.Injective (sgb_compMap G ht) := by
  intro C D
  refine SimpleGraph.ConnectedComponent.ind₂ (fun x y h => ?_) C D
  rw [sgb_compMap_mk, sgb_compMap_mk, SimpleGraph.ConnectedComponent.eq] at h
  exact SimpleGraph.ConnectedComponent.sound
    (sgb_reachable_descend G hc ht ((ht _).mp x.2).2 ((ht _).mp y.2).2 h)

theorem sgb_mem_range_compMap_iff (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (C : (G.induce s).ConnectedComponent) :
    C ∈ Set.range (sgb_compMap G ht) ↔ C ≠ (G.induce s).connectedComponentMk ⟨c, hcs⟩ := by
  refine SimpleGraph.ConnectedComponent.ind (fun x => ?_) C
  constructor
  · rintro ⟨D, hD⟩ hx
    refine SimpleGraph.ConnectedComponent.ind (fun z hD => ?_) D hD
    rw [sgb_compMap_mk, hx, SimpleGraph.ConnectedComponent.eq] at hD
    exact sgb_not_reachable_of_isolated G hc hcs ((ht _).mp z.2).2 hD.symm
  · intro hx
    have hxc : x.1 ≠ c := fun h => hx (congrArg _ (Subtype.ext h))
    exact ⟨(G.induce t).connectedComponentMk ⟨x.1, (ht _).mpr ⟨x.2, hxc⟩⟩, rfl⟩

/-- **The components of `G[s ∖ {c}]` are the components of `G[s]` other than that of the isolated `c`.** -/
def sgb_compEquiv (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    (G.induce t).ConnectedComponent ≃
      {C : (G.induce s).ConnectedComponent // C ≠ (G.induce s).connectedComponentMk ⟨c, hcs⟩} :=
  (Equiv.ofInjective _ (sgb_compMap_injective G hc ht)).trans
    (Equiv.subtypeEquivRight (sgb_mem_range_compMap_iff G hc hcs ht))

theorem sgb_compEquiv_apply_val (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (D : (G.induce t).ConnectedComponent) :
    (sgb_compEquiv G hc hcs ht D).1 = sgb_compMap G ht D := rfl

/-- Vertex by vertex: `x` lies in the component `e D` of `G[s]` iff it lies in `D`. -/
theorem sgb_compEquiv_mem_iff (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (D : (G.induce t).ConnectedComponent) (x : V) :
    (∃ hx : x ∈ s, (G.induce s).connectedComponentMk ⟨x, hx⟩ = (sgb_compEquiv G hc hcs ht D).1) ↔
      ∃ hx : x ∈ t, (G.induce t).connectedComponentMk ⟨x, hx⟩ = D := by
  refine SimpleGraph.ConnectedComponent.ind (fun z => ?_) D
  rw [sgb_compEquiv_apply_val, sgb_compMap_mk]
  constructor
  · rintro ⟨hx, h⟩
    rw [SimpleGraph.ConnectedComponent.eq] at h
    have hxc : x ≠ c := by
      intro hxc
      have hxe : (⟨x, hx⟩ : s) = ⟨c, hcs⟩ := Subtype.ext hxc
      rw [hxe] at h
      exact sgb_not_reachable_of_isolated G hc hcs ((ht _).mp z.2).2 h
    exact ⟨(ht x).mpr ⟨hx, hxc⟩, SimpleGraph.ConnectedComponent.sound
      (sgb_reachable_descend G hc ht hxc ((ht _).mp z.2).2 h)⟩
  · rintro ⟨hx, h⟩
    refine ⟨((ht x).mp hx).1, ?_⟩
    have := congrArg (sgb_compMap G ht) h
    rw [sgb_compMap_mk, sgb_compMap_mk] at this
    exact this

end SgbGraph

/-! SM part, at `hc = cg hn hP`: the vertex set of `G_P[U(S)]` is `CV.U (cg hn hP) S = supportUnselected hn hP S`
(`CV.U_eq_generic`), its adjacency is `Interlaces hn hP` (rfl); `c ∈ U(S)` with no undominated interlacer is an
isolated vertex, and `U(insert c S) = U(S) ∖ {c}` (`greedy_step`). -/

section SgbPieces

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {S : Finset (Crossing P)} {c : Crossing P}

/-- From U103-A's second conjunct and the printed hypothesis of cb:singleton: no undominated label
interlaces `c` (an undominated interlacer is a self-crossing of `A` other than `c`, excluded by `hiso`;
`interlaces_symm` flips the direction). -/
theorem sgb_not_interlaces_of_isolated (A : Component hn hP S)
    (hiso : ∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c')
    (hint : ∀ x ∈ supportUnselected hn hP S, Interlaces hn hP x c → x ∈ carrierCrossings hn hP S A) :
    ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c := by
  intro x hx hxc
  have hne : x ≠ c := fun h => interlaces_irrefl hn hP c (h ▸ hxc)
  exact hiso x (hint x hx hxc) hne (interlaces_symm hn hP hxc)

omit [NeZero n] in
/-- `U(insert c S) = U(S) ∖ {c}` membership-wise (eq. cb:greedy-step `greedy_step`, with `N({c}) ∩ U(S) = ∅`). -/
theorem sgb_mem_unselected_insert_iff (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c)
    (x : Crossing P) :
    x ∈ supportUnselected hn hP (insert c S) ↔ x ∈ supportUnselected hn hP S ∧ x ≠ c := by
  rw [greedy_step hn hP S c, Finset.mem_sdiff, Finset.mem_insert, mem_supportNeighbors]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun hxc => h (Or.inl hxc)⟩
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, ?_⟩
    rintro (h | ⟨y, hy, hxy⟩)
    · exact hxc h
    · rw [Finset.mem_singleton] at hy
      subst hy
      exact hiso x hx hxy

/-- `c` is a vertex of `G_P[U(S)]` (`CV.U` is `supportUnselected`, `CV.U_eq_generic`). -/
theorem sgb_mem_U (hcU : c ∈ supportUnselected hn hP S) :
    c ∈ (↑(CV.U (CB.cg hn hP) S) : Set (Crossing P)) := by
  rw [Finset.mem_coe, CV.U_eq_generic]
  exact hcU

/-- The vertex set of `G_P[U(insert c S)]` is that of `G_P[U(S)]` minus `c`. -/
theorem sgb_mem_U_insert_iff (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c)
    (x : Crossing P) :
    x ∈ (↑(CV.U (CB.cg hn hP) (insert c S)) : Set (Crossing P)) ↔
      x ∈ (↑(CV.U (CB.cg hn hP) S) : Set (Crossing P)) ∧ x ≠ c := by
  rw [Finset.mem_coe, Finset.mem_coe, CV.U_eq_generic, CV.U_eq_generic]
  exact sgb_mem_unselected_insert_iff hn hP hiso x

/-- `c` is isolated in `G_P[U(S)]` (adjacency of `G_P` is `Interlaces`, rfl). -/
theorem sgb_adj_isolated (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) :
    ∀ x ∈ (↑(CV.U (CB.cg hn hP) S) : Set (Crossing P)),
      ¬ (geometricInterlacementGraph (CB.cg hn hP)).Adj x c := by
  intro x hx
  rw [Finset.mem_coe, CV.U_eq_generic hn hP] at hx
  exact hiso x hx

/-- The block of `c` has the labels `{c}` (its component is the singleton `{c}`). -/
theorem sgb_pieceLabels_pieceOf (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) :
    CV.pieceLabels (CB.cg hn hP) S (CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU)) = {c} := by
  ext x
  rw [CV.mem_pieceLabels, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, h⟩
    by_contra hxc
    unfold CV.pieceOf at h
    exact sgb_not_reachable_of_isolated (geometricInterlacementGraph (CB.cg hn hP))
      (sgb_adj_isolated hn hP hiso) (sgb_mem_U hn hP hcU) (z := ⟨x, hx⟩) hxc
      (SimpleGraph.ConnectedComponent.exact h).symm
  · rintro rfl
    exact ⟨sgb_mem_U hn hP hcU, rfl⟩

/-- A block has the labels `{c}` iff it is the block of `c`. -/
theorem sgb_pieceLabels_eq_singleton_iff (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (H : CV.Piece (CB.cg hn hP) S) :
    CV.pieceLabels (CB.cg hn hP) S H = {c} ↔ H = CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU) := by
  constructor
  · intro h
    have hcH : c ∈ CV.pieceLabels (CB.cg hn hP) S H := by
      rw [h]; exact Finset.mem_singleton_self c
    obtain ⟨_, hH⟩ := (CV.mem_pieceLabels _ S H c).mp hcH
    exact hH.symm
  · rintro rfl
    exact sgb_pieceLabels_pieceOf hn hP hcU hiso

/-- The block of any other undominated label is not the block `{c}`. -/
theorem sgb_pieceLabels_pieceOf_ne (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) {x : Crossing P}
    (hx : x ∈ CV.U (CB.cg hn hP) S) (hxc : x ≠ c) :
    CV.pieceLabels (CB.cg hn hP) S (CV.pieceOf (CB.cg hn hP) S x hx) ≠ {c} := by
  intro h
  have h' := (sgb_pieceLabels_eq_singleton_iff hn hP hcU hiso _).mp h
  unfold CV.pieceOf at h'
  exact sgb_not_reachable_of_isolated (geometricInterlacementGraph (CB.cg hn hP))
    (sgb_adj_isolated hn hP hiso) (sgb_mem_U hn hP hcU) (z := ⟨x, hx⟩) hxc
    (SimpleGraph.ConnectedComponent.exact h').symm

/-- **U103-B: `Piece (insert c S) ≃ {H : Piece S // pieceLabels H ≠ {c}}`** (PLAN_FINAL §3.1 (3a)): the blocks
of `S' = insert c S` are the blocks of `S` other than `{c}`, `c` being isolated in `G_P[U(S)]`. Label-preserving:
`sgb_pieceEquiv_labels`. -/
def sgb_pieceEquiv (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) :
    CV.Piece (CB.cg hn hP) (insert c S) ≃
      {H : CV.Piece (CB.cg hn hP) S // CV.pieceLabels (CB.cg hn hP) S H ≠ {c}} :=
  (sgb_compEquiv (geometricInterlacementGraph (CB.cg hn hP)) (sgb_adj_isolated hn hP hiso)
      (sgb_mem_U hn hP hcU) (sgb_mem_U_insert_iff hn hP hiso)).trans
    (Equiv.subtypeEquivRight fun H =>
      (not_congr (sgb_pieceLabels_eq_singleton_iff hn hP hcU hiso H)).symm)

/-- The equivalence on the block of a label: `e (pieceOf S' x) = pieceOf S x`. -/
theorem sgb_pieceEquiv_pieceOf (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (x : Crossing P)
    (hx : x ∈ CV.U (CB.cg hn hP) (insert c S)) :
    (sgb_pieceEquiv hn hP hcU hiso (CV.pieceOf (CB.cg hn hP) (insert c S) x hx)).1 =
      CV.pieceOf (CB.cg hn hP) S x ((sgb_mem_U_insert_iff hn hP hiso x).mp hx).1 := rfl

/-- The inverse on the block of a label `x ≠ c`: `e.symm (pieceOf S x) = pieceOf S' x`. -/
theorem sgb_pieceEquiv_symm_pieceOf (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) {x : Crossing P}
    (hx : x ∈ CV.U (CB.cg hn hP) S) (hxc : x ≠ c) :
    (sgb_pieceEquiv hn hP hcU hiso).symm
        ⟨CV.pieceOf (CB.cg hn hP) S x hx, sgb_pieceLabels_pieceOf_ne hn hP hcU hiso hx hxc⟩ =
      CV.pieceOf (CB.cg hn hP) (insert c S) x ((sgb_mem_U_insert_iff hn hP hiso x).mpr ⟨hx, hxc⟩) := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext rfl

/-- **Label-preserving**: the labels of `e H'` (as a block of `S`) are the labels of `H'` (as a block of `S'`). -/
theorem sgb_pieceEquiv_labels (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c)
    (H' : CV.Piece (CB.cg hn hP) (insert c S)) :
    CV.pieceLabels (CB.cg hn hP) S (sgb_pieceEquiv hn hP hcU hiso H').1 =
      CV.pieceLabels (CB.cg hn hP) (insert c S) H' := by
  ext x
  rw [CV.mem_pieceLabels, CV.mem_pieceLabels]
  exact sgb_compEquiv_mem_iff (geometricInterlacementGraph (CB.cg hn hP)) (sgb_adj_isolated hn hP hiso)
    (sgb_mem_U hn hP hcU) (sgb_mem_U_insert_iff hn hP hiso) H' x

/-- The blocks of `insert c S` as blocks of `S` (the equivalence with the `≠ {c}` proof forgotten). -/
def sgb_pieceEmbedding (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) :
    CV.Piece (CB.cg hn hP) (insert c S) ↪ CV.Piece (CB.cg hn hP) S :=
  (sgb_pieceEquiv hn hP hcU hiso).toEmbedding.trans (Function.Embedding.subtype _)

theorem sgb_pieceEmbedding_apply (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c)
    (H' : CV.Piece (CB.cg hn hP) (insert c S)) :
    sgb_pieceEmbedding hn hP hcU hiso H' = (sgb_pieceEquiv hn hP hcU hiso H').1 := rfl

theorem sgb_pieceLabels_pieceEmbedding (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c)
    (H' : CV.Piece (CB.cg hn hP) (insert c S)) :
    CV.pieceLabels (CB.cg hn hP) S (sgb_pieceEmbedding hn hP hcU hiso H') =
      CV.pieceLabels (CB.cg hn hP) (insert c S) H' :=
  sgb_pieceEquiv_labels hn hP hcU hiso H'

/-- A block of `S` is in the range of the embedding iff it is not the block `{c}`. -/
theorem sgb_mem_range_pieceEmbedding_iff (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (H : CV.Piece (CB.cg hn hP) S) :
    (∃ H', sgb_pieceEmbedding hn hP hcU hiso H' = H) ↔ CV.pieceLabels (CB.cg hn hP) S H ≠ {c} := by
  constructor
  · rintro ⟨H', rfl⟩
    exact (sgb_pieceEquiv hn hP hcU hiso H').2
  · intro h
    exact ⟨(sgb_pieceEquiv hn hP hcU hiso).symm ⟨H, h⟩, by
      rw [sgb_pieceEmbedding_apply, Equiv.apply_symm_apply]⟩

/-- `Finset.univ` of the blocks of `S` is the block `{c}` together with the (images of the) blocks of `S'`. -/
theorem sgb_univ_pieces_eq (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) :
    (Finset.univ : Finset (CV.Piece (CB.cg hn hP) S)) =
      insert (CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU))
        (Finset.univ.map (sgb_pieceEmbedding hn hP hcU hiso)) := by
  ext H
  rw [Finset.mem_insert, Finset.mem_map]
  simp only [Finset.mem_univ, true_and, true_iff]
  by_cases h : CV.pieceLabels (CB.cg hn hP) S H = {c}
  · exact Or.inl ((sgb_pieceLabels_eq_singleton_iff hn hP hcU hiso H).mp h)
  · exact Or.inr ((sgb_mem_range_pieceEmbedding_iff hn hP hcU hiso H).mpr h)

theorem sgb_pieceOf_notMem_map (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) :
    CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU) ∉
      Finset.univ.map (sgb_pieceEmbedding hn hP hcU hiso) := by
  rw [Finset.mem_map]
  rintro ⟨H', -, hH'⟩
  exact (sgb_pieceEquiv hn hP hcU hiso H').2
    ((sgb_pieceLabels_eq_singleton_iff hn hP hcU hiso _).mpr hH')

/-- The block `{c}` is owned by the carrier `A` whose self-crossing `c` is (`mem_blocksOwnedBy_iff`). -/
theorem sgb_pieceOf_mem_blocksOwnedBy (A : Component hn hP S) (hc : c ∈ carrierCrossings hn hP S A)
    (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) :
    CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU) ∈ CB.blocksOwnedBy hn hP S A := by
  rw [CB.mem_blocksOwnedBy_iff, sgb_pieceLabels_pieceOf hn hP hcU hiso]
  intro x hx v hv
  rw [Finset.mem_singleton] at hx
  subst hx
  exact ((mem_carrierCrossings hn hP S A x).mp hc).2 v hv

/-- Products over blocks of `S` of the shape "the block `{c}` plus images of blocks of `S'`" (the shape of
`blocksOwnedBy S A` after the split, eq. cb:singleton-products): `Finset.prod_insert` + `Finset.prod_map`. -/
theorem sgb_prod_insert_map {M : Type*} [CommMonoid M] (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c)
    (T : Finset (CV.Piece (CB.cg hn hP) (insert c S))) (f : CV.Piece (CB.cg hn hP) S → M) :
    ∏ H ∈ insert (CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU))
        (T.map (sgb_pieceEmbedding hn hP hcU hiso)), f H =
      f (CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU)) *
        ∏ H' ∈ T, f (sgb_pieceEmbedding hn hP hcU hiso H') := by
  rw [Finset.prod_insert, Finset.prod_map]
  intro h
  exact sgb_pieceOf_notMem_map hn hP hcU hiso
    (Finset.map_subset_map.mpr (Finset.subset_univ T) h)

/-- The additive form (for `carrierCrossingCount = ∑ card (pieceLabels H)`). -/
theorem sgb_sum_insert_map {M : Type*} [AddCommMonoid M] (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c)
    (T : Finset (CV.Piece (CB.cg hn hP) (insert c S))) (f : CV.Piece (CB.cg hn hP) S → M) :
    ∑ H ∈ insert (CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU))
        (T.map (sgb_pieceEmbedding hn hP hcU hiso)), f H =
      f (CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU)) +
        ∑ H' ∈ T, f (sgb_pieceEmbedding hn hP hcU hiso H') := by
  rw [Finset.sum_insert, Finset.sum_map]
  intro h
  exact sgb_pieceOf_notMem_map hn hP hcU hiso
    (Finset.map_subset_map.mpr (Finset.subset_univ T) h)

/-- Membership of an image block in the blocks owned by `A` at `S`, read on the labels of the source block
(`mem_blocksOwnedBy_iff` + label preservation; the owner comparison at `S'` is U103-D's). -/
theorem sgb_pieceEmbedding_mem_blocksOwnedBy_iff (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (A : Component hn hP S)
    (H' : CV.Piece (CB.cg hn hP) (insert c S)) :
    sgb_pieceEmbedding hn hP hcU hiso H' ∈ CB.blocksOwnedBy hn hP S A ↔
      ∀ x ∈ CV.pieceLabels (CB.cg hn hP) (insert c S) H', ∀ v : Visit P, v.1 = x →
        owner hn hP S (Sum.inr v) = A := by
  rw [CB.mem_blocksOwnedBy_iff, sgb_pieceLabels_pieceEmbedding]

end SgbPieces

/-! ### Helpers of U103-C (prefix `sgc_`; PLAN_FINAL §3.1 item 3(b)), consumed by `sg_daughters_products`:
`P_H` is determined by the labels of the block across a refinement `S ⊆ S'` (the `blockPoly_eq_of_labels_eq`
promised at CBBlocks.lean:105), and the block whose labels are `{c}` has `P_H = 1` (lc:single-crossing).  Route: a block
carrier diagram of `H' : Piece S'` lives over an independent refinement `T ⊇ S' ⊇ S` (`exists_blockCarrier`,
CBProducts.lean:1740), so it is one of `H` as well, and `polynomial_independent` (cb:products) pins `SM.P D`
on both sides; the block diagram of a one-label block has one crossing (`carrierCrossingEquiv`,
LinkPositiveLift.lean:799), so `single_crossing.one_crossing` (SingleCrossing.lean:152-165) gives `1`. -/

/-- U103-C. A block carrier diagram of `H' : Piece S'` (over an independent refinement `T ⊇ S'`) is a block
carrier diagram of any `H : Piece S`, `S ⊆ S'`, with the same labels. -/
theorem sgc_isBlockCarrierDiagram_of_subset (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S S' : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hP S')
    (hSS' : S ⊆ S') (H : CV.Piece (CB.cg hn hP) S) (H' : CV.Piece (CB.cg hn hP) S')
    (hlab : CV.pieceLabels (CB.cg hn hP) S H = CV.pieceLabels (CB.cg hn hP) S' H') {D : Diagram}
    (hD : CB.IsBlockCarrierDiagram hn hP hS' H' D) : CB.IsBlockCarrierDiagram hn hP hS H D := by
  obtain ⟨T, hT, q, hST, hq, rfl⟩ := hD
  exact ⟨T, hT, q, hSS'.trans hST, hq.trans hlab.symm, rfl⟩

/-- U103-C. Blocks with the same labels across `S ⊆ S'` have isomorphic restricted named records. -/
theorem sgc_blockRecord_iso_of_labels_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S S' : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hP S')
    (hSS' : S ⊆ S') (H : CV.Piece (CB.cg hn hP) S) (H' : CV.Piece (CB.cg hn hP) S')
    (hlab : CV.pieceLabels (CB.cg hn hP) S H = CV.pieceLabels (CB.cg hn hP) S' H') :
    Nonempty (RecordIso (CB.blockRecord hn hP hS H) (CB.blockRecord hn hP hS' H')) := by
  obtain ⟨D, hD, -⟩ := (cb_products hn hP hS').block_diagram H'
  obtain ⟨ι⟩ := ((cb_products hn hP hS).polynomial_independent H D
    (sgc_isBlockCarrierDiagram_of_subset hn hP hS hS' hSS' H H' hlab hD)).1
  obtain ⟨κ⟩ := ((cb_products hn hP hS').polynomial_independent H' D hD).1
  exact ⟨ι.symm.trans κ⟩

/-- U103-C, the `blockPoly_eq_of_labels_eq` promised at CBBlocks.lean:105: `P_H` is determined by the labels
of the block across a refinement `S ⊆ S'` (cb:singleton's before/after split, sm-3:4719-4724). -/
theorem sgc_blockPoly_eq_of_labels_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S S' : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hP S')
    (hSS' : S ⊆ S') (H : CV.Piece (CB.cg hn hP) S) (H' : CV.Piece (CB.cg hn hP) S')
    (hlab : CV.pieceLabels (CB.cg hn hP) S H = CV.pieceLabels (CB.cg hn hP) S' H') :
    CB.blockPoly hn hP hS H = CB.blockPoly hn hP hS' H' := by
  obtain ⟨D, hD, -⟩ := (cb_products hn hP hS').block_diagram H'
  rw [← ((cb_products hn hP hS').polynomial_independent H' D hD).2,
    ← ((cb_products hn hP hS).polynomial_independent H D
      (sgc_isBlockCarrierDiagram_of_subset hn hP hS hS' hSS' H H' hlab hD)).2]

/-- U103-C, lc:single-crossing on a positive lift: a carrier with exactly one self-crossing (`m_q = 1`) has
`P_{D_q} = 1` (`card_carrierShadow_crossing` via `carrierCrossingEquiv`; `single_crossing.one_crossing`). -/
theorem sgc_P_positiveLift_eq_one_of_count_one (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {T : Finset (Crossing P)} (hT : IsDecomposition hn hP T) (q : Component hn hP T)
    (h : carrierCrossingCount hn hP T q = 1) : SM.P (positiveLift hn hP T q hT) = 1 := by
  have hcard : Fintype.card (carrierShadow hn hP T q hT).Crossing = 1 := by
    rw [card_carrierShadow_crossing, h]
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
  exact single_crossing.one_crossing (positiveLift hn hP T q hT) x rfl hx

/-- U103-C. A block with exactly one label has `P_H = 1`. -/
theorem sgc_blockPoly_eq_one_of_card_one (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (H : CV.Piece (CB.cg hn hP) S)
    (hH : (CV.pieceLabels (CB.cg hn hP) S H).card = 1) : CB.blockPoly hn hP hS H = 1 := by
  obtain ⟨T, hT, q, hST, hq⟩ := CB.exists_blockCarrier hn hP hS H
  rw [← ((cb_products hn hP hS).polynomial_independent H (positiveLift hn hP T q hT)
    ⟨T, hT, q, hST, hq, rfl⟩).2]
  apply sgc_P_positiveLift_eq_one_of_count_one
  show (carrierCrossings hn hP T q).card = 1
  rw [hq, hH]

/-- U103-C, "`blockPoly {c} = 1`" (lc:single-crossing, sm-3:4722-4723): the block whose labels are `{c}` has
`P_H = 1`. -/
theorem sgc_blockPoly_eq_one_of_labels_eq_singleton (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (H : CV.Piece (CB.cg hn hP) S)
    {c : Crossing P} (hH : CV.pieceLabels (CB.cg hn hP) S H = {c}) : CB.blockPoly hn hP hS H = 1 :=
  sgc_blockPoly_eq_one_of_card_one hn hP hS H (by rw [hH, Finset.card_singleton])

/-! ### Helpers of U103-D (prefix `sgd_`; PLAN_FINAL §3.1 items 2 and 3(c)), consumed by `sg_daughters_products`:
the two daughters of `A` at `S' = insert c S` with the owner `↔` (`smoothingSuccessor_insert_child_data`,
CarrierInsertOrbits.lean:49: the two child orbits are the two slices of the rotated mark list;
`owner_insert_eq_imp`, CarrierOrbitRefinement.lean:80: the refinement only splits), the block redistribution
`blocksOwnedBy S A = {c}-block ⊔ images of (blocksOwnedBy S' Λ₁ ⊔ blocksOwnedBy S' Λ₂)` through U103-B's
`sgb_pieceEmbedding` (`one_owner` at `S'` puts every other block of `A` on exactly one daughter), and cb:products
before and after (`product`, `count`) with U103-C's `sgc_blockPoly_eq_of_labels_eq` / `blockPoly {c} = 1`. -/

section SgdDaughters

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {S : Finset (Crossing P)} {c : Crossing P}

/-- U103-D, the daughters (sm-3:4711-4718): smoothing the self-crossing `c` of `A` at `S' = insert c S` splits `A`
into the two carriers `Λ₁ = owner S' (inr v)`, `Λ₂ = owner S' (inr (twin v))` of the two visits of `c`
(`Λ₁ ≠ Λ₂`: `independent_selected_pair_owners_ne`), and a mark lies on `A` iff it lies on one of them: every mark
is in the rotated mark list `inr v :: (L₁ ++ inr (twin v) :: L₂)`, whose `A`-marks in `L₂` / `L₁` are exactly the
children `inr v :: BL` / `inr (twin v) :: AL` of `smoothingSuccessor_insert_child_data`; conversely the refinement
only splits (`owner_insert_eq_imp`). -/
theorem sgd_daughters (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (hc : c ∈ carrierCrossings hn hP S A) (hS' : IsDecomposition hn hP (insert c S)) :
    ∃ Λ₁ Λ₂ : Component hn hP (insert c S), Λ₁ ≠ Λ₂ ∧
      ∀ m : Mark P, owner hn hP S m = A ↔
        owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂ := by
  obtain ⟨hcS, hcA⟩ := (mem_carrierCrossings hn hP S A c).mp hc
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  have hv : (⟨c, i⟩ : Visit P).1 ∉ S := hcS
  have hvA : owner hn hP S (Sum.inr ⟨c, i⟩) = A := hcA ⟨c, i⟩ rfl
  have htA : owner hn hP S (Sum.inr (visitTwin ⟨c, i⟩)) = A := hcA (visitTwin ⟨c, i⟩) rfl
  have hown : owner hn hP S (Sum.inr ⟨c, i⟩) = owner hn hP S (Sum.inr (visitTwin ⟨c, i⟩)) :=
    hvA.trans htA.symm
  obtain ⟨k, L₁, L₂, hrot, hdata⟩ :=
    smoothingSuccessor_insert_child_data hn hP S (independent_inheritsMarkOrder hn hP hS) ⟨c, i⟩ hv hown
  obtain ⟨-, -, -, h₁, h₂, -, -⟩ := hdata
  refine ⟨owner hn hP (insert c S) (Sum.inr ⟨c, i⟩), owner hn hP (insert c S) (Sum.inr (visitTwin ⟨c, i⟩)),
    independent_selected_pair_owners_ne hn hP hS' ⟨c, i⟩ (Finset.mem_insert_self c S), ?_⟩
  intro m
  constructor
  · intro hm
    have hmem : m ∈ (markList hn hP).rotate k := List.mem_rotate.mpr (mem_markList hn hP m)
    rw [hrot] at hmem
    simp only [List.mem_cons, List.mem_append] at hmem
    rcases hmem with rfl | hm1 | rfl | hm2
    · exact Or.inl rfl
    · refine Or.inr ((h₂ m).mpr (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hm1, ?_⟩)))
      rw [decide_eq_true_eq, hm, hvA]
    · exact Or.inr rfl
    · refine Or.inl ((h₁ m).mpr (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hm2, ?_⟩)))
      rw [decide_eq_true_eq, hm, hvA]
  · have hsc : (smoothingSuccessor hn hP S).SameCycle (Sum.inr ⟨c, i⟩) (Sum.inr (visitTwin ⟨c, i⟩)) :=
      (owner_eq_iff hn hP S _ _).mp hown
    rintro (hm | hm)
    · exact (owner_insert_eq_imp hn hP S ⟨c, i⟩ hv hsc hm).trans hvA
    · exact (owner_insert_eq_imp hn hP S ⟨c, i⟩ hv hsc hm).trans htA

/-- U103-D. Blocks owned by two distinct carriers are disjoint (`blockOwner` is a function). -/
theorem sgd_blocksOwnedBy_disjoint {S' : Finset (Crossing P)} (hS' : IsDecomposition hn hP S')
    {Λ₁ Λ₂ : Component hn hP S'} (hne : Λ₁ ≠ Λ₂) :
    Disjoint (CB.blocksOwnedBy hn hP S' Λ₁) (CB.blocksOwnedBy hn hP S' Λ₂) := by
  rw [Finset.disjoint_left]
  intro H h1 h2
  exact hne ((CB.blockOwner_eq_of_mem hn hP hS' h1).symm.trans (CB.blockOwner_eq_of_mem hn hP hS' h2))

/-- U103-D. A block of `S'` owned by a daughter is, as a block of `S`, owned by `A` (the owner `↔`, read on every
visit of every label). -/
theorem sgd_pieceEmbedding_mem_blocksOwnedBy (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (A : Component hn hP S)
    {Λ₁ Λ₂ : Component hn hP (insert c S)}
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂)
    {H' : CV.Piece (CB.cg hn hP) (insert c S)}
    (hH' : H' ∈ CB.blocksOwnedBy hn hP (insert c S) Λ₁ ∪ CB.blocksOwnedBy hn hP (insert c S) Λ₂) :
    sgb_pieceEmbedding hn hP hcU hiso H' ∈ CB.blocksOwnedBy hn hP S A := by
  rw [sgb_pieceEmbedding_mem_blocksOwnedBy_iff]
  intro x hx v hv
  rw [hown]
  rw [Finset.mem_union, CB.mem_blocksOwnedBy_iff, CB.mem_blocksOwnedBy_iff] at hH'
  rcases hH' with h | h
  · exact Or.inl (h x hx v hv)
  · exact Or.inr (h x hx v hv)

/-- U103-D. Conversely, a block of `S` owned by `A` other than `{c}` is the image of a block of `S'` owned by one of
the daughters: its owner at `S'` is the owner of any of its labels (`one_owner`), which lies on `A` at `S`, hence on
`Λ₁` or `Λ₂` at `S'`. -/
theorem sgd_exists_preimage (hS' : IsDecomposition hn hP (insert c S)) (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (A : Component hn hP S)
    {Λ₁ Λ₂ : Component hn hP (insert c S)}
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂)
    {H : CV.Piece (CB.cg hn hP) S} (hH : H ∈ CB.blocksOwnedBy hn hP S A)
    (hHc : CV.pieceLabels (CB.cg hn hP) S H ≠ {c}) :
    ∃ H' ∈ CB.blocksOwnedBy hn hP (insert c S) Λ₁ ∪ CB.blocksOwnedBy hn hP (insert c S) Λ₂,
      sgb_pieceEmbedding hn hP hcU hiso H' = H := by
  obtain ⟨H', rfl⟩ := (sgb_mem_range_pieceEmbedding_iff hn hP hcU hiso H).mpr hHc
  refine ⟨H', ?_, rfl⟩
  obtain ⟨x, hx⟩ := CV.pieceLabels_nonempty (CB.cg hn hP) (insert c S) H'
  have hxS : x ∈ CV.pieceLabels (CB.cg hn hP) S (sgb_pieceEmbedding hn hP hcU hiso H') := by
    rw [sgb_pieceLabels_pieceEmbedding]
    exact hx
  have hxA : owner hn hP S (Sum.inr (CB.someVisit x)) = A :=
    (CB.mem_blocksOwnedBy_iff hn hP A _).mp hH x hxS _ rfl
  have hbo : CB.blockOwner hn hP hS' H' = owner hn hP (insert c S) (Sum.inr (CB.someVisit x)) :=
    (((cb_products hn hP hS').one_owner H').2 x hx).symm
  rw [Finset.mem_union, CB.mem_blocksOwnedBy_iff_blockOwner hn hP hS',
    CB.mem_blocksOwnedBy_iff_blockOwner hn hP hS', hbo]
  exact (hown _).mp hxA

/-- **U103-D, the block redistribution** (sm-3:4719-4724): the blocks owned by `A` at `S` are the block `{c}` and
the images of the blocks owned by the two daughters at `S'`. -/
theorem sgd_blocksOwnedBy_eq (hS' : IsDecomposition hn hP (insert c S)) (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (A : Component hn hP S)
    (hc : c ∈ carrierCrossings hn hP S A) {Λ₁ Λ₂ : Component hn hP (insert c S)}
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    CB.blocksOwnedBy hn hP S A =
      insert (CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU))
        ((CB.blocksOwnedBy hn hP (insert c S) Λ₁ ∪ CB.blocksOwnedBy hn hP (insert c S) Λ₂).map
          (sgb_pieceEmbedding hn hP hcU hiso)) := by
  ext H
  rw [Finset.mem_insert, Finset.mem_map]
  constructor
  · intro hH
    by_cases h : CV.pieceLabels (CB.cg hn hP) S H = {c}
    · exact Or.inl ((sgb_pieceLabels_eq_singleton_iff hn hP hcU hiso H).mp h)
    · exact Or.inr (sgd_exists_preimage hn hP hS' hcU hiso A hown hH h)
  · rintro (rfl | ⟨H', hH', rfl⟩)
    · exact sgb_pieceOf_mem_blocksOwnedBy hn hP A hc hcU hiso
    · exact sgd_pieceEmbedding_mem_blocksOwnedBy hn hP hcU hiso A hown hH'

/-- U103-D, eq. cb:singleton-products for `P_A = P_{D_A}`: `P_A = P_{Λ₁} P_{Λ₂}` (cb:products `product` at `S` and
`S'`; the block `{c}` contributes `1` by lc:single-crossing, every other block of `A` has the `blockPoly` of its
preimage by `sgc_blockPoly_eq_of_labels_eq`). -/
theorem sgd_carrierPoly_eq (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hP (insert c S))
    (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (A : Component hn hP S)
    (hc : c ∈ carrierCrossings hn hP S A) {Λ₁ Λ₂ : Component hn hP (insert c S)} (hne : Λ₁ ≠ Λ₂)
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    CB.carrierPoly hn hP hS A = CB.carrierPoly hn hP hS' Λ₁ * CB.carrierPoly hn hP hS' Λ₂ := by
  rw [(cb_products hn hP hS).product A, (cb_products hn hP hS').product Λ₁,
    (cb_products hn hP hS').product Λ₂, sgd_blocksOwnedBy_eq hn hP hS' hcU hiso A hc hown,
    sgb_prod_insert_map,
    sgc_blockPoly_eq_one_of_labels_eq_singleton hn hP hS _ (sgb_pieceLabels_pieceOf hn hP hcU hiso), one_mul,
    Finset.prod_union (sgd_blocksOwnedBy_disjoint hn hP hS' hne)]
  congr 1 <;> exact Finset.prod_congr rfl fun H' _ =>
    sgc_blockPoly_eq_of_labels_eq hn hP hS hS' (Finset.subset_insert c S) _ H'
      (sgb_pieceLabels_pieceEmbedding hn hP hcU hiso H')

/-- U103-D, eq. cb:singleton-products for the writhes: `m_A = m_{Λ₁} + m_{Λ₂} + 1` (cb:products `count` at `S` and
`S'`; the block `{c}` contributes one label). -/
theorem sgd_carrierCrossingCount_eq (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hP (insert c S))
    (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) (A : Component hn hP S)
    (hc : c ∈ carrierCrossings hn hP S A) {Λ₁ Λ₂ : Component hn hP (insert c S)} (hne : Λ₁ ≠ Λ₂)
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    carrierCrossingCount hn hP S A =
      carrierCrossingCount hn hP (insert c S) Λ₁ + carrierCrossingCount hn hP (insert c S) Λ₂ + 1 := by
  rw [(cb_products hn hP hS).count A, (cb_products hn hP hS').count Λ₁,
    (cb_products hn hP hS').count Λ₂, sgd_blocksOwnedBy_eq hn hP hS' hcU hiso A hc hown,
    sgb_sum_insert_map, sgb_pieceLabels_pieceOf hn hP hcU hiso, Finset.card_singleton,
    Finset.sum_union (sgd_blocksOwnedBy_disjoint hn hP hS' hne)]
  simp only [sgb_pieceLabels_pieceEmbedding]
  omega

end SgdDaughters

/-- U103-B/C/D (the daughters and eq. cb:singleton-products).  Smoothing `c` at `S' = insert c S` splits
`A` into two carriers `Λ₁ ≠ Λ₂` (`smoothingSuccessor_insert_child_data`, CarrierInsertOrbits.lean:49;
`component_card_insert`, CarrierComponentCount.lean:58), leaves every other carrier unchanged
(`owner_insert_iff_of_unaffected`, :99), and cb:products before and after (the blocks of `S'` are the
blocks of `S` other than `{c}`, same labels hence same `blockPoly`; `blockPoly {c} = 1` by
lc:single-crossing) gives `P_A = P_{Λ₁} P_{Λ₂}`, `m_A = m_{Λ₁} + m_{Λ₂} + 1`. -/
theorem sg_daughters_products (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hiso : ∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') :
    ∃ (hS' : IsDecomposition hn hP (insert c S)) (Λ₁ Λ₂ : Component hn hP (insert c S)),
      Λ₁ ≠ Λ₂ ∧
      (∀ m : Mark P, owner hn hP S m = A ↔
        owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) ∧
      cornerHomfly hn hP S A hS =
        cornerHomfly hn hP (insert c S) Λ₁ hS' * cornerHomfly hn hP (insert c S) Λ₂ hS' ∧
      carrierCrossingCount hn hP S A =
        carrierCrossingCount hn hP (insert c S) Λ₁ + carrierCrossingCount hn hP (insert c S) Λ₂ + 1 := by
  -- `c ∈ U(S)` and no undominated label interlaces `c` (U103-A + `hiso`); `S' = insert c S` is a decomposition
  obtain ⟨hcU, hint, -⟩ := sg_isolated_undominated hn hP hS A hc hiso
  have hiso' := sgb_not_interlaces_of_isolated hn hP A hiso hint
  have hS' : IsDecomposition hn hP (insert c S) := greedy_independent hn hP hS hcU
  -- the two daughters and the owner `↔`
  obtain ⟨Λ₁, Λ₂, hne, hown⟩ := sgd_daughters hn hP hS A hc hS'
  refine ⟨hS', Λ₁, Λ₂, hne, hown, ?_, sgd_carrierCrossingCount_eq hn hP hS hS' hcU hiso' A hc hne hown⟩
  -- `H⁺ = P_{D}` (cb:blocks `equals_Hplus`), then eq. cb:singleton-products on `carrierPoly`
  rw [← ((cb_blocks_definition hn hP hS).equals_Hplus A).2,
    ← ((cb_blocks_definition hn hP hS').equals_Hplus Λ₁).2,
    ← ((cb_blocks_definition hn hP hS').equals_Hplus Λ₂).2]
  exact sgd_carrierPoly_eq hn hP hS hS' hcU hiso' A hc hne hown

/-! #### U103-E helpers (prefix `sge_`).  The corner turn of a carrier is a function of its corner
MARK alone (`turn_ccpCornerPolygon_eq_markTurn`, CX1); here the same is done for the REAL principal
turn: `principalTurn (ccpCornerPolygon …) j = sge_markPrincipalTurn S (ccpCornerMark … j)`, because both
corner edges are positive multiples of the original directions `edge P (ccpInEdge m)`,
`edge P (ccpOutSlot S m).1` (lem:carriers (ii), `ccpCornerPolygon_edge/_edge_pred`) and `principalAngle`
is invariant under positive scaling.  Then `2π r_Q` is a sum over the corner-mark finset, inherited
marks keep their value under `S → insert c S` (the out-slot of a true corner of `S` is unchanged), and
the two new smoothing corners cancel (`principalAngle` is antisymmetric on a transverse pair). -/

/-- `cornerRotor` is homogeneous under positive scaling of both arguments. -/
theorem sge_cornerRotor_smul (a b : ℝ) (u v : Plane) :
    cornerRotor (a • u) (b • v) = ((a * b : ℝ) : ℂ) * cornerRotor u v := by
  apply Complex.ext
  · rw [cornerRotor_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, cornerRotor_re,
      cornerRotor_im]
    simp only [planeDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · rw [cornerRotor_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, cornerRotor_re,
      cornerRotor_im]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- The principal angle does not see positive rescaling of either vector. -/
theorem sge_principalAngle_smul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u v : Plane) :
    principalAngle (a • u) (b • v) = principalAngle u v := by
  unfold principalAngle
  rw [sge_cornerRotor_smul, Complex.arg_real_mul _ (mul_pos ha hb)]

/-- Swapping the arguments conjugates the rotor. -/
theorem sge_cornerRotor_swap (u v : Plane) : cornerRotor v u = star (cornerRotor u v) := by
  unfold cornerRotor
  rw [star_mul, star_star]

/-- Antisymmetry of the principal angle on a transverse pair (`det ≠ 0`, so the rotor is off the
negative real axis and `arg (conj z) = − arg z`). -/
theorem sge_principalAngle_swap {u v : Plane} (h : det u v ≠ 0) :
    principalAngle v u = - principalAngle u v := by
  unfold principalAngle
  have hne : (cornerRotor u v).arg ≠ Real.pi := by
    intro hpi
    have him := (Complex.arg_eq_pi_iff.mp hpi).2
    rw [cornerRotor_im] at him
    exact h him
  rw [sge_cornerRotor_swap, Complex.star_def, Complex.arg_conj, ite_eq_right hne]

/-- The real principal turn of a true corner, read off its mark and the support: the principal
angle from the original incoming direction to the original outgoing direction (the real extension
of CX1's `markTurn`). -/
noncomputable def sge_markPrincipalTurn (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (m : Mark P) : ℝ :=
  principalAngle (edge P (ccpInEdge hn hP m)) (edge P (ccpOutSlot hn hP S m).1)

/-- The principal turn of the corner polygon at its `j`-th corner is the mark principal turn of
that corner (lem:carriers (ii): both corner edges are positive multiples of the original
directions). -/
theorem sge_principalTurn_eq_mark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    principalTurn (ccpCornerPolygon hn hP S q) j =
      sge_markPrincipalTurn hn hP S (ccpCornerMark hn hP S q j) := by
  obtain ⟨c₁, hc₁, he₁⟩ := ccpCornerPolygon_edge_pred hn hP hS q j
  obtain ⟨c₂, hc₂, he₂⟩ := ccpCornerPolygon_edge hn hP hS q j
  unfold principalTurn sge_markPrincipalTurn
  rw [he₁, he₂, sge_principalAngle_smul hc₁ hc₂]

/-- The corner marks of the carrier `q` at `S` as a finset: the true corners of `S` owned by `q`. -/
noncomputable def sge_cornerSet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Finset (Mark P) :=
  Finset.univ.filter fun m => owner hn hP S m = q ∧ IsTrueCorner S m

theorem sge_mem_cornerSet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (m : Mark P) :
    m ∈ sge_cornerSet hn hP S q ↔ owner hn hP S m = q ∧ IsTrueCorner S m := by
  simp only [sge_cornerSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `ccpCornerMark` enumerates the corner set exactly once. -/
theorem sge_image_cornerMark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    Finset.univ.image (ccpCornerMark hn hP S q) = sge_cornerSet hn hP S q := by
  ext m
  rw [Finset.mem_image, sge_mem_cornerSet]
  constructor
  · rintro ⟨j, -, rfl⟩
    exact ccpCornerMark_mem hn hP S q j
  · rintro ⟨h1, h2⟩
    obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S q m h1 h2
    exact ⟨j, Finset.mem_univ _, hj⟩

/-- A sum over the corners of `q` is a sum over its corner-mark finset. -/
theorem sge_sum_corners (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (f : Mark P → ℝ) :
    ∑ j, f (ccpCornerMark hn hP S q j) = ∑ m ∈ sge_cornerSet hn hP S q, f m := by
  rw [← sge_image_cornerMark, Finset.sum_image]
  intro i _ j _ hij
  exact ccpCornerMark_injective hn hP S q hij

/-- **Rotation as a mark sum**: `2π r_Q = Σ_{m corner mark of Q} markPrincipalTurn S m`. -/
theorem sge_rotation_eq_sum (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    carrierRotation hn hP S q * (2 * Real.pi) =
      ∑ m ∈ sge_cornerSet hn hP S q, sge_markPrincipalTurn hn hP S m := by
  unfold carrierRotation rotationNumber
  rw [div_mul_cancel₀ _ (by positivity), ← sge_sum_corners]
  exact Finset.sum_congr rfl fun j _ => sge_principalTurn_eq_mark hn hP hS q j

/-- **Inherited corners keep their principal turn** under the refinement `S → insert c S`: the
incoming edge is support-free and the outgoing slot of a true corner of `S` is unchanged. -/
theorem sge_markPrincipalTurn_insert (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (c : Crossing P) (m : Mark P) (hm : IsTrueCorner S m) :
    sge_markPrincipalTurn hn hP (insert c S) m = sge_markPrincipalTurn hn hP S m := by
  unfold sge_markPrincipalTurn
  cases m with
  | inl i => rw [ccpOutSlot_vertex, ccpOutSlot_vertex]
  | inr v =>
    have hv : v.1 ∈ S := hm
    rw [ccpOutSlot_selected hn hP S v hv,
      ccpOutSlot_selected hn hP (insert c S) v (Finset.mem_insert_of_mem hv)]

/-- **The two smoothing corners of a selected crossing cancel** in the real turn ledger: their
principal angles are `∠(d_i, d_j)` and `∠(d_j, d_i)` on a transverse pair. -/
theorem sge_new_turns_cancel (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    sge_markPrincipalTurn hn hP S (Sum.inr v) +
      sge_markPrincipalTurn hn hP S (Sum.inr (visitTwin v)) = 0 := by
  have hdet := ccp_corner_directions_det_ne_zero hn hP S (Sum.inr v) hv
  rw [ccpInEdge_visit, ccpOutSlot_selected hn hP S v hv] at hdet
  have hv' : (visitTwin v).1 ∈ S := by
    rw [visitTwin_crossing]
    exact hv
  unfold sge_markPrincipalTurn
  rw [ccpInEdge_visit, ccpOutSlot_selected hn hP S v hv, ccpInEdge_visit,
    ccpOutSlot_selected hn hP S (visitTwin v) hv', visitTwin_involutive,
    sge_principalAngle_swap hdet]
  ring

/-- The true corners of `insert c S` are those of `S` and the two visits of `c`. -/
theorem sge_isTrueCorner_insert {P : LabelledTuple n} (S : Finset (Crossing P)) (c : Crossing P)
    (v₀ : Visit P) (hv₀ : v₀.1 = c) (m : Mark P) :
    IsTrueCorner (insert c S) m ↔
      IsTrueCorner S m ∨ m = Sum.inr v₀ ∨ m = Sum.inr (visitTwin v₀) := by
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

/-- The corner sets of two distinct carriers are disjoint. -/
theorem sge_cornerSet_disjoint (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) {q r : Component hn hP S} (hqr : q ≠ r) :
    Disjoint (sge_cornerSet hn hP S q) (sge_cornerSet hn hP S r) := by
  rw [Finset.disjoint_left]
  intro m hq hr
  rw [sge_mem_cornerSet] at hq hr
  exact hqr (hq.1.symm.trans hr.1)

/-- **The corner ledger of the split**: the corner marks of the two daughters at `insert c S` are
the corner marks of `A` at `S` together with the two visits of `c`. -/
theorem sge_cornerSet_union (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (A : Component hn hP S) {c : Crossing P}
    (hown0 : ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = A)
    (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂)
    (v₀ : Visit P) (hv₀ : v₀.1 = c) :
    sge_cornerSet hn hP (insert c S) Λ₁ ∪ sge_cornerSet hn hP (insert c S) Λ₂ =
      sge_cornerSet hn hP S A ∪ {Sum.inr v₀, Sum.inr (visitTwin v₀)} := by
  ext m
  rw [Finset.mem_union, Finset.mem_union, sge_mem_cornerSet, sge_mem_cornerSet, sge_mem_cornerSet,
    Finset.mem_insert, Finset.mem_singleton, sge_isTrueCorner_insert S c v₀ hv₀ m, ← or_and_right,
    ← hown m]
  have hA₀ : owner hn hP S (Sum.inr v₀) = A := hown0 v₀ hv₀
  have hA₁ : owner hn hP S (Sum.inr (visitTwin v₀)) = A :=
    hown0 (visitTwin v₀) ((visitTwin_crossing v₀).trans hv₀)
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
theorem sge_cornerSet_disjoint_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (A : Component hn hP S) {c : Crossing P} (hcS : c ∉ S)
    (v₀ : Visit P) (hv₀ : v₀.1 = c) :
    Disjoint (sge_cornerSet hn hP S A) {Sum.inr v₀, Sum.inr (visitTwin v₀)} := by
  rw [Finset.disjoint_left]
  intro m hm hm'
  rw [sge_mem_cornerSet] at hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm'
  rcases hm' with rfl | rfl
  · exact hcS (hv₀ ▸ hm.2)
  · exact hcS (((visitTwin_crossing v₀).trans hv₀) ▸ hm.2)

/-- **eq. cb:singleton-rotations, real form**: `r_A = r_{Λ₁} + r_{Λ₂}` (the two new principal angles
cancel, every inherited corner keeps its principal turn). -/
theorem sge_rotation_add (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hS' : IsDecomposition hn hP (insert c S)) (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hne : Λ₁ ≠ Λ₂)
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    carrierRotation hn hP S A =
      carrierRotation hn hP (insert c S) Λ₁ + carrierRotation hn hP (insert c S) Λ₂ := by
  have hcS : c ∉ S := ((mem_carrierCrossings hn hP S A c).mp hc).1
  have hown0 : ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = A :=
    ((mem_carrierCrossings hn hP S A c).mp hc).2
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  let v₀ : Visit P := ⟨c, i⟩
  have hv₀ : v₀.1 = c := rfl
  have hv₀' : v₀.1 ∈ insert c S := by
    rw [hv₀]
    exact Finset.mem_insert_self c S
  have hvne : (Sum.inr v₀ : Mark P) ≠ Sum.inr (visitTwin v₀) := by
    intro h
    exact visitTwin_ne v₀ (Sum.inr.inj h).symm
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  apply mul_right_cancel₀ h2π
  rw [add_mul, sge_rotation_eq_sum hn hP hS A, sge_rotation_eq_sum hn hP hS' Λ₁,
    sge_rotation_eq_sum hn hP hS' Λ₂,
    ← Finset.sum_union (sge_cornerSet_disjoint hn hP (insert c S) hne),
    sge_cornerSet_union hn hP S A hown0 Λ₁ Λ₂ hown v₀ hv₀,
    Finset.sum_union (sge_cornerSet_disjoint_visits hn hP S A hcS v₀ hv₀),
    Finset.sum_pair hvne, sge_new_turns_cancel hn hP (insert c S) v₀ hv₀', add_zero]
  exact Finset.sum_congr rfl fun m hm =>
    (sge_markPrincipalTurn_insert hn hP S c m ((sge_mem_cornerSet hn hP S A m).mp hm).2).symm

/-- Two nonzero signs agree or are opposite. -/
theorem sge_signType_eq_or_neg {σ τ : SignType} (hσ : σ ≠ 0) (hτ : τ ≠ 0) : σ = τ ∨ σ = -τ := by
  revert hσ hτ
  revert σ τ
  decide

/-- Each daughter owns exactly one visit of `c`: there are visits `w₁, w₂` of `c` with
`owner (insert c S) (inr wᵢ) = Λᵢ`. -/
theorem sge_daughter_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (A : Component hn hP S)
    {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hS' : IsDecomposition hn hP (insert c S)) (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    ∃ w₁ w₂ : Visit P, w₁.1 = c ∧ w₂.1 = c ∧
      owner hn hP (insert c S) (Sum.inr w₁) = Λ₁ ∧ owner hn hP (insert c S) (Sum.inr w₂) = Λ₂ := by
  have hown0 : ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = A :=
    ((mem_carrierCrossings hn hP S A c).mp hc).2
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  let v₀ : Visit P := ⟨c, i⟩
  have hv₀ : v₀.1 = c := rfl
  have hv₁ : (visitTwin v₀).1 = c := (visitTwin_crossing v₀).trans hv₀
  have hv₀' : v₀.1 ∈ insert c S := by
    rw [hv₀]
    exact Finset.mem_insert_self c S
  have h0 := (hown (Sum.inr v₀)).mp (hown0 v₀ hv₀)
  have h1 := (hown (Sum.inr (visitTwin v₀))).mp (hown0 (visitTwin v₀) hv₁)
  have hsep := independent_selected_pair_owners_ne hn hP hS' v₀ hv₀'
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hsep
    · exact ⟨v₀, visitTwin v₀, hv₀, hv₁, h0, h1⟩
  · rcases h1 with h1 | h1
    · exact ⟨visitTwin v₀, v₀, hv₁, hv₀, h1, h0⟩
    · exact absurd (h0.trans h1.symm) hsep

/-- **The signed turn pattern of a daughter.** Every corner of the daughter `Λ` other than its visit
`w` of `c` is a corner of `A` (owned by `A`, a true corner of `S`), hence turns by `τ`; the corner at
`w` turns by `markTurn (inr w) ∈ {τ, −τ}`.  So `Λ` is uniform of sign `τ` or has exactly one dissent. -/
theorem sge_daughter_pattern (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {c : Crossing P} (hS' : IsDecomposition hn hP (insert c S))
    (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂)
    (Λ : Component hn hP (insert c S)) (hΛ : Λ = Λ₁ ∨ Λ = Λ₂)
    (w : Visit P) (hw : w.1 = c) (hwΛ : owner hn hP (insert c S) (Sum.inr w) = Λ)
    (τ : SignType) (hτ0 : τ ≠ 0) (hτ : ∀ j, turn (ccpCornerPolygon hn hP S A) j = τ) :
    (∀ j, turn (ccpCornerPolygon hn hP (insert c S) Λ) j = τ) ∨
      (∃ j₀, turn (ccpCornerPolygon hn hP (insert c S) Λ) j₀ = -τ ∧
        ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP (insert c S) Λ) j = τ) := by
  have hwT : IsTrueCorner (insert c S) (Sum.inr w) := by
    show w.1 ∈ insert c S
    rw [hw]
    exact Finset.mem_insert_self c S
  -- every corner of `Λ` other than `inr w` is an inherited corner of `A`, of turn `τ`
  have hother : ∀ j, ccpCornerMark hn hP (insert c S) Λ j ≠ Sum.inr w →
      turn (ccpCornerPolygon hn hP (insert c S) Λ) j = τ := by
    intro j hj
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS' Λ j]
    have hmΛ : owner hn hP (insert c S) (ccpCornerMark hn hP (insert c S) Λ j) = Λ :=
      ccpCornerMark_owner hn hP _ Λ j
    have hmA : owner hn hP S (ccpCornerMark hn hP (insert c S) Λ j) = A := by
      rw [hown]
      rcases hΛ with rfl | rfl
      · exact Or.inl hmΛ
      · exact Or.inr hmΛ
    have hmT' : IsTrueCorner (insert c S) (ccpCornerMark hn hP (insert c S) Λ j) :=
      ccpCornerMark_isTrueCorner hn hP _ Λ j
    rcases (sge_isTrueCorner_insert S c w hw _).mp hmT' with hT | hmw | hmw
    · obtain ⟨j', hj'⟩ := ccpCornerMark_exists hn hP S A _ hmA hT
      rw [← hj', ← turn_ccpCornerPolygon_eq_markTurn hn hP hS A j']
      exact hτ j'
    · exact absurd hmw hj
    · exfalso
      apply independent_selected_pair_owners_ne hn hP hS' w hwT
      rw [hwΛ, ← hmw]
      exact hmΛ.symm
  -- the corner at `w`
  obtain ⟨j₀, hj₀⟩ := ccpCornerMark_exists hn hP (insert c S) Λ (Sum.inr w) hwΛ hwT
  have hj₀turn : turn (ccpCornerPolygon hn hP (insert c S) Λ) j₀ = markTurn P (Sum.inr w) := by
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS' Λ j₀, hj₀]
  have hw0 : markTurn P (Sum.inr w) ≠ 0 := markTurn_ne_zero hn hP hS' w hwT
  rcases sge_signType_eq_or_neg hw0 hτ0 with h | h
  · left
    intro j
    by_cases hj : ccpCornerMark hn hP (insert c S) Λ j = Sum.inr w
    · have hjj : j = j₀ := ccpCornerMark_injective hn hP _ Λ (hj.trans hj₀.symm)
      rw [hjj, hj₀turn, h]
    · exact hother j hj
  · right
    refine ⟨j₀, by rw [hj₀turn, h], fun j hj => hother j ?_⟩
    intro hj'
    exact hj (ccpCornerMark_injective hn hP _ Λ (hj'.trans hj₀.symm))

/-- lem:uniformrot read at a signed pattern: a regular carrier polygon that is uniform of sign `τ` or
has exactly one dissent `−τ` has its rotation on the ray of `τ` (`uniform_rotation` (i)–(iv)). -/
theorem sge_rotation_ray (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (τ : SignType)
    (h : (∀ j, turn (ccpCornerPolygon hn hP S q) j = τ) ∨
      (∃ j₀, turn (ccpCornerPolygon hn hP S q) j₀ = -τ ∧
        ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP S q) j = τ)) :
    (τ = 1 → 1 ≤ carrierRotation hn hP S q) ∧ (τ = -1 → carrierRotation hn hP S q ≤ -1) := by
  have hreg := ccpCornerPolygon_regular hn hP hS q
  have h3 := ccpCornerCount_ge_three hn hP hS q
  have hnz : ∀ j, turn (ccpCornerPolygon hn hP S q) j ≠ 0 :=
    fun j => ccpCornerPolygon_turn_ne_zero hn hP hS q j
  obtain ⟨h1, h2, h3', h4⟩ := uniform_rotation h3 (ccpCornerPolygon hn hP S q) hreg hnz
  constructor
  · rintro rfl
    rcases h with h | ⟨j₀, hj₀, hoth⟩
    · exact h1 h
    · exact h3' ⟨j₀, hj₀, hoth⟩
  · rintro rfl
    rcases h with h | ⟨j₀, hj₀, hoth⟩
    · exact h2 h
    · refine h4 ⟨j₀, ?_, hoth⟩
      rw [hj₀]
      decide

/-- U103-E (the turn ledger, eq. cb:singleton-rotations).  The two new smoothing corners have opposite
nonzero turns (lem:carriers (ii)); every old corner of `A` lies on exactly one daughter with its old turn;
so one daughter is uniform with `A`'s sign `τ` and the other has exactly one dissent (both have the
SIGNED pattern the floor needs), and the real rotations add (the two new principal angles cancel).
lem:uniformrot (`uniform_rotation`, UniformRotation.lean:63) puts all three integers on the ray of `τ`,
hence `|r_A| = |r_{Λ₁}| + |r_{Λ₂}|`. -/
theorem sg_daughters_rotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (hA : CarrierUniform hn hP S A) {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A)
    (hS' : IsDecomposition hn hP (insert c S)) (Λ₁ Λ₂ : Component hn hP (insert c S))
    (hne : Λ₁ ≠ Λ₂)
    (hown : ∀ m : Mark P, owner hn hP S m = A ↔
      owner hn hP (insert c S) m = Λ₁ ∨ owner hn hP (insert c S) m = Λ₂) :
    SignedUniformOrOneDissent (ccpCornerPolygon hn hP (insert c S) Λ₁) ∧
      SignedUniformOrOneDissent (ccpCornerPolygon hn hP (insert c S) Λ₂) ∧
      carrierRotation hn hP S A =
        carrierRotation hn hP (insert c S) Λ₁ + carrierRotation hn hP (insert c S) Λ₂ ∧
      |carrierRotationInt hn hP S A| =
        |carrierRotationInt hn hP (insert c S) Λ₁| + |carrierRotationInt hn hP (insert c S) Λ₂| := by
  obtain ⟨τ, hτ0, hτ⟩ := hA
  obtain ⟨w₁, w₂, hw₁, hw₂, ho₁, ho₂⟩ := sge_daughter_visits hn hP S A hc hS' Λ₁ Λ₂ hown
  have hp₁ := sge_daughter_pattern hn hP hS A hS' Λ₁ Λ₂ hown Λ₁ (Or.inl rfl) w₁ hw₁ ho₁ τ hτ0 hτ
  have hp₂ := sge_daughter_pattern hn hP hS A hS' Λ₁ Λ₂ hown Λ₂ (Or.inr rfl) w₂ hw₂ ho₂ τ hτ0 hτ
  have hsum := sge_rotation_add hn hP hS A hc hS' Λ₁ Λ₂ hne hown
  refine ⟨⟨τ, hτ0, hp₁⟩, ⟨τ, hτ0, hp₂⟩, hsum, ?_⟩
  -- the integer form: all three rotations lie on the ray of `τ` (lem:uniformrot)
  have hrayA := sge_rotation_ray hn hP hS A τ (Or.inl hτ)
  have hray₁ := sge_rotation_ray hn hP hS' Λ₁ τ hp₁
  have hray₂ := sge_rotation_ray hn hP hS' Λ₂ τ hp₂
  have hcA := carrierRotationInt_cast hn hP hS A
  have hc₁ := carrierRotationInt_cast hn hP hS' Λ₁
  have hc₂ := carrierRotationInt_cast hn hP hS' Λ₂
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [hcA, hc₁, hc₂, hsum]
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · have hA' := hrayA.2 rfl
    have h1' := hray₁.2 rfl
    have h2' := hray₂.2 rfl
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
    ring
  · exact absurd rfl hτ0
  · have hA' := hrayA.1 rfl
    have h1' := hray₁.1 rfl
    have h2' := hray₂.1 rfl
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]

/-! ### Assembly of row 103 (PROVED from the leaves; exactly where `a_floor` enters: twice, at the two
daughters).  Route (FR-CC-3): the printed proof works with the `[z⁰]` rows `f_A = g₁ g₂` and a case
`f_A = 0`; here the full polynomials are nonzero (lp:core) and `mindegAZ_mul` gives eq. cb:singleton-gap
directly: `mindeg_a H⁺_A = mindeg_a H⁺_{Λ₁} + mindeg_a H⁺_{Λ₂} ≥ d_{Λ₁} + d_{Λ₂} = d_A + 2`. -/

/-- eq. cb:singleton-gap in slot form: `d_A = d_{Λ₁} + d_{Λ₂} − 2`. -/
theorem sg_slot_identity (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S S' : Finset (Crossing P)) (A : Component hn hP S) (Λ₁ Λ₂ : Component hn hP S')
    (hm : carrierCrossingCount hn hP S A =
      carrierCrossingCount hn hP S' Λ₁ + carrierCrossingCount hn hP S' Λ₂ + 1)
    (hr : |carrierRotationInt hn hP S A| =
      |carrierRotationInt hn hP S' Λ₁| + |carrierRotationInt hn hP S' Λ₂|) :
    cornerSlot hn hP S A = cornerSlot hn hP S' Λ₁ + cornerSlot hn hP S' Λ₂ - 2 := by
  unfold cornerSlot
  rw [hm, hr]
  push_cast
  ring

/-- **Row 103, conditional on the floor** (library material, D-F11/D-F14 pattern; never mapped). -/
theorem cb_singleton_of_floor (hF : FloorTheoremData) : CbSingletonData := by
  refine ⟨?_⟩
  intro n _ hn P hP S hS A hA c hc hiso
  obtain ⟨hS', Λ₁, Λ₂, hne, hown, hH, hm⟩ := sg_daughters_products hn hP hS A hc hiso
  obtain ⟨hu₁, hu₂, -, hr⟩ := sg_daughters_rotation hn hP hS A hA hc hS' Λ₁ Λ₂ hne hown
  -- thm:floor at the two daughters (their turn patterns are the ones it requires)
  have hf₁ := hF.slot_le_of_signed hn P hP (insert c S) hS' Λ₁ hu₁
  have hf₂ := hF.slot_le_of_signed hn P hP (insert c S) hS' Λ₂ hu₂
  have hslot := sg_slot_identity hn hP S (insert c S) A Λ₁ Λ₂ hm hr
  -- the coefficient at `d_A` lies strictly below the summed floor
  rw [cornerCoefficient_eq_coeffAt, hH]
  exact coeffAt_mul_eq_zero_of_lt_floor (cornerHomfly_ne_zero hn hP _ Λ₁ hS')
    (cornerHomfly_ne_zero hn hP _ Λ₂ hS') hf₁ hf₂ (by omega)

end Singleton

/-! ## §3 Row 105 lem:corner-values (sm-3:4801-4809; proof 4810-4820) -/

section CornerValues

variable {n : ℕ} [NeZero n]

/-- **lem:corner-values as printed**, one field per printed clause, `Q` a subpolygon of the decomposition
`S` of the generic `P` (def:C's binder), `m_Q = carrierCrossingCount`, `r_Q = carrierRotation` (def:uniform's
REAL `rot(Q)`, FR-CC-5), `d_Q = cornerSlot`, `c(Q) = cornerCoefficient`.
(i) "If `Q` is uniform and embedded (`m_Q = 0`) then `|r_Q| = 1`, `d_Q = 0` and `c(Q) = 1`": hypothesis
`m_Q = 0` (the printed parenthetical DEFINES embedded, FR-CC-4; embeddedness of the corner polygon in row
104's sense is a THEOREM, `cvl_embedded_of_no_crossings`); the three printed conclusions.
(ii) "If `Q` is uniform and `{y}` is a crossing of `Q` interlacing no other crossing of `Q`, then
`c(Q) = 0`" — the clause of cb:singleton with `(Q, y)` for `(A, c)` (FR-CC-6). -/
structure CornerValuesData : Prop where
  embedded_value : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniform hn hP S q → carrierCrossingCount hn hP S q = 0 →
      |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1
  isolated_zero : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniform hn hP S q →
    ∀ y ∈ carrierCrossings hn hP S q,
      (∀ y' ∈ carrierCrossings hn hP S q, y' ≠ y → ¬ Interlaces hn hP y y') →
      cornerCoefficient hn hP S q hS = 0

/-! ### Row 105 (i) — UNCONDITIONAL, PROVED (grafted from Sketch_A; no floor, no leaf).  Prefix `cvl_`. -/

/-- `m_Q = 0` ⇒ the corner polygon is an embedded polygon in the sense of row 104 (`Embedded`: nonzero
edges, remote edges disjoint, consecutive edges meet in the shared corner): lem:carriers (ii) and the
accepted `nonadjacent_meet_crossing` (LinkPositiveLift.lean:520), `consecutive_meet` (:698). -/
theorem cvl_embedded_of_no_crossings (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (h0 : carrierCrossings hn hP S q = ∅) : Embedded (ccpCornerPolygon hn hP S q) := by
  refine ⟨fun j => ((carriers_lemma hn hP hS).corner_polygons.2.1 q j).1, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨c, hc, -⟩ := nonadjacent_meet_crossing hn hP S q hS hij hxi hxj
    rw [h0] at hc
    exact Finset.notMem_empty _ hc
  · intro i
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      exact consecutive_meet hn hP S q hS i hx hx'
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨1, by norm_num, le_refl 1, (edgePoint_one _ _).symm⟩,
        ⟨0, le_refl 0, by norm_num, (edgePoint_zero _ _).symm⟩⟩

/-- (i) unconditionally: `|r_Q| = 1` by cb:embedded-rotation (EmbeddedRotation.lean:1081) on the embedded
regular corner polygon (`≥ 3` corners by lem:carriers (ii)), `d_Q = 1 − 0 − 1 = 0`, `c(Q) = [a⁰z⁰] 1 = 1`
by lp:core's `P_○ = 1` on the crossing-free positive lift (`positiveLift_isCrossingFreeCircle`,
LinkPositiveLift.lean:833; `P_circle`, `P_eq_homfly`, `coeffAt_one`).  The hypothesis "uniform" is unused
(FR-CC-4, kept literally). -/
theorem corner_values_i (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (_hu : CarrierUniform hn hP S q) (hm : carrierCrossingCount hn hP S q = 0) :
    |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1 := by
  have h0 : carrierCrossings hn hP S q = ∅ := Finset.card_eq_zero.mp hm
  have hreg : Regular (ccpCornerPolygon hn hP S q) := ccpCornerPolygon_regular hn hP hS q
  have h3 : 3 ≤ ccpCornerCount hn hP S q := (carriers_lemma hn hP hS).corner_polygons.2.2.1 q
  have hpm := (cb_embedded_rotation h3 (ccpCornerPolygon hn hP S q) hreg
    (cvl_embedded_of_no_crossings hn hP hS q h0)).pm_one
  have hrot : |carrierRotation hn hP S q| = 1 := by
    unfold carrierRotation; rcases hpm with h | h <;> rw [h] <;> simp
  have hrotZ : |carrierRotationInt hn hP S q| = 1 := by
    have := carrierRotationInt_cast hn hP hS q
    have h' : |((carrierRotationInt hn hP S q : ℤ) : ℝ)| = 1 := by rw [this]; exact hrot
    exact_mod_cast h'
  refine ⟨hrot, ?_, ?_⟩
  · simp only [cornerSlot, hm, hrotZ]; ring
  · have hslot : cornerSlot hn hP S q = 0 := by simp only [cornerSlot, hm, hrotZ]; ring
    rw [cornerCoefficient_eq_coeffAt, hslot]
    show coeffAt 0 0 (homfly _) = 1
    rw [← P_eq_homfly, P_circle (positiveLift_isCrossingFreeCircle hn hP S q hS h0), coeffAt_one]
    simp

/-- Companion: (i)'s rotation clause for def:C's integer `r_Q` (`carrierRotationInt_cast`). -/
theorem CornerValuesData.embedded_rotationInt (hD : CornerValuesData) (hn : 3 ≤ n)
    {P : LabelledTuple n} (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hu : CarrierUniform hn hP S q) (hm : carrierCrossingCount hn hP S q = 0) :
    |carrierRotationInt hn hP S q| = 1 := by
  have hrot := (hD.embedded_value n hn P hP S hS q hu hm).1
  have h' : |((carrierRotationInt hn hP S q : ℤ) : ℝ)| = 1 := by
    rw [carrierRotationInt_cast hn hP hS q]; exact hrot
  exact_mod_cast h'

/-- **Row 105 from row 103** ((ii) is cb:singleton at `(Q, y)`; (i) needs no floor). -/
theorem corner_values_of_singleton (h : CbSingletonData) : CornerValuesData where
  embedded_value := fun _ _ hn _ hP _ hS q hu h0 => corner_values_i hn hP hS q hu h0
  isolated_zero := fun n _ hn P hP S hS q hu y hy hiso => h.isolated_zero n hn P hP S hS q hu y hy hiso

/-- **Row 105, conditional on the floor** (library material). -/
theorem corner_values_of_floor (hF : FloorTheoremData) : CornerValuesData :=
  corner_values_of_singleton (cb_singleton_of_floor hF)

end CornerValues

/-! ## §4 Row 110 thm:C-S7 (sm-4:267-274; proof 275-908) — fixed target name `SM.thm_C_S7` -/

section VertexEdge

variable {n : ℕ} [NeZero n]

/-- **thm:C-S7 as printed**, one field: "At a simple vertex–edge wall at `(M; a)`, of bigon or sliding
type, with halves `λ₁, λ₂` (def:deletion-halves) and contact sign `s = χ_{a,a+1,M}(P₋)`,
`C(P₊) − C(P₋) = s C(λ₁) C(λ₂)`."  Shape of the accepted thm:A-S7 / cor:A-lawful `vertex_edge_law`
(SM/ALawful.lean:102) and of the consumer thm:uniqueness (c) (`UniquenessHypotheses.vertex_edge`,
SM/Uniqueness.lean:57): the wall is `g : WallGerm n` with `h : g.VertexEdgeAt M a` (def:walls (V));
"of bigon or sliding type" is the exhaustive dichotomy `vertexEdge_bigon_or_sliding`
(NamedWallPredicates.lean:46; FR-CC-7, no hypothesis); `s = g.contactSign M a` (`χ_{a,a+1,M}` on the
negative side, constant there: `contactSign_eq_at`, `vertex_contact_signs`, NamedWallSides.lean:58-69;
FR-CC-8); the halves are `firstHalf/secondHalf g.center M a`, generic by lem:children (ii)
(`vertex_halves_children`) — the genericity proofs are quantified (proof-irrelevant; FR-CC-9); `P₊`, `P₋`
are read at every pair of side parameters (the accepted C-row convention of prop:C-silent / hyp:R,
equivalent to def:germ's chamber values by prop:C-chamber). -/
structure CS7Data : Prop where
  vertex_edge_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.VertexEdgeAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)),
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property -
          cornerStateSum hn (g.sideTuple false tm).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂)

/-- Companion (the printed "of bigon type" reading): the law at a wall of bigon type. -/
theorem CS7Data.bigon (hD : CS7Data) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (tp tm : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true tp).property -
        cornerStateSum hn (g.sideTuple false tm).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) :=
  hD.vertex_edge_law n hn g M a h.1 h₁ h₂ tp tm

/-- Companion (the printed "of sliding type" reading): the law at a wall of sliding type. -/
theorem CS7Data.sliding (hD : CS7Data) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (tp tm : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true tp).property -
        cornerStateSum hn (g.sideTuple false tm).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) :=
  hD.vertex_edge_law n hn g M a h.1 h₁ h₂ tp tm

/-- Sanity (FR-CC-8): the contact sign in the bundle IS `χ_{a,a+1,M}` evaluated on `P₋`, at the very
parameter `tm` of the `C(P₋)` term (accepted `contactSign_eq_at`). -/
theorem CS7Data.contactSign_literal (g : WallGerm n) (M a : ZMod n) (tm : g.SideParameter) :
    (g.contactSign M a : ℤ) = ((chi (g.sideTuple false tm).val a (a + 1) M : SignType) : ℤ) := by
  rw [g.contactSign_eq_at M a tm]

/-! ### Leaves of row 110 (units U110-A … U110-K of PLAN_FINAL.md §4). Prefix `s7_`.
The two branch laws are stated at ONE side parameter below a radius; the row theorem moves both side
parameters there by chamber constancy along a side (`cornerStateSum_side_eq`, accepted SM/HypR.lean:119). -/

/-! ### U110-A helpers (prefix `s7a_`): the contact-wall partial mark transport on persistent marks -/

/-- A mark is *persistent* at the contact `(M; a)` when it is an original vertex or a visit of a
crossing other than the two contact pairs `{a, M−1}`, `{a, M}` (`ContactAffected`). -/
def s7a_Persistent (M a : ZMod n) {P : LabelledTuple n} : Mark P → Prop
  | Sum.inl _ => True
  | Sum.inr v => ¬ ContactAffected M a v.1.val

omit [NeZero n] in
@[simp] theorem s7a_persistent_inl (M a : ZMod n) {P : LabelledTuple n} (i : ZMod n) :
    s7a_Persistent M a (Sum.inl i : Mark P) := trivial

omit [NeZero n] in
@[simp] theorem s7a_persistent_inr (M a : ZMod n) {P : LabelledTuple n} (v : Visit P) :
    s7a_Persistent M a (Sum.inr v) ↔ ¬ ContactAffected M a v.1.val := Iff.rfl

section Transport

variable {P Q : LabelledTuple n} {M a : ZMod n}

omit [NeZero n] in
/-- The transported persistent visit: same crossing support, same edge label
(the visit-level content of the accepted `contactVisitTransport`). -/
def s7a_visit (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) : Visit Q :=
  ⟨⟨v.1.val, (hs _ hv).mpr v.1.property⟩, v.2⟩

omit [NeZero n] in
theorem s7a_visit_support (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    (s7a_visit hs v hv).1.val = v.1.val := rfl

omit [NeZero n] in
theorem s7a_visit_edge (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    (s7a_visit hs v hv).2.val = v.2.val := rfl

omit [NeZero n] in
theorem s7a_visit_eq_contactVisitTransport
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    s7a_visit hs v hv = (contactVisitTransport hs ⟨v, hv⟩).val := rfl

omit [NeZero n] in
theorem s7a_visit_not_affected
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    ¬ ContactAffected M a (s7a_visit hs v hv).1.val := hv

omit [NeZero n] in
theorem s7a_visit_injective
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val) (hw : ¬ ContactAffected M a w.1.val)
    (h : s7a_visit hs v hv = s7a_visit hs w hw) : v = w := by
  have h1 : (⟨v, hv⟩ : PersistentContactVisit P M a) = ⟨w, hw⟩ :=
    (contactVisitTransport hs).injective (Subtype.ext h)
  exact congrArg Subtype.val h1

omit [NeZero n] in
theorem s7a_visit_surjective
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (w : Visit Q) (hw : ¬ ContactAffected M a w.1.val) :
    ∃ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val), s7a_visit hs v hv = w := by
  obtain ⟨v, hv⟩ := (contactVisitTransport hs).surjective ⟨w, hw⟩
  exact ⟨v.1, v.2, congrArg Subtype.val hv⟩

omit [NeZero n] in
/-- Two visits with the same crossing and the same edge label are equal. -/
theorem s7a_visit_ext {P : LabelledTuple n} (v w : Visit P) (hc : v.1 = w.1)
    (he : v.2.val = w.2.val) : v = w := by
  rcases v with ⟨c, i⟩
  rcases w with ⟨d, j⟩
  dsimp only at hc he
  subst hc
  exact congrArg (fun k : {k // k ∈ c.val} => (⟨c, k⟩ : Visit P)) (Subtype.ext he)

omit [NeZero n] in
/-- The twin is carried (same crossing, different edge). -/
theorem s7a_visit_twin (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    s7a_visit hs (visitTwin v) hv = visitTwin (s7a_visit hs v hv) := by
  apply visitTwin_unique
  · rfl
  · intro h
    have he : (visitTwin v).2.val = v.2.val := congrArg (fun w : Visit Q => w.2.val) h
    exact visitTwin_ne v (s7a_visit_ext _ _ (visitTwin_crossing v) he)

omit [NeZero n] in
/-- The total mark map: vertices fixed, persistent visits transported, the (never used) contact
visits sent to the vertex `0`. -/
def s7a_markMap (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)) :
    Mark P → Mark Q
  | Sum.inl i => Sum.inl i
  | Sum.inr v => if hv : ContactAffected M a v.1.val then Sum.inl 0 else Sum.inr (s7a_visit hs v hv)

omit [NeZero n] in
@[simp] theorem s7a_markMap_inl (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (i : ZMod n) : s7a_markMap hs (Sum.inl i) = Sum.inl i := rfl

omit [NeZero n] in
theorem s7a_markMap_inr (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    s7a_markMap hs (Sum.inr v) = Sum.inr (s7a_visit hs v hv) := by
  show (if hv' : ContactAffected M a v.1.val then (Sum.inl 0 : Mark Q)
    else Sum.inr (s7a_visit hs v hv')) = _
  rw [dite_eq_right hv]

omit [NeZero n] in
theorem s7a_markMap_persistent
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (m : Mark P) (hm : s7a_Persistent M a m) : s7a_Persistent M a (s7a_markMap hs m) := by
  cases m with
  | inl i => trivial
  | inr v =>
    rw [s7a_markMap_inr hs v hm]
    exact hm

omit [NeZero n] in
theorem s7a_markMap_injOn
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (m m' : Mark P) (hm : s7a_Persistent M a m) (hm' : s7a_Persistent M a m')
    (h : s7a_markMap hs m = s7a_markMap hs m') : m = m' := by
  cases m with
  | inl i =>
    cases m' with
    | inl j => exact congrArg Sum.inl (Sum.inl_injective h)
    | inr w =>
      rw [s7a_markMap_inr hs w hm'] at h
      exact absurd h Sum.inl_ne_inr
  | inr v =>
    cases m' with
    | inl j =>
      rw [s7a_markMap_inr hs v hm] at h
      exact absurd h Sum.inr_ne_inl
    | inr w =>
      rw [s7a_markMap_inr hs v hm, s7a_markMap_inr hs w hm'] at h
      exact congrArg Sum.inr (s7a_visit_injective hs v w hm hm' (Sum.inr_injective h))

omit [NeZero n] in
theorem s7a_markMap_surjOn
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (m' : Mark Q) (hm' : s7a_Persistent M a m') :
    ∃ m : Mark P, s7a_Persistent M a m ∧ s7a_markMap hs m = m' := by
  cases m' with
  | inl i => exact ⟨Sum.inl i, trivial, rfl⟩
  | inr w =>
    obtain ⟨v, hv, hvw⟩ := s7a_visit_surjective hs w hm'
    exact ⟨Sum.inr v, hv, by rw [s7a_markMap_inr hs v hv, hvw]⟩

/-- The mark map commutes with the selected-mark exchange for a persistent support (the twin is
carried, membership in the transported support is membership in the support). -/
theorem s7a_markMap_selectedMarkPerm
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (S : Finset (Crossing P)) (S' : Finset (Crossing Q))
    (hSS' : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      (s7a_visit hs v hv).1 ∈ S' ↔ v.1 ∈ S)
    (m : Mark P) (hm : s7a_Persistent M a m) :
    selectedMarkPerm S' (s7a_markMap hs m) = s7a_markMap hs (selectedMarkPerm S m) := by
  cases m with
  | inl i => rfl
  | inr v =>
    have hv0 : ¬ ContactAffected M a v.1.val := hm
    rw [s7a_markMap_inr hs v hv0, selectedMarkPerm_visit, selectedMarkPerm_visit]
    by_cases hv : v.1 ∈ S
    · have hm' : ¬ ContactAffected M a (visitTwin v).1.val := hv0
      rw [selectedVisitTwin_of_mem _ _ hv, selectedVisitTwin_of_mem _ _ ((hSS' v hv0).mpr hv),
        s7a_markMap_inr hs _ hm']
      exact congrArg Sum.inr (s7a_visit_twin hs v hv0).symm
    · rw [selectedVisitTwin_of_not_mem _ _ hv,
        selectedVisitTwin_of_not_mem _ _ (fun h => hv ((hSS' v hv0).mp h)), s7a_markMap_inr hs v hv0]

/-! #### Key order and the filtered sorted mark list -/

/-- The mark order among persistent marks is carried, given the same-edge parameter order of
persistent visits (vertex/vertex by label, vertex/visit by label and strict interiority,
visit/visit by label or by the parameter hypothesis) — the persistent analogue of
`Carrier.markKey_lt_transport`. -/
theorem s7a_markKey_lt (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hpar : ∀ (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit hs v hv) < visitParameter (s7a_visit hs w hw) ↔
        visitParameter v < visitParameter w))
    (m m' : Mark P) (hm : s7a_Persistent M a m) (hm' : s7a_Persistent M a m') :
    markKey hn hQ.1 (s7a_markMap hs m) < markKey hn hQ.1 (s7a_markMap hs m') ↔
      markKey hn hP.1 m < markKey hn hP.1 m' := by
  cases m with
  | inl i =>
    cases m' with
    | inl j => simp only [s7a_markMap_inl, markKey_vertex]
    | inr w =>
      rw [s7a_markMap_inl, s7a_markMap_inr hs w hm']
      unfold markKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (i.val < w.2.val.val ∨ i = w.2.val ∧ (0 : ℝ) < visitParameter (s7a_visit hs w hm')) ↔
        (i.val < w.2.val.val ∨ i = w.2.val ∧ (0 : ℝ) < visitParameter w)
      exact or_congr Iff.rfl (and_congr_right fun _ => iff_of_true
        (visitPosition_interior hn hQ.1 _).1 (visitPosition_interior hn hP.1 w).1)
  | inr v =>
    cases m' with
    | inl j =>
      rw [s7a_markMap_inl, s7a_markMap_inr hs v hm]
      unfold markKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < j.val ∨ v.2.val = j ∧ visitParameter (s7a_visit hs v hm) < (0 : ℝ)) ↔
        (v.2.val.val < j.val ∨ v.2.val = j ∧ visitParameter v < (0 : ℝ))
      exact or_congr Iff.rfl (and_congr_right fun _ => iff_of_false
        (not_lt.mpr (visitPosition_interior hn hQ.1 _).1.le)
        (not_lt.mpr (visitPosition_interior hn hP.1 v).1.le))
    | inr w =>
      rw [s7a_markMap_inr hs v hm, s7a_markMap_inr hs w hm']
      unfold markKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧
          visitParameter (s7a_visit hs v hm) < visitParameter (s7a_visit hs w hm')) ↔
        (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧ visitParameter v < visitParameter w)
      exact or_congr Iff.rfl (and_congr_right fun he => hpar v w hm hm' he)

/-- The sorted mark list of `Q`, restricted to persistent marks, is literally the transported
restricted sorted mark list of `P` (`List.Perm.eq_of_pairwise`: both are strictly key-sorted lists of
the same members). -/
theorem s7a_markList_filter (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hpar : ∀ (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit hs v hv) < visitParameter (s7a_visit hs w hw) ↔
        visitParameter v < visitParameter w)) :
    (markList hn hQ).filter (fun m => decide (s7a_Persistent M a m)) =
      ((markList hn hP).filter (fun m => decide (s7a_Persistent M a m))).map (s7a_markMap hs) := by
  have hmemP : ∀ m : Mark P, m ∈ (markList hn hP).filter (fun m => decide (s7a_Persistent M a m)) ↔
      s7a_Persistent M a m := by
    intro m
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_markList hn hP m, h⟩⟩
  have hmemQ : ∀ m : Mark Q, m ∈ (markList hn hQ).filter (fun m => decide (s7a_Persistent M a m)) ↔
      s7a_Persistent M a m := by
    intro m
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_markList hn hQ m, h⟩⟩
  have hnodP : ((markList hn hP).filter (fun m => decide (s7a_Persistent M a m))).Nodup :=
    (markList_nodup hn hP).filter _
  have hnodQ : ((markList hn hQ).filter (fun m => decide (s7a_Persistent M a m))).Nodup :=
    (markList_nodup hn hQ).filter _
  have hnodmap : (((markList hn hP).filter (fun m => decide (s7a_Persistent M a m))).map
      (s7a_markMap hs)).Nodup := by
    refine hnodP.map_on ?_
    intro m hm m' hm' h
    exact s7a_markMap_injOn hs m m' ((hmemP m).mp hm) ((hmemP m').mp hm') h
  apply List.Perm.eq_of_pairwise (le := fun a b => markKey hn hQ.1 a ≤ markKey hn hQ.1 b)
  · intro a b _ _ hab hba
    exact markKey_injective hn hQ (le_antisymm hab hba)
  · exact (markList_sorted hn hQ).filter _
  · rw [List.pairwise_map]
    refine ((markList_sorted hn hP).filter _).imp_of_mem ?_
    intro a b ha hb h
    rw [← not_lt] at h ⊢
    intro h'
    exact h ((s7a_markKey_lt hn hP hQ hs hpar b a ((hmemP b).mp hb) ((hmemP a).mp ha)).mp h')
  · apply (List.perm_ext_iff_of_nodup hnodQ hnodmap).mpr
    intro m'
    rw [hmemQ, List.mem_map]
    constructor
    · intro h
      obtain ⟨m, hm, rfl⟩ := s7a_markMap_surjOn hs m' h
      exact ⟨m, (hmemP m).mpr hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact s7a_markMap_persistent hs m ((hmemP m).mp hm)

end Transport

/-! #### Circular order of marks (helpers on `traversalBetween`) -/

section Cyclic

variable {P : LabelledTuple n}

omit [NeZero n] in
theorem s7a_cyc_or (x y z : ℝ) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ((x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y)) ∨
      ((x < z ∧ z < y) ∨ (z < y ∧ y < x) ∨ (y < x ∧ x < z)) := by
  rcases lt_trichotomy x y with h1 | h1 | h1
  · rcases lt_trichotomy y z with h2 | h2 | h2
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · exact absurd h2 hyz
    · rcases lt_trichotomy x z with h3 | h3 | h3
      · exact Or.inr (Or.inl ⟨h3, h2⟩)
      · exact absurd h3 hxz
      · exact Or.inl (Or.inr (Or.inr ⟨h3, h1⟩))
  · exact absurd h1 hxy
  · rcases lt_trichotomy y z with h2 | h2 | h2
    · rcases lt_trichotomy x z with h3 | h3 | h3
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h3⟩))
      · exact absurd h3 hxz
      · exact Or.inl (Or.inr (Or.inl ⟨h2, h3⟩))
    · exact absurd h2 hyz
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))

/-- Three distinct marks are cyclically ordered one way or the other. -/
theorem s7a_between_or (hn : 3 ≤ n) (hP : Generic P) (p q r : Mark P) (hpq : p ≠ q) (hqr : q ≠ r)
    (hpr : p ≠ r) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r) ∨
      traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 r) (markPosition hn hP.1 q) := by
  have hk : ∀ u w : Mark P, u ≠ w →
      traversalKey (markPosition hn hP.1 u) ≠ traversalKey (markPosition hn hP.1 w) :=
    fun u w h he => h (markKey_injective hn hP he)
  exact s7a_cyc_or _ _ _ (hk p q hpq) (hk q r hqr) (hk p r hpr)

theorem s7a_between_trans (hn : 3 ≤ n) (hP : Generic P) {p q r s : Mark P}
    (h1 : traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r))
    (h2 : traversalBetween (markPosition hn hP.1 q) (markPosition hn hP.1 s) (markPosition hn hP.1 r)) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 s) (markPosition hn hP.1 r) := by
  let _inst : CircularOrder (TraversalPoint n) := traversalCircularOrder
  exact (traversalBetween_eq_circular _ _ _).mpr
    (sbtw_trans_left ((traversalBetween_eq_circular _ _ _).mp h1) ((traversalBetween_eq_circular _ _ _).mp h2))

theorem s7a_between_asymm (hn : 3 ≤ n) (hP : Generic P) {p q r : Mark P}
    (h1 : traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r))
    (h2 : traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 r) (markPosition hn hP.1 q)) :
    False := by
  let _inst : CircularOrder (TraversalPoint n) := traversalCircularOrder
  exact sbtw_asymm ((traversalBetween_eq_circular _ _ _).mp h1)
    (sbtw_cyclic_left ((traversalBetween_eq_circular _ _ _).mp h2))

omit [NeZero n] in
theorem s7a_between_ne (hn : 3 ≤ n) (hP : Generic P) {p q r : Mark P}
    (h : traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r)) :
    p ≠ q ∧ q ≠ r ∧ p ≠ r := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

end Cyclic

/-! #### The contracted successor (first return to the persistent marks) -/

section Contract

variable {P : LabelledTuple n} {M a : ZMod n}

/-- The persistent marks of `P`. -/
abbrev s7a_PMark (M a : ZMod n) (P : LabelledTuple n) := {m : Mark P // s7a_Persistent M a m}

variable (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))

theorem s7a_exists_return (m : Mark P) (hm : s7a_Persistent M a m) :
    ∃ j : ℕ, 0 < j ∧ s7a_Persistent M a ((smoothingSuccessor hn hP S ^ j) m) :=
  ⟨orderOf (smoothingSuccessor hn hP S), orderOf_pos _, by
    rw [pow_orderOf_eq_one, Equiv.Perm.one_apply]; exact hm⟩

/-- The first return time of the smoothing successor to the persistent marks. -/
def s7a_returnTime (m : Mark P) (hm : s7a_Persistent M a m) : ℕ :=
  Nat.find (s7a_exists_return hn hP S m hm)

theorem s7a_returnTime_pos (m : Mark P) (hm : s7a_Persistent M a m) :
    0 < s7a_returnTime hn hP S m hm :=
  (Nat.find_spec (s7a_exists_return hn hP S m hm)).1

theorem s7a_returnTime_persistent (m : Mark P) (hm : s7a_Persistent M a m) :
    s7a_Persistent M a ((smoothingSuccessor hn hP S ^ s7a_returnTime hn hP S m hm) m) :=
  (Nat.find_spec (s7a_exists_return hn hP S m hm)).2

theorem s7a_returnTime_min (m : Mark P) (hm : s7a_Persistent M a m) (i : ℕ) (hi : 0 < i)
    (hlt : i < s7a_returnTime hn hP S m hm) :
    ¬ s7a_Persistent M a ((smoothingSuccessor hn hP S ^ i) m) := by
  intro h
  exact absurd (Nat.find_min' (s7a_exists_return hn hP S m hm) ⟨hi, h⟩) (not_le.mpr hlt)

/-- The contracted successor on persistent marks. -/
def s7a_step (x : s7a_PMark M a P) : s7a_PMark M a P :=
  ⟨(smoothingSuccessor hn hP S ^ s7a_returnTime hn hP S x.1 x.2) x.1,
    s7a_returnTime_persistent hn hP S x.1 x.2⟩

theorem s7a_step_val (x : s7a_PMark M a P) :
    (s7a_step hn hP S x).1 = (smoothingSuccessor hn hP S ^ s7a_returnTime hn hP S x.1 x.2) x.1 := rfl

theorem s7a_step_inj_aux (x y : s7a_PMark M a P)
    (hle : s7a_returnTime hn hP S x.1 x.2 ≤ s7a_returnTime hn hP S y.1 y.2)
    (h : s7a_step hn hP S x = s7a_step hn hP S y) : x = y := by
  set f := smoothingSuccessor hn hP S with hf
  set i := s7a_returnTime hn hP S x.1 x.2 with hi
  set j := s7a_returnTime hn hP S y.1 y.2 with hj
  have h1 : (f ^ i) x.1 = (f ^ j) y.1 := congrArg Subtype.val h
  have h2 : (f ^ j) y.1 = (f ^ i) ((f ^ (j - i)) y.1) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
  have h3 : (f ^ (j - i)) y.1 = x.1 := (f ^ i).injective (h2.symm.trans h1.symm)
  by_cases hji : j - i = 0
  · have hij : i = j := by omega
    apply Subtype.ext
    exact (f ^ i).injective (h1.trans (by rw [hij]))
  · exfalso
    have hpos : 0 < j - i := Nat.pos_of_ne_zero hji
    have hlt : j - i < j := Nat.sub_lt_self (s7a_returnTime_pos hn hP S x.1 x.2) hle
    exact s7a_returnTime_min hn hP S y.1 y.2 (j - i) hpos hlt (h3 ▸ x.2)

theorem s7a_step_injective : Function.Injective (s7a_step hn hP S (M := M) (a := a)) := by
  intro x y h
  rcases le_total (s7a_returnTime hn hP S x.1 x.2) (s7a_returnTime hn hP S y.1 y.2) with hle | hle
  · exact s7a_step_inj_aux hn hP S x y hle h
  · exact (s7a_step_inj_aux hn hP S y x hle h.symm).symm

/-- The contracted successor as a permutation of the persistent marks. -/
def s7a_stepPerm : Equiv.Perm (s7a_PMark M a P) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (s7a_step_injective hn hP S))

theorem s7a_stepPerm_apply (x : s7a_PMark M a P) : s7a_stepPerm hn hP S x = s7a_step hn hP S x := rfl

theorem s7a_sameCycle_step (x : s7a_PMark M a P) :
    (smoothingSuccessor hn hP S).SameCycle x.1 (s7a_step hn hP S x).1 :=
  ⟨(s7a_returnTime hn hP S x.1 x.2 : ℤ), by rw [zpow_natCast]; rfl⟩

theorem s7a_sameCycle_of_stepPerm (x y : s7a_PMark M a P)
    (h : (s7a_stepPerm hn hP S).SameCycle x y) : (smoothingSuccessor hn hP S).SameCycle x.1 y.1 := by
  obtain ⟨k, _, hk⟩ := h.exists_pow_eq'
  have hpow : ∀ (m : ℕ) (z : s7a_PMark M a P),
      (smoothingSuccessor hn hP S).SameCycle z.1 (((s7a_stepPerm hn hP S) ^ m) z).1 := by
    intro m
    induction m with
    | zero => intro z; simp only [pow_zero, Equiv.Perm.one_apply]; exact Equiv.Perm.SameCycle.refl _ _
    | succ m ih =>
      intro z
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (ih z).trans (s7a_sameCycle_step hn hP S _)
  rw [← hk]
  exact hpow k x

theorem s7a_stepPerm_of_sameCycle (x y : s7a_PMark M a P)
    (h : (smoothingSuccessor hn hP S).SameCycle x.1 y.1) : (s7a_stepPerm hn hP S).SameCycle x y := by
  obtain ⟨k, _, hk⟩ := h.exists_pow_eq'
  set f := smoothingSuccessor hn hP S with hf
  have key : ∀ k : ℕ, ∀ x y : s7a_PMark M a P, (f ^ k) x.1 = y.1 →
      (s7a_stepPerm hn hP S).SameCycle x y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x y hk
      by_cases hk0 : k = 0
      · subst hk0
        simp only [pow_zero, Equiv.Perm.one_apply] at hk
        rw [Subtype.ext hk]
      · set r := s7a_returnTime hn hP S x.1 x.2 with hr
        have hrpos : 0 < r := s7a_returnTime_pos hn hP S x.1 x.2
        by_cases hrk : r ≤ k
        · have h1 : (f ^ (k - r)) (s7a_step hn hP S x).1 = y.1 := by
            rw [s7a_step_val, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hrk, hk]
          have h2 := ih (k - r) (Nat.sub_lt (Nat.pos_of_ne_zero hk0) hrpos) (s7a_step hn hP S x) y h1
          have h3 : (s7a_stepPerm hn hP S).SameCycle x (s7a_step hn hP S x) :=
            Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
          exact h3.trans h2
        · exfalso
          exact s7a_returnTime_min hn hP S x.1 x.2 k (Nat.pos_of_ne_zero hk0) (not_le.mp hrk) (hk ▸ y.2)
  exact key k x y hk

theorem s7a_sameCycle_stepPerm_iff (x y : s7a_PMark M a P) :
    (smoothingSuccessor hn hP S).SameCycle x.1 y.1 ↔ (s7a_stepPerm hn hP S).SameCycle x y :=
  ⟨s7a_stepPerm_of_sameCycle hn hP S x y, s7a_sameCycle_of_stepPerm hn hP S x y⟩

/-- Every carrier of a persistent support has a persistent mark (a true corner:
`component_has_trueCorner`). -/
theorem s7a_component_has_persistent (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val)
    (q : Component hn hP S) : ∃ m : Mark P, owner hn hP S m = q ∧ s7a_Persistent M a m := by
  obtain ⟨m, hm, hc⟩ := component_has_trueCorner hn hP S q
  refine ⟨m, hm, ?_⟩
  cases m with
  | inl i => trivial
  | inr v => exact hSp v.1 hc

/-- The carriers of a persistent support are the cycles of the contracted successor. -/
def s7a_componentEquivQuot (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) :
    Component hn hP S ≃ Quotient (Equiv.Perm.SameCycle.setoid (s7a_stepPerm hn hP S (M := M) (a := a))) :=
  (Equiv.ofBijective
    (Quotient.lift (fun x : s7a_PMark M a P => owner hn hP S x.1)
      (fun x y h => (owner_eq_iff hn hP S x.1 y.1).mpr ((s7a_sameCycle_stepPerm_iff hn hP S x y).mpr h)))
    (by
      constructor
      · intro u v huv
        induction u using Quotient.inductionOn with
        | h x =>
          induction v using Quotient.inductionOn with
          | h y =>
            apply Quotient.sound
            exact (s7a_sameCycle_stepPerm_iff hn hP S x y).mp
              ((owner_eq_iff hn hP S x.1 y.1).mp huv)
      · intro q
        obtain ⟨m, hm, hmp⟩ := s7a_component_has_persistent hn hP S hSp q
        exact ⟨Quotient.mk _ ⟨m, hmp⟩, hm⟩)).symm

theorem s7a_componentEquivQuot_owner (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val)
    (m : Mark P) (hm : s7a_Persistent M a m) :
    s7a_componentEquivQuot hn hP S hSp (owner hn hP S m) =
      Quotient.mk _ (⟨m, hm⟩ : s7a_PMark M a P) := by
  unfold s7a_componentEquivQuot
  exact Equiv.symm_apply_eq _ |>.mpr rfl

end Contract

/-! #### The order characterization of the contracted step, and its transport -/

section FirstAfter

variable {P : LabelledTuple n} {M a : ZMod n} (hn : 3 ≤ n) (hP : Generic P)

omit [NeZero n] in
/-- A power of a permutation, applied at a point of period `m`, reduces modulo `m`. -/
theorem s7a_pow_apply_mod {α : Type*} (f : Equiv.Perm α) (x : α) (m : ℕ) (hm : (f ^ m) x = x)
    (i : ℕ) : (f ^ i) x = (f ^ (i % m)) x := by
  conv_lhs => rw [← Nat.mod_add_div i m]
  rw [pow_add, pow_mul, Equiv.Perm.mul_apply]
  congr 1
  induction (i / m) with
  | zero => simp
  | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, hm, ih]

omit [NeZero n] in
/-- If two iterates `f^(j+1) c = f^k c` agree with `0 < k ≤ j`, the point has period `j+1-k`. -/
theorem s7a_pow_period {α : Type*} (f : Equiv.Perm α) (c : α) (j k : ℕ) (hk : k ≤ j + 1)
    (h : (f ^ (j + 1)) c = (f ^ k) c) : (f ^ (j + 1 - k)) c = c := by
  have h2 : (f ^ (j + 1)) c = (f ^ k) ((f ^ (j + 1 - k)) c) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hk]
  exact (f ^ k).injective (h2.symm.trans h)

/-- **The sweep lemma.** Iterating `nextMark` from `c` visits the marks in cyclic order: as long as a
mark `u ≠ c` is not among the first `j` iterates, none of these iterates has returned to `c` and the
`j`-th iterate lies cyclically before `u` (seen from `c`).  From the accepted
`markSuccessor_no_mark_between` (no mark strictly between a mark and its successor). -/
theorem s7a_sweep (c : Mark P) (j : ℕ) (hj : 0 < j) :
    ∀ u : Mark P, u ≠ c → (∀ i, 0 < i → i ≤ j → u ≠ (markSuccessor hn hP ^ i) c) →
    (∀ i, 0 < i → i ≤ j → (markSuccessor hn hP ^ i) c ≠ c) ∧
      traversalBetween (markPosition hn hP.1 c) (markPosition hn hP.1 ((markSuccessor hn hP ^ j) c))
        (markPosition hn hP.1 u) := by
  set ms := markSuccessor hn hP with hms
  induction j with
  | zero => exact absurd hj (lt_irrefl 0)
  | succ j ih =>
    intro u hu hchain
    -- the orbit of `ms` through `c` reaches `u`
    obtain ⟨k₀, _, hk₀⟩ := (markSuccessor_sameCycle hn hP c u).exists_pow_eq'
    -- (i') no return at step `j+1`
    have hne : (ms ^ (j + 1)) c ≠ c := by
      intro hret
      have hmod := s7a_pow_apply_mod ms c (j + 1) hret k₀
      rw [hk₀] at hmod
      have hlt : k₀ % (j + 1) < j + 1 := Nat.mod_lt _ (Nat.succ_pos j)
      by_cases h0 : k₀ % (j + 1) = 0
      · rw [h0, pow_zero, Equiv.Perm.one_apply] at hmod
        exact hu hmod
      · exact hchain _ (Nat.pos_of_ne_zero h0) (by omega) hmod
    by_cases hj0 : j = 0
    · subst hj0
      simp only [zero_add, pow_one] at hne hchain ⊢
      refine ⟨fun i hi hi1 => ?_, ?_⟩
      · have : i = 1 := by omega
        subst this
        simpa using hne
      · have hnb := markSuccessor_no_mark_between hn hP c u
        rcases s7a_between_or hn hP c (ms c) u (Ne.symm hne) (Ne.symm (hchain 1 one_pos le_rfl))
          (Ne.symm hu) with h | h
        · exact h
        · exact absurd h hnb
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hchainj : ∀ i, 0 < i → i ≤ j → u ≠ (ms ^ i) c :=
        fun i hi hij => hchain i hi (Nat.le_succ_of_le hij)
      obtain ⟨hA, hB⟩ := ih hjpos u hu hchainj
      -- the new iterate is not among the earlier ones
      have hnew : ∀ i, 0 < i → i ≤ j → (ms ^ (j + 1)) c ≠ (ms ^ i) c := by
        intro i hi hij heq
        have hper := s7a_pow_period ms c j i (by omega) heq
        exact hA (j + 1 - i) (by omega) (by omega) hper
      refine ⟨fun i hi hi1 => ?_, ?_⟩
      · rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · exact hA i hi (Nat.lt_succ_iff.mp hlt)
        · have : i = j + 1 := by omega
          subst this
          exact hne
      · -- the new iterate lies between `c` and `u`
        have hB' := (ih hjpos ((ms ^ (j + 1)) c) hne hnew).2
        have hsucc : (ms ^ (j + 1)) c = ms ((ms ^ j) c) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        have hnb := markSuccessor_no_mark_between hn hP ((ms ^ j) c) u
        rw [← hsucc] at hnb
        rcases s7a_between_or hn hP ((ms ^ j) c) ((ms ^ (j + 1)) c) u (hnew j hjpos le_rfl).symm
          (hchain (j + 1) (Nat.succ_pos j) le_rfl).symm (hchain j hjpos (Nat.le_succ j)).symm with h | h
        · exact s7a_between_trans hn hP hB h
        · exact absurd h hnb

variable (S : Finset (Crossing P))

/-- The `f`-iterates of a persistent mark up to its return time are the `nextMark`-iterates of its
selected-exchange image (the intermediate marks are unselected contact visits, fixed by the exchange). -/
theorem s7a_pow_eq_markSuccessor_pow (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val)
    (x : s7a_PMark M a P) (i : ℕ) (hi : 0 < i) (hle : i ≤ s7a_returnTime hn hP S x.1 x.2) :
    (smoothingSuccessor hn hP S ^ i) x.1 = (markSuccessor hn hP ^ i) (selectedMarkPerm S x.1) := by
  induction i with
  | zero => exact absurd hi (lt_irrefl 0)
  | succ i ih =>
    by_cases hi0 : i = 0
    · subst hi0
      rfl
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hilt : i < s7a_returnTime hn hP S x.1 x.2 := hle
      have hih := ih hipos hilt.le
      have hnp := s7a_returnTime_min hn hP S x.1 x.2 i hipos hilt
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hih]
      -- the intermediate mark is an unselected (contact) visit: the exchange fixes it
      change markSuccessor hn hP (selectedMarkPerm S ((markSuccessor hn hP ^ i) (selectedMarkPerm S x.1))) = _
      congr 1
      rw [← hih]
      cases hm : (smoothingSuccessor hn hP S ^ i) x.1 with
      | inl k => rw [hm] at hnp; exact (hnp trivial).elim
      | inr v =>
        rw [hm] at hnp
        have hvS : v.1 ∉ S := fun h => hnp (hSp v.1 h)
        rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hvS]

omit [NeZero n] in
include hn in
/-- Some vertex differs from two given marks (`n ≥ 3`). -/
theorem s7a_exists_vertex_ne (p y : Mark P) :
    ∃ i : ZMod n, (Sum.inl i : Mark P) ≠ p ∧ (Sum.inl i : Mark P) ≠ y := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have h1 : (0 : ZMod n) - 1 ≠ 0 := prev_ne_self 0
  have h2 : (0 : ZMod n) + 1 ≠ 0 := next_ne_self 0
  have h3 : (0 : ZMod n) - 1 ≠ 0 + 1 := prev_ne_next hn 0
  by_cases hp0 : p = Sum.inl (0 : ZMod n)
  · by_cases hy1 : y = Sum.inl ((0 : ZMod n) + 1)
    · exact ⟨0 - 1, by rw [hp0]; exact fun h => h1 (Sum.inl_injective h),
        by rw [hy1]; exact fun h => h3 (Sum.inl_injective h)⟩
    · exact ⟨0 + 1, by rw [hp0]; exact fun h => h2 (Sum.inl_injective h), fun h => hy1 h.symm⟩
  · by_cases hy0 : y = Sum.inl (0 : ZMod n)
    · by_cases hp1 : p = Sum.inl ((0 : ZMod n) + 1)
      · exact ⟨0 - 1, by rw [hp1]; exact fun h => h3 (Sum.inl_injective h),
          by rw [hy0]; exact fun h => h1 (Sum.inl_injective h)⟩
      · exact ⟨0 + 1, fun h => hp1 h.symm, by rw [hy0]; exact fun h => h2 (Sum.inl_injective h)⟩
    · exact ⟨0, fun h => hp0 h.symm, fun h => hy0 h.symm⟩

/-- **The order characterization of the contracted step**: `step x` is the first persistent mark
strictly after the selected-exchange image `p` of `x` in cyclic order — it differs from `p`, and every
other persistent mark `z ≠ p` lies cyclically after it (seen from `p`). -/
theorem s7a_step_firstAfter (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (x : s7a_PMark M a P) :
    (s7a_step hn hP S x).1 ≠ selectedMarkPerm S x.1 ∧
      ∀ z : Mark P, s7a_Persistent M a z → z ≠ selectedMarkPerm S x.1 →
        z ≠ (s7a_step hn hP S x).1 →
        traversalBetween (markPosition hn hP.1 (selectedMarkPerm S x.1))
          (markPosition hn hP.1 (s7a_step hn hP S x).1) (markPosition hn hP.1 z) := by
  set r := s7a_returnTime hn hP S x.1 x.2 with hr
  have hrpos : 0 < r := s7a_returnTime_pos hn hP S x.1 x.2
  set p := selectedMarkPerm S x.1 with hp
  have hstep : (s7a_step hn hP S x).1 = (markSuccessor hn hP ^ r) p :=
    s7a_pow_eq_markSuccessor_pow hn hP S hSp x r hrpos le_rfl
  -- the intermediate iterates are not persistent
  have hmid : ∀ i, 0 < i → i < r → ¬ s7a_Persistent M a ((markSuccessor hn hP ^ i) p) := by
    intro i hi hir
    rw [← s7a_pow_eq_markSuccessor_pow hn hP S hSp x i hi hir.le]
    exact s7a_returnTime_min hn hP S x.1 x.2 i hi hir
  have hchain : ∀ z : Mark P, s7a_Persistent M a z → z ≠ (s7a_step hn hP S x).1 →
      ∀ i, 0 < i → i ≤ r → z ≠ (markSuccessor hn hP ^ i) p := by
    intro z hz hzy i hi hir
    rcases Nat.lt_or_ge i r with hlt | hge
    · intro he
      exact hmid i hi hlt (he ▸ hz)
    · have : i = r := by omega
      subst this
      rw [← hstep]
      exact hzy
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hip, hiy⟩ := s7a_exists_vertex_ne hn p (s7a_step hn hP S x).1
    have hA := (s7a_sweep hn hP p r hrpos (Sum.inl i) hip (hchain _ trivial hiy)).1
    rw [hstep]
    exact hA r hrpos le_rfl
  · intro z hz hzp hzy
    have hB := (s7a_sweep hn hP p r hrpos z hzp (hchain z hz hzy)).2
    rw [hstep]
    exact hB

/-- Uniqueness of the first persistent mark after `p`. -/
theorem s7a_firstAfter_unique (p y y' : Mark P) (hy : s7a_Persistent M a y)
    (hy' : s7a_Persistent M a y')
    (h : y ≠ p ∧ ∀ z : Mark P, s7a_Persistent M a z → z ≠ p → z ≠ y →
      traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 y) (markPosition hn hP.1 z))
    (h' : y' ≠ p ∧ ∀ z : Mark P, s7a_Persistent M a z → z ≠ p → z ≠ y' →
      traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 y') (markPosition hn hP.1 z)) :
    y = y' := by
  by_contra hne
  exact s7a_between_asymm hn hP (h.2 y' hy' h'.1 (Ne.symm hne)) (h'.2 y hy h.1 hne)

end FirstAfter

/-! #### Conjugation of the contracted steps through the mark map; the carrier equivalence -/

omit [NeZero n] in
/-- `SameCycle` under a conjugating equivalence. -/
theorem s7a_sameCycle_of_equiv_conj {α β : Type*} (f : Equiv.Perm α) (g : Equiv.Perm β) (e : α ≃ β)
    (h : ∀ x, g (e x) = e (f x)) (x y : α) : g.SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  have hinv : ∀ x, g⁻¹ (e x) = e (f⁻¹ x) := by
    intro x
    rw [Equiv.Perm.inv_eq_iff_eq, h, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have hzpow : ∀ (i : ℤ) (x : α), (g ^ i) (e x) = e ((f ^ i) x) := by
    intro i
    induction i using Int.induction_on with
    | zero => intro x; rw [zpow_zero, zpow_zero, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
    | succ i ih =>
      intro x
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, ih]
    | pred i ih =>
      intro x
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, ih]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, e.injective ((hzpow i x).symm.trans hi)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hzpow i x).trans (congrArg e hi)⟩

section Conjugation

variable {P Q : LabelledTuple n} {M a : ZMod n} (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
  (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (hpar : ∀ (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit hs v hv) < visitParameter (s7a_visit hs w hw) ↔
        visitParameter v < visitParameter w))

/-- The mark map on persistent marks, as an equivalence. -/
def s7a_pmarkEquiv : s7a_PMark M a P ≃ s7a_PMark M a Q :=
  Equiv.ofBijective (fun x => ⟨s7a_markMap hs x.1, s7a_markMap_persistent hs x.1 x.2⟩)
    ⟨fun x y h => Subtype.ext (s7a_markMap_injOn hs x.1 y.1 x.2 y.2 (congrArg Subtype.val h)),
      fun y => by
        obtain ⟨m, hm, hmy⟩ := s7a_markMap_surjOn hs y.1 y.2
        exact ⟨⟨m, hm⟩, Subtype.ext hmy⟩⟩

omit [NeZero n] in
theorem s7a_pmarkEquiv_val (x : s7a_PMark M a P) :
    (s7a_pmarkEquiv hs x).1 = s7a_markMap hs x.1 := rfl

include hpar in
/-- Cyclic betweenness of persistent marks is carried by the mark map. -/
theorem s7a_between_map (p q r : Mark P) (hp : s7a_Persistent M a p) (hq : s7a_Persistent M a q)
    (hr : s7a_Persistent M a r) :
    traversalBetween (markPosition hn hQ.1 (s7a_markMap hs p)) (markPosition hn hQ.1 (s7a_markMap hs q))
        (markPosition hn hQ.1 (s7a_markMap hs r)) ↔
      traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r) := by
  show ((markKey hn hQ.1 _ < markKey hn hQ.1 _ ∧ markKey hn hQ.1 _ < markKey hn hQ.1 _) ∨
      (markKey hn hQ.1 _ < markKey hn hQ.1 _ ∧ markKey hn hQ.1 _ < markKey hn hQ.1 _) ∨
      (markKey hn hQ.1 _ < markKey hn hQ.1 _ ∧ markKey hn hQ.1 _ < markKey hn hQ.1 _)) ↔
    ((markKey hn hP.1 _ < markKey hn hP.1 _ ∧ markKey hn hP.1 _ < markKey hn hP.1 _) ∨
      (markKey hn hP.1 _ < markKey hn hP.1 _ ∧ markKey hn hP.1 _ < markKey hn hP.1 _) ∨
      (markKey hn hP.1 _ < markKey hn hP.1 _ ∧ markKey hn hP.1 _ < markKey hn hP.1 _))
  rw [s7a_markKey_lt hn hP hQ hs hpar p q hp hq, s7a_markKey_lt hn hP hQ hs hpar q r hq hr,
    s7a_markKey_lt hn hP hQ hs hpar r p hr hp]

variable (S : Finset (Crossing P)) (S' : Finset (Crossing Q))
  (hSS' : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val), (s7a_visit hs v hv).1 ∈ S' ↔ v.1 ∈ S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)

include hpar hSS' hSp hSp' in
/-- The contracted steps are conjugate under the mark map. -/
theorem s7a_step_map (x : s7a_PMark M a P) :
    (s7a_step hn hQ S' (s7a_pmarkEquiv hs x)).1 = s7a_markMap hs (s7a_step hn hP S x).1 := by
  have hP1 := s7a_step_firstAfter hn hP S hSp x
  have hQ1 := s7a_step_firstAfter hn hQ S' hSp' (s7a_pmarkEquiv hs x)
  have hperm : selectedMarkPerm S' (s7a_pmarkEquiv hs x).1 = s7a_markMap hs (selectedMarkPerm S x.1) := by
    rw [s7a_pmarkEquiv_val]
    exact s7a_markMap_selectedMarkPerm hs S S' hSS' x.1 x.2
  have hpp : s7a_Persistent M a (selectedMarkPerm S x.1) := by
    rcases x with ⟨m, hm⟩
    cases m with
    | inl i => trivial
    | inr v =>
      rw [selectedMarkPerm_visit]
      show ¬ ContactAffected M a (selectedVisitTwin S v).1.val
      rw [selectedVisitTwin_crossing]
      exact hm
  rw [hperm] at hQ1
  refine s7a_firstAfter_unique hn hQ _ _ _ (s7a_step hn hQ S' _).2
    (s7a_markMap_persistent hs _ (s7a_step hn hP S x).2) hQ1 ⟨?_, ?_⟩
  · intro h
    exact hP1.1 (s7a_markMap_injOn hs _ _ (s7a_step hn hP S x).2 hpp h)
  · intro z' hz' hz'p hz'y
    obtain ⟨z, hz, rfl⟩ := s7a_markMap_surjOn hs z' hz'
    rw [s7a_between_map hn hP hQ hs hpar _ _ _ hpp (s7a_step hn hP S x).2 hz]
    exact hP1.2 z hz (fun h => hz'p (congrArg _ h)) (fun h => hz'y (congrArg _ h))

include hpar hSS' hSp hSp' in
theorem s7a_stepPerm_map (x : s7a_PMark M a P) :
    s7a_stepPerm hn hQ S' (s7a_pmarkEquiv hs x) = s7a_pmarkEquiv hs (s7a_stepPerm hn hP S x) := by
  apply Subtype.ext
  rw [s7a_stepPerm_apply, s7a_stepPerm_apply, s7a_pmarkEquiv_val]
  exact s7a_step_map hn hP hQ hs hpar S S' hSS' hSp hSp' x

/-- **The carrier correspondence** of a persistent support across the contact wall. -/
def s7a_componentEquiv : Component hn hP S ≃ Component hn hQ S' :=
  (s7a_componentEquivQuot hn hP S hSp).trans
    ((Quotient.congr (s7a_pmarkEquiv hs) (fun x y =>
      (s7a_sameCycle_of_equiv_conj (s7a_stepPerm hn hP S) (s7a_stepPerm hn hQ S') (s7a_pmarkEquiv hs)
        (s7a_stepPerm_map hn hP hQ hs hpar S S' hSS' hSp hSp') x y).symm)).trans
      (s7a_componentEquivQuot hn hQ S' hSp').symm)

/-- The correspondence sends the carrier of a persistent mark to the carrier of its image. -/
theorem s7a_componentEquiv_owner (m : Mark P) (hm : s7a_Persistent M a m) :
    s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' (owner hn hP S m) =
      owner hn hQ S' (s7a_markMap hs m) := by
  unfold s7a_componentEquiv
  rw [Equiv.trans_apply, Equiv.trans_apply, s7a_componentEquivQuot_owner hn hP S hSp m hm,
    Equiv.symm_apply_eq, s7a_componentEquivQuot_owner hn hQ S' hSp' _ (s7a_markMap_persistent hs m hm)]
  rfl

end Conjugation

/-! #### Consequences on the carriers: self-crossings, corner lists, turns, uniformity, interlacement -/

section Carriers

variable {P Q : LabelledTuple n} {M a : ZMod n} (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
  (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (hpar : ∀ (v w : Visit P) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit hs v hv) < visitParameter (s7a_visit hs w hw) ↔
        visitParameter v < visitParameter w))

omit [NeZero n] in
/-- True corners of a persistent support are persistent marks. -/
theorem s7a_isTrueCorner_persistent {R : LabelledTuple n} (T : Finset (Crossing R))
    (hTp : ∀ x ∈ T, ¬ ContactAffected M a x.val) (m : Mark R) (h : IsTrueCorner T m) :
    s7a_Persistent M a m := by
  cases m with
  | inl i => trivial
  | inr v => exact hTp v.1 h

variable (S : Finset (Crossing P)) (S' : Finset (Crossing Q))
  (hSS' : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val), (s7a_visit hs v hv).1 ∈ S' ↔ v.1 ∈ S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)

omit [NeZero n] in
/-- The transported persistent crossing (same support). -/
def s7a_cross (x : Crossing P) (hx : ¬ ContactAffected M a x.val) : Crossing Q :=
  ⟨x.val, (hs _ hx).mpr x.property⟩

omit [NeZero n] in
theorem s7a_cross_val (x : Crossing P) (hx : ¬ ContactAffected M a x.val) :
    (s7a_cross hs x hx).val = x.val := rfl

omit [NeZero n] in
theorem s7a_visit_fst (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) :
    (s7a_visit hs v hv).1 = s7a_cross hs v.1 hv := rfl

omit [NeZero n] in
theorem s7a_cross_surj (x' : Crossing Q) (hx' : ¬ ContactAffected M a x'.val) :
    ∃ (x : Crossing P) (hx : ¬ ContactAffected M a x.val), s7a_cross hs x hx = x' :=
  ⟨⟨x'.val, (hs _ hx').mp x'.property⟩, hx', rfl⟩

include hSS' in
omit [NeZero n] in
/-- Membership in the transported support. -/
theorem s7a_cross_mem (x : Crossing P) (hx : ¬ ContactAffected M a x.val) :
    s7a_cross hs x hx ∈ S' ↔ x ∈ S := by
  obtain ⟨i, j, hij, _, _⟩ := x.property
  have hi : i ∈ x.val := by rw [hij]; simp
  exact hSS' ⟨x, ⟨i, hi⟩⟩ hx

include hpar hSS' hSp hSp' in
/-- A persistent crossing is a self-crossing of a carrier iff its transport is a self-crossing of the
corresponding carrier. -/
theorem s7a_mem_carrierCrossings (x : Crossing P) (hx : ¬ ContactAffected M a x.val)
    (q : Component hn hP S) :
    s7a_cross hs x hx ∈ carrierCrossings hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q) ↔
      x ∈ carrierCrossings hn hP S q := by
  rw [mem_carrierCrossings_iff_fiber, mem_carrierCrossings_iff_fiber, s7a_cross_mem hs S S' hSS' x hx]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  have hmark : (Sum.inr (⟨s7a_cross hs x hx, i⟩ : Visit Q) : Mark Q) =
      s7a_markMap hs (Sum.inr (⟨x, i⟩ : Visit P)) := by
    rw [s7a_markMap_inr hs _ hx]
    rfl
  rw [hmark, ← s7a_componentEquiv_owner hn hP hQ hs hpar S S' hSS' hSp hSp' (Sum.inr ⟨x, i⟩) hx]
  exact (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp').injective.eq_iff

include hSS' in
theorem s7a_isTrueCorner_map (m : Mark P) (hm : s7a_Persistent M a m) :
    IsTrueCorner S' (s7a_markMap hs m) ↔ IsTrueCorner S m := by
  cases m with
  | inl i => exact Iff.rfl
  | inr v =>
    rw [s7a_markMap_inr hs v hm, isTrueCorner_visit, isTrueCorner_visit]
    exact hSS' v hm

include hpar hSS' hSp hSp' in
/-- **The corner lists correspond literally** (no rotation): the corner list is the filter of the
sorted mark list by ownership and true-cornerhood, both carried by the mark map on persistent marks,
and the sorted persistent sublists agree (`s7a_markList_filter`). -/
theorem s7a_ccpCornerList_map (q : Component hn hP S) :
    ccpCornerList hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q) =
      (ccpCornerList hn hP S q).map (s7a_markMap hs) := by
  set e := s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' with he
  -- both corner lists as single filters
  have hP1 : ccpCornerList hn hP S q = (markList hn hP).filter
      (fun m => decide (IsTrueCorner S m) && decide (owner hn hP S m = q)) := by
    unfold ccpCornerList componentMarkList
    rw [List.filter_filter]
  have hQ1 : ccpCornerList hn hQ S' (e q) = (markList hn hQ).filter
      (fun m => decide (IsTrueCorner S' m) && decide (owner hn hQ S' m = e q)) := by
    unfold ccpCornerList componentMarkList
    rw [List.filter_filter]
  -- restrict `Q`'s filter to the persistent sublist
  have hQ2 : (markList hn hQ).filter
      (fun m => decide (IsTrueCorner S' m) && decide (owner hn hQ S' m = e q)) =
      ((markList hn hQ).filter (fun m => decide (s7a_Persistent M a m))).filter
        (fun m => decide (IsTrueCorner S' m) && decide (owner hn hQ S' m = e q)) := by
    rw [List.filter_filter]
    refine List.filter_congr (fun m _ => ?_)
    by_cases hc : IsTrueCorner S' m
    · simp only [hc, decide_true, Bool.true_and, s7a_isTrueCorner_persistent S' hSp' m hc,
        Bool.and_true]
    · simp only [hc, decide_false, Bool.false_and]
  have hP2 : (markList hn hP).filter
      (fun m => decide (IsTrueCorner S m) && decide (owner hn hP S m = q)) =
      ((markList hn hP).filter (fun m => decide (s7a_Persistent M a m))).filter
        (fun m => decide (IsTrueCorner S m) && decide (owner hn hP S m = q)) := by
    rw [List.filter_filter]
    refine List.filter_congr (fun m _ => ?_)
    by_cases hc : IsTrueCorner S m
    · simp only [hc, decide_true, Bool.true_and, s7a_isTrueCorner_persistent S hSp m hc,
        Bool.and_true]
    · simp only [hc, decide_false, Bool.false_and]
  rw [hQ1, hP1, hQ2, hP2, s7a_markList_filter hn hP hQ hs hpar, List.filter_map]
  congr 1
  refine List.filter_congr (fun m hm => ?_)
  have hmp : s7a_Persistent M a m := by
    rw [List.mem_filter, decide_eq_true_eq] at hm
    exact hm.2
  simp only [Function.comp]
  have h1 : decide (IsTrueCorner S' (s7a_markMap hs m)) = decide (IsTrueCorner S m) :=
    decide_eq_decide.mpr (s7a_isTrueCorner_map hs S S' hSS' m hmp)
  have h2 : decide (owner hn hQ S' (s7a_markMap hs m) = e q) = decide (owner hn hP S m = q) := by
    apply decide_eq_decide.mpr
    rw [← s7a_componentEquiv_owner hn hP hQ hs hpar S S' hSS' hSp hSp' m hmp]
    exact e.injective.eq_iff
  rw [h1, h2]

include hpar hSS' hSp hSp' in
theorem s7a_ccpCornerCount_eq (q : Component hn hP S) :
    ccpCornerCount hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q) =
      ccpCornerCount hn hP S q := by
  unfold ccpCornerCount
  rw [s7a_ccpCornerList_map hn hP hQ hs hpar S S' hSS' hSp hSp' q, List.length_map]

include hpar hSS' hSp hSp' in
/-- The corner marks correspond index by index (through the cast of the equal corner counts). -/
theorem s7a_ccpCornerMark_map (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ccpCornerMark hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q)
        (Equiv.cast (congrArg ZMod (s7a_ccpCornerCount_eq hn hP hQ hs hpar S S' hSS' hSp hSp' q).symm) j) =
      s7a_markMap hs (ccpCornerMark hn hP S q j) := by
  unfold ccpCornerMark
  exact Carrier.MarkTransport.getElem_eq_map_of_eq (s7a_markMap hs) _ _
    (s7a_ccpCornerList_map hn hP hQ hs hpar S S' hSS' hSp hSp' q) _ _
    (zmod_val_cast (s7a_ccpCornerCount_eq hn hP hQ hs hpar S S' hSS' hSp hSp' q).symm j) _ _

omit [NeZero n] in
/-- The turn of a persistent mark is carried when vertex turns and the crossing signs of persistent
crossings are. -/
theorem s7a_markTurn_map (hturn : ∀ i, turn Q i = turn P i)
    (hsgn : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      crossingSign Q (s7a_visit hs v hv).2.val (visitTwin (s7a_visit hs v hv)).2.val =
        crossingSign P v.2.val (visitTwin v).2.val)
    (m : Mark P) (hm : s7a_Persistent M a m) :
    markTurn Q (s7a_markMap hs m) = markTurn P m := by
  cases m with
  | inl i => exact hturn i
  | inr v =>
    rw [s7a_markMap_inr hs v hm, markTurn_inr, markTurn_inr]
    exact hsgn v hm

include hpar hSS' hSp hSp' in
/-- The turns of the corner polygons correspond index by index. -/
theorem s7a_turn_ccpCornerPolygon (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hQ S')
    (hturn : ∀ i, turn Q i = turn P i)
    (hsgn : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      crossingSign Q (s7a_visit hs v hv).2.val (visitTwin (s7a_visit hs v hv)).2.val =
        crossingSign P v.2.val (visitTwin v).2.val)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    turn (ccpCornerPolygon hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q))
        (Equiv.cast (congrArg ZMod (s7a_ccpCornerCount_eq hn hP hQ hs hpar S S' hSS' hSp hSp' q).symm) j) =
      turn (ccpCornerPolygon hn hP S q) j := by
  rw [turn_ccpCornerPolygon_eq_markTurn hn hQ hS', turn_ccpCornerPolygon_eq_markTurn hn hP hS,
    s7a_ccpCornerMark_map hn hP hQ hs hpar S S' hSS' hSp hSp' q j]
  exact s7a_markTurn_map hs hturn hsgn _
    (s7a_isTrueCorner_persistent S hSp _ (ccpCornerMark_mem hn hP S q j).2)

include hpar hSS' hSp hSp' in
/-- **Uniformity is carried** across the contact wall for corresponding carriers. -/
theorem s7a_carrierUniform_iff (hS : IsDecomposition hn hP S) (hS' : IsDecomposition hn hQ S')
    (hturn : ∀ i, turn Q i = turn P i)
    (hsgn : ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      crossingSign Q (s7a_visit hs v hv).2.val (visitTwin (s7a_visit hs v hv)).2.val =
        crossingSign P v.2.val (visitTwin v).2.val)
    (q : Component hn hP S) :
    CarrierUniform hn hQ S' (s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' q) ↔
      CarrierUniform hn hP S q := by
  unfold CarrierUniform
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h j
    rw [← s7a_turn_ccpCornerPolygon hn hP hQ hs hpar S S' hSS' hSp hSp' hS hS' hturn hsgn q j]
    exact h _
  · intro h j'
    obtain ⟨j, rfl⟩ := (Equiv.cast (congrArg ZMod
      (s7a_ccpCornerCount_eq hn hP hQ hs hpar S S' hSS' hSp hSp' q).symm)).surjective j'
    rw [s7a_turn_ccpCornerPolygon hn hP hQ hs hpar S S' hSS' hSp hSp' hS hS' hturn hsgn q j]
    exact h j

include hpar in
/-- Interlacement of persistent crossings is carried (all four visits are persistent; cyclic order of
persistent marks is carried, `s7a_between_map`). -/
theorem s7a_interlaces_iff (x y : Crossing P) (hx : ¬ ContactAffected M a x.val)
    (hy : ¬ ContactAffected M a y.val) :
    Interlaces hn hQ (s7a_cross hs x hx) (s7a_cross hs y hy) ↔ Interlaces hn hP x y := by
  have hne : s7a_cross hs x hx ≠ s7a_cross hs y hy ↔ x ≠ y := by
    constructor
    · intro h hxy; exact h (by subst hxy; rfl)
    · intro h h'
      have hv := congrArg Subtype.val h'
      exact h (Subtype.ext hv)
  have hbet : ∀ (x₀ x₁ : {i // i ∈ x.val}) (y₀ : {i // i ∈ y.val}),
      crossingVisitBetween hn hQ.1 (s7a_cross hs x hx) x₀ x₁ (s7a_cross hs y hy) y₀ ↔
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ := by
    intro x₀ x₁ y₀
    have h1 : (Sum.inr (⟨s7a_cross hs x hx, x₀⟩ : Visit Q) : Mark Q) =
        s7a_markMap hs (Sum.inr (⟨x, x₀⟩ : Visit P)) := by rw [s7a_markMap_inr hs _ hx]; rfl
    have h2 : (Sum.inr (⟨s7a_cross hs x hx, x₁⟩ : Visit Q) : Mark Q) =
        s7a_markMap hs (Sum.inr (⟨x, x₁⟩ : Visit P)) := by rw [s7a_markMap_inr hs _ hx]; rfl
    have h3 : (Sum.inr (⟨s7a_cross hs y hy, y₀⟩ : Visit Q) : Mark Q) =
        s7a_markMap hs (Sum.inr (⟨y, y₀⟩ : Visit P)) := by rw [s7a_markMap_inr hs _ hy]; rfl
    change traversalBetween (markPosition hn hQ.1 (Sum.inr ⟨s7a_cross hs x hx, x₀⟩))
      (markPosition hn hQ.1 (Sum.inr ⟨s7a_cross hs y hy, y₀⟩))
      (markPosition hn hQ.1 (Sum.inr ⟨s7a_cross hs x hx, x₁⟩)) ↔
      traversalBetween (markPosition hn hP.1 (Sum.inr ⟨x, x₀⟩)) (markPosition hn hP.1 (Sum.inr ⟨y, y₀⟩))
        (markPosition hn hP.1 (Sum.inr ⟨x, x₁⟩))
    rw [h1, h2, h3]
    exact s7a_between_map hn hP hQ hs hpar _ _ _ hx hy hx
  unfold Interlaces
  rw [hne]
  refine and_congr Iff.rfl ?_
  refine exists_congr fun x₀ => exists_congr fun x₁ => exists_congr fun y₀ => exists_congr fun y₁ => ?_
  rw [hbet x₀ x₁ y₀, hbet x₁ x₀ y₁]
  exact Iff.rfl

include hpar hSS' hSp hSp' in
/-- **Decompositions correspond**: a persistent support is independent iff its transport is. -/
theorem s7a_isDecomposition_iff : IsDecomposition hn hQ S' ↔ IsDecomposition hn hP S := by
  unfold IsDecomposition
  rw [mem_independentSupports_iff, mem_independentSupports_iff]
  constructor
  · intro h x hx y hy hxy hI
    exact h _ ((s7a_cross_mem hs S S' hSS' x (hSp x hx)).mpr hx) _
      ((s7a_cross_mem hs S S' hSS' y (hSp y hy)).mpr hy)
      (fun he => hxy (by have hv := congrArg Subtype.val he; exact Subtype.ext hv))
      ((s7a_interlaces_iff hn hP hQ hs hpar x y (hSp x hx) (hSp y hy)).mpr hI)
  · intro h x' hx' y' hy' hxy hI
    obtain ⟨x, hx, rfl⟩ := s7a_cross_surj hs x' (hSp' x' hx')
    obtain ⟨y, hy, rfl⟩ := s7a_cross_surj hs y' (hSp' y' hy')
    exact h x ((s7a_cross_mem hs S S' hSS' x hx).mp hx') y ((s7a_cross_mem hs S S' hSS' y hy).mp hy')
      (fun he => hxy (by subst he; rfl)) ((s7a_interlaces_iff hn hP hQ hs hpar x y hx hy).mp hI)

end Carriers

/-! #### Instantiation at a simple vertex–edge wall: the two sides at one parameter -/

section Germ

variable (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)

/-- The accepted local data of lem:wall-sides (V) (`VertexLocalData`, SM/VertexSides.lean) at BOTH
sides of the side parameter `t`, relative to the centre. -/
def s7a_SideLocal (r η : ℝ) (t : g.SideParameter) : Prop :=
  ∀ b : Bool, VertexLocalData hn g.center (g.curve (g.sideTime b t)) M a r η

/-- lem:wall-sides (V) (`vertex_sides`) supplies the contact parameter `r`, the window half-width `η`
and a radius `δ` below which both sides carry the local data. -/
theorem s7a_exists_sideLocal (h : g.VertexEdgeAt M a) :
    ∃ r η : ℝ, 0 < r ∧ r < 1 ∧ g.center M = edgePoint g.center a r ∧
      0 < η ∧ 4 * η < r ∧ 4 * η < 1 - r ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
        s7a_SideLocal hn g M a r η t := by
  obtain ⟨-, -, -, -, r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, hδr, hloc⟩ := vertex_sides hn g h
  refine ⟨r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, hδr, fun t ht b => ?_⟩
  exact hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)

variable {M a} {r η : ℝ} {t : g.SideParameter}

omit [NeZero n] in
/-- Genericity of a side point, written on `g.curve (g.sideTime b t)`. -/
theorem s7a_sideGeneric (b : Bool) : Generic (g.curve (g.sideTime b t)) :=
  g.generic_punctured _ (g.sideTime_ne_zero b t)

/-- (1) Persistent crossings agree between any two sides (both agree with the centre's):
the crossing hypothesis of the transport from side `b` to side `b'`. -/
theorem s7a_side_hs (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool) :
    ∀ s, ¬ ContactAffected M a s →
      (IsCrossing (g.curve (g.sideTime b' t)) s ↔ IsCrossing (g.curve (g.sideTime b t)) s) :=
  fun s hs => ((hL b').windows.1 s hs).trans ((hL b).windows.1 s hs).symm

/-- (2) The same-edge parameter order of persistent visits agrees between the two sides
(`VertexLocalData.visit_order` on both sides, composed through the centre): the parameter hypothesis
`hpar` of the transport from side `b` to side `b'`. -/
theorem s7a_side_hpar (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool) :
    ∀ (v w : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val)
      (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
      (visitParameter (s7a_visit (s7a_side_hs hn g hL b b') v hv) <
          visitParameter (s7a_visit (s7a_side_hs hn g hL b b') w hw) ↔
        visitParameter v < visitParameter w) := by
  intro v w hv hw he
  set hb := (hL b).windows.1
  set hb' := (hL b').windows.1
  let v₀ : PersistentContactVisit g.center M a := (contactVisitTransport hb).symm ⟨v, hv⟩
  let w₀ : PersistentContactVisit g.center M a := (contactVisitTransport hb).symm ⟨w, hw⟩
  have hv₀ : contactVisitTransport hb v₀ = ⟨v, hv⟩ := Equiv.apply_symm_apply _ _
  have hw₀ : contactVisitTransport hb w₀ = ⟨w, hw⟩ := Equiv.apply_symm_apply _ _
  have hedge : v₀.val.2.val = w₀.val.2.val := he
  have h1 := (hL b').visit_order (s7a_sideGeneric g b').1 v₀ w₀ hedge
  have h2 := (hL b).visit_order (s7a_sideGeneric g b).1 v₀ w₀ hedge
  rw [hv₀, hw₀] at h2
  have hv' : s7a_visit (s7a_side_hs hn g hL b b') v hv = (contactVisitTransport hb' v₀).val := rfl
  have hw' : s7a_visit (s7a_side_hs hn g hL b b') w hw = (contactVisitTransport hb' w₀).val := rfl
  rw [hv', hw', h1]
  exact h2.symm

/-- (3) Vertex turns agree between the two sides: the turn triple `{i−1, i, i+1}` is never the
contact support (`contactSupport_ne_turnSupport`), so `ChirotopesOutsideZerosAgree` applies. -/
theorem s7a_side_turn (h : g.VertexEdgeAt M a) (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool)
    (i : ZMod n) : turn (g.curve (g.sideTime b' t)) i = turn (g.curve (g.sideTime b t)) i := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have h1 : i - 1 ≠ i := prev_ne_self i
  have h2 : i ≠ i + 1 := (next_ne_self i).symm
  have h3 : i - 1 ≠ i + 1 := prev_ne_next hn i
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.2.1
  have hnot : ({i - 1, i, i + 1} : Finset (ZMod n)) ∉ pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    exact fun he => contactSupport_ne_turnSupport hn h.1 i he.symm
  have hb := ((hL b).chirotopes (i - 1) i (i + 1) h1 h2 h3 hnot).1
  have hb' := ((hL b').chirotopes (i - 1) i (i + 1) h1 h2 h3 hnot).1
  unfold turn
  rw [hb, hb']

omit [NeZero n] in
include hn in
/-- The crossing sign of a crossing `{i, j}` of a `G1` polygon is the chirotope `χ_{i,i+1,j+1}`
(the two endpoints of `E_j` lie on opposite sides of the line of `E_i`, `crossing_test`). -/
theorem s7a_crossingSign_eq_chi {P : LabelledTuple n} (hP : G1 P) {i j : ZMod n}
    (hc : IsCrossing P {i, j}) : crossingSign P i j = chi P i (i + 1) (j + 1) := by
  have hr := crossing_pair_remote hc
  have ht := ((crossing_test hn P hP).1 i j hr).mp hc
  have hprod : det (edge P i) (P j - P i) * det (edge P i) (P (j + 1) - P i) < 0 := by
    have := ht.1
    rw [chi_edge, chi_edge, sign_product_neg_iff] at this
    exact this
  have hdet : det (edge P i) (edge P j) =
      det (edge P i) (P (j + 1) - P i) - det (edge P i) (P j - P i) := by
    simp [edge, det]; ring
  unfold crossingSign
  rw [chi_edge, hdet]
  rcases mul_neg_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sign_neg h2, sign_neg (by linarith)]
  · rw [sign_pos h2, sign_pos (by linarith)]

/-- (4) Crossing signs of persistent crossings agree between the two sides: the sign is the
chirotope `χ_{e,e+1,f+1}`, whose triple is not the contact support for an unaffected pair, so
`ChirotopesOutsideZerosAgree` applies — the over-bit hypothesis `hsgn` of the transport. -/
theorem s7a_side_sgn (h : g.VertexEdgeAt M a) (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool) :
    ∀ (v : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val),
      crossingSign (g.curve (g.sideTime b' t)) (s7a_visit (s7a_side_hs hn g hL b b') v hv).2.val
          (visitTwin (s7a_visit (s7a_side_hs hn g hL b b') v hv)).2.val =
        crossingSign (g.curve (g.sideTime b t)) v.2.val (visitTwin v).2.val := by
  intro v hv
  have hpair : v.1.val = {v.2.val, (visitTwin v).2.val} := visit_crossing_val_eq_pair v
  have hcb : IsCrossing (g.curve (g.sideTime b t)) {v.2.val, (visitTwin v).2.val} :=
    hpair ▸ v.1.property
  have hnot : ¬ ContactAffected M a {v.2.val, (visitTwin v).2.val} := hpair ▸ hv
  have hcb' : IsCrossing (g.curve (g.sideTime b' t)) {v.2.val, (visitTwin v).2.val} :=
    (s7a_side_hs hn g hL b b' _ hnot).mpr hcb
  have hedge2 : (visitTwin (s7a_visit (s7a_side_hs hn g hL b b') v hv)).2.val = (visitTwin v).2.val := by
    rw [← s7a_visit_twin]
    rfl
  rw [hedge2]
  show crossingSign (g.curve (g.sideTime b' t)) v.2.val (visitTwin v).2.val = _
  rw [s7a_crossingSign_eq_chi hn (s7a_sideGeneric g b').1 hcb',
    s7a_crossingSign_eq_chi hn (s7a_sideGeneric g b).1 hcb]
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints _ _ (crossing_pair_remote hcb)
  have h1 : v.2.val ≠ v.2.val + 1 := (next_ne_self _).symm
  have h2 : v.2.val + 1 ≠ (visitTwin v).2.val + 1 := hf1e1.symm
  have h3 : v.2.val ≠ (visitTwin v).2.val + 1 := hf1e.symm
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.2.1
  have hnotz : ({v.2.val, v.2.val + 1, (visitTwin v).2.val + 1} : Finset (ZMod n)) ∉
      pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    intro heq
    have hea : v.2.val = a := contactSupport_successive hn h.1 (by rw [← heq]; simp) (by rw [← heq]; simp)
    have hf1 : (visitTwin v).2.val + 1 ∈ contactSupport M a := by rw [← heq]; simp
    simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hf1
    rcases hf1 with hf1 | hf1 | hf1
    · exact h3 (by rw [hea, hf1])
    · exact hfe (by rw [add_right_cancel hf1, hea])
    · apply hnot
      left
      rw [hea, eq_sub_of_add_eq hf1]
  have hcb1 := ((hL b).chirotopes _ _ _ h1 h2 h3 hnotz).1
  have hcb1' := ((hL b').chirotopes _ _ _ h1 h2 h3 hnotz).1
  rw [hcb1, hcb1']

omit [NeZero n] in
/-- In `SignType`, `s * t = -1` forces `s = -t`. -/
theorem s7a_signType_mul_eq_neg_one {s t : SignType} (h : s * t = -1) : s = -t := by
  cases s <;> cases t <;> first | rfl | exact absurd h (by decide)

/-- (5) **The sliding relocation sign.** When side `b` carries the contact crossing `{a, M−1}` and
side `b'` carries `{a, M}` (the sliding pattern), the crossing signs of the two contact crossings
agree: `sgn det(E_a, E_M)` on side `b'` equals `sgn det(E_a, E_{M−1})` on side `b`.  Inputs: the contact
test of side `b` (`WallGerm.vertexEdge_contact_tests`, at the side time of `t`), the sliding
alternation `χ_{a,a+1,M−1}(C) ≠ χ_{a,a+1,M+1}(C)`, and chirotope persistence at `{a, a+1, M+1}`.
This is the over-bit input for the relocated visit `x₋ ↦ x₊` (U110-D note 1). -/
theorem s7a_sliding_relocation_sign (h : g.SlidingAt M a) (hL : s7a_SideLocal hn g M a r η t)
    (b b' : Bool) (hb : IsCrossing (g.curve (g.sideTime b t)) {a, M - 1})
    (hb' : IsCrossing (g.curve (g.sideTime b' t)) {a, M})
    (htest : ∀ forward : Bool, IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg forward M} ↔
      chi (g.curve (g.sideTime b t)) a (a + 1) M *
        chi g.center a (a + 1) (contactNeighbour forward M) = -1) :
    crossingSign (g.curve (g.sideTime b' t)) a M = crossingSign (g.curve (g.sideTime b t)) a (M - 1) := by
  have hsep : ContactSeparated M a := h.1.1
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  -- side `b`: `sgn det(E_a, E_{M−1}) = χ_{a,a+1,M}(P_b) = −χ_{a,a+1,M−1}(C)`
  have h1 : crossingSign (g.curve (g.sideTime b t)) a (M - 1) =
      chi (g.curve (g.sideTime b t)) a (a + 1) M := by
    rw [s7a_crossingSign_eq_chi hn (s7a_sideGeneric g b).1 hb, sub_add_cancel]
  have htb := (htest false).mp (by simpa [contactLeg] using hb)
  simp only [contactNeighbour, Bool.false_eq_true, ↓reduceIte] at htb
  have h2 : chi (g.curve (g.sideTime b t)) a (a + 1) M = -chi g.center a (a + 1) (M - 1) :=
    s7a_signType_mul_eq_neg_one htb
  -- side `b'`: `sgn det(E_a, E_M) = χ_{a,a+1,M+1}(P_{b'}) = χ_{a,a+1,M+1}(C)`
  have h3 : crossingSign (g.curve (g.sideTime b' t)) a M =
      chi (g.curve (g.sideTime b' t)) a (a + 1) (M + 1) :=
    s7a_crossingSign_eq_chi hn (s7a_sideGeneric g b').1 hb'
  have hd1 : a ≠ a + 1 := (next_ne_self a).symm
  have hd2 : a + 1 ≠ M + 1 := fun he => hsep.2.1 (add_right_cancel he).symm
  have hd3 : a ≠ M + 1 := fun he => hsep.1 (by rw [he]; ring)
  have hnotz : ({a, a + 1, M + 1} : Finset (ZMod n)) ∉ pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    intro heq
    have hm : M + 1 ∈ contactSupport M a := by rw [← heq]; simp
    simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact hd3 hm.symm
    · exact hd2 hm.symm
    · exact (next_ne_self M) hm
  have h4 := ((hL b').chirotopes a (a + 1) (M + 1) hd1 hd2 hd3 hnotz).1
  -- the sliding alternation: `χ_{M+1}(C) = −χ_{M−1}(C)`
  have hne0 : chi g.center a (a + 1) (M - 1) ≠ 0 := by
    have := contactNeighbour_chi_nonzero hn hsep hz false
    simpa [contactNeighbour] using this
  have hne1 : chi g.center a (a + 1) (M + 1) ≠ 0 := by
    have := contactNeighbour_chi_nonzero hn hsep hz true
    simpa [contactNeighbour] using this
  have hneg0 : -chi g.center a (a + 1) (M - 1) ≠ 0 := by
    rcases signType_nonzero_cases hne0 with hh | hh <;> rw [hh] <;> decide
  have h5 : chi g.center a (a + 1) (M + 1) = -chi g.center a (a + 1) (M - 1) := by
    rw [signType_eq_iff_ne_neg hne1 hneg0, neg_neg]
    exact fun he => h.2 he.symm
  rw [h3, h4, h5, h1, h2]

/-! #### Convenience instantiations at the wall (how the consumers plug the pieces together) -/

variable (h : g.VertexEdgeAt M a) (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool)
  (S : Finset (Crossing (g.curve (g.sideTime b t)))) (S' : Finset (Crossing (g.curve (g.sideTime b' t))))
  (hSS' : ∀ (v : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val),
    (s7a_visit (s7a_side_hs hn g hL b b') v hv).1 ∈ S' ↔ v.1 ∈ S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)

include hL hSS' hSp hSp' in
/-- The carrier correspondence between the two sides for a persistent support. -/
def s7a_sideComponentEquiv :
    Component hn (s7a_sideGeneric g b) S ≃ Component hn (s7a_sideGeneric g b') S' :=
  s7a_componentEquiv hn (s7a_sideGeneric g b) (s7a_sideGeneric g b') (s7a_side_hs hn g hL b b')
    (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp'

theorem s7a_sideComponentEquiv_owner (m : Mark (g.curve (g.sideTime b t)))
    (hm : s7a_Persistent M a m) :
    s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' (owner hn (s7a_sideGeneric g b) S m) =
      owner hn (s7a_sideGeneric g b') S' (s7a_markMap (s7a_side_hs hn g hL b b') m) :=
  s7a_componentEquiv_owner hn _ _ _ _ S S' hSS' hSp hSp' m hm

include hL hSS' hSp hSp' in
/-- Decompositions correspond between the two sides. -/
theorem s7a_side_isDecomposition_iff :
    IsDecomposition hn (s7a_sideGeneric g b') S' ↔ IsDecomposition hn (s7a_sideGeneric g b) S :=
  s7a_isDecomposition_iff hn _ _ (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp'

include h in
/-- Uniformity corresponds between the two sides. -/
theorem s7a_side_carrierUniform_iff (hS : IsDecomposition hn (s7a_sideGeneric g b) S)
    (hS' : IsDecomposition hn (s7a_sideGeneric g b') S') (q : Component hn (s7a_sideGeneric g b) S) :
    CarrierUniform hn (s7a_sideGeneric g b') S' (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q) ↔
      CarrierUniform hn (s7a_sideGeneric g b) S q :=
  s7a_carrierUniform_iff hn _ _ (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp'
    hS hS' (s7a_side_turn hn g h hL b b') (s7a_side_sgn hn g h hL b b') q

/-- Self-crossings correspond for persistent crossings. -/
theorem s7a_side_mem_carrierCrossings (x : Crossing (g.curve (g.sideTime b t)))
    (hx : ¬ ContactAffected M a x.val) (q : Component hn (s7a_sideGeneric g b) S) :
    s7a_cross (s7a_side_hs hn g hL b b') x hx ∈
        carrierCrossings hn (s7a_sideGeneric g b') S' (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q) ↔
      x ∈ carrierCrossings hn (s7a_sideGeneric g b) S q :=
  s7a_mem_carrierCrossings hn _ _ (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' x hx q

end Germ

/-! ### Unit U110-B (helper unit, prefix `s7b_`; PLAN_FINAL §3.3 sliding (2), bigon (1)/(5) discharge, §4
row U110-B): halves ↔ intervals.  Part I — the first-return transport of permutations (the mark-level
engine generalising cor:flat-carriers' one-point skip); part II — labels, remoteness, crossings, visits
and parameters of the halves `λᵢ` against the wall centre; part IV — the support bijections
eq. s7c:sliding-bijection / s7c:eligible-bijection as `Equiv`s on `IsDecomposition`, given the
interlacement-transfer data (`s7b_PivotSplit` / `s7b_SupportSplit`); part III — the half crossings and
visits on a SIDE polygon, the sliding mark map `Mark λ₁ ⊕ Mark λ₂ → Mark Q`, and the transport
structure `s7b_SlidingTransport` whose one field `ret` (the first-return law of the smoothing
successors) yields the carrier correspondence `Component Q S ≃ Component λ₁ S₁ ⊕ Component λ₂ S₂`,
the owners and the carrier crossings / `m_Q`.  Requires `import SM.VertexSides` (lem:wall-sides (V):
`ContactAffected`, `VertexCrossingData`, `vertex_sides` are not reachable from the other imports). -/

section S7BReturn

/-! ### U110-B, part I: the first-return transport of permutations (pure combinatorics).
`ι : β → α` is an injection; `g` is the FIRST-RETURN map of `f` on the image of `ι`: from `ι b`
the iterates of `f` leave the image and come back to it first at `ι (g b)`.  Then the cycles of
`f` through the image are exactly the `ι`-images of the cycles of `g`.  This generalises the
one-point `skipJ` device of cor:flat-carriers (SM/FlatCarriers.lean, `sameCycle_skipJ_iff`) to an
arbitrary skipped set — the marks of a side polygon that have no counterpart on the halves. -/

variable {α β : Type*}

/-- `g` is the first-return map of `f` on the image of `ι`, and every point of `α` reaches the
image. -/
structure s7b_ReturnTransport (f : Equiv.Perm α) (g : Equiv.Perm β) (ι : β → α) : Prop where
  inj : Function.Injective ι
  step : ∀ b : β, ∃ k : ℕ, 0 < k ∧ (f ^ k) (ι b) = ι (g b) ∧
    ∀ j : ℕ, 0 < j → j < k → (f ^ j) (ι b) ∉ Set.range ι
  hit : ∀ a : α, ∃ j : ℕ, (f ^ j) a ∈ Set.range ι

namespace s7b_ReturnTransport

variable {f : Equiv.Perm α} {g : Equiv.Perm β} {ι : β → α}

/-- One `g`-step is realised by a positive power of `f` on the image. -/
theorem sameCycle_step (h : s7b_ReturnTransport f g ι) (b : β) :
    f.SameCycle (ι b) (ι (g b)) := by
  obtain ⟨k, -, hk, -⟩ := h.step b
  rw [← hk]
  exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)

theorem sameCycle_pow_of (h : s7b_ReturnTransport f g ι) (b : β) (m : ℕ) :
    f.SameCycle (ι b) (ι ((g ^ m) b)) := by
  induction m with
  | zero => simp only [pow_zero, Equiv.Perm.coe_one, id_eq]; exact Equiv.Perm.SameCycle.refl _ _
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (h.sameCycle_step _)

/-- Cycles of `g` are carried into cycles of `f`. -/
theorem sameCycle_of [Finite β] (h : s7b_ReturnTransport f g ι) {b b' : β}
    (hb : g.SameCycle b b') : f.SameCycle (ι b) (ι b') := by
  obtain ⟨m, -, hm⟩ := hb.exists_pow_eq'
  rw [← hm]
  exact h.sameCycle_pow_of b m

/-- The converse, by strong induction on the number of `f`-steps: an `f`-iterate of `ι b` that
lands in the image is a `g`-iterate of `b`. -/
theorem sameCycle_of_pow_eq (h : s7b_ReturnTransport f g ι) :
    ∀ (m : ℕ) (b b' : β), (f ^ m) (ι b) = ι b' → g.SameCycle b b' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro b b' hm
    obtain ⟨k, hk0, hk, hgap⟩ := h.step b
    rcases Nat.lt_or_ge m k with hmk | hmk
    · rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hm
        rw [h.inj hm]
      · exact absurd ⟨b', hm.symm⟩ (hgap m hm0 hmk)
    · have h1 : (f ^ (m - k)) (ι (g b)) = ι b' := by
        rw [← hk, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hmk]
        exact hm
      have h2 := ih (m - k) (by omega) (g b) b' h1
      exact Equiv.Perm.sameCycle_apply_left.mp h2

/-- Two image points lie on one `f`-cycle iff their preimages lie on one `g`-cycle. -/
theorem sameCycle_iff [Finite α] [Finite β] (h : s7b_ReturnTransport f g ι) (b b' : β) :
    f.SameCycle (ι b) (ι b') ↔ g.SameCycle b b' := by
  constructor
  · intro hb
    obtain ⟨m, -, hm⟩ := hb.exists_pow_eq'
    exact h.sameCycle_of_pow_eq m b b' hm
  · exact h.sameCycle_of

/-- The induced map on cycle spaces (`Quotient` of `SameCycle`), `⟦b⟧ ↦ ⟦ι b⟧`. -/
def cycleMap [Finite β] (h : s7b_ReturnTransport f g ι) :
    Quotient (Equiv.Perm.SameCycle.setoid g) → Quotient (Equiv.Perm.SameCycle.setoid f) :=
  Quotient.lift (fun b => (Quotient.mk (Equiv.Perm.SameCycle.setoid f) (ι b)))
    (fun _ _ hb => Quotient.sound (h.sameCycle_of hb))

theorem cycleMap_mk [Finite β] (h : s7b_ReturnTransport f g ι) (b : β) :
    h.cycleMap (Quotient.mk (Equiv.Perm.SameCycle.setoid g) b) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid f) (ι b) := rfl

theorem cycleMap_bijective [Finite α] [Finite β] (h : s7b_ReturnTransport f g ι) :
    Function.Bijective h.cycleMap := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h b =>
      induction y using Quotient.inductionOn with
      | h b' =>
        intro he
        rw [cycleMap_mk, cycleMap_mk] at he
        exact Quotient.sound ((h.sameCycle_iff b b').mp (Quotient.exact he))
  · intro x
    induction x using Quotient.inductionOn with
    | h a =>
      obtain ⟨j, b, hb⟩ := h.hit a
      refine ⟨Quotient.mk _ b, ?_⟩
      rw [cycleMap_mk, hb]
      exact Quotient.sound (Equiv.Perm.sameCycle_pow_left.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- **The cycle spaces correspond**: `Quotient (SameCycle g) ≃ Quotient (SameCycle f)`, sending
`⟦b⟧` to `⟦ι b⟧`. -/
def cycleEquiv [Finite α] [Finite β] (h : s7b_ReturnTransport f g ι) :
    Quotient (Equiv.Perm.SameCycle.setoid g) ≃ Quotient (Equiv.Perm.SameCycle.setoid f) :=
  Equiv.ofBijective h.cycleMap h.cycleMap_bijective

theorem cycleEquiv_mk [Finite α] [Finite β] (h : s7b_ReturnTransport f g ι) (b : β) :
    h.cycleEquiv (Quotient.mk (Equiv.Perm.SameCycle.setoid g) b) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid f) (ι b) := rfl

/-- The class of an arbitrary point of `α` is the class of the first image point it reaches. -/
theorem mk_eq_of_pow_eq (_h : s7b_ReturnTransport f g ι) (a : α) (j : ℕ) (b : β)
    (hb : (f ^ j) a = ι b) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid f) a =
      Quotient.mk (Equiv.Perm.SameCycle.setoid f) (ι b) := by
  rw [← hb]
  exact Quotient.sound (Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _))

end s7b_ReturnTransport

/-! Sum types: the cycles of `sumCongr g₁ g₂` are the cycles of `g₁` and of `g₂`. -/

variable {β₁ β₂ : Type*}

theorem s7b_sumCongr_pow_inl (g₁ : Equiv.Perm β₁) (g₂ : Equiv.Perm β₂) (k : ℕ) (x : β₁) :
    ((Equiv.Perm.sumCongr g₁ g₂) ^ k) (Sum.inl x) = Sum.inl ((g₁ ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]; rfl

theorem s7b_sumCongr_pow_inr (g₁ : Equiv.Perm β₁) (g₂ : Equiv.Perm β₂) (k : ℕ) (y : β₂) :
    ((Equiv.Perm.sumCongr g₁ g₂) ^ k) (Sum.inr y) = Sum.inr ((g₂ ^ k) y) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]; rfl

theorem s7b_sumCongr_sameCycle_inl [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (x y : β₁) :
    (Equiv.Perm.sumCongr g₁ g₂).SameCycle (Sum.inl x) (Sum.inl y) ↔ g₁.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
    rw [s7b_sumCongr_pow_inl] at hm
    exact ⟨m, by simpa using Sum.inl.inj hm⟩
  · intro h
    obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
    exact ⟨m, by rw [zpow_natCast, s7b_sumCongr_pow_inl, hm]⟩

theorem s7b_sumCongr_sameCycle_inr [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (x y : β₂) :
    (Equiv.Perm.sumCongr g₁ g₂).SameCycle (Sum.inr x) (Sum.inr y) ↔ g₂.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
    rw [s7b_sumCongr_pow_inr] at hm
    exact ⟨m, by simpa using Sum.inr.inj hm⟩
  · intro h
    obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
    exact ⟨m, by rw [zpow_natCast, s7b_sumCongr_pow_inr, hm]⟩

theorem s7b_sumCongr_not_sameCycle [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (x : β₁) (y : β₂) :
    ¬ (Equiv.Perm.sumCongr g₁ g₂).SameCycle (Sum.inl x) (Sum.inr y) := by
  intro h
  obtain ⟨m, -, hm⟩ := h.exists_pow_eq'
  rw [s7b_sumCongr_pow_inl] at hm
  exact Sum.inl_ne_inr hm

/-- The cycle space of a disjoint union of permutations is the disjoint union of the cycle
spaces. -/
def s7b_sumCongr_cycleEquiv [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁) (g₂ : Equiv.Perm β₂) :
    Quotient (Equiv.Perm.SameCycle.setoid (Equiv.Perm.sumCongr g₁ g₂)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid g₁) ⊕ Quotient (Equiv.Perm.SameCycle.setoid g₂) where
  toFun := Quotient.lift
    (fun z => match z with
      | Sum.inl x => Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid g₁) x)
      | Sum.inr y => Sum.inr (Quotient.mk (Equiv.Perm.SameCycle.setoid g₂) y))
    (by
      intro z z' hz
      cases z with
      | inl x =>
        cases z' with
        | inl x' =>
          exact congrArg Sum.inl (Quotient.sound ((s7b_sumCongr_sameCycle_inl g₁ g₂ x x').mp hz))
        | inr y' => exact absurd hz (s7b_sumCongr_not_sameCycle g₁ g₂ x y')
      | inr y =>
        cases z' with
        | inl x' => exact absurd hz.symm (s7b_sumCongr_not_sameCycle g₁ g₂ x' y)
        | inr y' =>
          exact congrArg Sum.inr (Quotient.sound ((s7b_sumCongr_sameCycle_inr g₁ g₂ y y').mp hz)))
  invFun := fun w => match w with
    | Sum.inl c => Quotient.lift (fun x => Quotient.mk _ (Sum.inl x))
        (fun x x' hx => Quotient.sound ((s7b_sumCongr_sameCycle_inl g₁ g₂ x x').mpr hx)) c
    | Sum.inr c => Quotient.lift (fun y => Quotient.mk _ (Sum.inr y))
        (fun y y' hy => Quotient.sound ((s7b_sumCongr_sameCycle_inr g₁ g₂ y y').mpr hy)) c
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h z => cases z <;> rfl
  right_inv := by
    intro w
    cases w with
    | inl c => induction c using Quotient.inductionOn with | h x => rfl
    | inr c => induction c using Quotient.inductionOn with | h y => rfl

theorem s7b_sumCongr_cycleEquiv_inl [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (x : β₁) :
    s7b_sumCongr_cycleEquiv g₁ g₂ (Quotient.mk _ (Sum.inl x)) =
      Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid g₁) x) := rfl

theorem s7b_sumCongr_cycleEquiv_inr [Finite β₁] [Finite β₂] (g₁ : Equiv.Perm β₁)
    (g₂ : Equiv.Perm β₂) (y : β₂) :
    s7b_sumCongr_cycleEquiv g₁ g₂ (Quotient.mk _ (Sum.inr y)) =
      Sum.inr (Quotient.mk (Equiv.Perm.SameCycle.setoid g₂) y) := rfl

end S7BReturn

section S7BHalves

/-! ### U110-B, part II: labels, remoteness, crossings and visits of the halves vs the centre.
The halves `λ₁ = firstHalf P M a`, `λ₂ = secondHalf P M a` (def:deletion-halves) live on the wall
centre `P`; their edge labels are the cyclic ranges `firstHalfIndex M a = cyclicRangeIndex M`
(edges `M, …, a`, the last one `-1 ↦ a` being the cut `[μ_a, μ_M] ⊂ E_a`) and
`secondHalfEdgeIndex M a = cyclicRangeIndex a` (edges `a, a+1, …, M-1`, the first one `0 ↦ a`
being the cut `[μ_M, μ_{a+1}] ⊂ E_a`).  A crossing of a half is a crossing of the centre with both
labels in the range and (on a cut edge) the meeting point in the cut; the only adjacent pair of a
half that maps to a REMOTE pair of the centre is its wrap-around pair, whose image is the
contact-affected pair `{a, M}` (first half) / `{a, M-1}` (second half). -/

omit [NeZero n] in
theorem s7b_adjacent_iff {k : ℕ} (i j : ZMod k) :
    adjacent i j ↔ j = i ∨ j = i + 1 ∨ i = j + 1 := by
  unfold adjacent
  constructor
  · rintro (h | h | h)
    · right; right; linear_combination -h
    · left; linear_combination h
    · right; left; linear_combination h
  · rintro (h | h | h)
    · right; left; rw [h]; ring
    · right; right; rw [h]; ring
    · left; rw [h]; ring

omit [NeZero n] in
theorem s7b_adjacent_zero_neg_one {k : ℕ} : adjacent (0 : ZMod k) (-1) := Or.inl (by ring)

omit [NeZero n] in
theorem s7b_adjacent_neg_one_zero {k : ℕ} : adjacent (-1 : ZMod k) 0 := Or.inr (Or.inr (by ring))

theorem s7b_cyclicRange_succ_iff {k : ℕ} [NeZero k] (hk : k < n) (s : ZMod n) (i j : ZMod k) :
    cyclicRangeIndex s j = cyclicRangeIndex s i + 1 ↔ i ≠ -1 ∧ j = i + 1 := by
  have hi := i.val_lt
  have hj := j.val_lt
  constructor
  · intro h
    have h1 : ((j.val : ℕ) : ZMod n) = ((i.val + 1 : ℕ) : ZMod n) := by
      simp only [cyclicRangeIndex] at h
      push_cast
      linear_combination h
    have h2 : j.val = i.val + 1 := by
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    have hi1 : i ≠ -1 := by
      intro he
      have hl := last_index_val_succ (n := k)
      rw [← he] at hl
      omega
    refine ⟨hi1, ZMod.val_injective k ?_⟩
    rw [zmod_val_next_of_ne_last hi1, h2]
  · rintro ⟨hi1, rfl⟩
    exact cyclicRangeIndex_next s hi1

theorem s7b_adjacent_cyclicRange_iff {k : ℕ} [NeZero k] (hk : k < n) (s : ZMod n)
    (i j : ZMod k) :
    adjacent (cyclicRangeIndex s i) (cyclicRangeIndex s j) ↔
      j = i ∨ (i ≠ -1 ∧ j = i + 1) ∨ (j ≠ -1 ∧ i = j + 1) := by
  rw [s7b_adjacent_iff, s7b_cyclicRange_succ_iff hk, s7b_cyclicRange_succ_iff hk,
    (cyclicRangeIndex_injective hk.le s).eq_iff]

omit [NeZero n] in
theorem s7b_zero_ne_neg_one {k : ℕ} [NeZero k] (hk : 2 ≤ k) : (0 : ZMod k) ≠ -1 := by
  intro he
  have hl := last_index_val_succ (n := k)
  rw [← he, ZMod.val_zero] at hl
  omega

omit [NeZero n] in
theorem s7b_one_ne_neg_one {k : ℕ} [NeZero k] (hk : 3 ≤ k) : (1 : ZMod k) ≠ -1 := by
  intro he
  have hl := last_index_val_succ (n := k)
  have : Fact (1 < k) := ⟨by omega⟩
  rw [← he, ZMod.val_one] at hl
  omega

/-- Remoteness along a cyclic range of size `k` (`3 ≤ k < n`): the images of two labels are remote
iff the labels are remote or form the wrap-around pair `{-1, 0}`. -/
theorem s7b_remote_cyclicRange_iff {k : ℕ} [NeZero k] (hk : k < n) (hk3 : 3 ≤ k) (s : ZMod n)
    (i j : ZMod k) :
    remote (cyclicRangeIndex s i) (cyclicRangeIndex s j) ↔
      remote i j ∨ (i = -1 ∧ j = 0) ∨ (j = -1 ∧ i = 0) := by
  unfold remote
  rw [s7b_adjacent_cyclicRange_iff hk, s7b_adjacent_iff]
  constructor
  · intro h
    by_cases h1 : i = -1 ∧ j = 0
    · exact Or.inr (Or.inl h1)
    by_cases h2 : j = -1 ∧ i = 0
    · exact Or.inr (Or.inr h2)
    left
    rintro (hji | hji | hji)
    · exact h (Or.inl hji)
    · apply h; right; left
      refine ⟨?_, hji⟩
      intro hi
      exact h1 ⟨hi, by rw [hji, hi]; ring⟩
    · apply h; right; right
      refine ⟨?_, hji⟩
      intro hj
      exact h2 ⟨hj, by rw [hji, hj]; ring⟩
  · rintro (h | ⟨hi, hj⟩ | ⟨hj, hi⟩) hadj
    · apply h
      rcases hadj with h' | ⟨_, h'⟩ | ⟨_, h'⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rcases hadj with h' | ⟨hi1, _⟩ | ⟨_, h'⟩
      · rw [hi, hj] at h'
        exact s7b_zero_ne_neg_one (by omega) h'
      · exact hi1 hi
      · rw [hi, hj, zero_add] at h'
        exact s7b_one_ne_neg_one hk3 h'.symm
    · rcases hadj with h' | ⟨_, h'⟩ | ⟨hj1, _⟩
      · rw [hi, hj] at h'
        exact s7b_zero_ne_neg_one (by omega) h'.symm
      · rw [hi, hj, zero_add] at h'
        exact s7b_one_ne_neg_one hk3 h'.symm
      · exact hj1 hj

/-! #### The first half `λ₁` -/

theorem s7b_firstHalfSize_lt (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) :
    firstHalfSize M a < n ∧ 3 ≤ firstHalfSize M a := by
  have hb := contactHalfSizes_bounds hn hsep
  omega

theorem s7b_secondHalfSize_lt (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) :
    secondHalfSize M a < n ∧ 3 ≤ secondHalfSize M a := by
  have hb := contactHalfSizes_bounds hn hsep
  omega

theorem s7b_remote_firstHalfIndex_iff (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    (i j : ZMod (firstHalfSize M a)) :
    remote (firstHalfIndex M a i) (firstHalfIndex M a j) ↔
      remote i j ∨ (i = -1 ∧ j = 0) ∨ (j = -1 ∧ i = 0) :=
  s7b_remote_cyclicRange_iff (s7b_firstHalfSize_lt hn hsep).1 (s7b_firstHalfSize_lt hn hsep).2 M i j

theorem s7b_remote_secondHalfEdgeIndex_iff (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) (i j : ZMod (secondHalfSize M a)) :
    remote (secondHalfEdgeIndex M a i) (secondHalfEdgeIndex M a j) ↔
      remote i j ∨ (i = -1 ∧ j = 0) ∨ (j = -1 ∧ i = 0) :=
  s7b_remote_cyclicRange_iff (s7b_secondHalfSize_lt hn hsep).1 (s7b_secondHalfSize_lt hn hsep).2
    a i j

/-- `M - 1` is not an edge label of the first half. -/
theorem s7b_firstHalfIndex_ne_pred (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    (i : ZMod (firstHalfSize M a)) : firstHalfIndex M a i ≠ M - 1 := by
  intro he
  have hr := (firstHalfIndex_range M a (M - 1)).mp ⟨i, he⟩
  have hb := contactHalfSizes_bounds hn hsep
  have hl := last_index_val_succ (n := n)
  have he' : M - 1 - M = (-1 : ZMod n) := by ring
  rw [he'] at hr
  omega

/-- `M` is not an edge label of the second half (its edge labels are `a, …, M-1`). -/
theorem s7b_secondHalfEdgeIndex_ne (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    (i : ZMod (secondHalfSize M a)) : secondHalfEdgeIndex M a i ≠ M := by
  intro he
  have hr := (cyclicRangeIndex_range (secondHalfSize_le M a) a M).mp ⟨i, he⟩
  have hb := contactHalfSizes_bounds hn hsep
  have hc : M - a = (secondHalfSize M a : ZMod n) := (secondHalfSize_cast M a).symm
  rw [hc, ZMod.val_natCast_of_lt (by omega)] at hr
  exact lt_irrefl _ hr

/-- The image of a crossing of `λ₁` is a crossing of the centre. -/
theorem s7b_isCrossing_firstHalf_image (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) {s : Finset (ZMod (firstHalfSize M a))}
    (hs : IsCrossing (firstHalf P M a) s) : IsCrossing P (s.image (firstHalfIndex M a)) := by
  obtain ⟨i, j, rfl, hr, x, hxi, hxj⟩ := hs
  refine ⟨firstHalfIndex M a i, firstHalfIndex M a j, ?_, ?_, x,
    firstHalf_segment_subset hm i hxi, firstHalf_segment_subset hm j hxj⟩
  · rw [Finset.image_insert, Finset.image_singleton]
  · exact (s7b_remote_firstHalfIndex_iff hn hsep i j).mpr (Or.inl hr)

/-- The image of a crossing of `λ₂` is a crossing of the centre. -/
theorem s7b_isCrossing_secondHalf_image (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) {s : Finset (ZMod (secondHalfSize M a))}
    (hs : IsCrossing (secondHalf P M a) s) : IsCrossing P (s.image (secondHalfEdgeIndex M a)) := by
  obtain ⟨i, j, rfl, hr, x, hxi, hxj⟩ := hs
  refine ⟨secondHalfEdgeIndex M a i, secondHalfEdgeIndex M a j, ?_, ?_, x,
    secondHalf_segment_subset hn hsep hm i hxi, secondHalf_segment_subset hn hsep hm j hxj⟩
  · rw [Finset.image_insert, Finset.image_singleton]
  · exact (s7b_remote_secondHalfEdgeIndex_iff hn hsep i j).mpr (Or.inl hr)

/-- The image of a crossing of `λ₁` is never a contact-affected pair. -/
theorem s7b_firstHalf_image_not_affected (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} {s : Finset (ZMod (firstHalfSize M a))}
    (hs : IsCrossing (firstHalf P M a) s) :
    ¬ ContactAffected M a (s.image (firstHalfIndex M a)) := by
  obtain ⟨i, j, rfl, hr, -⟩ := hs
  rw [Finset.image_insert, Finset.image_singleton]
  have hij : i ≠ j := (remote_endpoints i j hr).1.symm
  rintro (h | h)
  · have hmem : M - 1 ∈ ({firstHalfIndex M a i, firstHalfIndex M a j} : Finset (ZMod n)) := by
      rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · exact s7b_firstHalfIndex_ne_pred hn hsep i h'.symm
    · exact s7b_firstHalfIndex_ne_pred hn hsep j h'.symm
  · have hinj := firstHalfIndex_injective M a
    have hi : i = -1 ∨ i = 0 := by
      have hmem : firstHalfIndex M a i ∈ ({a, M} : Finset (ZMod n)) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (hinj (h'.trans (firstHalfIndex_last M a).symm))
      · exact Or.inr (hinj (h'.trans (firstHalfIndex_zero M a).symm))
    have hj : j = -1 ∨ j = 0 := by
      have hmem : firstHalfIndex M a j ∈ ({a, M} : Finset (ZMod n)) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (hinj (h'.trans (firstHalfIndex_last M a).symm))
      · exact Or.inr (hinj (h'.trans (firstHalfIndex_zero M a).symm))
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact hij rfl
    · exact hr s7b_adjacent_neg_one_zero
    · exact hr s7b_adjacent_zero_neg_one
    · exact hij rfl

/-- The image of a crossing of `λ₂` is never a contact-affected pair. -/
theorem s7b_secondHalf_image_not_affected (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n} {s : Finset (ZMod (secondHalfSize M a))}
    (hs : IsCrossing (secondHalf P M a) s) :
    ¬ ContactAffected M a (s.image (secondHalfEdgeIndex M a)) := by
  obtain ⟨i, j, rfl, hr, -⟩ := hs
  rw [Finset.image_insert, Finset.image_singleton]
  have hij : i ≠ j := (remote_endpoints i j hr).1.symm
  rintro (h | h)
  · have hinj := secondHalfEdgeIndex_injective M a
    have hi : i = 0 ∨ i = -1 := by
      have hmem : secondHalfEdgeIndex M a i ∈ ({a, M - 1} : Finset (ZMod n)) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (hinj (h'.trans (secondHalfEdgeIndex_zero M a).symm))
      · exact Or.inr (hinj (h'.trans (secondHalfEdgeIndex_last M a).symm))
    have hj : j = 0 ∨ j = -1 := by
      have hmem : secondHalfEdgeIndex M a j ∈ ({a, M - 1} : Finset (ZMod n)) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (hinj (h'.trans (secondHalfEdgeIndex_zero M a).symm))
      · exact Or.inr (hinj (h'.trans (secondHalfEdgeIndex_last M a).symm))
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact hij rfl
    · exact hr s7b_adjacent_zero_neg_one
    · exact hr s7b_adjacent_neg_one_zero
    · exact hij rfl
  · have hmem : M ∈ ({secondHalfEdgeIndex M a i, secondHalfEdgeIndex M a j} : Finset (ZMod n)) := by
      rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · exact s7b_secondHalfEdgeIndex_ne hn hsep i h'.symm
    · exact s7b_secondHalfEdgeIndex_ne hn hsep j h'.symm

/-! #### Segments of the halves as subsegments of the centre's edges -/

theorem s7b_edgeSegment_firstHalf (P : LabelledTuple n) (M a : ZMod n)
    {i : ZMod (firstHalfSize M a)} (hi : i ≠ -1) :
    edgeSegment (firstHalf P M a) i = edgeSegment P (firstHalfIndex M a i) := by
  ext x
  simp only [edgeSegment, Set.mem_ofPred_eq, edgePoint_firstHalf P M a hi]

theorem s7b_edgeSegment_secondHalf (P : LabelledTuple n) (M a : ZMod n)
    {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    edgeSegment (secondHalf P M a) i = edgeSegment P (secondHalfEdgeIndex M a i) := by
  ext x
  simp only [edgeSegment, Set.mem_ofPred_eq, edgePoint_secondHalf P M a hi]

/-- The cut of `λ₁` is the initial part `[0, r]` of the contact edge `E_a`. -/
theorem s7b_mem_edgeSegment_firstHalf_cut {P : LabelledTuple n} {M a : ZMod n} {r : ℝ}
    (hr : P M = edgePoint P a r) (hr0 : 0 < r) (x : Plane) :
    x ∈ edgeSegment (firstHalf P M a) (-1) ↔ ∃ u : ℝ, 0 ≤ u ∧ u ≤ r ∧ x = edgePoint P a u := by
  simp only [edgeSegment, Set.mem_ofPred_eq, edgePoint_firstHalf_cut hr]
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨r * t, mul_nonneg hr0.le ht0, by nlinarith, rfl⟩
  · rintro ⟨u, hu0, hu1, rfl⟩
    refine ⟨u / r, div_nonneg hu0 hr0.le, (div_le_one hr0).mpr hu1, ?_⟩
    rw [mul_div_cancel₀ u hr0.ne']

/-- The cut of `λ₂` is the final part `[r, 1]` of the contact edge `E_a`. -/
theorem s7b_mem_edgeSegment_secondHalf_cut (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} {r : ℝ} (hr : P M = edgePoint P a r) (hr1 : r < 1) (x : Plane) :
    x ∈ edgeSegment (secondHalf P M a) 0 ↔ ∃ u : ℝ, r ≤ u ∧ u ≤ 1 ∧ x = edgePoint P a u := by
  simp only [edgeSegment, Set.mem_ofPred_eq, edgePoint_secondHalf_cut hn hsep hr]
  have h1r : 0 < 1 - r := by linarith
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨r + (1 - r) * t, by nlinarith, by nlinarith, rfl⟩
  · rintro ⟨u, hu0, hu1, rfl⟩
    refine ⟨(u - r) / (1 - r), div_nonneg (by linarith) h1r.le,
      (div_le_one h1r).mpr (by linarith), ?_⟩
    rw [mul_div_cancel₀ _ h1r.ne']
    ring_nf

/-! #### Crossing and visit maps `λ_i → centre` -/

/-- The crossing of the centre carried by a crossing of `λ₁`. -/
def s7b_firstHalfCrossing (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (c : Crossing (firstHalf P M a)) :
    Crossing P :=
  ⟨c.val.image (firstHalfIndex M a), s7b_isCrossing_firstHalf_image hn hsep hm c.property⟩

/-- The crossing of the centre carried by a crossing of `λ₂`. -/
def s7b_secondHalfCrossing (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (c : Crossing (secondHalf P M a)) :
    Crossing P :=
  ⟨c.val.image (secondHalfEdgeIndex M a), s7b_isCrossing_secondHalf_image hn hsep hm c.property⟩

theorem s7b_firstHalfCrossing_val (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (c : Crossing (firstHalf P M a)) :
    (s7b_firstHalfCrossing hn hsep hm c).val = c.val.image (firstHalfIndex M a) := rfl

theorem s7b_secondHalfCrossing_val (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (c : Crossing (secondHalf P M a)) :
    (s7b_secondHalfCrossing hn hsep hm c).val = c.val.image (secondHalfEdgeIndex M a) := rfl

theorem s7b_firstHalfCrossing_injective (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) :
    Function.Injective (s7b_firstHalfCrossing hn hsep hm) := by
  intro c d h
  exact Subtype.ext (Finset.image_injective (firstHalfIndex_injective M a) (congrArg Subtype.val h))

theorem s7b_secondHalfCrossing_injective (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) :
    Function.Injective (s7b_secondHalfCrossing hn hsep hm) := by
  intro c d h
  exact Subtype.ext
    (Finset.image_injective (secondHalfEdgeIndex_injective M a) (congrArg Subtype.val h))

theorem s7b_firstHalfCrossing_not_affected (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (c : Crossing (firstHalf P M a)) :
    ¬ ContactAffected M a (s7b_firstHalfCrossing hn hsep hm c).val :=
  s7b_firstHalf_image_not_affected hn hsep c.property

theorem s7b_secondHalfCrossing_not_affected (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (c : Crossing (secondHalf P M a)) :
    ¬ ContactAffected M a (s7b_secondHalfCrossing hn hsep hm c).val :=
  s7b_secondHalf_image_not_affected hn hsep c.property

/-- The visit of the centre carried by a visit of `λ₁` (same crossing image, image edge label). -/
def s7b_firstHalfVisit (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (firstHalf P M a)) : Visit P :=
  ⟨s7b_firstHalfCrossing hn hsep hm v.1,
    ⟨firstHalfIndex M a v.2.val, Finset.mem_image_of_mem _ v.2.property⟩⟩

/-- The visit of the centre carried by a visit of `λ₂`. -/
def s7b_secondHalfVisit (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (secondHalf P M a)) : Visit P :=
  ⟨s7b_secondHalfCrossing hn hsep hm v.1,
    ⟨secondHalfEdgeIndex M a v.2.val, Finset.mem_image_of_mem _ v.2.property⟩⟩

theorem s7b_firstHalfVisit_fst (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (firstHalf P M a)) :
    (s7b_firstHalfVisit hn hsep hm v).1 = s7b_firstHalfCrossing hn hsep hm v.1 := rfl

theorem s7b_firstHalfVisit_edge (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (firstHalf P M a)) :
    (s7b_firstHalfVisit hn hsep hm v).2.val = firstHalfIndex M a v.2.val := rfl

theorem s7b_secondHalfVisit_fst (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (secondHalf P M a)) :
    (s7b_secondHalfVisit hn hsep hm v).1 = s7b_secondHalfCrossing hn hsep hm v.1 := rfl

theorem s7b_secondHalfVisit_edge (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (secondHalf P M a)) :
    (s7b_secondHalfVisit hn hsep hm v).2.val = secondHalfEdgeIndex M a v.2.val := rfl

theorem s7b_firstHalfVisit_injective (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) :
    Function.Injective (s7b_firstHalfVisit hn hsep hm) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hc : c = d := s7b_firstHalfCrossing_injective hn hsep hm (congrArg Sigma.fst h)
  subst hc
  have hi : firstHalfIndex M a i.val = firstHalfIndex M a j.val := by
    have := congrArg (fun w : Visit P => w.2.val) h
    exact this
  rw [Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (Subtype.ext (firstHalfIndex_injective M a hi))⟩

theorem s7b_secondHalfVisit_injective (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) :
    Function.Injective (s7b_secondHalfVisit hn hsep hm) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hc : c = d := s7b_secondHalfCrossing_injective hn hsep hm (congrArg Sigma.fst h)
  subst hc
  have hi : secondHalfEdgeIndex M a i.val = secondHalfEdgeIndex M a j.val := by
    have := congrArg (fun w : Visit P => w.2.val) h
    exact this
  rw [Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (Subtype.ext (secondHalfEdgeIndex_injective M a hi))⟩

/-- The visit maps commute with the crossing pairing `visitTwin`. -/
theorem s7b_firstHalfVisit_visitTwin (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (firstHalf P M a)) :
    s7b_firstHalfVisit hn hsep hm (visitTwin v) = visitTwin (s7b_firstHalfVisit hn hsep hm v) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne v (s7b_firstHalfVisit_injective hn hsep hm h)

theorem s7b_secondHalfVisit_visitTwin (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (v : Visit (secondHalf P M a)) :
    s7b_secondHalfVisit hn hsep hm (visitTwin v) =
      visitTwin (s7b_secondHalfVisit hn hsep hm v) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne v (s7b_secondHalfVisit_injective hn hsep hm h)

/-! #### Meeting points and parameters -/

/-- At the centre, two remote unaffected edges meet in at most one point (transversality,
`contact_unaffected_pair_geometry`). -/
theorem s7b_centre_meet_unique (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P : LabelledTuple n} (hz : pointZeroTriples P = {contactSupport M a}) {i j : ZMod n}
    (hr : remote i j) (hnot : ¬ ContactAffected M a {i, j}) {x y : Plane}
    (hxi : x ∈ edgeSegment P i) (hxj : x ∈ edgeSegment P j)
    (hyi : y ∈ edgeSegment P i) (hyj : y ∈ edgeSegment P j) : x = y := by
  have hd := (contact_unaffected_pair_geometry hn hsep hz hr hnot hxi hxj).2.2
  obtain ⟨s, -, -, hs⟩ := hxi
  obtain ⟨t, -, -, ht⟩ := hxj
  obtain ⟨s', -, -, hs'⟩ := hyi
  obtain ⟨t', -, -, ht'⟩ := hyj
  have h1 : P i + s • edge P i = P j + t • edge P j := hs.symm.trans ht
  have h2 : P i + s' • edge P i = P j + t' • edge P j := hs'.symm.trans ht'
  have := (intersection_parameters_unique hd h1 h2).1
  rw [hs, hs', this]

/-- The crossing point of a crossing of `λ₁` is the crossing point of its image. -/
theorem s7b_crossingPoint_firstHalfCrossing (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (c : Crossing (firstHalf P M a)) :
    crossingPoint (s7b_firstHalfCrossing hn hsep hm c) = crossingPoint c := by
  obtain ⟨i, j, hs, hr, -⟩ := c.property
  have hr' : remote (firstHalfIndex M a i) (firstHalfIndex M a j) :=
    (s7b_remote_firstHalfIndex_iff hn hsep i j).mpr (Or.inl hr)
  have hval : (s7b_firstHalfCrossing hn hsep hm c).val =
      {firstHalfIndex M a i, firstHalfIndex M a j} := by
    rw [s7b_firstHalfCrossing_val, hs, Finset.image_insert, Finset.image_singleton]
  have hnot : ¬ ContactAffected M a {firstHalfIndex M a i, firstHalfIndex M a j} := by
    rw [← hval]; exact s7b_firstHalfCrossing_not_affected hn hsep hm c
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  have hi' : firstHalfIndex M a i ∈ (s7b_firstHalfCrossing hn hsep hm c).val := by rw [hval]; simp
  have hj' : firstHalfIndex M a j ∈ (s7b_firstHalfCrossing hn hsep hm c).val := by rw [hval]; simp
  exact s7b_centre_meet_unique hn hsep hz hr' hnot (crossingPoint_mem _ _ hi') (crossingPoint_mem _ _ hj')
    (firstHalf_segment_subset hm i (crossingPoint_mem c i hi))
    (firstHalf_segment_subset hm j (crossingPoint_mem c j hj))

theorem s7b_crossingPoint_secondHalfCrossing (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (c : Crossing (secondHalf P M a)) :
    crossingPoint (s7b_secondHalfCrossing hn hsep hm c) = crossingPoint c := by
  obtain ⟨i, j, hs, hr, -⟩ := c.property
  have hr' : remote (secondHalfEdgeIndex M a i) (secondHalfEdgeIndex M a j) :=
    (s7b_remote_secondHalfEdgeIndex_iff hn hsep i j).mpr (Or.inl hr)
  have hval : (s7b_secondHalfCrossing hn hsep hm c).val =
      {secondHalfEdgeIndex M a i, secondHalfEdgeIndex M a j} := by
    rw [s7b_secondHalfCrossing_val, hs, Finset.image_insert, Finset.image_singleton]
  have hnot : ¬ ContactAffected M a {secondHalfEdgeIndex M a i, secondHalfEdgeIndex M a j} := by
    rw [← hval]; exact s7b_secondHalfCrossing_not_affected hn hsep hm c
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  have hi' : secondHalfEdgeIndex M a i ∈ (s7b_secondHalfCrossing hn hsep hm c).val := by
    rw [hval]; simp
  have hj' : secondHalfEdgeIndex M a j ∈ (s7b_secondHalfCrossing hn hsep hm c).val := by
    rw [hval]; simp
  exact s7b_centre_meet_unique hn hsep hz hr' hnot (crossingPoint_mem _ _ hi')
    (crossingPoint_mem _ _ hj')
    (secondHalf_segment_subset hn hsep hm i (crossingPoint_mem c i hi))
    (secondHalf_segment_subset hn hsep hm j (crossingPoint_mem c j hj))

/-- Off the cut, a visit of `λ₁` and its image have the same parameter. -/
theorem s7b_visitParameter_firstHalfVisit (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (v : Visit (firstHalf P M a)) (hv : v.2.val ≠ -1) :
    visitParameter (s7b_firstHalfVisit hn hsep hm v) = visitParameter v := by
  have hn5 := contactSeparated_size hn hsep
  have h1 : crossingPoint (s7b_firstHalfCrossing hn hsep hm v.1) =
      edgePoint P (firstHalfIndex M a v.2.val) (visitParameter (s7b_firstHalfVisit hn hsep hm v)) :=
    (crossingParameter_spec (s7b_firstHalfVisit hn hsep hm v).1
      (s7b_firstHalfVisit hn hsep hm v).2.val (s7b_firstHalfVisit hn hsep hm v).2.property).2.2
  have h2 : crossingPoint v.1 = edgePoint (firstHalf P M a) v.2.val (visitParameter v) :=
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2
  rw [s7b_crossingPoint_firstHalfCrossing hn hsep hz hm] at h1
  rw [edgePoint_firstHalf P M a hv] at h2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz _) (h1.symm.trans h2)

/-- On the cut of `λ₁`, the image parameter on `E_a` is `r · t` (`t` the parameter on the cut). -/
theorem s7b_visitParameter_firstHalfVisit_cut (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a) {r : ℝ}
    (hr : P M = edgePoint P a r) (v : Visit (firstHalf P M a)) (hv : v.2.val = -1) :
    visitParameter (s7b_firstHalfVisit hn hsep hm v) = r * visitParameter v := by
  have hn5 := contactSeparated_size hn hsep
  have h1 : crossingPoint (s7b_firstHalfCrossing hn hsep hm v.1) =
      edgePoint P (firstHalfIndex M a v.2.val) (visitParameter (s7b_firstHalfVisit hn hsep hm v)) :=
    (crossingParameter_spec (s7b_firstHalfVisit hn hsep hm v).1
      (s7b_firstHalfVisit hn hsep hm v).2.val (s7b_firstHalfVisit hn hsep hm v).2.property).2.2
  have h2 : crossingPoint v.1 = edgePoint (firstHalf P M a) v.2.val (visitParameter v) :=
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2
  rw [s7b_crossingPoint_firstHalfCrossing hn hsep hz hm, hv, firstHalfIndex_last] at h1
  rw [hv, edgePoint_firstHalf_cut hr] at h2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz _) (h1.symm.trans h2)

/-- Off the cut, a visit of `λ₂` and its image have the same parameter. -/
theorem s7b_visitParameter_secondHalfVisit (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (v : Visit (secondHalf P M a)) (hv : v.2.val ≠ 0) :
    visitParameter (s7b_secondHalfVisit hn hsep hm v) = visitParameter v := by
  have hn5 := contactSeparated_size hn hsep
  have h1 : crossingPoint (s7b_secondHalfCrossing hn hsep hm v.1) =
      edgePoint P (secondHalfEdgeIndex M a v.2.val)
        (visitParameter (s7b_secondHalfVisit hn hsep hm v)) :=
    (crossingParameter_spec (s7b_secondHalfVisit hn hsep hm v).1
      (s7b_secondHalfVisit hn hsep hm v).2.val (s7b_secondHalfVisit hn hsep hm v).2.property).2.2
  have h2 : crossingPoint v.1 = edgePoint (secondHalf P M a) v.2.val (visitParameter v) :=
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2
  rw [s7b_crossingPoint_secondHalfCrossing hn hsep hz hm] at h1
  rw [edgePoint_secondHalf P M a hv] at h2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz _) (h1.symm.trans h2)

/-- On the cut of `λ₂`, the image parameter on `E_a` is `r + (1 − r) t`. -/
theorem s7b_visitParameter_secondHalfVisit_cut (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a) {r : ℝ}
    (hr : P M = edgePoint P a r) (v : Visit (secondHalf P M a)) (hv : v.2.val = 0) :
    visitParameter (s7b_secondHalfVisit hn hsep hm v) = r + (1 - r) * visitParameter v := by
  have hn5 := contactSeparated_size hn hsep
  have h1 : crossingPoint (s7b_secondHalfCrossing hn hsep hm v.1) =
      edgePoint P (secondHalfEdgeIndex M a v.2.val)
        (visitParameter (s7b_secondHalfVisit hn hsep hm v)) :=
    (crossingParameter_spec (s7b_secondHalfVisit hn hsep hm v).1
      (s7b_secondHalfVisit hn hsep hm v).2.val (s7b_secondHalfVisit hn hsep hm v).2.property).2.2
  have h2 : crossingPoint v.1 = edgePoint (secondHalf P M a) v.2.val (visitParameter v) :=
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2
  rw [s7b_crossingPoint_secondHalfCrossing hn hsep hz hm, hv, secondHalfEdgeIndex_zero] at h1
  rw [hv, edgePoint_secondHalf_cut hn hsep hr] at h2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz _) (h1.symm.trans h2)

end S7BHalves

section S7BSupports

/-! ### U110-B, part IV: the support bijections (eq. s7c:sliding-bijection, s7c:eligible-bijection)
as a purely combinatorial splitting of independent sets.  `R` is the interlacement relation of the
side polygon, `R₁, R₂` those of the halves, `ι₁, ι₂` the half crossing maps: independent sets of `R`
contained in the two (disjoint) images — or containing the pivot `x₋` and otherwise contained in the
images — correspond to pairs of independent sets of `R₁`, `R₂`.  The geometric inputs (interlacement
is preserved by `ιᵢ`, no cross-interlacement, the interval dichotomy for the non-neighbours of `x₋`)
are the fields of `s7b_SupportSplit` / `s7b_PivotSplit`. -/

variable {γ γ₁ γ₂ : Type*}

/-- Independence of a finite set for a relation (`IsDecomposition` unfolds to this shape for
`R = Interlaces`, `mem_independentSupports_iff`). -/
def s7b_Indep (R : γ → γ → Prop) (S : Finset γ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y

theorem s7b_isDecomposition_iff_indep {n : ℕ} (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : IsDecomposition hn hP S ↔ s7b_Indep (Interlaces hn hP) S :=
  mem_independentSupports_iff hn hP S

/-- The data of two disjoint injective images on which `R` restricts to `R₁`, `R₂`, with no
interlacement across. -/
structure s7b_SupportSplit (R : γ → γ → Prop) (R₁ : γ₁ → γ₁ → Prop) (R₂ : γ₂ → γ₂ → Prop)
    (ι₁ : γ₁ → γ) (ι₂ : γ₂ → γ) : Prop where
  inj₁ : Function.Injective ι₁
  inj₂ : Function.Injective ι₂
  disjoint : ∀ c₁ c₂, ι₁ c₁ ≠ ι₂ c₂
  rel₁ : ∀ c c', R (ι₁ c) (ι₁ c') ↔ R₁ c c'
  rel₂ : ∀ c c', R (ι₂ c) (ι₂ c') ↔ R₂ c c'
  cross : ∀ c₁ c₂, ¬ R (ι₁ c₁) (ι₂ c₂)
  cross' : ∀ c₁ c₂, ¬ R (ι₂ c₂) (ι₁ c₁)

/-- The preimage of a support under an injection, as a finite set. -/
def s7b_pre [Fintype γ₁] (ι : γ₁ → γ) (S : Finset γ) : Finset γ₁ := Finset.univ.filter fun c => ι c ∈ S

theorem s7b_mem_pre [Fintype γ₁] (ι : γ₁ → γ) (S : Finset γ) (c : γ₁) : c ∈ s7b_pre ι S ↔ ι c ∈ S := by
  simp only [s7b_pre, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The image of a support under an injection. -/
def s7b_img {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ₁) : Finset γ := S.map ⟨ι, hι⟩

theorem s7b_mem_img {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ₁) (y : γ) :
    y ∈ s7b_img hι S ↔ ∃ c ∈ S, ι c = y := by
  simp only [s7b_img, Finset.mem_map, Function.Embedding.coeFn_mk]

theorem s7b_apply_mem_img {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ₁) (c : γ₁) :
    ι c ∈ s7b_img hι S ↔ c ∈ S := by
  rw [s7b_mem_img]
  constructor
  · rintro ⟨c', hc', he⟩
    rw [hι he] at hc'
    exact hc'
  · intro hc
    exact ⟨c, hc, rfl⟩

theorem s7b_pre_img [Fintype γ₁] {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ₁) :
    s7b_pre ι (s7b_img hι S) = S := by
  ext c
  rw [s7b_mem_pre, s7b_apply_mem_img]

theorem s7b_img_pre_subset [Fintype γ₁] {ι : γ₁ → γ} (hι : Function.Injective ι) (S : Finset γ) :
    s7b_img hι (s7b_pre ι S) ⊆ S := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := (s7b_mem_img hι _ y).mp hy
  exact (s7b_mem_pre ι S c).mp hc

namespace s7b_SupportSplit

variable {R : γ → γ → Prop} {R₁ : γ₁ → γ₁ → Prop} {R₂ : γ₂ → γ₂ → Prop} {ι₁ : γ₁ → γ} {ι₂ : γ₂ → γ}

theorem indep_pre₁ [Fintype γ₁] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) {S : Finset γ} (hS : s7b_Indep R S) :
    s7b_Indep R₁ (s7b_pre ι₁ S) := by
  intro c hc c' hc' hne hR
  rw [s7b_mem_pre] at hc hc'
  exact hS _ hc _ hc' (fun he => hne (h.inj₁ he)) ((h.rel₁ c c').mpr hR)

theorem indep_pre₂ [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) {S : Finset γ} (hS : s7b_Indep R S) :
    s7b_Indep R₂ (s7b_pre ι₂ S) := by
  intro c hc c' hc' hne hR
  rw [s7b_mem_pre] at hc hc'
  exact hS _ hc _ hc' (fun he => hne (h.inj₂ he)) ((h.rel₂ c c').mpr hR)

/-- The union of the two images of independent half supports. -/
def joinSupport (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) (S₁ : Finset γ₁) (S₂ : Finset γ₂) :
    Finset γ :=
  s7b_img h.inj₁ S₁ ∪ s7b_img h.inj₂ S₂

theorem mem_joinSupport (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) (S₁ : Finset γ₁) (S₂ : Finset γ₂)
    (y : γ) : y ∈ h.joinSupport S₁ S₂ ↔ (∃ c ∈ S₁, ι₁ c = y) ∨ ∃ c ∈ S₂, ι₂ c = y := by
  simp only [joinSupport, Finset.mem_union, s7b_mem_img]

theorem indep_joinSupport (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) {S₁ : Finset γ₁} {S₂ : Finset γ₂}
    (h₁ : s7b_Indep R₁ S₁) (h₂ : s7b_Indep R₂ S₂) : s7b_Indep R (h.joinSupport S₁ S₂) := by
  intro y hy y' hy' hne hR
  rw [mem_joinSupport] at hy hy'
  rcases hy with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;> rcases hy' with ⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩
  · exact h₁ c hc c' hc' (fun he => hne (congrArg ι₁ he)) ((h.rel₁ c c').mp hR)
  · exact h.cross c c' hR
  · exact h.cross' c' c hR
  · exact h₂ c hc c' hc' (fun he => hne (congrArg ι₂ he)) ((h.rel₂ c c').mp hR)

theorem pre₁_joinSupport [Fintype γ₁] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) (S₁ : Finset γ₁) (S₂ : Finset γ₂) :
    s7b_pre ι₁ (h.joinSupport S₁ S₂) = S₁ := by
  ext c
  rw [s7b_mem_pre, mem_joinSupport]
  constructor
  · rintro (⟨c', hc', he⟩ | ⟨c', -, he⟩)
    · rw [h.inj₁ he] at hc'; exact hc'
    · exact absurd he.symm (h.disjoint c c')
  · intro hc
    exact Or.inl ⟨c, hc, rfl⟩

theorem pre₂_joinSupport [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) (S₁ : Finset γ₁) (S₂ : Finset γ₂) :
    s7b_pre ι₂ (h.joinSupport S₁ S₂) = S₂ := by
  ext c
  rw [s7b_mem_pre, mem_joinSupport]
  constructor
  · rintro (⟨c', -, he⟩ | ⟨c', hc', he⟩)
    · exact absurd he (h.disjoint c' c)
    · rw [h.inj₂ he] at hc'; exact hc'
  · intro hc
    exact Or.inr ⟨c, hc, rfl⟩

theorem joinSupport_pre [Fintype γ₁] [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) {S : Finset γ}
    (hS : ∀ y ∈ S, y ∈ Set.range ι₁ ∪ Set.range ι₂) :
    h.joinSupport (s7b_pre ι₁ S) (s7b_pre ι₂ S) = S := by
  ext y
  rw [mem_joinSupport]
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact (s7b_mem_pre ι₁ S c).mp hc
    · exact (s7b_mem_pre ι₂ S c).mp hc
  · intro hy
    rcases hS y hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨c, (s7b_mem_pre ι₁ S c).mpr hy, rfl⟩
    · exact Or.inr ⟨c, (s7b_mem_pre ι₂ S c).mpr hy, rfl⟩

/-- **eq. s7c:eligible-bijection**, abstractly: independent sets of `R` inside the two images
correspond to pairs of independent sets of `R₁`, `R₂`. -/
def eligibleEquiv [Fintype γ₁] [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂) :
    {S : Finset γ // s7b_Indep R S ∧ ∀ y ∈ S, y ∈ Set.range ι₁ ∪ Set.range ι₂} ≃
      {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂} where
  toFun S := (⟨s7b_pre ι₁ S.1, h.indep_pre₁ S.2.1⟩, ⟨s7b_pre ι₂ S.1, h.indep_pre₂ S.2.1⟩)
  invFun p := ⟨h.joinSupport p.1.1 p.2.1, h.indep_joinSupport p.1.2 p.2.2, by
    intro y hy
    rcases (h.mem_joinSupport _ _ y).mp hy with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩⟩
  left_inv S := Subtype.ext (h.joinSupport_pre S.2.2)
  right_inv p := by
    ext1
    · exact Subtype.ext (h.pre₁_joinSupport _ _)
    · exact Subtype.ext (h.pre₂_joinSupport _ _)

theorem eligibleEquiv_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂)
    (S : {S : Finset γ // s7b_Indep R S ∧ ∀ y ∈ S, y ∈ Set.range ι₁ ∪ Set.range ι₂}) :
    ((h.eligibleEquiv S).1.1 = s7b_pre ι₁ S.1) ∧ ((h.eligibleEquiv S).2.1 = s7b_pre ι₂ S.1) :=
  ⟨rfl, rfl⟩

theorem eligibleEquiv_symm_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    (h.eligibleEquiv.symm p).1 = h.joinSupport p.1.1 p.2.1 := rfl

end s7b_SupportSplit

/-- The sliding data: a split plus a pivot `x` (the contact crossing `x₋`) outside both images,
interlacing nothing in them, such that every other non-neighbour of `x` lies in an image
(the two visits of `x` cut the traversal into the two half intervals). -/
structure s7b_PivotSplit (R : γ → γ → Prop) (R₁ : γ₁ → γ₁ → Prop) (R₂ : γ₂ → γ₂ → Prop)
    (ι₁ : γ₁ → γ) (ι₂ : γ₂ → γ) (x : γ) : Prop where
  split : s7b_SupportSplit R R₁ R₂ ι₁ ι₂
  x_not₁ : ∀ c, ι₁ c ≠ x
  x_not₂ : ∀ c, ι₂ c ≠ x
  x_free₁ : ∀ c, ¬ R x (ι₁ c) ∧ ¬ R (ι₁ c) x
  x_free₂ : ∀ c, ¬ R x (ι₂ c) ∧ ¬ R (ι₂ c) x
  x_split : ∀ y, y ≠ x → ¬ R x y → ¬ R y x → y ∈ Set.range ι₁ ∪ Set.range ι₂

namespace s7b_PivotSplit

variable {R : γ → γ → Prop} {R₁ : γ₁ → γ₁ → Prop} {R₂ : γ₂ → γ₂ → Prop} {ι₁ : γ₁ → γ} {ι₂ : γ₂ → γ}
  {x : γ}

theorem indep_insert (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) {S₁ : Finset γ₁} {S₂ : Finset γ₂}
    (h₁ : s7b_Indep R₁ S₁) (h₂ : s7b_Indep R₂ S₂) :
    s7b_Indep R (insert x (h.split.joinSupport S₁ S₂)) := by
  intro y hy y' hy' hne hR
  rw [Finset.mem_insert] at hy hy'
  rcases hy with rfl | hy
  · rcases hy' with rfl | hy'
    · exact hne rfl
    · rcases (h.split.mem_joinSupport _ _ y').mp hy' with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.x_free₁ c).1 hR
      · exact (h.x_free₂ c).1 hR
  · rcases hy' with rfl | hy'
    · rcases (h.split.mem_joinSupport _ _ y).mp hy with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.x_free₁ c).2 hR
      · exact (h.x_free₂ c).2 hR
    · exact h.split.indep_joinSupport h₁ h₂ y hy y' hy' hne hR

theorem pre₁_insert [Fintype γ₁] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) (S : Finset γ) :
    s7b_pre ι₁ (insert x S) = s7b_pre ι₁ S := by
  ext c
  rw [s7b_mem_pre, s7b_mem_pre, Finset.mem_insert]
  exact ⟨fun hc => hc.resolve_left (h.x_not₁ c), Or.inr⟩

theorem pre₂_insert [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) (S : Finset γ) :
    s7b_pre ι₂ (insert x S) = s7b_pre ι₂ S := by
  ext c
  rw [s7b_mem_pre, s7b_mem_pre, Finset.mem_insert]
  exact ⟨fun hc => hc.resolve_left (h.x_not₂ c), Or.inr⟩

theorem insert_join_pre [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) {S : Finset γ} (hS : s7b_Indep R S)
    (hx : x ∈ S) :
    insert x (h.split.joinSupport (s7b_pre ι₁ S) (s7b_pre ι₂ S)) = S := by
  ext y
  rw [Finset.mem_insert, h.split.mem_joinSupport]
  constructor
  · rintro (rfl | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact hx
    · exact (s7b_mem_pre ι₁ S c).mp hc
    · exact (s7b_mem_pre ι₂ S c).mp hc
  · intro hy
    by_cases hyx : y = x
    · exact Or.inl hyx
    · right
      rcases h.x_split y hyx (hS x hx y hy (Ne.symm hyx)) (hS y hy x hx hyx) with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact Or.inl ⟨c, (s7b_mem_pre ι₁ S c).mpr hy, rfl⟩
      · exact Or.inr ⟨c, (s7b_mem_pre ι₂ S c).mpr hy, rfl⟩

/-- **eq. s7c:sliding-bijection**, abstractly: independent sets of `R` containing the pivot `x`
correspond to pairs of independent sets of `R₁`, `R₂`; `S ↦ (S₁, S₂)` are the preimages, the
inverse is `(S₁, S₂) ↦ {x} ∪ ι₁ S₁ ∪ ι₂ S₂`. -/
def slidingEquiv [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x) :
    {S : Finset γ // s7b_Indep R S ∧ x ∈ S} ≃
      {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂} where
  toFun S := (⟨s7b_pre ι₁ S.1, h.split.indep_pre₁ S.2.1⟩,
    ⟨s7b_pre ι₂ S.1, h.split.indep_pre₂ S.2.1⟩)
  invFun p := ⟨insert x (h.split.joinSupport p.1.1 p.2.1), h.indep_insert p.1.2 p.2.2,
    Finset.mem_insert_self _ _⟩
  left_inv S := Subtype.ext (h.insert_join_pre S.2.1 S.2.2)
  right_inv p := by
    ext1
    · exact Subtype.ext ((h.pre₁_insert _).trans (h.split.pre₁_joinSupport _ _))
    · exact Subtype.ext ((h.pre₂_insert _).trans (h.split.pre₂_joinSupport _ _))

theorem slidingEquiv_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x)
    (S : {S : Finset γ // s7b_Indep R S ∧ x ∈ S}) :
    ((h.slidingEquiv S).1.1 = s7b_pre ι₁ S.1) ∧ ((h.slidingEquiv S).2.1 = s7b_pre ι₂ S.1) :=
  ⟨rfl, rfl⟩

theorem slidingEquiv_symm_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    (h.slidingEquiv.symm p).1 = insert x (h.split.joinSupport p.1.1 p.2.1) := rfl

/-- The support of a sliding row is the pivot together with the two half supports; its cardinality
is `|S₁| + |S₂| + 1` (the sign `(−1)^{|S|}` of the state sum). -/
theorem card_symm_apply [Fintype γ₁] [Fintype γ₂] (h : s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    (h.slidingEquiv.symm p).1.card = p.1.1.card + p.2.1.card + 1 := by
  rw [slidingEquiv_symm_apply]
  have hx : x ∉ h.split.joinSupport p.1.1 p.2.1 := by
    intro hx
    rcases (h.split.mem_joinSupport _ _ x).mp hx with ⟨c, -, he⟩ | ⟨c, -, he⟩
    · exact h.x_not₁ c he
    · exact h.x_not₂ c he
  rw [Finset.card_insert_of_notMem hx, s7b_SupportSplit.joinSupport, Finset.card_union_of_disjoint,
    s7b_img, s7b_img, Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro y hy₁ hy₂
  obtain ⟨c₁, -, rfl⟩ := (s7b_mem_img _ _ y).mp hy₁
  obtain ⟨c₂, -, he⟩ := (s7b_mem_img _ _ _).mp hy₂
  exact h.split.disjoint c₁ c₂ he.symm

end s7b_PivotSplit

/-- The eligible support's cardinality is `|T₁| + |T₂|`. -/
theorem s7b_SupportSplit.card_symm_apply {R : γ → γ → Prop} {R₁ : γ₁ → γ₁ → Prop}
    {R₂ : γ₂ → γ₂ → Prop} {ι₁ : γ₁ → γ} {ι₂ : γ₂ → γ} [Fintype γ₁] [Fintype γ₂]
    (h : s7b_SupportSplit R R₁ R₂ ι₁ ι₂)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    (h.eligibleEquiv.symm p).1.card = p.1.1.card + p.2.1.card := by
  rw [eligibleEquiv_symm_apply, joinSupport, Finset.card_union_of_disjoint, s7b_img, s7b_img,
    Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro y hy₁ hy₂
  obtain ⟨c₁, -, rfl⟩ := (s7b_mem_img _ _ y).mp hy₁
  obtain ⟨c₂, -, he⟩ := (s7b_mem_img _ _ _).mp hy₂
  exact h.disjoint c₁ c₂ he.symm

end S7BSupports


section S7BSide

/-! ### U110-B, part III: the halves on a SIDE polygon and the mark transport of a sliding row.
`P` is the wall centre, `Q` a generic side polygon; lem:wall-sides (V) (`vertex_sides`,
`VertexCrossingData`) gives `hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)`,
so the crossings and visits of the halves (part II) are crossings and visits of `Q`.  For a sliding
row `S ∋ x₋` the marks of `Q` are, apart from the second visit of `x₋` and the visits of the
crossings interlacing `x₋`, exactly the marks of `λ₁ ⊔ λ₂` (`s7b_slidingMark`); the smoothing
successor of `S` is the FIRST-RETURN map of the two halves' successors on that image
(`s7b_SlidingTransport.ret`, the geometric input of this row), whence owners, carriers and carrier
crossings correspond (part I). -/

/-- A crossing of the centre that is not contact-affected, read on a side polygon. -/
def s7b_sideCrossing {P Q : LabelledTuple n} {M a : ZMod n}
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (c : Crossing P) (hc : ¬ ContactAffected M a c.val) : Crossing Q :=
  ⟨c.val, (hQC _ hc).mpr c.property⟩

/-- The crossing of the side polygon carried by a crossing of `λ₁`. -/
def s7b_firstCrossingQ (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (c : Crossing (firstHalf P M a)) : Crossing Q :=
  s7b_sideCrossing hQC (s7b_firstHalfCrossing hn hsep hm c)
    (s7b_firstHalfCrossing_not_affected hn hsep hm c)

/-- The crossing of the side polygon carried by a crossing of `λ₂`. -/
def s7b_secondCrossingQ (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (c : Crossing (secondHalf P M a)) : Crossing Q :=
  s7b_sideCrossing hQC (s7b_secondHalfCrossing hn hsep hm c)
    (s7b_secondHalfCrossing_not_affected hn hsep hm c)

/-- A label in both half ranges is the contact edge `a`, reached only by the wrap labels. -/
theorem s7b_firstHalfIndex_eq_secondHalfEdgeIndex (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {i : ZMod (firstHalfSize M a)}
    {j : ZMod (secondHalfSize M a)} (h : firstHalfIndex M a i = secondHalfEdgeIndex M a j) :
    i = -1 ∧ j = 0 := by
  have hb := contactHalfSizes_bounds hn hsep
  have hi := i.val_lt
  have hj := j.val_lt
  have hd : firstHalfSize M a = contactDistance M a + 1 := rfl
  have hd' : secondHalfSize M a = n - contactDistance M a := rfl
  have hdn : contactDistance M a < n := ZMod.val_lt _
  have h1 : ((i.val : ℕ) : ZMod n) = ((contactDistance M a + j.val : ℕ) : ZMod n) := by
    have hc := contactDistance_cast M a
    simp only [firstHalfIndex, secondHalfEdgeIndex, cyclicRangeIndex] at h
    push_cast
    linear_combination h - hc
  have h2 : i.val = contactDistance M a + j.val := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hj0 : j.val = 0 := by omega
  have hi1 : i.val = contactDistance M a := by omega
  refine ⟨?_, (ZMod.val_eq_zero j).mp hj0⟩
  apply ZMod.val_injective
  have hl := last_index_val_succ (n := firstHalfSize M a)
  omega

theorem s7b_firstHalfIndex_ne_secondHalfIndex (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) (i : ZMod (firstHalfSize M a))
    {j : ZMod (secondHalfSize M a)} (hj : j ≠ 0) :
    firstHalfIndex M a i ≠ secondHalfIndex M a j := by
  intro h
  rw [secondHalfIndex_nonzero M a hj] at h
  exact hj (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep h).2

section Maps

variable (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) {P Q : LabelledTuple n}
  (hm : P M ∈ edgeInterior P a)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))

theorem s7b_firstCrossingQ_val (c : Crossing (firstHalf P M a)) :
    (s7b_firstCrossingQ hn hsep hm hQC c).val = c.val.image (firstHalfIndex M a) := rfl

theorem s7b_secondCrossingQ_val (c : Crossing (secondHalf P M a)) :
    (s7b_secondCrossingQ hn hsep hm hQC c).val = c.val.image (secondHalfEdgeIndex M a) := rfl

theorem s7b_firstCrossingQ_not_affected (c : Crossing (firstHalf P M a)) :
    ¬ ContactAffected M a (s7b_firstCrossingQ hn hsep hm hQC c).val :=
  s7b_firstHalfCrossing_not_affected hn hsep hm c

theorem s7b_secondCrossingQ_not_affected (c : Crossing (secondHalf P M a)) :
    ¬ ContactAffected M a (s7b_secondCrossingQ hn hsep hm hQC c).val :=
  s7b_secondHalfCrossing_not_affected hn hsep hm c

theorem s7b_firstCrossingQ_injective : Function.Injective (s7b_firstCrossingQ hn hsep hm hQC) := by
  intro c d h
  exact Subtype.ext (Finset.image_injective (firstHalfIndex_injective M a) (congrArg Subtype.val h))

theorem s7b_secondCrossingQ_injective :
    Function.Injective (s7b_secondCrossingQ hn hsep hm hQC) := by
  intro c d h
  exact Subtype.ext
    (Finset.image_injective (secondHalfEdgeIndex_injective M a) (congrArg Subtype.val h))

/-- A crossing of `λ₁` and a crossing of `λ₂` never carry the same crossing of `Q`. -/
theorem s7b_firstCrossingQ_ne_secondCrossingQ (c : Crossing (firstHalf P M a))
    (c' : Crossing (secondHalf P M a)) :
    s7b_firstCrossingQ hn hsep hm hQC c ≠ s7b_secondCrossingQ hn hsep hm hQC c' := by
  intro h
  have hv := congrArg Subtype.val h
  rw [s7b_firstCrossingQ_val, s7b_secondCrossingQ_val] at hv
  obtain ⟨i, j, hs, hr, -⟩ := c.property
  have hij : i ≠ j := (remote_endpoints i j hr).1.symm
  have hmem : ∀ k ∈ c.val, firstHalfIndex M a k = a := by
    intro k hk
    have : firstHalfIndex M a k ∈ c'.val.image (secondHalfEdgeIndex M a) := by
      rw [← hv]; exact Finset.mem_image_of_mem _ hk
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp this
    have := (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep hl.symm).1
    rw [this, firstHalfIndex_last]
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  exact hij (firstHalfIndex_injective M a ((hmem i hi).trans (hmem j hj).symm))

/-- The visit of `Q` carried by a visit of `λ₁`. -/
def s7b_firstVisitQ (v : Visit (firstHalf P M a)) : Visit Q :=
  ⟨s7b_firstCrossingQ hn hsep hm hQC v.1,
    ⟨firstHalfIndex M a v.2.val, Finset.mem_image_of_mem _ v.2.property⟩⟩

/-- The visit of `Q` carried by a visit of `λ₂`. -/
def s7b_secondVisitQ (v : Visit (secondHalf P M a)) : Visit Q :=
  ⟨s7b_secondCrossingQ hn hsep hm hQC v.1,
    ⟨secondHalfEdgeIndex M a v.2.val, Finset.mem_image_of_mem _ v.2.property⟩⟩

theorem s7b_firstVisitQ_fst (v : Visit (firstHalf P M a)) :
    (s7b_firstVisitQ hn hsep hm hQC v).1 = s7b_firstCrossingQ hn hsep hm hQC v.1 := rfl

theorem s7b_firstVisitQ_edge (v : Visit (firstHalf P M a)) :
    (s7b_firstVisitQ hn hsep hm hQC v).2.val = firstHalfIndex M a v.2.val := rfl

theorem s7b_secondVisitQ_fst (v : Visit (secondHalf P M a)) :
    (s7b_secondVisitQ hn hsep hm hQC v).1 = s7b_secondCrossingQ hn hsep hm hQC v.1 := rfl

theorem s7b_secondVisitQ_edge (v : Visit (secondHalf P M a)) :
    (s7b_secondVisitQ hn hsep hm hQC v).2.val = secondHalfEdgeIndex M a v.2.val := rfl

theorem s7b_firstVisitQ_injective : Function.Injective (s7b_firstVisitQ hn hsep hm hQC) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hc : c = d := s7b_firstCrossingQ_injective hn hsep hm hQC (congrArg Sigma.fst h)
  subst hc
  have hi : firstHalfIndex M a i.val = firstHalfIndex M a j.val :=
    congrArg (fun w : Visit Q => w.2.val) h
  rw [Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (Subtype.ext (firstHalfIndex_injective M a hi))⟩

theorem s7b_secondVisitQ_injective : Function.Injective (s7b_secondVisitQ hn hsep hm hQC) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hc : c = d := s7b_secondCrossingQ_injective hn hsep hm hQC (congrArg Sigma.fst h)
  subst hc
  have hi : secondHalfEdgeIndex M a i.val = secondHalfEdgeIndex M a j.val :=
    congrArg (fun w : Visit Q => w.2.val) h
  rw [Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (Subtype.ext (secondHalfEdgeIndex_injective M a hi))⟩

theorem s7b_firstVisitQ_visitTwin (v : Visit (firstHalf P M a)) :
    s7b_firstVisitQ hn hsep hm hQC (visitTwin v) = visitTwin (s7b_firstVisitQ hn hsep hm hQC v) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne v (s7b_firstVisitQ_injective hn hsep hm hQC h)

theorem s7b_secondVisitQ_visitTwin (v : Visit (secondHalf P M a)) :
    s7b_secondVisitQ hn hsep hm hQC (visitTwin v) =
      visitTwin (s7b_secondVisitQ hn hsep hm hQC v) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne v (s7b_secondVisitQ_injective hn hsep hm hQC h)

/-- Every visit of the image of a crossing of `λ₁` is the image of a visit of that crossing. -/
theorem s7b_visit_of_firstCrossingQ (v : Visit Q) (c : Crossing (firstHalf P M a))
    (hv : v.1 = s7b_firstCrossingQ hn hsep hm hQC c) :
    ∃ w : Visit (firstHalf P M a), w.1 = c ∧ s7b_firstVisitQ hn hsep hm hQC w = v := by
  obtain ⟨c', i⟩ := v
  change c' = _ at hv
  subst hv
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp i.property
  refine ⟨⟨c, ⟨j, hj⟩⟩, rfl, ?_⟩
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hji))

theorem s7b_visit_of_secondCrossingQ (v : Visit Q) (c : Crossing (secondHalf P M a))
    (hv : v.1 = s7b_secondCrossingQ hn hsep hm hQC c) :
    ∃ w : Visit (secondHalf P M a), w.1 = c ∧ s7b_secondVisitQ hn hsep hm hQC w = v := by
  obtain ⟨c', i⟩ := v
  change c' = _ at hv
  subst hv
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp i.property
  refine ⟨⟨c, ⟨j, hj⟩⟩, rfl, ?_⟩
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hji))

/-! #### The mark map of a sliding row -/

/-- The marks of `λ₁ ⊔ λ₂` inside the marks of `Q`, for a sliding row through the contact visit
`vm` (the visit of `x₋` on the leg edge `M−1` / `M`; its twin on `E_a` has no counterpart): the
vertices `M, …, a` of `λ₁` and `a+1, …, M−1` of `λ₂` are the vertices of `Q`, the vertex `0 = μ_M` of
`λ₂` is the smoothing corner `vm`, the visits are carried by `s7b_firstVisitQ`/`s7b_secondVisitQ`. -/
def s7b_slidingMark (vm : Visit Q) :
    Mark (firstHalf P M a) ⊕ Mark (secondHalf P M a) → Mark Q
  | Sum.inl (Sum.inl i) => Sum.inl (firstHalfIndex M a i)
  | Sum.inl (Sum.inr v) => Sum.inr (s7b_firstVisitQ hn hsep hm hQC v)
  | Sum.inr (Sum.inl i) => if i = 0 then Sum.inr vm else Sum.inl (secondHalfIndex M a i)
  | Sum.inr (Sum.inr v) => Sum.inr (s7b_secondVisitQ hn hsep hm hQC v)

theorem s7b_slidingMark_inl_inl (vm : Visit Q) (i : ZMod (firstHalfSize M a)) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inl (Sum.inl i)) = Sum.inl (firstHalfIndex M a i) := rfl

theorem s7b_slidingMark_inl_inr (vm : Visit Q) (v : Visit (firstHalf P M a)) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inl (Sum.inr v)) =
      Sum.inr (s7b_firstVisitQ hn hsep hm hQC v) := rfl

theorem s7b_slidingMark_inr_inl_zero (vm : Visit Q) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inr (Sum.inl 0)) = Sum.inr vm := by
  simp [s7b_slidingMark]

theorem s7b_slidingMark_inr_inl (vm : Visit Q) {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inr (Sum.inl i)) = Sum.inl (secondHalfIndex M a i) := by
  simp [s7b_slidingMark, hi]

theorem s7b_slidingMark_inr_inr (vm : Visit Q) (v : Visit (secondHalf P M a)) :
    s7b_slidingMark hn hsep hm hQC vm (Sum.inr (Sum.inr v)) =
      Sum.inr (s7b_secondVisitQ hn hsep hm hQC v) := rfl

theorem s7b_slidingMark_injective (vm : Visit Q) (hvm : ContactAffected M a vm.1.val) :
    Function.Injective (s7b_slidingMark hn hsep hm hQC vm) := by
  have hvm₁ : ∀ v : Visit (firstHalf P M a), s7b_firstVisitQ hn hsep hm hQC v ≠ vm := by
    intro v h
    exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1 (by
      rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, h]; exact hvm)
  have hvm₂ : ∀ v : Visit (secondHalf P M a), s7b_secondVisitQ hn hsep hm hQC v ≠ vm := by
    intro v h
    exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1 (by
      rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, h]; exact hvm)
  have h12 : ∀ (v : Visit (firstHalf P M a)) (w : Visit (secondHalf P M a)),
      s7b_firstVisitQ hn hsep hm hQC v ≠ s7b_secondVisitQ hn hsep hm hQC w := by
    intro v w h
    exact s7b_firstCrossingQ_ne_secondCrossingQ hn hsep hm hQC v.1 w.1 (congrArg Sigma.fst h)
  rintro (m | m) (m' | m') h
  · rcases m with i | v <;> rcases m' with i' | v'
    · exact congrArg (Sum.inl ∘ Sum.inl) (firstHalfIndex_injective M a (Sum.inl.inj h))
    · exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inr_ne_inl
    · exact congrArg (Sum.inl ∘ Sum.inr) (s7b_firstVisitQ_injective hn hsep hm hQC (Sum.inr.inj h))
  · rcases m with i | v <;> rcases m' with i' | v'
    · by_cases hi' : i' = 0
      · subst hi'
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd h Sum.inl_ne_inr
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
        exact absurd (Sum.inl.inj h) (s7b_firstHalfIndex_ne_secondHalfIndex hn hsep i hi')
    · exact absurd h Sum.inl_ne_inr
    · by_cases hi' : i' = 0
      · subst hi'
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd (Sum.inr.inj h) (hvm₁ v)
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
        exact absurd h Sum.inr_ne_inl
    · exact absurd (Sum.inr.inj h) (h12 v v')
  · rcases m with i | v <;> rcases m' with i' | v'
    · by_cases hi : i = 0
      · subst hi
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd h Sum.inr_ne_inl
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at h
        exact absurd (Sum.inl.inj h).symm (s7b_firstHalfIndex_ne_secondHalfIndex hn hsep i' hi)
    · by_cases hi : i = 0
      · subst hi
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd (Sum.inr.inj h).symm (hvm₁ v')
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at h
        exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inr_ne_inl
    · exact absurd (Sum.inr.inj h).symm (h12 v' v)
  · rcases m with i | v <;> rcases m' with i' | v'
    · by_cases hi : i = 0
      · subst hi
        by_cases hi' : i' = 0
        · subst hi'; rfl
        · rw [s7b_slidingMark_inr_inl_zero, s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
          exact absurd h Sum.inr_ne_inl
      · by_cases hi' : i' = 0
        · subst hi'
          rw [s7b_slidingMark_inr_inl_zero, s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at h
          exact absurd h Sum.inl_ne_inr
        · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi,
            s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
          exact congrArg (Sum.inr ∘ Sum.inl) (secondHalfIndex_injective M a (Sum.inl.inj h))
    · by_cases hi : i = 0
      · subst hi
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd (Sum.inr.inj h).symm (hvm₂ v')
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at h
        exact absurd h Sum.inl_ne_inr
    · by_cases hi' : i' = 0
      · subst hi'
        rw [s7b_slidingMark_inr_inl_zero] at h
        exact absurd (Sum.inr.inj h) (hvm₂ v)
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi'] at h
        exact absurd h Sum.inr_ne_inl
    · exact congrArg (Sum.inr ∘ Sum.inr) (s7b_secondVisitQ_injective hn hsep hm hQC (Sum.inr.inj h))

end Maps

end S7BSide

section S7BSlidingTransport

/-! ### U110-B, part III (continued): the sliding-row transport structure and its consequences.
The field `ret` (the smoothing successor of `S` is the first-return map of the halves' successors
on the image of `s7b_slidingMark`) is the ONLY geometric input; everything below is derived from
it with part I: owners, the carrier correspondence `Component hn hQ S ≃ Component λ₁ S₁ ⊕
Component λ₂ S₂`, and (with the pivot split of part IV) the carrier crossings and `m_Q`. -/

/-- A sliding row `S ∋ x₋ = vm.1` of the side polygon `Q` with its two half supports `S₁, S₂`
(the preimages of `S`), and the first-return law for the smoothing successors. -/
structure s7b_SlidingTransport (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
    (S : Finset (Crossing Q)) (S₁ : Finset (Crossing (firstHalf P M a)))
    (S₂ : Finset (Crossing (secondHalf P M a))) (vm : Visit Q) : Prop where
  affected : ContactAffected M a vm.1.val
  pivot_mem : vm.1 ∈ S
  first_pre : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S
  second_pre : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S
  ret : s7b_ReturnTransport (smoothingSuccessor hn hQ S)
    (Equiv.Perm.sumCongr (smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
      (smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂))
    (s7b_slidingMark hn hsep hm hQC vm)

namespace s7b_SlidingTransport

variable {hn : 3 ≤ n} {M a : ZMod n} {hsep : ContactSeparated M a} {P Q : LabelledTuple n}
  {hm : P M ∈ edgeInterior P a}
  {hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)}
  {hQ : Generic Q} {h₁ : Generic (firstHalf P M a)} {h₂ : Generic (secondHalf P M a)}
  {S : Finset (Crossing Q)} {S₁ : Finset (Crossing (firstHalf P M a))}
  {S₂ : Finset (Crossing (secondHalf P M a))} {vm : Visit Q}

/-- Two marks of `λ₁` have one owner iff their images have one owner on `Q`. -/
theorem owner_inl_iff (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m m' : Mark (firstHalf P M a)) :
    owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m)) =
        owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m')) ↔
      owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m =
        owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m' := by
  rw [owner_eq_iff, owner_eq_iff, h.ret.sameCycle_iff, s7b_sumCongr_sameCycle_inl]

theorem owner_inr_iff (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m m' : Mark (secondHalf P M a)) :
    owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m)) =
        owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m')) ↔
      owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m =
        owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m' := by
  rw [owner_eq_iff, owner_eq_iff, h.ret.sameCycle_iff, s7b_sumCongr_sameCycle_inr]

/-- Marks of the two different halves never share an owner on `Q`. -/
theorem owner_inl_ne_inr (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m : Mark (firstHalf P M a)) (m' : Mark (secondHalf P M a)) :
    owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m)) ≠
      owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m')) := by
  rw [Ne, owner_eq_iff, h.ret.sameCycle_iff]
  exact s7b_sumCongr_not_sameCycle _ _ m m'

/-- **The carrier correspondence of a sliding row**: the carriers of `S` on `Q` are the carriers of
`S₁` on `λ₁` together with those of `S₂` on `λ₂` (eq. s7c:sliding-residual). -/
def componentEquiv (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) :
    Component hn hQ S ≃
      Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ ⊕
        Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ :=
  h.ret.cycleEquiv.symm.trans (s7b_sumCongr_cycleEquiv _ _)

theorem componentEquiv_owner_inl (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m : Mark (firstHalf P M a)) :
    h.componentEquiv (owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m))) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m) := by
  have he : owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m)) =
      h.ret.cycleEquiv (Quotient.mk _ (Sum.inl m)) := rfl
  show s7b_sumCongr_cycleEquiv _ _
    (h.ret.cycleEquiv.symm (owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inl m)))) = _
  rw [he, Equiv.symm_apply_apply]
  rfl

theorem componentEquiv_owner_inr (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (m : Mark (secondHalf P M a)) :
    h.componentEquiv (owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m))) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m) := by
  have he : owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m)) =
      h.ret.cycleEquiv (Quotient.mk _ (Sum.inr m)) := rfl
  show s7b_sumCongr_cycleEquiv _ _
    (h.ret.cycleEquiv.symm (owner hn hQ S (s7b_slidingMark hn hsep hm hQC vm (Sum.inr m)))) = _
  rw [he, Equiv.symm_apply_apply]
  rfl

/-- The owner on `Q` of a visit carried from `λ₁`, in terms of the half owner. -/
theorem componentEquiv_owner_firstVisit
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (w : Visit (firstHalf P M a)) :
    h.componentEquiv (owner hn hQ S (Sum.inr (s7b_firstVisitQ hn hsep hm hQC w))) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ (Sum.inr w)) :=
  h.componentEquiv_owner_inl (Sum.inr w)

theorem componentEquiv_owner_secondVisit
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (w : Visit (secondHalf P M a)) :
    h.componentEquiv (owner hn hQ S (Sum.inr (s7b_secondVisitQ hn hsep hm hQC w))) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ (Sum.inr w)) :=
  h.componentEquiv_owner_inr (Sum.inr w)

/-- The carrier through the contact vertex `μ_M` on `Q` corresponds to `λ₁`'s carrier through its
vertex `0 = μ_M`. -/
theorem componentEquiv_owner_vertexM (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) :
    h.componentEquiv (owner hn hQ S (Sum.inl M)) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ (Sum.inl 0)) := by
  have he : (Sum.inl M : Mark Q) = s7b_slidingMark hn hsep hm hQC vm (Sum.inl (Sum.inl 0)) := by
    rw [s7b_slidingMark_inl_inl, firstHalfIndex_zero]
  rw [he, h.componentEquiv_owner_inl]

/-- The carrier through the contact visit `vm` on `Q` corresponds to `λ₂`'s carrier through its
vertex `0 = μ_M`. -/
theorem componentEquiv_owner_pivot (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) :
    h.componentEquiv (owner hn hQ S (Sum.inr vm)) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ (Sum.inl 0)) := by
  have he : (Sum.inr vm : Mark Q) = s7b_slidingMark hn hsep hm hQC vm (Sum.inr (Sum.inl 0)) :=
    (s7b_slidingMark_inr_inl_zero hn hsep hm hQC vm).symm
  rw [he, h.componentEquiv_owner_inr]

/-- A carried crossing of `λ₁` is a crossing of the carrier `q` of `S` iff it is a crossing of the
corresponding half carrier. -/
theorem firstCrossingQ_mem_carrierCrossings_iff
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (c : Crossing (firstHalf P M a))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : h.componentEquiv q = Sum.inl q₁) :
    s7b_firstCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ S q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_firstCrossingQ hn hsep hm hQC c ∈ S ↔ c ∈ S₁ := by
    rw [h.first_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_firstVisitQ hn hsep hm hQC w) (by
      rw [s7b_firstVisitQ_fst, hw])
    have := h.componentEquiv_owner_firstVisit w
    rw [hv, hq] at this
    exact (Sum.inl.inj this).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC v c hv
    apply h.componentEquiv.injective
    rw [h.componentEquiv_owner_firstVisit, hall w hw, hq]

theorem secondCrossingQ_mem_carrierCrossings_iff
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (c : Crossing (secondHalf P M a))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : h.componentEquiv q = Sum.inr q₂) :
    s7b_secondCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ S q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_secondCrossingQ hn hsep hm hQC c ∈ S ↔ c ∈ S₂ := by
    rw [h.second_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_secondVisitQ hn hsep hm hQC w) (by
      rw [s7b_secondVisitQ_fst, hw])
    have := h.componentEquiv_owner_secondVisit w
    rw [hv, hq] at this
    exact (Sum.inr.inj this).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC v c hv
    apply h.componentEquiv.injective
    rw [h.componentEquiv_owner_secondVisit, hall w hw, hq]

/-- A carried crossing of `λ₂` is never a crossing of a carrier corresponding to a carrier of `λ₁`
(and symmetrically). -/
theorem secondCrossingQ_notMem_carrierCrossings
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (c : Crossing (secondHalf P M a))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : h.componentEquiv q = Sum.inl q₁) :
    s7b_secondCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ S q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_secondVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := h.componentEquiv_owner_secondVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inl_ne_inr this

theorem firstCrossingQ_notMem_carrierCrossings
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm) (c : Crossing (firstHalf P M a))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : h.componentEquiv q = Sum.inr q₂) :
    s7b_firstCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ S q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_firstVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := h.componentEquiv_owner_firstVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inr_ne_inl this

/-- Under the pivot split (part IV: the crossings of `Q` off the two images are `x₋` and the
crossings interlacing it), every carrier crossing of `S` is carried from a half: a crossing
interlacing `x₋ ∈ S` has its visits on two different carriers (lem:carriers (iii)). -/
theorem carrierCrossings_mem_range
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S) {y : Crossing Q}
    (hy : y ∈ carrierCrossings hn hQ S q) :
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪
      Set.range (s7b_secondCrossingQ hn hsep hm hQC) := by
  rw [mem_carrierCrossings] at hy
  have hyx : y ≠ vm.1 := fun he => hy.1 (he ▸ h.pivot_mem)
  have hnot : ∀ z : Crossing Q, Interlaces hn hQ y z → z ∈ S → False := by
    intro z hz hzS
    have hN : y ∈ supportNeighbors hn hQ S := (mem_supportNeighbors hn hQ S y).mpr ⟨z, hzS, hz⟩
    obtain ⟨i, j, hs, -, -⟩ := y.property
    have hi : i ∈ y.val := by rw [hs]; simp
    have hsep' := (carriers_lemma hn hQ hS).neighbor_visits_separated y hN ⟨y, ⟨i, hi⟩⟩ rfl
    exact hsep' ((hy.2 ⟨y, ⟨i, hi⟩⟩ rfl).trans (hy.2 (visitTwin ⟨y, ⟨i, hi⟩⟩) rfl).symm)
  exact hsplit.x_split y hyx (fun hI => hnot _ (interlaces_symm hn hQ hI) h.pivot_mem)
    (fun hI => hnot _ hI h.pivot_mem)

/-- **`m_Q` of a carrier corresponding to a carrier of `λ₁`**: its crossings are exactly the carried
crossings of the half carrier, so the counts agree (eq. s7c:sliding-residual for the self-crossings;
the input to the coefficient transport of U110-D and to the slot `d_Q`). -/
theorem carrierCrossings_eq_img_first
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) (hq : h.componentEquiv q = Sum.inl q₁) :
    carrierCrossings hn hQ S q =
      s7b_img (s7b_firstCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases h.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨c, (h.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mp hy, rfl⟩
    · exact absurd hy (h.secondCrossingQ_notMem_carrierCrossings c q q₁ hq)
  · rintro ⟨c, hc, rfl⟩
    exact (h.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mpr hc

theorem carrierCrossings_eq_img_second
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hq : h.componentEquiv q = Sum.inr q₂) :
    carrierCrossings hn hQ S q =
      s7b_img (s7b_secondCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases h.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact absurd hy (h.firstCrossingQ_notMem_carrierCrossings c q q₂ hq)
    · exact ⟨c, (h.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mp hy, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact (h.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mpr hc

theorem carrierCrossingCount_eq_first
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) (hq : h.componentEquiv q = Sum.inl q₁) :
    carrierCrossingCount hn hQ S q =
      carrierCrossingCount (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := by
  unfold carrierCrossingCount
  rw [h.carrierCrossings_eq_img_first hsplit hS q q₁ hq, s7b_img, Finset.card_map]

theorem carrierCrossingCount_eq_second
    (h : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hq : h.componentEquiv q = Sum.inr q₂) :
    carrierCrossingCount hn hQ S q =
      carrierCrossingCount (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := by
  unfold carrierCrossingCount
  rw [h.carrierCrossings_eq_img_second hsplit hS q q₂ hq, s7b_img, Finset.card_map]

end s7b_SlidingTransport

/-- **eq. s7c:sliding-bijection on the actual decompositions**: given the pivot split for the
interlacement relations (the geometric input of U110-A/B), the sliding rows `{S ∈ Ind(G_Q) : x₋ ∈ S}`
correspond to `Ind(G_{λ₁}) × Ind(G_{λ₂})`. -/
def s7b_slidingDecompositionEquiv (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a)) (x : Crossing Q)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x) :
    {S : Finset (Crossing Q) // IsDecomposition hn hQ S ∧ x ∈ S} ≃
      {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂} :=
  (Equiv.subtypeEquivRight fun S => by
      rw [s7b_isDecomposition_iff_indep]).trans
    (hsplit.slidingEquiv.trans
      (Equiv.prodCongr (Equiv.subtypeEquivRight fun S₁ => by rw [s7b_isDecomposition_iff_indep])
        (Equiv.subtypeEquivRight fun S₂ => by rw [s7b_isDecomposition_iff_indep])))

/-- **eq. s7c:eligible-bijection on the actual decompositions**: the eligible supports of the
newborn-free side `P₀` (no crossing off the two half images) correspond to `Ind(G_{λ₁}) × Ind(G_{λ₂})`. -/
def s7b_eligibleDecompositionEquiv (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
    (hsplit : s7b_SupportSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC)) :
    {T : Finset (Crossing Q) // IsDecomposition hn hQ T ∧
        ∀ y ∈ T, y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪
          Set.range (s7b_secondCrossingQ hn hsep hm hQC)} ≃
      {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂} :=
  (Equiv.subtypeEquivRight fun T => by
      rw [s7b_isDecomposition_iff_indep]).trans
    (hsplit.eligibleEquiv.trans
      (Equiv.prodCongr (Equiv.subtypeEquivRight fun S₁ => by rw [s7b_isDecomposition_iff_indep])
        (Equiv.subtypeEquivRight fun S₂ => by rw [s7b_isDecomposition_iff_indep])))

end S7BSlidingTransport

/-! ### Helpers of unit U110-C (prefix `s7c_`; PLAN_FINAL §3.3: sliding item (3) "selector table
eq. s7c:short-selector on `carrierWeight` ⇒ `W₊ − W₋ = s W₁W₂`" (eqs. s7c:sliding-selector-factors,
s7c:sliding-selector-difference), bigon item (1) the contact triangle's `wt = s₀` (eq. s7c:triangle-data),
item (5) eqs. s7c:interlacing-selector / s7c:noninterlacing-selector with the uniform / one-dissent turn
patterns of the half contact carriers that the floor consumes (sm-4:556-585, 742-750), and the mixed
one-newborn carriers of eq. s7c:one-newborn-turns).
lem:C-X1's `wt(L) = carrierWeight` (CX1.lean:24) is the accepted `cornerSelector` of the corner polygon
(cor:flat-carriers (iii)) and depends on the polygon only through the MULTISET of its turns
(`s7c_turns`) and its corner count: `s7c_sel`.  The algebra is proved once on multisets
(`s7c_sel_refine`, `s7c_sel_interlacing`, `s7c_sel_noninterlacing`, `s7c_sel_triangle`, …) and read
back on carriers of DIFFERENT polygons (a side polygon and the two halves) through corner bijections
(`s7c_carrierWeight_refine`, `s7c_carrierWeight_interlacing`, `s7c_carrierWeight_noninterlacing`, …).
Consumers: U110-E (`s7_sliding_law_at`), U110-F (triangle), U110-J/K (bigon selectors, floor patterns). -/

section S7CSelector

/-! #### The selector on multisets of turns -/

/-- The multiset of turns of a closed polygon `Q` with `k ≥ 1` labelled corners (read on a corner
polygon `ccpCornerPolygon hn hP S q`, `k = ccpCornerCount hn hP S q`). -/
def s7c_turns {k : ℕ} [NeZero k] (Q : LabelledTuple k) : Multiset SignType :=
  Finset.univ.val.map (turn Q)

/-- lem:C-X1's selector as a function of the multiset of turns: `1` if all turns are right (`−1`),
`(−1)^{card}` if all are left (`1`), `0` if the turns are mixed (or if a turn is `0`). -/
def s7c_sel (m : Multiset SignType) : ℤ :=
  if ∀ x ∈ m, x = -1 then 1 else if ∀ x ∈ m, x = 1 then (-1) ^ Multiset.card m else 0

theorem s7c_sel_of_forall_neg {m : Multiset SignType} (h : ∀ x ∈ m, x = -1) : s7c_sel m = 1 := by
  unfold s7c_sel
  rw [ite_eq_left h]

theorem s7c_sel_of_forall_pos {m : Multiset SignType} (h : ∀ x ∈ m, x = 1) :
    s7c_sel m = (-1) ^ Multiset.card m := by
  unfold s7c_sel
  by_cases hneg : ∀ x ∈ m, x = -1
  · rw [ite_eq_left hneg]
    have hm : m = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro x hx
      have h1 := h x hx
      have h2 := hneg x hx
      rw [h1] at h2
      exact absurd h2 (by decide)
    rw [hm, Multiset.card_zero, pow_zero]
  · rw [ite_eq_right hneg, ite_eq_left h]

/-- A uniform multiset of turns of sign `σ ≠ 0` has selector `(−σ)^{card}` (`1` for right turns,
`(−1)^{card}` for left turns). -/
theorem s7c_sel_of_forall {m : Multiset SignType} {σ : SignType} (hσ : σ ≠ 0)
    (h : ∀ x ∈ m, x = σ) : s7c_sel m = (-(σ : ℤ)) ^ Multiset.card m := by
  rcases SignType.trichotomy σ with rfl | rfl | rfl
  · rw [s7c_sel_of_forall_neg h]
    simp
  · exact absurd rfl hσ
  · rw [s7c_sel_of_forall_pos h]
    simp

/-- "a mixed carrier makes its selector product zero": two different turns kill the selector. -/
theorem s7c_sel_eq_zero_of_ne {m : Multiset SignType} {x y : SignType} (hx : x ∈ m) (hy : y ∈ m)
    (hxy : x ≠ y) : s7c_sel m = 0 := by
  unfold s7c_sel
  rw [ite_eq_right, ite_eq_right]
  · intro h
    exact hxy ((h x hx).trans (h y hy).symm)
  · intro h
    exact hxy ((h x hx).trans (h y hy).symm)

theorem s7c_sel_eq_zero_of_zero_mem {m : Multiset SignType} (h : 0 ∈ m) : s7c_sel m = 0 := by
  unfold s7c_sel
  rw [ite_eq_right, ite_eq_right]
  · intro h'
    exact absurd (h' 0 h) (by decide)
  · intro h'
    exact absurd (h' 0 h) (by decide)

theorem s7c_neg_sign_ne_zero {σ : SignType} (hσ : σ ≠ 0) : -σ ≠ 0 :=
  fun h => hσ (SignType.neg_eq_zero_iff.mp h)

theorem s7c_sign_ne_neg_self {σ : SignType} (hσ : σ ≠ 0) : σ ≠ -σ :=
  fun h => hσ (SignType.self_eq_neg_iff.mp h)

theorem s7c_neg_sign_pow_ne_zero {σ : SignType} (hσ : σ ≠ 0) (c : ℕ) : (-(σ : ℤ)) ^ c ≠ 0 := by
  apply pow_ne_zero
  rcases SignType.trichotomy σ with rfl | rfl | rfl
  · simp
  · exact absurd rfl hσ
  · simp

theorem s7c_exists_ne_of_not_forall {m : Multiset SignType} {σ : SignType}
    (h : ¬ ∀ x ∈ m, x = σ) : ∃ x ∈ m, x ≠ σ := by
  by_contra hcon
  exact h fun x hx => by
    by_contra hne
    exact hcon ⟨x, hx, hne⟩

/-- The selector is nonzero exactly for a uniform multiset of a nonzero sign. -/
theorem s7c_sel_ne_zero_iff {m : Multiset SignType} :
    s7c_sel m ≠ 0 ↔ ∃ σ : SignType, σ ≠ 0 ∧ ∀ x ∈ m, x = σ := by
  constructor
  · intro h
    by_contra hcon
    have hcon' : ∀ σ : SignType, σ ≠ 0 → ∃ x ∈ m, x ≠ σ :=
      fun σ hσ => s7c_exists_ne_of_not_forall fun hall => hcon ⟨σ, hσ, hall⟩
    apply h
    unfold s7c_sel
    rw [ite_eq_right, ite_eq_right]
    · obtain ⟨x, hx, hne⟩ := hcon' 1 (by decide)
      intro h'
      exact hne (h' x hx)
    · obtain ⟨x, hx, hne⟩ := hcon' (-1) (by decide)
      intro h'
      exact hne (h' x hx)
  · rintro ⟨σ, hσ, h⟩
    rw [s7c_sel_of_forall hσ h]
    exact s7c_neg_sign_pow_ne_zero hσ _

/-- A nonzero selector of `m + {σ}` forces every turn of `m` to be `σ` (the contact turn fixes the
sign of a live carrier). -/
theorem s7c_sel_add_singleton_ne_zero {m : Multiset SignType} {σ : SignType}
    (h : s7c_sel (m + {σ}) ≠ 0) : ∀ x ∈ m, x = σ := by
  obtain ⟨σ', -, hall⟩ := s7c_sel_ne_zero_iff.mp h
  have hσ : σ = σ' := hall σ (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self σ)))
  intro x hx
  rw [hall x (Multiset.mem_add.mpr (Or.inl hx)), hσ]

theorem s7c_forall_add_singleton {m : Multiset SignType} {σ : SignType} (h : ∀ x ∈ m, x = σ) :
    ∀ x ∈ m + {σ}, x = σ := by
  intro x hx
  rcases Multiset.mem_add.mp hx with hx | hx
  · exact h x hx
  · exact Multiset.mem_singleton.mp hx

/-! #### eq. s7c:short-selector: refinement by one turn -/

/-- eq. s7c:short-selector (sm-4:365-381): a carrier with a corner of (contact) sign `η` refined by ONE
extra corner of turn `τ` has selector `−η · (old selector)` if `τ = η` and `0` if `τ = −η` — "a mixed
original carrier stays mixed; if `τ` disagrees with its contact sign it has both signs; if all signs are
right the extra right corner preserves weight `1`; and if all are left the extra left corner reverses
`(−1)^{#corners}`". -/
theorem s7c_sel_refine {m : Multiset SignType} {η τ : SignType} (hη : η ≠ 0) (hmem : η ∈ m) :
    s7c_sel (m + {τ}) = if τ = η then -(η : ℤ) * s7c_sel m else 0 := by
  by_cases hall : ∀ x ∈ m, x = η
  · by_cases hτη : τ = η
    · subst hτη
      rw [ite_eq_left rfl, s7c_sel_of_forall hη hall, s7c_sel_of_forall hη (s7c_forall_add_singleton hall),
        Multiset.card_add, Multiset.card_singleton, pow_succ]
      ring
    · rw [ite_eq_right hτη]
      exact s7c_sel_eq_zero_of_ne (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self τ)))
        (Multiset.mem_add.mpr (Or.inl hmem)) hτη
  · obtain ⟨x, hx, hne⟩ := s7c_exists_ne_of_not_forall hall
    rw [s7c_sel_eq_zero_of_ne (Multiset.mem_add.mpr (Or.inl hx)) (Multiset.mem_add.mpr (Or.inl hmem)) hne,
      s7c_sel_eq_zero_of_ne hx hmem hne]
    split_ifs <;> ring

/-- eq. s7c:sliding-selector-difference, the ℤ-algebra (sm-4:382-393): with `W₁W₂ = Q h_s h_{−s}`,
`W₋ = Q c_s h_{−s}`, `W₊ = Q h_s c_{−s}` and the two rows of the selector table (`c_η` for `η = s` and
`η = −s`), `W₊ − W₋ = s W₁W₂` — "If `τ = s`, then `c_s = −s h_s` and `c_{−s} = 0`; if `τ = −s`, then
`c_s = 0` and `c_{−s} = s h_{−s}`. Either way …". -/
theorem s7c_sliding_difference_of_table (Qsp hs hms cs cms : ℤ) {s τ : SignType} (hs0 : s ≠ 0)
    (hτ : τ ≠ 0) (hcs : cs = if τ = s then -(s : ℤ) * hs else 0)
    (hcms : cms = if τ = -s then -((-s : SignType) : ℤ) * hms else 0) :
    Qsp * hs * cms - Qsp * cs * hms = (s : ℤ) * (Qsp * hs * hms) := by
  subst hcs hcms
  by_cases hτs : τ = s
  · have hτns : τ ≠ -s := by
      rw [hτs]
      exact s7c_sign_ne_neg_self hs0
    rw [ite_eq_right hτns, ite_eq_left hτs]
    ring
  · have hτns : τ = -s := by
      rcases SignType.trichotomy s with rfl | rfl | rfl <;>
        rcases SignType.trichotomy τ with rfl | rfl | rfl <;>
        first | decide | exact absurd rfl hs0 | exact absurd rfl hτ | exact absurd rfl hτs
    rw [ite_eq_left hτns, ite_eq_right hτs, SignType.coe_neg]
    ring

/-- eq. s7c:sliding-selector-difference on the multisets of turns of the two half carriers `h_s`, `h_{−s}`
(contact corners of signs `s` and `−s`) and their refinements by the turn `τ`
(eqs. s7c:sliding-selector-factors with the spectator product `Q_sp`, "without assuming it nonzero"):
`W₊ − W₋ = s W₁W₂`. -/
theorem s7c_sliding_selector_difference (Qsp : ℤ) (m₁ m₂ : Multiset SignType) {s τ : SignType}
    (hs : s ≠ 0) (hτ : τ ≠ 0) (h₁ : s ∈ m₁) (h₂ : -s ∈ m₂) :
    Qsp * s7c_sel m₁ * s7c_sel (m₂ + {τ}) - Qsp * s7c_sel (m₁ + {τ}) * s7c_sel m₂ =
      (s : ℤ) * (Qsp * s7c_sel m₁ * s7c_sel m₂) :=
  s7c_sliding_difference_of_table Qsp (s7c_sel m₁) (s7c_sel m₂) _ _ hs hτ
    (s7c_sel_refine hs h₁) (s7c_sel_refine (s7c_neg_sign_ne_zero hs) h₂)

/-! #### eqs. s7c:interlacing-selector, s7c:noninterlacing-selector: the full contact carrier against
its two halves.  The full carrier's turns are the noncontact turns `m₁`, `m₂` of the halves plus ONE
contact turn (`s₀` interlacing, `−s₀` noninterlacing); each half has its noncontact turns plus one
contact turn `s₀` (sm-4:540-585). -/

/-- eq. s7c:interlacing-selector: `wt(L*) = −s₀ wt(L₁) wt(L₂)`, "including all zero cases" — if a
noncontact sign disagrees both sides vanish; otherwise all three carriers are uniform of sign `s₀`, and
"for right turns each weight is `1` and `s₀ = −1`; for left turns the full corner count is the sum of the
half counts minus one, giving a relative minus sign and `s₀ = +1`". -/
theorem s7c_sel_interlacing (m₁ m₂ : Multiset SignType) {s₀ : SignType} (hs₀ : s₀ ≠ 0) :
    s7c_sel (m₁ + m₂ + {s₀}) = -(s₀ : ℤ) * (s7c_sel (m₁ + {s₀}) * s7c_sel (m₂ + {s₀})) := by
  have hsq : (-(s₀ : ℤ)) ^ 2 = 1 := by
    rcases SignType.trichotomy s₀ with rfl | rfl | rfl
    · simp
    · exact absurd rfl hs₀
    · simp
  have hs₀mem : s₀ ∈ m₁ + m₂ + {s₀} := Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self s₀))
  by_cases h₁ : ∀ x ∈ m₁, x = s₀
  · by_cases h₂ : ∀ x ∈ m₂, x = s₀
    · have hA : ∀ x ∈ m₁ + m₂ + {s₀}, x = s₀ := by
        apply s7c_forall_add_singleton
        intro x hx
        rcases Multiset.mem_add.mp hx with hx | hx
        · exact h₁ x hx
        · exact h₂ x hx
      rw [s7c_sel_of_forall hs₀ hA, s7c_sel_of_forall hs₀ (s7c_forall_add_singleton h₁),
        s7c_sel_of_forall hs₀ (s7c_forall_add_singleton h₂)]
      simp only [Multiset.card_add, Multiset.card_singleton]
      have hexp : -(s₀ : ℤ) * ((-(s₀ : ℤ)) ^ (Multiset.card m₁ + 1) * (-(s₀ : ℤ)) ^ (Multiset.card m₂ + 1)) =
          (-(s₀ : ℤ)) ^ (Multiset.card m₁ + Multiset.card m₂ + 1) * (-(s₀ : ℤ)) ^ 2 := by ring
      rw [hexp, hsq, mul_one]
    · obtain ⟨x, hx, hne⟩ := s7c_exists_ne_of_not_forall h₂
      rw [s7c_sel_eq_zero_of_ne (m := m₂ + {s₀}) (Multiset.mem_add.mpr (Or.inl hx))
          (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self s₀))) hne,
        s7c_sel_eq_zero_of_ne (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hx)))) hs₀mem hne]
      ring
  · obtain ⟨x, hx, hne⟩ := s7c_exists_ne_of_not_forall h₁
    rw [s7c_sel_eq_zero_of_ne (m := m₁ + {s₀}) (Multiset.mem_add.mpr (Or.inl hx))
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self s₀))) hne,
      s7c_sel_eq_zero_of_ne (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hx)))) hs₀mem hne]
    ring

/-- The live interlacing row: a nonzero full selector makes both halves' noncontact turns `s₀`
("Otherwise all three carriers are uniform with the same sign", sm-4:558-562). -/
theorem s7c_uniform_of_interlacing {m₁ m₂ : Multiset SignType} {s₀ : SignType}
    (h : s7c_sel (m₁ + m₂ + {s₀}) ≠ 0) : (∀ x ∈ m₁, x = s₀) ∧ (∀ x ∈ m₂, x = s₀) := by
  have hall := s7c_sel_add_singleton_ne_zero h
  exact ⟨fun x hx => hall x (Multiset.mem_add.mpr (Or.inl hx)),
    fun x hx => hall x (Multiset.mem_add.mpr (Or.inr hx))⟩

/-- eq. s7c:noninterlacing-selector: `W_T W₁ W₂ = 0` — "a uniform full carrier gives each half one
opposite contact turn, while two uniform halves give the full carrier one opposite turn.  Thus at least
one of their selectors is zero" (a half must have a noncontact corner: "Every carrier used here has at
least three corners"). -/
theorem s7c_sel_noninterlacing (m₁ m₂ : Multiset SignType) {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hne : m₁ ≠ 0 ∨ m₂ ≠ 0) :
    s7c_sel (m₁ + m₂ + {-s₀}) * (s7c_sel (m₁ + {s₀}) * s7c_sel (m₂ + {s₀})) = 0 := by
  by_cases h : s7c_sel (m₁ + m₂ + {-s₀}) = 0
  · rw [h, zero_mul]
  · have hall := s7c_sel_add_singleton_ne_zero h
    have hss : -s₀ ≠ s₀ := (s7c_sign_ne_neg_self hs₀).symm
    rcases hne with hne | hne
    · obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      have hx' : x = -s₀ := hall x (Multiset.mem_add.mpr (Or.inl hx))
      rw [s7c_sel_eq_zero_of_ne (m := m₁ + {s₀}) (Multiset.mem_add.mpr (Or.inl hx))
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self s₀))) (by rw [hx']; exact hss)]
      ring
    · obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      have hx' : x = -s₀ := hall x (Multiset.mem_add.mpr (Or.inr hx))
      rw [s7c_sel_eq_zero_of_ne (m := m₂ + {s₀}) (Multiset.mem_add.mpr (Or.inl hx))
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self s₀))) (by rw [hx']; exact hss)]
      ring

/-- The live noninterlacing row (sm-4:742-747): a nonzero full selector makes the full carrier uniform of
sign `τ = −s₀`, so "every half inherits its old turns and has exactly one new contact turn of sign `s₀`,
hence exactly one dissent". -/
theorem s7c_dissent_of_noninterlacing {m₁ m₂ : Multiset SignType} {s₀ : SignType}
    (h : s7c_sel (m₁ + m₂ + {-s₀}) ≠ 0) : (∀ x ∈ m₁, x = -s₀) ∧ (∀ x ∈ m₂, x = -s₀) :=
  s7c_uniform_of_interlacing h

/-! #### eq. s7c:triangle-data: the contact triangle -/

/-- eq. s7c:triangle-data, `wt = s₀`: three corners of turn `−s₀` ("For `s₀ = +1` the triangle has three
right turns; for `s₀ = −1` it has three left turns") have selector `s₀`. -/
theorem s7c_sel_triangle {s₀ : SignType} (hs₀ : s₀ ≠ 0) :
    s7c_sel (Multiset.replicate 3 (-s₀)) = s₀ := by
  rw [s7c_sel_of_forall (s7c_neg_sign_ne_zero hs₀) (fun x hx => (Multiset.mem_replicate.mp hx).2),
    Multiset.card_replicate, SignType.coe_neg, neg_neg]
  rcases SignType.trichotomy s₀ with rfl | rfl | rfl
  · norm_num
  · exact absurd rfl hs₀
  · norm_num

/-! #### Reading the multiset algebra on corner polygons and carriers -/

theorem s7c_card_turns {k : ℕ} [NeZero k] (Q : LabelledTuple k) :
    Multiset.card (s7c_turns Q) = k := by
  unfold s7c_turns
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ, ZMod.card]

theorem s7c_mem_turns {k : ℕ} [NeZero k] (Q : LabelledTuple k) (x : SignType) :
    x ∈ s7c_turns Q ↔ ∃ j, turn Q j = x := by
  unfold s7c_turns
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp h
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact Multiset.mem_map.mpr ⟨j, by simp, hj⟩

theorem s7c_forall_turns {k : ℕ} [NeZero k] (Q : LabelledTuple k) (σ : SignType) :
    (∀ x ∈ s7c_turns Q, x = σ) ↔ ∀ j, turn Q j = σ := by
  constructor
  · intro h j
    exact h _ ((s7c_mem_turns Q _).mpr ⟨j, rfl⟩)
  · intro h x hx
    obtain ⟨j, hj⟩ := (s7c_mem_turns Q x).mp hx
    rw [← hj]
    exact h j

/-- The accepted `cornerSelector` (cor:flat-carriers (iii), FlatCarriersDefs.lean:466) is `s7c_sel` of the
multiset of turns. -/
theorem s7c_cornerSelector_eq_sel {k : ℕ} [NeZero k] (Q : LabelledTuple k) :
    cornerSelector Q = s7c_sel (s7c_turns Q) := by
  by_cases h1 : ∀ i, turn Q i = -1
  · rw [s7c_sel_of_forall_neg ((s7c_forall_turns Q _).mpr h1)]
    unfold cornerSelector
    rw [ite_eq_left h1]
  · by_cases h2 : ∀ i, turn Q i = 1
    · rw [s7c_sel_of_forall_pos ((s7c_forall_turns Q _).mpr h2), s7c_card_turns]
      unfold cornerSelector
      rw [ite_eq_right h1, ite_eq_left h2]
    · unfold cornerSelector s7c_sel
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right, ite_eq_right]
      · rwa [s7c_forall_turns]
      · rwa [s7c_forall_turns]

/-- lem:C-X1's `carrierWeight` is the accepted `cornerSelector` of the corner polygon (the identity
`carrierWeight_eq_cornerSelector` of SM/CS3.lean:1453, re-proved here since CS3 is not imported). -/
theorem s7c_carrierWeight_eq_cornerSelector (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierWeight hn hP S q = cornerSelector (ccpCornerPolygon hn hP S q) := by
  unfold carrierWeight cornerSelector
  split_ifs <;> rfl

/-- `wt(L) = s7c_sel` of the multiset of turns of `L`'s corner polygon. -/
theorem s7c_carrierWeight_eq_sel (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierWeight hn hP S q = s7c_sel (s7c_turns (ccpCornerPolygon hn hP S q)) := by
  rw [s7c_carrierWeight_eq_cornerSelector, s7c_cornerSelector_eq_sel]

/-- A carrier all of whose turns are `σ ≠ 0` has `wt = (−σ)^{k(L)}` (lem:C-X1 `weight_right`/`weight_left`
in one formula). -/
theorem s7c_carrierWeight_of_uniform_sign (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {σ : SignType} (hσ : σ ≠ 0)
    (h : ∀ j, turn (ccpCornerPolygon hn hP S q) j = σ) :
    carrierWeight hn hP S q = (-(σ : ℤ)) ^ ccpCornerCount hn hP S q := by
  rw [s7c_carrierWeight_eq_sel, s7c_sel_of_forall hσ ((s7c_forall_turns _ _).mpr h), s7c_card_turns]

/-- eq. s7c:triangle-data on a carrier: three corners, all of turn `−s₀` ⇒ `wt = s₀` (the contact
triangle of the two-newborn sector, sm-4:437-447). -/
theorem s7c_carrierWeight_triangle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (h3 : ccpCornerCount hn hP S q = 3)
    (h : ∀ j, turn (ccpCornerPolygon hn hP S q) j = -s₀) : carrierWeight hn hP S q = s₀ := by
  rw [s7c_carrierWeight_of_uniform_sign hn hP S q (s7c_neg_sign_ne_zero hs₀) h, h3, SignType.coe_neg,
    neg_neg]
  rcases SignType.trichotomy s₀ with rfl | rfl | rfl
  · norm_num
  · exact absurd rfl hs₀
  · norm_num

/-- Two corners of different turns kill the selector (eq. s7c:one-newborn-turns: "the opposite turns lie
on the same daughter carrier and make it mixed"). -/
theorem s7c_carrierWeight_eq_zero_of_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {i j : ZMod (ccpCornerCount hn hP S q)}
    (h : turn (ccpCornerPolygon hn hP S q) i ≠ turn (ccpCornerPolygon hn hP S q) j) :
    carrierWeight hn hP S q = 0 := by
  rw [s7c_carrierWeight_eq_sel]
  exact s7c_sel_eq_zero_of_ne ((s7c_mem_turns _ _).mpr ⟨i, rfl⟩) ((s7c_mem_turns _ _).mpr ⟨j, rfl⟩) h

/-- Two corners of opposite nonzero turns kill the selector. -/
theorem s7c_carrierWeight_eq_zero_of_opposite (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {i j : ZMod (ccpCornerCount hn hP S q)}
    {σ : SignType} (hσ : σ ≠ 0) (hi : turn (ccpCornerPolygon hn hP S q) i = σ)
    (hj : turn (ccpCornerPolygon hn hP S q) j = -σ) : carrierWeight hn hP S q = 0 := by
  have hne : turn (ccpCornerPolygon hn hP S q) i ≠ turn (ccpCornerPolygon hn hP S q) j := by
    rw [hi, hj]
    exact s7c_sign_ne_neg_self hσ
  exact s7c_carrierWeight_eq_zero_of_ne hn hP S q hne

/-- A live selector (`wt ≠ 0`) means a uniform carrier (contrapositive of lem:C-X1 `weight_mixed`). -/
theorem s7c_carrierUniform_of_weight_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (h : carrierWeight hn hP S q ≠ 0) :
    CarrierUniform hn hP S q := by
  by_contra hu
  exact h (carrierWeight_eq_zero_of_not_uniform hn hP S q hu)

/-- A live selector makes all turns equal. -/
theorem s7c_turn_eq_of_weight_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (h : carrierWeight hn hP S q ≠ 0)
    (i j : ZMod (ccpCornerCount hn hP S q)) :
    turn (ccpCornerPolygon hn hP S q) i = turn (ccpCornerPolygon hn hP S q) j := by
  by_contra hne
  exact h (s7c_carrierWeight_eq_zero_of_ne hn hP S q hne)

/-- A live selector and one corner of turn `σ` make every turn `σ` (the contact turn fixes the sign). -/
theorem s7c_forall_turn_of_weight_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (h : carrierWeight hn hP S q ≠ 0)
    {j : ZMod (ccpCornerCount hn hP S q)} {σ : SignType} (hj : turn (ccpCornerPolygon hn hP S q) j = σ) :
    ∀ i, turn (ccpCornerPolygon hn hP S q) i = σ := fun i =>
  (s7c_turn_eq_of_weight_ne_zero hn hP S q h i j).trans hj

/-! #### The signed turn patterns the floor consumes (`SignedUniformOrOneDissent`, §0) -/

/-- Uniform of sign `τ` ⇒ the signed pattern. -/
theorem s7c_signedUniformOrOneDissent_of_forall {m : ℕ} (Q : LabelledTuple m) {τ : SignType}
    (hτ : τ ≠ 0) (h : ∀ j, turn Q j = τ) : SignedUniformOrOneDissent Q :=
  ⟨τ, hτ, Or.inl h⟩

/-- One dissent `−τ` at `j₀` among turns `τ` ⇒ the signed pattern. -/
theorem s7c_signedUniformOrOneDissent_of_dissent {m : ℕ} (Q : LabelledTuple m) {τ : SignType}
    (hτ : τ ≠ 0) (j₀ : ZMod m) (h0 : turn Q j₀ = -τ) (h : ∀ j, j ≠ j₀ → turn Q j = τ) :
    SignedUniformOrOneDissent Q :=
  ⟨τ, hτ, Or.inr ⟨j₀, h0, h⟩⟩

/-! #### Transport of the multiset of turns along corner bijections -/

/-- Splitting off one corner: `turns(Q) = turns(Q ∖ j) + {turn Q j}`. -/
theorem s7c_turns_eq_erase_add {k : ℕ} [NeZero k] (Q : LabelledTuple k) (j : ZMod k) :
    s7c_turns Q = (Finset.univ.erase j).val.map (turn Q) + {turn Q j} := by
  unfold s7c_turns
  conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ j)]
  rw [Finset.insert_val_of_notMem (Finset.notMem_erase j _), Multiset.map_cons,
    ← Multiset.singleton_add, add_comm]

/-- A turn-preserving bijection of index types transports the multiset of turns. -/
theorem s7c_map_univ_eq_of_equiv {α β : Type*} [Fintype α] [Fintype β] (t : α → SignType)
    (t' : β → SignType) (e : α ≃ β) (h : ∀ x, t' (e x) = t x) :
    (Finset.univ : Finset α).val.map t = (Finset.univ : Finset β).val.map t' :=
  Multiset.map_eq_map_of_bij_of_nodup t t' Finset.univ.nodup Finset.univ.nodup
    (fun a _ => e a) (fun a _ => by simp) (fun a₁ _ a₂ _ h => e.injective h)
    (fun b _ => ⟨e.symm b, by simp, e.apply_symm_apply b⟩) (fun a _ => (h a).symm)

/-- The corners other than `j`, as the subtype `{i // i ≠ j}`. -/
theorem s7c_map_erase_eq_map_subtype {α : Type*} [Fintype α] [DecidableEq α] (t : α → SignType)
    (j : α) :
    (Finset.univ.erase j).val.map t =
      (Finset.univ : Finset {i : α // i ≠ j}).val.map (fun x => t x.1) :=
  Multiset.map_eq_map_of_bij_of_nodup t (fun x : {i : α // i ≠ j} => t x.1)
    (Finset.univ.erase j).nodup Finset.univ.nodup
    (fun a ha => ⟨a, Finset.ne_of_mem_erase (Finset.mem_def.mpr ha)⟩) (fun a _ => by simp)
    (fun a₁ _ a₂ _ h => congrArg Subtype.val h)
    (fun b _ => ⟨b.1, Finset.mem_def.mp (Finset.mem_erase.mpr ⟨b.2, Finset.mem_univ _⟩), rfl⟩)
    (fun a _ => rfl)

/-- The turns over a disjoint union of index types. -/
theorem s7c_map_univ_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → SignType) (g : β → SignType) :
    (Finset.univ : Finset (α ⊕ β)).val.map (Sum.elim f g) =
      Finset.univ.val.map f + Finset.univ.val.map g := by
  show (Finset.univ.disjSum Finset.univ : Finset (α ⊕ β)).val.map (Sum.elim f g) = _
  rw [Finset.val_disjSum, Multiset.map_disjSum]
  rfl

/-- Some corner other than `j` exists when `k ≥ 2` (`j + 1 ≠ j`). -/
theorem s7c_exists_ne {k : ℕ} [NeZero k] (hk : 2 ≤ k) (j : ZMod k) : ∃ i : ZMod k, i ≠ j := by
  refine ⟨j + 1, ?_⟩
  intro h
  have h1 : (1 : ZMod k) = 0 := by linear_combination h
  have hd : k ∣ 1 := (ZMod.natCast_eq_zero_iff 1 k).mp (by exact_mod_cast h1)
  have := Nat.le_of_dvd one_pos hd
  omega

/-- The noncontact turns of a polygon with `k ≥ 2` corners form a nonempty multiset. -/
theorem s7c_map_subtype_ne_zero {k : ℕ} [NeZero k] (hk : 2 ≤ k) (t : ZMod k → SignType) (j : ZMod k) :
    (Finset.univ : Finset {i : ZMod k // i ≠ j}).val.map (fun x => t x.1) ≠ 0 := by
  obtain ⟨i, hi⟩ := s7c_exists_ne hk j
  intro h
  have : t i ∈ (Finset.univ : Finset {i : ZMod k // i ≠ j}).val.map (fun x => t x.1) :=
    Multiset.mem_map.mpr ⟨⟨i, hi⟩, by simp, rfl⟩
  rw [h] at this
  exact Multiset.notMem_zero _ this

/-! #### The selector laws on carriers of different polygons, through corner bijections -/

/-- eq. s7c:short-selector on carriers (the sliding refinement, eq. s7c:short-direction-lists): the
carrier `q` (on the side polygon) has a corner `j` of turn `τ` and its other corners correspond
turn-preservingly to ALL corners of the half carrier `q₁`, which has a (contact) corner `jη` of sign `η`;
then `wt(q) = −η wt(q₁)` if `τ = η` and `0` if `τ = −η`. -/
theorem s7c_carrierWeight_refine (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    (j : ZMod (ccpCornerCount hn hP S q)) (jη : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁))
    {η τ : SignType} (hη : η ≠ 0)
    (hjη : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) jη = η) (hj : turn (ccpCornerPolygon hn hP S q) j = τ)
    (e : {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j} ≃ ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁))
    (he : ∀ x, turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) (e x) = turn (ccpCornerPolygon hn hP S q) x.1) :
    carrierWeight hn hP S q = if τ = η then -(η : ℤ) * carrierWeight hn₁ hP₁ S₁ q₁ else 0 := by
  have hm : s7c_turns (ccpCornerPolygon hn hP S q) = s7c_turns (ccpCornerPolygon hn₁ hP₁ S₁ q₁) + {τ} := by
    rw [s7c_turns_eq_erase_add _ j, hj, s7c_map_erase_eq_map_subtype,
      s7c_map_univ_eq_of_equiv
        (fun x : {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j} => turn (ccpCornerPolygon hn hP S q) x.1)
        (turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁)) e he]
    rfl
  rw [s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel, hm]
  exact s7c_sel_refine hη ((s7c_mem_turns _ _).mpr ⟨jη, hjη⟩)

/-- The two-halves corner correspondence of the bigon branch: the corners of the full contact carrier
`q` other than its contact corner `j` are, turn-preservingly, the corners of the half carriers `q₁`, `q₂`
other than their contact corners `j₁`, `j₂` ("All noncontact turns partition between the halves",
sm-4:551).  Packaged as the multiset identity behind eqs. s7c:interlacing-selector /
s7c:noninterlacing-selector. -/
theorem s7c_turns_of_halves (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    (S₂ : Finset (Crossing P₂)) (q₂ : Component hn₂ hP₂ S₂)
    (j : ZMod (ccpCornerCount hn hP S q)) (j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁))
    (j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂))
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, turn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y => turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y => turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x) :
    s7c_turns (ccpCornerPolygon hn hP S q) =
      (Finset.univ.erase j₁).val.map (turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁)) +
        (Finset.univ.erase j₂).val.map (turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) +
        {turn (ccpCornerPolygon hn hP S q) j} := by
  rw [s7c_turns_eq_erase_add _ j, s7c_map_erase_eq_map_subtype, s7c_map_erase_eq_map_subtype,
    s7c_map_erase_eq_map_subtype, ← s7c_map_univ_sum,
    s7c_map_univ_eq_of_equiv _
      (fun x : {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j} => turn (ccpCornerPolygon hn hP S q) x.1) e he]

/-- eq. s7c:interlacing-selector on carriers: contact turns `s₀` on the full carrier `q` (at `j`) and on
both halves (at `j₁`, `j₂`), noncontact corners in turn-preserving bijection ⇒
`wt(q) = −s₀ wt(q₁) wt(q₂)` (all zero cases included). -/
theorem s7c_carrierWeight_interlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    (S₂ : Finset (Crossing P₂)) (q₂ : Component hn₂ hP₂ S₂)
    (j : ZMod (ccpCornerCount hn hP S q)) (j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁))
    (j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)) {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj : turn (ccpCornerPolygon hn hP S q) j = s₀)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, turn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y => turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y => turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x) :
    carrierWeight hn hP S q = -(s₀ : ℤ) * (carrierWeight hn₁ hP₁ S₁ q₁ * carrierWeight hn₂ hP₂ S₂ q₂) := by
  rw [s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel,
    s7c_turns_of_halves hn hP S q hn₁ hP₁ S₁ q₁ hn₂ hP₂ S₂ q₂ j j₁ j₂ e he, hj,
    s7c_turns_eq_erase_add _ j₁, hj₁, s7c_turns_eq_erase_add _ j₂, hj₂]
  exact s7c_sel_interlacing _ _ hs₀

/-- eq. s7c:noninterlacing-selector on carriers: contact turn `−s₀` on the full carrier `q` (at `j`), `s₀`
on both halves (at `j₁`, `j₂`), noncontact corners in turn-preserving bijection, a half with `≥ 2`
corners ⇒ `wt(q) · wt(q₁) wt(q₂) = 0`. -/
theorem s7c_carrierWeight_noninterlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    (S₂ : Finset (Crossing P₂)) (q₂ : Component hn₂ hP₂ S₂)
    (j : ZMod (ccpCornerCount hn hP S q)) (j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁))
    (j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)) {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hk : 2 ≤ ccpCornerCount hn₁ hP₁ S₁ q₁ ∨ 2 ≤ ccpCornerCount hn₂ hP₂ S₂ q₂)
    (hj : turn (ccpCornerPolygon hn hP S q) j = -s₀)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, turn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y => turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y => turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x) :
    carrierWeight hn hP S q * (carrierWeight hn₁ hP₁ S₁ q₁ * carrierWeight hn₂ hP₂ S₂ q₂) = 0 := by
  rw [s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel,
    s7c_turns_of_halves hn hP S q hn₁ hP₁ S₁ q₁ hn₂ hP₂ S₂ q₂ j j₁ j₂ e he, hj,
    s7c_turns_eq_erase_add _ j₁, hj₁, s7c_turns_eq_erase_add _ j₂, hj₂]
  apply s7c_sel_noninterlacing _ _ hs₀
  rcases hk with hk | hk
  · left
    rw [s7c_map_erase_eq_map_subtype]
    exact s7c_map_subtype_ne_zero hk _ j₁
  · right
    rw [s7c_map_erase_eq_map_subtype]
    exact s7c_map_subtype_ne_zero hk _ j₂

/-- The live interlacing row on carriers (sm-4:558-562, 656-660): `wt(q) ≠ 0` ⇒ all three carriers are
uniform of the contact sign `s₀` (the shape lem:uniformrot and the floor take). -/
theorem s7c_uniform_halves_of_interlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    (S₂ : Finset (Crossing P₂)) (q₂ : Component hn₂ hP₂ S₂)
    (j : ZMod (ccpCornerCount hn hP S q)) (j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁))
    (j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)) {s₀ : SignType}
    (hj : turn (ccpCornerPolygon hn hP S q) j = s₀)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, turn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y => turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y => turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    (hW : carrierWeight hn hP S q ≠ 0) :
    (∀ i, turn (ccpCornerPolygon hn hP S q) i = s₀) ∧
      (∀ i, turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = s₀) ∧
      (∀ i, turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = s₀) := by
  have hall := s7c_forall_turn_of_weight_ne_zero hn hP S q hW hj
  refine ⟨hall, fun i => ?_, fun i => ?_⟩
  · by_cases hi : i = j₁
    · rw [hi, hj₁]
    · have := he (Sum.inl ⟨i, hi⟩)
      rw [hall] at this
      exact this.symm
  · by_cases hi : i = j₂
    · rw [hi, hj₂]
    · have := he (Sum.inr ⟨i, hi⟩)
      rw [hall] at this
      exact this.symm

/-- The live noninterlacing row on carriers (sm-4:742-747): `wt(q) ≠ 0` ⇒ the full carrier is uniform of
sign `−s₀` and each half has exactly one dissent (its contact corner, of sign `s₀`) among turns `−s₀` —
the `SignedUniformOrOneDissent` patterns `a_floor` needs at the two half contact carriers. -/
theorem s7c_dissent_halves_of_noninterlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    (S₂ : Finset (Crossing P₂)) (q₂ : Component hn₂ hP₂ S₂)
    (j : ZMod (ccpCornerCount hn hP S q)) (j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁))
    (j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)) {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj : turn (ccpCornerPolygon hn hP S q) j = -s₀)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, turn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y => turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y => turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    (hW : carrierWeight hn hP S q ≠ 0) :
    (∀ i, turn (ccpCornerPolygon hn hP S q) i = -s₀) ∧
      (∀ i, i ≠ j₁ → turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = -s₀) ∧
      (∀ i, i ≠ j₂ → turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = -s₀) ∧
      SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁) ∧
      SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂) := by
  have hall := s7c_forall_turn_of_weight_ne_zero hn hP S q hW hj
  have h₁ : ∀ i, i ≠ j₁ → turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = -s₀ := by
    intro i hi
    have := he (Sum.inl ⟨i, hi⟩)
    rw [hall] at this
    exact this.symm
  have h₂ : ∀ i, i ≠ j₂ → turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = -s₀ := by
    intro i hi
    have := he (Sum.inr ⟨i, hi⟩)
    rw [hall] at this
    exact this.symm
  refine ⟨hall, h₁, h₂, ?_, ?_⟩
  · exact s7c_signedUniformOrOneDissent_of_dissent _ (s7c_neg_sign_ne_zero hs₀) j₁
      (by rw [hj₁, neg_neg]) h₁
  · exact s7c_signedUniformOrOneDissent_of_dissent _ (s7c_neg_sign_ne_zero hs₀) j₂
      (by rw [hj₂, neg_neg]) h₂

end S7CSelector

/-! ### U110-D helpers (prefix `s7d_`): coefficient transport for spectators / relocated carriers -/

/-- `List.next` commutes with an injective-on-the-list map. -/
theorem s7d_next_map {α β : Type*} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hnd : (l.map f).Nodup) (x : α) (hx : x ∈ l) :
    (l.map f).next (f x) (List.mem_map_of_mem hx) = f (l.next x hx) := by
  have hl : l.Nodup := hnd.of_map f
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi' : i < (l.map f).length := by rw [List.length_map]; exact hi
  have h := List.next_getElem (l.map f) hnd i hi'
  simp only [List.getElem_map, List.length_map] at h
  rw [List.next_getElem l hl i hi]
  exact h

/-- The record-level bridge: a visit map carrying the restricted Gauss list of `X` to a rotation of the
restricted Gauss list of `Y`, commuting with the twin on `X`-visits and preserving the positive over bit,
induces a record isomorphism of the abstract restricted Gauss records (`gaussRecord`, KL0). -/
def s7d_gaussRecordIso {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}
    (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q) (X : Finset (Crossing P))
    (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q)
    (hrot : (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ))
    (htwin : ∀ v : Visit P, v.1 ∈ X → φ (visitTwin v) = visitTwin (φ v))
    (hbit : ∀ v : Visit P, v.1 ∈ X → CB.positiveOverBit (φ v) = CB.positiveOverBit v) :
    RecordIso (CB.gaussRecord hcP X) (CB.gaussRecord hcQ Y) :=
  have hndm : ((CB.gaussList hcP X).map φ).Nodup := hrot.nodup_iff.mp (CB.kl0_gaussList_nodup hcQ Y)
  have hmemφ : ∀ v : Visit P, v.1 ∈ X → (φ v).1 ∈ Y := fun v hv => by
    rw [← CB.kl0_mem_gaussList hcQ Y, hrot.mem_iff]
    exact List.mem_map_of_mem ((CB.kl0_mem_gaussList hcP X v).mpr hv)
  let f : {v : Visit P // v.1 ∈ X} → {w : Visit Q // w.1 ∈ Y} := fun v => ⟨φ v.1, hmemφ v.1 v.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      have h' : φ v.1 = φ w.1 := congrArg Subtype.val h
      exact Subtype.ext (List.inj_on_of_nodup_map hndm ((CB.kl0_mem_gaussList hcP X v.1).mpr v.2)
        ((CB.kl0_mem_gaussList hcP X w.1).mpr w.2) h')
    · intro w
      have hw : w.1 ∈ (CB.gaussList hcP X).map φ := by
        rw [← hrot.mem_iff]
        exact (CB.kl0_mem_gaussList hcQ Y w.1).mpr w.2
      obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hw
      exact ⟨⟨v, (CB.kl0_mem_gaussList hcP X v).mp hv⟩, Subtype.ext hvw⟩
  { e := Equiv.refl Unit
    Φ := Equiv.ofBijective f hf
    comp_eq := fun _ => Subsingleton.elim (α := Unit) _ _
    succ_eq := fun v => by
      apply Subtype.ext
      have hv : v.1 ∈ CB.gaussList hcP X := (CB.kl0_mem_gaussList hcP X v.1).mpr v.2
      have hfv : (f v).1 ∈ CB.gaussList hcQ Y := (CB.kl0_mem_gaussList hcQ Y _).mpr (f v).2
      show φ (CB.gaussSucc hcP X v).1 = (CB.gaussSucc hcQ Y (f v)).1
      rw [CB.gaussSucc_val hcP X v hv, CB.gaussSucc_val hcQ Y (f v) hfv,
        List.isRotated_next_eq hrot (CB.kl0_gaussList_nodup hcQ Y) hfv]
      exact (s7d_next_map (CB.gaussList hcP X) φ hndm v.1 hv).symm
    pair_eq := fun v => by
      apply Subtype.ext
      show φ (visitTwin v.1) = visitTwin (φ v.1)
      exact htwin v.1 v.2
    bit_eq := fun v => hbit v.1 v.2
    sgn_eq := fun _ => rfl }

/-- Two restricted Gauss lists with the same members (via `φ`) and `φ` strictly increasing in the traversal
key on `X`-visits are literally equal after mapping (both are the strictly key-sorted lists of their members). -/
theorem s7d_gaussList_eq_of_strictMono {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}
    (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q) (X : Finset (Crossing P))
    (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w)) :
    CB.gaussList hcQ Y = (CB.gaussList hcP X).map φ := by
  have hsortP : (CB.gaussList hcP X).Pairwise
      (fun v w => geometricVisitKey hcP v < geometricVisitKey hcP w) :=
    CB.kl2_gaussList_pairwise_lt hcP X
  have hsortQ : (CB.gaussList hcQ Y).Pairwise
      (fun v w => geometricVisitKey hcQ v < geometricVisitKey hcQ w) :=
    CB.kl2_gaussList_pairwise_lt hcQ Y
  have hsortM : ((CB.gaussList hcP X).map φ).Pairwise
      (fun v w => geometricVisitKey hcQ v < geometricVisitKey hcQ w) := by
    rw [List.pairwise_map]
    refine (List.Pairwise.and_mem.mp hsortP).imp ?_
    rintro v w ⟨hv, hw, hlt⟩
    exact hmono v w ((CB.kl0_mem_gaussList hcP X v).mp hv) ((CB.kl0_mem_gaussList hcP X w).mp hw) hlt
  -- the mapped list has no duplicates (strict monotonicity forces injectivity on `X`-visits)
  have hnd : ((CB.gaussList hcP X).map φ).Nodup := by
    rw [List.nodup_iff_pairwise_ne] at *
    exact hsortM.imp fun h => ne_of_lt h |> fun h' => fun e => h' (by rw [e])
  have hperm : (CB.gaussList hcQ Y).Perm ((CB.gaussList hcP X).map φ) := by
    rw [List.perm_ext_iff_of_nodup (CB.kl0_gaussList_nodup hcQ Y) hnd]
    intro w
    rw [CB.kl0_mem_gaussList, hmem, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (CB.kl0_mem_gaussList hcP X v).mpr hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (CB.kl0_mem_gaussList hcP X v).mp hv, rfl⟩
  exact List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _))
    hsortQ hsortM hperm

omit [NeZero n] in
/-- The positive over bit is `det(d_v, d_{τ v}) > 0`: equivalent determinant signs give equal bits. -/
theorem s7d_positiveOverBit_eq_of_det_pos_iff {m : ℕ} [NeZero m] {P : LabelledTuple n}
    {Q : LabelledTuple m} (v : Visit P) (w : Visit Q)
    (h : 0 < det (edge Q w.2.val) (edge Q (visitTwin w).2.val) ↔
      0 < det (edge P v.2.val) (edge P (visitTwin v).2.val)) :
    CB.positiveOverBit w = CB.positiveOverBit v := by
  unfold CB.positiveOverBit
  exact decide_eq_decide.mpr h

omit [NeZero n] in
/-- Determinants scale by the product of positive factors. -/
theorem s7d_det_smul_smul (c d : ℝ) (u w : Plane) : det (c • u) (d • w) = (c * d) * det u w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

omit [NeZero n] in
/-- Relocated carriers whose edge directions at the visit and at its twin are POSITIVE multiples of the
originals (the cut edges of a half, or the corner edges `corner_polygons.2.1`) keep the over bit. -/
theorem s7d_positiveOverBit_eq_of_smul {m : ℕ} [NeZero m] {P : LabelledTuple n}
    {Q : LabelledTuple m} (v : Visit P) (w : Visit Q) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (h1 : edge Q w.2.val = c • edge P v.2.val)
    (h2 : edge Q (visitTwin w).2.val = d • edge P (visitTwin v).2.val) :
    CB.positiveOverBit w = CB.positiveOverBit v := by
  apply s7d_positiveOverBit_eq_of_det_pos_iff
  rw [h1, h2, s7d_det_smul_smul]
  constructor
  · intro h
    exact pos_of_mul_pos_right h (mul_pos hc hd).le
  · intro h
    exact mul_pos (mul_pos hc hd) h

omit [NeZero n] in
/-- The positive over bit is read off the sign of `det(d_v, d_{τ v})`: equal crossing signs at a visit and
its image give equal bits. -/
theorem s7d_positiveOverBit_eq_of_crossingSign {m : ℕ} [NeZero m] {P : LabelledTuple n}
    {Q : LabelledTuple m} (v : Visit P) (w : Visit Q)
    (h : crossingSign Q w.2.val (visitTwin w).2.val = crossingSign P v.2.val (visitTwin v).2.val) :
    CB.positiveOverBit w = CB.positiveOverBit v := by
  unfold CB.positiveOverBit
  unfold crossingSign at h
  by_cases hp : 0 < det (edge P v.2.val) (edge P (visitTwin v).2.val)
  · have hq : 0 < det (edge Q w.2.val) (edge Q (visitTwin w).2.val) := by
      rw [← sign_eq_one_iff, h, sign_eq_one_iff]; exact hp
    simp [hp, hq]
  · have hq : ¬ 0 < det (edge Q w.2.val) (edge Q (visitTwin w).2.val) := by
      rw [← sign_eq_one_iff, h, sign_eq_one_iff]; exact hp
    simp [hp, hq]

/-! #### The coefficient transport proper: `H⁺`, `m`, `d` and `c` of two carriers with isomorphic
restricted Gauss records and equal rotations agree (across polygons of different sizes). -/

/-- `H⁺_q = H⁺_{q'}` when the abstract restricted Gauss records of the two carriers are isomorphic
(the CB record bridge `positiveLiftRecordIso` on both sides and lc:presentations, via `P_eq_homfly`). -/
theorem s7d_cornerHomfly_eq_of_recordIso {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (h : Nonempty (RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q))
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q')))) :
    cornerHomfly hn hP S q hS = cornerHomfly hm hQ T q' hT := by
  unfold cornerHomfly
  rw [← P_eq_homfly, ← P_eq_homfly]
  exact presentations _ _ ⟨(CB.positiveLiftRecordIso hn hP hS q).trans
    (h.some.trans (CB.positiveLiftRecordIso hm hQ hT q').symm)⟩

/-- `m_q = m_{q'}`: a record isomorphism preserves the number of occurrences, which is twice the number of
crossings of the carrier (`kl1_card_retained`). -/
theorem s7d_carrierCrossingCount_eq_of_recordIso {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (q : Component hn hP S)
    {T : Finset (Crossing Q)} (q' : Component hm hQ T)
    (h : Nonempty (RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q))
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q')))) :
    carrierCrossingCount hn hP S q = carrierCrossingCount hm hQ T q' := by
  have h1 := h.some.card_M_eq
  have e1 : Fintype.card (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q)).M =
      Fintype.card {u : Visit P // u.1 ∈ carrierCrossings hn hP S q} :=
    Fintype.card_congr (Equiv.refl _)
  have e2 : Fintype.card (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q')).M =
      Fintype.card {u : Visit Q // u.1 ∈ carrierCrossings hm hQ T q'} :=
    Fintype.card_congr (Equiv.refl _)
  rw [e1, e2, CB.kl1_card_retained hn hP q, CB.kl1_card_retained hm hQ q'] at h1
  rw [carrierCrossingCount_eq_card, carrierCrossingCount_eq_card]
  omega

/-- `d_q = d_{q'}` from the record isomorphism and equal (real) rotations. -/
theorem s7d_cornerSlot_eq_of_recordIso {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (q : Component hn hP S)
    {T : Finset (Crossing Q)} (q' : Component hm hQ T)
    (h : Nonempty (RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q))
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q'))))
    (hrot : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerSlot hn hP S q = cornerSlot hm hQ T q' := by
  unfold cornerSlot carrierRotationInt
  rw [s7d_carrierCrossingCount_eq_of_recordIso hn hm hP hQ q q' h, hrot]

/-- **Coefficient transport.** `c(q) = c(q')` for two carriers (of decompositions of possibly different
generic polygons) with isomorphic restricted Gauss records and equal rotations. -/
theorem s7d_cornerCoefficient_eq_of_recordIso {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (h : Nonempty (RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S q))
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q'))))
    (hrot : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt,
    s7d_cornerSlot_eq_of_recordIso hn hm hP hQ q q' h hrot,
    s7d_cornerHomfly_eq_of_recordIso hn hm hP hQ hS q hT q' h]

/-- Coefficient transport in the list form: a visit map `φ` carrying the carrier's restricted Gauss list to a
rotation of the other carrier's, commuting with the twin and preserving the over bits on the carrier's
crossings, plus equal rotations. -/
theorem s7d_cornerCoefficient_eq_of_gaussList_rotated {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (φ : Visit P → Visit Q)
    (hrot : (CB.gaussList (CB.cg hm hQ) (carrierCrossings hm hQ T q')).IsRotated
      ((CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S q)).map φ))
    (htwin : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q → φ (visitTwin v) = visitTwin (φ v))
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (φ v) = CB.positiveOverBit v)
    (hr : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT :=
  s7d_cornerCoefficient_eq_of_recordIso hn hm hP hQ hS q hT q'
    ⟨s7d_gaussRecordIso _ _ _ _ φ hrot htwin hbit⟩ hr

/-- Coefficient transport in the key-monotone form (the form the persistent-visit-order clause
`VertexLocalData.visit_order` of lem:wall-sides (V) delivers): `φ` maps the carrier's crossings' visits onto
the other carrier's crossings' visits, strictly increasing in the traversal key, twin-compatible, bit-preserving;
rotations equal. -/
theorem s7d_cornerCoefficient_eq_of_strictMono {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (φ : Visit P → Visit Q)
    (hmem : ∀ w : Visit Q, w.1 ∈ carrierCrossings hm hQ T q' ↔
      ∃ v : Visit P, v.1 ∈ carrierCrossings hn hP S q ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ carrierCrossings hn hP S q → w.1 ∈ carrierCrossings hn hP S q →
      geometricVisitKey (CB.cg hn hP) v < geometricVisitKey (CB.cg hn hP) w →
        geometricVisitKey (CB.cg hm hQ) (φ v) < geometricVisitKey (CB.cg hm hQ) (φ w))
    (htwin : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q → φ (visitTwin v) = visitTwin (φ v))
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (φ v) = CB.positiveOverBit v)
    (hr : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT :=
  s7d_cornerCoefficient_eq_of_gaussList_rotated hn hm hP hQ hS q hT q' φ
    (by rw [s7d_gaussList_eq_of_strictMono _ _ _ _ φ hmem hmono]) htwin hbit hr

/-- The corner product is carried by a bijection of carriers with equal coefficients. -/
theorem s7d_cornerProduct_eq_of_equiv {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T)
    (e : Component hn hP S ≃ Component hm hQ T)
    (hcoef : ∀ q, cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T (e q) hT) :
    cornerProduct hn hP S hS = cornerProduct hm hQ T hT := by
  unfold cornerProduct
  exact Fintype.prod_equiv e _ _ hcoef

/-! #### The cut form: a visit map monotone in the traversal key up to ONE cyclic cut (the labelling of a
half starts at the contact vertex; the traversal order of the parent's retained visits is a rotation of the
half's).  The mapped list is then a rotation of the sorted list. -/

/-- A strictly key-sorted list splits at a threshold: the members below `c` form a prefix. -/
theorem s7d_sorted_eq_filter_append {α : Type*} (key : α → ℝ) (c : ℝ) (l : List α)
    (hl : l.Pairwise (fun v w => key v < key w)) :
    l = l.filter (fun v => decide (key v < c)) ++ l.filter (fun v => !decide (key v < c)) := by
  have hperm : (l.filter (fun v => decide (key v < c)) ++ l.filter (fun v => !decide (key v < c))).Perm l :=
    List.filter_append_perm _ l
  symm
  refine List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _))
    ?_ hl hperm
  rw [List.pairwise_append]
  refine ⟨hl.filter _, hl.filter _, ?_⟩
  intro a ha b hb
  simp only [List.mem_filter, decide_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at ha hb
  exact lt_of_lt_of_le ha.2 hb.2

/-- The cut form of the restricted Gauss list transport: `φ` maps the `X`-visits onto the `Y`-visits, is
strictly key-increasing within each of the two blocks `key < c` / `key ≥ c`, and puts the block `key ≥ c` before
the block `key < c` in `Q`; then the `Y`-list is a rotation of the mapped `X`-list. -/
theorem s7d_gaussList_isRotated_of_cut {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}
    (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q) (X : Finset (Crossing P))
    (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q) (c : ℝ)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
      (geometricVisitKey hcP w < c ∨ c ≤ geometricVisitKey hcP v) →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w))
    (hcut : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < c → c ≤ geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ w) < geometricVisitKey hcQ (φ v)) :
    (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ) := by
  set L := CB.gaussList hcP X with hL
  set A := L.filter (fun v => decide (geometricVisitKey hcP v < c)) with hA
  set B := L.filter (fun v => !decide (geometricVisitKey hcP v < c)) with hB
  have hsortP : L.Pairwise (fun v w => geometricVisitKey hcP v < geometricVisitKey hcP w) :=
    CB.kl2_gaussList_pairwise_lt hcP X
  have hsplit : L = A ++ B := s7d_sorted_eq_filter_append (geometricVisitKey hcP) c L hsortP
  have hmemA : ∀ v ∈ A, v.1 ∈ X ∧ geometricVisitKey hcP v < c := fun v hv => by
    rw [hA, List.mem_filter, decide_eq_true_iff] at hv
    exact ⟨(CB.kl0_mem_gaussList hcP X v).mp hv.1, hv.2⟩
  have hmemB : ∀ v ∈ B, v.1 ∈ X ∧ c ≤ geometricVisitKey hcP v := fun v hv => by
    rw [hB] at hv
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hv
    exact ⟨(CB.kl0_mem_gaussList hcP X v).mp hv.1, hv.2⟩
  -- the rotated candidate `B ++ A`, mapped, is strictly key-sorted in `Q`
  have hsortBA : ((B ++ A).map φ).Pairwise
      (fun v w => geometricVisitKey hcQ v < geometricVisitKey hcQ w) := by
    rw [List.pairwise_map, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · refine (List.Pairwise.and_mem.mp (hsortP.filter _)).imp ?_
      rintro v w ⟨hv, hw, hlt⟩
      exact hmono v w (hmemB v hv).1 (hmemB w hw).1 hlt (Or.inr (hmemB v hv).2)
    · refine (List.Pairwise.and_mem.mp (hsortP.filter _)).imp ?_
      rintro v w ⟨hv, hw, hlt⟩
      exact hmono v w (hmemA v hv).1 (hmemA w hw).1 hlt (Or.inl (hmemA w hw).2)
    · intro b hb a ha
      exact hcut a b (hmemA a ha).1 (hmemB b hb).1 (hmemA a ha).2 (hmemB b hb).2
  have hnd : ((B ++ A).map φ).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hsortBA.imp fun h e => absurd (by rw [e] at h; exact h) (lt_irrefl _)
  have hsortQ : (CB.gaussList hcQ Y).Pairwise
      (fun v w => geometricVisitKey hcQ v < geometricVisitKey hcQ w) :=
    CB.kl2_gaussList_pairwise_lt hcQ Y
  have hperm : (CB.gaussList hcQ Y).Perm ((B ++ A).map φ) := by
    rw [List.perm_ext_iff_of_nodup (CB.kl0_gaussList_nodup hcQ Y) hnd]
    intro w
    have hBA : ∀ v, v ∈ B ++ A ↔ v ∈ L := fun v => by
      rw [hsplit, List.mem_append, List.mem_append]; exact or_comm
    rw [CB.kl0_mem_gaussList, hmem, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (hBA v).mpr ((CB.kl0_mem_gaussList hcP X v).mpr hv), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (CB.kl0_mem_gaussList hcP X v).mp ((hBA v).mp hv), rfl⟩
  have heq : CB.gaussList hcQ Y = (B ++ A).map φ :=
    List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _))
      hsortQ hsortBA hperm
  rw [heq, hsplit, List.map_append, List.map_append]
  exact List.isRotated_append

/-- Coefficient transport in the cut form (relocation to a half whose labelling starts at the contact). -/
theorem s7d_cornerCoefficient_eq_of_cut {m : ℕ} [NeZero m] (hn : 3 ≤ n) (hm : 3 ≤ m)
    {P : LabelledTuple n} {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q' : Component hm hQ T)
    (φ : Visit P → Visit Q) (c : ℝ)
    (hmem : ∀ w : Visit Q, w.1 ∈ carrierCrossings hm hQ T q' ↔
      ∃ v : Visit P, v.1 ∈ carrierCrossings hn hP S q ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ carrierCrossings hn hP S q → w.1 ∈ carrierCrossings hn hP S q →
      geometricVisitKey (CB.cg hn hP) v < geometricVisitKey (CB.cg hn hP) w →
      (geometricVisitKey (CB.cg hn hP) w < c ∨ c ≤ geometricVisitKey (CB.cg hn hP) v) →
        geometricVisitKey (CB.cg hm hQ) (φ v) < geometricVisitKey (CB.cg hm hQ) (φ w))
    (hcut : ∀ v w : Visit P, v.1 ∈ carrierCrossings hn hP S q → w.1 ∈ carrierCrossings hn hP S q →
      geometricVisitKey (CB.cg hn hP) v < c → c ≤ geometricVisitKey (CB.cg hn hP) w →
        geometricVisitKey (CB.cg hm hQ) (φ w) < geometricVisitKey (CB.cg hm hQ) (φ v))
    (htwin : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q → φ (visitTwin v) = visitTwin (φ v))
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (φ v) = CB.positiveOverBit v)
    (hr : carrierRotation hn hP S q = carrierRotation hm hQ T q') :
    cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT :=
  s7d_cornerCoefficient_eq_of_gaussList_rotated hn hm hP hQ hS q hT q' φ
    (s7d_gaussList_isRotated_of_cut _ _ _ _ φ c hmem hmono hcut) htwin hbit hr

omit [NeZero n] in
/-- Membership bookkeeping for a global visit bijection: `φ` carries `X`-visits onto `Y`-visits. -/
theorem s7d_mem_iff_of_equiv {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}
    (X : Finset (Crossing P)) (Y : Finset (Crossing Q)) (φ : Visit P ≃ Visit Q)
    (hXY : ∀ v : Visit P, (φ v).1 ∈ Y ↔ v.1 ∈ X) (w : Visit Q) :
    w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w := by
  constructor
  · intro hw
    refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
    rw [← hXY, φ.apply_symm_apply]; exact hw
  · rintro ⟨v, hv, rfl⟩
    exact (hXY v).mpr hv

/-! #### Decoding the traversal key: edge label first, then the edge parameter (the form in which
lem:wall-sides (V) `VertexLocalData.visit_order` states the persistent visit order). -/

/-- `key v < key w` iff `v` is on an earlier edge, or on the same edge at a smaller parameter. -/
theorem s7d_geometricVisitKey_lt_iff {P : LabelledTuple n} (hc : CrossingGeometry P) (v w : Visit P) :
    geometricVisitKey hc v < geometricVisitKey hc w ↔
      (v.2.val.val < w.2.val.val ∨ (v.2.val = w.2.val ∧ visitParameter v < visitParameter w)) := by
  have hv : geometricVisitKey hc v = (v.2.val.val : ℝ) + visitParameter v := rfl
  have hw : geometricVisitKey hc w = (w.2.val.val : ℝ) + visitParameter w := rfl
  have hv1 := (crossingParameter_interior_of_geometry hc v.1 v.2.val v.2.property)
  have hw1 := (crossingParameter_interior_of_geometry hc w.1 w.2.val w.2.property)
  change 0 < visitParameter v ∧ visitParameter v < 1 at hv1
  change 0 < visitParameter w ∧ visitParameter w < 1 at hw1
  constructor
  · intro h
    rcases lt_trichotomy v.2.val.val w.2.val.val with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr ⟨ZMod.val_injective n heq, ?_⟩
      rw [hv, hw, heq] at h
      linarith
    · exfalso
      have h1 : (w.2.val.val : ℝ) + 1 ≤ v.2.val.val := by exact_mod_cast hgt
      rw [hv, hw] at h
      linarith
  · rintro (hlt | ⟨he, hp⟩)
    · have h1 : (v.2.val.val : ℝ) + 1 ≤ w.2.val.val := by exact_mod_cast hlt
      rw [hv, hw]
      linarith
    · rw [hv, hw, he]
      linarith

/-- Strict key-monotonicity of a visit map between polygons with the same labels, from edge preservation and
edgewise preservation of the parameter order (on the visits of `X`). -/
theorem s7d_strictMono_of_edgewise {P Q : LabelledTuple n} (hcP : CrossingGeometry P)
    (hcQ : CrossingGeometry Q) (X : Finset (Crossing P)) (φ : Visit P → Visit Q)
    (hedge : ∀ v : Visit P, v.1 ∈ X → (φ v).2.val = v.2.val)
    (hpar : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X → v.2.val = w.2.val →
      visitParameter v < visitParameter w → visitParameter (φ v) < visitParameter (φ w)) :
    ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w) := by
  intro v w hv hw h
  rw [s7d_geometricVisitKey_lt_iff] at h ⊢
  rw [hedge v hv, hedge w hw]
  rcases h with h | ⟨he, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨he, hpar v w hv hw he hp⟩

/-! #### A full mark transport (SM/CChamber.lean `MarkTransport`) carries the restricted Gauss lists: a
`Deform`-free proof of the homfly hypothesis of `MarkTransport.cornerCoefficient_transport`, given the
crossing signs (over bits) are preserved. -/

/-- Rotations pass through `filterMap`. -/
theorem s7d_isRotated_filterMap {α β : Type*} (f : α → Option β) {l l' : List α}
    (h : l.IsRotated l') : (l.filterMap f).IsRotated (l'.filterMap f) := by
  obtain ⟨k, hk, rfl⟩ := List.isRotated_iff_mod.mp h
  have h1 := List.isRotated_append (l := (l.take k).filterMap f) (l' := (l.drop k).filterMap f)
  rw [← List.filterMap_append, List.take_append_drop] at h1
  rw [List.rotate_eq_drop_append_take hk, List.filterMap_append]
  exact h1

/-- Rotations pass through `filter`. -/
theorem s7d_isRotated_filter {α : Type*} (p : α → Bool) {l l' : List α}
    (h : l.IsRotated l') : (l.filter p).IsRotated (l'.filter p) := by
  obtain ⟨k, hk, rfl⟩ := List.isRotated_iff_mod.mp h
  have h1 := List.isRotated_append (l := (l.take k).filter p) (l' := (l.drop k).filter p)
  rw [← List.filter_append, List.take_append_drop] at h1
  rw [List.rotate_eq_drop_append_take hk, List.filter_append]
  exact h1

/-- The visits of the key-sorted mark list, in order, form the key-sorted Gauss list. -/
theorem s7d_markList_filterMap (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (markList hn hP).filterMap Sum.getRight? = geometricGaussList (CB.cg hn hP) := by
  have hsortM : ((markList hn hP).filterMap Sum.getRight?).Pairwise
      (fun v w : Visit P => geometricVisitKey (CB.cg hn hP) v < geometricVisitKey (CB.cg hn hP) w) := by
    refine List.Pairwise.filterMap _ ?_
      (CB.kl1_pairwise_lt (markList_sorted hn hP) (markList_nodup hn hP) (markKey_injective hn hP))
    intro a a' hlt b hb b' hb'
    cases a with
    | inl i => simp at hb
    | inr v =>
      cases a' with
      | inl i => simp at hb'
      | inr w =>
        simp only [Sum.getRight?_inr, Option.some.injEq] at hb hb'
        subst hb; subst hb'
        exact hlt
  have hsortG : (geometricGaussList (CB.cg hn hP)).Pairwise
      (fun v w : Visit P => geometricVisitKey (CB.cg hn hP) v < geometricVisitKey (CB.cg hn hP) w) :=
    CB.kl1_pairwise_lt (geometricGaussList_sorted _) (geometricGaussList_nodup _)
      (geometricVisitKey_injective _)
  have hnd : ((markList hn hP).filterMap Sum.getRight?).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hsortM.imp fun h e => absurd (by rw [e] at h; exact h) (lt_irrefl _)
  have hperm : ((markList hn hP).filterMap Sum.getRight?).Perm (geometricGaussList (CB.cg hn hP)) := by
    rw [List.perm_ext_iff_of_nodup hnd (geometricGaussList_nodup _)]
    intro v
    refine iff_of_true ?_ (mem_geometricGaussList _ v)
    rw [List.mem_filterMap]
    exact ⟨Sum.inr v, mem_markList hn hP _, rfl⟩
  exact List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _))
    hsortM hsortG hperm

/-- A mark transport carries the restricted Gauss list of `X` to a rotation of the restricted Gauss list of
the transported support (from `markList_rotated`, through `filterMap`/`filter`). -/
theorem s7d_gaussList_transport {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
    (τ : MarkTransport hn hP hQ) (X : Finset (Crossing P)) :
    (CB.gaussList (CB.cg hn hQ) (τ.support X)).IsRotated
      ((CB.gaussList (CB.cg hn hP) X).map τ.visit) := by
  unfold CB.gaussList
  rw [← s7d_markList_filterMap hn hQ, ← s7d_markList_filterMap hn hP]
  have h1 := s7d_isRotated_filter (fun v : Visit Q => decide (v.1 ∈ τ.support X))
    (s7d_isRotated_filterMap Sum.getRight? τ.markList_rotated)
  refine h1.trans ?_
  have h2 : ((markList hn hP).map (Sum.map τ.vert τ.visit)).filterMap Sum.getRight? =
      ((markList hn hP).filterMap Sum.getRight?).map τ.visit := by
    rw [List.filterMap_map, List.map_filterMap]
    congr 1
    funext m
    cases m <;> rfl
  rw [h2, List.filter_map]
  have h3 : ∀ v ∈ (markList hn hP).filterMap Sum.getRight?,
      ((fun w : Visit Q => decide (w.1 ∈ τ.support X)) ∘ τ.visit) v = decide (v.1 ∈ X) := by
    intro v _
    simp only [Function.comp_apply, τ.visit_fst, τ.mem_support]
  rw [List.filter_congr h3]

/-- **Deform-free homfly transport along a mark transport** preserving the positive over bits on the
carrier's crossings: the restricted Gauss records are isomorphic (`s7d_gaussRecordIso`), hence the positive
lifts have equal `homfly` (lc:presentations). -/
theorem s7d_homfly_transport {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
    (τ : MarkTransport hn hP hQ) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (τ.visit v) = CB.positiveOverBit v) :
    homfly (positiveLift hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS)) =
      homfly (positiveLift hn hP S q hS) := by
  have hrot : (CB.gaussList (CB.cg hn hQ) (carrierCrossings hn hQ (τ.support S) (τ.component S q))).IsRotated
      ((CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S q)).map τ.visit) := by
    rw [τ.carrierCrossings_transport S q]
    exact s7d_gaussList_transport τ _
  exact (s7d_cornerHomfly_eq_of_recordIso hn hn hP hQ hS q ((τ.isDecomposition_transport S).mpr hS)
    (τ.component S q) ⟨s7d_gaussRecordIso _ _ _ _ τ.visit hrot (fun v _ => τ.twin_eq v) hbit⟩).symm

/-- The over bits are preserved by a mark transport that preserves the crossing signs
`crossingSign P e (twin e)` at the visits of `X` (as CSilent's `sides_markTurn_eq` establishes for a silent
wall). -/
theorem s7d_positiveOverBit_transport {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P}
    {hQ : Generic Q} (τ : MarkTransport hn hP hQ) (X : Finset (Crossing P))
    (hsgn : ∀ v : Visit P, v.1 ∈ X →
      crossingSign Q (τ.visit v).2.val (τ.visit (visitTwin v)).2.val =
        crossingSign P v.2.val (visitTwin v).2.val) :
    ∀ v : Visit P, v.1 ∈ X → CB.positiveOverBit (τ.visit v) = CB.positiveOverBit v := by
  intro v hv
  apply s7d_positiveOverBit_eq_of_crossingSign
  rw [← τ.twin_eq]
  exact hsgn v hv

/-- `cornerCoefficient_transport` with the homfly hypothesis discharged by the record route: only the rotation
and the over bits remain. -/
theorem s7d_cornerCoefficient_transport {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P}
    {hQ : Generic Q} (τ : MarkTransport hn hP hQ) {S : Finset (Crossing P)}
    (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (hbit : ∀ v : Visit P, v.1 ∈ carrierCrossings hn hP S q →
      CB.positiveOverBit (τ.visit v) = CB.positiveOverBit v)
    (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q) :
    cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS :=
  τ.cornerCoefficient_transport hS q hrot (s7d_homfly_transport τ hS q hbit)

/-! ### Unit W2-S7A2 helpers (prefix `s7a2_`): the ROTATION EQUALITY `hr` of the persistent
transport (sm-4:483-503, eq. s7c:full-rotation; PLAN_FINAL §3.3 sliding step (1), bigon ineligible /
eligible `T`), the geometric input U110-A left open (U_S7A_REPORT §2) and U110-D's
`s7d_cornerCoefficient_eq_of_strictMono` / `_cut` and U110-I's `s7i_full_rotation_germ` consume.

Route.  For a persistent support `S` of the side `b` polygon `P = g.curve (g.sideTime b t)` and a
carrier `q`, the family `u ↦ s7a2_cornerFamily … q u` reads the corner marks of `q` on `g.curve u`
(vertex `i ↦ g.curve u i`; selected visit on edge `e` with twin edge `f` ↦ `edgePoint (g.curve u) e
(edgeParameter (g.curve u) e f)`, CSilent's `silentMarkPoint` template).  Its `j`-th edge is
`ψ_j(u) • edge (g.curve u) ε_j` (`s7a2_point_sub`), where `ε_j` is the outgoing edge of `c_j` = the
incoming edge of `c_{j+1}` (lem:carriers (ii), `ccpCornerPolygon_outEdge_eq_inEdge`) and `ψ_j(u)` is the
difference of the two Cramer parameters on `ε_j`.  `ψ_j` is positive at `u = sideTime b t`
(`ccpCornerPolygon_edge`), continuous on `|u| < δ` (`continuousAt_contact_edgeParameter` at the centre,
`continuousAt_edgeParameter` off it) and NEVER ZERO there — at the centre by `contact_pair_data`
(interior parameters) and `contact_unaffected_parameters_ne` (distinct parameters of two persistent
crossings on one edge) — so it is positive on `|u| ≤ t` by sign constancy (`s7a2_pos_of_ne_zero`):
"positive edge pieces".  The corner determinants are `ψ_{j-1} ψ_j det(edge ε_{j-1}, edge ε_j)` with the
last factor nonzero at every `|u| < δ` (vertex turns: `ChirotopesOutsideZerosAgree`; selected
crossings: `contact_pair_data.det_ne_zero`): "nonzero contact determinants".  Hence the family is
regular on `|u| ≤ t` INCLUDING the wall, and lem:rot (ii) (`rotationNumber_family_constant`) gives one
rotation number; the two side values are the corner polygon of `q` and (up to `recastTuple`) that of
`s7a_sideComponentEquiv … q` (`s7a_ccpCornerMark_map`), whence `hr` (`s7a2_carrierRotation_eq`).
The family with `s7a2_cornerFamily_continuousOn` / `s7a2_cornerFamily_regular` is exactly the object
`s7i_full_rotation_germ` / `s7i_carrierRotation_sides_of_family` expect. -/

section S7A2Marks

variable {R : LabelledTuple n}

omit [NeZero n] in
/-- The original edge along which the carrier LEAVES a true corner: the vertex's own edge, the
twin's edge for a selected visit (the smoothing continues along the twin's edge). -/
def s7a2_outEdge : Mark R → ZMod n
  | Sum.inl i => i
  | Sum.inr v => (visitTwin v).2.val

omit [NeZero n] in
/-- The original edge along which the carrier ARRIVES at a true corner: the previous edge at a
vertex, the visit's own edge at a visit. -/
def s7a2_inEdge : Mark R → ZMod n
  | Sum.inl i => i - 1
  | Sum.inr v => v.2.val

omit [NeZero n] in
/-- The parameter on `s7a2_outEdge m` at which the mark `m`, read on the polygon `Q`, leaves. -/
def s7a2_outParam (Q : LabelledTuple n) : Mark R → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => edgeParameter Q (visitTwin v).2.val v.2.val

omit [NeZero n] in
/-- The parameter on `s7a2_inEdge m` at which the mark `m`, read on the polygon `Q`, is reached. -/
def s7a2_inParam (Q : LabelledTuple n) : Mark R → ℝ
  | Sum.inl _ => 1
  | Sum.inr v => edgeParameter Q v.2.val (visitTwin v).2.val

omit [NeZero n] in
/-- The plane point of a mark of `R` READ ON the polygon `Q`: a vertex by its label, a visit as the
Cramer point of its edge and its twin's edge (CSilent's `silentMarkPoint`, for any pair `R`, `Q`). -/
def s7a2_point (Q : LabelledTuple n) : Mark R → Plane
  | Sum.inl i => Q i
  | Sum.inr v => edgePoint Q v.2.val (edgeParameter Q v.2.val (visitTwin v).2.val)

omit [NeZero n] in
@[simp] theorem s7a2_outEdge_inl (i : ZMod n) : s7a2_outEdge (Sum.inl i : Mark R) = i := rfl
omit [NeZero n] in
@[simp] theorem s7a2_outEdge_inr (v : Visit R) : s7a2_outEdge (Sum.inr v) = (visitTwin v).2.val := rfl
omit [NeZero n] in
@[simp] theorem s7a2_inEdge_inl (i : ZMod n) : s7a2_inEdge (Sum.inl i : Mark R) = i - 1 := rfl
omit [NeZero n] in
@[simp] theorem s7a2_inEdge_inr (v : Visit R) : s7a2_inEdge (Sum.inr v) = v.2.val := rfl
omit [NeZero n] in
@[simp] theorem s7a2_outParam_inl (Q : LabelledTuple n) (i : ZMod n) :
    s7a2_outParam Q (Sum.inl i : Mark R) = 0 := rfl
omit [NeZero n] in
@[simp] theorem s7a2_outParam_inr (Q : LabelledTuple n) (v : Visit R) :
    s7a2_outParam Q (Sum.inr v) = edgeParameter Q (visitTwin v).2.val v.2.val := rfl
omit [NeZero n] in
@[simp] theorem s7a2_inParam_inl (Q : LabelledTuple n) (i : ZMod n) :
    s7a2_inParam Q (Sum.inl i : Mark R) = 1 := rfl
omit [NeZero n] in
@[simp] theorem s7a2_inParam_inr (Q : LabelledTuple n) (v : Visit R) :
    s7a2_inParam Q (Sum.inr v) = edgeParameter Q v.2.val (visitTwin v).2.val := rfl
omit [NeZero n] in
@[simp] theorem s7a2_point_inl (Q : LabelledTuple n) (i : ZMod n) :
    s7a2_point Q (Sum.inl i : Mark R) = Q i := rfl
omit [NeZero n] in
@[simp] theorem s7a2_point_inr (Q : LabelledTuple n) (v : Visit R) :
    s7a2_point Q (Sum.inr v) = edgePoint Q v.2.val (edgeParameter Q v.2.val (visitTwin v).2.val) := rfl

omit [NeZero n] in
/-- Cramer's rule on abstract vectors: the two parametrisations of the intersection point of the
lines `a + ℝ u` and `b + ℝ v` agree when `det u v ≠ 0`. -/
theorem s7a2_cramer_vec (a b u v : Plane) (hd : det u v ≠ 0) :
    a + cramerFirst a b u v • u = b + cramerFirst b a v u • v := by
  unfold cramerFirst
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  simp only [det] at hd ⊢
  have hneg : v1 * u2 - v2 * u1 = -(u1 * v2 - u2 * v1) := by ring
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    rw [hneg, div_neg, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (b1 - a1) * (mul_inv_cancel₀ hd)
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    rw [hneg, div_neg, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (b2 - a2) * (mul_inv_cancel₀ hd)

omit [NeZero n] in
/-- **Cramer symmetry**: the crossing point of two transverse edge lines is the same whichever
edge it is read on. -/
theorem s7a2_cramer_symm (Q : LabelledTuple n) (e f : ZMod n)
    (hd : det (edge Q e) (edge Q f) ≠ 0) :
    edgePoint Q e (edgeParameter Q e f) = edgePoint Q f (edgeParameter Q f e) :=
  s7a2_cramer_vec (Q e) (Q f) (edge Q e) (edge Q f) hd

omit [NeZero n] in
/-- The point of a mark is reached on its incoming edge at its incoming parameter. -/
theorem s7a2_point_eq_in (Q : LabelledTuple n) (m : Mark R) :
    s7a2_point Q m = edgePoint Q (s7a2_inEdge m) (s7a2_inParam Q m) := by
  cases m with
  | inl i => rw [s7a2_point_inl, s7a2_inEdge_inl, s7a2_inParam_inl, edgePoint_one, sub_add_cancel]
  | inr v => rfl

omit [NeZero n] in
/-- The point of a mark is left on its outgoing edge at its outgoing parameter (for a visit this is
Cramer symmetry, so it needs the transversality of the visit's two edges on `Q`). -/
theorem s7a2_point_eq_out (Q : LabelledTuple n) (m : Mark R)
    (hd : ∀ v : Visit R, m = Sum.inr v → det (edge Q v.2.val) (edge Q (visitTwin v).2.val) ≠ 0) :
    s7a2_point Q m = edgePoint Q (s7a2_outEdge m) (s7a2_outParam Q m) := by
  cases m with
  | inl i => rw [s7a2_point_inl, s7a2_outEdge_inl, s7a2_outParam_inl, edgePoint_zero]
  | inr v =>
    rw [s7a2_point_inr, s7a2_outEdge_inr, s7a2_outParam_inr]
    exact s7a2_cramer_symm Q _ _ (hd v rfl)

/-- **The edge formula.** When the outgoing edge of `m` is the incoming edge of `m'`, the vector from
the point of `m` to the point of `m'` (both read on `Q`) is the parameter difference times that
original edge direction. -/
theorem s7a2_point_sub (Q : LabelledTuple n) (m m' : Mark R)
    (hε : s7a2_outEdge m = s7a2_inEdge m')
    (hd : ∀ v : Visit R, m = Sum.inr v → det (edge Q v.2.val) (edge Q (visitTwin v).2.val) ≠ 0) :
    s7a2_point Q m' - s7a2_point Q m =
      (s7a2_inParam Q m' - s7a2_outParam Q m) • edge Q (s7a2_outEdge m) := by
  rw [s7a2_point_eq_in Q m', s7a2_point_eq_out Q m hd, ← hε, edgePoint_sub_edgePoint]

/-! #### On a generic polygon: the mark points are the corner-polygon points, and consecutive
corners of a carrier are joined along one original edge with increasing parameters (lem:carriers
(ii), `ccpCornerPolygon_edge`). -/

/-- The point of a mark read on its own generic polygon is its traversal point. -/
theorem s7a2_point_eq_evaluation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (m : Mark P) :
    traversalEvaluation P (markPosition hn hP.1 m) = s7a2_point P m := by
  cases m with
  | inl i => rw [markPosition_evaluation_vertex]; rfl
  | inr v =>
    rw [markPosition_evaluation_visit, s7a2_point_inr,
      (crossingParameter_spec v.1 v.2.val v.2.property).2.2]
    have h := visitParameter_eq_of_support_pair hn hP.1 v (visitTwin v).2.val
      (visit_crossing_val_eq_pair v)
    unfold visitParameter at h
    rw [h]

omit [NeZero n] in
/-- The crossing of a visit, as the pair of its edge and its twin's edge. -/
theorem s7a2_visit_isCrossing {P : LabelledTuple n} (v : Visit P) :
    IsCrossing P {v.2.val, (visitTwin v).2.val} := by
  rw [← visit_crossing_val_eq_pair v]
  exact v.1.property

/-- The outgoing slot of a true corner lies on `s7a2_outEdge`. -/
theorem s7a2_outSlot_fst (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (m : Mark P) (hm : IsTrueCorner S m) :
    (ccpOutSlot hn hP S m).1 = s7a2_outEdge m := by
  cases m with
  | inl i => rfl
  | inr v => exact ccpOutSlot_selected hn hP S v hm

/-- The incoming edge of a mark is `s7a2_inEdge`. -/
theorem s7a2_inEdge_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (m : Mark P) :
    ccpInEdge hn hP m = s7a2_inEdge m := by
  cases m with
  | inl i => exact ccpInEdge_vertex hn hP i
  | inr v => exact ccpInEdge_visit hn hP v

/-- Consecutive corners of a carrier: the outgoing edge of `c_j` is the incoming edge of `c_{j+1}`. -/
theorem s7a2_corner_edges (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    s7a2_outEdge (ccpCornerMark hn hP S q j) = s7a2_inEdge (ccpCornerMark hn hP S q (j + 1)) := by
  rw [← s7a2_outSlot_fst hn hP S _ (ccpCornerMark_isTrueCorner hn hP S q j), ← s7a2_inEdge_eq hn hP]
  exact ccpCornerPolygon_outEdge_eq_inEdge hn hP hS q j

omit [NeZero n] in
/-- The transversality needed by `s7a2_point_eq_out` on a generic polygon. -/
theorem s7a2_det_ne_zero_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (m : Mark P) :
    ∀ v : Visit P, m = Sum.inr v → det (edge P v.2.val) (edge P (visitTwin v).2.val) ≠ 0 :=
  fun v _ => crossing_edgeParameter_det_ne_zero hn hP.1 (s7a2_visit_isCrossing v)

/-- Consecutive corners of a carrier: the parameter increases along the common edge
(the positive coefficient of `ccpCornerPolygon_edge`). -/
theorem s7a2_corner_params_lt (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    s7a2_outParam P (ccpCornerMark hn hP S q j) <
      s7a2_inParam P (ccpCornerMark hn hP S q (j + 1)) := by
  obtain ⟨c, hc, he⟩ := ccpCornerPolygon_edge hn hP hS q j
  rw [s7a2_outSlot_fst hn hP S _ (ccpCornerMark_isTrueCorner hn hP S q j)] at he
  have hpt : edge (ccpCornerPolygon hn hP S q) j =
      s7a2_point P (ccpCornerMark hn hP S q (j + 1)) - s7a2_point P (ccpCornerMark hn hP S q j) := by
    show ccpCornerPolygon hn hP S q (j + 1) - ccpCornerPolygon hn hP S q j = _
    rw [ccpCornerPolygon_apply, ccpCornerPolygon_apply, s7a2_point_eq_evaluation hn hP,
      s7a2_point_eq_evaluation hn hP]
  rw [hpt, s7a2_point_sub P _ _ (s7a2_corner_edges hn hP hS q j) (s7a2_det_ne_zero_generic hn hP _)]
    at he
  have hne : edge P (s7a2_outEdge (ccpCornerMark hn hP S q j)) ≠ 0 := (g1 hn P hP.1).2.1 _
  have hzero : (s7a2_inParam P (ccpCornerMark hn hP S q (j + 1)) -
      s7a2_outParam P (ccpCornerMark hn hP S q j) - c) • edge P (s7a2_outEdge (ccpCornerMark hn hP S q j)) = 0 := by
    rw [sub_smul, he, sub_self]
  rcases smul_eq_zero.mp hzero with h0 | h0
  · linarith [sub_eq_zero.mp h0]
  · exact absurd h0 hne

omit [NeZero n] in
theorem s7a2_det_smul_smul (c d : ℝ) (u w : Plane) : det (c • u) (d • w) = (c * d) * det u w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

end S7A2Marks

section S7A2Germ

variable (hn : 3 ≤ n) (g : WallGerm n)

/-- lem:wall-sides (V) (`VertexLocalData`) at EVERY parameter `|u| < δ` of the germ, relative to the
centre — the interval form of `s7a_SideLocal` (which reads it at the two side times of one `t`). -/
def s7a2_IntervalLocal (M a : ZMod n) (r η δ : ℝ) : Prop :=
  ∀ u : g.Parameter, |u.val| < δ → VertexLocalData hn g.center (g.curve u) M a r η

/-- `vertex_sides` supplies the interval-local data below a radius `δ`. -/
theorem s7a2_exists_intervalLocal (M a : ZMod n) (h : g.VertexEdgeAt M a) :
    ∃ r η : ℝ, 0 < r ∧ r < 1 ∧ g.center M = edgePoint g.center a r ∧
      0 < η ∧ 4 * η < r ∧ 4 * η < 1 - r ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ s7a2_IntervalLocal hn g M a r η δ := by
  obtain ⟨-, -, -, -, r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, hδr, hloc⟩ := vertex_sides hn g h
  exact ⟨r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, hδr, hloc⟩

variable {M a : ZMod n} {r η δ : ℝ}

/-- The interval-local data restricts to the side-local data of any `t < δ`. -/
theorem s7a2_sideLocal (hloc : s7a2_IntervalLocal hn g M a r η δ) {t : g.SideParameter}
    (ht : t.val < δ) : s7a_SideLocal hn g M a r η t :=
  fun b => hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)

variable (h : g.VertexEdgeAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
  {u : g.Parameter} (hu : |u.val| < δ)

include hloc hu in
/-- Persistent crossings agree with the centre's at every `|u| < δ`. -/
theorem s7a2_crossing_iff (s : Finset (ZMod n)) (hs : ¬ ContactAffected M a s) :
    IsCrossing (g.curve u) s ↔ IsCrossing g.center s :=
  (hloc u hu).windows.1 s hs

include hloc hu in
/-- Chirotopes outside the centre's zero triple are nonzero at every `|u| < δ`. -/
theorem s7a2_chi_ne_zero (i j k : ZMod n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hnot : ({i, j, k} : Finset (ZMod n)) ∉ pointZeroTriples g.center) :
    chi (g.curve u) i j k ≠ 0 :=
  ((hloc u hu).chirotopes i j k hij hjk hik hnot).2

include h hloc hu in
/-- Every vertex turn is nonzero at every `|u| < δ` (the turn triple is never the contact support,
`contactSupport_ne_turnSupport`) — including the centre. -/
theorem s7a2_turn_ne_zero (i : ZMod n) : turn (g.curve u) i ≠ 0 := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have h1 : i - 1 ≠ i := prev_ne_self i
  have h2 : i ≠ i + 1 := (next_ne_self i).symm
  have h3 : i - 1 ≠ i + 1 := prev_ne_next hn i
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.2.1
  have hnot : ({i - 1, i, i + 1} : Finset (ZMod n)) ∉ pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    exact fun he => contactSupport_ne_turnSupport hn h.1 i he.symm
  exact s7a2_chi_ne_zero hn g hloc hu (i - 1) i (i + 1) h1 h2 h3 hnot

include h hloc hu in
theorem s7a2_turn_det_ne_zero (i : ZMod n) :
    det (edge (g.curve u) (i - 1)) (edge (g.curve u) i) ≠ 0 := by
  have := s7a2_turn_ne_zero hn g h hloc hu i
  rw [turn_det] at this
  exact sign_ne_zero.mp this

include h hloc hu in
/-- Every edge is nonzero at every `|u| < δ` — including the centre. -/
theorem s7a2_edge_ne_zero (i : ZMod n) : edge (g.curve u) i ≠ 0 := by
  intro h0
  apply s7a2_turn_det_ne_zero hn g h hloc hu i
  rw [h0]
  simp [det]

include h hloc hu in
/-- The two edges of a persistent crossing are transverse at every `|u| < δ`: off the centre by
genericity, at the centre by `contact_pair_data` (sm-4:495-500, "nonzero contact determinants"). -/
theorem s7a2_det_ne_zero {i j : ZMod n} (hc : IsCrossing g.center {i, j})
    (hnot : ¬ ContactAffected M a {i, j}) :
    det (edge (g.curve u) i) (edge (g.curve u) j) ≠ 0 := by
  rcases eq_or_ne u.val 0 with hu0 | hu0
  · have hu' : u = g.zeroParameter := Subtype.ext hu0
    subst hu'
    exact (contact_pair_data hn h.1 h.2.1 hc hnot).det_ne_zero
  · exact crossing_edgeParameter_det_ne_zero hn (g.generic_punctured u hu0).1
      ((s7a2_crossing_iff hn g hloc hu _ hnot).mpr hc)

include h hloc hu in
/-- The Cramer parameter of a persistent crossing is interior at every `|u| < δ` — including the
centre ("positive edge pieces"). -/
theorem s7a2_edgeParameter_interior {i j : ZMod n} (hc : IsCrossing g.center {i, j})
    (hnot : ¬ ContactAffected M a {i, j}) :
    0 < edgeParameter (g.curve u) i j ∧ edgeParameter (g.curve u) i j < 1 := by
  rcases eq_or_ne u.val 0 with hu0 | hu0
  · have hu' : u = g.zeroParameter := Subtype.ext hu0
    subst hu'
    exact (contact_pair_data hn h.1 h.2.1 hc hnot).parameter_interior
  · have hc' := (s7a2_crossing_iff hn g hloc hu _ hnot).mpr hc
    have hG := (g.generic_punctured u hu0).1
    rw [← crossingParameter_eq_edgeParameter hn hG hc']
    exact crossingParameter_interior hn hG _ i _

include h hloc hu in
/-- Two persistent crossings on one edge have distinct Cramer parameters at every `|u| < δ`:
off the centre `generic_edgeParameters_ne`, at the centre `contact_unaffected_parameters_ne`. -/
theorem s7a2_edgeParameters_ne {i j k : ZMod n} (hjk : j ≠ k)
    (hij : IsCrossing g.center {i, j}) (hnij : ¬ ContactAffected M a {i, j})
    (hik : IsCrossing g.center {i, k}) (hnik : ¬ ContactAffected M a {i, k}) :
    edgeParameter (g.curve u) i j ≠ edgeParameter (g.curve u) i k := by
  rcases eq_or_ne u.val 0 with hu0 | hu0
  · have hu' : u = g.zeroParameter := Subtype.ext hu0
    subst hu'
    exact contact_unaffected_parameters_ne hn h.1 h.2.1 h.2.2.1 hjk hij hnij hik hnik
  · exact generic_edgeParameters_ne hn (g.generic_punctured u hu0) hjk
      ((s7a2_crossing_iff hn g hloc hu _ hnij).mpr hij)
      ((s7a2_crossing_iff hn g hloc hu _ hnik).mpr hik)

include h hloc hu in
/-- The Cramer parameter of a persistent crossing is continuous in the germ parameter at every
`|u| < δ`: at the centre `continuousAt_contact_edgeParameter`, off it `continuousAt_edgeParameter`. -/
theorem s7a2_continuousAt_edgeParameter {i j : ZMod n} (hc : IsCrossing g.center {i, j})
    (hnot : ¬ ContactAffected M a {i, j}) :
    ContinuousAt (fun w : g.Parameter => edgeParameter (g.curve w) i j) u := by
  have hF : ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q i j) (g.curve u) := by
    rcases eq_or_ne u.val 0 with hu0 | hu0
    · have hu' : u = g.zeroParameter := Subtype.ext hu0
      subst hu'
      exact continuousAt_contact_edgeParameter hn h.1 h.2.1 hc hnot
    · exact continuousAt_edgeParameter hn (g.generic_punctured u hu0).1
        ((s7a2_crossing_iff hn g hloc hu _ hnot).mpr hc)
  exact ContinuousAt.comp (f := g.curve) (x := u) hF g.continuous_curve.continuousAt

omit [NeZero n] in
/-- **Sign constancy on `|u| ≤ t`.** A real function of the germ parameter, continuous and nonzero
on `|u| < δ` and positive at one side time of `t < δ`, is positive on all of `|u| ≤ t`. -/
theorem s7a2_pos_of_ne_zero {ψ : g.Parameter → ℝ} {δ : ℝ} {t : g.SideParameter} (ht : t.val < δ)
    (hcont : ∀ u : g.Parameter, |u.val| < δ → ContinuousAt ψ u)
    (hne : ∀ u : g.Parameter, |u.val| < δ → ψ u ≠ 0) (b : Bool) (hpos : 0 < ψ (g.sideTime b t)) :
    ∀ u : g.Parameter, |u.val| ≤ t.val → 0 < ψ u := by
  intro u hu
  have hpre : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let ι : Set.Icc (-t.val) t.val → g.Parameter := fun w =>
    ⟨w.1, by obtain ⟨h1, h2⟩ := w.2; have := t.property.2; constructor <;> linarith⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hιδ : ∀ w, |(ι w).val| < δ := fun w => lt_of_le_of_lt (abs_le.mpr w.2) ht
  have hsign : Continuous fun w => SignType.sign (ψ (ι w)) := by
    rw [continuous_iff_continuousAt]
    intro w
    have hψι : ContinuousAt (fun w => ψ (ι w)) w :=
      ContinuousAt.comp (f := ι) (x := w) (hcont _ (hιδ w)) hι.continuousAt
    exact ContinuousAt.comp (g := SignType.sign) (f := fun w => ψ (ι w)) (x := w)
      (continuousAt_sign_of_ne_zero (hne _ (hιδ w))) hψι
  have hconst := PreconnectedSpace.constant hpre hsign (x := ⟨u.val, abs_le.mp hu⟩)
    (y := ⟨(g.sideTime b t).val, abs_le.mp (le_of_eq (g.sideTime_val_abs b t))⟩)
  change SignType.sign (ψ u) = SignType.sign (ψ (g.sideTime b t)) at hconst
  exact sign_eq_one_iff.mp (hconst.trans (sign_eq_one_iff.mpr hpos))

end S7A2Germ

/-! #### The corner-polygon family of a persistent carrier through the wall -/

section S7A2Family

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}
  (h : g.VertexEdgeAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
  {t : g.SideParameter} (ht : t.val < δ) (b : Bool)
  (S : Finset (Crossing (g.curve (g.sideTime b t))))
  (hS : IsDecomposition hn (s7a_sideGeneric g b) S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val)
  (q : Component hn (s7a_sideGeneric g b) S)

/-- **The corner-polygon family** of the carrier `q` of side `b` through the wall: at the parameter
`u` the `j`-th vertex is the `j`-th corner mark of `q` READ ON `g.curve u` (vertex `i ↦ g.curve u i`,
selected visit `↦ edgePoint (g.curve u) e (edgeParameter (g.curve u) e f)`); CSilent's
`silentCornerFamily` for the persistent transport. -/
def s7a2_cornerFamily (u : g.Parameter) : LabelledTuple (ccpCornerCount hn (s7a_sideGeneric g b) S q) :=
  fun j => s7a2_point (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q j)

/-- At the side time of its own side the family IS the corner polygon of `q`. -/
theorem s7a2_cornerFamily_side_self :
    s7a2_cornerFamily hn g b S q (g.sideTime b t) = ccpCornerPolygon hn (s7a_sideGeneric g b) S q := by
  funext j
  exact (s7a2_point_eq_evaluation hn (s7a_sideGeneric g b) _).symm

include hloc ht hSp in
/-- The crossing of a selected visit of a persistent support is a persistent crossing of the centre. -/
theorem s7a2_corner_crossing (v : Visit (g.curve (g.sideTime b t))) (hv : v.1 ∈ S) :
    IsCrossing g.center {v.2.val, (visitTwin v).2.val} ∧
      ¬ ContactAffected M a {v.2.val, (visitTwin v).2.val} := by
  have hnot : ¬ ContactAffected M a {v.2.val, (visitTwin v).2.val} := by
    rw [← visit_crossing_val_eq_pair v]
    exact hSp v.1 hv
  refine ⟨?_, hnot⟩
  exact (s7a2_crossing_iff hn g hloc (u := g.sideTime b t)
    (by rw [g.sideTime_val_abs]; exact ht) _ hnot).mp (s7a2_visit_isCrossing v)

include hloc ht hSp in
theorem s7a2_corner_crossing' (v : Visit (g.curve (g.sideTime b t))) (hv : v.1 ∈ S) :
    IsCrossing g.center {(visitTwin v).2.val, v.2.val} ∧
      ¬ ContactAffected M a {(visitTwin v).2.val, v.2.val} := by
  rw [Finset.pair_comm]
  exact s7a2_corner_crossing hn g hloc ht b S hSp v hv

include h hloc ht hSp in
/-- Transversality at a true corner, at every `|u| < δ` (the `hd` of `s7a2_point_sub`). -/
theorem s7a2_corner_hd (u : g.Parameter) (hu : |u.val| < δ) (m : Mark (g.curve (g.sideTime b t)))
    (hm : IsTrueCorner S m) :
    ∀ v, m = Sum.inr v → det (edge (g.curve u) v.2.val) (edge (g.curve u) (visitTwin v).2.val) ≠ 0 := by
  rintro v rfl
  obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v hm
  exact s7a2_det_ne_zero hn g h hloc hu hc hnot

include h hloc ht hS hSp in
/-- **The edges of the family** are the parameter differences times the original edge directions
read on `g.curve u`, at every `|u| < δ`. -/
theorem s7a2_cornerFamily_edge (u : g.Parameter) (hu : |u.val| < δ)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) S q)) :
    edge (s7a2_cornerFamily hn g b S q u) j =
      (s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1)) -
        s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q j)) •
        edge (g.curve u) (s7a2_outEdge (ccpCornerMark hn (s7a_sideGeneric g b) S q j)) := by
  show s7a2_point (g.curve u) _ - s7a2_point (g.curve u) _ = _
  exact s7a2_point_sub (g.curve u) _ _ (s7a2_corner_edges hn _ hS q j)
    (s7a2_corner_hd hn g h hloc ht b S hSp u hu _ (ccpCornerMark_isTrueCorner hn _ S q j))

include h hloc ht hS hSp in
/-- **The parameter difference of consecutive corners never vanishes** on `|u| < δ` — including the
centre: vertex–vertex `1`, vertex–visit and visit–vertex by interiority of the Cramer parameter,
visit–visit by distinctness of the Cramer parameters of two persistent crossings on one edge (their
twin edges differ because the parameters are ordered on side `b`). -/
theorem s7a2_psi_ne_zero (u : g.Parameter) (hu : |u.val| < δ)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) S q)) :
    s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1)) -
      s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q j) ≠ 0 := by
  have hε := s7a2_corner_edges hn (s7a_sideGeneric g b) hS q j
  have hlt := s7a2_corner_params_lt hn (s7a_sideGeneric g b) hS q j
  have hm := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j
  have hm' := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q (j + 1)
  rcases hmj : ccpCornerMark hn (s7a_sideGeneric g b) S q j with i | v <;>
    rcases hmj' : ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1) with i' | v' <;>
    rw [hmj, hmj'] at hε hlt <;> rw [hmj] at hm <;> rw [hmj'] at hm'
  · simp
  · simp only [s7a2_inParam_inr, s7a2_outParam_inl, sub_zero]
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v' hm'
    exact (s7a2_edgeParameter_interior hn g h hloc hu hc hnot).1.ne'
  · simp only [s7a2_inParam_inl, s7a2_outParam_inr]
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing' hn g hloc ht b S hSp v hm
    exact (sub_pos.mpr (s7a2_edgeParameter_interior hn g h hloc hu hc hnot).2).ne'
  · simp only [s7a2_inParam_inr, s7a2_outParam_inr, s7a2_outEdge_inr, s7a2_inEdge_inr] at hε hlt ⊢
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing' hn g hloc ht b S hSp v hm
    obtain ⟨hc', hnot'⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v' hm'
    rw [← hε] at hc' hnot' hlt ⊢
    have hne : (visitTwin v').2.val ≠ v.2.val := by
      intro heq
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    exact sub_ne_zero.mpr (s7a2_edgeParameters_ne hn g h hloc hu hne hc' hnot' hc hnot)

include h hloc ht hSp in
/-- The parameter difference of consecutive corners is continuous in the germ parameter on `|u| < δ`. -/
theorem s7a2_psi_continuousAt (u : g.Parameter) (hu : |u.val| < δ)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) S q)) :
    ContinuousAt (fun w : g.Parameter =>
      s7a2_inParam (g.curve w) (ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1)) -
        s7a2_outParam (g.curve w) (ccpCornerMark hn (s7a_sideGeneric g b) S q j)) u := by
  have hm := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j
  have hm' := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q (j + 1)
  apply ContinuousAt.sub
  · rcases hmj' : ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1) with i' | v'
    · simp only [s7a2_inParam_inl]
      exact continuousAt_const
    · simp only [s7a2_inParam_inr]
      rw [hmj'] at hm'
      obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v' hm'
      exact s7a2_continuousAt_edgeParameter hn g h hloc hu hc hnot
  · rcases hmj : ccpCornerMark hn (s7a_sideGeneric g b) S q j with i | v
    · simp only [s7a2_outParam_inl]
      exact continuousAt_const
    · simp only [s7a2_outParam_inr]
      rw [hmj] at hm
      obtain ⟨hc, hnot⟩ := s7a2_corner_crossing' hn g hloc ht b S hSp v hm
      exact s7a2_continuousAt_edgeParameter hn g h hloc hu hc hnot

include h hloc ht hS hSp in
/-- **Positive edge pieces on `|u| ≤ t`** (sm-4:495-500): the parameter difference of consecutive
corners is positive on side `b` (`ccpCornerPolygon_edge`), continuous and nonzero on `|u| < δ`, hence
positive on all of `|u| ≤ t` — including the centre. -/
theorem s7a2_psi_pos (u : g.Parameter) (hu : |u.val| ≤ t.val)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) S q)) :
    0 < s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1)) -
      s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q j) :=
  s7a2_pos_of_ne_zero g ht (fun w hw => s7a2_psi_continuousAt hn g h hloc ht b S hSp q w hw j)
    (fun w hw => s7a2_psi_ne_zero hn g h hloc ht b S hS hSp q w hw j) b
    (sub_pos.mpr (s7a2_corner_params_lt hn (s7a_sideGeneric g b) hS q j)) u hu

include h hloc ht hSp in
/-- The incoming and outgoing original directions at a true corner are transverse at every `|u| < δ`
(vertex: the turn; selected visit: the crossing determinant). -/
theorem s7a2_corner_det_ne_zero (u : g.Parameter) (hu : |u.val| < δ)
    (m : Mark (g.curve (g.sideTime b t))) (hm : IsTrueCorner S m) :
    det (edge (g.curve u) (s7a2_inEdge m)) (edge (g.curve u) (s7a2_outEdge m)) ≠ 0 := by
  cases m with
  | inl i => exact s7a2_turn_det_ne_zero hn g h hloc hu i
  | inr v =>
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v hm
    exact s7a2_det_ne_zero hn g h hloc hu hc hnot

include h hloc ht hS hSp in
/-- **The family is regular on `|u| ≤ t`, including at the wall**: nonzero edges (positive pieces of
nonzero original edges) and nonzero corner determinants (positive multiples of the transverse
original directions at each true corner). -/
theorem s7a2_cornerFamily_regular (u : g.Parameter) (hu : |u.val| ≤ t.val) :
    Regular (s7a2_cornerFamily hn g b S q u) := by
  have hu' : |u.val| < δ := lt_of_le_of_lt hu ht
  rw [regular_iff_edges]
  intro j
  have hψ := s7a2_psi_pos hn g h hloc ht b S hS hSp q u hu j
  have hψ' := s7a2_psi_pos hn g h hloc ht b S hS hSp q u hu (j - 1)
  rw [sub_add_cancel] at hψ'
  have he := s7a2_cornerFamily_edge hn g h hloc ht b S hS hSp q u hu' j
  have he' := s7a2_cornerFamily_edge hn g h hloc ht b S hS hSp q u hu' (j - 1)
  rw [sub_add_cancel] at he'
  have hε' := s7a2_corner_edges hn (s7a_sideGeneric g b) hS q (j - 1)
  rw [sub_add_cancel] at hε'
  have hdet : det (edge (s7a2_cornerFamily hn g b S q u) (j - 1))
      (edge (s7a2_cornerFamily hn g b S q u) j) ≠ 0 := by
    rw [he, he', s7a2_det_smul_smul, hε']
    exact mul_ne_zero (mul_ne_zero hψ'.ne' hψ.ne')
      (s7a2_corner_det_ne_zero hn g h hloc ht b S hSp u hu' _
        (ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j))
  refine ⟨?_, ?_⟩
  · rw [he]
    exact smul_ne_zero hψ.ne' (s7a2_edge_ne_zero hn g h hloc hu' _)
  · rintro ⟨r, _, hr⟩
    apply hdet
    rw [hr]
    exact det_smul_self _ r

include h hloc ht hSp in
/-- **The family is continuous on `|u| ≤ t`**: vertices by `g.continuous_curve`, selected visits by
the continuity of the Cramer parameter of a persistent crossing (`continuousAt_contact_edgeParameter`
at the centre, `continuousAt_edgeParameter` off it). -/
theorem s7a2_cornerFamily_continuousOn :
    ContinuousOn (s7a2_cornerFamily hn g b S q) {u : g.Parameter | |u.val| ≤ t.val} := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  have hu' : |u.val| < δ := lt_of_le_of_lt hu ht
  apply continuousAt_pi.mpr
  intro j
  show ContinuousAt (fun w : g.Parameter =>
    s7a2_point (g.curve w) (ccpCornerMark hn (s7a_sideGeneric g b) S q j)) u
  have hm := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j
  rcases hmj : ccpCornerMark hn (s7a_sideGeneric g b) S q j with i | v
  · simp only [s7a2_point_inl]
    exact ((continuous_apply i).comp g.continuous_curve).continuousAt
  · simp only [s7a2_point_inr]
    rw [hmj] at hm
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v hm
    show ContinuousAt (fun w : g.Parameter => (g.curve w) v.2.val +
      edgeParameter (g.curve w) v.2.val (visitTwin v).2.val • edge (g.curve w) v.2.val) u
    exact (((continuous_apply _).comp g.continuous_curve).continuousAt).add
      ((s7a2_continuousAt_edgeParameter hn g h hloc hu' hc hnot).smul
        ((continuous_edge _).comp g.continuous_curve).continuousAt)

include h hloc ht hS hSp in
/-- **eq. s7c:full-rotation for the persistent carrier** (lem:rot (ii), `rotationNumber_family_constant`
on `[−t, t]`): the rotation number of the family is constant on `|u| ≤ t`. -/
theorem s7a2_cornerFamily_rotation (u : g.Parameter) (hu : |u.val| ≤ t.val) :
    rotationNumber (s7a2_cornerFamily hn g b S q u) =
      rotationNumber (s7a2_cornerFamily hn g b S q (g.sideTime b t)) := by
  have hpre : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let ι : Set.Icc (-t.val) t.val → g.Parameter := fun w =>
    ⟨w.1, by obtain ⟨h1, h2⟩ := w.2; have := t.property.2; constructor <;> linarith⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hmem : ∀ w, |(ι w).val| ≤ t.val := fun w => abs_le.mpr w.2
  have hF : Continuous (fun w => s7a2_cornerFamily hn g b S q (ι w)) :=
    (s7a2_cornerFamily_continuousOn hn g h hloc ht b S hSp q).comp_continuous hι hmem
  exact rotationNumber_family_constant hF
    (fun w => s7a2_cornerFamily_regular hn g h hloc ht b S hS hSp q (ι w) (hmem w))
    ⟨u.val, abs_le.mp hu⟩ ⟨(g.sideTime b t).val, abs_le.mp (le_of_eq (g.sideTime_val_abs b t))⟩

end S7A2Family

/-! #### The rotation equality `hr` -/

section S7A2Assembly

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}

omit [NeZero n] in
/-- The point of a persistent mark read on `Q'` is unchanged by the mark map `s7a_markMap`: the
vertex is fixed, a transported visit keeps its edge and its twin's edge (`s7a_visit_twin`). -/
theorem s7a2_point_markMap {P Q : LabelledTuple n}
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (Q' : LabelledTuple n) (m : Mark P) (hm : s7a_Persistent M a m) :
    s7a2_point Q' (s7a_markMap hs m) = s7a2_point Q' m := by
  cases m with
  | inl i => rfl
  | inr v =>
    rw [s7a_markMap_inr hs v hm, s7a2_point_inr, s7a2_point_inr, ← s7a_visit_twin hs v hm]
    rfl

variable (h : g.VertexEdgeAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
  {t : g.SideParameter} (ht : t.val < δ) (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool)
  (S : Finset (Crossing (g.curve (g.sideTime b t))))
  (S' : Finset (Crossing (g.curve (g.sideTime b' t))))
  (hSS' : ∀ (v : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val),
    (s7a_visit (s7a_side_hs hn g hL b b') v hv).1 ∈ S' ↔ v.1 ∈ S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)
  (hS : IsDecomposition hn (s7a_sideGeneric g b) S) (q : Component hn (s7a_sideGeneric g b) S)

include hL hSS' hSp hSp' in
/-- The equal corner counts of corresponding carriers, stated on `s7a_sideComponentEquiv`
(`s7a_ccpCornerCount_eq`). -/
theorem s7a2_sideCornerCount_eq :
    ccpCornerCount hn (s7a_sideGeneric g b) S q =
      ccpCornerCount hn (s7a_sideGeneric g b') S'
        (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q) :=
  (s7a_ccpCornerCount_eq hn (s7a_sideGeneric g b) (s7a_sideGeneric g b') (s7a_side_hs hn g hL b b')
    (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' q).symm

include hL hSS' hSp hSp' in
/-- At the side time of the OTHER side `b'` the family is the corner polygon of the corresponding
carrier `s7a_sideComponentEquiv … q` of `S'`, recast along the equal corner counts
(`s7a_ccpCornerMark_map`: the corner marks correspond index by index). -/
theorem s7a2_cornerFamily_side_other :
    s7a2_cornerFamily hn g b S q (g.sideTime b' t) =
      recastTuple (s7a2_sideCornerCount_eq hn g hL b b' S S' hSS' hSp hSp' q)
        (ccpCornerPolygon hn (s7a_sideGeneric g b') S'
          (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q)) := by
  funext j
  have key := s7a_ccpCornerMark_map hn (s7a_sideGeneric g b) (s7a_sideGeneric g b')
    (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' q j
  show s7a2_point (g.curve (g.sideTime b' t)) (ccpCornerMark hn (s7a_sideGeneric g b) S q j) =
    traversalEvaluation (g.curve (g.sideTime b' t)) (markPosition hn (s7a_sideGeneric g b').1
      (ccpCornerMark hn (s7a_sideGeneric g b') S'
        (s7a_componentEquiv hn (s7a_sideGeneric g b) (s7a_sideGeneric g b') (s7a_side_hs hn g hL b b')
          (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' q)
        (Equiv.cast (congrArg ZMod (s7a_ccpCornerCount_eq hn (s7a_sideGeneric g b) (s7a_sideGeneric g b')
          (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' q).symm) j)))
  rw [key, s7a2_point_eq_evaluation hn (s7a_sideGeneric g b')]
  exact (s7a2_point_markMap (s7a_side_hs hn g hL b b') _ _
    (s7a_isTrueCorner_persistent S hSp _
      (ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j))).symm

include h hloc ht hL hSS' hSp hSp' hS in
/-- **The rotation equality `hr`** (sm-4:493-503, eq. s7c:full-rotation for the persistent carriers):
lem:rot (ii) along `s7a2_cornerFamily`, continuous and regular on `|u| ≤ t` INCLUDING the wall —
corresponding carriers on the two sides of a simple vertex–edge wall have equal `carrierRotation`.
This is the hypothesis `hr` of `s7d_cornerCoefficient_eq_of_strictMono` / `_cut` for the spectator
carriers, with `hP := s7a_sideGeneric g b`, `hQ := s7a_sideGeneric g b'` (definitionally
`(g.sideTuple b t).property`), `q' := s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q`.
Inputs: `hloc`/`ht` from `s7a2_exists_intervalLocal` (or `vertex_sides`), `hL` any proof of the
side-local data (e.g. `s7a2_sideLocal hn g hloc ht`; proof-irrelevant). -/
theorem s7a2_carrierRotation_eq :
    carrierRotation hn (s7a_sideGeneric g b) S q =
      carrierRotation hn (s7a_sideGeneric g b') S'
        (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q) := by
  have h1 := s7a2_cornerFamily_side_self hn g b S q
  have h2 := s7a2_cornerFamily_side_other hn g hL b b' S S' hSS' hSp hSp' q
  have h3 := s7a2_cornerFamily_rotation hn g h hloc ht b S hS hSp q (g.sideTime b' t)
    (le_of_eq (g.sideTime_val_abs b' t))
  rw [h1, h2, rotationNumber_recastTuple] at h3
  exact h3.symm

include h hloc ht hS hSp in
/-- The family is regular at the centre `u = 0` (the value `rot(L*)` of U110-I is defined). -/
theorem s7a2_cornerFamily_regular_centre :
    Regular (s7a2_cornerFamily hn g b S q g.zeroParameter) :=
  s7a2_cornerFamily_regular hn g h hloc ht b S hS hSp q g.zeroParameter
    (by show |(0 : ℝ)| ≤ t.val; rw [abs_zero]; exact t.property.1.le)

include h hloc ht hS hSp in
/-- The rotation number of the centre polygon `L*` of the family is the carrier rotation of `q`
(`rot(L*) = rot(L_L) = rot(L_H)`, sm-4:501-503). -/
theorem s7a2_rotation_centre :
    rotationNumber (s7a2_cornerFamily hn g b S q g.zeroParameter) =
      carrierRotation hn (s7a_sideGeneric g b) S q := by
  rw [carrierRotation, ← s7a2_cornerFamily_side_self hn g b S q]
  exact s7a2_cornerFamily_rotation hn g h hloc ht b S hS hSp q g.zeroParameter
    (by show |(0 : ℝ)| ≤ t.val; rw [abs_zero]; exact t.property.1.le)

end S7A2Assembly

/-! ### Unit S7E (leaf unit U110-E `s7_sliding_law_at`, prefix `s7e_`; PLAN_FINAL §3.3 sliding
(1)-(4), §4 row U110-E).  Probe section. -/

section S7EAlgebra

/-- The summand of lem:C-X1 as a total function of the support (`0` off `Ind(G_P)`): CS3's
`stateTerm`, re-declared here because `SM.CS3` is not among the frozen imports. -/
def s7e_term (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P)) : ℤ :=
  if h : IsDecomposition hn hP S then wind hn hP S * cornerProduct hn hP S h else 0

theorem s7e_term_of_not (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (h : ¬ IsDecomposition hn hP S) : s7e_term hn hP S = 0 :=
  dite_eq_right h

theorem s7e_term_of_decomposition (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (h : IsDecomposition hn hP S) :
    s7e_term hn hP S = wind hn hP S * cornerProduct hn hP S h :=
  dite_eq_left h

/-- lem:C-X1 as a sum over ALL supports (`C_X1.selector_form`, completion by zeros). -/
theorem s7e_cornerStateSum_eq_sum_term (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    cornerStateSum hn hP = ∑ S : Finset (Crossing P), s7e_term hn hP S := by
  rw [C_X1.selector_form]
  have h1 : (∑ S ∈ (independentSupports hn hP).attach,
      wind hn hP S.1 * cornerProduct hn hP S.1 S.2) =
      ∑ S ∈ (independentSupports hn hP).attach, s7e_term hn hP S.1 :=
    Finset.sum_congr rfl fun S _ => (s7e_term_of_decomposition hn hP S.2).symm
  rw [h1, Finset.sum_attach]
  exact Finset.sum_subset (Finset.subset_univ _) fun S _ hS => s7e_term_of_not hn hP hS

omit [NeZero n] in
/-- A finite sum split by a predicate into the two subtype sums (`¬P` first). -/
theorem s7e_sum_split {ι : Type*} [Fintype ι] (F : ι → ℤ) (P : ι → Prop) :
    ∑ S, F S = ∑ S : {S // ¬ P S}, F S.1 + ∑ S : {S // P S}, F S.1 := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype P F, add_comm]

omit [NeZero n] in
/-- Terms vanishing off `D` may be restricted to `D`. -/
theorem s7e_sum_full_eq_of_zero {ι : Type*} [Fintype ι] (F : ι → ℤ) (D : ι → Prop)
    (hz : ∀ S, ¬ D S → F S = 0) : ∑ S : {S // D S}, F S.1 = ∑ S, F S := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype D F]
  have h0 : ∑ S : {S // ¬ D S}, F S.1 = 0 := Finset.sum_eq_zero fun S _ => hz S.1 S.2
  rw [h0, add_zero]

omit [NeZero n] in
/-- Inside the sector `P`, terms vanishing off `D` may be restricted to `D ∧ P`. -/
theorem s7e_sum_subtype_eq_of_zero {ι : Type*} [Fintype ι] (F : ι → ℤ) (P D : ι → Prop)
    (hz : ∀ S, ¬ D S → F S = 0) :
    ∑ S : {S // P S}, F S.1 = ∑ S : {S // D S ∧ P S}, F S.1 := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun S : {S // P S} => D S.1) (fun S => F S.1)]
  have h0 : ∑ S : {S : {S // P S} // ¬ D S.1}, F S.1.1 = 0 :=
    Finset.sum_eq_zero fun S _ => hz _ S.2
  rw [h0, add_zero]
  exact Fintype.sum_equiv ((Equiv.subtypeSubtypeEquivSubtypeInter P D).trans
    (Equiv.subtypeEquivRight fun S => and_comm)) _ _ (fun S => rfl)

omit [NeZero n] in
/-- **The algebra of the sliding law** (PLAN §3.3 sliding (4): `Finset.sum_bij` + distributivity).
Two state sums `Σ f`, `Σ f'` (indexed by the supports of `P₋`, `P₊`) are compared through two sectors:
the SPECTATOR sector (`¬p`: supports avoiding the contact crossing) is matched term by term by `e₀`;
the CONTACT sector (`p`) is matched, on the decompositions `D`, `D'`, with the product `Ind(λ₁) × Ind(λ₂)`
by `e`, `e'`, where the termwise difference is `s · g₁ · g₂` (eq. s7c:sliding-selector-difference times
the equal coefficient products).  Terms vanish off the decompositions (`hz`, `hz'`, `hz₁`, `hz₂`).  Then
`Σ f' − Σ f = s (Σ g₁)(Σ g₂)`. -/
theorem s7e_law_of_sectors {α β γ₁ γ₂ : Type*} [Fintype α] [Fintype β] [Fintype γ₁] [Fintype γ₂]
    (f : α → ℤ) (f' : β → ℤ) (g₁ : γ₁ → ℤ) (g₂ : γ₂ → ℤ)
    (p : α → Prop) (p' : β → Prop) (D : α → Prop) (D' : β → Prop) (D₁ : γ₁ → Prop) (D₂ : γ₂ → Prop)
    (e₀ : {S : α // ¬ p S} ≃ {S : β // ¬ p' S}) (he₀ : ∀ S, f' (e₀ S).1 = f S.1)
    (hz : ∀ S, ¬ D S → f S = 0) (hz' : ∀ S, ¬ D' S → f' S = 0)
    (hz₁ : ∀ S, ¬ D₁ S → g₁ S = 0) (hz₂ : ∀ S, ¬ D₂ S → g₂ S = 0)
    (e : {S : α // D S ∧ p S} ≃ {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂})
    (e' : {S : β // D' S ∧ p' S} ≃ {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}) (s : ℤ)
    (hc : ∀ q, f' (e'.symm q).1 - f (e.symm q).1 = s * (g₁ q.1.1 * g₂ q.2.1)) :
    ∑ S, f' S - ∑ S, f S = s * ((∑ S₁, g₁ S₁) * (∑ S₂, g₂ S₂)) := by
  classical
  rw [s7e_sum_split f' p', s7e_sum_split f p]
  have hpers : ∑ S : {S // ¬ p' S}, f' S.1 = ∑ S : {S // ¬ p S}, f S.1 :=
    (Fintype.sum_equiv e₀ _ _ (fun S => (he₀ S).symm)).symm
  rw [hpers, s7e_sum_subtype_eq_of_zero f' p' D' hz', s7e_sum_subtype_eq_of_zero f p D hz]
  have h' : ∑ S : {S // D' S ∧ p' S}, f' S.1 =
      ∑ q : {S₁ // D₁ S₁} × {S₂ // D₂ S₂}, f' (e'.symm q).1 :=
    Fintype.sum_equiv e' _ _ (fun S => by rw [Equiv.symm_apply_apply])
  have h : ∑ S : {S // D S ∧ p S}, f S.1 =
      ∑ q : {S₁ // D₁ S₁} × {S₂ // D₂ S₂}, f (e.symm q).1 :=
    Fintype.sum_equiv e _ _ (fun S => by rw [Equiv.symm_apply_apply])
  rw [h', h]
  have hdiff : (∑ S : {S // ¬ p S}, f S.1 + ∑ q, f' (e'.symm q).1) -
      (∑ S : {S // ¬ p S}, f S.1 + ∑ q, f (e.symm q).1) =
      ∑ q : {S₁ // D₁ S₁} × {S₂ // D₂ S₂}, (f' (e'.symm q).1 - f (e.symm q).1) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hdiff]
  simp_rw [hc]
  rw [← Finset.mul_sum, Fintype.sum_prod_type, ← s7e_sum_full_eq_of_zero g₁ D₁ hz₁,
    ← s7e_sum_full_eq_of_zero g₂ D₂ hz₂, Finset.sum_mul_sum]

end S7EAlgebra

section S7ESliding

variable {g : WallGerm n} {M a : ZMod n}

/-- The leg of the contact crossing on the NEGATIVE side (`P₋ = g.curve (g.sideTime false t)`):
`true` if `P₋` carries the crossing `{a, M}`, `false` if it carries `{a, M − 1}` (constant along the
side, `s7e_pattern`).  The positive side carries the other one (`SlidingCrossingPattern`). -/
noncomputable def s7e_leg (g : WallGerm n) (M a : ZMod n) : Bool :=
  decide (IsCrossing (g.sideTuple false g.sideBase).val {a, M})

/-- The sliding crossing pattern (lem:wall-sides (V), `vertex_sides`, `SlidingCrossingPattern`) read
with the leg `s7e_leg`: `P₋(t)` has exactly the contact crossing `{a, contactLeg (s7e_leg) M}` and
`P₊(t)` exactly `{a, contactLeg (!s7e_leg) M}`, at EVERY side parameter `t`. -/
theorem s7e_pattern (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    IsCrossing (g.curve (g.sideTime false t)) {a, contactLeg (s7e_leg g M a) M} ∧
    ¬ IsCrossing (g.curve (g.sideTime false t)) {a, contactLeg (!s7e_leg g M a) M} ∧
    IsCrossing (g.curve (g.sideTime true t)) {a, contactLeg (!s7e_leg g M a) M} ∧
    ¬ IsCrossing (g.curve (g.sideTime true t)) {a, contactLeg (s7e_leg g M a) M} := by
  have hpat : SlidingCrossingPattern (g.curve (g.sideTime true t)) (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 t t).2.2.1 h.2
  have hbase : SlidingCrossingPattern (g.curve (g.sideTime true t))
      (g.curve (g.sideTime false g.sideBase)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 t g.sideBase).2.2.1 h.2
  unfold s7e_leg
  by_cases hM : IsCrossing (g.sideTuple false g.sideBase).val {a, M}
  · rw [decide_eq_true hM]
    simp only [Bool.not_true, contactLeg, ↓reduceIte, Bool.false_eq_true]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h4, h3, h1, h2⟩
    · exfalso
      rcases hbase with ⟨b1, _, _, _⟩ | ⟨_, _, _, b4⟩
      · exact h1 b1
      · exact b4 hM
  · rw [decide_eq_false hM]
    simp only [Bool.not_false, contactLeg, ↓reduceIte, Bool.false_eq_true]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, _, _, b4⟩ | ⟨b1, _, _, _⟩
      · exact hM b4
      · exact b1 h1
    · exact ⟨h3, h4, h2, h1⟩


/-- The contact crossing `x₋` of `P₋(t)`. -/
noncomputable def s7e_xm (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime false t)) :=
  ⟨{a, contactLeg (s7e_leg g M a) M}, (s7e_pattern hn h t).1⟩

/-- The contact crossing `x₊` of `P₊(t)`. -/
noncomputable def s7e_xp (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime true t)) :=
  ⟨{a, contactLeg (!s7e_leg g M a) M}, (s7e_pattern hn h t).2.2.1⟩

theorem s7e_xm_val (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    (s7e_xm hn h t).val = {a, contactLeg (s7e_leg g M a) M} := rfl

theorem s7e_xp_val (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    (s7e_xp hn h t).val = {a, contactLeg (!s7e_leg g M a) M} := rfl

theorem s7e_xm_affected (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    ContactAffected M a (s7e_xm hn h t).val :=
  (contactAffected_iff_leg _).mpr ⟨_, rfl⟩

theorem s7e_xp_affected (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    ContactAffected M a (s7e_xp hn h t).val :=
  (contactAffected_iff_leg _).mpr ⟨_, rfl⟩

/-- `x₋` is the ONLY contact-affected crossing of `P₋(t)`. -/
theorem s7e_eq_xm_of_affected (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter)
    (y : Crossing (g.curve (g.sideTime false t))) (hy : ContactAffected M a y.val) :
    y = s7e_xm hn h t := by
  obtain ⟨f, hf⟩ := (contactAffected_iff_leg _).mp hy
  apply Subtype.ext
  rw [hf, s7e_xm_val]
  by_cases hfl : f = s7e_leg g M a
  · rw [hfl]
  · exfalso
    have hf' : f = !s7e_leg g M a := by
      cases f <;> cases hl : s7e_leg g M a <;> simp_all
    rw [hf'] at hf
    exact (s7e_pattern hn h t).2.1 (hf ▸ y.property)

/-- `x₊` is the ONLY contact-affected crossing of `P₊(t)`. -/
theorem s7e_eq_xp_of_affected (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter)
    (y : Crossing (g.curve (g.sideTime true t))) (hy : ContactAffected M a y.val) :
    y = s7e_xp hn h t := by
  obtain ⟨f, hf⟩ := (contactAffected_iff_leg _).mp hy
  apply Subtype.ext
  rw [hf, s7e_xp_val]
  by_cases hfl : f = !s7e_leg g M a
  · rw [hfl]
  · exfalso
    have hf' : f = s7e_leg g M a := by
      cases f <;> cases hl : s7e_leg g M a <;> simp_all
    rw [hf'] at hf
    exact (s7e_pattern hn h t).2.2.2 (hf ▸ y.property)

/-- The CONTACT sector at the side parameter `t` (PLAN §3.3 sliding (2)-(3)), as the algebra
`s7e_law_of_sectors` consumes it: the decompositions of `P₋(t)` through `x₋` and those of `P₊(t)`
through `x₊` are both in bijection with `Ind(λ₁) × Ind(λ₂)` (eq. s7c:sliding-bijection,
`s7b_slidingDecompositionEquiv` on each side), and along the two bijections the difference of the
selector-form terms is `s · term(S₁) · term(S₂)` (eq. s7c:sliding-selector-difference with equal
coefficient products eq. s7c:sliding-coefficients). -/
def s7e_ContactSector (hn : 3 ≤ n) (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) : Prop :=
  ∃ (e : {S : Finset (Crossing (g.curve (g.sideTime false t))) //
        IsDecomposition hn (s7a_sideGeneric g false) S ∧ s7e_xm hn h t ∈ S} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂})
    (e' : {S : Finset (Crossing (g.curve (g.sideTime true t))) //
        IsDecomposition hn (s7a_sideGeneric g true) S ∧ s7e_xp hn h t ∈ S} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
    ∀ q, s7e_term hn (s7a_sideGeneric g true) (e'.symm q).1 -
        s7e_term hn (s7a_sideGeneric g false) (e.symm q).1 =
      (g.contactSign M a : ℤ) *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ q.1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ q.2.1)

/-- The SPECTATOR sector at `t` (PLAN §3.3 sliding (1)): a bijection between the supports of `P₋(t)`
avoiding `x₋` and the supports of `P₊(t)` avoiding `x₊` preserving the selector-form term. -/
def s7e_SpectatorSector (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) : Prop :=
  ∃ e₀ : {S : Finset (Crossing (g.curve (g.sideTime false t))) // s7e_xm hn h t ∉ S} ≃
      {S : Finset (Crossing (g.curve (g.sideTime true t))) // s7e_xp hn h t ∉ S},
    ∀ S, s7e_term hn (s7a_sideGeneric g true) (e₀ S).1 = s7e_term hn (s7a_sideGeneric g false) S.1

/-- The sliding law at one side parameter from its two sectors. -/
theorem s7e_law_at_of_sectors (hn : 3 ≤ n) (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter)
    (hsp : s7e_SpectatorSector hn h t) (hct : s7e_ContactSector hn h h₁ h₂ t) :
    cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨e₀, he₀⟩ := hsp
  obtain ⟨e, e', hc⟩ := hct
  rw [s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term,
    s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term]
  exact s7e_law_of_sectors (s7e_term hn (s7a_sideGeneric g false)) (s7e_term hn (s7a_sideGeneric g true))
    (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
    (fun S => s7e_xm hn h t ∈ S) (fun S => s7e_xp hn h t ∈ S)
    (IsDecomposition hn (s7a_sideGeneric g false)) (IsDecomposition hn (s7a_sideGeneric g true))
    (IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
    e₀ he₀ (fun S hS => s7e_term_of_not _ _ hS) (fun S hS => s7e_term_of_not _ _ hS)
    (fun S hS => s7e_term_of_not _ _ hS) (fun S hS => s7e_term_of_not _ _ hS) e e' _ hc

/-- The leaf from the two sectors, each available below a radius. -/
theorem s7e_sliding_law_at_of_sectors (hn : 3 ≤ n) (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a))
    (hsp : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_SpectatorSector hn h t)
    (hct : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_ContactSector hn h h₁ h₂ t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨δ₁, hδ₁, hsp⟩ := hsp
  obtain ⟨δ₂, hδ₂, hct⟩ := hct
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  exact s7e_law_at_of_sectors hn h h₁ h₂ t (hsp t (lt_of_lt_of_le ht (min_le_left _ _)))
    (hct t (lt_of_lt_of_le ht (min_le_right _ _)))

end S7ESliding

section S7EMarks

/-! #### Generic mark-successor lemmas (any generic polygon): the key decomposition
`markKey m = edge.val + param`, and the shape of `nextMark` at a visit and at a vertex. -/

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)

omit [NeZero n] in
/-- The edge of a mark: the vertex's own label, the visit's edge. -/
def s7e_mEdge : Mark P → ZMod n
  | Sum.inl i => i
  | Sum.inr v => v.2.val

omit [NeZero n] in
/-- The parameter of a mark on its edge: `0` for a vertex, the visit parameter for a visit. -/
def s7e_mParam : Mark P → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => visitParameter v

omit [NeZero n] in
@[simp] theorem s7e_mEdge_inl (i : ZMod n) : s7e_mEdge (Sum.inl i : Mark P) = i := rfl
omit [NeZero n] in
@[simp] theorem s7e_mEdge_inr (v : Visit P) : s7e_mEdge (Sum.inr v) = v.2.val := rfl
omit [NeZero n] in
@[simp] theorem s7e_mParam_inl (i : ZMod n) : s7e_mParam (Sum.inl i : Mark P) = 0 := rfl
omit [NeZero n] in
@[simp] theorem s7e_mParam_inr (v : Visit P) : s7e_mParam (Sum.inr v) = visitParameter v := rfl

omit [NeZero n] in
include hn hP in
theorem s7e_visitParameter_pos (v : Visit P) : 0 < visitParameter v :=
  (crossingParameter_interior hn hP.1 v.1 v.2.val v.2.property).1

omit [NeZero n] in
include hn hP in
theorem s7e_visitParameter_lt_one (v : Visit P) : visitParameter v < 1 :=
  (crossingParameter_interior hn hP.1 v.1 v.2.val v.2.property).2

omit [NeZero n] in
include hn hP in
theorem s7e_mParam_nonneg (m : Mark P) : 0 ≤ s7e_mParam m := by
  cases m with
  | inl i => exact le_refl 0
  | inr v => exact (s7e_visitParameter_pos hn hP v).le

omit [NeZero n] in
include hn hP in
theorem s7e_mParam_lt_one (m : Mark P) : s7e_mParam m < 1 := by
  cases m with
  | inl i => exact zero_lt_one
  | inr v => exact s7e_visitParameter_lt_one hn hP v

/-- `markKey m = (edge m).val + param m`. -/
theorem s7e_markKey_eq (m : Mark P) :
    markKey hn hP.1 m = ((s7e_mEdge m).val : ℝ) + s7e_mParam m := by
  cases m with
  | inl i => rw [markKey_vertex]; simp
  | inr v => rfl

/-- The key order decoded (edge label first, then parameter). -/
theorem s7e_markKey_lt_iff (m m' : Mark P) :
    markKey hn hP.1 m < markKey hn hP.1 m' ↔
      (s7e_mEdge m).val < (s7e_mEdge m').val ∨
        (s7e_mEdge m = s7e_mEdge m' ∧ s7e_mParam m < s7e_mParam m') := by
  have h := traversalKey_lt_iff (markPosition hn hP.1 m) (markPosition hn hP.1 m')
  cases m <;> cases m' <;> exact h

omit [NeZero n] in
/-- `traversalBetween` on mark positions, read on keys. -/
theorem s7e_between_iff (p q r : Mark P) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r) ↔
      (markKey hn hP.1 p < markKey hn hP.1 q ∧ markKey hn hP.1 q < markKey hn hP.1 r) ∨
      (markKey hn hP.1 q < markKey hn hP.1 r ∧ markKey hn hP.1 r < markKey hn hP.1 p) ∨
      (markKey hn hP.1 r < markKey hn hP.1 p ∧ markKey hn hP.1 p < markKey hn hP.1 q) := Iff.rfl

/-- A key strictly between two integers-plus-parameters pins the edge: if
`e.val + p < e'.val + p' < e.val + 1` with `0 ≤ p'` then `e' = e`. -/
theorem s7e_edge_eq_of_key_sandwich {e e' : ZMod n} {p p' : ℝ} (hp0 : 0 ≤ p) (hp0' : 0 ≤ p')
    (hp1 : p' < 1) (h1 : (e.val : ℝ) + p < e'.val + p') (h2 : (e'.val : ℝ) + p' < e.val + 1) :
    e' = e := by
  apply ZMod.val_injective
  have h3 : (e.val : ℝ) < e'.val + 1 := by linarith
  have h4 : (e'.val : ℝ) < e.val + 1 := by linarith
  have h3' : e.val < e'.val + 1 := by exact_mod_cast h3
  have h4' : e'.val < e.val + 1 := by exact_mod_cast h4
  omega

/-- The key of a mark lies in `[edge.val, edge.val + 1)`. -/
theorem s7e_markKey_bounds (m : Mark P) :
    ((s7e_mEdge m).val : ℝ) ≤ markKey hn hP.1 m ∧ markKey hn hP.1 m < (s7e_mEdge m).val + 1 := by
  rw [s7e_markKey_eq hn hP]
  exact ⟨by linarith [s7e_mParam_nonneg hn hP m], by linarith [s7e_mParam_lt_one hn hP m]⟩

theorem s7e_markKey_nonneg (m : Mark P) : 0 ≤ markKey hn hP.1 m := by
  have := (s7e_markKey_bounds hn hP m).1
  have h0 : (0 : ℝ) ≤ (s7e_mEdge m).val := Nat.cast_nonneg _
  linarith

theorem s7e_markKey_lt_n (m : Mark P) : markKey hn hP.1 m < n := by
  have := (s7e_markKey_bounds hn hP m).2
  have h0 : ((s7e_mEdge m).val : ℝ) + 1 ≤ n := by exact_mod_cast (ZMod.val_lt (s7e_mEdge m))
  linarith

omit [NeZero n] in
/-- A mark with positive parameter is a visit. -/
theorem s7e_mark_visit_of_param_pos (m : Mark P) (h : 0 < s7e_mParam m) :
    ∃ w : Visit P, m = Sum.inr w := by
  cases m with
  | inl i => exact absurd h (lt_irrefl 0)
  | inr w => exact ⟨w, rfl⟩

/-- `(i + 1).val` in the two cases. -/
theorem s7e_val_succ (i : ZMod n) :
    (i ≠ -1 ∧ ((i + 1).val : ℝ) = i.val + 1) ∨ (i = -1 ∧ (i + 1 : ZMod n) = 0 ∧ (i.val : ℝ) = n - 1) := by
  by_cases hi : i = -1
  · right
    refine ⟨hi, by rw [hi]; ring, ?_⟩
    rw [hi]
    have h := last_index_val_succ (n := n)
    have h' : (((-1 : ZMod n).val : ℕ) : ℝ) + 1 = n := by exact_mod_cast h
    linarith
  · left
    refine ⟨hi, ?_⟩
    rw [zmod_val_next_of_ne_last hi]
    push_cast; ring

/-- **The next mark after a visit** is either the next vertex or a later visit on the same edge. -/
theorem s7e_nextMark_inr (v : Visit P) :
    nextMark hn hP (Sum.inr v) = Sum.inl (v.2.val + 1) ∨
      ∃ w : Visit P, nextMark hn hP (Sum.inr v) = Sum.inr w ∧ w.2.val = v.2.val ∧
        visitParameter v < visitParameter w := by
  by_cases hm : nextMark hn hP (Sum.inr v) = Sum.inl (v.2.val + 1)
  · exact Or.inl hm
  right
  have hne2 : Sum.inr v ≠ nextMark hn hP (Sum.inr v) := (markSuccessor_ne_self hn hP (Sum.inr v)).symm
  have hne1 : (Sum.inr v : Mark P) ≠ Sum.inl (v.2.val + 1) := Sum.inr_ne_inl
  have hb := (s7a_between_or hn hP (Sum.inr v) (nextMark hn hP (Sum.inr v)) (Sum.inl (v.2.val + 1))
    hne2 hm hne1).resolve_right (nextMark_no_mark_between hn hP rfl _)
  rw [s7e_between_iff hn hP] at hb
  have hkv : markKey hn hP.1 (Sum.inr v) = (v.2.val.val : ℝ) + visitParameter v :=
    s7e_markKey_eq hn hP _
  have hkm : markKey hn hP.1 (nextMark hn hP (Sum.inr v)) =
      ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) + s7e_mParam (nextMark hn hP (Sum.inr v)) :=
    s7e_markKey_eq hn hP _
  have hkl : markKey hn hP.1 (Sum.inl (v.2.val + 1) : Mark P) = ((v.2.val + 1).val : ℝ) :=
    markKey_vertex hn hP.1 _
  have hc0 := s7e_visitParameter_pos hn hP v
  have hc1 := s7e_visitParameter_lt_one hn hP v
  have hp0 := s7e_mParam_nonneg hn hP (nextMark hn hP (Sum.inr v))
  have hp1 := s7e_mParam_lt_one hn hP (nextMark hn hP (Sum.inr v))
  have hk0 := s7e_markKey_nonneg hn hP (nextMark hn hP (Sum.inr v))
  have hev : ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) + 1 ≤ n := by
    exact_mod_cast ZMod.val_lt (s7e_mEdge (nextMark hn hP (Sum.inr v)))
  have key : s7e_mEdge (nextMark hn hP (Sum.inr v)) = v.2.val ∧
      visitParameter v < s7e_mParam (nextMark hn hP (Sum.inr v)) := by
    rcases s7e_val_succ (v.2.val) with ⟨_, hval⟩ | ⟨_, hzero, hval⟩
    · rcases hb with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h2, _⟩
      · have h1' : (v.2.val.val : ℝ) + visitParameter v <
            ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) +
              s7e_mParam (nextMark hn hP (Sum.inr v)) := by linarith
        have h2' : ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) +
            s7e_mParam (nextMark hn hP (Sum.inr v)) < (v.2.val.val : ℝ) + 1 := by linarith
        have he := s7e_edge_eq_of_key_sandwich hc0.le hp0 hp1 h1' h2'
        refine ⟨he, ?_⟩
        have : ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) = v.2.val.val := by rw [he]
        linarith
      · exfalso; linarith
      · exfalso; linarith
    · have hz : markKey hn hP.1 (Sum.inl (v.2.val + 1) : Mark P) = 0 := by
        rw [hkl, hzero, ZMod.val_zero, Nat.cast_zero]
      rcases hb with ⟨_, h2⟩ | ⟨h2, _⟩ | ⟨_, h2⟩
      · exfalso; linarith
      · exfalso; linarith
      · have h3 : ((n - 1 : ℕ) : ℝ) < (((s7e_mEdge (nextMark hn hP (Sum.inr v))).val + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)]; push_cast; linarith
        have h3' : n - 1 < (s7e_mEdge (nextMark hn hP (Sum.inr v))).val + 1 := by exact_mod_cast h3
        have h4 : n - 1 ≤ (s7e_mEdge (nextMark hn hP (Sum.inr v))).val := by omega
        have h5 : ((n - 1 : ℕ) : ℝ) ≤ (s7e_mEdge (nextMark hn hP (Sum.inr v))).val := by
          exact_mod_cast h4
        rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)] at h5
        push_cast at h5
        have h10 : ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) = v.2.val.val := by linarith
        have he : s7e_mEdge (nextMark hn hP (Sum.inr v)) = v.2.val :=
          ZMod.val_injective n (by exact_mod_cast h10)
        exact ⟨he, by linarith⟩
  obtain ⟨w, hw⟩ := s7e_mark_visit_of_param_pos (nextMark hn hP (Sum.inr v))
    (lt_of_le_of_lt hc0.le key.2)
  refine ⟨w, hw, ?_, ?_⟩
  · have := key.1; rw [hw] at this; exact this
  · have := key.2; rw [hw] at this; exact this

/-- **The next mark after a vertex** is either the next vertex or a visit on the vertex's edge. -/
theorem s7e_nextMark_inl (i : ZMod n) :
    nextMark hn hP (Sum.inl i) = Sum.inl (i + 1) ∨
      ∃ w : Visit P, nextMark hn hP (Sum.inl i) = Sum.inr w ∧ w.2.val = i := by
  by_cases hm : nextMark hn hP (Sum.inl i) = Sum.inl (i + 1)
  · exact Or.inl hm
  right
  have hne2 : (Sum.inl i : Mark P) ≠ nextMark hn hP (Sum.inl i) :=
    (markSuccessor_ne_self hn hP (Sum.inl i)).symm
  have hne1 : (Sum.inl i : Mark P) ≠ Sum.inl (i + 1) := by
    intro h
    have h' : i = i + 1 := Sum.inl_injective h
    have : (1 : ZMod n) = 0 := by linear_combination -h'
    have _inst : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
    exact one_ne_zero this
  have hb := (s7a_between_or hn hP (Sum.inl i) (nextMark hn hP (Sum.inl i)) (Sum.inl (i + 1))
    hne2 hm hne1).resolve_right (nextMark_no_mark_between hn hP rfl _)
  rw [s7e_between_iff hn hP] at hb
  have hki : markKey hn hP.1 (Sum.inl i : Mark P) = (i.val : ℝ) := markKey_vertex hn hP.1 _
  have hkm : markKey hn hP.1 (nextMark hn hP (Sum.inl i)) =
      ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) + s7e_mParam (nextMark hn hP (Sum.inl i)) :=
    s7e_markKey_eq hn hP _
  have hkl : markKey hn hP.1 (Sum.inl (i + 1) : Mark P) = ((i + 1).val : ℝ) := markKey_vertex hn hP.1 _
  have hp0 := s7e_mParam_nonneg hn hP (nextMark hn hP (Sum.inl i))
  have hp1 := s7e_mParam_lt_one hn hP (nextMark hn hP (Sum.inl i))
  have hk0 := s7e_markKey_nonneg hn hP (nextMark hn hP (Sum.inl i))
  have hev : ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) + 1 ≤ n := by
    exact_mod_cast ZMod.val_lt (s7e_mEdge (nextMark hn hP (Sum.inl i)))
  have key : s7e_mEdge (nextMark hn hP (Sum.inl i)) = i ∧ 0 < s7e_mParam (nextMark hn hP (Sum.inl i)) := by
    rcases s7e_val_succ i with ⟨_, hval⟩ | ⟨_, hzero, hval⟩
    · rcases hb with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h2, _⟩
      · have h1' : (i.val : ℝ) + 0 < ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) +
            s7e_mParam (nextMark hn hP (Sum.inl i)) := by linarith
        have h2' : ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) +
            s7e_mParam (nextMark hn hP (Sum.inl i)) < (i.val : ℝ) + 1 := by linarith
        have he := s7e_edge_eq_of_key_sandwich (le_refl (0 : ℝ)) hp0 hp1 h1' h2'
        refine ⟨he, ?_⟩
        have : ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) = i.val := by rw [he]
        linarith
      · exfalso; linarith
      · exfalso; linarith
    · have hz : markKey hn hP.1 (Sum.inl (i + 1) : Mark P) = 0 := by
        rw [hkl, hzero, ZMod.val_zero, Nat.cast_zero]
      rcases hb with ⟨_, h2⟩ | ⟨h2, _⟩ | ⟨_, h2⟩
      · exfalso; linarith
      · exfalso; linarith
      · have h3 : ((n - 1 : ℕ) : ℝ) < (((s7e_mEdge (nextMark hn hP (Sum.inl i))).val + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)]; push_cast; linarith
        have h3' : n - 1 < (s7e_mEdge (nextMark hn hP (Sum.inl i))).val + 1 := by exact_mod_cast h3
        have h4 : n - 1 ≤ (s7e_mEdge (nextMark hn hP (Sum.inl i))).val := by omega
        have h5 : ((n - 1 : ℕ) : ℝ) ≤ (s7e_mEdge (nextMark hn hP (Sum.inl i))).val := by
          exact_mod_cast h4
        rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)] at h5
        push_cast at h5
        have h10 : ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) = i.val := by linarith
        have he : s7e_mEdge (nextMark hn hP (Sum.inl i)) = i :=
          ZMod.val_injective n (by exact_mod_cast h10)
        exact ⟨he, by linarith⟩
  obtain ⟨w, hw⟩ := s7e_mark_visit_of_param_pos (nextMark hn hP (Sum.inl i)) key.2
  refine ⟨w, hw, ?_⟩
  have := key.1; rw [hw] at this; exact this

/-- Uniqueness of the successor: a mark `m' ≠ m` with no mark strictly between `m` and `m'` is
`nextMark m`. -/
theorem s7e_nextMark_eq_of_no_between (m m' : Mark P) (hne : m ≠ m')
    (hno : ∀ u : Mark P, ¬ traversalBetween (markPosition hn hP.1 m) (markPosition hn hP.1 u)
      (markPosition hn hP.1 m')) : nextMark hn hP m = m' := by
  by_contra hne'
  have hne2 : m ≠ nextMark hn hP m := (markSuccessor_ne_self hn hP m).symm
  rcases s7a_between_or hn hP m (nextMark hn hP m) m' hne2 hne' hne with hb | hb
  · exact hno _ hb
  · exact nextMark_no_mark_between hn hP rfl m' hb

include hn hP in
/-- Two visits on one edge with equal parameters coincide. -/
theorem s7e_visit_eq_of_param (u w : Visit P) (he : u.2.val = w.2.val)
    (hp : visitParameter u = visitParameter w) : u = w := by
  have hk : markKey hn hP.1 (Sum.inr u) = markKey hn hP.1 (Sum.inr w) := by
    rw [s7e_markKey_eq hn hP, s7e_markKey_eq hn hP]
    simp only [s7e_mEdge_inr, s7e_mParam_inr, he, hp]
  exact Sum.inr_injective (markKey_injective hn hP hk)

/-- Betweenness of three marks on one edge in parameter order. -/
theorem s7e_between_same_edge (p q r : Mark P) (hpq : s7e_mEdge p = s7e_mEdge q)
    (hqr : s7e_mEdge q = s7e_mEdge r) (h1 : s7e_mParam p < s7e_mParam q)
    (h2 : s7e_mParam q < s7e_mParam r) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r) := by
  rw [s7e_between_iff hn hP]
  left
  rw [s7e_markKey_eq hn hP, s7e_markKey_eq hn hP, s7e_markKey_eq hn hP, hpq, hqr]
  constructor <;> linarith

/-- A mark on edge `i` with positive parameter lies between the vertex `i` and the vertex `i + 1`. -/
theorem s7e_between_inl_mark_inl (i : ZMod n) (q : Mark P) (hq : s7e_mEdge q = i)
    (hp : 0 < s7e_mParam q) :
    traversalBetween (markPosition hn hP.1 (Sum.inl i)) (markPosition hn hP.1 q)
      (markPosition hn hP.1 (Sum.inl (i + 1))) := by
  rw [s7e_between_iff hn hP, markKey_vertex, markKey_vertex, s7e_markKey_eq hn hP, hq]
  have hp1 := s7e_mParam_lt_one hn hP q
  rcases s7e_val_succ i with ⟨_, hval⟩ | ⟨_, hzero, hval⟩
  · left; rw [hval]; constructor <;> linarith
  · right; right
    rw [hzero, ZMod.val_zero, Nat.cast_zero, hval]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    constructor <;> linarith

/-- A visit on edge `i` with parameter above `p`'s (on the same edge) lies between `p` and the vertex
`i + 1`. -/
theorem s7e_between_mark_mark_inl (p q : Mark P) (hpq : s7e_mEdge p = s7e_mEdge q)
    (h1 : s7e_mParam p < s7e_mParam q) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q)
      (markPosition hn hP.1 (Sum.inl (s7e_mEdge p + 1))) := by
  rw [s7e_between_iff hn hP, markKey_vertex, s7e_markKey_eq hn hP, s7e_markKey_eq hn hP, ← hpq]
  have hp1 := s7e_mParam_lt_one hn hP q
  have hp0 := s7e_mParam_nonneg hn hP p
  rcases s7e_val_succ (s7e_mEdge p) with ⟨_, hval⟩ | ⟨_, hzero, hval⟩
  · left; rw [hval]; constructor <;> linarith
  · right; right
    rw [hzero, ZMod.val_zero, Nat.cast_zero, hval]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    constructor <;> linarith

/-- `nextMark (inr v) = inl (v.edge + 1)` when no visit on the edge comes later. -/
theorem s7e_nextMark_inr_eq_inl (v : Visit P)
    (hlast : ∀ u : Visit P, u.2.val = v.2.val → visitParameter u ≤ visitParameter v) :
    nextMark hn hP (Sum.inr v) = Sum.inl (v.2.val + 1) := by
  rcases s7e_nextMark_inr hn hP v with h | ⟨w, _, hwe, hwp⟩
  · exact h
  · exact absurd (hlast w hwe) (not_le.mpr hwp)

/-- `nextMark (inl i) = inr w` when `w` is the first visit on edge `i`. -/
theorem s7e_nextMark_inl_eq_inr (i : ZMod n) (w : Visit P) (hw : w.2.val = i)
    (hmin : ∀ u : Visit P, u.2.val = i → visitParameter w ≤ visitParameter u) :
    nextMark hn hP (Sum.inl i) = Sum.inr w := by
  rcases s7e_nextMark_inl hn hP i with h | ⟨w', h', hw'⟩
  · exfalso
    have hb := s7e_between_inl_mark_inl hn hP i (Sum.inr w) hw (s7e_visitParameter_pos hn hP w)
    exact nextMark_no_mark_between hn hP h (Sum.inr w) hb
  · by_cases hww : w' = w
    · rw [h', hww]
    · exfalso
      have hle := hmin w' hw'
      have hlt : visitParameter w < visitParameter w' := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact absurd (s7e_visit_eq_of_param hn hP w' w (hw'.trans hw.symm) heq.symm) hww
      have hb := s7e_between_same_edge hn hP (Sum.inl i) (Sum.inr w) (Sum.inr w') hw.symm
        (hw.trans hw'.symm) (s7e_visitParameter_pos hn hP w) hlt
      exact nextMark_no_mark_between hn hP h' (Sum.inr w) hb

/-- `nextMark (inr v) = inr w` when `w` is the first later visit on the same edge. -/
theorem s7e_nextMark_inr_eq_inr (v w : Visit P) (he : w.2.val = v.2.val)
    (hp : visitParameter v < visitParameter w)
    (hmin : ∀ u : Visit P, u.2.val = v.2.val → visitParameter v < visitParameter u →
      visitParameter w ≤ visitParameter u) :
    nextMark hn hP (Sum.inr v) = Sum.inr w := by
  rcases s7e_nextMark_inr hn hP v with h | ⟨w', h', hw'e, hw'p⟩
  · exfalso
    have hb := s7e_between_mark_mark_inl hn hP (Sum.inr v) (Sum.inr w) he.symm hp
    exact nextMark_no_mark_between hn hP h (Sum.inr w) hb
  · by_cases hww : w' = w
    · rw [h', hww]
    · exfalso
      have hle := hmin w' hw'e hw'p
      have hlt : visitParameter w < visitParameter w' := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact absurd (s7e_visit_eq_of_param hn hP w' w (hw'e.trans he.symm) heq.symm) hww
      have hb := s7e_between_same_edge hn hP (Sum.inr v) (Sum.inr w) (Sum.inr w') he.symm
        (he.trans hw'e.symm) hp hlt
      exact nextMark_no_mark_between hn hP h' (Sum.inr w) hb

/-- The owner of an UNSELECTED visit is the owner of the next mark. -/
theorem s7e_owner_inr_eq_next (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    owner hn hP S (Sum.inr v) = owner hn hP S (nextMark hn hP (Sum.inr v)) := by
  rw [owner_eq_iff]
  have h := (Equiv.Perm.SameCycle.refl (smoothingSuccessor hn hP S) (Sum.inr v)).apply_right
  rwa [smoothingSuccessor_visit_of_not_mem hn hP S v hv] at h

/-- The owner of a vertex is the owner of the next mark. -/
theorem s7e_owner_inl_eq_next (S : Finset (Crossing P)) (i : ZMod n) :
    owner hn hP S (Sum.inl i) = owner hn hP S (nextMark hn hP (Sum.inl i)) := by
  rw [owner_eq_iff]
  have h := (Equiv.Perm.SameCycle.refl (smoothingSuccessor hn hP S) (Sum.inl i)).apply_right
  rwa [smoothingSuccessor_vertex hn hP S i] at h

end S7EMarks

section S7ERotated

/-! #### Rotated Gauss lists from a relocation (U110-D's cut form, specialised): the visit map is
key-monotone except at ONE visit `z`, which moves from the top of the key order to the bottom
(`s7e_isRotated_of_top_to_bottom`) or from the bottom to the top (`s7e_isRotated_of_bottom_to_top`);
or is key-monotone throughout (`s7e_isRotated_of_strictMono`). -/

variable {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}

theorem s7e_isRotated_of_strictMono (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q)
    (X : Finset (Crossing P)) (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w)) :
    (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ) := by
  rw [s7d_gaussList_eq_of_strictMono hcP hcQ X Y φ hmem hmono]

/-- The relocated visit `z` is the LAST visit of `X` in the key order of `P` and its image the FIRST
in the key order of `Q`; everything else is key-monotone. -/
theorem s7e_isRotated_of_top_to_bottom (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q)
    (X : Finset (Crossing P)) (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q) (z : Visit P)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X → v ≠ z → w ≠ z →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w))
    (htop : ∀ v : Visit P, v.1 ∈ X → v ≠ z → geometricVisitKey hcP v < geometricVisitKey hcP z)
    (hbot : ∀ v : Visit P, v.1 ∈ X → v ≠ z →
      geometricVisitKey hcQ (φ z) < geometricVisitKey hcQ (φ v)) :
    (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ) := by
  apply s7d_gaussList_isRotated_of_cut hcP hcQ X Y φ (geometricVisitKey hcP z) hmem
  · intro v w hv hw hvw hblk
    have hwz : w ≠ z := by
      rintro rfl
      rcases hblk with h | h
      · exact lt_irrefl _ h
      · exact lt_irrefl _ (lt_of_le_of_lt h hvw)
    have hvz : v ≠ z := by
      rintro rfl
      exact lt_irrefl _ (hvw.trans (htop w hw hwz))
    exact hmono v w hv hw hvz hwz hvw
  · intro v w hv hw hvc hcw
    have hwz : w = z := by
      by_contra hne
      exact absurd (htop w hw hne) (not_lt.mpr hcw)
    have hvz : v ≠ z := by
      rintro rfl
      exact lt_irrefl _ hvc
    subst hwz
    exact hbot v hv hvz

/-- The relocated visit `z` is the FIRST visit of `X` in the key order of `P` (below the cut `c`, all
others at or above it) and its image the LAST in the key order of `Q`; everything else is
key-monotone. -/
theorem s7e_isRotated_of_bottom_to_top (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q)
    (X : Finset (Crossing P)) (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q) (z : Visit P) (c : ℝ)
    (hzc : geometricVisitKey hcP z < c)
    (hc : ∀ v : Visit P, v.1 ∈ X → v ≠ z → c ≤ geometricVisitKey hcP v)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X → v ≠ z → w ≠ z →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w))
    (htop : ∀ v : Visit P, v.1 ∈ X → v ≠ z →
      geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ z)) :
    (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ) := by
  apply s7d_gaussList_isRotated_of_cut hcP hcQ X Y φ c hmem
  · intro v w hv hw hvw hblk
    have hwz : w ≠ z := by
      intro hwz
      have hvz : v ≠ z := by
        intro hvz
        rw [hvz, hwz] at hvw
        exact lt_irrefl _ hvw
      rw [hwz] at hvw
      exact lt_irrefl _ (lt_trans (lt_of_le_of_lt (hc v hv hvz) hvw) hzc)
    have hvz : v ≠ z := by
      intro hvz
      rw [hvz] at hblk
      rcases hblk with h | h
      · exact absurd (hc w hw hwz) (not_le.mpr h)
      · exact lt_irrefl _ (lt_of_lt_of_le hzc h)
    exact hmono v w hv hw hvz hwz hvw
  · intro v w hv hw hvc hcw
    have hvz : v = z := by
      by_contra hne
      exact absurd (hc v hv hne) (not_le.mpr hvc)
    have hwz : w ≠ z := by
      rintro rfl
      exact lt_irrefl _ (lt_of_lt_of_le hzc hcw)
    subst hvz
    exact htop w hw hwz

end S7ERotated

section S7EContactVisits

/-! #### The two visits of a crossing `{a, ℓ}` (generic `Q`): `s7e_va` on edge `a`, `s7e_vl` on edge `ℓ`
(twins of each other), their parameters (Cramer's `edgeParameter`), and exhaustion. -/

variable (hn : 3 ≤ n) {Q : LabelledTuple n} (hQ : Generic Q) {a ℓ : ZMod n}

omit [NeZero n] in
/-- The visit of the crossing `{a, ℓ}` on edge `a`. -/
def s7e_va (hc : IsCrossing Q {a, ℓ}) : Visit Q := pairVisit hc

omit [NeZero n] in
/-- The visit of the crossing `{a, ℓ}` on edge `ℓ`. -/
def s7e_vl (hc : IsCrossing Q {a, ℓ}) : Visit Q :=
  pairVisit (by rw [Finset.pair_comm]; exact hc : IsCrossing Q {ℓ, a})

omit [NeZero n] in
theorem s7e_va_fst_val (hc : IsCrossing Q {a, ℓ}) : (s7e_va hc).1.val = {a, ℓ} := rfl
omit [NeZero n] in
theorem s7e_va_edge (hc : IsCrossing Q {a, ℓ}) : (s7e_va hc).2.val = a := rfl
omit [NeZero n] in
theorem s7e_vl_fst_val (hc : IsCrossing Q {a, ℓ}) : (s7e_vl hc).1.val = {ℓ, a} := rfl
omit [NeZero n] in
theorem s7e_vl_edge (hc : IsCrossing Q {a, ℓ}) : (s7e_vl hc).2.val = ℓ := rfl

omit [NeZero n] in
theorem s7e_vl_fst (hc : IsCrossing Q {a, ℓ}) : (s7e_vl hc).1 = (s7e_va hc).1 :=
  Subtype.ext (Finset.pair_comm ℓ a)

omit [NeZero n] in
theorem s7e_va_fst_eq (hc : IsCrossing Q {a, ℓ}) : (s7e_va hc).1 = ⟨{a, ℓ}, hc⟩ := rfl

omit [NeZero n] in
include hn hQ in
theorem s7e_va_param (hc : IsCrossing Q {a, ℓ}) :
    visitParameter (s7e_va hc) = edgeParameter Q a ℓ :=
  pairVisit_parameter hn hQ.1 hc

omit [NeZero n] in
include hn hQ in
theorem s7e_vl_param (hc : IsCrossing Q {a, ℓ}) :
    visitParameter (s7e_vl hc) = edgeParameter Q ℓ a :=
  pairVisit_parameter hn hQ.1 _

omit [NeZero n] in
theorem s7e_vl_ne_va (hc : IsCrossing Q {a, ℓ}) (ha : a ≠ ℓ) : s7e_vl hc ≠ s7e_va hc := by
  intro h
  exact ha (congrArg (fun v : Visit Q => v.2.val) h).symm

omit [NeZero n] in
theorem s7e_twin_va (hc : IsCrossing Q {a, ℓ}) (ha : a ≠ ℓ) : visitTwin (s7e_va hc) = s7e_vl hc :=
  (visitTwin_unique (s7e_va hc) (s7e_vl hc) (s7e_vl_fst hc) (s7e_vl_ne_va hc ha)).symm

omit [NeZero n] in
theorem s7e_twin_vl (hc : IsCrossing Q {a, ℓ}) (ha : a ≠ ℓ) : visitTwin (s7e_vl hc) = s7e_va hc := by
  rw [← s7e_twin_va hc ha, visitTwin_involutive]

omit [NeZero n] in
/-- Every visit of the crossing `{a, ℓ}` is one of the two. -/
theorem s7e_visit_of_fst (hc : IsCrossing Q {a, ℓ}) (v : Visit Q) (hv : v.1.val = {a, ℓ}) (ha : a ≠ ℓ) :
    v = s7e_va hc ∨ v = s7e_vl hc := by
  have h1 : v.1 = (s7e_va hc).1 := Subtype.ext hv
  rcases visit_eq_or_twin (s7e_va hc) v h1 with h | h
  · exact Or.inl h
  · right; rw [h, s7e_twin_va hc ha]

omit [NeZero n] in
theorem s7e_visit_eq_va (hc : IsCrossing Q {a, ℓ}) (v : Visit Q) (hv : v.1.val = {a, ℓ})
    (he : v.2.val = a) (ha : a ≠ ℓ) : v = s7e_va hc := by
  rcases s7e_visit_of_fst hc v hv ha with h | h
  · exact h
  · exfalso; rw [h, s7e_vl_edge] at he; exact ha he.symm

omit [NeZero n] in
theorem s7e_visit_eq_vl (hc : IsCrossing Q {a, ℓ}) (v : Visit Q) (hv : v.1.val = {a, ℓ})
    (he : v.2.val = ℓ) (ha : a ≠ ℓ) : v = s7e_vl hc := by
  rcases s7e_visit_of_fst hc v hv ha with h | h
  · exfalso; rw [h, s7e_va_edge] at he; exact ha he
  · exact h

omit [NeZero n] in
/-- A visit of the crossing `{a, ℓ}` is on edge `a` or on edge `ℓ`. -/
theorem s7e_edge_of_fst (v : Visit Q) (hv : v.1.val = {a, ℓ}) : v.2.val = a ∨ v.2.val = ℓ := by
  have hm : v.2.val ∈ ({a, ℓ} : Finset (ZMod n)) := hv ▸ v.2.property
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

end S7EContactVisits

section S7ECrossEquiv

/-! #### The crossing bijection `Crossing P ≃ Crossing Q` of a sliding wall: `xm ↦ xp`, persistent
crossings by their supports (`s7a_cross`); its `Finset.map` on supports. -/

variable {P Q : LabelledTuple n} {M a : ZMod n}
  (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (xm : Crossing P) (xp : Crossing Q)

omit [NeZero n] in
/-- The crossing map: the contact crossing to the contact crossing, persistent crossings by support. -/
def s7e_crossMap (x : Crossing P) : Crossing Q :=
  if hx : ContactAffected M a x.val then xp else s7a_cross hs x hx

omit [NeZero n] in
theorem s7e_crossMap_of_not (x : Crossing P) (hx : ¬ ContactAffected M a x.val) :
    s7e_crossMap hs xp x = s7a_cross hs x hx := dite_eq_right hx

omit [NeZero n] in
theorem s7e_crossMap_of_affected (x : Crossing P) (hx : ContactAffected M a x.val) :
    s7e_crossMap hs xp x = xp := dite_eq_left hx

variable (hm : ∀ y : Crossing P, ContactAffected M a y.val → y = xm)
  (hp : ∀ y : Crossing Q, ContactAffected M a y.val → y = xp)
  (hxm : ContactAffected M a xm.val) (hxp : ContactAffected M a xp.val)

include hm hxp in
omit [NeZero n] in
theorem s7e_crossMap_injective : Function.Injective (s7e_crossMap hs xp) := by
  intro x y hxy
  by_cases hx : ContactAffected M a x.val <;> by_cases hy : ContactAffected M a y.val
  · rw [hm x hx, hm y hy]
  · exfalso
    rw [s7e_crossMap_of_affected hs xp x hx, s7e_crossMap_of_not hs xp y hy] at hxy
    have hv := congrArg Subtype.val hxy
    rw [s7a_cross_val] at hv
    exact hy (hv ▸ hxp)
  · exfalso
    rw [s7e_crossMap_of_affected hs xp y hy, s7e_crossMap_of_not hs xp x hx] at hxy
    have hv := congrArg Subtype.val hxy
    rw [s7a_cross_val] at hv
    exact hx (hv.symm ▸ hxp)
  · rw [s7e_crossMap_of_not hs xp x hx, s7e_crossMap_of_not hs xp y hy] at hxy
    have hv := congrArg Subtype.val hxy
    exact Subtype.ext hv

include hp hxm in
omit [NeZero n] in
theorem s7e_crossMap_surjective : Function.Surjective (s7e_crossMap hs xp) := by
  intro y
  by_cases hy : ContactAffected M a y.val
  · refine ⟨xm, ?_⟩
    rw [s7e_crossMap_of_affected hs xp xm hxm, hp y hy]
  · obtain ⟨x, hx, hxy⟩ := s7a_cross_surj hs y hy
    refine ⟨x, ?_⟩
    rw [s7e_crossMap_of_not hs xp x hx]
    exact hxy

omit [NeZero n] in
/-- The crossing bijection of the sliding wall. -/
def s7e_crossEquiv : Crossing P ≃ Crossing Q :=
  Equiv.ofBijective (s7e_crossMap hs xp)
    ⟨s7e_crossMap_injective hs xm xp hm hxp, s7e_crossMap_surjective hs xm xp hp hxm⟩

omit [NeZero n] in
theorem s7e_crossEquiv_apply (x : Crossing P) :
    s7e_crossEquiv hs xm xp hm hp hxm hxp x = s7e_crossMap hs xp x := rfl

omit [NeZero n] in
theorem s7e_crossEquiv_xm : s7e_crossEquiv hs xm xp hm hp hxm hxp xm = xp :=
  s7e_crossMap_of_affected hs xp xm hxm

omit [NeZero n] in
theorem s7e_crossEquiv_symm_xp : (s7e_crossEquiv hs xm xp hm hp hxm hxp).symm xp = xm :=
  (Equiv.symm_apply_eq _).mpr (s7e_crossEquiv_xm hs xm xp hm hp hxm hxp).symm

omit [NeZero n] in
theorem s7e_crossEquiv_of_not (x : Crossing P) (hx : ¬ ContactAffected M a x.val) :
    s7e_crossEquiv hs xm xp hm hp hxm hxp x = s7a_cross hs x hx :=
  s7e_crossMap_of_not hs xp x hx

omit [NeZero n] in
/-- The induced bijection of supports (`Finset.map` along the crossing bijection). -/
def s7e_supportEquiv : Finset (Crossing P) ≃ Finset (Crossing Q) where
  toFun S := S.map (s7e_crossEquiv hs xm xp hm hp hxm hxp).toEmbedding
  invFun S := S.map (s7e_crossEquiv hs xm xp hm hp hxm hxp).symm.toEmbedding
  left_inv S := by simp [Finset.map_map]
  right_inv S := by simp [Finset.map_map]

omit [NeZero n] in
theorem s7e_supportEquiv_apply (S : Finset (Crossing P)) :
    s7e_supportEquiv hs xm xp hm hp hxm hxp S =
      S.map (s7e_crossEquiv hs xm xp hm hp hxm hxp).toEmbedding := rfl

omit [NeZero n] in
theorem s7e_mem_supportEquiv (S : Finset (Crossing P)) (x : Crossing P) :
    s7e_crossEquiv hs xm xp hm hp hxm hxp x ∈ s7e_supportEquiv hs xm xp hm hp hxm hxp S ↔ x ∈ S :=
  Finset.mem_map' _

omit [NeZero n] in
theorem s7e_xp_mem_supportEquiv (S : Finset (Crossing P)) :
    xp ∈ s7e_supportEquiv hs xm xp hm hp hxm hxp S ↔ xm ∈ S := by
  rw [s7e_supportEquiv_apply, Finset.mem_map_equiv, s7e_crossEquiv_symm_xp]

include hm in
omit [NeZero n] in
/-- The supports avoiding `xm` are persistent. -/
theorem s7e_persistent_of_not_mem (S : Finset (Crossing P)) (hS : xm ∉ S) :
    ∀ x ∈ S, ¬ ContactAffected M a x.val :=
  fun x hx hxa => hS (hm x hxa ▸ hx)

omit [NeZero n] in
/-- The image of a support avoiding `xm` is persistent. -/
theorem s7e_supportEquiv_persistent (S : Finset (Crossing P)) (hS : xm ∉ S) :
    ∀ y ∈ s7e_supportEquiv hs xm xp hm hp hxm hxp S, ¬ ContactAffected M a y.val := by
  intro y hy hya
  rw [hp y hya, s7e_xp_mem_supportEquiv] at hy
  exact hS hy

omit [NeZero n] in
/-- U110-A's `hSS'` for the image support. -/
theorem s7e_supportEquiv_hSS' (S : Finset (Crossing P)) :
    ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      (s7a_visit hs v hv).1 ∈ s7e_supportEquiv hs xm xp hm hp hxm hxp S ↔ v.1 ∈ S := by
  intro v hv
  rw [s7a_visit_fst, ← s7e_crossEquiv_of_not hs xm xp hm hp hxm hxp v.1 hv, s7e_mem_supportEquiv]

omit [NeZero n] in
/-- The spectator bijection `{S // xm ∉ S} ≃ {S // xp ∉ S}`. -/
def s7e_spectatorEquiv : {S : Finset (Crossing P) // xm ∉ S} ≃ {S : Finset (Crossing Q) // xp ∉ S} :=
  Equiv.subtypeEquiv (s7e_supportEquiv hs xm xp hm hp hxm hxp)
    (fun S => not_congr (s7e_xp_mem_supportEquiv hs xm xp hm hp hxm hxp S).symm)

omit [NeZero n] in
theorem s7e_spectatorEquiv_val (S : {S : Finset (Crossing P) // xm ∉ S}) :
    (s7e_spectatorEquiv hs xm xp hm hp hxm hxp S).1 = s7e_supportEquiv hs xm xp hm hp hxm hxp S.1 := rfl

end S7ECrossEquiv

section S7ESidePolygon

/-! #### A side polygon `Q` of a sliding wall with its contact crossing `{a, contactLeg f M}` and the
parameter windows (lem:wall-sides (V), `ContactParameterWindows`): the leg visit is adjacent to the
vertex `μ_M` (so they share their owner for every support avoiding the contact crossing), and the
successor of the `a`-visit is persistent. -/

variable (hn : 3 ≤ n) {C Q : LabelledTuple n} (hQ : Generic Q) {M a : ZMod n} {r η : ℝ} (f : Bool)
  (hsep : ContactSeparated M a) (hη : 0 < η) (hηr : 4 * η < r) (hηr1 : 4 * η < 1 - r)
  (hw : ContactParameterWindows C Q M a r η)
  (hc : IsCrossing Q {a, contactLeg f M})
  (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg f M})

include hsep in
omit [NeZero n] in
theorem s7e_a_ne_leg : a ≠ contactLeg f M := by
  intro h
  cases f
  · exact hsep.2.2.1 (by simp only [contactLeg, Bool.false_eq_true, ↓reduceIte] at h; rw [h]; ring)
  · exact hsep.2.1 (by simp only [contactLeg, ↓reduceIte] at h; exact h.symm)

include hsep in
omit [NeZero n] in
theorem s7e_a_ne_M : a ≠ M := fun h => hsep.2.1 h.symm

include hsep in
omit [NeZero n] in
theorem s7e_a_ne_M_sub_one : a ≠ M - 1 := fun h => hsep.2.2.1 (by rw [h]; ring)

include hsep in
omit [NeZero n] in
theorem s7e_a_add_one_ne_M : a + 1 ≠ M := fun h => hsep.2.2.1 h.symm

include hsep in
omit [NeZero n] in
theorem s7e_M_ne_a_add_one : M ≠ a + 1 := hsep.2.2.1

include hn hQ hw in
/-- A persistent visit on edge `a` has its parameter more than `3η` away from `r`. -/
theorem s7e_persist_a (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    3 * η < |visitParameter u - r| :=
  unaffected_visit_outside_window hn hQ.1 hw u hu none he

include hn hQ hw in
/-- A persistent visit on the leg edge `contactLeg f' M` has its parameter more than `3η` away from
the contact endpoint. -/
theorem s7e_persist_leg (f' : Bool) (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val)
    (he : u.2.val = contactLeg f' M) : 3 * η < |visitParameter u - contactEndpoint f'| :=
  unaffected_visit_outside_window hn hQ.1 hw u hu (some f') he

include hn hQ hw in
theorem s7e_persist_M_sub_one (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val)
    (he : u.2.val = M - 1) : visitParameter u < 1 - 3 * η := by
  have h1 := s7e_persist_leg hn hQ hw false u hu he
  have h2 := s7e_visitParameter_lt_one hn hQ u
  simp only [contactEndpoint, Bool.false_eq_true, ↓reduceIte] at h1
  rw [abs_of_neg (by linarith)] at h1
  linarith

include hn hQ hw in
theorem s7e_persist_M (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = M) :
    3 * η < visitParameter u := by
  have h1 := s7e_persist_leg hn hQ hw true u hu he
  have h2 := s7e_visitParameter_pos hn hQ u
  simp only [contactEndpoint, ↓reduceIte] at h1
  rw [abs_of_pos (by linarith)] at h1
  linarith

omit [NeZero n] in
include hn hQ hw in
/-- The contact visit on edge `a` has its parameter within `η` of `r`. -/
theorem s7e_va_param_near (hc : IsCrossing Q {a, contactLeg f M}) :
    |visitParameter (s7e_va hc) - r| < η := by
  rw [s7e_va_param hn hQ]
  exact (hw.2.2 f).1

omit [NeZero n] in
include hn hQ hw in
/-- The contact visit on the leg has its parameter within `η` of the contact endpoint. -/
theorem s7e_vl_param_near (hc : IsCrossing Q {a, contactLeg f M}) :
    |visitParameter (s7e_vl hc) - contactEndpoint f| < η := by
  rw [s7e_vl_param hn hQ]
  exact (hw.2.2 f).2

omit [NeZero n] in
include hn hQ hw in
theorem s7e_vl_param_false (hc : IsCrossing Q {a, contactLeg false M}) :
    1 - η < visitParameter (s7e_vl hc) := by
  have h1 := s7e_vl_param_near hn hQ false hw hc
  simp only [contactEndpoint, Bool.false_eq_true, ↓reduceIte] at h1
  have := (abs_lt.mp h1).1
  linarith

omit [NeZero n] in
include hn hQ hw in
theorem s7e_vl_param_true (hc : IsCrossing Q {a, contactLeg true M}) :
    visitParameter (s7e_vl hc) < η := by
  have h1 := s7e_vl_param_near hn hQ true hw hc
  simp only [contactEndpoint, ↓reduceIte] at h1
  have := (abs_lt.mp h1).2
  linarith

include huniq hsep in
omit [NeZero n] in
/-- Every visit of `Q` is the contact `a`-visit, the contact leg visit, or persistent. -/
theorem s7e_visit_cases (v : Visit Q) :
    v = s7e_va hc ∨ v = s7e_vl hc ∨ ¬ ContactAffected M a v.1.val := by
  by_cases hv : ContactAffected M a v.1.val
  · rcases s7e_visit_of_fst hc v (huniq v.1 hv) (s7e_a_ne_leg f hsep) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hv)

include huniq hsep in
omit [NeZero n] in
/-- A visit on edge `a` that is not the contact `a`-visit is persistent. -/
theorem s7e_persistent_of_edge_a (v : Visit Q) (he : v.2.val = a) (hv : v ≠ s7e_va hc) :
    ¬ ContactAffected M a v.1.val := by
  intro hva
  exact hv (s7e_visit_eq_va hc v (huniq v.1 hva) he (s7e_a_ne_leg f hsep))

include huniq hsep in
omit [NeZero n] in
/-- A visit on the leg edge that is not the contact leg visit is persistent. -/
theorem s7e_persistent_of_edge_leg (v : Visit Q) (he : v.2.val = contactLeg f M)
    (hv : v ≠ s7e_vl hc) : ¬ ContactAffected M a v.1.val := by
  intro hva
  exact hv (s7e_visit_eq_vl hc v (huniq v.1 hva) he (s7e_a_ne_leg f hsep))

include huniq in
omit [NeZero n] in
/-- A visit on an edge other than `a` and the leg is persistent. -/
theorem s7e_persistent_of_edge_ne (v : Visit Q) (ha : v.2.val ≠ a) (hl : v.2.val ≠ contactLeg f M) :
    ¬ ContactAffected M a v.1.val := by
  intro hva
  rcases s7e_edge_of_fst v (huniq v.1 hva) with h | h
  · exact ha h
  · exact hl h

include hn hQ hsep hη hw huniq in
/-- **The leg visit and the vertex `μ_M` share their owner** for every support avoiding the contact
crossing (`f = false`: `nextMark v_ℓ = μ_M`; `f = true`: `nextMark μ_M = v_ℓ`). -/
theorem s7e_owner_vl_eq_vertex (S : Finset (Crossing Q)) (hS : (s7e_va hc).1 ∉ S) :
    owner hn hQ S (Sum.inr (s7e_vl hc)) = owner hn hQ S (Sum.inl M) := by
  cases f
  · -- the leg is `M - 1`: the leg visit is the last mark on edge `M - 1`
    have hnext : nextMark hn hQ (Sum.inr (s7e_vl hc)) = Sum.inl ((s7e_vl hc).2.val + 1) := by
      apply s7e_nextMark_inr_eq_inl hn hQ
      intro u hu
      by_cases hul : u = s7e_vl hc
      · rw [hul]
      · have hup := s7e_persistent_of_edge_leg false hsep hc huniq u (hu.trans (s7e_vl_edge hc)) hul
        have h1 := s7e_persist_M_sub_one hn hQ hw u hup
          (by rw [hu, s7e_vl_edge]; simp [contactLeg])
        have h2 := s7e_vl_param_false hn hQ hw hc
        linarith
    have hM : (s7e_vl hc).2.val + 1 = M := by
      rw [s7e_vl_edge]; simp only [contactLeg, Bool.false_eq_true, ↓reduceIte]; ring
    rw [s7e_owner_inr_eq_next hn hQ S _ (by rw [s7e_vl_fst]; exact hS), hnext, hM]
  · -- the leg is `M`: the leg visit is the first mark on edge `M`
    have hnext : nextMark hn hQ (Sum.inl M) = Sum.inr (s7e_vl hc) := by
      apply s7e_nextMark_inl_eq_inr hn hQ M (s7e_vl hc)
        (by rw [s7e_vl_edge]; simp [contactLeg])
      intro u hu
      by_cases hul : u = s7e_vl hc
      · rw [hul]
      · have hup := s7e_persistent_of_edge_leg true hsep hc huniq u
          (by rw [hu]; simp [contactLeg]) hul
        have h1 := s7e_persist_M hn hQ hw u hup hu
        have h2 := s7e_vl_param_true hn hQ hw hc
        linarith
    rw [s7e_owner_inl_eq_next hn hQ S M, hnext]

include hsep huniq in
/-- The successor of the contact `a`-visit is persistent. -/
theorem s7e_nextMark_va_persistent : s7a_Persistent M a (nextMark hn hQ (Sum.inr (s7e_va hc))) := by
  rcases s7e_nextMark_inr hn hQ (s7e_va hc) with hnext | ⟨w, hnext, hwe, hwp⟩
  · rw [hnext]; trivial
  · rw [hnext]
    show ¬ ContactAffected M a w.1.val
    apply s7e_persistent_of_edge_a f hsep hc huniq w (hwe.trans (s7e_va_edge hc))
    intro hwv
    rw [hwv] at hwp
    exact lt_irrefl _ hwp

include hn hQ in
/-- If the successor of the contact `a`-visit is the vertex `a + 1`, no persistent visit on edge `a`
lies beyond the contact `a`-visit. -/
theorem s7e_no_later_of_nextMark_inl (hnext : nextMark hn hQ (Sum.inr (s7e_va hc)) = Sum.inl (a + 1))
    (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    visitParameter u < visitParameter (s7e_va hc) := by
  by_contra hle
  have hlt : visitParameter (s7e_va hc) < visitParameter u := by
    rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | heq
    · exact hlt
    · exfalso
      have := s7e_visit_eq_of_param hn hQ (s7e_va hc) u (by rw [s7e_va_edge, he]) heq
      rw [← this] at hu
      exact hu ((contactAffected_iff_leg _).mpr ⟨f, rfl⟩)
  have hb := s7e_between_mark_mark_inl hn hQ (Sum.inr (s7e_va hc)) (Sum.inr u)
    (by simp only [s7e_mEdge_inr, s7e_va_edge, he]) hlt
  simp only [s7e_mEdge_inr, s7e_va_edge] at hb
  exact nextMark_no_mark_between hn hQ hnext (Sum.inr u) hb

include hn hQ in
/-- If the successor of the contact `a`-visit is the visit `w`, then `w` is the first visit on edge
`a` beyond the contact `a`-visit. -/
theorem s7e_min_of_nextMark_inr (w : Visit Q)
    (hnext : nextMark hn hQ (Sum.inr (s7e_va hc)) = Sum.inr w) (hwe : w.2.val = a)
    (u : Visit Q) (he : u.2.val = a) (hu : visitParameter (s7e_va hc) < visitParameter u) :
    visitParameter w ≤ visitParameter u := by
  by_contra hlt
  have hb := s7e_between_same_edge hn hQ (Sum.inr (s7e_va hc)) (Sum.inr u) (Sum.inr w)
    (by simp only [s7e_mEdge_inr, s7e_va_edge, he]) (by simp only [s7e_mEdge_inr, he, hwe])
    hu (not_le.mp hlt)
  exact nextMark_no_mark_between hn hQ hnext (Sum.inr u) hb

end S7ESidePolygon

section S7ESpectator

/-! #### The spectator sector at a sliding wall (PLAN §3.3 sliding (1), sm-4:300-314): every support
of `P₋ = g.curve (g.sideTime false t)` avoiding the contact crossing `x₋` is matched with the support
of `P₊ = g.curve (g.sideTime true t)` with the same persistent crossings, and the selector-form terms
agree: decompositions correspond (U110-A), corner turns correspond (U110-A), coefficients correspond
(U110-D's record route with the RELOCATED visit map `x₋ ↦ x₊` and U110-A2's rotation equality). -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}
  (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ) (t : g.SideParameter)
  (ht : t.val < δ) (hη : 0 < η)

include hloc ht in
theorem s7e_hL : s7a_SideLocal hn g M a r η t := s7a2_sideLocal hn g hloc ht

include hloc ht in
theorem s7e_hs : ∀ s, ¬ ContactAffected M a s →
    (IsCrossing (g.curve (g.sideTime true t)) s ↔ IsCrossing (g.curve (g.sideTime false t)) s) :=
  s7a_side_hs hn g (s7e_hL hn g hloc t ht) false true

include hloc ht in
theorem s7e_hw (b : Bool) : ContactParameterWindows g.center (g.curve (g.sideTime b t)) M a r η :=
  (s7e_hL hn g hloc t ht b).windows

include hloc ht in
theorem s7e_hpar : ∀ (v w : Visit (g.curve (g.sideTime false t))) (hv : ¬ ContactAffected M a v.1.val)
    (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
    (visitParameter (s7a_visit (s7e_hs hn g hloc t ht) v hv) <
        visitParameter (s7a_visit (s7e_hs hn g hloc t ht) w hw) ↔
      visitParameter v < visitParameter w) :=
  s7a_side_hpar hn g (s7e_hL hn g hloc t ht) false true

omit [NeZero n] in
theorem s7e_hPm : Generic (g.curve (g.sideTime false t)) := s7a_sideGeneric g false

omit [NeZero n] in
theorem s7e_hPp : Generic (g.curve (g.sideTime true t)) := s7a_sideGeneric g true

include hn h in
theorem s7e_hxm : IsCrossing (g.curve (g.sideTime false t)) {a, contactLeg (s7e_leg g M a) M} :=
  (s7e_pattern hn h t).1

include hn h in
theorem s7e_hxp : IsCrossing (g.curve (g.sideTime true t)) {a, contactLeg (!s7e_leg g M a) M} :=
  (s7e_pattern hn h t).2.2.1

include hn h in
theorem s7e_hm : ∀ y : Crossing (g.curve (g.sideTime false t)),
    ContactAffected M a y.val → y = s7e_xm hn h t :=
  fun y hy => s7e_eq_xm_of_affected hn h t y hy

include hn h in
theorem s7e_hp : ∀ y : Crossing (g.curve (g.sideTime true t)),
    ContactAffected M a y.val → y = s7e_xp hn h t :=
  fun y hy => s7e_eq_xp_of_affected hn h t y hy

include hn h in
theorem s7e_huniq_m : ∀ y : Crossing (g.curve (g.sideTime false t)),
    ContactAffected M a y.val → y.val = {a, contactLeg (s7e_leg g M a) M} :=
  fun y hy => congrArg Subtype.val (s7e_eq_xm_of_affected hn h t y hy)

include hn h in
theorem s7e_huniq_p : ∀ y : Crossing (g.curve (g.sideTime true t)),
    ContactAffected M a y.val → y.val = {a, contactLeg (!s7e_leg g M a) M} :=
  fun y hy => congrArg Subtype.val (s7e_eq_xp_of_affected hn h t y hy)

include hn h in
theorem s7e_va_fst_xm : (s7e_va (s7e_hxm hn g h t)).1 = s7e_xm hn h t := rfl
include hn h in
theorem s7e_vl_fst_xm : (s7e_vl (s7e_hxm hn g h t)).1 = s7e_xm hn h t := s7e_vl_fst _
include hn h in
theorem s7e_va_fst_xp : (s7e_va (s7e_hxp hn g h t)).1 = s7e_xp hn h t := rfl
include hn h in
theorem s7e_vl_fst_xp : (s7e_vl (s7e_hxp hn g h t)).1 = s7e_xp hn h t := s7e_vl_fst _

include h hloc ht hη in
/-- **Sign constancy through the wall**: the side of `r` on which a persistent `a`-visit lies is the
same on `P₋` and `P₊` (the Cramer parameter is continuous and stays `3η` away from `r` on the whole
interval, lem:wall-sides (V) windows + `s7a2_pos_of_ne_zero`). -/
theorem s7e_sign_const (j : ZMod n) (hc : IsCrossing g.center {a, j})
    (hnot : ¬ ContactAffected M a {a, j}) :
    edgeParameter (g.curve (g.sideTime false t)) a j < r ↔
      edgeParameter (g.curve (g.sideTime true t)) a j < r := by
  have hcont : ∀ u : g.Parameter, |u.val| < δ →
      ContinuousAt (fun w : g.Parameter => edgeParameter (g.curve w) a j - r) u :=
    fun u hu => (s7a2_continuousAt_edgeParameter hn g h.1 hloc hu hc hnot).sub continuousAt_const
  have hne : ∀ u : g.Parameter, |u.val| < δ → edgeParameter (g.curve u) a j - r ≠ 0 := by
    intro u hu h0
    have hcr : IsCrossing (g.curve u) {a, j} := (s7a2_crossing_iff hn g hloc hu {a, j} hnot).mpr hc
    have hw := (hloc u hu).windows.2.1 none j hcr hnot
    simp only [contactWindowEdge, contactWindowCenter] at hw
    rw [h0, abs_zero] at hw
    linarith
  have habs : ∀ b : Bool, |(g.sideTime b t).val| ≤ t.val := fun b => le_of_eq (g.sideTime_val_abs b t)
  have hlt : ∀ b : Bool, |(g.sideTime b t).val| < δ := fun b => by rw [g.sideTime_val_abs]; exact ht
  constructor
  · intro h1
    by_contra h2
    have hpos : 0 < edgeParameter (g.curve (g.sideTime true t)) a j - r :=
      lt_of_le_of_ne (by linarith) (hne _ (hlt true)).symm
    have := s7a2_pos_of_ne_zero g ht hcont hne true hpos (g.sideTime false t) (habs false)
    linarith
  · intro h1
    by_contra h2
    have hpos : 0 < edgeParameter (g.curve (g.sideTime false t)) a j - r :=
      lt_of_le_of_ne (by linarith) (hne _ (hlt false)).symm
    have := s7a2_pos_of_ne_zero g ht hcont hne false hpos (g.sideTime true t) (habs true)
    linarith

include h hloc ht hη in
/-- Sign constancy for a persistent visit on edge `a` and its transport. -/
theorem s7e_side_a (u : Visit (g.curve (g.sideTime false t))) (hu : ¬ ContactAffected M a u.1.val)
    (he : u.2.val = a) :
    visitParameter u < r ↔ visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hu) < r := by
  obtain ⟨j, _, hj⟩ := crossing_support_partner u.1 u.2.val u.2.property
  have h1 : visitParameter u = edgeParameter (g.curve (g.sideTime false t)) a j := by
    rw [visitParameter_eq_of_support_pair hn (s7e_hPm g t).1 u j hj, he]
  have h2 : visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hu) =
      edgeParameter (g.curve (g.sideTime true t)) a j := by
    rw [visitParameter_eq_of_support_pair hn (s7e_hPp g t).1 (s7a_visit (s7e_hs hn g hloc t ht) u hu) j
      hj, s7a_visit_edge, he]
  have hj' : u.1.val = {a, j} := by rw [hj, he]
  have hnot : ¬ ContactAffected M a {a, j} := by rw [← hj']; exact hu
  have hc : IsCrossing g.center {a, j} :=
    (s7a2_crossing_iff hn g hloc (u := g.sideTime false t) (by rw [g.sideTime_val_abs]; exact ht)
      {a, j} hnot).mp
      (by rw [← hj']; exact u.1.property)
  rw [h1, h2]
  exact s7e_sign_const hn g h hloc t ht hη j hc hnot

include hn g h hloc ht in
/-- **The relocated visit map** `Visit P₋ → Visit P₊`: persistent visits by U110-A's `s7a_visit`
(same support, same edge), the two visits of `x₋` to the two visits of `x₊` (edge `a` to edge `a`,
leg to leg). -/
noncomputable def s7e_visitMap (v : Visit (g.curve (g.sideTime false t))) :
    Visit (g.curve (g.sideTime true t)) :=
  if hv : ContactAffected M a v.1.val then
    (if v.2.val = a then s7e_va (s7e_hxp hn g h t) else s7e_vl (s7e_hxp hn g h t))
  else s7a_visit (s7e_hs hn g hloc t ht) v hv

theorem s7e_visitMap_of_not (v : Visit (g.curve (g.sideTime false t)))
    (hv : ¬ ContactAffected M a v.1.val) :
    s7e_visitMap hn g h hloc t ht v = s7a_visit (s7e_hs hn g hloc t ht) v hv :=
  dite_eq_right hv

theorem s7e_visitMap_va :
    s7e_visitMap hn g h hloc t ht (s7e_va (s7e_hxm hn g h t)) = s7e_va (s7e_hxp hn g h t) := by
  unfold s7e_visitMap
  rw [dite_eq_left (show ContactAffected M a (s7e_va (s7e_hxm hn g h t)).1.val from
    s7e_xm_affected hn h t), ite_eq_left (s7e_va_edge _)]

theorem s7e_visitMap_vl :
    s7e_visitMap hn g h hloc t ht (s7e_vl (s7e_hxm hn g h t)) = s7e_vl (s7e_hxp hn g h t) := by
  unfold s7e_visitMap
  have hne : (s7e_vl (s7e_hxm hn g h t)).2.val ≠ a := by
    rw [s7e_vl_edge]; exact (s7e_a_ne_leg _ h.1.1).symm
  rw [dite_eq_left (by rw [s7e_vl_fst_xm]; exact s7e_xm_affected hn h t), ite_eq_right hne]

theorem s7e_visitMap_affected (v : Visit (g.curve (g.sideTime false t)))
    (hv : ContactAffected M a v.1.val) :
    ContactAffected M a (s7e_visitMap hn g h hloc t ht v).1.val := by
  unfold s7e_visitMap
  rw [dite_eq_left hv]
  split_ifs
  · exact s7e_xp_affected hn h t
  · rw [s7e_vl_fst_xp]; exact s7e_xp_affected hn h t

/-- The support bijection of the wall (`Finset.map` along `s7e_crossEquiv`). -/
noncomputable def s7e_E : Finset (Crossing (g.curve (g.sideTime false t))) ≃
    Finset (Crossing (g.curve (g.sideTime true t))) :=
  s7e_supportEquiv (s7e_hs hn g hloc t ht) (s7e_xm hn h t) (s7e_xp hn h t) (s7e_hm hn g h t)
    (s7e_hp hn g h t) (s7e_xm_affected hn h t) (s7e_xp_affected hn h t)

theorem s7e_E_hSS' (S : Finset (Crossing (g.curve (g.sideTime false t)))) :
    ∀ (v : Visit (g.curve (g.sideTime false t))) (hv : ¬ ContactAffected M a v.1.val),
      (s7a_visit (s7e_hs hn g hloc t ht) v hv).1 ∈ s7e_E hn g h hloc t ht S ↔ v.1 ∈ S :=
  s7e_supportEquiv_hSS' _ _ _ _ _ _ _ S

include hn h in
theorem s7e_E_hSp (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    ∀ x ∈ S, ¬ ContactAffected M a x.val :=
  s7e_persistent_of_not_mem _ (s7e_hm hn g h t) S hS

theorem s7e_E_hSp' (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    ∀ y ∈ s7e_E hn g h hloc t ht S, ¬ ContactAffected M a y.val :=
  s7e_supportEquiv_persistent _ _ _ _ _ _ _ S hS

theorem s7e_xp_mem_E (S : Finset (Crossing (g.curve (g.sideTime false t)))) :
    s7e_xp hn h t ∈ s7e_E hn g h hloc t ht S ↔ s7e_xm hn h t ∈ S :=
  s7e_xp_mem_supportEquiv _ _ _ _ _ _ _ S

theorem s7e_xp_notMem_E (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    s7e_xp hn h t ∉ s7e_E hn g h hloc t ht S := by
  rw [s7e_xp_mem_E]; exact hS

/-- The carrier bijection of a persistent support (U110-A's `s7a_sideComponentEquiv`). -/
noncomputable def s7e_e (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    Component hn (s7e_hPm g t) S ≃ Component hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) :=
  s7a_sideComponentEquiv hn g (s7e_hL hn g hloc t ht) false true S (s7e_E hn g h hloc t ht S)
    (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS) (s7e_E_hSp' hn g h hloc t ht S hS)

theorem s7e_e_owner (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (m : Mark (g.curve (g.sideTime false t))) (hm : s7a_Persistent M a m) :
    s7e_e hn g h hloc t ht S hS (owner hn (s7e_hPm g t) S m) =
      owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (s7a_markMap (s7e_hs hn g hloc t ht) m) :=
  s7a_sideComponentEquiv_owner hn g _ false true S _ _ _ _ m hm

include hloc ht hη in
/-- The leg visit of `x₋` and the vertex `μ_M` share their owner on `P₋`. -/
theorem s7e_owner_vl_m (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    owner hn (s7e_hPm g t) S (Sum.inr (s7e_vl (s7e_hxm hn g h t))) = owner hn (s7e_hPm g t) S (Sum.inl M) :=
  s7e_owner_vl_eq_vertex hn (s7e_hPm g t) (s7e_leg g M a) h.1.1 hη (s7e_hw hn g hloc t ht false)
    (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) S hS

include hloc ht hη in
/-- The leg visit of `x₊` and the vertex `μ_M` share their owner on `P₊`. -/
theorem s7e_owner_vl_p (S' : Finset (Crossing (g.curve (g.sideTime true t)))) (hS' : s7e_xp hn h t ∉ S') :
    owner hn (s7e_hPp g t) S' (Sum.inr (s7e_vl (s7e_hxp hn g h t))) = owner hn (s7e_hPp g t) S' (Sum.inl M) :=
  s7e_owner_vl_eq_vertex hn (s7e_hPp g t) (!s7e_leg g M a) h.1.1 hη (s7e_hw hn g hloc t ht true)
    (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) S' hS'

include hloc ht hη in
/-- **The successor of the contact `a`-visit is transported**: `nextMark (inr w_a) = markMap (nextMark
(inr v_a))` — the first persistent mark after the contact `a`-visit is the same on both sides (same
edge, same side of `r` by sign constancy, same order of persistent visits). -/
theorem s7e_nextMark_wa :
    nextMark hn (s7e_hPp g t) (Sum.inr (s7e_va (s7e_hxp hn g h t))) =
      s7a_markMap (s7e_hs hn g hloc t ht) (nextMark hn (s7e_hPm g t) (Sum.inr (s7e_va (s7e_hxm hn g h t)))) := by
  have hpers := s7e_nextMark_va_persistent hn (s7e_hPm g t) (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t)
    (s7e_huniq_m hn g h t)
  have hva := s7e_va_param_near hn (s7e_hPm g t) (s7e_leg g M a) (s7e_hw hn g hloc t ht false) (s7e_hxm hn g h t)
  have hwa := s7e_va_param_near hn (s7e_hPp g t) (!s7e_leg g M a) (s7e_hw hn g hloc t ht true) (s7e_hxp hn g h t)
  have hva1 := (abs_lt.mp hva).1
  have hva2 := (abs_lt.mp hva).2
  have hwa1 := (abs_lt.mp hwa).1
  have hwa2 := (abs_lt.mp hwa).2
  rcases s7e_nextMark_inr hn (s7e_hPm g t) (s7e_va (s7e_hxm hn g h t)) with hnext | ⟨u, hnext, hue, hup⟩
  · -- the successor is the vertex `a + 1`
    have hnext' : nextMark hn (s7e_hPm g t) (Sum.inr (s7e_va (s7e_hxm hn g h t))) = Sum.inl (a + 1) := hnext
    rw [hnext', s7a_markMap_inl]
    apply s7e_nextMark_inr_eq_inl hn (s7e_hPp g t)
    intro u' hu'e
    by_cases hu'a : u' = s7e_va (s7e_hxp hn g h t)
    · rw [hu'a]
    · have hu'p : ¬ ContactAffected M a u'.1.val :=
        s7e_persistent_of_edge_a (!s7e_leg g M a) h.1.1 (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) u' hu'e hu'a
      obtain ⟨u, hu, rfl⟩ := s7a_visit_surjective (s7e_hs hn g hloc t ht) u' hu'p
      have hue : u.2.val = a := hu'e
      have hlt := s7e_no_later_of_nextMark_inl hn (s7e_hPm g t) (s7e_leg g M a) (s7e_hxm hn g h t) hnext' u hu hue
      have hu3 := s7e_persist_a hn (s7e_hPm g t) (s7e_hw hn g hloc t ht false) u hu hue
      have hur : visitParameter u < r := by
        by_contra hge
        rw [abs_of_nonneg (by linarith)] at hu3
        linarith
      have hur' := (s7e_side_a hn g h hloc t ht hη u hu hue).mp hur
      have hu3' := s7e_persist_a hn (s7e_hPp g t) (s7e_hw hn g hloc t ht true)
        (s7a_visit (s7e_hs hn g hloc t ht) u hu) hu hue
      rw [abs_of_neg (by linarith)] at hu3'
      linarith
  · -- the successor is a later visit `u` on edge `a`
    have hupers : ¬ ContactAffected M a u.1.val := by
      have := hpers; rw [hnext] at this; exact this
    have hue' : u.2.val = a := hue
    rw [hnext, s7a_markMap_inr _ u hupers]
    have hu3 := s7e_persist_a hn (s7e_hPm g t) (s7e_hw hn g hloc t ht false) u hupers hue'
    have hur : r < visitParameter u := by
      by_contra hge
      rw [abs_of_nonpos (by linarith)] at hu3
      linarith
    have hur'le : r ≤ visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hupers) :=
      not_lt.mp (fun hlt => not_lt.mpr hur.le ((s7e_side_a hn g h hloc t ht hη u hupers hue').mpr hlt))
    have hu3' := s7e_persist_a hn (s7e_hPp g t) (s7e_hw hn g hloc t ht true)
      (s7a_visit (s7e_hs hn g hloc t ht) u hupers) hupers hue'
    have hur' : r < visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hupers) :=
      lt_of_le_of_ne hur'le (fun heq => by rw [← heq, sub_self, abs_zero] at hu3'; linarith)
    rw [abs_of_pos (by linarith)] at hu3'
    apply s7e_nextMark_inr_eq_inr hn (s7e_hPp g t) (s7e_va (s7e_hxp hn g h t))
      (s7a_visit (s7e_hs hn g hloc t ht) u hupers) hue' (by linarith)
    intro u₂' he₂ hlt₂
    by_cases h₂a : u₂' = s7e_va (s7e_hxp hn g h t)
    · exfalso; rw [h₂a] at hlt₂; exact lt_irrefl _ hlt₂
    · have h₂p : ¬ ContactAffected M a u₂'.1.val :=
        s7e_persistent_of_edge_a (!s7e_leg g M a) h.1.1 (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) u₂' he₂ h₂a
      obtain ⟨u₂, hu₂, rfl⟩ := s7a_visit_surjective (s7e_hs hn g hloc t ht) u₂' h₂p
      have he₂' : u₂.2.val = a := he₂
      have h₂3 := s7e_persist_a hn (s7e_hPp g t) (s7e_hw hn g hloc t ht true)
        (s7a_visit (s7e_hs hn g hloc t ht) u₂ hu₂) hu₂ he₂'
      have h₂r : r < visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u₂ hu₂) := by
        by_contra hge
        rw [abs_of_nonpos (by linarith)] at h₂3
        linarith
      have h₂r'le : r ≤ visitParameter u₂ :=
        not_lt.mp (fun hlt => not_lt.mpr h₂r.le ((s7e_side_a hn g h hloc t ht hη u₂ hu₂ he₂').mp hlt))
      have h₂3m := s7e_persist_a hn (s7e_hPm g t) (s7e_hw hn g hloc t ht false) u₂ hu₂ he₂'
      have h₂r' : r < visitParameter u₂ :=
        lt_of_le_of_ne h₂r'le (fun heq => by rw [← heq, sub_self, abs_zero] at h₂3m; linarith)
      rw [abs_of_pos (by linarith)] at h₂3m
      have hle : visitParameter u ≤ visitParameter u₂ :=
        s7e_min_of_nextMark_inr hn (s7e_hPm g t) (s7e_leg g M a) (s7e_hxm hn g h t) u hnext hue' u₂ he₂'
          (by linarith)
      exact not_lt.mp (fun hlt' => not_lt.mpr hle
        ((s7e_hpar hn g hloc t ht u₂ u hu₂ hupers (he₂'.trans hue'.symm)).mp hlt'))

include hloc ht hη in
/-- **The contact crossing is a self-crossing of `q` iff `x₊` is one of `e q`** (the two contact
visits are owned, through their successors, by the same persistent marks on both sides). -/
theorem s7e_xm_mem_iff (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (q : Component hn (s7e_hPm g t) S) :
    s7e_xm hn h t ∈ carrierCrossings hn (s7e_hPm g t) S q ↔
      s7e_xp hn h t ∈ carrierCrossings hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S)
        (s7e_e hn g h hloc t ht S hS q) := by
  have hS' := s7e_xp_notMem_E hn g h hloc t ht S hS
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hm_iff : (∀ v : Visit (g.curve (g.sideTime false t)), v.1 = s7e_xm hn h t →
      owner hn (s7e_hPm g t) S (Sum.inr v) = q) ↔
      (owner hn (s7e_hPm g t) S (Sum.inr (s7e_va (s7e_hxm hn g h t))) = q ∧
        owner hn (s7e_hPm g t) S (Sum.inr (s7e_vl (s7e_hxm hn g h t))) = q) := by
    constructor
    · intro hall
      exact ⟨hall _ (s7e_va_fst_xm hn g h t), hall _ (s7e_vl_fst_xm hn g h t)⟩
    · rintro ⟨h1, h2⟩ v hv
      rcases s7e_visit_of_fst (s7e_hxm hn g h t) v (congrArg Subtype.val hv)
        (s7e_a_ne_leg _ h.1.1) with rfl | rfl
      · exact h1
      · exact h2
  have hp_iff : (∀ v : Visit (g.curve (g.sideTime true t)), v.1 = s7e_xp hn h t →
      owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (Sum.inr v) = s7e_e hn g h hloc t ht S hS q) ↔
      (owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (Sum.inr (s7e_va (s7e_hxp hn g h t))) =
          s7e_e hn g h hloc t ht S hS q ∧
        owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (Sum.inr (s7e_vl (s7e_hxp hn g h t))) =
          s7e_e hn g h hloc t ht S hS q) := by
    constructor
    · intro hall
      exact ⟨hall _ (s7e_va_fst_xp hn g h t), hall _ (s7e_vl_fst_xp hn g h t)⟩
    · rintro ⟨h1, h2⟩ v hv
      rcases s7e_visit_of_fst (s7e_hxp hn g h t) v (congrArg Subtype.val hv)
        (s7e_a_ne_leg _ h.1.1) with rfl | rfl
      · exact h1
      · exact h2
  rw [hm_iff, hp_iff]
  have o1 : owner hn (s7e_hPm g t) S (Sum.inr (s7e_va (s7e_hxm hn g h t))) =
      owner hn (s7e_hPm g t) S (nextMark hn (s7e_hPm g t) (Sum.inr (s7e_va (s7e_hxm hn g h t)))) :=
    s7e_owner_inr_eq_next hn (s7e_hPm g t) S _ (by rw [s7e_va_fst_xm]; exact hS)
  have o2 := s7e_owner_vl_m hn g h hloc t ht hη S hS
  have o1' : owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (Sum.inr (s7e_va (s7e_hxp hn g h t))) =
      owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S)
        (nextMark hn (s7e_hPp g t) (Sum.inr (s7e_va (s7e_hxp hn g h t)))) :=
    s7e_owner_inr_eq_next hn (s7e_hPp g t) _ _ (by rw [s7e_va_fst_xp]; exact hS')
  have o2' := s7e_owner_vl_p hn g h hloc t ht hη (s7e_E hn g h hloc t ht S) hS'
  rw [o1, o2, o1', o2', s7e_nextMark_wa hn g h hloc t ht hη]
  have hpers := s7e_nextMark_va_persistent hn (s7e_hPm g t) (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t)
    (s7e_huniq_m hn g h t)
  have e1 := s7e_e_owner hn g h hloc t ht S hS _ hpers
  have e2 := s7e_e_owner hn g h hloc t ht S hS (Sum.inl M) trivial
  rw [s7a_markMap_inl] at e2
  rw [← e1, ← e2, Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq]
  exact and_congr_left (fun _ => iff_of_true hS hS')

include hloc ht hη in
/-- **`hmem` of U110-D for the relocated visit map**: the visits of the carrier crossings of `e q`
are exactly the images of the visits of the carrier crossings of `q`. -/
theorem s7e_hmem (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (q : Component hn (s7e_hPm g t) S) :
    ∀ w : Visit (g.curve (g.sideTime true t)),
      w.1 ∈ carrierCrossings hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (s7e_e hn g h hloc t ht S hS q) ↔
        ∃ v : Visit (g.curve (g.sideTime false t)), v.1 ∈ carrierCrossings hn (s7e_hPm g t) S q ∧
          s7e_visitMap hn g h hloc t ht v = w := by
  intro w
  by_cases hw : ContactAffected M a w.1.val
  · have hw1 : w.1 = s7e_xp hn h t := s7e_eq_xp_of_affected hn h t w.1 hw
    rw [hw1, ← s7e_xm_mem_iff hn g h hloc t ht hη S hS q]
    constructor
    · intro hx
      rcases s7e_visit_of_fst (s7e_hxp hn g h t) w (congrArg Subtype.val hw1)
        (s7e_a_ne_leg _ h.1.1) with rfl | rfl
      · exact ⟨s7e_va (s7e_hxm hn g h t), by rw [s7e_va_fst_xm]; exact hx, s7e_visitMap_va hn g h hloc t ht⟩
      · exact ⟨s7e_vl (s7e_hxm hn g h t), by rw [s7e_vl_fst_xm]; exact hx, s7e_visitMap_vl hn g h hloc t ht⟩
    · rintro ⟨v, hv, rfl⟩
      by_cases hva : ContactAffected M a v.1.val
      · rw [s7e_eq_xm_of_affected hn h t v.1 hva] at hv; exact hv
      · exfalso
        rw [s7e_visitMap_of_not hn g h hloc t ht v hva] at hw
        exact hva hw
  · obtain ⟨v, hv, rfl⟩ := s7a_visit_surjective (s7e_hs hn g hloc t ht) w hw
    have hiff := s7a_side_mem_carrierCrossings hn g (s7e_hL hn g hloc t ht) false true S
      (s7e_E hn g h hloc t ht S) (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS)
      (s7e_E_hSp' hn g h hloc t ht S hS) v.1 hv q
    constructor
    · intro hx
      exact ⟨v, hiff.mp hx, s7e_visitMap_of_not hn g h hloc t ht v hv⟩
    · rintro ⟨v', hv', hφ⟩
      by_cases hv'a : ContactAffected M a v'.1.val
      · exfalso
        have := s7e_visitMap_affected hn g h hloc t ht v' hv'a
        rw [hφ] at this
        exact hw this
      · rw [s7e_visitMap_of_not hn g h hloc t ht v' hv'a] at hφ
        have := s7a_visit_injective _ v' v hv'a hv hφ
        subst this
        exact hiff.mpr hv'

end S7ESpectator

section S7EKeys

/-! #### The key order of the visits of a side polygon relative to its two contact visits (generic
side polygon `Q` with contact crossing `{a, contactLeg f M}` and the parameter windows). -/

variable (hn : 3 ≤ n) {C Q : LabelledTuple n} (hQ : Generic Q) {M a : ZMod n} {r η : ℝ} (f : Bool)
  (hsep : ContactSeparated M a) (hη : 0 < η) (hw : ContactParameterWindows C Q M a r η)
  (hc : IsCrossing Q {a, contactLeg f M})
  (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg f M})

omit [NeZero n] in
/-- The visit key of `CB.cg` is the mark key. -/
theorem s7e_gkey (v : Visit Q) : geometricVisitKey (CB.cg hn hQ) v = markKey hn hQ.1 (Sum.inr v) := rfl

include hn hQ hη hw in
/-- A persistent `a`-visit is before the contact `a`-visit iff its parameter is below `r`. -/
theorem s7e_param_lt_va_iff (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    visitParameter u < visitParameter (s7e_va hc) ↔ visitParameter u < r := by
  have h1 := s7e_persist_a hn hQ hw u hu he
  have h2 := abs_lt.mp (s7e_va_param_near hn hQ f hw hc)
  constructor
  · intro hlt
    by_contra hge
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  · intro hlt
    rw [abs_of_neg (by linarith)] at h1
    linarith

include hn hQ hη hw in
/-- A persistent `a`-visit is after the contact `a`-visit iff its parameter is above `r`. -/
theorem s7e_va_lt_param_iff (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    visitParameter (s7e_va hc) < visitParameter u ↔ r < visitParameter u := by
  have h1 := s7e_persist_a hn hQ hw u hu he
  have h2 := abs_lt.mp (s7e_va_param_near hn hQ f hw hc)
  constructor
  · intro hlt
    by_contra hge
    rw [abs_of_nonpos (by linarith)] at h1
    linarith
  · intro hlt
    rw [abs_of_pos (by linarith)] at h1
    linarith

include hn hQ hsep hη hw huniq in
/-- Leg `M − 1`: a visit is before the leg visit iff its edge label is at most `M − 1`. -/
theorem s7e_key_lt_vl_false (hf : f = false) (u : Visit Q) (hu : u ≠ s7e_vl hc) :
    markKey hn hQ.1 (Sum.inr u) < markKey hn hQ.1 (Sum.inr (s7e_vl hc)) ↔ u.2.val.val ≤ (M - 1).val := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M - 1 := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_lt_iff hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr, hℓ]
  constructor
  · rintro (h1 | ⟨h1, _⟩)
    · exact h1.le
    · rw [h1]
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · right
      have he : u.2.val = M - 1 := ZMod.val_injective n heq
      refine ⟨he, ?_⟩
      have hup := s7e_persistent_of_edge_leg false hsep hc huniq u (by rw [he]; rfl) hu
      have h1 := s7e_persist_M_sub_one hn hQ hw u hup he
      have h2 := s7e_vl_param_false hn hQ hw hc
      linarith

include hn hQ hsep hη hw huniq in
/-- Leg `M − 1`: a visit is after the leg visit iff its edge label exceeds `M − 1`. -/
theorem s7e_vl_lt_key_false (hf : f = false) (u : Visit Q) (hu : u ≠ s7e_vl hc) :
    markKey hn hQ.1 (Sum.inr (s7e_vl hc)) < markKey hn hQ.1 (Sum.inr u) ↔ (M - 1).val < u.2.val.val := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M - 1 := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_lt_iff hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr, hℓ]
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact h1
    · exfalso
      have hup := s7e_persistent_of_edge_leg false hsep hc huniq u (by rw [← h1]; rfl) hu
      have h3 := s7e_persist_M_sub_one hn hQ hw u hup h1.symm
      have h4 := s7e_vl_param_false hn hQ hw hc
      linarith
  · intro hlt
    exact Or.inl hlt

include hn hQ hsep hη hw huniq in
/-- Leg `M`: a visit is before the leg visit iff its edge label is below `M`. -/
theorem s7e_key_lt_vl_true (hf : f = true) (u : Visit Q) (hu : u ≠ s7e_vl hc) :
    markKey hn hQ.1 (Sum.inr u) < markKey hn hQ.1 (Sum.inr (s7e_vl hc)) ↔ u.2.val.val < M.val := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_lt_iff hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr, hℓ]
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact h1
    · exfalso
      have hup := s7e_persistent_of_edge_leg true hsep hc huniq u (by rw [h1]; rfl) hu
      have h3 := s7e_persist_M hn hQ hw u hup h1
      have h4 := s7e_vl_param_true hn hQ hw hc
      linarith
  · intro hlt
    exact Or.inl hlt

include hn hQ hsep hη hw huniq in
/-- Leg `M`: a visit is after the leg visit iff its edge label is at least `M`. -/
theorem s7e_vl_lt_key_true (hf : f = true) (u : Visit Q) (hu : u ≠ s7e_vl hc) :
    markKey hn hQ.1 (Sum.inr (s7e_vl hc)) < markKey hn hQ.1 (Sum.inr u) ↔ M.val ≤ u.2.val.val := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_lt_iff hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr, hℓ]
  constructor
  · rintro (h1 | ⟨h1, _⟩)
    · exact h1.le
    · rw [h1]
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · right
      have he : u.2.val = M := ZMod.val_injective n heq.symm
      refine ⟨he.symm, ?_⟩
      have hup := s7e_persistent_of_edge_leg true hsep hc huniq u (by rw [he]; rfl) hu
      have h1 := s7e_persist_M hn hQ hw u hup he
      have h2 := s7e_vl_param_true hn hQ hw hc
      linarith

include hn hQ hw in
/-- Leg `M = 0`: the leg visit has key below `η`. -/
theorem s7e_key_vl_lt_eta (hf : f = true) (hM : M = 0) :
    markKey hn hQ.1 (Sum.inr (s7e_vl hc)) < η := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_eq hn hQ]
  have h0 : (s7e_mEdge (Sum.inr (s7e_vl hc))).val = 0 := by
    rw [s7e_mEdge_inr, hℓ, hM, ZMod.val_zero]
  rw [h0, Nat.cast_zero, zero_add, s7e_mParam_inr]
  exact s7e_vl_param_true hn hQ hw hc

include hn hQ hsep hη hw huniq in
/-- Leg `M = 0`: every other visit has key at least `η`. -/
theorem s7e_eta_le_key (hf : f = true) (hM : M = 0) (hηr : 4 * η < r) (hr1 : r < 1) (u : Visit Q)
    (hu : u ≠ s7e_vl hc) : η ≤ markKey hn hQ.1 (Sum.inr u) := by
  subst hf
  rw [s7e_markKey_eq hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr]
  have hp0 := s7e_visitParameter_pos hn hQ u
  by_cases he : u.2.val = M
  · have hup := s7e_persistent_of_edge_leg true hsep hc huniq u (by rw [he]; rfl) hu
    have h1 := s7e_persist_M hn hQ hw u hup he
    have h2 : (0 : ℝ) ≤ u.2.val.val := Nat.cast_nonneg _
    linarith
  · have hne : u.2.val.val ≠ 0 := by
      intro h0
      exact he ((ZMod.val_eq_zero _).mp h0 ▸ hM.symm)
    have h1 : (1 : ℝ) ≤ u.2.val.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    linarith

end S7EKeys

section S7ESpectatorKeys

/-! #### The relocated visit map is key-monotone up to the leg visit; the coefficient, selector and
term equalities of the spectator sector; the sector itself. -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}
  (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ) (t : g.SideParameter)
  (ht : t.val < δ) (hη : 0 < η)

include h hloc ht hη in
theorem s7e_side_a_gt (u : Visit (g.curve (g.sideTime false t))) (hu : ¬ ContactAffected M a u.1.val)
    (he : u.2.val = a) :
    r < visitParameter u ↔ r < visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hu) := by
  have h1 := s7e_persist_a hn (s7e_hPm g t) (s7e_hw hn g hloc t ht false) u hu he
  have h2 := s7e_persist_a hn (s7e_hPp g t) (s7e_hw hn g hloc t ht true)
    (s7a_visit (s7e_hs hn g hloc t ht) u hu) hu he
  have hiff := s7e_side_a hn g h hloc t ht hη u hu he
  constructor
  · intro hlt
    have hle : r ≤ visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hu) :=
      not_lt.mp (fun hlt' => not_lt.mpr hlt.le (hiff.mpr hlt'))
    exact lt_of_le_of_ne hle (fun heq => by rw [← heq, sub_self, abs_zero] at h2; linarith)
  · intro hlt
    have hle : r ≤ visitParameter u := not_lt.mp (fun hlt' => not_lt.mpr hlt.le (hiff.mp hlt'))
    exact lt_of_le_of_ne hle (fun heq => by rw [← heq, sub_self, abs_zero] at h1; linarith)

theorem s7e_visitMap_edge (v : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    (s7e_visitMap hn g h hloc t ht v).2.val = v.2.val := by
  rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
    rfl | rfl | hp
  · rw [s7e_visitMap_va, s7e_va_edge, s7e_va_edge]
  · exact absurd rfl hv
  · rw [s7e_visitMap_of_not hn g h hloc t ht v hp]; rfl

theorem s7e_visitMap_ne_wl (v : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    s7e_visitMap hn g h hloc t ht v ≠ s7e_vl (s7e_hxp hn g h t) := by
  rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
    rfl | rfl | hp
  · rw [s7e_visitMap_va]
    exact (s7e_vl_ne_va _ (s7e_a_ne_leg _ h.1.1)).symm
  · exact absurd rfl hv
  · rw [s7e_visitMap_of_not hn g h hloc t ht v hp]
    intro heq
    have : ContactAffected M a (s7a_visit (s7e_hs hn g hloc t ht) v hp).1.val := by
      rw [heq, s7e_vl_fst_xp]; exact s7e_xp_affected hn h t
    exact hp this

include hη in
/-- Key monotonicity of the relocated visit map on the visits other than the leg visit. -/
theorem s7e_key_nonleg (v w : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t))
    (hw : w ≠ s7e_vl (s7e_hxm hn g h t))
    (hlt : geometricVisitKey (CB.cg hn (s7e_hPm g t)) v < geometricVisitKey (CB.cg hn (s7e_hPm g t)) w) :
    geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v) <
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht w) := by
  rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_markKey_lt_iff hn (s7e_hPm g t)] at hlt
  rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_markKey_lt_iff hn (s7e_hPp g t)]
  simp only [s7e_mEdge_inr, s7e_mParam_inr] at hlt ⊢
  rw [s7e_visitMap_edge hn g h hloc t ht v hv, s7e_visitMap_edge hn g h hloc t ht w hw]
  rcases hlt with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · right
    refine ⟨h1, ?_⟩
    have hwm := s7e_hw hn g hloc t ht false
    have hwp := s7e_hw hn g hloc t ht true
    rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
      rfl | rfl | hvp
    · rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) w with
        rfl | rfl | hwp'
      · exact absurd h2 (lt_irrefl _)
      · exact absurd rfl hw
      · rw [s7e_visitMap_va, s7e_visitMap_of_not hn g h hloc t ht w hwp']
        have hwe : w.2.val = a := h1.symm
        have h3 := (s7e_va_lt_param_iff hn (s7e_hPm g t) (s7e_leg g M a) hη hwm (s7e_hxm hn g h t)
          w hwp' hwe).mp h2
        have h4 := (s7e_side_a_gt hn g h hloc t ht hη w hwp' hwe).mp h3
        exact (s7e_va_lt_param_iff hn (s7e_hPp g t) (!s7e_leg g M a) hη hwp (s7e_hxp hn g h t)
          (s7a_visit (s7e_hs hn g hloc t ht) w hwp') hwp' hwe).mpr h4
    · exact absurd rfl hv
    · rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) w with
        rfl | rfl | hwp'
      · rw [s7e_visitMap_of_not hn g h hloc t ht v hvp, s7e_visitMap_va]
        have hve : v.2.val = a := h1
        have h3 := (s7e_param_lt_va_iff hn (s7e_hPm g t) (s7e_leg g M a) hη hwm (s7e_hxm hn g h t)
          v hvp hve).mp h2
        have h4 := (s7e_side_a hn g h hloc t ht hη v hvp hve).mp h3
        exact (s7e_param_lt_va_iff hn (s7e_hPp g t) (!s7e_leg g M a) hη hwp (s7e_hxp hn g h t)
          (s7a_visit (s7e_hs hn g hloc t ht) v hvp) hvp hve).mpr h4
      · exact absurd rfl hw
      · rw [s7e_visitMap_of_not hn g h hloc t ht v hvp, s7e_visitMap_of_not hn g h hloc t ht w hwp']
        exact (s7e_hpar hn g hloc t ht v w hvp hwp' h1).mpr h2

include hη in
/-- `M ≠ 0`: the leg visit is relocated without wrapping the key order. -/
theorem s7e_key_leg_ne (hM : M ≠ 0) (v : Visit (g.curve (g.sideTime false t)))
    (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    (geometricVisitKey (CB.cg hn (s7e_hPm g t)) v <
        geometricVisitKey (CB.cg hn (s7e_hPm g t)) (s7e_vl (s7e_hxm hn g h t)) →
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v) <
        geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_vl (s7e_hxp hn g h t))) ∧
    (geometricVisitKey (CB.cg hn (s7e_hPm g t)) (s7e_vl (s7e_hxm hn g h t)) <
        geometricVisitKey (CB.cg hn (s7e_hPm g t)) v →
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_vl (s7e_hxp hn g h t)) <
        geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v)) := by
  have hM1 : (M - 1).val + 1 = M.val := by
    have hne : M - 1 ≠ -1 := fun h' => hM (by linear_combination h')
    have := zmod_val_next_of_ne_last hne
    rw [sub_add_cancel] at this
    exact this.symm
  have hφe := s7e_visitMap_edge hn g h hloc t ht v hv
  have hφne := s7e_visitMap_ne_wl hn g h hloc t ht v hv
  have hwm := s7e_hw hn g hloc t ht false
  have hwp := s7e_hw hn g hloc t ht true
  have hsep := h.1.1
  rcases Bool.eq_false_or_eq_true (s7e_leg g M a) with hf | hf
  · have hf' : (!s7e_leg g M a) = false := by rw [hf]; rfl
    constructor
    · intro hlt
      rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_key_lt_vl_true hn (s7e_hPm g t) _ hsep hη hwm (s7e_hxm hn g h t)
        (s7e_huniq_m hn g h t) hf v hv] at hlt
      rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_key_lt_vl_false hn (s7e_hPp g t) _ hsep hη hwp (s7e_hxp hn g h t)
        (s7e_huniq_p hn g h t) hf' _ hφne, hφe]
      omega
    · intro hlt
      rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_vl_lt_key_true hn (s7e_hPm g t) _ hsep hη hwm (s7e_hxm hn g h t)
        (s7e_huniq_m hn g h t) hf v hv] at hlt
      rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_vl_lt_key_false hn (s7e_hPp g t) _ hsep hη hwp (s7e_hxp hn g h t)
        (s7e_huniq_p hn g h t) hf' _ hφne, hφe]
      omega
  · have hf' : (!s7e_leg g M a) = true := by rw [hf]; rfl
    constructor
    · intro hlt
      rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_key_lt_vl_false hn (s7e_hPm g t) _ hsep hη hwm (s7e_hxm hn g h t)
        (s7e_huniq_m hn g h t) hf v hv] at hlt
      rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_key_lt_vl_true hn (s7e_hPp g t) _ hsep hη hwp (s7e_hxp hn g h t)
        (s7e_huniq_p hn g h t) hf' _ hφne, hφe]
      omega
    · intro hlt
      rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_vl_lt_key_false hn (s7e_hPm g t) _ hsep hη hwm (s7e_hxm hn g h t)
        (s7e_huniq_m hn g h t) hf v hv] at hlt
      rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_vl_lt_key_true hn (s7e_hPp g t) _ hsep hη hwp (s7e_hxp hn g h t)
        (s7e_huniq_p hn g h t) hf' _ hφne, hφe]
      omega

include hη in
/-- `M = 0`, leg `M − 1 = −1` on `P₋`: the leg visit is the LAST visit and its image the FIRST. -/
theorem s7e_key_leg_zero_false (hM : M = 0) (hf : s7e_leg g M a = false)
    (v : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    geometricVisitKey (CB.cg hn (s7e_hPm g t)) v <
        geometricVisitKey (CB.cg hn (s7e_hPm g t)) (s7e_vl (s7e_hxm hn g h t)) ∧
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_vl (s7e_hxp hn g h t)) <
        geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v) := by
  have hM1 : (M - 1).val = n - 1 := by
    rw [hM, zero_sub]
    have := last_index_val_succ (n := n)
    omega
  have hφe := s7e_visitMap_edge hn g h hloc t ht v hv
  have hφne := s7e_visitMap_ne_wl hn g h hloc t ht v hv
  have hf' : (!s7e_leg g M a) = true := by rw [hf]; rfl
  constructor
  · rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_key_lt_vl_false hn (s7e_hPm g t) _ h.1.1 hη (s7e_hw hn g hloc t ht false)
      (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) hf v hv, hM1]
    have := ZMod.val_lt v.2.val
    omega
  · have hM0 : M.val = 0 := by rw [hM, ZMod.val_zero]
    rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_vl_lt_key_true hn (s7e_hPp g t) _ h.1.1 hη (s7e_hw hn g hloc t ht true)
      (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) hf' _ hφne, hM0]
    exact Nat.zero_le _

include hloc ht in
/-- `M = 0`, leg `M = 0` on `P₋`: the leg visit has key below `η`. -/
theorem s7e_key_vl_lt_eta_wall (hM : M = 0) (hf : s7e_leg g M a = true) :
    geometricVisitKey (CB.cg hn (s7e_hPm g t)) (s7e_vl (s7e_hxm hn g h t)) < η :=
  s7e_key_vl_lt_eta hn (s7e_hPm g t) _ (s7e_hw hn g hloc t ht false) (s7e_hxm hn g h t) hf hM

include hη in
/-- `M = 0`, leg `M = 0` on `P₋`: every other visit has key at least `η`, and its image precedes the
relocated leg visit (which is the LAST visit of `P₊`). -/
theorem s7e_key_leg_zero_true (hM : M = 0) (hf : s7e_leg g M a = true) (hηr : 4 * η < r) (hr1 : r < 1)
    (v : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    η ≤ geometricVisitKey (CB.cg hn (s7e_hPm g t)) v ∧
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v) <
        geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_vl (s7e_hxp hn g h t)) := by
  have hM1 : (M - 1).val = n - 1 := by
    rw [hM, zero_sub]
    have := last_index_val_succ (n := n)
    omega
  have hφe := s7e_visitMap_edge hn g h hloc t ht v hv
  have hφne := s7e_visitMap_ne_wl hn g h hloc t ht v hv
  have hf' : (!s7e_leg g M a) = false := by rw [hf]; rfl
  refine ⟨s7e_eta_le_key hn (s7e_hPm g t) _ h.1.1 hη (s7e_hw hn g hloc t ht false) (s7e_hxm hn g h t)
    (s7e_huniq_m hn g h t) hf hM hηr hr1 v hv, ?_⟩
  rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_key_lt_vl_false hn (s7e_hPp g t) _ h.1.1 hη (s7e_hw hn g hloc t ht true)
    (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) hf' _ hφne, hφe, hM1]
  have := ZMod.val_lt v.2.val
  omega

include hη in
/-- **The Gauss lists of corresponding spectator carriers are rotations of each other** along the
relocated visit map (U110-D's cut form: no wrap for `M ≠ 0`; the leg visit wraps for `M = 0`). -/
theorem s7e_isRotated (hηr : 4 * η < r) (hr1 : r < 1)
    (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (q : Component hn (s7e_hPm g t) S) :
    (CB.gaussList (CB.cg hn (s7e_hPp g t))
        (carrierCrossings hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (s7e_e hn g h hloc t ht S hS q))).IsRotated
      ((CB.gaussList (CB.cg hn (s7e_hPm g t)) (carrierCrossings hn (s7e_hPm g t) S q)).map
        (s7e_visitMap hn g h hloc t ht)) := by
  have hmem := s7e_hmem hn g h hloc t ht hη S hS q
  by_cases hM : M = 0
  · rcases Bool.eq_false_or_eq_true (s7e_leg g M a) with hf | hf
    · exact s7e_isRotated_of_bottom_to_top _ _ _ _ _ (s7e_vl (s7e_hxm hn g h t)) η
        (s7e_key_vl_lt_eta_wall hn g h hloc t ht hM hf)
        (fun v _ hv => (s7e_key_leg_zero_true hn g h hloc t ht hη hM hf hηr hr1 v hv).1) hmem
        (fun v w _ _ hv hw => s7e_key_nonleg hn g h hloc t ht hη v w hv hw)
        (fun v _ hv => by
          rw [s7e_visitMap_vl hn g h hloc t ht]
          exact (s7e_key_leg_zero_true hn g h hloc t ht hη hM hf hηr hr1 v hv).2)
    · exact s7e_isRotated_of_top_to_bottom _ _ _ _ _ (s7e_vl (s7e_hxm hn g h t)) hmem
        (fun v w _ _ hv hw => s7e_key_nonleg hn g h hloc t ht hη v w hv hw)
        (fun v _ hv => (s7e_key_leg_zero_false hn g h hloc t ht hη hM hf v hv).1)
        (fun v _ hv => by
          rw [s7e_visitMap_vl hn g h hloc t ht]
          exact (s7e_key_leg_zero_false hn g h hloc t ht hη hM hf v hv).2)
  · apply s7e_isRotated_of_strictMono _ _ _ _ _ hmem
    intro v w _ _ hvw
    by_cases hv : v = s7e_vl (s7e_hxm hn g h t)
    · subst hv
      by_cases hw : w = s7e_vl (s7e_hxm hn g h t)
      · subst hw; exact absurd hvw (lt_irrefl _)
      · rw [s7e_visitMap_vl hn g h hloc t ht]
        exact (s7e_key_leg_ne hn g h hloc t ht hη hM w hw).2 hvw
    · by_cases hw : w = s7e_vl (s7e_hxm hn g h t)
      · subst hw
        rw [s7e_visitMap_vl hn g h hloc t ht]
        exact (s7e_key_leg_ne hn g h hloc t ht hη hM v hv).1 hvw
      · exact s7e_key_nonleg hn g h hloc t ht hη v w hv hw hvw

/-- The relocated visit map commutes with the twin. -/
theorem s7e_htwin (v : Visit (g.curve (g.sideTime false t))) :
    s7e_visitMap hn g h hloc t ht (visitTwin v) = visitTwin (s7e_visitMap hn g h hloc t ht v) := by
  have ha := s7e_a_ne_leg (s7e_leg g M a) h.1.1
  have ha' := s7e_a_ne_leg (!s7e_leg g M a) h.1.1
  rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
    rfl | rfl | hp
  · rw [s7e_twin_va _ ha, s7e_visitMap_vl, s7e_visitMap_va, s7e_twin_va _ ha']
  · rw [s7e_twin_vl _ ha, s7e_visitMap_va, s7e_visitMap_vl, s7e_twin_vl _ ha']
  · rw [s7e_visitMap_of_not hn g h hloc t ht v hp, s7e_visitMap_of_not hn g h hloc t ht (visitTwin v) hp,
      s7a_visit_twin]

include h hloc ht in
/-- The crossing signs of the two contact crossings agree (`s7a_sliding_relocation_sign`), read with
the legs of the two sides. -/
theorem s7e_sgn_contact
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1) :
    crossingSign (g.curve (g.sideTime true t)) a (contactLeg (!s7e_leg g M a) M) =
      crossingSign (g.curve (g.sideTime false t)) a (contactLeg (s7e_leg g M a) M) := by
  have hL := s7e_hL hn g hloc t ht
  have htest : ∀ b : Bool, ∀ forward : Bool,
      IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg forward M} ↔
        chi (g.curve (g.sideTime b t)) a (a + 1) M *
          chi g.center a (a + 1) (contactNeighbour forward M) = -1 :=
    fun b => htests (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht) (g.sideTime_ne_zero b t)
  have hxm := s7e_hxm hn g h t
  have hxp := s7e_hxp hn g h t
  rcases Bool.eq_false_or_eq_true (s7e_leg g M a) with hf | hf
  · rw [hf] at hxm hxp ⊢
    simp only [Bool.not_true, contactLeg, ↓reduceIte, Bool.false_eq_true] at hxm hxp ⊢
    exact (s7a_sliding_relocation_sign hn g h hL true false hxp hxm (htest true)).symm
  · rw [hf] at hxm hxp ⊢
    simp only [Bool.not_false, contactLeg, ↓reduceIte, Bool.false_eq_true] at hxm hxp ⊢
    exact s7a_sliding_relocation_sign hn g h hL false true hxm hxp (htest false)

/-- **`hbit` of U110-D**: the positive over bit is preserved by the relocated visit map (persistent
visits: `s7a_side_sgn`; contact visits: the relocation sign). -/
theorem s7e_hbit
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1)
    (v : Visit (g.curve (g.sideTime false t))) :
    CB.positiveOverBit (s7e_visitMap hn g h hloc t ht v) = CB.positiveOverBit v := by
  have hsg := s7e_sgn_contact hn g h hloc t ht htests
  have ha := s7e_a_ne_leg (s7e_leg g M a) h.1.1
  have ha' := s7e_a_ne_leg (!s7e_leg g M a) h.1.1
  rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
    rfl | rfl | hp
  · rw [s7e_visitMap_va]
    apply s7d_positiveOverBit_eq_of_crossingSign
    rw [s7e_twin_va _ ha, s7e_twin_va _ ha', s7e_va_edge, s7e_va_edge, s7e_vl_edge, s7e_vl_edge]
    exact hsg
  · rw [s7e_visitMap_vl]
    apply s7d_positiveOverBit_eq_of_crossingSign
    rw [s7e_twin_vl _ ha, s7e_twin_vl _ ha', s7e_vl_edge, s7e_vl_edge, s7e_va_edge, s7e_va_edge,
      crossingSign_swap (g.curve (g.sideTime true t)) a, crossingSign_swap (g.curve (g.sideTime false t)) a,
      hsg]
  · rw [s7e_visitMap_of_not hn g h hloc t ht v hp]
    exact s7d_positiveOverBit_eq_of_crossingSign v _
      (s7a_side_sgn hn g h.1 (s7e_hL hn g hloc t ht) false true v hp)

include hloc ht in
theorem s7e_isDecomposition_E (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    IsDecomposition hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) ↔ IsDecomposition hn (s7e_hPm g t) S :=
  s7a_side_isDecomposition_iff hn g (s7e_hL hn g hloc t ht) false true S (s7e_E hn g h hloc t ht S)
    (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS) (s7e_E_hSp' hn g h hloc t ht S hS)

include hη in
/-- **The coefficient equality of the spectator sector** (eq. s7c:sliding-coefficients for the
supports avoiding `x₋`): U110-D's record route with the rotated Gauss lists, twin and over-bit
compatibility, and U110-A2's rotation equality. -/
theorem s7e_coef_eq (hηr : 4 * η < r) (hr1 : r < 1)
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1)
    (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (hdec : IsDecomposition hn (s7e_hPm g t) S) (q : Component hn (s7e_hPm g t) S) :
    cornerCoefficient hn (s7e_hPm g t) S q hdec =
      cornerCoefficient hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (s7e_e hn g h hloc t ht S hS q)
        ((s7e_isDecomposition_E hn g h hloc t ht S hS).mpr hdec) :=
  s7d_cornerCoefficient_eq_of_gaussList_rotated hn hn (s7e_hPm g t) (s7e_hPp g t) hdec q
    ((s7e_isDecomposition_E hn g h hloc t ht S hS).mpr hdec) (s7e_e hn g h hloc t ht S hS q)
    (s7e_visitMap hn g h hloc t ht) (s7e_isRotated hn g h hloc t ht hη hηr hr1 S hS q)
    (fun v _ => s7e_htwin hn g h hloc t ht v) (fun v _ => s7e_hbit hn g h hloc t ht htests v)
    (s7a2_carrierRotation_eq hn g h.1 hloc ht (s7e_hL hn g hloc t ht) false true S
      (s7e_E hn g h hloc t ht S) (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS)
      (s7e_E_hSp' hn g h hloc t ht S hS) hdec q)

include hloc ht in
/-- The selector weights agree (corner turns correspond index by index, U110-A). -/
theorem s7e_wind_eq (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (hdec : IsDecomposition hn (s7e_hPm g t) S) :
    wind hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) = wind hn (s7e_hPm g t) S := by
  have hdec' := (s7e_isDecomposition_E hn g h hloc t ht S hS).mpr hdec
  unfold wind
  symm
  apply Fintype.prod_equiv (s7e_e hn g h hloc t ht S hS)
  intro q
  rw [s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel]
  congr 1
  exact s7c_map_univ_eq_of_equiv _ _ (Equiv.cast (congrArg ZMod (s7a_ccpCornerCount_eq hn (s7e_hPm g t)
    (s7e_hPp g t) (s7e_hs hn g hloc t ht) (s7e_hpar hn g hloc t ht) S (s7e_E hn g h hloc t ht S)
    (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS) (s7e_E_hSp' hn g h hloc t ht S hS) q).symm))
    (fun j => s7a_turn_ccpCornerPolygon hn (s7e_hPm g t) (s7e_hPp g t) (s7e_hs hn g hloc t ht)
      (s7e_hpar hn g hloc t ht) S (s7e_E hn g h hloc t ht S) (s7e_E_hSS' hn g h hloc t ht S)
      (s7e_E_hSp hn g h t S hS) (s7e_E_hSp' hn g h hloc t ht S hS) hdec hdec'
      (s7a_side_turn hn g h.1 (s7e_hL hn g hloc t ht) false true)
      (s7a_side_sgn hn g h.1 (s7e_hL hn g hloc t ht) false true) q j)

include hη in
/-- **The spectator term equality**: for every support `S` of `P₋` avoiding `x₋`, the selector-form
term of `E S` on `P₊` equals the term of `S` on `P₋`. -/
theorem s7e_term_eq (hηr : 4 * η < r) (hr1 : r < 1)
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1)
    (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    s7e_term hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) = s7e_term hn (s7e_hPm g t) S := by
  by_cases hdec : IsDecomposition hn (s7e_hPm g t) S
  · have hdec' := (s7e_isDecomposition_E hn g h hloc t ht S hS).mpr hdec
    rw [s7e_term_of_decomposition _ _ hdec', s7e_term_of_decomposition _ _ hdec,
      s7e_wind_eq hn g h hloc t ht S hS hdec]
    congr 1
    exact (s7d_cornerProduct_eq_of_equiv hn hn (s7e_hPm g t) (s7e_hPp g t) hdec hdec'
      (s7e_e hn g h hloc t ht S hS) (fun q => s7e_coef_eq hn g h hloc t ht hη hηr hr1 htests S hS hdec q)).symm
  · have hdec' : ¬ IsDecomposition hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) :=
      fun h' => hdec ((s7e_isDecomposition_E hn g h hloc t ht S hS).mp h')
    rw [s7e_term_of_not _ _ hdec', s7e_term_of_not _ _ hdec]

include hloc ht hη in
/-- **The spectator sector at `t`.** -/
theorem s7e_spectatorSector_of (hηr : 4 * η < r) (hr1 : r < 1)
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1) :
    s7e_SpectatorSector hn h t :=
  ⟨s7e_spectatorEquiv (s7e_hs hn g hloc t ht) (s7e_xm hn h t) (s7e_xp hn h t) (s7e_hm hn g h t)
    (s7e_hp hn g h t) (s7e_xm_affected hn h t) (s7e_xp_affected hn h t),
    fun S => s7e_term_eq hn g h hloc t ht hη hηr hr1 htests S.1 S.2⟩

end S7ESpectatorKeys

section S7EAssembly

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n}

/-- **The spectator sector below a radius** (PLAN §3.3 sliding (1), PROVED): lem:wall-sides (V)
supplies the interval-local data (`s7a2_exists_intervalLocal`), the contact tests supply the
relocation sign (`vertexEdge_contact_tests`). -/
theorem s7e_exists_spectatorSector (h : g.SlidingAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_SpectatorSector hn h t := by
  obtain ⟨r, η, _, hr1, _, hη, hηr, _, δ₁, hδ₁, _, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1
  obtain ⟨δ₂, hδ₂, _, htests⟩ := g.vertexEdge_contact_tests hn h.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  have hloc' : s7a2_IntervalLocal hn g M a r η (min δ₁ δ₂) :=
    fun u hu => hloc u (lt_of_lt_of_le hu (min_le_left _ _))
  have htests' : ∀ u : g.Parameter, |u.val| < min δ₁ δ₂ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1 :=
    fun u hu hu0 => htests u (lt_of_lt_of_le hu (min_le_right _ _)) hu0
  exact s7e_spectatorSector_of hn g h hloc' t ht hη hηr hr1 htests'

/-- **The sliding law from the contact sector alone**: the spectator sector is proved, so the leaf
`s7_sliding_law_at` reduces to the contact sector below some radius (PLAN §3.3 sliding (2)-(3):
`s7b_slidingDecompositionEquiv` on both sides — which needs the interlacement transfer
`s7b_PivotSplit` — and the termwise identity, which needs `s7b_SlidingTransport.ret`, the corner
correspondence of the relocated carriers for `s7c_carrierWeight_refine`, and their rotation equality by
principal-angle addition; see W2_S7E_REPORT.md). -/
theorem s7e_sliding_law_at_of_contact (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a))
    (hct : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_ContactSector hn h h₁ h₂ t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) :=
  s7e_sliding_law_at_of_sectors hn h h₁ h₂ (s7e_exists_spectatorSector hn g h) hct

end S7EAssembly

section S7EContactRepack

/-! #### The contact sector, repackaged on U110-B's support bijections: given the two interlacement
transfers (`s7b_PivotSplit` on `P₋` at `x₋` and on `P₊` at `x₊`), the sector reduces to the termwise
identity along `s7b_slidingDecompositionEquiv`. -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.SlidingAt M a) (t : g.SideParameter)

include hn h in
/-- The last clause of `VertexCrossingData` (lem:wall-sides (V)): persistent crossings of a side agree
with the centre's. -/
theorem s7e_hQC (b : Bool) : ∀ s, ¬ ContactAffected M a s →
    (IsCrossing (g.curve (g.sideTime b t)) s ↔ IsCrossing g.center s) := by
  intro s hs
  have := ((vertex_sides hn g h.1).2.2.2.1 t t).2.2.2 s hs
  cases b
  · exact this.2
  · exact this.1

/-- The contact sector from the two interlacement transfers and the termwise identity along U110-B's
bijections `s7b_slidingDecompositionEquiv` (eq. s7c:sliding-bijection on each side). -/
theorem s7e_contactSector_of_pivotSplit (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a))
    (hsplitm : s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g false))
      (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
      (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false))
      (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)) (s7e_xm hn h t))
    (hsplitp : s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g true))
      (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
      (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true))
      (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)) (s7e_xp hn h t))
    (hterm : ∀ q, s7e_term hn (s7a_sideGeneric g true)
        ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)
          (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).1 -
      s7e_term hn (s7a_sideGeneric g false)
        ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)
          (s7a_sideGeneric g false) h₁ h₂ (s7e_xm hn h t) hsplitm).symm q).1 =
      (g.contactSign M a : ℤ) *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ q.1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ q.2.1)) :
    s7e_ContactSector hn h h₁ h₂ t :=
  ⟨_, _, hterm⟩

end S7EContactRepack


/-- The sliding branch (sm-4:300-406): relocation bijection `φ(x₋) = x₊`, the support bijection
eq. s7c:sliding-bijection with the halves, equal coefficient products eq. s7c:sliding-coefficients, and
the exact selector difference eq. s7c:sliding-selector-difference.  NO floor, NO singleton. -/
theorem s7_sliding_law_at (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry

/-! ### Unit U110-H (helper unit, prefix `s7h_`; PLAN_FINAL §3.3 (3), §4): the two-component row of
lem:homflyrows on the smoothing diagram `D_A`, its `knotRestrict`s, `2ℓ = twoLinking`, and the writhe
counts eq. s7c:crossing-partition / s7c:pre-curl-writhe / s7c:interlacing-writhe-row /
s7c:noninterlacing-writhe (sm-4:496-533, 638-668, 736-742).  Everything is stated on abstract diagrams:
`D_A` is known to the bigon route only through the record clause of the accepted
`exists_smoothing_record_visit` (SM/Smoothing.lean:8185), `Nonempty (RecordIso D_A.record
(D_H.record.smooth v))`, so the counts are derived from that clause; U110-K substitutes the actual lifts
(`positiveLift_writhe_eq_carrierCrossingCount` for `w_H, w_L`). -/

/-- The writhe of a block restriction is the sum of the signs of the internal crossings of the block
(`Shadow.restrictCrossingEquiv`, `Diagram.restrict_sign`). -/
theorem s7h_writhe_restrict (D : Diagram) (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) :
    (D.restrict B hB).writhe =
      ∑ x : {x : D.Γ.Crossing // ∀ s ∈ x.val, s.1 ∈ B}, (D.sign x.1 : ℤ) := by
  unfold Diagram.writhe
  exact Fintype.sum_equiv (D.Γ.restrictCrossingEquiv B hB) _ _
    (fun y => by rw [D.restrict_sign B hB y]; rfl)

/-- The self crossings of the component `i`: both strands on `i` (`val_eq_pair`). -/
theorem s7h_self_iff (D : Diagram) (i : Fin D.Γ.c) (x : D.Γ.Crossing) :
    (∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))) ↔
      (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i := by
  rw [D.val_eq_pair x]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/-- "their actual knot restrictions" (mp:lowest): the writhe of `D.knotRestrict i` is the sum of the
signs of the self crossings of component `i` (eq. s7c:crossing-partition, first two rows). -/
theorem s7h_writhe_knotRestrict (D : Diagram) (i : Fin D.Γ.c) :
    (D.knotRestrict i).writhe =
      ∑ x ∈ Finset.univ.filter
        (fun x : D.Γ.Crossing => (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i),
        (D.sign x : ℤ) := by
  unfold Diagram.knotRestrict
  rw [s7h_writhe_restrict]
  have hfilt : Finset.univ.filter
      (fun x : D.Γ.Crossing => (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i) =
      Finset.univ.filter
        (fun x : D.Γ.Crossing => ∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))) :=
    Finset.filter_congr fun x _ => (s7h_self_iff D i x).symm
  rw [hfilt]
  exact (Finset.sum_subtype (Finset.univ.filter
    (fun x : D.Γ.Crossing => ∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))))
    (fun x => by simp) (fun x => (D.sign x : ℤ))).symm

/-- `2ℓ_ij` as a sum over the mixed crossings (each mixed crossing is exactly one ordered strand pair
`(s, t)` with `s` on `i`, `t` on `j`; eq. s7c:crossing-partition, third row). -/
theorem s7h_mixedSignSum_eq (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    mixedSignSum D i j =
      ∑ x ∈ Finset.univ.filter (fun x : D.Γ.Crossing =>
        ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
        ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)), (D.sign x : ℤ) := by
  unfold mixedSignSum
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun s t : D.Γ.Strand =>
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0)]
  -- the term of an ordered pair is nonzero only when it is a mixed pair
  have hmp : ∀ p : D.Γ.Strand × D.Γ.Strand,
      (if h : D.Γ.MixedPair i j p.1 p.2 then ((D.sign ⟨{p.1, p.2}, h.2.2⟩ : SignType) : ℤ) else 0) ≠ 0 →
      D.Γ.MixedPair i j p.1 p.2 := by
    intro p hne
    by_contra hm
    exact hne (dite_eq_right hm)
  refine Finset.sum_bij_ne_zero (fun p _ hne => ⟨{p.1, p.2}, (hmp p hne).2.2⟩) ?_ ?_ ?_ ?_
  · -- lands in the mixed crossings
    intro p _ hne
    have hm := hmp p hne
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases D.eq_over_under_of_crossing_eq hm.2.2 rfl with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · left; exact ⟨by rw [← hs]; exact hm.1, by rw [← ht]; exact hm.2.1⟩
    · right; exact ⟨by rw [← ht]; exact hm.2.1, by rw [← hs]; exact hm.1⟩
  · -- injective: the pair is recovered from the crossing by the components
    intro p₁ _ hne₁ p₂ _ hne₂ e
    have hm₁ := hmp p₁ hne₁
    have hm₂ := hmp p₂ hne₂
    have e' : ({p₁.1, p₁.2} : Finset D.Γ.Strand) = {p₂.1, p₂.2} := congrArg Subtype.val e
    have hs : p₁.1 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_self _ _
    have ht : p₁.2 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hs ht
    refine Prod.ext ?_ ?_
    · exact hs.resolve_right fun h => hij (by rw [← hm₁.1, h, hm₂.2.1])
    · exact ht.resolve_left fun h => hij (by rw [← hm₂.1, ← h, hm₁.2.1])
  · -- surjective onto the mixed crossings
    intro x hx _
    have hx' := (Finset.mem_filter.mp hx).2
    have hsgn : ((D.sign x : SignType) : ℤ) ≠ 0 := by
      rcases D.sign_eq_one_or_neg_one x with h | h <;> rw [h] <;> decide
    rcases hx' with ⟨ho, hu⟩ | ⟨ho, hu⟩
    · have hm : D.Γ.MixedPair i j (D.overStrand x) (D.underStrand x) :=
        ⟨ho, hu, by rw [← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.overStrand x, D.underStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.overStrand x, D.underStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext (D.val_eq_pair x).symm
        rw [e]; exact hsgn
      · exact Subtype.ext (D.val_eq_pair x).symm
    · have hm : D.Γ.MixedPair i j (D.underStrand x) (D.overStrand x) :=
        ⟨hu, ho, by rw [Finset.pair_comm, ← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.underStrand x, D.overStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.underStrand x, D.overStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
        rw [e]; exact hsgn
      · exact Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
  · -- the terms agree
    intro p _ hne
    rw [dite_eq_left (hmp p hne)]

/-- With two components `i ≠ j`, every component is `i` or `j`. -/
theorem s7h_comp_eq_or (D : Diagram) {i j : Fin D.Γ.c} (h2 : D.componentCount = 2) (hij : i ≠ j)
    (c : Fin D.Γ.c) : c = i ∨ c = j := by
  have huniv : ({i, j} : Finset (Fin D.Γ.c)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    exact h2.le
  have hc : c ∈ ({i, j} : Finset (Fin D.Γ.c)) := by rw [huniv]; exact Finset.mem_univ c
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hc

/-- A two-component diagram has two distinct component indices. -/
theorem s7h_exists_two_components (D : Diagram) (h2 : D.componentCount = 2) :
    ∃ i j : Fin D.Γ.c, i ≠ j := by
  unfold Diagram.componentCount at h2
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  intro h
  have := congrArg Fin.val h
  simp at this

/-- **eq. s7c:crossing-partition as a writhe identity**: for a two-component diagram the writhe is the
sum of the writhes of the two knot restrictions plus `2ℓ` ("the self crossings contribute `w₁ + w₂`,
the mixed crossings of `D_A` contribute `2ℓ`", sm-4:649-651). -/
theorem s7h_writhe_two_component (D : Diagram) (i j : Fin D.Γ.c) (h2 : D.componentCount = 2)
    (hij : i ≠ j) :
    D.writhe = (D.knotRestrict i).writhe + (D.knotRestrict j).writhe + twoLinking D i j := by
  have key : ∀ x : D.Γ.Crossing, (D.sign x : ℤ) =
      (if (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i then (D.sign x : ℤ) else 0) +
      (if (D.overStrand x).1 = j ∧ (D.underStrand x).1 = j then (D.sign x : ℤ) else 0) +
      (if ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
          ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i) then (D.sign x : ℤ) else 0) := by
    intro x
    have hji : j ≠ i := hij.symm
    rcases s7h_comp_eq_or D h2 hij (D.overStrand x).1 with ho | ho <;>
      rcases s7h_comp_eq_or D h2 hij (D.underStrand x).1 with hu | hu <;>
      simp [ho, hu, hij, hji]
  rw [s7h_writhe_knotRestrict, s7h_writhe_knotRestrict, twoLinking, s7h_mixedSignSum_eq D i j hij]
  unfold Diagram.writhe
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]

/-- `2ℓ` is even (mp:zero-link `half_sum_integer`): the printed linking number `ℓ = lk(D_A)`. -/
theorem s7h_twoLinking_even (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    ∃ l : ℤ, twoLinking D i j = 2 * l :=
  zero_link.half_sum_integer D i j hij

/-- The record-level smoothing drops the writhe by the sign of the smoothed crossing (the two erased
occurrences carry that sign; `smooth_sgn`, `sgn_pair`). -/
theorem s7h_record_writhe_smooth (ρ : Record) (v : ρ.M) :
    (ρ.smooth v).writhe = ρ.writhe - (ρ.sgn v : ℤ) := by
  have h2 := ρ.two_mul_writhe
  -- the retained occurrences: the sum over the smoothing's occurrence set is the filtered sum
  have h1 : 2 * (ρ.smooth v).writhe = ∑ w ∈ Finset.univ.filter (ρ.SmoothKeep v), (ρ.sgn w : ℤ) := by
    rw [Record.two_mul_writhe]
    refine (Fintype.sum_equiv
      (Equiv.refl _ : (ρ.smooth v).M ≃ {w : ρ.M // ρ.SmoothKeep v w}) _
      (fun w => (ρ.sgn w.1 : ℤ)) (fun w => rfl)).trans ?_
    exact (Finset.sum_subtype (Finset.univ.filter (ρ.SmoothKeep v)) (fun w => by simp)
      (fun w => (ρ.sgn w : ℤ))).symm
  -- the two erased occurrences carry the sign of `v`
  have h4 : ∑ w ∈ Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w), (ρ.sgn w : ℤ) =
      2 * (ρ.sgn v : ℤ) := by
    have hf : Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w) = {v, ρ.pair v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Record.SmoothKeep, not_not]
    rw [hf, Finset.sum_pair (ρ.pair_ne v).symm, ρ.sgn_pair]
    ring
  have h5 : ∑ w ∈ Finset.univ.filter (ρ.SmoothKeep v), (ρ.sgn w : ℤ) +
      ∑ w ∈ Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w), (ρ.sgn w : ℤ) =
      ∑ w, (ρ.sgn w : ℤ) :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (ρ.SmoothKeep v) (fun w => (ρ.sgn w : ℤ))
  omega

/-- **The smoothing count on `D_A`**: any diagram whose record is the record-level smoothing of `D` at
the occurrence `v` (the clause of `exists_smoothing_record_visit`) has writhe `w(D) − σ(x)`;
at the positive contact crossing `q = x` this is "the smoothed crossing `q` contributes one"
(sm-4:651). -/
theorem s7h_writhe_of_smooth_iso (D D₀ : Diagram) (v : D.Γ.Visit)
    (h : Nonempty (RecordIso D₀.record (D.record.smooth v))) :
    D₀.writhe = D.writhe - (D.sign v.1 : ℤ) := by
  obtain ⟨ι⟩ := h
  rw [← D₀.record_writhe, ι.writhe_eq, s7h_record_writhe_smooth, D.record_writhe, D.record_sgn]

/-- Smoothing a crossing of a one-component diagram (every crossing is a self crossing) gives two
components ("A self crossing splits one parameter circle into two", sm-3:1087;
`componentCount_smooth_of_self`). -/
theorem s7h_componentCount_of_smooth_iso (D D₀ : Diagram) (hD : D.componentCount = 1)
    (v : D.Γ.Visit) (h : Nonempty (RecordIso D₀.record (D.record.smooth v))) :
    D₀.componentCount = 2 := by
  obtain ⟨ι⟩ := h
  have hself : D.record.IsSelfCrossing v := by
    rw [D.record_isSelfCrossing_iff]
    unfold Diagram.componentCount at hD
    apply Fin.ext
    have ha := ((v.2.val).1).2
    have hb := ((D.Γ.other v.1 v.2.2).1).2
    omega
  rw [← D₀.record_componentCount, ι.componentCount_eq,
    D.record.componentCount_smooth_of_self v hself, D.record_componentCount, hD]

/-- The oriented smoothing of a one-component diagram at a positive crossing, with its record clause,
component count `2` and writhe `w − 1` (`exists_smoothing_record_visit` at the over occurrence). -/
theorem s7h_exists_smoothing_two_component (D : Diagram) (hD : D.componentCount = 1)
    (x : D.Γ.Crossing) (hx : D.IsPositive x) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) ∧
      D₀.componentCount = 2 ∧ D₀.writhe = D.writhe - 1 := by
  obtain ⟨D₀, h₀, hrec⟩ := exists_smoothing_record_visit D x (D.overVisit x) rfl
  refine ⟨D₀, h₀, hrec, s7h_componentCount_of_smooth_iso D D₀ hD _ hrec, ?_⟩
  rw [s7h_writhe_of_smooth_iso D D₀ _ hrec]
  have hs : D.sign (D.overVisit x).1 = 1 := (D.isPositive_iff_sign_eq_one x).mp hx
  rw [hs, SignType.coe_one]

/-- **eq. s7c:interlacing-writhe-row, second identity, in `D_A`-component form** (valid in both
branches through eq. s7c:pre-curl-writhe): if `D_A` has the record of the smoothing of `D_H` at the
positive occurrence `v` and `w_H = w_L + 2` (the two newborn positive crossings), then
`w_L = w(D_A|ᵢ) + w(D_A|ⱼ) + 2ℓ − 1`.  For `ε = 1` the restrictions are the half contact carrier
diagrams (`w_i`); for `ε = 0` component `1` still carries the curl `y` (`w(D_A|₁) = w₁ + 1`), which
gives eq. s7c:noninterlacing-writhe `w_L = w₁ + w₂ + 2ℓ`. -/
theorem s7h_writhe_low (DH DL DA : Diagram) (v : DH.Γ.Visit) (hpos : DH.IsPositive v.1)
    (hrec : Nonempty (RecordIso DA.record (DH.record.smooth v))) (i j : Fin DA.Γ.c)
    (h2 : DA.componentCount = 2) (hij : i ≠ j) (hHL : DH.writhe = DL.writhe + 2) :
    DL.writhe = (DA.knotRestrict i).writhe + (DA.knotRestrict j).writhe + twoLinking DA i j - 1 := by
  have h1 := s7h_writhe_of_smooth_iso DH DA v hrec
  have h3 := s7h_writhe_two_component DA i j h2 hij
  rw [(DH.isPositive_iff_sign_eq_one _).mp hpos, SignType.coe_one] at h1
  omega

/-- The writhes of the positive lifts of two carriers differ by `2` when their crossing counts do
(def:positive-lift "Its writhe is `m_Q`", `positiveLift_writhe_eq_carrierCrossingCount`): the entry
point of `w_H = w_L + 2` from the crossing partition `X(P₊) ∆ X(P₋) = {x, y}` of U110-A/B. -/
theorem s7h_lift_writhe_add_two (hn : 3 ≤ n) {Pp Pm : LabelledTuple n} (hPp : Generic Pp)
    (hPm : Generic Pm) {Sp : Finset (Crossing Pp)} {Sm : Finset (Crossing Pm)}
    (qp : Component hn hPp Sp) (qm : Component hn hPm Sm) (hSp : IsDecomposition hn hPp Sp)
    (hSm : IsDecomposition hn hPm Sm)
    (hm : carrierCrossingCount hn hPp Sp qp = carrierCrossingCount hn hPm Sm qm + 2) :
    (positiveLift hn hPp Sp qp hSp).writhe = (positiveLift hn hPm Sm qm hSm).writhe + 2 := by
  rw [positiveLift_writhe_eq_carrierCrossingCount, positiveLift_writhe_eq_carrierCrossingCount, hm]
  push_cast
  ring

/-- eq. s7c:interlacing-slot: `k_L = K − 2ℓ` from the writhe row and `R_L = R₁ + R₂`. -/
theorem s7h_interlacing_slot {w₁ w₂ wL R₁ R₂ RL l2 : ℤ} (hw : wL = w₁ + w₂ + l2 - 1)
    (hR : RL = R₁ + R₂) : 1 - wL - RL = (1 - w₁ - R₁) + (1 - w₂ - R₂) - l2 := by
  omega

/-- eq. s7c:noninterlacing-slot: `K − k_L = 2ℓ + 2` from eq. s7c:noninterlacing-writhe and
eq. s7c:noninterlacing-rotation `R₁ + R₂ − R_L = −1`. -/
theorem s7h_noninterlacing_slot {w₁ w₂ wL R₁ R₂ RL l2 : ℤ} (hw : wL = w₁ + w₂ + l2)
    (hR : R₁ + R₂ - RL = -1) : (1 - w₁ - R₁) + (1 - w₂ - R₂) - (1 - wL - RL) = l2 + 2 := by
  omega

/-- **lem:homflyrows' two-component row, coefficientwise** (mp:lowest `two_component_row_of_lowest`,
MarkedProducts.lean:2500, and the `[z⁰]`-multiplicativity on `M₁`, `CV.zRow_zero_mul_of_inSupportM_one`):
`[a^d z^{−1}] P_D = [a^{d+2ℓ−1} z⁰](Q₁Q₂) − [a^{d+2ℓ+1} z⁰](Q₁Q₂)`, the two reads "at degree
`k_L + 2ℓ − 2` and `k_L + 2ℓ`" of sm-4:666-668 for `d = k_L − 1`. -/
theorem s7h_two_component_coeff (D : Diagram) (i j : Fin D.Γ.c) (h2 : D.componentCount = 2)
    (hij : i ≠ j) (d : ℤ) :
    coeffAt d (-1) (SM.P D) =
      coeffAt (d + twoLinking D i j - 1) 0 (SM.P (D.knotRestrict i) * SM.P (D.knotRestrict j)) -
        coeffAt (d + twoLinking D i j + 1) 0 (SM.P (D.knotRestrict i) * SM.P (D.knotRestrict j)) := by
  have h := two_component_row_of_lowest D i j h2 hij
  rw [← CV.zRow_zero_mul_of_inSupportM_one (P_knotRestrict_inSupportM_one D i)
    (P_knotRestrict_inSupportM_one D j)] at h
  set g := zRow 0 (SM.P (D.knotRestrict i) * SM.P (D.knotRestrict j)) with hg
  have e : aPow (-(twoLinking D i j)) * (aPow 1 - aPow (-1)) * g =
      LaurentPolynomial.T (1 - twoLinking D i j) * g -
        LaurentPolynomial.T (-1 - twoLinking D i j) * g := by
    simp only [aPow]
    rw [mul_sub, sub_mul, ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
    congr 3 <;> ring
  rw [e] at h
  have hc := congrArg (fun p : LaurentPolynomial ℤ => p.coeff d) h
  simp only [coeff_zRow] at hc
  rw [hc]
  show (LaurentPolynomial.T (1 - twoLinking D i j) * g).coeff d -
    (LaurentPolynomial.T (-1 - twoLinking D i j) * g).coeff d = _
  rw [coeff_T_mul', coeff_T_mul', hg, coeff_zRow, coeff_zRow]
  congr 2 <;> ring

/-- The same row for `homfly` (lem:homflyrows' `H`), through `P_eq_homfly`. -/
theorem s7h_two_component_coeff_homfly (D : Diagram) (i j : Fin D.Γ.c) (h2 : D.componentCount = 2)
    (hij : i ≠ j) (d : ℤ) :
    coeffAt d (-1) (homfly D) =
      coeffAt (d + twoLinking D i j - 1) 0 (homfly (D.knotRestrict i) * homfly (D.knotRestrict j)) -
        coeffAt (d + twoLinking D i j + 1) 0
          (homfly (D.knotRestrict i) * homfly (D.knotRestrict j)) := by
  rw [← P_eq_homfly, ← P_eq_homfly, ← P_eq_homfly]
  exact s7h_two_component_coeff D i j h2 hij d

/-- **eq. s7c:interlacing-extraction / s7c:noninterlacing-extraction before the slot substitution**:
from the extracted skein identity `Ω_H = Ω_L + [a^{k_L−1} z^{−1}] F_A` (the conclusion of
`s7_universal_extraction` with `F_A = P_{D_A}`) and the two-component row,
`Ω_H − Ω_L = [a^{k_L+2ℓ−2} z⁰](Q₁Q₂) − [a^{k_L+2ℓ} z⁰](Q₁Q₂)`; with eq. s7c:interlacing-slot
`k_L + 2ℓ = K` this is `[a^{K−2}](f₁f₂) − [a^K](f₁f₂)`, with eq. s7c:noninterlacing-slot
`k_L + 2ℓ = K − 2` it is `[a^{K−4}](f₁f₂) − [a^{K−2}](f₁f₂)`. -/
theorem s7h_extraction_two_component (DA : Diagram) (i j : Fin DA.Γ.c) (h2 : DA.componentCount = 2)
    (hij : i ≠ j) {FH FL : R} {kL : ℤ}
    (hext : coeffAt (kL - 2) 0 FH = coeffAt kL 0 FL + coeffAt (kL - 1) (-1) (SM.P DA)) :
    coeffAt (kL - 2) 0 FH - coeffAt kL 0 FL =
      coeffAt (kL + twoLinking DA i j - 2) 0 (SM.P (DA.knotRestrict i) * SM.P (DA.knotRestrict j)) -
        coeffAt (kL + twoLinking DA i j) 0 (SM.P (DA.knotRestrict i) * SM.P (DA.knotRestrict j)) := by
  rw [hext, s7h_two_component_coeff DA i j h2 hij (kL - 1)]
  have e1 : kL - 1 + twoLinking DA i j - 1 = kL + twoLinking DA i j - 2 := by ring
  have e2 : kL - 1 + twoLinking DA i j + 1 = kL + twoLinking DA i j := by ring
  rw [e1, e2]
  ring

/-! ### Helper unit U110-I (prefix `s7i_`): the contact rotation ledger — eq. s7c:full-rotation
(sm-4:483-503), the contact turns (540-551), eq. s7c:rotation-ledger (587-598), the `R`-identities
eq. s7c:interlacing-absolute (655-663) / eq. s7c:noninterlacing-rotation (748-757) and the slot
identities eqs. s7c:interlacing-slot, s7c:noninterlacing-slot, s7c:different-low/high-slot.

Design.  Everything is stated on REGULAR LABELLED POLYGONS (the corner polygons of the three contact
carriers — full `L*`, halves `L₁`, `L₂` — are `LabelledTuple`s of three different sizes) with the
corner correspondence of U110-C (`e : {i // i ≠ j₁} ⊕ {i // i ≠ j₂} ≃ {i // i ≠ j}`, "All noncontact
turns partition between the halves", sm-4:551), here required to preserve the PRINCIPAL turn (the real
angle, `principalTurn`), which implies U110-C's sign-preservation (`s7i_turn_elim_of_principalTurn_elim`).
The ledger then needs NO explicit angles: the three rotation numbers are integers (lem:rot,
`rotationNumber_integer`), so the three contact turns sum to a multiple of `2π`; each is in `(−π, π)`
(`principalAngle_bounds`) with the sign of its `turn` (`principalTurn_sign`); the two half contact
turns have the sign `s₀` and the full contact turn has the sign `s₀` (interlacing) or `−s₀`
(noninterlacing) — the multiple is then forced to `0`, resp. `s₀` (`s7i_ledger_of_int`).  The printed
explicit values `β`, `π − α`, `β − α ∓ π` are recovered at the vector level (`s7i_contact_*`), with
eq. s7c:angle-orders in the form "interlacing ⟺ the full contact turn has the sign of the half contact
turns ⟺ `sgn det(w₁, w₂) = −s₀`".  The `R`-identities use lem:uniformrot (`uniform_rotation`) to put
the three rotations on the ray of the uniform sign.  eq. s7c:full-rotation is lem:rot (ii)
(`rotationNumber_family_constant`) on a family through the wall, packaged for the germ's parameter.
Nothing here depends on the floor, the singleton, or any other unit. -/

section S7IRotationLedger

/-! #### eq. s7c:full-rotation — lem:rot (ii) through the wall -/

/-- lem:rot (ii) on a closed real interval: a family of `k`-gons continuous on `[a, b]` and regular at
EVERY parameter of `[a, b]` (including the wall parameter) has one rotation number on `[a, b]`. -/
theorem s7i_rotationNumber_constant_Icc {k : ℕ} [NeZero k] {f : ℝ → LabelledTuple k} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hr : ∀ t ∈ Set.Icc a b, Regular (f t)) {s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    rotationNumber (f s) = rotationNumber (f t) := by
  have : PreconnectedSpace (Set.Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hF : Continuous (fun u : Set.Icc a b => f u.1) :=
    hf.comp_continuous continuous_subtype_val (fun u => u.2)
  exact rotationNumber_family_constant hF (fun u => hr u.1 u.2) ⟨s, hs⟩ ⟨t, ht⟩

/-- The inclusion of the closed symmetric interval `[−t, t]` into the germ's parameter interval. -/
def s7i_germIcc (g : WallGerm n) (t : g.SideParameter) (u : Set.Icc (-t.val) t.val) : g.Parameter :=
  ⟨u.1, by
    obtain ⟨h1, h2⟩ := u.2
    have := t.property.2
    constructor <;> linarith⟩

omit [NeZero n] in
theorem s7i_continuous_germIcc (g : WallGerm n) (t : g.SideParameter) :
    Continuous (s7i_germIcc g t) :=
  continuous_subtype_val.subtype_mk _

omit [NeZero n] in
theorem s7i_germIcc_left (g : WallGerm n) (t : g.SideParameter) :
    s7i_germIcc g t ⟨-t.val, by constructor <;> linarith [t.property.1]⟩ = g.sideTime false t := by
  apply Subtype.ext
  simp [s7i_germIcc, WallGerm.sideTime]

omit [NeZero n] in
theorem s7i_germIcc_right (g : WallGerm n) (t : g.SideParameter) :
    s7i_germIcc g t ⟨t.val, by constructor <;> linarith [t.property.1]⟩ = g.sideTime true t := by
  apply Subtype.ext
  simp [s7i_germIcc, WallGerm.sideTime]

omit [NeZero n] in
/-- **eq. s7c:full-rotation** in the germ's parameter (sm-4:493-503): a family of `k`-gons over the germ's
parameter interval, continuous on `|u| ≤ t` and regular there — "the edge pieces have positive lengths at
the centre, and all its corner turns have nonzero determinants there … a continuous regular family,
including at the wall" — has the same rotation number at the two side parameters `−t` and `t`
(lem:rot (ii)).  `rot(L_L) = rot(L_H)`; `rot(L*)` is the value at the centre `u = 0`. -/
theorem s7i_full_rotation_germ {k : ℕ} [NeZero k] (g : WallGerm n) (t : g.SideParameter)
    {f : g.Parameter → LabelledTuple k} (hf : ContinuousOn f {u : g.Parameter | |u.val| ≤ t.val})
    (hr : ∀ u : g.Parameter, |u.val| ≤ t.val → Regular (f u)) :
    rotationNumber (f (g.sideTime false t)) = rotationNumber (f (g.sideTime true t)) := by
  have : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hmem : ∀ u : Set.Icc (-t.val) t.val, s7i_germIcc g t u ∈ {u : g.Parameter | |u.val| ≤ t.val} := by
    intro u
    show |u.1| ≤ t.val
    exact abs_le.mpr u.2
  have hF : Continuous (fun u : Set.Icc (-t.val) t.val => f (s7i_germIcc g t u)) :=
    hf.comp_continuous (s7i_continuous_germIcc g t) hmem
  have hc := rotationNumber_family_constant hF (fun u => hr _ (hmem u))
    ⟨-t.val, by constructor <;> linarith [t.property.1]⟩ ⟨t.val, by constructor <;> linarith [t.property.1]⟩
  simpa only [s7i_germIcc_left, s7i_germIcc_right] using hc

omit [NeZero n] in
/-- The centre value is the common side value (`rot(L*) = rot(L_L) = rot(L_H)`). -/
theorem s7i_full_rotation_germ_centre {k : ℕ} [NeZero k] (g : WallGerm n) (t : g.SideParameter)
    {f : g.Parameter → LabelledTuple k} (hf : ContinuousOn f {u : g.Parameter | |u.val| ≤ t.val})
    (hr : ∀ u : g.Parameter, |u.val| ≤ t.val → Regular (f u)) (b : Bool) :
    rotationNumber (f (g.sideTime b t)) = rotationNumber (f g.zeroParameter) := by
  have : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hmem : ∀ u : Set.Icc (-t.val) t.val, s7i_germIcc g t u ∈ {u : g.Parameter | |u.val| ≤ t.val} := by
    intro u
    show |u.1| ≤ t.val
    exact abs_le.mpr u.2
  have hF : Continuous (fun u : Set.Icc (-t.val) t.val => f (s7i_germIcc g t u)) :=
    hf.comp_continuous (s7i_continuous_germIcc g t) hmem
  have h0 : s7i_germIcc g t ⟨0, by constructor <;> linarith [t.property.1]⟩ = g.zeroParameter := by
    apply Subtype.ext
    simp [s7i_germIcc, WallGerm.zeroParameter]
  cases b
  · have hc := rotationNumber_family_constant hF (fun u => hr _ (hmem u))
      ⟨-t.val, by constructor <;> linarith [t.property.1]⟩ ⟨0, by constructor <;> linarith [t.property.1]⟩
    simpa only [s7i_germIcc_left, h0] using hc
  · have hc := rotationNumber_family_constant hF (fun u => hr _ (hmem u))
      ⟨t.val, by constructor <;> linarith [t.property.1]⟩ ⟨0, by constructor <;> linarith [t.property.1]⟩
    simpa only [s7i_germIcc_right, h0] using hc

/-- eq. s7c:full-rotation read on the two side carriers: if the corner polygons of the full contact
carriers `q₋` (on `P₋ = sideTuple false t`) and `q₊` (on `P₊ = sideTuple true t`) are, up to the size
recast, the two side values of one regular family through the wall, then `rot(L_L) = rot(L_H)`. -/
theorem s7i_carrierRotation_sides_of_family (hn : 3 ≤ n) (g : WallGerm n) (t : g.SideParameter)
    {k : ℕ} [NeZero k] {f : g.Parameter → LabelledTuple k}
    (hf : ContinuousOn f {u : g.Parameter | |u.val| ≤ t.val})
    (hr : ∀ u : g.Parameter, |u.val| ≤ t.val → Regular (f u))
    (Sm : Finset (Crossing (g.sideTuple false t).val)) (qm : Component hn (g.sideTuple false t).property Sm)
    (Sp : Finset (Crossing (g.sideTuple true t).val)) (qp : Component hn (g.sideTuple true t).property Sp)
    (hkm : k = ccpCornerCount hn (g.sideTuple false t).property Sm qm)
    (hkp : k = ccpCornerCount hn (g.sideTuple true t).property Sp qp)
    (hm : recastTuple hkm (ccpCornerPolygon hn (g.sideTuple false t).property Sm qm) = f (g.sideTime false t))
    (hp : recastTuple hkp (ccpCornerPolygon hn (g.sideTuple true t).property Sp qp) = f (g.sideTime true t)) :
    carrierRotation hn (g.sideTuple false t).property Sm qm =
      carrierRotation hn (g.sideTuple true t).property Sp qp := by
  unfold carrierRotation
  rw [← rotationNumber_recastTuple hkm, ← rotationNumber_recastTuple hkp, hm, hp]
  exact s7i_full_rotation_germ g t hf hr

/-! #### The contact turns at the vector level (sm-4:540-551): `r` the remote direction (edge `E_a`),
`w₁ = μ_{M−1} − μ_M`, `w₂ = μ_{M+1} − μ_M` the neighbour vectors.  Half 1 (`λ₁` closes with
`[μ_a, μ_M] ⊂ E_a`, def:deletion-halves) turns from `r` onto `w₂`; half 2 (`λ₂` closes with `E_{M−1}`
and opens with `[μ_M, μ_b] ⊂ E_a`) turns from `−w₁` onto `r`; the full contact carrier turns from `−w₁`
onto `w₂` (the polygon's own corner at `M`).  In the printed normalisation (`r = (1,0)`, both
neighbours above, arguments `α, β ∈ (0, π)`) these are `β`, `π − α`, `β − α ∓ π`. -/

theorem s7i_det_neg_left (u v : Plane) : det (-u) v = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]
  ring

theorem s7i_det_neg_right (u v : Plane) : det u (-v) = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]
  ring

theorem s7i_det_zero_left (v : Plane) : det 0 v = 0 := by
  simp [det]

theorem s7i_det_zero_right (u : Plane) : det u 0 = 0 := by
  simp [det]

/-- Two vectors with nonzero determinant form a regular pair (not collinear at all). -/
theorem s7i_regularPair_of_det_ne_zero {u v : Plane} (h : det u v ≠ 0) : RegularPair u v := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact h (s7i_det_zero_left v)
  · rintro rfl
    exact h (s7i_det_zero_right u)
  · rintro ⟨r, _, rfl⟩
    exact h (det_smul_self u r)

/-- The three contact turns sum to zero modulo `2π` (the telescoping identity of lem:rot on the triangle
of directions `−w₁ → r → w₂`). -/
theorem s7i_contact_angle_sum {r w₁ w₂ : Plane} (hr : r ≠ 0) (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) :
    ((principalAngle r w₂ + principalAngle (-w₁) r - principalAngle (-w₁) w₂ : ℝ) : Real.Angle) = 0 := by
  have h₁' : -w₁ ≠ 0 := neg_ne_zero.mpr h₁
  rw [Real.Angle.coe_sub, Real.Angle.coe_add, principalAngle_coe_angle hr h₂,
    principalAngle_coe_angle h₁' hr, principalAngle_coe_angle h₁' h₂]
  abel

/-- … hence they sum to an integer multiple of `2π`. -/
theorem s7i_contact_angle_sum_int {r w₁ w₂ : Plane} (hr : r ≠ 0) (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) :
    ∃ m : ℤ, principalAngle r w₂ + principalAngle (-w₁) r - principalAngle (-w₁) w₂ = m * (2 * Real.pi) := by
  obtain ⟨m, hm⟩ := Real.Angle.coe_eq_zero_iff.mp (s7i_contact_angle_sum hr h₁ h₂)
  exact ⟨m, by rw [← hm, zsmul_eq_mul]⟩

/-! #### The ledger as pure real arithmetic -/

/-- A nonzero sign is `1` or `−1`. -/
theorem s7i_signType_cases {σ : SignType} (h : σ ≠ 0) : σ = 1 ∨ σ = -1 := by
  cases σ
  · exact absurd rfl h
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The negative of a nonzero sign is nonzero. -/
theorem s7i_neg_signType_ne_zero {σ : SignType} (h : σ ≠ 0) : -σ ≠ 0 := by
  rcases s7i_signType_cases h with rfl | rfl <;> decide

/-- **The ledger from integrality, bounds and signs** (sm-4:587-598, "Dividing by `2π` gives the signed
identity … The second line contains a full-turn correction; unsigned angles would not give this
formula"): three angles in `(−π, π)` whose signed combination `θ₁ + θ₂ − θ` is a multiple of `2π`, the
first two of sign `s₀`: if `θ` has the sign `s₀` the combination is `0`; if `θ` has the sign `−s₀` it is
the full turn `2π s₀`. -/
theorem s7i_ledger_of_int {θ₁ θ₂ θ : ℝ} {m : ℤ} (hm : θ₁ + θ₂ - θ = m * (2 * Real.pi))
    (hb₁ : -Real.pi < θ₁ ∧ θ₁ < Real.pi) (hb₂ : -Real.pi < θ₂ ∧ θ₂ < Real.pi)
    (hb : -Real.pi < θ ∧ θ < Real.pi) {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (h₁ : SignType.sign θ₁ = s₀) (h₂ : SignType.sign θ₂ = s₀) :
    (SignType.sign θ = s₀ → θ₁ + θ₂ - θ = 0) ∧
      (SignType.sign θ = -s₀ → θ₁ + θ₂ - θ = 2 * Real.pi * (s₀ : ℝ)) := by
  have hpi := Real.pi_pos
  rcases s7i_signType_cases hs₀ with rfl | rfl
  · have hp₁ : 0 < θ₁ := sign_eq_one_iff.mp h₁
    have hp₂ : 0 < θ₂ := sign_eq_one_iff.mp h₂
    constructor
    · intro h
      have hp : 0 < θ := sign_eq_one_iff.mp h
      have hlt : (m : ℝ) < 1 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hgt : (-1 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have hm0 : m = 0 := by
        have h1 : m < 1 := by exact_mod_cast hlt
        have h2 : -1 < m := by exact_mod_cast hgt
        omega
      rw [hm, hm0]
      simp
    · intro h
      have hp : θ < 0 := sign_eq_neg_one_iff.mp (by simpa using h)
      have hlt : (m : ℝ) < 2 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hgt : (0 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have hm1 : m = 1 := by
        have h1 : m < 2 := by exact_mod_cast hlt
        have h2 : 0 < m := by exact_mod_cast hgt
        omega
      rw [hm, hm1]
      simp
  · have hp₁ : θ₁ < 0 := sign_eq_neg_one_iff.mp h₁
    have hp₂ : θ₂ < 0 := sign_eq_neg_one_iff.mp h₂
    constructor
    · intro h
      have hp : θ < 0 := sign_eq_neg_one_iff.mp h
      have hlt : (m : ℝ) < 1 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hgt : (-1 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have hm0 : m = 0 := by
        have h1 : m < 1 := by exact_mod_cast hlt
        have h2 : -1 < m := by exact_mod_cast hgt
        omega
      rw [hm, hm0]
      simp
    · intro h
      have hp : 0 < θ := sign_eq_one_iff.mp (by simpa using h)
      have hlt : (m : ℝ) < 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hgt : (-2 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have hm1 : m = -1 := by
        have h1 : m < 0 := by exact_mod_cast hlt
        have h2 : -2 < m := by exact_mod_cast hgt
        omega
      rw [hm, hm1]
      simp

/-! #### The contact turns: signs, eq. s7c:angle-orders, and the vector-level ledger -/

/-- The half contact turn of `λ₁` (`r → w₂`) has the sign of `det(r, w₂)` (`= s₀`: `β ∈ (0, π)` in the
normalisation). -/
theorem s7i_contact_sign_half₁ {r w₂ : Plane} (h : det r w₂ ≠ 0) :
    SignType.sign (principalAngle r w₂) = SignType.sign (det r w₂) :=
  principalAngle_sign (s7i_regularPair_of_det_ne_zero h)

/-- The half contact turn of `λ₂` (`−w₁ → r`) has the sign of `det(r, w₁)` (`= s₀`: `π − α ∈ (0, π)`). -/
theorem s7i_contact_sign_half₂ {r w₁ : Plane} (h : det r w₁ ≠ 0) :
    SignType.sign (principalAngle (-w₁) r) = SignType.sign (det r w₁) := by
  have h' : det (-w₁) r ≠ 0 := by
    rw [s7i_det_neg_left, det_swap, neg_neg]
    exact h
  rw [principalAngle_sign (s7i_regularPair_of_det_ne_zero h'), s7i_det_neg_left, det_swap, neg_neg]

/-- The full contact turn (`−w₁ → w₂`, the polygon's corner at `M`) has the sign of `−det(w₁, w₂)`
(`β − α ∓ π`). -/
theorem s7i_contact_sign_full {w₁ w₂ : Plane} (h : det w₁ w₂ ≠ 0) :
    SignType.sign (principalAngle (-w₁) w₂) = -SignType.sign (det w₁ w₂) := by
  have h' : det (-w₁) w₂ ≠ 0 := by
    rw [s7i_det_neg_left]
    exact neg_ne_zero.mpr h
  rw [principalAngle_sign (s7i_regularPair_of_det_ne_zero h'), s7i_det_neg_left, Left.sign_neg]

/-- **The contact configuration** (sm-4:540-551, eq. s7c:angle-orders): both neighbours strictly on the
same side `s₀` of the remote line (`sgn det(r, w₁) = sgn det(r, w₂) = s₀ ≠ 0`) and a nondegenerate corner
at `M` (`det(w₁, w₂) ≠ 0`, i.e. (G1)).  Interlacing (`ε = 1`, `β < α`) is `sgn det(w₁, w₂) = −s₀`: then the
full contact turn has the sign `s₀` of the half contact turns and the three contact turns satisfy
`θ₁ + θ₂ − θ* = 0` (`β + (π − α) − (β − α + π)`).  Noninterlacing (`ε = 0`, `α < β`) is `sgn det(w₁, w₂) = s₀`:
the full contact turn has the sign `−s₀` and `θ₁ + θ₂ − θ* = 2π s₀` (`β + (π − α) − (β − α − π)`; the
full-turn correction).  Stated for both orientations at once ("Reflection reverses all signs together"). -/
theorem s7i_contact_ledger {r w₁ w₂ : Plane} {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (h₁ : SignType.sign (det r w₁) = s₀) (h₂ : SignType.sign (det r w₂) = s₀) (h₁₂ : det w₁ w₂ ≠ 0) :
    (SignType.sign (det w₁ w₂) = -s₀ →
        SignType.sign (principalAngle (-w₁) w₂) = s₀ ∧
        principalAngle r w₂ + principalAngle (-w₁) r - principalAngle (-w₁) w₂ = 0) ∧
      (SignType.sign (det w₁ w₂) = s₀ →
        SignType.sign (principalAngle (-w₁) w₂) = -s₀ ∧
        principalAngle r w₂ + principalAngle (-w₁) r - principalAngle (-w₁) w₂ = 2 * Real.pi * (s₀ : ℝ)) := by
  have hd₁ : det r w₁ ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at h₁
    exact hs₀ h₁.symm
  have hd₂ : det r w₂ ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at h₂
    exact hs₀ h₂.symm
  have hr : r ≠ 0 := by
    rintro rfl
    exact hd₁ (s7i_det_zero_left w₁)
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl
    exact hd₁ (s7i_det_zero_right r)
  have hw₂ : w₂ ≠ 0 := by
    rintro rfl
    exact hd₂ (s7i_det_zero_right r)
  obtain ⟨m, hm⟩ := s7i_contact_angle_sum_int hr hw₁ hw₂
  have hb₁ := principalAngle_bounds (s7i_regularPair_of_det_ne_zero hd₂)
  have hb₂ := principalAngle_bounds (s7i_regularPair_of_det_ne_zero (u := -w₁) (v := r)
    (by rw [s7i_det_neg_left, det_swap, neg_neg]; exact hd₁))
  have hb := principalAngle_bounds (s7i_regularPair_of_det_ne_zero (u := -w₁) (v := w₂)
    (by rw [s7i_det_neg_left]; exact neg_ne_zero.mpr h₁₂))
  have hsg₁ : SignType.sign (principalAngle r w₂) = s₀ := (s7i_contact_sign_half₁ hd₂).trans h₂
  have hsg₂ : SignType.sign (principalAngle (-w₁) r) = s₀ := (s7i_contact_sign_half₂ hd₁).trans h₁
  have hled := s7i_ledger_of_int hm hb₁ hb₂ hb hs₀ hsg₁ hsg₂
  have hfull := s7i_contact_sign_full h₁₂
  constructor
  · intro h
    have hs : SignType.sign (principalAngle (-w₁) w₂) = s₀ := by rw [hfull, h, neg_neg]
    exact ⟨hs, hled.1 hs⟩
  · intro h
    have hs : SignType.sign (principalAngle (-w₁) w₂) = -s₀ := by rw [hfull, h]
    exact ⟨hs, hled.2 hs⟩

/-- The dichotomy behind eq. s7c:angle-orders: a nonzero sign is `s₀` or `−s₀`. -/
theorem s7i_sign_cases_of_ne_zero {σ s₀ : SignType} (hσ : σ ≠ 0) (hs₀ : s₀ ≠ 0) : σ = s₀ ∨ σ = -s₀ := by
  rcases s7i_signType_cases hσ with rfl | rfl <;> rcases s7i_signType_cases hs₀ with rfl | rfl <;> decide

/-- With `det(w₁, w₂) ≠ 0` exactly one line of `s7i_contact_ledger` applies: `sgn det(w₁, w₂) = −s₀`
(interlacing, `ε = 1`) or `= s₀` (noninterlacing, `ε = 0`). -/
theorem s7i_contact_dichotomy {w₁ w₂ : Plane} {s₀ : SignType} (hs₀ : s₀ ≠ 0) (h₁₂ : det w₁ w₂ ≠ 0) :
    SignType.sign (det w₁ w₂) = -s₀ ∨ SignType.sign (det w₁ w₂) = s₀ := by
  have hne : SignType.sign (det w₁ w₂) ≠ 0 := sign_ne_zero.mpr h₁₂
  rcases s7i_sign_cases_of_ne_zero hne hs₀ with h | h
  · exact Or.inr h
  · exact Or.inl h

/-! #### From edge directions to principal turns.  Positive rescaling of both edges at a corner leaves
the principal turn unchanged (`principalAngle_smul`): this is how the contact turns of the corner
polygons are identified with the vector-level turns above (the corner polygon's edges at the contact
corner are positive multiples of `r`, `−w₁`, `w₂`: `[μ_a, μ_M] = λ r`, `[μ_M, μ_b] = (1−λ) r`), and how the
inherited noncontact corners keep their principal turns across the half ↔ full correspondence ("corner
edges are positive multiples of the original edges", lem:carriers (ii), `corner_polygons.2.1`). -/

/-- A corner whose two edges are positive multiples of `u`, `v` has principal turn `principalAngle u v`. -/
theorem s7i_principalTurn_eq_of_pos_smul {k : ℕ} (Q : LabelledTuple k) (i : ZMod k) {u v : Plane}
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (hu : edge Q (i - 1) = c • u) (hv : edge Q i = d • v) :
    principalTurn Q i = principalAngle u v := by
  unfold principalTurn
  rw [hu, hv]
  exact principalAngle_smul hc hd u v

/-- … and its turn is `sgn det(u, v)`. -/
theorem s7i_turn_eq_of_pos_smul {k : ℕ} (Q : LabelledTuple k) (i : ZMod k) {u v : Plane}
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (hu : edge Q (i - 1) = c • u) (hv : edge Q i = d • v) :
    turn Q i = SignType.sign (det u v) := by
  rw [turn_det, hu, hv]
  have hdet : det (c • u) (d • v) = (c * d) * det u v := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hdet, sign_mul, sign_pos (mul_pos hc hd), one_mul]

/-- Two corners (of two polygons) whose edges agree up to positive rescaling have the same principal
turn — the hypothesis `he` of the ledger, corner by corner. -/
theorem s7i_principalTurn_eq_of_edges_pos_smul {k₁ k : ℕ} (Q₁ : LabelledTuple k₁) (Q : LabelledTuple k)
    (i₁ : ZMod k₁) (i : ZMod k) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hu : edge Q (i - 1) = c • edge Q₁ (i₁ - 1)) (hv : edge Q i = d • edge Q₁ i₁) :
    principalTurn Q i = principalTurn Q₁ i₁ :=
  s7i_principalTurn_eq_of_pos_smul Q i hc hd hu hv

/-- Equal edges give equal principal turns (the `c = d = 1` case). -/
theorem s7i_principalTurn_eq_of_edges_eq {k₁ k : ℕ} (Q₁ : LabelledTuple k₁) (Q : LabelledTuple k)
    (i₁ : ZMod k₁) (i : ZMod k) (hu : edge Q (i - 1) = edge Q₁ (i₁ - 1)) (hv : edge Q i = edge Q₁ i₁) :
    principalTurn Q i = principalTurn Q₁ i₁ := by
  unfold principalTurn
  rw [hu, hv]

/-! #### eq. s7c:rotation-ledger on regular polygons, through the corner correspondence of U110-C -/

/-- Bounds of a principal turn of a regular polygon: `ϑ_i ∈ (−π, π)` (lem:rot). -/
theorem s7i_principalTurn_bounds {k : ℕ} {Q : LabelledTuple k} (h : Regular Q) (i : ZMod k) :
    -Real.pi < principalTurn Q i ∧ principalTurn Q i < Real.pi :=
  principalAngle_bounds (h i)

/-- Splitting one corner off the turn sum: `Σ_i ϑ_i = Σ_{i ≠ j} ϑ_i + ϑ_j`. -/
theorem s7i_sum_principalTurn_split {k : ℕ} [NeZero k] (Q : LabelledTuple k) (j : ZMod k) :
    ∑ i, principalTurn Q i =
      ∑ x : {i : ZMod k // i ≠ j}, principalTurn Q x.1 + principalTurn Q j := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)]
  congr 1
  exact Finset.sum_subtype (Finset.univ.erase j) (fun i => by simp) (principalTurn Q)

/-- The turn sums of the three contact carriers, given the principal-turn-preserving noncontact corner
correspondence `e`: `Σϑ(Q₁) + Σϑ(Q₂) − Σϑ(Q) = ϑ_{j₁}(Q₁) + ϑ_{j₂}(Q₂) − ϑ_j(Q)` ("Subtract the explicit
full contact turn from the sum of the two half turns, and add the unchanged noncontact turns"). -/
theorem s7i_ledger_sum {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    (Q₁ : LabelledTuple k₁) (Q₂ : LabelledTuple k₂) (Q : LabelledTuple k)
    (j₁ : ZMod k₁) (j₂ : ZMod k₂) (j : ZMod k)
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x) :
    (∑ i, principalTurn Q₁ i) + (∑ i, principalTurn Q₂ i) - ∑ i, principalTurn Q i =
      principalTurn Q₁ j₁ + principalTurn Q₂ j₂ - principalTurn Q j := by
  rw [s7i_sum_principalTurn_split Q₁ j₁, s7i_sum_principalTurn_split Q₂ j₂,
    s7i_sum_principalTurn_split Q j]
  have hsplit : ∑ x : {i : ZMod k // i ≠ j}, principalTurn Q x.1 =
      ∑ x : {i : ZMod k₁ // i ≠ j₁}, principalTurn Q₁ x.1 +
        ∑ x : {i : ZMod k₂ // i ≠ j₂}, principalTurn Q₂ x.1 := by
    have h1 : ∑ x : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂},
        Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
          (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x =
        ∑ x : {i : ZMod k // i ≠ j}, principalTurn Q x.1 :=
      Fintype.sum_equiv e _ _ (fun x => (he x).symm)
    rw [← h1, Fintype.sum_sum_type]
    rfl
  rw [hsplit]
  ring

/-- The rotation numbers combine as the contact turns do:
`rot(Q₁) + rot(Q₂) − rot(Q) = (ϑ_{j₁} + ϑ_{j₂} − ϑ_j) / 2π`. -/
theorem s7i_rotation_ledger_sum {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    (Q₁ : LabelledTuple k₁) (Q₂ : LabelledTuple k₂) (Q : LabelledTuple k)
    (j₁ : ZMod k₁) (j₂ : ZMod k₂) (j : ZMod k)
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x) :
    rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q =
      (principalTurn Q₁ j₁ + principalTurn Q₂ j₂ - principalTurn Q j) / (2 * Real.pi) := by
  unfold rotationNumber
  rw [← s7i_ledger_sum Q₁ Q₂ Q j₁ j₂ j e he]
  ring

/-- Three regular polygons: the combination of contact turns is an integer multiple of `2π`
(lem:rot `rotationNumber_integer` three times). -/
theorem s7i_ledger_int {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    (j₁ : ZMod k₁) (j₂ : ZMod k₂) (j : ZMod k)
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x) :
    ∃ m : ℤ, rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q = m ∧
      principalTurn Q₁ j₁ + principalTurn Q₂ j₂ - principalTurn Q j = m * (2 * Real.pi) := by
  obtain ⟨m₁, hm₁⟩ := rotationNumber_integer h₁
  obtain ⟨m₂, hm₂⟩ := rotationNumber_integer h₂
  obtain ⟨m, hm⟩ := rotationNumber_integer h
  refine ⟨m₁ + m₂ - m, ?_, ?_⟩
  · rw [hm₁, hm₂, hm]
    push_cast
    ring
  · have hs := s7i_rotation_ledger_sum Q₁ Q₂ Q j₁ j₂ j e he
    rw [hm₁, hm₂, hm] at hs
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    rw [eq_div_iff hpi] at hs
    rw [← hs]
    push_cast
    ring

/-- A principal-turn-preserving corner correspondence preserves the turns (the form U110-C's selector
laws take), by `principalTurn_sign`. -/
theorem s7i_turn_elim_of_principalTurn_elim {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x) :
    ∀ x, turn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => turn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => turn Q₂ y.1) x := by
  intro x
  rw [← principalTurn_sign h, he x]
  rcases x with y | y
  · simp only [Sum.elim_inl]
    exact principalTurn_sign h₁ y.1
  · simp only [Sum.elim_inr]
    exact principalTurn_sign h₂ y.1

/-- **eq. s7c:rotation-ledger, interlacing line** (`ε = 1`): contact turns of sign `s₀` on all three
carriers ⇒ `rot(L₁) + rot(L₂) − rot(L*) = 0`. -/
theorem s7i_rotation_ledger_interlacing {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn Q₁ j₁ = s₀) (hj₂ : turn Q₂ j₂ = s₀) (hj : turn Q j = s₀) :
    rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q = 0 := by
  obtain ⟨m, hrot, hm⟩ := s7i_ledger_int h₁ h₂ h j₁ j₂ j e he
  have hled := s7i_ledger_of_int hm (s7i_principalTurn_bounds h₁ j₁) (s7i_principalTurn_bounds h₂ j₂)
    (s7i_principalTurn_bounds h j) hs₀ ((principalTurn_sign h₁ j₁).trans hj₁)
    ((principalTurn_sign h₂ j₂).trans hj₂)
  have h0 := hled.1 ((principalTurn_sign h j).trans hj)
  rw [h0] at hm
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hm0 : (m : ℝ) = 0 := by
    rcases mul_eq_zero.mp hm.symm with hm' | hm'
    · exact hm'
    · exact absurd hm' hpi
  rw [hrot, hm0]

/-- **eq. s7c:rotation-ledger, noninterlacing line** (`ε = 0`): half contact turns of sign `s₀`, full
contact turn of sign `−s₀` ⇒ `rot(L₁) + rot(L₂) − rot(L*) = s₀` (the full-turn correction). -/
theorem s7i_rotation_ledger_noninterlacing {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn Q₁ j₁ = s₀) (hj₂ : turn Q₂ j₂ = s₀) (hj : turn Q j = -s₀) :
    rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q = (s₀ : ℝ) := by
  obtain ⟨m, hrot, hm⟩ := s7i_ledger_int h₁ h₂ h j₁ j₂ j e he
  have hled := s7i_ledger_of_int hm (s7i_principalTurn_bounds h₁ j₁) (s7i_principalTurn_bounds h₂ j₂)
    (s7i_principalTurn_bounds h j) hs₀ ((principalTurn_sign h₁ j₁).trans hj₁)
    ((principalTurn_sign h₂ j₂).trans hj₂)
  have h0 := hled.2 ((principalTurn_sign h j).trans hj)
  rw [h0] at hm
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hm0 : (m : ℝ) = (s₀ : ℝ) := by
    have : (2 * Real.pi) * (s₀ : ℝ) = (2 * Real.pi) * (m : ℝ) := by rw [hm]; ring
    exact (mul_left_cancel₀ hpi this).symm
  rw [hrot, hm0]

/-! #### The `R`-identities: same-sign uniformity puts the three rotations on one ray (lem:uniformrot) -/

/-- lem:uniformrot on a uniform polygon of sign `τ`: `τ · rot ≥ 1`, hence `|rot| = τ · rot`. -/
theorem s7i_rotation_on_ray_of_uniform {k : ℕ} [NeZero k] (hk : 3 ≤ k) {Q : LabelledTuple k}
    (h : Regular Q) {τ : SignType} (hτ : τ ≠ 0) (hall : ∀ i, turn Q i = τ) :
    1 ≤ (τ : ℝ) * rotationNumber Q ∧ |rotationNumber Q| = (τ : ℝ) * rotationNumber Q := by
  have hne : ∀ i, turn Q i ≠ 0 := fun i => by rw [hall i]; exact hτ
  have hu := uniform_rotation hk Q h hne
  rcases s7i_signType_cases hτ with rfl | rfl
  · have h1 := hu.1 hall
    simp only [SignType.coe_one, one_mul]
    exact ⟨h1, abs_of_pos (by linarith)⟩
  · have h1 := hu.2.1 hall
    simp only [SignType.coe_neg_one, neg_mul, one_mul]
    exact ⟨by linarith, abs_of_neg (by linarith)⟩

/-- lem:uniformrot on a one-dissent polygon (one turn `−τ` at `j₀`, all others `τ`): `τ · rot ≥ 1`,
hence `|rot| = τ · rot`. -/
theorem s7i_rotation_on_ray_of_dissent {k : ℕ} [NeZero k] (hk : 3 ≤ k) {Q : LabelledTuple k}
    (h : Regular Q) {τ : SignType} (hτ : τ ≠ 0) (j₀ : ZMod k) (h0 : turn Q j₀ = -τ)
    (hrest : ∀ i, i ≠ j₀ → turn Q i = τ) :
    1 ≤ (τ : ℝ) * rotationNumber Q ∧ |rotationNumber Q| = (τ : ℝ) * rotationNumber Q := by
  have hne : ∀ i, turn Q i ≠ 0 := by
    intro i
    by_cases hi : i = j₀
    · rw [hi, h0]
      exact s7i_neg_signType_ne_zero hτ
    · rw [hrest i hi]
      exact hτ
  have hu := uniform_rotation hk Q h hne
  rcases s7i_signType_cases hτ with rfl | rfl
  · have h1 := hu.2.2.1 ⟨j₀, h0, hrest⟩
    simp only [SignType.coe_one, one_mul]
    exact ⟨h1, abs_of_pos (by linarith)⟩
  · have h1 := hu.2.2.2 ⟨j₀, by rw [h0, neg_neg], hrest⟩
    simp only [SignType.coe_neg_one, neg_mul, one_mul]
    exact ⟨by linarith, abs_of_neg (by linarith)⟩

/-- **eq. s7c:interlacing-absolute** (sm-4:655-663): in a live interlacing row all three contact carriers
are uniform of the contact sign `s₀` (U110-C `s7c_uniform_halves_of_interlacing`); the ledger and
lem:uniformrot give `R_L = R₁ + R₂` (`R = |rot|`). -/
theorem s7i_interlacing_absolute {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    (hk₁ : 3 ≤ k₁) (hk₂ : 3 ≤ k₂) (hk : 3 ≤ k)
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hall₁ : ∀ i, turn Q₁ i = s₀) (hall₂ : ∀ i, turn Q₂ i = s₀) (hall : ∀ i, turn Q i = s₀) :
    |rotationNumber Q| = |rotationNumber Q₁| + |rotationNumber Q₂| := by
  have hled := s7i_rotation_ledger_interlacing h₁ h₂ h e he hs₀ (hall₁ j₁) (hall₂ j₂) (hall j)
  obtain ⟨_, ha₁⟩ := s7i_rotation_on_ray_of_uniform hk₁ h₁ hs₀ hall₁
  obtain ⟨_, ha₂⟩ := s7i_rotation_on_ray_of_uniform hk₂ h₂ hs₀ hall₂
  obtain ⟨_, ha⟩ := s7i_rotation_on_ray_of_uniform hk h hs₀ hall
  rw [ha₁, ha₂, ha, ← mul_add]
  congr 1
  linarith

/-- **eq. s7c:noninterlacing-rotation** (sm-4:748-757): in a live noninterlacing row the full carrier is
uniform of sign `τ = −s₀` and each half has exactly one dissent, its contact corner of sign `s₀`
(U110-C `s7c_dissent_halves_of_noninterlacing`); lem:uniformrot puts all three rotations on the `τ` ray
and the ledger, multiplied by `τ`, gives `R₁ + R₂ − R_L = τ s₀ = −1`. -/
theorem s7i_noninterlacing_absolute {k₁ k₂ k : ℕ} [NeZero k₁] [NeZero k₂] [NeZero k]
    (hk₁ : 3 ≤ k₁) (hk₂ : 3 ≤ k₂) (hk : 3 ≤ k)
    {Q₁ : LabelledTuple k₁} {Q₂ : LabelledTuple k₂} {Q : LabelledTuple k}
    (h₁ : Regular Q₁) (h₂ : Regular Q₂) (h : Regular Q)
    {j₁ : ZMod k₁} {j₂ : ZMod k₂} {j : ZMod k}
    (e : {i : ZMod k₁ // i ≠ j₁} ⊕ {i : ZMod k₂ // i ≠ j₂} ≃ {i : ZMod k // i ≠ j})
    (he : ∀ x, principalTurn Q (e x).1 =
      Sum.elim (fun y : {i : ZMod k₁ // i ≠ j₁} => principalTurn Q₁ y.1)
        (fun y : {i : ZMod k₂ // i ≠ j₂} => principalTurn Q₂ y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn Q₁ j₁ = s₀) (hrest₁ : ∀ i, i ≠ j₁ → turn Q₁ i = -s₀)
    (hj₂ : turn Q₂ j₂ = s₀) (hrest₂ : ∀ i, i ≠ j₂ → turn Q₂ i = -s₀)
    (hall : ∀ i, turn Q i = -s₀) :
    |rotationNumber Q₁| + |rotationNumber Q₂| - |rotationNumber Q| = -1 := by
  have hled := s7i_rotation_ledger_noninterlacing h₁ h₂ h e he hs₀ hj₁ hj₂ (hall j)
  have hτ : -s₀ ≠ 0 := s7i_neg_signType_ne_zero hs₀
  obtain ⟨_, ha₁⟩ := s7i_rotation_on_ray_of_dissent hk₁ h₁ hτ j₁ (by rw [hj₁, neg_neg]) hrest₁
  obtain ⟨_, ha₂⟩ := s7i_rotation_on_ray_of_dissent hk₂ h₂ hτ j₂ (by rw [hj₂, neg_neg]) hrest₂
  obtain ⟨_, ha⟩ := s7i_rotation_on_ray_of_uniform hk h hτ hall
  rw [ha₁, ha₂, ha]
  have hsq : (s₀ : ℝ) * (s₀ : ℝ) = 1 := by
    rcases s7i_signType_cases hs₀ with rfl | rfl <;> simp
  have hc : ((-s₀ : SignType) : ℝ) = -(s₀ : ℝ) := by
    rcases s7i_signType_cases hs₀ with rfl | rfl <;> simp
  rw [hc]
  have : -(s₀ : ℝ) * (rotationNumber Q₁ + rotationNumber Q₂ - rotationNumber Q) = -(s₀ : ℝ) * (s₀ : ℝ) := by
    rw [hled]
  linear_combination this - hsq

/-! #### The ledger on carriers (`carrierRotation`, `carrierRotationInt`; def:uniform, def:C) -/

/-- The turn-preserving (SignType) correspondence of U110-C from the principal-turn-preserving one, on
corner polygons of carriers of decompositions. -/
theorem s7i_carrier_turn_elim (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x) :
    ∀ x, turn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x :=
  s7i_turn_elim_of_principalTurn_elim (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁)
    (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂) (ccpCornerPolygon_regular hn hP hS q) e he

/-- eq. s7c:rotation-ledger on carriers, interlacing line: `r_{L₁} + r_{L₂} − r_{L*} = 0`. -/
theorem s7i_carrierRotation_ledger_interlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (hj : turn (ccpCornerPolygon hn hP S q) j = s₀) :
    carrierRotation hn₁ hP₁ S₁ q₁ + carrierRotation hn₂ hP₂ S₂ q₂ - carrierRotation hn hP S q = 0 :=
  s7i_rotation_ledger_interlacing (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁)
    (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂) (ccpCornerPolygon_regular hn hP hS q) e he hs₀ hj₁ hj₂ hj

/-- eq. s7c:rotation-ledger on carriers, noninterlacing line: `r_{L₁} + r_{L₂} − r_{L*} = s₀`. -/
theorem s7i_carrierRotation_ledger_noninterlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (hj : turn (ccpCornerPolygon hn hP S q) j = -s₀) :
    carrierRotation hn₁ hP₁ S₁ q₁ + carrierRotation hn₂ hP₂ S₂ q₂ - carrierRotation hn hP S q = (s₀ : ℝ) :=
  s7i_rotation_ledger_noninterlacing (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁)
    (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂) (ccpCornerPolygon_regular hn hP hS q) e he hs₀ hj₁ hj₂ hj

/-- **eq. s7c:interlacing-absolute on carriers, in ℤ** (`R = |r_Q|` as def:C's `carrierRotationInt`):
three uniform carriers of the contact sign `s₀` ⇒ `R_{L*} = R_{L₁} + R_{L₂}`. -/
theorem s7i_carrierRotationInt_interlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hall₁ : ∀ i, turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = s₀)
    (hall₂ : ∀ i, turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = s₀)
    (hall : ∀ i, turn (ccpCornerPolygon hn hP S q) i = s₀) :
    |carrierRotationInt hn hP S q| = |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| := by
  have hR := s7i_interlacing_absolute (ccpCornerCount_ge_three hn₁ hP₁ hS₁ q₁)
    (ccpCornerCount_ge_three hn₂ hP₂ hS₂ q₂) (ccpCornerCount_ge_three hn hP hS q)
    (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁) (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂)
    (ccpCornerPolygon_regular hn hP hS q) e he hs₀ hall₁ hall₂ hall
  have hc : ((|carrierRotationInt hn hP S q| : ℤ) : ℝ) =
      ((|carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| : ℤ) : ℝ) := by
    push_cast
    rw [carrierRotationInt_cast hn hP hS q, carrierRotationInt_cast hn₁ hP₁ hS₁ q₁,
      carrierRotationInt_cast hn₂ hP₂ hS₂ q₂]
    exact hR
  exact_mod_cast hc

/-- **eq. s7c:noninterlacing-rotation on carriers, in ℤ**: full carrier uniform of sign `−s₀`, halves
one-dissent at their contact corners (sign `s₀`) ⇒ `R_{L₁} + R_{L₂} − R_{L*} = −1`. -/
theorem s7i_carrierRotationInt_noninterlacing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁) {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (q₁ : Component hn₁ hP₁ S₁)
    {n₂ : ℕ} [NeZero n₂] (hn₂ : 3 ≤ n₂) {P₂ : LabelledTuple n₂} (hP₂ : Generic P₂)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₂ : Component hn₂ hP₂ S₂)
    {j : ZMod (ccpCornerCount hn hP S q)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hP S q) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hrest₁ : ∀ i, i ≠ j₁ → turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = -s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (hrest₂ : ∀ i, i ≠ j₂ → turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = -s₀)
    (hall : ∀ i, turn (ccpCornerPolygon hn hP S q) i = -s₀) :
    |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| - |carrierRotationInt hn hP S q| = -1 := by
  have hR := s7i_noninterlacing_absolute (ccpCornerCount_ge_three hn₁ hP₁ hS₁ q₁)
    (ccpCornerCount_ge_three hn₂ hP₂ hS₂ q₂) (ccpCornerCount_ge_three hn hP hS q)
    (ccpCornerPolygon_regular hn₁ hP₁ hS₁ q₁) (ccpCornerPolygon_regular hn₂ hP₂ hS₂ q₂)
    (ccpCornerPolygon_regular hn hP hS q) e he hs₀ hj₁ hrest₁ hj₂ hrest₂ hall
  have hc : ((|carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hP S q| : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by
    push_cast
    rw [carrierRotationInt_cast hn hP hS q, carrierRotationInt_cast hn₁ hP₁ hS₁ q₁,
      carrierRotationInt_cast hn₂ hP₂ hS₂ q₂]
    exact hR
  exact_mod_cast hc

/-! #### The slot identities (pure ℤ; def:C `d_Q = 1 − m_Q − |r_Q|` with the writhe `w = m` of the
positive lift, `positiveLift_writhe_eq_carrierCrossingCount`) -/

/-- `k_H = k_L − 2` (sm-4:629-632): `w_H = w_L + 2`, `R_H = R_L` (eq. s7c:full-rotation). -/
theorem s7i_high_slot {kL kH wL wH RL RH : ℤ} (hkL : kL = 1 - wL - RL) (hkH : kH = 1 - wH - RH)
    (hw : wH = wL + 2) (hR : RH = RL) : kH = kL - 2 := by
  omega

/-- **eq. s7c:interlacing-slot** (sm-4:665-670): `w_L = w₁ + w₂ + 2ℓ − 1` and `R_L = R₁ + R₂` ⇒
`k_L = K − 2ℓ` with `K = k₁ + k₂`. -/
theorem s7i_interlacing_slot {kL k₁ k₂ wL w₁ w₂ RL R₁ R₂ ℓ : ℤ}
    (hkL : kL = 1 - wL - RL) (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂)
    (hw : wL = w₁ + w₂ + 2 * ℓ - 1) (hR : RL = R₁ + R₂) :
    kL = k₁ + k₂ - 2 * ℓ := by
  omega

/-- **eq. s7c:noninterlacing-slot** (sm-4:758-762): `w_L = w₁ + w₂ + 2ℓ` and `R₁ + R₂ − R_L = −1` ⇒
`K − k_L = 2ℓ + 2`. -/
theorem s7i_noninterlacing_slot {kL k₁ k₂ wL w₁ w₂ RL R₁ R₂ ℓ : ℤ}
    (hkL : kL = 1 - wL - RL) (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂)
    (hw : wL = w₁ + w₂ + 2 * ℓ) (hR : R₁ + R₂ - RL = -1) :
    k₁ + k₂ - kL = 2 * ℓ + 2 := by
  omega

/-- **eqs. s7c:different-low-slot / s7c:different-high-slot** (sm-4:827-832): `w_L = w₁ + w₂`,
`w_H = w₁ + w₂ + 2`, `R₁ + R₂ − R_L = −1`, `R_H = R_L` ⇒ `k_L = K − 2`, `k_H = K − 4`. -/
theorem s7i_different_slot {kL kH k₁ k₂ wL wH w₁ w₂ RL RH R₁ R₂ : ℤ}
    (hkL : kL = 1 - wL - RL) (hkH : kH = 1 - wH - RH) (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂)
    (hwL : wL = w₁ + w₂) (hwH : wH = w₁ + w₂ + 2) (hR : R₁ + R₂ - RL = -1) (hRH : RH = RL) :
    kL = k₁ + k₂ - 2 ∧ kH = k₁ + k₂ - 4 := by
  omega

end S7IRotationLedger

/-- The bigon branch (sm-4:407-874): two-newborn sector `B = (1−ε)J` (contact triangle: a crossing-free
uniform carrier, `corner_values_i`), universal skein extraction eq. s7c:universal-extraction (lp:core
skein, R-II deletion, oriented smoothing), lem:homflyrows two-component row, the rotation ledger, and the
two floor-dependent branches (interlacing: `Ω_H − Ω_L = −ω₁ω₂`; noninterlacing: every returned row zero,
the one-newborn rows by cb:singleton).  `a_floor` enters at the two half contact carriers (uniform for
`ε = 1`, one-dissent for `ε = 0`), read as carriers of the decompositions `T_i` of the generic halves
`λ_i` (sm-4:800-835); cb:singleton enters at the one-newborn rows (sm-4:777-783) — both printed
dependencies are explicit parameters. -/
theorem s7_bigon_law_at (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (g : WallGerm n) (M a : ZMod n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry

/-! Two pure-algebra leaves of the bigon branch, stated now on the accepted ring (units U110-G / U110-J). -/

/-! ### Helpers of unit U110-G (prefix `s7g_`): coefficient shifts by the monomial units of `R`, and the
skein extraction on actual diagrams through the accepted record-level smoothing
(`exists_smoothing_record_visit`, SM/Smoothing.lean) and `lp_core`'s recursion `P_recursion_pos`.
Go/no-go of the bigon route (U_S7G_REPORT.md): the skein triple at the positive contact crossing `q`
and the identification of the oriented smoothing with the record smoothing are AVAILABLE generically
(`s7g_skein_at_positive`); the R-II deletion of the bigon `{x, y}` and the R-I deletion of the curl `y`
need `RIIData`/`RIData` witnesses on the actual polygonal lifts, for which NO generic constructor exists
in the accepted library (the precedents are the slot-diagram-specific `riiData_of` of SM/FrontRowsW3.lean
and the kink INSERTION `k2_ri` of SM/Curl.lean); they enter below only as hypotheses
(`s7g_switch_value_of_rii`, `s7g_value_of_ri`). -/

/-- `[a^d z^k] (a^p z^q · f) = [a^{d−p} z^{k−q}] f`: multiplication by a monomial unit shifts every
coefficient (Mathlib `AddMonoidAlgebra.coeff_single_mul_apply`).  There is no shift lemma for
`coeffAt` in SM/LinkLaurentRing.lean; `coeffAt_mul_of_max_weight` :719 is the nearest tool. -/
theorem s7g_coeffAt_single_mul (p q d k : ℤ) (f : R) :
    coeffAt d k (AddMonoidAlgebra.single (p, q) (1 : ℤ) * f) = coeffAt (d - p) (k - q) f := by
  unfold coeffAt
  have h : ((d, k) : ℤ × ℤ) = (p, q) + (d - p, k - q) := by ext <;> simp
  rw [h, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_add_cancel_left]

/-- `[a^d z^k] (a f) = [a^{d−1} z^k] f`. -/
theorem s7g_coeffAt_a_mul (d k : ℤ) (f : R) : coeffAt d k (R.a * f) = coeffAt (d - 1) k f := by
  rw [R.a, s7g_coeffAt_single_mul]; congr 1; ring

/-- `[a^d z^k] (a⁻¹ f) = [a^{d+1} z^k] f`. -/
theorem s7g_coeffAt_aInv_mul (d k : ℤ) (f : R) : coeffAt d k (R.aInv * f) = coeffAt (d + 1) k f := by
  rw [R.aInv, s7g_coeffAt_single_mul]; congr 1; ring

/-- `[a^d z^k] (z f) = [a^d z^{k−1}] f`. -/
theorem s7g_coeffAt_z_mul (d k : ℤ) (f : R) : coeffAt d k (R.z * f) = coeffAt d (k - 1) f := by
  rw [R.z, s7g_coeffAt_single_mul]; congr 1; ring

/-- `[a^d z^k] (z⁻¹ f) = [a^d z^{k+1}] f`. -/
theorem s7g_coeffAt_zInv_mul (d k : ℤ) (f : R) : coeffAt d k (R.zInv * f) = coeffAt d (k + 1) f := by
  rw [R.zInv, s7g_coeffAt_single_mul]; congr 1; ring

/-- eq. s7c:universal-extraction as a ring identity (the body of the leaf `s7_universal_extraction`):
from `F_H = a⁻² F_L + a⁻¹ z F_A`, `[a^{k−2} z⁰] F_H = [a^k z⁰] F_L + [a^{k−1} z⁻¹] F_A`. -/
theorem s7g_extraction_of_skein (FH FL FA : R) (k : ℤ)
    (hsk : FH = R.aInv * R.aInv * FL + R.aInv * R.z * FA) :
    coeffAt (k - 2) 0 FH = coeffAt k 0 FL + coeffAt (k - 1) (-1) FA := by
  subst hsk
  rw [coeffAt_add, mul_assoc, mul_assoc, s7g_coeffAt_aInv_mul, s7g_coeffAt_aInv_mul,
    s7g_coeffAt_aInv_mul, s7g_coeffAt_z_mul]
  congr 2 <;> ring

/-- **The skein triple at a positive crossing, with the record-level smoothing** (sm-4:596-608 "The
actual oriented smoothing is the tagged `D_A`. Thus the skein relation at `q` first gives
`a F_H − a⁻¹ F_L = z F_A`, then `F_H = a⁻² F_L + a⁻¹ z F_A`"): for every diagram `D`, positive
crossing `x` and occurrence `v` of `x`, some oriented smoothing `D₀` of `D` at `x` has the record
`D.record.smooth v` (accepted `exists_smoothing_record_visit`), `(D, D^{sw}, D₀)` is a skein triple
(`IsSkeinTriple`, design decision D3: `D₋` is literally the switch), and eq. s7c:universal-skein holds
with `F_L` read as `P (D.switch x)` (`P_recursion_pos`). -/
theorem s7g_skein_at_positive (D : Diagram) (x : D.Γ.Crossing) (hx : D.IsPositive x)
    (v : D.Γ.Visit) (hv : v.1 = x) :
    ∃ D₀ : Diagram, IsSkeinTriple D (D.switch x) D₀ ∧ IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth v)) ∧
      P D = R.aInv * R.aInv * P (D.switch x) + R.aInv * R.z * P D₀ := by
  obtain ⟨D₀, h₀, hrec⟩ := exists_smoothing_record_visit D x v hv
  exact ⟨D₀, ⟨x, hx, rfl, h₀⟩, h₀, hrec, P_recursion_pos h₀ hx⟩

/-- The record of the switched diagram, identified through the record-level switch (accepted
`Diagram.switchRecordIso`): a record isomorphism out of `D.record.switch v` is one out of
`(D.switch x).record`. -/
theorem s7g_switch_record_iso (D : Diagram) (x : D.Γ.Crossing) (v : D.Γ.Visit) (hv : v.1 = x)
    {ρ : Record} (h : Nonempty (RecordIso (D.record.switch v) ρ)) :
    Nonempty (RecordIso (D.switch x).record ρ) :=
  h.elim fun ι => ⟨(D.switchRecordIso x v hv).trans ι⟩

/-- The value of the switch side after an R-II deletion and a record identification (sm-4:600-606
"Switching the positive contact crossing `q` makes the same strand over at both crossings ... this is
the actual ordinary R-II template ... Delete it using local LM invariance. The remaining diagram has the
same complete decorated record as `D_L` ...; Lemma rp:record-polynomial gives its value `F_L`"):
`P (D^{sw}) = P D_L` from `RII D_red D^{sw}` (`lp_core.reidemeister_II`) and
`D_red.record ≅ D_L.record` (`presentations`).  The witness `RII D_red (D.switch x)` is the open
geometric input of the bigon route (U_S7G_REPORT.md, verdict). -/
theorem s7g_switch_value_of_rii (D Dred DL : Diagram) (x : D.Γ.Crossing)
    (hR : RII Dred (D.switch x)) (hrec : Nonempty (RecordIso Dred.record DL.record)) :
    P (D.switch x) = P DL :=
  (P_reidemeister_II hR).symm.trans (presentations _ _ hrec)

/-- The value after an R-I deletion and a record identification (sm-4:491-503, the `ε = 0` branch:
"component 1 contains the permitted positive self R-I curl `y`; delete exactly that curl ... The local
LM R-I equality applies to the entire two-component diagram"): `P D = P D_L` from `RI D_red D`
(`lp_core.reidemeister_I`) and `D_red.record ≅ D_L.record`.  The witness `RI D_red D_A` is the second
open geometric input (U_S7G_REPORT.md). -/
theorem s7g_value_of_ri (D Dred DL : Diagram) (hR : RI Dred D)
    (hrec : Nonempty (RecordIso Dred.record DL.record)) : P D = P DL :=
  (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)

/-- eq. s7c:universal-extraction on an actual diagram: at a positive crossing `x` of `D` whose switch
side has value `F_L`, some oriented smoothing `D₀` (record `D.record.smooth v`) satisfies
`[a^{k−2} z⁰] P D = [a^k z⁰] F_L + [a^{k−1} z⁻¹] P D₀`. -/
theorem s7g_extraction_at_positive (D : Diagram) (x : D.Γ.Crossing) (hx : D.IsPositive x)
    (v : D.Γ.Visit) (hv : v.1 = x) (FL : R) (hL : P (D.switch x) = FL) (k : ℤ) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth v)) ∧
      coeffAt (k - 2) 0 (P D) = coeffAt k 0 FL + coeffAt (k - 1) (-1) (P D₀) := by
  obtain ⟨D₀, -, h₀, hrec, hsk⟩ := s7g_skein_at_positive D x hx v hv
  refine ⟨D₀, h₀, hrec, ?_⟩
  rw [← hL]
  exact s7g_extraction_of_skein _ _ _ k hsk

/-- The skein triple on the actual positive lift of a carrier (`D_H = positiveLift`, every crossing
positive by `positiveLift_isPositive`), with `F_H = cornerHomfly` (`P_eq_homfly`): at EVERY crossing
`x` of the lift, `H⁺_Q = a⁻² P (D_H^{sw x}) + a⁻¹ z P D₀` with `D₀` an oriented smoothing of record
`(positiveLift …).record.smooth v`. -/
theorem s7g_cornerHomfly_skein (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S)
    (x : (positiveLift hn hP S q hS).Γ.Crossing) (v : (positiveLift hn hP S q hS).Γ.Visit)
    (hv : v.1 = x) :
    ∃ D₀ : Diagram, IsSkeinTriple (positiveLift hn hP S q hS) ((positiveLift hn hP S q hS).switch x) D₀ ∧
      IsOrientedSmoothing (positiveLift hn hP S q hS) x D₀ ∧
      Nonempty (RecordIso D₀.record ((positiveLift hn hP S q hS).record.smooth v)) ∧
      cornerHomfly hn hP S q hS =
        R.aInv * R.aInv * SM.P ((positiveLift hn hP S q hS).switch x) + R.aInv * R.z * SM.P D₀ := by
  unfold cornerHomfly
  rw [← P_eq_homfly]
  exact s7g_skein_at_positive _ x (positiveLift_isPositive hn hP S q hS x) v hv

/-- eq. s7c:universal-extraction on the actual positive lift: `[a^{k−2} z⁰] H⁺_Q = [a^k z⁰] F_L +
[a^{k−1} z⁻¹] P D₀` whenever the switch side at `x` has value `F_L` (to be supplied by
`s7g_switch_value_of_rii` once the R-II witness exists). -/
theorem s7g_cornerCoefficient_extraction (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S)
    (x : (positiveLift hn hP S q hS).Γ.Crossing) (v : (positiveLift hn hP S q hS).Γ.Visit)
    (hv : v.1 = x) (FL : R) (hL : SM.P ((positiveLift hn hP S q hS).switch x) = FL) (k : ℤ) :
    ∃ D₀ : Diagram, IsOrientedSmoothing (positiveLift hn hP S q hS) x D₀ ∧
      Nonempty (RecordIso D₀.record ((positiveLift hn hP S q hS).record.smooth v)) ∧
      coeffAt (k - 2) 0 (cornerHomfly hn hP S q hS) =
        coeffAt k 0 FL + coeffAt (k - 1) (-1) (SM.P D₀) := by
  unfold cornerHomfly
  rw [← P_eq_homfly]
  exact s7g_extraction_at_positive _ x (positiveLift_isPositive hn hP S q hS x) v hv FL hL k


/-- eq. s7c:universal-extraction: from `F_H = a⁻² F_L + a⁻¹ z F_A` (the skein relation at the positive
contact crossing, `lp_core.skein`), `[a^{k−2} z⁰] F_H = [a^k z⁰] F_L + [a^{k−1} z⁻¹] F_A`. -/
theorem s7_universal_extraction (FH FL FA : R) (k : ℤ)
    (hsk : FH = R.aInv * R.aInv * FL + R.aInv * R.z * FA) :
    coeffAt (k - 2) 0 FH = coeffAt k 0 FL + coeffAt (k - 1) (-1) FA := by
  exact s7g_extraction_of_skein FH FL FA k hsk

/-- eq. s7c:interlacing-coefficient-result, the algebra: if `f, g ≠ 0` have `a`-floors `k₁, k₂` and no
negative `z`-exponents (`a_floor` and lp:core's `knot_support` at the two half contact carriers), then
`[a^{k₁+k₂−2} z⁰](fg) = 0` and `[a^{k₁+k₂} z⁰](fg) = [a^{k₁} z⁰]f · [a^{k₂} z⁰]g`. -/
theorem s7_corner_product {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) {k₁ k₂ : ℤ}
    (h₁ : k₁ ≤ mindegAZ f) (h₂ : k₂ ≤ mindegAZ g)
    (hz₁ : ∀ d k, coeffAt d k f ≠ 0 → 0 ≤ k) (hz₂ : ∀ d k, coeffAt d k g ≠ 0 → 0 ≤ k) :
    coeffAt (k₁ + k₂ - 2) 0 (f * g) = 0 ∧
      coeffAt (k₁ + k₂) 0 (f * g) = coeffAt k₁ 0 f * coeffAt k₂ 0 g := by
  refine ⟨coeffAt_mul_eq_zero_of_lt_floor hf hg h₁ h₂ (by omega), ?_⟩
  -- 2nd conjunct (assembler-provided, wave-1 assembly 2026-09-15): the `(k₁+k₂, 0)` monomial of
  -- `f * g` is reached by exactly one pair of support monomials, `(k₁, 0) + (k₂, 0)`: the `a`-floors
  -- force `a.1 = k₁`, `b.1 = k₂`, and the absence of negative `z`-exponents forces `a.2 = b.2 = 0`
  -- (Mathlib `AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd`, the device of `coeff_mul_of_max_weight`).
  have hsum : ((k₁ + k₂, 0) : ℤ × ℤ) = (k₁, 0) + (k₂, 0) := by simp
  show (f * g).coeff (k₁ + k₂, 0) = f.coeff (k₁, 0) * g.coeff (k₂, 0)
  rw [hsum]
  apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
  intro a b ha hb hab
  have ha' : coeffAt a.1 a.2 f ≠ 0 := Finsupp.mem_support_iff.1 ha
  have hb' : coeffAt b.1 b.2 g ≠ 0 := Finsupp.mem_support_iff.1 hb
  have ha1 : mindegAZ f ≤ a.1 := (mindegAZ_spec hf).2 a.1 a.2 ha'
  have hb1 : mindegAZ g ≤ b.1 := (mindegAZ_spec hg).2 b.1 b.2 hb'
  have ha2 : 0 ≤ a.2 := hz₁ a.1 a.2 ha'
  have hb2 : 0 ≤ b.2 := hz₂ b.1 b.2 hb'
  have h1 : a.1 + b.1 = k₁ + k₂ := by simpa using congrArg Prod.fst hab
  have h2 : a.2 + b.2 = 0 := by simpa using congrArg Prod.snd hab
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp only <;> omega

/-- **Row 110, conditional on thm:floor AND cb:singleton** (the printed dependency list of
tools/claims.py; library material).  PROVED from the two branch leaves: the wall is of bigon or sliding
type (`vertexEdge_bigon_or_sliding`); both side parameters are moved below the branch radius by chamber
constancy along each side (`cornerStateSum_side_eq`). -/
theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data := by
  refine ⟨?_⟩
  intro n _ hn g M a h h₁ h₂ tp tm
  obtain ⟨δ, hδ, hlaw⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂) := by
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact s7_bigon_law_at hF hsing hn g M a hb h₁ h₂
    · exact s7_sliding_law_at hn g M a hs h₁ h₂
  have hr := g.radius_pos
  let t : g.SideParameter := ⟨min δ g.radius / 2, by
    constructor
    · have := lt_min hδ hr; linarith
    · have := min_le_right δ g.radius; linarith⟩
  have ht : t.val < δ := by
    show min δ g.radius / 2 < δ
    have := min_le_left δ g.radius; linarith
  rw [cornerStateSum_side_eq hn g true tp t, cornerStateSum_side_eq hn g false tm t]
  exact hlaw t ht

/-- **Row 110, conditional on the floor alone** (the row theorem `SM.thm_C_S7 := thm_C_S7_of_floor
SM.thm_floor` once row 100 lands). -/
theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=
  thm_C_S7_of hF (cb_singleton_of_floor hF)

end VertexEdge

/-! ## §5 Row 112 thm:C-soft (sm-4:984-991; proof 992-1147) — fixed target name `SM.thm_C_soft` -/

section Soft

open SoftDuplication

variable {n : ℕ} [NeZero n]

/-- **thm:C-soft as printed**, one field: "Let `P` be generic, `j` a vertex, `q` admissible, and `P_ε` the
soft insertion of def:soft, with attachment signs `χ_±`. Then for all sufficiently small `ε > 0`,
`C(P_ε) = ((χ₋ + χ₊)/2) C(P)`."  Shape of the consumer thm:uniqueness (e) (`UniquenessHypotheses.soft`,
SM/Uniqueness.lean:72): `SoftAdmissible P j q` (def:soft), `softInsertion P j q ε = P_ε`, the multiplier
`softAmplitudeMultiplier P j q = (χ₋ + χ₊)/2 ∈ ℚ` (SoftAmplitudeSectors.lean:96, def:soft's
`softAttachmentMinus/Plus`; FR-CC-11), the ℤ-valued `C` cast to `ℚ`; "for all sufficiently small `ε > 0`"
= `∃ ε₁ > 0, ∀ ε ∈ (0, ε₁)`; `C(P_ε)` presupposes `P_ε` generic (lem:soft-generic (i)), quantified as
`∀ hQ` (FR-CC-12; the `∃ hQ` form of the accepted thm:A-soft is the companion `exists_generic`). -/
structure CSoftData : Prop where
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
        softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)

/-- Companion (the accepted thm:A-soft's shape, `A_lawful.soft_theorem`): genericity of `P_ε` as part of
the conclusion, from lem:soft-generic (i) (`soft_family_generic`, SoftGenericLemma.lean:36). -/
theorem CSoftData.exists_generic (hD : CSoftData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
  obtain ⟨ε₁, hε₁, hall⟩ := hD.soft_theorem n hn P hP j q hq
  obtain ⟨δ, hδ, B, hgen⟩ := (soft_family_generic hn hP j q hq).2.2.2.2.2
  refine ⟨min ε₁ δ, lt_min hε₁ hδ, fun ε hε hlt => ?_⟩
  obtain ⟨hQ, -⟩ := hgen ε hε (lt_of_lt_of_le hlt (min_le_right _ _))
  exact ⟨hQ, hall ε hε (lt_of_lt_of_le hlt (min_le_left _ _)) hQ⟩

/-- Companion (the printed proof's three sector multipliers, sm-4:1123-1127): in `ℤ`,
`2 C(P_ε) = (χ₋ + χ₊) C(P)`. -/
theorem CSoftData.doubled (hD : CSoftData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      2 * cornerStateSum (by omega : 3 ≤ n + 1) hQ =
        ((softAttachmentMinus P j q : ℤ) + (softAttachmentPlus P j q : ℤ)) * cornerStateSum hn hP := by
  obtain ⟨ε₁, hε₁, hall⟩ := hD.soft_theorem n hn P hP j q hq
  refine ⟨ε₁, hε₁, fun ε hε hε' hQ => ?_⟩
  have heq := hall ε hε hε' hQ
  have h2 : (2 : ℚ) * (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
      (((softAttachmentMinus P j q : ℤ) : ℚ) + ((softAttachmentPlus P j q : ℤ) : ℚ)) *
        (cornerStateSum hn hP : ℚ) := by
    rw [heq, softAmplitudeMultiplier]; ring
  exact_mod_cast h2

/-! ### Leaves of row 112 (the three printed sectors; units U112-A … U112-D). Prefix `sft_`. -/

omit [NeZero n] in
/-- The turn at a vertex of a generic polygon is nonzero (def:generic (G1) at the triple `(j−1, j, j+1)`,
distinct for `n ≥ 3`); needed to name the sectors. -/
theorem sft_turn_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) :
    turn P j ≠ 0 := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    intro h
    have hd : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd one_pos hd
    omega
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos hd
    omega
  apply hP.1 (j - 1) j (j + 1)
  · intro h; apply h1; linear_combination -h
  · intro h; apply h1; linear_combination -h
  · intro h; apply h2; linear_combination -h

/-! ### U112-A helpers (prefix `sfta_`): the soft mark transport and the carrier correspondence for
common supports (PLAN_FINAL.md §3.4, §4 U112-A).

An abstract *insertion mark transport* `sfta_InsertMarkTransport hn hP hQ` from the generic `n`-gon `P`
to the generic `(n+1)`-gon `Q` (the `MarkTransport` of SM/CChamber.lean for mark sets differing by
exactly one vertex `new`, inserted right after the attachment vertex `att`) carries the whole Carrier
lane: the cyclic and smoothing successors (`markSuccessor_of_ne/_att/_new`,
`smoothingSuccessor_of_ne/_att/_new`), the cycles (`sameCycle_iff`, `sameCycle_new`), the carriers
(`component : Component ≃ Component`, `component_owner`, `owner_new`), their crossings and `m_Q`,
decompositions, true corners, the mark and corner lists (insertion shape for the carrier through the
attachment, rotation for the others), corner counts, uniformity (`carrierUniform_iff_insertion`,
`carrierUniform_iff_of_ne`, `carrierUniform_iff`), the index set, the corner coefficients, the signed
sum (`sum_transport`), the left-turn count (`leftTurns_transport`) and the state sum up to the sign
`(−1)^{ℓ(Q)+ℓ(P)}` (`cornerStateSum_transport`).  The soft instance `sfta_softTransport` (non-loop
sectors; vertices `softOldIndex j`, new vertex `softNewIndex j`, crossings/visits the accepted
`softInheritedCrossing/Visit`) has its mark-list clause proved by sortedness
(`sfta_soft_markList_insertion`; literal when `j ≠ 0`, one rotation when `j = 0`, where `M_ε` becomes
the label `0`) and its interlacement clause by the visit-order clause of lem:soft-generic
(`sfta_interlaces_transport`); `sfta_soft_data` extracts from `soft_family_generic` on one interval
exactly the hypotheses of `sfta_softTransport` and `sfta_softTransport_markTurn` (vertex turns,
`−χ₋` at `μ_j`, `−χ₊` at `M_ε`, inherited crossing signs). -/

section ListLayer
variable {α β : Type*}

/-- `R` is a rotation of `L` mapped by `f` with `y` inserted immediately after `f a₀`. -/
def sfta_IsInsertion (f : α → β) (a₀ : α) (y : β) (L : List α) (R : List β) : Prop :=
  ∃ L₁ L₂ : List α, L = L₁ ++ a₀ :: L₂ ∧ R.IsRotated (L₁.map f ++ f a₀ :: y :: L₂.map f)

theorem sfta_insert_length (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) :
    (L₁.map f ++ f a :: y :: L₂.map f).length = (L₁ ++ a :: L₂).length + 1 := by
  simp only [List.length_append, List.length_map, List.length_cons]; omega

theorem sfta_insert_perm (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) :
    (L₁.map f ++ f a :: y :: L₂.map f).Perm (y :: (L₁ ++ a :: L₂).map f) := by
  have h := List.perm_middle (l₁ := L₁.map f ++ [f a]) (a := y) (l₂ := L₂.map f)
  simpa only [List.append_assoc, List.singleton_append, List.map_append, List.map_cons] using h

theorem sfta_insert_nodup (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) (hf : Function.Injective f)
    (hL : (L₁ ++ a :: L₂).Nodup) (hy : y ∉ (L₁ ++ a :: L₂).map f) :
    (L₁.map f ++ f a :: y :: L₂.map f).Nodup :=
  (sfta_insert_perm L₁ L₂ a f y).nodup_iff.mpr (List.nodup_cons.mpr ⟨hy, hL.map hf⟩)

theorem sfta_insert_mem (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) (m : β) :
    m ∈ L₁.map f ++ f a :: y :: L₂.map f ↔ m = y ∨ ∃ x ∈ L₁ ++ a :: L₂, f x = m := by
  rw [(sfta_insert_perm L₁ L₂ a f y).mem_iff, List.mem_cons, List.mem_map]

theorem sfta_insert_getElem_le (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) {i : ℕ}
    (hi : i ≤ L₁.length) (h₁ : i < (L₁ ++ a :: L₂).length)
    (h₂ : i < (L₁.map f ++ f a :: y :: L₂.map f).length) :
    (L₁.map f ++ f a :: y :: L₂.map f)[i] = f ((L₁ ++ a :: L₂)[i]) := by
  rcases lt_or_eq_of_le hi with hlt | heq
  · rw [List.getElem_append_left (by simpa using hlt), List.getElem_append_left hlt,
      List.getElem_map]
  · subst heq
    rw [List.getElem_append_right (by simp), List.getElem_append_right le_rfl]
    simp

theorem sfta_insert_getElem_gt (L₁ L₂ : List α) (a : α) (f : α → β) (y : β) {i : ℕ}
    (hi : L₁.length < i) (h₁ : i < (L₁ ++ a :: L₂).length)
    (h₂ : i + 1 < (L₁.map f ++ f a :: y :: L₂.map f).length) :
    (L₁.map f ++ f a :: y :: L₂.map f)[i + 1] = f ((L₁ ++ a :: L₂)[i]) := by
  rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, i - L₁.length = k + 1 := ⟨i - L₁.length - 1, by omega⟩
  have h3 : i + 1 - (L₁.map f).length = k + 2 := by simp only [List.length_map]; omega
  simp only [h3, hk, List.getElem_cons_succ, List.getElem_map]

theorem sfta_insert_getElem_new (L₁ L₂ : List α) (a : α) (f : α → β) (y : β)
    (h₂ : L₁.length + 1 < (L₁.map f ++ f a :: y :: L₂.map f).length) :
    (L₁.map f ++ f a :: y :: L₂.map f)[L₁.length + 1] = y := by
  rw [List.getElem_append_right (by simp)]
  simp

theorem sfta_insert_getElem_att (L₁ L₂ : List α) (a : α) (h₁ : L₁.length < (L₁ ++ a :: L₂).length) :
    (L₁ ++ a :: L₂)[L₁.length] = a := by
  rw [List.getElem_append_right le_rfl]; simp

variable [DecidableEq α] [DecidableEq β]

/-- `next` on a nodup list, with the element given by an index up to a propositional equality. -/
theorem sfta_next_eq_of_getElem {l : List α} (hl : l.Nodup) (i : ℕ) (hi : i < l.length)
    (x : α) (hx : x ∈ l) (he : x = l[i]) :
    l.next x hx = l[(i + 1) % l.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  subst he
  exact List.next_getElem l hl i hi

theorem sfta_insert_next_of_ne (L₁ L₂ : List α) (a : α) (f : α → β) (y : β)
    (hf : Function.Injective f) (hL : (L₁ ++ a :: L₂).Nodup) (hy : y ∉ (L₁ ++ a :: L₂).map f)
    (m : α) (hm : m ∈ L₁ ++ a :: L₂) (hne : m ≠ a) (hmR : f m ∈ L₁.map f ++ f a :: y :: L₂.map f) :
    (L₁.map f ++ f a :: y :: L₂.map f).next (f m) hmR = f ((L₁ ++ a :: L₂).next m hm) := by
  have hR := sfta_insert_nodup L₁ L₂ a f y hf hL hy
  have hlen := sfta_insert_length L₁ L₂ a f y
  have hcL : L₁.length < (L₁ ++ a :: L₂).length := by simp
  obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem hm
  have hic : i ≠ L₁.length := by
    intro h
    apply hne
    rw [← hiL]
    subst h
    exact sfta_insert_getElem_att L₁ L₂ a hcL
  rw [sfta_next_eq_of_getElem hL i hi m hm hiL.symm]
  rcases lt_or_gt_of_ne hic with hlt | hgt
  · have h1 : f m = (L₁.map f ++ f a :: y :: L₂.map f)[i]'(by omega) := by
      rw [sfta_insert_getElem_le L₁ L₂ a f y hlt.le hi, hiL]
    rw [sfta_next_eq_of_getElem hR i (by omega) (f m) hmR h1]
    have hmod1 : (i + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = i + 1 :=
      Nat.mod_eq_of_lt (by omega)
    have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = i + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hmod1, hmod2]
    exact sfta_insert_getElem_le L₁ L₂ a f y (by omega) (by omega) (by omega)
  · have h1 : f m = (L₁.map f ++ f a :: y :: L₂.map f)[i + 1]'(by omega) := by
      rw [sfta_insert_getElem_gt L₁ L₂ a f y hgt hi, hiL]
    rw [sfta_next_eq_of_getElem hR (i + 1) (by omega) (f m) hmR h1]
    by_cases hlast : i + 1 < (L₁ ++ a :: L₂).length
    · have hmod1 : (i + 1 + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = i + 2 :=
        Nat.mod_eq_of_lt (by omega)
      have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = i + 1 := Nat.mod_eq_of_lt hlast
      simp only [hmod1, hmod2]
      exact sfta_insert_getElem_gt L₁ L₂ a f y (by omega) hlast (by omega)
    · have hiN : i + 1 = (L₁ ++ a :: L₂).length := by omega
      have hmod1 : (i + 1 + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = 0 := by
        rw [hlen, hiN]; simp
      have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = 0 := by rw [hiN]; simp
      simp only [hmod1, hmod2]
      exact sfta_insert_getElem_le L₁ L₂ a f y (Nat.zero_le _) (by omega) (by omega)

theorem sfta_insert_next_att (L₁ L₂ : List α) (a : α) (f : α → β) (y : β)
    (hf : Function.Injective f) (hL : (L₁ ++ a :: L₂).Nodup) (hy : y ∉ (L₁ ++ a :: L₂).map f)
    (haR : f a ∈ L₁.map f ++ f a :: y :: L₂.map f) :
    (L₁.map f ++ f a :: y :: L₂.map f).next (f a) haR = y := by
  have hR := sfta_insert_nodup L₁ L₂ a f y hf hL hy
  have hlen := sfta_insert_length L₁ L₂ a f y
  have hcL : L₁.length < (L₁ ++ a :: L₂).length := by simp
  have h1 : f a = (L₁.map f ++ f a :: y :: L₂.map f)[L₁.length]'(by omega) := by
    rw [sfta_insert_getElem_le L₁ L₂ a f y le_rfl hcL, sfta_insert_getElem_att L₁ L₂ a hcL]
  rw [sfta_next_eq_of_getElem hR L₁.length (by omega) (f a) haR h1]
  have hmod : (L₁.length + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = L₁.length + 1 :=
    Nat.mod_eq_of_lt (by omega)
  simp only [hmod]
  exact sfta_insert_getElem_new L₁ L₂ a f y (by omega)

theorem sfta_insert_next_new (L₁ L₂ : List α) (a : α) (f : α → β) (y : β)
    (hf : Function.Injective f) (hL : (L₁ ++ a :: L₂).Nodup) (hy : y ∉ (L₁ ++ a :: L₂).map f)
    (hyR : y ∈ L₁.map f ++ f a :: y :: L₂.map f) (ha : a ∈ L₁ ++ a :: L₂) :
    (L₁.map f ++ f a :: y :: L₂.map f).next y hyR = f ((L₁ ++ a :: L₂).next a ha) := by
  have hR := sfta_insert_nodup L₁ L₂ a f y hf hL hy
  have hlen := sfta_insert_length L₁ L₂ a f y
  have hcL : L₁.length < (L₁ ++ a :: L₂).length := by simp
  have h1 : y = (L₁.map f ++ f a :: y :: L₂.map f)[L₁.length + 1]'(by omega) :=
    (sfta_insert_getElem_new L₁ L₂ a f y (by omega)).symm
  rw [sfta_next_eq_of_getElem hR (L₁.length + 1) (by omega) y hyR h1,
    sfta_next_eq_of_getElem hL L₁.length hcL a ha (sfta_insert_getElem_att L₁ L₂ a hcL).symm]
  by_cases hlast : L₁.length + 1 < (L₁ ++ a :: L₂).length
  · have hmod1 : (L₁.length + 1 + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length =
        L₁.length + 2 := Nat.mod_eq_of_lt (by omega)
    have hmod2 : (L₁.length + 1) % (L₁ ++ a :: L₂).length = L₁.length + 1 := Nat.mod_eq_of_lt hlast
    simp only [hmod1, hmod2]
    exact sfta_insert_getElem_gt L₁ L₂ a f y (by omega) hlast (by omega)
  · have hiN : L₁.length + 1 = (L₁ ++ a :: L₂).length := by omega
    have hmod1 : (L₁.length + 1 + 1) % (L₁.map f ++ f a :: y :: L₂.map f).length = 0 := by
      rw [hlen, hiN]; simp
    have hmod2 : (L₁.length + 1) % (L₁ ++ a :: L₂).length = 0 := by rw [hiN]; simp
    simp only [hmod1, hmod2]
    exact sfta_insert_getElem_le L₁ L₂ a f y (Nat.zero_le _) (by omega) (by omega)

end ListLayer


section InsertTransport

theorem sfta_next_congr {α : Type*} [DecidableEq α] {l l' : List α} (h : l = l') (x : α) (hx : x ∈ l) :
    l.next x hx = l'.next x (h ▸ hx) := by
  subst h; rfl


/-- An *insertion mark transport* from the generic `n`-gon `P` to the generic `(n+1)`-gon `Q`:
compatible bijections of crossings and visits, a vertex map `vert` with one new vertex `new`
inserted immediately after the attachment vertex `att` in the sorted mark list (up to rotation),
and preserved interlacement.  This is the `MarkTransport` of SM/CChamber.lean for mark sets that
differ by exactly one vertex (the soft insertion `P ↦ P_ε` of def:soft, sm-4:1024-1057). -/
structure sfta_InsertMarkTransport (hn : 3 ≤ n) {P : LabelledTuple n} {Q : LabelledTuple (n + 1)}
    (hP : Generic P) (hQ : Generic Q) where
  vert : ZMod n → ZMod (n + 1)
  new : ZMod (n + 1)
  att : ZMod n
  cross : Crossing P ≃ Crossing Q
  visit : Visit P ≃ Visit Q
  visit_fst : ∀ v, (visit v).1 = cross v.1
  markList_insertion : sfta_IsInsertion (Sum.map vert visit) (Sum.inl att) (Sum.inl new)
    (markList hn hP) (markList (by omega) hQ)
  interlaces_iff : ∀ x y, Interlaces (by omega) hQ (cross x) (cross y) ↔ Interlaces hn hP x y

namespace sfta_InsertMarkTransport

variable {hn : 3 ≤ n} {P : LabelledTuple n} {Q : LabelledTuple (n + 1)} {hP : Generic P}
  {hQ : Generic Q} (τ : sfta_InsertMarkTransport hn hP hQ)

/-- The induced map of marks (injective, missing exactly `Sum.inl new`). -/
def toMark : Mark P → Mark Q := Sum.map τ.vert τ.visit

theorem toMark_inl (i : ZMod n) : τ.toMark (Sum.inl i) = Sum.inl (τ.vert i) := rfl

theorem toMark_inr (v : Visit P) : τ.toMark (Sum.inr v) = Sum.inr (τ.visit v) := rfl

theorem markList_insertion' : sfta_IsInsertion τ.toMark (Sum.inl τ.att) (Sum.inl τ.new)
    (markList hn hP) (markList (by omega) hQ) := τ.markList_insertion

/-- The sorted mark list of `Q` is a permutation of `Sum.inl new :: (markList P).map toMark`. -/
theorem markList_perm :
    (markList (by omega : 3 ≤ n + 1) hQ).Perm (Sum.inl τ.new :: (markList hn hP).map τ.toMark) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  refine hrot.perm.trans ?_
  rw [hL]
  exact sfta_insert_perm L₁ L₂ _ _ _

theorem new_cons_map_nodup : (Sum.inl τ.new :: (markList hn hP).map τ.toMark).Nodup :=
  τ.markList_perm.nodup_iff.mp (markList_nodup _ hQ)

theorem toMark_injective : Function.Injective τ.toMark := by
  have h := (List.nodup_cons.mp τ.new_cons_map_nodup).2
  intro a b hab
  exact List.inj_on_of_nodup_map h (mem_markList hn hP a) (mem_markList hn hP b) hab

theorem new_notMem_map : Sum.inl τ.new ∉ (markList hn hP).map τ.toMark :=
  (List.nodup_cons.mp τ.new_cons_map_nodup).1

theorem toMark_ne_new (m : Mark P) : τ.toMark m ≠ Sum.inl τ.new := fun h =>
  τ.new_notMem_map (List.mem_map.mpr ⟨m, mem_markList hn hP m, h⟩)

theorem vert_ne_new (i : ZMod n) : τ.vert i ≠ τ.new := fun h =>
  τ.toMark_ne_new (Sum.inl i) (by rw [toMark_inl, h])

theorem vert_injective : Function.Injective τ.vert := fun i k h =>
  Sum.inl_injective (τ.toMark_injective (a₁ := Sum.inl i) (a₂ := Sum.inl k) (by rw [toMark_inl, toMark_inl, h]))

/-- Every mark of `Q` is the new vertex or a transported mark. -/
theorem exhaust (m : Mark Q) : m = Sum.inl τ.new ∨ ∃ a : Mark P, τ.toMark a = m := by
  have hm := τ.markList_perm.mem_iff.mp (mem_markList _ hQ m)
  rw [List.mem_cons, List.mem_map] at hm
  rcases hm with h | ⟨a, _, ha⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, ha⟩

theorem vert_exhaust (a : ZMod (n + 1)) : a = τ.new ∨ ∃ i : ZMod n, τ.vert i = a := by
  rcases τ.exhaust (Sum.inl a) with h | ⟨m, hm⟩
  · exact Or.inl (Sum.inl_injective h)
  · cases m with
    | inl i => exact Or.inr ⟨i, Sum.inl_injective hm⟩
    | inr v => exact absurd hm (by rw [toMark_inr]; exact Sum.inr_ne_inl)

/-- The transported support. -/
def support (S : Finset (Crossing P)) : Finset (Crossing Q) :=
  S.map τ.cross.toEmbedding

theorem mem_support (S : Finset (Crossing P)) (x : Crossing P) :
    τ.cross x ∈ τ.support S ↔ x ∈ S := by
  simp only [support, Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem support_card (S : Finset (Crossing P)) : (τ.support S).card = S.card :=
  Finset.card_map _

theorem support_surjective (S' : Finset (Crossing Q)) : ∃ S, τ.support S = S' :=
  ⟨S'.map τ.cross.symm.toEmbedding, by simp [support, Finset.map_map]⟩

theorem support_injective : Function.Injective τ.support := fun S T h =>
  Finset.map_injective τ.cross.toEmbedding h

/-- The visit twin is carried to the visit twin. -/
theorem twin_eq (v : Visit P) : τ.visit (visitTwin v) = visitTwin (τ.visit v) := by
  apply visitTwin_unique (τ.visit v) (τ.visit (visitTwin v))
  · rw [τ.visit_fst, τ.visit_fst, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v (τ.visit.injective h)

/-! ### The cyclic successor: literal for marks other than the attachment, through the new vertex
at the attachment -/

theorem markSuccessor_of_ne (m : Mark P) (hm : m ≠ Sum.inl τ.att) :
    markSuccessor (by omega) hQ (τ.toMark m) = τ.toMark (markSuccessor hn hP m) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  have hy : Sum.inl τ.new ∉ (L₁ ++ Sum.inl τ.att :: L₂).map τ.toMark := by
    rw [← hL]; exact τ.new_notMem_map
  rw [markSuccessor_apply, markSuccessor_apply, nextMark_eq_list_next, nextMark_eq_list_next,
    List.isRotated_next_eq hrot (markList_nodup _ hQ), sfta_next_congr hL]
  exact sfta_insert_next_of_ne L₁ L₂ _ τ.toMark _ τ.toMark_injective hnd hy m
    (hL ▸ mem_markList hn hP m) hm _

theorem markSuccessor_att :
    markSuccessor (by omega) hQ (Sum.inl (τ.vert τ.att)) = Sum.inl τ.new := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  have hy : Sum.inl τ.new ∉ (L₁ ++ Sum.inl τ.att :: L₂).map τ.toMark := by
    rw [← hL]; exact τ.new_notMem_map
  rw [markSuccessor_apply, nextMark_eq_list_next,
    List.isRotated_next_eq hrot (markList_nodup _ hQ)]
  exact sfta_insert_next_att L₁ L₂ _ τ.toMark _ τ.toMark_injective hnd hy _

theorem markSuccessor_new :
    markSuccessor (by omega) hQ (Sum.inl τ.new) = τ.toMark (markSuccessor hn hP (Sum.inl τ.att)) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  have hy : Sum.inl τ.new ∉ (L₁ ++ Sum.inl τ.att :: L₂).map τ.toMark := by
    rw [← hL]; exact τ.new_notMem_map
  rw [markSuccessor_apply, markSuccessor_apply, nextMark_eq_list_next, nextMark_eq_list_next,
    List.isRotated_next_eq hrot (markList_nodup _ hQ), sfta_next_congr hL]
  exact sfta_insert_next_new L₁ L₂ _ τ.toMark _ τ.toMark_injective hnd hy _ _

theorem selectedMarkPerm_transport (S : Finset (Crossing P)) (m : Mark P) :
    selectedMarkPerm (τ.support S) (τ.toMark m) = τ.toMark (selectedMarkPerm S m) := by
  cases m with
  | inl i => rfl
  | inr v =>
    rw [toMark_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, toMark_inr]
    have hv' : (τ.visit v).1 ∈ τ.support S ↔ v.1 ∈ S := by
      rw [τ.visit_fst, τ.mem_support]
    by_cases hv : v.1 ∈ S
    · rw [selectedVisitTwin_of_mem _ _ hv, selectedVisitTwin_of_mem _ _ (hv'.mpr hv), τ.twin_eq]
    · rw [selectedVisitTwin_of_not_mem _ _ hv,
        selectedVisitTwin_of_not_mem _ _ (fun h => hv (hv'.mp h))]

theorem selectedMarkPerm_ne_att (S : Finset (Crossing P)) (m : Mark P) (hm : m ≠ Sum.inl τ.att) :
    selectedMarkPerm S m ≠ Sum.inl τ.att := by
  cases m with
  | inl i => exact hm
  | inr v => rw [selectedMarkPerm_visit]; exact Sum.inr_ne_inl

theorem smoothingSuccessor_of_ne (S : Finset (Crossing P)) (m : Mark P) (hm : m ≠ Sum.inl τ.att) :
    smoothingSuccessor (by omega) hQ (τ.support S) (τ.toMark m) =
      τ.toMark (smoothingSuccessor hn hP S m) := by
  change markSuccessor (by omega) hQ (selectedMarkPerm (τ.support S) (τ.toMark m)) =
    τ.toMark (markSuccessor hn hP (selectedMarkPerm S m))
  rw [τ.selectedMarkPerm_transport, τ.markSuccessor_of_ne _ (τ.selectedMarkPerm_ne_att S m hm)]

theorem smoothingSuccessor_att (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.support S) (Sum.inl (τ.vert τ.att)) = Sum.inl τ.new := by
  rw [smoothingSuccessor_vertex]; exact τ.markSuccessor_att

theorem smoothingSuccessor_new (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.support S) (Sum.inl τ.new) =
      τ.toMark (smoothingSuccessor hn hP S (Sum.inl τ.att)) := by
  rw [smoothingSuccessor_vertex, smoothingSuccessor_vertex]; exact τ.markSuccessor_new

/-! ### Cycles and carriers -/

theorem sameCycle_new (S : Finset (Crossing P)) :
    (smoothingSuccessor (by omega) hQ (τ.support S)).SameCycle (τ.toMark (Sum.inl τ.att))
      (Sum.inl τ.new) := by
  have h := (Equiv.Perm.SameCycle.refl (smoothingSuccessor (by omega) hQ (τ.support S))
    (τ.toMark (Sum.inl τ.att))).apply_right
  rwa [toMark_inl, τ.smoothingSuccessor_att S] at h

theorem sameCycle_of (S : Finset (Crossing P)) {a b : Mark P}
    (h : (smoothingSuccessor hn hP S).SameCycle a b) :
    (smoothingSuccessor (by omega) hQ (τ.support S)).SameCycle (τ.toMark a) (τ.toMark b) := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  clear hk
  induction k with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply]; exact Equiv.Perm.SameCycle.refl _ _
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    by_cases hm : (smoothingSuccessor hn hP S ^ k) a = Sum.inl τ.att
    · rw [hm] at ih ⊢
      have h1 := ih.apply_right.apply_right
      rwa [toMark_inl, τ.smoothingSuccessor_att, τ.smoothingSuccessor_new] at h1
    · have h1 := ih.apply_right
      rwa [τ.smoothingSuccessor_of_ne S _ hm] at h1

theorem sameCycle_iff (S : Finset (Crossing P)) (a b : Mark P) :
    (smoothingSuccessor (by omega) hQ (τ.support S)).SameCycle (τ.toMark a) (τ.toMark b) ↔
      (smoothingSuccessor hn hP S).SameCycle a b := by
  refine ⟨fun h => ?_, τ.sameCycle_of S⟩
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have key : ∀ k : ℕ, ∃ m : Mark P, (smoothingSuccessor hn hP S).SameCycle a m ∧
      ((smoothingSuccessor (by omega) hQ (τ.support S) ^ k) (τ.toMark a) = τ.toMark m ∨
        ((smoothingSuccessor (by omega) hQ (τ.support S) ^ k) (τ.toMark a) = Sum.inl τ.new ∧
          m = Sum.inl τ.att)) := by
    intro k
    induction k with
    | zero => exact ⟨a, Equiv.Perm.SameCycle.refl _ _, Or.inl (by simp)⟩
    | succ k ih =>
      obtain ⟨m, hm, hk⟩ := ih
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases hk with hk | ⟨hk, rfl⟩
      · rw [hk]
        by_cases hma : m = Sum.inl τ.att
        · subst hma
          exact ⟨Sum.inl τ.att, hm, Or.inr ⟨by rw [toMark_inl, τ.smoothingSuccessor_att], rfl⟩⟩
        · exact ⟨smoothingSuccessor hn hP S m, hm.apply_right,
            Or.inl (τ.smoothingSuccessor_of_ne S m hma)⟩
      · rw [hk, τ.smoothingSuccessor_new]
        exact ⟨smoothingSuccessor hn hP S (Sum.inl τ.att), hm.apply_right, Or.inl rfl⟩
  obtain ⟨m, hm, hmk⟩ := key k
  rw [hk] at hmk
  rcases hmk with hmk | ⟨hmk, _⟩
  · rw [← τ.toMark_injective hmk] at hm
    exact hm
  · exact absurd hmk (τ.toMark_ne_new b)

/-- The carriers of `S` correspond to the carriers of the transported support. -/
def component (S : Finset (Crossing P)) :
    Component hn hP S ≃ Component (by omega) hQ (τ.support S) :=
  Equiv.ofBijective
    (Quotient.lift (fun a => owner (by omega) hQ (τ.support S) (τ.toMark a))
      (fun a b hab => (owner_eq_iff _ hQ _ _ _).mpr (τ.sameCycle_of S hab)))
    ⟨by
      intro q r hqr
      obtain ⟨a, rfl⟩ := owner_surjective hn hP S q
      obtain ⟨b, rfl⟩ := owner_surjective hn hP S r
      apply (owner_eq_iff hn hP S a b).mpr
      exact (τ.sameCycle_iff S a b).mp ((owner_eq_iff _ hQ _ _ _).mp hqr),
     by
      intro q'
      obtain ⟨m, rfl⟩ := owner_surjective _ hQ (τ.support S) q'
      rcases τ.exhaust m with rfl | ⟨a, rfl⟩
      · refine ⟨owner hn hP S (Sum.inl τ.att), ?_⟩
        exact (owner_eq_iff _ hQ _ _ _).mpr (τ.sameCycle_new S)
      · exact ⟨owner hn hP S a, rfl⟩⟩

theorem component_owner (S : Finset (Crossing P)) (m : Mark P) :
    τ.component S (owner hn hP S m) = owner (by omega) hQ (τ.support S) (τ.toMark m) := rfl

theorem owner_new (S : Finset (Crossing P)) :
    owner (by omega) hQ (τ.support S) (Sum.inl τ.new) =
      τ.component S (owner hn hP S (Sum.inl τ.att)) := by
  rw [component_owner]
  exact ((owner_eq_iff _ hQ _ _ _).mpr (τ.sameCycle_new S)).symm

theorem carrierCrossings_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossings (by omega) hQ (τ.support S) (τ.component S q) =
      (carrierCrossings hn hP S q).map τ.cross.toEmbedding := by
  ext x'
  obtain ⟨x, rfl⟩ := τ.cross.surjective x'
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  rw [mem_carrierCrossings, mem_carrierCrossings, τ.mem_support]
  apply and_congr Iff.rfl
  constructor
  · intro h v hv
    have h1 : owner (by omega) hQ (τ.support S) (Sum.inr (τ.visit v)) = τ.component S q :=
      h (τ.visit v) (by rw [τ.visit_fst, hv])
    apply (τ.component S).injective
    exact h1
  · intro h w hw
    obtain ⟨v, rfl⟩ := τ.visit.surjective w
    have hv : v.1 = x := τ.cross.injective ((τ.visit_fst v).symm.trans hw)
    show τ.component S (owner hn hP S (Sum.inr v)) = τ.component S q
    exact congrArg _ (h v hv)

theorem carrierCrossingCount_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossingCount (by omega) hQ (τ.support S) (τ.component S q) =
      carrierCrossingCount hn hP S q := by
  rw [carrierCrossingCount_eq_card, carrierCrossingCount_eq_card,
    τ.carrierCrossings_transport, Finset.card_map]

theorem isDecomposition_transport (S : Finset (Crossing P)) :
    IsDecomposition (by omega) hQ (τ.support S) ↔ IsDecomposition hn hP S := by
  unfold IsDecomposition
  rw [mem_independentSupports_iff, mem_independentSupports_iff]
  constructor
  · intro h x hx y hy hxy hI
    exact h _ ((τ.mem_support S x).mpr hx) _ ((τ.mem_support S y).mpr hy)
      (fun he => hxy (τ.cross.injective he)) ((τ.interlaces_iff x y).mpr hI)
  · intro h x hx y hy hxy hI
    obtain ⟨x₀, rfl⟩ := τ.cross.surjective x
    obtain ⟨y₀, rfl⟩ := τ.cross.surjective y
    exact h x₀ ((τ.mem_support S x₀).mp hx) y₀ ((τ.mem_support S y₀).mp hy)
      (fun he => hxy (congrArg τ.cross he)) ((τ.interlaces_iff x₀ y₀).mp hI)

theorem isTrueCorner_transport (S : Finset (Crossing P)) (m : Mark P) :
    IsTrueCorner (τ.support S) (τ.toMark m) ↔ IsTrueCorner S m := by
  cases m with
  | inl i => rw [toMark_inl]; exact Iff.rfl
  | inr v => rw [toMark_inr, isTrueCorner_visit, isTrueCorner_visit, τ.visit_fst, τ.mem_support]

end sfta_InsertMarkTransport

end InsertTransport


section InsertLists

variable {α β : Type*}

theorem sfta_IsInsertion.filter {f : α → β} {a₀ : α} {y : β} {L : List α} {R : List β}
    (h : sfta_IsInsertion f a₀ y L R) (p : β → Bool) (p' : α → Bool) (hpp : ∀ x, p (f x) = p' x)
    (hp₀ : p' a₀ = true) (hpy : p y = true) :
    sfta_IsInsertion f a₀ y (L.filter p') (R.filter p) := by
  obtain ⟨L₁, L₂, rfl, hrot⟩ := h
  refine ⟨L₁.filter p', L₂.filter p', ?_, ?_⟩
  · simp only [List.filter_append, List.filter_cons, hp₀, ite_true]
  · refine (hrot.filter p).trans ?_
    simp only [List.filter_append, List.filter_cons, List.filter_map, Function.comp_def, hpp, hp₀,
      hpy, ite_true]
    exact List.IsRotated.refl _

theorem sfta_IsInsertion.filter_not {f : α → β} {a₀ : α} {y : β} {L : List α} {R : List β}
    (h : sfta_IsInsertion f a₀ y L R) (p : β → Bool) (p' : α → Bool) (hpp : ∀ x, p (f x) = p' x)
    (hp₀ : p' a₀ = false) (hpy : p y = false) :
    (R.filter p).IsRotated ((L.filter p').map f) := by
  obtain ⟨L₁, L₂, rfl, hrot⟩ := h
  refine (hrot.filter p).trans ?_
  simp only [List.filter_append, List.filter_cons, List.filter_map, Function.comp_def, hpp, hp₀,
    hpy, Bool.false_eq_true, ite_false, List.map_append]
  exact List.IsRotated.refl _

end InsertLists

section CornerMarks


/-- Uniformity of a carrier of a decomposition, read on the `markTurn`s of its corner list
(`turn_ccpCornerPolygon_eq_markTurn`, CX1.lean). -/
theorem sfta_carrierUniform_iff_forall_mem (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    CarrierUniform hn hP S q ↔
      ∃ σ : SignType, σ ≠ 0 ∧ ∀ m ∈ ccpCornerList hn hP S q, markTurn P m = σ := by
  unfold CarrierUniform
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h m hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have hi' : i < ccpCornerCount hn hP S q := hi
    have := h (i : ZMod (ccpCornerCount hn hP S q))
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS] at this
    unfold ccpCornerMark at this
    have hval : ((i : ZMod (ccpCornerCount hn hP S q))).val = i := ZMod.val_natCast_of_lt hi'
    simp only [hval] at this
    exact this
  · intro h k
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS]
    exact h _ (List.getElem_mem _)

end CornerMarks

namespace sfta_InsertMarkTransport

variable {hn : 3 ≤ n} {P : LabelledTuple n} {Q : LabelledTuple (n + 1)}
  {hP : Generic P} {hQ : Generic Q} (τ : sfta_InsertMarkTransport hn hP hQ)

theorem owner_toMark_eq_iff (S : Finset (Crossing P)) (q : Component hn hP S) (m : Mark P) :
    owner (by omega) hQ (τ.support S) (τ.toMark m) = τ.component S q ↔ owner hn hP S m = q := by
  rw [← τ.component_owner]
  exact (τ.component S).injective.eq_iff

/-! ### Mark lists and corner lists of the carriers: the carrier through the attachment vertex
gains the new vertex right after it; every other carrier is carried up to rotation -/

theorem componentMarkList_insertion (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) = q) :
    sfta_IsInsertion τ.toMark (Sum.inl τ.att) (Sum.inl τ.new) (componentMarkList hn hP S q)
      (componentMarkList (by omega) hQ (τ.support S) (τ.component S q)) := by
  unfold componentMarkList
  refine τ.markList_insertion'.filter _ _ (fun m => ?_) ?_ ?_
  · exact decide_eq_decide.mpr (τ.owner_toMark_eq_iff S q m)
  · exact decide_eq_true hq
  · apply decide_eq_true
    rw [τ.owner_new, hq]

theorem componentMarkList_rotated_of_ne (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) ≠ q) :
    (componentMarkList (by omega) hQ (τ.support S) (τ.component S q)).IsRotated
      ((componentMarkList hn hP S q).map τ.toMark) := by
  unfold componentMarkList
  refine τ.markList_insertion'.filter_not _ _ (fun m => ?_) ?_ ?_
  · exact decide_eq_decide.mpr (τ.owner_toMark_eq_iff S q m)
  · exact decide_eq_false hq
  · apply decide_eq_false
    rw [τ.owner_new]
    exact fun h => hq ((τ.component S).injective h)

theorem ccpCornerList_insertion (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) = q) :
    sfta_IsInsertion τ.toMark (Sum.inl τ.att) (Sum.inl τ.new) (ccpCornerList hn hP S q)
      (ccpCornerList (by omega) hQ (τ.support S) (τ.component S q)) := by
  unfold ccpCornerList
  exact (τ.componentMarkList_insertion S q hq).filter _ _
    (fun m => decide_eq_decide.mpr (τ.isTrueCorner_transport S m)) (decide_eq_true trivial)
    (decide_eq_true trivial)

theorem ccpCornerList_rotated_of_ne (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) ≠ q) :
    (ccpCornerList (by omega) hQ (τ.support S) (τ.component S q)).IsRotated
      ((ccpCornerList hn hP S q).map τ.toMark) := by
  unfold ccpCornerList
  exact Carrier.MarkTransport.isRotated_filter_map_of_forall τ.toMark (τ.componentMarkList_rotated_of_ne S q hq) _ _
    (fun a => decide_eq_decide.mpr (τ.isTrueCorner_transport S a))

theorem ccpCornerCount_insertion (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) = q) :
    ccpCornerCount (by omega) hQ (τ.support S) (τ.component S q) = ccpCornerCount hn hP S q + 1 := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.ccpCornerList_insertion S q hq
  unfold ccpCornerCount
  rw [hrot.perm.length_eq, sfta_insert_length, hL]

theorem ccpCornerCount_of_ne (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) ≠ q) :
    ccpCornerCount (by omega) hQ (τ.support S) (τ.component S q) = ccpCornerCount hn hP S q := by
  unfold ccpCornerCount
  rw [(τ.ccpCornerList_rotated_of_ne S q hq).perm.length_eq, List.length_map]

theorem mem_ccpCornerList_insertion (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) = q) (m' : Mark Q) :
    m' ∈ ccpCornerList (by omega) hQ (τ.support S) (τ.component S q) ↔
      m' = Sum.inl τ.new ∨ ∃ m ∈ ccpCornerList hn hP S q, τ.toMark m = m' := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.ccpCornerList_insertion S q hq
  rw [hrot.mem_iff, sfta_insert_mem, hL]

theorem mem_ccpCornerList_of_ne (S : Finset (Crossing P)) (q : Component hn hP S)
    (hq : owner hn hP S (Sum.inl τ.att) ≠ q) (m' : Mark Q) :
    m' ∈ ccpCornerList (by omega) hQ (τ.support S) (τ.component S q) ↔
      ∃ m ∈ ccpCornerList hn hP S q, τ.toMark m = m' := by
  rw [(τ.ccpCornerList_rotated_of_ne S q hq).mem_iff, List.mem_map]

/-! ### Uniformity -/

theorem carrierUniform_iff_insertion (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hq : owner hn hP S (Sum.inl τ.att) = q) :
    CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔
      ∃ σ : SignType, σ ≠ 0 ∧ (∀ m ∈ ccpCornerList hn hP S q, markTurn Q (τ.toMark m) = σ) ∧
        turn Q τ.new = σ := by
  rw [sfta_carrierUniform_iff_forall_mem _ hQ ((τ.isDecomposition_transport S).mpr hS)]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h
    refine ⟨fun m hm => h _ ((τ.mem_ccpCornerList_insertion S q hq _).mpr (Or.inr ⟨m, hm, rfl⟩)), ?_⟩
    have := h _ ((τ.mem_ccpCornerList_insertion S q hq _).mpr (Or.inl rfl))
    rwa [markTurn_inl] at this
  · rintro ⟨h1, h2⟩ m' hm'
    rcases (τ.mem_ccpCornerList_insertion S q hq m').mp hm' with rfl | ⟨m, hm, rfl⟩
    · rw [markTurn_inl]; exact h2
    · exact h1 m hm

theorem carrierUniform_iff_of_ne (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hq : owner hn hP S (Sum.inl τ.att) ≠ q) :
    CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔
      ∃ σ : SignType, σ ≠ 0 ∧ ∀ m ∈ ccpCornerList hn hP S q, markTurn Q (τ.toMark m) = σ := by
  rw [sfta_carrierUniform_iff_forall_mem _ hQ ((τ.isDecomposition_transport S).mpr hS)]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h m hm
    exact h _ ((τ.mem_ccpCornerList_of_ne S q hq _).mpr ⟨m, hm, rfl⟩)
  · rintro h m' hm'
    obtain ⟨m, hm, rfl⟩ := (τ.mem_ccpCornerList_of_ne S q hq m').mp hm'
    exact h m hm

/-- **Uniformity is carried** when every corner mark keeps its turn and the new vertex turns like
the attachment vertex (the same-sign sector of thm:C-soft). -/
theorem carrierUniform_iff (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hturn : ∀ m, markTurn Q (τ.toMark m) = markTurn P m)
    (hnew : turn Q τ.new = turn P τ.att) :
    CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q := by
  rw [sfta_carrierUniform_iff_forall_mem hn hP hS q]
  by_cases hq : owner hn hP S (Sum.inl τ.att) = q
  · rw [τ.carrierUniform_iff_insertion S hS q hq]
    refine exists_congr fun σ => and_congr_right fun _ => ?_
    simp only [hturn]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rw [hnew, ← markTurn_inl]
      exact h _ ((mem_ccpCornerList hn hP S q _).mpr ⟨hq, isTrueCorner_vertex S _⟩)
  · rw [τ.carrierUniform_iff_of_ne S hS q hq]
    simp only [hturn]

theorem uniformDecomposition_transport {S : Finset (Crossing P)}
    (huni : ∀ q : Component hn hP S,
      CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q) :
    UniformDecomposition (by omega) hQ (τ.support S) ↔ UniformDecomposition hn hP S := by
  unfold UniformDecomposition
  rw [(τ.component S).surjective.forall]
  exact forall_congr' huni

theorem mem_uniformDecompositions_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q)
    (S : Finset (Crossing P)) :
    τ.support S ∈ uniformDecompositions (by omega) hQ ↔ S ∈ uniformDecompositions hn hP := by
  rw [mem_uniformDecompositions, mem_uniformDecompositions]
  have hd : τ.support S ∈ independentSupports (by omega) hQ ↔ S ∈ independentSupports hn hP :=
    τ.isDecomposition_transport S
  by_cases hS : IsDecomposition hn hP S
  · exact and_congr hd (τ.uniformDecomposition_transport (huni S hS))
  · constructor
    · rintro ⟨h, _⟩
      exact absurd (hd.mp h) hS
    · rintro ⟨h, _⟩
      exact absurd h hS

/-! ### The left-turn count -/

/-- `ℓ(Q) = ℓ(P) − [τ_att(P) = 1] + [τ_{vert att}(Q) = 1] + [τ_new(Q) = 1]` (additive form) when
every other vertex keeps its turn. -/
theorem leftTurns_transport (hturn : ∀ i, i ≠ τ.att → turn Q (τ.vert i) = turn P i) :
    leftTurns Q + (if turn P τ.att = 1 then 1 else 0) =
      leftTurns P + (if turn Q (τ.vert τ.att) = 1 then 1 else 0) +
        (if turn Q τ.new = 1 then 1 else 0) := by
  unfold leftTurns
  rw [Finset.card_filter, Finset.card_filter]
  have huniv : (Finset.univ : Finset (ZMod (n + 1))) = insert τ.new (Finset.univ.image τ.vert) := by
    ext a
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_image, true_and]
    rcases τ.vert_exhaust a with h | ⟨i, hi⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi⟩
  have hnot : τ.new ∉ Finset.univ.image τ.vert := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun i => τ.vert_ne_new i
  rw [huniv, Finset.sum_insert hnot, Finset.sum_image (fun i _ k _ h => τ.vert_injective h),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ τ.att),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ τ.att)]
  have hrest : ∑ x ∈ Finset.univ.erase τ.att, (if turn Q (τ.vert x) = 1 then 1 else 0) =
      ∑ x ∈ Finset.univ.erase τ.att, (if turn P x = 1 then 1 else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hturn x (Finset.ne_of_mem_erase hx)]
  rw [hrest]
  ring

/-! ### The corner coefficients and the state sum -/

theorem cornerSlot_transport {S : Finset (Crossing P)} (q : Component hn hP S)
    (hrot : carrierRotation (by omega) hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q) :
    cornerSlot (by omega) hQ (τ.support S) (τ.component S q) = cornerSlot hn hP S q := by
  unfold cornerSlot carrierRotationInt
  rw [τ.carrierCrossingCount_transport S q, hrot]

theorem cornerCoefficient_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hrot : carrierRotation (by omega) hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q)
    (hH : homfly (positiveLift (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS)) = homfly (positiveLift hn hP S q hS)) :
    cornerCoefficient (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt]
  unfold cornerHomfly
  rw [τ.cornerSlot_transport q hrot, hH]

theorem cornerProduct_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (hcoef : ∀ q : Component hn hP S,
      cornerCoefficient (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerProduct (by omega) hQ (τ.support S) ((τ.isDecomposition_transport S).mpr hS) =
      cornerProduct hn hP S hS := by
  unfold cornerProduct
  exact (Fintype.prod_equiv (τ.component S) _ _ fun q => (hcoef q).symm).symm

/-- **The signed sum over the uniform decompositions is carried** under a transport preserving
uniformity and the corner coefficients (the prefactor `(−1)^ℓ` is treated by `leftTurns_transport`). -/
theorem sum_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q)
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    (∑ S ∈ (uniformDecompositions (by omega) hQ).attach,
      (-1) ^ S.1.card *
        cornerProduct (by omega) hQ S.1 (isDecomposition_of_mem_uniformDecompositions _ hQ S.2)) =
    ∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2) := by
  set g : Finset (Crossing P) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions hn hP then
      (-1) ^ S.card * cornerProduct hn hP S (isDecomposition_of_mem_uniformDecompositions hn hP h)
    else 0 with hg
  set g' : Finset (Crossing Q) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions (by omega) hQ then
      (-1) ^ S.card * cornerProduct (by omega) hQ S (isDecomposition_of_mem_uniformDecompositions _ hQ h)
    else 0 with hg'
  have h1 : (∑ S ∈ (uniformDecompositions (by omega) hQ).attach,
      (-1) ^ S.1.card *
        cornerProduct (by omega) hQ S.1 (isDecomposition_of_mem_uniformDecompositions _ hQ S.2)) =
      ∑ S ∈ (uniformDecompositions (by omega) hQ).attach, g' S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg']
    rw [dite_eq_left S.2]
  have h2 : (∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2)) =
      ∑ S ∈ (uniformDecompositions hn hP).attach, g S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg]
    rw [dite_eq_left S.2]
  rw [h1, h2, Finset.sum_attach, Finset.sum_attach]
  symm
  refine Finset.sum_nbij τ.support ?_ ?_ ?_ ?_
  · intro S hS
    exact (τ.mem_uniformDecompositions_transport huni S).mpr hS
  · intro S _ T _ h
    exact τ.support_injective h
  · intro S' hS'
    obtain ⟨S, rfl⟩ := τ.support_surjective S'
    exact ⟨S, (τ.mem_uniformDecompositions_transport huni S).mp hS', rfl⟩
  · intro S hS
    have hS' : IsDecomposition hn hP S := isDecomposition_of_mem_uniformDecompositions hn hP hS
    have hSQ : τ.support S ∈ uniformDecompositions (by omega) hQ :=
      (τ.mem_uniformDecompositions_transport huni S).mpr hS
    simp only [hg, hg']
    rw [dite_eq_left hS, dite_eq_left hSQ, τ.support_card]
    congr 1
    exact (τ.cornerProduct_transport hS' (hcoef S hS')).symm

theorem sfta_sign_cancel (ℓ₁ ℓ₂ : ℕ) (x : ℤ) :
    (-1) ^ ℓ₁ * x = (-1) ^ (ℓ₁ + ℓ₂) * ((-1) ^ ℓ₂ * x) := by
  have h : ((-1 : ℤ) ^ ℓ₂) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  rw [pow_add]
  linear_combination (-((-1 : ℤ) ^ ℓ₁ * x)) * h

/-- The corner state sum is carried up to the sign `(−1)^{ℓ(Q) + ℓ(P)}`. -/
theorem cornerStateSum_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      CarrierUniform (by omega) hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q)
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient (by omega) hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerStateSum (by omega) hQ = (-1) ^ (leftTurns Q + leftTurns P) * cornerStateSum hn hP := by
  unfold cornerStateSum
  rw [τ.sum_transport huni hcoef]
  exact sfta_sign_cancel _ _ _

end sfta_InsertMarkTransport


section SoftIndices


theorem sfta_softOldIndex_val_of_ne_zero (j i : ZMod n) (hj : j ≠ 0) :
    (softOldIndex j i).val = if i.val ≤ j.val then i.val else i.val + 1 := by
  by_cases hi : i = j
  · subst hi
    simp only [le_refl, ite_true]
    rw [softOldIndex_at_attachment, canonicalPosition_val_nonzero i hj]
    have hp := ZMod.val_pos.mpr hj
    have hlt := ZMod.val_lt i
    have h1 : i.val - 1 + 1 = i.val := by omega
    rw [h1]
    exact ZMod.val_natCast_of_lt (by omega)
  · rw [← softParentEdge_of_ne j i hi, softParentEdge_val]
    have hne : i.val ≠ j.val := fun h => hi (ZMod.val_injective n h)
    simp only [hj, false_or]
    split_ifs <;> omega

theorem sfta_softNewIndex_val_of_ne_zero (j : ZMod n) (hj : j ≠ 0) :
    (softNewIndex j).val = j.val + 1 := by
  rw [softNewIndex_physical, canonicalPosition_val_nonzero j hj]
  have hp := ZMod.val_pos.mpr hj
  have hlt := ZMod.val_lt j
  have h1 : j.val - 1 + 2 = j.val + 1 := by omega
  rw [h1]
  exact ZMod.val_natCast_of_lt (by omega)

theorem sfta_softOldIndex_zero_val (i : ZMod n) :
    (softOldIndex (0 : ZMod n) i).val = if i = 0 then n else i.val := by
  by_cases hi : i = 0
  · subst hi
    simp only [ite_true]
    rw [softOldIndex_at_attachment, canonicalPosition_val_zero]
    have := NeZero.pos n
    have h1 : n - 1 + 1 = n := by omega
    rw [h1]
    exact ZMod.val_natCast_of_lt (by omega)
  · rw [if_neg hi, ← softParentEdge_of_ne 0 i hi, softParentEdge_val]
    simp

theorem sfta_softNewIndex_zero : softNewIndex (0 : ZMod n) = 0 := by
  rw [softNewIndex_physical, canonicalPosition_val_zero]
  have := NeZero.pos n
  have h1 : n - 1 + 2 = n + 1 := by omega
  rw [h1, ZMod.natCast_self]

theorem sfta_softParentEdge_val_of_ne_zero (j e : ZMod n) (hj : j ≠ 0) :
    (softParentEdge j e).val = if e.val < j.val then e.val else e.val + 1 := by
  rw [softParentEdge_val]; simp [hj]

theorem sfta_softParentEdge_zero_val (e : ZMod n) : (softParentEdge (0 : ZMod n) e).val = e.val := by
  rw [softParentEdge_val]; simp

end SoftIndices

section SoftKeys

theorem sfta_nat_lt_add_iff (a b : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    (a : ℝ) < b + t ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast (not_le.mp hab)
    linarith
  · intro h
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

theorem sfta_add_lt_nat_iff (a b : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    (b : ℝ) + t < a ↔ b < a := by
  constructor
  · intro h
    by_contra hab
    have : (a : ℝ) ≤ b := by exact_mod_cast (not_lt.mp hab)
    linarith
  · intro h
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    linarith


theorem sfta_markKey_visit_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) (v : Visit P) :
    markKey hn hP (Sum.inr v) = (v.2.val.val : ℝ) + visitParameter v := rfl

theorem sfta_markKey_vertex_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) (i : ZMod n) :
    markKey hn hP (Sum.inl i) = (i.val : ℝ) := markKey_vertex hn hP i

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n} {q : Plane} {ε : ℝ}
  (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)

/-- The soft mark map on the source marks (vertices by `softOldIndex`, visits by
`softInheritedVisit`). -/
abbrev sfta_softMap : Mark P → Mark (softInsertion P j q ε) :=
  Sum.map (softOldIndex j) (softInheritedVisit hp)

include hn hP hQ in
/-- The traversal keys of transported marks compare as the parent keys, except that when `j = 0`
the attachment vertex `inl 0` (which moves to the label `n`) is excluded. -/
theorem sfta_soft_markKey_lt_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
    (a b : Mark P) (ha : a = Sum.inl j → j ≠ 0) (hb : b = Sum.inl j → j ≠ 0) :
    markKey (by omega) hQ.1 (sfta_softMap hp a) < markKey (by omega) hQ.1 (sfta_softMap hp b) ↔
      markKey hn hP.1 a < markKey hn hP.1 b := by
  cases a with
  | inl i =>
    cases b with
    | inl k =>
      simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, Nat.cast_lt]
      by_cases hj : j = 0
      · subst hj
        have hi : i ≠ 0 := fun h => ha (by rw [h]) rfl
        have hk : k ≠ 0 := fun h => hb (by rw [h]) rfl
        rw [sfta_softOldIndex_zero_val, sfta_softOldIndex_zero_val, if_neg hi, if_neg hk]
      · rw [sfta_softOldIndex_val_of_ne_zero j i hj, sfta_softOldIndex_val_of_ne_zero j k hj]
        split_ifs <;> omega
    | inr w =>
      simp only [sfta_softMap, Sum.map_inl, Sum.map_inr, sfta_markKey_vertex_eq,
        sfta_markKey_visit_eq, softInheritedVisit_edge]
      have hw := visitPosition_interior hn hP.1 w
      have hw' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp w)
      rw [sfta_nat_lt_add_iff _ _ hw'.1 hw'.2, sfta_nat_lt_add_iff _ _ hw.1 hw.2]
      by_cases hj : j = 0
      · subst hj
        have hi : i ≠ 0 := fun h => ha (by rw [h]) rfl
        rw [sfta_softOldIndex_zero_val, if_neg hi, sfta_softParentEdge_zero_val]
      · rw [sfta_softOldIndex_val_of_ne_zero j i hj, sfta_softParentEdge_val_of_ne_zero j _ hj]
        split_ifs <;> omega
  | inr v =>
    cases b with
    | inl k =>
      simp only [sfta_softMap, Sum.map_inl, Sum.map_inr, sfta_markKey_vertex_eq,
        sfta_markKey_visit_eq, softInheritedVisit_edge]
      have hv := visitPosition_interior hn hP.1 v
      have hv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
      rw [sfta_add_lt_nat_iff _ _ hv'.1 hv'.2, sfta_add_lt_nat_iff _ _ hv.1 hv.2]
      by_cases hj : j = 0
      · subst hj
        have hk : k ≠ 0 := fun h => hb (by rw [h]) rfl
        rw [sfta_softOldIndex_zero_val, if_neg hk, sfta_softParentEdge_zero_val]
      · rw [sfta_softOldIndex_val_of_ne_zero j k hj, sfta_softParentEdge_val_of_ne_zero j _ hj]
        split_ifs <;> omega
    | inr w =>
      simp only [sfta_softMap, Sum.map_inr, markKey_visit]
      rw [visitKey_lt_iff, visitKey_lt_iff]
      simp only [softInheritedVisit_edge, softParentEdge_val_lt_iff,
        (softParentEdge_injective j).eq_iff]
      exact or_congr Iff.rfl (and_congr_right (fun he => hord v w he))

include hn hP hQ in
theorem sfta_soft_markKey_le_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
    (a b : Mark P) (ha : a = Sum.inl j → j ≠ 0) (hb : b = Sum.inl j → j ≠ 0) :
    markKey (by omega) hQ.1 (sfta_softMap hp a) ≤ markKey (by omega) hQ.1 (sfta_softMap hp b) ↔
      markKey hn hP.1 a ≤ markKey hn hP.1 b := by
  simpa only [not_lt] using not_congr (sfta_soft_markKey_lt_iff hn hP hQ hp hord b a hb ha)

include hn hP hQ in
/-- `j ≠ 0`: the new vertex sits strictly above the attachment vertex and below every transported
mark that follows the attachment vertex. -/
theorem sfta_soft_new_key (hj : j ≠ 0) :
    markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) = (j.val : ℝ) + 1 ∧
    markKey (by omega) hQ.1 (sfta_softMap hp (Sum.inl j)) = (j.val : ℝ) := by
  simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, sfta_softNewIndex_val_of_ne_zero j hj,
    sfta_softOldIndex_val_of_ne_zero j j hj, le_refl, ite_true, Nat.cast_add, Nat.cast_one]
  exact ⟨trivial, trivial⟩

include hn hP hQ in
theorem sfta_soft_new_key_le (hj : j ≠ 0) (w : Mark P) (hw : w ≠ Sum.inl j)
    (hlt : markKey hn hP.1 (Sum.inl j) < markKey hn hP.1 w) :
    markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) ≤ markKey (by omega) hQ.1 (sfta_softMap hp w) := by
  rw [(sfta_soft_new_key hn hP hQ hp hj).1]
  cases w with
  | inl i =>
    simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, Nat.cast_lt] at hlt ⊢
    rw [sfta_softOldIndex_val_of_ne_zero j i hj, if_neg (by omega)]
    push_cast
    have : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hlt
    linarith
  | inr v =>
    simp only [sfta_softMap, Sum.map_inr, sfta_markKey_vertex_eq, sfta_markKey_visit_eq,
      softInheritedVisit_edge] at hlt ⊢
    have hv := visitPosition_interior hn hP.1 v
    have hv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
    have h1 : j.val ≤ v.2.val.val := by
      by_contra hc
      have : (v.2.val.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (not_le.mp hc)
      linarith
    rw [sfta_softParentEdge_val_of_ne_zero j _ hj, if_neg (by omega)]
    push_cast
    have : (j.val : ℝ) ≤ v.2.val.val := by exact_mod_cast h1
    linarith

include hn hP hQ in
/-- `j = 0`: the new vertex is the label `0`, the old vertex `0` is the label `n`, and every other
transported mark lies strictly between. -/
theorem sfta_soft_zero_keys (hj : j = 0) :
    markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) = 0 ∧
    markKey (by omega) hQ.1 (sfta_softMap hp (Sum.inl j)) = (n : ℝ) ∧
    ∀ w : Mark P, w ≠ Sum.inl j → markKey (by omega) hQ.1 (sfta_softMap hp w) ≤ (n : ℝ) := by
  subst hj
  refine ⟨?_, ?_, ?_⟩
  · rw [sfta_softNewIndex_zero, sfta_markKey_vertex_eq, ZMod.val_zero, Nat.cast_zero]
  · simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, sfta_softOldIndex_zero_val, ite_true]
  · intro w hw
    cases w with
    | inl i =>
      have hi : i ≠ 0 := fun h => hw (by rw [h])
      simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, sfta_softOldIndex_zero_val,
        if_neg hi]
      exact_mod_cast (ZMod.val_lt i).le
    | inr v =>
      simp only [sfta_softMap, Sum.map_inr, sfta_markKey_visit_eq, softInheritedVisit_edge,
        sfta_softParentEdge_zero_val]
      have hv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
      have : (v.2.val.val : ℝ) + 1 ≤ n := by exact_mod_cast ZMod.val_lt v.2.val
      linarith

end SoftKeys

section SoftMarkList

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n}
  {q : Plane} {ε : ℝ} (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)

theorem sfta_softMap_injective : Function.Injective (sfta_softMap hp) :=
  Sum.map_injective.mpr ⟨softOldIndex_injective j, softInheritedVisit_injective hp⟩

theorem sfta_softMap_ne_new (m : Mark P) : sfta_softMap hp m ≠ Sum.inl (softNewIndex j) := by
  cases m with
  | inl i => exact fun h => softOldIndex_ne_new j i (Sum.inl_injective h)
  | inr v => exact Sum.inr_ne_inl

theorem sfta_softMap_exhaust (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
    (m : Mark (softInsertion P j q ε)) :
    m = Sum.inl (softNewIndex j) ∨ ∃ a : Mark P, sfta_softMap hp a = m := by
  cases m with
  | inl a =>
    rcases soft_indices_exhaust j a with h | ⟨k, hk⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨Sum.inl k, by rw [hk]; rfl⟩
  | inr w =>
    obtain ⟨v, hv⟩ := softInheritedVisit_surjective_nonloop hp hclass hnot w
    exact Or.inr ⟨Sum.inr v, by rw [← hv]; rfl⟩

include hn hP in
theorem sfta_softMap_new_notMem :
    Sum.inl (softNewIndex j) ∉ (markList hn hP).map (sfta_softMap hp) := by
  intro h
  obtain ⟨m, _, hm⟩ := List.mem_map.mp h
  exact sfta_softMap_ne_new hp m hm

/-- The head of the sorted mark list is the vertex `0` (the cut of def:gauss). -/
theorem sfta_markList_head : markList hn hP = Sum.inl 0 :: (markList hn hP).tail := by
  obtain ⟨m, hm⟩ := markList_nonempty hn hP
  obtain ⟨h, T, hT⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hm)
  rw [hT, List.tail_cons]
  congr 1
  by_contra hh
  have h0 : Sum.inl (0 : ZMod n) ∈ T := by
    have := mem_markList hn hP (Sum.inl 0)
    rw [hT, List.mem_cons] at this
    exact this.resolve_left (fun h' => hh h'.symm)
  have hs := markList_sorted hn hP
  rw [hT, List.pairwise_cons] at hs
  have h1 := hs.1 _ h0
  have h2 : 0 ≤ markKey hn hP.1 h := traversalKey_nonneg _
  have h3 : markKey hn hP.1 h = markKey hn hP.1 (Sum.inl 0) := by
    rw [sfta_markKey_vertex_eq, ZMod.val_zero, Nat.cast_zero] at h1 ⊢
    linarith
  exact hh (markKey_injective hn hP h3)

include hn hP hQ in
/-- **The sorted mark list of the soft insertion** is the parent list mapped by the soft mark map
with the new vertex `M_ε` inserted immediately after the attachment vertex `μ_j`, up to rotation
(literally when `j ≠ 0`; when `j = 0` the new vertex is the label `0`, the cut moves by one). -/
theorem sfta_soft_markList_insertion (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w)) :
    sfta_IsInsertion (sfta_softMap hp) (Sum.inl j) (Sum.inl (softNewIndex j))
      (markList hn hP) (markList (by omega) hQ) := by
  have hinj := sfta_softMap_injective hp
  have hnew := sfta_softMap_new_notMem hn hP hp
  have hndP := markList_nodup hn hP
  have hndQ := markList_nodup (by omega : 3 ≤ n + 1) hQ
  have hsP := markList_sorted hn hP
  have hsQ := markList_sorted (by omega : 3 ≤ n + 1) hQ
  have hkey := sfta_soft_markKey_le_iff hn hP hQ hp hord
  -- a candidate list which is a permutation of `M_ε :: (parent list).map f` is a permutation of the
  -- sorted mark list of the child
  have hperm : ∀ R : List (Mark (softInsertion P j q ε)),
      R.Perm (Sum.inl (softNewIndex j) :: (markList hn hP).map (sfta_softMap hp)) →
        (markList (by omega) hQ).Perm R := by
    intro R hR
    have hRnd : R.Nodup := hR.nodup_iff.mpr (List.nodup_cons.mpr ⟨hnew, hndP.map hinj⟩)
    apply (List.perm_ext_iff_of_nodup hndQ hRnd).mpr
    intro m
    refine ⟨fun _ => ?_, fun _ => mem_markList _ hQ m⟩
    rw [hR.mem_iff, List.mem_cons, List.mem_map]
    rcases sfta_softMap_exhaust hp hclass hnot m with h | ⟨a, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, mem_markList hn hP a, ha⟩
  by_cases hj : j = 0
  · subst hj
    obtain ⟨hk0, hkn, hkle⟩ := sfta_soft_zero_keys hn hP hQ hp rfl
    have hhead := sfta_markList_head hn hP
    set T := (markList hn hP).tail with hTdef
    have hT : Sum.inl (0 : ZMod n) ∉ T := by
      have := hndP
      rw [hhead, List.nodup_cons] at this
      exact this.1
    have hsT : T.Pairwise (fun a b => markKey hn hP.1 a ≤ markKey hn hP.1 b) := by
      have := hsP
      rw [hhead, List.pairwise_cons] at this
      exact this.2
    have heq : markList (by omega) hQ =
        Sum.inl (softNewIndex (0 : ZMod n)) ::
          (T.map (sfta_softMap hp) ++ [sfta_softMap hp (Sum.inl 0)]) := by
      apply List.Perm.eq_of_pairwise (le := fun a b => markKey (by omega) hQ.1 a ≤ markKey (by omega) hQ.1 b)
        (fun a b _ _ hab hba => markKey_injective _ hQ (le_antisymm hab hba)) hsQ
      · rw [List.pairwise_cons]
        refine ⟨fun w _ => ?_, ?_⟩
        · rw [hk0]; exact traversalKey_nonneg _
        · rw [List.pairwise_append]
          refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
          · rw [List.pairwise_map]
            refine hsT.imp_of_mem (fun {a b} ha hb hab => ?_)
            exact (hkey a b (fun h => absurd (h ▸ ha) hT) (fun h => absurd (h ▸ hb) hT)).mpr hab
          · intro u hu w hw
            rw [List.mem_singleton] at hw
            obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.mp hu
            rw [hw, hkn]
            exact hkle u₀ (fun h => hT (h ▸ hu₀))
      · apply hperm
        rw [hhead, List.map_cons]
        exact List.Perm.cons _ (List.perm_append_singleton _ _)
    refine ⟨[], T, by rw [List.nil_append]; exact hhead, ?_⟩
    rw [heq, List.map_nil, List.nil_append, ← List.cons_append]
    exact List.isRotated_concat _ _
  · obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem (mem_markList hn hP (Sum.inl j))
    obtain ⟨hknew, hkatt⟩ := sfta_soft_new_key hn hP hQ hp hj
    have hsP' : (L₁ ++ Sum.inl j :: L₂).Pairwise (fun a b => markKey hn hP.1 a ≤ markKey hn hP.1 b) := by
      rw [← hL]; exact hsP
    have hndP' : (L₁ ++ Sum.inl j :: L₂).Nodup := by rw [← hL]; exact hndP
    obtain ⟨hL₁, hcons, hcross⟩ := List.pairwise_append.mp hsP'
    obtain ⟨hjL₂, hL₂⟩ := List.pairwise_cons.mp hcons
    have hjnot₂ : Sum.inl j ∉ L₂ := by
      have := (List.nodup_append.mp hndP').2.1
      exact (List.nodup_cons.mp this).1
    have hkey' : ∀ a b : Mark P, markKey (by omega) hQ.1 (sfta_softMap hp a) ≤
        markKey (by omega) hQ.1 (sfta_softMap hp b) ↔ markKey hn hP.1 a ≤ markKey hn hP.1 b :=
      fun a b => hkey a b (fun _ => hj) (fun _ => hj)
    have heq : markList (by omega) hQ =
        L₁.map (sfta_softMap hp) ++ sfta_softMap hp (Sum.inl j) ::
          Sum.inl (softNewIndex j) :: L₂.map (sfta_softMap hp) := by
      apply List.Perm.eq_of_pairwise (le := fun a b => markKey (by omega) hQ.1 a ≤ markKey (by omega) hQ.1 b)
        (fun a b _ _ hab hba => markKey_injective _ hQ (le_antisymm hab hba)) hsQ
      · rw [List.pairwise_append]
        refine ⟨?_, ?_, ?_⟩
        · rw [List.pairwise_map]
          exact hL₁.imp (fun {a b} hab => (hkey' a b).mpr hab)
        · rw [List.pairwise_cons, List.pairwise_cons]
          refine ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩
          · rw [List.mem_cons] at hw
            rcases hw with rfl | hw
            · rw [hknew, hkatt]; linarith
            · obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
              exact (hkey' _ _).mpr (hjL₂ w₀ hw₀)
          · obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
            have hne : w₀ ≠ Sum.inl j := fun h => hjnot₂ (h ▸ hw₀)
            exact sfta_soft_new_key_le hn hP hQ hp hj w₀ hne
              (lt_of_le_of_ne (hjL₂ w₀ hw₀) (fun h => hne (markKey_injective hn hP h).symm))
          · rw [List.pairwise_map]
            exact hL₂.imp (fun {a b} hab => (hkey' a b).mpr hab)
        · intro u hu w hw
          obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.mp hu
          rw [List.mem_cons, List.mem_cons] at hw
          rcases hw with rfl | rfl | hw
          · exact (hkey' _ _).mpr (hcross u₀ hu₀ _ (List.mem_cons_self))
          · have h1 := (hkey' _ _).mpr (hcross u₀ hu₀ _ (List.mem_cons_self))
            rw [hkatt] at h1
            rw [hknew]
            linarith
          · obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
            exact (hkey' _ _).mpr (hcross u₀ hu₀ w₀ (List.mem_cons_of_mem _ hw₀))
      · apply hperm
        rw [hL]
        exact sfta_insert_perm L₁ L₂ _ _ _
    exact ⟨L₁, L₂, hL, by rw [heq]⟩

end SoftMarkList


section InterlacesTransport

/-- Interlacement (def:interlace) in terms of visits: alternating visits of `x` and `y`. -/
theorem sfta_interlaces_iff_visits {n : ℕ} (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (x y : Crossing P) :
    Interlaces hn hP x y ↔ x ≠ y ∧ ∃ u₀ u₁ v₀ v₁ : Visit P,
      u₀.1 = x ∧ u₁.1 = x ∧ v₀.1 = y ∧ v₁.1 = y ∧ u₀ ≠ u₁ ∧ v₀ ≠ v₁ ∧
      traversalBetween (visitPosition hn hP.1 u₀) (visitPosition hn hP.1 v₀) (visitPosition hn hP.1 u₁) ∧
      traversalBetween (visitPosition hn hP.1 u₁) (visitPosition hn hP.1 v₁) (visitPosition hn hP.1 u₀) := by
  constructor
  · rintro ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀, h₁⟩
    refine ⟨hxy, ⟨x, x₀⟩, ⟨x, x₁⟩, ⟨y, y₀⟩, ⟨y, y₁⟩, rfl, rfl, rfl, rfl, ?_, ?_, h₀, h₁⟩
    · intro h; exact hx (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    · intro h; exact hy (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · rintro ⟨hxy, ⟨c₀, x₀⟩, ⟨c₁, x₁⟩, ⟨d₀, y₀⟩, ⟨d₁, y₁⟩, h₀, h₁, h₂, h₃, hu, hv, hb₀, hb₁⟩
    dsimp only at h₀ h₁ h₂ h₃
    subst h₀; subst h₁; subst h₂; subst h₃
    refine ⟨hxy, x₀, x₁, y₀, y₁, ?_, ?_, hb₀, hb₁⟩
    · intro h; exact hu (by rw [h])
    · intro h; exact hv (by rw [h])

/-- Interlacement is carried by compatible crossing/visit bijections preserving the cyclic order
of the visit positions. -/
theorem sfta_interlaces_transport {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m) {P : LabelledTuple n}
    {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q) (cross : Crossing P ≃ Crossing Q)
    (visit : Visit P ≃ Visit Q) (hfst : ∀ v, (visit v).1 = cross v.1)
    (hbtw : ∀ u v w : Visit P,
      traversalBetween (visitPosition hm hQ.1 (visit u)) (visitPosition hm hQ.1 (visit v))
        (visitPosition hm hQ.1 (visit w)) ↔
      traversalBetween (visitPosition hn hP.1 u) (visitPosition hn hP.1 v) (visitPosition hn hP.1 w))
    (x y : Crossing P) :
    Interlaces hm hQ (cross x) (cross y) ↔ Interlaces hn hP x y := by
  rw [sfta_interlaces_iff_visits hm hQ, sfta_interlaces_iff_visits hn hP]
  refine and_congr cross.injective.ne_iff ?_
  constructor
  · rintro ⟨u₀, u₁, v₀, v₁, h₀, h₁, h₂, h₃, hu, hv, hb₀, hb₁⟩
    obtain ⟨u₀, rfl⟩ := visit.surjective u₀
    obtain ⟨u₁, rfl⟩ := visit.surjective u₁
    obtain ⟨v₀, rfl⟩ := visit.surjective v₀
    obtain ⟨v₁, rfl⟩ := visit.surjective v₁
    rw [hfst] at h₀ h₁ h₂ h₃
    refine ⟨u₀, u₁, v₀, v₁, cross.injective h₀, cross.injective h₁, cross.injective h₂,
      cross.injective h₃, fun h => hu (by rw [h]), fun h => hv (by rw [h]),
      (hbtw _ _ _).mp hb₀, (hbtw _ _ _).mp hb₁⟩
  · rintro ⟨u₀, u₁, v₀, v₁, h₀, h₁, h₂, h₃, hu, hv, hb₀, hb₁⟩
    refine ⟨visit u₀, visit u₁, visit v₀, visit v₁, ?_, ?_, ?_, ?_, visit.injective.ne hu,
      visit.injective.ne hv, (hbtw _ _ _).mpr hb₀, (hbtw _ _ _).mpr hb₁⟩
    · rw [hfst, h₀]
    · rw [hfst, h₁]
    · rw [hfst, h₂]
    · rw [hfst, h₃]

end InterlacesTransport

section SoftInstance

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n}
  {q : Plane} {ε : ℝ} (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)

include hn hP hQ in
theorem sfta_soft_visitKey_lt_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w)) (v w : Visit P) :
    visitKey (by omega) hQ.1 (softInheritedVisit hp v) < visitKey (by omega) hQ.1 (softInheritedVisit hp w) ↔
      visitKey hn hP.1 v < visitKey hn hP.1 w := by
  rw [visitKey_lt_iff, visitKey_lt_iff]
  simp only [softInheritedVisit_edge, softParentEdge_val_lt_iff, (softParentEdge_injective j).eq_iff]
  exact or_congr Iff.rfl (and_congr_right (hord v w))

include hn hP hQ in
theorem sfta_soft_traversalBetween_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w)) (u v w : Visit P) :
    traversalBetween (visitPosition (by omega) hQ.1 (softInheritedVisit hp u))
      (visitPosition (by omega) hQ.1 (softInheritedVisit hp v))
      (visitPosition (by omega) hQ.1 (softInheritedVisit hp w)) ↔
    traversalBetween (visitPosition hn hP.1 u) (visitPosition hn hP.1 v) (visitPosition hn hP.1 w) := by
  have k := sfta_soft_visitKey_lt_iff hn hP hQ hp hord
  exact or_congr (and_congr (k u v) (k v w))
    (or_congr (and_congr (k v w) (k w u)) (and_congr (k w u) (k u v)))

include hn hP hQ in
theorem sfta_soft_interlaces_iff
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
    (x y : Crossing P) :
    Interlaces (by omega) hQ (softInheritedCrossing hp x) (softInheritedCrossing hp y) ↔
      Interlaces hn hP x y :=
  sfta_interlaces_transport hn (by omega) hP hQ (softCrossingEquivNonloop hp hclass hnot)
    (softVisitEquivNonloop hp hclass hnot) (fun _ => rfl)
    (sfta_soft_traversalBetween_iff hn hP hQ hp hord) x y

/-- **The soft mark transport** `P → P_ε` in the non-loop sectors: vertices by `softOldIndex j`, the
new vertex `softNewIndex j`, attachment `j`, crossings and visits by the accepted inherited maps. -/
def sfta_softTransport (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w)) :
    sfta_InsertMarkTransport hn hP hQ where
  vert := softOldIndex j
  new := softNewIndex j
  att := j
  cross := softCrossingEquivNonloop hp hclass hnot
  visit := softVisitEquivNonloop hp hclass hnot
  visit_fst := fun _ => rfl
  markList_insertion := sfta_soft_markList_insertion hn hP hQ hp hclass hnot hord
  interlaces_iff := fun x y => sfta_soft_interlaces_iff hn hP hQ hp hord hclass hnot x y

variable (hclass : SoftCrossingClassificationAt P j q ε)
  (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
  (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))

@[simp] theorem sfta_softTransport_vert :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).vert = softOldIndex j := rfl

@[simp] theorem sfta_softTransport_new :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).new = softNewIndex j := rfl

@[simp] theorem sfta_softTransport_att :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).att = j := rfl

@[simp] theorem sfta_softTransport_cross (x : Crossing P) :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).cross x = softInheritedCrossing hp x := rfl

@[simp] theorem sfta_softTransport_visit (v : Visit P) :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).visit v = softInheritedVisit hp v := rfl

theorem sfta_softTransport_toMark_inl (i : ZMod n) :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).toMark (Sum.inl i) =
      Sum.inl (softOldIndex j i) := rfl

theorem sfta_softTransport_toMark_inr (v : Visit P) :
    (sfta_softTransport hn hP hQ hp hclass hnot hord).toMark (Sum.inr v) =
      Sum.inr (softInheritedVisit hp v) := rfl

/-- The smoothing corners keep their turns when the crossing signs are inherited
(lem:soft-generic (iii)). -/
theorem sfta_softTransport_markTurn_inr
    (hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge P k) (edge P l))) (v : Visit P) :
    markTurn (softInsertion P j q ε) ((sfta_softTransport hn hP hQ hp hclass hnot hord).toMark (Sum.inr v)) =
      markTurn P (Sum.inr v) := by
  rw [sfta_softTransport_toMark_inr, markTurn_inr, markTurn_inr]
  have ht := (sfta_softTransport hn hP hQ hp hclass hnot hord).twin_eq v
  rw [sfta_softTransport_visit, sfta_softTransport_visit] at ht
  rw [← ht]
  simp only [softInheritedVisit_edge]
  unfold crossingSign
  apply hsign
  rw [← visit_crossing_val_eq_pair v]
  exact v.1.property

/-- All mark turns are carried when the vertex turns are (the same-sign sector supplies
`turn P_ε (softOldIndex j j) = −χ₋ = τ_j(P)`). -/
theorem sfta_softTransport_markTurn
    (hvert : ∀ k : ZMod n, turn (softInsertion P j q ε) (softOldIndex j k) = turn P k)
    (hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge P k) (edge P l))) (m : Mark P) :
    markTurn (softInsertion P j q ε) ((sfta_softTransport hn hP hQ hp hclass hnot hord).toMark m) =
      markTurn P m := by
  cases m with
  | inl i => rw [sfta_softTransport_toMark_inl, markTurn_inl, markTurn_inl]; exact hvert i
  | inr v => exact sfta_softTransport_markTurn_inr hn hP hQ hp hclass hnot hord hsign v

end SoftInstance

section SoftData


/-- **The soft data on one interval** (from lem:soft-generic, `soft_family_generic`): for every
small `ε > 0` and every genericity proof of `P_ε`, the crossing persistence and classification, the
same-edge visit order, the vertex turns (`k ≠ j` kept; `−χ₋` at `μ_j`, `−χ₊` at `M_ε`), and the
inherited crossing signs — exactly the hypotheses of `sfta_softTransport` and
`sfta_softTransport_markTurn`. -/
theorem sfta_soft_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ _hQ : Generic (softInsertion P j q ε),
      ∃ (hp : SoftCrossingPersistence P j q ε) (_hclass : SoftCrossingClassificationAt P j q ε),
        (∀ v w : Visit P, v.2.val = w.2.val →
          (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
            visitParameter v < visitParameter w)) ∧
        (∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k) ∧
        turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
        turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q ∧
        (∀ k l : ZMod n, IsCrossing P {k, l} →
          SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l))) := by
  obtain ⟨δ, hδ, _B, hall⟩ := (soft_family_generic hn hP j q hq).2.2.2.2.2
  refine ⟨δ, hδ, fun ε hε hεδ _hQ => ?_⟩
  obtain ⟨_, hp, hclass, _, hii, hiii, hord, _, _⟩ := hall ε hε hεδ
  exact ⟨hp, hclass, hord, hii.2.2.2.1, hii.2.2.2.2.1, hii.2.2.2.2.2.1,
    fun k l hc => (hiii k l hc).2.2.2.1⟩

end SoftData


/-! ### U112-C helpers (prefix `sftc_`) for the leaf `sft_same_sign` (PLAN_FINAL.md §3.4, §4 U112-C).

Route.  The soft mark transport `sfta_softTransport` (U112-A) carries the state sum up to the sign
`(−1)^{ℓ(P_ε)+ℓ(P)}` once, for every decomposition `S` and carrier `q`, (a) the rotations agree and (b) the
HOMFLY polynomials of the positive lifts agree (`sfta_InsertMarkTransport.cornerStateSum_transport`).
(b) is combinatorial: the record of a positive lift is the abstract Gauss record of the carrier's
crossings (`CB.positiveLiftRecordIso`, cb:products KL1), the two Gauss records are isomorphic through the
inherited-visit bijection (order by the same-edge parameter clause of lem:soft-generic, twins, over bits by
the inherited crossing signs), and rp:record-polynomial (`presentations`) with `P_eq_homfly` closes.
(a) is analytic: `2π r_Q` is the sum of the mark principal turns over the corner marks (`sge_rotation_eq_sum`);
in `P_ε` every transported corner has the turn `∠(dir_ε(in), dir_ε(out))` where `dir_ε e` is the parent
direction (`edge P e`, or `edge P j − ε q` for the return edge), and the two corners `μ_j, M_ε` merge by
angle addition into `∠(u, v − ε q)`; so `2π r_{Q_ε} = F(ε)` for an explicit `F` continuous at `0` with
`F(0) = 2π r_Q`, and integrality pins `r_{Q_ε} = r_Q` for all small `ε`, uniformly over the finitely many
`(S, q)`.  Finally `ℓ(P_ε) = ℓ(P) + [τ = 1]` (`leftTurns_transport`) gives the sign `−τ`. -/

section SftcData

/-- The soft data on one interval, as `sfta_soft_data` plus the return-edge sign of lem:soft-generic (ii):
`sgn det(u, v − ε q) = τ_j(P)`. -/
theorem sftc_soft_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ _hQ : Generic (softInsertion P j q ε),
      ∃ (hp : SoftCrossingPersistence P j q ε) (_hclass : SoftCrossingClassificationAt P j q ε),
        (∀ v w : Visit P, v.2.val = w.2.val →
          (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
            visitParameter v < visitParameter w)) ∧
        (∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k) ∧
        turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
        turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q ∧
        (∀ k l : ZMod n, IsCrossing P {k, l} →
          SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l))) ∧
        SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
          turn P j := by
  obtain ⟨δ, hδ, _B, hall⟩ := (soft_family_generic hn hP j q hq).2.2.2.2.2
  refine ⟨δ, hδ, fun ε hε hεδ _hQ => ?_⟩
  obtain ⟨_, hp, hclass, _, hii, hiii, hord, _, _⟩ := hall ε hε hεδ
  exact ⟨hp, hclass, hord, hii.2.2.2.1, hii.2.2.2.2.1, hii.2.2.2.2.2.1,
    fun k l hc => (hiii k l hc).2.2.2.1, hii.2.2.2.2.2.2.1⟩

end SftcData

section SftcDirections

variable (P : LabelledTuple n) (j : ZMod n) (q : Plane)

/-- The direction of the parent edge `e` in `P_ε`: unchanged except for the return edge (`e = j`), whose
direction is `v − ε q`.  Defined for every real `ε` (affine in `ε`), so that it can be studied at `ε = 0`. -/
def sftc_dir (ε : ℝ) (e : ZMod n) : Plane :=
  if e = j then edge P j - ε • q else edge P e

omit [NeZero n] in
theorem sftc_dir_of_ne (ε : ℝ) {e : ZMod n} (he : e ≠ j) : sftc_dir P j q ε e = edge P e := by
  simp only [sftc_dir, he, ite_false]

omit [NeZero n] in
theorem sftc_dir_att (ε : ℝ) : sftc_dir P j q ε j = edge P j - ε • q := by
  simp only [sftc_dir, ite_true]

omit [NeZero n] in
theorem sftc_dir_zero (e : ZMod n) : sftc_dir P j q 0 e = edge P e := by
  unfold sftc_dir
  split_ifs with h
  · rw [h, zero_smul, sub_zero]
  · rfl

omit [NeZero n] in
theorem sftc_continuous_dir (e : ZMod n) : Continuous (fun ε : ℝ => sftc_dir P j q ε e) := by
  unfold sftc_dir
  split_ifs
  · fun_prop
  · exact continuous_const

/-- The parent edge `softParentEdge j e` of `P_ε` has the direction `sftc_dir ε e`
(`edge_softInsertion_old`, `edge_softInsertion_return`). -/
theorem sftc_edge_softParentEdge (ε : ℝ) (e : ZMod n) :
    edge (softInsertion P j q ε) (softParentEdge j e) = sftc_dir P j q ε e := by
  by_cases he : e = j
  · subst he
    rw [softParentEdge_at_attachment, edge_softInsertion_return, sftc_dir_att]
  · rw [softParentEdge_of_ne j e he, edge_softInsertion_old P j e q ε he, sftc_dir_of_ne P j q ε he]

end SftcDirections

section SftcAngles

omit [NeZero n] in
theorem sftc_det_zero_left (v : Plane) : det (0 : Plane) v = 0 := by
  simp [det]

omit [NeZero n] in
theorem sftc_det_zero_right (u : Plane) : det u (0 : Plane) = 0 := by
  simp [det]

omit [NeZero n] in
theorem sftc_det_smul_self (u : Plane) (r : ℝ) : det u (r • u) = 0 := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

omit [NeZero n] in
/-- A transverse pair is a regular pair (re-proof of `regularPair_of_det_ne_zero`, SM/SoftRotation.lean,
which is not in the import closure). -/
theorem sftc_regularPair_of_det_ne_zero {u v : Plane} (h : det u v ≠ 0) : RegularPair u v := by
  refine ⟨fun hu => h (by rw [hu, sftc_det_zero_left]), fun hv => h (by rw [hv, sftc_det_zero_right]), ?_⟩
  rintro ⟨r, -, rfl⟩
  exact h (sftc_det_smul_self u r)

omit [NeZero n] in
theorem sftc_ne_zero_of_det_ne_zero_left {u v : Plane} (h : det u v ≠ 0) : u ≠ 0 :=
  fun hu => h (by rw [hu, sftc_det_zero_left])

omit [NeZero n] in
theorem sftc_ne_zero_of_det_ne_zero_right {u v : Plane} (h : det u v ≠ 0) : v ≠ 0 :=
  fun hv => h (by rw [hv, sftc_det_zero_right])

omit [NeZero n] in
theorem sftc_signType_cases {σ : SignType} (h : σ ≠ 0) : σ = 1 ∨ σ = -1 := by
  rcases SignType.trichotomy σ with h1 | h1 | h1
  · exact Or.inr h1
  · exact absurd h1 h
  · exact Or.inl h1

omit [NeZero n] in
theorem sftc_det_ne_zero_of_sign {u v : Plane} {τ : SignType} (hτ : τ ≠ 0)
    (h : SignType.sign (det u v) = τ) : det u v ≠ 0 := by
  intro h0
  rw [h0, sign_zero] at h
  exact hτ h.symm

omit [NeZero n] in
/-- **Angle addition for principal angles of one sign**: when `∠(u,q)`, `∠(q,w)`, `∠(u,w)` all have the sign
`τ ≠ 0`, `∠(u,q) + ∠(q,w) = ∠(u,w)` exactly (the three angles agree modulo `2π` by
`principalAngle_coe_angle`, and the multiple of `2π` is pinned by the bounds `(−π, π)` and the common sign).
This is the merging of the two turns at `μ_j` and `M_ε` into the turn `∠(u, v − ε q)` of the same-sign sector
(sm-4:1040-1046). -/
theorem sftc_principalAngle_add {u q w : Plane} {τ : SignType} (hτ : τ ≠ 0)
    (h1 : SignType.sign (det u q) = τ) (h2 : SignType.sign (det q w) = τ)
    (h3 : SignType.sign (det u w) = τ) :
    principalAngle u q + principalAngle q w = principalAngle u w := by
  have d1 := sftc_det_ne_zero_of_sign hτ h1
  have d2 := sftc_det_ne_zero_of_sign hτ h2
  have d3 := sftc_det_ne_zero_of_sign hτ h3
  have hu := sftc_ne_zero_of_det_ne_zero_left d1
  have hq := sftc_ne_zero_of_det_ne_zero_right d1
  have hw := sftc_ne_zero_of_det_ne_zero_right d2
  have r1 := sftc_regularPair_of_det_ne_zero d1
  have r2 := sftc_regularPair_of_det_ne_zero d2
  have r3 := sftc_regularPair_of_det_ne_zero d3
  have hang : ((principalAngle u q + principalAngle q w : ℝ) : Real.Angle) =
      (principalAngle u w : Real.Angle) := by
    rw [Real.Angle.coe_add, principalAngle_coe_angle hu hq, principalAngle_coe_angle hq hw,
      principalAngle_coe_angle hu hw]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have b1 := principalAngle_bounds r1
  have b2 := principalAngle_bounds r2
  have b3 := principalAngle_bounds r3
  have s1 := principalAngle_sign r1
  have s2 := principalAngle_sign r2
  have s3 := principalAngle_sign r3
  rw [h1] at s1
  rw [h2] at s2
  rw [h3] at s3
  have hpi := Real.pi_pos
  have hk0 : k = 0 := by
    rcases sftc_signType_cases hτ with rfl | rfl
    · rw [sign_eq_one_iff] at s1 s2 s3
      have hk1 : (k : ℝ) < 1 := by
        by_contra hc
        have : (1 : ℝ) ≤ k := not_lt.mp hc
        nlinarith
      have hk2 : (-1 : ℝ) < k := by
        by_contra hc
        have : (k : ℝ) ≤ -1 := not_lt.mp hc
        nlinarith
      have hk1' : k < 1 := by exact_mod_cast hk1
      have hk2' : -1 < k := by exact_mod_cast hk2
      omega
    · rw [sign_eq_neg_one_iff] at s1 s2 s3
      have hk1 : (k : ℝ) < 1 := by
        by_contra hc
        have : (1 : ℝ) ≤ k := not_lt.mp hc
        nlinarith
      have hk2 : (-1 : ℝ) < k := by
        by_contra hc
        have : (k : ℝ) ≤ -1 := not_lt.mp hc
        nlinarith
      have hk1' : k < 1 := by exact_mod_cast hk1
      have hk2' : -1 < k := by exact_mod_cast hk2
      omega
  rw [hk0] at hk
  simp only [Int.cast_zero, mul_zero] at hk
  linarith

omit [NeZero n] in
theorem sftc_sub_one_ne (hn : 3 ≤ n) (j : ZMod n) : j - 1 ≠ j := by
  intro h
  have h1 : (1 : ZMod n) = 0 := sub_eq_self.mp h
  have := ZMod.one_eq_zero_iff.mp h1
  omega

end SftcAngles

section SftcMarkTurns

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n} {q : Plane} {ε : ℝ}
  (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
  (hclass : SoftCrossingClassificationAt P j q ε)
  (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
  (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))

/-- The explicit mark turn at parameter `ε`: `∠(dir_ε(in-edge of m), dir_ε(out-slot of m))`; at `ε = 0` it is
`sge_markPrincipalTurn`. -/
def sftc_markTurnAt (S : Finset (Crossing P)) (ε : ℝ) (m : Mark P) : ℝ :=
  principalAngle (sftc_dir P j q ε (ccpInEdge hn hP m)) (sftc_dir P j q ε (ccpOutSlot hn hP S m).1)

theorem sftc_markTurnAt_zero (S : Finset (Crossing P)) (m : Mark P) :
    sftc_markTurnAt hn hP (j := j) (q := q) S 0 m = sge_markPrincipalTurn hn hP S m := by
  unfold sftc_markTurnAt sge_markPrincipalTurn
  rw [sftc_dir_zero, sftc_dir_zero]

/-- `softOldIndex j k − 1 = softOldIndex j (k − 1)` when `k − 1 ≠ j` (`softOldIndex_next`). -/
theorem sftc_softOldIndex_pred (j k : ZMod n) (hk : k - 1 ≠ j) :
    softOldIndex j k - 1 = softOldIndex j (k - 1) := by
  have h := softOldIndex_next j (k - 1) hk
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem sftc_softOldIndex_succ_pred (j : ZMod n) :
    softOldIndex j (j + 1) - 1 = softNewIndex j := by
  rw [← softNewIndex_next, add_sub_cancel_right]

theorem sftc_softNewIndex_pred (j : ZMod n) : softNewIndex j - 1 = softOldIndex j j := by
  rw [← softOldIndex_attachment_next, add_sub_cancel_right]

/-- The incoming direction at a transported OLD vertex `k ≠ j`: the parent direction of `E_{k−1}`
(`v − ε q` when `k = j + 1`). -/
theorem sftc_edge_pred_old (k : ZMod n) :
    edge (softInsertion P j q ε) (softOldIndex j k - 1) = sftc_dir P j q ε (k - 1) := by
  by_cases hk1 : k - 1 = j
  · have hk' : k = j + 1 := by rw [← hk1, sub_add_cancel]
    rw [hk1, sftc_dir_att, hk', sftc_softOldIndex_succ_pred, edge_softInsertion_return]
  · rw [sftc_softOldIndex_pred j k hk1, edge_softInsertion_old P j (k - 1) q ε hk1,
      sftc_dir_of_ne P j q ε hk1]

include hn hP hQ hp hclass hnot hord in
/-- **Transported corners keep their explicit turn**: for a true corner `m ≠ μ_j` of `S`, the mark principal
turn of `toMark m` in `P_ε` (at the transported support) is `∠(dir_ε(in m), dir_ε(out m))`. -/
theorem sftc_markPrincipalTurn_toMark (S : Finset (Crossing P)) (m : Mark P) (hm : IsTrueCorner S m)
    (hmj : m ≠ Sum.inl j) :
    sge_markPrincipalTurn (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).toMark m) =
      sftc_markTurnAt hn hP (j := j) (q := q) S ε m := by
  unfold sge_markPrincipalTurn sftc_markTurnAt
  cases m with
  | inl k =>
    have hk : k ≠ j := fun h => hmj (by rw [h])
    rw [sfta_softTransport_toMark_inl, ccpInEdge_vertex, ccpOutSlot_vertex, ccpInEdge_vertex,
      ccpOutSlot_vertex, sftc_edge_pred_old (j := j) (q := q) (ε := ε) k,
      edge_softInsertion_old P j k q ε hk, sftc_dir_of_ne P j q ε hk]
  | inr v =>
    have hv : v.1 ∈ S := hm
    have hv' : ((sfta_softTransport hn hP hQ hp hclass hnot hord).visit v).1 ∈
        (sfta_softTransport hn hP hQ hp hclass hnot hord).support S := by
      rw [(sfta_softTransport hn hP hQ hp hclass hnot hord).visit_fst,
        (sfta_softTransport hn hP hQ hp hclass hnot hord).mem_support]
      exact hv
    rw [(sfta_softTransport hn hP hQ hp hclass hnot hord).toMark_inr, ccpInEdge_visit,
      ccpOutSlot_selected _ hQ _ _ hv', ccpInEdge_visit, ccpOutSlot_selected hn hP S v hv,
      ← (sfta_softTransport hn hP hQ hp hclass hnot hord).twin_eq v]
    simp only [sfta_softTransport_visit, softInheritedVisit_edge]
    rw [sftc_edge_softParentEdge, sftc_edge_softParentEdge]

include hn hP hQ hp hclass hnot hord in
/-- **The two new corners merge**: in the same-sign sector the mark principal turns of `P_ε` at `μ_j` and at
`M_ε` add up to the explicit turn `∠(u, v − ε q)` of the mark `μ_j` (angle addition, all signs `τ`). -/
theorem sftc_markPrincipalTurn_att_new (S : Finset (Crossing P)) (hε : 0 < ε)
    (hs : softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j)
    (hret : SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
      turn P j) :
    sge_markPrincipalTurn (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        (Sum.inl (softOldIndex j j)) +
      sge_markPrincipalTurn (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        (Sum.inl (softNewIndex j)) =
      sftc_markTurnAt hn hP (j := j) (q := q) S ε (Sum.inl j) := by
  have hτ : turn P j ≠ 0 := sft_turn_ne_zero hn hP j
  have hj1 : j - 1 ≠ j := sftc_sub_one_ne hn j
  unfold sge_markPrincipalTurn sftc_markTurnAt
  rw [ccpInEdge_vertex, ccpOutSlot_vertex, ccpInEdge_vertex, ccpOutSlot_vertex, ccpInEdge_vertex,
    ccpOutSlot_vertex, sftc_softOldIndex_pred j j hj1, edge_softInsertion_old P j (j - 1) q ε hj1,
    edge_softInsertion_soft, sftc_softNewIndex_pred, edge_softInsertion_soft, edge_softInsertion_return,
    sftc_dir_of_ne P j q ε hj1, sftc_dir_att]
  -- rescale the soft edge `ε q` to `q`
  have e1 : principalAngle (edge P (j - 1)) (ε • q) = principalAngle (edge P (j - 1)) q := by
    have h := sge_principalAngle_smul one_pos hε (edge P (j - 1)) q
    rwa [one_smul] at h
  have e2 : principalAngle (ε • q) (edge P j - ε • q) = principalAngle q (edge P j - ε • q) := by
    have h := sge_principalAngle_smul hε one_pos q (edge P j - ε • q)
    rwa [one_smul] at h
  rw [e1, e2]
  -- the three signs are `τ`
  have s1 : SignType.sign (det (edge P (j - 1)) q) = turn P j := by
    have h := hs.1
    unfold softAttachmentMinus at h
    rw [neg_eq_iff_eq_neg, neg_neg] at h
    exact h
  have s2 : SignType.sign (det q (edge P j - ε • q)) = turn P j := by
    have h := hs.2
    unfold softAttachmentPlus at h
    rw [neg_eq_iff_eq_neg, neg_neg] at h
    have hd : det q (edge P j - ε • q) = det q (edge P j) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hd]
    exact h
  have s3 : SignType.sign (det (edge P (j - 1)) (edge P j - ε • q)) = turn P j := by
    rw [← edge_softInsertion_return P j q ε]
    exact hret
  exact sftc_principalAngle_add hτ s1 s2 s3

end SftcMarkTurns

section SftcCornerSets

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n} {q : Plane} {ε : ℝ}
  (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
  (hclass : SoftCrossingClassificationAt P j q ε)
  (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
  (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))

include hn hP hQ hp hclass hnot hord in
/-- **The corner marks of a transported carrier**: the transported corner marks of `q`, plus the new vertex
`M_ε` exactly when `q` is the carrier through the attachment vertex `μ_j`. -/
theorem sftc_mem_cornerSet_Q (S : Finset (Crossing P)) (qq : Component hn hP S)
    (m' : Mark (softInsertion P j q ε)) :
    m' ∈ sge_cornerSet (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq) ↔
      (m' = Sum.inl (softNewIndex j) ∧ owner hn hP S (Sum.inl j) = qq) ∨
        ∃ m ∈ sge_cornerSet hn hP S qq, (sfta_softTransport hn hP hQ hp hclass hnot hord).toMark m = m' := by
  set τ := sfta_softTransport hn hP hQ hp hclass hnot hord with hτ
  rw [sge_mem_cornerSet]
  rcases τ.exhaust m' with rfl | ⟨m, rfl⟩
  · have hnew : (Sum.inl τ.new : Mark (softInsertion P j q ε)) = Sum.inl (softNewIndex j) := rfl
    rw [hnew]
    constructor
    · rintro ⟨h, -⟩
      left
      refine ⟨rfl, ?_⟩
      rw [← hnew, τ.owner_new] at h
      exact (τ.component S).injective h
    · rintro (⟨-, h⟩ | ⟨m, -, hm⟩)
      · refine ⟨?_, trivial⟩
        have hatt : τ.att = j := rfl
        rw [← hnew, τ.owner_new, hatt, h]
      · exact absurd hm (τ.toMark_ne_new m)
  · rw [τ.owner_toMark_eq_iff, τ.isTrueCorner_transport]
    constructor
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨m, (sge_mem_cornerSet hn hP S qq m).mpr ⟨h1, h2⟩, rfl⟩
    · rintro (⟨h, -⟩ | ⟨m₀, hm₀, hm⟩)
      · exact absurd h (τ.toMark_ne_new m)
      · rw [τ.toMark_injective hm] at hm₀
        exact (sge_mem_cornerSet hn hP S qq m).mp hm₀

include hn hP hQ hp hclass hnot hord in
/-- **The turn ledger of a transported carrier**: the sum of the mark principal turns of `P_ε` over the corner
marks of the transported carrier equals the sum of the explicit turns `∠(dir_ε(in), dir_ε(out))` over the
corner marks of `q` (same-sign sector, `ε > 0`, with the return-edge sign of lem:soft-generic (ii)). -/
theorem sftc_sum_cornerSet_Q (S : Finset (Crossing P)) (qq : Component hn hP S) (hε : 0 < ε)
    (hs : softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j)
    (hret : SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
      turn P j) :
    ∑ m' ∈ sge_cornerSet (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq),
      sge_markPrincipalTurn (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S) m' =
    ∑ m ∈ sge_cornerSet hn hP S qq, sftc_markTurnAt hn hP (j := j) (q := q) S ε m := by
  set τ := sfta_softTransport hn hP hQ hp hclass hnot hord with hτ
  set T := sge_cornerSet hn hP S qq with hT
  have hinj : Set.InjOn τ.toMark (T : Set (Mark P)) := fun a _ b _ h => τ.toMark_injective h
  have hnew_notin : (Sum.inl (softNewIndex j) : Mark (softInsertion P j q ε)) ∉ T.image τ.toMark := by
    rw [Finset.mem_image]
    rintro ⟨m, -, hm⟩
    exact τ.toMark_ne_new m hm
  have htrue : ∀ m ∈ T, IsTrueCorner S m := fun m hm => ((sge_mem_cornerSet hn hP S qq m).mp hm).2
  by_cases hatt : owner hn hP S (Sum.inl j) = qq
  · have hT' : sge_cornerSet (by omega) hQ (τ.support S) (τ.component S qq) =
        insert (Sum.inl (softNewIndex j)) (T.image τ.toMark) := by
      ext m'
      rw [Finset.mem_insert, Finset.mem_image, sftc_mem_cornerSet_Q hn hP hQ hp hclass hnot hord S qq m']
      constructor
      · rintro (⟨h, -⟩ | h)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl ⟨h, hatt⟩
        · exact Or.inr h
    have hj_mem : Sum.inl j ∈ T := by
      rw [hT, sge_mem_cornerSet]
      exact ⟨hatt, isTrueCorner_vertex S j⟩
    rw [hT', Finset.sum_insert hnew_notin, Finset.sum_image hinj, ← Finset.add_sum_erase T _ hj_mem,
      ← Finset.add_sum_erase T _ hj_mem, ← add_assoc,
      add_comm (sge_markPrincipalTurn _ hQ (τ.support S) (Sum.inl (softNewIndex j))),
      show τ.toMark (Sum.inl j) = Sum.inl (softOldIndex j j) from rfl,
      sftc_markPrincipalTurn_att_new hn hP hQ hp hclass hnot hord S hε hs hret]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmT : m ∈ T := Finset.mem_of_mem_erase hm
    exact sftc_markPrincipalTurn_toMark hn hP hQ hp hclass hnot hord S m (htrue m hmT)
      (Finset.ne_of_mem_erase hm)
  · have hT' : sge_cornerSet (by omega) hQ (τ.support S) (τ.component S qq) = T.image τ.toMark := by
      ext m'
      rw [Finset.mem_image, sftc_mem_cornerSet_Q hn hP hQ hp hclass hnot hord S qq m']
      constructor
      · rintro (⟨-, h⟩ | h)
        · exact absurd h hatt
        · exact h
      · exact fun h => Or.inr h
    rw [hT', Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmj : m ≠ Sum.inl j := by
      rintro rfl
      exact hatt ((sge_mem_cornerSet hn hP S qq _).mp hm).1
    exact sftc_markPrincipalTurn_toMark hn hP hQ hp hclass hnot hord S m (htrue m hm) hmj

include hn hP hQ hp hclass hnot hord in
/-- `2π r_{Q_ε}` for the transported carrier is the explicit turn ledger at `ε`. -/
theorem sftc_rotation_mul_two_pi (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (qq : Component hn hP S) (hε : 0 < ε)
    (hs : softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j)
    (hret : SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
      turn P j) :
    carrierRotation (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq) * (2 * Real.pi) =
      ∑ m ∈ sge_cornerSet hn hP S qq, sftc_markTurnAt hn hP (j := j) (q := q) S ε m := by
  rw [sge_rotation_eq_sum (by omega) hQ
    (((sfta_softTransport hn hP hQ hp hclass hnot hord).isDecomposition_transport S).mpr hS),
    sftc_sum_cornerSet_Q hn hP hQ hp hclass hnot hord S qq hε hs hret]

end SftcCornerSets

section SftcLimit

open Filter Topology

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)

/-- The explicit turn ledger `F_{S,q}(ε) = Σ_{m corner mark of q} ∠(dir_ε(in m), dir_ε(out m))`, a function of the
real parameter `ε` built from `P` alone. -/
def sftc_turnSum (S : Finset (Crossing P)) (qq : Component hn hP S) (ε : ℝ) : ℝ :=
  ∑ m ∈ sge_cornerSet hn hP S qq, sftc_markTurnAt hn hP (j := j) (q := q) S ε m

/-- At `ε = 0` the ledger is `2π r_q` (`sge_rotation_eq_sum`). -/
theorem sftc_turnSum_zero {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (qq : Component hn hP S) :
    sftc_turnSum hn hP j q S qq 0 = carrierRotation hn hP S qq * (2 * Real.pi) := by
  unfold sftc_turnSum
  rw [sge_rotation_eq_sum hn hP hS qq]
  exact Finset.sum_congr rfl fun m _ => sftc_markTurnAt_zero hn hP S m

/-- The ledger is continuous at `ε = 0`: every corner mark is a regular pair of original directions
(`ccp_corner_directions_det_ne_zero`), and `principalAngle` is continuous on regular pairs. -/
theorem sftc_continuousAt_turnSum (S : Finset (Crossing P)) (qq : Component hn hP S) :
    ContinuousAt (sftc_turnSum hn hP j q S qq) 0 := by
  unfold sftc_turnSum sftc_markTurnAt
  apply tendsto_finsetSum
  intro m hm
  have hdet : det (edge P (ccpInEdge hn hP m)) (edge P (ccpOutSlot hn hP S m).1) ≠ 0 :=
    ccp_corner_directions_det_ne_zero hn hP S m ((sge_mem_cornerSet hn hP S qq m).mp hm).2
  have hc : ContinuousAt (fun ε : ℝ => principalAngle (sftc_dir P j q ε (ccpInEdge hn hP m))
      (sftc_dir P j q ε (ccpOutSlot hn hP S m).1)) 0 := by
    apply continuousAt_principalAngle (sftc_continuous_dir P j q _).continuousAt
      (sftc_continuous_dir P j q _).continuousAt
    rw [sftc_dir_zero, sftc_dir_zero]
    exact sftc_regularPair_of_det_ne_zero hdet
  exact hc.tendsto

/-- **Rotation equality for all small `ε`, uniformly in `(S, q)`** (same-sign sector): `2π r_{Q_ε} = F(ε)`,
`2π r_q = F(0)`, `F` continuous at `0`, both rotations integers; so they agree as soon as `|F(ε) − F(0)| < 2π`,
which holds below some `δ` for all of the finitely many `(S, q)` at once. -/
theorem sftc_rotation_eventually (hq : SoftAdmissible P j q)
    (hs : softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ (hQ : Generic (softInsertion P j q ε))
      (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
      (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
      (hord : ∀ v w : Visit P, v.2.val = w.2.val →
        (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
          visitParameter v < visitParameter w))
      (S : Finset (Crossing P)) (_hS : IsDecomposition hn hP S) (qq : Component hn hP S),
      carrierRotation (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq) =
        carrierRotation hn hP S qq := by
  obtain ⟨δ₁, hδ₁, hdata⟩ := sftc_soft_data hn hP j q hq
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Σ S : Finset (Crossing P), Component hn hP S,
      |sftc_turnSum hn hP j q i.1 i.2 ε - sftc_turnSum hn hP j q i.1 i.2 0| < 2 * Real.pi := by
    rw [Filter.eventually_all]
    intro i
    have hc := (sftc_continuousAt_turnSum hn hP j q i.1 i.2).tendsto
    have h := Metric.tendsto_nhds.mp hc (2 * Real.pi) Real.two_pi_pos
    simpa only [Real.dist_eq] using h
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε hlt hQ hp hclass hnot hord S hS qq => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hret⟩ := hdata ε hε (lt_of_lt_of_le hlt (min_le_left _ _)) hQ
  have hF := hδ₂' (y := ε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    exact lt_of_lt_of_le hlt (min_le_right _ _)) ⟨S, qq⟩
  have h1 : carrierRotation (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
      ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq) * (2 * Real.pi) =
      sftc_turnSum hn hP j q S qq ε :=
    sftc_rotation_mul_two_pi hn hP hQ hp hclass hnot hord S hS qq hε hs hret
  have h0 := sftc_turnSum_zero hn hP j q hS qq
  change |sftc_turnSum hn hP j q S qq ε - sftc_turnSum hn hP j q S qq 0| < 2 * Real.pi at hF
  rw [← h1, h0] at hF
  obtain ⟨k₁, hk₁⟩ := carrierRotation_exists_int (by omega) hQ
    (((sfta_softTransport hn hP hQ hp hclass hnot hord).isDecomposition_transport S).mpr hS)
    ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq)
  obtain ⟨k₀, hk₀⟩ := carrierRotation_exists_int hn hP hS qq
  rw [hk₁, hk₀, ← sub_mul, abs_mul, abs_of_pos Real.two_pi_pos] at hF
  have hlt1 : |(k₁ : ℝ) - k₀| < 1 := by
    have hF' : |(k₁ : ℝ) - k₀| * (2 * Real.pi) < 1 * (2 * Real.pi) := by
      rw [one_mul]
      exact hF
    exact lt_of_mul_lt_mul_right hF' Real.two_pi_pos.le
  have hlt1' : |k₁ - k₀| < 1 := by
    have : ((|k₁ - k₀| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs, Int.cast_sub]
      exact hlt1
    exact_mod_cast this
  have hk : k₁ = k₀ := by
    have := abs_lt.mp hlt1'
    omega
  rw [hk₁, hk₀, hk]

end SftcLimit

section SftcRecord

/-- `List.next` commutes with an injective map (the missing `List.next_map`). -/
theorem sftc_next_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) {l : List α} (hl : l.Nodup) (x : α) (hx : x ∈ l)
    (hx' : f x ∈ l.map f) :
    (l.map f).next (f x) hx' = f (l.next x hx) := by
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hl' : (l.map f).Nodup := hl.map hf
  have hi' : i < (l.map f).length := by rw [List.length_map]; exact hi
  rw [sfta_next_eq_of_getElem hl i hi x hx hix.symm,
    sfta_next_eq_of_getElem hl' i hi' (f x) hx' (by rw [List.getElem_map, hix])]
  simp only [List.getElem_map, List.length_map]

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n} {q : Plane} {ε : ℝ}
  (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
  (hclass : SoftCrossingClassificationAt P j q ε)
  (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))
  (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))

include hn hP hQ hp hclass hnot hord in
/-- **The restricted Gauss list is carried literally**: the key-sorted visit list of the transported carrier's
crossings in `P_ε` is the parent list mapped by the inherited-visit bijection (the visit keys compare as the
parent keys, `sfta_soft_visitKey_lt_iff`; sorted nodup lists with the same members are equal). -/
theorem sftc_gaussList_map (S : Finset (Crossing P)) (qq : Component hn hP S) :
    CB.gaussList (CB.cg (by omega) hQ) (carrierCrossings (by omega) hQ
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq)) =
      (CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S qq)).map
        (sfta_softTransport hn hP hQ hp hclass hnot hord).visit := by
  set τ := sfta_softTransport hn hP hQ hp hclass hnot hord with hτ
  have hndL := CB.kl0_gaussList_nodup (CB.cg (by omega) hQ)
    (carrierCrossings (by omega) hQ (τ.support S) (τ.component S qq))
  have hndR : ((CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S qq)).map τ.visit).Nodup :=
    (CB.kl0_gaussList_nodup _ _).map τ.visit.injective
  have hsL : (CB.gaussList (CB.cg (by omega) hQ) (carrierCrossings (by omega) hQ (τ.support S)
      (τ.component S qq))).Pairwise
        (fun v w => visitKey (by omega) hQ.1 v ≤ visitKey (by omega) hQ.1 w) :=
    (geometricGaussList_sorted (CB.cg (by omega) hQ)).sublist List.filter_sublist
  have hsP : (CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S qq)).Pairwise
      (fun v w => visitKey hn hP.1 v ≤ visitKey hn hP.1 w) :=
    (geometricGaussList_sorted (CB.cg hn hP)).sublist List.filter_sublist
  have hsR : ((CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S qq)).map τ.visit).Pairwise
      (fun v w => visitKey (by omega) hQ.1 v ≤ visitKey (by omega) hQ.1 w) := by
    rw [List.pairwise_map]
    refine hsP.imp ?_
    intro a b hab
    rw [← not_lt] at hab ⊢
    intro hlt
    apply hab
    exact (sfta_soft_visitKey_lt_iff hn hP hQ hp hord b a).mp hlt
  apply List.Perm.eq_of_pairwise
    (le := fun v w => visitKey (by omega) hQ.1 v ≤ visitKey (by omega) hQ.1 w)
    (fun a b _ _ hab hba => visitKey_injective (by omega) hQ (le_antisymm hab hba)) hsL hsR
  rw [List.perm_ext_iff_of_nodup hndL hndR]
  intro w
  rw [CB.kl0_mem_gaussList, List.mem_map, τ.carrierCrossings_transport]
  constructor
  · intro hw
    refine ⟨τ.visit.symm w, ?_, τ.visit.apply_symm_apply w⟩
    rw [CB.kl0_mem_gaussList]
    have h1 : (τ.visit (τ.visit.symm w)).1 = τ.cross (τ.visit.symm w).1 := τ.visit_fst _
    rw [τ.visit.apply_symm_apply] at h1
    rw [h1, Finset.mem_map_equiv, Equiv.symm_apply_apply] at hw
    exact hw
  · rintro ⟨v, hv, rfl⟩
    rw [CB.kl0_mem_gaussList] at hv
    rw [τ.visit_fst, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact hv

include hn hP hQ hp hclass hnot hord in
/-- **The abstract Gauss records of corresponding carriers are isomorphic** (rp:record-polynomial's data):
occurrences by the inherited-visit bijection, successor by `sftc_gaussList_map`, pairing by the twin
(`twin_eq`), over bits by the inherited crossing signs (lem:soft-generic (iii)), all signs `+1`. -/
def sftc_gaussRecordIso
    (hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge P k) (edge P l)))
    (S : Finset (Crossing P)) (qq : Component hn hP S) :
    RecordIso (CB.gaussRecord (CB.cg hn hP) (carrierCrossings hn hP S qq))
      (CB.gaussRecord (CB.cg (by omega) hQ) (carrierCrossings (by omega) hQ
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq))) where
  e := Equiv.refl Unit
  Φ := Equiv.subtypeEquiv (sfta_softTransport hn hP hQ hp hclass hnot hord).visit (fun v => by
    rw [(sfta_softTransport hn hP hQ hp hclass hnot hord).visit_fst,
      (sfta_softTransport hn hP hQ hp hclass hnot hord).carrierCrossings_transport,
      Finset.mem_map_equiv, Equiv.symm_apply_apply])
  comp_eq _ := rfl
  succ_eq v := by
    apply Subtype.ext
    have hv : v.1 ∈ CB.gaussList (CB.cg hn hP) (carrierCrossings hn hP S qq) :=
      (CB.kl0_mem_gaussList _ _ _).mpr v.2
    have hv' : (sfta_softTransport hn hP hQ hp hclass hnot hord).visit v.1 ∈
        CB.gaussList (CB.cg (by omega) hQ) (carrierCrossings (by omega) hQ
          ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
          ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq)) := by
      rw [sftc_gaussList_map hn hP hQ hp hclass hnot hord S qq]
      exact List.mem_map.mpr ⟨v.1, hv, rfl⟩
    show (sfta_softTransport hn hP hQ hp hclass hnot hord).visit
        (CB.gaussSucc (CB.cg hn hP) (carrierCrossings hn hP S qq) v).1 =
      (CB.gaussSucc (CB.cg (by omega) hQ) _ ⟨(sfta_softTransport hn hP hQ hp hclass hnot hord).visit v.1, _⟩).1
    rw [CB.gaussSucc_val _ _ v hv, CB.gaussSucc_val _ _ _ hv',
      sfta_next_congr (sftc_gaussList_map hn hP hQ hp hclass hnot hord S qq) _ hv']
    exact (sftc_next_map _ (sfta_softTransport hn hP hQ hp hclass hnot hord).visit.injective
      (CB.kl0_gaussList_nodup _ _) v.1 hv _).symm
  pair_eq v := by
    apply Subtype.ext
    show (sfta_softTransport hn hP hQ hp hclass hnot hord).visit (visitTwin v.1) =
      visitTwin ((sfta_softTransport hn hP hQ hp hclass hnot hord).visit v.1)
    exact (sfta_softTransport hn hP hQ hp hclass hnot hord).twin_eq v.1
  bit_eq v := by
    show CB.positiveOverBit ((sfta_softTransport hn hP hQ hp hclass hnot hord).visit v.1) =
      CB.positiveOverBit v.1
    unfold CB.positiveOverBit
    rw [decide_eq_decide, ← (sfta_softTransport hn hP hQ hp hclass hnot hord).twin_eq v.1]
    have hc : IsCrossing P {v.1.2.val, (visitTwin v.1).2.val} := by
      rw [← visit_crossing_val_eq_pair v.1]
      exact v.1.1.property
    have h := hsign _ _ hc
    change 0 < det (edge (softInsertion P j q ε) (softParentEdge j v.1.2.val))
      (edge (softInsertion P j q ε) (softParentEdge j (visitTwin v.1).2.val)) ↔ _
    rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]
  sgn_eq _ := rfl

include hn hP hQ hp hclass hnot hord in
/-- **HOMFLY equality of the positive lifts** of corresponding carriers: through cb:products' KL1 record bridge
`CB.positiveLiftRecordIso` on both sides, the record isomorphism `sftc_gaussRecordIso`, rp:record-polynomial
(`presentations`) and lp:core's `P_eq_homfly`. -/
theorem sftc_homfly_eq
    (hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge P k) (edge P l)))
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (qq : Component hn hP S) :
    homfly (positiveLift (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq)
        (((sfta_softTransport hn hP hQ hp hclass hnot hord).isDecomposition_transport S).mpr hS)) =
      homfly (positiveLift hn hP S qq hS) := by
  rw [← P_eq_homfly, ← P_eq_homfly]
  apply presentations
  exact ⟨((CB.positiveLiftRecordIso (by omega) hQ
      (((sfta_softTransport hn hP hQ hp hclass hnot hord).isDecomposition_transport S).mpr hS)
      ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq)).trans
    (sftc_gaussRecordIso hn hP hQ hp hclass hnot hord hsign S qq).symm).trans
    (CB.positiveLiftRecordIso hn hP hS qq).symm⟩

end SftcRecord


/-- Same-sign sector `χ₋ = χ₊ = −τ` (sm-4:1024-1057): same Gauss word (lem:soft-generic (iv)), carriers
correspond by contracting the inserted vertex, the carrier through `M` gains one corner of the same sign,
rotations equal (angle addition + integrality), coefficients equal (record / planar isotopy of the positive
lifts), `ℓ(P_ε) = ℓ(P) + [τ = 1]`: `C(P_ε) = −τ C(P)`.  NO floor. -/
theorem sft_same_sign (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q)
    (hs : softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      cornerStateSum (by omega : 3 ≤ n + 1) hQ = -((turn P j : ℤ) * cornerStateSum hn hP) := by
  obtain ⟨δ₁, hδ₁, hdata⟩ := sftc_soft_data hn hP j q hq
  obtain ⟨δ₂, hδ₂, hrot⟩ := sftc_rotation_eventually hn hP j q hq hs
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε hlt hQ => ?_⟩
  have hlt₁ := lt_of_lt_of_le hlt (min_le_left _ _)
  have hlt₂ := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨hp, hclass, hord, hvne, hvj, hnew, hsign, -⟩ := hdata ε hε hlt₁ hQ
  have hτ : turn P j ≠ 0 := sft_turn_ne_zero hn hP j
  -- the same-sign sector is not the loop sector
  have hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) := by
    rintro ⟨h1, -⟩
    have h2 : -turn P j = turn P j := hs.1.symm.trans h1
    rcases sftc_signType_cases hτ with h | h <;> rw [h] at h2 <;> exact absurd h2 (by decide)
  -- the vertex turns are all carried (`−χ₋ = τ` at `μ_j`) and `M_ε` turns like `μ_j` (`−χ₊ = τ`)
  have hvert : ∀ k : ZMod n, turn (softInsertion P j q ε) (softOldIndex j k) = turn P k := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [hvj, hs.1, neg_neg]
    · exact hvne k hk
  have hturn := sfta_softTransport_markTurn hn hP hQ hp hclass hnot hord hvert hsign
  have hnew' : turn (softInsertion P j q ε) (sfta_softTransport hn hP hQ hp hclass hnot hord).new =
      turn P (sfta_softTransport hn hP hQ hp hclass hnot hord).att := by
    show turn (softInsertion P j q ε) (softNewIndex j) = turn P j
    rw [hnew, hs.2, neg_neg]
  have huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ qq : Component hn hP S,
      CarrierUniform (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq) ↔ CarrierUniform hn hP S qq :=
    fun S hS qq => (sfta_softTransport hn hP hQ hp hclass hnot hord).carrierUniform_iff S hS qq hturn hnew'
  have hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (qq : Component hn hP S),
      cornerCoefficient (by omega) hQ ((sfta_softTransport hn hP hQ hp hclass hnot hord).support S)
        ((sfta_softTransport hn hP hQ hp hclass hnot hord).component S qq)
        (((sfta_softTransport hn hP hQ hp hclass hnot hord).isDecomposition_transport S).mpr hS) =
        cornerCoefficient hn hP S qq hS :=
    fun S hS qq => (sfta_softTransport hn hP hQ hp hclass hnot hord).cornerCoefficient_transport hS qq
      (hrot ε hε hlt₂ hQ hp hclass hnot hord S hS qq)
      (sftc_homfly_eq hn hP hQ hp hclass hnot hord hsign S hS qq)
  rw [(sfta_softTransport hn hP hQ hp hclass hnot hord).cornerStateSum_transport huni hcoef]
  -- the left-turn count: `ℓ(P_ε) = ℓ(P) + [τ = 1]`
  have hl := (sfta_softTransport hn hP hQ hp hclass hnot hord).leftTurns_transport (fun i hi => hvne i hi)
  change leftTurns (softInsertion P j q ε) + (if turn P j = 1 then 1 else 0) =
    leftTurns P + (if turn (softInsertion P j q ε) (softOldIndex j j) = 1 then 1 else 0) +
      (if turn (softInsertion P j q ε) (softNewIndex j) = 1 then 1 else 0) at hl
  rw [hvert j, hnew, hs.2, neg_neg] at hl
  rcases sftc_signType_cases hτ with h1 | h1
  · rw [h1] at hl ⊢
    simp only [ite_true] at hl
    have hℓ : leftTurns (softInsertion P j q ε) = leftTurns P + 1 := by omega
    rw [hℓ, show leftTurns P + 1 + leftTurns P = 2 * leftTurns P + 1 by ring, pow_succ, pow_mul,
      neg_one_sq, one_pow, one_mul]
    simp
  · rw [h1] at hl ⊢
    simp only [show (-1 : SignType) ≠ 1 by decide, ite_false, add_zero] at hl
    rw [hl, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    simp

/-! #### U112-B helpers (prefix `sftb_`) for the leaf `sft_mixed`: the thm:C-S5 pattern
(`Carrier.markSuccessor_vertex_of_no_crossing`, CS5.lean:30, re-proved here because `SM.CS5` is not in the
import closure; the draft lemma `cornerStateSum_eq_zero_of_consecutive_opposite`, work/drafts/CS5B.lean:171)
plus the reading of lem:soft-generic (i) as "the soft edge carries no crossing". -/

/-- (U112-B helper) The traversal successor of the vertex mark `μ_i` whose outgoing edge `E_i` carries
no crossing is the next vertex mark `μ_{i+1}` (CS5.lean:30, `Carrier.markSuccessor_vertex_of_no_crossing`,
same proof): by `markSuccessor_position_cases` the only alternative is a mark on `E_i` at positive
parameter, which is a crossing visit on `E_i`. -/
theorem sftb_markSuccessor_vertex_of_no_crossing (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i : ZMod n) (hi : ∀ c : Crossing P, i ∉ c.val) :
    Carrier.markSuccessor hn hP (Sum.inl i) = Sum.inl (i + 1) := by
  rcases Carrier.markSuccessor_position_cases hn hP (Sum.inl i) with ⟨hedge, hlt⟩ | h
  · exfalso
    generalize hm : Carrier.markSuccessor hn hP (Sum.inl i) = m at hedge hlt
    cases m with
    | inl k =>
      change (0 : ℝ) < 0 at hlt
      exact lt_irrefl _ hlt
    | inr v =>
      change v.2.val = i at hedge
      exact hi v.1 (by rw [← hedge]; exact v.2.property)
  · exact h

/-- (U112-B helper) The thm:C-S5 argument for one decomposition `S` (sm-4:934-965): if the consecutive
corners `i`, `i+1` have opposite turns and `E_i` carries no crossing, then `S` is not uniform — the
carrier owning both vertex marks (`smoothingSuccessor` fixes vertex marks and sends `μ_i` to `μ_{i+1}`)
has a left and a right true corner, with their original turns on its corner polygon. -/
theorem sftb_not_uniformDecomposition_of_consecutive_opposite (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i : ZMod n) (hno : ∀ c : Crossing P, i ∉ c.val)
    (hopp : turn P (i + 1) = -turn P i) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) : ¬ UniformDecomposition hn hP S := by
  intro huni
  -- the vertex marks `i` and `i + 1` are smoothing-successor adjacent, hence share their carrier
  have hq1 : owner hn hP S (Sum.inl (i + 1)) = owner hn hP S (Sum.inl i) := by
    rw [← sftb_markSuccessor_vertex_of_no_crossing hn hP i hno,
      ← smoothingSuccessor_vertex hn hP S i]
    exact owner_successor hn hP S (Sum.inl i)
  -- both are true corners of that carrier, with their original turns
  obtain ⟨j₁, hj₁⟩ := ccpCornerMark_exists hn hP S (owner hn hP S (Sum.inl i)) (Sum.inl i) rfl
    (isTrueCorner_vertex S i)
  obtain ⟨j₂, hj₂⟩ := ccpCornerMark_exists hn hP S (owner hn hP S (Sum.inl i)) (Sum.inl (i + 1))
    hq1 (isTrueCorner_vertex S (i + 1))
  have ht₁ := ccpCornerPolygon_turn_vertex hn hP hS _ j₁ i hj₁
  have ht₂ := ccpCornerPolygon_turn_vertex hn hP hS _ j₂ (i + 1) hj₂
  obtain ⟨τ, hτ, hall⟩ := huni (owner hn hP S (Sum.inl i))
  have h1 : τ = turn P i := by rw [← hall j₁, ht₁]
  have h2 : τ = -turn P i := by rw [← hall j₂, ht₂, hopp]
  have h3 : τ = -τ := by rw [← h1] at h2; exact h2
  apply hτ
  revert h3
  cases τ <;> decide

/-- (U112-B helper) The reusable thm:C-S5 lemma (work/drafts/CS5B.lean:171): a generic polygon with two
consecutive corners `i`, `i+1` of opposite turn whose connecting edge `E_i` carries no crossing has
`C(P) = 0` — no decomposition is uniform, so every term of the lem:C-X1 form of def:C vanishes. -/
theorem sftb_cornerStateSum_eq_zero_of_consecutive_opposite (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i : ZMod n) (hno : ∀ c : Crossing P, i ∉ c.val)
    (hopp : turn P (i + 1) = -turn P i) : cornerStateSum hn hP = 0 := by
  rw [cornerStateSum_eq_sum_independentSupports, Finset.sum_eq_zero, mul_zero]
  intro S _
  exact ite_eq_right (sftb_not_uniformDecomposition_of_consecutive_opposite hn hP i hno hopp S.2)

/-- (U112-B helper) Two distinct nonzero signs are opposite. -/
theorem sftb_signType_eq_neg_of_ne {σ τ : SignType} (hσ : σ ≠ 0) (hτ : τ ≠ 0) (hne : σ ≠ τ) :
    τ = -σ := by
  revert hσ hτ hne
  cases σ <;> cases τ <;> decide

omit [NeZero n] in
/-- (U112-B helper) `j - 1 ≠ j` in `ZMod n` for `n ≥ 3`. -/
theorem sftb_sub_one_ne (hn : 3 ≤ n) (j : ZMod n) : j - 1 ≠ j := by
  intro h
  have h1 : (1 : ZMod n) = 0 := sub_eq_self.mp h
  have := ZMod.one_eq_zero_iff.mp h1
  omega

/-- (U112-B helper) The soft edge `E_{softOldIndex j j}` of `P_ε` carries no crossing when its segment is
disjoint from every edge other than its two neighbours `E_{softOldIndex j (j-1)}`, `E_{softNewIndex j}`
(the last clause of lem:soft-generic (i)): a crossing is a pair of REMOTE edges with intersecting
segments (`remote = ¬ adjacent`, def:crossings), and the neighbours are the adjacent edges
(`softOldIndex_next`, `softOldIndex_attachment_next`). -/
theorem sftb_soft_edge_no_crossing (hn : 3 ≤ n) {P : LabelledTuple n} (j : ZMod n) (q : Plane)
    (ε : ℝ)
    (hdisj : ∀ a : ZMod (n + 1), a ≠ softOldIndex j j → a ≠ softOldIndex j (j - 1) →
      a ≠ softNewIndex j →
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) a)) :
    ∀ c : Crossing (softInsertion P j q ε), softOldIndex j j ∉ c.val := by
  intro c hmem
  obtain ⟨a, b, hs, hr, hne⟩ := c.property
  -- the neighbours of the soft edge: `softOldIndex j (j-1) + 1 = softOldIndex j j`,
  -- `softOldIndex j j + 1 = softNewIndex j`
  have hprev : softOldIndex j (j - 1) + 1 = softOldIndex j j := by
    rw [← softOldIndex_next j (j - 1) (sftb_sub_one_ne hn j), sub_add_cancel]
  have hnext : softOldIndex j j + 1 = softNewIndex j := softOldIndex_attachment_next j
  rw [hs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  -- the other edge of the crossing is remote from the soft edge, so it is neither neighbour
  rcases hmem with rfl | rfl
  · -- the soft edge is `a`
    refine (Set.Nonempty.not_disjoint hne) (hdisj b ?_ ?_ ?_)
    · intro hb; apply hr; right; left; rw [hb, sub_self]
    · intro hb; apply hr; left; rw [hb, ← hprev]; ring
    · intro hb; apply hr; right; right; rw [hb, ← hnext]; ring
  · -- the soft edge is `b`
    have hne' : (edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
        edgeSegment (softInsertion P j q ε) a).Nonempty := by rwa [Set.inter_comm]
    refine (Set.Nonempty.not_disjoint hne') (hdisj a ?_ ?_ ?_)
    · intro ha; apply hr; right; left; rw [ha, sub_self]
    · intro ha; apply hr; right; right; rw [ha, ← hprev]; ring
    · intro ha; apply hr; left; rw [ha, ← hnext]; ring

/-- Mixed sector `χ₋ ≠ χ₊` (sm-4:1059-1065): the soft edge carries no crossing (lem:soft-generic (i)), so
`M, M_ε` are consecutive corners of one carrier with opposite turns — no uniform decomposition (the
thm:C-S5 argument, `Carrier.markSuccessor_vertex_of_no_crossing`, CS5.lean:30): `C(P_ε) = 0`.  NO floor. -/
theorem sft_mixed (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q) (hmix : softAttachmentMinus P j q ≠ softAttachmentPlus P j q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      cornerStateSum (by omega : 3 ≤ n + 1) hQ = 0 := by
  -- lem:soft-generic: below `δ` the soft edge carries no crossing and the two new turns are `−χ₋`, `−χ₊`
  obtain ⟨δ, hδ, B, hgen⟩ := (soft_family_generic hn hP j q hq).2.2.2.2.2
  refine ⟨δ, hδ, fun ε hε hlt hQ => ?_⟩
  obtain ⟨_hQ', _hp, _hclass, hI, hII, -⟩ := hgen ε hε hlt
  -- clause (i): the soft edge meets only its two neighbours (at the shared vertices)
  have hno : ∀ c : Crossing (softInsertion P j q ε), softOldIndex j j ∉ c.val :=
    sftb_soft_edge_no_crossing hn j q ε hI.2.2.2.2
  -- clause (ii): the turns at `M = μ_j` and `M_ε` are `−χ₋` and `−χ₊`, opposite in the mixed sector
  have hτ₁ : turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q :=
    hII.2.2.2.2.1
  have hτ₂ : turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q :=
    hII.2.2.2.2.2.1
  have hsigns := softAttachment_signs_nonzero hq
  have hopp : turn (softInsertion P j q ε) (softOldIndex j j + 1) =
      -turn (softInsertion P j q ε) (softOldIndex j j) := by
    rw [softOldIndex_attachment_next, hτ₂, hτ₁,
      sftb_signType_eq_neg_of_ne hsigns.1 hsigns.2 hmix]
  -- `M, M_ε` are consecutive corners of one carrier with opposite turns: thm:C-S5's argument
  exact sftb_cornerStateSum_eq_zero_of_consecutive_opposite (by omega : 3 ≤ n + 1) hQ
    (softOldIndex j j) hno hopp

/-! #### U112-D helpers (prefix `sftd_`) for the leaf `sft_loop`: the loop-sector transport
(PLAN_FINAL.md §3.4 "Loop", §4 U112-D; sm-4:1067-1143).

In the loop sector `χ₋ = χ₊ = τ` the soft insertion `P_ε` has one more crossing than `P`, the
newborn `y` between the incoming edge `E_{j-1}` and the return edge `D_ε`, with its two visits
`a` (incoming) and `b` (return) adjacent in the traversal: the sorted mark list of `P_ε` is the
parent list with the attachment vertex `μ_j` replaced by the block `a, μ_j, M_ε, b`
(`sftd_IsLoopInsertion`).  An abstract *loop transport* `sftd_LoopTransport hn hP hQ` records this
shape together with the inherited crossing/visit maps (injective, onto everything but `y`), the
preserved interlacement of inherited crossings and the isolation of `y`.  From it: the cyclic
successor through the block, the smoothing successor at the enlarged support `S ∪ {y}`
(`supportY`), where the residual map `toMark'` (the attachment vertex goes to `a`) commutes with
the smoothing successors and the triangle `b → μ_j → M_ε → b` is a separate cycle; the carriers
`Component (S ∪ {y}) ≃ Option (Component S)` (`residual`, `tri`); crossings, decompositions,
corner lists, uniformity, the two newborn visits on one carrier for supports omitting `y`
(so lem:corner-values (ii) kills those terms); the signed sum and the left-turn count.  The soft
instance is built from `soft_family_generic` (SoftGenericLemma.lean) and the newborn-arc data of
`soft_newborn_small_empty_arc` (SoftNewbornVisits.lean). -/

section SftdListLayer
variable {α β : Type*}

/-- The loop-sector shape of a mark list: `R` is a rotation of `L` mapped by `f`, with the entry
`f a₀` replaced by the block `[y₁, f a₀, y₂, y₃]` (the marks `a, μ_j, M_ε, b`). -/
def sftd_IsLoopInsertion (f : α → β) (a₀ : α) (y₁ y₂ y₃ : β) (L : List α) (R : List β) : Prop :=
  ∃ L₁ L₂ : List α, L = L₁ ++ a₀ :: L₂ ∧
    R.IsRotated (L₁.map f ++ y₁ :: f a₀ :: y₂ :: y₃ :: L₂.map f)

theorem sftd_block_length (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length = (L₁ ++ a :: L₂).length + 3 := by
  simp only [List.length_append, List.length_map, List.length_cons]; omega

theorem sftd_block_perm (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).Perm
      (y₁ :: y₂ :: y₃ :: (L₁ ++ a :: L₂).map f) := by
  have h1 : (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).Perm
      (y₁ :: (L₁.map f ++ f a :: y₂ :: y₃ :: L₂.map f)) := List.perm_middle
  have h2 : (L₁.map f ++ f a :: y₂ :: y₃ :: L₂.map f).Perm
      (y₂ :: (L₁.map f ++ f a :: y₃ :: L₂.map f)) := by
    have := List.perm_middle (l₁ := L₁.map f ++ [f a]) (a := y₂) (l₂ := y₃ :: L₂.map f)
    simpa only [List.append_assoc, List.singleton_append] using this
  have h3 : (L₁.map f ++ f a :: y₃ :: L₂.map f).Perm
      (y₃ :: (L₁.map f ++ f a :: L₂.map f)) := by
    have := List.perm_middle (l₁ := L₁.map f ++ [f a]) (a := y₃) (l₂ := L₂.map f)
    simpa only [List.append_assoc, List.singleton_append] using this
  refine h1.trans (List.Perm.cons _ (h2.trans (List.Perm.cons _ (h3.trans (List.Perm.cons _ ?_)))))
  simp only [List.map_append, List.map_cons]
  exact List.Perm.refl _

theorem sftd_block_nodup (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (hf : Function.Injective f) (hL : (L₁ ++ a :: L₂).Nodup)
    (h1 : y₁ ∉ (L₁ ++ a :: L₂).map f) (h2 : y₂ ∉ (L₁ ++ a :: L₂).map f)
    (h3 : y₃ ∉ (L₁ ++ a :: L₂).map f) (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).Nodup := by
  refine (sftd_block_perm L₁ L₂ a f y₁ y₂ y₃).nodup_iff.mpr ?_
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨h3, hL.map hf⟩⟩⟩
  · simp only [List.mem_cons, not_or]; exact ⟨h12, h13, h1⟩
  · simp only [List.mem_cons, not_or]; exact ⟨h23, h2⟩

theorem sftd_block_mem (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β) (m : β) :
    m ∈ L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f ↔
      m = y₁ ∨ m = y₂ ∨ m = y₃ ∨ ∃ x ∈ L₁ ++ a :: L₂, f x = m := by
  rw [(sftd_block_perm L₁ L₂ a f y₁ y₂ y₃).mem_iff, List.mem_cons, List.mem_cons, List.mem_cons,
    List.mem_map]

theorem sftd_block_getElem_lt (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β) {i : ℕ}
    (hi : i < L₁.length) (h₁ : i < (L₁ ++ a :: L₂).length)
    (h₂ : i < (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[i] = f ((L₁ ++ a :: L₂)[i]) := by
  rw [List.getElem_append_left (by simpa using hi), List.getElem_append_left hi, List.getElem_map]

theorem sftd_block_getElem_y₁ (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (h₂ : L₁.length < (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[L₁.length] = y₁ := by
  rw [List.getElem_append_right (by simp)]; simp

theorem sftd_block_getElem_att (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (h₂ : L₁.length + 1 < (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[L₁.length + 1] = f a := by
  rw [List.getElem_append_right (by simp)]; simp

theorem sftd_block_getElem_y₂ (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (h₂ : L₁.length + 2 < (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[L₁.length + 2] = y₂ := by
  rw [List.getElem_append_right (by simp)]; simp

theorem sftd_block_getElem_y₃ (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (h₂ : L₁.length + 3 < (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[L₁.length + 3] = y₃ := by
  rw [List.getElem_append_right (by simp)]; simp

theorem sftd_block_getElem_gt (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β) {i : ℕ}
    (hi : L₁.length < i) (h₁ : i < (L₁ ++ a :: L₂).length)
    (h₂ : i + 3 < (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[i + 3] = f ((L₁ ++ a :: L₂)[i]) := by
  rw [List.getElem_append_right (by simp only [List.length_map]; omega),
    List.getElem_append_right (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, i - L₁.length = k + 1 := ⟨i - L₁.length - 1, by omega⟩
  have h3 : i + 3 - (L₁.map f).length = k + 4 := by simp only [List.length_map]; omega
  simp only [h3, hk, List.getElem_cons_succ, List.getElem_map]

variable [DecidableEq α] [DecidableEq β]

/-- `next` in the block list of a transported mark other than the attachment: the transported
successor, except that the predecessor of the attachment goes to `y₁`. -/
theorem sftd_block_next_of_ne (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (hL : (L₁ ++ a :: L₂).Nodup)
    (hR : (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).Nodup)
    (m : α) (hm : m ∈ L₁ ++ a :: L₂) (hne : m ≠ a)
    (hmR : f m ∈ L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).next (f m) hmR =
      if (L₁ ++ a :: L₂).next m hm = a then y₁ else f ((L₁ ++ a :: L₂).next m hm) := by
  have hlen := sftd_block_length L₁ L₂ a f y₁ y₂ y₃
  have hcL : L₁.length < (L₁ ++ a :: L₂).length := by simp
  have hatt := sfta_insert_getElem_att L₁ L₂ a hcL
  obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem hm
  have hic : i ≠ L₁.length := by
    intro h; apply hne; rw [← hiL]; subst h; exact hatt
  -- an entry at an index other than `L₁.length` is not `a`
  have hnot_a : ∀ (k : ℕ) (hk : k < (L₁ ++ a :: L₂).length), k ≠ L₁.length →
      (L₁ ++ a :: L₂)[k] ≠ a := by
    intro k hk hkc h
    apply hkc
    exact List.Nodup.getElem_inj_iff hL |>.mp (h.trans hatt.symm)
  rw [sfta_next_eq_of_getElem hL i hi m hm hiL.symm]
  rcases lt_or_gt_of_ne hic with hlt | hgt
  · have h1 : f m = (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[i]'(by omega) := by
      rw [sftd_block_getElem_lt L₁ L₂ a f y₁ y₂ y₃ hlt hi, hiL]
    rw [sfta_next_eq_of_getElem hR i (by omega) (f m) hmR h1]
    have hmod1 : (i + 1) % (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length = i + 1 :=
      Nat.mod_eq_of_lt (by omega)
    have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = i + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hmod1, hmod2]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hlt) with hlt' | heq
    · rw [ite_eq_right (hnot_a (i + 1) (by omega) (by omega))]
      exact sftd_block_getElem_lt L₁ L₂ a f y₁ y₂ y₃ hlt' (by omega) (by omega)
    · have key : ∀ (k : ℕ) (hk : k < (L₁ ++ a :: L₂).length), k = L₁.length →
          (L₁ ++ a :: L₂)[k] = a := by
        rintro k hk rfl; exact hatt
      have key' : ∀ (k : ℕ) (hk : k < (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length),
          k = L₁.length → (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[k] = y₁ := by
        rintro k hk rfl; exact sftd_block_getElem_y₁ L₁ L₂ a f y₁ y₂ y₃ hk
      rw [ite_eq_left (key (i + 1) (by omega) heq)]
      exact key' (i + 1) (by omega) heq
  · have h1 : f m = (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[i + 3]'(by omega) := by
      rw [sftd_block_getElem_gt L₁ L₂ a f y₁ y₂ y₃ hgt hi, hiL]
    rw [sfta_next_eq_of_getElem hR (i + 3) (by omega) (f m) hmR h1]
    by_cases hlast : i + 1 < (L₁ ++ a :: L₂).length
    · have hmod1 : (i + 3 + 1) % (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length = i + 4 :=
        Nat.mod_eq_of_lt (by omega)
      have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = i + 1 := Nat.mod_eq_of_lt hlast
      simp only [hmod1, hmod2]
      rw [ite_eq_right (hnot_a (i + 1) hlast (by omega))]
      exact sftd_block_getElem_gt L₁ L₂ a f y₁ y₂ y₃ (by omega) hlast (by omega)
    · have hiN : i + 1 = (L₁ ++ a :: L₂).length := by omega
      have hmod1 : (i + 3 + 1) % (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length = 0 := by
        rw [hlen, ← hiN]; simp
      have hmod2 : (i + 1) % (L₁ ++ a :: L₂).length = 0 := by rw [hiN]; simp
      simp only [hmod1, hmod2]
      by_cases hL₁ : L₁.length = 0
      · have key : ∀ (k : ℕ) (hk : k < (L₁ ++ a :: L₂).length), k = L₁.length →
            (L₁ ++ a :: L₂)[k] = a := by
          rintro k hk rfl; exact hatt
        have key' : ∀ (k : ℕ) (hk : k < (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length),
            k = L₁.length → (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f)[k] = y₁ := by
          rintro k hk rfl; exact sftd_block_getElem_y₁ L₁ L₂ a f y₁ y₂ y₃ hk
        rw [ite_eq_left (key 0 (by omega) hL₁.symm)]
        exact key' 0 (by omega) hL₁.symm
      · rw [ite_eq_right (hnot_a 0 (by omega) (Ne.symm hL₁))]
        exact sftd_block_getElem_lt L₁ L₂ a f y₁ y₂ y₃ (by omega) (by omega) (by omega)

omit [DecidableEq α] in
theorem sftd_block_next_y₁ (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (hR : (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).Nodup)
    (hmR : y₁ ∈ L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).next y₁ hmR = f a := by
  have hlen := sftd_block_length L₁ L₂ a f y₁ y₂ y₃
  rw [sfta_next_eq_of_getElem hR L₁.length (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega) y₁ hmR
    (sftd_block_getElem_y₁ L₁ L₂ a f y₁ y₂ y₃ (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)).symm]
  have hmod : (L₁.length + 1) % (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length =
      L₁.length + 1 := Nat.mod_eq_of_lt (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)
  simp only [hmod]
  exact sftd_block_getElem_att L₁ L₂ a f y₁ y₂ y₃ (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)

omit [DecidableEq α] in
theorem sftd_block_next_att (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (hR : (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).Nodup)
    (hmR : f a ∈ L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).next (f a) hmR = y₂ := by
  have hlen := sftd_block_length L₁ L₂ a f y₁ y₂ y₃
  rw [sfta_next_eq_of_getElem hR (L₁.length + 1) (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega) (f a) hmR
    (sftd_block_getElem_att L₁ L₂ a f y₁ y₂ y₃ (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)).symm]
  have hmod : (L₁.length + 1 + 1) % (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length =
      L₁.length + 2 := Nat.mod_eq_of_lt (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)
  simp only [hmod]
  exact sftd_block_getElem_y₂ L₁ L₂ a f y₁ y₂ y₃ (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)

omit [DecidableEq α] in
theorem sftd_block_next_y₂ (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (hR : (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).Nodup)
    (hmR : y₂ ∈ L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).next y₂ hmR = y₃ := by
  have hlen := sftd_block_length L₁ L₂ a f y₁ y₂ y₃
  rw [sfta_next_eq_of_getElem hR (L₁.length + 2) (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega) y₂ hmR
    (sftd_block_getElem_y₂ L₁ L₂ a f y₁ y₂ y₃ (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)).symm]
  have hmod : (L₁.length + 2 + 1) % (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length =
      L₁.length + 3 := Nat.mod_eq_of_lt (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)
  simp only [hmod]
  exact sftd_block_getElem_y₃ L₁ L₂ a f y₁ y₂ y₃ (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)

/-- `next` of the last block entry is the transported successor of the attachment (which is not the
attachment itself when the list has at least two entries). -/
theorem sftd_block_next_y₃ (L₁ L₂ : List α) (a : α) (f : α → β) (y₁ y₂ y₃ : β)
    (hL : (L₁ ++ a :: L₂).Nodup)
    (hR : (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).Nodup)
    (h2 : 2 ≤ (L₁ ++ a :: L₂).length)
    (hmR : y₃ ∈ L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f) (ha : a ∈ L₁ ++ a :: L₂) :
    (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).next y₃ hmR =
      f ((L₁ ++ a :: L₂).next a ha) := by
  have hlen := sftd_block_length L₁ L₂ a f y₁ y₂ y₃
  have hcL : L₁.length < (L₁ ++ a :: L₂).length := by simp
  rw [sfta_next_eq_of_getElem hR (L₁.length + 3) (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega) y₃ hmR
    (sftd_block_getElem_y₃ L₁ L₂ a f y₁ y₂ y₃ (by rw [hlen]; simp only [List.length_append, List.length_cons]; omega)).symm,
    sfta_next_eq_of_getElem hL L₁.length hcL a ha (sfta_insert_getElem_att L₁ L₂ a hcL).symm]
  by_cases hlast : L₁.length + 1 < (L₁ ++ a :: L₂).length
  · have hmod1 : (L₁.length + 3 + 1) % (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length =
        L₁.length + 1 + 3 := Nat.mod_eq_of_lt (by omega)
    have hmod2 : (L₁.length + 1) % (L₁ ++ a :: L₂).length = L₁.length + 1 := Nat.mod_eq_of_lt hlast
    simp only [hmod1, hmod2]
    exact sftd_block_getElem_gt L₁ L₂ a f y₁ y₂ y₃ (by omega) hlast (by omega)
  · have hiN : L₁.length + 1 = (L₁ ++ a :: L₂).length := by omega
    have hmod1 : (L₁.length + 3 + 1) % (L₁.map f ++ y₁ :: f a :: y₂ :: y₃ :: L₂.map f).length = 0 := by
      rw [hlen, ← hiN]; simp
    have hmod2 : (L₁.length + 1) % (L₁ ++ a :: L₂).length = 0 := by rw [hiN]; simp
    simp only [hmod1, hmod2]
    exact sftd_block_getElem_lt L₁ L₂ a f y₁ y₂ y₃ (by omega) (by omega) (by omega)

end SftdListLayer

section SftdLoopTransport

/-- The cyclic successor of `P` has no fixed mark (the mark list has at least three entries). -/
theorem sftd_markSuccessor_ne_self (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (m : Mark P) : markSuccessor hn hP m ≠ m := by
  intro h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (mem_markList hn hP m)
  rw [markSuccessor_getElem hn hP i hi] at h
  have hlen : 3 ≤ (markList hn hP).length := by
    rw [markList_length]; omega
  have h' := (List.Nodup.getElem_inj_iff (markList_nodup hn hP)).mp h
  rcases Nat.lt_or_ge (i + 1) (markList hn hP).length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h'; omega
  · have hiN : i + 1 = (markList hn hP).length := by omega
    rw [hiN, Nat.mod_self] at h'
    omega


/-- A *loop transport* from the generic `n`-gon `P` to the generic `(n+1)`-gon `Q` (the soft
insertion `P ↦ P_ε` in the loop sector `χ₋ = χ₊ = τ`, sm-4:1067-1143): a vertex map `vert` with one
new vertex `new` right after the attachment vertex `att`, one newborn crossing `y` with its two
visits `a` (incoming edge) and `b` (return edge), injective crossing/visit maps onto everything but
`y` (visits over their crossings), the sorted mark list of `Q` a rotation of the transported list
of `P` with the attachment vertex replaced by the block `a, μ_att, M_ε, b`
(`sftd_IsLoopInsertion`), preserved interlacement of the inherited crossings, and the isolation
of `y` ("its visits are adjacent in the Gauss word, so it interlaces no crossing"). -/
structure sftd_LoopTransport (hn : 3 ≤ n) {P : LabelledTuple n} {Q : LabelledTuple (n + 1)}
    (hP : Generic P) (hQ : Generic Q) where
  vert : ZMod n → ZMod (n + 1)
  new : ZMod (n + 1)
  att : ZMod n
  y : Crossing Q
  a : Visit Q
  b : Visit Q
  a_fst : a.1 = y
  b_fst : b.1 = y
  a_ne_b : a ≠ b
  cross : Crossing P → Crossing Q
  visit : Visit P → Visit Q
  cross_injective : Function.Injective cross
  cross_ne : ∀ x, cross x ≠ y
  visit_fst : ∀ v, (visit v).1 = cross v.1
  markList_insertion : sftd_IsLoopInsertion (Sum.map vert visit) (Sum.inl att) (Sum.inr a)
    (Sum.inl new) (Sum.inr b) (markList hn hP) (markList (by omega) hQ)
  interlaces_iff : ∀ x x', Interlaces (by omega) hQ (cross x) (cross x') ↔ Interlaces hn hP x x'
  y_isolated : ∀ x, ¬ Interlaces (by omega) hQ y (cross x)

namespace sftd_LoopTransport

variable {hn : 3 ≤ n} {P : LabelledTuple n} {Q : LabelledTuple (n + 1)} {hP : Generic P}
  {hQ : Generic Q} (τ : sftd_LoopTransport hn hP hQ)

/-- The transported mark (vertices by `vert`, visits by `visit`); misses `inr a`, `inl new`, `inr b`. -/
def toMark : Mark P → Mark Q := Sum.map τ.vert τ.visit

theorem toMark_inl (i : ZMod n) : τ.toMark (Sum.inl i) = Sum.inl (τ.vert i) := rfl

theorem toMark_inr (v : Visit P) : τ.toMark (Sum.inr v) = Sum.inr (τ.visit v) := rfl

/-- The *residual* mark map: the attachment vertex `μ_att` goes to the incoming newborn visit `a`
(the corner `M` is replaced by the smoothing corner `y`, sm-4:1103-1105); every other mark is
transported. -/
def toMark' (m : Mark P) : Mark Q :=
  if m = Sum.inl τ.att then Sum.inr τ.a else τ.toMark m

theorem toMark'_att : τ.toMark' (Sum.inl τ.att) = Sum.inr τ.a := by
  unfold toMark'; rw [ite_eq_left rfl]

theorem toMark'_of_ne (m : Mark P) (hm : m ≠ Sum.inl τ.att) : τ.toMark' m = τ.toMark m := by
  unfold toMark'; rw [ite_eq_right hm]

theorem toMark'_inr (v : Visit P) : τ.toMark' (Sum.inr v) = Sum.inr (τ.visit v) :=
  τ.toMark'_of_ne _ Sum.inr_ne_inl

theorem markList_insertion' : sftd_IsLoopInsertion τ.toMark (Sum.inl τ.att) (Sum.inr τ.a)
    (Sum.inl τ.new) (Sum.inr τ.b) (markList hn hP) (markList (by omega) hQ) :=
  τ.markList_insertion

/-- The sorted mark list of `Q` is a permutation of `a :: M_ε :: b :: (markList P).map toMark`. -/
theorem markList_perm :
    (markList (by omega : 3 ≤ n + 1) hQ).Perm
      (Sum.inr τ.a :: Sum.inl τ.new :: Sum.inr τ.b :: (markList hn hP).map τ.toMark) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  refine hrot.perm.trans ?_
  rw [hL]
  exact sftd_block_perm L₁ L₂ _ _ _ _ _

theorem three_cons_map_nodup :
    (Sum.inr τ.a :: Sum.inl τ.new :: Sum.inr τ.b :: (markList hn hP).map τ.toMark).Nodup :=
  τ.markList_perm.nodup_iff.mp (markList_nodup _ hQ)

theorem toMark_injective : Function.Injective τ.toMark := by
  have h := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp
    τ.three_cons_map_nodup).2).2).2
  intro m m' hmm
  exact List.inj_on_of_nodup_map h (mem_markList hn hP m) (mem_markList hn hP m') hmm

theorem a_notMem_map : Sum.inr τ.a ∉ (markList hn hP).map τ.toMark := by
  have h := (List.nodup_cons.mp τ.three_cons_map_nodup).1
  simp only [List.mem_cons, not_or] at h
  exact h.2.2

theorem new_notMem_map : Sum.inl τ.new ∉ (markList hn hP).map τ.toMark := by
  have h := (List.nodup_cons.mp (List.nodup_cons.mp τ.three_cons_map_nodup).2).1
  simp only [List.mem_cons, not_or] at h
  exact h.2

theorem b_notMem_map : Sum.inr τ.b ∉ (markList hn hP).map τ.toMark :=
  (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp τ.three_cons_map_nodup).2).2).1

theorem toMark_ne_a (m : Mark P) : τ.toMark m ≠ Sum.inr τ.a := fun h =>
  τ.a_notMem_map (List.mem_map.mpr ⟨m, mem_markList hn hP m, h⟩)

theorem toMark_ne_new (m : Mark P) : τ.toMark m ≠ Sum.inl τ.new := fun h =>
  τ.new_notMem_map (List.mem_map.mpr ⟨m, mem_markList hn hP m, h⟩)

theorem toMark_ne_b (m : Mark P) : τ.toMark m ≠ Sum.inr τ.b := fun h =>
  τ.b_notMem_map (List.mem_map.mpr ⟨m, mem_markList hn hP m, h⟩)

theorem visit_injective : Function.Injective τ.visit := fun v w h =>
  Sum.inr_injective (τ.toMark_injective (a₁ := Sum.inr v) (a₂ := Sum.inr w)
    (by rw [toMark_inr, toMark_inr, h]))

theorem vert_injective : Function.Injective τ.vert := fun i k h =>
  Sum.inl_injective (τ.toMark_injective (a₁ := Sum.inl i) (a₂ := Sum.inl k)
    (by rw [toMark_inl, toMark_inl, h]))

theorem vert_ne_new (i : ZMod n) : τ.vert i ≠ τ.new := fun h =>
  τ.toMark_ne_new (Sum.inl i) (by rw [toMark_inl, h])

theorem visit_ne_a (v : Visit P) : τ.visit v ≠ τ.a := fun h =>
  τ.toMark_ne_a (Sum.inr v) (by rw [toMark_inr, h])

theorem visit_ne_b (v : Visit P) : τ.visit v ≠ τ.b := fun h =>
  τ.toMark_ne_b (Sum.inr v) (by rw [toMark_inr, h])

/-- Every mark of `Q` is one of the three new marks or a transported mark. -/
theorem exhaust (m : Mark Q) :
    m = Sum.inr τ.a ∨ m = Sum.inl τ.new ∨ m = Sum.inr τ.b ∨ ∃ m₀ : Mark P, τ.toMark m₀ = m := by
  have hm := τ.markList_perm.mem_iff.mp (mem_markList _ hQ m)
  simp only [List.mem_cons, List.mem_map] at hm
  rcases hm with h | h | h | ⟨m₀, _, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨m₀, h⟩))

theorem vert_exhaust (k : ZMod (n + 1)) : k = τ.new ∨ ∃ i : ZMod n, τ.vert i = k := by
  rcases τ.exhaust (Sum.inl k) with h | h | h | ⟨m, hm⟩
  · exact absurd h Sum.inl_ne_inr
  · exact Or.inl (Sum.inl_injective h)
  · exact absurd h Sum.inl_ne_inr
  · cases m with
    | inl i => exact Or.inr ⟨i, Sum.inl_injective hm⟩
    | inr v => exact absurd hm (by rw [toMark_inr]; exact Sum.inr_ne_inl)

theorem visit_exhaust (w : Visit Q) : w = τ.a ∨ w = τ.b ∨ ∃ v : Visit P, τ.visit v = w := by
  rcases τ.exhaust (Sum.inr w) with h | h | h | ⟨m, hm⟩
  · exact Or.inl (Sum.inr_injective h)
  · exact absurd h Sum.inr_ne_inl
  · exact Or.inr (Or.inl (Sum.inr_injective h))
  · cases m with
    | inl i => exact absurd hm (by rw [toMark_inl]; exact Sum.inl_ne_inr)
    | inr v => exact Or.inr (Or.inr ⟨v, Sum.inr_injective hm⟩)

/-- The two visits of the newborn are exactly `a` and `b`. -/
theorem visit_fst_eq_y_iff (w : Visit Q) : w.1 = τ.y ↔ w = τ.a ∨ w = τ.b := by
  constructor
  · intro hw
    rcases τ.visit_exhaust w with h | h | ⟨v, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (τ.visit_fst v ▸ hw) (τ.cross_ne v.1)
  · rintro (rfl | rfl)
    · exact τ.a_fst
    · exact τ.b_fst

theorem visit_range (w : Visit Q) (hw : w.1 ≠ τ.y) : ∃ v : Visit P, τ.visit v = w := by
  rcases τ.visit_exhaust w with rfl | rfl | h
  · exact absurd τ.a_fst hw
  · exact absurd τ.b_fst hw
  · exact h

theorem cross_range (d : Crossing Q) (hd : d ≠ τ.y) : ∃ x : Crossing P, τ.cross x = d := by
  obtain ⟨i, -, -⟩ := crossing_visits_exist d
  obtain ⟨v, hv⟩ := τ.visit_range ⟨d, i⟩ hd
  exact ⟨v.1, by rw [← τ.visit_fst, hv]⟩

theorem visit_fst_eq_iff (v : Visit P) (x : Crossing P) : (τ.visit v).1 = τ.cross x ↔ v.1 = x := by
  rw [τ.visit_fst]; exact τ.cross_injective.eq_iff

/-- The visit twin is carried to the visit twin; `b` is the twin of `a`. -/
theorem twin_eq (v : Visit P) : τ.visit (visitTwin v) = visitTwin (τ.visit v) := by
  apply visitTwin_unique (τ.visit v) (τ.visit (visitTwin v))
  · rw [τ.visit_fst, τ.visit_fst, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v (τ.visit_injective h)

theorem twin_a : visitTwin τ.a = τ.b :=
  (visitTwin_unique τ.a τ.b (τ.b_fst.trans τ.a_fst.symm) τ.a_ne_b.symm).symm

theorem twin_b : visitTwin τ.b = τ.a := by
  rw [← τ.twin_a, visitTwin_involutive]

/-! ### The residual map -/

theorem toMark'_injective : Function.Injective τ.toMark' := by
  intro m m' h
  by_cases hm : m = Sum.inl τ.att <;> by_cases hm' : m' = Sum.inl τ.att
  · exact hm.trans hm'.symm
  · rw [hm, toMark'_att, τ.toMark'_of_ne m' hm'] at h
    exact absurd h.symm (τ.toMark_ne_a m')
  · rw [hm', toMark'_att, τ.toMark'_of_ne m hm] at h
    exact absurd h (τ.toMark_ne_a m)
  · rw [τ.toMark'_of_ne m hm, τ.toMark'_of_ne m' hm'] at h
    exact τ.toMark_injective h

theorem toMark'_ne_b (m : Mark P) : τ.toMark' m ≠ Sum.inr τ.b := by
  by_cases hm : m = Sum.inl τ.att
  · rw [hm, toMark'_att]; exact fun h => τ.a_ne_b (Sum.inr_injective h)
  · rw [τ.toMark'_of_ne m hm]; exact τ.toMark_ne_b m

theorem toMark'_ne_vatt (m : Mark P) : τ.toMark' m ≠ Sum.inl (τ.vert τ.att) := by
  by_cases hm : m = Sum.inl τ.att
  · rw [hm, toMark'_att]; exact Sum.inr_ne_inl
  · rw [τ.toMark'_of_ne m hm]
    intro h
    exact hm (τ.toMark_injective (a₁ := m) (a₂ := Sum.inl τ.att) (by rw [h, toMark_inl]))

theorem toMark'_ne_new (m : Mark P) : τ.toMark' m ≠ Sum.inl τ.new := by
  by_cases hm : m = Sum.inl τ.att
  · rw [hm, toMark'_att]; exact Sum.inr_ne_inl
  · rw [τ.toMark'_of_ne m hm]; exact τ.toMark_ne_new m

/-- Every mark of `Q` is a triangle mark (`b`, `μ_att`, `M_ε`) or a residual mark. -/
theorem exhaust' (m : Mark Q) :
    m = Sum.inr τ.b ∨ m = Sum.inl (τ.vert τ.att) ∨ m = Sum.inl τ.new ∨
      ∃ m₀ : Mark P, τ.toMark' m₀ = m := by
  rcases τ.exhaust m with h | h | h | ⟨m₀, hm₀⟩
  · exact Or.inr (Or.inr (Or.inr ⟨Sum.inl τ.att, by rw [toMark'_att, h]⟩))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl h
  · by_cases hm : m₀ = Sum.inl τ.att
    · rw [hm, toMark_inl] at hm₀
      exact Or.inr (Or.inl hm₀.symm)
    · exact Or.inr (Or.inr (Or.inr ⟨m₀, by rw [τ.toMark'_of_ne m₀ hm, hm₀]⟩))

/-! ### The cyclic successor through the block -/

theorem markSuccessor_toMark (m : Mark P) (hm : m ≠ Sum.inl τ.att) :
    markSuccessor (by omega) hQ (τ.toMark m) =
      if markSuccessor hn hP m = Sum.inl τ.att then Sum.inr τ.a
      else τ.toMark (markSuccessor hn hP m) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  have hR : (L₁.map τ.toMark ++ Sum.inr τ.a :: τ.toMark (Sum.inl τ.att) :: Sum.inl τ.new ::
      Sum.inr τ.b :: L₂.map τ.toMark).Nodup :=
    hrot.nodup_iff.mp (markList_nodup _ hQ)
  rw [markSuccessor_apply, markSuccessor_apply, nextMark_eq_list_next, nextMark_eq_list_next,
    List.isRotated_next_eq hrot (markList_nodup _ hQ), sfta_next_congr hL]
  exact sftd_block_next_of_ne L₁ L₂ _ τ.toMark _ _ _ hnd hR m
    (hL ▸ mem_markList hn hP m) hm _

theorem markSuccessor_a :
    markSuccessor (by omega) hQ (Sum.inr τ.a) = Sum.inl (τ.vert τ.att) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hR : (L₁.map τ.toMark ++ Sum.inr τ.a :: τ.toMark (Sum.inl τ.att) :: Sum.inl τ.new ::
      Sum.inr τ.b :: L₂.map τ.toMark).Nodup :=
    hrot.nodup_iff.mp (markList_nodup _ hQ)
  rw [markSuccessor_apply, nextMark_eq_list_next, List.isRotated_next_eq hrot (markList_nodup _ hQ)]
  exact sftd_block_next_y₁ L₁ L₂ _ τ.toMark _ _ _ hR _

theorem markSuccessor_vatt :
    markSuccessor (by omega) hQ (Sum.inl (τ.vert τ.att)) = Sum.inl τ.new := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hR : (L₁.map τ.toMark ++ Sum.inr τ.a :: τ.toMark (Sum.inl τ.att) :: Sum.inl τ.new ::
      Sum.inr τ.b :: L₂.map τ.toMark).Nodup :=
    hrot.nodup_iff.mp (markList_nodup _ hQ)
  rw [markSuccessor_apply, nextMark_eq_list_next, List.isRotated_next_eq hrot (markList_nodup _ hQ)]
  exact sftd_block_next_att L₁ L₂ _ τ.toMark _ _ _ hR _

theorem markSuccessor_new :
    markSuccessor (by omega) hQ (Sum.inl τ.new) = Sum.inr τ.b := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hR : (L₁.map τ.toMark ++ Sum.inr τ.a :: τ.toMark (Sum.inl τ.att) :: Sum.inl τ.new ::
      Sum.inr τ.b :: L₂.map τ.toMark).Nodup :=
    hrot.nodup_iff.mp (markList_nodup _ hQ)
  rw [markSuccessor_apply, nextMark_eq_list_next, List.isRotated_next_eq hrot (markList_nodup _ hQ)]
  exact sftd_block_next_y₂ L₁ L₂ _ τ.toMark _ _ _ hR _

theorem markSuccessor_b :
    markSuccessor (by omega) hQ (Sum.inr τ.b) = τ.toMark (markSuccessor hn hP (Sum.inl τ.att)) := by
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  have hR : (L₁.map τ.toMark ++ Sum.inr τ.a :: τ.toMark (Sum.inl τ.att) :: Sum.inl τ.new ::
      Sum.inr τ.b :: L₂.map τ.toMark).Nodup :=
    hrot.nodup_iff.mp (markList_nodup _ hQ)
  have h2 : 2 ≤ (L₁ ++ Sum.inl τ.att :: L₂).length := by
    rw [← hL, markList_length]; omega
  rw [markSuccessor_apply, markSuccessor_apply, nextMark_eq_list_next, nextMark_eq_list_next,
    List.isRotated_next_eq hrot (markList_nodup _ hQ), sfta_next_congr hL]
  exact sftd_block_next_y₃ L₁ L₂ _ τ.toMark _ _ _ hnd hR h2 _ _

/-! ### Supports: the transported support and the enlarged support `S ∪ {y}` -/

/-- The transported support (never contains `y`). -/
def support (S : Finset (Crossing P)) : Finset (Crossing Q) :=
  S.map ⟨τ.cross, τ.cross_injective⟩

theorem mem_support (S : Finset (Crossing P)) (x : Crossing P) :
    τ.cross x ∈ τ.support S ↔ x ∈ S := by
  simp only [support, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x', hx', h⟩
    rw [τ.cross_injective h] at hx'; exact hx'
  · intro hx; exact ⟨x, hx, rfl⟩

theorem y_notMem_support (S : Finset (Crossing P)) : τ.y ∉ τ.support S := by
  intro h
  obtain ⟨x, -, hx⟩ := Finset.mem_map.mp h
  exact τ.cross_ne x hx

theorem support_card (S : Finset (Crossing P)) : (τ.support S).card = S.card := Finset.card_map _

theorem support_injective : Function.Injective τ.support := fun S T h =>
  Finset.map_injective _ h

theorem support_surjective_of_notMem (S' : Finset (Crossing Q)) (hy : τ.y ∉ S') :
    ∃ S, τ.support S = S' := by
  classical
  refine ⟨Finset.univ.filter (fun x => τ.cross x ∈ S'), ?_⟩
  ext d
  simp only [support, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hd
    obtain ⟨x, rfl⟩ := τ.cross_range d (fun h => hy (h ▸ hd))
    exact ⟨x, hd, rfl⟩

/-- The enlarged support `S ∪ {y}`. -/
def supportY (S : Finset (Crossing P)) : Finset (Crossing Q) := insert τ.y (τ.support S)

theorem y_mem_supportY (S : Finset (Crossing P)) : τ.y ∈ τ.supportY S := Finset.mem_insert_self _ _

theorem mem_supportY_cross (S : Finset (Crossing P)) (x : Crossing P) :
    τ.cross x ∈ τ.supportY S ↔ x ∈ S := by
  unfold supportY
  rw [Finset.mem_insert, τ.mem_support]
  exact or_iff_right (τ.cross_ne x)

theorem supportY_card (S : Finset (Crossing P)) : (τ.supportY S).card = S.card + 1 := by
  unfold supportY
  rw [Finset.card_insert_of_notMem (τ.y_notMem_support S), τ.support_card]

theorem supportY_injective : Function.Injective τ.supportY := by
  intro S T h
  apply τ.support_injective
  have h1 : τ.support S = (τ.supportY S).erase τ.y := by
    unfold supportY; rw [Finset.erase_insert (τ.y_notMem_support S)]
  have h2 : τ.support T = (τ.supportY T).erase τ.y := by
    unfold supportY; rw [Finset.erase_insert (τ.y_notMem_support T)]
  rw [h1, h2, h]

theorem supportY_surjective_of_mem (S' : Finset (Crossing Q)) (hy : τ.y ∈ S') :
    ∃ S, τ.supportY S = S' := by
  obtain ⟨S, hS⟩ := τ.support_surjective_of_notMem (S'.erase τ.y) (Finset.notMem_erase _ _)
  refine ⟨S, ?_⟩
  unfold supportY
  rw [hS, Finset.insert_erase hy]

/-! ### The selected-visit exchange and the smoothing successor at the enlarged support -/

theorem selectedMarkPerm_supportY_toMark (S : Finset (Crossing P)) (m : Mark P) :
    selectedMarkPerm (τ.supportY S) (τ.toMark m) = τ.toMark (selectedMarkPerm S m) := by
  cases m with
  | inl i => rfl
  | inr v =>
    rw [toMark_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, toMark_inr]
    have hv' : (τ.visit v).1 ∈ τ.supportY S ↔ v.1 ∈ S := by
      rw [τ.visit_fst, τ.mem_supportY_cross]
    by_cases hv : v.1 ∈ S
    · rw [selectedVisitTwin_of_mem _ _ hv, selectedVisitTwin_of_mem _ _ (hv'.mpr hv), τ.twin_eq]
    · rw [selectedVisitTwin_of_not_mem _ _ hv,
        selectedVisitTwin_of_not_mem _ _ (fun h => hv (hv'.mp h))]

theorem selectedMarkPerm_supportY_a (S : Finset (Crossing P)) :
    selectedMarkPerm (τ.supportY S) (Sum.inr τ.a) = Sum.inr τ.b := by
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem _ _ (τ.a_fst ▸ τ.y_mem_supportY S), τ.twin_a]

theorem selectedMarkPerm_supportY_b (S : Finset (Crossing P)) :
    selectedMarkPerm (τ.supportY S) (Sum.inr τ.b) = Sum.inr τ.a := by
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem _ _ (τ.b_fst ▸ τ.y_mem_supportY S), τ.twin_b]

theorem selectedMarkPerm_support_toMark (S : Finset (Crossing P)) (m : Mark P) :
    selectedMarkPerm (τ.support S) (τ.toMark m) = τ.toMark (selectedMarkPerm S m) := by
  cases m with
  | inl i => rfl
  | inr v =>
    rw [toMark_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, toMark_inr]
    have hv' : (τ.visit v).1 ∈ τ.support S ↔ v.1 ∈ S := by
      rw [τ.visit_fst, τ.mem_support]
    by_cases hv : v.1 ∈ S
    · rw [selectedVisitTwin_of_mem _ _ hv, selectedVisitTwin_of_mem _ _ (hv'.mpr hv), τ.twin_eq]
    · rw [selectedVisitTwin_of_not_mem _ _ hv,
        selectedVisitTwin_of_not_mem _ _ (fun h => hv (hv'.mp h))]

theorem selectedMarkPerm_support_a (S : Finset (Crossing P)) :
    selectedMarkPerm (τ.support S) (Sum.inr τ.a) = Sum.inr τ.a := by
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem _ _ (τ.a_fst ▸ τ.y_notMem_support S)]

theorem selectedMarkPerm_ne_att (S : Finset (Crossing P)) (m : Mark P) (hm : m ≠ Sum.inl τ.att) :
    selectedMarkPerm S m ≠ Sum.inl τ.att := by
  cases m with
  | inl i => exact hm
  | inr v => rw [selectedMarkPerm_visit]; exact Sum.inr_ne_inl

/-- **The residual map commutes with the smoothing successors** at `S ∪ {y}` and `S`
("the remaining swaps `S` act only on that residual cycle"). -/
theorem smoothingSuccessor_supportY_toMark' (S : Finset (Crossing P)) (m : Mark P) :
    smoothingSuccessor (by omega) hQ (τ.supportY S) (τ.toMark' m) =
      τ.toMark' (smoothingSuccessor hn hP S m) := by
  by_cases hm : m = Sum.inl τ.att
  · subst hm
    rw [toMark'_att]
    change markSuccessor (by omega) hQ (selectedMarkPerm (τ.supportY S) (Sum.inr τ.a)) =
      τ.toMark' (markSuccessor hn hP (selectedMarkPerm S (Sum.inl τ.att)))
    rw [τ.selectedMarkPerm_supportY_a, τ.markSuccessor_b, selectedMarkPerm_vertex,
      τ.toMark'_of_ne _ (sftd_markSuccessor_ne_self hn hP _)]
  · rw [τ.toMark'_of_ne m hm]
    change markSuccessor (by omega) hQ (selectedMarkPerm (τ.supportY S) (τ.toMark m)) =
      τ.toMark' (markSuccessor hn hP (selectedMarkPerm S m))
    rw [τ.selectedMarkPerm_supportY_toMark,
      τ.markSuccessor_toMark _ (τ.selectedMarkPerm_ne_att S m hm)]
    unfold toMark'
    rfl

theorem smoothingSuccessor_supportY_b (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.supportY S) (Sum.inr τ.b) = Sum.inl (τ.vert τ.att) := by
  change markSuccessor (by omega) hQ (selectedMarkPerm (τ.supportY S) (Sum.inr τ.b)) = _
  rw [τ.selectedMarkPerm_supportY_b, τ.markSuccessor_a]

theorem smoothingSuccessor_supportY_vatt (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.supportY S) (Sum.inl (τ.vert τ.att)) = Sum.inl τ.new := by
  rw [smoothingSuccessor_vertex]; exact τ.markSuccessor_vatt

theorem smoothingSuccessor_supportY_new (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.supportY S) (Sum.inl τ.new) = Sum.inr τ.b := by
  rw [smoothingSuccessor_vertex]; exact τ.markSuccessor_new

/-- The smoothing successor at the transported support (no `y`) runs through the block
`a → μ_att → M_ε → b`. -/
theorem smoothingSuccessor_support_a (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.support S) (Sum.inr τ.a) = Sum.inl (τ.vert τ.att) := by
  change markSuccessor (by omega) hQ (selectedMarkPerm (τ.support S) (Sum.inr τ.a)) = _
  rw [τ.selectedMarkPerm_support_a, τ.markSuccessor_a]

theorem smoothingSuccessor_support_vatt (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.support S) (Sum.inl (τ.vert τ.att)) = Sum.inl τ.new := by
  rw [smoothingSuccessor_vertex]; exact τ.markSuccessor_vatt

theorem smoothingSuccessor_support_new (S : Finset (Crossing P)) :
    smoothingSuccessor (by omega) hQ (τ.support S) (Sum.inl τ.new) = Sum.inr τ.b := by
  rw [smoothingSuccessor_vertex]; exact τ.markSuccessor_new

/-- For a support omitting `y`, both newborn visits lie on one carrier
(lem:carriers (iii) as used in sm-4:1076-1078). -/
theorem owner_support_a_eq_b (S : Finset (Crossing P)) :
    owner (by omega) hQ (τ.support S) (Sum.inr τ.a) = owner (by omega) hQ (τ.support S) (Sum.inr τ.b) := by
  have h1 := owner_successor (by omega) hQ (τ.support S) (Sum.inr τ.a)
  have h2 := owner_successor (by omega) hQ (τ.support S) (Sum.inl (τ.vert τ.att))
  have h3 := owner_successor (by omega) hQ (τ.support S) (Sum.inl τ.new)
  rw [τ.smoothingSuccessor_support_a] at h1
  rw [τ.smoothingSuccessor_support_vatt] at h2
  rw [τ.smoothingSuccessor_support_new] at h3
  rw [← h1, ← h2, ← h3]

/-! ### Cycles and carriers at the enlarged support -/

theorem pow_toMark' (S : Finset (Crossing P)) (k : ℕ) (m : Mark P) :
    (smoothingSuccessor (by omega) hQ (τ.supportY S) ^ k) (τ.toMark' m) =
      τ.toMark' ((smoothingSuccessor hn hP S ^ k) m) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, τ.smoothingSuccessor_supportY_toMark', pow_succ', Equiv.Perm.mul_apply]

theorem sameCycle_toMark'_iff (S : Finset (Crossing P)) (m m' : Mark P) :
    (smoothingSuccessor (by omega) hQ (τ.supportY S)).SameCycle (τ.toMark' m) (τ.toMark' m') ↔
      (smoothingSuccessor hn hP S).SameCycle m m' := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [τ.pow_toMark'] at hk
    exact ⟨k, by rw [zpow_natCast]; exact τ.toMark'_injective hk⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [zpow_natCast, τ.pow_toMark', hk]⟩

/-- The powers of the smoothing successor on `b` stay in the triangle. -/
theorem pow_b_mem_tri (S : Finset (Crossing P)) (k : ℕ) :
    (smoothingSuccessor (by omega) hQ (τ.supportY S) ^ k) (Sum.inr τ.b) = Sum.inr τ.b ∨
    (smoothingSuccessor (by omega) hQ (τ.supportY S) ^ k) (Sum.inr τ.b) = Sum.inl (τ.vert τ.att) ∨
    (smoothingSuccessor (by omega) hQ (τ.supportY S) ^ k) (Sum.inr τ.b) = Sum.inl τ.new := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases ih with h | h | h <;> rw [h]
    · exact Or.inr (Or.inl (τ.smoothingSuccessor_supportY_b S))
    · exact Or.inr (Or.inr (τ.smoothingSuccessor_supportY_vatt S))
    · exact Or.inl (τ.smoothingSuccessor_supportY_new S)

theorem not_sameCycle_b_toMark' (S : Finset (Crossing P)) (m : Mark P) :
    ¬ (smoothingSuccessor (by omega) hQ (τ.supportY S)).SameCycle (Sum.inr τ.b) (τ.toMark' m) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rcases τ.pow_b_mem_tri S k with h' | h' | h' <;> rw [h'] at hk
  · exact τ.toMark'_ne_b m hk.symm
  · exact τ.toMark'_ne_vatt m hk.symm
  · exact τ.toMark'_ne_new m hk.symm

/-- The residual carrier of a carrier of `S`. -/
def residual (S : Finset (Crossing P)) :
    Component hn hP S → Component (by omega) hQ (τ.supportY S) :=
  Quotient.lift (fun m => owner (by omega) hQ (τ.supportY S) (τ.toMark' m))
    (fun m m' hmm => (owner_eq_iff _ hQ _ _ _).mpr ((τ.sameCycle_toMark'_iff S m m').mpr hmm))

theorem residual_owner (S : Finset (Crossing P)) (m : Mark P) :
    τ.residual S (owner hn hP S m) = owner (by omega) hQ (τ.supportY S) (τ.toMark' m) := rfl

/-- The triangle carrier `(b, μ_att, M_ε)`. -/
def tri (S : Finset (Crossing P)) : Component (by omega) hQ (τ.supportY S) :=
  owner (by omega) hQ (τ.supportY S) (Sum.inr τ.b)

theorem owner_vatt_eq_tri (S : Finset (Crossing P)) :
    owner (by omega) hQ (τ.supportY S) (Sum.inl (τ.vert τ.att)) = τ.tri S := by
  unfold tri
  rw [← τ.smoothingSuccessor_supportY_b S, owner_successor]

theorem owner_new_eq_tri (S : Finset (Crossing P)) :
    owner (by omega) hQ (τ.supportY S) (Sum.inl τ.new) = τ.tri S := by
  rw [← τ.owner_vatt_eq_tri S, ← τ.smoothingSuccessor_supportY_vatt S, owner_successor]

theorem residual_injective (S : Finset (Crossing P)) : Function.Injective (τ.residual S) := by
  intro q r hqr
  obtain ⟨m, rfl⟩ := owner_surjective hn hP S q
  obtain ⟨m', rfl⟩ := owner_surjective hn hP S r
  rw [residual_owner, residual_owner, owner_eq_iff, τ.sameCycle_toMark'_iff] at hqr
  exact (owner_eq_iff hn hP S m m').mpr hqr

theorem residual_ne_tri (S : Finset (Crossing P)) (q : Component hn hP S) : τ.residual S q ≠ τ.tri S := by
  obtain ⟨m, rfl⟩ := owner_surjective hn hP S q
  rw [residual_owner, tri]
  intro h
  exact τ.not_sameCycle_b_toMark' S m ((owner_eq_iff _ hQ _ _ _).mp h.symm)

theorem owner_toMark'_eq_residual_iff (S : Finset (Crossing P)) (q : Component hn hP S) (m : Mark P) :
    owner (by omega) hQ (τ.supportY S) (τ.toMark' m) = τ.residual S q ↔ owner hn hP S m = q := by
  rw [← τ.residual_owner]
  exact (τ.residual_injective S).eq_iff

theorem owner_toMark'_ne_tri (S : Finset (Crossing P)) (m : Mark P) :
    owner (by omega) hQ (τ.supportY S) (τ.toMark' m) ≠ τ.tri S := by
  rw [← τ.residual_owner]; exact τ.residual_ne_tri S _

/-- Every carrier of `S ∪ {y}` is the triangle or a residual carrier. -/
theorem component_cases (S : Finset (Crossing P)) (q' : Component (by omega) hQ (τ.supportY S)) :
    q' = τ.tri S ∨ ∃ q : Component hn hP S, τ.residual S q = q' := by
  obtain ⟨m, rfl⟩ := owner_surjective _ hQ (τ.supportY S) q'
  rcases τ.exhaust' m with rfl | rfl | rfl | ⟨m₀, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl (τ.owner_vatt_eq_tri S)
  · exact Or.inl (τ.owner_new_eq_tri S)
  · exact Or.inr ⟨owner hn hP S m₀, rfl⟩

/-- `Component (S ∪ {y}) ≃ Option (Component S)`: `none ↦ triangle`, `some q ↦ residual q`. -/
def componentEquiv (S : Finset (Crossing P)) :
    Option (Component hn hP S) ≃ Component (by omega) hQ (τ.supportY S) :=
  Equiv.ofBijective (fun o => o.elim (τ.tri S) (τ.residual S))
    ⟨by
      intro o o' h
      cases o with
      | none =>
        cases o' with
        | none => rfl
        | some q => exact absurd h.symm (τ.residual_ne_tri S q)
      | some q =>
        cases o' with
        | none => exact absurd h (τ.residual_ne_tri S q)
        | some q' => exact congrArg some (τ.residual_injective S h),
     by
      intro q'
      rcases τ.component_cases S q' with h | ⟨q, h⟩
      · exact ⟨none, h.symm⟩
      · exact ⟨some q, h⟩⟩

theorem componentEquiv_none (S : Finset (Crossing P)) : τ.componentEquiv S none = τ.tri S := rfl

theorem componentEquiv_some (S : Finset (Crossing P)) (q : Component hn hP S) :
    τ.componentEquiv S (some q) = τ.residual S q := rfl

end sftd_LoopTransport

end SftdLoopTransport

section SftdLoopCarriers

namespace sftd_LoopTransport

variable {hn : 3 ≤ n} {P : LabelledTuple n} {Q : LabelledTuple (n + 1)} {hP : Generic P}
  {hQ : Generic Q} (τ : sftd_LoopTransport hn hP hQ)

/-! ### Crossings of the carriers at the enlarged support -/

/-- The crossings of a residual carrier are the transported crossings of its parent
("all old crossing visits lie on the residual cycle"). -/
theorem carrierCrossings_residual (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossings (by omega) hQ (τ.supportY S) (τ.residual S q) =
      (carrierCrossings hn hP S q).map ⟨τ.cross, τ.cross_injective⟩ := by
  ext d
  rw [mem_carrierCrossings]
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  by_cases hd : d = τ.y
  · subst hd
    constructor
    · rintro ⟨hy, -⟩; exact absurd (τ.y_mem_supportY S) hy
    · rintro ⟨x, -, hx⟩; exact absurd hx (τ.cross_ne x)
  · obtain ⟨x, rfl⟩ := τ.cross_range d hd
    rw [τ.mem_supportY_cross]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨x, (mem_carrierCrossings hn hP S q x).mpr ⟨hx, fun v hv => ?_⟩, rfl⟩
      have h' := h (τ.visit v) (by rw [τ.visit_fst, hv])
      rw [← toMark'_inr, τ.owner_toMark'_eq_residual_iff] at h'
      exact h'
    · rintro ⟨x', hx', hxx⟩
      have hxx' : x' = x := τ.cross_injective hxx
      subst hxx'
      obtain ⟨hx, h⟩ := (mem_carrierCrossings hn hP S q x').mp hx'
      refine ⟨hx, fun w hw => ?_⟩
      obtain ⟨v, rfl⟩ := τ.visit_range w (by rw [hw]; exact τ.cross_ne x')
      have hv : v.1 = x' := (τ.visit_fst_eq_iff v x').mp hw
      rw [← toMark'_inr, τ.owner_toMark'_eq_residual_iff]
      exact h v hv

theorem carrierCrossingCount_residual (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossingCount (by omega) hQ (τ.supportY S) (τ.residual S q) =
      carrierCrossingCount hn hP S q := by
  rw [carrierCrossingCount_eq_card, carrierCrossingCount_eq_card, τ.carrierCrossings_residual,
    Finset.card_map]

/-- The triangle is crossing-free (`y` is selected, every other crossing has its visits on the
residual carriers). -/
theorem carrierCrossings_tri (S : Finset (Crossing P)) :
    carrierCrossings (by omega) hQ (τ.supportY S) (τ.tri S) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro d hd
  obtain ⟨hdS, h⟩ := (mem_carrierCrossings _ hQ _ _ d).mp hd
  have hdy : d ≠ τ.y := fun h' => hdS (h' ▸ τ.y_mem_supportY S)
  obtain ⟨i, -, -⟩ := crossing_visits_exist d
  obtain ⟨v, hv⟩ := τ.visit_range ⟨d, i⟩ hdy
  have h' := h (τ.visit v) (by rw [hv])
  rw [← toMark'_inr] at h'
  exact τ.owner_toMark'_ne_tri S _ h'

theorem carrierCrossingCount_tri (S : Finset (Crossing P)) :
    carrierCrossingCount (by omega) hQ (τ.supportY S) (τ.tri S) = 0 := by
  rw [carrierCrossingCount_eq_card, τ.carrierCrossings_tri, Finset.card_empty]

/-! ### Decompositions -/

/-- `S ∪ {y}` is a decomposition of `Q` iff `S` is one of `P` (`y` interlaces nothing, inherited
interlacement is preserved). -/
theorem isDecomposition_supportY_iff (S : Finset (Crossing P)) :
    IsDecomposition (by omega) hQ (τ.supportY S) ↔ IsDecomposition hn hP S := by
  unfold IsDecomposition
  rw [mem_independentSupports_iff, mem_independentSupports_iff]
  constructor
  · intro h x hx x' hx' hne hI
    exact h _ ((τ.mem_supportY_cross S x).mpr hx) _ ((τ.mem_supportY_cross S x').mpr hx')
      (fun he => hne (τ.cross_injective he)) ((τ.interlaces_iff x x').mpr hI)
  · intro h d hd d' hd' hne hI
    by_cases hdy : d = τ.y
    · subst hdy
      obtain ⟨x', rfl⟩ := τ.cross_range d' (Ne.symm hne)
      exact τ.y_isolated x' hI
    · obtain ⟨x, rfl⟩ := τ.cross_range d hdy
      by_cases hdy' : d' = τ.y
      · subst hdy'
        exact τ.y_isolated x (interlaces_symm _ hQ hI)
      · obtain ⟨x', rfl⟩ := τ.cross_range d' hdy'
        exact h x ((τ.mem_supportY_cross S x).mp hd) x' ((τ.mem_supportY_cross S x').mp hd')
          (fun he => hne (congrArg τ.cross he)) ((τ.interlaces_iff x x').mp hI)

/-! ### True corners, component mark lists and corner lists -/

theorem isTrueCorner_toMark' (S : Finset (Crossing P)) (m : Mark P) :
    IsTrueCorner (τ.supportY S) (τ.toMark' m) ↔ IsTrueCorner S m := by
  by_cases hm : m = Sum.inl τ.att
  · subst hm
    rw [toMark'_att, isTrueCorner_visit, τ.a_fst]
    exact iff_of_true (τ.y_mem_supportY S) trivial
  · rw [τ.toMark'_of_ne m hm]
    cases m with
    | inl i => rw [toMark_inl]; exact Iff.rfl
    | inr v =>
      rw [toMark_inr, isTrueCorner_visit, isTrueCorner_visit, τ.visit_fst, τ.mem_supportY_cross]

theorem notMem_att_of_insertion {L₁ L₂ : List (Mark P)}
    (hL : markList hn hP = L₁ ++ Sum.inl τ.att :: L₂) :
    (∀ m ∈ L₁, m ≠ Sum.inl τ.att) ∧ (∀ m ∈ L₂, m ≠ Sum.inl τ.att) := by
  have hnd := markList_nodup hn hP
  rw [hL] at hnd
  obtain ⟨-, hnd₂, hdisj⟩ := List.nodup_append.mp hnd
  refine ⟨fun m hm h => ?_, fun m hm h => ?_⟩
  · subst h
    exact hdisj (Sum.inl τ.att) hm (Sum.inl τ.att) List.mem_cons_self rfl
  · subst h
    exact (List.nodup_cons.mp hnd₂).1 hm

/-- The component mark list of a residual carrier is the residual image of its parent's, up to
rotation. -/
theorem componentMarkList_residual (S : Finset (Crossing P)) (q : Component hn hP S) :
    (componentMarkList (by omega) hQ (τ.supportY S) (τ.residual S q)).IsRotated
      ((componentMarkList hn hP S q).map τ.toMark') := by
  unfold componentMarkList
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  obtain ⟨hL₁, hL₂⟩ := τ.notMem_att_of_insertion hL
  set p : Mark P → Bool := fun m => decide (owner hn hP S m = q) with hp_def
  set p' : Mark Q → Bool :=
    fun m' => decide (owner (by omega) hQ (τ.supportY S) m' = τ.residual S q) with hp'_def
  have hp : ∀ m, p' (τ.toMark' m) = p m := fun m =>
    decide_eq_decide.mpr (τ.owner_toMark'_eq_residual_iff S q m)
  have hmap : ∀ (L : List (Mark P)), (∀ m ∈ L, m ≠ Sum.inl τ.att) →
      (L.map τ.toMark).filter p' = (L.filter p).map τ.toMark' := by
    intro L hLne
    rw [List.map_congr_left (fun m hm => (τ.toMark'_of_ne m (hLne m hm)).symm), List.filter_map]
    congr 1
    exact List.filter_congr (fun m _ => hp m)
  have h1 : p' (τ.toMark (Sum.inl τ.att)) = false := by
    simp only [hp'_def, toMark_inl, τ.owner_vatt_eq_tri, decide_eq_false_iff_not]
    exact (τ.residual_ne_tri S q).symm
  have h2 : p' (Sum.inl τ.new) = false := by
    simp only [hp'_def, τ.owner_new_eq_tri, decide_eq_false_iff_not]
    exact (τ.residual_ne_tri S q).symm
  have h3 : p' (Sum.inr τ.b) = false := by
    simp only [hp'_def, decide_eq_false_iff_not]
    exact (τ.residual_ne_tri S q).symm
  have h4 : p' (Sum.inr τ.a) = p (Sum.inl τ.att) := by rw [← toMark'_att]; exact hp _
  refine (hrot.filter p').trans ?_
  rw [hL, List.filter_append, List.filter_append, hmap L₁ hL₁, List.filter_cons, List.filter_cons,
    List.filter_cons, List.filter_cons, hmap L₂ hL₂, List.filter_cons, h1, h2, h3, h4,
    List.map_append]
  simp only [Bool.false_eq_true, ite_false]
  by_cases hatt : p (Sum.inl τ.att) = true
  · rw [ite_eq_left hatt, ite_eq_left hatt, List.map_cons, toMark'_att]
  · rw [ite_eq_right hatt, ite_eq_right hatt]

theorem ccpCornerList_residual (S : Finset (Crossing P)) (q : Component hn hP S) :
    (ccpCornerList (by omega) hQ (τ.supportY S) (τ.residual S q)).IsRotated
      ((ccpCornerList hn hP S q).map τ.toMark') := by
  unfold ccpCornerList
  exact Carrier.MarkTransport.isRotated_filter_map_of_forall τ.toMark'
    (τ.componentMarkList_residual S q) _ _
    (fun m => decide_eq_decide.mpr (τ.isTrueCorner_toMark' S m))

theorem ccpCornerCount_residual (S : Finset (Crossing P)) (q : Component hn hP S) :
    ccpCornerCount (by omega) hQ (τ.supportY S) (τ.residual S q) = ccpCornerCount hn hP S q := by
  unfold ccpCornerCount
  rw [(τ.ccpCornerList_residual S q).perm.length_eq, List.length_map]

theorem mem_ccpCornerList_residual (S : Finset (Crossing P)) (q : Component hn hP S) (m' : Mark Q) :
    m' ∈ ccpCornerList (by omega) hQ (τ.supportY S) (τ.residual S q) ↔
      ∃ m ∈ ccpCornerList hn hP S q, τ.toMark' m = m' := by
  rw [(τ.ccpCornerList_residual S q).mem_iff, List.mem_map]

/-- The component mark list of the triangle is `μ_att, M_ε, b` up to rotation. -/
theorem componentMarkList_tri (S : Finset (Crossing P)) :
    (componentMarkList (by omega) hQ (τ.supportY S) (τ.tri S)).IsRotated
      [Sum.inl (τ.vert τ.att), Sum.inl τ.new, Sum.inr τ.b] := by
  unfold componentMarkList
  obtain ⟨L₁, L₂, hL, hrot⟩ := τ.markList_insertion'
  obtain ⟨hL₁, hL₂⟩ := τ.notMem_att_of_insertion hL
  set p' : Mark Q → Bool :=
    fun m' => decide (owner (by omega) hQ (τ.supportY S) m' = τ.tri S) with hp'_def
  have hmap : ∀ (L : List (Mark P)), (∀ m ∈ L, m ≠ Sum.inl τ.att) →
      (L.map τ.toMark).filter p' = [] := by
    intro L hLne
    rw [List.filter_eq_nil_iff]
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hm'
    simp only [hp'_def, decide_eq_true_eq]
    rw [← τ.toMark'_of_ne m (hLne m hm)]
    exact τ.owner_toMark'_ne_tri S m
  have ha : p' (Sum.inr τ.a) = false := by
    simp only [hp'_def, decide_eq_false_iff_not]
    rw [← toMark'_att]; exact τ.owner_toMark'_ne_tri S _
  have h1 : p' (τ.toMark (Sum.inl τ.att)) = true := by
    simp only [hp'_def, toMark_inl, τ.owner_vatt_eq_tri, decide_eq_true_eq]
  have h2 : p' (Sum.inl τ.new) = true := by
    simp only [hp'_def, τ.owner_new_eq_tri, decide_eq_true_eq]
  have h3 : p' (Sum.inr τ.b) = true := by
    simp only [hp'_def, tri, decide_eq_true_eq]
  refine (hrot.filter p').trans ?_
  rw [List.filter_append, hmap L₁ hL₁, List.filter_cons, List.filter_cons, List.filter_cons,
    List.filter_cons, hmap L₂ hL₂, ha, h1, h2, h3, toMark_inl]
  simp only [Bool.false_eq_true, ite_false, ite_true, List.nil_append]
  exact List.IsRotated.refl _

theorem ccpCornerList_tri (S : Finset (Crossing P)) :
    (ccpCornerList (by omega) hQ (τ.supportY S) (τ.tri S)).IsRotated
      [Sum.inl (τ.vert τ.att), Sum.inl τ.new, Sum.inr τ.b] := by
  unfold ccpCornerList
  refine ((τ.componentMarkList_tri S).filter _).trans ?_
  have h : [Sum.inl (τ.vert τ.att), Sum.inl τ.new, Sum.inr τ.b].filter
      (fun m => decide (IsTrueCorner (τ.supportY S) m)) =
      [Sum.inl (τ.vert τ.att), Sum.inl τ.new, Sum.inr τ.b] := by
    rw [List.filter_eq_self]
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact decide_eq_true trivial
    · exact decide_eq_true trivial
    · exact decide_eq_true (show IsTrueCorner (τ.supportY S) (Sum.inr τ.b) from by
        rw [isTrueCorner_visit, τ.b_fst]; exact τ.y_mem_supportY S)
  rw [h]

theorem ccpCornerCount_tri (S : Finset (Crossing P)) :
    ccpCornerCount (by omega) hQ (τ.supportY S) (τ.tri S) = 3 := by
  unfold ccpCornerCount
  rw [(τ.ccpCornerList_tri S).perm.length_eq]
  rfl

theorem mem_ccpCornerList_tri (S : Finset (Crossing P)) (m' : Mark Q) :
    m' ∈ ccpCornerList (by omega) hQ (τ.supportY S) (τ.tri S) ↔
      m' = Sum.inl (τ.vert τ.att) ∨ m' = Sum.inl τ.new ∨ m' = Sum.inr τ.b := by
  rw [(τ.ccpCornerList_tri S).mem_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

/-! ### Uniformity -/

/-- Uniformity of a residual carrier is that of its parent when every residual mark keeps its
turn (the smoothing corner `y` has the turn of the vertex `μ_att` it replaces). -/
theorem carrierUniform_residual_iff (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (hturn : ∀ m, markTurn Q (τ.toMark' m) = markTurn P m) :
    CarrierUniform (by omega) hQ (τ.supportY S) (τ.residual S q) ↔ CarrierUniform hn hP S q := by
  rw [sfta_carrierUniform_iff_forall_mem _ hQ ((τ.isDecomposition_supportY_iff S).mpr hS),
    sfta_carrierUniform_iff_forall_mem hn hP hS q]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  constructor
  · intro h m hm
    rw [← hturn m]
    exact h _ ((τ.mem_ccpCornerList_residual S q _).mpr ⟨m, hm, rfl⟩)
  · rintro h m' hm'
    obtain ⟨m, hm, rfl⟩ := (τ.mem_ccpCornerList_residual S q m').mp hm'
    rw [hturn m]
    exact h m hm

/-- The triangle is uniform when its three corners turn alike. -/
theorem carrierUniform_tri (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (σ : SignType) (hσ : σ ≠ 0) (h1 : turn Q (τ.vert τ.att) = σ) (h2 : turn Q τ.new = σ)
    (h3 : markTurn Q (Sum.inr τ.b) = σ) :
    CarrierUniform (by omega) hQ (τ.supportY S) (τ.tri S) := by
  rw [sfta_carrierUniform_iff_forall_mem _ hQ ((τ.isDecomposition_supportY_iff S).mpr hS)]
  refine ⟨σ, hσ, fun m hm => ?_⟩
  rcases (τ.mem_ccpCornerList_tri S m).mp hm with rfl | rfl | rfl
  · rw [markTurn_inl]; exact h1
  · rw [markTurn_inl]; exact h2
  · exact h3

theorem uniformDecomposition_supportY_iff (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (hturn : ∀ m, markTurn Q (τ.toMark' m) = markTurn P m)
    (htri : CarrierUniform (by omega) hQ (τ.supportY S) (τ.tri S)) :
    UniformDecomposition (by omega) hQ (τ.supportY S) ↔ UniformDecomposition hn hP S := by
  unfold UniformDecomposition
  constructor
  · intro h q
    exact (τ.carrierUniform_residual_iff S hS q hturn).mp (h _)
  · intro h q'
    rcases τ.component_cases S q' with rfl | ⟨q, rfl⟩
    · exact htri
    · exact (τ.carrierUniform_residual_iff S hS q hturn).mpr (h q)

theorem mem_uniformDecompositions_supportY_iff
    (hturn : ∀ m, markTurn Q (τ.toMark' m) = markTurn P m)
    (htri : ∀ S : Finset (Crossing P), IsDecomposition hn hP S →
      CarrierUniform (by omega) hQ (τ.supportY S) (τ.tri S))
    (S : Finset (Crossing P)) :
    τ.supportY S ∈ uniformDecompositions (by omega) hQ ↔ S ∈ uniformDecompositions hn hP := by
  rw [mem_uniformDecompositions, mem_uniformDecompositions]
  have hd : τ.supportY S ∈ independentSupports (by omega) hQ ↔ S ∈ independentSupports hn hP :=
    τ.isDecomposition_supportY_iff S
  by_cases hS : IsDecomposition hn hP S
  · exact and_congr hd (τ.uniformDecomposition_supportY_iff S hS hturn (htri S hS))
  · constructor
    · rintro ⟨h, _⟩
      exact absurd (hd.mp h) hS
    · rintro ⟨h, _⟩
      exact absurd h hS

/-! ### The supports omitting `y`: lem:corner-values (ii) kills their terms -/

/-- (HERE row 105 (ii), hence the floor, enters.) For a uniform decomposition of `Q` omitting `y`,
the carrier through the newborn (both visits `a`, `b` lie on it) has `y` as a crossing interlacing
no other of its crossings, so its coefficient vanishes and so does the product
(sm-4:1076-1084). -/
theorem cornerProduct_support_eq_zero (hCV : CornerValuesData) (S : Finset (Crossing P))
    (hS' : IsDecomposition (by omega) hQ (τ.support S))
    (huni : UniformDecomposition (by omega) hQ (τ.support S)) :
    cornerProduct (by omega) hQ (τ.support S) hS' = 0 := by
  set q' := owner (by omega) hQ (τ.support S) (Sum.inr τ.a) with hq'
  have hy : τ.y ∈ carrierCrossings (by omega) hQ (τ.support S) q' := by
    rw [mem_carrierCrossings]
    refine ⟨τ.y_notMem_support S, fun w hw => ?_⟩
    rcases (τ.visit_fst_eq_y_iff w).mp hw with rfl | rfl
    · rfl
    · exact (τ.owner_support_a_eq_b S).symm
  have hiso : ∀ y' ∈ carrierCrossings (by omega) hQ (τ.support S) q', y' ≠ τ.y →
      ¬ Interlaces (by omega) hQ τ.y y' := by
    intro y' _ hne
    obtain ⟨x, rfl⟩ := τ.cross_range y' hne
    exact τ.y_isolated x
  have hc := hCV.isolated_zero (n + 1) (by omega) Q hQ (τ.support S) hS' q' (huni q') τ.y hy hiso
  unfold cornerProduct
  exact Finset.prod_eq_zero (Finset.mem_univ q') hc

/-! ### The corner coefficients and the product at `S ∪ {y}` -/

theorem cornerSlot_residual (S : Finset (Crossing P)) (q : Component hn hP S)
    (hrot : carrierRotation (by omega) hQ (τ.supportY S) (τ.residual S q) =
      carrierRotation hn hP S q) :
    cornerSlot (by omega) hQ (τ.supportY S) (τ.residual S q) = cornerSlot hn hP S q := by
  unfold cornerSlot carrierRotationInt
  rw [τ.carrierCrossingCount_residual S q, hrot]

theorem cornerCoefficient_residual (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hrot : carrierRotation (by omega) hQ (τ.supportY S) (τ.residual S q) =
      carrierRotation hn hP S q)
    (hH : homfly (positiveLift (by omega) hQ (τ.supportY S) (τ.residual S q)
        ((τ.isDecomposition_supportY_iff S).mpr hS)) = homfly (positiveLift hn hP S q hS)) :
    cornerCoefficient (by omega) hQ (τ.supportY S) (τ.residual S q)
        ((τ.isDecomposition_supportY_iff S).mpr hS) = cornerCoefficient hn hP S q hS := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt]
  unfold cornerHomfly
  rw [τ.cornerSlot_residual S q hrot, hH]

/-- lem:corner-values (i) on the triangle: a crossing-free uniform carrier has coefficient `1`
(sm-4:1097-1100). -/
theorem cornerCoefficient_tri (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (htri : CarrierUniform (by omega) hQ (τ.supportY S) (τ.tri S)) :
    cornerCoefficient (by omega) hQ (τ.supportY S) (τ.tri S)
      ((τ.isDecomposition_supportY_iff S).mpr hS) = 1 :=
  (corner_values_i (by omega) hQ ((τ.isDecomposition_supportY_iff S).mpr hS) (τ.tri S) htri
    (τ.carrierCrossingCount_tri S)).2.2

/-- "Every surviving term gains exactly one selected crossing and one triangle coefficient `1`". -/
theorem cornerProduct_supportY (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (htri : CarrierUniform (by omega) hQ (τ.supportY S) (τ.tri S))
    (hcoef : ∀ q : Component hn hP S,
      cornerCoefficient (by omega) hQ (τ.supportY S) (τ.residual S q)
        ((τ.isDecomposition_supportY_iff S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerProduct (by omega) hQ (τ.supportY S) ((τ.isDecomposition_supportY_iff S).mpr hS) =
      cornerProduct hn hP S hS := by
  unfold cornerProduct
  rw [← Fintype.prod_equiv (τ.componentEquiv S)
    (fun o => cornerCoefficient (by omega) hQ (τ.supportY S) (τ.componentEquiv S o)
      ((τ.isDecomposition_supportY_iff S).mpr hS)) _ (fun _ => rfl),
    Fintype.prod_option, componentEquiv_none, τ.cornerCoefficient_tri S hS htri, one_mul]
  exact Fintype.prod_congr _ _ (fun q => by rw [componentEquiv_some]; exact hcoef q)

/-! ### The signed sum -/

/-- **The signed sum over the uniform decompositions of `Q` is minus that of `P`**: the supports
omitting `y` contribute `0` (`cornerProduct_support_eq_zero`), the supports containing `y` are the
`S ∪ {y}` with `(−1)^{|S|+1}` and the parent's product (sm-4:1130-1136). -/
theorem sum_transport (hCV : CornerValuesData)
    (hturn : ∀ m, markTurn Q (τ.toMark' m) = markTurn P m)
    (htri : ∀ S : Finset (Crossing P), IsDecomposition hn hP S →
      CarrierUniform (by omega) hQ (τ.supportY S) (τ.tri S))
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient (by omega) hQ (τ.supportY S) (τ.residual S q)
        ((τ.isDecomposition_supportY_iff S).mpr hS) = cornerCoefficient hn hP S q hS) :
    (∑ S ∈ (uniformDecompositions (by omega) hQ).attach,
      (-1) ^ S.1.card *
        cornerProduct (by omega) hQ S.1 (isDecomposition_of_mem_uniformDecompositions _ hQ S.2)) =
    -∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2) := by
  set g : Finset (Crossing P) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions hn hP then
      (-1) ^ S.card * cornerProduct hn hP S (isDecomposition_of_mem_uniformDecompositions hn hP h)
    else 0 with hg
  set g' : Finset (Crossing Q) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions (by omega) hQ then
      (-1) ^ S.card * cornerProduct (by omega) hQ S (isDecomposition_of_mem_uniformDecompositions _ hQ h)
    else 0 with hg'
  have h1 : (∑ S ∈ (uniformDecompositions (by omega) hQ).attach,
      (-1) ^ S.1.card *
        cornerProduct (by omega) hQ S.1 (isDecomposition_of_mem_uniformDecompositions _ hQ S.2)) =
      ∑ S ∈ (uniformDecompositions (by omega) hQ).attach, g' S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg']
    rw [dite_eq_left S.2]
  have h2 : (∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2)) =
      ∑ S ∈ (uniformDecompositions hn hP).attach, g S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg]
    rw [dite_eq_left S.2]
  rw [h1, h2, Finset.sum_attach, Finset.sum_attach,
    ← Finset.sum_filter_add_sum_filter_not (uniformDecompositions (by omega) hQ)
      (fun S' => τ.y ∈ S')]
  -- the supports omitting `y` contribute nothing
  have hzero : ∑ S' ∈ (uniformDecompositions (by omega) hQ).filter (fun S' => ¬ τ.y ∈ S'),
      g' S' = 0 := by
    apply Finset.sum_eq_zero
    intro S' hS'
    rw [Finset.mem_filter] at hS'
    obtain ⟨S, rfl⟩ := τ.support_surjective_of_notMem S' hS'.2
    simp only [hg']
    rw [dite_eq_left hS'.1, τ.cornerProduct_support_eq_zero hCV S _
      (uniform_of_mem_uniformDecompositions _ hQ hS'.1), mul_zero]
  -- the supports containing `y` are the `S ∪ {y}`
  have hin : ∑ S' ∈ (uniformDecompositions (by omega) hQ).filter (fun S' => τ.y ∈ S'), g' S' =
      ∑ S ∈ uniformDecompositions hn hP, -(g S) := by
    symm
    refine Finset.sum_nbij τ.supportY ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_filter]
      exact ⟨(τ.mem_uniformDecompositions_supportY_iff hturn htri S).mpr hS, τ.y_mem_supportY S⟩
    · intro S _ T _ h
      exact τ.supportY_injective h
    · intro S' hS'
      rw [Finset.mem_coe, Finset.mem_filter] at hS'
      obtain ⟨S, rfl⟩ := τ.supportY_surjective_of_mem S' hS'.2
      exact ⟨S, (τ.mem_uniformDecompositions_supportY_iff hturn htri S).mp hS'.1, rfl⟩
    · intro S hS
      have hS' : IsDecomposition hn hP S := isDecomposition_of_mem_uniformDecompositions hn hP hS
      have hSQ : τ.supportY S ∈ uniformDecompositions (by omega) hQ :=
        (τ.mem_uniformDecompositions_supportY_iff hturn htri S).mpr hS
      simp only [hg, hg']
      rw [dite_eq_left hS, dite_eq_left hSQ, τ.supportY_card, pow_succ,
        τ.cornerProduct_supportY S hS' (htri S hS') (hcoef S hS')]
      ring
  rw [hzero, add_zero, hin, Finset.sum_neg_distrib]

/-! ### The left-turn count -/

/-- `ℓ(Q) + [τ_att(P) = 1] = ℓ(P) + [τ_{vert att}(Q) = 1] + [τ_new(Q) = 1]` when every other vertex
keeps its turn (additive form, as `sfta_InsertMarkTransport.leftTurns_transport`). -/
theorem leftTurns_transport (hturn : ∀ i, i ≠ τ.att → turn Q (τ.vert i) = turn P i) :
    leftTurns Q + (if turn P τ.att = 1 then 1 else 0) =
      leftTurns P + (if turn Q (τ.vert τ.att) = 1 then 1 else 0) +
        (if turn Q τ.new = 1 then 1 else 0) := by
  unfold leftTurns
  rw [Finset.card_filter, Finset.card_filter]
  have huniv : (Finset.univ : Finset (ZMod (n + 1))) = insert τ.new (Finset.univ.image τ.vert) := by
    ext a
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_image, true_and]
    rcases τ.vert_exhaust a with h | ⟨i, hi⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi⟩
  have hnot : τ.new ∉ Finset.univ.image τ.vert := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun i => τ.vert_ne_new i
  rw [huniv, Finset.sum_insert hnot, Finset.sum_image (fun i _ k _ h => τ.vert_injective h),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ τ.att),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ τ.att)]
  have hrest : ∑ x ∈ Finset.univ.erase τ.att, (if turn Q (τ.vert x) = 1 then 1 else 0) =
      ∑ x ∈ Finset.univ.erase τ.att, (if turn P x = 1 then 1 else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hturn x (Finset.ne_of_mem_erase hx)]
  rw [hrest]
  ring

/-- **The corner state sum in the loop sector, abstractly**: `C(Q) = −(−1)^{ℓ(Q)+ℓ(P)} C(P)`. -/
theorem cornerStateSum_transport (hCV : CornerValuesData)
    (hturn : ∀ m, markTurn Q (τ.toMark' m) = markTurn P m)
    (htri : ∀ S : Finset (Crossing P), IsDecomposition hn hP S →
      CarrierUniform (by omega) hQ (τ.supportY S) (τ.tri S))
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient (by omega) hQ (τ.supportY S) (τ.residual S q)
        ((τ.isDecomposition_supportY_iff S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerStateSum (by omega) hQ = -((-1) ^ (leftTurns Q + leftTurns P) * cornerStateSum hn hP) := by
  unfold cornerStateSum
  rw [τ.sum_transport hCV hturn htri hcoef, mul_neg,
    sfta_InsertMarkTransport.sfta_sign_cancel (leftTurns Q) (leftTurns P)]

end sftd_LoopTransport

end SftdLoopCarriers

section SftdInterlacesTransport

/-- Interlacement is carried by compatible INJECTIVE crossing/visit maps (not necessarily onto)
preserving the cyclic order of the visit positions, provided every visit of a crossing in the
range is in the range (the loop sector: everything but the newborn). -/
theorem sftd_interlaces_transport {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m) {P : LabelledTuple n}
    {Q : LabelledTuple m} (hP : Generic P) (hQ : Generic Q)
    (cross : Crossing P → Crossing Q) (hcross : Function.Injective cross)
    (visit : Visit P → Visit Q) (hvisit : Function.Injective visit)
    (hfst : ∀ v, (visit v).1 = cross v.1)
    (hrange : ∀ (w : Visit Q) (x : Crossing P), w.1 = cross x → ∃ v, visit v = w)
    (hbtw : ∀ u v w : Visit P,
      traversalBetween (visitPosition hm hQ.1 (visit u)) (visitPosition hm hQ.1 (visit v))
        (visitPosition hm hQ.1 (visit w)) ↔
      traversalBetween (visitPosition hn hP.1 u) (visitPosition hn hP.1 v) (visitPosition hn hP.1 w))
    (x y : Crossing P) :
    Interlaces hm hQ (cross x) (cross y) ↔ Interlaces hn hP x y := by
  rw [sfta_interlaces_iff_visits hm hQ, sfta_interlaces_iff_visits hn hP]
  refine and_congr hcross.ne_iff ?_
  constructor
  · rintro ⟨u₀, u₁, v₀, v₁, h₀, h₁, h₂, h₃, hu, hv, hb₀, hb₁⟩
    obtain ⟨u₀, rfl⟩ := hrange u₀ x h₀
    obtain ⟨u₁, rfl⟩ := hrange u₁ x h₁
    obtain ⟨v₀, rfl⟩ := hrange v₀ y h₂
    obtain ⟨v₁, rfl⟩ := hrange v₁ y h₃
    rw [hfst] at h₀ h₁ h₂ h₃
    exact ⟨u₀, u₁, v₀, v₁, hcross h₀, hcross h₁, hcross h₂, hcross h₃,
      fun h => hu (by rw [h]), fun h => hv (by rw [h]), (hbtw _ _ _).mp hb₀, (hbtw _ _ _).mp hb₁⟩
  · rintro ⟨u₀, u₁, v₀, v₁, h₀, h₁, h₂, h₃, hu, hv, hb₀, hb₁⟩
    refine ⟨visit u₀, visit u₁, visit v₀, visit v₁, ?_, ?_, ?_, ?_, hvisit.ne hu, hvisit.ne hv,
      (hbtw _ _ _).mpr hb₀, (hbtw _ _ _).mpr hb₁⟩
    · rw [hfst, h₀]
    · rw [hfst, h₁]
    · rw [hfst, h₂]
    · rw [hfst, h₃]

end SftdInterlacesTransport

section SftdSoftInstance

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n} {q : Plane} {ε : ℝ}
  (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
  (hclass : SoftCrossingClassificationAt P j q ε)
  (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)

include hn in
/-- Every mark of `P_ε` in the loop sector is `a`, `M_ε`, `b` or a transported mark. -/
theorem sftd_soft_mark_exhaust (m : Mark (softInsertion P j q ε)) :
    m = Sum.inr (softNewbornIncomingVisit hclass hloop) ∨ m = Sum.inl (softNewIndex j) ∨
    m = Sum.inr (softNewbornReturnVisit hclass hloop) ∨
    ∃ m₀ : Mark P, sfta_softMap hp m₀ = m := by
  cases m with
  | inl k =>
    rcases soft_indices_exhaust j k with h | ⟨i, hi⟩
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inr ⟨Sum.inl i, by rw [hi]; rfl⟩))
  | inr w =>
    by_cases hw : w.1 = softNewbornCrossing hclass hloop
    · rcases softNewbornVisits_exhaust hclass hloop w hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    · obtain ⟨v, hv⟩ := (softInheritedVisit_range_loop hn hp hclass hloop w).mpr hw
      exact Or.inr (Or.inr (Or.inr ⟨Sum.inr v, by rw [← hv]; rfl⟩))

include hn in
theorem sftd_softMap_ne_a (m : Mark P) :
    sfta_softMap hp m ≠ Sum.inr (softNewbornIncomingVisit hclass hloop) := by
  cases m with
  | inl i => exact Sum.inl_ne_inr
  | inr v =>
    intro h
    have h1 : (softInheritedVisit hp v).1 = softNewbornCrossing hclass hloop :=
      congrArg Sigma.fst (Sum.inr_injective h)
    exact (softInheritedCrossing_range_loop hn hp hclass hloop _).mp ⟨v.1, rfl⟩ h1

include hn in
theorem sftd_softMap_ne_b (m : Mark P) :
    sfta_softMap hp m ≠ Sum.inr (softNewbornReturnVisit hclass hloop) := by
  cases m with
  | inl i => exact Sum.inl_ne_inr
  | inr v =>
    intro h
    have h1 : (softInheritedVisit hp v).1 = softNewbornCrossing hclass hloop :=
      congrArg Sigma.fst (Sum.inr_injective h)
    exact (softInheritedCrossing_range_loop hn hp hclass hloop _).mp ⟨v.1, rfl⟩ h1

/-! #### Traversal keys of the newborn visits -/

include hn hP hQ in
theorem sftd_soft_key_a :
    markKey (by omega) hQ.1 (Sum.inr (softNewbornIncomingVisit hclass hloop)) =
      ((canonicalPosition j).val : ℝ) + visitParameter (softNewbornIncomingVisit hclass hloop) := by
  rw [sfta_markKey_visit_eq, softNewbornIncomingVisit_edge, (soft_vertex_arc_label_values hn j).1]

include hn hP hQ in
theorem sftd_soft_key_b :
    markKey (by omega) hQ.1 (Sum.inr (softNewbornReturnVisit hclass hloop)) =
      ((softNewIndex j).val : ℝ) + visitParameter (softNewbornReturnVisit hclass hloop) := by
  rw [sfta_markKey_visit_eq, softNewbornReturnVisit_edge]

include hn hP hQ in
/-- `j ≠ 0`: every transported mark below the attachment vertex lies below `a`. -/
theorem sftd_key_lt_a_of_ne_zero (hj : j ≠ 0)
    (hbound : ∀ v : Visit P, v.2.val = j - 1 →
      visitParameter (softInheritedVisit hp v) <
        visitParameter (softNewbornIncomingVisit hclass hloop))
    (w : Mark P) (hw : markKey hn hP.1 w < markKey hn hP.1 (Sum.inl j)) :
    markKey (by omega) hQ.1 (sfta_softMap hp w) <
      markKey (by omega) hQ.1 (Sum.inr (softNewbornIncomingVisit hclass hloop)) := by
  rw [sftd_soft_key_a hn hP hQ hclass hloop, canonicalPosition_val_nonzero j hj]
  have hta := (visitPosition_interior (by omega) hQ.1 (softNewbornIncomingVisit hclass hloop)).1
  have hjpos := ZMod.val_pos.mpr hj
  have hcast : ((j.val - 1 : ℕ) : ℝ) + 1 = (j.val : ℝ) := by
    have : ((j.val - 1 : ℕ) : ℝ) = (j.val : ℝ) - 1 := by
      rw [Nat.cast_sub hjpos, Nat.cast_one]
    rw [this]; ring
  rw [sfta_markKey_vertex_eq] at hw
  cases w with
  | inl k =>
    simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, Nat.cast_lt] at hw ⊢
    rw [sfta_softOldIndex_val_of_ne_zero j k hj, ite_eq_left hw.le]
    have : (k.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hw
    linarith
  | inr v =>
    simp only [sfta_softMap, Sum.map_inr, sfta_markKey_visit_eq, softInheritedVisit_edge] at hw ⊢
    have htv := visitPosition_interior hn hP.1 v
    have htv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
    have he : v.2.val.val < j.val := by
      by_contra hc
      push_neg at hc
      have : (j.val : ℝ) ≤ v.2.val.val := by exact_mod_cast hc
      linarith
    rw [sfta_softParentEdge_val_of_ne_zero j _ hj, ite_eq_left he]
    rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt he) with hlt | heq
    · have : (v.2.val.val : ℝ) + 1 ≤ ((j.val - 1 : ℕ) : ℝ) := by exact_mod_cast hlt
      linarith
    · have hv : v.2.val = j - 1 := by
        apply ZMod.val_injective
        rw [heq]
        exact (canonicalPosition_val_nonzero j hj).symm
      have hlt := hbound v hv
      have : (v.2.val.val : ℝ) = ((j.val - 1 : ℕ) : ℝ) := by exact_mod_cast heq
      linarith

include hn hP hQ in
/-- `j ≠ 0`: every transported mark above the attachment vertex lies above `b`. -/
theorem sftd_key_b_lt_of_ne_zero (hj : j ≠ 0)
    (hbound : ∀ v : Visit P, v.2.val = j →
      visitParameter (softNewbornReturnVisit hclass hloop) <
        visitParameter (softInheritedVisit hp v))
    (w : Mark P) (hw : markKey hn hP.1 (Sum.inl j) < markKey hn hP.1 w) :
    markKey (by omega) hQ.1 (Sum.inr (softNewbornReturnVisit hclass hloop)) <
      markKey (by omega) hQ.1 (sfta_softMap hp w) := by
  rw [sftd_soft_key_b hn hP hQ hclass hloop, sfta_softNewIndex_val_of_ne_zero j hj]
  have htb := visitPosition_interior (by omega) hQ.1 (softNewbornReturnVisit hclass hloop)
  rw [sfta_markKey_vertex_eq] at hw
  push_cast
  cases w with
  | inl k =>
    simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, Nat.cast_lt] at hw ⊢
    rw [sfta_softOldIndex_val_of_ne_zero j k hj, ite_eq_right (not_le.mpr hw)]
    have : (j.val : ℝ) + 1 ≤ (k.val : ℝ) := by exact_mod_cast hw
    push_cast
    linarith
  | inr v =>
    simp only [sfta_softMap, Sum.map_inr, sfta_markKey_visit_eq, softInheritedVisit_edge] at hw ⊢
    have htv := visitPosition_interior hn hP.1 v
    have htv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
    have he : j.val ≤ v.2.val.val := by
      by_contra hc
      push_neg at hc
      have : (v.2.val.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hc
      linarith
    rw [sfta_softParentEdge_val_of_ne_zero j _ hj, ite_eq_right (not_lt.mpr he)]
    push_cast
    rcases lt_or_eq_of_le he with hlt | heq
    · have : (j.val : ℝ) + 1 ≤ (v.2.val.val : ℝ) := by exact_mod_cast hlt
      linarith
    · have hv : v.2.val = j := ZMod.val_injective n heq.symm
      have hlt := hbound v hv
      have : (v.2.val.val : ℝ) = (j.val : ℝ) := by exact_mod_cast heq.symm
      linarith

include hn hP hQ in
/-- `j ≠ 0`: the block `a < μ_j < M_ε < b` in the keys. -/
theorem sftd_key_block_of_ne_zero (hj : j ≠ 0) :
    markKey (by omega) hQ.1 (Sum.inr (softNewbornIncomingVisit hclass hloop)) <
      markKey (by omega) hQ.1 (sfta_softMap hp (Sum.inl j)) ∧
    markKey (by omega) hQ.1 (sfta_softMap hp (Sum.inl j)) <
      markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) ∧
    markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) <
      markKey (by omega) hQ.1 (Sum.inr (softNewbornReturnVisit hclass hloop)) := by
  obtain ⟨hknew, hkatt⟩ := sfta_soft_new_key hn hP hQ hp hj
  have hta := visitPosition_interior (by omega) hQ.1 (softNewbornIncomingVisit hclass hloop)
  have htb := visitPosition_interior (by omega) hQ.1 (softNewbornReturnVisit hclass hloop)
  have hjpos := ZMod.val_pos.mpr hj
  have hcast : ((j.val - 1 : ℕ) : ℝ) + 1 = (j.val : ℝ) := by
    have : ((j.val - 1 : ℕ) : ℝ) = (j.val : ℝ) - 1 := by
      rw [Nat.cast_sub hjpos, Nat.cast_one]
    rw [this]; ring
  rw [sftd_soft_key_a hn hP hQ hclass hloop, canonicalPosition_val_nonzero j hj,
    sftd_soft_key_b hn hP hQ hclass hloop, sfta_softNewIndex_val_of_ne_zero j hj, hknew, hkatt]
  push_cast
  refine ⟨by linarith, by linarith, by linarith⟩

include hn hP hQ in
/-- `j = 0`: `M_ε` is the label `0`, `b` follows, every transported mark other than `μ_0` lies
above `b` and below `a`, and `μ_0` (label `n`) comes last. -/
theorem sftd_keys_zero (hj : j = 0)
    (hbound : ∀ v : Visit P,
      (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
        visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
      (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
        visitParameter (softInheritedVisit hp v))) :
    markKey (by omega) hQ.1 (Sum.inl (softNewIndex j)) <
      markKey (by omega) hQ.1 (Sum.inr (softNewbornReturnVisit hclass hloop)) ∧
    (∀ w : Mark P, w ≠ Sum.inl j →
      markKey (by omega) hQ.1 (Sum.inr (softNewbornReturnVisit hclass hloop)) <
        markKey (by omega) hQ.1 (sfta_softMap hp w)) ∧
    (∀ w : Mark P, w ≠ Sum.inl j →
      markKey (by omega) hQ.1 (sfta_softMap hp w) <
        markKey (by omega) hQ.1 (Sum.inr (softNewbornIncomingVisit hclass hloop))) ∧
    markKey (by omega) hQ.1 (Sum.inr (softNewbornIncomingVisit hclass hloop)) <
      markKey (by omega) hQ.1 (sfta_softMap hp (Sum.inl j)) ∧
    markKey (by omega) hQ.1 (Sum.inr (softNewbornReturnVisit hclass hloop)) <
      markKey (by omega) hQ.1 (Sum.inr (softNewbornIncomingVisit hclass hloop)) := by
  subst hj
  obtain ⟨hk0, hkn, -⟩ := sfta_soft_zero_keys hn hP hQ hp rfl
  have hta := visitPosition_interior (by omega) hQ.1 (softNewbornIncomingVisit hclass hloop)
  have htb := visitPosition_interior (by omega) hQ.1 (softNewbornReturnVisit hclass hloop)
  have hka := sftd_soft_key_a hn hP hQ hclass hloop
  have hkb := sftd_soft_key_b hn hP hQ hclass hloop
  rw [canonicalPosition_val_zero] at hka
  rw [sfta_softNewIndex_zero, ZMod.val_zero, Nat.cast_zero, zero_add] at hkb
  have hn1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have hpos := NeZero.pos n
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hpos, Nat.cast_one]
    rw [this]; ring
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, fun w hw => ?_, fun w hw => ?_, ?_, ?_⟩
  · rw [hk0, hkb]; exact htb.1
  · rw [hkb]
    cases w with
    | inl k =>
      have hk : k ≠ 0 := fun h => hw (by rw [h])
      simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, sfta_softOldIndex_zero_val,
        ite_eq_right hk]
      have : (1 : ℝ) ≤ k.val := by exact_mod_cast ZMod.val_pos.mpr hk
      linarith
    | inr v =>
      simp only [sfta_softMap, Sum.map_inr, sfta_markKey_visit_eq, softInheritedVisit_edge,
        sfta_softParentEdge_zero_val]
      have htv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
      by_cases he : v.2.val = 0
      · have hlt := (hbound v).2 he
        rw [he, ZMod.val_zero, Nat.cast_zero, zero_add]
        exact hlt
      · have : (1 : ℝ) ≤ v.2.val.val := by exact_mod_cast ZMod.val_pos.mpr he
        linarith
  · rw [hka]
    cases w with
    | inl k =>
      have hk : k ≠ 0 := fun h => hw (by rw [h])
      simp only [sfta_softMap, Sum.map_inl, sfta_markKey_vertex_eq, sfta_softOldIndex_zero_val,
        ite_eq_right hk]
      have : k.val ≤ n - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt k)
      have : (k.val : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    | inr v =>
      simp only [sfta_softMap, Sum.map_inr, sfta_markKey_visit_eq, softInheritedVisit_edge,
        sfta_softParentEdge_zero_val]
      have htv' := visitPosition_interior (by omega) hQ.1 (softInheritedVisit hp v)
      have hle : v.2.val.val ≤ n - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt _)
      rcases lt_or_eq_of_le hle with hlt | heq
      · have : (v.2.val.val : ℝ) + 1 ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hlt
        linarith
      · have hv : v.2.val = (0 : ZMod n) - 1 := by
          apply ZMod.val_injective
          rw [heq]
          exact canonicalPosition_val_zero.symm
        have hlt := (hbound v).1 hv
        have : (v.2.val.val : ℝ) = ((n - 1 : ℕ) : ℝ) := by exact_mod_cast heq
        linarith
  · rw [hka, hkn]
    linarith
  · rw [hka, hkb]
    linarith

include hn hP hQ in
/-- **The sorted mark list of the soft insertion in the loop sector** is the parent list with the
attachment vertex `μ_j` replaced by the block `a, μ_j, M_ε, b`, up to rotation (literally when
`j ≠ 0`; when `j = 0` the new vertex `M_ε` is the label `0`, the cut moves by two). -/
theorem sftd_soft_markList_insertion
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
    (hbound : ∀ v : Visit P,
      (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
        visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
      (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
        visitParameter (softInheritedVisit hp v))) :
    sftd_IsLoopInsertion (sfta_softMap hp) (Sum.inl j)
      (Sum.inr (softNewbornIncomingVisit hclass hloop)) (Sum.inl (softNewIndex j))
      (Sum.inr (softNewbornReturnVisit hclass hloop)) (markList hn hP) (markList (by omega) hQ) := by
  have hinj := sfta_softMap_injective hp
  have hnew := sfta_softMap_new_notMem hn hP hp
  have hndP := markList_nodup hn hP
  have hndQ := markList_nodup (by omega : 3 ≤ n + 1) hQ
  have hsP := markList_sorted hn hP
  have hsQ := markList_sorted (by omega : 3 ≤ n + 1) hQ
  have hkey := sfta_soft_markKey_le_iff hn hP hQ hp hord
  have hkeylt := sfta_soft_markKey_lt_iff hn hP hQ hp hord
  set a := softNewbornIncomingVisit hclass hloop with ha_def
  set b := softNewbornReturnVisit hclass hloop with hb_def
  set f := sfta_softMap hp with hf_def
  have hna : Sum.inr a ∉ (markList hn hP).map f := by
    intro h
    obtain ⟨m, _, hm⟩ := List.mem_map.mp h
    exact sftd_softMap_ne_a hn hp hclass hloop m hm
  have hnb : Sum.inr b ∉ (markList hn hP).map f := by
    intro h
    obtain ⟨m, _, hm⟩ := List.mem_map.mp h
    exact sftd_softMap_ne_b hn hp hclass hloop m hm
  have hab : (Sum.inr a : Mark (softInsertion P j q ε)) ≠ Sum.inr b := fun h =>
    softNewbornVisits_distinct hclass hloop (Sum.inr_injective h)
  -- a candidate list which is a permutation of `a :: M_ε :: b :: (parent list).map f` is a
  -- permutation of the sorted mark list of the child
  have hperm : ∀ R : List (Mark (softInsertion P j q ε)),
      R.Perm (Sum.inr a :: Sum.inl (softNewIndex j) :: Sum.inr b :: (markList hn hP).map f) →
        (markList (by omega) hQ).Perm R := by
    intro R hR
    have hRnd : R.Nodup := by
      refine hR.nodup_iff.mpr (List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
        List.nodup_cons.mpr ⟨hnb, hndP.map hinj⟩⟩⟩)
      · simp only [List.mem_cons, not_or]
        exact ⟨Sum.inr_ne_inl, hab, hna⟩
      · simp only [List.mem_cons, not_or]
        exact ⟨Sum.inl_ne_inr, hnew⟩
    apply (List.perm_ext_iff_of_nodup hndQ hRnd).mpr
    intro m
    refine ⟨fun _ => ?_, fun _ => mem_markList _ hQ m⟩
    rw [hR.mem_iff]
    simp only [List.mem_cons, List.mem_map]
    rcases sftd_soft_mark_exhaust hn hp hclass hloop m with h | h | h | ⟨m₀, hm₀⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨m₀, mem_markList hn hP m₀, hm₀⟩))
  -- strict key order of the candidate lists
  set K : Mark (softInsertion P j q ε) → ℝ := markKey (by omega) hQ.1 with hK_def
  by_cases hj : j = 0
  · -- `j = 0`
    obtain ⟨h0b, hbT, hTa, hatt, hba⟩ := sftd_keys_zero hn hP hQ hp hclass hloop hj hbound
    subst hj
    have hhead := sfta_markList_head hn hP
    set T := (markList hn hP).tail with hTdef
    have hT : Sum.inl (0 : ZMod n) ∉ T := by
      have := hndP
      rw [hhead, List.nodup_cons] at this
      exact this.1
    have hsT : T.Pairwise (fun a b => markKey hn hP.1 a ≤ markKey hn hP.1 b) := by
      have := hsP
      rw [hhead, List.pairwise_cons] at this
      exact this.2
    have hTne : ∀ w ∈ T, w ≠ Sum.inl (0 : ZMod n) := fun w hw h => hT (h ▸ hw)
    have heq : markList (by omega) hQ =
        Sum.inl (softNewIndex (0 : ZMod n)) :: Sum.inr b ::
          (T.map f ++ [Sum.inr a, f (Sum.inl 0)]) := by
      apply List.Perm.eq_of_pairwise (le := fun x y => K x ≤ K y)
        (fun x y _ _ hxy hyx => markKey_injective _ hQ (le_antisymm hxy hyx)) hsQ
      · -- sortedness of the candidate
        have hTlt : ∀ x ∈ T.map f, K (Sum.inr b) < K x ∧ K x < K (Sum.inr a) := by
          intro x hx
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
          exact ⟨hbT w (hTne w hw), hTa w (hTne w hw)⟩
        rw [List.pairwise_cons, List.pairwise_cons, List.pairwise_append]
        refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
        · -- `M_ε` below everything
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | hx | rfl | rfl
          · exact h0b.le
          · exact (h0b.trans (hTlt x hx).1).le
          · exact (h0b.trans hba).le
          · exact (h0b.trans (hba.trans hatt)).le
        · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | rfl | rfl
          · exact (hTlt x hx).1.le
          · exact hba.le
          · exact (hba.trans hatt).le
        · rw [List.pairwise_map]
          exact hsT.imp_of_mem (fun {x y} hx hy hxy =>
            (hkey x y (fun h => absurd (h ▸ hx) hT) (fun h => absurd (h ▸ hy) hT)).mpr hxy)
        · exact List.pairwise_pair.mpr hatt.le
        · intro x hx y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact (hTlt x hx).2.le
          · exact ((hTlt x hx).2.trans hatt).le
      · apply hperm
        rw [hhead, List.map_cons]
        -- `M_ε :: b :: (T.map f ++ [a, μ_0]) ~ a :: M_ε :: b :: μ_0 :: T.map f`
        exact (List.Perm.cons _ (List.Perm.cons _ List.perm_append_comm)).trans
          (List.perm_middle (l₁ := [Sum.inl (softNewIndex 0), Sum.inr b]) (a := Sum.inr a)
            (l₂ := f (Sum.inl 0) :: T.map f))
    refine ⟨[], T, by rw [List.nil_append]; exact hhead, ?_⟩
    rw [heq, List.map_nil, List.nil_append]
    refine List.IsRotated.symm ⟨2, ?_⟩
    simp only [List.rotate_cons_succ, List.rotate_zero, List.cons_append, List.append_assoc,
      List.nil_append]
  · -- `j ≠ 0`
    obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem (mem_markList hn hP (Sum.inl j))
    obtain ⟨hka, hkm, hkb⟩ := sftd_key_block_of_ne_zero hn hP hQ hp hclass hloop hj
    have hsP' : (L₁ ++ Sum.inl j :: L₂).Pairwise (fun a b => markKey hn hP.1 a ≤ markKey hn hP.1 b) := by
      rw [← hL]; exact hsP
    have hndP' : (L₁ ++ Sum.inl j :: L₂).Nodup := by rw [← hL]; exact hndP
    obtain ⟨hL₁, hcons, hcross⟩ := List.pairwise_append.mp hsP'
    obtain ⟨hjL₂, hL₂⟩ := List.pairwise_cons.mp hcons
    obtain ⟨-, hndc, hdisj⟩ := List.nodup_append.mp hndP'
    have hjnot₂ : Sum.inl j ∉ L₂ := (List.nodup_cons.mp hndc).1
    have hjnot₁ : Sum.inl j ∉ L₁ := fun h => hdisj _ h _ List.mem_cons_self rfl
    have hkey' : ∀ x y : Mark P, K (f x) ≤ K (f y) ↔ markKey hn hP.1 x ≤ markKey hn hP.1 y :=
      fun x y => hkey x y (fun _ => hj) (fun _ => hj)
    -- the marks of `L₁` lie strictly below `a`, those of `L₂` strictly above `b`
    have hAlt : ∀ x ∈ L₁.map f, K x < K (Sum.inr a) := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      have hne : u ≠ Sum.inl j := fun h => hjnot₁ (h ▸ hu)
      exact sftd_key_lt_a_of_ne_zero hn hP hQ hp hclass hloop hj (fun v hv => (hbound v).1 hv) u
        (lt_of_le_of_ne (hcross u hu _ List.mem_cons_self)
          (fun h => hne (markKey_injective hn hP h)))
    have hBgt : ∀ x ∈ L₂.map f, K (Sum.inr b) < K x := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      have hne : w ≠ Sum.inl j := fun h => hjnot₂ (h ▸ hw)
      exact sftd_key_b_lt_of_ne_zero hn hP hQ hp hclass hloop hj (fun v hv => (hbound v).2 hv) w
        (lt_of_le_of_ne (hjL₂ w hw) (fun h => hne (markKey_injective hn hP h).symm))
    have heq : markList (by omega) hQ =
        L₁.map f ++ Sum.inr a :: f (Sum.inl j) :: Sum.inl (softNewIndex j) :: Sum.inr b ::
          L₂.map f := by
      apply List.Perm.eq_of_pairwise (le := fun x y => K x ≤ K y)
        (fun x y _ _ hxy hyx => markKey_injective _ hQ (le_antisymm hxy hyx)) hsQ
      · rw [List.pairwise_append, List.pairwise_cons, List.pairwise_cons, List.pairwise_cons,
          List.pairwise_cons]
        refine ⟨?_, ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, ?_⟩, ?_⟩
        · rw [List.pairwise_map]
          exact hL₁.imp (fun {x y} hxy => (hkey' x y).mpr hxy)
        · simp only [List.mem_cons] at hy
          rcases hy with rfl | rfl | rfl | hy
          · exact hka.le
          · exact (hka.trans hkm).le
          · exact (hka.trans (hkm.trans hkb)).le
          · exact (hka.trans (hkm.trans (hkb.trans (hBgt y hy)))).le
        · simp only [List.mem_cons] at hy
          rcases hy with rfl | rfl | hy
          · exact hkm.le
          · exact (hkm.trans hkb).le
          · exact (hkm.trans (hkb.trans (hBgt y hy))).le
        · simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hkb.le
          · exact (hkb.trans (hBgt y hy)).le
        · exact (hBgt y hy).le
        · rw [List.pairwise_map]
          exact hL₂.imp (fun {x y} hxy => (hkey' x y).mpr hxy)
        · intro x hx y hy
          have hxa := hAlt x hx
          simp only [List.mem_cons] at hy
          rcases hy with rfl | rfl | rfl | rfl | hy
          · exact hxa.le
          · exact (hxa.trans hka).le
          · exact (hxa.trans (hka.trans hkm)).le
          · exact (hxa.trans (hka.trans (hkm.trans hkb))).le
          · exact (hxa.trans (hka.trans (hkm.trans (hkb.trans (hBgt y hy))))).le
      · apply hperm
        rw [hL]
        exact sftd_block_perm L₁ L₂ _ _ _ _ _
    exact ⟨L₁, L₂, hL, by rw [heq]⟩


include hn in
/-- The newborn interlaces no inherited crossing: an alternation would put a visit strictly between
its two visits `a` and `b` on the traversal circle, against lem:soft-generic (iv). -/
theorem sftd_soft_y_isolated
    (hnob : ∀ w : Visit (softInsertion P j q ε),
      ¬ traversalBetween
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)))
    (x : Crossing P) :
    ¬ Interlaces (by omega) hQ (softNewbornCrossing hclass hloop) (softInheritedCrossing hp x) := by
  rw [sfta_interlaces_iff_visits]
  rintro ⟨-, u₀, u₁, v₀, v₁, h₀, h₁, -, -, hu, -, hb₀, hb₁⟩
  rcases softNewbornVisits_exhaust hclass hloop u₀ h₀ with rfl | rfl <;>
    rcases softNewbornVisits_exhaust hclass hloop u₁ h₁ with rfl | rfl
  · exact hu rfl
  · exact hnob v₀ hb₀
  · exact hnob v₁ hb₁
  · exact hu rfl

variable (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
  (hbound : ∀ v : Visit P,
      (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
        visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
      (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
        visitParameter (softInheritedVisit hp v)))
  (hnob : ∀ w : Visit (softInsertion P j q ε),
      ¬ traversalBetween
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)))

include hn hP hQ hp hclass hloop hord hbound hnob in
/-- **The soft loop transport** `P → P_ε` in the loop sector: vertices by `softOldIndex j`, the new
vertex `softNewIndex j`, attachment `j`, the newborn `y` with its visits `a`, `b`, crossings and
visits by the accepted inherited maps. -/
def sftd_softLoopTransport : sftd_LoopTransport hn hP hQ where
  vert := softOldIndex j
  new := softNewIndex j
  att := j
  y := softNewbornCrossing hclass hloop
  a := softNewbornIncomingVisit hclass hloop
  b := softNewbornReturnVisit hclass hloop
  a_fst := rfl
  b_fst := rfl
  a_ne_b := softNewbornVisits_distinct hclass hloop
  cross := softInheritedCrossing hp
  visit := softInheritedVisit hp
  cross_injective := softInheritedCrossing_injective hp
  cross_ne := fun x => (softInheritedCrossing_range_loop hn hp hclass hloop _).mp ⟨x, rfl⟩
  visit_fst := fun _ => rfl
  markList_insertion := sftd_soft_markList_insertion hn hP hQ hp hclass hloop hord hbound
  interlaces_iff := fun x x' => sftd_interlaces_transport hn (by omega) hP hQ _
    (softInheritedCrossing_injective hp) _ (softInheritedVisit_injective hp) (fun _ => rfl)
    (fun w x hw => (softInheritedVisit_range_crossing_iff hp w).mpr ⟨x, hw.symm⟩)
    (sfta_soft_traversalBetween_iff hn hP hQ hp hord) x x'
  y_isolated := sftd_soft_y_isolated hn hQ hp hclass hloop hnob

@[simp] theorem sftd_softLoopTransport_vert :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).vert = softOldIndex j := rfl

@[simp] theorem sftd_softLoopTransport_new :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).new = softNewIndex j := rfl

@[simp] theorem sftd_softLoopTransport_att :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).att = j := rfl

@[simp] theorem sftd_softLoopTransport_y :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).y =
      softNewbornCrossing hclass hloop := rfl

@[simp] theorem sftd_softLoopTransport_a :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).a =
      softNewbornIncomingVisit hclass hloop := rfl

@[simp] theorem sftd_softLoopTransport_b :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).b =
      softNewbornReturnVisit hclass hloop := rfl

@[simp] theorem sftd_softLoopTransport_cross (x : Crossing P) :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).cross x =
      softInheritedCrossing hp x := rfl

@[simp] theorem sftd_softLoopTransport_visit (v : Visit P) :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).visit v =
      softInheritedVisit hp v := rfl

theorem sftd_softLoopTransport_toMark (m : Mark P) :
    (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).toMark m =
      sfta_softMap hp m := rfl

/-- **Every residual mark keeps its turn** (lem:soft-generic (ii), (iii)): the vertices `k ≠ j`
literally, the smoothing corner `y` (replacing `μ_j`) turns by `sgn det(u, D_ε) = τ`, and the
inherited smoothing corners keep their crossing signs. -/
theorem sftd_softLoopTransport_markTurn'
    (hvert : ∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k)
    (hedge : ∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k)
    (hret : SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
      turn P j)
    (hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge P k) (edge P l)))
    (m : Mark P) :
    markTurn (softInsertion P j q ε)
      ((sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).toMark' m) =
      markTurn P m := by
  set τ := sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob with hτ
  by_cases hm : m = Sum.inl j
  · subst hm
    rw [show (Sum.inl j : Mark P) = Sum.inl τ.att from rfl, τ.toMark'_att, markTurn_inr,
      markTurn_inl, τ.twin_a]
    show crossingSign (softInsertion P j q ε) (softOldIndex j (j - 1)) (softNewIndex j) = turn P j
    unfold crossingSign
    rw [hedge (j - 1) (sftb_sub_one_ne hn j)]
    exact hret
  · rw [τ.toMark'_of_ne m hm]
    cases m with
    | inl k =>
      have hk : k ≠ j := fun h => hm (by rw [h])
      rw [sftd_LoopTransport.toMark_inl, markTurn_inl, markTurn_inl]
      exact hvert k hk
    | inr v =>
      rw [sftd_LoopTransport.toMark_inr, markTurn_inr, markTurn_inr, ← τ.twin_eq]
      show crossingSign (softInsertion P j q ε) (softParentEdge j v.2.val)
        (softParentEdge j (visitTwin v).2.val) = crossingSign P v.2.val (visitTwin v).2.val
      unfold crossingSign
      apply hsign
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property

/-- The three corners of the triangle `(b, μ_j, M_ε)` turn by `−τ` (sm-4:1094-1097: the turns at
`M, M_ε` are `−χ_∓ = −τ`, the smoothing turn at `b` follows `D_ε` into `u` and has sign `−τ`). -/
theorem sftd_softLoopTransport_tri_turns
    (hM : turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q)
    (hMε : turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q)
    (hedge : ∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k)
    (hret' : SignType.sign (det (edge (softInsertion P j q ε) (softNewIndex j)) (edge P (j - 1))) =
      -turn P j) :
    turn (softInsertion P j q ε)
        ((sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).vert
          (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).att) = -turn P j ∧
    turn (softInsertion P j q ε)
      (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).new = -turn P j ∧
    markTurn (softInsertion P j q ε)
      (Sum.inr (sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob).b) = -turn P j := by
  set τ := sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob with hτ
  refine ⟨?_, ?_, ?_⟩
  · show turn (softInsertion P j q ε) (softOldIndex j j) = -turn P j
    rw [hM, hloop.1]
  · show turn (softInsertion P j q ε) (softNewIndex j) = -turn P j
    rw [hMε, hloop.2]
  · rw [markTurn_inr, τ.twin_b]
    show crossingSign (softInsertion P j q ε) (softNewIndex j) (softOldIndex j (j - 1)) = -turn P j
    unfold crossingSign
    rw [hedge (j - 1) (sftb_sub_one_ne hn j)]
    exact hret'

end SftdSoftInstance

section SftdSoftData

/-- **The loop-sector data on one interval** (lem:soft-generic `soft_family_generic` and the
newborn-arc theorem `soft_newborn_small_empty_arc`): for every small `ε > 0` and every genericity
proof of `P_ε`, the persistence and classification, the same-edge visit order, the newborn
parameter bounds, the empty short arc, the vertex directions and turns, the newborn determinant
signs, the inherited crossing signs and the crossing points. -/
theorem sftd_soft_loop_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n)
    (q : Plane) (hq : SoftAdmissible P j q)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ hQ : Generic (softInsertion P j q ε),
      ∃ (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε),
        (∀ v w : Visit P, v.2.val = w.2.val →
          (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
            visitParameter v < visitParameter w)) ∧
        (∀ v : Visit P,
          (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
            visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
          (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
            visitParameter (softInheritedVisit hp v))) ∧
        (∀ w : Visit (softInsertion P j q ε),
          ¬ traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop))) ∧
        (∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k) ∧
        (∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k) ∧
        turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
        turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q ∧
        SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
          turn P j ∧
        SignType.sign (det (edge (softInsertion P j q ε) (softNewIndex j)) (edge P (j - 1))) =
          -turn P j ∧
        (∀ k l : ZMod n, IsCrossing P {k, l} →
          SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l))) ∧
        (∀ k l : ZMod n, ∀ hc : IsCrossing P {k, l},
          crossingPoint (softInheritedCrossing hp (⟨{k, l}, hc⟩ : Crossing P)) =
            softInheritedPoint P j k l q ε) ∧
        crossingPoint (softNewbornCrossing hclass hloop) = softNewbornPoint P j q ε := by
  obtain ⟨δ₁, hδ₁, _B, hall⟩ := (soft_family_generic hn hP j q hq).2.2.2.2.2
  obtain ⟨δ₂, hδ₂, harc⟩ := soft_newborn_small_empty_arc hn hP j q hq
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε hεδ hQ => ?_⟩
  obtain ⟨_, hp, hclass, _, hii, hiii, hord, _, hiv⟩ :=
    hall ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
  obtain ⟨_, hp', hclass', harc'⟩ := harc ε hε (lt_of_lt_of_le hεδ (min_le_right _ _))
  obtain ⟨hbound, hnob⟩ := harc' hloop
  exact ⟨hp, hclass, hord, hbound, hnob, hii.1, hii.2.2.2.1, hii.2.2.2.2.1, hii.2.2.2.2.2.1,
    hii.2.2.2.2.2.2.1, hii.2.2.2.2.2.2.2, fun k l hc => (hiii k l hc).2.2.2.1,
    fun k l hc => (hiii k l hc).2.2.2.2.1, (hiv hloop).2.2.1⟩

end SftdSoftData

section SftdRecord

/-- `List.next` commutes with an injective map. -/
theorem sftd_next_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List α) (hl : l.Nodup) (x : α) (hx : x ∈ l)
    (hx' : f x ∈ l.map f) : (l.map f).next (f x) hx' = f (l.next x hx) := by
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hl' : (l.map f).Nodup := hl.map hf
  have hi' : i < (l.map f).length := by rw [List.length_map]; exact hi
  rw [sfta_next_eq_of_getElem hl i hi x hx hix.symm,
    sfta_next_eq_of_getElem hl' i hi' (f x) hx' (by rw [List.getElem_map, hix])]
  simp only [List.getElem_map, List.length_map]

namespace sftd_LoopTransport

variable {hn : 3 ≤ n} {P : LabelledTuple n} {Q : LabelledTuple (n + 1)} {hP : Generic P}
  {hQ : Generic Q} (τ : sftd_LoopTransport hn hP hQ)

/-- The transported crossing set of a Gauss record. -/
def crossSet (X : Finset (Crossing P)) : Finset (Crossing Q) := X.map ⟨τ.cross, τ.cross_injective⟩

theorem mem_crossSet (X : Finset (Crossing P)) (d : Crossing Q) :
    d ∈ τ.crossSet X ↔ ∃ x ∈ X, τ.cross x = d := by
  simp only [crossSet, Finset.mem_map, Function.Embedding.coeFn_mk]

/-- **The Gauss list of `Q` at the transported crossings is the transported Gauss list of `P`**
("their retained crossing successors and pairings agree under the inherited correspondence"),
given that the visit keys compare as the parent keys. -/
theorem gaussList_transport
    (hbtw : ∀ v w : Visit P, visitKey (by omega) hQ.1 (τ.visit v) < visitKey (by omega) hQ.1 (τ.visit w) ↔
      visitKey hn hP.1 v < visitKey hn hP.1 w) (X : Finset (Crossing P)) :
    CB.gaussList (CB.cg (by omega) hQ) (τ.crossSet X) = (CB.gaussList (CB.cg hn hP) X).map τ.visit := by
  apply List.Perm.eq_of_pairwise
    (le := fun v w : Visit Q => visitKey (by omega) hQ.1 v < visitKey (by omega) hQ.1 w)
    (fun v w _ _ h1 h2 => absurd h2 (lt_asymm h1))
  · exact CB.kl2_gaussList_pairwise_lt _ _
  · rw [List.pairwise_map]
    exact (CB.kl2_gaussList_pairwise_lt (CB.cg hn hP) X).imp (fun {v w} h => (hbtw v w).mpr h)
  · apply (List.perm_ext_iff_of_nodup (CB.kl2_gaussList_nodup _ _)
      ((CB.kl2_gaussList_nodup _ _).map τ.visit_injective)).mpr
    intro w
    rw [CB.kl2_mem_gaussList, List.mem_map, τ.mem_crossSet]
    constructor
    · rintro ⟨x, hx, hxw⟩
      obtain ⟨v, rfl⟩ := τ.visit_range w (by rw [← hxw]; exact τ.cross_ne x)
      have hv : v.1 = x := (τ.visit_fst_eq_iff v x).mp hxw.symm
      refine ⟨v, (CB.kl2_mem_gaussList _ _ v).mpr ?_, rfl⟩
      rw [hv]; exact hx
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.1, (CB.kl2_mem_gaussList _ _ v).mp hv, (τ.visit_fst v).symm⟩

/-- The occurrence map of the record isomorphism. -/
def occMap (X : Finset (Crossing P)) (v : {v : Visit P // v.1 ∈ X}) :
    {w : Visit Q // w.1 ∈ τ.crossSet X} :=
  ⟨τ.visit v.1, (τ.mem_crossSet X _).mpr ⟨v.1.1, v.2, (τ.visit_fst v.1).symm⟩⟩

theorem occMap_val (X : Finset (Crossing P)) (v : {v : Visit P // v.1 ∈ X}) :
    (τ.occMap X v).1 = τ.visit v.1 := rfl

theorem occMap_bijective (X : Finset (Crossing P)) : Function.Bijective (τ.occMap X) := by
  refine ⟨fun v w h => Subtype.ext (τ.visit_injective (congrArg Subtype.val h)), fun w => ?_⟩
  obtain ⟨x, hx, hxw⟩ := (τ.mem_crossSet X _).mp w.2
  obtain ⟨v, hv⟩ := τ.visit_range w.1 (by rw [← hxw]; exact τ.cross_ne x)
  refine ⟨⟨v, ?_⟩, Subtype.ext hv⟩
  have hvx : v.1 = x := (τ.visit_fst_eq_iff v x).mp (by rw [hv]; exact hxw.symm)
  rw [hvx]; exact hx

/-- **The named record isomorphism** (def:gauss-record) between the restricted Gauss record of `P`
at `X` and that of `Q` at the transported crossings: occurrences by `visit`, the successor by the
transported Gauss list, the pairing by `twin_eq`, the over bits by the inherited determinant signs
(lem:soft-generic (iii)), all signs `+1`. -/
def gaussRecordIso
    (hbtw : ∀ v w : Visit P, visitKey (by omega) hQ.1 (τ.visit v) < visitKey (by omega) hQ.1 (τ.visit w) ↔
      visitKey hn hP.1 v < visitKey hn hP.1 w)
    (hbit : ∀ v : Visit P, CB.positiveOverBit (τ.visit v) = CB.positiveOverBit v)
    (X : Finset (Crossing P)) :
    RecordIso (CB.gaussRecord (CB.cg hn hP) X) (CB.gaussRecord (CB.cg (by omega) hQ) (τ.crossSet X)) where
  e := Equiv.refl Unit
  Φ := Equiv.ofBijective (τ.occMap X) (τ.occMap_bijective X)
  comp_eq _ := rfl
  succ_eq v := by
    apply Subtype.ext
    change (τ.occMap X (CB.gaussSucc (CB.cg hn hP) X v)).1 =
      (CB.gaussSucc (CB.cg (by omega) hQ) (τ.crossSet X) (τ.occMap X v)).1
    rw [occMap_val, CB.gaussSucc_val _ _ _ ((CB.kl2_mem_gaussList _ _ _).mpr v.2),
      CB.gaussSucc_val _ _ _ ((CB.kl2_mem_gaussList _ _ _).mpr (τ.occMap X v).2),
      sfta_next_congr (τ.gaussList_transport hbtw X)]
    exact (sftd_next_map τ.visit τ.visit_injective _ (CB.kl2_gaussList_nodup _ _) v.1 _ _).symm
  pair_eq v := by
    apply Subtype.ext
    show τ.visit (visitTwin v.1) = visitTwin (τ.visit v.1)
    exact τ.twin_eq v.1
  bit_eq v := hbit v.1
  sgn_eq _ := rfl

/-- **Equal HOMFLY–PT polynomials of the positive lifts** of a carrier and its residual carrier
(sm-4:1114-1118: "the earlier named-record argument gives equal positive-lift polynomials"):
`CB.positiveLiftRecordIso` (cb:products KL1) on both sides and the record isomorphism above, through
lc:presentations (`presentations`) and lp:core's `P = homfly`. -/
theorem homfly_residual
    (hbtw : ∀ v w : Visit P, visitKey (by omega) hQ.1 (τ.visit v) < visitKey (by omega) hQ.1 (τ.visit w) ↔
      visitKey hn hP.1 v < visitKey hn hP.1 w)
    (hbit : ∀ v : Visit P, CB.positiveOverBit (τ.visit v) = CB.positiveOverBit v)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    homfly (positiveLift (by omega) hQ (τ.supportY S) (τ.residual S q)
        ((τ.isDecomposition_supportY_iff S).mpr hS)) = homfly (positiveLift hn hP S q hS) := by
  rw [← P_eq_homfly, ← P_eq_homfly]
  apply presentations
  refine ⟨(CB.positiveLiftRecordIso (by omega) hQ ((τ.isDecomposition_supportY_iff S).mpr hS)
    (τ.residual S q)).trans ?_⟩
  have hX : carrierCrossings (by omega) hQ (τ.supportY S) (τ.residual S q) =
      τ.crossSet (carrierCrossings hn hP S q) := τ.carrierCrossings_residual S q
  rw [hX]
  exact (τ.gaussRecordIso hbtw hbit (carrierCrossings hn hP S q)).symm.trans
    (CB.positiveLiftRecordIso hn hP hS q).symm

end sftd_LoopTransport

/-- The over bit of the positive resolution is inherited (lem:soft-generic (iii): the determinant
signs of corresponding ordered direction pairs agree). -/
theorem sftd_soft_positiveOverBit (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n}
    {q : Plane} {ε : ℝ} (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hord : ∀ v w : Visit P, v.2.val = w.2.val →
      (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
        visitParameter v < visitParameter w))
    (hbound : ∀ v : Visit P,
      (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
        visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
      (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
        visitParameter (softInheritedVisit hp v)))
    (hnob : ∀ w : Visit (softInsertion P j q ε),
      ¬ traversalBetween
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)))
    (hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge P k) (edge P l)))
    (v : Visit P) : CB.positiveOverBit (softInheritedVisit hp v) = CB.positiveOverBit v := by
  set τ := sftd_softLoopTransport hn hP hQ hp hclass hloop hord hbound hnob with hτ
  have ht : visitTwin (softInheritedVisit hp v) = softInheritedVisit hp (visitTwin v) :=
    (τ.twin_eq v).symm
  unfold CB.positiveOverBit
  rw [ht]
  simp only [softInheritedVisit_edge]
  apply decide_eq_decide.mpr
  rw [← sign_eq_one_iff, ← sign_eq_one_iff]
  have hs := hsign v.2.val (visitTwin v).2.val (by
    rw [← visit_crossing_val_eq_pair v]; exact v.1.property)
  rw [hs]

end SftdRecord

section SftdLoopData

/-- **The loop-sector data at one parameter** (all supplied on an interval by
`sftd_soft_loop_data`): persistence and classification of the crossings, the same-edge visit order,
the newborn parameter bounds, the empty short arc `a → μ_j → M_ε → b`, the unchanged directions and
turns, the two newborn determinant signs, the inherited crossing signs and the crossing points. -/
structure sftd_LoopData (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (ε : ℝ) (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hQ : Generic (softInsertion P j q ε)) : Prop where
  hp : SoftCrossingPersistence P j q ε
  hclass : SoftCrossingClassificationAt P j q ε
  hord : ∀ v w : Visit P, v.2.val = w.2.val →
    (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
      visitParameter v < visitParameter w)
  hbound : ∀ v : Visit P,
    (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
      visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
    (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
      visitParameter (softInheritedVisit hp v))
  hnob : ∀ w : Visit (softInsertion P j q ε),
    ¬ traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
      (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
      (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop))
  hedge : ∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k
  hvert : ∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k
  hM : turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q
  hMε : turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q
  hret : SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
    turn P j
  hret' : SignType.sign (det (edge (softInsertion P j q ε) (softNewIndex j)) (edge P (j - 1))) =
    -turn P j
  hsign : ∀ k l : ZMod n, IsCrossing P {k, l} →
    SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
      (edge (softInsertion P j q ε) (softParentEdge j l))) =
    SignType.sign (det (edge P k) (edge P l))
  hpt : ∀ k l : ZMod n, ∀ hc : IsCrossing P {k, l},
    crossingPoint (softInheritedCrossing hp (⟨{k, l}, hc⟩ : Crossing P)) =
      softInheritedPoint P j k l q ε
  hnb : crossingPoint (softNewbornCrossing hclass hloop) = softNewbornPoint P j q ε

/-- The data theorem in packaged form. -/
theorem sftd_soft_loop_data' (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n)
    (q : Plane) (hq : SoftAdmissible P j q)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ hQ : Generic (softInsertion P j q ε),
      sftd_LoopData hn hP j q ε hloop hQ := by
  obtain ⟨δ, hδ, h⟩ := sftd_soft_loop_data hn hP j q hq hloop
  refine ⟨δ, hδ, fun ε hε hlt hQ => ?_⟩
  obtain ⟨hp, hclass, hord, hbound, hnob, hedge, hvert, hM, hMε, hret, hret', hsign, hpt, hnb⟩ :=
    h ε hε hlt hQ
  exact ⟨hp, hclass, hord, hbound, hnob, hedge, hvert, hM, hMε, hret, hret', hsign, hpt, hnb⟩

/-- `P_ε` is generic for all small `ε > 0` (lem:soft-generic (i)). -/
theorem sftd_soft_generic_small (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n)
    (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → Generic (softInsertion P j q ε) := by
  obtain ⟨δ, hδ, h⟩ := soft_small_crossing_transport_data hn hP j q hq
  exact ⟨δ, hδ, fun ε hε hlt => (h ε hε hlt).1⟩

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {j : ZMod n} {q : Plane} {ε : ℝ}
  (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
  (hQ : Generic (softInsertion P j q ε)) (d : sftd_LoopData hn hP j q ε hloop hQ)

/-- The soft loop transport built from the packaged data. -/
def sftd_loopTransport : sftd_LoopTransport hn hP hQ :=
  sftd_softLoopTransport hn hP hQ d.hp d.hclass hloop d.hord d.hbound d.hnob

theorem sftd_loopTransport_markTurn' (m : Mark P) :
    markTurn (softInsertion P j q ε) ((sftd_loopTransport hn hP hloop hQ d).toMark' m) =
      markTurn P m :=
  sftd_softLoopTransport_markTurn' hn hP hQ d.hp d.hclass hloop d.hord d.hbound d.hnob d.hvert
    d.hedge d.hret d.hsign m

theorem sftd_loopTransport_tri_turns :
    turn (softInsertion P j q ε)
        ((sftd_loopTransport hn hP hloop hQ d).vert (sftd_loopTransport hn hP hloop hQ d).att) =
      -turn P j ∧
    turn (softInsertion P j q ε) (sftd_loopTransport hn hP hloop hQ d).new = -turn P j ∧
    markTurn (softInsertion P j q ε) (Sum.inr (sftd_loopTransport hn hP hloop hQ d).b) = -turn P j :=
  sftd_softLoopTransport_tri_turns hn hP hQ d.hp d.hclass hloop d.hord d.hbound d.hnob d.hM d.hMε
    d.hedge d.hret'

theorem sftd_loopTransport_homfly (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q' : Component hn hP S) :
    homfly (positiveLift (by omega) hQ ((sftd_loopTransport hn hP hloop hQ d).supportY S)
        ((sftd_loopTransport hn hP hloop hQ d).residual S q')
        (((sftd_loopTransport hn hP hloop hQ d).isDecomposition_supportY_iff S).mpr hS)) =
      homfly (positiveLift hn hP S q' hS) :=
  (sftd_loopTransport hn hP hloop hQ d).homfly_residual
    (fun v w => sfta_soft_visitKey_lt_iff hn hP hQ d.hp d.hord v w)
    (fun v => sftd_soft_positiveOverBit hn hP hQ d.hp d.hclass hloop d.hord d.hbound d.hnob d.hsign v)
    S hS q'

end SftdLoopData

section SftdRotation

namespace sftd_LoopTransport

variable {hn : 3 ≤ n} {P : LabelledTuple n} {Q : LabelledTuple (n + 1)} {hP : Generic P}
  {hQ : Generic Q} (τ : sftd_LoopTransport hn hP hQ)

/-- The corner polygon of the carrier `q` read through the residual map at the geometry of `Q`. -/
def residualCornerPolygon (S : Finset (Crossing P)) (q : Component hn hP S) :
    LabelledTuple (ccpCornerCount hn hP S q) :=
  fun i => traversalEvaluation Q (markPosition (by omega) hQ.1 (τ.toMark' (ccpCornerMark hn hP S q i)))

theorem exists_ccpCornerMark_residual (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ r : ZMod (ccpCornerCount hn hP S q),
      ∀ i : ZMod (ccpCornerCount (by omega) hQ (τ.supportY S) (τ.residual S q)),
        ccpCornerMark (by omega) hQ (τ.supportY S) (τ.residual S q) i =
          τ.toMark' (ccpCornerMark hn hP S q
            (Equiv.cast (congrArg ZMod (τ.ccpCornerCount_residual S q)) i + r)) := by
  obtain ⟨m, hm⟩ := (τ.ccpCornerList_residual S q).symm
  refine ⟨(m : ZMod (ccpCornerCount hn hP S q)), fun i => ?_⟩
  unfold ccpCornerMark
  refine Carrier.MarkTransport.getElem_eq_map_of_rotate_eq τ.toMark' _ _ m hm _ _ ?_ _ _
  change (_ + m) % ccpCornerCount hn hP S q = _
  rw [ZMod.val_add, ZMod.val_natCast, zmod_val_cast (τ.ccpCornerCount_residual S q) i,
    Nat.add_mod_mod]

/-- The corner polygon of the residual carrier is the residual corner polygon up to a cyclic
re-indexing. -/
theorem exists_ccpCornerPolygon_residual (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ r : ZMod (ccpCornerCount hn hP S q),
      ccpCornerPolygon (by omega) hQ (τ.supportY S) (τ.residual S q) =
        recastTuple (τ.ccpCornerCount_residual S q) (shift r (τ.residualCornerPolygon S q)) := by
  obtain ⟨r, hr⟩ := τ.exists_ccpCornerMark_residual S q
  refine ⟨r, funext fun i => ?_⟩
  rw [ccpCornerPolygon_apply, hr i]
  rfl

theorem carrierRotation_residual_eq (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierRotation (by omega) hQ (τ.supportY S) (τ.residual S q) =
      rotationNumber (τ.residualCornerPolygon S q) := by
  obtain ⟨r, hr⟩ := τ.exists_ccpCornerPolygon_residual S q
  unfold carrierRotation
  rw [hr, rotationNumber_recastTuple, rotationNumber_shift]

end sftd_LoopTransport

/-- The plane point of a residual corner as a function of the parameter `ε`: vertices stay, the
attachment vertex becomes the newborn point `y_ε`, the inherited crossing points move by Cramer's
rule (`softInheritedPoint`). -/
def sftd_cornerPoint (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) : Mark P → Plane
  | Sum.inl k => if k = j then softNewbornPoint P j q ε else P k
  | Sum.inr v => softInheritedPoint P j v.2.val (visitTwin v).2.val q ε

/-- The residual corner polygon of the carrier `q'` of `S` as a function of `ε`. -/
def sftd_cornerFamily (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n) (q : Plane)
    (S : Finset (Crossing P)) (q' : Component hn hP S) (ε : ℝ) :
    LabelledTuple (ccpCornerCount hn hP S q') :=
  fun i => sftd_cornerPoint P j q ε (ccpCornerMark hn hP S q' i)

/-- At `ε = 0` the family is the parent's corner polygon (`y_0 = μ_j`, inherited points at their
parent crossing points). -/
theorem sftd_cornerFamily_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (j : ZMod n)
    (q : Plane) (S : Finset (Crossing P)) (q' : Component hn hP S) :
    sftd_cornerFamily hn hP j q S q' 0 = ccpCornerPolygon hn hP S q' := by
  funext i
  unfold sftd_cornerFamily
  rw [ccpCornerPolygon_apply]
  cases hm : ccpCornerMark hn hP S q' i with
  | inl k =>
    rw [markPosition_evaluation_vertex]
    by_cases hk : k = j
    · subst hk
      show (if k = k then softNewbornPoint P k q 0 else P k) = P k
      rw [ite_eq_left rfl]
      exact (softNewborn_values_zero hn hP.1 k q).2.2
    · show (if k = j then softNewbornPoint P j q 0 else P k) = P k
      rw [ite_eq_right hk]
  | inr v =>
    rw [markPosition_evaluation_visit]
    show softInheritedPoint P j v.2.val (visitTwin v).2.val q 0 = crossingPoint v.1
    have hc : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]; exact v.1.property
    rw [softInheritedPoint_zero_crossing hn hP.1 j _ _ q hc]
    congr 1
    exact (Subtype.ext (visit_crossing_val_eq_pair v) : v.1 = ⟨_, hc⟩).symm

/-- The family is continuous at `ε = 0` (lem:soft-generic: the newborn point and the inherited
crossing points converge to their parents). -/
theorem sftd_cornerFamily_continuousAt (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (S : Finset (Crossing P)) (q' : Component hn hP S) :
    ContinuousAt (sftd_cornerFamily hn hP j q S q') 0 := by
  apply continuousAt_pi.mpr
  intro i
  unfold sftd_cornerFamily
  cases hm : ccpCornerMark hn hP S q' i with
  | inl k =>
    by_cases hk : k = j
    · subst hk
      have h : (fun ε => sftd_cornerPoint P k q ε (Sum.inl k)) = softNewbornPoint P k q := by
        funext ε
        show (if k = k then softNewbornPoint P k q ε else P k) = _
        rw [ite_eq_left rfl]
      rw [h]
      exact (softNewborn_continuousAt_zero hn hP.1 k q).2.2
    · have h : (fun ε => sftd_cornerPoint P j q ε (Sum.inl k)) = fun _ => P k := by
        funext ε
        show (if k = j then softNewbornPoint P j q ε else P k) = _
        rw [ite_eq_right hk]
      rw [h]
      exact continuousAt_const
  | inr v =>
    show ContinuousAt (fun ε => softInheritedPoint P j v.2.val (visitTwin v).2.val q ε) 0
    have hc : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]; exact v.1.property
    exact continuousAt_softInheritedPoint P j _ _ q (crossing_det_ne_zero_of_geometry (CB.cg hn hP) hc)

/-- The rotation number is continuous at a regular polygon of a continuous family
(`continuousAt_principalAngle`, RotationContinuity.lean). -/
theorem sftd_rotationNumber_continuousAt {k : ℕ} [NeZero k] {g : ℝ → LabelledTuple k}
    (hg : ContinuousAt g 0) (hr : Regular (g 0)) :
    ContinuousAt (fun ε => rotationNumber (g ε)) 0 := by
  have he : ∀ i : ZMod k, ContinuousAt (fun ε => edge (g ε) i) 0 := fun i =>
    ((continuous_apply (i + 1)).continuousAt.comp hg).sub ((continuous_apply i).continuousAt.comp hg)
  have h : ∀ i : ZMod k, ContinuousAt (fun ε => principalTurn (g ε) i) 0 := fun i =>
    continuousAt_principalAngle (he (i - 1)) (he i) (hr i)
  unfold rotationNumber
  exact (tendsto_finsetSum _ (fun i _ => h i)).div_const _

/-- An integer-valued function on `(0, δ)`, continuous at `0` with an integer value there, is
eventually equal to its value at `0` ("integer-valuedness again gives equality of all rotations on a
common small interval"). -/
theorem sftd_eventually_eq_of_continuousAt_int {φ : ℝ → ℝ} (hφ : ContinuousAt φ 0) {δ : ℝ}
    (hδ : 0 < δ) (hint : ∀ ε : ℝ, 0 < ε → ε < δ → ∃ k : ℤ, φ ε = k) (h0 : ∃ k₀ : ℤ, φ 0 = k₀) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₂ → φ ε = φ 0 := by
  obtain ⟨k₀, hk₀⟩ := h0
  have ht := Metric.tendsto_nhds.mp hφ 1 one_pos
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp ht
  refine ⟨min ε₁ δ, lt_min hε₁ hδ, fun ε hε hlt => ?_⟩
  obtain ⟨k, hk⟩ := hint ε hε (lt_of_lt_of_le hlt (min_le_right _ _))
  have hd : dist (φ ε) (φ 0) < 1 := hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    exact lt_of_lt_of_le hlt (min_le_left _ _))
  rw [hk, hk₀, Real.dist_eq] at hd
  have hd' : |k - k₀| < 1 := by exact_mod_cast hd
  rw [hk, hk₀]
  exact_mod_cast (sub_eq_zero.mp (Int.abs_lt_one_iff.mp hd'))

/-- The residual corner polygon of the soft loop transport is the corner family at `ε`. -/
theorem sftd_residualCornerPolygon_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {j : ZMod n} {q : Plane} {ε : ℝ}
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hQ : Generic (softInsertion P j q ε)) (d : sftd_LoopData hn hP j q ε hloop hQ)
    (S : Finset (Crossing P)) (q' : Component hn hP S) :
    (sftd_loopTransport hn hP hloop hQ d).residualCornerPolygon S q' =
      sftd_cornerFamily hn hP j q S q' ε := by
  set τ := sftd_loopTransport hn hP hloop hQ d with hτ
  funext i
  unfold sftd_LoopTransport.residualCornerPolygon sftd_cornerFamily
  generalize ccpCornerMark hn hP S q' i = m
  by_cases hm : m = Sum.inl j
  · subst hm
    rw [show (Sum.inl j : Mark P) = Sum.inl τ.att from rfl, τ.toMark'_att,
      markPosition_evaluation_visit]
    show crossingPoint (softNewbornCrossing d.hclass hloop) =
      (if j = j then softNewbornPoint P j q ε else P j)
    rw [ite_eq_left rfl]
    exact d.hnb
  · rw [τ.toMark'_of_ne m hm]
    cases m with
    | inl k =>
      have hk : k ≠ j := fun h => hm (by rw [h])
      rw [sftd_LoopTransport.toMark_inl, markPosition_evaluation_vertex]
      show softInsertion P j q ε (softOldIndex j k) = (if k = j then softNewbornPoint P j q ε else P k)
      rw [ite_eq_right hk, softInsertion_old]
    | inr v =>
      rw [sftd_LoopTransport.toMark_inr, markPosition_evaluation_visit]
      show crossingPoint (softInheritedCrossing d.hp v.1) =
        softInheritedPoint P j v.2.val (visitTwin v).2.val q ε
      have hc : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
        rw [← visit_crossing_val_eq_pair v]; exact v.1.property
      have hv1 : v.1 = ⟨{v.2.val, (visitTwin v).2.val}, hc⟩ :=
        Subtype.ext (visit_crossing_val_eq_pair v)
      exact (congrArg (fun c => crossingPoint (softInheritedCrossing d.hp c)) hv1).trans
        (d.hpt _ _ hc)

/-- **The rotation of a residual carrier equals its parent's for all small `ε`**
(sm-4:1110-1114): the residual corner polygon converges to the parent's regular corner polygon,
the rotation number is continuous there, both are integers. -/
theorem sftd_residual_rotation_eventually (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q' : Component hn hP S) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₂ → ∀ (hQ : Generic (softInsertion P j q ε))
      (d : sftd_LoopData hn hP j q ε hloop hQ),
      carrierRotation (by omega) hQ ((sftd_loopTransport hn hP hloop hQ d).supportY S)
          ((sftd_loopTransport hn hP hloop hQ d).residual S q') =
        carrierRotation hn hP S q' := by
  obtain ⟨δ₁, hδ₁, hdata⟩ := sftd_soft_loop_data' hn hP j q hq hloop
  obtain ⟨δ₂, hδ₂, hgen⟩ := sftd_soft_generic_small hn hP j q hq
  set g := sftd_cornerFamily hn hP j q S q' with hg
  have hg0 : g 0 = ccpCornerPolygon hn hP S q' := sftd_cornerFamily_zero hn hP j q S q'
  have hcont : ContinuousAt (fun ε => rotationNumber (g ε)) 0 :=
    sftd_rotationNumber_continuousAt (sftd_cornerFamily_continuousAt hn hP j q S q')
      (by rw [hg0]; exact ccpCornerPolygon_regular hn hP hS q')
  have hint : ∀ ε : ℝ, 0 < ε → ε < min δ₁ δ₂ → ∃ k : ℤ, rotationNumber (g ε) = k := by
    intro ε hε hlt
    have hQ := hgen ε hε (lt_of_lt_of_le hlt (min_le_right _ _))
    have d := hdata ε hε (lt_of_lt_of_le hlt (min_le_left _ _)) hQ
    set τ := sftd_loopTransport hn hP hloop hQ d with hτ
    obtain ⟨k, hk⟩ := carrierRotation_exists_int (by omega) hQ
      ((τ.isDecomposition_supportY_iff S).mpr hS) (τ.residual S q')
    refine ⟨k, ?_⟩
    show rotationNumber (sftd_cornerFamily hn hP j q S q' ε) = (k : ℝ)
    rw [← sftd_residualCornerPolygon_eq hn hP hloop hQ d S q', ← τ.carrierRotation_residual_eq S q',
      hk]
  have h0 : ∃ k₀ : ℤ, rotationNumber (g 0) = k₀ := by
    rw [hg0]; exact carrierRotation_exists_int hn hP hS q'
  obtain ⟨ε₂, hε₂, hev⟩ :=
    sftd_eventually_eq_of_continuousAt_int hcont (lt_min hδ₁ hδ₂) hint h0
  refine ⟨ε₂, hε₂, fun ε hε hlt hQ d => ?_⟩
  set τ := sftd_loopTransport hn hP hloop hQ d with hτ
  rw [τ.carrierRotation_residual_eq S q', sftd_residualCornerPolygon_eq hn hP hloop hQ d S q']
  change rotationNumber (g ε) = rotationNumber (ccpCornerPolygon hn hP S q')
  rw [hev ε hε hlt, hg0]

/-- A finite family of positive reals has a positive common lower bound. -/
theorem sftd_finite_min {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ i, ε₀ ≤ f i := by
  classical
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/-- **Uniform version**: one `ε₂` for all (finitely many) decompositions and carriers. -/
theorem sftd_residual_rotation_bound (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
      (q' : Component hn hP S) (ε : ℝ), 0 < ε → ε < ε₂ → ∀ (hQ : Generic (softInsertion P j q ε))
      (d : sftd_LoopData hn hP j q ε hloop hQ),
      carrierRotation (by omega) hQ ((sftd_loopTransport hn hP hloop hQ d).supportY S)
          ((sftd_loopTransport hn hP hloop hQ d).residual S q') =
        carrierRotation hn hP S q' := by
  classical
  have hex : ∀ σ : Σ S : Finset (Crossing P), Component hn hP S, ∃ ε₂ : ℝ, 0 < ε₂ ∧
      (IsDecomposition hn hP σ.1 → ∀ ε : ℝ, 0 < ε → ε < ε₂ →
        ∀ (hQ : Generic (softInsertion P j q ε)) (d : sftd_LoopData hn hP j q ε hloop hQ),
        carrierRotation (by omega) hQ ((sftd_loopTransport hn hP hloop hQ d).supportY σ.1)
            ((sftd_loopTransport hn hP hloop hQ d).residual σ.1 σ.2) =
          carrierRotation hn hP σ.1 σ.2) := by
    intro σ
    by_cases hS : IsDecomposition hn hP σ.1
    · obtain ⟨ε₂, hε₂, h⟩ := sftd_residual_rotation_eventually hn hP j q hq hloop σ.1 hS σ.2
      exact ⟨ε₂, hε₂, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hS⟩
  choose f hf using hex
  obtain ⟨ε₂, hε₂, hle⟩ := sftd_finite_min f (fun σ => (hf σ).1)
  exact ⟨ε₂, hε₂, fun S hS q' ε hε hlt hQ d =>
    (hf ⟨S, q'⟩).2 hS ε hε (lt_of_lt_of_le hlt (hle ⟨S, q'⟩)) hQ d⟩

end SftdRotation

section SftdSign

/-- The sign bookkeeping of the loop sector: from `ℓ(Q) + [τ = 1] = ℓ(P) + 2[−τ = 1]`,
`−(−1)^{ℓ(Q)+ℓ(P)} = τ` for `τ = ±1` (sm-4:1137-1142). -/
theorem sftd_sign_arith (ℓQ ℓP a b : ℕ) (h : ℓQ + a = ℓP + b + b) :
    (-1 : ℤ) ^ (ℓQ + ℓP) = (-1) ^ a := by
  have h1 : (-1 : ℤ) ^ (ℓQ + a + ℓP) = 1 := by
    rw [h, show ℓP + b + b + ℓP = 2 * (ℓP + b) by ring, pow_mul, neg_one_sq, one_pow]
  have h2 : ((-1 : ℤ) ^ a) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  calc (-1 : ℤ) ^ (ℓQ + ℓP) = (-1) ^ (ℓQ + ℓP) * ((-1) ^ a) ^ 2 := by rw [h2, mul_one]
    _ = (-1) ^ (ℓQ + a + ℓP) * (-1) ^ a := by ring
    _ = (-1) ^ a := by rw [h1, one_mul]

theorem sftd_neg_sign_pow (τ : SignType) (hτ : τ ≠ 0) (x : ℤ) :
    -((-1 : ℤ) ^ (if τ = 1 then 1 else 0) * x) = (τ : ℤ) * x := by
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · simp
  · exact absurd rfl hτ
  · simp

end SftdSign

/-- Loop sector `χ₋ = χ₊ = τ` (sm-4:1067-1143): the newborn `y` is isolated; supports omitting `y`
contribute `0` by lem:corner-values (ii) (HERE row 105 (ii), hence the floor, enters); for `S ∪ {y}` the
triangle `(b, M, M_ε)` has coefficient `1` by lem:corner-values (i) and the residual carriers correspond to
those of `S` with `M` replaced by the smoothing corner `y` of the same sign; sign bookkeeping gives
`C(P_ε) = τ C(P)`. -/
theorem sft_loop (hCV : CornerValuesData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (hl : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      cornerStateSum (by omega : 3 ≤ n + 1) hQ = (turn P j : ℤ) * cornerStateSum hn hP := by
  -- the loop-sector data on one interval and the rotation bound
  obtain ⟨δ, hδ, hdata⟩ := sftd_soft_loop_data' hn hP j q hq hl
  obtain ⟨ε₂, hε₂, hrot⟩ := sftd_residual_rotation_bound hn hP j q hq hl
  refine ⟨min δ ε₂, lt_min hδ hε₂, fun ε hε hlt hQ => ?_⟩
  have d := hdata ε hε (lt_of_lt_of_le hlt (min_le_left _ _)) hQ
  set τ := sftd_loopTransport hn hP hl hQ d with hτ
  have hτne : -turn P j ≠ 0 := fun h => sft_turn_ne_zero hn hP j (SignType.neg_eq_zero_iff.mp h)
  -- turns: every residual corner keeps its turn, the triangle turns by `−τ`
  have hturn := sftd_loopTransport_markTurn' hn hP hl hQ d
  obtain ⟨ht1, ht2, ht3⟩ := sftd_loopTransport_tri_turns hn hP hl hQ d
  have htri : ∀ S : Finset (Crossing P), IsDecomposition hn hP S →
      CarrierUniform (by omega) hQ (τ.supportY S) (τ.tri S) :=
    fun S hS => τ.carrierUniform_tri S hS (-turn P j) hτne ht1 ht2 ht3
  -- coefficients: rotations agree (limit argument), polynomials agree (record bridge)
  have hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q' : Component hn hP S),
      cornerCoefficient (by omega) hQ (τ.supportY S) (τ.residual S q')
        ((τ.isDecomposition_supportY_iff S).mpr hS) = cornerCoefficient hn hP S q' hS :=
    fun S hS q' => τ.cornerCoefficient_residual S hS q'
      (hrot S hS q' ε hε (lt_of_lt_of_le hlt (min_le_right _ _)) hQ d)
      (sftd_loopTransport_homfly hn hP hl hQ d S hS q')
  -- the state sum and the left-turn count
  have hC := τ.cornerStateSum_transport hCV hturn htri hcoef
  have hℓ := τ.leftTurns_transport d.hvert
  rw [ht1, ht2] at hℓ
  rw [hC, sftd_sign_arith _ _ _ _ hℓ]
  exact sftd_neg_sign_pow (turn P j) (sft_turn_ne_zero hn hP j) _

/-! ### Assembly of row 112 (PROVED from the three sector leaves): the attachment signs are `±1`
(admissibility), `τ = ±1` (genericity), and the three sectors exhaust the sign patterns with the
multipliers `−τ`, `0`, `τ` — "The three sector multipliers are exactly `(χ₋ + χ₊)/2`". -/

theorem sft_signType_neg_ne_zero {σ : SignType} (h : σ ≠ 0) : -σ ≠ 0 := by
  revert h; cases σ <;> decide

omit [NeZero n] in
theorem sft_attachment_ne_zero {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) :
    softAttachmentMinus P j q ≠ 0 ∧ softAttachmentPlus P j q ≠ 0 := by
  unfold softAttachmentMinus softAttachmentPlus
  exact ⟨sft_signType_neg_ne_zero (sign_ne_zero.mpr hq.1),
    sft_signType_neg_ne_zero (sign_ne_zero.mpr hq.2.1)⟩

theorem sft_signType_cases {σ : SignType} (h : σ ≠ 0) : σ = 1 ∨ σ = -1 := by
  rcases SignType.trichotomy σ with h1 | h1 | h1
  · exact Or.inr h1
  · exact absurd h1 h
  · exact Or.inl h1

/-- **Row 112 from row 105** (the printed dependency: thm:C-soft ← lem:corner-values). -/
theorem thm_C_soft_of_cornerValues (hCV : CornerValuesData) : CSoftData := by
  refine ⟨?_⟩
  intro n _ hn P hP j q hq
  have hτ := sft_signType_cases (sft_turn_ne_zero hn hP j)
  have hχm := sft_signType_cases (sft_attachment_ne_zero hq).1
  have hχp := sft_signType_cases (sft_attachment_ne_zero hq).2
  -- the same-sign, mixed and loop sectors, with their multipliers
  have hsame : softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
    intro hs
    obtain ⟨ε₁, hε₁, hval⟩ := sft_same_sign hn hP j q hq hs
    refine ⟨ε₁, hε₁, fun ε hε0 hε1 hQ => ?_⟩
    rw [hval ε hε0 hε1 hQ]
    unfold softAmplitudeMultiplier
    rw [hs.1, hs.2]
    push_cast
    ring
  have hmixed : softAttachmentMinus P j q ≠ softAttachmentPlus P j q →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
    intro hne
    obtain ⟨ε₁, hε₁, hval⟩ := sft_mixed hn hP j q hq hne
    refine ⟨ε₁, hε₁, fun ε hε0 hε1 hQ => ?_⟩
    rw [hval ε hε0 hε1 hQ]
    unfold softAmplitudeMultiplier
    rcases hχm with hm | hm <;> rcases hχp with hp | hp
    · exact absurd (hm.trans hp.symm) hne
    · rw [hm, hp]; norm_num
    · rw [hm, hp]; norm_num
    · exact absurd (hm.trans hp.symm) hne
  have hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
    intro hl
    obtain ⟨ε₁, hε₁, hval⟩ := sft_loop hCV hn hP j q hq hl
    refine ⟨ε₁, hε₁, fun ε hε0 hε1 hQ => ?_⟩
    rw [hval ε hε0 hε1 hQ]
    unfold softAmplitudeMultiplier
    rw [hl.1, hl.2]
    push_cast
    ring
  -- the sectors exhaust the sign patterns
  by_cases hne : softAttachmentMinus P j q = softAttachmentPlus P j q
  · rcases hτ with ht | ht <;> rcases hχm with hm | hm
    · exact hloop ⟨hm.trans ht.symm, (hne.symm.trans hm).trans ht.symm⟩
    · exact hsame ⟨by rw [hm, ht]; try decide, by rw [← hne, hm, ht]; try decide⟩
    · exact hsame ⟨by rw [hm, ht]; try decide, by rw [← hne, hm, ht]; try decide⟩
    · exact hloop ⟨hm.trans ht.symm, (hne.symm.trans hm).trans ht.symm⟩
  · exact hmixed hne

/-- **Row 112, conditional on the floor** (library material; the row theorem `SM.thm_C_soft :=
thm_C_soft_of_floor SM.thm_floor` once row 100 lands). -/
theorem thm_C_soft_of_floor (hF : FloorTheoremData) : CSoftData :=
  thm_C_soft_of_cornerValues (corner_values_of_floor hF)

end Soft

/-! ## §6 The row theorems (UNCONDITIONAL statements; `sorry` until row 100 lands).  Once the floor lane's
`SM.thm_floor : FloorTheoremData` is accepted, each body is the one-liner named in its docstring; until
then the rows stay UNMAPPED (D-F11/D-F14) and these four declarations are not ported. -/

/-- Row 103 cb:singleton (proposed name).  Body once row 100 lands: `cb_singleton_of_floor thm_floor`. -/
theorem cb_singleton : CbSingletonData := by
  exact cb_singleton_of_floor SM.thm_floor

/-- Row 105 lem:corner-values (proposed name).  Body once row 100 lands:
`corner_values_of_floor thm_floor`.  Clause (i) is unconditional NOW (`corner_values_i`). -/
theorem corner_values : CornerValuesData := by
  exact corner_values_of_floor SM.thm_floor

/-- Row 110 thm:C-S7 (FIXED target name, axiom-policy.json).  Body once row 100 lands:
`thm_C_S7_of_floor thm_floor`. -/
theorem thm_C_S7 : CS7Data := by
  exact thm_C_S7_of_floor SM.thm_floor

/-- Row 112 thm:C-soft (FIXED target name, axiom-policy.json).  Body once row 100 lands:
`thm_C_soft_of_floor thm_floor`. -/
theorem thm_C_soft : CSoftData := by
  exact thm_C_soft_of_floor SM.thm_floor

/-! ## §7 Consumer shape check (thm:comparison, thm:uniqueness (c), (e)).
`UniquenessHypotheses.vertex_edge` / `.soft` (SM/Uniqueness.lean:57-76) have literally the shapes of
`CS7Data.vertex_edge_law` / `CSoftData.soft_theorem` with `F n Q := C` read on the polygon quotient
`GenericPolygon n`; the descent of `cornerStateSum` to the quotient is the accepted
`cornerStateSum_genericShift` (SM/CChamber.lean) — thm:comparison's business (FR-CC-13). -/
example (hF : FloorTheoremData) : CS7Data ∧ CSoftData ∧ CbSingletonData ∧ CornerValuesData :=
  ⟨thm_C_S7_of_floor hF, thm_C_soft_of_floor hF, cb_singleton_of_floor hF, corner_values_of_floor hF⟩

end


/-! ROW-CLOSURE PROBE -/
#print axioms SM.thm_floor
#print axioms cb_singleton
#print axioms corner_values
#print axioms thm_C_S7
#print axioms thm_C_soft
#print axioms cb_singleton_of_floor
#print axioms corner_values_of_floor
#print axioms corner_values_of_singleton
#print axioms thm_C_soft_of_cornerValues
#print axioms thm_C_soft_of_floor
#print axioms thm_C_S7_of_floor
#print axioms s7_sliding_law_at
#print axioms CS7Data.sliding
#print axioms CS7Data.bigon
example : CbSingletonData ∧ CornerValuesData ∧ CSoftData := ⟨cb_singleton, corner_values, thm_C_soft⟩

end SM
