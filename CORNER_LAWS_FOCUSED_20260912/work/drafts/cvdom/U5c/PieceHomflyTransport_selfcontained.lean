import CV.ChamberInvII

/-! # CV/PieceHomflyTransport — the piece polynomials are carried along a chamber
(CV-DOM unit U5c; closes the one open lemma of CV/ChamberInvII.lean)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor (CV-DOM decision,
work/drafts/cvdom/DECISION_FINAL.md §5 row U5a, §6 item 6; U5a report §6 "recommended route").
Intended home `work/lean/CV/PieceHomflyTransport.lean`. Nothing under work/lean was written.

## What is proved

`CV.pieceHomflyTransported hn hP hQ h : PieceHomflyTransported hn hP hQ h` for every pair of CV-generic
polygons `P`, `Q` of one CV chamber: the piece polynomial `P_H = pieceHomfly` (CV:def:piecediagram,
`homfly` of the positive lift of the carrier `q_H` of `S ∪ K_H` carrying the piece `H`) is carried by the
piece bijection `pieceEquiv` of the chamber transport. With it, `CV.X1_eq_of_mem_chamber_of_pieceHomfly`
(CV/ChamberInvII.lean) gives CV:prop:chamberinv (ii).

## Route (U5a report §6, item 2)

`pieceSupport` is a `Classical.choose`, so the support chosen at `Q` need not be the transport of the
support chosen at `P`. The proof therefore has two steps.

1. **Choice independence at one polygon** (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`): on a
   fixed polygon `Q` (tier 1, `hG : CarrierGeometry Q`), two carriers `q₁`, `q₂` of two independent supports
   `T₁`, `T₂` with the same retained crossings `geoCarrierCrossings T₁ q₁ = geoCarrierCrossings T₂ q₂` have
   positive lifts with the same HOMFLY polynomial. Proof: a record isomorphism (CV:def:record's (a)–(d),
   `CV.recordIsoOfData`) between the two lifts, then the accepted CV:ax:gausscode replacement
   `CV.gausscode_polynomial`. The occurrences of either lift are identified with the visits of the retained
   crossings (`liftVisitEquiv`: a crossing of the lift is a retained crossing, U4 `geoCarrierCrossingEquiv`;
   its strand is the block of the corner polygon through the visit, `visitBlock`, by `geo_mark_block` and
   the shadow's `no_triple`). Under this identification
   * the pairing is the parent's `visitTwin` (`twin_liftVisit`),
   * the over bit is the sign of `det` of the two parent edges at the visit (`isOver_liftVisit_iff`; the
     corner-polygon edges are positive multiples of the parent edges, `geoCornerPolygon_edge_smul`),
   * the signs are all `+1` (`geoPositiveLift_sign`),
   * **the cyclic order along the corner polygon is the parent's cyclic order** of the visits
     (`visitBetween_liftVisit_iff`): the traversal coordinate of an occurrence on the corner polygon is the
     *block coordinate* `markCoord` of its mark — block index plus the affine position inside the block —
     which is strictly increasing along the `ρ_T`-orbit of the carrier from its corner `c₀`
     (`markCoord_lt_succ`, from the block structure `geoCornerPolygon_block`); by lem:carrierword
     (`TracedSuccessor`) that orbit is the carrier's mark list in the parent's traversal order, so both
     coordinates induce one cyclic order (`cycBetween_markCoord_iff`).
2. **Transport along the chamber**: at `Q`, the carrier of `S' ∪ K'` (the choice at `Q`) and the transported
   carrier of `S' ∪ tK` (the choice at `P`, carried by `geoMarkTransport_of_mem_chamber`) have the same
   retained crossings (`pieceCarrier_geoCarrierCrossings`, `pieceLabels_eq`,
   `geoCarrierCrossings_eq_of_mem_chamber`), so step 1 applies; and the transported carrier's lift has the
   HOMFLY polynomial of the lift at `P` by U5a's `homfly_geoPositiveLift_eq_of_mem_chamber` (lit:homfly's
   planar clause along the chamber path).

Everything is on the printed binders (`hP hQ : CV.Generic`, `h : Q ∈ CV.chamber P`); tier 1 for the shadow
geometry (ruling R4), tier 0 for the marks. Axioms: standard plus `SM.lit_homfly` where `homfly` occurs. -/

namespace CV

open SM SM.Carrier SM.GeoCarrier SM.Link

attribute [local instance] Classical.propDecidable

/-! ## 0. Cyclic betweenness under strictly monotone maps and rotations -/

section CycHelpers

/-- Strict oriented betweenness is invariant under a strictly increasing reparametrisation. -/
theorem cycBetween_map_of_strictMonoOn {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Set.Iio N))
    {a b c : ℕ} (ha : a < N) (hb : b < N) (hc : c < N) :
    cycBetween (f a) (f b) (f c) ↔ cycBetween (a : ℝ) (b : ℝ) (c : ℝ) := by
  unfold cycBetween
  rw [hf.lt_iff_lt ha hb, hf.lt_iff_lt hb hc, hf.lt_iff_lt hc ha]
  simp only [Nat.cast_lt]

/-- Strict oriented betweenness of three positions on a circle of `N` positions is invariant under
rotation by `s`. -/
theorem cycBetween_add_mod {N s a b c : ℕ} (hs : s < N) (ha : a < N) (hb : b < N) (hc : c < N) :
    cycBetween (((a + s) % N : ℕ) : ℝ) (((b + s) % N : ℕ) : ℝ) (((c + s) % N : ℕ) : ℝ) ↔
      cycBetween (a : ℝ) (b : ℝ) (c : ℝ) := by
  unfold cycBetween
  simp only [Nat.cast_lt]
  have hN : 0 < N := by omega
  have ma := Nat.mod_lt (a + s) hN
  have mb := Nat.mod_lt (b + s) hN
  have mc := Nat.mod_lt (c + s) hN
  rcases add_mod_cases N a s ha hs with h1 | h1 <;> rcases add_mod_cases N b s hb hs with h2 | h2 <;>
    rcases add_mod_cases N c s hc hs with h3 | h3 <;> omega

/-- A function increasing at every step below `N` is strictly monotone on `[0, N)`. -/
theorem strictMonoOn_Iio_of_lt_succ {f : ℕ → ℝ} {N : ℕ} (h : ∀ j, j + 1 < N → f j < f (j + 1)) :
    StrictMonoOn f (Set.Iio N) := by
  have key : ∀ a d, a + d + 1 < N → f a < f (a + d + 1) := by
    intro a d
    induction d with
    | zero => intro hd; simpa using h a hd
    | succ d ih =>
      intro hd
      have h1 : a + d + 1 < N := by omega
      have h2 := h (a + d + 1) (by omega)
      have : a + (d + 1) + 1 = a + d + 1 + 1 := by omega
      rw [this]
      exact (ih h1).trans h2
  intro a _ b hb hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  exact key a d hb

end CycHelpers

/-! ## 1. Block coordinates of the marks of a carrier (tier 1)

For a carrier `q` of an independent set `T` on a polygon `Q` with `hG : CarrierGeometry Q`: the corner
polygon `C = geoCornerPolygon` has one edge per corner `c_k`; its edge `k` runs along the original edge
`blockEdge k` of `Q` from the parameter `blockStart k` over a length `blockScale k` (in units of that edge,
U2b `geoCornerPolygon_edge_smul`), and the marks of the block of `c_k` are `ρ_T^r c_k`, `r < blockLen k`,
unselected visits on that edge with increasing parameters (`geoCornerPolygon_block`). The block coordinate
`markCoord m = k + (p_m − blockStart k) / blockScale k` of an owned mark `m = ρ_T^r c_k` is its traversal
coordinate on `C`. -/

namespace PieceHomfly

variable {n : ℕ} [NeZero n] {Q : LabelledTuple n}

section Blocks

variable (hn : 3 ≤ n) (hG : CarrierGeometry Q) {T : Finset (Crossing Q)} (hT : GeoIndependent hG.cg T)
  (q : GeoComponent hG.cg T)

/-- The original edge carrying the block (= the edge `k` of the corner polygon) of the corner `c_k`. -/
noncomputable def blockEdge (k : ZMod (geoCornerCount hG.cg T q)) : ZMod n :=
  (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).1

/-- The parameter of the corner `c_k` on `blockEdge k`. -/
noncomputable def blockStart (k : ZMod (geoCornerCount hG.cg T q)) : ℝ :=
  (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.val

/-- The length of the edge `k` of the corner polygon in units of `edge Q (blockEdge k)`. -/
noncomputable def blockScale (k : ZMod (geoCornerCount hG.cg T q)) : ℝ :=
  Classical.choose (geoCornerPolygon_edge_smul hn hG.cg hT q k)

theorem blockScale_pos (k : ZMod (geoCornerCount hG.cg T q)) : 0 < blockScale hn hG hT q k :=
  (Classical.choose_spec (geoCornerPolygon_edge_smul hn hG.cg hT q k)).1

theorem edge_geoCornerPolygon_eq (k : ZMod (geoCornerCount hG.cg T q)) :
    edge (geoCornerPolygon hG.cg T q) k = blockScale hn hG hT q k • edge Q (blockEdge hG q k) :=
  (Classical.choose_spec (geoCornerPolygon_edge_smul hn hG.cg hT q k)).2

theorem edge_blockEdge_ne_zero (k : ZMod (geoCornerCount hG.cg T q)) : edge Q (blockEdge hG q k) ≠ 0 :=
  hG.cg.1 _

/-- The corner `c_k` as a point of its block's edge. -/
theorem geoCornerPolygon_eq_edgePoint (k : ZMod (geoCornerCount hG.cg T q)) :
    geoCornerPolygon hG.cg T q k = edgePoint Q (blockEdge hG q k) (blockStart hG q k) :=
  geo_evaluation_eq_outSlot hG.cg T _

/-- Points of the edge `k` of the corner polygon, as points of the original edge `blockEdge k`. -/
theorem edgePoint_geoCornerPolygon (k : ZMod (geoCornerCount hG.cg T q)) (τ : ℝ) :
    edgePoint (geoCornerPolygon hG.cg T q) k τ =
      edgePoint Q (blockEdge hG q k) (blockStart hG q k + τ * blockScale hn hG hT q k) := by
  rw [edgePoint, edge_geoCornerPolygon_eq hn hG hT q k, geoCornerPolygon_eq_edgePoint hG q k]
  apply Prod.ext <;> simp [edgePoint, smul_eq_mul] <;> ring

include hn hT in
/-- The block structure of `geoCornerPolygon_block`, clauses 1–5, without the `let`s. -/
theorem block_data (k : ZMod (geoCornerCount hG.cg T q)) :
    ∃ m : ℕ, 1 ≤ m ∧
      (geoSmoothingSuccessor hG.cg T ^ m) (geoCornerMark hG.cg T q k) = geoCornerMark hG.cg T q (k + 1) ∧
      (∀ r, 1 ≤ r → r < m → ∃ v : Visit Q,
        (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k) = Sum.inr v ∧ v.1 ∉ T ∧
          v.2.val = blockEdge hG q k) ∧
      (∀ r < m, (geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k))).1 =
        blockEdge hG q k) ∧
      (∀ r, r + 1 < m →
        (geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k))).2.val <
          (geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ (r + 1)) (geoCornerMark hG.cg T q k))).2.val) := by
  obtain ⟨m, h1, h2, h3, h4, h5, -, -, -⟩ := geoCornerPolygon_block hn hG.cg hT q k
  exact ⟨m, h1, h2, h3, h4, h5⟩

/-- The number of `ρ_T`-steps from `c_k` to `c_{k+1}`. -/
noncomputable def blockLen (k : ZMod (geoCornerCount hG.cg T q)) : ℕ :=
  Classical.choose (block_data hn hG hT q k)

theorem blockLen_spec (k : ZMod (geoCornerCount hG.cg T q)) :
    1 ≤ blockLen hn hG hT q k ∧
      (geoSmoothingSuccessor hG.cg T ^ blockLen hn hG hT q k) (geoCornerMark hG.cg T q k) =
        geoCornerMark hG.cg T q (k + 1) ∧
      (∀ r, 1 ≤ r → r < blockLen hn hG hT q k → ∃ v : Visit Q,
        (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k) = Sum.inr v ∧ v.1 ∉ T ∧
          v.2.val = blockEdge hG q k) ∧
      (∀ r < blockLen hn hG hT q k,
        (geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k))).1 =
          blockEdge hG q k) ∧
      (∀ r, r + 1 < blockLen hn hG hT q k →
        (geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k))).2.val <
          (geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ (r + 1)) (geoCornerMark hG.cg T q k))).2.val) :=
  Classical.choose_spec (block_data hn hG hT q k)

/-- A block-interior representation `ρ_T^r c_k` has `r < blockLen k` (the corner `c_{k+1}` is reached
only at step `blockLen k`). -/
theorem lt_blockLen_of_blockInterior {k : ZMod (geoCornerCount hG.cg T q)} {r : ℕ}
    (hb : GeoBlockInterior hG.cg T q k r) : r < blockLen hn hG hT q k := by
  by_contra hle
  obtain ⟨h1, h2, -, -, -⟩ := blockLen_spec hn hG hT q k
  apply hb.not_trueCorner hG.cg T q (blockLen hn hG hT q k) h1 (not_lt.mp hle)
  rw [h2]
  exact isTrueCorner_geoCornerMark hG.cg T q (k + 1)

include hn hT in
/-- Block marks lie on the block's edge (their outgoing slot is on `blockEdge k`). -/
theorem outSlot_edge_of_blockInterior {k : ZMod (geoCornerCount hG.cg T q)} {r : ℕ}
    (hb : GeoBlockInterior hG.cg T q k r) :
    (geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k))).1 =
      blockEdge hG q k :=
  (blockLen_spec hn hG hT q k).2.2.2.1 r (lt_blockLen_of_blockInterior hn hG hT q hb)

/-- The block of an owned mark (the corner index of `geo_mark_block`). -/
noncomputable def markBlock (m : Mark Q) (hm : geoOwner hG.cg T m = q) : ZMod (geoCornerCount hG.cg T q) :=
  Classical.choose (geo_mark_block hn hG.cg hT q m hm)

/-- The position of an owned mark inside its block. -/
noncomputable def markStep (m : Mark Q) (hm : geoOwner hG.cg T m = q) : ℕ :=
  Classical.choose (Classical.choose_spec (geo_mark_block hn hG.cg hT q m hm))

theorem markBlock_spec (m : Mark Q) (hm : geoOwner hG.cg T m = q) :
    (geoSmoothingSuccessor hG.cg T ^ markStep hn hG hT q m hm)
        (geoCornerMark hG.cg T q (markBlock hn hG hT q m hm)) = m ∧
      GeoBlockInterior hG.cg T q (markBlock hn hG hT q m hm) (markStep hn hG hT q m hm) ∧
      traversalEvaluation Q (geoMarkPosition hG.cg m) ∈
        edgeSegment (geoCornerPolygon hG.cg T q) (markBlock hn hG hT q m hm) :=
  Classical.choose_spec (Classical.choose_spec (geo_mark_block hn hG.cg hT q m hm))

/-- Any block-interior representation of an owned mark is the chosen one. -/
theorem markBlock_eq {m : Mark Q} (hm : geoOwner hG.cg T m = q) {k : ZMod (geoCornerCount hG.cg T q)}
    {r : ℕ} (hr : (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k) = m)
    (hb : GeoBlockInterior hG.cg T q k r) :
    markBlock hn hG hT q m hm = k ∧ markStep hn hG hT q m hm = r :=
  geo_block_mark_eq hG.cg T q (markBlock_spec hn hG hT q m hm).2.1 hb
    ((markBlock_spec hn hG hT q m hm).1.trans hr.symm)

/-- **The block coordinate of a mark**: block index plus affine position in the block (`0` off `q`). -/
noncomputable def markCoord (m : Mark Q) : ℝ :=
  if hm : geoOwner hG.cg T m = q then
    ((markBlock hn hG hT q m hm).val : ℝ) +
      ((geoOutSlot hG.cg T m).2.val - blockStart hG q (markBlock hn hG hT q m hm)) /
        blockScale hn hG hT q (markBlock hn hG hT q m hm)
  else 0

theorem markCoord_of_block {m : Mark Q} (hm : geoOwner hG.cg T m = q) {k : ZMod (geoCornerCount hG.cg T q)}
    {r : ℕ} (hr : (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k) = m)
    (hb : GeoBlockInterior hG.cg T q k r) :
    markCoord hn hG hT q m =
      (k.val : ℝ) + ((geoOutSlot hG.cg T m).2.val - blockStart hG q k) / blockScale hn hG hT q k := by
  unfold markCoord
  rw [dite_eq_left hm, (markBlock_eq hn hG hT q hm hr hb).1]

/-- The coordinate of the corner `c_k` is `k`. -/
theorem markCoord_geoCornerMark (k : ZMod (geoCornerCount hG.cg T q)) :
    markCoord hn hG hT q (geoCornerMark hG.cg T q k) = (k.val : ℝ) := by
  rw [markCoord_of_block hn hG hT q (geoOwner_geoCornerMark hG.cg T q k) (r := 0)
    (by rw [pow_zero, Equiv.Perm.one_apply]) (fun i h1 h0 => absurd (h1.trans h0) (by omega))]
  unfold blockStart
  rw [sub_self, zero_div, add_zero]

/-- The successor of a block-interior mark that is not the corner `c_{k+1}` stays in the block. -/
theorem blockInterior_succ {k : ZMod (geoCornerCount hG.cg T q)} {r : ℕ}
    (hb : GeoBlockInterior hG.cg T q k r) (hlt : r + 1 < blockLen hn hG hT q k) :
    GeoBlockInterior hG.cg T q k (r + 1) := by
  intro i h1 hi
  rcases Nat.lt_or_ge i (r + 1) with h | h
  · exact hb i h1 (by omega)
  · have hi' : i = r + 1 := by omega
    subst hi'
    exact (blockLen_spec hn hG hT q k).2.2.1 (r + 1) h1 hlt

/-- The end corner of a block as a point of the block's edge. -/
theorem geoCornerPolygon_add_one_eq (k : ZMod (geoCornerCount hG.cg T q)) :
    geoCornerPolygon hG.cg T q (k + 1) =
      edgePoint Q (blockEdge hG q k) (blockStart hG q k + blockScale hn hG hT q k) := by
  have h := edgePoint_geoCornerPolygon hn hG hT q k 1
  rw [edgePoint_one, one_mul] at h
  exact h

/-- **The block coordinate increases along `ρ_T`** except at the return to the corner `c₀`. -/
theorem markCoord_lt_succ {m : Mark Q} (hm : geoOwner hG.cg T m = q)
    (hne : geoSmoothingSuccessor hG.cg T m ≠ geoCornerMark hG.cg T q 0) :
    markCoord hn hG hT q m < markCoord hn hG hT q (geoSmoothingSuccessor hG.cg T m) := by
  obtain ⟨hr, hb, -⟩ := markBlock_spec hn hG hT q m hm
  set k := markBlock hn hG hT q m hm
  set r := markStep hn hG hT q m hm
  have hrl : r < blockLen hn hG hT q k := lt_blockLen_of_blockInterior hn hG hT q hb
  have hsucc : geoSmoothingSuccessor hG.cg T m =
      (geoSmoothingSuccessor hG.cg T ^ (r + 1)) (geoCornerMark hG.cg T q k) := by
    rw [← hr, pow_succ', Equiv.Perm.mul_apply]
  have hm' : geoOwner hG.cg T (geoSmoothingSuccessor hG.cg T m) = q := by
    rw [geoOwner_successor]; exact hm
  have hpos := blockScale_pos hn hG hT q k
  rw [markCoord_of_block hn hG hT q hm hr hb]
  rcases Nat.lt_or_ge (r + 1) (blockLen hn hG hT q k) with hlt | hge
  · -- the successor stays in the block: its parameter is larger
    have hb' := blockInterior_succ hn hG hT q hb hlt
    rw [markCoord_of_block hn hG hT q hm' hsucc.symm hb']
    have h5 := (blockLen_spec hn hG hT q k).2.2.2.2 r hlt
    rw [← hsucc, hr] at h5
    have hfrac : ((geoOutSlot hG.cg T m).2.val - blockStart hG q k) / blockScale hn hG hT q k <
        ((geoOutSlot hG.cg T (geoSmoothingSuccessor hG.cg T m)).2.val - blockStart hG q k) /
          blockScale hn hG hT q k :=
      (div_lt_div_iff_of_pos_right hpos).mpr (sub_lt_sub_right h5 _)
    linarith
  · -- the successor is the corner `c_{k+1}`: one full step
    have hreq : r + 1 = blockLen hn hG hT q k := by omega
    have hcorner : geoSmoothingSuccessor hG.cg T m = geoCornerMark hG.cg T q (k + 1) := by
      rw [hsucc, hreq]
      exact (blockLen_spec hn hG hT q k).2.1
    rw [hcorner, markCoord_geoCornerMark]
    -- `k + 1 ≠ 0`, so `(k + 1).val = k.val + 1`
    have hk1 : k + 1 ≠ 0 := by
      intro h0
      apply hne
      rw [hcorner, h0]
    have hval : (k + 1).val = k.val + 1 := by
      have : Fact (1 < geoCornerCount hG.cg T q) := ⟨by have := three_le_geoCornerCount hn hG hT q; omega⟩
      rw [ZMod.val_add, ZMod.val_one]
      apply Nat.mod_eq_of_lt
      have hlt := ZMod.val_lt k
      rcases Nat.lt_or_ge (k.val + 1) (geoCornerCount hG.cg T q) with h | h
      · exact h
      · exfalso
        apply hk1
        rw [← ZMod.val_eq_zero, ZMod.val_add, ZMod.val_one]
        have : k.val + 1 = geoCornerCount hG.cg T q := by omega
        rw [this, Nat.mod_self]
    rw [hval, Nat.cast_add, Nat.cast_one]
    -- the parameter of `m` is below the end of the block
    obtain ⟨t, hmt, -, hend⟩ := geo_subsegment_data hn hG.cg T m
    have hedge : (geoOutSlot hG.cg T m).1 = blockEdge hG q k := by
      rw [← hr]; exact outSlot_edge_of_blockInterior hn hG hT q hb
    rw [hedge, hcorner, ← geoCornerPolygon_apply, geoCornerPolygon_add_one_eq hn hG hT q k] at hend
    have ht : t = blockStart hG q k + blockScale hn hG hT q k :=
      edgePoint_injective (edge_blockEdge_ne_zero hG q k) hend.symm
    have hfrac : ((geoOutSlot hG.cg T m).2.val - blockStart hG q k) / blockScale hn hG hT q k < 1 := by
      rw [div_lt_one hpos]
      linarith
    linarith

end Blocks

/-! ## 2. The orbit of the carrier and the two cyclic orders

lem:carrierword (`TracedSuccessor`, U1b): `ρ_T` on the marks of `q` is the cyclic successor of the mark
list `geoComponentMarkList` (the owned marks in the parent's traversal order). Along the orbit from the
corner `c₀` the block coordinate is strictly increasing (`markCoord_lt_succ`), so the cyclic order it
induces is the orbit order, which is the rotation of the list order, which is the parent's key order. -/

section Orbit

variable (hn : 3 ≤ n) (hG : CarrierGeometry Q) {T : Finset (Crossing Q)} (hT : GeoIndependent hG.cg T)
  (q : GeoComponent hG.cg T)

theorem markList_length_pos : 0 < (geoComponentMarkList hG.cg T q).length :=
  geoComponentMarkList_length_pos hG.cg T q

/-- The marks of `q` enumerated cyclically in the inherited order (indices modulo the count). -/
noncomputable def mk (j : ℕ) : Mark Q :=
  (geoComponentMarkList hG.cg T q)[j % (geoComponentMarkList hG.cg T q).length]'
    (Nat.mod_lt _ (markList_length_pos hG q))

theorem mk_of_lt {j : ℕ} (hj : j < (geoComponentMarkList hG.cg T q).length) :
    mk hG q j = (geoComponentMarkList hG.cg T q)[j]'hj := by
  simp only [mk, Nat.mod_eq_of_lt hj]

theorem owner_mk (j : ℕ) : geoOwner hG.cg T (mk hG q j) = q :=
  (mem_geoComponentMarkList hG.cg T q _).mp (List.getElem_mem _)

theorem mk_inj_iff (a b : ℕ) :
    mk hG q a = mk hG q b ↔
      a % (geoComponentMarkList hG.cg T q).length = b % (geoComponentMarkList hG.cg T q).length := by
  unfold mk
  exact (geoComponentMarkList_nodup hG.cg T q).getElem_inj_iff

theorem exists_mk (m : Mark Q) (hm : geoOwner hG.cg T m = q) :
    ∃ i, i < (geoComponentMarkList hG.cg T q).length ∧ mk hG q i = m := by
  obtain ⟨i, hi, hm'⟩ := List.getElem_of_mem ((mem_geoComponentMarkList hG.cg T q m).mpr hm)
  exact ⟨i, hi, by rw [mk_of_lt hG q hi, hm']⟩

include hn hT in
/-- `ρ_T` advances the enumeration by one (lem:carrierword, `TracedSuccessor`). -/
theorem succ_mk (j : ℕ) : geoSmoothingSuccessor hG.cg T (mk hG q j) = mk hG q (j + 1) := by
  have htr := geoTracedSuccessor_of_independent hn hG.cg hT q
    ⟨j % (geoComponentMarkList hG.cg T q).length, Nat.mod_lt _ (markList_length_pos hG q)⟩
  simp only at htr
  unfold mk
  rw [htr]
  simp only [Nat.mod_add_mod]

include hn hT in
theorem pow_mk (j a : ℕ) :
    (geoSmoothingSuccessor hG.cg T ^ j) (mk hG q a) = mk hG q (a + j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, succ_mk hn hG hT q, Nat.add_assoc]

/-- The list index of the corner `c₀`. -/
noncomputable def cornerIndex : ℕ :=
  Classical.choose (exists_mk hG q (geoCornerMark hG.cg T q 0) (geoOwner_geoCornerMark hG.cg T q 0))

theorem cornerIndex_lt : cornerIndex hG q < (geoComponentMarkList hG.cg T q).length :=
  (Classical.choose_spec (exists_mk hG q (geoCornerMark hG.cg T q 0) (geoOwner_geoCornerMark hG.cg T q 0))).1

theorem mk_cornerIndex : mk hG q (cornerIndex hG q) = geoCornerMark hG.cg T q 0 :=
  (Classical.choose_spec (exists_mk hG q (geoCornerMark hG.cg T q 0) (geoOwner_geoCornerMark hG.cg T q 0))).2

include hn hT in
/-- Along the orbit from `c₀` the block coordinate increases at every step before the return. -/
theorem markCoord_mk_lt_succ (j : ℕ) (hj : j + 1 < (geoComponentMarkList hG.cg T q).length) :
    markCoord hn hG hT q (mk hG q (cornerIndex hG q + j)) <
      markCoord hn hG hT q (mk hG q (cornerIndex hG q + (j + 1))) := by
  rw [← Nat.add_assoc, ← succ_mk hn hG hT q]
  apply markCoord_lt_succ hn hG hT q (owner_mk hG q _)
  rw [succ_mk hn hG hT q, ← mk_cornerIndex hG q]
  intro h
  rw [mk_inj_iff] at h
  have hi := cornerIndex_lt hG q
  rw [Nat.mod_eq_of_lt hi, Nat.add_assoc] at h
  rcases add_mod_cases _ (cornerIndex hG q) (j + 1) hi hj with h' | h' <;> omega

include hn hT in
theorem strictMonoOn_markCoord_mk :
    StrictMonoOn (fun j => markCoord hn hG hT q (mk hG q (cornerIndex hG q + j)))
      (Set.Iio (geoComponentMarkList hG.cg T q).length) :=
  strictMonoOn_Iio_of_lt_succ fun j hj => markCoord_mk_lt_succ hn hG hT q j hj

/-- The orbit position from `c₀` of the mark at list index `i`. -/
noncomputable def orbitPos (i : ℕ) : ℕ :=
  (i + ((geoComponentMarkList hG.cg T q).length - cornerIndex hG q) %
      (geoComponentMarkList hG.cg T q).length) % (geoComponentMarkList hG.cg T q).length

theorem orbitPos_lt (i : ℕ) : orbitPos hG q i < (geoComponentMarkList hG.cg T q).length :=
  Nat.mod_lt _ (markList_length_pos hG q)

theorem mk_add_orbitPos (i : ℕ) : mk hG q (cornerIndex hG q + orbitPos hG q i) = mk hG q i := by
  rw [mk_inj_iff]
  unfold orbitPos
  rw [Nat.add_mod_mod, ← Nat.add_assoc, Nat.add_mod_mod]
  have h : cornerIndex hG q + i + ((geoComponentMarkList hG.cg T q).length - cornerIndex hG q) =
      i + (geoComponentMarkList hG.cg T q).length := by
    have := cornerIndex_lt hG q
    omega
  rw [h, Nat.add_mod_right]

/-- The mark list is sorted by the parent's traversal key (it is a sublist of `geoMarkList`). -/
theorem markList_pairwise :
    (geoComponentMarkList hG.cg T q).Pairwise (fun a b => geoMarkKey hG.cg a ≤ geoMarkKey hG.cg b) :=
  (geoMarkList_sorted hG.cg).sublist List.filter_sublist

theorem key_mk_lt {i j : ℕ} (hi : i < (geoComponentMarkList hG.cg T q).length)
    (hj : j < (geoComponentMarkList hG.cg T q).length) (hij : i < j) :
    geoMarkKey hG.cg (mk hG q i) < geoMarkKey hG.cg (mk hG q j) := by
  rw [mk_of_lt hG q hi, mk_of_lt hG q hj]
  have hle := List.pairwise_iff_getElem.mp (markList_pairwise hG q) i j hi hj hij
  refine lt_of_le_of_ne hle fun heq => ?_
  have h := geoMarkKey_injective hG.cg heq
  rw [(geoComponentMarkList_nodup hG.cg T q).getElem_inj_iff] at h
  omega

theorem strictMonoOn_key_mk :
    StrictMonoOn (fun i => geoMarkKey hG.cg (mk hG q i)) (Set.Iio (geoComponentMarkList hG.cg T q).length) :=
  fun _ hi _ hj hij => key_mk_lt hG q hi hj hij

include hn hT in
/-- **The block coordinate and the parent's traversal key induce the same cyclic order on the marks of
`q`** (the cyclic order of the corner polygon is the inherited cyclic order, lem:carrierword). -/
theorem cycBetween_markCoord_iff {a b c : Mark Q} (ha : geoOwner hG.cg T a = q)
    (hb : geoOwner hG.cg T b = q) (hc : geoOwner hG.cg T c = q) :
    cycBetween (markCoord hn hG hT q a) (markCoord hn hG hT q b) (markCoord hn hG hT q c) ↔
      cycBetween (geoMarkKey hG.cg a) (geoMarkKey hG.cg b) (geoMarkKey hG.cg c) := by
  obtain ⟨ia, hia, rfl⟩ := exists_mk hG q a ha
  obtain ⟨ib, hib, rfl⟩ := exists_mk hG q b hb
  obtain ⟨ic, hic, rfl⟩ := exists_mk hG q c hc
  have hN := markList_length_pos hG q
  have e : ∀ i, markCoord hn hG hT q (mk hG q i) =
      markCoord hn hG hT q (mk hG q (cornerIndex hG q + orbitPos hG q i)) := fun i => by
    rw [mk_add_orbitPos]
  have h1 := cycBetween_map_of_strictMonoOn (strictMonoOn_markCoord_mk hn hG hT q) (orbitPos_lt hG q ia)
    (orbitPos_lt hG q ib) (orbitPos_lt hG q ic)
  have h2 := cycBetween_map_of_strictMonoOn (strictMonoOn_key_mk hG q) hia hib hic
  rw [e ia, e ib, e ic, h1, h2]
  unfold orbitPos
  exact cycBetween_add_mod (Nat.mod_lt _ hN) hia hib hic

end Orbit

/-! ## 3. The occurrences of the positive lift are the visits of the retained crossings

A crossing of the carrier shadow is a retained crossing `c` of `q` (U4 `geoCarrierCrossingEquiv`); an
occurrence is a crossing together with a strand — an edge `k` of the corner polygon through the crossing
point. The two visits `w`, `visitTwin w` of `c` are owned marks lying in two blocks `visitBlock w`,
`visitBlock (visitTwin w)` of two different original edges; their crossing point is interior to both
corner-polygon edges (it is no corner, lem:carriers (iii)), and `no_triple` of the generic shadow forbids
a third edge through it. Hence `w ↦ (crossing of c, edge visitBlock w)` is a bijection `liftVisit`. -/

section Visits

variable (hn : 3 ≤ n) (hG : CarrierGeometry Q) {T : Finset (Crossing Q)} (hT : GeoIndependent hG.cg T)
  (q : GeoComponent hG.cg T)

/-- A visit of a retained crossing is an owned mark. -/
theorem owner_of_mem_geoCarrierCrossings {w : Visit Q} (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    geoOwner hG.cg T (Sum.inr w) = q :=
  ((mem_geoCarrierCrossings hG.cg T q w.1).mp hw).2 w rfl

theorem not_mem_of_mem_geoCarrierCrossings {w : Visit Q} (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    w.1 ∉ T :=
  ((mem_geoCarrierCrossings hG.cg T q w.1).mp hw).1

/-- The twin visit is a visit of the same retained crossing. -/
theorem mem_twin {w : Visit Q} (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (visitTwin w).1 ∈ geoCarrierCrossings hG.cg T q := by
  rw [visitTwin_crossing]; exact hw

/-- The block (edge of the corner polygon) through a visit of a retained crossing. -/
noncomputable def visitBlock (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    ZMod (geoCornerCount hG.cg T q) :=
  markBlock hn hG hT q (Sum.inr w) (owner_of_mem_geoCarrierCrossings hG q hw)

/-- A visit of a retained crossing is not a corner, so it is interior to its block. -/
theorem one_le_markStep_visit (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    1 ≤ markStep hn hG hT q (Sum.inr w) (owner_of_mem_geoCarrierCrossings hG q hw) := by
  by_contra h0
  have h : markStep hn hG hT q (Sum.inr w) (owner_of_mem_geoCarrierCrossings hG q hw) = 0 := by omega
  have hr := (markBlock_spec hn hG hT q (Sum.inr w) (owner_of_mem_geoCarrierCrossings hG q hw)).1
  rw [h, pow_zero, Equiv.Perm.one_apply] at hr
  have hc := isTrueCorner_geoCornerMark hG.cg T q
    (markBlock hn hG hT q (Sum.inr w) (owner_of_mem_geoCarrierCrossings hG q hw))
  rw [hr] at hc
  exact not_mem_of_mem_geoCarrierCrossings hG q hw ((isTrueCorner_visit T w).mp hc)

/-- The visit lies on the original edge of its block. -/
theorem visit_edge_eq_blockEdge (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    w.2.val = blockEdge hG q (visitBlock hn hG hT q w hw) := by
  obtain ⟨hr, hb, -⟩ := markBlock_spec hn hG hT q (Sum.inr w) (owner_of_mem_geoCarrierCrossings hG q hw)
  exact GeoBlockInterior.visit_edge hG.cg T q hb (one_le_markStep_visit hn hG hT q w hw) hr

/-- The crossing point lies on the corner-polygon edge of the block of the visit. -/
theorem crossingPoint_mem_edgeSegment_visitBlock (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    crossingPoint w.1 ∈ edgeSegment (geoCornerPolygon hG.cg T q) (visitBlock hn hG hT q w hw) := by
  have h := (markBlock_spec hn hG hT q (Sum.inr w) (owner_of_mem_geoCarrierCrossings hG q hw)).2.2
  rw [geoMarkPosition_evaluation_visit] at h
  exact h

/-- … and in its interior: the crossing point of a retained crossing is the plane point of no corner
(lem:carriers (iii), `geo_carrier_selfIntersection_not_corner`). -/
theorem crossingPoint_mem_edgeInterior_visitBlock (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    crossingPoint w.1 ∈ edgeInterior (geoCornerPolygon hG.cg T q) (visitBlock hn hG hT q w hw) := by
  obtain ⟨t, h0, h1, ht⟩ := crossingPoint_mem_edgeSegment_visitBlock hn hG hT q w hw
  have hnc := (geo_carrier_selfIntersection_not_corner hG T q hw).2.2.2
  refine ⟨t, lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_, ht⟩
  · rintro rfl
    rw [edgePoint_zero] at ht
    exact hnc _ (isTrueCorner_geoCornerMark hG.cg T q _) ht.symm
  · rintro rfl
    rw [edgePoint_one] at ht
    exact hnc _ (isTrueCorner_geoCornerMark hG.cg T q _) ht.symm

/-- The crossing of the carrier shadow at a retained crossing. -/
noncomputable def shadowCrossing (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoCarrierShadow hn hG hT q).Crossing :=
  (geoCarrierCrossingEquiv hn hG hT q).symm ⟨w.1, hw⟩

theorem shadowCrossing_crossingPoint (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoCarrierShadow hn hG hT q).crossingPoint (shadowCrossing hn hG hT q w hw) = crossingPoint w.1 := by
  unfold shadowCrossing
  rw [← crossingPoint_geoCarrierCrossingEquiv, Equiv.apply_symm_apply]

/-- The strand of the block of a visit is a strand of the shadow crossing (`no_triple`). -/
theorem blockStrand_mem (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (⟨0, visitBlock hn hG hT q w hw⟩ : (geoCarrierShadow hn hG hT q).Strand) ∈
      (shadowCrossing hn hG hT q w hw).val := by
  by_contra hnot
  obtain ⟨s₀, t₀, hx, hna, -⟩ := (shadowCrossing hn hG hT q w hw).2
  have hs₀ : s₀ ∈ (shadowCrossing hn hG hT q w hw).val := by rw [hx]; simp
  have ht₀ : t₀ ∈ (shadowCrossing hn hG hT q w hw).val := by rw [hx]; simp
  have hΓ := geoCarrierShadow_generic hn hG hT q
  apply hΓ.no_triple
  refine ⟨s₀, t₀, ⟨0, visitBlock hn hG hT q w hw⟩, (geoCarrierShadow hn hG hT q).ne_of_not_adjacent hna,
    fun h => hnot (h ▸ ht₀), fun h => hnot (h ▸ hs₀),
    (geoCarrierShadow hn hG hT q).crossingPoint (shadowCrossing hn hG hT q w hw),
    ⟨hΓ.crossingPoint_mem_interior _ hs₀, hΓ.crossingPoint_mem_interior _ ht₀⟩, ?_⟩
  show (geoCarrierShadow hn hG hT q).crossingPoint (shadowCrossing hn hG hT q w hw) ∈
    edgeInterior (geoCornerPolygon hG.cg T q) (visitBlock hn hG hT q w hw)
  rw [shadowCrossing_crossingPoint]
  exact crossingPoint_mem_edgeInterior_visitBlock hn hG hT q w hw

/-- **The occurrence of the positive lift at a visit of a retained crossing.** -/
noncomputable def liftVisit (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoCarrierShadow hn hG hT q).Visit :=
  ⟨shadowCrossing hn hG hT q w hw, ⟨⟨0, visitBlock hn hG hT q w hw⟩, blockStrand_mem hn hG hT q w hw⟩⟩

theorem liftVisit_injective :
    Function.Injective (fun w : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T q} =>
      liftVisit hn hG hT q w.1 w.2) := by
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
  have h1 : shadowCrossing hn hG hT q w hw = shadowCrossing hn hG hT q w' hw' := congrArg Sigma.fst h
  have hc : w.1 = w'.1 :=
    congrArg Subtype.val ((geoCarrierCrossingEquiv hn hG hT q).symm.injective h1)
  have h2 : visitBlock hn hG hT q w hw = visitBlock hn hG hT q w' hw' :=
    congrArg (fun v : (geoCarrierShadow hn hG hT q).Visit => Shadow.singleStrandEquiv _ v.2.val) h
  have he : w.2.val = w'.2.val := by
    rw [visit_edge_eq_blockEdge hn hG hT q w hw, visit_edge_eq_blockEdge hn hG hT q w' hw', h2]
  apply Subtype.ext
  obtain ⟨c, i⟩ := w
  obtain ⟨c', i'⟩ := w'
  change c = c' at hc
  subst hc
  change i.val = i'.val at he
  rw [Subtype.ext he]

theorem liftVisit_surjective :
    Function.Surjective (fun w : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T q} =>
      liftVisit hn hG hT q w.1 w.2) := by
  rintro ⟨x, s, hs⟩
  have hc : (geoToCarrierCrossing hn hG hT q x).1 ∈ geoCarrierCrossings hG.cg T q :=
    (geoToCarrierCrossing hn hG hT q x).2
  obtain ⟨i, -, -⟩ := crossing_visits_exist (geoToCarrierCrossing hn hG hT q x).1
  let w : Visit Q := ⟨(geoToCarrierCrossing hn hG hT q x).1, i⟩
  have hw : w.1 ∈ geoCarrierCrossings hG.cg T q := hc
  have htw : (visitTwin w).1 ∈ geoCarrierCrossings hG.cg T q := mem_twin hG q hw
  have hx : shadowCrossing hn hG hT q w hw = x := by
    unfold shadowCrossing
    rw [Equiv.symm_apply_eq, geoCarrierCrossingEquiv_apply]
  have hΓ := geoCarrierShadow_generic hn hG hT q
  have hpt : (geoCarrierShadow hn hG hT q).crossingPoint x = crossingPoint w.1 := by
    rw [← hx, shadowCrossing_crossingPoint]
  have hs_int := hΓ.crossingPoint_mem_interior x hs
  have hw_int : (geoCarrierShadow hn hG hT q).crossingPoint x ∈
      (geoCarrierShadow hn hG hT q).interior ⟨0, visitBlock hn hG hT q w hw⟩ := by
    rw [hpt]; exact crossingPoint_mem_edgeInterior_visitBlock hn hG hT q w hw
  have htw_int : (geoCarrierShadow hn hG hT q).crossingPoint x ∈
      (geoCarrierShadow hn hG hT q).interior ⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ := by
    rw [hpt]; exact crossingPoint_mem_edgeInterior_visitBlock hn hG hT q (visitTwin w) htw
  have hne : (⟨0, visitBlock hn hG hT q w hw⟩ : (geoCarrierShadow hn hG hT q).Strand) ≠
      ⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ := by
    intro h
    have hk : visitBlock hn hG hT q w hw = visitBlock hn hG hT q (visitTwin w) htw :=
      congrArg (Shadow.singleStrandEquiv _) h
    apply visitTwin_edge_ne w
    rw [visit_edge_eq_blockEdge hn hG hT q w hw, visit_edge_eq_blockEdge hn hG hT q (visitTwin w) htw, hk]
  have hcases : s = ⟨0, visitBlock hn hG hT q w hw⟩ ∨ s = ⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ := by
    by_contra hnot
    have h1 : s ≠ ⟨0, visitBlock hn hG hT q w hw⟩ := fun h => hnot (Or.inl h)
    have h2 : s ≠ ⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ := fun h => hnot (Or.inr h)
    apply hΓ.no_triple
    exact ⟨s, _, _, h1, hne, h2, _, ⟨hs_int, hw_int⟩, htw_int⟩
  have hiff : ∀ t : (geoCarrierShadow hn hG hT q).Strand,
      t ∈ (shadowCrossing hn hG hT q w hw).val ↔ t ∈ x.val := fun t => by rw [hx]
  rcases hcases with rfl | rfl
  · exact ⟨⟨w, hw⟩, Sigma.ext hx ((Subtype.heq_iff_coe_eq hiff).mpr rfl)⟩
  · exact ⟨⟨visitTwin w, htw⟩, Sigma.ext hx ((Subtype.heq_iff_coe_eq hiff).mpr rfl)⟩

/-- **The occurrences of the lift ≃ the visits of the retained crossings.** -/
noncomputable def liftVisitEquiv :
    {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T q} ≃ (geoCarrierShadow hn hG hT q).Visit :=
  Equiv.ofBijective _ ⟨liftVisit_injective hn hG hT q, liftVisit_surjective hn hG hT q⟩

@[simp] theorem liftVisitEquiv_apply (w : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T q}) :
    liftVisitEquiv hn hG hT q w = liftVisit hn hG hT q w.1 w.2 := rfl

/-- **The pairing of the lift is the parent's `visitTwin`.** -/
theorem twin_liftVisit (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoPositiveLift hn hG hT q).twin (liftVisit hn hG hT q w hw) =
      liftVisit hn hG hT q (visitTwin w) (mem_twin hG q hw) := by
  refine (Diagram.twin_unique (geoPositiveLift hn hG hT q) (liftVisit hn hG hT q w hw)
    (liftVisit hn hG hT q (visitTwin w) (mem_twin hG q hw)) rfl ?_).symm
  intro h
  have := liftVisit_injective hn hG hT q (a₁ := ⟨visitTwin w, mem_twin hG q hw⟩) (a₂ := ⟨w, hw⟩) h
  exact visitTwin_ne w (congrArg Subtype.val this)

theorem det_smul_smul_both (c d : ℝ) (v w : Plane) : det (c • v) (d • w) = (c * d) * det v w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **The over bit of the lift at a visit is the sign of `det` of the two parent edges there**
(divide convention read on the parent's edges: the corner-polygon edges are positive multiples of them). -/
theorem isOver_liftVisit_iff (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoPositiveLift hn hG hT q).isOver (liftVisit hn hG hT q w hw) ↔
      0 < det (edge Q w.2.val) (edge Q (visitTwin w).2.val) := by
  have hs : (⟨0, visitBlock hn hG hT q w hw⟩ : (geoCarrierShadow hn hG hT q).Strand) ∈
      (shadowCrossing hn hG hT q w hw).val := blockStrand_mem hn hG hT q w hw
  have htw := mem_twin hG q hw
  have hs' : (⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ : (geoCarrierShadow hn hG hT q).Strand) ∈
      (shadowCrossing hn hG hT q w hw).val := blockStrand_mem hn hG hT q (visitTwin w) htw
  have hne : (⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ : (geoCarrierShadow hn hG hT q).Strand) ≠
      ⟨0, visitBlock hn hG hT q w hw⟩ := by
    intro h
    have hk : visitBlock hn hG hT q (visitTwin w) htw = visitBlock hn hG hT q w hw :=
      congrArg (Shadow.singleStrandEquiv _) h
    apply visitTwin_edge_ne w
    rw [visit_edge_eq_blockEdge hn hG hT q w hw, visit_edge_eq_blockEdge hn hG hT q (visitTwin w) htw, hk]
  have hdir : (geoCarrierShadow hn hG hT q).dir ⟨0, visitBlock hn hG hT q w hw⟩ =
      blockScale hn hG hT q (visitBlock hn hG hT q w hw) • edge Q w.2.val := by
    show edge (geoCornerPolygon hG.cg T q) (visitBlock hn hG hT q w hw) = _
    rw [edge_geoCornerPolygon_eq hn hG hT q, ← visit_edge_eq_blockEdge hn hG hT q w hw]
  have hdir' : (geoCarrierShadow hn hG hT q).dir ⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ =
      blockScale hn hG hT q (visitBlock hn hG hT q (visitTwin w) htw) • edge Q (visitTwin w).2.val := by
    show edge (geoCornerPolygon hG.cg T q) (visitBlock hn hG hT q (visitTwin w) htw) = _
    rw [edge_geoCornerPolygon_eq hn hG hT q, ← visit_edge_eq_blockEdge hn hG hT q (visitTwin w) htw]
  have hpos_iff : 0 < det ((geoCarrierShadow hn hG hT q).dir ⟨0, visitBlock hn hG hT q w hw⟩)
      ((geoCarrierShadow hn hG hT q).dir ⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩) ↔
      0 < det (edge Q w.2.val) (edge Q (visitTwin w).2.val) := by
    rw [hdir, hdir', det_smul_smul_both]
    exact mul_pos_iff_of_pos_left (mul_pos (blockScale_pos hn hG hT q _) (blockScale_pos hn hG hT q _))
  have hposD := geoPositiveLift_isPositive hn hG hT q (shadowCrossing hn hG hT q w hw)
  unfold Diagram.IsPositive at hposD
  rcases ((geoPositiveLift hn hG hT q).mem_iff (shadowCrossing hn hG hT q w hw) _).mp hs with hso | hsu
  · -- the block strand of `w` is the over strand
    have hu : (geoPositiveLift hn hG hT q).underStrand (shadowCrossing hn hG hT q w hw) =
        (⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ : (geoCarrierShadow hn hG hT q).Strand) := by
      symm
      apply (geoPositiveLift hn hG hT q).eq_under_of_mem_of_ne _ hs'
      rw [← hso]
      exact hne
    constructor
    · intro _
      rw [← hso, hu] at hposD
      exact hpos_iff.mp hposD
    · intro _
      exact hso
  · -- the block strand of `w` is the under strand: the determinant is negative
    have ho : (geoPositiveLift hn hG hT q).overStrand (shadowCrossing hn hG hT q w hw) =
        (⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩ : (geoCarrierShadow hn hG hT q).Strand) := by
      symm
      apply (geoPositiveLift hn hG hT q).eq_over_of_mem_of_ne _ hs'
      rw [← hsu]
      exact hne
    constructor
    · intro h
      exfalso
      have h' : (⟨0, visitBlock hn hG hT q w hw⟩ : (geoCarrierShadow hn hG hT q).Strand) =
          (geoPositiveLift hn hG hT q).overStrand (shadowCrossing hn hG hT q w hw) := h
      rw [ho] at h'
      exact hne h'.symm
    · intro h
      exfalso
      rw [ho, ← hsu, det_swap] at hposD
      have h1 : 0 < -det ((geoCarrierShadow hn hG hT q).dir ⟨0, visitBlock hn hG hT q w hw⟩)
          ((geoCarrierShadow hn hG hT q).dir ⟨0, visitBlock hn hG hT q (visitTwin w) htw⟩) := hposD
      have h2 := hpos_iff.mpr h
      linarith

/-- **The traversal coordinate of an occurrence of the lift is the block coordinate of its mark.** -/
theorem visitCoord_liftVisit (w : Visit Q) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoPositiveLift hn hG hT q).visitCoord (liftVisit hn hG hT q w hw) = markCoord hn hG hT q (Sum.inr w) := by
  have hm := owner_of_mem_geoCarrierCrossings hG q hw
  obtain ⟨hr, hb, -⟩ := markBlock_spec hn hG hT q (Sum.inr w) hm
  rw [markCoord_of_block hn hG hT q hm hr hb]
  show ((visitBlock hn hG hT q w hw).val : ℝ) +
    (geoPositiveLift hn hG hT q).crossingParam (shadowCrossing hn hG hT q w hw) (blockStrand_mem hn hG hT q w hw) = _
  congr 1
  have hspec : (geoCarrierShadow hn hG hT q).crossingPoint (shadowCrossing hn hG hT q w hw) =
      edgePoint (geoCornerPolygon hG.cg T q) (visitBlock hn hG hT q w hw)
        ((geoPositiveLift hn hG hT q).crossingParam (shadowCrossing hn hG hT q w hw)
          (blockStrand_mem hn hG hT q w hw)) :=
    ((geoPositiveLift hn hG hT q).crossingParam_spec (shadowCrossing hn hG hT q w hw)
      (blockStrand_mem hn hG hT q w hw)).2.2
  rw [shadowCrossing_crossingPoint, edgePoint_geoCornerPolygon hn hG hT q] at hspec
  have hpos : crossingPoint w.1 =
      edgePoint Q (blockEdge hG q (visitBlock hn hG hT q w hw)) (geoOutSlot hG.cg T (Sum.inr w)).2.val := by
    rw [← geoMarkPosition_evaluation_visit hG.cg w, geo_evaluation_eq_outSlot hG.cg T]
    congr 1
    rw [← hr]
    exact outSlot_edge_of_blockInterior hn hG hT q hb
  rw [hpos] at hspec
  have heq := edgePoint_injective (edge_blockEdge_ne_zero hG q _) hspec
  have hsc := blockScale_pos hn hG hT q (visitBlock hn hG hT q w hw)
  show _ = ((geoOutSlot hG.cg T (Sum.inr w)).2.val - blockStart hG q (visitBlock hn hG hT q w hw)) /
    blockScale hn hG hT q (visitBlock hn hG hT q w hw)
  rw [eq_div_iff hsc.ne']
  linarith

/-- **The cyclic order of the lift's occurrences is the parent's cyclic order of the visits.** -/
theorem visitBetween_liftVisit_iff (a b c : Visit Q) (ha : a.1 ∈ geoCarrierCrossings hG.cg T q)
    (hb : b.1 ∈ geoCarrierCrossings hG.cg T q) (hc : c.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoPositiveLift hn hG hT q).VisitBetween (liftVisit hn hG hT q a ha) (liftVisit hn hG hT q b hb)
        (liftVisit hn hG hT q c hc) ↔
      cycBetween (geometricVisitKey hG.cg a) (geometricVisitKey hG.cg b) (geometricVisitKey hG.cg c) := by
  unfold Diagram.VisitBetween
  rw [visitCoord_liftVisit, visitCoord_liftVisit, visitCoord_liftVisit]
  exact cycBetween_markCoord_iff hn hG hT q (owner_of_mem_geoCarrierCrossings hG q ha)
    (owner_of_mem_geoCarrierCrossings hG q hb) (owner_of_mem_geoCarrierCrossings hG q hc)

/-! ### The same data, typed on the occurrences of the positive lift -/

/-- `liftVisitEquiv`, typed on the occurrences `D.Γ.Visit` of the positive lift `D` (the type
`recordIsoOfData` reads; definitionally the same bijection). -/
noncomputable def liftOcc :
    {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T q} ≃ (geoPositiveLift hn hG hT q).Γ.Visit :=
  liftVisitEquiv hn hG hT q

theorem twin_liftOcc (a : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T q}) :
    (geoPositiveLift hn hG hT q).twin (liftOcc hn hG hT q a) =
      liftOcc hn hG hT q ⟨visitTwin a.1, mem_twin hG q a.2⟩ :=
  twin_liftVisit hn hG hT q a.1 a.2

theorem isOver_liftOcc_iff (a : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T q}) :
    (geoPositiveLift hn hG hT q).isOver (liftOcc hn hG hT q a) ↔
      0 < det (edge Q a.1.2.val) (edge Q (visitTwin a.1).2.val) :=
  isOver_liftVisit_iff hn hG hT q a.1 a.2

theorem visitBetween_liftOcc_iff (a b c : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T q}) :
    (geoPositiveLift hn hG hT q).VisitBetween (liftOcc hn hG hT q a) (liftOcc hn hG hT q b)
        (liftOcc hn hG hT q c) ↔
      cycBetween (geometricVisitKey hG.cg a.1) (geometricVisitKey hG.cg b.1) (geometricVisitKey hG.cg c.1) :=
  visitBetween_liftVisit_iff hn hG hT q a.1 b.1 c.1 a.2 b.2 c.2

end Visits

end PieceHomfly

/-! ## 4. Choice independence of the positive lift's HOMFLY polynomial at one polygon

Two carriers `q₁`, `q₂` of independent supports `T₁`, `T₂` with the same retained crossings. Their lifts
have isomorphic records through `liftOcc`: the cyclic orders agree (`visitBetween_liftOcc_iff`), the
pairings are both `visitTwin` (`twin_liftOcc`), the over bits are both the sign of `det` of the parent
edges (`isOver_liftOcc_iff`), all signs are `+1`. (Each clause is a separate declaration: the kernel
checks are heavier than they look.) -/

namespace PieceHomfly

section TwoCarriers

variable {n : ℕ} [NeZero n] {Q : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry Q)
  {T₁ T₂ : Finset (Crossing Q)} (hT₁ : GeoIndependent hG.cg T₁) (hT₂ : GeoIndependent hG.cg T₂)
  (q₁ : GeoComponent hG.cg T₁) (q₂ : GeoComponent hG.cg T₂)
  (hH : geoCarrierCrossings hG.cg T₁ q₁ = geoCarrierCrossings hG.cg T₂ q₂)

/-- The visits of the common retained crossings, read on either carrier. -/
def crossEquiv : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T₁ q₁} ≃
    {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T₂ q₂} :=
  Equiv.subtypeEquivRight fun w => by rw [hH]

theorem crossEquiv_val (w : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T₁ q₁}) :
    (crossEquiv hG q₁ q₂ hH w).1 = w.1 := by
  rw [crossEquiv, Equiv.subtypeEquivRight_apply]

/-- **The occurrence bijection between the two lifts.** -/
noncomputable def liftIso :
    (geoPositiveLift hn hG hT₁ q₁).Γ.Visit ≃ (geoPositiveLift hn hG hT₂ q₂).Γ.Visit :=
  (liftOcc hn hG hT₁ q₁).symm.trans ((crossEquiv hG q₁ q₂ hH).trans (liftOcc hn hG hT₂ q₂))

theorem liftIso_liftOcc (w : {w : Visit Q // w.1 ∈ geoCarrierCrossings hG.cg T₁ q₁}) :
    liftIso hn hG hT₁ hT₂ q₁ q₂ hH (liftOcc hn hG hT₁ q₁ w) =
      liftOcc hn hG hT₂ q₂ (crossEquiv hG q₁ q₂ hH w) := by
  simp only [liftIso, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- (a) the cyclic order is preserved. -/
theorem liftIso_cyclicOrder :
    PreservesCyclicOrder (geoPositiveLift hn hG hT₁ q₁) (geoPositiveLift hn hG hT₂ q₂)
      (liftIso hn hG hT₁ hT₂ q₁ q₂ hH) := by
  intro v w u h
  obtain ⟨a, rfl⟩ := (liftOcc hn hG hT₁ q₁).surjective v
  obtain ⟨b, rfl⟩ := (liftOcc hn hG hT₁ q₁).surjective w
  obtain ⟨c, rfl⟩ := (liftOcc hn hG hT₁ q₁).surjective u
  rw [visitBetween_liftOcc_iff] at h
  rw [liftIso_liftOcc, liftIso_liftOcc, liftIso_liftOcc, visitBetween_liftOcc_iff, crossEquiv_val,
    crossEquiv_val, crossEquiv_val]
  exact h

/-- (b) double points are carried to double points. -/
theorem liftIso_doublePoints :
    CarriesDoublePoints (ρ := (geoPositiveLift hn hG hT₁ q₁).record)
      (ρ' := (geoPositiveLift hn hG hT₂ q₂).record) (liftIso hn hG hT₁ hT₂ q₁ q₂ hH) := by
  refine (carriesDoublePoints_iff (ρ := (geoPositiveLift hn hG hT₁ q₁).record)
    (ρ' := (geoPositiveLift hn hG hT₂ q₂).record) _).2 fun v => ?_
  obtain ⟨a, rfl⟩ := (liftOcc hn hG hT₁ q₁).surjective v
  show liftIso hn hG hT₁ hT₂ q₁ q₂ hH ((geoPositiveLift hn hG hT₁ q₁).twin (liftOcc hn hG hT₁ q₁ a)) =
    (geoPositiveLift hn hG hT₂ q₂).twin (liftIso hn hG hT₁ hT₂ q₁ q₂ hH (liftOcc hn hG hT₁ q₁ a))
  rw [liftIso_liftOcc, twin_liftOcc, twin_liftOcc, liftIso_liftOcc]
  refine congrArg (liftOcc hn hG hT₂ q₂) (Subtype.ext ?_)
  rw [crossEquiv_val]
  show visitTwin a.1 = visitTwin (crossEquiv hG q₁ q₂ hH a).1
  rw [crossEquiv_val]

/-- (c) over positions go to over positions, under to under. -/
theorem liftIso_overUnder :
    CarriesOverUnder (ρ := (geoPositiveLift hn hG hT₁ q₁).record)
      (ρ' := (geoPositiveLift hn hG hT₂ q₂).record) (liftIso hn hG hT₁ hT₂ q₁ q₂ hH) := by
  refine (carriesOverUnder_iff (ρ := (geoPositiveLift hn hG hT₁ q₁).record)
    (ρ' := (geoPositiveLift hn hG hT₂ q₂).record) _).2 fun v => ?_
  obtain ⟨a, rfl⟩ := (liftOcc hn hG hT₁ q₁).surjective v
  show (geoPositiveLift hn hG hT₂ q₂).overBit (liftIso hn hG hT₁ hT₂ q₁ q₂ hH (liftOcc hn hG hT₁ q₁ a)) =
    (geoPositiveLift hn hG hT₁ q₁).overBit (liftOcc hn hG hT₁ q₁ a)
  rw [Bool.eq_iff_iff, Diagram.overBit_eq_true_iff, Diagram.overBit_eq_true_iff, liftIso_liftOcc,
    isOver_liftOcc_iff, isOver_liftOcc_iff, crossEquiv_val]

/-- (d) the signs are preserved (all `+1`). -/
theorem liftIso_signs (v : (geoPositiveLift hn hG hT₁ q₁).Γ.Visit) :
    (geoPositiveLift hn hG hT₂ q₂).record.sgn (liftIso hn hG hT₁ hT₂ q₁ q₂ hH v) =
      (geoPositiveLift hn hG hT₁ q₁).record.sgn v := by
  show (geoPositiveLift hn hG hT₂ q₂).sign (liftIso hn hG hT₁ hT₂ q₁ q₂ hH v).1 =
    (geoPositiveLift hn hG hT₁ q₁).sign v.1
  rw [geoPositiveLift_sign, geoPositiveLift_sign]

/-- **The records of the two lifts are isomorphic** (CV:def:record (a)–(d) through `recordIsoOfData`). -/
noncomputable def liftRecordIso :
    RecordIso (geoPositiveLift hn hG hT₁ q₁).record (geoPositiveLift hn hG hT₂ q₂).record :=
  recordIsoOfData (geoPositiveLift_componentCount hn hG hT₁ q₁) (geoPositiveLift_componentCount hn hG hT₂ q₂)
    (liftIso hn hG hT₁ hT₂ q₁ q₂ hH)
    ⟨liftIso_cyclicOrder hn hG hT₁ hT₂ q₁ q₂ hH, liftIso_doublePoints hn hG hT₁ hT₂ q₁ q₂ hH,
      liftIso_overUnder hn hG hT₁ hT₂ q₁ q₂ hH, liftIso_signs hn hG hT₁ hT₂ q₁ q₂ hH⟩

end TwoCarriers

end PieceHomfly

/-- **Two carriers with the same retained crossings have positive lifts with the same HOMFLY polynomial**
(on one polygon, tier 1): the records are isomorphic (`PieceHomfly.liftRecordIso`) and the accepted
CV:ax:gausscode replacement `gausscode_polynomial` gives the equality of polynomials. -/
theorem homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq {n : ℕ} [NeZero n] {Q : LabelledTuple n}
    (hn : 3 ≤ n) (hG : CarrierGeometry Q) {T₁ T₂ : Finset (Crossing Q)}
    (hT₁ : GeoIndependent hG.cg T₁) (hT₂ : GeoIndependent hG.cg T₂)
    (q₁ : GeoComponent hG.cg T₁) (q₂ : GeoComponent hG.cg T₂)
    (hH : geoCarrierCrossings hG.cg T₁ q₁ = geoCarrierCrossings hG.cg T₂ q₂) :
    homfly (geoPositiveLift hn hG hT₁ q₁) = homfly (geoPositiveLift hn hG hT₂ q₂) :=
  gausscode_polynomial _ _ (geoPositiveLift_componentCount hn hG hT₁ q₁)
    (geoPositiveLift_componentCount hn hG hT₂ q₂) (PieceHomfly.liftRecordIso hn hG hT₁ hT₂ q₁ q₂ hH)

/-! ## 5. The chamber transport of the piece polynomials -/

/-- **The piece polynomials are carried along a chamber** (the open hypothesis of CV/ChamberInvII.lean):
at `Q` the carrier of `S' ∪ K'` (the support chosen at `Q`) and the transport of the carrier of `S ∪ K_H`
(the support chosen at `P`) both carry exactly the labels of the piece, so their positive lifts have the same
HOMFLY polynomial (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`), and the transported lift has the
polynomial of the lift at `P` (`homfly_geoPositiveLift_eq_of_mem_chamber`, lit:homfly's planar clause along
the chamber path). -/
theorem pieceHomflyTransported {n : ℕ} [NeZero n] {P Q : LabelledTuple n} (hn : 3 ≤ n) (hP : Generic P)
    (hQ : Generic Q) (h : Q ∈ chamber P) : PieceHomflyTransported hn hP hQ h := by
  intro S hS hS' H
  have hSK : S ∪ pieceSupport (hP.diagrammatic hn) hS H ∈ Ind hP.crossingGeometry :=
    pieceSupport_mem_Ind (hP.diagrammatic hn) hS H
  have hSK' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h)
      (S ∪ pieceSupport (hP.diagrammatic hn) hS H) ∈ Ind hQ.crossingGeometry :=
    (mem_Ind_transport_iff hn hP hQ h _).mpr hSK
  have hK2 : GeoIndependent (CarrierGeometry.ofCV hQ).cg (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h)
      (S ∪ pieceSupport (hP.diagrammatic hn) hS H)) :=
    geoIndependent_of_mem_Ind _ hSK'
  have hcross : geoCarrierCrossings hQ.crossingGeometry
      (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∪
        pieceSupport (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H))
      (pieceCarrier (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H)) =
      geoCarrierCrossings hQ.crossingGeometry
        (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) (S ∪ pieceSupport (hP.diagrammatic hn) hS H))
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component _ (pieceCarrier (hP.diagrammatic hn) hS H)) := by
    rw [pieceCarrier_geoCarrierCrossings, pieceLabels_eq hn hP hQ h S H,
      geoCarrierCrossings_eq_of_mem_chamber hn hP hQ h, pieceCarrier_geoCarrierCrossings]
  unfold pieceHomfly pieceDiagram
  rw [homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn (CarrierGeometry.ofDiagrammatic (hQ.diagrammatic hn))
    (pieceSupport_geoIndependent (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H)) hK2
    (pieceCarrier (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H)) _ hcross]
  exact homfly_geoPositiveLift_eq_of_mem_chamber hn hP hQ h _ hSK hK2 (pieceCarrier (hP.diagrammatic hn) hS H)

end CV
