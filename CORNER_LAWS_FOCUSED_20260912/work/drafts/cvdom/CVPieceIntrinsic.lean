import CV.PieceCurve

/-! # CV lane, row 156 — CV:lem:pieceintrinsic, "carrier restriction is the intrinsic piece diagram"

Source: reference/R/CV/d6_vertexedge.tex, `lem:pieceintrinsic` (statement lines 56–74, proof 75–115);
consumer `cor:groupedknot` (263–330, the record comparison at the leaves and the factor identification
of clause (B)). Dependencies: CV:def:piecediagram (row 142, `CV.pieceDiagram`, work/lean/CV/PieceCurve.lean),
CV:lem:carrierword (row 137, work/lean/CV/CarrierWord.lean), CV:def:record (row 140,
work/lean/CV/RecordHomfly.lean), CV:ax:gausscode (row 163, F4 replacement `CV.gausscode_polynomial`,
work/lean/CV/Axioms.lean). Written 2026-09-14 by a Claude Code prover subagent; checked with
`cd work/lean && lake env lean ../drafts/cvdom/CVPieceIntrinsic.lean`.

Row declaration: `CV.pieceintrinsic (hn) (hG : Generic P) (S) (hS) (H) : CV.PieceIntrinsicData …`, on the
printed binder "Let `P` be generic" (d6:58), one field per printed clause (§7). The Diagrammatic form
`CV.pieceintrinsic_of_diagrammatic` is the working theorem; the row is its instance through
`CV.Generic.diagrammatic hn`.

## Readings (DECISION_FINAL.md §2, reading (ii); recorded in CVPIECEINTRINSIC_REPORT.md)

* `D_P(H)`, "the intrinsic piece diagram of that definition, obtained from the parent polygon `P` by
  retaining exactly the same crossings under the same convention" (d6:62–64), is the accepted
  `CV.pieceDiagram hn hD hS H` of row 142: the positive lift of the piece curve `C_H` (reading (ii)).
* `D_L(H)`, "the diagram obtained from `L` by retaining exactly the crossings of `H`, each resolved by the
  divide convention of Definition def:piecediagram, and erasing all others" (d6:59–62): under the same
  reading "erasing" a double point is smoothing it into the carrier of `H`, Step 5's iteration of
  lem:piececurve; so `D_L(H)` is the positive lift of a carrier `q` of `S ∪ K`, where `K` is any admissible
  set of erased double points (`StepInvariant`: `K ⊆ U(S)`, `K ∩ H = ∅`, `S ∪ K ∈ Ind(G_P)`) with
  `geoCarrierCrossings (S ∪ K) q = H` ("retaining exactly the crossings of `H`"). Such a `q` lies inside
  `L` (`IsCarrierRestriction.owner_eq`, from lem:carrierword's refinement clause). The row quantifies over
  every such `(K, q)`: the printed lemma names one `D_L(H)`, but the text fixes neither the order in which
  the other double points of `L` are erased nor the terminal set, so "the" diagram is the family, and the
  lemma's content — the intrinsic piece diagram does not depend on the route — is exactly the statement
  for every member. `D_P(H)` itself is a member (`pieceSupport`, `pieceCarrier`).
* "the identity map on the visits of `H`" (d6:67): every occurrence (`Diagram.record`'s `M`) of the
  positive lift of a carrier `q` is a double point of the corner polygon of `q` reached along one of its two
  strands; the strand lies on one parent edge of the crossing, and that names the parent visit
  `liftVisit v : Visit P` — "the same point of the plane, reached by the same branch" (d6:100–102). The
  isomorphism `ι` of the row satisfies `liftVisit (ι.Φ v) = liftVisit v`.
* "they present the same oriented link (Axiom ax:gausscode)" (d6:69–70): the F4 replacement of row 163
  (CV/Axioms.lean): the two HOMFLY–PT polynomials agree (`CV.gausscode_polynomial`); link equivalence
  itself is outside the formal scope and is neither assumed nor claimed.

## Proof route (d6:75–115, the three paragraphs and the isomorphism)

The general theorem behind the row is §6 `exists_recordIso_of_geoCarrierCrossings_eq`: two carriers `q`
(of `T`) and `q'` (of `T'`), both independent, with the same retained crossings have record-isomorphic
positive lifts, the isomorphism being the identity on parent visits. Its four clauses are the printed
paragraphs: *same double points* — the occurrences of each lift are the visits of the retained crossings
(§4 `liftVisitEquiv`); *same over/under and signs* — the divide convention reads the over strand from
the two branch directions, and each strand of the corner polygon is a positive multiple of the parent edge
of its visit (`geoCornerPolygon_edge_smul`), so the bit is the parent's `det(edge v, edge (twin v)) > 0`
(§5 `overBit_eq_true_iff_parent`), and every sign is `+1`; *same cyclic order* — the traversal order of the
occurrences along the corner polygon of `q` is the cyclic order the marks of `q` inherit from `Γ`
(lem:carrierword), rendered as `visitBetween_iff_key` (§5) through the corner-polygon coordinate of §3 and
the traced mark list of §2; *the isomorphism* — clauses (a)–(d) of def:record assembled by the accepted
`CV.recordIsoOfData` (row 140). -/

namespace CV

open SM SM.Carrier SM.GeoCarrier SM.Link

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## 1. Cyclic betweenness: transport along an order embedding and along a rotation -/

section CycBetweenTransport

/-- `cycBetween` is a Boolean combination of the three strict comparisons, so any map that preserves
and reflects `<` transports it. -/
theorem cycBetween_iff_of_lt_iff {α : Type*} {f g : α → ℝ} (h : ∀ x y, f x < f y ↔ g x < g y)
    (a b c : α) : cycBetween (f a) (f b) (f c) ↔ cycBetween (g a) (g b) (g c) := by
  unfold cycBetween
  rw [h a b, h b c, h c a]

/-- A sequence increasing at every step below `N` is strictly increasing below `N`. -/
theorem lt_of_lt_succ_below {g : ℕ → ℝ} {N : ℕ} (h : ∀ j, j + 1 < N → g j < g (j + 1)) :
    ∀ i j, i < j → j < N → g i < g j := by
  intro i j hij hjN
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact (ih hlt (by omega)).trans (h j hjN)
    · have hij' : i = j := by omega
      subst hij'
      exact h i hjN

theorem lt_iff_of_lt_succ_below {g : ℕ → ℝ} {N : ℕ} (h : ∀ j, j + 1 < N → g j < g (j + 1))
    {i j : ℕ} (hi : i < N) (hj : j < N) : g i < g j ↔ i < j := by
  constructor
  · intro hlt
    by_contra hge
    rcases Nat.lt_or_ge j i with hji | hij
    · exact absurd (lt_of_lt_succ_below h j i hji hi) (not_lt.mpr hlt.le)
    · have : i = j := by omega
      subst this
      exact lt_irrefl _ hlt
  · intro hij
    exact lt_of_lt_succ_below h i j hij hj

/-- The residue `(x + N - s) % N` for `x, s < N`, in closed form. -/
theorem rotate_mod_eq {N s x : ℕ} (hs : s < N) (hx : x < N) :
    (x + N - s) % N = if s ≤ x then x - s else x + N - s := by
  split_ifs with h
  · have e : x + N - s = (x - s) + N := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Cyclic betweenness of three positions on a circle of `N` places is invariant under rotating the
cut by `s` places. -/
theorem rotate_cyc_iff {N s i j k : ℕ} (hs : s < N) (hi : i < N) (hj : j < N) (hk : k < N) :
    (((i + N - s) % N < (j + N - s) % N ∧ (j + N - s) % N < (k + N - s) % N) ∨
      ((j + N - s) % N < (k + N - s) % N ∧ (k + N - s) % N < (i + N - s) % N) ∨
      ((k + N - s) % N < (i + N - s) % N ∧ (i + N - s) % N < (j + N - s) % N)) ↔
    ((i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)) := by
  rw [rotate_mod_eq hs hi, rotate_mod_eq hs hj, rotate_mod_eq hs hk]
  split_ifs <;> omega

/-- `((x + N - s) % N + s) % N = x` for `x, s < N`. -/
theorem rotate_unrotate {N s x : ℕ} (hs : s < N) (hx : x < N) :
    ((x + N - s) % N + s) % N = x := by
  rw [Nat.mod_add_mod, show x + N - s + s = x + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

end CycBetweenTransport

/-! ## 2. The traced mark list of a carrier: `ρ`-powers of its head, strict `Γ`-order

lem:carrierword (row 137): `geoComponentMarkList hP T q` lists the marks of the carrier `q` in the order
induced from `Γ` (sorted by `geoMarkKey`, the traversal coordinate on `Γ`), and `ρ_T` traces it entry by
entry (`TracedSuccessor`, `geoComponentMarkList_getElem_successor`). Here: the `i`-th entry is
`ρ_T^i` of the head, `ρ_T^N` fixes the head, and the `Γ`-keys are strictly increasing along the list. -/

section TracedList

variable (hP : CrossingGeometry P) {T : Finset (Crossing P)} (hT : GeoIndependent hP T)
  (q : GeoComponent hP T)

theorem markList_length_pos : 0 < (geoComponentMarkList hP T q).length :=
  geoComponentMarkList_length_pos hP T q

include hT in
/-- The `i`-th mark of the carrier is `ρ_T^i` of its first mark (`TracedSuccessor`, lem:carrierword). -/
theorem markList_getElem_pow (i : ℕ) (hi : i < (geoComponentMarkList hP T q).length) :
    (geoComponentMarkList hP T q)[i] =
      (geoSmoothingSuccessor hP T ^ i) ((geoComponentMarkList hP T q)[0]'(markList_length_pos hP q)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i < (geoComponentMarkList hP T q).length := by omega
    have hs := geoComponentMarkList_getElem_successor hP hT q ⟨i, hi'⟩
    dsimp only at hs
    simp only [Nat.mod_eq_of_lt hi] at hs
    rw [← hs, ih hi', pow_succ', Equiv.Perm.mul_apply]

include hT in
/-- `ρ_T^N` fixes the first mark, `N` the number of marks of the carrier. -/
theorem markList_pow_length :
    (geoSmoothingSuccessor hP T ^ (geoComponentMarkList hP T q).length)
        ((geoComponentMarkList hP T q)[0]'(markList_length_pos hP q)) =
      (geoComponentMarkList hP T q)[0]'(markList_length_pos hP q) := by
  have hN := markList_length_pos hP q
  have hs := geoComponentMarkList_getElem_successor hP hT q
    ⟨(geoComponentMarkList hP T q).length - 1, by omega⟩
  dsimp only at hs
  simp only [show (geoComponentMarkList hP T q).length - 1 + 1 = (geoComponentMarkList hP T q).length
    by omega, Nat.mod_self] at hs
  rw [markList_getElem_pow hP hT q _ (by omega)] at hs
  have hs' : (geoSmoothingSuccessor hP T ^ ((geoComponentMarkList hP T q).length - 1 + 1))
      ((geoComponentMarkList hP T q)[0]'(markList_length_pos hP q)) =
      (geoComponentMarkList hP T q)[0]'(markList_length_pos hP q) := by
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hs
  rw [show (geoComponentMarkList hP T q).length - 1 + 1 = (geoComponentMarkList hP T q).length
    by omega] at hs'
  exact hs'

include hT in
theorem markList_pow_mul_add (d r : ℕ) :
    (geoSmoothingSuccessor hP T ^ ((geoComponentMarkList hP T q).length * d + r))
        ((geoComponentMarkList hP T q)[0]'(markList_length_pos hP q)) =
      (geoSmoothingSuccessor hP T ^ r) ((geoComponentMarkList hP T q)[0]'(markList_length_pos hP q)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, show (geoComponentMarkList hP T q).length * d +
      (geoComponentMarkList hP T q).length + r =
        ((geoComponentMarkList hP T q).length * d + r) + (geoComponentMarkList hP T q).length by ring,
      pow_add, Equiv.Perm.mul_apply, markList_pow_length hP hT q, ih]

include hT in
/-- Every `ρ_T`-power of the first mark is an entry of the list, at the index reduced modulo `N`. -/
theorem markList_pow (j : ℕ) :
    (geoSmoothingSuccessor hP T ^ j) ((geoComponentMarkList hP T q)[0]'(markList_length_pos hP q)) =
      (geoComponentMarkList hP T q)[j % (geoComponentMarkList hP T q).length]'
        (Nat.mod_lt _ (markList_length_pos hP q)) := by
  conv_lhs => rw [← Nat.div_add_mod j (geoComponentMarkList hP T q).length]
  rw [markList_pow_mul_add hP hT q, markList_getElem_pow hP hT q _ (Nat.mod_lt _ (markList_length_pos hP q))]

/-- The marks of a carrier are listed in strictly increasing `Γ`-coordinate (`geoMarkKey`). -/
theorem markList_pairwise_key_lt :
    (geoComponentMarkList hP T q).Pairwise (fun a b => geoMarkKey hP a < geoMarkKey hP b) := by
  have h1 : (geoMarkList hP).Pairwise (fun a b => geoMarkKey hP a < geoMarkKey hP b) := by
    have hs := geoMarkList_sorted hP
    have hnd : (geoMarkList hP).Pairwise (fun a b => a ≠ b) := geoMarkList_nodup hP
    exact (hs.and hnd).imp fun {a b} h =>
      lt_of_le_of_ne h.1 fun heq => h.2 (geoMarkKey_injective hP heq)
  exact h1.filter _

theorem markList_key_lt_iff {i j : ℕ} (hi : i < (geoComponentMarkList hP T q).length)
    (hj : j < (geoComponentMarkList hP T q).length) :
    geoMarkKey hP (geoComponentMarkList hP T q)[i] < geoMarkKey hP (geoComponentMarkList hP T q)[j] ↔
      i < j := by
  have hpw := markList_pairwise_key_lt hP q
  rw [List.pairwise_iff_getElem] at hpw
  constructor
  · intro hlt
    by_contra hge
    rcases Nat.lt_or_ge j i with hji | hij
    · exact absurd (hpw j i hj hi hji) (not_lt.mpr hlt.le)
    · have : i = j := by omega
      subst this
      exact lt_irrefl _ hlt
  · exact hpw i j hi hj

end TracedList

/-! ## 3. The corner-polygon coordinate of a mark of a carrier (tier 1)

The positive lift of a carrier `q` is a diagram on the corner polygon `Q = geoCornerPolygon q`
(`geoCarrierShadow`), whose record orders the occurrences by their traversal coordinate on `Q`
(`Diagram.visitCoord`: corner-edge index plus edge parameter). Every mark `a` of `q` sits on the closed
edge `k` of `Q` of its block (`geo_mark_block`: `a = ρ_T^r c_k`, the intermediate marks interior to the
block); its **corner coordinate** `κ(a) = k.val + t`, `Q k + t • edge Q k = position of a`, is the
`Q`-traversal coordinate of its point. The coordinate increases along `ρ_T` until the corner `c_0` is
reached again (`cornerCoord_lt_successor`), so the cyclic order it induces on the marks of `q` is the
orbit order of `ρ_T`, which is the order inherited from `Γ` (§2): `cornerCoord_cycBetween_iff_key`. This
is the "same cyclic order" paragraph of the printed proof (d6:92–96). -/

section CornerCoordinate

variable (hn : 3 ≤ n) (hG : CarrierGeometry P) {T : Finset (Crossing P)}
  (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

/-- The corner-polygon edge (block) of a mark of `q` (junk value `0` off `q`). -/
noncomputable def blockIndex (a : Mark P) : ZMod (geoCornerCount hG.cg T q) :=
  if ha : geoOwner hG.cg T a = q then Classical.choose (geo_mark_block hn hG.cg hT q a ha) else 0

theorem blockIndex_spec {a : Mark P} (ha : geoOwner hG.cg T a = q) :
    ∃ r : ℕ,
      (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q (blockIndex hn hG hT q a)) = a ∧
      GeoBlockInterior hG.cg T q (blockIndex hn hG hT q a) r ∧
      traversalEvaluation P (geoMarkPosition hG.cg a) ∈
        edgeSegment (geoCornerPolygon hG.cg T q) (blockIndex hn hG hT q a) := by
  unfold blockIndex
  simp only [ha, ↓reduceDIte]
  exact Classical.choose_spec (geo_mark_block hn hG.cg hT q a ha)

/-- The block of a mark is unique (`geo_block_mark_eq`). -/
theorem blockIndex_eq {a : Mark P} (ha : geoOwner hG.cg T a = q) {k : ZMod (geoCornerCount hG.cg T q)}
    {r : ℕ} (hb : GeoBlockInterior hG.cg T q k r)
    (hr : (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k) = a) :
    blockIndex hn hG hT q a = k := by
  obtain ⟨r', hr', hb', -⟩ := blockIndex_spec hn hG hT q ha
  exact (geo_block_mark_eq hG.cg T q hb' hb (hr'.trans hr.symm)).1

theorem position_mem_edgeSegment_blockIndex {a : Mark P} (ha : geoOwner hG.cg T a = q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ traversalEvaluation P (geoMarkPosition hG.cg a) =
      edgePoint (geoCornerPolygon hG.cg T q) (blockIndex hn hG hT q a) t :=
  (blockIndex_spec hn hG hT q ha).choose_spec.2.2

/-- The parameter of the point of a mark of `q` along the corner-polygon edge of its block. -/
noncomputable def blockParam (a : Mark P) : ℝ :=
  if ha : geoOwner hG.cg T a = q then
    Classical.choose (position_mem_edgeSegment_blockIndex hn hG hT q ha)
  else 0

theorem blockParam_spec {a : Mark P} (ha : geoOwner hG.cg T a = q) :
    0 ≤ blockParam hn hG hT q a ∧ blockParam hn hG hT q a ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hG.cg a) =
        edgePoint (geoCornerPolygon hG.cg T q) (blockIndex hn hG hT q a) (blockParam hn hG hT q a) := by
  unfold blockParam
  simp only [ha, ↓reduceDIte]
  exact Classical.choose_spec (position_mem_edgeSegment_blockIndex hn hG hT q ha)

theorem blockParam_eq {a : Mark P} (ha : geoOwner hG.cg T a = q) {t : ℝ}
    (ht : traversalEvaluation P (geoMarkPosition hG.cg a) =
      edgePoint (geoCornerPolygon hG.cg T q) (blockIndex hn hG hT q a) t) :
    blockParam hn hG hT q a = t :=
  edgePoint_injective (geoCornerPolygon_edge_ne_zero_of_independent hn hG.cg hT q _)
    ((blockParam_spec hn hG hT q ha).2.2.symm.trans ht)

/-- **The corner coordinate** of a mark of `q`: its traversal coordinate on the corner polygon `Q`
(block index plus edge parameter), the coordinate `Diagram.visitCoord` reads on the positive lift. -/
noncomputable def cornerCoord (a : Mark P) : ℝ :=
  ((blockIndex hn hG hT q a).val : ℝ) + blockParam hn hG hT q a

theorem blockIndex_cornerMark (k : ZMod (geoCornerCount hG.cg T q)) :
    blockIndex hn hG hT q (geoCornerMark hG.cg T q k) = k :=
  blockIndex_eq hn hG hT q (geoOwner_geoCornerMark hG.cg T q k) (r := 0)
    (fun _ h1 h0 => (by omega : False).elim) (by simp)

theorem blockParam_cornerMark (k : ZMod (geoCornerCount hG.cg T q)) :
    blockParam hn hG hT q (geoCornerMark hG.cg T q k) = 0 := by
  apply blockParam_eq hn hG hT q (geoOwner_geoCornerMark hG.cg T q k)
  rw [blockIndex_cornerMark, edgePoint_zero]
  exact (geoCornerPolygon_apply hG.cg T q k).symm

/-- A corner `c_k` has coordinate `k`. -/
theorem cornerCoord_cornerMark (k : ZMod (geoCornerCount hG.cg T q)) :
    cornerCoord hn hG hT q (geoCornerMark hG.cg T q k) = k.val := by
  unfold cornerCoord
  rw [blockIndex_cornerMark, blockParam_cornerMark, add_zero]

/-- The corner coordinate increases along `ρ_T`, except at the step returning to the corner `c_0`:
inside a block the parent-edge parameters of the block marks increase (`geoCornerPolygon_block`), and
the step to the next corner `c_{k+1}` raises the block index by one. -/
theorem cornerCoord_lt_successor {a : Mark P} (ha : geoOwner hG.cg T a = q)
    (hne : geoSmoothingSuccessor hG.cg T a ≠ geoCornerMark hG.cg T q 0) :
    cornerCoord hn hG hT q a < cornerCoord hn hG hT q (geoSmoothingSuccessor hG.cg T a) := by
  have h3 := three_le_geoCornerCount hn hG hT q
  obtain ⟨r, hr, hb, -⟩ := blockIndex_spec hn hG hT q ha
  set k := blockIndex hn hG hT q a with hkdef
  obtain ⟨m, hm1, hchain, hmid, hout, hinc, ⟨cc, hcc, hedge⟩, -, -⟩ :=
    geoCornerPolygon_block hn hG.cg hT q k
  set e := (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).1 with hedef
  -- `r < m`: the block ends at the next corner, which is not an interior visit
  have hrm : r < m := by
    by_contra hge
    obtain ⟨v, hv, hvT, -⟩ := hb m hm1 (not_lt.mp hge)
    have hcorner := isTrueCorner_geoCornerMark hG.cg T q (k + 1)
    rw [← hchain, hv] at hcorner
    exact hvT ((isTrueCorner_visit T v).mp hcorner)
  -- the point of a block mark `ρ^r' c_k`, `r' < m`, on the parent edge `e`
  have hpos : ∀ r' < m,
      traversalEvaluation P (geoMarkPosition hG.cg
        ((geoSmoothingSuccessor hG.cg T ^ r') (geoCornerMark hG.cg T q k))) =
      edgePoint P e (geoOutSlot hG.cg T
        ((geoSmoothingSuccessor hG.cg T ^ r') (geoCornerMark hG.cg T q k))).2.val := by
    intro r' hr'
    rw [geoCsi_evaluation_start hG.cg T]
    change edgePoint P (geoOutSlot hG.cg T _).1 (geoOutSlot hG.cg T _).2.val = _
    rw [hout r' hr']
  have hQk : geoCornerPolygon hG.cg T q k =
      edgePoint P e (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.val := by
    have h0 := hpos 0 (by omega)
    rw [pow_zero, Equiv.Perm.one_apply] at h0
    rw [geoCornerPolygon_apply]
    exact h0
  -- the edge-`k` parametrisation in parent coordinates
  have hQpt : ∀ t : ℝ, edgePoint (geoCornerPolygon hG.cg T q) k t =
      edgePoint P e ((geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.val + t * cc) := by
    intro t
    have hE : edge (geoCornerPolygon hG.cg T q) k = cc • edge P e := hedge
    unfold edgePoint at hQk ⊢
    rw [hE, hQk, smul_smul, add_smul, add_assoc]
  -- the block parameter of a block mark
  have hbp : ∀ r' < m, GeoBlockInterior hG.cg T q k r' →
      blockParam hn hG hT q ((geoSmoothingSuccessor hG.cg T ^ r') (geoCornerMark hG.cg T q k)) =
        ((geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r') (geoCornerMark hG.cg T q k))).2.val -
          (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.val) / cc := by
    intro r' hr' hb'
    have hown : geoOwner hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r') (geoCornerMark hG.cg T q k)) = q := by
      rw [geo_pow_owner]
      exact geoOwner_geoCornerMark hG.cg T q k
    have hbi : blockIndex hn hG hT q ((geoSmoothingSuccessor hG.cg T ^ r') (geoCornerMark hG.cg T q k)) = k :=
      blockIndex_eq hn hG hT q hown hb' rfl
    apply blockParam_eq hn hG hT q hown
    rw [hbi, hQpt, hpos r' hr']
    congr 1
    field_simp
    ring
  rcases Nat.lt_or_ge (r + 1) m with hlt | hge
  · -- inside the block: the next mark is `ρ^(r+1) c_k`, further along the same edge
    have hsucc : geoSmoothingSuccessor hG.cg T a =
        (geoSmoothingSuccessor hG.cg T ^ (r + 1)) (geoCornerMark hG.cg T q k) := by
      rw [← hr, pow_succ', Equiv.Perm.mul_apply]
    have hb' : GeoBlockInterior hG.cg T q k (r + 1) := fun i h1 hi => hmid i h1 (by omega)
    have hown' : geoOwner hG.cg T (geoSmoothingSuccessor hG.cg T a) = q := by
      rw [geoOwner_successor]
      exact ha
    have hbi' : blockIndex hn hG hT q (geoSmoothingSuccessor hG.cg T a) = k :=
      blockIndex_eq hn hG hT q hown' hb' hsucc.symm
    have h1 : blockParam hn hG hT q a =
        ((geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k))).2.val -
          (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.val) / cc := by
      rw [← hbp r (by omega) hb, hr]
    have h2 : blockParam hn hG hT q (geoSmoothingSuccessor hG.cg T a) =
        ((geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ (r + 1)) (geoCornerMark hG.cg T q k))).2.val -
          (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.val) / cc := by
      rw [hsucc]
      exact hbp (r + 1) hlt hb'
    unfold cornerCoord
    rw [hbi', ← hkdef, h1, h2]
    have hi := hinc r hlt
    have : ((geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k))).2.val -
          (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.val) / cc <
        ((geoOutSlot hG.cg T ((geoSmoothingSuccessor hG.cg T ^ (r + 1)) (geoCornerMark hG.cg T q k))).2.val -
          (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.val) / cc := by
      apply div_lt_div_of_pos_right _ hcc
      linarith
    linarith
  · -- the end of the block: the next mark is the corner `c_{k+1} ≠ c_0`
    have hrm' : r + 1 = m := by omega
    have hsucc : geoSmoothingSuccessor hG.cg T a = geoCornerMark hG.cg T q (k + 1) := by
      rw [← hr, ← Equiv.Perm.mul_apply, ← pow_succ', hrm', hchain]
    have hk1 : k + 1 ≠ 0 := fun h => hne (by rw [hsucc, h])
    have hval : (k + 1).val = k.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (show 1 < geoCornerCount hG.cg T q by omega)]
      have hklt := ZMod.val_lt k
      rcases Nat.lt_or_ge (k.val + 1) (geoCornerCount hG.cg T q) with h | h
      · exact Nat.mod_eq_of_lt h
      · exfalso
        apply hk1
        rw [← ZMod.val_eq_zero, ZMod.val_add, ZMod.val_one_eq_one_mod,
          Nat.mod_eq_of_lt (show 1 < geoCornerCount hG.cg T q by omega),
          show k.val + 1 = geoCornerCount hG.cg T q by omega, Nat.mod_self]
    -- the block parameter of `a` is strictly below `1`: `a`'s point is not the end corner
    have hlt1 : blockParam hn hG hT q a < 1 := by
      refine lt_of_le_of_ne (blockParam_spec hn hG hT q ha).2.1 fun h1 => ?_
      have hpa := (blockParam_spec hn hG hT q ha).2.2
      rw [h1, ← hkdef, edgePoint_one] at hpa
      have h0 : geoSmoothingSegment hG.cg T ((geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k)) 0 =
          geoCornerPolygon hG.cg T q (k + 1) := by
        rw [geoSmoothingSegment_zero, hr]
        exact hpa
      have hkk := geo_block_param_corner hn hG hT q le_rfl zero_lt_one hb h0
      have h10 : (1 : ZMod (geoCornerCount hG.cg T q)) = 0 := add_eq_left.mp hkk
      have hv := congrArg ZMod.val h10
      rw [ZMod.val_one_eq_one_mod, ZMod.val_zero,
        Nat.mod_eq_of_lt (show 1 < geoCornerCount hG.cg T q by omega)] at hv
      exact one_ne_zero hv
    rw [hsucc, cornerCoord_cornerMark, hval]
    unfold cornerCoord
    rw [← hkdef]
    push_cast
    linarith

/-- Along the orbit of `ρ_T` from the corner `c_0`, the corner coordinate is strictly increasing on the
first `N` steps (`N` the number of marks of `q`); `s` is the index of `c_0` in the traced list. -/
theorem cornerCoord_orbit_lt_iff {s : ℕ} (hs : s < (geoComponentMarkList hG.cg T q).length)
    (hc₀ : (geoComponentMarkList hG.cg T q)[s] = geoCornerMark hG.cg T q 0) {i j : ℕ}
    (hi : i < (geoComponentMarkList hG.cg T q).length) (hj : j < (geoComponentMarkList hG.cg T q).length) :
    cornerCoord hn hG hT q ((geoSmoothingSuccessor hG.cg T ^ i) (geoCornerMark hG.cg T q 0)) <
        cornerCoord hn hG hT q ((geoSmoothingSuccessor hG.cg T ^ j) (geoCornerMark hG.cg T q 0)) ↔
      i < j := by
  have hstep : ∀ j, j + 1 < (geoComponentMarkList hG.cg T q).length →
      cornerCoord hn hG hT q ((geoSmoothingSuccessor hG.cg T ^ j) (geoCornerMark hG.cg T q 0)) <
        cornerCoord hn hG hT q ((geoSmoothingSuccessor hG.cg T ^ (j + 1)) (geoCornerMark hG.cg T q 0)) := by
    intro j hj
    have hown : geoOwner hG.cg T ((geoSmoothingSuccessor hG.cg T ^ j) (geoCornerMark hG.cg T q 0)) = q := by
      rw [geo_pow_owner]
      exact geoOwner_geoCornerMark hG.cg T q 0
    rw [pow_succ', Equiv.Perm.mul_apply]
    apply cornerCoord_lt_successor hn hG hT q hown
    intro heq
    have hc₀' : geoCornerMark hG.cg T q 0 =
        (geoSmoothingSuccessor hG.cg T ^ s) ((geoComponentMarkList hG.cg T q)[0]'(markList_length_pos hG.cg q)) := by
      rw [← markList_getElem_pow hG.cg hT q s hs, hc₀]
    have h1 : (geoSmoothingSuccessor hG.cg T ^ (j + 1 + s))
          ((geoComponentMarkList hG.cg T q)[0]'(markList_length_pos hG.cg q)) =
        (geoSmoothingSuccessor hG.cg T ^ s) ((geoComponentMarkList hG.cg T q)[0]'(markList_length_pos hG.cg q)) := by
      rw [pow_add, Equiv.Perm.mul_apply, ← hc₀', pow_succ', Equiv.Perm.mul_apply, heq]
    rw [markList_pow hG.cg hT q, markList_pow hG.cg hT q] at h1
    simp only [Nat.mod_eq_of_lt hs] at h1
    have hmod := (geoComponentMarkList_nodup hG.cg T q).getElem_inj_iff.mp h1
    rcases Nat.lt_or_ge (j + 1 + s) (geoComponentMarkList hG.cg T q).length with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  exact lt_iff_of_lt_succ_below
    (g := fun j => cornerCoord hn hG hT q ((geoSmoothingSuccessor hG.cg T ^ j) (geoCornerMark hG.cg T q 0)))
    hstep hi hj

/-- **The two cyclic orders on the marks of a carrier agree**: three marks of `q` occur in a cyclic order
on the corner polygon `Q` (corner coordinate) exactly when they occur in that cyclic order on `Γ`
(`geoMarkKey`). Both orders are the orbit order of `ρ_T` (lem:carrierword for `Γ`; §3 for `Q`), read
from two different cuts (`rotate_cyc_iff`). -/
theorem cornerCoord_cycBetween_iff_key {a b d : Mark P} (ha : geoOwner hG.cg T a = q)
    (hb : geoOwner hG.cg T b = q) (hd : geoOwner hG.cg T d = q) :
    cycBetween (cornerCoord hn hG hT q a) (cornerCoord hn hG hT q b) (cornerCoord hn hG hT q d) ↔
      cycBetween (geoMarkKey hG.cg a) (geoMarkKey hG.cg b) (geoMarkKey hG.cg d) := by
  have hN := markList_length_pos hG.cg q
  obtain ⟨s, hs, hc₀⟩ := List.getElem_of_mem
    ((mem_geoComponentMarkList hG.cg T q _).mpr (geoOwner_geoCornerMark hG.cg T q 0))
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((mem_geoComponentMarkList hG.cg T q a).mpr ha)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((mem_geoComponentMarkList hG.cg T q b).mpr hb)
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ((mem_geoComponentMarkList hG.cg T q d).mpr hd)
  -- every entry is a `ρ`-power of `c_0`, at the rotated index
  have hrot : ∀ i (hi : i < (geoComponentMarkList hG.cg T q).length),
      (geoComponentMarkList hG.cg T q)[i] =
        (geoSmoothingSuccessor hG.cg T ^ ((i + (geoComponentMarkList hG.cg T q).length - s) %
          (geoComponentMarkList hG.cg T q).length)) (geoCornerMark hG.cg T q 0) := by
    intro i hi
    rw [← hc₀, markList_getElem_pow hG.cg hT q s hs, ← Equiv.Perm.mul_apply, ← pow_add,
      markList_pow hG.cg hT q]
    have hidx := rotate_unrotate hs hi
    simp only [hidx]
  have hQ : ∀ i j (hi : i < (geoComponentMarkList hG.cg T q).length)
      (hj : j < (geoComponentMarkList hG.cg T q).length),
      cornerCoord hn hG hT q (geoComponentMarkList hG.cg T q)[i] <
          cornerCoord hn hG hT q (geoComponentMarkList hG.cg T q)[j] ↔
        (i + (geoComponentMarkList hG.cg T q).length - s) % (geoComponentMarkList hG.cg T q).length <
          (j + (geoComponentMarkList hG.cg T q).length - s) % (geoComponentMarkList hG.cg T q).length := by
    intro i j hi hj
    rw [hrot i hi, hrot j hj]
    exact cornerCoord_orbit_lt_iff hn hG hT q hs hc₀ (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
  unfold cycBetween
  rw [hQ i j hi hj, hQ j k hj hk, hQ k i hk hi, markList_key_lt_iff hG.cg q hi hj,
    markList_key_lt_iff hG.cg q hj hk, markList_key_lt_iff hG.cg q hk hi]
  exact rotate_cyc_iff hs hi hj hk

end CornerCoordinate

/-! ## 4. The occurrences of the positive lift of a carrier are the visits of its retained crossings
(tier 1)

An occurrence (`Diagram.record`'s marked point) of `geoPositiveLift q` is a double point `x` of the corner
polygon `Q` together with one of its two strands, a corner edge `k` of `Q`. The double point is the
crossing point of a retained crossing `c` (`geoCarrierCrossingEquiv`); the edge `k` carries, in its block,
a visit `w` of `c` sitting at that point (`geo_edgeSegment_param`, `geo_carrier_crossingPoint_parameters`),
and `w` lies on the parent edge of the block (`GeoBlockInterior.visit_edge`), along which the strand is
directed (`geoCornerPolygon_edge_smul`). `liftVisit v := w` is "the same point of the plane, reached by
the same branch" (d6:100–102): the parent visit of the occurrence. This is the "same double points"
paragraph of the printed proof (d6:76–82). -/

section LiftVisit

variable (hn : 3 ≤ n) (hG : CarrierGeometry P) {T : Finset (Crossing P)}
  (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

theorem det_smul_left' (c : ℝ) (u v : Plane) : det (c • u) v = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem det_smul_right' (c : ℝ) (u v : Plane) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem det_self' (u : Plane) : det u u = 0 := by
  simp only [det]
  ring

/-- The retained crossing of `P` at an occurrence of the lift. -/
noncomputable def parentCrossing (v : (geoPositiveLift hn hG hT q).Γ.Visit) : Crossing P :=
  (geoCarrierCrossingEquiv hn hG hT q v.1).1

theorem liftCrossing_mem (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    parentCrossing hn hG hT q v ∈ geoCarrierCrossings hG.cg T q :=
  (geoCarrierCrossingEquiv hn hG hT q v.1).2

theorem liftCrossing_not_mem (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    parentCrossing hn hG hT q v ∉ T :=
  ((mem_geoCarrierCrossings hG.cg T q _).mp (liftCrossing_mem hn hG hT q v)).1

theorem crossingPoint_liftCrossing (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    crossingPoint (parentCrossing hn hG hT q v) = (geoPositiveLift hn hG hT q).Γ.crossingPoint v.1 :=
  crossingPoint_geoCarrierCrossingEquiv hn hG hT q v.1

/-- The corner edge of `Q` carrying the strand of an occurrence. -/
def liftEdge (v : (geoPositiveLift hn hG hT q).Γ.Visit) : ZMod (geoCornerCount hG.cg T q) := v.2.val.2

theorem crossingPoint_mem_liftEdge (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    crossingPoint (parentCrossing hn hG hT q v) ∈
      edgeSegment (geoCornerPolygon hG.cg T q) (liftEdge hn hG hT q v) := by
  rw [crossingPoint_liftCrossing]
  exact (geoPositiveLift hn hG hT q).Γ.crossingPoint_mem v.1 v.2.2

/-- The strand of an occurrence passes through the crossing point at a visit of the retained crossing
lying in the block of the strand's edge. -/
theorem liftVisit_exists (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    ∃ w : Visit P, w.1 = parentCrossing hn hG hT q v ∧ ∃ r : ℕ,
      GeoBlockInterior hG.cg T q (liftEdge hn hG hT q v) r ∧
      (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q (liftEdge hn hG hT q v)) =
        Sum.inr w := by
  have hc := liftCrossing_mem hn hG hT q v
  rcases geo_edgeSegment_param hn hG.cg hT q _ (crossingPoint_mem_liftEdge hn hG hT q v) with
    ⟨r, u, hu0, hu1, hb, hx⟩ | hx
  · obtain ⟨w, hw, -, hp⟩ := (geo_carrier_crossingPoint_parameters hn hG T q _ _).mp
      ⟨geoIsCarrierParameter_block hG.cg T q _ r hu0 hu1, hx⟩
    exact ⟨w, hw, r, hb, congrArg Prod.fst hp⟩
  · exfalso
    rw [geoCornerPolygon_apply] at hx
    exact (geo_carrier_selfIntersection_not_corner hG T q hc).2.2.2 _
      (isTrueCorner_geoCornerMark hG.cg T q _) hx.symm

/-- **The parent visit of an occurrence** of the lift: "the same visit … — the same point of the plane,
reached by the same branch" (d6:100–102). -/
noncomputable def liftVisit (v : (geoPositiveLift hn hG hT q).Γ.Visit) : Visit P :=
  Classical.choose (liftVisit_exists hn hG hT q v)

theorem liftVisit_fst (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (liftVisit hn hG hT q v).1 = parentCrossing hn hG hT q v :=
  (Classical.choose_spec (liftVisit_exists hn hG hT q v)).1

theorem liftVisit_block (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    ∃ r : ℕ, GeoBlockInterior hG.cg T q (liftEdge hn hG hT q v) r ∧
      (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q (liftEdge hn hG hT q v)) =
        Sum.inr (liftVisit hn hG hT q v) :=
  (Classical.choose_spec (liftVisit_exists hn hG hT q v)).2

theorem liftVisit_mem (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (liftVisit hn hG hT q v).1 ∈ geoCarrierCrossings hG.cg T q := by
  rw [liftVisit_fst]
  exact liftCrossing_mem hn hG hT q v

theorem liftVisit_owner (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    geoOwner hG.cg T (Sum.inr (liftVisit hn hG hT q v)) = q := by
  obtain ⟨r, -, hr⟩ := liftVisit_block hn hG hT q v
  rw [← hr, geo_pow_owner]
  exact geoOwner_geoCornerMark hG.cg T q _

theorem blockIndex_liftVisit (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    blockIndex hn hG hT q (Sum.inr (liftVisit hn hG hT q v)) = liftEdge hn hG hT q v := by
  obtain ⟨r, hb, hr⟩ := liftVisit_block hn hG hT q v
  exact blockIndex_eq hn hG hT q (liftVisit_owner hn hG hT q v) hb hr

/-- The parent visit lies on the parent edge of its block: the strand of the occurrence is a piece of
that parent edge. -/
theorem liftVisit_edge (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (liftVisit hn hG hT q v).2.val =
      (geoOutSlot hG.cg T (geoCornerMark hG.cg T q (liftEdge hn hG hT q v))).1 := by
  obtain ⟨r, hb, hr⟩ := liftVisit_block hn hG hT q v
  have hr1 : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, Equiv.Perm.one_apply] at hr
    have hcorner := isTrueCorner_geoCornerMark hG.cg T q (liftEdge hn hG hT q v)
    rw [hr] at hcorner
    exact liftCrossing_not_mem hn hG hT q v
      (liftVisit_fst hn hG hT q v ▸ (isTrueCorner_visit T _).mp hcorner)
  exact hb.visit_edge hG.cg T q hr1 hr

/-- The strand direction at an occurrence is a positive multiple of the direction of its parent edge
("smoothing performed at a different point … alters the curve only inside a disc containing no other
double point", d6:87–89; `geoCornerPolygon_edge_smul`). -/
theorem dir_liftVisit (v : (geoPositiveLift hn hG hT q).Γ.Visit) : ∃ t : ℝ, 0 < t ∧
    (geoPositiveLift hn hG hT q).Γ.dir v.2.val = t • edge P (liftVisit hn hG hT q v).2.val := by
  obtain ⟨t, ht, h⟩ := geoCornerPolygon_edge_smul hn hG.cg hT q (liftEdge hn hG hT q v)
  refine ⟨t, ht, ?_⟩
  rw [liftVisit_edge]
  exact h

/-- The corner coordinate of the parent visit is the traversal coordinate of the occurrence on the lift. -/
theorem cornerCoord_liftVisit (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    cornerCoord hn hG hT q (Sum.inr (liftVisit hn hG hT q v)) =
      (geoPositiveLift hn hG hT q).visitCoord v := by
  unfold cornerCoord
  rw [blockIndex_liftVisit]
  have hbp : blockParam hn hG hT q (Sum.inr (liftVisit hn hG hT q v)) =
      (geoPositiveLift hn hG hT q).crossingParam v.1 v.2.2 := by
    apply blockParam_eq hn hG hT q (liftVisit_owner hn hG hT q v)
    rw [blockIndex_liftVisit, geoMarkPosition_evaluation_visit, liftVisit_fst,
      crossingPoint_liftCrossing]
    exact ((geoPositiveLift hn hG hT q).crossingParam_spec v.1 v.2.2).2.2
  rw [hbp]
  rfl

/-- The other occurrence of the same double point names the twin visit: the two strands of a double
point of `Q` lie along the two parent edges of the crossing (transversality of the generic shadow). -/
theorem liftVisit_twin (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).twin v) = visitTwin (liftVisit hn hG hT q v) := by
  have hfst : (liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).twin v)).1 =
      (liftVisit hn hG hT q v).1 := by
    rw [liftVisit_fst, liftVisit_fst]
    rfl
  apply visitTwin_unique _ _ hfst
  intro heq
  obtain ⟨t, ht, h1⟩ := dir_liftVisit hn hG hT q v
  obtain ⟨t', ht', h2⟩ := dir_liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).twin v)
  rw [heq] at h2
  have hne : ((geoPositiveLift hn hG hT q).twin v).2.val ≠ v.2.val :=
    (geoPositiveLift hn hG hT q).Γ.other_ne v.1 v.2.2
  obtain ⟨hna, hmeet⟩ := (geoPositiveLift hn hG hT q).Γ.crossing_pair_spec v.1
    ((geoPositiveLift hn hG hT q).twin v).2.2 v.2.2 hne
  apply (geoPositiveLift hn hG hT q).generic.transverse _ _ hna hmeet
  rw [h2, h1, det_smul_left', det_smul_right', det_self']
  ring

theorem liftVisit_injective : Function.Injective (liftVisit hn hG hT q) := by
  intro v v' h
  have hx : v.1 = v'.1 := by
    apply (geoCarrierCrossingEquiv hn hG hT q).injective
    apply Subtype.ext
    have h1 := liftVisit_fst hn hG hT q v
    have h2 := liftVisit_fst hn hG hT q v'
    unfold parentCrossing at h1 h2
    rw [← h1, ← h2, h]
  rcases (geoPositiveLift hn hG hT q).eq_or_eq_twin v v' hx.symm with h' | h'
  · exact h'.symm
  · exfalso
    rw [h', liftVisit_twin] at h
    exact visitTwin_ne _ h.symm

theorem liftVisit_surjective {w : Visit P} (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    ∃ v, liftVisit hn hG hT q v = w := by
  let x : (geoPositiveLift hn hG hT q).Γ.Crossing := (geoCarrierCrossingEquiv hn hG hT q).symm ⟨w.1, hw⟩
  have hx : parentCrossing hn hG hT q ((geoPositiveLift hn hG hT q).overVisit x) = w.1 := by
    show ((geoCarrierCrossingEquiv hn hG hT q) x).1 = w.1
    rw [Equiv.apply_symm_apply]
  have h1 : w.1 = (liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).overVisit x)).1 := by
    rw [liftVisit_fst, hx]
  rcases visit_eq_or_twin _ w h1 with h | h
  · exact ⟨_, h.symm⟩
  · exact ⟨(geoPositiveLift hn hG hT q).twin ((geoPositiveLift hn hG hT q).overVisit x),
      by rw [liftVisit_twin, h]⟩

/-- **Same double points** (d6:76–82): the occurrences of the lift of `q` correspond bijectively to the
visits of the retained crossings of `q`, by the parent-visit map. -/
noncomputable def liftVisitEquiv :
    (geoPositiveLift hn hG hT q).Γ.Visit ≃ {w : Visit P // w.1 ∈ geoCarrierCrossings hG.cg T q} :=
  Equiv.ofBijective (fun v => ⟨liftVisit hn hG hT q v, liftVisit_mem hn hG hT q v⟩)
    ⟨fun v v' h => liftVisit_injective hn hG hT q (congrArg Subtype.val h),
     fun w => by
      obtain ⟨v, hv⟩ := liftVisit_surjective hn hG hT q w.2
      exact ⟨v, Subtype.ext hv⟩⟩

@[simp] theorem liftVisitEquiv_apply_val (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (liftVisitEquiv hn hG hT q v).1 = liftVisit hn hG hT q v := rfl

theorem liftVisit_symm (w : {w : Visit P // w.1 ∈ geoCarrierCrossings hG.cg T q}) :
    liftVisit hn hG hT q ((liftVisitEquiv hn hG hT q).symm w) = w.1 :=
  congrArg Subtype.val ((liftVisitEquiv hn hG hT q).apply_symm_apply w)

/-! ### Over/under bits and the cyclic order, read on the parent -/

/-- The divide convention at an occurrence of the lift: the occurrence is the over position exactly when
the determinant of its own strand direction with the other strand's direction is positive. -/
theorem isOver_iff_det_pos (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (geoPositiveLift hn hG hT q).isOver v ↔
      0 < det ((geoPositiveLift hn hG hT q).Γ.dir v.2.val)
        ((geoPositiveLift hn hG hT q).Γ.dir ((geoPositiveLift hn hG hT q).twin v).2.val) := by
  have hpos : 0 < det ((geoPositiveLift hn hG hT q).Γ.dir ((geoPositiveLift hn hG hT q).overStrand v.1))
      ((geoPositiveLift hn hG hT q).Γ.dir ((geoPositiveLift hn hG hT q).underStrand v.1)) :=
    Shadow.positiveDiagram_det_pos (geoCarrierShadow hn hG hT q) (geoCarrierShadow_generic hn hG hT q) v.1
  rcases (geoPositiveLift hn hG hT q).visit_eq_over_or_under v with h | h
  · rw [h, Diagram.twin_overVisit]
    exact iff_of_true ((geoPositiveLift hn hG hT q).isOver_overVisit v.1) hpos
  · rw [h, Diagram.twin_underVisit]
    refine iff_of_false ((geoPositiveLift hn hG hT q).not_isOver_underVisit v.1) ?_
    intro h'
    change 0 < det ((geoPositiveLift hn hG hT q).Γ.dir ((geoPositiveLift hn hG hT q).underStrand v.1))
      ((geoPositiveLift hn hG hT q).Γ.dir ((geoPositiveLift hn hG hT q).overStrand v.1)) at h'
    rw [det_swap] at h'
    linarith

theorem det_dir_eq (v : (geoPositiveLift hn hG hT q).Γ.Visit) : ∃ t : ℝ, 0 < t ∧
    det ((geoPositiveLift hn hG hT q).Γ.dir v.2.val)
        ((geoPositiveLift hn hG hT q).Γ.dir ((geoPositiveLift hn hG hT q).twin v).2.val) =
      t * det (edge P (liftVisit hn hG hT q v).2.val) (edge P (visitTwin (liftVisit hn hG hT q v)).2.val) := by
  obtain ⟨t1, ht1, h1⟩ := dir_liftVisit hn hG hT q v
  obtain ⟨t2, ht2, h2⟩ := dir_liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).twin v)
  rw [liftVisit_twin] at h2
  refine ⟨t1 * t2, mul_pos ht1 ht2, ?_⟩
  rw [h1, h2, det_smul_left', det_smul_right']
  ring

/-- **Same over/under** (d6:84–90): the over/under bit of an occurrence of the lift is the divide
convention read on the parent's two branch directions at its visit, `det(edge P v, edge P (twin v)) > 0`
— unchanged by any smoothing performed at another point. -/
theorem overBit_eq_true_iff_parent (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (geoPositiveLift hn hG hT q).overBit v = true ↔
      0 < det (edge P (liftVisit hn hG hT q v).2.val) (edge P (visitTwin (liftVisit hn hG hT q v)).2.val) := by
  rw [Diagram.overBit_eq_true_iff, isOver_iff_det_pos]
  obtain ⟨t, ht, h⟩ := det_dir_eq hn hG hT q v
  rw [h]
  exact ⟨fun hp => (pos_iff_pos_of_mul_pos hp).mp ht, fun hp => mul_pos ht hp⟩

/-- **Same cyclic order** (d6:92–96): three occurrences of the lift occur in a cyclic order along its
traversal circle (the corner polygon of `q`) exactly when their parent visits occur in that cyclic order
on `Γ` (`geometricVisitKey`, the traversal coordinate on `Γ`) — lem:carrierword at `T`, through §3. -/
theorem visitBetween_iff_key (v w u : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (geoPositiveLift hn hG hT q).VisitBetween v w u ↔
      cycBetween (geometricVisitKey hG.cg (liftVisit hn hG hT q v))
        (geometricVisitKey hG.cg (liftVisit hn hG hT q w))
        (geometricVisitKey hG.cg (liftVisit hn hG hT q u)) := by
  show cycBetween ((geoPositiveLift hn hG hT q).visitCoord v) ((geoPositiveLift hn hG hT q).visitCoord w)
    ((geoPositiveLift hn hG hT q).visitCoord u) ↔ _
  rw [← cornerCoord_liftVisit hn hG hT q v, ← cornerCoord_liftVisit hn hG hT q w,
    ← cornerCoord_liftVisit hn hG hT q u]
  exact cornerCoord_cycBetween_iff_key hn hG hT q (liftVisit_owner hn hG hT q v)
    (liftVisit_owner hn hG hT q w) (liftVisit_owner hn hG hT q u)

end LiftVisit

/-! ## 5. Two carriers with the same retained crossings have record-isomorphic lifts

"The two records are not equal: their traversal circles are different circles … What the three
paragraphs give is the map" (d6:98–108). The map is the identity on parent visits
(`liftVisitTransfer`); clauses (a)–(d) of def:record are §4's four lemmas; the named record isomorphism
is assembled by the accepted `CV.recordIsoOfData` (row 140, Gap G13). -/

section TwoLifts

variable (hn : 3 ≤ n) (hG : CarrierGeometry P) {T T' : Finset (Crossing P)}
  (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG.cg T') (q : GeoComponent hG.cg T)
  (q' : GeoComponent hG.cg T')

/-- "the identity map on the visits of `H`" (d6:67): the bijection of occurrences of the two lifts fixing
the parent visit. -/
noncomputable def liftVisitTransfer (h : geoCarrierCrossings hG.cg T q = geoCarrierCrossings hG.cg T' q') :
    (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG hT' q').Γ.Visit :=
  (liftVisitEquiv hn hG hT q).trans
    ((Equiv.subtypeEquivRight fun w => by rw [h]).trans (liftVisitEquiv hn hG hT' q').symm)

theorem liftVisit_liftVisitTransfer (h : geoCarrierCrossings hG.cg T q = geoCarrierCrossings hG.cg T' q')
    (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    liftVisit hn hG hT' q' (liftVisitTransfer hn hG hT hT' q q' h v) = liftVisit hn hG hT q v := by
  show liftVisit hn hG hT' q' ((liftVisitEquiv hn hG hT' q').symm _) = _
  rw [liftVisit_symm]
  rfl

/-- **The general theorem behind lem:pieceintrinsic.** Two carriers `q` of `T` and `q'` of `T'` (both
independent) with the same retained crossings have record-isomorphic positive lifts, the isomorphism
being the identity on parent visits: (a) cyclic order (`visitBetween_iff_key`), (b) double points
(`liftVisit_twin`), (c) over/under (`overBit_eq_true_iff_parent`), (d) signs (all `+1`), assembled by
`CV.recordIsoOfData` (def:record, row 140). -/
theorem exists_recordIso_of_geoCarrierCrossings_eq
    (h : geoCarrierCrossings hG.cg T q = geoCarrierCrossings hG.cg T' q') :
    ∃ ι : RecordIso (geoPositiveLift hn hG hT q).record (geoPositiveLift hn hG hT' q').record,
      ∀ v, liftVisit hn hG hT' q' (ι.Φ v) = liftVisit hn hG hT q v := by
  have hΦ : ∀ v, liftVisit hn hG hT' q' (liftVisitTransfer hn hG hT hT' q q' h v) =
      liftVisit hn hG hT q v := liftVisit_liftVisitTransfer hn hG hT hT' q q' h
  have hdata : IsRecordIsoData (geoPositiveLift hn hG hT q) (geoPositiveLift hn hG hT' q')
      (liftVisitTransfer hn hG hT hT' q q' h) :=
    { cyclic_order := fun v w u hb => by
        rw [visitBetween_iff_key, hΦ, hΦ, hΦ]
        exact (visitBetween_iff_key hn hG hT q v w u).mp hb
      double_points :=
        (carriesDoublePoints_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG hT' q').record) (liftVisitTransfer hn hG hT hT' q q' h)).2
          fun v => by
            apply liftVisit_injective hn hG hT' q'
            change liftVisit hn hG hT' q'
                (liftVisitTransfer hn hG hT hT' q q' h ((geoPositiveLift hn hG hT q).twin v)) =
              liftVisit hn hG hT' q'
                ((geoPositiveLift hn hG hT' q').twin (liftVisitTransfer hn hG hT hT' q q' h v))
            rw [hΦ, liftVisit_twin hn hG hT q, liftVisit_twin hn hG hT' q', hΦ]
      over_under :=
        (carriesOverUnder_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG hT' q').record) (liftVisitTransfer hn hG hT hT' q q' h)).2
          fun v => by
            change (geoPositiveLift hn hG hT' q').overBit (liftVisitTransfer hn hG hT hT' q q' h v) =
              (geoPositiveLift hn hG hT q).overBit v
            rw [Bool.eq_iff_iff, overBit_eq_true_iff_parent, overBit_eq_true_iff_parent, hΦ]
      signs := fun v => by
        change (geoPositiveLift hn hG hT' q').sign (liftVisitTransfer hn hG hT hT' q q' h v).1 =
          (geoPositiveLift hn hG hT q).sign v.1
        rw [geoPositiveLift_sign, geoPositiveLift_sign] }
  exact ⟨recordIsoOfData (geoPositiveLift_componentCount hn hG hT q)
    (geoPositiveLift_componentCount hn hG hT' q') (liftVisitTransfer hn hG hT hT' q q' h) hdata, hΦ⟩

end TwoLifts

/-! ## 6. Row 156 — CV:lem:pieceintrinsic (d6_vertexedge.tex:56–74)

Printed statement: "Let `P` be generic, `S ∈ Ind(G_P)`, and let `H` be a residual piece of `S`, carried
by the carrier `L` (Lemma lem:carriers (iv)). Let `D_L(H)` be the diagram obtained from `L` by retaining
exactly the crossings of `H`, each resolved by the divide convention of Definition def:piecediagram, and
erasing all others; and let `D_P(H)` be the intrinsic piece diagram of that definition, obtained from the
parent polygon `P` by retaining exactly the same crossings under the same convention. Throughout, that a
crossing *lies on* a carrier means that both of its traversal preimages belong to that carrier, which is
the condition Lemma lem:carriers (iv) supplies. Then the identity map on the visits of `H` is a record
isomorphism (Definition def:record) from the record of `D_L(H)` to the record of `D_P(H)`. Consequently
they present the same oriented link (Axiom ax:gausscode), so `P_{D_L(H)} = P_H`, `w(D_L(H)) = |H|`." -/

section Row

variable (hn : 3 ≤ n) (hD : Diagrammatic P) (S : Finset (Crossing P)) (H : Piece hD.crossingGeometry S)

/-- "the diagram obtained from `L` by retaining exactly the crossings of `H`, each resolved by the divide
convention of Definition def:piecediagram, and erasing all others" (d6:59–62), reading (ii): the erased
double points form an admissible set `K` of Step 5 of lem:piececurve (`StepInvariant`: every erased
double point is undominated and outside `H`, and `S ∪ K ∈ Ind(G_P)`), and `q` is a carrier of `S ∪ K`
retaining exactly the crossings of `H`. Every such `q` lies inside `L` (`IsCarrierRestriction.owner_eq`). -/
structure IsCarrierRestriction (K : Finset (Crossing P))
    (q : GeoComponent hD.crossingGeometry (S ∪ K)) : Prop where
  /-- the erased double points: undominated, outside `H`, and `S ∪ K` independent -/
  erased : StepInvariant hD.crossingGeometry S H K
  /-- "retaining exactly the crossings of `H`" -/
  retained : geoCarrierCrossings hD.crossingGeometry (S ∪ K) q = pieceLabels hD.crossingGeometry S H

theorem IsCarrierRestriction.geoIndependent {K : Finset (Crossing P)}
    {q : GeoComponent hD.crossingGeometry (S ∪ K)} (h : IsCarrierRestriction hD S H K q) :
    GeoIndependent hD.crossingGeometry (S ∪ K) :=
  geoIndependent_of_mem_Ind hD.crossingGeometry h.erased.indep

/-- **`D_L(H)`**: the positive lift ("each resolved by the divide convention") of the carrier `q` of
`S ∪ K` retaining exactly the crossings of `H`. -/
noncomputable def carrierRestriction {K : Finset (Crossing P)}
    {q : GeoComponent hD.crossingGeometry (S ∪ K)} (h : IsCarrierRestriction hD S H K q) : Diagram :=
  geoPositiveLift hn (CarrierGeometry.ofDiagrammatic hD) h.geoIndependent q

/-- The parent visit of an occurrence of `D_L(H)` ("the visits of `H`"). -/
noncomputable def restrictionVisit {K : Finset (Crossing P)}
    {q : GeoComponent hD.crossingGeometry (S ∪ K)} (h : IsCarrierRestriction hD S H K q) :
    (carrierRestriction hn hD S H h).Γ.Visit → Visit P :=
  liftVisit hn (CarrierGeometry.ofDiagrammatic hD) h.geoIndependent q

/-- The parent visit of an occurrence of `D_P(H) = pieceDiagram H`. -/
noncomputable def pieceVisit (hS : S ∈ Ind hD.crossingGeometry) :
    (pieceDiagram hn hD hS H).Γ.Visit → Visit P :=
  liftVisit hn (CarrierGeometry.ofDiagrammatic hD) (pieceSupport_geoIndependent hD hS H)
    (pieceCarrier hD hS H)

/-- `D_L(H)` lies inside `L`: every mark of `q` is a mark of the carrier `L = pieceOwner H` of `S`
(lem:carrierword's refinement clause and lem:carriers (iv)). -/
theorem IsCarrierRestriction.owner_eq (hS : S ∈ Ind hD.crossingGeometry) {K : Finset (Crossing P)}
    {q : GeoComponent hD.crossingGeometry (S ∪ K)} (h : IsCarrierRestriction hD S H K q) (m : Mark P)
    (hm : geoOwner hD.crossingGeometry (S ∪ K) m = q) :
    geoOwner hD.crossingGeometry S m = pieceOwner hD.crossingGeometry hS H := by
  obtain ⟨q₀, hq₀⟩ := carrierword_refines hD.crossingGeometry h.erased.indep
    Finset.subset_union_left q
  rw [hq₀ m hm]
  apply pieceOwner_unique hD.crossingGeometry hS H q₀
  intro c hc v hv
  apply hq₀
  have hc' : c ∈ geoCarrierCrossings hD.crossingGeometry (S ∪ K) q := by
    rw [h.retained]
    exact hc
  exact ((mem_geoCarrierCrossings hD.crossingGeometry (S ∪ K) q c).mp hc').2 v hv

/-- `D_P(H)` is itself obtained by the erasing route: `K = pieceSupport H`, `q = pieceCarrier H`. -/
theorem isCarrierRestriction_pieceSupport (hS : S ∈ Ind hD.crossingGeometry) :
    IsCarrierRestriction hD S H (pieceSupport hD hS H) (pieceCarrier hD hS H) :=
  ⟨pieceSupport_stepInvariant hD hS H, pieceCarrier_geoCarrierCrossings hD hS H⟩

theorem carrierRestriction_pieceSupport (hS : S ∈ Ind hD.crossingGeometry) :
    carrierRestriction hn hD S H (isCarrierRestriction_pieceSupport hD S H hS) = pieceDiagram hn hD hS H :=
  rfl

/-- **The record isomorphism of lem:pieceintrinsic**: for every `D_L(H)`, the identity on the visits of
`H` is a named record isomorphism from the record of `D_L(H)` to the record of `D_P(H)`. -/
theorem carrierRestriction_recordIso (hS : S ∈ Ind hD.crossingGeometry) {K : Finset (Crossing P)}
    {q : GeoComponent hD.crossingGeometry (S ∪ K)} (h : IsCarrierRestriction hD S H K q) :
    ∃ ι : RecordIso (carrierRestriction hn hD S H h).record (pieceDiagram hn hD hS H).record,
      ∀ v, pieceVisit hn hD S H hS (ι.Φ v) = restrictionVisit hn hD S H h v :=
  exists_recordIso_of_geoCarrierCrossings_eq hn (CarrierGeometry.ofDiagrammatic hD) h.geoIndependent
    (pieceSupport_geoIndependent hD hS H) q (pieceCarrier hD hS H)
    (h.retained.trans (pieceCarrier_geoCarrierCrossings hD hS H).symm)

/-- CV:lem:pieceintrinsic (d6_vertexedge.tex:56–74) as printed, one field per printed clause, on the
binder `hD : Diagrammatic P`, `S ∈ Ind(G_P)`, `H` a residual piece of `S` (the row `CV.pieceintrinsic`
instantiates it at the printed "Let `P` be generic", d6:58). `L = pieceOwner H` (lem:carriers (iv));
`D_L(H)` ranges over `carrierRestriction h`, `h : IsCarrierRestriction K q` (reading (ii), module
docstring); `D_P(H) = pieceDiagram hn hD hS H` (row 142); `hn : 3 ≤ n` is reading (iii). -/
structure PieceIntrinsicData (hS : S ∈ Ind hD.crossingGeometry) : Prop where
  /-- "Let `P` be generic, `S ∈ Ind(G_P)`, and let `H` be a residual piece of `S`, carried by the carrier
  `L` (Lemma lem:carriers (iv))" (d6:58–59); "Throughout, that a crossing *lies on* a carrier means that
  both of its traversal preimages belong to that carrier, which is the condition Lemma lem:carriers (iv)
  supplies" (d6:64–66): every crossing of `H` lies on `L = pieceOwner H` in that sense (it is a retained
  crossing of `L`: unselected, both visits on `L`), and `L` is the only carrier of `S` on which the visits
  of `H` lie -/
  carried :
    (∀ c ∈ pieceLabels hD.crossingGeometry S H,
      c ∈ geoCarrierCrossings hD.crossingGeometry S (pieceOwner hD.crossingGeometry hS H)) ∧
    ∀ q : GeoComponent hD.crossingGeometry S,
      (∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
        geoOwner hD.crossingGeometry S (Sum.inr v) = q) →
      q = pieceOwner hD.crossingGeometry hS H
  /-- "Let `D_L(H)` be the diagram obtained from `L` by retaining exactly the crossings of `H`, each
  resolved by the divide convention of Definition def:piecediagram, and erasing all others" (d6:59–62):
  such diagrams exist (the erasing route of lem:piececurve), and every one of them —
  `carrierRestriction h` for `h : IsCarrierRestriction K q` — is a one-component diagram lying inside `L`,
  whose crossings are exactly the crossings of `H`, every one resolved by the divide convention
  (`Diagram.IsPositive`) -/
  restriction :
    (∃ (K : Finset (Crossing P)) (q : GeoComponent hD.crossingGeometry (S ∪ K)),
      IsCarrierRestriction hD S H K q) ∧
    ∀ (K : Finset (Crossing P)) (q : GeoComponent hD.crossingGeometry (S ∪ K))
      (h : IsCarrierRestriction hD S H K q),
      (∀ m : Mark P, geoOwner hD.crossingGeometry (S ∪ K) m = q →
        geoOwner hD.crossingGeometry S m = pieceOwner hD.crossingGeometry hS H) ∧
      (carrierRestriction hn hD S H h).componentCount = 1 ∧
      Nonempty ((carrierRestriction hn hD S H h).Γ.Crossing ≃
        {c : Crossing P // c ∈ pieceLabels hD.crossingGeometry S H}) ∧
      ∀ x, (carrierRestriction hn hD S H h).IsPositive x
  /-- "and let `D_P(H)` be the intrinsic piece diagram of that definition, obtained from the parent
  polygon `P` by retaining exactly the same crossings under the same convention" (d6:62–64):
  `D_P(H) = pieceDiagram H` (row 142) is a one-component diagram whose crossings are exactly those of `H`,
  all resolved by the divide convention; it is itself one of the diagrams of the erasing route
  (`pieceSupport`, `pieceCarrier`) -/
  intrinsic :
    (pieceDiagram hn hD hS H).componentCount = 1 ∧
    Nonempty ((pieceDiagram hn hD hS H).Γ.Crossing ≃
      {c : Crossing P // c ∈ pieceLabels hD.crossingGeometry S H}) ∧
    (∀ x, (pieceDiagram hn hD hS H).IsPositive x) ∧
    ∃ h : IsCarrierRestriction hD S H (pieceSupport hD hS H) (pieceCarrier hD hS H),
      carrierRestriction hn hD S H h = pieceDiagram hn hD hS H
  /-- "Then the identity map on the visits of `H` is a record isomorphism (Definition def:record) from
  the record of `D_L(H)` to the record of `D_P(H)`" (d6:67–69): for every `D_L(H)` a named record
  isomorphism `ι` (SM `RecordIso` = CV def:record's (a)–(d), row 140) from `(D_L(H)).record` to
  `(D_P(H)).record` whose bijection of marked points fixes the visit of `H`: `ι.Φ v` is the same visit
  of `H` as `v` -/
  record_iso : ∀ (K : Finset (Crossing P)) (q : GeoComponent hD.crossingGeometry (S ∪ K))
    (h : IsCarrierRestriction hD S H K q),
    ∃ ι : RecordIso (carrierRestriction hn hD S H h).record (pieceDiagram hn hD hS H).record,
      ∀ v, pieceVisit hn hD S H hS (ι.Φ v) = restrictionVisit hn hD S H h v
  /-- "Consequently they present the same oriented link (Axiom ax:gausscode)" (d6:69–70), in the form of
  row 163's F4 replacement (`CV.gausscode_polynomial`): the HOMFLY–PT polynomials of `D_L(H)` and
  `D_P(H)` agree -/
  same_link : ∀ (K : Finset (Crossing P)) (q : GeoComponent hD.crossingGeometry (S ∪ K))
    (h : IsCarrierRestriction hD S H K q),
    homfly (carrierRestriction hn hD S H h) = homfly (pieceDiagram hn hD hS H)
  /-- "so `P_{D_L(H)} = P_H`" (d6:72), `P_H = pieceHomfly H` (row 142) -/
  polynomial : ∀ (K : Finset (Crossing P)) (q : GeoComponent hD.crossingGeometry (S ∪ K))
    (h : IsCarrierRestriction hD S H K q),
    homfly (carrierRestriction hn hD S H h) = pieceHomfly hn hD hS H
  /-- "`w(D_L(H)) = |H|`" (d6:72): the writhe of `D_L(H)` is the number of crossings of `H`
  (`= pieceWrithe H`, rows 139/142) -/
  writhe : ∀ (K : Finset (Crossing P)) (q : GeoComponent hD.crossingGeometry (S ∪ K))
    (h : IsCarrierRestriction hD S H K q),
    (carrierRestriction hn hD S H h).writhe = ((pieceLabels hD.crossingGeometry S H).card : ℤ) ∧
    (carrierRestriction hn hD S H h).writhe = pieceWrithe hD.crossingGeometry S H

/-- Row 156 on the binder `hD : Diagrammatic P` (the working form; the row is its generic instance). -/
theorem pieceintrinsic_of_diagrammatic (hS : S ∈ Ind hD.crossingGeometry) :
    PieceIntrinsicData hn hD S H hS where
  carried :=
    ⟨fun c hc => (mem_geoCarrierCrossings hD.crossingGeometry S _ c).mpr
      ⟨((mem_U_iff hD.crossingGeometry S c).mp (pieceLabels_subset hD.crossingGeometry S H hc)).1,
        pieceOwner_spec hD.crossingGeometry hS H c hc⟩,
     fun q hq => pieceOwner_unique hD.crossingGeometry hS H q hq⟩
  restriction :=
    ⟨⟨_, _, isCarrierRestriction_pieceSupport hD S H hS⟩, fun K q h =>
      ⟨IsCarrierRestriction.owner_eq hD S H hS h, rfl,
        ⟨(geoCarrierCrossingEquiv hn (CarrierGeometry.ofDiagrammatic hD) h.geoIndependent q).trans
          (Equiv.subtypeEquivRight fun c => by rw [h.retained])⟩,
        geoPositiveLift_isPositive hn _ _ q⟩⟩
  intrinsic :=
    ⟨rfl, ⟨pieceDiagramCrossingEquiv hn hD hS H⟩, pieceDiagram_isPositive hn hD hS H,
      ⟨isCarrierRestriction_pieceSupport hD S H hS, rfl⟩⟩
  record_iso := fun _ _ h => carrierRestriction_recordIso hn hD S H hS h
  same_link := fun _ _ h => by
    obtain ⟨ι, -⟩ := carrierRestriction_recordIso hn hD S H hS h
    exact gausscode_polynomial _ _ rfl rfl ι
  polynomial := fun _ _ h => by
    obtain ⟨ι, -⟩ := carrierRestriction_recordIso hn hD S H hS h
    exact gausscode_polynomial _ _ rfl rfl ι
  writhe := fun _ _ h =>
    ⟨by rw [carrierRestriction, geoPositiveLift_writhe, h.retained],
     by rw [carrierRestriction, geoPositiveLift_writhe, h.retained]; rfl⟩

end Row

/-- **Row 156, CV:lem:pieceintrinsic** (d6_vertexedge.tex:56–74), on the printed binder "Let `P` be
generic" (d6:58): `hG : CV.Generic P`, `S ∈ Ind(G_P)`, `H` a residual piece of `S`. The diagrammatic
form `pieceintrinsic_of_diagrammatic` is instantiated through `CV.Generic.diagrammatic hn` (CV's standing
`n ≥ 3`, d1:932), exactly as `CV.carrierword_generic` instantiates row 137. -/
theorem pieceintrinsic (hn : 3 ≤ n) (hG : Generic P) (S : Finset (Crossing P))
    (hS : S ∈ Ind hG.crossingGeometry) (H : Piece hG.crossingGeometry S) :
    PieceIntrinsicData hn (hG.diagrammatic hn) S H hS :=
  pieceintrinsic_of_diagrammatic hn (hG.diagrammatic hn) S H hS

end CV
