import SM.LinkDiagram
import SM.CarrierCornerPolygon
import SM.CarrierSelfIntersections
import SM.CarriersLemma
import SM.UniformDefinition

/-! # The positive lift of a carrier (def:positive-lift, sm-3:325-335)

Source: reference/SM/sm-3-statesum.tex, frame SM15, def:positive-lift (lines 325-335):

"An oriented link diagram in the plane is a finite collection of closed oriented curves with
finitely many transverse double points, no triple points, and at each double point a choice of
the over strand. A double point with over-strand direction u_o and under-strand direction u_u is
positive if det(u_o,u_u)>0 and negative otherwise. The positive lift of a subpolygon Q is the
oriented knot diagram whose curve is Q, whose double points are the crossings of Q, and in which
at every double point the over strand is chosen so that the crossing is positive. Its writhe (the
sum of crossing signs) is m_Q."

The subpolygons Q are the carriers of lem:carriers (sm-3:54-95), accepted as `SM.carriers_lemma`
with the bundle `CarriersLemmaData`; a carrier `q : Carrier.Component hn hP S` is read as its
corner polygon `Carrier.ccpCornerPolygon hn hP S q` (lem:carriers (ii): "Every carrier has nonzero
edges, at least three corners, and no antiparallel consecutive directions", sm-3:72-73), and its
crossings are `Carrier.carrierCrossings hn hP S q` with `m_Q = Carrier.carrierCrossingCount hn hP S q`
(def:smoothing).  lem:carriers (iii) (sm-3:84-86): "A carrier's self-intersections are exactly the
unselected crossings both of whose visits are assigned to it. They are transverse, none is a
corner, and no carrier has a triple point."

Layer: the Chapter-3 representation layer `SM.Link` (work/lean/SM/LinkDiagram.lean:
`PolyComp`, `Shadow`, `Shadow.single`, `Shadow.Generic`, `Diagram`, `IsPositive`, `sign`,
`writhe`), following work/reports/design-decision-diagram-record-20260913.md, section
positive_lift_and_carriers ("CarrierGeneric", `positiveLift`, the crossing correspondence and
"writhe = m_Q").

Main declarations (all in `SM.Link`):
* `Shadow.Generic.exists_positive_strand`, `Shadow.positiveDiagram` — on any generic shadow the
  over strand can be chosen so that every crossing is positive (the general form of the third
  sentence of def:positive-lift);
* `Shadow.single_generic_of` — the label-level criterion for genericity of a one-component shadow;
* `carrierPolyComp`, `carrierShadow` — the carrier `Q` as a one-component shadow;
* `carrierShadow_generic` — "CarrierGeneric": the shadow of a carrier of a decomposition is
  generic (from lem:carriers (ii) and (iii), through the block parametrization of the corner
  polygon by the inherited straight subsegments);
* `positiveLift` — the positive lift, with `positiveLift_isPositive`, `positiveLift_sign`,
  `positiveLift_writhe`;
* `carrierCrossingEquiv` — the crossings of the lift are the crossings of `Q`
  (`carrierCrossings hn hP S q`), and `positiveLift_writhe_eq_carrierCrossingCount` — "Its writhe
  (the sum of crossing signs) is m_Q".

Deviation from the requested signature: `carrierShadow` takes the decomposition hypothesis `hS`
(as does `positiveLift`), because the component bound `3 ≤ k` is lem:carriers (ii) and holds only
for independent `S` (`ccpCornerCount_ge_three hn hP hS q`). -/

namespace SM.Link

open SM Carrier

noncomputable section

/-! ## The positive over-strand choice on a generic shadow -/

namespace Shadow

variable {Γ : Shadow}

/-- On a generic shadow every crossing has a strand `s` whose direction makes a positive
determinant with the direction of the other strand: this is the strand that def:positive-lift
(sm-3:333-334) chooses as over strand, "so that the crossing is positive". -/
theorem Generic.exists_positive_strand (hΓ : Γ.Generic) (x : Γ.Crossing) :
    ∃ s : Γ.Strand, ∃ hs : s ∈ x.val, 0 < det (Γ.dir s) (Γ.dir (Γ.other x hs)) := by
  obtain ⟨s, t, hx, hna, hmeet⟩ := x.2
  have hs : s ∈ x.val := by rw [hx]; simp
  have ht : t ∈ x.val := by rw [hx]; simp
  have hne : t ≠ s := (Γ.ne_of_not_adjacent hna).symm
  have hts : Γ.other x hs = t := (Γ.eq_other_of_mem_of_ne x hs ht hne).symm
  have hst : Γ.other x ht = s :=
    (Γ.eq_other_of_mem_of_ne x ht hs (Γ.ne_of_not_adjacent hna)).symm
  have hd : det (Γ.dir s) (Γ.dir t) ≠ 0 := hΓ.transverse s t hna hmeet
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · refine ⟨t, ht, ?_⟩
    rw [hst, det_swap]
    exact neg_pos.mpr hneg
  · exact ⟨s, hs, by rw [hts]; exact hpos⟩

end Shadow

/-- def:positive-lift (sm-3:333-334), general form: the diagram on a generic shadow `Γ` "in which
at every double point the over strand is chosen so that the crossing is positive". -/
def Shadow.positiveDiagram (Γ : Shadow) (hΓ : Γ.Generic) : Diagram where
  Γ := Γ
  generic := hΓ
  overStrand := fun x => Classical.choose (hΓ.exists_positive_strand x)
  over_mem := fun x => Classical.choose (Classical.choose_spec (hΓ.exists_positive_strand x))

namespace Shadow

variable (Γ : Shadow) (hΓ : Γ.Generic)

@[simp] theorem positiveDiagram_Γ : (Γ.positiveDiagram hΓ).Γ = Γ := rfl

theorem positiveDiagram_det_pos (x : Γ.Crossing) :
    0 < det (Γ.dir ((Γ.positiveDiagram hΓ).overStrand x))
      (Γ.dir (Γ.other x ((Γ.positiveDiagram hΓ).over_mem x))) :=
  Classical.choose_spec (Classical.choose_spec (hΓ.exists_positive_strand x))

/-- Every crossing of the positive diagram is positive. -/
theorem positiveDiagram_isPositive (x : Γ.Crossing) : (Γ.positiveDiagram hΓ).IsPositive x :=
  Γ.positiveDiagram_det_pos hΓ x

theorem positiveDiagram_sign (x : Γ.Crossing) : (Γ.positiveDiagram hΓ).sign x = 1 :=
  ((Γ.positiveDiagram hΓ).isPositive_iff_sign_eq_one x).mp (Γ.positiveDiagram_isPositive hΓ x)

/-- The writhe of the positive diagram is its number of crossings. -/
theorem positiveDiagram_writhe :
    (Γ.positiveDiagram hΓ).writhe = Fintype.card Γ.Crossing := by
  have h : ∀ x : Γ.Crossing, ((Γ.positiveDiagram hΓ).sign x : ℤ) = 1 := fun x => by
    rw [positiveDiagram_sign]
    rfl
  change ∑ x : Γ.Crossing, ((Γ.positiveDiagram hΓ).sign x : ℤ) = _
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]

/-- The positive diagram is the unique diagram on `Γ` all of whose crossings are positive. -/
theorem eq_positiveDiagram_of_isPositive (D : Diagram) (hD : D.Γ = Γ)
    (hpos : ∀ x, D.IsPositive x) : D = Γ.positiveDiagram hΓ := by
  subst hD
  have h : D.overStrand = (D.Γ.positiveDiagram hΓ).overStrand := by
    funext x
    by_contra hne
    have h1 := D.Γ.positiveDiagram_det_pos hΓ x
    have h2 := hpos x
    unfold Diagram.IsPositive at h2
    have hmem := (D.Γ.positiveDiagram hΓ).over_mem x
    have hu : (D.Γ.positiveDiagram hΓ).overStrand x = D.underStrand x :=
      D.eq_under_of_mem_of_ne x hmem (fun h => hne h.symm)
    have hother : D.Γ.other x hmem = D.overStrand x := by
      have h3 := D.Γ.other_other x (D.over_mem x)
      rw [← h3]
      congr 1
    have h1' : 0 < det (D.Γ.dir (D.underStrand x)) (D.Γ.dir (D.overStrand x)) := by
      rw [← hu, ← hother]
      exact h1
    rw [det_swap] at h1'
    linarith
  calc D = D.withOver D.overStrand D.over_mem := rfl
    _ = D.withOver (D.Γ.positiveDiagram hΓ).overStrand (D.Γ.positiveDiagram hΓ).over_mem :=
        D.withOver_congr h _ _
    _ = D.Γ.positiveDiagram hΓ := rfl

/-! ## Genericity of a one-component shadow from label-level facts -/

/-- The label-level form of `Shadow.Generic` for a one-component shadow `single C`: regularity
of the polygon, no vertex on a non-incident closed edge, transversality of meeting non-adjacent
edges, and no point interior to three distinct edges.  (`single_generic_of_generic` is the
special case of an accepted generic polygon.) -/
theorem single_generic_of (C : PolyComp) (hreg : Regular C.P)
    (htail : ∀ a b : ZMod C.k, ¬ incident a b → C.P a ∉ edgeSegment C.P b)
    (htrans : ∀ a b : ZMod C.k, ¬ adjacent a b → (edgeSegment C.P a ∩ edgeSegment C.P b).Nonempty →
      det (edge C.P a) (edge C.P b) ≠ 0)
    (htriple : ¬ ∃ a b c : ZMod C.k, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (edgeInterior C.P a ∩ edgeInterior C.P b ∩ edgeInterior C.P c).Nonempty) :
    (single C).Generic where
  regular := fun _ => hreg
  tail_off := by
    intro s t hinc hmem
    rw [single_incidentTail_iff] at hinc
    rw [single_seg] at hmem
    exact htail _ _ hinc hmem
  transverse := by
    intro s t hna hmeet
    rw [single_adjacent_iff] at hna
    rw [single_seg, single_seg] at hmeet
    rw [single_dir, single_dir]
    exact htrans _ _ hna hmeet
  no_triple := by
    rintro ⟨s, t, u, hst, htu, hsu, hne⟩
    apply htriple
    refine ⟨singleStrandEquiv C s, singleStrandEquiv C t, singleStrandEquiv C u,
      fun h => hst ((singleStrandEquiv C).injective h),
      fun h => htu ((singleStrandEquiv C).injective h),
      fun h => hsu ((singleStrandEquiv C).injective h), ?_⟩
    rw [single_interior, single_interior, single_interior] at hne
    exact hne

end Shadow

/-! ## Adjacency of edge labels: three sufficient conditions -/

theorem adjacent_of_eq {k : ℕ} {a b : ZMod k} (h : a = b) : adjacent a b :=
  Or.inr (Or.inl (by rw [h, sub_self]))

theorem adjacent_of_eq_add_one {k : ℕ} {a b : ZMod k} (h : a = b + 1) : adjacent a b :=
  Or.inl (by rw [h]; ring)

theorem adjacent_of_add_one_eq {k : ℕ} {a b : ZMod k} (h : a + 1 = b) : adjacent a b :=
  Or.inr (Or.inr (by rw [← h]; ring))

/-! ## The carrier as a one-component shadow -/

variable {n : ℕ} [NeZero n]

/-- The subpolygon `Q` of def:positive-lift ("whose curve is Q", sm-3:332) as one component:
the corner polygon `ccpCornerPolygon hn hP S q` of the carrier `q` of the decomposition `S`
(lem:carriers, sm-3:66-68: "tracing the resulting cycles by inherited straight subsegments, with
corners at original vertices and selected smoothing sites"), with its `k = ccpCornerCount`
corners; `3 ≤ k` is lem:carriers (ii) "at least three corners" (sm-3:72). -/
abbrev carrierPolyComp (hn : 3 ≤ n) {P : LabelledTuple n} (hP : SM.Generic P)
    (S : Finset (SM.Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) :
    PolyComp :=
  ⟨ccpCornerCount hn hP S q, ccpCornerCount_ge_three hn hP hS q, ccpCornerPolygon hn hP S q⟩

/-- The shadow of the positive lift of `Q` (def:positive-lift, sm-3:332: "the oriented knot
diagram whose curve is Q"): the one-component shadow of the corner polygon of the carrier `q`. -/
abbrev carrierShadow (hn : 3 ≤ n) {P : LabelledTuple n} (hP : SM.Generic P)
    (S : Finset (SM.Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) :
    Shadow :=
  Shadow.single (carrierPolyComp hn hP S q hS)

section CarrierGeneric

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : SM.Generic P) (S : Finset (SM.Crossing P))
  (q : Component hn hP S) (hS : IsDecomposition hn hP S)

theorem carrierPolyComp_k : (carrierPolyComp hn hP S q hS).k = ccpCornerCount hn hP S q := rfl

theorem carrierPolyComp_P : (carrierPolyComp hn hP S q hS).P = ccpCornerPolygon hn hP S q := rfl

theorem carrierShadow_c : (carrierShadow hn hP S q hS).c = 1 := rfl

theorem carrierShadow_comp (i : Fin 1) :
    (carrierShadow hn hP S q hS).comp i = carrierPolyComp hn hP S q hS := rfl

/-! ### The block parametrization of the corner polygon

`ccpCornerPolygon_block` (lem:carriers (ii)): from the corner `c_j = ccpCornerMark j` the next
corner `c_{j+1}` is reached in `m ≥ 1` steps of `ρ_S`, the intermediate marks being unselected
visits on the one original edge `e_j` of the outgoing slot of `c_j`, and the closed edge segment
`[Q j, Q (j+1)]` is the union of the `m` inherited straight subsegments.  We read points of the
edge segments as half-open carrier parameters (`IsCarrierParameter`, `carrierTrace`) to apply
lem:carriers (iii) as accepted in `CarrierSelfIntersections`. -/

/-- The interior marks of the block of the edge `j` of the corner polygon: the marks
`ρ_S^i c_j`, `1 ≤ i ≤ r`, are unselected visits on the original edge `e_j` of the outgoing slot of
`c_j` (lem:carriers, sm-3:66-68: the carrier is traced "by inherited straight subsegments, with
corners at original vertices and selected smoothing sites" — the marks strictly between two
consecutive corners are the unselected crossing visits passed on one original edge). -/
def BlockInterior (j : ZMod (ccpCornerCount hn hP S q)) (r : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ r → ∃ v : SM.Visit P,
    (smoothingSuccessor hn hP S ^ i) (ccpCornerMark hn hP S q j) = Sum.inr v ∧ v.1 ∉ S ∧
      v.2.val = (ccpOutSlot hn hP S (ccpCornerMark hn hP S q j)).1

theorem BlockInterior.mono {j : ZMod (ccpCornerCount hn hP S q)} {r r' : ℕ} (h : r' ≤ r)
    (hb : BlockInterior hn hP S q j r) : BlockInterior hn hP S q j r' :=
  fun i h1 hi => hb i h1 (hi.trans h)

/-- The interior marks of a block are not true corners. -/
theorem BlockInterior.not_trueCorner {j : ZMod (ccpCornerCount hn hP S q)} {r : ℕ}
    (hb : BlockInterior hn hP S q j r) :
    ∀ i, 1 ≤ i → i ≤ r →
      ¬ IsTrueCorner S ((smoothingSuccessor hn hP S ^ i) (ccpCornerMark hn hP S q j)) := by
  intro i h1 hi hc
  obtain ⟨v, hv, hvS, -⟩ := hb i h1 hi
  rw [hv] at hc
  exact hvS ((isTrueCorner_visit S v).mp hc)

/-- A block mark that is a true corner is the starting corner (`r = 0`). -/
theorem BlockInterior.eq_zero_of_trueCorner {j : ZMod (ccpCornerCount hn hP S q)} {r : ℕ}
    (hb : BlockInterior hn hP S q j r)
    (hc : IsTrueCorner S ((smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q j))) :
    r = 0 := by
  by_contra hr
  exact hb.not_trueCorner hn hP S q r (Nat.one_le_iff_ne_zero.mpr hr) le_rfl hc

/-- A block mark that is a crossing visit `w` with `1 ≤ r` lies on the block's original edge. -/
theorem BlockInterior.visit_edge {j : ZMod (ccpCornerCount hn hP S q)} {r : ℕ}
    (hb : BlockInterior hn hP S q j r) (hr : 1 ≤ r) {w : SM.Visit P}
    (hw : (smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q j) = Sum.inr w) :
    w.2.val = (ccpOutSlot hn hP S (ccpCornerMark hn hP S q j)).1 := by
  obtain ⟨v, hv, -, hve⟩ := hb r hr le_rfl
  rw [hw] at hv
  rw [Sum.inr.inj hv]
  exact hve

/-- A block parameter `(ρ_S^r c_j, u)`, `u ∈ [0,1)`, is a carrier parameter of `q`. -/
theorem isCarrierParameter_block (j : ZMod (ccpCornerCount hn hP S q)) (r : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IsCarrierParameter hn hP S q ((smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q j), u) := by
  refine ⟨?_, hu0, hu1⟩
  show owner hn hP S _ = q
  rw [ccp_pow_owner]
  exact ccpCornerMark_owner hn hP S q j

/-- The corner `c_j` at parameter `0` is a carrier parameter tracing the corner point `Q j`. -/
theorem corner_param (j : ZMod (ccpCornerCount hn hP S q)) :
    IsCarrierParameter hn hP S q (ccpCornerMark hn hP S q j, 0) ∧
      carrierTrace hn hP S (ccpCornerMark hn hP S q j, 0) = ccpCornerPolygon hn hP S q j :=
  ⟨⟨ccpCornerMark_owner hn hP S q j, le_rfl, zero_lt_one⟩,
    (smoothingSegment_zero hn hP S _).trans (ccpCornerPolygon_apply hn hP S q j).symm⟩

/-- **Unique previous corner.**  Two true corners `c`, `c'` with `ρ_S^r c = ρ_S^{r'} c'` and no
true corner strictly after them within `r`, resp. `r'`, steps coincide, with `r = r'`. -/
theorem prevCorner_unique_of_le {c c' : Mark P} (hc : IsTrueCorner S c) {r r' : ℕ} (hrr : r ≤ r')
    (hr' : ∀ i, 1 ≤ i → i ≤ r' → ¬ IsTrueCorner S ((smoothingSuccessor hn hP S ^ i) c'))
    (h : (smoothingSuccessor hn hP S ^ r) c = (smoothingSuccessor hn hP S ^ r') c') :
    c = c' ∧ r = r' := by
  have hsplit : (smoothingSuccessor hn hP S ^ r) ((smoothingSuccessor hn hP S ^ (r' - r)) c') =
      (smoothingSuccessor hn hP S ^ r') c' := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hrr]
  rw [← hsplit] at h
  have hc' : c = (smoothingSuccessor hn hP S ^ (r' - r)) c' :=
    (smoothingSuccessor hn hP S ^ r).injective h
  by_cases hz : r' - r = 0
  · have hrr' : r = r' := by omega
    subst hrr'
    rw [hz, pow_zero, Equiv.Perm.one_apply] at hc'
    exact ⟨hc', rfl⟩
  · exfalso
    apply hr' (r' - r) (by omega) (by omega)
    rw [← hc']
    exact hc

theorem prevCorner_unique {c c' : Mark P} (hc : IsTrueCorner S c) (hc' : IsTrueCorner S c')
    {r r' : ℕ}
    (hr : ∀ i, 1 ≤ i → i ≤ r → ¬ IsTrueCorner S ((smoothingSuccessor hn hP S ^ i) c))
    (hr' : ∀ i, 1 ≤ i → i ≤ r' → ¬ IsTrueCorner S ((smoothingSuccessor hn hP S ^ i) c'))
    (h : (smoothingSuccessor hn hP S ^ r) c = (smoothingSuccessor hn hP S ^ r') c') :
    c = c' ∧ r = r' := by
  rcases le_total r r' with hle | hle
  · exact prevCorner_unique_of_le hn hP S hc hle hr' h
  · obtain ⟨h1, h2⟩ := prevCorner_unique_of_le hn hP S hc' hle hr h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- Two block marks (of the blocks of `a` and `b`) that coincide force `a = b` (and the same
position in the block). -/
theorem block_mark_eq {a b : ZMod (ccpCornerCount hn hP S q)} {r r' : ℕ}
    (hba : BlockInterior hn hP S q a r) (hbb : BlockInterior hn hP S q b r')
    (h : (smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q a) =
      (smoothingSuccessor hn hP S ^ r') (ccpCornerMark hn hP S q b)) : a = b ∧ r = r' := by
  obtain ⟨hc, hr⟩ := prevCorner_unique hn hP S (ccpCornerMark_isTrueCorner hn hP S q a)
    (ccpCornerMark_isTrueCorner hn hP S q b) (hba.not_trueCorner hn hP S q)
    (hbb.not_trueCorner hn hP S q) h
  exact ⟨ccpCornerMark_injective hn hP S q hc, hr⟩

include hS

/-- **Block parametrization of a closed edge segment.**  A point of the `j`-th edge segment of
the corner polygon is traced at a half-open parameter `(ρ_S^r c_j, u)`, `u ∈ [0,1)`, by a mark of
the block of `j`, or it is the end corner `Q (j+1)`. -/
theorem edgeSegment_param (j : ZMod (ccpCornerCount hn hP S q)) {x : Plane}
    (hx : x ∈ edgeSegment (ccpCornerPolygon hn hP S q) j) :
    (∃ (r : ℕ) (u : ℝ), 0 ≤ u ∧ u < 1 ∧ BlockInterior hn hP S q j r ∧
      smoothingSegment hn hP S ((smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q j)) u
        = x) ∨
    x = ccpCornerPolygon hn hP S q (j + 1) := by
  obtain ⟨m, hm, hchain, hmid, -, -, -, -, himage⟩ := ccpCornerPolygon_block hn hP hS q j
  rw [ccpCornerPolygon_edgeSegment, ← himage, Set.mem_iUnion₂] at hx
  obtain ⟨r, hr, u, ⟨hu0, hu1⟩, hux⟩ := hx
  have hint : ∀ r' < m, BlockInterior hn hP S q j r' :=
    fun r' hr' i h1 hi => hmid i h1 (by omega)
  rcases lt_or_eq_of_le hu1 with hlt | heq
  · exact Or.inl ⟨r, u, hu0, hlt, hint r hr, hux⟩
  · subst heq
    rw [smoothingSegment_glue, ← Equiv.Perm.mul_apply, ← pow_succ'] at hux
    rcases Nat.lt_or_ge (r + 1) m with hlt | hge
    · exact Or.inl ⟨r + 1, 0, le_rfl, zero_lt_one, hint (r + 1) hlt, hux⟩
    · right
      have heq : r + 1 = m := by omega
      rw [heq, hchain, smoothingSegment_zero] at hux
      exact hux.symm

/-- **Block parametrization of an open edge.**  A point of the open `j`-th edge is traced at a
half-open block parameter of the block of `j`. -/
theorem edgeInterior_param (j : ZMod (ccpCornerCount hn hP S q)) {x : Plane}
    (hx : x ∈ edgeInterior (ccpCornerPolygon hn hP S q) j) :
    ∃ (r : ℕ) (u : ℝ), 0 ≤ u ∧ u < 1 ∧ BlockInterior hn hP S q j r ∧
      smoothingSegment hn hP S ((smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q j)) u
        = x := by
  rcases edgeSegment_param hn hP S q hS j (edgeInterior_subset_edgeSegment _ _ hx) with h | h
  · exact h
  · exfalso
    obtain ⟨t, -, ht1, hxt⟩ := hx
    have hne : edge (ccpCornerPolygon hn hP S q) j ≠ 0 :=
      ccpCornerPolygon_edge_ne_zero hn hP hS q j
    have h1 : edgePoint (ccpCornerPolygon hn hP S q) j t =
        edgePoint (ccpCornerPolygon hn hP S q) j 1 := by
      rw [edgePoint_one, ← hxt, h]
    have := edgePoint_injective hne h1
    linarith

/-- lem:carriers (iii) "none is a corner" in parameter form: two carrier parameters of `q`
tracing the plane point of a true corner coincide (otherwise that point would be a
self-intersection, hence the crossing point of an unselected crossing of `q`, which is the plane
point of no true corner). -/
theorem param_eq_of_corner {p p' : Mark P × ℝ} (hp : IsCarrierParameter hn hP S q p)
    (hp' : IsCarrierParameter hn hP S q p') {m : Mark P} (hm : IsTrueCorner S m)
    (hx : carrierTrace hn hP S p = traversalEvaluation P (markPosition hn hP.1 m))
    (hx' : carrierTrace hn hP S p' = traversalEvaluation P (markPosition hn hP.1 m)) : p = p' := by
  by_contra hne
  have hsi : IsSelfIntersection hn hP S q (traversalEvaluation P (markPosition hn hP.1 m)) :=
    ⟨p, p', hp, hp', hne, hx, hx'⟩
  obtain ⟨c, hc, he⟩ := (carrier_selfIntersection_iff hn hP hS q _).mp hsi
  exact (carrier_selfIntersection_not_corner hn hP S q hc).2.2.2 m hm he

/-- The corner points of a carrier are pairwise distinct (sanity: the corner polygon is
injective). -/
theorem ccpCornerPolygon_injective : Function.Injective (ccpCornerPolygon hn hP S q) := by
  intro a b hab
  have h := param_eq_of_corner hn hP S q hS (corner_param hn hP S q a).1
    (corner_param hn hP S q b).1 (ccpCornerMark_isTrueCorner hn hP S q b)
    ((corner_param hn hP S q a).2.trans (hab.trans (ccpCornerPolygon_apply hn hP S q b)))
    ((corner_param hn hP S q b).2.trans (ccpCornerPolygon_apply hn hP S q b))
  exact ccpCornerMark_injective hn hP S q (congrArg Prod.fst h)

/-- A block parameter of the edge `b` tracing the corner point `Q a` is the corner parameter
`(c_a, 0)`; in particular `c_a = c_b`, i.e. `a = b`. -/
theorem block_param_corner {a b : ZMod (ccpCornerCount hn hP S q)} {r : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hb : BlockInterior hn hP S q b r)
    (h : smoothingSegment hn hP S ((smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q b)) u
      = ccpCornerPolygon hn hP S q a) : a = b := by
  have hp := isCarrierParameter_block hn hP S q b r hu0 hu1
  have heq := param_eq_of_corner hn hP S q hS hp (corner_param hn hP S q a).1
    (ccpCornerMark_isTrueCorner hn hP S q a) (h.trans (ccpCornerPolygon_apply hn hP S q a))
    ((corner_param hn hP S q a).2.trans (ccpCornerPolygon_apply hn hP S q a))
  have hmk : (smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q b) =
      ccpCornerMark hn hP S q a :=
    congrArg Prod.fst heq
  have hr : r = 0 := hb.eq_zero_of_trueCorner hn hP S q
    (by rw [hmk]; exact ccpCornerMark_isTrueCorner hn hP S q a)
  rw [hr, pow_zero, Equiv.Perm.one_apply] at hmk
  exact (ccpCornerMark_injective hn hP S q hmk).symm

/-! ### The meeting lemma for two non-adjacent edges of the corner polygon -/

/-- **Meeting of two non-adjacent edges of the corner polygon** (lem:carriers (iii), sm-3:84-86).
A common point `x` of the closed edge segments `a`, `b` of `Q`, `a`, `b` not adjacent, is the
crossing point of an unselected crossing `c` of `q` ("exactly the unselected crossings both of
whose visits are assigned to it"), whose two visits `w`, `visitTwin w` lie on the original edges
`e_a`, `e_b` carrying the two edges of `Q`. -/
theorem nonadjacent_meet {a b : ZMod (ccpCornerCount hn hP S q)} (hab : ¬ adjacent a b)
    {x : Plane} (hxa : x ∈ edgeSegment (ccpCornerPolygon hn hP S q) a)
    (hxb : x ∈ edgeSegment (ccpCornerPolygon hn hP S q) b) :
    ∃ (c : SM.Crossing P) (w : SM.Visit P), c ∈ carrierCrossings hn hP S q ∧
      x = SM.crossingPoint c ∧ w.1 = c ∧
      w.2.val = (ccpOutSlot hn hP S (ccpCornerMark hn hP S q a)).1 ∧
      (visitTwin w).2.val = (ccpOutSlot hn hP S (ccpCornerMark hn hP S q b)).1 := by
  rcases edgeSegment_param hn hP S q hS a hxa with ⟨r, u, hu0, hu1, hba, hux⟩ | hxa'
  · rcases edgeSegment_param hn hP S q hS b hxb with ⟨r', v, hv0, hv1, hbb, hvx⟩ | hxb'
    · -- both points are half-open block parameters
      have hpa := isCarrierParameter_block hn hP S q a r hu0 hu1
      have hpb := isCarrierParameter_block hn hP S q b r' hv0 hv1
      have htr : carrierTrace hn hP S
            ((smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q a), u) =
          carrierTrace hn hP S
            ((smoothingSuccessor hn hP S ^ r') (ccpCornerMark hn hP S q b), v) := by
        show smoothingSegment hn hP S _ u = smoothingSegment hn hP S _ v
        rw [hux, hvx]
      by_cases hpp : ((smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q a), u) =
          ((smoothingSuccessor hn hP S ^ r') (ccpCornerMark hn hP S q b), v)
      · exfalso
        exact hab (adjacent_of_eq (block_mark_eq hn hP S q hba hbb (congrArg Prod.fst hpp)).1)
      · have hmk := csi_mark_ne_of_param_ne hn hP S hpp htr
        obtain ⟨-, -, c, hxc, ⟨w, hw, hwa₀⟩, ⟨w', hw', hwb₀⟩⟩ :=
          csi_trace_meet hn hP S hmk hu0 hu1 hv0 hv1 (hux.trans hvx.symm)
        have hwa : (smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q a) = Sum.inr w := hwa₀
        have hwb : (smoothingSuccessor hn hP S ^ r') (ccpCornerMark hn hP S q b) = Sum.inr w' :=
          hwb₀
        have hww' : w' ≠ w := fun h => hmk (by
          show (smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q a) =
            (smoothingSuccessor hn hP S ^ r') (ccpCornerMark hn hP S q b)
          rw [hwa, hwb, h])
        have htw : w' = visitTwin w := visitTwin_unique w w' (hw'.trans hw.symm) hww'
        have hoa : owner hn hP S (Sum.inr w) = q := by rw [← hwa]; exact hpa.1
        have hob : owner hn hP S (Sum.inr (visitTwin w)) = q := by
          rw [← htw, ← hwb]; exact hpb.1
        have hcS : c ∉ S := by
          intro hcS
          apply independent_selected_pair_owners_ne hn hP hS w (hw ▸ hcS)
          rw [hoa, hob]
        have hr : 1 ≤ r := by
          by_contra h
          have hr0 : r = 0 := by omega
          rw [hr0, pow_zero, Equiv.Perm.one_apply] at hwa
          have hcorner := ccpCornerMark_isTrueCorner hn hP S q a
          rw [hwa] at hcorner
          exact hcS (hw ▸ (isTrueCorner_visit S w).mp hcorner)
        have hr' : 1 ≤ r' := by
          by_contra h
          have hr0 : r' = 0 := by omega
          rw [hr0, pow_zero, Equiv.Perm.one_apply] at hwb
          have hcorner := ccpCornerMark_isTrueCorner hn hP S q b
          rw [hwb] at hcorner
          exact hcS (hw' ▸ (isTrueCorner_visit S w').mp hcorner)
        have hcmem : c ∈ carrierCrossings hn hP S q := by
          rw [mem_carrierCrossings]
          refine ⟨hcS, fun v hv => ?_⟩
          rcases visit_eq_or_twin w v (hv.trans hw.symm) with rfl | rfl
          · exact hoa
          · exact hob
        refine ⟨c, w, hcmem, hux.symm.trans hxc, hw, hba.visit_edge hn hP S q hr hwa, ?_⟩
        rw [← htw]
        exact hbb.visit_edge hn hP S q hr' hwb
    · -- `x = Q (b+1)` is a corner point traced by a block parameter of `a`
      exfalso
      rw [hxb'] at hux
      exact hab (adjacent_of_eq_add_one (block_param_corner hn hP S q hS hu0 hu1 hba hux).symm)
  · rcases edgeSegment_param hn hP S q hS b hxb with ⟨r', v, hv0, hv1, hbb, hvx⟩ | hxb'
    · exfalso
      rw [hxa'] at hvx
      exact hab (adjacent_of_add_one_eq (block_param_corner hn hP S q hS hv0 hv1 hbb hvx))
    · exfalso
      have h := ccpCornerPolygon_injective hn hP S q hS (hxa'.symm.trans hxb')
      exact hab (adjacent_of_eq (add_right_cancel h))

/-- The common point of two non-adjacent edges of `Q` is the crossing point of a crossing of `q`
(lem:carriers (iii), first sentence, on the corner polygon). -/
theorem nonadjacent_meet_crossing {a b : ZMod (ccpCornerCount hn hP S q)} (hab : ¬ adjacent a b)
    {x : Plane} (hxa : x ∈ edgeSegment (ccpCornerPolygon hn hP S q) a)
    (hxb : x ∈ edgeSegment (ccpCornerPolygon hn hP S q) b) :
    ∃ c ∈ carrierCrossings hn hP S q, x = SM.crossingPoint c := by
  obtain ⟨c, -, hc, hxc, -⟩ := nonadjacent_meet hn hP S q hS hab hxa hxb
  exact ⟨c, hc, hxc⟩

/-! ### The four label-level genericity facts for the corner polygon -/

/-- No corner of `Q` lies on a non-incident closed edge of `Q` (lem:carriers (iii): "none is a
corner", together with the distinctness of the corner points). -/
theorem ccpCornerPolygon_tail_off (a b : ZMod (ccpCornerCount hn hP S q)) (hab : ¬ incident a b) :
    ccpCornerPolygon hn hP S q a ∉ edgeSegment (ccpCornerPolygon hn hP S q) b := by
  intro hx
  rcases edgeSegment_param hn hP S q hS b hx with ⟨r, u, hu0, hu1, hb, hux⟩ | h
  · exact hab (Or.inr (block_param_corner hn hP S q hS hu0 hu1 hb hux).symm)
  · have h' := ccpCornerPolygon_injective hn hP S q hS h
    exact hab (Or.inl (by rw [h']; ring))

/-- Meeting non-adjacent edges of `Q` are transverse (lem:carriers (iii): "They are
transverse"). -/
theorem ccpCornerPolygon_transverse (a b : ZMod (ccpCornerCount hn hP S q)) (hab : ¬ adjacent a b)
    (hmeet : (edgeSegment (ccpCornerPolygon hn hP S q) a ∩
      edgeSegment (ccpCornerPolygon hn hP S q) b).Nonempty) :
    det (edge (ccpCornerPolygon hn hP S q) a) (edge (ccpCornerPolygon hn hP S q) b) ≠ 0 := by
  obtain ⟨x, hxa, hxb⟩ := hmeet
  obtain ⟨c, w, -, -, hw, hwa, hwb⟩ := nonadjacent_meet hn hP S q hS hab hxa hxb
  obtain ⟨c₁, hc₁, he₁⟩ := ccpCornerPolygon_edge hn hP hS q a
  obtain ⟨c₂, hc₂, he₂⟩ := ccpCornerPolygon_edge hn hP hS q b
  rw [he₁, he₂, ccp_det_smul_smul, ← hwa, ← hwb]
  refine mul_ne_zero (mul_pos hc₁ hc₂).ne' ?_
  have hmem : w.2.val ∈ c.val := hw ▸ w.2.property
  have hmem' : (visitTwin w).2.val ∈ c.val := hw ▸ (visitTwin w).2.property
  exact csi_crossing_edges_det_ne_zero hn hP.1 c hmem hmem' (visitTwin_edge_ne w).symm

/-- `Q` has no triple point (lem:carriers (iii): "no carrier has a triple point"). -/
theorem ccpCornerPolygon_no_triple :
    ¬ ∃ a b c : ZMod (ccpCornerCount hn hP S q), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (edgeInterior (ccpCornerPolygon hn hP S q) a ∩ edgeInterior (ccpCornerPolygon hn hP S q) b ∩
        edgeInterior (ccpCornerPolygon hn hP S q) c).Nonempty := by
  rintro ⟨a, b, c, hab, hbc, hac, x, ⟨hxa, hxb⟩, hxc⟩
  obtain ⟨r, u, hu0, hu1, hba, hux⟩ := edgeInterior_param hn hP S q hS a hxa
  obtain ⟨r', v, hv0, hv1, hbb, hvx⟩ := edgeInterior_param hn hP S q hS b hxb
  obtain ⟨r'', t, ht0, ht1, hbc', htx⟩ := edgeInterior_param hn hP S q hS c hxc
  apply carrier_no_triple_point hn hP S q x
  refine ⟨_, _, _, isCarrierParameter_block hn hP S q a r hu0 hu1,
    isCarrierParameter_block hn hP S q b r' hv0 hv1,
    isCarrierParameter_block hn hP S q c r'' ht0 ht1, ?_, ?_, ?_, hux, hvx, htx⟩
  · intro h
    exact hab (block_mark_eq hn hP S q hba hbb (congrArg Prod.fst h)).1
  · intro h
    exact hac (block_mark_eq hn hP S q hba hbc' (congrArg Prod.fst h)).1
  · intro h
    exact hbc (block_mark_eq hn hP S q hbb hbc' (congrArg Prod.fst h)).1

/-- **CarrierGeneric** (design: positive_lift_and_carriers).  The shadow of a carrier of a
decomposition is generic in the sense of def:positive-lift (sm-3:326-327: "finitely many
transverse double points, no triple points"): regularity and `3 ≤ k` are lem:carriers (ii)
(sm-3:72-73), and the immersion, transversality and no-triple-point clauses are lem:carriers (iii)
(sm-3:84-86) read on the corner polygon through the block parametrization. -/
theorem carrierShadow_generic : (carrierShadow hn hP S q hS).Generic :=
  Shadow.single_generic_of (carrierPolyComp hn hP S q hS) (ccpCornerPolygon_regular hn hP hS q)
    (ccpCornerPolygon_tail_off hn hP S q hS) (ccpCornerPolygon_transverse hn hP S q hS)
    (ccpCornerPolygon_no_triple hn hP S q hS)

end CarrierGeneric

/-! ## The positive lift -/

/-- def:positive-lift (sm-3:331-334): "The positive lift of a subpolygon Q is the oriented knot
diagram whose curve is Q, whose double points are the crossings of Q, and in which at every double
point the over strand is chosen so that the crossing is positive."  The curve is the one-component
shadow `carrierShadow` of the corner polygon of the carrier `q` of the decomposition `S`; its
double points are the crossings of that shadow (identified with `carrierCrossings hn hP S q` in
`carrierCrossingEquiv`); the over strand at each crossing is the strand `s` with
`det(dir s, dir (other s)) > 0` (`Shadow.positiveDiagram`). -/
def positiveLift (hn : 3 ≤ n) {P : LabelledTuple n} (hP : SM.Generic P)
    (S : Finset (SM.Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) : Diagram :=
  (carrierShadow hn hP S q hS).positiveDiagram (carrierShadow_generic hn hP S q hS)

section PositiveLift

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : SM.Generic P) (S : Finset (SM.Crossing P))
  (q : Component hn hP S) (hS : IsDecomposition hn hP S)

include hS

@[simp] theorem positiveLift_Γ : (positiveLift hn hP S q hS).Γ = carrierShadow hn hP S q hS := rfl

/-- "the oriented knot diagram": one component. -/
theorem positiveLift_componentCount : (positiveLift hn hP S q hS).componentCount = 1 := rfl

/-- The component of the lift is the corner polygon of the carrier ("whose curve is Q"). -/
theorem positiveLift_comp (i : Fin 1) :
    ((positiveLift hn hP S q hS).Γ.comp i).P = ccpCornerPolygon hn hP S q := rfl

/-- def:positive-lift (sm-3:333-334): "at every double point the over strand is chosen so that the
crossing is positive". -/
theorem positiveLift_isPositive (x : (positiveLift hn hP S q hS).Γ.Crossing) :
    (positiveLift hn hP S q hS).IsPositive x :=
  Shadow.positiveDiagram_isPositive _ _ x

theorem positiveLift_sign (x : (positiveLift hn hP S q hS).Γ.Crossing) :
    (positiveLift hn hP S q hS).sign x = 1 :=
  Shadow.positiveDiagram_sign _ _ x

/-- The writhe of the positive lift is its number of crossings (all signs are `+1`). -/
theorem positiveLift_writhe :
    (positiveLift hn hP S q hS).writhe = Fintype.card (carrierShadow hn hP S q hS).Crossing :=
  Shadow.positiveDiagram_writhe _ _

/-- The positive lift is the unique diagram on the carrier shadow all of whose crossings are
positive. -/
theorem eq_positiveLift_of_isPositive (D : Diagram) (hD : D.Γ = carrierShadow hn hP S q hS)
    (hpos : ∀ x, D.IsPositive x) : D = positiveLift hn hP S q hS :=
  Shadow.eq_positiveDiagram_of_isPositive _ _ D hD hpos

/-! ## The double points of the lift are the crossings of `Q` -/

/-- Every crossing of the carrier shadow sits at the crossing point of a crossing of `q`
(def:positive-lift, sm-3:332-333: "whose double points are the crossings of Q"). -/
theorem exists_carrierCrossing (x : (carrierShadow hn hP S q hS).Crossing) :
    ∃ c : SM.Crossing P, c ∈ carrierCrossings hn hP S q ∧
      (carrierShadow hn hP S q hS).crossingPoint x = SM.crossingPoint c := by
  obtain ⟨s, t, hx, hna, -⟩ := x.2
  have hs : s ∈ x.val := by rw [hx]; simp
  have ht : t ∈ x.val := by rw [hx]; simp
  have hna' : ¬ adjacent (Shadow.singleStrandEquiv _ s) (Shadow.singleStrandEquiv _ t) :=
    fun h => hna ((Shadow.single_adjacent_iff _ s t).mpr h)
  have hps : (carrierShadow hn hP S q hS).crossingPoint x ∈
      edgeSegment (ccpCornerPolygon hn hP S q) (Shadow.singleStrandEquiv _ s) :=
    (carrierShadow hn hP S q hS).crossingPoint_mem x hs
  have hpt : (carrierShadow hn hP S q hS).crossingPoint x ∈
      edgeSegment (ccpCornerPolygon hn hP S q) (Shadow.singleStrandEquiv _ t) :=
    (carrierShadow hn hP S q hS).crossingPoint_mem x ht
  exact nonadjacent_meet_crossing hn hP S q hS hna' hps hpt

/-- The crossing of `q` at a crossing of the carrier shadow. -/
def toCarrierCrossing (x : (carrierShadow hn hP S q hS).Crossing) :
    {c : SM.Crossing P // c ∈ carrierCrossings hn hP S q} :=
  ⟨Classical.choose (exists_carrierCrossing hn hP S q hS x),
    (Classical.choose_spec (exists_carrierCrossing hn hP S q hS x)).1⟩

theorem crossingPoint_toCarrierCrossing (x : (carrierShadow hn hP S q hS).Crossing) :
    SM.crossingPoint (toCarrierCrossing hn hP S q hS x).val =
      (carrierShadow hn hP S q hS).crossingPoint x :=
  (Classical.choose_spec (exists_carrierCrossing hn hP S q hS x)).2.symm

theorem toCarrierCrossing_injective : Function.Injective (toCarrierCrossing hn hP S q hS) := by
  intro x y h
  apply (carrierShadow_generic hn hP S q hS).crossingPoint_injective
  rw [← crossingPoint_toCarrierCrossing hn hP S q hS x,
    ← crossingPoint_toCarrierCrossing hn hP S q hS y, h]

/-- Every mark owned by `q` is a block mark: `m = ρ_S^r c_j` for a corner `c_j` with the
intermediate marks interior to the block, and its plane point lies on the edge `j` of `Q`. -/
theorem mark_block (m : Mark P) (hm : owner hn hP S m = q) :
    ∃ (j : ZMod (ccpCornerCount hn hP S q)) (r : ℕ),
      (smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q j) = m ∧
      BlockInterior hn hP S q j r ∧
      traversalEvaluation P (markPosition hn hP.1 m) ∈
        edgeSegment (ccpCornerPolygon hn hP S q) j := by
  obtain ⟨a, r, ha, hac, hra, hmid⟩ := ccp_previous_corner hn hP S q m hm
  obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S q a ha hac
  subst hj
  obtain ⟨mj, hmj, hchain, hmidj, -, -, -, -, himage⟩ := ccpCornerPolygon_block hn hP hS q j
  have hr : r < mj := by
    by_contra hle
    apply hmid mj hmj (not_lt.mp hle)
    rw [hchain]
    exact ccpCornerMark_isTrueCorner hn hP S q (j + 1)
  refine ⟨j, r, hra, fun i h1 hi => hmidj i h1 (by omega), ?_⟩
  rw [ccpCornerPolygon_edgeSegment, ← himage, Set.mem_iUnion₂]
  refine ⟨r, hr, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
  rw [hra, smoothingSegment_zero]

/-- Consecutive edges of `Q` meet only at their common corner (all corner turns are nonzero,
lem:carriers (ii)). -/
theorem consecutive_meet (j : ZMod (ccpCornerCount hn hP S q)) {x : Plane}
    (hx : x ∈ edgeSegment (ccpCornerPolygon hn hP S q) j)
    (hx' : x ∈ edgeSegment (ccpCornerPolygon hn hP S q) (j + 1)) :
    x = ccpCornerPolygon hn hP S q (j + 1) := by
  obtain ⟨s, -, -, hs⟩ := hx
  obtain ⟨t, -, -, ht⟩ := hx'
  have hd : det (edge (ccpCornerPolygon hn hP S q) j)
      (edge (ccpCornerPolygon hn hP S q) (j + 1)) ≠ 0 := by
    have h := ccpCornerPolygon_det_ne_zero hn hP hS q (j + 1)
    have hj : j + 1 - 1 = j := by ring
    rwa [hj] at h
  have h1 : ccpCornerPolygon hn hP S q j + s • edge (ccpCornerPolygon hn hP S q) j =
      ccpCornerPolygon hn hP S q (j + 1) + t • edge (ccpCornerPolygon hn hP S q) (j + 1) :=
    hs.symm.trans ht
  have h2 : ccpCornerPolygon hn hP S q j + (1 : ℝ) • edge (ccpCornerPolygon hn hP S q) j =
      ccpCornerPolygon hn hP S q (j + 1) + (0 : ℝ) • edge (ccpCornerPolygon hn hP S q) (j + 1) := by
    rw [one_smul, zero_smul, add_zero]
    simp only [edge]
    abel
  obtain ⟨rfl, -⟩ := intersection_parameters_unique hd h1 h2
  rw [hs, edgePoint_one]

/-- The two visits of a crossing of `q` lie on two non-adjacent edges of `Q`, and its crossing
point lies on both. -/
theorem carrierCrossing_edges {c : SM.Crossing P} (hc : c ∈ carrierCrossings hn hP S q) :
    ∃ j j' : ZMod (ccpCornerCount hn hP S q), ¬ adjacent j j' ∧
      SM.crossingPoint c ∈ edgeSegment (ccpCornerPolygon hn hP S q) j ∧
      SM.crossingPoint c ∈ edgeSegment (ccpCornerPolygon hn hP S q) j' := by
  obtain ⟨hcS, hown⟩ := (mem_carrierCrossings hn hP S q c).mp hc
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  let w : SM.Visit P := ⟨c, i⟩
  have hw : w.1 = c := rfl
  have hw' : (visitTwin w).1 = c := rfl
  obtain ⟨j, r, hrj, hbj, hmemj⟩ := mark_block hn hP S q hS (Sum.inr w) (hown w hw)
  obtain ⟨j', r', hrj', hbj', hmemj'⟩ :=
    mark_block hn hP S q hS (Sum.inr (visitTwin w)) (hown _ hw')
  rw [markPosition_evaluation_visit] at hmemj hmemj'
  have hr : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, Equiv.Perm.one_apply] at hrj
    have hcorner := ccpCornerMark_isTrueCorner hn hP S q j
    rw [hrj] at hcorner
    exact hcS ((isTrueCorner_visit S w).mp hcorner)
  have hr' : 1 ≤ r' := by
    by_contra h
    have hr0 : r' = 0 := by omega
    rw [hr0, pow_zero, Equiv.Perm.one_apply] at hrj'
    have hcorner := ccpCornerMark_isTrueCorner hn hP S q j'
    rw [hrj'] at hcorner
    exact hcS ((isTrueCorner_visit S (visitTwin w)).mp hcorner)
  have hwe := hbj.visit_edge hn hP S q hr hrj
  have hwe' := hbj'.visit_edge hn hP S q hr' hrj'
  have hnc : ∀ m : Mark P, IsTrueCorner S m →
      traversalEvaluation P (markPosition hn hP.1 m) ≠ SM.crossingPoint c :=
    (carrier_selfIntersection_not_corner hn hP S q hc).2.2.2
  refine ⟨j, j', ?_, hmemj, hmemj'⟩
  intro hadj
  rcases hadj with h | h | h
  · -- `j' - j = -1`: `j = j' + 1`
    have hj : j = j' + 1 := by linear_combination -h
    rw [hj] at hmemj
    exact hnc _ (ccpCornerMark_isTrueCorner hn hP S q (j' + 1))
      (consecutive_meet hn hP S q hS j' hmemj' hmemj).symm
  · -- `j' = j`: both visits on one original edge
    have hj : j' = j := by linear_combination h
    rw [hj] at hwe'
    exact visitTwin_edge_ne w (hwe'.trans hwe.symm)
  · -- `j' - j = 1`: `j' = j + 1`
    have hj : j' = j + 1 := by linear_combination h
    rw [hj] at hmemj'
    exact hnc _ (ccpCornerMark_isTrueCorner hn hP S q (j + 1))
      (consecutive_meet hn hP S q hS j hmemj hmemj').symm

theorem toCarrierCrossing_surjective : Function.Surjective (toCarrierCrossing hn hP S q hS) := by
  rintro ⟨c, hc⟩
  obtain ⟨j, j', hna, hmemj, hmemj'⟩ := carrierCrossing_edges hn hP S q hS hc
  have hcr : (carrierShadow hn hP S q hS).IsCrossing
      {(⟨0, j⟩ : (carrierShadow hn hP S q hS).Strand), ⟨0, j'⟩} :=
    (carrierShadow hn hP S q hS).isCrossing_pair
      (fun h => hna ((Shadow.single_adjacent_iff _ _ _).mp h))
      ⟨SM.crossingPoint c, hmemj, hmemj'⟩
  obtain ⟨y, hy⟩ : ∃ y : (carrierShadow hn hP S q hS).Crossing,
      y.val = {(⟨0, j⟩ : (carrierShadow hn hP S q hS).Strand), ⟨0, j'⟩} := ⟨⟨_, hcr⟩, rfl⟩
  refine ⟨y, Subtype.ext ?_⟩
  apply generic_crossingPoint_injective hn hP
  refine (crossingPoint_toCarrierCrossing hn hP S q hS y).trans ?_
  symm
  apply (carrierShadow_generic hn hP S q hS).common_point_unique
  intro s hs
  rw [hy] at hs
  have hs' : s = ⟨0, j⟩ ∨ s = ⟨0, j'⟩ := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hs
  rcases hs' with rfl | rfl
  · exact hmemj
  · exact hmemj'

/-- def:positive-lift (sm-3:332-333), "whose double points are the crossings of Q": the crossings
of the positive lift correspond bijectively to the crossings `carrierCrossings hn hP S q` of the
carrier (def:smoothing; lem:carriers (iii)), each crossing of the lift sitting at the crossing
point of its image. -/
def carrierCrossingEquiv :
    (carrierShadow hn hP S q hS).Crossing ≃ {c : SM.Crossing P // c ∈ carrierCrossings hn hP S q} :=
  Equiv.ofBijective (toCarrierCrossing hn hP S q hS)
    ⟨toCarrierCrossing_injective hn hP S q hS, toCarrierCrossing_surjective hn hP S q hS⟩

theorem carrierCrossingEquiv_apply (x : (carrierShadow hn hP S q hS).Crossing) :
    carrierCrossingEquiv hn hP S q hS x = toCarrierCrossing hn hP S q hS x := rfl

/-- Sanity: the equivalence preserves the crossing point. -/
theorem crossingPoint_carrierCrossingEquiv (x : (carrierShadow hn hP S q hS).Crossing) :
    SM.crossingPoint (carrierCrossingEquiv hn hP S q hS x).val =
      (carrierShadow hn hP S q hS).crossingPoint x :=
  crossingPoint_toCarrierCrossing hn hP S q hS x

/-- The number of crossings of the carrier shadow is `m_Q`. -/
theorem card_carrierShadow_crossing :
    Fintype.card (carrierShadow hn hP S q hS).Crossing = carrierCrossingCount hn hP S q := by
  rw [Fintype.card_congr (carrierCrossingEquiv hn hP S q hS)]
  exact Fintype.card_coe _

/-- def:positive-lift (sm-3:334-335): "Its writhe (the sum of crossing signs) is m_Q." -/
theorem positiveLift_writhe_eq_carrierCrossingCount :
    (positiveLift hn hP S q hS).writhe = carrierCrossingCount hn hP S q := by
  rw [positiveLift_writhe, card_carrierShadow_crossing]

/-- Sanity: on the carrier shadow the multi-component crossing point is the accepted one-polygon
`SM.crossingPoint` of the corner polygon (through `Shadow.singleCrossingEquiv`). -/
theorem carrierShadow_crossingPoint (x : (carrierShadow hn hP S q hS).Crossing) :
    (carrierShadow hn hP S q hS).crossingPoint x =
      SM.crossingPoint (Shadow.singleCrossingEquiv (carrierPolyComp hn hP S q hS) x) :=
  Shadow.single_crossingPoint _ (carrierShadow_generic hn hP S q hS) x

/-- Sanity: the lift of a carrier without crossings is a crossing-free circle (lit:homfly's
"the crossing-free circle"). -/
theorem positiveLift_isCrossingFreeCircle (h : carrierCrossings hn hP S q = ∅) :
    (positiveLift hn hP S q hS).IsCrossingFreeCircle := by
  refine ⟨rfl, ⟨fun x => ?_⟩⟩
  obtain ⟨d, hd⟩ := toCarrierCrossing hn hP S q hS x
  rw [h] at hd
  exact Finset.notMem_empty _ hd

end PositiveLift

end

end SM.Link

#print axioms SM.Link.carrierShadow_generic
#print axioms SM.Link.positiveLift_isPositive
#print axioms SM.Link.positiveLift_writhe
#print axioms SM.Link.positiveLift_writhe_eq_carrierCrossingCount
#print axioms SM.Link.carrierCrossingEquiv
#print axioms SM.Link.Shadow.eq_positiveDiagram_of_isPositive
