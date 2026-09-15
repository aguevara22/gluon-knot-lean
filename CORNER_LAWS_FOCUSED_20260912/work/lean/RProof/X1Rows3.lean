-- Ported 10:49Z 2026-09-14 from work/drafts/rlane2/RLaneX1Rows3.lean (R lane wave 3, row 173 unit GT) by the pod executor; body verbatim. LIBRARY MATERIAL: row 173 R:generic_transport is NOT mapped — RProof.GT_generic_transport_of_G11 proves the row MODULO the open fact GT_G11 (HOMFLY invariance of the distinguished carrier's grouped diagram across the RIII wall); see work/drafts/rlane2/W3_GT_REPORT.md and work/AUTHOR_NOTES.md. SUPERSEDED NOTE 17:41Z: the open fact GT_G11 was proved (as GT_G11_strong) and row 173 R:generic_transport is stated, proved and ACCEPTED in RProof/GenericTransport.lean (theorem RProof.generic_transport); this module remains as the accepted row's imported library (GT_generic_transport_of_G11 and the transport toolkit). Header comment only; no declaration changed.
import RProof.X1Rows2
import CV.GroupedKnot

/-! # R lane, X₁ rows — wave 3 portable module, unit U-GT (row 173, R:generic_transport)

Written 2026-09-14 by the wave-3 prover (unit U-GT) on Mark's RunPod home pod; report
`work/drafts/rlane2/W3_GT_REPORT.md`, unit file `W3_GT.lean`. This module is `import RProof.X1Rows2`
(the wave-2 portable module: bundles, auxiliaries, the proved rows 168, 170, 172 and the `PRE_`/`SEL_`/
`A2_`/`EXT_`/`AV_` toolkits) + `import CV.GroupedKnot` (CV:cor:groupedknot, row 158, accepted) and
ONLY the new material of unit U-GT, prefixed `GT_`:

* the corner-level wall transport at full availability (`GT_Wall`, `GT_Good`, `GT_carrierEquiv`, the
  corner lists, turns, selector, `wind`, rotation and `R(L)` across the wall) — the AV toolkit's
  next-corner machinery without the availability-`≤ 1` clause;
* the relabelled piece transport (`GT_Relabel`, `GT_pieceEquiv`, `GT_piecesOn_eq`), the bridge
  `P_{S,L} = P(D(W))` (`GT_groupedPoly_eq_homfly`, cor:groupedknot (B)), the generalized record
  isomorphism of two lifts (`GT_homfly_wall_gen`) and the cyclic-order lemmas it needs (`GT_cyc_carried`);
* the one-polygon arc lemma (`GT_owner_arc`: the carrier of a selected visit lies in the arc it cuts)
  and the endpoint-row configuration `GT_Endpoint` with its transport `GT_endpoint_rowTerm_eq`;
* the event-level instantiation and the two PROVED fields `GT_173_endpoint_rows_canonical`,
  `GT_173_endpoint_rows_relabelled` of `GenericTransportData`;
* the missing fact **G11** (`GT_G11`: HOMFLY invariance of the grouped diagram across the RIII wall, an
  actual Reidemeister III move between the two positive lifts), the field `GT_173_empty_row` PROVED
  modulo `GT_G11`, and the row `GT_generic_transport_of_G11` PROVED modulo `GT_G11`.

No `sorry`; the row theorem `RProof.generic_transport` itself is not in this module (it stays open in
`W3_GT.lean`, its field `empty_row` needing G11). -/

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-! ## Unit GT (row 173, wave 3) — the corner-level wall transport at full availability

Section `GT`: the AV toolkit's corner-cycle transport (`AV_nextCorner`, `AV_cornerSucc`, their order
specifications) rebuilt on **wall data without the availability-`≤ 1` clause `dominated`**: the reversed
same-edge pairs of `R-LOC-2 (2)` are the pairs of distinct `T`-visits on one edge (`GT_Rev`); a mark is
*good* when none of its reversed partners is a corner (`GT_Good`), and the wall data ask only that no two
corners form a reversed pair (`corners_apart`) — true whenever the support contains at most one triangle
crossing (rows `∅`, `a`, `b`, `c` of the full-availability fibre). Every lemma is the AV lemma with
`AV_good_key_lt` replaced by `GT_good_key_lt`. -/

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

/-- A *reversed pair* of the wall: two same-edge visits of two distinct `T`-crossings (R-LOC-2 (2)). -/
def GT_Rev (T : Finset (Crossing P)) (v w : Visit P) : Prop :=
  v.1 ∈ T ∧ w.1 ∈ T ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val

omit [NeZero n] in
theorem GT_Rev.symm {T : Finset (Crossing P)} {v w : Visit P} (h : GT_Rev T v w) : GT_Rev T w v :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩

omit [NeZero n] in
theorem GT_not_rev_of_not_mem_left {T : Finset (Crossing P)} {v w : Visit P} (hv : v.1 ∉ T) :
    ¬ GT_Rev T v w := fun h => hv h.1

omit [NeZero n] in
theorem GT_not_rev_of_not_mem_right {T : Finset (Crossing P)} {v w : Visit P} (hw : w.1 ∉ T) :
    ¬ GT_Rev T v w := fun h => hw h.2.1

omit [NeZero n] in
theorem GT_not_rev_of_edge_ne {T : Finset (Crossing P)} {v w : Visit P} (h : v.2.val ≠ w.2.val) :
    ¬ GT_Rev T v w := fun h' => h h'.2.2.2

/-- **Wall data for a support `S` across a simple RIII wall at full availability**: as `AV_Wall`
(visit-key orders carried except on the reversed pairs, turns, signs, a common ray), with the
transported support independent and — in place of `dominated` — no two corners of `S` forming a
reversed pair. -/
structure GT_Wall (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (T S : Finset (Crossing P)) : Prop where
  indep : GeoIndependent hP S
  indep' : GeoIndependent hP' (transportSupport hs S)
  key_lt : ∀ v w : Visit P, ¬ GT_Rev T v w →
    (geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hP' (visitTransport hs v) < geometricVisitKey hP' (visitTransport hs w))
  corners_apart : ∀ v w : Visit P, GT_Rev T v w → ¬ (v.1 ∈ S ∧ w.1 ∈ S)
  turn_eq : ∀ i, turn P' i = turn P i
  sign_eq : ∀ i j, IsCrossing P {i, j} → crossingSign P' i j = crossingSign P i j
  ray : ∃ r : Plane, ∀ h : ZMod n, det r (edge P h) ≠ 0 ∧
    SignType.sign (det r (edge P' h)) = SignType.sign (det r (edge P h))

/-- A *good* mark: none of its reversed partners is a corner, so its key order relative to every
corner is carried across the wall. -/
def GT_Good (T S : Finset (Crossing P)) (m : Mark P) : Prop :=
  ∀ v : Visit P, m = Sum.inr v → ∀ w : Visit P, GT_Rev T v w → ¬ IsTrueCorner S (Sum.inr w)

omit [NeZero n] in
theorem GT_good_vertex (T S : Finset (Crossing P)) (i : ZMod n) : GT_Good T S (Sum.inl i) :=
  fun _ h => nomatch h

omit [NeZero n] in
/-- A visit of a crossing outside `T` is good (it has no reversed partner). -/
theorem GT_good_of_not_mem (T S : Finset (Crossing P)) {v : Visit P} (hv : v.1 ∉ T) :
    GT_Good T S (Sum.inr v) := by
  intro v' hv' w hrev
  obtain rfl := Sum.inr.inj hv'
  exact absurd hrev.1 hv

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}

omit [NeZero n] in
theorem GT_good_of_corner (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : IsTrueCorner S m) :
    GT_Good T S m := by
  intro v hv w hrev hw
  subst hv
  exact W.corners_apart v w hrev ⟨hm, hw⟩

/-- Mark keys are carried for every pair of marks that is not a reversed pair (the accepted
`geoMarkKey_lt_transport_of_visitKey`, word for word, with the exception built in). -/
theorem GT_mark_key_lt (W : GT_Wall hP hP' hs T S) (a b : Mark P)
    (hab : ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w → ¬ GT_Rev T v w) :
    geoMarkKey hP a < geoMarkKey hP b ↔
      geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs b) := by
  cases a with
  | inl i =>
    cases b with
    | inl k => exact Iff.rfl
    | inr v =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hP' (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (i.val < v.2.val.val ∨ i = v.2.val ∧ (0 : ℝ) < visitParameter v) ↔
        (i.val < v.2.val.val ∨ i = v.2.val ∧ (0 : ℝ) < visitParameter (visitTransport hs v))
      exact or_congr Iff.rfl (and_congr Iff.rfl ⟨fun _ => h2, fun _ => h1⟩)
  | inr v =>
    cases b with
    | inl i =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hP' (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter v < (0 : ℝ)) ↔
        (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter (visitTransport hs v) < (0 : ℝ))
      exact or_congr Iff.rfl (and_congr Iff.rfl
        ⟨fun h => (lt_asymm h1 h).elim, fun h => (lt_asymm h2 h).elim⟩)
    | inr w => exact W.key_lt v w (hab v w rfl rfl)

/-- A good mark and a corner: their key order is carried, in both directions. -/
theorem GT_good_key_lt (W : GT_Wall hP hP' hs T S) {m d : Mark P} (hm : GT_Good T S m)
    (hd : IsTrueCorner S d) :
    (geoMarkKey hP m < geoMarkKey hP d ↔
        geoMarkKey hP' (markTransport hs m) < geoMarkKey hP' (markTransport hs d)) ∧
    (geoMarkKey hP d < geoMarkKey hP m ↔
        geoMarkKey hP' (markTransport hs d) < geoMarkKey hP' (markTransport hs m)) := by
  have hno : ∀ v w : Visit P, m = Sum.inr v → d = Sum.inr w → ¬ GT_Rev T v w := by
    rintro v w rfl rfl hrev
    exact hm v rfl w hrev hd
  exact ⟨GT_mark_key_lt W m d hno,
    GT_mark_key_lt W d m fun w v hw hv h => hno v w hv hw h.symm⟩

/-! ### Transport of the next-corner specifications (the AV proofs, `GT_good_key_lt` in place of
`AV_good_key_lt`) -/

theorem GT_ncspec_transport (W : GT_Wall hP hP' hs T S) {m d : Mark P} (hm : GT_Good T S m)
    (h : AV_NCSpec hP S m d) :
    AV_NCSpec hP' (transportSupport hs S) (markTransport hs m) (markTransport hs d) := by
  obtain ⟨hc, h⟩ := h
  refine ⟨(AV_corner_transport S d).mpr hc, ?_⟩
  rcases h with ⟨hle, hmin⟩ | ⟨hall, rfl⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [← not_lt] at hle ⊢
      exact fun h' => hle (((GT_good_key_lt W hm hc).2).mpr h')
    · intro d'' hd'' hle''
      obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
      have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
      have hle' : geoMarkKey hP m ≤ geoMarkKey hP d' := by
        rw [← not_lt] at hle'' ⊢
        exact fun h' => hle'' (((GT_good_key_lt W hm hd').2).mp h')
      have hdd' := hmin d' hd' hle'
      rw [← not_lt] at hdd' ⊢
      exact fun h' => hdd' (((GT_good_key_lt W (GT_good_of_corner W hc) hd').2).mpr h')
  · right
    refine ⟨?_, markTransport_vertex hs 0⟩
    intro d'' hd''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    exact ((GT_good_key_lt W hm hd').2).mp (hall d' hd')

open scoped Classical in
/-- **The next corner of a good mark is carried across the wall.** -/
theorem GT_nextCorner_transport (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : GT_Good T S m) :
    AV_nextCorner hP' (transportSupport hs S) (markTransport hs m) =
      markTransport hs (AV_nextCorner hP S m) :=
  AV_ncspec_unique (AV_nextCorner_spec hP' _ _) (GT_ncspec_transport W hm (AV_nextCorner_spec hP S m))

theorem GT_csspec_transport (W : GT_Wall hP hP' hs T S) {x d : Mark P} (hx : IsTrueCorner S x)
    (h : AV_CSSpec hP S x d) :
    AV_CSSpec hP' (transportSupport hs S) (markTransport hs x) (markTransport hs d) := by
  obtain ⟨hc, h⟩ := h
  have hxg : GT_Good T S x := GT_good_of_corner W hx
  refine ⟨(AV_corner_transport S d).mpr hc, ?_⟩
  rcases h with ⟨hlt, hmin⟩ | ⟨hall, rfl⟩
  · left
    refine ⟨((GT_good_key_lt W hxg hc).1).mp hlt, ?_⟩
    intro d'' hd'' hlt''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    have hlt' : geoMarkKey hP x < geoMarkKey hP d' := ((GT_good_key_lt W hxg hd').1).mpr hlt''
    have hdd' := hmin d' hd' hlt'
    rw [← not_lt] at hdd' ⊢
    exact fun h' => hdd' (((GT_good_key_lt W (GT_good_of_corner W hc) hd').2).mpr h')
  · right
    refine ⟨?_, markTransport_vertex hs 0⟩
    intro d'' hd''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    have h1 := hall d' hd'
    rw [← not_lt] at h1 ⊢
    exact fun h' => h1 (((GT_good_key_lt W hxg hd').1).mpr h')

/-- **The corner successor of a corner is carried across the wall.** -/
theorem GT_cornerSucc_transport (W : GT_Wall hP hP' hs T S) {c : Mark P} (hc : IsTrueCorner S c) :
    AV_cornerSucc hP' (transportSupport hs S) (markTransport hs c) =
      markTransport hs (AV_cornerSucc hP S c) := by
  have h1 : AV_CSSpec hP' (transportSupport hs S) (markTransport hs (selectedMarkPerm S c))
      (AV_cornerSucc hP' (transportSupport hs S) (markTransport hs c)) := by
    unfold AV_cornerSucc
    rw [geoSmoothingSuccessor_apply, selectedMarkPerm_markTransport]
    exact AV_nextCorner_succ_spec hP' _ _
  have h2 : AV_CSSpec hP' (transportSupport hs S) (markTransport hs (selectedMarkPerm S c))
      (markTransport hs (AV_cornerSucc hP S c)) :=
    GT_csspec_transport W (AV_corner_selectedMarkPerm S hc)
      (by unfold AV_cornerSucc; rw [geoSmoothingSuccessor_apply]; exact AV_nextCorner_succ_spec hP S _)
  exact AV_csspec_unique h1 h2

/-! ### The carrier bijection across the wall -/

theorem GT_carrierMap_aux (W : GT_Wall hP hP' hs T S) (m : Mark P) :
    geoOwner hP' (transportSupport hs S)
        (markTransport hs (AV_nextCorner hP S (geoSmoothingSuccessor hP S m))) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := by
  by_cases hm : IsTrueCorner S m
  · change geoOwner hP' (transportSupport hs S) (markTransport hs (AV_cornerSucc hP S m)) = _
    rw [← GT_cornerSucc_transport W hm, AV_cornerSucc_owner, AV_nextCorner_of_corner hm]
  · rw [AV_smoothing_of_not_corner hP S hm, AV_nextCorner_succ hm]

theorem GT_carrierMap_pow (W : GT_Wall hP hP' hs T S) (m : Mark P) (k : ℕ) :
    geoOwner hP' (transportSupport hs S)
        (markTransport hs (AV_nextCorner hP S ((geoSmoothingSuccessor hP S ^ k) m))) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, GT_carrierMap_aux W, ih]

/-- The carrier map across the wall: the carrier of `P'` through the transported next corner. -/
noncomputable def GT_carrierMap (W : GT_Wall hP hP' hs T S) :
    GeoComponent hP S → GeoComponent hP' (transportSupport hs S) :=
  Quotient.lift
    (fun m => geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)))
    (fun a b hab => by
      obtain ⟨i, -, rfl⟩ :=
        (show (geoSmoothingSuccessor hP S).SameCycle a b from hab).exists_pow_eq'
      exact (GT_carrierMap_pow W a i).symm)

theorem GT_carrierMap_owner (W : GT_Wall hP hP' hs T S) (m : Mark P) :
    GT_carrierMap W (geoOwner hP S m) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := rfl

theorem GT_carrierInv_aux (W : GT_Wall hP hP' hs T S) (m' : Mark P') :
    geoOwner hP S ((markTransport hs).symm
        (AV_nextCorner hP' (transportSupport hs S) (geoSmoothingSuccessor hP' (transportSupport hs S) m'))) =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
  by_cases hm : IsTrueCorner (transportSupport hs S) m'
  · change geoOwner hP S ((markTransport hs).symm (AV_cornerSucc hP' (transportSupport hs S) m')) = _
    have hc : IsTrueCorner S ((markTransport hs).symm m') := by
      rw [← AV_corner_transport (hs := hs) S ((markTransport hs).symm m'), Equiv.apply_symm_apply]
      exact hm
    have := GT_cornerSucc_transport W hc
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply, AV_cornerSucc_owner, AV_nextCorner_of_corner hm]
  · rw [AV_smoothing_of_not_corner hP' _ hm, AV_nextCorner_succ hm]

theorem GT_carrierInv_pow (W : GT_Wall hP hP' hs T S) (m' : Mark P') (k : ℕ) :
    geoOwner hP S ((markTransport hs).symm
        (AV_nextCorner hP' (transportSupport hs S) ((geoSmoothingSuccessor hP' (transportSupport hs S) ^ k) m'))) =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, GT_carrierInv_aux W, ih]

/-- The inverse carrier map. -/
noncomputable def GT_carrierInv (W : GT_Wall hP hP' hs T S) :
    GeoComponent hP' (transportSupport hs S) → GeoComponent hP S :=
  Quotient.lift
    (fun m' => geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')))
    (fun a b hab => by
      obtain ⟨i, -, rfl⟩ :=
        (show (geoSmoothingSuccessor hP' (transportSupport hs S)).SameCycle a b from hab).exists_pow_eq'
      exact (GT_carrierInv_pow W a i).symm)

theorem GT_carrierInv_owner (W : GT_Wall hP hP' hs T S) (m' : Mark P') :
    GT_carrierInv W (geoOwner hP' (transportSupport hs S) m') =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := rfl

/-- **The carriers of `S` correspond to the carriers of the transported support across the wall**:
the corner cycles are carried, corner by corner. -/
noncomputable def GT_carrierEquiv (W : GT_Wall hP hP' hs T S) :
    GeoComponent hP S ≃ GeoComponent hP' (transportSupport hs S) where
  toFun := GT_carrierMap W
  invFun := GT_carrierInv W
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h m =>
      change GT_carrierInv W (GT_carrierMap W (geoOwner hP S m)) = geoOwner hP S m
      rw [GT_carrierMap_owner, GT_carrierInv_owner,
        AV_nextCorner_of_corner ((AV_corner_transport S _).mpr (AV_nextCorner_corner hP S m)),
        Equiv.symm_apply_apply, AV_nextCorner_owner]
  right_inv q' := by
    induction q' using Quotient.inductionOn with
    | h m' =>
      change GT_carrierMap W (GT_carrierInv W (geoOwner hP' (transportSupport hs S) m')) =
        geoOwner hP' (transportSupport hs S) m'
      rw [GT_carrierInv_owner, GT_carrierMap_owner]
      have hc : IsTrueCorner S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
        rw [← AV_corner_transport (hs := hs) S, Equiv.apply_symm_apply]
        exact AV_nextCorner_corner hP' _ m'
      rw [AV_nextCorner_of_corner hc, Equiv.apply_symm_apply, AV_nextCorner_owner]

theorem GT_carrierEquiv_owner (W : GT_Wall hP hP' hs T S) (m : Mark P) :
    GT_carrierEquiv W (geoOwner hP S m) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := rfl

/-- **Ownership of good marks is carried**: a good mark lies on the copy of its carrier. -/
theorem GT_owner_transport (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : GT_Good T S m) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) =
      GT_carrierEquiv W (geoOwner hP S m) := by
  rw [GT_carrierEquiv_owner, ← GT_nextCorner_transport W hm, AV_nextCorner_owner]

theorem GT_owner_transport_corner (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : IsTrueCorner S m) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) =
      GT_carrierEquiv W (geoOwner hP S m) :=
  GT_owner_transport W (GT_good_of_corner W hm)

/-- Ownership of a good mark, as an equivalence of "lies on `q`" and "lies on the copy of `q`". -/
theorem GT_owner_iff (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : GT_Good T S m)
    (q : GeoComponent hP S) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) = GT_carrierEquiv W q ↔
      geoOwner hP S m = q := by
  rw [GT_owner_transport W hm]
  exact (GT_carrierEquiv W).injective.eq_iff

/-! ### The corner list of a carrier is carried literally; turns, selector, `wind` -/

theorem GT_cornerList_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    (geoComponentCornerList hP S q).map (markTransport hs) =
      geoComponentCornerList hP' (transportSupport hs S) (GT_carrierEquiv W q) := by
  apply List.Perm.eq_of_pairwise (le := fun a b => geoMarkKey hP' a < geoMarkKey hP' b)
  · intro a b _ _ h1 h2
    exact absurd h2 (lt_asymm h1)
  · rw [List.pairwise_map]
    refine (AV_cornerList_pairwise hP S q).imp_of_mem ?_
    intro a b ha hb hab
    exact ((GT_good_key_lt W
      (GT_good_of_corner W ((mem_geoComponentCornerList hP S q a).mp ha).2)
      ((mem_geoComponentCornerList hP S q b).mp hb).2).1).mp hab
  · exact AV_cornerList_pairwise hP' _ _
  · rw [List.perm_ext_iff_of_nodup
      ((geoComponentCornerList_nodup hP S q).map (markTransport hs).injective)
      (geoComponentCornerList_nodup hP' _ _)]
    intro a'
    obtain ⟨a, rfl⟩ := (markTransport hs).surjective a'
    rw [List.mem_map_of_injective (markTransport hs).injective, mem_geoComponentCornerList,
      mem_geoComponentCornerList, AV_corner_transport]
    constructor
    · rintro ⟨hq, hc⟩
      exact ⟨by rw [GT_owner_transport_corner W hc, hq], hc⟩
    · rintro ⟨hq, hc⟩
      refine ⟨?_, hc⟩
      rw [GT_owner_transport_corner W hc] at hq
      exact (GT_carrierEquiv W).injective hq

theorem GT_cornerCount_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCornerCount hP' (transportSupport hs S) (GT_carrierEquiv W q) = geoCornerCount hP S q := by
  unfold geoCornerCount
  rw [← GT_cornerList_eq W q, List.length_map]

theorem GT_cornerMark_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP' (transportSupport hs S) (GT_carrierEquiv W q)
        (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q).symm) k) =
      markTransport hs (geoCornerMark hP S q k) := by
  have hL := GT_cornerList_eq W q
  have hlen : k.val < (geoComponentCornerList hP' (transportSupport hs S) (GT_carrierEquiv W q)).length := by
    rw [← hL, List.length_map]; exact ZMod.val_lt k
  have h3 : k.val < ((geoComponentCornerList hP S q).map (markTransport hs)).length := by
    rw [List.length_map]; exact ZMod.val_lt k
  unfold geoCornerMark
  refine (geo_getElem_congr _ _ rfl _ _ _ hlen (geo_zmod_val_cast (GT_cornerCount_eq W q).symm k)).trans ?_
  refine (geo_getElem_congr _ _ hL.symm _ _ hlen h3 rfl).trans ?_
  exact List.getElem_map _

theorem GT_cornerMark_eq' (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (j : ZMod (geoCornerCount hP' (transportSupport hs S) (GT_carrierEquiv W q))) :
    geoCornerMark hP' (transportSupport hs S) (GT_carrierEquiv W q) j =
      markTransport hs (geoCornerMark hP S q (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q)) j)) := by
  have h := GT_cornerMark_eq W q (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q)) j)
  rwa [geo_zmod_cast_cast (GT_cornerCount_eq W q) j] at h

/-- The corner polygon of `q` read at the geometry of `P'`. -/
noncomputable def GT_tcp (_W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    LabelledTuple (geoCornerCount hP S q) :=
  fun k => traversalEvaluation P' (geoMarkPosition hP' (markTransport hs (geoCornerMark hP S q k)))

theorem GT_cornerPolygon_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCornerPolygon hP' (transportSupport hs S) (GT_carrierEquiv W q) =
      geoRecast (GT_cornerCount_eq W q) (GT_tcp W q) := by
  funext j
  show traversalEvaluation P' (geoMarkPosition hP' (geoCornerMark hP' (transportSupport hs S)
    (GT_carrierEquiv W q) j)) = _
  rw [GT_cornerMark_eq' W q j]
  rfl

theorem GT_tcp_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    GT_tcp W q =
      geoRecast (GT_cornerCount_eq W q).symm
        (geoCornerPolygon hP' (transportSupport hs S) (GT_carrierEquiv W q)) := by
  rw [GT_cornerPolygon_eq W q]
  funext k
  rw [geoRecast_apply, geoRecast_apply, geo_zmod_cast_cast' (GT_cornerCount_eq W q) k]

theorem GT_turn_tcp_eq_turn_cast (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (GT_tcp W q) k =
      turn (geoCornerPolygon hP' (transportSupport hs S) (GT_carrierEquiv W q))
        (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q).symm) k) := by
  rw [GT_cornerPolygon_eq W q, turn_geoRecast_cast]

/-- **Corner turns are carried across the wall**: vertex corners by `turn_eq`, smoothing corners by
`sign_eq`. -/
theorem GT_turn_tcp (W : GT_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (GT_tcp W q) k = turn (geoCornerPolygon hP S q) k := by
  have hS := W.indep
  have hS' := W.indep'
  rw [GT_turn_tcp_eq_turn_cast W q k]
  have hmark := GT_cornerMark_eq W q k
  have hcorner := isTrueCorner_geoCornerMark hP S q k
  cases hc : geoCornerMark hP S q k with
  | inl i =>
    rw [hc, markTransport_vertex] at hmark
    rw [geoCornerPolygon_turn_vertex hn hP' hS' _ _ i hmark,
      geoCornerPolygon_turn_vertex hn hP hS q k i hc]
    exact W.turn_eq i
  | inr v =>
    rw [hc] at hcorner
    have hv : v.1 ∈ S := (isTrueCorner_visit S v).mp hcorner
    rw [hc, markTransport_visit] at hmark
    have hv' : (visitTransport hs v).1 ∈ transportSupport hs S := by
      rw [visitTransport_crossing, mem_transportSupport_iff]; exact hv
    rw [geoCornerPolygon_turn_visit hn hP' hS' _ _ (visitTransport hs v) hv' hmark,
      geoCornerPolygon_turn_visit hn hP hS q k v hv hc, ← visitTransport_visitTwin,
      visitTransport_edge, visitTransport_edge]
    apply W.sign_eq
    rw [← visit_crossing_val_eq_pair v]
    exact v.1.property

/-- The selector (`wt`) of a carrier is carried across the wall. -/
theorem GT_selector_eq (W : GT_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S) :
    geoCarrierSelector hP' (transportSupport hs S) (GT_carrierEquiv W q) = geoCarrierSelector hP S q := by
  unfold geoCarrierSelector
  rw [GT_cornerPolygon_eq W q, cornerSelector_geoRecast]
  exact cornerSelector_congr_turn (GT_turn_tcp W hn q)

/-- `wind(S)` is carried across the wall. -/
theorem GT_geoWind_eq (W : GT_Wall hP hP' hs T S) (hn : 3 ≤ n) :
    geoWind hP' (transportSupport hs S) = geoWind hP S := by
  unfold geoWind
  exact (Fintype.prod_equiv (GT_carrierEquiv W) _ _ fun q => (GT_selector_eq W hn q).symm).symm

/-! ### The rotation of a carrier is carried (CV:def:rot's ray formula, as `AV_rotationNumber_tcp`) -/

theorem GT_edge_tcp (W : GT_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      edge (GT_tcp W q) k = c • edge P' (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  rw [GT_tcp_eq W q, AV_edge_geoRecast]
  obtain ⟨c, hc, h⟩ := geoCornerPolygon_edge_smul hn hP' W.indep' (GT_carrierEquiv W q)
    (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q).symm) k)
  refine ⟨c, hc, ?_⟩
  rw [h, GT_cornerMark_eq' W q, geo_zmod_cast_cast' (GT_cornerCount_eq W q) k, AV_outSlot_transport]

theorem GT_rotationNumber_tcp (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (W : GT_Wall hG.cg hG'.cg hs T S) (q : GeoComponent hG.cg S) :
    rotationNumber (GT_tcp W q) = rotationNumber (geoCornerPolygon hG.cg S q) := by
  obtain ⟨r, hr⟩ := W.ray
  have hL : CV.Regular (geoCornerPolygon hG.cg S q) :=
    (CV.regular_iff_sm _).mpr (geoCornerPolygon_regular hn hG W.indep q)
  have hL'' : CV.Regular (GT_tcp W q) := by
    rw [CV.regular_iff_sm, GT_tcp_eq W q, regular_geoRecast]
    exact geoCornerPolygon_regular hn hG' W.indep' _
  have hr' : ∀ h : ZMod n, det r (edge P' h) ≠ 0 := by
    intro h h0
    have := (hr h).2
    rw [h0, sign_zero] at this
    exact (hr h).1 (sign_eq_zero_iff.mp this.symm)
  have hadm : CV.Admissible (geoCornerPolygon hG.cg S q) r := by
    intro k
    obtain ⟨c, hc, h⟩ := geoCornerPolygon_edge_smul hn hG.cg W.indep q k
    rw [h, det_smul_right]
    exact mul_ne_zero hc.ne' (hr _).1
  have hadm'' : CV.Admissible (GT_tcp W q) r := by
    intro k
    obtain ⟨c, hc, h⟩ := GT_edge_tcp W hn q k
    rw [h, det_smul_right]
    exact mul_ne_zero hc.ne' (hr' _)
  rw [← CV.rotRay_eq_rotationNumber hL hadm, ← CV.rotRay_eq_rotationNumber hL'' hadm'']
  congr 1
  unfold CV.rotRay
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [CV.epsRot_eq_epsOfSigns, CV.epsRot_eq_epsOfSigns]
  have hturn : SignType.sign (det (edge (GT_tcp W q) (k - 1)) (edge (GT_tcp W q) k)) =
      SignType.sign (det (edge (geoCornerPolygon hG.cg S q) (k - 1))
        (edge (geoCornerPolygon hG.cg S q) k)) := by
    rw [← turn_det, ← turn_det]
    exact GT_turn_tcp W hn q k
  have hray : ∀ j : ZMod (geoCornerCount hG.cg S q),
      SignType.sign (det r (edge (GT_tcp W q) j)) =
        SignType.sign (det r (edge (geoCornerPolygon hG.cg S q) j)) := by
    intro j
    obtain ⟨c, hc, h⟩ := GT_edge_tcp W hn q j
    obtain ⟨c', hc', h'⟩ := geoCornerPolygon_edge_smul hn hG.cg W.indep q j
    rw [h, h', AV_sign_det_smul_right c hc, AV_sign_det_smul_right c' hc']
    exact (hr _).2
  have hray' : ∀ j : ZMod (geoCornerCount hG.cg S q),
      SignType.sign (det (edge (GT_tcp W q) j) r) =
        SignType.sign (det (edge (geoCornerPolygon hG.cg S q) j) r) := by
    intro j
    rw [AV_sign_det_swap (edge (GT_tcp W q) j) r,
      AV_sign_det_swap (edge (geoCornerPolygon hG.cg S q) j) r, hray j]
  rw [hturn, hray' (k - 1), hray k]

/-! ### The def:X1 objects on `CV.Generic` binders -/

theorem GT_carrierR_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : GT_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.carrierR hn hG' hS' (GT_carrierEquiv W q) = CV.carrierR hn hG hS q := by
  unfold CV.carrierR CV.rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [CV.rot_eq_rotationNumber, CV.rot_eq_rotationNumber, GT_cornerPolygon_eq W q,
    rotationNumber_geoRecast]
  exact GT_rotationNumber_tcp hn (CarrierGeometry.ofCV hG) (CarrierGeometry.ofCV hG') W q

theorem GT_weight_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : GT_Wall hG.crossingGeometry hG'.crossingGeometry hs T S) (q : GeoComponent hG.crossingGeometry S) :
    CV.weight hG'.crossingGeometry (transportSupport hs S) (GT_carrierEquiv W q) =
      CV.weight hG.crossingGeometry S q :=
  GT_selector_eq W hn q

theorem GT_wind_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : GT_Wall hG.crossingGeometry hG'.crossingGeometry hs T S) :
    CV.wind hG'.crossingGeometry (transportSupport hs S) = CV.wind hG.crossingGeometry S :=
  GT_geoWind_eq W hn

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}
variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}

/-! ### Retained crossings when every unselected visit is good (the empty row) -/

/-- **The retained crossings of a carrier are carried to those of its copy** when every visit of an
unselected crossing is a good mark (no reversed partner is a corner). -/
theorem GT_geoCarrierCrossings_eq_of_good (W : GT_Wall hP hP' hs T S)
    (hgood : ∀ v : Visit P, v.1 ∉ S → GT_Good T S (Sum.inr v)) (q : GeoComponent hP S) :
    geoCarrierCrossings hP' (transportSupport hs S) (GT_carrierEquiv W q) =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding := by
  classical
  ext x'
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_geoCarrierCrossings, mem_geoCarrierCrossings,
    mem_transportSupport_iff]
  constructor
  · rintro ⟨hxS, hall⟩
    refine ⟨hxS, fun v hv => ?_⟩
    have := hall (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, GT_owner_transport W (hgood v (hv ▸ hxS))] at this
    exact (GT_carrierEquiv W).injective this
  · rintro ⟨hxS, hall⟩
    refine ⟨hxS, fun w hw => ?_⟩
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
    rw [visitTransport_crossing] at hw
    have hvx : v.1 = x := (crossingTransport hs).injective hw
    rw [← markTransport_visit, GT_owner_transport W (hgood v (hvx ▸ hxS)), hall v hvx]

/-! ### Pieces under a relabelling of the retained crossings (the endpoint rows) -/

/-- **Relabelling data**: a bijection `φ` of the crossings agreeing with the edge-pair transport on
`S`, carrying the retained crossings of every carrier to those of its copy, carrying `U(S)` and the
residual interlacement. (For the endpoint rows `φ` is the transport composed with the exchange of
the two unselected triangle crossings; for a triangle-free support it is the transport itself.) -/
structure GT_Relabel (W : GT_Wall hP hP' hs T S) (φ : Crossing P ≃ Crossing P') : Prop where
  phi_S : ∀ c ∈ S, φ c = crossingTransport hs c
  retained : ∀ q : GeoComponent hP S,
    geoCarrierCrossings hP' (transportSupport hs S) (GT_carrierEquiv W q) =
      (geoCarrierCrossings hP S q).map φ.toEmbedding
  mem_U : ∀ y : Crossing P, φ y ∈ CV.U hP' (transportSupport hs S) ↔ y ∈ CV.U hP S
  adj : ∀ y ∈ CV.U hP S, ∀ z ∈ CV.U hP S,
    (GeometricInterlaces hP' (φ y) (φ z) ↔ GeometricInterlaces hP y z)

variable {W : GT_Wall hP hP' hs T S} {φ : Crossing P ≃ Crossing P'}

/-- The residual graphs are isomorphic along `φ`. -/
noncomputable def GT_residualIso (R : GT_Relabel W φ) :
    CV.residualGraph hP S ≃g CV.residualGraph hP' (transportSupport hs S) where
  toEquiv := Equiv.subtypeEquiv φ (fun y => (R.mem_U y).symm)
  map_rel_iff' := by
    intro a b
    show GeometricInterlaces hP' (φ a.1) (φ b.1) ↔ GeometricInterlaces hP a.1 b.1
    exact R.adj a.1 a.2 b.1 b.2

theorem GT_residualIso_apply_val (R : GT_Relabel W φ) (a : ↑(CV.U hP S)) :
    ((GT_residualIso R) a).1 = φ a.1 := rfl

/-- The pieces of `S` correspond to the pieces of the transported support along `φ`. -/
noncomputable def GT_pieceEquiv (R : GT_Relabel W φ) :
    CV.Piece hP S ≃ CV.Piece hP' (transportSupport hs S) :=
  (GT_residualIso R).connectedComponentEquiv

theorem GT_pieceEquiv_pieceOf (R : GT_Relabel W φ) (c : Crossing P) (hc : c ∈ CV.U hP S) :
    GT_pieceEquiv R (CV.pieceOf hP S c hc) =
      CV.pieceOf hP' (transportSupport hs S) (φ c) ((R.mem_U c).mpr hc) := by
  unfold GT_pieceEquiv CV.pieceOf
  rw [SimpleGraph.Iso.connectedComponentEquiv_apply, SimpleGraph.ConnectedComponent.map_mk]
  rfl

/-- The labels of a piece are carried along `φ`. -/
theorem GT_pieceLabels_eq (R : GT_Relabel W φ) (H : CV.Piece hP S) :
    CV.pieceLabels hP' (transportSupport hs S) (GT_pieceEquiv R H) =
      (CV.pieceLabels hP S H).map φ.toEmbedding := by
  ext c'
  obtain ⟨c, rfl⟩ := φ.surjective c'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, CV.mem_pieceLabels, CV.mem_pieceLabels]
  constructor
  · rintro ⟨hc', hH⟩
    have hc : c ∈ CV.U hP S := (R.mem_U c).mp hc'
    refine ⟨hc, (GT_pieceEquiv R).injective ?_⟩
    rw [GT_pieceEquiv_pieceOf]
    exact hH
  · rintro ⟨hc, hH⟩
    refine ⟨(R.mem_U c).mpr hc, ?_⟩
    rw [← GT_pieceEquiv_pieceOf R c hc, hH]

theorem GT_pieceWrithe_eq (R : GT_Relabel W φ) (H : CV.Piece hP S) :
    CV.pieceWrithe hP' (transportSupport hs S) (GT_pieceEquiv R H) = CV.pieceWrithe hP S H := by
  unfold CV.pieceWrithe
  rw [GT_pieceLabels_eq, Finset.card_map]

/-- A piece is assigned to a carrier iff its labels are among the carrier's retained crossings. -/
theorem GT_mem_piecesOn_iff_subset (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (H : CV.Piece hP S) :
    H ∈ CV.piecesOn hP S q ↔ CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q := by
  rw [CV.mem_piecesOn]
  constructor
  · intro h c hc
    rw [mem_geoCarrierCrossings]
    exact ⟨((CV.mem_U_iff hP S c).mp (CV.pieceLabels_subset hP S H hc)).1, h c hc⟩
  · intro h c hc v hv
    exact ((mem_geoCarrierCrossings hP S q c).mp (h hc)).2 v hv

/-- The pieces assigned to a carrier are carried onto the pieces assigned to its copy. -/
theorem GT_piecesOn_eq (R : GT_Relabel W φ) (q : GeoComponent hP S) :
    CV.piecesOn hP' (transportSupport hs S) (GT_carrierEquiv W q) =
      (CV.piecesOn hP S q).map (GT_pieceEquiv R).toEmbedding := by
  ext H'
  obtain ⟨H, rfl⟩ := (GT_pieceEquiv R).surjective H'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, GT_mem_piecesOn_iff_subset,
    GT_mem_piecesOn_iff_subset, GT_pieceLabels_eq, R.retained]
  exact Finset.map_subset_map

theorem GT_card_geoCarrierCrossings_eq (R : GT_Relabel W φ) (q : GeoComponent hP S) :
    (geoCarrierCrossings hP' (transportSupport hs S) (GT_carrierEquiv W q)).card =
      (geoCarrierCrossings hP S q).card := by
  rw [R.retained, Finset.card_map]

/-! ### `P_{S,L}` is the HOMFLY polynomial of the positive lift (CV:cor:groupedknot (B), both cases) -/

/-- **`P_{S,L} = P(D(W))`** on every carrier: cor:groupedknot (B) `grouped_polynomial` when the carrier
bears a piece, and its parenthetical `no_piece` (`P_{S,L} = 1 = P(○)`) otherwise. -/
theorem GT_groupedPoly_eq_homfly (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    CV.groupedPoly hn hG hS q = homfly (CV.carrierDiagram hn hG hS q) := by
  by_cases hne : (CV.piecesOn hG.crossingGeometry S q).Nonempty
  · exact ((CV.groupedknot hn hG hS q).grouped_polynomial hne).1.symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨h1, -, -, h4⟩ := (CV.groupedknot hn hG hS q).no_piece hne
    rw [h1, h4]

/-! ### The generalized record isomorphism of two lifts (EXT_homfly_wall with an arbitrary visit
bijection) -/

/-- **Two carriers whose retained visits correspond through any bijection `ψ` compatible with the
twin pairing, carrying the cyclic key order and the divide signs, have positive lifts with the same
HOMFLY polynomial**: `ψ` lifted through the parent-visit maps is a record isomorphism (CV:def:record
(a)–(d), `recordIsoOfData`) and CV:ax:gausscode (`gausscode_polynomial`) applies. `EXT_homfly_wall` is
the case `ψ = visitTransport`. -/
theorem GT_homfly_wall_gen (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
    (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
    (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
    (ψ : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q} ≃
      {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q'})
    (htwin : ∀ (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q),
      (ψ ⟨visitTwin v, by rw [visitTwin_crossing]; exact hv⟩).1 = visitTwin (ψ ⟨v, hv⟩).1)
    (hcyc : ∀ u v w : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q},
      cycBetween (geometricVisitKey hG.cg u.1) (geometricVisitKey hG.cg v.1) (geometricVisitKey hG.cg w.1) →
      cycBetween (geometricVisitKey hG'.cg (ψ u).1) (geometricVisitKey hG'.cg (ψ v).1)
        (geometricVisitKey hG'.cg (ψ w).1))
    (hdet : ∀ v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q},
      (0 < det (edge P v.1.2.val) (edge P (visitTwin v.1).2.val) ↔
        0 < det (edge P' (ψ v).1.2.val) (edge P' (visitTwin (ψ v).1).2.val))) :
    homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q) := by
  let Φ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit :=
    (CV.liftVisitEquiv hn hG hT q).trans (ψ.trans (CV.liftVisitEquiv hn hG' hT' q').symm)
  have hΦ : ∀ v, CV.liftVisit hn hG' hT' q' (Φ v) = (ψ (CV.liftVisitEquiv hn hG hT q v)).1 := by
    intro v
    show CV.liftVisit hn hG' hT' q'
      ((CV.liftVisitEquiv hn hG' hT' q').symm (ψ (CV.liftVisitEquiv hn hG hT q v))) = _
    rw [CV.liftVisit_symm]
  have hval : ∀ v, (CV.liftVisitEquiv hn hG hT q v).1 = CV.liftVisit hn hG hT q v := fun v => rfl
  have hdata : CV.IsRecordIsoData (geoPositiveLift hn hG hT q) (geoPositiveLift hn hG' hT' q') Φ :=
    { cyclic_order := fun v w u hb => by
        rw [CV.visitBetween_iff_key, hΦ, hΦ, hΦ]
        rw [CV.visitBetween_iff_key] at hb
        exact hcyc _ _ _ (by simpa only [hval] using hb)
      double_points :=
        (CV.carriesDoublePoints_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG' hT' q').record) Φ).2 fun v => by
          apply CV.liftVisit_injective hn hG' hT' q'
          change CV.liftVisit hn hG' hT' q' (Φ ((geoPositiveLift hn hG hT q).twin v)) =
            CV.liftVisit hn hG' hT' q' ((geoPositiveLift hn hG' hT' q').twin (Φ v))
          rw [hΦ, CV.liftVisit_twin, hΦ]
          have h := htwin (CV.liftVisit hn hG hT q v) (CV.liftVisit_mem hn hG hT q v)
          have hL : CV.liftVisitEquiv hn hG hT q ((geoPositiveLift hn hG hT q).twin v) =
              ⟨visitTwin (CV.liftVisit hn hG hT q v), by
                rw [visitTwin_crossing]; exact CV.liftVisit_mem hn hG hT q v⟩ :=
            Subtype.ext (CV.liftVisit_twin hn hG hT q v)
          rw [hL, h]
          rfl
      over_under :=
        (CV.carriesOverUnder_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG' hT' q').record) Φ).2 fun v => by
          change (geoPositiveLift hn hG' hT' q').overBit (Φ v) = (geoPositiveLift hn hG hT q).overBit v
          rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΦ]
          exact (hdet (CV.liftVisitEquiv hn hG hT q v)).symm
      signs := fun v => by
        change (geoPositiveLift hn hG' hT' q').sign (Φ v).1 = (geoPositiveLift hn hG hT q).sign v.1
        rw [geoPositiveLift_sign, geoPositiveLift_sign] }
  exact (CV.gausscode_polynomial _ _ (geoPositiveLift_componentCount hn hG hT q)
    (geoPositiveLift_componentCount hn hG' hT' q')
    (CV.recordIsoOfData (geoPositiveLift_componentCount hn hG hT q)
      (geoPositiveLift_componentCount hn hG' hT' q') Φ hdata)).symm

end GT

section GT

open SM.Carrier SM.Link

/-! ### Real-number cyclic-order lemmas for the relabelled record isomorphism -/

theorem GT_cyc_gt_gt {a x y : ℝ} (hx : a < x) (hy : a < y) : cycBetween a x y ↔ x < y := by
  unfold cycBetween
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> first | exact h | (exfalso; linarith)
  · intro h; exact Or.inl ⟨hx, h⟩

theorem GT_cyc_gt_lt {a x y : ℝ} (hx : a < x) (hy : y < a) : cycBetween a x y := by
  unfold cycBetween
  exact Or.inr (Or.inr ⟨hy, hx⟩)

theorem GT_cyc_lt_gt {a x y : ℝ} (hx : x < a) (hy : a < y) : ¬ cycBetween a x y := by
  unfold cycBetween
  rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> linarith

theorem GT_cyc_lt_lt {a x y : ℝ} (hx : x < a) (hy : y < a) : cycBetween a x y ↔ x < y := by
  unfold cycBetween
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩) <;> first | exact h | (exfalso; linarith)
  · intro h; exact Or.inr (Or.inl ⟨h, hy⟩)

/-- **Cyclic betweenness read from a base point `a`**: for `a` distinct from `u, v, s`, the cyclic order
of `(u, v, s)` is the cyclic closure of the linear order "first after `a`" (`cycBetween a · ·`). -/
theorem GT_cyc_base {a u v s : ℝ} (hau : a ≠ u) (hav : a ≠ v) (has : a ≠ s) :
    cycBetween u v s ↔
      (cycBetween a u v ∧ cycBetween a v s) ∨ (cycBetween a v s ∧ cycBetween a s u) ∨
      (cycBetween a s u ∧ cycBetween a u v) := by
  rcases lt_or_gt_of_ne hau with h1 | h1 <;> rcases lt_or_gt_of_ne hav with h2 | h2 <;>
    rcases lt_or_gt_of_ne has with h3 | h3
  · rw [GT_cyc_gt_gt h1 h2, GT_cyc_gt_gt h2 h3, GT_cyc_gt_gt h3 h1]; rfl
  · have hq : ¬ v < s := by intro h; linarith
    have hr : s < u := by linarith
    rw [iff_true_intro (GT_cyc_gt_lt h2 h3), iff_false_intro (GT_cyc_lt_gt h3 h1), GT_cyc_gt_gt h1 h2]
    unfold cycBetween; tauto
  · have hp : ¬ u < v := by intro h; linarith
    have hq : v < s := by linarith
    rw [iff_true_intro (GT_cyc_gt_lt h1 h2), iff_false_intro (GT_cyc_lt_gt h2 h3), GT_cyc_gt_gt h3 h1]
    unfold cycBetween; tauto
  · have hp : ¬ u < v := by intro h; linarith
    have hr : s < u := by linarith
    rw [iff_true_intro (GT_cyc_gt_lt h1 h2), iff_false_intro (GT_cyc_lt_gt h3 h1), GT_cyc_lt_lt h2 h3]
    unfold cycBetween; tauto
  · have hp : u < v := by linarith
    have hr : ¬ s < u := by intro h; linarith
    rw [iff_false_intro (GT_cyc_lt_gt h1 h2), iff_true_intro (GT_cyc_gt_lt h3 h1), GT_cyc_gt_gt h2 h3]
    unfold cycBetween; tauto
  · have hp : u < v := by linarith
    have hq : ¬ v < s := by intro h; linarith
    rw [iff_false_intro (GT_cyc_lt_gt h1 h2), iff_true_intro (GT_cyc_gt_lt h2 h3), GT_cyc_lt_lt h3 h1]
    unfold cycBetween; tauto
  · have hq : v < s := by linarith
    have hr : ¬ s < u := by intro h; linarith
    rw [iff_false_intro (GT_cyc_lt_gt h2 h3), iff_true_intro (GT_cyc_gt_lt h3 h1), GT_cyc_lt_lt h1 h2]
    unfold cycBetween; tauto
  · rw [GT_cyc_lt_lt h1 h2, GT_cyc_lt_lt h2 h3, GT_cyc_lt_lt h3 h1]; rfl

/-- Four points: if `u` and `w` lie in the arc from `a` to `b` and `w` comes before `u` from `a`,
then `u` lies in the arc from `w` to `b`. -/
theorem GT_cyc_arc_step {a u w b : ℝ} (h1 : cycBetween a u b) (h2 : cycBetween a w b)
    (h3 : cycBetween a w u) : cycBetween w u b := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h3 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | (exfalso; linarith)
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

theorem GT_cyc_rotate {a b c : ℝ} : cycBetween a b c ↔ cycBetween b c a := by
  unfold cycBetween; tauto

/-- Totality of "first after `a`" on points distinct from `a` and from each other. -/
theorem GT_cyc_total {a u v : ℝ} (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v) :
    cycBetween a u v ∨ cycBetween a v u :=
  cycBetween_or_of_ne hau huv hav

/-- **Carriage of the cyclic order by a bijection that carries the base-point order on all pairs not
involving one element `p`, while `p` either keeps its position or moves from last to first (or from
first to last)**: the cyclic order of every triple is carried. -/
theorem GT_cyc_carried {ι : Type*} (k₁ k₂ : ι → ℝ) (a₁ a₂ : ℝ)
    (hk₁ : Function.Injective k₁) (hk₂ : Function.Injective k₂)
    (ha₁ : ∀ u, a₁ ≠ k₁ u) (ha₂ : ∀ u, a₂ ≠ k₂ u) (p : ι)
    (hrest : ∀ u v, u ≠ p → v ≠ p → (cycBetween a₁ (k₁ u) (k₁ v) ↔ cycBetween a₂ (k₂ u) (k₂ v)))
    (hp : (∀ u, u ≠ p → (cycBetween a₁ (k₁ u) (k₁ p) ↔ cycBetween a₂ (k₂ u) (k₂ p))) ∨
          (∀ u, u ≠ p → cycBetween a₁ (k₁ u) (k₁ p) ∧ cycBetween a₂ (k₂ p) (k₂ u)) ∨
          (∀ u, u ≠ p → cycBetween a₁ (k₁ p) (k₁ u) ∧ cycBetween a₂ (k₂ u) (k₂ p))) :
    ∀ u v s, cycBetween (k₁ u) (k₁ v) (k₁ s) ↔ cycBetween (k₂ u) (k₂ v) (k₂ s) := by
  -- the relations `r₁ u v = cycBetween a₁ (k₁ u) (k₁ v)`, `r₂` likewise, are asymmetric and total
  have asym₁ : ∀ u v, cycBetween a₁ (k₁ u) (k₁ v) → ¬ cycBetween a₁ (k₁ v) (k₁ u) := by
    intro u v h h'
    exact cycBetween_asymm' h (GT_cyc_rotate.mp h')
  have asym₂ : ∀ u v, cycBetween a₂ (k₂ u) (k₂ v) → ¬ cycBetween a₂ (k₂ v) (k₂ u) := by
    intro u v h h'
    exact cycBetween_asymm' h (GT_cyc_rotate.mp h')
  have irr₁ : ∀ u, ¬ cycBetween a₁ (k₁ u) (k₁ u) := fun u => not_cycBetween_self_mid _ _
  have irr₂ : ∀ u, ¬ cycBetween a₂ (k₂ u) (k₂ u) := fun u => not_cycBetween_self_mid _ _
  have tot₁ : ∀ u v, u ≠ v → cycBetween a₁ (k₁ u) (k₁ v) ∨ cycBetween a₁ (k₁ v) (k₁ u) :=
    fun u v huv => GT_cyc_total (ha₁ u) (ha₁ v) (hk₁.ne huv)
  have tot₂ : ∀ u v, u ≠ v → cycBetween a₂ (k₂ u) (k₂ v) ∨ cycBetween a₂ (k₂ v) (k₂ u) :=
    fun u v huv => GT_cyc_total (ha₂ u) (ha₂ v) (hk₂.ne huv)
  -- the core: triples with `p` in first position
  have core : ∀ v s, v ≠ p → s ≠ p → v ≠ s →
      (cycBetween (k₁ p) (k₁ v) (k₁ s) ↔ cycBetween (k₂ p) (k₂ v) (k₂ s)) := by
    intro v s hv hs hvs
    rw [GT_cyc_base (ha₁ p) (ha₁ v) (ha₁ s), GT_cyc_base (ha₂ p) (ha₂ v) (ha₂ s)]
    have hvs' := hrest v s hv hs
    rcases hp with h | h | h
    · -- `p` keeps its position: every atom is carried
      have hpv : cycBetween a₁ (k₁ p) (k₁ v) ↔ cycBetween a₂ (k₂ p) (k₂ v) := by
        rcases tot₁ v p hv with h1 | h1 <;> rcases tot₂ v p hv with h2 | h2
        · exact ⟨fun h' => absurd h1 (asym₁ _ _ h'), fun h' => absurd h2 (asym₂ _ _ h')⟩
        · exact absurd ((h v hv).mp h1) (asym₂ _ _ h2)
        · exact absurd ((h v hv).mpr h2) (asym₁ _ _ h1)
        · exact ⟨fun _ => h2, fun _ => h1⟩
      rw [hpv, hvs', h s hs]
    · -- `p` moves from last to first
      have h1 := h v hv
      have h2 := h s hs
      rw [iff_false_intro (asym₁ _ _ h1.1), iff_true_intro h2.1, iff_true_intro h1.2,
        iff_false_intro (asym₂ _ _ h2.2)]
      simp only [false_and, and_true, true_and, and_false, false_or, or_false]
      exact hvs'
    · -- `p` moves from first to last
      have h1 := h v hv
      have h2 := h s hs
      rw [iff_true_intro h1.1, iff_false_intro (asym₁ _ _ h2.1), iff_false_intro (asym₂ _ _ h1.2),
        iff_true_intro h2.2]
      simp only [false_and, and_true, true_and, and_false, false_or, or_false]
      exact hvs'
  have core' : ∀ u v s, u ≠ p → v ≠ p → s ≠ p →
      (cycBetween (k₁ u) (k₁ v) (k₁ s) ↔ cycBetween (k₂ u) (k₂ v) (k₂ s)) := by
    intro u v s hu hv hs
    rw [GT_cyc_base (ha₁ u) (ha₁ v) (ha₁ s), GT_cyc_base (ha₂ u) (ha₂ v) (ha₂ s),
      hrest u v hu hv, hrest v s hv hs, hrest s u hs hu]
  intro u v s
  by_cases hu : u = p
  · subst hu
    by_cases hv : v = u
    · subst hv
      exact iff_of_false (not_cycBetween_self_left _ _) (not_cycBetween_self_left _ _)
    by_cases hs : s = u
    · subst hs
      exact iff_of_false (not_cycBetween_self_right _ _) (not_cycBetween_self_right _ _)
    by_cases hvs : v = s
    · subst hvs
      exact iff_of_false (not_cycBetween_self_mid _ _) (not_cycBetween_self_mid _ _)
    exact core v s hv hs hvs
  by_cases hv : v = p
  · subst hv
    by_cases hs : s = v
    · subst hs
      exact iff_of_false (not_cycBetween_self_mid _ _) (not_cycBetween_self_mid _ _)
    by_cases hus : u = s
    · subst hus
      exact iff_of_false (not_cycBetween_self_right _ _) (not_cycBetween_self_right _ _)
    rw [GT_cyc_rotate, GT_cyc_rotate (a := k₂ u)]
    exact core s u hs hu (Ne.symm hus)
  by_cases hs : s = p
  · subst hs
    by_cases huv : u = v
    · subst huv
      exact iff_of_false (not_cycBetween_self_left _ _) (not_cycBetween_self_left _ _)
    rw [← GT_cyc_rotate, ← GT_cyc_rotate (a := k₂ s)]
    exact core u v hu hv huv
  exact core' u v s hu hv hs

end GT

section GT

open SM.Carrier SM.Link

variable {P : LabelledTuple n}

/-! ### One polygon: adjacent visits, arcs and the carriers of a selected crossing -/

omit [NeZero n] in
/-- The key of a visit as a mark is its visit key. -/
theorem GT_markKey_visit (hP : CrossingGeometry P) (v : Visit P) :
    geoMarkKey hP (Sum.inr v) = geometricVisitKey hP v := rfl

omit [NeZero n] in
theorem GT_traversalBetween_iff (hP : CrossingGeometry P) (v u w : Visit P) :
    traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP u)
        (geometricVisitPosition hP w) ↔
      cycBetween (geometricVisitKey hP v) (geometricVisitKey hP u) (geometricVisitKey hP w) :=
  Iff.rfl

omit [NeZero n] in
/-- Of the two arcs cut by two adjacent visits, the one containing a crossing visit is the nonempty
one; so the other arc carries no crossing visit. -/
theorem GT_adj_empty (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w)
    (z : Visit P) (hz : cycBetween (geometricVisitKey hP w) (geometricVisitKey hP z) (geometricVisitKey hP v)) :
    ∀ u : Visit P, ¬ cycBetween (geometricVisitKey hP v) (geometricVisitKey hP u) (geometricVisitKey hP w) := by
  rcases hadj.2 with h | h
  · exact h
  · exact absurd hz (h z)

omit [NeZero n] in
theorem GT_adj_empty' (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w)
    (z : Visit P) (hz : cycBetween (geometricVisitKey hP v) (geometricVisitKey hP z) (geometricVisitKey hP w)) :
    ∀ u : Visit P, ¬ cycBetween (geometricVisitKey hP w) (geometricVisitKey hP u) (geometricVisitKey hP v) := by
  rcases hadj.2 with h | h
  · exact absurd hz (h z)
  · exact h

/-- Adjacent visits are consecutive marks in one of the two orders. -/
theorem GT_succ_of_adjacent (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w)
    (hedge : v.2.val = w.2.val) :
    geoMarkSuccessor hP (Sum.inr v) = Sum.inr w ∨ geoMarkSuccessor hP (Sum.inr w) = Sum.inr v := by
  rcases hadj.2 with h | h
  · exact Or.inl (SEL_geoMarkSuccessor_eq_of_no_visit_between hP hadj.1 hedge h)
  · exact Or.inr (SEL_geoMarkSuccessor_eq_of_no_visit_between hP (Ne.symm hadj.1) hedge.symm h)

/-- Two adjacent unselected visits lie on the same carrier. -/
theorem GT_owner_eq_of_adjacent (hP : CrossingGeometry P) (S : Finset (Crossing P)) {v w : Visit P}
    (hadj : AdjacentVisits hP v w) (hedge : v.2.val = w.2.val) (hv : v.1 ∉ S) (hw : w.1 ∉ S) :
    geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr w) := by
  rcases GT_succ_of_adjacent hP hadj hedge with h | h
  · rw [← geoOwner_successor hP S (Sum.inr v), geoSmoothingSuccessor_visit_of_not_mem hP S v hv, h]
  · rw [← geoOwner_successor hP S (Sum.inr w), geoSmoothingSuccessor_visit_of_not_mem hP S w hw, h]

/-- Two visits on different edges have different keys, in the order of their edge indices. -/
theorem GT_key_lt_of_edge_val_lt (hP : CrossingGeometry P) {v w : Visit P}
    (h : v.2.val.val < w.2.val.val) : geometricVisitKey hP v < geometricVisitKey hP w := by
  unfold geometricVisitKey
  rw [traversalKey_lt_iff]
  exact Or.inl h

theorem GT_key_ne_of_ne (hP : CrossingGeometry P) {v w : Visit P} (h : v ≠ w) :
    geometricVisitKey hP v ≠ geometricVisitKey hP w :=
  fun h' => h (geometricVisitKey_injective hP h')

theorem GT_markKey_ne_of_ne (hP : CrossingGeometry P) {a b : Mark P} (h : a ≠ b) :
    geoMarkKey hP a ≠ geoMarkKey hP b :=
  fun h' => h (geoMarkKey_injective hP h')

/-- The key of a visit is positive (the vertex `0` alone has key `0`). -/
theorem GT_markKey_visit_pos (hP : CrossingGeometry P) (v : Visit P) :
    0 < geoMarkKey hP (Sum.inr v) := by
  rcases lt_or_eq_of_le (AV_key_nonneg hP (Sum.inr v)) with h | h
  · exact h
  · exfalso
    have : geoMarkKey hP (Sum.inl (0 : ZMod n)) = geoMarkKey hP (Sum.inr v) := by
      rw [AV_key_inl_zero, ← h]
    exact absurd (geoMarkKey_injective hP this) (by simp)

/-- **The arc step**: if a mark `m'` lies in the arc from `x₁` to `x₂` (or is `x₁`), its
traversal successor lies in that arc or is `x₂`. -/
theorem GT_arc_succ (hP : CrossingGeometry P) {x₁ x₂ : Visit P} (hx : x₁ ≠ x₂) (m' : Mark P)
    (hm : cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP m') (geoMarkKey hP (Sum.inr x₂)) ∨
      m' = Sum.inr x₁) :
    cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP (geoMarkSuccessor hP m'))
        (geoMarkKey hP (Sum.inr x₂)) ∨
      geoMarkSuccessor hP m' = Sum.inr x₂ := by
  have hx12 : geoMarkKey hP (Sum.inr x₁) ≠ geoMarkKey hP (Sum.inr x₂) :=
    GT_markKey_ne_of_ne hP (fun h => hx (Sum.inr.inj h))
  have hpos2 := GT_markKey_visit_pos hP x₂
  rcases AV_succ_spec hP m' with ⟨hlt, hbet⟩ | ⟨hwrap, hall⟩
  · -- no wrap: the successor is the next key, nothing strictly between
    by_cases heq : geoMarkKey hP (geoMarkSuccessor hP m') = geoMarkKey hP (Sum.inr x₂)
    · exact Or.inr (geoMarkKey_injective hP heq)
    left
    rcases lt_or_gt_of_ne heq with hlt2 | hgt2
    · -- successor below `x₂`
      rcases hm with hm | rfl
      · unfold cycBetween at hm ⊢
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by linarith, hlt2⟩
        · exact Or.inr (Or.inl ⟨hlt2, h2⟩)
        · exact absurd hlt2 (by linarith)
      · unfold cycBetween
        exact Or.inl ⟨hlt, hlt2⟩
    · -- successor above `x₂`: `x₂` is not strictly between, so `m'` is above `x₂` as well
      have hnb := hbet (Sum.inr x₂)
      have h2 : ¬ geoMarkKey hP m' < geoMarkKey hP (Sum.inr x₂) := fun h => hnb ⟨h, hgt2⟩
      rcases hm with hm | rfl
      · unfold cycBetween at hm ⊢
        rcases hm with ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩
        · exact absurd h3 h2
        · exact absurd h1 h2
        · exact Or.inr (Or.inr ⟨h1, by linarith⟩)
      · unfold cycBetween
        rcases lt_or_gt_of_ne hx12 with h | h
        · exact absurd h h2
        · exact Or.inr (Or.inr ⟨h, hlt⟩)
  · -- wrap: `m'` is the last mark, its successor the vertex `0`
    left
    rw [hwrap, AV_key_inl_zero]
    have hle2 := hall (Sum.inr x₂)
    have hle1 := hall (Sum.inr x₁)
    rcases hm with hm | rfl
    · unfold cycBetween at hm ⊢
      rcases hm with ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩
      · exact absurd h3 (not_lt.mpr hle2)
      · exact absurd h1 (not_lt.mpr hle2)
      · exact Or.inr (Or.inl ⟨hpos2, h1⟩)
    · unfold cycBetween
      rcases lt_or_gt_of_ne hx12 with h | h
      · exact absurd h (not_lt.mpr hle2)
      · exact Or.inr (Or.inl ⟨hpos2, h⟩)

/-- For an independent support and a selected visit `x₁` with twin `x₂`, the set
"the arc from `x₁` to `x₂`, together with `x₂`" is closed under the smoothing successor. -/
theorem GT_arc_closed (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x₁ : Visit P} (hx : x₁.1 ∈ S) (m : Mark P)
    (hm : cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP m)
        (geoMarkKey hP (Sum.inr (visitTwin x₁))) ∨ m = Sum.inr (visitTwin x₁)) :
    cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP (geoSmoothingSuccessor hP S m))
        (geoMarkKey hP (Sum.inr (visitTwin x₁))) ∨
      geoSmoothingSuccessor hP S m = Sum.inr (visitTwin x₁) := by
  have hne : x₁ ≠ visitTwin x₁ := (visitTwin_ne x₁).symm
  rw [geoSmoothingSuccessor_apply]
  apply GT_arc_succ hP hne
  rcases hm with hm | rfl
  · -- `m` is in the open arc: its selected image is in the arc as well
    cases m with
    | inl i => exact Or.inl (by simpa using hm)
    | inr v =>
      by_cases hv : v.1 ∈ S
      · rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv]
        -- `v` is a visit of another selected crossing, which does not interlace `x₁.1`
        have hvx : v.1 ≠ x₁.1 := by
          intro h
          rcases visit_eq_or_twin x₁ v h with rfl | rfl
          · exact not_cycBetween_self_left _ _ hm
          · exact not_cycBetween_self_mid _ _ hm
        have hnI : ¬ GeometricInterlaces hP x₁.1 v.1 := hS _ hx _ hv (Ne.symm hvx)
        have hx2 : x₁.2 ≠ (visitTwin x₁).2 := by
          intro h
          exact visitTwin_ne x₁ (Sigma.ext (visitTwin_crossing x₁) (heq_of_eq h.symm))
        have hv2 : v.2 ≠ (visitTwin v).2 := by
          intro h
          exact visitTwin_ne v (Sigma.ext (visitTwin_crossing v) (heq_of_eq h.symm))
        rw [L.interlaces_iff_xor hP (Ne.symm hvx) (x₀ := x₁.2) (x₁ := (visitTwin x₁).2) hx2
          (y₀ := v.2) (y₁ := (visitTwin v).2) hv2] at hnI
        left
        show cycBetween (geometricVisitKey hP x₁) (geometricVisitKey hP (visitTwin v))
          (geometricVisitKey hP (visitTwin x₁))
        have hm' : L.Cyc (geometricVisitKey hP ⟨x₁.1, x₁.2⟩) (geometricVisitKey hP ⟨v.1, v.2⟩)
            (geometricVisitKey hP ⟨x₁.1, (visitTwin x₁).2⟩) := hm
        by_contra hcon
        exact hnI (Or.inl ⟨hm', hcon⟩)
      · rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv]
        exact Or.inl hm
  · -- `m = x₂`: its selected image is `x₁`
    right
    rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S _ (by rw [visitTwin_crossing]; exact hx),
      visitTwin_involutive]

/-- **The carrier of `x₂` lies in the arc from `x₁` to `x₂`** (plus `x₂` itself): every mark on the
carrier of the selected visit `x₂ = visitTwin x₁` is `x₂` or lies strictly between `x₁` and `x₂`
going forward from `x₁`. -/
theorem GT_owner_arc (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x₁ : Visit P} (hx : x₁.1 ∈ S) (m : Mark P)
    (hm : geoOwner hP S m = geoOwner hP S (Sum.inr (visitTwin x₁))) :
    m = Sum.inr (visitTwin x₁) ∨
      cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP m) (geoMarkKey hP (Sum.inr (visitTwin x₁))) := by
  have hsc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr (visitTwin x₁)) m :=
    (geoOwner_eq_iff hP S _ _).mp hm.symm
  obtain ⟨k, -, hk⟩ := hsc.exists_pow_eq'
  rw [← hk]
  clear hk hm
  induction k with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply]
    exact Or.inl rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases GT_arc_closed hP hS hx ((geoSmoothingSuccessor hP S ^ k) (Sum.inr (visitTwin x₁)))
      (ih.symm) with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- The two visits of a selected crossing lie on different carriers. -/
theorem GT_owner_twin_ne (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x₁ : Visit P} (hx : x₁.1 ∈ S) :
    geoOwner hP S (Sum.inr x₁) ≠ geoOwner hP S (Sum.inr (visitTwin x₁)) := by
  intro h
  rcases GT_owner_arc hP hS hx (Sum.inr x₁) h with h' | h'
  · exact (visitTwin_ne x₁) (Sum.inr.inj h').symm
  · exact not_cycBetween_self_left _ _ h'

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

omit [NeZero n] in
/-- The support of an endpoint row: `Q ∪ {x}` (reducible, so that it is `Q ∪ {x}` to every consumer). -/
abbrev GT_S (Q : Finset (Crossing P)) (x : Crossing P) : Finset (Crossing P) := Q ∪ {x}

omit [NeZero n] in
theorem GT_mem_S_iff (Q : Finset (Crossing P)) (x y : Crossing P) :
    y ∈ GT_S Q x ↔ y ∈ Q ∨ y = x := by
  simp only [GT_S, Finset.mem_union, Finset.mem_singleton]

omit [NeZero n] in
/-- The crossing relabelling of an endpoint row: the edge-pair transport followed by the exchange of
`w'` and `m'` ("the map fixing every outside label and sending `c` to `b`",
R_GENERIC_COMMON_TRANSPORT_PROOF.md §2). -/
noncomputable def GT_φ (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (w m : Crossing P) :
    Crossing P ≃ Crossing P' :=
  (crossingTransport hs).trans (Equiv.swap (crossingTransport hs w) (crossingTransport hs m))

/-! ### The endpoint-row configuration (R_GENERIC_COMMON_TRANSPORT_PROOF.md §2–§3, all six branches)

Row `x` of the full-availability fibre, `x` a member of the selected pair `{x, w}`, `m` the centre of the
path side: side `P` is the two-edge side (edges `x–m`, `w–m`; `x`, `w` independent), side `P'` the
one-edge side. Edge labels: `ℓ₁` shared by `x, m`, `ℓ₂` shared by `x, w`, `ℓ₃` shared by `w, m`. The
structure collects exactly the facts the printed proof cites: the local graph, R-LOC-2 (2)–(4), the
adjacency of the three bundle pairs on both sides, lem:guardconst (turns, signs, a ray), the sharpened
masks ("`w, m` are twins relative to every outside survivor") and the sign identity (4)/(6). -/
structure GT_Endpoint (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n) (Q : Finset (Crossing P))
    (x w m : Crossing P) (ℓ₁ ℓ₂ ℓ₃ : ZMod n) : Prop where
  hef : e ≠ f
  heg : e ≠ g
  hfg : f ≠ g
  xT : x.val ∈ triangleSupports e f g
  wT : w.val ∈ triangleSupports e f g
  mT : m.val ∈ triangleSupports e f g
  tri_cases : ∀ y : Crossing P, y.val ∈ triangleSupports e f g → y = x ∨ y = w ∨ y = m
  xw : x ≠ w
  xm : x ≠ m
  wm : w ≠ m
  x1 : ℓ₁ ∈ x.val
  m1 : ℓ₁ ∈ m.val
  x2 : ℓ₂ ∈ x.val
  w2 : ℓ₂ ∈ w.val
  w3 : ℓ₃ ∈ w.val
  m3 : ℓ₃ ∈ m.val
  l12 : ℓ₁ ≠ ℓ₂
  l13 : ℓ₁ ≠ ℓ₃
  l23 : ℓ₂ ≠ ℓ₃
  Q_ind : Q ∈ CV.Ind hP
  Q_out : ∀ q ∈ Q, q.val ∉ triangleSupports e f g
  Q_avail : ∀ q ∈ Q, ∀ y : Crossing P, y.val ∈ triangleSupports e f g → ¬ GeometricInterlaces hP q y
  hxw : ¬ GeometricInterlaces hP x w
  hxm : GeometricInterlaces hP x m
  hwm : GeometricInterlaces hP w m
  gauss : ExactTriangleVisitOrders P P' e f g hs
  toggle : ∀ y z : Crossing P, ¬ (y.val ∈ triangleSupports e f g ∧ z.val ∈ triangleSupports e f g) →
    (GeometricInterlaces hP' (crossingTransport hs y) (crossingTransport hs z) ↔
      GeometricInterlaces hP y z)
  compl : ∀ y z : Crossing P, y.val ∈ triangleSupports e f g → z.val ∈ triangleSupports e f g →
    y ≠ z →
    (GeometricInterlaces hP' (crossingTransport hs y) (crossingTransport hs z) ↔
      ¬ GeometricInterlaces hP y z)
  adj1 : AdjacentVisits hP (visitOn x ℓ₁ x1) (visitOn m ℓ₁ m1)
  adj2 : AdjacentVisits hP (visitOn x ℓ₂ x2) (visitOn w ℓ₂ w2)
  adj3 : AdjacentVisits hP (visitOn w ℓ₃ w3) (visitOn m ℓ₃ m3)
  adj1' : AdjacentVisits hP' (visitTransport hs (visitOn x ℓ₁ x1)) (visitTransport hs (visitOn m ℓ₁ m1))
  adj2' : AdjacentVisits hP' (visitTransport hs (visitOn x ℓ₂ x2)) (visitTransport hs (visitOn w ℓ₂ w2))
  adj3' : AdjacentVisits hP' (visitTransport hs (visitOn w ℓ₃ w3)) (visitTransport hs (visitOn m ℓ₃ m3))
  turn_eq : ∀ i, turn P' i = turn P i
  sign_eq : ∀ i j, IsCrossing P {i, j} → crossingSign P' i j = crossingSign P i j
  ray : ∃ r : Plane, ∀ h : ZMod n, det r (edge P h) ≠ 0 ∧
    SignType.sign (det r (edge P' h)) = SignType.sign (det r (edge P h))
  twins : ∀ y ∈ CV.U hP (GT_S Q x), y.val ∉ triangleSupports e f g →
    (GeometricInterlaces hP y w ↔ GeometricInterlaces hP y m)
  sgn : crossingSign P ℓ₂ ℓ₃ = crossingSign P ℓ₁ ℓ₃

/-- For a crossing of `U(S)`, all visits are on the carrier iff one of them is. -/
theorem GT_forall_visit_owner_iff {hP : CrossingGeometry P} {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hP) {c : Crossing P} (hc : c ∈ CV.U hP S) (v₀ : Visit P) (hv₀ : v₀.1 = c)
    (q : GeoComponent hP S) :
    (∀ v : Visit P, v.1 = c → geoOwner hP S (Sum.inr v) = q) ↔ geoOwner hP S (Sum.inr v₀) = q := by
  constructor
  · intro h; exact h v₀ hv₀
  · intro h v hv
    rw [CV.owner_eq_of_mem_U hP hS hc v v₀ hv hv₀]
    exact h

theorem GT_retained_of_not_mem_U {hP : CrossingGeometry P} {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) {c : Crossing P} (hc : c ∉ CV.U hP S) (q : GeoComponent hP S) :
    c ∉ geoCarrierCrossings hP S q := by
  intro h
  apply hc
  have := geoCarrierCrossings_subset_U hP hS q h
  rw [mem_geoSupportUnselected_iff] at this
  exact (CV.mem_U_iff hP S c).mpr this

namespace GT_Endpoint

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

local notation "𝑇" => triangleCrossings P e f g
local notation "𝑆" => GT_S Q x
local notation "𝑆'" => transportSupport hs (GT_S Q x)

variable (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
include D

/-! #### Names: the six visits -/

/-- `x₁`, the visit of `x` on the edge `ℓ₁` shared with `m`. -/
def x₁ : Visit P := visitOn x ℓ₁ D.x1
/-- `x₂`, the visit of `x` on the edge `ℓ₂` shared with `w`. -/
def x₂ : Visit P := visitOn x ℓ₂ D.x2
/-- `w₂`, the visit of `w` on `ℓ₂`. -/
def w₂ : Visit P := visitOn w ℓ₂ D.w2
/-- `w₃`, the visit of `w` on `ℓ₃`. -/
def w₃ : Visit P := visitOn w ℓ₃ D.w3
/-- `m₁`, the visit of `m` on `ℓ₁`. -/
def m₁ : Visit P := visitOn m ℓ₁ D.m1
/-- `m₃`, the visit of `m` on `ℓ₃`. -/
def m₃ : Visit P := visitOn m ℓ₃ D.m3

theorem x₁_fst : D.x₁.1 = x := rfl
theorem x₂_fst : D.x₂.1 = x := rfl
theorem w₂_fst : D.w₂.1 = w := rfl
theorem w₃_fst : D.w₃.1 = w := rfl
theorem m₁_fst : D.m₁.1 = m := rfl
theorem m₃_fst : D.m₃.1 = m := rfl
theorem x₁_edge : D.x₁.2.val = ℓ₁ := rfl
theorem x₂_edge : D.x₂.2.val = ℓ₂ := rfl
theorem w₂_edge : D.w₂.2.val = ℓ₂ := rfl
theorem w₃_edge : D.w₃.2.val = ℓ₃ := rfl
theorem m₁_edge : D.m₁.2.val = ℓ₁ := rfl
theorem m₃_edge : D.m₃.2.val = ℓ₃ := rfl

theorem twin_x₁ : visitTwin D.x₁ = D.x₂ := SEL_visitTwin_visitOn D.x2 D.x1 D.l12.symm
theorem twin_x₂ : visitTwin D.x₂ = D.x₁ := SEL_visitTwin_visitOn D.x1 D.x2 D.l12
theorem twin_w₂ : visitTwin D.w₂ = D.w₃ := SEL_visitTwin_visitOn D.w3 D.w2 D.l23.symm
theorem twin_w₃ : visitTwin D.w₃ = D.w₂ := SEL_visitTwin_visitOn D.w2 D.w3 D.l23
theorem twin_m₁ : visitTwin D.m₁ = D.m₃ := SEL_visitTwin_visitOn D.m3 D.m1 D.l13.symm
theorem twin_m₃ : visitTwin D.m₃ = D.m₁ := SEL_visitTwin_visitOn D.m1 D.m3 D.l13

/-- The support of `x`: exactly `{ℓ₁, ℓ₂}`. -/
theorem xval : x.val = {ℓ₁, ℓ₂} := by
  have h2 := crossing_card_two x
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact D.x1
    · exact D.x2
  · rw [h2, Finset.card_pair D.l12]

theorem wval : w.val = {ℓ₂, ℓ₃} := by
  have h2 := crossing_card_two w
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact D.w2
    · exact D.w3
  · rw [h2, Finset.card_pair D.l23]

theorem mval : m.val = {ℓ₁, ℓ₃} := by
  have h2 := crossing_card_two m
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact D.m1
    · exact D.m3
  · rw [h2, Finset.card_pair D.l13]

theorem l3_not_mem_x : ℓ₃ ∉ x.val := by
  rw [D.xval]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.l13.symm, D.l23.symm⟩

theorem l1_not_mem_w : ℓ₁ ∉ w.val := by
  rw [D.wval]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.l12, D.l13⟩

theorem l2_not_mem_m : ℓ₂ ∉ m.val := by
  rw [D.mval]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.l12.symm, D.l23⟩

/-! #### The triangle and the support -/

theorem x_mem_T : x ∈ 𝑇 := (F1.mem_triangleCrossings e f g x).mpr D.xT
theorem w_mem_T : w ∈ 𝑇 := (F1.mem_triangleCrossings e f g w).mpr D.wT
theorem m_mem_T : m ∈ 𝑇 := (F1.mem_triangleCrossings e f g m).mpr D.mT

omit [NeZero n] D in
theorem x_mem_S : x ∈ 𝑆 := (GT_mem_S_iff Q x x).mpr (Or.inr rfl)

theorem not_mem_Q_of_mem_T {y : Crossing P} (hy : y.val ∈ triangleSupports e f g) : y ∉ Q :=
  fun h => D.Q_out y h hy

theorem w_not_mem_S : w ∉ 𝑆 := by
  rw [GT_mem_S_iff]
  rintro (h | h)
  · exact D.not_mem_Q_of_mem_T D.wT h
  · exact D.xw h.symm

theorem m_not_mem_S : m ∉ 𝑆 := by
  rw [GT_mem_S_iff]
  rintro (h | h)
  · exact D.not_mem_Q_of_mem_T D.mT h
  · exact D.xm h.symm

/-- The only triangle crossing in `S` is `x`. -/
theorem eq_x_of_mem_S_T {y : Crossing P} (hyS : y ∈ 𝑆) (hyT : y.val ∈ triangleSupports e f g) :
    y = x := by
  rcases (GT_mem_S_iff Q x y).mp hyS with h | h
  · exact absurd h (D.not_mem_Q_of_mem_T hyT)
  · exact h

theorem S_ind : 𝑆 ∈ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  intro a ha b hb hab
  rcases (GT_mem_S_iff Q x a).mp ha with ha | hax <;>
    rcases (GT_mem_S_iff Q x b).mp hb with hb | hbx
  · exact ((CV.mem_Ind_iff hP Q).mp D.Q_ind) a ha b hb hab
  · subst b; exact D.Q_avail a ha _ D.xT
  · subst a; exact fun h => D.Q_avail b hb _ D.xT (geometricInterlaces_symm hP h)
  · subst a; exact absurd hbx.symm hab

theorem S_geoIndep : GeoIndependent hP 𝑆 := CV.geoIndependent_of_mem_Ind hP D.S_ind

/-! #### `U(S)` on both sides -/

theorem w_mem_U : w ∈ CV.U hP 𝑆 := by
  rw [CV.mem_U_iff]
  refine ⟨D.w_not_mem_S, fun s hs => ?_⟩
  rcases (GT_mem_S_iff Q x s).mp hs with h | hsx
  · exact fun h' => D.Q_avail s h w D.wT (geometricInterlaces_symm hP h')
  · subst s; exact fun h' => D.hxw (geometricInterlaces_symm hP h')

theorem m_not_mem_U : m ∉ CV.U hP 𝑆 := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  exact h x x_mem_S (geometricInterlaces_symm hP D.hxm)

omit D in
theorem x_not_mem_U : x ∉ CV.U hP 𝑆 := fun h => ((CV.mem_U_iff hP _ x).mp h).1 x_mem_S

/-- A crossing of `U(S)` is `w` or an outside crossing. -/
theorem mem_U_cases {y : Crossing P} (hy : y ∈ CV.U hP 𝑆) :
    y = w ∨ y.val ∉ triangleSupports e f g := by
  by_cases hyT : y.val ∈ triangleSupports e f g
  · rcases D.tri_cases y hyT with rfl | rfl | rfl
    · exact absurd hy x_not_mem_U
    · exact Or.inl rfl
    · exact absurd hy D.m_not_mem_U
  · exact Or.inr hyT

omit [NeZero n] D in
theorem mem_S'_iff (y : Crossing P) : crossingTransport hs y ∈ 𝑆' ↔ y ∈ 𝑆 :=
  mem_transportSupport_iff hs _ y

theorem S'_ind : GeoIndependent hP' 𝑆' := by
  intro a' ha' b' hb' hab
  obtain ⟨a, rfl⟩ := (crossingTransport hs).surjective a'
  obtain ⟨b, rfl⟩ := (crossingTransport hs).surjective b'
  rw [mem_S'_iff] at ha' hb'
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  have hnT : ¬ (a.val ∈ triangleSupports e f g ∧ b.val ∈ triangleSupports e f g) := by
    rintro ⟨haT, hbT⟩
    exact hab' ((D.eq_x_of_mem_S_T ha' haT).trans (D.eq_x_of_mem_S_T hb' hbT).symm)
  rw [D.toggle a b hnT]
  exact D.S_geoIndep a ha' b hb' hab'

theorem S'_mem_Ind : 𝑆' ∈ CV.Ind hP' := (CV.mem_Ind_iff_geoIndependent _ _).mpr D.S'_ind

theorem m'_mem_U : crossingTransport hs m ∈ CV.U hP' 𝑆' := by
  rw [CV.mem_U_iff]
  refine ⟨fun h => D.m_not_mem_S ((mem_S'_iff m).mp h), fun s' hs' => ?_⟩
  obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
  rw [mem_S'_iff] at hs'
  rcases (GT_mem_S_iff Q x s).mp hs' with h | hsx
  · rw [D.toggle m s (fun h' => D.Q_out s h h'.2)]
    exact fun h' => D.Q_avail s h m D.mT (geometricInterlaces_symm hP h')
  · subst s
    rw [D.compl m x D.mT D.xT D.xm.symm]
    exact fun h' => h' (geometricInterlaces_symm hP D.hxm)

theorem w'_not_mem_U : crossingTransport hs w ∉ CV.U hP' 𝑆' := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  apply h (crossingTransport hs x) ((mem_S'_iff x).mpr x_mem_S)
  rw [D.compl w x D.wT D.xT D.xw.symm]
  exact fun h' => D.hxw (geometricInterlaces_symm hP h')

omit D in
theorem x'_not_mem_U : crossingTransport hs x ∉ CV.U hP' 𝑆' :=
  fun h => ((CV.mem_U_iff hP' _ _).mp h).1 ((mem_S'_iff x).mpr x_mem_S)

/-- Outside crossings: membership in `U` is carried. -/
theorem mem_U_iff_of_outside {y : Crossing P} (hy : y.val ∉ triangleSupports e f g) :
    crossingTransport hs y ∈ CV.U hP' 𝑆' ↔ y ∈ CV.U hP 𝑆 := by
  rw [CV.mem_U_iff, CV.mem_U_iff, mem_S'_iff]
  apply and_congr Iff.rfl
  constructor
  · intro h s hsS
    rw [← D.toggle y s (fun h' => hy h'.1)]
    exact h _ ((mem_S'_iff s).mpr hsS)
  · intro h s' hs'
    obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
    rw [D.toggle y s (fun h' => hy h'.1)]
    exact h s ((mem_S'_iff s).mp hs')

/-! #### The wall data and the good marks -/

theorem wall : GT_Wall hP hP' hs 𝑇 𝑆 where
  indep := D.S_geoIndep
  indep' := D.S'_ind
  key_lt v w hvw := AV_key_lt_of_gauss hP hP' hs D.hef D.heg D.hfg D.gauss v w hvw
  corners_apart v w hrev := by
    rintro ⟨hvS, hwS⟩
    have h1 := D.eq_x_of_mem_S_T hvS ((F1.mem_triangleCrossings e f g v.1).mp hrev.1)
    have h2 := D.eq_x_of_mem_S_T hwS ((F1.mem_triangleCrossings e f g w.1).mp hrev.2.1)
    exact hrev.2.2.1 (h1.trans h2.symm)
  turn_eq := D.turn_eq
  sign_eq := D.sign_eq
  ray := D.ray

/-- Every visit not on the edges `ℓ₁`, `ℓ₂` shared with `x` is good; in particular the visits of
outside crossings and the `ℓ₃`-visits `w₃`, `m₃`. -/
theorem good_of_edge {v : Visit P} (hv : v.2.val ∉ x.val) : GT_Good 𝑇 𝑆 (Sum.inr v) := by
  intro v' hv' u hrev hu
  obtain rfl := Sum.inr.inj hv'
  have huS : u.1 ∈ 𝑆 := hu
  have hux : u.1 = x := D.eq_x_of_mem_S_T huS ((F1.mem_triangleCrossings e f g u.1).mp hrev.2.1)
  apply hv
  rw [hrev.2.2.2, ← hux]
  exact u.2.property

omit D in
theorem good_of_outside {v : Visit P} (hv : v.1.val ∉ triangleSupports e f g) :
    GT_Good 𝑇 𝑆 (Sum.inr v) :=
  GT_good_of_not_mem _ _ (fun h => hv ((F1.mem_triangleCrossings e f g v.1).mp h))

theorem good_w₃ : GT_Good 𝑇 𝑆 (Sum.inr D.w₃) := D.good_of_edge (v := D.w₃) D.l3_not_mem_x
theorem good_m₃ : GT_Good 𝑇 𝑆 (Sum.inr D.m₃) := D.good_of_edge (v := D.m₃) D.l3_not_mem_x

theorem x₁_corner : IsTrueCorner 𝑆 (Sum.inr D.x₁) := x_mem_S
theorem x₂_corner : IsTrueCorner 𝑆 (Sum.inr D.x₂) := x_mem_S

/-! #### The carriers of the local visits -/

/-- Both visits of `w` lie on one carrier of `S` (`w ∈ U(S)`). -/
theorem owner_w₂_eq_w₃ : geoOwner hP 𝑆 (Sum.inr D.w₂) = geoOwner hP 𝑆 (Sum.inr D.w₃) :=
  CV.owner_eq_of_mem_U hP D.S_ind D.w_mem_U D.w₂ D.w₃ rfl rfl

/-- Both visits of `m'` lie on one carrier of `S'` (`m' ∈ U(S')`). -/
theorem owner'_m₁_eq_m₃ :
    geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₁)) =
      geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₃)) :=
  CV.owner_eq_of_mem_U hP' D.S'_mem_Ind D.m'_mem_U _ _ rfl rfl

/-- On the one-edge side the `ℓ₃`-visits of `w'` and `m'` are adjacent unselected visits, hence on one
carrier. -/
theorem owner'_w₃_eq_m₃ :
    geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.w₃)) =
      geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₃)) :=
  GT_owner_eq_of_adjacent hP' _ D.adj3' rfl
    (fun h => D.w_not_mem_S ((mem_S'_iff w).mp h))
    (fun h => D.m_not_mem_S ((mem_S'_iff m).mp h))

theorem owner_w₃_eq_m₃ :
    geoOwner hP 𝑆 (Sum.inr D.w₃) = geoOwner hP 𝑆 (Sum.inr D.m₃) :=
  GT_owner_eq_of_adjacent hP _ D.adj3 rfl D.w_not_mem_S D.m_not_mem_S

/-- The carrier bijection of the endpoint row. -/
noncomputable abbrev β : GeoComponent hP 𝑆 ≃ GeoComponent hP' 𝑆' := GT_carrierEquiv D.wall

/-- **The visit of `m'` on `ℓ₃` lies on the copy of the carrier of `w₃`**: `m₃'` and `w₃'` are
adjacent unselected visits on the one-edge side, and `w₃` is a good mark. -/
theorem owner'_m₃ :
    geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₃)) = D.β (geoOwner hP 𝑆 (Sum.inr D.w₃)) := by
  rw [← D.owner'_w₃_eq_m₃, ← markTransport_visit]
  exact GT_owner_transport D.wall D.good_w₃

theorem owner'_m₁ :
    geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₁)) = D.β (geoOwner hP 𝑆 (Sum.inr D.w₃)) := by
  rw [D.owner'_m₁_eq_m₃, D.owner'_m₃]

/-! #### The relabelling `φ = swap(w', m') ∘ τ` -/

omit [NeZero n] D in
theorem φ_apply (y : Crossing P) :
    GT_φ hs w m y = Equiv.swap (crossingTransport hs w) (crossingTransport hs m) (crossingTransport hs y) := rfl

omit [NeZero n] D in
theorem φ_w : GT_φ hs w m w = crossingTransport hs m := by
  rw [φ_apply]; exact Equiv.swap_apply_left _ _

omit [NeZero n] D in
theorem φ_m : GT_φ hs w m m = crossingTransport hs w := by
  rw [φ_apply]; exact Equiv.swap_apply_right _ _

omit [NeZero n] D in
theorem φ_of_ne {y : Crossing P} (hyw : y ≠ w) (hym : y ≠ m) : GT_φ hs w m y = crossingTransport hs y := by
  rw [φ_apply]
  exact Equiv.swap_apply_of_ne_of_ne ((crossingTransport hs).injective.ne hyw)
    ((crossingTransport hs).injective.ne hym)

theorem φ_of_mem_S {y : Crossing P} (hy : y ∈ 𝑆) : GT_φ hs w m y = crossingTransport hs y :=
  φ_of_ne (fun h => D.w_not_mem_S (h ▸ hy)) (fun h => D.m_not_mem_S (h ▸ hy))

theorem φ_of_outside {y : Crossing P} (hy : y.val ∉ triangleSupports e f g) :
    GT_φ hs w m y = crossingTransport hs y :=
  φ_of_ne (fun h => hy (h ▸ D.wT)) (fun h => hy (h ▸ D.mT))

/-- A crossing not among `x, w, m` is outside. -/
theorem outside_of_ne {y : Crossing P} (hyx : y ≠ x) (hyw : y ≠ w) (hym : y ≠ m) :
    y.val ∉ triangleSupports e f g := by
  intro h
  rcases D.tri_cases y h with h | h | h
  · exact hyx h
  · exact hyw h
  · exact hym h

/-- **The retained crossings of a carrier are carried to those of its copy along `φ`**: outside
crossings by the ownership transport of their (good) visits, `w ↦ m'` through the `ℓ₃`-pair. -/
theorem retained (q : GeoComponent hP 𝑆) :
    geoCarrierCrossings hP' 𝑆' (D.β q) = (geoCarrierCrossings hP 𝑆 q).map (GT_φ hs w m).toEmbedding := by
  classical
  ext y'
  obtain ⟨y, rfl⟩ := (GT_φ hs w m).surjective y'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hyw : y = w
  · subst hyw
    rw [φ_w, mem_geoCarrierCrossings, mem_geoCarrierCrossings,
      GT_forall_visit_owner_iff D.S'_mem_Ind D.m'_mem_U (visitTransport hs D.m₃) rfl,
      GT_forall_visit_owner_iff D.S_ind D.w_mem_U D.w₃ rfl, D.owner'_m₃]
    refine and_congr ?_ (GT_carrierEquiv D.wall).injective.eq_iff
    exact iff_of_true (fun h => D.m_not_mem_S ((mem_S'_iff m).mp h)) D.w_not_mem_S
  by_cases hym : y = m
  · subst hym
    rw [φ_m]
    exact iff_of_false (GT_retained_of_not_mem_U D.S'_ind D.w'_not_mem_U _)
      (GT_retained_of_not_mem_U D.S_geoIndep D.m_not_mem_U _)
  by_cases hyx : y = x
  · subst hyx
    rw [φ_of_ne hyw hym]
    exact iff_of_false (GT_retained_of_not_mem_U D.S'_ind x'_not_mem_U _)
      (GT_retained_of_not_mem_U D.S_geoIndep x_not_mem_U _)
  have hyT : y.val ∉ triangleSupports e f g := D.outside_of_ne hyx hyw hym
  rw [φ_of_ne hyw hym, mem_geoCarrierCrossings, mem_geoCarrierCrossings, mem_S'_iff]
  apply and_congr Iff.rfl
  constructor
  · intro hall v hv
    have := hall (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, GT_owner_transport D.wall (good_of_outside (hv ▸ hyT))] at this
    exact (GT_carrierEquiv D.wall).injective this
  · intro hall v' hv'
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective v'
    rw [visitTransport_crossing] at hv'
    have hv : v.1 = y := (crossingTransport hs).injective hv'
    rw [← markTransport_visit, GT_owner_transport D.wall (good_of_outside (hv ▸ hyT)), hall v hv]

/-- `U(S)` is carried along `φ`. -/
theorem mem_U_iff (y : Crossing P) : GT_φ hs w m y ∈ CV.U hP' 𝑆' ↔ y ∈ CV.U hP 𝑆 := by
  by_cases hyw : y = w
  · subst hyw; rw [φ_w]; exact iff_of_true D.m'_mem_U D.w_mem_U
  by_cases hym : y = m
  · subst hym; rw [φ_m]; exact iff_of_false D.w'_not_mem_U D.m_not_mem_U
  by_cases hyx : y = x
  · subst hyx; rw [φ_of_ne hyw hym]; exact iff_of_false x'_not_mem_U x_not_mem_U
  rw [φ_of_ne hyw hym]
  exact D.mem_U_iff_of_outside (D.outside_of_ne hyx hyw hym)

/-- Residual interlacement is carried along `φ` ("`b` and `c` are twins relative to every outside
vertex that survives `Q ∪ {a}`"). -/
theorem adj (y : Crossing P) (hy : y ∈ CV.U hP 𝑆) (z : Crossing P) (hz : z ∈ CV.U hP 𝑆) :
    GeometricInterlaces hP' (GT_φ hs w m y) (GT_φ hs w m z) ↔ GeometricInterlaces hP y z := by
  rcases D.mem_U_cases hy with rfl | hyT <;> rcases D.mem_U_cases hz with rfl | hzT
  · rw [φ_w]
    exact iff_of_false (geometricInterlaces_irrefl hP' _) (geometricInterlaces_irrefl hP _)
  · rw [φ_w, D.φ_of_outside hzT, CV.geometricInterlaces_comm hP' _ _, CV.geometricInterlaces_comm hP _ _,
      D.toggle z m (fun h => hzT h.1)]
    exact (D.twins z hz hzT).symm
  · rw [φ_w, D.φ_of_outside hyT, D.toggle y m (fun h => hyT h.1)]
    exact (D.twins y hy hyT).symm
  · rw [D.φ_of_outside hyT, D.φ_of_outside hzT]
    exact D.toggle y z (fun h => hyT h.1)

/-- The relabelling data of the endpoint row. -/
theorem relabel : GT_Relabel D.wall (GT_φ hs w m) where
  phi_S _ hc := D.φ_of_mem_S hc
  retained := D.retained
  mem_U := D.mem_U_iff
  adj := D.adj

end GT_Endpoint

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

/-! ### Keys of visits: different edges compare by edge index; betweenness on one edge -/

theorem GT_key_lt_iff_of_edge_ne (hP : CrossingGeometry P) {v w : Visit P} (h : v.2.val ≠ w.2.val) :
    geometricVisitKey hP v < geometricVisitKey hP w ↔ v.2.val.val < w.2.val.val := by
  unfold geometricVisitKey
  rw [traversalKey_lt_iff]
  constructor
  · rintro (h1 | ⟨h1, -⟩)
    · exact h1
    · exact absurd h1 h
  · exact fun h1 => Or.inl h1

/-- A visit whose key lies strictly between the keys of two visits of one edge is on that edge. -/
theorem GT_edge_of_between (hP : CrossingGeometry P) {v u w : Visit P} (hvw : v.2.val = w.2.val)
    (h1 : geometricVisitKey hP v < geometricVisitKey hP u) (h2 : geometricVisitKey hP u < geometricVisitKey hP w) :
    u.2.val = v.2.val := by
  by_contra hne
  have h1' := (GT_key_lt_iff_of_edge_ne hP (Ne.symm hne)).mp h1
  have h2' := (GT_key_lt_iff_of_edge_ne hP (fun h => hne (h.trans hvw.symm))).mp h2
  rw [← hvw] at h2'
  omega

/-- **Adjacent same-edge visits are indistinguishable from any other visit's position**: if `v, w` are
adjacent visits on one edge and some crossing visit `z` lies on another edge, then no visit `y ≠ v, w`
lies strictly between them, so `key y < key v ↔ key y < key w`. -/
theorem GT_adj_lt_iff (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w)
    (hedge : v.2.val = w.2.val) (z : Visit P) (hz : z.2.val ≠ v.2.val) (y : Visit P) (hyv : y ≠ v)
    (hyw : y ≠ w) :
    (geometricVisitKey hP y < geometricVisitKey hP v ↔ geometricVisitKey hP y < geometricVisitKey hP w) ∧
    (geometricVisitKey hP v < geometricVisitKey hP y ↔ geometricVisitKey hP w < geometricVisitKey hP y) := by
  have hkyv := GT_key_ne_of_ne hP hyv
  have hkyw := GT_key_ne_of_ne hP hyw
  have hkvw := GT_key_ne_of_ne hP hadj.1
  -- the arc between `v` and `w` (in the linear order) contains no visit: the other arc contains `z`
  have hzout : ∀ a b : Visit P, a.2.val = b.2.val → geometricVisitKey hP a < geometricVisitKey hP b →
      z.2.val ≠ a.2.val → cycBetween (geometricVisitKey hP b) (geometricVisitKey hP z) (geometricVisitKey hP a) := by
    intro a b hab hlt hza
    have hza' : z ≠ a := fun h => hza (congrArg (fun v : Visit P => v.2.val) h)
    have hzb' : z ≠ b := fun h => hza ((congrArg (fun v : Visit P => v.2.val) h).trans hab.symm)
    rcases lt_or_gt_of_ne (GT_key_ne_of_ne hP hza') with h | h
    · -- `z` below `a`
      exact Or.inr (Or.inl ⟨h, hlt⟩)
    · -- `z` above `a`: not between `a` and `b` (else on their edge), so above `b`
      have hzb : geometricVisitKey hP b < geometricVisitKey hP z := by
        rcases lt_or_gt_of_ne (GT_key_ne_of_ne hP hzb') with h' | h'
        · exact absurd (GT_edge_of_between hP hab h h') hza
        · exact h'
      exact Or.inr (Or.inr ⟨hlt, hzb⟩)
  have hnot : ∀ a b : Visit P, AdjacentVisits hP a b → a.2.val = b.2.val →
      geometricVisitKey hP a < geometricVisitKey hP b → z.2.val ≠ a.2.val →
      ¬ (geometricVisitKey hP a < geometricVisitKey hP y ∧ geometricVisitKey hP y < geometricVisitKey hP b) := by
    intro a b hab hedge' hlt hza ⟨h1, h2⟩
    exact GT_adj_empty hP hab z (hzout a b hedge' hlt hza) y (Or.inl ⟨h1, h2⟩)
  rcases lt_or_gt_of_ne hkvw with hvw | hwv
  · have hn := hnot v w hadj hedge hvw hz
    constructor
    · constructor
      · intro h; linarith
      · intro h
        rcases lt_or_gt_of_ne hkyv with h' | h'
        · exact h'
        · exact absurd ⟨h', h⟩ hn
    · constructor
      · intro h
        rcases lt_or_gt_of_ne hkyw with h' | h'
        · exact absurd ⟨h, h'⟩ hn
        · exact h'
      · intro h; linarith
  · have hn := hnot w v ⟨Ne.symm hadj.1, hadj.2.symm⟩ hedge.symm hwv (hedge ▸ hz)
    constructor
    · constructor
      · intro h
        rcases lt_or_gt_of_ne hkyw with h' | h'
        · exact h'
        · exact absurd ⟨h', h⟩ hn
      · intro h; linarith
    · constructor
      · intro h; linarith
      · intro h
        rcases lt_or_gt_of_ne hkyv with h' | h'
        · exact absurd ⟨h, h'⟩ hn
        · exact h'

omit [NeZero n] in
theorem GT_cyc_congr_of_lt {a b c a' b' c' : ℝ} (h1 : a < b ↔ a' < b') (h2 : b < c ↔ b' < c')
    (h3 : c < a ↔ c' < a') : cycBetween a b c ↔ cycBetween a' b' c' := by
  unfold cycBetween
  rw [h1, h2, h3]

omit [NeZero n] in
theorem GT_det_pos_iff_of_sign {a b : ℝ} (h : SignType.sign b = SignType.sign a) : 0 < a ↔ 0 < b := by
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

namespace GT_Endpoint

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

local notation "𝑇" => triangleCrossings P e f g
local notation "𝑆" => GT_S Q x
local notation "𝑆'" => transportSupport hs (GT_S Q x)

variable (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
include D

/-! #### The visit relabelling `ψ₀ = swap(τw₂, τm₁) ∘ swap(τw₃, τm₃) ∘ τ` -/

/-- The visit relabelling of the endpoint row (`w₂ ↦ m₁'`, `w₃ ↦ m₃'`, the other visits transported). -/
noncomputable def ψ₀ : Visit P ≃ Visit P' :=
  (visitTransport hs).trans
    ((Equiv.swap (visitTransport hs D.w₃) (visitTransport hs D.m₃)).trans
      (Equiv.swap (visitTransport hs D.w₂) (visitTransport hs D.m₁)))

theorem ψ₀_apply (v : Visit P) :
    D.ψ₀ v = Equiv.swap (visitTransport hs D.w₂) (visitTransport hs D.m₁)
      (Equiv.swap (visitTransport hs D.w₃) (visitTransport hs D.m₃) (visitTransport hs v)) := rfl

theorem w₂_ne_w₃ : D.w₂ ≠ D.w₃ := fun h => D.l23 (congrArg (fun v : Visit P => v.2.val) h)
theorem m₁_ne_m₃ : D.m₁ ≠ D.m₃ := fun h => D.l13 (congrArg (fun v : Visit P => v.2.val) h)
theorem w₂_ne_m₁ : D.w₂ ≠ D.m₁ := fun h => D.wm (congrArg Sigma.fst h)
theorem w₂_ne_m₃ : D.w₂ ≠ D.m₃ := fun h => D.wm (congrArg Sigma.fst h)
theorem w₃_ne_m₁ : D.w₃ ≠ D.m₁ := fun h => D.wm (congrArg Sigma.fst h)
theorem w₃_ne_m₃ : D.w₃ ≠ D.m₃ := fun h => D.wm (congrArg Sigma.fst h)
theorem x₁_ne_x₂ : D.x₁ ≠ D.x₂ := fun h => D.l12 (congrArg (fun v : Visit P => v.2.val) h)

theorem ψ₀_w₂ : D.ψ₀ D.w₂ = visitTransport hs D.m₁ := by
  rw [ψ₀_apply, Equiv.swap_apply_of_ne_of_ne ((visitTransport hs).injective.ne D.w₂_ne_w₃)
    ((visitTransport hs).injective.ne D.w₂_ne_m₃), Equiv.swap_apply_left]

theorem ψ₀_w₃ : D.ψ₀ D.w₃ = visitTransport hs D.m₃ := by
  rw [ψ₀_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne
    ((visitTransport hs).injective.ne D.w₂_ne_m₃.symm) ((visitTransport hs).injective.ne D.m₁_ne_m₃.symm)]

theorem ψ₀_m₁ : D.ψ₀ D.m₁ = visitTransport hs D.w₂ := by
  rw [ψ₀_apply, Equiv.swap_apply_of_ne_of_ne ((visitTransport hs).injective.ne D.w₃_ne_m₁.symm)
    ((visitTransport hs).injective.ne D.m₁_ne_m₃), Equiv.swap_apply_right]

theorem ψ₀_m₃ : D.ψ₀ D.m₃ = visitTransport hs D.w₃ := by
  rw [ψ₀_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne
    ((visitTransport hs).injective.ne D.w₂_ne_w₃.symm) ((visitTransport hs).injective.ne D.w₃_ne_m₁)]

theorem ψ₀_of_ne {v : Visit P} (hvw : v.1 ≠ w) (hvm : v.1 ≠ m) : D.ψ₀ v = visitTransport hs v := by
  have h1 : v ≠ D.w₂ := fun h => hvw (congrArg Sigma.fst h)
  have h2 : v ≠ D.w₃ := fun h => hvw (congrArg Sigma.fst h)
  have h3 : v ≠ D.m₁ := fun h => hvm (congrArg Sigma.fst h)
  have h4 : v ≠ D.m₃ := fun h => hvm (congrArg Sigma.fst h)
  rw [ψ₀_apply, Equiv.swap_apply_of_ne_of_ne ((visitTransport hs).injective.ne h2)
    ((visitTransport hs).injective.ne h4), Equiv.swap_apply_of_ne_of_ne
    ((visitTransport hs).injective.ne h1) ((visitTransport hs).injective.ne h3)]

/-- The visits of `w` are `w₂`, `w₃`. -/
theorem eq_w₂_or_w₃ {v : Visit P} (hv : v.1 = w) : v = D.w₂ ∨ v = D.w₃ := by
  rcases visit_eq_or_twin D.w₂ v hv with h | h
  · exact Or.inl h
  · rw [D.twin_w₂] at h; exact Or.inr h

theorem eq_m₁_or_m₃ {v : Visit P} (hv : v.1 = m) : v = D.m₁ ∨ v = D.m₃ := by
  rcases visit_eq_or_twin D.m₁ v hv with h | h
  · exact Or.inl h
  · rw [D.twin_m₁] at h; exact Or.inr h

/-- `ψ₀` lies over the crossing relabelling `φ`. -/
theorem ψ₀_fst (v : Visit P) : (D.ψ₀ v).1 = GT_φ hs w m v.1 := by
  by_cases hvw : v.1 = w
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · rw [D.ψ₀_w₂, visitTransport_crossing, w₂_fst, φ_w]; rfl
    · rw [D.ψ₀_w₃, visitTransport_crossing, w₃_fst, φ_w]; rfl
  by_cases hvm : v.1 = m
  · rcases D.eq_m₁_or_m₃ hvm with rfl | rfl
    · rw [D.ψ₀_m₁, visitTransport_crossing, m₁_fst, φ_m]; rfl
    · rw [D.ψ₀_m₃, visitTransport_crossing, m₃_fst, φ_m]; rfl
  rw [D.ψ₀_of_ne hvw hvm, visitTransport_crossing, φ_of_ne hvw hvm]

/-- `ψ₀` commutes with the twin pairing. -/
theorem ψ₀_twin (v : Visit P) : D.ψ₀ (visitTwin v) = visitTwin (D.ψ₀ v) := by
  by_cases hvw : v.1 = w
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · rw [D.twin_w₂, D.ψ₀_w₃, D.ψ₀_w₂, ← visitTransport_visitTwin, D.twin_m₁]
    · rw [D.twin_w₃, D.ψ₀_w₂, D.ψ₀_w₃, ← visitTransport_visitTwin, D.twin_m₃]
  by_cases hvm : v.1 = m
  · rcases D.eq_m₁_or_m₃ hvm with rfl | rfl
    · rw [D.twin_m₁, D.ψ₀_m₃, D.ψ₀_m₁, ← visitTransport_visitTwin, D.twin_w₂]
    · rw [D.twin_m₃, D.ψ₀_m₁, D.ψ₀_m₃, ← visitTransport_visitTwin, D.twin_w₃]
  have htw : (visitTwin v).1 = v.1 := visitTwin_crossing v
  rw [D.ψ₀_of_ne hvw hvm, D.ψ₀_of_ne (htw ▸ hvw) (htw ▸ hvm), visitTransport_visitTwin]

/-- The divide signs are carried by `ψ₀` (outside visits by `sign_eq`; `w₂ ↦ m₁'`, `w₃ ↦ m₃'` by the
sign identity `sgn`, R_GENERIC_COMMON_TRANSPORT_PROOF.md (4)/(6)). -/
theorem ψ₀_det (v : Visit P) (hvm : v.1 ≠ m) :
    (0 < det (edge P v.2.val) (edge P (visitTwin v).2.val) ↔
      0 < det (edge P' (D.ψ₀ v).2.val) (edge P' (visitTwin (D.ψ₀ v)).2.val)) := by
  have hsign : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)) := by
    intro i j hij
    exact GT_det_pos_iff_of_sign (D.sign_eq i j hij)
  have hm : IsCrossing P {ℓ₁, ℓ₃} := by rw [← D.mval]; exact m.property
  by_cases hvw : v.1 = w
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · rw [D.twin_w₂, D.ψ₀_w₂, ← visitTransport_visitTwin, D.twin_m₁, visitTransport_edge,
        visitTransport_edge, w₂_edge, w₃_edge, m₁_edge, m₃_edge, ← hsign ℓ₁ ℓ₃ hm]
      exact GT_det_pos_iff_of_sign D.sgn.symm
    · rw [D.twin_w₃, D.ψ₀_w₃, ← visitTransport_visitTwin, D.twin_m₃, visitTransport_edge,
        visitTransport_edge, w₂_edge, w₃_edge, m₁_edge, m₃_edge, ← hsign ℓ₃ ℓ₁ (by rwa [Finset.pair_comm])]
      have h' : crossingSign P ℓ₃ ℓ₂ = crossingSign P ℓ₃ ℓ₁ := by
        rw [crossingSign_swap P ℓ₂ ℓ₃, crossingSign_swap P ℓ₁ ℓ₃, D.sgn]
      exact GT_det_pos_iff_of_sign h'.symm
  · rw [D.ψ₀_of_ne hvw hvm, ← visitTransport_visitTwin, visitTransport_edge, visitTransport_edge]
    apply hsign
    rw [← visit_crossing_val_eq_pair v]
    exact v.1.property

/-! #### Key comparisons with the `ℓ₃`-visits and with the `x`-visits -/

theorem adj1_v : AdjacentVisits hP D.x₁ D.m₁ := D.adj1
theorem adj2_v : AdjacentVisits hP D.x₂ D.w₂ := D.adj2
theorem adj3_v : AdjacentVisits hP D.w₃ D.m₃ := D.adj3
theorem adj1'_v : AdjacentVisits hP' (visitTransport hs D.x₁) (visitTransport hs D.m₁) := D.adj1'
theorem adj2'_v : AdjacentVisits hP' (visitTransport hs D.x₂) (visitTransport hs D.w₂) := D.adj2'
theorem adj3'_v : AdjacentVisits hP' (visitTransport hs D.w₃) (visitTransport hs D.m₃) := D.adj3'

/-- For a visit `y` on another edge than `ℓ₃`, or an outside visit, its key order relative to `w₃`
is carried to the key order of `τy` relative to `m₃'` (`w₃, m₃` are adjacent on `ℓ₃`, `x₁` on another
edge). -/
theorem key_lt_w₃_iff (y : Visit P) (hy : y.1 ≠ w) (hym : y.1 ≠ m) (hyx : y.2.val ≠ ℓ₃ ∨ y.1.val ∉ triangleSupports e f g) :
    (geometricVisitKey hP y < geometricVisitKey hP D.w₃ ↔
        geometricVisitKey hP' (visitTransport hs y) < geometricVisitKey hP' (visitTransport hs D.m₃)) ∧
    (geometricVisitKey hP D.w₃ < geometricVisitKey hP y ↔
        geometricVisitKey hP' (visitTransport hs D.m₃) < geometricVisitKey hP' (visitTransport hs y)) := by
  have hyw3 : y ≠ D.w₃ := fun h => hy (congrArg Sigma.fst h)
  have hym3 : y ≠ D.m₃ := fun h => hym (congrArg Sigma.fst h)
  -- the order of `y` and `m₃` is carried (not a reversed pair: `y ∉ T`, or different edges)
  have hcarry : ∀ v : Visit P, v.2.val ≠ ℓ₃ ∨ v.1.val ∉ triangleSupports e f g →
      (geometricVisitKey hP v < geometricVisitKey hP D.m₃ ↔
        geometricVisitKey hP' (visitTransport hs v) < geometricVisitKey hP' (visitTransport hs D.m₃)) ∧
      (geometricVisitKey hP D.m₃ < geometricVisitKey hP v ↔
        geometricVisitKey hP' (visitTransport hs D.m₃) < geometricVisitKey hP' (visitTransport hs v)) := by
    intro v hv
    have hnr : ¬ GT_Rev 𝑇 v D.m₃ := by
      rcases hv with hv | hv
      · exact GT_not_rev_of_edge_ne hv
      · exact GT_not_rev_of_not_mem_left (fun h => hv ((F1.mem_triangleCrossings e f g v.1).mp h))
    exact ⟨D.wall.key_lt v D.m₃ hnr, D.wall.key_lt D.m₃ v (fun h => hnr h.symm)⟩
  by_cases hy3 : y.2.val = ℓ₃
  · -- `y` on `ℓ₃`, outside: not between the adjacent `w₃`, `m₃`
    have hlt := GT_adj_lt_iff hP D.adj3_v rfl D.x₁ D.l13 y hyw3 hym3
    rw [hlt.1, hlt.2]
    exact hcarry y (Or.inr (hyx.resolve_left (fun h => h hy3)))
  · -- different edges: the key order is the edge order, on both sides
    have h1 := GT_key_lt_iff_of_edge_ne hP (v := y) (w := D.w₃) hy3
    have h2 := GT_key_lt_iff_of_edge_ne hP' (v := visitTransport hs y) (w := visitTransport hs D.m₃)
      (by rw [visitTransport_edge, visitTransport_edge]; exact hy3)
    have h3 := GT_key_lt_iff_of_edge_ne hP (v := D.w₃) (w := y) (Ne.symm hy3)
    have h4 := GT_key_lt_iff_of_edge_ne hP' (v := visitTransport hs D.m₃) (w := visitTransport hs y)
      (by rw [visitTransport_edge, visitTransport_edge]; exact Ne.symm hy3)
    rw [h1, h2, h3, h4, visitTransport_edge, visitTransport_edge]
    exact ⟨Iff.rfl, Iff.rfl⟩

end GT_Endpoint

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

namespace GT_Endpoint

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

local notation "𝑇" => triangleCrossings P e f g
local notation "𝑆" => GT_S Q x
local notation "𝑆'" => transportSupport hs (GT_S Q x)

variable (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
include D

/-! #### The carrier of `w` and the arcs cut by the two visits of `x` -/

/-- The carrier of `S` bearing `w` (the "`BC`"-type carrier of §2). -/
noncomputable abbrev qw : GeoComponent hP 𝑆 := geoOwner hP 𝑆 (Sum.inr D.w₃)

theorem owner_w₂ : geoOwner hP 𝑆 (Sum.inr D.w₂) = D.qw := D.owner_w₂_eq_w₃

/-- `w₂` is adjacent to `x₂`, so the carrier of `w` is the carrier of `x₂` or that of `x₁`. -/
theorem qw_eq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂) ∨ D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁) := by
  rcases GT_succ_of_adjacent hP D.adj2_v rfl with h | h
  · right
    rw [← D.owner_w₂, ← geoOwner_successor hP _ (Sum.inr D.x₁),
      geoSmoothingSuccessor_visit_of_mem hP (GT_S Q x) D.x₁ x_mem_S, D.twin_x₁, h]
  · left
    rw [← D.owner_w₂, ← geoOwner_successor hP _ (Sum.inr D.w₂),
      geoSmoothingSuccessor_visit_of_not_mem hP (GT_S Q x) D.w₂ D.w_not_mem_S, h]

theorem mem_arc_of_owner_x₂ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂)) {u : Mark P}
    (hu : geoOwner hP 𝑆 u = D.qw) (hne : u ≠ Sum.inr D.x₂) :
    cycBetween (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP u) (geoMarkKey hP (Sum.inr D.x₂)) := by
  have h := GT_owner_arc hP D.S_geoIndep (x₁ := D.x₁) x_mem_S u (by rw [hu, hq, D.twin_x₁])
  rw [D.twin_x₁] at h
  exact h.resolve_left hne

theorem mem_arc_of_owner_x₁ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁)) {u : Mark P}
    (hu : geoOwner hP 𝑆 u = D.qw) (hne : u ≠ Sum.inr D.x₁) :
    cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP u) (geoMarkKey hP (Sum.inr D.x₁)) := by
  have h := GT_owner_arc hP D.S_geoIndep (x₁ := D.x₂) x_mem_S u (by rw [hu, hq, D.twin_x₂])
  rw [D.twin_x₂] at h
  exact h.resolve_left hne

theorem x'_mem_S' : (visitTransport hs D.x₁).1 ∈ 𝑆' := (mem_S'_iff x).mpr x_mem_S

theorem twin_τx₁ : visitTwin (visitTransport hs D.x₁) = visitTransport hs D.x₂ := by
  rw [← visitTransport_visitTwin, D.twin_x₁]
theorem twin_τx₂ : visitTwin (visitTransport hs D.x₂) = visitTransport hs D.x₁ := by
  rw [← visitTransport_visitTwin, D.twin_x₂]

theorem β_qw_of_x₂ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂)) :
    D.β D.qw = geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.x₂)) := by
  rw [hq, ← markTransport_visit, GT_owner_transport_corner D.wall D.x₂_corner]

theorem β_qw_of_x₁ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁)) :
    D.β D.qw = geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.x₁)) := by
  rw [hq, ← markTransport_visit, GT_owner_transport_corner D.wall D.x₁_corner]

theorem mem_arc'_of_owner_x₂ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂)) {u' : Mark P'}
    (hu : geoOwner hP' 𝑆' u' = D.β D.qw) (hne : u' ≠ Sum.inr (visitTransport hs D.x₂)) :
    cycBetween (geoMarkKey hP' (Sum.inr (visitTransport hs D.x₁))) (geoMarkKey hP' u')
      (geoMarkKey hP' (Sum.inr (visitTransport hs D.x₂))) := by
  have h := GT_owner_arc hP' D.S'_ind (x₁ := visitTransport hs D.x₁) D.x'_mem_S' u'
    (by rw [hu, D.β_qw_of_x₂ hq, D.twin_τx₁])
  rw [D.twin_τx₁] at h
  exact h.resolve_left hne

theorem mem_arc'_of_owner_x₁ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁)) {u' : Mark P'}
    (hu : geoOwner hP' 𝑆' u' = D.β D.qw) (hne : u' ≠ Sum.inr (visitTransport hs D.x₁)) :
    cycBetween (geoMarkKey hP' (Sum.inr (visitTransport hs D.x₂))) (geoMarkKey hP' u')
      (geoMarkKey hP' (Sum.inr (visitTransport hs D.x₁))) := by
  have h := GT_owner_arc hP' D.S'_ind (x₁ := visitTransport hs D.x₂)
    ((mem_S'_iff x).mpr x_mem_S) u' (by rw [hu, D.β_qw_of_x₁ hq, D.twin_τx₂])
  rw [D.twin_τx₂] at h
  exact h.resolve_left hne

/-! #### The visits of the piece of `w` -/

/-- A visit of a crossing of `U(S)` other than `m`: its carrier's copy carries the relabelled visit. -/
theorem owner'_ψ₀ {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) :
    geoOwner hP' 𝑆' (Sum.inr (D.ψ₀ v)) = D.β (geoOwner hP 𝑆 (Sum.inr v)) := by
  rcases D.mem_U_cases hv with hvw | hvT
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · rw [D.ψ₀_w₂, D.owner'_m₁, D.owner_w₂]
    · rw [D.ψ₀_w₃, D.owner'_m₃]
  · have hvw : v.1 ≠ w := fun h => hvT (h ▸ D.wT)
    have hvm : v.1 ≠ m := fun h => hvT (h ▸ D.mT)
    rw [D.ψ₀_of_ne hvw hvm, ← markTransport_visit]
    exact GT_owner_transport D.wall (good_of_outside hvT)

/-- Key orders are carried by `ψ₀` on the visits of `U(S) ∪ {x}` other than `w₂` (the visits of
outside crossings, the two visits of `x`, and `w₃ ↦ m₃'`). -/
theorem key_lt_ψ₀ (y z : Visit P) (hy : y.1 ≠ m ∧ (y.1 ≠ w ∨ y = D.w₃))
    (hz : z.1 ≠ m ∧ (z.1 ≠ w ∨ z = D.w₃)) :
    geometricVisitKey hP y < geometricVisitKey hP z ↔
      geometricVisitKey hP' (D.ψ₀ y) < geometricVisitKey hP' (D.ψ₀ z) := by
  -- a visit of a triangle crossing other than `w, m` is a visit of `x`, hence not on `ℓ₃`
  have hx3 : ∀ v : Visit P, v.1 ≠ w → v.1 ≠ m → v.2.val ≠ ℓ₃ ∨ v.1.val ∉ triangleSupports e f g := by
    intro v hvw hvm
    by_cases hvT : v.1.val ∈ triangleSupports e f g
    · left
      rcases D.tri_cases v.1 hvT with hvx | hvx | hvx
      · intro h3
        apply D.l3_not_mem_x
        rw [← h3, ← hvx]
        exact v.2.property
      · exact absurd hvx hvw
      · exact absurd hvx hvm
    · exact Or.inr hvT
  rcases hy.2 with hyw | rfl <;> rcases hz.2 with hzw | rfl
  · -- neither is `w₃`: transported visits, not a reversed pair
    rw [D.ψ₀_of_ne hyw hy.1, D.ψ₀_of_ne hzw hz.1]
    apply D.wall.key_lt
    rintro ⟨hyT, hzT, hne, -⟩
    have hyx := D.tri_cases y.1 ((F1.mem_triangleCrossings e f g y.1).mp hyT)
    have hzx := D.tri_cases z.1 ((F1.mem_triangleCrossings e f g z.1).mp hzT)
    rcases hyx with hyx | hyx | hyx <;> rcases hzx with hzx | hzx | hzx <;>
      first | exact hne (hyx.trans hzx.symm) | exact absurd hyx hyw | exact absurd hyx hy.1 |
        exact absurd hzx hzw | exact absurd hzx hz.1
  · rw [D.ψ₀_of_ne hyw hy.1, D.ψ₀_w₃]
    exact (D.key_lt_w₃_iff y hyw hy.1 (hx3 y hyw hy.1)).1
  · rw [D.ψ₀_of_ne hzw hz.1, D.ψ₀_w₃]
    exact (D.key_lt_w₃_iff z hzw hz.1 (hx3 z hzw hz.1)).2
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)

theorem x₁_not_mem_U_visit : D.x₁.1 ∉ CV.U hP 𝑆 := x_not_mem_U
theorem x₁_ne_of_mem_U {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) : D.x₁ ≠ v :=
  fun h => x_not_mem_U (h ▸ hv)
theorem x₂_ne_of_mem_U {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) : D.x₂ ≠ v :=
  fun h => x_not_mem_U (h ▸ hv)
theorem τx₁_ne_ψ₀_of_mem_U {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) : visitTransport hs D.x₁ ≠ D.ψ₀ v := by
  intro h
  have h1 := congrArg Sigma.fst h
  rw [D.ψ₀_fst, visitTransport_crossing] at h1
  have : GT_φ hs w m v.1 ∈ CV.U hP' 𝑆' := (D.mem_U_iff v.1).mpr hv
  rw [← h1] at this
  exact x'_not_mem_U this
theorem τx₂_ne_ψ₀_of_mem_U {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) : visitTransport hs D.x₂ ≠ D.ψ₀ v := by
  intro h
  have h1 := congrArg Sigma.fst h
  rw [D.ψ₀_fst, visitTransport_crossing] at h1
  have : GT_φ hs w m v.1 ∈ CV.U hP' 𝑆' := (D.mem_U_iff v.1).mpr hv
  rw [← h1] at this
  exact x'_not_mem_U this

/-- `ψ₀ v = m₁'` only for `v = w₂`. -/
theorem ψ₀_ne_τm₁ {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) (hvw₂ : v ≠ D.w₂) :
    D.ψ₀ v ≠ visitTransport hs D.m₁ := by
  intro h
  have h1 := congrArg Sigma.fst h
  rw [D.ψ₀_fst, visitTransport_crossing, m₁_fst] at h1
  rcases D.mem_U_cases hv with hvw | hvT
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · exact hvw₂ rfl
    · rw [D.ψ₀_w₃] at h
      exact D.m₁_ne_m₃ ((visitTransport hs).injective h).symm
  · rw [D.φ_of_outside hvT] at h1
    exact hvT (((crossingTransport hs).injective h1) ▸ D.mT)

/-- **The rotation clause, case `qw = owner x₂`**: from `x₁`, every visit of the piece comes before
`w₂` (the last visit before `x₂`), and on the other side `m₁'` (the first after `x₁'`) comes before
every relabelled visit. -/
theorem rot_of_owner_x₂ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂)) {u : Visit P}
    (hu : u.1 ∈ CV.U hP 𝑆) (hqu : geoOwner hP 𝑆 (Sum.inr u) = D.qw) (huw : u ≠ D.w₂) :
    cycBetween (geometricVisitKey hP D.x₁) (geometricVisitKey hP u) (geometricVisitKey hP D.w₂) ∧
    cycBetween (geometricVisitKey hP' (visitTransport hs D.x₁))
      (geometricVisitKey hP' (visitTransport hs D.m₁)) (geometricVisitKey hP' (D.ψ₀ u)) := by
  have hne2 : u ≠ D.x₂ := (D.x₂_ne_of_mem_U hu).symm
  have hw2ne : D.w₂ ≠ D.x₂ := fun h => D.xw (congrArg Sigma.fst h).symm
  have hu_arc := D.mem_arc_of_owner_x₂ hq (u := Sum.inr u) hqu (fun h => hne2 (Sum.inr.inj h))
  have hw_arc := D.mem_arc_of_owner_x₂ hq (u := Sum.inr D.w₂) D.owner_w₂ (fun h => hw2ne (Sum.inr.inj h))
  constructor
  · -- the arc from `w₂` to `x₂` is empty: `x₁` lies in the other arc
    have hempty : ∀ v : Visit P, ¬ cycBetween (geometricVisitKey hP D.w₂) (geometricVisitKey hP v)
        (geometricVisitKey hP D.x₂) :=
      GT_adj_empty' hP D.adj2_v D.x₁ (GT_cyc_rotate.mp (GT_cyc_rotate.mp hw_arc))
    rcases GT_cyc_total (GT_key_ne_of_ne hP (D.x₁_ne_of_mem_U hu))
      (GT_key_ne_of_ne hP (v := D.x₁) (w := D.w₂) (fun h => D.xw (congrArg Sigma.fst h)))
      (GT_key_ne_of_ne hP huw) with h | h
    · exact h
    · exact absurd (GT_cyc_arc_step hu_arc hw_arc h) (hempty u)
  · -- on the other side: the arc from `x₁'` to `m₁'` is empty
    have hu'_arc := D.mem_arc'_of_owner_x₂ hq (u' := Sum.inr (D.ψ₀ u))
      (by rw [D.owner'_ψ₀ hu, hqu]) (fun h => D.τx₂_ne_ψ₀_of_mem_U hu (Sum.inr.inj h).symm)
    have hm'_arc := D.mem_arc'_of_owner_x₂ hq (u' := Sum.inr (visitTransport hs D.m₁))
      (by rw [D.owner'_m₁])
      (fun h => D.xm (congrArg Sigma.fst ((visitTransport hs).injective (Sum.inr.inj h))).symm)
    have hempty : ∀ v : Visit P', ¬ cycBetween (geometricVisitKey hP' (visitTransport hs D.x₁))
        (geometricVisitKey hP' v) (geometricVisitKey hP' (visitTransport hs D.m₁)) :=
      GT_adj_empty hP' D.adj1'_v (visitTransport hs D.x₂) (GT_cyc_rotate.mp hm'_arc)
    rcases GT_cyc_total (GT_key_ne_of_ne hP' ((visitTransport hs).injective.ne
        (fun h : D.x₁ = D.m₁ => D.xm (congrArg Sigma.fst h))))
      (GT_key_ne_of_ne hP' (D.τx₁_ne_ψ₀_of_mem_U hu))
      (GT_key_ne_of_ne hP' (D.ψ₀_ne_τm₁ hu huw).symm) with h | h
    · exact h
    · exact absurd h (hempty _)

/-- **The rotation clause, case `qw = owner x₁`**: from `x₂`, `w₂` (the first visit after `x₂`) comes
before every visit of the piece, and on the other side every relabelled visit comes before `m₁'` (the
last before `x₁'`). -/
theorem rot_of_owner_x₁ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁)) {u : Visit P}
    (hu : u.1 ∈ CV.U hP 𝑆) (hqu : geoOwner hP 𝑆 (Sum.inr u) = D.qw) (huw : u ≠ D.w₂) :
    cycBetween (geometricVisitKey hP D.x₂) (geometricVisitKey hP D.w₂) (geometricVisitKey hP u) ∧
    cycBetween (geometricVisitKey hP' (visitTransport hs D.x₂)) (geometricVisitKey hP' (D.ψ₀ u))
      (geometricVisitKey hP' (visitTransport hs D.m₁)) := by
  have hne1 : u ≠ D.x₁ := (D.x₁_ne_of_mem_U hu).symm
  have hw1ne : D.w₂ ≠ D.x₁ := fun h => D.xw (congrArg Sigma.fst h).symm
  have hu_arc := D.mem_arc_of_owner_x₁ hq (u := Sum.inr u) hqu (fun h => hne1 (Sum.inr.inj h))
  have hw_arc := D.mem_arc_of_owner_x₁ hq (u := Sum.inr D.w₂) D.owner_w₂ (fun h => hw1ne (Sum.inr.inj h))
  constructor
  · -- the arc from `x₂` to `w₂` is empty: `x₁` lies in the other arc
    have hempty : ∀ v : Visit P, ¬ cycBetween (geometricVisitKey hP D.x₂) (geometricVisitKey hP v)
        (geometricVisitKey hP D.w₂) :=
      GT_adj_empty hP D.adj2_v D.x₁ (GT_cyc_rotate.mp hw_arc)
    rcases GT_cyc_total (GT_key_ne_of_ne hP (D.x₂_ne_of_mem_U hu))
      (GT_key_ne_of_ne hP (v := D.x₂) (w := D.w₂) (fun h => D.xw (congrArg Sigma.fst h)))
      (GT_key_ne_of_ne hP huw) with h | h
    · exact absurd h (hempty u)
    · exact h
  · -- on the other side: the arc from `m₁'` to `x₁'` is empty
    have hu'_arc := D.mem_arc'_of_owner_x₁ hq (u' := Sum.inr (D.ψ₀ u))
      (by rw [D.owner'_ψ₀ hu, hqu]) (fun h => D.τx₁_ne_ψ₀_of_mem_U hu (Sum.inr.inj h).symm)
    have hm'_arc := D.mem_arc'_of_owner_x₁ hq (u' := Sum.inr (visitTransport hs D.m₁))
      (by rw [D.owner'_m₁])
      (fun h => D.xm (congrArg Sigma.fst ((visitTransport hs).injective (Sum.inr.inj h))).symm)
    have hempty : ∀ v : Visit P', ¬ cycBetween (geometricVisitKey hP' (visitTransport hs D.m₁))
        (geometricVisitKey hP' v) (geometricVisitKey hP' (visitTransport hs D.x₁)) :=
      GT_adj_empty' hP' D.adj1'_v (visitTransport hs D.x₂)
        (GT_cyc_rotate.mp (GT_cyc_rotate.mp hm'_arc))
    rcases GT_cyc_total (GT_key_ne_of_ne hP' (D.τx₂_ne_ψ₀_of_mem_U hu))
      (GT_key_ne_of_ne hP' ((visitTransport hs).injective.ne
        (fun h : D.x₂ = D.m₁ => D.xm (congrArg Sigma.fst h))))
      (GT_key_ne_of_ne hP' (D.ψ₀_ne_τm₁ hu huw)) with h | h
    · exact h
    · exact absurd (GT_cyc_arc_step hu'_arc hm'_arc h) (hempty _)

end GT_Endpoint

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

/-! ### The X₁ objects of the endpoint row across the wall (`CV.Generic` binders) -/

section GTEndpointX1

variable {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
variable (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)

/-- The piece polynomials of the pieces not containing `w` are carried (their labels are outside and
transported; `EXT_pieceHomfly_wall`). -/
theorem GT_endpoint_pieceHomfly_out (H : CV.Piece hG.crossingGeometry (GT_S Q x))
    (hw : w ∉ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H) :
    CV.pieceHomfly hn (hG'.diagrammatic hn) D.S'_mem_Ind (GT_pieceEquiv D.relabel H) =
      CV.pieceHomfly hn (hG.diagrammatic hn) D.S_ind H := by
  have hout : ∀ c ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H, c.val ∉ triangleSupports e f g := by
    intro c hc
    rcases D.mem_U_cases (CV.pieceLabels_subset _ _ H hc) with rfl | h
    · exact absurd hc hw
    · exact h
  refine EXT_pieceHomfly_wall hn hG hG' hs D.S_ind D.S'_mem_Ind ?_ ?_ H (GT_pieceEquiv D.relabel H)
    hout ?_
  · intro v w hv hw
    exact D.wall.key_lt v w (GT_not_rev_of_not_mem_left
      (fun h => hv ((F1.mem_triangleCrossings e f g v.1).mp h)))
  · intro i j hij
    exact GT_det_pos_iff_of_sign (D.sign_eq i j hij)
  · rw [GT_pieceLabels_eq D.relabel H]
    ext c'
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, by rw [D.φ_of_outside (hout c hc)]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, by rw [D.φ_of_outside (hout c hc)]⟩

/-- The visits of the piece of `w` lie on the carrier of `w`. -/
theorem GT_endpoint_owner_of_mem_piece (H : CV.Piece hG.crossingGeometry (GT_S Q x))
    (hw : w ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H) {v : Visit P}
    (hv : v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H) :
    geoOwner hG.crossingGeometry (GT_S Q x) (Sum.inr v) = D.qw := by
  obtain ⟨hc, hH⟩ := (CV.mem_pieceLabels _ _ H v.1).mp hv
  obtain ⟨hw', hHw⟩ := (CV.mem_pieceLabels _ _ H w).mp hw
  exact CV.owner_eq_of_same_piece _ D.S_ind hc hw' (hH.trans hHw.symm) v D.w₃ rfl rfl

/-- **The piece polynomial of the piece of `w` is carried**: the relabelled record isomorphism
(`GT_homfly_wall_gen` with `ψ₀`), its cyclic-order clause from `GT_cyc_carried` (the arc of the
carrier of `w`, `w₂` moving from last to first or from first to last). -/
theorem GT_endpoint_pieceHomfly_w (H : CV.Piece hG.crossingGeometry (GT_S Q x))
    (hw : w ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H) :
    CV.pieceHomfly hn (hG'.diagrammatic hn) D.S'_mem_Ind (GT_pieceEquiv D.relabel H) =
      CV.pieceHomfly hn (hG.diagrammatic hn) D.S_ind H := by
  unfold CV.pieceHomfly CV.pieceDiagram
  have hret := CV.pieceCarrier_geoCarrierCrossings (hG.diagrammatic hn) D.S_ind H
  have hret' := CV.pieceCarrier_geoCarrierCrossings (hG'.diagrammatic hn) D.S'_mem_Ind
    (GT_pieceEquiv D.relabel H)
  have hlab' := GT_pieceLabels_eq D.relabel H
  -- membership of a visit in the retained set of the piece carrier
  have hmem : ∀ v : Visit P,
      v.1 ∈ geoCarrierCrossings hG.crossingGeometry _ (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H) ↔
      v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H := fun v => by rw [hret]
  have hmem' : ∀ v : Visit P,
      (D.ψ₀ v).1 ∈ geoCarrierCrossings hG'.crossingGeometry _
        (CV.pieceCarrier (hG'.diagrammatic hn) D.S'_mem_Ind (GT_pieceEquiv D.relabel H)) ↔
      v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H := fun v => by
    rw [hret', hlab', D.ψ₀_fst, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  let ψ : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
      (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)} ≃
      {v' : Visit P' // v'.1 ∈ geoCarrierCrossings hG'.crossingGeometry _
        (CV.pieceCarrier (hG'.diagrammatic hn) D.S'_mem_Ind (GT_pieceEquiv D.relabel H))} :=
    Equiv.subtypeEquiv D.ψ₀ (fun v => (hmem v).trans (hmem' v).symm)
  have hU : ∀ v : Visit P, v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H →
      v.1 ∈ CV.U hG.crossingGeometry (GT_S Q x) := fun v hv => CV.pieceLabels_subset _ _ H hv
  refine GT_homfly_wall_gen hn _ _ _ _ _ _ ψ ?_ ?_ ?_
  · intro v hv
    exact D.ψ₀_twin v
  · -- the cyclic order
    intro u v s hcyc
    have hw₂ : D.w₂.1 ∈ geoCarrierCrossings hG.crossingGeometry _
        (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H) := (hmem D.w₂).mpr hw
    have key := GT_cyc_carried (ι := {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
        (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)})
      (fun v => geometricVisitKey hG.crossingGeometry v.1)
      (fun v => geometricVisitKey hG'.crossingGeometry (D.ψ₀ v.1))
    -- the two cases of the carrier of `w`
    have hgood : ∀ v : Visit P, v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H → v ≠ D.w₂ →
        v.1 ≠ m ∧ (v.1 ≠ w ∨ v = D.w₃) := by
      intro v hv hvw
      have hvU := hU v hv
      refine ⟨fun h => D.m_not_mem_U (h ▸ hvU), ?_⟩
      by_cases h : v.1 = w
      · rcases D.eq_w₂_or_w₃ h with rfl | rfl
        · exact absurd rfl hvw
        · exact Or.inr rfl
      · exact Or.inl h
    have hinj₁ : Function.Injective (fun v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
        (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)} => geometricVisitKey hG.crossingGeometry v.1) :=
      fun a b h => Subtype.ext (geometricVisitKey_injective _ h)
    have hinj₂ : Function.Injective (fun v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
        (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)} =>
          geometricVisitKey hG'.crossingGeometry (D.ψ₀ v.1)) :=
      fun a b h => Subtype.ext (D.ψ₀.injective (geometricVisitKey_injective _ h))
    have hrest : ∀ (a : Visit P), a.1 ≠ m → (a.1 ≠ w ∨ a = D.w₃) →
        ∀ (u v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
          (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)}), u ≠ ⟨D.w₂, hw₂⟩ → v ≠ ⟨D.w₂, hw₂⟩ →
        (cycBetween (geometricVisitKey hG.crossingGeometry a) (geometricVisitKey hG.crossingGeometry u.1)
            (geometricVisitKey hG.crossingGeometry v.1) ↔
          cycBetween (geometricVisitKey hG'.crossingGeometry (D.ψ₀ a))
            (geometricVisitKey hG'.crossingGeometry (D.ψ₀ u.1))
            (geometricVisitKey hG'.crossingGeometry (D.ψ₀ v.1))) := by
      intro a ham haw u v hu hv
      have hu' := hgood u.1 ((hmem u.1).mp u.2) (fun h => hu (Subtype.ext h))
      have hv' := hgood v.1 ((hmem v.1).mp v.2) (fun h => hv (Subtype.ext h))
      exact GT_cyc_congr_of_lt (D.key_lt_ψ₀ a u.1 ⟨ham, haw⟩ hu') (D.key_lt_ψ₀ u.1 v.1 hu' hv')
        (D.key_lt_ψ₀ v.1 a hv' ⟨ham, haw⟩)
    rcases D.qw_eq with hq | hq
    · -- `qw = owner x₂`: base point `x₁`, `w₂` last ↦ `m₁'` first
      have hx₁ : D.x₁.1 ≠ m ∧ (D.x₁.1 ≠ w ∨ D.x₁ = D.w₃) := ⟨D.xm, Or.inl D.xw⟩
      refine (key (geometricVisitKey hG.crossingGeometry D.x₁)
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs D.x₁)) hinj₁ hinj₂ ?_ ?_ ⟨D.w₂, hw₂⟩
        ?_ ?_ u v s).mp hcyc
      · intro u
        exact GT_key_ne_of_ne _ (D.x₁_ne_of_mem_U (hU u.1 ((hmem u.1).mp u.2)))
      · intro u
        exact GT_key_ne_of_ne _ (D.τx₁_ne_ψ₀_of_mem_U (hU u.1 ((hmem u.1).mp u.2)))
      · intro u v hu hv
        have := hrest D.x₁ hx₁.1 hx₁.2 u v hu hv
        rwa [D.ψ₀_of_ne D.xw D.xm] at this
      · right; left
        intro u hu
        have hu' := D.rot_of_owner_x₂ hq (hU u.1 ((hmem u.1).mp u.2))
          (GT_endpoint_owner_of_mem_piece hG hG' D H hw ((hmem u.1).mp u.2))
          (fun h => hu (Subtype.ext h))
        refine ⟨hu'.1, ?_⟩
        show cycBetween (geometricVisitKey hG'.crossingGeometry (visitTransport hs D.x₁))
          (geometricVisitKey hG'.crossingGeometry (D.ψ₀ D.w₂)) (geometricVisitKey hG'.crossingGeometry (D.ψ₀ u.1))
        rw [D.ψ₀_w₂]
        exact hu'.2
    · -- `qw = owner x₁`: base point `x₂`, `w₂` first ↦ `m₁'` last
      have hx₂ : D.x₂.1 ≠ m ∧ (D.x₂.1 ≠ w ∨ D.x₂ = D.w₃) := ⟨D.xm, Or.inl D.xw⟩
      refine (key (geometricVisitKey hG.crossingGeometry D.x₂)
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs D.x₂)) hinj₁ hinj₂ ?_ ?_ ⟨D.w₂, hw₂⟩
        ?_ ?_ u v s).mp hcyc
      · intro u
        exact GT_key_ne_of_ne _ (D.x₂_ne_of_mem_U (hU u.1 ((hmem u.1).mp u.2)))
      · intro u
        exact GT_key_ne_of_ne _ (D.τx₂_ne_ψ₀_of_mem_U (hU u.1 ((hmem u.1).mp u.2)))
      · intro u v hu hv
        have := hrest D.x₂ hx₂.1 hx₂.2 u v hu hv
        rwa [D.ψ₀_of_ne D.xw D.xm] at this
      · right; right
        intro u hu
        have hu' := D.rot_of_owner_x₁ hq (hU u.1 ((hmem u.1).mp u.2))
          (GT_endpoint_owner_of_mem_piece hG hG' D H hw ((hmem u.1).mp u.2))
          (fun h => hu (Subtype.ext h))
        refine ⟨hu'.1, ?_⟩
        show cycBetween (geometricVisitKey hG'.crossingGeometry (visitTransport hs D.x₂))
          (geometricVisitKey hG'.crossingGeometry (D.ψ₀ u.1)) (geometricVisitKey hG'.crossingGeometry (D.ψ₀ D.w₂))
        rw [D.ψ₀_w₂]
        exact hu'.2
  · -- the divide signs
    intro v
    exact D.ψ₀_det v.1 (fun h => D.m_not_mem_U (h ▸ hU v.1 ((hmem v.1).mp v.2)))

/-- `P_{S,L}` is carried across the wall for the endpoint row. -/
theorem GT_endpoint_groupedPoly_eq (q : GeoComponent hG.crossingGeometry (GT_S Q x)) :
    CV.groupedPoly hn hG' D.S'_mem_Ind (D.β q) = CV.groupedPoly hn hG D.S_ind q := by
  unfold CV.groupedPoly
  rw [GT_piecesOn_eq D.relabel q, Finset.prod_map]
  refine Finset.prod_congr rfl fun H _ => ?_
  by_cases hw : w ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H
  · exact GT_endpoint_pieceHomfly_w hn hG hG' D H hw
  · exact GT_endpoint_pieceHomfly_out hn hG hG' D H hw

theorem GT_endpoint_groupedWrithe_eq (q : GeoComponent hG.crossingGeometry (GT_S Q x)) :
    CV.groupedWrithe hG' (D.β q) = CV.groupedWrithe hG q := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG' D.S'_mem_Ind,
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG D.S_ind, GT_card_geoCarrierCrossings_eq D.relabel q]

theorem GT_endpoint_Omega1_eq (q : GeoComponent hG.crossingGeometry (GT_S Q x)) :
    CV.Omega1 hn hG' D.S'_mem_Ind (D.β q) = CV.Omega1 hn hG D.S_ind q := by
  unfold CV.Omega1 CV.slot
  rw [GT_endpoint_groupedWrithe_eq hG hG' D q, GT_carrierR_eq hn hG hG' D.wall D.S_ind D.S'_mem_Ind q,
    GT_endpoint_groupedPoly_eq hn hG hG' D q]

/-- **The summand transport of an endpoint row.** -/
theorem GT_endpoint_summandTransport : SummandTransport hn hG hG' D.S_ind D.S'_mem_Ind :=
  ⟨GT_wind_eq hn hG hG' D.wall, D.β, fun q =>
    ⟨GT_weight_eq hn hG hG' D.wall q, GT_carrierR_eq hn hG hG' D.wall D.S_ind D.S'_mem_Ind q,
      GT_endpoint_groupedWrithe_eq hG hG' D q, GT_endpoint_groupedPoly_eq hn hG hG' D q,
      GT_endpoint_Omega1_eq hn hG hG' D q⟩⟩

include D in
/-- **`T_P(x) = T_E(x)`**: the row term of the endpoint row is carried across the wall
(R_GENERIC_COMMON_TRANSPORT_PROOF.md §2–§3, on the abstract configuration). -/
theorem GT_endpoint_rowTerm_eq :
    rowTerm hn hG (Q ∪ {x}) = rowTerm hn hG' (transportSupport hs (Q ∪ {x})) :=
  AV_rowTerm_eq_of_summandTransport hn hG hG' D.S_ind D.S'_mem_Ind
    (GT_endpoint_summandTransport hn hG hG' D)

end GTEndpointX1

end GT

section GT

open SM.Carrier SM.Link

/-! ### The endpoint configuration from the event data (rows 164, 172-table, the sign radius) -/

section GTEvent

variable {P : LabelledTuple n}

omit [NeZero n] in
theorem GT_adjacent_symm {hP : CrossingGeometry P} {v w : Visit P} (h : AdjacentVisits hP v w) :
    AdjacentVisits hP w v :=
  ⟨Ne.symm h.1, h.2.symm⟩

omit [NeZero n] in
/-- A crossing containing two distinct labels is carried by exactly that pair. -/
theorem GT_val_eq_pair {y : Crossing P} {i j : ZMod n} (hi : i ∈ y.val) (hj : j ∈ y.val) (hij : i ≠ j) :
    y.val = {i, j} := by
  have h2 := crossing_card_two y
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  · exact le_of_eq (by rw [h2, Finset.card_pair hij])

omit [NeZero n] in
theorem GT_isCrossing_of_mem {y : Crossing P} {i j : ZMod n} (hi : i ∈ y.val) (hj : j ∈ y.val)
    (hij : i ≠ j) : IsCrossing P {i, j} := by
  rw [← GT_val_eq_pair hi hj hij]; exact y.property

omit [NeZero n] in
theorem GT_S_eq_insert {Q : Finset (Crossing P)} {x : Crossing P} : GT_S Q x = insert x Q := by
  rw [Finset.insert_eq, Finset.union_comm]

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **Adjacency of any two triangle crossings on their common edge** (R-LOC-2 (2), all three pairs,
either order). -/
theorem GT_adjacent_of_shared (hL : LocalizationData E e f g δ) (hef : e ≠ f) (heg : e ≠ g)
    (hfg : f ≠ g) (t : E.Parameter) (ht : Punctured E δ t) {y z : Crossing (E.curve t)}
    (hy : y.val ∈ triangleSupports e f g) (hz : z.val ∈ triangleSupports e f g) (hyz : y ≠ z)
    {ℓ : ZMod n} (hℓy : ℓ ∈ y.val) (hℓz : ℓ ∈ z.val) :
    AdjacentVisits (geomAt E t ht.1) (visitOn y ℓ hℓy) (visitOn z ℓ hℓz) := by
  obtain ⟨hef', heg', hfg'⟩ := hL.triangle_crossings t ht
  obtain ⟨h1, h2, h3⟩ := hL.adjacent t ht hef' heg' hfg'
  have hy' := (P1.mem_triangleCrossings_iff hef' heg' hfg' y).mp
    ((F1.mem_triangleCrossings e f g y).mpr hy)
  have hz' := (P1.mem_triangleCrossings_iff hef' heg' hfg' z).mp
    ((F1.mem_triangleCrossings e f g z).mpr hz)
  have hmem : ∀ {i j k : ZMod n} (_ : k ∈ ({i, j} : Finset (ZMod n))), k = i ∨ k = j := by
    intro i j k hk
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hk
  rcases hy' with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl
  · exact absurd rfl hyz
  · -- `x_ef`, `x_eg`: shared edge `e`
    rcases hmem hℓy with h | h
    · subst h; exact h1
    · exfalso
      rcases hmem (h ▸ hℓz : f ∈ ({e, g} : Finset (ZMod n))) with h' | h'
      · exact hef h'.symm
      · exact hfg h'
  · -- `x_ef`, `x_fg`: shared edge `f`
    rcases hmem hℓy with h | h
    · exfalso
      rcases hmem (h ▸ hℓz : e ∈ ({f, g} : Finset (ZMod n))) with h' | h'
      · exact hef h'
      · exact heg h'
    · subst h; exact h2
  · -- `x_eg`, `x_ef`: shared edge `e`
    rcases hmem hℓy with h | h
    · subst h; exact GT_adjacent_symm h1
    · exfalso
      rcases hmem (h ▸ hℓz : g ∈ ({e, f} : Finset (ZMod n))) with h' | h'
      · exact heg h'.symm
      · exact hfg h'.symm
  · exact absurd rfl hyz
  · -- `x_eg`, `x_fg`: shared edge `g`
    rcases hmem hℓy with h | h
    · exfalso
      rcases hmem (h ▸ hℓz : e ∈ ({f, g} : Finset (ZMod n))) with h' | h'
      · exact hef h'
      · exact heg h'
    · subst h; exact h3
  · -- `x_fg`, `x_ef`: shared edge `f`
    rcases hmem hℓy with h | h
    · subst h; exact GT_adjacent_symm h2
    · exfalso
      rcases hmem (h ▸ hℓz : g ∈ ({e, f} : Finset (ZMod n))) with h' | h'
      · exact heg h'.symm
      · exact hfg h'.symm
  · -- `x_fg`, `x_eg`: shared edge `g`
    rcases hmem hℓy with h | h
    · exfalso
      rcases hmem (h ▸ hℓz : f ∈ ({e, g} : Finset (ZMod n))) with h' | h'
      · exact hef h'.symm
      · exact hfg h'
    · subst h; exact GT_adjacent_symm h3
  · exact absurd rfl hyz

/-- The three triangle crossings. -/
theorem GT_tri_cases (t : E.Parameter) (hef : IsCrossing (E.curve t) {e, f})
    (heg : IsCrossing (E.curve t) {e, g}) (hfg : IsCrossing (E.curve t) {f, g})
    (y : Crossing (E.curve t)) (hy : y.val ∈ triangleSupports e f g) :
    y = xPair hef ∨ y = xPair heg ∨ y = xPair hfg :=
  (P1.mem_triangleCrossings_iff hef heg hfg y).mp ((F1.mem_triangleCrossings e f g y).mpr hy)

/-- **The twin masks** (R-PAR sharpened by full availability, `GenericTableData.mask_sharpening`): after
selecting the triangle crossing `x`, every outside survivor interlaces both other triangle crossings or
neither. -/
theorem GT_twins_of_mask (hG : GenericTableData E e f g δ) (t : E.Parameter) (ht : Punctured E δ t)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {x w m : Crossing (E.curve t)} (hx : x.val ∈ triangleSupports e f g)
    (hw : w.val ∈ triangleSupports e f g) (hm : m.val ∈ triangleSupports e f g)
    (hxw : x ≠ w) (hxm : x ≠ m) :
    ∀ y ∈ CV.U (geomAt E t ht.1) (GT_S Q x), y.val ∉ triangleSupports e f g →
      (GeometricInterlaces (geomAt E t ht.1) y w ↔ GeometricInterlaces (geomAt E t ht.1) y m) := by
  intro y hy hyT
  rw [GT_S_eq_insert] at hy
  obtain ⟨ha, hc, hb, -⟩ := hG.mask_sharpening t ht hef heg hfg Q hQ hfull
  have hint : ∀ z : Crossing (E.curve t), z.val ∈ triangleSupports e f g →
      (GeometricInterlaces (geomAt E t ht.1) y z ↔ z ∈ interlacedTriangle (geomAt E t ht.1) e f g y) := by
    intro z hz
    rw [G2.mem_interlacedTriangle_iff]
    exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  rw [hint w hw, hint m hm]
  have hw' := GT_tri_cases t hef heg hfg w hw
  have hm' := GT_tri_cases t hef heg hfg m hm
  rcases GT_tri_cases t hef heg hfg x hx with rfl | rfl | rfl
  · rcases ha y hy hyT with hM | hM
    · rw [hM]; simp
    · rw [hM]
      refine iff_of_true ?_ ?_
      · rcases hw' with h | h | h
        · exact absurd h.symm hxw
        · rw [h]; simp
        · rw [h]; simp
      · rcases hm' with h | h | h
        · exact absurd h.symm hxm
        · rw [h]; simp
        · rw [h]; simp
  · rcases hb y hy hyT with hM | hM
    · rw [hM]; simp
    · rw [hM]
      refine iff_of_true ?_ ?_
      · rcases hw' with h | h | h
        · rw [h]; simp
        · exact absurd h.symm hxw
        · rw [h]; simp
      · rcases hm' with h | h | h
        · rw [h]; simp
        · exact absurd h.symm hxm
        · rw [h]; simp
  · rcases hc y hy hyT with hM | hM
    · rw [hM]; simp
    · rw [hM]
      refine iff_of_true ?_ ?_
      · rcases hw' with h | h | h
        · rw [h]; simp
        · rw [h]; simp
        · exact absurd h.symm hxw
      · rcases hm' with h | h | h
        · rw [h]; simp
        · rw [h]; simp
        · exact absurd h.symm hxm

/-- The triangle is carried across the wall. -/
theorem GT_triangleCrossings_map {t t' : E.Parameter}
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s) :
    (triangleCrossings (E.curve t) e f g).map (crossingTransport hs).toEmbedding =
      triangleCrossings (E.curve t') e f g := by
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, F1.mem_triangleCrossings, F1.mem_triangleCrossings]
  rfl

/-- An outside independent support is one on the far side as well (R-LOC-2 (4) off `T`). -/
theorem GT_outsideSupports_transport (hL : LocalizationData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) :
    transportSupport hs Q ∈ outsideSupports (geomAt E t' ht'.1) e f g := by
  obtain ⟨hQi, hQd⟩ := (F1.mem_outsideSupports _ e f g Q).mp hQ
  rw [F1.mem_outsideSupports]
  refine ⟨?_, ?_⟩
  · rw [CV.mem_Ind_iff]
    intro a' ha' b' hb' hab
    obtain ⟨a, rfl⟩ := (crossingTransport hs).surjective a'
    obtain ⟨b, rfl⟩ := (crossingTransport hs).surjective b'
    rw [mem_transportSupport_iff] at ha' hb'
    have hab' : a ≠ b := fun h => hab (h ▸ rfl)
    have hnT : ¬ (a ≠ b ∧ a.val ∈ triangleSupports e f g ∧ b.val ∈ triangleSupports e f g) := by
      rintro ⟨-, haT, -⟩
      exact Finset.disjoint_left.mp hQd ha' ((F1.mem_triangleCrossings e f g a).mpr haT)
    rw [hL.interlace_toggle t t' ht ht' hop hs a b, L.xor_iff_of_not_right hnT]
    exact ((CV.mem_Ind_iff _ Q).mp hQi) a ha' b hb' hab'
  · rw [Finset.disjoint_left]
    intro a' ha' haT
    obtain ⟨a, rfl⟩ := (crossingTransport hs).surjective a'
    rw [mem_transportSupport_iff] at ha'
    exact Finset.disjoint_left.mp hQd ha' ((F1.mem_triangleCrossings e f g a).mpr
      ((F1.mem_triangleCrossings e f g (crossingTransport hs a)).mp haT))

/-- Full availability is carried across the wall (`F1.avail_same`). -/
theorem GT_fullAvail_transport (hL : LocalizationData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    FullAvail (geomAt E t' ht'.1) e f g (transportSupport hs Q) := by
  unfold FullAvail at hfull ⊢
  rw [show transportSupport hs Q = Q.map (crossingTransport hs).toEmbedding from rfl,
    F1.avail_same hL t t' ht ht' hop hs Q hQ, hfull, GT_triangleCrossings_map]

/-- **The endpoint configuration from the event data**: the wall clauses of R-LOC-2 (row 164), the
adjacency of the three bundle pairs on both sides, the twin masks (row 172-table), the turns, signs
and ray (the sign radius), for a triangle crossing `x` with the two others `w` (the other member of
the selected pair) and `m` (the centre of the path side `t`). -/
theorem GT_endpointData (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hIxw : ¬ GeometricInterlaces (geomAt E t ht.1) x w) (hIxm : GeometricInterlaces (geomAt E t ht.1) x m)
    (hIwm : GeometricInterlaces (geomAt E t ht.1) w m)
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    GT_Endpoint (geomAt E t ht.1) (geomAt E t' ht'.1) hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃ := by
  obtain ⟨hQi, hQd⟩ := (F1.mem_outsideSupports _ e f g Q).mp hQ
  obtain ⟨hef', heg', hfg'⟩ := hL.triangle_crossings t ht
  exact {
    hef := hef, heg := heg, hfg := hfg
    xT := hx, wT := hw, mT := hm
    tri_cases := fun y hy => GT_tri_cases t hef' heg' hfg' y hy |>.imp id (fun h => h) |> fun h => by
      -- `y ∈ {x_ef, x_eg, x_fg} = {x, w, m}` (the three are distinct triangle crossings)
      rcases GT_tri_cases t hef' heg' hfg' x hx with hx' | hx' | hx' <;>
      rcases GT_tri_cases t hef' heg' hfg' w hw with hw' | hw' | hw' <;>
      rcases GT_tri_cases t hef' heg' hfg' m hm with hm' | hm' | hm' <;>
      first
      | exact absurd (hx'.trans hw'.symm) hxw
      | exact absurd (hx'.trans hm'.symm) hxm
      | exact absurd (hw'.trans hm'.symm) hwm
      | (rcases h with h | h | h <;> first
          | exact Or.inl (h.trans hx'.symm)
          | exact Or.inr (Or.inl (h.trans hw'.symm))
          | exact Or.inr (Or.inr (h.trans hm'.symm)))
    xw := hxw, xm := hxm, wm := hwm
    x1 := x1, m1 := m1, x2 := x2, w2 := w2, w3 := w3, m3 := m3
    l12 := l12, l13 := l13, l23 := l23
    Q_ind := hQi
    Q_out := fun q hq hqT => Finset.disjoint_left.mp hQd hq ((F1.mem_triangleCrossings e f g q).mpr hqT)
    Q_avail := fun q hq y hy => by
      have hyA : y ∈ avail (geomAt E t ht.1) e f g Q := by
        rw [hfull]; exact (F1.mem_triangleCrossings e f g y).mpr hy
      exact ((F1.mem_avail _ e f g Q y).mp hyA).2 q hq
    hxw := hIxw, hxm := hIxm, hwm := hIwm
    gauss := hL.gauss_words t t' ht ht' hop hs
    toggle := fun y z hyz => by
      rw [hL.interlace_toggle t t' ht ht' hop hs y z, L.xor_iff_of_not_right (fun h => hyz ⟨h.2.1, h.2.2⟩)]
    compl := fun y z hy hz hyz => hL.complement_on_triangle t t' ht ht' hop hs y z hy hz hyz
    adj1 := GT_adjacent_of_shared hL hef heg hfg t ht hx hm hxm x1 m1
    adj2 := GT_adjacent_of_shared hL hef heg hfg t ht hx hw hxw x2 w2
    adj3 := GT_adjacent_of_shared hL hef heg hfg t ht hw hm hwm w3 m3
    adj1' := GT_adjacent_of_shared hL hef heg hfg t' ht' (y := crossingTransport hs x)
      (z := crossingTransport hs m) hx hm ((crossingTransport hs).injective.ne hxm) x1 m1
    adj2' := GT_adjacent_of_shared hL hef heg hfg t' ht' (y := crossingTransport hs x)
      (z := crossingTransport hs w) hx hw ((crossingTransport hs).injective.ne hxw) x2 w2
    adj3' := GT_adjacent_of_shared hL hef heg hfg t' ht' (y := crossingTransport hs w)
      (z := crossingTransport hs m) hw hm ((crossingTransport hs).injective.ne hwm) w3 m3
    turn_eq := hR.turn_eq t t' ht ht'
    sign_eq := hR.sign_eq t t' ht ht'
    ray := by
      obtain ⟨r, hr⟩ := hR.ray
      refine ⟨r, fun h => ⟨(hr t ht h).1, ?_⟩⟩
      rw [(hr t' ht' h).2, (hr t ht h).2]
    twins := GT_twins_of_mask hG t ht hef' heg' hfg' hQ hfull hx hw hm hxw hxm
    sgn := hsgn }

/-- **The endpoint transport, `t` the two-edge side.** -/
theorem GT_endpoint_transport_path (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hIxw : ¬ GeometricInterlaces (geomAt E t ht.1) x w) (hIxm : GeometricInterlaces (geomAt E t ht.1) x m)
    (hIwm : GeometricInterlaces (geomAt E t ht.1) w m)
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {x}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {x})) :=
  GT_endpoint_rowTerm_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1)
    (GT_endpointData hL hG hR hef heg hfg ht ht' hop hs hQ hfull x w m ℓ₁ ℓ₂ ℓ₃ hx hw hm hxw hxm hwm
      x1 m1 x2 w2 w3 m3 l12 l13 l23 hIxw hIxm hIwm hsgn)

omit [NeZero n] in
theorem GT_transportSupport_S {P Q' : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q' s)
    (Q : Finset (Crossing P)) (x : Crossing P) :
    transportSupport hs (Q ∪ {x}) = transportSupport hs Q ∪ {crossingTransport hs x} := by
  rw [AV_transportSupport_union]
  rfl

/-- **The endpoint transport, `t` the one-edge side**: apply the two-edge case to the pair `(t', t)`. -/
theorem GT_endpoint_transport_edge (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hIxw : GeometricInterlaces (geomAt E t ht.1) x w) (hIxm : ¬ GeometricInterlaces (geomAt E t ht.1) x m)
    (hIwm : ¬ GeometricInterlaces (geomAt E t ht.1) w m)
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {x}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {x})) := by
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hsgn' : crossingSign (E.curve t') ℓ₂ ℓ₃ = crossingSign (E.curve t') ℓ₁ ℓ₃ := by
    rw [hR.sign_eq t t' ht ht' ℓ₂ ℓ₃ (GT_isCrossing_of_mem w2 w3 l23),
      hR.sign_eq t t' ht ht' ℓ₁ ℓ₃ (GT_isCrossing_of_mem m1 m3 l13), hsgn]
  have h := GT_endpoint_transport_path hn hL hG hR hef heg hfg ht' ht hop' hs' hQ' hfull'
    (crossingTransport hs x) (crossingTransport hs w) (crossingTransport hs m) ℓ₁ ℓ₂ ℓ₃ hx hw hm
    ((crossingTransport hs).injective.ne hxw) ((crossingTransport hs).injective.ne hxm)
    ((crossingTransport hs).injective.ne hwm) x1 m1 x2 w2 w3 m3 l12 l13 l23
    (by rw [hL.complement_on_triangle t t' ht ht' hop hs x w hx hw hxw]; exact fun h => h hIxw)
    (by rw [hL.complement_on_triangle t t' ht ht' hop hs x m hx hm hxm]; exact hIxm)
    (by rw [hL.complement_on_triangle t t' ht ht' hop hs w m hw hm hwm]; exact hIwm) hsgn'
  rw [← GT_transportSupport_S hs Q x, EXT_transportSupport_symm hs (Q ∪ {x})] at h
  exact h.symm

/-- **The endpoint transport** for a row `x` of the selected pair `{x, w}`, `m` the third crossing: the
local graph at `t` is the path with centre `m` or the single edge `x–w`. -/
theorem GT_endpoint_transport (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hloc : (¬ GeometricInterlaces (geomAt E t ht.1) x w ∧ GeometricInterlaces (geomAt E t ht.1) x m ∧
        GeometricInterlaces (geomAt E t ht.1) w m) ∨
      (GeometricInterlaces (geomAt E t ht.1) x w ∧ ¬ GeometricInterlaces (geomAt E t ht.1) x m ∧
        ¬ GeometricInterlaces (geomAt E t ht.1) w m))
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {x}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {x})) := by
  rcases hloc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact GT_endpoint_transport_path hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull x w m ℓ₁ ℓ₂ ℓ₃
      hx hw hm hxw hxm hwm x1 m1 x2 w2 w3 m3 l12 l13 l23 h1 h2 h3 hsgn
  · exact GT_endpoint_transport_edge hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull x w m ℓ₁ ℓ₂ ℓ₃
      hx hw hm hxw hxm hwm x1 m1 x2 w2 w3 m3 l12 l13 l23 h1 h2 h3 hsgn

end GTEvent

end GT

section GT

open SM.Carrier SM.Link

/-! ### The six endpoint rows: the two fields `endpoint_rows_canonical`, `endpoint_rows_relabelled` -/

section GTFields

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- Nonalternating, `s_a = −s_b` (pair `ab` selected) forces `s_b = s_c`. -/
theorem GT_signs_of_selectedAB : ∀ sa sb sc : SignType, sa ≠ 0 → sb ≠ 0 → sc ≠ 0 →
    ¬ IsAlternating sa sb sc → SelectedAB sa sb → sb = sc := by
  intro sa sb sc
  cases sa <;> cases sb <;> cases sc <;> decide

/-- Nonalternating, `s_b = −s_c` (pair `bc` selected) forces `s_a = s_b`. -/
theorem GT_signs_of_selectedBC : ∀ sa sb sc : SignType, sa ≠ 0 → sb ≠ 0 → sc ≠ 0 →
    ¬ IsAlternating sa sb sc → SelectedBC sb sc → sa = sb := by
  intro sa sb sc
  cases sa <;> cases sb <;> cases sc <;> decide

omit [NeZero n] in
theorem GT_mem_pair_l {i j : ZMod n} : i ∈ ({i, j} : Finset (ZMod n)) := mem_pair_left i j
omit [NeZero n] in
theorem GT_mem_pair_r {i j : ZMod n} : j ∈ ({i, j} : Finset (ZMod n)) := mem_pair_right i j

omit [NeZero n] in
theorem GT_tri_ef {e f g : ZMod n} : ({e, f} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  simp [triangleSupports]
omit [NeZero n] in
theorem GT_tri_eg {e f g : ZMod n} : ({e, g} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  simp [triangleSupports]
omit [NeZero n] in
theorem GT_tri_fg {e f g : ZMod n} : ({f, g} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  simp [triangleSupports]

omit [NeZero n] in
/-- In the generic orbit not all three local edges are present. -/
theorem GT_not_all_edges {P : LabelledTuple n} (hP : CrossingGeometry P)
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hgen : ¬ ExtremeLocal hP hef heg hfg) (hAB : EdgeAB hP hef heg) (hBC : EdgeBC hP heg hfg) :
    ¬ EdgeAC hP hef hfg :=
  fun hAC => hgen (Or.inl ⟨hAB, hAC, hBC⟩)

omit [NeZero n] in
theorem GT_not_all_edges' {P : LabelledTuple n} (hP : CrossingGeometry P)
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hgen : ¬ ExtremeLocal hP hef heg hfg) (hAC : EdgeAC hP hef hfg) (hBC : EdgeBC hP heg hfg) :
    ¬ EdgeAB hP hef heg :=
  fun hAB => hgen (Or.inl ⟨hAB, hAC, hBC⟩)

omit [NeZero n] in
theorem GT_not_all_edges'' {P : LabelledTuple n} (hP : CrossingGeometry P)
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hgen : ¬ ExtremeLocal hP hef heg hfg) (hAB : EdgeAB hP hef heg) (hAC : EdgeAC hP hef hfg) :
    ¬ EdgeBC hP heg hfg :=
  fun hBC => hgen (Or.inl ⟨hAB, hAC, hBC⟩)

/-- **Row `a` in the branch `ac`** (`x = a`, `w = c`, `m = b`; `ℓ₁ = e`, `ℓ₂ = f`, `ℓ₃ = g`). -/
theorem GT_row_a_of_AC (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAC (geomAt E t ht.1) hef' hfg') ∨
      (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg'))
    (hsbc : strandSign (E.curve t) e g = strandSign (E.curve t) f g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hef') (xPair hfg') (xPair heg') e f g GT_tri_ef GT_tri_fg GT_tri_eg
    (P1.xPair_ef_ne_fg hef' heg' hfg') (P1.xPair_ef_ne_eg hef' heg' hfg')
    (P1.xPair_eg_ne_fg hef' heg' hfg').symm
    GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r hef heg hfg ?_ ?_
  · rcases hloc with ⟨hAB, hBC, hAC⟩ | ⟨hAC, hAB, hBC⟩
    · exact Or.inl ⟨hAC, hAB, geometricInterlaces_symm _ hBC⟩
    · exact Or.inr ⟨hAC, hAB, fun h => hBC (geometricInterlaces_symm _ h)⟩
  · exact hsbc.symm

/-- **Row `c` in the branch `ac`** (`x = c`, `w = a`, `m = b`; `ℓ₁ = g`, `ℓ₂ = f`, `ℓ₃ = e`). -/
theorem GT_row_c_of_AC (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAC (geomAt E t ht.1) hef' hfg') ∨
      (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg'))
    (hsab : strandSign (E.curve t) e f = strandSign (E.curve t) e g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hfg') (xPair hef') (xPair heg') g f e GT_tri_fg GT_tri_ef GT_tri_eg
    (P1.xPair_ef_ne_fg hef' heg' hfg').symm (P1.xPair_eg_ne_fg hef' heg' hfg').symm
    (P1.xPair_ef_ne_eg hef' heg' hfg')
    GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l
    hfg.symm heg.symm hef.symm ?_ ?_
  · rcases hloc with ⟨hAB, hBC, hAC⟩ | ⟨hAC, hAB, hBC⟩
    · exact Or.inl ⟨fun h => hAC (geometricInterlaces_symm _ h), geometricInterlaces_symm _ hBC, hAB⟩
    · exact Or.inr ⟨geometricInterlaces_symm _ hAC, fun h => hBC (geometricInterlaces_symm _ h), hAB⟩
  · -- `crossingSign f e = crossingSign g e ⟸ s_a = s_b`
    show crossingSign (E.curve t) f e = crossingSign (E.curve t) g e
    rw [crossingSign_swap (E.curve t) e f, crossingSign_swap (E.curve t) e g]
    exact congrArg Neg.neg hsab

/-- **Row `a` in the branch `ab`** (`x = a`, `w = b`, `m = c`; `ℓ₁ = f`, `ℓ₂ = e`, `ℓ₃ = g`). -/
theorem GT_row_a_of_AB (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAB (geomAt E t ht.1) hef' heg') ∨
      (EdgeAB (geomAt E t ht.1) hef' heg' ∧ ¬ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg'))
    (hsbc : strandSign (E.curve t) e g = strandSign (E.curve t) f g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hef') (xPair heg') (xPair hfg') f e g GT_tri_ef GT_tri_eg GT_tri_fg
    (P1.xPair_ef_ne_eg hef' heg' hfg') (P1.xPair_ef_ne_fg hef' heg' hfg')
    (P1.xPair_eg_ne_fg hef' heg' hfg')
    GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r
    hef.symm hfg heg ?_ ?_
  · rcases hloc with ⟨hAC, hBC, hAB⟩ | ⟨hAB, hAC, hBC⟩
    · exact Or.inl ⟨hAB, hAC, hBC⟩
    · exact Or.inr ⟨hAB, hAC, hBC⟩
  · exact hsbc

/-- **Row `b` in the branch `ab`** (`x = b`, `w = a`, `m = c`; `ℓ₁ = g`, `ℓ₂ = e`, `ℓ₃ = f`). -/
theorem GT_row_b_of_AB (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAB (geomAt E t ht.1) hef' heg') ∨
      (EdgeAB (geomAt E t ht.1) hef' heg' ∧ ¬ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg'))
    (hsab : strandSign (E.curve t) e f = -strandSign (E.curve t) e g)
    (hsbc : strandSign (E.curve t) e g = strandSign (E.curve t) f g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair heg') (xPair hef') (xPair hfg') g e f GT_tri_eg GT_tri_ef GT_tri_fg
    (P1.xPair_ef_ne_eg hef' heg' hfg').symm (P1.xPair_eg_ne_fg hef' heg' hfg')
    (P1.xPair_ef_ne_fg hef' heg' hfg')
    GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_l
    heg.symm hfg.symm hef ?_ ?_
  · rcases hloc with ⟨hAC, hBC, hAB⟩ | ⟨hAB, hAC, hBC⟩
    · exact Or.inl ⟨fun h => hAB (geometricInterlaces_symm _ h), hBC, hAC⟩
    · exact Or.inr ⟨geometricInterlaces_symm _ hAB, hBC, hAC⟩
  · -- `crossingSign e f = crossingSign g f ⟸ s_a = −s_c`
    show crossingSign (E.curve t) e f = crossingSign (E.curve t) g f
    rw [crossingSign_swap (E.curve t) f g]
    show strandSign (E.curve t) e f = -strandSign (E.curve t) f g
    rw [← hsbc]; exact hsab

/-- **Row `b` in the branch `bc`** (`x = b`, `w = c`, `m = a`; `ℓ₁ = e`, `ℓ₂ = g`, `ℓ₃ = f`). -/
theorem GT_row_b_of_BC (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg') ∨
      (EdgeBC (geomAt E t ht.1) heg' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeAC (geomAt E t ht.1) hef' hfg'))
    (hsab : strandSign (E.curve t) e f = strandSign (E.curve t) e g)
    (hsbc : strandSign (E.curve t) e g = -strandSign (E.curve t) f g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair heg') (xPair hfg') (xPair hef') e g f GT_tri_eg GT_tri_fg GT_tri_ef
    (P1.xPair_eg_ne_fg hef' heg' hfg') (P1.xPair_ef_ne_eg hef' heg' hfg').symm
    (P1.xPair_ef_ne_fg hef' heg' hfg').symm
    GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r
    heg hef hfg.symm ?_ ?_
  · rcases hloc with ⟨hAB, hAC, hBC⟩ | ⟨hBC, hAB, hAC⟩
    · exact Or.inl ⟨hBC, geometricInterlaces_symm _ hAB, geometricInterlaces_symm _ hAC⟩
    · exact Or.inr ⟨hBC, fun h => hAB (geometricInterlaces_symm _ h),
        fun h => hAC (geometricInterlaces_symm _ h)⟩
  · -- `crossingSign g f = crossingSign e f ⟸ s_a = −s_c`
    show crossingSign (E.curve t) g f = crossingSign (E.curve t) e f
    rw [crossingSign_swap (E.curve t) f g]
    show -strandSign (E.curve t) f g = strandSign (E.curve t) e f
    rw [hsab, hsbc]

/-- **Row `c` in the branch `bc`** (`x = c`, `w = b`, `m = a`; `ℓ₁ = f`, `ℓ₂ = g`, `ℓ₃ = e`). -/
theorem GT_row_c_of_BC (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg') ∨
      (EdgeBC (geomAt E t ht.1) heg' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeAC (geomAt E t ht.1) hef' hfg'))
    (hsab : strandSign (E.curve t) e f = strandSign (E.curve t) e g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hfg') (xPair heg') (xPair hef') f g e GT_tri_fg GT_tri_eg GT_tri_ef
    (P1.xPair_eg_ne_fg hef' heg' hfg').symm (P1.xPair_ef_ne_fg hef' heg' hfg').symm
    (P1.xPair_ef_ne_eg hef' heg' hfg').symm
    GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l
    hfg hef.symm heg.symm ?_ ?_
  · rcases hloc with ⟨hAB, hAC, hBC⟩ | ⟨hBC, hAB, hAC⟩
    · exact Or.inl ⟨fun h => hBC (geometricInterlaces_symm _ h), geometricInterlaces_symm _ hAC,
        geometricInterlaces_symm _ hAB⟩
    · exact Or.inr ⟨geometricInterlaces_symm _ hBC, fun h => hAC (geometricInterlaces_symm _ h),
        fun h => hAB (geometricInterlaces_symm _ h)⟩
  · -- `crossingSign g e = crossingSign f e ⟸ s_a = s_b`
    show crossingSign (E.curve t) g e = crossingSign (E.curve t) f e
    rw [crossingSign_swap (E.curve t) e g, crossingSign_swap (E.curve t) e f]
    exact congrArg Neg.neg hsab.symm

/-- **Field `endpoint_rows_canonical` of `GenericTransportData`** (R_GENERIC_COMMON_TRANSPORT_PROOF.md
(2), `T_P(a) = T_E(a)`, `T_P(c) = T_E(c)` in the canonical branch `s_a = s_b = s_c`). -/
theorem GT_173_endpoint_rows_canonical (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'})) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen hsab hsbc Q hQ hfull
  have hsel : SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) :=
    hsab.trans hsbc
  have hloc := ((hG.selected_is_graph_selected t ht hef' heg' hfg' hgen).1).mp hsel
  have hloc' : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
      ¬ EdgeAC (geomAt E t ht.1) hef' hfg') ∨
      (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg') := by
    rcases hloc with ⟨hAB, hBC⟩ | h
    · exact Or.inl ⟨hAB, hBC, GT_not_all_edges _ hgen hAB hBC⟩
    · exact Or.inr h
  exact ⟨GT_row_a_of_AC hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsbc hQ hfull,
    GT_row_c_of_AC hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsab hQ hfull⟩

/-- **Field `endpoint_rows_relabelled` of `GenericTransportData`** ("Every generic branch can be put in
this form by relabelling …"): the endpoint rows of the branches `ab` (rows `a, b`) and `bc` (rows `b, c`). -/
theorem GT_173_endpoint_rows_relabelled (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'}))) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'}))) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen Q hQ hfull
  obtain ⟨h1, h2, h3, -⟩ := hG.nonzero t ht
  have hna := (hG.generic_iff_nonalternating t ht hef' heg' hfg').mp hgen
  have hz1 : strandSign (E.curve t) e f ≠ 0 := sign_ne_zero.mpr h1
  have hz2 : strandSign (E.curve t) e g ≠ 0 := sign_ne_zero.mpr h2
  have hz3 : strandSign (E.curve t) f g ≠ 0 := sign_ne_zero.mpr h3
  have hsel := hG.selected_is_graph_selected t ht hef' heg' hfg' hgen
  constructor
  · intro hAB
    have hsbc := GT_signs_of_selectedAB _ _ _ hz1 hz2 hz3 hna hAB
    have hloc := (hsel.2.1).mp hAB
    have hloc' : (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAB (geomAt E t ht.1) hef' heg') ∨
        (EdgeAB (geomAt E t ht.1) hef' heg' ∧ ¬ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
          ¬ EdgeBC (geomAt E t ht.1) heg' hfg') := by
      rcases hloc with ⟨hAC, hBC⟩ | h
      · exact Or.inl ⟨hAC, hBC, GT_not_all_edges' _ hgen hAC hBC⟩
      · exact Or.inr h
    exact ⟨GT_row_a_of_AB hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsbc hQ hfull,
      GT_row_b_of_AB hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hAB hsbc hQ hfull⟩
  · intro hBC
    have hsab := GT_signs_of_selectedBC _ _ _ hz1 hz2 hz3 hna hBC
    have hloc := (hsel.2.2).mp hBC
    have hloc' : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg') ∨
        (EdgeBC (geomAt E t ht.1) heg' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
          ¬ EdgeAC (geomAt E t ht.1) hef' hfg') := by
      rcases hloc with ⟨hAB, hAC⟩ | h
      · exact Or.inl ⟨hAB, hAC, GT_not_all_edges'' _ hgen hAB hAC⟩
      · exact Or.inr h
    exact ⟨GT_row_b_of_BC hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsab hBC hQ hfull,
      GT_row_c_of_BC hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsab hQ hfull⟩

end GTFields

end GT

section GT

open SM.Carrier SM.Link

/-! ### The empty row (R_GENERIC_COMMON_TRANSPORT_PROOF.md §1) and the missing fact G11

§1 transports the empty row carrier by carrier. Every carrier of `Q` has a copy across the wall
(`GT_carrierEquiv`, all marks are good since no triangle visit is a corner), with the same corner list,
turns, rotation and retained crossings; by cor:groupedknot (B) the grouped polynomial `P_{Q,L}` of every
carrier is the HOMFLY polynomial of its positive lift (`GT_groupedPoly_eq_homfly`). For a
triangle-disjoint carrier the two lifts are record-isomorphic (`EXT_homfly_wall`). For the one
distinguished carrier bearing the three local crossings the two lifts differ by the printed
"ordinary oriented Reidemeister III move" — the fact **G11** below, which the accepted library does not
provide: `SM.homfly_reidemeister_III` needs a geometric disc-local `SM.Link.RIII` site, and no
`RIIIData` is constructed anywhere in `work/lean`; the record-level replacement of CV:ax:gausscode
(`CV.gausscode_polynomial`) covers record *isomorphisms* only. `GT_G11` states exactly the polynomial
consequence the printed proof invokes ("Apply the corresponding ordinary oriented Reidemeister III
move to `D_P` … `ax:homfly` gives `P(D') = P(D_P)` … `ax:gausscode` identifies their oriented
links"), in the form in which the empty row consumes it. -/

/-- **G11 — HOMFLY invariance of the grouped diagram across the RIII wall.** Two carriers on the two
sides of a simple RIII wall in the generic orbit (`¬ IsAlternating`: the divide over-order of the
three local strands is transitive), with corresponding retained crossings, both retaining the three
triangle crossings, whose six triangle visits are exchanged pairwise on their edges
(`ExactTriangleVisitOrders`) and whose divide signs are carried, have positive lifts with the same
HOMFLY polynomial. This is an actual Reidemeister III move between the two lifts followed by a record
isomorphism; it is NOT provable from the accepted library (see the section docstring). -/
def GT_G11 : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) {P P' : LabelledTuple n}
    (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n),
    e ≠ f → e ≠ g → f ≠ g →
    ExactTriangleVisitOrders P P' e f g hs →
    (∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j))) →
    ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g) →
    ∀ {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
      (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
      (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T'),
      geoCarrierCrossings hG'.cg T' q' =
        (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding →
      triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q →
      homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q)

section GTEmpty

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

omit [NeZero n] in
/-- Two distinct triangle crossings share a label. -/
theorem GT_shared_label {P : LabelledTuple n} {y z : Crossing P} (hy : y.val ∈ triangleSupports e f g) (hz : z.val ∈ triangleSupports e f g)
    (hyz : y ≠ z) : ∃ ℓ : ZMod n, ℓ ∈ y.val ∧ ℓ ∈ z.val := by
  have hmem : ∀ {s : Finset (ZMod n)}, s ∈ triangleSupports e f g → s = {e, f} ∨ s = {e, g} ∨ s = {f, g} := by
    intro s hs
    simpa [triangleSupports] using hs
  have hne : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases hmem hy with h1 | h1 | h1 <;> rcases hmem hz with h2 | h2 | h2 <;>
    first
    | exact absurd (h1.trans h2.symm) hne
    | exact ⟨e, by rw [h1]; exact mem_pair_left _ _, by rw [h2]; exact mem_pair_left _ _⟩
    | exact ⟨f, by rw [h1]; exact mem_pair_right _ _, by rw [h2]; exact mem_pair_left _ _⟩
    | exact ⟨g, by rw [h1]; exact mem_pair_right _ _, by rw [h2]; exact mem_pair_right _ _⟩
    | exact ⟨f, by rw [h1]; exact mem_pair_left _ _, by rw [h2]; exact mem_pair_right _ _⟩

/-- The wall data of the empty row `S = Q` (no triangle crossing is selected). -/
theorem GT_empty_wall (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) :
    GT_Wall (geomAt E t ht.1) (geomAt E t' ht'.1) hs (triangleCrossings (E.curve t) e f g) Q where
  indep := CV.geoIndependent_of_mem_Ind _ ((F1.mem_outsideSupports _ e f g Q).mp hQ).1
  indep' := CV.geoIndependent_of_mem_Ind _
    ((F1.mem_outsideSupports _ e f g _).mp (GT_outsideSupports_transport hL ht ht' hop hs hQ)).1
  key_lt v w hvw := AV_key_lt_of_gauss _ _ hs hef heg hfg (hL.gauss_words t t' ht ht' hop hs) v w hvw
  corners_apart v w hrev := by
    rintro ⟨hvQ, -⟩
    exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hvQ hrev.1
  turn_eq := hR.turn_eq t t' ht ht'
  sign_eq := hR.sign_eq t t' ht ht'
  ray := by
    obtain ⟨r, hr⟩ := hR.ray
    refine ⟨r, fun h => ⟨(hr t ht h).1, ?_⟩⟩
    rw [(hr t' ht' h).2, (hr t ht h).2]

/-- In the empty row every visit of an unselected crossing is good (no triangle visit is a corner). -/
theorem GT_empty_good {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (v : Visit (E.curve t)) (_ : v.1 ∉ Q) :
    GT_Good (triangleCrossings (E.curve t) e f g) Q (Sum.inr v) := by
  intro v' hv' w hrev hw
  have hwQ : w.1 ∈ Q := hw
  exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hwQ hrev.2.1

/-- At full availability the three triangle crossings are undominated by `Q`. -/
theorem GT_empty_tri_mem_U {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {y : Crossing (E.curve t)} (hy : y.val ∈ triangleSupports e f g) : y ∈ CV.U (geomAt E t ht.1) Q := by
  have hyA : y ∈ avail (geomAt E t ht.1) e f g Q := by
    rw [hfull]; exact (F1.mem_triangleCrossings e f g y).mpr hy
  rw [CV.mem_U_iff]
  refine ⟨fun h => Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 h
    ((F1.mem_triangleCrossings e f g y).mpr hy), fun q hq h => ?_⟩
  exact ((F1.mem_avail _ e f g Q y).mp hyA).2 q hq (geometricInterlaces_symm _ h)

/-- **A carrier of the empty row owning one triangle visit retains all three triangle crossings**:
the two visits of an undominated crossing lie on one carrier, and the adjacent unselected visits of
two triangle crossings on their shared edge lie on one carrier. -/
theorem GT_empty_tri_subset (hL : LocalizationData E e f g δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (q : GeoComponent (geomAt E t ht.1) Q) {v : Visit (E.curve t)}
    (hv : v.1.val ∈ triangleSupports e f g) (hvq : geoOwner (geomAt E t ht.1) Q (Sum.inr v) = q) :
    triangleCrossings (E.curve t) e f g ⊆ geoCarrierCrossings (geomAt E t ht.1) Q q := by
  have hQi := ((F1.mem_outsideSupports _ e f g Q).mp hQ).1
  have hall : ∀ {y : Crossing (E.curve t)}, y.val ∈ triangleSupports e f g →
      ∀ u : Visit (E.curve t), u.1 = y → geoOwner (geomAt E t ht.1) Q (Sum.inr u) = q →
      y ∈ geoCarrierCrossings (geomAt E t ht.1) Q q := by
    intro y hy u hu huq
    rw [mem_geoCarrierCrossings]
    refine ⟨((CV.mem_U_iff _ Q y).mp (GT_empty_tri_mem_U ht hQ hfull hy)).1, fun u' hu' => ?_⟩
    rw [CV.owner_eq_of_mem_U _ hQi (GT_empty_tri_mem_U ht hQ hfull hy) u' u hu' hu]
    exact huq
  intro z hz
  have hzT := (F1.mem_triangleCrossings e f g z).mp hz
  by_cases hzv : z = v.1
  · exact hall hzT v hzv.symm hvq
  · obtain ⟨ℓ, hℓv, hℓz⟩ := GT_shared_label hv hzT (Ne.symm hzv)
    have hadj := GT_adjacent_of_shared hL hef heg hfg t ht hv hzT (Ne.symm hzv) hℓv hℓz
    have hzQ : z ∉ Q := ((CV.mem_U_iff _ Q z).mp (GT_empty_tri_mem_U ht hQ hfull hzT)).1
    have hvQ : v.1 ∉ Q := ((CV.mem_U_iff _ Q v.1).mp (GT_empty_tri_mem_U ht hQ hfull hv)).1
    have h1 := GT_owner_eq_of_adjacent _ Q hadj rfl hvQ hzQ
    have h2 : geoOwner (geomAt E t ht.1) Q (Sum.inr (visitOn v.1 ℓ hℓv)) = q := by
      rw [CV.owner_eq_of_mem_U _ hQi (GT_empty_tri_mem_U ht hQ hfull hv) (visitOn v.1 ℓ hℓv) v rfl rfl]
      exact hvq
    exact hall hzT (visitOn z ℓ hℓz) rfl (h1.symm.trans h2)

/-- **The grouped polynomial of every carrier of the empty row is carried**: triangle-disjoint carriers
by the record isomorphism `EXT_homfly_wall`, the distinguished carrier by G11. -/
theorem GT_empty_groupedPoly_eq (hG11 : GT_G11) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hgen : ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (q : GeoComponent (geomAt E t ht.1) Q) :
    CV.groupedPoly hn (genericAt E t' ht'.1) hQi' (GT_carrierEquiv (GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ) q) =
      CV.groupedPoly hn (genericAt E t ht.1) hQi q := by
  set W := GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ
  have hX := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  by_cases htri : ∃ v : Visit (E.curve t), v.1.val ∈ triangleSupports e f g ∧
      geoOwner (geomAt E t ht.1) Q (Sum.inr v) = q
  · -- the distinguished carrier: G11
    obtain ⟨v, hv, hvq⟩ := htri
    exact hG11 n hn (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
      (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hs e f g hef heg hfg
      (hL.gauss_words t t' ht ht' hop hs) hdet
      ((hGT.generic_iff_nonalternating t ht hef' heg' hfg').mp hgen) _ _ q _ hX
      (GT_empty_tri_subset hL hef heg hfg ht hQ hfull q hv hvq)
  · -- a triangle-disjoint carrier: the record isomorphism
    have htri' : ∀ v : Visit (E.curve t), v.1.val ∈ triangleSupports e f g →
        geoOwner (geomAt E t ht.1) Q (Sum.inr v) ≠ q := fun v hv hq => htri ⟨v, hv, hq⟩
    refine EXT_homfly_wall hn _ _ hs _ _ q _ hX ?_ ?_
    · intro v w hv hw
      have hvT : v.1.val ∉ triangleSupports e f g := fun h =>
        htri' v h (((mem_geoCarrierCrossings _ Q q v.1).mp hv).2 v rfl)
      exact W.key_lt v w (GT_not_rev_of_not_mem_left
        (fun h => hvT ((F1.mem_triangleCrossings e f g v.1).mp h)))
    · intro v _
      exact hdet _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property)

/-- **Field `empty_row` of `GenericTransportData`, modulo G11** (R_GENERIC_COMMON_TRANSPORT_PROOF.md
§1: "`T_P(empty) = T_E(empty)`"). -/
theorem GT_173_empty_row (hG11 : GT_G11) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q = rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen Q hQ hfull
  have W := GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ
  have hQi : Q ∈ CV.Ind (geomAt E t ht.1) := ((F1.mem_outsideSupports _ e f g Q).mp hQ).1
  have hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) :=
    ((F1.mem_outsideSupports _ e f g _).mp (GT_outsideSupports_transport hL ht ht' hop hs hQ)).1
  refine AV_rowTerm_eq_of_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hQi hQi'
    ⟨GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W, GT_carrierEquiv W, fun q =>
      ⟨GT_weight_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W q,
        GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hQi hQi' q, ?_, ?_, ?_⟩⟩
  · rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q, Finset.card_map]
  · exact GT_empty_groupedPoly_eq hG11 hn hL hGT hR hef heg hfg ht ht' hop hs hef' heg' hfg' hgen hQ hfull
      hQi hQi' q
  · unfold CV.Omega1 CV.slot
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q, Finset.card_map,
      GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hQi hQi' q,
      GT_empty_groupedPoly_eq hG11 hn hL hGT hR hef heg hfg ht ht' hop hs hef' heg' hfg' hgen hQ hfull hQi hQi' q]

end GTEmpty

/-! ### The bundle and the row, modulo G11 -/

/-- **`GenericTransportData` from the accepted rows 164, 172-table, the sign radius, and G11.** -/
theorem GT_genericTransportData (hG11 : GT_G11) (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : GenericTransportData hn E e f g δ where
  canonical_branch := PRE_173_canonical_branch hGT
  empty_row := GT_173_empty_row hG11 hn hL hGT hR hef heg hfg
  endpoint_rows_canonical := GT_173_endpoint_rows_canonical hn hL hGT hR hef heg hfg
  endpoint_rows_relabelled := GT_173_endpoint_rows_relabelled hn hL hGT hR hef heg hfg

/-- **Row 173, R:generic_transport, modulo G11**: the row theorem with the radius
`min δ_L (min δ_G δ_R)` of the accepted `localization`, `generic_table` and the sign radius. -/
theorem GT_generic_transport_of_G11 (hG11 : GT_G11) (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ := by
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δG δR), lt_min hδL (lt_min hδG hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δG δR)) hL
  have hGT' := SEL_genericTableData_mono ((min_le_right δL (min δG δR)).trans (min_le_left δG δR)) hGT
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δG δR)).trans (min_le_right δG δR)) hR
  exact GT_genericTransportData hG11 hn hL' hGT' hR' hef heg hfg

end GT

end RProof
