import RProof.X1Rows
import CV.PieceHomflyTransport

/-! # R lane, X₁ rows — wave 2 portable module (2026-09-14)

Built by the wave-2 assembler from the unit files `work/drafts/rlane2/W2_EXT.lean` (row 168) and
`W2_AV.lean` (row 170), reports `W2_EXT_REPORT.md`, `W2_AV_REPORT.md`, `ASSEMBLY2_REPORT.md`. This module is
`import RProof.X1Rows` (the wave-1 portable module: bundles, auxiliaries, `CV.hyp_R`, the proved row 172,
the `PRE_`/`SEL_`/`A2_` lemmas) plus ONLY the new wave-2 material, in this order:

* `section EXT` — the 96 `EXT_` helpers of unit EXT (carrier correspondence, list/crossing transport,
  same-polygon and wall lemmas, the guard radius `EXT_exists_guardRadius`, the record isomorphism
  `EXT_homfly_wall`/`EXT_pieceHomfly_wall`, the rotation `EXT_rotation_wall`, the field lemmas
  `EXT_168_independent_of_A`, `EXT_168_wall_invariant`, `EXT_168_factorization`);
* **Row 168, R:exterior** — `RProof.exterior`, PROVED (radius `min δ_L δ_G` of row 164 `localization` and
  the guard radius);
* `section AV` and six top-level `AV_` lemmas — the wall data `AV_Wall`, the corner-successor transport of
  carriers, the record isomorphism of positive lifts `AV_homfly_lift_eq`, the ray-formula rotation
  `AV_rotationNumber_tcp`, the event radius `AV_exists_eventRadius`, and the X₁ field lemmas
  `AV_170_summand_transport`, `AV_170_summands_agree`, `AV_170_fibre_identity`;
* **Row 170, R:availability_0_1** — `RProof.availability_zero_one`, PROVED (radius `min δ_L (min δ_F δ_R)`
  of rows 164, 171 and the sign radius; presupposition fields from the wave-1 `PRE_170_*` lemmas).

Every declaration here is absent from `RProof.X1Rows` (checked name by name; nothing is redeclared), the
statements of the two row theorems are the frozen ones of `Statements_FINAL.lean` verbatim, and the module
has no placeholder proof. Compile: `cd work/lean && lake env lean ../drafts/rlane2/RLaneX1Rows2.lean`
(with `RProof.X1Rows` built). The same context as `RProof.X1Rows` is opened below (`namespace RProof`,
`open SM SM.GeoCarrier`, `variable {n : ℕ} [NeZero n]`) so that the unit text is unchanged. -/

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-! ## Unit EXT — proof lane of row 168, R:exterior (2026-09-14)

Helper lemmas (prefix `EXT_`) for the three fields of `ExteriorData`, placed before the row theorem.
Nothing in the fixed statements is changed. Structure (NOTES_FINAL §2, R-EXTERIOR-1 proof §1–§4):
* `EXT_sameCycle_of_conj_on`, `EXT_block`, `EXT_corr*` — the carrier correspondence: on a set of marks
  invariant under one smoothing successor on which the other successor agrees (through an identification
  of marks), the cycles correspond (§1 "exterior carriers are fiber-stable", and §4 "erasing the six `T`
  visits gives the same marked traversal word on both sides");
* `EXT_markList_map`, `EXT_cornerList_map`, `EXT_cornerCount_eq`, `EXT_cornerMark_eq`,
  `EXT_cornerPolygon_eq` — mark lists, corner lists and the corner polygon are carried;
* `EXT_carrierCrossings_map`, `EXT_walk_transfer`, `EXT_PieceSetting`, `EXT_mem_labels_iff`,
  `EXT_pieceMap*`, `EXT_piecesOn_prod/sum`, `EXT_pieceSetting` — retained crossings and residual pieces
  are carried piece for piece (§2 "exterior residual pieces are fiber-stable", lem:carriers (iv) as
  `EXT_closed`);
* `EXT_weight_eq`, `EXT_carrierR_eq`, `EXT_groupedWrithe_eq`, `EXT_groupedPoly_eq`, `EXT_Omega1_eq`,
  `EXT_pieceHomfly_eq_of_labels`, `EXT_exteriorFactor_eq` — `wt`, `R`, `w_{S,L}`, `P_{S,L}`, `Ω₁` and the
  exterior factor are carried (§3), the piece polynomial at one polygon by choice independence
  (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`, lem:pieceintrinsic);
* `EXT_exteriorFactor_eq_base`, `EXT_168_independent_of_A` — the same-polygon instance `Q ∪ A` vs `Q`
  (`geoSmoothingSuccessor_union_of_disjoint`) and the field `independent_of_A`;
* `EXT_key_lt_wall`, `EXT_markSucc_wall`, `EXT_succ_wall`, `EXT_turn_wall` — the wall: traversal order of
  non-bundle pairs (`ExactTriangleVisitOrders`, R-LOC-2 (2)–(3)), the successor of a good mark, the
  corner turns (`turn_vertex_of_traced`, `turn_visit_of_traced`);
* `EXT_GuardAt`, `EXT_exists_guardRadius` — lem:guardconst for `G1`/`G5` uniformly over the finitely many
  members, giving wall-invariant turn signs, crossing signs and divide signs;
* `EXT_homfly_wall`, `EXT_pieceHomfly_wall` — the identity on parent visits is a record isomorphism
  between the positive lifts on the two sides (CV:def:record (a)–(d), `recordIsoOfData`), so the piece
  polynomials agree by the accepted `gausscode_polynomial` (§4 "ax:gausscode gives the same oriented link
  and ax:homfly the same polynomial");
* `EXT_seg`, `EXT_familyEdge`, `EXT_pa_lt_pb_all`, `EXT_family_regular`, `EXT_family_continuous`,
  `EXT_rotation_wall` — the corner polygon of an exterior carrier deforms continuously and regularly
  through the wall along `t ↦ P(t)` (every edge a positive multiple of a polygon edge, corners at
  `G1 ≠ 0` / `G5 ≠ 0`), so its rotation number is constant (`rotationNumber_family_constant`; §4 "for
  rotation … lem:turnlift(ii)");
* `EXT_exteriorFactor_wall`, `EXT_168_wall_invariant`, `EXT_168_factorization` — the fields. -/

section EXT

open SM.Carrier

section EXTCore

variable {P P' : LabelledTuple n}

/-- Conjugation on an invariant set: for `a` in a set `U` invariant under `f`, on which `g ∘ e = e ∘ f`,
the `g`-cycle of `e a` is the image of the `f`-cycle of `a`. -/
theorem EXT_sameCycle_of_conj_on {α β : Type*} (f : Equiv.Perm α) (g : Equiv.Perm β) (e : α ≃ β)
    (U : Set α) (hU : Set.BijOn f U U) (h : ∀ a ∈ U, g (e a) = e (f a)) :
    ∀ a ∈ U, ∀ b, g.SameCycle (e a) (e b) ↔ f.SameCycle a b := by
  intro a ha b
  have hconj : ∀ x, (e.permCongr f) (e x) = e (f x) := by
    intro x
    simp [Equiv.permCongr_apply]
  have h1 := sameCycle_of_equiv_conj f (e.permCongr f) e hconj a b
  have hbij : Set.BijOn (e.permCongr f) (e '' U) (e '' U) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [hconj]
      exact ⟨f x, hU.mapsTo hx, rfl⟩
    · intro x _ y _ hxy
      exact (e.permCongr f).injective hxy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hfx⟩ := hU.surjOn hy
      exact ⟨e x, ⟨x, hx, rfl⟩, by rw [hconj, hfx]⟩
  have heq : Set.EqOn (e.permCongr f) g (e '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj, h x hx]
  exact (sameCycle_congr_of_eqOn_bijOn (e.permCongr f) g (e '' U) hbij heq (e a) ⟨a, ha, rfl⟩
    (e b)).trans h1

/-- A carrier avoids the bad marks: every mark it owns is good. -/
def EXT_Avoids (hP : CrossingGeometry P) (S : Finset (Crossing P)) (Good : Mark P → Prop)
    (q : GeoComponent hP S) : Prop :=
  ∀ a, geoOwner hP S a = q → Good a

/-- The block lemma: if the two smoothing successors commute with the identification `e` at every good
mark with good successor, then for a mark `a` of a good-avoiding carrier the images of the marks of the
carrier of `a` are exactly the marks of the carrier of `e a`. -/
theorem EXT_block (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) (a : Mark P) (ha : geoOwner hP S a = q)
    (b : Mark P) :
    geoOwner hP' S' (e a) = geoOwner hP' S' (e b) ↔ geoOwner hP S a = geoOwner hP S b := by
  rw [geoOwner_eq_iff, geoOwner_eq_iff]
  refine EXT_sameCycle_of_conj_on _ _ e {m | geoOwner hP S m = q}
    (geoSmoothingSuccessor_bijOn_owner hP S q) ?_ a ha b
  intro m hm
  refine hcomm m (hq m hm) (hq _ ?_)
  rw [geoOwner_successor]
  exact hm

/-- The corresponding carrier: the carrier of the image of any mark of `q`. -/
noncomputable def EXT_corr (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S) :
    GeoComponent hP' S' :=
  geoOwner hP' S' (e (Classical.choose (geoOwner_surjective hP S q)))

theorem EXT_corr_iff (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) (b : Mark P) :
    geoOwner hP' S' (e b) = EXT_corr hP hP' e S S' q ↔ geoOwner hP S b = q := by
  have ha := Classical.choose_spec (geoOwner_surjective hP S q)
  unfold EXT_corr
  rw [eq_comm, EXT_block hP hP' e S S' Good hcomm q hq _ ha b, ha, eq_comm]

theorem EXT_corr_iff' (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) (b' : Mark P') :
    geoOwner hP' S' b' = EXT_corr hP hP' e S S' q ↔ geoOwner hP S (e.symm b') = q := by
  have h := EXT_corr_iff hP hP' e S S' Good hcomm q hq (e.symm b')
  rwa [Equiv.apply_symm_apply] at h

/-- The corresponding carrier avoids the bad marks of `P'` (the images of the bad marks). -/
theorem EXT_corr_avoids (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) :
    EXT_Avoids hP' S' (fun b' => Good (e.symm b')) (EXT_corr hP hP' e S S' q) := by
  intro b' hb'
  exact hq _ ((EXT_corr_iff' hP hP' e S S' Good hcomm q hq b').mp hb')

/-- `EXT_corr` is inverted by the corresponding map in the other direction. -/
theorem EXT_corr_corr (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (hcomm' : ∀ b', Good (e.symm b') → Good (e.symm (geoSmoothingSuccessor hP' S' b')) →
      geoSmoothingSuccessor hP S (e.symm b') = e.symm (geoSmoothingSuccessor hP' S' b'))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) :
    EXT_corr hP' hP e.symm S' S (EXT_corr hP hP' e S S' q) = q := by
  have ha := Classical.choose_spec (geoOwner_surjective hP S q)
  set a₀ := Classical.choose (geoOwner_surjective hP S q)
  have h1 : geoOwner hP' S' (e a₀) = EXT_corr hP hP' e S S' q :=
    (EXT_corr_iff hP hP' e S S' Good hcomm q hq a₀).mpr ha
  have h2 := EXT_corr_iff hP' hP e.symm S' S (fun b' => Good (e.symm b')) hcomm'
    (EXT_corr hP hP' e S S' q) (EXT_corr_avoids hP hP' e S S' Good hcomm q hq) (e a₀)
  rw [Equiv.symm_apply_apply] at h2
  exact (h2.mpr h1).symm.trans ha

end EXTCore


section EXTLists

variable {P P' : LabelledTuple n}

/-- The marks of a carrier are carried onto the marks of the corresponding carrier, in inherited order,
provided the traversal order of its marks is carried (`hkey`): both lists are the strictly increasing
enumerations of the same set of marks. -/
theorem EXT_markList_map (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hblock : ∀ b, geoOwner hP' S' (e b) = q' ↔ geoOwner hP S b = q)
    (hkey : ∀ a b, geoOwner hP S a = q → geoOwner hP S b = q →
      (geoMarkKey hP a < geoMarkKey hP b ↔ geoMarkKey hP' (e a) < geoMarkKey hP' (e b))) :
    (geoComponentMarkList hP S q).map e = geoComponentMarkList hP' S' q' := by
  classical
  have hnodup : ((geoComponentMarkList hP S q).map e).Nodup :=
    (geoComponentMarkList_nodup hP S q).map e.injective
  have hperm : ((geoComponentMarkList hP S q).map e).Perm (geoComponentMarkList hP' S' q') := by
    rw [List.perm_ext_iff_of_nodup hnodup (geoComponentMarkList_nodup hP' S' q')]
    intro x
    rw [List.mem_map, mem_geoComponentMarkList]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hblock a).mpr ((mem_geoComponentMarkList hP S q a).mp ha)
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [mem_geoComponentMarkList, ← hblock, e.apply_symm_apply]
      exact hx
  have hsorted' : (geoComponentMarkList hP' S' q').Pairwise
      (fun a b => geoMarkKey hP' a ≤ geoMarkKey hP' b) :=
    (geoMarkList_sorted hP').filter _
  have hsorted : ((geoComponentMarkList hP S q).map e).Pairwise
      (fun a b => geoMarkKey hP' a ≤ geoMarkKey hP' b) := by
    rw [List.pairwise_map]
    have h1 : (geoComponentMarkList hP S q).Pairwise (fun a b => geoMarkKey hP a ≤ geoMarkKey hP b) :=
      (geoMarkList_sorted hP).filter _
    have h2 : (geoComponentMarkList hP S q).Pairwise (fun a b => a ≠ b) :=
      geoComponentMarkList_nodup hP S q
    refine List.Pairwise.imp_of_mem ?_ (h1.and h2)
    intro a b ha hb hab
    have hlt : geoMarkKey hP a < geoMarkKey hP b :=
      lt_of_le_of_ne hab.1 (fun h => hab.2 (geoMarkKey_injective hP h))
    exact ((hkey a b ((mem_geoComponentMarkList hP S q a).mp ha)
      ((mem_geoComponentMarkList hP S q b).mp hb)).mp hlt).le
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => geoMarkKey_injective hP' (le_antisymm hab hba)) hsorted hsorted' hperm

/-- The corner list is carried once the mark list is and corners correspond. -/
theorem EXT_cornerList_map (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hlist : (geoComponentMarkList hP S q).map e = geoComponentMarkList hP' S' q')
    (hcorner : ∀ a, geoOwner hP S a = q → (IsTrueCorner S' (e a) ↔ IsTrueCorner S a)) :
    (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q' := by
  unfold geoComponentCornerList
  rw [← hlist, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x hx
  simp only [Function.comp]
  exact decide_eq_decide.mpr (hcorner x ((mem_geoComponentMarkList hP S q x).mp hx)).symm

theorem EXT_cornerCount_eq (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q') :
    geoCornerCount hP' S' q' = geoCornerCount hP S q := by
  unfold geoCornerCount
  rw [← hcl, List.length_map]

theorem EXT_cornerMark_eq (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q')
    (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP' S' q'
        (Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' e S S' q q' hcl).symm) k) =
      e (geoCornerMark hP S q k) := by
  have hc := EXT_cornerCount_eq hP hP' e S S' q q' hcl
  have hlen : k.val < (geoComponentCornerList hP' S' q').length := by
    rw [← hcl, List.length_map]
    exact ZMod.val_lt k
  have h3 : k.val < ((geoComponentCornerList hP S q).map e).length := by
    rw [List.length_map]
    exact ZMod.val_lt k
  unfold geoCornerMark
  refine (geo_getElem_congr _ _ rfl _ _ _ hlen (geo_zmod_val_cast hc.symm k)).trans ?_
  refine (geo_getElem_congr _ _ hcl.symm _ _ hlen h3 rfl).trans ?_
  exact List.getElem_map _

theorem EXT_cornerMark_eq' (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q')
    (j : ZMod (geoCornerCount hP' S' q')) :
    geoCornerMark hP' S' q' j =
      e (geoCornerMark hP S q
        (Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' e S S' q q' hcl)) j)) := by
  have h := EXT_cornerMark_eq hP hP' e S S' q q' hcl
    (Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' e S S' q q' hcl)) j)
  rwa [geo_zmod_cast_cast (EXT_cornerCount_eq hP hP' e S S' q q' hcl) j] at h

/-- The corner polygon of the corresponding carrier is the polygon of the images of the corner marks,
recast along the equal corner counts. -/
theorem EXT_cornerPolygon_eq (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q') :
    geoCornerPolygon hP' S' q' =
      geoRecast (EXT_cornerCount_eq hP hP' e S S' q q' hcl)
        (fun k => traversalEvaluation P' (geoMarkPosition hP' (e (geoCornerMark hP S q k)))) := by
  funext j
  show traversalEvaluation P' (geoMarkPosition hP' (geoCornerMark hP' S' q' j)) = _
  rw [EXT_cornerMark_eq' hP hP' e S S' q q' hcl j]
  rfl

/-- Same polygon, identity identification: the corner polygon is literally the recast corner polygon. -/
theorem EXT_cornerPolygon_eq_self (hP : CrossingGeometry P) (e : Mark P ≃ Mark P) (he : ∀ a, e a = a)
    (S S' : Finset (Crossing P)) (q : GeoComponent hP S) (q' : GeoComponent hP S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP S' q') :
    geoCornerPolygon hP S' q' =
      geoRecast (EXT_cornerCount_eq hP hP e S S' q q' hcl) (geoCornerPolygon hP S q) := by
  rw [EXT_cornerPolygon_eq hP hP e S S' q q' hcl]
  congr 1
  funext k
  rw [he]
  rfl

end EXTLists

section EXTCrossings

variable {P P' : LabelledTuple n}

/-- The retained crossings of corresponding carriers correspond. -/
theorem EXT_carrierCrossings_map (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hblock : ∀ b, geoOwner hP' S' (markTransport hs b) = q' ↔ geoOwner hP S b = q)
    (hsel : ∀ x : Crossing P, (∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q) →
      (crossingTransport hs x ∈ S' ↔ x ∈ S)) :
    geoCarrierCrossings hP' S' q' =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding := by
  ext x'
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_geoCarrierCrossings, mem_geoCarrierCrossings]
  have hvis : (∀ w : Visit P', w.1 = crossingTransport hs x → geoOwner hP' S' (Sum.inr w) = q') ↔
      (∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q) := by
    constructor
    · intro h v hv
      have := h (visitTransport hs v) (by rw [visitTransport_crossing, hv])
      rw [← markTransport_visit, hblock] at this
      exact this
    · intro h w hw
      obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
      rw [visitTransport_crossing] at hw
      rw [← markTransport_visit, hblock]
      exact h v ((crossingTransport hs).injective hw)
  rw [hvis]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hx => h1 ((hsel x h2).mpr hx), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hx => h1 ((hsel x h2).mp hx), h2⟩

/-- A walk of the induced graph on `U` starting in a closed set `X` stays in `X` and is carried to a
walk of the induced graph on `U'`. -/
theorem EXT_walk_transfer {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')
    (U : Set V) (U' : Set V') (X : Set V) (φ : V → V')
    (hXU' : ∀ c ∈ X, φ c ∈ U')
    (hadj : ∀ c ∈ X, ∀ d ∈ X, G.Adj c d → G'.Adj (φ c) (φ d))
    (hclosed : ∀ c ∈ X, ∀ d ∈ U, G.Adj c d → d ∈ X) :
    ∀ (a b : ↑U) (_ : (G.induce U).Walk a b) (ha : a.val ∈ X),
      ∃ hb : b.val ∈ X, (G'.induce U').Reachable ⟨φ a.val, hXU' _ ha⟩ ⟨φ b.val, hXU' _ hb⟩ := by
  intro a b w
  induction w with
  | nil =>
    intro ha
    exact ⟨ha, SimpleGraph.Reachable.refl _⟩
  | @cons a a₁ b h w ih =>
    intro ha
    have hadj₁ : G.Adj a.val a₁.val := h
    have ha₁ : a₁.val ∈ X := hclosed _ ha _ a₁.property hadj₁
    obtain ⟨hb, hr⟩ := ih ha₁
    refine ⟨hb, SimpleGraph.Reachable.trans ?_ hr⟩
    exact SimpleGraph.Adj.reachable (hadj _ ha _ ha₁ hadj₁)

/-- Membership in the piece of `c`, read through reachability in the residual graph. -/
theorem EXT_mem_pieceLabels_pieceOf (hP : CrossingGeometry P) (S : Finset (Crossing P)) {c : Crossing P}
    (hc : c ∈ CV.U hP S) (d : Crossing P) :
    d ∈ CV.pieceLabels hP S (CV.pieceOf hP S c hc) ↔
      ∃ hd : d ∈ CV.U hP S, (CV.residualGraph hP S).Reachable ⟨c, hc⟩ ⟨d, hd⟩ := by
  rw [CV.mem_pieceLabels]
  constructor
  · rintro ⟨hd, h⟩
    exact ⟨hd, (SimpleGraph.ConnectedComponent.eq.mp h).symm⟩
  · rintro ⟨hd, h⟩
    exact ⟨hd, SimpleGraph.ConnectedComponent.eq.mpr h.symm⟩

/-- The data under which the pieces with labels in `X` correspond across the identification of
crossings `crossingTransport hs`: `X` lies in both undominated sets, interlacement on `X` is carried,
and `X` is closed under interlacement with undominated crossings on both sides. -/
structure EXT_PieceSetting (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) : Prop where
  subU : ∀ c ∈ X, c ∈ CV.U hP S
  subU' : ∀ c ∈ X, crossingTransport hs c ∈ CV.U hP' S'
  adj_iff : ∀ c ∈ X, ∀ d ∈ X,
    GeometricInterlaces hP' (crossingTransport hs c) (crossingTransport hs d) ↔ GeometricInterlaces hP c d
  closed : ∀ c ∈ X, ∀ d ∈ CV.U hP S, GeometricInterlaces hP c d → d ∈ X
  closed' : ∀ c ∈ X, ∀ d' ∈ CV.U hP' S', GeometricInterlaces hP' (crossingTransport hs c) d' →
    (crossingTransport hs).symm d' ∈ X

/-- The labels of corresponding pieces correspond (for pieces with a label in `X`). -/
theorem EXT_mem_labels_iff (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X) {c : Crossing P} (hcX : c ∈ X)
    (d : Crossing P) :
    d ∈ CV.pieceLabels hP S (CV.pieceOf hP S c (hX.subU c hcX)) ↔
      crossingTransport hs d ∈
        CV.pieceLabels hP' S' (CV.pieceOf hP' S' (crossingTransport hs c) (hX.subU' c hcX)) := by
  rw [EXT_mem_pieceLabels_pieceOf, EXT_mem_pieceLabels_pieceOf]
  constructor
  · rintro ⟨hd, ⟨w⟩⟩
    obtain ⟨hdX, hr⟩ := EXT_walk_transfer (geometricInterlacementGraph hP)
      (geometricInterlacementGraph hP') (↑(CV.U hP S)) (↑(CV.U hP' S')) (↑X) (crossingTransport hs)
      (fun c hc => hX.subU' c hc) (fun c hc d hd h => (hX.adj_iff c hc d hd).mpr h)
      (fun c hc d hd h => hX.closed c hc d hd h) ⟨c, hX.subU c hcX⟩ ⟨d, hd⟩ w hcX
    exact ⟨hX.subU' d hdX, hr⟩
  · rintro ⟨hd', ⟨w⟩⟩
    have himg : ∀ c' ∈ ((fun x => crossingTransport hs x) '' (↑X : Set (Crossing P))),
        (crossingTransport hs).symm c' ∈ (↑X : Set (Crossing P)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Equiv.symm_apply_apply]
      exact hx
    obtain ⟨hdX, hr⟩ := EXT_walk_transfer (geometricInterlacementGraph hP')
      (geometricInterlacementGraph hP) (↑(CV.U hP' S')) (↑(CV.U hP S))
      ((fun x => crossingTransport hs x) '' (↑X : Set (Crossing P))) (crossingTransport hs).symm
      (fun c' hc' => hX.subU _ (himg c' hc'))
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact (hX.adj_iff x hx y hy).mp h)
      (by
        rintro _ ⟨x, hx, rfl⟩ d' hd' h
        exact ⟨(crossingTransport hs).symm d', hX.closed' x hx d' hd' h, Equiv.apply_symm_apply _ _⟩)
      ⟨crossingTransport hs c, hX.subU' c hcX⟩ ⟨crossingTransport hs d, hd'⟩ w ⟨c, hcX, rfl⟩
    have hdX' : d ∈ X := by
      have := himg _ hdX
      rwa [Equiv.symm_apply_apply] at this
    refine ⟨hX.subU d hdX', ?_⟩
    exact hr

/-- The labels of a piece carried by `q` are retained crossings of `q`. -/
theorem EXT_pieceLabels_subset_of_mem_piecesOn (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (H : CV.Piece hP S) (hH : H ∈ CV.piecesOn hP S q) :
    CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q := by
  intro c hc
  rw [mem_geoCarrierCrossings]
  exact ⟨((CV.mem_U_iff hP S c).mp (CV.pieceLabels_subset hP S H hc)).1,
    (CV.mem_piecesOn hP S q H).mp hH c hc⟩

theorem EXT_mem_piecesOn_of_subset (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (H : CV.Piece hP S) (h : CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q) :
    H ∈ CV.piecesOn hP S q := by
  rw [CV.mem_piecesOn]
  intro c hc v hv
  exact ((mem_geoCarrierCrossings hP S q c).mp (h hc)).2 v hv

/-- Pieces with the same labels are equal. -/
theorem EXT_piece_eq_of_labels_eq (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (H H' : CV.Piece hP S) (h : CV.pieceLabels hP S H = CV.pieceLabels hP S H') : H = H' := by
  by_contra hne
  obtain ⟨c, hc⟩ := CV.pieceLabels_nonempty hP S H
  exact Finset.disjoint_left.mp (CV.pieceLabels_disjoint hP S H H' hne) hc (h ▸ hc)

/-- The piece corresponding to `H` (with labels in `X`): the piece of the image of a label of `H`. -/
noncomputable def EXT_pieceMap (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X)
    (H : CV.Piece hP S) (hH : CV.pieceLabels hP S H ⊆ X) : CV.Piece hP' S' :=
  CV.pieceOf hP' S' (crossingTransport hs (CV.pieceLabels_nonempty hP S H).choose)
    (hX.subU' _ (hH (CV.pieceLabels_nonempty hP S H).choose_spec))

theorem EXT_pieceMap_labels (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X)
    (H : CV.Piece hP S) (hH : CV.pieceLabels hP S H ⊆ X) :
    CV.pieceLabels hP' S' (EXT_pieceMap hP hP' hs S S' X hX H hH) =
      (CV.pieceLabels hP S H).map (crossingTransport hs).toEmbedding := by
  set c := (CV.pieceLabels_nonempty hP S H).choose with hcdef
  have hcH : c ∈ CV.pieceLabels hP S H := (CV.pieceLabels_nonempty hP S H).choose_spec
  have hcX : c ∈ X := hH hcH
  obtain ⟨hcU, hHc⟩ := (CV.mem_pieceLabels hP S H c).mp hcH
  ext d'
  obtain ⟨d, rfl⟩ := (crossingTransport hs).surjective d'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  unfold EXT_pieceMap
  rw [← EXT_mem_labels_iff hP hP' hs S S' X hX hcX d]
  have : CV.pieceOf hP S c (hX.subU c hcX) = H := hHc
  rw [this]

/-- The inverse piece map. -/
noncomputable def EXT_pieceMapRev (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X)
    (H' : CV.Piece hP' S') (hH' : CV.pieceLabels hP' S' H' ⊆ X.map (crossingTransport hs).toEmbedding) :
    CV.Piece hP S :=
  CV.pieceOf hP S ((crossingTransport hs).symm (CV.pieceLabels_nonempty hP' S' H').choose)
    (hX.subU _ (Finset.mem_map_equiv.mp (hH' (CV.pieceLabels_nonempty hP' S' H').choose_spec)))

theorem EXT_pieceMapRev_labels (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X)
    (H' : CV.Piece hP' S') (hH' : CV.pieceLabels hP' S' H' ⊆ X.map (crossingTransport hs).toEmbedding) :
    (CV.pieceLabels hP S (EXT_pieceMapRev hP hP' hs S S' X hX H' hH')).map (crossingTransport hs).toEmbedding =
      CV.pieceLabels hP' S' H' := by
  set c' := (CV.pieceLabels_nonempty hP' S' H').choose with hcdef
  have hcH : c' ∈ CV.pieceLabels hP' S' H' := (CV.pieceLabels_nonempty hP' S' H').choose_spec
  have hcX : (crossingTransport hs).symm c' ∈ X := Finset.mem_map_equiv.mp (hH' hcH)
  obtain ⟨hcU, hHc⟩ := (CV.mem_pieceLabels hP' S' H' c').mp hcH
  ext d'
  obtain ⟨d, rfl⟩ := (crossingTransport hs).surjective d'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  unfold EXT_pieceMapRev
  rw [EXT_mem_labels_iff hP hP' hs S S' X hX hcX d]
  have : CV.pieceOf hP' S' (crossingTransport hs ((crossingTransport hs).symm c'))
      (hX.subU' _ hcX) = H' := by
    have h2 : crossingTransport hs ((crossingTransport hs).symm c') = c' := Equiv.apply_symm_apply _ _
    rw [← hHc]
    congr 1
  rw [this]

/-- Reindexing a product over the pieces carried by `q` along the piece correspondence. -/
theorem EXT_piecesOn_prod {M : Type*} [CommMonoid M] (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hX : EXT_PieceSetting hP hP' hs S S' (geoCarrierCrossings hP S q))
    (hX' : geoCarrierCrossings hP' S' q' =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding)
    (F : CV.Piece hP S → M) (F' : CV.Piece hP' S' → M)
    (hF : ∀ (H : CV.Piece hP S) (H' : CV.Piece hP' S'),
      CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q →
      CV.pieceLabels hP' S' H' = (CV.pieceLabels hP S H).map (crossingTransport hs).toEmbedding →
      F' H' = F H) :
    ∏ H ∈ CV.piecesOn hP S q, F H = ∏ H' ∈ CV.piecesOn hP' S' q', F' H' := by
  refine Finset.prod_bij'
    (fun H hH => EXT_pieceMap hP hP' hs S S' _ hX H (EXT_pieceLabels_subset_of_mem_piecesOn hP S q H hH))
    (fun H' hH' => EXT_pieceMapRev hP hP' hs S S' _ hX H'
      (hX' ▸ EXT_pieceLabels_subset_of_mem_piecesOn hP' S' q' H' hH')) ?_ ?_ ?_ ?_ ?_
  · intro H hH
    apply EXT_mem_piecesOn_of_subset
    rw [EXT_pieceMap_labels, hX']
    exact Finset.map_subset_map.mpr (EXT_pieceLabels_subset_of_mem_piecesOn hP S q H hH)
  · intro H' hH'
    apply EXT_mem_piecesOn_of_subset
    have h := EXT_pieceMapRev_labels hP hP' hs S S' _ hX H'
      (hX' ▸ EXT_pieceLabels_subset_of_mem_piecesOn hP' S' q' H' hH')
    have h2 := EXT_pieceLabels_subset_of_mem_piecesOn hP' S' q' H' hH'
    rw [hX', ← h] at h2
    exact Finset.map_subset_map.mp h2
  · intro H hH
    apply EXT_piece_eq_of_labels_eq
    apply Finset.map_injective (crossingTransport hs).toEmbedding
    rw [EXT_pieceMapRev_labels, EXT_pieceMap_labels]
  · intro H' hH'
    apply EXT_piece_eq_of_labels_eq
    rw [EXT_pieceMap_labels, EXT_pieceMapRev_labels]
  · intro H hH
    exact (hF H _ (EXT_pieceLabels_subset_of_mem_piecesOn hP S q H hH)
      (EXT_pieceMap_labels hP hP' hs S S' _ hX H _)).symm

/-- The additive form of `EXT_piecesOn_prod`. -/
theorem EXT_piecesOn_sum {M : Type*} [AddCommMonoid M] (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hX : EXT_PieceSetting hP hP' hs S S' (geoCarrierCrossings hP S q))
    (hX' : geoCarrierCrossings hP' S' q' =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding)
    (F : CV.Piece hP S → M) (F' : CV.Piece hP' S' → M)
    (hF : ∀ (H : CV.Piece hP S) (H' : CV.Piece hP' S'),
      CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q →
      CV.pieceLabels hP' S' H' = (CV.pieceLabels hP S H).map (crossingTransport hs).toEmbedding →
      F' H' = F H) :
    ∑ H ∈ CV.piecesOn hP S q, F H = ∑ H' ∈ CV.piecesOn hP' S' q', F' H' :=
  EXT_piecesOn_prod (M := Multiplicative M) hP hP' hs S S' q q' hX hX'
    (fun H => Multiplicative.ofAdd (F H)) (fun H' => Multiplicative.ofAdd (F' H'))
    (fun H H' h1 h2 => congrArg Multiplicative.ofAdd (hF H H' h1 h2))

/-- `X = geoCarrierCrossings q` is closed under interlacement with undominated crossings
(lem:carriers (iv): an undominated crossing interlacing a retained crossing of `q` lies on `q`). -/
theorem EXT_closed (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hP)
    (q : GeoComponent hP S) :
    ∀ c ∈ geoCarrierCrossings hP S q, ∀ d ∈ CV.U hP S, GeometricInterlaces hP c d →
      d ∈ geoCarrierCrossings hP S q := by
  intro c hc d hd hI
  have hcU : c ∈ CV.U hP S :=
    (CV.mem_U_iff hP S c).mpr ((mem_geoSupportUnselected_iff hP S c).mp
      (geoCarrierCrossings_subset_U hP (CV.geoIndependent_of_mem_Ind hP hS) q hc))
  rw [mem_geoCarrierCrossings] at hc ⊢
  refine ⟨((CV.mem_U_iff hP S d).mp hd).1, ?_⟩
  intro w hw
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  have := CV.owner_eq_of_interlaces_mem_U hP hS hcU hd hI ⟨c, i⟩ w rfl hw
  rw [← this]
  exact hc.2 ⟨c, i⟩ rfl

/-- The piece setting at the retained crossings of corresponding carriers of independent supports. -/
theorem EXT_pieceSetting (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hP) (hS' : S' ∈ CV.Ind hP')
    (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hX' : geoCarrierCrossings hP' S' q' =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding)
    (hadj : ∀ c ∈ geoCarrierCrossings hP S q, ∀ d ∈ geoCarrierCrossings hP S q,
      GeometricInterlaces hP' (crossingTransport hs c) (crossingTransport hs d) ↔
        GeometricInterlaces hP c d) :
    EXT_PieceSetting hP hP' hs S S' (geoCarrierCrossings hP S q) where
  subU c hc := (CV.mem_U_iff hP S c).mpr ((mem_geoSupportUnselected_iff hP S c).mp
    (geoCarrierCrossings_subset_U hP (CV.geoIndependent_of_mem_Ind hP hS) q hc))
  subU' c hc := (CV.mem_U_iff hP' S' _).mpr ((mem_geoSupportUnselected_iff hP' S' _).mp
    (geoCarrierCrossings_subset_U hP' (CV.geoIndependent_of_mem_Ind hP' hS') q'
      (by rw [hX']; exact Finset.mem_map_of_mem _ hc)))
  adj_iff := hadj
  closed := EXT_closed hP hS q
  closed' c hc d' hd' h := by
    have hc' : crossingTransport hs c ∈ geoCarrierCrossings hP' S' q' := by
      rw [hX']; exact Finset.mem_map_of_mem _ hc
    have := EXT_closed hP' hS' q' _ hc' d' hd' h
    rw [hX'] at this
    exact Finset.mem_map_equiv.mp this

end EXTCrossings

section EXTCarrierData

variable {P P' : LabelledTuple n}

/-- The bad marks: the six traversal visits of the triangle (including a selected triangle crossing's
smoothing-site visits, which are the same marks). -/
def EXT_TriVisit (e f g : ZMod n) : Mark P → Prop
  | Sum.inl _ => False
  | Sum.inr v => v.1.val ∈ triangleSupports e f g

omit [NeZero n] in
theorem EXT_triVisit_markTransport_symm {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} (e f g : ZMod n)
    (b' : Mark P') : EXT_TriVisit e f g ((markTransport hs).symm b') ↔ EXT_TriVisit e f g b' := by
  cases b' with
  | inl i => exact Iff.rfl
  | inr v => exact Iff.rfl

omit [NeZero n] in
theorem EXT_triVisit_markTransport {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} (e f g : ZMod n)
    (a : Mark P) : EXT_TriVisit e f g (markTransport hs a) ↔ EXT_TriVisit e f g a := by
  cases a with
  | inl i => exact Iff.rfl
  | inr v => exact Iff.rfl

theorem EXT_triangleDisjoint_iff (hP : CrossingGeometry P) (S : Finset (Crossing P)) (e f g : ZMod n)
    (q : GeoComponent hP S) :
    TriangleDisjoint hP S e f g q ↔ EXT_Avoids hP S (fun a => ¬ EXT_TriVisit e f g a) q := by
  constructor
  · intro h a ha
    cases a with
    | inl i => exact id
    | inr v => exact fun hv => h v hv ha
  · intro h v hv hq
    exact h _ hq hv

/-- `wt(L)` is determined by the turn sequence of the corner polygon. -/
theorem EXT_weight_eq (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (S : Finset (Crossing P))
    (S' : Finset (Crossing P')) (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hc : geoCornerCount hP' S' q' = geoCornerCount hP S q)
    (hturn : ∀ k, turn (geoCornerPolygon hP' S' q') k =
      turn (geoCornerPolygon hP S q) (Equiv.cast (congrArg ZMod hc) k)) :
    CV.weight hP' S' q' = CV.weight hP S q := by
  unfold CV.weight geoCarrierSelector
  rw [← cornerSelector_geoRecast hc.symm (geoCornerPolygon hP' S' q')]
  apply cornerSelector_congr_turn
  intro j
  rw [turn_geoRecast, hturn, geo_zmod_cast_cast' hc j]

/-- `R(L) = |rot(L)|` is determined by the rotation number of the corner polygon. -/
theorem EXT_carrierR_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')} (hS : S ∈ CV.Ind hG.crossingGeometry)
    (hS' : S' ∈ CV.Ind hG'.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (q' : GeoComponent hG'.crossingGeometry S')
    (hrot : rotationNumber (geoCornerPolygon hG'.crossingGeometry S' q') =
      rotationNumber (geoCornerPolygon hG.crossingGeometry S q)) :
    CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q := by
  unfold CV.carrierR CV.rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [CV.rot_eq_rotationNumber, CV.rot_eq_rotationNumber]
  exact hrot

theorem EXT_groupedWrithe_eq (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (hX : EXT_PieceSetting hG.crossingGeometry hG'.crossingGeometry hs S S'
      (geoCarrierCrossings hG.crossingGeometry S q))
    (hX' : geoCarrierCrossings hG'.crossingGeometry S' q' =
      (geoCarrierCrossings hG.crossingGeometry S q).map (crossingTransport hs).toEmbedding) :
    CV.groupedWrithe hG' q' = CV.groupedWrithe hG q := by
  unfold CV.groupedWrithe
  symm
  apply EXT_piecesOn_sum hG.crossingGeometry hG'.crossingGeometry hs S S' q q' hX hX'
  intro H H' _ h
  unfold CV.pieceWrithe
  rw [h, Finset.card_map]

theorem EXT_groupedPoly_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (hX : EXT_PieceSetting hG.crossingGeometry hG'.crossingGeometry hs S S'
      (geoCarrierCrossings hG.crossingGeometry S q))
    (hX' : geoCarrierCrossings hG'.crossingGeometry S' q' =
      (geoCarrierCrossings hG.crossingGeometry S q).map (crossingTransport hs).toEmbedding)
    (hPH : ∀ (H : CV.Piece hG.crossingGeometry S) (H' : CV.Piece hG'.crossingGeometry S'),
      CV.pieceLabels hG.crossingGeometry S H ⊆ geoCarrierCrossings hG.crossingGeometry S q →
      CV.pieceLabels hG'.crossingGeometry S' H' =
        (CV.pieceLabels hG.crossingGeometry S H).map (crossingTransport hs).toEmbedding →
      CV.pieceHomfly hn (hG'.diagrammatic hn) hS' H' = CV.pieceHomfly hn (hG.diagrammatic hn) hS H) :
    CV.groupedPoly hn hG' hS' q' = CV.groupedPoly hn hG hS q := by
  unfold CV.groupedPoly
  symm
  exact EXT_piecesOn_prod hG.crossingGeometry hG'.crossingGeometry hs S S' q q' hX hX' _ _ hPH

theorem EXT_Omega1_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')} (hS : S ∈ CV.Ind hG.crossingGeometry)
    (hS' : S' ∈ CV.Ind hG'.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (q' : GeoComponent hG'.crossingGeometry S')
    (hR : CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q)
    (hw : CV.groupedWrithe hG' q' = CV.groupedWrithe hG q)
    (hp : CV.groupedPoly hn hG' hS' q' = CV.groupedPoly hn hG hS q) :
    CV.Omega1 hn hG' hS' q' = CV.Omega1 hn hG hS q := by
  unfold CV.Omega1 CV.slot
  rw [hR, hw, hp]

/-- Two pieces of one polygon with the same labels have the same polynomial (choice independence of
the piece polynomial, `homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`). -/
theorem EXT_pieceHomfly_eq_of_labels (hn : 3 ≤ n) (hD : CV.Diagrammatic P) {S S' : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hD.crossingGeometry) (hS' : S' ∈ CV.Ind hD.crossingGeometry)
    (H : CV.Piece hD.crossingGeometry S) (H' : CV.Piece hD.crossingGeometry S')
    (h : CV.pieceLabels hD.crossingGeometry S' H' = CV.pieceLabels hD.crossingGeometry S H) :
    CV.pieceHomfly hn hD hS' H' = CV.pieceHomfly hn hD hS H := by
  unfold CV.pieceHomfly CV.pieceDiagram
  exact CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn (CarrierGeometry.ofDiagrammatic hD)
    (CV.pieceSupport_geoIndependent hD hS' H') (CV.pieceSupport_geoIndependent hD hS H) _ _
    (by rw [CV.pieceCarrier_geoCarrierCrossings, CV.pieceCarrier_geoCarrierCrossings, h])

/-- The reindexing of the exterior factor along the carrier correspondence. -/
theorem EXT_exteriorFactor_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry) (e f g : ZMod n)
    (hcomm : ∀ a, ¬ EXT_TriVisit e f g a → ¬ EXT_TriVisit e f g (geoSmoothingSuccessor hG.crossingGeometry S a) →
      geoSmoothingSuccessor hG'.crossingGeometry S' (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor hG.crossingGeometry S a))
    (hcomm' : ∀ b', ¬ EXT_TriVisit e f g ((markTransport hs).symm b') →
      ¬ EXT_TriVisit e f g ((markTransport hs).symm (geoSmoothingSuccessor hG'.crossingGeometry S' b')) →
      geoSmoothingSuccessor hG.crossingGeometry S ((markTransport hs).symm b') =
        (markTransport hs).symm (geoSmoothingSuccessor hG'.crossingGeometry S' b'))
    (hval : ∀ q : GeoComponent hG.crossingGeometry S, TriangleDisjoint hG.crossingGeometry S e f g q →
      CV.weight hG'.crossingGeometry S' (EXT_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' q) *
        CV.Omega1 hn hG' hS' (EXT_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' q) =
      CV.weight hG.crossingGeometry S q * CV.Omega1 hn hG hS q) :
    exteriorFactor hn hG' hS' e f g = exteriorFactor hn hG hS e f g := by
  classical
  have hcomm₁ : ∀ a, (fun a => ¬ EXT_TriVisit e f g a) a →
      (fun a => ¬ EXT_TriVisit e f g a) (geoSmoothingSuccessor hG.crossingGeometry S a) →
      geoSmoothingSuccessor hG'.crossingGeometry S' (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor hG.crossingGeometry S a) := hcomm
  have hcomm₂ : ∀ b', (fun a => ¬ EXT_TriVisit e f g a) ((markTransport hs).symm b') →
      (fun a => ¬ EXT_TriVisit e f g a)
        ((markTransport hs).symm (geoSmoothingSuccessor hG'.crossingGeometry S' b')) →
      geoSmoothingSuccessor hG.crossingGeometry S ((markTransport hs).symm b') =
        (markTransport hs).symm (geoSmoothingSuccessor hG'.crossingGeometry S' b') := hcomm'
  -- the avoiding predicate on `P'`
  have hav' : ∀ q : GeoComponent hG.crossingGeometry S, TriangleDisjoint hG.crossingGeometry S e f g q →
      TriangleDisjoint hG'.crossingGeometry S' e f g
        (EXT_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' q) := by
    intro q hq
    rw [EXT_triangleDisjoint_iff] at hq ⊢
    have h := EXT_corr_avoids hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' _ hcomm₁ q hq
    intro b' hb'
    have this : ¬ EXT_TriVisit e f g ((markTransport hs).symm b') := h b' hb'
    rwa [EXT_triVisit_markTransport_symm] at this
  have hav : ∀ q' : GeoComponent hG'.crossingGeometry S', TriangleDisjoint hG'.crossingGeometry S' e f g q' →
      TriangleDisjoint hG.crossingGeometry S e f g
        (EXT_corr hG'.crossingGeometry hG.crossingGeometry (markTransport hs).symm S' S q') := by
    intro q' hq'
    rw [EXT_triangleDisjoint_iff] at hq' ⊢
    have hq'' : EXT_Avoids hG'.crossingGeometry S' (fun b' => ¬ EXT_TriVisit e f g ((markTransport hs).symm b')) q' := by
      intro b' hb'
      show ¬ EXT_TriVisit e f g ((markTransport hs).symm b')
      rw [EXT_triVisit_markTransport_symm]
      exact hq' b' hb'
    have h := EXT_corr_avoids hG'.crossingGeometry hG.crossingGeometry (markTransport hs).symm S' S _ hcomm₂ q' hq''
    intro b hb
    have this : ¬ EXT_TriVisit e f g ((markTransport hs).symm ((markTransport hs).symm.symm b)) := h b hb
    rwa [Equiv.symm_symm, Equiv.symm_apply_apply] at this
  unfold exteriorFactor
  symm
  refine Finset.prod_nbij' (EXT_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S')
    (EXT_corr hG'.crossingGeometry hG.crossingGeometry (markTransport hs).symm S' S) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨Finset.mem_univ _, hav' q hq.2⟩
  · intro q' hq'
    rw [Finset.mem_filter] at hq' ⊢
    exact ⟨Finset.mem_univ _, hav q' hq'.2⟩
  · intro q hq
    rw [Finset.mem_filter, EXT_triangleDisjoint_iff] at hq
    exact EXT_corr_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' _ hcomm₁ hcomm₂ q hq.2
  · intro q' hq'
    rw [Finset.mem_filter, EXT_triangleDisjoint_iff] at hq'
    have hq'' : EXT_Avoids hG'.crossingGeometry S' (fun b' => ¬ EXT_TriVisit e f g ((markTransport hs).symm b')) q' := by
      intro b' hb'
      show ¬ EXT_TriVisit e f g ((markTransport hs).symm b')
      rw [EXT_triVisit_markTransport_symm]
      exact hq'.2 b' hb'
    exact EXT_corr_corr hG'.crossingGeometry hG.crossingGeometry (markTransport hs).symm S' S _ hcomm₂
      (by simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using hcomm₁) q' hq''
  · intro q hq
    rw [Finset.mem_filter] at hq
    exact (hval q hq.2).symm

end EXTCarrierData

section EXTSamePolygon

variable {P : LabelledTuple n}

omit [NeZero n] in
theorem EXT_markTransport_symm_self (hs : ∀ s, IsCrossing P s ↔ IsCrossing P s) (b : Mark P) :
    (markTransport hs).symm b = b := by
  cases b <;> rfl

omit [NeZero n] in
theorem EXT_map_self (hs : ∀ s, IsCrossing P s ↔ IsCrossing P s) (X : Finset (Crossing P)) :
    X.map (crossingTransport hs).toEmbedding = X := by
  ext x
  rw [Finset.mem_map_equiv]
  exact Iff.rfl

/-- Smoothing the triangle crossings of `A` as well as `Q` changes the successor only at the triangle
visits (`geoSmoothingSuccessor_union_of_disjoint`). -/
theorem EXT_succ_union (hP : CrossingGeometry P) {Q A : Finset (Crossing P)} (hQA : Disjoint Q A)
    {e f g : ZMod n} (hAT : ∀ x ∈ A, x.val ∈ triangleSupports e f g) (a : Mark P)
    (ha : ¬ EXT_TriVisit e f g a) :
    geoSmoothingSuccessor hP (Q ∪ A) a = geoSmoothingSuccessor hP Q a := by
  have h : geoSmoothingSuccessor hP (Q ∪ A) =
      (selectedMarkPerm A).trans (geoSmoothingSuccessor hP Q) := by
    convert geoSmoothingSuccessor_union_of_disjoint hP Q A hQA using 3
    congr 1
    exact Subsingleton.elim _ _
  rw [h, Equiv.trans_apply]
  congr 1
  cases a with
  | inl i => rfl
  | inr v =>
    rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem]
    intro hv
    exact ha (hAT v.1 hv)

/-- **Fibre stability of the exterior factor at one polygon**: the exterior factor of the row `Q ∪ A`
equals that of the base row `Q` (R-EXTERIOR-1, proof §1–§3). -/
theorem EXT_exteriorFactor_eq_base (hn : 3 ≤ n) (hG : CV.Generic P) {Q A : Finset (Crossing P)}
    {e f g : ZMod n} (hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g)
    (hAT : ∀ x ∈ A, x.val ∈ triangleSupports e f g)
    (hA : Q ∪ A ∈ CV.Ind hG.crossingGeometry) (hQ : Q ∈ CV.Ind hG.crossingGeometry) :
    exteriorFactor hn hG hQ e f g = exteriorFactor hn hG hA e f g := by
  classical
  set hP := hG.crossingGeometry
  set hs : ∀ s, IsCrossing P s ↔ IsCrossing P s := fun _ => Iff.rfl
  have hQA : Disjoint Q A := by
    rw [Finset.disjoint_left]
    intro x hxQ hxA
    exact hQT x hxQ (hAT x hxA)
  have hcomm : ∀ a, ¬ EXT_TriVisit e f g a →
      ¬ EXT_TriVisit e f g (geoSmoothingSuccessor hP (Q ∪ A) a) →
      geoSmoothingSuccessor hP Q (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor hP (Q ∪ A) a) := by
    intro a ha _
    rw [markTransport_self, markTransport_self, EXT_succ_union hP hQA hAT a ha]
  have hcomm' : ∀ b', ¬ EXT_TriVisit e f g ((markTransport hs).symm b') →
      ¬ EXT_TriVisit e f g ((markTransport hs).symm (geoSmoothingSuccessor hP Q b')) →
      geoSmoothingSuccessor hP (Q ∪ A) ((markTransport hs).symm b') =
        (markTransport hs).symm (geoSmoothingSuccessor hP Q b') := by
    intro b' hb' _
    rw [EXT_markTransport_symm_self] at hb' ⊢
    rw [EXT_markTransport_symm_self, EXT_succ_union hP hQA hAT b' hb']
  refine EXT_exteriorFactor_eq hn hG hG hs hA hQ e f g hcomm hcomm' ?_
  intro q hq
  set q' := EXT_corr hP hP (markTransport hs) (Q ∪ A) Q q
  have hqav : EXT_Avoids hP (Q ∪ A) (fun a => ¬ EXT_TriVisit e f g a) q :=
    (EXT_triangleDisjoint_iff hP (Q ∪ A) e f g q).mp hq
  have hblock : ∀ b, geoOwner hP Q (markTransport hs b) = q' ↔ geoOwner hP (Q ∪ A) b = q :=
    EXT_corr_iff hP hP (markTransport hs) (Q ∪ A) Q _ hcomm q hqav
  have hlist : (geoComponentMarkList hP (Q ∪ A) q).map (markTransport hs) = geoComponentMarkList hP Q q' := by
    refine EXT_markList_map hP hP (markTransport hs) (Q ∪ A) Q q q' hblock ?_
    intro a b _ _
    rw [markTransport_self, markTransport_self]
  have hcorner : ∀ a, geoOwner hP (Q ∪ A) a = q →
      (IsTrueCorner Q (markTransport hs a) ↔ IsTrueCorner (Q ∪ A) a) := by
    intro a ha
    rw [markTransport_self]
    cases a with
    | inl i => exact Iff.rfl
    | inr v =>
      rw [isTrueCorner_visit, isTrueCorner_visit, Finset.mem_union]
      have hv : v.1 ∉ A := fun hvA => hqav _ ha (hAT v.1 hvA)
      exact ⟨Or.inl, fun h => h.resolve_right hv⟩
  have hcl : (geoComponentCornerList hP (Q ∪ A) q).map (markTransport hs) =
      geoComponentCornerList hP Q q' :=
    EXT_cornerList_map hP hP (markTransport hs) (Q ∪ A) Q q q' hlist hcorner
  have hc := EXT_cornerCount_eq hP hP (markTransport hs) (Q ∪ A) Q q q' hcl
  have hpoly : geoCornerPolygon hP Q q' = geoRecast hc (geoCornerPolygon hP (Q ∪ A) q) :=
    EXT_cornerPolygon_eq_self hP (markTransport hs) (markTransport_self hs) (Q ∪ A) Q q q' hcl
  have hsel : ∀ x : Crossing P, (∀ v : Visit P, v.1 = x → geoOwner hP (Q ∪ A) (Sum.inr v) = q) →
      (crossingTransport hs x ∈ Q ↔ x ∈ Q ∪ A) := by
    intro x hx
    obtain ⟨i, -, -⟩ := crossing_visits_exist x
    have hxT : x.val ∉ triangleSupports e f g := hqav _ (hx ⟨x, i⟩ rfl)
    have hxA : x ∉ A := fun hxA => hxT (hAT x hxA)
    show x ∈ Q ↔ x ∈ Q ∪ A
    rw [Finset.mem_union]
    exact ⟨Or.inl, fun h => h.resolve_right hxA⟩
  have hX' : geoCarrierCrossings hP Q q' =
      (geoCarrierCrossings hP (Q ∪ A) q).map (crossingTransport hs).toEmbedding :=
    EXT_carrierCrossings_map hP hP hs (Q ∪ A) Q q q' hblock hsel
  have hX : EXT_PieceSetting hP hP hs (Q ∪ A) Q (geoCarrierCrossings hP (Q ∪ A) q) :=
    EXT_pieceSetting hP hP hs hA hQ q q' hX' (fun _ _ _ _ => Iff.rfl)
  have hweight : CV.weight hP Q q' = CV.weight hP (Q ∪ A) q := by
    refine EXT_weight_eq hP hP (Q ∪ A) Q q q' hc ?_
    intro k
    rw [hpoly, turn_geoRecast]
  have hR : CV.carrierR hn hG hQ q' = CV.carrierR hn hG hA q := by
    refine EXT_carrierR_eq hn hG hG hA hQ q q' ?_
    rw [hpoly, rotationNumber_geoRecast]
  have hw : CV.groupedWrithe hG q' = CV.groupedWrithe hG q :=
    EXT_groupedWrithe_eq hG hG hs q q' hX hX'
  have hp : CV.groupedPoly hn hG hQ q' = CV.groupedPoly hn hG hA q := by
    refine EXT_groupedPoly_eq hn hG hG hs hA hQ q q' hX hX' ?_
    intro H H' _ h
    rw [EXT_map_self] at h
    exact EXT_pieceHomfly_eq_of_labels hn (hG.diagrammatic hn) hA hQ H H' h
  rw [hweight, EXT_Omega1_eq hn hG hG hA hQ q q' hR hw hp]

/-- **Row 168, field `independent_of_A`**: "Then `C_{Q,sigma}(A)` is independent of `A`". -/
theorem EXT_168_independent_of_A (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ A A' : Finset (Crossing (E.curve t)),
      A ⊆ triangleCrossings (E.curve t) e f g → A' ⊆ triangleCrossings (E.curve t) e f g →
      ∀ (hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1)) (hA' : Q ∪ A' ∈ CV.Ind (geomAt E t ht.1)),
        exteriorFactor hn (genericAt E t ht.1) hA e f g =
          exteriorFactor hn (genericAt E t ht.1) hA' e f g := by
  intro t ht Q hQ A A' hAT hAT' hA hA'
  have hQ' : Q ∈ CV.Ind (geomAt E t ht.1) := mem_Ind_of_mem_outsideSupports hQ
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := by
    intro x hx hxT
    exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  have h1 := EXT_exteriorFactor_eq_base hn (genericAt E t ht.1) hQT
    (fun x hx => (P1.mem_triangleCrossings x).mp (hAT hx)) hA hQ'
  have h2 := EXT_exteriorFactor_eq_base hn (genericAt E t ht.1) hQT
    (fun x hx => (P1.mem_triangleCrossings x).mp (hAT' hx)) hA' hQ'
  rw [← h1, ← h2]

end EXTSamePolygon

section EXTWall

variable {P P' : LabelledTuple n}

/-- An empty oriented gap between distinct members of a finite linear order identifies the
sorted-list successor, including the last/first cut (a verbatim port of the accepted
`SM.sorted_next_of_no_cyclic_between`, SM/GaussNextFromEmptyArc.lean, which is not in the import
closure of this file; the same port as `SEL_sorted_next_of_no_cyclic_between`, which is declared later in
this file). -/
theorem EXT_sorted_next_of_no_cyclic_between {α : Type*} [LinearOrder α]
    (s : Finset α) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hgap : ∀ x ∈ s,
      ¬ ((a < x ∧ x < b) ∨ (x < b ∧ b < a) ∨ (b < a ∧ a < x))) :
    s.sort.next a ((Finset.mem_sort _).mpr ha) = b := by
  let e := s.orderIsoOfFin rfl
  let ia := e.symm ⟨a, ha⟩
  let ib := e.symm ⟨b, hb⟩
  have hcoe {i j : Fin s.card} (h : i < j) : (e i).val < (e j).val :=
    Subtype.coe_lt_coe.mpr (e.strictMono h)
  have hsize : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hne : ia.val ≠ ib.val := by
    intro he
    apply hab
    have hv := congrArg (fun k : Fin s.card => (e k).val) (Fin.ext he : ia = ib)
    simpa only [ia, ib, e.apply_symm_apply] using hv
  have haN := ia.isLt
  have hbN := ib.isLt
  have hindex : ib.val = (ia.val + 1) % s.card := by
    by_cases hcut : ia.val + 1 < s.card
    · let j : Fin s.card := ⟨ia.val + 1, hcut⟩
      have haj : a < (e j).val := by
        have h : ia < j := by change ia.val < ia.val + 1; omega
        simpa only [ia, e.apply_symm_apply] using hcoe h
      have hnone := hgap (e j).val (e j).property
      have hnotBack : ¬ ib.val < ia.val := by
        intro h
        have hba : b < a := by
          simpa only [ia, ib, e.apply_symm_apply] using
            hcoe (show ib < ia from h)
        exact hnone (Or.inr (Or.inr ⟨hba, haj⟩))
      have hnotGap : ¬ j.val < ib.val := by
        intro h
        have hjb : (e j).val < b := by
          simpa only [ib, e.apply_symm_apply] using
            hcoe (show j < ib from h)
        exact hnone (Or.inl ⟨haj, hjb⟩)
      have hj : j.val = ia.val + 1 := rfl
      rw [Nat.mod_eq_of_lt hcut]
      omega
    · have hlast : ia.val + 1 = s.card := by omega
      let j : Fin s.card := ⟨0, hsize⟩
      have hnone := hgap (e j).val (e j).property
      have hnotPos : ¬ 0 < ib.val := by
        intro h
        have hjb : (e j).val < b := by
          simpa only [ib, e.apply_symm_apply] using
            hcoe (show j < ib from h)
        have hba : b < a := by
          have hi : ib < ia := by change ib.val < ia.val; omega
          simpa only [ia, ib, e.apply_symm_apply] using hcoe hi
        exact hnone (Or.inr (Or.inl ⟨hjb, hba⟩))
      rw [hlast, Nat.mod_self]
      omega
  let nextIndex : Fin s.card := ⟨(ia.val + 1) % s.card, Nat.mod_lt _ hsize⟩
  have hvalue : s.sort.next a ((Finset.mem_sort _).mpr ha) = (e nextIndex).val := by
    rw [List.next_eq_getElem]
    simp only [e, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply, Finset.length_sort]
    rfl
  have hi : nextIndex = ib := Fin.ext hindex.symm
  rw [hvalue, hi]
  simp only [ib, e.apply_symm_apply]


/-- On the sorted mark list, key order is index order. -/
theorem EXT_geoMarkList_key_lt_iff (hP : CrossingGeometry P) {i j : ℕ}
    (hi : i < (geoMarkList hP).length) (hj : j < (geoMarkList hP).length) :
    geoMarkKey hP ((geoMarkList hP)[i]'hi) < geoMarkKey hP ((geoMarkList hP)[j]'hj) ↔ i < j := by
  have hs := List.pairwise_iff_getElem.mp (geoMarkList_sorted hP)
  have hnd : ∀ (i j : ℕ) (hi : i < (geoMarkList hP).length) (hj : j < (geoMarkList hP).length),
      i < j → (geoMarkList hP)[i] ≠ (geoMarkList hP)[j] :=
    List.pairwise_iff_getElem.mp (geoMarkList_nodup hP)
  constructor
  · intro h
    by_contra hij
    have hij' : j ≤ i := not_lt.mp hij
    rcases hij'.lt_or_eq with hlt | heq
    · exact absurd h (not_lt.mpr (hs j i hj hi hlt))
    · subst heq
      exact lt_irrefl _ h
  · intro hij
    exact lt_of_le_of_ne (hs i j hi hj hij)
      (fun h => hnd i j hi hj hij (geoMarkKey_injective hP h))

/-- No mark lies strictly between a mark and its `ρ`-successor. -/
theorem EXT_not_between_succ (hP : CrossingGeometry P) (a x : Mark P) :
    ¬ Link.cycBetween (geoMarkKey hP a) (geoMarkKey hP x) (geoMarkKey hP (geoMarkSuccessor hP a)) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP a)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP x)
  rw [geoMarkSuccessor_getElem hP i hi]
  have hlen : 0 < (geoMarkList hP).length := lt_of_le_of_lt (Nat.zero_le i) hi
  have hk : (i + 1) % (geoMarkList hP).length < (geoMarkList hP).length := Nat.mod_lt _ hlen
  intro hc
  unfold Link.cycBetween at hc
  rw [EXT_geoMarkList_key_lt_iff hP hi hj, EXT_geoMarkList_key_lt_iff hP hj hk,
    EXT_geoMarkList_key_lt_iff hP hk hi] at hc
  by_cases hlt : i + 1 < (geoMarkList hP).length
  · rw [Nat.mod_eq_of_lt hlt] at hc
    omega
  · have h1 : i + 1 = (geoMarkList hP).length := by omega
    rw [h1, Nat.mod_self] at hc
    omega

omit [NeZero n] in
theorem EXT_markTransport_vertex (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (i : ZMod n) :
    markTransport hs (Sum.inl i) = Sum.inl i := rfl

/-- **Key order across the wall**: the traversal order of two marks is carried by the canonical
identification unless they are the two visits of a bundle pair on their common edge
(R-LOC-2 (2)–(3), `ExactTriangleVisitOrders`). -/
theorem EXT_key_lt_wall (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n}
    (hgw : ExactTriangleVisitOrders P P' e f g hs) (a b : Mark P)
    (hab : ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w → v.1.val ∪ w.1.val ≠ {e, f, g}) :
    geoMarkKey hP a < geoMarkKey hP b ↔
      geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs b) := by
  unfold geoMarkKey
  rw [traversalKey_lt_iff, traversalKey_lt_iff]
  cases a with
  | inl i =>
    cases b with
    | inl j => exact Iff.rfl
    | inr w =>
      have h0 : 0 < visitParameter w :=
        (crossingParameter_interior_of_geometry hP w.1 w.2.val w.2.property).1
      have h0' : 0 < visitParameter (visitTransport hs w) :=
        (crossingParameter_interior_of_geometry hP' _ _ _).1
      rw [EXT_markTransport_vertex, markTransport_visit, geoMarkPosition_vertex, geoMarkPosition_vertex,
        geoMarkPosition_visit, geoMarkPosition_visit]
      simp only [geometricVisitPosition_edge, geometricVisitPosition_parameter, visitTransport_edge, h0, h0',
        and_true]
  | inr v =>
    cases b with
    | inl j =>
      have h0 : 0 < visitParameter v :=
        (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h0' : 0 < visitParameter (visitTransport hs v) :=
        (crossingParameter_interior_of_geometry hP' _ _ _).1
      rw [EXT_markTransport_vertex, markTransport_visit, geoMarkPosition_vertex, geoMarkPosition_vertex,
        geoMarkPosition_visit, geoMarkPosition_visit]
      simp only [geometricVisitPosition_edge, geometricVisitPosition_parameter, visitTransport_edge]
      have hn0 : ¬ visitParameter v < 0 := not_lt.mpr h0.le
      have hn0' : ¬ visitParameter (visitTransport hs v) < 0 := not_lt.mpr h0'.le
      simp only [hn0, hn0', and_false, or_false]
    | inr w =>
      rw [markTransport_visit, markTransport_visit, geoMarkPosition_visit, geoMarkPosition_visit,
        geoMarkPosition_visit, geoMarkPosition_visit]
      simp only [geometricVisitPosition_edge, geometricVisitPosition_parameter, visitTransport_edge]
      apply or_congr Iff.rfl
      apply and_congr_right
      intro he
      exact (hgw v w he).2 (hab v w rfl rfl)

omit [NeZero n] in
/-- A good mark and any mark are never a bundle pair. -/
theorem EXT_hab_of_good_left {e f g : ZMod n} {a b : Mark P} (ha : ¬ EXT_TriVisit e f g a) :
    ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w → v.1.val ∪ w.1.val ≠ {e, f, g} := by
  rintro v w rfl _ hu
  exact ha (L.mem_triangleSupports_of_union hu).1

omit [NeZero n] in
theorem EXT_hab_of_good_right {e f g : ZMod n} {a b : Mark P} (hb : ¬ EXT_TriVisit e f g b) :
    ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w → v.1.val ∪ w.1.val ≠ {e, f, g} := by
  rintro v w _ rfl hu
  exact hb (L.mem_triangleSupports_of_union hu).2

/-- The marked circle has at least two marks (`n ≥ 3` vertices). -/
theorem EXT_two_le_geoMarkList_length (hn : 3 ≤ n) (hP : CrossingGeometry P) :
    2 ≤ (geoMarkList hP).length := by
  classical
  have h01 : (Sum.inl (0 : ZMod n) : Mark P) ≠ Sum.inl 1 := by
    intro h
    have h' : (0 : ZMod n) = 1 := Sum.inl_injective h
    have : Fact (1 < n) := ⟨by omega⟩
    exact zero_ne_one h'
  have hsub : ({Sum.inl 0, Sum.inl 1} : Finset (Mark P)) ⊆ (geoMarkList hP).toFinset := by
    intro x _
    exact List.mem_toFinset.mpr (mem_geoMarkList hP x)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair h01, List.toFinset_card_of_nodup (geoMarkList_nodup hP)] at hcard
  exact hcard

/-- `ρ` has no fixed point. -/
theorem EXT_geoMarkSuccessor_ne (hn : 3 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    geoMarkSuccessor hP a ≠ a := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP a)
  rw [geoMarkSuccessor_getElem hP i hi]
  have hnd : ∀ (i j : ℕ) (hi : i < (geoMarkList hP).length) (hj : j < (geoMarkList hP).length),
      i < j → (geoMarkList hP)[i] ≠ (geoMarkList hP)[j] :=
    List.pairwise_iff_getElem.mp (geoMarkList_nodup hP)
  have hlen2 := EXT_two_le_geoMarkList_length hn hP
  have hlen : 0 < (geoMarkList hP).length := by omega
  intro h
  by_cases hlt : i + 1 < (geoMarkList hP).length
  · have hk : (i + 1) % (geoMarkList hP).length = i + 1 := Nat.mod_eq_of_lt hlt
    have h' : (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'(Nat.mod_lt _ hlen) =
        (geoMarkList hP)[i + 1]'hlt :=
      geo_getElem_congr _ _ rfl _ _ _ _ hk
    exact hnd i (i + 1) hi hlt (Nat.lt_succ_self i) (h'.symm.trans h).symm
  · have h1 : (i + 1) % (geoMarkList hP).length = 0 := by
      have : i + 1 = (geoMarkList hP).length := by omega
      rw [this, Nat.mod_self]
    have h' : (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'(Nat.mod_lt _ hlen) =
        (geoMarkList hP)[0]'hlen :=
      geo_getElem_congr _ _ rfl _ _ _ _ h1
    have hi0 : 0 < i := by omega
    exact hnd 0 i hlen hi hi0 (h'.symm.trans h)

/-- **`ρ` across the wall at a good mark with a good successor**: erasing the six triangle visits gives
the same marked traversal word on both sides (R-EXTERIOR-1 §4), so the successor of a good mark whose
successor is good is carried by the identification. -/
theorem EXT_markSucc_wall (hn : 3 ≤ n) (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n}
    (hgw : ExactTriangleVisitOrders P P' e f g hs) (a : Mark P)
    (ha : ¬ EXT_TriVisit e f g a) (hρ : ¬ EXT_TriVisit e f g (geoMarkSuccessor hP a)) :
    geoMarkSuccessor hP' (markTransport hs a) = markTransport hs (geoMarkSuccessor hP a) := by
  classical
  let _ := geoMarkLinearOrder hP'
  have hne : markTransport hs a ≠ markTransport hs (geoMarkSuccessor hP a) :=
    fun h => EXT_geoMarkSuccessor_ne hn hP a ((markTransport hs).injective h).symm
  have hgap : ∀ x ∈ (Finset.univ : Finset (Mark P')),
      ¬ ((markTransport hs a < x ∧ x < markTransport hs (geoMarkSuccessor hP a)) ∨
        (x < markTransport hs (geoMarkSuccessor hP a) ∧
          markTransport hs (geoMarkSuccessor hP a) < markTransport hs a) ∨
        (markTransport hs (geoMarkSuccessor hP a) < markTransport hs a ∧ markTransport hs a < x)) := by
    intro x _
    obtain ⟨y, rfl⟩ := (markTransport hs).surjective x
    have h1 := EXT_key_lt_wall hP hP' hgw a y (EXT_hab_of_good_left ha)
    have h2 := EXT_key_lt_wall hP hP' hgw y (geoMarkSuccessor hP a) (EXT_hab_of_good_right hρ)
    have h3 := EXT_key_lt_wall hP hP' hgw (geoMarkSuccessor hP a) a (EXT_hab_of_good_left hρ)
    change ¬ ((geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs y) ∧
        geoMarkKey hP' (markTransport hs y) < geoMarkKey hP' (markTransport hs (geoMarkSuccessor hP a))) ∨
      (geoMarkKey hP' (markTransport hs y) < geoMarkKey hP' (markTransport hs (geoMarkSuccessor hP a)) ∧
        geoMarkKey hP' (markTransport hs (geoMarkSuccessor hP a)) < geoMarkKey hP' (markTransport hs a)) ∨
      (geoMarkKey hP' (markTransport hs (geoMarkSuccessor hP a)) < geoMarkKey hP' (markTransport hs a) ∧
        geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs y)))
    rw [← h1, ← h2, ← h3]
    exact EXT_not_between_succ hP a y
  have hnext := EXT_sorted_next_of_no_cyclic_between (Finset.univ : Finset (Mark P'))
    (Finset.mem_univ _) (Finset.mem_univ _) hne hgap
  rw [geoMarkSuccessor_apply, geoNextMark_eq_list_next]
  convert hnext using 2
  rfl

/-- The selected exchange preserves the bad marks (a twin visit belongs to the same crossing). -/
theorem EXT_triVisit_selectedMarkPerm {e f g : ZMod n} (S : Finset (Crossing P)) (a : Mark P) :
    EXT_TriVisit e f g (selectedMarkPerm S a) ↔ EXT_TriVisit e f g a := by
  cases a with
  | inl i => exact Iff.rfl
  | inr v =>
    rw [selectedMarkPerm_visit]
    show (selectedVisitTwin S v).1.val ∈ triangleSupports e f g ↔ v.1.val ∈ triangleSupports e f g
    unfold selectedVisitTwin
    split_ifs <;> exact Iff.rfl

/-- **`ρ_Q` across the wall** at a good mark with a good successor (any support `Q`). -/
theorem EXT_succ_wall (hn : 3 ≤ n) (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n}
    (hgw : ExactTriangleVisitOrders P P' e f g hs) (Q : Finset (Crossing P)) (a : Mark P)
    (ha : ¬ EXT_TriVisit e f g a) (hρ : ¬ EXT_TriVisit e f g (geoSmoothingSuccessor hP Q a)) :
    geoSmoothingSuccessor hP' (transportSupport hs Q) (markTransport hs a) =
      markTransport hs (geoSmoothingSuccessor hP Q a) := by
  rw [geoSmoothingSuccessor_apply] at hρ
  rw [geoSmoothingSuccessor_apply, geoSmoothingSuccessor_apply, selectedMarkPerm_markTransport]
  exact EXT_markSucc_wall hn hP hP' hgw _ ((EXT_triVisit_selectedMarkPerm Q a).not.mpr ha) hρ

omit [NeZero n] in
theorem EXT_markTransport_symm_eq (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (b' : Mark P') :
    (markTransport hs).symm b' = markTransport (fun s => (hs s).symm) b' := by
  cases b' <;> rfl

omit [NeZero n] in
theorem EXT_transportSupport_symm (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (Q : Finset (Crossing P)) :
    transportSupport (fun s => (hs s).symm) (transportSupport hs Q) = Q := by
  ext x
  unfold transportSupport
  rw [Finset.mem_map_equiv, Finset.mem_map_equiv]
  exact Iff.rfl

/-- **Corner turns across the wall**: at a vertex corner the turn is `τ_i` of the polygon, at a
smoothing corner the crossing sign; both are wall-invariant on the punctured neighbourhood. -/
theorem EXT_turn_wall (hn : 3 ≤ n) (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hP)
    (hS' : transportSupport hs S ∈ CV.Ind hP') (q : GeoComponent hP S)
    (q' : GeoComponent hP' (transportSupport hs S))
    (hcl : (geoComponentCornerList hP S q).map (markTransport hs) =
      geoComponentCornerList hP' (transportSupport hs S) q')
    (hturnP : ∀ i, turn P' i = turn P i)
    (hsign : ∀ v : Visit P, v.1 ∈ S →
      crossingSign P' v.2.val (visitTwin v).2.val = crossingSign P v.2.val (visitTwin v).2.val) :
    ∀ k, turn (geoCornerPolygon hP' (transportSupport hs S) q') k =
      turn (geoCornerPolygon hP S q)
        (Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' (markTransport hs) S _ q q' hcl)) k) := by
  intro k
  have hm := EXT_cornerMark_eq' hP hP' (markTransport hs) S _ q q' hcl k
  set j := Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' (markTransport hs) S _ q q' hcl)) k
  obtain ⟨_, hcorner⟩ := geoCornerMark_mem hP S q j
  rcases hmark : geoCornerMark hP S q j with i | v
  · rw [hmark, EXT_markTransport_vertex] at hm
    rw [CV.turn_vertex_of_traced hP' _ hn q' (CV.carrierword_traced hP' hS' q') k i hm,
      CV.turn_vertex_of_traced hP S hn q (CV.carrierword_traced hP hS q) j i hmark]
    exact hturnP i
  · rw [hmark, markTransport_visit] at hm
    rw [hmark, isTrueCorner_visit] at hcorner
    have hv' : (visitTransport hs v).1 ∈ transportSupport hs S := by
      rw [visitTransport_crossing, mem_transportSupport_iff]
      exact hcorner
    rw [CV.turn_visit_of_traced hP' _ hn q' (CV.carrierword_traced hP' hS' q') k _ hm hv',
      CV.turn_visit_of_traced hP S hn q (CV.carrierword_traced hP hS q) j v hmark hcorner,
      visitTransport_edge, ← visitTransport_visitTwin, visitTransport_edge]
    exact hsign v hcorner

end EXTWall

section EXTGuard

variable {E : CV.Event n}

/-- Sign constancy at a parameter `u` of the members outside the forced bundle: `G1` at every vertex and
`G5` at every crossing pair (lem:guardconst). -/
def EXT_GuardAt (E : CV.Event n) (u : E.Parameter) : Prop :=
  (∀ i : ZMod n, CV.G1 (E.curve u) i ≠ 0 ∧
    SignType.sign (CV.G1 (E.curve u) i) = SignType.sign (CV.G1 E.center i)) ∧
  (∀ i j : ZMod n, IsCrossing E.center {i, j} →
    CV.G5 (E.curve u) i j ≠ 0 ∧ SignType.sign (CV.G5 (E.curve u) i j) = SignType.sign (CV.G5 E.center i j))

theorem EXT_curve_eq_center (u : E.Parameter) (hu : u.val = 0) : E.curve u = E.center := by
  have : u = E.zeroParameter := Subtype.ext hu
  rw [this]
  rfl

/-- The four `G2` members of a remote pair are nonzero at every parameter (unconditional, outside `Z`). -/
theorem EXT_g2_ne_zero {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (u : E.Parameter) (a i : ZMod n) (h : i ≠ a ∧ i ≠ a + 1) : CV.G2 (E.curve u) a i ≠ 0 := by
  by_cases hu : u.val = 0
  · rw [EXT_curve_eq_center u hu]
    obtain ⟨t₀, ht₀⟩ := G1.exists_punctured_parameter E
    exact (CV.guardconst E (CV.Member.g2 a i h) ⟨t₀, ht₀, CV.Member.relevant_g2 _ a i h⟩
      (G1.g2_not_mem_zeroSet hE a i h)).1
  · exact (E.generic_punctured u hu).g2 h.1 h.2

/-- A crossing pair of one side is an active pair at every parameter, the centre included. -/
theorem EXT_crosses_all {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {t : E.Parameter} {i j : ZMod n} (hc : IsCrossing (E.curve t) {i, j}) (u : E.Parameter) :
    CV.Crosses (E.curve u) i j := by
  have hr : remote i j := crossing_pair_remote hc
  have hcu : IsCrossing (E.curve u) {i, j} := (hE.tripleEventData.crossing_set_constant t u _).mp hc
  obtain ⟨h0, h1, h2, h3'⟩ := remote_endpoints i j hr
  exact CV.crosses_of_meet hr ⟨EXT_g2_ne_zero hE u i j ⟨h0, h1⟩, EXT_g2_ne_zero hE u i (j + 1) ⟨h2, h3'⟩,
    EXT_g2_ne_zero hE u j i ⟨h0.symm, h2.symm⟩, EXT_g2_ne_zero hE u j (i + 1) ⟨h1.symm, h3'.symm⟩⟩
    ((isCrossing_pair _ i j hr).mp hcu)

/-- The Cramer parameter of an active pair is interior. -/
theorem EXT_edgeParameter_interior {P : LabelledTuple n} {i j : ZMod n} (hc : CV.Crosses P i j) :
    0 < edgeParameter P i j ∧ edgeParameter P i j < 1 := by
  obtain ⟨_, s, t, hs0, hs1, _, _, heq, hd⟩ := (CV.crosses_iff P i j).mp hc
  have h := (edgeParameters_of_intersection hd heq).1
  rw [h]
  exact ⟨hs0, hs1⟩

omit [NeZero n] in
theorem EXT_G5_swap (P : LabelledTuple n) (i j : ZMod n) : CV.G5 P i j = -CV.G5 P j i := by
  unfold CV.G5
  rw [det_swap]

/-- **The guard radius**: a radius on which `G1` at every vertex and `G5` at every crossing pair keep
their central signs (lem:guardconst, uniformly over the finitely many members). -/
theorem EXT_exists_guardRadius {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u := by
  rw [← E.eventually_center_iff_radius]
  obtain ⟨t₀, ht₀⟩ := G1.exists_punctured_parameter E
  apply Filter.Eventually.and
  · rw [Filter.eventually_all]
    intro i
    exact G1.eventually_sign_eq_of_not_mem (CV.Member.g1 i) ⟨t₀, ht₀, CV.Member.relevant_g1 _ i⟩
      (by rw [hE.1]; simp)
  · rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hc : IsCrossing E.center {i, j}
    · have hr : remote i j := crossing_pair_remote hc
      have hne : i ≠ j := (remote_endpoints i j hr).1.symm
      have hcross : CV.Crosses (E.curve t₀) i j := EXT_crosses_all hE hc t₀
      rcases CV.rep_lt_or_lt hne with hlt | hlt
      · have hev := G1.eventually_sign_eq_of_not_mem (CV.Member.g5 i j ⟨hr, hlt⟩)
          ⟨t₀, ht₀, Or.inr hcross⟩ (G1.g5_not_mem_zeroSet hE i j ⟨hr, hlt⟩)
        exact hev.mono fun u hu _ => hu
      · have hcross' : CV.Crosses (E.curve t₀) j i := EXT_crosses_all hE (by rw [Finset.pair_comm]; exact hc) t₀
        have hev := G1.eventually_sign_eq_of_not_mem (CV.Member.g5 j i ⟨remote_symm hr, hlt⟩)
          ⟨t₀, ht₀, Or.inr hcross'⟩ (G1.g5_not_mem_zeroSet hE j i ⟨remote_symm hr, hlt⟩)
        refine hev.mono fun u hu _ => ?_
        change CV.G5 (E.curve u) j i ≠ 0 ∧ SignType.sign (CV.G5 (E.curve u) j i) = SignType.sign (CV.G5 E.center j i) at hu
        rw [EXT_G5_swap (E.curve u) i j, EXT_G5_swap E.center i j, neg_ne_zero, Left.sign_neg, Left.sign_neg, hu.2]
        exact ⟨hu.1, rfl⟩
    · exact Filter.Eventually.of_forall fun u h => absurd h hc

/-- The vertex turns agree at any two guarded parameters. -/
theorem EXT_turn_eq_of_guard {u u' : E.Parameter} (hu : EXT_GuardAt E u) (hu' : EXT_GuardAt E u') (i : ZMod n) :
    turn (E.curve u') i = turn (E.curve u) i := by
  rw [turn_det, turn_det]
  exact ((hu'.1 i).2.trans (hu.1 i).2.symm)

/-- The crossing signs of a crossing pair agree at any two guarded parameters. -/
theorem EXT_G5_sign_eq_of_guard {u u' : E.Parameter} (hu : EXT_GuardAt E u) (hu' : EXT_GuardAt E u')
    {i j : ZMod n} (hc : IsCrossing E.center {i, j}) :
    SignType.sign (CV.G5 (E.curve u') i j) = SignType.sign (CV.G5 (E.curve u) i j) :=
  (hu'.2 i j hc).2.trans (hu.2 i j hc).2.symm

theorem EXT_det_pos_iff_of_guard {u u' : E.Parameter} (hu : EXT_GuardAt E u) (hu' : EXT_GuardAt E u')
    {i j : ZMod n} (hc : IsCrossing E.center {i, j}) :
    0 < det (edge (E.curve u) i) (edge (E.curve u) j) ↔ 0 < det (edge (E.curve u') i) (edge (E.curve u') j) := by
  have h := EXT_G5_sign_eq_of_guard hu hu' hc
  unfold CV.G5 at h
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

end EXTGuard

section EXTRecord

variable {P P' : LabelledTuple n}

/-- **Two carriers on the two sides with corresponding retained crossings have positive lifts with the same
HOMFLY polynomial** when the traversal order of the visits of those crossings and the divide signs at them
are carried by the identification: the identity on parent visits is a record isomorphism
(CV:def:record (a)–(d), assembled by `recordIsoOfData`) and the accepted `gausscode_polynomial` applies. -/
theorem EXT_homfly_wall (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
    (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
    (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
    (hX : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (hkey : ∀ v w : Visit P, v.1 ∈ geoCarrierCrossings hG.cg T q → w.1 ∈ geoCarrierCrossings hG.cg T q →
      (geometricVisitKey hG.cg v < geometricVisitKey hG.cg w ↔
        geometricVisitKey hG'.cg (visitTransport hs v) < geometricVisitKey hG'.cg (visitTransport hs w)))
    (hdet : ∀ v : Visit P, v.1 ∈ geoCarrierCrossings hG.cg T q →
      (0 < det (edge P v.2.val) (edge P (visitTwin v).2.val) ↔
        0 < det (edge P' v.2.val) (edge P' (visitTwin v).2.val))) :
    homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q) := by
  let ψ : {w : Visit P // w.1 ∈ geoCarrierCrossings hG.cg T q} ≃
      {w : Visit P' // w.1 ∈ geoCarrierCrossings hG'.cg T' q'} :=
    (visitTransport hs).subtypeEquiv fun w => by
      rw [hX, visitTransport_crossing, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  let Φ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit :=
    (CV.liftVisitEquiv hn hG hT q).trans (ψ.trans (CV.liftVisitEquiv hn hG' hT' q').symm)
  have hΦ : ∀ v, CV.liftVisit hn hG' hT' q' (Φ v) = visitTransport hs (CV.liftVisit hn hG hT q v) := by
    intro v
    show CV.liftVisit hn hG' hT' q'
      ((CV.liftVisitEquiv hn hG' hT' q').symm (ψ (CV.liftVisitEquiv hn hG hT q v))) = _
    rw [CV.liftVisit_symm]
    rfl
  have hmem : ∀ v, (CV.liftVisit hn hG hT q v).1 ∈ geoCarrierCrossings hG.cg T q :=
    CV.liftVisit_mem hn hG hT q
  have hdata : CV.IsRecordIsoData (geoPositiveLift hn hG hT q) (geoPositiveLift hn hG' hT' q') Φ :=
    { cyclic_order := fun v w u hb => by
        rw [CV.visitBetween_iff_key, hΦ, hΦ, hΦ]
        rw [CV.visitBetween_iff_key] at hb
        unfold Link.cycBetween at hb ⊢
        rw [← hkey _ _ (hmem v) (hmem w), ← hkey _ _ (hmem w) (hmem u), ← hkey _ _ (hmem u) (hmem v)]
        exact hb
      double_points :=
        (CV.carriesDoublePoints_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG' hT' q').record) Φ).2 fun v => by
          apply CV.liftVisit_injective hn hG' hT' q'
          change CV.liftVisit hn hG' hT' q' (Φ ((geoPositiveLift hn hG hT q).twin v)) =
            CV.liftVisit hn hG' hT' q' ((geoPositiveLift hn hG' hT' q').twin (Φ v))
          rw [hΦ, CV.liftVisit_twin, CV.liftVisit_twin, hΦ, visitTransport_visitTwin]
      over_under :=
        (CV.carriesOverUnder_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG' hT' q').record) Φ).2 fun v => by
          change (geoPositiveLift hn hG' hT' q').overBit (Φ v) = (geoPositiveLift hn hG hT q).overBit v
          rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΦ,
            visitTransport_edge, ← visitTransport_visitTwin, visitTransport_edge]
          exact (hdet _ (hmem v)).symm
      signs := fun v => by
        change (geoPositiveLift hn hG' hT' q').sign (Φ v).1 = (geoPositiveLift hn hG hT q).sign v.1
        rw [geoPositiveLift_sign, geoPositiveLift_sign] }
  exact (CV.gausscode_polynomial _ _ (geoPositiveLift_componentCount hn hG hT q)
    (geoPositiveLift_componentCount hn hG' hT' q')
    (CV.recordIsoOfData (geoPositiveLift_componentCount hn hG hT q)
      (geoPositiveLift_componentCount hn hG' hT' q') Φ hdata)).symm

/-- The piece polynomials of corresponding pieces with triangle-free labels agree across the wall. -/
theorem EXT_pieceHomfly_wall (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (hkey : ∀ v w : Visit P, v.1.val ∉ triangleSupports e f g → w.1.val ∉ triangleSupports e f g →
      (geometricVisitKey hG.crossingGeometry v < geometricVisitKey hG.crossingGeometry w ↔
        geometricVisitKey hG'.crossingGeometry (visitTransport hs v) <
          geometricVisitKey hG'.crossingGeometry (visitTransport hs w)))
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (H : CV.Piece hG.crossingGeometry S) (H' : CV.Piece hG'.crossingGeometry S')
    (hHT : ∀ c ∈ CV.pieceLabels hG.crossingGeometry S H, c.val ∉ triangleSupports e f g)
    (hH' : CV.pieceLabels hG'.crossingGeometry S' H' =
      (CV.pieceLabels hG.crossingGeometry S H).map (crossingTransport hs).toEmbedding) :
    CV.pieceHomfly hn (hG'.diagrammatic hn) hS' H' = CV.pieceHomfly hn (hG.diagrammatic hn) hS H := by
  unfold CV.pieceHomfly CV.pieceDiagram
  refine EXT_homfly_wall hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
    (CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn)) hs
    (CV.pieceSupport_geoIndependent (hG.diagrammatic hn) hS H)
    (CV.pieceSupport_geoIndependent (hG'.diagrammatic hn) hS' H') _ _ ?_ ?_ ?_
  · rw [CV.pieceCarrier_geoCarrierCrossings, CV.pieceCarrier_geoCarrierCrossings]
    exact hH'
  · intro v w hv hw
    rw [CV.pieceCarrier_geoCarrierCrossings] at hv hw
    exact hkey v w (hHT _ hv) (hHT _ hw)
  · intro v hv
    have hc : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rwa [visit_crossing_val_eq_pair v] at h
    exact hdet _ _ hc

end EXTRecord

section EXTRotation

variable {E : CV.Event n}

theorem EXT_seg_mem (t t' : E.Parameter) (u : unitInterval) :
    t.val + u.val * (t'.val - t.val) ∈ Set.Ioo (-E.radius) E.radius := by
  obtain ⟨hm0, hm1⟩ := t.property
  obtain ⟨hp0, hp1⟩ := t'.property
  have hu0 := unitInterval.nonneg u
  have hu1 := unitInterval.le_one u
  rcases le_total t.val t'.val with h | h
  · have h1 := mul_nonneg hu0 (sub_nonneg.mpr h)
    have h2 := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr h)
    constructor <;> nlinarith
  · have h1 := mul_nonpos_of_nonneg_of_nonpos hu0 (sub_nonpos.mpr h)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu1) (sub_nonpos.mpr h)
    constructor <;> nlinarith

/-- The affine parameter path `u ↦ t + u (t' − t)` through the wall. -/
def EXT_seg (t t' : E.Parameter) (u : unitInterval) : E.Parameter :=
  ⟨t.val + u.val * (t'.val - t.val), EXT_seg_mem t t' u⟩

theorem EXT_seg_zero (t t' : E.Parameter) : EXT_seg t t' 0 = t := by
  apply Subtype.ext
  simp [EXT_seg]

theorem EXT_seg_one (t t' : E.Parameter) : EXT_seg t t' 1 = t' := by
  apply Subtype.ext
  simp [EXT_seg]

theorem EXT_continuous_seg (t t' : E.Parameter) : Continuous (EXT_seg t t') :=
  (continuous_const.add (continuous_subtype_val.mul continuous_const)).subtype_mk _

theorem EXT_seg_abs_lt {δ : ℝ} {t t' : E.Parameter} (ht : |t.val| < δ) (ht' : |t'.val| < δ)
    (u : unitInterval) : |(EXT_seg t t' u).val| < δ := by
  have hu0 := unitInterval.nonneg u
  have hu1 := unitInterval.le_one u
  rw [abs_lt] at ht ht' ⊢
  change -δ < t.val + u.val * (t'.val - t.val) ∧ t.val + u.val * (t'.val - t.val) < δ
  have h1 := mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ t'.val + δ)
  have h2 := mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ δ - t'.val)
  have h3 := mul_nonneg (sub_nonneg.mpr hu1) (by linarith : (0 : ℝ) ≤ t.val + δ)
  have h4 := mul_nonneg (sub_nonneg.mpr hu1) (by linarith : (0 : ℝ) ≤ δ - t.val)
  constructor <;> nlinarith

omit [NeZero n] in
theorem EXT_regularPair_of_det {u v : Plane} (hd : det u v ≠ 0) : RegularPair u v := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply hd
    simp [det]
  · rintro rfl
    apply hd
    simp [det]
  · rintro ⟨r, _, rfl⟩
    exact hd (det_smul_self u r)

variable {P : LabelledTuple n}

/-- The parameter of a corner mark along the edge of its outgoing slot. -/
noncomputable def EXT_paOut (R : LabelledTuple n) : Mark P → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => edgeParameter R (visitTwin v).2.val v.2.val

/-- The parameter of a corner mark along the edge of its incoming segment. -/
noncomputable def EXT_pbIn (R : LabelledTuple n) : Mark P → ℝ
  | Sum.inl _ => 1
  | Sum.inr w => edgeParameter R w.2.val (visitTwin w).2.val

theorem EXT_markPoint_out (hP : CrossingGeometry P) (S : Finset (Crossing P)) (R : LabelledTuple n)
    (a : Mark P) (hsel : ∀ v : Visit P, a = Sum.inr v → v.1 ∈ S)
    (hdet : ∀ v : Visit P, a = Sum.inr v → det (edge R v.2.val) (edge R (visitTwin v).2.val) ≠ 0) :
    geoMarkPoint R a = edgePoint R (geoOutSlot hP S a).1 (EXT_paOut R a) := by
  cases a with
  | inl i =>
    rw [geoOutSlot_vertex, geoMarkPoint_vertex]
    show R i = edgePoint R i 0
    rw [edgePoint_zero]
  | inr v =>
    rw [geoOutSlot_selected hP S v (hsel v rfl), geoMarkPoint_visit]
    exact edgeParameters_intersection R _ _ (hdet v rfl)

theorem EXT_markPoint_in (hn : 3 ≤ n) (hP : CrossingGeometry P) (R : LabelledTuple n) (b : Mark P) :
    geoMarkPoint R b = edgePoint R (geoInEdge hP b) (EXT_pbIn R b) := by
  cases b with
  | inl j =>
    rw [geoInEdge_vertex hn, geoMarkPoint_vertex]
    show R j = edgePoint R (j - 1) 1
    rw [edgePoint_one, sub_add_cancel]
  | inr w =>
    rw [geoInEdge_visit hn, geoMarkPoint_visit]
    rfl

/-- The `k`-th edge of the corner polygon read on any polygon `R`: a multiple of the edge of the
outgoing slot of the `k`-th corner. -/
theorem EXT_familyEdge (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (R : LabelledTuple n)
    (hdetR : ∀ v : Visit P, v.1 ∈ S → det (edge R v.2.val) (edge R (visitTwin v).2.val) ≠ 0)
    (k : ZMod (geoCornerCount hP S q)) :
    edge (fun j => geoMarkPoint R (geoCornerMark hP S q j)) k =
      (EXT_pbIn R (geoCornerMark hP S q (k + 1)) - EXT_paOut R (geoCornerMark hP S q k)) •
        edge R (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  have hab := geoCornerPolygon_outEdge_eq_inEdge_of_independent hn hP hS q k
  have hcorner := (geoCornerMark_mem hP S q k).2
  show geoMarkPoint R (geoCornerMark hP S q (k + 1)) - geoMarkPoint R (geoCornerMark hP S q k) = _
  rw [EXT_markPoint_in hn hP R, EXT_markPoint_out hP S R (geoCornerMark hP S q k) ?_ ?_, ← hab,
    edgePoint_sub_edgePoint]
  · intro v hv
    rw [hv, isTrueCorner_visit] at hcorner
    exact hcorner
  · intro v hv
    rw [hv, isTrueCorner_visit] at hcorner
    exact hdetR v hcorner

/-- At the polygon itself the corner parameters increase along every edge of the corner polygon
(`geoCornerPolygon_edge_smul`). -/
theorem EXT_pa_lt_pb_self (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    EXT_paOut P (geoCornerMark hP S q k) < EXT_pbIn P (geoCornerMark hP S q (k + 1)) := by
  obtain ⟨c, hc, hedge⟩ := geoCornerPolygon_edge_smul hn hP hS q k
  have hF : (fun j => geoMarkPoint P (geoCornerMark hP S q j)) = geoCornerPolygon hP S q := by
    funext j
    rw [geoMarkPoint_self hP]
    rfl
  have h := EXT_familyEdge hn hP hS q P (fun v _ => CV.det_visit_twin_ne_zero hP v) k
  rw [hF, hedge] at h
  have hne : edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1 ≠ 0 := hP.1 _
  have h0 : (EXT_pbIn P (geoCornerMark hP S q (k + 1)) - EXT_paOut P (geoCornerMark hP S q k) - c) •
      edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1 = 0 := by
    rw [sub_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · linarith [sub_eq_zero.mp h1]
  · exact absurd h1 hne

/-- The corner parameters increase along every edge at every parameter of the event (the order of two
crossings of `S` on a common edge is wall-invariant, R-LOC-2 (3); an interior crossing parameter
stays in `(0,1)`). -/
theorem EXT_pa_lt_pb_all {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hn : 3 ≤ n) {t : E.Parameter} (ht : t.val ≠ 0) {S : Finset (Crossing (E.curve t))}
    (hS : GeoIndependent (geomAt E t ht) S) (hST : ∀ x ∈ S, x.val ∉ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht) S) (k : ZMod (geoCornerCount (geomAt E t ht) S q)) (u : E.Parameter) :
    EXT_paOut (E.curve u) (geoCornerMark (geomAt E t ht) S q k) <
      EXT_pbIn (E.curve u) (geoCornerMark (geomAt E t ht) S q (k + 1)) := by
  have h0 := EXT_pa_lt_pb_self hn (geomAt E t ht) hS q k
  have hab := geoCornerPolygon_outEdge_eq_inEdge_of_independent hn (geomAt E t ht) hS q k
  have hTE := hE.tripleEventData
  have hacorner := (geoCornerMark_mem (geomAt E t ht) S q k).2
  have hbcorner := (geoCornerMark_mem (geomAt E t ht) S q (k + 1)).2
  rcases hma : geoCornerMark (geomAt E t ht) S q k with i | v <;>
    rcases hmb : geoCornerMark (geomAt E t ht) S q (k + 1) with j | w
  · show (0 : ℝ) < 1
    exact zero_lt_one
  · show (0 : ℝ) < edgeParameter (E.curve u) w.2.val (visitTwin w).2.val
    have hc : IsCrossing (E.curve t) {w.2.val, (visitTwin w).2.val} := by
      rw [← visit_crossing_val_eq_pair]
      exact w.1.property
    exact (EXT_edgeParameter_interior (EXT_crosses_all hE hc u)).1
  · show edgeParameter (E.curve u) (visitTwin v).2.val v.2.val < 1
    have hc : IsCrossing (E.curve t) {(visitTwin v).2.val, v.2.val} := by
      rw [Finset.pair_comm, ← visit_crossing_val_eq_pair]
      exact v.1.property
    exact (EXT_edgeParameter_interior (EXT_crosses_all hE hc u)).2
  · show edgeParameter (E.curve u) (visitTwin v).2.val v.2.val <
      edgeParameter (E.curve u) w.2.val (visitTwin w).2.val
    rw [hma, isTrueCorner_visit] at hacorner
    rw [hma, hmb] at hab h0
    rw [geoOutSlot_selected _ S v hacorner, geoInEdge_visit hn] at hab
    change edgeParameter (E.curve t) (visitTwin v).2.val v.2.val <
      edgeParameter (E.curve t) w.2.val (visitTwin w).2.val at h0
    rw [← hab] at h0 ⊢
    rw [← CV.crossParam_eq_edgeParameter, ← CV.crossParam_eq_edgeParameter] at h0 ⊢
    have hvc : IsCrossing (E.curve t) {(visitTwin v).2.val, v.2.val} := by
      rw [Finset.pair_comm, ← visit_crossing_val_eq_pair]
      exact v.1.property
    have hwc : IsCrossing (E.curve t) {(visitTwin v).2.val, (visitTwin w).2.val} := by
      rw [hab, ← visit_crossing_val_eq_pair]
      exact w.1.property
    have hnot : ¬ (({(visitTwin v).2.val, v.2.val} : Finset (ZMod n)) ∈
        ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n))) ∧
        ({(visitTwin v).2.val, (visitTwin w).2.val} : Finset (ZMod n)) ∈
        ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n)))) := by
      intro h
      apply hST v.1 hacorner
      rw [visit_crossing_val_eq_pair v, Finset.pair_comm]
      exact h.1
    exact (hTE.other_orders_persist t u _ _ _ hvc hwc hnot).mp h0

/-- **The corner family is regular at every parameter of the event** (the wall included): every edge is a
positive multiple of a polygon edge, and consecutive edges meet at a vertex turn `G1 ≠ 0` or at a crossing
`G5 ≠ 0`, both outside the forced bundle. -/
theorem EXT_family_regular {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hn : 3 ≤ n) {t : E.Parameter} (ht : t.val ≠ 0) {S : Finset (Crossing (E.curve t))}
    (hS : GeoIndependent (geomAt E t ht) S) (hST : ∀ x ∈ S, x.val ∉ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht) S) (u : E.Parameter) (hguard : EXT_GuardAt E u) :
    Regular (fun j => geoMarkPoint (E.curve u) (geoCornerMark (geomAt E t ht) S q j)) := by
  have hTE := hE.tripleEventData
  have hdetR : ∀ v : Visit (E.curve t), v.1 ∈ S →
      det (edge (E.curve u) v.2.val) (edge (E.curve u) (visitTwin v).2.val) ≠ 0 := by
    intro v _
    have hc : IsCrossing E.center {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rw [visit_crossing_val_eq_pair v] at h
      exact (hTE.crossing_set_constant t E.zeroParameter _).mp h
    exact (hguard.2 _ _ hc).1
  intro k
  rw [EXT_familyEdge hn _ hS q _ hdetR (k - 1), EXT_familyEdge hn _ hS q _ hdetR k, sub_add_cancel]
  apply EXT_regularPair_of_det
  rw [CV.det_smul_left', CV.det_smul_right']
  have hc1 := EXT_pa_lt_pb_all hE hn ht hS hST q (k - 1) u
  have hc2 := EXT_pa_lt_pb_all hE hn ht hS hST q k u
  rw [sub_add_cancel] at hc1
  refine mul_ne_zero (sub_pos.mpr hc1).ne' (mul_ne_zero (sub_pos.mpr hc2).ne' ?_)
  rw [geoCornerPolygon_outEdge_eq_inEdge_of_independent hn _ hS q (k - 1), sub_add_cancel]
  have hacorner := (geoCornerMark_mem (geomAt E t ht) S q k).2
  rcases hma : geoCornerMark (geomAt E t ht) S q k with i | v
  · rw [geoInEdge_vertex hn, geoOutSlot_vertex]
    exact (hguard.1 i).1
  · rw [hma, isTrueCorner_visit] at hacorner
    rw [geoInEdge_visit hn, geoOutSlot_selected _ S v hacorner]
    exact hdetR v hacorner

/-- The corner family is continuous along the parameter path (vertices by projection, crossing points by
Cramer's rule at nonvanishing `G5`). -/
theorem EXT_family_continuous {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {t t' : E.Parameter} (ht : t.val ≠ 0) {S : Finset (Crossing (E.curve t))}
    (q : GeoComponent (geomAt E t ht) S) {δ : ℝ}
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u) (hδt : |t.val| < δ) (hδt' : |t'.val| < δ) :
    Continuous (fun u : unitInterval =>
      (fun j => geoMarkPoint (E.curve (EXT_seg t t' u)) (geoCornerMark (geomAt E t ht) S q j))) := by
  have hTE := hE.tripleEventData
  apply continuous_pi
  intro k
  have hγ : Continuous (fun u : unitInterval => E.curve (EXT_seg t t' u)) :=
    E.continuous_curve.comp (EXT_continuous_seg t t')
  rcases hma : geoCornerMark (geomAt E t ht) S q k with i | v
  · simp only [geoMarkPoint_vertex]
    exact (continuous_apply i).comp hγ
  · simp only [geoMarkPoint_visit]
    rw [continuous_iff_continuousAt]
    intro u
    have hc : IsCrossing E.center {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rw [visit_crossing_val_eq_pair v] at h
      exact (hTE.crossing_set_constant t E.zeroParameter _).mp h
    have hd : det (edge (E.curve (EXT_seg t t' u)) v.2.val)
        (edge (E.curve (EXT_seg t t' u)) (visitTwin v).2.val) ≠ 0 :=
      ((hguard _ (EXT_seg_abs_lt hδt hδt' u)).2 _ _ hc).1
    have hcont : ContinuousAt (fun R : LabelledTuple n =>
        edgePoint R v.2.val (edgeParameter R v.2.val (visitTwin v).2.val)) (E.curve (EXT_seg t t' u)) := by
      unfold edgePoint
      exact (continuous_vertex _).continuousAt.add
        ((continuousAt_edgeParameter_of_det hd).smul (continuous_edge _).continuousAt)
    exact hcont.comp (f := fun u : unitInterval => E.curve (EXT_seg t t' u)) hγ.continuousAt

/-- **The rotation number of an exterior carrier's corner polygon is the same on both sides of the wall**
(R-EXTERIOR-1 §4, "for rotation …"): the corner polygon deforms continuously and regularly through the
wall, so its rotation number (an integer) is constant (`rotationNumber_family_constant`). -/
theorem EXT_rotation_wall {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hn : 3 ≤ n) {t t' : E.Parameter} (ht : t.val ≠ 0) (ht' : t'.val ≠ 0) {δ : ℝ}
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u) (hδt : |t.val| < δ) (hδt' : |t'.val| < δ)
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ CV.Ind (geomAt E t ht))
    (hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht) Q) (q' : GeoComponent (geomAt E t' ht') (transportSupport hs Q))
    (hcl : (geoComponentCornerList (geomAt E t ht) Q q).map (markTransport hs) =
      geoComponentCornerList (geomAt E t' ht') (transportSupport hs Q) q') :
    rotationNumber (geoCornerPolygon (geomAt E t' ht') (transportSupport hs Q) q') =
      rotationNumber (geoCornerPolygon (geomAt E t ht) Q q) := by
  have hS : GeoIndependent (geomAt E t ht) Q := CV.geoIndependent_of_mem_Ind _ hQ
  let F : unitInterval → LabelledTuple (geoCornerCount (geomAt E t ht) Q q) :=
    fun u j => geoMarkPoint (E.curve (EXT_seg t t' u)) (geoCornerMark (geomAt E t ht) Q q j)
  have hF0 : F 0 = geoCornerPolygon (geomAt E t ht) Q q := by
    funext j
    show geoMarkPoint (E.curve (EXT_seg t t' 0)) _ = _
    rw [EXT_seg_zero, geoMarkPoint_self (geomAt E t ht)]
    rfl
  have hF1 : geoCornerPolygon (geomAt E t' ht') (transportSupport hs Q) q' =
      geoRecast (EXT_cornerCount_eq (geomAt E t ht) (geomAt E t' ht') (markTransport hs) Q _ q q' hcl) (F 1) := by
    rw [EXT_cornerPolygon_eq (geomAt E t ht) (geomAt E t' ht') (markTransport hs) Q _ q q' hcl]
    congr 1
    funext j
    show _ = geoMarkPoint (E.curve (EXT_seg t t' 1)) _
    rw [EXT_seg_one, geoMarkPoint_eq (geomAt E t' ht') hs]
  have hcont : Continuous F := EXT_family_continuous hE ht q hguard hδt hδt'
  have hreg : ∀ u, Regular (F u) := fun u =>
    EXT_family_regular hE hn ht hS hQT q _ (hguard _ (EXT_seg_abs_lt hδt hδt' u))
  rw [hF1, rotationNumber_geoRecast, ← hF0]
  exact rotationNumber_family_constant hcont hreg 1 0

end EXTRotation

section EXTAssembly

variable {E : CV.Event n}

/-- The retained crossings of a triangle-disjoint carrier are triangle-free. -/
theorem EXT_carrierCrossings_triFree {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {e f g : ZMod n} (q : GeoComponent hP S)
    (hq : TriangleDisjoint hP S e f g q) :
    ∀ c ∈ geoCarrierCrossings hP S q, c.val ∉ triangleSupports e f g := by
  intro c hc hcT
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  exact hq ⟨c, i⟩ hcT (((mem_geoCarrierCrossings hP S q c).mp hc).2 ⟨c, i⟩ rfl)

theorem EXT_oppositeSides_symm {t t' : E.Parameter} (h : OppositeSides E t t') : OppositeSides E t' t := by
  unfold OppositeSides at h ⊢
  rw [mul_comm]
  exact h

/-- **The exterior factor of the base row is the same on both sides of the wall** (R-EXTERIOR-1 §4). -/
theorem EXT_exteriorFactor_wall {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hn : 3 ≤ n) {δ : ℝ} (hL : LocalizationData E e f g δ)
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ CV.Ind (geomAt E t ht.1))
    (hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g)
    (hQ' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1)) :
    exteriorFactor hn (genericAt E t' ht'.1) hQ' e f g = exteriorFactor hn (genericAt E t ht.1) hQ e f g := by
  classical
  have hTE := hE.tripleEventData
  set hG := genericAt E t ht.1
  set hG' := genericAt E t' ht'.1
  set hP := geomAt E t ht.1
  set hP' := geomAt E t' ht'.1
  set hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hgw : ExactTriangleVisitOrders (E.curve t) (E.curve t') e f g hs := hL.gauss_words t t' ht ht' hop hs
  have hgw' : ExactTriangleVisitOrders (E.curve t') (E.curve t) e f g hs' :=
    hL.gauss_words t' t ht' ht (EXT_oppositeSides_symm hop) hs'
  have hgt := hguard t ht.2
  have hgt' := hguard t' ht'.2
  have hcenter : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} → IsCrossing E.center {i, j} :=
    fun i j h => (hTE.crossing_set_constant t E.zeroParameter _).mp h
  have hcomm : ∀ a, ¬ EXT_TriVisit e f g a → ¬ EXT_TriVisit e f g (geoSmoothingSuccessor hP Q a) →
      geoSmoothingSuccessor hP' (transportSupport hs Q) (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor hP Q a) :=
    fun a ha hρ => EXT_succ_wall hn hP hP' hgw Q a ha hρ
  have hcomm' : ∀ b', ¬ EXT_TriVisit e f g ((markTransport hs).symm b') →
      ¬ EXT_TriVisit e f g ((markTransport hs).symm (geoSmoothingSuccessor hP' (transportSupport hs Q) b')) →
      geoSmoothingSuccessor hP Q ((markTransport hs).symm b') =
        (markTransport hs).symm (geoSmoothingSuccessor hP' (transportSupport hs Q) b') := by
    intro b' hb' hρ
    rw [EXT_triVisit_markTransport_symm] at hb' hρ
    rw [EXT_markTransport_symm_eq, EXT_markTransport_symm_eq]
    have h := EXT_succ_wall hn hP' hP hgw' (transportSupport hs Q) b' hb' hρ
    rwa [EXT_transportSupport_symm] at h
  have hkeyAll : ∀ v w : Visit (E.curve t), v.1.val ∉ triangleSupports e f g → w.1.val ∉ triangleSupports e f g →
      (geometricVisitKey hG.crossingGeometry v < geometricVisitKey hG.crossingGeometry w ↔
        geometricVisitKey hG'.crossingGeometry (visitTransport hs v) <
          geometricVisitKey hG'.crossingGeometry (visitTransport hs w)) := by
    intro v w hv hw
    exact EXT_key_lt_wall hP hP' hgw (Sum.inr v) (Sum.inr w)
      (EXT_hab_of_good_left (a := Sum.inr v) (b := Sum.inr w) hv)
  have hdetAll : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔ 0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hc => EXT_det_pos_iff_of_guard hgt hgt' (hcenter i j hc)
  refine EXT_exteriorFactor_eq hn hG hG' hs hQ hQ' e f g hcomm hcomm' ?_
  intro q hq
  set q' := EXT_corr hP hP' (markTransport hs) Q (transportSupport hs Q) q
  have hqav : EXT_Avoids hP Q (fun a => ¬ EXT_TriVisit e f g a) q :=
    (EXT_triangleDisjoint_iff hP Q e f g q).mp hq
  have hblock : ∀ b, geoOwner hP' (transportSupport hs Q) (markTransport hs b) = q' ↔ geoOwner hP Q b = q :=
    EXT_corr_iff hP hP' (markTransport hs) Q _ _ hcomm q hqav
  have hlist : (geoComponentMarkList hP Q q).map (markTransport hs) =
      geoComponentMarkList hP' (transportSupport hs Q) q' := by
    refine EXT_markList_map hP hP' (markTransport hs) Q _ q q' hblock ?_
    intro a b ha _
    exact EXT_key_lt_wall hP hP' hgw a b (EXT_hab_of_good_left (hqav a ha))
  have hcorner : ∀ a, geoOwner hP Q a = q →
      (IsTrueCorner (transportSupport hs Q) (markTransport hs a) ↔ IsTrueCorner Q a) :=
    fun a _ => isTrueCorner_markTransport hs Q a
  have hcl : (geoComponentCornerList hP Q q).map (markTransport hs) =
      geoComponentCornerList hP' (transportSupport hs Q) q' :=
    EXT_cornerList_map hP hP' (markTransport hs) Q _ q q' hlist hcorner
  have hc := EXT_cornerCount_eq hP hP' (markTransport hs) Q _ q q' hcl
  have hsel : ∀ x : Crossing (E.curve t), (∀ v : Visit (E.curve t), v.1 = x → geoOwner hP Q (Sum.inr v) = q) →
      (crossingTransport hs x ∈ transportSupport hs Q ↔ x ∈ Q) :=
    fun x _ => mem_transportSupport_iff hs Q x
  have hX' : geoCarrierCrossings hP' (transportSupport hs Q) q' =
      (geoCarrierCrossings hP Q q).map (crossingTransport hs).toEmbedding :=
    EXT_carrierCrossings_map hP hP' hs Q _ q q' hblock hsel
  have htri := EXT_carrierCrossings_triFree hP Q q hq
  have hX : EXT_PieceSetting hP hP' hs Q (transportSupport hs Q) (geoCarrierCrossings hP Q q) :=
    EXT_pieceSetting hP hP' hs hQ hQ' q q' hX'
      (fun c hc d hd => F1.graph_on_W_same hL t t' ht ht' hop hs c d (htri c hc) (htri d hd))
  have hturnP : ∀ i, turn (E.curve t') i = turn (E.curve t) i := EXT_turn_eq_of_guard hgt hgt'
  have hsign : ∀ v : Visit (E.curve t), v.1 ∈ Q →
      crossingSign (E.curve t') v.2.val (visitTwin v).2.val = crossingSign (E.curve t) v.2.val (visitTwin v).2.val := by
    intro v _
    have hc : IsCrossing (E.curve t) {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rwa [visit_crossing_val_eq_pair v] at h
    exact EXT_G5_sign_eq_of_guard hgt hgt' (hcenter _ _ hc)
  have hweight : CV.weight hP' (transportSupport hs Q) q' = CV.weight hP Q q :=
    EXT_weight_eq hP hP' Q _ q q' hc (EXT_turn_wall hn hP hP' hs hQ hQ' q q' hcl hturnP hsign)
  have hR : CV.carrierR hn hG' hQ' q' = CV.carrierR hn hG hQ q :=
    EXT_carrierR_eq hn hG hG' hQ hQ' q q'
      (EXT_rotation_wall hE hn ht.1 ht'.1 hguard ht.2 ht'.2 hs hQ hQT q q' hcl)
  have hw : CV.groupedWrithe hG' q' = CV.groupedWrithe hG q :=
    EXT_groupedWrithe_eq hG hG' hs q q' hX hX'
  have hp : CV.groupedPoly hn hG' hQ' q' = CV.groupedPoly hn hG hQ q := by
    refine EXT_groupedPoly_eq hn hG hG' hs hQ hQ' q q' hX hX' ?_
    intro H H' hHX hH'
    exact EXT_pieceHomfly_wall hn hG hG' hs hQ hQ' hkeyAll hdetAll H H' (fun c hc => htri c (hHX hc)) hH'
  rw [hweight, EXT_Omega1_eq hn hG hG' hQ hQ' q q' hR hw hp]

/-- **Row 168, field `wall_invariant`**: "and its common value is the same for `sigma=-` and `sigma=+`". -/
theorem EXT_168_wall_invariant (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u)
    {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ (A : Finset (Crossing (E.curve t))) (A' : Finset (Crossing (E.curve t'))),
      A ⊆ triangleCrossings (E.curve t) e f g → A' ⊆ triangleCrossings (E.curve t') e f g →
      ∀ (hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1))
        (hA' : transportSupport hs Q ∪ A' ∈ CV.Ind (geomAt E t' ht'.1)),
        exteriorFactor hn (genericAt E t ht.1) hA e f g =
          exteriorFactor hn (genericAt E t' ht'.1) hA' e f g := by
  intro t t' ht ht' hop hs Q hQ A A' hAT hAT' hA hA'
  have hQind : Q ∈ CV.Ind (geomAt E t ht.1) := mem_Ind_of_mem_outsideSupports hQ
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := by
    intro x hx hxT
    exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  have hQ'ind : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) :=
    PRE_mem_Ind_of_subset hA' Finset.subset_union_left
  have hQ'T : ∀ x ∈ transportSupport hs Q, x.val ∉ triangleSupports e f g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hQT y hy
  rw [← EXT_exteriorFactor_eq_base hn (genericAt E t ht.1) hQT
      (fun x hx => (P1.mem_triangleCrossings x).mp (hAT hx)) hA hQind,
    ← EXT_exteriorFactor_eq_base hn (genericAt E t' ht'.1) hQ'T
      (fun x hx => (P1.mem_triangleCrossings x).mp (hAT' hx)) hA' hQ'ind]
  exact (EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQind hQT hQ'ind).symm

/-- **Row 168, field `factorization`**: "Consequently every full-availability row factors exactly as
`tau_sigma(A) = C_Q * rho_sigma(A)`", with `C_Q` the exterior factor of the base row on side `t`. -/
theorem EXT_168_factorization (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u)
    {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q, ∀ hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      (∀ A : Finset (Crossing (E.curve t)), A ⊆ triangleCrossings (E.curve t) e f g →
        ∀ hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1),
          rowTerm hn (genericAt E t ht.1) (Q ∪ A) =
            exteriorFactor hn (genericAt E t ht.1) (mem_Ind_of_mem_outsideSupports hQ) e f g *
              touchingFactor hn (genericAt E t ht.1) hA e f g) ∧
      (∀ A' : Finset (Crossing (E.curve t')), A' ⊆ triangleCrossings (E.curve t') e f g →
        ∀ hA' : transportSupport hs Q ∪ A' ∈ CV.Ind (geomAt E t' ht'.1),
          rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q ∪ A') =
            exteriorFactor hn (genericAt E t ht.1) (mem_Ind_of_mem_outsideSupports hQ) e f g *
              touchingFactor hn (genericAt E t' ht'.1) hA' e f g) := by
  intro t t' ht ht' hop hs Q hQ _
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := by
    intro x hx hxT
    exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  refine ⟨fun A hAT hA => ?_, fun A' hAT' hA' => ?_⟩
  · rw [rowTerm_eq_exterior_mul_touching hn _ hA e f g,
      EXT_exteriorFactor_eq_base hn (genericAt E t ht.1) hQT
        (fun x hx => (P1.mem_triangleCrossings x).mp (hAT hx)) hA (mem_Ind_of_mem_outsideSupports hQ)]
  · have hQ'ind : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) :=
      PRE_mem_Ind_of_subset hA' Finset.subset_union_left
    have hQ'T : ∀ x ∈ transportSupport hs Q, x.val ∉ triangleSupports e f g := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact hQT y hy
    rw [rowTerm_eq_exterior_mul_touching hn _ hA' e f g,
      ← EXT_exteriorFactor_eq_base hn (genericAt E t' ht'.1) hQ'T
        (fun x hx => (P1.mem_triangleCrossings x).mp (hAT' hx)) hA' hQ'ind,
      EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs (mem_Ind_of_mem_outsideSupports hQ) hQT hQ'ind]

end EXTAssembly

end EXT

/-- **Row 168, R:exterior** (R-EXTERIOR-1). -/
theorem exterior (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExteriorData hn E e f g δ := by
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hguard⟩ := EXT_exists_guardRadius hE
  refine ⟨min δL δG, lt_min hδL hδG, (min_le_left _ _).trans hδLr, ?_⟩
  have hL' : LocalizationData E e f g (min δL δG) := F1.localizationData_mono (min_le_left δL δG) hL
  have hguard' : ∀ u : E.Parameter, |u.val| < min δL δG → EXT_GuardAt E u :=
    fun u hu => hguard u (lt_of_lt_of_le hu (min_le_right _ _))
  exact { independent_of_A := EXT_168_independent_of_A hn E e f g _
          wall_invariant := EXT_168_wall_invariant hn E e f g hL' hguard' hE
          factorization := EXT_168_factorization hn E e f g hL' hguard' hE }

/-! ## Unit AV — the transport across the wall at availability ≤ 1 (proof lane, 2026-09-14)

The wall data `AV_Wall` (abstracted from the event), the corner-successor transport of carriers, the
literal carriage of corner lists, turns, `wt`, `wind`, retained crossings and pieces, the record
isomorphism of the positive lifts (`AV_homfly_lift_eq`), the rotation by CV:def:rot's ray formula
(`AV_rotationNumber_tcp`), and the event data at a common radius (`AV_EventRadius`). Nothing in the
fixed statements is changed. -/

section AV

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

/-- A crossing *dominated* by the support `S` through a dominator outside the local set `T`
(R-PAR-v6: "`x` interlaces a member of `S'`"; the dominator is an outside crossing, so the
interlacement is wall-invariant). -/
def AV_Dom (hP : CrossingGeometry P) (T S : Finset (Crossing P)) (x : Crossing P) : Prop :=
  ∃ s ∈ S, s ∉ T ∧ GeometricInterlaces hP x s

/-- **Wall data for a support `S` across a simple RIII wall**, abstracted from the event: two
polygons `P`, `P'` on the record domain with the same crossing supports, a local crossing set `T`
(the triangle), and a support `S` such that (i) same-edge visit orders are carried except for the
pairs of distinct `T`-crossings on a common edge (R-LOC-2 (2)–(3), `ExactTriangleVisitOrders`),
(ii) interlacement is carried off the pairs inside `T` (R-LOC-2 (4)), (iii) of any two distinct
`T`-crossings one is dominated by `S` through an outside crossing (availability `≤ 1`),
(iv) vertex turns and crossing signs agree (lem:guardconst), (v) a common reference vector `r`
sees every edge direction with the same nonzero sign on both sides. -/
structure AV_Wall (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (T S : Finset (Crossing P)) : Prop where
  indep : GeoIndependent hP S
  key_lt : ∀ v w : Visit P, ¬ (v.1 ∈ T ∧ w.1 ∈ T ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val) →
    (geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hP' (visitTransport hs v) < geometricVisitKey hP' (visitTransport hs w))
  interlaces_iff : ∀ x y : Crossing P, ¬ (x ∈ T ∧ y ∈ T) →
    (GeometricInterlaces hP x y ↔
      GeometricInterlaces hP' (crossingTransport hs x) (crossingTransport hs y))
  dominated : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → AV_Dom hP T S x ∨ AV_Dom hP T S y
  turn_eq : ∀ i, turn P' i = turn P i
  sign_eq : ∀ i j, IsCrossing P {i, j} → crossingSign P' i j = crossingSign P i j
  ray : ∃ r : Plane, ∀ h : ZMod n, det r (edge P h) ≠ 0 ∧
    SignType.sign (det r (edge P' h)) = SignType.sign (det r (edge P h))

namespace AV_Wall

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}

omit [NeZero n] in
/-- Wall data pass to any larger independent support (domination is monotone in `S`). -/
theorem mono (W : AV_Wall hP hP' hs T S) {S₂ : Finset (Crossing P)} (hS : S ⊆ S₂)
    (hind : GeoIndependent hP S₂) : AV_Wall hP hP' hs T S₂ where
  indep := hind
  key_lt := W.key_lt
  interlaces_iff := W.interlaces_iff
  dominated x hx y hy hxy := by
    rcases W.dominated x hx y hy hxy with ⟨s, hs₁, hs₂, h⟩ | ⟨s, hs₁, hs₂, h⟩
    · exact Or.inl ⟨s, hS hs₁, hs₂, h⟩
    · exact Or.inr ⟨s, hS hs₁, hs₂, h⟩
  turn_eq := W.turn_eq
  sign_eq := W.sign_eq
  ray := W.ray

omit [NeZero n] in
/-- A selected crossing is not dominated (independence). -/
theorem not_dom_of_mem (W : AV_Wall hP hP' hs T S) {x : Crossing P} (hx : x ∈ S) :
    ¬ AV_Dom hP T S x := by
  rintro ⟨s, hsS, -, hxs⟩
  have hne : x ≠ s := fun h => geometricInterlaces_irrefl hP x (h ▸ hxs)
  exact W.indep x hx s hsS hne hxs

omit [NeZero n] in
/-- Domination is carried across the wall (the dominator is outside `T`). -/
theorem dom_transport (W : AV_Wall hP hP' hs T S) {x : Crossing P} (h : AV_Dom hP T S x) :
    AV_Dom hP' (transportSupport hs T) (transportSupport hs S) (crossingTransport hs x) := by
  obtain ⟨s, hsS, hsT, hxs⟩ := h
  refine ⟨crossingTransport hs s, (mem_transportSupport_iff hs S s).mpr hsS,
    fun h => hsT ((mem_transportSupport_iff hs T s).mp h), ?_⟩
  exact (W.interlaces_iff x s (fun h => hsT h.2)).mp hxs

omit [NeZero n] in
/-- The transported support is independent. -/
theorem indep' (W : AV_Wall hP hP' hs T S) : GeoIndependent hP' (transportSupport hs S) := by
  intro x' hx' y' hy' hne
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [mem_transportSupport_iff] at hx' hy'
  have hxy : x ≠ y := fun h => hne (h ▸ rfl)
  have hnT : ¬ (x ∈ T ∧ y ∈ T) := by
    rintro ⟨hxT, hyT⟩
    rcases W.dominated x hxT y hyT hxy with h | h
    · exact W.not_dom_of_mem hx' h
    · exact W.not_dom_of_mem hy' h
  exact fun h => W.indep x hx' y hy' hxy ((W.interlaces_iff x y hnT).mpr h)

/-- Mark keys are carried for every pair of marks that is not a same-edge pair of distinct
`T`-visits (the accepted `geoMarkKey_lt_transport_of_visitKey`, word for word, with the exception
built in). -/
theorem mark_key_lt (W : AV_Wall hP hP' hs T S) (a b : Mark P)
    (hab : ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w →
      ¬ (v.1 ∈ T ∧ w.1 ∈ T ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val)) :
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

end AV_Wall

/-- A *good* mark: its position relative to every corner is carried across the wall — every mark
except the visits of dominated `T`-crossings (the swap partners of the selected `T`-visit). -/
def AV_Good (hP : CrossingGeometry P) (T S : Finset (Crossing P)) (m : Mark P) : Prop :=
  ∀ v : Visit P, m = Sum.inr v → v.1 ∈ T → ¬ AV_Dom hP T S v.1

omit [NeZero n] in
theorem AV_good_vertex (hP : CrossingGeometry P) (T S : Finset (Crossing P)) (i : ZMod n) :
    AV_Good hP T S (Sum.inl i) := fun _ h => nomatch h

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}

omit [NeZero n] in
theorem AV_good_of_corner (W : AV_Wall hP hP' hs T S) {m : Mark P} (hm : IsTrueCorner S m) :
    AV_Good hP T S m := by
  intro v hv _
  subst hv
  exact W.not_dom_of_mem hm

/-- A good mark and a corner: their key order is carried, in both directions. -/
theorem AV_good_key_lt (W : AV_Wall hP hP' hs T S) {m d : Mark P} (hm : AV_Good hP T S m)
    (hd : IsTrueCorner S d) :
    (geoMarkKey hP m < geoMarkKey hP d ↔
        geoMarkKey hP' (markTransport hs m) < geoMarkKey hP' (markTransport hs d)) ∧
    (geoMarkKey hP d < geoMarkKey hP m ↔
        geoMarkKey hP' (markTransport hs d) < geoMarkKey hP' (markTransport hs m)) := by
  have hno : ∀ v w : Visit P, m = Sum.inr v → d = Sum.inr w →
      ¬ (v.1 ∈ T ∧ w.1 ∈ T ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val) := by
    rintro v w rfl rfl ⟨hvT, hwT, hne, -⟩
    have hwS : w.1 ∈ S := hd
    rcases W.dominated v.1 hvT w.1 hwT hne with h | h
    · exact hm v rfl hvT h
    · exact W.not_dom_of_mem hwS h
  exact ⟨W.mark_key_lt m d hno,
    W.mark_key_lt d m fun w v hw hv h => hno v w hv hw ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩

/-- Corners are carried to corners. -/
theorem AV_corner_transport (S : Finset (Crossing P)) (m : Mark P) :
    IsTrueCorner (transportSupport hs S) (markTransport hs m) ↔ IsTrueCorner S m := by
  cases m with
  | inl i =>
    rw [markTransport_vertex]
    exact iff_of_true (isTrueCorner_vertex _ i) (isTrueCorner_vertex S i)
  | inr v =>
    rw [markTransport_visit, isTrueCorner_visit, isTrueCorner_visit, visitTransport_crossing,
      mem_transportSupport_iff]

/-! ### The next corner along the traversal circle -/

/-- Some `ρ`-iterate of every mark is a corner (`ρ` is one cycle through the vertex `0`). -/
theorem AV_exists_corner_pow (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    ∃ k : ℕ, IsTrueCorner S ((geoMarkSuccessor hP ^ k) m) := by
  obtain ⟨i, -, hi⟩ := (geoMarkSuccessor_sameCycle hP m (Sum.inl 0)).exists_pow_eq'
  exact ⟨i, by rw [hi]; exact isTrueCorner_vertex S 0⟩

open scoped Classical in
/-- The first corner at or after a mark along the traversal circle (`ρ`-iteration). -/
noncomputable def AV_nextCorner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    Mark P :=
  (geoMarkSuccessor hP ^ Nat.find (AV_exists_corner_pow hP S m)) m

open scoped Classical in
theorem AV_nextCorner_corner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    IsTrueCorner S (AV_nextCorner hP S m) :=
  Nat.find_spec (AV_exists_corner_pow hP S m)

open scoped Classical in
theorem AV_nextCorner_of_corner {m : Mark P} (hm : IsTrueCorner S m) :
    AV_nextCorner hP S m = m := by
  unfold AV_nextCorner
  have h0 : Nat.find (AV_exists_corner_pow hP S m) = 0 := by
    rw [Nat.find_eq_zero]
    show IsTrueCorner S ((geoMarkSuccessor hP ^ 0) m)
    rw [pow_zero, Equiv.Perm.one_apply]
    exact hm
  rw [h0, pow_zero, Equiv.Perm.one_apply]

open scoped Classical in
theorem AV_find_succ {m : Mark P} (hm : ¬ IsTrueCorner S m) :
    Nat.find (AV_exists_corner_pow hP S (geoMarkSuccessor hP m)) =
      Nat.find (AV_exists_corner_pow hP S m) - 1 := by
  have hk0 : Nat.find (AV_exists_corner_pow hP S m) ≠ 0 := by
    intro h
    apply hm
    have := Nat.find_spec (AV_exists_corner_pow hP S m)
    rw [h, pow_zero, Equiv.Perm.one_apply] at this
    exact this
  rw [Nat.find_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
    exact Nat.find_spec (AV_exists_corner_pow hP S m)
  · intro j hj
    rw [← Equiv.Perm.mul_apply, ← pow_succ]
    exact Nat.find_min (AV_exists_corner_pow hP S m) (by omega)

open scoped Classical in
theorem AV_nextCorner_succ {m : Mark P} (hm : ¬ IsTrueCorner S m) :
    AV_nextCorner hP S (geoMarkSuccessor hP m) = AV_nextCorner hP S m := by
  have hk0 : Nat.find (AV_exists_corner_pow hP S m) ≠ 0 := by
    intro h
    apply hm
    have := Nat.find_spec (AV_exists_corner_pow hP S m)
    rw [h, pow_zero, Equiv.Perm.one_apply] at this
    exact this
  unfold AV_nextCorner
  rw [AV_find_succ hm, ← Equiv.Perm.mul_apply, ← pow_succ,
    Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]

/-- At a non-corner (an unselected visit) the smoothing successor is the plain successor. -/
theorem AV_smoothing_of_not_corner (hP : CrossingGeometry P) (S : Finset (Crossing P))
    {m : Mark P} (hm : ¬ IsTrueCorner S m) :
    geoSmoothingSuccessor hP S m = geoMarkSuccessor hP m := by
  cases m with
  | inl i => exact absurd (isTrueCorner_vertex S i) hm
  | inr v => exact geoSmoothingSuccessor_visit_of_not_mem hP S v hm

theorem AV_owner_pow_of_not_corner (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (m : Mark P) : ∀ k : ℕ, (∀ j < k, ¬ IsTrueCorner S ((geoMarkSuccessor hP ^ j) m)) →
    geoOwner hP S ((geoMarkSuccessor hP ^ k) m) = geoOwner hP S m := by
  intro k
  induction k with
  | zero => intro _; rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih =>
    intro h
    rw [pow_succ', Equiv.Perm.mul_apply,
      ← AV_smoothing_of_not_corner hP S (h k (Nat.lt_succ_self k)), geoOwner_successor]
    exact ih fun j hj => h j (Nat.lt_succ_of_lt hj)

open scoped Classical in
/-- The next corner lies on the carrier of the mark (the carrier follows `ρ` through unselected
visits). -/
theorem AV_nextCorner_owner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    geoOwner hP S (AV_nextCorner hP S m) = geoOwner hP S m :=
  AV_owner_pow_of_not_corner hP S m _ fun _ hj => Nat.find_min (AV_exists_corner_pow hP S m) hj

/-- The corner successor of a mark: the first corner strictly after its outgoing slot — the next
corner of its carrier after it. -/
noncomputable def AV_cornerSucc (hP : CrossingGeometry P) (S : Finset (Crossing P)) (c : Mark P) :
    Mark P :=
  AV_nextCorner hP S (geoSmoothingSuccessor hP S c)

theorem AV_cornerSucc_corner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (c : Mark P) :
    IsTrueCorner S (AV_cornerSucc hP S c) :=
  AV_nextCorner_corner hP S _

theorem AV_cornerSucc_owner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (c : Mark P) :
    geoOwner hP S (AV_cornerSucc hP S c) = geoOwner hP S c := by
  unfold AV_cornerSucc
  rw [AV_nextCorner_owner, geoOwner_successor]

/-! ### Keys along the sorted marked circle -/

omit [NeZero n] in
theorem AV_key_nonneg (hP : CrossingGeometry P) (m : Mark P) : 0 ≤ geoMarkKey hP m :=
  add_nonneg (Nat.cast_nonneg _) (geoMarkPosition hP m).2.property.1

omit [NeZero n] in
theorem AV_key_inl_zero (hP : CrossingGeometry P) : geoMarkKey hP (Sum.inl 0) = 0 := by
  show ((0 : ZMod n).val : ℝ) + (0 : ℝ) = 0
  rw [ZMod.val_zero]
  simp

theorem AV_geoMarkList_pairwise_lt (hP : CrossingGeometry P) :
    (geoMarkList hP).Pairwise (fun a b => geoMarkKey hP a < geoMarkKey hP b) :=
  pairwise_lt_of_pairwise_le_nodup (geoMarkList_sorted hP) (geoMarkList_nodup hP)
    (geoMarkKey_injective hP)

theorem AV_geoMarkList_key_lt_iff (hP : CrossingGeometry P) {i j : ℕ}
    (hi : i < (geoMarkList hP).length) (hj : j < (geoMarkList hP).length) :
    geoMarkKey hP (geoMarkList hP)[i] < geoMarkKey hP (geoMarkList hP)[j] ↔ i < j := by
  have hpw := AV_geoMarkList_pairwise_lt hP
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

/-- `ρ` increases the key with no mark strictly in between, except at the last mark, where it wraps
to the vertex `0` (the least mark). -/
theorem AV_succ_spec (hP : CrossingGeometry P) (m : Mark P) :
    (geoMarkKey hP m < geoMarkKey hP (geoMarkSuccessor hP m) ∧
      ∀ d, ¬ (geoMarkKey hP m < geoMarkKey hP d ∧
        geoMarkKey hP d < geoMarkKey hP (geoMarkSuccessor hP m))) ∨
    (geoMarkSuccessor hP m = Sum.inl 0 ∧ ∀ d, geoMarkKey hP d ≤ geoMarkKey hP m) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP m)
  rw [geoMarkSuccessor_getElem hP i hi]
  have hpos : 0 < (geoMarkList hP).length := lt_of_le_of_lt (Nat.zero_le i) hi
  by_cases h : i + 1 < (geoMarkList hP).length
  · left
    have hmod : (i + 1) % (geoMarkList hP).length = i + 1 := Nat.mod_eq_of_lt h
    refine ⟨?_, ?_⟩
    · rw [AV_geoMarkList_key_lt_iff hP hi (Nat.mod_lt _ hpos), hmod]
      omega
    · intro d ⟨h1, h2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP d)
      rw [AV_geoMarkList_key_lt_iff hP hi hj] at h1
      rw [AV_geoMarkList_key_lt_iff hP hj (Nat.mod_lt _ hpos), hmod] at h2
      omega
  · right
    have hlen : i + 1 = (geoMarkList hP).length := by omega
    have hmod : (i + 1) % (geoMarkList hP).length = 0 := by rw [hlen, Nat.mod_self]
    have hidx : (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'(Nat.mod_lt _ hpos) =
        (geoMarkList hP)[0]'hpos :=
      geo_getElem_congr _ _ rfl _ _ _ hpos hmod
    rw [hidx]
    refine ⟨?_, ?_⟩
    · apply geoMarkKey_injective hP
      apply le_antisymm
      · obtain ⟨j0, hj0, hj0e⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP (Sum.inl 0))
        rw [← hj0e]
        rcases Nat.eq_zero_or_pos j0 with hz | hz
        · rw [geo_getElem_congr _ _ rfl 0 j0 hpos hj0 hz.symm]
        · exact le_of_lt ((AV_geoMarkList_key_lt_iff hP hpos hj0).mpr hz)
      · rw [AV_key_inl_zero]
        exact AV_key_nonneg hP _
    · intro d
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP d)
      rcases Nat.lt_or_ge j i with hji | hji
      · exact le_of_lt ((AV_geoMarkList_key_lt_iff hP hj hi).mpr hji)
      · have : j = i := by omega
        subst this
        exact le_refl _

/-! ### The order-theoretic specification of the next corner and of the corner successor -/

/-- `d` is the first corner at or after `m`: either the least corner with key `≥ key m`, or — when
no corner has key `≥ key m` — the vertex `0`. -/
def AV_NCSpec (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m d : Mark P) : Prop :=
  IsTrueCorner S d ∧
  ((geoMarkKey hP m ≤ geoMarkKey hP d ∧
      ∀ d', IsTrueCorner S d' → geoMarkKey hP m ≤ geoMarkKey hP d' →
        geoMarkKey hP d ≤ geoMarkKey hP d') ∨
    ((∀ d', IsTrueCorner S d' → geoMarkKey hP d' < geoMarkKey hP m) ∧ d = Sum.inl 0))

theorem AV_ncspec_unique {m d₁ d₂ : Mark P} (h1 : AV_NCSpec hP S m d₁) (h2 : AV_NCSpec hP S m d₂) :
    d₁ = d₂ := by
  obtain ⟨hc1, h1⟩ := h1
  obtain ⟨hc2, h2⟩ := h2
  rcases h1 with ⟨hle1, hmin1⟩ | ⟨hall1, rfl⟩ <;> rcases h2 with ⟨hle2, hmin2⟩ | ⟨hall2, rfl⟩
  · exact geoMarkKey_injective hP (le_antisymm (hmin1 d₂ hc2 hle2) (hmin2 d₁ hc1 hle1))
  · exact absurd (lt_of_le_of_lt hle1 (hall2 d₁ hc1)) (lt_irrefl _)
  · exact absurd (lt_of_le_of_lt hle2 (hall1 d₂ hc2)) (lt_irrefl _)
  · rfl

open scoped Classical in
theorem AV_nextCorner_spec_aux (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    ∀ k : ℕ, ∀ m : Mark P, Nat.find (AV_exists_corner_pow hP S m) = k →
      AV_NCSpec hP S m (AV_nextCorner hP S m) := by
  intro k
  induction k with
  | zero =>
    intro m hk
    have hm : IsTrueCorner S m := by
      have := Nat.find_spec (AV_exists_corner_pow hP S m)
      rw [hk, pow_zero, Equiv.Perm.one_apply] at this
      exact this
    rw [AV_nextCorner_of_corner hm]
    exact ⟨hm, Or.inl ⟨le_refl _, fun d' _ h => h⟩⟩
  | succ k ih =>
    intro m hk
    have hm : ¬ IsTrueCorner S m := by
      intro hm
      have h0 : Nat.find (AV_exists_corner_pow hP S m) = 0 := by
        rw [Nat.find_eq_zero]
        show IsTrueCorner S ((geoMarkSuccessor hP ^ 0) m)
        rw [pow_zero, Equiv.Perm.one_apply]
        exact hm
      omega
    have hk' : Nat.find (AV_exists_corner_pow hP S (geoMarkSuccessor hP m)) = k := by
      rw [AV_find_succ hm, hk]
      rfl
    have hspec := ih (geoMarkSuccessor hP m) hk'
    rw [AV_nextCorner_succ hm] at hspec
    obtain ⟨hcorner, hspec⟩ := hspec
    refine ⟨hcorner, ?_⟩
    have hne : ∀ d', IsTrueCorner S d' → geoMarkKey hP d' ≠ geoMarkKey hP m := by
      intro d' hd' h
      exact hm (geoMarkKey_injective hP h ▸ hd')
    rcases AV_succ_spec hP m with ⟨hlt, hbetween⟩ | ⟨hwrap, hall⟩
    · rcases hspec with ⟨hle, hmin⟩ | ⟨hall, hzero⟩
      · left
        refine ⟨le_of_lt (lt_of_lt_of_le hlt hle), ?_⟩
        intro d' hd' hmd'
        have hmd'' : geoMarkKey hP m < geoMarkKey hP d' := lt_of_le_of_ne hmd' (hne d' hd').symm
        have : ¬ geoMarkKey hP d' < geoMarkKey hP (geoMarkSuccessor hP m) :=
          fun h => hbetween d' ⟨hmd'', h⟩
        exact hmin d' hd' (not_lt.mp this)
      · right
        refine ⟨?_, hzero⟩
        intro d' hd'
        have h1 := hall d' hd'
        have : ¬ geoMarkKey hP m < geoMarkKey hP d' := fun h => hbetween d' ⟨h, h1⟩
        exact lt_of_le_of_ne (not_lt.mp this) (hne d' hd')
    · right
      refine ⟨?_, ?_⟩
      · intro d' hd'
        exact lt_of_le_of_ne (hall d') (hne d' hd')
      · rw [← AV_nextCorner_succ hm, hwrap]
        exact AV_nextCorner_of_corner (isTrueCorner_vertex S 0)

open scoped Classical in
theorem AV_nextCorner_spec (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    AV_NCSpec hP S m (AV_nextCorner hP S m) :=
  AV_nextCorner_spec_aux hP S _ m rfl

/-- `d` is the first corner strictly after `x`: the least corner with key `> key x`, or the vertex
`0` when no corner has key `> key x`. -/
def AV_CSSpec (hP : CrossingGeometry P) (S : Finset (Crossing P)) (x d : Mark P) : Prop :=
  IsTrueCorner S d ∧
  ((geoMarkKey hP x < geoMarkKey hP d ∧
      ∀ d', IsTrueCorner S d' → geoMarkKey hP x < geoMarkKey hP d' →
        geoMarkKey hP d ≤ geoMarkKey hP d') ∨
    ((∀ d', IsTrueCorner S d' → geoMarkKey hP d' ≤ geoMarkKey hP x) ∧ d = Sum.inl 0))

theorem AV_csspec_unique {x d₁ d₂ : Mark P} (h1 : AV_CSSpec hP S x d₁) (h2 : AV_CSSpec hP S x d₂) :
    d₁ = d₂ := by
  obtain ⟨hc1, h1⟩ := h1
  obtain ⟨hc2, h2⟩ := h2
  rcases h1 with ⟨hlt1, hmin1⟩ | ⟨hall1, rfl⟩ <;> rcases h2 with ⟨hlt2, hmin2⟩ | ⟨hall2, rfl⟩
  · exact geoMarkKey_injective hP (le_antisymm (hmin1 d₂ hc2 hlt2) (hmin2 d₁ hc1 hlt1))
  · exact absurd (lt_of_lt_of_le hlt1 (hall2 d₁ hc1)) (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le hlt2 (hall1 d₂ hc2)) (lt_irrefl _)
  · rfl

/-- The next corner after `ρ x` is the first corner strictly after `x`. -/
theorem AV_nextCorner_succ_spec (hP : CrossingGeometry P) (S : Finset (Crossing P)) (x : Mark P) :
    AV_CSSpec hP S x (AV_nextCorner hP S (geoMarkSuccessor hP x)) := by
  obtain ⟨hcorner, hspec⟩ := AV_nextCorner_spec hP S (geoMarkSuccessor hP x)
  refine ⟨hcorner, ?_⟩
  rcases AV_succ_spec hP x with ⟨hlt, hbetween⟩ | ⟨hwrap, hall⟩
  · rcases hspec with ⟨hle, hmin⟩ | ⟨hall, hzero⟩
    · left
      refine ⟨lt_of_lt_of_le hlt hle, ?_⟩
      intro d' hd' hxd'
      have : ¬ geoMarkKey hP d' < geoMarkKey hP (geoMarkSuccessor hP x) :=
        fun h => hbetween d' ⟨hxd', h⟩
      exact hmin d' hd' (not_lt.mp this)
    · right
      refine ⟨?_, hzero⟩
      intro d' hd'
      have h1 := hall d' hd'
      have : ¬ geoMarkKey hP x < geoMarkKey hP d' := fun h => hbetween d' ⟨h, h1⟩
      exact not_lt.mp this
  · right
    refine ⟨fun d' _ => hall d', ?_⟩
    rw [hwrap]
    exact AV_nextCorner_of_corner (isTrueCorner_vertex S 0)

/-! ### Transport of the specifications across the wall -/

theorem AV_ncspec_transport (W : AV_Wall hP hP' hs T S) {m d : Mark P} (hm : AV_Good hP T S m)
    (h : AV_NCSpec hP S m d) :
    AV_NCSpec hP' (transportSupport hs S) (markTransport hs m) (markTransport hs d) := by
  obtain ⟨hc, h⟩ := h
  refine ⟨(AV_corner_transport S d).mpr hc, ?_⟩
  rcases h with ⟨hle, hmin⟩ | ⟨hall, rfl⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [← not_lt] at hle ⊢
      exact fun h' => hle (((AV_good_key_lt W hm hc).2).mpr h')
    · intro d'' hd'' hle''
      obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
      have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
      have hle' : geoMarkKey hP m ≤ geoMarkKey hP d' := by
        rw [← not_lt] at hle'' ⊢
        exact fun h' => hle'' (((AV_good_key_lt W hm hd').2).mp h')
      have hdd' := hmin d' hd' hle'
      rw [← not_lt] at hdd' ⊢
      exact fun h' => hdd' (((AV_good_key_lt W (AV_good_of_corner W hc) hd').2).mpr h')
  · right
    refine ⟨?_, markTransport_vertex hs 0⟩
    intro d'' hd''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    exact ((AV_good_key_lt W hm hd').2).mp (hall d' hd')

open scoped Classical in
/-- **The next corner of a good mark is carried across the wall.** -/
theorem AV_nextCorner_transport (W : AV_Wall hP hP' hs T S) {m : Mark P} (hm : AV_Good hP T S m) :
    AV_nextCorner hP' (transportSupport hs S) (markTransport hs m) =
      markTransport hs (AV_nextCorner hP S m) :=
  AV_ncspec_unique (AV_nextCorner_spec hP' _ _) (AV_ncspec_transport W hm (AV_nextCorner_spec hP S m))

theorem AV_csspec_transport (W : AV_Wall hP hP' hs T S) {x d : Mark P} (hx : IsTrueCorner S x)
    (h : AV_CSSpec hP S x d) :
    AV_CSSpec hP' (transportSupport hs S) (markTransport hs x) (markTransport hs d) := by
  obtain ⟨hc, h⟩ := h
  have hxg : AV_Good hP T S x := AV_good_of_corner W hx
  refine ⟨(AV_corner_transport S d).mpr hc, ?_⟩
  rcases h with ⟨hlt, hmin⟩ | ⟨hall, rfl⟩
  · left
    refine ⟨((AV_good_key_lt W hxg hc).1).mp hlt, ?_⟩
    intro d'' hd'' hlt''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    have hlt' : geoMarkKey hP x < geoMarkKey hP d' := ((AV_good_key_lt W hxg hd').1).mpr hlt''
    have hdd' := hmin d' hd' hlt'
    rw [← not_lt] at hdd' ⊢
    exact fun h' => hdd' (((AV_good_key_lt W (AV_good_of_corner W hc) hd').2).mpr h')
  · right
    refine ⟨?_, markTransport_vertex hs 0⟩
    intro d'' hd''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    have h1 := hall d' hd'
    rw [← not_lt] at h1 ⊢
    exact fun h' => h1 (((AV_good_key_lt W hxg hd').1).mpr h')

/-- The outgoing slot of a corner is a corner (itself, or the twin of a selected visit). -/
theorem AV_corner_selectedMarkPerm (S : Finset (Crossing P)) {c : Mark P} (hc : IsTrueCorner S c) :
    IsTrueCorner S (selectedMarkPerm S c) := by
  cases c with
  | inl i => exact isTrueCorner_vertex S i
  | inr v =>
    rw [selectedMarkPerm_visit, isTrueCorner_visit, selectedVisitTwin_crossing]
    exact hc

/-- **The corner successor of a corner is carried across the wall.** -/
theorem AV_cornerSucc_transport (W : AV_Wall hP hP' hs T S) {c : Mark P} (hc : IsTrueCorner S c) :
    AV_cornerSucc hP' (transportSupport hs S) (markTransport hs c) =
      markTransport hs (AV_cornerSucc hP S c) := by
  have h1 : AV_CSSpec hP' (transportSupport hs S) (markTransport hs (selectedMarkPerm S c))
      (AV_cornerSucc hP' (transportSupport hs S) (markTransport hs c)) := by
    unfold AV_cornerSucc
    rw [geoSmoothingSuccessor_apply, selectedMarkPerm_markTransport]
    exact AV_nextCorner_succ_spec hP' _ _
  have h2 : AV_CSSpec hP' (transportSupport hs S) (markTransport hs (selectedMarkPerm S c))
      (markTransport hs (AV_cornerSucc hP S c)) :=
    AV_csspec_transport W (AV_corner_selectedMarkPerm S hc)
      (by unfold AV_cornerSucc; rw [geoSmoothingSuccessor_apply]; exact AV_nextCorner_succ_spec hP S _)
  exact AV_csspec_unique h1 h2

/-! ### The carrier bijection across the wall -/

theorem AV_carrierMap_aux (W : AV_Wall hP hP' hs T S) (m : Mark P) :
    geoOwner hP' (transportSupport hs S)
        (markTransport hs (AV_nextCorner hP S (geoSmoothingSuccessor hP S m))) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := by
  by_cases hm : IsTrueCorner S m
  · change geoOwner hP' (transportSupport hs S) (markTransport hs (AV_cornerSucc hP S m)) = _
    rw [← AV_cornerSucc_transport W hm, AV_cornerSucc_owner, AV_nextCorner_of_corner hm]
  · rw [AV_smoothing_of_not_corner hP S hm, AV_nextCorner_succ hm]

theorem AV_carrierMap_pow (W : AV_Wall hP hP' hs T S) (m : Mark P) (k : ℕ) :
    geoOwner hP' (transportSupport hs S)
        (markTransport hs (AV_nextCorner hP S ((geoSmoothingSuccessor hP S ^ k) m))) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, AV_carrierMap_aux W, ih]

/-- The carrier map across the wall: the carrier of `P'` through the transported next corner. -/
noncomputable def AV_carrierMap (W : AV_Wall hP hP' hs T S) :
    GeoComponent hP S → GeoComponent hP' (transportSupport hs S) :=
  Quotient.lift
    (fun m => geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)))
    (fun a b hab => by
      obtain ⟨i, -, rfl⟩ :=
        (show (geoSmoothingSuccessor hP S).SameCycle a b from hab).exists_pow_eq'
      exact (AV_carrierMap_pow W a i).symm)

theorem AV_carrierMap_owner (W : AV_Wall hP hP' hs T S) (m : Mark P) :
    AV_carrierMap W (geoOwner hP S m) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := rfl

theorem AV_carrierInv_aux (W : AV_Wall hP hP' hs T S) (m' : Mark P') :
    geoOwner hP S ((markTransport hs).symm
        (AV_nextCorner hP' (transportSupport hs S) (geoSmoothingSuccessor hP' (transportSupport hs S) m'))) =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
  by_cases hm : IsTrueCorner (transportSupport hs S) m'
  · change geoOwner hP S ((markTransport hs).symm (AV_cornerSucc hP' (transportSupport hs S) m')) = _
    have hc : IsTrueCorner S ((markTransport hs).symm m') := by
      rw [← AV_corner_transport (hs := hs) S ((markTransport hs).symm m'), Equiv.apply_symm_apply]
      exact hm
    have := AV_cornerSucc_transport W hc
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply, AV_cornerSucc_owner, AV_nextCorner_of_corner hm]
  · rw [AV_smoothing_of_not_corner hP' _ hm, AV_nextCorner_succ hm]

theorem AV_carrierInv_pow (W : AV_Wall hP hP' hs T S) (m' : Mark P') (k : ℕ) :
    geoOwner hP S ((markTransport hs).symm
        (AV_nextCorner hP' (transportSupport hs S) ((geoSmoothingSuccessor hP' (transportSupport hs S) ^ k) m'))) =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, AV_carrierInv_aux W, ih]

/-- The inverse carrier map. -/
noncomputable def AV_carrierInv (W : AV_Wall hP hP' hs T S) :
    GeoComponent hP' (transportSupport hs S) → GeoComponent hP S :=
  Quotient.lift
    (fun m' => geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')))
    (fun a b hab => by
      obtain ⟨i, -, rfl⟩ :=
        (show (geoSmoothingSuccessor hP' (transportSupport hs S)).SameCycle a b from hab).exists_pow_eq'
      exact (AV_carrierInv_pow W a i).symm)

theorem AV_carrierInv_owner (W : AV_Wall hP hP' hs T S) (m' : Mark P') :
    AV_carrierInv W (geoOwner hP' (transportSupport hs S) m') =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := rfl

/-- **The carriers of `S` correspond to the carriers of the transported support across the wall**:
the corner cycles are carried (corner by corner, the non-corner marks may change carrier). -/
noncomputable def AV_carrierEquiv (W : AV_Wall hP hP' hs T S) :
    GeoComponent hP S ≃ GeoComponent hP' (transportSupport hs S) where
  toFun := AV_carrierMap W
  invFun := AV_carrierInv W
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h m =>
      change AV_carrierInv W (AV_carrierMap W (geoOwner hP S m)) = geoOwner hP S m
      rw [AV_carrierMap_owner, AV_carrierInv_owner,
        AV_nextCorner_of_corner ((AV_corner_transport S _).mpr (AV_nextCorner_corner hP S m)),
        Equiv.symm_apply_apply, AV_nextCorner_owner]
  right_inv q' := by
    induction q' using Quotient.inductionOn with
    | h m' =>
      change AV_carrierMap W (AV_carrierInv W (geoOwner hP' (transportSupport hs S) m')) =
        geoOwner hP' (transportSupport hs S) m'
      rw [AV_carrierInv_owner, AV_carrierMap_owner]
      have hc : IsTrueCorner S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
        rw [← AV_corner_transport (hs := hs) S, Equiv.apply_symm_apply]
        exact AV_nextCorner_corner hP' _ m'
      rw [AV_nextCorner_of_corner hc, Equiv.apply_symm_apply, AV_nextCorner_owner]

theorem AV_carrierEquiv_owner (W : AV_Wall hP hP' hs T S) (m : Mark P) :
    AV_carrierEquiv W (geoOwner hP S m) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := rfl

/-- **Ownership of good marks is carried**: a good mark lies on the copy of its carrier. -/
theorem AV_owner_transport (W : AV_Wall hP hP' hs T S) {m : Mark P} (hm : AV_Good hP T S m) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) =
      AV_carrierEquiv W (geoOwner hP S m) := by
  rw [AV_carrierEquiv_owner, ← AV_nextCorner_transport W hm, AV_nextCorner_owner]

theorem AV_owner_transport_corner (W : AV_Wall hP hP' hs T S) {m : Mark P} (hm : IsTrueCorner S m) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) =
      AV_carrierEquiv W (geoOwner hP S m) :=
  AV_owner_transport W (AV_good_of_corner W hm)

/-! ### The corner list of a carrier is carried literally -/

theorem AV_cornerList_pairwise (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) :
    (geoComponentCornerList hP S q).Pairwise (fun a b => geoMarkKey hP a < geoMarkKey hP b) := by
  unfold geoComponentCornerList geoComponentMarkList
  exact ((AV_geoMarkList_pairwise_lt hP).filter _).filter _

/-- **The corners of a carrier transport, in inherited order, to the corners of its copy**: both
lists are sorted by the key, have no duplicates and the same members (corner ownership is carried). -/
theorem AV_cornerList_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    (geoComponentCornerList hP S q).map (markTransport hs) =
      geoComponentCornerList hP' (transportSupport hs S) (AV_carrierEquiv W q) := by
  apply List.Perm.eq_of_pairwise (le := fun a b => geoMarkKey hP' a < geoMarkKey hP' b)
  · intro a b _ _ h1 h2
    exact absurd h2 (lt_asymm h1)
  · rw [List.pairwise_map]
    refine (AV_cornerList_pairwise hP S q).imp_of_mem ?_
    intro a b ha hb hab
    exact ((AV_good_key_lt W
      (AV_good_of_corner W ((mem_geoComponentCornerList hP S q a).mp ha).2)
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
      exact ⟨by rw [AV_owner_transport_corner W hc, hq], hc⟩
    · rintro ⟨hq, hc⟩
      refine ⟨?_, hc⟩
      rw [AV_owner_transport_corner W hc] at hq
      exact (AV_carrierEquiv W).injective hq

theorem AV_cornerCount_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCornerCount hP' (transportSupport hs S) (AV_carrierEquiv W q) = geoCornerCount hP S q := by
  unfold geoCornerCount
  rw [← AV_cornerList_eq W q, List.length_map]

theorem AV_cornerMark_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP' (transportSupport hs S) (AV_carrierEquiv W q)
        (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q).symm) k) =
      markTransport hs (geoCornerMark hP S q k) := by
  have hL := AV_cornerList_eq W q
  have hlen : k.val < (geoComponentCornerList hP' (transportSupport hs S) (AV_carrierEquiv W q)).length := by
    rw [← hL, List.length_map]; exact ZMod.val_lt k
  have h3 : k.val < ((geoComponentCornerList hP S q).map (markTransport hs)).length := by
    rw [List.length_map]; exact ZMod.val_lt k
  unfold geoCornerMark
  refine (geo_getElem_congr _ _ rfl _ _ _ hlen (geo_zmod_val_cast (AV_cornerCount_eq W q).symm k)).trans ?_
  refine (geo_getElem_congr _ _ hL.symm _ _ hlen h3 rfl).trans ?_
  exact List.getElem_map _

theorem AV_cornerMark_eq' (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (j : ZMod (geoCornerCount hP' (transportSupport hs S) (AV_carrierEquiv W q))) :
    geoCornerMark hP' (transportSupport hs S) (AV_carrierEquiv W q) j =
      markTransport hs (geoCornerMark hP S q (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q)) j)) := by
  have h := AV_cornerMark_eq W q (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q)) j)
  rwa [geo_zmod_cast_cast (AV_cornerCount_eq W q) j] at h

/-- The corner polygon of `q` read at the geometry of `P'` (the accepted
`GeoMarkTransport.transportedCornerPolygon`, on the wall bijection). -/
noncomputable def AV_tcp (_W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    LabelledTuple (geoCornerCount hP S q) :=
  fun k => traversalEvaluation P' (geoMarkPosition hP' (markTransport hs (geoCornerMark hP S q k)))

theorem AV_cornerPolygon_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCornerPolygon hP' (transportSupport hs S) (AV_carrierEquiv W q) =
      geoRecast (AV_cornerCount_eq W q) (AV_tcp W q) := by
  funext j
  show traversalEvaluation P' (geoMarkPosition hP' (geoCornerMark hP' (transportSupport hs S)
    (AV_carrierEquiv W q) j)) = _
  rw [AV_cornerMark_eq' W q j]
  rfl

theorem AV_tcp_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    AV_tcp W q =
      geoRecast (AV_cornerCount_eq W q).symm
        (geoCornerPolygon hP' (transportSupport hs S) (AV_carrierEquiv W q)) := by
  rw [AV_cornerPolygon_eq W q]
  funext k
  rw [geoRecast_apply, geoRecast_apply, geo_zmod_cast_cast' (AV_cornerCount_eq W q) k]

theorem AV_turn_tcp_eq_turn_cast (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (AV_tcp W q) k =
      turn (geoCornerPolygon hP' (transportSupport hs S) (AV_carrierEquiv W q))
        (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q).symm) k) := by
  rw [AV_cornerPolygon_eq W q, turn_geoRecast_cast]

/-- **Corner turns are carried across the wall**: vertex corners by `turn_eq`, smoothing corners by
`sign_eq` (the accepted `GeoMarkTransport.turn_transportedCornerPolygon`, on the wall bijection). -/
theorem AV_turn_tcp (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (AV_tcp W q) k = turn (geoCornerPolygon hP S q) k := by
  have hS := W.indep
  have hS' := W.indep'
  rw [AV_turn_tcp_eq_turn_cast W q k]
  have hmark := AV_cornerMark_eq W q k
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

theorem AV_turn_cornerPolygon_eq (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (j : ZMod (geoCornerCount hP' (transportSupport hs S) (AV_carrierEquiv W q))) :
    turn (geoCornerPolygon hP' (transportSupport hs S) (AV_carrierEquiv W q)) j =
      turn (geoCornerPolygon hP S q) (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q)) j) := by
  have h := AV_turn_tcp_eq_turn_cast W q (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q)) j)
  rw [geo_zmod_cast_cast (AV_cornerCount_eq W q) j] at h
  rw [← h, AV_turn_tcp W hn q]

/-- Uniformity of a carrier is carried across the wall. -/
theorem AV_carrierUniform_iff (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S) :
    geoCarrierUniform hP' (transportSupport hs S) (AV_carrierEquiv W q) ↔ geoCarrierUniform hP S q := by
  unfold geoCarrierUniform
  rw [AV_cornerPolygon_eq W q]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  rw [forall_turn_geoRecast]
  simp only [AV_turn_tcp W hn q]

/-- The selector (`wt`) of a carrier is carried across the wall. -/
theorem AV_selector_eq (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S) :
    geoCarrierSelector hP' (transportSupport hs S) (AV_carrierEquiv W q) = geoCarrierSelector hP S q := by
  unfold geoCarrierSelector
  rw [AV_cornerPolygon_eq W q, cornerSelector_geoRecast]
  exact cornerSelector_congr_turn (AV_turn_tcp W hn q)

/-- `wind(S)` is carried across the wall. -/
theorem AV_geoWind_eq (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) :
    geoWind hP' (transportSupport hs S) = geoWind hP S := by
  unfold geoWind
  exact (Fintype.prod_equiv (AV_carrierEquiv W) _ _ fun q => (AV_selector_eq W hn q).symm).symm

/-! ### Retained crossings, `U`, pieces -/

/-- A retained crossing of a carrier is not dominated (def:smoothing: a neighbour of `S` is a
crossing of no carrier). -/
theorem AV_not_dom_of_retained (W : AV_Wall hP hP' hs T S) {q : GeoComponent hP S} {x : Crossing P}
    (hx : x ∈ geoCarrierCrossings hP S q) (hd : AV_Dom hP T S x) : False := by
  obtain ⟨s, hsS, -, hxs⟩ := hd
  exact geo_neighbor_not_mem_geoCarrierCrossings hP W.indep
    ((mem_geoSupportNeighbors hP S x).mpr ⟨s, hsS, hxs⟩) q hx

theorem AV_not_mem_U_of_dom {x : Crossing P} (hd : AV_Dom hP T S x) : x ∉ CV.U hP S := by
  intro hx
  obtain ⟨s, hsS, -, hxs⟩ := hd
  exact ((CV.mem_U_iff hP S x).mp hx).2 s hsS hxs

omit [NeZero n] in
/-- The visits of an undominated crossing are good marks. -/
theorem AV_good_of_not_dom {x : Crossing P} (hx : ¬ AV_Dom hP T S x) (v : Visit P) (hv : v.1 = x) :
    AV_Good hP T S (Sum.inr v) := by
  intro w hw _
  obtain rfl := Sum.inr.inj hw
  rw [hv]
  exact hx

theorem AV_good_of_mem_U {x : Crossing P} (hx : x ∈ CV.U hP S) (v : Visit P) (hv : v.1 = x) :
    AV_Good hP T S (Sum.inr v) :=
  AV_good_of_not_dom (fun hd => AV_not_mem_U_of_dom hd hx) v hv

/-- **The retained crossings of a carrier are carried to those of its copy** (a dominated crossing
is retained by no carrier on either side; the visits of an undominated crossing are good marks). -/
theorem AV_geoCarrierCrossings_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCarrierCrossings hP' (transportSupport hs S) (AV_carrierEquiv W q) =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding := by
  classical
  ext x'
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hdom : AV_Dom hP T S x
  · refine iff_of_false ?_ ?_
    · obtain ⟨s', hsS', -, hxs'⟩ := W.dom_transport hdom
      exact geo_neighbor_not_mem_geoCarrierCrossings hP' W.indep'
        ((mem_geoSupportNeighbors hP' _ _).mpr ⟨s', hsS', hxs'⟩) _
    · exact fun h => AV_not_dom_of_retained W h hdom
  · rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings, mem_transportSupport_iff]
    apply and_congr Iff.rfl
    constructor
    · intro hw v hv
      have := hw (visitTransport hs v) (by rw [visitTransport_crossing, hv])
      rw [← markTransport_visit, AV_owner_transport W (AV_good_of_not_dom hdom v hv)] at this
      exact (AV_carrierEquiv W).injective this
    · intro hv w hw
      obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
      rw [visitTransport_crossing] at hw
      have hvx : v.1 = x := (crossingTransport hs).injective hw
      rw [← markTransport_visit, AV_owner_transport W (AV_good_of_not_dom hdom v hvx), hv v hvx]

theorem AV_card_geoCarrierCrossings_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    (geoCarrierCrossings hP' (transportSupport hs S) (AV_carrierEquiv W q)).card =
      (geoCarrierCrossings hP S q).card := by
  rw [AV_geoCarrierCrossings_eq W q, Finset.card_map]

/-- `U(S)` is carried across the wall. -/
theorem AV_mem_U_iff (W : AV_Wall hP hP' hs T S) (y : Crossing P) :
    crossingTransport hs y ∈ CV.U hP' (transportSupport hs S) ↔ y ∈ CV.U hP S := by
  rw [CV.mem_U_iff, CV.mem_U_iff, mem_transportSupport_iff]
  by_cases hyS : y ∈ S
  · exact iff_of_false (fun h => h.1 hyS) (fun h => h.1 hyS)
  by_cases hdom : AV_Dom hP T S y
  · refine iff_of_false ?_ ?_
    · obtain ⟨s', hs', -, h⟩ := W.dom_transport hdom
      exact fun h' => h'.2 s' hs' h
    · obtain ⟨s, hsS, -, h⟩ := hdom
      exact fun h' => h'.2 s hsS h
  · apply and_congr Iff.rfl
    have hnT : ∀ x ∈ S, ¬ (y ∈ T ∧ x ∈ T) := by
      intro x hxS ⟨hyT, hxT⟩
      have hne : y ≠ x := fun e => hyS (e ▸ hxS)
      rcases W.dominated y hyT x hxT hne with hd | hd
      · exact hdom hd
      · exact W.not_dom_of_mem hxS hd
    constructor
    · intro h x hxS h'
      exact h (crossingTransport hs x) ((mem_transportSupport_iff hs S x).mpr hxS)
        ((W.interlaces_iff y x (hnT x hxS)).mp h')
    · intro h x' hx' h'
      obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
      rw [mem_transportSupport_iff] at hx'
      exact h x hx' ((W.interlaces_iff y x (hnT x hx')).mpr h')

/-- **The residual graphs are isomorphic across the wall** (`U(S)` is carried and interlacement on
`U(S)` is carried: two undominated distinct `T`-crossings cannot both lie in `U(S)`). -/
noncomputable def AV_residualIso (W : AV_Wall hP hP' hs T S) :
    CV.residualGraph hP S ≃g CV.residualGraph hP' (transportSupport hs S) where
  toEquiv := Equiv.subtypeEquiv (crossingTransport hs) (fun y => (AV_mem_U_iff W y).symm)
  map_rel_iff' := by
    intro a b
    show GeometricInterlaces hP' (crossingTransport hs a.1) (crossingTransport hs b.1) ↔
      GeometricInterlaces hP a.1 b.1
    by_cases hab : a.1 = b.1
    · rw [hab]
      exact iff_of_false (geometricInterlaces_irrefl hP' _) (geometricInterlaces_irrefl hP _)
    · have hnT : ¬ (a.1 ∈ T ∧ b.1 ∈ T) := by
        rintro ⟨haT, hbT⟩
        rcases W.dominated a.1 haT b.1 hbT hab with hd | hd
        · exact AV_not_mem_U_of_dom hd a.2
        · exact AV_not_mem_U_of_dom hd b.2
      exact (W.interlaces_iff a.1 b.1 hnT).symm

theorem AV_residualIso_apply_val (W : AV_Wall hP hP' hs T S) (a : ↑(CV.U hP S)) :
    ((AV_residualIso W) a).1 = crossingTransport hs a.1 := rfl

/-- **The pieces of `S` correspond to the pieces of the transported support** across the wall. -/
noncomputable def AV_pieceEquiv (W : AV_Wall hP hP' hs T S) :
    CV.Piece hP S ≃ CV.Piece hP' (transportSupport hs S) :=
  (AV_residualIso W).connectedComponentEquiv

theorem AV_pieceEquiv_pieceOf (W : AV_Wall hP hP' hs T S) (c : Crossing P) (hc : c ∈ CV.U hP S) :
    AV_pieceEquiv W (CV.pieceOf hP S c hc) =
      CV.pieceOf hP' (transportSupport hs S) (crossingTransport hs c) ((AV_mem_U_iff W c).mpr hc) := by
  unfold AV_pieceEquiv CV.pieceOf
  rw [SimpleGraph.Iso.connectedComponentEquiv_apply, SimpleGraph.ConnectedComponent.map_mk]
  rfl

/-- The labels of a piece are carried. -/
theorem AV_pieceLabels_eq (W : AV_Wall hP hP' hs T S) (H : CV.Piece hP S) :
    CV.pieceLabels hP' (transportSupport hs S) (AV_pieceEquiv W H) =
      (CV.pieceLabels hP S H).map (crossingTransport hs).toEmbedding := by
  ext c'
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, CV.mem_pieceLabels, CV.mem_pieceLabels]
  constructor
  · rintro ⟨hc', hH⟩
    have hc : c ∈ CV.U hP S := (AV_mem_U_iff W c).mp hc'
    refine ⟨hc, (AV_pieceEquiv W).injective ?_⟩
    rw [AV_pieceEquiv_pieceOf]
    exact hH
  · rintro ⟨hc, hH⟩
    refine ⟨(AV_mem_U_iff W c).mpr hc, ?_⟩
    rw [← AV_pieceEquiv_pieceOf W c hc, hH]

theorem AV_pieceWrithe_eq (W : AV_Wall hP hP' hs T S) (H : CV.Piece hP S) :
    CV.pieceWrithe hP' (transportSupport hs S) (AV_pieceEquiv W H) = CV.pieceWrithe hP S H := by
  unfold CV.pieceWrithe
  rw [AV_pieceLabels_eq, Finset.card_map]

/-- The pieces assigned to a carrier are carried onto the pieces assigned to its copy (the visits of
the labels are good marks). -/
theorem AV_mem_piecesOn_transport_iff (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (H : CV.Piece hP S) :
    AV_pieceEquiv W H ∈ CV.piecesOn hP' (transportSupport hs S) (AV_carrierEquiv W q) ↔
      H ∈ CV.piecesOn hP S q := by
  rw [CV.mem_piecesOn, CV.mem_piecesOn, AV_pieceLabels_eq]
  constructor
  · intro hall c hc v hv
    have := hall (crossingTransport hs c) (Finset.mem_map_of_mem _ hc)
      (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit,
      AV_owner_transport W (AV_good_of_mem_U (CV.pieceLabels_subset hP S H hc) v hv)] at this
    exact (AV_carrierEquiv W).injective this
  · intro hall c' hc' w hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hc'
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
    rw [visitTransport_crossing] at hw
    have hv : v.1 = c := (crossingTransport hs).injective hw
    rw [← markTransport_visit,
      AV_owner_transport W (AV_good_of_mem_U (CV.pieceLabels_subset hP S H hc) v hv), hall c hc v hv]

theorem AV_piecesOn_transport_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    CV.piecesOn hP' (transportSupport hs S) (AV_carrierEquiv W q) =
      (CV.piecesOn hP S q).map (AV_pieceEquiv W).toEmbedding := by
  ext H'
  obtain ⟨H, rfl⟩ := (AV_pieceEquiv W).surjective H'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, AV_mem_piecesOn_transport_iff]

/-! ### The HOMFLY polynomial of the positive lift is carried across the wall -/

section AVLift

variable (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (W : AV_Wall hG.cg hG'.cg hs T S) (hS : GeoIndependent hG.cg S)
  (hS' : GeoIndependent hG'.cg (transportSupport hs S)) (q : GeoComponent hG.cg S)

/-- The occurrences of the two lifts correspond through the parent visits and the canonical visit
identification ("the identity map on the visits", d6:67, across the wall). -/
noncomputable def AV_liftEquiv :
    (geoPositiveLift hn hG hS q).Γ.Visit ≃
      (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).Γ.Visit :=
  (CV.liftVisitEquiv hn hG hS q).trans
    ((Equiv.subtypeEquiv (visitTransport hs) (fun w => by
        rw [AV_geoCarrierCrossings_eq W q, visitTransport_crossing, Finset.mem_map_equiv,
          Equiv.symm_apply_apply])).trans
      (CV.liftVisitEquiv hn hG' hS' (AV_carrierEquiv W q)).symm)

theorem AV_liftVisit_liftEquiv (v : (geoPositiveLift hn hG hS q).Γ.Visit) :
    CV.liftVisit hn hG' hS' (AV_carrierEquiv W q) (AV_liftEquiv hn hG hG' W hS hS' q v) =
      visitTransport hs (CV.liftVisit hn hG hS q v) := by
  show CV.liftVisit hn hG' hS' _ ((CV.liftVisitEquiv hn hG' hS' _).symm _) = _
  rw [CV.liftVisit_symm]
  rfl

/-- **The HOMFLY polynomial of the positive lift of a carrier is carried across the wall**: the
occurrence bijection is a record isomorphism — (a) cyclic order by the carried visit keys (no two
retained crossings form a reversed same-edge pair), (b) double points by the twin pairing, (c) over/under
by the carried crossing signs, (d) all signs `+1` — and CV:ax:gausscode (`gausscode_polynomial`). -/
theorem AV_homfly_lift_eq :
    homfly (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)) = homfly (geoPositiveLift hn hG hS q) := by
  have hΦ := AV_liftVisit_liftEquiv hn hG hG' W hS hS' q
  have hkey : ∀ v w : (geoPositiveLift hn hG hS q).Γ.Visit,
      geometricVisitKey hG.cg (CV.liftVisit hn hG hS q v) <
          geometricVisitKey hG.cg (CV.liftVisit hn hG hS q w) ↔
        geometricVisitKey hG'.cg (visitTransport hs (CV.liftVisit hn hG hS q v)) <
          geometricVisitKey hG'.cg (visitTransport hs (CV.liftVisit hn hG hS q w)) := by
    intro v w
    apply W.key_lt
    rintro ⟨hvT, hwT, hne, -⟩
    rcases W.dominated _ hvT _ hwT hne with hd | hd
    · exact AV_not_dom_of_retained W (CV.liftVisit_mem hn hG hS q v) hd
    · exact AV_not_dom_of_retained W (CV.liftVisit_mem hn hG hS q w) hd
  have hdata : CV.IsRecordIsoData (geoPositiveLift hn hG hS q)
      (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)) (AV_liftEquiv hn hG hG' W hS hS' q) :=
    { cyclic_order := fun v w u hb => by
        rw [CV.visitBetween_iff_key, hΦ, hΦ, hΦ]
        rw [CV.visitBetween_iff_key] at hb
        unfold cycBetween at hb ⊢
        rw [← hkey, ← hkey, ← hkey]
        exact hb
      double_points :=
        (CV.carriesDoublePoints_iff (ρ := (geoPositiveLift hn hG hS q).record)
          (ρ' := (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).record)
          (AV_liftEquiv hn hG hG' W hS hS' q)).2 fun v => by
          apply CV.liftVisit_injective hn hG' hS' (AV_carrierEquiv W q)
          change CV.liftVisit hn hG' hS' _
              (AV_liftEquiv hn hG hG' W hS hS' q ((geoPositiveLift hn hG hS q).twin v)) =
            CV.liftVisit hn hG' hS' _
              ((geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).twin
                (AV_liftEquiv hn hG hG' W hS hS' q v))
          rw [hΦ, CV.liftVisit_twin hn hG hS q, CV.liftVisit_twin hn hG' hS', hΦ, visitTransport_visitTwin]
      over_under :=
        (CV.carriesOverUnder_iff (ρ := (geoPositiveLift hn hG hS q).record)
          (ρ' := (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).record)
          (AV_liftEquiv hn hG hG' W hS hS' q)).2 fun v => by
          change (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).overBit
              (AV_liftEquiv hn hG hG' W hS hS' q v) = (geoPositiveLift hn hG hS q).overBit v
          rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΦ,
            ← visitTransport_visitTwin, visitTransport_edge, visitTransport_edge]
          have hcross : IsCrossing P {(CV.liftVisit hn hG hS q v).2.val,
              (visitTwin (CV.liftVisit hn hG hS q v)).2.val} := by
            rw [← visit_crossing_val_eq_pair]
            exact (CV.liftVisit hn hG hS q v).1.property
          have hsign := W.sign_eq _ _ hcross
          unfold crossingSign at hsign
          constructor
          · intro h
            exact sign_eq_one_iff.mp (by rw [← hsign]; exact sign_pos h)
          · intro h
            exact sign_eq_one_iff.mp (by rw [hsign]; exact sign_pos h)
      signs := fun v => by
        change (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).sign
            (AV_liftEquiv hn hG hG' W hS hS' q v).1 = (geoPositiveLift hn hG hS q).sign v.1
        rw [geoPositiveLift_sign, geoPositiveLift_sign] }
  exact (CV.gausscode_polynomial _ _ (geoPositiveLift_componentCount hn hG hS q)
    (geoPositiveLift_componentCount hn hG' hS' _)
    (CV.recordIsoOfData (geoPositiveLift_componentCount hn hG hS q)
      (geoPositiveLift_componentCount hn hG' hS' _) _ hdata)).symm

end AVLift

/-! ### The rotation of a carrier is carried across the wall (CV:def:rot's ray formula) -/

theorem AV_edge_geoRecast {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k) (f : LabelledTuple k)
    (j : ZMod k') : edge (geoRecast hk f) j = edge f (Equiv.cast (congrArg ZMod hk) j) := by
  subst hk
  rfl

/-- The edge label of the outgoing slot of a mark is carried (vertices by label, visits by edge). -/
theorem AV_outSlot_transport (S : Finset (Crossing P)) (a : Mark P) :
    (geoOutSlot hP' (transportSupport hs S) (markTransport hs a)).1 = (geoOutSlot hP S a).1 := by
  unfold geoOutSlot
  rw [selectedMarkPerm_markTransport]
  generalize selectedMarkPerm S a = b
  cases b <;> rfl

theorem AV_edge_tcp (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      edge (AV_tcp W q) k = c • edge P' (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  rw [AV_tcp_eq W q, AV_edge_geoRecast]
  obtain ⟨c, hc, h⟩ := geoCornerPolygon_edge_smul hn hP' W.indep' (AV_carrierEquiv W q)
    (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q).symm) k)
  refine ⟨c, hc, ?_⟩
  rw [h, AV_cornerMark_eq' W q, geo_zmod_cast_cast' (AV_cornerCount_eq W q) k, AV_outSlot_transport]

theorem AV_sign_det_smul_left (c : ℝ) (hc : 0 < c) (u r : Plane) :
    SignType.sign (det (c • u) r) = SignType.sign (det u r) := by
  rw [CV.det_smul_left', sign_mul, sign_pos hc, one_mul]

theorem AV_sign_det_smul_right (c : ℝ) (hc : 0 < c) (r u : Plane) :
    SignType.sign (det r (c • u)) = SignType.sign (det r u) := by
  rw [det_smul_right, sign_mul, sign_pos hc, one_mul]

theorem AV_sign_det_swap (u r : Plane) : SignType.sign (det u r) = -SignType.sign (det r u) := by
  rw [det_swap r u, Left.sign_neg]

/-- **The rotation number of the corner polygon is carried across the wall**: `2π rot = Σ τ_i`
(lem:turnlift (ii)) and `rot = Σ_i ε_i(r)` with `ε_i` a function of three determinant signs
(CV:def:rot, `epsRot_eq_epsOfSigns`), each of which is carried — the corner turns by `AV_turn_tcp`,
the ray signs because both corner polygons run along the same original edges and `r` sees those
edges with the same sign on both sides. -/
theorem AV_rotationNumber_tcp (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (W : AV_Wall hG.cg hG'.cg hs T S) (q : GeoComponent hG.cg S) :
    rotationNumber (AV_tcp W q) = rotationNumber (geoCornerPolygon hG.cg S q) := by
  obtain ⟨r, hr⟩ := W.ray
  have hL : CV.Regular (geoCornerPolygon hG.cg S q) :=
    (CV.regular_iff_sm _).mpr (geoCornerPolygon_regular hn hG W.indep q)
  have hL'' : CV.Regular (AV_tcp W q) := by
    rw [CV.regular_iff_sm, AV_tcp_eq W q, regular_geoRecast]
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
  have hadm'' : CV.Admissible (AV_tcp W q) r := by
    intro k
    obtain ⟨c, hc, h⟩ := AV_edge_tcp W hn q k
    rw [h, det_smul_right]
    exact mul_ne_zero hc.ne' (hr' _)
  rw [← CV.rotRay_eq_rotationNumber hL hadm, ← CV.rotRay_eq_rotationNumber hL'' hadm'']
  congr 1
  unfold CV.rotRay
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [CV.epsRot_eq_epsOfSigns, CV.epsRot_eq_epsOfSigns]
  have hturn : SignType.sign (det (edge (AV_tcp W q) (k - 1)) (edge (AV_tcp W q) k)) =
      SignType.sign (det (edge (geoCornerPolygon hG.cg S q) (k - 1))
        (edge (geoCornerPolygon hG.cg S q) k)) := by
    rw [← turn_det, ← turn_det]
    exact AV_turn_tcp W hn q k
  have hray : ∀ j : ZMod (geoCornerCount hG.cg S q),
      SignType.sign (det r (edge (AV_tcp W q) j)) =
        SignType.sign (det r (edge (geoCornerPolygon hG.cg S q) j)) := by
    intro j
    obtain ⟨c, hc, h⟩ := AV_edge_tcp W hn q j
    obtain ⟨c', hc', h'⟩ := geoCornerPolygon_edge_smul hn hG.cg W.indep q j
    rw [h, h', AV_sign_det_smul_right c hc, AV_sign_det_smul_right c' hc']
    exact (hr _).2
  have hray' : ∀ j : ZMod (geoCornerCount hG.cg S q),
      SignType.sign (det (edge (AV_tcp W q) j) r) =
        SignType.sign (det (edge (geoCornerPolygon hG.cg S q) j) r) := by
    intro j
    rw [AV_sign_det_swap (edge (AV_tcp W q) j) r,
      AV_sign_det_swap (edge (geoCornerPolygon hG.cg S q) j) r, hray j]
  rw [hturn, hray' (k - 1), hray k]

/-! ### The per-carrier objects of def:X1 across the wall (`CV.Generic` binders) -/

omit [NeZero n] in
theorem AV_transportSupport_union {P P' : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
    (A B : Finset (Crossing P)) :
    transportSupport hs (A ∪ B) = transportSupport hs A ∪ transportSupport hs B := by
  ext x'
  simp only [transportSupport, Finset.mem_map, Finset.mem_union]
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

/-- `Finset.subset_union_left` with the `DecidableEq` instance as an explicit argument (the CV
library's unions carry the classical instance, `RProof.Cores` the decidable one; passing the instance
avoids re-synthesis). -/
theorem AV_subset_union_left' {α : Type*} (inst : DecidableEq α) (s t : Finset α) :
    s ⊆ @Union.union _ (@Finset.instUnion _ inst) s t :=
  @Finset.subset_union_left _ inst s t

section AVGeneric

/-- `w_{S,L}` is carried across the wall (it is the number of retained crossings). -/
theorem AV_groupedWrithe_eq (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.groupedWrithe hG' (AV_carrierEquiv W q) = CV.groupedWrithe hG q := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG' hS',
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS, AV_card_geoCarrierCrossings_eq W q]

/-- **The piece polynomials are carried across the wall**: at `P'` the carrier of `S' ∪ K'` (the
support chosen at `P'`) and the wall copy of the carrier of `S ∪ K_H` (the support chosen at `P`)
retain exactly the labels of the piece, so their lifts have the same polynomial (CV:lem:pieceintrinsic,
`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`), and the wall copy's lift has the polynomial of
the lift at `P` (`AV_homfly_lift_eq`, the wall data passed to `S ∪ K_H`). -/
theorem AV_pieceHomfly_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (H : CV.Piece hG.crossingGeometry S) :
    CV.pieceHomfly hn (hG'.diagrammatic hn) hS' (AV_pieceEquiv W H) =
      CV.pieceHomfly hn (hG.diagrammatic hn) hS H := by
  have hSK := CV.pieceSupport_mem_Ind (hG.diagrammatic hn) hS H
  have W₂ := W.mono (AV_subset_union_left' _ S _) (CV.geoIndependent_of_mem_Ind _ hSK)
  have hK2 := W₂.indep'
  have hcross : geoCarrierCrossings hG'.crossingGeometry _
      (CV.pieceCarrier (hG'.diagrammatic hn) hS' (AV_pieceEquiv W H)) =
      geoCarrierCrossings hG'.crossingGeometry _
        (AV_carrierEquiv W₂ (CV.pieceCarrier (hG.diagrammatic hn) hS H)) := by
    rw [CV.pieceCarrier_geoCarrierCrossings, AV_pieceLabels_eq W H, AV_geoCarrierCrossings_eq W₂,
      CV.pieceCarrier_geoCarrierCrossings]
  unfold CV.pieceHomfly CV.pieceDiagram
  rw [CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn
    (CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn))
    (CV.pieceSupport_geoIndependent (hG'.diagrammatic hn) hS' (AV_pieceEquiv W H)) hK2
    (CV.pieceCarrier (hG'.diagrammatic hn) hS' (AV_pieceEquiv W H)) _ hcross]
  exact AV_homfly_lift_eq hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
    (CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn)) W₂
    (CV.pieceSupport_geoIndependent (hG.diagrammatic hn) hS H) hK2
    (CV.pieceCarrier (hG.diagrammatic hn) hS H)

/-- `P_{S,L}` is carried across the wall. -/
theorem AV_groupedPoly_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.groupedPoly hn hG' hS' (AV_carrierEquiv W q) = CV.groupedPoly hn hG hS q := by
  unfold CV.groupedPoly
  rw [AV_piecesOn_transport_eq W q, Finset.prod_map]
  exact Finset.prod_congr rfl fun H _ => AV_pieceHomfly_eq hn hG hG' W hS hS' H

/-- `R(L) = |rot(L)|` is carried across the wall. -/
theorem AV_carrierR_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.carrierR hn hG' hS' (AV_carrierEquiv W q) = CV.carrierR hn hG hS q := by
  unfold CV.carrierR CV.rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [CV.rot_eq_rotationNumber, CV.rot_eq_rotationNumber, AV_cornerPolygon_eq W q,
    rotationNumber_geoRecast]
  exact AV_rotationNumber_tcp hn (CarrierGeometry.ofCV hG) (CarrierGeometry.ofCV hG') W q

/-- The slot `1 − w_{S,L} − R(L)` is carried across the wall. -/
theorem AV_slot_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.slot hn hG' hS' (AV_carrierEquiv W q) = CV.slot hn hG hS q := by
  unfold CV.slot
  rw [AV_groupedWrithe_eq hG hG' W hS hS' q, AV_carrierR_eq hn hG hG' W hS hS' q]

/-- The factor `Ω₁(S,L)` is carried across the wall. -/
theorem AV_Omega1_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.Omega1 hn hG' hS' (AV_carrierEquiv W q) = CV.Omega1 hn hG hS q := by
  unfold CV.Omega1
  rw [AV_slot_eq hn hG hG' W hS hS' q, AV_groupedPoly_eq hn hG hG' W hS hS' q]

/-- `wt` (CV:def:wind) is carried across the wall. -/
theorem AV_weight_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S) (q : GeoComponent hG.crossingGeometry S) :
    CV.weight hG'.crossingGeometry (transportSupport hs S) (AV_carrierEquiv W q) =
      CV.weight hG.crossingGeometry S q :=
  AV_selector_eq W hn q

/-- `wind(S)` (CV:def:wind) is carried across the wall. -/
theorem AV_wind_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S) :
    CV.wind hG'.crossingGeometry (transportSupport hs S) = CV.wind hG.crossingGeometry S :=
  AV_geoWind_eq W hn

end AVGeneric

/-! ### The event data: turn signs, crossing signs and a common reference vector near the wall -/

/-- The sign data of the event on a punctured radius `δ`: vertex turns and crossing signs agree at
any two punctured parameters (lem:guardconst on the unconditional `G1` members and on the active `G5`
members, none of which lies in the zero set of a simple RIII event), and one reference vector `r` sees
every edge direction with its central sign. -/
structure AV_EventRadius (E : CV.Event n) (δ : ℝ) : Prop where
  turn_eq : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' →
    ∀ i, turn (E.curve t') i = turn (E.curve t) i
  sign_eq : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' →
    ∀ i j, IsCrossing (E.curve t) {i, j} → crossingSign (E.curve t') i j = crossingSign (E.curve t) i j
  ray : ∃ r : Plane, ∀ t : E.Parameter, Punctured E δ t → ∀ h : ZMod n,
    det r (edge (E.curve t) h) ≠ 0 ∧
      SignType.sign (det r (edge (E.curve t) h)) = SignType.sign (det r (edge E.center h))

theorem AV_eventRadius_mono {E : CV.Event n} {δ δ' : ℝ} (h : δ' ≤ δ) (hR : AV_EventRadius E δ) :
    AV_EventRadius E δ' where
  turn_eq t t' ht ht' := hR.turn_eq t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  sign_eq t t' ht ht' := hR.sign_eq t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  ray := by
    obtain ⟨r, hr⟩ := hR.ray
    exact ⟨r, fun t ht => hr t (F1.punctured_mono h ht)⟩

theorem AV_g1_not_mem_zeroSet {E : CV.Event n} {e f g : ZMod n} {h3 h4e h4f h4g}
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) (i : ZMod n) : CV.Member.g1 i ∉ E.zeroSet := by
  rw [hE.1]; simp

omit [NeZero n] in
theorem AV_turn_eq_sign_G1 (P : LabelledTuple n) (i : ZMod n) :
    turn P i = SignType.sign (CV.G1 P i) :=
  turn_det P i

/-- The continuity of a determinant with a fixed vector along the event. -/
theorem AV_continuous_det (E : CV.Event n) (r : Plane) (h : ZMod n) :
    Continuous fun t : E.Parameter => det r (edge (E.curve t) h) := by
  have h1 : Continuous fun t : E.Parameter => E.curve t (h + 1) :=
    (continuous_apply (h + 1)).comp E.continuous_curve
  have h0 : Continuous fun t : E.Parameter => E.curve t h :=
    (continuous_apply h).comp E.continuous_curve
  simp only [det, edge, Prod.fst_sub, Prod.snd_sub]
  exact (continuous_const.mul (h1.snd.sub h0.snd)).sub (continuous_const.mul (h1.fst.sub h0.fst))

/-- **The sign data exist on some punctured radius** for every simple RIII event. -/
theorem AV_exists_eventRadius {E : CV.Event n} {e f g : ZMod n} {h3 h4e h4f h4g}
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AV_EventRadius E δ := by
  obtain ⟨t0, ht0⟩ := G1.exists_punctured_parameter E
  -- (1) turns: the `G1` members are unconditional and outside `Z`
  have hturn : ∀ᶠ t in nhds E.zeroParameter, ∀ i : ZMod n,
      SignType.sign (CV.G1 (E.curve t) i) = SignType.sign (CV.G1 E.center i) := by
    rw [Filter.eventually_all]
    intro i
    exact (G1.eventually_sign_eq_of_not_mem (CV.Member.g1 i) ⟨t0, ht0, Or.inl trivial⟩
      (AV_g1_not_mem_zeroSet hE i)).mono fun t ht => ht.2
  obtain ⟨δ₁, hδ₁, hδ₁r, h1⟩ := (E.eventually_center_iff_radius _).mp hturn
  -- (2) crossing signs: the `G5` members active at some punctured parameter are outside `Z`
  have hsign : ∀ᶠ t in nhds E.zeroParameter, ∀ ab : ZMod n × ZMod n,
      (∃ t₁ : E.Parameter, t₁.val ≠ 0 ∧ IsCrossing (E.curve t₁) {ab.1, ab.2}) →
        SignType.sign (CV.G5 (E.curve t) ab.1 ab.2) = SignType.sign (CV.G5 E.center ab.1 ab.2) := by
    rw [Filter.eventually_all]
    rintro ⟨a, b⟩
    by_cases hex : ∃ t₁ : E.Parameter, t₁.val ≠ 0 ∧ IsCrossing (E.curve t₁) {a, b}
    · obtain ⟨t₁, ht₁, hab⟩ := hex
      have hr : remote a b := crossing_pair_remote hab
      have hcr : CV.Crosses (E.curve t₁) a b := ((genericAt E t₁ ht₁).crosses_iff a b).mpr hab
      rcases CV.rep_lt_or_lt (remote_endpoints a b hr).1.symm with hlt | hlt
      · exact (G1.eventually_sign_eq_of_not_mem (CV.Member.g5 a b ⟨hr, hlt⟩)
          ⟨t₁, ht₁, Or.inr hcr⟩ (G1.g5_not_mem_zeroSet hE a b ⟨hr, hlt⟩)).mono fun t ht _ => ht.2
      · have hab' : IsCrossing (E.curve t₁) {b, a} := by rwa [Finset.pair_comm]
        have hcr' : CV.Crosses (E.curve t₁) b a := ((genericAt E t₁ ht₁).crosses_iff b a).mpr hab'
        refine (G1.eventually_sign_eq_of_not_mem (CV.Member.g5 b a ⟨remote_symm hr, hlt⟩)
          ⟨t₁, ht₁, Or.inr hcr'⟩ (G1.g5_not_mem_zeroSet hE b a ⟨remote_symm hr, hlt⟩)).mono
          fun t ht _ => ?_
        have h5 : ∀ Q : LabelledTuple n, CV.G5 Q a b = -CV.G5 Q b a := fun Q => by
          unfold CV.G5; exact det_swap _ _
        rw [h5, h5, Left.sign_neg, Left.sign_neg]
        exact congrArg _ ht.2
    · exact Filter.Eventually.of_forall fun t h => absurd h hex
  obtain ⟨δ₂, hδ₂, -, h2⟩ := (E.eventually_center_iff_radius _).mp hsign
  -- (3) a reference vector admissible for the centre keeps its signs near the centre
  obtain ⟨r, hr⟩ := CV.exists_admissible (L := E.center) E.center_polygon
  have hray : ∀ᶠ t in nhds E.zeroParameter, ∀ h : ZMod n,
      det r (edge (E.curve t) h) ≠ 0 ∧
        SignType.sign (det r (edge (E.curve t) h)) = SignType.sign (det r (edge E.center h)) := by
    rw [Filter.eventually_all]
    intro h
    have hc : ContinuousAt (fun t : E.Parameter => det r (edge (E.curve t) h)) E.zeroParameter :=
      (AV_continuous_det E r h).continuousAt
    rcases lt_or_gt_of_ne (hr h) with hneg | hpos
    · have hev : ∀ᶠ t in nhds E.zeroParameter, det r (edge (E.curve t) h) < 0 :=
        hc.eventually_lt continuousAt_const hneg
      exact hev.mono fun t ht => ⟨ht.ne, by rw [sign_neg ht, sign_neg hneg]⟩
    · have hev : ∀ᶠ t in nhds E.zeroParameter, 0 < det r (edge (E.curve t) h) :=
        continuousAt_const.eventually_lt hc hpos
      exact hev.mono fun t ht => ⟨ht.ne', by rw [sign_pos ht, sign_pos hpos]⟩
  obtain ⟨δ₃, hδ₃, -, h3'⟩ := (E.eventually_center_iff_radius _).mp hray
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), (min_le_left _ _).trans hδ₁r, ?_⟩
  have hm1 : ∀ t : E.Parameter, Punctured E (min δ₁ (min δ₂ δ₃)) t → |t.val| < δ₁ :=
    fun t ht => lt_of_lt_of_le ht.2 (min_le_left _ _)
  have hm2 : ∀ t : E.Parameter, Punctured E (min δ₁ (min δ₂ δ₃)) t → |t.val| < δ₂ :=
    fun t ht => lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 : ∀ t : E.Parameter, Punctured E (min δ₁ (min δ₂ δ₃)) t → |t.val| < δ₃ :=
    fun t ht => lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨?_, ?_, ⟨r, fun t ht h => h3' t (hm3 t ht) h⟩⟩
  · intro t t' ht ht' i
    rw [AV_turn_eq_sign_G1, AV_turn_eq_sign_G1, h1 t (hm1 t ht) i, h1 t' (hm1 t' ht') i]
  · intro t t' ht ht' i j hij
    have hw : ∃ t₁ : E.Parameter, t₁.val ≠ 0 ∧ IsCrossing (E.curve t₁) {i, j} := ⟨t, ht.1, hij⟩
    show SignType.sign (CV.G5 (E.curve t') i j) = SignType.sign (CV.G5 (E.curve t) i j)
    rw [h2 t (hm2 t ht) (i, j) hw, h2 t' (hm2 t' ht') (i, j) hw]

/-! ### The wall data of an availability-`≤ 1` fibre -/

omit [NeZero n] in
theorem AV_card_triple {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ({e, f, g} : Finset (ZMod n)).card = 3 :=
  Finset.card_eq_three.mpr ⟨e, f, g, hef, heg, hfg, rfl⟩

omit [NeZero n] in
/-- A two-element subset of `{e, f, g}` is one of the three triangle supports. -/
theorem AV_pair_mem_triangleSupports {e f g a b : ZMod n}
    (ha : a ∈ ({e, f, g} : Finset (ZMod n))) (hb : b ∈ ({e, f, g} : Finset (ZMod n))) (hab : a ≠ b) :
    ({a, b} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  unfold triangleSupports
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | simp [Finset.pair_comm]

omit [NeZero n] in
/-- Two same-edge visits whose supports cover the triangle are visits of two distinct triangle
crossings (the reversed pairs of R-LOC-2 (2)). -/
theorem AV_triangle_of_union {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (v w : Visit P) (hu : v.1.val ∪ w.1.val = {e, f, g}) :
    v.1.val ∈ triangleSupports e f g ∧ w.1.val ∈ triangleSupports e f g ∧ v.1 ≠ w.1 := by
  have h3 := AV_card_triple hef heg hfg
  have hpair : ∀ u : Visit P, u.1.val ⊆ ({e, f, g} : Finset (ZMod n)) →
      u.1.val ∈ triangleSupports e f g := by
    intro u hsub
    have hne : u.2.val ≠ (visitTwin u).2.val := by
      intro heq
      have hc := crossing_card_two u.1
      rw [visit_crossing_val_eq_pair u, ← heq, Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
        Finset.card_singleton] at hc
      exact absurd hc (by norm_num)
    rw [visit_crossing_val_eq_pair u] at hsub ⊢
    exact AV_pair_mem_triangleSupports (hsub (Finset.mem_insert_self _ _))
      (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) hne
  refine ⟨hpair v (hu ▸ Finset.subset_union_left), hpair w (hu ▸ Finset.subset_union_right), ?_⟩
  intro hvw
  have hc := congrArg Finset.card hu
  rw [hvw, Finset.union_self, crossing_card_two, h3] at hc
  exact absurd hc (by norm_num)

/-- The visit-key clause of the wall data from R-LOC-2's `ExactTriangleVisitOrders`. -/
theorem AV_key_lt_of_gauss (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) (hX : ExactTriangleVisitOrders P P' e f g hs)
    (v w : Visit P)
    (hvw : ¬ (v.1 ∈ triangleCrossings P e f g ∧ w.1 ∈ triangleCrossings P e f g ∧ v.1 ≠ w.1 ∧
      v.2.val = w.2.val)) :
    geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hP' (visitTransport hs v) < geometricVisitKey hP' (visitTransport hs w) := by
  unfold geometricVisitKey
  rw [traversalKey_lt_iff, traversalKey_lt_iff]
  change (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧ visitParameter v < visitParameter w) ↔
    (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧
      visitParameter (visitTransport hs v) < visitParameter (visitTransport hs w))
  refine or_congr Iff.rfl (and_congr_right fun he => ?_)
  refine (hX v w he).2 fun hu => hvw ?_
  obtain ⟨hv, hw, hne⟩ := AV_triangle_of_union hef heg hfg v w hu
  exact ⟨(F1.mem_triangleCrossings e f g v.1).mpr hv, (F1.mem_triangleCrossings e f g w.1).mpr hw,
    hne, he⟩

theorem AV_fibrePartitionData_mono {E : CV.Event n} {e f g : ZMod n} {δ δ' : ℝ} (h : δ' ≤ δ)
    (hF : FibrePartitionData E e f g δ) : FibrePartitionData E e f g δ' where
  graph_on_W_same t t' ht ht' :=
    hF.graph_on_W_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  W_to_T_same t t' ht ht' := hF.W_to_T_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  avail_same t t' ht ht' := hF.avail_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  decompose t ht := hF.decompose t (F1.punctured_mono h ht)
  compose t ht := hF.compose t (F1.punctured_mono h ht)
  bijection t ht := hF.bijection t (F1.punctured_mono h ht)
  state_sum_partition t ht := hF.state_sum_partition t (F1.punctured_mono h ht)
  avail_card t ht := hF.avail_card t (F1.punctured_mono h ht)

/-- **The wall data of a fibre of availability `≤ 1`**: `Q ∪ J` independent (`F1.compose_geom`);
visit orders from R-LOC-2 (2)–(3) (`gauss_words`); interlacement off `T × T` from R-LOC-2 (4)
(`interlace_toggle`); of two distinct triangle crossings at most one is available, so the other
interlaces a member of `Q` (`mem_avail`), which is outside `T`; turns, signs and the ray from the
event radius. -/
theorem AV_wall_of_event {E : CV.Event n} {e f g : ZMod n} {δ : ℝ} (hL : LocalizationData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hcard : (avail (geomAt E t ht.1) e f g Q).card ≤ 1)
    {J : Finset (Crossing (E.curve t))} (hJ : J ∈ localFibre (geomAt E t ht.1) e f g Q) :
    AV_Wall (geomAt E t ht.1) (geomAt E t' ht'.1) hs (triangleCrossings (E.curve t) e f g) (Q ∪ J) where
  indep := by
    have hJ' := (F1.mem_localFibre _ e f g Q J).mp hJ
    exact (CV.mem_Ind_iff_geoIndependent _ _).mp (F1.compose_geom _ e f g Q J hQ hJ'.1 hJ'.2)
  key_lt := AV_key_lt_of_gauss _ _ hs hef heg hfg (hL.gauss_words t t' ht ht' hop hs)
  interlaces_iff x y hxy := by
    have h := hL.interlace_toggle t t' ht ht' hop hs x y
    rw [L.xor_iff_of_not_right (by
      rintro ⟨-, hx, hy⟩
      exact hxy ⟨(F1.mem_triangleCrossings e f g x).mpr hx,
        (F1.mem_triangleCrossings e f g y).mpr hy⟩)] at h
    exact h.symm
  dominated x hx y hy hxy := by
    have hQT : Disjoint Q (triangleCrossings (E.curve t) e f g) :=
      ((F1.mem_outsideSupports _ e f g Q).mp hQ).2
    have hdom : ∀ z ∈ triangleCrossings (E.curve t) e f g, z ∉ avail (geomAt E t ht.1) e f g Q →
        AV_Dom (geomAt E t ht.1) (triangleCrossings (E.curve t) e f g) (Q ∪ J) z := by
      intro z hz hza
      rw [F1.mem_avail] at hza
      have hzT := (F1.mem_triangleCrossings e f g z).mp hz
      obtain ⟨q, hq, hqz⟩ : ∃ q ∈ Q, GeometricInterlaces (geomAt E t ht.1) q z := by
        by_contra hcon
        exact hza ⟨hzT, fun q hq hqz => hcon ⟨q, hq, hqz⟩⟩
      exact ⟨q, Finset.mem_union_left J hq, Finset.disjoint_left.mp hQT hq,
        geometricInterlaces_symm _ hqz⟩
    by_cases hxa : x ∈ avail (geomAt E t ht.1) e f g Q
    · right
      apply hdom y hy
      intro hya
      exact hxy (Finset.card_le_one.mp hcard x hxa y hya)
    · exact Or.inl (hdom x hx hxa)
  turn_eq := hR.turn_eq t t' ht ht'
  sign_eq := hR.sign_eq t t' ht ht'
  ray := by
    obtain ⟨r, hr⟩ := hR.ray
    refine ⟨r, fun h => ⟨(hr t ht h).1, ?_⟩⟩
    rw [(hr t' ht' h).2, (hr t ht h).2]

end AV

/-! ### Unit AV — the X₁ fields of row 170 (`summand_transport`, `summands_agree`,
`fibre_identity`), each with exactly the field's type -/

/-- A `SummandTransport` gives the equality of the two present rows: `wind` agrees and the product of
the `Ω₁` is reindexed along the carrier bijection. -/
theorem AV_rowTerm_eq_of_summandTransport (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P)
    (hG' : CV.Generic P') {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (h : SummandTransport hn hG hG' hS hS') : rowTerm hn hG S = rowTerm hn hG' S' := by
  rw [rowTerm_of_mem_Ind hn hG hS, rowTerm_of_mem_Ind hn hG' hS']
  obtain ⟨hwind, τ, hτ⟩ := h
  rw [hwind]
  congr 1
  exact Fintype.prod_equiv τ _ _ fun q => ((hτ q).2.2.2.2).symm

/-- **The summand transport from wall data**: the carrier bijection `AV_carrierEquiv` with `wt`,
`R(L)`, `w_{S,L}`, `P_{S,L}` and `Ω₁(S,L)` carried. -/
theorem AV_summandTransport (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry) :
    SummandTransport hn hG hG' hS hS' :=
  ⟨AV_wind_eq hn hG hG' W, AV_carrierEquiv W, fun q =>
    ⟨AV_weight_eq hn hG hG' W q, AV_carrierR_eq hn hG hG' W hS hS' q, AV_groupedWrithe_eq hG hG' W hS hS' q,
      AV_groupedPoly_eq hn hG hG' W hS hS' q, AV_Omega1_eq hn hG hG' W hS hS' q⟩⟩

/-- Field `summand_transport` of `AvailabilityZeroOneData`. -/
theorem AV_170_summand_transport (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
      ∀ (hS : Q ∪ J ∈ CV.Ind (geomAt E t ht.1))
        (hS' : transportSupport hs (Q ∪ J) ∈ CV.Ind (geomAt E t' ht'.1)),
        SummandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' := by
  intro t t' ht ht' hop hs Q hQ hcard J hJ hS hS'
  exact AV_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1)
    (AV_wall_of_event hL hR hef heg hfg ht ht' hop hs hQ (by omega) hJ) hS hS'

/-- Field `summands_agree` of `AvailabilityZeroOneData`: the row is present on both sides
(`F1.compose_geom`; independence is carried by the wall data) and the summand transport gives the
equality. -/
theorem AV_170_summands_agree (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
        rowTerm hn (genericAt E t ht.1) (Q ∪ J) =
          rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ J)) := by
  intro t t' ht ht' hop hs Q hQ hcard J hJ
  have W := AV_wall_of_event hL hR hef heg hfg ht ht' hop hs hQ (by omega) hJ
  have hS : Q ∪ J ∈ CV.Ind (geomAt E t ht.1) := (CV.mem_Ind_iff_geoIndependent _ _).mpr W.indep
  have hS' : transportSupport hs (Q ∪ J) ∈ CV.Ind (geomAt E t' ht'.1) :=
    (CV.mem_Ind_iff_geoIndependent _ _).mpr W.indep'
  exact AV_rowTerm_eq_of_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS'
    (AV_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS')

/-- Field `fibre_identity` of `AvailabilityZeroOneData`: the far fibre is the image of the near
fibre (`PRE_170_fibre_correspond`), and the summands agree term by term. -/
theorem AV_170_fibre_identity (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hF : FibrePartitionData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  intro t t' ht ht' hop hs Q hQ hcard
  have hfib := PRE_170_fibre_correspond hF t t' ht ht' hop hs Q hQ hcard
  unfold fibreTerm fibreSum
  rw [hfib, Finset.sum_map]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [supportEmb_apply, ← AV_transportSupport_union]
  exact AV_170_summands_agree hn hL hR hef heg hfg t t' ht ht' hop hs Q hQ hcard J hJ

omit [NeZero n] in
theorem AV_ne_of_remote {i j : ZMod n} (h : remote i j) : i ≠ j := by
  intro hij
  exact h (Or.inr (Or.inl (by rw [hij, sub_self])))

/-- **Row 170, R:availability_0_1**. -/
theorem availability_zero_one (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AvailabilityZeroOneData hn E e f g δ := by
  -- Unit AV: the common radius of rows 164 (`localization`), 171 (`fibre_partition`) and the sign
  -- data `AV_exists_eventRadius`; the three presupposition fields from unit PRE, the three X₁ fields
  -- from the wall transport.
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δF, hδF, -, hF⟩ := fibre_partition E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δF δR), lt_min hδL (lt_min hδF hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δF δR)) hL
  have hF' := AV_fibrePartitionData_mono ((min_le_right δL (min δF δR)).trans (min_le_left δF δR)) hF
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δF δR)).trans (min_le_right δF δR)) hR
  exact {
    fibre_zero := PRE_170_fibre_zero E e f g _
    fibre_one := PRE_170_fibre_one E e f g _
    fibre_correspond := PRE_170_fibre_correspond hF'
    summand_transport := AV_170_summand_transport hn hL' hR' hef heg hfg
    summands_agree := AV_170_summands_agree hn hL' hR' hef heg hfg
    fibre_identity := AV_170_fibre_identity hn hL' hF' hR' hef heg hfg }

end RProof
