import SM.FlatCarriers
import SM.GeometricRecords
import SM.GeoCarriersLemma
import SM.GeoPositiveLift

/-! # SM/GeoMarkTransport.lean — mark transports on the geometric carrier lane (CV-DOM unit U5a, part 1)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1–R5, §5 row **U5a**). Draft; intended home
`work/lean/SM/GeoMarkTransport.lean` (library module, namespace `SM.GeoCarrier`, `open Carrier Link`,
CV-free). Nothing under work/lean was written.

## What this module is

The re-binding of the *combinatorial* half of the accepted prop:C-chamber module (SM/CChamber.lean §1,
`Carrier.MarkTransport` between two `SM.Generic` polygons) to two polygons on the accepted geometric
record domain (`CrossingGeometry`, tier 0) whose geometric records agree. On the geo lane the
identification of marks is *canonical* — vertices by their labels, visits through the accepted
`visitTransport hs` (`SM.markTransport hs`, SM/FlatCarriersDefs.lean §4) — so a transport is a `Prop`:

* `GeoMarkTransport hP hQ hs` : the sorted marked circle is carried mark by mark (`marks`),
  interlacement is carried (`interlaces_iff`), crossing signs agree (`sign_eq`). Constructors:
  `ofOrderAgrees` (same-edge parameter order, the local data of `geometric_records_persist`),
  `of_gaussList` (the Gauss-list clause of `GeometricRecordsAgree`), `of_recordsAgree`
  (`GeometricRecordsAgree hP hQ`, the accepted record agreement of SM/GeometricRecords.lean).

* Transports, all reusing the accepted geo transport of SM/FlatCarriers.lean §"Side ↔ centre"
  (`geoMarkSuccessor_markTransport`, `geoSmoothingSuccessor_markTransport`, `geoOwner_markTransport_iff`,
  `geoComponentMarkList_markTransport`, `geoComponentCornerList_markTransport`,
  `geoCornerCount_markTransport`), never redoing them: the carrier bijection `τ.component S`
  (`Quotient.congr`), `geoOwner`, `geoComponentMarkList`, `geoComponentCornerList`, `geoCornerCount`,
  `geoCornerMark`, `geoCarrierCrossings` (and its cardinality), `GeoIndependent`, the corner polygon (read
  at the geometry of `Q` as `τ.transportedCornerPolygon`, a literal carriage since the mark list is carried
  literally — `geoCornerPolygon_transport`), and, given equal vertex turn data, the corner turns
  (`turn_transportedCornerPolygon`), uniformity (`geoCarrierUniform_iff`), the selector / weight
  (`geoCarrierSelector_eq`) and `geoWind` (`geoWind_eq`), the shadow of the positive lift
  (`geoCarrierShadow_eq`).

The *analytic* half (rotation numbers and HOMFLY polynomials along a continuous family) is
SM/GeoPathTransport.lean (part 2), which consumes this module.

## Names (ruling R3)

Namespace `SM.GeoCarrier`; the structure is `GeoMarkTransport`, its lemmas live in the namespace
`GeoMarkTransport` (dot notation `τ.…`). The re-indexing toolkit of SM/CChamber.lean §0 (`recastTuple`
and its invariants) is a row module's and is NOT imported; it is copied here under the names `geoRecast`,
`rotationNumber_geoRecast`, `regular_geoRecast`, `turn_geoRecast`, `turn_geoRecast_cast`,
`forall_turn_geoRecast`, `polyComp_geoRecast`, `cornerSelector_geoRecast`, `geo_zmod_val_cast`,
`geo_zmod_cast_cast`, `geo_getElem_congr` (the last is CS3's `getElem_congr_lists`). No accepted or ported
`geo*` name is re-declared (each name grepped against work/lean before use). -/

namespace SM.GeoCarrier

open Carrier Link

/-! ## 0. Re-indexing a labelled tuple along an equality of sizes (copy of SM/CChamber.lean §0) -/

/-- A labelled `k`-tuple read as a labelled `k'`-tuple along `hk : k' = k` (the accepted row module's
`recastTuple`, copied). All invariants below are proved by `subst hk`. -/
def geoRecast {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) : LabelledTuple k' :=
  fun j => f (Equiv.cast (congrArg ZMod hk) j)

theorem geoRecast_rfl {k : ℕ} (f : LabelledTuple k) : geoRecast rfl f = f := rfl

theorem geoRecast_apply {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (j : ZMod k') :
    geoRecast hk f j = f (Equiv.cast (congrArg ZMod hk) j) := rfl

/-- The value of a `ZMod` element is unchanged by a cast along an equality of sizes. -/
theorem geo_zmod_val_cast {k k' : ℕ} (h : k = k') (j : ZMod k) :
    (Equiv.cast (congrArg ZMod h) j).val = j.val := by
  subst h; rfl

/-- Casting forth and back along an equality of sizes is the identity. -/
theorem geo_zmod_cast_cast {k k' : ℕ} (h : k' = k) (j : ZMod k') :
    Equiv.cast (congrArg ZMod h.symm) (Equiv.cast (congrArg ZMod h) j) = j := by
  subst h; rfl

theorem geo_zmod_cast_cast' {k k' : ℕ} (h : k' = k) (j : ZMod k) :
    Equiv.cast (congrArg ZMod h) (Equiv.cast (congrArg ZMod h.symm) j) = j := by
  subst h; rfl

theorem rotationNumber_geoRecast {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k)
    (f : LabelledTuple k) : rotationNumber (geoRecast hk f) = rotationNumber f := by
  subst hk; rfl

theorem regular_geoRecast {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) :
    Regular (geoRecast hk f) ↔ Regular f := by
  subst hk; rfl

theorem turn_geoRecast {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (j : ZMod k') :
    turn (geoRecast hk f) j = turn f (Equiv.cast (congrArg ZMod hk) j) := by
  subst hk; rfl

theorem turn_geoRecast_cast {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (j : ZMod k) :
    turn (geoRecast hk f) (Equiv.cast (congrArg ZMod hk.symm) j) = turn f j := by
  subst hk; rfl

theorem forall_turn_geoRecast {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (σ : SignType) :
    (∀ j, turn (geoRecast hk f) j = σ) ↔ ∀ j, turn f j = σ := by
  subst hk; rfl

/-- The one-component shadow data is unchanged by a recast. -/
theorem polyComp_geoRecast {k k' : ℕ} (hk : k' = k) (h : 3 ≤ k) (h' : 3 ≤ k')
    (f : LabelledTuple k) : (PolyComp.mk k' h' (geoRecast hk f)) = PolyComp.mk k h f := by
  subst hk; rfl

/-- The selector of def:flat-carriers is unchanged by a recast. -/
theorem cornerSelector_geoRecast {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k)
    (f : LabelledTuple k) : cornerSelector (geoRecast hk f) = cornerSelector f := by
  subst hk; rfl

/-- The selector depends only on the turn sequence. -/
theorem cornerSelector_congr_turn {k : ℕ} [NeZero k] {f g : LabelledTuple k}
    (h : ∀ j, turn f j = turn g j) : cornerSelector f = cornerSelector g := by
  unfold cornerSelector
  simp only [h]

/-- Reading an entry of a list along an equality of lists and of indices (CS3's `getElem_congr_lists`,
copied). -/
theorem geo_getElem_congr {α : Type*} (L L' : List α) (h : L = L') (i i' : ℕ)
    (hi : i < L.length) (hi' : i' < L'.length) (hii : i = i') : L[i]'hi = L'[i']'hi' := by
  subst h; subst hii; rfl

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n}

/-! ## 1. The mark transport predicate and its constructors -/

/-- A *mark transport* from `P` to `Q` (both on the geometric record domain, with the same crossing
supports `hs`) along the canonical identification `markTransport hs` of marks (vertices by label, visits
through `visitTransport hs`): the sorted marked circle of `P` is carried mark by mark onto that of `Q`
(hence `geoMarkSuccessor` and every `geoSmoothingSuccessor` commute with the identification),
interlacement is carried, and crossing signs agree. The geo-lane form of the accepted
`Carrier.MarkTransport` (SM/CChamber.lean §1): there the vertex relabelling and the crossing bijection are
data and the mark list is carried up to rotation; here both are canonical and the list is carried
literally, so the transport is a proposition. Vertex turn data are NOT part of the predicate (they are
tier 2, `WeakGeneric`); the lemmas that need them take `hturn : ∀ i, turn Q i = turn P i`. -/
structure GeoMarkTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) : Prop where
  /-- the sorted marked circle is carried mark by mark -/
  marks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ
  /-- interlacement is carried -/
  interlaces_iff : ∀ x y, GeometricInterlaces hP x y ↔
    GeometricInterlaces hQ (crossingTransport hs x) (crossingTransport hs y)
  /-- crossing signs agree -/
  sign_eq : ∀ i j, IsCrossing P {i, j} → crossingSign Q i j = crossingSign P i j

/-- **Constructor from the local data of `geometric_records_persist`**: same crossing supports, same
same-edge parameter order (`CrossingParameterOrderAgrees`), same crossing signs. The marks are carried by
the accepted `geoMarkList_map_transport`, interlacement by the accepted `geometric_interlaces_transport`. -/
theorem GeoMarkTransport.ofOrderAgrees (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q)
    (hsign : ∀ i j, IsCrossing P {i, j} → crossingSign Q i j = crossingSign P i j) :
    GeoMarkTransport hP hQ hs where
  marks := geoMarkList_map_transport hP hQ hs ho
  interlaces_iff := geometric_interlaces_transport hP hQ hs ho
  sign_eq := hsign

/-! ### 1a. From the Gauss-list clause of `GeometricRecordsAgree` to the marked circle -/

/-- Two lists strictly sorted by injective real keys and related by a map have the same key order on
their members. -/
theorem lt_iff_of_sorted_map_eq {α β : Type*} {f : α → ℝ} {g : β → ℝ} {l : List α}
    {l' : List β} (e : α → β) (hl : l.Pairwise (fun a b => f a < f b))
    (hl' : l'.Pairwise (fun a b => g a < g b)) (h : l.map e = l') {a b : α} (ha : a ∈ l)
    (hb : b ∈ l) : f a < f b ↔ g (e a) < g (e b) := by
  subst h
  rw [List.pairwise_map] at hl'
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact iff_of_true (List.pairwise_iff_getElem.mp hl i j hi hj hij)
      (List.pairwise_iff_getElem.mp hl' i j hi hj hij)
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · exact iff_of_false (lt_asymm (List.pairwise_iff_getElem.mp hl j i hj hi hji))
      (lt_asymm (List.pairwise_iff_getElem.mp hl' j i hj hi hji))

/-- A list sorted (`≤`) by an injective key and without duplicates is strictly sorted. -/
theorem pairwise_lt_of_pairwise_le_nodup {α : Type*} {f : α → ℝ} {l : List α}
    (hl : l.Pairwise (fun a b => f a ≤ f b)) (hnd : l.Nodup) (hf : Function.Injective f) :
    l.Pairwise (fun a b => f a < f b) :=
  (hl.and hnd).imp fun ⟨hle, hne⟩ => lt_of_le_of_ne hle fun h => hne (hf h)

/-- The Gauss lists of `P` and `Q` are strictly sorted by the visit keys. -/
theorem geometricGaussList_pairwise_lt (hP : CrossingGeometry P) :
    (geometricGaussList hP).Pairwise
      (fun v w => geometricVisitKey hP v < geometricVisitKey hP w) :=
  pairwise_lt_of_pairwise_le_nodup (geometricGaussList_sorted hP) (geometricGaussList_nodup hP)
    (geometricVisitKey_injective hP)

/-- The Gauss-list clause carries the visit key order. -/
theorem geometricVisitKey_lt_of_gaussList (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hg : (geometricGaussList hP).map (visitTransport hs) = geometricGaussList hQ) (v w : Visit P) :
    geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hQ (visitTransport hs v) < geometricVisitKey hQ (visitTransport hs w) :=
  lt_iff_of_sorted_map_eq (visitTransport hs) (geometricGaussList_pairwise_lt hP)
    (geometricGaussList_pairwise_lt hQ) hg (mem_geometricGaussList hP v)
    (mem_geometricGaussList hP w)

/-- The mark order is determined by the visit-key order (vertex/vertex by label, vertex/visit by label
and strict interiority of the visit parameter — the accepted `geoMarkKey_lt_transport` word for word,
with the visit/visit clause taken as a hypothesis instead of derived from `CrossingParameterOrderAgrees`). -/
theorem geoMarkKey_lt_transport_of_visitKey (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hv : ∀ v w : Visit P, geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hQ (visitTransport hs v) < geometricVisitKey hQ (visitTransport hs w))
    (a b : Mark P) :
    geoMarkKey hP a < geoMarkKey hP b ↔
      geoMarkKey hQ (markTransport hs a) < geoMarkKey hQ (markTransport hs b) := by
  cases a with
  | inl i =>
    cases b with
    | inl k => exact Iff.rfl
    | inr v =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hQ (visitTransport hs v).1
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
      have h2 := (crossingParameter_interior_of_geometry hQ (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter v < (0 : ℝ)) ↔
        (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter (visitTransport hs v) < (0 : ℝ))
      exact or_congr Iff.rfl (and_congr Iff.rfl
        ⟨fun h => (lt_asymm h1 h).elim, fun h => (lt_asymm h2 h).elim⟩)
    | inr w => exact hv v w

/-- The sorted marked circle is carried mark by mark once the visit-key order is
(the accepted `geoMarkList_map_transport`'s proof with `geoMarkKey_lt_transport_of_visitKey`). -/
theorem geoMarkList_map_transport_of_visitKey (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hv : ∀ v w : Visit P, geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hQ (visitTransport hs v) < geometricVisitKey hQ (visitTransport hs w)) :
    (geoMarkList hP).map (markTransport hs) = geoMarkList hQ := by
  apply List.Perm.eq_of_pairwise
    (fun x y _ _ hxy hyx => geoMarkKey_injective hQ (le_antisymm hxy hyx))
    _ (geoMarkList_sorted hQ) (geoMarkList_transport_perm hP hQ hs)
  apply List.pairwise_map.mpr
  apply (geoMarkList_sorted hP).imp
  intro a b h
  rw [← not_lt] at h ⊢
  exact fun h' => h ((geoMarkKey_lt_transport_of_visitKey hP hQ hs hv b a).mpr h')

/-- **Constructor from the clauses of `GeometricRecordsAgree`** (Gauss list carried, interlacement
carried, signs equal): the marked circle is carried by `geoMarkList_map_transport_of_visitKey`. -/
theorem GeoMarkTransport.of_gaussList (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hg : (geometricGaussList hP).map (visitTransport hs) = geometricGaussList hQ)
    (hI : ∀ x y, GeometricInterlaces hP x y ↔
      GeometricInterlaces hQ (crossingTransport hs x) (crossingTransport hs y))
    (hsign : ∀ i j, IsCrossing P {i, j} → crossingSign Q i j = crossingSign P i j) :
    GeoMarkTransport hP hQ hs where
  marks := geoMarkList_map_transport_of_visitKey hP hQ hs
    (geometricVisitKey_lt_of_gaussList hP hQ hs hg)
  interlaces_iff := hI
  sign_eq := hsign

/-- **Constructor from the accepted record agreement** (`GeometricRecordsAgree`, SM/GeometricRecords.lean):
the witness `hs` of the agreement carries a mark transport. -/
theorem GeoMarkTransport.of_recordsAgree {hP : CrossingGeometry P} {hQ : CrossingGeometry Q}
    (h : GeometricRecordsAgree hP hQ) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s, GeoMarkTransport hP hQ hs := by
  obtain ⟨hs, hg, -, hI, hsign⟩ := h
  exact ⟨hs, GeoMarkTransport.of_gaussList hP hQ hs hg hI hsign⟩

/-- Any two crossing-support identifications of `P` and `Q` are the same function (proof irrelevance):
a mark transport along one is a mark transport along the other. -/
theorem GeoMarkTransport.congr_hs {hP : CrossingGeometry P} {hQ : CrossingGeometry Q}
    {hs hs' : ∀ s, IsCrossing P s ↔ IsCrossing Q s} (τ : GeoMarkTransport hP hQ hs) :
    GeoMarkTransport hP hQ hs' := by
  have : hs = hs' := Subsingleton.elim _ _
  subst this
  exact τ

/-- The crossing supports of two polygons with agreeing records coincide (the witness clause of
`GeometricRecordsAgree`; any such proof is as good as any other, `Subsingleton`). -/
theorem recordsAgree_crossing_iff {hP : CrossingGeometry P} {hQ : CrossingGeometry Q}
    (h : GeometricRecordsAgree hP hQ) : ∀ s, IsCrossing P s ↔ IsCrossing Q s := by
  obtain ⟨hs, -⟩ := h
  exact hs

/-- The mark transport of a record agreement, along its crossing-support identification. -/
theorem geoTransport_of_recordsAgree {hP : CrossingGeometry P} {hQ : CrossingGeometry Q}
    (h : GeometricRecordsAgree hP hQ) : GeoMarkTransport hP hQ (recordsAgree_crossing_iff h) := by
  obtain ⟨hs, τ⟩ := GeoMarkTransport.of_recordsAgree h
  exact τ.congr_hs

/-! ## 2. Transport of the carrier data -/

namespace GeoMarkTransport

variable {hP : CrossingGeometry P} {hQ : CrossingGeometry Q}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s} (τ : GeoMarkTransport hP hQ hs)

/-! ### 2a. Marks, successors, supports -/

include τ in
theorem geoMarkSuccessor_eq (a : Mark P) :
    geoMarkSuccessor hQ (markTransport hs a) = markTransport hs (geoMarkSuccessor hP a) :=
  geoMarkSuccessor_markTransport hP hQ hs τ.marks a

include τ in
theorem geoSmoothingSuccessor_eq (S : Finset (Crossing P)) (a : Mark P) :
    geoSmoothingSuccessor hQ (transportSupport hs S) (markTransport hs a) =
      markTransport hs (geoSmoothingSuccessor hP S a) :=
  geoSmoothingSuccessor_markTransport hP hQ hs τ.marks S a

include τ in
/-- Two marks lie on one carrier iff their images do. -/
theorem geoOwner_iff (S : Finset (Crossing P)) (a a' : Mark P) :
    geoOwner hP S a = geoOwner hP S a' ↔
      geoOwner hQ (transportSupport hs S) (markTransport hs a) =
        geoOwner hQ (transportSupport hs S) (markTransport hs a') :=
  geoOwner_markTransport_iff hP hQ hs τ.marks S a a'

omit [NeZero n] in
theorem mem_support (S : Finset (Crossing P)) (x : Crossing P) :
    crossingTransport hs x ∈ transportSupport hs S ↔ x ∈ S :=
  mem_transportSupport_iff hs S x

omit [NeZero n] in
theorem support_card (S : Finset (Crossing P)) : (transportSupport hs S).card = S.card :=
  Finset.card_map _

omit [NeZero n] in
theorem support_injective : Function.Injective (transportSupport hs) := fun _ _ h =>
  Finset.map_injective (crossingTransport hs).toEmbedding h

omit [NeZero n] in
theorem support_surjective (S' : Finset (Crossing Q)) : ∃ S, transportSupport hs S = S' :=
  ⟨S'.map (crossingTransport hs).symm.toEmbedding, by
    simp [transportSupport, Finset.map_map]⟩

omit [NeZero n] in
theorem support_bijective : Function.Bijective (transportSupport hs) :=
  ⟨support_injective, fun S' => support_surjective S'⟩

omit [NeZero n] in
/-- The support bijection as an equivalence of the finite sets of supports. -/
noncomputable def supportEquiv (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) :
    Finset (Crossing P) ≃ Finset (Crossing Q) :=
  Equiv.ofBijective (transportSupport hs) support_bijective

omit [NeZero n] in
theorem supportEquiv_apply (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (S : Finset (Crossing P)) :
    supportEquiv hs S = transportSupport hs S := rfl

/-- The canonical identification is an isomorphism of interlacement graphs (the accepted
`geometricInterlacementTransportIso`, on the transport's interlacement clause). -/
def interlacementIso (τ : GeoMarkTransport hP hQ hs) :
    geometricInterlacementGraph hP ≃g geometricInterlacementGraph hQ where
  toEquiv := crossingTransport hs
  map_rel_iff' := (τ.interlaces_iff _ _).symm

theorem interlacementIso_apply (x : Crossing P) : τ.interlacementIso x = crossingTransport hs x := rfl

include τ in
/-- Independence is carried (`geoIndependent_map_iff` with the interlacement clause). -/
theorem geoIndependent_iff (S : Finset (Crossing P)) :
    GeoIndependent hQ (transportSupport hs S) ↔ GeoIndependent hP S :=
  (geoIndependent_map_iff hP hQ (crossingTransport hs) τ.interlaces_iff S).symm

/-! ### 2b. Carriers -/

/-- The carriers of `S` correspond to the carriers of the transported support (the accepted
`MarkTransport.component`, on the canonical identification). -/
noncomputable def component (S : Finset (Crossing P)) :
    GeoComponent hP S ≃ GeoComponent hQ (transportSupport hs S) :=
  Quotient.congr (markTransport hs) fun a b =>
    (sameCycle_of_equiv_conj (geoSmoothingSuccessor hP S)
      (geoSmoothingSuccessor hQ (transportSupport hs S)) (markTransport hs)
      (τ.geoSmoothingSuccessor_eq S) a b).symm

theorem component_owner (S : Finset (Crossing P)) (a : Mark P) :
    τ.component S (geoOwner hP S a) = geoOwner hQ (transportSupport hs S) (markTransport hs a) := rfl

theorem owner_transport (S : Finset (Crossing P)) (a : Mark P) :
    geoOwner hQ (transportSupport hs S) (markTransport hs a) = τ.component S (geoOwner hP S a) := rfl

theorem component_symm_owner (S : Finset (Crossing P)) (b : Mark Q) :
    (τ.component S).symm (geoOwner hQ (transportSupport hs S) b) =
      geoOwner hP S ((markTransport hs).symm b) := by
  obtain ⟨a, rfl⟩ := (markTransport hs).surjective b
  rw [Equiv.symm_apply_apply, τ.owner_transport, Equiv.symm_apply_apply]

/-- The marks of a carrier transport, in inherited order, to the marks of its copy. -/
theorem geoComponentMarkList_eq (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    (geoComponentMarkList hP S q).map (markTransport hs) =
      geoComponentMarkList hQ (transportSupport hs S) (τ.component S q) := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP S q
  exact geoComponentMarkList_markTransport hP hQ hs τ.marks S a

/-- The corners of a carrier transport, in inherited order, to the corners of its copy. -/
theorem geoComponentCornerList_eq (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    (geoComponentCornerList hP S q).map (markTransport hs) =
      geoComponentCornerList hQ (transportSupport hs S) (τ.component S q) := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP S q
  exact geoComponentCornerList_markTransport hP hQ hs τ.marks S a

theorem geoCornerCount_eq (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCornerCount hQ (transportSupport hs S) (τ.component S q) = geoCornerCount hP S q := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP S q
  exact (geoCornerCount_markTransport hP hQ hs τ.marks S a).symm

/-- The `k`-th corner mark of a carrier is carried to the corner mark of its copy at the cast index
(the accepted row module's `geoCornerMark_markTransport`, on the canonical identification). -/
theorem geoCornerMark_eq (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hQ (transportSupport hs S) (τ.component S q)
        (Equiv.cast (congrArg ZMod (τ.geoCornerCount_eq S q).symm) k) =
      markTransport hs (geoCornerMark hP S q k) := by
  have hL := τ.geoComponentCornerList_eq S q
  have hlen : k.val < (geoComponentCornerList hQ (transportSupport hs S) (τ.component S q)).length := by
    rw [← hL, List.length_map]; exact ZMod.val_lt k
  have h3 : k.val < ((geoComponentCornerList hP S q).map (markTransport hs)).length := by
    rw [List.length_map]; exact ZMod.val_lt k
  unfold geoCornerMark
  refine (geo_getElem_congr _ _ rfl _ _ _ hlen (geo_zmod_val_cast (τ.geoCornerCount_eq S q).symm k)).trans ?_
  refine (geo_getElem_congr _ _ hL.symm _ _ hlen h3 rfl).trans ?_
  exact List.getElem_map _

/-- The same, with the cast on the other side. -/
theorem geoCornerMark_eq' (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (j : ZMod (geoCornerCount hQ (transportSupport hs S) (τ.component S q))) :
    geoCornerMark hQ (transportSupport hs S) (τ.component S q) j =
      markTransport hs (geoCornerMark hP S q (Equiv.cast (congrArg ZMod (τ.geoCornerCount_eq S q)) j)) := by
  have h := τ.geoCornerMark_eq S q (Equiv.cast (congrArg ZMod (τ.geoCornerCount_eq S q)) j)
  rwa [geo_zmod_cast_cast (τ.geoCornerCount_eq S q) j] at h

/-! ### 2c. Retained crossings -/

/-- The retained crossings of a carrier are carried to those of its copy (the accepted row module's
`geoCarrierCrossings_markTransport`, on the canonical identification). -/
theorem geoCarrierCrossings_eq (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCarrierCrossings hQ (transportSupport hs S) (τ.component S q) =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding := by
  classical
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP S q
  ext x'
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  unfold geoCarrierCrossings
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [mem_transportSupport_iff]
  apply and_congr Iff.rfl
  constructor
  · intro hw v hv
    have hvo := hw (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [τ.component_owner, ← markTransport_visit, ← τ.geoOwner_iff] at hvo
    exact hvo
  · intro hv w hw
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
    rw [visitTransport_crossing] at hw
    have hvo := hv v ((crossingTransport hs).injective hw)
    rw [τ.component_owner, ← markTransport_visit, ← τ.geoOwner_iff]
    exact hvo

theorem card_geoCarrierCrossings_eq (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    (geoCarrierCrossings hQ (transportSupport hs S) (τ.component S q)).card =
      (geoCarrierCrossings hP S q).card := by
  rw [τ.geoCarrierCrossings_eq S q, Finset.card_map]

theorem mem_geoCarrierCrossings_iff (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (x : Crossing P) :
    crossingTransport hs x ∈ geoCarrierCrossings hQ (transportSupport hs S) (τ.component S q) ↔
      x ∈ geoCarrierCrossings hP S q := by
  rw [τ.geoCarrierCrossings_eq S q, Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-! ### 2d. The corner polygon read at the geometry of `Q` -/

/-- The corner polygon of the carrier `q` of `P` read at the geometry of `Q`: the vertex at the corner
mark `c_k` of `q` is the plane point of `Q` at the transported mark (the accepted
`MarkTransport.transportedCornerPolygon`). The transport `τ` is a (proof) argument only so that the
polygon is written `τ.transportedCornerPolygon S q`; the body reads `hQ` and `hs`. -/
noncomputable def transportedCornerPolygon (_τ : GeoMarkTransport hP hQ hs) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : LabelledTuple (geoCornerCount hP S q) :=
  fun k => traversalEvaluation Q (geoMarkPosition hQ (markTransport hs (geoCornerMark hP S q k)))

theorem transportedCornerPolygon_apply (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    τ.transportedCornerPolygon S q k =
      traversalEvaluation Q (geoMarkPosition hQ (markTransport hs (geoCornerMark hP S q k))) := rfl

/-- **The corner polygon of the transported carrier is the transported corner polygon**, re-indexed
along the equal corner counts (a literal carriage: the corner list is carried literally). -/
theorem geoCornerPolygon_eq (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCornerPolygon hQ (transportSupport hs S) (τ.component S q) =
      geoRecast (τ.geoCornerCount_eq S q) (τ.transportedCornerPolygon S q) := by
  funext j
  show traversalEvaluation Q (geoMarkPosition hQ (geoCornerMark hQ (transportSupport hs S)
    (τ.component S q) j)) = _
  rw [τ.geoCornerMark_eq' S q j]
  rfl

/-- The transported corner polygon is the corner polygon of the copy, recast back. -/
theorem transportedCornerPolygon_eq (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    τ.transportedCornerPolygon S q =
      geoRecast (τ.geoCornerCount_eq S q).symm
        (geoCornerPolygon hQ (transportSupport hs S) (τ.component S q)) := by
  rw [τ.geoCornerPolygon_eq S q]
  funext k
  rw [geoRecast_apply, geoRecast_apply, geo_zmod_cast_cast' (τ.geoCornerCount_eq S q) k]

theorem regular_transportedCornerPolygon_iff (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    Regular (τ.transportedCornerPolygon S q) ↔
      Regular (geoCornerPolygon hQ (transportSupport hs S) (τ.component S q)) := by
  rw [τ.geoCornerPolygon_eq S q, regular_geoRecast]

theorem rotationNumber_transportedCornerPolygon (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    rotationNumber (τ.transportedCornerPolygon S q) =
      geoCarrierRotation hQ (transportSupport hs S) (τ.component S q) := by
  unfold geoCarrierRotation
  rw [τ.geoCornerPolygon_eq S q, rotationNumber_geoRecast]

theorem turn_transportedCornerPolygon_eq_turn_cast (S : Finset (Crossing P))
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    turn (τ.transportedCornerPolygon S q) k =
      turn (geoCornerPolygon hQ (transportSupport hs S) (τ.component S q))
        (Equiv.cast (congrArg ZMod (τ.geoCornerCount_eq S q).symm) k) := by
  rw [τ.geoCornerPolygon_eq S q, turn_geoRecast_cast]

/-! ### 2e. Corner turns, uniformity, selector and wind (given equal vertex turn data) -/

/-- **Corner turns are carried** when the vertex turns agree (tier 2 datum `hturn`) — the selected-visit
corners by the sign clause of the transport (`geoCornerPolygon_turn_visit`, U2b), the vertex corners by
`hturn` (`geoCornerPolygon_turn_vertex`, U2b). -/
theorem turn_transportedCornerPolygon (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (τ.transportedCornerPolygon S q) k = turn (geoCornerPolygon hP S q) k := by
  have hS' : GeoIndependent hQ (transportSupport hs S) := (τ.geoIndependent_iff S).mpr hS
  rw [τ.turn_transportedCornerPolygon_eq_turn_cast S q k]
  have hmark := τ.geoCornerMark_eq S q k
  have hcorner := isTrueCorner_geoCornerMark hP S q k
  cases hc : geoCornerMark hP S q k with
  | inl i =>
    rw [hc, markTransport_vertex] at hmark
    rw [geoCornerPolygon_turn_vertex hn hQ hS' _ _ i hmark,
      geoCornerPolygon_turn_vertex hn hP hS q k i hc]
    exact hturn i
  | inr v =>
    rw [hc] at hcorner
    have hv : v.1 ∈ S := (isTrueCorner_visit S v).mp hcorner
    rw [hc, markTransport_visit] at hmark
    have hv' : (visitTransport hs v).1 ∈ transportSupport hs S := by
      rw [visitTransport_crossing, mem_transportSupport_iff]; exact hv
    rw [geoCornerPolygon_turn_visit hn hQ hS' _ _ (visitTransport hs v) hv' hmark,
      geoCornerPolygon_turn_visit hn hP hS q k v hv hc, ← visitTransport_visitTwin,
      visitTransport_edge, visitTransport_edge]
    apply τ.sign_eq
    rw [← visit_crossing_val_eq_pair v]
    exact v.1.property

/-- The turns of the corner polygon of the copy, at the cast indices. -/
theorem turn_geoCornerPolygon_cast (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hQ (transportSupport hs S) (τ.component S q))
        (Equiv.cast (congrArg ZMod (τ.geoCornerCount_eq S q).symm) k) =
      turn (geoCornerPolygon hP S q) k := by
  rw [← τ.turn_transportedCornerPolygon_eq_turn_cast S q k,
    τ.turn_transportedCornerPolygon hn hturn hS q k]

/-- The corner polygon of the copy is the corner polygon of `q` up to a recast, *as a turn sequence*:
every turn agrees at the corresponding index. -/
theorem turn_geoCornerPolygon_eq (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (j : ZMod (geoCornerCount hQ (transportSupport hs S) (τ.component S q))) :
    turn (geoCornerPolygon hQ (transportSupport hs S) (τ.component S q)) j =
      turn (geoCornerPolygon hP S q) (Equiv.cast (congrArg ZMod (τ.geoCornerCount_eq S q)) j) := by
  have h := τ.turn_geoCornerPolygon_cast hn hturn hS q (Equiv.cast (congrArg ZMod (τ.geoCornerCount_eq S q)) j)
  rwa [geo_zmod_cast_cast (τ.geoCornerCount_eq S q) j] at h

/-- Uniformity (def:uniform, `geoCarrierUniform`) is carried. -/
theorem geoCarrierUniform_iff (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    geoCarrierUniform hQ (transportSupport hs S) (τ.component S q) ↔ geoCarrierUniform hP S q := by
  unfold geoCarrierUniform
  rw [τ.geoCornerPolygon_eq S q]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  rw [forall_turn_geoRecast]
  simp only [τ.turn_transportedCornerPolygon hn hturn hS q]

include τ in
/-- Uniformity of every carrier (`geoUniformSupport`) is carried. -/
theorem geoUniformSupport_iff (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    geoUniformSupport hQ (transportSupport hs S) ↔ geoUniformSupport hP S := by
  unfold geoUniformSupport
  rw [(τ.component S).surjective.forall]
  exact forall_congr' fun q => τ.geoCarrierUniform_iff hn hturn hS q

/-- The selector of def:flat-carriers / cor (iii) (`geoCarrierSelector`, = def:wind's weight) is carried. -/
theorem geoCarrierSelector_eq (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    geoCarrierSelector hQ (transportSupport hs S) (τ.component S q) = geoCarrierSelector hP S q := by
  unfold geoCarrierSelector
  rw [τ.geoCornerPolygon_eq S q, cornerSelector_geoRecast]
  exact cornerSelector_congr_turn (τ.turn_transportedCornerPolygon hn hturn hS q)

theorem geoCarrierWeight_eq (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    geoCarrierWeight hQ (transportSupport hs S) (τ.component S q) = geoCarrierWeight hP S q :=
  τ.geoCarrierSelector_eq hn hturn hS q

include τ in
/-- **`geoWind` is carried** (def:wind's `wind(S) = ∏_L wt(L)`, reindexed along `τ.component S`). -/
theorem geoWind_eq (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    geoWind hQ (transportSupport hs S) = geoWind hP S := by
  unfold geoWind
  exact (Fintype.prod_equiv (τ.component S) _ _ fun q => (τ.geoCarrierWeight_eq hn hturn hS q).symm).symm

/-- The number of left turns of the corner polygon is carried. -/
theorem geoCarrierLeftTurns_eq (hn : 3 ≤ n) (hturn : ∀ i, turn Q i = turn P i)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    geoCarrierLeftTurns hQ (transportSupport hs S) (τ.component S q) = geoCarrierLeftTurns hP S q := by
  unfold geoCarrierLeftTurns leftTurns
  symm
  apply Finset.card_equiv (Equiv.cast (congrArg ZMod (τ.geoCornerCount_eq S q).symm))
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [τ.turn_geoCornerPolygon_cast hn hturn hS q k]

end GeoMarkTransport

/-! ### 2f. The carrier shadow of the positive lift (tier 1) -/

namespace GeoMarkTransport

section Tier1

variable (hGP : CarrierGeometry P) (hGQ : CarrierGeometry Q)
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s} (τ : GeoMarkTransport hGP.cg hGQ.cg hs)

/-- The shadow of the positive lift of the copy is the one-component shadow of the transported corner
polygon (`polyComp_geoRecast`). -/
theorem geoCarrierShadow_eq (hn : 3 ≤ n) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S) :
    geoCarrierShadow hn hGQ ((τ.geoIndependent_iff S).mpr hS) (τ.component S q) =
      Shadow.single ⟨geoCornerCount hGP.cg S q, three_le_geoCornerCount hn hGP hS q,
        τ.transportedCornerPolygon S q⟩ := by
  unfold geoCarrierShadow geoCarrierPolyComp
  rw [τ.geoCornerPolygon_eq S q, polyComp_geoRecast _ (three_le_geoCornerCount hn hGP hS q)]

/-- The transported corner polygon is a generic one-component shadow (tier 1 at `Q`). -/
theorem single_generic_transportedCornerPolygon (hn : 3 ≤ n) {S : Finset (Crossing P)}
    (hS : GeoIndependent hGP.cg S) (q : GeoComponent hGP.cg S) :
    (Shadow.single ⟨geoCornerCount hGP.cg S q, three_le_geoCornerCount hn hGP hS q,
      τ.transportedCornerPolygon S q⟩).Generic := by
  rw [← τ.geoCarrierShadow_eq hGP hGQ hn hS q]
  exact geoCarrierShadow_generic hn hGQ _ _

end Tier1

end GeoMarkTransport

end SM.GeoCarrier
