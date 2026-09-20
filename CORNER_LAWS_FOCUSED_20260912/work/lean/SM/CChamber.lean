import SM.CornerStateSum
import SM.Chambers
import SM.ChamberPaths
import SM.CyclicChambers
import SM.CrossingTransport
import SM.GeometricInterlacement
import SM.GeometricCrossingStability
import SM.RotationContinuity
import SM.LinkMoves
import SM.VisitRelabel
import SM.InterlaceRelabel
import SM.SortedCut
import Mathlib.Topology.LocallyConstant.Basic

/-! Ported verbatim 2026-09-13 from work/drafts/cchamber/CChamber_Assembled.lean (assembler subagent of the pod executor merging the six placeholder-free prover units U1a, U1b, U2, U3, U4, U5 of work/drafts/cchamber/ into the judge-merged Skeleton_FINAL.lean; ASSEMBLY_REPORT.md; checked with `lake env lean`, no placeholder, axioms propext/Classical.choice/Quot.sound/SM.lit_homfly); only this header added and `#print axioms` lines removed. Row prop:C-chamber → `SM.prop_C_chamber : CChamberData` (statement verbatim work/drafts/CChamber_statement.lean; design PLAN_FINAL.md). -/


/-! Source prop:C-chamber (reference/SM/sm-4-knotlaws.tex:36-40, frame SM15): chamber constancy of the corner
state sum. Main declaration: `SM.prop_C_chamber`.

Notation (accepted rows def:chamber / prop:chambers, SM/Chambers.lean and SM/ChamberPaths.lean): the space of
generic polygons `𝓤_n / (ℤ/n)` is `GenericPolygon n` (the quotient of `GenericTuple n = {P // Generic P}` by
cyclic relabelling, `polygonProjection`); a chamber is a connected component of it, `chamber (polygonProjection P)`;
"the state sum `C` of def:C" is `cornerStateSum hn hP` (SM/CornerStateSum.lean, accepted row def:C), defined on
labelled generic polygons. "Constant on every chamber": any two generic labelled polygons whose classes lie in one
chamber have the same state sum (in particular `C` is invariant under cyclic relabelling and constant on labelled
chambers).

Assembly provenance (2026-09-13).  Assembled from work/drafts/cchamber/Skeleton_FINAL.lean and the six
prover units U1a, U1b, U2, U3, U4, U5 (work/drafts/cchamber/U*.lean; plan PLAN_FINAL.md, route B with
three grafts from route A); every placeholder of the skeleton is replaced by the owning unit's proof, the
units' helpers are inserted where they placed them, and the one recorded statement fix
(`leftTurns_transport`, PLAN_FINAL.md §5 addendum) is applied.  The route:

Plan: work/drafts/cchamber/PLAN_FINAL.md (route B with three grafts from route A).

Route.  A *mark transport* `Carrier.MarkTransport hn hP hQ` between two generic polygons (bijections
of vertex labels, crossings and visits over their crossings, carrying the sorted mark list of `P` to a
rotation of the sorted mark list of `Q`, preserving interlacement and the vertex turn signs) transports
the whole Carrier lane: the smoothing successor, the carriers (`Component`), their crossings and
`m_Q`, decompositions, true corners, the corner list up to rotation, and the index set
`uniformDecompositions` — the last *given* that uniformity is preserved, which is read on the
*transported corner polygon* `Φ = transportedCornerPolygon` (the corners of the old carrier evaluated
in the new polygon).  The corner state sum is carried once, per carrier, (i) uniformity of `Φ`
matches, (ii) `carrierRotation` agrees and (iii) `homfly` of the positive lifts agrees
(`cornerStateSum_transport`).

Two instances.  (i) `pathTransport γ 0 t` along `γ : Path P Q` in `GenericTuple n` (accepted
`SM.chambers`: constant chirotope, crossing set and same-edge parameter orders; the mark list is
carried *literally*, so the corner polygon of the transported carrier is a recast of `Φ t`); `Φ t` is
continuous in `t` and regular, so its rotation is constant (`rotationNumber_family_constant`) and its
turn signs are constant (continuous nonzero determinants); its crossing pairs are constant (accepted
`crossing_support_persists_of_geometry` + connectedness of `unitInterval`) and positivity persists, so
the positive lifts at `0` and `1` are related by a `Deform` (`Deform.of_family`) and `homfly` agrees
(`homfly_planar`).  (ii) `shiftTransport a` for the cyclic relabelling `shift a P`: `Φ` is literally
`ccpCornerPolygon`, so uniformity is trivial, the rotation agrees by `rotationNumber_shift`, and the
positive lifts differ by a cyclic re-indexing of the one component, a `Reparam`
(`reparam_positiveDiagram_single_shift`).

Descent (already closed, no placeholder): `chamber (polygonProjection P) = polygonProjection '' labelledChamber P`
(accepted `projection_labelledChamber_eq_chamber`), `projection_eq_iff`, and labelled chambers are path
connected (`labelledChambers_open_pathConnected`).

Every lemma of the chain is proved; `SM.prop_C_chamber` is proved from the chain. -/

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

/-! ## 0. Re-indexing a labelled tuple along an equality of sizes (unit U1b) -/

/-- A labelled `k`-tuple read as a labelled `k'`-tuple along `hk : k' = k`. All invariants below
are proved by `subst hk`. -/
def recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) : LabelledTuple k' :=
  fun j => f (Equiv.cast (congrArg ZMod hk) j)

theorem recastTuple_rfl {k : ℕ} (f : LabelledTuple k) : recastTuple rfl f = f := rfl

/-- The value of a `ZMod` element is unchanged by a cast along an equality of sizes. -/
theorem zmod_val_cast {k k' : ℕ} (h : k = k') (j : ZMod k) :
    (Equiv.cast (congrArg ZMod h) j).val = j.val := by
  subst h; rfl

/-- Casting forth and back along an equality of sizes is the identity. -/
theorem zmod_cast_cast {k k' : ℕ} (h : k' = k) (j : ZMod k') :
    Equiv.cast (congrArg ZMod h.symm) (Equiv.cast (congrArg ZMod h) j) = j := by
  subst h; rfl

theorem rotationNumber_recastTuple {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k)
    (f : LabelledTuple k) : rotationNumber (recastTuple hk f) = rotationNumber f := by
  subst hk; rfl

theorem regular_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) :
    Regular (recastTuple hk f) ↔ Regular f := by
  subst hk; rfl

theorem turn_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (j : ZMod k') :
    turn (recastTuple hk f) j = turn f (Equiv.cast (congrArg ZMod hk) j) := by
  subst hk; rfl

theorem forall_turn_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (σ : SignType) :
    (∀ j, turn (recastTuple hk f) j = σ) ↔ ∀ j, turn f j = σ := by
  subst hk; rfl

/-- The one-component shadow data is unchanged by a recast. -/
theorem polyComp_recastTuple {k k' : ℕ} (hk : k' = k) (h : 3 ≤ k) (h' : 3 ≤ k')
    (f : LabelledTuple k) : (PolyComp.mk k' h' (recastTuple hk f)) = PolyComp.mk k h f := by
  subst hk; rfl

namespace Carrier

variable {n : ℕ} [NeZero n]

/-! ## 1. Mark transports: the combinatorial equivalence of two generic marked traversals -/

/-- A *mark transport* from the generic polygon `P` to the generic polygon `Q`: compatible bijections
of vertex labels, crossings and visits (visits over their crossings), carrying the sorted mark list of
`P` to a rotation of the sorted mark list of `Q` (hence commuting with `markSuccessor`), preserving
interlacement and the vertex turn signs.  (The visit twin is carried automatically, `twin_eq`.) -/
structure MarkTransport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P) (hQ : Generic Q) where
  /-- vertex relabelling -/
  vert : ZMod n ≃ ZMod n
  /-- crossing bijection -/
  cross : Crossing P ≃ Crossing Q
  /-- visit bijection -/
  visit : Visit P ≃ Visit Q
  /-- visits are carried over their crossings -/
  visit_fst : ∀ v, (visit v).1 = cross v.1
  /-- the sorted mark list of `Q` is a rotation of the transported sorted mark list of `P` -/
  markList_rotated :
    (markList hn hQ).IsRotated ((markList hn hP).map (Sum.map vert visit))
  /-- interlacement is preserved -/
  interlaces_iff : ∀ x y, Interlaces hn hQ (cross x) (cross y) ↔ Interlaces hn hP x y
  /-- vertex turn signs are preserved -/
  turn_eq : ∀ i, turn Q (vert i) = turn P i

namespace MarkTransport

variable {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
  (τ : MarkTransport hn hP hQ)

/-- The induced bijection of marks. -/
def toMark : Mark P ≃ Mark Q := Equiv.sumCongr τ.vert τ.visit

theorem toMark_apply (m : Mark P) : τ.toMark m = Sum.map τ.vert τ.visit m := rfl

theorem toMark_inl (i : ZMod n) : τ.toMark (Sum.inl i) = Sum.inl (τ.vert i) := rfl

theorem toMark_inr (v : Visit P) : τ.toMark (Sum.inr v) = Sum.inr (τ.visit v) := rfl

/-- The transported support. -/
noncomputable def support (S : Finset (Crossing P)) : Finset (Crossing Q) :=
  S.map τ.cross.toEmbedding

theorem mem_support (S : Finset (Crossing P)) (x : Crossing P) :
    τ.cross x ∈ τ.support S ↔ x ∈ S := by
  simp only [support, Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem support_card (S : Finset (Crossing P)) : (τ.support S).card = S.card :=
  Finset.card_map _

theorem support_surjective (S' : Finset (Crossing Q)) : ∃ S, τ.support S = S' :=
  ⟨S'.map τ.cross.symm.toEmbedding, by
    simp [support, Finset.map_map]⟩

/-! ### 1a. The twin, the successor and the smoothing successor (unit U1a) -/

/-- The visit twin is carried to the visit twin (`visitTwin_unique`: same crossing by `visit_fst`,
distinct by injectivity). -/
theorem twin_eq (v : Visit P) : τ.visit (visitTwin v) = visitTwin (τ.visit v) := by
  apply visitTwin_unique (τ.visit v) (τ.visit (visitTwin v))
  · rw [τ.visit_fst, τ.visit_fst, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v (τ.visit.injective h)

/-- The cyclic successor commutes with the transport (from `markList_rotated` through
`List.isRotated_next_eq` and the `getElem` formula `markSuccessor_getElem`). -/
theorem markSuccessor_transport (m : Mark P) :
    markSuccessor hn hQ (τ.toMark m) = τ.toMark (markSuccessor hn hP m) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_markList hn hP m)
  have hnd : ((markList hn hP).map τ.toMark).Nodup :=
    (markList_nodup hn hP).map τ.toMark.injective
  have hi' : i < ((markList hn hP).map τ.toMark).length := by
    rw [List.length_map]; exact hi
  rw [markSuccessor_apply hn hQ, nextMark_eq_list_next hn hQ,
    List.isRotated_next_eq τ.markList_rotated (markList_nodup hn hQ),
    markSuccessor_getElem hn hP i hi]
  have h := List.next_getElem ((markList hn hP).map τ.toMark) hnd i hi'
  simp only [List.getElem_map, List.length_map] at h
  exact h

theorem selectedMarkPerm_transport (S : Finset (Crossing P)) (m : Mark P) :
    selectedMarkPerm (τ.support S) (τ.toMark m) = τ.toMark (selectedMarkPerm S m) := by
  cases m with
  | inl i => rfl
  | inr v =>
    rw [toMark_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, toMark_inr]
    have hv' : (τ.visit v).1 ∈ τ.support S ↔ v.1 ∈ S := by
      rw [τ.visit_fst, τ.mem_support]
    by_cases hv : v.1 ∈ S
    · rw [selectedVisitTwin_of_mem _ _ hv, selectedVisitTwin_of_mem _ _ (hv'.mpr hv),
        τ.twin_eq]
    · rw [selectedVisitTwin_of_not_mem _ _ hv,
        selectedVisitTwin_of_not_mem _ _ (fun h => hv (hv'.mp h))]

theorem smoothingSuccessor_transport (S : Finset (Crossing P)) (m : Mark P) :
    smoothingSuccessor hn hQ (τ.support S) (τ.toMark m) =
      τ.toMark (smoothingSuccessor hn hP S m) := by
  change markSuccessor hn hQ (selectedMarkPerm (τ.support S) (τ.toMark m)) =
    τ.toMark (markSuccessor hn hP (selectedMarkPerm S m))
  rw [τ.selectedMarkPerm_transport, τ.markSuccessor_transport]

theorem sameCycle_transport (S : Finset (Crossing P)) (a b : Mark P) :
    (smoothingSuccessor hn hQ (τ.support S)).SameCycle (τ.toMark a) (τ.toMark b) ↔
      (smoothingSuccessor hn hP S).SameCycle a b := by
  set f := smoothingSuccessor hn hP S with hf
  set f' := smoothingSuccessor hn hQ (τ.support S) with hf'
  have hstep : ∀ x, f' (τ.toMark x) = τ.toMark (f x) := τ.smoothingSuccessor_transport S
  have hinv : ∀ x, f'⁻¹ (τ.toMark x) = τ.toMark (f⁻¹ x) := by
    intro x
    rw [Equiv.Perm.inv_eq_iff_eq, hstep, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have hzpow : ∀ (i : ℤ) (x : Mark P), (f' ^ i) (τ.toMark x) = τ.toMark ((f ^ i) x) := by
    intro i
    induction i using Int.induction_on with
    | zero =>
      intro x
      rw [zpow_zero, zpow_zero, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
    | succ i ih =>
      intro x
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hstep, ih]
    | pred i ih =>
      intro x
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, ih]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, τ.toMark.injective ((hzpow i a).symm.trans hi)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hzpow i a).trans (congrArg τ.toMark hi)⟩

/-! ### 1b. Carriers, their crossings, decompositions, true corners (unit U1a) -/

/-- The carriers of `S` correspond to the carriers of the transported support. -/
noncomputable def component (S : Finset (Crossing P)) :
    Component hn hP S ≃ Component hn hQ (τ.support S) :=
  Quotient.congr τ.toMark (fun a b => (τ.sameCycle_transport S a b).symm)

theorem component_owner (S : Finset (Crossing P)) (m : Mark P) :
    τ.component S (owner hn hP S m) = owner hn hQ (τ.support S) (τ.toMark m) := rfl

theorem carrierCrossings_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossings hn hQ (τ.support S) (τ.component S q) =
      (carrierCrossings hn hP S q).map τ.cross.toEmbedding := by
  ext x'
  obtain ⟨x, rfl⟩ := τ.cross.surjective x'
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  rw [mem_carrierCrossings, mem_carrierCrossings, τ.mem_support]
  apply and_congr Iff.rfl
  constructor
  · intro h v hv
    have h1 : owner hn hQ (τ.support S) (Sum.inr (τ.visit v)) = τ.component S q :=
      h (τ.visit v) (by rw [τ.visit_fst, hv])
    apply (τ.component S).injective
    exact h1
  · intro h w hw
    obtain ⟨v, rfl⟩ := τ.visit.surjective w
    have hv : v.1 = x := τ.cross.injective ((τ.visit_fst v).symm.trans hw)
    show τ.component S (owner hn hP S (Sum.inr v)) = τ.component S q
    exact congrArg _ (h v hv)

theorem carrierCrossingCount_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossingCount hn hQ (τ.support S) (τ.component S q) =
      carrierCrossingCount hn hP S q := by
  rw [carrierCrossingCount_eq_card, carrierCrossingCount_eq_card,
    τ.carrierCrossings_transport, Finset.card_map]

theorem isDecomposition_transport (S : Finset (Crossing P)) :
    IsDecomposition hn hQ (τ.support S) ↔ IsDecomposition hn hP S := by
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
  | inl i =>
    rw [toMark_inl]
    exact Iff.rfl
  | inr v =>
    rw [toMark_inr, isTrueCorner_visit, isTrueCorner_visit, τ.visit_fst, τ.mem_support]

/-! ### 1c. The corner list and the corner polygon (unit U1b) -/

/-- Filtering a rotation of a mapped list, when the predicates correspond along the map. -/
theorem isRotated_filter_map_of_forall {α β : Type*} {l : List α} {l' : List β} (f : α → β)
    (h : l'.IsRotated (l.map f)) (p : β → Bool) (p' : α → Bool) (hp : ∀ a, p (f a) = p' a) :
    (l'.filter p).IsRotated ((l.filter p').map f) := by
  refine (h.filter p).trans ?_
  have hf : l.filter (p ∘ f) = l.filter p' := List.filter_congr (fun a _ => hp a)
  rw [List.filter_map, hf]

/-- Reading an entry of a mapped list, with the index given up to a propositional equality. -/
theorem getElem_eq_map_of_eq {α β : Type*} (f : α → β) (l : List α) (l' : List β)
    (h : l' = l.map f) (i i' : ℕ) (hii' : i = i') (hi : i < l'.length) (hi' : i' < l.length) :
    l'[i] = f (l[i']) := by
  subst h; subst hii'
  exact List.getElem_map f

/-- Reading an entry of a rotation of a mapped list. -/
theorem getElem_eq_map_of_rotate_eq {α β : Type*} (f : α → β) (l : List α) (l' : List β)
    (m : ℕ) (h : (l.map f).rotate m = l') (i i' : ℕ) (hii' : (i + m) % l.length = i')
    (hi : i < l'.length) (hi' : i' < l.length) : l'[i] = f (l[i']) := by
  subst h; subst hii'
  rw [List.getElem_rotate, List.getElem_map]
  simp only [List.length_map]

/-- The mark list of the transported carrier is a rotation of the transported mark list
(`List.IsRotated.filter`, `List.filter_map`). -/
theorem componentMarkList_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    (componentMarkList hn hQ (τ.support S) (τ.component S q)).IsRotated
      ((componentMarkList hn hP S q).map τ.toMark) := by
  unfold componentMarkList
  refine isRotated_filter_map_of_forall τ.toMark τ.markList_rotated _ _ (fun a => ?_)
  apply decide_eq_decide.mpr
  rw [← τ.component_owner S a]
  exact (τ.component S).injective.eq_iff

theorem ccpCornerList_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    (ccpCornerList hn hQ (τ.support S) (τ.component S q)).IsRotated
      ((ccpCornerList hn hP S q).map τ.toMark) := by
  unfold ccpCornerList
  exact isRotated_filter_map_of_forall τ.toMark (τ.componentMarkList_transport S q) _ _
    (fun a => decide_eq_decide.mpr (τ.isTrueCorner_transport S a))

theorem ccpCornerCount_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    ccpCornerCount hn hQ (τ.support S) (τ.component S q) = ccpCornerCount hn hP S q := by
  unfold ccpCornerCount
  rw [(τ.ccpCornerList_transport S q).perm.length_eq, List.length_map]

/-- The corner marks correspond up to a rotation `r` of the corner indices. -/
theorem exists_ccpCornerMark_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ r : ZMod (ccpCornerCount hn hP S q), ∀ j : ZMod (ccpCornerCount hn hP S q),
      ccpCornerMark hn hQ (τ.support S) (τ.component S q)
          (Equiv.cast (congrArg ZMod (τ.ccpCornerCount_transport S q).symm) j) =
        τ.toMark (ccpCornerMark hn hP S q (j + r)) := by
  obtain ⟨m, hm⟩ := (τ.ccpCornerList_transport S q).symm
  refine ⟨(m : ZMod (ccpCornerCount hn hP S q)), fun j => ?_⟩
  unfold ccpCornerMark
  refine getElem_eq_map_of_rotate_eq τ.toMark _ _ m hm _ _ ?_ _ _
  change (_ + m) % ccpCornerCount hn hP S q = _
  rw [zmod_val_cast (τ.ccpCornerCount_transport S q).symm j, ZMod.val_add, ZMod.val_natCast,
    Nat.add_mod_mod]

/-- The corner polygon of the carrier `q` of `P` read at the geometry of `Q`: the vertex at the
corner mark `c_j` of `q` is the plane point of `Q` at the transported mark. -/
noncomputable def transportedCornerPolygon (S : Finset (Crossing P)) (q : Component hn hP S) :
    LabelledTuple (ccpCornerCount hn hP S q) :=
  fun j => traversalEvaluation Q (markPosition hn hQ.1 (τ.toMark (ccpCornerMark hn hP S q j)))

/-- The corner polygon of the transported carrier is the transported corner polygon, up to a
cyclic re-indexing. -/
theorem exists_ccpCornerPolygon_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ r : ZMod (ccpCornerCount hn hP S q),
      ccpCornerPolygon hn hQ (τ.support S) (τ.component S q) =
        recastTuple (τ.ccpCornerCount_transport S q) (shift r (τ.transportedCornerPolygon S q)) := by
  obtain ⟨r, hr⟩ := τ.exists_ccpCornerMark_transport S q
  refine ⟨r, funext fun j => ?_⟩
  have h := hr (Equiv.cast (congrArg ZMod (τ.ccpCornerCount_transport S q)) j)
  rw [zmod_cast_cast (τ.ccpCornerCount_transport S q) j] at h
  exact congrArg (fun m => traversalEvaluation Q (markPosition hn hQ.1 m)) h

/-- When the mark list is carried literally (no rotation), so is the corner polygon. -/
theorem ccpCornerPolygon_transport_of_markList_eq
    (h : markList hn hQ = (markList hn hP).map τ.toMark)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    ccpCornerPolygon hn hQ (τ.support S) (τ.component S q) =
      recastTuple (τ.ccpCornerCount_transport S q) (τ.transportedCornerPolygon S q) := by
  have h1 : componentMarkList hn hQ (τ.support S) (τ.component S q) =
      (componentMarkList hn hP S q).map τ.toMark := by
    unfold componentMarkList
    rw [h, List.filter_map]
    congr 1
    refine List.filter_congr (fun a _ => ?_)
    apply decide_eq_decide.mpr
    rw [← τ.component_owner S a]
    exact (τ.component S).injective.eq_iff
  have h2 : ccpCornerList hn hQ (τ.support S) (τ.component S q) =
      (ccpCornerList hn hP S q).map τ.toMark := by
    unfold ccpCornerList
    rw [h1, List.filter_map]
    congr 1
    exact List.filter_congr (fun a _ => decide_eq_decide.mpr (τ.isTrueCorner_transport S a))
  funext j
  exact congrArg (fun m => traversalEvaluation Q (markPosition hn hQ.1 m))
    (getElem_eq_map_of_eq τ.toMark _ _ h2 _ _
      (zmod_val_cast (τ.ccpCornerCount_transport S q) j).symm _ _)

/-! ### 1d. Uniformity read on the transported corner polygon, the index set, the prefactor
(unit U2) -/

/-- Uniformity of the transported carrier is uniformity of the transported corner polygon
(`exists_ccpCornerPolygon_transport`, `forall_turn_recastTuple`, `turn_shift`, reindexing by
`Equiv.addRight r`). -/
theorem carrierUniform_iff_transported (S : Finset (Crossing P)) (q : Component hn hP S) :
    CarrierUniform hn hQ (τ.support S) (τ.component S q) ↔
      ∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ := by
  obtain ⟨r, hr⟩ := τ.exists_ccpCornerPolygon_transport S q
  unfold CarrierUniform
  rw [hr]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  rw [forall_turn_recastTuple]
  simp only [turn_shift]
  constructor
  · intro h j
    have := h (j - r)
    rwa [sub_add_cancel] at this
  · intro h j
    exact h _

theorem uniformDecomposition_transport {S : Finset (Crossing P)}
    (huni : ∀ q : Component hn hP S,
      (∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ) ↔
        CarrierUniform hn hP S q) :
    UniformDecomposition hn hQ (τ.support S) ↔ UniformDecomposition hn hP S := by
  unfold UniformDecomposition
  rw [(τ.component S).surjective.forall]
  exact forall_congr' fun q => (τ.carrierUniform_iff_transported S q).trans (huni q)

theorem mem_uniformDecompositions_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      (∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ) ↔
        CarrierUniform hn hP S q)
    (S : Finset (Crossing P)) :
    τ.support S ∈ uniformDecompositions hn hQ ↔ S ∈ uniformDecompositions hn hP := by
  rw [mem_uniformDecompositions, mem_uniformDecompositions]
  have hd : τ.support S ∈ independentSupports hn hQ ↔ S ∈ independentSupports hn hP :=
    τ.isDecomposition_transport S
  by_cases hS : IsDecomposition hn hP S
  · exact and_congr hd (τ.uniformDecomposition_transport (huni S hS))
  · constructor
    · rintro ⟨h, _⟩
      exact absurd (hd.mp h) hS
    · rintro ⟨h, _⟩
      exact absurd h hS

include τ in
/-- The intended `leftTurns_transport`: the prefactor `ℓ` is carried by a mark transport
(`Finset.card_equiv τ.vert`, `turn_eq`). -/
theorem leftTurns_eq_of_transport : leftTurns Q = leftTurns P := by
  unfold leftTurns
  symm
  apply Finset.card_equiv τ.vert
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, τ.turn_eq]

include τ in
/-- Assembly fix (PLAN_FINAL.md §5 addendum, found by U2): in the skeleton this statement did not
mention `τ`, so by Lean's variable-inclusion rule it did not take the transport and was false as stated
(machine-checked counterexample `leftTurns_transport_false_as_stated` in U2.lean).  `include τ in`
restores the intended content; the proof is `leftTurns_eq_of_transport`. -/
theorem leftTurns_transport : leftTurns Q = leftTurns P :=
  τ.leftTurns_eq_of_transport

/-! ### 1e. The state sum under a transport with equal corner coefficients (unit U2) -/

theorem cornerSlot_transport {S : Finset (Crossing P)} (q : Component hn hP S)
    (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q) :
    cornerSlot hn hQ (τ.support S) (τ.component S q) = cornerSlot hn hP S q := by
  unfold cornerSlot carrierRotationInt
  rw [τ.carrierCrossingCount_transport S q, hrot]

theorem cornerCoefficient_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q)
    (hH : homfly (positiveLift hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS)) = homfly (positiveLift hn hP S q hS)) :
    cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt]
  unfold cornerHomfly
  rw [τ.cornerSlot_transport q hrot, hH]

theorem cornerProduct_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (hcoef : ∀ q : Component hn hP S,
      cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerProduct hn hQ (τ.support S) ((τ.isDecomposition_transport S).mpr hS) =
      cornerProduct hn hP S hS := by
  unfold cornerProduct
  exact (Fintype.prod_equiv (τ.component S) _ _ fun q => (hcoef q).symm).symm

/-- **Assembly.** The corner state sum is carried by a mark transport under which uniformity
(read on the transported corner polygons) and the corner coefficients agree. -/
theorem cornerStateSum_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      (∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ) ↔
        CarrierUniform hn hP S q)
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerStateSum hn hQ = cornerStateSum hn hP := by
  unfold cornerStateSum
  rw [τ.leftTurns_eq_of_transport]
  congr 1
  -- the dependent summands as total functions of the underlying set (device of
  -- `cornerStateSum_eq_sum_independentSupports`)
  set g : Finset (Crossing P) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions hn hP then
      (-1) ^ S.card * cornerProduct hn hP S (isDecomposition_of_mem_uniformDecompositions hn hP h)
    else 0 with hg
  set g' : Finset (Crossing Q) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions hn hQ then
      (-1) ^ S.card * cornerProduct hn hQ S (isDecomposition_of_mem_uniformDecompositions hn hQ h)
    else 0 with hg'
  have h1 : (∑ S ∈ (uniformDecompositions hn hQ).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hQ S.1 (isDecomposition_of_mem_uniformDecompositions hn hQ S.2)) =
      ∑ S ∈ (uniformDecompositions hn hQ).attach, g' S.1 := by
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
  -- reindex the index set along `τ.support`, a bijection `uD(P) → uD(Q)`
  refine Finset.sum_nbij τ.support ?_ ?_ ?_ ?_
  · intro S hS
    exact (τ.mem_uniformDecompositions_transport huni S).mpr hS
  · intro S _ T _ h
    exact Finset.map_injective τ.cross.toEmbedding h
  · intro S' hS'
    obtain ⟨S, rfl⟩ := τ.support_surjective S'
    exact ⟨S, (τ.mem_uniformDecompositions_transport huni S).mp hS', rfl⟩
  · intro S hS
    have hS' : IsDecomposition hn hP S := isDecomposition_of_mem_uniformDecompositions hn hP hS
    have hSQ : τ.support S ∈ uniformDecompositions hn hQ :=
      (τ.mem_uniformDecompositions_transport huni S).mpr hS
    simp only [hg, hg']
    rw [dite_eq_left hS, dite_eq_left hSQ, τ.support_card]
    congr 1
    exact (τ.cornerProduct_transport hS' (hcoef S hS')).symm

end MarkTransport

end Carrier

/-! ## 2c. Link-layer lemmas (units U4 and U5) -/

namespace Link

/-- Proof-irrelevant congruence of positive diagrams along an equality of shadows. -/
theorem positiveDiagram_congr {Γ Γ' : Shadow} (h : Γ = Γ') (hΓ : Γ.Generic) (hΓ' : Γ'.Generic) :
    Γ.positiveDiagram hΓ = Γ'.positiveDiagram hΓ' := by
  subst h
  rfl

/-- Crossing pairs of one-component shadows on two polygons with the same crossing supports. -/
theorem single_isCrossing_iff_of_forall {k : ℕ} (hk : 3 ≤ k) {X Y : LabelledTuple k}
    (h : ∀ s, IsCrossing X s ↔ IsCrossing Y s) (x : Finset (Shadow.single ⟨k, hk, X⟩).Strand) :
    (Shadow.single ⟨k, hk, X⟩).IsCrossing x ↔ (Shadow.single ⟨k, hk, Y⟩).IsCrossing x := by
  rw [Shadow.single_isCrossing_iff, Shadow.single_isCrossing_iff]
  exact h _

/-- (Graft from route A.)  A polygon whose one-component shadow is generic lies on the geometric
record domain: nonzero edges (`regular`), meetings of remote edges interior and transverse
(`tail_off`, `transverse`), no triple point (`no_triple`). -/
theorem crossingGeometry_of_single_generic {k : ℕ} (hk : 3 ≤ k) {T : LabelledTuple k}
    (h : (Shadow.single ⟨k, hk, T⟩).Generic) : CrossingGeometry T := by
  -- `tail_off` in label form: no vertex on a non-incident closed edge.
  have hvertex : ∀ a b : ZMod k, ¬ incident a b → T a ∉ edgeSegment T b := fun a b hinc =>
    h.tail_off ⟨0, a⟩ ⟨0, b⟩ (fun h' => hinc ((Shadow.single_incidentTail_iff _ _ _).mp h'))
  refine ⟨fun i => ((regular_iff_edges T).mp (h.regular 0) i).1, ?_, ?_⟩
  · intro i j hr x hi hj
    refine ⟨remote_closed_point_interior hvertex hr hi hj,
      remote_closed_point_interior hvertex (remote_symm hr) hj hi, ?_⟩
    exact h.transverse ⟨0, i⟩ ⟨0, j⟩
      (fun h' => hr ((Shadow.single_adjacent_iff _ _ _).mp h')) ⟨x, hi, hj⟩
  · rintro ⟨i, j, l, x, hij, hjl, hil, hi, hj, hl⟩
    exact h.no_triple ⟨⟨0, i⟩, ⟨0, j⟩, ⟨0, l⟩,
      fun e => hij (congrArg (Shadow.singleStrandEquiv _) e),
      fun e => hjl (congrArg (Shadow.singleStrandEquiv _) e),
      fun e => hil (congrArg (Shadow.singleStrandEquiv _) e), x, ⟨hi, hj⟩, hl⟩

/-- A generic deformation from a family on the unit interval (`DeformData` with
`γ t := V (Set.projIcc 0 1 zero_le_one t)`). -/
theorem Deform.of_family (D : Diagram) {V : unitInterval → D.Γ.Vertices}
    (hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun t => V t i j)
    (hgen : ∀ t, (D.Γ.withVertices (V t)).Generic)
    (hcross : ∀ t (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V t)).IsCrossing x ↔ D.Γ.IsCrossing x)
    (h0 : V 0 = D.Γ.vertices) :
    Deform D (D.deform (V 1) (hgen 1) (hcross 1)) := by
  have h0' : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := Set.projIcc_left _
  have h1' : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) := Set.projIcc_right _
  exact ⟨{ γ := fun t => V (Set.projIcc 0 1 zero_le_one t)
           continuous := fun i j => ((hV i j).comp continuous_projIcc).continuousOn
           start := by
             show V (Set.projIcc 0 1 zero_le_one 0) = D.Γ.vertices
             rw [h0']
             exact h0
           generic := fun t _ => hgen _
           crossings := fun t _ x => hcross _ x
           stop := by
             show D.deform (V 1) (hgen 1) (hcross 1) =
               D.deform (V (Set.projIcc 0 1 zero_le_one 1)) (hgen _) (hcross _)
             rw [h1'] }⟩

/-- Positivity of every crossing persists along a generic deformation: the determinant of the
over and under directions is continuous and nonzero at every time. -/
theorem Diagram.isPositive_deform_of_family (D : Diagram) {V : unitInterval → D.Γ.Vertices}
    (hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun t => V t i j)
    (hgen : ∀ t, (D.Γ.withVertices (V t)).Generic)
    (hcross : ∀ t (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V t)).IsCrossing x ↔ D.Γ.IsCrossing x)
    (h0 : V 0 = D.Γ.vertices) (hpos : ∀ x, D.IsPositive x)
    (x : (D.deform (V 1) (hgen 1) (hcross 1)).Γ.Crossing) :
    (D.deform (V 1) (hgen 1) (hcross 1)).IsPositive x := by
  -- the same crossing pair read in `D` and at every time `t`
  let x₀ : D.Γ.Crossing := ⟨x.val, (hcross 1 x.val).mp x.2⟩
  let xt (t : unitInterval) : (D.Γ.withVertices (V t)).Crossing :=
    ⟨x.val, (hcross t x.val).mpr x₀.2⟩
  let o : D.Γ.Strand := D.overStrand x₀
  let u : D.Γ.Strand := D.underStrand x₀
  -- the determinant of the over and under directions along the family
  let f (t : unitInterval) : ℝ := det (edge (V t o.1) o.2) (edge (V t u.1) u.2)
  have he : ∀ s : D.Γ.Strand, Continuous fun t => edge (V t s.1) s.2 := fun s =>
    (hV s.1 (s.2 + 1)).sub (hV s.1 s.2)
  have hf : Continuous f := ((he o).fst.mul (he u).snd).sub ((he o).snd.mul (he u).fst)
  have hne : ∀ t, f t ≠ 0 := fun t =>
    (hgen t).transverse o u (D.not_adjacent_over_under x₀)
      ((D.Γ.withVertices (V t)).crossing_pair_spec (xt t) (D.over_mem x₀) (D.under_mem x₀)
        (D.over_ne_under x₀)).2
  have hsign : Continuous fun t => SignType.sign (f t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_sign_of_ne_zero (hne t)).comp hf.continuousAt
  have hconst : SignType.sign (f 1) = SignType.sign (f 0) :=
    PreconnectedSpace.constant inferInstance hsign
  have hf0 : 0 < f 0 := by
    show 0 < det (edge (V 0 o.1) o.2) (edge (V 0 u.1) u.2)
    rw [h0]
    exact hpos x₀
  have hunder : (D.deform (V 1) (hgen 1) (hcross 1)).underStrand x = u :=
    ((D.Γ.withVertices (V 1)).eq_other_of_mem_of_ne x (D.over_mem x₀) (D.under_mem x₀)
      (D.under_ne_over x₀)).symm
  show 0 < det _ _
  rw [hunder]
  exact sign_eq_one_iff.mp (hconst.trans (sign_eq_one_iff.mpr hf0))

/-- A recast of the polygon does not change the positive diagram of a one-component shadow. -/
theorem positiveDiagram_single_recast {k k' : ℕ} (hk : k' = k) (h : 3 ≤ k) (h' : 3 ≤ k')
    (X : LabelledTuple k) (hΓ : (Shadow.single ⟨k', h', recastTuple hk X⟩).Generic)
    (hΓ' : (Shadow.single ⟨k, h, X⟩).Generic) :
    (Shadow.single ⟨k', h', recastTuple hk X⟩).positiveDiagram hΓ =
      (Shadow.single ⟨k, h, X⟩).positiveDiagram hΓ' := by
  subst hk
  rfl

/-- Points of a one-component shadow are determined by their traversal point. -/
theorem Shadow.single_pt_ext (C : PolyComp) {p q : (Shadow.single C).Pt} (h : p.2 = q.2) :
    p = q := by
  obtain ⟨i, p⟩ := p
  obtain ⟨j, q⟩ := q
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  exact congrArg (Sigma.mk 0) h

/-- The strand relabelling of the cyclic shift by `r`, `⟨i, a⟩ ↦ ⟨i, a + r⟩`, from the shifted
one-component shadow to the original one (`f = id`, `sgn = 1`). -/
def shiftStrandMap (C : PolyComp) (r : ZMod C.k) :
    StrandMap (Shadow.single ⟨C.k, C.hk, shift r C.P⟩) (Shadow.single C) where
  toFun s := ⟨s.1, s.2 + r⟩
  inj := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    obtain rfl : i = 0 := Subsingleton.elim i 0
    obtain rfl : j = 0 := Subsingleton.elim j 0
    have h' : a + r = b + r := congrArg (Shadow.singleStrandEquiv C) h
    rw [add_right_cancel h']
  f := id
  f_inj := Function.injective_id
  seg_eq := fun s => by
    rw [Set.image_id]
    exact (edgeSegment_shift r C.P s.2).symm
  interior_eq := fun s => by
    rw [Set.image_id]
    exact (edgeInterior_shift r C.P s.2).symm
  vert s := ⟨s.1, s.2 + r⟩
  tail_eq := fun _ => rfl
  adjacent_iff := fun s t =>
    (Shadow.single_adjacent_iff C _ _).trans
      ((show adjacent (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ s + r)
            (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ t + r) ↔
          adjacent (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ s)
            (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ t) by
        unfold adjacent
        rw [add_sub_add_right_eq_sub]).trans (Shadow.single_adjacent_iff _ s t).symm)
  incidentTail_iff := fun s t =>
    (Shadow.single_incidentTail_iff C _ _).trans
      ((show incident (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ s + r)
            (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ t + r) ↔
          incident (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ s)
            (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ t) by
        unfold incident
        rw [add_sub_right_comm, add_left_inj, add_left_inj]).trans
        (Shadow.single_incidentTail_iff _ s t).symm)
  sgn := 1
  sgn_ne := by decide
  det_eq := fun s t => by
    show det (edge C.P (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ s + r))
        (edge C.P (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ t + r)) =
      ((1 : SignType) : ℝ) *
        det (edge (shift r C.P) (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ s))
          (edge (shift r C.P) (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ t))
    rw [edge_shift, edge_shift, SignType.coe_one, one_mul]

section ShiftReparam

variable (C : PolyComp) (r : ZMod C.k)

theorem shiftStrandMap_toFun (s : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).Strand) :
    (shiftStrandMap C r).toFun s = ⟨s.1, s.2 + r⟩ := rfl

theorem shiftStrandMap_surjective : Function.Surjective (shiftStrandMap C r).toFun := by
  intro s
  refine ⟨⟨s.1, s.2 - r⟩, ?_⟩
  show (⟨s.1, s.2 - r + r⟩ : (Shadow.single C).Strand) = s
  rw [sub_add_cancel]

/-- The pullback of the positive diagram along the shift relabelling (bookkeeping name). -/
noncomputable abbrev shiftPullback (hΓ : (Shadow.single C).Generic)
    (hΓ' : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).Generic) : Diagram :=
  ((Shadow.single C).positiveDiagram hΓ).pullback (shiftStrandMap C r) hΓ'.regular

/-- The pullback of the positive diagram along the shift is positive (`sgn = 1`), hence it is the
positive diagram of the shifted shadow. -/
theorem shiftPullback_eq_positiveDiagram (hΓ : (Shadow.single C).Generic)
    (hΓ' : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).Generic) :
    shiftPullback C r hΓ hΓ' = (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).positiveDiagram hΓ' := by
  apply Shadow.eq_positiveDiagram_of_isPositive _ hΓ' _ rfl
  intro x
  exact (Diagram.pullback_isPositive_iff _ _ _ x).mpr
    (Or.inl ⟨rfl, Shadow.positiveDiagram_isPositive _ _ _⟩)

/-- The over occurrence of the pullback at `x'` is the shift of the over occurrence of the
positive diagram at the corresponding crossing: the labels agree by `toFun_pullback_overStrand`
and the crossing parameters by uniqueness on a nonzero edge. -/
theorem shiftPullback_overVisit_snd (hΓ : (Shadow.single C).Generic)
    (hΓ' : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).Generic)
    (x' : (shiftPullback C r hΓ hΓ').Γ.Crossing) :
    traversalShift r (((Shadow.single C).positiveDiagram hΓ).visitPt
        (((Shadow.single C).positiveDiagram hΓ).overVisit
          ((shiftStrandMap C r).mapCrossing x'))).2 =
      ((shiftPullback C r hΓ hΓ').visitPt ((shiftPullback C r hΓ hΓ').overVisit x')).2 := by
  have hover : (shiftStrandMap C r).toFun ((shiftPullback C r hΓ hΓ').overStrand x') =
      ((Shadow.single C).positiveDiagram hΓ).overStrand ((shiftStrandMap C r).mapCrossing x') :=
    Diagram.toFun_pullback_overStrand ((Shadow.single C).positiveDiagram hΓ) (shiftStrandMap C r)
      hΓ'.regular x'
  have hlab : Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩
        ((shiftPullback C r hΓ hΓ').overStrand x') + r =
      Shadow.singleStrandEquiv C
        (((Shadow.single C).positiveDiagram hΓ).overStrand ((shiftStrandMap C r).mapCrossing x')) :=
    congrArg (Shadow.singleStrandEquiv C) hover
  have hpar : (shiftPullback C r hΓ hΓ').crossingParam x' ((shiftPullback C r hΓ hΓ').over_mem x') =
      ((Shadow.single C).positiveDiagram hΓ).crossingParam ((shiftStrandMap C r).mapCrossing x')
        (((Shadow.single C).positiveDiagram hΓ).over_mem _) := by
    have h1 : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).crossingPoint x' =
        edgePoint (shift r C.P)
          (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ ((shiftPullback C r hΓ hΓ').overStrand x'))
          ((shiftPullback C r hΓ hΓ').crossingParam x' ((shiftPullback C r hΓ hΓ').over_mem x')) :=
      ((shiftPullback C r hΓ hΓ').crossingParam_spec x' ((shiftPullback C r hΓ hΓ').over_mem x')).2.2
    have h2 : (Shadow.single C).crossingPoint ((shiftStrandMap C r).mapCrossing x') =
        edgePoint C.P
          (Shadow.singleStrandEquiv C
            (((Shadow.single C).positiveDiagram hΓ).overStrand ((shiftStrandMap C r).mapCrossing x')))
          (((Shadow.single C).positiveDiagram hΓ).crossingParam ((shiftStrandMap C r).mapCrossing x')
            (((Shadow.single C).positiveDiagram hΓ).over_mem _)) :=
      (((Shadow.single C).positiveDiagram hΓ).crossingParam_spec ((shiftStrandMap C r).mapCrossing x')
        (((Shadow.single C).positiveDiagram hΓ).over_mem _)).2.2
    have h3 : (Shadow.single C).crossingPoint ((shiftStrandMap C r).mapCrossing x') =
        (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).crossingPoint x' :=
      (shiftStrandMap C r).crossingPoint_mapCrossing hΓ x'
    apply edgePoint_injective ((regular_iff_edges C.P).mp (hΓ.regular 0) _).1
    calc edgePoint C.P
          (Shadow.singleStrandEquiv C
            (((Shadow.single C).positiveDiagram hΓ).overStrand ((shiftStrandMap C r).mapCrossing x')))
          ((shiftPullback C r hΓ hΓ').crossingParam x' ((shiftPullback C r hΓ hΓ').over_mem x'))
        = edgePoint C.P
          (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩
            ((shiftPullback C r hΓ hΓ').overStrand x') + r)
          ((shiftPullback C r hΓ hΓ').crossingParam x' ((shiftPullback C r hΓ hΓ').over_mem x')) := by
          rw [hlab]
      _ = edgePoint (shift r C.P)
          (Shadow.singleStrandEquiv ⟨C.k, C.hk, shift r C.P⟩ ((shiftPullback C r hΓ hΓ').overStrand x'))
          ((shiftPullback C r hΓ hΓ').crossingParam x' ((shiftPullback C r hΓ hΓ').over_mem x')) :=
          (edgePoint_shift r C.P _ _).symm
      _ = (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).crossingPoint x' := h1.symm
      _ = (Shadow.single C).crossingPoint ((shiftStrandMap C r).mapCrossing x') := h3.symm
      _ = _ := h2
  refine Prod.ext ?_ (Subtype.ext ?_)
  · exact (eq_sub_of_add_eq hlab).symm
  · exact hpar.symm

/-- The reparametrization data of the cyclic shift: `e = id`, `φ = traversalShiftEquiv r`. -/
noncomputable def shiftReparamData (hΓ : (Shadow.single C).Generic)
    (hΓ' : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).Generic) :
    ReparamData ((Shadow.single C).positiveDiagram hΓ) (shiftPullback C r hΓ hΓ') where
  e := Equiv.refl _
  φ := fun _ => traversalShiftEquiv r
  between := fun _ p q s h => (traversalBetween_shift r p q s).mpr h
  eval_eq := fun _ p => traversalEvaluation_shift C.P r p
  over_map := fun x =>
    ⟨((shiftStrandMap C r).crossingEquiv (shiftStrandMap_surjective C r)).symm x, by
      have h := shiftPullback_overVisit_snd C r hΓ hΓ'
        (((shiftStrandMap C r).crossingEquiv (shiftStrandMap_surjective C r)).symm x)
      rw [show (shiftStrandMap C r).mapCrossing
          (((shiftStrandMap C r).crossingEquiv (shiftStrandMap_surjective C r)).symm x) = x from
        ((shiftStrandMap C r).crossingEquiv (shiftStrandMap_surjective C r)).apply_symm_apply x]
        at h
      exact Shadow.single_pt_ext ⟨C.k, C.hk, shift r C.P⟩ h⟩
  over_surj := fun x' =>
    ⟨(shiftStrandMap C r).mapCrossing x',
      Shadow.single_pt_ext ⟨C.k, C.hk, shift r C.P⟩ (shiftPullback_overVisit_snd C r hΓ hΓ' x')⟩

end ShiftReparam

/-- A cyclic shift of the labels of a one-component positive diagram is a reparametrization
(`StrandMap` `⟨i, a⟩ ↦ ⟨i, a + r⟩` with `f = id`, `sgn = 1`; the pullback of the positive diagram is
positive, hence the positive diagram of the shifted shadow; `ReparamData` with
`φ = traversalShiftEquiv r`, `traversalBetween_shift`, `traversalEvaluation_shift`; over occurrences
by `toFun_pullback_overStrand` and uniqueness of the crossing parameter on a nonzero edge). -/
theorem reparam_positiveDiagram_single_shift (C : PolyComp) (r : ZMod C.k)
    (hΓ : (Shadow.single C).Generic) (hΓ' : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).Generic) :
    Reparam ((Shadow.single C).positiveDiagram hΓ)
      ((Shadow.single ⟨C.k, C.hk, shift r C.P⟩).positiveDiagram hΓ') := by
  rw [← shiftPullback_eq_positiveDiagram C r hΓ hΓ']
  exact ⟨shiftReparamData C r hΓ hΓ'⟩

end Link

namespace Carrier

variable {n : ℕ} [NeZero n]

/-! ## 2. Transport along a path of generic polygons (unit U3) -/

section PathTransport

/-- (U3 helper.) `turn` of a recast tuple at a cast index is the turn at the index. -/
theorem turn_recastTuple_cast {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (j : ZMod k) :
    turn (recastTuple hk f) (Equiv.cast (congrArg ZMod hk.symm) j) = turn f j := by
  subst hk
  rfl

/-- The mark order is determined by the crossing set and the same-edge parameter orders
(vertex/vertex by label, vertex/visit by label and strict interiority, visit/visit by
`geometric_visitKey_lt_transport`). -/
theorem markKey_lt_transport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P)
    (hQ : Generic Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : CrossingParameterOrderAgrees P Q) (a b : Mark P) :
    markKey hn hQ.1 (Sum.map id (visitTransport hs) a) <
        markKey hn hQ.1 (Sum.map id (visitTransport hs) b) ↔
      markKey hn hP.1 a < markKey hn hP.1 b := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      simp only [Sum.map_inl, id_eq, markKey_vertex]
    | inr w =>
      simp only [Sum.map_inl, Sum.map_inr, id_eq]
      unfold markKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (i.val < w.2.val.val ∨ i = w.2.val ∧ (0 : ℝ) < visitParameter (visitTransport hs w)) ↔
        (i.val < w.2.val.val ∨ i = w.2.val ∧ (0 : ℝ) < visitParameter w)
      exact or_congr Iff.rfl (and_congr_right fun _ => iff_of_true
        (visitPosition_interior hn hQ.1 _).1 (visitPosition_interior hn hP.1 w).1)
  | inr v =>
    cases b with
    | inl j =>
      simp only [Sum.map_inl, Sum.map_inr, id_eq]
      unfold markKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < j.val ∨ v.2.val = j ∧ visitParameter (visitTransport hs v) < (0 : ℝ)) ↔
        (v.2.val.val < j.val ∨ v.2.val = j ∧ visitParameter v < (0 : ℝ))
      exact or_congr Iff.rfl (and_congr_right fun _ => iff_of_false
        (not_lt.mpr (visitPosition_interior hn hQ.1 _).1.le)
        (not_lt.mpr (visitPosition_interior hn hP.1 v).1.le))
    | inr w =>
      simp only [Sum.map_inr]
      exact (geometric_visitKey_lt_transport (generic_crossingGeometry hn hP)
        (generic_crossingGeometry hn hQ) hs ho v w).symm

/-- Both sorted mark lists are sorted by keys whose order agrees: they are literally carried. -/
theorem markList_transport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P)
    (hQ : Generic Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : CrossingParameterOrderAgrees P Q) :
    markList hn hQ = (markList hn hP).map (Sum.map id (visitTransport hs)) := by
  have hinj : Function.Injective (Sum.map (id : ZMod n → ZMod n) (visitTransport hs)) :=
    Sum.map_injective.mpr ⟨Function.injective_id, (visitTransport hs).injective⟩
  have hsurj : Function.Surjective (Sum.map (id : ZMod n → ZMod n) (visitTransport hs)) :=
    Sum.map_surjective.mpr ⟨Function.surjective_id, (visitTransport hs).surjective⟩
  apply List.Perm.eq_of_pairwise (le := fun a b => markKey hn hQ.1 a ≤ markKey hn hQ.1 b)
  · intro a b _ _ hab hba
    exact markKey_injective hn hQ (le_antisymm hab hba)
  · exact markList_sorted hn hQ
  · rw [List.pairwise_map]
    refine (markList_sorted hn hP).imp ?_
    intro a b h
    rw [← not_lt] at h ⊢
    exact fun h' => h ((markKey_lt_transport hn hP hQ hs ho b a).mp h')
  · apply (List.perm_ext_iff_of_nodup (markList_nodup hn hQ) ((markList_nodup hn hP).map hinj)).mpr
    intro a
    refine ⟨fun _ => ?_, fun _ => mem_markList hn hQ a⟩
    obtain ⟨b, rfl⟩ := hsurj a
    exact List.mem_map.mpr ⟨b, mem_markList hn hP b, rfl⟩

variable {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]

omit [NeZero n] in
theorem generic_family_crossingParameterOrderAgrees (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) : CrossingParameterOrderAgrees (F s).val (F t).val := by
  intro i j k hij hik
  exact generic_family_crossingOrder_constant hn hF s i j k hij hik t s

omit [NeZero n] in
theorem generic_family_turn_constant {F : α → GenericTuple n} (hF : Continuous F) (s t : α)
    (i : ZMod n) : turn (F s).val i = turn (F t).val i :=
  generic_family_chi_constant hF s t _ _ _

variable (hn : 3 ≤ n) {P Q : GenericTuple n} (γ : Path P Q)
include hn γ

omit [NeZero n] in
theorem path_crossing_iff (s t : unitInterval) (c : Finset (ZMod n)) :
    IsCrossing (γ s).val c ↔ IsCrossing (γ t).val c :=
  generic_family_crossing_constant hn γ.continuous s t c

/-- The mark transport along a path, from time `s` to time `t`. -/
noncomputable def pathTransport (s t : unitInterval) : MarkTransport hn (γ s).2 (γ t).2 where
  vert := Equiv.refl _
  cross := crossingTransport (path_crossing_iff hn γ s t)
  visit := visitTransport (path_crossing_iff hn γ s t)
  visit_fst := fun _ => rfl
  markList_rotated := by
    rw [markList_transport hn (γ s).2 (γ t).2 (path_crossing_iff hn γ s t)
      (generic_family_crossingParameterOrderAgrees hn γ.continuous s t)]
    exact List.IsRotated.refl _
  interlaces_iff := fun x y =>
    ((geometric_interlaces_transport (generic_crossingGeometry hn (γ s).2)
      (generic_crossingGeometry hn (γ t).2) (path_crossing_iff hn γ s t)
      (generic_family_crossingParameterOrderAgrees hn γ.continuous s t) x y)).symm
  turn_eq := fun i => generic_family_turn_constant γ.continuous t s i

theorem pathTransport_toMark_self (s : unitInterval) (m : Mark (γ s).val) :
    (pathTransport hn γ s s).toMark m = m := by
  cases m with
  | inl i => rfl
  | inr v => rfl

theorem pathTransport_markList_eq (s t : unitInterval) :
    markList hn (γ t).2 = (markList hn (γ s).2).map (pathTransport hn γ s t).toMark :=
  markList_transport hn (γ s).2 (γ t).2 (path_crossing_iff hn γ s t)
    (generic_family_crossingParameterOrderAgrees hn γ.continuous s t)

/-! ### 2a. The corner polygons form a continuous family of regular tuples -/

omit [NeZero n] in
/-- The crossing point of a persisting crossing moves continuously (Cramer: `edgeParameter` is
continuous, `generic_family_edgeParameter_continuous`). -/
theorem continuous_path_crossingPoint (c : Crossing (γ 0).val) :
    Continuous fun t : unitInterval => crossingPoint (crossingTransport (path_crossing_iff hn γ 0 t) c) := by
  obtain ⟨i, j, hij, _, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hij]; simp
  have hcross : ∀ t : unitInterval, IsCrossing (γ t).val {i, j} := fun t =>
    (path_crossing_iff hn γ 0 t _).mp (hij ▸ c.property)
  have key : ∀ t : unitInterval,
      crossingPoint (crossingTransport (path_crossing_iff hn γ 0 t) c) =
        (γ t).val i + edgeParameter (γ t).val i j • edge (γ t).val i := by
    intro t
    rw [(crossingParameter_spec (crossingTransport (path_crossing_iff hn γ 0 t) c) i hi).2.2,
      crossingParameter_eq_of_support_pair hn (γ t).2.1 _ i j hi hij]
    rfl
  have hc : Continuous fun t : unitInterval => (γ t).val := continuous_subtype_val.comp γ.continuous
  simp_rw [key]
  exact ((continuous_vertex i).comp hc).add
    ((generic_family_edgeParameter_continuous hn γ.continuous i j hcross).smul
      ((continuous_edge i).comp hc))

theorem continuous_transportedCornerPolygon (S : Finset (Crossing (γ 0).val))
    (q : Component hn (γ 0).2 S) (j : ZMod (ccpCornerCount hn (γ 0).2 S q)) :
    Continuous fun t : unitInterval => (pathTransport hn γ 0 t).transportedCornerPolygon S q j := by
  have hc : Continuous fun t : unitInterval => (γ t).val := continuous_subtype_val.comp γ.continuous
  unfold MarkTransport.transportedCornerPolygon
  cases h : ccpCornerMark hn (γ 0).2 S q j with
  | inl i =>
    show Continuous fun t : unitInterval =>
      traversalEvaluation (γ t).val (markPosition hn (γ t).2.1 (Sum.inl i))
    simp only [markPosition_evaluation_vertex]
    exact (continuous_vertex i).comp hc
  | inr v =>
    show Continuous fun t : unitInterval => traversalEvaluation (γ t).val
      (markPosition hn (γ t).2.1 (Sum.inr (visitTransport (path_crossing_iff hn γ 0 t) v)))
    simp only [markPosition_evaluation_visit]
    exact continuous_path_crossingPoint hn γ v.1

theorem transportedCornerPolygon_zero (S : Finset (Crossing (γ 0).val))
    (q : Component hn (γ 0).2 S) :
    (pathTransport hn γ 0 0).transportedCornerPolygon S q = ccpCornerPolygon hn (γ 0).2 S q := by
  funext j
  unfold MarkTransport.transportedCornerPolygon
  rw [pathTransport_toMark_self]
  rfl

theorem ccpCornerPolygon_pathTransport (t : unitInterval) (S : Finset (Crossing (γ 0).val))
    (q : Component hn (γ 0).2 S) :
    ccpCornerPolygon hn (γ t).2 ((pathTransport hn γ 0 t).support S)
        ((pathTransport hn γ 0 t).component S q) =
      recastTuple ((pathTransport hn γ 0 t).ccpCornerCount_transport S q)
        ((pathTransport hn γ 0 t).transportedCornerPolygon S q) :=
  (pathTransport hn γ 0 t).ccpCornerPolygon_transport_of_markList_eq
    (pathTransport_markList_eq hn γ 0 t) S q

theorem regular_transportedCornerPolygon {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) (t : unitInterval) :
    Regular ((pathTransport hn γ 0 t).transportedCornerPolygon S q) := by
  have h := ccpCornerPolygon_regular hn (γ t).2
    (((pathTransport hn γ 0 t).isDecomposition_transport S).mpr hS)
    ((pathTransport hn γ 0 t).component S q)
  rw [ccpCornerPolygon_pathTransport, regular_recastTuple] at h
  exact h

/-- lem:rot (ii) along the path: the rotation of the carrier is constant. -/
theorem carrierRotation_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    carrierRotation hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q) = carrierRotation hn (γ 0).2 S q := by
  unfold carrierRotation
  rw [ccpCornerPolygon_pathTransport, rotationNumber_recastTuple,
    ← transportedCornerPolygon_zero hn γ S q]
  exact rotationNumber_family_constant
    (f := fun t : unitInterval => (pathTransport hn γ 0 t).transportedCornerPolygon S q)
    (continuous_pi (continuous_transportedCornerPolygon hn γ S q))
    (regular_transportedCornerPolygon hn γ hS q) 1 0

/-- (Graft from route A.)  Turn signs of the transported corner polygon are constant along the
path: `turn = sign ∘ det` of consecutive edges, continuous in `t` and nonzero at every `t`
(`ccpCornerPolygon_turn_ne_zero` through `ccpCornerPolygon_pathTransport` and `turn_recastTuple`),
hence constant on the connected `unitInterval`. -/
theorem turn_transportedCornerPolygon_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) (t : unitInterval)
    (j : ZMod (ccpCornerCount hn (γ 0).2 S q)) :
    turn ((pathTransport hn γ 0 t).transportedCornerPolygon S q) j =
      turn (ccpCornerPolygon hn (γ 0).2 S q) j := by
  have hne : ∀ t : unitInterval,
      det (edge ((pathTransport hn γ 0 t).transportedCornerPolygon S q) (j - 1))
        (edge ((pathTransport hn γ 0 t).transportedCornerPolygon S q) j) ≠ 0 := by
    intro t
    have h := ccpCornerPolygon_turn_ne_zero hn (γ t).2
      (((pathTransport hn γ 0 t).isDecomposition_transport S).mpr hS)
      ((pathTransport hn γ 0 t).component S q)
      (Equiv.cast (congrArg ZMod ((pathTransport hn γ 0 t).ccpCornerCount_transport S q).symm) j)
    rw [ccpCornerPolygon_pathTransport, turn_recastTuple_cast, turn_det, sign_ne_zero] at h
    exact h
  have hcont : Continuous fun t : unitInterval =>
      det (edge ((pathTransport hn γ 0 t).transportedCornerPolygon S q) (j - 1))
        (edge ((pathTransport hn γ 0 t).transportedCornerPolygon S q) j) := by
    rw [continuous_iff_continuousAt]
    intro t
    apply continuousAt_det
    · exact ((continuous_transportedCornerPolygon hn γ S q (j - 1 + 1)).sub
        (continuous_transportedCornerPolygon hn γ S q (j - 1))).continuousAt
    · exact ((continuous_transportedCornerPolygon hn γ S q (j + 1)).sub
        (continuous_transportedCornerPolygon hn γ S q j)).continuousAt
  have hsign : Continuous fun t : unitInterval => SignType.sign
      (det (edge ((pathTransport hn γ 0 t).transportedCornerPolygon S q) (j - 1))
        (edge ((pathTransport hn γ 0 t).transportedCornerPolygon S q) j)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (g := SignType.sign) (continuousAt_sign_of_ne_zero (hne t))
      (hcont.continuousAt (x := t))
  rw [turn_det, turn_det, ← transportedCornerPolygon_zero hn γ S q]
  exact PreconnectedSpace.constant inferInstance hsign

theorem uniform_transportedCornerPolygon_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) (t : unitInterval) :
    (∃ σ : SignType, σ ≠ 0 ∧
        ∀ j, turn ((pathTransport hn γ 0 t).transportedCornerPolygon S q) j = σ) ↔
      CarrierUniform hn (γ 0).2 S q := by
  simp only [turn_transportedCornerPolygon_path hn γ hS q t]
  rfl

/-- (Graft from route A.)  The crossing pairs of the transported corner polygon are constant along
the path: locally constant by the accepted `crossing_support_persists_of_geometry` at every
`t` (the corner polygon is on the geometric record domain, `crossingGeometry_of_single_generic`),
pulled back along the continuous family; constant on the connected `unitInterval`. -/
theorem isCrossing_transportedCornerPolygon_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) (t : unitInterval)
    (s : Finset (ZMod (ccpCornerCount hn (γ 0).2 S q))) :
    IsCrossing ((pathTransport hn γ 0 t).transportedCornerPolygon S q) s ↔
      IsCrossing ((pathTransport hn γ 0 0).transportedCornerPolygon S q) s := by
  have hΦ : Continuous fun t : unitInterval => (pathTransport hn γ 0 t).transportedCornerPolygon S q :=
    continuous_pi (continuous_transportedCornerPolygon hn γ S q)
  have hgen : ∀ t₀ : unitInterval, (Shadow.single ⟨_, ccpCornerCount_ge_three hn (γ 0).2 hS q,
      (pathTransport hn γ 0 t₀).transportedCornerPolygon S q⟩).Generic := by
    intro t₀
    have h := carrierShadow_generic hn (γ t₀).2 ((pathTransport hn γ 0 t₀).support S)
      ((pathTransport hn γ 0 t₀).component S q)
      (((pathTransport hn γ 0 t₀).isDecomposition_transport S).mpr hS)
    unfold carrierShadow carrierPolyComp at h
    rw [ccpCornerPolygon_pathTransport hn γ t₀ S q,
      polyComp_recastTuple _ (ccpCornerCount_ge_three hn (γ 0).2 hS q) _ _] at h
    exact h
  have hg : IsLocallyConstant fun t : unitInterval =>
      {s | IsCrossing ((pathTransport hn γ 0 t).transportedCornerPolygon S q) s} := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    have hev := crossing_support_persists_of_geometry
      (crossingGeometry_of_single_generic _ (hgen t₀))
    filter_upwards [hΦ.continuousAt.eventually hev] with t' ht'
    exact Set.ext ht'
  exact Set.ext_iff.mp (IsLocallyConstant.apply_eq_of_preconnectedSpace hg t 0) s

/-! ### 2b. The positive lifts are related by a generic deformation -/

/-- The carrier shadow at time `t` is the carrier shadow at time `0` re-vertexed with the
transported corner polygon (from `ccpCornerPolygon_pathTransport` and `polyComp_recastTuple`). -/
theorem carrierShadow_pathTransport (t : unitInterval) {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    carrierShadow hn (γ t).2 ((pathTransport hn γ 0 t).support S)
        ((pathTransport hn γ 0 t).component S q)
        (((pathTransport hn γ 0 t).isDecomposition_transport S).mpr hS) =
      (carrierShadow hn (γ 0).2 S q hS).withVertices
        (fun _ => (pathTransport hn γ 0 t).transportedCornerPolygon S q) := by
  unfold carrierShadow carrierPolyComp
  rw [ccpCornerPolygon_pathTransport hn γ t S q,
    polyComp_recastTuple _ (ccpCornerCount_ge_three hn (γ 0).2 hS q) _ _]

theorem deform_positiveLift_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    Deform (positiveLift hn (γ 0).2 S q hS)
      (positiveLift hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q)
        (((pathTransport hn γ 0 1).isDecomposition_transport S).mpr hS)) := by
  let D : Diagram := positiveLift hn (γ 0).2 S q hS
  let V : unitInterval → D.Γ.Vertices :=
    fun t _ => (pathTransport hn γ 0 t).transportedCornerPolygon S q
  have hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun t => V t i j :=
    fun _ j => continuous_transportedCornerPolygon hn γ S q j
  have hgen : ∀ t, (D.Γ.withVertices (V t)).Generic := by
    intro t
    have h := carrierShadow_generic hn (γ t).2 ((pathTransport hn γ 0 t).support S)
      ((pathTransport hn γ 0 t).component S q)
      (((pathTransport hn γ 0 t).isDecomposition_transport S).mpr hS)
    rw [carrierShadow_pathTransport hn γ t hS q] at h
    exact h
  have hcross : ∀ t (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V t)).IsCrossing x ↔ D.Γ.IsCrossing x := by
    intro t x
    exact single_isCrossing_iff_of_forall (ccpCornerCount_ge_three hn (γ 0).2 hS q)
      (fun s => (isCrossing_transportedCornerPolygon_path hn γ hS q t s).trans
        (by rw [transportedCornerPolygon_zero])) x
  have h0 : V 0 = D.Γ.vertices := funext fun _ => transportedCornerPolygon_zero hn γ S q
  have hd : Deform D (D.deform (V 1) (hgen 1) (hcross 1)) := Deform.of_family D hV hgen hcross h0
  have heq : D.deform (V 1) (hgen 1) (hcross 1) =
      positiveLift hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q)
        (((pathTransport hn γ 0 1).isDecomposition_transport S).mpr hS) :=
    eq_positiveLift_of_isPositive hn (γ 1).2 _ _ _ _ (carrierShadow_pathTransport hn γ 1 hS q).symm
      (D.isPositive_deform_of_family hV hgen hcross h0 (positiveLift_isPositive hn (γ 0).2 S q hS))
  rw [← heq]
  exact hd

theorem homfly_positiveLift_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    homfly (positiveLift hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q)
        (((pathTransport hn γ 0 1).isDecomposition_transport S).mpr hS)) =
      homfly (positiveLift hn (γ 0).2 S q hS) :=
  (homfly_planar (PlanarIsotopic.of_deform (deform_positiveLift_path hn γ hS q))).symm

theorem cornerCoefficient_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    cornerCoefficient hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q)
        (((pathTransport hn γ 0 1).isDecomposition_transport S).mpr hS) =
      cornerCoefficient hn (γ 0).2 S q hS :=
  (pathTransport hn γ 0 1).cornerCoefficient_transport hS q (carrierRotation_path hn γ hS q)
    (homfly_positiveLift_path hn γ hS q)

/-- Constancy of `C` along a labelled path. -/
theorem cornerStateSum_path_constant : cornerStateSum hn P.2 = cornerStateSum hn Q.2 := by
  have h01 : cornerStateSum hn (γ 1).2 = cornerStateSum hn (γ 0).2 :=
    (pathTransport hn γ 0 1).cornerStateSum_transport
      (fun S hS q => uniform_transportedCornerPolygon_path hn γ hS q 1)
      (fun S hS q => cornerCoefficient_path hn γ hS q)
  have h0 : cornerStateSum hn (γ 0).2 = cornerStateSum hn P.2 :=
    congrArg (fun R : GenericTuple n => cornerStateSum hn R.2) γ.source
  have h1 : cornerStateSum hn (γ 1).2 = cornerStateSum hn Q.2 :=
    congrArg (fun R : GenericTuple n => cornerStateSum hn R.2) γ.target
  rw [← h0, ← h1, h01]

end PathTransport

/-! ## 3. Transport along a cyclic relabelling (unit U5) -/

section ShiftTransport

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (a : ZMod n)

/-- The sorted mark list of the relabelled polygon is a rotation of the relabelled sorted mark
list (`sorted_map_cut_rotation`, as for `gaussList_shift_rotation`). -/
theorem markList_shift_rotated :
    (markList hn ((generic_shift a P).mpr hP)).IsRotated
      ((markList hn hP).map (Sum.map (Equiv.addRight (-a)) (visitShiftEquiv a P))) := by
  have hQ : Generic (shift a P) := (generic_shift a P).mpr hP
  have hfb : Function.Bijective
      (Sum.map (Equiv.addRight (-a)) (visitShiftEquiv a P) : Mark P → Mark (shift a P)) :=
    (Equiv.sumCongr (Equiv.addRight (-a)) (visitShiftEquiv a P)).bijective
  symm
  apply sorted_map_cut_rotation (markList hn hP) (markList hn hQ)
    (Sum.map (Equiv.addRight (-a)) (visitShiftEquiv a P)) (markKey hn hP.1) (markKey hn hQ.1)
    n a.val (markKey_injective hn hP) (markKey_injective hn hQ) (markList_sorted hn hP)
    (markList_sorted hn hQ)
  · apply (List.perm_ext_iff_of_nodup ((markList_nodup hn hP).map hfb.1)
      (markList_nodup hn hQ)).mpr
    intro w
    constructor
    · intro _
      exact mem_markList hn hQ w
    · intro _
      obtain ⟨v, rfl⟩ := hfb.2 w
      exact List.mem_map.mpr ⟨v, mem_markList hn hP v, rfl⟩
  · intro x _
    exact ⟨traversalKey_nonneg _, traversalKey_lt_size _⟩
  · intro x _
    have hpos : markPosition hn hQ.1 (Sum.map (Equiv.addRight (-a)) (visitShiftEquiv a P) x) =
        traversalShift a (markPosition hn hP.1 x) := by
      cases x with
      | inl i =>
        show ((i + -a : ZMod n), (⟨0, by norm_num⟩ : Set.Ico (0 : ℝ) 1)) =
          (i - a, ⟨0, by norm_num⟩)
        rw [sub_eq_add_neg]
      | inr v => exact visitPosition_shift hn hP.1 a v
    show traversalKey (markPosition hn hQ.1 _) = _
    rw [hpos, traversalKey_shift]
    rfl

/-- The mark transport of the cyclic relabelling `shift a P`. -/
noncomputable def shiftTransport : MarkTransport hn hP ((generic_shift a P).mpr hP) where
  vert := Equiv.addRight (-a)
  cross := crossingShiftEquiv a P
  visit := visitShiftEquiv a P
  visit_fst := fun _ => rfl
  markList_rotated := markList_shift_rotated hn hP a
  interlaces_iff := interlaces_shift hn hP a
  turn_eq := fun i => by
    show turn (shift a P) (i + -a) = turn P i
    rw [turn_shift, neg_add_cancel_right]

/-- Relabelling does not move points: the transported corner polygon is the corner polygon. -/
theorem transportedCornerPolygon_shift (S : Finset (Crossing P)) (q : Component hn hP S) :
    (shiftTransport hn hP a).transportedCornerPolygon S q = ccpCornerPolygon hn hP S q := by
  funext j
  rw [ccpCornerPolygon_apply]
  show traversalEvaluation (shift a P) (markPosition hn ((generic_shift a P).mpr hP).1
    ((shiftTransport hn hP a).toMark (ccpCornerMark hn hP S q j))) = _
  generalize ccpCornerMark hn hP S q j = m
  cases m with
  | inl i =>
    rw [MarkTransport.toMark_inl, markPosition_evaluation_vertex, markPosition_evaluation_vertex]
    show P (i + -a + a) = P i
    rw [neg_add_cancel_right]
  | inr v =>
    rw [MarkTransport.toMark_inr, markPosition_evaluation_visit, markPosition_evaluation_visit]
    exact crossingPoint_shift hn hP.1 a v.1

theorem uniform_transportedCornerPolygon_shift (S : Finset (Crossing P)) (q : Component hn hP S) :
    (∃ σ : SignType, σ ≠ 0 ∧
        ∀ j, turn ((shiftTransport hn hP a).transportedCornerPolygon S q) j = σ) ↔
      CarrierUniform hn hP S q := by
  rw [transportedCornerPolygon_shift]
  rfl

theorem carrierRotation_shift (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierRotation hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
        ((shiftTransport hn hP a).component S q) = carrierRotation hn hP S q := by
  unfold carrierRotation
  obtain ⟨r, hr⟩ := (shiftTransport hn hP a).exists_ccpCornerPolygon_transport S q
  rw [hr, rotationNumber_recastTuple, rotationNumber_shift, transportedCornerPolygon_shift]

theorem reparam_positiveLift_shift {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    Reparam (positiveLift hn hP S q hS)
      (positiveLift hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
        ((shiftTransport hn hP a).component S q)
        (((shiftTransport hn hP a).isDecomposition_transport S).mpr hS)) := by
  obtain ⟨r, hr⟩ := (shiftTransport hn hP a).exists_ccpCornerPolygon_transport S q
  rw [transportedCornerPolygon_shift] at hr
  have hsh : carrierShadow hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
      ((shiftTransport hn hP a).component S q)
      (((shiftTransport hn hP a).isDecomposition_transport S).mpr hS) =
      Shadow.single ⟨ccpCornerCount hn hP S q, ccpCornerCount_ge_three hn hP hS q,
        shift r (ccpCornerPolygon hn hP S q)⟩ := by
    show Shadow.single (PolyComp.mk _ _ (ccpCornerPolygon hn ((generic_shift a P).mpr hP)
      ((shiftTransport hn hP a).support S) ((shiftTransport hn hP a).component S q))) = _
    rw [hr, polyComp_recastTuple _ (ccpCornerCount_ge_three hn hP hS q)]
  have hgen' : (Shadow.single ⟨ccpCornerCount hn hP S q, ccpCornerCount_ge_three hn hP hS q,
      shift r (ccpCornerPolygon hn hP S q)⟩).Generic := by
    rw [← hsh]
    exact carrierShadow_generic hn ((generic_shift a P).mpr hP) _ _ _
  unfold positiveLift
  rw [positiveDiagram_congr hsh (carrierShadow_generic hn ((generic_shift a P).mpr hP) _ _ _) hgen']
  exact reparam_positiveDiagram_single_shift (carrierPolyComp hn hP S q hS) r
    (carrierShadow_generic hn hP S q hS) hgen'

theorem homfly_positiveLift_shift {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    homfly (positiveLift hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
        ((shiftTransport hn hP a).component S q)
        (((shiftTransport hn hP a).isDecomposition_transport S).mpr hS)) =
      homfly (positiveLift hn hP S q hS) :=
  (homfly_planar (PlanarIsotopic.of_reparam (reparam_positiveLift_shift hn hP a hS q))).symm

theorem cornerCoefficient_shift {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    cornerCoefficient hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
        ((shiftTransport hn hP a).component S q)
        (((shiftTransport hn hP a).isDecomposition_transport S).mpr hS) =
      cornerCoefficient hn hP S q hS :=
  (shiftTransport hn hP a).cornerCoefficient_transport hS q (carrierRotation_shift hn hP a S q)
    (homfly_positiveLift_shift hn hP a hS q)

/-- "Cyclically shifting the vertex labels preserves `C`." -/
theorem cornerStateSum_shift :
    cornerStateSum hn ((generic_shift a P).mpr hP) = cornerStateSum hn hP :=
  (shiftTransport hn hP a).cornerStateSum_transport
    (fun S _ q => uniform_transportedCornerPolygon_shift hn hP a S q)
    (fun _ hS q => cornerCoefficient_shift hn hP a hS q)

end ShiftTransport

end Carrier

/-! ## 4. Descent to the cyclic quotient and the theorem (closed) -/

variable {n : ℕ} [NeZero n]

theorem cornerStateSum_genericShift (hn : 3 ≤ n) (a : ZMod n) (P : GenericTuple n) :
    cornerStateSum hn (genericShift a P).2 = cornerStateSum hn P.2 :=
  Carrier.cornerStateSum_shift hn P.2 a

theorem cornerStateSum_eq_of_mem_labelledChamber (hn : 3 ≤ n) {P Q : GenericTuple n}
    (hQ : Q ∈ labelledChamber P) : cornerStateSum hn P.2 = cornerStateSum hn Q.2 := by
  obtain ⟨γ⟩ := ((labelledChambers_open_pathConnected hn P).2.joinedIn P mem_connectedComponent
    Q hQ).joined
  exact Carrier.cornerStateSum_path_constant hn γ

/-- prop:C-chamber as printed: "The state sum `C` of Definition def:C is constant on every chamber." -/
structure CChamberData : Prop where
  constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    polygonProjection Q ∈ chamber (polygonProjection P) →
    cornerStateSum hn P.2 = cornerStateSum hn Q.2

theorem prop_C_chamber : CChamberData where
  constant := by
    intro n _ hn P Q hQ
    rw [← projection_labelledChamber_eq_chamber hn P] at hQ
    obtain ⟨Q', hQ', hproj⟩ := hQ
    obtain ⟨a, rfl⟩ := (projection_eq_iff Q' Q).mp hproj
    rw [cornerStateSum_genericShift hn a Q']
    exact cornerStateSum_eq_of_mem_labelledChamber hn hQ'

end SM
