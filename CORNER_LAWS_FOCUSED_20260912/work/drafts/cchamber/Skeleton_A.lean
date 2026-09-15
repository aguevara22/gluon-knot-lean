import SM.CornerStateSum
import SM.Chambers
import SM.ChamberPaths
import SM.CrossingTransport
import SM.GeometricRecords
import SM.GeometricInterlacement
import SM.FlatCarriersDefs
import SM.RotationContinuity
import SM.GaussRelabel
import SM.InterlaceRelabel
import SM.LinkMoves
import SM.GeometricCrossingStability
import SM.GeometricOrderStability
import Mathlib.Topology.LocallyConstant.Basic

/-! # Skeleton A for prop:C-chamber (work/drafts/CChamber_statement.lean)

Plan: work/drafts/cchamber/PLAN_A.md.  Every lemma of the chain is stated with `sorry`;
`SM.C_chamber` at the end is PROVED from the chain.

Route (tag A, "maximal reuse of the geometric-records transport machinery"):
0. `TupleAgree`: index-free comparison of labelled tuples of propositionally equal size
   (needed because `ccpCornerCount` depends on the polygon).
1. `MarkEquiv hn hP hQ`: a bijection of crossings/visits/vertex labels of two generic polygons
   carrying the marked traversal circle `markCycle` to the marked traversal circle (as a `Cycle`,
   i.e. up to the cut) and independence to independence.  From it, purely combinatorially:
   `smoothingSuccessor` commutes, carriers correspond (`component`), corner cycles and retained
   crossings correspond, and the corner polygon of the transported carrier agrees with a cyclic
   shift of the *transported corner tuple* `E.cornerTuple S q` (the corners of the old carrier
   evaluated in the new polygon).
2. Shift invariance of the four invariants of a corner polygon (rotation, uniform turn sign,
   genericity of its one-component shadow, `homfly` of its positive diagram — the last via
   `Reparam`).
3. Assembly: `cornerStateSum hn hQ = cornerStateSum hn hP` for any `MarkEquiv` whose transported
   corner tuples have the right rotation, uniformity and `homfly`.
4. Paths: `markTransport hs` (accepted, SM.FlatCarriersDefs) is a `MarkEquiv` when the crossing
   sets agree and the same-edge parameter orders agree (`CrossingParameterOrderAgrees`, accepted
   SM.GeometricTransport) — both constant along a path in `GenericTuple n` by `SM.chambers`;
   the transported corner tuple moves continuously, stays regular (rotation constant by
   `rotationNumber_family_constant`), its turn signs are constant, and the positive diagrams
   along the way are a `Deform`, so `homfly` is constant (`homfly_planar`).
5. Cyclic shift: `crossingShiftEquiv`/`visitShiftEquiv` (accepted) give a `MarkEquiv` (the marked
   circle is rotated: `sorted_map_cut_rotation`), with the transported corner tuple literally the
   old corner polygon.
6. Descent: `C` is locally constant on `GenericTuple n` (labelled chambers are open and path
   connected) and cyclically invariant, hence descends to a locally constant function on the
   quotient, constant on connected components. -/

namespace SM

open Carrier Link Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-! ## 0. Index-free agreement of labelled tuples -/

/-- `T : LabelledTuple k` and `T' : LabelledTuple k'` agree: `k = k'` and the `j`-th vertices
coincide for every natural index `j`. -/
def TupleAgree {k k' : ℕ} (T : LabelledTuple k) (T' : LabelledTuple k') : Prop :=
  k = k' ∧ ∀ j : ℕ, T (j : ZMod k) = T' (j : ZMod k')

theorem TupleAgree.refl {k : ℕ} (T : LabelledTuple k) : TupleAgree T T := ⟨rfl, fun _ => rfl⟩

theorem TupleAgree.eq {k : ℕ} [NeZero k] {T T' : LabelledTuple k} (h : TupleAgree T T') :
    T = T' := by
  sorry

theorem TupleAgree.rotationNumber_eq {k k' : ℕ} [NeZero k] [NeZero k'] {T : LabelledTuple k}
    {T' : LabelledTuple k'} (h : TupleAgree T T') : rotationNumber T = rotationNumber T' := by
  sorry

theorem TupleAgree.regular_iff {k k' : ℕ} [NeZero k] [NeZero k'] {T : LabelledTuple k}
    {T' : LabelledTuple k'} (h : TupleAgree T T') : Regular T ↔ Regular T' := by
  sorry

theorem TupleAgree.uniform_iff {k k' : ℕ} [NeZero k] [NeZero k'] {T : LabelledTuple k}
    {T' : LabelledTuple k'} (h : TupleAgree T T') :
    (∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn T j = τ) ↔ (∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn T' j = τ) := by
  sorry

theorem TupleAgree.polyComp_eq {k k' : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k') {T : LabelledTuple k}
    {T' : LabelledTuple k'} (h : TupleAgree T T') :
    (⟨k, hk, T⟩ : PolyComp) = ⟨k', hk', T'⟩ := by
  sorry

/-! ## 1. Mark equivalences: the "same combinatorics" predicate -/

/-- A bijection of the crossings, visits and vertex labels of two generic polygons carrying the
marked traversal circle of `P` (as a cycle, i.e. up to the cut at label zero) onto that of `Q`,
and independent supports to independent supports. -/
structure MarkEquiv (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P) (hQ : Generic Q) where
  ec : Crossing P ≃ Crossing Q
  ev : Visit P ≃ Visit Q
  ev_fst : ∀ v, (ev v).1 = ec v.1
  eV : ZMod n ≃ ZMod n
  cycle : (markCycle hn hP).map (Equiv.sumCongr eV ev) = markCycle hn hQ
  indep : ∀ S : Finset (Crossing P),
    IsDecomposition hn hQ (S.map ec.toEmbedding) ↔ IsDecomposition hn hP S

namespace MarkEquiv

variable {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
  (E : MarkEquiv hn hP hQ)

/-- The induced bijection of marks. -/
def e : Mark P ≃ Mark Q := Equiv.sumCongr E.eV E.ev

/-- The support `S` read on `Q`. -/
def support (S : Finset (Crossing P)) : Finset (Crossing Q) := S.map E.ec.toEmbedding

theorem e_inl (i : ZMod n) : E.e (Sum.inl i) = Sum.inl (E.eV i) := rfl

theorem e_inr (v : Visit P) : E.e (Sum.inr v) = Sum.inr (E.ev v) := rfl

theorem mem_support (S : Finset (Crossing P)) (c : Crossing P) :
    E.ec c ∈ E.support S ↔ c ∈ S :=
  Finset.mem_map' _

theorem card_support (S : Finset (Crossing P)) : (E.support S).card = S.card :=
  Finset.card_map _

theorem decomposition {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) :
    IsDecomposition hn hQ (E.support S) :=
  (E.indep S).mpr hS

/-- Twins correspond (the twin is the unique other visit of the same crossing). -/
theorem ev_twin (v : Visit P) : E.ev (visitTwin v) = visitTwin (E.ev v) := by
  sorry

theorem selectedMarkPerm_comm (S : Finset (Crossing P)) (a : Mark P) :
    E.e (selectedMarkPerm S a) = selectedMarkPerm (E.support S) (E.e a) := by
  sorry

/-- `Cycle.next` commutes with an injective map of cycles. -/
theorem cycle_next_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (s : Cycle α) (hs : s.Nodup) (hs' : (s.map f).Nodup)
    (a : α) (ha : a ∈ s) (ha' : f a ∈ s.map f) :
    (s.map f).next hs' (f a) ha' = f (s.next hs a ha) := by
  sorry

/-- The successor `ρ` commutes with the mark bijection. -/
theorem succ (a : Mark P) : E.e (markSuccessor hn hP a) = markSuccessor hn hQ (E.e a) := by
  sorry

theorem smoothingSuccessor_comm (S : Finset (Crossing P)) (a : Mark P) :
    E.e (smoothingSuccessor hn hP S a) = smoothingSuccessor hn hQ (E.support S) (E.e a) := by
  sorry

theorem smoothingSuccessor_eq (S : Finset (Crossing P)) :
    smoothingSuccessor hn hQ (E.support S) = E.e.permCongr (smoothingSuccessor hn hP S) := by
  sorry

theorem sameCycle_iff (S : Finset (Crossing P)) (a b : Mark P) :
    (smoothingSuccessor hn hP S).SameCycle a b ↔
      (smoothingSuccessor hn hQ (E.support S)).SameCycle (E.e a) (E.e b) := by
  sorry

/-- The carriers of `S` on `P` are the carriers of `E.support S` on `Q`. -/
def component (S : Finset (Crossing P)) : Component hn hP S ≃ Component hn hQ (E.support S) :=
  Quotient.congr E.e (E.sameCycle_iff S)

theorem component_owner (S : Finset (Crossing P)) (a : Mark P) :
    E.component S (owner hn hP S a) = owner hn hQ (E.support S) (E.e a) := rfl

theorem isTrueCorner_iff (S : Finset (Crossing P)) (a : Mark P) :
    IsTrueCorner (E.support S) (E.e a) ↔ IsTrueCorner S a := by
  sorry

theorem componentCycle_map (S : Finset (Crossing P)) (q : Component hn hP S) :
    (componentCycle hn hP S q).map E.e = componentCycle hn hQ (E.support S) (E.component S q) := by
  sorry

theorem componentCornerCycle_map (S : Finset (Crossing P)) (q : Component hn hP S) :
    (componentCornerCycle hn hP S q).map E.e =
      componentCornerCycle hn hQ (E.support S) (E.component S q) := by
  sorry

/-- The corner list of the transported carrier is a rotation of the transported corner list. -/
theorem ccpCornerList_rotated (S : Finset (Crossing P)) (q : Component hn hP S) :
    ((ccpCornerList hn hP S q).map E.e).IsRotated
      (ccpCornerList hn hQ (E.support S) (E.component S q)) := by
  sorry

theorem ccpCornerCount_eq (S : Finset (Crossing P)) (q : Component hn hP S) :
    ccpCornerCount hn hQ (E.support S) (E.component S q) = ccpCornerCount hn hP S q := by
  sorry

/-- The corners of the carrier `q` of `P`, transported to `Q` and evaluated there. -/
def cornerTuple (S : Finset (Crossing P)) (q : Component hn hP S) :
    LabelledTuple (ccpCornerCount hn hP S q) :=
  fun j => traversalEvaluation Q (markPosition hn hQ.1 (E.e (ccpCornerMark hn hP S q j)))

/-- The corner polygon of the transported carrier is a cyclic shift of the transported corner
tuple. -/
theorem cornerPolygon_agree (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ m : ZMod (ccpCornerCount hn hP S q),
      TupleAgree (ccpCornerPolygon hn hQ (E.support S) (E.component S q))
        (shift m (E.cornerTuple S q)) := by
  sorry

theorem carrierCrossings_map (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossings hn hQ (E.support S) (E.component S q) =
      (carrierCrossings hn hP S q).map E.ec.toEmbedding := by
  sorry

theorem carrierCrossingCount_eq (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossingCount hn hQ (E.support S) (E.component S q) = carrierCrossingCount hn hP S q := by
  sorry

end MarkEquiv

/-! ## 2. Shift invariance of the invariants of a corner polygon -/

theorem uniformTurns_shift {k : ℕ} [NeZero k] (m : ZMod k) (T : LabelledTuple k) :
    (∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn (shift m T) j = τ) ↔
      (∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn T j = τ) := by
  sorry

/-- Genericity of a one-component shadow is invariant under cyclic relabelling of the polygon. -/
theorem single_generic_shift {k : ℕ} (hk : 3 ≤ k) (m : ZMod k) (T : LabelledTuple k) :
    (Shadow.single ⟨k, hk, shift m T⟩).Generic ↔ (Shadow.single ⟨k, hk, T⟩).Generic := by
  sorry

theorem homfly_positiveDiagram_congr {Γ Γ' : Shadow} (h : Γ = Γ') (hΓ : Γ.Generic)
    (hΓ' : Γ'.Generic) : homfly (Γ.positiveDiagram hΓ) = homfly (Γ'.positiveDiagram hΓ') := by
  subst h
  rfl

/-- The positive diagram of a cyclically relabelled polygon is a reparametrization of the positive
diagram of the polygon (`Reparam`, through a `StrandMap` with `f = id`, `sgn = 1`), so the two
HOMFLY-PT polynomials agree (`homfly_planar`). -/
theorem homfly_positiveDiagram_shift {k : ℕ} (hk : 3 ≤ k) (m : ZMod k) (T : LabelledTuple k)
    (h₁ : (Shadow.single ⟨k, hk, shift m T⟩).Generic) (h₂ : (Shadow.single ⟨k, hk, T⟩).Generic) :
    homfly ((Shadow.single ⟨k, hk, shift m T⟩).positiveDiagram h₁) =
      homfly ((Shadow.single ⟨k, hk, T⟩).positiveDiagram h₂) := by
  sorry

/-- A polygon whose one-component shadow is generic lies on the geometric record domain. -/
theorem crossingGeometry_of_single_generic {k : ℕ} (hk : 3 ≤ k) {T : LabelledTuple k}
    (h : (Shadow.single ⟨k, hk, T⟩).Generic) : CrossingGeometry T := by
  sorry

/-! ## 2'. Invariants of the transported carrier in terms of the transported corner tuple -/

namespace MarkEquiv

variable {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
  (E : MarkEquiv hn hP hQ)

theorem carrierRotation_eq (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    carrierRotation hn hQ (E.support S) (E.component S q) = rotationNumber (E.cornerTuple S q) := by
  sorry

theorem carrierUniform_iff (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    CarrierUniform hn hQ (E.support S) (E.component S q) ↔
      ∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn (E.cornerTuple S q) j = τ := by
  sorry

theorem cornerTuple_generic (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    (Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).Generic := by
  sorry

theorem cornerHomfly_eq (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    cornerHomfly hn hQ (E.support S) (E.component S q) (E.decomposition hS) =
      homfly ((Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).positiveDiagram
        (E.cornerTuple_generic S hS q)) := by
  sorry

/-! ## 3. Assembly: the state sum under a mark equivalence -/

theorem cornerSlot_eq (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hrot : rotationNumber (E.cornerTuple S q) = carrierRotation hn hP S q) :
    cornerSlot hn hQ (E.support S) (E.component S q) = cornerSlot hn hP S q := by
  sorry

theorem cornerCoefficient_eq (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hrot : rotationNumber (E.cornerTuple S q) = carrierRotation hn hP S q)
    (hhom : ∀ h : (Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).Generic,
      homfly ((Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).positiveDiagram h) =
        cornerHomfly hn hP S q hS) :
    cornerCoefficient hn hQ (E.support S) (E.component S q) (E.decomposition hS) =
      cornerCoefficient hn hP S q hS := by
  sorry

theorem cornerProduct_eq (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (hrot : ∀ q, rotationNumber (E.cornerTuple S q) = carrierRotation hn hP S q)
    (hhom : ∀ q (h : (Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).Generic),
      homfly ((Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).positiveDiagram h) =
        cornerHomfly hn hP S q hS) :
    cornerProduct hn hQ (E.support S) (E.decomposition hS) = cornerProduct hn hP S hS := by
  sorry

theorem uniformDecomposition_iff (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S)
    (huni : ∀ q, (∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn (E.cornerTuple S q) j = τ) ↔
      CarrierUniform hn hP S q) :
    UniformDecomposition hn hQ (E.support S) ↔ UniformDecomposition hn hP S := by
  sorry

theorem uniformDecompositions_eq
    (huni : ∀ S (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      (∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn (E.cornerTuple S q) j = τ) ↔ CarrierUniform hn hP S q) :
    uniformDecompositions hn hQ =
      (uniformDecompositions hn hP).map (Finset.mapEmbedding E.ec.toEmbedding).toEmbedding := by
  sorry

end MarkEquiv

/-- **Assembly.** Under a mark equivalence whose transported corner tuples have the rotation,
uniformity and HOMFLY-PT polynomial of the original carriers, the corner state sums agree. -/
theorem cornerStateSum_eq_of_markEquiv (hn : 3 ≤ n) {P Q : LabelledTuple n} {hP : Generic P}
    {hQ : Generic Q} (E : MarkEquiv hn hP hQ) (hL : leftTurns Q = leftTurns P)
    (hrot : ∀ S (_ : IsDecomposition hn hP S) (q : Component hn hP S),
      rotationNumber (E.cornerTuple S q) = carrierRotation hn hP S q)
    (huni : ∀ S (_ : IsDecomposition hn hP S) (q : Component hn hP S),
      (∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn (E.cornerTuple S q) j = τ) ↔ CarrierUniform hn hP S q)
    (hhom : ∀ S (hS : IsDecomposition hn hP S) (q : Component hn hP S)
      (h : (Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).Generic),
      homfly ((Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).positiveDiagram h) =
        cornerHomfly hn hP S q hS) :
    cornerStateSum hn hQ = cornerStateSum hn hP := by
  sorry

/-! ## 4. Paths of labelled generic polygons -/

section Transport

variable (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P) (hQ : Generic Q)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q)
include ho

/-- `markTransport` preserves the order of the marks along the traversal circle (vertices by
label, visits by `geometric_visitKey_lt_transport`). -/
theorem markTransport_key_lt_iff (a b : Mark P) :
    markKey hn hP.1 a < markKey hn hP.1 b ↔
      markKey hn hQ.1 (markTransport hs a) < markKey hn hQ.1 (markTransport hs b) := by
  sorry

/-- The sorted marked circles correspond mark by mark (`List.Perm.eq_of_pairwise`). -/
theorem markList_transport : (markList hn hP).map (markTransport hs) = markList hn hQ := by
  sorry

/-- Independence transports (`geometric_interlaces_transport`, `geometricInterlaces_iff_generic`). -/
theorem isDecomposition_transport (S : Finset (Crossing P)) :
    IsDecomposition hn hQ (transportSupport hs S) ↔ IsDecomposition hn hP S := by
  sorry

/-- The accepted `markTransport` as a mark equivalence. -/
def transportMarkEquiv : MarkEquiv hn hP hQ where
  ec := crossingTransport hs
  ev := visitTransport hs
  ev_fst := fun _ => rfl
  eV := Equiv.refl _
  cycle := by
    sorry
  indep := isDecomposition_transport hn hP hQ hs ho

theorem transportMarkEquiv_e : (transportMarkEquiv hn hP hQ hs ho).e = markTransport hs := rfl

theorem transportMarkEquiv_support (S : Finset (Crossing P)) :
    (transportMarkEquiv hn hP hQ hs ho).support S = transportSupport hs S := rfl

end Transport

/-- `markTransport` between a polygon and itself is the identity. -/
theorem markTransport_self {P : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing P s)
    (a : Mark P) : markTransport hs a = a := by
  sorry

section Family

variable (hn : 3 ≤ n) {F : unitInterval → GenericTuple n} (hF : Continuous F)
include hn hF

omit [NeZero n] in
theorem family_crossing_iff (t : unitInterval) (s : Finset (ZMod n)) :
    IsCrossing (F 0).1 s ↔ IsCrossing (F t).1 s :=
  generic_family_crossing_constant hn hF 0 t s

omit [NeZero n] in
theorem family_order_agrees (t : unitInterval) : CrossingParameterOrderAgrees (F 0).1 (F t).1 := by
  intro i j k hij hik
  exact generic_family_crossingOrder_constant hn hF 0 i j k hij hik t 0

/-- The mark equivalence from the base point `F 0` of a continuous family to `F t`. -/
def familyMarkEquiv (t : unitInterval) : MarkEquiv hn (F 0).2 (F t).2 :=
  transportMarkEquiv hn (F 0).2 (F t).2 (family_crossing_iff hn hF t) (family_order_agrees hn hF t)

/-- The corners of the carrier `q` of `F 0`, followed along the family. -/
def cornerFamily (S : Finset (Crossing (F 0).1)) (q : Component hn (F 0).2 S) (t : unitInterval) :
    LabelledTuple (ccpCornerCount hn (F 0).2 S q) :=
  (familyMarkEquiv hn hF t).cornerTuple S q

variable (S : Finset (Crossing (F 0).1)) (q : Component hn (F 0).2 S)

/-- Each corner moves continuously: original vertices by continuity of the vertex maps, crossing
points by `generic_family_edgeParameter_continuous` (Cramer). -/
theorem cornerFamily_continuous : Continuous (cornerFamily hn hF S q) := by
  sorry

theorem cornerFamily_zero : cornerFamily hn hF S q 0 = ccpCornerPolygon hn (F 0).2 S q := by
  sorry

variable (hS : IsDecomposition hn (F 0).2 S)
include hS

theorem cornerFamily_regular (t : unitInterval) : Regular (cornerFamily hn hF S q t) := by
  sorry

/-- lem:rot (ii) along the family of regular corner polygons. -/
theorem cornerFamily_rotation (t : unitInterval) :
    rotationNumber (cornerFamily hn hF S q t) = carrierRotation hn (F 0).2 S q := by
  sorry

/-- Turn signs are constant along the family (continuous nonzero determinants). -/
theorem cornerFamily_turn (t : unitInterval) (j : ZMod (ccpCornerCount hn (F 0).2 S q)) :
    turn (cornerFamily hn hF S q t) j = turn (ccpCornerPolygon hn (F 0).2 S q) j := by
  sorry

theorem cornerFamily_uniform_iff (t : unitInterval) :
    (∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn (cornerFamily hn hF S q t) j = τ) ↔
      CarrierUniform hn (F 0).2 S q := by
  sorry

theorem cornerFamily_generic (t : unitInterval) :
    (Shadow.single ⟨_, ccpCornerCount_ge_three hn (F 0).2 hS q, cornerFamily hn hF S q t⟩).Generic := by
  sorry

/-- The crossing pairs of the corner polygon are constant along the family (locally constant by
`crossing_support_persists_of_geometry`, `unitInterval` connected). -/
theorem cornerFamily_isCrossing_iff (t : unitInterval) (s : Finset (ZMod (ccpCornerCount hn (F 0).2 S q))) :
    IsCrossing (cornerFamily hn hF S q t) s ↔ IsCrossing (cornerFamily hn hF S q 0) s := by
  sorry

/-- At a retained crossing the determinant of the two edge directions keeps its sign. -/
theorem cornerFamily_det_sign (t : unitInterval) (a b : ZMod (ccpCornerCount hn (F 0).2 S q))
    (hab : IsCrossing (cornerFamily hn hF S q 0) {a, b}) :
    SignType.sign (det (edge (cornerFamily hn hF S q t) a) (edge (cornerFamily hn hF S q t) b)) =
      SignType.sign (det (edge (cornerFamily hn hF S q 0) a) (edge (cornerFamily hn hF S q 0) b)) := by
  sorry

/-- The positive diagrams along the family are related by a generic deformation (`DeformData`
with the path `r ↦ cornerFamily (r t)`, the over data kept, positivity preserved). -/
theorem cornerFamily_deform (t : unitInterval) :
    Deform
      ((Shadow.single ⟨_, ccpCornerCount_ge_three hn (F 0).2 hS q, cornerFamily hn hF S q 0⟩).positiveDiagram
        (cornerFamily_generic hn hF S q hS 0))
      ((Shadow.single ⟨_, ccpCornerCount_ge_three hn (F 0).2 hS q, cornerFamily hn hF S q t⟩).positiveDiagram
        (cornerFamily_generic hn hF S q hS t)) := by
  sorry

theorem cornerFamily_homfly (t : unitInterval)
    (h : (Shadow.single ⟨_, ccpCornerCount_ge_three hn (F 0).2 hS q, cornerFamily hn hF S q t⟩).Generic) :
    homfly ((Shadow.single ⟨_, ccpCornerCount_ge_three hn (F 0).2 hS q, cornerFamily hn hF S q t⟩).positiveDiagram h) =
      cornerHomfly hn (F 0).2 S q hS := by
  sorry

omit hS

/-- `ℓ(P)` is constant along the family (`chi` constant, `SM.chambers`). -/
theorem family_leftTurns (t : unitInterval) : leftTurns (F t).1 = leftTurns (F 0).1 := by
  sorry

/-- Constancy of `C` along a continuous family of labelled generic polygons. -/
theorem cornerStateSum_family (t : unitInterval) :
    cornerStateSum hn (F t).2 = cornerStateSum hn (F 0).2 := by
  sorry

end Family

/-- Constancy of `C` along a path of labelled generic polygons. -/
theorem cornerStateSum_path (hn : 3 ≤ n) {P Q : GenericTuple n} (γ : Path P Q) :
    cornerStateSum hn P.2 = cornerStateSum hn Q.2 := by
  sorry

/-! ## 5. Cyclic relabelling -/

section Shift

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (a : ZMod n)

/-- The mark bijection of the cyclic shift: vertex `i ↦ i - a`, visits by `visitShiftEquiv`. -/
def shiftMark : Mark P ≃ Mark (shift a P) :=
  Equiv.sumCongr (Equiv.subRight a) (visitShiftEquiv a P)

theorem markPosition_shiftMark (m : Mark P) :
    markPosition hn ((generic_shift a P).mpr hP).1 (shiftMark a m) =
      traversalShift a (markPosition hn hP.1 m) := by
  sorry

/-- The marked circle of the shifted polygon is the shifted marked circle, cut elsewhere
(`sorted_map_cut_rotation`). -/
theorem markList_shift_rotated :
    ((markList hn hP).map (shiftMark a)).IsRotated (markList hn ((generic_shift a P).mpr hP)) := by
  sorry

/-- The cyclic shift as a mark equivalence. -/
def shiftMarkEquiv : MarkEquiv hn hP ((generic_shift a P).mpr hP) where
  ec := crossingShiftEquiv a P
  ev := visitShiftEquiv a P
  ev_fst := fun _ => rfl
  eV := Equiv.subRight a
  cycle := by
    sorry
  indep := fun S => independentSupports_shift hn hP a S

theorem shiftMarkEquiv_e : (shiftMarkEquiv hn hP a).e = shiftMark a := rfl

/-- Points do not move under relabelling: the transported corner tuple is the corner polygon. -/
theorem shiftMarkEquiv_cornerTuple (S : Finset (Crossing P)) (q : Component hn hP S) :
    (shiftMarkEquiv hn hP a).cornerTuple S q = ccpCornerPolygon hn hP S q := by
  sorry

/-- Cyclic invariance of `C`. -/
theorem cornerStateSum_shift :
    cornerStateSum hn ((generic_shift a P).mpr hP) = cornerStateSum hn hP := by
  sorry

end Shift

/-! ## 6. Descent to the quotient -/

/-- `C` is locally constant on the labelled generic locus: labelled chambers are open and path
connected (`labelledChambers_open_pathConnected`) and `C` is constant along paths. -/
theorem cornerStateSum_locallyConstant (hn : 3 ≤ n) :
    IsLocallyConstant (fun R : GenericTuple n => cornerStateSum hn R.2) := by
  sorry

theorem cornerStateSum_cyclic (hn : 3 ≤ n) (R R' : GenericTuple n)
    (h : ∃ k : ZMod n, R'.1 = shift k R.1) : cornerStateSum hn R.2 = cornerStateSum hn R'.2 := by
  sorry

/-- `C` on the space of (unlabelled) generic polygons. -/
def polygonStateSum (hn : 3 ≤ n) : GenericPolygon n → ℤ :=
  Quotient.lift (fun R : GenericTuple n => cornerStateSum hn R.2)
    (fun R R' h => cornerStateSum_cyclic hn R R' h)

theorem polygonStateSum_mk (hn : 3 ≤ n) (R : GenericTuple n) :
    polygonStateSum hn (polygonProjection R) = cornerStateSum hn R.2 := rfl

/-- The preimage of a value is an open saturated set, so its image is open in the quotient
(`isQuotientMap_quotient_mk'`). -/
theorem polygonStateSum_locallyConstant (hn : 3 ≤ n) : IsLocallyConstant (polygonStateSum hn) := by
  sorry

/-- prop:C-chamber as printed (verbatim from work/drafts/CChamber_statement.lean): "The state sum
`C` of Definition def:C is constant on every chamber." -/
structure CChamberData : Prop where
  constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    polygonProjection Q ∈ chamber (polygonProjection P) →
    cornerStateSum hn P.2 = cornerStateSum hn Q.2

/-- prop:C-chamber, proved from the chain above. -/
theorem C_chamber : CChamberData where
  constant := fun n _ hn P Q h => by
    have hc := IsLocallyConstant.apply_eq_of_isPreconnected (polygonStateSum_locallyConstant hn)
      isPreconnected_connectedComponent (mem_connectedComponent (x := polygonProjection P)) h
    simpa only [polygonStateSum_mk] using hc

end

end SM
