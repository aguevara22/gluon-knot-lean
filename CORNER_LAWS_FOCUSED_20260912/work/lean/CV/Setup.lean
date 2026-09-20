import SM.CrossingGeometry
import SM.LineConcurrence
import SM.RegularDefinition
import SM.FlatCrossingGeometry
import SM.NamedWallPredicates
import SM.Crossings
import SM.Chambers

/-! CV lane, module CV.Setup: the CV definitions of reference/R/CV/d1_setup.tex — CV:def:polygon (8-19), CV:def:regular (22-40),
CV:def:guarded (42-218: the guarded list of determinants as the indexed type `Member`), CV:def:generic (220-238) and
CV:def:diagrammatic (315-344) — each with a row bundle `CV.<row>Data` and its theorem `CV.<row>_definition`, plus the theorems relating
them to the accepted SM notions (`CV.Regular ↔ SM.Regular`, `SM.Generic → CV.Generic` = Bridge B1(1), `CV.Generic → CrossingGeometry`).
Follows the CV-lane plan (work/reports/cv-lane-plan-20260913.md) and decision F2 (no domain narrowing; recorded in work/AUTHOR_NOTES.md).
Written 2026-09-13 by a Claude Code implementer subagent of the pod executor (workflow implement-cv-definitions), checked with
`lake env lean` (placeholder-free, standard axioms) and ported verbatim from work/drafts/CV_Setup.lean (only this header added and #print lines
removed). -/

/-! # CV lane, setup definitions (reference/R/CV/d1_setup.tex, frozen)

Rows 129–133 of the CV lane: CV:def:polygon (d1_setup.tex:8–19), CV:def:regular (22–40),
CV:def:guarded (42–218), CV:def:generic (220–238), CV:def:diagrammatic (315–344).

Decision F2 (work/AUTHOR_NOTES.md, 2026-09-13): no domain narrowing. Every CV notion below is
stated on CV's own locus exactly as printed, on *labelled tuples* `LabelledTuple n = ZMod n → Plane`
(CV has no cyclic quotient: "a polygon is a tuple", d1_setup.tex:8–11). The relation to the SM
notions is always a theorem (`CV.generic_of_sm : SM.Generic P → CV.Generic P`, etc.), never an
identification.

Row declarations: `CV.polygon_definition : PolygonData`, `CV.regular_definition : RegularData`,
`CV.guarded_definition : GuardedData`, `CV.generic_definition : GenericData`,
`CV.diagrammatic_definition : DiagrammaticData`. Each field of a `…Data` structure is named after
the printed clause it renders. -/

namespace CV

open SM

variable {n : ℕ}

/-! ## Row 129 — CV:def:polygon (d1_setup.tex:8–19) -/

/-- CV def:polygon (d1_setup.tex:8–13): "A *polygon* on `n` vertices is a tuple
`P = (p_1,…,p_n) ∈ (ℝ²)^n` with `p_{i+1} ≠ p_i` for every `i`, indices read cyclically modulo `n`";
stated through the edge directions `d_i = p_{i+1} − p_i ∈ ℝ² ∖ {0}` (line 12–13), `d_i = edge P i`. -/
def IsPolygon (P : LabelledTuple n) : Prop := ∀ i, edge P i ≠ 0

theorem isPolygon_iff (P : LabelledTuple n) : IsPolygon P ↔ ∀ i, P (i + 1) ≠ P i :=
  forall_congr' fun _ => sub_ne_zero

/-- "Two edges are *consecutive* if their index sets meet" (d1_setup.tex:13–14); the index set of
the edge `e_i = [p_i, p_{i+1}]` is `{i, i+1}`. -/
def Consecutive (i j : ZMod n) : Prop := ∃ k, (k = i ∨ k = i + 1) ∧ (k = j ∨ k = j + 1)

/-- "and *remote* otherwise" (d1_setup.tex:14). -/
def Remote (i j : ZMod n) : Prop := ¬ Consecutive i j

/-- "An edge is *remote to a vertex* `p_M` when it is remote to both edges incident to `M`"
(d1_setup.tex:14–18): the edges incident to `M` are `e_{M−1}` and `e_M`. This is "the stronger
of the two possible readings". -/
def RemoteToVertex (M j : ZMod n) : Prop := Remote j (M - 1) ∧ Remote j M

theorem adjacent_iff (i j : ZMod n) : adjacent i j ↔ j = i - 1 ∨ j = i ∨ j = i + 1 := by
  unfold adjacent
  constructor
  · rintro (h | h | h)
    · left; linear_combination h
    · right; left; linear_combination h
    · right; right; linear_combination h
  · rintro (h | h | h)
    · left; linear_combination h
    · right; left; linear_combination h
    · right; right; linear_combination h

theorem consecutive_iff_adjacent (i j : ZMod n) : Consecutive i j ↔ adjacent i j := by
  rw [adjacent_iff]
  constructor
  · rintro ⟨k, (rfl | rfl), (h | h)⟩
    · right; left; exact h.symm
    · left; linear_combination -h
    · right; right; exact h.symm
    · right; left; linear_combination -h
  · rintro (h | h | h)
    · exact ⟨i, Or.inl rfl, Or.inr (by rw [h, sub_add_cancel])⟩
    · exact ⟨i, Or.inl rfl, Or.inl h.symm⟩
    · exact ⟨i + 1, Or.inr rfl, Or.inl h.symm⟩

theorem remote_iff (i j : ZMod n) : Remote i j ↔ remote i j :=
  not_congr (consecutive_iff_adjacent i j)

theorem remoteToVertex_iff (M j : ZMod n) :
    RemoteToVertex M j ↔ remoteToVertexAndEdges M j := by
  unfold RemoteToVertex remoteToVertexAndEdges
  rw [remote_iff, remote_iff, remote, remote, adjacent_iff, adjacent_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; apply h1; right; right; linear_combination -h
    · intro h; apply h1; right; left; exact h.symm
    · intro h; apply h2; right; left; exact h.symm
    · intro h; apply h2; left; linear_combination -h
  · rintro ⟨h2, h1, h0, hp⟩
    constructor
    · rintro (h | h | h)
      · exact h0 (by linear_combination -h)
      · exact h1 h.symm
      · exact h2 (by linear_combination -h)
    · rintro (h | h | h)
      · exact hp (by linear_combination -h)
      · exact h0 h.symm
      · exact h1 (by linear_combination -h)

/-- The stronger reading implies the weaker one: an edge remote to the vertex `p_M` is not incident
to `M` (d1_setup.tex:15–18, "it excludes an edge that merely avoids `p_M` while sharing a vertex
with one of its edges"). -/
theorem RemoteToVertex.not_incident {M j : ZMod n} (h : RemoteToVertex M j) : ¬ incident M j := by
  obtain ⟨_, h1, h0, _⟩ := (remoteToVertex_iff M j).mp h
  rintro (he | he)
  · exact h1 he
  · exact h0 he

theorem edgeSegment_eq_segment (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i = segment ℝ (P i) (P (i + 1)) := by
  rw [segment_eq_image']
  ext x
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨t, h0, h1, rfl⟩

/-- CV def:polygon (d1_setup.tex:8–19), clause by clause. -/
structure PolygonData : Prop where
  /-- "A polygon on `n` vertices is a tuple `P = (p_1,…,p_n) ∈ (ℝ²)^n` with `p_{i+1} ≠ p_i` for
  every `i`" (8–11), `n ≥ 3`. -/
  polygon : ∀ (n : ℕ) (_hn : 3 ≤ n) (P : LabelledTuple n), IsPolygon P ↔ ∀ i, P (i + 1) ≠ P i
  /-- "indices read cyclically modulo `n` throughout" (10–11). -/
  cyclic : ∀ (n : ℕ) (P : LabelledTuple n) (i : ZMod n), P (i + n) = P i
  /-- "Its edges are the closed segments `e_i = [p_i, p_{i+1}]`" (11–12). -/
  edge_segment : ∀ (n : ℕ) (P : LabelledTuple n) (i : ZMod n),
    edgeSegment P i = segment ℝ (P i) (P (i + 1))
  /-- "and its edge directions are `d_i = p_{i+1} − p_i`" (12–13). -/
  edge_direction : ∀ (n : ℕ) (P : LabelledTuple n) (i : ZMod n), edge P i = P (i + 1) - P i
  /-- "`d_i ∈ ℝ² ∖ {0}`" (13). -/
  direction_ne_zero : ∀ (n : ℕ) (P : LabelledTuple n), IsPolygon P → ∀ i, edge P i ≠ 0
  /-- "Two edges are consecutive if their index sets meet" (13–14) — this is SM's `adjacent`. -/
  consecutive : ∀ (n : ℕ) (i j : ZMod n), Consecutive i j ↔ adjacent i j
  /-- "and remote otherwise" (14) — this is SM's `remote`. -/
  remote : ∀ (n : ℕ) (i j : ZMod n), Remote i j ↔ SM.remote i j
  /-- "An edge is remote to a vertex `p_M` when it is remote to both edges incident to `M`"
  (14–15) — SM's `remoteToVertexAndEdges M j`, i.e. `j ∉ {M−2, M−1, M, M+1}`. -/
  remote_to_vertex : ∀ (n : ℕ) (M j : ZMod n), RemoteToVertex M j ↔ remoteToVertexAndEdges M j
  /-- "the stronger of the two possible readings" (15–18): it implies non-incidence. -/
  remote_to_vertex_stronger : ∀ (n : ℕ) (M j : ZMod n), RemoteToVertex M j → ¬ incident M j
  /-- "We write `det(u,v) = u_1 v_2 − u_2 v_1`" (18–19). -/
  det_formula : ∀ u v : Plane, det u v = u.1 * v.2 - u.2 * v.1

theorem polygon_definition : PolygonData where
  polygon := fun _ _ P => isPolygon_iff P
  cyclic := fun _ P i => by simp
  edge_segment := fun _ P i => edgeSegment_eq_segment P i
  edge_direction := fun _ _ _ => rfl
  direction_ne_zero := fun _ _ h => h
  consecutive := fun _ i j => consecutive_iff_adjacent i j
  remote := fun _ i j => remote_iff i j
  remote_to_vertex := fun _ M j => remoteToVertex_iff M j
  remote_to_vertex_stronger := fun _ _ _ h => h.not_incident
  det_formula := fun _ _ => rfl

/-! ## Row 130 — CV:def:regular (d1_setup.tex:22–40) -/

/-- CV def:regular (A) (d1_setup.tex:23–28): for a closed polygon `L` with corners `q_0,…,q_{c−1}`
and edge directions `δ_i = q_{i+1} − q_i`, "the *principal turn* at `q_i` is the unique
`τ_i ∈ (−π,π)` with `cos τ_i = ⟨δ_{i−1},δ_i⟩/(|δ_{i−1}||δ_i|)` and `sgn τ_i = sgn det(δ_{i−1},δ_i)`".
This is the specification `τ` must satisfy (SM's `PrincipalAngleSpec (edge L (i-1)) (edge L i) τ`). -/
def PrincipalTurnSpec {c : ℕ} (L : LabelledTuple c) (i : ZMod c) (τ : ℝ) : Prop :=
  (-Real.pi < τ ∧ τ < Real.pi) ∧
  Real.cos τ = planeDot (edge L (i - 1)) (edge L i) /
    (euclideanLength (edge L (i - 1)) * euclideanLength (edge L i)) ∧
  SignType.sign τ = SignType.sign (det (edge L (i - 1)) (edge L i))

/-- The principal turn `τ_i` itself (the argument of the corner rotor; SM's `principalTurn`). -/
noncomputable def principalTurn {c : ℕ} (L : LabelledTuple c) (i : ZMod c) : ℝ :=
  principalAngle (edge L (i - 1)) (edge L i)

/-- "The excluded case `δ_i ∈ ℝ_{<0} δ_{i−1}` is the *kink*" (d1_setup.tex:30–32). -/
def Kink {c : ℕ} (L : LabelledTuple c) (i : ZMod c) : Prop :=
  ∃ r : ℝ, r < 0 ∧ edge L i = r • edge L (i - 1)

/-- CV def:regular (B) (d1_setup.tex:33–38): "The *regular locus* `𝓡_n ⊆ (ℝ²)^n` is the set of
`P = (p_1,…,p_n)` with `d_i ≠ 0` for all `i` and `d_{i+1} ≠ −λ d_i` for all `i` and all `λ > 0`:
nonzero edges and no consecutive pair that doubles back." -/
def Regular (P : LabelledTuple n) : Prop :=
  (∀ i, edge P i ≠ 0) ∧ ∀ i (l : ℝ), 0 < l → edge P (i + 1) ≠ (-l) • edge P i

/-- `𝓡_n`. -/
def regularLocus (n : ℕ) : Set (LabelledTuple n) := {P | Regular P}

theorem principalTurnSpec_iff {c : ℕ} (L : LabelledTuple c) (i : ZMod c) (τ : ℝ) :
    PrincipalTurnSpec L i τ ↔ PrincipalAngleSpec (edge L (i - 1)) (edge L i) τ := Iff.rfl

theorem principalTurn_eq_sm {c : ℕ} (L : LabelledTuple c) (i : ZMod c) :
    principalTurn L i = SM.principalTurn L i := rfl

theorem principalTurnSpec_unique {c : ℕ} {L : LabelledTuple c} {i : ZMod c} {τ τ' : ℝ}
    (h : PrincipalTurnSpec L i τ) (h' : PrincipalTurnSpec L i τ') : τ = τ' :=
  principalAngleSpec_unique h h'

theorem principalTurn_spec {c : ℕ} {L : LabelledTuple c} {i : ZMod c}
    (h : RegularPair (edge L (i - 1)) (edge L i)) : PrincipalTurnSpec L i (principalTurn L i) :=
  principalAngle_spec h

theorem principalTurnSpec_eq {c : ℕ} {L : LabelledTuple c} {i : ZMod c} {τ : ℝ}
    (h : PrincipalTurnSpec L i τ) : τ = principalTurn L i :=
  SM.principalTurn_unique h

/-- "It exists precisely when `δ_i` is not a negative multiple of `δ_{i−1}`" (28–29), read with
the nonzero edges of a polygon. -/
theorem existsUnique_principalTurn_iff {c : ℕ} (L : LabelledTuple c) (i : ZMod c) :
    (∃! τ, PrincipalTurnSpec L i τ) ↔ edge L (i - 1) ≠ 0 ∧ edge L i ≠ 0 ∧ ¬ Kink L i :=
  principalAngle_existsUnique_iff _ _

/-- "if `det(δ_{i−1},δ_i) ≠ 0` it is nonzero" (29). -/
theorem principalTurn_ne_zero_of_det {c : ℕ} {L : LabelledTuple c} {i : ZMod c}
    (h : RegularPair (edge L (i - 1)) (edge L i)) (hd : det (edge L (i - 1)) (edge L i) ≠ 0) :
    principalTurn L i ≠ 0 := by
  intro hz
  have hs := (principalTurn_spec h).2.2
  rw [hz, sign_zero] at hs
  exact hd (sign_eq_zero_iff.mp hs.symm)

/-- "and if `δ_i` is a positive multiple of `δ_{i−1}` it is `0`" (29–30). -/
theorem principalTurn_eq_zero_of_positive {c : ℕ} {L : LabelledTuple c} {i : ZMod c}
    (hu : edge L (i - 1) ≠ 0) (h : ∃ r : ℝ, 0 < r ∧ edge L i = r • edge L (i - 1)) :
    principalTurn L i = 0 := by
  obtain ⟨r, hr, he⟩ := h
  have hv : edge L i ≠ 0 := by
    rw [he]
    exact smul_ne_zero hr.ne' hu
  exact (principalAngle_eq_zero_iff hu hv).mpr ⟨r, hr, he⟩

/-- At a kink "the two candidate values `±π` are both excluded from the open interval" (31–32):
no principal turn exists. -/
theorem Kink.no_principalTurn {c : ℕ} {L : LabelledTuple c} {i : ZMod c} (hk : Kink L i) :
    ¬ ∃ τ, PrincipalTurnSpec L i τ := by
  rintro ⟨τ, hτ⟩
  exact (regularPair_of_principalAngleSpec hτ).2.2 hk

theorem regular_iff_sm (P : LabelledTuple n) : Regular P ↔ SM.Regular P := by
  rw [regular_iff_edges]
  constructor
  · rintro ⟨hedge, hback⟩ i
    refine ⟨hedge i, ?_⟩
    rintro ⟨r, hr, he⟩
    apply hback (i - 1) (-r) (by linarith)
    rw [sub_add_cancel, neg_neg]
    exact he
  · intro h
    refine ⟨fun i => (h i).1, ?_⟩
    intro i l hl he
    apply (h (i + 1)).2
    refine ⟨-l, by linarith, ?_⟩
    rw [add_sub_cancel_right]
    exact he

/-- "Equivalently, every principal turn of clause (A) exists" (38–39). -/
theorem regular_iff_principalTurns (P : LabelledTuple n) :
    Regular P ↔ ∀ i, ∃! τ, PrincipalTurnSpec P i τ :=
  (regular_iff_sm P).trans (regular_iff_principalTurns_exist P)

/-- CV def:regular (d1_setup.tex:22–40), clause by clause. -/
structure RegularData : Prop where
  /-- (A) the specification of `τ_i`: `τ_i ∈ (−π,π)`, `cos τ_i = ⟨δ_{i−1},δ_i⟩/(|δ_{i−1}||δ_i|)`,
  `sgn τ_i = sgn det(δ_{i−1},δ_i)` (23–28). -/
  principal_turn_spec : ∀ (c : ℕ) (L : LabelledTuple c) (i : ZMod c) (τ : ℝ),
    PrincipalTurnSpec L i τ ↔
      (-Real.pi < τ ∧ τ < Real.pi) ∧
      Real.cos τ = planeDot (edge L (i - 1)) (edge L i) /
        (euclideanLength (edge L (i - 1)) * euclideanLength (edge L i)) ∧
      SignType.sign τ = SignType.sign (det (edge L (i - 1)) (edge L i))
  /-- (A) "the unique `τ_i`": any two solutions coincide (25). -/
  principal_turn_unique : ∀ (c : ℕ) (L : LabelledTuple c) (i : ZMod c) (τ τ' : ℝ),
    PrincipalTurnSpec L i τ → PrincipalTurnSpec L i τ' → τ = τ'
  /-- (A) `principalTurn L i` is that unique value whenever it exists. -/
  principal_turn_value : ∀ (c : ℕ) (L : LabelledTuple c) (i : ZMod c),
    RegularPair (edge L (i - 1)) (edge L i) →
      PrincipalTurnSpec L i (principalTurn L i) ∧
      ∀ τ, PrincipalTurnSpec L i τ → τ = principalTurn L i
  /-- (A) "It exists precisely when `δ_i` is not a negative multiple of `δ_{i−1}`" (28–29). -/
  exists_iff : ∀ (c : ℕ) (L : LabelledTuple c) (i : ZMod c),
    (∃! τ, PrincipalTurnSpec L i τ) ↔ edge L (i - 1) ≠ 0 ∧ edge L i ≠ 0 ∧ ¬ Kink L i
  /-- (A) "if `det(δ_{i−1},δ_i) ≠ 0` it is nonzero" (29). -/
  nonzero_of_det : ∀ (c : ℕ) (L : LabelledTuple c) (i : ZMod c),
    RegularPair (edge L (i - 1)) (edge L i) → det (edge L (i - 1)) (edge L i) ≠ 0 →
      principalTurn L i ≠ 0
  /-- (A) "if `δ_i` is a positive multiple of `δ_{i−1}` it is `0`" (29–30). -/
  zero_of_positive_multiple : ∀ (c : ℕ) (L : LabelledTuple c) (i : ZMod c),
    edge L (i - 1) ≠ 0 → (∃ r : ℝ, 0 < r ∧ edge L i = r • edge L (i - 1)) →
      principalTurn L i = 0
  /-- (A) "The excluded case `δ_i ∈ ℝ_{<0} δ_{i−1}` is the kink, where the two candidate values
  `±π` are both excluded from the open interval" (30–32). -/
  kink : ∀ (c : ℕ) (L : LabelledTuple c) (i : ZMod c),
    (Kink L i ↔ ∃ r : ℝ, r < 0 ∧ edge L i = r • edge L (i - 1)) ∧
    (Kink L i → ¬ ∃ τ, PrincipalTurnSpec L i τ)
  /-- (B) "The regular locus `𝓡_n ⊆ (ℝ²)^n` is the set of `P` with `d_i ≠ 0` for all `i` and
  `d_{i+1} ≠ −λ d_i` for all `i` and all `λ > 0`" (33–37). -/
  regular_locus : ∀ (n : ℕ) (_hn : 3 ≤ n) (P : LabelledTuple n),
    P ∈ regularLocus n ↔
      (∀ i, edge P i ≠ 0) ∧ ∀ i (l : ℝ), 0 < l → edge P (i + 1) ≠ (-l) • edge P i
  /-- (B) "Equivalently, every principal turn of clause (A) exists" (38–39). -/
  regular_iff_turns_exist : ∀ (n : ℕ) (_hn : 3 ≤ n) (P : LabelledTuple n),
    Regular P ↔ ∀ i, ∃! τ, PrincipalTurnSpec P i τ
  /-- The CV regular locus is SM's `Regular` (SM def:regular), as a theorem. -/
  regular_iff_sm : ∀ (n : ℕ) (P : LabelledTuple n), Regular P ↔ SM.Regular P
  /-- The CV principal turn is SM's `principalTurn`. -/
  principal_turn_eq_sm : ∀ (c : ℕ) (L : LabelledTuple c) (i : ZMod c),
    principalTurn L i = SM.principalTurn L i

theorem regular_definition : RegularData where
  principal_turn_spec := fun _ _ _ _ => Iff.rfl
  principal_turn_unique := fun _ _ _ _ _ h h' => principalTurnSpec_unique h h'
  principal_turn_value := fun _ _ _ h =>
    ⟨principalTurn_spec h, fun _ hτ => principalTurnSpec_eq hτ⟩
  exists_iff := fun _ L i => existsUnique_principalTurn_iff L i
  nonzero_of_det := fun _ _ _ h hd => principalTurn_ne_zero_of_det h hd
  zero_of_positive_multiple := fun _ _ _ hu h => principalTurn_eq_zero_of_positive hu h
  kink := fun _ _ _ => ⟨Iff.rfl, fun hk => hk.no_principalTurn⟩
  regular_locus := fun _ _ _ => Iff.rfl
  regular_iff_turns_exist := fun _ _ P => regular_iff_principalTurns P
  regular_iff_sm := fun _ P => regular_iff_sm P
  principal_turn_eq_sm := fun _ _ _ => rfl

/-! ## Row 131 — CV:def:guarded (d1_setup.tex:42–218) -/

/-- "Normalization of cyclic aliases" (d1_setup.tex:132–140): the integer representative in
`{1,…,n}` naming the edge `e_i` (`rep 1 = 1`, `rep 0 = n`). Every comparison `e < f` of the
definition "is a comparison of representatives". -/
def rep [NeZero n] (i : ZMod n) : ℕ := (i - 1).val + 1

theorem rep_injective [NeZero n] : Function.Injective (rep (n := n)) := by
  intro a b h
  have h1 : (a - 1).val = (b - 1).val := Nat.succ_injective h
  exact sub_left_injective (ZMod.val_injective n h1)

theorem rep_pos [NeZero n] (i : ZMod n) : 1 ≤ rep i := Nat.succ_le_succ (Nat.zero_le _)

theorem rep_le [NeZero n] (i : ZMod n) : rep i ≤ n := by
  unfold rep
  have := ZMod.val_lt (i - 1)
  omega

/-- The representative names the same edge. -/
theorem rep_cast [NeZero n] (i : ZMod n) : ((rep i : ℕ) : ZMod n) = i := by
  unfold rep
  push_cast
  rw [ZMod.natCast_zmod_val, sub_add_cancel]

theorem rep_lt_or_lt [NeZero n] {f g : ZMod n} (h : f ≠ g) : rep f < rep g ∨ rep g < rep f := by
  rcases lt_trichotomy (rep f) (rep g) with hlt | heq | hgt
  · exact Or.inl hlt
  · exact (h (rep_injective heq)).elim
  · exact Or.inr hgt

/-- `ℓ_e(x) = det(d_e, x − p_e)`, "the affine form vanishing on the line of `e`"
(d1_setup.tex:45–46). -/
def lineForm (P : LabelledTuple n) (e : ZMod n) (x : Plane) : ℝ := det (edge P e) (x - P e)

/-- The coefficient row `(A_e, B_e, C_e) = (−d_{e,2}, d_{e,1}, d_{e,2} p_{e,1} − d_{e,1} p_{e,2})`
of the line of `e` (d1_setup.tex:46–48). -/
def row (P : LabelledTuple n) (e : ZMod n) : Fin 3 → ℝ :=
  ![-(edge P e).2, (edge P e).1, (edge P e).2 * (P e).1 - (edge P e).1 * (P e).2]

/-- The determinant of a `3 × 3` matrix given by its three rows. -/
def det3 (r s t : Fin 3 → ℝ) : ℝ :=
  r 0 * (s 1 * t 2 - s 2 * t 1) - r 1 * (s 0 * t 2 - s 2 * t 0) + r 2 * (s 0 * t 1 - s 1 * t 0)

/-- (G1) `G1_i = det(d_{i−1}, d_i)` (d1_setup.tex:52). -/
def G1 (P : LabelledTuple n) (i : ZMod n) : ℝ := det (edge P (i - 1)) (edge P i)

/-- (G2) `G2_{e,i} = ℓ_e(p_i) = det(d_e, p_i − p_e)`, for `i ∉ {e, e+1}` (d1_setup.tex:53–54). -/
def G2 (P : LabelledTuple n) (e i : ZMod n) : ℝ := lineForm P e (P i)

/-- (G5) `G5_{e,f} = det(d_e, d_f)` (d1_setup.tex:99). -/
def G5 (P : LabelledTuple n) (e f : ZMod n) : ℝ := det (edge P e) (edge P f)

/-- (G3) `G3_{e,f,g} = det` of the three coefficient rows `(A_e,B_e,C_e)`, `(A_f,B_f,C_f)`,
`(A_g,B_g,C_g)` (d1_setup.tex:113–118). -/
def G3 (P : LabelledTuple n) (e f g : ZMod n) : ℝ := det3 (row P e) (row P f) (row P g)

/-- (G4) `G4_{e;f,g} = det(d_f, p_f − p_e) det(d_g, d_e) − det(d_g, p_g − p_e) det(d_f, d_e)`
(d1_setup.tex:128–129). -/
def G4 (P : LabelledTuple n) (e f g : ZMod n) : ℝ :=
  det (edge P f) (P f - P e) * det (edge P g) (edge P e)
    - det (edge P g) (P g - P e) * det (edge P f) (edge P e)

/-- "the crossing of `e` with `f` sits at the parameter `t_f = det(d_f, p_f − p_e)/det(d_f, d_e)`
along `e`" (d1_setup.tex:184–186). -/
noncomputable def crossParam (P : LabelledTuple n) (e f : ZMod n) : ℝ :=
  det (edge P f) (P f - P e) / det (edge P f) (edge P e)

/-- *Activation* (d1_setup.tex:57–63): "Two remote edges `e, f` are *defined* to cross when
`G2_{e,f} G2_{e,f+1} < 0` and `G2_{f,e} G2_{f,e+1} < 0`", the products strict. -/
def Crosses (P : LabelledTuple n) (e f : ZMod n) : Prop :=
  remote e f ∧ G2 P e f * G2 P e (f + 1) < 0 ∧ G2 P f e * G2 P f (e + 1) < 0

/-! ### Row 131, theorems on the printed polynomials and on activation -/

theorem row_zero (P : LabelledTuple n) (e : ZMod n) : row P e 0 = -(edge P e).2 := rfl
theorem row_one (P : LabelledTuple n) (e : ZMod n) : row P e 1 = (edge P e).1 := rfl
theorem row_two (P : LabelledTuple n) (e : ZMod n) :
    row P e 2 = (edge P e).2 * (P e).1 - (edge P e).1 * (P e).2 := rfl

/-- "so that `ℓ_e(x) = A_e x_1 + B_e x_2 + C_e`" (d1_setup.tex:48). -/
theorem lineForm_eq_row (P : LabelledTuple n) (e : ZMod n) (x : Plane) :
    lineForm P e x = row P e 0 * x.1 + row P e 1 * x.2 + row P e 2 := by
  simp only [lineForm, det, row_zero, row_one, row_two, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `ℓ_e` vanishes on the line of `e` (d1_setup.tex:45–46). -/
theorem lineForm_edgePoint (P : LabelledTuple n) (e : ZMod n) (t : ℝ) :
    lineForm P e (edgePoint P e t) = 0 := det_edge_line P e t

theorem lineForm_eq_zero_of_mem (P : LabelledTuple n) (e : ZMod n) {x : Plane}
    (hx : x ∈ edgeSegment P e) : lineForm P e x = 0 := by
  obtain ⟨t, _, _, rfl⟩ := hx
  exact lineForm_edgePoint P e t

theorem G5_swap (P : LabelledTuple n) (e f : ZMod n) : G5 P f e = -G5 P e f := det_swap _ _

/-- "`G4_{e;g,f} = −G4_{e;f,g}`" (d1_setup.tex:130–131). -/
theorem G4_swap (P : LabelledTuple n) (e f g : ZMod n) : G4 P e g f = -G4 P e f g := by
  unfold G4
  ring

/-- The three identities of d8a_dictionary.tex:429–435 ("for a fixed ordering") and
d1_setup.tex:174–177: `G4_{e;f,g} = −G3_{e,f,g}`, `G4_{f;e,g} = +G3_{e,f,g}`,
`G4_{g;e,f} = −G3_{e,f,g}`, as identities of polynomials. -/
theorem G4_eq_neg_G3 (P : LabelledTuple n) (e f g : ZMod n) : G4 P e f g = -G3 P e f g := by
  simp only [G4, G3, det3, row_zero, row_one, row_two, det, Prod.fst_sub, Prod.snd_sub]
  ring

theorem G4_swap_first_eq_G3 (P : LabelledTuple n) (e f g : ZMod n) : G4 P f e g = G3 P e f g := by
  simp only [G4, G3, det3, row_zero, row_one, row_two, det, Prod.fst_sub, Prod.snd_sub]
  ring

theorem G4_last_eq_neg_G3 (P : LabelledTuple n) (e f g : ZMod n) : G4 P g e f = -G3 P e f g := by
  simp only [G4, G3, det3, row_zero, row_one, row_two, det, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `G3` is SM's `concurrenceDet` (SM/LineConcurrence.lean). -/
theorem G3_eq_concurrenceDet (P : LabelledTuple n) (e f g : ZMod n) :
    G3 P e f g = concurrenceDet P e f g := by
  rw [concurrenceDet_formula]
  simp only [G3, det3, row_zero, row_one, row_two, edgeLineA, edgeLineB, edgeLineC, edge,
    Prod.fst_sub, Prod.snd_sub]
  ring

/-- With `x` on the lines of `e` and `f`: `G3_{e,f,g} = det(d_e,d_f) · ℓ_g(x)`. Hence (d1_setup.tex:
118–127) `G3` "vanishes exactly when the three lines share a point" once `e, f` are not parallel. -/
theorem G3_eq_det_mul_lineForm (P : LabelledTuple n) (e f g : ZMod n) {x : Plane}
    (he : lineForm P e x = 0) (hf : lineForm P f x = 0) :
    G3 P e f g = det (edge P e) (edge P f) * lineForm P g x := by
  simp only [lineForm, det, Prod.fst_sub, Prod.snd_sub] at he hf ⊢
  simp only [G3, det3, row_zero, row_one, row_two]
  linear_combination
    ((edge P f).1 * (edge P g).2 - (edge P f).2 * (edge P g).1) * he -
    ((edge P e).1 * (edge P g).2 - (edge P e).2 * (edge P g).1) * hf

theorem G3_eq_zero_of_common_point (P : LabelledTuple n) (e f g : ZMod n) {x : Plane}
    (he : lineForm P e x = 0) (hf : lineForm P f x = 0) (hg : lineForm P g x = 0) :
    G3 P e f g = 0 := by
  rw [G3_eq_det_mul_lineForm P e f g he hf, hg, mul_zero]

theorem lineForm_eq_zero_of_G3 (P : LabelledTuple n) (e f g : ZMod n) {x : Plane}
    (hd : det (edge P e) (edge P f) ≠ 0) (h3 : G3 P e f g = 0)
    (he : lineForm P e x = 0) (hf : lineForm P f x = 0) : lineForm P g x = 0 := by
  rw [G3_eq_det_mul_lineForm P e f g he hf] at h3
  exact (mul_eq_zero.mp h3).resolve_left hd

/-- Activation is symmetric in the two edges. -/
theorem crosses_comm (P : LabelledTuple n) (e f : ZMod n) : Crosses P e f ↔ Crosses P f e := by
  unfold Crosses
  constructor
  · rintro ⟨hr, h1, h2⟩
    exact ⟨remote_symm hr, h2, h1⟩
  · rintro ⟨hr, h1, h2⟩
    exact ⟨remote_symm hr, h2, h1⟩

/-- The strict four-sign test is "exactly a transverse interior crossing" (d1_setup.tex:79–83). -/
theorem crosses_iff (P : LabelledTuple n) (e f : ZMod n) :
    Crosses P e f ↔ remote e f ∧ ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      edgePoint P e s = edgePoint P f t ∧ det (edge P e) (edge P f) ≠ 0 := by
  have hcrit := segment_crossing_criterion (P e) (P f) (edge P e) (edge P f)
  have he : P e + edge P e = P (e + 1) := by simp [edge]
  have hf : P f + edge P f = P (f + 1) := by simp [edge]
  rw [he, hf] at hcrit
  unfold Crosses G2 lineForm
  rw [← hcrit]
  exact Iff.rfl

theorem Crosses.remote {P : LabelledTuple n} {e f : ZMod n} (h : Crosses P e f) : remote e f := h.1

theorem Crosses.det_ne_zero {P : LabelledTuple n} {e f : ZMod n} (h : Crosses P e f) :
    det (edge P e) (edge P f) ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hd⟩ := (crosses_iff P e f).mp h
  exact hd

theorem Crosses.det_ne_zero' {P : LabelledTuple n} {e f : ZMod n} (h : Crosses P e f) :
    det (edge P f) (edge P e) ≠ 0 := by
  rw [det_swap]
  exact neg_ne_zero.mpr h.det_ne_zero

theorem Crosses.ne {P : LabelledTuple n} {e f : ZMod n} (h : Crosses P e f) : e ≠ f :=
  (remote_endpoints e f h.1).1.symm

/-- Active pairs are actual crossings (SM def:crossings). -/
theorem Crosses.isCrossing {P : LabelledTuple n} {e f : ZMod n} (h : Crosses P e f) :
    IsCrossing P {e, f} := by
  obtain ⟨hr, s, t, hs0, hs1, ht0, ht1, heq, _⟩ := (crosses_iff P e f).mp h
  exact ⟨e, f, rfl, hr, edgePoint P e s, ⟨s, hs0.le, hs1.le, rfl⟩, ⟨t, ht0.le, ht1.le, heq⟩⟩

/-- "The two agree wherever the four members are nonzero" (d1_setup.tex:79–81): if the four
unconditional members `G2_{e,f}, G2_{e,f+1}, G2_{f,e}, G2_{f,e+1}` are nonzero, then meeting
segments are an active pair. -/
theorem crosses_of_meet {P : LabelledTuple n} {e f : ZMod n} (hr : remote e f)
    (h4 : G2 P e f ≠ 0 ∧ G2 P e (f + 1) ≠ 0 ∧ G2 P f e ≠ 0 ∧ G2 P f (e + 1) ≠ 0)
    (h : (edgeSegment P e ∩ edgeSegment P f).Nonempty) : Crosses P e f := by
  obtain ⟨x, ⟨s, hs0, hs1, hs⟩, ⟨t, ht0, ht1, ht⟩⟩ := h
  have heq : edgePoint P e s = edgePoint P f t := hs.symm.trans ht
  have hd : det (edge P e) (edge P f) ≠ 0 := by
    intro hd
    apply h4.1
    have hid := intersection_second_parameter_identity heq
    unfold G2 lineForm
    rw [det_swap, hid, hd, mul_zero, neg_zero]
  have hs0' : s ≠ 0 := by
    rintro rfl
    apply h4.2.2.1
    rw [edgePoint_zero] at heq
    unfold G2 lineForm
    rw [heq]
    exact det_edge_line P f t
  have hs1' : s ≠ 1 := by
    rintro rfl
    apply h4.2.2.2
    rw [edgePoint_one] at heq
    unfold G2 lineForm
    rw [heq]
    exact det_edge_line P f t
  have ht0' : t ≠ 0 := by
    rintro rfl
    apply h4.1
    rw [edgePoint_zero] at heq
    unfold G2 lineForm
    rw [← heq]
    exact det_edge_line P e s
  have ht1' : t ≠ 1 := by
    rintro rfl
    apply h4.2.1
    rw [edgePoint_one] at heq
    unfold G2 lineForm
    rw [← heq]
    exact det_edge_line P e s
  exact (crosses_iff P e f).mpr ⟨hr, s, t, lt_of_le_of_ne hs0 (Ne.symm hs0'),
    lt_of_le_of_ne hs1 hs1', lt_of_le_of_ne ht0 (Ne.symm ht0'), lt_of_le_of_ne ht1 ht1', heq, hd⟩

theorem crosses_iff_isCrossing {P : LabelledTuple n} {e f : ZMod n} (hr : remote e f)
    (h4 : G2 P e f ≠ 0 ∧ G2 P e (f + 1) ≠ 0 ∧ G2 P f e ≠ 0 ∧ G2 P f (e + 1) ≠ 0) :
    Crosses P e f ↔ IsCrossing P {e, f} :=
  ⟨Crosses.isCrossing, fun h => crosses_of_meet hr h4 ((isCrossing_pair P e f hr).mp h)⟩

/-- `t_f` is SM's `edgeParameter P e f` (the Cramer parameter along `e`). -/
theorem crossParam_eq_edgeParameter (P : LabelledTuple n) (e f : ZMod n) :
    crossParam P e f = edgeParameter P e f := by
  unfold crossParam edgeParameter cramerFirst
  rw [det_swap (P f - P e) (edge P f), det_swap (edge P e) (edge P f), neg_div_neg_eq]

/-- "the crossing of `e` with `f` sits at the parameter `t_f` along `e`" (d1_setup.tex:184–186). -/
theorem crossParam_spec (P : LabelledTuple n) (e f : ZMod n) {s t : ℝ}
    (heq : edgePoint P e s = edgePoint P f t) (hd : det (edge P e) (edge P f) ≠ 0) :
    crossParam P e f = s := by
  have hid := intersection_parameter_identity heq
  unfold crossParam
  rw [det_swap (P f - P e) (edge P f), det_swap (edge P e) (edge P f), neg_div_neg_eq, hid]
  exact mul_div_cancel_right₀ s hd

/-- The display of d1_setup.tex:186–189: `G4_{e;f,g} = (t_f − t_g) det(d_f,d_e) det(d_g,d_e)`. -/
theorem G4_factorization (P : LabelledTuple n) (e f g : ZMod n)
    (hf : det (edge P f) (edge P e) ≠ 0) (hg : det (edge P g) (edge P e) ≠ 0) :
    G4 P e f g = (crossParam P e f - crossParam P e g) *
      det (edge P f) (edge P e) * det (edge P g) (edge P e) := by
  unfold G4 crossParam
  field_simp

/-- "so its vanishing is exactly a tie `t_f = t_g` in the order of crossings along `e`"
(d1_setup.tex:189–191). -/
theorem G4_eq_zero_iff (P : LabelledTuple n) {e f g : ZMod n}
    (hf : Crosses P e f) (hg : Crosses P e g) :
    G4 P e f g = 0 ↔ crossParam P e f = crossParam P e g := by
  rw [G4_factorization P e f g hf.det_ne_zero' hg.det_ne_zero', mul_eq_zero, mul_eq_zero,
    sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact h
    · exact (hf.det_ne_zero' h).elim
    · exact (hg.det_ne_zero' h).elim
  · intro h
    exact Or.inl (Or.inl h)

theorem continuous_det {α : Type*} [TopologicalSpace α] {u v : α → Plane}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => det (u x) (v x) :=
  (hu.fst.mul hv.snd).sub (hu.snd.mul hv.fst)

theorem continuous_G1 (i : ZMod n) : Continuous fun P : LabelledTuple n => G1 P i :=
  continuous_det (continuous_edge _) (continuous_edge _)

theorem continuous_G2 (e i : ZMod n) : Continuous fun P : LabelledTuple n => G2 P e i :=
  continuous_det (continuous_edge e) ((continuous_vertex i).sub (continuous_vertex e))

theorem continuous_G5 (e f : ZMod n) : Continuous fun P : LabelledTuple n => G5 P e f :=
  continuous_det (continuous_edge e) (continuous_edge f)

theorem continuous_G4 (e f g : ZMod n) : Continuous fun P : LabelledTuple n => G4 P e f g :=
  ((continuous_det (continuous_edge f) ((continuous_vertex f).sub (continuous_vertex e))).mul
    (continuous_det (continuous_edge g) (continuous_edge e))).sub
  ((continuous_det (continuous_edge g) ((continuous_vertex g).sub (continuous_vertex e))).mul
    (continuous_det (continuous_edge f) (continuous_edge e)))

theorem continuous_G3 (e f g : ZMod n) : Continuous fun P : LabelledTuple n => G3 P e f g := by
  simp only [G3_eq_concurrenceDet]
  exact continuous_concurrenceDet e f g

/-- The guarded list `𝓖` (d1_setup.tex:42–44): "a finite family of real polynomial functions on
`(ℝ²)^n`, indexed once and for all by combinatorial data that does not depend on the
configuration". One constructor per family; the index data carries the printed side conditions:
(G1) every `i`; (G2) every edge `e` and `i ∉ {e, e+1}`; (G5) remote `e, f` with `e < f` as
representatives (99–101); (G3) pairwise remote `e < f < g` (116–118); (G4) `f, g` remote to `e`
with `f < g` (129–131). -/
inductive Member (n : ℕ) [NeZero n]
  | g1 (i : ZMod n)
  | g2 (e i : ZMod n) (h : i ≠ e ∧ i ≠ e + 1)
  | g5 (e f : ZMod n) (h : remote e f ∧ rep e < rep f)
  | g3 (e f g : ZMod n) (h : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g)
  | g4 (e f g : ZMod n) (h : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g)

variable [NeZero n]

/-- The polynomial function of a member of `𝓖`. -/
def Member.eval : Member n → LabelledTuple n → ℝ
  | .g1 i, P => G1 P i
  | .g2 e i _, P => G2 P e i
  | .g5 e f _, P => G5 P e f
  | .g3 e f g _, P => G3 P e f g
  | .g4 e f g _, P => G4 P e f g

/-- "Unconditional members" (d1_setup.tex:50): (G1) and (G2). -/
def Member.Unconditional : Member n → Prop
  | .g1 _ => True
  | .g2 _ _ _ => True
  | .g5 _ _ _ => False
  | .g3 _ _ _ _ => False
  | .g4 _ _ _ _ => False

/-- "Conditional members" (d1_setup.tex:97): (G5), (G3), (G4). -/
def Member.Conditional (m : Member n) : Prop := ¬ m.Unconditional

/-- The (G5) members, singled out by prop:fidelity (d1_setup.tex:263–288). -/
def Member.IsG5 : Member n → Prop
  | .g5 _ _ _ => True
  | _ => False

/-- Activation at `P` (d1_setup.tex:101, 118, 131): (G5) "active when `e` and `f` cross";
(G3) "active when `e, f, g` pairwise cross"; (G4) "active when `f` and `g` both cross `e`".
Unconditional members are never called active. -/
def Member.Active (P : LabelledTuple n) : Member n → Prop
  | .g1 _ => False
  | .g2 _ _ _ => False
  | .g5 e f _ => Crosses P e f
  | .g3 e f g _ => Crosses P e f ∧ Crosses P f g ∧ Crosses P e g
  | .g4 e f g _ => Crosses P e f ∧ Crosses P e g

/-- CV def:generic (A) (d1_setup.tex:221–223): "A member of `𝓖` is *relevant* at a polygon `P` if
it is unconditional, or if it is conditional and active at `P`". -/
def Member.Relevant (P : LabelledTuple n) (m : Member n) : Prop := m.Unconditional ∨ m.Active P

/-- "The two accessors" (d1_setup.tex:142–160): the *member-valued* accessor
`G4⟨e;f,g⟩ = G4_{e; min(f̄,ḡ), max(f̄,ḡ)} ∈ 𝓖`, "the one indexed by the ordered representative
pair". -/
def G4acc (e f g : ZMod n) (h : remote e f ∧ remote e g ∧ f ≠ g) : Member n :=
  if hfg : rep f < rep g then .g4 e f g ⟨h.1, h.2.1, h.2.2, hfg⟩
  else .g4 e g f ⟨h.2.1, h.1, h.2.2.symm,
    (rep_lt_or_lt h.2.2).resolve_left hfg⟩

/-- The *orientation sign* `ε(f,g) = +1` if `f̄ < ḡ`, `−1` if `f̄ > ḡ` (d1_setup.tex:148–150), "a
constant of the index data and not a function of the configuration". -/
def eps (f g : ZMod n) : ℤ := if rep f < rep g then 1 else -1

/-- The *oriented value* `Ĝ4_{e;f,g} = ε(f,g) · G4⟨e;f,g⟩` (d1_setup.tex:156–160). -/
def orientedG4 (P : LabelledTuple n) (e f g : ZMod n)
    (h : remote e f ∧ remote e g ∧ f ≠ g) : ℝ :=
  (eps f g : ℝ) * (G4acc e f g h).eval P

/-! ### Row 131, theorems on the indexed family `𝓖`: evaluation, accessors, finiteness -/

@[simp] theorem Member.eval_g1 (i : ZMod n) (P : LabelledTuple n) :
    (Member.g1 i).eval P = G1 P i := rfl
@[simp] theorem Member.eval_g2 (e i : ZMod n) (h : i ≠ e ∧ i ≠ e + 1) (P : LabelledTuple n) :
    (Member.g2 e i h).eval P = G2 P e i := rfl
@[simp] theorem Member.eval_g5 (e f : ZMod n) (h : remote e f ∧ rep e < rep f)
    (P : LabelledTuple n) : (Member.g5 e f h).eval P = G5 P e f := rfl
@[simp] theorem Member.eval_g3 (e f g : ZMod n)
    (h : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g)
    (P : LabelledTuple n) : (Member.g3 e f g h).eval P = G3 P e f g := rfl
@[simp] theorem Member.eval_g4 (e f g : ZMod n) (h : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g)
    (P : LabelledTuple n) : (Member.g4 e f g h).eval P = G4 P e f g := rfl

theorem eps_eq_one {f g : ZMod n} (h : rep f < rep g) : eps f g = 1 := by
  simp [eps, h]

theorem eps_eq_neg_one {f g : ZMod n} (h : rep g < rep f) : eps f g = -1 := by
  simp [eps, not_lt.mpr h.le]

theorem eps_mul_self (f g : ZMod n) : eps f g * eps f g = 1 := by
  unfold eps
  split_ifs <;> norm_num

theorem eps_eq_one_or (f g : ZMod n) : eps f g = 1 ∨ eps f g = -1 := by
  unfold eps
  split_ifs <;> simp

theorem eps_symm {f g : ZMod n} (h : f ≠ g) : eps g f = -eps f g := by
  rcases rep_lt_or_lt h with hlt | hlt
  · rw [eps_eq_one hlt, eps_eq_neg_one hlt]
  · rw [eps_eq_neg_one hlt, eps_eq_one hlt, neg_neg]

theorem G4acc_of_lt (e : ZMod n) {f g : ZMod n} (h : remote e f ∧ remote e g ∧ f ≠ g)
    (hfg : rep f < rep g) : G4acc e f g h = Member.g4 e f g ⟨h.1, h.2.1, h.2.2, hfg⟩ := by
  simp [G4acc, hfg]

theorem G4acc_of_gt (e : ZMod n) {f g : ZMod n} (h : remote e f ∧ remote e g ∧ f ≠ g)
    (hgf : rep g < rep f) : G4acc e f g h = Member.g4 e g f ⟨h.2.1, h.1, h.2.2.symm, hgf⟩ := by
  simp [G4acc, not_lt.mpr hgf.le]

/-- The accessor is insensitive to the presentation order (d1_setup.tex:177–178: "Statements
about vanishing, activation and relevance are statements about the member and are insensitive to
the presentation order"). -/
theorem G4acc_comm (e : ZMod n) {f g : ZMod n} (h : remote e f ∧ remote e g ∧ f ≠ g) :
    G4acc e g f ⟨h.2.1, h.1, h.2.2.symm⟩ = G4acc e f g h := by
  rcases rep_lt_or_lt h.2.2 with hlt | hlt
  · rw [G4acc_of_lt e h hlt, G4acc_of_gt e _ hlt]
  · rw [G4acc_of_gt e h hlt, G4acc_of_lt e _ hlt]

theorem G4acc_eval (P : LabelledTuple n) (e : ZMod n) {f g : ZMod n}
    (h : remote e f ∧ remote e g ∧ f ≠ g) :
    (G4acc e f g h).eval P = if rep f < rep g then G4 P e f g else G4 P e g f := by
  by_cases hfg : rep f < rep g
  · rw [G4acc_of_lt e h hfg, Member.eval_g4]
    simp [hfg]
  · rw [G4acc_of_gt e h ((rep_lt_or_lt h.2.2).resolve_left hfg), Member.eval_g4]
    simp [hfg]

/-- The oriented value is `G4_{e;f,g}` read in the presented order: "a real polynomial function
on `(ℝ²)^n`, antisymmetric in the ordered pair, equal to the member up to the orientation sign"
(d1_setup.tex:158–160). -/
theorem orientedG4_eq_G4 (P : LabelledTuple n) (e : ZMod n) {f g : ZMod n}
    (h : remote e f ∧ remote e g ∧ f ≠ g) : orientedG4 P e f g h = G4 P e f g := by
  unfold orientedG4
  rw [G4acc_eval]
  by_cases hfg : rep f < rep g
  · rw [eps_eq_one hfg]
    simp [hfg]
  · rw [eps_eq_neg_one ((rep_lt_or_lt h.2.2).resolve_left hfg), G4_swap P e f g]
    simp [hfg]

theorem orientedG4_antisymm (P : LabelledTuple n) (e : ZMod n) {f g : ZMod n}
    (h : remote e f ∧ remote e g ∧ f ≠ g) :
    orientedG4 P e g f ⟨h.2.1, h.1, h.2.2.symm⟩ = -orientedG4 P e f g h := by
  rw [orientedG4_eq_G4, orientedG4_eq_G4, G4_swap]

theorem G4acc_eval_eq_eps_mul (P : LabelledTuple n) (e : ZMod n) {f g : ZMod n}
    (h : remote e f ∧ remote e g ∧ f ≠ g) :
    (G4acc e f g h).eval P = (eps f g : ℝ) * orientedG4 P e f g h := by
  unfold orientedG4
  rw [← mul_assoc, ← Int.cast_mul, eps_mul_self]
  simp

/-- The illustration of d1_setup.tex:180–184: at `j = 0` the pair `(e_{n−1}, e_n)` has increasing
representatives, `ε = +1`; at `j = 1` the pair `(e_0, e_1)` has representatives `(n, 1)`,
`ε = −1`. -/
theorem eps_illustration (hn : 3 ≤ n) : eps (-1 : ZMod n) 0 = 1 ∧ eps (0 : ZMod n) 1 = -1 := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hrep0 : rep (0 : ZMod n) = n := by
    unfold rep
    rw [zero_sub, ZMod.neg_val, ZMod.val_one]
    split_ifs with h
    · exact absurd h one_ne_zero
    · omega
  have hrep1 : rep (1 : ZMod n) = 1 := by
    unfold rep
    rw [sub_self, ZMod.val_zero]
  have hrepm : rep (-1 : ZMod n) = n - 1 := by
    unfold rep
    have h2 : (-1 - 1 : ZMod n) = -(2 : ℕ) := by push_cast; ring
    have h20 : ((2 : ℕ) : ZMod n) ≠ 0 := by
      intro h
      have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 n).mp h)
      omega
    rw [h2, ZMod.neg_val, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    split_ifs with h
    · exact absurd h h20
    · omega
  constructor
  · exact eps_eq_one (by rw [hrepm, hrep0]; omega)
  · exact eps_eq_neg_one (by rw [hrep0, hrep1]; omega)

/-- Relevance, membership characterisations. -/
theorem Member.relevant_iff (P : LabelledTuple n) (m : Member n) :
    m.Relevant P ↔ m.Unconditional ∨ m.Active P := Iff.rfl

theorem Member.unconditional_g1 (i : ZMod n) : (Member.g1 i : Member n).Unconditional := trivial
theorem Member.unconditional_g2 (e i : ZMod n) (h : i ≠ e ∧ i ≠ e + 1) :
    (Member.g2 e i h : Member n).Unconditional := trivial
theorem Member.conditional_g5 (e f : ZMod n) (h : remote e f ∧ rep e < rep f) :
    (Member.g5 e f h : Member n).Conditional := fun h => h
theorem Member.conditional_g3 (e f g : ZMod n)
    (h : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g) :
    (Member.g3 e f g h : Member n).Conditional := fun h => h
theorem Member.conditional_g4 (e f g : ZMod n) (h : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g) :
    (Member.g4 e f g h : Member n).Conditional := fun h => h

theorem Member.not_active_of_unconditional {P : LabelledTuple n} {m : Member n}
    (h : m.Unconditional) : ¬ m.Active P := by
  cases m <;> simp [Member.Unconditional, Member.Active] at h ⊢

theorem Member.relevant_g1 (P : LabelledTuple n) (i : ZMod n) :
    (Member.g1 i : Member n).Relevant P := Or.inl trivial
theorem Member.relevant_g2 (P : LabelledTuple n) (e i : ZMod n) (h : i ≠ e ∧ i ≠ e + 1) :
    (Member.g2 e i h : Member n).Relevant P := Or.inl trivial
theorem Member.relevant_g5_iff (P : LabelledTuple n) (e f : ZMod n) (h : remote e f ∧ rep e < rep f) :
    (Member.g5 e f h : Member n).Relevant P ↔ Crosses P e f := by
  simp [Member.Relevant, Member.Unconditional, Member.Active]
theorem Member.relevant_g3_iff (P : LabelledTuple n) (e f g : ZMod n)
    (h : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g) :
    (Member.g3 e f g h : Member n).Relevant P ↔ Crosses P e f ∧ Crosses P f g ∧ Crosses P e g := by
  simp [Member.Relevant, Member.Unconditional, Member.Active]
theorem Member.relevant_g4_iff (P : LabelledTuple n) (e f g : ZMod n)
    (h : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g) :
    (Member.g4 e f g h : Member n).Relevant P ↔ Crosses P e f ∧ Crosses P e g := by
  simp [Member.Relevant, Member.Unconditional, Member.Active]

/-- The index data of a member (the proof fields carry no data). -/
def Member.code : Member n → Fin 5 × ZMod n × ZMod n × ZMod n
  | .g1 i => (0, i, 0, 0)
  | .g2 e i _ => (1, e, i, 0)
  | .g5 e f _ => (2, e, f, 0)
  | .g3 e f g _ => (3, e, f, g)
  | .g4 e f g _ => (4, e, f, g)

theorem Member.code_injective : Function.Injective (Member.code (n := n)) := by
  intro a b hab
  cases a <;> cases b <;> simp [Member.code] at hab <;> (obtain ⟨rfl, rfl, rfl⟩ := hab; rfl)

/-- "a finite family" (d1_setup.tex:43). -/
instance Member.finite : Finite (Member n) := Finite.of_injective _ Member.code_injective

/-- Every member is a continuous (indeed polynomial) function of the configuration. -/
theorem Member.continuous_eval (m : Member n) : Continuous fun P : LabelledTuple n => m.eval P := by
  cases m with
  | g1 i => exact continuous_G1 i
  | g2 e i _ => exact continuous_G2 e i
  | g5 e f _ => exact continuous_G5 e f
  | g3 e f g _ => exact continuous_G3 e f g
  | g4 e f g _ => exact continuous_G4 e f g

theorem Member.unconditional_iff (m : Member n) :
    m.Unconditional ↔ (∃ i, m = .g1 i) ∨ (∃ e i h, m = .g2 e i h) := by
  cases m with
  | g1 i => exact ⟨fun _ => Or.inl ⟨i, rfl⟩, fun _ => trivial⟩
  | g2 e i h => exact ⟨fun _ => Or.inr ⟨e, i, h, rfl⟩, fun _ => trivial⟩
  | g5 e f h =>
    refine ⟨fun h => False.elim h, ?_⟩
    rintro (⟨i, hi⟩ | ⟨e', i', h', hi⟩) <;> cases hi
  | g3 e f g h =>
    refine ⟨fun h => False.elim h, ?_⟩
    rintro (⟨i, hi⟩ | ⟨e', i', h', hi⟩) <;> cases hi
  | g4 e f g h =>
    refine ⟨fun h => False.elim h, ?_⟩
    rintro (⟨i, hi⟩ | ⟨e', i', h', hi⟩) <;> cases hi

/-- CV def:guarded (d1_setup.tex:42–218), clause by clause. -/
structure GuardedData : Prop where
  /-- "Write `d_i = p_{i+1} − p_i` and, for an edge index `e`, write `ℓ_e(x) = det(d_e, x − p_e)`
  for the affine form vanishing on the line of `e`" (44–46). -/
  line_form : ∀ (n : ℕ) (P : LabelledTuple n) (e : ZMod n) (x : Plane),
    lineForm P e x = det (P (e + 1) - P e) (x - P e)
  line_form_vanishes : ∀ (n : ℕ) (P : LabelledTuple n) (e : ZMod n) (t : ℝ),
    lineForm P e (edgePoint P e t) = 0
  /-- "with coefficient row `(A_e,B_e,C_e) = (−d_{e,2}, d_{e,1}, d_{e,2}p_{e,1} − d_{e,1}p_{e,2})`,
  so that `ℓ_e(x) = A_e x_1 + B_e x_2 + C_e`" (46–48). -/
  coefficient_row : ∀ (n : ℕ) (P : LabelledTuple n) (e : ZMod n),
    row P e 0 = -(edge P e).2 ∧ row P e 1 = (edge P e).1 ∧
    row P e 2 = (edge P e).2 * (P e).1 - (edge P e).1 * (P e).2
  line_form_row : ∀ (n : ℕ) (P : LabelledTuple n) (e : ZMod n) (x : Plane),
    lineForm P e x = row P e 0 * x.1 + row P e 1 * x.2 + row P e 2
  /-- (G1) "`G1_i = det(d_{i−1}, d_i)`, for every `i`" (52). -/
  g1 : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (i : ZMod n),
    (Member.g1 i).eval P = det (edge P (i - 1)) (edge P i)
  /-- (G2) "`G2_{e,i} = ℓ_e(p_i) = det(d_e, p_i − p_e)`, for every edge index `e` and every
  `i ∉ {e, e+1}`" (53–54). -/
  g2 : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (e i : ZMod n) (h : i ≠ e ∧ i ≠ e + 1),
    (Member.g2 e i h).eval P = det (edge P e) (P i - P e)
  /-- "Unconditional members" are exactly (G1) and (G2) (50–55); the others are "conditional"
  (97). -/
  unconditional : ∀ (n : ℕ) [NeZero n] (m : Member n),
    m.Unconditional ↔ (∃ i, m = .g1 i) ∨ (∃ e i h, m = .g2 e i h)
  conditional : ∀ (n : ℕ) [NeZero n] (m : Member n), m.Conditional ↔ ¬ m.Unconditional
  /-- Activation (57–63): "Two remote edges `e, f` are *defined* to cross when
  `G2_{e,f} G2_{e,f+1} < 0` and `G2_{f,e} G2_{f,e+1} < 0`", with strict products. -/
  activation : ∀ (n : ℕ) (P : LabelledTuple n) (e f : ZMod n),
    Crosses P e f ↔ remote e f ∧ G2 P e f * G2 P e (f + 1) < 0 ∧ G2 P f e * G2 P f (e + 1) < 0
  /-- "there they say that each edge has its two endpoints strictly on opposite sides of the
  other's line, which for segments is exactly a transverse interior crossing" (80–83). -/
  activation_geometric : ∀ (n : ℕ) (P : LabelledTuple n) (e f : ZMod n),
    Crosses P e f ↔ remote e f ∧ ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      edgePoint P e s = edgePoint P f t ∧ det (edge P e) (edge P f) ≠ 0
  /-- "The two agree wherever the four members are nonzero" (79–80): with the four unconditional
  members nonzero, activation is the meeting of the two closed segments (SM def:crossings). -/
  activation_agrees : ∀ (n : ℕ) (P : LabelledTuple n) (e f : ZMod n), remote e f →
    (G2 P e f ≠ 0 ∧ G2 P e (f + 1) ≠ 0 ∧ G2 P f e ≠ 0 ∧ G2 P f (e + 1) ≠ 0) →
    (Crosses P e f ↔ IsCrossing P {e, f})
  /-- Unconditionally, an active pair is an actual crossing. -/
  activation_crossing : ∀ (n : ℕ) (P : LabelledTuple n) (e f : ZMod n),
    Crosses P e f → IsCrossing P {e, f}
  /-- (G5) "`G5_{e,f} = det(d_e,d_f)`, for every pair of remote edge indices with `1 ≤ e < f ≤ n`
  as integers … *active* when `e` and `f` cross" (99–108). -/
  g5 : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (e f : ZMod n) (h : remote e f ∧ rep e < rep f),
    (Member.g5 e f h).eval P = det (edge P e) (edge P f) ∧
    ((Member.g5 e f h).Active P ↔ Crosses P e f)
  /-- "`det(d_f,d_e) = −det(d_e,d_f)`" (104–105). -/
  g5_antisymmetric : ∀ (n : ℕ) (P : LabelledTuple n) (e f : ZMod n), G5 P f e = -G5 P e f
  /-- (G3) "`G3_{e,f,g} = det` of the matrix of the rows `(A_e,B_e,C_e)`, `(A_f,B_f,C_f)`,
  `(A_g,B_g,C_g)` … for every triple of pairwise remote edges `1 ≤ e < f < g ≤ n` … *active* when
  `e, f, g` pairwise cross" (113–118). -/
  g3 : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (e f g : ZMod n)
    (h : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g),
    (Member.g3 e f g h).eval P = det3 (row P e) (row P f) (row P g) ∧
    ((Member.g3 e f g h).Active P ↔ Crosses P e f ∧ Crosses P f g ∧ Crosses P e g)
  /-- "It vanishes exactly when the three lines share a point of the projective plane … On the
  active domain the three edges pairwise cross, so no two of the lines are parallel and the
  vanishing is exactly a concurrence at a finite point" (118–127): for `x` on the lines of `e`
  and `f`, `G3_{e,f,g} = det(d_e,d_f) · ℓ_g(x)`. -/
  g3_concurrence : ∀ (n : ℕ) (P : LabelledTuple n) (e f g : ZMod n) (x : Plane),
    lineForm P e x = 0 → lineForm P f x = 0 → G3 P e f g = det (edge P e) (edge P f) * lineForm P g x
  /-- (G4) "`G4_{e;f,g} = det(d_f, p_f − p_e) det(d_g,d_e) − det(d_g, p_g − p_e) det(d_f,d_e)`, for
  every edge `e` and every pair of edges remote to `e` with `1 ≤ f < g ≤ n` as integers … *active*
  when `f` and `g` both cross `e`" (128–131). -/
  g4 : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (e f g : ZMod n)
    (h : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g),
    (Member.g4 e f g h).eval P =
      det (edge P f) (P f - P e) * det (edge P g) (edge P e)
        - det (edge P g) (P g - P e) * det (edge P f) (edge P e) ∧
    ((Member.g4 e f g h).Active P ↔ Crosses P e f ∧ Crosses P e g)
  /-- "since `G4_{e;g,f} = −G4_{e;f,g}`" (130–131). -/
  g4_antisymmetric : ∀ (n : ℕ) (P : LabelledTuple n) (e f g : ZMod n), G4 P e g f = -G4 P e f g
  /-- "Normalization of cyclic aliases" (132–140): `rep i ∈ {1,…,n}` names the edge `e_i`, and
  distinct edges have distinct representatives. -/
  representative : ∀ (n : ℕ) [NeZero n] (i : ZMod n),
    1 ≤ rep i ∧ rep i ≤ n ∧ ((rep i : ℕ) : ZMod n) = i
  representative_injective : ∀ (n : ℕ) [NeZero n], Function.Injective (rep (n := n))
  /-- The member-valued accessor "`G4⟨e;f,g⟩ = G4_{e;min(f̄,ḡ),max(f̄,ḡ)} ∈ 𝓖`" (142–148), insensitive
  to the presentation order (177–178). -/
  accessor : ∀ (n : ℕ) [NeZero n] (e f g : ZMod n) (h : remote e f ∧ remote e g ∧ f ≠ g),
    (∀ hfg : rep f < rep g, G4acc e f g h = Member.g4 e f g ⟨h.1, h.2.1, h.2.2, hfg⟩) ∧
    (∀ hgf : rep g < rep f, G4acc e f g h = Member.g4 e g f ⟨h.2.1, h.1, h.2.2.symm, hgf⟩) ∧
    G4acc e g f ⟨h.2.1, h.1, h.2.2.symm⟩ = G4acc e f g h
  /-- The orientation sign "`ε(f,g) = +1` if `f̄ < ḡ`, `−1` if `f̄ > ḡ`", "in `{±1}`" (148–152). -/
  orientation_sign : ∀ (n : ℕ) [NeZero n] (f g : ZMod n),
    (rep f < rep g → eps f g = 1) ∧ (rep g < rep f → eps f g = -1) ∧ (eps f g = 1 ∨ eps f g = -1)
  /-- "Their product `Ĝ4_{e;f,g} = ε(f,g) · G4⟨e;f,g⟩` is the oriented value: a real polynomial
  function on `(ℝ²)^n`, antisymmetric in the ordered pair, equal to the member up to the
  orientation sign" (154–160); it is `G4_{e;f,g}` read in the presented order. -/
  oriented_value : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (e f g : ZMod n)
    (h : remote e f ∧ remote e g ∧ f ≠ g),
    orientedG4 P e f g h = (eps f g : ℝ) * (G4acc e f g h).eval P ∧
    orientedG4 P e f g h = G4 P e f g ∧
    orientedG4 P e g f ⟨h.2.1, h.1, h.2.2.symm⟩ = -orientedG4 P e f g h ∧
    (G4acc e f g h).eval P = (eps f g : ℝ) * orientedG4 P e f g h
  /-- "Two illustrations of the reduction" (180–184): `(e_{n−1}, e_n)` has `ε = +1`, `(e_0, e_1)`
  has representatives `(n, 1)` and `ε = −1`. -/
  illustration : ∀ (n : ℕ) [NeZero n], 3 ≤ n → eps (-1 : ZMod n) 0 = 1 ∧ eps (0 : ZMod n) 1 = -1
  /-- The display (184–191): "When active, both `det(d_f,d_e)` and `det(d_g,d_e)` are nonzero, the
  crossing of `e` with `f` sits at the parameter `t_f = det(d_f,p_f−p_e)/det(d_f,d_e)` along `e`,
  and `G4_{e;f̄,ḡ} = (t_f̄ − t_ḡ) det(d_f̄,d_e) det(d_ḡ,d_e)`, so its vanishing is exactly a tie
  `t_f̄ = t_ḡ`". -/
  display : ∀ (n : ℕ) (P : LabelledTuple n) (e f g : ZMod n), Crosses P e f → Crosses P e g →
    det (edge P f) (edge P e) ≠ 0 ∧ det (edge P g) (edge P e) ≠ 0 ∧
    G4 P e f g = (crossParam P e f - crossParam P e g) *
      det (edge P f) (edge P e) * det (edge P g) (edge P e) ∧
    (G4 P e f g = 0 ↔ crossParam P e f = crossParam P e g)
  crossing_parameter : ∀ (n : ℕ) (P : LabelledTuple n) (e f : ZMod n) (s t : ℝ),
    edgePoint P e s = edgePoint P f t → det (edge P e) (edge P f) ≠ 0 → crossParam P e f = s
  /-- "for three pairwise remote edges `G4_{e;f,g} = −G3_{e,f,g}` — an identity of polynomials"
  (174–177), with its two companions (d8a_dictionary.tex:429–435). -/
  dictionary_identities : ∀ (n : ℕ) (P : LabelledTuple n) (e f g : ZMod n),
    G4 P e f g = -G3 P e f g ∧ G4 P f e g = G3 P e f g ∧ G4 P g e f = -G3 P e f g
  /-- "a finite family of real polynomial functions on `(ℝ²)^n`" (42–43): finitely many members,
  each a continuous function of the configuration. -/
  finite : ∀ (n : ℕ) [NeZero n], Finite (Member n)
  continuous : ∀ (n : ℕ) [NeZero n] (m : Member n), Continuous fun P : LabelledTuple n => m.eval P

theorem guarded_definition : GuardedData where
  line_form := fun _ _ _ _ => rfl
  line_form_vanishes := fun _ P e t => lineForm_edgePoint P e t
  coefficient_row := fun _ _ _ => ⟨rfl, rfl, rfl⟩
  line_form_row := fun _ P e x => lineForm_eq_row P e x
  g1 := fun _ _ _ _ => rfl
  g2 := fun _ _ _ _ _ _ => rfl
  unconditional := fun _ _ m => Member.unconditional_iff m
  conditional := fun _ _ _ => Iff.rfl
  activation := fun _ _ _ _ => Iff.rfl
  activation_geometric := fun _ P e f => crosses_iff P e f
  activation_agrees := fun _ _ _ _ hr h4 => crosses_iff_isCrossing hr h4
  activation_crossing := fun _ _ _ _ h => h.isCrossing
  g5 := fun _ _ _ _ _ _ => ⟨rfl, Iff.rfl⟩
  g5_antisymmetric := fun _ P e f => G5_swap P e f
  g3 := fun _ _ _ _ _ _ _ => ⟨rfl, Iff.rfl⟩
  g3_concurrence := fun _ P e f g _ he hf => G3_eq_det_mul_lineForm P e f g he hf
  g4 := fun _ _ _ _ _ _ _ => ⟨rfl, Iff.rfl⟩
  g4_antisymmetric := fun _ P e f g => G4_swap P e f g
  representative := fun _ _ i => ⟨rep_pos i, rep_le i, rep_cast i⟩
  representative_injective := fun _ _ => rep_injective
  accessor := fun _ _ e _ _ h =>
    ⟨fun hfg => G4acc_of_lt e h hfg, fun hgf => G4acc_of_gt e h hgf, G4acc_comm e h⟩
  orientation_sign := fun _ _ f g =>
    ⟨fun h => eps_eq_one h, fun h => eps_eq_neg_one h, eps_eq_one_or f g⟩
  oriented_value := fun _ _ P e _ _ h =>
    ⟨rfl, orientedG4_eq_G4 P e h, orientedG4_antisymm P e h, G4acc_eval_eq_eps_mul P e h⟩
  illustration := fun _ _ hn => eps_illustration hn
  display := fun _ P e f g hf hg =>
    ⟨hf.det_ne_zero', hg.det_ne_zero', G4_factorization P e f g hf.det_ne_zero' hg.det_ne_zero',
      G4_eq_zero_iff P hf hg⟩
  crossing_parameter := fun _ P e f _ _ heq hd => crossParam_spec P e f heq hd
  dictionary_identities := fun _ P e f g =>
    ⟨G4_eq_neg_G3 P e f g, G4_swap_first_eq_G3 P e f g, G4_last_eq_neg_G3 P e f g⟩
  finite := fun _ _ => Member.finite
  continuous := fun _ _ m => m.continuous_eval

/-! ## Row 132 — CV:def:generic (d1_setup.tex:220–238) -/

/-- CV def:generic (A) (d1_setup.tex:223–224): "A polygon `P` (Definition def:polygon) is *generic*
if every member relevant at `P` is nonzero at `P`". -/
def Generic (P : LabelledTuple n) : Prop :=
  IsPolygon P ∧ ∀ m : Member n, m.Relevant P → m.eval P ≠ 0

/-- "We write `𝓤_n` for the set of generic polygons on `n` vertices" (d1_setup.tex:226–227). -/
def genericLocus (n : ℕ) [NeZero n] : Set (LabelledTuple n) := {P | Generic P}

/-- CV def:generic (B) (d1_setup.tex:229–231): "A *chamber* is a connected component of the set
`𝓤_n` of generic polygons on `n` vertices" — on labelled tuples, no cyclic quotient. -/
def chamber (P : LabelledTuple n) : Set (LabelledTuple n) :=
  connectedComponentIn (genericLocus n) P

/-- prop:fidelity (d1_setup.tex:263–266): "`𝓤_n^♭` the set of polygons at which every member of the
four families (G1)–(G4) that is relevant is nonzero". -/
def flatGenericLocus (n : ℕ) [NeZero n] : Set (LabelledTuple n) :=
  {P | IsPolygon P ∧ ∀ m : Member n, ¬ m.IsG5 → m.Relevant P → m.eval P ≠ 0}

variable {P : LabelledTuple n}

theorem Generic.isPolygon (hP : Generic P) : IsPolygon P := hP.1

theorem Generic.edge_ne_zero (hP : Generic P) (i : ZMod n) : edge P i ≠ 0 := hP.1 i

theorem Generic.g1 (hP : Generic P) (i : ZMod n) : G1 P i ≠ 0 :=
  hP.2 (.g1 i) (Member.relevant_g1 P i)

theorem Generic.g2 (hP : Generic P) {e i : ZMod n} (h0 : i ≠ e) (h1 : i ≠ e + 1) :
    G2 P e i ≠ 0 :=
  hP.2 (.g2 e i ⟨h0, h1⟩) (Member.relevant_g2 P e i ⟨h0, h1⟩)

theorem Generic.turn_ne_zero (hP : Generic P) (i : ZMod n) : turn P i ≠ 0 := by
  rw [turn_det]
  exact sign_ne_zero.mpr (hP.g1 i)

theorem Generic.four_g2 (hP : Generic P) {e f : ZMod n} (hr : remote e f) :
    G2 P e f ≠ 0 ∧ G2 P e (f + 1) ≠ 0 ∧ G2 P f e ≠ 0 ∧ G2 P f (e + 1) ≠ 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := remote_endpoints e f hr
  exact ⟨hP.g2 h0 h1, hP.g2 h2 h3, hP.g2 h0.symm h2.symm, hP.g2 h1.symm h3.symm⟩

/-- On generic polygons, activation is exactly the actual crossing relation (SM def:crossings). -/
theorem Generic.crosses_iff (hP : Generic P) (e f : ZMod n) :
    Crosses P e f ↔ IsCrossing P {e, f} := by
  refine ⟨Crosses.isCrossing, fun h => ?_⟩
  have hr := crossing_pair_remote h
  exact crosses_of_meet hr (hP.four_g2 hr) ((isCrossing_pair P e f hr).mp h)

theorem Generic.g5 (_hP : Generic P) {e f : ZMod n} (h : Crosses P e f) : G5 P e f ≠ 0 :=
  h.det_ne_zero

theorem Generic.g4 (hP : Generic P) {e f g : ZMod n} (hf : Crosses P e f) (hg : Crosses P e g)
    (hfg : f ≠ g) : G4 P e f g ≠ 0 := by
  rcases rep_lt_or_lt hfg with hlt | hlt
  · exact hP.2 (.g4 e f g ⟨hf.remote, hg.remote, hfg, hlt⟩) (Or.inr ⟨hf, hg⟩)
  · have h := hP.2 (.g4 e g f ⟨hg.remote, hf.remote, hfg.symm, hlt⟩) (Or.inr ⟨hg, hf⟩)
    rw [Member.eval_g4, G4_swap] at h
    exact neg_ne_zero.mp h

theorem Generic.g3 (hP : Generic P) {e f g : ZMod n} (hef : Crosses P e f) (hfg : Crosses P f g)
    (heg : Crosses P e g) : G3 P e f g ≠ 0 := by
  rw [← neg_ne_zero, ← G4_eq_neg_G3]
  exact hP.g4 hef heg hfg.ne

/-- "`G2_{e,i} ≠ 0` says no vertex lies on the line of a non-incident edge, hence none lies on the
edge" (rem:genericmeans, d1_setup.tex:246–247). -/
theorem Generic.vertex_off_line (hP : Generic P) {k e : ZMod n} (hk : ¬ incident k e) (t : ℝ) :
    P k ≠ edgePoint P e t := by
  obtain ⟨h0, h1⟩ := (nonincident_iff k e).mp hk
  intro heq
  apply hP.g2 h0 h1
  unfold G2 lineForm
  rw [heq]
  exact det_edge_line P e t

theorem Generic.vertex_not_mem_edge (hP : Generic P) {k e : ZMod n} (hk : ¬ incident k e) :
    P k ∉ edgeSegment P e := by
  rintro ⟨t, _, _, heq⟩
  exact hP.vertex_off_line hk t heq

/-- "`G4 ≠ 0` says the crossings along each edge are totally ordered with no ties" (rem:genericmeans,
d1_setup.tex:249–250). -/
theorem Generic.crossParam_ne (hP : Generic P) {e f g : ZMod n} (hf : Crosses P e f)
    (hg : Crosses P e g) (hfg : f ≠ g) : crossParam P e f ≠ crossParam P e g :=
  fun h => hP.g4 hf hg hfg ((G4_eq_zero_iff P hf hg).mpr h)

/-- CV-generic polygons are weakly generic in SM's sense (fidelity fact F1). -/
theorem Generic.weakGeneric (hP : Generic P) : WeakGeneric P := by
  have hvert : ∀ k e, ¬ incident k e → P k ∉ edgeSegment P e :=
    fun _ _ hk => hP.vertex_not_mem_edge hk
  refine ⟨hP.1, hP.turn_ne_zero, hvert, ?_, ?_⟩
  · intro i j hr
    have hmeet : ∀ x, x ∈ edgeSegment P i → x ∈ edgeSegment P j →
        det (edge P i) (edge P j) ≠ 0 :=
      fun x hi hj => (crosses_of_meet hr (hP.four_g2 hr) ⟨x, hi, hj⟩).det_ne_zero
    exact ⟨hmeet, fun x y hxi hxj hyi hyj =>
      transverse_segments_unique (hmeet x hxi hxj) hxi hxj hyi hyj⟩
  · apply (weak_base_g2_iff_no_remote_closed_triples hP.1 hP.turn_ne_zero hvert).mpr
    rintro i j k hij hjk hik ⟨x, hi, hj, hk⟩
    have cij := crosses_of_meet hij (hP.four_g2 hij) ⟨x, hi, hj⟩
    have cjk := crosses_of_meet hjk (hP.four_g2 hjk) ⟨x, hj, hk⟩
    have cik := crosses_of_meet hik (hP.four_g2 hik) ⟨x, hi, hk⟩
    exact hP.g3 cij cjk cik (G3_eq_zero_of_common_point P i j k
      (lineForm_eq_zero_of_mem P i hi) (lineForm_eq_zero_of_mem P j hj)
      (lineForm_eq_zero_of_mem P k hk))

theorem Generic.crossingGeometry (hP : Generic P) : CrossingGeometry P :=
  weak_crossingGeometry hP.weakGeneric

/-- "`G3 ≠ 0` says no three pairwise remote edges are concurrent" (rem:genericmeans, 247–248): SM's
(G2), no three edge interiors concur. -/
theorem Generic.g2_sm (hP : Generic P) : SM.G2 P := hP.weakGeneric.2.2.2.2

/-- "`G1_i ≠ 0` … excludes both degenerate turns at once: the flat turn … and the kink"
(rem:genericmeans, 241–245): generic polygons are regular. -/
theorem Generic.regular (hP : Generic P) : Regular P := by
  refine ⟨hP.1, ?_⟩
  intro i l _ he
  have hd : det (edge P i) (edge P (i + 1)) ≠ 0 := by
    have h := hP.g1 (i + 1)
    unfold G1 at h
    rwa [add_sub_cancel_right] at h
  exact no_multiple_of_det_ne_zero hd (-l) he

theorem Generic.regular_sm (hP : Generic P) : SM.Regular P := (regular_iff_sm P).mp hP.regular

omit [NeZero n] in
/-- Under SM genericity every active (G4) member is nonzero: the two crossings on `e` are distinct
points, so their parameters differ (SM lem:crossing-test). -/
theorem sm_G4_ne_zero (hn : 3 ≤ n) (hP : SM.Generic P) {e f g : ZMod n} (hf : Crosses P e f)
    (hg : Crosses P e g) (hfg : f ≠ g) : G4 P e f g ≠ 0 := by
  rw [G4_factorization P e f g hf.det_ne_zero' hg.det_ne_zero', crossParam_eq_edgeParameter,
    crossParam_eq_edgeParameter]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr
    (generic_edgeParameters_ne hn hP hfg hf.isCrossing hg.isCrossing)) hf.det_ne_zero')
    hg.det_ne_zero'

/-- Bridge B1 clause (1): `𝓤_n^SM ⊆ 𝓤_n^CV` — SM def:generic (all vertex triples in general
position, no three edge interiors concurrent) implies CV genericity. -/
theorem generic_of_sm (hn : 3 ≤ n) (hP : SM.Generic P) : Generic P := by
  have : Fact (1 < n) := ⟨by omega⟩
  refine ⟨g1_edge_ne_zero hn hP.1, ?_⟩
  intro m hm
  cases m with
  | g1 i => exact g1_turn_nonzero hn hP.1 i
  | g2 e i h => exact g1_area_ne_zero hP.1 (next_ne_self e).symm h.2.symm h.1.symm
  | g5 e f h => exact ((Member.relevant_g5_iff P e f h).mp hm).det_ne_zero
  | g4 e f g h =>
    obtain ⟨hf, hg⟩ := (Member.relevant_g4_iff P e f g h).mp hm
    exact sm_G4_ne_zero hn hP hf hg h.2.2.1
  | g3 e f g h =>
    obtain ⟨hef, hfg, heg⟩ := (Member.relevant_g3_iff P e f g h).mp hm
    rw [Member.eval_g3, ← neg_ne_zero, ← G4_eq_neg_G3]
    exact sm_G4_ne_zero hn hP hef heg hfg.ne

theorem genericLocus_sm_subset (hn : 3 ≤ n) :
    {P : LabelledTuple n | SM.Generic P} ⊆ genericLocus n :=
  fun _ hP => generic_of_sm hn hP

/-- The printed "equivalently" of def:generic (A) (d1_setup.tex:224–226). -/
theorem generic_iff_unconditional_active (P : LabelledTuple n) :
    Generic P ↔ IsPolygon P ∧ (∀ m : Member n, m.Unconditional → m.eval P ≠ 0) ∧
      (∀ m : Member n, m.Conditional → m.Active P → m.eval P ≠ 0) := by
  constructor
  · rintro ⟨hpoly, h⟩
    exact ⟨hpoly, fun m hm => h m (Or.inl hm), fun m _ hm => h m (Or.inr hm)⟩
  · rintro ⟨hpoly, h1, h2⟩
    refine ⟨hpoly, fun m hm => ?_⟩
    rcases hm with hu | ha
    · exact h1 m hu
    · by_cases hu : m.Unconditional
      · exact h1 m hu
      · exact h2 m hu ha

theorem Member.relevant_iff_conditional (P : LabelledTuple n) (m : Member n) :
    m.Relevant P ↔ m.Unconditional ∨ (m.Conditional ∧ m.Active P) := by
  constructor
  · rintro (hu | ha)
    · exact Or.inl hu
    · by_cases hu : m.Unconditional
      · exact Or.inl hu
      · exact Or.inr ⟨hu, ha⟩
  · rintro (hu | ⟨_, ha⟩)
    · exact Or.inl hu
    · exact Or.inr ha

/-- prop:fidelity (ii) (d1_setup.tex:270–271, 285–288): `𝓤_n = 𝓤_n^♭`. -/
theorem generic_iff_flat (P : LabelledTuple n) : Generic P ↔ P ∈ flatGenericLocus n := by
  constructor
  · rintro ⟨hpoly, h⟩
    exact ⟨hpoly, fun m _ hm => h m hm⟩
  · rintro ⟨hpoly, h⟩
    refine ⟨hpoly, fun m hm => ?_⟩
    cases m
    case g5 e f h5 => exact ((Member.relevant_g5_iff P e f h5).mp hm).det_ne_zero
    all_goals exact h _ (fun h' => h') hm

theorem genericLocus_eq_flat : genericLocus n = flatGenericLocus n :=
  Set.ext fun P => generic_iff_flat P

theorem mem_genericLocus (P : LabelledTuple n) : P ∈ genericLocus n ↔ Generic P := Iff.rfl

theorem chamber_subset (P : LabelledTuple n) : chamber P ⊆ genericLocus n :=
  connectedComponentIn_subset _ _

theorem mem_chamber_self (hP : Generic P) : P ∈ chamber P := mem_connectedComponentIn hP

theorem chamber_eq_empty (hP : ¬ Generic P) : chamber P = ∅ := connectedComponentIn_eq_empty hP

theorem isPreconnected_chamber (P : LabelledTuple n) : IsPreconnected (chamber P) :=
  isPreconnected_connectedComponentIn

theorem isConnected_chamber (hP : Generic P) : IsConnected (chamber P) :=
  isConnected_connectedComponentIn_iff.mpr hP

theorem subset_chamber {S : Set (LabelledTuple n)} (hS : IsPreconnected S)
    (hSU : S ⊆ genericLocus n) (hPS : P ∈ S) : S ⊆ chamber P :=
  hS.subset_connectedComponentIn hPS hSU

theorem chamber_eq_of_mem {Q : LabelledTuple n} (hQ : Q ∈ chamber P) : chamber Q = chamber P :=
  (connectedComponentIn_eq hQ).symm

/-- CV def:generic (d1_setup.tex:220–238) with rem:genericmeans and prop:fidelity, clause by clause. -/
structure GenericData : Prop where
  /-- (A) "A member of `𝓖` is *relevant* at a polygon `P` if it is unconditional, or if it is
  conditional and active at `P`" (221–223). -/
  relevant : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (m : Member n),
    m.Relevant P ↔ m.Unconditional ∨ (m.Conditional ∧ m.Active P)
  /-- (A) "A polygon `P` (Definition def:polygon) is *generic* if every member relevant at `P` is
  nonzero at `P`" (223–224). -/
  generic : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n),
    Generic P ↔ IsPolygon P ∧ ∀ m : Member n, m.Relevant P → m.eval P ≠ 0
  /-- (A) "equivalently, if every unconditional member of `𝓖` is nonzero at `P` and every
  conditional member that is active at `P` is nonzero at `P`" (224–226). -/
  generic_iff : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n),
    Generic P ↔ IsPolygon P ∧ (∀ m : Member n, m.Unconditional → m.eval P ≠ 0) ∧
      (∀ m : Member n, m.Conditional → m.Active P → m.eval P ≠ 0)
  /-- (A) "We write `𝓤_n` for the set of generic polygons on `n` vertices" (226–227). -/
  locus : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n), P ∈ genericLocus n ↔ Generic P
  /-- (B) "A *chamber* is a connected component of the set `𝓤_n` of generic polygons on `n`
  vertices" (229–231): `chamber P` is the connected component of `P` in `𝓤_n`. -/
  chamber_def : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n),
    chamber P = connectedComponentIn (genericLocus n) P
  /-- (B) The connected-component clauses: `chamber P ⊆ 𝓤_n`; a generic `P` lies in its chamber,
  which is connected; a non-generic `P` has empty chamber; every preconnected subset of `𝓤_n`
  through `P` lies in `chamber P`; points of one chamber have the same chamber. -/
  chamber_component : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n),
    chamber P ⊆ genericLocus n ∧
    (Generic P → P ∈ chamber P ∧ IsConnected (chamber P)) ∧
    (¬ Generic P → chamber P = ∅) ∧
    (∀ S : Set (LabelledTuple n), IsPreconnected S → S ⊆ genericLocus n → P ∈ S →
      S ⊆ chamber P) ∧
    (∀ Q, Q ∈ chamber P → chamber Q = chamber P)
  /-- Bridge B1(1): `𝓤_n^SM ⊆ 𝓤_n^CV` (labelled loci, `n ≥ 3`) — SM def:generic implies CV
  def:generic, as a theorem. -/
  of_sm : ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ P : LabelledTuple n, SM.Generic P → Generic P
  /-- rem:genericmeans (240–256), item by item: nonzero turns (G1); no vertex on the line of a
  non-incident edge (G2); every active triple non-concurrent (G3, as SM's (G2)); no ties among the
  crossings along an edge (G4); every crossing transversal (G5); and the active pairs are exactly
  the actual crossings. -/
  consequences : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n), Generic P →
    (∀ i, turn P i ≠ 0) ∧
    (∀ k e, ¬ incident k e → ∀ t : ℝ, P k ≠ edgePoint P e t) ∧
    SM.G2 P ∧
    (∀ e f g, Crosses P e f → Crosses P e g → f ≠ g → crossParam P e f ≠ crossParam P e g) ∧
    (∀ e f, Crosses P e f → det (edge P e) (edge P f) ≠ 0) ∧
    (∀ e f, Crosses P e f ↔ IsCrossing P {e, f})
  /-- CV-generic polygons are weakly generic (SM def:weak), have SM's crossing geometry and are
  regular (CV def:regular = SM def:regular). -/
  weak : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n), Generic P →
    WeakGeneric P ∧ CrossingGeometry P ∧ Regular P ∧ SM.Regular P
  /-- prop:fidelity (263–288): (i) every active (G5) member is nonzero; (ii) `𝓤_n = 𝓤_n^♭`. -/
  fidelity : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n),
    (∀ e f, Crosses P e f → G5 P e f ≠ 0) ∧ (Generic P ↔ P ∈ flatGenericLocus n)

theorem generic_definition : GenericData where
  relevant := fun _ _ P m => Member.relevant_iff_conditional P m
  generic := fun _ _ _ => Iff.rfl
  generic_iff := fun _ _ P => generic_iff_unconditional_active P
  locus := fun _ _ _ => Iff.rfl
  chamber_def := fun _ _ _ => rfl
  chamber_component := fun _ _ P =>
    ⟨chamber_subset P, fun hP => ⟨mem_chamber_self hP, isConnected_chamber hP⟩,
      fun hP => chamber_eq_empty hP, fun _ hS hSU hPS => subset_chamber hS hSU hPS,
      fun _ hQ => chamber_eq_of_mem hQ⟩
  of_sm := fun _ _ hn _ hP => generic_of_sm hn hP
  consequences := fun _ _ _ hP =>
    ⟨hP.turn_ne_zero, fun _ _ hk t => hP.vertex_off_line hk t, hP.g2_sm,
      fun _ _ _ hf hg hfg => hP.crossParam_ne hf hg hfg, fun _ _ h => h.det_ne_zero,
      hP.crosses_iff⟩
  weak := fun _ _ _ hP => ⟨hP.weakGeneric, hP.crossingGeometry, hP.regular, hP.regular_sm⟩
  fidelity := fun _ _ P => ⟨fun _ _ h => h.det_ne_zero, generic_iff_flat P⟩

end CV

namespace CV

open SM

variable {n : ℕ}

/-! ## Row 133 — CV:def:diagrammatic (d1_setup.tex:315–344) -/

/-- The traversal circle of `P` (d1_setup.tex:306–312, "Traversing `P` once from `p_1` in the
direction of increasing index"), read edge by edge: a parameter `(i, s)` with `0 ≤ s < 1` names the
point `p_i + s d_i` of the edge `e_i`; each corner `p_i` has the single parameter `(i, 0)`. -/
def TraversalParam (p : ZMod n × ℝ) : Prop := 0 ≤ p.2 ∧ p.2 < 1

/-- The point of the traversal circle named by a parameter. -/
def traverse (P : LabelledTuple n) (p : ZMod n × ℝ) : Plane := edgePoint P p.1 p.2

/-- The preimages of a point `x` on the traversal circle. -/
def preimages (P : LabelledTuple n) (x : Plane) : Set (ZMod n × ℝ) :=
  {p | TraversalParam p ∧ traverse P p = x}

/-- A *self-intersection* of `P`: a point of the plane with two distinct preimages on the
traversal circle. -/
def IsSelfIntersection (P : LabelledTuple n) (x : Plane) : Prop :=
  ∃ p ∈ preimages P x, ∃ q ∈ preimages P x, p ≠ q

/-- The set of self-intersections of `P`. -/
def selfIntersections (P : LabelledTuple n) : Set Plane := {x | IsSelfIntersection P x}

/-- CV def:diagrammatic (d1_setup.tex:316–320): "A polygon `P` is *diagrammatic* if its
self-intersections are finitely many, each of them an isolated transverse crossing of two edges
with exactly two preimages on the traversal circle, no two of them sharing an image or a preimage,
none of them at a corner, and no vertex of `P` lying on an edge not incident to it."

Clause by clause: `IsPolygon P` (a polygon); the self-intersections are finitely many; each
self-intersection `x` is a crossing of two edges `i ≠ j` — its preimages are exactly two, one on
each edge — and transverse (`det(d_i, d_j) ≠ 0`); none is a corner `p_i`; no vertex lies on a
non-incident edge. "Exactly two preimages" is the clause that forbids two crossings sharing an
image (a triple point); a preimage determines its image, so two self-intersections at distinct
points never share a preimage. "Isolated" follows from finiteness (`Diagrammatic.isolated`). -/
def Diagrammatic (P : LabelledTuple n) : Prop :=
  IsPolygon P ∧
  (selfIntersections P).Finite ∧
  (∀ x ∈ selfIntersections P, ∃ (i j : ZMod n) (s t : ℝ), i ≠ j ∧
      preimages P x = {(i, s), (j, t)} ∧ det (edge P i) (edge P j) ≠ 0) ∧
  (∀ x ∈ selfIntersections P, ∀ i, x ≠ P i) ∧
  (∀ i e, ¬ incident i e → P i ∉ edgeSegment P e)

theorem mem_preimages (P : LabelledTuple n) (x : Plane) (i : ZMod n) (s : ℝ) :
    (i, s) ∈ preimages P x ↔ (0 ≤ s ∧ s < 1) ∧ edgePoint P i s = x := Iff.rfl

theorem mem_selfIntersections (P : LabelledTuple n) (x : Plane) :
    x ∈ selfIntersections P ↔ ∃ p ∈ preimages P x, ∃ q ∈ preimages P x, p ≠ q := Iff.rfl

/-- Two closed consecutive edges of a polygon with no vertex on a non-incident edge meet only at
their common corner (`n ≥ 3`): a second common point would make the second edge double back, and
then either `p_i` lies on `e_{i+1}` or `p_{i+2}` lies on `e_i`. -/
theorem meet_next_eq_corner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hvert : ∀ k e, ¬ incident k e → P k ∉ edgeSegment P e) (i : ZMod n) {x : Plane}
    (hx : x ∈ edgeSegment P i) (hx' : x ∈ edgeSegment P (i + 1)) : x = P (i + 1) := by
  have : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨s, hs0, hs1, hs⟩ := hx
  obtain ⟨u, hu0, hu1, hu⟩ := hx'
  by_cases hs1' : s = 1
  · rw [hs, hs1', edgePoint_one]
  by_cases hu0' : u = 0
  · rw [hu, hu0', edgePoint_zero]
  have hs1lt : s < 1 := lt_of_le_of_ne hs1 hs1'
  have hu0lt : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu0')
  have hnext : P (i + 1) = P i + edge P i := by simp [edge]
  have hrel : u • edge P (i + 1) = (s - 1) • edge P i := by
    have h1 : P i + s • edge P i = P (i + 1) + u • edge P (i + 1) := hs.symm.trans hu
    rw [hnext] at h1
    rw [sub_smul, one_smul]
    calc u • edge P (i + 1) = (P i + edge P i + u • edge P (i + 1)) - (P i + edge P i) := by abel
      _ = (P i + s • edge P i) - (P i + edge P i) := by rw [h1]
      _ = s • edge P i - edge P i := by abel
  have hdir : edge P (i + 1) = (u⁻¹ * (s - 1)) • edge P i := by
    rw [mul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hu0lt.ne', one_smul]
  have hnot_inc1 : ¬ incident i (i + 1) := by
    rintro (h | h)
    · exact prev_ne_next hn i h.symm
    · exact next_ne_self i h
  have hnot_inc2 : ¬ incident (i + 1 + 1) i := by
    rintro (h | h)
    · rw [add_sub_cancel_right] at h
      exact next_ne_self i h.symm
    · have h2 := prev_ne_next hn (i + 1)
      rw [add_sub_cancel_right] at h2
      exact h2 h
  exfalso
  have hs1ne : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1')
  rcases le_or_gt u (1 - s) with hle | hlt
  · apply hvert i (i + 1) hnot_inc1
    refine ⟨u / (1 - s), div_nonneg hu0 (by linarith), (div_le_one (by linarith)).mpr hle, ?_⟩
    rw [edgePoint, hdir, smul_smul, hnext]
    have hc : u / (1 - s) * (u⁻¹ * (s - 1)) = -1 := by
      field_simp
      ring
    rw [hc, neg_one_smul]
    abel
  · apply hvert (i + 1 + 1) i hnot_inc2
    refine ⟨1 + u⁻¹ * (s - 1), ?_, ?_, ?_⟩
    · have h1 : u⁻¹ * (s - 1) = -((1 - s) / u) := by ring
      have h2 := (div_lt_one hu0lt).mpr hlt
      rw [h1]
      linarith
    · have h1 : u⁻¹ * (s - 1) < 0 := mul_neg_of_pos_of_neg (inv_pos.mpr hu0lt) (by linarith)
      linarith
    · have h2 : P (i + 1 + 1) = P (i + 1) + edge P (i + 1) := by simp [edge]
      rw [edgePoint, h2, hdir, hnext, add_smul, one_smul]
      abel

/-- The geometry of a self-intersection under SM's `CrossingGeometry` and the vertex clause: its
two preimages lie on distinct remote edges, in their interiors, and the crossing is transverse. -/
theorem selfIntersection_geometry (hn : 3 ≤ n) {P : LabelledTuple n} (hCG : CrossingGeometry P)
    (hvert : ∀ k e, ¬ incident k e → P k ∉ edgeSegment P e) {x : Plane} {i j : ZMod n} {s t : ℝ}
    (hp : (i, s) ∈ preimages P x) (hq : (j, t) ∈ preimages P x) (hne : (i, s) ≠ (j, t)) :
    i ≠ j ∧ remote i j ∧ x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧
      det (edge P i) (edge P j) ≠ 0 := by
  obtain ⟨⟨hs0, hs1⟩, hs⟩ := hp
  obtain ⟨⟨ht0, ht1⟩, ht⟩ := hq
  change edgePoint P i s = x at hs
  change edgePoint P j t = x at ht
  have hxi : x ∈ edgeSegment P i := ⟨s, hs0, hs1.le, hs.symm⟩
  have hxj : x ∈ edgeSegment P j := ⟨t, ht0, ht1.le, ht.symm⟩
  have hij : i ≠ j := by
    rintro rfl
    have hst : s = t := edgePoint_injective (hCG.1 i) (hs.trans ht.symm)
    exact hne (by rw [hst])
  have hr : remote i j := by
    intro hadj
    rcases adjacent_distinct_cases hij hadj with rfl | rfl
    · have hx := meet_next_eq_corner hn hvert i hxi hxj
      have h1 : s = 1 :=
        edgePoint_injective (hCG.1 i) (hs.trans (hx.trans (edgePoint_one P i).symm))
      exact hs1.ne h1
    · have hx := meet_next_eq_corner hn hvert j hxj hxi
      have h1 : t = 1 :=
        edgePoint_injective (hCG.1 j) (ht.trans (hx.trans (edgePoint_one P j).symm))
      exact ht1.ne h1
  obtain ⟨hii, hjj, hd⟩ := hCG.2.1 i j hr x hxi hxj
  exact ⟨hij, hr, hii, hjj, hd⟩

variable [NeZero n]

/-- Fidelity fact F3, one direction: SM's `CrossingGeometry` with no vertex on a non-incident edge
gives a diagrammatic polygon (`n ≥ 3`). -/
theorem diagrammatic_of_crossingGeometry (hn : 3 ≤ n) {P : LabelledTuple n}
    (hCG : CrossingGeometry P) (hvert : ∀ k e, ¬ incident k e → P k ∉ edgeSegment P e) :
    Diagrammatic P := by
  refine ⟨hCG.1, ?_, ?_, ?_, hvert⟩
  · have hsub : selfIntersections P ⊆ ⋃ p : ZMod n × ZMod n,
        {x | remote p.1 p.2 ∧ x ∈ edgeSegment P p.1 ∧ x ∈ edgeSegment P p.2} := by
      rintro x ⟨⟨i, s⟩, hp, ⟨j, t⟩, hq, hne⟩
      obtain ⟨_, hr, hii, hjj, _⟩ := selfIntersection_geometry hn hCG hvert hp hq hne
      exact Set.mem_iUnion.mpr ⟨(i, j), hr, edgeInterior_subset_edgeSegment P i hii,
        edgeInterior_subset_edgeSegment P j hjj⟩
    refine Set.Finite.subset (Set.finite_iUnion fun p => ?_) hsub
    apply Set.Subsingleton.finite
    rintro x ⟨hr, hxi, hxj⟩ y ⟨_, hyi, hyj⟩
    exact transverse_segments_unique (hCG.2.1 p.1 p.2 hr x hxi hxj).2.2 hxi hxj hyi hyj
  · rintro x ⟨⟨i, s⟩, hp, ⟨j, t⟩, hq, hne⟩
    obtain ⟨hij, hr, hii, hjj, hd⟩ := selfIntersection_geometry hn hCG hvert hp hq hne
    refine ⟨i, j, s, t, hij, ?_, hd⟩
    ext ⟨k, u⟩
    constructor
    · intro hk
      obtain ⟨⟨hu0, hu1⟩, hku⟩ := hk
      change edgePoint P k u = x at hku
      by_cases hki : k = i
      · subst hki
        have hus : u = s := edgePoint_injective (hCG.1 k) (hku.trans hp.2.symm)
        simp [hus]
      by_cases hkj : k = j
      · subst hkj
        have hut : u = t := edgePoint_injective (hCG.1 k) (hku.trans hq.2.symm)
        simp [hut]
      exfalso
      have hxk : x ∈ edgeSegment P k := ⟨u, hu0, hu1.le, hku.symm⟩
      have hkk : x ∈ edgeInterior P k := by
        by_cases hrk : remote i k
        · exact (hCG.2.1 i k hrk x (edgeInterior_subset_edgeSegment P i hii) hxk).2.1
        · exfalso
          rcases adjacent_distinct_cases (Ne.symm hki) (not_not.mp hrk) with rfl | rfl
          · have hx := meet_next_eq_corner hn hvert i
              (edgeInterior_subset_edgeSegment P i hii) hxk
            obtain ⟨s', _, hs'1, hs'⟩ := hii
            have h1 : s' = 1 := edgePoint_injective (hCG.1 i)
              (hs'.symm.trans (hx.trans (edgePoint_one P i).symm))
            exact hs'1.ne h1
          · have hx := meet_next_eq_corner hn hvert k hxk
              (edgeInterior_subset_edgeSegment P (k + 1) hii)
            obtain ⟨s', hs'0, _, hs'⟩ := hii
            have h0 : s' = 0 := edgePoint_injective (hCG.1 (k + 1))
              (hs'.symm.trans (hx.trans (edgePoint_zero P (k + 1)).symm))
            exact hs'0.ne' h0
      exact hCG.2.2 ⟨i, j, k, x, hij, Ne.symm hkj, Ne.symm hki, hii, hjj, hkk⟩
    · intro hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp
      · exact hq
  · rintro x ⟨⟨i, s⟩, hp, ⟨j, t⟩, hq, hne⟩ m hxm
    obtain ⟨_, _, hii, _, _⟩ := selfIntersection_geometry hn hCG hvert hp hq hne
    by_cases hinc : incident m i
    · rcases hinc with h | h
      · subst h
        obtain ⟨s', _, hs'1, hs'⟩ := hii
        have hPm : P m = edgePoint P (m - 1) 1 := by rw [edgePoint_one, sub_add_cancel]
        have h1 : s' = 1 := edgePoint_injective (hCG.1 _) (hs'.symm.trans (hxm.trans hPm))
        exact hs'1.ne h1
      · subst h
        obtain ⟨s', hs'0, _, hs'⟩ := hii
        have h0 : s' = 0 :=
          edgePoint_injective (hCG.1 _) (hs'.symm.trans (hxm.trans (edgePoint_zero P _).symm))
        exact hs'0.ne' h0
    · exact hvert m i hinc (hxm ▸ edgeInterior_subset_edgeSegment P i hii)

omit [NeZero n] in
/-- Fidelity fact F3, the other direction: a diagrammatic polygon has SM's `CrossingGeometry`
(nonzero edges; remote edges meet, if at all, in interior transverse points; no three edge
interiors concur). Hence the geometric Gauss word of SM (`geometricGaussWord`) exists on this class,
as the printed text asserts (d1_setup.tex:306–312, 341–344). -/
theorem Diagrammatic.crossingGeometry {P : LabelledTuple n} (hD : Diagrammatic P) :
    CrossingGeometry P := by
  obtain ⟨hpoly, _, htwo, hcorner, hvert⟩ := hD
  refine ⟨hpoly, ?_, ?_⟩
  · intro i j hr x hxi hxj
    obtain ⟨s, hs0, hs1, hs⟩ := hxi
    obtain ⟨t, ht0, ht1, ht⟩ := hxj
    obtain ⟨hji, hji1, hj1i, hj1i1⟩ := remote_endpoints i j hr
    have hs1' : s ≠ 1 := by
      rintro rfl
      rw [edgePoint_one] at hs
      exact hvert (i + 1) j ((nonincident_iff _ _).mpr ⟨hji1.symm, hj1i1.symm⟩)
        (hs ▸ ⟨t, ht0, ht1, ht⟩)
    have ht1' : t ≠ 1 := by
      rintro rfl
      rw [edgePoint_one] at ht
      exact hvert (j + 1) i ((nonincident_iff _ _).mpr ⟨hj1i, hj1i1⟩)
        (ht ▸ ⟨s, hs0, hs1, hs⟩)
    have hp : (i, s) ∈ preimages P x := ⟨⟨hs0, lt_of_le_of_ne hs1 hs1'⟩, hs.symm⟩
    have hq : (j, t) ∈ preimages P x := ⟨⟨ht0, lt_of_le_of_ne ht1 ht1'⟩, ht.symm⟩
    have hne : (i, s) ≠ (j, t) := fun h => hji (congrArg Prod.fst h).symm
    have hx : x ∈ selfIntersections P := ⟨(i, s), hp, (j, t), hq, hne⟩
    have hs0' : s ≠ 0 := by
      rintro rfl
      rw [edgePoint_zero] at hs
      exact hcorner x hx i hs
    have ht0' : t ≠ 0 := by
      rintro rfl
      rw [edgePoint_zero] at ht
      exact hcorner x hx j ht
    refine ⟨⟨s, lt_of_le_of_ne hs0 (Ne.symm hs0'), lt_of_le_of_ne hs1 hs1', hs⟩,
      ⟨t, lt_of_le_of_ne ht0 (Ne.symm ht0'), lt_of_le_of_ne ht1 ht1', ht⟩, ?_⟩
    obtain ⟨i', j', s', t', _, hpre, hd⟩ := htwo x hx
    have hp' := hp
    have hq' := hq
    rw [hpre] at hp' hq'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp' hq'
    rcases hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · exact hd
    · rw [det_swap]
      exact neg_ne_zero.mpr hd
    · exact absurd rfl hne
  · rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
    obtain ⟨s, hs0, hs1, hs⟩ := hi
    obtain ⟨t, ht0, ht1, ht⟩ := hj
    obtain ⟨u, hu0, hu1, hu⟩ := hk
    have hpi : (i, s) ∈ preimages P x := ⟨⟨hs0.le, hs1⟩, hs.symm⟩
    have hpj : (j, t) ∈ preimages P x := ⟨⟨ht0.le, ht1⟩, ht.symm⟩
    have hpk : (k, u) ∈ preimages P x := ⟨⟨hu0.le, hu1⟩, hu.symm⟩
    have hx : x ∈ selfIntersections P :=
      ⟨(i, s), hpi, (j, t), hpj, fun h => hij (congrArg Prod.fst h)⟩
    obtain ⟨i', j', s', t', _, hpre, _⟩ := htwo x hx
    rw [hpre] at hpi hpj hpk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hpi hpj hpk
    rcases hpi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hpj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first
      | exact absurd rfl hij
      | exact absurd rfl hjk
      | exact absurd rfl hik

/-- Fidelity fact F3 (`n ≥ 3`): CV's diagrammatic class is exactly SM's `CrossingGeometry` together
with "no vertex of `P` lying on an edge not incident to it". -/
theorem diagrammatic_iff (hn : 3 ≤ n) (P : LabelledTuple n) :
    Diagrammatic P ↔ CrossingGeometry P ∧ ∀ i e, ¬ incident i e → P i ∉ edgeSegment P e :=
  ⟨fun hD => ⟨hD.crossingGeometry, hD.2.2.2.2⟩,
    fun h => diagrammatic_of_crossingGeometry hn h.1 h.2⟩

/-- "Every generic polygon is diagrammatic" (d1_setup.tex:329–332). -/
theorem Generic.diagrammatic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Diagrammatic P :=
  diagrammatic_of_crossingGeometry hn hP.crossingGeometry fun _ _ hk => hP.vertex_not_mem_edge hk

/-- SM weakly generic polygons (SM def:weak) are diagrammatic. -/
theorem diagrammatic_of_weak (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P) :
    Diagrammatic P :=
  diagrammatic_of_crossingGeometry hn (weak_crossingGeometry hW) hW.2.2.1

/-- "So is the polygon at a simple positive flat wall, whose only degeneracy is a vanishing turn
with the middle vertex *inside* the segment" (d1_setup.tex:332–334): the centre of an SM flat wall
germ (`WallGerm.FlatAt`, whose data include `StrictBetween` for the middle vertex). -/
theorem diagrammatic_of_flatAt (g : WallGerm n) (j : ZMod n) (hf : g.FlatAt j) :
    Diagrammatic g.center := by
  obtain ⟨hn4, hz, hc, hb, _⟩ := hf
  exact diagrammatic_of_crossingGeometry (by omega) (flat_crossingGeometry hn4 hz hb hc)
    (flat_nonincident_vertex_exclusion hn4 hz hb)

omit [NeZero n] in
/-- "isolated": a self-intersection of a diagrammatic polygon has a neighbourhood containing no
other self-intersection (from finiteness). -/
theorem Diagrammatic.isolated {P : LabelledTuple n} (hD : Diagrammatic P) {x : Plane}
    (hx : x ∈ selfIntersections P) : ∃ U ∈ nhds x, U ∩ selfIntersections P = {x} := by
  have hfin : (selfIntersections P \ {x}).Finite := hD.2.1.subset Set.sdiff_subset
  refine ⟨(selfIntersections P \ {x})ᶜ, hfin.isClosed.isOpen_compl.mem_nhds (by simp), ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyS⟩
    by_contra hyx
    exact hy ⟨hyS, hyx⟩
  · rintro rfl
    exact ⟨fun h => h.2 rfl, hx⟩

/-- The tuple `((0,0),(2,0),(1,0),(0,1))` of d1_setup.tex:337–340 (indices read from `0`). -/
def collinearExample : LabelledTuple 4 :=
  (![((0 : ℝ), (0 : ℝ)), (2, 0), (1, 0), (0, 1)] : Fin 4 → Plane)

/-- The example of d1_setup.tex:337–340, "`((0,0),(2,0),(1,0),(0,1))`, which is not diagrammatic":
its vertex `p_2 = (1,0)` lies on the non-incident edge `e_0 = [(0,0),(2,0)]`. -/
theorem not_diagrammatic_collinearExample : ¬ Diagrammatic collinearExample := by
  intro hD
  apply hD.2.2.2.2 2 0 (by unfold incident; decide)
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  ext <;> simp [collinearExample, edgePoint, edge]

/-- CV def:diagrammatic (d1_setup.tex:315–344), clause by clause. -/
structure DiagrammaticData : Prop where
  /-- The traversal circle (306–312): the parameter `(i, s)`, `0 ≤ s < 1`, names the point
  `p_i + s d_i`, and `preimages P x` is the set of parameters naming `x`. -/
  traversal : ∀ (n : ℕ) (P : LabelledTuple n) (x : Plane) (i : ZMod n) (s : ℝ),
    (i, s) ∈ preimages P x ↔ (0 ≤ s ∧ s < 1) ∧ edgePoint P i s = x
  /-- A self-intersection is a point with two distinct preimages. -/
  self_intersection : ∀ (n : ℕ) (P : LabelledTuple n) (x : Plane),
    x ∈ selfIntersections P ↔ ∃ p ∈ preimages P x, ∃ q ∈ preimages P x, p ≠ q
  /-- "A polygon `P` is *diagrammatic* if its self-intersections are finitely many, each of them an
  isolated transverse crossing of two edges with exactly two preimages on the traversal circle, no
  two of them sharing an image or a preimage, none of them at a corner, and no vertex of `P` lying
  on an edge not incident to it" (316–320). -/
  diagrammatic : ∀ (n : ℕ) (P : LabelledTuple n), Diagrammatic P ↔
    IsPolygon P ∧
    (selfIntersections P).Finite ∧
    (∀ x ∈ selfIntersections P, ∃ (i j : ZMod n) (s t : ℝ), i ≠ j ∧
        preimages P x = {(i, s), (j, t)} ∧ det (edge P i) (edge P j) ≠ 0) ∧
    (∀ x ∈ selfIntersections P, ∀ i, x ≠ P i) ∧
    (∀ i e, ¬ incident i e → P i ∉ edgeSegment P e)
  /-- "isolated" (317): each self-intersection has a neighbourhood containing no other. -/
  isolated : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n), Diagrammatic P →
    ∀ x ∈ selfIntersections P, ∃ U ∈ nhds x, U ∩ selfIntersections P = {x}
  /-- Fidelity fact F3 (`n ≥ 3`): in SM vocabulary the class is `CrossingGeometry P` together with
  "no vertex on a non-incident edge" — the class on which SM's geometric Gauss word is defined
  (341–344: "the Gauss word, the interlacement graph, … are read off a diagrammatic polygon"). -/
  iff_crossing_geometry : ∀ (n : ℕ) [NeZero n] (_hn : 3 ≤ n) (P : LabelledTuple n),
    Diagrammatic P ↔ CrossingGeometry P ∧ ∀ i e, ¬ incident i e → P i ∉ edgeSegment P e
  /-- "Every generic polygon is diagrammatic" (329–332), and so is every SM weakly generic polygon. -/
  of_generic : ∀ (n : ℕ) [NeZero n] (_hn : 3 ≤ n) (P : LabelledTuple n), Generic P → Diagrammatic P
  of_weak : ∀ (n : ℕ) [NeZero n] (_hn : 3 ≤ n) (P : LabelledTuple n), WeakGeneric P → Diagrammatic P
  /-- "So is the polygon at a simple positive flat wall, whose only degeneracy is a vanishing turn
  with the middle vertex inside the segment" (332–334): the centre of an SM flat wall germ. -/
  of_flat : ∀ (n : ℕ) [NeZero n] (g : WallGerm n) (j : ZMod n), g.FlatAt j → Diagrammatic g.center
  /-- The printed non-example `((0,0),(2,0),(1,0),(0,1))` (337–340). -/
  counterexample : ¬ Diagrammatic collinearExample

theorem diagrammatic_definition : DiagrammaticData where
  traversal := fun _ _ _ _ _ => Iff.rfl
  self_intersection := fun _ _ _ => Iff.rfl
  diagrammatic := fun _ _ => Iff.rfl
  isolated := fun _ _ _ hD _ hx => hD.isolated hx
  iff_crossing_geometry := fun _ _ hn P => diagrammatic_iff hn P
  of_generic := fun _ _ hn _ hP => hP.diagrammatic hn
  of_weak := fun _ _ hn _ hW => diagrammatic_of_weak hn hW
  of_flat := fun _ _ g j hf => diagrammatic_of_flatAt g j hf
  counterexample := not_diagrammatic_collinearExample

end CV

