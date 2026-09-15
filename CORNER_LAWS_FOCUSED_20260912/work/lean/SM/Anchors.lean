import SM.SoftRotation
import SM.Admissible
import SM.Fibres

/-! Towards def:anchors (sm-5-transport.tex:373) and prop:anchors-exist (sm-5-transport.tex:399). Written 2026-09-13 by a Claude Code
prover subagent of the pod executor (workflow prove-transport-lane-2 / prove:anchors), checked with `lake env lean` (sorry-free, standard
axioms) and ported verbatim from work/drafts/Anchors.lean (only this header added and #print lines removed). -/

/-! Source def:anchors (reference/SM/sm-5-transport.tex:373) and prop:anchors-exist
(sm-5-transport.tex:399), frame SM15. Main declarations: `SM.SoftAnchorData`, `SM.ZeroAnchor`,
`SM.LoopAnchor`, `SM.LoopAnchorZero`, `SM.Anchor` (def:anchors) and `SM.anchors_exist`
(prop:anchors-exist).

Notation. The admissible pair `(n, r)` of the source is `((m : ℤ) + 1, r)` where `m` is the vertex
count of the parent (so `n - 1 = m`, `n ≥ 4 ↔ m ≥ 3`); an anchor is an `n`-gon
`softInsertion P j q ε : LabelledTuple (m + 1)` (`P^{(j,q)}_ε`, def:soft) with parent `P`, insertion
vertex `j : ZMod m`, admissible `q` (`SoftAdmissible P j q`), and `0 < ε < ε₀` where
`ε₀ = ε₀(P, j, q) > 0` is the bound of lem:soft-generic: on `(0, ε₀)` every `P_ε` is generic and
all of them lie in one (labelled) chamber (`labelledChamber`, `chamber`: def:chamber); the bound is
carried as data (`SoftAnchorData.bound`). The sectors are those of lem:soft-generic (iv) /
lem:soft-rotation: mixed `χ_- ≠ χ_+`, loop `χ_- = χ_+ = τ_j` with
`χ_- = softAttachmentMinus P j q`, `χ_+ = softAttachmentPlus P j q`, `τ_j = turn P j`.
`sgn r = SignType.sign r`. The soft edge of the anchor is its edge `E_j` at the label
`softOldIndex j j` (from `μ_j` to `μ_* = μ_{j+1}`, the label `softNewIndex j = softOldIndex j j + 1`
in the labelling of the anchor). -/

namespace SM

noncomputable section
open Filter Topology

variable {m : ℕ} [NeZero m]

/-! ### def:anchors -/

/-- The common data of an anchor (def:anchors): the parent `P` (a generic `m`-gon, `m = n - 1 ≥ 3`),
the insertion vertex `j`, an admissible vector `q`, the bound `ε₀ = ε₀(P, j, q) > 0` of
lem:soft-generic (on `(0, ε₀)` the insertion `P^{(j,q)}_ε` is generic and lies in one chamber), and
the parameter `0 < ε < ε₀`. The anchor itself is the `(m + 1)`-gon `softInsertion P j q ε`. -/
structure SoftAnchorData (m : ℕ) [NeZero m] where
  /-- the parent `P`, an `(n-1)`-gon -/
  parent : LabelledTuple m
  parent_card : 3 ≤ m
  parent_generic : Generic parent
  /-- the insertion vertex `j` -/
  vertex : ZMod m
  /-- the inserted vector `q` -/
  vector : Plane
  admissible : SoftAdmissible parent vertex vector
  /-- the geometric bound `ε₀(P, j, q)` of lem:soft-generic, part of the anchor data -/
  bound : ℝ
  bound_pos : 0 < bound
  /-- on `(0, ε₀)` the insertion is generic and lies in one chamber -/
  bound_spec : ∃ B : GenericTuple (m + 1), ∀ ε : ℝ, 0 < ε → ε < bound →
    ∃ hQ : Generic (softInsertion parent vertex vector ε),
      (⟨softInsertion parent vertex vector ε, hQ⟩ : GenericTuple (m + 1)) ∈ labelledChamber B ∧
      polygonProjection (⟨softInsertion parent vertex vector ε, hQ⟩ : GenericTuple (m + 1)) ∈
        chamber (polygonProjection B)
  /-- the parameter `ε` with `0 < ε < ε₀` -/
  param : ℝ
  param_pos : 0 < param
  param_lt : param < bound

/-- The anchor polygon `P^{(j,q)}_ε`, an `n`-gon (`n = m + 1`). -/
def SoftAnchorData.polygon (A : SoftAnchorData m) : LabelledTuple (m + 1) :=
  softInsertion A.parent A.vertex A.vector A.param

/-- The label of the soft edge `E_j` of the anchor (the edge from `μ_j` to `μ_*`). -/
def SoftAnchorData.softEdge (A : SoftAnchorData m) : ZMod (m + 1) :=
  softOldIndex A.vertex A.vertex

/-- (Z) A zero anchor for `(n, r)` (with `(n - 1, r)` admissible): a generic `n`-gon
`P^{(j,q)}_ε` in the mixed sector, for a generic `(n-1)`-gon `P` of rotation `r`, a vertex `j`,
admissible `q` and `0 < ε < ε₀`. -/
structure ZeroAnchor (m : ℕ) [NeZero m] (r : ℤ) extends SoftAnchorData m where
  parent_rotation : rotationNumber parent = (r : ℝ)
  /-- the mixed sector `χ_- ≠ χ_+` -/
  mixed : softAttachmentMinus parent vertex vector ≠ softAttachmentPlus parent vertex vector

/-- (L) A loop anchor for `(n, r)` (with `(n, r)` minimal, `|r| ≥ 2`): a generic `n`-gon
`P^{(j,q)}_ε` in the loop sector, for a generic `(n-1)`-gon `P` of rotation `r - sgn r` and a
vertex `j` with `τ_j(P) = -sgn r`. -/
structure LoopAnchor (m : ℕ) [NeZero m] (r : ℤ) extends SoftAnchorData m where
  parent_rotation : rotationNumber parent = (r : ℝ) - (SignType.sign r : ℝ)
  parent_turn : turn parent vertex = -SignType.sign r
  /-- the loop sector `χ_- = χ_+ = τ_j` -/
  loop : softAttachmentMinus parent vertex vector = turn parent vertex ∧
    softAttachmentPlus parent vertex vector = turn parent vertex

/-- (L₀) A loop anchor for `(n, r) = (4, 0)`: a generic `4`-gon `P^{(j,q)}_ε` in the loop sector
for a triangle `P` and any of its vertices `j`. -/
structure LoopAnchorZero (m : ℕ) [NeZero m] extends SoftAnchorData m where
  triangle : m = 3
  /-- the loop sector `χ_- = χ_+ = τ_j` -/
  loop : softAttachmentMinus parent vertex vector = turn parent vertex ∧
    softAttachmentPlus parent vertex vector = turn parent vertex

/-- def:anchors: an anchor for the admissible pair `(n, r) = ((m : ℤ) + 1, r)`, in the case that
applies: (Z) `(n - 1, r)` admissible, (L) `(n, r)` minimal with `|r| ≥ 2`, (L₀) `(n, r) = (4, 0)`. -/
inductive Anchor (m : ℕ) [NeZero m] (r : ℤ) : Type
  | zero (hZ : Admissible (m : ℤ) r) (A : ZeroAnchor m r) : Anchor m r
  | loop (hL : MinimalAdmissible ((m : ℤ) + 1) r) (hr : 2 ≤ |r|) (A : LoopAnchor m r) : Anchor m r
  | loopZero (hL₀ : ((m : ℤ) + 1, r) = (4, 0)) (A : LoopAnchorZero m) : Anchor m r

/-- The underlying data (parent, insertion vertex, vector, bound, parameter) of an anchor. -/
def Anchor.data {r : ℤ} : Anchor m r → SoftAnchorData m
  | .zero _ A => A.toSoftAnchorData
  | .loop _ _ A => A.toSoftAnchorData
  | .loopZero _ A => A.toSoftAnchorData

/-- The anchor as an `n`-gon. -/
def Anchor.polygon {r : ℤ} (A : Anchor m r) : LabelledTuple (m + 1) := A.data.polygon

/-- The parent `P` of an anchor. -/
def Anchor.parent {r : ℤ} (A : Anchor m r) : LabelledTuple m := A.data.parent

/-- The insertion vertex `j` of an anchor. -/
def Anchor.vertex {r : ℤ} (A : Anchor m r) : ZMod m := A.data.vertex

/-- The label of the soft edge `E_j` of an anchor. -/
def Anchor.softEdge {r : ℤ} (A : Anchor m r) : ZMod (m + 1) := A.data.softEdge

/-! ### Elementary facts about the anchor data -/

theorem SoftAnchorData.generic_of_lt (A : SoftAnchorData m) {ε : ℝ} (hε : 0 < ε)
    (hεb : ε < A.bound) : Generic (softInsertion A.parent A.vertex A.vector ε) := by
  obtain ⟨B, hB⟩ := A.bound_spec
  obtain ⟨hQ, -⟩ := hB ε hε hεb
  exact hQ

theorem SoftAnchorData.regular_of_lt (A : SoftAnchorData m) {ε : ℝ} (hε : 0 < ε)
    (hεb : ε < A.bound) : Regular (softInsertion A.parent A.vertex A.vector ε) :=
  generic_regular (by have := A.parent_card; omega) (A.generic_of_lt hε hεb)

/-- The anchor is generic. -/
theorem SoftAnchorData.polygon_generic (A : SoftAnchorData m) : Generic A.polygon :=
  A.generic_of_lt A.param_pos A.param_lt

/-- The soft edge of the anchor is its edge `E_j`: the edge `ε q` from `μ_j` to
`μ_* = μ_j + ε q`, which sits at the next label `softNewIndex j`. -/
theorem SoftAnchorData.softEdge_spec (A : SoftAnchorData m) :
    A.polygon A.softEdge = A.parent A.vertex ∧
    A.softEdge + 1 = softNewIndex A.vertex ∧
    A.polygon (A.softEdge + 1) = A.parent A.vertex + A.param • A.vector ∧
    edge A.polygon A.softEdge = A.param • A.vector := by
  refine ⟨softInsertion_old _ _ _ _ _, softOldIndex_attachment_next _, ?_,
    edge_softInsertion_soft _ _ _ _⟩
  rw [SoftAnchorData.softEdge, softOldIndex_attachment_next]
  exact softInsertion_new _ _ _ _

/-- The rotation law of lem:soft-rotation on the whole interval `(0, ε₀)` of the anchor data. -/
theorem SoftAnchorData.rotation_law (A : SoftAnchorData m) :
    (((softAttachmentMinus A.parent A.vertex A.vector = -turn A.parent A.vertex ∧
        softAttachmentPlus A.parent A.vertex A.vector = -turn A.parent A.vertex) ∨
        softAttachmentMinus A.parent A.vertex A.vector ≠
          softAttachmentPlus A.parent A.vertex A.vector) →
      rotationNumber A.polygon = rotationNumber A.parent) ∧
    ((softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
        softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex) →
      rotationNumber A.polygon = rotationNumber A.parent - (turn A.parent A.vertex : ℝ)) :=
  soft_rotation_of_regular_interval A.parent_card A.parent_generic A.vertex A.vector A.admissible
    A.bound_pos (fun _ hε hεb => A.regular_of_lt hε hεb) A.param_pos A.param_lt

/-- A zero anchor has the rotation `r` of its parent. -/
theorem ZeroAnchor.polygon_rotation {r : ℤ} (A : ZeroAnchor m r) :
    rotationNumber A.polygon = (r : ℝ) := by
  rw [A.toSoftAnchorData.rotation_law.1 (Or.inr A.mixed), A.parent_rotation]

/-- A loop anchor has rotation `(r - sgn r) - (-sgn r) = r`. -/
theorem LoopAnchor.polygon_rotation {r : ℤ} (A : LoopAnchor m r) :
    rotationNumber A.polygon = (r : ℝ) := by
  rw [A.toSoftAnchorData.rotation_law.2 A.loop, A.parent_rotation, A.parent_turn]
  simp

/-- A loop anchor over a triangle has rotation `τ_j - τ_j = 0`. -/
theorem LoopAnchorZero.polygon_rotation (A : LoopAnchorZero m) :
    rotationNumber A.polygon = 0 := by
  rw [A.toSoftAnchorData.rotation_law.2 A.loop]
  have h3 := A.triangle
  have hreg := generic_regular A.parent_card A.parent_generic
  subst h3
  rw [(rotationNumber_triangle hreg).1 A.vertex]
  ring

/-! ### Sign lemmas -/

theorem anchor_signType_ne_neg_self : ∀ s : SignType, s ≠ 0 → s ≠ -s := by
  decide

theorem anchor_signType_mixed_cases (a b s : SignType) (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) : -a = s ∨ -b = s := by
  revert ha hb hs hab
  cases a <;> cases b <;> cases s <;> decide

/-! ### Sectors contain admissible vectors -/

/-- If `w` is annihilated by both `det u ·` and `det v ·` for independent `u, v`, then `w = 0`. -/
theorem anchor_det_zero_of_both {u v w : Plane} (huv : det u v ≠ 0) (hu : det u w = 0)
    (hv : det v w = 0) : w = 0 := by
  have h := det_cramer u v w
  rw [det_swap v w, hv, hu] at h
  simp only [neg_zero, zero_smul, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_left huv

/-- Along the ray `u + b v`, the condition `det (u + b v) w = 0` (for `w ≠ 0`) holds for at
most one `b`. -/
theorem anchor_roots_finite {u v w : Plane} (huv : det u v ≠ 0) (hw : w ≠ 0) :
    {b : ℝ | det (u + b • v) w = 0}.Finite := by
  have hlin : ∀ b : ℝ, det (u + b • v) w = det u w + b * det v w := by
    intro b; simp [det]; ring
  by_cases hv : det v w = 0
  · have hu : det u w ≠ 0 := fun hu => hw (anchor_det_zero_of_both huv hu hv)
    have : {b : ℝ | det (u + b • v) w = 0} = ∅ := by
      ext b
      simp [hlin, hv, hu]
    rw [this]
    exact Set.finite_empty
  · apply Set.Finite.subset (Set.finite_singleton (-det u w / det v w))
    intro b hb
    have hb' : det u w + b * det v w = 0 := (hlin b).symm.trans hb
    show b = -det u w / det v w
    field_simp
    linarith

/-- Every open cone `openCone u v` (`det u v ≠ 0`) contains a vector `q` with
`det (q, μ_k - μ_j) ≠ 0` for all `k ≠ j`: admissibility removes finitely many lines. -/
theorem anchor_exists_in_cone_avoiding (P : LabelledTuple m) (j : ZMod m)
    (hinj : ∀ k, k ≠ j → P k - P j ≠ 0) {u v : Plane} (huv : det u v ≠ 0) :
    ∃ q ∈ openCone u v, ∀ k, k ≠ j → det q (P k - P j) ≠ 0 := by
  classical
  let S : Set ℝ := ⋃ k ∈ ((Finset.univ : Finset (ZMod m)).filter (fun k => k ≠ j)),
    {b : ℝ | det (u + b • v) (P k - P j) = 0}
  have hS : S.Finite := by
    apply Set.Finite.biUnion (Finset.finite_toSet _)
    intro k hk
    have hk' : k ≠ j := by simpa using hk
    exact anchor_roots_finite huv (hinj k hk')
  obtain ⟨b, hb, hbS⟩ := (Set.Ioi_infinite (0 : ℝ)).exists_notMem_finite hS
  refine ⟨u + b • v, ⟨1, b, one_pos, hb, by rw [one_smul]⟩, ?_⟩
  intro k hk hzero
  apply hbS
  exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, hzero⟩

theorem anchor_vertices_sub_ne_zero (hn : 3 ≤ m) {P : LabelledTuple m} (hP : Generic P)
    (j : ZMod m) : ∀ k, k ≠ j → P k - P j ≠ 0 := by
  intro k hk h
  exact hk (g1_vertices_injective hn hP.1 (sub_eq_zero.mp h))

/-- The loop sector contains admissible vectors. -/
theorem anchor_loop_sector_nonempty (hn : 3 ≤ m) {P : LabelledTuple m} (hP : Generic P)
    (j : ZMod m) :
    ∃ q : Plane, SoftAdmissible P j q ∧
      (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) := by
  have : Fact (1 < m) := ⟨by omega⟩
  have hD : det (edge P (j - 1)) (edge P j) ≠ 0 := g1_turn_nonzero hn hP.1 j
  have hD' : det (-edge P (j - 1)) (-edge P j) ≠ 0 := by rwa [det_neg_neg]
  obtain ⟨q, hq, hav⟩ :=
    anchor_exists_in_cone_avoiding P j (anchor_vertices_sub_ne_zero hn hP j) hD'
  have hloop := (soft_loop_sector_iff hn hP.1 j q).mpr hq
  have hτ : turn P j ≠ 0 := soft_turn_ne_zero hn hP.1 j
  refine ⟨q, ⟨?_, ?_, hav⟩, hloop⟩
  · intro h0
    apply hτ
    rw [← hloop.1, softAttachmentMinus, h0, sign_zero, neg_zero]
  · intro h0
    apply hτ
    rw [← hloop.2, softAttachmentPlus, h0, sign_zero, neg_zero]

/-- The mixed sector contains admissible vectors (indeed the whole open cone strictly between
`ℓ_{j-1}` and `-ℓ_j` lies in it). -/
theorem anchor_mixed_sector_nonempty (hn : 3 ≤ m) {P : LabelledTuple m} (hP : Generic P)
    (j : ZMod m) :
    ∃ q : Plane, SoftAdmissible P j q ∧
      softAttachmentMinus P j q ≠ softAttachmentPlus P j q := by
  have : Fact (1 < m) := ⟨by omega⟩
  have hD : det (edge P (j - 1)) (edge P j) ≠ 0 := g1_turn_nonzero hn hP.1 j
  have hD' : det (edge P (j - 1)) (-edge P j) ≠ 0 := by
    rw [det_neg_right]; exact neg_ne_zero.mpr hD
  obtain ⟨q, hq, hav⟩ :=
    anchor_exists_in_cone_avoiding P j (anchor_vertices_sub_ne_zero hn hP j) hD'
  obtain ⟨a, b, ha, hb, rfl⟩ := hq
  have h1 : det (edge P (j - 1)) (a • edge P (j - 1) + b • (-edge P j)) =
      -(b * det (edge P (j - 1)) (edge P j)) := by
    simp [det]; ring
  have h2 : det (a • edge P (j - 1) + b • (-edge P j)) (edge P j) =
      a * det (edge P (j - 1)) (edge P j) := by
    simp [det]; ring
  refine ⟨_, ⟨?_, ?_, hav⟩, ?_⟩
  · rw [h1]; exact neg_ne_zero.mpr (mul_ne_zero hb.ne' hD)
  · rw [h2]; exact mul_ne_zero ha.ne' hD
  · rw [softAttachmentMinus, softAttachmentPlus, h1, h2, Left.sign_neg, sign_mul, sign_mul,
      sign_pos ha, sign_pos hb, one_mul, neg_neg]
    exact anchor_signType_ne_neg_self _ (sign_ne_zero.mpr hD)

/-! ### Building anchors over a given parent -/

/-- Over a generic parent `P` of rotation `r` and any vertex `j`, a zero anchor with that parent
and insertion vertex exists (case (Z): the insertion vertex may be prescribed). -/
theorem zeroAnchor_of_parent (hn : 3 ≤ m) {r : ℤ} {P : LabelledTuple m} (hP : Generic P)
    (hr : rotationNumber P = (r : ℝ)) (j : ZMod m) :
    ∃ A : ZeroAnchor m r, A.parent = P ∧ A.vertex = j := by
  obtain ⟨q, hq, hmixed⟩ := anchor_mixed_sector_nonempty hn hP j
  obtain ⟨-, δ, hδ, B, hfam⟩ := soft_family_regular_data hn hP j q hq
  have hspec : ∃ B : GenericTuple (m + 1), ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (m + 1)) ∈ labelledChamber B ∧
        polygonProjection (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (m + 1)) ∈
          chamber (polygonProjection B) := by
    refine ⟨B, fun ε hε hεδ => ?_⟩
    obtain ⟨hQ, h1, h2, -⟩ := hfam ε hε hεδ
    exact ⟨hQ, h1, h2⟩
  exact ⟨{ parent := P
           parent_card := hn
           parent_generic := hP
           vertex := j
           vector := q
           admissible := hq
           bound := δ
           bound_pos := hδ
           bound_spec := hspec
           param := δ / 2
           param_pos := by positivity
           param_lt := by linarith
           parent_rotation := hr
           mixed := hmixed }, rfl, rfl⟩

/-- Over a generic parent `P` of rotation `r - sgn r` with `τ_j(P) = -sgn r`, a loop anchor with
that parent and insertion vertex exists. -/
theorem loopAnchor_of_parent (hn : 3 ≤ m) {r : ℤ} {P : LabelledTuple m} (hP : Generic P)
    (hr : rotationNumber P = (r : ℝ) - (SignType.sign r : ℝ)) {j : ZMod m}
    (hj : turn P j = -SignType.sign r) :
    ∃ A : LoopAnchor m r, A.parent = P ∧ A.vertex = j := by
  obtain ⟨q, hq, hloop⟩ := anchor_loop_sector_nonempty hn hP j
  obtain ⟨-, δ, hδ, B, hfam⟩ := soft_family_regular_data hn hP j q hq
  have hspec : ∃ B : GenericTuple (m + 1), ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (m + 1)) ∈ labelledChamber B ∧
        polygonProjection (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (m + 1)) ∈
          chamber (polygonProjection B) := by
    refine ⟨B, fun ε hε hεδ => ?_⟩
    obtain ⟨hQ, h1, h2, -⟩ := hfam ε hε hεδ
    exact ⟨hQ, h1, h2⟩
  exact ⟨{ parent := P
           parent_card := hn
           parent_generic := hP
           vertex := j
           vector := q
           admissible := hq
           bound := δ
           bound_pos := hδ
           bound_spec := hspec
           param := δ / 2
           param_pos := by positivity
           param_lt := by linarith
           parent_rotation := hr
           parent_turn := hj
           loop := hloop }, rfl, rfl⟩

/-- Over any generic triangle `P` and any of its vertices `j`, a loop anchor (L₀) with that parent
and insertion vertex exists. -/
theorem loopAnchorZero_of_parent (h3 : m = 3) {P : LabelledTuple m} (hP : Generic P)
    (j : ZMod m) : ∃ A : LoopAnchorZero m, A.parent = P ∧ A.vertex = j := by
  have hn : 3 ≤ m := by omega
  obtain ⟨q, hq, hloop⟩ := anchor_loop_sector_nonempty hn hP j
  obtain ⟨-, δ, hδ, B, hfam⟩ := soft_family_regular_data hn hP j q hq
  have hspec : ∃ B : GenericTuple (m + 1), ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (m + 1)) ∈ labelledChamber B ∧
        polygonProjection (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (m + 1)) ∈
          chamber (polygonProjection B) := by
    refine ⟨B, fun ε hε hεδ => ?_⟩
    obtain ⟨hQ, h1, h2, -⟩ := hfam ε hε hεδ
    exact ⟨hQ, h1, h2⟩
  exact ⟨{ parent := P
           parent_card := hn
           parent_generic := hP
           vertex := j
           vector := q
           admissible := hq
           bound := δ
           bound_pos := hδ
           bound_spec := hspec
           param := δ / 2
           param_pos := by positivity
           param_lt := by linarith
           triangle := h3
           loop := hloop }, rfl, rfl⟩

/-! ### The parent of a loop anchor: a generic `2|r|`-gon of rotation `r - sgn r` with a turn
`-sgn r`. A mixed-sector soft insertion into a generic polygon keeps the rotation and creates
two new corners with turns `-χ_-`, `-χ_+` of opposite signs (lem:soft-generic (ii)). -/

theorem anchor_exists_parent_with_turn (hn : 3 ≤ m) {P₀ : LabelledTuple m} (hP₀ : Generic P₀)
    (s : SignType) (hs : s ≠ 0) :
    ∃ P : LabelledTuple (m + 1), Generic P ∧ rotationNumber P = rotationNumber P₀ ∧
      ∃ j : ZMod (m + 1), turn P j = s := by
  obtain ⟨q, hq, hmixed⟩ := anchor_mixed_sector_nonempty hn hP₀ 0
  obtain ⟨-, δ, hδ, B, hfam⟩ := soft_family_regular_data hn hP₀ 0 q hq
  have hgen : ∀ ε : ℝ, 0 < ε → ε < δ → Generic (softInsertion P₀ 0 q ε) :=
    fun ε hε hεδ => (hfam ε hε hεδ).1
  have hreg : ∀ ε : ℝ, 0 < ε → ε < δ → Regular (softInsertion P₀ 0 q ε) :=
    fun ε hε hεδ => generic_regular (by omega) (hgen ε hε hεδ)
  have hε : 0 < δ / 2 := by positivity
  have hεδ : δ / 2 < δ := by linarith
  have ht := softInsertion_attachment_turns hn P₀ 0 q (δ / 2) hε
  refine ⟨softInsertion P₀ 0 q (δ / 2), hgen _ hε hεδ, ?_, ?_⟩
  · exact (soft_rotation_of_regular_interval hn hP₀ 0 q hq hδ hreg hε hεδ).1 (Or.inr hmixed)
  · have hχ := softAttachment_signs_nonzero hq
    rcases anchor_signType_mixed_cases _ _ s hχ.1 hχ.2 hs hmixed with h | h
    · exact ⟨softOldIndex 0 0, by rw [ht.1, h]⟩
    · exact ⟨softNewIndex 0, by rw [ht.2, h]⟩

/-! ### Exhaustion of the three cases -/

/-- For every admissible `(n, r)` with `n ≥ 4` exactly one of (Z) `(n-1, r)` admissible,
(L) `(n, r)` minimal with `|r| ≥ 2`, (L₀) `(n, r) = (4, 0)` applies. -/
theorem anchor_cases_exhaustive (n r : ℤ) (ha : Admissible n r) (hn : 4 ≤ n) :
    (Admissible (n - 1) r ∨ (MinimalAdmissible n r ∧ 2 ≤ |r|) ∨ (n, r) = (4, 0)) ∧
    ¬ (Admissible (n - 1) r ∧ (MinimalAdmissible n r ∧ 2 ≤ |r|)) ∧
    ¬ (Admissible (n - 1) r ∧ (n, r) = (4, 0)) ∧
    ¬ ((MinimalAdmissible n r ∧ 2 ≤ |r|) ∧ (n, r) = (4, 0)) := by
  simp only [Admissible, MinimalAdmissible, ne_eq, Prod.mk.injEq] at ha ⊢
  rcases abs_cases r with ⟨habs, -⟩ | ⟨habs, -⟩ <;> omega

/-! ### Existence of anchors of each type -/

/-- (Z) existence: a generic `(n-1)`-gon of rotation `r` exists by lem:fibres. -/
theorem zeroAnchor_exists {r : ℤ} (hZ : Admissible (m : ℤ) r) : Nonempty (ZeroAnchor m r) := by
  have hn : 3 ≤ m := by have := hZ.1; omega
  obtain ⟨P, hP, hr⟩ := exists_generic_of_admissible hZ
  obtain ⟨A, -⟩ := zeroAnchor_of_parent hn hP hr 0
  exact ⟨A⟩

/-- (L₀) existence: the counterclockwise triangle (a generic triangle of rotation `1`,
lem:fibres) with a loop inserted at any vertex. -/
theorem loopAnchorZero_exists (h3 : m = 3) : Nonempty (LoopAnchorZero m) := by
  have hadm : Admissible (m : ℤ) 1 := by
    refine ⟨by omega, by simp; omega, ?_⟩
    simp
  obtain ⟨P, hP, -⟩ := exists_generic_of_admissible hadm
  obtain ⟨A, -⟩ := loopAnchorZero_of_parent h3 hP 0
  exact ⟨A⟩

/-- (L) existence: `(n, r)` minimal with `|r| ≥ 2` gives `n - 1 = 2|r|`; a generic
`(2|r| - 1)`-gon of rotation `r - sgn r` exists (lem:fibres), a mixed-sector insertion makes it a
generic `2|r|`-gon of the same rotation with a corner of turn `-sgn r`, and a loop-sector insertion
there is the anchor. -/
theorem loopAnchor_exists {r : ℤ} (hL : MinimalAdmissible ((m : ℤ) + 1) r) (hr : 2 ≤ |r|) :
    Nonempty (LoopAnchor m r) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [abs_zero] at hr
    omega
  have hm : (m : ℤ) = 2 * |r| := by
    obtain ⟨-, h⟩ := hL
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · exact absurd h hr0
  obtain ⟨m₀, rfl⟩ : ∃ m₀ : ℕ, m = m₀ + 1 := ⟨m - 1, by omega⟩
  have : NeZero m₀ := ⟨by omega⟩
  have hm₀ : 3 ≤ m₀ := by omega
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · -- `sgn r = -1`, parent rotation `r + 1`
    have hs : SignType.sign r = -1 := sign_neg hneg
    have habs : |r| = -r := abs_of_neg hneg
    have habs' : |r + 1| = -(r + 1) := abs_of_nonpos (by omega)
    have hadm : Admissible (m₀ : ℤ) (r + 1) := by
      simp only [Admissible, ne_eq, Prod.mk.injEq]
      omega
    obtain ⟨P₀, hP₀, hrot₀⟩ := exists_generic_of_admissible hadm
    obtain ⟨P, hP, hrot, j, hj⟩ := anchor_exists_parent_with_turn hm₀ hP₀ 1 (by decide)
    obtain ⟨A, -⟩ := loopAnchor_of_parent (r := r) (by omega) hP
      (by rw [hrot, hrot₀, hs, SignType.coe_neg_one]; push_cast; ring) (j := j)
      (by rw [hj, hs]; decide)
    exact ⟨A⟩
  · -- `sgn r = 1`, parent rotation `r - 1`
    have hs : SignType.sign r = 1 := sign_pos hpos
    have habs : |r| = r := abs_of_pos hpos
    have habs' : |r - 1| = r - 1 := abs_of_nonneg (by omega)
    have hadm : Admissible (m₀ : ℤ) (r - 1) := by
      simp only [Admissible, ne_eq, Prod.mk.injEq]
      omega
    obtain ⟨P₀, hP₀, hrot₀⟩ := exists_generic_of_admissible hadm
    obtain ⟨P, hP, hrot, j, hj⟩ := anchor_exists_parent_with_turn hm₀ hP₀ (-1) (by decide)
    obtain ⟨A, -⟩ := loopAnchor_of_parent (r := r) (by omega) hP
      (by rw [hrot, hrot₀, hs, SignType.coe_one]; push_cast; ring) (j := j) (by rw [hj, hs])
    exact ⟨A⟩

/-- An anchor for every admissible `(n, r)` with `n ≥ 4` (`n = m + 1`). -/
theorem anchor_exists (r : ℤ) (ha : Admissible ((m : ℤ) + 1) r) (hn : 4 ≤ (m : ℤ) + 1) :
    Nonempty (Anchor m r) := by
  obtain ⟨hcases, -, -, -⟩ := anchor_cases_exhaustive ((m : ℤ) + 1) r ha hn
  simp only [add_sub_cancel_right] at hcases
  rcases hcases with hZ | ⟨hL, hr⟩ | hL₀
  · obtain ⟨A⟩ := zeroAnchor_exists hZ
    exact ⟨.zero hZ A⟩
  · obtain ⟨A⟩ := loopAnchor_exists hL hr
    exact ⟨.loop hL hr A⟩
  · have h3 : m = 3 := by
      simp only [Prod.mk.injEq] at hL₀
      omega
    obtain ⟨A⟩ := loopAnchorZero_exists h3
    exact ⟨.loopZero hL₀ A⟩

/-! ### Every anchor is generic, has `n` vertices and rotation `r` -/

theorem Anchor.polygon_generic {r : ℤ} (A : Anchor m r) : Generic A.polygon :=
  A.data.polygon_generic

theorem Anchor.polygon_rotation {r : ℤ} (A : Anchor m r) : rotationNumber A.polygon = (r : ℝ) := by
  cases A with
  | zero hZ A => exact A.polygon_rotation
  | loop hL hr A => exact A.polygon_rotation
  | loopZero hL₀ A =>
    have hr : r = 0 := by
      simp only [Prod.mk.injEq] at hL₀
      exact hL₀.2
    subst hr
    rw [Int.cast_zero]
    exact A.polygon_rotation

/-! ### prop:anchors-exist -/

/-- prop:anchors-exist (anchors exist), as printed on SM15, with `(n, r) = ((m : ℤ) + 1, r)`.
For every admissible `(n, r)` with `n ≥ 4`, exactly one of the cases (Z), (L), (L₀) of def:anchors
applies (first clause, stated for integer pairs); an anchor of that type exists (second clause:
each case separately, and the bundled `Anchor`); every anchor is generic, is an `n`-gon
(`LabelledTuple (m + 1)`) and has rotation `r` (third clause); for a given generic parent `P` and
vertex `j` the mixed and loop sectors both contain admissible vectors (fourth clause), so in case
(Z) the insertion vertex may be prescribed (fifth clause); likewise the parent and vertex may be
prescribed in case (L₀) and, given a parent as in (L), in case (L) (sixth clause). -/
theorem anchors_exist :
    (∀ n r : ℤ, Admissible n r → 4 ≤ n →
      (Admissible (n - 1) r ∨ (MinimalAdmissible n r ∧ 2 ≤ |r|) ∨ (n, r) = (4, 0)) ∧
      ¬ (Admissible (n - 1) r ∧ (MinimalAdmissible n r ∧ 2 ≤ |r|)) ∧
      ¬ (Admissible (n - 1) r ∧ (n, r) = (4, 0)) ∧
      ¬ ((MinimalAdmissible n r ∧ 2 ≤ |r|) ∧ (n, r) = (4, 0))) ∧
    (∀ (m : ℕ) [NeZero m] (r : ℤ),
      (Admissible (m : ℤ) r → Nonempty (ZeroAnchor m r)) ∧
      (MinimalAdmissible ((m : ℤ) + 1) r → 2 ≤ |r| → Nonempty (LoopAnchor m r)) ∧
      (((m : ℤ) + 1, r) = (4, 0) → Nonempty (LoopAnchorZero m)) ∧
      (Admissible ((m : ℤ) + 1) r → 4 ≤ (m : ℤ) + 1 → Nonempty (Anchor m r))) ∧
    (∀ (m : ℕ) [NeZero m] (r : ℤ) (A : Anchor m r),
      Generic A.polygon ∧ rotationNumber A.polygon = (r : ℝ)) ∧
    (∀ (m : ℕ) [NeZero m], 3 ≤ m → ∀ P : LabelledTuple m, Generic P → ∀ j : ZMod m,
      (∃ q : Plane, SoftAdmissible P j q ∧
        softAttachmentMinus P j q ≠ softAttachmentPlus P j q) ∧
      (∃ q : Plane, SoftAdmissible P j q ∧
        (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j))) ∧
    (∀ (m : ℕ) [NeZero m], 3 ≤ m → ∀ (r : ℤ) (P : LabelledTuple m), Generic P →
      rotationNumber P = (r : ℝ) → ∀ j : ZMod m,
      ∃ A : ZeroAnchor m r, A.parent = P ∧ A.vertex = j) ∧
    ((∀ (m : ℕ) [NeZero m], m = 3 → ∀ P : LabelledTuple m, Generic P → ∀ j : ZMod m,
      ∃ A : LoopAnchorZero m, A.parent = P ∧ A.vertex = j) ∧
     (∀ (m : ℕ) [NeZero m], 3 ≤ m → ∀ (r : ℤ) (P : LabelledTuple m), Generic P →
      rotationNumber P = (r : ℝ) - (SignType.sign r : ℝ) → ∀ j : ZMod m,
      turn P j = -SignType.sign r → ∃ A : LoopAnchor m r, A.parent = P ∧ A.vertex = j)) := by
  refine ⟨anchor_cases_exhaustive, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m _ r
    refine ⟨zeroAnchor_exists, loopAnchor_exists, fun h => ?_, anchor_exists r⟩
    apply loopAnchorZero_exists
    simp only [Prod.mk.injEq] at h
    omega
  · intro m _ r A
    exact ⟨A.polygon_generic, A.polygon_rotation⟩
  · intro m _ hn P hP j
    exact ⟨anchor_mixed_sector_nonempty hn hP j, anchor_loop_sector_nonempty hn hP j⟩
  · intro m _ hn r P hP hr j
    exact zeroAnchor_of_parent hn hP hr j
  · intro m _ h3 P hP j
    exact loopAnchorZero_of_parent h3 hP j
  · intro m _ hn r P hP hr j hj
    exact loopAnchor_of_parent hn hP hr hj

end
end SM

