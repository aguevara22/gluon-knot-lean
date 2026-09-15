import SM.Anchors

/-! Source def:anchors (reference/SM/sm-5-transport.tex:373, frame SM15): zero anchors (Z), loop
anchors (L) and loop anchors over a triangle (L₀). Main declaration: `SM.anchors_definition`, the
specification of the anchor structures `SM.SoftAnchorData`, `SM.ZeroAnchor`, `SM.LoopAnchor`,
`SM.LoopAnchorZero` and `SM.Anchor` (module `SM.Anchors`).

Notation. The admissible pair `(n, r)` of the source is `((m : ℤ) + 1, r)`, where `m` is the vertex
count of the parent (`n - 1 = m`, so `n ≥ 4 ↔ 3 ≤ m`). The anchor is the `n`-gon
`P^{(j,q)}_ε = softInsertion P j q ε : LabelledTuple (m + 1)` (def:soft) with parent `P = A.parent`
(a generic `(n-1)`-gon), insertion vertex `j = A.vertex : ZMod m`, admissible `q = A.vector`
(`SoftAdmissible P j q`, def:soft), and parameter `ε = A.param` with `0 < ε < ε₀`, where
`ε₀ = A.bound = ε₀(P, j, q) > 0` is the bound of lem:soft-generic carried as data: on `(0, ε₀)`
every `P_ε` is generic and all of them lie in one chamber (`labelledChamber`, `chamber`,
`polygonProjection`: def:chamber). The sectors are those of lem:soft-generic (iv) /
lem:soft-rotation with `χ_- = softAttachmentMinus P j q`, `χ_+ = softAttachmentPlus P j q` and
`τ_j(P) = turn P j`: mixed sector `χ_- ≠ χ_+`, loop sector `χ_- = χ_+ = τ_j`. `sgn r =
SignType.sign r`; `rot = rotationNumber`; `(n, r)` admissible / minimal = `Admissible` /
`MinimalAdmissible` (def:admissible). The soft edge `E_j` of the anchor (from `μ_j` to
`μ_* = μ_{j+1}` in the anchor's labelling) is the edge at the label `A.softEdge`
(`= softOldIndex j j`, the anchor label of the old vertex `μ_j`; the next label
`A.softEdge + 1 = softNewIndex j` carries `μ_* = μ_j + ε q`; `edge Q i = Q (i + 1) - Q i`). -/

namespace SM

/-- def:anchors as printed on SM15, read on the anchor structures of `SM.Anchors`. -/
structure AnchorsDefinitionData : Prop where
  /-- The data common to all three cases: a generic parent `P` with `n - 1 = m ≥ 3` vertices, an
  insertion vertex `j`, an admissible vector `q`, the bound `ε₀ = ε₀(P, j, q) > 0` of
  lem:soft-generic (on `(0, ε₀)` the insertion `P^{(j,q)}_ε` is generic and lies in one chamber),
  and the parameter `0 < ε < ε₀`; the anchor is the generic `n`-gon `P^{(j,q)}_ε`. -/
  data : ∀ (m : ℕ) [NeZero m] (A : SoftAnchorData m),
    3 ≤ m ∧ Generic A.parent ∧ SoftAdmissible A.parent A.vertex A.vector ∧
    0 < A.bound ∧
    (∀ ε : ℝ, 0 < ε → ε < A.bound → Generic (softInsertion A.parent A.vertex A.vector ε)) ∧
    (∃ B : GenericTuple (m + 1), ∀ ε : ℝ, 0 < ε → ε < A.bound →
      ∃ hQ : Generic (softInsertion A.parent A.vertex A.vector ε),
        (⟨softInsertion A.parent A.vertex A.vector ε, hQ⟩ : GenericTuple (m + 1)) ∈
            labelledChamber B ∧
          polygonProjection
              (⟨softInsertion A.parent A.vertex A.vector ε, hQ⟩ : GenericTuple (m + 1)) ∈
            chamber (polygonProjection B)) ∧
    0 < A.param ∧ A.param < A.bound ∧
    A.polygon = softInsertion A.parent A.vertex A.vector A.param ∧ Generic A.polygon
  /-- The soft edge of the anchor is its edge `E_j` from `μ_j` to `μ_* = μ_j + ε q`. -/
  softEdge : ∀ (m : ℕ) [NeZero m] (A : SoftAnchorData m),
    A.polygon A.softEdge = A.parent A.vertex ∧
    A.polygon (A.softEdge + 1) = A.parent A.vertex + A.param • A.vector ∧
    edge A.polygon A.softEdge = A.param • A.vector
  /-- (Z) A zero anchor for `(n, r)`: the parent has rotation `r` and `q` lies in the mixed
  sector `χ_- ≠ χ_+`. -/
  zero : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : ZeroAnchor m r),
    rotationNumber A.parent = (r : ℝ) ∧
    softAttachmentMinus A.parent A.vertex A.vector ≠ softAttachmentPlus A.parent A.vertex A.vector
  /-- (L) A loop anchor for `(n, r)`: the parent has rotation `r - sgn r`, the insertion vertex
  has `τ_j(P) = -sgn r`, and `q` lies in the loop sector `χ_- = χ_+ = τ_j`. -/
  loop : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : LoopAnchor m r),
    rotationNumber A.parent = (r : ℝ) - (SignType.sign r : ℝ) ∧
    turn A.parent A.vertex = -SignType.sign r ∧
    softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
    softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex
  /-- (L₀) A loop anchor for `(n, r) = (4, 0)`: the parent is a triangle, `j` any of its
  vertices, and `q` lies in the loop sector. -/
  loopZero : ∀ (m : ℕ) [NeZero m] (A : LoopAnchorZero m),
    m = 3 ∧
    softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
    softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex
  /-- An anchor for `(n, r)` is a zero anchor in case (Z) (`(n - 1, r)` admissible), a loop anchor
  in case (L) (`(n, r)` minimal with `|r| ≥ 2`), or a loop anchor over a triangle in case (L₀)
  (`(n, r) = (4, 0)`). -/
  cases : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : Anchor m r),
    (∃ (hZ : Admissible (m : ℤ) r) (A₀ : ZeroAnchor m r), A = Anchor.zero hZ A₀) ∨
    (∃ (hL : MinimalAdmissible ((m : ℤ) + 1) r) (hr : 2 ≤ |r|) (A₀ : LoopAnchor m r),
      A = Anchor.loop hL hr A₀) ∨
    (∃ (hL₀ : ((m : ℤ) + 1, r) = (4, 0)) (A₀ : LoopAnchorZero m), A = Anchor.loopZero hL₀ A₀)
  /-- The anchor polygon, parent, insertion vertex and soft edge of an `Anchor` are those of its
  underlying data in each of the three cases. -/
  projections : ∀ (m : ℕ) [NeZero m] (r : ℤ),
    (∀ A : Anchor m r, A.polygon = A.data.polygon ∧ A.parent = A.data.parent ∧
      A.vertex = A.data.vertex ∧ A.softEdge = A.data.softEdge) ∧
    (∀ (hZ : Admissible (m : ℤ) r) (A₀ : ZeroAnchor m r),
      (Anchor.zero hZ A₀).data = A₀.toSoftAnchorData) ∧
    (∀ (hL : MinimalAdmissible ((m : ℤ) + 1) r) (hr : 2 ≤ |r|) (A₀ : LoopAnchor m r),
      (Anchor.loop hL hr A₀).data = A₀.toSoftAnchorData) ∧
    (∀ (hL₀ : ((m : ℤ) + 1, r) = (4, 0)) (A₀ : LoopAnchorZero m),
      (Anchor.loopZero hL₀ A₀ : Anchor m r).data = A₀.toSoftAnchorData)

theorem anchors_definition : AnchorsDefinitionData where
  data := fun _ _ A =>
    ⟨A.parent_card, A.parent_generic, A.admissible, A.bound_pos,
      fun _ hε hεb => A.generic_of_lt hε hεb, A.bound_spec, A.param_pos, A.param_lt, rfl,
      A.polygon_generic⟩
  softEdge := fun _ _ A => ⟨A.softEdge_spec.1, A.softEdge_spec.2.2.1, A.softEdge_spec.2.2.2⟩
  zero := fun _ _ _ A => ⟨A.parent_rotation, A.mixed⟩
  loop := fun _ _ _ A => ⟨A.parent_rotation, A.parent_turn, A.loop.1, A.loop.2⟩
  loopZero := fun _ _ A => ⟨A.triangle, A.loop.1, A.loop.2⟩
  cases := fun _ _ _ A => by
    cases A with
    | zero hZ A₀ => exact Or.inl ⟨hZ, A₀, rfl⟩
    | loop hL hr A₀ => exact Or.inr (Or.inl ⟨hL, hr, A₀, rfl⟩)
    | loopZero hL₀ A₀ => exact Or.inr (Or.inr ⟨hL₀, A₀, rfl⟩)
  projections := fun _ _ _ =>
    ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

end SM
