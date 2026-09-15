import SM.SoftAttachmentSigns

/-! Source def:soft (reference/SM/sm-2-amplitude.tex:996, frame SM15): the soft insertion
`P^{(j,q)}_ε` of a vector `q` at the vertex `j`, its soft and return edges, the attachment
signs `χ_-`, `χ_+`, and admissibility of `q`. Main declaration:
`SM.softInsertion_definition`.

Notation. `softInsertion P j q ε : LabelledTuple (n + 1)` is `P_ε`: the old vertex `μ_k` sits
at the label `softOldIndex j k`, the new vertex `μ_* = μ_j + ε q` at the label
`softNewIndex j`, which is the cyclic successor of `softOldIndex j j` (inserted immediately
after `μ_j`) and whose successor is `softOldIndex j (j+1)`. Edge labels follow vertex labels
(def:polygon): the soft edge is the edge `softOldIndex j j` (from `μ_j` to `μ_*`), the return
edge is the edge `softNewIndex j` (from `μ_*` to `μ_{j+1}`), every other edge `softOldIndex j k`
(`k ≠ j`) is the parent edge `E_k`. `softAttachmentMinus P j q = -sgn det(ℓ_{j-1}, q) = χ_-`,
`softAttachmentPlus P j q = -sgn det(q, ℓ_j) = χ_+`, with `edge P k = ℓ_k`;
`SoftAdmissible P j q` is admissibility. The family is defined for every real `ε`; the source
uses `ε > 0`. -/

namespace SM

variable {n : ℕ} [NeZero n]

/-- The printed description of the soft insertion at one parameter `ε > 0`. -/
structure SoftInsertionData (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) : Prop where
  /-- the `n + 1` labels are the old labels and the new one, without repetition -/
  labels_exhaustive : ∀ a : ZMod (n + 1), a = softNewIndex j ∨ ∃ k : ZMod n, a = softOldIndex j k
  labels_injective : Function.Injective (softOldIndex (n := n) j)
  labels_new_ne_old : ∀ k : ZMod n, softOldIndex j k ≠ softNewIndex j
  /-- `μ_*` is inserted immediately after `μ_j`; all other successions are inherited -/
  new_after_j : softOldIndex j j + 1 = softNewIndex j
  new_before_succ : softNewIndex j + 1 = softOldIndex j (j + 1)
  old_next : ∀ k : ZMod n, k ≠ j → softOldIndex j (k + 1) = softOldIndex j k + 1
  /-- the vertices: `(μ_1, …, μ_j, μ_j + ε q, μ_{j+1}, …, μ_n)` -/
  old_vertices : ∀ k : ZMod n, softInsertion P j q ε (softOldIndex j k) = P k
  new_vertex : softInsertion P j q ε (softNewIndex j) = P j + ε • q
  /-- the edges: `ℓ_{j-1}` and the others unchanged, the soft edge `ε q`, the return edge
  `ℓ_j - ε q` -/
  old_edges : ∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k
  soft_edge : edge (softInsertion P j q ε) (softOldIndex j j) = ε • q
  return_edge : edge (softInsertion P j q ε) (softNewIndex j) = edge P j - ε • q
  /-- the attachment signs `χ_- = χ_{*,j,j-1}(P_ε) = -sgn det(ℓ_{j-1}, q)` and
  `χ_+ = χ_{*,j,j+1}(P_ε) = -sgn det(q, ℓ_j)` -/
  attachment_minus :
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j - 1)) =
      softAttachmentMinus P j q ∧
    softAttachmentMinus P j q = -SignType.sign (det (edge P (j - 1)) q)
  attachment_plus :
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j + 1)) =
      softAttachmentPlus P j q ∧
    softAttachmentPlus P j q = -SignType.sign (det q (edge P j))
  /-- admissibility is exactly the three determinant conditions -/
  admissible_iff : SoftAdmissible P j q ↔
    det (edge P (j - 1)) q ≠ 0 ∧ det q (edge P j) ≠ 0 ∧ ∀ k : ZMod n, k ≠ j → det q (P k - P j) ≠ 0

theorem softInsertion_data (P : LabelledTuple n) (j : ZMod n) (q : Plane) {ε : ℝ} (hε : 0 < ε) :
    SoftInsertionData P j q ε where
  labels_exhaustive := soft_indices_exhaust j
  labels_injective := softOldIndex_injective j
  labels_new_ne_old := fun k => softOldIndex_ne_new j k
  new_after_j := softOldIndex_attachment_next j
  new_before_succ := softNewIndex_next j
  old_next := fun k hk => softOldIndex_next j k hk
  old_vertices := fun k => softInsertion_old P j k q ε
  new_vertex := softInsertion_new P j q ε
  old_edges := fun k hk => edge_softInsertion_old P j k q ε hk
  soft_edge := edge_softInsertion_soft P j q ε
  return_edge := edge_softInsertion_return P j q ε
  attachment_minus := ⟨(softInsertion_attachment_signs P j q ε hε).1, rfl⟩
  attachment_plus := ⟨(softInsertion_attachment_signs P j q ε hε).2, rfl⟩
  admissible_iff := Iff.rfl

/-- def:soft, for every polygon `P` (in particular every `P` satisfying (G1)), vertex `j`,
vector `q` (in particular `q ≠ 0`) and every `ε > 0`. -/
def SoftInsertionDefinitionData : Prop :=
  ∀ k : ℕ, ∀ _ : NeZero k, ∀ _hk : 3 ≤ k, ∀ P : LabelledTuple k, ∀ j : ZMod k, ∀ q : Plane,
    ∀ ε : ℝ, 0 < ε → SoftInsertionData P j q ε

theorem softInsertion_definition : SoftInsertionDefinitionData :=
  fun _ _ _ P j q _ hε => softInsertion_data P j q hε

end SM
