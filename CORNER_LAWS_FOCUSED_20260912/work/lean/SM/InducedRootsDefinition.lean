import SM.ContactHalfRoots
import SM.PhysicalDeletionRoots
import SM.DeletionHalvesDefinition

/-! Source def:induced-roots (reference/SM/sm-2-amplitude.tex:385, frame SM15): the
deletion map `D_j` on roots at a simple flat or cusp wall at `j`, and the half map `H`
on roots at a simple vertex–edge wall at `(M; a)`. Main declaration:
`SM.induced_roots_definition`.

Notation. Roots are edge indices (def:root). `deleteVertex P j = P ∖ j` with vertex labels
`deletionIndex j i` (def:deletion-halves, `SM.deletion_halves_definition`); its edge `-1`
is the fused edge `[μ_{j-1}, μ_{j+1}]`. `firstHalf P M a = λ₁` (vertices `M, …, a`) and
`secondHalf P M a = λ₂` (vertices `M, a+1, …, M-1`) are the halves of def:deletion-halves;
`d₁ = [μ_a, μ_M]` is the closing edge `-1` of `λ₁` and `d₂ = [μ_M, μ_{a+1}]` the opening
edge `0` of `λ₂`; `firstHalfIndex M a i` / `secondHalfEdgeIndex M a i` are the parent
labels of the inherited edges. The arc `{M, M+1, …, a-1}` is
`(g - M).val < contactDistance M a` and the arc `{a+1, …, M-1}` is
`contactDistance M a < (g - M).val`, where `contactDistance M a = (a - M).val`. -/

namespace SM

variable {n : ℕ} [NeZero n]

/-- `D_j(g)`: the root of `P ∖ j` induced by the root `g` of `P` (def:induced-roots). -/
def deletionRoot (j g : ZMod (n + 1)) : ZMod n := fusionIndex j g

/-- `H(g) = (h₁, h₂)`: the pair of roots of the halves `λ₁, λ₂` induced by the root `g`
(def:induced-roots). -/
def halfRoots (M a g : ZMod n) : ZMod (firstHalfSize M a) × ZMod (secondHalfSize M a) :=
  contactHalfRoots M a g

/-- The printed two-case description of `D_j`. -/
structure DeletionRootData (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) : Prop where
  /-- `g ∈ {j-1, j}`: `D_j(g)` is the fused edge `[μ_{j-1}, μ_{j+1}]` of `P ∖ j`. -/
  incident_case : ∀ g : ZMod (n + 1), SM.incident j g →
    deletionRoot j g = -1 ∧
    deleteVertex P j (deletionRoot j g) = P (j - 1) ∧
    deleteVertex P j (deletionRoot j g + 1) = P (j + 1) ∧
    edge (deleteVertex P j) (deletionRoot j g) = P (j + 1) - P (j - 1)
  /-- otherwise: `D_j(g)` is the edge of `P ∖ j` with the same endpoints (vertices `g`,
  `g+1`) as `E_g`, and it is the only such edge. -/
  nonincident_case : ∀ g : ZMod (n + 1), ¬ SM.incident j g →
    deletionRoot j g ≠ -1 ∧
    deletionIndex j (deletionRoot j g) = g ∧
    deletionIndex j (deletionRoot j g + 1) = g + 1 ∧
    deleteVertex P j (deletionRoot j g) = P g ∧
    deleteVertex P j (deletionRoot j g + 1) = P (g + 1) ∧
    edge (deleteVertex P j) (deletionRoot j g) = edge P g ∧
    ∀ i : ZMod n, deletionIndex j i = g → deletionIndex j (i + 1) = g + 1 → i = deletionRoot j g

/-- The printed three-case description of `H` at `(M; a)`. -/
structure HalfRootsData (P : LabelledTuple n) (M a : ZMod n) : Prop where
  /-- `d₁ = [μ_a, μ_M]` is the closing edge `-1` of `λ₁`. -/
  d₁ : firstHalf P M a (-1) = P a ∧ firstHalf P M a 0 = P M ∧
    edge (firstHalf P M a) (-1) = P M - P a
  /-- `d₂ = [μ_M, μ_{a+1}]` is the opening edge `0` of `λ₂`. -/
  d₂ : secondHalf P M a 0 = P M ∧ secondHalf P M a 1 = P (a + 1) ∧
    edge (secondHalf P M a) 0 = P (a + 1) - P M
  /-- `g = a`: `H(g) = (d₁, d₂)`. -/
  base : halfRoots M a a = (-1, 0)
  /-- `g ∈ {M, …, a-1}`: `H(g) = (E_g in λ₁, d₂)`. -/
  first_arc : ∀ g : ZMod n, (g - M).val < contactDistance M a →
    (halfRoots M a g).1 ≠ -1 ∧ firstHalfIndex M a (halfRoots M a g).1 = g ∧
    firstHalf P M a (halfRoots M a g).1 = P g ∧
    firstHalf P M a ((halfRoots M a g).1 + 1) = P (g + 1) ∧
    edge (firstHalf P M a) (halfRoots M a g).1 = edge P g ∧
    (halfRoots M a g).2 = 0
  /-- `g ∈ {a+1, …, M-1}`: `H(g) = (d₁, E_g in λ₂)`. -/
  second_arc : ∀ g : ZMod n, contactDistance M a < (g - M).val →
    (halfRoots M a g).1 = -1 ∧ (halfRoots M a g).2 ≠ 0 ∧
    secondHalfEdgeIndex M a (halfRoots M a g).2 = g ∧
    secondHalf P M a (halfRoots M a g).2 = P g ∧
    secondHalf P M a ((halfRoots M a g).2 + 1) = P (g + 1) ∧
    edge (secondHalf P M a) (halfRoots M a g).2 = edge P g
  /-- the three cases are exhaustive and exclusive (`g = a` is the middle position). -/
  cases : ∀ g : ZMod n,
    (g = a ↔ (g - M).val = contactDistance M a) ∧
    (g = a ∨ (g - M).val < contactDistance M a ∨ contactDistance M a < (g - M).val)

theorem deletionRoot_data (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    DeletionRootData P j where
  incident_case := by
    intro g hg
    have hl : deletionRoot j g = -1 := (fusionIndex_eq_last_iff_incident j g).mpr hg
    refine ⟨hl, ?_, ?_, ?_⟩
    · rw [hl, deleteVertex_last]
    · rw [hl, neg_add_cancel, deleteVertex_zero]
    · rw [hl, edge_deleteVertex_last]
  nonincident_case := by
    intro g hg
    have hp : g ≠ j - 1 := fun he => hg (Or.inl he)
    have hj : g ≠ j := fun he => hg (Or.inr he)
    have hne : deletionRoot j g ≠ -1 := fusionIndex_ne_last hj hp
    have hlabels := fusionIndex_nonincident_labels j g hg
    have hpoints := (fusionIndex_physical_deletion_root P j g).2 hg
    refine ⟨hne, hlabels.1, hlabels.2, hpoints.1, hpoints.2, ?_, ?_⟩
    · rw [edge_deleteVertex P j hne]
      change edge P (deletionIndex j (fusionIndex j g)) = edge P g
      rw [hlabels.1]
    · intro i h1 h2
      by_cases hi : i = -1
      · exfalso
        subst hi
        rw [deletionIndex_last] at h1
        exact hp h1.symm
      · obtain ⟨i₀, _, huniq⟩ := fusionIndex_unique_nonincident_root j g hg
        have hi₀ := huniq i ⟨hi, h1, h2⟩
        have hf := huniq (fusionIndex j g) ⟨hne, hlabels.1, hlabels.2⟩
        exact hi₀.trans hf.symm

theorem halfRoots_data (hn : 3 ≤ n) {M a : ZMod n} (hc : ContactSeparated M a)
    (P : LabelledTuple n) : HalfRootsData P M a where
  d₁ := ⟨firstHalf_last P M a, firstHalf_zero P M a, edge_firstHalf_last P M a⟩
  d₂ := ⟨secondHalf_zero P M a, secondHalf_one hn hc P, edge_secondHalf_zero hn hc P⟩
  base := contactHalfRoots_base M a
  first_arc := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := (firstHalf_inherited_root_iff M a g).mpr hg
    have hr : halfRoots M a (firstHalfIndex M a i) = (i, 0) := contactHalfRoots_first M a hi
    rw [hr]
    refine ⟨hi, rfl, rfl, ?_, edge_firstHalf P M a hi, rfl⟩
    show P (firstHalfIndex M a (i + 1)) = P (firstHalfIndex M a i + 1)
    rw [firstHalfIndex_next M a hi]
  second_arc := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := (secondHalf_inherited_root_iff M a g).mpr hg
    have hr : halfRoots M a (secondHalfEdgeIndex M a i) = (-1, i) := contactHalfRoots_second M a hi
    rw [hr]
    refine ⟨rfl, hi, rfl, ?_, ?_, edge_secondHalf P M a hi⟩
    · show P (secondHalfIndex M a i) = P (secondHalfEdgeIndex M a i)
      rw [secondHalfIndex_nonzero M a hi]
    · show P (secondHalfIndex M a (i + 1)) = P (secondHalfEdgeIndex M a i + 1)
      rw [secondHalfIndex_next M a hi]
  cases := by
    intro g
    have hiff : g = a ↔ (g - M).val = contactDistance M a := by
      constructor
      · rintro rfl; rfl
      · intro h
        have h' : g - M = a - M := ZMod.val_injective n h
        exact sub_left_injective h'
    refine ⟨hiff, ?_⟩
    rcases lt_trichotomy (g - M).val (contactDistance M a) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (hiff.mpr h)
    · exact Or.inr (Or.inr h)

/-- def:induced-roots: the deletion map on roots (for every polygon `P` with `n+1 ≥ 4`
vertices and every deleted vertex `j`, hence at every simple flat or cusp wall at `j`,
whose centre is such a `P`) and the half map on roots at every simple vertex–edge wall. -/
def InducedRootsDefinitionData : Prop :=
  (∀ k : ℕ, ∀ _ : NeZero k, ∀ _hk : 3 ≤ k,
    ∀ P : LabelledTuple (k + 1), ∀ j : ZMod (k + 1), DeletionRootData P j) ∧
  (∀ k : ℕ, ∀ _ : NeZero k, ∀ _hk : 3 ≤ k, ∀ w : WallGerm k,
    ∀ M a : ZMod k, w.VertexEdgeAt M a → HalfRootsData w.center M a)

theorem induced_roots_definition : InducedRootsDefinitionData :=
  ⟨fun _ _ _ P j => deletionRoot_data P j,
    fun _ _ hk w _ _ h => halfRoots_data hk h.1 w.center⟩

end SM
