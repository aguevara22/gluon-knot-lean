import DirectGLSSW.SpinorGates
import DirectGLSSW.CutIncidence
import DirectGLSSW.VertexRecursion

/-!
# Spinor vertex products on an opened polygon word

Source: GLSSW version 1, equations (18)--(22), and the frozen note's
`ep:H`, `ep:linear-gates`, `ep:Phi`, and `ep:tree-recursion`.

The vertices below are defined directly from adjacent and partial chord
spinor brackets, using the published ratio inside the positive step. Their
identification with the rational-array gates is proved for every valid cut
set under interval noncollinearity. The signs at zero are totalized only to
define arrays; the comparison theorems establish that all bracket arguments
actually used by a vertex are nonzero.

The word is open. This module does not assert cyclic invariance or identify
HOMFLY data. Coordinates are in a linearly ordered field; specialization to
the reals is separate.
-/

namespace DirectGLSSW
open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Every ordered triple of vertices within the closed interval is
noncollinear. No assertion is imposed outside that interval. -/
def IntervalNoncollinear (q : ℕ → PlanarPoint K) (i j : ℕ) : Prop :=
  ∀ a b c, i ≤ a → a < b → b < c → c ≤ j → polygonHDet q a b c ≠ 0

/-- The determinant sign array, with the scalar sign's explicit extension
at zero. Actual gate identifications below use only nonzero entries. -/
noncomputable def polygonSignArray (q : ℕ → PlanarPoint K) : TripleArray :=
  fun a b c => scalarSignValue (polygonHDet q a b c)

/-- Ordered triples of successive cuts have the parent interval's bounds. -/
theorem cutTriples_interval_bounds {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {a b c : ℕ}
    (ht : (a, b, c) ∈ cutTriples i j S) :
    i ≤ a ∧ a < b ∧ b < c ∧ c ≤ j := by
  have hb : b ∈ S := cutTriples_middle_mem hij hS ht
  have hsne : S.Nonempty := ⟨b, hb⟩
  obtain ⟨hab, hbc⟩ := (cutTriples_mem_iff hij hS).mp ht
  simp only [cutEdges, List.mem_toFinset] at hab hbc
  have he₁ := cutVertices_branch_bounds hij hS hsne hab
  have he₂ := cutVertices_branch_bounds hij hS hsne hbc
  exact ⟨he₁.1, he₁.2.1, he₂.2.1, he₂.2.2.1⟩

/-- The ordinary GLSSW vertex: adjacent block signs and negative far/near
ratios. An empty cut set gives the empty product one. -/
noncomputable def spinorOrdinaryVertex (q : ℕ → PlanarPoint K)
    (i j : ℕ) (S : Finset ℕ) : ℚ :=
  ∏ t ∈ cutTriples i j S,
    scalarSignValue (spinorBracket (polygonChord q t.1 t.2.1)
      (polygonChord q t.2.1 t.2.2)) *
    scalarPositiveStep (-(spinorBracket (polygonChord q i t.2.1)
      (polygonChord q t.2.1 j) /
      spinorBracket (polygonChord q t.1 t.2.1) (polygonChord q t.2.1 t.2.2)))

/-- The second GLSSW vertex product, with positive far/near ratios. -/
noncomputable def spinorMarkedVertex (q : ℕ → PlanarPoint K)
    (i j : ℕ) (S : Finset ℕ) : ℚ :=
  ∏ t ∈ cutTriples i j S,
    scalarSignValue (spinorBracket (polygonChord q t.1 t.2.1)
      (polygonChord q t.2.1 t.2.2)) *
    scalarPositiveStep (spinorBracket (polygonChord q i t.2.1)
      (polygonChord q t.2.1 j) /
      spinorBracket (polygonChord q t.1 t.2.1) (polygonChord q t.2.1 t.2.2))

/-- The finite ordinary vertex functional with arbitrary branch values. -/
noncomputable def spinorOrdinaryPhi (q : ℕ → PlanarPoint K)
    (X : IntervalArray) (i j : ℕ) : ℚ :=
  ∑ S ∈ (Finset.Ioo i j).powerset,
    spinorOrdinaryVertex q i j S * branchProduct X (cutVertices i j S)

/-- The finite marked vertex functional retains the unary root. -/
noncomputable def spinorMarkedPhi (q : ℕ → PlanarPoint K)
    (X : IntervalArray) (i j : ℕ) : ℚ :=
  ∑ S ∈ (Finset.Ioo i j).powerset,
    spinorMarkedVertex q i j S * branchProduct X (cutVertices i j S)

/-- Every ordinary published vertex factor matches the finite-cut gate
product, with both near and far nonzero conditions derived from geometry. -/
theorem spinorOrdinaryVertex_eq_gateProduct (q : ℕ → PlanarPoint K)
    {i j : ℕ} {S : Finset ℕ} (hij : i < j)
    (hq : IntervalNoncollinear q i j) (hS : S ⊆ Finset.Ioo i j) :
    spinorOrdinaryVertex q i j S =
      gateProduct (polygonSignArray q) (polygonSignArray q) i j
        (cutVertices i j S) := by
  rw [gateProduct_eq_prod_cutTriples _ _ hij hS]
  unfold spinorOrdinaryVertex
  apply Finset.prod_congr rfl
  rintro ⟨a, b, c⟩ ht
  obtain ⟨hia, hab, hbc, hcj⟩ := cutTriples_interval_bounds hij hS ht
  have hd := hq a b c hia hab hbc hcj
  have hh := hq i b j (le_refl i) (by omega) (by omega) (le_refl j)
  simp only [spinorBracket_polygonChords, polygonSignArray]
  exact scalarSignValue_ordinary_ratio _ _ hd hh

/-- Every marked published vertex factor matches the sign-reversed far
array product, including the unary empty-product case. -/
theorem spinorMarkedVertex_eq_gateProduct (q : ℕ → PlanarPoint K)
    {i j : ℕ} {S : Finset ℕ} (hij : i < j)
    (hq : IntervalNoncollinear q i j) (hS : S ⊆ Finset.Ioo i j) :
    spinorMarkedVertex q i j S =
      gateProduct (polygonSignArray q) (fun a b c => -polygonSignArray q a b c)
        i j (cutVertices i j S) := by
  rw [gateProduct_eq_prod_cutTriples _ _ hij hS]
  unfold spinorMarkedVertex
  apply Finset.prod_congr rfl
  rintro ⟨a, b, c⟩ ht
  obtain ⟨hia, hab, hbc, hcj⟩ := cutTriples_interval_bounds hij hS ht
  have hd := hq a b c hia hab hbc hcj
  have hh := hq i b j (le_refl i) (by omega) (by omega) (le_refl j)
  simp only [spinorBracket_polygonChords, polygonSignArray, sub_neg_eq_add]
  exact scalarSignValue_marked_ratio _ _ hd hh

/-- The actual ordinary spinor vertex functional is the source Phi map. -/
theorem spinorOrdinaryPhi_eq_phi (q : ℕ → PlanarPoint K) (X : IntervalArray)
    {i j : ℕ} (hij : i < j) (hq : IntervalNoncollinear q i j) :
    spinorOrdinaryPhi q X i j =
      phi (polygonSignArray q) (polygonSignArray q) X i j := by
  unfold spinorOrdinaryPhi phi cutContribution
  apply Finset.sum_congr rfl
  intro S hS
  rw [spinorOrdinaryVertex_eq_gateProduct q hij hq (Finset.mem_powerset.mp hS)]

/-- The actual marked spinor vertex functional is the source marked map. -/
theorem spinorMarkedPhi_eq_phi (q : ℕ → PlanarPoint K) (X : IntervalArray)
    {i j : ℕ} (hij : i < j) (hq : IntervalNoncollinear q i j) :
    spinorMarkedPhi q X i j =
      phi (polygonSignArray q) (fun a b c => -polygonSignArray q a b c) X i j := by
  unfold spinorMarkedPhi phi cutContribution
  apply Finset.sum_congr rfl
  intro S hS
  rw [spinorMarkedVertex_eq_gateProduct q hij hq (Finset.mem_powerset.mp hS)]

/-- The constructed ordinary current obeys the published recurrence with
at least three branches, expressed in the original spinor ratio vertices. -/
theorem ordinaryCurrent_spinor_recurrence (q : ℕ → PlanarPoint K)
    {i j : ℕ} (hij : i < j) (hq : IntervalNoncollinear q i j) :
    ordinaryCurrent (polygonSignArray q) (polygonSignArray q) i j =
      source i j -
        ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => 2 ≤ S.card),
          spinorOrdinaryVertex q i j S *
            branchProduct (ordinaryCurrent (polygonSignArray q) (polygonSignArray q))
              (cutVertices i j S) := by
  rw [ordinaryCurrent_self_recurrence _ hij]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  rw [spinorOrdinaryVertex_eq_gateProduct q hij hq
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)]
  rfl

/-- The difference of the original marked and ordinary vertex sums,
evaluated on any supplied branch array. The published overall minus sign
on (ordinary minus marked) is written as marked minus ordinary. -/
noncomputable def spinorVertexDifference (q : ℕ → PlanarPoint K)
    (X : IntervalArray) (i j : ℕ) : ℚ :=
  spinorMarkedPhi q X i j - spinorOrdinaryPhi q X i j

/-- On the actual ordinary current the published difference expression
has exactly the source correction, also on a one-edge word. -/
theorem spinorVertexDifference_eq_marked_sub_source (q : ℕ → PlanarPoint K)
    {i j : ℕ} (hij : i < j) (hq : IntervalNoncollinear q i j) :
    spinorVertexDifference q
        (ordinaryCurrent (polygonSignArray q) (polygonSignArray q)) i j =
      markedAmplitude (polygonSignArray q) (polygonSignArray q) i j - source i j := by
  unfold spinorVertexDifference
  rw [spinorMarkedPhi_eq_phi q _ hij hq, spinorOrdinaryPhi_eq_phi q _ hij hq]
  exact vertexDifferenceAmplitude_eq_marked_sub_source (polygonSignArray q) hij

/-- Genuine polygon words have at least two complementary edges, so the
published difference expression equals the note's marked current. -/
theorem spinorVertexDifference_eq_marked (q : ℕ → PlanarPoint K)
    {i j : ℕ} (hij : i + 1 < j) (hq : IntervalNoncollinear q i j) :
    spinorVertexDifference q
        (ordinaryCurrent (polygonSignArray q) (polygonSignArray q)) i j =
      markedAmplitude (polygonSignArray q) (polygonSignArray q) i j := by
  rw [spinorVertexDifference_eq_marked_sub_source q (by omega) hq]
  have hne : j ≠ i + 1 := by omega
  simp only [source, if_neg hne, sub_zero]

end DirectGLSSW
