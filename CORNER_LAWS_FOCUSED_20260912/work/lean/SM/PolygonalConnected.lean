import SM.WeakTopology
import Mathlib.Logic.Relation
import Mathlib.Analysis.Convex.Segment

/-! Finite polygonal chains in actual real vector spaces. The inductive
reflexive-transitive closure has finitely many affine-segment steps; it is not
an arbitrary continuous path supplied as a surrogate for a polygonal path. -/

namespace SM

open Set Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- A finite chain of straight closed segments, each wholly contained in S. -/
def PolygonalJoin (S : Set E) (x y : E) : Prop :=
  Relation.ReflTransGen (fun a b : E => segment ℝ a b ⊆ S) x y

def PolygonallyConnected (S : Set E) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, PolygonalJoin S x y

theorem polygonalJoin_mem {S : Set E} {x y : E} (hx : x ∈ S)
    (h : PolygonalJoin S x y) : y ∈ S := by
  induction h with
  | refl => exact hx
  | @tail b c _ hbc _ => exact hbc (right_mem_segment ℝ b c)

theorem isOpen_polygonal_reachable {S : Set E} (hS : IsOpen S) {x : E} (hx : x ∈ S) :
    IsOpen {y : E | PolygonalJoin S x y} := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  have hyS := polygonalJoin_mem hx hy
  obtain ⟨U, ⟨hU, hconv⟩, hUS⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) y).mem_iff.mp (hS.mem_nhds hyS)
  have hyU := mem_of_mem_nhds hU
  exact mem_of_superset hU fun z hz => hy.tail ((hconv.segment_subset hyU hz).trans hUS)

theorem isOpen_polygonal_unreachable {S : Set E} (hS : IsOpen S) (x : E) :
    IsOpen (S \ {y : E | PolygonalJoin S x y}) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨hyS, hyR⟩
  obtain ⟨U, ⟨hU, hconv⟩, hUS⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) y).mem_iff.mp (hS.mem_nhds hyS)
  have hyU := mem_of_mem_nhds hU
  refine mem_of_superset hU fun z hz => ⟨hUS hz, ?_⟩
  intro hzR
  exact hyR (hzR.tail ((hconv.segment_subset hz hyU).trans hUS))

theorem polygonallyConnected_of_isOpen_isPreconnected {S : Set E}
    (hS : IsOpen S) (hconn : IsPreconnected S) : PolygonallyConnected S := by
  intro x hx y hy
  have hr := isOpen_polygonal_reachable hS hx
  have hn := isOpen_polygonal_unreachable hS x
  have hd : Disjoint {z | PolygonalJoin S x z} (S \ {z | PolygonalJoin S x z}) := by
    exact disjoint_left.mpr (fun _ ha hb => hb.2 ha)
  have hcover : S ⊆ {z | PolygonalJoin S x z} ∪ (S \ {z | PolygonalJoin S x z}) := by
    intro z hz
    by_cases h : PolygonalJoin S x z
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  have hnonempty : (S ∩ {z | PolygonalJoin S x z}).Nonempty := ⟨x, hx, .refl⟩
  exact hconn.subset_left_of_subset_union hr hn hd hcover hnonempty hy

theorem open_components_polygonallyConnected {S : Set E} (hS : IsOpen S) (x : E) :
    IsOpen (connectedComponentIn S x) ∧ PolygonallyConnected (connectedComponentIn S x) :=
  ⟨hS.connectedComponentIn,
    polygonallyConnected_of_isOpen_isPreconnected hS.connectedComponentIn
      isPreconnected_connectedComponentIn⟩

end SM
