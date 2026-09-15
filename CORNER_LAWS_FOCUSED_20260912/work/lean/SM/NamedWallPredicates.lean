import SM.GermDefinition
import SM.StrictBetween
import SM.ContactCenter
import SM.PureCutIndices

/-! The exact F/V/T/E/C predicates consumed by lem:wall-sides.
This is not the completed def:walls: cusp side/empty data, named side
conventions, mutual exclusivity and cyclic compatibility remain to be proved. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

def FlatAt (j : ZMod n) : Prop :=
  4 ≤ n ∧ g.pointZeros = {turnSupport j} ∧ g.concurrences = ∅ ∧
  StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)) ∧
  g.SignChanges (fun P => (turn P j : ℝ))

def VertexEdgeAt (M a : ZMod n) : Prop :=
  ContactSeparated M a ∧ g.pointZeros = {contactSupport M a} ∧ g.concurrences = ∅ ∧
  g.center M ∈ edgeInterior g.center a ∧
  g.SignChanges (fun P => (chi P a (a + 1) M : ℝ))

def BigonAt (M a : ZMod n) : Prop :=
  g.VertexEdgeAt M a ∧ chi g.center a (a + 1) (M - 1) = chi g.center a (a + 1) (M + 1)

def SlidingAt (M a : ZMod n) : Prop :=
  g.VertexEdgeAt M a ∧ chi g.center a (a + 1) (M - 1) ≠ chi g.center a (a + 1) (M + 1)

def TripleAt (e f k : ZMod n) : Prop :=
  g.pointZeros = ∅ ∧ g.concurrences = {{e, f, k}} ∧
  g.SignChanges (fun P => edgeParameter P e f - edgeParameter P e k) ∧
  g.SignChanges (fun P => edgeParameter P f e - edgeParameter P f k) ∧
  g.SignChanges (fun P => edgeParameter P k e - edgeParameter P k f)

def ExtensionAt (M a : ZMod n) : Prop :=
  ContactSeparated M a ∧ g.pointZeros = {contactSupport M a} ∧ g.concurrences = ∅ ∧
  (∃ t : ℝ, g.center M = edgePoint g.center a t) ∧
  g.center M ∉ edgeSegment g.center a ∧
  g.SignChanges (fun P => (chi P a (a + 1) M : ℝ))

def PureCutAt (i j k : ZMod n) : Prop :=
  NoConsecutive ({i, j, k} : Finset (ZMod n)) ∧ g.pointZeros = {{i, j, k}} ∧
  g.concurrences = ∅ ∧ g.SignChanges (fun P => (chi P i j k : ℝ))

theorem vertexEdge_bigon_or_sliding {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    g.BigonAt M a ∨ g.SlidingAt M a := by
  by_cases he : chi g.center a (a + 1) (M - 1) = chi g.center a (a + 1) (M + 1)
  · exact Or.inl ⟨h, he⟩
  · exact Or.inr ⟨h, he⟩

theorem bigon_not_sliding {M a : ZMod n} (h : g.BigonAt M a) : ¬ g.SlidingAt M a :=
  fun hs => hs.2 h.2

theorem vertexEdge_regular (hn : 3 ≤ n) {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    Regular g.center := contact_regular hn h.1 h.2.1

theorem extension_regular (hn : 3 ≤ n) {M a : ZMod n} (h : g.ExtensionAt M a) :
    Regular g.center := contact_regular hn h.1 h.2.1

theorem pureCut_regular {i j k : ZMod n} (h : g.PureCutAt i j k) :
    Regular g.center := by
  have hn := noConsecutive_size (singlePointTriple_data h.2.1).1 h.1
  exact singlePointTriple_nonflat_regular (by omega) h.2.1 (noConsecutive_ne_turnSupport h.1)

theorem triple_regular (hn : 3 ≤ n) {e f k : ZMod n} (h : g.TripleAt e f k) :
    Regular g.center := g1_regular hn ((g.pointZeros_empty_iff).mp h.1)

end SM.WallGerm
