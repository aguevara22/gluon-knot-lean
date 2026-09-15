import SM.NamedWallPredicates
import SM.CuspDefinition

/-! The six printed wall kinds and their actual central conditions.
These conditions omit only the germ's separate sign-change requirements. -/

namespace SM

variable {n : ℕ} [NeZero n]

inductive WallKind where
  | flat | cusp | vertex | triple | extension | cut
  deriving DecidableEq

def FlatCenterAt (P : LabelledTuple n) (j : ZMod n) : Prop :=
  4 ≤ n ∧ pointZeroTriples P = {turnSupport j} ∧ concurrenceTriples P = ∅ ∧
    StrictBetween (P (j - 1)) (P j) (P (j + 1))

def CuspCenterAt (P : LabelledTuple n) (j : ZMod n) : Prop :=
  4 ≤ n ∧ pointZeroTriples P = {turnSupport j} ∧ concurrenceTriples P = ∅ ∧
    ¬ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ P j = P (j - 1) + t • (P (j + 1) - P (j - 1))

def VertexCenterAt (P : LabelledTuple n) (M a : ZMod n) : Prop :=
  ContactSeparated M a ∧ pointZeroTriples P = {contactSupport M a} ∧
    concurrenceTriples P = ∅ ∧ P M ∈ edgeInterior P a

def TripleCenterAt (P : LabelledTuple n) (e f k : ZMod n) : Prop :=
  pointZeroTriples P = ∅ ∧ concurrenceTriples P = {{e, f, k}}

def ExtensionCenterAt (P : LabelledTuple n) (M a : ZMod n) : Prop :=
  ContactSeparated M a ∧ pointZeroTriples P = {contactSupport M a} ∧
    concurrenceTriples P = ∅ ∧ (∃ t : ℝ, P M = edgePoint P a t) ∧ P M ∉ edgeSegment P a

def CutCenterAt (P : LabelledTuple n) (i j k : ZMod n) : Prop :=
  NoConsecutive ({i, j, k} : Finset (ZMod n)) ∧ pointZeroTriples P = {{i, j, k}} ∧
    concurrenceTriples P = ∅

inductive WallCenterKind (P : LabelledTuple n) : WallKind → Prop where
  | flat (j : ZMod n) (h : FlatCenterAt P j) : WallCenterKind P .flat
  | cusp (j : ZMod n) (h : CuspCenterAt P j) : WallCenterKind P .cusp
  | vertex (M a : ZMod n) (h : VertexCenterAt P M a) : WallCenterKind P .vertex
  | triple (e f k : ZMod n) (h : TripleCenterAt P e f k) : WallCenterKind P .triple
  | extension (M a : ZMod n) (h : ExtensionCenterAt P M a) : WallCenterKind P .extension
  | cut (i j k : ZMod n) (h : CutCenterAt P i j k) : WallCenterKind P .cut

namespace WallGerm

def HasWallKind (g : WallGerm n) : WallKind → Prop
  | .flat => ∃ j, g.FlatAt j
  | .cusp => ∃ j, g.CuspAt j
  | .vertex => ∃ M a, g.VertexEdgeAt M a
  | .triple => ∃ e f k, g.TripleAt e f k
  | .extension => ∃ M a, g.ExtensionAt M a
  | .cut => ∃ i j k, g.PureCutAt i j k

def Simple (g : WallGerm n) : Prop := ∃ kind : WallKind, g.HasWallKind kind

theorem hasWallKind_center {g : WallGerm n} {kind : WallKind} (h : g.HasWallKind kind) :
    WallCenterKind g.center kind := by
  cases kind with
  | flat =>
    obtain ⟨j, h⟩ := h
    exact .flat j ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | cusp =>
    obtain ⟨j, h⟩ := h
    exact .cusp j ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | vertex =>
    obtain ⟨M, a, h⟩ := h
    exact .vertex M a ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | triple =>
    obtain ⟨e, f, k, h⟩ := h
    exact .triple e f k ⟨h.1, h.2.1⟩
  | extension =>
    obtain ⟨M, a, h⟩ := h
    exact .extension M a ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  | cut =>
    obtain ⟨i, j, k, h⟩ := h
    exact .cut i j k ⟨h.1, h.2.1, h.2.2.1⟩

end WallGerm
end SM
