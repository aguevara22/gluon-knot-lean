import SM.WallGerm

/-! Both actual punctured side images are connected and lie in unique genuine
chambers. Side values are independent of the chosen point on that side. -/

namespace SM.WallGerm

open Set Topology

variable {n : ℕ} (g : WallGerm n)

instance sideParameter_connectedSpace : ConnectedSpace g.SideParameter :=
  isConnected_iff_connectedSpace.mp (isConnected_Ioo g.radius_pos)

def labelledSide (positive : Bool) : Set (GenericTuple n) :=
  labelledChamber (g.sideTuple positive g.sideBase)

def side (positive : Bool) : Set (GenericPolygon n) :=
  chamber (g.sidePolygon positive g.sideBase)

theorem labelledSideRange_connected (positive : Bool) :
    IsConnected (Set.range (g.sideTuple positive)) :=
  isConnected_range (g.continuous_sideTuple positive)

theorem sideRange_connected (positive : Bool) :
    IsConnected (Set.range (g.sidePolygon positive)) :=
  isConnected_range (g.continuous_sidePolygon positive)

theorem sideTuple_mem_labelledSide (positive : Bool) (t : g.SideParameter) :
    g.sideTuple positive t ∈ g.labelledSide positive :=
  (g.labelledSideRange_connected positive).subset_connectedComponent
    (Set.mem_range_self g.sideBase) (Set.mem_range_self t)

theorem sidePolygon_mem_side (positive : Bool) (t : g.SideParameter) :
    g.sidePolygon positive t ∈ g.side positive :=
  (g.sideRange_connected positive).subset_connectedComponent
    (Set.mem_range_self g.sideBase) (Set.mem_range_self t)

theorem labelledSide_eq_at (positive : Bool) (t : g.SideParameter) :
    g.labelledSide positive = labelledChamber (g.sideTuple positive t) :=
  connectedComponent_eq (g.sideTuple_mem_labelledSide positive t)

theorem side_eq_at (positive : Bool) (t : g.SideParameter) :
    g.side positive = chamber (g.sidePolygon positive t) :=
  connectedComponent_eq (g.sidePolygon_mem_side positive t)

theorem side_unique (positive : Bool) (Q : GenericPolygon n)
    (hQ : ∀ t, g.sidePolygon positive t ∈ chamber Q) :
    chamber Q = g.side positive :=
  connectedComponent_eq (hQ g.sideBase)

theorem side_projection (hn : 3 ≤ n) (positive : Bool) :
    polygonProjection '' g.labelledSide positive = g.side positive :=
  projection_labelledChamber_eq_chamber hn (g.sideTuple positive g.sideBase)

def ConstantOnChambers {α : Type*} (F : GenericPolygon n → α) : Prop :=
  ∀ P Q, Q ∈ chamber P → F Q = F P

noncomputable def sideValue {α : Type*} (F : GenericPolygon n → α) (positive : Bool) : α :=
  F (g.sidePolygon positive g.sideBase)

theorem sideValue_eq_at {α : Type*} {F : GenericPolygon n → α}
    (hF : ConstantOnChambers F) (positive : Bool) (t : g.SideParameter) :
    g.sideValue F positive = F (g.sidePolygon positive t) :=
  (hF _ _ (g.sidePolygon_mem_side positive t)).symm

end SM.WallGerm
