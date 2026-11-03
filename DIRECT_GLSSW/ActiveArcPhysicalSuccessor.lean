import ActiveArcRegularGeometry
import ActiveArcClosedCorners

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalSegments
open DirectGLSSW ActiveArc
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

include hR in
/-- Chosen visit points equal every actual physical pair intersection on the regular domain. -/
theorem visitPoint_eq_of_intersection (v : Visit q) (x : PlanarPoint ℝ)
    (hl : edgeInterior q v.1.val.1 x) (hr : edgeInterior q v.1.val.2 x) :
    eventPoint q (Sum.inr v)=x :=
  crossingPoint_eq_of_mem_regular q hR v.1 x hl hr

theorem parameter_bounds (x : Event q) : 0≤parameter q x ∧ parameter q x<1 := by
  cases x with
  | inl i => exact ⟨le_rfl,zero_lt_one⟩
  | inr v => exact ⟨le_of_lt (visitParameter_spec q v).1,(visitParameter_spec q v).2.1⟩

theorem edgeTag_lt (x : Event q) (hx : x≠terminal q) : edgeTag q x<n+1 := by
  cases x with
  | inl i =>
    have hi := i.isLt
    have hn : i.val≠n+1 := by
      intro he
      apply hx
      apply congrArg Sum.inl
      exact Fin.ext he
    change i.val<n+1
    omega
  | inr v => exact (visitEdge q v).isLt

def physicalEdge (x : Event q) (hx : x≠terminal q) : Fin (n+1) := ⟨edgeTag q x,edgeTag_lt q x hx⟩

theorem eventPoint_affine (x : Event q) (hx : x≠terminal q) :
    eventPoint q x=affinePoint (q (physicalEdge q x hx).castSucc)
      (q (physicalEdge q x hx).succ) (parameter q x) := by
  cases x with
  | inl i =>
    have he : (physicalEdge q (Sum.inl i) hx).castSucc=i := Fin.ext rfl
    rw [he]
    exact (affinePoint_zero _ _).symm
  | inr v => exact (visitParameter_spec q v).2.2

include hR in
theorem anchor_le_of_tag_le (i : Fin (n+2)) (x : Event q) (hi : i.val≤edgeTag q x) :
    letI : LinearOrder (Event q) := eventOrder q hR.noTriple; (show Event q from Sum.inl i)≤x := by
  letI := eventOrder q hR.noTriple
  apply le_of_not_gt
  intro hh
  rcases (event_lt_iff q hR.noTriple x (Sum.inl i)).mp hh with hh|⟨_,hh⟩
  · exact (not_lt_of_ge hi) hh
  · exact (not_lt_of_ge (parameter_bounds q x).1) hh

theorem successor_min (x z : Event q) (hx : x≠terminal q)
    (hz : letI := eventOrder q hR.noTriple; x<z) :
    letI := eventOrder q hR.noTriple; successor q hR.noTriple x≤z := by
  letI := eventOrder q hR.noTriple
  rcases orderedCyclicSuccessor_order_spec (Event q) x with hh|hh
  · exact hh.2 z hz
  · exact False.elim ((not_lt_of_ge (hh.1 z)) hz)

/-- The next event lies later on the same physical edge or at that edge's endpoint anchor. -/
theorem successor_sameEdge_or_anchor (x : Event q) (hx : x≠terminal q) :
    (edgeTag q (successor q hR.noTriple x)=edgeTag q x ∧
      parameter q x<parameter q (successor q hR.noTriple x)) ∨
    successor q hR.noTriple x=Sum.inl (physicalEdge q x hx).succ := by
  letI := eventOrder q hR.noTriple
  let y := successor q hR.noTriple x
  have hxy : x<y := successor_strict_before_terminal q hR.noTriple x hx
  have hxa : x<(Sum.inl (physicalEdge q x hx).succ : Event q) := by
    apply (event_lt_iff q hR.noTriple _ _).mpr
    left
    change edgeTag q x<edgeTag q x+1
    omega
  have hya : y≤Sum.inl (physicalEdge q x hx).succ := successor_min q hR x _ hx hxa
  by_cases he : edgeTag q y=edgeTag q x
  · left
    refine ⟨he,?_⟩
    rcases (event_lt_iff q hR.noTriple x y).mp hxy with hh|hh
    · exact False.elim ((ne_of_lt hh) he.symm)
    · exact hh.2
  · right
    have htag : edgeTag q x<edgeTag q y := by
      rcases (event_lt_iff q hR.noTriple x y).mp hxy with hh|hh
      · exact hh
      · exact False.elim (he hh.1.symm)
    exact le_antisymm hya (anchor_le_of_tag_le q hR (physicalEdge q x hx).succ y (by change edgeTag q x+1≤edgeTag q y;omega))

def endParameter (x : Event q) : ℝ :=
  if edgeTag q (successor q hR.noTriple x)=edgeTag q x then
    parameter q (successor q hR.noTriple x) else 1

/-- The source-facing physical step has a uniquely determined forward edge parameter. -/
theorem successor_physical_spec (x : Event q) (hx : x≠terminal q) :
    parameter q x<endParameter q hR x ∧ endParameter q hR x≤1 ∧
    eventPoint q (successor q hR.noTriple x)=
      affinePoint (q (physicalEdge q x hx).castSucc) (q (physicalEdge q x hx).succ) (endParameter q hR x) ∧
    ∀ t : ℝ, eventPoint q (successor q hR.noTriple x)=
      affinePoint (q (physicalEdge q x hx).castSucc) (q (physicalEdge q x hx).succ) t →
      t=endParameter q hR x := by
  have hbase : parameter q x<endParameter q hR x ∧ endParameter q hR x≤1 ∧
      eventPoint q (successor q hR.noTriple x)=
        affinePoint (q (physicalEdge q x hx).castSucc) (q (physicalEdge q x hx).succ) (endParameter q hR x) := by
    rcases successor_sameEdge_or_anchor q hR x hx with ⟨he,ht⟩|hy
    · have hyn : successor q hR.noTriple x≠terminal q := by
        intro hh
        rw [hh] at he
        have hb := edgeTag_lt q x hx
        change n+1=edgeTag q x at he
        omega
      have hedge : physicalEdge q (successor q hR.noTriple x) hyn=physicalEdge q x hx := Fin.ext he
      simp only [endParameter,if_pos he]
      refine ⟨ht,le_of_lt (parameter_bounds q _).2,?_⟩
      rw [eventPoint_affine q _ hyn,hedge]
    · have he : edgeTag q (successor q hR.noTriple x)≠edgeTag q x := by
        rw [hy]
        change edgeTag q x+1≠edgeTag q x
        omega
      simp only [endParameter,if_neg he]
      refine ⟨(parameter_bounds q x).2,le_rfl,?_⟩
      rw [hy]
      exact (affinePoint_one _ _).symm
  refine ⟨hbase.1,hbase.2.1,hbase.2.2,?_⟩
  intro t ht
  exact edge_parameter_unique q hR (physicalEdge q x hx) t (endParameter q hR x)
    (ht.symm.trans hbase.2.2)

variable (S : Finset (Crossing q))

theorem pairing_point (x : Event q) : eventPoint q (pairing q S x)=eventPoint q x := by
  classical
  cases x with
  | inl i => rfl
  | inr v =>
    change eventPoint q (if v.1∈S then Sum.inr (v.1,!v.2) else Sum.inr v)=_
    split_ifs <;> rfl

theorem pairing_ne_terminal (x : Event q) (hx : x≠terminal q) : pairing q S x≠terminal q := by
  intro hh
  apply hx
  apply (pairing q S).injective
  exact hh

def outgoingEdge (x : Event q) (hx : x≠terminal q) : Fin (n+1) :=
  physicalEdge q (pairing q S x) (pairing_ne_terminal q S x hx)

/-- The actual smoothed incoming step follows the paired outgoing physical branch. -/
theorem incoming_physical_spec (x : Event q) (hx : x≠terminal q) :
    ∃ a b : ℝ, 0≤a ∧ a<b ∧ b≤1 ∧
      eventPoint q x=affinePoint (q (outgoingEdge q S x hx).castSucc) (q (outgoingEdge q S x hx).succ) a ∧
      eventPoint q (incoming q hR.noTriple S x)=
        affinePoint (q (outgoingEdge q S x hx).castSucc) (q (outgoingEdge q S x hx).succ) b ∧
      ∀ t : ℝ, eventPoint q (incoming q hR.noTriple S x)=
        affinePoint (q (outgoingEdge q S x hx).castSucc) (q (outgoingEdge q S x hx).succ) t → t=b := by
  let y := pairing q S x
  have hy := pairing_ne_terminal q S x hx
  have hs := successor_physical_spec q hR y hy
  refine ⟨parameter q y,endParameter q hR y,(parameter_bounds q y).1,hs.1,hs.2.1,?_,hs.2.2.1,hs.2.2.2⟩
  rw [← pairing_point q S x]
  exact eventPoint_affine q y hy

end DirectGLSSW.ActiveArc.PhysicalSegments
