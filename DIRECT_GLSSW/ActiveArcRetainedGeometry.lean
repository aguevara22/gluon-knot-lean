import ActiveArcRetainedWords
import ActiveArcPhysicalSuccessor

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalSegments
open DirectGLSSW ActiveArc RetainedWords
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

/-- A later event before the next anchor has a unique parameter on the same physical edge. -/
theorem bounded_event_physical_spec (y z : Event q) (hy : y≠terminal q)
    (hlt : letI := eventOrder q hR.noTriple; y<z)
    (hle : letI := eventOrder q hR.noTriple; z≤Sum.inl (physicalEdge q y hy).succ) :
    ∃ b : ℝ, parameter q y<b ∧ b≤1 ∧
      eventPoint q z=affinePoint (q (physicalEdge q y hy).castSucc) (q (physicalEdge q y hy).succ) b ∧
      ∀ t : ℝ, eventPoint q z=affinePoint (q (physicalEdge q y hy).castSucc)
        (q (physicalEdge q y hy).succ) t → t=b := by
  letI := eventOrder q hR.noTriple
  have hb : ∃ b : ℝ, parameter q y<b ∧ b≤1 ∧
      eventPoint q z=affinePoint (q (physicalEdge q y hy).castSucc) (q (physicalEdge q y hy).succ) b := by
    by_cases he : edgeTag q z=edgeTag q y
    · have hzn : z≠terminal q := by
        intro hh
        rw [hh] at he
        have hyb := edgeTag_lt q y hy
        change n+1=edgeTag q y at he
        omega
      have hedge : physicalEdge q z hzn=physicalEdge q y hy := Fin.ext he
      have hp : parameter q y<parameter q z := by
        rcases (event_lt_iff q hR.noTriple y z).mp hlt with hh|hh
        · exact False.elim ((ne_of_lt hh) he.symm)
        · exact hh.2
      refine ⟨parameter q z,hp,le_of_lt (parameter_bounds q z).2,?_⟩
      rw [eventPoint_affine q z hzn,hedge]
    · have htag : edgeTag q y<edgeTag q z := by
        rcases (event_lt_iff q hR.noTriple y z).mp hlt with hh|hh
        · exact hh
        · exact False.elim (he hh.1.symm)
      have hz : z=Sum.inl (physicalEdge q y hy).succ :=
        le_antisymm hle (anchor_le_of_tag_le q hR (physicalEdge q y hy).succ z (by change edgeTag q y+1≤edgeTag q z;omega))
      refine ⟨1,(parameter_bounds q y).2,le_rfl,?_⟩
      rw [hz]
      exact (affinePoint_one _ _).symm
  obtain ⟨b,hb,hb1,hpoint⟩ := hb
  refine ⟨b,hb,hb1,hpoint,?_⟩
  intro t ht
  exact edge_parameter_unique q hR (physicalEdge q y hy) t b (ht.symm.trans hpoint)

variable (S : Finset (Crossing q))

/-- Before the next retained event, every positive iterate stays before the next original
anchor of the paired outgoing edge. The endpoint seam cannot occur in this interval. -/
theorem firstReturn_prefix_bounded (x : Event q) (hx : x≠terminal q) (d : ℕ)
    (hno : ∀ k : ℕ, 0<k → k<d → ¬retained q S ((incoming q hR.noTriple S ^ k) x)) :
    ∀ k : ℕ, 0<k → k≤d →
      letI := eventOrder q hR.noTriple
      pairing q S x<(incoming q hR.noTriple S ^ k) x ∧
      (incoming q hR.noTriple S ^ k) x≤Sum.inl (outgoingEdge q S x hx).succ := by
  letI := eventOrder q hR.noTriple
  let y := pairing q S x
  let a : Event q := Sum.inl (outgoingEdge q S x hx).succ
  have hy : y≠terminal q := pairing_ne_terminal q S x hx
  have hya : y<a := by
    apply (event_lt_iff q hR.noTriple _ _).mpr
    left
    change edgeTag q y<edgeTag q y+1
    omega
  intro k
  induction k with
  | zero => intro hk;omega
  | succ k ih =>
    intro hk hkd
    by_cases hk0 : k=0
    · subst k
      simp only [zero_add,pow_one,incoming,Equiv.Perm.mul_apply]
      exact ⟨successor_strict_before_terminal q hR.noTriple y hy,successor_min q hR y a hy hya⟩
    · have hkp : 0<k := by omega
      have hi := ih hkp (by omega)
      let u := (incoming q hR.noTriple S ^ k) x
      have hnr : ¬retained q S u := hno k hkp (by omega)
      have hut : u≠terminal q := by
        intro hh;apply hnr;rw [hh];exact (endpoints_retained q S).2
      have hua : u<a := by
        apply lt_of_le_of_ne hi.2
        intro hh
        apply hnr
        change retained q S ((incoming q hR.noTriple S ^ k) x)
        rw [hh]
        trivial
      have hf := pairing_fixes_nonretained q S u hnr
      have hs : u < incoming q hR.noTriple S u := by
        change u<successor q hR.noTriple (pairing q S u)
        rw [hf]
        exact successor_strict_before_terminal q hR.noTriple u hut
      have hb : incoming q hR.noTriple S u≤a := by
        change successor q hR.noTriple (pairing q S u)≤a
        rw [hf]
        exact successor_min q hR u a hut hua
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact ⟨lt_trans hi.1 hs,hb⟩

/-- The intermediate visits are strictly forward along the physical event order. -/
theorem firstReturn_prefix_step (x : Event q) (d k : ℕ) (hk : 0<k) (hkd : k<d)
    (hno : ∀ j : ℕ, 0<j → j<d → ¬retained q S ((incoming q hR.noTriple S ^ j) x)) :
    letI := eventOrder q hR.noTriple
    (incoming q hR.noTriple S ^ k) x<(incoming q hR.noTriple S ^ (k+1)) x := by
  letI := eventOrder q hR.noTriple
  let u := (incoming q hR.noTriple S ^ k) x
  have hn := hno k hk hkd
  have hu : u≠terminal q := by
    intro hh;apply hn;rw [show (incoming q hR.noTriple S ^ k) x=terminal q from hh]
    exact (endpoints_retained q S).2
  rw [pow_succ',Equiv.Perm.mul_apply]
  change u<successor q hR.noTriple (pairing q S u)
  rw [pairing_fixes_nonretained q S u hn]
  exact successor_strict_before_terminal q hR.noTriple u hu

/-- Compressing to the next retained corner follows one positive physical subsegment.
The sole excluded source is the terminal endpoint, whose next permutation step is the seam. -/
theorem retained_side_physical (root : Event q) (c : Corner q hR S root)
    (hx : eventAt q hR S root c.val≠terminal q) :
    ∃ a b : ℝ, 0≤a ∧ a<b ∧ b≤1 ∧
      eventPoint q (eventAt q hR S root c.val)=
        affinePoint (q (outgoingEdge q S (eventAt q hR S root c.val) hx).castSucc)
          (q (outgoingEdge q S (eventAt q hR S root c.val) hx).succ) a ∧
      eventPoint q (eventAt q hR S root (nextCorner q hR S root c).val)=
        affinePoint (q (outgoingEdge q S (eventAt q hR S root c.val) hx).castSucc)
          (q (outgoingEdge q S (eventAt q hR S root c.val) hx).succ) b ∧
      ∀ t : ℝ, eventPoint q (eventAt q hR S root (nextCorner q hR S root c).val)=
        affinePoint (q (outgoingEdge q S (eventAt q hR S root c.val) hx).castSucc)
          (q (outgoingEdge q S (eventAt q hR S root c.val) hx).succ) t → t=b := by
  let x := eventAt q hR S root c.val
  let d := cornerGap q hR S root c
  have hf := corner_firstReturn q hR S root c
  have hb := firstReturn_prefix_bounded q hR S x hx d hf.2.2 d hf.1 le_rfl
  rw [hf.2.1] at hb
  obtain ⟨b,hb0,hb1,hpoint,hunique⟩ := bounded_event_physical_spec q hR
    (pairing q S x) (eventAt q hR S root (nextCorner q hR S root c).val)
    (pairing_ne_terminal q S x hx) hb.1 hb.2
  refine ⟨parameter q (pairing q S x),b,(parameter_bounds q _).1,hb0,hb1,?_,hpoint,hunique⟩
  rw [← pairing_point q S x]
  exact eventPoint_affine q _ (pairing_ne_terminal q S x hx)

end DirectGLSSW.ActiveArc.PhysicalSegments
