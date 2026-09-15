import SM.Crossings

/-! Cyclic relabelling for every component of source def:crossings. -/

namespace SM

variable {n : ℕ}

def translateSupport (a : ZMod n) (s : Finset (ZMod n)) : Finset (ZMod n) :=
  s.image (fun i => i + a)

theorem translateSupport_cancel (a : ZMod n) (s : Finset (ZMod n)) :
    translateSupport a (translateSupport (-a) s) = s := by
  simp [translateSupport, Finset.image_image, add_assoc]

theorem remote_add (a i j : ZMod n) : remote (i + a) (j + a) ↔ remote i j := by
  have he : (j + a) - (i + a) = j - i := by ring
  simp only [remote, adjacent, he]

/-- If the tuple shifts forward by a, its old edge i has new label i-a. -/
def crossingShift (a : ZMod n) {P : LabelledTuple n} (c : Crossing P) :
    Crossing (shift a P) := ⟨translateSupport (-a) c.val, by
  obtain ⟨i, j, hs, hr, hmeet⟩ := c.property
  refine ⟨i - a, j - a, ?_, ?_, ?_⟩
  · simp [translateSupport, hs, sub_eq_add_neg]
  · simpa only [sub_eq_add_neg] using (remote_add (-a) i j).mpr hr
  · simpa only [edgeSegment_shift, sub_add_cancel] using hmeet⟩

def crossingUnshift (a : ZMod n) {P : LabelledTuple n} (d : Crossing (shift a P)) :
    Crossing P := ⟨translateSupport a d.val, by
  obtain ⟨i, j, hs, hr, hmeet⟩ := d.property
  refine ⟨i + a, j + a, ?_, (remote_add a i j).mpr hr, ?_⟩
  · simp [translateSupport, hs]
  · simpa only [edgeSegment_shift] using hmeet⟩

def crossingShiftEquiv (a : ZMod n) (P : LabelledTuple n) :
    Crossing P ≃ Crossing (shift a P) where
  toFun := crossingShift a
  invFun := crossingUnshift a
  left_inv c := by
    apply Subtype.ext
    exact translateSupport_cancel a c.val
  right_inv d := by
    apply Subtype.ext
    change translateSupport (-a) (translateSupport a d.val) = d.val
    simpa only [neg_neg] using translateSupport_cancel (-a) d.val

theorem mem_crossingShift (a : ZMod n) {P : LabelledTuple n} (c : Crossing P)
    (i : ZMod n) (hi : i ∈ c.val) : i - a ∈ (crossingShift a c).val := by
  exact Finset.mem_image.mpr ⟨i, hi, (sub_eq_add_neg i a).symm⟩

theorem crossingPoint_shift (hn : 3 ≤ n) {P : LabelledTuple n} (h : G1 P)
    (a : ZMod n) (c : Crossing P) : crossingPoint (crossingShift a c) = crossingPoint c := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  apply crossingPoint_unique h c
  intro i hi
  have hm := crossingPoint_mem (crossingShift a c) (i - a) (mem_crossingShift a c i hi)
  simpa only [edgeSegment_shift, sub_add_cancel] using hm

theorem crossingParameter_shift (hn : 3 ≤ n) {P : LabelledTuple n} (h : G1 P)
    (a : ZMod n) (c : Crossing P) (i : ZMod n) (hi : i ∈ c.val) :
    crossingParameter (crossingShift a c) (i - a) (mem_crossingShift a c i hi) =
      crossingParameter c i hi := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hshift := (crossingParameter_spec (crossingShift a c)
    (i - a) (mem_crossingShift a c i hi)).2.2
  rw [crossingPoint_shift hn h, edgePoint_shift, sub_add_cancel] at hshift
  apply edgePoint_injective (g1_edge_ne_zero hn h i)
  exact hshift.symm.trans (crossingParameter_spec c i hi).2.2

theorem crossingSign_shift (P : LabelledTuple n) (a i j : ZMod n) :
    crossingSign (shift a P) (i - a) (j - a) = crossingSign P i j := by
  simp only [crossingSign, edge_shift, sub_add_cancel]

/-- Review aggregate binding the exact source crossing set, point, parameter
and directed reading sign. Source uniqueness/interiority are proved under G1;
crossingShiftEquiv and the three shift laws supply representative independence. -/
noncomputable def crossingData [NeZero n] (P : LabelledTuple n) :=
  (crossingSet P, @crossingPoint n P, @crossingParameter n P, crossingSign P)

end SM
