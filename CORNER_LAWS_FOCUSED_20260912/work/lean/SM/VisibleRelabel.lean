import SM.VisibleSignature

/-! The induced cyclic relabelling of all three signature components.
Turns at new label i read old label i+a; old crossing labels move by -a. -/

namespace SM

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem translateSupport_zero (s : Finset (ZMod n)) : translateSupport 0 s = s := by
  simp [translateSupport]

theorem translateSupport_add (a b : ZMod n) (s : Finset (ZMod n)) :
    translateSupport a (translateSupport b s) = translateSupport (a + b) s := by
  simp [translateSupport, Finset.image_image, add_assoc, add_comm, add_left_comm]

noncomputable def visibleSignatureShift (a : ZMod n) (s : VisibleSignatureData n) :
    VisibleSignatureData n :=
  (fun i => s.1 (i + a), s.2.1.image (translateSupport (-a)),
    s.2.2.map (translateSupport (-a)))

theorem visibleSignatureShift_zero (s : VisibleSignatureData n) :
    visibleSignatureShift 0 s = s := by
  rcases s with ⟨t, X, w⟩
  change (fun i => t (i + 0), X.image (translateSupport (-0)),
    w.map (translateSupport (-0))) = (t, X, w)
  have hz : translateSupport (0 : ZMod n) = id := funext translateSupport_zero
  simp only [add_zero, neg_zero, hz, Finset.image_id, cycle_map_id]

theorem visibleSignatureShift_add (a b : ZMod n) (s : VisibleSignatureData n) :
    visibleSignatureShift a (visibleSignatureShift b s) = visibleSignatureShift (a + b) s := by
  have hc : translateSupport (-a) ∘ translateSupport (-b) = translateSupport (-(a + b)) := by
    funext X
    simpa only [Function.comp_apply, neg_add] using translateSupport_add (-a) (-b) X
  apply Prod.ext
  · funext i
    exact congrArg s.1 (add_assoc i a b)
  · apply Prod.ext
    · change (s.2.1.image (translateSupport (-b))).image (translateSupport (-a)) = _
      rw [Finset.image_image]
      exact congrArg (fun f => s.2.1.image f) hc
    · change (s.2.2.map (translateSupport (-b))).map (translateSupport (-a)) = _
      rw [cycle_map_map, hc]
      rfl

theorem crossingSet_shift [NeZero n] (P : LabelledTuple n) (a : ZMod n) :
    crossingSet (shift a P) = (crossingSet P).image (translateSupport (-a)) := by
  ext s
  rw [mem_crossingSet, Finset.mem_image]
  constructor
  · intro hs
    obtain ⟨c, hc⟩ := (crossingShiftEquiv a P).surjective (⟨s, hs⟩ : Crossing (shift a P))
    exact ⟨c.val, (mem_crossingSet P c.val).mpr c.property, congrArg Subtype.val hc⟩
  · rintro ⟨s, hs, rfl⟩
    exact (crossingShift a (⟨s, (mem_crossingSet P s).mp hs⟩ : Crossing P)).property

theorem gaussSupportWord_shift (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : ZMod n) : gaussSupportWord hn ((generic_shift a P).mpr hP) =
      (gaussSupportWord hn hP).map (translateSupport (-a)) := by
  have h := congrArg (fun w : Cycle (Crossing (shift a P)) => w.map (fun c => c.val))
    (gaussWord_shift hn hP a)
  rw [cycle_map_map] at h
  unfold gaussSupportWord
  rw [cycle_map_map]
  exact h.symm

theorem visibleSignature_shift (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (a : ZMod n) : visibleSignature hn (shift a P) ((generic_shift a P).mpr hP) =
      visibleSignatureShift a (visibleSignature hn P hP) := by
  haveI : NeZero n := ⟨by omega⟩
  apply Prod.ext
  · funext i
    exact turn_shift a P i
  · apply Prod.ext
    · exact crossingSet_shift P a
    · exact gaussSupportWord_shift hn hP a

end SM
