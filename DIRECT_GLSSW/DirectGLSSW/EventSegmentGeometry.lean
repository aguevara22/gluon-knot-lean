import DirectGLSSW.OrderedEventSuccessor
import DirectGLSSW.PolygonGeometry
import DirectGLSSW.AffineSegments

namespace DirectGLSSW.EventSegmentGeometry

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ}

theorem polygonEventSuccessor_sameEdge_next_or_nextAnchor
    (q : Fin n → PlanarPoint K)
    (hG2 : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (x : PolygonEvent q) :
    letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hG2
    let e := polygonEventEdge q x
    let y := polygonEventSuccessor q hG2 x
    (polygonEventEdge q y = e ∧
      polygonEventParameter q x < polygonEventParameter q y ∧
      ∀ z : PolygonEvent q, polygonEventEdge q z = e →
        polygonEventParameter q x < polygonEventParameter q z → y ≤ z) ∨
    (y = Sum.inl (cyclicSuccessor e) ∧
      ∀ z : PolygonEvent q, polygonEventEdge q z = e →
        polygonEventParameter q z ≤ polygonEventParameter q x) := by
  classical
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hG2
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hG2
  let e := polygonEventEdge q x
  let y := polygonEventSuccessor q hG2 x
  have hs := polygonEventSuccessor_order_spec q hG2 x
  have h_anchor_le (z : PolygonEvent q) :
      (Sum.inl (polygonEventEdge q z) : PolygonEvent q) ≤ z := by
    cases z with
    | inl a => exact le_rfl
    | inr v => exact le_of_lt (polygonEvent_anchor_lt_visit q hG2 v)
  rcases hs with ⟨hxy, hleast⟩ | ⟨hmax, hmin⟩
  · by_cases hey : polygonEventEdge q y = e
    · left
      refine ⟨hey, ?_, ?_⟩
      · exact (polygonEvent_sameEdge_lt_iff q hG2 x y hey.symm).1 hxy
      · intro z hze htz
        have hxz := (polygonEvent_sameEdge_lt_iff q hG2 x z hze.symm).2 htz
        exact hleast z hxz
    · have hed : e < polygonEventEdge q y := by
        have hlt := (polygonEvent_lt_iff q hG2 x y).1 hxy
        rcases hlt with hlt | ⟨heq, _⟩
        · exact hlt
        · exact (hey (by simpa [e] using heq.symm)).elim
      let a : PolygonEvent q := Sum.inl (polygonEventEdge q y)
      have haxy : x < a := by
        apply (polygonEvent_lt_iff q hG2 x a).2
        exact Or.inl hed
      have hay : a ≤ y := h_anchor_le y
      have hya : y ≤ a := hleast a haxy
      have hyeq : y = a := le_antisymm hya hay
      have hnext_val : (cyclicSuccessor e).val = e.val + 1 := by
        have hev : e.val + 1 < n := by
          have hltv := Fin.lt_iff_val_lt_val.mp hed
          have hyv := (polygonEventEdge q y).isLt
          omega
        change (e.val + 1 + 0) % n = e.val + 1
        rw [Nat.add_zero, Nat.mod_eq_of_lt hev]
      have hnext_le : y ≤ (Sum.inl (cyclicSuccessor e) : PolygonEvent q) := by
        apply hleast
        apply (polygonEvent_lt_iff q hG2 x _).2
        left
        have he_next : e < cyclicSuccessor e := by
          change e.val < (cyclicSuccessor e).val
          rw [hnext_val]
          omega
        simpa [e] using he_next
      have hey_le_next : polygonEventEdge q y ≤ cyclicSuccessor e := by
        have hya_next : a ≤ (Sum.inl (cyclicSuccessor e) : PolygonEvent q) := by
          rw [← hyeq]
          exact hnext_le
        have hfin : ¬ cyclicSuccessor e < polygonEventEdge q y := by
          intro hlt
          have hbad : (Sum.inl (cyclicSuccessor e) : PolygonEvent q) < a := by
            apply (polygonEvent_lt_iff q hG2 _ _).2
            exact Or.inl (by simpa [a] using hlt)
          exact (not_lt_of_ge hya_next) hbad
        exact le_of_not_gt hfin
      have heqnext : polygonEventEdge q y = cyclicSuccessor e := by
        apply Fin.ext
        have hle := Fin.le_iff_val_le_val.mp hey_le_next
        rw [hyeq] at hle
        dsimp [a] at hle
        omega
      right
      refine ⟨?_, ?_⟩
      · change y = Sum.inl (cyclicSuccessor e)
        exact hyeq.trans (congrArg Sum.inl heqnext)
      · intro z hze
        by_cases htz : polygonEventParameter q x < polygonEventParameter q z
        · have hxz := (polygonEvent_sameEdge_lt_iff q hG2 x z hze.symm).2 htz
          have hzy : z < y := by
            apply (polygonEvent_lt_iff q hG2 z y).2
            exact Or.inl (by simpa [hze, heqnext] using hed)
          have hyz := hleast z hxz
          exact False.elim ((not_le_of_gt hzy) hyz)
        · exact le_of_not_gt htz
  · have hlast_edge : e.val + 1 = n := by
      apply Classical.byContradiction
      intro hnot
      have he_lt := e.isLt
      have hlt : e.val + 1 < n := by omega
      let f : Fin n := ⟨e.val + 1, hlt⟩
      have hxf : x < (Sum.inl f : PolygonEvent q) := by
        apply (polygonEvent_lt_iff q hG2 x _).2
        left
        change e.val < f.val
        dsimp [f]
        omega
      have hle := hmax (Sum.inl f)
      exact False.elim ((not_le_of_gt hxf) hle)
    have h_edge_last : e.val = n - 1 := by omega
    let zero : Fin n := ⟨0, by omega⟩
    have hzero_le_y : (Sum.inl zero : PolygonEvent q) ≤ y := by
      by_cases hyzero : y < Sum.inl zero
      · have hlt := (polygonEvent_lt_iff q hG2 y (Sum.inl zero)).1 hyzero
        rcases hlt with hlt | ⟨heq, hparam⟩
        · have hz : ¬ polygonEventEdge q y < zero := by
            intro hlt'
            have : (polygonEventEdge q y).val < 0 := Fin.lt_iff_val_lt_val.mp hlt'
            omega
          exact False.elim (hz hlt)
        · have hpar_nonneg := (polygonEventParameter_bounds q y).1
          have hzparam : polygonEventParameter q (Sum.inl zero) = 0 := rfl
          rw [hzparam] at hparam
          exact False.elim ((not_lt_of_ge hpar_nonneg) hparam)
      · exact le_of_not_gt hyzero
    have hy_zero := hmin (Sum.inl zero)
    have h_y_zero : y = Sum.inl zero := le_antisymm hy_zero hzero_le_y
    have hsucc_zero : cyclicSuccessor e = zero := by
      apply Fin.ext
      change (e.val + 1 + 0) % n = zero.val
      rw [Nat.add_zero, h_edge_last]
      have hnpos : 0 < n := by omega
      have heq : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
      rw [heq]
      simp [zero]
    right
    refine ⟨?_, ?_⟩
    · change y = Sum.inl (cyclicSuccessor e)
      calc
        y = Sum.inl zero := h_y_zero
        _ = Sum.inl (cyclicSuccessor e) := congrArg Sum.inl hsucc_zero.symm
    · intro z hze
      by_cases htz : polygonEventParameter q x < polygonEventParameter q z
      · have hxz := (polygonEvent_sameEdge_lt_iff q hG2 x z hze.symm).2 htz
        exact False.elim ((not_le_of_gt hxz) (hmax z))
      · exact le_of_not_gt htz

noncomputable def polygonEventSuccessorTerminalParameter
    (q : Fin n → PlanarPoint K)
    (hG2 : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (x : PolygonEvent q) : K :=
  let e := polygonEventEdge q x
  let y := polygonEventSuccessor q hG2 x
  if polygonEventEdge q y = e
  then polygonEventParameter q y
  else 1

theorem polygonEventSuccessorTerminalParameter_spec
    (q : Fin n → PlanarPoint K)
    (hG2 : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (x : PolygonEvent q) :
    let e := polygonEventEdge q x
    let y := polygonEventSuccessor q hG2 x
    let u := polygonEventSuccessorTerminalParameter q hG2 hn x
    (polygonEventEdge q y = e → u = polygonEventParameter q y) ∧
    (y = Sum.inl (cyclicSuccessor e) → u = 1) := by
  by_cases he : polygonEventEdge q (polygonEventSuccessor q hG2 x) = polygonEventEdge q x
  · simp [polygonEventSuccessorTerminalParameter, he]
    intro hnext
    have hedge : polygonEventEdge q (polygonEventSuccessor q hG2 x) =
        cyclicSuccessor (polygonEventEdge q x) := by
      simpa [polygonEventEdge] using congrArg (polygonEventEdge q) hnext
    have hsucc : cyclicSuccessor (polygonEventEdge q x) = polygonEventEdge q x :=
      hedge.symm.trans he
    exact (cyclicSuccessor_ne_self (by omega) _ hsucc).elim
  · simp [polygonEventSuccessorTerminalParameter, he]

theorem polygonEventSuccessorTerminalParameter_bounds
    (q : Fin n → PlanarPoint K)
    (hG2 : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (x : PolygonEvent q) :
    polygonEventParameter q x <
      polygonEventSuccessorTerminalParameter q hG2 hn x ∧
    polygonEventSuccessorTerminalParameter q hG2 hn x ≤ 1 := by
  classical
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hG2
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hG2
  have hclass := polygonEventSuccessor_sameEdge_next_or_nextAnchor q hG2 hn x
  dsimp at hclass
  dsimp [polygonEventSuccessorTerminalParameter]
  rcases hclass with ⟨hey, hlt, _⟩ | ⟨hnext, _⟩
  · simp only [if_pos hey]
    exact ⟨hlt, (polygonEventParameter_bounds q
      (polygonEventSuccessor q hG2 x)).2.le⟩
  · have hne : polygonEventEdge q (polygonEventSuccessor q hG2 x) ≠
      polygonEventEdge q x := by
        intro heq
        have hedge : polygonEventEdge q (polygonEventSuccessor q hG2 x) =
            cyclicSuccessor (polygonEventEdge q x) := by
          simpa [polygonEventEdge] using congrArg (polygonEventEdge q) hnext
        have hsucc : cyclicSuccessor (polygonEventEdge q x) = polygonEventEdge q x :=
          hedge.symm.trans heq
        have hs := cyclicSuccessor_ne_self (by omega) (polygonEventEdge q x)
        exact hs hsucc
    simp only [if_neg hne]
    exact ⟨(polygonEventParameter_bounds q x).2, le_rfl⟩

theorem polygonEventSuccessor_positive_elementary_step
    (q : Fin n → PlanarPoint K)
    (hG2 : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (x : PolygonEvent q) :
    let e := polygonEventEdge q x
    let y := polygonEventSuccessor q hG2 x
    let t := polygonEventParameter q x
    let u := polygonEventSuccessorTerminalParameter q hG2 hn x
    polygonEventParameter q x < u ∧ u ≤ 1 ∧ 0 < u - t ∧
      polygonEventPoint q y =
        affinePoint (q e) (q (cyclicSuccessor e)) u ∧
      polygonEventPoint q y - polygonEventPoint q x =
        (u - t) • cyclicTangent q e := by
  let e := polygonEventEdge q x
  let y := polygonEventSuccessor q hG2 x
  let t := polygonEventParameter q x
  let u := polygonEventSuccessorTerminalParameter q hG2 hn x
  have hbounds := polygonEventSuccessorTerminalParameter_bounds q hG2 hn x
  rcases hbounds with ⟨hlt, hle⟩
  have hpoint : polygonEventPoint q y = affinePoint (q e) (q (cyclicSuccessor e)) u := by
    rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor q hG2 hn x with
      hsame | hnext
    · have hu := (polygonEventSuccessorTerminalParameter_spec q hG2 hn x).1 hsame.1
      have hu' : u = polygonEventParameter q y := by simpa [u] using hu
      calc
        polygonEventPoint q y =
            affinePoint (q (polygonEventEdge q y))
              (q (cyclicSuccessor (polygonEventEdge q y)))
              (polygonEventParameter q y) := polygonEventPoint_eq_affine q y
        _ = affinePoint (q e) (q (cyclicSuccessor e)) u := by
          rw [hsame.1, hu'.symm]
    · have hu := (polygonEventSuccessorTerminalParameter_spec q hG2 hn x).2 hnext.1
      have hu' : u = 1 := by simpa [u] using hu
      calc
        polygonEventPoint q y = q (cyclicSuccessor e) := by
          change polygonEventPoint q (polygonEventSuccessor q hG2 x) = _
          rw [hnext.1]
          rfl
        _ = affinePoint (q e) (q (cyclicSuccessor e)) u := by
          rw [hu', affinePoint_one]
  refine ⟨hlt, hle, sub_pos.mpr hlt, hpoint, ?_⟩
  calc
    polygonEventPoint q y - polygonEventPoint q x =
        affinePoint (q e) (q (cyclicSuccessor e)) u -
          affinePoint (q e) (q (cyclicSuccessor e)) t := by
      rw [hpoint, polygonEventPoint_eq_affine q x]
    _ = (u - t) • cyclicTangent q e := by
      ext <;> simp [affinePoint, cyclicTangent] <;> ring

theorem polygonEventSuccessor_step_ne_zero
    (q : Fin n → PlanarPoint K)
    (hG2 : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (hG1 : cyclicNoncollinear q) (x : PolygonEvent q) :
    polygonEventPoint q (polygonEventSuccessor q hG2 x) -
      polygonEventPoint q x ≠ 0 := by
  let e := polygonEventEdge q x
  let u := polygonEventSuccessorTerminalParameter q hG2 hn x
  have h := polygonEventSuccessor_positive_elementary_step q hG2 hn x
  rcases h with ⟨_, _, hpos, _, hstep⟩
  intro hzero
  have hmul : (u - polygonEventParameter q x) • cyclicTangent q e = 0 := by
    rw [← hstep, hzero]
  have hfst := congrArg Prod.fst hmul
  have hsnd := congrArg Prod.snd hmul
  have hfst_mul : (u - polygonEventParameter q x) * (cyclicTangent q e).1 = 0 := by
    simpa [smul_eq_mul] using hfst
  have hsnd_mul : (u - polygonEventParameter q x) * (cyclicTangent q e).2 = 0 := by
    simpa [smul_eq_mul] using hsnd
  have htan_zero : cyclicTangent q e = 0 := by
    apply Prod.ext
    · exact (mul_eq_zero.mp hfst_mul).resolve_left (ne_of_gt hpos)
    · exact (mul_eq_zero.mp hsnd_mul).resolve_left (ne_of_gt hpos)
  exact (cyclicTangent_ne_zero hn q hG1 e) htan_zero

end DirectGLSSW.EventSegmentGeometry
