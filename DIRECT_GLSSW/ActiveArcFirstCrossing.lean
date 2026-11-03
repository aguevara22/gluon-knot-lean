import ActiveArcCursorCrossings
import Mathlib.Data.Finset.Max

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Literal first physical crossing encountered along the first oriented edge. -/
def FirstCrossing (c : Crossing q) : Prop :=
  c.val.1=0 ∧ ∀ d : Crossing q, d.val.1=0 → leftParameter q c≤leftParameter q d

theorem firstParameter_injective (hR : Regular q) (c d : Crossing q)
    (hc : c.val.1=0) (hd : d.val.1=0) (h : leftParameter q c=leftParameter q d) : c=d := by
  apply crossingPoint_injective q hR.noTriple
  rw [(leftParameter_spec q c).2.2,(leftParameter_spec q d).2.2,hc,hd,h]

theorem exists_firstCrossing (hex : ∃ c : Crossing q, c.val.1=0) :
    ∃ c : Crossing q, FirstCrossing q c := by
  have hne : (criticalParameters q).Nonempty := by
    obtain ⟨c,hc⟩ := hex
    exact ⟨leftParameter q c,(mem_criticalParameters q _).mpr ⟨c,hc,rfl⟩⟩
  obtain ⟨c,hc,hp⟩ := (mem_criticalParameters q _).mp (Finset.min'_mem (criticalParameters q) hne)
  refine ⟨c,hc,?_⟩
  intro d hd
  rw [hp]
  exact Finset.min'_le _ _ ((mem_criticalParameters q _).mpr ⟨d,hd,rfl⟩)

/-- The next actual event parameter, or the physical first-edge endpoint 1.
This is a finite minimum of genuine parameters with a real endpoint bound. -/
def afterBound (c : Crossing q) : ℝ :=
  (insert 1 ((criticalParameters q).filter (fun t => leftParameter q c<t))).min'
    (Finset.insert_nonempty _ _)

theorem parameter_lt_afterBound (c : Crossing q) : leftParameter q c<afterBound q c := by
  unfold afterBound
  apply (Finset.lt_min'_iff _ _).mpr
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact (leftParameter_spec q c).2.1
  · exact (Finset.mem_filter.mp ht).2

theorem afterBound_le_one (c : Crossing q) : afterBound q c≤1 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem afterBound_le_parameter (c d : Crossing q) (hd : d.val.1=0)
    (hcd : leftParameter q c<leftParameter q d) : afterBound q c≤leftParameter q d :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
    ⟨(mem_criticalParameters q _).mpr ⟨d,hd,rfl⟩,hcd⟩))

theorem first_parameter_strict (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (d : Crossing q) (hd : d.val.1=0) (hne : d≠c) : leftParameter q c<leftParameter q d := by
  apply lt_of_le_of_ne (hc.2 d hd)
  intro hh
  exact hne (firstParameter_injective q hR c d hc.1 hd hh).symm

theorem survives_before_first (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (ht : t<leftParameter q c) (d : Crossing q) : Survives q t d := by
  intro hd;exact lt_of_lt_of_le ht (hc.2 d hd)

theorem survives_after_first_iff (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (htc : leftParameter q c<t) (htb : t<afterBound q c) (d : Crossing q) :
    Survives q t d ↔ d≠c := by
  constructor
  · intro hd he;subst d
    exact lt_asymm htc (hd hc.1)
  · intro hd hdf
    exact lt_of_lt_of_le htb (afterBound_le_parameter q c d hdf
      (first_parameter_strict q hR c hc d hdf hd))

/-- The window contains exactly the designated physical crossing time. -/
theorem critical_before_after_iff (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (htb : t<afterBound q c) :
    t∈criticalParameters q ↔ t=leftParameter q c := by
  constructor
  · intro ht
    obtain ⟨d,hd,hp⟩ := (mem_criticalParameters q t).mp ht
    by_cases hdc : d=c
    · subst d;exact hp.symm
    · have hh := afterBound_le_parameter q c d hd (first_parameter_strict q hR c hc d hd hdc)
      rw [hp] at hh;exact False.elim (not_lt_of_ge hh htb)
  · intro ht;exact (mem_criticalParameters q t).mpr ⟨c,hc.1,ht.symm⟩

/-- The two open regular chambers are derived, not supplied as fields. -/
theorem regular_first_window_iff (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (ht0 : 0≤t) (htb : t<afterBound q c) :
    Regular (moveStart q t) ↔ t≠leftParameter q c := by
  rw [regular_moveStart_iff q hR t ht0 (lt_of_lt_of_le htb (afterBound_le_one q c)),
    critical_before_after_iff q hR c hc t htb]

/-- Before the first event every original physical crossing label is present. -/
def crossingEquiv_before_first (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (ht0 : 0≤t) (htc : t<leftParameter q c) :
    Crossing (moveStart q t) ≃ Crossing q :=
  (crossingEquiv q hR t ht0 (lt_trans htc (leftParameter_spec q c).2.1)).trans
    (Equiv.subtypeUnivEquiv (survives_before_first q c hc t htc))

/-- After the event precisely the first crossing label is removed. -/
def crossingEquiv_after_first (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (htc : leftParameter q c<t) (htb : t<afterBound q c) :
    Crossing (moveStart q t) ≃ {d : Crossing q // d≠c} :=
  (crossingEquiv q hR t (le_of_lt (lt_trans (leftParameter_spec q c).1 htc))
    (lt_of_lt_of_le htb (afterBound_le_one q c))).trans
    (Equiv.subtypeEquivRight (survives_after_first_iff q hR c hc t htc htb))

/-- Both regular sides have actual parameter values on the original first edge. -/
theorem exists_regular_sides (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c) :
    ∃ a b : ℝ, 0≤a ∧ a<leftParameter q c ∧ leftParameter q c<b ∧ b<afterBound q c ∧
      Regular (moveStart q a) ∧ Regular (moveStart q b) := by
  have hp := (leftParameter_spec q c).1
  have hb := parameter_lt_afterBound q c
  let a := leftParameter q c/2
  let b := (leftParameter q c+afterBound q c)/2
  have ha0 : 0≤a := by dsimp [a];linarith
  have hac : a<leftParameter q c := by dsimp [a];linarith
  have hcb : leftParameter q c<b := by dsimp [b];linarith
  have hbb : b<afterBound q c := by dsimp [b];linarith
  refine ⟨a,b,ha0,hac,hcb,hbb,?_,?_⟩
  · exact (regular_first_window_iff q hR c hc a ha0 (lt_trans hac hb)).mpr (ne_of_lt hac)
  · exact (regular_first_window_iff q hR c hc b (by linarith) hbb).mpr (ne_of_gt hcb)

end DirectGLSSW.ActiveArc.Cursor
