import ActiveArcBeforeFirstOrbits

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.BeforeFirst
open DirectGLSSW ActiveArc PermutationOrbits SingletonWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0 ≤ t) (htc : t < leftParameter q c)
variable (S : Finset (Crossing (moveStart q t)))

/-- At matching actual roots, a closed retained point word is unchanged. -/
theorem closed_root_word (root : Event (moveStart q t))
    (hclosed : componentOf (incoming (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) root ≠
      openComponent (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) :
    List.ofFn (RetainedWords.vertex q hR (selectionEquiv q hR c hc t ht0 htc S)
      (eventEquiv q hR c hc t ht0 htc root)) =
    List.ofFn (RetainedWords.vertex (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) S root) := by
  rw [retainedWord_eq_filtered (a:=n) (b:=0),retainedWord_eq_filtered (a:=n) (b:=0),eventEquiv_orbitWord,
    ← DaughterPointListFilter.map_filter_comp]
  simp only [eventEquiv_retained,List.map_map]
  apply List.map_congr_left
  intro x hx
  apply (eventEquiv_point q hR c hc t ht0 htc x _).symm
  intro he
  have hh := (mem_orbitWord_iff _ _ _).mp (List.mem_filter.mp hx).1
  apply hclosed
  apply (componentOf_eq_iff _ _ _).mpr
  simpa only [he] using hh

/-- Exactly the first endpoint moves in the literal retained open point list. -/
theorem open_word :
    List.ofFn (RetainedWords.vertex (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) S (start (moveStart q t))) =
      affinePoint (q 0) (q 1) t ::
        (List.ofFn (RetainedWords.vertex q hR (selectionEquiv q hR c hc t ht0 htc S) (start q))).tail := by
  let p := moveStart q t
  let hp := before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc
  let F := (orbitWord (incoming p hp.noTriple S) (start p)).filter (fun x => decide (retained p S x))
  have hh : F.head? = some (start p) := filtered_head (a:=n) (b:=0) p hp S (start p) (endpoints_retained p S).1
  obtain ⟨xs,hF⟩ : ∃ xs, F = start p :: xs := by
    cases he : F with
    | nil => simp [he] at hh
    | cons x xs =>
      have hx : x = start p := by simpa only [he,List.head?_cons,Option.some.injEq] using hh
      exact ⟨xs,by rw [hx]⟩
  have hnd : F.Nodup := (orbitWord_nodup _ _).filter _
  have hn : start p ∉ xs := by rw [hF] at hnd; exact (List.nodup_cons.mp hnd).1
  have hpoints : xs.map (eventPoint p) = xs.map (fun x => eventPoint q (eventEquiv q hR c hc t ht0 htc x)) := by
    apply List.map_congr_left
    intro x hx
    exact eventEquiv_point q hR c hc t ht0 htc x (fun h => hn (h ▸ hx))
  have hw : List.ofFn (RetainedWords.vertex q hR (selectionEquiv q hR c hc t ht0 htc S) (start q)) =
      F.map (fun x => eventPoint q (eventEquiv q hR c hc t ht0 htc x)) := by
    have h := eventEquiv_orbitWord q hR c hc t ht0 htc S (start p)
    have hstart : eventEquiv q hR c hc t ht0 htc (start p) = start q := rfl
    rw [hstart] at h
    rw [retainedWord_eq_filtered (a:=n) (b:=0),h,← DaughterPointListFilter.map_filter_comp]
    simp only [eventEquiv_retained,List.map_map]
    rfl
  rw [hw,retainedWord_eq_filtered (a:=n) (b:=0)]
  change F.map (eventPoint p) = _
  rw [hF,List.map_cons,List.map_cons,List.tail_cons]
  rw [hpoints]
  rfl

end DirectGLSSW.ActiveArc.Cursor.BeforeFirst
