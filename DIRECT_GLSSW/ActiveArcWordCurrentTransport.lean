import OpenCurrentWordCongruence
import ActiveArcVirtualEventGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW RetainedWords EndpointEventGeometry

/-- An exact finite word equality determines the length and every used point.
No behavior of a total word outside its finite range is required. -/
theorem ofFn_replace_head {m l : ℕ} (f : Fin m → PlanarPoint ℝ)
    (g : Fin l → PlanarPoint ℝ) (p : PlanarPoint ℝ) (hm : 0<m)
    (hw : List.ofFn g = p :: (List.ofFn f).tail) :
    l=m ∧ ∀ (i : ℕ) (hi : i<l) (hj : i<m),
      g ⟨i,hi⟩ = if i=0 then p else f ⟨i,hj⟩ := by
  have hlen := congrArg List.length hw
  simp only [List.length_ofFn,List.length_cons,List.length_tail] at hlen
  have hlm : l=m := by omega
  clear hlen
  subst l
  refine ⟨rfl,?_⟩
  cases m with
  | zero => omega
  | succ k =>
    rw [List.ofFn_succ,List.ofFn_succ,List.tail_cons] at hw
    have hh := List.cons.inj hw
    have ht := List.ofFn_injective hh.2
    intro i hi hj
    cases i with
    | zero => simpa using hh.1
    | succ j =>
      have he := congrFun ht (⟨j,by omega⟩ : Fin k)
      simpa using he

/-- Convert a proved physical point-word transport into the actual open
current on the explicit endpoint curve. The word equality is consumed,
and the change of finite index length is proved internally. -/
theorem openCurrent_eq_event_of_word
    {n m : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (U : Support q hR) (c : Crossing q)
    (r : Fin (m+2) → PlanarPoint ℝ) (hM : Regular r) (V : Support r hM)
    (v : PlanarPoint ℝ) (ε : ℝ)
    (hw : List.ofFn (OpenVertex r hM V) =
      (crossingPoint q c + ε • v) :: (List.ofFn (OpenVertex q hR U)).tail) :
    openCurrent r hM V =
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) v ε))
        0 (openCount q hR U.val-1) := by
  have hpoints := ofFn_replace_head (OpenVertex q hR U) (OpenVertex r hM V)
    (crossingPoint q c+ε • v) (by
      change 0<openCount q hR U.val
      have := open_count_ge_two q hR U.val
      omega) hw
  have hcount : openCount r hM V.val = openCount q hR U.val := hpoints.1
  rw [openCurrent_eq_entry_of_word_eq r hM V
    (moveEndpoint (eventOpenWord q hR U c) v ε) ?_]
  · rw [hcount]
  · intro i hi
    have hj : i<openCount q hR U.val := by rw [← hcount]; exact hi
    rw [hpoints.2 i hi hj]
    by_cases hz : i=0
    · subst i
      simp [moveEndpoint,eventOpenWord]
    · simp only [moveEndpoint,if_neg hz]
      exact eventOpenWord_pos q hR U c i (by omega) hj



end DirectGLSSW.ActiveArc.Primitive
