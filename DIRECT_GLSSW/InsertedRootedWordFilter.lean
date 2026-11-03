import DirectGLSSW.PermutationInsertionWords
import DirectGLSSW.DaughterRootRotation

set_option autoImplicit false
namespace DirectGLSSW.PermutationInsertion
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A nodup cyclic word has only one rotation with a prescribed first letter. -/
theorem nodup_rotated_eq_of_head {α : Type*} {l m : List α}
    (hl : l.Nodup) (hr : l ~r m) (hh : l.head? = m.head?) : l = m := by
  obtain ⟨n, rfl⟩ := hr
  by_cases hn : l = []
  · simp [hn]
  have hp : 0 < l.length := List.length_pos_of_ne_nil hn
  have hm : n % l.length < l.length := Nat.mod_lt _ hp
  have hh' : l[0] = l[n % l.length] := by
    apply Option.some.inj
    calc
      some l[0] = l.head? := by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hp]
      _ = (l.rotate n).head? := hh
      _ = (l.rotate (n % l.length)).head? := by rw [List.rotate_mod]
      _ = some l[n % l.length] := by rw [List.head?_rotate hm, List.getElem?_eq_getElem hm]
  have he : 0 = n % l.length := hl.getElem_inj_iff.mp hh'
  rw [← List.rotate_mod l n, ← he, List.rotate_zero]

theorem orbitWord_head {α : Type*} [Fintype α] (p : Perm α) (root : α) :
    (orbitWord p root).head? = some root := by
  have hp : 0 < Fintype.card (Fibre p (componentOf p root)) := Fintype.card_pos
  rw [List.head?_eq_getElem?]
  simp [orbitWord, hp, orbitEnumeration_apply_val]

theorem filter_head_of_kept {α : Type*} (p : α → Bool) (l : List α) (x : α)
    (hx : l.head? = some x) (hp : p x = true) : (l.filter p).head? = some x := by
  cases l with
  | nil => simp at hx
  | cons y ys =>
    have hy : y = x := Option.some.inj hx
    subst y
    simp [hp]

theorem filter_lift_word {α β : Type*} (b : β) (E : α ≃ {y : β // y ≠ b}) (l : List α) :
    (l.map (fun x => (E x).val)).filter (fun y => decide (y ≠ b)) =
      l.map (fun x => (E x).val) := by
  apply List.filter_eq_self.mpr
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [decide_eq_true_eq] using (E x).property

/-- Exact rooted deletion. In particular the deleted root is replaced by its
prescribed successor, rather than an independently chosen surviving root. -/
theorem inserted_orbitWord_filter {α β : Type*} [Fintype α] [Fintype β]
    (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val)
    (root : β) :
    (orbitWord q root).filter (fun y => decide (y ≠ b)) =
      (orbitWord p (dropPoint a b E root)).map (fun x => (E x).val) := by
  by_cases hr : root = b
  · subst root
    rw [inserted_orbitWord p q a b E hb hstep, dropPoint_extra]
    simpa using filter_lift_word b E (orbitWord p a)
  · let x := E.symm ⟨root, hr⟩
    have hx : (E x).val = root := congrArg Subtype.val (E.apply_symm_apply ⟨root, hr⟩)
    have hdrop : dropPoint a b E root = x := by simp only [dropPoint, dif_neg hr]; rfl
    rw [hdrop]
    by_cases hc : p.SameCycle a x
    · have hq : q.SameCycle b root := by
        rw [← hx]
        exact (extra_sameCycle_iff p q a b E hb hstep x).mpr hc
      have hrot := DaughterRootRotation.listIsRotated_filter
        (DaughterRootRotation.orbitWord_isRotated_of_sameCycle q root b hq.symm)
        (fun y => decide (y ≠ b))
      have hbase : (orbitWord q b).filter (fun y => decide (y ≠ b)) =
          (orbitWord p a).map (fun z => (E z).val) := by
        rw [inserted_orbitWord p q a b E hb hstep]
        simpa using filter_lift_word b E (orbitWord p a)
      rw [hbase] at hrot
      have hrot' := (DaughterRootRotation.orbitWord_isRotated_of_sameCycle p a x hc).map
        (fun z => (E z).val)
      apply nodup_rotated_eq_of_head ((orbitWord_nodup q root).filter _)
        (hrot.trans hrot')
      have hleft := filter_head_of_kept (fun y => decide (y ≠ b)) (orbitWord q root) root
        (orbitWord_head q root) (by simp [hr])
      rw [hleft]
      rw [List.head?_map, orbitWord_head]
      change some root = some (E x).val
      exact congrArg some hx.symm
    · have hn : ¬ p.SameCycle x a := fun h => hc h.symm
      rw [← hx, unaffected_orbitWord p q a b E hb hstep x hn]
      exact filter_lift_word b E (orbitWord p x)

end
end DirectGLSSW.PermutationInsertion



