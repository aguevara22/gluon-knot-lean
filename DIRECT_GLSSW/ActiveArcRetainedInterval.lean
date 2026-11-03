import ActiveArcPhysicalWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalSegments
open RetainedWords PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- Every actual event between the paired outgoing endpoint and its next retained
endpoint belongs to the same incoming smoothing component. -/
theorem firstReturn_interval_exists (x : Event q) (hx : x≠terminal q)
    (d : ℕ) (hd : 0<d)
    (hno : ∀ k : ℕ, 0<k → k<d → ¬retained q S ((incoming q hR.noTriple S ^ k) x))
    (v : Event q)
    (hv : (eventOrder q hR.noTriple).lt (pairing q S x) v)
    (hvend : (eventOrder q hR.noTriple).le v ((incoming q hR.noTriple S ^ d) x)) :
    ∃ k : ℕ, 0<k ∧ k≤d ∧ (incoming q hR.noTriple S ^ k) x=v := by
  letI := eventOrder q hR.noTriple
  induction d with
  | zero => omega
  | succ k ih =>
    by_cases hk : k=0
    · subst k
      have hmin := successor_min q hR (pairing q S x) v
        (pairing_ne_terminal q S x hx) hv
      have he : v=incoming q hR.noTriple S x :=
        le_antisymm (by simpa using hvend) hmin
      exact ⟨1,by omega,by omega,by simpa using he.symm⟩
    · have hkp : 0<k := Nat.pos_of_ne_zero hk
      by_cases hle : v≤(incoming q hR.noTriple S ^ k) x
      · obtain ⟨j,hj,hjk,hje⟩ := ih hkp (fun j hj hjk => hno j hj (by omega)) hle
        exact ⟨j,hj,by omega,hje⟩
      · have hlt : (incoming q hR.noTriple S ^ k) x<v := lt_of_not_ge hle
        have hnr := hno k hkp (by omega)
        have hn : (incoming q hR.noTriple S ^ k) x≠terminal q := by
          intro hh;apply hnr;rw [hh];exact (endpoints_retained q S).2
        have hmin := successor_min q hR ((incoming q hR.noTriple S ^ k) x) v hn hlt
        have he : v=(incoming q hR.noTriple S ^ (k+1)) x := by
          apply le_antisymm hvend
          rw [pow_succ',Equiv.Perm.mul_apply]
          change successor q hR.noTriple (pairing q S ((incoming q hR.noTriple S ^ k) x))≤v
          rw [pairing_fixes_nonretained q S _ hnr]
          exact hmin
        exact ⟨k+1,by omega,le_rfl,he.symm⟩

theorem retained_interval_component (root : Event q) (c : Corner q hR S root)
    (hx : eventAt q hR S root c.val≠terminal q) (v : Event q)
    (hv : (eventOrder q hR.noTriple).lt (pairing q S (eventAt q hR S root c.val)) v)
    (hvend : (eventOrder q hR.noTriple).le v
      (eventAt q hR S root (nextCorner q hR S root c).val)) :
    componentOf (incoming q hR.noTriple S) v=componentOf (incoming q hR.noTriple S) root := by
  have hf := corner_firstReturn q hR S root c
  obtain ⟨k,hk,hkd,hkv⟩ := firstReturn_interval_exists q hR S _ hx (cornerGap q hR S root c)
    hf.1 hf.2.2 v hv (by rw [hf.2.1];exact hvend)
  have hs : (incoming q hR.noTriple S).SameCycle (eventAt q hR S root c.val) v :=
    ⟨(k : ℤ),by rw [zpow_natCast];exact hkv⟩
  have he := (componentOf_eq_iff _ _ _).mpr hs
  exact he.symm.trans (orbitEnumeration (incoming q hR.noTriple S) root c.val).property

end DirectGLSSW.ActiveArc.PhysicalSegments
