namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Source thm:A-S7 for the actual two halves and prescribed physical root map.
The sign is the chirotope on the named minus side. Both side parameters are
arbitrary and independent; no local-radius or neighbor-side restriction remains. -/
theorem vertex_edge_tree_law (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) (g : ZMod n) (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn -
      treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn =
      (w.contactSign M a : ℤ) *
        (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
          (contactHalfRoots M a g).1 (contactHalfSizes_bounds hn hc.1).1.1 *
        treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
          (contactHalfRoots M a g).2 (contactHalfSizes_bounds hn hc.1).2.1) := by
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ := w.contact_signed_response_all_roots g M a hn hc
  let q : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have hMinus : (w.sideTime false q).val < 0 := by
    change -(δ / 2) < 0
    linarith
  have hPlus : 0 < (w.sideTime true q).val := by
    change 0 < δ / 2
    linarith
  have hMinusNear : |(w.sideTime false q).val| < δ := by
    change |-(δ / 2)| < δ
    rw [abs_neg, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hPlusNear : |(w.sideTime true q).val| < δ := by
    change |δ / 2| < δ
    rw [abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hr := hresponse (w.sideTime false q) (w.sideTime true q) hMinus hPlus hMinusNear hPlusNear
  have hsign : -(chi (w.sideTuple true q).val a (a + 1) M : ℤ) +
      (chi (w.sideTuple false q).val a (a + 1) M : ℤ) = 2 * d := hr.1
  have hsigns := w.vertex_contact_signs hc q q
  rw [hsigns.2.1, hsigns.2.2, SignType.coe_neg] at hsign
  have hdcontact : d = (w.contactSign M a : ℤ) := by omega
  have hcoeff :
      treeCoefficient (w.sideTuple true q).val (w.sideTuple true q).property.1 g hn -
        treeCoefficient (w.sideTuple false q).val (w.sideTuple false q).property.1 g hn =
        d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
          (contactHalfRoots M a g).1 (contactHalfSizes_bounds hn hc.1).1.1 *
        treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
          (contactHalfRoots M a g).2 (contactHalfSizes_bounds hn hc.1).2.1) := hr.2
  have hplusCoeff := treeCoefficient_eq_of_chi (w.sideTuple true q).property.1
    (w.sideTuple true t).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple true) q t i j k) g hn
  have hminusCoeff := treeCoefficient_eq_of_chi (w.sideTuple false q).property.1
    (w.sideTuple false s).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple false) q s i j k) g hn
  rw [hplusCoeff, hminusCoeff, hdcontact] at hcoeff
  exact hcoeff

end
end SM.WallGerm
