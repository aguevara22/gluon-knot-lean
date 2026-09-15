import SM.LinkInterfaces

/-! Source lp:coefficient-transport (reference/SM/sm-3-statesum.tex:981-992, frame SM15): Gaussian coefficient
transport of skein uniqueness. Main declaration: `SM.coefficient_transport`.

Notation (Chapter-3 layer, namespace `SM.Link`): `R = ℤ[a^{±1}, z^{±1}]` is `R` (`R.a`, `R.aInv`, `R.z`);
"oriented link diagrams" are `Diagram` (the document's polygonal class, def:positive-lift); "invariant under
planar isotopy and the three Reidemeister moves" is invariance under `PlanarIsotopic`, `RI`, `RII`, `RIII`;
"the crossing-free circle" is every one-component crossing-free diagram (`Diagram.IsCrossingFreeCircle`);
"every skein triple" is `IsSkeinTriple Dp Dm D0`. The hypotheses on a map are bundled in the Prop structure
`RCompetitor` (one field per printed clause); "no restriction on the support or on the coefficients of the maps
is imposed" is the absence of any further hypothesis on `Q`. -/

namespace SM

open SM.Link

/-- The hypotheses of lp:coefficient-transport on a map `D ↦ Q_D ∈ R`: "invariant under planar isotopy and
the three Reidemeister moves, take the value 1 on the crossing-free circle, and satisfy
`a Q_{D₊} − a⁻¹ Q_{D₋} = z Q_{D₀}` on every skein triple". -/
structure RCompetitor (Q : Diagram → R) : Prop where
  /-- "invariant under planar isotopy" -/
  planar : ∀ D D' : Diagram, PlanarIsotopic D D' → Q D = Q D'
  /-- "and the three Reidemeister moves" -/
  reidemeister_I : ∀ D D' : Diagram, RI D D' → Q D = Q D'
  reidemeister_II : ∀ D D' : Diagram, RII D D' → Q D = Q D'
  reidemeister_III : ∀ D D' : Diagram, RIII D D' → Q D = Q D'
  /-- "take the value 1 on the crossing-free circle" -/
  circle : ∀ D : Diagram, D.IsCrossingFreeCircle → Q D = 1
  /-- "satisfy `a Q_{D₊} − a⁻¹ Q_{D₋} = z Q_{D₀}` on every skein triple" -/
  skein : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
    R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0

/-! ### The proof of sm-3:993-1039, step by step

The route is the printed one. Embed `R ⊂ R_G` (`R.toRG`), transport by `ψ : R_G → T_G` to
`G_D = ψ(Q_D)`, split `G = U + iV` with `U = re G`, `V = im G` (`TG.re`, `TG.im`), show that `U` and
`F + V` are competitors in the sense of lp:lm-uniqueness, conclude `U = F`, `V = 0`, hence
`ψ(Q_D) = F_D` in `T_G` and `Q_D = φ(F_D)` in `R_G`; two competitors agree in `R_G`, hence in `R`
by injectivity of `R ⊂ R_G`. -/

/-- The image of the formal `i` in `T_G` ("both fixing i", sm-3:1018). -/
noncomputable def TG.iota : TG := algebraMap GaussianInt TG gaussI

/-- `i² = -1` in `T_G` (sm-3:994: "Adjoin a formal i with i² = -1"). -/
theorem TG.iota_mul_iota : TG.iota * TG.iota = -1 := by
  rw [TG.iota, ← map_mul, gaussI_mul_gaussI, map_neg, map_one]

/-- `ψ(a) = -i l` (sm-3:1015), written with the unit `i` of `T_G`. -/
theorem psi_a_eq_neg_iota_mul_l : psi RG.a = -(TG.iota * TG.l) := by
  rw [psi_a, TG.iota, TG.algebraMap_apply, TG.l, TG.single_mul_single, zero_add, mul_one]
  exact AddMonoidAlgebra.single_neg (1, 0) gaussI

/-- `ψ(a⁻¹) = (-il)⁻¹ = i l⁻¹` (sm-3:1027-1028). -/
theorem psi_aInv_eq_iota_mul_lInv : psi RG.aInv = TG.iota * TG.lInv := by
  rw [psi_aInv, TG.iota, TG.algebraMap_apply, TG.lInv, TG.single_mul_single, zero_add, mul_one]

/-- `ψ(z) = i m` (sm-3:1015). -/
theorem psi_z_eq_iota_mul_m : psi RG.z = TG.iota * TG.m := by
  rw [psi_z, TG.iota, TG.algebraMap_apply, TG.m, TG.single_mul_single, zero_add, mul_one]

/-- The transported skein (sm-3:1029-1033): applying `ψ` to `a Q₊ − a⁻¹ Q₋ − z Q₀ = 0` gives
`(−il) Q̃₊ − (il⁻¹) Q̃₋ − (im) Q̃₀ = 0`, "and multiplying by the unit i gives
`l Q̃₊ + l⁻¹ Q̃₋ + m Q̃₀ = 0`". -/
theorem RCompetitor.transport_skein {Q : Diagram → R} (hQ : RCompetitor Q) {Dp Dm D0 : Diagram}
    (h : IsSkeinTriple Dp Dm D0) :
    TG.l * psi (R.toRG (Q Dp)) + TG.lInv * psi (R.toRG (Q Dm)) + TG.m * psi (R.toRG (Q D0)) = 0 := by
  have h1 := congrArg (fun x : R => psi (R.toRG x)) (hQ.skein Dp Dm D0 h)
  simp only [map_sub, map_mul, R.toRG_a, R.toRG_aInv, R.toRG_z, psi_a_eq_neg_iota_mul_l,
    psi_aInv_eq_iota_mul_lInv, psi_z_eq_iota_mul_m] at h1
  linear_combination TG.iota * h1 +
    (TG.l * psi (R.toRG (Q Dp)) + TG.lInv * psi (R.toRG (Q Dm)) + TG.m * psi (R.toRG (Q D0))) *
      TG.iota_mul_iota

/-- `U = re ψ(Q)` is a competitor of lp:lm-uniqueness (sm-3:1002-1008: "Both coordinates inherit the
invariance ... the source skein for U ... with U_○ = 1"). -/
theorem RCompetitor.re_competitor {Q : Diagram → R} (hQ : RCompetitor Q) :
    LMCompetitor (fun D => TG.re (psi (R.toRG (Q D)))) where
  planar D D' h := congrArg (fun x : R => TG.re (psi (R.toRG x))) (hQ.planar D D' h)
  reidemeister_I D D' h := congrArg (fun x : R => TG.re (psi (R.toRG x))) (hQ.reidemeister_I D D' h)
  reidemeister_II D D' h := congrArg (fun x : R => TG.re (psi (R.toRG x))) (hQ.reidemeister_II D D' h)
  reidemeister_III D D' h :=
    congrArg (fun x : R => TG.re (psi (R.toRG x))) (hQ.reidemeister_III D D' h)
  unknot D h := by
    show TG.re (psi (R.toRG (Q D))) = 1
    rw [hQ.circle D h, map_one, map_one, TG.re_one]
  sourceSkein Dp Dm D0 h := TG.re_skein (hQ.transport_skein h)

/-- `F + V` with `V = im ψ(Q)` is a competitor of lp:lm-uniqueness (sm-3:1006-1008: "V_○ = 0. The skein
is linear, so U and F + V are both invariant T-valued maps satisfying the source skein with unknot
value 1"). -/
theorem RCompetitor.lmF_add_im_competitor {Q : Diagram → R} (hQ : RCompetitor Q) :
    LMCompetitor (fun D => lmF D + TG.im (psi (R.toRG (Q D)))) where
  planar D D' h := by
    show lmF D + TG.im (psi (R.toRG (Q D))) = lmF D' + TG.im (psi (R.toRG (Q D')))
    rw [lmF_planar h, hQ.planar D D' h]
  reidemeister_I D D' h := by
    show lmF D + TG.im (psi (R.toRG (Q D))) = lmF D' + TG.im (psi (R.toRG (Q D')))
    rw [lmF_reidemeister_I h, hQ.reidemeister_I D D' h]
  reidemeister_II D D' h := by
    show lmF D + TG.im (psi (R.toRG (Q D))) = lmF D' + TG.im (psi (R.toRG (Q D')))
    rw [lmF_reidemeister_II h, hQ.reidemeister_II D D' h]
  reidemeister_III D D' h := by
    show lmF D + TG.im (psi (R.toRG (Q D))) = lmF D' + TG.im (psi (R.toRG (Q D')))
    rw [lmF_reidemeister_III h, hQ.reidemeister_III D D' h]
  unknot D h := by
    show lmF D + TG.im (psi (R.toRG (Q D))) = 1
    rw [lmF_unknot h, hQ.circle D h, map_one, map_one, TG.im_one, add_zero]
  sourceSkein Dp Dm D0 h := by
    show T.l * (lmF Dp + TG.im (psi (R.toRG (Q Dp)))) + T.lInv * (lmF Dm + TG.im (psi (R.toRG (Q Dm))))
      + T.m * (lmF D0 + TG.im (psi (R.toRG (Q D0)))) = 0
    linear_combination lmF_sourceSkein h + TG.im_skein (hQ.transport_skein h)

/-- "By the first step, `Q̃ = F`" (sm-3:1034): `ψ(Q_D) = F_D` in `T_G`, via `U = F` and `F + V = F`
(sm-3:1008-1010: "gives U = F and F + V = F, hence V = 0 and G = F"). -/
theorem RCompetitor.psi_toRG_eq_toTG_lmF {Q : Diagram → R} (hQ : RCompetitor Q) (D : Diagram) :
    psi (R.toRG (Q D)) = T.toTG (lmF D) := by
  have hU : TG.re (psi (R.toRG (Q D))) = lmF D := lmF_unique hQ.re_competitor D
  have hFV : lmF D + TG.im (psi (R.toRG (Q D))) = lmF D := lmF_unique hQ.lmF_add_im_competitor D
  have hV : TG.im (psi (R.toRG (Q D))) = 0 := add_left_cancel (hFV.trans (add_zero (lmF D)).symm)
  calc psi (R.toRG (Q D))
      = T.toTG (TG.re (psi (R.toRG (Q D)))) + gaussI • T.toTG (TG.im (psi (R.toRG (Q D)))) :=
        TG.eq_toTG_re_add_gaussI_smul_toTG_im _
    _ = T.toTG (lmF D) := by rw [hU, hV, map_zero, smul_zero, add_zero]

/-- "hence `Q_D = φ(F_D)` for every diagram D" (sm-3:1034-1035), in `R_G`. -/
theorem RCompetitor.toRG_eq_phi_toTG_lmF {Q : Diagram → R} (hQ : RCompetitor Q) (D : Diagram) :
    R.toRG (Q D) = phi (T.toTG (lmF D)) := by
  rw [← hQ.psi_toRG_eq_toTG_lmF D, phi_psi_apply]

/-- lp:coefficient-transport as printed: "Any two maps `D ↦ Q_D ∈ R` on oriented link diagrams that are
invariant under planar isotopy and the three Reidemeister moves, take the value 1 on the crossing-free
circle, and satisfy `a Q_{D₊} − a⁻¹ Q_{D₋} = z Q_{D₀}` on every skein triple coincide. No restriction on
the support or on the coefficients of the maps is imposed." -/
theorem coefficient_transport (Q Q' : Diagram → R) (hQ : RCompetitor Q) (hQ' : RCompetitor Q') :
    Q = Q' := by
  funext D
  exact R.toRG_injective ((hQ.toRG_eq_phi_toTG_lmF D).trans (hQ'.toRG_eq_phi_toTG_lmF D).symm)

end SM

#print axioms SM.coefficient_transport
