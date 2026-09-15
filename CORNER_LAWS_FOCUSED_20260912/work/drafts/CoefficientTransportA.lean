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

/-! ## Proof of lp:coefficient-transport (sm-3:993-1039)

The Gaussian rings `TG = ℤ[i][l^±,m^±]`, `RG = ℤ[i][a^±,z^±]`, the inclusions `T.toTG`, `R.toRG`, the
coordinates `TG.re`, `TG.im` (`G = U + iV`) and the mutually inverse transports `phi : TG → RG`
(`l ↦ ia, m ↦ -iz`), `psi : RG → TG` (`a ↦ -il, z ↦ im`) are those of `SM.LinkLaurentRing`. -/

/-- `φ(l) = i·a` with `i` the image of `gaussI` under the structure map `ℤ[i] → R_G` (sm-3:1013). -/
theorem phi_l_eq_algebraMap_mul : phi TG.l = algebraMap GaussianInt RG gaussI * RG.a :=
  phi_l'.trans (Algebra.smul_def gaussI RG.a)

/-- `φ(m) = -i·z` (sm-3:1013). -/
theorem phi_m_eq_algebraMap_mul : phi TG.m = -(algebraMap GaussianInt RG gaussI * RG.z) := by
  rw [phi_m', Algebra.smul_def]

/-- `φ(l⁻¹) = (ia)⁻¹ = -i·a⁻¹` (sm-3:1071). -/
theorem phi_lInv_eq_algebraMap_mul :
    phi TG.lInv = -(algebraMap GaussianInt RG gaussI * RG.aInv) := by
  have h1 : phi TG.lInv = gaussI • ((-gaussI) • phi TG.lInv) := by
    rw [smul_smul, gaussI_mul_neg_gaussI, one_smul]
  rw [h1, neg_gaussI_smul_phi_lInv, smul_neg, Algebra.smul_def]

namespace RCompetitor

variable {Q : Diagram → R}

/-- The transported map `Q̃_D = ψ(Q_D) ∈ T_G` of the printed proof (sm-3:1025-1026), `Q_D` regarded
as `R_G`-valued through the inclusion `R.toRG`. -/
noncomputable def transported (Q : Diagram → R) (D : Diagram) : TG := psi (R.toRG (Q D))

/-- `Q̃` inherits every invariance of `Q` (sm-3:1026-1027). -/
theorem transported_congr (D D' : Diagram) (h : Q D = Q D') : transported Q D = transported Q D' := by
  unfold transported; rw [h]

/-- `Q̃_○ = 1` (sm-3:1027). -/
theorem transported_circle (hQ : RCompetitor Q) (D : Diagram) (h : D.IsCrossingFreeCircle) :
    transported Q D = 1 := by
  unfold transported; rw [hQ.circle D h, map_one, map_one]

/-- The transported skein `l Q̃₊ + l⁻¹ Q̃₋ + m Q̃₀ = 0` (sm-3:1027-1035): apply `ψ` to
`a Q₊ − a⁻¹ Q₋ − z Q₀ = 0` and multiply by the unit `i`. Here checked after applying the inverse `φ`,
where the identity reads `i(a Q₊ − a⁻¹ Q₋ − z Q₀) = 0` in `R_G`. -/
theorem transported_skein (hQ : RCompetitor Q) (Dp Dm D0 : Diagram) (h : IsSkeinTriple Dp Dm D0) :
    TG.l * transported Q Dp + TG.lInv * transported Q Dm + TG.m * transported Q D0 = 0 := by
  refine phi_injective ?_
  simp only [transported, map_add, map_mul, map_zero, phi_psi_apply]
  have hR := congrArg R.toRG (hQ.skein Dp Dm D0 h)
  simp only [map_sub, map_mul, R.toRG_a, R.toRG_aInv, R.toRG_z] at hR
  rw [phi_l_eq_algebraMap_mul, phi_lInv_eq_algebraMap_mul, phi_m_eq_algebraMap_mul]
  linear_combination (algebraMap GaussianInt RG gaussI) * hR

/-- The real coordinate `U = re Q̃` is a competitor of lp:lm-uniqueness (sm-3:1002-1009). -/
theorem re_competitor (hQ : RCompetitor Q) : LMCompetitor (fun D => TG.re (transported Q D)) where
  planar D D' h := congrArg TG.re (transported_congr D D' (hQ.planar D D' h))
  reidemeister_I D D' h := congrArg TG.re (transported_congr D D' (hQ.reidemeister_I D D' h))
  reidemeister_II D D' h := congrArg TG.re (transported_congr D D' (hQ.reidemeister_II D D' h))
  reidemeister_III D D' h := congrArg TG.re (transported_congr D D' (hQ.reidemeister_III D D' h))
  unknot D h := by
    show TG.re (transported Q D) = 1
    rw [hQ.transported_circle D h, TG.re_one]
  sourceSkein Dp Dm D0 h := TG.re_skein (hQ.transported_skein Dp Dm D0 h)

/-- `F + V` (with `V = im Q̃`) is a competitor of lp:lm-uniqueness: "The skein is linear, so `U` and
`F + V` are both invariant `T`-valued maps satisfying the source skein with unknot value 1"
(sm-3:1007-1009). -/
theorem lmF_add_im_competitor (hQ : RCompetitor Q) :
    LMCompetitor (fun D => lmF D + TG.im (transported Q D)) where
  planar D D' h :=
    congrArg₂ (· + ·) (lmF_planar h) (congrArg TG.im (transported_congr D D' (hQ.planar D D' h)))
  reidemeister_I D D' h :=
    congrArg₂ (· + ·) (lmF_reidemeister_I h)
      (congrArg TG.im (transported_congr D D' (hQ.reidemeister_I D D' h)))
  reidemeister_II D D' h :=
    congrArg₂ (· + ·) (lmF_reidemeister_II h)
      (congrArg TG.im (transported_congr D D' (hQ.reidemeister_II D D' h)))
  reidemeister_III D D' h :=
    congrArg₂ (· + ·) (lmF_reidemeister_III h)
      (congrArg TG.im (transported_congr D D' (hQ.reidemeister_III D D' h)))
  unknot D h := by
    show lmF D + TG.im (transported Q D) = 1
    rw [lmF_unknot h, hQ.transported_circle D h, TG.im_one, add_zero]
  sourceSkein Dp Dm D0 h := by
    have h1 := lmF_sourceSkein h
    have h2 := TG.im_skein (hQ.transported_skein Dp Dm D0 h)
    show T.l * (lmF Dp + TG.im (transported Q Dp)) + T.lInv * (lmF Dm + TG.im (transported Q Dm)) +
      T.m * (lmF D0 + TG.im (transported Q D0)) = 0
    linear_combination h1 + h2

/-- lp:lm-uniqueness gives `U = F` (sm-3:1009-1010). -/
theorem re_transported (hQ : RCompetitor Q) (D : Diagram) : TG.re (transported Q D) = lmF D :=
  congrFun (lp_lm_uniqueness _ hQ.re_competitor) D

/-- lp:lm-uniqueness gives `F + V = F`, hence `V = 0` (sm-3:1009-1010). -/
theorem im_transported (hQ : RCompetitor Q) (D : Diagram) : TG.im (transported Q D) = 0 := by
  have h : lmF D + TG.im (transported Q D) = lmF D :=
    congrFun (lp_lm_uniqueness _ hQ.lmF_add_im_competitor) D
  linear_combination h

/-- `G = U + iV = F` (sm-3:1010, "hence `V = 0` and `G = F`"): `Q̃_D = F_D` embedded in `T_G`. -/
theorem transported_eq_toTG_lmF (hQ : RCompetitor Q) (D : Diagram) :
    transported Q D = T.toTG (lmF D) := by
  rw [TG.eq_toTG_re_add_gaussI_smul_toTG_im (transported Q D), hQ.re_transported D,
    hQ.im_transported D, map_zero, smul_zero, add_zero]

/-- "`Q_D = φ(F_D)` for every diagram `D`" (sm-3:1036-1037), in `R_G`. -/
theorem toRG_eq (hQ : RCompetitor Q) (D : Diagram) : R.toRG (Q D) = phi (T.toTG (lmF D)) := by
  rw [← hQ.transported_eq_toTG_lmF D, transported, phi_psi_apply]

end RCompetitor

/-- lp:coefficient-transport as printed: "Any two maps `D ↦ Q_D ∈ R` on oriented link diagrams that are
invariant under planar isotopy and the three Reidemeister moves, take the value 1 on the crossing-free
circle, and satisfy `a Q_{D₊} − a⁻¹ Q_{D₋} = z Q_{D₀}` on every skein triple coincide. No restriction on
the support or on the coefficients of the maps is imposed." -/
theorem coefficient_transport (Q Q' : Diagram → R) (hQ : RCompetitor Q) (hQ' : RCompetitor Q') :
    Q = Q' := by
  funext D
  exact R.toRG_injective ((hQ.toRG_eq D).trans (hQ'.toRG_eq D).symm)

end SM

#print axioms SM.coefficient_transport
