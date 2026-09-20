import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Degree
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! Chapter-3 representation layer, module LinkLaurentRing: the two-variable Laurent-polynomial ring layer (R = ℤ[a^{±1}, z^{±1}], the distinct T = ℤ[l^{±1}, m^{±1}], the Gaussian detour RG/TG with φ, ψ, coefficient extraction, def:adeg degrees). Implements the design adopted 2026-09-13
(work/reports/design-decision-diagram-record-20260913.md, Proposal #1 with the judges' grafts). Written 2026-09-13 by a Claude Code
implementer subagent of the pod executor (workflow implement-diagram-layer-phase1), checked with `lake env lean` (placeholder-free,
standard axioms) and ported verbatim from work/drafts/LinkLaurentRing.lean (only this header added and #print lines removed). All
declarations live in `SM.Link`; no row points here yet — the definition rows (def:positive-lift, def:gauss-record, def:adeg, ...)
are stated on top of this layer and reviewed against the source. -/

/-!
# The two-variable Laurent ring layer for SM Chapter 3 (`SM.Link`)

Design record: `work/reports/design-decision-diagram-record-20260913.md`, section `ring_layer`
(Proposal #1, with the judges' graft that def:adeg goes through Mathlib's
`AddMonoidAlgebra.supDegree`/`infDegree`).

Printed sources rendered here (reference/SM/sm-3-statesum.tex, frozen):

* lit:homfly 916-921: "a map `D ↦ H_D(a,z) ∈ ℤ[a^{±1},z^{±1}]` on oriented link diagrams" — the
  ring `R`.
* lp:lm 935-960: "The source constructs it in `ℤ[l^{±1},m^{±1}]`", the source skein
  "`l F_{D_+} + l^{-1} F_{D_-} + m F_{D_0} = 0, μ = -(l+l^{-1})m^{-1}`" — the ring `T` and `T.mu`.
* lp:lm-uniqueness 962-979: "to `T = ℤ[l^{±1},m^{±1}]`", "The ring is the source's: no statement
  over `ℤ[a^{±1},z^{±1}]` is imported here" — why `T` is a type DISTINCT from `R`.
* lp:coefficient-transport 981-1039: "Put `R = ℤ[a^{±1},z^{±1}]`"; its proof 994-1039: "Adjoin a
  formal i with i² = -1 and put `T_G = ℤ[i][l^{±1},m^{±1}]` and `R_G = ℤ[i][a^{±1},z^{±1}]`. Since
  1, i is a free integer basis of ℤ[i], ... the inclusions `T ⊂ T_G`, `R ⊂ R_G` are injective";
  lp:ring-transports 1013-1017: "`φ : T_G → R_G, l ↦ ia, m ↦ -iz`, `ψ : R_G → T_G, a ↦ -il,
  z ↦ im`, both fixing i, send the Laurent generators to units and therefore define ring
  homomorphisms. On generators, `ψ(φ(l)) = i(-il) = l`, `ψ(φ(m)) = -i(im) = m`,
  `φ(ψ(a)) = -i(ia) = a` and `φ(ψ(z)) = i(-iz) = z`, so φ and ψ are mutually inverse
  isomorphisms."
* lp:core 1041-1060: "`aP_{D_+} - a^{-1}P_{D_-} = zP_{D_0}, δ = (a-a^{-1})z^{-1}`" — `R.delta`.
* def:C 1688-1699: "`c(Q) = [a^{d_Q} z^0] H^+_Q(a,z) ∈ ℤ`, the coefficient of `a^{d_Q}z^0` (zero
  if that monomial is absent)" — `coeffAt`.
* mp:lowest 1582-1592: "`[z^{1-c}] P_D = a^{-2Λ}(a-a^{-1})^{c-1} ∏ [z^0] P_{D_i}`" — the `[z^k]`
  rows `zRow` valued in `ℤ[a^{±1}]`.
* def:adeg 1887-1893: "For a nonzero Laurent polynomial f in a with coefficients in the integral
  domain `ℤ[z^{±1}]`, `deg_a f = maxdeg_a f` denotes the largest a-exponent with nonzero
  coefficient and `mindeg_a f` the smallest; both are integers. The same symbols with the
  subscript z denote the largest and smallest z-exponents of a nonzero element of
  `ℤ[a^{±1},z^{±1}]`." — `degA`, `mindegA`, `degZ`, `mindegZ` and their unwrapping lemmas.

Encoding: `Laurent₂ K := AddMonoidAlgebra K (ℤ × ℤ)`; the exponent `(d, k)` is the monomial
`a^d z^k` (in `R`, `RG`) resp. `l^d m^k` (in `T`, `TG`). `AddMonoidAlgebra` is a structure with the
single field `coeff : (ℤ × ℤ) →₀ K`, so every coefficient statement is a `Finsupp` statement.

`T` and `TG` are `def` wrappers (not `abbrev`s) so that `l` can never be silently identified with
`a`. Inside THIS file the wrappers are unfolded (`show`, `inferInstanceAs`) to build their ring
structure, their generators and the bridges `T.toTG`, `phi`, `psi`; consumers (lp:core,
lp:coefficient-transport) must use only those bridges and `R.toRG` (fidelity risk 12 of the record).
-/

namespace SM.Link

open AddMonoidAlgebra

/-! ### The rings `R`, `T`, `RG`, `TG` -/

/-- Two-variable Laurent polynomials over `K`: `AddMonoidAlgebra K (ℤ × ℤ)`; exponent `(d, k)` is
`a^d z^k` (or `l^d m^k`). This is Mathlib's own `LaurentPolynomial` construction
(`AddMonoidAlgebra R ℤ`) with a second exponent. -/
abbrev Laurent₂ (K : Type) [CommRing K] : Type := AddMonoidAlgebra K (ℤ × ℤ)

/-- `R = ℤ[a^{±1}, z^{±1}]`: the coefficient ring of lit:homfly (sm-3:917, "`H_D(a,z) ∈
ℤ[a^{±1},z^{±1}]`"), lp:coefficient-transport (983, "Put `R = ℤ[a^{±1},z^{±1}]`") and lp:core
(1042, "Set `R = ℤ[a^{±1},z^{±1}]`"). -/
abbrev R : Type := Laurent₂ ℤ

/-- `T = ℤ[l^{±1}, m^{±1}]`: the source ring of lp:lm (sm-3:939, "The source constructs it in
`ℤ[l^{±1},m^{±1}]`") and lp:lm-uniqueness (966, "to `T = ℤ[l^{±1},m^{±1}]`"; 976-978, "The ring
is the source's: no statement over `ℤ[a^{±1},z^{±1}]` is imported here"). A `def` with its own name (not
an `abbrev`), distinct from `R` at reducible transparency; NOTE that `T = R` is nevertheless `rfl` at default
transparency, so the separation of the two rings is a POLICY enforced by review — distinct names and
generators, only the documented bridges convert — not a barrier the elaborator provides (AUTHOR_NOTES
2026-09-13, documentation defects (a)). -/
def T : Type := Laurent₂ ℤ

noncomputable instance : CommRing T := inferInstanceAs (CommRing (Laurent₂ ℤ))
noncomputable instance : IsDomain T := inferInstanceAs (IsDomain (Laurent₂ ℤ))

/-- `R_G = ℤ[i][a^{±1}, z^{±1}]` of lp:coefficient-transport's proof (sm-3:995-996) and lp:core's
proof (1064: "Start in `R_G = ℤ[i][a^{±1},z^{±1}]` with i² = -1"). `ℤ[i]` is Mathlib's
`GaussianInt = Zsqrtd (-1)`. -/
abbrev RG : Type := Laurent₂ GaussianInt

/-- `T_G = ℤ[i][l^{±1}, m^{±1}]` of lp:coefficient-transport's proof (sm-3:995). A DISTINCT type
from `RG`, like `T` from `R`. -/
def TG : Type := Laurent₂ GaussianInt

noncomputable instance : CommRing TG := inferInstanceAs (CommRing (Laurent₂ GaussianInt))
noncomputable instance : IsDomain TG := inferInstanceAs (IsDomain (Laurent₂ GaussianInt))
noncomputable instance : Algebra GaussianInt TG :=
  inferInstanceAs (Algebra GaussianInt (Laurent₂ GaussianInt))

/-- def:adeg's "integral domain" (sm-3:1889): `R` is a domain (Mathlib: `ℤ` is a domain and
`ℤ × ℤ` has unique sums). -/
example : IsDomain R := inferInstance
example : IsDomain RG := inferInstance
example : Nontrivial T := inferInstance
example : Nontrivial TG := inferInstance

/-! ### Monomials and monomial units in `Laurent₂ K` -/

namespace Laurent₂

variable {K : Type} [CommRing K]

theorem single_one_mul_single_one (e e' : ℤ × ℤ) :
    (single e 1 : Laurent₂ K) * single e' 1 = single (e + e') 1 := by
  simp [single_mul_single]

theorem single_mul_single_neg (e : ℤ × ℤ) : (single e 1 : Laurent₂ K) * single (-e) 1 = 1 := by
  simp [single_mul_single, one_def]

theorem single_neg_mul_single (e : ℤ × ℤ) : (single (-e) 1 : Laurent₂ K) * single e 1 = 1 := by
  simp [single_mul_single, one_def]

/-- The monomial `x^e` (`e : ℤ × ℤ`) as a unit of `Laurent₂ K`, with inverse `x^{-e}`; this is how
"the Laurent generators" are "units" (lp:ring-transports, sm-3:1018). -/
noncomputable def monoUnit (e : ℤ × ℤ) : (Laurent₂ K)ˣ :=
  ⟨single e 1, single (-e) 1, single_mul_single_neg e, single_neg_mul_single e⟩

@[simp] theorem val_monoUnit (e : ℤ × ℤ) : ((monoUnit e : (Laurent₂ K)ˣ) : Laurent₂ K) = single e 1 :=
  rfl

@[simp] theorem val_monoUnit_inv (e : ℤ × ℤ) :
    (((monoUnit e)⁻¹ : (Laurent₂ K)ˣ) : Laurent₂ K) = single (-e) 1 :=
  rfl

theorem monoUnit_inv (e : ℤ × ℤ) : ((monoUnit e)⁻¹ : (Laurent₂ K)ˣ) = monoUnit (-e) :=
  Units.ext rfl

theorem monoUnit_mul (e e' : ℤ × ℤ) :
    (monoUnit e : (Laurent₂ K)ˣ) * monoUnit e' = monoUnit (e + e') :=
  Units.ext (by simp [single_mul_single])

theorem monoUnit_zero : (monoUnit 0 : (Laurent₂ K)ˣ) = 1 :=
  Units.ext (by simp [one_def])

/-- `(x^e)^d = x^{d e}` for integer `d`. -/
theorem monoUnit_zpow (e : ℤ × ℤ) (d : ℤ) :
    (monoUnit e : (Laurent₂ K)ˣ) ^ d = monoUnit (d • e) := by
  induction d using Int.induction_on with
  | zero => rw [zpow_zero, zero_smul, monoUnit_zero]
  | succ n ih => rw [zpow_add_one, ih, monoUnit_mul, add_smul, one_smul]
  | pred n ih => rw [zpow_sub_one, ih, monoUnit_inv, monoUnit_mul, sub_smul, one_smul, sub_eq_add_neg]

end Laurent₂

/-! ### Generators of `R` and `T`, unit laws, `δ` and `μ` -/

/-- `a ∈ R`: the monomial `a^1 z^0`. -/
noncomputable def R.a : R := single (1, 0) 1
/-- `z ∈ R`: the monomial `a^0 z^1`. -/
noncomputable def R.z : R := single (0, 1) 1
/-- `a^{-1} ∈ R`. -/
noncomputable def R.aInv : R := single (-1, 0) 1
/-- `z^{-1} ∈ R`. -/
noncomputable def R.zInv : R := single (0, -1) 1

/-- `a` as a unit of `R` (value `R.a`, inverse `R.aInv`). -/
noncomputable def R.aUnit : Rˣ := Laurent₂.monoUnit (1, 0)
/-- `z` as a unit of `R` (value `R.z`, inverse `R.zInv`). -/
noncomputable def R.zUnit : Rˣ := Laurent₂.monoUnit (0, 1)

@[simp] theorem R.val_aUnit : (R.aUnit : R) = R.a := rfl
@[simp] theorem R.val_aUnit_inv : ((R.aUnit⁻¹ : Rˣ) : R) = R.aInv := rfl
@[simp] theorem R.val_zUnit : (R.zUnit : R) = R.z := rfl
@[simp] theorem R.val_zUnit_inv : ((R.zUnit⁻¹ : Rˣ) : R) = R.zInv := rfl

theorem R.a_mul_aInv : R.a * R.aInv = 1 := R.aUnit.mul_inv
theorem R.aInv_mul_a : R.aInv * R.a = 1 := R.aUnit.inv_mul
theorem R.z_mul_zInv : R.z * R.zInv = 1 := R.zUnit.mul_inv
theorem R.zInv_mul_z : R.zInv * R.z = 1 := R.zUnit.inv_mul

theorem R.a_ne_zero : R.a ≠ 0 := R.aUnit.ne_zero
theorem R.z_ne_zero : R.z ≠ 0 := R.zUnit.ne_zero

/-- Sanity: the monomial `a^d z^k` is `a^d · z^k` computed with the units. -/
theorem R.single_eq_aUnit_zpow_mul_zUnit_zpow (d k : ℤ) :
    (single (d, k) 1 : R) = ((R.aUnit ^ d * R.zUnit ^ k : Rˣ) : R) := by
  rw [R.aUnit, R.zUnit, Laurent₂.monoUnit_zpow, Laurent₂.monoUnit_zpow, Laurent₂.monoUnit_mul,
    Laurent₂.val_monoUnit]
  simp

/-- `δ = (a - a^{-1}) z^{-1}` of lp:core (sm-3:1046, "`δ = (a-a^{-1})z^{-1}`"). -/
noncomputable def R.delta : R := (R.a - R.aInv) * R.zInv

theorem R.delta_mul_z : R.delta * R.z = R.a - R.aInv := by
  rw [R.delta, mul_assoc, R.zInv_mul_z, mul_one]

/-- `l ∈ T`: the monomial `l^1 m^0` (lp:lm, sm-3:939 "`ℤ[l^{±1},m^{±1}]`"). -/
noncomputable def T.l : T := (single (1, 0) 1 : Laurent₂ ℤ)
/-- `m ∈ T`: the monomial `l^0 m^1`. -/
noncomputable def T.m : T := (single (0, 1) 1 : Laurent₂ ℤ)
/-- `l^{-1} ∈ T`. -/
noncomputable def T.lInv : T := (single (-1, 0) 1 : Laurent₂ ℤ)
/-- `m^{-1} ∈ T`. -/
noncomputable def T.mInv : T := (single (0, -1) 1 : Laurent₂ ℤ)

/-- `l` as a unit of `T`. -/
noncomputable def T.lUnit : Tˣ := (Laurent₂.monoUnit (1, 0) : (Laurent₂ ℤ)ˣ)
/-- `m` as a unit of `T`. -/
noncomputable def T.mUnit : Tˣ := (Laurent₂.monoUnit (0, 1) : (Laurent₂ ℤ)ˣ)

@[simp] theorem T.val_lUnit : (T.lUnit : T) = T.l := rfl
@[simp] theorem T.val_lUnit_inv : ((T.lUnit⁻¹ : Tˣ) : T) = T.lInv := rfl
@[simp] theorem T.val_mUnit : (T.mUnit : T) = T.m := rfl
@[simp] theorem T.val_mUnit_inv : ((T.mUnit⁻¹ : Tˣ) : T) = T.mInv := rfl

theorem T.l_mul_lInv : T.l * T.lInv = 1 := T.lUnit.mul_inv
theorem T.lInv_mul_l : T.lInv * T.l = 1 := T.lUnit.inv_mul
theorem T.m_mul_mInv : T.m * T.mInv = 1 := T.mUnit.mul_inv
theorem T.mInv_mul_m : T.mInv * T.m = 1 := T.mUnit.inv_mul

theorem T.l_ne_zero : T.l ≠ 0 := T.lUnit.ne_zero
theorem T.m_ne_zero : T.m ≠ 0 := T.mUnit.ne_zero

/-- `μ = -(l + l^{-1}) m^{-1}` of lp:lm (sm-3:944-945, lp:source-skein: "`μ = -(l+l^{-1})m^{-1}`"). -/
noncomputable def T.mu : T := -(T.l + T.lInv) * T.mInv

theorem T.mu_mul_m : T.mu * T.m = -(T.l + T.lInv) := by
  rw [T.mu, mul_assoc, T.mInv_mul_m, mul_one]

/-! ### Generators of `RG` and `TG` -/

/-- `a ∈ R_G`. -/
noncomputable def RG.a : RG := single (1, 0) 1
/-- `z ∈ R_G`. -/
noncomputable def RG.z : RG := single (0, 1) 1
/-- `a^{-1} ∈ R_G`. -/
noncomputable def RG.aInv : RG := single (-1, 0) 1
/-- `z^{-1} ∈ R_G`. -/
noncomputable def RG.zInv : RG := single (0, -1) 1
/-- `a` as a unit of `R_G`. -/
noncomputable def RG.aUnit : RGˣ := Laurent₂.monoUnit (1, 0)
/-- `z` as a unit of `R_G`. -/
noncomputable def RG.zUnit : RGˣ := Laurent₂.monoUnit (0, 1)

@[simp] theorem RG.val_aUnit : (RG.aUnit : RG) = RG.a := rfl
@[simp] theorem RG.val_aUnit_inv : ((RG.aUnit⁻¹ : RGˣ) : RG) = RG.aInv := rfl
@[simp] theorem RG.val_zUnit : (RG.zUnit : RG) = RG.z := rfl
@[simp] theorem RG.val_zUnit_inv : ((RG.zUnit⁻¹ : RGˣ) : RG) = RG.zInv := rfl

theorem RG.a_mul_aInv : RG.a * RG.aInv = 1 := RG.aUnit.mul_inv
theorem RG.z_mul_zInv : RG.z * RG.zInv = 1 := RG.zUnit.mul_inv

/-- `l ∈ T_G`. -/
noncomputable def TG.l : TG := (single (1, 0) 1 : Laurent₂ GaussianInt)
/-- `m ∈ T_G`. -/
noncomputable def TG.m : TG := (single (0, 1) 1 : Laurent₂ GaussianInt)
/-- `l^{-1} ∈ T_G`. -/
noncomputable def TG.lInv : TG := (single (-1, 0) 1 : Laurent₂ GaussianInt)
/-- `m^{-1} ∈ T_G`. -/
noncomputable def TG.mInv : TG := (single (0, -1) 1 : Laurent₂ GaussianInt)
/-- `l` as a unit of `T_G`. -/
noncomputable def TG.lUnit : TGˣ := (Laurent₂.monoUnit (1, 0) : (Laurent₂ GaussianInt)ˣ)
/-- `m` as a unit of `T_G`. -/
noncomputable def TG.mUnit : TGˣ := (Laurent₂.monoUnit (0, 1) : (Laurent₂ GaussianInt)ˣ)

@[simp] theorem TG.val_lUnit : (TG.lUnit : TG) = TG.l := rfl
@[simp] theorem TG.val_lUnit_inv : ((TG.lUnit⁻¹ : TGˣ) : TG) = TG.lInv := rfl
@[simp] theorem TG.val_mUnit : (TG.mUnit : TG) = TG.m := rfl
@[simp] theorem TG.val_mUnit_inv : ((TG.mUnit⁻¹ : TGˣ) : TG) = TG.mInv := rfl

theorem TG.l_mul_lInv : TG.l * TG.lInv = 1 := TG.lUnit.mul_inv
theorem TG.m_mul_mInv : TG.m * TG.mInv = 1 := TG.mUnit.mul_inv

/-- Monomial multiplication in `T_G`, transported from `Laurent₂ ℤ[i]` (the definitional bridge used
only inside this file). -/
theorem TG.single_mul_single (e e' : ℤ × ℤ) (c c' : GaussianInt) :
    (show TG from single e c) * (show TG from single e' c') = show TG from single (e + e') (c * c') :=
  AddMonoidAlgebra.single_mul_single e e' c c'

/-! ### Coefficient extraction `[a^d z^k]` and the `[z^k]` rows -/

/-- `[a^d z^k] f`: the coefficient of the monomial `a^d z^k` in `f ∈ R`, "zero if that monomial is
absent" (def:C, sm-3:1692-1694: "`c(Q) = [a^{d_Q} z^0] H^+_Q(a,z) ∈ ℤ`, the coefficient of
`a^{d_Q}z^0` (zero if that monomial is absent)"). Finsupp evaluation of the coefficient function. -/
def coeffAt (d k : ℤ) (f : R) : ℤ := f.coeff (d, k)

@[simp] theorem coeffAt_zero (d k : ℤ) : coeffAt d k (0 : R) = 0 := rfl

theorem coeffAt_add (d k : ℤ) (f g : R) : coeffAt d k (f + g) = coeffAt d k f + coeffAt d k g := by
  simp [coeffAt]

theorem coeffAt_neg (d k : ℤ) (f : R) : coeffAt d k (-f) = -coeffAt d k f := by
  simp [coeffAt]

theorem coeffAt_sub (d k : ℤ) (f g : R) : coeffAt d k (f - g) = coeffAt d k f - coeffAt d k g := by
  simp [coeffAt]

theorem coeffAt_single (d k p q : ℤ) (c : ℤ) :
    coeffAt d k (single (p, q) c) = if (p, q) = (d, k) then c else 0 := by
  simp [coeffAt, Finsupp.single_apply]

theorem coeffAt_single_self (d k : ℤ) (c : ℤ) : coeffAt d k (single (d, k) c) = c := by
  simp [coeffAt_single]

theorem coeffAt_one (d k : ℤ) : coeffAt d k (1 : R) = if (0, 0) = (d, k) then 1 else 0 := by
  rw [one_def, Prod.mk_zero_zero.symm, coeffAt_single]

theorem coeffAt_a (d k : ℤ) : coeffAt d k R.a = if (1, 0) = (d, k) then 1 else 0 := coeffAt_single ..
theorem coeffAt_z (d k : ℤ) : coeffAt d k R.z = if (0, 1) = (d, k) then 1 else 0 := coeffAt_single ..

/-- Two elements of `R` with the same coefficients `[a^d z^k]` are equal. -/
theorem ext_coeffAt {f g : R} (h : ∀ d k, coeffAt d k f = coeffAt d k g) : f = g := by
  ext ⟨d, k⟩; exact h d k

theorem coeffAt_eq_zero_of_notMem_support {f : R} {d k : ℤ} (h : (d, k) ∉ f.coeff.support) :
    coeffAt d k f = 0 :=
  Finsupp.notMem_support_iff.1 h

theorem mem_support_iff_coeffAt_ne_zero {f : R} {d k : ℤ} :
    (d, k) ∈ f.coeff.support ↔ coeffAt d k f ≠ 0 :=
  Finsupp.mem_support_iff

/-- The `[z^k]` row as an additive map `R →+ ℤ[a^{±1}]`: `zRowHom k f` is the Laurent polynomial in
`a` whose `a^d` coefficient is `[a^d z^k] f`. This is the `[z^{1-c}] P_D ∈ ℤ[a^{±1}]` of
mp:lowest (sm-3:1588-1591: "`[z^{1-c}] P_D = a^{-2Λ}(a-a^{-1})^{c-1} ∏ [z^0] P_{D_i}`"). Built
from `Finsupp.comapDomain` along the injection `d ↦ (d, k)`. -/
noncomputable def zRowHom (k : ℤ) : R →+ LaurentPolynomial ℤ :=
  (AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom).comp
    ((Finsupp.comapDomain.addMonoidHom (f := fun d : ℤ => (d, k))
      (fun _ _ h => by simpa using congrArg Prod.fst h)).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

/-- The `[z^k]` row of `f ∈ R`, an element of `ℤ[a^{±1}]` (Mathlib's `LaurentPolynomial ℤ`). -/
noncomputable def zRow (k : ℤ) (f : R) : LaurentPolynomial ℤ := zRowHom k f

/-- Pinning lemma: the `a^d` coefficient of the `[z^k]` row is `[a^d z^k] f`. -/
@[simp] theorem coeff_zRow (k : ℤ) (f : R) (d : ℤ) : (zRow k f).coeff d = coeffAt d k f := by
  simp [zRow, zRowHom, coeffAt, Finsupp.comapDomain.addMonoidHom, Finsupp.comapDomain_apply]

theorem zRow_zero (k : ℤ) : zRow k (0 : R) = 0 := by simp [zRow]
theorem zRow_add (k : ℤ) (f g : R) : zRow k (f + g) = zRow k f + zRow k g := by simp [zRow]
theorem zRow_neg (k : ℤ) (f : R) : zRow k (-f) = -zRow k f := by simp [zRow]
theorem zRow_sub (k : ℤ) (f g : R) : zRow k (f - g) = zRow k f - zRow k g := by simp [zRow]

/-- The `[z^k]` row of a monomial `c a^p z^q` is `c a^p` if `q = k` and `0` otherwise. -/
theorem zRow_single (k p q : ℤ) (c : ℤ) :
    zRow k (single (p, q) c) = if q = k then single p c else 0 := by
  ext d
  rw [coeff_zRow, coeffAt_single]
  split_ifs with h1 h2 h2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact Finsupp.single_eq_same.symm
  · exact absurd (Prod.mk.inj h1).2 h2
  · have hp : p ≠ d := fun hpd => h1 (by rw [hpd, h2])
    exact (Finsupp.single_eq_of_ne' hp).symm
  · rfl

theorem zRow_eq_zero_iff (k : ℤ) (f : R) : zRow k f = 0 ↔ ∀ d, coeffAt d k f = 0 := by
  constructor
  · intro h d
    have := congrArg (fun p : LaurentPolynomial ℤ => p.coeff d) h
    simpa using this
  · intro h
    ext d
    simp [h d]

/-! ### def:adeg — degrees in `a` and in `z` -/

/-- The a-exponent weight `(d, k) ↦ d` valued in `WithBot ℤ`. -/
def wtA : ℤ × ℤ → WithBot ℤ := fun e => (e.1 : WithBot ℤ)
/-- The a-exponent weight `(d, k) ↦ d` valued in `WithTop ℤ`. -/
def wtA' : ℤ × ℤ → WithTop ℤ := fun e => (e.1 : WithTop ℤ)
/-- The z-exponent weight `(d, k) ↦ k` valued in `WithBot ℤ`. -/
def wtZ : ℤ × ℤ → WithBot ℤ := fun e => (e.2 : WithBot ℤ)
/-- The z-exponent weight `(d, k) ↦ k` valued in `WithTop ℤ`. -/
def wtZ' : ℤ × ℤ → WithTop ℤ := fun e => (e.2 : WithTop ℤ)

@[simp] theorem wtA_apply (d k : ℤ) : wtA (d, k) = (d : WithBot ℤ) := rfl
@[simp] theorem wtA'_apply (d k : ℤ) : wtA' (d, k) = (d : WithTop ℤ) := rfl
@[simp] theorem wtZ_apply (d k : ℤ) : wtZ (d, k) = (k : WithBot ℤ) := rfl
@[simp] theorem wtZ'_apply (d k : ℤ) : wtZ' (d, k) = (k : WithTop ℤ) := rfl

theorem wtA_add (e e' : ℤ × ℤ) : wtA (e + e') = wtA e + wtA e' := by simp [wtA]
theorem wtA'_add (e e' : ℤ × ℤ) : wtA' (e + e') = wtA' e + wtA' e' := by simp [wtA']
theorem wtZ_add (e e' : ℤ × ℤ) : wtZ (e + e') = wtZ e + wtZ e' := by simp [wtZ]
theorem wtZ'_add (e e' : ℤ × ℤ) : wtZ' (e + e') = wtZ' e + wtZ' e' := by simp [wtZ']

/-- `deg_a f` of def:adeg (sm-3:1887-1891): the supremum of the a-exponents in the support of `f`,
`⊥` for `f = 0` (Mathlib `AddMonoidAlgebra.supDegree` with weight `Prod.fst`). For `f ≠ 0` it is an
integer, "the largest a-exponent with nonzero coefficient": `degA_eq_degAZ`, `degAZ_spec`. -/
noncomputable def degA (f : R) : WithBot ℤ := f.supDegree wtA

/-- `mindeg_a f` of def:adeg (sm-3:1890-1891, "and `mindeg_a f` the smallest"): the infimum of the
a-exponents in the support of `f`, `⊤` for `f = 0` (Mathlib `infDegree`). -/
noncomputable def mindegA (f : R) : WithTop ℤ := f.infDegree wtA'

/-- `deg_z f` of def:adeg (sm-3:1891-1893, "The same symbols with the subscript z denote the largest
and smallest z-exponents of a nonzero element of `ℤ[a^{±1},z^{±1}]`"). -/
noncomputable def degZ (f : R) : WithBot ℤ := f.supDegree wtZ

/-- `mindeg_z f` of def:adeg (sm-3:1891-1893). -/
noncomputable def mindegZ (f : R) : WithTop ℤ := f.infDegree wtZ'

section degreeLemmas

/-! #### `degA` -/

@[simp] theorem degA_zero : degA 0 = ⊥ := by simp [degA]

theorem le_degA_of_coeffAt_ne_zero {f : R} {d k : ℤ} (h : coeffAt d k f ≠ 0) :
    (d : WithBot ℤ) ≤ degA f :=
  Finset.le_sup (f := wtA) (Finsupp.mem_support_iff.2 h)

theorem coeffAt_eq_zero_of_degA_lt {f : R} {d k : ℤ} (h : degA f < d) : coeffAt d k f = 0 :=
  coeff_eq_zero_of_not_le_supDegree (D := wtA) (a := (d, k)) (not_le.2 h)

/-- For `f ≠ 0`, `deg_a f` is attained: some monomial `a^d z^k` with nonzero coefficient has
`d = deg_a f`. -/
theorem exists_degA_eq {f : R} (hf : f ≠ 0) : ∃ d k : ℤ, coeffAt d k f ≠ 0 ∧ degA f = d := by
  obtain ⟨⟨d, k⟩, hmem, he⟩ := exists_supDegree_mem_support wtA hf
  exact ⟨d, k, Finsupp.mem_support_iff.1 hmem, he⟩

theorem degA_ne_bot {f : R} (hf : f ≠ 0) : degA f ≠ ⊥ := by
  obtain ⟨d, k, -, he⟩ := exists_degA_eq hf
  rw [he]; exact WithBot.coe_ne_bot

theorem degA_eq_bot_iff {f : R} : degA f = ⊥ ↔ f = 0 :=
  ⟨fun h => by_contra fun hf => degA_ne_bot hf h, fun h => h ▸ degA_zero⟩

theorem degA_add_le (f g : R) : degA (f + g) ≤ max (degA f) (degA g) := supDegree_add_le
theorem degA_neg (f : R) : degA (-f) = degA f := supDegree_neg
theorem degA_sub_le (f g : R) : degA (f - g) ≤ max (degA f) (degA g) := supDegree_sub_le
theorem degA_mul_le (f g : R) : degA (f * g) ≤ degA f + degA g := supDegree_mul_le wtA_add

theorem degA_single (d k : ℤ) {c : ℤ} (hc : c ≠ 0) : degA (single (d, k) c) = d :=
  supDegree_single_ne_zero (D := wtA) (d, k) hc

@[simp] theorem degA_a : degA R.a = 1 := degA_single 1 0 one_ne_zero
@[simp] theorem degA_aInv : degA R.aInv = ((-1 : ℤ) : WithBot ℤ) := degA_single (-1) 0 one_ne_zero
@[simp] theorem degA_z : degA R.z = 0 := degA_single 0 1 one_ne_zero
@[simp] theorem degA_one : degA (1 : R) = 0 := by
  rw [one_def, Prod.mk_zero_zero.symm]; exact degA_single 0 0 one_ne_zero

/-- The integer value of `deg_a f` (meaningful for `f ≠ 0`; `0` by convention at `f = 0`). -/
noncomputable def degAZ (f : R) : ℤ := (degA f).unbotD 0

/-- def:adeg, "both are integers": for `f ≠ 0`, `deg_a f` is the integer `degAZ f`. -/
theorem degA_eq_degAZ {f : R} (hf : f ≠ 0) : degA f = (degAZ f : WithBot ℤ) := by
  obtain ⟨d, k, -, he⟩ := exists_degA_eq hf
  rw [degAZ, he, WithBot.unbotD_coe]

/-- def:adeg, "the largest a-exponent with nonzero coefficient": for `f ≠ 0`, `degAZ f` is attained
by some monomial with nonzero coefficient and bounds every exponent of the support. -/
theorem degAZ_spec {f : R} (hf : f ≠ 0) :
    (∃ k, coeffAt (degAZ f) k f ≠ 0) ∧ ∀ d k, coeffAt d k f ≠ 0 → d ≤ degAZ f := by
  obtain ⟨d, k, hne, he⟩ := exists_degA_eq hf
  have hd : degAZ f = d := by rw [degAZ, he, WithBot.unbotD_coe]
  refine ⟨⟨k, hd ▸ hne⟩, fun d' k' h' => ?_⟩
  have := le_degA_of_coeffAt_ne_zero h'
  rw [he] at this
  rw [hd]; exact WithBot.coe_le_coe.1 this

/-- Uniqueness half of def:adeg: an integer attained by the support and bounding it is `degAZ f`. -/
theorem degAZ_eq_of_spec {f : R} {d : ℤ} (hatt : ∃ k, coeffAt d k f ≠ 0)
    (hbd : ∀ d' k, coeffAt d' k f ≠ 0 → d' ≤ d) : degAZ f = d := by
  obtain ⟨k, hk⟩ := hatt
  have hf : f ≠ 0 := fun h => hk (by simp [h])
  obtain ⟨⟨k₀, hk₀⟩, hb⟩ := degAZ_spec hf
  exact le_antisymm (hbd _ _ hk₀) (hb _ _ hk)

/-! #### `mindegA` -/

@[simp] theorem mindegA_zero : mindegA 0 = ⊤ := by simp [mindegA]

theorem mindegA_le_of_coeffAt_ne_zero {f : R} {d k : ℤ} (h : coeffAt d k f ≠ 0) :
    mindegA f ≤ (d : WithTop ℤ) :=
  Finset.inf_le (f := wtA') (Finsupp.mem_support_iff.2 h)

theorem coeffAt_eq_zero_of_lt_mindegA {f : R} {d k : ℤ} (h : (d : WithTop ℤ) < mindegA f) :
    coeffAt d k f = 0 := by
  by_contra hne
  exact absurd (mindegA_le_of_coeffAt_ne_zero hne) (not_le.2 h)

theorem exists_mindegA_eq {f : R} (hf : f ≠ 0) : ∃ d k : ℤ, coeffAt d k f ≠ 0 ∧ mindegA f = d := by
  obtain ⟨⟨d, k⟩, hmem, he⟩ := Finset.exists_mem_eq_inf f.coeff.support
    (by simpa [Finsupp.support_nonempty_iff] using hf) wtA'
  exact ⟨d, k, Finsupp.mem_support_iff.1 hmem, he⟩

theorem mindegA_ne_top {f : R} (hf : f ≠ 0) : mindegA f ≠ ⊤ := by
  obtain ⟨d, k, -, he⟩ := exists_mindegA_eq hf
  rw [he]; exact WithTop.coe_ne_top

theorem mindegA_eq_top_iff {f : R} : mindegA f = ⊤ ↔ f = 0 :=
  ⟨fun h => by_contra fun hf => mindegA_ne_top hf h, fun h => h ▸ mindegA_zero⟩

theorem le_mindegA_add (f g : R) : min (mindegA f) (mindegA g) ≤ mindegA (f + g) :=
  le_infDegree_add _ f g
theorem le_mindegA_mul (f g : R) : mindegA f + mindegA g ≤ mindegA (f * g) :=
  le_infDegree_mul ⟨wtA', wtA'_add⟩ f g

theorem mindegA_single (d k : ℤ) {c : ℤ} (hc : c ≠ 0) : mindegA (single (d, k) c) = d := by
  simp [mindegA, infDegree, hc]

/-- The integer value of `mindeg_a f` (meaningful for `f ≠ 0`; `0` by convention at `f = 0`). -/
noncomputable def mindegAZ (f : R) : ℤ := (mindegA f).untopD 0

theorem mindegA_eq_mindegAZ {f : R} (hf : f ≠ 0) : mindegA f = (mindegAZ f : WithTop ℤ) := by
  obtain ⟨d, k, -, he⟩ := exists_mindegA_eq hf
  rw [mindegAZ, he, WithTop.untopD_coe]

/-- def:adeg, "the smallest": for `f ≠ 0`, `mindegAZ f` is attained and is a lower bound. -/
theorem mindegAZ_spec {f : R} (hf : f ≠ 0) :
    (∃ k, coeffAt (mindegAZ f) k f ≠ 0) ∧ ∀ d k, coeffAt d k f ≠ 0 → mindegAZ f ≤ d := by
  obtain ⟨d, k, hne, he⟩ := exists_mindegA_eq hf
  have hd : mindegAZ f = d := by rw [mindegAZ, he, WithTop.untopD_coe]
  refine ⟨⟨k, hd ▸ hne⟩, fun d' k' h' => ?_⟩
  have := mindegA_le_of_coeffAt_ne_zero h'
  rw [he] at this
  rw [hd]; exact WithTop.coe_le_coe.1 this

theorem mindegAZ_le_degAZ {f : R} (hf : f ≠ 0) : mindegAZ f ≤ degAZ f := by
  obtain ⟨⟨k, hk⟩, -⟩ := degAZ_spec hf
  exact (mindegAZ_spec hf).2 _ _ hk

/-! #### `degZ` -/

@[simp] theorem degZ_zero : degZ 0 = ⊥ := by simp [degZ]

theorem le_degZ_of_coeffAt_ne_zero {f : R} {d k : ℤ} (h : coeffAt d k f ≠ 0) :
    (k : WithBot ℤ) ≤ degZ f :=
  Finset.le_sup (f := wtZ) (Finsupp.mem_support_iff.2 h)

theorem coeffAt_eq_zero_of_degZ_lt {f : R} {d k : ℤ} (h : degZ f < k) : coeffAt d k f = 0 :=
  coeff_eq_zero_of_not_le_supDegree (D := wtZ) (a := (d, k)) (not_le.2 h)

theorem exists_degZ_eq {f : R} (hf : f ≠ 0) : ∃ d k : ℤ, coeffAt d k f ≠ 0 ∧ degZ f = k := by
  obtain ⟨⟨d, k⟩, hmem, he⟩ := exists_supDegree_mem_support wtZ hf
  exact ⟨d, k, Finsupp.mem_support_iff.1 hmem, he⟩

theorem degZ_ne_bot {f : R} (hf : f ≠ 0) : degZ f ≠ ⊥ := by
  obtain ⟨d, k, -, he⟩ := exists_degZ_eq hf
  rw [he]; exact WithBot.coe_ne_bot

theorem degZ_eq_bot_iff {f : R} : degZ f = ⊥ ↔ f = 0 :=
  ⟨fun h => by_contra fun hf => degZ_ne_bot hf h, fun h => h ▸ degZ_zero⟩

theorem degZ_add_le (f g : R) : degZ (f + g) ≤ max (degZ f) (degZ g) := supDegree_add_le
theorem degZ_neg (f : R) : degZ (-f) = degZ f := supDegree_neg
theorem degZ_mul_le (f g : R) : degZ (f * g) ≤ degZ f + degZ g := supDegree_mul_le wtZ_add

theorem degZ_single (d k : ℤ) {c : ℤ} (hc : c ≠ 0) : degZ (single (d, k) c) = k :=
  supDegree_single_ne_zero (D := wtZ) (d, k) hc

@[simp] theorem degZ_z : degZ R.z = 1 := degZ_single 0 1 one_ne_zero
@[simp] theorem degZ_zInv : degZ R.zInv = ((-1 : ℤ) : WithBot ℤ) := degZ_single 0 (-1) one_ne_zero
@[simp] theorem degZ_a : degZ R.a = 0 := degZ_single 1 0 one_ne_zero

/-- The integer value of `deg_z f` (meaningful for `f ≠ 0`). -/
noncomputable def degZZ (f : R) : ℤ := (degZ f).unbotD 0

theorem degZ_eq_degZZ {f : R} (hf : f ≠ 0) : degZ f = (degZZ f : WithBot ℤ) := by
  obtain ⟨d, k, -, he⟩ := exists_degZ_eq hf
  rw [degZZ, he, WithBot.unbotD_coe]

/-- def:adeg for the subscript z, "the largest z-exponent": attained and an upper bound. -/
theorem degZZ_spec {f : R} (hf : f ≠ 0) :
    (∃ d, coeffAt d (degZZ f) f ≠ 0) ∧ ∀ d k, coeffAt d k f ≠ 0 → k ≤ degZZ f := by
  obtain ⟨d, k, hne, he⟩ := exists_degZ_eq hf
  have hk : degZZ f = k := by rw [degZZ, he, WithBot.unbotD_coe]
  refine ⟨⟨d, hk ▸ hne⟩, fun d' k' h' => ?_⟩
  have := le_degZ_of_coeffAt_ne_zero h'
  rw [he] at this
  rw [hk]; exact WithBot.coe_le_coe.1 this

/-! #### `mindegZ` -/

@[simp] theorem mindegZ_zero : mindegZ 0 = ⊤ := by simp [mindegZ]

theorem mindegZ_le_of_coeffAt_ne_zero {f : R} {d k : ℤ} (h : coeffAt d k f ≠ 0) :
    mindegZ f ≤ (k : WithTop ℤ) :=
  Finset.inf_le (f := wtZ') (Finsupp.mem_support_iff.2 h)

theorem coeffAt_eq_zero_of_lt_mindegZ {f : R} {d k : ℤ} (h : (k : WithTop ℤ) < mindegZ f) :
    coeffAt d k f = 0 := by
  by_contra hne
  exact absurd (mindegZ_le_of_coeffAt_ne_zero hne) (not_le.2 h)

theorem exists_mindegZ_eq {f : R} (hf : f ≠ 0) : ∃ d k : ℤ, coeffAt d k f ≠ 0 ∧ mindegZ f = k := by
  obtain ⟨⟨d, k⟩, hmem, he⟩ := Finset.exists_mem_eq_inf f.coeff.support
    (by simpa [Finsupp.support_nonempty_iff] using hf) wtZ'
  exact ⟨d, k, Finsupp.mem_support_iff.1 hmem, he⟩

theorem mindegZ_ne_top {f : R} (hf : f ≠ 0) : mindegZ f ≠ ⊤ := by
  obtain ⟨d, k, -, he⟩ := exists_mindegZ_eq hf
  rw [he]; exact WithTop.coe_ne_top

theorem le_mindegZ_add (f g : R) : min (mindegZ f) (mindegZ g) ≤ mindegZ (f + g) :=
  le_infDegree_add _ f g
theorem le_mindegZ_mul (f g : R) : mindegZ f + mindegZ g ≤ mindegZ (f * g) :=
  le_infDegree_mul ⟨wtZ', wtZ'_add⟩ f g

theorem mindegZ_single (d k : ℤ) {c : ℤ} (hc : c ≠ 0) : mindegZ (single (d, k) c) = k := by
  simp [mindegZ, infDegree, hc]

/-- The integer value of `mindeg_z f` (meaningful for `f ≠ 0`). -/
noncomputable def mindegZZ (f : R) : ℤ := (mindegZ f).untopD 0

theorem mindegZ_eq_mindegZZ {f : R} (hf : f ≠ 0) : mindegZ f = (mindegZZ f : WithTop ℤ) := by
  obtain ⟨d, k, -, he⟩ := exists_mindegZ_eq hf
  rw [mindegZZ, he, WithTop.untopD_coe]

/-- def:adeg for the subscript z, "the smallest z-exponent": attained and a lower bound. -/
theorem mindegZZ_spec {f : R} (hf : f ≠ 0) :
    (∃ d, coeffAt d (mindegZZ f) f ≠ 0) ∧ ∀ d k, coeffAt d k f ≠ 0 → mindegZZ f ≤ k := by
  obtain ⟨d, k, hne, he⟩ := exists_mindegZ_eq hf
  have hk : mindegZZ f = k := by rw [mindegZZ, he, WithTop.untopD_coe]
  refine ⟨⟨d, hk ▸ hne⟩, fun d' k' h' => ?_⟩
  have := mindegZ_le_of_coeffAt_ne_zero h'
  rw [he] at this
  rw [hk]; exact WithTop.coe_le_coe.1 this

theorem degZZ_eq_of_spec {f : R} {k : ℤ} (hatt : ∃ d, coeffAt d k f ≠ 0)
    (hbd : ∀ d k', coeffAt d k' f ≠ 0 → k' ≤ k) : degZZ f = k := by
  obtain ⟨d, hd⟩ := hatt
  have hf : f ≠ 0 := fun h => hd (by simp [h])
  obtain ⟨⟨d₀, hd₀⟩, hb⟩ := degZZ_spec hf
  exact le_antisymm (hbd _ _ hd₀) (hb _ _ hd)

theorem mindegAZ_eq_of_spec {f : R} {d : ℤ} (hatt : ∃ k, coeffAt d k f ≠ 0)
    (hbd : ∀ d' k, coeffAt d' k f ≠ 0 → d ≤ d') : mindegAZ f = d := by
  obtain ⟨k, hk⟩ := hatt
  have hf : f ≠ 0 := fun h => hk (by simp [h])
  obtain ⟨⟨k₀, hk₀⟩, hb⟩ := mindegAZ_spec hf
  exact le_antisymm (hb _ _ hk) (hbd _ _ hk₀)

theorem mindegZZ_eq_of_spec {f : R} {k : ℤ} (hatt : ∃ d, coeffAt d k f ≠ 0)
    (hbd : ∀ d k', coeffAt d k' f ≠ 0 → k ≤ k') : mindegZZ f = k := by
  obtain ⟨d, hd⟩ := hatt
  have hf : f ≠ 0 := fun h => hd (by simp [h])
  obtain ⟨⟨d₀, hd₀⟩, hb⟩ := mindegZZ_spec hf
  exact le_antisymm (hb _ _ hd) (hbd _ _ hd₀)

/-! #### Multiplicativity of the degrees (def:adeg's "integral domain `ℤ[z^{±1}]`", sm-3:1889)

For nonzero `f, g` the extreme monomial pair in a lexicographic order contributes exactly one term
to `f * g` (Mathlib `coeff_mul_add_of_uniqueAdd`), whose coefficient is a product of nonzero
integers; hence `deg_a (fg) = deg_a f + deg_a g` and likewise for `mindeg_a`, `deg_z`, `mindeg_z`. -/

/-- `toLex : ℤ × ℤ → Lex (ℤ × ℤ)` as an additive homomorphism. -/
def toLexHom : ℤ × ℤ →+ Lex (ℤ × ℤ) where
  toFun := toLex
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `e ↦ toLex (-e)`: reverses the lexicographic order. -/
def negToLexHom : ℤ × ℤ →+ Lex (ℤ × ℤ) where
  toFun e := toLex (-e)
  map_zero' := by simp
  map_add' _ _ := by rw [neg_add]; rfl

/-- `e ↦ toLex e.swap`: lexicographic order with the z-exponent first. -/
def swapToLexHom : ℤ × ℤ →+ Lex (ℤ × ℤ) :=
  toLexHom.comp (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).toAddMonoidHom

/-- `e ↦ toLex (-e.swap)`. -/
def negSwapToLexHom : ℤ × ℤ →+ Lex (ℤ × ℤ) :=
  negToLexHom.comp (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).toAddMonoidHom

@[simp] theorem swapToLexHom_apply (e : ℤ × ℤ) : swapToLexHom e = toLex (e.2, e.1) := rfl
@[simp] theorem negSwapToLexHom_apply (e : ℤ × ℤ) : negSwapToLexHom e = toLex (-(e.2, e.1)) := rfl

theorem toLexHom_injective : Function.Injective toLexHom := toLex.injective
theorem negToLexHom_injective : Function.Injective negToLexHom := fun _ _ h =>
  neg_inj.1 (toLex.injective h)
theorem swapToLexHom_injective : Function.Injective swapToLexHom := fun _ _ h =>
  (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).injective (toLexHom_injective h)
theorem negSwapToLexHom_injective : Function.Injective negSwapToLexHom := fun _ _ h =>
  (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).injective (negToLexHom_injective h)

theorem fst_le_of_toLexHom_le {e e' : ℤ × ℤ} (h : toLexHom e ≤ toLexHom e') : e.1 ≤ e'.1 :=
  Prod.Lex.monotone_fst _ _ h
theorem fst_ge_of_negToLexHom_le {e e' : ℤ × ℤ} (h : negToLexHom e ≤ negToLexHom e') : e'.1 ≤ e.1 :=
  neg_le_neg_iff.1 (Prod.Lex.monotone_fst _ _ h)
theorem snd_le_of_swapToLexHom_le {e e' : ℤ × ℤ} (h : swapToLexHom e ≤ swapToLexHom e') :
    e.2 ≤ e'.2 := by
  rw [swapToLexHom_apply, swapToLexHom_apply] at h
  exact Prod.Lex.monotone_fst _ _ h
theorem snd_ge_of_negSwapToLexHom_le {e e' : ℤ × ℤ} (h : negSwapToLexHom e ≤ negSwapToLexHom e') :
    e'.2 ≤ e.2 := by
  rw [negSwapToLexHom_apply, negSwapToLexHom_apply] at h
  exact neg_le_neg_iff.1 (Prod.Lex.monotone_fst _ _ h)

/-- The pair of `w`-maximal monomials of nonzero `f, g` contributes a single term to `f * g`. -/
theorem coeff_mul_of_max_weight (w : ℤ × ℤ →+ Lex (ℤ × ℤ)) (hw : Function.Injective w) {f g : R}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ e₁ ∈ f.coeff.support, ∃ e₂ ∈ g.coeff.support,
      (∀ e ∈ f.coeff.support, w e ≤ w e₁) ∧ (∀ e ∈ g.coeff.support, w e ≤ w e₂) ∧
      (f * g).coeff (e₁ + e₂) = f.coeff e₁ * g.coeff e₂ := by
  have hfs : f.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hf
  have hgs : g.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hg
  obtain ⟨e₁, he₁, hmax₁⟩ := Finset.exists_max_image f.coeff.support w hfs
  obtain ⟨e₂, he₂, hmax₂⟩ := Finset.exists_max_image g.coeff.support w hgs
  refine ⟨e₁, he₁, e₂, he₂, hmax₁, hmax₂, ?_⟩
  apply coeff_mul_add_of_uniqueAdd
  intro a b ha hb hab
  have h1 := hmax₁ a ha
  have h2 := hmax₂ b hb
  have hsum : w a + w b = w e₁ + w e₂ := by rw [← map_add, ← map_add, hab]
  have ha' : w a = w e₁ := by
    by_contra hne
    exact absurd hsum (ne_of_lt (add_lt_add_of_lt_of_le (lt_of_le_of_ne h1 hne) h2))
  have hb' : w b = w e₂ := by
    by_contra hne
    exact absurd hsum (ne_of_lt (add_lt_add_of_le_of_lt h1 (lt_of_le_of_ne h2 hne)))
  exact ⟨hw ha', hw hb'⟩

/-- The extreme term of a product is nonzero (coefficients in the domain `ℤ`). -/
theorem coeffAt_mul_of_max_weight (w : ℤ × ℤ →+ Lex (ℤ × ℤ)) (hw : Function.Injective w) {f g : R}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ e₁ e₂ : ℤ × ℤ, coeffAt e₁.1 e₁.2 f ≠ 0 ∧ coeffAt e₂.1 e₂.2 g ≠ 0 ∧
      (∀ d k, coeffAt d k f ≠ 0 → w (d, k) ≤ w e₁) ∧ (∀ d k, coeffAt d k g ≠ 0 → w (d, k) ≤ w e₂) ∧
      coeffAt (e₁.1 + e₂.1) (e₁.2 + e₂.2) (f * g) ≠ 0 := by
  obtain ⟨e₁, he₁, e₂, he₂, hm₁, hm₂, hc⟩ := coeff_mul_of_max_weight w hw hf hg
  refine ⟨e₁, e₂, Finsupp.mem_support_iff.1 he₁, Finsupp.mem_support_iff.1 he₂,
    fun d k h => hm₁ (d, k) (Finsupp.mem_support_iff.2 h),
    fun d k h => hm₂ (d, k) (Finsupp.mem_support_iff.2 h), ?_⟩
  show (f * g).coeff (e₁.1 + e₂.1, e₁.2 + e₂.2) ≠ 0
  rw [← Prod.mk_add_mk, hc]
  exact mul_ne_zero (Finsupp.mem_support_iff.1 he₁) (Finsupp.mem_support_iff.1 he₂)

/-- `deg_a (fg) = deg_a f + deg_a g` for nonzero `f, g` (integer form). -/
theorem degAZ_mul {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) : degAZ (f * g) = degAZ f + degAZ g := by
  obtain ⟨e₁, e₂, h₁, h₂, hm₁, hm₂, hprod⟩ :=
    coeffAt_mul_of_max_weight toLexHom toLexHom_injective hf hg
  have hd₁ : degAZ f = e₁.1 :=
    degAZ_eq_of_spec ⟨e₁.2, h₁⟩ fun d k h => fst_le_of_toLexHom_le (hm₁ d k h)
  have hd₂ : degAZ g = e₂.1 :=
    degAZ_eq_of_spec ⟨e₂.2, h₂⟩ fun d k h => fst_le_of_toLexHom_le (hm₂ d k h)
  rw [hd₁, hd₂]
  refine degAZ_eq_of_spec ⟨_, hprod⟩ fun d k h => ?_
  have hle := le_degA_of_coeffAt_ne_zero h
  rw [degA_eq_degAZ (mul_ne_zero hf hg)] at hle
  have hle' : d ≤ degAZ (f * g) := WithBot.coe_le_coe.1 hle
  have hup : (degAZ (f * g) : WithBot ℤ) ≤ (degAZ f : WithBot ℤ) + (degAZ g : WithBot ℤ) := by
    rw [← degA_eq_degAZ (mul_ne_zero hf hg), ← degA_eq_degAZ hf, ← degA_eq_degAZ hg]
    exact degA_mul_le f g
  rw [← WithBot.coe_add] at hup
  have := WithBot.coe_le_coe.1 hup
  omega

/-- def:adeg with the "integral domain" clause: `deg_a (fg) = deg_a f + deg_a g` for nonzero `f, g`. -/
theorem degA_mul {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) : degA (f * g) = degA f + degA g := by
  rw [degA_eq_degAZ (mul_ne_zero hf hg), degA_eq_degAZ hf, degA_eq_degAZ hg, degAZ_mul hf hg,
    WithBot.coe_add]

theorem mindegAZ_mul {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) :
    mindegAZ (f * g) = mindegAZ f + mindegAZ g := by
  obtain ⟨e₁, e₂, h₁, h₂, hm₁, hm₂, hprod⟩ :=
    coeffAt_mul_of_max_weight negToLexHom negToLexHom_injective hf hg
  have hd₁ : mindegAZ f = e₁.1 :=
    mindegAZ_eq_of_spec ⟨e₁.2, h₁⟩ fun d k h => fst_ge_of_negToLexHom_le (hm₁ d k h)
  have hd₂ : mindegAZ g = e₂.1 :=
    mindegAZ_eq_of_spec ⟨e₂.2, h₂⟩ fun d k h => fst_ge_of_negToLexHom_le (hm₂ d k h)
  rw [hd₁, hd₂]
  refine mindegAZ_eq_of_spec ⟨_, hprod⟩ fun d k h => ?_
  have hle := mindegA_le_of_coeffAt_ne_zero h
  rw [mindegA_eq_mindegAZ (mul_ne_zero hf hg)] at hle
  have hle' : mindegAZ (f * g) ≤ d := WithTop.coe_le_coe.1 hle
  have hlo : (mindegAZ f : WithTop ℤ) + (mindegAZ g : WithTop ℤ) ≤ (mindegAZ (f * g) : WithTop ℤ) := by
    rw [← mindegA_eq_mindegAZ (mul_ne_zero hf hg), ← mindegA_eq_mindegAZ hf, ← mindegA_eq_mindegAZ hg]
    exact le_mindegA_mul f g
  rw [← WithTop.coe_add] at hlo
  have := WithTop.coe_le_coe.1 hlo
  omega

theorem mindegA_mul {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) :
    mindegA (f * g) = mindegA f + mindegA g := by
  rw [mindegA_eq_mindegAZ (mul_ne_zero hf hg), mindegA_eq_mindegAZ hf, mindegA_eq_mindegAZ hg,
    mindegAZ_mul hf hg, WithTop.coe_add]

theorem degZZ_mul {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) : degZZ (f * g) = degZZ f + degZZ g := by
  obtain ⟨e₁, e₂, h₁, h₂, hm₁, hm₂, hprod⟩ :=
    coeffAt_mul_of_max_weight swapToLexHom swapToLexHom_injective hf hg
  have hd₁ : degZZ f = e₁.2 :=
    degZZ_eq_of_spec ⟨e₁.1, h₁⟩ fun d k h => snd_le_of_swapToLexHom_le (hm₁ d k h)
  have hd₂ : degZZ g = e₂.2 :=
    degZZ_eq_of_spec ⟨e₂.1, h₂⟩ fun d k h => snd_le_of_swapToLexHom_le (hm₂ d k h)
  rw [hd₁, hd₂]
  refine degZZ_eq_of_spec ⟨_, hprod⟩ fun d k h => ?_
  have hle := le_degZ_of_coeffAt_ne_zero h
  rw [degZ_eq_degZZ (mul_ne_zero hf hg)] at hle
  have hle' : k ≤ degZZ (f * g) := WithBot.coe_le_coe.1 hle
  have hup : (degZZ (f * g) : WithBot ℤ) ≤ (degZZ f : WithBot ℤ) + (degZZ g : WithBot ℤ) := by
    rw [← degZ_eq_degZZ (mul_ne_zero hf hg), ← degZ_eq_degZZ hf, ← degZ_eq_degZZ hg]
    exact degZ_mul_le f g
  rw [← WithBot.coe_add] at hup
  have := WithBot.coe_le_coe.1 hup
  omega

theorem degZ_mul {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) : degZ (f * g) = degZ f + degZ g := by
  rw [degZ_eq_degZZ (mul_ne_zero hf hg), degZ_eq_degZZ hf, degZ_eq_degZZ hg, degZZ_mul hf hg,
    WithBot.coe_add]

theorem mindegZZ_mul {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) :
    mindegZZ (f * g) = mindegZZ f + mindegZZ g := by
  obtain ⟨e₁, e₂, h₁, h₂, hm₁, hm₂, hprod⟩ :=
    coeffAt_mul_of_max_weight negSwapToLexHom negSwapToLexHom_injective hf hg
  have hd₁ : mindegZZ f = e₁.2 :=
    mindegZZ_eq_of_spec ⟨e₁.1, h₁⟩ fun d k h => snd_ge_of_negSwapToLexHom_le (hm₁ d k h)
  have hd₂ : mindegZZ g = e₂.2 :=
    mindegZZ_eq_of_spec ⟨e₂.1, h₂⟩ fun d k h => snd_ge_of_negSwapToLexHom_le (hm₂ d k h)
  rw [hd₁, hd₂]
  refine mindegZZ_eq_of_spec ⟨_, hprod⟩ fun d k h => ?_
  have hle := mindegZ_le_of_coeffAt_ne_zero h
  rw [mindegZ_eq_mindegZZ (mul_ne_zero hf hg)] at hle
  have hle' : mindegZZ (f * g) ≤ k := WithTop.coe_le_coe.1 hle
  have hlo : (mindegZZ f : WithTop ℤ) + (mindegZZ g : WithTop ℤ) ≤ (mindegZZ (f * g) : WithTop ℤ) := by
    rw [← mindegZ_eq_mindegZZ (mul_ne_zero hf hg), ← mindegZ_eq_mindegZZ hf, ← mindegZ_eq_mindegZZ hg]
    exact le_mindegZ_mul f g
  rw [← WithTop.coe_add] at hlo
  have := WithTop.coe_le_coe.1 hlo
  omega

theorem mindegZ_mul {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) :
    mindegZ (f * g) = mindegZ f + mindegZ g := by
  rw [mindegZ_eq_mindegZZ (mul_ne_zero hf hg), mindegZ_eq_mindegZZ hf, mindegZ_eq_mindegZZ hg,
    mindegZZ_mul hf hg, WithTop.coe_add]

/-- The `[z^k]` row vanishes above `deg_z`. -/
theorem zRow_eq_zero_of_degZ_lt {f : R} {k : ℤ} (h : degZ f < k) : zRow k f = 0 :=
  (zRow_eq_zero_iff k f).2 fun _ => coeffAt_eq_zero_of_degZ_lt h

/-- The `[z^k]` row vanishes below `mindeg_z`. -/
theorem zRow_eq_zero_of_lt_mindegZ {f : R} {k : ℤ} (h : (k : WithTop ℤ) < mindegZ f) :
    zRow k f = 0 :=
  (zRow_eq_zero_iff k f).2 fun _ => coeffAt_eq_zero_of_lt_mindegZ h

end degreeLemmas

/-! ### lp:support — the additive subgroups `M_c = z^{1-c} ℤ[a^{±1}, z^2]` -/

/-- `f ∈ M_c = z^{1-c} ℤ[a^{±1}, z^2]` (lp:support, sm-3:1055-1056: "`P_D ∈ z^{1-c} ℤ[a^{±1},z^2]`";
lp:core proof 1119-1120: "let `M_c = z^{1-c} ℤ[a^{±1},z^2]`, viewed as an additive subgroup"):
every monomial `a^d z^k` in the support of `f` has `k = 1 - c + 2j` for some `j : ℕ`. -/
def InSupportM (c : ℕ) (f : R) : Prop :=
  ∀ e ∈ f.coeff.support, ∃ j : ℕ, e.2 = 1 - (c : ℤ) + 2 * (j : ℤ)

theorem InSupportM.zero (c : ℕ) : InSupportM c (0 : R) := by
  intro e he; simp at he

theorem InSupportM.add {c : ℕ} {f g : R} (hf : InSupportM c f) (hg : InSupportM c g) :
    InSupportM c (f + g) := by
  intro e he
  rcases Finset.mem_union.1 (Finsupp.support_add he) with h | h
  · exact hf e h
  · exact hg e h

theorem InSupportM.neg {c : ℕ} {f : R} (hf : InSupportM c f) : InSupportM c (-f) := by
  intro e he
  exact hf e (by simpa using he)

theorem InSupportM.sub {c : ℕ} {f g : R} (hf : InSupportM c f) (hg : InSupportM c g) :
    InSupportM c (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem InSupportM.of_single {c : ℕ} (d k : ℤ) (x : ℤ) (hk : ∃ j : ℕ, k = 1 - (c : ℤ) + 2 * (j : ℤ)) :
    InSupportM c (single (d, k) x) := by
  intro e he
  have : e = (d, k) := Finset.mem_singleton.1 (Finsupp.support_single_subset he)
  subst this; exact hk

/-- Coefficientwise characterisation: `f ∈ M_c` iff `[a^d z^k] f = 0` whenever `k` is not of the form
`1 - c + 2j`. -/
theorem inSupportM_iff {c : ℕ} {f : R} :
    InSupportM c f ↔ ∀ d k, (¬ ∃ j : ℕ, k = 1 - (c : ℤ) + 2 * (j : ℤ)) → coeffAt d k f = 0 := by
  constructor
  · intro h d k hk
    by_contra hne
    exact hk (h (d, k) (Finsupp.mem_support_iff.2 hne))
  · intro h e he
    by_contra hk
    exact Finsupp.mem_support_iff.1 he (h e.1 e.2 hk)

/-- Multiplication by an element of `ℤ[a^{±1}, z^2]` (all z-exponents even and nonnegative) preserves
`M_c` ("multiplication by any a unit preserves this subgroup", lp:core proof, sm-3:1123-1124). -/
theorem InSupportM.mul_left {c : ℕ} {f g : R} (hf : InSupportM c f)
    (hg : ∀ e ∈ g.coeff.support, ∃ j : ℕ, e.2 = 2 * (j : ℤ)) : InSupportM c (g * f) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset g f he)
  obtain ⟨j₁, hj₁⟩ := hg a ha
  obtain ⟨j₂, hj₂⟩ := hf b hb
  refine ⟨j₁ + j₂, ?_⟩
  rw [Prod.snd_add, hj₁, hj₂]; push_cast; ring

theorem InSupportM.single_a_mul {c : ℕ} {f : R} (hf : InSupportM c f) (d : ℤ) (x : ℤ) :
    InSupportM c (single (d, 0) x * f) := by
  refine hf.mul_left fun e he => ⟨0, ?_⟩
  have : e = (d, 0) := Finset.mem_singleton.1 (Finsupp.support_single_subset he)
  subst this; simp

theorem InSupportM.a_mul {c : ℕ} {f : R} (hf : InSupportM c f) : InSupportM c (R.a * f) :=
  hf.single_a_mul 1 1
theorem InSupportM.aInv_mul {c : ℕ} {f : R} (hf : InSupportM c f) : InSupportM c (R.aInv * f) :=
  hf.single_a_mul (-1) 1
theorem InSupportM.intCast_mul {c : ℕ} {f : R} (hf : InSupportM c f) (n : ℤ) :
    InSupportM c ((n : R) * f) := by
  have : (n : R) = single (0, 0) n := by rw [intCast_def, Prod.mk_zero_zero]; rfl
  rw [this]; exact hf.single_a_mul 0 n

/-- lp:self-support (sm-3:1125-1127: "`z M_{c+1} = z z^{-c} ℤ[a^{±1},z^2] = M_c`"), the inclusion
`z M_{c+1} ⊆ M_c`. -/
theorem InSupportM.z_mul {c : ℕ} {f : R} (hf : InSupportM (c + 1) f) : InSupportM c (R.z * f) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset R.z f he)
  have ha' : a = (0, 1) := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
  obtain ⟨j, hj⟩ := hf b hb
  refine ⟨j, ?_⟩
  rw [Prod.snd_add, ha', hj]; push_cast; ring

/-- lp:self-support, the reverse inclusion `M_c ⊆ z M_{c+1}`: `z^{-1} M_c ⊆ M_{c+1}`. -/
theorem InSupportM.zInv_mul {c : ℕ} {f : R} (hf : InSupportM c f) :
    InSupportM (c + 1) (R.zInv * f) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset R.zInv f he)
  have ha' : a = (0, -1) := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
  obtain ⟨j, hj⟩ := hf b hb
  refine ⟨j, ?_⟩
  rw [Prod.snd_add, ha', hj]; push_cast; ring

/-- `z M_{c+1} = M_c` (lp:self-support) as an equality of sets: `f ∈ M_c ↔ f = z g` with `g ∈ M_{c+1}`. -/
theorem inSupportM_iff_exists_z_mul {c : ℕ} {f : R} :
    InSupportM c f ↔ ∃ g : R, InSupportM (c + 1) g ∧ f = R.z * g := by
  constructor
  · intro hf
    refine ⟨R.zInv * f, hf.zInv_mul, ?_⟩
    rw [← mul_assoc, R.z_mul_zInv, one_mul]
  · rintro ⟨g, hg, rfl⟩
    exact hg.z_mul

/-- lp:mixed-support (sm-3:1129-1131: "`z M_{c-1} = z z^{2-c} ℤ[a^{±1},z^2] = z^2 M_c ⊆ M_c`"): for
`c ≥ 1`, `z M_{c-1} ⊆ M_c`. -/
theorem InSupportM.z_mul_of_pred {c : ℕ} (hc : 1 ≤ c) {f : R} (hf : InSupportM (c - 1) f) :
    InSupportM c (R.z * f) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset R.z f he)
  have ha' : a = (0, 1) := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
  obtain ⟨j, hj⟩ := hf b hb
  refine ⟨j + 1, ?_⟩
  rw [Prod.snd_add, ha', hj]
  have : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
  rw [this]; push_cast; ring

/-- `z^2 M_c ⊆ M_c`, the intermediate form of lp:mixed-support. -/
theorem InSupportM.z_mul_z_mul {c : ℕ} {f : R} (hf : InSupportM c f) :
    InSupportM c (R.z * (R.z * f)) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset R.z (R.z * f) he)
  have ha' : a = (0, 1) := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
  obtain ⟨a', ha'', b', hb', rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset R.z f hb)
  have ha''' : a' = (0, 1) := Finset.mem_singleton.1 (Finsupp.support_single_subset ha'')
  obtain ⟨j, hj⟩ := hf b' hb'
  refine ⟨j + 1, ?_⟩
  rw [Prod.snd_add, Prod.snd_add, ha', ha''', hj]; push_cast; ring

theorem InSupportM.one : InSupportM 1 (1 : R) := by
  rw [one_def, Prod.mk_zero_zero.symm]
  exact InSupportM.of_single 0 0 1 ⟨0, by simp⟩

/-- "The initialization belongs to `M_c`, since `δ^{c-1} = z^{1-c}(a-a^{-1})^{c-1}`" (lp:core proof,
sm-3:1120-1122): `δ^c ∈ M_{c+1}` for every `c : ℕ`. -/
theorem InSupportM.delta_pow (c : ℕ) : InSupportM (c + 1) (R.delta ^ c) := by
  induction c with
  | zero => simpa using InSupportM.one
  | succ n ih =>
    rw [pow_succ, mul_comm, R.delta, mul_assoc]
    have h1 : InSupportM (n + 1 + 1) (R.zInv * R.delta ^ n) := ih.zInv_mul
    have h2 : InSupportM (n + 1 + 1) (R.a * (R.zInv * R.delta ^ n) - R.aInv * (R.zInv * R.delta ^ n)) :=
      h1.a_mul.sub h1.aInv_mul
    rwa [← sub_mul] at h2

/-! ### The Gaussian detour: `i`, the inclusions `R ⊂ R_G`, `T ⊂ T_G` -/

/-- The formal `i` with `i² = -1` of lp:coefficient-transport's proof (sm-3:994: "Adjoin a formal i
with i² = -1"): the element `⟨0, 1⟩` of Mathlib's `GaussianInt = ℤ√(-1)`. -/
def gaussI : GaussianInt := ⟨0, 1⟩

theorem gaussI_mul_gaussI : gaussI * gaussI = -1 := by
  ext <;> simp [gaussI]

theorem neg_gaussI_mul_gaussI : -gaussI * gaussI = 1 := by
  rw [neg_mul, gaussI_mul_gaussI, neg_neg]

theorem gaussI_mul_neg_gaussI : gaussI * -gaussI = 1 := by
  rw [mul_neg, gaussI_mul_gaussI, neg_neg]

/-- `i` as a unit of `ℤ[i]`, with inverse `-i`. -/
def gaussIUnit : GaussianIntˣ := ⟨gaussI, -gaussI, gaussI_mul_neg_gaussI, neg_gaussI_mul_gaussI⟩

@[simp] theorem val_gaussIUnit : (gaussIUnit : GaussianInt) = gaussI := rfl
@[simp] theorem val_gaussIUnit_inv : ((gaussIUnit⁻¹ : GaussianIntˣ) : GaussianInt) = -gaussI := rfl

/-- The image of the unit `i` in any `ℤ[i]`-algebra `A` ("both fixing i", sm-3:1018). -/
noncomputable def iUnit (A : Type) [CommRing A] [Algebra GaussianInt A] : Aˣ :=
  Units.map (algebraMap GaussianInt A : GaussianInt →* A) gaussIUnit

theorem val_iUnit (A : Type) [CommRing A] [Algebra GaussianInt A] :
    ((iUnit A : Aˣ) : A) = algebraMap GaussianInt A gaussI := rfl

theorem val_iUnit_inv (A : Type) [CommRing A] [Algebra GaussianInt A] :
    (((iUnit A)⁻¹ : Aˣ) : A) = algebraMap GaussianInt A (-gaussI) := by
  rw [iUnit, ← map_inv, Units.coe_map, val_gaussIUnit_inv]; rfl

/-- The inclusion `R ⊂ R_G` ("the standard inclusion `R ↪ R_G`", lp:core proof, sm-3:1133-1134):
coefficientwise `ℤ → ℤ[i]`. -/
noncomputable def R.toRG : R →+* RG := mapRingHom (ℤ × ℤ) (Int.castRingHom GaussianInt)

/-- "The standard inclusion `R ↪ R_G` is injective (the Gaussian coefficient ring has the free
integer basis 1, i)" (lp:core proof, sm-3:1133-1135; lp:coefficient-transport proof, 996-999). -/
theorem R.toRG_injective : Function.Injective R.toRG :=
  AddMonoidAlgebra.map_injective (M := ℤ × ℤ) (Int.castRingHom GaussianInt).toAddMonoidHom
    Int.cast_injective

@[simp] theorem R.coeff_toRG (f : R) (e : ℤ × ℤ) : (R.toRG f).coeff e = (f.coeff e : GaussianInt) :=
  coeff_mapRingHom _ f e

@[simp] theorem R.toRG_single (e : ℤ × ℤ) (c : ℤ) : R.toRG (single e c) = single e (c : GaussianInt) :=
  mapRingHom_single _ e c

@[simp] theorem R.toRG_a : R.toRG R.a = RG.a := by simp [R.a, RG.a]
@[simp] theorem R.toRG_z : R.toRG R.z = RG.z := by simp [R.z, RG.z]
@[simp] theorem R.toRG_aInv : R.toRG R.aInv = RG.aInv := by simp [R.aInv, RG.aInv]
@[simp] theorem R.toRG_zInv : R.toRG R.zInv = RG.zInv := by simp [R.zInv, RG.zInv]

/-- The inclusion `T ⊂ T_G` (lp:coefficient-transport proof, sm-3:998: "the inclusions `T ⊂ T_G`,
`R ⊂ R_G` are injective"). -/
noncomputable def T.toTG : T →+* TG :=
  (mapRingHom (ℤ × ℤ) (Int.castRingHom GaussianInt) : Laurent₂ ℤ →+* Laurent₂ GaussianInt)

theorem T.toTG_injective : Function.Injective T.toTG :=
  AddMonoidAlgebra.map_injective (M := ℤ × ℤ) (Int.castRingHom GaussianInt).toAddMonoidHom
    Int.cast_injective

@[simp] theorem T.toTG_l : T.toTG T.l = TG.l := by
  show mapRingHom (ℤ × ℤ) (Int.castRingHom GaussianInt) (single (1, 0) 1) = _
  simp [TG.l]
@[simp] theorem T.toTG_m : T.toTG T.m = TG.m := by
  show mapRingHom (ℤ × ℤ) (Int.castRingHom GaussianInt) (single (0, 1) 1) = _
  simp [TG.m]
@[simp] theorem T.toTG_lInv : T.toTG T.lInv = TG.lInv := by
  show mapRingHom (ℤ × ℤ) (Int.castRingHom GaussianInt) (single (-1, 0) 1) = _
  simp [TG.lInv]
@[simp] theorem T.toTG_mInv : T.toTG T.mInv = TG.mInv := by
  show mapRingHom (ℤ × ℤ) (Int.castRingHom GaussianInt) (single (0, -1) 1) = _
  simp [TG.mInv]

/-! ### Coordinates over `ℤ[i]`: `T_G = T ⊕ i T` -/

/-- `Zsqrtd.re : ℤ[i] → ℤ` as an additive map. -/
def reHom : GaussianInt →+ ℤ where
  toFun := Zsqrtd.re
  map_zero' := rfl
  map_add' := Zsqrtd.re_add

/-- `Zsqrtd.im : ℤ[i] → ℤ` as an additive map. -/
def imHom : GaussianInt →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' := Zsqrtd.im_add

@[simp] theorem reHom_apply (c : GaussianInt) : reHom c = c.re := rfl
@[simp] theorem imHom_apply (c : GaussianInt) : imHom c = c.im := rfl

/-- Coefficientwise real part `Laurent₂ ℤ[i] →+ Laurent₂ ℤ`. -/
noncomputable def reMap : Laurent₂ GaussianInt →+ Laurent₂ ℤ where
  toFun := AddMonoidAlgebra.map reHom
  map_zero' := AddMonoidAlgebra.map_zero reHom
  map_add' := AddMonoidAlgebra.map_add reHom

/-- Coefficientwise imaginary part `Laurent₂ ℤ[i] →+ Laurent₂ ℤ`. -/
noncomputable def imMap : Laurent₂ GaussianInt →+ Laurent₂ ℤ where
  toFun := AddMonoidAlgebra.map imHom
  map_zero' := AddMonoidAlgebra.map_zero imHom
  map_add' := AddMonoidAlgebra.map_add imHom

@[simp] theorem coeff_reMap (g : Laurent₂ GaussianInt) (e : ℤ × ℤ) :
    (reMap g).coeff e = (g.coeff e).re := by
  simp [reMap, AddMonoidAlgebra.coeff_map]
@[simp] theorem coeff_imMap (g : Laurent₂ GaussianInt) (e : ℤ × ℤ) :
    (imMap g).coeff e = (g.coeff e).im := by
  simp [imMap, AddMonoidAlgebra.coeff_map]

theorem reMap_single (e : ℤ × ℤ) (c : GaussianInt) : reMap (single e c) = single e c.re :=
  AddMonoidAlgebra.map_single reHom c e
theorem imMap_single (e : ℤ × ℤ) (c : GaussianInt) : imMap (single e c) = single e c.im :=
  AddMonoidAlgebra.map_single imHom c e

theorem reMap_toRG (t : R) : reMap (R.toRG t) = t := by
  ext e; simp
theorem imMap_toRG (t : R) : imMap (R.toRG t) = 0 := by
  ext e; simp

/-- `z = z.re + i z.im` in `ℤ[i]`. -/
theorem gaussianInt_eq_re_add_gaussI_mul_im (c : GaussianInt) :
    c = (c.re : GaussianInt) + gaussI * (c.im : GaussianInt) := by
  ext <;> simp [gaussI]

/-- Every element of `Laurent₂ ℤ[i]` is `u + i v` with `u, v` integral. -/
theorem eq_toRG_reMap_add_gaussI_smul_toRG_imMap (g : Laurent₂ GaussianInt) :
    g = R.toRG (reMap g) + gaussI • R.toRG (imMap g) := by
  ext e : 2
  simp only [coeff_add, Finsupp.add_apply, coeff_smul_apply, R.coeff_toRG, coeff_reMap, coeff_imMap,
    smul_eq_mul]
  exact gaussianInt_eq_re_add_gaussI_mul_im _

theorem reMap_toRG_add_gaussI_smul_toRG (u v : Laurent₂ ℤ) :
    reMap (R.toRG u + gaussI • R.toRG v) = u := by
  ext e; simp [gaussI]
theorem imMap_toRG_add_gaussI_smul_toRG (u v : Laurent₂ ℤ) :
    imMap (R.toRG u + gaussI • R.toRG v) = v := by
  ext e; simp [gaussI]

/-- The real coordinate is linear over the integral subring: `re(t g) = t re(g)` for integral `t`
("since the three coefficients `l, l^{-1}, m` lie in `T`, comparing coordinates gives the source
skein for `U` and for `V` separately", sm-3:1004-1006). -/
theorem reMap_toRG_mul (t : Laurent₂ ℤ) (g : Laurent₂ GaussianInt) :
    reMap (R.toRG t * g) = t * reMap g := by
  suffices h : ∀ (e : ℤ × ℤ) (c : GaussianInt),
      reMap (R.toRG t * single e c) = t * reMap (single e c) by
    have h1 : reMap.comp (AddMonoidHom.mulLeft (R.toRG t)) = (AddMonoidHom.mulLeft t).comp reMap :=
      AddMonoidAlgebra.addMonoidHom_ext fun e c => h e c
    exact DFunLike.congr_fun h1 g
  intro e c
  have h2 : reMap.comp ((AddMonoidHom.mulRight (single e c)).comp R.toRG.toAddMonoidHom) =
      AddMonoidHom.mulRight (reMap (single e c)) := by
    refine AddMonoidAlgebra.addMonoidHom_ext fun e' n => ?_
    change reMap (R.toRG (single e' n) * single e c) = single e' n * reMap (single e c)
    rw [R.toRG_single, single_mul_single, reMap_single, reMap_single, single_mul_single]
    congr 1
    exact Zsqrtd.re_smul n c
  exact DFunLike.congr_fun h2 t

theorem imMap_toRG_mul (t : Laurent₂ ℤ) (g : Laurent₂ GaussianInt) :
    imMap (R.toRG t * g) = t * imMap g := by
  suffices h : ∀ (e : ℤ × ℤ) (c : GaussianInt),
      imMap (R.toRG t * single e c) = t * imMap (single e c) by
    have h1 : imMap.comp (AddMonoidHom.mulLeft (R.toRG t)) = (AddMonoidHom.mulLeft t).comp imMap :=
      AddMonoidAlgebra.addMonoidHom_ext fun e c => h e c
    exact DFunLike.congr_fun h1 g
  intro e c
  have h2 : imMap.comp ((AddMonoidHom.mulRight (single e c)).comp R.toRG.toAddMonoidHom) =
      AddMonoidHom.mulRight (imMap (single e c)) := by
    refine AddMonoidAlgebra.addMonoidHom_ext fun e' n => ?_
    change imMap (R.toRG (single e' n) * single e c) = single e' n * imMap (single e c)
    rw [R.toRG_single, single_mul_single, imMap_single, imMap_single, single_mul_single]
    congr 1
    exact Zsqrtd.im_smul n c
  exact DFunLike.congr_fun h2 t

/-- The coordinate `U` of `G = U + iV ∈ T_G` (lp:coefficient-transport proof, sm-3:996-998: "every
element of `T_G` is uniquely `u + iv` with `u, v ∈ T`"; 1002: "Write `G_D = U_D + iV_D` with
`U_D, V_D ∈ T`"): coefficientwise `Zsqrtd.re`. -/
noncomputable def TG.re : TG →+ T := reMap

/-- The coordinate `V` of `G = U + iV ∈ T_G` (sm-3:996-998, 1002): coefficientwise `Zsqrtd.im`. -/
noncomputable def TG.im : TG →+ T := imMap

theorem TG.re_toTG (t : T) : TG.re (T.toTG t) = t := reMap_toRG t
theorem TG.im_toTG (t : T) : TG.im (T.toTG t) = 0 := imMap_toRG t

/-- Existence of the decomposition `G = U + iV` (sm-3:996-998). -/
theorem TG.eq_toTG_re_add_gaussI_smul_toTG_im (g : TG) :
    g = T.toTG (TG.re g) + gaussI • T.toTG (TG.im g) :=
  eq_toRG_reMap_add_gaussI_smul_toRG_imMap g

/-- Uniqueness of the decomposition `G = U + iV` (sm-3:996-998, "uniquely"), real coordinate. -/
theorem TG.re_toTG_add_gaussI_smul_toTG (u v : T) : TG.re (T.toTG u + gaussI • T.toTG v) = u :=
  reMap_toRG_add_gaussI_smul_toRG u v

/-- Uniqueness of the decomposition `G = U + iV` (sm-3:996-998, "uniquely"), imaginary coordinate. -/
theorem TG.im_toTG_add_gaussI_smul_toTG (u v : T) : TG.im (T.toTG u + gaussI • T.toTG v) = v :=
  imMap_toRG_add_gaussI_smul_toRG u v

/-- `T`-linearity of the real coordinate (sm-3:1004-1006). -/
theorem TG.re_toTG_mul (t : T) (g : TG) : TG.re (T.toTG t * g) = t * TG.re g := reMap_toRG_mul t g
/-- `T`-linearity of the imaginary coordinate (sm-3:1004-1006). -/
theorem TG.im_toTG_mul (t : T) (g : TG) : TG.im (T.toTG t * g) = t * TG.im g := imMap_toRG_mul t g

theorem TG.re_l_mul (g : TG) : TG.re (TG.l * g) = T.l * TG.re g := by
  rw [← T.toTG_l, TG.re_toTG_mul]
theorem TG.re_lInv_mul (g : TG) : TG.re (TG.lInv * g) = T.lInv * TG.re g := by
  rw [← T.toTG_lInv, TG.re_toTG_mul]
theorem TG.re_m_mul (g : TG) : TG.re (TG.m * g) = T.m * TG.re g := by
  rw [← T.toTG_m, TG.re_toTG_mul]
theorem TG.im_l_mul (g : TG) : TG.im (TG.l * g) = T.l * TG.im g := by
  rw [← T.toTG_l, TG.im_toTG_mul]
theorem TG.im_lInv_mul (g : TG) : TG.im (TG.lInv * g) = T.lInv * TG.im g := by
  rw [← T.toTG_lInv, TG.im_toTG_mul]
theorem TG.im_m_mul (g : TG) : TG.im (TG.m * g) = T.m * TG.im g := by
  rw [← T.toTG_m, TG.im_toTG_mul]

/-- "comparing coordinates gives the source skein for `U` and for `V` separately" (sm-3:1004-1006):
the real coordinate of a source-skein relation in `T_G` is the source-skein relation in `T`. -/
theorem TG.re_skein {gp gm g0 : TG} (h : TG.l * gp + TG.lInv * gm + TG.m * g0 = 0) :
    T.l * TG.re gp + T.lInv * TG.re gm + T.m * TG.re g0 = 0 := by
  have := congrArg TG.re h
  rwa [map_add, map_add, map_zero, TG.re_l_mul, TG.re_lInv_mul, TG.re_m_mul] at this

theorem TG.im_skein {gp gm g0 : TG} (h : TG.l * gp + TG.lInv * gm + TG.m * g0 = 0) :
    T.l * TG.im gp + T.lInv * TG.im gm + T.m * TG.im g0 = 0 := by
  have := congrArg TG.im h
  rwa [map_add, map_add, map_zero, TG.im_l_mul, TG.im_lInv_mul, TG.im_m_mul] at this

theorem TG.re_one : TG.re 1 = 1 := by
  rw [← map_one T.toTG, TG.re_toTG]
theorem TG.im_one : TG.im 1 = 0 := by
  rw [← map_one T.toTG, TG.im_toTG]

/-! ### Substitution homomorphisms determined on the unit generators -/

/-- `(p, q) ↦ u^p v^q` as a monoid homomorphism `Multiplicative (ℤ × ℤ) →* A` for units `u v` of
`A`: the exponent law that makes "`l ↦ ia`, `m ↦ -iz` ... send the Laurent generators to units and
therefore define ring homomorphisms" (lp:ring-transports, sm-3:1013-1019). -/
noncomputable def unitPowers {A : Type} [CommRing A] (u v : Aˣ) : Multiplicative (ℤ × ℤ) →* A where
  toFun g := ((u ^ (Multiplicative.toAdd g).1 * v ^ (Multiplicative.toAdd g).2 : Aˣ) : A)
  map_one' := by simp
  map_mul' g h := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add, Units.val_mul]; ring

theorem unitPowers_apply {A : Type} [CommRing A] (u v : Aˣ) (p q : ℤ) :
    unitPowers u v (Multiplicative.ofAdd (p, q)) = ((u ^ p * v ^ q : Aˣ) : A) := rfl

/-- The `ℤ[i]`-algebra homomorphism `Laurent₂ ℤ[i] →ₐ[ℤ[i]] A` sending the first generator to the
unit `u` and the second to the unit `v` (`AddMonoidAlgebra.lift` of `unitPowers u v`). φ and ψ of
lp:ring-transports (sm-3:1013-1017) are instances. -/
noncomputable def substHom {A : Type} [CommRing A] [Algebra GaussianInt A] (u v : Aˣ) :
    Laurent₂ GaussianInt →ₐ[GaussianInt] A :=
  AddMonoidAlgebra.lift GaussianInt A (ℤ × ℤ) (unitPowers u v)

theorem substHom_single {A : Type} [CommRing A] [Algebra GaussianInt A] (u v : Aˣ) (p q : ℤ)
    (c : GaussianInt) :
    substHom u v (single (p, q) c) = c • ((u ^ p * v ^ q : Aˣ) : A) := by
  simp [substHom, lift_single, unitPowers_apply]

theorem substHom_single_one {A : Type} [CommRing A] [Algebra GaussianInt A] (u v : Aˣ) (p q : ℤ) :
    substHom u v (single (p, q) 1) = ((u ^ p * v ^ q : Aˣ) : A) := by
  rw [substHom_single, one_smul]

/-- Two `ℤ[i]`-algebra homomorphisms out of `Laurent₂ ℤ[i]` agreeing on the monomials
`single (p, q) 1` are equal. -/
theorem algHom_ext₂ {A : Type} [CommRing A] [Algebra GaussianInt A]
    {φ₁ φ₂ : Laurent₂ GaussianInt →ₐ[GaussianInt] A}
    (h : ∀ p q : ℤ, φ₁ (single (p, q) 1) = φ₂ (single (p, q) 1)) : φ₁ = φ₂ :=
  algHom_ext (fun e => h e.1 e.2) (Subsingleton.elim _ _)

/-- Composing a substitution with an algebra homomorphism `F` substitutes the images of the units. -/
theorem substHom_comp {A B : Type} [CommRing A] [Algebra GaussianInt A] [CommRing B]
    [Algebra GaussianInt B] (F : A →ₐ[GaussianInt] B) (u v : Aˣ) :
    F.comp (substHom u v) = substHom (Units.map (F : A →* B) u) (Units.map (F : A →* B) v) := by
  apply algHom_ext₂
  intro p q
  simp only [AlgHom.comp_apply, substHom_single_one]
  rw [← map_zpow (Units.map (F : A →* B)), ← map_zpow (Units.map (F : A →* B)), ← map_mul,
    Units.coe_map]
  rfl

/-- The substitution by the two monomial generators themselves is the identity. -/
theorem Laurent₂.substHom_monoUnit :
    substHom (Laurent₂.monoUnit (1, 0) : (Laurent₂ GaussianInt)ˣ) (Laurent₂.monoUnit (0, 1)) =
      AlgHom.id GaussianInt (Laurent₂ GaussianInt) := by
  apply algHom_ext₂
  intro p q
  rw [substHom_single_one, Laurent₂.monoUnit_zpow, Laurent₂.monoUnit_zpow, Laurent₂.monoUnit_mul,
    Laurent₂.val_monoUnit, AlgHom.id_apply]
  simp

theorem RG.substHom_aUnit_zUnit : substHom RG.aUnit RG.zUnit = AlgHom.id GaussianInt RG :=
  Laurent₂.substHom_monoUnit

theorem TG.substHom_lUnit_mUnit :
    (substHom TG.lUnit TG.mUnit : TG →ₐ[GaussianInt] TG) = AlgHom.id GaussianInt TG :=
  Laurent₂.substHom_monoUnit

/-! ### lp:ring-transports: `φ : T_G → R_G` and `ψ : R_G → T_G` -/

/-- `φ : T_G → R_G, l ↦ ia, m ↦ -iz`, "fixing i" (lp:ring-transports, sm-3:1013-1018; lp:gaussian,
1067-1069: "`φ(l) = ia, φ(m) = -iz`"). Here `-i = i⁻¹`, so `m ↦ i⁻¹ z`. -/
noncomputable def phi : TG →ₐ[GaussianInt] RG :=
  substHom (iUnit RG * RG.aUnit) ((iUnit RG)⁻¹ * RG.zUnit)

/-- `ψ : R_G → T_G, a ↦ -il, z ↦ im`, "fixing i" (lp:ring-transports, sm-3:1015-1018). Here
`-i = i⁻¹`, so `a ↦ i⁻¹ l`. -/
noncomputable def psi : RG →ₐ[GaussianInt] TG :=
  substHom ((iUnit TG)⁻¹ * TG.lUnit) (iUnit TG * TG.mUnit)

theorem RG.algebraMap_apply (c : GaussianInt) : algebraMap GaussianInt RG c = single 0 c := by
  simp

theorem TG.algebraMap_apply (c : GaussianInt) :
    algebraMap GaussianInt TG c = (single 0 c : Laurent₂ GaussianInt) := by
  show algebraMap GaussianInt (Laurent₂ GaussianInt) c = _
  simp

/-- `φ(l) = i a` (sm-3:1013, 1067). -/
theorem phi_l : phi TG.l = single (1, 0) gaussI := by
  show substHom (iUnit RG * RG.aUnit) ((iUnit RG)⁻¹ * RG.zUnit) (single (1, 0) 1) = _
  rw [substHom_single_one, zpow_one, zpow_zero, mul_one, Units.val_mul, val_iUnit, RG.val_aUnit,
    RG.algebraMap_apply, RG.a, single_mul_single]
  simp

theorem phi_l' : phi TG.l = gaussI • RG.a := by
  rw [phi_l, RG.a, smul_single, smul_eq_mul, mul_one]

/-- `φ(m) = -i z` (sm-3:1013, 1067). -/
theorem phi_m : phi TG.m = single (0, 1) (-gaussI) := by
  show substHom (iUnit RG * RG.aUnit) ((iUnit RG)⁻¹ * RG.zUnit) (single (0, 1) 1) = _
  rw [substHom_single_one, zpow_one, zpow_zero, one_mul, Units.val_mul, val_iUnit_inv, RG.val_zUnit,
    RG.algebraMap_apply, RG.z, single_mul_single]
  simp

theorem phi_m' : phi TG.m = -(gaussI • RG.z) := by
  rw [phi_m, RG.z, smul_single, smul_eq_mul, mul_one, single_neg]

/-- `φ(l^{-1}) = (ia)^{-1} = -i a^{-1}` (lp:core proof, sm-3:1071: "`(ia)^{-1} = -ia^{-1}`"). -/
theorem phi_lInv : phi TG.lInv = single (-1, 0) (-gaussI) := by
  show substHom (iUnit RG * RG.aUnit) ((iUnit RG)⁻¹ * RG.zUnit) (single (-1, 0) 1) = _
  rw [substHom_single_one, zpow_neg_one, zpow_zero, mul_one, mul_inv, Units.val_mul, val_iUnit_inv,
    RG.val_aUnit_inv, RG.algebraMap_apply, RG.aInv, single_mul_single]
  simp

/-- `φ(m^{-1}) = (-iz)^{-1} = i z^{-1}`. -/
theorem phi_mInv : phi TG.mInv = single (0, -1) gaussI := by
  show substHom (iUnit RG * RG.aUnit) ((iUnit RG)⁻¹ * RG.zUnit) (single (0, -1) 1) = _
  rw [substHom_single_one, zpow_neg_one, zpow_zero, one_mul, mul_inv, inv_inv, Units.val_mul,
    val_iUnit, RG.val_zUnit_inv, RG.algebraMap_apply, RG.zInv, single_mul_single]
  simp

/-- `ψ(a) = -i l` (sm-3:1015). -/
theorem psi_a : psi RG.a = (single (1, 0) (-gaussI) : Laurent₂ GaussianInt) := by
  show substHom ((iUnit TG)⁻¹ * TG.lUnit) (iUnit TG * TG.mUnit) (single (1, 0) 1) = _
  rw [substHom_single_one, zpow_one, zpow_zero, mul_one, Units.val_mul, val_iUnit_inv, TG.val_lUnit,
    TG.algebraMap_apply]
  exact (TG.single_mul_single 0 (1, 0) (-gaussI) 1).trans (by rw [zero_add, mul_one])

/-- `ψ(z) = i m` (sm-3:1015). -/
theorem psi_z : psi RG.z = (single (0, 1) gaussI : Laurent₂ GaussianInt) := by
  show substHom ((iUnit TG)⁻¹ * TG.lUnit) (iUnit TG * TG.mUnit) (single (0, 1) 1) = _
  rw [substHom_single_one, zpow_one, zpow_zero, one_mul, Units.val_mul, val_iUnit, TG.val_mUnit,
    TG.algebraMap_apply]
  exact (TG.single_mul_single 0 (0, 1) gaussI 1).trans (by rw [zero_add, mul_one])

/-- `ψ(a^{-1}) = (-il)^{-1} = i l^{-1}` (lp:coefficient-transport proof, sm-3:1027-1028:
"`ψ(a^{-1}) = (-il)^{-1} = il^{-1}`"). -/
theorem psi_aInv : psi RG.aInv = (single (-1, 0) gaussI : Laurent₂ GaussianInt) := by
  show substHom ((iUnit TG)⁻¹ * TG.lUnit) (iUnit TG * TG.mUnit) (single (-1, 0) 1) = _
  rw [substHom_single_one, zpow_neg_one, zpow_zero, mul_one, mul_inv, inv_inv, Units.val_mul,
    val_iUnit, TG.val_lUnit_inv, TG.algebraMap_apply]
  exact (TG.single_mul_single 0 (-1, 0) gaussI 1).trans (by rw [zero_add, mul_one])

/-- `ψ(z^{-1}) = (im)^{-1} = -i m^{-1}`. -/
theorem psi_zInv : psi RG.zInv = (single (0, -1) (-gaussI) : Laurent₂ GaussianInt) := by
  show substHom ((iUnit TG)⁻¹ * TG.lUnit) (iUnit TG * TG.mUnit) (single (0, -1) 1) = _
  rw [substHom_single_one, zpow_neg_one, zpow_zero, one_mul, mul_inv, Units.val_mul, val_iUnit_inv,
    TG.val_mUnit_inv, TG.algebraMap_apply]
  exact (TG.single_mul_single 0 (0, -1) (-gaussI) 1).trans (by rw [zero_add, mul_one])

/-- `φ(ψ(a)) = -i(ia) = a` at the level of units (sm-3:1021). -/
theorem phi_mapUnit_a : Units.map (phi : TG →* RG) ((iUnit TG)⁻¹ * TG.lUnit) = RG.aUnit := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, val_iUnit_inv, map_mul, AlgHom.commutes,
    TG.val_lUnit, phi_l, RG.val_aUnit, RG.algebraMap_apply, RG.a, single_mul_single,
    neg_gaussI_mul_gaussI]
  simp

/-- `φ(ψ(z)) = i(-iz) = z` at the level of units (sm-3:1022). -/
theorem phi_mapUnit_z : Units.map (phi : TG →* RG) (iUnit TG * TG.mUnit) = RG.zUnit := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, val_iUnit, map_mul, AlgHom.commutes,
    TG.val_mUnit, phi_m, RG.val_zUnit, RG.algebraMap_apply, RG.z, single_mul_single,
    gaussI_mul_neg_gaussI]
  simp

/-- `ψ(φ(l)) = i(-il) = l` at the level of units (sm-3:1019). -/
theorem psi_mapUnit_l : Units.map (psi : RG →* TG) (iUnit RG * RG.aUnit) = TG.lUnit := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, val_iUnit, map_mul, AlgHom.commutes,
    RG.val_aUnit, psi_a, TG.val_lUnit, TG.algebraMap_apply]
  exact (TG.single_mul_single 0 (1, 0) gaussI (-gaussI)).trans
    (by rw [zero_add, gaussI_mul_neg_gaussI]; rfl)

/-- `ψ(φ(m)) = -i(im) = m` at the level of units (sm-3:1020). -/
theorem psi_mapUnit_m : Units.map (psi : RG →* TG) ((iUnit RG)⁻¹ * RG.zUnit) = TG.mUnit := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, val_iUnit_inv, map_mul, AlgHom.commutes,
    RG.val_zUnit, psi_z, TG.val_mUnit, TG.algebraMap_apply]
  exact (TG.single_mul_single 0 (0, 1) (-gaussI) gaussI).trans
    (by rw [zero_add, neg_gaussI_mul_gaussI]; rfl)

/-- "φ and ψ are mutually inverse isomorphisms" (sm-3:1023-1024), first half: `φ ∘ ψ = id_{R_G}`. -/
theorem phi_comp_psi : phi.comp psi = AlgHom.id GaussianInt RG := by
  rw [psi, substHom_comp, phi_mapUnit_a, phi_mapUnit_z]
  exact RG.substHom_aUnit_zUnit

/-- "φ and ψ are mutually inverse isomorphisms" (sm-3:1023-1024), second half: `ψ ∘ φ = id_{T_G}`. -/
theorem psi_comp_phi : psi.comp phi = AlgHom.id GaussianInt TG := by
  have h := substHom_comp psi (iUnit RG * RG.aUnit) ((iUnit RG)⁻¹ * RG.zUnit)
  rw [psi_mapUnit_l, psi_mapUnit_m] at h
  exact h.trans TG.substHom_lUnit_mUnit

theorem phi_psi_apply (f : RG) : phi (psi f) = f := AlgHom.congr_fun phi_comp_psi f
theorem psi_phi_apply (g : TG) : psi (phi g) = g := AlgHom.congr_fun psi_comp_phi g

theorem phi_injective : Function.Injective phi :=
  Function.LeftInverse.injective psi_phi_apply
theorem psi_injective : Function.Injective psi :=
  Function.LeftInverse.injective phi_psi_apply
theorem phi_surjective : Function.Surjective phi :=
  Function.RightInverse.surjective phi_psi_apply
theorem psi_surjective : Function.Surjective psi :=
  Function.RightInverse.surjective psi_phi_apply

/-- φ as a `ℤ[i]`-algebra isomorphism `T_G ≃ R_G` with inverse ψ (sm-3:1023-1024). -/
noncomputable def phiEquiv : TG ≃ₐ[GaussianInt] RG :=
  AlgEquiv.ofAlgHom phi psi phi_comp_psi psi_comp_phi

@[simp] theorem phiEquiv_apply (g : TG) : phiEquiv g = phi g := rfl
@[simp] theorem phiEquiv_symm_apply (f : RG) : phiEquiv.symm f = psi f := rfl

/-- Sanity: the source skein coefficients `l, l^{-1}, m` are carried by φ to `ia, -ia^{-1}, -iz`
(lp:gaussian-skein, sm-3:1073-1075: "`iaP_+^G - ia^{-1}P_-^G - izP_0^G = 0`"), so that after
multiplying by `-i` one obtains `a P_+ - a^{-1} P_- - z P_0` (sm-3:1077). -/
theorem neg_gaussI_smul_phi_l : (-gaussI) • phi TG.l = RG.a := by
  rw [phi_l, smul_single, smul_eq_mul, neg_gaussI_mul_gaussI, RG.a]

theorem neg_gaussI_smul_phi_lInv : (-gaussI) • phi TG.lInv = -RG.aInv := by
  rw [phi_lInv, smul_single, smul_eq_mul, neg_mul_neg, gaussI_mul_gaussI, RG.aInv, single_neg]

theorem neg_gaussI_smul_phi_m : (-gaussI) • phi TG.m = -RG.z := by
  rw [phi_m, smul_single, smul_eq_mul, neg_mul_neg, gaussI_mul_gaussI, RG.z, single_neg]

/-- Sanity: `φ` carries the numerator `l + l^{-1}` of μ to `i(a - a^{-1})` (lp:core proof,
sm-3:1078-1079: "the numerator `l+l^{-1}` maps to `i(a-a^{-1})`"). -/
theorem phi_l_add_lInv : phi (TG.l + TG.lInv) = gaussI • (RG.a - RG.aInv) := by
  rw [map_add, phi_l, phi_lInv, RG.a, RG.aInv, smul_sub, smul_single, smul_single, smul_eq_mul,
    mul_one, single_neg, sub_eq_add_neg]

/-! ### The `ℚ(a)` specialization of lp:core (sm-3:1145-1160) -/

section specialization

open Polynomial in
theorem ratFuncX_sub_inv_ne_zero : (RatFunc.X : RatFunc ℚ) - RatFunc.X⁻¹ ≠ 0 := by
  intro h
  have hX : (RatFunc.X : RatFunc ℚ) = RatFunc.X⁻¹ := sub_eq_zero.1 h
  have h1 : (RatFunc.X : RatFunc ℚ) * RatFunc.X = 1 := by
    calc (RatFunc.X : RatFunc ℚ) * RatFunc.X = RatFunc.X * RatFunc.X⁻¹ := by
          conv_lhs => rw [hX]
          rw [← hX]
      _ = 1 := mul_inv_cancel₀ RatFunc.X_ne_zero
  have h2 : algebraMap ℚ[X] (RatFunc ℚ) (X * X) = algebraMap ℚ[X] (RatFunc ℚ) 1 := by
    rw [map_mul, RatFunc.algebraMap_X, map_one, h1]
  have h3 : (X * X : ℚ[X]) = 1 := RatFunc.algebraMap_injective ℚ h2
  have h4 := congrArg (fun p : ℚ[X] => p.coeff 0) h3
  simp at h4

/-- The indeterminate `a` of `ℚ(a)` as a unit (Mathlib `RatFunc.X`). -/
noncomputable def ratA : (RatFunc ℚ)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero
/-- `a - a^{-1}`, "a nonzero rational function" (sm-3:1147), as a unit of `ℚ(a)`. -/
noncomputable def ratZ : (RatFunc ℚ)ˣ := Units.mk0 (RatFunc.X - RatFunc.X⁻¹) ratFuncX_sub_inv_ne_zero

@[simp] theorem val_ratA : (ratA : RatFunc ℚ) = RatFunc.X := rfl
@[simp] theorem val_ratZ : (ratZ : RatFunc ℚ) = RatFunc.X - RatFunc.X⁻¹ := rfl

/-- "map `R` to `ℚ(a)` by fixing the indeterminate `a` and sending `z` to `a - a^{-1}`. This target
is a field, and `a - a^{-1}` is a nonzero rational function, so the Laurent specialization is
well-defined" (lp:core proof, sm-3:1145-1147). -/
noncomputable def specQ : R →ₐ[ℤ] RatFunc ℚ :=
  AddMonoidAlgebra.lift ℤ (RatFunc ℚ) (ℤ × ℤ) (unitPowers ratA ratZ)

theorem specQ_single (p q : ℤ) (c : ℤ) :
    specQ (single (p, q) c) = (c : RatFunc ℚ) * ((ratA ^ p * ratZ ^ q : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  rw [specQ, lift_single, Algebra.smul_def, eq_intCast]; rfl

@[simp] theorem specQ_a : specQ R.a = RatFunc.X := by
  rw [R.a, specQ_single, Int.cast_one, one_mul, zpow_one, zpow_zero, mul_one, val_ratA]
@[simp] theorem specQ_z : specQ R.z = RatFunc.X - RatFunc.X⁻¹ := by
  rw [R.z, specQ_single, Int.cast_one, one_mul, zpow_one, zpow_zero, one_mul, val_ratZ]
@[simp] theorem specQ_aInv : specQ R.aInv = RatFunc.X⁻¹ := by
  rw [R.aInv, specQ_single, Int.cast_one, one_mul, zpow_neg_one, zpow_zero, mul_one,
    Units.val_inv_eq_inv_val, val_ratA]
@[simp] theorem specQ_zInv : specQ R.zInv = (RatFunc.X - RatFunc.X⁻¹)⁻¹ := by
  rw [R.zInv, specQ_single, Int.cast_one, one_mul, zpow_neg_one, zpow_zero, one_mul,
    Units.val_inv_eq_inv_val, val_ratZ]

/-- "The initialized `δ` maps to `1`" (sm-3:1148). -/
theorem specQ_delta : specQ R.delta = 1 := by
  rw [R.delta, map_mul, map_sub, specQ_a, specQ_aInv, specQ_zInv]
  exact mul_inv_cancel₀ ratFuncX_sub_inv_ne_zero

/-- lp:nonzero-positive (sm-3:1153-1155): "`a^{-2} + a^{-1}(a - a^{-1}) = a^{-2} + 1 - a^{-2} = 1`",
the specialization of the positive-crossing recurrence coefficients (lp:positive, 1104-1106). -/
theorem specQ_positive_identity : specQ (R.aInv * R.aInv + R.aInv * R.z) = 1 := by
  rw [map_add, map_mul, map_mul, specQ_aInv, specQ_z, mul_sub,
    inv_mul_cancel₀ (RatFunc.X_ne_zero : (RatFunc.X : RatFunc ℚ) ≠ 0)]
  ring

/-- lp:nonzero-negative (sm-3:1158-1160): "`a^2 - a(a - a^{-1}) = a^2 - a^2 + 1 = 1`", the
specialization of the negative-crossing recurrence coefficients (lp:negative, 1111-1113). -/
theorem specQ_negative_identity : specQ (R.a * R.a - R.a * R.z) = 1 := by
  rw [map_sub, map_mul, map_mul, specQ_a, specQ_z, mul_sub,
    mul_inv_cancel₀ (RatFunc.X_ne_zero : (RatFunc.X : RatFunc ℚ) ≠ 0)]
  ring

/-- Sanity: `specQ` of an integer constant is that integer. -/
theorem specQ_intCast (n : ℤ) : specQ (n : R) = n := map_intCast specQ n

end specialization

end SM.Link

