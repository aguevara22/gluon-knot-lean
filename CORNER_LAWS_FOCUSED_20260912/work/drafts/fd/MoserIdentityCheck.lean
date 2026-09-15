import Mathlib.Tactic

/-! Decisive check for row 84 (fd:transverse-neighborhood): in the chart `F` of sm-3:2414-2416
the forms are EXACT polynomials, `β = (1+g) dθ − 2v du`, `α₀ = dθ + u dv − v du`, so the Moser
field `V_t` and multiplier `μ_t` are explicit rational functions and the Moser identity
`ν + ι_{V_t} dα_t = μ_t α_t` (sm-3:2464-2466) is a rational identity, checked here by
`field_simp; ring`.  Coordinates `(θ, u, v)`; `g` is the function `g = (c u y' − c v x' − c c' u v)/a`
and `gu, gv` its `u`-, `v`-derivatives (its `θ`-derivative drops out of `dα_t`). -/

namespace MoserCheck

noncomputable section

/-- `α_t = (1 + t g) dθ − (1+t) v du + (1−t) u dv` on `w = (wθ, wu, wv)`. -/
def alphaT (u v t g wθ wu wv : ℝ) : ℝ := (1 + t * g) * wθ - (1 + t) * v * wu + (1 - t) * u * wv
/-- `ν = β − α₀ = g dθ − v du − u dv`. -/
def nu (u v g wθ wu wv : ℝ) : ℝ := g * wθ - v * wu - u * wv
/-- `dα_t = 2 du∧dv + t (g_u du + g_v dv) ∧ dθ`. -/
def dalphaT (t gu gv xθ xu xv yθ yu yv : ℝ) : ℝ :=
  2 * (xu * yv - xv * yu) + t * gu * (xu * yθ - xθ * yu) + t * gv * (xv * yθ - xθ * yv)

/-- `P = α_t(∂_θ) = 1 + t g` and `N = P · D_t` (closed forms). -/
def P (t g : ℝ) : ℝ := 1 + t * g
def N (u v t g gu gv : ℝ) : ℝ := 2 * P t g - t * gu * ((1 - t) * u) - t * gv * ((1 + t) * v)

/-- `X₁ = ∂_u − (α_t(∂_u)/α_t(∂_θ)) ∂_θ`, `X₂ = ∂_v − (α_t(∂_v)/α_t(∂_θ)) ∂_θ`: θ-components. -/
def X1θ (v t g : ℝ) : ℝ := (1 + t) * v / P t g
def X2θ (u t g : ℝ) : ℝ := -((1 - t) * u) / P t g
/-- `D_t = dα_t(X₁, X₂)` as printed. -/
def D (u v t g gu gv : ℝ) : ℝ := dalphaT t gu gv (X1θ v t g) 1 0 (X2θ u t g) 0 1

theorem D_eq (u v t g gu gv : ℝ) (hP : P t g ≠ 0) : D u v t g gu gv = N u v t g gu gv / P t g := by
  unfold D dalphaT X1θ X2θ N
  field_simp
  ring

/-- `V_t = (ν(X₁) X₂ − ν(X₂) X₁)/D_t` as printed (sm-3:2446), components. -/
def Vθ (u v t g gu gv : ℝ) : ℝ :=
  (nu u v g (X1θ v t g) 1 0 * X2θ u t g - nu u v g (X2θ u t g) 0 1 * X1θ v t g) / D u v t g gu gv
def Vu (u v t g gu gv : ℝ) : ℝ := (- nu u v g (X2θ u t g) 0 1) / D u v t g gu gv
def Vv (u v t g gu gv : ℝ) : ℝ := (nu u v g (X1θ v t g) 1 0) / D u v t g gu gv

/-- Closed forms: `V_t = (2uv/N, u(1+g)/N, v(g−1)/N)`. -/
theorem Vu_eq (u v t g gu gv : ℝ) (hP : P t g ≠ 0) (hN : N u v t g gu gv ≠ 0) :
    Vu u v t g gu gv = u * (1 + g) / N u v t g gu gv := by
  unfold Vu; rw [D_eq u v t g gu gv hP]; unfold nu X2θ; field_simp; unfold P; ring
theorem Vv_eq (u v t g gu gv : ℝ) (hP : P t g ≠ 0) (hN : N u v t g gu gv ≠ 0) :
    Vv u v t g gu gv = v * (g - 1) / N u v t g gu gv := by
  unfold Vv; rw [D_eq u v t g gu gv hP]; unfold nu X1θ; field_simp; unfold P; ring
theorem Vθ_eq (u v t g gu gv : ℝ) (hP : P t g ≠ 0) (hN : N u v t g gu gv ≠ 0) :
    Vθ u v t g gu gv = 2 * u * v / N u v t g gu gv := by
  unfold Vθ; rw [D_eq u v t g gu gv hP]; unfold nu X1θ X2θ; field_simp; unfold P; ring

/-- `μ_t = (ν + ι_V dα_t)(∂_θ) / α_t(∂_θ)` (sm-3:2464-2465). -/
def mu (u v t g gu gv : ℝ) : ℝ :=
  (nu u v g 1 0 0 + dalphaT t gu gv (Vθ u v t g gu gv) (Vu u v t g gu gv) (Vv u v t g gu gv) 1 0 0)
    / P t g

/-- `α_t(V_t) = 0` (sm-3:2466 "since α_t(V_t) = 0"). -/
theorem alphaT_V (u v t g gu gv : ℝ) (hP : P t g ≠ 0) (hN : N u v t g gu gv ≠ 0) :
    alphaT u v t g (Vθ u v t g gu gv) (Vu u v t g gu gv) (Vv u v t g gu gv) = 0 := by
  rw [Vθ_eq u v t g gu gv hP hN, Vu_eq u v t g gu gv hP hN, Vv_eq u v t g gu gv hP hN]
  unfold alphaT
  have hP' : (1 + t * g) = P t g := rfl
  rw [hP']
  generalize hPP : P t g = PP at hP ⊢
  generalize hNN : N u v t g gu gv = NN at hN ⊢
  field_simp
  subst hPP hNN
  unfold N P
  ring

/-- The Moser identity `ν(w) + dα_t(V_t, w) = μ_t α_t(w)` for every vector `w` (sm-3:2464-2466). -/
theorem moser_identity (u v t g gu gv : ℝ) (hP : P t g ≠ 0) (hN : N u v t g gu gv ≠ 0)
    (wθ wu wv : ℝ) :
    nu u v g wθ wu wv
      + dalphaT t gu gv (Vθ u v t g gu gv) (Vu u v t g gu gv) (Vv u v t g gu gv) wθ wu wv
      = mu u v t g gu gv * alphaT u v t g wθ wu wv := by
  unfold mu
  rw [Vθ_eq u v t g gu gv hP hN, Vu_eq u v t g gu gv hP hN, Vv_eq u v t g gu gv hP hN]
  unfold alphaT nu dalphaT
  have hP' : (1 + t * g) = P t g := rfl
  rw [hP']
  generalize hPP : P t g = PP at hP ⊢
  generalize hNN : N u v t g gu gv = NN at hN ⊢
  field_simp
  subst hPP hNN
  unfold N P
  ring

/-- `D_t = 2` on the core `u = v = 0`. -/
theorem D_core (t g gu gv : ℝ) : D 0 0 t g gu gv = 2 := by
  unfold D dalphaT X1θ X2θ; simp

/-- `V_t` vanishes on the core. -/
theorem V_core (t g gu gv : ℝ) :
    Vθ 0 0 t g gu gv = 0 ∧ Vu 0 0 t g gu gv = 0 ∧ Vv 0 0 t g gu gv = 0 := by
  unfold Vθ Vu Vv nu X1θ X2θ; simp

end

end MoserCheck
