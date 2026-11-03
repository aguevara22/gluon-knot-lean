import HOMFLYDiskTranslatedRay

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

/-- The actual affine coordinates of a nondegenerate triangle, with its explicit
inverse. This chart will supply interior approximation in region uniqueness. -/
def triangleChart (T : TrianglePatch) : PlanarPoint ℝ ≃ₜ PlanarPoint ℝ where
  toFun p := T.a + p.1 • (T.b-T.a) + p.2 • (T.c-T.a)
  invFun z := (planarDet (z-T.a) (T.c-T.a) / planarDet (T.b-T.a) (T.c-T.a),
    planarDet (T.b-T.a) (z-T.a) / planarDet (T.b-T.a) (T.c-T.a))
  left_inv p := by
    have hd : (T.b.1-T.a.1)*(T.c.2-T.a.2)-(T.b.2-T.a.2)*(T.c.1-T.a.1) ≠ 0 := T.nondegenerate
    ext <;> dsimp [planarDet] <;> field_simp [hd] <;> ring
  right_inv z := by
    have hd : (T.b.1-T.a.1)*(T.c.2-T.a.2)-(T.b.2-T.a.2)*(T.c.1-T.a.1) ≠ 0 := T.nondegenerate
    ext <;> dsimp [planarDet] <;> field_simp [hd] <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by unfold planarDet; fun_prop

theorem triangle_mem_of_barycentric (a b c : PlanarPoint ℝ) (α β γ : ℝ)
    (hα : 0≤α) (hβ : 0≤β) (hγ : 0≤γ) (hs : α+β+γ=1) :
    α • a+β • b+γ • c ∈ convexHull ℝ {a,b,c} := by
  have hh := (convex_convexHull ℝ ({a,b,c} : Set (PlanarPoint ℝ))).sum_mem
    (t := Finset.univ) (w := ![α,β,γ]) (z := ![a,b,c])
    (by intro i _; fin_cases i; exact hα; exact hβ; exact hγ)
    (by simpa [Fin.sum_univ_three] using hs)
    (by intro i _; fin_cases i <;> apply subset_convexHull ℝ _ <;> simp)
  simpa [Fin.sum_univ_three] using hh

namespace TrianglePatch

theorem fill_interior_nonempty (T : TrianglePatch) : (interior T.fill).Nonempty := by
  let U : Set (PlanarPoint ℝ) := {p | 0<p.1 ∧ 0<p.2 ∧ p.1+p.2<1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hUin : triangleChart T '' U ⊆ T.fill := by
    rintro z ⟨p,hp,rfl⟩
    have hh := triangle_mem_of_barycentric T.a T.b T.c (1-p.1-p.2) p.1 p.2
      (by dsimp [U] at hp; linarith [hp.2.2]) (le_of_lt hp.1) (le_of_lt hp.2.1) (by ring)
    convert hh using 1 <;> ext <;> dsimp [triangleChart] <;> ring
  have hopen : IsOpen (triangleChart T '' U) := (triangleChart T).isOpenMap U hU
  have hquarter : ((1/4 : ℝ),(1/4 : ℝ)) ∈ U := by norm_num [U]
  exact ⟨triangleChart T ((1/4 : ℝ),(1/4 : ℝ)),
    (hopen.subset_interior_iff.2 hUin) ⟨_,hquarter,rfl⟩⟩

theorem fill_closure_interior (T : TrianglePatch) : closure (interior T.fill) = T.fill := by
  have he := (convex_convexHull ℝ ({T.a,T.b,T.c} : Set (PlanarPoint ℝ))).closure_interior_eq_closure_of_nonempty_interior
    T.fill_interior_nonempty
  exact he.trans T.fill_isCompact.isClosed.closure_eq

end TrianglePatch
end
end DirectGLSSW.HOMFLY




