# -*- coding: utf-8 -*-
"""The W3C assembler's connections (exact, unique string replacements applied by assemble_W3C.py).
(2) the four Wave-3 skeleton sub-leaves that are FALSE as stated (kink: `BigonData.hk : 5 ≤ k`) are RESTATED with
unit G's non-kink hypothesis and proved by the units' corrected forms; the consumers `w3bi_bigon_of_site_model`,
`w3bi_bigon_of_site`, `w3bi_bigon_pair_of` carry the non-kink condition, supplied by unit SITE's `w3cs_not_kink_site`.
BIGON's duplicate consumer variants `w3cz_bigon_of_site_model_of_not_kink` / `w3cz_bigon_of_site_of_not_kink` are
removed (their bodies ARE the new `w3bi_` bodies)."""
CONNECT = []

# ---- (2a) w3g_bigonData_smooth_arcST : statement + body
CONNECT.append(("""    (clear_vertex : ∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- (G) everything but `hk5 : 5 ≤ k` is proved in `w3bg_bigonData_smooth_arcST_of_five`; `hk5` is NOT derivable
  -- from the hypotheses above (kink counterexample, see the docstring there) — rule 3, reported.
  exact w3bg_bigonData_smooth_arcST_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (by sorry)
""", """    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- (W3C assembler) STATEMENT RESTATED (W3C_ASSEMBLY_REPORT.md §2): the Wave-3 skeleton form (with `clear_vertex`,
  -- without `hkink`) is false on a kink (`BigonData.hk : 5 ≤ k`, W3B_G_REPORT.md §2); this is unit G's proved
  -- corrected form `w3bg_bigonData_smooth_arcST_of_not_kink`, which does not consume `clear_vertex`.
  exact w3bg_bigonData_smooth_arcST_of_not_kink D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀
    hy₀ hz₀ hkink
""", "w3g_bigonData_smooth_arcST restated (non-kink hypothesis) and closed by w3bg_…_of_not_kink"))

# ---- (2b) w3g_bigonData_smooth_arcTS
CONNECT.append(("""    (clear_vertex : ∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- (G) as for `arcST`: reduced to the missing `hk5 : 5 ≤ k` on the component of `cutStartT` (rule 3).
  exact w3bg_bigonData_smooth_arcTS_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (by sorry)
""", """    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- (W3C assembler) STATEMENT RESTATED as for `arcST` (W3C_ASSEMBLY_REPORT.md §2): unit G's proved corrected form
  -- `w3bg_bigonData_smooth_arcTS_of_not_kink` (non-kink hypothesis on the component of `cutStartT`).
  exact w3bg_bigonData_smooth_arcTS_of_not_kink D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀
    hy₀ hz₀ hkink
""", "w3g_bigonData_smooth_arcTS restated (non-kink hypothesis) and closed by w3bg_…_of_not_kink"))

# ---- (2c) w3bi_bigonData_smooth_arcST_switch_z
CONNECT.append(("""    (clear_vertex : ∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- (BIGON) everything but `hk5 : 5 ≤ k` is proved in `w3cz_bigonData_smooth_arcST_switch_z_of_five`; `hk5` is NOT
  -- derivable from the hypotheses above (unit G's kink counterexample; the shadow does not see the switch) — rule 3.
  exact w3cz_bigonData_smooth_arcST_switch_z_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀
    hy₀ hz₀ (by sorry)
""", """    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- (W3C assembler) STATEMENT RESTATED (W3C_ASSEMBLY_REPORT.md §2): the Wave-3b form is false on a kink for unit G's
  -- reason (the shadow does not see the switch; W3C_BIGON_REPORT.md §3); unit BIGON's proved corrected form.
  exact w3cz_bigonData_smooth_arcST_switch_z_of_not_kink D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover
    y₀ z₀ hy₀ hz₀ hkink
""", "w3bi_bigonData_smooth_arcST_switch_z restated and closed by w3cz_…_switch_z_of_not_kink"))

# ---- (2d) w3bi_bigonData_smooth_arcTS_switch_z
CONNECT.append(("""    (clear_vertex : ∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- (BIGON) as for `arcST`: reduced to the missing `hk5 : 5 ≤ k` on the component of `cutStartT` (rule 3).
  exact w3cz_bigonData_smooth_arcTS_switch_z_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀
    hy₀ hz₀ (by sorry)
""", """    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- (W3C assembler) STATEMENT RESTATED as for `arcST` (W3C_ASSEMBLY_REPORT.md §2): unit BIGON's proved corrected form.
  exact w3cz_bigonData_smooth_arcTS_switch_z_of_not_kink D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover
    y₀ z₀ hy₀ hz₀ hkink
""", "w3bi_bigonData_smooth_arcTS_switch_z restated and closed by w3cz_…_switch_z_of_not_kink"))

# ---- (2e) w3bi_bigon_of_site_model: the non-kink conditions as hypotheses; body = BIGON's variant
CONNECT.append(("""/-- **One bigon from the site data, any `SpliceModel` (PROVED from `w3g_*` and the `switch_z` forms by name)**:
the smoothing crossings `y₀, z₀` over `y, z` (`liftCrossing`, `origCrossing_liftCrossing`), the consumer's `y_H`
at `py` is `y₀` or `z₀` (`crossingPoint_origCrossing` + generic injectivity), then the four cases
(orientation × switched crossing). -/
theorem w3bi_bigon_of_site_model (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε) (py pz : Plane) (hsite : w3bi_SiteData D x py pz)
    (y_H : (toDiagram D x M hε).Γ.Crossing) (hyH : (toDiagram D x M hε).Γ.crossingPoint y_H = py) :
    ∃ z_H : (toDiagram D x M hε).Γ.Crossing, (toDiagram D x M hε).Γ.crossingPoint z_H = pz ∧
      ∃ B : BigonData ((toDiagram D x M hε).switch y_H), (B.y = y_H ∧ B.z = z_H) ∨ (B.y = z_H ∧ B.z = y_H) := by
  obtain ⟨g, hgs, hgt, y, z, hyx, hzx, hy, hz, hsy, htz, hor, clear, clear_vertex, hover, hpts⟩ := hsite
""", """/-- **One bigon from the site data, any `SpliceModel` (PROVED from `w3g_*` and the `switch_z` forms by name)**:
the smoothing crossings `y₀, z₀` over `y, z` (`liftCrossing`, `origCrossing_liftCrossing`), the consumer's `y_H`
at `py` is `y₀` or `z₀` (`crossingPoint_origCrossing` + generic injectivity), then the four cases
(orientation × switched crossing).  (W3C assembler) carries unit G's two non-kink conditions `hkST`, `hkTS`
(`⟨s.1, s.2 − 1⟩ ≠ ⟨t.1, t.2 + 1⟩`, `⟨t.1, t.2 − 1⟩ ≠ ⟨s.1, s.2 + 1⟩`), which the four restated sub-leaves need;
`clear_vertex` of the site data is no longer consumed.  Body = unit BIGON's `w3cz_bigon_of_site_model_of_not_kink`. -/
theorem w3bi_bigon_of_site_model (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε) (py pz : Plane) (hsite : w3bi_SiteData D x py pz)
    (hkST : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩)
    (hkTS : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩)
    (y_H : (toDiagram D x M hε).Γ.Crossing) (hyH : (toDiagram D x M hε).Γ.crossingPoint y_H = py) :
    ∃ z_H : (toDiagram D x M hε).Γ.Crossing, (toDiagram D x M hε).Γ.crossingPoint z_H = pz ∧
      ∃ B : BigonData ((toDiagram D x M hε).switch y_H), (B.y = y_H ∧ B.z = z_H) ∨ (B.y = z_H ∧ B.z = y_H) := by
  obtain ⟨g, hgs, hgt, y, z, hyx, hzx, hy, hz, hsy, htz, hor, clear, -, hover, hpts⟩ := hsite
""", "w3bi_bigon_of_site_model: non-kink hypotheses added (header)"))
CONNECT.append(("""    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3g_bigonData_smooth_arcST D x M hε g hgs hgt y z hy hz hsy htz hys hzt
        clear clear_vertex hover y₀ z₀ hy₀ hz₀
      exact ⟨B, Or.inl ⟨hBy, hBz⟩⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3g_bigonData_smooth_arcTS D x M hε g hgs hgt y z hy hz hsy htz hys hzt
        clear clear_vertex hover y₀ z₀ hy₀ hz₀
      exact ⟨B, Or.inr ⟨hBy, hBz⟩⟩
""", """    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3g_bigonData_smooth_arcST D x M hε g hgs hgt y z hy hz hsy htz hys hzt
        clear hover y₀ z₀ hy₀ hz₀ hkST
      exact ⟨B, Or.inl ⟨hBy, hBz⟩⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3g_bigonData_smooth_arcTS D x M hε g hgs hgt y z hy hz hsy htz hys hzt
        clear hover y₀ z₀ hy₀ hz₀ hkTS
      exact ⟨B, Or.inr ⟨hBy, hBz⟩⟩
""", "w3bi_bigon_of_site_model: w3g_ calls carry the non-kink hypotheses"))
CONNECT.append(("""    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3bi_bigonData_smooth_arcST_switch_z D x M hε g hgs hgt y z hy hz hsy htz
        hys hzt clear clear_vertex hover y₀ z₀ hy₀ hz₀
      exact ⟨B, Or.inr ⟨hBy, hBz⟩⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3bi_bigonData_smooth_arcTS_switch_z D x M hε g hgs hgt y z hy hz hsy htz
        hys hzt clear clear_vertex hover y₀ z₀ hy₀ hz₀
      exact ⟨B, Or.inl ⟨hBy, hBz⟩⟩
""", """    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3bi_bigonData_smooth_arcST_switch_z D x M hε g hgs hgt y z hy hz hsy htz
        hys hzt clear hover y₀ z₀ hy₀ hz₀ hkST
      exact ⟨B, Or.inr ⟨hBy, hBz⟩⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3bi_bigonData_smooth_arcTS_switch_z D x M hε g hgs hgt y z hy hz hsy htz
        hys hzt clear hover y₀ z₀ hy₀ hz₀ hkTS
      exact ⟨B, Or.inl ⟨hBy, hBz⟩⟩
""", "w3bi_bigon_of_site_model: switch_z calls carry the non-kink hypotheses"))

# ---- (2f) w3bi_bigon_of_site: the non-kink condition in the self case; body = BIGON's variant
CONNECT.append(("""/-- the same on the library smoothing `smoothDiagram D x (eps D x) (eps_small D x)` (`unfold; split_ifs`) -/
theorem w3bi_bigon_of_site (D : Diagram) (x : D.Γ.Crossing) (py pz : Plane) (hsite : w3bi_SiteData D x py pz)
    (y_H : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.Crossing)
""", """/-- the same on the library smoothing `smoothDiagram D x (eps D x) (eps_small D x)` (`unfold; split_ifs`).
(W3C assembler) the non-kink conditions are needed only in the self case `(sS D x).1 = (tS D x).1` (in the mixed case
they hold by `w3bg_not_kink_of_ne_comp`); body = unit BIGON's `w3cz_bigon_of_site_of_not_kink`. -/
theorem w3bi_bigon_of_site (D : Diagram) (x : D.Γ.Crossing) (py pz : Plane) (hsite : w3bi_SiteData D x py pz)
    (hk : (sS D x).1 = (tS D x).1 →
      (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ ∧
      (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩)
    (y_H : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.Crossing)
""", "w3bi_bigon_of_site: non-kink hypothesis added (header)"))
CONNECT.append(("""  · rw [dif_pos h]
    exact w3bi_bigon_of_site_model D x (selfModel D x (eps D x) h) (eps_small D x) py pz hsite
  · rw [dif_neg h]
    exact w3bi_bigon_of_site_model D x (mixedModel D x (eps D x) h) (eps_small D x) py pz hsite
""", """  · rw [dif_pos h]
    exact w3bi_bigon_of_site_model D x (selfModel D x (eps D x) h) (eps_small D x) py pz hsite (hk h).1 (hk h).2
  · rw [dif_neg h]
    exact w3bi_bigon_of_site_model D x (mixedModel D x (eps D x) h) (eps_small D x) py pz hsite
      (w3bg_not_kink_of_ne_comp D x h).1 (w3bg_not_kink_of_ne_comp D x h).2
""", "w3bi_bigon_of_site: body passes the non-kink conditions"))

# ---- (2g) remove BIGON's duplicate consumer variants (their bodies are now the w3bi_ bodies above)
CONNECT.append(("""/-- (BIGON) **`w3bi_bigon_of_site_model` on standard axioms only**: the same statement under the two non-kink conditions
of unit G (`⟨s.1, s.2 − 1⟩ ≠ ⟨t.1, t.2 + 1⟩` for the `arcST` orientation, `⟨t.1, t.2 − 1⟩ ≠ ⟨s.1, s.2 + 1⟩` for
`arcTS`; both trivial in the mixed case, `w3bg_not_kink_of_ne_comp`), consuming the corrected forms
`w3bg_…_of_not_kink` and `w3cz_…_switch_z_of_not_kink` instead of the frozen `w3g_*` / `w3bi_*_switch_z`.  The proof
is the frozen one with the four lemma names replaced (`clear_vertex` is not consumed by the corrected forms). -/
theorem w3cz_bigon_of_site_model_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
""", """/-! (W3C assembler) unit BIGON's consumer variants `w3cz_bigon_of_site_model_of_not_kink` /
`w3cz_bigon_of_site_of_not_kink` were merged INTO `w3bi_bigon_of_site_model` / `w3bi_bigon_of_site` above
(same statements, same bodies) and are not repeated here. -/
theorem w3cz_REMOVED_bigon_of_site_model_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
""", "mark BIGON's duplicate consumer variants for removal (start marker)"))

# ---- (2h) w3bi_bigon_pair_of / w3bi_bigon_pair_data take SITE's non-kink box
CONNECT.append(("""/-- **β1 from β1′ (PROVED)**: one bigon per side by `w3bi_bigon_of_site`. -/
theorem w3bi_bigon_pair_of (hsite : w3bi_site_data) : w3bi_bigon_pair := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL y_H y_L hyH hyL
  obtain ⟨sH, sL⟩ := hsite hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀'
    hq₀ hq₀' x_H x_L hxH hxL
  obtain ⟨z_H, hzH, B_H, hBH⟩ := w3bi_bigon_of_site _ x_H _ _ sH y_H hyH
  obtain ⟨z_L, hzL, B_L, hBL⟩ := w3bi_bigon_of_site _ x_L _ _ sL y_L hyL
  exact ⟨z_H, z_L, hzH, hzL, B_H, B_L, hBH, hBL⟩

/-- β1 with β1′ asserted -/
theorem w3bi_bigon_pair_data : w3bi_bigon_pair := w3bi_bigon_pair_of w3bi_site_data_data
""", """/-- **β1 from β1′ (PROVED)**: one bigon per side by `w3bi_bigon_of_site`.  (W3C assembler) also takes unit SITE's
non-kink condition at the two lift crossings (`w3cs_not_kink_site`), which the restated bigon sub-leaves need. -/
theorem w3bi_bigon_pair_of (hsite : w3bi_site_data) (hkink : w3cs_not_kink_site) : w3bi_bigon_pair := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL y_H y_L hyH hyL
  obtain ⟨sH, sL⟩ := hsite hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀'
    hq₀ hq₀' x_H x_L hxH hxL
  obtain ⟨kH, kL⟩ := hkink hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀'
    hq₀ hq₀' x_H x_L hxH hxL
  obtain ⟨z_H, hzH, B_H, hBH⟩ := w3bi_bigon_of_site _ x_H _ _ sH (fun _ => kH) y_H hyH
  obtain ⟨z_L, hzL, B_L, hBL⟩ := w3bi_bigon_of_site _ x_L _ _ sL (fun _ => kL) y_L hyL
  exact ⟨z_H, z_L, hzH, hzL, B_H, B_L, hBH, hBL⟩

/-- β1 with β1′ (PROVED by unit SITE) and the non-kink box (OPEN, unit SITE) -/
theorem w3bi_bigon_pair_data : w3bi_bigon_pair := w3bi_bigon_pair_of w3bi_site_data_data w3cs_not_kink_site_data
""", "w3bi_bigon_pair_of / w3bi_bigon_pair_data take w3cs_not_kink_site(_data)"))

def POST(text):
    """Delete the marked duplicate block: from `theorem w3cz_REMOVED_…` to just before the frozen β1′ docstring."""
    i = text.index("theorem w3cz_REMOVED_bigon_of_site_model_of_not_kink")
    j = text.index("/-- **BLACK BOX β1′ (the site data at the 177 configuration, both sides)**", i)
    removed = text[i:j]
    assert "w3cz_bigon_of_site_of_not_kink" in removed and removed.count("theorem ") == 2, removed.count("theorem ")
    print(f"removed duplicate consumer block: {removed.count(chr(10))} lines")
    return text[:i] + text[j:]

# ---- (3a) SPLITC's black box `w3cc_splitA_corners` CLOSED from unit SPLITA's carriers (assembler-authored `w3cx_`)
CONNECT.append(("""/-- the black box asserted (open body): unit SPLITA's content, in the form this unit consumes. -/
theorem w3cc_splitA_corners_data : w3cc_splitA_corners := by
  sorry
""", """/-! #### (W3C assembler, `w3cx_`) SPLITC's corner ledger from SPLITA's carriers -/

/-- (W3C assembler) **`w3cc_SplitCorners` from SPLITA's core data** (abstract form): with the six-visit data `D`
(twins, `a, b, c ∉ Q`), `S = Q ∪ {a, b, c}` (instance-free, as `w3ca_core` takes it), the core `w3ca_CoreData` (whose
`central` clause names the three inner visits `zA zB zC` and says `Z` owns exactly them), the definitions of the
outer carriers (`w3ca_Ac/Bc/Cc`: the carrier of the other visit of the same crossing, by the orientation pattern)
and the marks partition (`w3ca_marks_partition`: a mark is on `A ∪ B ∪ C ∪ Z` iff it is on `q₀`).  `ownA/B/C`: in
either orientation pattern the outer carrier `X` is by definition the owner of one visit of its crossing and `Z` of
the other, and `Z ≠ X`, so the inner visit `zX` is the visit `Z` owns and `X` owns its twin.  `inherited`: a
`q₀`-mark on `Z` is one of `zA, zB, zC`, whose crossings are not in `Q`, so it is not a true corner of `Q`.
`cover`: a true corner of `S` on `A ∪ B ∪ C ∪ Z` is on `q₀`; its crossing is in `Q` or is `a`, `b` or `c`, and
the two visits of `a` are `zA` and its twin (`visit_eq_or_twin`). -/
theorem w3cx_splitCorners_of_core {P : LabelledTuple n} (hP : CrossingGeometry P) {Q S : Finset (Crossing P)}
    {a₁ a₂ b₁ b₂ c₁ c₂ : Visit P} (D : w3ca_SixData hP Q a₁ a₂ b₁ b₂ c₁ c₂)
    (hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = a₁.1 ∨ x = b₁.1 ∨ x = c₁.1)
    {A B C Z : GeoComponent hP S} (core : w3ca_CoreData hP S a₁ a₂ b₁ b₂ c₁ c₂ A B C Z)
    (hA : A = w3ca_Ac hP S a₁ a₂ b₁) (hB : B = w3ca_Bc hP S a₁ b₁ b₂) (hC : C = w3ca_Cc hP S a₁ b₁ c₁ c₂)
    (q₀ : GeoComponent hP Q)
    (hpart : ∀ m : Mark P, (geoOwner hP S m = A ∨ geoOwner hP S m = B ∨ geoOwner hP S m = C ∨
      geoOwner hP S m = Z) ↔ geoOwner hP Q m = q₀) :
    ∃ zA zB zC : Visit P, w3cc_SplitCorners hP Q S q₀ A B C Z zA zB zC := by
  obtain ⟨zA, zB, zC, hzA, hzB, hzC, hiff⟩ := core.central
  have hQS : Q ⊆ S := fun x hx => (hSeq x).mpr (Or.inl hx)
  have haS : a₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inl rfl))
  have hbS : b₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hcS : c₁.1 ∈ S := (hSeq _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have ownZA : geoOwner hP S (Sum.inr zA) = Z := (hiff _).mpr (Or.inl rfl)
  have ownZB : geoOwner hP S (Sum.inr zB) = Z := (hiff _).mpr (Or.inr (Or.inl rfl))
  have ownZC : geoOwner hP S (Sum.inr zC) = Z := (hiff _).mpr (Or.inr (Or.inr rfl))
  obtain ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩ := core.distinct
  -- the outer ownerships, by the orientation pattern in the definitions
  have hown : geoOwner hP S (Sum.inr (visitTwin zA)) = A ∧ geoOwner hP S (Sum.inr (visitTwin zB)) = B ∧
      geoOwner hP S (Sum.inr (visitTwin zC)) = C := by
    by_cases h : geoMarkSuccessor hP (Sum.inr a₁) = Sum.inr b₁
    · simp only [w3ca_Ac, w3ca_Bc, w3ca_Cc, h, ↓reduceIte] at hA hB hC
      refine ⟨?_, ?_, ?_⟩
      · rcases visit_eq_or_twin a₁ zA hzA with h1 | h1
        · exact absurd (hA.trans (by rw [← h1, ownZA])) hAZ
        · rw [h1, D.ta, D.ta']; exact hA.symm
      · rcases visit_eq_or_twin b₁ zB hzB with h1 | h1
        · rw [h1, D.tb]; exact hB.symm
        · exact absurd (hB.trans (by rw [← D.tb, ← h1, ownZB])) hBZ
      · rcases visit_eq_or_twin c₁ zC hzC with h1 | h1
        · rw [h1, D.tc]; exact hC.symm
        · exact absurd (hC.trans (by rw [← D.tc, ← h1, ownZC])) hCZ
    · simp only [w3ca_Ac, w3ca_Bc, w3ca_Cc, h, ↓reduceIte] at hA hB hC
      refine ⟨?_, ?_, ?_⟩
      · rcases visit_eq_or_twin a₁ zA hzA with h1 | h1
        · rw [h1, D.ta]; exact hA.symm
        · exact absurd (hA.trans (by rw [← D.ta, ← h1, ownZA])) hAZ
      · rcases visit_eq_or_twin b₁ zB hzB with h1 | h1
        · exact absurd (hB.trans (by rw [← h1, ownZB])) hBZ
        · rw [h1, D.tb, D.tb']; exact hB.symm
      · rcases visit_eq_or_twin c₁ zC hzC with h1 | h1
        · exact absurd (hC.trans (by rw [← h1, ownZC])) hCZ
        · rw [h1, D.tc, D.tc']; exact hC.symm
  refine ⟨zA, zB, zC, ?_⟩
  exact {
    subset := hQS
    distinct := ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩
    memA := ⟨by rw [hzA]; exact haS, by rw [hzA]; exact D.aQ⟩
    memB := ⟨by rw [hzB]; exact hbS, by rw [hzB]; exact D.bQ⟩
    memC := ⟨by rw [hzC]; exact hcS, by rw [hzC]; exact D.cQ⟩
    ownZ := ⟨ownZA, ownZB, ownZC⟩
    ownA := hown.1
    ownB := hown.2.1
    ownC := hown.2.2
    inherited := fun m hm hq => by
      rcases (hpart m).mpr hq with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exfalso
        rcases (hiff m).mp h with rfl | rfl | rfl
        · have hm' : zA.1 ∈ Q := hm
          rw [hzA] at hm'
          exact D.aQ hm'
        · have hm' : zB.1 ∈ Q := hm
          rw [hzB] at hm'
          exact D.bQ hm'
        · have hm' : zC.1 ∈ Q := hm
          rw [hzC] at hm'
          exact D.cQ hm'
    cover := fun m hm hown' => by
      have hq : geoOwner hP Q m = q₀ := (hpart m).mp hown'
      rcases m with i | v
      · exact Or.inl ⟨trivial, hq⟩
      · have hv : v.1 ∈ S := hm
        rcases (hSeq _).mp hv with hvQ | hva | hvb | hvc
        · exact Or.inl ⟨hvQ, hq⟩
        · rcases visit_eq_or_twin zA v (hva.trans hzA.symm) with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases visit_eq_or_twin zB v (hvb.trans hzB.symm) with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · rcases visit_eq_or_twin zC v (hvc.trans hzC.symm) with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) }

/-- (W3C assembler) **`w3cc_splitA_corners` PROVED** at every configuration of the extended interface, from
unit SPLITA's `w3ca_split_config` (the core at `t'`), `w3ca_sixData_config` (the six-visit data), and
`w3ca_marks_partition_config` (the marks partition against the contact carrier `q₀'`), with the supports
transported by `GT_outsideSupports_transport` / `GT_fullAvail_transport` and `S' = Q' ∪ T'` read through
`P1.mem_triangleCrossings_iff`. -/
theorem w3cx_splitA_corners_proof : w3cc_splitA_corners := by
  intro n _ _hn E e f g δ hL _hGT _hR t t' ht ht' hop hs hef heg hfg _hK Q hQ hfull _hQi _hQi' hS' _q₀ q₀' _hq₀ hq₀'
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  have D := w3ca_sixData_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull'
  have hSeq : ∀ x, x ∈ transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ↔
      x ∈ transportSupport hs Q ∨ x = xPair ((hs _).mp hef) ∨ x = xPair ((hs _).mp heg) ∨
        x = xPair ((hs _).mp hfg) := by
    intro x
    rw [Finset.mem_union, P1.mem_triangleCrossings_iff ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)]
  obtain ⟨zA, zB, zC, hC⟩ := w3cx_splitCorners_of_core (geomAt E t' ht'.1) D hSeq core rfl rfl rfl q₀'
    (fun m => w3ca_marks_partition_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
      q₀' hq₀' m)
  exact ⟨_, _, _, _, zA, zB, zC, hC⟩

/-- (W3C assembler) the black box CLOSED: unit SPLITA's content in this unit's form (`w3cx_splitA_corners_proof`). -/
theorem w3cc_splitA_corners_data : w3cc_splitA_corners :=
  w3cx_splitA_corners_proof
""", "w3cc_splitA_corners_data CLOSED from SPLITA (w3cx_splitCorners_of_core, w3cx_splitA_corners_proof)"))

# ---- (3b/3c) the OUTER data modulo ONE residue: SPLITB's core and KNOT's split+identification box from SPLITA's
#      carriers, the assembler's corner ledger, SPLITC's record and SPLITB's fields.  The three event-level SPLITB
#      declarations move after the residue (statements unchanged).
_S = "(transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)"
_H = "((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)"
_A = "w3ca_A (geomAt E t' ht'.1) " + _S + " " + _H
_B = "w3ca_B (geomAt E t' ht'.1) " + _S + " " + _H
_C = "w3ca_C (geomAt E t' ht'.1) " + _S + " " + _H
_Z = "w3ca_Z (geomAt E t' ht'.1) " + _S + " " + _H
_OWN = "geoOwner (geomAt E t' ht'.1) " + _S + " (Sum.inr v)"
_TABLE = ("(∀ v : Visit (E.curve t'), v.1 ∈ triangleCrossings (E.curve t') e f g →\n"
          "          (" + _OWN + " =\n              " + _A + " ∨\n"
          "            " + _OWN + " =\n              " + _B + " ∨\n"
          "            " + _OWN + " =\n              " + _C + ") →\n"
          "          w3cb_turnAt (geomAt E t' ht'.1) " + _S + " (Sum.inr v) = s)")
_MIXED = ("(w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q)\n          " + _S + " q₀').card = 2 * Λ")
_IDENT = ("w3ck_three_components_ident_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')\n"
          "          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ\n"
          "          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (" + _A + "))\n"
          "          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (" + _B + "))\n"
          "          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' (" + _C + "))")

SPLITB_MOVED_OLD = """/-- the black box asserted (open body): SPLITA's geometry, not this unit's content -/
theorem w3cb_split_core_data : w3cb_split_core := by
  sorry

/-- the split geometry at every configuration from the core (`triangle_on_contact` supplied by
`w3cb_triangle_on_contact_at`) -/
theorem w3cb_split_geometry_of_core (h : w3cb_split_core) : w3cb_split_geometry := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨A, B, C, Λ, s, hc⟩ :=
    h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  exact ⟨A, B, C, Λ, s, w3cb_splitGeometry_of_residue _ ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)
    (CV.geoIndependent_of_mem_Ind _ hS')
    (w3cb_residue_of_core _ hc (w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'))⟩

/-- the split geometry at every configuration, on the black box -/
theorem w3cb_split_geometry_data : w3cb_split_geometry :=
  w3cb_split_geometry_of_core w3cb_split_core_data
"""
CONNECT.append((SPLITB_MOVED_OLD, """/-! (W3C assembler) the event-level declarations `w3cb_split_core_data`, `w3cb_split_geometry_of_core`,
`w3cb_split_geometry_data` are declared after the OUTER residue `w3cx_outer_residue` (in `section W3CK_Outer`,
after KNOT's `w3ck_split_ident`), statements unchanged: the black box `w3cb_split_core_data` is there proved from
SPLITA's carriers and the residue (`w3cx_split_core_of_residue`). -/
""", "SPLITB's event-level black-box declarations moved after the residue"))

OUTER_BLOCK = """/-! #### (W3C assembler, `w3cx_`) the OUTER data from SPLITA + SPLITB + SPLITC + KNOT, modulo ONE residue -/

/-- (W3C assembler) **SPLITB's core `w3cb_SplitCore` from SPLITA's core data** (abstract form): with the six-visit
data `D`, the core (each outer carrier owns one of the six visits, every one of them is on `A`, `B`, `C` or `Z`, and `Z`
owns exactly the three inner visits), the residue's sign table (every triangle visit on an outer carrier has turn `s`)
and parity (`#mixedSet = 2Λ`).  `localX` = the visit `X` owns (`hitX`) with its turn from the table; `central`: a
triangle visit not on `A, B, C` is on `Z`, whose marks are the inner visits, all on triangle crossings. -/
theorem w3cx_splitCore_of_core {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)
    {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    {Q : Finset (Crossing P)} (q₀ : GeoComponent hP Q)
    {A B C Z : GeoComponent hP (Q ∪ triangleCrossings P e f g)}
    (D : w3ca_SixData hP Q (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)))
    (core : w3ca_CoreData hP (Q ∪ triangleCrossings P e f g)
      (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)) A B C Z)
    {Λ : ℕ} {s : SignType} (hs0 : s ≠ 0)
    (htable : ∀ v : Visit P, v.1 ∈ triangleCrossings P e f g →
      (geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = A ∨
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = B ∨
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = C) →
      w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s)
    (hmixed : (w3cb_mixedSet hP Q (Q ∪ triangleCrossings P e f g) q₀).card = 2 * Λ) :
    w3cb_SplitCore hP e f g q₀ A B C Λ s := by
  have hsix : ∀ v : Visit P, (v = visitOn (xPair hef) e (mem_pair_left e f) ∨
      v = visitOn (xPair hef) f (mem_pair_right e f) ∨ v = visitOn (xPair heg) e (mem_pair_left e g) ∨
      v = visitOn (xPair heg) g (mem_pair_right e g) ∨ v = visitOn (xPair hfg) g (mem_pair_right f g) ∨
      v = visitOn (xPair hfg) f (mem_pair_left f g)) → v.1 ∈ triangleCrossings P e f g := by
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl))
    · exact (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl))
  have hmem : ∀ w : Visit P, w.1 ∈ triangleCrossings P e f g →
      (w = visitOn (xPair hef) e (mem_pair_left e f) ∨ w = visitOn (xPair hef) f (mem_pair_right e f) ∨
      w = visitOn (xPair heg) e (mem_pair_left e g) ∨ w = visitOn (xPair heg) g (mem_pair_right e g) ∨
      w = visitOn (xPair hfg) g (mem_pair_right f g) ∨ w = visitOn (xPair hfg) f (mem_pair_left f g)) := by
    intro w hw
    rcases (P1.mem_triangleCrossings_iff hef heg hfg _).mp hw with h | h | h
    · rcases visit_eq_or_twin (visitOn (xPair hef) e (mem_pair_left e f)) w h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (h1.trans D.ta))
    · rcases visit_eq_or_twin (visitOn (xPair heg) e (mem_pair_left e g)) w h with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h1.trans D.tb))))
    · rcases visit_eq_or_twin (visitOn (xPair hfg) g (mem_pair_right f g)) w h with h1 | h1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h1.trans D.tc)))))
  obtain ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩ := core.distinct
  obtain ⟨zA, zB, zC, hzA, hzB, hzC, hiff⟩ := core.central
  refine ⟨hs0, ?_, ?_, ?_, hAB, hAC, hBC, ?_, hmixed⟩
  · obtain ⟨v, hv6, hvA⟩ := core.hitA
    exact ⟨v, hsix v hv6, hvA, htable v (hsix v hv6) (Or.inl hvA)⟩
  · obtain ⟨v, hv6, hvB⟩ := core.hitB
    exact ⟨v, hsix v hv6, hvB, htable v (hsix v hv6) (Or.inr (Or.inl hvB))⟩
  · obtain ⟨v, hv6, hvC⟩ := core.hitC
    exact ⟨v, hsix v hv6, hvC, htable v (hsix v hv6) (Or.inr (Or.inr hvC))⟩
  · intro w hw
    rcases core.six w (hmem w hw) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr fun m hm => ?_))
      rw [h] at hm
      rcases (hiff m).mp hm with rfl | rfl | rfl
      · exact ⟨zA, rfl, by rw [hzA]; exact hsix _ (Or.inl rfl)⟩
      · exact ⟨zB, rfl, by rw [hzB]; exact hsix _ (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨zC, rfl, by rw [hzC]; exact hsix _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩

/-- (W3C assembler) the turn `w3cb_turnAt` at a SELECTED visit is the crossing sign of its two edge labels
(`geoInEdge_visit`, `geoOutSlot_selected`: the incoming edge is the visit's own, the outgoing slot is the twin's). -/
theorem w3cx_turnAt_selected {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    w3cb_turnAt hP S (Sum.inr v) = crossingSign P v.2.val (visitTwin v).2.val := by
  unfold w3cb_turnAt crossingSign
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv]

/-- (W3C assembler) **the sign table (ESC (1c)) from SPLITA's core data and the alternating triple**: with `A, B, C, Z`
SPLITA's carriers (`w3ca_Ac/Bc/Cc/Zc`), every triangle visit owned by an outer carrier has the same nonzero turn `s`.
In the orientation pattern `σ a₁ = b₁` the outer visits are `a₁ : e → f`, `b₂ : g → e`, `c₂ : f → g` (turns
`cs(e,f)`, `cs(g,e) = −cs(e,g)`, `cs(f,g)`) and `Z` owns `a₂, b₁, c₁`; in the mirror pattern the outer visits are
`a₂ : f → e`, `b₁ : e → g`, `c₁ : g → f` and `Z` owns `a₁, b₂, c₂`.  The alternating triple `cs(e,f) = cs(f,g) =
−cs(e,g)` makes the three outer turns agree (`s = cs(e,f)` resp. `s = cs(e,g)`), `s ≠ 0` by
`CV.crossingSign_visit_twin_ne_zero`, and a visit owned by `Z` is owned by none of `A, B, C` (`distinct`; which
visits `Z` owns comes from the `central` clause). -/
theorem w3cx_sign_table_of_core {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    {Q : Finset (Crossing P)} {A B C Z : GeoComponent hP (Q ∪ triangleCrossings P e f g)}
    (D : w3ca_SixData hP Q (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)))
    (core : w3ca_CoreData hP (Q ∪ triangleCrossings P e f g)
      (visitOn (xPair hef) e (mem_pair_left e f)) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)) (visitOn (xPair hfg) f (mem_pair_left f g)) A B C Z)
    (hA : A = w3ca_Ac hP (Q ∪ triangleCrossings P e f g) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair hef) f (mem_pair_right e f)) (visitOn (xPair heg) e (mem_pair_left e g)))
    (hB : B = w3ca_Bc hP (Q ∪ triangleCrossings P e f g) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair heg) g (mem_pair_right e g)))
    (hC : C = w3ca_Cc hP (Q ∪ triangleCrossings P e f g) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) (visitOn (xPair hfg) g (mem_pair_right f g))
      (visitOn (xPair hfg) f (mem_pair_left f g)))
    (hZ : Z = w3ca_Zc hP (Q ∪ triangleCrossings P e f g) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair hef) f (mem_pair_right e f)) (visitOn (xPair heg) e (mem_pair_left e g)))
    (halt : IsAlternating (crossingSign P e f) (crossingSign P e g) (crossingSign P f g)) :
    ∃ s : SignType, s ≠ 0 ∧ ∀ v : Visit P, v.1 ∈ triangleCrossings P e f g →
      (geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = A ∨
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = B ∨
        geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = C) →
      w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = s := by
  obtain ⟨hfg_eq, heg_eq⟩ := halt
  have hsix : ∀ v : Visit P, (v = visitOn (xPair hef) e (mem_pair_left e f) ∨
      v = visitOn (xPair hef) f (mem_pair_right e f) ∨ v = visitOn (xPair heg) e (mem_pair_left e g) ∨
      v = visitOn (xPair heg) g (mem_pair_right e g) ∨ v = visitOn (xPair hfg) g (mem_pair_right f g) ∨
      v = visitOn (xPair hfg) f (mem_pair_left f g)) → v.1 ∈ Q ∪ triangleCrossings P e f g := by
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl)))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl)))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl)))
    · exact Finset.mem_union_right _ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl)))
  have hmem : ∀ w : Visit P, w.1 ∈ triangleCrossings P e f g →
      (w = visitOn (xPair hef) e (mem_pair_left e f) ∨ w = visitOn (xPair hef) f (mem_pair_right e f) ∨
      w = visitOn (xPair heg) e (mem_pair_left e g) ∨ w = visitOn (xPair heg) g (mem_pair_right e g) ∨
      w = visitOn (xPair hfg) g (mem_pair_right f g) ∨ w = visitOn (xPair hfg) f (mem_pair_left f g)) := by
    intro w hw
    rcases (P1.mem_triangleCrossings_iff hef heg hfg _).mp hw with h | h | h
    · rcases visit_eq_or_twin (visitOn (xPair hef) e (mem_pair_left e f)) w h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (h1.trans D.ta))
    · rcases visit_eq_or_twin (visitOn (xPair heg) e (mem_pair_left e g)) w h with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h1.trans D.tb))))
    · rcases visit_eq_or_twin (visitOn (xPair hfg) g (mem_pair_right f g)) w h with h1 | h1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h1.trans D.tc)))))
  obtain ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩ := core.distinct
  obtain ⟨zA, zB, zC, hzA, hzB, hzC, hiff⟩ := core.central
  -- the six turns
  have hta₁ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hef) e (mem_pair_left e f))) =
      crossingSign P e f := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inl rfl)); rw [D.ta] at this; exact this
  have hta₂ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hef) f (mem_pair_right e f))) =
      crossingSign P f e := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inl rfl))); rw [D.ta'] at this; exact this
  have htb₁ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair heg) e (mem_pair_left e g))) =
      crossingSign P e g := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inr (Or.inl rfl)))); rw [D.tb] at this; exact this
  have htb₂ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair heg) g (mem_pair_right e g))) =
      crossingSign P g e := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    rw [D.tb'] at this; exact this
  have htc₁ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hfg) g (mem_pair_right f g))) =
      crossingSign P g f := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    rw [D.tc] at this; exact this
  have htc₂ : w3cb_turnAt hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hfg) f (mem_pair_left f g))) =
      crossingSign P f g := by
    have := w3cx_turnAt_selected hn hP _ _ (hsix _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    rw [D.tc'] at this; exact this
  have hne : crossingSign P e f ≠ 0 := by
    have := CV.crossingSign_visit_twin_ne_zero hP (visitOn (xPair hef) e (mem_pair_left e f))
    rw [D.ta] at this; exact this
  have hnotZ : ∀ v : Visit P, (geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = A ∨
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = B ∨
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) = C) →
      geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr v) ≠ Z := by
    rintro v (h | h | h) <;> rw [h] <;> assumption
  by_cases h : geoMarkSuccessor hP (Sum.inr (visitOn (xPair hef) e (mem_pair_left e f))) =
      Sum.inr (visitOn (xPair heg) e (mem_pair_left e g))
  · simp only [w3ca_Ac, w3ca_Bc, w3ca_Cc, w3ca_Zc, h, ↓reduceIte] at hA hB hC hZ
    -- `A = owner a₁`, `B = owner b₂`, `C = owner c₂`, `Z = owner a₂`; `Z` also owns `b₁`, `c₁`
    have hZb₁ : geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair heg) e (mem_pair_left e g))) = Z := by
      rcases visit_eq_or_twin (visitOn (xPair heg) e (mem_pair_left e g)) zB hzB with h1 | h1
      · rw [← h1]; exact (hiff _).mpr (Or.inr (Or.inl rfl))
      · exact absurd (hB.trans (by rw [← D.tb, ← h1]; exact (hiff _).mpr (Or.inr (Or.inl rfl)))) hBZ
    have hZc₁ : geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hfg) g (mem_pair_right f g))) = Z := by
      rcases visit_eq_or_twin (visitOn (xPair hfg) g (mem_pair_right f g)) zC hzC with h1 | h1
      · rw [← h1]; exact (hiff _).mpr (Or.inr (Or.inr rfl))
      · exact absurd (hC.trans (by rw [← D.tc, ← h1]; exact (hiff _).mpr (Or.inr (Or.inr rfl)))) hCZ
    refine ⟨crossingSign P e f, hne, fun v hv hown => ?_⟩
    rcases hmem v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hta₁
    · exact absurd hZ.symm (hnotZ _ hown)
    · exact absurd hZb₁ (hnotZ _ hown)
    · rw [htb₂, crossingSign_swap, heg_eq, neg_neg]
    · exact absurd hZc₁ (hnotZ _ hown)
    · rw [htc₂, ← hfg_eq]
  · simp only [w3ca_Ac, w3ca_Bc, w3ca_Cc, w3ca_Zc, h, ↓reduceIte] at hA hB hC hZ
    -- `A = owner a₂`, `B = owner b₁`, `C = owner c₁`, `Z = owner a₁`; `Z` also owns `b₂`, `c₂`
    have hZb₂ : geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair heg) g (mem_pair_right e g))) = Z := by
      rcases visit_eq_or_twin (visitOn (xPair heg) e (mem_pair_left e g)) zB hzB with h1 | h1
      · exact absurd (hB.trans (by rw [← h1]; exact (hiff _).mpr (Or.inr (Or.inl rfl)))) hBZ
      · rw [← D.tb, ← h1]; exact (hiff _).mpr (Or.inr (Or.inl rfl))
    have hZc₂ : geoOwner hP (Q ∪ triangleCrossings P e f g) (Sum.inr (visitOn (xPair hfg) f (mem_pair_left f g))) = Z := by
      rcases visit_eq_or_twin (visitOn (xPair hfg) g (mem_pair_right f g)) zC hzC with h1 | h1
      · exact absurd (hC.trans (by rw [← h1]; exact (hiff _).mpr (Or.inr (Or.inr rfl)))) hCZ
      · rw [← D.tc, ← h1]; exact (hiff _).mpr (Or.inr (Or.inr rfl))
    have hne' : crossingSign P e g ≠ 0 := by
      rw [heg_eq]; exact (by decide : ∀ a : SignType, a ≠ 0 → -a ≠ 0) _ hne
    refine ⟨crossingSign P e g, hne', fun v hv hown => ?_⟩
    rcases hmem v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hZ.symm (hnotZ _ hown)
    · rw [hta₂, crossingSign_swap, heg_eq]
    · exact htb₁
    · exact absurd hZb₂ (hnotZ _ hown)
    · rw [htc₁, crossingSign_swap, heg_eq, ← hfg_eq]
    · exact absurd hZc₂ (hnotZ _ hown)

/-- (W3C assembler) **the sign table at a configuration** for SPLITA's carriers: the alternating triple of `CompleteLocal`
at `t` (`w3e_alt_of_completeLocal`, via `GenericTableData.extreme_iff_alternating`) transported to `t'` by
`AV_EventRadius.sign_eq` (as unit SITE does), then `w3cx_sign_table_of_core` on `w3ca_split_config` / `w3ca_sixData_config`. -/
theorem w3cx_sign_table_at {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1)) :
    ∃ s : SignType, s ≠ 0 ∧
      @TABLE@ := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  have D := w3ca_sixData_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull'
  have halt : IsAlternating (crossingSign (E.curve t) e f) (crossingSign (E.curve t) e g)
      (crossingSign (E.curve t) f g) :=
    w3e_alt_of_completeLocal hGT t ht hef heg hfg hK
  have halt' : IsAlternating (crossingSign (E.curve t') e f) (crossingSign (E.curve t') e g)
      (crossingSign (E.curve t') f g) := by
    rw [hR.sign_eq t t' ht ht' e f hef, hR.sign_eq t t' ht ht' e g heg, hR.sign_eq t t' ht ht' f g hfg]
    exact halt
  exact w3cx_sign_table_of_core hn (geomAt E t' ht'.1) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) D core
    rfl rfl rfl rfl halt'

/-- (W3C assembler) **BLACK BOX — the residue of the OUTER data** after SPLITA (the carriers `w3ca_A/B/C/Z`,
`touching_iff`, `distinct`, `central_no_piece`, `central_rot`, and — via `w3cx_splitCorners_of_core` — SPLITC's corner
ledger), SPLITB (`writhe`, `mixed` from the core), SPLITC (`outer_alternative`, `uniform`) and KNOT (the two counts,
`w3ck_knot_after_two` / `w3ck_three_components_count`).  At every configuration of the extended interface there are
`Λ` such that (i) **the parity** (KNOT's bridge count, the analogue of `r176m_bridge_count`): the retained crossings of
`q₀'` whose two visits lie on different carriers of `Q' ∪ T'` (`w3cb_mixedSet`) number `2Λ`; (ii) **KNOT's
identification** for the same `Λ`: `twoLambda J_L = 2Λ` and the three knot restrictions of `J_L = D_L^{xy}` have the
HOMFLY polynomials of `A, B, C` (`w3ck_three_components_ident_occ`, record-clause form).  The sign table (ESC (1c)) is
PROVED above (`w3cx_sign_table_at`); everything else of `w3ck_split_ident` and of `w3cb_split_core` is PROVED from the
residue below. -/
def w3cx_outer_residue : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (_hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ Λ : ℕ,
        @MIXED@ ∧
        @IDENT@

/-- the residue asserted (OPEN body; W3C_ASSEMBLY_REPORT.md §3) -/
theorem w3cx_outer_residue_data : w3cx_outer_residue := by
  sorry

/-- (W3C assembler) **`esc_FullSplitData` at a configuration for SPLITA's carriers**, given the residue's sign table
and parity: SPLITA's `w3ca_split_at_outer` (`touching_iff`, `central_no_piece`), the corner ledger
`w3cx_splitCorners_of_core` (from `w3ca_split_config`, `w3ca_sixData_config`, `w3ca_marks_partition_config`), SPLITB's
`w3cb_fields_of_residue` (`writhe`, `mixed`) on the core `w3cx_splitCore_of_core` with `w3cb_triangle_on_contact_at`,
assembled by SPLITC's `w3cc_fullSplitData_of` (`distinct`, `central_rot`, `outer_alternative`, `uniform`). -/
theorem w3cx_fullSplitData_at {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q))
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀')
    (Λ : ℕ) (s : SignType) (hs0 : s ≠ 0)
    (htable : @TABLE@)
    (hmixed : @MIXED@) :
    esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀'
      (@A@) (@B@) (@C@) (@Z@) Λ := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  have D := w3ca_sixData_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull'
  have hSeq : ∀ x, x ∈ transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ↔
      x ∈ transportSupport hs Q ∨ x = xPair ((hs _).mp hef) ∨ x = xPair ((hs _).mp heg) ∨
        x = xPair ((hs _).mp hfg) := by
    intro x
    rw [Finset.mem_union, P1.mem_triangleCrossings_iff ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)]
  obtain ⟨zA, zB, zC, hC⟩ := w3cx_splitCorners_of_core (geomAt E t' ht'.1) D hSeq core rfl rfl rfl q₀'
    (fun m => w3ca_marks_partition_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
      q₀' hq₀' m)
  obtain ⟨touching_iff, -, central_no_piece⟩ :=
    w3ca_split_at_outer E e f g δ hL t t' ht ht' hop hs hef heg hfg Q hQ hfull hS'
  have hcore := w3cx_splitCore_of_core (geomAt E t' ht'.1) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) q₀'
    D core hs0 htable hmixed
  obtain ⟨writhe, mixed⟩ := w3cb_fields_of_residue hn (genericAt E t' ht'.1) e f g hQi' hS' ((hs _).mp hef)
    ((hs _).mp heg) ((hs _).mp hfg) q₀' (@Z@)
    (w3cb_residue_of_core _ hcore (w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'))
  exact w3cc_fullSplitData_of hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' _ _ _ _ Λ hC touching_iff
    central_no_piece writhe mixed

/-- (W3C assembler) **KNOT's `w3ck_split_ident` from the residue**: `esc_FullSplitData` by `w3cx_fullSplitData_at`,
the identification clause verbatim from the residue, for the SAME `Λ`. -/
theorem w3cx_split_ident_of_residue (h : w3cx_outer_residue) : w3ck_split_ident := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨Λ, hmixed, hident⟩ :=
    h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨s, hs0, htable⟩ := w3cx_sign_table_at hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hS'
  exact ⟨_, _, _, _, Λ, w3cx_fullSplitData_at hn E e f g δ hL t t' ht ht' hop hs hef heg hfg Q hQ hfull hQi' hS'
    q₀' hq₀' Λ s hs0 htable hmixed, hident⟩

/-- (W3C assembler) **SPLITB's `w3cb_split_core` from the residue**: SPLITA's carriers and core with the residue's
sign table and parity (`w3cx_splitCore_of_core`). -/
theorem w3cx_split_core_of_residue (h : w3cx_outer_residue) : w3cb_split_core := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨Λ, hmixed, -⟩ :=
    h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨s, hs0, htable⟩ := w3cx_sign_table_at hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hS'
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  obtain ⟨core, -, -, -⟩ :=
    w3ca_split_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull' hS'
  exact ⟨_, _, _, Λ, s, w3cx_splitCore_of_core (geomAt E t' ht'.1) ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)
    q₀' (w3ca_sixData_config hL ht' ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) hQ' hfull') core hs0 htable
    hmixed⟩

/-- (W3C assembler) SPLITB's black box, PROVED modulo the residue (moved here from `section W3CB_SPLITB`; statement
unchanged). -/
theorem w3cb_split_core_data : w3cb_split_core :=
  w3cx_split_core_of_residue w3cx_outer_residue_data

/-- the split geometry at every configuration from the core (`triangle_on_contact` supplied by
`w3cb_triangle_on_contact_at`) — unit SPLITB's theorem, moved after the residue -/
theorem w3cb_split_geometry_of_core (h : w3cb_split_core) : w3cb_split_geometry := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨A, B, C, Λ, s, hc⟩ :=
    h hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  exact ⟨A, B, C, Λ, s, w3cb_splitGeometry_of_residue _ ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)
    (CV.geoIndependent_of_mem_Ind _ hS')
    (w3cb_residue_of_core _ hc (w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'))⟩

/-- the split geometry at every configuration, on the black box (unit SPLITB's theorem, moved after the residue) -/
theorem w3cb_split_geometry_data : w3cb_split_geometry :=
  w3cb_split_geometry_of_core w3cb_split_core_data

/-- (W3C assembler) KNOT's black box, PROVED modulo the residue. -/
theorem w3ck_split_ident_data : w3ck_split_ident :=
  w3cx_split_ident_of_residue w3cx_outer_residue_data
"""
OUTER_BLOCK = (OUTER_BLOCK.replace("@TABLE@", _TABLE).replace("@MIXED@", _MIXED).replace("@IDENT@", _IDENT)
               .replace("@A@", _A).replace("@B@", _B).replace("@C@", _C).replace("@Z@", _Z))
CONNECT.append(("""/-- the black box asserted (open body): the split is unit SPLITB's; the identification is the open part of
this unit -/
theorem w3ck_split_ident_data : w3ck_split_ident := by
  sorry
""", OUTER_BLOCK, "OUTER residue block: w3cx_splitCore_of_core, w3cx_outer_residue(_data), w3cx_fullSplitData_at, "
                  "w3cx_split_ident_of_residue, w3cx_split_core_of_residue; w3cb_split_core_data / w3ck_split_ident_data closed modulo it"))
