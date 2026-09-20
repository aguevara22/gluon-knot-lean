-- Ported <HH:MM>Z 2026-09-15 from work/drafts/comparison/Comparison_Assembled.lean lines 131-186 (comparison lane §1, library: the descent of `C` to the polygon space — `cp_cornerStateSum_compat`, `cornerPolygonSum`, `cornerPolygonSum_projection`, `cp_cornerStateSum_congr`, `cornerPolygon`, `cornerPolygon_projection`, `cornerPolygon_projection'`, `cornerPolygon_chamber`) by the pod executor; body verbatim except this header, the import block (`import SM.CChamber` alone replaces the draft's 14 imports; compile-verified sufficient), the module docstring (new) and the draft's file-level line 49 `open WallGerm SoftDuplication Carrier` reduced to `open WallGerm Carrier` (the namespace `SoftDuplication` is not in this module's import closure; nothing in §1 uses it).  The wrappers `namespace SM` (line 47) / `end SM` (line 1052) are repeated.
import SM.CChamber

/-! # The descent of `C` to the polygon space — comparison lane §1 (library material)

Source: work/drafts/comparison/Comparison_Assembled.lean §1 (ASSEMBLY_REPORT.md §7 port plan; PLAN_FINAL.md §4 unit
U-CM-CPOLY, FR-CM-5).  def:C defines `C` on labelled generic tuples; sm-5/sm-6 compare it with thm:uniqueness's
`F : ∀ n [NeZero n], GenericPolygon n → ℤ`.  `cornerPolygon` is the `Quotient.lift` of `cornerStateSum` along def:C's
cyclic quotient (the accepted `cornerStateSum_genericShift`, SM/CChamber.lean), `0` below arity 3; `cornerPolygon_chamber`
is prop:C-chamber on the quotient.  Consumers: SM/AnchorValues.lean (row 122), SM/Comparison.lean (row 127),
SM/CInherits.lean (row 128). -/

namespace SM

open WallGerm Carrier

/-! ## §1 The descent of `C` to the polygon space (library; helpers prefixed `cp_`).
def:C defines `C` on labelled generic tuples; sm-5/sm-6 compare it with thm:uniqueness's
`F : ∀ n [NeZero n], GenericPolygon n → ℤ`.  The descent is along def:C's cyclic quotient by the accepted
`cornerStateSum_genericShift` (SM/CChamber.lean:1362); the same construction as the accepted
`alA_polygonAmplitude` (SM/ALawful.lean).  FR-CM-5. -/

section Descent
variable {n : ℕ} [NeZero n]

theorem cp_cornerStateSum_compat (hn : 3 ≤ n) (P Q : GenericTuple n)
    (h : (genericCyclicSetoid n) P Q) :
    cornerStateSum hn P.property = cornerStateSum hn Q.property := by
  obtain ⟨k, hk⟩ : ∃ k : ZMod n, Q.val = shift k P.val := h
  have hQ : Q = genericShift k P := Subtype.ext hk
  rw [hQ]
  exact (cornerStateSum_genericShift hn k P).symm

/-- `C` on the space of generic polygons of arity `n ≥ 3` (the `Quotient.lift` of `cornerStateSum`). -/
noncomputable def cornerPolygonSum (hn : 3 ≤ n) : GenericPolygon n → ℤ :=
  Quotient.lift (s := genericCyclicSetoid n) (fun P : GenericTuple n => cornerStateSum hn P.property)
    (fun P Q h => cp_cornerStateSum_compat hn P Q h)

theorem cornerPolygonSum_projection (hn : 3 ≤ n) (P : GenericTuple n) :
    cornerPolygonSum hn (polygonProjection P) = cornerStateSum hn P.property := rfl

/-- Transport of `cornerStateSum` along an equality of tuples (proof-irrelevant witnesses). -/
theorem cp_cornerStateSum_congr (hn : 3 ≤ n) {P Q : LabelledTuple n} (h : P = Q)
    (hP : Generic P) (hQ : Generic Q) : cornerStateSum hn hP = cornerStateSum hn hQ := by
  subst h; rfl

end Descent

/-- `C` as a function on generic polygons of every arity — the object thm:uniqueness and
prop:anchor-values quantify over ("a function on generic polygons of all arities"); `0` below arity 3,
where def:C defines nothing (irrelevant: every clause quantifies `3 ≤ n`; FR-CM-5). -/
noncomputable def cornerPolygon : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ :=
  fun n _ Q => if hn : 3 ≤ n then cornerPolygonSum hn Q else 0

theorem cornerPolygon_projection {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : GenericTuple n) :
    cornerPolygon n (polygonProjection P) = cornerStateSum hn P.property := by
  simp only [cornerPolygon, hn, ↓reduceDIte, cornerPolygonSum_projection]

theorem cornerPolygon_projection' {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) : cornerPolygon n (polygonProjection ⟨P, hP⟩) = cornerStateSum hn hP :=
  cornerPolygon_projection hn ⟨P, hP⟩

/-- Chamber constancy of `cornerPolygon` (prop:C-chamber on the quotient; accepted
`prop_C_chamber.constant`, SM/CChamber.lean). -/
theorem cornerPolygon_chamber : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericPolygon n),
    Q ∈ chamber P → cornerPolygon n Q = cornerPolygon n P := by
  intro n _ hn P Q
  refine Quotient.inductionOn₂ P Q ?_
  intro P' Q' hQ
  show cornerPolygon n (polygonProjection Q') = cornerPolygon n (polygonProjection P')
  rw [cornerPolygon_projection hn, cornerPolygon_projection hn]
  exact (prop_C_chamber.constant n hn P' Q' hQ).symm

end SM
