-- Written 13:49Z 2026-09-15 by the pod executor: row 91 cp:finite-contact-path closed from the conditional theorem SM.cp_finite_contact_path_of_descent (SM/ContactPathOfDescent.lean, statement reviewed 2026-09-14) applied to the axiom SM.lit_homfly_descent (author's decision D-GAP2, 2026-09-15).
import SM.LitHomflyDescent

/-! # Row 91 cp:finite-contact-path (sm-3:3210-3233)

`ContactPathData` (SM/ContactPathOfDescent.lean §1, one field per printed clause, table in that module's
docstring) is the row's statement; the proof is the reviewed conditional theorem
`cp_finite_contact_path_of_descent` applied to the descent sentence of lit:homfly declared as
`lit_homfly_descent` (SM/LitHomflyDescent.lean). -/

namespace SM

/-- **Lemma cp:finite-contact-path** (sm-3:3210-3233, "The supplied contact-path diagram endpoints"): under
the printed hypotheses on `L`, its cusped xz projection and the supplied family `G_t` from `L` to `T`,
every clean ordinary cusp smoothing S(F), with smaller y over at the unchanged crossings, has the same
campaign polynomial as `D_T`. -/
theorem cp_finite_contact_path : ContactPathData :=
  cp_finite_contact_path_of_descent lit_homfly_descent

end SM
