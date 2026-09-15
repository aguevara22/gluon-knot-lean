import SM.ContactLegs
import SM.ContactParameters

/-! The actual parameters of each contact pair approach the contact parameter
on the base and the appropriate endpoint on its incident leg. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

def contactEndpoint (forward : Bool) : ℝ := if forward then 0 else 1

theorem contact_edgePoint_endpoint (P : LabelledTuple n) (M : ZMod n) (forward : Bool) :
    edgePoint P (contactLeg forward M) (contactEndpoint forward) = P M := by
  cases forward <;> simp [contactLeg, contactEndpoint, edgePoint, edge]

theorem contact_vertex_on_leg (P : LabelledTuple n) (M : ZMod n) (forward : Bool) :
    P M ∈ edgeSegment P (contactLeg forward M) := by
  refine ⟨contactEndpoint forward, ?_, ?_, (contact_edgePoint_endpoint P M forward).symm⟩
  · cases forward <;> norm_num [contactEndpoint]
  · cases forward <;> norm_num [contactEndpoint]

theorem contact_pair_det_ne_zero (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (forward : Bool) : det (edge P a) (edge P (contactLeg forward M)) ≠ 0 := by
  have hn5 := contactSeparated_size hn hsep
  exact singlePointTriple_remote_transverse (by omega) hz (contactLeg_remote hsep forward)
    (edgeInterior_subset_edgeSegment P a hm) (contact_vertex_on_leg P M forward)

theorem contact_parameters_center (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (r : ℝ) (hr : P M = edgePoint P a r) (forward : Bool) :
    edgeParameter P a (contactLeg forward M) = r ∧
    edgeParameter P (contactLeg forward M) a = contactEndpoint forward := by
  have hd := contact_pair_det_ne_zero hn hsep hz hm forward
  have hdr : det (edge P (contactLeg forward M)) (edge P a) ≠ 0 := by
    rw [det_swap]
    exact neg_ne_zero.mpr hd
  have he : edgePoint P a r = edgePoint P (contactLeg forward M) (contactEndpoint forward) :=
    hr.symm.trans (contact_edgePoint_endpoint P M forward).symm
  exact ⟨(div_eq_iff hd).mpr (intersection_parameter_identity he),
    (div_eq_iff hdr).mpr (intersection_parameter_identity he.symm)⟩

theorem continuousAt_contact_pair_parameters (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (forward : Bool) :
    ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q a (contactLeg forward M)) P ∧
    ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q (contactLeg forward M) a) P := by
  have hd := contact_pair_det_ne_zero hn hsep hz hm forward
  have hdr : det (edge P (contactLeg forward M)) (edge P a) ≠ 0 := by
    rw [det_swap]
    exact neg_ne_zero.mpr hd
  exact ⟨continuousAt_cramerFirst (continuous_vertex a).continuousAt
    (continuous_vertex (contactLeg forward M)).continuousAt (continuous_edge a).continuousAt
    (continuous_edge (contactLeg forward M)).continuousAt hd,
    continuousAt_cramerFirst (continuous_vertex (contactLeg forward M)).continuousAt
    (continuous_vertex a).continuousAt (continuous_edge (contactLeg forward M)).continuousAt
    (continuous_edge a).continuousAt hdr⟩

theorem continuousAt_approach_value {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} {x : α} {c ε : ℝ} (hf : ContinuousAt f x) (hc : f x = c) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, |f y - c| < ε := by
  have hnear := hf.eventually (isOpen_Ioo.mem_nhds
    (show f x ∈ Set.Ioo (c - ε) (c + ε) by rw [hc]; constructor <;> linarith))
  filter_upwards [hnear] with y hy
  exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem contact_parameters_approach (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (r : ℝ) (hr : P M = edgePoint P a r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q in 𝓝 P, ∀ forward : Bool,
      |edgeParameter Q a (contactLeg forward M) - r| < ε ∧
      |edgeParameter Q (contactLeg forward M) a - contactEndpoint forward| < ε := by
  apply eventually_all.mpr
  intro forward
  have hc := contact_parameters_center hn hsep hz hm r hr forward
  have hcont := continuousAt_contact_pair_parameters hn hsep hz hm forward
  exact (continuousAt_approach_value hcont.1 hc.1 hε).and
    (continuousAt_approach_value hcont.2 hc.2 hε)

end SM
