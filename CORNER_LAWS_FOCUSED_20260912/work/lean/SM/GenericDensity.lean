import SM.AreaDensity
import SM.ConcurrenceDensity

/-! Full Generic density in the actual tuple space, as required by lem:fibres.
Both all-triple G1 and no-three-interior-concurrence G2 are proved. This is the
density clause only; admissible-fibre existence remains a separate obligation. -/

namespace SM

open Set

variable {n : ℕ}

theorem generic_of_G1_remoteNonconcurrent (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : G1 P) (hR : RemoteNonconcurrent P) : Generic P := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨hG, ?_⟩
  rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
  have hrij := g1_common_interiors_remote hn hG hij hi hj
  have hrjk := g1_common_interiors_remote hn hG hjk hj hk
  have hrik := g1_common_interiors_remote hn hG hik hi hk
  apply hR i j k hrij hrjk hrik
  exact concurrenceDet_eq_zero_of_closedTriple P i j k
    ⟨x, edgeInterior_subset_edgeSegment P i hi, edgeInterior_subset_edgeSegment P j hj,
      edgeInterior_subset_edgeSegment P k hk⟩

theorem dense_Generic (hn : 3 ≤ n) : Dense {P : LabelledTuple n | Generic P} := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hd : Dense ({P : LabelledTuple n | G1 P} ∩ {P | RemoteNonconcurrent P}) :=
    dense_G1.inter_of_isOpen_right dense_remoteNonconcurrent isOpen_remoteNonconcurrent
  exact hd.mono (fun _ h => generic_of_G1_remoteNonconcurrent hn h.1 h.2)

theorem generic_in_nonempty_open (hn : 3 ≤ n) (U : Set (LabelledTuple n))
    (hU : IsOpen U) (hne : U.Nonempty) : ∃ P ∈ U, Generic P := by
  obtain ⟨P, hP, hPU⟩ := (dense_Generic hn).exists_mem_open hU hne
  exact ⟨P, hPU, hP⟩

end SM
