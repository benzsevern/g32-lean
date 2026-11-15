import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Restriction
import HodgeLean.Foundations.Program.SchoenTowerHardt2

/-! Boolean ambient limits with concrete finite chart partitions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_closure_partition {n : ℕ} (S : s2v_t11b_Formula n) :
    ∃ C : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition C.realize,
      C.realize = closure S.realize := by
  obtain ⟨C, hC, _⟩ := s2v_hardt2_closure_formula S
  obtain ⟨Q⟩ := s2v_hardt_cad5_partition_exists C
  exact ⟨C, Q, hC⟩

theorem s2v_hardt_cad5_boundary_partition {n : ℕ} (S : s2v_t11b_Formula n) :
    ∃ B : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition B.realize,
      B.realize = closure S.realize \ S.realize := by
  obtain ⟨C, hC, _⟩ := s2v_hardt2_closure_formula S
  let B := s2v_t11b_Formula.inter C (.compl S)
  obtain ⟨Q⟩ := s2v_hardt_cad5_partition_exists B
  refine ⟨B, Q, ?_⟩
  change C.realize ∩ S.realizeᶜ = _
  rw [hC]
  rfl

end HodgeLean.Foundations.Program
