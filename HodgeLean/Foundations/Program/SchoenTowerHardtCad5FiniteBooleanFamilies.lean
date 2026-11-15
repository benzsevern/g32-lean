import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools

/-! Boolean formulas for unions over actual finite index types. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_finite_union_formula {n : ℕ} {ι : Type*} [Fintype ι]
    (C : ι → s2v_t11b_Formula n) :
    ∃ F : s2v_t11b_Formula n, F.realize = ⋃ i, (C i).realize := by
  classical
  obtain ⟨I, hI⟩ := s2v_hardt_cad3_finite_inter (fun i => (C i).compl)
  refine ⟨I.compl, ?_⟩
  ext x
  change (¬ x ∈ I.realize) ↔ _
  rw [hI]
  simp only [s2v_t11b_Formula.realize, Set.mem_compl_iff, not_forall, not_not, Set.mem_iUnion]

end HodgeLean.Foundations.Program
