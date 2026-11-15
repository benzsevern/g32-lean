import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Defs

/-! Transport of partition data along equality of the actual carrier. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_cast_dimension {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))} (h : S = T)
    (P : s2v_hardt_cad5_Partition S) :
    ((h ▸ P) : s2v_hardt_cad5_Partition T).dimension = P.dimension := by
  cases h
  rfl

end HodgeLean.Foundations.Program
