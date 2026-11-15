import HodgeLean.Foundations.Program.UniversalFamilyB60cComparison

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A member has a six-dimensional Hodge plane with balanced three-dimensional eigenspaces. -/
theorem b60c_member_hodge_dimensions (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    letI := (torusCohomology_cupProductOf P.X).finite
    Module.finrank ℂ (b60c_F P) = 6 ∧
      Module.finrank ℂ ↥(P.W.Vs ⊓ b60c_F P) = 3 ∧
      Module.finrank ℂ ↥(P.W.Vsbar ⊓ b60c_F P) = 3 := by
  letI := (torusCohomology_cupProductOf P.X).finite
  refine ⟨?_, hP.finrank_eq_three, ?_⟩
  · have hF : b60c_F P = complexHolomorphicH1 P.X := by
      change cohomologyHodgePiece P.X 1 (1, 0) = _
      rw [spec_g4_cohomologyHodgePiece_one_eq]
      simp only [latticeHodgePieces, ite_true]
    rw [hF, (spec_complexH1_dimension P.X).1, hP.dim_eq]
  · exact (P.W.finrank_inf_H10_eq_inf_H01
      (h10_sup_h01_eq_top (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
        (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X)) hP.isWeilType).trans
      ((finrank_Vsbar_inf_H01 (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
        (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W).trans
        hP.finrank_eq_three)

#print axioms b60c_member_hodge_dimensions

end HodgeLean.Foundations.Program
