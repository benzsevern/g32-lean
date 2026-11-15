import HodgeLean.Foundations.Program.G32Native.PELReferenceComplexification

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The actual holomorphic plane is the negative-i eigenspace of the canonical real operator.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.1–1.3. -/
theorem pel_holomorphic_negative_eigenspace (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Module.End.eigenspace
      (complexifyRealEnd (weightOneComplexStructure X (finiteBetti_abelian X)
        (spec_bettiDeRhamIso_abelian X))) (-Complex.I) = complexHolomorphicH1 X := by
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let M := (abelianVarietyCohomologyOf (finiteBetti_abelian X)
    (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X) hT).weight1
  have h10 : M.H (1, 0) = complexHolomorphicH1 X := by
    change cohomologyHodgePiece X 1 (1, 0) = _
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp only [latticeHodgePieces, ite_true]
  have h01 : M.H (0, 1) = complexAntiholomorphicH1 X := by
    change cohomologyHodgePiece X 1 (0, 1) = _
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    norm_num [latticeHodgePieces]
  apply pel_negative_eigenspace_of_split _ _ _ (spec_complexH1_split X).1
  · intro x hx
    rw [(spec_weightOneComplexStructure X (finiteBetti_abelian X)
      (spec_bettiDeRhamIso_abelian X)).2.1]
    exact spec_weightOneComplexOperator_h10 M x (h10.symm ▸ hx)
  · intro x hx
    rw [(spec_weightOneComplexStructure X (finiteBetti_abelian X)
      (spec_bettiDeRhamIso_abelian X)).2.1]
    exact spec_weightOneComplexOperator_h01 M x (h01.symm ▸ hx)

#print axioms pel_holomorphic_negative_eigenspace
end HodgeLean.Foundations.Program.GeneralTypeIII
