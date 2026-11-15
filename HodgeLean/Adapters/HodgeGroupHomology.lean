import HodgeLean.Foundations.HodgeGroupDualityBridge
import HodgeLean.Adapters.PWTheorem42EisensteinProofs

/-! The homological group hypothesis for Theorem B, in the basis dual to a basis of H¹. -/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The homological group equality implies the cohomological `HodgeLieIsGk` input of Theorem B. -/
theorem f1_hodgeLieIsGk_of_homology_group_eq (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    {n : ℕ} (b : Module.Basis (Fin n) ℚ (HQ A 1))
    (h : g2_homologyHodgeGroup (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal b =
      g2_homologySpecialUnitary b (polarizationForm (torusCohomology_cupProductOf A) hη)
        (pwActionRange A θ) (pwAction A θ u) 3) :
    letI := (finiteBetti_abelian A).finite 1
    HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
      (abelianWeightOneHodgeStructure A).isInternal
      (polarizationForm (torusCohomology_cupProductOf A) hη)
      (pwActionRange A θ) (pwAction A θ u) := by
  let _ := (finiteBetti_abelian A).finite 1
  exact g2_hodgeLieIsGk_of_homology_group_eq _ _ b _ _ _ (by norm_num)
    (f1_weilAction A θ u 3 hu).J_sq
    (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη) h

/-- Composition with the existing Hermitian Lie comparison, starting on homology. -/
theorem f1_complexSU_of_homology_group_eq (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    {n : ℕ} (b : Module.Basis (Fin n) ℚ (HQ A 1))
    (h : g2_homologyHodgeGroup (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal b =
      g2_homologySpecialUnitary b (polarizationForm (torusCohomology_cupProductOf A) hη)
        (pwActionRange A θ) (pwAction A θ u) 3) :
    letI := (finiteBetti_abelian A).finite 1
    complexSpan (hodgeLieAlgebra (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal).toSubmodule =
      (complexSU (polarizationForm (torusCohomology_cupProductOf A) hη)
        (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη)
        (f1_weilAction A θ u 3 hu).J (f1_weilAction A θ u 3 hu).J_sq
        (polarizationForm_skew (torusCohomology_cupProductOf A) hη hRos)).toSubmodule := by
  let _ := (finiteBetti_abelian A).finite 1
  exact (f1_hodgeLieIsGk_iff_aux A θ u hu hL pol hη hRos).mp
    (f1_hodgeLieIsGk_of_homology_group_eq A θ u hu pol hη b h)

end HodgeLean.Adapters
