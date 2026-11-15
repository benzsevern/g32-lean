import HodgeLean.Foundations.Program.SchoenTransferJ12CrossAdjointLinear
import HodgeLean.Foundations.Program.UniversalFamilyB60cHom

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Adjoint pullback between two nondegenerate algebraic divisor forms preserves the holomorphic H1 summand. -/
theorem s4_selected_cross_adjoint_holomorphic
    (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (pA : HQ A 2) (pB : HQ B 2)
    (hA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pA))
    (hB : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf B) pB))
    (hpA : (pA : H^(2 * 1)(A; ℚ)) ∈ Hdg^1(A; ℚ))
    (hpB : (pB : H^(2 * 1)(B; ℚ)) ∈ Hdg^1(B; ℚ)) (s : A ⟶ B) [IsMonHom s] :
    (complexHolomorphicH1 A).map
      ((s4_selected_cross_adjoint hB hA (homPullback s 1)).baseChange ℂ) ≤
        complexHolomorphicH1 B := by
  letI := (torusCohomology_cupProductOf A).finite
  letI := (torusCohomology_cupProductOf B).finite
  obtain ⟨⟨hA10, _⟩, _⟩ := (spec_firstRiemannRelation A (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) hA).mp hpA
  obtain ⟨⟨hB10, hB01⟩, _⟩ := (spec_firstRiemannRelation B (finiteBetti_abelian B)
    (spec_bettiDeRhamIso_abelian B) hB).mp hpB
  have eA : complexHolomorphicH1 A = cohomologyHodgePiece A 1 (1, 0) := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  have eB : complexHolomorphicH1 B = cohomologyHodgePiece B 1 (1, 0) := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  have eB' : complexAntiholomorphicH1 B = cohomologyHodgePiece B 1 (0, 1) := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  refine s4_selected_cross_adjoint_map_isotropic
    ((polarizationForm (torusCohomology_cupProductOf B) hB).baseChange ℂ)
    ((polarizationForm (torusCohomology_cupProductOf A) hA).baseChange ℂ)
    (WeilPower.nondegenerate_baseChange _
      (nondegenerate_polarizationForm (torusCohomology_cupProductOf B) hB))
    (complexHolomorphicH1 B) (complexAntiholomorphicH1 B) (complexHolomorphicH1 A)
    (spec_complexH1_split B).1 ?_ ?_ ?_
    ((homPullback s 1).baseChange ℂ)
    ((s4_selected_cross_adjoint hB hA (homPullback s 1)).baseChange ℂ) ?_ ?_
  · rw [eB]
    exact hB10
  · rw [eB']
    exact hB01
  · rw [eA]
    exact hA10
  · exact s4_selected_cross_adjoint_baseChange_pairing _ _ _ _
      (s4_selected_cross_adjoint_pairing hB hA (homPullback s 1))
  · exact (spec_homPullback_hodge s).1

#print axioms s4_selected_cross_adjoint_holomorphic
end HodgeLean.Foundations.Program
