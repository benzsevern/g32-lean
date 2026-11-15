import HodgeLean.Foundations.Program.MilneMatrixPresentation
import HodgeLean.Foundations.Program.MilneDivisorsGroup

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

def m2_lefschetzCoordinateIdeal (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) :
    Ideal (MvPolynomial (Fin (Module.finrank ℚ (HQ J 1)) ×
      Fin (Module.finrank ℚ (HQ J 1))) ℚ) :=
  letI := (torusCohomology_cupProductOf J).finite
  m2_formCoordinateIdeal (Module.finBasis ℚ (HQ J 1))
    (polarizationForm (torusCohomology_cupProductOf J) hη)
      (fun φ : AbelianEnd0 J => (abelianEnd0Action J φ).unop)

abbrev m2_lefschetzCoordinateAlgebra (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) : Type :=
  MvPolynomial (Fin (Module.finrank ℚ (HQ J 1)) × Fin (Module.finrank ℚ (HQ J 1))) ℚ ⧸
    m2_lefschetzCoordinateIdeal J pol hη

theorem m2_lefschetzCoordinate_reduced (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) :
    _root_.IsReduced (m2_lefschetzCoordinateAlgebra J pol hη) := by
  letI := (torusCohomology_cupProductOf J).finite
  exact m2_matrixCoordinate_reduced
    (LinearMap.BilinForm.toMatrix (Module.finBasis ℚ (HQ J 1))
      (polarizationForm (torusCohomology_cupProductOf J) hη))
    (fun φ : AbelianEnd0 J => LinearMap.toMatrix (Module.finBasis ℚ (HQ J 1))
      (Module.finBasis ℚ (HQ J 1)) (abelianEnd0Action J φ).unop)

def m2_lefschetzPointEnd (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (φ : m2_lefschetzCoordinateAlgebra J pol hη →ₐ[ℚ] ℂ) :
    Module.End ℂ (ℂ ⊗[ℚ] HQ J 1) :=
  letI := (torusCohomology_cupProductOf J).finite
  m2_coordinateEnd (Module.finBasis ℚ (HQ J 1))
    (polarizationForm (torusCohomology_cupProductOf J) hη)
    (fun ψ : AbelianEnd0 J => (abelianEnd0Action J ψ).unop) φ

theorem m2_lefschetzPointEnd_mem (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (φ : m2_lefschetzCoordinateAlgebra J pol hη →ₐ[ℚ] ℂ) :
    m2_lefschetzPointEnd J pol hη φ ∈ g32p_lefschetz J pol := by
  letI := (torusCohomology_cupProductOf J).finite
  let b := Module.finBasis ℚ (HQ J 1)
  let E := polarizationForm (torusCohomology_cupProductOf J) hη
  let T := fun ψ : AbelianEnd0 J => (abelianEnd0Action J ψ).unop
  apply (m0_mem_lefschetz_iff J pol hη _).2
  refine ⟨m2_coordinateEnd_isUnit b E T (m0_form_nondegenerate J pol hη) φ, ?_,
    m2_coordinateEnd_isometry b E T φ⟩
  rw [m0_endCentralizer, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨ψ, rfl⟩
  exact (m2_coordinateEnd_commutes b E T φ ψ).symm


theorem m2_exists_lefschetzPointEnd (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : u ∈ g32p_lefschetz J pol) :
    ∃ φ : m2_lefschetzCoordinateAlgebra J pol hη →ₐ[ℚ] ℂ,
      m2_lefschetzPointEnd J pol hη φ = u := by
  letI := (torusCohomology_cupProductOf J).finite
  obtain ⟨_, hc, he⟩ := (m0_mem_lefschetz_iff J pol hη u).1 hu
  apply m2_exists_coordinateEnd (Module.finBasis ℚ (HQ J 1))
    (polarizationForm (torusCohomology_cupProductOf J) hη)
    (fun ψ : AbelianEnd0 J => (abelianEnd0Action J ψ).unop) u _ he
  intro ψ
  have hh := (Subalgebra.mem_centralizer_iff ℂ).mp hc _ ⟨ψ, rfl⟩
  exact hh.symm


theorem m2_invariants_coordinatePoints (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (r n : ℕ) :
    g32p_invariants J pol r n =
      (⨅ φ : m2_lefschetzCoordinateAlgebra J pol hη →ₐ[ℚ] ℂ,
        LinearMap.eqLocus (exteriorPower.map n
          (g32p_diag J (m2_lefschetzPointEnd J pol hη φ) r)) LinearMap.id).map
            (g32p_powerClass J r n) := by
  unfold g32p_invariants
  congr 1
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]
  constructor
  · intro h φ
    exact h _ (m2_lefschetzPointEnd_mem J pol hη φ)
  · intro h u hu
    obtain ⟨φ, rfl⟩ := m2_exists_lefschetzPointEnd J pol hη u hu
    exact h φ


end HodgeLean.Foundations.Program
