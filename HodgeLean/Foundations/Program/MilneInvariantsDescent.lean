import HodgeLean.Foundations.Program.MilneLefschetzPresentation
import HodgeLean.Foundations.Program.MilnePowerBaseChange
import HodgeLean.Foundations.Program.MilneInvariantTransport

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

theorem m2_invariants_descend (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (r n : ℕ) :
    g32p_invariants J pol r n =
      (((g32p_invariants J pol r n).restrictScalars ℚ).comap
        (TensorProduct.mk ℚ ℂ (HQ (g3_power J r) n) 1)).baseChange ℂ := by
  letI := (torusCohomology_cupProductOf J).finite
  let b := Module.finBasis ℚ (HQ J 1)
  let d := Module.finrank ℚ (HQ J 1)
  let A := m2_lefschetzCoordinateAlgebra J pol hη
  letI : _root_.IsReduced A := m2_lefschetzCoordinate_reduced J pol hη
  let M : Matrix (Set.powersetCard (Fin (d * r)) n)
      (Set.powersetCard (Fin (d * r)) n) A :=
    (m2_exteriorMatrixPolynomial (K := ℚ) d r n).map
      (Ideal.Quotient.mkₐ ℚ (m2_lefschetzCoordinateIdeal J pol hη))
  have hm (φ : A →ₐ[ℚ] ℂ) : M.map φ =
      m2_exteriorMatrix d r n
        (LinearMap.toMatrix (b.baseChange ℂ) (b.baseChange ℂ)
          (m2_lefschetzPointEnd J pol hη φ)) := by
    have hmat := m2_coordinateEnd_matrix b
      (polarizationForm (torusCohomology_cupProductOf J) hη)
      (fun ψ : AbelianEnd0 J => (abelianEnd0Action J ψ).unop) φ
    exact (m2_exteriorMatrixQuotient_eval d r n
      (m2_lefschetzCoordinateIdeal J pol hη) φ).trans
        (congrArg (m2_exteriorMatrix d r n) hmat.symm)
  have ha (φ : A →ₐ[ℚ] ℂ) :
      exteriorPower.map n (g32p_diag J (m2_lefschetzPointEnd J pol hη φ) r) ∘ₗ
          (m2_powerExteriorEquiv b r n).toLinearMap =
        (m2_powerExteriorEquiv b r n).toLinearMap ∘ₗ
          Matrix.toLin (((m2_piBasis b r).exteriorPower n).baseChange ℂ)
            (((m2_piBasis b r).exteriorPower n).baseChange ℂ) (M.map φ) := by
    rw [hm]
    exact m2_powerExteriorEquiv_intertwines b r n _
  simp only [m2_invariants_coordinatePoints J pol hη r n]
  exact m2_polynomial_invariant_images_descend
    ((m2_piBasis b r).exteriorPower n) M (m2_powerCupQ J r n)
    (m2_powerExteriorEquiv b r n)
    (fun φ => exteriorPower.map n (g32p_diag J (m2_lefschetzPointEnd J pol hη φ) r))
    (g32p_powerClass J r n) ha (m2_powerClass_baseChange J b r n)

end HodgeLean.Foundations.Program
