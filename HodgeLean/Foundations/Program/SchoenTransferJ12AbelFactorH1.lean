import HodgeLean.Foundations.Program.SchoenTransferJ12AlgebraicFactor
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

/-- Centering gives an abelian factor with the original rational H1 pullback equation. -/
theorem s4_selected_abel_factor_H1
    (X A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [ConnectedSpace (ComplexPoint X)]
    (h : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1)
    (p : ComplexPoint X) (j : X ⟶ model h)
    (hj : ∀ x, Point.map j x = modelAbel h p x)
    (f : X ⟶ A) :
    ∃ π : model h ⟶ A, IsMonHom π ∧
      (homPullback j 1).comp (homPullback π 1) = homPullback f 1 := by
  obtain ⟨π, hπ, hfac⟩ := s4_selected_algebraic_abel_factor X A h p j hj
    (StageTwo.centered f p) (StageTwo.translationPoint f p).2.1
  exact ⟨π, hπ, (StageTwo.factorH1 f p j π hfac).1.symm⟩

#print axioms s4_selected_abel_factor_H1

end HodgeLean.Foundations.Program
