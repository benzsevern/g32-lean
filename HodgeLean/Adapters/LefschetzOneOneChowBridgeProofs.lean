import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian
import HodgeLean.Foundations.AnalyticDivisorAlgebraic24

/-! # Chow bridge proof obligations

Three separate obligations for statement review. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic24
open Set
namespace HodgeLean.Adapters

theorem bhg_algebraization_of_chow_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (D : bh4_LocalDivisorData X) :
    Nonempty (bh4_Algebraization X D) := by
  obtain ⟨A⟩ := gaga24_algebraization X D.valid D.periodic hChow
  exact ⟨⟨A.n, A.x, A.distinct, A.codim, A.mult, A.positive, A.support,
    A.local_equations⟩⟩

theorem bhg_localDivisorDataAlgebraizes_of_chow_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    bh4_LocalDivisorDataAlgebraizes X := by
  intro D
  exact bhg_algebraization_of_chow_aux X hChow D

theorem bhg_lefschetzOneOne_of_chow_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    LefschetzOneOneFor X := by
  exact spec_bh4_lefschetzOneOneFor_of_localDivisorDataAlgebraizes X
    (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
    (bhg_localDivisorDataAlgebraizes_of_chow_aux X hChow)

end HodgeLean.Adapters
