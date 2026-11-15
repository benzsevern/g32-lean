import HodgeLean.Foundations.Program.G32SelectedRealizationMarked

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem g32y_dualOperator_period (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (φ : b2_abelianLattice X →+ b2_abelianLattice X) (x : HQ X 1)
    (l : b2_abelianLattice X) :
    abelianPeriod X (b63g_dualOperator X φ x) l = abelianPeriod X x (φ l) := by
  have h := Classical.choose_spec (spec_abelianPeriod_equiv X)
  rw [← h, ← h]
  simp [abelianPeriodEquiv, b63g_dualOperator, b63g_precomp]

theorem g32y_dualOperator_sum (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {I : Type*} [Fintype I] (z : I → ℤ)
    (φ : I → b2_abelianLattice X →+ b2_abelianLattice X) :
    b63g_dualOperator X (∑ i, z i • φ i) =
      ∑ i, (z i : ℚ) • b63g_dualOperator X (φ i) := by
  classical
  apply LinearMap.ext
  intro x
  apply (abelianPeriodEquiv X).injective
  apply AddMonoidHom.ext
  intro l
  simp [b63g_dualOperator, b63g_precomp, map_sum]

end HodgeLean.Foundations.Program
