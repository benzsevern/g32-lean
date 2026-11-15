import HodgeLean.Foundations.TubularEuler.ActualConormalSectionChartHelpers
import HodgeLean.Foundations.TubularEuler.ModuleAffineFibreChartIsoHelpers

/-! # Original scheme conormal fibre factors

The specified open chart comparison is followed by the named original affine cotangent comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

theorem actualConormalFibreAffineCotangentIso_eq
    {Q : Over (Spec (CommRingCat.of ℂ))} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen (j ⁻¹ᵁ V)) :
    letI : Algebra Γ(W, V) ℂ := ((j.app V) ≫ Spec.preimage
      (ComplexPoint.liftToOpen Q (j ⁻¹ᵁ V) x hx ≫ (hV.preimage j).isoSpec.hom)).hom.toAlgebra
    actualConormalFibreAffineCotangentIso j V hV x hx =
      moduleAffineFibreChartIso (Conormal.sheaf j) (j ⁻¹ᵁ V) (hV.preimage j)
        (Conormal.sheaf (Spec.map (j.app V))) (actualConormalAffineChartIso j V hV) x hx ≪≫
      affineConormalFibreCotangentIso (W.presheaf.obj (.op V))
        (Q.left.presheaf.obj (.op (j ⁻¹ᵁ V))) (j.app V) (Spec.preimage
          (ComplexPoint.liftToOpen Q (j ⁻¹ᵁ V) x hx ≫ (hV.preimage j).isoSpec.hom)) := by
  rfl

#print axioms actualConormalFibreAffineCotangentIso_eq

end HodgeLean.Foundations.TubularEuler
