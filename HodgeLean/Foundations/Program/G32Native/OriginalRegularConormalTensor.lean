import HodgeLean.Foundations.Program.G32Native.ActualConormalSectionDataPresentedTensor
import HodgeLean.Foundations.Program.G32Native.ModuleAffineCanonicalPresentation
import HodgeLean.Foundations.Program.G32Native.OriginalRegularConormalValue
import HodgeLean.Foundations.Program.G32Native.ActualConormalPresentedCotangent

/-! # Tensor presentation of an original regular conormal value -/
noncomputable section
set_option maxHeartbeats 50000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

/-- The original descended equation value has the tensor of the same equation
in the retained affine cotangent presentation.
Source: `affineSectionData_presented_cotangent` and
`moduleAffineFibreChartIso_eq_presented`. -/
theorem originalRegularConormalValue_tensor
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) :
    let R := W.presheaf.obj (.op A)
    let S := Q.left.presheaf.obj (.op (j ⁻¹ᵁ A))
    let φ : R ⟶ S := j.app A
    let b := ComplexPoint.liftToOpen Q (j ⁻¹ᵁ A) x hx ≫ (hA.preimage j).isoSpec.hom
    letI : Algebra R ℂ := (φ ≫ Spec.preimage b).hom.toAlgebra
    moduleIsoValue (actualConormalFibreAffineCotangentIso j A hA x hx)
      (originalRegularConormalValue j A hA u x hx) =
      (1 : ℂ) ⊗ₜ[R] (RingHom.ker φ.hom).toCotangent u := by
  intro R S φ b
  rw [actualConormalFibreAffineCotangentIso_eq_presented, originalRegularConormalValue_eq]
  exact actualConormalSectionData_presented_tensor j A hA u x hx
    (Spec.preimage b) (Spec.map_preimage b).symm

#print axioms originalRegularConormalValue_tensor
end HodgeLean.Foundations.TubularEuler
