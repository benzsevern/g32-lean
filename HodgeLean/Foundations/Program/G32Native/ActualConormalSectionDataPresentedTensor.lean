import HodgeLean.Foundations.Program.G32Native.ModuleIsoValueBoundary
import HodgeLean.Foundations.Program.G32Native.ModuleAffineCanonicalPresentation
import HodgeLean.Foundations.Program.G32Native.OriginalRegularConormalValue
import HodgeLean.Foundations.TubularEuler.ActualConormalFibreFactorHelpers

/-! # Tensor presentation of an original regular conormal value -/
noncomputable section
set_option maxHeartbeats 50000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

/-- A descended equation value specializes to its cotangent tensor when
its spectrum-point presentation is supplied explicitly.
Source: `affineSectionData_presented_cotangent`. -/
theorem actualConormalSectionData_presented_tensor
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A))
    (ψ : Q.left.presheaf.obj (.op (j ⁻¹ᵁ A)) ⟶ CommRingCat.of ℂ)
    (hp : ComplexPoint.liftToOpen Q (j ⁻¹ᵁ A) x hx ≫ (hA.preimage j).isoSpec.hom =
      Spec.map ψ) :
    let R := W.presheaf.obj (.op A)
    let S := Q.left.presheaf.obj (.op (j ⁻¹ᵁ A))
    let φ : R ⟶ S := j.app A
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    moduleIsoValue (moduleAffinePresentedFibreIso (Conormal.sheaf j) (j ⁻¹ᵁ A) (hA.preimage j)
      (Conormal.sheaf (Spec.map φ)) (actualConormalAffineChartIso j A hA) x hx
      (Spec.map ψ) hp ≪≫ affineConormalFibreCotangentIso R S φ ψ)
        (BundleResolution.i1_moduleSectionValue (Conormal.sheaf j) (j ⁻¹ᵁ A)
          (actualConormalAffineSectionData j A hA u).localSection x hx) =
      (1 : ℂ) ⊗ₜ[R] (RingHom.ker φ.hom).toCotangent u := by
  intro R S φ
  exact affineSectionData_presented_cotangent_value (Conormal.sheaf j)
    (j ⁻¹ᵁ A) (hA.preimage j) R φ ψ
    (actualConormalAffineChartIso j A hA) u
    (actualConormalAffineSectionData j A hA u) x hx hp

#print axioms actualConormalSectionData_presented_tensor
end HodgeLean.Foundations.TubularEuler
