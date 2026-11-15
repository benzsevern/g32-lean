import HodgeLean.Foundations.TubularEuler.ActualConormalFibreAffineHelpers
import HodgeLean.Foundations.TubularEuler.AffineImmersionPointKernelHelpers
import HodgeLean.Foundations.TubularEuler.SurjectiveScalarTensorHelpers

/-! # Original regular representatives of retained conormal vectors

Surjectivity of the actual point scalar map makes each fibre element the
class of one original affine immersion-ideal section.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleThom

theorem retainedConormal_regular_representative
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V)) (a : i1_conormalFibre j.left x) :
    let ρ := (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
    letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
    ∃ u : RingHom.ker (j.left.app V).hom,
      (actualConormalFibreAffineCotangentIso j.left V hV x hx).toLinearEquiv a =
        (1 : ℂ) ⊗ₜ[Γ(X.left, V)] (RingHom.ker (j.left.app V).hom).toCotangent u := by
  let ρ := (j.left.app V ≫ Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
  letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
  obtain ⟨q, hq⟩ := tensor_exists_one_tmul_of_surjective
    (affineImmersion_pointMap_surjective X Y j V hV x hx)
    ((actualConormalFibreAffineCotangentIso j.left V hV x hx).toLinearEquiv a)
  obtain ⟨u, rfl⟩ := (RingHom.ker (j.left.app V).hom).toCotangent_surjective q
  exact ⟨u, hq⟩

#print axioms retainedConormal_regular_representative

end HodgeLean.Foundations.TubularEuler
