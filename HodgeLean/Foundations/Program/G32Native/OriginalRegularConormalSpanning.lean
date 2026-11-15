import HodgeLean.Foundations.Program.G32Native.OriginalRegularConormalTensor
import HodgeLean.Foundations.Program.G32Native.ModuleIsoValueInjectivity
import HodgeLean.Foundations.TubularEuler.ConormalRegularRepresentativeHelpers

/-! # Original descended equations span the retained conormal fibre -/
noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- Every retained conormal vector is the actual value of one original
regular ideal equation on the specified affine open.
Source: `retainedConormal_regular_representative` and
`originalRegularConormalValue_tensor`. -/
theorem originalRegularConormalValue_surjective
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) :
    Function.Surjective (fun u : RingHom.ker (j.left.app A).hom =>
      originalRegularConormalValue j.left A hA u x hx) := by
  intro a
  obtain ⟨u, hu⟩ := retainedConormal_regular_representative X Y j A hA x hx a
  refine ⟨u, ?_⟩
  apply moduleIsoValue_injective (actualConormalFibreAffineCotangentIso j.left A hA x hx)
  exact (originalRegularConormalValue_tensor j.left A hA u x hx).trans
    (moduleIsoValue_of_linear_equation _ a _ hu).symm

/-- A surjective family detects equality of linear maps.
Source: `Function.Surjective.forall` and `LinearMap.ext`. -/
theorem linearMap_ext_of_surjective_family
    {K V E I : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    [AddCommMonoid E] [Module K E] (s : I → V) (hs : Function.Surjective s)
    (F G : V →ₗ[K] E) (h : ∀ i, F (s i) = G (s i)) : F = G :=
  LinearMap.ext (hs.forall.mpr h)

#print axioms linearMap_ext_of_surjective_family
#print axioms originalRegularConormalValue_surjective
end HodgeLean.Foundations.TubularEuler
