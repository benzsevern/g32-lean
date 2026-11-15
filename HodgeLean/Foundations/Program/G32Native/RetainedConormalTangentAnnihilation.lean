import HodgeLean.Foundations.Program.G32Native.OriginalIdealTangentAnnihilation
import HodgeLean.Foundations.TubularEuler.ConormalRegularRepresentativeHelpers
import HodgeLean.Foundations.TubularEuler.RetainedConormalDifferentialHelpers

/-! # The retained conormal annihilates the actual immersion tangent

Every element of the original conormal fibre has an original regular equation
representative, to which the differentiated immersion equation applies.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

/-- The original retained conormal covectors annihilate the actual coordinate
derivative of the original immersion.
Source: Hartshorne, Algebraic Geometry, II.8, conormal sequence;
`retainedConormal_regular_representative` and the differentiated ideal equation.
HC no distance; AV milestone no distance. -/
theorem retainedConormal_comp_immersion_derivative_zero
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d m : ℕ) [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension m Y.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (S : (Fin m → ℂ) →L[ℂ] (Fin d → ℂ))
    (hS : HasFDerivAt (fun b => (chartAt (Fin d → ℂ) z)
        (Point.map j ((chartAt (Fin m → ℂ) x).symm b))) S
      ((chartAt (Fin m → ℂ) x) x))
    (a : BundleThom.i1_conormalFibre j.left x) :
    (retainedAffineConormalDifferential X Y j d A hA x hx z hz a).comp S = 0 := by
  let ρ := (j.left.app A ≫ Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ A) x hx ≫ (hA.preimage j.left).isoSpec.hom)).hom
  letI : Algebra Γ(X.left, A) ℂ := ρ.toAlgebra
  obtain ⟨u, hu⟩ := retainedConormal_regular_representative X Y j A hA x hx a
  change (affineConormalTensorDifferential X Y j d A hA x hx z hz
    ((actualConormalFibreAffineCotangentIso j.left A hA x hx).toLinearEquiv a)).comp S = 0
  rw [hu]
  rw [affineConormalTensorDifferential_regular_section, one_smul]
  have h := affineIdealDifferential_comp_immersion_derivative_zero X Y j d m A hA x hx z hz S hS u
  change (actualStalkDifferential X d z (Point.map j x) hz
    (X.left.presheaf.germ A (Point.map j x).underlying hx u.val)).comp S = 0 at h
  rwa [actualStalkDifferential_eq_section] at h

#print axioms retainedConormal_comp_immersion_derivative_zero

end HodgeLean.Foundations.TubularEuler
