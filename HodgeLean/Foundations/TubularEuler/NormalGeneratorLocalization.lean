import HodgeLean.Foundations.TubularEuler.RetainedConormalDifferentialHelpers

/-! # Generator localization on the retained affine conormal

The affine presentation and the analytic local-ring differential are the specified maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry Topology Bundle
open HodgeLean.Adapters HodgeLean.Foundations.BundleThom
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

/-- An original ideal generator has the same differential before and after the retained fibre map.
This records localization at the actual point as well as the specified affine fibre comparison.
Source: Hartshorne, Algebraic Geometry, II.8; the regular-section formula for
`affineConormalTensorDifferential`.
HC no distance; AV milestone no distance. -/
theorem retained_conormal_generator_localization
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (u : RingHom.ker (j.left.app V).hom) (c : ℂ) (a : i1_conormalFibre j.left x) :
    let ρ := (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
    letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
    (actualConormalFibreAffineCotangentIso j.left V hV x hx).toLinearEquiv a =
      c ⊗ₜ (RingHom.ker (j.left.app V).hom).toCotangent u →
    retainedAffineConormalDifferential X Y j d V hV x hx z hz a =
      c • fderiv ℂ (fun b : Fin d → ℂ =>
        Point.evaluate V u.val ((chartAt (Fin d → ℂ) z).symm b))
        ((chartAt (Fin d → ℂ) z) (Point.map j x)) := by
  intro ρ ha
  exact (congrArg (affineConormalTensorDifferential X Y j d V hV x hx z hz) ha).trans
    (affineConormalTensorDifferential_regular_section X Y j d V hV x hx z hz u c)


example
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (u : RingHom.ker (j.left.app V).hom) (a : i1_conormalFibre j.left x) :
    let ρ := (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
    letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
    (actualConormalFibreAffineCotangentIso j.left V hV x hx).toLinearEquiv a =
      (2 : ℂ) ⊗ₜ (RingHom.ker (j.left.app V).hom).toCotangent u →
    retainedAffineConormalDifferential X Y j d V hV x hx z hz a =
      (2 : ℂ) • fderiv ℂ (fun b : Fin d → ℂ =>
        Point.evaluate V u.val ((chartAt (Fin d → ℂ) z).symm b))
        ((chartAt (Fin d → ℂ) z) (Point.map j x)) :=
  retained_conormal_generator_localization X Y j d V hV x hx z hz u 2 a

#print axioms retained_conormal_generator_localization

end HodgeLean.Foundations.TubularEuler
