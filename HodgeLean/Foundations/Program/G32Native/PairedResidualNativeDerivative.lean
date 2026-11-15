import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeSubmersion
import HodgeLean.Adapters.ExpHolomorphic
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # The original native coordinate derivative -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The centred native coordinate expression retains the actual manifold
 differential of the original morphism.
Source: Mathlib, Geometry.Manifold.MFDeriv.Defs; the native chart construction. -/
theorem residual_native_coordinate_derivative
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) (p : ComplexPoint X) :
    fderiv ℂ (fun z : Fin d → ℂ =>
      localChart Y e (Point.map f p)
        (Point.map f ((localChart X d p).symm (localChart X d p p + z)))) 0 =
    mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) (Point.map f) p := by
  have hf := (spec_contMDiff_pointMap X Y d e f).mdifferentiable (by simp) p
  rw [mfderiv, if_pos hf]
  simp only [tangentSpaceCastModel, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id, modelWithCornersSelf_coe, Set.range_id,
    fderivWithin_univ]
  change fderiv ℂ (fun z : Fin d → ℂ =>
    localChart Y e (Point.map f p)
      (Point.map f ((localChart X d p).symm (localChart X d p p + z)))) 0 =
    fderiv ℂ (fun z => localChart Y e (Point.map f p)
      (Point.map f ((localChart X d p).symm z))) (localChart X d p p)
  simpa only [add_zero] using
    (fderiv_comp_add_left (𝕜 := ℂ)
      (f := fun z => localChart Y e (Point.map f p)
        (Point.map f ((localChart X d p).symm z)))
      (x := (0 : Fin d → ℂ)) (localChart X d p p))

/-- Surjectivity of the original point-map differential gives scheme smoothness.
Source: EGA IV, 17.11.1 and 17.3.3. -/
theorem residual_smooth_of_mfderiv_surjective
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left]
    (ht : ∀ p : ComplexPoint X, Function.Surjective
      (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) (Point.map f) p)) :
    Smooth f.left := by
  apply residual_native_submersion_smooth X Y d e f
  intro p
  rw [residual_native_coordinate_derivative]
  exact ht p

#print axioms residual_native_coordinate_derivative
#print axioms residual_smooth_of_mfderiv_surjective
end HodgeLean.Foundations.Program.G32Native
