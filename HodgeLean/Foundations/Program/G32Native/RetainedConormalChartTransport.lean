import HodgeLean.Foundations.Program.G32Native.ActualStalkChartTransport
import HodgeLean.Foundations.TubularEuler.RetainedConormalDifferentialHelpers

/-! # Actual affine conormal covectors under ambient chart changes

Tensor generators are evaluated by their original ideal sections. The same
affine comparison identifies the retained conormal fibre in both charts.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

/-- The original affine conormal tensor differential transforms by the actual
ambient chart derivative, with the affine point and tensor presentation fixed.
Source: `affineConormalTensorDifferential_regular_section` and
`actualStalkDifferential_change_chart`; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance. -/
theorem affineConormalTensorDifferential_change_chart
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z z' : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (hz' : Point.map j x ∈ (chartAt (Fin d → ℂ) z').source) :
    let ρ := (j.left.app A ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ A) x hx ≫ (hA.preimage j.left).isoSpec.hom)).hom
    letI : Algebra Γ(X.left, A) ℂ := ρ.toAlgebra
    ∀ t : ℂ ⊗[Γ(X.left, A)] (RingHom.ker (j.left.app A).hom).Cotangent,
      affineConormalTensorDifferential X Y j d A hA x hx z hz t =
        (affineConormalTensorDifferential X Y j d A hA x hx z' hz' t).comp
          (fderiv ℂ (fun a => (chartAt (Fin d → ℂ) z')
            ((chartAt (Fin d → ℂ) z).symm a))
            ((chartAt (Fin d → ℂ) z) (Point.map j x))) := by
  intro ρ
  letI : Algebra Γ(X.left, A) ℂ := ρ.toAlgebra
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, ContinuousLinearMap.zero_comp]
  | tmul c a =>
    obtain ⟨u, rfl⟩ := (RingHom.ker (j.left.app A).hom).toCotangent_surjective a
    rw [affineConormalTensorDifferential_regular_section,
      affineConormalTensorDifferential_regular_section]
    have hdiff := actualStalkDifferential_change_chart X d z z' (Point.map j x) hz hz'
      (X.left.presheaf.germ A (Point.map j x).underlying hx u.val)
    rw [actualStalkDifferential_eq_section, actualStalkDifferential_eq_section] at hdiff
    apply ContinuousLinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] using
      congrArg (fun D : (Fin d → ℂ) →L[ℂ] ℂ => c • D v) hdiff
  | add s t hs ht =>
    simp only [map_add, ContinuousLinearMap.add_comp, hs, ht]

#print axioms affineConormalTensorDifferential_change_chart

/-- Ambient chart covariance on the original retained conormal fibre, using
the same affine fibre comparison on both sides.
Source: `affineConormalTensorDifferential_change_chart` and the definition
`retainedAffineConormalDifferential`; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance. -/
theorem retainedAffineConormalDifferential_change_chart
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z z' : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (hz' : Point.map j x ∈ (chartAt (Fin d → ℂ) z').source)
    (a : BundleThom.i1_conormalFibre j.left x) :
    retainedAffineConormalDifferential X Y j d A hA x hx z hz a =
      (retainedAffineConormalDifferential X Y j d A hA x hx z' hz' a).comp
        (fderiv ℂ (fun b => (chartAt (Fin d → ℂ) z')
          ((chartAt (Fin d → ℂ) z).symm b))
          ((chartAt (Fin d → ℂ) z) (Point.map j x))) := by
  let ρ := (j.left.app A ≫ Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ A) x hx ≫ (hA.preimage j.left).isoSpec.hom)).hom
  letI : Algebra Γ(X.left, A) ℂ := ρ.toAlgebra
  exact affineConormalTensorDifferential_change_chart X Y j d A hA x hx z z' hz hz'
    ((actualConormalFibreAffineCotangentIso j.left A hA x hx).toLinearEquiv a)

#print axioms retainedAffineConormalDifferential_change_chart

end HodgeLean.Foundations.TubularEuler
