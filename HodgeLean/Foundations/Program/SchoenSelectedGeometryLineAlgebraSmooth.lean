import HodgeLean.Foundations.Program.SchoenSelectedGeometryAffineCurveSmooth

noncomputable section
set_option maxHeartbeats 400000
open Set Topology AlgebraicGeometry ComplexAlgHom
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- A finite flat domain over the complex affine line is smooth at every nonisolated locally injective evaluation.
Source: dimension at most one under integral extensions and the affine curve smoothness criterion. -/
theorem s0_finite_flat_line_algebra_smooth_at
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra (complexPolynomialRing 1) S] [IsScalarTower ℂ (complexPolynomialRing 1) S]
    [Module.Finite (complexPolynomialRing 1) S] [Module.Flat (complexPolynomialRing 1) S]
    (w : S →ₐ[ℂ] ℂ) [Filter.NeBot (𝓝[≠] w)]
    (N : Set (S →ₐ[ℂ] ℂ)) (hN : IsOpen N) (hw : w ∈ N)
    (hi : Set.InjOn (fun z : S →ₐ[ℂ] ℂ ↦
      z.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing 1) S)) N) :
    letI : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
    Algebra.IsSmoothAt ℂ (RingHom.ker w) := by
  letI : Ring.DimensionLEOne (complexPolynomialRing 1) :=
    Ring.DimensionLEOne.of_ringEquiv (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toRingEquiv
  letI : Ring.DimensionLEOne S := Ring.DimensionLEOne.of_isIntegral (complexPolynomialRing 1) S
  exact s0_affine_curve_smooth_of_locally_injective S w N hN hw hi

#print axioms s0_finite_flat_line_algebra_smooth_at
end HodgeLean.Foundations.Program
