import HodgeLean.Foundations.Program.SchoenSelectedGeometrySpecSmoothPoint

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint ComplexAlgHom Set Topology
namespace HodgeLean.Foundations.Program

/-- A locally injective finite flat line coordinate gives scheme smoothness at its marked evaluation. -/
theorem s0_finite_flat_line_spec_smooth_at
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra (complexPolynomialRing 1) S] [IsScalarTower ℂ (complexPolynomialRing 1) S]
    [Module.Finite (complexPolynomialRing 1) S] [Module.Flat (complexPolynomialRing 1) S]
    [Algebra.FinitePresentation ℂ S]
    (w : S →ₐ[ℂ] ℂ) [Filter.NeBot (𝓝[≠] w)]
    (N : Set (S →ₐ[ℂ] ℂ)) (hN : IsOpen N) (hw : w ∈ N)
    (hi : Set.InjOn (fun z : S →ₐ[ℂ] ℂ ↦
      z.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing 1) S)) N) :
    letI := s0_affine_spec_finite_presentation S
    ((affineSpecEquiv S).symm w).underlying ∈ (affineSpecStructureMap S).smoothLocus := by
  letI := s0_affine_spec_finite_presentation S
  letI : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
  letI := s0_finite_flat_line_algebra_smooth_at S w N hN hw hi
  have hp : ((affineSpecEquiv S).symm w).underlying =
      (⟨RingHom.ker w, inferInstance⟩ : PrimeSpectrum S) := by
    apply PrimeSpectrum.ext
    change Ideal.comap w.toRingHom (IsLocalRing.maximalIdeal ℂ) = RingHom.ker w
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  rw [hp]
  exact s0_spec_mem_smoothLocus S ⟨RingHom.ker w, inferInstance⟩

#print axioms s0_finite_flat_line_spec_smooth_at
end HodgeLean.Foundations.Program
