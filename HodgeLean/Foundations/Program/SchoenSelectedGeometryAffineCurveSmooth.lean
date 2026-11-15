import HodgeLean.Foundations.Program.SchoenSelectedGeometryAffineCurveEtale
import HodgeLean.Foundations.Program.SchoenSelectedGeometryPolynomialCentering
import Mathlib.RingTheory.RingHom.Finite

noncomputable section
set_option maxHeartbeats 400000
open Set Topology AlgebraicGeometry ComplexAlgHom
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- A finite flat integral affine curve with a locally injective parameter map is smooth at the marked evaluation.
Source: translation to the origin and the local etaleness criterion for affine curves. -/
theorem s0_affine_curve_smooth_of_locally_injective
    {n : ℕ} (S : Type) [CommRing S] [IsDomain S] [Ring.DimensionLEOne S]
    [Algebra ℂ S] [Algebra (complexPolynomialRing n) S]
    [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Module.Finite (complexPolynomialRing n) S] [Module.Flat (complexPolynomialRing n) S]
    (w₀ : S →ₐ[ℂ] ℂ) [Filter.NeBot (𝓝[≠] w₀)]
    (N : Set (S →ₐ[ℂ] ℂ)) (hN : IsOpen N) (hwN : w₀ ∈ N)
    (hi : Set.InjOn (fun w : S →ₐ[ℂ] ℂ ↦
      w.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) S)) N) :
    letI : (RingHom.ker w₀).IsPrime := RingHom.ker_isPrime w₀
    Algebra.IsSmoothAt ℂ (RingHom.ker w₀) := by
  let A := complexPolynomialRing n
  let φ : A →ₐ[ℂ] S := IsScalarTower.toAlgHom ℂ A S
  let a : Fin n → ℂ := fun j ↦ w₀ (φ (MvPolynomial.X j))
  let e := s0_polynomial_centering_equiv a
  let ψ : A →ₐ[ℂ] S := φ.comp e.toAlgHom
  have hfin : ψ.toRingHom.Finite :=
    (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite A S)).comp e.toRingEquiv.finite
  have hflat : ψ.toRingHom.Flat :=
    (RingHom.Flat.of_bijective e.bijective).comp
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat A S))
  have hiφ : Set.InjOn (fun w : S →ₐ[ℂ] ℂ ↦ w.comp φ) N := hi
  letI : Algebra A S := ψ.toAlgebra
  letI : IsScalarTower ℂ A S := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  letI : Module.Finite A S := hfin
  letI : Module.Flat A S := hflat
  letI : Module.FinitePresentation A S := Module.finitePresentation_of_finite A S
  have hzero : w₀.comp (IsScalarTower.toAlgHom ℂ A S) = MvPolynomial.aeval (0 : Fin n → ℂ) := by
    apply MvPolynomial.algHom_ext
    intro j
    change w₀ (φ (e (MvPolynomial.X j))) =
      (MvPolynomial.aeval (R := ℂ) (0 : Fin n → ℂ)) (MvPolynomial.X j)
    have heX : e (MvPolynomial.X j) = MvPolynomial.X j - MvPolynomial.C (a j) := by
      simp [e, s0_polynomial_centering_equiv]
    rw [heX, map_sub, map_sub]
    have hC : φ (MvPolynomial.C (a j)) = algebraMap ℂ S (a j) := φ.commutes (a j)
    rw [hC, w₀.commutes]
    simp [a]
  have hiψ : Set.InjOn (fun w : S →ₐ[ℂ] ℂ ↦ w.comp (IsScalarTower.toAlgHom ℂ A S)) N := by
    intro u hu v hv huv
    apply hiφ hu hv
    apply AlgHom.ext
    intro r
    have hr := congrArg (fun f : A →ₐ[ℂ] ℂ ↦ f (e.symm r)) huv
    change u (φ (e (e.symm r))) = v (φ (e (e.symm r))) at hr
    change u (φ r) = v (φ r)
    simpa only [AlgEquiv.apply_symm_apply] using hr
  letI : (RingHom.ker w₀).IsPrime := RingHom.ker_isPrime w₀
  letI : Algebra.IsEtaleAt A (RingHom.ker w₀) :=
    s0_affine_curve_etale_at_zero S w₀ hzero N hN hwN hiψ
  exact Algebra.FormallySmooth.comp ℂ A (Localization.AtPrime (RingHom.ker w₀))

#print axioms s0_affine_curve_smooth_of_locally_injective
end HodgeLean.Foundations.Program
