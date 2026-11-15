import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.HolomorphicRoots
import HodgeLean.Foundations.Program.SchoenCycleC11StandardHelpers

/-! # Holomorphic evaluation in étale presentations

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Set Filter Topology HodgeLean.Foundations.Analytic
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.SingularCycles

/-- Polynomial evaluation preserves holomorphic coefficient families.
Source: Grauert–Remmert, Coherent Analytic Sheaves, §1.1.5; the holomorphic subring. -/
theorem holFun_polynomial_eval {M : Type*} [TopologicalSpace M] (S : an_ReducedSpace M)
    {U : Set M} {A : Type*} [CommRing A] (e : U → (A →+* ℂ))
    (he : ∀ a, S.IsHolFun (fun y => e y a)) (r : U → ℂ) (hr : S.IsHolFun r)
    (p : Polynomial A) : S.IsHolFun (fun y => Polynomial.eval₂ (e y) (r y) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h : S.IsHolFun (fun y => Polynomial.eval₂ (e y) (r y) p +
        Polynomial.eval₂ (e y) (r y) q) := (S.atlas.holSubring U).add_mem hp hq
    simpa only [Polynomial.eval₂_add] using h
  | monomial n a =>
    have h : S.IsHolFun (fun y => e y a * r y ^ n) :=
      (S.atlas.holSubring U).mul_mem (he a) ((S.atlas.holSubring U).pow_mem hr n)
    simpa only [Polynomial.eval₂_monomial] using h

/-- Continuous simple roots remain holomorphic for an arbitrary complex coefficient algebra.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Ch. I, §B, Theorem 4. -/
theorem holFun_algebraic_simple_root {M : Type*} [TopologicalSpace M]
    (S : an_ReducedSpace M) {U : Set M} (hU : IsOpen U)
    {A : Type} [CommRing A] [Algebra ℂ A] (e : U → (A →ₐ[ℂ] ℂ))
    (he : ∀ a, S.IsHolFun (fun y => e y a)) (p : Polynomial A)
    (r : U → ℂ) (hr : Continuous r)
    (hroot : ∀ y, Polynomial.eval₂ (e y).toRingHom (r y) p = 0)
    (hsimple : ∀ y, Polynomial.eval₂ (e y).toRingHom (r y) p.derivative ≠ 0) :
    S.IsHolFun r := by
  apply holFun_of_continuous_simple_root S hU
    (s2e_c11_universalCoefficientPolynomial (p.natDegree + 1))
    (fun y => s2e_c11_coefficientParameters p (e y))
    (fun j => he (p.coeff j)) r hr
  · intro y
    change (Polynomial.mvFamilySpecialization
      (s2e_c11_universalCoefficientPolynomial (p.natDegree + 1))
      (s2e_c11_coefficientParameters p (e y))).eval (r y) = 0
    rw [s2e_c11_universalCoefficient_specialization, Polynomial.eval_map]
    exact hroot y
  · intro y
    rw [s2e_c11_universalCoefficient_specialization, Polynomial.derivative_map, Polynomial.eval_map]
    exact hsimple y

end AlgebraicGeometry.SingularCycles
