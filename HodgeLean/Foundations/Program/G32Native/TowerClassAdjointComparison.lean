import HodgeLean.Foundations.Program.G32Native.TowerOrbitNeighbourhoods

/-! # Actual supported classes and the retained adjoint

The geometric projection equation is an explicit argument. Its source and target
are the actual normalized representatives of the actual algebraic pushforward.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native

/-- Perfectness and adjunction turn the geometric projection equation for actual
normalized representatives into equality with the specified adjoint.
Source: Schoen (1988), printed p. 18; Fulton, Intersection Theory, 19.1–19.2. -/
theorem tower_normalized_push_eq_adjoint
    {W W₀ : Over (Spec ↧ℂ)} (φ : W ⟶ W₀) [QuasiCompact φ.left]
    (k : ℕ)
    (trr : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W))
      (2 * (2 * k)) →ₗ[ℚ] ℚ)
    (tr₀ : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀))
      (2 * (2 * k)) →ₗ[ℚ] ℚ)
    (hperfect : Function.Bijective (s2e_middlePairing (TopCat.of (ComplexPoint W₀)) k tr₀))
    (G : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * k) →ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (2 * k))
    (hadjoint : ∀ u v,
      s2e_middlePairing (TopCat.of (ComplexPoint W₀)) k tr₀ (G u) v =
      s2e_middlePairing (TopCat.of (ComplexPoint W)) k trr u (s2e_pullback ℚ φ (2 * k) v))
    (γ : AlgebraicCycle W.left ℚ)
    (cr : s2e_supportedClass W γ k)
    (c₀ : s2e_supportedClass W₀ (a1p_pushforward φ.left γ) k)
    (hprojection : ∀ v,
      s2e_middlePairing (TopCat.of (ComplexPoint W₀)) k tr₀
        (s2e_classToAbsolute W₀ (a1p_pushforward φ.left γ) k c₀) v =
      s2e_middlePairing (TopCat.of (ComplexPoint W)) k trr
        (s2e_classToAbsolute W γ k cr) (s2e_pullback ℚ φ (2 * k) v)) :
    s2e_classToAbsolute W₀ (a1p_pushforward φ.left γ) k c₀ =
      G (s2e_classToAbsolute W γ k cr) := by
  apply hperfect.1
  apply LinearMap.ext
  intro v
  exact (hprojection v).trans (hadjoint _ v).symm

end HodgeLean.Foundations.Program.G32Native
