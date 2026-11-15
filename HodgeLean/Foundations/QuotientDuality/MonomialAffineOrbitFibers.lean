import HodgeLean.Foundations.QuotientDuality.MonomialInvariantEvaluationOrbits
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

/-! Orbit fibers on the actual complex points of an affine invariant presentation. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

theorem affine_invariant_presentation_orbit_fibers
    {N A G : Type} [CommRing N] [CommRing A] [Algebra ℂ N] [Algebra ℂ A]
    [Group G] [Finite G]
    (ρ : G →* (A ≃ₐ[ℂ] A)) (β : N →ₐ[ℂ] A)
    (hfixed : ∀ a : A, (∃ b, β b = a) ↔ ∀ g, ρ g a = a)
    (x y : ComplexPoint (CategoryTheory.Over.mk (affineSpecStructureMap A)))
    (heq : affineSpecComplexPointMap β x = affineSpecComplexPointMap β y) :
    ∃ g : G, affineSpecComplexPointMap (ρ g).toAlgHom x = y := by
  have heval := congrArg (affineSpecEquiv N) heq
  rw [affineSpecEquiv_affineSpecComplexPointMap,
    affineSpecEquiv_affineSpecComplexPointMap] at heval
  obtain ⟨g, hg⟩ := invariant_presentation_evaluation_orbits ρ β.toRingHom hfixed
    (affineSpecEquiv A x) (affineSpecEquiv A y) (fun b => AlgHom.congr_fun heval b)
  refine ⟨g, (affineSpecEquiv A).injective ?_⟩
  rw [affineSpecEquiv_affineSpecComplexPointMap]
  ext a
  exact (hg a).symm

#print axioms affine_invariant_presentation_orbit_fibers
end HodgeLean.Foundations.QuotientDuality
