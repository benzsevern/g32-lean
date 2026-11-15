import HodgeLean.Foundations.QuotientDuality.MonomialAffineAlgebraicAction
import HodgeLean.Foundations.QuotientDuality.MonomialAffineOrbitFibers
import HodgeLean.Foundations.QuotientDuality.LocalFiniteSmoothQuotient

/-! Coherent local orientations on affine normalizations with a smooth invariant presentation. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem affine_invariant_presentation_coherent_orientation
    {N A G : Type} [CommRing N] [CommRing A] [Algebra ℂ N] [Algebra ℂ A]
    [Algebra.FiniteType ℂ N] [Algebra.FiniteType ℂ A]
    [Group G] [Finite G] (d : ℕ) [SmoothOfRelativeDimension d (affineSpecStructureMap A)]
    (ρ : G →* (A ≃ₐ[ℂ] A)) (β : N →ₐ[ℂ] A)
    (hβ : Function.Injective β) (hfinite : β.toRingHom.Finite)
    (hfixed : ∀ a : A, (∃ b, β b = a) ↔ ∀ g, ρ g a = a) :
    Nonempty (LocalRationalOrientation
      (TopCat.of (ComplexPoint (Over.mk (affineSpecStructureMap N)))) (2 * d)) := by
  let X := Over.mk (affineSpecStructureMap A)
  let Y := Over.mk (affineSpecStructureMap N)
  letI : SmoothOfRelativeDimension d X.hom :=
    inferInstanceAs (SmoothOfRelativeDimension d (affineSpecStructureMap A))
  letI : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  letI : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of N)))
  letI : LocallyOfFiniteType X.hom := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : LocallyOfFiniteType Y.hom := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Fintype G := Fintype.ofFinite G
  letI := affineAutomorphismPointAction ρ
  obtain ⟨hcont, σ, hσ⟩ := affine_action_algebraic_and_continuous ρ
  letI := hcont
  let q : X ⟶ Y := Over.homMk (Spec.map (CommRingCat.ofHom β.toRingHom))
    (specMap_comp_affineSpecStructureMap β)
  letI : IsFinite q.left := (IsFinite.SpecMap_iff _).mpr hfinite
  have hint : β.toRingHom.IsIntegral := by
    letI : Algebra N A := β.toRingHom.toAlgebra
    letI : Module.Finite N A := hfinite
    exact algebraMap_isIntegral_iff.mpr inferInstance
  letI : Surjective q.left := ⟨hint.comap_surjective hβ⟩
  apply finite_smooth_quotient_coherent_orientation X Y d G σ hσ q (f4_map_surjective q)
  · intro g x
    apply (affineSpecEquiv N).injective
    change affineSpecEquiv N (affineSpecComplexPointMap β
      (affineSpecComplexPointMap (ρ g⁻¹).toAlgHom x)) =
        affineSpecEquiv N (affineSpecComplexPointMap β x)
    simp only [affineSpecEquiv_affineSpecComplexPointMap]
    ext b
    exact congrArg (affineSpecEquiv A x) ((hfixed (β b)).mp ⟨b, rfl⟩ g⁻¹)
  · intro x y hxy
    obtain ⟨g, hg⟩ := affine_invariant_presentation_orbit_fibers ρ β hfixed x y hxy
    refine ⟨g⁻¹, ?_⟩
    change affineSpecComplexPointMap (ρ (g⁻¹)⁻¹).toAlgHom x = y
    simpa only [inv_inv] using hg

#print axioms affine_invariant_presentation_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
