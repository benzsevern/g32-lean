import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicDegree
import HodgeLean.Foundations.QuotientDuality.RetainedCycleMiddleCapPerfect

/-! # Intrinsic integration detected by the actual middle cap -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- All rational cohomology evaluations detect equality in ordinary singular homology. -/
theorem retained_homology_eq_iff_evaluation (X : TopCat.{0}) (n : ℕ)
    (a b : Homology ℚ X n) :
    a = b ↔ ∀ u : Cohomology ℚ X n,
      cohomologyEquivDualHomology ℚ X n u a =
        cohomologyEquivDualHomology ℚ X n u b := by
  constructor
  · rintro rfl u
    rfl
  · intro h
    apply Module.eval_apply_injective ℚ
    ext f
    obtain ⟨u, rfl⟩ := (cohomologyEquivDualHomology ℚ X n).surjective f
    exact h u

/-- Intrinsic integration against every middle class is exactly the actual cap image equation. -/
theorem retained_intrinsic_integral_iff_cap_image
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (c : Homology ℚ (a3b4_an X.hom) (2*(2*k)))
    (ξ : X.left) (hc : Order.coheight ξ = k)
    (a : s2e_supportedClass X (properPrime ξ) k) :
    (∀ u : Cohomology ℚ (a3b4_an X.hom) (2*k),
      properCyclePairing (a3b4_an X.hom) k c
        (s2e_classToAbsolute X (properPrime ξ) k a) u =
      orientationIntegral (a3b4_an (intrinsicComponent X ξ).hom) (2*k)
        (retainedIntrinsicFundamentalClass X k hdim ξ hc)
        (s2e_pullback ℚ (intrinsicComponentInclusion X ξ) (2*k) u)) ↔
    retainedMiddleCapWithOrientation (a3b4_an X.hom) k c
      (s2e_classToAbsolute X (properPrime ξ) k a) =
        properCycle_intrinsic_component X k ξ := by
  rw [retained_homology_eq_iff_evaluation]
  apply forall_congr'
  intro u
  rw [retained_intrinsic_integral_component_image X k hdim ξ hc]
  change cohomologyEquivDualHomology ℚ (a3b4_an X.hom) (2*(2*k))
    (HodgeLean.Foundations.Singular.cup (a3b4_an X.hom) (by omega)
      (s2e_classToAbsolute X (properPrime ξ) k a) u) c = _ ↔ _
  rw [retained_orientation_cap_evaluation_cast]
  rfl

end HodgeLean.Foundations.QuotientDuality
