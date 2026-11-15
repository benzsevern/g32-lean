import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicDegree
import HodgeLean.Foundations.QuotientDuality.RetainedCycleStageEight

/-! # Intrinsic integration and the actual residue degree

The component images use the literal reduced inclusions and singular evaluation.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Integration on the specified intrinsic component equals evaluation on its actual ambient image. -/
theorem retained_intrinsic_integral_component_image
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (ξ : X.left) (hc : Order.coheight ξ = k)
    (u : Cohomology ℚ (a3b4_an X.hom) (2*k)) :
    orientationIntegral (a3b4_an (intrinsicComponent X ξ).hom) (2*k)
      (retainedIntrinsicFundamentalClass X k hdim ξ hc)
      (s2e_pullback ℚ (intrinsicComponentInclusion X ξ) (2*k) u) =
    cohomologyEquivDualHomology ℚ (a3b4_an X.hom) (2*k) u
      (properCycle_intrinsic_component X k ξ) := by
  rw [properCycle_intrinsic_component_eq_image X k ξ
    (properCycle_middle_component_dimension X k hdim ξ hc)]
  exact cohomologyEquivDualHomology_cohomologyMap ℚ (2*k)
    (TopCat.ofHom (Point.continuousMap (intrinsicComponentInclusion X ξ))) u
    (retainedIntrinsicFundamentalClass X k hdim ξ hc)

/-- Intrinsic integration under a proper map retains its literal residue degree. -/
theorem retained_intrinsic_degree_integral
    {W W₀ : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsIntegral W₀.left]
    [IsProjective W.hom] [IsProjective W₀.hom]
    (f : W ⟶ W₀) [IsProper f.left]
    (k : ℕ) (hdimW : TopologicalSpace.dim W.left = 2*k)
    (hdimW₀ : TopologicalSpace.dim W₀.left = 2*k)
    (ξ : W.left) (hc : Order.coheight ξ = k)
    (hd : 0 < a1p_degree f.left ξ) :
    let hcη : Order.coheight (f.left ξ) = k :=
      (properCycle_coheight_of_degree f (hdimW.trans hdimW₀.symm) ξ hd).trans hc
    ∀ u : Cohomology ℚ (a3b4_an W₀.hom) (2*k),
      orientationIntegral (a3b4_an (intrinsicComponent W ξ).hom) (2*k)
        (retainedIntrinsicFundamentalClass W k hdimW ξ hc)
        (s2e_pullback ℚ (intrinsicComponentInclusion W ξ) (2*k)
          (s2e_pullback ℚ f (2*k) u)) =
        (a1p_degree f.left ξ : ℚ) *
          orientationIntegral (a3b4_an (intrinsicComponent W₀ (f.left ξ)).hom) (2*k)
            (retainedIntrinsicFundamentalClass W₀ k hdimW₀ (f.left ξ) hcη)
            (s2e_pullback ℚ (intrinsicComponentInclusion W₀ (f.left ξ)) (2*k) u) := by
  dsimp only
  intro u
  rw [retained_intrinsic_integral_component_image W k hdimW ξ hc,
    retained_intrinsic_integral_component_image W₀ k hdimW₀ (f.left ξ)
      ((properCycle_coheight_of_degree f (hdimW.trans hdimW₀.symm) ξ hd).trans hc)]
  change cohomologyEquivDualHomology ℚ (a3b4_an W.hom) (2*k)
    (cohomologyMap ℚ (2*k) (TopCat.ofHom (Point.continuousMap f)) u)
      (properCycle_intrinsic_component W k ξ) = _
  exact (cohomologyEquivDualHomology_cohomologyMap ℚ (2*k)
    (TopCat.ofHom (Point.continuousMap f)) u (properCycle_intrinsic_component W k ξ)).trans
    ((congrArg (cohomologyEquivDualHomology ℚ (a3b4_an W₀.hom) (2*k) u)
      (properCycle_intrinsic_component_degree_aux f k hdimW hdimW₀ ξ hc)).trans
        (map_smul (cohomologyEquivDualHomology ℚ (a3b4_an W₀.hom) (2*k) u) _ _))

end HodgeLean.Foundations.QuotientDuality
