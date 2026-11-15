import HodgeLean.RealDefs.FundamentalClass.Point
import HodgeLean.Foundations.QuotientDuality.LocalOrientationNaturality
import HodgeLean.RealDefs.ComplexFundamentalClass

/-! Absolute singular fundamental classes of the smooth projective source schemes. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem smooth_projective_absolute_fundamental
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∃ c : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d),
      ∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) c x =
        complexLocalOrientation X d x := by
  obtain ⟨w, hw⟩ := j5c_exists_complexFundamentalClass X d
  let A := TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
    ((((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ) : Set (ComplexPoint X))
  letI : IsIso (relativeChainProjection ℚ A) :=
    isIso_relativeChainProjection _ ⟨fun y => y.2 trivial⟩
  letI : IsIso (relativeHomologyProjection ℚ A (2 * d)) := by
    unfold relativeHomologyProjection
    infer_instance
  have hproj : Function.Bijective (relativeHomologyProjection ℚ A (2 * d)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  obtain ⟨c, hc⟩ := hproj.2 w
  refine ⟨c, fun x => ?_⟩
  have hn := relativeHomologyProjection_map (2 * d)
    (supportInclusionPairMap (TopCat.of (ComplexPoint X))
      (Set.singleton_subset_iff.mpr (Opens.mem_top x))) c
  have hi : (supportInclusionPairMap (TopCat.of (ComplexPoint X))
      (Set.singleton_subset_iff.mpr (Opens.mem_top x))).hom.right =
      𝟙 (TopCat.of (ComplexPoint X)) := rfl
  rw [hi] at hn
  erw [homologyMap_id] at hn
  exact hn.symm.trans ((congrArg (relativeHomologyMap ℚ (2 * d)
    (supportInclusionPairMap (TopCat.of (ComplexPoint X))
      (Set.singleton_subset_iff.mpr (Opens.mem_top x)))) hc).trans (hw x))

#print axioms smooth_projective_absolute_fundamental
end HodgeLean.Foundations.QuotientDuality
