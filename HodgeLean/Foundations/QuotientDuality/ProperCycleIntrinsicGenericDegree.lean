import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicClassProperties
import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericOpenHomologyDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothHolomorphicChart

/-! # Actual intrinsic class degrees on generic finite etale opens -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The original intrinsic global classes have their actual residue-degree pushforward whenever the generic finite etale calculation is based in one original holomorphic target chart.
Source: Fulton, Intersection Theory, section 1.4; properCycle_generic_open_residue_homology_degree.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_generic_open_degree
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [IsProjective X.hom] [IsProjective Y.hom] (f : X ⟶ Y)
    (d : ℕ) (hdimX : topologicalKrullDim X.left = (d : ℕ))
    (hdimY : topologicalKrullDim Y.left = (d : ℕ))
    (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f.left ⁻¹ᵁ U)]
    [IsFinite (f.left ∣_ U)] [Etale (f.left ∣_ U)]
    (y : ComplexPoint (openScheme Y U))
    (e : OpenPartialHomeomorph (ComplexPoint Y) (Fin d → ℂ))
    (hy : Point.map (openInclusion Y U) y ∈ e.source)
    (he : ∀ i, (f4_analytification Y).IsHolFun (fun z : e.source => e z i)) :
    homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap f))
      (properCycle_intrinsic_class X d hdimX) =
    (a1p_degree f.left (genericPoint X.left) : ℚ) • properCycle_intrinsic_class Y d hdimY := by
  exact properCycle_generic_open_residue_homology_degree X Y f hg U hU d y
    (properCycle_intrinsic_class X d hdimX) (properCycle_intrinsic_class Y d hdimY)
    (properCycle_intrinsic_class_chart X d hdimX)
    (properCycle_intrinsic_class_chart Y d hdimY)
    (properCycle_intrinsic_homology_finrank Y d hdimY) e hy he

/-- For a smooth target the original algebraic local chart supplies the target chart in the generic finite etale intrinsic degree comparison.
Source: SGA 1, Expose XII, Proposition 3.1; Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_generic_open_degree_smooth_target
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [IsProjective X.hom] [IsProjective Y.hom] (f : X ⟶ Y)
    (d : ℕ) [SmoothOfRelativeDimension d Y.hom]
    (hdimX : topologicalKrullDim X.left = (d : ℕ))
    (hdimY : topologicalKrullDim Y.left = (d : ℕ))
    (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f.left ⁻¹ᵁ U)]
    [IsFinite (f.left ∣_ U)] [Etale (f.left ∣_ U)]
    (y : ComplexPoint (openScheme Y U)) :
    homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap f))
      (properCycle_intrinsic_class X d hdimX) =
    (a1p_degree f.left (genericPoint X.left) : ℚ) • properCycle_intrinsic_class Y d hdimY := by
  let y' := Point.map (openInclusion Y U) y
  exact properCycle_intrinsic_generic_open_degree X Y f d hdimX hdimY hg U hU y
    (ComplexPoint.localChart Y d y') (ComplexPoint.mem_localChart_source Y d y')
    (properCycle_smooth_local_chart_holomorphic Y d y')

end HodgeLean.Foundations.QuotientDuality
