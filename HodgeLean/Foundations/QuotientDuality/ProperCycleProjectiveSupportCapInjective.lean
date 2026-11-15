import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveSupportDimensionTriangulation
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriangulatedCapInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedMaps

/-! # Actual supported cap injectivity on original projective algebraic supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar cap on a dimension-bounded original projective algebraic support is injective under the specified ambient orientation-line and concentration data, without ambient smoothness.
Source: properCycle_projective_support_dimension_triangulation; properCycle_triangulated_support_cap_injective.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_algebraic_support_cap_injective
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] [LocallyOfFiniteType X.hom]
    [NoetherianSpace X.left] (S : Closeds X.left) (d : ℕ) (hdim : topologicalKrullDim S ≤ d)
    (C : ProperCycleSupportCollar (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left)))
    (p : ℕ) (hp : Even p) (c : Homology ℚ (TopCat.of (ComplexPoint X)) (p+2*d))
    (hlocal : ∀ x, Function.Bijective (orientationLine (TopCat.of (ComplexPoint X)) (p+2*d) c x))
    (hvan : ∀ j : ℕ, j ≠ p+2*d → ∀ x : ComplexPoint X,
      Subsingleton (orientationGroup (TopCat.of (ComplexPoint X)) j x)) :
    Function.Injective (C.cap (S.isClosed.preimage (continuous_underlying_to_zariski X)) p (2*d) c) := by
  classical
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  obtain ⟨a, K, D, hK, hD, hDK, e, hmark, hdimD⟩ :=
    properCycle_projective_support_dimension_triangulation X S d hdim
  letI : LinearOrder (EuclideanSpace ℝ (Fin a)) := IsWellOrder.linearOrder WellOrderingRel
  have hvfinite : K.vertices.Finite :=
    Set.Finite.preimage (fun _ _ _ _ he => Finset.singleton_injective he) hK
  let V := hvfinite.toFinset
  have hV : ∀ b ∈ K.vertices, b ∈ V := fun b hb => hvfinite.mem_toFinset.mpr hb
  exact properCycle_triangulated_support_cap_injective (TopCat.of (ComplexPoint X))
    (Point.underlying ⁻¹' (S : Set X.left)) (S.isClosed.preimage (continuous_underlying_to_zariski X))
    C K D hK hDK V hV e hmark p (2*d) hp hdimD c hlocal hvan

end HodgeLean.Foundations.QuotientDuality
