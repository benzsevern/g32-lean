import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveSupportCapIndependence
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollaredSupportCapNaturality

/-! # Actual global support cap naturality on original projective supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual global projective support cap intertwines the literal analytic support inclusion and the original cohomological enlargement map.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of supported cap products; actual projective support-fixing collars.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_support_cap_enlarge_support
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S T : Closeds X.left)
    (hST : (Point.underlying ⁻¹' (S : Set X.left) : Set (ComplexPoint X)) ⊆
      Point.underlying ⁻¹' (T : Set X.left))
    (p q : ℕ) (c : Homology ℚ (TopCat.of (ComplexPoint X)) (p+q))
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left)) p) :
    homologyMap ℚ q (TopCat.ofHom (ContinuousMap.inclusion hST))
      (properCycle_projective_support_cap X S p q c a) =
      properCycle_projective_support_cap X T p q c
        (enlargeSupport ℚ (TopCat.of (ComplexPoint X)) hST p a) := by
  let C := properCycle_projective_strong_support_collar X S
  let D := properCycle_projective_support_collar X T
  have he := LinearMap.congr_fun
    (properCycle_projective_support_cap_eq_collar X S C.collar p q c) a
  calc
    _ = homologyMap ℚ q (TopCat.ofHom (ContinuousMap.inclusion hST))
        (C.collar.cap (S.isClosed.preimage (continuous_underlying_to_zariski X)) p q c a) :=
      congrArg (homologyMap ℚ q (TopCat.ofHom (ContinuousMap.inclusion hST))) he
    _ = D.cap (T.isClosed.preimage (continuous_underlying_to_zariski X)) p q c
        (enlargeSupport ℚ (TopCat.of (ComplexPoint X)) hST p a) :=
      properCycle_collared_support_cap_enlargement hST C.collar D C.fixed
        (S.isClosed.preimage (continuous_underlying_to_zariski X))
        (T.isClosed.preimage (continuous_underlying_to_zariski X)) p q c a
    _ = _ := rfl

end HodgeLean.Foundations.QuotientDuality
