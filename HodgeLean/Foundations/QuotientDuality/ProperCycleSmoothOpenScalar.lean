import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedLocalCoefficients
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenSmoothOrientation
import HodgeLean.Foundations.Connected

/-! # Actual smooth-open coefficients of original ordinary top classes -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original ordinary top class has a single rational coefficient against the actual canonical orientations on an original integral smooth algebraic open.
Source: properCycle_connected_local_coefficients; properCycle_open_smooth_orientation_chart_coherence; ComplexPoint.connectedSpace.
HC no distance; AV milestone no distance. -/
theorem properCycle_smooth_open_top_class_scalar
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (U : X.left.Opens)
    [IsIntegral (openScheme X U).left] [Smooth (openScheme X U).hom]
    [QuasiCompact (openScheme X U).hom] [IsSeparated (openScheme X U).hom]
    (d : ℕ) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (c : Homology ℚ (a3b4_an X.hom) (2*d)) :
    ∃ q : ℚ, ∀ y : ComplexPoint (openScheme X U),
      localOrientation (a3b4_an X.hom) (2*d) c (Point.map (openInclusion X U) y) =
        q • properCycle_open_smooth_orientation X U d y := by
  let Y := openScheme X U
  letI : T2Space (a3b4_an X.hom) := HodgeLean.Foundations.Analytic.f4_t2Space X
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  letI := AlgebraicGeometry.ComplexPoint.connectedSpace Y
  letI : PreconnectedSpace (a3b4_an Y.hom) := inferInstanceAs (PreconnectedSpace (ComplexPoint Y))
  exact properCycle_connected_local_coefficients (a3b4_an X.hom) (a3b4_an Y.hom)
    (TopCat.ofHom (Point.continuousMap (openInclusion X U))) d
    (properCycle_open_smooth_orientation X U d)
    (properCycle_open_smooth_orientation_generates X U d)
    (properCycle_open_smooth_orientation_chart_coherence X U d) c

end HodgeLean.Foundations.QuotientDuality
