import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Foundations.QuotientDuality.LocalCompactComplexHomologyBound
import HodgeLean.Foundations.QuotientDuality.LocalOpenHomologyCompactBound
import HodgeLean.Foundations.QuotientDuality.LocalCompactDetection
import HodgeLean.Foundations.QuotientDuality.LocalCompactGluing
import HodgeLean.Foundations.AnalyticDivisorAlgebraic24Proofs

/-! Absolute fundamental classes for coherent orientations on compact complex schemes. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem compact_complex_coherent_orientation_absolute_class
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [CompactSpace (ComplexPoint X)] (n : ℕ)
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) n) :
    ∃ c : Homology ℚ (TopCat.of (ComplexPoint X)) n,
      ∀ x, localOrientation (TopCat.of (ComplexPoint X)) n c x = o.generator x := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  obtain ⟨N, hN⟩ := compact_complex_open_homology_bound X
  have hd := compact_detection_of_uniform_bound (TopCat.of (ComplexPoint X)) n (N + 1)
    (fun x i hi => o.vanishes x i (by omega))
    (fun A hA i hi => open_homology_compact_support_bound
      (TopCat.of (ComplexPoint X)) N hN A hA i hi)
  obtain ⟨c, hc, _⟩ := fundamental_class_of_compact_detection
    (TopCat.of (ComplexPoint X)) n o hd
  exact ⟨c, hc⟩

#print axioms compact_complex_coherent_orientation_absolute_class
end HodgeLean.Foundations.QuotientDuality
