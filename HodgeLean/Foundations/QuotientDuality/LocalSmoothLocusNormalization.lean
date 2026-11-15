import HodgeLean.Foundations.QuotientDuality.LocalConnectedFamilyNormalization
import HodgeLean.Foundations.QuotientDuality.LocalImmersionOrientationFamily
import HodgeLean.Foundations.QuotientDuality.LocalChartDimension
import HodgeLean.Foundations.Connected
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! Normalize a coherent global orientation against the canonical complex smooth-locus family. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem normalize_orientation_on_smooth_locus
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (c : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d))
    (hc : ∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) c x = o.generator x) :
    ∃ I : SmoothOfRelativeDimension d (openScheme X X.hom.smoothLocus).hom,
      letI := I
      ∃ (o' : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
        (c' : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d)),
        (∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) c' x = o'.generator x) ∧
        ∀ z : ComplexPoint (openScheme X X.hom.smoothLocus),
          o'.generator (Point.map (openInclusion X X.hom.smoothLocus) z) =
            immersionComplexOrientation (openScheme X X.hom.smoothLocus) X d
              (openInclusion X X.hom.smoothLocus) z := by
  classical
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  let U := X.hom.smoothLocus
  let S := openScheme X U
  obtain ⟨a, ha⟩ := X.hom.dense_smoothLocus_of_perfectField.nonempty
  letI : Nonempty U := ⟨⟨a, ha⟩⟩
  letI : Nonempty S.left := inferInstanceAs (Nonempty U)
  letI : IsIntegral S.left := isIntegral_of_isOpenImmersion U.ι
  letI : Smooth S.hom := X.hom.smooth_restrict_smoothLocus
  letI : IsSeparated S.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  letI : QuasiSeparatedSpace S.left := quasiSeparatedSpace_of_quasiSeparated S.hom
  letI : ConnectedSpace (ComplexPoint S) := ComplexPoint.connectedSpace S
  let z := Classical.choice (inferInstance : Nonempty (ComplexPoint S))
  let j := openInclusion X U
  let hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  let k := dim S.left
  let E := (localChart S k z).lift_openEmbedding hj
  have hz : Point.map j z ∈ E.source := ⟨z, mem_localChart_source S k z, rfl⟩
  have hdim : d = k := by
    have h := localOrientation_degree_eq_chart_dimension (TopCat.of (ComplexPoint X))
      (2 * d) o k E (Point.map j z) hz
    omega
  letI : SmoothOfRelativeDimension d S.hom := by rw [hdim]; infer_instance
  refine ⟨inferInstance, ?_⟩
  exact normalize_global_orientation_on_connected_family (TopCat.of (ComplexPoint X)) (2 * d) o c hc
    (ComplexPoint S) (Point.map j) (Point.continuous_map j)
    (immersionComplexOrientation S X d j)
    (immersionComplexOrientation_ne_zero S X d j)
    (immersionComplexOrientation_locally_represented S X d j)

#print axioms normalize_orientation_on_smooth_locus
end HodgeLean.Foundations.QuotientDuality
