import HodgeLean.Foundations.QuotientDuality.LocalCoherentSmoothNormalization
import Mathlib.AlgebraicGeometry.Noetherian
import HodgeLean.Foundations.QuotientDuality.LocalSmoothLocusNormalization
import HodgeLean.Foundations.QuotientDuality.LocalImmersionChartNormalization
import HodgeLean.Foundations.QuotientDuality.LocalDenseChartCalibration
import HodgeLean.Foundations.AnalyticDivisorAlgebraic24Proofs

/-! Normalize an actual global orientation class in all holomorphic topological charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem normalize_coherent_complex_orientation
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d)) :
    ∃ o' : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d),
      ∀ (x : ComplexPoint X) (F : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
        (hx : x ∈ F.source),
        (∀ i, (f4_analytification X).IsHolFun (fun y : F.source => F y i)) →
        o'.generator x = localClassOfChart d F x hx := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : IsNoetherian X.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.hom }
  obtain ⟨I, hI⟩ := normalize_coherent_orientation_on_smooth_locus X d o
  letI := I
  obtain ⟨o', hμ⟩ := hI
  let U := X.hom.smoothLocus
  let A := openScheme X U
  let j := openInclusion X U
  letI : LocallyOfFiniteType A.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : NoetherianSpace X.left := IsNoetherian.noetherianSpace
  letI : NoetherianSpace A.left := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : QuasiCompact A.hom := inferInstance
  letI : IsSeparated A.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  obtain ⟨a, ha⟩ := X.hom.dense_smoothLocus_of_perfectField.nonempty
  letI : Nonempty U := ⟨⟨a, ha⟩⟩
  have hS := HodgeLean.Foundations.AnalyticDivisorAlgebraic24.gaga24_dense_overOpen X U
  refine ⟨o', ?_⟩
  intro x F hx hF
  apply chart_orientation_normalized_of_dense (TopCat.of (ComplexPoint X)) d o'
    (Point.overOpen U) hS F x hx
  intro y hySmooth hyChart
  let z := asOpenPoint X U y hySmooth
  have hz : Point.map j z = y :=
    congrArg Subtype.val ((openHomeomorph X U).apply_symm_apply ⟨y, hySmooth⟩)
  have hzF : Point.map j z ∈ F.source := by
    rw [hz]
    exact chartOrientationNeighborhood_subset_source d F x hx hyChart
  have hn := immersion_complex_orientation_holomorphic_chart A X d j o' hμ F hF z hzF
  have he : (⟨Point.map j z, hzF⟩ : F.source) =
      ⟨y, chartOrientationNeighborhood_subset_source d F x hx hyChart⟩ := Subtype.ext hz
  exact Eq.mp (congrArg (fun p : F.source =>
    o'.generator p.val = localClassOfChart d F p.val p.property) he) hn

#print axioms normalize_coherent_complex_orientation
end HodgeLean.Foundations.QuotientDuality
