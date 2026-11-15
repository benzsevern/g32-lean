import HodgeLean.Foundations.QuotientDuality.LocalImmersionHolomorphicCharts
import HodgeLean.Foundations.QuotientDuality.LocalChartEmbedding
import HodgeLean.Foundations.QuotientDuality.LocalSmoothOrientation

/-! The complex local orientation family of a smooth open subscheme in its ambient space. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

instance canonicalOpenInclusion_isOpenImmersion (X : Over (Spec ↧ℂ)) (U : X.left.Opens) :
    IsOpenImmersion (openInclusion X U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

variable (A X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (j : A ⟶ X) [IsOpenImmersion j.left]

def immersionComplexOrientation (z : ComplexPoint A) :
    orientationGroup (TopCat.of (ComplexPoint X)) (2 * d) (Point.map j z) :=
  relativeHomologyMap ℚ (2 * d)
    (imagePointPairMap (TopCat.ofHom (Point.continuousMap j))
      (HodgeLean.Foundations.ComplexTopology.openImmersion_points j).injective z)
    (complexLocalOrientation A d z)

theorem immersionComplexOrientation_ne_zero [T1Space (ComplexPoint X)] (z : ComplexPoint A) :
    immersionComplexOrientation A X d j z ≠ 0 := by
  let hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  have h : immersionComplexOrientation A X d j z =
      localClassOfChart d ((localChart A d z).lift_openEmbedding hj)
        (Point.map j z) ⟨z, mem_localChart_source A d z, rfl⟩ := by
    convert localClassOfChart_lift_openEmbedding (Point.map j) hj d (localChart A d z) z
      (mem_localChart_source A d z) using 1 <;> rfl
  intro hz
  exact localClassOfChart_ne_zero d ((localChart A d z).lift_openEmbedding hj)
    (Point.map j z) ⟨z, mem_localChart_source A d z, rfl⟩ (h.symm.trans hz)

theorem immersionComplexOrientation_locally_represented (z : ComplexPoint A) :
    ∃ (U : Opens (ComplexPoint X)), Point.map j z ∈ U ∧
      ∃ w : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
          (U : Set (ComplexPoint X))ᶜ) (2 * d),
        ∀ (t : ComplexPoint A) (ht : Point.map j t ∈ U),
          relativeHomologyMap ℚ (2 * d) (supportInclusionPairMap
            (TopCat.of (ComplexPoint X)) (Set.singleton_subset_iff.mpr ht)) w =
              immersionComplexOrientation A X d j t := by
  let hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  let E := localChart A d z
  let F := E.lift_openEmbedding hj
  have hz : Point.map j z ∈ F.source := ⟨z, mem_localChart_source A d z, rfl⟩
  refine ⟨chartOrientationNeighborhood d F (Point.map j z) hz,
    mem_chartOrientationNeighborhood d F (Point.map j z) hz,
    chartOrientationNeighborhoodClass d F (Point.map j z) hz, ?_⟩
  intro t ht
  have hts := chartOrientationNeighborhood_subset_source d F (Point.map j z) hz ht
  obtain ⟨v, hv, he⟩ := hts
  have hvt : v = t := hj.injective he
  subst v
  have hcan := complexLocalOrientation_eq_localClassOfChart_localChart A d z t hv
  have hlift := localClassOfChart_lift_openEmbedding (Point.map j) hj d E t hv
  exact (chartOrientationNeighborhoodClass_restrict d F (Point.map j z) hz (Point.map j t) ht).trans
    (hlift.symm.trans (congrArg (relativeHomologyMap ℚ (2 * d)
      (imagePointPairMap (TopCat.ofHom (Point.continuousMap j)) hj.injective t)) hcan.symm))

#print axioms immersionComplexOrientation_ne_zero
#print axioms immersionComplexOrientation_locally_represented
end HodgeLean.Foundations.QuotientDuality
