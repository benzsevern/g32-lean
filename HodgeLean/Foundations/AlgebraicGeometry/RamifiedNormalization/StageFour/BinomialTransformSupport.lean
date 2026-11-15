import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartSupportSquares
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RatioResidualRegular
import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartTensor

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- On an actual binomial blowup chart the numerator transform is the zero ratio and the denominator transform is absent. -/
theorem binomial_chart_transform_support {X B : Scheme}
    (f : X ⟶ B) (U : B.affineOpens) (u v : Γ(B, U))
    (I J : B.IdealSheafData) (hI : I.ideal U = Ideal.span {u})
    (hJ : J.ideal U = Ideal.span {v})
    (hv : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v))
    (j : Spec ↧(RegularPairChart.ring u v) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫ U.2.fromSpec) :
    j ⁻¹' ((s2c_strictTransform f I (I ⊔ J)).support : Set X) =
      PrimeSpectrum.zeroLocus {RegularPairChart.ratio u v} ∧
    j ⁻¹' ((s2c_strictTransform f J (I ⊔ J)).support : Set X) = ∅ := by
  have hrel : RegularPairChart.coeff u v u =
      RegularPairChart.ratio u v * RegularPairChart.coeff u v v :=
    RegularPairChart.chart_relation u v
  have hpreI := chart_support_coefficient_square f U u v u I hI j hj
  have hpreJ := chart_support_coefficient_square f U u v v J hJ j hj
  have hpreK : j ⁻¹' (f ⁻¹' ((I ⊔ J).support : Set B)) =
      PrimeSpectrum.zeroLocus {RegularPairChart.coeff u v v} := by
    rw [Scheme.IdealSheafData.support_sup]
    change j ⁻¹' (f ⁻¹' ((I.support : Set B) ∩ (J.support : Set B))) = _
    rw [Set.preimage_inter, Set.preimage_inter, hpreI, hpreJ]
    apply Set.inter_eq_right.mpr
    rw [hrel, PrimeSpectrum.zeroLocus_singleton_mul]
    exact Set.subset_union_right
  constructor
  · change j ⁻¹' closure (f ⁻¹' ((I.support : Set B) \ ((I ⊔ J).support : Set B))) = _
    rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous,
      Set.preimage_sdiff, Set.preimage_sdiff, hpreI, hpreK, hrel]
    exact residual_regular_support _ _ (ratio_residual_denominator_regular u v hv)
  · change j ⁻¹' closure (f ⁻¹' ((J.support : Set B) \ ((I ⊔ J).support : Set B))) = _
    rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous,
      Set.preimage_sdiff, Set.preimage_sdiff, hpreJ, hpreK, Set.sdiff_self, closure_empty]

end AlgebraicGeometry.RamifiedNormalization.StageFour
