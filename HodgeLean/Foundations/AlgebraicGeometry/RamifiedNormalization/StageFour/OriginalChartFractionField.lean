import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartBaseFieldFactorization
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntermediateCoefficientFractionField

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The faithfully embedded original binomial chart uses the same base fraction field, with both scalar towers retained. -/
theorem original_chart_fraction_field
    {R K L : Type} [CommRing R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    (u v : R) (κ : K →+* L)
    (G : RegularPairChart.ring u v →+* L)
    (hc : G.comp (RegularPairChart.coeff u v) = κ.comp (algebraMap R K))
    (hi : Function.Injective G) (hv : algebraMap R K v ≠ 0) :
    ∃ H : RegularPairChart.ring u v →+* K,
      H.comp (RegularPairChart.coeff u v) = algebraMap R K ∧
      H (RegularPairChart.ratio u v) = algebraMap R K u / algebraMap R K v ∧
      κ.comp H = G ∧
      (letI := H.toAlgebra
       letI := G.toAlgebra
       letI := κ.toAlgebra
       IsFractionRing (RegularPairChart.ring u v) K ∧
       IsScalarTower R (RegularPairChart.ring u v) K ∧
       IsScalarTower (RegularPairChart.ring u v) K L) := by
  obtain ⟨H, hHc, hHr, hHG, hHi⟩ := regular_pair_chart_base_field_factorization u v
    (algebraMap R K) κ G hc hi hv
  refine ⟨H, hHc, hHr, hHG, ?_⟩
  letI := H.toAlgebra
  letI := G.toAlgebra
  letI := κ.toAlgebra
  letI : IsScalarTower R (RegularPairChart.ring u v) K :=
    IsScalarTower.of_algebraMap_eq' hHc.symm
  letI : IsScalarTower (RegularPairChart.ring u v) K L :=
    IsScalarTower.of_algebraMap_eq' hHG.symm
  letI : FaithfulSMul (RegularPairChart.ring u v) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hHi
  exact ⟨fraction_field_of_intermediate_coefficient_ring (R := R), inferInstance, inferInstance⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
