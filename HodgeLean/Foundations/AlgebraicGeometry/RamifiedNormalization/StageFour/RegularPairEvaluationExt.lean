import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartTensor
import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original coefficients and literal ratio determine an evaluation of the actual regular-pair chart. -/
theorem regular_pair_evaluation_ext
    {R A : Type*} [CommRing R] [CommRing A] (u v : R)
    (f g : RegularPairChart.ring u v →+* A)
    (hcoeff : f.comp (RegularPairChart.coeff u v) = g.comp (RegularPairChart.coeff u v))
    (hratio : f (RegularPairChart.ratio u v) = g (RegularPairChart.ratio u v)) : f = g := by
  have hrel : (f.comp (RegularPairChart.coeff u v)) u =
      f (RegularPairChart.ratio u v) * (f.comp (RegularPairChart.coeff u v)) v := by
    change f (RegularPairChart.coeff u v u) = _
    have hchart : RegularPairChart.coeff u v u =
        RegularPairChart.ratio u v * RegularPairChart.coeff u v v :=
      RegularPairChart.chart_relation u v
    rw [hchart, map_mul] <;> rfl
  obtain ⟨h, hh, huniq⟩ := RegularPairChart.universal u v
    (f.comp (RegularPairChart.coeff u v)) (f (RegularPairChart.ratio u v)) hrel
  exact (huniq f ⟨rfl, rfl⟩).trans (huniq g ⟨hcoeff.symm, hratio.symm⟩).symm

end AlgebraicGeometry.RamifiedNormalization.StageFour
