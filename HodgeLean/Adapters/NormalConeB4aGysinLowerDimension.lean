import HodgeLean.Adapters.NormalConeB4aGysinRegularParameters
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
namespace HodgeLean.Adapters
open scoped NNReal ENNReal

/-- A differentiable image from a smaller real dimension has zero volume. -/
theorem a3b4a_gysin_lower_dimensional_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasureTheory.MeasureSpace F] [BorelSpace F]
    [MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure F)]
    (U : Set E) (f : E → F) (hf : DifferentiableOn ℝ f U)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F) :
    MeasureTheory.volume (f '' U) = 0 := by
  have habs : MeasureTheory.Measure.AbsolutelyContinuous (MeasureTheory.volume : MeasureTheory.Measure F)
      (MeasureTheory.Measure.hausdorffMeasure (Module.finrank ℝ F : ℝ)) :=
    MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply measure_zero_of_dimH_lt
    (d := (Module.finrank ℝ F : ℝ≥0))
    (by simpa only [NNReal.coe_natCast] using habs)
  calc
    dimH (f '' U) ≤ dimH U := hf.dimH_image_le
    _ ≤ dimH (Set.univ : Set E) := dimH_mono (Set.subset_univ U)
    _ = (Module.finrank ℝ E : ℝ≥0∞) := Real.dimH_univ_eq_finrank E
    _ < (Module.finrank ℝ F : ℝ≥0) := by exact_mod_cast hdim

end HodgeLean.Adapters
