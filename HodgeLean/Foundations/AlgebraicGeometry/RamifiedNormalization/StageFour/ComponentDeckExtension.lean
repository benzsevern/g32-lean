import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentTopology
import Mathlib.Topology.DenseEmbedding

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A retained component deck equation on its affine parameter extends to its actual point at infinity. -/
theorem component_deck_extension
    (F : Over (Spec ↧ℂ)) [T2Space (ComplexPoint F)]
    (D : F ⟶ F) (j k : projectiveLine ⟶ F)
    (c : ℂ) (hc : c ≠ 0)
    (hfinite : ∀ z : ℂ,
      Point.map D (Point.map j (lineCoordinate.symm (z : OnePoint ℂ))) =
        Point.map k (lineCoordinate.symm ((c * z : ℂ) : OnePoint ℂ))) :
    ∀ z : OnePoint ℂ,
      Point.map D (Point.map j (lineCoordinate.symm z)) =
        Point.map k (lineCoordinate.symm
          ((Homeomorph.onePointCongr (Homeomorph.mulLeft₀ c hc)) z)) := by
  have hh := OnePoint.denseRange_coe.equalizer
    ((Point.continuous_map D).comp ((Point.continuous_map j).comp lineCoordinate.symm.continuous))
    ((Point.continuous_map k).comp (lineCoordinate.symm.continuous.comp
      (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ c hc)).continuous))
    (show (fun z : OnePoint ℂ => Point.map D (Point.map j (lineCoordinate.symm z))) ∘
        ((↑) : ℂ → OnePoint ℂ) =
      (fun z : OnePoint ℂ => Point.map k (lineCoordinate.symm
        ((Homeomorph.onePointCongr (Homeomorph.mulLeft₀ c hc)) z))) ∘
        ((↑) : ℂ → OnePoint ℂ) from by
      funext z
      simpa using hfinite z)
  exact congrFun hh

end AlgebraicGeometry.RamifiedNormalization.StageFour
