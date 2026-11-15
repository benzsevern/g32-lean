import HodgeLean.Adapters.NormalConeB4aClassNormalCharts

/-! # Analytic inverse regularity of the chosen holomorphic flattening chart

The inverse is the original ambient chart inverse composed with the
bi-analytic normal-coordinate change.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

theorem holomorphic_flattening_inverse_contMDiffAt
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    (y : ComplexPoint X)
    (hy : y ∈ (ComplexPoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    ContMDiffAt 𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ)) 𝓘(ℂ, Fin d → ℂ) ω
      (ComplexPoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).symm
      (ComplexPoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y) := by
  let C := ComplexPoint.localChart X d (Point.map i z)
  let K := ComplexPoint.closedImmersionNormalCoordinateChange X Y i m d z
  let a := ComplexPoint.closedImmersionHolomorphicFlatteningChart X Y i m d z
  have hCy : y ∈ C.source := hy.1.1
  have hK := ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff K (C y)).mp hy.1.2).2.2
  have hKC : K.symm (a y) = C y := K.left_inv hy.1.2.1
  have hC : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω C.symm (C y) := by
    exact (contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin d → ℂ))
      (n := ω) (x := Point.map i z) (C y) (C.map_source hCy)).contMDiffAt
        (C.open_target.mem_nhds (C.map_source hCy))
  have hC' : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      C.symm (K.symm (a y)) := hKC.symm ▸ hC
  exact hC'.comp (a y) hK.contDiffAt.contMDiffAt

#print axioms holomorphic_flattening_inverse_contMDiffAt
end HodgeLean.Foundations.TubularEuler
