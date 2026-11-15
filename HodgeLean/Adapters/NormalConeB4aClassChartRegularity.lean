import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCharts

/-! # Analytic regularity of the frozen holomorphic-chart predicate

Route: F4 identifies each holomorphic coordinate with a complex smooth
function of order infinity. Finite products combine these coordinates into
the chart map on the smooth complex-point manifold.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff

/-- The frozen coordinate predicate makes the whole chart analytic on its
source in the complex-point manifold. -/
theorem a3b4a_classHolomorphicChart_contMDiffOn
    (X : Over (Spec (CommRingCat.of ℂ))) (d r c : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, (Fin r → ℂ) × (Fin c → ℂ)) ω e e.source := by
  apply (contMDiffOn_prod_module_iff _).mpr
  constructor
  · apply contMDiffOn_pi_space.mpr
    intro j
    exact (f4_isHolFun_iff_contMDiffOn X d (fun y => (e y).1 j)
      e.open_source).mp (he.1 j)
  · apply contMDiffOn_pi_space.mpr
    intro j
    exact (f4_isHolFun_iff_contMDiffOn X d (fun y => (e y).2 j)
      e.open_source).mp (he.2 j)

end HodgeLean.Adapters
