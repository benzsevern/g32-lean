import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! # Derivatives in the original charts for self models

The model tangent identifications are identities, while the original chart
functions and their base points remain explicit.
-/

open scoped Manifold
namespace HodgeLean.Foundations.TubularEuler

theorem hasMFDerivAt_self_iff_original_charts
    {K E F M N : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
    {f : M → N} {x : M} {A : E →L[K] F} :
    HasMFDerivAt 𝓘(K, E) 𝓘(K, F) f x A ↔
      ContinuousAt f x ∧ HasFDerivAt
        (fun c => (chartAt F (f x)) (f ((chartAt E x).symm c))) A ((chartAt E x) x) := by
  simp only [HasMFDerivAt, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, hasFDerivWithinAt_univ]
  rfl

#print axioms hasMFDerivAt_self_iff_original_charts

theorem mfderiv_self_eq_original_chart_derivative
    {K E F M N : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
    {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(K, E) 𝓘(K, F) f x) :
    mfderiv 𝓘(K, E) 𝓘(K, F) f x = fderiv K
      (fun c => (chartAt F (f x)) (f ((chartAt E x).symm c))) ((chartAt E x) x) := by
  exact ((hasMFDerivAt_self_iff_original_charts.mp hf.hasMFDerivAt).2.fderiv).symm

#print axioms mfderiv_self_eq_original_chart_derivative
end HodgeLean.Foundations.TubularEuler
