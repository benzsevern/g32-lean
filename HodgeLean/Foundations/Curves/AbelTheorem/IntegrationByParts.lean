import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem integral_d_wedge_eq_neg_smul_d (h : Module.finrank ℂ E = 1)
    (g : C → ℝ) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α) :
    b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g)) α) =
      -b3Forms_integral (b4c_residue_basis h) (b3Forms_smulFun g (b3Forms_d α)) := by
  have hgs := b3Forms_isSmooth_fun hg
  have he := b3Forms_integral_d_eq_zero b3Forms_oriented_complex
    (b4c_residue_basis h) (hα.smulFun hg)
  rw [b3Forms_d_smulFun hgs hα,
    b3Forms_integral_add _ (hgs.d.wedgeForm hα) (hα.d.smulFun hg)] at he
  linarith

end HodgeLean.Foundations.Curves.AbelTheorem
