import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.Basic

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

theorem exists_holomorphic_curve_tangent {E C : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace C] [ChartedSpace E C]
    [IsManifold 𝓘(ℂ, E) ω C] (q : C) (v : E) :
    ∃ r : ℂ → C, r 0 = q ∧ ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω r 0 ∧
      HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) r 0
        ((ContinuousLinearMap.id ℂ ℂ).smulRight v) := by
  let φ := extChartAt 𝓘(ℂ, E) q
  let d := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  let l : ℂ → E := fun z ↦ φ q + d z
  let r : ℂ → C := fun z ↦ φ.symm (l z)
  have hl0 : l 0 = φ q := by simp only [l, map_zero, add_zero]
  have hchart : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω φ.symm (φ q) := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℂ, E)) (n := ω) q)
  have hdeq : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) φ.symm (φ q) = ContinuousLinearMap.id ℂ E := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] using!
      (mfderivWithin_range_extChartAt_symm (I := 𝓘(ℂ, E)) (x := q))
  have hchartder := (hchart.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv hdeq
  have hlhol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω l :=
    (contDiff_const.add d.contDiff).contMDiff
  have hld : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) l 0 d :=
    (d.hasFDerivAt.const_add (φ q)).hasMFDerivAt
  have hchart_l : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω φ.symm (l 0) := by
    simpa only [hl0] using hchart
  have hd_l : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) φ.symm (l 0)
      (ContinuousLinearMap.id ℂ E) := by
    rw [hl0]
    exact hchartder
  refine ⟨r, ?_, hchart_l.comp 0 (hlhol 0), ?_⟩
  · change φ.symm (l 0) = q
    rw [hl0]
    exact φ.left_inv (mem_extChartAt_source q)
  · exact (hd_l.comp 0 hld).congr_mfderiv (ContinuousLinearMap.id_comp d)

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
