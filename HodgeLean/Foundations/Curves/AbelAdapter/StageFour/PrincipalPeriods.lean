import HodgeLean.Foundations.Curves.AbelTheorem.Basic
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.MeromorphicTrace
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.FiberPeriodReduction
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.AbelGeneration
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.DegreeZeroAdjustment
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.Defs
import HodgeLean.Foundations.Program.RiemannRoch

noncomputable section
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Source: Forster, Lectures on Riemann Surfaces, GTM 81, §21, Abel theorem. -/
theorem analyticPrincipalPeriods (h : Module.finrank ℂ E = 1) (p : C)
    (f : b4c_MeroFun E C) (hf : ∃ x, f x ≠ (0 : ℂ)) :
    weightedSum (analyticAbel h p) (b4c_div E f) = 0 := by
  classical
  by_cases hnc : ∃ x y, f x ≠ f y
  · letI := b3_periodLattice_finite (E := E) (C := C) h
    letI := b3_periodLattice_free (E := E) (C := C)
    letI := b2_latticeMap_discrete (Λ := b3_periodLattice E C) (b3_periodF E C)
      (b3_isWeightOne (E := E) (C := C) h)
    have ha := b3_abelJacobi_holomorphic (E := E) (C := C) h p
      (analyticAbel (E := E) (C := C) h p)
      (b3_exists_abelJacobi (E := E) (C := C) h p).choose_spec
    exact meromorphic_divisor_sum_zero_of_fiber_holomorphic h f hnc
      (b3_periodLattice E C) (b3_periodF E C) (b3_isWeightOne (E := E) (C := C) h)
      (analyticAbel (E := E) (C := C) h p)
      (meromorphicFiberSum_contMDiff h f hnc (b3_periodF E C)
        (analyticAbel (E := E) (C := C) h p) ha)
  · have hc : ∀ x y, f x = f y := by
      push_neg at hnc
      exact hnc
    rw [meromorphic_divisor_eq_zero_of_constant f hf hc, map_zero]

/-- Source: Forster, Lectures on Riemann Surfaces, GTM 81, §21, Abel theorem. -/
theorem meromorphicFunction_of_abelSum_zero (h : Module.finrank ℂ E = 1) (p : C)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0)
    (hperiod : weightedSum (analyticAbel h p) D = 0) :
    ∃ f : b4c_MeroFun E C, (∃ x, f x ≠ (0 : ℂ)) ∧ b4c_div E f = D := by
  exact HodgeLean.Foundations.Curves.AbelTheorem.abelConverse h p D hdeg hperiod

/-- Source: Forster, Lectures on Riemann Surfaces, GTM 81, §20, Jacobi inversion. -/
theorem degreeZero_abelSum_surjective (h : Module.finrank ℂ E = 1) (p : C)
    (t : b3_Jacobian E C) :
    ∃ D : C →₀ ℤ, b4c_deg D = 0 ∧ weightedSum (analyticAbel h p) D = t := by
  letI := b3_periodLattice_finite (E := E) (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete (Λ := b3_periodLattice E C) (b3_periodF E C)
    (b3_isWeightOne (E := E) (C := C) h)
  exact degreeZero_sum_of_surjective (analyticAbel (E := E) (C := C) h p) p
    (b3_exists_abelJacobi (E := E) (C := C) h p).choose_spec.1
    (abelSum_surjective (E := E) (C := C) h p) t

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
