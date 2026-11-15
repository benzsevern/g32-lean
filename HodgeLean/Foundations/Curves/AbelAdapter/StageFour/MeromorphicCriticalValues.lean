import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.RamifiedFibers

noncomputable section
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Source: Forster, Lectures on Riemann Surfaces, §17, branch values of a proper holomorphic map. -/
def meromorphicCriticalValues (f : C → OnePoint ℂ) : Set (OnePoint ℂ) :=
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  f '' {x | mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f x = 0}

/-- Source: Forster, Lectures on Riemann Surfaces, §17, finiteness of branch values. -/
theorem meromorphicCriticalValues_finite [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hnc : ∃ x y, f x ≠ f y) : (meromorphicCriticalValues (E := E) f).Finite := by
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  exact (b4cov_critical_finite h f f.property.1 hnc).image f


/-- Source: Forster, Lectures on Riemann Surfaces, §17, multiplicities away from branch values. -/
theorem meromorphicMultiplicity_eq_one_of_not_criticalValue
    (f : b4c_MeroFun E C) (y : OnePoint ℂ)
    (hy : y ∉ meromorphicCriticalValues (E := E) f) (x : C) (hxy : f x = y) :
    meromorphicMultiplicity (E := E) f x = 1 := by
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  have hd : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f x ≠ 0 := fun hx ↦ hy ⟨x, hx, hxy⟩
  have he := (b4cov_ramIndex_eq_one_iff f f.property.1 x).mpr hd
  change (b4_ramIndex E ℂ f x : ℤ) = 1
  exact_mod_cast he

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
