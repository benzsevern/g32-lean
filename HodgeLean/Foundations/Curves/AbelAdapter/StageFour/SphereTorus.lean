import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.GenusZero
import HodgeLean.Foundations.Program.HurwitzPrymCovSphere

noncomputable section
open HodgeLean.Foundations.Program
open scoped TensorProduct Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§13, 21; Liouville theorem. -/
theorem sphere_torusMap_constant
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]
    (G : Submodule ℂ (ℂ ⊗[ℤ] M)) (hG : b2_IsWeightOne M G)
    [DiscreteTopology (b2_latticeMap M G).range] :
    letI := b4cov_sphChartedSpace
    letI := b4cov_sph_isManifold
    ∀ (f : OnePoint ℂ → b2_torus M G),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V M G) ω f → ∀ x y, f x = f y := by
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  intro f hf x y
  letI : Subsingleton (b3_HolForm ℂ (OnePoint ℂ)) := ⟨fun u v ↦
    Subtype.ext ((b4cov_sphere_form_eq_zero u.val u.property).trans
      (b4cov_sphere_form_eq_zero v.val v.property).symm)⟩
  have h : Module.finrank ℂ ℂ = 1 := by simp
  letI := b3_periodLattice_finite (E := ℂ) (C := OnePoint ℂ) h
  letI := b3_periodLattice_free (E := ℂ) (C := OnePoint ℂ)
  letI := b2_latticeMap_discrete (Λ := b3_periodLattice ℂ (OnePoint ℂ))
    (b3_periodF ℂ (OnePoint ℂ)) (b3_isWeightOne (E := ℂ) (C := OnePoint ℂ) h)
  exact torusMap_constant_of_no_forms (E := ℂ) (C := OnePoint ℂ) h M G hG y f hf x

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
