import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticDefs
import Mathlib.Geometry.Manifold.Submersion

noncomputable section

open scoped Manifold ContDiff
open Manifold

namespace HodgeLean.Foundations.Program

theorem b6a_submersion_of_parameter_charts (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val) :
    IsSubmersion 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, Fin 10 → ℂ) ω
      (fun q : b6t_polydisc b × C ↦ q.1.val) := by
  apply IsSubmersionOfComplement.isSubmersion (F := ℂ)
  intro q
  apply IsSubmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.refl ℂ ((Fin 10 → ℂ) × ℂ))
    (A q) (OpenPartialHomeomorph.refl (Fin 10 → ℂ)) (hA q).1 (Set.mem_univ _)
    (IsManifold.subset_maximalAtlas (hA q).2)
    (IsManifold.subset_maximalAtlas (chartedSpaceSelf_atlas.mpr rfl))
    (by intro y hy; exact Set.mem_univ _)
  intro z hz
  simp only [OpenPartialHomeomorph.extend, mfld_simps] at hz ⊢
  have h := hparam q ((A q).symm z) ((A q).map_target hz)
  rw [(A q).right_inv hz] at h
  exact h.symm

end HodgeLean.Foundations.Program
