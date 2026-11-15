import HodgeLean.Foundations.Program.CoverDictionaryReconstruct

/-! Linear assembly of holomorphic extensions. -/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- Coordinatewise extensions assemble into a linear family with values in a submodule. -/
theorem caf_linear_family_extend {U : Type*} (W : Submodule ℂ (U → ℂ)) (s : Set U)
    (F : (Fin 4 → ℂ) →ₗ[ℂ] (U → ℂ))
    (hF : ∀ v, ∃ ω' ∈ W, ∀ u ∈ s, ω' u = F v u) :
    ∃ φ : (Fin 4 → ℂ) →ₗ[ℂ] (U → ℂ),
      (∀ v, φ v ∈ W) ∧ ∀ v u, u ∈ s → φ v u = F v u := by
  classical
  choose ω' hω' he using fun i : Fin 4 ↦ hF (Pi.single i 1)
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (U → ℂ) :=
    { toFun := fun v ↦ ∑ i, v i • ω' i
      map_add' := fun v w ↦ by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  refine ⟨φ, ?_, ?_⟩
  · intro v
    change (∑ i, v i • ω' i) ∈ W
    exact W.sum_mem fun i _ ↦ W.smul_mem (v i) (hω' i)
  intro v u hu
  change (∑ i, v i • ω' i) u = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [he _ u hu]
  exact (caf_linearMap_coordinates F v u).symm

/-- Holomorphic extensions of a matrix formula assemble linearly in the input vector. -/
theorem caf_extend_matrix_form_family {U : Type*} (W : Submodule ℂ (U → ℂ)) (s : Set U)
    (M : U → Matrix (Fin 4) (Fin 4) ℂ) (R : U → Fin 4 → ℂ) (ds : U → ℂ)
    (hF : ∀ v : Fin 4 → ℂ, ∃ ω' ∈ W, ∀ u ∈ s,
      ω' u = (v ⬝ᵥ (M u *ᵥ R u)) * ds u) :
    ∃ φ : (Fin 4 → ℂ) →ₗ[ℂ] (U → ℂ), (∀ v, φ v ∈ W) ∧
      ∀ v u, u ∈ s → φ v u = (v ⬝ᵥ (M u *ᵥ R u)) * ds u := by
  let F : (Fin 4 → ℂ) →ₗ[ℂ] (U → ℂ) :=
    { toFun := fun v u ↦ (v ⬝ᵥ (M u *ᵥ R u)) * ds u
      map_add' := fun v w ↦ by
        funext u
        simp only [add_dotProduct, add_mul, Pi.add_apply]
      map_smul' := fun c v ↦ by
        funext u
        simp only [smul_dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc] }
  exact caf_linear_family_extend W s F hF

end HodgeLean.Foundations.Program
