import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleDivisors
import HodgeLean.Foundations.Program.SchoenCycleCanonicalDivisors

/-! # Principal residue rank with retained divisor multiplicities -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Adapters
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Above the canonical degree, no nonzero holomorphic form annihilates all
principal residues, including the full jets at repeated support points.
Source: Forster, Lectures on Riemann Surfaces, §§18–19. -/
theorem residual_high_degree_residue_kernel
    (hE : Module.finrank ℂ E = 1) (D : C →₀ ℤ)
    (hD : ∀ x, 0 ≤ D x)
    (hd : 2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 < b4c_deg D) :
    LinearMap.ker (RiemannRochAna_holPrincipalResidueLinear hE D) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro θ hθ
  change θ = 0
  by_contra hn
  have hb := RiemannRochAna_holKernel_divisor_bound hE D hD θ hn hθ
  let w : b4c_MeroForm E C hE := ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  have he := RiemannRochAna_deg_nonneg
    (b4c_divForm (hE := hE) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) - D)
    (fun x => by
      rw [Finsupp.sub_apply, RiemannRochAna_divForm_apply_of_finite hE w
        (b4c_meroForm_orderSupport_finite_aux hE w) x]
      exact sub_nonneg.mpr (hb x))
  rw [RiemannRochAna_deg_sub, s2e_holomorphic_divisor_degree hE θ hn] at he
  omega

#print axioms residual_high_degree_residue_kernel

/-- Principal residues have the full genus rank above the canonical degree.
Source: Forster, Lectures on Riemann Surfaces, §§18–19. -/
theorem residual_high_degree_residue_rank
    (hE : Module.finrank ℂ E = 1) (D : C →₀ ℤ)
    (hD : ∀ x, 0 ≤ D x)
    (hd : 2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 < b4c_deg D) :
    Module.finrank ℂ (LinearMap.range (RiemannRochAna_principalResidueLinear hE D)) =
      Module.finrank ℂ (b3_HolForm E C) := by
  have hr := RiemannRochAna_principalResidue_rank_add_holKernel hE D
  rw [residual_high_degree_residue_kernel hE D hD hd, finrank_bot, add_zero] at hr
  exact hr

#print axioms residual_high_degree_residue_rank

/-- Every functional on holomorphic forms is an actual principal residue
functional when the effective divisor exceeds the canonical degree.
Source: Forster, Lectures on Riemann Surfaces, §§18–19. -/
theorem residual_high_degree_residue_surjective
    (hE : Module.finrank ℂ E = 1) (D : C →₀ ℤ)
    (hD : ∀ x, 0 ≤ D x)
    (hd : 2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 < b4c_deg D) :
    Function.Surjective (RiemannRochAna_principalResidueLinear hE D) := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  letI : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [Subspace.dual_finrank_eq]
  exact residual_high_degree_residue_rank hE D hD hd

#print axioms residual_high_degree_residue_surjective

/-- The principal-data kernel has the expected degree-minus-genus dimension.
Source: Forster, Lectures on Riemann Surfaces, §§18–19. -/
theorem residual_high_degree_principal_kernel_dimension
    (hE : Module.finrank ℂ E = 1) (D : C →₀ ℤ)
    (hD : ∀ x, 0 ≤ D x)
    (hd : 2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 < b4c_deg D) :
    (Module.finrank ℂ
        (LinearMap.ker (RiemannRochAna_principalResidueLinear hE D)) : ℤ) =
      b4c_deg D - Module.finrank ℂ (b3_HolForm E C) := by
  have hr := (RiemannRochAna_principalResidueLinear hE D).finrank_range_add_finrank_ker
  rw [residual_high_degree_residue_rank hE D hD hd] at hr
  have hz := congrArg (fun n : ℕ => (n : ℤ)) hr
  push_cast at hz
  rw [RiemannRochAna_principalData_finrank_effective D hD] at hz
  omega

#print axioms residual_high_degree_principal_kernel_dimension
end HodgeLean.Foundations.Program.G32Native
