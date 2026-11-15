import HodgeLean.Foundations.Program.CodifferentialDictionaryDirectionProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryLinearProofs

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

theorem b66d_frame_functionals_independent {L : Type*} [AddCommGroup L]
    (m : (ℚ ⊗[ℤ] L) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) (z : Fin 9 → ℂ) :
    LinearIndependent ℂ (fun ij : Fin 2 × Fin 3 => fun x : L =>
      b60_E.baseChange ℂ (b64b_complexMarking L m (1 ⊗ₜ[ℤ] x)) (b60_frame z ij)) := by
  let G : (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] (L → ℂ) :=
    { toFun := fun n x => b60_E.baseChange ℂ (b64b_complexMarking L m (1 ⊗ₜ[ℤ] x)) n
      map_add' := fun a b => funext (fun x => map_add _ a b)
      map_smul' := fun a b => funext (fun x => map_smul _ a b) }
  have hG : Function.Injective G := by
    intro a b h
    have hh : (((b60_E.baseChange ℂ).flip a).comp (b64b_complexMarking L m).toLinearMap) =
        (((b60_E.baseChange ℂ).flip b).comp (b64b_complexMarking L m).toLinearMap) :=
      b66d_dual_integral_ext _ _ (fun x => congrFun h x)
    apply b66m_polarization_right_injective
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := (b64b_complexMarking L m).surjective y
    exact congrArg (fun f => f x) hh
  exact (b60_frame_independent z).map' G (LinearMap.ker_eq_bot_of_injective hG)

theorem b66d_frame_period_eigen {L : Type*} [AddCommGroup L]
    (A : L →ₗ[ℤ] L) (m : (ℚ ⊗[ℤ] L) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (z : Fin 9 → ℂ) (ij : Fin 2 × Fin 3) (x : L) :
    b60_E.baseChange ℂ (b64b_complexMarking L m (1 ⊗ₜ[ℤ] A x)) (b60_frame z ij) =
      (if ij.1 = 0 then Complex.I * (Real.sqrt 3 : ℂ)
        else -Complex.I * (Real.sqrt 3 : ℂ)) *
      b60_E.baseChange ℂ (b64b_complexMarking L m (1 ⊗ₜ[ℤ] x)) (b60_frame z ij) := by
  rw [← LinearMap.baseChange_tmul, b64b_complex_intertwines L A m hJ,
    b66d_pairing_omega_skew, b60_omegaC_frame, map_smul]
  split_ifs <;> simp only [smul_eq_mul] <;> ring

end HodgeLean.Foundations.Program
