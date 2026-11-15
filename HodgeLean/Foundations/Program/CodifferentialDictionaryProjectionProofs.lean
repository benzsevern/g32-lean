import HodgeLean.Foundations.Program.CodifferentialDictionarySplittingProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryOverlapProofs

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

def b66d_projectionCoeff {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (a : b66f_Index D) (u : (Fin 10 → ℂ) × ℂ) : ℂ :=
  b4cov_chart0 (b6a_map c D.atlas.f ((D.atlas.A a).symm u))

theorem b66d_projectionCoeff_free {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (a : b66f_Index D)
    (hfree : D.atlas.f a.2 ∉ Set.range (b6_branch c))
    (u : (Fin 10 → ℂ) × ℂ) (hu : u ∈ (D.atlas.A a).target) :
    b66d_projectionCoeff D a u = u.2 := by
  unfold b66d_projectionCoeff
  rw [(D.atlas.hfree a hfree).2 _ ((D.atlas.A a).map_target hu),
    (D.atlas.A a).right_inv hu, b4cov_chart0_coe]

theorem b66d_projectionCoeff_finite {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (a : b66f_Index D) (j : Fin 13)
    (heq : D.atlas.f a.2 = b6_branch c j) (hj : j.val ≠ 12)
    (u : (Fin 10 → ℂ) × ℂ) (hu : u ∈ (D.atlas.A a).target) :
    b66d_projectionCoeff D a u = b6a_valueShift u.1 j + u.2 ^ D.atlas.n a.2 := by
  unfold b66d_projectionCoeff
  rw [(D.atlas.hmark a j heq).2 _ ((D.atlas.A a).map_target hu)]
  rw [b66f_gen_b66k_inverse_parameter D a _ hu, (D.atlas.A a).right_inv hu,
    b6a_value_finite _ _ hj, b4cov_chart0_coe]

theorem b66d_projectionCoeff_infinite {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (a : b66f_Index D) (j : Fin 13)
    (heq : D.atlas.f a.2 = b6_branch c j) (hj : j.val = 12)
    (u : (Fin 10 → ℂ) × ℂ) (hu : u ∈ (D.atlas.A a).target) (hz : u.2 ≠ 0) :
    b66d_projectionCoeff D a u = (u.2 ^ D.atlas.n a.2)⁻¹ := by
  unfold b66d_projectionCoeff
  rw [(D.atlas.hmark a j heq).2 _ ((D.atlas.A a).map_target hu)]
  rw [b66f_gen_b66k_inverse_parameter D a _ hu, (D.atlas.A a).right_inv hu,
    b6a_value_infinite _ _ hj, b4cov_chart0_sphInv (pow_ne_zero _ hz)]

end HodgeLean.Foundations.Program
