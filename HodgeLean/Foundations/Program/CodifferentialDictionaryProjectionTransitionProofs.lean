import HodgeLean.Foundations.Program.CodifferentialDictionaryProjectionProofs

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

theorem b66d_projectionCoeff_transition_eventually
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (a b : b66f_Index D)
    (u : (Fin 10 → ℂ) × ℂ) (hua : u ∈ (D.atlas.A a).target)
    (hub : (D.atlas.A a).symm u ∈ (D.atlas.A b).source) :
    b66d_projectionCoeff D a =ᶠ[𝓝 u]
      (fun v => b66d_projectionCoeff D b (v.1, b66f_transition D a b v)) := by
  have hB : ∀ᶠ v in 𝓝 u, (D.atlas.A a).symm v ∈ (D.atlas.A b).source :=
    ((D.atlas.A a).continuousAt_symm hua).tendsto.eventually
      ((D.atlas.A b).open_source.mem_nhds hub)
  filter_upwards [(D.atlas.A a).open_target.mem_nhds hua, hB] with v hva hvb
  have hp : (D.atlas.A b ((D.atlas.A a).symm v)).1 = v.1 :=
    (D.atlas.hparam b _ hvb).trans (b66f_gen_b66k_inverse_parameter D a v hva)
  have he : (v.1, b66f_transition D a b v) = D.atlas.A b ((D.atlas.A a).symm v) :=
    Prod.ext hp.symm rfl
  unfold b66d_projectionCoeff
  rw [he, (D.atlas.A b).left_inv hvb]

end HodgeLean.Foundations.Program
