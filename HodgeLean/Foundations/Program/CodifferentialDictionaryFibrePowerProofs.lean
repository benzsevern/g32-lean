import HodgeLean.Foundations.Program.CodifferentialDictionaryStandardSplittingsProofs

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

theorem b66d_projection_marked_chart {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a : b66f_Index D) (j : Fin 13)
    (heq : D.atlas.f a.2 = b6_branch c j) (p : b65z_fibre c D.C t)
    (hp : p.val ∈ (D.atlas.A a).source) :
    b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t p =
      b6a_value t.val j ((D.atlas.A a p.val).2 ^ D.atlas.n a.2) := by
  have h := (D.atlas.hmark a j heq).2 p.val hp
  simpa only [b63d_projection, p.property] using h

end HodgeLean.Foundations.Program
