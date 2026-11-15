import HodgeLean.Foundations.Program.CodifferentialDictionaryAtlasPowerProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryNormalizationProofs

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
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b66d_sFun_marked_chart {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a b : ℂ)
    (A : b66f_Index D) (k : Fin 10)
    (hk : D.atlas.f A.2 = b6_branch c (Fin.castLE (by norm_num) k))
    (y : b65z_fibre c D.C t) (hy : y.val ∈ (D.atlas.A A).source) :
    b65g_sFun D t a b y = b66d_inverseNormalize a b
      (t.val k + (b66f_gen_b66g_slice D t A y) ^ D.atlas.n A.2) := by
  have h := b66d_projection_marked_chart D t A (Fin.castLE (by norm_num) k) hk y hy
  unfold b65g_sFun
  rw [h, b6a_value_finite _ _ (by change k.val ≠ 12; have := k.isLt; omega)]
  have hs : b6a_valueShift t.val (Fin.castLE (by norm_num) k) = t.val k := by
    simp [b6a_valueShift, k.isLt]
  rw [hs]
  rfl

end HodgeLean.Foundations.Program
