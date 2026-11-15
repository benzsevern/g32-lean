import HodgeLean.Foundations.Program.CodifferentialDictionaryAtlasPowerProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryRamificationIndexProofs

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

theorem b66d_atlas_ramIndex {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (p : b65z_fibre c D.C t) (j : Fin 13) (hj : D.atlas.f p.val.2 = b6_branch c j) :
    b4_ramIndex ℂ ℂ (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t) p =
      D.atlas.n p.val.2 := by
  let π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  have ha : p.val ∈ (D.atlas.A p.val).source := (D.atlas.hA p.val).1
  obtain ⟨hF, hFd, -⟩ := b66f_gen_b66g_slice_chart D t p.val p p
    (mem_extChartAt_source p) ha
  have hF0 : (b66f_gen_b66g_slice D t p.val ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
      (extChartAt 𝓘(ℂ, ℂ) p p) = 0 := by
    change (D.atlas.A p.val ((extChartAt 𝓘(ℂ, ℂ) p).symm
      (extChartAt 𝓘(ℂ, ℂ) p p)).val).2 = 0
    rw [extChartAt_to_inv]
    exact (D.atlas.hmark p.val j hj).1
  have hnc : ∃ x y : b65z_fibre c D.C t, π x ≠ π y := by
    obtain ⟨x, hx⟩ := D.hsurj t ((0 : ℂ) : OnePoint ℂ)
    obtain ⟨y, hy⟩ := D.hsurj t ((1 : ℂ) : OnePoint ℂ)
    refine ⟨x, y, ?_⟩
    dsimp only [π]
    rw [hx, hy]
    exact OnePoint.coe_injective.ne (by norm_num)
  exact b66d_ramIndex_of_chart_power π (D.hk t) hnc p _ _ hF hF0 hFd
    (b66d_written_projection_power D t p j hj)

end HodgeLean.Foundations.Program
