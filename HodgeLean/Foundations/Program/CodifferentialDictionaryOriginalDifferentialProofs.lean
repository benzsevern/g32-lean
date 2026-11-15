import HodgeLean.Foundations.Program.CodifferentialDictionaryOriginalCoordinateProofs

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

set_option backward.isDefEq.respectTransparency false in
theorem b66d_ds_marked_chart {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a b : ℂ)
    (A : b66f_Index D) (k : Fin 10)
    (hk : D.atlas.f A.2 = b6_branch c (Fin.castLE (by norm_num) k))
    (y : b65z_fibre c D.C t) (hy : y.val ∈ (D.atlas.A A).source)
    (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (hw : b - (t.val k + (b66f_gen_b66g_slice D t A y) ^ D.atlas.n A.2) * (b - a) ≠ 0)
    (v : ℂ) :
    b65g_ds D t a b ⟨y, v⟩ =
      ((b65g_sFun D t a b y) ^ 2 / (a * b / (b - a)) *
        ((D.atlas.n A.2 : ℂ) * (b66f_gen_b66g_slice D t A y) ^ (D.atlas.n A.2 - 1))) *
        b66f_gen_b66g_sliceD D t A y v := by
  let z := b66f_gen_b66g_slice D t A y
  let L : ℂ → ℂ := fun z => b66d_inverseNormalize a b (t.val k + z ^ D.atlas.n A.2)
  have hL : HasDerivAt L
      ((b66d_inverseNormalize a b (t.val k + z ^ D.atlas.n A.2)) ^ 2 /
        (a * b / (b - a)) * ((D.atlas.n A.2 : ℂ) * z ^ (D.atlas.n A.2 - 1))) z := by
    simpa only [zero_add, mul_one, L, z, Function.comp_def, Pi.add_apply, Pi.pow_apply, id_eq] using
      (b66d_inverseNormalize_derivative_scaled hab hba hw).comp z
        ((hasDerivAt_const z (t.val k)).add ((hasDerivAt_id z).pow (D.atlas.n A.2)))
  have hsl := (b66f_gen_b66g_slice_contMDiffAt D t A y hy).mdifferentiableAt (by simp)
  have heq : b65g_sFun D t a b =ᶠ[𝓝 y] L ∘ b66f_gen_b66g_slice D t A := by
    have hopen : IsOpen {w : b65z_fibre c D.C t | w.val ∈ (D.atlas.A A).source} :=
      (D.atlas.A A).open_source.preimage continuous_subtype_val
    filter_upwards [hopen.mem_nhds hy] with w hw
    exact b66d_sFun_marked_chart D t a b A k hk w hw
  have hd := (HasMFDerivAt.comp (g := L) (f := b66f_gen_b66g_slice D t A) y
    hL.hasFDerivAt.hasMFDerivAt hsl.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b65g_ds b66f_gen_b66g_sliceD
  rw [hd.mfderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  rw [b66d_sFun_marked_chart D t a b A k hk y hy]
  exact mul_comm _ _

end HodgeLean.Foundations.Program
