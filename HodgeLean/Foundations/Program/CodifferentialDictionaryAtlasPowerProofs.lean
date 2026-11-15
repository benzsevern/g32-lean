import HodgeLean.Foundations.Program.CodifferentialDictionaryFibrePowerProofs

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

theorem b66d_written_projection_power {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (p : b65z_fibre c D.C t) (j : Fin 13) (hj : D.atlas.f p.val.2 = b6_branch c j) :
    let π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
    let e := extChartAt 𝓘(ℂ, ℂ) p
    let F := b66f_gen_b66g_slice D t p.val ∘ e.symm
    writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) p π =ᶠ[𝓝 (e p)]
      (fun z => writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) p π (e p) + F z ^ D.atlas.n p.val.2) := by
  let π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  let e := extChartAt 𝓘(ℂ, ℂ) p
  let F := b66f_gen_b66g_slice D t p.val ∘ e.symm
  have ha : p.val ∈ (D.atlas.A p.val).source := (D.atlas.hA p.val).1
  have hzero : (D.atlas.A p.val p.val).2 = 0 := (D.atlas.hmark p.val j hj).1
  have hπp : π p = b6_branch t.val j := by
    have h := b66d_projection_marked_chart D t p.val j hj p ha
    rw [hzero, zero_pow (Nat.ne_of_gt (D.atlas.hn p.val.2)), b6a_value_zero] at h
    exact h
  have hopen : IsOpen {q : b65z_fibre c D.C t | q.val ∈ (D.atlas.A p.val).source} :=
    (D.atlas.A p.val).open_source.preimage continuous_subtype_val
  have hnear : ∀ᶠ z in 𝓝 (e p), (e.symm z).val ∈ (D.atlas.A p.val).source := by
    change (extChartAt 𝓘(ℂ, ℂ) p).symm ⁻¹'
      {q : b65z_fibre c D.C t | q.val ∈ (D.atlas.A p.val).source} ∈
        𝓝 (extChartAt 𝓘(ℂ, ℂ) p p)
    apply (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) p).preimage_mem_nhds
    rw [extChartAt_to_inv]
    exact hopen.mem_nhds ha
  filter_upwards [hnear] with z hz
  have hπz : π (e.symm z) = b6a_value t.val j (F z ^ D.atlas.n p.val.2) :=
    b66d_projection_marked_chart D t p.val j hj (e.symm z) hz
  by_cases hinf : j.val = 12
  · have hb : b6_branch t.val j = OnePoint.infty := by
      rw [← b6a_value_zero, b6a_value_infinite _ _ hinf, b4cov_sphInv_zero]
    have hc : writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) p π (e p) = 0 := by
      change (extChartAt 𝓘(ℂ, ℂ) (π p)) (π (e.symm (e p))) = 0
      rw [show e.symm (e p) = p from extChartAt_to_inv p, hπp, hb]
      simp [extChartAt_coe, b4cov_chartAt_infty, b4cov_chartInf_apply, b4cov_sphInv_infty, b4cov_chart0_coe, id_eq]
    change (extChartAt 𝓘(ℂ, ℂ) (π p)) (π (e.symm z)) = _
    rw [hc, hπp, hb, hπz, b6a_value_infinite _ _ hinf]
    simp only [extChartAt_coe, b4cov_chartAt_infty, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq, b4cov_chartInf_apply,
      b4cov_sphInv_involutive (↑(F z ^ D.atlas.n p.val.2)),
      b4cov_chart0_coe, zero_add, F, Function.comp_apply]
    change b4cov_chart0 (b4cov_sphInv (b4cov_sphInv
      (↑(F z ^ D.atlas.n p.val.2)))) = F z ^ D.atlas.n p.val.2
    rw [b4cov_sphInv_involutive _, b4cov_chart0_coe]
  · have hb : b6_branch t.val j = ((b6a_valueShift t.val j : ℂ) : OnePoint ℂ) := by
      rw [← b6a_value_zero, b6a_value_finite _ _ hinf, add_zero]
    have hc : writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) p π (e p) = b6a_valueShift t.val j := by
      change (extChartAt 𝓘(ℂ, ℂ) (π p)) (π (e.symm (e p))) = _
      rw [show e.symm (e p) = p from extChartAt_to_inv p, hπp, hb]
      simp only [extChartAt_coe, b4cov_chartAt_coe, modelWithCornersSelf_coe,
        Function.comp_apply, id_eq, b4cov_chart0_coe, F, Function.comp_apply]
    change (extChartAt 𝓘(ℂ, ℂ) (π p)) (π (e.symm z)) = _
    rw [hc, hπp, hb, hπz, b6a_value_finite _ _ hinf]
    simp only [extChartAt_coe, b4cov_chartAt_coe, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq, b4cov_chart0_coe, F, Function.comp_apply]
    rfl

end HodgeLean.Foundations.Program
