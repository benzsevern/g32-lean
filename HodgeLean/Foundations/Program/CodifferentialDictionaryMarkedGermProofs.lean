import HodgeLean.Foundations.Program.CodifferentialDictionaryMarkedCoefficientProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryCoordinateGermProofs

import HodgeLean.Foundations.Program.CoverDictionaryCharts

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
set_option maxHeartbeats 400000 in
theorem b66d_multiply_marked_germ {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a b s₀ : ℂ)
    (p : b65z_fibre c D.C t) (k : Fin 10)
    (hk : D.atlas.f p.val.2 = b6_branch c (Fin.castLE (by norm_num) k))
    (hab : a * b ≠ 0) (hba : b - a ≠ 0) (hs₀ : s₀ ≠ 0)
    (ht : t.val k = b65s_normalize a b s₀)
    (cj : Bool) (φ : b65g_homG D t cj) (ψ : b65g_homG D t (!cj))
    (q r : b66f_primitiveForms D t)
    (hq : b66f_chartForm D t q.val = φ.val (Pi.single 0 1))
    (hr : b66f_chartForm D t r.val = ψ.val (Pi.single 0 1))
    (poles : Fin 4 ⊕ Fin 12 → ℂ) (N : Fin 10 → ℂ)
    (h0 : (0 : ℂ) ∈ Set.range poles)
    (hnum : ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t),
      u.1 ∈ b65g_good D t a b poles →
      b65g_contract φ.val ψ.val u = b65g_quadratic D t a b poles N u) :
    (fun z => b66f_multiply D t q r p.val ((D.atlas.A p.val).symm (t.val, z)).2) =ᶠ[𝓝[≠] 0]
      (fun z => let s := b66d_inverseNormalize a b (t.val k + z ^ D.atlas.n p.val.2)
        (1 / 4 : ℂ) * (∑ j : Fin 10, N j * s ^ j.val) /
          (b65q_denominator poles).eval s *
          (s ^ 2 / (a * b / (b - a)) *
            ((D.atlas.n p.val.2 : ℂ) * z ^ (D.atlas.n p.val.2 - 1))) ^ 2) := by
  let e := extChartAt 𝓘(ℂ, ℂ) p
  let F := b66f_gen_b66g_slice D t p.val ∘ e.symm
  have hp : p.val ∈ (D.atlas.A p.val).source := (D.atlas.hA p.val).1
  obtain ⟨hF, hFd, -⟩ := b66f_gen_b66g_slice_chart D t p.val p p (mem_extChartAt_source p) hp
  have hF0 : F (e p) = 0 := by
    change (D.atlas.A p.val ((extChartAt 𝓘(ℂ, ℂ) p).symm
      (extChartAt 𝓘(ℂ, ℂ) p p)).val).2 = 0
    rw [extChartAt_to_inv]
    exact (D.atlas.hmark p.val (Fin.castLE (by norm_num) k) hk).1
  have hden : b - t.val k * (b - a) ≠ 0 := by
    rw [ht]
    intro hz
    have hh := b66d_inverseNormalize_center hab hba hs₀
    rw [b66d_inverseNormalize, hz, div_zero] at hh
    exact hs₀ hh.symm
  have hnear : ∀ᶠ z in 𝓝 (e p), (e.symm z).val ∈ (D.atlas.A p.val).source := by
    have hopen : IsOpen {y : b65z_fibre c D.C t | y.val ∈ (D.atlas.A p.val).source} :=
      (D.atlas.A p.val).open_source.preimage continuous_subtype_val
    change (extChartAt 𝓘(ℂ, ℂ) p).symm ⁻¹'
      {y : b65z_fibre c D.C t | y.val ∈ (D.atlas.A p.val).source} ∈
        𝓝 (extChartAt 𝓘(ℂ, ℂ) p p)
    apply (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) p).preimage_mem_nhds
    simpa only [extChartAt_to_inv] using hopen.mem_nhds hp
  have hdnear : ∀ᶠ z in 𝓝 (e p),
      b - (t.val k + F z ^ D.atlas.n p.val.2) * (b - a) ≠ 0 := by
    have hc : ContinuousAt (fun z => b - (t.val k + F z ^ D.atlas.n p.val.2) * (b - a)) (e p) := by
      fun_prop
    have hd : b - (t.val k + F (e p) ^ D.atlas.n p.val.2) * (b - a) ≠ 0 := by
      simpa only [hF0, zero_pow (Nat.ne_of_gt (D.atlas.hn p.val.2)), add_zero] using hden
    exact hc.tendsto.eventually (eventually_ne_nhds hd)
  apply b66d_eventuallyEq_of_coordinate_comp F _ _ (e p) hF hF0 hFd
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
    hdnear.filter_mono nhdsWithin_le_nhds, b65g_chart_punctured_good D t hab hba poles p] with z hz hdz hgood
  have hD := b66d_denominator_away_poles poles h0 _ (b65g_good_sFun hgood.2)
  have hcoef := b66d_multiply_marked_coefficient D t a b p.val k hk (e.symm z) hz
    hab hba hdz cj φ ψ q r hq hr poles N hD (hnum ⟨e.symm z, (1 : ℂ)⟩ hgood.2)
  have hinv : (D.atlas.A p.val).symm (t.val, F z) = (e.symm z).val := by
    have hv : D.atlas.A p.val (e.symm z).val = (t.val, F z) :=
      b66f_gen_b66g_slice_value D t p.val (e.symm z) hz
    rw [← hv]
    exact (D.atlas.A p.val).left_inv hz
  change b66f_multiply D t q r p.val ((D.atlas.A p.val).symm (t.val, F z)).2 = _
  rw [hinv, hcoef, b66d_sFun_marked_chart D t a b p.val k hk (e.symm z) hz]
  rfl

end HodgeLean.Foundations.Program
