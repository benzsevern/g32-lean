import HodgeLean.Foundations.Program.SchoenCycleDivisorInjectivity

/-! # Regular ratios of differential germs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Analytic divisibility makes the local meromorphic quotient regular.
Source: Forster, Lectures on Riemann Surfaces, §14, quotients of differential forms. -/
theorem s2e_divisible_form_ratio_nonneg
    (hE : Module.finrank ℂ E = 1) (u v : b4c_MeroForm E C hE)
    (p : C) (hv : meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (he : HurwitzPrymRR_loc hE u p =ᶠ[𝓝[≠] 0]
      (fun z => g z * HurwitzPrymRR_loc hE v p z)) :
    0 ≤ meromorphicOrderAt
      (fun z => HurwitzPrymRR_loc hE u p z / HurwitzPrymRR_loc hE v p z) 0 := by
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (v.property.2 p)).mp hv
  have heq : (fun z => HurwitzPrymRR_loc hE u p z /
      HurwitzPrymRR_loc hE v p z) =ᶠ[𝓝[≠] 0] g := by
    filter_upwards [he, hn] with z hz hnz
    rw [hz, mul_div_cancel_right₀ _ hnz]
  rw [meromorphicOrderAt_congr heq]
  exact hg.meromorphicOrderAt_nonneg

/-- A locally analytically divisible ratio on a compact connected curve is constant.
Source: Forster, Lectures on Riemann Surfaces, §2, maximum principle, and §14. -/
theorem s2e_divisible_form_ratio_constant
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (u v : b4c_MeroForm E C hE)
    (hu : (u : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hv : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hgu : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE u p) 0 ≠ ⊤)
    (hgv : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤)
    (hdiv : ∀ p, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      HurwitzPrymRR_loc hE u p =ᶠ[𝓝[≠] 0]
        (fun z => g z * HurwitzPrymRR_loc hE v p z)) :
    ∃ c : ℂ, ∀ p, b4c_formRatio (hE := hE) u v p = (c : OnePoint ℂ) := by
  let F : b4c_MeroFun E C := ⟨b4c_formRatio (hE := hE) u v,
    b4c_formRatio_isMeroFun_aux hE u v hu hv hgu hgv⟩
  have hf (p : C) : F p ≠ OnePoint.infty := by
    obtain ⟨g, hg, he⟩ := hdiv p
    have ho := s2e_divisible_form_ratio_nonneg hE u v p
      (b4c_meroForm_order_ne_top hE v hgv p) g hg he
    change b4c_formRatio (hE := hE) u v p ≠ OnePoint.infty
    simp only [b4c_formRatio, not_lt.mpr ho, ite_false]
    split <;> exact OnePoint.coe_ne_infty _
  have hc (p q : C) : F p = F q := by
    by_contra hn
    obtain ⟨x, hx⟩ := b4cov_surjective (by simp : Module.finrank ℂ ℂ = 1)
      F F.property.1 ⟨p, q, hn⟩ OnePoint.infty
    exact hf x hx
  let p : C := Classical.choice inferInstance
  obtain ⟨c, he⟩ := OnePoint.ne_infty_iff_exists.mp (hf p)
  exact ⟨c, fun q => (hc q p).trans he.symm⟩

/-- Local analytic divisibility of paired differentials identifies their parameters up to scale.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, tangent spaces to Abel fibres. -/
theorem s2e_divisible_paired_parameters_proportional
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (u v : b3_HolForm E C × (Fin r → ℂ)) (hv : v ≠ 0)
    (hdiv : ∀ p, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w u) p =ᶠ[𝓝[≠] 0]
        (fun z => g z * HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p z)) :
    ∃ c : ℂ, u = c • v := by
  by_cases hu : u = 0
  · exact ⟨0, by rw [hu, zero_smul]⟩
  let F := s2e_pairedDifferentialLinear hE w
  let U : b4c_MeroForm E C hE := ⟨F u, s2e_pairedDifferentialLinear_isMeroForm hE w u.1 u.2⟩
  let V : b4c_MeroForm E C hE := ⟨F v, s2e_pairedDifferentialLinear_isMeroForm hE w v.1 v.2⟩
  have hU : (U : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := by
    intro hz
    apply hu
    apply s2e_pairedDifferentialLinear_injective hE w x hres
    simpa only [map_zero] using hz
  have hV : (V : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := by
    intro hz
    apply hv
    apply s2e_pairedDifferentialLinear_injective hE w x hres
    simpa only [map_zero] using hz
  have hgU := s2e_pairedDifferentialLinear_exists_finite_order hE w x hres u.1 u.2 hu
  have hgV := s2e_pairedDifferentialLinear_exists_finite_order hE w x hres v.1 v.2 hv
  obtain ⟨c, hc⟩ := s2e_divisible_form_ratio_constant hE U V hU hV hgU hgV hdiv
  refine ⟨c, sub_eq_zero.mp ?_⟩
  apply s2e_pairedDifferential_germ_zero hE w x hres (u - c • v).1 (u - c • v).2
  intro p
  have hp := s2e_constant_formRatio_germ hE U V hgU hgV c hc p
  change HurwitzPrymRR_loc hE (F (u - c • v)) p =ᶠ[𝓝[≠] 0] (fun _ => (0 : ℂ))
  have he : HurwitzPrymRR_loc hE (F (u - c • v)) p =
      (fun z => HurwitzPrymRR_loc hE (F u) p z - c * HurwitzPrymRR_loc hE (F v) p z) := by
    rw [map_sub, map_smul]
    rfl
  rw [he]
  filter_upwards [hp] with z hz
  exact sub_eq_zero.mpr hz

end HodgeLean.Foundations.Program
