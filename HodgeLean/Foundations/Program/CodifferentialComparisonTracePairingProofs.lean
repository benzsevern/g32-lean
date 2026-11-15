import HodgeLean.Foundations.Program.CodifferentialComparisonResidueInvariantProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonGraphProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonDefs


noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers Metric
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] b3Forms_isManifold_real
variable {c₀ : Fin 10 → ℂ} {g₀ : Fin 13 → b4b_Group}

theorem b66f_gen_b66m_form_analytic (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (m : ℕ) (q : b66f_forms R t m) (a : b66f_Index R) :
    AnalyticOnNhd ℂ (fun z => q.val a ((R.atlas.A a).symm (t.val, z)).2)
      (b66f_domain R t a) := by
  rcases q with ⟨q, hq⟩
  change AnalyticOnNhd ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2) _
  change q ∈ Submodule.span ℂ _ at hq
  induction hq using Submodule.span_induction with
  | mem q hq => exact hq.1 a
  | zero => exact analyticOnNhd_const
  | add q r _ _ hq hr => exact hq.add hr
  | smul c q _ hq => exact analyticOnNhd_const.mul hq

theorem b66f_gen_b66m_form_transition (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (m : ℕ) (q : b66f_forms R t m) (a b : b66f_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source) :
    q.val a x = b66f_vertical R t a b x ^ m * q.val b x := by
  rcases q with ⟨q, hq⟩
  change q a x = b66f_vertical R t a b x ^ m * q b x
  change q ∈ Submodule.span ℂ _ at hq
  induction hq using Submodule.span_induction with
  | mem q hq => exact hq.2.1 a b x ha hb
  | zero => exact (mul_zero _).symm
  | add q r _ _ hq hr =>
    change q a x + r a x = _ * (q b x + r b x)
    rw [hq, hr, mul_add]
  | smul c q _ hq =>
    change c * q a x = _ * (c * q b x)
    rw [hq]
    ring

theorem b66f_gen_b66m_tensor_splitting (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (u : b66f_Cochain R) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hm : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_boundary R t v a b x)
    (q : b66f_forms R t 1) :
    let w := fun a z => q.val a ((R.atlas.A a).symm (t.val, z)).2 * v a z
    (∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (w a) z) ∧
    (∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (w a) z) ∧
    ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_gen_b66g_contract R q.val u a b x = b66f_gen_b66g_scalarBoundary R t w a b x := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro a z hz
    exact ((b66f_gen_b66m_form_analytic R t 1 q a) z hz).meromorphicAt.mul (hm a z hz)
  · intro a z hz hx
    exact ((b66f_gen_b66m_form_analytic R t 1 q a) z hz).mul (hr a z hz hx)
  · intro a b x hx ha hb
    have hpa : (t.val, (R.atlas.A a (t, x)).2) = R.atlas.A a (t, x) :=
      Prod.ext (R.atlas.hparam a (t, x) ha).symm rfl
    have hpb : (t.val, (R.atlas.A b (t, x)).2) = R.atlas.A b (t, x) :=
      Prod.ext (R.atlas.hparam b (t, x) hb).symm rfl
    simp only [b66f_gen_b66g_contract, hv a b x hx ha hb, b66f_boundary,
      b66f_gen_b66g_scalarBoundary, Set.mem_inter_iff, ha, hb, and_self, ite_true,
      hpa, hpb, (R.atlas.A a).left_inv ha, (R.atlas.A b).left_inv hb]
    have ht := b66f_gen_b66m_form_transition R t 1 q a b x ha hb
    rw [pow_one] at ht
    rw [ht]
    ring

theorem b66f_gen_b66m_re01_wedge_eq_inner (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    letI : Fact (Module.finrank ℂ ℂ = 1) := ⟨Module.finrank_self ℂ⟩
    b3Forms_integral (b3Rest_b (Module.finrank_self ℂ))
      (b3Forms_wedgeForm (RiemannRochAna_re01 β) (b3Forms_reForm θ)) =
      -inner ℝ (RiemannRochAna_re01L2 β)
        (RiemannRochAna_holRealL2 ((-Complex.I) • θ)) := by
  letI : Fact (Module.finrank ℂ ℂ = 1) := ⟨Module.finrank_self ℂ⟩
  let a := b3Rest_SF.mk (RiemannRochAna_re01 β) (RiemannRochAna_re01_smooth β)
  let h := b3Rest_SF.mk (b3Forms_star (b3Forms_reForm θ)) (b3Forms_isSmooth_reForm θ).star
  have heq : (h : b3Rest_L2 ℂ (b65z_fibre c₀ R.C t)) =
      RiemannRochAna_holRealL2 ((-Complex.I) • θ) := by
    apply congrArg (fun x : b3Rest_SF ℂ (b65z_fibre c₀ R.C t) =>
      (x : b3Rest_L2 ℂ (b65z_fibre c₀ R.C t)))
    apply b3Rest_SF.ext
    exact (b3Forms_star_reForm θ).trans (b3Forms_imForm_eq θ)
  have ht : inner ℝ (RiemannRochAna_re01L2 β)
      (RiemannRochAna_holRealL2 ((-Complex.I) • θ)) =
      -b3Forms_integral (b3Rest_b (Module.finrank_self ℂ))
        (b3Forms_wedgeForm (RiemannRochAna_re01 β) (b3Forms_reForm θ)) := by
    rw [← heq]
    change inner ℝ (a : b3Rest_L2 ℂ (b65z_fibre c₀ R.C t))
      (h : b3Rest_L2 ℂ (b65z_fibre c₀ R.C t)) = _
    rw [UniformSpace.Completion.inner_coe]
    exact b3Rest_inner_star_eq a (b3Forms_isSmooth_reForm θ)
  linarith

theorem b66f_gen_b66m_dolbeaultIntegral_add_left (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (β γ : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_dolbeaultIntegral R t (β + γ) θ =
      b66f_gen_b66m_dolbeaultIntegral R t β θ + b66f_gen_b66m_dolbeaultIntegral R t γ θ := by
  simp only [b66f_gen_b66m_dolbeaultIntegral, b66f_gen_b66m_re01_wedge_eq_inner, map_add,
    inner_add_left, Complex.ofReal_add, Complex.ofReal_neg]
  ring

theorem b66f_gen_b66m_dbar_integral_zero (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (u : b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t))
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b3Forms_integral (b3Rest_b (Module.finrank_self ℂ))
      (b3Forms_wedgeForm
        (RiemannRochAna_re01
          (⟨b4c_dbar ℂ (b65z_fibre c₀ R.C t) u, b4c_dbar_mem_aux u⟩ :
            b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)))
        (b3Forms_reForm θ)) = 0 := by
  letI : Fact (Module.finrank ℂ ℂ = 1) := ⟨Module.finrank_self ℂ⟩
  let β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t) :=
    ⟨b4c_dbar ℂ (b65z_fibre c₀ R.C t) u, b4c_dbar_mem_aux u⟩
  let a := b3Rest_SF.mk (RiemannRochAna_re01 β) (RiemannRochAna_re01_smooth β)
  let h := b3Rest_SF.mk (b3Forms_star (b3Forms_reForm θ)) (b3Forms_isSmooth_reForm θ).star
  have heq : (h : b3Rest_L2 ℂ (b65z_fibre c₀ R.C t)) =
      RiemannRochAna_holRealL2 ((-Complex.I) • θ) := by
    apply congrArg (fun x : b3Rest_SF ℂ (b65z_fibre c₀ R.C t) =>
      (x : b3Rest_L2 ℂ (b65z_fibre c₀ R.C t)))
    apply b3Rest_SF.ext
    exact (b3Forms_star_reForm θ).trans (b3Forms_imForm_eq θ)
  have hh : (h : b3Rest_L2 ℂ (b65z_fibre c₀ R.C t)) ∈
      (b3Rest_Ex ℂ (b65z_fibre c₀ R.C t) ⊔ b3Rest_Co ℂ (b65z_fibre c₀ R.C t))ᗮ := by
    rw [heq, ← Submodule.inf_orthogonal]
    exact RiemannRochAna_range_le_harmonic ⟨(-Complex.I) • θ, rfl⟩
  have ha : (a : b3Rest_L2 ℂ (b65z_fibre c₀ R.C t)) ∈
      b3Rest_Ex ℂ (b65z_fibre c₀ R.C t) ⊔ b3Rest_Co ℂ (b65z_fibre c₀ R.C t) :=
    RiemannRochAna_re01_dbar_mem u
  have hz : inner ℝ a h = 0 := by
    have ht := ((Submodule.mem_orthogonal' _ _).mp hh) _ ha
    rw [real_inner_comm, UniformSpace.Completion.inner_coe] at ht
    exact ht
  have ht := b3Rest_inner_star_eq a (b3Forms_isSmooth_reForm θ)
  change inner ℝ a h = -_ at ht
  rw [hz] at ht
  change b3Forms_integral (b3Rest_b (Module.finrank_self ℂ))
    (b3Forms_wedgeForm a.form (b3Forms_reForm θ)) = 0
  linarith

theorem b66f_gen_b66m_dolbeaultIntegral_dbar (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (u : b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_dolbeaultIntegral R t
      ⟨b4c_dbar ℂ (b65z_fibre c₀ R.C t) u, b4c_dbar_mem_aux u⟩ θ = 0 := by
  rw [b66f_gen_b66m_dolbeaultIntegral, b66f_gen_b66m_dbar_integral_zero R t u θ,
    b66f_gen_b66m_dbar_integral_zero R t u (Complex.I • θ)]
  simp

theorem b66f_gen_b66m_dolbeaultIntegral_class_invariant (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (β γ : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t))
    (hc : (Submodule.Quotient.mk β : b4c_Dolbeault01 ℂ (b65z_fibre c₀ R.C t)) =
      Submodule.Quotient.mk γ) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_dolbeaultIntegral R t β θ = b66f_gen_b66m_dolbeaultIntegral R t γ θ := by
  let P := (Submodule.span ℂ (b4c_dbar ℂ (b65z_fibre c₀ R.C t) ''
    (b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t) : Set (b65z_fibre c₀ R.C t → ℂ)))).comap
      (b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)).subtype
  have hz : P.mkQ (β - γ) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hc
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  change β.val - γ.val ∈ Submodule.span ℂ (b4c_dbar ℂ (b65z_fibre c₀ R.C t) ''
    (b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t) : Set (b65z_fibre c₀ R.C t → ℂ))) at hm
  rw [← SetLike.mem_coe, b4c_dbar_image_eq_aux (Module.finrank_self ℂ)] at hm
  obtain ⟨u, hu, hdu⟩ := hm
  have heq : β = γ +
      (⟨b4c_dbar ℂ (b65z_fibre c₀ R.C t) u, b4c_dbar_mem_aux ⟨u, hu⟩⟩ :
        b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) := by
    apply Subtype.ext
    change β.val = γ.val + b4c_dbar ℂ (b65z_fibre c₀ R.C t) u
    rw [hdu]
    abel
  rw [heq, b66f_gen_b66m_dolbeaultIntegral_add_left,
    b66f_gen_b66m_dolbeaultIntegral_dbar R t ⟨u, hu⟩ θ, add_zero]

theorem b66f_gen_b66m_dolbeaultTrace_mk (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_dolbeaultTrace R t (Submodule.Quotient.mk β) θ =
      b66f_gen_b66m_dolbeaultIntegral R t β θ := by
  let P := (Submodule.span ℂ (b4c_dbar ℂ (b65z_fibre c₀ R.C t) ''
    (b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t) : Set (b65z_fibre c₀ R.C t → ℂ)))).comap
      (b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)).subtype
  change b66f_gen_b66m_dolbeaultIntegral R t (Classical.choose (P.mkQ_surjective (P.mkQ β))) θ = _
  apply b66f_gen_b66m_dolbeaultIntegral_class_invariant
  exact Classical.choose_spec (P.mkQ_surjective (P.mkQ β))

theorem b66f_gen_b66m_cechTrace_cycle (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_gen_b66g_scalarCycles R t) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_cechTrace R t ρ hρ (b66f_gen_b66m_sc_cechProjection R t u) θ =
      b66f_gen_b66m_dolbeaultIntegral R t
        ⟨b66f_gen_b66m_sc_gamma R t ρ u.val, b66f_gen_b66m_sc_gamma_mem R t ρ hρ u.property⟩ θ := by
  unfold b66f_gen_b66m_cechTrace
  rw [(Classical.choose_spec (b66f_gen_b66m_sc_comparison R t ρ hρ)).2 u]
  exact b66f_gen_b66m_dolbeaultTrace_mk R t _ θ

end HodgeLean.Foundations.Program
