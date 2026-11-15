import HodgeLean.Foundations.Curves.AbelTheorem.AvoidingDual
import HodgeLean.Foundations.Curves.AbelTheorem.CoverCompactSet
import HodgeLean.Foundations.Curves.AbelTheorem.CutoffPrimitives
import HodgeLean.Foundations.Curves.AbelTheorem.SmoothCutoff
import HodgeLean.Foundations.Curves.AbelTheorem.ProjectedPathIntegral
import HodgeLean.Foundations.Curves.AbelTheorem.Normalization

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem local_dual_pairs_meromorphic_form (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (γ : b3_SmoothLoop E C) (hav : ∀ t, γ.val t ∉ D.support)
    (K : b3Rest_Cover E γ.val)
    (hK : ∀ k, closedBall (chartAt E (K.x k) (K.x k)) (K.r k) ⊆
      (chartAt E (K.x k)).target ∧ (chartAt E (K.x k)).symm ''
        closedBall (chartAt E (K.x k) (K.x k)) (K.r k) ⊆ (D.support : Set C)ᶜ)
    (η : C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hout : ∀ y, (∀ k : ℤ, y ∉ (chartAt E (K.x k)).symm ''
      ball (chartAt E (K.x k) (K.x k)) (K.r k)) → η y = 0)
    (hpair : ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α →
      ∀ f : ℤ → E → ℝ, (∀ k, ∀ u ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k),
        HasFDerivAt (f k) (b3Forms_toCLM (b3Forms_loc α (K.x k) u)) u) →
      b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α η) =
        b3Forms_lineIntegral α γ.val 0 1) :
    ∀ P : ℂ →L[ℝ] ℝ, b3Forms_integral (b3Rest_b h)
      (b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) η) =
      P (loopIntegral γ w) := by
  classical
  let S : Set C := D.support
  have hS : IsClosed S := D.support.finite_toSet.isClosed
  obtain ⟨A, hA, hAS, hKA⟩ := compact_set_containing_loop_cover K S hK
  obtain ⟨μ, hμ, hμzero, hμone⟩ := smooth_cutoff_of_disjoint_closed (E := E) S A
    hS hA.isClosed (Set.disjoint_left.mpr fun y hy hyA => hAS hyA hy)
  have hpoles : ∀ y, meromorphicOrderAt (HurwitzPrymRR_loc h w y) 0 < 0 → μ =ᶠ[𝓝 y] 0 := by
    intro y hy
    by_cases hys : y ∈ D.support
    · exact hμzero y hys
    · exact False.elim ((not_lt_of_ge (ha y hys).meromorphicOrderAt_nonneg) hy)
  intro P
  let θ : TangentBundle 𝓘(ℂ, E) C → ℂ :=
    fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm h w v
  let α := b4c_residue_realForm h θ P
  have hα : b3Forms_IsSmooth α := b4c_residue_smooth_global h w μ hμ hpoles P
  have hpr (k : ℤ) := cutoff_form_primitive_on_chart h w μ hμ hpoles P (K.x k)
    (convex_ball _ _) isOpen_ball (K.ball_sub k)
    (fun u hu => hμone _ (hKA k ⟨u, hu, rfl⟩))
  choose f hf using hpr
  have he := hpair α hα f hf
  have hwed : b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) η =
      b3Forms_wedgeForm α η := by
    funext y
    by_cases hm : μ y = 1
    · simp only [b3Forms_wedgeForm, α, θ, b4c_residue_realForm, hm,
        Complex.ofReal_one, one_mul]
    · have hz : η y = 0 := hout y (fun k hk =>
        hm ((hμone y (hKA k hk)).self_of_nhds))
      ext v
      simp only [b3Forms_wedgeForm, hz, b3Forms_wedge_apply,
        ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero, sub_self]
  rw [hwed, he]
  have hθ : HurwitzPrymRR_IsLinear θ := by
    intro y a v v'
    change (μ y : ℂ) * _ = a * ((μ y : ℂ) * _) + (μ y : ℂ) * _
    rw [b4c_residue_normalizedForm_linear h w]
    ring
  have hθγ (t : ℝ) : θ ⟨γ.val t, b3_velocity E C γ.val t⟩ =
      w ⟨γ.val t, b3_velocity E C γ.val t⟩ := by
    have hyA : γ.val t ∈ A := by
      have hcov := K.mem (⌊K.N * t⌋) (K.N * t - ⌊K.N * t⌋)
      have ht : K.N * t - (⌊K.N * t⌋ : ℝ) ∈ Icc (0 : ℝ) 1 :=
        ⟨sub_nonneg.mpr (Int.floor_le _), by linarith [Int.lt_floor_add_one ((K.N : ℝ) * t)]⟩
      have hv := hcov ht
      have heq : (((⌊(K.N : ℝ) * t⌋ : ℤ) : ℝ) + (K.N * t - ⌊K.N * t⌋)) / K.N = t := by
        have hn : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr K.pos.ne'
        field_simp
        ring
      rw [heq] at hv
      apply hKA ⌊(K.N : ℝ) * t⌋
      exact ⟨_, hv.2, (chartAt E (K.x ⌊(K.N : ℝ) * t⌋)).left_inv hv.1⟩
    simp only [θ, (hμone _ hyA).self_of_nhds, Complex.ofReal_one, one_mul,
      b4c_residue_normalizedForm_eq h w _ (ha _ (hav t))]
  have hint : IntervalIntegrable
      (fun t => w ⟨γ.val t, b3_velocity E C γ.val t⟩) volume 0 1 :=
    (continuous_integrand_off_support h D w ha γ.val γ.property.2 hav).intervalIntegrable 0 1
  have hintθ : IntervalIntegrable (fun t => θ ⟨γ.val t, b3_velocity E C γ.val t⟩) volume 0 1 := by
    simpa only [hθγ] using hint
  rw [projected_form_path_integral h θ hθ P γ.val hintθ]
  congr 1
  unfold loopIntegral b3_pathIntegral
  exact intervalIntegral.integral_congr (fun t _ => hθγ t)

end HodgeLean.Foundations.Curves.AbelTheorem
