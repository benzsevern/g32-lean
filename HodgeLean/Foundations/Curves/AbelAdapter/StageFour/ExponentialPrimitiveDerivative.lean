import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.ExponentialPathIntegral

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology Set Metric
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §10, differentiation of exponentiated path integrals. -/
theorem exponentialPrimitive_disc_derivative
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [ConnectedSpace C] (θ : b3_HolForm E C) (p : C) (F : C → ℂ)
    (hF : ∀ (q : C) (γ : ℝ → C), b3A_IsGoodPath (E := E) γ p q →
      F q = Complex.exp (b3_pathIntegral E C γ θ))
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ v : E, v = κ v • u)
    (hκu : κ u = 1) (hu : u ≠ 0) (q : C) :
    HasDerivAt (fun z => F (b3A_disc q u z))
      (F q * b3A_discCoef θ q u 0) 0 := by
  obtain ⟨γ, hγ⟩ := b3A_joined (E := E) p q
  obtain ⟨R, hR0, hR⟩ := b3A_chart_radius u hu q
  obtain ⟨G, hG⟩ : Complex.IsExactOn
      (b3A_discCoef (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) q u) (ball (0 : ℂ) R) :=
    DifferentiableOn.isExactOn_ball fun z hz => (b3A_discCoef_differentiableAt θ.property q u
      (hR z (mem_ball_zero_iff.mp hz))).differentiableWithinAt
  have he : (fun z => F (b3A_disc q u z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => F q * Complex.exp (G z - G 0)) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hR0] with z hz
    have hzn := mem_ball_zero_iff.mp hz
    have hs := b3A_isGoodPath_segment q (chartAt E q q) (chartAt E q q + z • u)
      (b3A_segment_subset u q hR z hzn)
    rw [(chartAt E q).left_inv (mem_chart_source E q)] at hs
    change F ((chartAt E q).symm (chartAt E q q + z • u)) = _
    rw [hF _ _ (hγ.trans hs), b3A_pathIntegral_trans θ.property hγ hs,
      b3A_segment_integral θ.property κ u hκ hκu q hR hG z hzn,
      Complex.exp_add, ← hF q γ hγ]
  have hd := (((hG 0 (mem_ball_self hR0)).sub_const (G 0)).cexp).const_mul (F q)
  simpa only [sub_self, Complex.exp_zero, one_mul] using hd.congr_of_eventuallyEq he

/-- Source: Forster, Lectures on Riemann Surfaces, §10, the logarithmic equation on a coordinate disc. -/
theorem exponentialPrimitive_disc_equation
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [ConnectedSpace C] (θ : b3_HolForm E C) (p : C) (F : C → ℂ)
    (hF : ∀ (q : C) (γ : ℝ → C), b3A_IsGoodPath (E := E) γ p q →
      F q = Complex.exp (b3_pathIntegral E C γ θ))
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ v : E, v = κ v • u)
    (hκu : κ u = 1) (hu : u ≠ 0) (q : C) :
    ∃ R > 0, (∀ z : ℂ, ‖z‖ < R → chartAt E q q + z • u ∈ (chartAt E q).target) ∧
      ∀ z ∈ ball (0 : ℂ) R, HasDerivAt (fun t => F (b3A_disc q u t))
        (b3A_discCoef θ q u z * F (b3A_disc q u z)) z := by
  obtain ⟨γ, hγ⟩ := b3A_joined (E := E) p q
  obtain ⟨R, hR0, hR⟩ := b3A_chart_radius u hu q
  obtain ⟨G, hG⟩ : Complex.IsExactOn
      (b3A_discCoef (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) q u) (ball (0 : ℂ) R) :=
    DifferentiableOn.isExactOn_ball fun z hz => (b3A_discCoef_differentiableAt θ.property q u
      (hR z (mem_ball_zero_iff.mp hz))).differentiableWithinAt
  have he (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      F (b3A_disc q u z) = F q * Complex.exp (G z - G 0) := by
    have hzn := mem_ball_zero_iff.mp hz
    have hs := b3A_isGoodPath_segment q (chartAt E q q) (chartAt E q q + z • u)
      (b3A_segment_subset u q hR z hzn)
    rw [(chartAt E q).left_inv (mem_chart_source E q)] at hs
    change F ((chartAt E q).symm (chartAt E q q + z • u)) = _
    rw [hF _ _ (hγ.trans hs), b3A_pathIntegral_trans θ.property hγ hs,
      b3A_segment_integral θ.property κ u hκ hκu q hR hG z hzn,
      Complex.exp_add, ← hF q γ hγ]
  refine ⟨R, hR0, hR, fun z hz => ?_⟩
  have hev : (fun t => F (b3A_disc q u t)) =ᶠ[𝓝 z]
      (fun t => F q * Complex.exp (G t - G 0)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with t ht
    exact he t ht
  have hd := (((hG z hz).sub_const (G 0)).cexp).const_mul (F q)
  convert hd.congr_of_eventuallyEq hev using 1
  rw [he z hz]
  ring

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
