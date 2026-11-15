import HodgeLean.Foundations.Program.SchoenCyclePreparedVariation

/-! # Prepared variations in a linear differential family -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
namespace HodgeLean.Foundations.Program
local instance : Module ℂ ℂ := Semiring.toModule
local instance : NormedSpace ℂ ℂ := NormedField.toNormedSpace

/-- Stationary prepared coefficients give divisibility of the actual linear-family
variation, rather than only of a derivative of an auxiliary extension.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, tangent spaces to Abel fibres. -/
theorem s2e_linear_prepared_variation_divisible
    {m d : ℕ} (L : ℂ → ((Fin m → ℂ) →L[ℂ] ℂ))
    (a δ : Fin m → ℂ) (f u : (Fin m → ℂ) × ℂ → ℂ)
    (c : Fin d → (Fin m → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0)
    (hδ : ∀ j, fderiv ℂ (c j) 0 δ = 0)
    (hprep : f =ᶠ[𝓝 0] fun tz => u tz * monicInLast c tz)
    (hlinear : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ t, f (t, z) = L z (a + t)) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), L z δ = q z * L z a := by
  obtain ⟨q, hq, hd⟩ := s2e_prepared_variation_analytic_divisible f u c δ hf hu hu0 hc hδ hprep
  refine ⟨q, hq, ?_⟩
  have hs : Tendsto (fun z : ℂ => ((0 : Fin m → ℂ), z)) (𝓝 0) (𝓝 0) :=
    (continuous_const.prodMk continuous_id).tendsto 0
  have hev : ∀ᶠ z : ℂ in 𝓝 0, AnalyticAt ℂ f (0, z) := hs hf.eventually_analyticAt
  filter_upwards [hlinear, hd.filter_mono nhdsWithin_le_nhds,
    hev.filter_mono nhdsWithin_le_nhds] with z hz hdz hfz
  have hline : HasDerivAt (fun t : ℂ => (t • δ, z)) (δ, 0) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).smul_const δ).prodMk
      (hasDerivAt_const (0 : ℂ) z) using 1 <;> simp only [one_smul, id_eq]
  have hfz' : AnalyticAt ℂ f ((0 : ℂ) • δ, z) := by
    simpa only [zero_smul, Set.mem_preimage, Set.mem_ofPred_eq] using hfz
  have hFline : HasDerivAt (fun t : ℂ => f (t • δ, z))
      (fderiv ℂ f (0, z) (δ, 0)) 0 := by
    convert hfz'.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline using 1 <;>
      simp only [Function.comp_def, zero_smul]
  have ha : HasDerivAt (fun t : ℂ => a + t • δ) δ 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).smul_const δ).const_add a using 1 <;>
      simp only [one_smul, id_eq]
  have hLline : HasDerivAt (fun t : ℂ => L z (a + t • δ)) (L z δ) 0 := by
    convert (L z).hasFDerivAt.comp_hasDerivAt 0 ha using 1 <;>
      simp only [Function.comp_def]
  have he := hFline.unique (hLline.congr_of_eventuallyEq
    (Eventually.of_forall (fun t => hz (t • δ))))
  have hz0 := hz 0
  simp only [add_zero] at hz0
  simpa only [he, hz0] using hdz

/-- A nonzero punctured correction factor cancels from the prepared tangent calculation.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, local equations of divisors. -/
theorem s2e_corrected_linear_prepared_variation_divisible
    {m d : ℕ} (L : ℂ → ((Fin m → ℂ) →L[ℂ] ℂ))
    (a δ : Fin m → ℂ) (κ : ℂ → ℂ)
    (f u : (Fin m → ℂ) × ℂ → ℂ) (c : Fin d → (Fin m → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0)
    (hδ : ∀ j, fderiv ℂ (c j) 0 δ = 0)
    (hprep : f =ᶠ[𝓝 0] fun tz => u tz * monicInLast c tz)
    (hlinear : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ t, f (t, z) = κ z * L z (a + t))
    (hκ : ∀ᶠ z in 𝓝[≠] (0 : ℂ), κ z ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), L z δ = q z * L z a := by
  have hl : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ t,
      f (t, z) = (κ z • L z) (a + t) := by
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using hlinear
  obtain ⟨q, hq, he⟩ := s2e_linear_prepared_variation_divisible
    (fun z => κ z • L z) a δ f u c hf hu hu0 hc hδ hprep hl
  refine ⟨q, hq, ?_⟩
  filter_upwards [he, hκ] with z hz hκz
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hz
  apply mul_left_cancel₀ hκz
  calc
    κ z * L z δ = q z * (κ z * L z a) := hz
    _ = κ z * (q z * L z a) := by ring

end HodgeLean.Foundations.Program
