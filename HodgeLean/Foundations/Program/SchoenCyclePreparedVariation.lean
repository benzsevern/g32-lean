import HodgeLean.Foundations.Program.SchoenCyclePreparedResidues
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Parameter variations of prepared local divisor equations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open scoped BigOperators
namespace HodgeLean.Foundations.Program
local instance : Module ℂ ℂ := Semiring.toModule
local instance : NormedSpace ℂ ℂ := NormedField.toNormedSpace

/-- A direction preserving all prepared coefficients gives an analytically
locally divisible first variation, with repeated roots retained.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, tangent spaces to Abel fibres;
Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Theorem 2. -/
theorem s2e_prepared_variation_analytic_divisible
    {m d : ℕ} (f u : (Fin m → ℂ) × ℂ → ℂ)
    (c : Fin d → (Fin m → ℂ) → ℂ) (δ : Fin m → ℂ)
    (hf : AnalyticAt ℂ f 0) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0)
    (hδ : ∀ j, fderiv ℂ (c j) 0 δ = 0)
    (hprep : f =ᶠ[𝓝 0] fun tz => u tz * monicInLast c tz) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ z in 𝓝 0, fderiv ℂ f (0, z) (δ, 0) = q z * f (0, z) := by
  let q : ℂ → ℂ := fun z => fderiv ℂ u (0, z) (δ, 0) / u (0, z)
  have hdu : AnalyticAt ℂ (fun z : ℂ => fderiv ℂ u (0, z) (δ, 0)) 0 :=
    (((ContinuousLinearMap.apply ℂ ℂ (δ, (0 : ℂ))).analyticAt _).comp hu.fderiv).comp
      (f := fun z : ℂ => ((0 : Fin m → ℂ), z)) (analyticAt_const.prod analyticAt_id)
  have hus : AnalyticAt ℂ (fun z : ℂ => u (0, z)) 0 :=
    hu.comp (f := fun z : ℂ => ((0 : Fin m → ℂ), z))
      (analyticAt_const.prod analyticAt_id)
  refine ⟨q, hdu.div hus hu0, ?_⟩
  have hs : Tendsto (fun z : ℂ => ((0 : Fin m → ℂ), z)) (𝓝 0) (𝓝 0) :=
    (continuous_const.prodMk continuous_id).tendsto 0
  filter_upwards [hs hprep.eventuallyEq_nhds, hs hu.eventually_analyticAt,
    hs hf.eventually_analyticAt, hus.continuousAt.eventually_ne hu0]
    with z hprepz huz hfz hune
  have hline : HasDerivAt (fun t : ℂ => (t • δ, z)) (δ, 0) 0 :=
    by
      convert ((hasDerivAt_id (0 : ℂ)).smul_const δ).prodMk
        (hasDerivAt_const (0 : ℂ) z) using 1 <;> simp only [one_smul, id_eq]
  have hcline (j : Fin d) : HasDerivAt (fun t : ℂ => c j (t • δ)) 0 0 := by
    have hcj : AnalyticAt ℂ (c j) ((0 : ℂ) • δ) := by simpa only [zero_smul] using hc j
    have h := hcj.differentiableAt.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℂ)).smul_const δ)
    simpa only [zero_smul, one_smul, id_eq, Function.comp_def, hδ j] using h
  have hPline : HasDerivAt (fun t : ℂ => monicInLast c (t • δ, z)) 0 0 := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (hcline j).mul_const (z ^ (j : ℕ)))
    convert (hasDerivAt_const (0 : ℂ) (z ^ d)).add hsum using 1 <;>
      simp only [monicInLast, zero_mul, Finset.sum_const_zero, add_zero]
    funext t
    rfl
  have hUline : HasDerivAt (fun t : ℂ => u (t • δ, z))
      (fderiv ℂ u (0, z) (δ, 0)) 0 := by
    have huz' : AnalyticAt ℂ u ((0 : ℂ) • δ, z) := by simpa only [zero_smul, Set.mem_preimage, Set.mem_setOf_eq] using huz
    convert huz'.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline using 1 <;>
      simp only [Function.comp_def, zero_smul]
  have hFline : HasDerivAt (fun t : ℂ => f (t • δ, z))
      (fderiv ℂ f (0, z) (δ, 0)) 0 := by
    have hfz' : AnalyticAt ℂ f ((0 : ℂ) • δ, z) := by simpa only [zero_smul, Set.mem_preimage, Set.mem_setOf_eq] using hfz
    convert hfz'.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline using 1 <;>
      simp only [Function.comp_def, zero_smul]
  have he : (fun t : ℂ => f (t • δ, z)) =ᶠ[𝓝 0]
      fun t => u (t • δ, z) * monicInLast c (t • δ, z) := by
    apply hprepz.comp_tendsto
    simpa only [zero_smul] using hline.continuousAt.tendsto
  have hd := hFline.unique ((hUline.mul hPline).congr_of_eventuallyEq he)
  simp only [zero_smul, mul_zero, add_zero] at hd
  rw [hd, hprepz.self_of_nhds]
  change fderiv ℂ u (0, z) (δ, 0) * monicInLast c (0, z) =
    (fderiv ℂ u (0, z) (δ, 0) / u (0, z)) * (u (0, z) * monicInLast c (0, z))
  field_simp

end HodgeLean.Foundations.Program
