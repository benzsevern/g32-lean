import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold Filter Topology
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]

theorem continuous_integrand_off_support (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (hav : ∀ t, γ t ∉ D.support) :
    Continuous (fun t => w ⟨γ t, b3_velocity E C γ t⟩) := by
  let δ : ℝ → divisorComplement D := fun t => ⟨γ t, hav t⟩
  have hd : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ := by
    intro t
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1) δ Set.univ t).mp (hγ t)
  have hc := b3A_continuous_integrand δ hd (divisorDifferentialRestriction h D w ha)
  have he (t : ℝ) : w ⟨γ t, b3_velocity E C γ t⟩ =
      (divisorDifferentialRestriction h D w ha :
        TangentBundle 𝓘(ℂ, E) (divisorComplement D) → ℂ) ⟨δ t, b3_velocity E (divisorComplement D) δ t⟩ := by
    rw [show γ = (fun x : divisorComplement D => (x : C)) ∘ δ from rfl,
      b3A_velocity_comp _ contMDiff_subtype_val δ hd t]
    rfl
  simpa only [← he] using hc

variable [FiniteDimensional ℂ E] [CompactSpace C] [ConnectedSpace C]

theorem normalized_third_kind_construction (h : Module.finrank ℂ E = 1) (p : C)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (F : PeriodFrame (E := E) D) :
    ∃ w : b4c_MeroForm E C h,
      (∀ x, b4c_res (hE := h) w x = (D x : ℂ)) ∧
      (∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0) ∧
      (∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0) ∧
      ∀ i, loopIntegral (F.a i) w = 0 := by
  classical
  obtain ⟨w, hr, ho, ha⟩ := thirdKindDifferential_supported_on_divisor h p D hdeg
  let v : b3_HolForm E C := ∑ j, loopIntegral (F.a j) w • F.forms j
  obtain ⟨hm, hres⟩ := RiemannRochEichler_sub_holForm h w v
  let w' : b4c_MeroForm E C h := ⟨fun t => w t - v.val t, hm⟩
  have hloc (x : C) : HurwitzPrymRR_loc h w' x =
      HurwitzPrymRR_loc h w x - HurwitzPrymRR_loc h v x := rfl
  refine ⟨w', fun x => (hres x).trans (hr x), ?_, ?_, ?_⟩
  · intro x
    rw [hloc, sub_eq_add_neg]
    have hv := (RiemannRochEichler_loc_analytic h v x).neg
    have hn : (-1 : WithTop ℤ) ≤ 0 := by
      change ((-1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ)
      exact_mod_cast (show (-1 : ℤ) ≤ 0 by omega)
    exact (le_min (ho x) (hn.trans hv.meromorphicOrderAt_nonneg)).trans
      (meromorphicOrderAt_add (w.property.2 x) hv.meromorphicAt)
  · intro x hx
    rw [hloc]
    exact (ha x hx).sub (RiemannRochEichler_loc_analytic h v x)
  · intro i
    have hv : loopIntegral (F.a i) v = loopIntegral (F.a i) w := by
      have hl := b3A_pathPeriod_linear (F.a i).val (F.a i).property.2
      let L : b3_HolForm E C →ₗ[ℂ] ℂ := b3A_toDual ⟨_, hl⟩
      change L v = _
      simp only [v, map_sum, map_smul, smul_eq_mul]
      change (∑ j, loopIntegral (F.a j) w * loopIntegral (F.a i) (F.forms j)) = _
      simp only [F.normalized, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    change b3_pathIntegral E C (F.a i).val (fun t => w t - v.val t) = 0
    unfold b3_pathIntegral
    rw [intervalIntegral.integral_sub
      ((continuous_integrand_off_support h D w ha (F.a i).val
        (F.a i).property.2 (F.a_avoids i)).intervalIntegrable 0 1)
      ((b3A_continuous_integrand (F.a i).val (F.a i).property.2 v).intervalIntegrable 0 1)]
    exact sub_eq_zero.mpr hv.symm

end HodgeLean.Foundations.Curves.AbelTheorem
