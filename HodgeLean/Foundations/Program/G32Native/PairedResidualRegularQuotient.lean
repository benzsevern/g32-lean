import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemInjectivity
import HodgeLean.Foundations.Program.SchoenCycleRegularRatio
import HodgeLean.Foundations.Program.SchoenCycleDivisorInjectivity

/-! # Regular quotients in normalized differential spaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters Filter
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- A locally analytically divisible variation in a normalized differential space is scalar. -/
theorem residual_normalized_divisible_proportional
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (S : Set C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ S, ∀ u, q.val ⟨p, u⟩ = 0)
    (u v : W) (hv : v ≠ 0)
    (hdiv : ∀ p, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      HurwitzPrymRR_loc hE u.val p =ᶠ[𝓝[≠] 0]
        (fun z => g z * HurwitzPrymRR_loc hE v.val p z)) :
    ∃ c : ℂ, u = c • v := by
  by_cases hu : u = 0
  · exact ⟨0, by rw [hu, zero_smul]⟩
  let U : b4c_MeroForm E C hE := ⟨u.val, (hW u).1⟩
  let V : b4c_MeroForm E C hE := ⟨v.val, (hW v).1⟩
  have hU : (U : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun h => hu (Subtype.ext h)
  have hV : (V : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun h => hv (Subtype.ext h)
  have hgU := residual_normalized_form_has_finite_order hE S U hU (hW u).2.1 (hW u).2.2
  have hgV := residual_normalized_form_has_finite_order hE S V hV (hW v).2.1 (hW v).2.2
  obtain ⟨c, hr⟩ := s2e_divisible_form_ratio_constant hE U V hU hV hgU hgV hdiv
  refine ⟨c, sub_eq_zero.mp (Subtype.ext ?_)⟩
  apply RiemannRochEichler_regular_zero_of_zero_germs hE (u - c • v).val
    (hW (u - c • v)).1.1 S (hW (u - c • v)).2.1 (hW (u - c • v)).2.2
  intro p
  have hp := s2e_constant_formRatio_germ hE U V hgU hgV c hr p
  have he : HurwitzPrymRR_loc hE (u - c • v).val p =
      (fun z => HurwitzPrymRR_loc hE U p z - c * HurwitzPrymRR_loc hE V p z) := by
    rfl
  rw [he]
  filter_upwards [hp] with z hz
  exact sub_eq_zero.mpr hz

#print axioms residual_normalized_divisible_proportional
end HodgeLean.Foundations.Program.G32Native
