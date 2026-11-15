import HodgeLean.Foundations.Program.SchoenCycleDivisorInjectivity

/-! # Normalizing assigned values at the marked poles -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Set the assigned values at the marked poles to zero, retaining all other values. -/
def residual_normalize_poles (S : Finset C) :
    (TangentBundle 𝓘(ℂ, E) C → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, E) C → ℂ) := by
  classical
  exact {
    toFun := fun w t => if t.1 ∈ S then 0 else w t
    map_add' := by
      intro w v
      funext t
      by_cases ht : t.1 ∈ S <;> simp only [ht, ite_true, ite_false, Pi.add_apply, add_zero]
    map_smul' := by
      intro a w
      funext t
      by_cases ht : t.1 ∈ S <;>
        simp only [ht, ite_true, ite_false, Pi.smul_apply, smul_zero, RingHom.id_apply] }

#print axioms residual_normalize_poles

/-- Normalizing the assigned pole values retains every punctured coefficient germ. -/
theorem residual_normalize_poles_loc [T1Space C]
    (hE : Module.finrank ℂ E = 1) (S : Finset C)
    (w : TangentBundle 𝓘(ℂ, E) C → ℂ) (p : C) :
    HurwitzPrymRR_loc hE (residual_normalize_poles S w) p =ᶠ[𝓝[≠] 0]
      HurwitzPrymRR_loc hE w p := by
  classical
  apply RiemannRochEichler_loc_congr_off_finite hE (S : Set C) S.finite_toSet
  intro q hq u
  change (if q ∈ S then 0 else w ⟨q, u⟩) = w ⟨q, u⟩
  exact if_neg hq

#print axioms residual_normalize_poles_loc

end HodgeLean.Foundations.Program.G32Native
