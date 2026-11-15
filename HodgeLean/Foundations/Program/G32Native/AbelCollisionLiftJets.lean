import HodgeLean.Foundations.Program.G32Native.AbelCollisionCoefficientContinuity
import HodgeLean.Foundations.Program.G32Native.AbelCollisionBlockJets
import HodgeLean.Foundations.Program.G32Native.AbelLocalTraceDescent

/-! # The scalar jet criterion for an actual quotient Abel trace -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- A zero scalar differential of an actual Abel lift retains every block multiplicity order. -/
theorem collision_quotient_lift_jet_orders
    {A : Type} [Fintype A] [DecidableEq A] (m : A → ℕ)
    {V T : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace T] [AddCommGroup T]
    (q : V →+ T) (hq : IsLocalHomeomorph q)
    (f : ((Σ a, Fin (m a)) → ℂ) → V) (hf : DifferentiableAt ℂ f 0)
    (g : A → ℂ → V) (hg : ∀ a, AnalyticAt ℂ (g a) 0)
    (ℓ : V →L[ℂ] ℂ) (hz : fderiv ℂ (ℓ ∘ f) 0 = 0)
    (he : ∀ᶠ z in 𝓝 (0 : (Σ a, Fin (m a)) → ℂ),
      q (f (collisionBlockCoefficients m z)) = ∑ s : Σ a, Fin (m a), q (g s.1 (z s))) :
    ∀ a, (m a : ℕ∞) ≤ analyticOrderAt (deriv (ℓ ∘ g a)) 0 := by
  have hc : ContinuousAt (fun z => f (collisionBlockCoefficients m z)) 0 :=
    hf.continuousAt.comp_of_eq (collisionBlockCoefficients_continuous m).continuousAt
      (collisionBlockCoefficients_zero m)
  obtain ⟨c, htrace⟩ := local_abel_lift_scalar_trace q hq
    (fun z => f (collisionBlockCoefficients m z)) (fun s : Σ a, Fin (m a) => g s.1)
    hc (fun s => (hg s.1).continuousAt) he ℓ.toLinearMap
  have hscalar (a : A) : AnalyticAt ℂ (ℓ ∘ g a) 0 := (ℓ.analyticAt (g a 0)).comp (hg a)
  choose p hp using hscalar
  exact (collision_block_trace_jet_kernel m (ℓ ∘ f) (fun a => ℓ ∘ g a) p
    (ℓ.differentiableAt.comp 0 hf) hp c htrace).mp hz

#print axioms collision_quotient_lift_jet_orders
end HodgeLean.Foundations.Program.G32Native
