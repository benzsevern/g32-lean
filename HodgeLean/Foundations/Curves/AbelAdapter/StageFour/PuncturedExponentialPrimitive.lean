import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.RegularDifferentialPullback
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.ExponentialPathIntegral
import HodgeLean.Foundations.Program.HurwitzPrymCovConnected

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology Set
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §13, the complement of a divisor support. -/
def divisorComplement {C : Type} [TopologicalSpace C] [T2Space C] (D : C →₀ ℤ) :
    TopologicalSpace.Opens C :=
  ⟨(D.support : Set C)ᶜ, D.support.finite_toSet.isClosed.isOpen_compl⟩

/-- Source: Forster, Lectures on Riemann Surfaces, §§9, 14, restriction of differentials away from poles. -/
def divisorDifferentialRestriction
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]
    (h : Module.finrank ℂ E = 1) (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0) :
    b3_HolForm E (divisorComplement D) :=
  ⟨b3_pullback E E (fun x : divisorComplement D => (x : C)) w,
    differential_pullback_holomorphic_on_regular_image h h _ contMDiff_subtype_val w
      w.property.1 (fun x => ha x.val x.property)⟩

/-- Source: Forster, Lectures on Riemann Surfaces, §10, exponentiation on a punctured curve. -/
theorem exponentialPrimitive_on_divisorComplement
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (p : divisorComplement D)
    (hperiod : ∀ γ : b3_SmoothLoop E (divisorComplement D),
      Complex.exp (b3_period E (divisorComplement D) γ
        (divisorDifferentialRestriction h D w ha)) = 1) :
    ∃ F : divisorComplement D → ℂ, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω F ∧
      (∀ q, F q ≠ 0) ∧
      ∀ (q : divisorComplement D) (γ : ℝ → divisorComplement D),
        b3A_IsGoodPath (E := E) γ p q →
          F q = Complex.exp (b3_pathIntegral E (divisorComplement D) γ
            (divisorDifferentialRestriction h D w ha)) := by
  have hc : IsPreconnected ((Set.univ : Set C) \ (D.support : Set C)) :=
    b4cov_isPreconnected_diff_finite isOpen_univ isPreconnected_univ
      D.support.finite_toSet (fun x _ => b4cov_goodPoint h x)
  have hU : ((Set.univ : Set C) \ (D.support : Set C)) = (divisorComplement D : Set C) := by
    ext x
    simp [divisorComplement]
  rw [hU] at hc
  letI : ConnectedSpace (divisorComplement D) :=
    isConnected_iff_connectedSpace.mp ⟨⟨p.val, p.property⟩, hc⟩
  exact exponentialPrimitive_of_integralPeriods h p (divisorDifferentialRestriction h D w ha) hperiod

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
