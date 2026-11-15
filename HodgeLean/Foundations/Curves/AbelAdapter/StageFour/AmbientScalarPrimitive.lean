import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.PuncturedPrimitiveDerivative

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology Set
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §10, scalar representatives of punctured exponential primitives. -/
theorem ambientScalarPrimitive_of_integralPeriods
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (p : divisorComplement D)
    (hperiod : ∀ γ : b3_SmoothLoop E (divisorComplement D),
      Complex.exp (b3_period E (divisorComplement D) γ
        (divisorDifferentialRestriction h D w ha)) = 1) :
    ∃ f : C → ℂ, ContinuousOn f (divisorComplement D : Set C) ∧
      (∀ x, x ∉ D.support → f x ≠ 0) ∧
      ∀ x : divisorComplement D,
        HasDerivAt (fun z : ℂ => f ((extChartAt 𝓘(ℂ, E) (x : C)).symm
          (extChartAt 𝓘(ℂ, E) (x : C) (x : C) + b4cov_lineEquiv h z)))
          (HurwitzPrymRR_loc h w (x : C) 0 * f x.val) 0 := by
  classical
  have hc : IsPreconnected ((Set.univ : Set C) \ (D.support : Set C)) :=
    b4cov_isPreconnected_diff_finite isOpen_univ isPreconnected_univ
      D.support.finite_toSet (fun x _ => b4cov_goodPoint h x)
  have hU : ((Set.univ : Set C) \ (D.support : Set C)) = (divisorComplement D : Set C) := by
    ext x
    simp [divisorComplement]
  rw [hU] at hc
  letI : ConnectedSpace (divisorComplement D) :=
    isConnected_iff_connectedSpace.mp ⟨⟨p.val, p.property⟩, hc⟩
  obtain ⟨F, hF, hFn, hFp⟩ := exponentialPrimitive_on_divisorComplement h D w ha p hperiod
  let f : C → ℂ := fun x => if hx : x ∈ (divisorComplement D : Set C) then F ⟨x, hx⟩ else 0
  have hf (x : divisorComplement D) : f x.val = F x := by
    dsimp only [f]
    split_ifs with hx
    · rfl
    · exact (hx x.property).elim
  refine ⟨f, ?_, ?_, puncturedPrimitive_ambient_derivative h D w ha p F hFp f hf⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun x : divisorComplement D => f x.val) = F := funext hf
    change Continuous (fun x : divisorComplement D => f x.val)
    rw [he]
    exact hF.continuous
  · intro x hx
    have hxu : x ∈ (divisorComplement D : Set C) := hx
    rw [show f x = F ⟨x, hxu⟩ from hf ⟨x, hxu⟩]
    exact hFn _

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
