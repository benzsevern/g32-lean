import HodgeLean.Foundations.Program.CurveJacobianRest2Singular
import HodgeLean.Foundations.Program.CurveJacobianAFunctor

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The holomorphic form representing real periods commutes with pullback of rational classes. -/
theorem s0_period_form_pullback
    {C Y : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (a : Cohomology ℚ (TopCat.of Y) 1) :
    b3Rest2_T (Module.finrank_self ℂ) (cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩) a) =
      b3A_pullHol f hf (b3Rest2_T (Module.finrank_self ℂ) a) := by
  apply b3Rest2_Pc_unique (Module.finrank_self ℂ) (b3Rest2_T_spec _ _)
  intro γ
  have hp := b3Rest2_T_spec (Module.finrank_self ℂ) a (b3A_mapLoop f hf γ)
  have hc : b3Rest2_circ (b3A_mapLoop f hf γ) =
      (⟨f, hf.continuous⟩ : ContinuousMap C Y).comp (b3Rest2_circ γ) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H x => rfl
  rw [hc, loopPeriod_comp] at hp
  rw [← b3A_precomp_period f hf γ (b3A_mapLoop f hf γ) rfl] at hp
  exact hp

#print axioms s0_period_form_pullback
end HodgeLean.Foundations.Program
