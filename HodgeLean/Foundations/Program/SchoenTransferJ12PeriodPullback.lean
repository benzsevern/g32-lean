import HodgeLean.Foundations.Program.SchoenSelectedGeometryPeriodNaturality

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Period-form pullback for arbitrary complex line models of the two curves. -/
theorem s4_selected_period_pullback
    {E F C Y : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold 𝓘(ℂ, F) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (hE : Module.finrank ℂ E = 1) (hF : Module.finrank ℂ F = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (a : Cohomology ℚ (TopCat.of Y) 1) :
    b3Rest2_T hE (cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩) a) =
      b3A_pullHol f hf (b3Rest2_T hF a) := by
  apply b3Rest2_Pc_unique hE (b3Rest2_T_spec _ _)
  intro γ
  have hp := b3Rest2_T_spec hF a (b3A_mapLoop f hf γ)
  have hc : b3Rest2_circ (b3A_mapLoop f hf γ) =
      (⟨f, hf.continuous⟩ : ContinuousMap C Y).comp (b3Rest2_circ γ) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H x => rfl
  rw [hc, loopPeriod_comp] at hp
  rw [← b3A_precomp_period f hf γ (b3A_mapLoop f hf γ) rfl] at hp
  exact hp


#print axioms s4_selected_period_pullback

end HodgeLean.Foundations.Program
