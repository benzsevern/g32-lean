import HodgeLean.Foundations.Program.SchoenSelectedGeometryIntegrationRange
import HodgeLean.Foundations.Program.CurveJacobianRest2Singular

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory HodgeLean.Adapters HodgeLean.Foundations
open AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Real-part integration classes of a real holomorphic-form basis are complex-linearly independent. -/
theorem s0_integration_basis_independent
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (hE : Module.finrank ℂ E = 1) (p₀ : C)
    (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj) (hajc : Continuous aj)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (b3_HolForm E C)) :
    LinearIndependent ℂ (fun j ↦ Singular.cohomologyClass (TopCat.of C) 1
      (b3Rest2_integCocycle aj hajc b3Rest2_gre (b j))) := by
  classical
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  let x := fun j ↦ Singular.cohomologyClass (TopCat.of C) 1
    (b3Rest2_integCocycle aj hajc b3Rest2_gre (b j))
  have hval : ∀ (j : ι) (γ : b3_SmoothLoop E C),
      AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ (TopCat.of C) 1 (x j)
        (((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of C)).sc 1).moduleCatHomologyClass
          (loopCycle ℂ (b3Rest2_circ γ))) = ((b3_period E C γ (b j)).re : ℂ) := by
    intro j γ
    rw [cohomologyEquivDualHomology_cohomologyClass]
    exact b3Rest2_integCocycle_loop aj hajc hE p₀ haj b3Rest2_gre (b j) γ (b3Rest2_circ γ)
      (b3Rest2_circ_apply γ)
  have hli : LinearIndependent ℂ x := by
    refine Fintype.linearIndependent_iff.2 fun c hc ↦ ?_
    have hγ : ∀ γ : b3_SmoothLoop E C,
        ∑ j, c j * ((b3_period E C γ (b j)).re : ℂ) = 0 := by
      intro γ
      let ev : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of C) 1 →ₗ[ℂ] ℂ :=
        (LinearMap.applyₗ (((AlgebraicTopology.Singular.SingularChainComplex ℂ
          (TopCat.of C)).sc 1).moduleCatHomologyClass (loopCycle ℂ (b3Rest2_circ γ)))).comp
          (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ (TopCat.of C) 1).toLinearMap
      have hev : ∀ j, ev (x j) = ((b3_period E C γ (b j)).re : ℂ) := fun j ↦ hval j γ
      have e := congrArg ev hc
      rw [map_sum, map_zero] at e
      simp only [map_smul, smul_eq_mul, hev] at e
      exact e
    have hre : ∀ r : ι → ℝ,
        (∀ γ : b3_SmoothLoop E C, ∑ j, r j * (b3_period E C γ (b j)).re = 0) → ∀ j, r j = 0 := by
      intro r hr
      have h0 : ∑ j, r j • b j = 0 := by
        refine b3Rest2_eq_of_re_period hE fun γ ↦ ?_
        rw [b3Rest2_period_sum]
        simp only [b3Rest2_period_rsmul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, hr γ]
        simp [b3_period, b3_pathPeriod, b3_pathIntegral]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent r h0
    intro j
    apply Complex.ext
    · refine hre (fun j ↦ (c j).re) (fun γ ↦ ?_) j
      have := congrArg Complex.re (hγ γ)
      simpa [Complex.re_sum, Complex.mul_re] using this
    · refine hre (fun j ↦ (c j).im) (fun γ ↦ ?_) j
      have := congrArg Complex.im (hγ γ)
      simpa [Complex.im_sum, Complex.mul_im] using this
  exact hli

#print axioms s0_integration_basis_independent
end HodgeLean.Foundations.Program
