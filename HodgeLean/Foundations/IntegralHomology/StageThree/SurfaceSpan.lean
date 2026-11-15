import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralLiftPairing

/-! Real-part integration classes span complex singular degree-one cohomology. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Manifold
open HodgeLean.Adapters
open scoped ContDiff
namespace HodgeLean.Foundations.IntegralHomology.StageThree
open HodgeLean.Foundations.Program
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable (C : Type) [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

def surfaceRealClass (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (θ : b3_HolForm E C) : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of C) (1 : ℕ) :=
  Singular.cohomologyClass (TopCat.of C) (1 : ℕ)
    (b3Rest2_integCocycle aj haj b3Rest2_gre θ)

variable (hE : Module.finrank ℂ E = (1 : ℕ))
include hE

theorem surfaceRealClass_loop
    (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (p₀ : C) (h : b3_IsAbelJacobi E C p₀ aj)
    (θ : b3_HolForm E C) (γ : b3_SmoothLoop E C) :
    AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ (TopCat.of C) (1 : ℕ)
      (surfaceRealClass C aj haj θ)
      (((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of C)).sc (1 : ℕ)).moduleCatHomologyClass
        (loopCycle ℂ (b3Rest2_circ γ))) = ((b3_period E C γ θ).re : ℂ) := by
  rw [surfaceRealClass, cohomologyEquivDualHomology_cohomologyClass]
  exact b3Rest2_integCocycle_loop aj haj hE p₀ h b3Rest2_gre θ γ
    (b3Rest2_circ γ) (b3Rest2_circ_apply γ)

theorem surfaceRealClass_linearIndependent
    (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (p₀ : C) (h : b3_IsAbelJacobi E C p₀ aj)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (b3_HolForm E C)) :
    LinearIndependent ℂ (fun j => surfaceRealClass C aj haj (b j)) := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have hγ (γ : b3_SmoothLoop E C) : ∑ j, c j * ((b3_period E C γ (b j)).re : ℂ) = (0 : ℂ) := by
    let ev : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of C) (1 : ℕ) →ₗ[ℂ] ℂ :=
      (LinearMap.applyₗ (((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of C)).sc (1 : ℕ)).moduleCatHomologyClass (loopCycle ℂ (b3Rest2_circ γ)))).comp
        (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ (TopCat.of C) (1 : ℕ)).toLinearMap
    have he (j) : ev (surfaceRealClass C aj haj (b j)) =
        ((b3_period E C γ (b j)).re : ℂ) := surfaceRealClass_loop C hE aj haj p₀ h _ γ
    have e := congrArg ev hc
    rw [map_sum, map_zero] at e
    simpa only [map_smul, smul_eq_mul, he] using e
  have hre (r : ι → ℝ)
      (hr : ∀ γ : b3_SmoothLoop E C, ∑ j, r j * (b3_period E C γ (b j)).re = (0 : ℝ)) : ∀ j, r j = (0 : ℝ) := by
    have h0 : ∑ j, r j • b j = (0 : b3_HolForm E C) := by
      refine b3Rest2_eq_of_re_period hE fun γ => ?_
      rw [b3Rest2_period_sum]
      simp only [b3Rest2_period_rsmul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hr γ]
      simp [b3_period, b3_pathPeriod, b3_pathIntegral]
    exact Fintype.linearIndependent_iff.1 b.linearIndependent r h0
  intro j
  apply Complex.ext
  · apply hre (fun j => (c j).re) (fun γ => ?_) j
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.zero_re] using congrArg Complex.re (hγ γ)
  · apply hre (fun j => (c j).im) (fun γ => ?_) j
    simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, Complex.zero_im] using congrArg Complex.im (hγ γ)

theorem surfaceRealClass_span
    (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (p₀ : C) (h : b3_IsAbelJacobi E C p₀ aj)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (b3_HolForm E C)) :
    Submodule.span ℂ (Set.range (fun j => surfaceRealClass C aj haj (b j))) = ⊤ := by
  letI := (b3Rest2_finrank_cohomology_le (C := C) hE).1
  obtain ⟨hfin, hrk⟩ := spec_finrank_complexSingular_of_finite_aux (TopCat.of C) (1 : ℕ) inferInstance
  letI := hfin
  letI := b3_holForm_finiteDimensional (E := E) (C := C) hE
  apply (surfaceRealClass_linearIndependent C hE aj haj p₀ h b).span_eq_top_of_card_eq_finrank'
  rw [hrk, b3Rest2_finrank_cohomology (E := E) (C := C) hE,
    ← finrank_real_of_complex]
  exact (Module.finrank_eq_card_basis b).symm

end HodgeLean.Foundations.IntegralHomology.StageThree
