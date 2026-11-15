import HodgeLean.Foundations.Program.G32Native.AbelDiscPrimitive

/-! # Local primitives of the original curve Abel map in every genus -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Manifold Filter Set
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

/-- The actual curve Abel map has an analytic local lift whose scalar derivatives
are the original normalized coefficient germs of every holomorphic form.
Source: Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_curve_local_abel_primitive
    (h : Module.finrank ℂ E = 1) (p q : C) :
    ∃ g : ℂ → b3Rest2_VJ E C,
      AnalyticAt ℂ g 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), b3Rest2_covHom (g z) =
        analyticAbel h p (b3A_disc q (b4cov_lineEquiv h 1) z)) ∧
      ∀ θ : b3_HolForm E C,
        deriv (fun z => periodLinear θ (g z)) =ᶠ[𝓝 0]
          HurwitzPrymRR_loc h θ q := by
  letI : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional h
  let b := Module.finBasis ℂ (b3_HolForm E C)
  let L := b4cov_lineEquiv h
  let u := L 1
  let κ := L.symm.toContinuousLinearMap
  have hu : u ≠ 0 := L.map_ne_zero_iff.mpr one_ne_zero
  obtain ⟨R, hR, hchart⟩ := b3A_chart_radius u hu q
  have hprim (i : Fin (Module.finrank ℂ (b3_HolForm E C))) :
      ∃ H : ℂ → ℂ, ∀ z ∈ Metric.ball (0 : ℂ) R,
        HasDerivAt H (b3A_discCoef (b i).val q u z) z :=
    DifferentiableOn.isExactOn_ball (fun z hz =>
      (b3A_discCoef_differentiableAt (b i).property q u
        (hchart z (mem_ball_zero_iff.mp hz))).differentiableWithinAt)
  choose H hH using hprim
  have hκ (v : E) : v = κ v • u := by
    change v = L.symm v • L 1
    rw [← map_smul, smul_eq_mul, mul_one, L.apply_symm_apply]
  have hκu : κ u = 1 := L.symm_apply_apply 1
  obtain ⟨g, hg, hcover, hderiv⟩ :=
    abel_disc_primitive_of_basis h p q b κ u hκ hκu R hR hchart H hH
  refine ⟨g, hg, hcover, ?_⟩
  intro θ
  have hd := hderiv (b.equivFun θ)
  rw [b.equivFun.symm_apply_apply] at hd
  exact hd.trans (discCoefficient_lineEquiv h θ.val q)

#print axioms residual_curve_local_abel_primitive
end HodgeLean.Foundations.Program.G32Native
