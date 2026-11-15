import HodgeLean.Foundations.Program.G32Native.AbelDiscCoefficientPairing

/-! # Disc primitives with literal evaluation of every original form -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Manifold Filter Set
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

/-- Basis primitives yield an analytic Abel lift with the same literal scalar derivatives. -/
theorem abel_disc_primitive_of_basis
    (h : Module.finrank ℂ E = 1) (p q : C)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (b3_HolForm E C))
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ v, v = κ v • u) (hκu : κ u = 1)
    (R : ℝ) (hR : 0 < R)
    (hchart : ∀ z : ℂ, ‖z‖ < R → chartAt E q q + z • u ∈ (chartAt E q).target)
    (H : ι → ℂ → ℂ) (hH : ∀ i, ∀ z ∈ Metric.ball (0 : ℂ) R,
      HasDerivAt (H i) (b3A_discCoef (b i).val q u z) z) :
    ∃ g : ℂ → b3Rest2_VJ E C,
      AnalyticAt ℂ g 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), b3Rest2_covHom (g z) = analyticAbel h p (b3A_disc q u z)) ∧
      ∀ a : ι → ℂ,
        deriv (fun z => periodLinear (b.equivFun.symm a) (g z)) =ᶠ[𝓝 0]
          b3A_discCoef (b.equivFun.symm a).val q u := by
  have hHa (i : ι) : AnalyticAt ℂ (H i) 0 :=
    (show DifferentiableOn ℂ (H i) (Metric.ball (0 : ℂ) R) from
      fun z hz => (hH i z hz).differentiableAt.differentiableWithinAt).analyticAt
        (Metric.ball_mem_nhds 0 hR)
  let V := fun z : ℂ => fun i => H i z - H i 0
  let Q := quotientBasisEquiv h b
  let M := (b2_coord (b3Rest2_QJ E C)).toLinearMap.comp
    Q.symm.toLinearMap
  obtain ⟨c, hc⟩ := (b3Rest2_covHom_spec (E := E) (C := C)).2 (analyticAbel h p q)
  let g := fun z => c + M (V z)
  have hg : AnalyticAt ℂ g 0 := analyticAt_const.add
    ((M.toContinuousLinearMap.analyticAt _).comp (AnalyticAt.pi fun i => (hHa i).sub analyticAt_const))
  have hQ : Q.symm.toLinearMap.comp (b3Rest_evalQ b) = LinearMap.id := by
    apply LinearMap.ext
    intro w
    change Q.symm (b3Rest_evalQ b w) = w
    rw [← quotientBasisEquiv_apply h b w]
    exact Q.symm_apply_apply w
  refine ⟨g, hg, ?_, ?_⟩
  · filter_upwards [Metric.ball_mem_nhds 0 hR] with z hz
    change b3Rest2_covHom (c + b2_coord _ (Q.symm (V z))) = _
    rw [map_add, hc, b3Rest2_covHom_coord]
    exact (b3Rest_abelJacobi_disc b Q.symm.toLinearMap hQ p (analyticAbel h p)
      (b3_exists_abelJacobi h p).choose_spec κ u hκ hκu q hchart H hH z
        (mem_ball_zero_iff.mp hz)).symm
  · intro a
    have heval (z : ℂ) : periodLinear (b.equivFun.symm a) (g z) =
        periodLinear (b.equivFun.symm a) c + ∑ i, a i * (H i z - H i 0) := by
      change periodLinear (b.equivFun.symm a) (c + b2_coord _ (Q.symm (V z))) = _
      rw [map_add, periodLinear_basis_pairing h b a (V z)]
    have hd (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) :
        HasDerivAt (fun z => periodLinear (b.equivFun.symm a) (g z))
          (b3A_discCoef (b.equivFun.symm a).val q u z) z := by
      have hs := HasDerivAt.fun_sum (u := Finset.univ)
        (fun i _ => ((hH i z hz).sub_const (H i 0)).const_mul (a i))
      have ht := hs.const_add (periodLinear (b.equivFun.symm a) c)
      have ht' := ht.congr_of_eventuallyEq (Filter.Eventually.of_forall heval)
      exact ht'.congr_deriv (discCoefficient_basis_pairing b a q u z).symm
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
    exact (hd z hz).deriv

#print axioms abel_disc_primitive_of_basis
end HodgeLean.Foundations.Program.G32Native
