import HodgeLean.Foundations.Curves.AbelTheorem.LocalPrimitiveDual
import HodgeLean.Foundations.Curves.AbelTheorem.AvoidingChartCover

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem exists_dual_vanishing_near_closed_set (h : Module.finrank ℂ E = 1)
    {P : ℝ → C} (K : b3Rest_Cover E P)
    (hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P) (hper : Function.Periodic P 1)
    (S : Set C) (hS : IsClosed S) (hav : ∀ t, P t ∉ S)
    (hK : ∀ k, (chartAt E (K.x k)).symm ''
      ball (chartAt E (K.x k) (K.x k)) (K.r k) ⊆ Sᶜ) :
    ∃ η : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth η ∧
      (∀ x ∈ S, η =ᶠ[𝓝 x] 0) ∧
      (∀ y, (∀ k : ℤ, y ∉ (chartAt E (K.x k)).symm ''
        ball (chartAt E (K.x k) (K.x k)) (K.r k)) → η y = 0) ∧
      ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α →
        ∀ f : ℤ → E → ℝ, (∀ k, ∀ u ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k),
          HasFDerivAt (f k) (b3Forms_toCLM (b3Forms_loc α (K.x k) u)) u) →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α η) =
          b3Forms_lineIntegral α P 0 1 := by
  obtain ⟨ε₀, hε₀, he⟩ := exists_arc_dual_of_local_primitives h K hP hper hS
    (fun k => hav (k / K.N))
  obtain ⟨κ, hσ, hσt, hκ, hκsupport, hκt, hη, hpair⟩ :=
    he (ε₀ / 2) (half_pos hε₀) (half_lt_self hε₀)
  refine ⟨_, hη, ?_, ?_, hpair⟩
  · intro x hx
    have ha : ∀ᶠ y in 𝓝 x, ∀ i : Fin K.N,
        b3Rest2_arcPiece h K (ε₀ / 2) i y = 0 := by
      rw [Filter.eventually_all]
      intro i
      have hn : x ∉ tsupport (b3Rest2_arcPiece h K (ε₀ / 2) i) :=
        fun hi => hK i (hσt i hi) hx
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      exact hy
    have hb : ∀ᶠ y in 𝓝 x, ∀ i : Fin K.N, κ i y = 0 := by
      rw [Filter.eventually_all]
      intro i
      have hn : x ∉ tsupport (κ i) := fun hi => hκt i x hi hx
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      exact hy
    filter_upwards [ha, hb] with y hy hz
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.add_apply, hy, hz, add_zero,
      Finset.sum_const_zero, smul_zero, Pi.zero_apply]
  · intro y hy
    have ha (i : Fin K.N) : b3Rest2_arcPiece h K (ε₀ / 2) i y = 0 :=
      image_eq_zero_of_notMem_tsupport fun hi => hy i (hσt i hi)
    have hb (i : Fin K.N) : κ i y = 0 :=
      image_eq_zero_of_notMem_tsupport fun hi => hy i (hκsupport i hi)
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.add_apply, ha, hb, add_zero,
      Finset.sum_const_zero, smul_zero]

end HodgeLean.Foundations.Curves.AbelTheorem
