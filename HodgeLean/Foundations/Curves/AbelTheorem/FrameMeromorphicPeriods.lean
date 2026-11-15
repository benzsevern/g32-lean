import HodgeLean.Foundations.Curves.AbelTheorem.IntegralNullCyclePeriods
import HodgeLean.Foundations.Curves.AbelTheorem.ResidueDivisorDegree

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory Module
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem integral_meromorphic_loop_period_of_frame (h : finrank ℂ E = 1)
    (D : C →₀ ℤ) (F : PeriodFrame (E := E) D) (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (hpa : ∀ i, ∃ n : ℤ, loopIntegral (F.a i) w = (2 * Real.pi * Complex.I) * (n : ℂ))
    (hpb : ∀ i, ∃ n : ℤ, loopIntegral (F.b i) w = (2 * Real.pi * Complex.I) * (n : ℂ))
    (γ : b3_SmoothLoop E C) (hav : ∀ t, γ.val t ∉ D.support) :
    ∃ N : ℤ, loopIntegral γ w = (2 * Real.pi * Complex.I) * (N : ℂ) := by
  classical
  let ell := b3_latticePeriod E C γ
  let Γ : Option (Fin F.genus ⊕ Fin F.genus) → b3_SmoothLoop E C :=
    fun o => o.elim γ (Sum.elim F.a F.b)
  let n : Option (Fin F.genus ⊕ Fin F.genus) → ℤ :=
    fun o => o.elim 1 (fun s => -F.latticeBasis.repr ell s)
  have hbase (s : Fin F.genus ⊕ Fin F.genus) :
      b3_latticePeriod E C (Sum.elim F.a F.b s) = F.latticeBasis s := by
    cases s with
    | inl i => exact (F.a_basis i).symm
    | inr i => exact (F.b_basis i).symm
  have hcycle : ∑ o, n o • b3_latticePeriod E C (Γ o) = 0 := by
    simp only [Fintype.sum_option, Γ, n, Option.elim_none, Option.elim_some,
      one_smul, hbase, neg_smul, Finset.sum_neg_distrib, F.latticeBasis.sum_repr]
    exact add_neg_cancel ell
  have hΓ : ∀ o t, (Γ o).val t ∉ D.support := by
    intro o t
    cases o with
    | none => exact hav t
    | some s => cases s with
      | inl i => exact F.a_avoids i t
      | inr i => exact F.b_avoids i t
  obtain ⟨N, hN⟩ := integral_meromorphic_periods_of_null_cycle h D
    (residue_divisor_degree_zero h D w hr ha) w hr ha Γ hΓ n hcycle
  have hbm : ∀ s : Fin F.genus ⊕ Fin F.genus, ∃ m : ℤ,
      loopIntegral (Sum.elim F.a F.b s) w = (2 * Real.pi * Complex.I) * (m : ℂ) := by
    intro s
    cases s with
    | inl i => exact hpa i
    | inr i => exact hpb i
  choose m hm using hbm
  refine ⟨N + ∑ s, F.latticeBasis.repr ell s * m s, ?_⟩
  have hs : ∑ s, (-F.latticeBasis.repr ell s : ℂ) * loopIntegral (Sum.elim F.a F.b s) w =
      -(2 * Real.pi * Complex.I) * ∑ s, ((F.latticeBasis.repr ell s * m s : ℤ) : ℂ) := by
    simp only [hm, Int.cast_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp only [Fintype.sum_option, Γ, n, Option.elim_none, Option.elim_some,
    Int.cast_one, one_mul, Int.cast_neg] at hN
  rw [hs] at hN
  simp only [Int.cast_add, Int.cast_sum]
  linear_combination hN

end HodgeLean.Foundations.Curves.AbelTheorem
