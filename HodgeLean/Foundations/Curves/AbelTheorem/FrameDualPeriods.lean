import HodgeLean.Foundations.Curves.AbelTheorem.DualIntersectionPeriods

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory Module
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem frame_dual_periods (h : finrank ℂ E = 1) {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (η : Fin F.genus ⊕ Fin F.genus → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ s, b3Forms_IsSmooth (η s))
    (hdual : ∀ s, ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ,
      b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α (η s)) =
          b3Forms_lineIntegral α (Sum.elim F.a F.b s).val 0 1) :
    (∀ i j, b3Forms_lineIntegral (η (.inl i)) (F.a j).val 0 1 = 0) ∧
    (∀ i j, b3Forms_lineIntegral (η (.inl i)) (F.b j).val 0 1 = if i = j then 1 else 0) ∧
    (∀ i j, b3Forms_lineIntegral (η (.inr i)) (F.a j).val 0 1 = -(if i = j then 1 else 0)) ∧
    (∀ i j, b3Forms_lineIntegral (η (.inr i)) (F.b j).val 0 1 = 0) := by
  have hb (s : Fin F.genus ⊕ Fin F.genus) :
      b3_latticePeriod E C (Sum.elim F.a F.b s) = F.latticeBasis s := by
    cases s with
    | inl i => exact (F.a_basis i).symm
    | inr i => exact (F.b_basis i).symm
  have hc (s t : Fin F.genus ⊕ Fin F.genus) :
      b3Forms_lineIntegral (η s) (Sum.elim F.a F.b t).val 0 1 =
        (F.intersection (F.latticeBasis s) (F.latticeBasis t) : ℝ) := by
    have he := dual_form_period_is_intersection h F.intersection F.intersection_spec
      (Sum.elim F.a F.b s) (Sum.elim F.a F.b t) (η s) (hη s) (hdual s)
    simpa only [hb] using he
  have hR := b3_intersectionForm_isRiemannForm h F.intersection F.intersection_spec
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [Sum.elim_inl, F.aa, Int.cast_zero] using hc (.inl i) (.inl j)
  · intro i j
    simpa only [Sum.elim_inr, F.ab, Int.cast_ite, Int.cast_one, Int.cast_zero] using hc (.inl i) (.inr j)
  · intro i j
    have he := hc (.inr i) (.inl j)
    rw [integral_alternating_skew F.intersection hR.alt, F.ab] at he
    simpa only [Sum.elim_inl, Int.cast_neg, Int.cast_ite, Int.cast_one, Int.cast_zero,
      eq_comm] using he
  · intro i j
    simpa only [Sum.elim_inr, F.bb, Int.cast_zero] using hc (.inr i) (.inr j)

end HodgeLean.Foundations.Curves.AbelTheorem
