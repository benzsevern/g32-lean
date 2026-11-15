import HodgeLean.Foundations.Curves.AbelTheorem.ClosedFormPeriods

noncomputable section
open HodgeLean.Foundations.Program
open Module Manifold
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem closed_form_period_coordinates (h : finrank ℂ E = 1)
    {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α) (hd : b3Forms_d α = 0)
    (γ : b3_SmoothLoop E C) :
    b3Forms_lineIntegral α γ.val 0 1 =
      ∑ s, (F.latticeBasis.repr (b3_latticePeriod E C γ) s : ℝ) *
        b3Forms_lineIntegral α (Sum.elim F.a F.b s).val 0 1 := by
  classical
  letI : IsManifold 𝓘(ℝ, E) ∞ C := b3Forms_isManifold_real
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : Fact (finrank ℂ E = 1) := ⟨h⟩
  obtain ⟨θ, f, hf, he⟩ := b3Rest_hodge hα hd
  have heval (ξ : b3_SmoothLoop E C) :
      b3Forms_lineIntegral α ξ.val 0 1 = (b3_period E C ξ θ).re := by
    have hend : ξ.val 1 = ξ.val 0 := by simpa only [zero_add] using ξ.property.1 0
    rw [he, b3Forms_lineIntegral_add (b3Forms_isSmooth_reForm θ) hf.d ξ.property.2,
      b3Forms_lineIntegral_d hf ξ.property.2, hend, sub_self, add_zero,
      ← b3Rest2_re_period]
  let ev : b3_periodLattice E C →ₗ[ℤ] ℝ :=
    Complex.reCLM.toLinearMap.restrictScalars ℤ |>.comp
      ((LinearMap.proj θ).comp (b3_periodLattice E C).subtype.toIntLinearMap)
  have heq := congrArg ev (F.latticeBasis.sum_repr (b3_latticePeriod E C γ))
  simp only [map_sum, map_smul, zsmul_eq_mul] at heq
  rw [heval]
  calc
    (b3_period E C γ θ).re = ∑ s,
        (F.latticeBasis.repr (b3_latticePeriod E C γ) s : ℝ) * ev (F.latticeBasis s) := heq.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      cases s with
      | inl i => rw [F.a_basis, heval]; rfl
      | inr i => rw [F.b_basis, heval]; rfl

theorem closed_form_primitive_of_frame_periods_zero (h : finrank ℂ E = 1)
    {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α) (hd : b3Forms_d α = 0)
    (ha : ∀ i, b3Forms_lineIntegral α (F.a i).val 0 1 = 0)
    (hb : ∀ i, b3Forms_lineIntegral α (F.b i).val 0 1 = 0) :
    ∃ f : C → ℝ, b3Forms_IsSmooth (b3Forms_fun (E := E) f) ∧
      b3Forms_d (b3Forms_fun (E := E) f) = α := by
  letI : IsManifold 𝓘(ℝ, E) ∞ C := b3Forms_isManifold_real
  apply b3Forms_exists_primitive hα hd
  intro γ hper hγ
  rw [closed_form_period_coordinates h F α hα hd ⟨γ, hper, hγ⟩]
  apply Finset.sum_eq_zero
  intro s _
  cases s with
  | inl i => simp only [Sum.elim_inl, ha i, mul_zero]
  | inr i => simp only [Sum.elim_inr, hb i, mul_zero]

end HodgeLean.Foundations.Curves.AbelTheorem
