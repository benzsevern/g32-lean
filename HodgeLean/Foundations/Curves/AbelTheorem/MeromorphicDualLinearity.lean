import HodgeLean.Foundations.Curves.AbelTheorem.FormsLocalization

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem meromorphic_dual_primitive_pairing (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    {ι : Type} [Fintype ι] (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ i, b3Forms_IsSmooth (η i))
    (hzero : ∀ i x, x ∈ D.support → η i =ᶠ[𝓝 x] 0)
    (n : ι → ℤ) (f : C → ℝ)
    (hdf : b3Forms_d (b3Forms_fun (E := E) f) = ∑ i, (n i : ℝ) • η i)
    (v : ι → ℂ) (P : ℂ →L[ℝ] ℝ)
    (hpair : ∀ i, b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) (η i)) =
        P (v i)) :
    b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) f))
        (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P)) =
      -P (∑ i, (n i : ℂ) * v i) := by
  classical
  let β := b4c_residue_realForm h (b4c_residue_normalizedForm h w) P
  have hβ : ∀ x ∉ (D.support : Set C),
      ContDiffAt ℝ ∞ (b3Forms_loc β x) (chartAt E x x) := by
    intro x hx
    exact projected_form_smooth_at_center h _ (b4c_residue_normalizedForm_linear h w) P x
      ((b4c_residue_normalizedForm_analytic h w x (ha x hx).meromorphicOrderAt_nonneg).contDiffAt.restrict_scalars ℝ)
  have hηβ (i : ι) : b3Forms_IsSmooth (b3Forms_wedgeForm (η i) β) :=
    wedge_form_smooth_away_from_singular_set (D.support : Set C) _ _ (hη i) (hzero i) hβ
  have hβη (i : ι) : b3Forms_IsSmooth (b3Forms_wedgeForm β (η i)) := by
    have he : b3Forms_wedgeForm β (η i) = (-1 : ℝ) • b3Forms_wedgeForm (η i) β := by
      funext x
      simp only [b3Forms_wedgeForm, b3Forms_wedge_comm (η i x), Pi.smul_apply, neg_one_smul]
    rw [he]
    exact (hηβ i).smul (-1)
  change b3Forms_pairing (b4c_residue_basis h) _ β = _
  rw [b3Forms_pairing_comm]
  change -b3Forms_integral (b4c_residue_basis h)
    (b3Forms_wedgeForm β (b3Forms_d (b3Forms_fun (E := E) f))) = _
  rw [hdf, b3Rest_wedgeForm_sum]
  have hs (i : ι) : b3Forms_IsSmooth (b3Forms_wedgeForm β ((n i : ℝ) • η i)) := by
    rw [b3Rest_wedgeForm_smul]
    exact (hβη i).smul _
  rw [b3Forms_integral_finsetSum _ _ (fun i _ => hs i)]
  simp only [b3Rest_wedgeForm_smul, b3Forms_integral_smul, β, hpair]
  congr 1
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← zsmul_eq_mul, map_zsmul]

end HodgeLean.Foundations.Curves.AbelTheorem
