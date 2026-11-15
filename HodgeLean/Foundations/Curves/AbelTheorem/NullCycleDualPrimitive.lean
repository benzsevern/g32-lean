import HodgeLean.Foundations.Curves.AbelTheorem.DualIntersectionPeriods

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem primitive_of_integral_null_cycle_duals (h : Module.finrank ℂ E = 1)
    {ι : Type} [Fintype ι] (γ : ι → b3_SmoothLoop E C)
    (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ) (hη : ∀ i, b3Forms_IsSmooth (η i))
    (hdual : ∀ i, ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ,
      b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α (η i)) =
          b3Forms_lineIntegral α (γ i).val 0 1)
    (n : ι → ℤ) (hcycle : ∑ i, n i • b3_latticePeriod E C (γ i) = 0) :
    ∃ f : C → ℝ, b3Forms_IsSmooth (b3Forms_fun (E := E) f) ∧
      b3Forms_d (b3Forms_fun (E := E) f) = ∑ i, (n i : ℝ) • η i := by
  classical
  let ζ (i : ι) : b3Forms_closed E C 0 :=
    ⟨⟨η i, hη i⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact b3Rest2_d_eq_zero_of_dual h (γ i).property.2 (γ i).property.1 (hη i) (hdual i)⟩
  let α : b3Forms_closed E C 0 := ∑ i, (n i : ℝ) • ζ i
  have heq : α.val.val = ∑ i, (n i : ℝ) • η i := by
    simp only [α, Submodule.coe_sum, Submodule.coe_smul_of_tower, ζ]
  have hs : b3Forms_IsSmooth (∑ i, (n i : ℝ) • η i) := heq ▸ α.val.property
  have hd : b3Forms_d (∑ i, (n i : ℝ) • η i) = 0 := heq ▸ b3Forms_closed_d_eq_zero α
  apply b3Forms_exists_primitive hs hd
  intro δ hper hδ
  let δl : b3_SmoothLoop E C := ⟨δ, hper, hδ⟩
  let Q := b3Rest2_QZ (C := C) h (b3Rest2_key h)
  have hQ : b3_IsIntersectionForm E Q := b3Rest2_isIntersectionForm h (b3Rest2_key h)
  have he := congrArg (Q.flip (b3_latticePeriod E C δl)) hcycle
  simp only [_root_.map_sum, map_smul, _root_.map_zero, smul_eq_mul, RingHom.id_apply] at he
  have hr : ∑ i, (n i : ℝ) *
      (Q (b3_latticePeriod E C (γ i)) (b3_latticePeriod E C δl) : ℝ) = 0 := by
    exact_mod_cast he
  rw [b3Rest2_lineIntegral_sum _ (fun i _ => (hη i).smul _) hδ]
  simp only [b3Forms_lineIntegral_smul]
  convert hr using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact dual_form_period_is_intersection h Q hQ (γ i) δl (η i) (hη i) (hdual i)

end HodgeLean.Foundations.Curves.AbelTheorem
