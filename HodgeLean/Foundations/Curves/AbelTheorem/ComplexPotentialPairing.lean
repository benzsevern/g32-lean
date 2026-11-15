import HodgeLean.Foundations.Curves.AbelTheorem.ComplexLinearWedge
import HodgeLean.Foundations.Curves.AbelTheorem.FormsLocalization

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

/-- Source: Farkas–Kra, Riemann Surfaces, III.6, integration against dual forms. -/
theorem complex_potential_dual_pairing (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    {ι : Type} [Fintype ι] (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ s, b3Forms_IsSmooth (η s))
    (hzero : ∀ s x, x ∈ D.support → η s =ᶠ[𝓝 x] 0)
    (c : ι → ℂ) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (G : C → ℂ)
    (hre : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).re)) =
      b4c_residue_realForm h θ Complex.reCLM + ∑ s, (c s).re • η s)
    (him : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).im)) =
      b4c_residue_realForm h θ Complex.imCLM + ∑ s, (c s).im • η s)
    (v : ι → ℂ)
    (hpair : ∀ (P : ℂ →L[ℝ] ℝ) s, b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) (η s)) = P (v s))
    (P : ℂ →L[ℝ] ℝ) :
    b3Forms_IsSmooth (complex_multiplier_wedge h G (b4c_residue_normalizedForm h w) P) ∧
    b3Forms_integral (b4c_residue_basis h)
      (complex_multiplier_wedge h G (b4c_residue_normalizedForm h w) P) = -P (∑ s, c s * v s) := by
  classical
  let ψ := b4c_residue_normalizedForm h w
  let β := b4c_residue_realForm h ψ P
  let Q := P.comp (ContinuousLinearMap.mul ℝ ℂ Complex.I)
  let βI := b4c_residue_realForm h ψ Q
  have hsm (R : ℂ →L[ℝ] ℝ) (s : ι) :
      b3Forms_IsSmooth (b3Forms_wedgeForm (η s) (b4c_residue_realForm h ψ R)) := by
    apply wedge_form_smooth_away_from_singular_set (D.support : Set C) _ _ (hη s) (hzero s)
    intro x hx
    exact projected_form_smooth_at_center h ψ (b4c_residue_normalizedForm_linear h w) R x
      ((b4c_residue_normalizedForm_analytic h w x (ha x hx).meromorphicOrderAt_nonneg).contDiffAt.restrict_scalars ℝ)
  have heq : complex_multiplier_wedge h G ψ P =
      ∑ s, (c s).re • b3Forms_wedgeForm (η s) β +
      ∑ s, (c s).im • b3Forms_wedgeForm (η s) βI := by
    have hz := complex_linear_wedge_zero h θ ψ hθ (b4c_residue_normalizedForm_linear h w) P
    funext x
    ext v
    have hzv := congrArg (fun A => A x v) hz
    simp only [Pi.add_apply, b3Forms_wedgeForm, ContinuousAlternatingMap.add_apply,
      Pi.zero_apply, b3Forms_wedge_apply] at hzv
    change _ = (0 : ℝ) at hzv
    simp only [complex_multiplier_wedge, hre, him, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, b3Forms_wedgeForm, b3Forms_wedge_apply,
      smul_eq_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, mul_sub, sub_mul]
    dsimp only [β, βI, Q]
    simp only [add_mul, mul_add, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← mul_assoc]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linear_combination hzv
  have hsre : ∀ s ∈ Finset.univ, b3Forms_IsSmooth ((c s).re • b3Forms_wedgeForm (η s) β) :=
    fun s _ => (hsm P s).smul _
  have hsim : ∀ s ∈ Finset.univ, b3Forms_IsSmooth ((c s).im • b3Forms_wedgeForm (η s) βI) :=
    fun s _ => (hsm Q s).smul _
  have hsumre := (b3Forms_Ω E C 2).sum_mem hsre
  have hsumim := (b3Forms_Ω E C 2).sum_mem hsim
  refine ⟨by rw [heq]; exact hsumre.add hsumim, ?_⟩
  rw [heq, b3Forms_integral_add _ hsumre hsumim,
    b3Forms_integral_finsetSum _ _ hsre, b3Forms_integral_finsetSum _ _ hsim]
  have hcomm (R : ℂ →L[ℝ] ℝ) s : b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (η s) (b4c_residue_realForm h ψ R)) = -R (v s) := by
    change b3Forms_pairing _ (η s) _ = _
    rw [b3Forms_pairing_comm]
    exact congrArg Neg.neg (hpair R s)
  simp only [b3Forms_integral_smul, β, βI, hcomm]
  rw [← Finset.sum_add_distrib, _root_.map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hc : c s * v s = (c s).re • v s + (c s).im • (Complex.I * v s) := by
    conv_lhs => rw [← Complex.re_add_im (c s)]
    simp only [Complex.real_smul]
    ring
  rw [hc, map_add, map_smul, map_smul]
  change (c s).re * (-P (v s)) + (c s).im * (-P (Complex.I * v s)) =
    -((c s).re * P (v s) + (c s).im * P (Complex.I * v s))
  ring

end HodgeLean.Foundations.Curves.AbelTheorem
