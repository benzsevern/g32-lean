import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem primitive_on_convex_domain (α : E → E [⋀^Fin 1]→L[ℝ] ℝ)
    {U : Set E} (hUc : Convex ℝ U) (hUo : IsOpen U)
    (hs : ContDiffOn ℝ ∞ α U) (hd : ∀ w ∈ U, extDeriv α w = 0) :
    ∃ f : E → ℝ, ∀ w ∈ U, HasFDerivAt f (b3Forms_toCLM (α w)) w := by
  let θ : E → E →L[ℝ] ℝ := fun w => b3Forms_toCLM (α w)
  have hdiff (w : E) (hw : w ∈ U) : DifferentiableAt ℝ α w :=
    (hs.contDiffAt (hUo.mem_nhds hw)).differentiableAt (by simp)
  have hθd (w : E) (hw : w ∈ U) : DifferentiableAt ℝ θ w :=
    (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv
      |>.differentiableAt.comp w (hdiff w hw)
  refine hUc.exists_forall_hasFDerivAt_of_fderiv_symmetric hUo
    (fun w hw => (hθd w hw).differentiableWithinAt) fun w hw a b => ?_
  have h1 := congrArg (fun A : E [⋀^Fin 2]→L[ℝ] ℝ => A ![a, b]) (hd w hw)
  simp only [extDeriv_apply (hdiff w hw), ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    at h1
  rw [Fin.sum_univ_two] at h1
  have e0 : Fin.removeNth 0 ![a, b] = fun _ => b := by funext i; fin_cases i; rfl
  have e1 : Fin.removeNth 1 ![a, b] = fun _ => a := by funext i; fin_cases i; rfl
  rw [e0, e1] at h1
  have hev (a' c : E) :
      fderiv ℝ θ w a' c = fderiv ℝ (fun w' => α w' (fun _ => c)) w a' := by
    rw [show (fun w' => α w' (fun _ => c)) = fun w' => θ w' c from rfl,
      fderiv_clm_apply (hθd w hw) (differentiableAt_const c)]
    simp
  rw [hev a b, hev b a]
  simp at h1
  linarith

end HodgeLean.Foundations.Curves.AbelTheorem
