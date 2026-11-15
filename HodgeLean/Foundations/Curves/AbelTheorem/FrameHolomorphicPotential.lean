import HodgeLean.Foundations.Curves.AbelTheorem.FrameDualPrimitive
import HodgeLean.Foundations.Curves.AbelTheorem.HolomorphicPotentialDerivative
import HodgeLean.Foundations.Curves.AbelTheorem.LocalHolomorphicPotential
import HodgeLean.Foundations.Curves.AbelTheorem.SmoothScalarFromForm

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

/-- Source: Farkas–Kra, Riemann Surfaces, III.2, dual forms for a symplectic frame. -/
theorem exists_frame_holomorphic_potential (h : finrank ℂ E = 1) {D : C →₀ ℤ}
    (F : PeriodFrame (E := E) D)
    (η : Fin F.genus ⊕ Fin F.genus → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ s, b3Forms_IsSmooth (η s))
    (hdual : ∀ s, ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ,
      b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α (η s)) =
          b3Forms_lineIntegral α (Sum.elim F.a F.b s).val 0 1)
    (hzero : ∀ s x, x ∈ D.support → η s =ᶠ[𝓝 x] 0)
    (θ : b3_HolForm E C) :
    ∃ G : C → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G ∧
      (b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).re)) = b3Forms_reForm θ +
        ∑ s, Sum.elim (fun i => -b3Forms_lineIntegral (b3Forms_reForm θ) (F.b i).val 0 1)
          (fun i => b3Forms_lineIntegral (b3Forms_reForm θ) (F.a i).val 0 1) s • η s) ∧
      (b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).im)) = b3Forms_imForm θ +
        ∑ s, Sum.elim (fun i => -b3Forms_lineIntegral (b3Forms_imForm θ) (F.b i).val 0 1)
          (fun i => b3Forms_lineIntegral (b3Forms_imForm θ) (F.a i).val 0 1) s • η s) ∧
      ∀ x ∈ D.support, ∀ᶠ y in 𝓝 x, AnalyticAt ℂ (centeredScalar h G y) 0 := by
  classical
  obtain ⟨f, hf, hdf⟩ := primitive_of_frame_dual_remainder h F η hη hdual
    (b3Forms_reForm θ) (b3Forms_isSmooth_reForm θ) (b3Forms_d_reForm h θ)
  have hims : b3Forms_IsSmooth (b3Forms_imForm θ) := by
    rw [b3Forms_imForm_eq]
    exact b3Forms_isSmooth_reForm _
  have himd : b3Forms_d (b3Forms_imForm θ) = 0 := by
    rw [b3Forms_imForm_eq]
    exact b3Forms_d_reForm h _
  obtain ⟨g, hg, hdg⟩ := primitive_of_frame_dual_remainder h F η hη hdual
    (b3Forms_imForm θ) hims himd
  let G : C → ℂ := fun x => (f x : ℂ) + Complex.I * (g x : ℂ)
  have hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G :=
    (Complex.ofRealCLM.contMDiff.comp (smooth_scalar_of_smooth_zero_form f hf)).add
      (contMDiff_const.mul (Complex.ofRealCLM.contMDiff.comp (smooth_scalar_of_smooth_zero_form g hg)))
  have hre : (fun x => (G x).re) = f := by funext x; simp [G]
  have him : (fun x => (G x).im) = g := by funext x; simp [G]
  refine ⟨G, hG, by rw [hre]; exact hdf, by rw [him]; exact hdg, ?_⟩
  intro x hx
  apply eventually_centered_scalar_analytic_of_centered_differentiable h G x
  have he : ∀ᶠ y in 𝓝 x, ∀ s, η s y = 0 := by
    rw [Filter.eventually_all]
    intro s
    exact hzero s x hx
  filter_upwards [he] with y hy
  apply (centered_scalar_hasDerivAt_of_projected_differentials h G hG θ.val θ.property.2 y ?_ ?_).differentiableAt
  · rw [hre, hdf]
    have heq : b3Forms_reForm θ y = b4c_residue_realForm h θ.val Complex.reCLM y := by
      ext v
      have hv : v = fun _ => v 0 := funext fun i => by fin_cases i; rfl
      rw [hv, b3Forms_reForm_apply, b4c_residue_realForm_apply h θ.val θ.property.2]
      rfl
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, hy, smul_zero,
      Finset.sum_const_zero, add_zero] using heq
  · rw [him, hdg]
    have heq : b3Forms_imForm θ y = b4c_residue_realForm h θ.val Complex.imCLM y := by
      ext v
      have hv : v = fun _ => v 0 := funext fun i => by fin_cases i; rfl
      rw [hv, b3Forms_imForm_apply, b4c_residue_realForm_apply h θ.val θ.property.2]
      rfl
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, hy, smul_zero,
      Finset.sum_const_zero, add_zero] using heq

end HodgeLean.Foundations.Curves.AbelTheorem
