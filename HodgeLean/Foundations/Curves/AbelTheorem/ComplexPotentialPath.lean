import HodgeLean.Foundations.Curves.AbelTheorem.FrameHolomorphicPotential

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

/-- Source: Farkas–Kra, Riemann Surfaces, III.2, integration of an exact differential. -/
theorem complex_potential_path_increment {ι : Type} [Fintype ι]
    (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ) (hη : ∀ s, b3Forms_IsSmooth (η s))
    (c : ι → ℂ) (θ : b3_HolForm E C) (G : C → ℂ)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G)
    (hre : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).re)) =
      b3Forms_reForm θ + ∑ s, (c s).re • η s)
    (him : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).im)) =
      b3Forms_imForm θ + ∑ s, (c s).im • η s)
    (p q : C) (γ : ℝ → C) (hγ : b3A_IsGoodPath (E := E) γ p q) :
    G q - G p = b3_pathIntegral E C γ θ.val +
      ∑ s, c s * (b3Forms_lineIntegral (η s) γ 0 1 : ℂ) := by
  classical
  have hr := b3Forms_lineIntegral_d (b3Forms_isSmooth_fun (Complex.reCLM.contMDiff.comp hG)) hγ.1 0 1
  have hi := b3Forms_lineIntegral_d (b3Forms_isSmooth_fun (Complex.imCLM.contMDiff.comp hG)) hγ.1 0 1
  change b3Forms_lineIntegral (b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).re))) γ 0 1 = _ at hr
  change b3Forms_lineIntegral (b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).im))) γ 0 1 = _ at hi
  rw [hre, b3Forms_lineIntegral_add (b3Forms_isSmooth_reForm θ)
    ((b3Forms_Ω E C 1).sum_mem fun s _ => (hη s).smul _) hγ.1,
    b3Rest2_lineIntegral_sum _ (fun s _ => (hη s).smul _) hγ.1,
    hγ.apply_zero, hγ.apply_one] at hr
  rw [him, b3Forms_lineIntegral_add (b3Forms_isSmooth_imForm θ)
    ((b3Forms_Ω E C 1).sum_mem fun s _ => (hη s).smul _) hγ.1,
    b3Rest2_lineIntegral_sum _ (fun s _ => (hη s).smul _) hγ.1,
    hγ.apply_zero, hγ.apply_one] at hi
  simp only [b3Forms_lineIntegral_smul] at hr hi
  rw [b3Forms_pathIntegral_eq θ hγ.1]
  apply Complex.ext
  · simpa using hr.symm
  · simpa using hi.symm

end HodgeLean.Foundations.Curves.AbelTheorem
