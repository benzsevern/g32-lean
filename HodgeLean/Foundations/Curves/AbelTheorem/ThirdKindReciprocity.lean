import HodgeLean.Foundations.Curves.AbelTheorem.PrincipalIntegration
import HodgeLean.Foundations.Curves.AbelTheorem.CurveBilinear
import HodgeLean.Foundations.Curves.AbelTheorem.TransverseFrameReciprocity
import HodgeLean.Foundations.Curves.AbelTheorem.DivisorPathDifference

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Module Manifold
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem third_kind_reciprocity_class (h : finrank ℂ E = 1) (p : C)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (F : PeriodFrame (E := E) D)
    (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (hn : ∀ i, loopIntegral (F.a i) w = 0)
    (paths : C → ℝ → C) (hp : ∀ x, b3A_IsGoodPath (E := E) (paths x) p x) :
    ∃ ell : b3_periodLattice E C, ∀ i,
      loopIntegral (F.b i) w = (2 * Real.pi * Complex.I) *
        (divisorIntegral (E := E) D paths (F.forms i) + ell.val (F.forms i)) := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  obtain ⟨q, other, hq, ell, he⟩ := exists_transverse_frame_reciprocity h D hdeg F w hr ho ha hn
  obtain ⟨m, hm⟩ := integral_lattice_of_divisor_path_difference h D hdeg p q paths other hp hq
  refine ⟨m + ell, fun i => ?_⟩
  rw [he]
  congr 1
  change divisorIntegral (E := E) D other (F.forms i) + ell.val (F.forms i) =
    divisorIntegral (E := E) D paths (F.forms i) + (m.val (F.forms i) + ell.val (F.forms i))
  rw [← hm (F.forms i)]
  ring

end HodgeLean.Foundations.Curves.AbelTheorem
