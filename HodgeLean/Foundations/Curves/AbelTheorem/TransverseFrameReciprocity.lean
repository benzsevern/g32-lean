import HodgeLean.Foundations.Curves.AbelTheorem.FramePotentialReciprocity
import HodgeLean.Foundations.Curves.AbelTheorem.IntegralMeromorphicDual
import HodgeLean.Foundations.Curves.AbelTheorem.FiniteTransverseDivisorPaths
import HodgeLean.Foundations.Curves.AbelTheorem.ComplexIntegrationBasis

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

/-- Source: Farkas–Kra, Riemann Surfaces, III.6, divisor paths transverse to the period frame. -/
theorem exists_transverse_frame_reciprocity (h : finrank ℂ E = 1)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (F : PeriodFrame (E := E) D)
    (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (hn : ∀ i, loopIntegral (F.a i) w = 0) :
    ∃ (p : C) (paths : C → ℝ → C),
      (∀ x, b3A_IsGoodPath (E := E) (paths x) p x) ∧
      ∃ ell : b3_periodLattice E C, ∀ i,
        loopIntegral (F.b i) w = (2 * Real.pi * Complex.I) *
          (divisorIntegral (E := E) D paths (F.forms i) + ell.val (F.forms i)) := by
  classical
  let γ : Fin F.genus ⊕ Fin F.genus → b3_SmoothLoop E C := Sum.elim F.a F.b
  have hav : ∀ s t, (γ s).val t ∉ D.support := by
    intro s
    cases s with
    | inl i => exact F.a_avoids i
    | inr i => exact F.b_avoids i
  obtain ⟨p, paths, hp, hbound, hpoff, htr⟩ :=
    exists_divisor_paths_transverse_to_finite_loops h D γ hav
  have hex (s : Fin F.genus ⊕ Fin F.genus) := exists_integral_meromorphic_dual h D w ha (γ s) (hav s)
    (fun x : D.support => paths x.val) (fun x => (hp x.val).1) (fun x => hbound x.val)
    (fun x => htr s x.val x.property)
    (by
      intro x t
      rw [(hp x.val).apply_zero, (hp x.val).apply_one]
      exact ⟨hpoff s t, fun he => hav s t (he ▸ x.property)⟩)
  choose η hη hzero hint hdual hpair using hex
  refine ⟨p, paths, hp, frame_reciprocity_from_dual_data h D hdeg F w hr ho ha hn p paths hp
    η hη hzero hdual ?_ ?_⟩
  · intro P s
    rw [integral_eq_of_positive_basis_change (b3Rest_b h) (b4c_residue_basis h)
      (complex_integration_basis_change_positive h)]
    exact hpair s P
  · intro s x hx
    exact hint s ⟨x, hx⟩

end HodgeLean.Foundations.Curves.AbelTheorem
