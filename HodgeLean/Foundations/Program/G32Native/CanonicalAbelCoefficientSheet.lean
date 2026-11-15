import HodgeLean.Foundations.Program.SchoenFiniteMorphisms
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelGeometry
import HodgeLean.Foundations.Program.G32Native.AbelSheetCoefficientInverse
import HodgeLean.Foundations.Program.SchoenCycleEtaleMapAnalyticChart
import HodgeLean.Foundations.Program.SchoenCycleS1j1

/-! # The original etale sheet over a mixed divisor coefficient chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open HodgeLean.Adapters Filter Manifold
open scoped Topology BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Reindexing the ambient dimension leaves analyticity in the original native chart unchanged. -/
theorem native_chart_analytic_dim_change (X : Over (Spec ↧ℂ)) (n d : ℕ) (hd : n = d)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension d X.hom]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (x : ComplexPoint X) (s : V → ComplexPoint X) (a : V)
    (ha : AnalyticAt ℂ (fun c => localChart X n x (s c)) a) :
    AnalyticAt ℂ (fun c => localChart X d x (s c)) a := by
  subst d
  exact ha

/-- The retained mixed coefficient chart lifts analytically to the specified original sheet. -/
theorem canonical_abel_coefficient_sheet (G : CanonicalAbelGeometry)
    (w : ComplexPoint G.W) (z : ComplexPoint (g3_power G.Z (2 * G.k)))
    (hz : Point.map G.γ z = Point.map G.β w)
    (b : ℕ) (m : Fin b → ℕ) (hm : ∀ a, 0 < m a)
    (ι : (Σ a, Fin (m a)) ≃ Fin (2 * G.k))
    (p : Fin b → ComplexPoint G.Z) (hp : Function.Injective p)
    (hzip : ∀ a i, Point.map (g3_proj G.Z (2 * G.k) (ι ⟨a, i⟩)) z = p a) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint G.B) (Fin (2 * G.k) → ℂ),
      Point.map G.β w ∈ e.source ∧ e (Point.map G.β w) = 0 ∧
      ∃ s : (Fin (2 * G.k) → ℂ) → ComplexPoint G.W,
        s 0 = w ∧ ContinuousAt s 0 ∧
        AnalyticAt ℂ (fun c => localChart G.W (G.k + G.k) w (s c)) 0 ∧
        (∀ᶠ c in 𝓝 (0 : Fin (2 * G.k) → ℂ), Point.map G.β (s c) = e.symm c) ∧
        (∀ᶠ q in 𝓝 z, ∀ a (j : Fin (m a)),
          e (Point.map G.γ q) (ι ⟨a, j⟩) = (-1 : ℂ) ^ (m a - j.val) *
            aeval (fun i : Fin (m a) =>
              (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
                (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
                  (Point.map (g3_proj G.Z (2 * G.k) (ι ⟨a, i⟩)) q) -
                 extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)))
              (esymm (Fin (m a)) ℂ (m a - j.val))) := by
  letI : Surjective G.γ.left := ⟨s2_surjective_of_point_surjective G.γ G.surjectiveγ⟩
  letI : SmoothOfRelativeDimension (2 * G.k) G.B.hom := by
    simpa only [two_mul] using G.smoothB
  obtain ⟨e, he, he0, _, hei, hcoef⟩ := s2e_mixed_coefficient_neighbourhood
    G.Z G.B (2 * G.k) G.γ G.invariantγ G.quotientγ z b m hm ι p hp hzip
  rw [hz] at he he0 hei
  obtain ⟨eβ, heβ, heβc, _, heβi⟩ := s2e_etale_map_analytic_chart
    G.W G.B (G.k + G.k) G.β w
  let C := localChart G.B (G.k + G.k) (Point.map G.β w)
  let D := localChart G.W (G.k + G.k) w
  have hC : Point.map G.β w ∈ C.source := mem_localChart_source _ _ _
  have hei' : AnalyticAt ℂ (C ∘ e.symm) 0 := by
    exact native_chart_analytic_dim_change G.B (2 * G.k) (G.k + G.k) (by omega)
      (Point.map G.β w) e.symm 0 hei
  obtain ⟨s, hs0, hsc, hsa, hse⟩ := sheet_coefficient_inverse (Point.map G.β) w
    eβ C e D heβ hC he he0 (Point.continuous_map G.β).continuousAt heβc heβi hei'
  exact ⟨e, he, he0, s, hs0, hsc, hsa, hse, hcoef⟩

#print axioms native_chart_analytic_dim_change
#print axioms canonical_abel_coefficient_sheet
end HodgeLean.Foundations.Program.G32Native
