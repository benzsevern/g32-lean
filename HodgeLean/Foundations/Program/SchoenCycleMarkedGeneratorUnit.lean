import HodgeLean.Foundations.Program.SchoenCycleBranchGeneratorPullback
import HodgeLean.Foundations.Program.SchoenCycleNativeFunctionPullback
import HodgeLean.Foundations.Program.SchoenCycleRootChartNeighbourhoods
import HodgeLean.Foundations.Program.SchoenCycleReducedPullbackUnit

/-! # Analytic unit comparison for actual marked branch generators -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- An actual marked-product generator differs from a native analytic coefficient with the same reduced root product by an analytic unit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B and III.A. -/
theorem s2e_marked_generator_native_unit
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n d : ℕ) [SmoothOfRelativeDimension n (g3_power Z n).hom]
    [SmoothOfRelativeDimension d B.hom] (γ : g3_power Z n ⟶ B)
    (x : ComplexPoint (g3_power Z n)) (S : Finset (Fin n))
    (V : B.left.Opens) (hyV : (Point.map γ x).underlying ∈ V) (c : Γ(B.left, V))
    (u : ((g3_power Z n).left.presheaf.stalk x.underlying)ˣ)
    (hc : γ.left.stalkMap x.underlying
      (B.left.presheaf.germ V (Point.map γ x).underlying hyV c) =
      (∏ i ∈ S, s2e_curvePowerParameter Z n x i) * (u : _))
    (E : ComplexPoint B → ℂ)
    (hE : AnalyticAt ℂ (fun z => E ((ComplexPoint.localChart B d (Point.map γ x)).symm
      (ComplexPoint.localChart B d (Point.map γ x) (Point.map γ x) + z))) 0)
    (scalar : ℂ) (hscalar : scalar ≠ 0)
    (hprod : ∀ᶠ z in 𝓝 0,
      E (Point.map γ (s2e_curvePowerRootChart Z n x
        (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)) z)) = scalar * ∏ i ∈ S, z i)
    (hmap : Filter.map (fun z => Point.map γ (s2e_curvePowerRootChart Z n x
      (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)) z)) (𝓝 0) = 𝓝 (Point.map γ x)) :
    ∃ η : (Fin d → ℂ) → ℂ, AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 0,
        let v := (ComplexPoint.localChart B d (Point.map γ x)).symm
          (ComplexPoint.localChart B d (Point.map γ x) (Point.map γ x) + z)
        Point.evaluate V c v = η z * E v := by
  let y := Point.map γ x
  let C := ComplexPoint.localChart B d y
  let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
  let Q := fun z => Point.map γ (s2e_curvePowerRootChart Z n x L z)
  have hQ : Tendsto Q (𝓝 0) (𝓝 y) :=
    (Point.continuous_map γ).continuousAt.tendsto.comp
      (s2e_curvePowerRootChart_tendsto Z n x L)
  have hQ0 : Q 0 = y := by dsimp only [Q, y]; rw [s2e_curvePowerRootChart_zero]
  have hqa : AnalyticAt ℂ (fun z => C (Q z)) 0 :=
    s2e_curvePowerRootChart_map_analytic Z B n d γ x
  obtain ⟨v, hv⟩ := s2e_native_function_pullback_product B n d y Q hQ hQ0 hqa E hE S
    scalar hscalar hprod
  obtain ⟨w, hw⟩ := s2e_branch_generator_analytic_pullback Z B n d γ x S V hyV c u hc
  exact s2e_analytic_unit_of_open_reduced_pullback
    (fun z => C (Q z) - C y) (hqa.sub analyticAt_const)
    (by rw [hQ0]; exact sub_self _)
    (s2e_centered_native_chart_map_nhds B d y Q 0 hmap)
    (fun z => Point.evaluate V c (C.symm (C y + z)))
    (fun z => E (C.symm (C y + z)))
    (s2e_native_section_analytic B d y V hyV c) hE S w v hw hv

end HodgeLean.Foundations.Program
