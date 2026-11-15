import HodgeLean.Foundations.Program.SchoenCycleRootParameterGerms
import HodgeLean.Foundations.Program.SchoenCycleAnalyticParameterProducts

/-! # Actual branch generator pullbacks in root coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- An actual section whose stalk pulls back to the marked parameter product times a unit has the reduced coordinate-product analytic pullback.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_branch_generator_analytic_pullback
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n d : ℕ) [SmoothOfRelativeDimension n (g3_power Z n).hom]
    [SmoothOfRelativeDimension d B.hom] (γ : g3_power Z n ⟶ B)
    (x : ComplexPoint (g3_power Z n)) (S : Finset (Fin n))
    (V : B.left.Opens) (hyV : (Point.map γ x).underlying ∈ V) (c : Γ(B.left, V))
    (u : ((g3_power Z n).left.presheaf.stalk x.underlying)ˣ)
    (hc : γ.left.stalkMap x.underlying
      (B.left.presheaf.germ V (Point.map γ x).underlying hyV c) =
      (∏ i ∈ S, s2e_curvePowerParameter Z n x i) * (u : _)) :
    let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
    let Q := s2e_curvePowerRootChart Z n x L
    let φ := fun z => ComplexPoint.localChart B d (Point.map γ x) (Point.map γ (Q z)) -
      ComplexPoint.localChart B d (Point.map γ x) (Point.map γ x)
    ∃ v : (AnalyticGermAt n 0)ˣ,
      s2e_analyticGermPullback φ
        ((s2e_curvePowerRootChart_map_analytic Z B n d γ x).sub analyticAt_const)
        (by dsimp only [φ, Q]; rw [s2e_curvePowerRootChart_zero]; exact sub_self _)
        (s2e_nativeSectionGermHom B d (Point.map γ x) V hyV c) =
          (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * (v : AnalyticGermAt n 0) := by
  dsimp only
  let X := g3_power Z n
  let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
  let Q := s2e_curvePowerRootChart Z n x L
  have hQ := s2e_curvePowerRootChart_tendsto Z n x L
  have hQ0 : Q 0 = x := s2e_curvePowerRootChart_zero Z n x L
  have hqa : AnalyticAt ℂ (fun z => ComplexPoint.localChart X n x (Q z)) 0 := by
    have h := s2e_curvePowerRootChart_map_analytic Z X n n (𝟙 X) x
    change AnalyticAt ℂ (fun z => ComplexPoint.localChart X n x (Q z)) 0 at h
    exact h
  obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x.underlying ∈ (⊤ : X.left.Opens) from trivial)
  let A := s2e_stalkGermAlongNativeChart X n n x Q hQ hQ0 hqa ⟨W, hW⟩ hxW
  obtain ⟨v, hv⟩ := s2e_analytic_parameter_product_unit n A
    (s2e_curvePowerParameter Z n x) S ((L 1) 0)
    (s2e_one_dimensional_line_scale_ne_zero L)
    (fun i _ => s2e_root_parameter_germ Z n n x hqa ⟨W, hW⟩ hxW i) u
  refine ⟨v, ?_⟩
  have heq : s2e_analyticGermPullback
      (fun z => ComplexPoint.localChart B d (Point.map γ x) (Point.map γ (Q z)) -
        ComplexPoint.localChart B d (Point.map γ x) (Point.map γ x))
      ((s2e_curvePowerRootChart_map_analytic Z B n d γ x).sub analyticAt_const)
      (by rw [hQ0]; exact sub_self _)
      (s2e_nativeSectionGermHom B d (Point.map γ x) V hyV c) =
        A (γ.left.stalkMap x.underlying
          (B.left.presheaf.germ V (Point.map γ x).underlying hyV c)) := by
    rw [s2e_nativeSectionGermHom_pullback_along_chart B d n (Point.map γ x)
      (fun z => Point.map γ (Q z))
      ((Point.continuous_map γ).continuousAt.tendsto.comp hQ)
      (by rw [hQ0]) (s2e_curvePowerRootChart_map_analytic Z B n d γ x)]
    apply Subtype.ext
    exact (s2e_stalkGermAlongNativeChart_pullback_germ X B γ n n x Q
      hQ hQ0 hqa ⟨W, hW⟩ hxW V hyV c).symm
  exact heq.trans ((congrArg A hc).trans hv)

end HodgeLean.Foundations.Program
