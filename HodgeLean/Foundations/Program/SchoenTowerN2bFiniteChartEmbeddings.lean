import HodgeLean.Foundations.Program.SchoenTowerN2bPullbackCharts
import HodgeLean.Foundations.Program.SchoenTowerN2bGeometryHelpers
import HodgeLean.Foundations.Analytic.AnalytificationChow3Charts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

/-- The actual finite source has affine projective charts with finite coordinate embeddings. -/
theorem n2b_finite_source_chart_embeddings
    {W B : Over (Spec ↧ℂ)} [IsProjective B.hom]
    (β : W ⟶ B) [IsFinite β.left] :
    ∃ (n : ℕ) (ψ : W.left ⟶ g3c_P n), IsAffineHom ψ ∧
      ∀ i : Fin (n + 1), ∃ (m : ℕ)
        (v : Fin m → Γ(n2b_pullbackChart ψ i, ⊤)),
        IsClosedImmersion
          (AffineSpace.homOfVector (n2b_pullbackChartι ψ i ≫ W.hom) v) := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := B.hom)
  haveI := P.isClosedImmersion
  haveI : IsAffineHom (terminal.from (Spec ↧ℂ)) := inferInstance
  haveI : IsAffineHom P.immersion := inferInstance
  haveI : IsAffineHom (pullback.snd (terminal.from (Spec ↧ℂ))
      (terminal.from (g3c_P P.ambientDimension))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  let ψ : W.left ⟶ g3c_P P.ambientDimension :=
    β.left ≫ P.immersion ≫ pullback.snd _ _
  haveI : IsAffineHom ψ := by dsimp only [ψ]; infer_instance
  haveI : IsProper W.hom := n2b_proper_over_projective_base β
  refine ⟨P.ambientDimension, ψ, inferInstance, fun i => ?_⟩
  haveI : IsAffine (n2b_pullbackChart ψ i) := by
    dsimp only [n2b_pullbackChart]
    exact isAffine_of_isAffineHom (pullback.snd ψ (g3c_chartι P.ambientDimension i))
  haveI : IsOpenImmersion (n2b_pullbackChartι ψ i) := by
    dsimp only [n2b_pullbackChartι]
    infer_instance
  exact AnalytificationChow3_exists_isClosedImmersion_homOfVector
    (n2b_pullbackChartι ψ i ≫ W.hom)

end HodgeLean.Foundations.Program
