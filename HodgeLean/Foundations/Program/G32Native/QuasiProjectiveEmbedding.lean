import HodgeLean.Foundations.Program.G32Native.ProjectorInjectivity
import HodgeLean.Foundations.TubularEuler.QuasiProjectiveImmersion

/-! # Injective analytic Euclidean coordinates for a specified presentation

The map is the actual Hermitian projector, transported linearly into Euclidean
space. Its injectivity is retained together with its analytic derivatives.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- Restricting the projective projector along the specified scheme immersion
retains injectivity on complex points.
Source: `projectiveHermitianProjector_injective` and
`ComplexPoint.map_injective_of_mono`.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveProjector_injective
    {X : Over (Spec ↧ℂ)} {N : ℕ}
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] : Function.Injective (quasiProjectiveProjector e) := by
  letI : Mono e := Over.mono_of_mono_left e
  exact (projectiveHermitianProjector_injective N).comp
    (ComplexPoint.map_injective_of_mono e)

#print axioms quasiProjectiveProjector_injective

/-- The specified quasi-projective immersion supplies injective analytic
Euclidean coordinates and their injective tangent maps simultaneously.
Source: `quasiProjectiveProjector_chart_regular_aux`,
`quasiProjectiveProjector_differential_aux`, and
`quasiProjectiveProjector_injective`.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveEuclideanEmbedding_exists
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (d N : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] :
    ∃ (n : ℕ) (f : ComplexPoint X → EuclideanSpace ℝ (Fin n)),
      ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω f ∧
      Function.Injective f ∧ ∀ x, Function.Injective
        (mfderiv 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f x) := by
  letI := complexPoint_isRealAnalyticManifold X d
  let H := Fin (N+1) → Fin (N+1) → ℂ
  let n := Module.finrank ℝ H
  let L : H ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [finrank_euclideanSpace_fin]; rfl)
  have hL : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω L :=
    L.toContinuousLinearMap.contDiff.contMDiff
  have hreg := quasiProjectiveProjector_chart_regular_aux X d N e
  refine ⟨n, L ∘ quasiProjectiveProjector e,
    hL.comp hreg,
    L.injective.comp (quasiProjectiveProjector_injective e), ?_⟩
  intro x
  rw [mfderiv_comp x L.differentiableAt.mdifferentiableAt
    (hreg.mdifferentiableAt (by simp)), L.mfderiv_eq]
  exact L.injective.comp (quasiProjectiveProjector_differential_aux X d N e x)

#print axioms quasiProjectiveEuclideanEmbedding_exists

end HodgeLean.Foundations.TubularEuler
