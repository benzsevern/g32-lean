import HodgeLean.Foundations.TubularEuler.RegularConormalSubmersionHelpers
import HodgeLean.Foundations.TubularEuler.SurjectiveDifferentialNeighbourhoodHelpers

/-! # Analytic regular equation vectors in the specified ambient chart

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler

theorem regular_equation_vector_analyticAt
    (X : Over (Spec (CommRingCat.of ℂ))) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (u : Fin k → Γ(X.left, V))
    (z x : ComplexPoint X) (hz : x ∈ (chartAt (Fin d → ℂ) z).source)
    (hx : x ∈ Point.overOpen V) :
    AnalyticAt ℂ (fun a : Fin d → ℂ =>
      fun i => Point.evaluate V (u i) ((chartAt (Fin d → ℂ) z).symm a))
      ((chartAt (Fin d → ℂ) z) x) := by
  apply AnalyticAt.pi
  intro i
  apply ComplexPoint.analyticAt_localChart_symm_evaluate X d z
    ((chartAt (Fin d → ℂ) z).map_source hz) V (u i)
  change ((chartAt (Fin d → ℂ) z).symm ((chartAt (Fin d → ℂ) z) x)).underlying ∈ V
  rw [(chartAt (Fin d → ℂ) z).left_inv hz]
  exact hx

#print axioms regular_equation_vector_analyticAt

theorem exists_regular_conormal_submersion_neighbourhood
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (k : ℕ) [SmoothOfRelativeDimension k Y.hom] [SmoothOfRelativeDimension (k + k) X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin (k + k) → ℂ) z).source) :
    ∃ u : Fin k → RingHom.ker (j.left.app V).hom,
      ∀ᶠ a in 𝓝 ((chartAt (Fin (k + k) → ℂ) z) (Point.map j x)),
        Function.Surjective (fderiv ℂ (fun b : Fin (k + k) → ℂ =>
          fun i => Point.evaluate V (u i).val ((chartAt (Fin (k + k) → ℂ) z).symm b)) a) := by
  obtain ⟨u, hu⟩ := exists_regular_conormal_submersion X Y j k V hV x hx z hz
  refine ⟨u, ?_⟩
  have ha := regular_equation_vector_analyticAt X (k + k) k V (fun i => (u i).val)
    z (Point.map j x) hz hx
  exact finite_target_surjective_eventually_of_continuousAt _ _
    ((ha.contDiffAt : ContDiffAt ℂ 1 _ _).continuousAt_fderiv (by decide)) hu

#print axioms exists_regular_conormal_submersion_neighbourhood

end HodgeLean.Foundations.TubularEuler
