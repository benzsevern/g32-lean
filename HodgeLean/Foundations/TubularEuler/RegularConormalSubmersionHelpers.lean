import HodgeLean.Foundations.TubularEuler.RegularConormalCovectorHelpers
import HodgeLean.Foundations.TubularEuler.IndependentCovectorSurjectivityHelpers

/-! # Surjective differentials of original regular conormal equations

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

theorem exists_regular_conormal_submersion
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (k : ℕ) [SmoothOfRelativeDimension k Y.hom] [SmoothOfRelativeDimension (k + k) X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin (k + k) → ℂ) z).source) :
    ∃ u : Fin k → RingHom.ker (j.left.app V).hom,
      Function.Surjective (fderiv ℂ (fun a : Fin (k + k) → ℂ =>
        fun i => Point.evaluate V (u i).val ((chartAt (Fin (k + k) → ℂ) z).symm a))
        ((chartAt (Fin (k + k) → ℂ) z) (Point.map j x))) := by
  obtain ⟨u, hu⟩ := exists_independent_regular_conormal_covectors X Y j k V hV x hx z hz
  refine ⟨u, ?_⟩
  have ha (i : Fin k) : AnalyticAt ℂ
      (fun a : Fin (k + k) → ℂ =>
        Point.evaluate V (u i).val ((chartAt (Fin (k + k) → ℂ) z).symm a))
      ((chartAt (Fin (k + k) → ℂ) z) (Point.map j x)) := by
    apply ComplexPoint.analyticAt_localChart_symm_evaluate X (k + k) z
      ((chartAt (Fin (k + k) → ℂ) z).map_source hz) V (u i).val
    change ((chartAt (Fin (k + k) → ℂ) z).symm
      ((chartAt (Fin (k + k) → ℂ) z) (Point.map j x))).underlying ∈ V
    rw [(chartAt (Fin (k + k) → ℂ) z).left_inv hz]
    exact hx
  rw [fderiv_pi (fun i => (ha i).differentiableAt)]
  exact independent_continuous_covectors_surjective _ hu

#print axioms exists_regular_conormal_submersion

end HodgeLean.Foundations.TubularEuler
